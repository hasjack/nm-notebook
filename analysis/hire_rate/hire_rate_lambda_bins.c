/* hire_rate_lambda_bins.c — bin H - P_Pois by λ = Li(X)/(q-1).
 * Reuses owner-ordered rem-sieve (hired bitset) from hire_rate_bin_residual.
 *
 * Usage: ./hire_rate_lambda_bins [X_max] [seg_size]
 * Default X_max=20000000000  seg=4194304
 * CSV long-form on stdout; progress on stderr.
 *
 * P_Pois uses 1-exp(-Li/(q-1)) over odd primes q≠3, q≤X/2.
 * No k0 histogram.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <sys/resource.h>

#define MAX_CP 16

/* Fine log-scale λ edges: (-∞,0.125), [0.125,0.25), ..., [64,∞)
 * indices 0..N_FINE-1; last bin is open to +∞ */
static const double FINE_EDGES[] = {
    0.0, 0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0
};
#define N_FINE_EDGES ((int)(sizeof(FINE_EDGES)/sizeof(FINE_EDGES[0])))
#define N_FINE (N_FINE_EDGES) /* N_FINE_EDGES-1 closed + 1 open tail = N_FINE_EDGES bins */

/* Coarse: λ<0.5, [0.5,1), [1,2), [2,4), ≥4 */
#define N_COARSE 5

static double wall_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static double peak_rss_mb(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_maxrss / 1024.0;
}

/* Ei(x) for x>0; Li(X)=Ei(ln X). Same as hire_rate_bin_residual.c */
static double expint_Ei(double x) {
    const double gamma = 0.57721566490153286060651209;
    if (x <= 0.0) return NAN;
    if (x <= 40.0) {
        double sum = 0.0, term = 1.0;
        for (int n = 1; n <= 800; n++) {
            term *= x / (double)n;
            double add = term / (double)n;
            sum += add;
            if (fabs(add) <= fabs(sum) * 1e-17 + 1e-300) break;
        }
        return gamma + log(x) + sum;
    } else {
        double sum = 1.0, term = 1.0;
        for (int n = 1; n <= 200; n++) {
            double next = term * ((double)n / x);
            if (fabs(next) >= fabs(term) && n > 1) break;
            term = next;
            sum += term;
            if (fabs(term) <= fabs(sum) * 1e-17) break;
        }
        return exp(x) / x * sum;
    }
}

static double Li_of(double X) { return expint_Ei(log(X)); }

static uint32_t *sieve_primes(uint64_t limit, uint32_t *out_n) {
    if (limit < 2) { *out_n = 0; return NULL; }
    size_t n = (size_t)limit + 1;
    uint8_t *comp = calloc(n, 1);
    if (!comp) { perror("calloc"); exit(1); }
    comp[0] = comp[1] = 1;
    uint64_t r = (uint64_t)sqrt((double)limit);
    for (uint64_t i = 2; i <= r; i++) {
        if (!comp[i]) {
            for (uint64_t m = i * i; m <= limit; m += i) comp[m] = 1;
        }
    }
    uint32_t cnt = 0;
    for (uint64_t i = 2; i <= limit; i++) if (!comp[i]) cnt++;
    uint32_t *primes = malloc(cnt * sizeof(uint32_t));
    if (!primes) { perror("malloc"); exit(1); }
    cnt = 0;
    for (uint64_t i = 2; i <= limit; i++) if (!comp[i]) primes[cnt++] = (uint32_t)i;
    free(comp);
    *out_n = cnt;
    return primes;
}

static inline int is_hired(const uint8_t *hired, uint64_t q) {
    uint64_t i = q >> 1;
    return (hired[i >> 3] >> (i & 7)) & 1;
}

static inline void mark_hired(uint8_t *hired, uint64_t *H, uint64_t q, uint64_t X_max) {
    if (q <= 3 || (q & 1ull) == 0) return;
    if (q > X_max + 1) return;
    uint64_t i = q >> 1;
    uint64_t bi = i >> 3;
    uint8_t bit = (uint8_t)(1u << (i & 7));
    uint8_t b = hired[bi];
    if (!(b & bit)) {
        hired[bi] = (uint8_t)(b | bit);
        (*H)++;
    }
}

/* Fine bin index for λ: 0 = [0, 0.125), ..., N_FINE-1 = [64, ∞) */
static int fine_bin(double lam) {
    if (lam < 0.0) lam = 0.0;
    for (int i = 0; i < N_FINE_EDGES - 1; i++) {
        if (lam < FINE_EDGES[i + 1]) return i;
    }
    return N_FINE - 1; /* ≥ 64 */
}

/* Coarse: 0:<0.5, 1:[0.5,1), 2:[1,2), 3:[2,4), 4:≥4 */
static int coarse_bin(double lam) {
    if (lam < 0.5) return 0;
    if (lam < 1.0) return 1;
    if (lam < 2.0) return 2;
    if (lam < 4.0) return 3;
    return 4;
}

typedef struct {
    uint64_t X;
    double Li;
    double u_star;       /* 1 - loglog(X)/log(X) */
    double lam_at_ustar; /* Li / (X^{u_*} - 1) ≈ 1 */
    uint64_t Hf[N_FINE];
    double   Pf[N_FINE];
    uint64_t Hc[N_COARSE];
    double   Pc[N_COARSE];
    uint64_t H_all;
    uint64_t H_le_half;
    double   P_total;
    double   wall_s;
} CPResult;

static void bin_checkpoint(CPResult *r, const uint8_t *hired, uint32_t *small, uint32_t nsmall) {
    uint64_t X = r->X;
    uint64_t half = X / 2;
    double Li = r->Li;

    memset(r->Hf, 0, sizeof(r->Hf));
    memset(r->Pf, 0, sizeof(r->Pf));
    memset(r->Hc, 0, sizeof(r->Hc));
    memset(r->Pc, 0, sizeof(r->Pc));
    r->H_le_half = 0;
    r->P_total = 0;

    const uint64_t SEG = 1ull << 24;
    uint8_t *seg = malloc(SEG);
    if (!seg) { perror("malloc seg"); exit(1); }

    for (uint64_t L = 0; L <= half; L += SEG) {
        uint64_t R = L + SEG;
        if (R > half + 1) R = half + 1;
        uint64_t len = R - L;
        memset(seg, 0, (size_t)len);

        for (uint32_t si = 0; si < nsmall; si++) {
            uint64_t p = small[si];
            uint64_t p2 = p * p;
            uint64_t start;
            if (p2 >= L) start = p2;
            else {
                uint64_t rem = L % p;
                start = rem == 0 ? L : L + (p - rem);
            }
            for (uint64_t m = start; m < R; m += p)
                seg[m - L] = 1;
        }
        if (L == 0) {
            if (0 < len) seg[0] = 1;
            if (1 < len) seg[1] = 1;
            if (2 < len) seg[2] = 1; /* skip 2 */
        }

        for (uint64_t n = (L == 0 ? 3 : L); n < R; n++) {
            if (seg[n - L]) continue;
            if (n == 3) continue; /* odd primes q≠3 */

            double nd = (double)n;
            double lam = Li / (nd - 1.0);
            double p_hire = 1.0 - exp(-lam);

            r->P_total += p_hire;

            int fi = fine_bin(lam);
            int ci = coarse_bin(lam);
            r->Pf[fi] += p_hire;
            r->Pc[ci] += p_hire;

            if (is_hired(hired, n)) {
                r->H_le_half++;
                r->Hf[fi]++;
                r->Hc[ci]++;
            }
        }
    }
    free(seg);
}

static void emit_csv_rows(FILE *out, const CPResult *r) {
    /* fine bins */
    for (int i = 0; i < N_FINE; i++) {
        double lo = FINE_EDGES[i];
        double hi = (i + 1 < N_FINE_EDGES) ? FINE_EDGES[i + 1] : INFINITY;
        double resid = (double)r->Hf[i] - r->Pf[i];
        double rel = (r->Pf[i] > 0) ? resid / r->Pf[i] : 0.0;
        if (isfinite(hi))
            fprintf(out, "%llu,%.6g,%.6g,%llu,%.6f,%.6f,%.8f\n",
                    (unsigned long long)r->X, lo, hi,
                    (unsigned long long)r->Hf[i], r->Pf[i], resid, rel);
        else
            fprintf(out, "%llu,%.6g,inf,%llu,%.6f,%.6f,%.8f\n",
                    (unsigned long long)r->X, lo,
                    (unsigned long long)r->Hf[i], r->Pf[i], resid, rel);
    }
    fflush(out);
}

static void do_checkpoint(CPResult *r, const uint8_t *hired,
                          uint32_t *small_bin, uint32_t nsmall_bin,
                          uint64_t H, double t0, FILE *csv) {
    r->H_all = H;
    r->wall_s = wall_now() - t0;
    double logX = log((double)r->X);
    double loglogX = log(logX);
    r->u_star = 1.0 - loglogX / logX;
    double q_star = exp(r->u_star * logX); /* X^{u_*} */
    r->lam_at_ustar = r->Li / (q_star - 1.0);

    fprintf(stderr, "[cp-bin] X=%llu  H_all=%llu  starting prime scan to %llu ...\n",
            (unsigned long long)r->X, (unsigned long long)H,
            (unsigned long long)(r->X / 2));
    double tb = wall_now();
    bin_checkpoint(r, hired, small_bin, nsmall_bin);
    fprintf(stderr,
        "[cp] X=%llu  H_all=%llu  H_le=%llu  P=%.2f  resid=%.2f  R=%.6f  "
        "u*=%.6f  λ(u*)=%.4f  bin_wall=%.2fs  cum=%.2fs  RSS=%.0fMB\n",
        (unsigned long long)r->X,
        (unsigned long long)r->H_all,
        (unsigned long long)r->H_le_half,
        r->P_total,
        (double)r->H_le_half - r->P_total,
        r->P_total > 0 ? (double)r->H_le_half / r->P_total : 0.0,
        r->u_star, r->lam_at_ustar,
        wall_now() - tb, wall_now() - t0, peak_rss_mb());

    /* stderr fine table */
    fprintf(stderr, "  fine λ bins (H, P, resid, rel%%):\n");
    int peak_i = 0;
    double peak_resid = -1e300;
    for (int i = 0; i < N_FINE; i++) {
        double lo = FINE_EDGES[i];
        double hi = (i + 1 < N_FINE_EDGES) ? FINE_EDGES[i + 1] : INFINITY;
        double resid = (double)r->Hf[i] - r->Pf[i];
        double rel = (r->Pf[i] > 0) ? resid / r->Pf[i] : 0.0;
        if (resid > peak_resid) { peak_resid = resid; peak_i = i; }
        if (isfinite(hi))
            fprintf(stderr, "    [%.3g,%.3g): H=%llu P=%.2f resid=%.2f rel=%.4f%%\n",
                    lo, hi, (unsigned long long)r->Hf[i], r->Pf[i], resid, 100.0*rel);
        else
            fprintf(stderr, "    [%.3g,inf): H=%llu P=%.2f resid=%.2f rel=%.4f%%\n",
                    lo, (unsigned long long)r->Hf[i], r->Pf[i], resid, 100.0*rel);
    }
    {
        double plo = FINE_EDGES[peak_i];
        double phi = (peak_i + 1 < N_FINE_EDGES) ? FINE_EDGES[peak_i + 1] : INFINITY;
        fprintf(stderr, "  peak residual fine bin: ");
        if (isfinite(phi)) fprintf(stderr, "[%.3g,%.3g)", plo, phi);
        else fprintf(stderr, "[%.3g,inf)", plo);
        fprintf(stderr, " resid=%.2f\n", peak_resid);
    }
    fprintf(stderr, "  coarse:\n");
    {
        const char *clab[N_COARSE] = {"λ<0.5", "[0.5,1)", "[1,2)", "[2,4)", "λ≥4"};
        for (int i = 0; i < N_COARSE; i++) {
            double resid = (double)r->Hc[i] - r->Pc[i];
            double rel = (r->Pc[i] > 0) ? resid / r->Pc[i] : 0.0;
            fprintf(stderr, "    %s: H=%llu P=%.2f resid=%.2f rel=%.4f%%\n",
                    clab[i], (unsigned long long)r->Hc[i], r->Pc[i], resid, 100.0*rel);
        }
    }

    emit_csv_rows(csv, r);
}

int main(int argc, char **argv) {
    uint64_t X_max = 20000000000ull;
    uint64_t seg_size = 1ull << 22;
    if (argc >= 2) X_max = strtoull(argv[1], NULL, 10);
    if (argc >= 3) seg_size = strtoull(argv[2], NULL, 10);

    uint64_t cp_list[] = {
        1000000ull, 10000000ull, 100000000ull, 1000000000ull,
        10000000000ull, 20000000000ull
    };
    int ncp_all = (int)(sizeof(cp_list) / sizeof(cp_list[0]));
    CPResult cps[MAX_CP];
    int ncp = 0;
    for (int i = 0; i < ncp_all; i++) {
        if (cp_list[i] > X_max) break;
        memset(&cps[ncp], 0, sizeof(cps[ncp]));
        cps[ncp].X = cp_list[i];
        cps[ncp].Li = Li_of((double)cp_list[i]);
        ncp++;
    }
    struct { uint64_t X; double Li; } li_ref[] = {
        {1000000ull, 7.862754915946e+04},
        {10000000ull, 6.649184050486e+05},
        {100000000ull, 5.762209375448e+06},
        {1000000000ull, 5.084923495700e+07},
        {10000000000ull, 4.550556145866e+08},
        {20000000000ull, 8.822148792048e+08},
    };
    for (int i = 0; i < ncp; i++) {
        for (size_t j = 0; j < sizeof(li_ref)/sizeof(li_ref[0]); j++) {
            if (cps[i].X == li_ref[j].X) {
                fprintf(stderr, "[Li] X=%llu  Ei=%.10e  scipy=%.10e  rel=%.3e\n",
                        (unsigned long long)cps[i].X, cps[i].Li, li_ref[j].Li,
                        fabs(cps[i].Li - li_ref[j].Li) / li_ref[j].Li);
                cps[i].Li = li_ref[j].Li;
            }
        }
    }

    double t0 = wall_now();
    uint64_t sqrt_lim = (uint64_t)sqrt((double)(X_max + 1)) + 2;
    uint64_t sqrt_half = (uint64_t)sqrt((double)(X_max / 2)) + 2;
    if (sqrt_half > sqrt_lim) sqrt_half = sqrt_lim;
    uint32_t nsmall = 0;
    uint32_t *small_primes = sieve_primes(sqrt_lim > sqrt_half ? sqrt_lim : sqrt_half, &nsmall);
    fprintf(stderr, "[init] X_max=%llu  sqrt_lim=%llu  #small=%u  seg=%llu  ncp=%d  RSS=%.0fMB\n",
            (unsigned long long)X_max, (unsigned long long)sqrt_lim, nsmall,
            (unsigned long long)seg_size, ncp, peak_rss_mb());

    uint64_t n_odds = (X_max + 1) / 2 + 1;
    uint64_t hired_bytes = (n_odds + 7) / 8;
    fprintf(stderr, "[init] hired_bitset bytes=%llu (%.1f MB reserved)\n",
            (unsigned long long)hired_bytes, hired_bytes / (1024.0 * 1024.0));
    uint8_t *hired = calloc(hired_bytes, 1);
    if (!hired) { perror("calloc hired"); exit(1); }
    uint64_t H = 0;
    int cp_i = 0;
    int seg_count = 0;
    uint64_t total_segs = (X_max - 5 + seg_size) / seg_size;

    printf("X,bin_lo,bin_hi,H,P,resid,rel\n");
    fflush(stdout);

    uint32_t nsmall_bin = 0;
    uint32_t *small_bin = sieve_primes(sqrt_half, &nsmall_bin);

    for (uint64_t A = 5; A <= X_max; ) {
        uint64_t B = A + seg_size;
        if (B > X_max + 1) B = X_max + 1;
        seg_count++;

        uint64_t M0_L = (A >= 1) ? A - 1 : 1;
        if (M0_L < 1) M0_L = 1;
        uint64_t M0_R = B + 1;
        uint64_t nlen = M0_R - M0_L;

        uint64_t *rem = malloc(nlen * sizeof(uint64_t));
        if (!rem) { perror("malloc rem"); exit(1); }
        for (uint64_t i = 0; i < nlen; i++) rem[i] = M0_L + i;

        uint64_t own_n = B - A;
        uint8_t *is_comp = calloc(own_n, 1);
        if (!is_comp) { perror("calloc is_comp"); exit(1); }

        for (uint32_t si = 0; si < nsmall; si++) {
            uint64_t p = small_primes[si];
            if (p * p >= B) break;
            uint64_t start = p * p;
            if (start < A) start = A;
            start = ((start + p - 1) / p) * p;
            for (uint64_t m = start; m < B; m += p) is_comp[m - A] = 1;
        }

        for (uint32_t si = 0; si < nsmall; si++) {
            uint64_t p = small_primes[si];
            if (p * p >= M0_R) break;
            uint64_t start = ((M0_L + p - 1) / p) * p;
            for (uint64_t m = start; m < M0_R; m += p) {
                uint64_t idx = m - M0_L;
                uint64_t rv = rem[idx];
                if (rv % p) continue;
                do { rv /= p; } while (rv % p == 0);
                rem[idx] = rv;
            }
        }

        for (uint64_t i = 0; i < own_n; i++) {
            if (is_comp[i]) continue;
            uint64_t p = A + i;

            while (cp_i < ncp && cps[cp_i].X < p) {
                do_checkpoint(&cps[cp_i], hired, small_bin, nsmall_bin, H, t0, stdout);
                cp_i++;
            }

            uint64_t m0;
            uint64_t r3 = p % 3;
            if (r3 == 1) m0 = p + 1;
            else if (r3 == 2) m0 = p - 1;
            else continue;

            uint64_t n = m0;
            while ((n & 1ull) == 0) n >>= 1;
            while (n % 3ull == 0) n /= 3ull;

            uint64_t big = rem[m0 - M0_L];
            if (big > 3 && n % big == 0) {
                mark_hired(hired, &H, big, X_max);
                do { n /= big; } while (n % big == 0);
            }
            for (uint32_t si = 0; si < nsmall; si++) {
                uint64_t q = small_primes[si];
                if (q < 5) continue;
                if (q * q > n) break;
                if (n % q == 0) {
                    mark_hired(hired, &H, q, X_max);
                    do { n /= q; } while (n % q == 0);
                }
            }
            if (n > 1) mark_hired(hired, &H, n, X_max);
        }

        while (cp_i < ncp && cps[cp_i].X < B) {
            do_checkpoint(&cps[cp_i], hired, small_bin, nsmall_bin, H, t0, stdout);
            cp_i++;
        }

        if (seg_count % 50 == 0) {
            double wall = wall_now() - t0;
            double pct = 100.0 * (double)(B - 5) / (double)(X_max - 5 + 1);
            fprintf(stderr, "[seg %d/%llu] owners[%llu,%llu) (%.2f%%)  H=%llu  wall=%.1fs  RSS=%.0fMB\n",
                    seg_count, (unsigned long long)total_segs,
                    (unsigned long long)A, (unsigned long long)B, pct,
                    (unsigned long long)H, wall, peak_rss_mb());
        }

        free(rem);
        free(is_comp);
        A = B;
    }

    while (cp_i < ncp) {
        do_checkpoint(&cps[cp_i], hired, small_bin, nsmall_bin, H, t0, stdout);
        cp_i++;
    }

    fprintf(stderr, "[done] wall=%.2fs  peak_RSS=%.0fMB\n", wall_now() - t0, peak_rss_mb());
    for (int i = 0; i < ncp; i++) {
        CPResult *r = &cps[i];
        fprintf(stderr, "[summary] X=%llu H=%llu P=%.4f resid=%.4f u*=%.6f λ*=%.4f\n",
                (unsigned long long)r->X, (unsigned long long)r->H_le_half,
                r->P_total, (double)r->H_le_half - r->P_total,
                r->u_star, r->lam_at_ustar);
    }

    free(hired);
    free(small_primes);
    free(small_bin);
    return 0;
}
