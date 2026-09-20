/* hire_rate_bin_residual.c — bin H - P_Pois by u-scale and decades.
 * Owner-ordered rem-sieve (hired bitset) + per-checkpoint prime scan for bins.
 *
 * Usage: ./hire_rate_bin_residual [X_max] [seg_size]
 * Default X_max=20000000000  seg=4194304
 * CSV long-form on stdout; progress on stderr.
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
#define N_UBIN 10
#define MAX_DEC 16   /* decades 10^0 .. 10^15 */

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

/* Ei(x) for x>0; Li(X)=Ei(ln X). Same as hire_rate_Rpois.c */
static double expint_Ei(double x) {
    const double gamma = 0.57721566490153286060651209;
    if (x <= 0.0) return NAN;
    /* Power series is stable for moderate x; asymptotic needs optimal truncation. */
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
        /* asymptotic: e^x/x * Σ_{n=0} n!/x^n ; stop when |term| increases */
        double sum = 1.0, term = 1.0;
        for (int n = 1; n <= 200; n++) {
            double next = term * ((double)n / x);
            if (fabs(next) >= fabs(term) && n > 1) break; /* past optimal term */
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

typedef struct {
    uint64_t X;
    double Li;
    int do_trunc;          /* also compute truncated P* */
    /* u-bins */
    uint64_t Hu[N_UBIN];
    double   Pu[N_UBIN];
    double   Pstu[N_UBIN]; /* truncated /q */
    double   Pstum1[N_UBIN]; /* truncated /(q-1) */
    /* decades: index k means [10^k, 10^{k+1}) */
    uint64_t Hd[MAX_DEC];
    double   Pd[MAX_DEC];
    double   Pstd[MAX_DEC];
    double   Pstdm1[MAX_DEC];
    /* totals */
    uint64_t H_all;        /* rem-sieve H (all hired odd q≠3) */
    uint64_t H_le_half;    /* hired primes q≤X/2, q≠3 (and q≠2) */
    uint64_t H_gt_half;    /* hired with X/2 < q ≤ X+1 (approx) */
    double   P_total;
    double   Pst_total;
    double   Pstm1_total;
    double   wall_s;
} CPResult;

static int decade_of(uint64_t q) {
    if (q < 10) return 0;
    int k = 0;
    uint64_t p = 1;
    while (k + 1 < MAX_DEC) {
        /* next power: careful overflow */
        if (p > UINT64_MAX / 10) break;
        uint64_t nxt = p * 10;
        if (q < nxt) return k;
        p = nxt;
        k++;
    }
    return k;
}

/* Bin primes q≤X/2 against hired bitset. */
static void bin_checkpoint(CPResult *r, const uint8_t *hired, uint32_t *small, uint32_t nsmall) {
    uint64_t X = r->X;
    uint64_t half = X / 2;
    double Li = r->Li;
    double logX = log((double)X);
    int trunc = r->do_trunc;

    memset(r->Hu, 0, sizeof(r->Hu));
    memset(r->Pu, 0, sizeof(r->Pu));
    memset(r->Pstu, 0, sizeof(r->Pstu));
    memset(r->Pstum1, 0, sizeof(r->Pstum1));
    memset(r->Hd, 0, sizeof(r->Hd));
    memset(r->Pd, 0, sizeof(r->Pd));
    memset(r->Pstd, 0, sizeof(r->Pstd));
    memset(r->Pstdm1, 0, sizeof(r->Pstdm1));
    r->H_le_half = 0;
    r->P_total = 0;
    r->Pst_total = 0;
    r->Pstm1_total = 0;

    const uint64_t SEG = 1ull << 24;
    uint8_t *seg = malloc(SEG);
    if (!seg) { perror("malloc seg"); exit(1); }

    /* Skip q=2 (even, not in H); start from 3. We exclude q=3 from H and from P
     * to match hire definition (odd primes q≠3). Task: sum over primes q≤X/2
     * in R_Pois includes 2 and 3 historically — but residual bins are about hired
     * odd q≠3. For P_bin we sum over odd primes q≠3 in the bin (same population).
     * Documented R_Pois used all primes incl 2,3; the 1.4% is vs that. For WHERE
     * excess lives among hired odds, bin P over odd q≠3. Also emit a note:
     * P_all_primes vs P_odd_ne3 differs by ~2 (negligible vs millions). */

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
            /* n prime, 3 ≤ n ≤ half */
            if (n == 3) {
                /* exclude from hire population; still optionally in classic P —
                 * we skip for bin residual alignment with H */
                continue;
            }

            double nd = (double)n;
            double p_hire = 1.0 - exp(-Li / nd);
            r->P_total += p_hire;

            int ui = (int)(log(nd) / logX * N_UBIN);
            if (ui < 0) ui = 0;
            if (ui >= N_UBIN) ui = N_UBIN - 1;
            r->Pu[ui] += p_hire;

            int dk = decade_of(n);
            if (dk < 0) dk = 0;
            if (dk >= MAX_DEC) dk = MAX_DEC - 1;
            r->Pd[dk] += p_hire;

            if (trunc) {
                double Li2q = Li_of(2.0 * nd);
                double lam = Li - Li2q;
                if (lam < 0.0) lam = 0.0;
                double pt = 1.0 - exp(-lam / nd);
                double ptm1 = 1.0 - exp(-lam / (nd - 1.0));
                r->Pst_total += pt;
                r->Pstm1_total += ptm1;
                r->Pstu[ui] += pt;
                r->Pstum1[ui] += ptm1;
                r->Pstd[dk] += pt;
                r->Pstdm1[dk] += ptm1;
            }

            if (is_hired(hired, n)) {
                r->H_le_half++;
                r->Hu[ui]++;
                r->Hd[dk]++;
            }
        }
    }
    free(seg);

    /* H_gt filled by caller as H_all - H_le_half (avoids O(X) bitset scan). */
    (void)hired; (void)X;
}


static void emit_csv_rows(FILE *out, const CPResult *r) {
    /* u bins */
    for (int i = 0; i < N_UBIN; i++) {
        double lo = (double)i / N_UBIN;
        double hi = (double)(i + 1) / N_UBIN;
        double resid = (double)r->Hu[i] - r->Pu[i];
        double rel = (r->Pu[i] > 0) ? resid / r->Pu[i] : 0.0;
        fprintf(out, "%llu,u,%.1f,%.1f,%llu,%.6f,%.6f,%.8f\n",
                (unsigned long long)r->X, lo, hi,
                (unsigned long long)r->Hu[i], r->Pu[i], resid, rel);
    }
    /* decades */
    for (int k = 0; k < MAX_DEC; k++) {
        if (r->Hd[k] == 0 && r->Pd[k] == 0.0) continue;
        double lo = pow(10.0, k);
        double hi = pow(10.0, k + 1);
        double resid = (double)r->Hd[k] - r->Pd[k];
        double rel = (r->Pd[k] > 0) ? resid / r->Pd[k] : 0.0;
        fprintf(out, "%llu,decade,%.0f,%.0f,%llu,%.6f,%.6f,%.8f\n",
                (unsigned long long)r->X, lo, hi,
                (unsigned long long)r->Hd[k], r->Pd[k], resid, rel);
    }
    /* totals as special bins */
    {
        double resid = (double)r->H_le_half - r->P_total;
        double rel = (r->P_total > 0) ? resid / r->P_total : 0.0;
        fprintf(out, "%llu,total_le_half,0,%.0f,%llu,%.6f,%.6f,%.8f\n",
                (unsigned long long)r->X, (double)(r->X / 2),
                (unsigned long long)r->H_le_half, r->P_total, resid, rel);
    }
    if (r->do_trunc) {
        for (int i = 0; i < N_UBIN; i++) {
            double lo = (double)i / N_UBIN;
            double hi = (double)(i + 1) / N_UBIN;
            double resid = (double)r->Hu[i] - r->Pstu[i];
            double rel = (r->Pstu[i] > 0) ? resid / r->Pstu[i] : 0.0;
            fprintf(out, "%llu,u_trunc_q,%.1f,%.1f,%llu,%.6f,%.6f,%.8f\n",
                    (unsigned long long)r->X, lo, hi,
                    (unsigned long long)r->Hu[i], r->Pstu[i], resid, rel);
        }
        for (int i = 0; i < N_UBIN; i++) {
            double lo = (double)i / N_UBIN;
            double hi = (double)(i + 1) / N_UBIN;
            double resid = (double)r->Hu[i] - r->Pstum1[i];
            double rel = (r->Pstum1[i] > 0) ? resid / r->Pstum1[i] : 0.0;
            fprintf(out, "%llu,u_trunc_qm1,%.1f,%.1f,%llu,%.6f,%.6f,%.8f\n",
                    (unsigned long long)r->X, lo, hi,
                    (unsigned long long)r->Hu[i], r->Pstum1[i], resid, rel);
        }
        {
            double resid = (double)r->H_le_half - r->Pst_total;
            double rel = (r->Pst_total > 0) ? resid / r->Pst_total : 0.0;
            fprintf(out, "%llu,total_trunc_q,0,%.0f,%llu,%.6f,%.6f,%.8f\n",
                    (unsigned long long)r->X, (double)(r->X / 2),
                    (unsigned long long)r->H_le_half, r->Pst_total, resid, rel);
            resid = (double)r->H_le_half - r->Pstm1_total;
            rel = (r->Pstm1_total > 0) ? resid / r->Pstm1_total : 0.0;
            fprintf(out, "%llu,total_trunc_qm1,0,%.0f,%llu,%.6f,%.6f,%.8f\n",
                    (unsigned long long)r->X, (double)(r->X / 2),
                    (unsigned long long)r->H_le_half, r->Pstm1_total, resid, rel);
        }
    }
    fflush(out);
}

int main(int argc, char **argv) {
    uint64_t X_max = 20000000000ull;
    uint64_t seg_size = 1ull << 22;
    if (argc >= 2) X_max = strtoull(argv[1], NULL, 10);
    if (argc >= 3) seg_size = strtoull(argv[2], NULL, 10);

    /* Checkpoints */
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
        /* Use scipy-matched Li where available; else compute */
        cps[ncp].Li = Li_of((double)cp_list[i]);
        cps[ncp].do_trunc = (cp_list[i] >= 10000000000ull) ? 1 : 0;
        ncp++;
    }
    /* Override Li with scipy references for reproducibility */
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
    /* For binning sieves we need small primes up to sqrt(X_max/2) */
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

    printf("X,bin_type,bin_lo,bin_hi,H_bin,P_bin,residual,rel\n");
    fflush(stdout);

    /* Small primes for binning: up to sqrt(X_max/2) is enough */
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
                CPResult *r = &cps[cp_i];
                r->H_all = H;
                r->wall_s = wall_now() - t0;
                fprintf(stderr, "[cp-bin] X=%llu  H_all=%llu  starting prime scan to %llu ...\n",
                        (unsigned long long)r->X, (unsigned long long)H,
                        (unsigned long long)(r->X / 2));
                double tb = wall_now();
                bin_checkpoint(r, hired, small_bin, nsmall_bin);
                r->H_gt_half = r->H_all - r->H_le_half;
                fprintf(stderr,
                    "[cp] X=%llu  H_all=%llu  H_le_half=%llu  H_gt_half=%llu  "
                    "P=%.2f  resid_le=%.2f  Rpois_le=%.6f  bin_wall=%.2fs  "
                    "cum=%.2fs  RSS=%.0fMB\n",
                    (unsigned long long)r->X,
                    (unsigned long long)r->H_all,
                    (unsigned long long)r->H_le_half,
                    (unsigned long long)r->H_gt_half,
                    r->P_total,
                    (double)r->H_le_half - r->P_total,
                    r->P_total > 0 ? (double)r->H_le_half / r->P_total : 0.0,
                    wall_now() - tb, wall_now() - t0, peak_rss_mb());
                if (r->do_trunc) {
                    fprintf(stderr,
                        "[trunc] X=%llu  Pst=%.2f  R_trunc_q=%.6f  R_trunc_qm1=%.6f\n",
                        (unsigned long long)r->X, r->Pst_total,
                        r->Pst_total > 0 ? (double)r->H_le_half / r->Pst_total : 0.0,
                        r->Pstm1_total > 0 ? (double)r->H_le_half / r->Pstm1_total : 0.0);
                }
                emit_csv_rows(stdout, r);
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
            CPResult *r = &cps[cp_i];
            r->H_all = H;
            r->wall_s = wall_now() - t0;
            fprintf(stderr, "[cp-bin] X=%llu  H_all=%llu  starting prime scan to %llu ...\n",
                    (unsigned long long)r->X, (unsigned long long)H,
                    (unsigned long long)(r->X / 2));
            double tb = wall_now();
            bin_checkpoint(r, hired, small_bin, nsmall_bin);
                r->H_gt_half = r->H_all - r->H_le_half;
            fprintf(stderr,
                "[cp] X=%llu  H_all=%llu  H_le_half=%llu  H_gt_half=%llu  "
                "P=%.2f  resid_le=%.2f  Rpois_le=%.6f  bin_wall=%.2fs  "
                "cum=%.2fs  RSS=%.0fMB\n",
                (unsigned long long)r->X,
                (unsigned long long)r->H_all,
                (unsigned long long)r->H_le_half,
                (unsigned long long)r->H_gt_half,
                r->P_total,
                (double)r->H_le_half - r->P_total,
                r->P_total > 0 ? (double)r->H_le_half / r->P_total : 0.0,
                wall_now() - tb, wall_now() - t0, peak_rss_mb());
            if (r->do_trunc) {
                fprintf(stderr,
                    "[trunc] X=%llu  Pst=%.2f  R_trunc_q=%.6f  R_trunc_qm1=%.6f\n",
                    (unsigned long long)r->X, r->Pst_total,
                    r->Pst_total > 0 ? (double)r->H_le_half / r->Pst_total : 0.0,
                    r->Pstm1_total > 0 ? (double)r->H_le_half / r->Pstm1_total : 0.0);
            }
            emit_csv_rows(stdout, r);
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
        CPResult *r = &cps[cp_i];
        r->H_all = H;
        r->wall_s = wall_now() - t0;
        fprintf(stderr, "[cp-bin] X=%llu  H_all=%llu  starting prime scan ...\n",
                (unsigned long long)r->X, (unsigned long long)H);
        double tb = wall_now();
        bin_checkpoint(r, hired, small_bin, nsmall_bin);
                r->H_gt_half = r->H_all - r->H_le_half;
        fprintf(stderr,
            "[cp] X=%llu  H_all=%llu  H_le_half=%llu  H_gt_half=%llu  "
            "P=%.2f  Rpois_le=%.6f  bin_wall=%.2fs  cum=%.2fs  RSS=%.0fMB\n",
            (unsigned long long)r->X,
            (unsigned long long)r->H_all,
            (unsigned long long)r->H_le_half,
            (unsigned long long)r->H_gt_half,
            r->P_total,
            r->P_total > 0 ? (double)r->H_le_half / r->P_total : 0.0,
            wall_now() - tb, wall_now() - t0, peak_rss_mb());
        if (r->do_trunc) {
            fprintf(stderr,
                "[trunc] X=%llu  Pst=%.2f  R_trunc_q=%.6f  R_trunc_qm1=%.6f\n",
                (unsigned long long)r->X, r->Pst_total,
                r->Pst_total > 0 ? (double)r->H_le_half / r->Pst_total : 0.0,
                r->Pstm1_total > 0 ? (double)r->H_le_half / r->Pstm1_total : 0.0);
        }
        emit_csv_rows(stdout, r);
        cp_i++;
    }

    /* Summary meta on stderr */
    fprintf(stderr, "[done] wall=%.2fs  peak_RSS=%.0fMB\n", wall_now() - t0, peak_rss_mb());
    for (int i = 0; i < ncp; i++) {
        CPResult *r = &cps[i];
        fprintf(stderr, "[summary] X=%llu H_all=%llu H_le=%llu H_gt=%llu P=%.4f resid=%.4f\n",
                (unsigned long long)r->X, (unsigned long long)r->H_all,
                (unsigned long long)r->H_le_half, (unsigned long long)r->H_gt_half,
                r->P_total, (double)r->H_le_half - r->P_total);
        fprintf(stderr, "  u-bins H:");
        for (int u = 0; u < N_UBIN; u++) fprintf(stderr, " %llu", (unsigned long long)r->Hu[u]);
        fprintf(stderr, "\n  u-bins resid:");
        for (int u = 0; u < N_UBIN; u++)
            fprintf(stderr, " %.1f", (double)r->Hu[u] - r->Pu[u]);
        fprintf(stderr, "\n");
    }

    free(hired);
    free(small_primes);
    free(small_bin);
    return 0;
}
