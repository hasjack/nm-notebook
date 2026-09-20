/* hire_rate_cumulants.c — factorial moments for Q_2nd / sign fingerprint.
 * Same rem-sieve as tilde_g; stores factorial moments
 * m2=E[N(N-1)], m3=E[N(N-1)(N-2)], m4=E[N(N-1)(N-2)(N-3)]
 * and kappa2F/kappa3F/kappa4F, S2=mu-Var, S3=kappa3F/2.
 * Unnamed C lab tool. Papers frozen; no Mathlib.
 *
 * Usage: ./hire_rate_cumulants [X_max] [lam_lo] [lam_hi] [seg_size]
 * Default: X_max=2e10  lam_lo=0.5  lam_hi=4  seg=1<<22
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
#define MAX_BINS 64

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

/* λ bin edges: lam_lo * 2^{k/4} until lam_hi */
static int build_edges(double lam_lo, double lam_hi, double *edges, int max_e) {
    int n = 0;
    double x = lam_lo;
    const double step = pow(2.0, 0.25);
    edges[n++] = x;
    while (n + 1 < max_e) {
        x *= step;
        if (x >= lam_hi * (1.0 - 1e-12)) break;
        edges[n++] = x;
    }
    edges[n++] = lam_hi;
    return n; /* #edges; nbins = n-1 */
}

static int bin_of(double lam, const double *edges, int nedges) {
    if (lam < edges[0] || lam >= edges[nedges - 1]) return -1;
    /* binary search: largest i with edges[i] <= lam, bin = i if edges[i+1] > lam */
    int lo = 0, hi = nedges - 2;
    while (lo < hi) {
        int mid = (lo + hi + 1) / 2;
        if (edges[mid] <= lam) lo = mid;
        else hi = mid - 1;
    }
    return lo;
}

typedef struct {
    uint64_t X;
    double Li;
    double wall_s;
    /* per-bin accumulators */
    uint64_t n_q[MAX_BINS];
    uint64_t sum_N[MAX_BINS];
    uint64_t sum_N2[MAX_BINS]; /* Σ N^2 */
    uint64_t sum_N3[MAX_BINS]; /* Σ N^3 */
    uint64_t sum_N4[MAX_BINS]; /* Σ N^4 */
    uint64_t sum_f2[MAX_BINS]; /* Σ N(N-1) */
    uint64_t sum_f3[MAX_BINS]; /* Σ N(N-1)(N-2) */
    uint64_t sum_f4[MAX_BINS]; /* Σ N(N-1)(N-2)(N-3) */
    uint64_t n_zero[MAX_BINS];
    uint64_t n_occ[MAX_BINS][4]; /* N=0,1,2,≥3 */
    double   sum_lam[MAX_BINS];
    uint64_t n_sat; /* saturated uint8 counts seen at checkpoint */
    uint64_t H_inc; /* total increments into band (with multiplicity) */
} CPResult;

/* Global count band */
static uint8_t *g_cnt = NULL;
static uint64_t g_q_lo = 0;   /* inclusive odd */
static uint64_t g_q_hi = 0;   /* inclusive odd */
static uint64_t g_n_slots = 0;
static uint64_t g_sat_incs = 0; /* times we refused to increment past 255 */
static uint64_t g_band_incs = 0;

static inline void inc_q(uint64_t q) {
    if (q < g_q_lo || q > g_q_hi) return;
    if ((q & 1ull) == 0) return;
    if (q == 3) return;
    uint64_t idx = (q - g_q_lo) >> 1;
    if (idx >= g_n_slots) return;
    uint8_t v = g_cnt[idx];
    if (v < 255) {
        g_cnt[idx] = (uint8_t)(v + 1);
        g_band_incs++;
    } else {
        g_sat_incs++;
    }
}

static void aggregate_checkpoint(CPResult *r, uint32_t *small, uint32_t nsmall,
                                 const double *edges, int nedges) {
    uint64_t X = r->X;
    uint64_t half = X / 2;
    double Li = r->Li;
    int nbins = nedges - 1;

    memset(r->n_q, 0, sizeof(r->n_q));
    memset(r->sum_N, 0, sizeof(r->sum_N));
    memset(r->sum_N2, 0, sizeof(r->sum_N2));
    memset(r->sum_N3, 0, sizeof(r->sum_N3));
    memset(r->sum_N4, 0, sizeof(r->sum_N4));
    memset(r->sum_f2, 0, sizeof(r->sum_f2));
    memset(r->sum_f3, 0, sizeof(r->sum_f3));
    memset(r->sum_f4, 0, sizeof(r->sum_f4));
    memset(r->n_zero, 0, sizeof(r->n_zero));
    memset(r->n_occ, 0, sizeof(r->n_occ));
    memset(r->sum_lam, 0, sizeof(r->sum_lam));
    r->n_sat = 0;
    r->H_inc = 0;

    /* q-range for λ∈[edges[0], edges[nedges-1]) */
    double lam_lo = edges[0];
    double lam_hi = edges[nedges - 1];
    /* λ = Li/(q-1) ∈ [lam_lo, lam_hi) ⇒ q-1 ∈ (Li/lam_hi, Li/lam_lo]
       q ∈ (Li/lam_hi+1, Li/lam_lo+1] */
    double qmin_d = Li / lam_hi + 1.0;
    double qmax_d = Li / lam_lo + 1.0;
    uint64_t qmin = (uint64_t)ceil(qmin_d);
    uint64_t qmax = (uint64_t)floor(qmax_d);
    if (qmin < 5) qmin = 5;
    if (qmin % 2 == 0) qmin++;
    if (qmax > half) qmax = half;
    if (qmax % 2 == 0) qmax--;
    if (qmax < qmin) return;

    /* clamp to allocated band */
    if (qmin < g_q_lo) qmin = g_q_lo;
    if (qmax > g_q_hi) qmax = g_q_hi;
    if (qmin % 2 == 0) qmin++;
    if (qmax % 2 == 0) qmax--;
    if (qmax < qmin) return;

    const uint64_t SEG = 1ull << 24;
    uint8_t *seg = malloc(SEG);
    if (!seg) { perror("malloc seg"); exit(1); }

    for (uint64_t L = qmin; L <= qmax; ) {
        uint64_t R = L + SEG;
        if (R > qmax + 1) R = qmax + 1;
        uint64_t len = R - L;
        memset(seg, 0, (size_t)len);

        for (uint32_t si = 0; si < nsmall; si++) {
            uint64_t p = small[si];
            uint64_t p2 = p * p;
            if (p2 >= R) break;
            uint64_t start;
            if (p2 >= L) start = p2;
            else {
                uint64_t rem = L % p;
                start = rem == 0 ? L : L + (p - rem);
            }
            for (uint64_t m = start; m < R; m += p)
                seg[m - L] = 1;
        }

        for (uint64_t n = L; n < R; n++) {
            if (seg[n - L]) continue;
            if ((n & 1ull) == 0) continue;
            if (n == 3) continue;
            /* prime */
            double lam = Li / ((double)n - 1.0);
            int bi = bin_of(lam, edges, nedges);
            if (bi < 0 || bi >= nbins) continue;

            uint64_t idx = (n - g_q_lo) >> 1;
            uint32_t N = 0;
            if (idx < g_n_slots) N = g_cnt[idx];
            if (N == 255) r->n_sat++;

            r->n_q[bi]++;
            {
                uint64_t Nu = (uint64_t)N;
                uint64_t n2 = Nu * Nu;
                uint64_t n3 = n2 * Nu;
                uint64_t n4 = n3 * Nu;
                r->sum_N[bi] += Nu;
                r->sum_N2[bi] += n2;
                r->sum_N3[bi] += n3;
                r->sum_N4[bi] += n4;
                if (Nu >= 2) {
                    uint64_t f2 = Nu * (Nu - 1);
                    r->sum_f2[bi] += f2;
                    if (Nu >= 3) {
                        uint64_t f3 = f2 * (Nu - 2);
                        r->sum_f3[bi] += f3;
                        if (Nu >= 4)
                            r->sum_f4[bi] += f3 * (Nu - 3);
                    }
                }
            }
            r->sum_lam[bi] += lam;
            if (N == 0) r->n_zero[bi]++;
            if (N == 0) r->n_occ[bi][0]++;
            else if (N == 1) r->n_occ[bi][1]++;
            else if (N == 2) r->n_occ[bi][2]++;
            else r->n_occ[bi][3]++;
            r->H_inc += N;
        }

        L = R;
    }
    free(seg);
}

static void emit_csv(FILE *out, const CPResult *r, const double *edges, int nedges) {
    int nbins = nedges - 1;
    double logX = log((double)r->X);
    for (int i = 0; i < nbins; i++) {
        uint64_t nq = r->n_q[i];
        if (nq == 0) continue;
        double mu = (double)r->sum_N[i] / (double)nq;
        double EN2 = (double)r->sum_N2[i] / (double)nq;
        double var = EN2 - mu * mu;
        double var_over_mu = (mu > 0.0) ? var / mu : NAN;
        double lam_mean = r->sum_lam[i] / (double)nq;
        double P0 = (double)r->n_zero[i] / (double)nq;
        double P1 = (double)r->n_occ[i][1] / (double)nq;
        double P2 = (double)r->n_occ[i][2] / (double)nq;
        double Pge3 = (double)r->n_occ[i][3] / (double)nq;
        double e_mu = exp(-mu);
        double e_lam = exp(-lam_mean);
        double under = e_mu - P0;
        double g = e_lam - P0;
        double tilde_g = logX * under;
        double logX_g = logX * g;
        double m2f = (double)r->sum_f2[i] / (double)nq;
        double m3f = (double)r->sum_f3[i] / (double)nq;
        double m4f = (double)r->sum_f4[i] / (double)nq;
        double kappa2F = m2f - mu * mu;
        double kappa3F = m3f - 3.0 * m2f * mu + 2.0 * mu * mu * mu;
        double kappa4F = m4f - 4.0 * m3f * mu - 3.0 * m2f * m2f
                         + 12.0 * m2f * mu * mu - 6.0 * mu * mu * mu * mu;
        double S2 = mu - var;
        double S3 = kappa3F / 2.0;
        fprintf(out,
            "%llu,%.8g,%.8g,%llu,%.8f,%.8f,%.8f,%.8f,%.8f,%.8f,%.8f,%.8f,%.8f,%.8f,%.8f,"
            "%.8f,%.8f,%.8f,%.8f,%.8f,%.8f,%.8f,%.8e,%.8e,%.8e,%.8e,%.8e\n",
            (unsigned long long)r->X,
            edges[i], edges[i + 1],
            (unsigned long long)nq,
            mu, lam_mean, P0, e_mu, e_lam, g,
            under, tilde_g, logX_g, var, var_over_mu,
            P0, P1, P2, Pge3,
            m2f, m3f, m4f, kappa2F, kappa3F, kappa4F, S2, S3);
    }
    fflush(out);
}

static void do_checkpoint(CPResult *r, uint32_t *small, uint32_t nsmall,
                          const double *edges, int nedges, double t0, FILE *csv) {
    r->wall_s = wall_now() - t0;
    fprintf(stderr,
        "[cp-agg] X=%llu  Li=%.6e  band_incs=%llu  sat_incs=%llu  starting prime agg ...\n",
        (unsigned long long)r->X, r->Li,
        (unsigned long long)g_band_incs, (unsigned long long)g_sat_incs);
    double tb = wall_now();
    aggregate_checkpoint(r, small, nsmall, edges, nedges);
    fprintf(stderr,
        "[cp] X=%llu  H_band=%llu  sat_cells=%llu  agg=%.2fs  cum=%.2fs  RSS=%.0fMB\n",
        (unsigned long long)r->X, (unsigned long long)r->H_inc,
        (unsigned long long)r->n_sat, wall_now() - tb, wall_now() - t0, peak_rss_mb());

    int nbins = nedges - 1;
    double logX = log((double)r->X);
    fprintf(stderr,
        "  λ-bin  n_q  mu  lam  P0  P1  P2  P≥3  e-mu  e-lam  g  under  tilde_g  Var/μ  bias\n");
    for (int i = 0; i < nbins; i++) {
        uint64_t nq = r->n_q[i];
        if (nq == 0) continue;
        double mu = (double)r->sum_N[i] / (double)nq;
        double m2 = (double)r->sum_N2[i] / (double)nq;
        double var = m2 - mu * mu;
        double vom = (mu > 0.0) ? var / mu : NAN;
        double lm = r->sum_lam[i] / (double)nq;
        double P0 = (double)r->n_zero[i] / (double)nq;
        double P1 = (double)r->n_occ[i][1] / (double)nq;
        double P2 = (double)r->n_occ[i][2] / (double)nq;
        double Pge3 = (double)r->n_occ[i][3] / (double)nq;
        double e_mu = exp(-mu);
        double e_lam = exp(-lm);
        double g = e_lam - P0;
        double under0 = e_mu - P0;
        double tilde_g = logX * under0;
        double bias = mu - lm;
        fprintf(stderr,
            "  [%.4f,%.4f)  n=%llu  mu=%.4f  lam=%.4f  P0=%.4f  P1=%.4f  P2=%.4f  P3+=%.4f  "
            "e-mu=%.4f  e-lam=%.4f  g=%+.5f  under=%+.5f  tild=%+.4f  V/μ=%.4f  bias=%+.4f\n",
            edges[i], edges[i + 1],
            (unsigned long long)nq, mu, lm, P0, P1, P2, Pge3,
            e_mu, e_lam, g, under0, tilde_g, vom, bias);
    }
    emit_csv(csv, r, edges, nedges);
}

int main(int argc, char **argv) {
    uint64_t X_max = 20000000000ull;
    double lam_lo = 0.5;
    double lam_hi = 4.0;
    uint64_t seg_size = 1ull << 22;
    if (argc >= 2) X_max = strtoull(argv[1], NULL, 10);
    if (argc >= 3) lam_lo = strtod(argv[2], NULL);
    if (argc >= 4) lam_hi = strtod(argv[3], NULL);
    if (argc >= 5) seg_size = strtoull(argv[4], NULL, 10);

    double edges[MAX_BINS + 1];
    int nedges = build_edges(lam_lo, lam_hi, edges, MAX_BINS + 1);
    int nbins = nedges - 1;
    fprintf(stderr, "[bins] %d bins over [%.4g,%.4g]:", nbins, lam_lo, lam_hi);
    for (int i = 0; i < nedges; i++) fprintf(stderr, " %.4f", edges[i]);
    fprintf(stderr, "\n");

    uint64_t cp_list[] = {
        100000000ull, 1000000000ull,
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
        {10000000ull, 6.649184050486e+05},
        {100000000ull, 5.762209375448e+06},
        {1000000000ull, 5.084923495700e+07},
        {10000000000ull, 4.550556145866e+08},
        {20000000000ull, 8.822148792048e+08},
    };
    for (int i = 0; i < ncp; i++) {
        for (size_t j = 0; j < sizeof(li_ref)/sizeof(li_ref[0]); j++) {
            if (cps[i].X == li_ref[j].X) {
                fprintf(stderr, "[Li] X=%llu  Ei=%.10e  ref=%.10e  rel=%.3e\n",
                        (unsigned long long)cps[i].X, cps[i].Li, li_ref[j].Li,
                        fabs(cps[i].Li - li_ref[j].Li) / li_ref[j].Li);
                cps[i].Li = li_ref[j].Li;
            }
        }
    }

    /* Band covering union of λ-ranges across checkpoints */
    double qmin_d = 1e300, qmax_d = 0.0;
    for (int i = 0; i < ncp; i++) {
        double a = cps[i].Li / lam_hi + 1.0;
        double b = cps[i].Li / lam_lo + 1.0;
        if (a < qmin_d) qmin_d = a;
        if (b > qmax_d) qmax_d = b;
    }
    g_q_lo = (uint64_t)floor(qmin_d);
    g_q_hi = (uint64_t)ceil(qmax_d);
    if (g_q_lo < 5) g_q_lo = 5;
    if (g_q_lo % 2 == 0) g_q_lo--;
    if (g_q_lo < 5) g_q_lo = 5;
    if (g_q_hi % 2 == 0) g_q_hi++;
    if (g_q_hi > X_max / 2) g_q_hi = X_max / 2;
    if (g_q_hi % 2 == 0) g_q_hi--;
    g_n_slots = (g_q_hi >= g_q_lo) ? ((g_q_hi - g_q_lo) / 2 + 1) : 0;

    fprintf(stderr,
        "[init] X_max=%llu  lam=[%.3g,%.3g]  q_band=[%llu,%llu]  slots=%llu (%.2f MB)  ncp=%d\n",
        (unsigned long long)X_max, lam_lo, lam_hi,
        (unsigned long long)g_q_lo, (unsigned long long)g_q_hi,
        (unsigned long long)g_n_slots, g_n_slots / (1024.0 * 1024.0), ncp);

    g_cnt = calloc(g_n_slots, 1);
    if (!g_cnt) {
        fprintf(stderr, "[fatal] calloc %.2f MB failed — shrink lam range or X_max\n",
                g_n_slots / (1024.0 * 1024.0));
        return 1;
    }
    fprintf(stderr, "[init] count band allocated  RSS=%.0fMB\n", peak_rss_mb());

    double t0 = wall_now();
    uint64_t sqrt_lim = (uint64_t)sqrt((double)(X_max + 1)) + 2;
    uint32_t nsmall = 0;
    uint32_t *small_primes = sieve_primes(sqrt_lim, &nsmall);
    uint64_t sqrt_band = (uint64_t)sqrt((double)g_q_hi) + 2;
    uint32_t nsmall_bin = 0;
    uint32_t *small_bin = sieve_primes(sqrt_band > sqrt_lim ? sqrt_band : sqrt_lim, &nsmall_bin);
    fprintf(stderr, "[init] #small=%u  #small_bin=%u  seg=%llu  RSS=%.0fMB\n",
            nsmall, nsmall_bin, (unsigned long long)seg_size, peak_rss_mb());

        printf("X,lam_lo,lam_hi,n_q,mu_emp,lam_mean,P0_emp,exp_m_mu,exp_m_lam,g,under,tilde_g,logX_g,var_N,var_over_mu,"
           "P_N0,P_N1,P_N2,P_Nge3,m2_fact,m3_fact,m4_fact,kappa2F,kappa3F,kappa4F,S2,S3\n");
    fflush(stdout);

    int cp_i = 0;
    int seg_count = 0;
    uint64_t total_segs = (X_max - 5 + seg_size) / seg_size;

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
                do_checkpoint(&cps[cp_i], small_bin, nsmall_bin, edges, nedges, t0, stdout);
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
                inc_q(big);
                do { n /= big; } while (n % big == 0);
            }
            for (uint32_t si = 0; si < nsmall; si++) {
                uint64_t q = small_primes[si];
                if (q < 5) continue;
                if (q * q > n) break;
                if (n % q == 0) {
                    inc_q(q);
                    do { n /= q; } while (n % q == 0);
                }
            }
            if (n > 1) inc_q(n);
        }

        while (cp_i < ncp && cps[cp_i].X < B) {
            do_checkpoint(&cps[cp_i], small_bin, nsmall_bin, edges, nedges, t0, stdout);
            cp_i++;
        }

        if (seg_count % 50 == 0) {
            double wall = wall_now() - t0;
            double pct = 100.0 * (double)(B - 5) / (double)(X_max - 5 + 1);
            fprintf(stderr,
                "[seg %d/%llu] owners[%llu,%llu) (%.2f%%)  band_incs=%llu  sat=%llu  wall=%.1fs  RSS=%.0fMB\n",
                seg_count, (unsigned long long)total_segs,
                (unsigned long long)A, (unsigned long long)B, pct,
                (unsigned long long)g_band_incs, (unsigned long long)g_sat_incs,
                wall, peak_rss_mb());
        }

        free(rem);
        free(is_comp);
        A = B;
    }

    while (cp_i < ncp) {
        do_checkpoint(&cps[cp_i], small_bin, nsmall_bin, edges, nedges, t0, stdout);
        cp_i++;
    }

    fprintf(stderr, "[done] wall=%.2fs  peak_RSS=%.0fMB  band_incs=%llu  sat_incs=%llu\n",
            wall_now() - t0, peak_rss_mb(),
            (unsigned long long)g_band_incs, (unsigned long long)g_sat_incs);

    free(g_cnt);
    free(small_primes);
    free(small_bin);
    return 0;
}
