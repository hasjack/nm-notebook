/* hire_rate_Rpois.c — π(X), R(X), R_Pois, R_Pois_qm1 at H(X) checkpoints.
 * Segmented sieve to X_max; on-the-fly Poisson hire sums over primes q ≤ X/2.
 *
 * Li(X) = Ei(ln X)  (offset logarithmic integral li(X)), via series/asymptotic Ei.
 * PRIMARY:  R_Pois     = H / Σ_{q≤X/2} (1 - exp(-Li(X)/q))
 * OPTIONAL: R_Pois_qm1 = H / Σ_{q≤X/2} (1 - exp(-Li(X)/(q-1)))
 *
 * Usage: ./hire_rate_Rpois
 * Prints CSV to stdout; progress on stderr.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <sys/resource.h>

#define NCP 15
#define SEG_BITS 24
#define SEG_SIZE (1ull << SEG_BITS)

static const uint64_t XS[NCP] = {
    10000ull, 100000ull, 500000ull, 1000000ull, 5000000ull,
    10000000ull, 50000000ull, 100000000ull, 500000000ull, 1000000000ull,
    2200000000ull, 5000000000ull, 10000000000ull, 15000000000ull, 20000000000ull
};
static const uint64_t HS[NCP] = {
    361ull, 2401ull, 9291ull, 16688ull, 68222ull,
    125661ull, 527157ull, 980292ull, 4195019ull, 7877140ull,
    16173662ull, 34296996ull, 64838984ull, 94178863ull, 122776796ull
};

/* scipy.special.expi(log(X)) reference values (for Li cross-check / use) */
static const double LI_SCIPY[NCP] = {
    1.246137215899e+03,
    9.629809001051e+03,
    4.160628878643e+04,
    7.862754915946e+04,
    3.486381150413e+05,
    6.649184050486e+05,
    3.001557426702e+06,
    5.762209375448e+06,
    2.635683214886e+07,
    5.084923495700e+07,
    1.075428870011e+08,
    2.349587808739e+08,
    4.550556145866e+08,
    6.701865365273e+08,
    8.822148792048e+08
};

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

/* Exponential integral Ei(x) for x > 0.
 * Series for x <= 18; asymptotic for larger x.
 * Li(x) = Ei(ln x). */
static double expint_Ei(double x) {
    const double gamma = 0.57721566490153286060651209;
    if (x <= 0.0) return NAN;
    if (x <= 18.0) {
        double sum = 0.0, term = 1.0;
        for (int n = 1; n <= 300; n++) {
            term *= x / (double)n;
            double add = term / (double)n;
            sum += add;
            if (fabs(add) <= fabs(sum) * 1e-17 + 1e-300) break;
        }
        return gamma + log(x) + sum;
    } else {
        /* asymptotic: e^x/x * Σ n!/x^n */
        double sum = 1.0, term = 1.0;
        for (int n = 1; n <= 80; n++) {
            term *= (double)n / x;
            sum += term;
            if (fabs(term) <= fabs(sum) * 1e-17) break;
            if (term > 1e300) break; /* divergence of truncated asymptotic */
        }
        return exp(x) / x * sum;
    }
}

static double Li_of(double X) {
    return expint_Ei(log(X));
}

static double R_of(uint64_t H, uint64_t X) {
    double lnX = log((double)X);
    return (double)H * (lnX * lnX) / ((double)X * log(lnX));
}

/* Simple sieve of primes up to limit (inclusive), return malloc'd array. */
static uint32_t *sieve_primes_u32(uint64_t limit, uint32_t *out_n) {
    if (limit < 2) { *out_n = 0; return NULL; }
    size_t n = (size_t)limit + 1;
    uint8_t *comp = calloc(n, 1);
    if (!comp) { perror("calloc"); exit(1); }
    comp[0] = comp[1] = 1;
    uint64_t r = (uint64_t)sqrt((double)limit) + 1;
    for (uint64_t i = 2; i <= r; i++) {
        if (!comp[i]) {
            for (uint64_t m = i * i; m <= limit; m += i) comp[m] = 1;
        }
    }
    uint32_t cnt = 0;
    for (uint64_t i = 2; i <= limit; i++) if (!comp[i]) cnt++;
    uint32_t *primes = malloc((size_t)cnt * sizeof(uint32_t));
    if (!primes) { perror("malloc"); exit(1); }
    cnt = 0;
    for (uint64_t i = 2; i <= limit; i++) if (!comp[i]) primes[cnt++] = (uint32_t)i;
    free(comp);
    *out_n = cnt;
    return primes;
}

int main(void) {
    const uint64_t X_max = XS[NCP - 1];
    double t0 = wall_now();

    double Li[NCP];
    fprintf(stderr, "[Li] Computing Ei(ln X); cross-check vs scipy.special.expi(log X)\n");
    for (int i = 0; i < NCP; i++) {
        Li[i] = Li_of((double)XS[i]);
        double rel = fabs(Li[i] - LI_SCIPY[i]) / LI_SCIPY[i];
        fprintf(stderr, "  X=%llu  Li_c=%.10e  Li_scipy=%.10e  rel_err=%.3e\n",
                (unsigned long long)XS[i], Li[i], LI_SCIPY[i], rel);
        /* Prefer scipy-matched values for reproducibility of documented method */
        Li[i] = LI_SCIPY[i];
    }

    uint64_t sqrt_lim = (uint64_t)sqrt((double)X_max) + 2;
    uint32_t nsmall = 0;
    uint32_t *small = sieve_primes_u32(sqrt_lim, &nsmall);
    fprintf(stderr, "[init] X_max=%llu  sqrt_lim=%llu  #small=%u  seg=%llu  RSS=%.0fMB\n",
            (unsigned long long)X_max, (unsigned long long)sqrt_lim, nsmall,
            (unsigned long long)SEG_SIZE, peak_rss_mb());

    /* Half-limits for R_Pois (primes q ≤ X/2) */
    uint64_t half[NCP];
    for (int i = 0; i < NCP; i++) half[i] = XS[i] / 2;

    uint64_t pi_at[NCP];
    double sum_q[NCP], sum_qm1[NCP];
    double wall_at[NCP];
    int done_pi[NCP], done_pois[NCP];
    memset(pi_at, 0, sizeof(pi_at));
    memset(done_pi, 0, sizeof(done_pi));
    memset(done_pois, 0, sizeof(done_pois));
    for (int i = 0; i < NCP; i++) {
        sum_q[i] = 0.0;
        sum_qm1[i] = 0.0;
        wall_at[i] = 0.0;
    }

    uint64_t pi_count = 0;
    int next_pi = 0;      /* next checkpoint awaiting pi finalize (when n > X) */
    int next_pois = 0;    /* next checkpoint still needing q ≤ half updates;
                             all cps with half[i] >= current prime stay active */

    /* Odd-only segmented sieve from 3; handle 2 separately */
    {
        uint64_t p = 2;
        pi_count = 1;
        /* finalize any X < 2 — none */
        /* R_Pois: q=2 for all checkpoints with half >= 2 (all of them) */
        for (int i = 0; i < NCP; i++) {
            if (2 <= half[i]) {
                sum_q[i] += 1.0 - exp(-Li[i] / 2.0);
                sum_qm1[i] += 1.0 - exp(-Li[i] / 1.0); /* q-1 = 1 */
            }
        }
        (void)p;
    }

    uint8_t *seg = malloc(SEG_SIZE);
    if (!seg) { perror("malloc seg"); exit(1); }

    /* Process odds: numbers 3,5,7,... up to X_max.
     * Represent odd n = 2*k+1; we sieve all integers in [L,R) for simplicity. */
    for (uint64_t L = 0; L <= X_max; L += SEG_SIZE) {
        uint64_t R = L + SEG_SIZE;
        if (R > X_max + 1) R = X_max + 1;
        uint64_t len = R - L;
        memset(seg, 0, (size_t)len);

        /* mark composites in [L,R) */
        for (uint32_t si = 0; si < nsmall; si++) {
            uint64_t p = small[si];
            uint64_t p2 = p * p;
            uint64_t start;
            if (p2 >= L) start = p2;
            else {
                uint64_t rem = L % p;
                start = rem == 0 ? L : L + (p - rem);
            }
            if (start < L) start = L; /* paranoia */
            for (uint64_t m = start; m < R; m += p) {
                seg[m - L] = 1;
            }
        }
        if (L == 0) {
            if (0 < len) seg[0] = 1; /* 0 */
            if (1 < len) seg[1] = 1; /* 1 */
            /* 2 already counted; mark so we skip */
            if (2 < len) seg[2] = 1;
        }

        for (uint64_t n = (L == 0 ? 3 : L); n < R; n++) {
            if (seg[n - L]) continue;
            /* n is prime */
            pi_count++;

            /* Finalize π checkpoints: when we have counted all primes ≤ X,
               i.e. after processing prime n, if next numbers exceed X we still
               wait until n > X. Actually: pi(X) = count of primes ≤ X.
               So when n > XS[next_pi], we've already counted all primes ≤ XS. */
            while (next_pi < NCP && n > XS[next_pi]) {
                pi_at[next_pi] = pi_count - 1; /* current n is already > X, subtract */
                wall_at[next_pi] = wall_now() - t0;
                done_pi[next_pi] = 1;
                fprintf(stderr, "[pi] X=%llu  pi=%llu  wall=%.2fs  RSS=%.0fMB\n",
                        (unsigned long long)XS[next_pi],
                        (unsigned long long)pi_at[next_pi],
                        wall_at[next_pi], peak_rss_mb());
                next_pi++;
            }

            /* Advance pois floor: checkpoints whose half < n are done with summing */
            while (next_pois < NCP && n > half[next_pois]) {
                done_pois[next_pois] = 1;
                if (!done_pi[next_pois]) {
                    /* wall snapshot for pois-complete even if pi not yet */
                    wall_at[next_pois] = wall_now() - t0;
                }
                fprintf(stderr, "[pois] half-done X=%llu (half=%llu) sum_q=%.6f sum_qm1=%.6f wall=%.2fs\n",
                        (unsigned long long)XS[next_pois],
                        (unsigned long long)half[next_pois],
                        sum_q[next_pois], sum_qm1[next_pois],
                        wall_now() - t0);
                next_pois++;
            }

            /* Update active R_Pois sums: checkpoints with half >= n */
            if (next_pois < NCP) {
                double nd = (double)n;
                double nm1 = nd - 1.0;
                for (int i = next_pois; i < NCP; i++) {
                    sum_q[i] += 1.0 - exp(-Li[i] / nd);
                    sum_qm1[i] += 1.0 - exp(-Li[i] / nm1);
                }
            }
        }

        if ((L / SEG_SIZE) % 64 == 0) {
            fprintf(stderr, "[seg] L=%llu / %llu  pi=%llu  next_pois=%d  wall=%.1fs  RSS=%.0fMB\n",
                    (unsigned long long)L, (unsigned long long)X_max,
                    (unsigned long long)pi_count, next_pois,
                    wall_now() - t0, peak_rss_mb());
        }
    }

    /* Finalize remaining π (all primes ≤ X_max counted) */
    while (next_pi < NCP) {
        pi_at[next_pi] = pi_count;
        wall_at[next_pi] = wall_now() - t0;
        done_pi[next_pi] = 1;
        fprintf(stderr, "[pi] X=%llu  pi=%llu  wall=%.2fs\n",
                (unsigned long long)XS[next_pi],
                (unsigned long long)pi_at[next_pi],
                wall_at[next_pi]);
        next_pi++;
    }
    while (next_pois < NCP) {
        done_pois[next_pois] = 1;
        fprintf(stderr, "[pois] half-done X=%llu sum_q=%.6f\n",
                (unsigned long long)XS[next_pois], sum_q[next_pois]);
        next_pois++;
    }

    free(seg);
    free(small);

    double t1 = wall_now();
    fprintf(stderr, "[done] total_wall=%.2fs  peak_RSS=%.0fMB  pi(Xmax)=%llu\n",
            t1 - t0, peak_rss_mb(), (unsigned long long)pi_count);

    /* Sanity checks */
    struct { uint64_t X; uint64_t pi; } sanity[] = {
        {10000000ull, 664579ull},
        {100000000ull, 5761455ull},
        {1000000000ull, 50847534ull},
    };
    for (size_t s = 0; s < sizeof(sanity)/sizeof(sanity[0]); s++) {
        for (int i = 0; i < NCP; i++) {
            if (XS[i] == sanity[s].X) {
                if (pi_at[i] != sanity[s].pi) {
                    fprintf(stderr, "SANITY FAIL: pi(%llu)=%llu expected %llu\n",
                            (unsigned long long)sanity[s].X,
                            (unsigned long long)pi_at[i],
                            (unsigned long long)sanity[s].pi);
                    return 1;
                }
                fprintf(stderr, "SANITY OK: pi(%llu)=%llu\n",
                        (unsigned long long)sanity[s].X,
                        (unsigned long long)pi_at[i]);
            }
        }
    }

    /* CSV header + rows */
    printf("X,H,pi,H_over_pi,sparsity_pred,R,R_Pois,R_Pois_qm1,wall_s\n");
    for (int i = 0; i < NCP; i++) {
        double X = (double)XS[i];
        double H = (double)HS[i];
        double pi = (double)pi_at[i];
        double H_over_pi = H / pi;
        double sparsity = log(log(X)) / log(X);
        double R = R_of(HS[i], XS[i]);
        double Rpois = H / sum_q[i];
        double Rpois_qm1 = H / sum_qm1[i];
        printf("%llu,%llu,%llu,%.12g,%.12g,%.12g,%.12g,%.12g,%.4f\n",
               (unsigned long long)XS[i],
               (unsigned long long)HS[i],
               (unsigned long long)pi_at[i],
               H_over_pi, sparsity, R, Rpois, Rpois_qm1,
               wall_at[i]);
    }
    return 0;
}
