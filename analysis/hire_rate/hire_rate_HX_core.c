/* Thin hire-rate H(X), R(X) — owner-ordered segmented rem-sieve.
 * Usage: hire_rate_HX_core X_max seg_size cp1,cp2,...
 * Prints CSV lines: X,H,R,wall_s  and progress on stderr.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <sys/resource.h>

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

static double R_of(uint64_t H, uint64_t X) {
    double lnX = log((double)X);
    return (double)H * (lnX * lnX) / ((double)X * log(lnX));
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "Usage: %s X_max seg_size cp1,cp2,...\n", argv[0]);
        return 2;
    }
    uint64_t X_max = strtoull(argv[1], NULL, 10);
    uint64_t seg_size = strtoull(argv[2], NULL, 10);

    /* parse checkpoints */
    int cp_cap = 64, cp_n = 0;
    uint64_t *cps = malloc(cp_cap * sizeof(uint64_t));
    char *cps_str = strdup(argv[3]);
    for (char *tok = strtok(cps_str, ","); tok; tok = strtok(NULL, ",")) {
        if (cp_n >= cp_cap) {
            cp_cap *= 2;
            cps = realloc(cps, cp_cap * sizeof(uint64_t));
        }
        cps[cp_n++] = strtoull(tok, NULL, 10);
    }
    free(cps_str);
    /* sort checkpoints */
    for (int i = 0; i < cp_n; i++)
        for (int j = i + 1; j < cp_n; j++)
            if (cps[j] < cps[i]) { uint64_t t = cps[i]; cps[i] = cps[j]; cps[j] = t; }

    double t0 = wall_now();
    uint64_t sqrt_lim = (uint64_t)sqrt((double)(X_max + 1)) + 2;
    uint32_t nsmall = 0;
    uint32_t *small_primes = sieve_primes(sqrt_lim, &nsmall);
    fprintf(stderr, "[init] X_max=%llu  sqrt_lim=%llu  #small=%u  seg=%llu  RSS=%.0fMB\n",
            (unsigned long long)X_max, (unsigned long long)sqrt_lim, nsmall,
            (unsigned long long)seg_size, peak_rss_mb());

    uint64_t n_odds = (X_max + 1) / 2 + 1;
    uint64_t hired_bytes = (n_odds + 7) / 8;
    uint8_t *hired = calloc(hired_bytes, 1);
    if (!hired) { perror("calloc hired"); exit(1); }
    uint64_t H = 0;
    int cp_i = 0;
    int seg_count = 0;
    uint64_t total_segs = (X_max - 5 + seg_size) / seg_size;

    printf("X,H,R,wall_s_cumulative\n");
    fflush(stdout);

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
                uint64_t r = rem[idx];
                if (r % p) continue;
                do { r /= p; } while (r % p == 0);
                rem[idx] = r;
            }
        }

        for (uint64_t i = 0; i < own_n; i++) {
            if (is_comp[i]) continue;
            uint64_t p = A + i;

            /* snapshots: all owners ≤ X done for X < p */
            while (cp_i < cp_n && cps[cp_i] < p) {
                uint64_t X = cps[cp_i];
                double wall = wall_now() - t0;
                double Rv = R_of(H, X);
                printf("%llu,%llu,%.10f,%.4f\n",
                       (unsigned long long)X, (unsigned long long)H, Rv, wall);
                fflush(stdout);
                fprintf(stderr, "[cp] X=%-12llu  H=%-12llu  R=%.6f  wall=%.2fs  RSS=%.0fMB\n",
                        (unsigned long long)X, (unsigned long long)H, Rv, wall, peak_rss_mb());
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

        while (cp_i < cp_n && cps[cp_i] < B) {
            uint64_t X = cps[cp_i];
            double wall = wall_now() - t0;
            double Rv = R_of(H, X);
            printf("%llu,%llu,%.10f,%.4f\n",
                   (unsigned long long)X, (unsigned long long)H, Rv, wall);
            fflush(stdout);
            fprintf(stderr, "[cp] X=%-12llu  H=%-12llu  R=%.6f  wall=%.2fs  RSS=%.0fMB\n",
                    (unsigned long long)X, (unsigned long long)H, Rv, wall, peak_rss_mb());
            cp_i++;
        }

        if (seg_count % 20 == 0) {
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

    while (cp_i < cp_n) {
        uint64_t X = cps[cp_i];
        double wall = wall_now() - t0;
        double Rv = R_of(H, X);
        printf("%llu,%llu,%.10f,%.4f\n",
               (unsigned long long)X, (unsigned long long)H, Rv, wall);
        fflush(stdout);
        fprintf(stderr, "[cp] X=%-12llu  H=%-12llu  R=%.6f  wall=%.2fs  RSS=%.0fMB\n",
                (unsigned long long)X, (unsigned long long)H, Rv, wall, peak_rss_mb());
        cp_i++;
    }

    fprintf(stderr, "[done] H(%llu)=%llu  wall=%.2fs  peak_RSS=%.0fMB\n",
            (unsigned long long)X_max, (unsigned long long)H, wall_now() - t0, peak_rss_mb());
    free(hired);
    free(small_primes);
    free(cps);
    return 0;
}
