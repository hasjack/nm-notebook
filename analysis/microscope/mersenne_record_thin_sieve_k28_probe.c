/* Hunt odd prime r <= R with 28*(2^e-1)+1 ≡ 0 (mod r), e=136279841 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static uint64_t modmul(uint64_t a, uint64_t b, uint64_t m) {
    return (unsigned __int128)a * b % m;
}
static uint64_t modpow(uint64_t base, uint64_t exp, uint64_t m) {
    uint64_t r = 1;
    base %= m;
    while (exp) {
        if (exp & 1) r = modmul(r, base, m);
        base = modmul(base, base, m);
        exp >>= 1;
    }
    return r;
}

int main(int argc, char **argv) {
    uint64_t R = argc > 1 ? strtoull(argv[1], 0, 10) : 1000000000ULL;
    const uint64_t E = 136279841ULL;
    const uint64_t K = 28ULL;
    clock_t t0 = clock();
    /* segmented sieve */
    uint64_t lim = (uint64_t)sqrt((double)R) + 1;
    unsigned char *base = calloc(lim + 1, 1);
    for (uint64_t i = 2; i * i <= lim; i++)
        if (!base[i]) for (uint64_t j = i * i; j <= lim; j += i) base[j] = 1;
    uint64_t *small; uint64_t ns = 0;
    for (uint64_t i = 2; i <= lim; i++) if (!base[i]) ns++;
    small = malloc(ns * sizeof(uint64_t));
    ns = 0;
    for (uint64_t i = 2; i <= lim; i++) if (!base[i]) small[ns++] = i;
    free(base);

    uint64_t seg = 1 << 20; /* 1M */
    unsigned char *buf = malloc(seg);
    uint64_t found = 0;
    uint64_t checked = 0;
    for (uint64_t low = 2; low <= R; low += seg) {
        uint64_t high = low + seg - 1;
        if (high > R) high = R;
        memset(buf, 0, high - low + 1);
        for (uint64_t i = 0; i < ns; i++) {
            uint64_t p = small[i];
            uint64_t start = ((low + p - 1) / p) * p;
            if (start < p * p) start = p * p;
            for (uint64_t j = start; j <= high; j += p) buf[j - low] = 1;
        }
        for (uint64_t n = low; n <= high; n++) {
            if (buf[n - low] || n < 3) continue;
            /* odd prime n */
            checked++;
            uint64_t qmod = modpow(2, E, n);
            if (qmod == 0) continue; /* 2^e ≡ 0 impossible */
            qmod = (qmod + n - 1) % n; /* 2^e - 1 */
            if (qmod == 0) continue;
            uint64_t val = modmul(K, qmod, n);
            if (val == n - 1) { /* K*q ≡ -1 */
                found = n;
                goto done;
            }
        }
    }
done:
    double wall = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (found)
        printf("HIT r=%llu checked_primes~%llu wall=%.3fs\n",
               (unsigned long long)found, (unsigned long long)checked, wall);
    else
        printf("NO_HIT R=%llu checked_primes~%llu wall=%.3fs\n",
               (unsigned long long)R, (unsigned long long)checked, wall);
    free(buf); free(small);
    return 0;
}
