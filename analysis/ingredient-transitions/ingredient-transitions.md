# Ingredient changes between consecutive prime doors

Exact census through 10,000,000; 664,576 consecutive prime pairs, starting at 5.

For each prime p > 3, d = p + chi3(p). Shared ingredients count distinct odd prime factors: 2 is universal and excluded; powers are retained in the example factorisations. Largest odd factor is defined as 1 for a pure power-of-two door.

## Exact restriction

For consecutive primes p < r, write d=m0(p), e=m0(r), Delta=e-d. Then gcd(d,e)=gcd(d,Delta). Every shared odd ingredient must therefore divide Delta. Since neither door contains 3, a gap Delta=2^a*3^b forces disjoint odd ingredients. This is true for all pairs, not just consecutive ones. Door gaps differ from prime gaps by chi3(r)-chi3(p).

## Census

| Measure | Count | Share of pairs |
|---|---:|---:|
| shared | 41,295 | 6.21% |
| disjoint | 623,281 | 93.79% |
| forced_disjoint_by_gap | 468,151 | 70.44% |
| largest_same | 1 | 0.00% |
| largest_up_10x | 199,213 | 29.98% |
| largest_down_10x | 197,479 | 29.72% |
| pure_two_endpoint | 18 | 0.00% |
| same_odd_support | 1 | 0.00% |

## By door gap

| Door gap | Pairs | Shared odd ingredients | Share |
|---:|---:|---:|---:|
| 2 | 58,621 | 0 | 0.00% |
| 4 | 58,979 | 0 | 0.00% |
| 6 | 99,987 | 0 | 0.00% |
| 8 | 54,431 | 0 | 0.00% |
| 10 | 42,352 | 11,852 | 27.98% |
| 12 | 65,513 | 0 | 0.00% |
| 14 | 25,099 | 3,982 | 15.87% |
| 16 | 35,394 | 0 | 0.00% |
| 18 | 43,851 | 0 | 0.00% |
| 20 | 19,451 | 7,786 | 40.03% |
| 22 | 22,084 | 2,075 | 9.40% |
| 24 | 27,170 | 0 | 0.00% |
| 26 | 13,255 | 1,032 | 7.79% |
| 28 | 12,249 | 3,497 | 28.55% |
| 30 | 21,741 | 5,597 | 25.74% |
| 32 | 6,721 | 0 | 0.00% |
| 34 | 6,364 | 332 | 5.22% |
| 36 | 10,194 | 0 | 0.00% |
| 38 | 5,318 | 281 | 5.28% |
| 40 | 4,498 | 1,342 | 29.84% |
| 42 | 7,180 | 1,239 | 17.26% |
| 44 | 2,326 | 270 | 11.61% |
| 46 | 2,779 | 108 | 3.89% |
| 48 | 3,784 | 0 | 0.00% |
| 50 | 1,449 | 553 | 38.16% |
| 52 | 2,048 | 224 | 10.94% |
| 54 | 2,403 | 0 | 0.00% |
| 56 | 1,052 | 161 | 15.30% |
| 58 | 1,072 | 39 | 3.64% |
| 60 | 1,834 | 440 | 23.99% |
| 62 | 559 | 12 | 2.15% |
| 64 | 543 | 0 | 0.00% |
| 66 | 973 | 65 | 6.68% |
| 68 | 524 | 32 | 6.11% |
| 70 | 358 | 155 | 43.30% |
| 72 | 468 | 0 | 0.00% |
| 74 | 194 | 3 | 1.55% |
| 76 | 218 | 20 | 9.17% |
| 78 | 362 | 24 | 6.63% |
| 80 | 100 | 46 | 46.00% |
| 82 | 165 | 5 | 3.03% |
| 84 | 247 | 48 | 19.43% |
| 86 | 71 | 0 | 0.00% |
| 88 | 66 | 6 | 9.09% |
| 90 | 141 | 29 | 20.57% |
| 92 | 39 | 3 | 7.69% |
| 94 | 37 | 0 | 0.00% |
| 96 | 65 | 0 | 0.00% |
| 98 | 36 | 7 | 19.44% |
| 100 | 29 | 7 | 24.14% |
| 102 | 34 | 3 | 8.82% |
| 104 | 12 | 2 | 16.67% |
| 106 | 21 | 0 | 0.00% |
| 108 | 26 | 0 | 0.00% |
| 110 | 11 | 5 | 45.45% |
| 112 | 11 | 3 | 27.27% |
| 114 | 11 | 0 | 0.00% |
| 116 | 4 | 0 | 0.00% |
| 118 | 7 | 0 | 0.00% |
| 120 | 10 | 4 | 40.00% |
| 122 | 4 | 0 | 0.00% |
| 124 | 3 | 1 | 33.33% |
| 126 | 8 | 2 | 25.00% |
| 128 | 1 | 0 | 0.00% |
| 130 | 2 | 1 | 50.00% |
| 132 | 5 | 2 | 40.00% |
| 134 | 2 | 0 | 0.00% |
| 136 | 1 | 0 | 0.00% |
| 138 | 2 | 0 | 0.00% |
| 142 | 2 | 0 | 0.00% |
| 146 | 2 | 0 | 0.00% |
| 148 | 1 | 0 | 0.00% |
| 152 | 1 | 0 | 0.00% |
| 154 | 1 | 0 | 0.00% |

## By endpoint band

| Larger endpoint band | Pairs | Shared | Forced disjoint | Largest grows 10x |
|---|---:|---:|---:|---:|
| (0, 10,000] | 1,226 | 3.83% | 84.91% | 17.86% |
| (10,000, 100,000] | 8,363 | 4.85% | 77.93% | 23.91% |
| (100,000, 1,000,000] | 68,906 | 5.61% | 73.87% | 27.62% |
| (1,000,000, 10,000,000] | 586,081 | 6.31% | 69.90% | 30.36% |

## Separation in prime positions

Descriptive overlap at fixed lag; not a significance test or a test of independence. Lag means number of steps in the prime sequence, not integer distance.

| Lag | Pairs | Share with common odd factor |
|---:|---:|---:|
| 1 | 664,576 | 6.21% |
| 2 | 664,575 | 10.38% |
| 3 | 664,574 | 11.28% |
| 4 | 664,573 | 11.46% |
| 5 | 664,572 | 11.59% |
| 10 | 664,567 | 11.53% |
| 20 | 664,557 | 11.78% |
| 50 | 664,527 | 11.92% |
| 100 | 664,477 | 11.89% |

## Abrupt changes below 10,000

| Consecutive primes | Door factorisations | Largest-factor multiplier |
|---|---|---:|
| 199 → 211 | 2^3 · 5^2 → 2^2 · 53 | 10.60 |
| 223 → 227 | 2^5 · 7 → 2 · 113 | 16.14 |
| 281 → 283 | 2^3 · 5 · 7 → 2^2 · 71 | 10.14 |
| 337 → 347 | 2 · 13^2 → 2 · 173 | 13.31 |
| 353 → 359 | 2^5 · 11 → 2 · 179 | 16.27 |
| 379 → 383 | 2^2 · 5 · 19 → 2 · 191 | 10.05 |
| 419 → 421 | 2 · 11 · 19 → 2 · 211 | 11.11 |
| 449 → 457 | 2^6 · 7 → 2 · 229 | 32.71 |
| 499 → 503 | 2^2 · 5^3 → 2 · 251 | 50.20 |
| 521 → 523 | 2^3 · 5 · 13 → 2^2 · 131 | 10.08 |
| 577 → 587 | 2 · 17^2 → 2 · 293 | 17.24 |
| 607 → 613 | 2^5 · 19 → 2 · 307 | 16.16 |
| 701 → 709 | 2^2 · 5^2 · 7 → 2 · 5 · 71 | 10.14 |
| 727 → 733 | 2^3 · 7 · 13 → 2 · 367 | 28.23 |
| 769 → 773 | 2 · 5 · 7 · 11 → 2^2 · 193 | 17.55 |

## Limits and checks

All primality and factorisation results use an exact sieve. Every factorisation was reconstructed and every adjacent pair checked against the gcd identity. Totals were cross-checked against the lag-one computation. Long-window averages do not show a periodic prime pattern. Local modular exclusions are exact, while the counts of which permitted positions are prime remain empirical here. Categories overlap: forced-disjoint is a subset of disjoint, and largest-factor events may overlap other categories. Bands assign each pair by its larger endpoint.

Reproduce: `python3 ingredient_transitions.py --limit 10000000`, with waits.py beside it.
