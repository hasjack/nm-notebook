# Prime-power firing census

Exact sieve: primes 3 < p <= 10,000,000. 664,577 primes; bases (5, 7, 11, 13, 17, 19). All powers with 2q^e-1 <= X included, including lanes with no hits.

A cumulative firing means q^e divides m0(p). An exact firing means q^e divides it and q^(e+1) does not. Eligible positions use the two residues 2Q-chi3(Q), 4Q+chi3(Q) modulo 6Q. Exact-power opportunities also exclude positions divisible by the next power in their door. Percentages are prime hits divided by eligible positions, not by all integers.

Waits include only consecutive hits inside the window. Initial misses are separate; trailing runs and missing first appearances are censored. A zero-hit lane does not mean it never fires. Sparse high powers cannot support stable rate estimates. Lanes overlap; their counts are not independent.

| Ingredient | First prime | Prior misses | Hits | Exact hits | Eligible positions | Success | Mean number-line gap | Mean missed positions |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 5^1 = 5 | 11 | 0 | 166,111 | 132,914 | 666,666 | 24.92% | 60.20 | 3.013 |
| 5^2 = 25 | 101 | 1 | 33,197 | 26,592 | 133,333 | 24.90% | 301.22 | 3.016 |
| 5^3 = 125 | 251 | 0 | 6,605 | 5,292 | 26,666 | 24.77% | 1,514.01 | 3.037 |
| 5^4 = 625 | 1249 | 0 | 1,313 | 1,037 | 5,333 | 24.62% | 7,620.05 | 3.064 |
| 5^5 = 3,125 | 31249 | 3 | 276 | 219 | 1,066 | 25.89% | 35,931.82 | 2.833 |
| 5^6 = 15,625 | 31249 | 0 | 57 | 46 | 213 | 26.76% | 175,781.25 | 2.750 |
| 5^7 = 78,125 | 1093751 | 4 | 11 | 9 | 42 | 26.19% | 718,749.80 | 2.100 |
| 5^8 = 390,625 | 3124999 | 2 | 2 | 1 | 8 | 25.00% | 4,687,500.00 | 3.000 |
| 5^9 = 1,953,125 | 7812499 | 1 | 1 | 1 | 2 | 50.00% | — | — |
| 7^1 = 7 | 13 | 0 | 110,749 | 94,978 | 476,190 | 23.26% | 90.29 | 3.300 |
| 7^2 = 49 | 97 | 0 | 15,771 | 13,519 | 68,027 | 23.18% | 634.03 | 3.313 |
| 7^3 = 343 | 1373 | 1 | 2,252 | 1,934 | 9,718 | 23.17% | 4,439.34 | 3.314 |
| 7^4 = 2,401 | 4801 | 0 | 318 | 276 | 1,388 | 22.91% | 31,508.40 | 3.375 |
| 7^5 = 16,807 | 33613 | 0 | 42 | 33 | 198 | 21.21% | 241,036.98 | 3.780 |
| 7^6 = 117,649 | 470597 | 1 | 9 | 6 | 28 | 32.14% | 970,604.25 | 1.750 |
| 7^7 = 823,543 | 3294173 | 1 | 3 | 3 | 4 | 75.00% | 2,470,629.00 | 0.000 |
| 11^1 = 11 | 23 | 0 | 66,487 | 60,473 | 303,030 | 21.94% | 150.41 | 3.558 |
| 11^2 = 121 | 241 | 0 | 6,014 | 5,474 | 27,548 | 21.83% | 1,662.69 | 3.580 |
| 11^3 = 1,331 | 2663 | 0 | 540 | 491 | 2,504 | 21.57% | 18,535.22 | 3.642 |
| 11^4 = 14,641 | 117127 | 2 | 49 | 46 | 228 | 21.49% | 201,313.75 | 3.583 |
| 11^5 = 161,051 | 6442039 | 13 | 3 | 3 | 21 | 14.29% | 1,449,459.00 | 2.000 |
| 11^6 = 1,771,561 | not seen | — | 0 | 0 | 2 | 0.00% | — | — |
| 13^1 = 13 | 53 | 1 | 55,427 | 51,185 | 256,410 | 21.62% | 180.42 | 3.626 |
| 13^2 = 169 | 337 | 0 | 4,242 | 3,913 | 19,724 | 21.51% | 2,357.47 | 3.650 |
| 13^3 = 2,197 | 30757 | 4 | 329 | 306 | 1,517 | 21.69% | 30,114.98 | 3.570 |
| 13^4 = 28,561 | 285611 | 3 | 23 | 22 | 117 | 19.66% | 418,029.09 | 3.864 |
| 13^5 = 371,293 | 2970343 | 2 | 1 | 1 | 9 | 11.11% | — | — |
| 13^6 = 4,826,809 | not seen | — | 0 | 0 | 1 | 0.00% | — | — |
| 17^1 = 17 | 67 | 1 | 41,534 | 39,084 | 196,078 | 21.18% | 240.77 | 3.721 |
| 17^2 = 289 | 577 | 0 | 2,450 | 2,316 | 11,534 | 21.24% | 4,082.82 | 3.709 |
| 17^3 = 4,913 | 78607 | 5 | 134 | 125 | 678 | 19.76% | 74,249.10 | 4.038 |
| 17^4 = 83,521 | 1169293 | 4 | 9 | 9 | 40 | 22.50% | 897,851.00 | 2.625 |
| 17^5 = 1,419,857 | not seen | — | 0 | 0 | 2 | 0.00% | — | — |
| 19^1 = 19 | 37 | 0 | 36,880 | 34,954 | 175,438 | 21.02% | 271.15 | 3.757 |
| 19^2 = 361 | 2887 | 2 | 1,926 | 1,812 | 9,234 | 20.86% | 5,192.77 | 3.795 |
| 19^3 = 6,859 | 27437 | 1 | 114 | 109 | 486 | 23.46% | 87,406.73 | 3.248 |
| 19^4 = 130,321 | 3648989 | 9 | 5 | 4 | 26 | 19.23% | 1,563,852.00 | 3.000 |
| 19^5 = 2,476,099 | 9904397 | 1 | 1 | 1 | 2 | 50.00% | — | — |

## Companions

Counts below are for cumulative lanes. Other odd primes exclude the lane base and the universal factor 2. A door may contribute to multiple companion counts.

| Lane | Top three other odd companions (share of hires) | No other odd prime |
|---|---|---:|
| 5^1 | 7: 27,734 (16.70%); 11: 16,582 (9.98%); 13: 13,754 (8.28%) | 38 |
| 5^2 | 7: 5,533 (16.67%); 11: 3,293 (9.92%); 13: 2,733 (8.23%) | 26 |
| 5^3 | 7: 1,123 (17.00%); 11: 660 (9.99%); 13: 548 (8.30%) | 18 |
| 7^1 | 5: 27,734 (25.04%); 11: 11,103 (10.03%); 13: 9,241 (8.34%) | 32 |
| 7^2 | 5: 3,940 (24.98%); 11: 1,573 (9.97%); 13: 1,329 (8.43%) | 23 |
| 7^3 | 5: 556 (24.69%); 11: 223 (9.90%); 13: 186 (8.26%) | 14 |
| 11^1 | 5: 16,582 (24.94%); 7: 11,103 (16.70%); 13: 5,566 (8.37%) | 15 |
| 11^2 | 5: 1,492 (24.81%); 7: 1,013 (16.84%); 13: 512 (8.51%) | 9 |
| 11^3 | 5: 128 (23.70%); 7: 97 (17.96%); 13: 50 (9.26%) | 5 |
| 13^1 | 5: 13,754 (24.81%); 7: 9,241 (16.67%); 11: 5,566 (10.04%) | 13 |
| 13^2 | 5: 1,064 (25.08%); 7: 706 (16.64%); 11: 442 (10.42%) | 8 |
| 13^3 | 5: 78 (23.71%); 7: 55 (16.72%); 11: 32 (9.73%) | 3 |
| 17^1 | 5: 10,346 (24.91%); 7: 6,905 (16.62%); 11: 4,177 (10.06%) | 14 |
| 17^2 | 5: 612 (24.98%); 7: 389 (15.88%); 11: 261 (10.65%) | 8 |
| 17^3 | 5: 39 (29.10%); 7: 24 (17.91%); 11: 13 (9.70%) | 4 |
| 19^1 | 5: 9,211 (24.98%); 7: 6,203 (16.82%); 11: 3,689 (10.00%) | 12 |
| 19^2 | 5: 505 (26.22%); 7: 323 (16.77%); 11: 202 (10.49%) | 7 |
| 19^3 | 5: 32 (28.07%); 7: 21 (18.42%); 11: 13 (11.40%) | 3 |

## Interpretation

Compare powers within the same base using success per eligible position as well as raw number-line gaps. Higher powers thin the opportunity lattice. For example, progression counts suggest a q-fold reduction in opportunities for each extra power; the measured next-power share is provided in the data. This finite census does not establish an asymptotic theorem or independence.

The next-power share uses cumulative hits as its denominator; exact shares are its complement. Companion percentages also use cumulative hits. The CSV gives all lanes; JSON additionally includes gap quantiles, censored boundaries, exact-lane waits, first-door factorisations and companion counts.

Independent trial division through 10000; full-window nested-count and door-factorisation checks.

Reproduce with Python 3: `python3 firing.py --limit 10000000` (keep waits.py alongside). No third-party dependencies, PRP tests, or network needed.
