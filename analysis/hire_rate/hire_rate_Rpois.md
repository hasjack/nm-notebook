# Thin hire-rate diagnostics: H/pi, R, R_Pois

## Definitions

- H(X) from `hire_rate_HX.csv` (exact values reused; not recomputed).
- pi(X) = number of primes <= X.
- H_over_pi = H(X)/pi(X).
- sparsity_pred = log(log(X))/log(X) (natural logs), X > e.
- R(X) = H(X)*(log X)^2 / (X*log(log X)) (recomputed; matches prior table).
- Li(X) = Ei(ln X) = offset logarithmic integral li(X), taken as
  `scipy.special.expi(log(X))` (principal-value exponential integral).
  Documented values embedded in `hire_rate_Rpois.c` after cross-check.
- PRIMARY: R_Pois(X) = H(X) / Sum_{q prime, q <= X/2} (1 - exp(-Li(X)/q)).
- OPTIONAL: R_Pois_qm1(X) = H(X) / Sum_{q prime, q <= X/2} (1 - exp(-Li(X)/(q-1))).

## Method

Single-pass segmented sieve (`hire_rate_Rpois.c`, gcc -O3 -march=native -ffast-math)
to X_max = 2e10 (segment 2^24). Counts pi(X) at each checkpoint. For each prime
q discovered with q <= X/2 for still-active checkpoints, accumulates both Poisson
sums on the fly (no full prime list stored). Peak RSS ~18 MB. Total wall ~112.4 s.

Sanity: pi(1e7)=664579, pi(1e8)=5761455, pi(1e9)=50847534 (exact match).

## Table

| X | H | pi | H/pi | sparsity_pred | R | R_Pois | R_Pois_qm1 | wall_s |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 10000 | 361 | 1229 | 0.293735 | 0.241069 | 1.379246 | 1.044340 | 1.044015 | 0.06 |
| 100000 | 2401 | 9592 | 0.250313 | 0.212237 | 1.302436 | 1.052438 | 1.052397 | 0.06 |
| 500000 | 9291 | 41538 | 0.223675 | 0.196178 | 1.242952 | 1.038335 | 1.038326 | 0.06 |
| 1000000 | 16688 | 78498 | 0.212591 | 0.190061 | 1.213048 | 1.025814 | 1.025810 | 0.06 |
| 5000000 | 68222 | 348513 | 0.195752 | 0.177374 | 1.186555 | 1.027917 | 1.027916 | 0.08 |
| 10000000 | 125661 | 664579 | 0.189084 | 0.172473 | 1.174335 | 1.026236 | 1.026235 | 0.09 |
| 50000000 | 527157 | 3001134 | 0.175653 | 0.162184 | 1.152420 | 1.025189 | 1.025189 | 0.28 |
| 100000000 | 980292 | 5761455 | 0.170147 | 0.158163 | 1.141710 | 1.022424 | 1.022423 | 0.57 |
| 500000000 | 4195019 | 26355867 | 0.159168 | 0.149637 | 1.123078 | 1.019467 | 1.019467 | 2.89 |
| 1000000000 | 7877140 | 50847534 | 0.154917 | 0.146273 | 1.115995 | 1.018264 | 1.018264 | 5.80 |
| 2200000000 | 16173662 | 107540122 | 0.150397 | 0.142648 | 1.108654 | 1.017071 | 1.017071 | 12.50 |
| 5000000000 | 34296996 | 234954223 | 0.145973 | 0.139081 | 1.101438 | 1.015742 | 1.015742 | 29.14 |
| 10000000000 | 64838984 | 455052511 | 0.142487 | 0.136222 | 1.095989 | 1.014864 | 1.014864 | 58.03 |
| 15000000000 | 94178863 | 670180516 | 0.140528 | 0.134609 | 1.092908 | 1.014316 | 1.014316 | 85.37 |
| 20000000000 | 122776796 | 882206716 | 0.139170 | 0.133491 | 1.090762 | 1.013908 | 1.013908 | 112.42 |

## Note on tip

At X=2e10, R_Pois ≈ 1.0139 is closer to 1 than R ≈ 1.0908 (and nearly identical to R_Pois_qm1).
