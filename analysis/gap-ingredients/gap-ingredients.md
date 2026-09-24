# Door gaps and arriving ingredients

Exact sieve through 10,000,000; consecutive primes p > 3. New ingredients are distinct odd prime factors present in the next door but absent from the preceding door. Departing ingredients reverse that comparison; powers are not counted as new distinct ingredients.

## What is forced

Every shared odd factor q satisfies 2q <= Delta, since q divides the even door gap Delta. New factors satisfy Delta = -d (mod q), but this does not bound q by the gap: q can be much larger than Delta. These are exact arithmetic identities, not predictive fits.

## Measurements

All percentages use all pairs in each row. Medians of arriving/departing factors exclude pairs without such factors. Log-size fraction log(q)/log(next door) expresses factor size relative to the door; 0.5 means its square root. Gap bins are fixed in advance.

| Band | Door gap | Pairs | Median largest arriving | Median largest departing | Median log-size fraction | Arrival > sqrt(door) | Arrival > door^0.75 | Tenfold largest-factor increase |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| all | 2–8 | 272,018 | 8,923 | 8,807 | 0.610 | 69.66% | 29.27% | 29.97% |
| <=100k | 2–8 | 5,294 | 557 | 509 | 0.615 | 69.64% | 30.45% | 23.59% |
| all | 10–18 | 212,209 | 10,181 | 10,321 | 0.616 | 70.66% | 30.41% | 29.98% |
| <=100k | 10–18 | 3,074 | 601 | 656 | 0.610 | 69.97% | 31.23% | 22.84% |
| all | 20–38 | 144,547 | 10,957 | 11,071 | 0.616 | 70.64% | 30.41% | 29.93% |
| <=100k | 20–38 | 1,146 | 803 | 739 | 0.627 | 69.72% | 31.41% | 22.08% |
| all | 40–78 | 34,624 | 12,619 | 12,239 | 0.618 | 71.06% | 30.86% | 30.14% |
| <=100k | 40–78 | 75 | 739 | 1,217 | 0.595 | 74.67% | 25.33% | 20.00% |
| 100k–1m | 10–18 | 22,523 | 3,121 | 3,203 | 0.619 | 70.93% | 30.86% | 27.51% |
| 100k–1m | 20–38 | 12,730 | 3,187 | 3,083 | 0.615 | 70.51% | 30.38% | 27.56% |
| 100k–1m | 2–8 | 31,645 | 2,713 | 2,713 | 0.608 | 69.39% | 29.16% | 27.71% |
| 100k–1m | 40–78 | 1,977 | 3,673 | 3,229 | 0.622 | 71.78% | 30.25% | 27.92% |
| all | 80+ | 1,178 | 15,774 | 13,553 | 0.626 | 69.35% | 30.81% | 30.65% |
| 100k–1m | 80+ | 31 | 10,753 | 18,973 | 0.679 | 77.42% | 35.48% | 22.58% |
| 1m–10m | 20–38 | 130,671 | 12,804 | 12,976 | 0.616 | 70.67% | 30.40% | 30.23% |
| 1m–10m | 2–8 | 235,079 | 11,399 | 11,251 | 0.610 | 69.70% | 29.25% | 30.42% |
| 1m–10m | 40–78 | 32,572 | 13,963 | 13,337 | 0.618 | 71.01% | 30.91% | 30.30% |
| 1m–10m | 10–18 | 186,612 | 12,601 | 12,763 | 0.616 | 70.64% | 30.34% | 30.40% |
| 1m–10m | 80+ | 1,147 | 15,791 | 12,917 | 0.622 | 69.14% | 30.69% | 30.86% |

## Correlations

Pearson correlation of log(door gap) with log(largest arriving odd factor). The partial correlation removes each variable's linear association with log(next door). Pairs with no arriving odd factor are excluded. This is an exploratory descriptive adjustment, not a causal model or a forecast validation.

| Band | Pairs | Raw correlation | Controlling log door size |
|---|---:|---:|---:|
| all | 664,560 | 0.04099 | 0.02380 |
| <=100k | 9,579 | 0.06733 | 0.02618 |
| 100k–1m | 68,902 | 0.03735 | 0.03053 |
| 1m–10m | 586,079 | 0.02801 | 0.02315 |

## Limits

This tests gap size and ingredient size, not every possible residue pattern or return-time law. Exact congruence restrictions can remain despite weak linear correlations. Adjacent transitions overlap, and the dataset is observational and bounded. No claim of random or independent prime factors is made. Exact-gap data are included in JSON.

Checks: every shared factor obeys 2q <= Delta, every arriving factor divides the next door. Pair counts and sqrt-threshold counts are independently cross-checked in the small window during this run.

Reproduce: python3 gap_ingredients.py --limit 10000000, with waits.py and ingredient_transitions.py alongside.
