# Waiting inside the door lattice

Exact sieve through 10,000,000; ingredients 5, 7, 49 and 11. No probable-prime tests.

A miss is an eligible composite position between consecutive prime hires. A numeric gap is the difference between the prime endpoints. After filtering, a miss means a composite not eliminated by primes at most 100. A small prime is never eliminated merely because it equals the trial divisor.

Only intervals with both endpoints inside a band enter its wait distribution. Leading/trailing boundary runs are reported separately in JSON. First hires are not pooled with subsequent waits. Powers and different ingredients overlap, so lanes are not independent datasets.

## Whole-window census

| Q | Candidates | Prime hires | Mean misses | 90th percentile | Maximum misses | After ≤100 sieve: mean misses |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 666,666 | 166,111 | 3.013 | 7 | 41 | 0.811 |
| 7 | 476,190 | 110,749 | 3.300 | 8 | 41 | 0.811 |
| 49 | 68,027 | 15,771 | 3.313 | 8 | 33 | 0.816 |
| 11 | 303,030 | 66,487 | 3.558 | 9 | 37 | 0.810 |

First hires (kept separate): Q=5: 11, 0 preceding misses; Q=7: 13, 0 preceding misses; Q=49: 97, 0 preceding misses; Q=11: 23, 0 preceding misses. All four happen to succeed at their first eligible position; this selection is not representative of all ingredients.

## Moving along the number line

| Q | Band (lower exclusive) | Mean misses | After sieve: mean misses | After sieve: immediate next survivor prime | Fitted independent baseline |
|---:|---|---:|---:|---:|---:|
| 5 | (0, 10,000] | 1.188 | 0.000 | 100.00% | 100.00% |
| 5 | (10,000, 100,000] | 1.876 | 0.272 | 78.61% | 78.60% |
| 5 | (100,000, 1,000,000] | 2.487 | 0.583 | 63.55% | 63.18% |
| 5 | (1,000,000, 10,000,000] | 3.095 | 0.847 | 54.02% | 54.13% |
| 7 | (0, 10,000] | 1.312 | 0.000 | 100.00% | 100.00% |
| 7 | (10,000, 100,000] | 2.065 | 0.265 | 78.68% | 79.04% |
| 7 | (100,000, 1,000,000] | 2.733 | 0.580 | 63.47% | 63.28% |
| 7 | (1,000,000, 10,000,000] | 3.388 | 0.848 | 54.04% | 54.12% |
| 49 | (0, 10,000] | 1.333 | 0.000 | 100.00% | 100.00% |
| 49 | (10,000, 100,000] | 2.102 | 0.286 | 76.53% | 77.87% |
| 49 | (100,000, 1,000,000] | 2.756 | 0.589 | 62.48% | 62.82% |
| 49 | (1,000,000, 10,000,000] | 3.398 | 0.851 | 54.06% | 54.01% |
| 11 | (0, 10,000] | 1.400 | 0.000 | 100.00% | 100.00% |
| 11 | (10,000, 100,000] | 2.239 | 0.262 | 80.14% | 79.28% |
| 11 | (100,000, 1,000,000] | 2.955 | 0.580 | 63.95% | 63.24% |
| 11 | (1,000,000, 10,000,000] | 3.652 | 0.847 | 54.08% | 54.15% |

## Residue transitions

| Q | Switch class | Same class | Switch share | Equal-hazard independent baseline |
|---:|---:|---:|---:|---:|
| 5 | 97,860 | 68,250 | 58.91% | 57.12% |
| 7 | 64,458 | 46,290 | 58.20% | 56.58% |
| 49 | 9,292 | 6,478 | 58.92% | 56.56% |
| 11 | 39,071 | 27,415 | 58.77% | 56.16% |

Classes alternate at candidate level. With M missed candidate positions, a successful transition switches class iff M is even. Under an independent constant success probability h, its switching fraction would be 1/(2−h), not 1/2. The comparison assumes equal hazards for the two classes; their empirical counts are in the JSON.

## Accounting for the small-prime blocking pattern

Keep the actual candidate positions surviving the <=100 sieve, including their residue-class order, and independently label each a success with the band's observed survivor success rate. The expected transition counts below are calculated analytically, not by random simulation. This is a fitted comparison, not a significance test.

| Q | Band | Observed switch share | Raw independent model | Sieve-aware independent model |
|---:|---|---:|---:|---:|
| 5 | (1,000,000, 10,000,000] | 58.70% | 56.95% | 58.58% |
| 7 | (1,000,000, 10,000,000] | 58.05% | 56.43% | 58.18% |
| 49 | (1,000,000, 10,000,000] | 58.92% | 56.41% | 58.63% |
| 11 | (1,000,000, 10,000,000] | 58.46% | 56.02% | 58.91% |

## Composite blockers

A composite is assigned only its smallest prime factor; the categories are disjoint. The >100 category is the surviving composite population, not an assertion of primality.

| Q | Composites | Blocked by primes ≤100 | Share removed | Most frequent smallest blockers |
|---:|---:|---:|---:|---|
| 5 | 500,555 | 365,793 | 73.08% | 7: 95,238; 11: 51,947; 13: 39,960; 17: 28,207; 19: 23,752 |
| 7 | 365,441 | 275,618 | 75.42% | 5: 95,238; 11: 34,632; 13: 26,639; 17: 18,805; 19: 15,835 |
| 49 | 52,256 | 39,384 | 75.37% | 5: 13,606; 11: 4,947; 13: 3,806; 17: 2,686; 19: 2,263 |
| 11 | 236,543 | 182,672 | 77.23% | 5: 60,606; 7: 34,632; 13: 15,984; 17: 11,283; 19: 9,502 |

## Longest complete waits

| Q | Prime endpoints | Missed opportunities | Surviving misses after sieve | Number-line gap |
|---:|---|---:|---:|---:|
| 5 | 3,542,141 → 3,542,771 | 41 | 13 | 630 |
| 7 | 4,456,339 → 4,457,221 | 41 | 10 | 882 |
| 49 | 5,731,433 → 5,736,431 | 33 | 9 | 4,998 |
| 11 | 1,583,053 → 1,584,307 | 37 | 8 | 1,254 |

## Interpretation limits

The 7 and 49 lanes have nearly equal waits when measured in candidate opportunities. This is consistent with the classical density calculation: the candidate count is asymptotic to X/(3Q), while covered prime count is asymptotic to Li(X)/phi(Q). For Q=q^a, the ratio Q/phi(Q)=q/(q−1) does not depend on a. Higher powers thin both candidate positions and prime hits. Their number-line gaps still grow.

Below 10,000, removal by all primes at most 100 removes every composite, since a composite has a prime factor at most its square root. Zero post-sieve misses in that band are therefore guaranteed, not an empirical discovery.

The geometric baseline is descriptive. Prime density changes across broad bands, residue classes have local restrictions, and pair correlations can remain after sieving. These comparisons do not establish a new law, statistical significance, or a bound on the next prime. The mean wait is largely determined by the number of successes: it is not by itself evidence of independence. Inspect zero-miss frequencies, tails, transitions and blockers separately.

For a blocking prime r not dividing 6Q, each candidate branch hits one blocked residue of its branch index modulo r. Thus the blocking pattern repeats with r within each branch, although composites may have several blockers. Removing small blockers leaves larger ones; it does not create independent trials.

Reproduce: `python3 analysis/door-coverage/waits.py --limit 10000000`. Full histograms, class counts, censored edges and factor counts are in `waits-results.json`.
