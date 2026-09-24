# One level deeper: ingredient continuity

Exact sieve through 10,000,000; 664,576 consecutive prime transitions.

For a preceding prime a and next prime p, let O be the odd prime factors of m0(a), and N those of m0(p). Arriving factors are N minus O. Expand each arriving prime q to the odd prime factors of its own door m0(q). A deeper connection is an intersection of that union with O. Both 2 and 3 are excluded; multiplicities are ignored. This is exactly one additional edge, not eventual connectivity.

## Observed transitions

| Measure | Count |
|---|---:|
| pairs | 664,576 |
| direct | 41,295 |
| deeper_any | 134,678 |
| disjoint | 623,281 |
| disjoint_with_deeper | 114,709 |
| disjoint_with_deeper_other_than_5 | 63,588 |
| disjoint_old_has_5 | 135,629 |
| disjoint_old_without_5 | 487,652 |
| disjoint_old_without_5_deeper | 47,797 |

Of directly disjoint transitions, 18.40% reconnect one level deeper. 10.20% reconnect through at least one prime other than 5.

When the preceding door has no factor 5, 47,797 of 487,652 directly disjoint transitions reconnect (9.80%).

## Local re-pairing comparison

Partition the directly disjoint transition records, in increasing prime order, into blocks of 1000 records. Keep each destination door and its one-level expansion fixed. Cyclically shift the origin ingredient sets within each block by each specified offset; discard re-pairings that now share a direct ingredient. This preserves local ingredients approximately and enforces direct disjointness, but changes the original gap distribution and is not a matched causal experiment or significance test. The offsets give descriptive sensitivity checks, not independent trials.

| Offset | Retained re-pairings | Deeper connection | Via non-5 ingredient | Origin lacks 5: deeper connection |
|---:|---:|---:|---:|---:|
| 137 | 560,214 | 16.12% | 8.94% | 8.91% |
| 389 | 560,610 | 16.15% | 8.97% | 8.93% |
| 613 | 560,477 | 16.15% | 8.98% | 8.94% |

## Shared ingredients at the deeper level

Counts overlap when a transition reconnects through several ingredients.

| Ingredient | Disjoint transitions reconnecting through it |
|---:|---:|
| 5 | 60,003 |
| 7 | 30,128 |
| 11 | 11,396 |
| 13 | 6,328 |
| 17 | 3,573 |
| 19 | 3,263 |
| 23 | 2,135 |
| 29 | 1,321 |
| 31 | 1,187 |
| 37 | 860 |
| 41 | 770 |
| 43 | 589 |
| 53 | 499 |
| 47 | 369 |
| 61 | 258 |
| 83 | 251 |
| 79 | 251 |
| 67 | 239 |
| 59 | 228 |
| 73 | 203 |

## Examples

| Consecutive primes | Previous odd ingredients | Next odd ingredients | Next factor → previous ingredient |
|---|---|---|---|
| 19 → 23 | (5,) | (11,) | [(11, [5])] |
| 41 → 43 | (5,) | (11,) | [(11, [5])] |
| 43 → 47 | (11,) | (23,) | [(23, [11])] |
| 79 → 83 | (5,) | (41,) | [(41, [5])] |
| 103 → 107 | (13,) | (53,) | [(53, [13])] |
| 163 → 167 | (41,) | (83,) | [(83, [41])] |
| 223 → 227 | (7,) | (113,) | [(113, [7])] |
| 281 → 283 | (5, 7) | (71,) | [(71, [5, 7])] |
| 349 → 353 | (5, 7) | (11,) | [(11, [5])] |
| 379 → 383 | (5, 19) | (191,) | [(191, [19, 5])] |
| 409 → 419 | (5, 41) | (11, 19) | [(11, [5]), (19, [5])] |
| 463 → 467 | (29,) | (233,) | [(233, [29])] |
| 499 → 503 | (5,) | (251,) | [(251, [5])] |
| 521 → 523 | (5, 13) | (131,) | [(131, [5, 13])] |
| 619 → 631 | (5, 31) | (79,) | [(79, [5])] |
| 859 → 863 | (5, 43) | (431,) | [(431, [43, 5])] |
| 883 → 887 | (13, 17) | (443,) | [(443, [17, 13])] |
| 941 → 947 | (5, 47) | (11, 43) | [(11, [5])] |

## Scope

These results establish how often one-step hidden overlap occurs in this window. They do not by themselves establish that adjacent doors are specially linked, forecast the next prime, or preserve exact powers. The 499 → 503 example is asserted by the script. Run check_deeper_connections.py for an independent trial-division check of the first 10,000.

Reproduce: python3 deeper_connections.py --limit 10000000. Requires the bundled waits.py and ingredient_transitions.py; standard library only.
