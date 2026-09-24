# Preserving powers through an arriving prime

Exact sieve of consecutive prime doors through 10,000,000. Directly disjoint odd support is required throughout.

For a departing odd factor q appearing with exponent e >= 2 in the preceding door, test whether any arriving prime r satisfies q | m0(r), and whether any satisfies q^e | m0(r). Full preservation means at least the old exponent, not necessarily equality. Whole-odd-part preservation requires a SINGLE arriving prime whose door is divisible by the entire odd part of the old door. The vacuous odd part 1 is excluded.

## Counts

| Measure | Count |
|---|---:|
| disjoint | 623,281 |
| whole_odd_part_preserved_all | 8,924 |
| nonempty_old_odd_part | 623,271 |
| repeated_factor_opportunities | 58,666 |
| repeated_factor_reconnects | 18,285 |
| full_power_preserved | 2,927 |
| whole_odd_part_preserved_repeated | 1,336 |

Among 58,666 transitions with at least one repeated departing odd factor: 31.17% reconnect through a repeated factor, 4.99% preserve at least one full power, and 2.28% preserve the entire old odd part through a single arriving prime. Among the 18,285 repeated-factor reconnections, 16.01% preserve a full power. These are pair-level counts; multiple successes in one pair count once.

## By exponent

This table counts (transition, departing repeated prime) opportunities; rows can overlap at transition level.

| Departing exponent | Opportunities | Reconnect through prime | Preserve full power | Full among reconnected |
|---:|---:|---:|---:|---:|
| 2 | 52,298 | 15,336 | 2,732 | 17.81% |
| 3 | 7,062 | 2,571 | 229 | 8.91% |
| 4 | 1,181 | 458 | 21 | 4.59% |
| 5 | 222 | 78 | 8 | 10.26% |
| 6 | 43 | 15 | 1 | 6.67% |
| 7 | 9 | 3 | 0 | 0.00% |
| 8 | 1 | 0 | 0 | — |

## Matched comparison

Controls: real nonconsecutive prime pairs, also with disjoint odd support and repeated departing factors. Match exact door gap, dyadic location band of the later door, and both doors' profiles: distinct odd-factor count, EXACT exponents of 5 and 7, whether the largest factor exceeds sqrt(door), number of repeated odd factors, and maximum odd exponent. Control rates within each stratum are weighted by observed pair counts. These profiles are stricter than the previous support-only census.

| Minimum controls | Matched observed pairs | Coverage | Full-power observed | Full-power controls | Whole odd part observed | Whole odd part controls |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 35,209 | 60.02% | 3.39% | 3.46% | 0.46% | 0.55% |
| 10 | 15,186 | 25.89% | 3.80% | 3.95% | 0.30% | 0.34% |
| 30 | 5,775 | 9.84% | 4.35% | 4.03% | 0.05% | 0.05% |

## Examples

| Consecutive primes | Doors | Full-power paths | Entire odd part? |
|---|---|---|---|
| 499 → 503 | 500 → 502 | 251: 5^3 divides 250 | True |
| 2801 → 2803 | 2800 → 2804 | 701: 5^2 divides 700 | True |
| 7699 → 7703 | 7700 → 7702 | 3851: 5^2 divides 3850 | True |
| 9463 → 9467 | 9464 → 9466 | 4733: 13^2 divides 4732 | True |

## Limits

Door gaps 2 and 4 have no nonconsecutive prime controls. This includes 499 → 503. Matching therefore cannot assess adjacency enhancement for that example; sparse profiles further reduce coverage. Matched rates refer to their own subsets, not the complete census. Paired records share endpoints; these are descriptive comparisons, not independent significance tests or causal estimates. Exact identities can force some examples: if old door=4A, next door=4A+2 and r=2A+1 is an arriving prime with m0(r)=2A, it preserves all of A. Such constructions do not establish a general law of inheritance.

Reproduce: python3 power_continuity.py --limit 10000000 (with waits.py and ingredient_transitions.py). Independent trial-division validation: python3 check_power_continuity.py.
