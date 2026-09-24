# Matched one-level continuity comparison

Exact sieve through 10,000,000. Observed population: 623,281 consecutive prime pairs with disjoint odd door support; 114,709 reconnect one level deeper.

Outcome: an odd factor of the earlier door divides the door of an odd factor of the later door. Under disjoint immediate support, all later factors are arriving and all earlier ones departing. Multiplicity is ignored.

Controls are real nonconsecutive prime pairs, not synthetic ingredient swaps. They also have disjoint odd support. Their exact door gap must appear in the observed population. Location is the dyadic band of the later door: [2^b, 2^(b+1)). Full matching additionally uses, separately for each door: exact count of distinct odd factors; presence of 5; presence of 7; and whether its largest odd factor exceeds its square root.

Within each stratum, compute the control outcome rate. Weight that rate by the number of observed pairs in the same stratum. Compare with the observed rate on those same supported strata. Thus the displayed control rate is standardized to the matched observed distribution, not the raw pooled control average. Rows requiring 10 or 30 controls are sensitivity checks for sparse strata.

| Matching | Minimum controls per stratum | Matched neighbours | Coverage | Observed continuity | Standardized control | Difference (percentage points) |
|---|---:|---:|---:|---:|---:|---:|
| Exact gap + location | 1 | 505,681 | 81.13% | 16.28% | 17.47% | -1.195 |
| Exact gap + location | 10 | 505,605 | 81.12% | 16.28% | 17.48% | -1.194 |
| Exact gap + location | 30 | 505,246 | 81.06% | 16.29% | 17.48% | -1.195 |
| Exact gap + location + both ingredient profiles | 1 | 501,484 | 80.46% | 16.17% | 16.17% | +0.004 |
| Exact gap + location + both ingredient profiles | 10 | 463,609 | 74.38% | 15.31% | 15.31% | +0.003 |
| Exact gap + location + both ingredient profiles | 30 | 394,651 | 63.32% | 14.17% | 14.09% | +0.080 |

## Coverage and interpretation

Door gaps 2 and 4 cannot have nonconsecutive prime controls: they correspond respectively to prime gaps 4 and 2 in these residue classes, with no intervening prime possible. Other strata can also lack controls. Results therefore concern the matched subset, not the complete 18.40% population.

This is an observational comparison. Consecutiveness encodes absence of intermediate primes; matching these summaries does not remove all arithmetic differences. Prime pairs share endpoints, controls are reused across sensitivity rows, and no independent-sample significance claim is made. A residual difference is not a causal adjacency effect. The profile definition was chosen before inspecting this run. The three minimum-count rows are sensitivity checks, not independent replications.

Full per-gap weighted counts are in JSON. Reproduce: python3 matched_continuity.py --limit 10000000 (requires bundled waits.py and ingredient_transitions.py). Run check_matched_continuity.py for independent small-window validation.
