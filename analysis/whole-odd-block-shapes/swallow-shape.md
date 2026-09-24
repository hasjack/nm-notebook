# Shape of whole-odd-part preservation

Exact census through 10,000,000. This is the SAME cohort as the full-power run: consecutive prime doors with disjoint odd supports, with a repeated odd factor in the preceding door, and at least one arriving prime preserving its entire odd part.

Write the preceding door as 2^u A with A odd. For EACH arriving prime r satisfying A | m0(r), decompose m0(r)/A uniquely as 2^k B, where B is odd. The proposed pure shape is B=1. If B>1, the door preserves A and carries additional odd multiplicity; those factors may repeat factors already in A, so they need not be new prime species. Every k is at least 1.

## Transition and witness counts

| Measure | Count |
|---|---:|
| witnesses | 1,336 |
| pure_witnesses | 1,336 |
| transitions | 1,336 |
| pure_transitions | 1,336 |
| pure_only | 1,336 |
| extra_only | 0 |
| both_types | 0 |

100.00% of preserving transitions have at least one pure witness. 100.00% of all witnesses are pure.

## Pure-shape powers of two

| k in m0(r)=2^k A | Witnesses | Share of pure witnesses |
|---:|---:|---:|
| 1 | 678 | 50.75% |
| 2 | 325 | 24.33% |
| 3 | 178 | 13.32% |
| 4 | 67 | 5.01% |
| 5 | 39 | 2.92% |
| 6 | 29 | 2.17% |
| 7 | 7 | 0.52% |
| 8 | 7 | 0.52% |
| 9 | 4 | 0.30% |
| 10 | 2 | 0.15% |

## Odd multipliers

| B in m0(r)=2^k A B | Witnesses |
|---:|---:|
| 1 | 1,336 |

## First examples with an extra odd multiplier

| Consecutive primes | Old odd block A | Arriving r | m0(r) | k | B |
|---|---:|---:|---:|---:|---:|

## Interpretation and checks

This classifies selected successful whole-block preservations; it is not the prevalence of the shape among all transitions. It does not compare against a matched baseline or establish an adjacency effect. The other whole-odd-part preservations with squarefree preceding odd block are deliberately excluded to retain the original 1,336-event denominator.

Each quotient is checked exactly. Transition categories partition the cohort, and witness multiplicities reconstruct the witness count. The 10-million run asserts agreement with the previous 1,336 result. JSON contains every event and every preserving prime, including multiplicities and extra odd factors.

Run: python3 swallow_shape.py --limit 10000000 (keep waits.py, ingredient_transitions.py and the prior power-continuity.json beside it).


## Stronger observed normal form

1,336 of 1,336 witnesses also satisfy: old door = 2^(v+k) A; next door = 2^v(2^k A+1); arriving prime r = 2^k A+1, with k,v >= 1 and r congruent to 2 modulo 3. The door gap is therefore exactly 2^v. This is an observed classification within this census, not an asserted universal theorem.

Normal-form door gaps (gap: witness count): {2: 753, 4: 360, 8: 173, 16: 42, 32: 8}.

Independent verification of every listed transition and witness: python3 check_swallow_shape.py.
