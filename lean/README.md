# Lean: 3-free door / hire graph

Formal companion to the **3-free door** of an odd prime and the **hire graph** `G` (star on 2, gold chords).

Lives inside the e-walk explorer repo so GitHub Pages can link at the sources. Proofs are checked with [Lean 4](https://lean-lang.org/) + [Mathlib](https://github.com/leanprover-community/mathlib4).

Barrel: `Hire.lean`. Layer map: [`LEMMA8_PROOF_MAP.md`](LEMMA8_PROOF_MAP.md).

## Status

| Module | Contents |
|--------|----------|
| `Hire/Doors.lean` | `chi3`, `m0` / `m1`, 3-free + even + `6 ∣ m1`, poster checks 11/13; Saturday: `mid_gap_m0`, `chi3_eq_legendreSym_neg_three` |
| `Hire/HireSet.lean` | Finite owners `≤ X`, inductive `Hired`, **3 ∉ S**, directed `GoldArc`, hire bounds |
| `Hire/Graph.lean` | `G` / `GX` as Mathlib `SimpleGraph` on hired vertices; star on 2 + gold chords |
| `Hire/Finite.lean` | `Finite` / `Fintype` for `HireVertex (owners X)`; classical `DecidableRel` Adj |
| `Hire/StarLap.lean` | Pure star `Gstar` / `GXstar`; Lemma 7 style: Laplacian eigenvalues `n` and `1` |
| `Hire/Lemma8.lean` | Gold-free ⇒ `G = Gstar` + eigenvalue `1`; card-3 converse; card-4 chord keeps `1` |
| `Hire/Cone.lean` | Layer C block `[k -1ᵀ; -1 I+L']`; ordered shift `λᵢ = 1 + μᵢ`; Layer D `λ₂ = 1` iff gold-on-leaves disconnected |
| `Hire/WitnessXstar.lean` | Connecting window `X* = 92274421`; bridge `46137211`; island `M₁₉` facts by `native_decide` |
| `Hire/WeakQ2.lean` | Definitions: `IsTwoPowerDoor`, `UndirectedGold` (endpoints other than `2` and `3`), `InGoldComponentOf5`. No sorry |
| `Hire/GoldBridge.lean` | Strong Q2, 0 sorry: Dirichlet bridge ⇒ every odd prime ≠ 3 in infinite gold component of 5 |
| `Hire/GoldDisconnects.lean` | Sequel A: size bound `2q ≤ p + 1`; door closure; descent; sinks are the 2-power doors, and gold is connected iff those sinks are joined; first-owner isolation; infinitude package |
| `Hire/Dirichlet.lean` | `exists_owner_prime_in_AP` (Mathlib primes in AP). No sorry |
| `Hire/TwoClassCoverage.lean` | `Q ∣ m0 p` iff `p` is in one of two classes mod `6Q` |
| `Hire/InfiniteHire.lean` | Infinitely many owners of odd `Q` with `3 ∤ Q`; `eventually_hired` |
| `Hire/FltTwoDoor.lean` | Exploratory FLT × two-door cheap-kill. **Not** imported by `Hire.lean` |
| `Hire/HireGraph.lean` | Early arithmetic sketch; superseded by the spine above |

`Cone.lean` proves `eigenvalues_lapMatrix_le_card` because the pinned Mathlib has no Laplacian bound by `|V|`. The local proof follows the reviewed form of [mathlib4#43953](https://github.com/leanprover-community/mathlib4/pull/43953): `lapMatrix_toLinearMap₂'_mono`, then `le_top`, then one `grw`, over a linearly ordered field. Delete the local copy when that PR is in the toolchain.

## Build

Needs [elan](https://github.com/leanprover/elan):

```bash
cd lean
lake update
lake exe cache get   # Mathlib cache; skip if unavailable
lake build
```

First run downloads the Lean toolchain and Mathlib (large).
