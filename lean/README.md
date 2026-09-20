# Lean: 3-free door / hire graph

Formal companion to the Natural Mathematics note on the **3-free door** of an odd prime and the **hire graph** `G` (star on 2, gold chords).

Lives inside the e-walk explorer repo so GitHub Pages can link at the sources. Proofs are checked with [Lean 4](https://lean-lang.org/) + [Mathlib](https://github.com/leanprover-community/mathlib4).

Barrel: `Hire.lean`. Layer map: [`LEMMA8_PROOF_MAP.md`](LEMMA8_PROOF_MAP.md).

## Status

| Module | Contents |
|--------|----------|
| `Hire/Doors.lean` | `chi3`, `m0` / `m1`, 3-free + even + `6 ∣ m1`, poster checks 11/13 |
| `Hire/HireSet.lean` | Finite owners `≤ X`, inductive `Hired`, **3 ∉ S**, directed `GoldArc`, hire bounds |
| `Hire/Graph.lean` | `G` / `GX` as Mathlib `SimpleGraph` on hired vertices; star on 2 + gold chords |
| `Hire/Finite.lean` | `Finite` / `Fintype` for `HireVertex (owners X)`; classical `DecidableRel` Adj |
| `Hire/StarLap.lean` | Pure star `Gstar` / `GXstar`; Lemma 7 style: Laplacian eigenvalues `n` and `1` |
| `Hire/Lemma8.lean` | Gold-free ⇒ `G = Gstar` + eigenvalue `1`; card-3 converse; card-4 chord keeps `1` |
| `Hire/Cone.lean` | Layer C block `[k -1ᵀ; -1 I+L']`; ordered shift `λᵢ = 1 + μᵢ`; Layer D `λ₂ = 1` iff gold-on-leaves disconnected |
| `Hire/WitnessXstar.lean` | Connecting window `X* = 92274421`; bridge `46137211`; island `M₁₉` facts by `native_decide` |
| `Hire/WeakQ2.lean` | Statement scaffolding for 2-power-door Mersennes in `comp(5)` (proof deferred) |
| `Hire/GoldBridge.lean` | Strong Q2, 0 sorry: Dirichlet bridge ⇒ every odd prime ≠ 3 in infinite gold component of 5 |
| `Hire/GoldDisconnects.lean` | Sequel A: first-owner isolation of 2-power doors; sink chains; infinitude package |
| `Hire/Dirichlet.lean` | Stub: `Nat.forall_exists_prime_gt_and_eq_mod` + `eventually_hired` placeholder |
| `Hire/FltTwoDoor.lean` | Exploratory FLT × two-door cheap-kill. **Not** imported by `Hire.lean` |
| `Hire/HireGraph.lean` | Early arithmetic sketch; superseded by the spine above |

`Cone.lean` proves `eigenvalues_lapMatrix_le_card` (complete-graph comparison) because Mathlib did not have a Laplacian bound by `|V|`. Same lemma is [mathlib4#43953](https://github.com/leanprover-community/mathlib4/pull/43953). Keep the local copy until that merges.

## Build

Needs [elan](https://github.com/leanprover/elan):

```bash
cd lean
lake update
lake exe cache get   # Mathlib cache; skip if unavailable
lake build
```

First run downloads the Lean toolchain and Mathlib (large).
