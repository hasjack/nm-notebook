# Lean: 3-free door / hire graph

Formal companion to the Natural Mathematics note on the **3-free door** of an odd prime and the **hire graph** `G` (star on 2, gold chords).

Lives inside the e-walk explorer repo so GitHub Pages can link at the sources. Proofs are checked with [Lean 4](https://lean-lang.org/) + [Mathlib](https://github.com/leanprover-community/mathlib4).

## Status

| Module | Contents |
|--------|----------|
| `Hire/Doors.lean` | `chi3`, `m0` / `m1`, 3-free + even + `6 ∣ m1`, poster checks 11/13 |
| `Hire/HireSet.lean` | Finite owners `≤ X`, inductive `Hired`, **3 ∉ S**, directed `GoldArc`, hire bounds |
| `Hire/Graph.lean` | `G` / `GX` as Mathlib `SimpleGraph` on hired vertices; star on 2 + gold chords |
| `Hire/Finite.lean` | `Finite` / `Fintype` for `HireVertex (owners X)`; classical `DecidableRel` Adj |
| `Hire/StarLap.lean` | Pure star `Gstar` / `GXstar`; Lemma 7 style: Laplacian eigenvalues `n` and `1` |
| `Hire/Lemma8.lean` | Gold-free ⇒ `G = Gstar` + eigenvalue `1`; card-3 converse; card-4 chord keeps `1` |
| `Hire/Cone.lean` | Layer C cone block: seed-then-leaves Laplacian equals `[k -1ᵀ; -1 I+L']` |
| `Hire/Dirichlet.lean` | Stub: `Nat.forall_exists_prime_gt_and_eq_mod` + `eventually_hired` placeholder |

## Build

Needs [elan](https://github.com/leanprover/elan):

```bash
cd lean
lake update
lake exe cache get   # Mathlib cache; skip if unavailable
lake build
```

First run downloads the Lean toolchain and Mathlib (large).

