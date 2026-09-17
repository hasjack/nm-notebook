/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Graph
import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness of hire windows

For each bound `X`, owners are primes `≤ X`, and hired vertices are bounded by
`max 2 (X + 1)`. Hence `HireVertex (owners X)` is finite — enough to form
Laplacian matrices on `GX X`.
-/

namespace Hire

theorem finite_hireVertex_owners (X : ℕ) : Finite (HireVertex (owners X)) := by
  change Finite (↑{q | Hired (owners X) q})
  exact (hired_set_finite X).to_subtype

noncomputable instance instFiniteHireVertexOwners (X : ℕ) :
    Finite (HireVertex (owners X)) :=
  finite_hireVertex_owners X

/-- Noncomputable `Fintype` for window vertices (classical; for `lapMatrix`). -/
noncomputable instance instFintypeHireVertexOwners (X : ℕ) :
    Fintype (HireVertex (owners X)) :=
  Fintype.ofFinite _

/-- Decidable equality on window vertices. -/
noncomputable instance instDecidableEqHireVertexOwners (X : ℕ) :
    DecidableEq (HireVertex (owners X)) :=
  Classical.decEq _

/-- Adj of `GX` is decidable (classical), so `lapMatrix` applies. -/
noncomputable instance instDecidableRelAdjGX (X : ℕ) :
    DecidableRel (GX X).Adj := by
  classical
  infer_instance

end Hire
