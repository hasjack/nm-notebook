/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Lemma8
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Layer C — cone block of the hire Laplacian

On a finite hire window the doors split as the seed `2`, then the leaves.
The combinatorial Laplacian of `GX` (star on the seed, undirected gold edges
only among the leaves), reindexed along that split, is the cone block

```
[ k    -1ᵀ ]
[ -1   I+L' ]
```

`k` is the number of leaves, `1` is the all-ones vector on the leaves, and `L'`
is the Laplacian of `GgoldLeaves`.

Why the entries are those:
* every leaf is a spoke of the seed, and gold never touches the seed
  (`ne_seed_of_GoldEdge`);
* the seed degree is therefore `k`, and every seed–leaf entry is `-1`;
* a leaf's degree is the spoke plus its gold degree;
* a leaf–leaf entry is `-1` on a gold edge and `0` otherwise;
* so the leaf block is `I + lapMatrix (GgoldLeaves)`.

The block equality is proved. From the same window:
* `0` is a Laplacian eigenvalue, the all-ones vector on the seed door and the
  leaves (`hasEigenvector_lapMatrix_GX_zero`);
* when the window has at least one leaf (`n ≥ 2`), `n` is a Laplacian
  eigenvalue. The test vector is Lemma 7's star-max vector, value `n - 1` on
  the seed and `-1` on every leaf. Gold edges contribute `0` because that
  vector is constant on the leaves (`card_mem_spectrum_lapMatrix_GX`);
* a vector that is `0` on the seed and an `L'`-eigenvector `v` on the leaves
  is an eigenvector for `1 + μ` only when `∑ v = 0` (`eigenvector_of_leaf_mode`).

`spectrum` as a set is the wrong reading of the cone. A repeated leaf
eigenvalue `μ = 0` (gold on the leaves disconnected) is still just `{0}` in
`spectrum ℝ L'`, so the union `{1 + μ | μ ≠ 0}` misses the eigenvalue `1`.
That is exactly `four_vertex_star_leaf_edge_keeps_one`. The Mathlib-honest
form is the ordered shift `spectrum_lapMatrix_GX`: ascending
`λ₁ ≤ ⋯ ≤ λₙ` and `μ₁ ≤ ⋯ ≤ μₖ`, with `λᵢ = 1 + μᵢ` for `i = 2, …, n - 1`.
The shift starts at `μ₂`, not `μ₁`. `μ₁ = 0` is the leaf all-ones vector;
mixed with the seed it is already the global kernel, and folding it into
`1 + μ` double-counts that kernel. The ordered endpoints are proved:
`lambda_GX_one` is `λ₁ = 0`, and `lambda_GX_card` is `λₙ = n` when `n ≥ 2`.
The bound used for `λₙ` is the complete-graph comparison
`eigenvalues_lapMatrix_le_card` (local copy; same argument is
mathlib4#43953).
The middle shift is `spectrum_lapMatrix_GX`. The antitone cone list is `n`,
then `1 + μₙ₋₁ ≥ ⋯ ≥ 1 + μ₂`, then `0`. Index `0` of that list is `λₙ`, the
last index is `λ₁`, and the matching ranks give `λᵢ = 1 + μᵢ` for
`i = 2, …, n - 1`. The leading `n` may tie with `1 + μₙ₋₁`.

`lambda2_eq_one_iff_GoldLeavesDisconnected` is the Layer D sentence
`λ₂ = 1` iff gold-on-leaves is disconnected. `spectrum_lapMatrix_GX` reads
`λ₂ = 1 + μ₂`, and `μ₂ = 0` is the Laplacian fact that `0` has multiplicity
at least two on a graph with at least two vertices: Mathlib's
`card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` says that
multiplicity is the number of components, so the leaf gold graph is not
connected.
-/

namespace Hire

open Finset Matrix

/-- Classical decidability so the leaf gold Laplacian is a matrix. -/
noncomputable instance instDecidableRelAdjGgoldLeaves (X : ℕ) :
    DecidableRel (GgoldLeaves (owners X)).Adj := by
  classical
  infer_instance

/-- Leaves of a hire window are finite. -/
noncomputable instance instFintypeHireLeaf (X : ℕ) : Fintype (HireLeaf (owners X)) :=
  Fintype.ofFinite _

/-- Reindex a hire window as the seed door, then the leaves. `inl ()` is the seed `2`. -/
def seedLeavesEquiv (O : Set ℕ) : HireVertex O ≃ Unit ⊕ HireLeaf O where
  toFun v := if h : v = seedVertex O then Sum.inl () else Sum.inr ⟨v, h⟩
  invFun := Sum.elim (fun _ => seedVertex O) Subtype.val
  left_inv v := by
    by_cases h : v = seedVertex O
    · simp [h]
    · simp [h]
  right_inv s := by
    cases s with
    | inl u =>
      cases u
      simp
    | inr u =>
      simp [u.property]

@[simp] theorem seedLeavesEquiv_symm_inl (O : Set ℕ) :
    (seedLeavesEquiv O).symm (Sum.inl ()) = seedVertex O :=
  rfl

@[simp] theorem seedLeavesEquiv_symm_inr (O : Set ℕ) (u : HireLeaf O) :
    (seedLeavesEquiv O).symm (Sum.inr u) = u.1 :=
  rfl

/-- Gold stays off the seed door. -/
theorem not_GoldEdge_seed {O : Set ℕ} (v : HireVertex O) :
    ¬ GoldEdge O (seedVertex O) v ∧ ¬ GoldEdge O v (seedVertex O) := by
  constructor
  · intro h
    exact (ne_seed_of_GoldEdge h).1 rfl
  · intro h
    exact (ne_seed_of_GoldEdge h).2.1 rfl

/-- A star spoke always meets the seed, so two leaves are never a star edge. -/
theorem not_StarEdge_of_leaves {O : Set ℕ} (u v : HireLeaf O) :
    ¬ StarEdge O u.1 v.1 := by
  intro h
  rcases (StarEdge_iff_starGraph u.1 v.1).mp h with hu | hv
  · exact u.property hu
  · exact v.property hv

/-- On leaves, hire adjacency is exactly a gold edge. -/
theorem GX_adj_leaf_leaf {X : ℕ} (u v : HireLeaf (owners X)) :
    (GX X).Adj u.1 v.1 ↔ (GgoldLeaves (owners X)).Adj u v := by
  rw [GgoldLeaves, SimpleGraph.fromRel_adj, GX_adj_iff]
  constructor
  · rintro ⟨hne, hrel⟩
    refine ⟨fun hEq => hne (congrArg Subtype.val hEq), ?_⟩
    rcases hrel with h | h
    · rcases h with hs | hg
      · exact (not_StarEdge_of_leaves u v hs).elim
      · exact Or.inl hg
    · rcases h with hs | hg
      · exact (not_StarEdge_of_leaves v u hs).elim
      · exact Or.inr hg
  · rintro ⟨hne, hg | hg⟩
    · exact ⟨fun hEq => hne (Subtype.ext hEq), Or.inl (Or.inr hg)⟩
    · exact ⟨fun hEq => hne (Subtype.ext hEq), Or.inr (Or.inr hg)⟩

/-- The seed door's hire relation is the star spoke. Gold never meets the seed. -/
theorem hireRel_seed_iff_star {O : Set ℕ} (v : HireVertex O) :
    hireRel O (seedVertex O) v ↔ StarEdge O (seedVertex O) v := by
  constructor
  · rintro (hs | hg)
    · exact hs
    · exact ((not_GoldEdge_seed v).1 hg).elim
  · exact Or.inl

/-- Every leaf is joined to the seed by a star spoke. -/
theorem GX_adj_seed_of_leaf {X : ℕ} (u : HireLeaf (owners X)) :
    (GX X).Adj (seedVertex (owners X)) u.1 := by
  have hne : seedVertex (owners X) ≠ u.1 := fun h => u.property h.symm
  have hstar : StarEdge (owners X) (seedVertex (owners X)) u.1 := Or.inl rfl
  rw [GX_adj_iff]
  exact ⟨hne, Or.inl ((hireRel_seed_iff_star u.1).mpr hstar)⟩

private theorem lapMatrix_apply {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
    G.lapMatrix ℝ i j =
      (if i = j then (G.degree i : ℝ) else 0) -
        (if G.Adj i j then (1 : ℝ) else 0) := by
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
    Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]

private theorem nsmul_one_real (n : ℕ) : n • (1 : ℝ) = (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih, Nat.cast_succ]

private theorem sum_one_eq_card {α : Type*} [Fintype α] :
    (∑ _ : α, (1 : ℝ)) = (Fintype.card α : ℝ) := by
  rw [sum_const, card_univ, nsmul_one_real]

/-- Seed degree equals the number of leaves: the star meets every leaf, and gold
does not add a further door (`not_GoldEdge_seed`). -/
theorem degree_GX_seed (X : ℕ) :
    (GX X).degree (seedVertex (owners X)) = Fintype.card (HireLeaf (owners X)) := by
  classical
  set seed := seedVertex (owners X)
  set e := seedLeavesEquiv (owners X)
  have hcast : ((GX X).degree seed : ℝ) =
      ∑ s : Unit ⊕ HireLeaf (owners X),
        if (GX X).Adj seed (e.symm s) then (1 : ℝ) else 0 :=
    ((GX X).degree_eq_sum_if_adj seed).trans
      (e.symm.sum_comp (fun v => if (GX X).Adj seed v then (1 : ℝ) else 0)).symm
  rw [Fintype.sum_sum_type] at hcast
  have hunit :
      (∑ a : Unit, if (GX X).Adj seed (e.symm (Sum.inl a)) then (1 : ℝ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    cases a
    rw [seedLeavesEquiv_symm_inl, ite_eq_right (show ¬ (GX X).Adj seed seed from SimpleGraph.irrefl (GX X))]
  have hleaf :
      (∑ u : HireLeaf (owners X),
          if (GX X).Adj seed (e.symm (Sum.inr u)) then (1 : ℝ) else 0) =
        (Fintype.card (HireLeaf (owners X)) : ℝ) := by
    have hterm : ∀ u : HireLeaf (owners X),
        (if (GX X).Adj seed (e.symm (Sum.inr u)) then (1 : ℝ) else 0) = 1 := by
      intro u
      rw [seedLeavesEquiv_symm_inr, ite_eq_left (GX_adj_seed_of_leaf u)]
    simp_rw [hterm]
    exact sum_one_eq_card
  rw [hunit, hleaf, zero_add] at hcast
  exact_mod_cast hcast

/-- A leaf's hire degree is one spoke plus its gold degree on the leaves. -/
theorem degree_GX_leaf (X : ℕ) (u : HireLeaf (owners X)) :
    (GX X).degree u.1 = (GgoldLeaves (owners X)).degree u + 1 := by
  classical
  set seed := seedVertex (owners X)
  set e := seedLeavesEquiv (owners X)
  have hcast : ((GX X).degree u.1 : ℝ) =
      ∑ s : Unit ⊕ HireLeaf (owners X),
        if (GX X).Adj u.1 (e.symm s) then (1 : ℝ) else 0 :=
    ((GX X).degree_eq_sum_if_adj u.1).trans
      (e.symm.sum_comp (fun v => if (GX X).Adj u.1 v then (1 : ℝ) else 0)).symm
  rw [Fintype.sum_sum_type] at hcast
  have hunit :
      (∑ a : Unit, if (GX X).Adj u.1 (e.symm (Sum.inl a)) then (1 : ℝ) else 0) = 1 := by
    have hterm : ∀ a : Unit,
        (if (GX X).Adj u.1 (e.symm (Sum.inl a)) then (1 : ℝ) else 0) = 1 := by
      intro a
      cases a
      rw [seedLeavesEquiv_symm_inl, ite_eq_left (GX_adj_seed_of_leaf u).symm]
    simp_rw [hterm]
    rw [sum_one_eq_card, Fintype.card_unit, Nat.cast_one]
  have hleaf :
      (∑ v : HireLeaf (owners X),
          if (GX X).Adj u.1 (e.symm (Sum.inr v)) then (1 : ℝ) else 0) =
        ((GgoldLeaves (owners X)).degree u : ℝ) := by
    rw [(GgoldLeaves (owners X)).degree_eq_sum_if_adj u]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [seedLeavesEquiv_symm_inr]
    by_cases h : (GgoldLeaves (owners X)).Adj u v
    · rw [ite_eq_left ((GX_adj_leaf_leaf u v).mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun hgx => h ((GX_adj_leaf_leaf u v).mp hgx)), ite_eq_right h]
  have hsum : (1 : ℝ) + ((GgoldLeaves (owners X)).degree u : ℝ) =
      (((GgoldLeaves (owners X)).degree u + 1 : ℕ) : ℝ) := by
    rw [add_comm, ← Nat.cast_one, ← Nat.cast_add]
  rw [hunit, hleaf, hsum] at hcast
  exact_mod_cast hcast

/-- **Entry:** seed diagonal is `k`, the number of leaves. -/
theorem lapMatrix_GX_seed_diag (X : ℕ) :
    (GX X).lapMatrix ℝ (seedVertex (owners X)) (seedVertex (owners X)) =
      (Fintype.card (HireLeaf (owners X)) : ℝ) := by
  rw [lapMatrix_apply, ite_eq_left rfl,
    ite_eq_right (show ¬ (GX X).Adj _ _ from SimpleGraph.irrefl (GX X)), sub_zero, degree_GX_seed]

/-- **Entry:** every seed–leaf entry is `-1` (the spoke). -/
theorem lapMatrix_GX_seed_leaf (X : ℕ) (u : HireLeaf (owners X)) :
    (GX X).lapMatrix ℝ (seedVertex (owners X)) u.1 = -1 := by
  rw [lapMatrix_apply]
  have hne : seedVertex (owners X) ≠ u.1 := fun h => u.property h.symm
  rw [ite_eq_right hne, ite_eq_left (GX_adj_seed_of_leaf u), zero_sub]

/-- **Entry:** every leaf–seed entry is `-1`. -/
theorem lapMatrix_GX_leaf_seed (X : ℕ) (u : HireLeaf (owners X)) :
    (GX X).lapMatrix ℝ u.1 (seedVertex (owners X)) = -1 := by
  rw [lapMatrix_apply]
  rw [ite_eq_right u.property, ite_eq_left (GX_adj_seed_of_leaf u).symm, zero_sub]

/-- **Entry:** leaf diagonal is the spoke plus the gold degree. -/
theorem lapMatrix_GX_leaf_diag (X : ℕ) (u : HireLeaf (owners X)) :
    (GX X).lapMatrix ℝ u.1 u.1 =
      1 + ((GgoldLeaves (owners X)).degree u : ℝ) := by
  rw [lapMatrix_apply, ite_eq_left rfl,
    ite_eq_right (show ¬ (GX X).Adj _ _ from SimpleGraph.irrefl (GX X)), sub_zero, degree_GX_leaf,
    Nat.cast_add, Nat.cast_one, add_comm]

/-- **Entry:** a leaf–leaf off-diagonal is `-1` on a gold edge and `0` otherwise. -/
theorem lapMatrix_GX_leaf_off (X : ℕ) {u v : HireLeaf (owners X)} (huv : u ≠ v) :
    (GX X).lapMatrix ℝ u.1 v.1 =
      if (GgoldLeaves (owners X)).Adj u v then -1 else 0 := by
  rw [lapMatrix_apply]
  have hne : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  rw [ite_eq_right hne]
  by_cases h : (GgoldLeaves (owners X)).Adj u v
  · rw [ite_eq_left ((GX_adj_leaf_leaf u v).mpr h), ite_eq_left h, zero_sub]
  · rw [ite_eq_right (fun hgx => h ((GX_adj_leaf_leaf u v).mp hgx)), ite_eq_right h, sub_zero]

/-- Leaf block of `GX`, entrywise: `I +` the leaf gold Laplacian. -/
theorem lapMatrix_GX_leaf_block (X : ℕ) (u v : HireLeaf (owners X)) :
    (GX X).lapMatrix ℝ u.1 v.1 =
      (1 + (GgoldLeaves (owners X)).lapMatrix ℝ) u v := by
  rw [Matrix.add_apply]
  by_cases huv : u = v
  · subst huv
    rw [one_apply_eq, lapMatrix_GX_leaf_diag, lapMatrix_apply, ite_eq_left rfl,
      ite_eq_right (show ¬ _ from SimpleGraph.irrefl (GgoldLeaves (owners X))), sub_zero, add_comm]
  · rw [one_apply_ne huv, zero_add, lapMatrix_GX_leaf_off (huv := huv), lapMatrix_apply, ite_eq_right huv]
    by_cases h : (GgoldLeaves (owners X)).Adj u v
    · rw [ite_eq_left h, zero_sub, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, sub_self]

/-- **Layer C.** After reindexing the hire window seed-then-leaves, the
Laplacian of `GX` is the cone block

```
[ k    -1ᵀ ]
[ -1   I+L' ]
```

with `k` the number of leaves and `L'` the Laplacian of gold on the leaves.
Spectrum identification is not part of this theorem. -/
theorem lapMatrix_GX_reindex_eq_fromBlocks (X : ℕ) :
    ((GX X).lapMatrix ℝ).reindex
        (seedLeavesEquiv (owners X)) (seedLeavesEquiv (owners X)) =
      Matrix.fromBlocks
        (Matrix.of fun (_ _ : Unit) => (Fintype.card (HireLeaf (owners X)) : ℝ))
        (Matrix.of fun (_ : Unit) (_ : HireLeaf (owners X)) => (-1 : ℝ))
        (Matrix.of fun (_ : HireLeaf (owners X)) (_ : Unit) => (-1 : ℝ))
        (1 + (GgoldLeaves (owners X)).lapMatrix ℝ) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  cases i with
  | inl u =>
    cases u
    cases j with
    | inl v =>
      cases v
      simp [fromBlocks_apply₁₁, of_apply, lapMatrix_GX_seed_diag]
    | inr leaf =>
      simp [fromBlocks_apply₁₂, of_apply, lapMatrix_GX_seed_leaf]
  | inr leaf =>
    cases j with
    | inl v =>
      cases v
      simp [fromBlocks_apply₂₁, of_apply, lapMatrix_GX_leaf_seed]
    | inr leaf' =>
      simp [fromBlocks_apply₂₂, lapMatrix_GX_leaf_block]


/-- Doors in a window: the seed, then the leaves. -/
theorem card_HireVertex_eq_succ_card_HireLeaf (X : ℕ) :
    Fintype.card (HireVertex (owners X)) =
      Fintype.card (HireLeaf (owners X)) + 1 := by
  rw [Fintype.card_congr (seedLeavesEquiv (owners X)), Fintype.card_sum,
    Fintype.card_unit, add_comm]

/-- Neighbors of the seed door are exactly the leaves: every non-seed door is a
spoke (`star_adj_GX`), and the seed is loopless. -/
theorem neighborFinset_GX_seed (X : ℕ) :
    (GX X).neighborFinset (seedVertex (owners X)) =
      Finset.univ.erase (seedVertex (owners X)) := by
  classical
  ext u
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · intro h
    exact h.ne.symm
  · intro hne
    exact star_adj_GX u ((seedVertex_eq_iff u).not.mp hne)

/-- **Eigenvalue `0`.** The all-ones vector on the seed door and every leaf is a
kernel vector of the hire Laplacian. The seed door is always a vertex. -/
theorem hasEigenvector_lapMatrix_GX_zero (X : ℕ) :
    Module.End.HasEigenvector ((GX X).lapMatrix ℝ).toLin' (0 : ℝ)
      (1 : HireVertex (owners X) → ℝ) := by
  refine ⟨Module.End.mem_genEigenspace_one.mpr ?_, ?_⟩
  · simpa [Matrix.toLin'_apply, zero_smul] using (GX X).lapMatrix_mulVec_one_eq_zero ℝ
  · intro h
    have h1 := congrFun h (seedVertex (owners X))
    simp only [Pi.one_apply, Pi.zero_apply] at h1
    exact one_ne_zero h1

/-- **Eigenvalue `0`.** `0` lies in the spectrum of `(GX X).lapMatrix ℝ`. -/
theorem zero_mem_spectrum_lapMatrix_GX (X : ℕ) :
    (0 : ℝ) ∈ spectrum ℝ ((GX X).lapMatrix ℝ) := by
  rw [← Matrix.spectrum_toLin']
  exact Module.End.HasEigenvalue.mem_spectrum
    (Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_lapMatrix_GX_zero X))

/-- The star-max test vector is constant off the seed door, so its difference on
any two leaves is `0`. A gold edge, which never meets the seed, contributes `0`. -/
lemma starMaxEigenvec_sub_eq_zero_of_ne_seed (X : ℕ)
    {u v : HireVertex (owners X)}
    (hu : u ≠ seedVertex (owners X)) (hv : v ≠ seedVertex (owners X)) :
    starMaxEigenvec (seedVertex (owners X))
        (Fintype.card (HireVertex (owners X))) u -
      starMaxEigenvec (seedVertex (owners X))
        (Fintype.card (HireVertex (owners X))) v = 0 := by
  simp [starMaxEigenvec, hu, hv]

/-- **Eigenvalue `n`.** Lemma 7's star-max vector survives gold. It takes the
value `n - 1` on the seed door and `-1` on every leaf, so each gold edge has
difference `0` and does not move the eigenvalue. -/
theorem lapMatrix_GX_mulVec_starMaxEigenvec (X : ℕ) :
    (GX X).lapMatrix ℝ *ᵥ
        starMaxEigenvec (seedVertex (owners X))
          (Fintype.card (HireVertex (owners X))) =
      (Fintype.card (HireVertex (owners X)) : ℝ) •
        starMaxEigenvec (seedVertex (owners X))
          (Fintype.card (HireVertex (owners X))) := by
  classical
  set seed := seedVertex (owners X)
  set n := Fintype.card (HireVertex (owners X))
  set vec := starMaxEigenvec seed n
  have hn1 : 1 ≤ n := Fintype.card_pos
  ext v
  rw [SimpleGraph.lapMatrix_mulVec_apply']
  by_cases hv : v = seed
  · subst hv
    rw [neighborFinset_GX_seed]
    have hdiff : ∀ u ∈ univ.erase seed, vec seed - vec u = (n : ℝ) := by
      intro u hu
      have hu' : u ≠ seed := (mem_erase.mp hu).1
      simp only [vec, starMaxEigenvec, ↓reduceIte, hu']
      ring
    rw [sum_congr rfl hdiff, sum_const, card_erase_of_mem (mem_univ seed), card_univ]
    simp only [vec, starMaxEigenvec, ↓reduceIte, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [Nat.cast_sub hn1]
    ring
  · have hseed : seed ∈ (GX X).neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]
      exact (star_adj_GX v ((seedVertex_eq_iff v).not.mp hv)).symm
    have hdiff : ∀ u ∈ (GX X).neighborFinset v,
        vec v - vec u = if u = seed then -(n : ℝ) else 0 := by
      intro u _
      by_cases hu : u = seed
      · subst hu
        simp only [vec, starMaxEigenvec, hv, ↓reduceIte]
        ring
      · -- Both doors are leaves: the test vector is constant, so a gold edge
        -- contributes difference zero.
        rw [starMaxEigenvec_sub_eq_zero_of_ne_seed (X := X) (u := v) (v := u) hv hu,
          ite_eq_right hu]
    rw [sum_congr rfl hdiff, sum_ite_eq', ite_eq_left hseed]
    simp only [vec, starMaxEigenvec, hv, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Eigenvalue `n`.** When the window has at least one leaf (`n ≥ 2`), `n` lies
in the spectrum of `(GX X).lapMatrix ℝ`. -/
theorem card_mem_spectrum_lapMatrix_GX (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    (Fintype.card (HireVertex (owners X)) : ℝ) ∈
      spectrum ℝ ((GX X).lapMatrix ℝ) := by
  classical
  set n := Fintype.card (HireVertex (owners X))
  set vec := starMaxEigenvec (seedVertex (owners X)) n
  have hx : vec ≠ 0 := starMaxEigenvec_ne_zero (seedVertex (owners X)) hn
  have hmul := lapMatrix_GX_mulVec_starMaxEigenvec X
  rw [← Matrix.spectrum_toLin']
  refine Module.End.HasEigenvalue.mem_spectrum ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := vec) ⟨?_, hx⟩
  exact Module.End.mem_genEigenspace_one.mpr
    (by simpa [Matrix.toLin'_apply, vec, n] using hmul)

/-- Lift a leaf vector to the hire window: `0` on the seed door, `v` on the leaves. -/
def leafMode {O : Set ℕ} (v : HireLeaf O → ℝ) : HireVertex O → ℝ :=
  Sum.elim (fun _ => (0 : ℝ)) v ∘ seedLeavesEquiv O

theorem leafMode_seed {O : Set ℕ} (v : HireLeaf O → ℝ) :
    leafMode v (seedVertex O) = 0 := by
  unfold leafMode
  rw [Function.comp_apply]
  have he : seedLeavesEquiv O (seedVertex O) = Sum.inl () := by
    change (if h : seedVertex O = seedVertex O then Sum.inl () else Sum.inr ⟨seedVertex O, h⟩) =
      Sum.inl ()
    exact dite_eq_left rfl
  simp [he, Sum.elim_inl]

theorem leafMode_leaf {O : Set ℕ} (v : HireLeaf O → ℝ) (u : HireLeaf O) :
    leafMode v u.1 = v u := by
  have hu : u.1 ≠ seedVertex O := u.property
  unfold leafMode
  rw [Function.comp_apply]
  have he : seedLeavesEquiv O u.1 = Sum.inr u := by
    change (if h : u.1 = seedVertex O then Sum.inl () else Sum.inr ⟨u.1, h⟩) = Sum.inr u
    rw [dite_eq_right hu]
  simp [he, Sum.elim_inr]

/-- **Leaf mode.** A vector that is `0` on the seed and an `L'`-eigenvector `v`
on the leaves is an eigenvector of the cone block for `1 + μ` precisely when
`∑ v = 0` (orthogonal to the leaf all-ones vector). The leaf all-ones mode
`μ₁ = 0` fails that test: it is already the global kernel vector, mixed with
the seed, so it must not be folded into `1 + μ`. -/
theorem lapMatrix_GX_mulVec_leafMode (X : ℕ) (v : HireLeaf (owners X) → ℝ) (μ : ℝ)
    (hv : (GgoldLeaves (owners X)).lapMatrix ℝ *ᵥ v = μ • v)
    (hsum : ∑ i, v i = 0) :
    (GX X).lapMatrix ℝ *ᵥ leafMode v = ((1 : ℝ) + μ) • leafMode v := by
  classical
  set e := seedLeavesEquiv (owners X)
  set w : Unit ⊕ HireLeaf (owners X) → ℝ := Sum.elim (fun _ => 0) v
  have hre :
      ((GX X).lapMatrix ℝ).reindex e e *ᵥ w =
        ((GX X).lapMatrix ℝ *ᵥ leafMode v) ∘ e.symm := by
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm]
    rfl
  have hblock :
      ((GX X).lapMatrix ℝ).reindex e e *ᵥ w = ((1 : ℝ) + μ) • w := by
    rw [lapMatrix_GX_reindex_eq_fromBlocks, Matrix.fromBlocks_mulVec]
    have hinl : w ∘ Sum.inl = 0 := by
      ext u
      cases u
      rfl
    have hinr : w ∘ Sum.inr = v := by
      ext u
      rfl
    rw [hinl, hinr, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add, zero_add]
    ext s
    cases s with
    | inl u =>
      cases u
      simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul]
      have hw0 : w (Sum.inl ()) = 0 := rfl
      rw [hw0, mul_zero]
      rw [Matrix.mulVec_apply_eq_sum]
      simp only [Matrix.of_apply, neg_one_mul, sum_neg_distrib, hsum, neg_zero]
    | inr leaf =>
      simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
      have hwv : w (Sum.inr leaf) = v leaf := rfl
      rw [hwv]
      have hD :
          ((1 : Matrix (HireLeaf (owners X)) (HireLeaf (owners X)) ℝ) +
              (GgoldLeaves (owners X)).lapMatrix ℝ) *ᵥ v =
            ((1 : ℝ) + μ) • v := by
        rw [Matrix.add_mulVec, Matrix.one_mulVec, hv]
        calc
          v + μ • v = (1 : ℝ) • v + μ • v := by rw [one_smul]
          _ = ((1 : ℝ) + μ) • v := (add_smul (1 : ℝ) μ v).symm
      rw [hD]
      simp [Pi.smul_apply, smul_eq_mul]
  have hfun :
      ((GX X).lapMatrix ℝ *ᵥ leafMode v) ∘ e.symm = ((1 : ℝ) + μ) • w := by
    rw [← hre, hblock]
  ext x
  have hxs := congrFun hfun (e x)
  simpa [Function.comp_apply, Equiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul,
    leafMode, w] using hxs

theorem eigenvector_of_leaf_mode (X : ℕ) (v : HireLeaf (owners X) → ℝ) (μ : ℝ)
    (hv : (GgoldLeaves (owners X)).lapMatrix ℝ *ᵥ v = μ • v)
    (hsum : ∑ i, v i = 0) (hne : v ≠ 0) :
    Module.End.HasEigenvector ((GX X).lapMatrix ℝ).toLin'
      ((1 : ℝ) + μ) (leafMode v) := by
  have hmul := lapMatrix_GX_mulVec_leafMode X v μ hv hsum
  have hnz : leafMode v ≠ 0 := by
    intro h
    apply hne
    ext u
    have := congrFun h u.1
    rw [leafMode_leaf] at this
    simpa [Pi.zero_apply] using this
  refine ⟨Module.End.mem_genEigenspace_one.mpr ?_, hnz⟩
  simpa [Matrix.toLin'_apply] using hmul

/-! ### Ordered spectrum, `μ₂` cutoff

`IsHermitian.eigenvalues₀` lists Laplacian eigenvalues in **antitone** order
(index `0` is the largest). The ascending eigenvalue of rank `i` (1-indexed,
so `i = 1` is the smallest) is therefore index `card - i`.
-/

/-- Ascending eigenvalue `λᵢ` of the hire Laplacian, `1 ≤ i ≤ n`.
`λ₁` is the smallest, `λ₂` the second smallest. -/
noncomputable def lambda_GX (X : ℕ) (i : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ Fintype.card (HireVertex (owners X))) : ℝ :=
  let n := Fintype.card (HireVertex (owners X))
  ((GX X).posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀
    ⟨n - i, by omega⟩

/-- Ascending eigenvalue `μᵢ` of gold on the leaves, `1 ≤ i ≤ k`. -/
noncomputable def mu_goldLeaves (X : ℕ) (i : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ Fintype.card (HireLeaf (owners X))) : ℝ :=
  let k := Fintype.card (HireLeaf (owners X))
  ((GgoldLeaves (owners X)).posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀
    ⟨k - i, by omega⟩

/-- Quadratic form of a simple-graph Laplacian, bounded by the number of vertices.

Mathlib had no `eigenvalues_le_card` (same argument proposed as mathlib4#43953).
The comparison proved here is the complete graph:
adjacency of `G` is a subset of pairs `i ≠ j`, so
`xᵀ L(G) x ≤ xᵀ L(K) x`, and `lapMatrix_top` writes `L(K)` as `n` minus the
all-ones matrix. That quadratic form is `n ‖x‖² - (∑ x)²`, hence at most
`n ‖x‖²`. -/
theorem dotProduct_mulVec_lapMatrix_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) ≤ (Fintype.card V : ℝ) * (x ⬝ᵥ x) := by
  classical
  have hcmp : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x ≤
      Matrix.toLinearMap₂' ℝ ((⊤ : SimpleGraph V).lapMatrix ℝ) x x := by
    rw [G.lapMatrix_toLinearMap₂' ℝ x, (⊤ : SimpleGraph V).lapMatrix_toLinearMap₂' ℝ x]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hadj : G.Adj i j
    · have hne : i ≠ j := hadj.ne
      rw [ite_eq_left hadj]
      simp only [SimpleGraph.top_adj]
      rw [ite_eq_left hne]
    · rw [ite_eq_right hadj]
      simp only [SimpleGraph.top_adj]
      split_ifs with hne
      · exact sq_nonneg _
      · exact le_rfl
  have htop : Matrix.toLinearMap₂' ℝ ((⊤ : SimpleGraph V).lapMatrix ℝ) x x ≤
      (Fintype.card V : ℝ) * (x ⬝ᵥ x) := by
    rw [SimpleGraph.lapMatrix_top (R := ℝ), Matrix.toLinearMap₂'_apply']
    rw [sub_mulVec, dotProduct_sub, natCast_mulVec, dotProduct_smul, smul_eq_mul]
    have hJ : x ⬝ᵥ (Matrix.of (1 : V → V → ℝ) *ᵥ x) = (∑ i, x i) ^ 2 := by
      have hmul : Matrix.of (1 : V → V → ℝ) *ᵥ x = fun _ => ∑ j, x j := by
        ext i
        rw [mulVec_apply_eq_sum]
        simp [of_apply]
      rw [hmul, dotProduct, ← Finset.sum_mul]
      ring
    rw [hJ]
    exact sub_le_self _ (sq_nonneg _)
  calc
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x)
        = Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x :=
          (Matrix.toLinearMap₂'_apply' _ x x).symm
    _ ≤ Matrix.toLinearMap₂' ℝ ((⊤ : SimpleGraph V).lapMatrix ℝ) x x := hcmp
    _ ≤ (Fintype.card V : ℝ) * (x ⬝ᵥ x) := htop

/-- Every eigenvalue of a finite simple-graph Laplacian is at most the number
of vertices. Mathlib does not state this; it is the Rayleigh form of
`dotProduct_mulVec_lapMatrix_le_card` on a unit eigenvector from
`IsHermitian.eigenvectorBasis`. -/
theorem eigenvalues_lapMatrix_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    ((G.posSemidef_lapMatrix ℝ).isHermitian.eigenvalues i) ≤ (Fintype.card V : ℝ) := by
  classical
  let hA := (G.posSemidef_lapMatrix ℝ).isHermitian
  let v := hA.eigenvectorBasis i
  have hunit : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.norm_eq_one i
  have hdot : ⇑v ⬝ᵥ ⇑v = 1 := by
    rw [dotProduct]
    have hsq := EuclideanSpace.real_norm_sq_eq v
    rw [hunit, one_pow] at hsq
    have hsq' : ∑ j, (v.ofLp j) * (v.ofLp j) = ∑ j, (v.ofLp j) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsq', ← hsq]
  have hquad := dotProduct_mulVec_lapMatrix_le_card G (⇑v)
  rw [hA.eigenvalues_eq i]
  simp only [RCLike.re_to_real, star_trivial]
  calc
    ⇑v ⬝ᵥ (G.lapMatrix ℝ *ᵥ ⇑v) ≤ (Fintype.card V : ℝ) * (⇑v ⬝ᵥ ⇑v) := hquad
    _ = (Fintype.card V : ℝ) := by rw [hdot, mul_one]

/-- `eigenvalues₀` of the hire Laplacian, read as `eigenvalues` along the
Mathlib reindexing `Fin n ≃` the doors. -/
private theorem eigenvalues₀_GX_eq_eigenvalues (X : ℕ)
    (j : Fin (Fintype.card (HireVertex (owners X)))) :
    ((GX X).posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀ j =
      ((GX X).posSemidef_lapMatrix ℝ).isHermitian.eigenvalues
        (Fintype.equivOfCardEq
          (Fintype.card_fin (Fintype.card (HireVertex (owners X)))) j) := by
  simp [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]

/-- **Ordered endpoint `λ₁ = 0`.**

The hire Laplacian is positive semidefinite, so every eigenvalue is
nonnegative (`IsHermitian.posSemidef_iff_eigenvalues_nonneg` on
`posSemidef_lapMatrix`). `0` is achieved (`zero_mem_spectrum_lapMatrix_GX`).
`eigenvalues₀` is antitone, so its last index is the smallest eigenvalue, and
that value is `0`. Hypothesis `n ≥ 1` is the nonempty window (the seed door). -/
theorem lambda_GX_one (X : ℕ)
    (hn : 1 ≤ Fintype.card (HireVertex (owners X))) :
    lambda_GX X 1 (by omega) hn = 0 := by
  classical
  let n := Fintype.card (HireVertex (owners X))
  have hn0 : 0 < n := by omega
  let hA := ((GX X).posSemidef_lapMatrix ℝ).isHermitian
  unfold lambda_GX
  dsimp only
  have hrew (h : n - 1 < n) :
      hA.eigenvalues₀ ⟨n - 1, h⟩ =
        hA.eigenvalues₀ ⟨n - 1, Nat.sub_lt hn0 zero_lt_one⟩ := by
    rw [show (⟨n - 1, h⟩ : Fin n) = ⟨n - 1, Nat.sub_lt hn0 zero_lt_one⟩ from Fin.ext rfl]
  rw [hrew]
  have hnn (j : Fin n) : 0 ≤ hA.eigenvalues₀ j := by
    rw [eigenvalues₀_GX_eq_eigenvalues]
    have hpsd := (GX X).posSemidef_lapMatrix ℝ
    have hle : 0 ≤ hA.eigenvalues := (hA.posSemidef_iff_eigenvalues_nonneg).mp hpsd
    exact (Pi.le_def.mp hle) _
  have hmem : (0 : ℝ) ∈ spectrum ℝ ((GX X).lapMatrix ℝ) := zero_mem_spectrum_lapMatrix_GX X
  rw [hA.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i, hi⟩ := hmem
  have hsome : hA.eigenvalues₀
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (HireVertex (owners X))))).symm i) = 0 := by
    rw [eigenvalues₀_GX_eq_eigenvalues]
    simpa [Equiv.apply_symm_apply] using hi
  have hlast_le : hA.eigenvalues₀ ⟨n - 1, Nat.sub_lt hn0 zero_lt_one⟩ ≤
      hA.eigenvalues₀
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (HireVertex (owners X))))).symm i) := by
    apply hA.eigenvalues₀_antitone
    rw [Fin.le_def]
    exact Nat.le_sub_one_of_lt
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (HireVertex (owners X))))).symm i).isLt
  have hlast_ge := hnn ⟨n - 1, Nat.sub_lt hn0 zero_lt_one⟩
  linarith

/-- **Ordered endpoint `λₙ = n`.**

When the window has at least one leaf (`n ≥ 2`), `n` is achieved
(`card_mem_spectrum_lapMatrix_GX`, the star-max vector). It is maximal because
every simple-graph Laplacian eigenvalue is at most `n`
(`eigenvalues_lapMatrix_le_card`). Mathlib does not contain that bound; it is
proved from `lapMatrix_top`, not from a degree bound. `eigenvalues₀` is
antitone, so index `0` is the largest eigenvalue, and `lambda_GX` reads that
index as `λₙ`.

The hypothesis `n ≥ 2` is necessary: a single door has Laplacian eigenvalue
`0`, not `1`. -/
theorem lambda_GX_card (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    lambda_GX X (Fintype.card (HireVertex (owners X))) (by omega) le_rfl =
      (Fintype.card (HireVertex (owners X)) : ℝ) := by
  classical
  let n := Fintype.card (HireVertex (owners X))
  have hn0 : 0 < n := by omega
  let hA := ((GX X).posSemidef_lapMatrix ℝ).isHermitian
  unfold lambda_GX
  dsimp only
  have hrew (h : n - n < n) :
      hA.eigenvalues₀ ⟨n - n, h⟩ = hA.eigenvalues₀ ⟨0, hn0⟩ := by
    have hfin : (⟨n - n, h⟩ : Fin n) = ⟨0, hn0⟩ := by
      apply Fin.ext
      simp
    rw [hfin]
  rw [hrew]
  have hle : hA.eigenvalues₀ ⟨0, hn0⟩ ≤ (n : ℝ) := by
    rw [eigenvalues₀_GX_eq_eigenvalues]
    exact eigenvalues_lapMatrix_le_card (GX X) _
  have hmem := card_mem_spectrum_lapMatrix_GX X hn
  rw [hA.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i, hi⟩ := hmem
  have hsome : hA.eigenvalues₀
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (HireVertex (owners X))))).symm i) =
        (n : ℝ) := by
    rw [eigenvalues₀_GX_eq_eigenvalues]
    simpa [Equiv.apply_symm_apply] using hi
  have hge : (n : ℝ) ≤ hA.eigenvalues₀ ⟨0, hn0⟩ := by
    rw [← hsome]
    apply hA.eigenvalues₀_antitone
    rw [Fin.le_def]
    exact Nat.zero_le _
  linarith


/-! ### Middle spectrum

`eigenvalues₀` is antitone, so the ascending rank `λᵢ` is index `n - i`.
The cone list in that same antitone order is `coneRank`: `n`, then
`1 + μ_{n-1}, …, 1 + μ₂`, then `0`. `0` is strictly last in that list
(every earlier entry is at least `1`). The leading `n` may tie with
`1 + μ_{n-1}`.
-/

/-- Seed `0`, then the leaves, as `Fin (k + 1) ≃ Unit ⊕ Fin k`. -/
private def finSeed (k : ℕ) : Fin (k + 1) ≃ Unit ⊕ Fin k where
  toFun i := if h : i = 0 then Sum.inl () else Sum.inr (i.pred h)
  invFun
    | Sum.inl () => 0
    | Sum.inr j => j.succ
  left_inv i := by
    by_cases h : i = 0
    · subst h
      rfl
    · simp only [h, dite_false]
      exact Fin.succ_pred i h
  right_inv
    | Sum.inl () => rfl
    | Sum.inr j => by
        show (if h : j.succ = 0 then Sum.inl () else Sum.inr (j.succ.pred h)) = Sum.inr j
        rw [dite_eq_right (Fin.succ_ne_zero j), Fin.pred_succ]

@[simp] private theorem finSeed_zero (k : ℕ) : finSeed k 0 = Sum.inl () := rfl

@[simp] private theorem finSeed_succ (k : ℕ) (j : Fin k) :
    finSeed k j.succ = Sum.inr j := by
  show (if h : j.succ = 0 then Sum.inl () else Sum.inr (j.succ.pred h)) = Sum.inr j
  rw [dite_eq_right (Fin.succ_ne_zero j), Fin.pred_succ]

/-- Determinant of a matrix bordered by a scalar row and column.

`det` of
```
[ a  vᵀ ]
[ u  D  ]
```
is `a det D - v ⬝ adj(D) u`, over any commutative ring. -/
private theorem det_bordered_fin {R : Type*} [CommRing R] {k : ℕ}
    (a : R) (u v : Fin k → R) (D : Matrix (Fin k) (Fin k) R) :
    (Matrix.fromBlocks
        (Matrix.of fun (_ _ : Unit) => a)
        (Matrix.of fun (_ : Unit) (j : Fin k) => v j)
        (Matrix.of fun (i : Fin k) (_ : Unit) => u i)
        D).det =
      a * D.det - v ⬝ᵥ (D.adjugate *ᵥ u) := by
  classical
  let e := finSeed k
  set B := Matrix.fromBlocks
      (Matrix.of fun (_ _ : Unit) => a)
      (Matrix.of fun (_ : Unit) (j : Fin k) => v j)
      (Matrix.of fun (i : Fin k) (_ : Unit) => u i)
      D
  set M : Matrix (Fin (k + 1)) (Fin (k + 1)) R := B.submatrix e e
  have hMdet : M.det = B.det := by
    simp [M]
  rw [← hMdet]
  have h00 : M 0 0 = a := by
    simp only [M, B, Matrix.submatrix_apply, e, finSeed_zero]
    rfl
  have h0s (j : Fin k) : M 0 j.succ = v j := by
    simp only [M, B, Matrix.submatrix_apply, e, finSeed_zero, finSeed_succ]
    rfl
  have hs0 (i : Fin k) : M i.succ 0 = u i := by
    simp only [M, B, Matrix.submatrix_apply, e, finSeed_succ, finSeed_zero]
    rfl
  have hss (i j : Fin k) : M i.succ j.succ = D i j := by
    simp only [M, B, Matrix.submatrix_apply, e, finSeed_succ]
    rfl
  have hDD : M.submatrix Fin.succ Fin.succ = D := by
    ext i j
    simp [Matrix.submatrix_apply, hss]
  have hminor (i : Fin k) :
      (M.submatrix Fin.succ i.succ.succAbove).det =
        (-1 : R) ^ (i : ℕ) * (D.updateCol i u).det := by
    set S : Matrix (Fin k) (Fin k) R := M.submatrix Fin.succ i.succ.succAbove
    set σ : Equiv.Perm (Fin k) := Fin.cycleRange i
    have hS : S.submatrix id σ = D.updateCol i u := by
      ext r j
      simp only [S, Matrix.submatrix_apply, id_eq]
      have hcol : i.succ.succAbove (σ j) = Equiv.swap 0 i.succ j.succ := by
        simp [σ, Fin.succAbove_cycleRange]
      rw [hcol]
      by_cases hji : j = i
      · subst hji
        simp [Equiv.swap_apply_right, hs0, Matrix.updateCol_self]
      · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j)
          (fun h => hji ((Fin.succ_injective k) h))]
        simp [hss, hji]
    have hperm : (D.updateCol i u).det =
        (Equiv.Perm.sign σ : R) * S.det := by
      simpa [hS] using Matrix.det_permute' σ S
    have hsign : (Equiv.Perm.sign σ : R) = (-1) ^ (i : ℕ) := by
      simp [σ, Fin.sign_cycleRange]
    have hsq : (Equiv.Perm.sign σ : R) * Equiv.Perm.sign σ = 1 := by
      rw [hsign, ← pow_add, ← two_mul, pow_mul, pow_two]
      simp
    calc
      S.det = ((Equiv.Perm.sign σ : R) * Equiv.Perm.sign σ) * S.det := by
        rw [hsq, one_mul]
      _ = (Equiv.Perm.sign σ : R) * ((Equiv.Perm.sign σ : R) * S.det) := by
        rw [mul_assoc]
      _ = (Equiv.Perm.sign σ : R) * (D.updateCol i u).det := by
        rw [hperm]
      _ = (-1) ^ (i : ℕ) * (D.updateCol i u).det := by rw [hsign]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, h00, hDD]
  have hterm (i : Fin k) :
      (-1 : R) ^ (i.succ : ℕ) * M 0 i.succ *
          (M.submatrix Fin.succ i.succ.succAbove).det =
        -(v i * (D.updateCol i u).det) := by
    rw [h0s, hminor, Fin.val_succ]
    have hpow : (-1 : R) ^ ((i : ℕ) + 1) * (-1) ^ (i : ℕ) = -1 := by
      have hexp : (i : ℕ) + 1 + (i : ℕ) = 2 * (i : ℕ) + 1 := by omega
      rw [← pow_add, hexp, pow_add, pow_mul, pow_two]
      simp
    calc
      (-1 : R) ^ ((i : ℕ) + 1) * v i * ((-1) ^ (i : ℕ) * (D.updateCol i u).det) =
          ((-1) ^ ((i : ℕ) + 1) * (-1) ^ (i : ℕ)) * (v i * (D.updateCol i u).det) := by ring
      _ = -(v i * (D.updateCol i u).det) := by rw [hpow, neg_one_mul]
  simp_rw [hterm, Finset.sum_neg_distrib]
  have hdot : ∑ i : Fin k, v i * (D.updateCol i u).det = v ⬝ᵥ (D.adjugate *ᵥ u) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
  rw [hdot]
  ring

/-- Reindexing the leaf block of a cone does not change the border entries, only the leaf index. -/
private theorem fromBlocks_reindex_sumCongr {ι κ R : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [CommRing R]
    (e : ι ≃ κ) (a : R) (u v : ι → R) (D : Matrix ι ι R) :
    (Matrix.fromBlocks
        (Matrix.of fun (_ _ : Unit) => a)
        (Matrix.of fun (_ : Unit) (j : ι) => v j)
        (Matrix.of fun (i : ι) (_ : Unit) => u i)
        D).reindex ((Equiv.refl Unit).sumCongr e) ((Equiv.refl Unit).sumCongr e) =
      Matrix.fromBlocks
        (Matrix.of fun (_ _ : Unit) => a)
        (Matrix.of fun (_ : Unit) (j : κ) => v (e.symm j))
        (Matrix.of fun (i : κ) (_ : Unit) => u (e.symm i))
        (D.reindex e e) := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.reindex_apply, Equiv.sumCongr_apply, Equiv.sumCongr_symm,
      Matrix.of_apply]


private theorem det_bordered {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (a : R) (u v : ι → R) (D : Matrix ι ι R) :
    (Matrix.fromBlocks
        (Matrix.of fun (_ _ : Unit) => a)
        (Matrix.of fun (_ : Unit) (j : ι) => v j)
        (Matrix.of fun (i : ι) (_ : Unit) => u i)
        D).det =
      a * D.det - v ⬝ᵥ (D.adjugate *ᵥ u) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hre := fromBlocks_reindex_sumCongr e a u v D
  rw [← Matrix.det_reindex_self ((Equiv.refl Unit).sumCongr e)]
  rw [hre, det_bordered_fin]
  have hdet : (D.reindex e e).det = D.det := Matrix.det_reindex_self e D
  rw [hdet]
  congr 1
  rw [Matrix.adjugate_reindex]
  have hmul :
      ((D.adjugate).reindex e e) *ᵥ (fun i : Fin (Fintype.card ι) => u (e.symm i)) =
        (D.adjugate *ᵥ u) ∘ e.symm := by
    simpa [Matrix.reindex_apply, Function.comp_def, Equiv.symm_apply_apply] using
      Matrix.submatrix_mulVec_equiv (D.adjugate) (fun i => u (e.symm i)) e.symm e.symm
  rw [hmul]
  exact comp_equiv_dotProduct_comp_equiv v (D.adjugate *ᵥ u) (e.symm)

/-- Ascending-index `0` of `eigenvalues₀` is the smallest leaf eigenvalue. `eigenvalues₀`
itself is antitone, so this index is `Fin.last`. -/
private noncomputable def leafEig₀ (X : ℕ) :
    Fin (Fintype.card (HireLeaf (owners X))) → ℝ :=
  ((GgoldLeaves (owners X)).posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀

private theorem zero_mem_spectrum_lapMatrix_goldLeaves (X : ℕ)
    (hk : 1 ≤ Fintype.card (HireLeaf (owners X))) :
    (0 : ℝ) ∈ spectrum ℝ ((GgoldLeaves (owners X)).lapMatrix ℝ) := by
  have hpos : 0 < Fintype.card (HireLeaf (owners X)) := by omega
  obtain ⟨u⟩ := Fintype.card_pos_iff.mp hpos
  rw [← Matrix.spectrum_toLin']
  exact Module.End.HasEigenvalue.mem_spectrum <|
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_genEigenspace_one.mpr
          (by simpa [Matrix.toLin'_apply, zero_smul] using
            (GgoldLeaves (owners X)).lapMatrix_mulVec_one_eq_zero ℝ),
        fun h => by
          have h1 := congrFun h u
          simp only [Pi.one_apply, Pi.zero_apply] at h1
          exact one_ne_zero h1⟩

private theorem eigenvalues₀_goldLeaves_eq (X : ℕ)
    (j : Fin (Fintype.card (HireLeaf (owners X)))) :
    leafEig₀ X j =
      ((GgoldLeaves (owners X)).posSemidef_lapMatrix ℝ).isHermitian.eigenvalues
        (Fintype.equivOfCardEq
          (Fintype.card_fin (Fintype.card (HireLeaf (owners X)))) j) := by
  simp [leafEig₀, Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]

/-- `μ₁ = 0`: the smallest leaf-gold eigenvalue is `0`. -/
private theorem eigenvalues₀_goldLeaves_last (X : ℕ)
    (hk : 1 ≤ Fintype.card (HireLeaf (owners X))) :
    leafEig₀ X ⟨Fintype.card (HireLeaf (owners X)) - 1, by omega⟩ = 0 := by
  classical
  let hA := ((GgoldLeaves (owners X)).posSemidef_lapMatrix ℝ).isHermitian
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (HireLeaf (owners X))))
  have hnn (j : Fin (Fintype.card (HireLeaf (owners X)))) : 0 ≤ leafEig₀ X j := by
    have hpsd := (GgoldLeaves (owners X)).posSemidef_lapMatrix ℝ
    have hle : 0 ≤ hA.eigenvalues := (hA.posSemidef_iff_eigenvalues_nonneg).mp hpsd
    rw [eigenvalues₀_goldLeaves_eq]
    exact (Pi.le_def.mp hle) _
  have hmem : (0 : ℝ) ∈ spectrum ℝ ((GgoldLeaves (owners X)).lapMatrix ℝ) :=
    zero_mem_spectrum_lapMatrix_goldLeaves X hk
  rw [hA.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i, hi⟩ := hmem
  have hsome : leafEig₀ X (e.symm i) = 0 := by
    rw [eigenvalues₀_goldLeaves_eq]
    simpa [e, Equiv.apply_symm_apply] using hi
  have hle : leafEig₀ X ⟨Fintype.card (HireLeaf (owners X)) - 1, by omega⟩ ≤
      leafEig₀ X (e.symm i) := by
    apply hA.eigenvalues₀_antitone
    rw [Fin.le_def]
    exact Nat.le_sub_one_of_lt (e.symm i).isLt
  linarith [hnn ⟨Fintype.card (HireLeaf (owners X)) - 1, by omega⟩, hle, hsome]

private theorem eigenvalues₀_goldLeaves_nonneg (X : ℕ)
    (j : Fin (Fintype.card (HireLeaf (owners X)))) :
    0 ≤ leafEig₀ X j := by
  classical
  let hA := ((GgoldLeaves (owners X)).posSemidef_lapMatrix ℝ).isHermitian
  have hpsd := (GgoldLeaves (owners X)).posSemidef_lapMatrix ℝ
  have hle : 0 ≤ hA.eigenvalues := (hA.posSemidef_iff_eigenvalues_nonneg).mp hpsd
  rw [eigenvalues₀_goldLeaves_eq]
  exact (Pi.le_def.mp hle) _

private theorem eigenvalues₀_goldLeaves_le (X : ℕ)
    (j : Fin (Fintype.card (HireLeaf (owners X)))) :
    leafEig₀ X j ≤ (Fintype.card (HireLeaf (owners X)) : ℝ) := by
  rw [eigenvalues₀_goldLeaves_eq]
  exact eigenvalues_lapMatrix_le_card (GgoldLeaves (owners X)) _

/-- Middle index of the antitone cone list lands in the leaf spectrum. -/
private theorem leafIndex_middle (X : ℕ)
    (j : Fin (Fintype.card (HireVertex (owners X))))
    (h0 : (j : ℕ) ≠ 0)
    (hlast : (j : ℕ) ≠ Fintype.card (HireVertex (owners X)) - 1) :
    j.1 - 1 < Fintype.card (HireLeaf (owners X)) := by
  have hc := card_HireVertex_eq_succ_card_HireLeaf X
  have hj := j.isLt
  have := h0
  have := hlast
  omega

/-- Antitone cone list on `Fin n`: index `0` is `n`, indices `1, …, n - 2` are
`1 + μₙ₋₁, …, 1 + μ₂` in that decreasing order, index `n - 1` is `0`.
`0` is strictly last: every earlier entry is at least `1`. The leading `n` may
tie with `1 + μₙ₋₁`. -/
private noncomputable def coneRank (X : ℕ) :
    Fin (Fintype.card (HireVertex (owners X))) → ℝ := fun j =>
  let n := Fintype.card (HireVertex (owners X))
  if h0 : (j : ℕ) = 0 then (n : ℝ)
  else if hlast : (j : ℕ) = n - 1 then 0
  else 1 + leafEig₀ X ⟨j.1 - 1, leafIndex_middle X j h0 hlast⟩

private theorem coneRank_zero (X : ℕ)
    (hn : 1 ≤ Fintype.card (HireVertex (owners X))) :
    coneRank X ⟨0, by omega⟩ = (Fintype.card (HireVertex (owners X)) : ℝ) := by
  simp [coneRank]

private theorem coneRank_last (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    coneRank X ⟨Fintype.card (HireVertex (owners X)) - 1, by omega⟩ = 0 := by
  unfold coneRank
  dsimp only
  split_ifs with h0 hlast
  · omega
  · rfl
  · omega

private theorem coneRank_middle (X : ℕ)
    (j : Fin (Fintype.card (HireVertex (owners X))))
    (h0 : (j : ℕ) ≠ 0)
    (hlast : (j : ℕ) ≠ Fintype.card (HireVertex (owners X)) - 1) :
    coneRank X j = 1 + leafEig₀ X ⟨j.1 - 1, leafIndex_middle X j h0 hlast⟩ := by
  simp [coneRank, h0, hlast]

private theorem coneRank_nonneg (X : ℕ)
    (j : Fin (Fintype.card (HireVertex (owners X)))) :
    0 ≤ coneRank X j := by
  let n := Fintype.card (HireVertex (owners X))
  have hn1 : 1 ≤ n := by
    have := j.isLt
    omega
  by_cases h0 : (j : ℕ) = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext h0
    rw [hj, coneRank_zero X hn1]
    exact_mod_cast (Nat.zero_le n)
  · by_cases hlast : (j : ℕ) = n - 1
    · have hj : j = ⟨n - 1, by omega⟩ := Fin.ext hlast
      have hn2 : 2 ≤ n := by
        have := j.isLt
        omega
      rw [hj, coneRank_last X hn2]
    · rw [coneRank_middle X j h0 hlast]
      linarith [eigenvalues₀_goldLeaves_nonneg X ⟨j.1 - 1, leafIndex_middle X j h0 hlast⟩]

private theorem coneRank_le_card (X : ℕ)
    (hn : 1 ≤ Fintype.card (HireVertex (owners X)))
    (j : Fin (Fintype.card (HireVertex (owners X)))) :
    coneRank X j ≤ (Fintype.card (HireVertex (owners X)) : ℝ) := by
  let n := Fintype.card (HireVertex (owners X))
  let k := Fintype.card (HireLeaf (owners X))
  by_cases h0 : (j : ℕ) = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext h0
    rw [hj, coneRank_zero X hn]
  · by_cases hlast : (j : ℕ) = n - 1
    · have hj : j = ⟨n - 1, by omega⟩ := Fin.ext hlast
      have hn2 : 2 ≤ n := by
        have : (j : ℕ) < n := j.isLt
        omega
      rw [hj, coneRank_last X hn2]
      exact_mod_cast (Nat.zero_le n)
    · rw [coneRank_middle X j h0 hlast]
      have hleaf := eigenvalues₀_goldLeaves_le X ⟨j.1 - 1, leafIndex_middle X j h0 hlast⟩
      have hc := card_HireVertex_eq_succ_card_HireLeaf X
      have hcast : (n : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hc
      linarith

/-- `0` is strictly last in the antitone cone list. -/
private theorem coneRank_pos_of_ne_last (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X)))
    (j : Fin (Fintype.card (HireVertex (owners X))))
    (hlast : (j : ℕ) ≠ Fintype.card (HireVertex (owners X)) - 1) :
    0 < coneRank X j := by
  let n := Fintype.card (HireVertex (owners X))
  by_cases h0 : (j : ℕ) = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext h0
    rw [hj, coneRank_zero X (by omega)]
    exact_mod_cast (by omega : 0 < n)
  · rw [coneRank_middle X j h0 hlast]
    linarith [eigenvalues₀_goldLeaves_nonneg X ⟨j.1 - 1, leafIndex_middle X j h0 hlast⟩]

/-- The cone list decreases: `n ≥ 1 + μₙ₋₁ ≥ ⋯ ≥ 1 + μ₂ > 0`, allowing the
tie `1 + μₙ₋₁ = n`. -/
private theorem coneRank_antitone (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    Antitone (coneRank X) := by
  classical
  let n := Fintype.card (HireVertex (owners X))
  intro p q hpq
  by_cases hqL : (q : ℕ) = n - 1
  · have hq : q = ⟨n - 1, by omega⟩ := Fin.ext hqL
    rw [hq, coneRank_last X hn]
    exact coneRank_nonneg X p
  · by_cases hq0 : (q : ℕ) = 0
    · have hp0 : (p : ℕ) = 0 := by
        rw [Fin.le_def] at hpq
        omega
      have hp : p = ⟨0, by omega⟩ := Fin.ext hp0
      have hq : q = ⟨0, by omega⟩ := Fin.ext hq0
      rw [hp, hq]
    · by_cases hp0 : (p : ℕ) = 0
      · have hp : p = ⟨0, by omega⟩ := Fin.ext hp0
        rw [hp, coneRank_zero X (by omega)]
        exact coneRank_le_card X (by omega) q
      · by_cases hpL : (p : ℕ) = n - 1
        · rw [Fin.le_def] at hpq
          omega
        · rw [coneRank_middle X p hp0 hpL, coneRank_middle X q hq0 hqL]
          have hip := leafIndex_middle X p hp0 hpL
          have hiq := leafIndex_middle X q hq0 hqL
          have hle : (⟨p.1 - 1, hip⟩ : Fin (Fintype.card (HireLeaf (owners X)))) ≤
              ⟨q.1 - 1, hiq⟩ := by
            rw [Fin.le_def]
            simp
            rw [Fin.le_def] at hpq
            omega
          have hant :=
            ((GgoldLeaves (owners X)).posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀_antitone hle
          simpa [leafEig₀] using hant

open Polynomial

private theorem charpoly_goldLeaves_factor (X : ℕ)
    (hk : 1 ≤ Fintype.card (HireLeaf (owners X))) :
    ((GgoldLeaves (owners X)).lapMatrix ℝ).charpoly =
      Polynomial.X * ∏ i : Fin (Fintype.card (HireLeaf (owners X)) - 1),
        (Polynomial.X - C (leafEig₀ X ⟨(i : ℕ), by omega⟩)) := by
  classical
  let hA := ((GgoldLeaves (owners X)).posSemidef_lapMatrix ℝ).isHermitian
  let k := Fintype.card (HireLeaf (owners X))
  rw [hA.charpoly_eq]
  let e := Fintype.equivOfCardEq (Fintype.card_fin k)
  have hprod :
      (∏ i : HireLeaf (owners X), (Polynomial.X - C (RCLike.ofReal (hA.eigenvalues i)))) =
        ∏ j : Fin k, (Polynomial.X - C (leafEig₀ X j)) := by
    rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← eigenvalues₀_goldLeaves_eq]
    congr 2
  rw [hprod]
  have hk1 : (k - 1) + 1 = k := by omega
  rw [← Equiv.prod_comp (finCongr hk1)]
  rw [Fin.prod_univ_castSucc]
  have hidx (i : Fin (k - 1)) :
      finCongr hk1 i.castSucc = ⟨(i : ℕ), by omega⟩ := by
    apply Fin.ext
    simp
  have hlast :
      finCongr hk1 (Fin.last (k - 1)) = ⟨k - 1, by omega⟩ := by
    apply Fin.ext
    simp [Fin.val_last]
  rw [hlast, eigenvalues₀_goldLeaves_last X hk]
  simp only [C_0, sub_zero]
  rw [mul_comm]
  congr 1

private theorem charpoly_one_add_lap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℝ) :
    (1 + L).charpoly = L.charpoly.comp (Polynomial.X - C (1 : ℝ)) := by
  have h1 : (1 : Matrix ι ι ℝ) = Matrix.scalar ι (1 : ℝ) := by
    rw [Matrix.scalar_apply, Matrix.diagonal_one]
  have hneg : Matrix.scalar ι (1 : ℝ) = - Matrix.scalar ι (-1 : ℝ) := by
    rw [← map_neg, neg_neg]
  rw [h1, hneg, add_comm, ← sub_eq_add_neg, Matrix.charpoly_sub_scalar]
  congr 1
  simp [C_neg, sub_eq_add_neg]

/-- Characteristic polynomial of the hire Laplacian, factored as
`X (X - n)` times the leaf characteristic polynomial with the kernel factor
`X` removed and the indeterminate shifted by `1`. -/
private theorem charpoly_lapMatrix_GX_factor (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    ((GX X).lapMatrix ℝ).charpoly =
      Polynomial.X * (Polynomial.X - C (Fintype.card (HireVertex (owners X)) : ℝ)) *
        ((∏ i : Fin (Fintype.card (HireLeaf (owners X)) - 1),
            (Polynomial.X - C (leafEig₀ X ⟨(i : ℕ), by omega⟩))).comp
          (Polynomial.X - C (1 : ℝ))) := by
  classical
  let k := Fintype.card (HireLeaf (owners X))
  let n := Fintype.card (HireVertex (owners X))
  have hk : 1 ≤ k := by
    have hc := card_HireVertex_eq_succ_card_HireLeaf X
    omega
  have hkn : (n : ℝ) = (k : ℝ) + 1 := by
    have hc := card_HireVertex_eq_succ_card_HireLeaf X
    exact_mod_cast hc
  let L' := (GgoldLeaves (owners X)).lapMatrix ℝ
  rw [← Matrix.charpoly_reindex (seedLeavesEquiv (owners X)) ((GX X).lapMatrix ℝ)]
  rw [lapMatrix_GX_reindex_eq_fromBlocks]
  set A : Matrix (Unit ⊕ HireLeaf (owners X)) (Unit ⊕ HireLeaf (owners X)) ℝ :=
    Matrix.fromBlocks
      (Matrix.of fun _ _ => (k : ℝ))
      (Matrix.of fun _ _ => (-1 : ℝ))
      (Matrix.of fun _ _ => (-1 : ℝ))
      (1 + L')
  let D := Matrix.charmatrix (1 + L')
  have hform :
      A.charmatrix =
        Matrix.fromBlocks
          (Matrix.of fun _ _ => Polynomial.X - C (k : ℝ))
          (Matrix.of fun (_ : Unit) (_ : HireLeaf (owners X)) => (1 : ℝ[X]))
          (Matrix.of fun (_ : HireLeaf (owners X)) (_ : Unit) => (1 : ℝ[X]))
          D := by
    rw [Matrix.charmatrix_fromBlocks]
    ext i j
    cases i <;> cases j <;>
      simp [D, Matrix.charmatrix_apply_eq, Matrix.of_apply, map_neg]
  rw [Matrix.charpoly, hform, det_bordered]
  set Q : ℝ[X] := ∏ i : Fin (k - 1), (Polynomial.X - C (leafEig₀ X ⟨(i : ℕ), by omega⟩))
  have hQ : (1 + L').charpoly = (Polynomial.X - C (1 : ℝ)) * Q.comp (Polynomial.X - C (1 : ℝ)) := by
    rw [charpoly_one_add_lap, charpoly_goldLeaves_factor X hk]
    simp only [Q]
    rw [Polynomial.mul_comp, Polynomial.X_comp]
  rw [show D.det = (1 + L').charpoly from rfl, hQ]
  set ones : HireLeaf (owners X) → ℝ[X] := fun _ => 1
  set s : ℝ[X] := Q.comp (Polynomial.X - C (1 : ℝ))
  have hDmul : D *ᵥ ones = (Polynomial.X - C (1 : ℝ)) • ones := by
    have hL : L' *ᵥ (1 : HireLeaf (owners X) → ℝ) = 0 :=
      (GgoldLeaves (owners X)).lapMatrix_mulVec_one_eq_zero ℝ
    have hM : (1 + L') *ᵥ (1 : HireLeaf (owners X) → ℝ) = 1 := by
      rw [Matrix.add_mulVec, hL, Matrix.one_mulVec, add_zero]
    refine funext fun u => ?_
    have hchar : D = Matrix.scalar _ Polynomial.X - (1 + L').map C := rfl
    rw [hchar, Matrix.sub_mulVec]
    simp only [ones, Pi.sub_apply, Pi.smul_apply]
    have hsc : ((Matrix.scalar (HireLeaf (owners X)) Polynomial.X) *ᵥ fun _ => (1 : ℝ[X])) u =
        Polynomial.X := by
      simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply,
        Finset.sum_ite_eq, Finset.mem_univ]
    have hmap : (((1 + L').map C) *ᵥ fun _ => (1 : ℝ[X])) u = 1 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_one]
      rw [← map_sum]
      have hsum :
          ∑ j, (1 + L') u j = ((1 + L') *ᵥ (1 : HireLeaf (owners X) → ℝ)) u := by
        simp [Matrix.mulVec, dotProduct, mul_one]
      rw [hsum, hM]
      simp [C_1]
    rw [hsc, hmap]
    simp only [smul_eq_mul, mul_one]
    rw [← C_1]
  have hadj : D.adjugate *ᵥ ones = s • ones := by
    have hcancel :
        (Polynomial.X - C (1 : ℝ)) • (D.adjugate *ᵥ ones) = (Polynomial.X - C (1 : ℝ)) • (s • ones) := by
      calc
        (Polynomial.X - C (1 : ℝ)) • (D.adjugate *ᵥ ones)
            = D.adjugate *ᵥ ((Polynomial.X - C (1 : ℝ)) • ones) := by
              rw [← Matrix.mulVec_smul]
        _ = D.adjugate *ᵥ (D *ᵥ ones) := by rw [hDmul]
        _ = (D.adjugate * D) *ᵥ ones := by rw [← Matrix.mulVec_mulVec]
        _ = (D.det • (1 : Matrix _ _ ℝ[X])) *ᵥ ones := by rw [Matrix.adjugate_mul]
        _ = D.det • ones := by simp [Matrix.smul_mulVec, Matrix.one_mulVec]
        _ = ((Polynomial.X - C (1 : ℝ)) * s) • ones := by
              rw [show D.det = (1 + L').charpoly from rfl, hQ]
        _ = (Polynomial.X - C (1 : ℝ)) • (s • ones) := by rw [smul_smul, mul_comm]
    refine funext fun u => ?_
    have hu := congrFun hcancel u
    simp only [Pi.smul_apply, smul_eq_mul] at hu
    apply mul_left_cancel₀ (a := Polynomial.X - C (1 : ℝ))
      (Polynomial.X_sub_C_ne_zero (1 : ℝ))
    exact hu
  have hdot : ones ⬝ᵥ (D.adjugate *ᵥ ones) = (k : ℝ[X]) * s := by
    rw [hadj]
    simp only [dotProduct, ones, Pi.smul_apply, smul_eq_mul, mul_one, one_mul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  rw [hdot]
  have hkcast : (k : ℝ[X]) = C (k : ℝ) := (C_eq_natCast k).symm
  have hnC : C (n : ℝ) = C (k : ℝ) + 1 := by rw [hkn, map_add, C_1]
  rw [hkcast, hnC, C_1]
  ring

/-- `(X - C μ).comp (X - C 1) = X - C (1 + μ)`. -/
private theorem charpoly_shift_one (μ : ℝ) :
    (Polynomial.X - C μ).comp (Polynomial.X - C (1 : ℝ)) =
      Polynomial.X - C ((1 : ℝ) + μ) := by
  rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, sub_sub, ← C_add]

/-- Expanding the antitone cone list.
Index `0` contributes `X - C n`, indices `1, …, n - 2` contribute
`X - C (1 + μₙ₋₁), …, X - C (1 + μ₂)` in that order, and index `n - 1`
contributes `X`. The factor `X - C n` may equal the next factor. -/
private theorem prod_coneRank_eq_factor (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    (∏ j : Fin (Fintype.card (HireVertex (owners X))),
        (Polynomial.X - C (coneRank X j))) =
      Polynomial.X *
        (Polynomial.X - C (Fintype.card (HireVertex (owners X)) : ℝ)) *
        ((∏ i : Fin (Fintype.card (HireLeaf (owners X)) - 1),
            (Polynomial.X - C (leafEig₀ X ⟨(i : ℕ), by omega⟩))).comp
          (Polynomial.X - C (1 : ℝ))) := by
  classical
  let n := Fintype.card (HireVertex (owners X))
  let k := Fintype.card (HireLeaf (owners X))
  have hc : n = k + 1 := card_HireVertex_eq_succ_card_HireLeaf X
  have _ := hc
  have hk1 : (n - 1) + 1 = n := by omega
  have hm : (n - 2) + 1 = n - 1 := by omega
  have hleaf : n - 2 = k - 1 := by omega
  rw [← (finCongr hk1).prod_comp, Fin.prod_univ_castSucc]
  have hcast (j : Fin (n - 1)) :
      finCongr hk1 j.castSucc = (⟨(j : ℕ), by omega⟩ : Fin n) := by
    apply Fin.ext
    simp
  simp_rw [hcast]
  have hlastIdx :
      finCongr hk1 (Fin.last (n - 1)) = ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    simp [Fin.val_last]
  rw [hlastIdx, coneRank_last X hn, C_0, sub_zero, mul_comm, mul_assoc]
  congr 1
  rw [← (finCongr hm).prod_comp, Fin.prod_univ_succ]
  have hzero :
      finCongr hm (0 : Fin ((n - 2) + 1)) = (⟨0, by omega⟩ : Fin (n - 1)) := by
    apply Fin.ext
    simp
  have hsucc (i : Fin (n - 2)) :
      finCongr hm i.succ = (⟨i.1 + 1, by omega⟩ : Fin (n - 1)) := by
    apply Fin.ext
    simp [Fin.val_succ]
  simp_rw [hzero, hsucc]
  rw [coneRank_zero X (by omega)]
  congr 1
  rw [Polynomial.prod_comp, ← (finCongr hleaf).prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [charpoly_shift_one]
  have hi : (i : ℕ) < n - 2 := i.isLt
  have hlt : (i : ℕ) + 1 < n := by omega
  have h0 : ((⟨(i : ℕ) + 1, hlt⟩ : Fin n) : ℕ) ≠ 0 := by
    simp
  have hnl : ((⟨(i : ℕ) + 1, hlt⟩ : Fin n) : ℕ) ≠ n - 1 := by
    have := hi
    simpa using show (i : ℕ) + 1 ≠ n - 1 by omega
  rw [coneRank_middle X ⟨(i : ℕ) + 1, hlt⟩ h0 hnl]
  congr 1

private theorem one_add_eq_one_iff (μ : ℝ) : (1 : ℝ) + μ = 1 ↔ μ = 0 := by
  constructor <;> intro h <;> linarith

private theorem charpoly_lapMatrix_GX_eq_prod_coneRank (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    ((GX X).lapMatrix ℝ).charpoly =
      ∏ j : Fin (Fintype.card (HireVertex (owners X))),
        (Polynomial.X - C (coneRank X j)) := by
  rw [charpoly_lapMatrix_GX_factor X hn, prod_coneRank_eq_factor X hn]

set_option backward.isDefEq.respectTransparency.types false in
/-- Ranking step. `eigenvalues₀` is already the antitone order (index `0`
largest). `coneRank` is the same order by `coneRank_antitone`: index `0` is
`n`, then `1 + μₙ₋₁ ≥ ⋯ ≥ 1 + μ₂`, then `0` strictly last
(`coneRank_pos_of_ne_last`; the leading `n` may tie with `1 + μₙ₋₁`). The
characteristic polynomial is the product of `X - C (coneRank j)` in that
index order, so the sorted real roots are `List.ofFn coneRank`, which is
also `List.ofFn eigenvalues₀`. -/
private theorem eigenvalues₀_eq_coneRank (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    ((GX X).posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀ = coneRank X := by
  classical
  let hA := ((GX X).posSemidef_lapMatrix ℝ).isHermitian
  have hchar := charpoly_lapMatrix_GX_eq_prod_coneRank X hn
  simp_rw [← List.ofFn_inj]
  rw [← hA.sort_roots_charpoly_eq_eigenvalues₀, hchar]
  have hnz : (∏ j : Fin (Fintype.card (HireVertex (owners X))),
      (Polynomial.X - C (coneRank X j))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Polynomial.X_sub_C_ne_zero _
  have hroots :
      (∏ j : Fin (Fintype.card (HireVertex (owners X))),
          (Polynomial.X - C (coneRank X j))).roots =
        Finset.univ.val.map (coneRank X) := by
    rw [Polynomial.roots_prod _ _ hnz]
    simp_rw [Polynomial.roots_X_sub_C]
    rw [Multiset.bind_singleton]
  simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.re_to_real, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact (coneRank_antitone X hn).sortedGE_ofFn

/-- **Layer C spectrum reading.**

Ascending eigenvalues `λ₁ ≤ ⋯ ≤ λₙ` of `(GX X).lapMatrix` and
`μ₁ ≤ ⋯ ≤ μₖ` of the leaf gold Laplacian, with `k = n - 1` leaves.
The antitone cone list (`coneRank`) is pinned as

`n ≥ 1 + μₙ₋₁ ≥ ⋯ ≥ 1 + μ₂ > 0`,

index `0` first (`λₙ = n`) and `0` strictly last (`λ₁`). The leading `n` may
tie with `1 + μₙ₋₁`. For the matching ranks `i = 2, …, n - 1`,

`λᵢ = 1 + μᵢ`.
-/
theorem spectrum_lapMatrix_GX (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X)))
    (i : ℕ) (hi2 : 2 ≤ i) (hi : i + 1 ≤ Fintype.card (HireVertex (owners X))) :
    lambda_GX X i (by omega) (by omega) =
      (1 : ℝ) + mu_goldLeaves X i (by omega) (by
        have hc := card_HireVertex_eq_succ_card_HireLeaf X
        omega) := by
  classical
  let n := Fintype.card (HireVertex (owners X))
  let k := Fintype.card (HireLeaf (owners X))
  have hc : n = k + 1 := card_HireVertex_eq_succ_card_HireLeaf X
  unfold lambda_GX
  dsimp only
  rw [eigenvalues₀_eq_coneRank X hn]
  unfold mu_goldLeaves
  dsimp only
  have hlt : n - i < n := by omega
  have h0n : n - i ≠ 0 := by omega
  have hlastn : n - i ≠ n - 1 := by omega
  have h0 : ((⟨n - i, hlt⟩ : Fin n) : ℕ) ≠ 0 := by simpa using h0n
  have hlast : ((⟨n - i, hlt⟩ : Fin n) : ℕ) ≠ n - 1 := by simpa using hlastn
  rw [coneRank_middle X ⟨n - i, hlt⟩ h0 hlast]
  unfold leafEig₀
  congr 1
  congr 1
  apply Fin.ext
  change (n - i) - 1 = k - i
  have := hc
  omega


/-- On a finite simple graph with at least two vertices, the second-smallest
Laplacian eigenvalue is `0` iff the graph is not connected.

`posSemidef_lapMatrix` makes every eigenvalue nonnegative, and the constants
are a kernel vector, so the smallest eigenvalue is `0`.
`card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` identifies the
number of components with `dim ker`. Rank-nullity and
`IsHermitian.rank_eq_card_non_zero_eigs` make that dimension the multiplicity
of the eigenvalue `0`. `eigenvalues₀` is antitone, so the second-smallest
entry vanishes iff that multiplicity is at least `2`. On a nonempty graph
that is exactly "more than one component", which is `¬ Connected`. -/
private theorem eigenvalues₀_lapMatrix_two_eq_zero_iff_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hk : 2 ≤ Fintype.card V) :
    ((G.posSemidef_lapMatrix ℝ).isHermitian.eigenvalues₀
        ⟨Fintype.card V - 2, by omega⟩ = 0) ↔ ¬ G.Connected := by
  classical
  let k := Fintype.card V
  let hA := (G.posSemidef_lapMatrix ℝ).isHermitian
  have hk0 : 0 < k := by omega
  let j1 : Fin k := ⟨k - 1, by omega⟩
  let j2 : Fin k := ⟨k - 2, by omega⟩
  have hrew (h : k - 2 < k) :
      hA.eigenvalues₀ ⟨k - 2, h⟩ = hA.eigenvalues₀ j2 := by
    have : (⟨k - 2, h⟩ : Fin k) = j2 := Fin.ext rfl
    rw [this]
  rw [hrew]
  have hnn (j : Fin k) : 0 ≤ hA.eigenvalues₀ j := by
    have hle : 0 ≤ hA.eigenvalues :=
      (hA.posSemidef_iff_eigenvalues_nonneg).mp (G.posSemidef_lapMatrix ℝ)
    have hidx := (Pi.le_def.mp hle) (Fintype.equivOfCardEq (Fintype.card_fin k) j)
    simpa [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using hidx
  have hker : Module.finrank ℝ (G.lapMatrix ℝ).toLin'.ker =
      Fintype.card {i : V // hA.eigenvalues i = 0} := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (G.lapMatrix ℝ).toLin'
    rw [Module.finrank_fintype_fun_eq_card] at hrn
    have hrank : (G.lapMatrix ℝ).rank =
        Module.finrank ℝ (LinearMap.range (G.lapMatrix ℝ).toLin') := by
      unfold Matrix.rank
      rw [Matrix.toLin'_apply']
    rw [← hrank] at hrn
    have hker_sub : Module.finrank ℝ (G.lapMatrix ℝ).toLin'.ker =
        k - (G.lapMatrix ℝ).rank := Nat.eq_sub_of_add_eq' hrn
    have hrewrite : Fintype.card {i : V // hA.eigenvalues i = 0} =
        Fintype.card {i : V // ¬ hA.eigenvalues i ≠ 0} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun _ => not_ne_iff.symm)
    rw [hker_sub, hrewrite, Fintype.card_subtype_compl
      (fun i : V => hA.eigenvalues i ≠ 0), hA.rank_eq_card_non_zero_eigs]
  have hcomp : Fintype.card G.ConnectedComponent =
      Module.finrank ℝ (G.lapMatrix ℝ).toLin'.ker :=
    G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix
  have hsame : Fintype.card {j : Fin k // hA.eigenvalues₀ j = 0} =
      Fintype.card {i : V // hA.eigenvalues i = 0} := by
    let e := Fintype.equivOfCardEq (Fintype.card_fin k)
    refine Fintype.card_congr (e.subtypeEquiv fun j => ?_)
    simp [e, Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]
  have : Nonempty V := Fintype.card_pos_iff.mp hk0
  have hconn : G.Connected ↔ Fintype.card G.ConnectedComponent = 1 := by
    constructor
    · intro hc
      have : Subsingleton G.ConnectedComponent :=
        hc.preconnected.subsingleton_connectedComponent
      have : Nonempty G.ConnectedComponent := inferInstance
      exact Fintype.card_eq_one_iff.mpr
        ⟨Classical.choice ‹Nonempty G.ConnectedComponent›, fun y => Subsingleton.elim y _⟩
    · intro hcard
      have hsub : Subsingleton G.ConnectedComponent := by
        rw [← Fintype.card_le_one_iff_subsingleton]
        omega
      have hne : Nonempty G.ConnectedComponent :=
        Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card G.ConnectedComponent)
      let c : G.ConnectedComponent := Classical.choice hne
      rw [SimpleGraph.connected_iff]
      refine ⟨fun u w => ?_, inferInstance⟩
      exact SimpleGraph.ConnectedComponent.exact <|
        (Subsingleton.elim (h := hsub) (G.connectedComponentMk u) c).trans
          (Subsingleton.elim (h := hsub) (G.connectedComponentMk w) c).symm
  have hdis : ¬ G.Connected ↔ 2 ≤ Fintype.card G.ConnectedComponent := by
    have hpos : 0 < Fintype.card G.ConnectedComponent :=
      Fintype.card_pos
    constructor
    · intro hnot
      have hne : Fintype.card G.ConnectedComponent ≠ 1 := fun h1 => hnot (hconn.mpr h1)
      omega
    · intro h2 hc
      exact (by omega : Fintype.card G.ConnectedComponent ≠ 1) (hconn.mp hc)
  have hj : j2 ≤ j1 := by
    rw [Fin.le_def]
    simp only [j1, j2]
    omega
  have hj_ne : j1 ≠ j2 := by
    intro h
    have := congrArg (Fin.val) h
    simp only [j1, j2] at this
    omega
  have hmu : hA.eigenvalues₀ j2 = 0 ↔
      2 ≤ Fintype.card {j : Fin k // hA.eigenvalues₀ j = 0} := by
    constructor
    · intro hz
      have hz1 : hA.eigenvalues₀ j1 = 0 := by
        have hle : hA.eigenvalues₀ j1 ≤ hA.eigenvalues₀ j2 := hA.eigenvalues₀_antitone hj
        linarith [hle, hz, hnn j1]
      have hne : (⟨j1, hz1⟩ : {j : Fin k // hA.eigenvalues₀ j = 0}) ≠ ⟨j2, hz⟩ := by
        intro heq
        exact hj_ne (congrArg Subtype.val heq)
      have : Nontrivial {j : Fin k // hA.eigenvalues₀ j = 0} :=
        ⟨⟨j1, hz1⟩, ⟨j2, hz⟩, hne⟩
      have : 1 < Fintype.card {j : Fin k // hA.eigenvalues₀ j = 0} :=
        Fintype.one_lt_card_iff_nontrivial.mpr this
      omega
    · intro hcard
      by_contra hne0
      have hpos2 : 0 < hA.eigenvalues₀ j2 := lt_of_le_of_ne (hnn j2) (Ne.symm hne0)
      have hsub : Subsingleton {j : Fin k // hA.eigenvalues₀ j = 0} := by
        constructor
        intro a b
        have hidx (c : {j : Fin k // hA.eigenvalues₀ j = 0}) : c.1 = j1 := by
          apply Fin.ext
          have hlt := c.1.isLt
          have hle_or : c.1.val ≤ k - 2 ∨ c.1.val = k - 1 := by omega
          rcases hle_or with hle | hlast
          · have hle' : c.1 ≤ j2 := by
              rw [Fin.le_def]
              simpa [j2, Fin.val_mk] using hle
            have hge' : hA.eigenvalues₀ j2 ≤ hA.eigenvalues₀ c.1 :=
              hA.eigenvalues₀_antitone hle'
            have hneq : hA.eigenvalues₀ c.1 ≠ 0 := by linarith
            exact False.elim (hneq c.2)
          · simpa [j1, Fin.val_mk] using hlast
        exact Subtype.ext (hidx a ▸ hidx b ▸ rfl)
      have : Fintype.card {j : Fin k // hA.eigenvalues₀ j = 0} ≤ 1 :=
        Fintype.card_le_one_iff_subsingleton.mpr hsub
      omega
  rw [hmu, hsame, ← hker, ← hcomp]
  exact hdis.symm

/-- **Layer D.** On a window with at least two leaves, `λ₂ = 1` iff gold on
the leaves is disconnected.

`spectrum_lapMatrix_GX` at index `2` is `λ₂ = 1 + μ₂`, so `λ₂ = 1` iff
`μ₂ = 0`. With `k ≥ 2` leaves, `μ₂ = 0` is the ordered reading of a
Laplacian kernel of dimension at least `2`, which is
`card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`: at least two
components, so `GgoldLeaves` is not connected.
-/
theorem lambda2_eq_one_iff_GoldLeavesDisconnected (X : ℕ)
    (hk : 2 ≤ Fintype.card (HireLeaf (owners X))) :
    lambda_GX X 2 (by omega) (by
        have hc := card_HireVertex_eq_succ_card_HireLeaf X
        omega) =
      1 ↔ GoldLeavesDisconnected (owners X) := by
  have hshift := spectrum_lapMatrix_GX X
    (by
      have hc := card_HireVertex_eq_succ_card_HireLeaf X
      omega)
    2 (by omega) (by
      have hc := card_HireVertex_eq_succ_card_HireLeaf X
      omega)
  rw [hshift, one_add_eq_one_iff]
  unfold mu_goldLeaves GoldLeavesDisconnected
  exact eigenvalues₀_lapMatrix_two_eq_zero_iff_not_connected
    (GgoldLeaves (owners X)) hk

end Hire
