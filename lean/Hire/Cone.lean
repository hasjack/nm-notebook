/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Lemma8
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block

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

The block equality is proved. The spectrum reading
`spec = {0, n} ∪ {1 + μᵢ}` is the next gap and is not stated here.

Card 4, as a comment only: `four_vertex_star_leaf_edge_keeps_one` is the
`μ₂ = 0` special case of this block. One gold chord on three leaves leaves the
leaf gold graph disconnected, so a zero eigenvalue of `L'` would shift to
eigenvalue `1` of `GX`. That identification is not proved in this module.
Layer D (`λ₂ = 1` iff the gold leaves are disconnected) is not claimed here.
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

end Hire
