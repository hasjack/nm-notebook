/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Lemma8
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul

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
Mathlib has no Laplacian bound by the number of doors; the bound used for
`λₙ` is the complete-graph comparison `eigenvalues_lapMatrix_le_card`. The
middle shift stays `sorry`.

`lambda2_eq_one_iff_GoldLeavesDisconnected` is the Layer D sentence
`λ₂ = 1` iff gold-on-leaves is disconnected, obtained as `λ₂ = 1 + μ₂` from
that statement. The step `μ₂ = 0` iff the leaf gold graph is disconnected is
not proved here. Layer D is not a checked proof.
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

Mathlib has no `eigenvalues_le_card` (and no spectral-radius bound of a
Laplacian by `Fintype.card`). The comparison proved here is the complete graph:
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

private theorem one_add_eq_one_iff (μ : ℝ) : (1 : ℝ) + μ = 1 ↔ μ = 0 := by
  constructor <;> intro h <;> linarith

/-- **Layer C spectrum reading (not proved).**

Ascending eigenvalues `λ₁ ≤ ⋯ ≤ λₙ` of `(GX X).lapMatrix` and
`μ₁ ≤ ⋯ ≤ μₖ` of the leaf gold Laplacian, with `k = n - 1` leaves.
For `i = 2, …, n - 1`,

`λᵢ = 1 + μᵢ`.

The shift **starts at `μ₂`, not `μ₁`**. `μ₁ = 0` is the leaf all-ones vector.
Mixing it with the seed already accounts for the global kernel
(`hasEigenvector_lapMatrix_GX_zero`); the other mix of that same direction is
the star-max eigenvalue `n` (`card_mem_spectrum_lapMatrix_GX`). Folding `μ₁`
into `1 + μ` would double-count the kernel.

A set-level union `{0, n} ∪ {1 + μ | μ ∈ spectrum L', μ ≠ 0}` is not used:
`spectrum` forgets multiplicity, so a repeated leaf zero (gold leaves
disconnected) never appears as a new point, and eigenvalue `1` would be lost.
`four_vertex_star_leaf_edge_keeps_one` is that case. The ordered shift is the
honest form. The endpoints are `lambda_GX_one` and `lambda_GX_card`.
This middle identification stays `sorry`.
-/
theorem spectrum_lapMatrix_GX (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X)))
    (i : ℕ) (hi2 : 2 ≤ i) (hi : i + 1 ≤ Fintype.card (HireVertex (owners X))) :
    lambda_GX X i (by omega) (by omega) =
      (1 : ℝ) + mu_goldLeaves X i (by omega) (by
        have hc := card_HireVertex_eq_succ_card_HireLeaf X
        omega) := by
  sorry

/-- **Layer D sentence, not a checked proof.**

On a window with at least two leaves, the cone reading specialises to
`λ₂ = 1 + μ₂` (`spectrum_lapMatrix_GX` at index `2`). Therefore
`λ₂ = 1` iff `μ₂ = 0`.

`μ₂ = 0` is the ordered reading of "gold on the leaves is disconnected".
That last step is `sorry`: this corollary assumes the spectrum identification
and does not prove disconnected gold from scratch. Layer D stays open as a
checked argument.
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
  -- Endpoints are `lambda_GX_one` and `lambda_GX_card`. They are not this step.
  -- `μ₂ = 0` iff the leaf gold graph is disconnected. Not proved here.
  sorry

end Hire
