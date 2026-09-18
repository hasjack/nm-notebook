# Lemma 8 — proof map

Target claim (note, cone formula): on the hire graph \(H_X\) (star on 2 plus undirected gold),
\(\lambda_2(H_X)=1\) exactly when the undirected gold graph on the leaves is disconnected
(\(\mu_2(L'_X)=0\)).

```
Paper path
──────────
Lemma 7   λ_max(H_X)=n   (star eigenvector; gold edges contribute 0)
    │
    ▼
Lemma 8   cone / block form
          H_X = [ k  -1ᵀ ]
                [ -1  I+L' ]
          ⇒  spec(H_X) = {0,n} ∪ {1+μ₂,…,1+μ_{n-1}}
          ⇒  λ₂(H_X)=1  ⟺  gold-on-leaves disconnected
```

```
Lean path today (lean/Hire/)
───────────────────────────
Doors / HireSet / Graph / StarLap
    │
    ▼
GoldFree  ──►  G = Gstar  ──►  1 ∈ spectrum, n ∈ spectrum, Connected
               (Lemma8.lean forward)         (StarLap helpers)

Layer B footholds (proved):
  • lapMatrix_toLinearMap₂'_sup_edge
      xᵀ L' x = xᵀ L x + (x_a - x_b)²
  • three_vertex_star_leaf_edge_not_second_one  (card V = 3 only)
      star + leaf edge = K₃; 1 ∉ spectrum; ¬ HasSecondLaplacianEigenvalueOne
  • four_vertex_star_leaf_edge_keeps_one  (card V = 4)
      star + one leaf gold chord stays connected and keeps eigenvalue 1
      (center 0, joined leaves 1, hanging leaf −2); weak predicate survives
      comment only: this is the μ₂ = 0 special case of the Layer C block
      (one gold chord on three leaves); not a new proof

Layer C block (proved, Hire/Cone.lean):
  seedLeavesEquiv : doors ≃ seed ⊕ leaves
  lapMatrix_GX_reindex_eq_fromBlocks
      [ k    -1ᵀ ]
      [ -1   I+L' ]
  entries: lapMatrix_GX_seed_diag, lapMatrix_GX_seed_leaf,
           lapMatrix_GX_leaf_seed, lapMatrix_GX_leaf_diag,
           lapMatrix_GX_leaf_off, lapMatrix_GX_leaf_block

Layer C spectrum (Hire/Cone.lean):
  proved:
    hasEigenvector_lapMatrix_GX_zero, zero_mem_spectrum_lapMatrix_GX
      all-ones on the seed door and the leaves; kernel value 0
    lapMatrix_GX_mulVec_starMaxEigenvec, card_mem_spectrum_lapMatrix_GX
      star-max vector (n-1 on the seed, -1 on every leaf) is an
      n-eigenvector when n ≥ 2; gold edges contribute 0
      (starMaxEigenvec_sub_eq_zero_of_ne_seed: constant on the leaves)
    eigenvector_of_leaf_mode, lapMatrix_GX_mulVec_leafMode
      0 on the seed, L'-eigenvector v on the leaves, eigenvalue 1+μ
      only when ∑ v = 0
    lambda_GX_one
      ordered λ₁ = 0 (n ≥ 1). Laplacian is positive semidefinite
      (posSemidef_iff_eigenvalues_nonneg on posSemidef_lapMatrix),
      so eigenvalues₀ ≥ 0, and 0 is achieved, so the last
      (smallest) entry is 0
    lambda_GX_card
      ordered λₙ = n when n ≥ 2. n is achieved by the star-max vector,
      and it is maximal. Mathlib has no eigenvalues_le_card for a
      Laplacian. eigenvalues_lapMatrix_le_card is proved here:
      quadratic form of G is at most that of the complete graph, and
      lapMatrix_top is n minus the all-ones matrix, whose form is
      n ‖x‖² − (∑ x)²
  sorry (middle shift only, not a set union):
    spectrum_lapMatrix_GX
      ascending λᵢ = 1 + μᵢ for i = 2, …, n-1
      endpoints are lambda_GX_one and lambda_GX_card, not this sorry
      cutoff is μ₂, not μ₁: μ₁ = 0 is the leaf all-ones vector and is
      already the global kernel (folding it into 1+μ double-counts 0)
      a set union {0,n} ∪ {1+μ | μ ≠ 0} is not used: spectrum forgets
      multiplicity, so a repeated leaf zero (the card-4 chord) never
      appears as a new point and eigenvalue 1 would be lost
  corollary, not a checked Layer D proof:
    lambda2_eq_one_iff_GoldLeavesDisconnected
      λ₂ = 1 + μ₂ by specialising the spectrum statement (index 2)
      then sorry: μ₂ = 0 iff gold-on-leaves is disconnected
      does not prove disconnected gold from scratch

lemma8_converse_card_three : HasSecondLaplacianEigenvalueOne ⇒ GoldFree
    └── card = 3 only, no sorry:
        GX_eq_star_sup_edge_of_gold_card_three
        → three_vertex_star_leaf_edge_not_second_one
    n=4 does not extend: four_vertex_star_leaf_edge_keeps_one
        shows the weak predicate survives one leaf chord

GoldLeavesDisconnected  := ¬ (GgoldLeaves).Connected
    └── distinct from GoldFree; forests allowed
    └── GoldFree ⇒ GoldLeavesDisconnected (when ≥2 leaves)
    └── money line typed as lambda2_eq_one_iff_GoldLeavesDisconnected; the μ₂=0 step is sorry
```

## Layers

| Layer | Content | Status |
|-------|---------|--------|
| A | `GoldFree` ⇒ `G = Gstar` ⇒ `1` and `n` in spectrum | Checked (`Lemma8` + `StarLap`) |
| B | Hire star, gold edges, finite windows | n=3 proved: K₃ kills the weak predicate, and `lemma8_converse_card_three` reaches `GoldFree` with no sorry. n=4: one leaf chord keeps `HasSecondLaplacianEigenvalueOne`, so the GoldFree converse does not extend. Remaining open spectral project: ordered `λ₂` toward Layer D |
| C | Cone block `[ k -1ᵀ ; -1 I+L' ]` and the ordered shift `λᵢ = 1 + μᵢ` for `i ≥ 2` | Block equality proved, no sorry. Eigenvalues `0` and `n` proved as spectrum members and as ordered endpoints `lambda_GX_one`, `lambda_GX_card`. The upper bound is not in Mathlib; `eigenvalues_lapMatrix_le_card` compares with the complete graph. Leaf mode proved (`∑ v = 0`). Middle shift `spectrum_lapMatrix_GX` is still one sorry |
| D | `λ₂=1` ⟺ `GoldLeavesDisconnected` | Stated as `lambda2_eq_one_iff_GoldLeavesDisconnected`, read off `λ₂ = 1 + μ₂`. The step `μ₂ = 0` iff the leaf gold graph is disconnected is sorry. Not a checked proof |

## Dependency order for Lean

1. Keep Layer A as the present stake.
2. Layer B n=3 is proved. n=4 shows the weak predicate survives one chord, so the GoldFree converse does not extend. The remaining open spectral project is ordered λ₂ toward Layer D, with no false sorry left in the converse.
3. Layer C block equality is proved (`lapMatrix_GX_reindex_eq_fromBlocks`). Eigenvalue `0` (all-ones) and eigenvalue `n` (star-max, gold differences zero) are proved, including the ordered endpoints `lambda_GX_one` (`λ₁ = 0`) and `lambda_GX_card` (`λₙ = n` for `n ≥ 2`). Mathlib does not bound Laplacian eigenvalues by `Fintype.card`; that bound is `eigenvalues_lapMatrix_le_card`, from `lapMatrix_top`. `eigenvector_of_leaf_mode` is proved when `∑ v = 0`. The middle shift `spectrum_lapMatrix_GX` (`λᵢ = 1 + μᵢ` for `i = 2, …, n − 1`) is still one sorry. The set form is not stated: it would miss a repeated `μ₂ = 0`. Card 4 is that case, still a comment, not a new proof.
4. Layer D is typed as `lambda2_eq_one_iff_GoldLeavesDisconnected`: `λ₂ = 1` iff gold-on-leaves is disconnected, by `λ₂ = 1 + μ₂` from the spectrum statement. The connectivity step is sorry. Not proved from scratch.

Layer B alone does not unlock Layer D: zero gold is stricter than a disconnected forest.

## Modules

- Checked spine: `Doors`, `HireSet`, `Graph`, `StarLap`, `Lemma8` forward + Layer B footholds, `Cone` block equality
- Named separately: `HireLeaf`, `GgoldLeaves`, `GoldLeavesDisconnected` (no longer an alias of `GoldFree`)
- Open: `spectrum_lapMatrix_GX` (one sorry; middle ordered shift `λᵢ = 1 + μᵢ` for `i = 2, …, n − 1`; endpoints `lambda_GX_one` and `lambda_GX_card` are proved) and the connectivity step of `lambda2_eq_one_iff_GoldLeavesDisconnected` (second sorry; `μ₂ = 0` iff gold-on-leaves is disconnected is not proved; Layer D not checked). No sorry in `lemma8_converse_card_three`. Dirichlet owner stub in `Dirichlet.lean`
- Paper: `paper/two_doors.tex` Lemmas 7–8 and the window table
