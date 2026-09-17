/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.StarLap
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Operations

set_option maxHeartbeats 800000

/-!
# Lemma 8 sketch: `λ₂ = 1` iff gold leaves are disconnected

Paper core: on the hire graph (star on 2 plus gold chords), the second Laplacian
eigenvalue equals `1` precisely when the undirected gold graph on the leaves is
disconnected (forests allowed; equivalently `μ₂(L') = 0`).

This module records the combinatorial half cleanly and the spectral half as far
as Mathlib reaches without a full interlacing development:

* `GoldFree` ⇒ hire graph equals the pure star;
* pure star with two leaves has Laplacian eigenvalue `1` (from `StarLap`);
* `GoldLeavesDisconnected` names the paper money line separately from `GoldFree`;
* Layer B footholds (proved): quadratic-form bump; star on three vertices plus
  the leaf edge is the triangle, so `1 ∉ spectrum` / weak
  `HasSecondLaplacianEigenvalueOne` fails;
* converse sketch wires gold leaf chords to that foothold for `card = 3`; larger
  windows keep one honest `sorry` (ordered `λ₂` / Courant–Fischer / Cauchy
  interlacing). A single leaf chord on ≥3 leaves does **not** kill eigenvalue
  `1`, so Layer B still undershoots Layer D (forests / money line).

Public voice: doors, hire set, gold edges, finite windows.
-/

namespace Hire

/-- No undirected gold chord on hired vertices. -/
def GoldFree (O : Set ℕ) : Prop :=
  ∀ u v : HireVertex O, ¬ GoldEdge O u v

/-- Leaf vertices: hired vertices other than the seed. -/
abbrev HireLeaf (O : Set ℕ) : Type :=
  { v : HireVertex O // v ≠ seedVertex O }

/-- Undirected gold graph on leaves only (star spokes omitted). -/
def GgoldLeaves (O : Set ℕ) : SimpleGraph (HireLeaf O) :=
  SimpleGraph.fromRel fun u v => GoldEdge O u.1 v.1

/-- Gold-on-leaves disconnected: the leaf gold graph is not connected.
This is the paper money line (forests allowed). `GoldFree` is the stricter
zero-edge special case used by Layer A. -/
def GoldLeavesDisconnected (O : Set ℕ) : Prop :=
  ¬ (GgoldLeaves O).Connected

theorem not_adj_GgoldLeaves_of_GoldFree {O : Set ℕ} (h : GoldFree O)
    (u v : HireLeaf O) : ¬ (GgoldLeaves O).Adj u v := by
  intro hadj
  have hfr :=
    (SimpleGraph.fromRel_adj (fun u v : HireLeaf O => GoldEdge O u.1 v.1) u v).mp hadj
  cases hfr.2 with
  | inl hg => exact h u.1 v.1 hg
  | inr hg => exact h v.1 u.1 hg

/-- Zero gold among leaves implies the leaf gold graph is disconnected once two
distinct leaves exist. -/
theorem GoldLeavesDisconnected_of_GoldFree {O : Set ℕ} (h : GoldFree O)
    {a b : HireLeaf O} (hab : a ≠ b) : GoldLeavesDisconnected O := by
  intro hc
  obtain ⟨w⟩ := hc a b
  cases w with
  | nil => exact hab rfl
  | cons hadj _ => exact (not_adj_GgoldLeaves_of_GoldFree h _ _ hadj).elim

theorem hireRel_eq_StarEdge_of_goldFree {O : Set ℕ} (h : GoldFree O)
    (u v : HireVertex O) : hireRel O u v ↔ StarEdge O u v := by
  constructor
  · rintro (hs | hg)
    · exact hs
    · exact (h u v hg).elim
  · exact Or.inl

/-- Star incidence matches Mathlib `starGraph` at the seed. -/
theorem StarEdge_iff_starGraph {O : Set ℕ} (u v : HireVertex O) :
    StarEdge O u v ↔ u = seedVertex O ∨ v = seedVertex O := by
  simp [StarEdge, seedVertex_eq_iff]

/-- **Combinatorial Lemma 8 (⇒ direction setup):** no gold ⇒ `G = Gstar`. -/
theorem G_eq_Gstar_of_goldFree {O : Set ℕ} (h : GoldFree O) :
    G O = Gstar O := by
  ext u v
  simp only [G, Gstar, SimpleGraph.fromRel_adj, SimpleGraph.starGraph_adj,
    hireRel_eq_StarEdge_of_goldFree h, StarEdge_iff_starGraph]
  tauto

theorem GX_eq_GXstar_of_goldFree {X : ℕ} (h : GoldFree (owners X)) :
    GX X = GXstar X :=
  G_eq_Gstar_of_goldFree h

/-- Transport Laplacian along graph equality (DecidableRel is a subsingleton). -/
theorem lapMatrix_eq_of_graph_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G = H) :
    G.lapMatrix ℝ = H.lapMatrix ℝ := by
  subst h
  congr 1

/-- Under `GoldFree`, eigenvalue `1` appears for windows with at least two leaves. -/
theorem one_mem_spectrum_GX_of_goldFree {X : ℕ}
    (h : GoldFree (owners X))
    {a b : HireVertex (owners X)}
    (ha : a ≠ seedVertex (owners X)) (hb : b ≠ seedVertex (owners X))
    (hab : a ≠ b) :
    (1 : ℝ) ∈ spectrum ℝ ((GX X).lapMatrix ℝ) := by
  classical
  rw [lapMatrix_eq_of_graph_eq (GX_eq_GXstar_of_goldFree h)]
  exact one_mem_spectrum_lapMatrix_starGraph_of_two_leaves
    (seedVertex (owners X)) a b ha hb hab

/-- Under `GoldFree` and `|V| ≥ 2`, eigenvalue `|V|` appears. -/
theorem card_mem_spectrum_GX_of_goldFree {X : ℕ}
    (h : GoldFree (owners X))
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    (Fintype.card (HireVertex (owners X)) : ℝ) ∈
      spectrum ℝ ((GX X).lapMatrix ℝ) := by
  classical
  rw [lapMatrix_eq_of_graph_eq (GX_eq_GXstar_of_goldFree h)]
  exact card_mem_spectrum_lapMatrix_GXstar X hn

/-! ### Spectral converse (Layer B footholds)

Paper money line: `λ₂(H) = 1` iff gold leaves are disconnected.

Layer B (proved): quadratic-form bump; star on three vertices plus the leaf edge
is `K₃`, so `1 ∉ spectrum` and the weak `HasSecondLaplacianEigenvalueOne` fails.
A single leaf chord on ≥3 leaves does **not** kill eigenvalue `1`.
-/

/-- Placeholder for “second Laplacian eigenvalue is `1`”.
Until ordered spectra / interlacing land: eigenvalue `1` present and connected. -/
def HasSecondLaplacianEigenvalueOne {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  (1 : ℝ) ∈ spectrum ℝ (H.lapMatrix ℝ) ∧ H.Connected

open Finset Matrix

private theorem sum_indicator_eq {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (c : ℝ) :
    (∑ i : V, ∑ j : V, if i = a ∧ j = b then c else 0) = c := by
  have hinner (i : V) :
      (∑ j : V, if i = a ∧ j = b then c else 0) = if i = a then c else 0 := by
    by_cases hi : i = a <;> simp [hi, sum_ite_eq']
  simp_rw [hinner, sum_ite_eq']
  simp [mem_univ]

/-- **Layer B foothold:** adjoining edge `a b` bumps the Laplacian quadratic form
by `(x a - x b)²`. -/
theorem lapMatrix_toLinearMap₂'_sup_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (hne : a ≠ b) (hnadj : ¬ G.Adj a b) (x : V → ℝ) :
    toLinearMap₂' ℝ ((G ⊔ SimpleGraph.edge a b).lapMatrix ℝ) x x =
      toLinearMap₂' ℝ (G.lapMatrix ℝ) x x + (x a - x b) ^ 2 := by
  classical
  -- Use the inferred `Sup.adjDecidable` instance (not `Classical.decRel`) so it
  -- matches the instance in the goal's `lapMatrix`.
  have hba : ¬ G.Adj b a := fun h => hnadj h.symm
  have hAdj (i j : V) :
      (G ⊔ SimpleGraph.edge a b).Adj i j ↔
        G.Adj i j ∨ i = a ∧ j = b ∨ i = b ∧ j = a := by
    constructor
    · intro h
      rcases (SimpleGraph.sup_adj G (SimpleGraph.edge a b) i j).mp h with hG | he
      · exact Or.inl hG
      · exact Or.inr ((SimpleGraph.edge_adj a b i j).mp he).1
    · intro h
      refine (SimpleGraph.sup_adj G (SimpleGraph.edge a b) i j).mpr ?_
      rcases h with hG | h | h
      · exact Or.inl hG
      · rw [h.1, h.2]
        exact Or.inr <| (SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
      · rw [h.1, h.2]
        exact Or.inr <| (SimpleGraph.edge_adj a b b a).mpr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩
  -- Pointwise: new edge contributes exactly the two orientations `{a,b}`.
  have hpt (i j : V) :
      (if (G ⊔ SimpleGraph.edge a b).Adj i j then (x i - x j) ^ 2 else 0) =
        (if G.Adj i j then (x i - x j) ^ 2 else 0) +
          (if i = a ∧ j = b then (x a - x b) ^ 2 else 0) +
            (if i = b ∧ j = a then (x b - x a) ^ 2 else 0) := by
    by_cases hG : G.Adj i j
    · have hsup : (G ⊔ SimpleGraph.edge a b).Adj i j :=
        (SimpleGraph.sup_adj G (SimpleGraph.edge a b) i j).mpr (Or.inl hG)
      -- Cannot be the new orientations: that would contradict hnadj/hba.
      have h1 : ¬ (i = a ∧ j = b) := fun hij => hnadj (by simpa [hij.1, hij.2] using hG)
      have h2 : ¬ (i = b ∧ j = a) := fun hij => hba (by simpa [hij.1, hij.2] using hG)
      simp [hsup, hG, h1, h2]
    · by_cases h1 : i = a ∧ j = b
      · have hsup : (G ⊔ SimpleGraph.edge a b).Adj i j :=
          (hAdj i j).mpr (Or.inr (Or.inl h1))
        have h2 : ¬ (i = b ∧ j = a) := fun h2 =>
          hne (h1.1.symm.trans h2.1)
        -- After knowing i=a, j=b, reduce ifs.
        cases h1 with
        | intro hi hj =>
          subst hi; subst hj
          simp [hsup, hG, hne]
      · by_cases h2 : i = b ∧ j = a
        · have hsup : (G ⊔ SimpleGraph.edge a b).Adj i j :=
            (hAdj i j).mpr (Or.inr (Or.inr h2))
          cases h2 with
          | intro hi hj =>
            subst hi; subst hj
            simp [hsup, hG, Ne.symm hne]
        · have hsup : ¬ (G ⊔ SimpleGraph.edge a b).Adj i j := by
            intro h
            rcases (hAdj i j).mp h with hG' | h' | h'
            · exact hG hG'
            · exact h1 h'
            · exact h2 h'
          simp [hsup, hG, h1, h2]
  have hsum :
      (∑ i : V, ∑ j : V,
          if (G ⊔ SimpleGraph.edge a b).Adj i j then (x i - x j) ^ 2 else 0) =
        (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) +
          2 * (x a - x b) ^ 2 := by
    simp_rw [hpt, sum_add_distrib]
    have h1 :
        (∑ i : V, ∑ j : V, if i = a ∧ j = b then (x a - x b) ^ 2 else 0) =
          (x a - x b) ^ 2 := sum_indicator_eq a b _
    have h2 :
        (∑ i : V, ∑ j : V, if i = b ∧ j = a then (x b - x a) ^ 2 else 0) =
          (x b - x a) ^ 2 := sum_indicator_eq b a _
    rw [h1, h2]; ring
  have hL := SimpleGraph.lapMatrix_toLinearMap₂' (G := G) (R := ℝ) x
  have hL' :=
    SimpleGraph.lapMatrix_toLinearMap₂' (G := G ⊔ SimpleGraph.edge a b) (R := ℝ) x
  rw [hL', hL, hsum]; ring

theorem one_not_mem_spectrum_lapMatrix_top
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hn : 2 ≤ Fintype.card V) :
    (1 : ℝ) ∉ spectrum ℝ ((⊤ : SimpleGraph V).lapMatrix ℝ) := by
  classical
  intro hmem
  rw [← Matrix.spectrum_toLin'] at hmem
  obtain ⟨x, hx⟩ :=
    (Module.End.HasEigenvalue.of_mem_spectrum hmem).exists_hasEigenvector
  have hx0 : x ≠ 0 := hx.2
  have h := hx.apply_eq_smul
  -- Avoid `simpa` unfolding `lapMatrix` underneath `toLin'`.
  replace h : Matrix.toLin' ((⊤ : SimpleGraph V).lapMatrix ℝ) x = x := by
    simpa [one_smul] using h
  rw [Matrix.toLin'_apply] at h
  set n := Fintype.card V
  have hcomp (v : V) : ((n : ℝ) - 1) * x v = ∑ u : V, x u := by
    have hv := congrFun h v
    have hnei : (⊤ : SimpleGraph V).neighborFinset v = univ.erase v := by
      ext u; simp [eq_comm]
    rw [SimpleGraph.lapMatrix_mulVec_apply', hnei, sum_sub_distrib] at hv
    have hc : ∑ _u ∈ univ.erase v, x v = ((n : ℝ) - 1) * x v := by
      simp [card_erase_of_mem (mem_univ v), nsmul_eq_mul, n,
        Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos)]
    have hxsum : ∑ u ∈ univ.erase v, x u = ∑ u : V, x u - x v :=
      sum_erase_eq_sub (mem_univ v)
    linarith
  obtain ⟨v0⟩ := ‹Nonempty V›
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set c := (∑ u : V, x u) / ((n : ℝ) - 1)
  have hc : ∀ v, x v = c := by
    intro v
    exact (eq_div_iff hn1).2 (by linarith [hcomp v])
  have hsum : ∑ u : V, x u = (n : ℝ) * c := by
    simp [hc, sum_const, nsmul_eq_mul, n]
  have hc0 : c = 0 := by
    have := hcomp v0
    simp [hc v0, hsum] at this
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℕ) < n := Fintype.card_pos
      exact_mod_cast this.ne'
    nlinarith
  exact hx0 (funext fun v => by simp [hc v, hc0])

private theorem card_triple_eq_three {V : Type*} [DecidableEq V]
    {r a b : V} (ha : a ≠ r) (hb : b ≠ r) (hab : a ≠ b) :
    ({r, a, b} : Finset V).card = 3 := by
  have hab' : a ∉ ({b} : Finset V) := by simpa [mem_singleton] using hab
  have hr : r ∉ ({a, b} : Finset V) := by
    intro h
    simp only [mem_insert, mem_singleton] at h
    exact h.elim (Ne.symm ha) (Ne.symm hb)
  rw [card_insert_of_notMem hr, card_insert_of_notMem hab', card_singleton]

/-- On three vertices, star plus the unique leaf edge is the complete graph. -/
theorem starGraph_sup_leaf_edge_eq_top_of_card_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {r a b : V} (ha : a ≠ r) (hb : b ≠ r) (hab : a ≠ b)
    (hcard : Fintype.card V = 3) :
    SimpleGraph.starGraph r ⊔ SimpleGraph.edge a b = ⊤ := by
  classical
  have univ_eq : (univ : Finset V) = {r, a, b} :=
    (eq_univ_of_card _ (by rw [card_triple_eq_three ha hb hab, hcard])).symm
  have mem_triple (x : V) : x = r ∨ x = a ∨ x = b := by
    have hx : x ∈ ({r, a, b} : Finset V) := by simp [← univ_eq]
    simpa [mem_insert, mem_singleton, or_assoc] using hx
  ext u v
  constructor
  · exact fun h => (SimpleGraph.top_adj u v).mpr h.ne
  · intro hadj
    have huv : u ≠ v := (SimpleGraph.top_adj u v).mp hadj
    refine (SimpleGraph.sup_adj _ _ u v).mpr ?_
    by_cases hu : u = r
    · -- u = r, so spoke to leaf v
      subst hu
      exact Or.inl (SimpleGraph.starGraph_center_adj huv)
    · by_cases hv : v = r
      · subst hv
        exact Or.inl (SimpleGraph.starGraph_center_adj' (Ne.symm huv))
      · -- both leaves: must be the pair {a,b}
        have hu' : u = a ∨ u = b := by
          rcases mem_triple u with h | h | h
          · exact (hu h).elim
          · exact Or.inl h
          · exact Or.inr h
        have hv' : v = a ∨ v = b := by
          rcases mem_triple v with h | h | h
          · exact (hv h).elim
          · exact Or.inl h
          · exact Or.inr h
        refine Or.inr ?_
        cases hu' with
        | inl hua =>
          cases hv' with
          | inl hva => exact (huv (hua.trans hva.symm)).elim
          | inr hvb =>
              rw [hua, hvb]
              exact (SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
        | inr hub =>
          cases hv' with
          | inl hva =>
              rw [hub, hva]
              exact (SimpleGraph.edge_adj a b b a).mpr ⟨Or.inr ⟨rfl, rfl⟩, hab.symm⟩
          | inr hvb => exact (huv (hub.trans hvb.symm)).elim

/-- **Layer B foothold (proved):** star on three vertices plus the leaf edge is
the triangle (`K₃`); Laplacian spectrum `{0,3}`, so the weak
`HasSecondLaplacianEigenvalueOne` fails.

Honesty: on ≥3 leaves a single leaf chord does **not** kill eigenvalue `1`. -/
theorem star_plus_leaf_edge_raises_second_eigenvalue
    {V : Type*} [Fintype V] [DecidableEq V]
    (r a b : V) (ha : a ≠ r) (hb : b ≠ r) (hab : a ≠ b)
    (hcard : Fintype.card V = 3)
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hstar : H = SimpleGraph.starGraph r)
    (H' : SimpleGraph V) [DecidableRel H'.Adj]
    (hedge : H' = H ⊔ SimpleGraph.edge a b) :
    ¬ HasSecondLaplacianEigenvalueOne H' := by
  classical
  intro hspec
  have htop : H' = ⊤ := by
    rw [hedge, hstar, starGraph_sup_leaf_edge_eq_top_of_card_three ha hb hab hcard]
  have : Nonempty V := ⟨r⟩
  have hn : 2 ≤ Fintype.card V := by omega
  -- Transport `1 ∈ spectrum` along the graph equality, then contradict.
  have hlap : H'.lapMatrix ℝ = (⊤ : SimpleGraph V).lapMatrix ℝ :=
    lapMatrix_eq_of_graph_eq htop
  have h1 : (1 : ℝ) ∈ spectrum ℝ ((⊤ : SimpleGraph V).lapMatrix ℝ) := by
    rw [← hlap]; exact hspec.1
  exact (one_not_mem_spectrum_lapMatrix_top hn) h1

/-- Gold chords never touch the seed `2`. -/
theorem ne_seed_of_GoldEdge {O : Set ℕ} {u v : HireVertex O} (h : GoldEdge O u v) :
    u ≠ seedVertex O ∧ v ≠ seedVertex O ∧ u ≠ v := by
  cases h with
  | inl hg =>
      refine ⟨?_, ?_, ?_⟩
      · intro hu; cases hu; exact hg.2.2.1 rfl
      · intro hv; cases hv; exact hg.2.2.2.1 rfl
      · intro huv; exact hg.2.2.2.2.2 (congrArg Subtype.val huv)
  | inr hg =>
      refine ⟨?_, ?_, ?_⟩
      · intro hu; cases hu; exact hg.2.2.2.1 rfl
      · intro hv; cases hv; exact hg.2.2.1 rfl
      · intro huv; exact hg.2.2.2.2.2 (congrArg Subtype.val huv).symm

theorem gold_adj_of_GoldEdge {O : Set ℕ} {u v : HireVertex O}
    (h : GoldEdge O u v) : (G O).Adj u v :=
  (G_adj_iff u v).mpr ⟨(ne_seed_of_GoldEdge h).2.2, Or.inl (Or.inr h)⟩

/-- On a three-vertex hire window, a gold leaf chord makes `GX` the star plus that edge. -/
theorem GX_eq_star_sup_edge_of_gold_card_three {X : ℕ}
    {u v : HireVertex (owners X)} (hg : GoldEdge (owners X) u v)
    (hcard : Fintype.card (HireVertex (owners X)) = 3) :
    GX X =
      SimpleGraph.starGraph (seedVertex (owners X)) ⊔ SimpleGraph.edge u v := by
  classical
  obtain ⟨hu, hv, huv⟩ := ne_seed_of_GoldEdge hg
  have hstar_top :=
    starGraph_sup_leaf_edge_eq_top_of_card_three hu hv huv hcard
  have univ_eq : (univ : Finset (HireVertex (owners X))) =
      {seedVertex (owners X), u, v} :=
    (eq_univ_of_card _ (by rw [card_triple_eq_three hu hv huv, hcard])).symm
  have mem_triple (x : HireVertex (owners X)) :
      x = seedVertex (owners X) ∨ x = u ∨ x = v := by
    have hx : x ∈ ({seedVertex (owners X), u, v} : Finset _) := by simp [← univ_eq]
    simpa [mem_insert, mem_singleton, or_assoc] using hx
  have hGXtop : GX X = ⊤ := by
    ext p q
    constructor
    · intro hadj; exact (SimpleGraph.top_adj p q).mpr hadj.ne
    · intro hadj
      have hpq : p ≠ q := (SimpleGraph.top_adj p q).mp hadj
      set seed := seedVertex (owners X)
      have leaf : ∀ x : HireVertex (owners X), x ≠ seed → x = u ∨ x = v := by
        intro x hx
        rcases mem_triple x with h | h | h
        · exact (hx h).elim
        · exact Or.inl h
        · exact Or.inr h
      by_cases hp : p = seed
      · subst hp
        exact star_adj_GX q (fun hval => hpq ((seedVertex_eq_iff _).mpr hval).symm)
      · by_cases hq : q = seed
        · subst hq
          exact (star_adj_GX p (fun hval => hp ((seedVertex_eq_iff _).mpr hval))).symm
        · rcases leaf p hp with hp' | hp' <;> rcases leaf q hq with hq' | hq'
          · exact (hpq (hp'.trans hq'.symm)).elim
          · rw [hp', hq']; exact gold_adj_of_GoldEdge hg
          · rw [hp', hq']; exact (gold_adj_of_GoldEdge hg).symm
          · exact (hpq (hp'.trans hq'.symm)).elim
  exact hGXtop.trans hstar_top.symm

/-- **Lemma 8 (⇒ combinatorial):** gold-free hire graph with ≥2 leaves is connected
and has Laplacian eigenvalue `1`. -/
theorem lemma8_forward {X : ℕ} (h : GoldFree (owners X))
    {a b : HireVertex (owners X)}
    (ha : a ≠ seedVertex (owners X)) (hb : b ≠ seedVertex (owners X))
    (hab : a ≠ b) :
    HasSecondLaplacianEigenvalueOne (GX X) := by
  classical
  refine ⟨one_mem_spectrum_GX_of_goldFree h ha hb hab, ?_⟩
  rw [GX_eq_GXstar_of_goldFree h]
  exact SimpleGraph.connected_starGraph (seedVertex (owners X))

/-- **Lemma 8 (⇐ spectral sketch at `GoldFree` strength):** gold leaf chord reduces
to the star-plus-edge setting.

* Three-vertex windows: discharged by `star_plus_leaf_edge_raises_second_eigenvalue`.
* Larger windows: one honest `sorry` — Mathlib gap is ordered `λ₂` /
  Courant–Fischer / Cauchy interlacing. Still undershoots Layer D. -/
theorem lemma8_converse_sketch {X : ℕ}
    (hspec : HasSecondLaplacianEigenvalueOne (GX X))
    (_hn : 3 ≤ Fintype.card (HireVertex (owners X))) :
    GoldFree (owners X) := by
  classical
  intro u v hg
  obtain ⟨hu, hv, huv⟩ := ne_seed_of_GoldEdge hg
  by_cases hcard : Fintype.card (HireVertex (owners X)) = 3
  · have hG := GX_eq_star_sup_edge_of_gold_card_three hg hcard
    exact (star_plus_leaf_edge_raises_second_eigenvalue
      (seedVertex (owners X)) u v hu hv huv hcard
      (SimpleGraph.starGraph (seedVertex (owners X))) rfl
      (GX X) hG) hspec
  · -- Mathlib gap: ordered λ₂ / Courant–Fischer / Cauchy interlacing.
    sorry

end Hire
