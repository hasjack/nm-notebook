/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.StarLap
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

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
* converse spectral rigidity at zero-gold left as a documented `sorry`
  pending edge-monotonicity / Cauchy interlacing for Laplacians.

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

/-! ### Spectral converse (sketch)

Paper money line: `λ₂(H) = 1` iff gold leaves are disconnected.

Layer B foothold: converse at `GoldFree` strength (zero gold). Mathlib currently
exposes PSD Laplacians and the star spectrum helpers above, but not a packaged
“adding an edge strictly raises `λ₂` above `1`” lemma for stars. We keep the
statement and mark the body `sorry` so the interface is stable.
-/

/-- Placeholder for “second Laplacian eigenvalue is `1`”.
Until ordered spectra / interlacing land, we use: eigenvalue `1` present and connected. -/
def HasSecondLaplacianEigenvalueOne {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  (1 : ℝ) ∈ spectrum ℝ (H.lapMatrix ℝ) ∧ H.Connected

/-- **Lemma 8 (⇒ combinatorial):** gold-free hire graph with ≥2 leaves is connected
and has Laplacian eigenvalue `1`. -/
theorem lemma8_forward {X : ℕ} (h : GoldFree (owners X))
    {a b : HireVertex (owners X)}
    (ha : a ≠ seedVertex (owners X)) (hb : b ≠ seedVertex (owners X))
    (hab : a ≠ b) :
    HasSecondLaplacianEigenvalueOne (GX X) := by
  classical
  refine ⟨one_mem_spectrum_GX_of_goldFree h ha hb hab, ?_⟩
  have heq := GX_eq_GXstar_of_goldFree h
  rw [heq]
  exact SimpleGraph.connected_starGraph (seedVertex (owners X))

/-- **Lemma 8 (⇐ spectral sketch at `GoldFree` strength):** if the hire graph has
second eigenvalue `1` in the strong sense of the paper, then there is no gold chord.

Body deferred: needs Laplacian edge-monotonicity / interlacing relative to the star.
Filling this `sorry` still undershoots `GoldLeavesDisconnected` (forests). -/
theorem lemma8_converse_sketch {X : ℕ}
    (_hspec : HasSecondLaplacianEigenvalueOne (GX X))
    (_hn : 3 ≤ Fintype.card (HireVertex (owners X))) :
    GoldFree (owners X) := by
  -- Adding any gold chord among leaves raises λ₂ strictly above 1 for the star
  -- (Cauchy interlacing / edge monotonicity). Not yet in this Mathlib slice.
  sorry

end Hire
