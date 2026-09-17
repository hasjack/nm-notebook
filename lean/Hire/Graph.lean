/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.HireSet
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Finite hire graph `G_X`

Vertices are numbers `Hired` relative to an owner set (window `owners X`).
Edges are the undirected **star on 2** together with **gold chords** (symmetric
closure of `GoldArc`).

Uses Mathlib `SimpleGraph` via `fromRel` so Adj is automatically symmetric and
irreflexive. Public voice: doors, hire set, gold edges; finite windows keep
spectra on finite graphs.
-/

namespace Hire

/-- Vertex type: hired numbers relative to owner set `O`. -/
abbrev HireVertex (O : Set ℕ) : Type :=
  {q // Hired O q}

/-- Seed vertex `2`. -/
def seedVertex (O : Set ℕ) : HireVertex O :=
  ⟨2, Hired.seed⟩

/-- Star incidence: one endpoint is the seed `2`. -/
def StarEdge (O : Set ℕ) (u v : HireVertex O) : Prop :=
  u.val = 2 ∨ v.val = 2

/-- Undirected gold chord: either direction of `GoldArc`. -/
def GoldEdge (O : Set ℕ) (u v : HireVertex O) : Prop :=
  GoldArc O u.val v.val ∨ GoldArc O v.val u.val

/-- Raw hire relation (star or gold); `fromRel` adds symmetry + looplessness. -/
def hireRel (O : Set ℕ) (u v : HireVertex O) : Prop :=
  StarEdge O u v ∨ GoldEdge O u v

/-- Hire graph on an arbitrary owner set. -/
def G (O : Set ℕ) : SimpleGraph (HireVertex O) :=
  SimpleGraph.fromRel (hireRel O)

/-- Finite window hire graph `G_X`. -/
def GX (X : ℕ) : SimpleGraph (HireVertex (owners X)) :=
  G (owners X)

/-- `3` is never a vertex (because it is never hired). -/
theorem hireVertex_ne_three {O : Set ℕ} (v : HireVertex O) : v.val ≠ 3 :=
  hired_ne_three v.property

theorem GX_vertex_ne_three {X : ℕ} (v : HireVertex (owners X)) : v.val ≠ 3 :=
  hireVertex_ne_three v

@[simp] theorem G_adj_iff {O : Set ℕ} (u v : HireVertex O) :
    (G O).Adj u v ↔ u ≠ v ∧ (hireRel O u v ∨ hireRel O v u) :=
  SimpleGraph.fromRel_adj _ _ _

@[simp] theorem GX_adj_iff {X : ℕ} (u v : HireVertex (owners X)) :
    (GX X).Adj u v ↔ u ≠ v ∧ (hireRel (owners X) u v ∨ hireRel (owners X) v u) :=
  G_adj_iff u v

/-- Star edge: seed adjacent to every other hired vertex. -/
theorem star_adj {O : Set ℕ} (v : HireVertex O) (hv : v.val ≠ 2) :
    (G O).Adj (seedVertex O) v := by
  refine (G_adj_iff _ _).mpr ⟨?_, Or.inl (Or.inl (Or.inl rfl))⟩
  intro h
  exact hv (by simpa [seedVertex] using (congrArg Subtype.val h).symm)

theorem star_adj_GX {X : ℕ} (v : HireVertex (owners X)) (hv : v.val ≠ 2) :
    (GX X).Adj (seedVertex (owners X)) v :=
  star_adj v hv

/-- Gold chord lifts a directed `GoldArc` to an undirected Adj. -/
theorem gold_adj_of_GoldArc {O : Set ℕ} {p q : ℕ}
    (hp : Hired O p) (hq : Hired O q) (h : GoldArc O p q) :
    (G O).Adj ⟨p, hp⟩ ⟨q, hq⟩ := by
  have hne : p ≠ q := h.2.2.2.2.2
  refine (G_adj_iff _ _).mpr ⟨?_, Or.inl (Or.inr (Or.inl h))⟩
  intro heq
  exact hne (by simpa using congrArg Subtype.val heq)

/-- Tiny window sanity: seed is a vertex for every `X`. -/
example (X : ℕ) : (seedVertex (owners X) : HireVertex (owners X)).val = 2 := rfl

end Hire
