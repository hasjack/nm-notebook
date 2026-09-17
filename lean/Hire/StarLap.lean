/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Finite
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Pure star Laplacian (Lemma 7 style)

On a finite vertex set the Mathlib `starGraph` centered at the hire seed has
Laplacian eigenvalue equal to the number of vertices (`λ_max = n` for `n ≥ 2`).
Also `1` is an eigenvalue when there are two distinct leaves.

Public voice: star on 2; gold chords deferred to `Lemma8`.
-/

open Finset Matrix Module

namespace Hire

/-- Pure star on hired vertices: center = seed `2`. -/
def Gstar (O : Set ℕ) : SimpleGraph (HireVertex O) :=
  SimpleGraph.starGraph (seedVertex O)

/-- Window pure star. -/
def GXstar (X : ℕ) : SimpleGraph (HireVertex (owners X)) :=
  Gstar (owners X)

noncomputable instance (X : ℕ) : DecidableRel (GXstar X).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.starGraph (seedVertex (owners X))).Adj)

instance (O : Set ℕ) : Nonempty (HireVertex O) := ⟨seedVertex O⟩

theorem seedVertex_eq_iff {O : Set ℕ} (v : HireVertex O) :
    v = seedVertex O ↔ v.val = 2 := by
  constructor
  · rintro rfl; rfl
  · intro h
    exact Subtype.ext (by simpa [seedVertex] using h)

lemma neighborFinset_starGraph_center {V : Type*} [Fintype V] [DecidableEq V] (r : V) :
    (SimpleGraph.starGraph r).neighborFinset r = univ.erase r := by
  ext u
  simp [SimpleGraph.mem_neighborFinset, SimpleGraph.starGraph_adj, eq_comm]

lemma neighborFinset_starGraph_leaf {V : Type*} [Fintype V] [DecidableEq V]
    {r v : V} (hv : v ≠ r) :
    (SimpleGraph.starGraph r).neighborFinset v = {r} := by
  ext u
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.starGraph_adj, mem_singleton]
  constructor
  · rintro ⟨_, h | h⟩
    · exact (hv h).elim
    · exact h
  · rintro rfl
    exact ⟨hv, Or.inr rfl⟩

/-- Test vector for eigenvalue `n`: `n-1` at the center, `-1` on leaves. -/
def starMaxEigenvec {V : Type*} [DecidableEq V] (r : V) (n : ℕ) : V → ℝ :=
  fun v => if v = r then (n : ℝ) - 1 else (-1 : ℝ)

lemma sum_starMaxEigenvec {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (r : V) :
    ∑ u : V, starMaxEigenvec r (Fintype.card V) u = 0 := by
  classical
  set n := Fintype.card V
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hpos : ∑ u ∈ filter (· = r) univ, starMaxEigenvec r n u = (n : ℝ) - 1 := by
    simp [starMaxEigenvec, filter_eq', n]
  have hneg : ∑ u ∈ filter (· ≠ r) univ, starMaxEigenvec r n u = -((n : ℝ) - 1) := by
    have hset : filter (· ≠ r) univ = univ.erase r := by
      ext; simp [mem_erase]
    rw [hset]
    have hx : ∀ u ∈ univ.erase r, starMaxEigenvec r n u = (-1 : ℝ) := by
      intro u hu
      have : u ≠ r := (mem_erase.mp hu).1
      simp [starMaxEigenvec, this]
    rw [sum_congr rfl hx, sum_const, card_erase_of_mem (mem_univ r)]
    simp [nsmul_eq_mul, Nat.cast_sub hn1, n]
  have hsplit := (sum_filter_add_sum_filter_not univ (· = r) (starMaxEigenvec r n)).symm
  calc ∑ u : V, starMaxEigenvec r n u
      = ∑ u ∈ filter (· = r) univ, starMaxEigenvec r n u +
          ∑ u ∈ filter (· ≠ r) univ, starMaxEigenvec r n u := hsplit
    _ = (n : ℝ) - 1 + -((n : ℝ) - 1) := by rw [hpos, hneg]
    _ = 0 := by ring

lemma starMaxEigenvec_ne_zero {V : Type*} [DecidableEq V] (r : V) {n : ℕ}
    (hn : 2 ≤ n) : starMaxEigenvec (V := V) r n ≠ 0 := by
  intro h
  have hr : starMaxEigenvec r n r = 0 := congrFun h r
  simp only [starMaxEigenvec, ↓reduceIte] at hr
  have hn1 : (n : ℝ) = 1 := by linarith
  have : n = 1 := by exact_mod_cast hn1
  omega

/-- Laplacian action of the star on the max-eigenvalue test vector. -/
theorem lapMatrix_mulVec_starMaxEigenvec
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (r : V) :
    (SimpleGraph.starGraph r).lapMatrix ℝ *ᵥ starMaxEigenvec r (Fintype.card V) =
      (Fintype.card V : ℝ) • starMaxEigenvec r (Fintype.card V) := by
  classical
  set n := Fintype.card V
  have hn1 : 1 ≤ n := Fintype.card_pos
  ext v
  by_cases hv : v = r
  · rw [hv, SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.degree_starGraph_center,
      neighborFinset_starGraph_center]
    have hsum : ∑ u ∈ univ.erase r, starMaxEigenvec r n u = -((n : ℝ) - 1) := by
      have htot := sum_starMaxEigenvec (V := V) r
      have hsub := sum_erase_eq_sub (a := r) (f := starMaxEigenvec r n) (mem_univ r)
      have hr : starMaxEigenvec r n r = (n : ℝ) - 1 := by simp [starMaxEigenvec]
      linarith
    rw [hsum]
    simp only [starMaxEigenvec, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
    rw [Nat.cast_sub hn1]
    ring
  · rw [SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.degree_starGraph_of_ne_center hv,
      neighborFinset_starGraph_leaf hv]
    simp only [starMaxEigenvec, hv, ↓reduceIte, Pi.smul_apply, smul_eq_mul, sum_singleton]
    ring

/-- **Lemma 7 style:** Laplacian of `starGraph r` on `n ≥ 2` vertices has eigenvalue `n`. -/
theorem card_mem_spectrum_lapMatrix_starGraph
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (r : V)
    (hn : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ∈ spectrum ℝ ((SimpleGraph.starGraph r).lapMatrix ℝ) := by
  classical
  set n := Fintype.card V
  set vec := starMaxEigenvec r n
  have hx : vec ≠ 0 := starMaxEigenvec_ne_zero r hn
  have hmul := lapMatrix_mulVec_starMaxEigenvec (V := V) r
  rw [← Matrix.spectrum_toLin']
  refine Module.End.HasEigenvalue.mem_spectrum ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := vec) ⟨?_, hx⟩
  exact Module.End.mem_genEigenspace_one.mpr (by simpa [Matrix.toLin'_apply, vec, n] using hmul)

/-- Window specialization: `GXstar` has Laplacian eigenvalue `|V|` when `|V| ≥ 2`. -/
theorem card_mem_spectrum_lapMatrix_GXstar (X : ℕ)
    (hn : 2 ≤ Fintype.card (HireVertex (owners X))) :
    (Fintype.card (HireVertex (owners X)) : ℝ) ∈
      spectrum ℝ ((GXstar X).lapMatrix ℝ) :=
  card_mem_spectrum_lapMatrix_starGraph (seedVertex (owners X)) hn

/-- Test vector for eigenvalue `1`: opposite signs on two distinct leaves. -/
def starOneEigenvec {V : Type*} [DecidableEq V] (a b : V) : V → ℝ :=
  fun v => if v = a then (1 : ℝ) else if v = b then (-1 : ℝ) else 0

lemma starOneEigenvec_ne_zero {V : Type*} [DecidableEq V] {a b : V} :
    starOneEigenvec a b ≠ 0 := by
  intro h
  have : (1 : ℝ) = 0 := by
    have := congrFun h a
    simp [starOneEigenvec] at this
  exact absurd this (by norm_num)

lemma starOneEigenvec_eq_indicators {V : Type*} [DecidableEq V]
    {a b : V} (hab : a ≠ b) :
    starOneEigenvec a b =
      (fun v => if v = a then (1 : ℝ) else 0) +
        (fun v => if v = b then (-1 : ℝ) else 0) := by
  ext v
  simp only [starOneEigenvec, Pi.add_apply]
  by_cases h1 : v = a
  · simp [h1, hab]
  · by_cases h2 : v = b
    · simp [h2, Ne.symm hab]
    · simp [h1, h2]

lemma sum_starOneEigenvec {V : Type*} [Fintype V] [DecidableEq V]
    {a b : V} (hab : a ≠ b) :
    ∑ u : V, starOneEigenvec a b u = 0 := by
  classical
  rw [starOneEigenvec_eq_indicators hab]
  simp only [Pi.add_apply]
  rw [sum_add_distrib]
  simp

/-- If `a,b` are distinct leaves, the sign vector is a `1`-eigenvector. -/
theorem lapMatrix_mulVec_starOneEigenvec
    {V : Type*} [Fintype V] [DecidableEq V] {r a b : V}
    (ha : a ≠ r) (hb : b ≠ r) (hab : a ≠ b) :
    (SimpleGraph.starGraph r).lapMatrix ℝ *ᵥ starOneEigenvec a b =
      (1 : ℝ) • starOneEigenvec a b := by
  classical
  ext v
  by_cases hv : v = r
  · rw [hv, SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.degree_starGraph_center,
      neighborFinset_starGraph_center]
    have hsum : ∑ u ∈ univ.erase r, starOneEigenvec a b u = 0 := by
      have htot := sum_starOneEigenvec (V := V) hab
      have hsub := sum_erase_eq_sub (a := r) (f := starOneEigenvec a b) (mem_univ r)
      have hr0 : starOneEigenvec a b r = 0 := by simp [starOneEigenvec, Ne.symm ha, Ne.symm hb]
      linarith
    have hr0 : starOneEigenvec a b r = 0 := by simp [starOneEigenvec, Ne.symm ha, Ne.symm hb]
    simp [hsum, hr0, Pi.smul_apply]
  · by_cases hva : v = a
    · rw [hva, SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.degree_starGraph_of_ne_center ha,
        neighborFinset_starGraph_leaf ha]
      simp [starOneEigenvec, Pi.smul_apply, Ne.symm ha, Ne.symm hb]
    · by_cases hvb : v = b
      · rw [hvb, SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.degree_starGraph_of_ne_center hb,
          neighborFinset_starGraph_leaf hb]
        simp [starOneEigenvec, Pi.smul_apply, Ne.symm ha, Ne.symm hb, Ne.symm hab]
      · rw [SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.degree_starGraph_of_ne_center hv,
          neighborFinset_starGraph_leaf hv]
        have hv0 : starOneEigenvec a b v = 0 := by simp [starOneEigenvec, hva, hvb]
        have hr0 : starOneEigenvec a b r = 0 := by simp [starOneEigenvec, Ne.symm ha, Ne.symm hb]
        simp [hv0, hr0, Pi.smul_apply]

/-- **Lemma 7 style (secondary):** `1` is a Laplacian eigenvalue when two distinct leaves exist. -/
theorem one_mem_spectrum_lapMatrix_starGraph_of_two_leaves
    {V : Type*} [Fintype V] [DecidableEq V] (r a b : V)
    (ha : a ≠ r) (hb : b ≠ r) (hab : a ≠ b) :
    (1 : ℝ) ∈ spectrum ℝ ((SimpleGraph.starGraph r).lapMatrix ℝ) := by
  classical
  set vec := starOneEigenvec a b
  have hx : vec ≠ 0 := starOneEigenvec_ne_zero (a := a) (b := b)
  have hmul := lapMatrix_mulVec_starOneEigenvec ha hb hab
  rw [← Matrix.spectrum_toLin']
  refine Module.End.HasEigenvalue.mem_spectrum ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := vec) ⟨?_, hx⟩
  exact Module.End.mem_genEigenspace_one.mpr (by simpa [Matrix.toLin'_apply, vec] using hmul)

end Hire
