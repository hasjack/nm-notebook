/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Doors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Hire set `S` (relative to a finite owner window)

Owners are odd primes in `[5, X]`. The hire set seeds `2` and closes under
odd prime factors `≠ 3` of `m0 p` for owners `p`.

This matches the paper's finite `G_X` / `S_X` framing so spectra stay on finite graphs.
`3` never enters `S`.
-/

namespace Hire

/-- Owners for window `X`: odd primes `p` with `5 ≤ p ≤ X`. -/
def owners (X : ℕ) : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ p ≠ 3 ∧ p ≤ X ∧ 5 ≤ p}

/-- Hire predicate relative to an owner set: seed `2`, then factors of doors. -/
inductive Hired (O : Set ℕ) : ℕ → Prop where
  | seed : Hired O 2
  | ofDoor {p q : ℕ} (hp : p ∈ O) (hq : q.Prime) (hne : q ≠ 3) (hd : q ∣ m0 p) :
      Hired O q

/-- Convenience: hired in window `X`. -/
def hiredIn (X : ℕ) (q : ℕ) : Prop := Hired (owners X) q

/-- **3 never enters `S`.** -/
theorem not_hired_three (O : Set ℕ) : ¬ Hired O 3 := by
  intro h
  cases h with
  | @ofDoor p q hp hq hne hd => exact hne rfl

theorem not_hired_three_in (X : ℕ) : ¬ hiredIn X 3 :=
  not_hired_three _

theorem hired_ne_three {O : Set ℕ} {q : ℕ} (h : Hired O q) : q ≠ 3 := by
  rintro rfl
  exact not_hired_three O h

/-- Gold arc (directed): `p → q` when `q ∣ m0 p`, both hired leaves. -/
def GoldArc (O : Set ℕ) (p q : ℕ) : Prop :=
  Hired O p ∧ Hired O q ∧ p ≠ 2 ∧ q ≠ 2 ∧ q ∣ m0 p ∧ p ≠ q

/-- Asymmetry example from the notes: `5 ∣ m0 11` but not `11 ∣ m0 5`. -/
example : 5 ∣ m0 11 := by native_decide
example : ¬ 11 ∣ m0 5 := by native_decide

/-! ### Bounds useful for finiteness of windows -/

lemma m0_le_succ (p : ℕ) : m0 p ≤ p + 1 := by
  unfold m0
  split_ifs <;> omega

lemma m0_pos_of_owners_mem {X p : ℕ} (hp : p ∈ owners X) : 0 < m0 p := by
  have hp5 : 5 ≤ p := hp.2.2.2.2
  have : 1 ≤ p := by omega
  unfold m0
  split_ifs <;> omega

/-- Any hired number in window `X` is at most `max 2 (X + 1)`. -/
theorem hired_le_max {X q : ℕ} (h : Hired (owners X) q) : q ≤ max 2 (X + 1) := by
  cases h with
  | seed => exact le_max_left _ _
  | @ofDoor p q hp hq hne hd =>
      have hpX : p ≤ X := hp.2.2.2.1
      have hpos : 0 < m0 p := m0_pos_of_owners_mem hp
      have hq_le : q ≤ m0 p := Nat.le_of_dvd hpos hd
      have : m0 p ≤ p + 1 := m0_le_succ p
      have : q ≤ X + 1 := by omega
      exact le_trans this (le_max_right _ _)

theorem owners_finite (X : ℕ) : (owners X).Finite :=
  (Set.finite_le_nat X).subset fun _p hp => hp.2.2.2.1

theorem hired_set_finite (X : ℕ) : {q | Hired (owners X) q}.Finite :=
  (Set.finite_le_nat (max 2 (X + 1))).subset fun _q hq => hired_le_max hq

end Hire
