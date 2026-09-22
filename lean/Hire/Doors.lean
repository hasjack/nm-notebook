/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# The 3-free door of an odd prime

Elementary formalization of the χ₃ door package (hire graph).

* `chi3` — non-principal character mod 3 as `ℕ → ℤ`
* `m0 p` — unique **3-free** even neighbour for odd primes `p ≠ 3`
* `m1 p` — other face (divisible by 6)

Public voice: no ζ; doors and hire set only.
-/

namespace Hire

/-- Non-principal character mod 3: `+1` if `n ≡ 1 [MOD 3]`, `-1` if `n ≡ 2`, else `0`. -/
def chi3 (n : ℕ) : ℤ :=
  match n % 3 with
  | 1 => 1
  | 2 => -1
  | _ => 0

@[simp] lemma chi3_of_mod_one {n : ℕ} (h : n % 3 = 1) : chi3 n = 1 := by simp [chi3, h]
@[simp] lemma chi3_of_mod_two {n : ℕ} (h : n % 3 = 2) : chi3 n = -1 := by simp [chi3, h]
@[simp] lemma chi3_of_mod_zero {n : ℕ} (h : n % 3 = 0) : chi3 n = 0 := by simp [chi3, h]

lemma chi3_eq_zero_iff_dvd_three (n : ℕ) : chi3 n = 0 ↔ 3 ∣ n := by
  constructor
  · intro h
    rw [Nat.dvd_iff_mod_eq_zero]
    have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
    match hmod : n % 3 with
    | 0 => rfl
    | 1 => simp [chi3, hmod] at h
    | 2 => simp [chi3, hmod] at h
    | k + 3 =>
        have : n % 3 < 3 := hlt
        omega
  · intro h
    have : n % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    simp [chi3, this]

/-- 3-free door. For odd primes `p ≠ 3` this equals `p ± 1`. -/
def m0 (p : ℕ) : ℕ := if p % 3 = 1 then p + 1 else p - 1

/-- Other face. For odd primes `p ≠ 3` this is divisible by 6. -/
def m1 (p : ℕ) : ℕ := if p % 3 = 1 then p - 1 else p + 1

lemma m0_of_mod_one {p : ℕ} (h : p % 3 = 1) : m0 p = p + 1 := by simp [m0, h]
lemma m0_of_mod_two {p : ℕ} (h : p % 3 = 2) : m0 p = p - 1 := by simp [m0, h]
lemma m1_of_mod_one {p : ℕ} (h : p % 3 = 1) : m1 p = p - 1 := by simp [m1, h]
lemma m1_of_mod_two {p : ℕ} (h : p % 3 = 2) : m1 p = p + 1 := by simp [m1, h]

lemma not_three_dvd_of_prime_ne_three {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) : ¬ 3 ∣ p := by
  intro hd
  rcases hp.eq_one_or_self_of_dvd 3 hd with h | h
  · exact absurd h (by decide)
  · exact h3 h.symm

lemma prime_ne_three_mod_eq_one_or_two {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have hne : ¬ 3 ∣ p := not_three_dvd_of_prime_ne_three hp h3
  have hmod0 : p % 3 ≠ 0 := fun h0 => hne (Nat.dvd_iff_mod_eq_zero.mpr h0)
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  match h : p % 3 with
  | 0 => exact absurd h hmod0
  | 1 => exact Or.inl rfl
  | 2 => exact Or.inr rfl
  | k + 3 => omega

/-- **3-free:** if `p` is prime and `p ≠ 3`, then `3 ∤ m0 p`. -/
theorem three_not_dvd_m0 {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) : ¬ 3 ∣ m0 p := by
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with h | h
  · rw [m0_of_mod_one h, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h]
    decide
  · have : 2 ≤ p := hp.two_le
    rw [m0_of_mod_two h, Nat.dvd_iff_mod_eq_zero]
    have : (p - 1) % 3 = 1 := by omega
    simp [this]

/-- Odd prime `p ≠ 3` ⇒ `m0 p` is even. -/
theorem even_m0 {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) : Even (m0 p) := by
  rw [even_iff_two_dvd]
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with h | h
  · rw [m0_of_mod_one h]
    exact Nat.dvd_of_mod_eq_zero (by
      have := Nat.odd_iff.mp hodd
      omega)
  · rw [m0_of_mod_two h]
    have : 1 ≤ p := Nat.le_of_lt hp.one_lt
    exact Nat.dvd_of_mod_eq_zero (by
      have := Nat.odd_iff.mp hodd
      omega)

/-- Other face divisible by 3. -/
theorem three_dvd_m1 {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) : 3 ∣ m1 p := by
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with h | h
  · have hp2 : 2 ≤ p := hp.two_le
    simp [m1, h, Nat.dvd_iff_mod_eq_zero]
    omega
  · simp [m1, h, Nat.dvd_iff_mod_eq_zero, Nat.add_mod]

theorem even_m1 {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) : Even (m1 p) := by
  rw [even_iff_two_dvd]
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with h | h
  · have : 1 ≤ p := Nat.le_of_lt hp.one_lt
    rw [m1_of_mod_one h]
    exact Nat.dvd_of_mod_eq_zero (by
      have := Nat.odd_iff.mp hodd
      omega)
  · rw [m1_of_mod_two h]
    exact Nat.dvd_of_mod_eq_zero (by
      have := Nat.odd_iff.mp hodd
      omega)

/-- Other face divisible by 6. -/
theorem six_dvd_m1 {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) : 6 ∣ m1 p := by
  have h2 : 2 ∣ m1 p := even_iff_two_dvd.mp (even_m1 hp hodd h3)
  have h3d : 3 ∣ m1 p := three_dvd_m1 hp h3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) h2 h3d

/-- Poster checks after Lemma 1. -/
example : m0 11 = 10 := by native_decide
example : m0 13 = 14 := by native_decide
example : m1 11 = 12 := by native_decide
example : m1 13 = 12 := by native_decide
example : chi3 11 = -1 := by native_decide
example : chi3 13 = 1 := by native_decide

end Hire
