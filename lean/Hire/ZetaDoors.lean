/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Doors

/-!
# Zeta-door arithmetic (lab)

Not the hire-graph barrel. The exact modular connection used on `/zeta-doors`:

If `k ≡ 2 [MOD 12]` and `p > 3` is prime with `p - 1 ∣ k`, then `p ≡ 11 [MOD 12]`
and the 3-free door is `m0 p = p - 1`, so the door divides the index.

That is the selection rule for extra Bernoulli-denominator primes. It is not
gold (`q ∣ m0 p`). Von Staudt–Clausen itself is Mathlib's `Bernoulli.vonStaudt_clausen`.
-/

namespace Hire

theorem m0_eq_pred_iff {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    m0 p = p - 1 ↔ p % 3 = 2 := by
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with h | h
  · simp [m0_of_mod_one h, h]
    have : 2 ≤ p := hp.two_le
    omega
  · simp [m0_of_mod_two h, h]

/-- `k ≡ 2 [MOD 12]` is even but not divisible by 4 or by 3. -/
lemma two_dvd_of_mod_twelve {k : ℕ} (hk : k % 12 = 2) : 2 ∣ k := by
  omega

lemma not_four_dvd_of_mod_twelve {k : ℕ} (hk : k % 12 = 2) : ¬ 4 ∣ k := by
  omega

lemma not_three_dvd_of_mod_twelve {k : ℕ} (hk : k % 12 = 2) : ¬ 3 ∣ k := by
  omega

/-- If `p - 1` divides an index `k ≡ 2 [MOD 12]` and `p` is prime `> 3`,
then `p ≡ 11 [MOD 12]`. -/
theorem prime_mod_twelve_of_pred_dvd_index {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hk : k % 12 = 2) (hdvd : p - 1 ∣ k) :
    p % 12 = 11 := by
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := by
      intro h; subst h; exact (by decide : ¬ Nat.Prime 4) hp
    omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpred : 1 ≤ p := Nat.le_of_lt hp.one_lt
  have h4 : ¬ 4 ∣ p - 1 := by
    intro h
    exact not_four_dvd_of_mod_twelve hk (Nat.dvd_trans h hdvd)
  have hpmod4 : p % 4 = 3 := by
    have := Nat.odd_iff.mp hodd
    have : (p - 1) % 4 ≠ 0 := fun h => h4 (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  have h3pred : ¬ 3 ∣ p - 1 := by
    intro h
    exact not_three_dvd_of_mod_twelve hk (Nat.dvd_trans h hdvd)
  have hpmod3 : p % 3 = 2 := by
    have hne0 : p % 3 ≠ 0 := by
      intro h
      exact not_three_dvd_of_prime_ne_three hp hp3 (Nat.dvd_iff_mod_eq_zero.mpr h)
    have hne1 : p % 3 ≠ 1 := by
      intro h
      have : (p - 1) % 3 = 0 := by omega
      exact h3pred (Nat.dvd_iff_mod_eq_zero.mpr this)
    have : p % 3 < 3 := Nat.mod_lt p (by decide)
    interval_cases p % 3 <;> omega
  omega

/-- The 3-free door divides the index. -/
theorem m0_dvd_of_pred_dvd_index {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hk : k % 12 = 2) (hdvd : p - 1 ∣ k) :
    m0 p ∣ k := by
  have h12 := prime_mod_twelve_of_pred_dvd_index hp hp2 hp3 hk hdvd
  have : p % 3 = 2 := by omega
  rw [m0_of_mod_two this]
  exact hdvd

/-- Even k not divisible by 3 is 2, 4, 8, or 10 (mod 12). -/
lemma even_not_three_mod_twelve {k : ℕ} (h2 : 2 ∣ k) (h3 : ¬ 3 ∣ k) :
    k % 12 = 2 ∨ k % 12 = 4 ∨ k % 12 = 8 ∨ k % 12 = 10 := by
  have h2m : k % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
  have h3m : k % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have h12_2 : (k % 12) % 2 = k % 2 := Nat.mod_mod_of_dvd k (by decide : 2 ∣ 12)
  have h12_3 : (k % 12) % 3 = k % 3 := Nat.mod_mod_of_dvd k (by decide : 3 ∣ 12)
  have : k % 12 < 12 := Nat.mod_lt k (by decide)
  interval_cases k % 12 <;> omega

/-- Removing the unique factor of 3 from the denominator still leaves a 3-free
even door when `3 ∤ k`. Extra primes then satisfy `p ≡ 2 (mod 3)`. -/
theorem prime_mod_three_of_pred_dvd_even {p k : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3)
    (_h2 : 2 ∣ k) (h3 : ¬ 3 ∣ k) (hdvd : p - 1 ∣ k) :
    p % 3 = 2 := by
  have h3pred : ¬ 3 ∣ p - 1 := fun h => h3 (Nat.dvd_trans h hdvd)
  have hne0 : p % 3 ≠ 0 := by
    intro h
    exact not_three_dvd_of_prime_ne_three hp hp3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hne1 : p % 3 ≠ 1 := by
    intro h
    have : (p - 1) % 3 = 0 := by omega
    exact h3pred (Nat.dvd_iff_mod_eq_zero.mpr this)
  have : p % 3 < 3 := Nat.mod_lt p (by decide)
  interval_cases p % 3 <;> omega

theorem m0_dvd_of_pred_dvd_even {p k : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3)
    (h2 : 2 ∣ k) (h3 : ¬ 3 ∣ k) (hdvd : p - 1 ∣ k) :
    m0 p ∣ k := by
  have : p % 3 = 2 := prime_mod_three_of_pred_dvd_even hp hp3 h2 h3 hdvd
  rw [m0_of_mod_two this]
  exact hdvd

/-- If also `4 ∤ k` (so k ≡ 2 or 10 (mod 12)), the extra primes are 11 (mod 12). -/
theorem prime_mod_twelve_of_pred_dvd_not_four {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h2 : 2 ∣ k) (h3 : ¬ 3 ∣ k) (h4 : ¬ 4 ∣ k)
    (hdvd : p - 1 ∣ k) :
    p % 12 = 11 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h4pred : ¬ 4 ∣ p - 1 := fun h => h4 (Nat.dvd_trans h hdvd)
  have hpmod4 : p % 4 = 3 := by
    have := Nat.odd_iff.mp hodd
    have : (p - 1) % 4 ≠ 0 := fun h => h4pred (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  have hpmod3 : p % 3 = 2 := prime_mod_three_of_pred_dvd_even hp hp3 h2 h3 hdvd
  omega

/-- If `4 ∣ k`, extra primes may be 5 or 11 (mod 12). -/
theorem prime_mod_twelve_of_pred_dvd_four {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h2 : 2 ∣ k) (h3 : ¬ 3 ∣ k)
    (hdvd : p - 1 ∣ k) :
    p % 12 = 5 ∨ p % 12 = 11 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpmod3 : p % 3 = 2 := prime_mod_three_of_pred_dvd_even hp hp3 h2 h3 hdvd
  have hpmod2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have h12_2 : (p % 12) % 2 = p % 2 := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 12)
  have h12_3 : (p % 12) % 3 = p % 3 := Nat.mod_mod_of_dvd p (by decide : 3 ∣ 12)
  have : p % 12 < 12 := Nat.mod_lt p (by decide)
  interval_cases p % 12 <;> omega

end Hire
