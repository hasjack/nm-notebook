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

end Hire
