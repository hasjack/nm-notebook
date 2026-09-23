/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett

Exploratory lab note (infinite owners hiring a fixed odd ingredient).
Not part of the Hire.lean import barrel. Public voice: no ζ; doors and hire
classes only. Papers frozen.
-/
import Hire.TwoClassCoverage
import Hire.Dirichlet
import Mathlib.Order.Interval.Finset.Basic

/-!
# Infinitely many primes hire a fixed odd ingredient (lab)

Lab shelf — same camera as GoldBridge’s Dirichlet engine plus Albert’s
two-class naming (`classA` / `classB`) from `Hire.TwoClassCoverage`.

**Not** a new distribution theorem: once the two hire residues mod `6Q` are
coprime to the modulus, Mathlib Dirichlet (via `Hire.exists_owner_prime_in_AP`)
supplies arbitrarily large owner primes, and two-class coverage turns congruence
into `Q ∣ m0 p`. GoldBridge itself is unused; the Dirichlet wrapper is enough.

Public voice: doors and hire classes; no ζ.
-/

namespace Hire

/-! ### Coprimality of the two hire residues -/

lemma classA_odd {Q : ℕ} (hQ : 0 < Q) : Odd (classA Q) := by
  simp [classA]
  split_ifs <;> (rw [Nat.odd_iff]; omega)

lemma classB_odd {Q : ℕ} (hQ : 0 < Q) : Odd (classB Q) := by
  simp [classB]
  split_ifs <;> (rw [Nat.odd_iff]; omega)

lemma classA_not_dvd_three {Q : ℕ} (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) :
    ¬ 3 ∣ classA Q := by
  intro h
  have hmod0 : classA Q % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  rcases chi3_eq_one_or_neg_one hQ3 with hs | hs
  · have hQ1 := Q_mod_eq_one_of_chi3_one hs
    rw [classA_of_one hs] at hmod0
    omega
  · have hQ2 := Q_mod_eq_two_of_chi3_neg hs
    rw [classA_of_neg hs] at hmod0
    omega

lemma classB_not_dvd_three {Q : ℕ} (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) :
    ¬ 3 ∣ classB Q := by
  intro h
  have hmod0 : classB Q % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  rcases chi3_eq_one_or_neg_one hQ3 with hs | hs
  · have hQ1 := Q_mod_eq_one_of_chi3_one hs
    rw [classB_of_one hs] at hmod0
    omega
  · have hQ2 := Q_mod_eq_two_of_chi3_neg hs
    rw [classB_of_neg hs] at hmod0
    omega

lemma classA_modEq_Q {Q : ℕ} (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) :
    classA Q ≡ 1 [MOD Q] ∨ classA Q ≡ Q - 1 [MOD Q] := by
  rcases chi3_eq_one_or_neg_one hQ3 with hs | hs
  · right
    -- 2Q − 1 ≡ −1 ≡ Q − 1 (mod Q)
    rw [classA_of_one hs]
    change (2 * Q - 1) % Q = (Q - 1) % Q
    have hL : (2 * Q - 1) % Q = Q - 1 := by
      have hrewrite : 2 * Q - 1 = (Q - 1) + Q * 1 := by omega
      rw [hrewrite, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hR : (Q - 1) % Q = Q - 1 := Nat.mod_eq_of_lt (by omega)
    omega
  · left
    rw [classA_of_neg hs]
    change (2 * Q + 1) % Q = 1 % Q
    have hL : (2 * Q + 1) % Q = 1 := by
      have hrewrite : 2 * Q + 1 = 1 + Q * 2 := by omega
      rw [hrewrite, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQ]
    have hR : 1 % Q = 1 := Nat.mod_eq_of_lt hQ
    omega

lemma classB_modEq_Q {Q : ℕ} (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) :
    classB Q ≡ 1 [MOD Q] ∨ classB Q ≡ Q - 1 [MOD Q] := by
  rcases chi3_eq_one_or_neg_one hQ3 with hs | hs
  · left
    rw [classB_of_one hs]
    change (4 * Q + 1) % Q = 1 % Q
    have hL : (4 * Q + 1) % Q = 1 := by
      have hrewrite : 4 * Q + 1 = 1 + Q * 4 := by omega
      rw [hrewrite, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQ]
    have hR : 1 % Q = 1 := Nat.mod_eq_of_lt hQ
    omega
  · right
    rw [classB_of_neg hs]
    change (4 * Q - 1) % Q = (Q - 1) % Q
    have hL : (4 * Q - 1) % Q = Q - 1 := by
      have hrewrite : 4 * Q - 1 = (Q - 1) + Q * 3 := by omega
      rw [hrewrite, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hR : (Q - 1) % Q = Q - 1 := Nat.mod_eq_of_lt (by omega)
    omega

lemma coprime_of_modEq_one {a n : ℕ} (hn : 1 < n) (h : a ≡ 1 [MOD n]) :
    a.Coprime n := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
  have : a % n = 1 := Nat.mod_eq_of_modEq h (by omega)
  rw [this, Nat.gcd_one_left]

lemma coprime_of_modEq_pred {a n : ℕ} (hn : 1 ≤ n) (h : a ≡ n - 1 [MOD n]) :
    a.Coprime n := by
  have hn0 : 0 < n := by omega
  have hlt : n - 1 < n := Nat.sub_lt hn0 (by decide)
  have ha : a % n = n - 1 := Nat.mod_eq_of_modEq h hlt
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, ha]
  exact (Nat.coprime_self_sub_left (Nat.succ_le_of_lt hn0)).2 (Nat.coprime_one_left _)

lemma classA_coprime_Q {Q : ℕ} (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) :
    (classA Q).Coprime Q := by
  rcases classA_modEq_Q hQ hQ3 with h | h
  · exact coprime_of_modEq_one hQ h
  · exact coprime_of_modEq_pred (Nat.le_of_lt hQ) h

lemma classB_coprime_Q {Q : ℕ} (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) :
    (classB Q).Coprime Q := by
  rcases classB_modEq_Q hQ hQ3 with h | h
  · exact coprime_of_modEq_one hQ h
  · exact coprime_of_modEq_pred (Nat.le_of_lt hQ) h

lemma odd_coprime_two {n : ℕ} (h : Odd n) : n.Coprime 2 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro hd
  exact Nat.not_even_iff_odd.mpr h (even_iff_two_dvd.mpr hd)

lemma classA_coprime_six_mul {Q : ℕ} (hQ : 1 < Q) (_hQodd : Odd Q) (hQ3 : ¬ 3 ∣ Q) :
    (classA Q).Coprime (6 * Q) := by
  have h6 : 6 * Q = 2 * 3 * Q := by ring
  rw [h6]
  have h2 : (classA Q).Coprime 2 := odd_coprime_two (classA_odd (by omega))
  have h3 : (classA Q).Coprime 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (classA_not_dvd_three hQ hQ3)
  exact (h2.mul_right h3).mul_right (classA_coprime_Q hQ hQ3)

lemma classB_coprime_six_mul {Q : ℕ} (hQ : 1 < Q) (_hQodd : Odd Q) (hQ3 : ¬ 3 ∣ Q) :
    (classB Q).Coprime (6 * Q) := by
  have h6 : 6 * Q = 2 * 3 * Q := by ring
  rw [h6]
  have h2 : (classB Q).Coprime 2 := odd_coprime_two (classB_odd (by omega))
  have h3 : (classB Q).Coprime 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (classB_not_dvd_three hQ hQ3)
  exact (h2.mul_right h3).mul_right (classB_coprime_Q hQ hQ3)

/-! ### Arbitrarily large owner primes -/

/-- For any bound `N`, a prime `p > max(N,3)` in class A hiring `Q`. -/
theorem exists_prime_hire_gt (Q : ℕ) (hQ : 1 < Q) (hQodd : Odd Q) (hQ3 : ¬ 3 ∣ Q)
    (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ 3 < p ∧ Q ∣ m0 p := by
  have hm : 6 * Q ≠ 0 := by omega
  have hcop := classA_coprime_six_mul hQ hQodd hQ3
  obtain ⟨p, hpN, hpPrime, hpMod⟩ :=
    exists_owner_prime_in_AP (max N 3) hm hcop
  have hp3 : 3 < p := lt_of_le_of_lt (Nat.le_max_right N 3) hpN
  have hN : N < p := lt_of_le_of_lt (Nat.le_max_left N 3) hpN
  have hmod : p % (6 * Q) = classA Q := by
    have : p % (6 * Q) = classA Q % (6 * Q) := hpMod
    rwa [Nat.mod_eq_of_lt (classA_lt (by omega))] at this
  have hdvd : Q ∣ m0 p :=
    (two_class_coverage hQ hQodd hQ3 hpPrime hp3).mpr (Or.inl hmod)
  exact ⟨p, hN, hpPrime, hp3, hdvd⟩

/-- Infinitely many primes hire the fixed odd ingredient `Q` (`3 ∤ Q`). -/
theorem infinite_primes_hire (Q : ℕ) (hQ : 1 < Q) (hQodd : Odd Q) (hQ3 : ¬ 3 ∣ Q) :
    {p : ℕ | p.Prime ∧ 3 < p ∧ Q ∣ m0 p}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨p, hpN, hpPrime, hp3, hdvd⟩ := exists_prime_hire_gt Q hQ hQodd hQ3 N
  exact ⟨p, ⟨hpPrime, hp3, hdvd⟩, hpN⟩

/-! ### Poster sanity (optional; congruence-level, no search) -/

example : (classA 5).Coprime (6 * 5) := by native_decide
example : (classB 5).Coprime (6 * 5) := by native_decide

end Hire
