import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open scoped BigOperators

namespace HireMobius

theorem weighted_divisor_sum_ne_zero_iff (n : ℕ) :
    (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        ArithmeticFunction.log d) ≠ 0 ↔
      IsPrimePow n := by
  rw [ArithmeticFunction.sum_moebius_mul_log_eq]
  simpa using
    (ArithmeticFunction.vonMangoldt_ne_zero_iff (n := n))

theorem prime_base_eq_two_of_even_power
    {q k : ℕ} (hq : Nat.Prime q)
    (heven : 2 ∣ q ^ k) :
    q = 2 := by
  have hdiv : 2 ∣ q :=
    Nat.prime_two.dvd_of_dvd_pow heven
  rcases hq.eq_one_or_self_of_dvd 2 hdiv with h | h
  · norm_num at h
  · exact h.symm

theorem weighted_divisor_sum_two_pow
    {k : ℕ} (hk : k ≠ 0) :
    (∑ d ∈ (2 ^ k).divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        ArithmeticFunction.log d) =
      -Real.log 2 := by
  rw [ArithmeticFunction.sum_moebius_mul_log_eq,
    ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

theorem weighted_divisor_sum_eq_zero_of_not_prime_pow
    {n : ℕ} (hn : ¬ IsPrimePow n) :
    (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        ArithmeticFunction.log d) = 0 := by
  rw [ArithmeticFunction.sum_moebius_mul_log_eq,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
  simp

theorem even_prime_pow_iff_two_pow
    {n : ℕ} (heven : 2 ∣ n) :
    IsPrimePow n ↔ ∃ k : ℕ, 0 < k ∧ n = 2 ^ k := by
  constructor
  · intro hn
    obtain ⟨q, k, hq, hk, hpow⟩ :=
      (isPrimePow_nat_iff n).mp hn
    have hq2 : q = 2 :=
      prime_base_eq_two_of_even_power (k := k) hq
        (by
          rw [hpow]
          exact heven)
    exact ⟨k, hk, by simpa [hq2] using hpow.symm⟩
  · rintro ⟨k, hk, hpow⟩
    exact (isPrimePow_nat_iff n).mpr
      ⟨2, k, Nat.prime_two, hk, hpow.symm⟩

theorem weighted_divisor_sum_ne_zero_iff_two_pow
    {n : ℕ} (heven : 2 ∣ n) :
    (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        ArithmeticFunction.log d) ≠ 0 ↔
      ∃ k : ℕ, 0 < k ∧ n = 2 ^ k := by
  exact (weighted_divisor_sum_ne_zero_iff n).trans
    (even_prime_pow_iff_two_pow heven)

open scoped Classical
theorem weighted_divisor_sum_even
    {n : ℕ} (heven : 2 ∣ n) :
    (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        ArithmeticFunction.log d) =
      if ∃ k : ℕ, 0 < k ∧ n = 2 ^ k
      then -Real.log 2
      else 0 := by
  classical
  by_cases h : ∃ k : ℕ, 0 < k ∧ n = 2 ^ k
  · rw [ite_eq_left h]
    obtain ⟨k, hk, rfl⟩ := h
    exact weighted_divisor_sum_two_pow (Nat.ne_zero_of_lt hk)
  · rw [ite_eq_right h]
    apply weighted_divisor_sum_eq_zero_of_not_prime_pow
    intro hn
    exact h ((even_prime_pow_iff_two_pow heven).mp hn)

/-- An odd divisor of an even number brings the factor 2. -/
theorem two_mul_dvd_iff_of_odd_of_even
    {e m : ℕ} (he : Odd e) (hm : Even m) :
    2 * e ∣ m ↔ e ∣ m := by
  constructor
  · intro h
    exact dvd_trans (by simp : e ∣ 2 * e) h
  · intro h
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      he.coprime_two_left
      (even_iff_two_dvd.mp hm) h

/-- Adding the prime factor 2 reverses the Möbius sign
when the original number is odd. -/
theorem moebius_two_mul_of_odd
    {e : ℕ} (he : Odd e) :
    ArithmeticFunction.moebius (2 * e) =
      -ArithmeticFunction.moebius e := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    he.coprime_two_left,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  simp

/-- The logarithm-weighted terms for `e` and `2 * e`
cancel down to a constant multiple of `μ(e)`. -/
theorem weighted_moebius_pair
    {e : ℕ} (he : Odd e) :
    (ArithmeticFunction.moebius e : ℝ) *
        Real.log (e : ℝ) +
      (ArithmeticFunction.moebius (2 * e) : ℝ) *
        Real.log ((2 * e : ℕ) : ℝ) =
      -(ArithmeticFunction.moebius e : ℝ) *
        Real.log 2 := by
  have he0 : e ≠ 0 := by
    intro h
    subst e
    simp at he
  have heR : (e : ℝ) ≠ 0 := by
    exact_mod_cast he0
  rw [moebius_two_mul_of_odd he]
  push_cast
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) heR]
  ring

/-- A divisor containing the square factor 4 has Möbius value zero. -/
theorem moebius_eq_zero_of_four_dvd
    {d : ℕ} (hd : 4 ∣ d) :
    ArithmeticFunction.moebius d = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hs
  have hnot : ¬ (2 : ℕ) * 2 ∣ d :=
    (Nat.squarefree_iff_prime_squarefree.mp hs)
      2 Nat.prime_two
  exact hnot (by simpa using hd)

/-- Such divisors contribute nothing to the weighted sum. -/
theorem weighted_moebius_eq_zero_of_four_dvd
    {d : ℕ} (hd : 4 ∣ d) :
    (ArithmeticFunction.moebius d : ℝ) *
      Real.log (d : ℝ) = 0 := by
  rw [moebius_eq_zero_of_four_dvd hd]
  simp

/-- A natural number not divisible by four is odd or twice an odd number. -/
theorem not_four_dvd_iff_odd_or_twice_odd (d : ℕ) :
    ¬ 4 ∣ d ↔ Odd d ∨ ∃ e : ℕ, Odd e ∧ d = 2 * e := by
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.odd_iff]
  constructor
  · intro h4
    by_cases ho : d % 2 = 1
    · exact Or.inl ho
    · right
      refine ⟨d / 2, ?_, ?_⟩ <;> omega
  · intro h
    rcases h with ho | ⟨e, he, hde⟩
    · omega
    · omega

end HireMobius
