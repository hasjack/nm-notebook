import Hire.CharacterObjects

namespace HireCharacterReadout

/-- The discarded-door conditions for hire 5. -/
def discardedIndicator15 (n : ℕ) : ℕ :=
  if (n % 3 = 1 ∧ n % 5 = 1) ∨
      (n % 3 = 2 ∧ n % 5 = 4) then 1 else 0

/-- For prime owners other than 3, the indicator detects
    precisely whether 5 divides the discarded door. -/
theorem discardedIndicator15_eq_door_indicator
    {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    discardedIndicator15 p =
      if 5 ∣ Hire.m1 p then 1 else 0 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hminus : 5 ∣ p - 1 ↔ p % 5 = 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hplus : 5 ∣ p + 1 ↔ p % 5 = 4 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  rcases Hire.prime_ne_three_mod_three_eq_one_or_two hp h3
    with h | h
  · simp [discardedIndicator15, Hire.m1, h, hminus]
  · simp [discardedIndicator15, Hire.m1, h, hplus]

/-- The discarded door has the opposite complex-character sign. -/
theorem discardedIndicator15_decomposition (n : ℕ) :
    4 * (discardedIndicator15 n : ℝ) =
      (principal15 n : ℝ) +
        (quadratic15 n : ℝ) +
          2 * (complex15 n).re := by
  set r3 := n % 3 with h3
  set r5 := n % 5 with h5
  have hr3 : r3 < 3 := Nat.mod_lt n (by norm_num)
  have hr5 : r5 < 5 := Nat.mod_lt n (by norm_num)
  interval_cases r3 <;> interval_cases r5 <;>
    norm_num [discardedIndicator15, principal15, quadratic15,
      complex15, quarticFive, Hire.chi3, ← h3, ← h5]

/-- Adding the doors removes the complex-character contribution. -/
theorem twoDoorIndicator15_add (n : ℕ) :
    (ownerIndicator15 n : ℝ) +
        (discardedIndicator15 n : ℝ) =
      ((principal15 n : ℝ) + (quadratic15 n : ℝ)) / 2 := by
  have hK := ownerIndicator15_decomposition n
  have hD := discardedIndicator15_decomposition n
  linarith

/-- Subtracting the doors isolates the complex-character contribution. -/
theorem twoDoorIndicator15_sub (n : ℕ) :
    (ownerIndicator15 n : ℝ) -
        (discardedIndicator15 n : ℝ) =
      -(complex15 n).re := by
  have hK := ownerIndicator15_decomposition n
  have hD := discardedIndicator15_decomposition n
  linarith

/-- The addition identity holds for any finite real weighting. -/
theorem sum_weighted_twoDoorIndicator15_add
    (S : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ S,
      w n * ((ownerIndicator15 n : ℝ) +
        (discardedIndicator15 n : ℝ))) =
      ((∑ n ∈ S, w n * (principal15 n : ℝ)) +
        (∑ n ∈ S, w n * (quadratic15 n : ℝ))) / 2 := by
  calc
    _ = ∑ n ∈ S,
        (w n * (principal15 n : ℝ) +
          w n * (quadratic15 n : ℝ)) / 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [twoDoorIndicator15_add]
      ring
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]

/-- The subtraction identity holds for any finite real weighting. -/
theorem sum_weighted_twoDoorIndicator15_sub
    (S : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ S,
      w n * ((ownerIndicator15 n : ℝ) -
        (discardedIndicator15 n : ℝ))) =
      -(∑ n ∈ S, w n * (complex15 n).re) := by
  calc
    _ = ∑ n ∈ S, -(w n * (complex15 n).re) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [twoDoorIndicator15_sub, mul_neg]
    _ = _ := by
      rw [Finset.sum_neg_distrib]

/-- The finite discarded-door Mangoldt readout. -/
noncomputable def discardedMangoldtSum15
    (N : ℕ) (σ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    mangoldtDirichletWeight σ n *
      (discardedIndicator15 n : ℝ)

/-- The finite difference is exactly minus the complex-character sum. -/
theorem owner_sub_discardedMangoldtSum15
    (N : ℕ) (σ : ℝ) :
    ownerMangoldtSum15 N σ -
        discardedMangoldtSum15 N σ =
      -(∑ n ∈ Finset.Icc 1 N,
        mangoldtDirichletWeight σ n * (complex15 n).re) := by
  unfold ownerMangoldtSum15 discardedMangoldtSum15
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ n ∈ Finset.Icc 1 N,
        mangoldtDirichletWeight σ n *
          ((ownerIndicator15 n : ℝ) -
            (discardedIndicator15 n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := sum_weighted_twoDoorIndicator15_sub
      (Finset.Icc 1 N) (mangoldtDirichletWeight σ)

/-- For σ > 1, the door difference converges to
    minus the complex character's Mangoldt value. -/
theorem tendsto_owner_sub_discardedMangoldtSum15
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ownerMangoldtSum15 N σ -
          discardedMangoldtSum15 N σ)
      Filter.atTop
      (nhds
        (-characterMangoldtValue15 complexCharacter15 σ)) := by
  have heq :
      (fun N : ℕ =>
        ownerMangoldtSum15 N σ -
          discardedMangoldtSum15 N σ) =
      (fun N : ℕ =>
        -(∑ n ∈ Finset.Icc 1 N,
          mangoldtDirichletWeight σ n * (complex15 n).re)) := by
    funext N
    exact owner_sub_discardedMangoldtSum15 N σ
  rw [heq]
  exact (tendsto_complexMangoldtSum15 hσ).neg

/-- The analytic door difference has a finite right-hand limit at 1. -/
theorem tendsto_twoDoorDifferenceValue15_at_one :
    Filter.Tendsto
      (fun σ : ℝ =>
        -characterMangoldtValue15 complexCharacter15 σ)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds
        (-continuedCharacterMangoldtValue15 complexCharacter15 1)) := by
  exact tendsto_complexMangoldtValue15_at_one.neg

/-- The door difference written as four residue indicators. -/
theorem twoDoorIndicator15_sub_eq_residue_indicators (n : ℕ) :
    (ownerIndicator15 n : ℝ) -
        (discardedIndicator15 n : ℝ) =
      ((if n % 15 = 4 then 1 else 0 : ℝ) +
        (if n % 15 = 11 then 1 else 0 : ℝ)) -
      (if n % 15 = 1 then 1 else 0 : ℝ) -
      (if n % 15 = 14 then 1 else 0 : ℝ) := by
  set r := n % 15 with hr
  have hlt : r < 15 := Nat.mod_lt n (by norm_num)
  have h3 : n % 3 = r % 3 := by omega
  have h5 : n % 5 = r % 5 := by omega
  interval_cases r <;>
    norm_num [ownerIndicator15, discardedIndicator15,
      h3, h5, ← hr]

/-- A finite weighted sum in one residue class modulo 15. -/
noncomputable def residueWeightSum15
    (S : Finset ℕ) (w : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ n ∈ S.filter (fun n => n % 15 = r), w n

/-- The weighted door difference is the signed sum of four classes. -/
theorem sum_weighted_twoDoor_eq_four_classes
    (S : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ S,
      w n * ((ownerIndicator15 n : ℝ) -
        (discardedIndicator15 n : ℝ))) =
      residueWeightSum15 S w 4 +
        residueWeightSum15 S w 11 -
        residueWeightSum15 S w 1 -
        residueWeightSum15 S w 14 := by
  classical
  unfold residueWeightSum15
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [twoDoorIndicator15_sub_eq_residue_indicators]
  by_cases h4 : n % 15 = 4 <;>
    by_cases h11 : n % 15 = 11 <;>
    by_cases h1 : n % 15 = 1 <;>
    by_cases h14 : n % 15 = 14 <;>
    simp [h4, h11, h1, h14]

/-- The unsmoothed Mangoldt sum in one class modulo 15. -/
noncomputable def residueMangoldtSum15
    (N r : ℕ) : ℝ :=
  residueWeightSum15 (Finset.Icc 1 N)
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) r

/-- The unsmoothed kept-minus-discarded Mangoldt readout. -/
noncomputable def twoDoorMangoldtDifference15 (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((ownerIndicator15 n : ℝ) -
        (discardedIndicator15 n : ℝ))

/-- The exact arithmetic-progression expression for the difference. -/
theorem twoDoorMangoldtDifference15_eq_four_classes (N : ℕ) :
    twoDoorMangoldtDifference15 N =
      residueMangoldtSum15 N 4 +
        residueMangoldtSum15 N 11 -
        residueMangoldtSum15 N 1 -
        residueMangoldtSum15 N 14 := by
  exact sum_weighted_twoDoor_eq_four_classes
    (Finset.Icc 1 N)
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- The same difference isolates the complex character. -/
theorem twoDoorMangoldtDifference15_eq_character_sum (N : ℕ) :
    twoDoorMangoldtDifference15 N =
      -(∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          (complex15 n).re) := by
  exact sum_weighted_twoDoorIndicator15_sub
    (Finset.Icc 1 N)
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- The door difference on a half-open interval [a, b). -/
noncomputable def twoDoorMangoldtInterval15
    (a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico a b,
    (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((ownerIndicator15 n : ℝ) -
        (discardedIndicator15 n : ℝ))

/-- The interval difference is the signed sum of four residue classes. -/
theorem twoDoorMangoldtInterval15_eq_four_classes
    (a b : ℕ) :
    twoDoorMangoldtInterval15 a b =
      residueWeightSum15 (Finset.Ico a b)
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 4 +
        residueWeightSum15 (Finset.Ico a b)
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 11 -
        residueWeightSum15 (Finset.Ico a b)
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 1 -
        residueWeightSum15 (Finset.Ico a b)
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) 14 := by
  exact sum_weighted_twoDoor_eq_four_classes
    (Finset.Ico a b)
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- The interval difference also isolates the complex character. -/
theorem twoDoorMangoldtInterval15_eq_character_sum
    (a b : ℕ) :
    twoDoorMangoldtInterval15 a b =
      -(∑ n ∈ Finset.Ico a b,
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          (complex15 n).re) := by
  exact sum_weighted_twoDoorIndicator15_sub
    (Finset.Ico a b)
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- H consecutive blocks of length 15, starting at block J. -/
noncomputable def groupedDoorMangoldtDifference15
    (J H : ℕ) : ℝ :=
  twoDoorMangoldtInterval15 (15 * J) (15 * (J + H))

/-- The grouped experimental readout has an exact character expression. -/
theorem groupedDoorMangoldtDifference15_eq_character_sum
    (J H : ℕ) :
    groupedDoorMangoldtDifference15 J H =
      -(∑ n ∈ Finset.Ico (15 * J) (15 * (J + H)),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          (complex15 n).re) := by
  exact twoDoorMangoldtInterval15_eq_character_sum
    (15 * J) (15 * (J + H))

/-- Each door-difference coefficient has absolute value at most 1. -/
theorem abs_twoDoorIndicator15_sub_le_one (n : ℕ) :
    |(ownerIndicator15 n : ℝ) -
      (discardedIndicator15 n : ℝ)| ≤ 1 := by
  unfold ownerIndicator15 discardedIndicator15
  split_ifs <;> norm_num

/-- The absolute weighted difference is bounded by the total
    Mangoldt weight on the same finite set. -/
theorem abs_sum_mangoldt_twoDoor_le
    (S : Finset ℕ) :
    |∑ n ∈ S,
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((ownerIndicator15 n : ℝ) -
          (discardedIndicator15 n : ℝ))| ≤
      ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) := by
  calc
    _ ≤ ∑ n ∈ S,
        |(ArithmeticFunction.vonMangoldt n : ℝ) *
          ((ownerIndicator15 n : ℝ) -
            (discardedIndicator15 n : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      rw [abs_mul, abs_of_nonneg hΛ]
      calc
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left
            (abs_twoDoorIndicator15_sub_le_one n) hΛ
        _ = _ := mul_one _

/-- Our natural-number cutoff agrees with Mathlib's ψ function. -/
theorem sum_vonMangoldt_Icc_eq_psi (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.vonMangoldt n : ℝ)) =
      Chebyshev.psi (N : ℝ) := by
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  simp [Chebyshev.psi]

/-- The unsmoothed door difference is bounded by ψ(N). -/
theorem abs_twoDoorMangoldtDifference15_le_psi (N : ℕ) :
    |twoDoorMangoldtDifference15 N| ≤
      Chebyshev.psi (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt n : ℝ) := by
      exact abs_sum_mangoldt_twoDoor_le (Finset.Icc 1 N)
    _ = _ := sum_vonMangoldt_Icc_eq_psi N

/-- An explicit linear baseline, valid for every natural cutoff. -/
theorem abs_twoDoorMangoldtDifference15_le_linear (N : ℕ) :
    |twoDoorMangoldtDifference15 N| ≤
      (Real.log 4 + 4) * (N : ℝ) := by
  exact (abs_twoDoorMangoldtDifference15_le_psi N).trans
    (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N))

/-- A sharper Chebyshev baseline for positive cutoffs. -/
theorem abs_twoDoorMangoldtDifference15_le_chebyshev
    (N : ℕ) (hN : 1 ≤ N) :
    |twoDoorMangoldtDifference15 N| ≤
      Real.log 4 * (N : ℝ) +
        2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  exact (abs_twoDoorMangoldtDifference15_le_psi N).trans
    (Chebyshev.psi_le hNR)

/-- The door difference restricted to primes. -/
noncomputable def primeDoorDifference15 (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
    Real.log (p : ℝ) *
      ((ownerIndicator15 p : ℝ) -
        (discardedIndicator15 p : ℝ))

/-- On primes, the Mangoldt weight is exactly log p. -/
theorem primeDoorDifference15_eq_mangoldt_sum (N : ℕ) :
    primeDoorDifference15 N =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (ArithmeticFunction.vonMangoldt p : ℝ) *
          ((ownerIndicator15 p : ℝ) -
            (discardedIndicator15 p : ℝ)) := by
  unfold primeDoorDifference15
  apply Finset.sum_congr rfl
  intro p hp
  rw [ArithmeticFunction.vonMangoldt_apply_prime
    (Finset.mem_filter.mp hp).2]

/-- The prime part of the total Mangoldt weight is θ(N). -/
theorem sum_prime_vonMangoldt_eq_theta (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (ArithmeticFunction.vonMangoldt p : ℝ)) =
      Chebyshev.theta (N : ℝ) := by
  have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hlog :
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (ArithmeticFunction.vonMangoldt p : ℝ)) =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log (p : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact ArithmeticFunction.vonMangoldt_apply_prime
      (Finset.mem_filter.mp hp).2
  simpa [Chebyshev.theta, hset] using hlog

/-- The total nonprime Mangoldt weight is ψ(N) - θ(N). -/
theorem sum_nonprime_vonMangoldt_eq_psi_sub_theta (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      if n.Prime then 0
      else (ArithmeticFunction.vonMangoldt n : ℝ)) =
      Chebyshev.psi (N : ℝ) -
        Chebyshev.theta (N : ℝ) := by
  classical
  rw [← sum_vonMangoldt_Icc_eq_psi,
    ← sum_prime_vonMangoldt_eq_theta]
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> simp [hp]

/-- Removing the prime-only signal leaves only nonprime terms. -/
theorem twoDoorDifference_sub_prime_eq_nonprime_sum (N : ℕ) :
    twoDoorMangoldtDifference15 N - primeDoorDifference15 N =
      ∑ n ∈ Finset.Icc 1 N,
        if n.Prime then 0
        else
          (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((ownerIndicator15 n : ℝ) -
              (discardedIndicator15 n : ℝ)) := by
  classical
  rw [primeDoorDifference15_eq_mangoldt_sum]
  unfold twoDoorMangoldtDifference15
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> simp [hp]

/-- The signed higher-power correction is bounded by
    the total higher-power weight. -/
theorem abs_twoDoorDifference_sub_prime_le_psi_sub_theta
    (N : ℕ) :
    |twoDoorMangoldtDifference15 N - primeDoorDifference15 N| ≤
      Chebyshev.psi (N : ℝ) -
        Chebyshev.theta (N : ℝ) := by
  classical
  rw [twoDoorDifference_sub_prime_eq_nonprime_sum]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        |if n.Prime then 0
          else
            (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((ownerIndicator15 n : ℝ) -
                (discardedIndicator15 n : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        if n.Prime then 0
        else (ArithmeticFunction.vonMangoldt n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime
      · simp [hp]
      · simp only [hp, ite_false]
        have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
          ArithmeticFunction.vonMangoldt_nonneg
        rw [abs_mul, abs_of_nonneg hΛ]
        calc
          _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left
              (abs_twoDoorIndicator15_sub_le_one n) hΛ
          _ = _ := mul_one _
    _ = _ := sum_nonprime_vonMangoldt_eq_psi_sub_theta N

/-- An explicit square-root-times-log bound for the
    higher-prime-power correction. -/
theorem abs_twoDoorDifference_sub_prime_le_sqrt_log
    (N : ℕ) (hN : 1 ≤ N) :
    |twoDoorMangoldtDifference15 N - primeDoorDifference15 N| ≤
      2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  calc
    _ ≤ Chebyshev.psi (N : ℝ) -
        Chebyshev.theta (N : ℝ) :=
      abs_twoDoorDifference_sub_prime_le_psi_sub_theta N
    _ ≤ |Chebyshev.psi (N : ℝ) -
        Chebyshev.theta (N : ℝ)| := le_abs_self _
    _ ≤ _ :=
      Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hNR

/-- A prime-only estimate transfers to the full Mangoldt signal. -/
theorem abs_twoDoorDifference_le_of_prime_bound
    (N : ℕ) (hN : 1 ≤ N)
    (E : ℝ)
    (hPrime : |primeDoorDifference15 N| ≤ E) :
    |twoDoorMangoldtDifference15 N| ≤
      E + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  calc
    _ = |primeDoorDifference15 N +
        (twoDoorMangoldtDifference15 N -
          primeDoorDifference15 N)| := by
      congr 1
      ring
    _ ≤ |primeDoorDifference15 N| +
        |twoDoorMangoldtDifference15 N -
          primeDoorDifference15 N| := abs_add_le _ _
    _ ≤ E + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
      add_le_add hPrime
        (abs_twoDoorDifference_sub_prime_le_sqrt_log N hN)

/-- A uniform prime-only estimate transfers at every positive cutoff. -/
theorem twoDoorDifference_bound_of_prime_bound
    (E : ℕ → ℝ)
    (hPrime : ∀ N : ℕ, 1 ≤ N →
      |primeDoorDifference15 N| ≤ E N) :
    ∀ N : ℕ, 1 ≤ N →
      |twoDoorMangoldtDifference15 N| ≤
        E N + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  intro N hN
  exact abs_twoDoorDifference_le_of_prime_bound
    N hN (E N) (hPrime N hN)

end HireCharacterReadout
