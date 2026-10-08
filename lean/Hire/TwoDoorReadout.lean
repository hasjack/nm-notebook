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

end HireCharacterReadout
