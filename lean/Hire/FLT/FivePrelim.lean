import Hire.FLT.Four

namespace Hire

/-- The second factor in the sum-of-fifth-powers factorisation. -/
def fifthFactor (a b : ℤ) : ℤ :=
  a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4

theorem sum_fifth_powers_factorisation (a b : ℤ) :
    a ^ 5 + b ^ 5 = (a + b) * fifthFactor a b := by
  unfold fifthFactor
  ring

/-- Modulo the first factor, the second factor reduces to 5b⁴. -/
theorem fifthFactor_sub_five_mul_fourth (a b : ℤ) :
    fifthFactor a b - 5 * b ^ 4 =
      (a + b) *
        (a ^ 3 - 2 * a ^ 2 * b + 3 * a * b ^ 2 - 4 * b ^ 3) := by
  unfold fifthFactor
  ring

/-- A common divisor of the two factors divides 5b⁴. -/
theorem common_dvd_fifthFactor_dvd_five_mul_fourth
    {a b d : ℤ}
    (hS : d ∣ a + b)
    (hQ : d ∣ fifthFactor a b) :
    d ∣ 5 * b ^ 4 := by
  have hprod :
      d ∣ (a + b) *
        (a ^ 3 - 2 * a ^ 2 * b + 3 * a * b ^ 2 - 4 * b ^ 3) :=
    dvd_mul_of_dvd_left hS _

  rw [← fifthFactor_sub_five_mul_fourth a b] at hprod

  have hdiff :=
    dvd_sub hQ hprod

  simpa only [sub_sub_cancel] using hdiff

/-- For coprime inputs, a common divisor of the fifth-power
factors divides 5. -/
theorem common_dvd_fifthFactor_dvd_five
    {a b d : ℤ}
    (hab : IsCoprime a b)
    (hS : d ∣ a + b)
    (hQ : d ∣ fifthFactor a b) :
    d ∣ 5 := by
  have hfive : d ∣ 5 * b ^ 4 :=
    common_dvd_fifthFactor_dvd_five_mul_fourth hS hQ

  have hsumCop : IsCoprime (a + b) b := by
    obtain ⟨u, v, huv⟩ := hab
    refine ⟨u, v - u, ?_⟩
    calc
      u * (a + b) + (v - u) * b = u * a + v * b := by
        ring
      _ = 1 := huv

  have hsumPow : IsCoprime (a + b) (b ^ 4) :=
    hsumCop.pow_right

  have hdPow : IsCoprime d (b ^ 4) :=
    hsumPow.of_isCoprime_of_dvd_left hS

  exact hdPow.dvd_of_dvd_mul_right hfive

/-- Expose the factor of 5 when the sum is a multiple of 5. -/
theorem fifthFactor_of_sum_eq_five_mul
    {a b t : ℤ}
    (hS : a + b = 5 * t) :
    fifthFactor a b =
      5 * (125 * t ^ 4 - 125 * t ^ 3 * b +
        50 * t ^ 2 * b ^ 2 - 10 * t * b ^ 3 + b ^ 4) := by
  have ha : a = 5 * t - b := by linarith
  rw [ha]
  unfold fifthFactor
  ring

/-- Coprimality excludes 5 from b when it divides the sum. -/
theorem five_not_dvd_right_of_coprime_of_dvd_sum
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (5 : ℤ) ∣ a + b) :
    ¬ (5 : ℤ) ∣ b := by
  intro hb
  have ha : (5 : ℤ) ∣ a := by
    have hd := dvd_sub hS hb
    simpa using hd

  obtain ⟨u, v, huv⟩ := hab
  have hone : (5 : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add
      (dvd_mul_of_dvd_right ha u)
      (dvd_mul_of_dvd_right hb v)
  norm_num at hone

/-- The factor remaining after extracting 5 is 5-free. -/
theorem five_not_dvd_remaining_fifth_factor
    {t b : ℤ}
    (hb : ¬ (5 : ℤ) ∣ b) :
    ¬ (5 : ℤ) ∣
      (125 * t ^ 4 - 125 * t ^ 3 * b +
        50 * t ^ 2 * b ^ 2 - 10 * t * b ^ 3 + b ^ 4) := by
  intro hF

  have hmultiple :
      (5 : ℤ) ∣
        5 * (25 * t ^ 4 - 25 * t ^ 3 * b +
          10 * t ^ 2 * b ^ 2 - 2 * t * b ^ 3) :=
    dvd_mul_right 5 _

  have hfourth : (5 : ℤ) ∣ b ^ 4 := by
    have hd := dvd_sub hF hmultiple
    have heq :
        (125 * t ^ 4 - 125 * t ^ 3 * b +
          50 * t ^ 2 * b ^ 2 - 10 * t * b ^ 3 + b ^ 4) -
        5 * (25 * t ^ 4 - 25 * t ^ 3 * b +
          10 * t ^ 2 * b ^ 2 - 2 * t * b ^ 3) =
        b ^ 4 := by ring
    rw [heq] at hd
    exact hd

  have hprime : Prime (5 : ℤ) := by norm_num
  exact hb (hprime.dvd_of_dvd_pow hfourth)

/-- The fifth factor is 5 times a 5-free integer. -/
theorem fifthFactor_eq_five_mul_five_free
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (5 : ℤ) ∣ a + b) :
    ∃ F : ℤ,
      fifthFactor a b = 5 * F ∧ ¬ (5 : ℤ) ∣ F := by
  have hb := five_not_dvd_right_of_coprime_of_dvd_sum hab hS
  obtain ⟨t, ht⟩ := hS
  refine ⟨125 * t ^ 4 - 125 * t ^ 3 * b +
    50 * t ^ 2 * b ^ 2 - 10 * t * b ^ 3 + b ^ 4, ?_, ?_⟩
  · exact fifthFactor_of_sum_eq_five_mul ht
  · exact five_not_dvd_remaining_fifth_factor hb

/-- For coprime inputs whose sum is divisible by 5,
the fifth factor is not divisible by 25. -/
theorem twenty_five_not_dvd_fifthFactor
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (5 : ℤ) ∣ a + b) :
    ¬ (25 : ℤ) ∣ fifthFactor a b := by
  obtain ⟨F, hQ, hF⟩ :=
    fifthFactor_eq_five_mul_five_free hab hS

  intro h25
  obtain ⟨k, hk⟩ := h25

  apply hF
  refine ⟨k, ?_⟩
  nlinarith [hQ, hk]

/-- In the branch where 5 divides the sum, a coprime
fifth-power solution forces 625 to divide the sum. -/
theorem six_hundred_twenty_five_dvd_sum_of_fifth_powers
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (5 : ℤ) ∣ a + b)
    (hc : a ^ 5 + b ^ 5 = c ^ 5) :
    (625 : ℤ) ∣ a + b := by
  have hprime : Prime (5 : ℤ) := by norm_num

  have hproduct : (a + b) * fifthFactor a b = c ^ 5 := by
    rw [← sum_fifth_powers_factorisation]
    exact hc

  have hc5 : (5 : ℤ) ∣ c ^ 5 := by
    rw [← hproduct]
    exact dvd_mul_of_dvd_left hS (fifthFactor a b)

  have hcdvd : (5 : ℤ) ∣ c :=
    hprime.dvd_of_dvd_pow hc5

  obtain ⟨F, hQ, hF⟩ :=
    fifthFactor_eq_five_mul_five_free hab hS
  obtain ⟨t, ht⟩ := hS
  obtain ⟨k, hk⟩ := hcdvd

  have htf : t * F = 125 * k ^ 5 := by
    rw [ht, hQ, hk] at hproduct
    nlinarith [hproduct]

  have step :
      ∀ x y : ℤ, x * F = 5 * y →
        ∃ u : ℤ, x = 5 * u ∧ u * F = y := by
    intro x y hxy
    have hdiv : (5 : ℤ) ∣ x * F := by
      rw [hxy]
      exact dvd_mul_right 5 y

    have hx : (5 : ℤ) ∣ x := by
      rcases hprime.dvd_mul.mp hdiv with hx | hf
      · exact hx
      · exact False.elim (hF hf)

    obtain ⟨u, hu⟩ := hx
    refine ⟨u, hu, ?_⟩
    rw [hu] at hxy
    nlinarith [hxy]

  obtain ⟨u, hu, huF⟩ :=
    step t (25 * k ^ 5) (by nlinarith [htf])
  obtain ⟨v, hv, hvF⟩ :=
    step u (5 * k ^ 5) (by nlinarith [huF])
  obtain ⟨w, hw, _⟩ :=
    step v (k ^ 5) hvF

  refine ⟨w, ?_⟩
  rw [ht, hu, hv, hw]
  ring

/-- The fifth factor agrees with the fourth power of the sum modulo 5. -/
theorem sum_fourth_sub_fifthFactor (a b : ℤ) :
    (a + b) ^ 4 - fifthFactor a b =
      5 * (a * b * (a ^ 2 + a * b + b ^ 2)) := by
  unfold fifthFactor
  ring

/-- The exceptional prime divides precisely the same branch
of both fifth-power factors. -/
theorem five_dvd_fifthFactor_iff_dvd_sum
    (a b : ℤ) :
    (5 : ℤ) ∣ fifthFactor a b ↔ (5 : ℤ) ∣ a + b := by
  have hprime : Prime (5 : ℤ) := by norm_num
  have hdiff :
      (5 : ℤ) ∣ (a + b) ^ 4 - fifthFactor a b := by
    rw [sum_fourth_sub_fifthFactor]
    exact dvd_mul_right 5 _

  constructor
  · intro hQ
    have hpow : (5 : ℤ) ∣ (a + b) ^ 4 := by
      have hd := dvd_add hdiff hQ
      simpa only [sub_add_cancel] using hd
    exact hprime.dvd_of_dvd_pow hpow

  · intro hS
    have hpow : (5 : ℤ) ∣ (a + b) ^ 4 := by
      obtain ⟨t, ht⟩ := hS
      refine ⟨125 * t ^ 4, ?_⟩
      rw [ht]
      ring
    have hd := dvd_sub hpow hdiff
    simpa only [sub_sub_cancel] using hd

/-- In the 5-free branch, the two fifth-power factors are coprime. -/
theorem fifth_factors_coprime_of_five_free_sum
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : ¬ (5 : ℤ) ∣ a + b) :
    IsCoprime (a + b) (fifthFactor a b) := by
  have hprime : Prime (5 : ℤ) := by norm_num
  have hfive : IsCoprime (5 : ℤ) (a + b) :=
    hprime.coprime_iff_not_dvd.mpr hS

  have hrel : IsRelPrime (a + b) (fifthFactor a b) := by
    intro d hdS hdQ
    have hd5 : d ∣ (5 : ℤ) :=
      common_dvd_fifthFactor_dvd_five hab hdS hdQ
    exact hfive.isUnit_of_dvd' hd5 hdS

  exact hrel.isCoprime

/-- A coprime solution in the 5-free branch has
both factors equal to fifth powers. -/
theorem fifth_factors_are_fifth_powers_of_five_free_sum
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : ¬ (5 : ℤ) ∣ a + b)
    (hc : a ^ 5 + b ^ 5 = c ^ 5) :
    ∃ u v : ℤ,
      a + b = u ^ 5 ∧ fifthFactor a b = v ^ 5 := by
  have hcop :=
    fifth_factors_coprime_of_five_free_sum hab hS

  have hproduct : (a + b) * fifthFactor a b = c ^ 5 := by
    rw [← sum_fifth_powers_factorisation]
    exact hc

  obtain ⟨u, hu⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcop (by decide : Odd (5 : ℕ)) hproduct
  obtain ⟨v, hv⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_right
      hcop (by decide : Odd (5 : ℕ)) hproduct

  exact ⟨u, v, hu, hv⟩

/-- Express the fifth factor as a difference of square expressions. -/
theorem four_mul_fifthFactor (a b : ℤ) :
    4 * fifthFactor a b =
      5 * (a ^ 2 + b ^ 2) ^ 2 - (a + b) ^ 4 := by
  unfold fifthFactor
  ring

/-- The fifth factor appears in a quadratic norm expression. -/
theorem fifthFactor_quadratic_norm (a b : ℤ) :
    ((a + b) ^ 2) ^ 2 - 5 * (a ^ 2 + b ^ 2) ^ 2 =
      -4 * fifthFactor a b := by
  unfold fifthFactor
  ring

/-- Split the fifth factor using a root of X² - X - 1. -/
theorem fifth_factor_golden_split
    {R : Type*} [CommRing R]
    (phi a b : R)
    (hphi : phi ^ 2 = phi + 1) :
    a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 -
        a * b ^ 3 + b ^ 4 =
      (a ^ 2 + b ^ 2 - phi * a * b) *
        (a ^ 2 + b ^ 2 + (phi - 1) * a * b) := by
  linear_combination (a * b) ^ 2 * hphi

/-- The exceptional element in the golden-ratio ring squares to 5. -/
theorem golden_exceptional_sq
    {R : Type*} [CommRing R]
    (phi : R)
    (hphi : phi ^ 2 = phi + 1) :
    (2 * phi - 1) ^ 2 = 5 := by
  linear_combination 4 * hphi

/-- Difference of the two golden-ratio factors. -/
theorem golden_factors_difference
    {R : Type*} [CommRing R]
    (phi a b : R) :
    (a ^ 2 + b ^ 2 + (phi - 1) * a * b) -
      (a ^ 2 + b ^ 2 - phi * a * b) =
        (2 * phi - 1) * a * b := by
  ring

/-- A common divisor of the golden-ratio factors divides
the exceptional element times ab. -/
theorem common_dvd_golden_factors
    {R : Type*} [CommRing R]
    {phi a b d : R}
    (hL : d ∣ a ^ 2 + b ^ 2 - phi * a * b)
    (hM : d ∣ a ^ 2 + b ^ 2 + (phi - 1) * a * b) :
    d ∣ (2 * phi - 1) * a * b := by
  have hd := dvd_sub hM hL
  rw [golden_factors_difference] at hd
  exact hd

/-- The first golden factor is coprime to ab
when a and b are coprime. -/
theorem golden_factor_coprime_product
    {R : Type*} [CommRing R]
    {phi a b : R}
    (hab : IsCoprime a b) :
    IsCoprime (a * b)
      (a ^ 2 + b ^ 2 - phi * a * b) := by
  obtain ⟨u, v, huv⟩ := hab

  have hunit : (u * a + v * b) ^ 2 = 1 := by
    rw [huv]
    norm_num

  have haL :
      IsCoprime a (a ^ 2 + b ^ 2 - phi * a * b) := by
    refine ⟨
      u ^ 2 * a + 2 * u * v * b -
        v ^ 2 * a + v ^ 2 * phi * b,
      v ^ 2, ?_⟩
    linear_combination hunit

  have hbL :
      IsCoprime b (a ^ 2 + b ^ 2 - phi * a * b) := by
    refine ⟨
      v ^ 2 * b + 2 * u * v * a -
        u ^ 2 * b + u ^ 2 * phi * a,
      u ^ 2, ?_⟩
    linear_combination hunit

  exact IsCoprime.mul_left_iff.mpr ⟨haL, hbL⟩

/-- For coprime inputs, a common divisor of the golden factors divides the exceptional element alone. -/
theorem common_dvd_golden_factors_dvd_exceptional
    {R : Type*} [CommRing R]
    {phi a b d : R}
    (hab : IsCoprime a b)
    (hL : d ∣ a ^ 2 + b ^ 2 - phi * a * b)
    (hM : d ∣ a ^ 2 + b ^ 2 + (phi - 1) * a * b) :
    d ∣ 2 * phi - 1 := by
  have hprodCop :
      IsCoprime (a * b)
        (a ^ 2 + b ^ 2 - phi * a * b) :=
    golden_factor_coprime_product hab

  have hdCop : IsCoprime d (a * b) :=
    (hprodCop.of_isCoprime_of_dvd_right hL).symm

  have hd : d ∣ (2 * phi - 1) * (a * b) := by
    simpa only [mul_assoc] using
      common_dvd_golden_factors hL hM

  exact hdCop.dvd_of_dvd_mul_right hd

/-- The five possible fifth-power residues modulo 25. -/
def fifthResidue25 (i : Fin 5) : ZMod 25 :=
  ![0, 1, 7, 18, 24] i

theorem fifth_power_residue_25 :
    ∀ x : ZMod 25,
      ∃ i : Fin 5, x ^ 5 = fifthResidue25 i := by
  decide

/-- A sum of fifth-power residues can match another only if at least one of the three residues is zero. -/
theorem fifth_residue_sum_requires_zero :
    ∀ i j k : Fin 5,
      fifthResidue25 i + fifthResidue25 j = fifthResidue25 k →
        i = 0 ∨ j = 0 ∨ k = 0 := by
  decide

/-- A fifth power vanishing modulo 25 has a base divisible by 5. -/
theorem five_dvd_of_fifth_power_cast_zero
    {a : ℤ}
    (h : (a : ZMod 25) ^ 5 = 0) :
    (5 : ℤ) ∣ a := by
  have hcast : ((a ^ 5 : ℤ) : ZMod 25) = 0 := by
    simpa only [Int.cast_pow] using h

  have h25 : (25 : ℤ) ∣ a ^ 5 := by
    simpa using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 5) 25).mp hcast

  have h5 : (5 : ℤ) ∣ a ^ 5 :=
    dvd_trans (by norm_num : (5 : ℤ) ∣ 25) h25

  have hprime : Prime (5 : ℤ) := by norm_num
  exact hprime.dvd_of_dvd_pow h5

/-- Every integer fifth-power solution has an input or output divisible by 5. -/
theorem five_dvd_some_of_sum_fifth_powers
    {a b c : ℤ}
    (hc : a ^ 5 + b ^ 5 = c ^ 5) :
    (5 : ℤ) ∣ a ∨ (5 : ℤ) ∣ b ∨ (5 : ℤ) ∣ c := by
  have hcast :
      (a : ZMod 25) ^ 5 + (b : ZMod 25) ^ 5 =
        (c : ZMod 25) ^ 5 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 25)) hc
    simpa only [Int.cast_add, Int.cast_pow] using h

  obtain ⟨i, hi⟩ := fifth_power_residue_25 (a : ZMod 25)
  obtain ⟨j, hj⟩ := fifth_power_residue_25 (b : ZMod 25)
  obtain ⟨k, hk⟩ := fifth_power_residue_25 (c : ZMod 25)

  rw [hi, hj, hk] at hcast
  rcases fifth_residue_sum_requires_zero i j k hcast with
    hzero | hzero | hzero
  · subst i
    left
    apply five_dvd_of_fifth_power_cast_zero
    simpa [fifthResidue25] using hi
  · subst j
    right
    left
    apply five_dvd_of_fifth_power_cast_zero
    simpa [fifthResidue25] using hj
  · subst k
    right
    right
    apply five_dvd_of_fifth_power_cast_zero
    simpa [fifthResidue25] using hk

/-- An output divisible by 5 forces the input sum
to be divisible by 5. -/
theorem five_dvd_sum_of_fifth_power_output
    {a b c : ℤ}
    (hc : a ^ 5 + b ^ 5 = c ^ 5)
    (hc5 : (5 : ℤ) ∣ c) :
    (5 : ℤ) ∣ a + b := by
  have hfifth : ∀ x : ZMod 5, x ^ 5 = x := by
    decide

  have hcast :
      (a : ZMod 5) ^ 5 + (b : ZMod 5) ^ 5 =
        (c : ZMod 5) ^ 5 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 5)) hc
    simpa only [Int.cast_add, Int.cast_pow] using h

  have hcZero : (c : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mpr
      (by simpa using hc5)

  have hsum : (a : ZMod 5) + (b : ZMod 5) = 0 := by
    simpa only [hfifth, hcZero] using hcast

  have hsumCast : ((a + b : ℤ) : ZMod 5) = 0 := by
    simpa only [Int.cast_add] using hsum

  simpa using
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 5).mp hsumCast

/-- A coprime solution with output divisible by 5
has input sum divisible by 625. -/
theorem sum_dvd_625_of_fifth_power_output
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hc : a ^ 5 + b ^ 5 = c ^ 5)
    (hc5 : (5 : ℤ) ∣ c) :
    (625 : ℤ) ∣ a + b := by
  exact six_hundred_twenty_five_dvd_sum_of_fifth_powers
    hab (five_dvd_sum_of_fifth_power_output hc hc5) hc

/-- The integer factors remaining after removing the exceptional powers of 5 are coprime. -/
theorem fifth_integer_quotients_coprime
    {a b t F : ℤ}
    (hab : IsCoprime a b)
    (hS : a + b = 625 * t)
    (hQ : fifthFactor a b = 5 * F)
    (hF : ¬ (5 : ℤ) ∣ F) :
    IsCoprime t F := by
  have hprime : Prime (5 : ℤ) := by norm_num
  have hfiveCop : IsCoprime (5 : ℤ) F :=
    hprime.coprime_iff_not_dvd.mpr hF

  have hrel : IsRelPrime t F := by
    intro d hdt hdF

    have hdS : d ∣ a + b := by
      rw [hS]
      exact dvd_mul_of_dvd_right hdt 625

    have hdQ : d ∣ fifthFactor a b := by
      rw [hQ]
      exact dvd_mul_of_dvd_right hdF 5

    have hdFive : d ∣ (5 : ℤ) :=
      common_dvd_fifthFactor_dvd_five hab hdS hdQ

    exact hfiveCop.isUnit_of_dvd' hdFive hdF

  exact hrel.isCoprime

/-- After removing the exceptional powers of 5, the remaining product is a fifth power. -/
theorem fifth_integer_quotients_product
    {a b c t F k : ℤ}
    (hc : a ^ 5 + b ^ 5 = c ^ 5)
    (hS : a + b = 625 * t)
    (hQ : fifthFactor a b = 5 * F)
    (hk : c = 5 * k) :
    t * F = k ^ 5 := by
  have hproduct :
      (a + b) * fifthFactor a b = c ^ 5 := by
    calc
      (a + b) * fifthFactor a b =
          a ^ 5 + b ^ 5 :=
        (sum_fifth_powers_factorisation a b).symm
      _ = c ^ 5 := hc

  rw [hS, hQ, hk] at hproduct
  nlinarith [hproduct]

/-- After removing the exceptional powers of 5,
both remaining integer factors are fifth powers. -/
theorem fifth_integer_quotients_are_fifth_powers
    {a b c t F k : ℤ}
    (hab : IsCoprime a b)
    (hc : a ^ 5 + b ^ 5 = c ^ 5)
    (hS : a + b = 625 * t)
    (hQ : fifthFactor a b = 5 * F)
    (hF : ¬ (5 : ℤ) ∣ F)
    (hk : c = 5 * k) :
    ∃ u v : ℤ, t = u ^ 5 ∧ F = v ^ 5 := by
  have hcop : IsCoprime t F :=
    fifth_integer_quotients_coprime hab hS hQ hF

  have hproduct : t * F = k ^ 5 :=
    fifth_integer_quotients_product hc hS hQ hk

  obtain ⟨u, hu⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcop (by decide : Odd (5 : ℕ)) hproduct

  obtain ⟨v, hv⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_right
      hcop (by decide : Odd (5 : ℕ)) hproduct

  exact ⟨u, v, hu, hv⟩

end Hire
