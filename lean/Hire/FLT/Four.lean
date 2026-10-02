import Hire.FLT.Cubic

namespace Hire

theorem fourth_gap_from_cubic_gap (a b c : ℤ) :
    c ^ 4 - a ^ 4 - b ^ 4 =
      c * (c ^ 3 - a ^ 3 - b ^ 3) +
        a ^ 3 * (c - a) + b ^ 3 * (c - b) := by
  ring

/-- Relate mismatches at consecutive exponents. -/
theorem successor_gap (a b c : ℤ) (n : ℕ) :
    c ^ (n + 1) - a ^ (n + 1) - b ^ (n + 1) =
      c * (c ^ n - a ^ n - b ^ n) +
        a ^ n * (c - a) + b ^ n * (c - b) := by
  simp only [pow_succ]
  ring

/-- A match at the next exponent forces a negative gap here. -/
theorem gap_negative_of_successor_match
    {a b c : ℤ} {n : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hac : a < c) (hbc : b < c)
    (hmatch :
      a ^ (n + 1) + b ^ (n + 1) = c ^ (n + 1)) :
    c ^ n < a ^ n + b ^ n := by
  have hc : 0 < c := lt_trans ha hac
  have hapos : 0 < a ^ n := pow_pos ha n
  have hbpos : 0 < b ^ n := pow_pos hb n
  have hleft : 0 < a ^ n * (c - a) :=
    mul_pos hapos (sub_pos.mpr hac)
  have hright : 0 < b ^ n * (c - b) :=
    mul_pos hbpos (sub_pos.mpr hbc)

  have hgap := successor_gap a b c n
  have hzero :
      c ^ (n + 1) - a ^ (n + 1) - b ^ (n + 1) = 0 := by
    linarith [hmatch]
  rw [hzero] at hgap

  by_contra h
  have hnonneg : 0 ≤ c ^ n - a ^ n - b ^ n := by
    linarith
  have hproduct :
      0 ≤ c * (c ^ n - a ^ n - b ^ n) :=
    mul_nonneg (le_of_lt hc) hnonneg
  linarith

/-- A fourth-power solution gives a Pythagorean triple of squares. -/
theorem squares_pythagorean_of_fourth_match
    {a b c : ℤ}
    (h : a ^ 4 + b ^ 4 = c ^ 4) :
    (a ^ 2) ^ 2 + (b ^ 2) ^ 2 = (c ^ 2) ^ 2 := by
  simpa only [← pow_mul] using h

/-- Parametrise a primitive fourth-power-to-square solution,
with the odd leg placed first. -/
theorem fourth_square_parametrisation
    {a b z : ℤ}
    (h : a ^ 4 + b ^ 4 = z ^ 2)
    (hcop : Int.gcd (a ^ 2) (b ^ 2) = 1)
    (hodd : a ^ 2 % 2 = 1)
    (hz : 0 < z) :
    ∃ m n : ℤ,
      a ^ 2 = m ^ 2 - n ^ 2 ∧
      b ^ 2 = 2 * m * n ∧
      z = m ^ 2 + n ^ 2 ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨
       m % 2 = 1 ∧ n % 2 = 0) ∧
      0 ≤ m := by
  have hpyth : PythagoreanTriple (a ^ 2) (b ^ 2) z := by
    unfold PythagoreanTriple
    nlinarith [h]
  exact hpyth.coprime_classification' hcop hodd hz

/-- Coprime inputs give coprime square legs. -/
theorem square_legs_gcd_one
    {a b : ℤ} (hab : IsCoprime a b) :
    Int.gcd (a ^ 2) (b ^ 2) = 1 := by
  have hn : Nat.Coprime a.natAbs b.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hab
  have hs : Nat.Coprime (a.natAbs ^ 2) (b.natAbs ^ 2) := by
    simpa only [
      Nat.coprime_pow_left_iff (by decide : 0 < (2 : ℕ)),
      Nat.coprime_pow_right_iff (by decide : 0 < (2 : ℕ))
    ] using hn
  change Nat.gcd (a ^ 2).natAbs (b ^ 2).natAbs = 1
  simpa only [Int.natAbs_pow] using hs

/-- The square legs have opposite parity. -/
theorem square_legs_opposite_parity
    {a b z : ℤ}
    (hab : IsCoprime a b)
    (h : a ^ 4 + b ^ 4 = z ^ 2) :
    (a ^ 2 % 2 = 0 ∧ b ^ 2 % 2 = 1) ∨
    (a ^ 2 % 2 = 1 ∧ b ^ 2 % 2 = 0) := by
  have hpyth : PythagoreanTriple (a ^ 2) (b ^ 2) z := by
    unfold PythagoreanTriple
    nlinarith [h]
  exact hpyth.even_odd_of_coprime (square_legs_gcd_one hab)

/-- Choose a positive hypotenuse without changing the equation. -/
theorem positive_hypotenuse_of_fourth_square
    {a b z : ℤ}
    (ha : a ≠ 0)
    (h : a ^ 4 + b ^ 4 = z ^ 2) :
    0 < |z| ∧ a ^ 4 + b ^ 4 = |z| ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have ha4 : 0 < a ^ 4 := by
    nlinarith [sq_nonneg (a ^ 2)]
  have hb4 : 0 ≤ b ^ 4 := by
    nlinarith [sq_nonneg (b ^ 2)]
  have hz : z ≠ 0 := by
    intro hz
    subst z
    norm_num at h
    linarith
  constructor
  · exact abs_pos.mpr hz
  · simpa only [sq_abs] using h

/-- Orient and parametrise a coprime fourth-power-to-square solution. -/
theorem oriented_fourth_square_parametrisation
    {a b z : ℤ}
    (ha : a ≠ 0)
    (hab : IsCoprime a b)
    (h : a ^ 4 + b ^ 4 = z ^ 2) :
    ∃ A B m n : ℤ,
      ((A = a ∧ B = b) ∨ (A = b ∧ B = a)) ∧
      A ^ 2 = m ^ 2 - n ^ 2 ∧
      B ^ 2 = 2 * m * n ∧
      |z| = m ^ 2 + n ^ 2 ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨
       m % 2 = 1 ∧ n % 2 = 0) ∧
      0 ≤ m := by
  obtain ⟨hzpos, habs⟩ :=
    positive_hypotenuse_of_fourth_square ha h

  rcases square_legs_opposite_parity hab h with hpar | hpar
  · -- The second leg is odd: swap the inputs.
    have hswap : b ^ 4 + a ^ 4 = |z| ^ 2 := by
      linarith [habs]
    obtain ⟨m, n, hm, hn, hz, hcop, hmnpar, hmpos⟩ :=
      fourth_square_parametrisation
        hswap (square_legs_gcd_one hab.symm) hpar.2 hzpos
    exact ⟨b, a, m, n, Or.inr ⟨rfl, rfl⟩,
      hm, hn, hz, hcop, hmnpar, hmpos⟩
  · -- The first leg is odd: keep the inputs.
    obtain ⟨m, n, hm, hn, hz, hcop, hmnpar, hmpos⟩ :=
      fourth_square_parametrisation
        habs (square_legs_gcd_one hab) hpar.1 hzpos
    exact ⟨a, b, m, n, Or.inl ⟨rfl, rfl⟩,
      hm, hn, hz, hcop, hmnpar, hmpos⟩

/-- Coprime parameters of opposite parity have coprime
difference and sum. -/
theorem difference_sum_coprime
    {m n : ℤ}
    (hcop : Int.gcd m n = 1)
    (hpar :
      (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    IsCoprime (m - n) (m + n) := by
  have hmn : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hcop

  have hodd : Odd (m - n) := by
    refine ⟨(m - n) / 2, ?_⟩
    rcases hpar with hpar | hpar
    · omega
    · omega

  have htwo : IsCoprime (2 : ℤ) (m - n) :=
    Int.isCoprime_two_left.mpr hodd

  obtain ⟨u, v, huv⟩ := hmn
  obtain ⟨r, s, hrs⟩ := htwo

  refine ⟨s + r * (u - v), r * (u + v), ?_⟩
  calc
    (s + r * (u - v)) * (m - n) +
        (r * (u + v)) * (m + n) =
        s * (m - n) + 2 * r * (u * m + v * n) := by
          ring
    _ = 1 := by
      rw [huv]
      nlinarith [hrs]

/-- The difference of the parameters is a square up to sign. -/
theorem parameter_difference_square
    {A m n : ℤ}
    (hcop : Int.gcd m n = 1)
    (hpar :
      (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0))
    (hA : A ^ 2 = m ^ 2 - n ^ 2) :
    ∃ r : ℤ, m - n = r ^ 2 ∨ m - n = -(r ^ 2) := by
  have hprod : (m - n) * (m + n) = A ^ 2 := by
    nlinarith [hA]
  exact Int.sq_of_isCoprime
    (difference_sum_coprime hcop hpar) hprod

/-- Both factors of the odd square leg are positive. -/
theorem parameter_factors_positive
    {A m n : ℤ}
    (hA0 : A ≠ 0)
    (hm : 0 ≤ m)
    (hA : A ^ 2 = m ^ 2 - n ^ 2) :
    0 < m - n ∧ 0 < m + n := by
  have hApos : 0 < A ^ 2 := sq_pos_of_ne_zero hA0
  constructor
  · by_contra h
    have hle : m ≤ n := by omega
    have hprod : 0 ≤ (n - m) * (n + m) :=
      mul_nonneg (sub_nonneg.mpr hle) (by omega)
    nlinarith [hA]
  · by_contra h
    have hle : n ≤ -m := by omega
    have hprod : 0 ≤ (-n - m) * (-n + m) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [hA]

/-- The parameter difference and sum are genuine squares. -/
theorem parameter_factors_are_squares
    {A m n : ℤ}
    (hA0 : A ≠ 0)
    (hm : 0 ≤ m)
    (hcop : Int.gcd m n = 1)
    (hpar :
      (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0))
    (hA : A ^ 2 = m ^ 2 - n ^ 2) :
    ∃ r s : ℤ,
      m - n = r ^ 2 ∧ m + n = s ^ 2 := by
  obtain ⟨hminus, hplus⟩ :=
    parameter_factors_positive hA0 hm hA

  have hcopFactors := difference_sum_coprime hcop hpar
  have hprod : (m - n) * (m + n) = A ^ 2 := by
    nlinarith [hA]

  obtain ⟨r, hr⟩ :=
    Int.sq_of_isCoprime hcopFactors hprod
  obtain ⟨s, hs⟩ :=
    Int.sq_of_isCoprime hcopFactors.symm
      (by simpa only [mul_comm] using hprod)

  have hrpos : m - n = r ^ 2 := by
    rcases hr with hr | hr
    · exact hr
    · nlinarith [sq_nonneg r]

  have hspos : m + n = s ^ 2 := by
    rcases hs with hs | hs
    · exact hs
    · nlinarith [sq_nonneg s]

  exact ⟨r, s, hrpos, hspos⟩

/-- The first parametrisation exposes a second Pythagorean triple. -/
theorem second_pythagorean_of_parameter
    {A m n : ℤ}
    (hA : A ^ 2 = m ^ 2 - n ^ 2) :
    PythagoreanTriple A n m := by
  unfold PythagoreanTriple
  nlinarith [hA]

/-- The second parametrisation turns the even-leg constraint
into a square product. -/
theorem even_leg_square_product
    {B m n u v w : ℤ}
    (hB : B ^ 2 = 2 * m * n)
    (hn : n = 2 * u * v)
    (hw : B = 2 * w) :
    w ^ 2 = m * u * v := by
  rw [hn, hw] at hB
  nlinarith [hB]

/-- The second Pythagorean triple has coprime legs. -/
theorem second_pythagorean_coprime
    {A m n : ℤ}
    (hcop : Int.gcd m n = 1)
    (hA : A ^ 2 = m ^ 2 - n ^ 2) :
    IsCoprime A n := by
  have hmn : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hcop

  apply isCoprime_of_prime_dvd
  · rintro ⟨hAz, hnz⟩
    have hmz : m = 0 := by
      rw [hAz, hnz] at hA
      nlinarith [sq_nonneg m]
    subst m
    subst n
    norm_num at hcop

  · intro p hp hpA hpn

    have hpA2 : p ∣ A ^ 2 := by
      simpa only [pow_two] using
        dvd_mul_of_dvd_left hpA A

    have hpn2 : p ∣ n ^ 2 := by
      simpa only [pow_two] using
        dvd_mul_of_dvd_left hpn n

    have hm2 : m ^ 2 = A ^ 2 + n ^ 2 := by
      linarith [hA]

    have hpm2 : p ∣ m ^ 2 := by
      rw [hm2]
      exact dvd_add hpA2 hpn2

    have hpm : p ∣ m :=
      hp.dvd_of_dvd_pow hpm2

    exact hp.not_isUnit (hmn.isUnit_of_dvd' hpm hpn)

/-- An odd square has an odd root. -/
theorem odd_mod_two_of_square_odd
    {A : ℤ}
    (hodd : A ^ 2 % 2 = 1) :
    A % 2 = 1 := by
  by_contra h
  have hzero : A % 2 = 0 := by omega
  have hsquare : A ^ 2 % 2 = 0 := by
    simp [pow_two, Int.mul_emod, hzero]
  omega

/-- Parametrise the second primitive Pythagorean triple. -/
theorem second_parameterisation
    {A m n : ℤ}
    (hA0 : A ≠ 0)
    (hm : 0 ≤ m)
    (hcop : Int.gcd m n = 1)
    (hodd : A ^ 2 % 2 = 1)
    (hA : A ^ 2 = m ^ 2 - n ^ 2) :
    ∃ u v : ℤ,
      A = u ^ 2 - v ^ 2 ∧
      n = 2 * u * v ∧
      m = u ^ 2 + v ^ 2 ∧
      Int.gcd u v = 1 ∧
      (u % 2 = 0 ∧ v % 2 = 1 ∨
       u % 2 = 1 ∧ v % 2 = 0) ∧
      0 ≤ u := by
  have hpyth : PythagoreanTriple A n m :=
    second_pythagorean_of_parameter hA

  have hcopAn : Int.gcd A n = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp
      (second_pythagorean_coprime hcop hA)

  have hAodd : A % 2 = 1 :=
    odd_mod_two_of_square_odd hodd

  obtain ⟨hminus, hplus⟩ :=
    parameter_factors_positive hA0 hm hA

  have hmpos : 0 < m := by omega

  exact hpyth.coprime_classification'
    hcopAn hAodd hmpos

/-- The three factors in the square product are pairwise coprime. -/
theorem second_parameters_pairwise_coprime
    {m n u v : ℤ}
    (hmn : Int.gcd m n = 1)
    (huv : Int.gcd u v = 1)
    (hn : n = 2 * u * v) :
    IsCoprime m u ∧ IsCoprime m v ∧ IsCoprime u v := by
  have hmnCop : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hmn

  have hun : u ∣ n := by
    rw [hn]
    exact ⟨2 * v, by ring⟩

  have hvn : v ∣ n := by
    rw [hn]
    exact ⟨2 * u, by ring⟩

  exact ⟨
    hmnCop.of_isCoprime_of_dvd_right hun,
    hmnCop.of_isCoprime_of_dvd_right hvn,
    Int.isCoprime_iff_gcd_eq_one.mpr huv⟩

/-- The old parameter m becomes the square of the new hypotenuse. -/
theorem square_of_coprime_square_product
    {m u v w : ℤ}
    (hm : 0 < m)
    (hmu : IsCoprime m u)
    (hmv : IsCoprime m v)
    (hprod : w ^ 2 = m * u * v) :
    ∃ t : ℤ, m = t ^ 2 := by
  have hcop : IsCoprime m (u * v) :=
    IsCoprime.mul_right_iff.mpr ⟨hmu, hmv⟩

  have heq : m * (u * v) = w ^ 2 := by
    nlinarith [hprod]

  obtain ⟨t, ht⟩ := Int.sq_of_isCoprime hcop heq
  refine ⟨t, ?_⟩
  rcases ht with ht | ht
  · exact ht
  · nlinarith [sq_nonneg t]

/-- Nonzero legs force the second parameters to be positive. -/
theorem second_parameters_positive
    {B m n u v : ℤ}
    (hB0 : B ≠ 0)
    (hm : 0 < m)
    (hu : 0 ≤ u)
    (hB : B ^ 2 = 2 * m * n)
    (hn : n = 2 * u * v) :
    0 < u ∧ 0 < v := by
  have hBpos : 0 < B ^ 2 := sq_pos_of_ne_zero hB0
  have hnpos : 0 < n := by
    by_contra h
    have hnle : n ≤ 0 := by omega
    have hnonpos : 2 * m * n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hnle
    linarith [hB]

  have hupos : 0 < u := by
    by_contra h
    have huzero : u = 0 := by omega
    rw [huzero] at hn
    nlinarith [hn]

  have hvpos : 0 < v := by
    by_contra h
    have hvle : v ≤ 0 := by omega
    have hnonpos : 2 * u * v ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hvle
    linarith [hn]

  exact ⟨hupos, hvpos⟩

/-- A positive, pairwise coprime square product
has three square factors. -/
theorem three_square_factors
    {m u v w : ℤ}
    (hm : 0 < m) (hu : 0 < u) (hv : 0 < v)
    (hmu : IsCoprime m u)
    (hmv : IsCoprime m v)
    (huv : IsCoprime u v)
    (hprod : w ^ 2 = m * u * v) :
    ∃ t r s : ℤ,
      m = t ^ 2 ∧ u = r ^ 2 ∧ v = s ^ 2 := by
  obtain ⟨t, ht⟩ :=
    square_of_coprime_square_product hm hmu hmv hprod

  have hprodU : w ^ 2 = u * m * v := by
    nlinarith [hprod]
  obtain ⟨r, hr⟩ :=
    square_of_coprime_square_product
      hu hmu.symm huv hprodU

  have hprodV : w ^ 2 = v * m * u := by
    nlinarith [hprod]
  obtain ⟨s, hs⟩ :=
    square_of_coprime_square_product
      hv hmv.symm huv.symm hprodV

  exact ⟨t, r, s, ht, hr, hs⟩

/-- Square parameters produce another fourth-power-to-square equation. -/
theorem fourth_square_from_square_parameters
    {m u v t r s : ℤ}
    (hm : m = u ^ 2 + v ^ 2)
    (ht : m = t ^ 2)
    (hr : u = r ^ 2)
    (hs : v = s ^ 2) :
    r ^ 4 + s ^ 4 = t ^ 2 := by
  rw [hr, hs] at hm
  nlinarith [hm, ht]

/-- The new hypotenuse is strictly smaller than the old one. -/
theorem new_hypotenuse_strictly_smaller
    {m n t z : ℤ}
    (hm : 0 < m)
    (hn0 : n ≠ 0)
    (ht : m = t ^ 2)
    (hz : |z| = m ^ 2 + n ^ 2) :
    |t| < |z| := by
  have ht0 : t ≠ 0 := by
    intro hzero
    rw [hzero] at ht
    norm_num at ht
    linarith

  have htpos : 0 < |t| := abs_pos.mpr ht0
  have htge : 1 ≤ |t| := by omega
  have hmge : 1 ≤ m := by omega

  have habssq : |t| ^ 2 = t ^ 2 := by
    simp only [sq_abs]

  have htbound : |t| ≤ m := by
    nlinarith [sq_nonneg (|t| - 1)]

  have hmSquare : m ≤ m ^ 2 := by
    nlinarith [sq_nonneg (m - 1)]

  have hnSquare : 0 < n ^ 2 := sq_pos_of_ne_zero hn0
  linarith [hz]

/-- Positive square parameters give nonzero new legs. -/
theorem new_fourth_square_legs_nonzero
    {u v r s : ℤ}
    (hu : 0 < u) (hv : 0 < v)
    (hr : u = r ^ 2)
    (hs : v = s ^ 2) :
    r ≠ 0 ∧ s ≠ 0 := by
  constructor
  · intro hzero
    rw [hzero] at hr
    norm_num at hr
    linarith
  · intro hzero
    rw [hzero] at hs
    norm_num at hs
    linarith

/-- Opposite-parity parameters make the first square leg odd. -/
theorem first_parameter_square_odd
    {A m n : ℤ}
    (hpar :
      (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0))
    (hA : A ^ 2 = m ^ 2 - n ^ 2) :
    A ^ 2 % 2 = 1 := by
  have hmod := congrArg (fun x : ℤ => x % 2) hA
  rcases hpar with hpar | hpar
  · simpa [pow_two, Int.sub_emod, Int.mul_emod,
      hpar.1, hpar.2] using hmod
  · simpa [pow_two, Int.sub_emod, Int.mul_emod,
      hpar.1, hpar.2] using hmod

/-- The even square leg has an integer half. -/
theorem even_leg_has_half
    {B m n : ℤ}
    (hB : B ^ 2 = 2 * m * n) :
    ∃ w : ℤ, B = 2 * w := by
  have hsquareEven : B ^ 2 % 2 = 0 := by
    rw [hB]
    simp [Int.mul_emod]

  have hBEven : B % 2 = 0 := by
    by_contra h
    have hBOdd : B % 2 = 1 := by omega
    have hsquareOdd : B ^ 2 % 2 = 1 := by
      simp [pow_two, Int.mul_emod, hBOdd]
    omega

  exact ⟨B / 2, by omega⟩

/-- A coprime fourth-power-to-square solution produces
another coprime solution with a smaller hypotenuse. -/
theorem exists_smaller_fourth_square_solution
    {a b z : ℤ}
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hab : IsCoprime a b)
    (h : a ^ 4 + b ^ 4 = z ^ 2) :
    ∃ r s t : ℤ,
      r ≠ 0 ∧ s ≠ 0 ∧
      IsCoprime r s ∧
      r ^ 4 + s ^ 4 = t ^ 2 ∧
      |t| < |z| := by
  obtain ⟨A, B, m, n, hchoice,
      hA, hB, hz, hmn, hpar, hm⟩ :=
    oriented_fourth_square_parametrisation ha hab h

  have hA0 : A ≠ 0 := by
    rcases hchoice with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ha
    · exact hb

  have hB0 : B ≠ 0 := by
    rcases hchoice with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hb
    · exact ha

  obtain ⟨hminus, hplus⟩ :=
    parameter_factors_positive hA0 hm hA
  have hmpos : 0 < m := by omega

  have hn0 : n ≠ 0 := by
    intro hnzero
    rw [hnzero] at hB
    have hBpos : 0 < B ^ 2 := sq_pos_of_ne_zero hB0
    nlinarith [hB]

  have hAodd : A ^ 2 % 2 = 1 :=
    first_parameter_square_odd hpar hA

  obtain ⟨u, v, hAu, hn, hmuSum,
      huv, huvParity, huNonneg⟩ :=
    second_parameterisation hA0 hm hmn hAodd hA

  obtain ⟨w, hw⟩ := even_leg_has_half hB
  have hprod : w ^ 2 = m * u * v :=
    even_leg_square_product hB hn hw

  obtain ⟨huPos, hvPos⟩ :=
    second_parameters_positive
      hB0 hmpos huNonneg hB hn

  obtain ⟨hmu, hmv, huvCop⟩ :=
    second_parameters_pairwise_coprime hmn huv hn

  obtain ⟨t, r, s, ht, hr, hs⟩ :=
    three_square_factors
      hmpos huPos hvPos hmu hmv huvCop hprod

  obtain ⟨hr0, hs0⟩ :=
    new_fourth_square_legs_nonzero huPos hvPos hr hs

  have hrsCop : IsCoprime r s := by
    have hroots : IsCoprime (r ^ 2) (s ^ 2) := by
      simpa only [hr, hs] using huvCop
    exact (IsCoprime.pow_iff
      (by decide : 0 < (2 : ℕ))
      (by decide : 0 < (2 : ℕ))).mp hroots

  have hnew : r ^ 4 + s ^ 4 = t ^ 2 :=
    fourth_square_from_square_parameters hmuSum ht hr hs

  have hsmaller : |t| < |z| :=
    new_hypotenuse_strictly_smaller hmpos hn0 ht hz

  exact ⟨r, s, t, hr0, hs0, hrsCop, hnew, hsmaller⟩

/-- Infinite descent rules out coprime fourth-power-to-square solutions. -/
theorem no_coprime_fourth_square_solution
    {a b z : ℤ}
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hab : IsCoprime a b) :
    a ^ 4 + b ^ 4 ≠ z ^ 2 := by
  have H :
      ∀ N : ℕ, ∀ A B Z : ℤ,
        Z.natAbs = N →
        A ≠ 0 → B ≠ 0 →
        IsCoprime A B →
        A ^ 4 + B ^ 4 = Z ^ 2 → False := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro A B Z hsize hA hB hAB heq

      obtain ⟨r, s, t, hr, hs, hrs, hnew, hlt⟩ :=
        exists_smaller_fourth_square_solution hA hB hAB heq

      have hltNat : t.natAbs < Z.natAbs := by
        have hcast :
            (t.natAbs : ℤ) < (Z.natAbs : ℤ) := by
          simpa only [Int.natCast_natAbs] using hlt
        exact_mod_cast hcast

      have hltN : t.natAbs < N := by omega

      exact ih t.natAbs hltN r s t rfl
        hr hs hrs hnew

  intro heq
  exact H z.natAbs a b z rfl ha hb hab heq

/-- Our integer descent proves FLT for exponent four. -/
theorem fermatLastTheoremFour_via_descent :
    FermatLastTheoremFor 4 := by
  apply fermatLastTheoremFor_iff_int.mpr
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb _hc hgcd heq

  have hab : IsCoprime a b := by
    apply isCoprime_of_prime_dvd
    · rintro ⟨haz, _⟩
      exact ha haz
    · intro p hp hpa hpb

      have pow_dvd : ∀ x : ℤ, p ∣ x → p ∣ x ^ 4 := by
        intro x hx
        obtain ⟨k, hk⟩ := hx
        refine ⟨p ^ 3 * k ^ 4, ?_⟩
        rw [hk]
        ring

      have hpc4 : p ∣ c ^ 4 := by
        rw [← heq]
        exact dvd_add (pow_dvd a hpa) (pow_dvd b hpb)

      have hpc : p ∣ c :=
        hp.dvd_of_dvd_pow hpc4

      have hpgcd : p ∣ Finset.gcd {a, b, c} id := by
        apply Finset.dvd_gcd_iff.mpr
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hpa
        · exact hpb
        · exact hpc

      have hpone : p ∣ (1 : ℤ) := by
        simpa only [hgcd] using hpgcd

      exact hp.not_isUnit (isUnit_of_dvd_one hpone)

  have hsquare : a ^ 4 + b ^ 4 = (c ^ 2) ^ 2 := by
    simpa only [← pow_mul] using heq

  exact no_coprime_fourth_square_solution ha hb hab hsquare

end Hire
