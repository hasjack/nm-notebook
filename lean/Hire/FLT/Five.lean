import Hire.FLT.GoldenRing

namespace Hire
namespace GoldenBridge

/-- Coordinates after multiplying C + D*phi by phi^n. -/
def phiTwistCoordinates : ℕ → ℤ → ℤ → ℤ × ℤ
  | 0, C, D => (C, D)
  | n + 1, C, D =>
      let T := phiTwistCoordinates n C D
      (T.2, T.1 + T.2)

theorem phi_mul_integer_coordinates (C D : ℤ) :
    phi * ((C : G) + (D : G) * phi) =
      (D : G) + ((C + D : ℤ) : G) * phi := by
  push_cast
  linear_combination (D : G) * phi_relation

theorem phi_pow_integer_coordinates
    (n : ℕ) (C D : ℤ) :
    phi ^ n * ((C : G) + (D : G) * phi) =
      ((phiTwistCoordinates n C D).1 : G) +
        ((phiTwistCoordinates n C D).2 : G) * phi := by
  induction n with
  | zero =>
      simp [phiTwistCoordinates]
  | succ n ih =>
      calc
        phi ^ (n + 1) * ((C : G) + (D : G) * phi) =
            phi * (phi ^ n *
              ((C : G) + (D : G) * phi)) := by ring
        _ = phi *
            (((phiTwistCoordinates n C D).1 : G) +
              ((phiTwistCoordinates n C D).2 : G) * phi) := by
          rw [ih]
        _ = ((phiTwistCoordinates n C D).2 : G) +
            (((phiTwistCoordinates n C D).1 +
              (phiTwistCoordinates n C D).2 : ℤ) : G) *
                phi :=
          phi_mul_integer_coordinates
            (phiTwistCoordinates n C D).1
            (phiTwistCoordinates n C D).2
        _ = _ := rfl

/-- Coordinates of any unit twist of a fifth power. -/
theorem twisted_fifth_power_coordinates
    (n : ℕ) (r s : ℤ) :
    phi ^ n * ((r : G) + (s : G) * phi) ^ 5 =
      ((phiTwistCoordinates n
        (fifthConstant r s) (fifthPhiCoeff r s)).1 : G) +
      ((phiTwistCoordinates n
        (fifthConstant r s) (fifthPhiCoeff r s)).2 : G) *
          phi := by
  rw [fifth_power_coordinates]
  exact phi_pow_integer_coordinates n
    (fifthConstant r s) (fifthPhiCoeff r s)

/-- The exceptional golden factor gives explicit integer
coordinate equations in one of five unit cases. -/
theorem exceptional_leftFactor_coordinate_equations
    {a b : ℤ} {Y W : G}
    (hY : leftFactor a b = delta * Y)
    (hA : Associated (W ^ 5) Y) :
    ∃ j : Fin 5, ∃ r s : ℤ,
      a ^ 2 + b ^ 2 =
        -(phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).1 +
        2 * (phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).2 ∧
      -(a * b) =
        2 * (phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).1 +
        (phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).2 := by
  obtain ⟨j, V, hV⟩ :=
    associated_fifth_power_normal_form hA
  obtain ⟨r, s, hcoords⟩ :=
    exists_integer_coordinates V

  let T := phiTwistCoordinates (j : ℕ)
    (fifthConstant r s) (fifthPhiCoeff r s)

  have heq :
      ((a ^ 2 + b ^ 2 : ℤ) : G) +
          ((-(a * b) : ℤ) : G) * phi =
        ((-T.1 + 2 * T.2 : ℤ) : G) +
          ((2 * T.1 + T.2 : ℤ) : G) * phi := by
    calc
      _ = leftFactor a b := by
        unfold leftFactor
        push_cast
        ring
      _ = delta * Y := hY
      _ = delta *
          (phi ^ (j : ℕ) *
            ((r : G) + (s : G) * phi) ^ 5) := by
        rw [hV, hcoords]
      _ = delta * ((T.1 : G) + (T.2 : G) * phi) := by
        rw [twisted_fifth_power_coordinates]
      _ = _ := delta_mul_coordinates T.1 T.2

  have hpair := integer_coordinates_eq heq
  exact ⟨j, r, s, hpair.1, hpair.2⟩

/-- The coordinate equations identify the square of a+b. -/
theorem exceptional_coordinates_sum_square
    {a b C D : ℤ}
    (hconstant : a ^ 2 + b ^ 2 = -C + 2 * D)
    (hphi : -(a * b) = 2 * C + D) :
    (a + b) ^ 2 = -5 * C := by
  nlinarith [hconstant, hphi]

/-- If 625 divides a+b, the constant coordinate is divisible by 5^7. -/
theorem exceptional_constant_dvd_five_pow_seven
    {a b C D : ℤ}
    (hS : (625 : ℤ) ∣ a + b)
    (hconstant : a ^ 2 + b ^ 2 = -C + 2 * D)
    (hphi : -(a * b) = 2 * C + D) :
    (5 ^ 7 : ℤ) ∣ C := by
  have hsquare :=
    exceptional_coordinates_sum_square hconstant hphi
  obtain ⟨t, ht⟩ := hS
  rw [ht] at hsquare
  refine ⟨-(t ^ 2), ?_⟩
  nlinarith [hsquare]

/-- Only twist 1 can have a constant coordinate divisible by 5 while its golden residue remains nonzero. -/
theorem exceptional_twist_index_eq_one
    {j : Fin 5} {C D : ℤ}
    (hD : (5 : ℤ) ∣ D)
    (hconstant :
      (5 : ℤ) ∣ (phiTwistCoordinates (j : ℕ) C D).1)
    (hfree :
      ¬ (5 : ℤ) ∣
        (phiTwistCoordinates (j : ℕ) C D).1 +
          3 * (phiTwistCoordinates (j : ℕ) C D).2) :
    j = 1 := by
  fin_cases j
  all_goals
    norm_num [phiTwistCoordinates] at hconstant hfree ⊢
  all_goals
    exfalso
    apply hfree
    rw [Int.dvd_iff_emod_eq_zero] at hD hconstant ⊢
    omega

/-- A delta-free exceptional quotient with constant coordinate divisible by 5 must have unit twist phi. -/
theorem exceptional_fifth_power_twist_eq_one
    {j : Fin 5} {r s : ℤ} {Y : G}
    (hY :
      Y = phi ^ (j : ℕ) *
        ((r : G) + (s : G) * phi) ^ 5)
    (hYfree : ¬ delta ∣ Y)
    (hconstant :
      (5 : ℤ) ∣
        (phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).1) :
    j = 1 := by
  let T := phiTwistCoordinates (j : ℕ)
    (fifthConstant r s) (fifthPhiCoeff r s)

  have hfree : ¬ (5 : ℤ) ∣ T.1 + 3 * T.2 := by
    intro hd
    apply hYfree
    apply (goldenResidue_eq_zero_iff Y).mp
    rw [hY, twisted_fifth_power_coordinates,
      goldenResidue_coordinates]

    have hz : ((T.1 + 3 * T.2 : ℤ) : ZMod 5) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hd

    push_cast at hz
    simpa only [mul_comm] using hz

  exact exceptional_twist_index_eq_one
    (five_dvd_fifthPhiCoeff r s) hconstant hfree

/-- The quartic factor in the phi coefficient of a fifth power. -/
def fifthSquareFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4

theorem fifthPhiCoeff_factor (r s : ℤ) :
    fifthPhiCoeff r s = 5 * s * fifthSquareFactor r s := by
  unfold fifthPhiCoeff fifthSquareFactor
  ring

/-- In unit twist 1, the exceptional coordinate equations give a product that is a square. -/
theorem exceptional_twist_one_square_equation
    {a b r s t : ℤ}
    (hS : a + b = 5 * t)
    (hconstant :
      a ^ 2 + b ^ 2 =
        -fifthPhiCoeff r s +
          2 * (fifthConstant r s + fifthPhiCoeff r s))
    (hphi :
      -(a * b) =
        2 * fifthPhiCoeff r s +
          (fifthConstant r s + fifthPhiCoeff r s)) :
    t ^ 2 = -s * fifthSquareFactor r s := by
  have hsquare :=
    exceptional_coordinates_sum_square hconstant hphi
  rw [hS, fifthPhiCoeff_factor] at hsquare
  nlinarith [hsquare]

/-- For coprime coordinates, s and the quartic factor are coprime as well. -/
theorem fifthSquareFactor_coprime
    {r s : ℤ}
    (hrs : IsCoprime r s) :
    IsCoprime s (fifthSquareFactor r s) := by
  have hpow : IsCoprime s (r ^ 4) :=
    hrs.symm.pow_right

  have hrel : IsRelPrime s (fifthSquareFactor r s) := by
    intro d hds hdF

    have hmultiple :
        d ∣ s *
          (2 * r ^ 3 + 4 * r ^ 2 * s +
            3 * r * s ^ 2 + s ^ 3) :=
      dvd_mul_of_dvd_left hds _

    have hidentity :
        fifthSquareFactor r s -
          s * (2 * r ^ 3 + 4 * r ^ 2 * s +
            3 * r * s ^ 2 + s ^ 3) =
          r ^ 4 := by
      unfold fifthSquareFactor
      ring

    have hdr : d ∣ r ^ 4 := by
      have h := dvd_sub hdF hmultiple
      rw [hidentity] at h
      exact h

    exact hpow.isUnit_of_dvd' hds hdr

  exact hrel.isCoprime

/-- A sum-of-squares expression for the quartic factor. -/
theorem four_mul_fifthSquareFactor (r s : ℤ) :
    4 * fifthSquareFactor r s =
      (2 * r ^ 2 + 2 * r * s + s ^ 2) ^ 2 +
        2 * (s * (2 * r + s)) ^ 2 + (s ^ 2) ^ 2 := by
  unfold fifthSquareFactor
  ring

theorem fifthSquareFactor_nonneg (r s : ℤ) :
    0 ≤ fifthSquareFactor r s := by
  have h := four_mul_fifthSquareFactor r s
  nlinarith [
    sq_nonneg (2 * r ^ 2 + 2 * r * s + s ^ 2),
    sq_nonneg (s * (2 * r + s)),
    sq_nonneg (s ^ 2)]

/-- Coprime inputs make a²+b² and ab coprime. -/
theorem sum_squares_coprime_product
    {a b : ℤ}
    (hab : IsCoprime a b) :
    IsCoprime (a ^ 2 + b ^ 2) (a * b) := by
  obtain ⟨u, v, huv⟩ := hab

  refine ⟨u ^ 4 * a ^ 2 + v ^ 4 * b ^ 2,
    4 * u ^ 3 * v * a ^ 2 +
      (6 * u ^ 2 * v ^ 2 - u ^ 4 - v ^ 4) * a * b +
      4 * u * v ^ 3 * b ^ 2, ?_⟩

  calc
    _ = (u * a + v * b) ^ 4 := by ring
    _ = 1 := by simp only [huv, one_pow]

/-- A common coordinate divisor divides both fifth-power coefficients. -/
theorem common_dvd_fifth_coordinates
    {r s d : ℤ}
    (hdr : d ∣ r)
    (hds : d ∣ s) :
    d ∣ fifthConstant r s ∧ d ∣ fifthPhiCoeff r s := by
  obtain ⟨x, hx⟩ := hdr
  obtain ⟨y, hy⟩ := hds

  constructor
  · refine ⟨d ^ 4 * fifthConstant x y, ?_⟩
    rw [hx, hy]
    unfold fifthConstant
    ring
  · refine ⟨d ^ 4 * fifthPhiCoeff x y, ?_⟩
    rw [hx, hy]
    unfold fifthPhiCoeff
    ring

/-- Multiplication by powers of phi preserves a common integer divisor of the coordinates. -/
theorem common_dvd_phiTwistCoordinates
    (n : ℕ) {C D d : ℤ}
    (hC : d ∣ C)
    (hD : d ∣ D) :
    d ∣ (phiTwistCoordinates n C D).1 ∧
      d ∣ (phiTwistCoordinates n C D).2 := by
  induction n with
  | zero =>
      exact ⟨hC, hD⟩
  | succ n ih =>
      exact ⟨ih.2, dvd_add ih.1 ih.2⟩

/-- Coprimality of a,b forces coprimality of the extracted fifth-power coordinates, in every unit twist. -/
theorem exceptional_fifth_coordinates_coprime
    {a b r s : ℤ} {j : Fin 5}
    (hab : IsCoprime a b)
    (hconstant :
      a ^ 2 + b ^ 2 =
        -(phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).1 +
        2 * (phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).2)
    (hphi :
      -(a * b) =
        2 * (phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).1 +
        (phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).2) :
    IsCoprime r s := by
  have habFactors := sum_squares_coprime_product hab

  have hrel : IsRelPrime r s := by
    intro d hdr hds

    obtain ⟨hC, hD⟩ :=
      common_dvd_fifth_coordinates hdr hds

    obtain ⟨hTconstant, hTphi⟩ :=
      common_dvd_phiTwistCoordinates (j : ℕ) hC hD

    have hdSum : d ∣ a ^ 2 + b ^ 2 := by
      rw [hconstant]
      exact dvd_add
        (dvd_neg.mpr hTconstant)
        (dvd_mul_of_dvd_right hTphi 2)

    have hdNegProduct : d ∣ -(a * b) := by
      rw [hphi]
      exact dvd_add
        (dvd_mul_of_dvd_right hTconstant 2)
        hTphi

    have hdProduct : d ∣ a * b :=
      dvd_neg.mp hdNegProduct

    exact habFactors.isUnit_of_dvd' hdSum hdProduct

  exact hrel.isCoprime

theorem fifthSquareFactor_pos
    {r s : ℤ}
    (hne : r ≠ 0 ∨ s ≠ 0) :
    0 < fifthSquareFactor r s := by
  by_cases hs : s = 0
  · have hr : r ≠ 0 := by
      rcases hne with hr | hsne
      · exact hr
      · exact False.elim (hsne hs)
    have hp : 0 < r ^ 4 := by positivity
    simpa [fifthSquareFactor, hs] using hp
  · have hp : 0 < (s ^ 2) ^ 2 := by positivity
    have h := four_mul_fifthSquareFactor r s
    nlinarith [
      sq_nonneg (2 * r ^ 2 + 2 * r * s + s ^ 2),
      sq_nonneg (s * (2 * r + s))]

/-- A nonnegative integer associated to a square is a square. -/
theorem nonneg_eq_square_of_associated_square
    {A w : ℤ}
    (hA : 0 ≤ A)
    (hassoc : Associated (w ^ 2) A) :
    ∃ x : ℤ, A = x ^ 2 := by
  obtain ⟨e, he⟩ := hassoc
  rcases Int.units_eq_one_or e with heOne | heNeg
  · refine ⟨w, ?_⟩
    simpa [heOne] using he.symm
  · have hnegative : A = -(w ^ 2) := by
      simpa [heNeg] using he.symm
    have hzero : A = 0 := by
      nlinarith [sq_nonneg w]
    refine ⟨0, ?_⟩
    simpa using hzero

/-- Coprime coordinates and the exceptional square equation
force both remaining factors to be squares. -/
theorem exceptional_square_factors
    {r s t : ℤ}
    (hrs : IsCoprime r s)
    (hsquare : t ^ 2 = -s * fifthSquareFactor r s) :
    ∃ x y : ℤ,
      -s = x ^ 2 ∧ fifthSquareFactor r s = y ^ 2 := by
  have hne : r ≠ 0 ∨ s ≠ 0 := by
    by_cases hr : r = 0
    · right
      intro hs
      obtain ⟨u, v, huv⟩ := hrs
      norm_num [hr, hs] at huv
    · exact Or.inl hr

  have hpositive : 0 < fifthSquareFactor r s :=
    fifthSquareFactor_pos hne

  have hsnonneg : 0 ≤ -s := by
    by_contra h
    have hspos : 0 < s := by omega
    have hproduct : 0 < s * fifthSquareFactor r s :=
      mul_pos hspos hpositive
    nlinarith [hsquare, sq_nonneg t]

  have hcop : IsCoprime (-s) (fifthSquareFactor r s) := by
    obtain ⟨u, v, huv⟩ := fifthSquareFactor_coprime hrs
    refine ⟨-u, v, ?_⟩
    calc
      (-u) * (-s) + v * fifthSquareFactor r s =
          u * s + v * fifthSquareFactor r s := by ring
      _ = 1 := huv

  have hproduct :
      (-s) * fifthSquareFactor r s = t ^ 2 :=
    hsquare.symm

  obtain ⟨w, hw⟩ :=
    exists_associated_pow_of_mul_eq_pow' hcop hproduct
  obtain ⟨z, hz⟩ :=
    exists_associated_pow_of_mul_eq_pow'
      hcop.symm (by simpa only [mul_comm] using hproduct)

  obtain ⟨x, hx⟩ :=
    nonneg_eq_square_of_associated_square hsnonneg hw
  obtain ⟨y, hy⟩ :=
    nonneg_eq_square_of_associated_square
      (le_of_lt hpositive) hz

  exact ⟨x, y, hx, hy⟩

/-- Modulo 5, the quartic factor is a fourth power. -/
theorem five_dvd_fifthSquareFactor_sub_fourth (r s : ℤ) :
    (5 : ℤ) ∣ fifthSquareFactor r s - (r + 3 * s) ^ 4 := by
  refine ⟨-2 * r ^ 3 * s - 10 * r ^ 2 * s ^ 2 -
    21 * r * s ^ 3 - 16 * s ^ 4, ?_⟩
  unfold fifthSquareFactor
  ring

/-- A nonzero golden residue makes the quartic factor 5-free. -/
theorem five_not_dvd_fifthSquareFactor
    {r s : ℤ}
    (hfree : ¬ (5 : ℤ) ∣ r + 3 * s) :
    ¬ (5 : ℤ) ∣ fifthSquareFactor r s := by
  intro hH
  have hfourth : (5 : ℤ) ∣ (r + 3 * s) ^ 4 := by
    have h := dvd_sub hH
      (five_dvd_fifthSquareFactor_sub_fourth r s)
    simpa only [sub_sub_cancel] using h

  have hprime : Prime (5 : ℤ) := by norm_num
  exact hfree (hprime.dvd_of_dvd_pow hfourth)

/-- The exceptional sum forces six factors of 5 into s, because the quartic factor is 5-free. -/
theorem five_pow_six_dvd_exceptional_coordinate
    {a b r s u : ℤ}
    (hS : a + b = 625 * u ^ 5)
    (hconstant :
      a ^ 2 + b ^ 2 =
        -fifthPhiCoeff r s +
          2 * (fifthConstant r s + fifthPhiCoeff r s))
    (hphi :
      -(a * b) =
        2 * fifthPhiCoeff r s +
          (fifthConstant r s + fifthPhiCoeff r s))
    (hfree : ¬ (5 : ℤ) ∣ r + 3 * s) :
    (5 ^ 6 : ℤ) ∣ s := by
  have hsquare :=
    exceptional_coordinates_sum_square hconstant hphi
  rw [hS, fifthPhiCoeff_factor] at hsquare

  have hproduct :
      (5 ^ 6 : ℤ) ∣ s * fifthSquareFactor r s := by
    refine ⟨-(u ^ 10), ?_⟩
    nlinarith [hsquare]

  have hprime : Prime (5 : ℤ) := by norm_num
  have hcopFive : IsCoprime (5 : ℤ) (fifthSquareFactor r s) :=
    hprime.coprime_iff_not_dvd.mpr
      (five_not_dvd_fifthSquareFactor hfree)

  have hcop :
      IsCoprime (5 ^ 6 : ℤ) (fifthSquareFactor r s) :=
    hcopFive.pow_left

  exact hcop.dvd_of_dvd_mul_right hproduct

/-- Six factors of 5 in an integer square force
three factors of 5 in its square root. -/
theorem dvd_125_of_five_pow_six_dvd_square
    {x : ℤ}
    (hdiv : (5 ^ 6 : ℤ) ∣ x ^ 2) :
    (125 : ℤ) ∣ x := by
  have hprime : Prime (5 : ℤ) := by norm_num

  have hxFive : (5 : ℤ) ∣ x := by
    apply hprime.dvd_of_dvd_pow
    exact dvd_trans
      (by norm_num : (5 : ℤ) ∣ (5 ^ 6 : ℤ)) hdiv

  obtain ⟨y, hy⟩ := hxFive
  obtain ⟨k, hk⟩ := hdiv

  have hySquare : (5 ^ 4 : ℤ) ∣ y ^ 2 := by
    refine ⟨k, ?_⟩
    rw [hy] at hk
    nlinarith [hk]

  have hyFive : (5 : ℤ) ∣ y := by
    apply hprime.dvd_of_dvd_pow
    exact dvd_trans
      (by norm_num : (5 : ℤ) ∣ (5 ^ 4 : ℤ)) hySquare

  obtain ⟨z, hz⟩ := hyFive
  obtain ⟨l, hl⟩ := hySquare

  have hzSquare : (5 ^ 2 : ℤ) ∣ z ^ 2 := by
    refine ⟨l, ?_⟩
    rw [hz] at hl
    nlinarith [hl]

  have hzFive : (5 : ℤ) ∣ z := by
    apply hprime.dvd_of_dvd_pow
    exact dvd_trans
      (by norm_num : (5 : ℤ) ∣ (5 ^ 2 : ℤ)) hzSquare

  obtain ⟨w, hw⟩ := hzFive
  refine ⟨w, ?_⟩
  rw [hy, hz, hw]
  ring

/-- Apply the square-root restriction when -s is a square. -/
theorem exceptional_square_root_dvd_125
    {s x : ℤ}
    (hs : (5 ^ 6 : ℤ) ∣ s)
    (hx : -s = x ^ 2) :
    (125 : ℤ) ∣ x := by
  apply dvd_125_of_five_pow_six_dvd_square
  rw [← hx]
  exact dvd_neg.mpr hs

/-- The quartic that reproduces the auxiliary norm equation. -/
def descentNormFactor (c d : ℤ) : ℤ :=
  c ^ 4 + 10 * c ^ 2 * d ^ 2 + 5 * d ^ 4

/-- Fifth-power coordinates in the basis 1, delta,
where delta² = 5. -/
theorem sqrtFive_fifth_power_coordinates (c d : ℤ) :
    ((c : G) + (d : G) * delta) ^ 5 =
      ((c * (c ^ 4 + 50 * c ^ 2 * d ^ 2 +
        125 * d ^ 4) : ℤ) : G) +
      ((5 * d * descentNormFactor c d : ℤ) : G) *
        delta := by
  unfold descentNormFactor
  push_cast
  linear_combination
    (10 * (c : G) ^ 3 * (d : G) ^ 2 +
      10 * (c : G) ^ 2 * (d : G) ^ 3 * delta +
      5 * (c : G) * (d : G) ^ 4 * (delta ^ 2 + 5) +
      (d : G) ^ 5 * delta * (delta ^ 2 + 5)) *
        delta_sq

/-- The auxiliary quartic is bounded below by 5d⁴. -/
theorem descentNormFactor_lower_bound (c d : ℤ) :
    5 * d ^ 4 ≤ descentNormFactor c d := by
  have hc : 0 ≤ c ^ 4 := by positivity
  have hcross : 0 ≤ 10 * c ^ 2 * d ^ 2 := by positivity
  unfold descentNormFactor
  nlinarith [hc, hcross]

/-- The proposed new coefficient is strictly smaller
than the old coefficient. -/
theorem descent_coefficient_strictly_decreases
    {c d : ℤ}
    (hd : 0 < d) :
    2 * d ^ 2 < 5 * d * descentNormFactor c d := by
  have hdOne : 1 ≤ d := by omega

  have hdSquare : d ≤ d ^ 2 := by
    have h := mul_nonneg
      (le_of_lt hd) (show 0 ≤ d - 1 by omega)
    nlinarith [h]

  have hdFourth : d ^ 2 ≤ d ^ 4 := by
    have h := mul_nonneg
      (sq_nonneg d) (show 0 ≤ d ^ 2 - 1 by nlinarith)
    nlinarith [h]

  have hfactor : d ≤ descentNormFactor c d := by
    have h := descentNormFactor_lower_bound c d
    nlinarith [h, hdSquare, hdFourth]

  have hproduct :
      0 ≤ d * (descentNormFactor c d - d) :=
    mul_nonneg (le_of_lt hd) (by omega)

  have hdPositiveSquare : 0 < d ^ 2 := by positivity
  nlinarith [hproduct, hdPositiveSquare]

/-- The proposed smaller pair has the required norm. -/
theorem descentNormFactor_identity (c d : ℤ) :
    (c ^ 2 + 5 * d ^ 2) ^ 2 - 5 * (2 * d ^ 2) ^ 2 =
      descentNormFactor c d := by
  unfold descentNormFactor
  ring

/-- The coefficient after extracting d = 80w^5 again has the form 400 times a fifth power. -/
theorem descent_coefficient_shape (w : ℤ) :
    2 * (80 * w ^ 5) ^ 2 =
      400 * (2 * w ^ 2) ^ 5 := by
  ring

/-- The new first coordinate is coprime to d². -/
theorem descent_new_first_coprime_square
    {c d : ℤ}
    (hcd : IsCoprime c d) :
    IsCoprime (c ^ 2 + 5 * d ^ 2) (d ^ 2) := by
  have hleft : IsCoprime (c ^ 2) d :=
    hcd.pow_left
  have hboth : IsCoprime (c ^ 2) (d ^ 2) :=
    hleft.pow_right
  exact hboth.add_mul_right_left 5

/-- Odd c and even d make the new first coordinate odd. -/
theorem descent_new_first_odd
    {c d : ℤ}
    (hc : Odd c)
    (hd : Even d) :
    Odd (c ^ 2 + 5 * d ^ 2) := by
  obtain ⟨k, hk⟩ := hc
  obtain ⟨l, hl⟩ := hd
  refine ⟨2 * k ^ 2 + 2 * k + 10 * l ^ 2, ?_⟩
  rw [hk, hl]
  ring

/-- The smaller auxiliary pair is coprime. -/
theorem descent_new_pair_coprime
    {c d : ℤ}
    (hcd : IsCoprime c d)
    (hc : Odd c)
    (hd : Even d) :
    IsCoprime (c ^ 2 + 5 * d ^ 2) (2 * d ^ 2) := by
  have htwo : IsCoprime (c ^ 2 + 5 * d ^ 2) 2 :=
    (descent_new_first_odd hc hd).isCoprime_two
  have hsquare :=
    descent_new_first_coprime_square hcd
  exact htwo.mul_right hsquare

/-- The new second coordinate is even. -/
theorem descent_new_second_even (d : ℤ) :
    Even (2 * d ^ 2) := by
  refine ⟨d ^ 2, ?_⟩
  ring

/-- Coprime c,d make the auxiliary quartic coprime to d. -/
theorem descentNormFactor_coprime_coordinate
    {c d : ℤ}
    (hcd : IsCoprime c d) :
    IsCoprime (descentNormFactor c d) d := by
  have hpower : IsCoprime (c ^ 4) d :=
    hcd.pow_left

  have hidentity :
      descentNormFactor c d =
        c ^ 4 + d * (10 * c ^ 2 * d + 5 * d ^ 3) := by
    unfold descentNormFactor
    ring

  rw [hidentity]
  exact hpower.add_mul_left_left _

theorem descentNormFactor_odd
    {c d : ℤ}
    (hc : Odd c)
    (hd : Even d) :
    Odd (descentNormFactor c d) := by
  obtain ⟨k, hk⟩ := hc
  obtain ⟨l, hl⟩ := hd
  refine ⟨8 * k ^ 4 + 16 * k ^ 3 + 12 * k ^ 2 +
    4 * k + 20 * c ^ 2 * l ^ 2 + 40 * l ^ 4, ?_⟩
  unfold descentNormFactor
  rw [hk, hl]
  ring

theorem five_not_dvd_descentNormFactor
    {c d : ℤ}
    (hc : ¬ (5 : ℤ) ∣ c) :
    ¬ (5 : ℤ) ∣ descentNormFactor c d := by
  intro hK

  have hmultiple :
      (5 : ℤ) ∣ 5 * (2 * c ^ 2 * d ^ 2 + d ^ 4) :=
    dvd_mul_right 5 _

  have hidentity :
      descentNormFactor c d -
        5 * (2 * c ^ 2 * d ^ 2 + d ^ 4) = c ^ 4 := by
    unfold descentNormFactor
    ring

  have hcFourth : (5 : ℤ) ∣ c ^ 4 := by
    have h := dvd_sub hK hmultiple
    rw [hidentity] at h
    exact h

  have hprime : Prime (5 : ℤ) := by norm_num
  exact hc (hprime.dvd_of_dvd_pow hcFourth)

theorem descentNormFactor_coprime_eighty
    {c d : ℤ}
    (hcOdd : Odd c)
    (hdEven : Even d)
    (hcFive : ¬ (5 : ℤ) ∣ c) :
    IsCoprime (descentNormFactor c d) 80 := by
  have htwo : IsCoprime (descentNormFactor c d) 2 :=
    (descentNormFactor_odd hcOdd hdEven).isCoprime_two

  have hprime : Prime (5 : ℤ) := by norm_num
  have hfive : IsCoprime (descentNormFactor c d) 5 :=
    (hprime.coprime_iff_not_dvd.mpr
      (five_not_dvd_descentNormFactor hcFive)).symm

  have hsixteen :
      IsCoprime (descentNormFactor c d) (2 ^ 4 : ℤ) :=
    htwo.pow_right

  have h := hsixteen.mul_right hfive
  norm_num at h
  exact h

/-- Allocate the exceptional factor 80 to d,
then extract both remaining fifth powers. -/
theorem descent_fifth_power_allocation
    {c d t : ℤ}
    (hcd : IsCoprime c d)
    (hcOdd : Odd c)
    (hdEven : Even d)
    (hcFive : ¬ (5 : ℤ) ∣ c)
    (hproduct :
      d * descentNormFactor c d = 80 * t ^ 5) :
    ∃ w v : ℤ,
      d = 80 * w ^ 5 ∧ descentNormFactor c d = v ^ 5 := by
  have hK80 :=
    descentNormFactor_coprime_eighty hcOdd hdEven hcFive

  have hdK : IsCoprime d (descentNormFactor c d) :=
    (descentNormFactor_coprime_coordinate hcd).symm

  have hdivProduct :
      (80 : ℤ) ∣ d * descentNormFactor c d := by
    rw [hproduct]
    exact dvd_mul_right 80 (t ^ 5)

  have hdivD : (80 : ℤ) ∣ d :=
    hK80.symm.dvd_of_dvd_mul_right hdivProduct

  obtain ⟨e, he⟩ := hdivD

  have hed : e ∣ d := by
    refine ⟨80, ?_⟩
    rw [he]
    ring

  have heK : IsCoprime e (descentNormFactor c d) :=
    hdK.of_isCoprime_of_dvd_left hed

  have hremaining :
      e * descentNormFactor c d = t ^ 5 := by
    have hscaled :
        80 * (e * descentNormFactor c d) =
          80 * t ^ 5 := by
      calc
        80 * (e * descentNormFactor c d) =
            (80 * e) * descentNormFactor c d := by ring
        _ = d * descentNormFactor c d := by rw [← he]
        _ = 80 * t ^ 5 := hproduct
    nlinarith [hscaled]

  obtain ⟨w, hw⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      heK (by decide : Odd (5 : ℕ)) hremaining

  obtain ⟨v, hv⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_right
      heK (by decide : Odd (5 : ℕ)) hremaining

  refine ⟨w, v, ?_, hv⟩
  rw [he, hw]

/-- The auxiliary norm equation used by this descent branch. -/
structure FifthNormSolution where
  A : ℤ
  B : ℤ
  t : ℤ
  v : ℤ
  coprime : IsCoprime A B
  odd_first : Odd A
  even_second : Even B
  coefficient : B = 400 * t ^ 5
  positive_second : 0 < B
  norm_eq : A ^ 2 - 5 * B ^ 2 = v ^ 5

/-- The extracted root produces a smaller auxiliary solution.
The root-extraction hypotheses are explicit here. -/
theorem fifthNormSolution_descent_of_root
    (S : FifthNormSolution)
    {c d : ℤ}
    (hcd : IsCoprime c d)
    (hcOdd : Odd c)
    (hdEven : Even d)
    (hcFive : ¬ (5 : ℤ) ∣ c)
    (hdPositive : 0 < d)
    (hB : S.B = 5 * d * descentNormFactor c d) :
    ∃ S' : FifthNormSolution, S'.B < S.B := by
  have hproduct :
      d * descentNormFactor c d = 80 * S.t ^ 5 := by
    have hcoefficient := S.coefficient
    nlinarith [hB, hcoefficient]

  obtain ⟨w, v, hd, hK⟩ :=
    descent_fifth_power_allocation
      hcd hcOdd hdEven hcFive hproduct

  let S' : FifthNormSolution :=
    { A := c ^ 2 + 5 * d ^ 2
      B := 2 * d ^ 2
      t := 2 * w ^ 2
      v := v
      coprime :=
        descent_new_pair_coprime hcd hcOdd hdEven
      odd_first :=
        descent_new_first_odd hcOdd hdEven
      even_second :=
        descent_new_second_even d
      coefficient := by
        rw [hd]
        exact descent_coefficient_shape w
      positive_second := by
        positivity
      norm_eq := by
        rw [descentNormFactor_identity, hK] }

  refine ⟨S', ?_⟩
  change 2 * d ^ 2 < S.B
  rw [hB]
  exact descent_coefficient_strictly_decreases hdPositive

/-- The factor A + B*sqrt(5), expressed using delta. -/
noncomputable def sqrtFiveFactor (A B : ℤ) : G :=
  (A : G) + (B : G) * delta

theorem sqrtFiveFactor_mul_conjugate (A B : ℤ) :
    sqrtFiveFactor A B * sqrtFiveFactor A (-B) =
      ((A ^ 2 - 5 * B ^ 2 : ℤ) : G) := by
  unfold sqrtFiveFactor
  push_cast
  linear_combination -(B : G) ^ 2 * delta_sq

/-- Opposite parity excludes the factor 2. -/
theorem sqrtFiveFactor_coprime_two
    {A B : ℤ}
    (hA : Odd A)
    (hB : Even B) :
    IsCoprime (sqrtFiveFactor A B) 2 := by
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  refine ⟨1, -((k : G) + (l : G) * delta), ?_⟩
  unfold sqrtFiveFactor
  rw [hk, hl]
  push_cast
  ring

/-- A 5-free first coordinate excludes delta. -/
theorem sqrtFiveFactor_coprime_delta
    {A B : ℤ}
    (hA : ¬ (5 : ℤ) ∣ A) :
    IsCoprime (sqrtFiveFactor A B) delta := by
  have hfree : ¬ delta ∣ sqrtFiveFactor A B := by
    intro hd
    have hz :=
      (goldenResidue_eq_zero_iff (sqrtFiveFactor A B)).mpr hd
    have hcast : (A : ZMod 5) = 0 := by
      simpa [sqrtFiveFactor, goldenResidue_delta] using hz
    have hdiv : (5 : ℤ) ∣ A := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast
    exact hA hdiv

  exact (delta_prime.coprime_iff_not_dvd.mpr hfree).symm

/-- The conjugate norm factors are coprime under the auxiliary solution's arithmetic conditions. -/
theorem sqrtFiveFactor_conjugates_coprime
    {A B : ℤ}
    (hab : IsCoprime A B)
    (hAodd : Odd A)
    (hBeven : Even B)
    (hAfive : ¬ (5 : ℤ) ∣ A) :
    IsCoprime (sqrtFiveFactor A B)
      (sqrtFiveFactor A (-B)) := by
  have hcop :
      IsCoprime (sqrtFiveFactor A B) (2 * delta) :=
    (sqrtFiveFactor_coprime_two hAodd hBeven).mul_right
      (sqrtFiveFactor_coprime_delta hAfive)

  obtain ⟨u, v, huv⟩ := hab

  have hbez :
      (u : G) * (A : G) + (v : G) * (B : G) = 1 := by
    have h := congrArg (fun z : ℤ => (z : G)) huv
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using h

  have hrel :
      IsRelPrime (sqrtFiveFactor A B)
        (sqrtFiveFactor A (-B)) := by
    intro e hePlus heMinus

    have heSum : e ∣ 2 * (A : G) := by
      have h := dvd_add hePlus heMinus
      have heq :
          sqrtFiveFactor A B + sqrtFiveFactor A (-B) =
            2 * (A : G) := by
        unfold sqrtFiveFactor
        push_cast
        ring
      rwa [heq] at h

    have heDiff : e ∣ 2 * (B : G) * delta := by
      have h := dvd_sub hePlus heMinus
      have heq :
          sqrtFiveFactor A B - sqrtFiveFactor A (-B) =
            2 * (B : G) * delta := by
        unfold sqrtFiveFactor
        push_cast
        ring
      rwa [heq] at h

    have heExceptional : e ∣ 2 * delta := by
      have h :
          e ∣ (u : G) * delta * (2 * (A : G)) +
            (v : G) * (2 * (B : G) * delta) :=
        dvd_add
          (dvd_mul_of_dvd_right heSum ((u : G) * delta))
          (dvd_mul_of_dvd_right heDiff (v : G))

      have heq :
          (u : G) * delta * (2 * (A : G)) +
            (v : G) * (2 * (B : G) * delta) =
              2 * delta := by
        calc
          _ = 2 * delta *
              ((u : G) * (A : G) +
                (v : G) * (B : G)) := by ring
          _ = 2 * delta := by simp only [hbez, mul_one]

      rwa [heq] at h

    exact hcop.isUnit_of_dvd' hePlus heExceptional

  exact hrel.isCoprime

theorem fifthNormSolution_five_not_dvd_first
    (S : FifthNormSolution) :
    ¬ (5 : ℤ) ∣ S.A := by
  intro hA

  have hB : (5 : ℤ) ∣ S.B := by
    rw [S.coefficient]
    exact dvd_mul_of_dvd_left
      (by norm_num : (5 : ℤ) ∣ 400) (S.t ^ 5)

  obtain ⟨u, v, huv⟩ := S.coprime

  have hone : (5 : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add
      (dvd_mul_of_dvd_right hA u)
      (dvd_mul_of_dvd_right hB v)

  norm_num at hone

/-- A coefficient divisible by 5 and a nonzero residue force unit twist 0. -/
theorem norm_twist_index_eq_zero
    {j : Fin 5} {C D : ℤ}
    (hD : (5 : ℤ) ∣ D)
    (hcoefficient :
      (5 : ℤ) ∣ (phiTwistCoordinates (j : ℕ) C D).2)
    (hfree :
      ¬ (5 : ℤ) ∣
        (phiTwistCoordinates (j : ℕ) C D).1 +
          3 * (phiTwistCoordinates (j : ℕ) C D).2) :
    j = 0 := by
  fin_cases j
  all_goals
    norm_num [phiTwistCoordinates] at hcoefficient hfree ⊢
  all_goals
    exfalso
    apply hfree
    rw [Int.dvd_iff_emod_eq_zero] at hD hcoefficient ⊢
    omega

/-- Coprime conjugate factors allow fifth-power extraction. -/
theorem fifthNormSolution_factor_associated
    (S : FifthNormSolution) :
    ∃ W : G, Associated (W ^ 5) (sqrtFiveFactor S.A S.B) := by
  have hcop :=
    sqrtFiveFactor_conjugates_coprime
      S.coprime S.odd_first S.even_second
      (fifthNormSolution_five_not_dvd_first S)

  have hproduct :
      sqrtFiveFactor S.A S.B *
        sqrtFiveFactor S.A (-S.B) = (S.v : G) ^ 5 := by
    rw [sqrtFiveFactor_mul_conjugate, S.norm_eq]
    push_cast
    rfl

  exact exists_associated_pow_of_mul_eq_pow' hcop hproduct

/-- The auxiliary factor is a genuine fifth power,
rather than merely associated to one. -/
theorem fifthNormSolution_factor_is_fifth_power
    (S : FifthNormSolution) :
    ∃ V : G, sqrtFiveFactor S.A S.B = V ^ 5 := by
  obtain ⟨W, hW⟩ := fifthNormSolution_factor_associated S
  obtain ⟨j, V, hV⟩ := associated_fifth_power_normal_form hW
  obtain ⟨r, s, hcoords⟩ := exists_integer_coordinates V

  let T := phiTwistCoordinates (j : ℕ)
    (fifthConstant r s) (fifthPhiCoeff r s)

  have heq :
      ((S.A - S.B : ℤ) : G) +
          ((2 * S.B : ℤ) : G) * phi =
        (T.1 : G) + (T.2 : G) * phi := by
    calc
      _ = sqrtFiveFactor S.A S.B := by
        unfold sqrtFiveFactor delta
        push_cast
        ring
      _ = phi ^ (j : ℕ) *
          ((r : G) + (s : G) * phi) ^ 5 := by
        rw [hV, hcoords]
      _ = _ := twisted_fifth_power_coordinates (j : ℕ) r s

  have hpair := integer_coordinates_eq heq

  have hBfive : (5 : ℤ) ∣ S.B := by
    rw [S.coefficient]
    exact dvd_mul_of_dvd_left
      (by norm_num : (5 : ℤ) ∣ 400) (S.t ^ 5)

  have hcoefficient : (5 : ℤ) ∣ T.2 := by
    rw [← hpair.2]
    exact dvd_mul_of_dvd_right hBfive 2

  have hfree : ¬ (5 : ℤ) ∣ T.1 + 3 * T.2 := by
    intro hd

    have hmultiple : (5 : ℤ) ∣ 5 * S.B :=
      dvd_mul_right 5 S.B

    have hidentity : T.1 + 3 * T.2 - 5 * S.B = S.A := by
      nlinarith [hpair.1, hpair.2]

    have hAfive : (5 : ℤ) ∣ S.A := by
      have h := dvd_sub hd hmultiple
      rwa [hidentity] at h

    exact fifthNormSolution_five_not_dvd_first S hAfive

  have hj : j = 0 :=
    norm_twist_index_eq_zero
      (five_dvd_fifthPhiCoeff r s) hcoefficient hfree

  refine ⟨V, ?_⟩
  simpa [hj] using hV

theorem fifthPhiCoeff_cast_two (r s : ℤ) :
    (fifthPhiCoeff r s : ZMod 2) = (s : ZMod 2) := by
  have hfinite :
      ∀ x y : ZMod 2,
        5 * x ^ 4 * y +
          10 * x ^ 3 * y ^ 2 +
          20 * x ^ 2 * y ^ 3 +
          15 * x * y ^ 4 +
          5 * y ^ 5 = y := by
    decide

  unfold fifthPhiCoeff
  push_cast
  exact hfinite (r : ZMod 2) (s : ZMod 2)

/-- An even fifth-power phi coefficient forces
the root's phi coefficient to be even. -/
theorem even_coordinate_of_even_fifthPhiCoeff
    {r s : ℤ}
    (hD : Even (fifthPhiCoeff r s)) :
    Even s := by
  have hdiv : (2 : ℤ) ∣ fifthPhiCoeff r s :=
    even_iff_two_dvd.mp hD

  have hzero : (fifthPhiCoeff r s : ZMod 2) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdiv

  rw [fifthPhiCoeff_cast_two] at hzero

  apply even_iff_two_dvd.mpr
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero

/-- The auxiliary fifth-power root has integer
coordinates in the basis 1, delta. -/
theorem fifthNormSolution_integer_root
    (S : FifthNormSolution) :
    ∃ c d : ℤ,
      sqrtFiveFactor S.A S.B = (sqrtFiveFactor c d) ^ 5 := by
  obtain ⟨V, hV⟩ := fifthNormSolution_factor_is_fifth_power S
  obtain ⟨r, s, hcoords⟩ := exists_integer_coordinates V

  have heq :
      ((S.A - S.B : ℤ) : G) +
          ((2 * S.B : ℤ) : G) * phi =
        (fifthConstant r s : G) +
          (fifthPhiCoeff r s : G) * phi := by
    calc
      _ = sqrtFiveFactor S.A S.B := by
        unfold sqrtFiveFactor delta
        push_cast
        ring
      _ = V ^ 5 := hV
      _ = ((r : G) + (s : G) * phi) ^ 5 := by
        rw [hcoords]
      _ = _ := fifth_power_coordinates r s

  have hpair := integer_coordinates_eq heq

  have hDeven : Even (fifthPhiCoeff r s) := by
    rw [← hpair.2]
    refine ⟨S.B, ?_⟩
    ring

  have hseven := even_coordinate_of_even_fifthPhiCoeff hDeven
  obtain ⟨d, hd⟩ := even_iff_two_dvd.mp hseven

  have hroot : V = sqrtFiveFactor (r + d) d := by
    rw [hcoords, hd]
    unfold sqrtFiveFactor delta
    push_cast
    ring

  refine ⟨r + d, d, ?_⟩
  rw [← hroot]
  exact hV

theorem sqrtFiveFactor_coordinates_eq
    {A B C D : ℤ}
    (h : sqrtFiveFactor A B = sqrtFiveFactor C D) :
    A = C ∧ B = D := by
  have heq :
      ((A - B : ℤ) : G) + ((2 * B : ℤ) : G) * phi =
        ((C - D : ℤ) : G) + ((2 * D : ℤ) : G) * phi := by
    calc
      _ = sqrtFiveFactor A B := by
        unfold sqrtFiveFactor delta
        push_cast
        ring
      _ = sqrtFiveFactor C D := h
      _ = _ := by
        unfold sqrtFiveFactor delta
        push_cast
        ring

  have hpair := integer_coordinates_eq heq
  constructor <;> omega

/-- Extract the integer equations from a genuine fifth-power root. -/
theorem sqrtFive_root_coefficient_equations
    {A B c d : ℤ}
    (hroot :
      sqrtFiveFactor A B = (sqrtFiveFactor c d) ^ 5) :
    A = c * (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4) ∧
      B = 5 * d * descentNormFactor c d := by
  apply sqrtFiveFactor_coordinates_eq
  rw [hroot]
  exact sqrtFive_fifth_power_coordinates c d

/-- Coprimality passes from the original coefficients to the root. -/
theorem sqrtFive_root_coordinates_coprime
    {A B c d : ℤ}
    (hab : IsCoprime A B)
    (hA :
      A = c * (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4))
    (hB : B = 5 * d * descentNormFactor c d) :
    IsCoprime c d := by
  have hrel : IsRelPrime c d := by
    intro e hec hed
    obtain ⟨x, hx⟩ := hec
    obtain ⟨y, hy⟩ := hed

    have heA : e ∣ A := by
      rw [hA, hx, hy]
      refine ⟨e ^ 4 * x *
        (x ^ 4 + 50 * x ^ 2 * y ^ 2 + 125 * y ^ 4), ?_⟩
      ring

    have heB : e ∣ B := by
      rw [hB, hx, hy]
      refine ⟨5 * e ^ 4 * y * descentNormFactor x y, ?_⟩
      unfold descentNormFactor
      ring

    exact hab.isUnit_of_dvd' heA heB

  exact hrel.isCoprime

/-- An odd first coefficient forces c odd and d even. -/
theorem sqrtFive_root_coordinate_parity
    {A c d : ℤ}
    (hAodd : Odd A)
    (hA :
      A = c * (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4)) :
    Odd c ∧ Even d := by
  have hAcast : (A : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hAodd
    rw [hk]
    push_cast
    have hfinite : ∀ z : ZMod 2, 2 * z + 1 = 1 := by
      decide
    exact hfinite (k : ZMod 2)

  have hmod := congrArg (fun z : ℤ => (z : ZMod 2)) hA
  push_cast at hmod
  rw [hAcast] at hmod

  have hfinite :
      ∀ x y : ZMod 2,
        x * (x ^ 4 + 50 * x ^ 2 * y ^ 2 + 125 * y ^ 4) = 1 →
          x = 1 ∧ y = 0 := by
    decide

  have hparity := hfinite (c : ZMod 2) (d : ZMod 2) hmod.symm

  constructor
  · have hz : ((c - 1 : ℤ) : ZMod 2) = 0 := by
      push_cast
      rw [hparity.1]
      ring
    have hdiv : (2 : ℤ) ∣ c - 1 := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨k, ?_⟩
    linarith [hk]

  · apply even_iff_two_dvd.mpr
    have hz := hparity.2
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz

theorem sqrtFive_root_first_five_free
    {A c d : ℤ}
    (hAfive : ¬ (5 : ℤ) ∣ A)
    (hA :
      A = c * (c ^ 4 + 50 * c ^ 2 * d ^ 2 + 125 * d ^ 4)) :
    ¬ (5 : ℤ) ∣ c := by
  intro hc
  apply hAfive
  rw [hA]
  exact dvd_mul_of_dvd_left hc _

theorem sqrtFive_root_second_positive
    {B c d : ℤ}
    (hBpositive : 0 < B)
    (hB : B = 5 * d * descentNormFactor c d) :
    0 < d := by
  have hK : 0 ≤ descentNormFactor c d := by
    have h := descentNormFactor_lower_bound c d
    have hdFourth : 0 ≤ d ^ 4 := by positivity
    nlinarith [h, hdFourth]

  by_contra h
  have hd : d ≤ 0 := by omega
  have hproduct : 5 * d * descentNormFactor c d ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by omega) hK
  rw [← hB] at hproduct
  linarith

/-- Every auxiliary norm solution produces a smaller one. -/
theorem fifthNormSolution_descent
    (S : FifthNormSolution) :
    ∃ S' : FifthNormSolution, S'.B < S.B := by
  obtain ⟨c, d, hroot⟩ := fifthNormSolution_integer_root S
  obtain ⟨hA, hB⟩ := sqrtFive_root_coefficient_equations hroot

  have hcd :=
    sqrtFive_root_coordinates_coprime S.coprime hA hB

  obtain ⟨hcOdd, hdEven⟩ :=
    sqrtFive_root_coordinate_parity S.odd_first hA

  have hcFive :=
    sqrtFive_root_first_five_free
      (fifthNormSolution_five_not_dvd_first S) hA

  have hdPositive :=
    sqrtFive_root_second_positive S.positive_second hB

  exact fifthNormSolution_descent_of_root
    S hcd hcOdd hdEven hcFive hdPositive hB

/-- Infinite descent rules out the auxiliary norm solution. -/
theorem no_fifthNormSolution (S : FifthNormSolution) : False := by
  have hall :
      ∀ n : ℕ, ∀ T : FifthNormSolution,
        T.B.natAbs = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro T hmeasure
        obtain ⟨T', hsmaller⟩ := fifthNormSolution_descent T

        have hnat : T'.B.natAbs < T.B.natAbs := by
          have hcast :
              (T'.B.natAbs : ℤ) < (T.B.natAbs : ℤ) := by
            simpa only [
              Int.natCast_natAbs,
              abs_of_pos T'.positive_second,
              abs_of_pos T.positive_second
            ] using hsmaller
          exact_mod_cast hcast

        have hlt : T'.B.natAbs < n := by
          omega

        exact ih T'.B.natAbs hlt T' rfl

  exact hall S.B.natAbs S rfl

/-- Allocate fifth powers between the two coprime factors. -/
theorem fifty_mul_fifth_power_allocation
    {r R z : ℤ}
    (hcop : IsCoprime (50 * r) R)
    (hproduct : (50 * r) * R = z ^ 5) :
    ∃ u v : ℤ, r = 2000 * u ^ 5 ∧ R = v ^ 5 := by
  obtain ⟨e, he⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcop (by decide : Odd (5 : ℕ)) hproduct

  obtain ⟨v, hv⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcop.symm (by decide : Odd (5 : ℕ))
      (by simpa only [mul_comm] using hproduct)

  have htwo : (2 : ℤ) ∣ e := by
    have hp : Prime (2 : ℤ) := by norm_num
    have hpow : (2 : ℤ) ∣ e ^ 5 := by
      rw [← he]
      refine ⟨25 * r, ?_⟩
      ring
    exact hp.dvd_of_dvd_pow hpow

  have hfive : (5 : ℤ) ∣ e := by
    have hp : Prime (5 : ℤ) := by norm_num
    have hpow : (5 : ℤ) ∣ e ^ 5 := by
      rw [← he]
      refine ⟨10 * r, ?_⟩
      ring
    exact hp.dvd_of_dvd_pow hpow

  have hten : (10 : ℤ) ∣ e := by
    have hmod2 : e % 2 = 0 :=
      Int.dvd_iff_emod_eq_zero.mp htwo
    have hmod5 : e % 5 = 0 :=
      Int.dvd_iff_emod_eq_zero.mp hfive
    apply Int.dvd_iff_emod_eq_zero.mpr
    omega

  obtain ⟨u, hu⟩ := hten
  refine ⟨u, v, ?_, hv⟩
  rw [hu] at he
  nlinarith [he]

/-- Construct an auxiliary norm solution from the allocated factors. -/
theorem fifthNormSolution_of_normalized_factors
    {q r z : ℤ}
    (hr : r ≠ 0)
    (hcop :
      IsCoprime (50 * r)
        (q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4))
    (hpair :
      IsCoprime (q ^ 2 + 25 * r ^ 2) (10 * r ^ 2))
    (hodd : Odd (q ^ 2 + 25 * r ^ 2))
    (hproduct :
      (50 * r) *
        (q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4) =
          z ^ 5) :
    Nonempty FifthNormSolution := by
  obtain ⟨u, v, hu, hv⟩ :=
    fifty_mul_fifth_power_allocation hcop hproduct

  refine ⟨{
    A := q ^ 2 + 25 * r ^ 2
    B := 10 * r ^ 2
    t := 10 * u ^ 2
    v := v
    coprime := hpair
    odd_first := hodd
    even_second := ?_
    coefficient := ?_
    positive_second := ?_
    norm_eq := ?_
  }⟩

  · apply even_iff_two_dvd.mpr
    refine ⟨5 * r ^ 2, ?_⟩
    ring

  · rw [hu]
    ring

  · have hr2 : 0 < r ^ 2 := by positivity
    nlinarith

  · calc
      (q ^ 2 + 25 * r ^ 2) ^ 2 -
          5 * (10 * r ^ 2) ^ 2 =
          q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4 := by
            ring
      _ = v ^ 5 := hv

/-- Adding 25r² preserves coprimality with r². -/
theorem normalized_norm_first_coprime_square
    {q r : ℤ}
    (hqr : IsCoprime q r) :
    IsCoprime (q ^ 2 + 25 * r ^ 2) (r ^ 2) := by
  have hsq : IsCoprime (q ^ 2) (r ^ 2) :=
    hqr.pow_left.pow_right
  exact hsq.add_mul_right_left 25

/-- If q is 5-free, so is the first norm coordinate. -/
theorem normalized_norm_first_five_free
    {q r : ℤ}
    (hq : ¬ (5 : ℤ) ∣ q) :
    ¬ (5 : ℤ) ∣ q ^ 2 + 25 * r ^ 2 := by
  intro hA

  have hmultiple : (5 : ℤ) ∣ 25 * r ^ 2 := by
    refine ⟨5 * r ^ 2, ?_⟩
    ring

  have hsquare : (5 : ℤ) ∣ q ^ 2 := by
    have h := dvd_sub hA hmultiple
    simpa using h

  have hp : Prime (5 : ℤ) := by norm_num
  exact hq (hp.dvd_of_dvd_pow hsquare)

/-- Opposite parity makes the first norm coordinate odd. -/
theorem normalized_norm_first_odd
    {q r : ℤ}
    (hparity : Odd (q + r)) :
    Odd (q ^ 2 + 25 * r ^ 2) := by
  have hsum : ((q + r : ℤ) : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hparity
    rw [hk]
    push_cast
    have hfinite : ∀ x : ZMod 2, 2 * x + 1 = 1 := by
      decide
    exact hfinite (k : ZMod 2)

  have hfinite :
      ∀ x y : ZMod 2,
        x ^ 2 + 25 * y ^ 2 = x + y := by
    decide

  have hcast :
      ((q ^ 2 + 25 * r ^ 2 : ℤ) : ZMod 2) = 1 := by
    push_cast
    rw [hfinite]
    simpa only [Int.cast_add] using hsum

  have hz :
      ((q ^ 2 + 25 * r ^ 2 - 1 : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_sub, hcast]
    norm_num

  have hdiv : (2 : ℤ) ∣ q ^ 2 + 25 * r ^ 2 - 1 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz

  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k, ?_⟩
  linarith [hk]

/-- A 5-free integer is coprime to 5. -/
theorem integer_coprime_five_of_five_free
    {A : ℤ}
    (hA : ¬ (5 : ℤ) ∣ A) :
    IsCoprime A 5 := by
  have hlo : 0 ≤ A % 5 :=
    Int.emod_nonneg A (by decide : (5 : ℤ) ≠ 0)
  have hhi : A % 5 < 5 :=
    Int.emod_lt_of_pos A (by decide : (0 : ℤ) < 5)

  interval_cases h : A % 5
  · exact False.elim
      (hA (Int.dvd_iff_emod_eq_zero.mpr h))
  · refine ⟨1, -(A / 5), ?_⟩
    omega
  · refine ⟨-2, 2 * (A / 5) + 1, ?_⟩
    omega
  · refine ⟨2, -2 * (A / 5) - 1, ?_⟩
    omega
  · refine ⟨-1, A / 5 + 1, ?_⟩
    omega

/-- The two norm coordinates are coprime. -/
theorem normalized_norm_pair_coprime
    {q r : ℤ}
    (hqr : IsCoprime q r)
    (hqFive : ¬ (5 : ℤ) ∣ q)
    (hparity : Odd (q + r)) :
    IsCoprime (q ^ 2 + 25 * r ^ 2) (10 * r ^ 2) := by
  have hodd :=
    normalized_norm_first_odd hparity

  have htwo :
      IsCoprime (q ^ 2 + 25 * r ^ 2) 2 :=
    hodd.isCoprime_two

  have hfive :
      IsCoprime (q ^ 2 + 25 * r ^ 2) 5 :=
    integer_coprime_five_of_five_free
      (normalized_norm_first_five_free hqFive)

  have hten :
      IsCoprime (q ^ 2 + 25 * r ^ 2) 10 := by
    have h := htwo.mul_right hfive
    norm_num at h
    exact h

  exact hten.mul_right
    (normalized_norm_first_coprime_square hqr)

/-- The normalized fifth-power factors are coprime. -/
theorem normalized_fifth_factors_coprime
    {q r : ℤ}
    (hqr : IsCoprime q r)
    (hqFive : ¬ (5 : ℤ) ∣ q)
    (hparity : Odd (q + r)) :
    IsCoprime (50 * r)
      (q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4) := by
  let R : ℤ :=
    q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4

  have hRr : IsCoprime R r := by
    have hpow : IsCoprime (q ^ 4) r := hqr.pow_left
    have h :=
      hpow.add_mul_right_left
        (50 * r * q ^ 2 + 125 * r ^ 3)
    convert h using 1
    dsimp [R]
    ring

  have hRFive : ¬ (5 : ℤ) ∣ R := by
    intro hR
    have hmultiple :
        (5 : ℤ) ∣ 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4 := by
      refine ⟨10 * r ^ 2 * q ^ 2 + 25 * r ^ 4, ?_⟩
      ring
    have hqpow : (5 : ℤ) ∣ q ^ 4 := by
      have h := dvd_sub hR hmultiple
      dsimp [R] at h
      simpa using h
    have hp : Prime (5 : ℤ) := by norm_num
    exact hqFive (hp.dvd_of_dvd_pow hqpow)

  have hRodd : Odd R := by
    have hsum : ((q + r : ℤ) : ZMod 2) = 1 := by
      obtain ⟨k, hk⟩ := hparity
      rw [hk]
      push_cast
      have hfinite : ∀ x : ZMod 2, 2 * x + 1 = 1 := by
        decide
      exact hfinite (k : ZMod 2)

    have hfinite :
        ∀ x y : ZMod 2,
          x ^ 4 + 50 * y ^ 2 * x ^ 2 + 125 * y ^ 4 =
            x + y := by
      decide

    have hcast : (R : ZMod 2) = 1 := by
      dsimp [R]
      push_cast
      rw [hfinite]
      simpa only [Int.cast_add] using hsum

    have hz : ((R - 1 : ℤ) : ZMod 2) = 0 := by
      rw [Int.cast_sub, hcast]
      norm_num

    have hdiv : (2 : ℤ) ∣ R - 1 := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz

    obtain ⟨k, hk⟩ := hdiv
    refine ⟨k, ?_⟩
    linarith [hk]

  have hRtwo : IsCoprime R 2 :=
    hRodd.isCoprime_two

  have hRfive : IsCoprime R 5 :=
    integer_coprime_five_of_five_free hRFive

  have hRtwentyFive : IsCoprime R (5 ^ 2) :=
    hRfive.pow_right

  have hRfifty : IsCoprime R 50 := by
    have h := hRtwo.mul_right hRtwentyFive
    norm_num at h
    exact h

  exact (hRfifty.mul_right hRr).symm

/-- The normalized equation is impossible under the primitive coprimality, parity, and 5-free conditions. -/
theorem no_normalized_fifth_solution
    {q r z : ℤ}
    (hr : r ≠ 0)
    (hqr : IsCoprime q r)
    (hqFive : ¬ (5 : ℤ) ∣ q)
    (hparity : Odd (q + r))
    (hproduct :
      (50 * r) *
        (q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4) =
          z ^ 5) :
    False := by
  obtain ⟨S⟩ :=
    fifthNormSolution_of_normalized_factors
      hr
      (normalized_fifth_factors_coprime hqr hqFive hparity)
      (normalized_norm_pair_coprime hqr hqFive hparity)
      (normalized_norm_first_odd hparity)
      hproduct
  exact no_fifthNormSolution S

/-- Centering the inputs at 5r gives the normalized factorization. -/
theorem centered_fifth_powers_identity (q r : ℤ) :
    (5 * r + q) ^ 5 + (5 * r - q) ^ 5 =
      (50 * r) *
        (q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4) := by
  ring

/-- Rule out a fifth-power solution with these centered coordinates. -/
theorem no_fifth_solution_of_centered_coordinates
    {a b z q r : ℤ}
    (hr : r ≠ 0)
    (hqr : IsCoprime q r)
    (hqFive : ¬ (5 : ℤ) ∣ q)
    (hparity : Odd (q + r))
    (hcenter : a + b = 10 * r)
    (hgap : a - b = 2 * q)
    (hc : a ^ 5 + b ^ 5 = z ^ 5) :
    False := by
  have ha : a = 5 * r + q := by
    linarith [hcenter, hgap]
  have hb : b = 5 * r - q := by
    linarith [hcenter, hgap]

  apply no_normalized_fifth_solution hr hqr hqFive hparity
  calc
    (50 * r) *
        (q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4) =
        (5 * r + q) ^ 5 + (5 * r - q) ^ 5 :=
      (centered_fifth_powers_identity q r).symm
    _ = a ^ 5 + b ^ 5 := by rw [ha, hb]
    _ = z ^ 5 := hc

/-- Primitive centered inputs give the required coprimality, 5-free condition, and opposite parity. -/
theorem centered_fifth_coordinates_properties
    {a b q r : ℤ}
    (hab : IsCoprime a b)
    (haOdd : Odd a)
    (hcenter : a + b = 10 * r)
    (hgap : a - b = 2 * q) :
    IsCoprime q r ∧
      ¬ (5 : ℤ) ∣ q ∧
      Odd (q + r) := by
  have ha : a = 5 * r + q := by
    linarith [hcenter, hgap]
  have hb : b = 5 * r - q := by
    linarith [hcenter, hgap]

  obtain ⟨u, v, huv⟩ := hab

  have hqr : IsCoprime q r := by
    refine ⟨u - v, 5 * (u + v), ?_⟩
    rw [ha, hb] at huv
    nlinarith [huv]

  have hqFive : ¬ (5 : ℤ) ∣ q := by
    intro hq
    obtain ⟨k, hk⟩ := hq

    have hda : (5 : ℤ) ∣ a := by
      refine ⟨r + k, ?_⟩
      rw [ha, hk]
      ring

    have hdb : (5 : ℤ) ∣ b := by
      refine ⟨r - k, ?_⟩
      rw [hb, hk]
      ring

    have hone : (5 : ℤ) ∣ 1 := by
      rw [← huv]
      exact dvd_add
        (dvd_mul_of_dvd_right hda u)
        (dvd_mul_of_dvd_right hdb v)

    norm_num at hone

  have hparity : Odd (q + r) := by
    obtain ⟨k, hk⟩ := haOdd
    refine ⟨k - 2 * r, ?_⟩
    linarith [ha, hk]

  exact ⟨hqr, hqFive, hparity⟩

/-- Rule out primitive odd inputs whose centered sum is nonzero. -/
theorem no_primitive_fifth_solution_of_centered_coordinates
    {a b z q r : ℤ}
    (hab : IsCoprime a b)
    (haOdd : Odd a)
    (hsum : a + b ≠ 0)
    (hcenter : a + b = 10 * r)
    (hgap : a - b = 2 * q)
    (hc : a ^ 5 + b ^ 5 = z ^ 5) :
    False := by
  have hr : r ≠ 0 := by
    intro hr
    apply hsum
    rw [hcenter, hr]
    ring

  obtain ⟨hqr, hqFive, hparity⟩ :=
    centered_fifth_coordinates_properties hab haOdd hcenter hgap

  exact no_fifth_solution_of_centered_coordinates
    hr hqr hqFive hparity hcenter hgap hc

/-- Rule out the branch with odd inputs and a sum divisible by 5. -/
theorem no_primitive_fifth_solution_odd_inputs_five_dvd_sum
    {a b z : ℤ}
    (hab : IsCoprime a b)
    (haOdd : Odd a)
    (hbOdd : Odd b)
    (hz : z ≠ 0)
    (hfive : (5 : ℤ) ∣ a + b)
    (hc : a ^ 5 + b ^ 5 = z ^ 5) :
    False := by
  have hsum : a + b ≠ 0 := by
    intro hzero
    have hb : b = -a := by linarith [hzero]
    have hzpow : z ^ 5 = 0 := by
      calc
        z ^ 5 = a ^ 5 + b ^ 5 := hc.symm
        _ = 0 := by rw [hb]; ring
    exact (pow_ne_zero 5 hz) hzpow

  obtain ⟨ka, hka⟩ := haOdd
  obtain ⟨kb, hkb⟩ := hbOdd

  have htwo : (2 : ℤ) ∣ a + b := by
    refine ⟨ka + kb + 1, ?_⟩
    linarith [hka, hkb]

  have hten : (10 : ℤ) ∣ a + b := by
    have hmod2 : (a + b) % 2 = 0 :=
      Int.dvd_iff_emod_eq_zero.mp htwo
    have hmod5 : (a + b) % 5 = 0 :=
      Int.dvd_iff_emod_eq_zero.mp hfive
    apply Int.dvd_iff_emod_eq_zero.mpr
    omega

  obtain ⟨r, hr⟩ := hten

  have hgap : a - b = 2 * (ka - kb) := by
    linarith [hka, hkb]

  have haOdd' : Odd a := ⟨ka, hka⟩

  exact no_primitive_fifth_solution_of_centered_coordinates
    hab haOdd' hsum hr hgap hc

/-- A fifth-power equation preserves the sum modulo 5. -/
theorem five_dvd_sum_of_fifth_solution
    {a b z : ℤ}
    (hc : a ^ 5 + b ^ 5 = z ^ 5)
    (hzFive : (5 : ℤ) ∣ z) :
    (5 : ℤ) ∣ a + b := by
  have hfifth : ∀ x : ZMod 5, x ^ 5 = x := by
    decide

  have hcast :=
    congrArg (fun x : ℤ => (x : ZMod 5)) hc
  push_cast at hcast
  simp only [hfifth] at hcast

  have hzcast : (z : ZMod 5) = 0 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]

  have hsum : ((a + b : ℤ) : ZMod 5) = 0 := by
    rw [Int.cast_add]
    exact hcast.trans hzcast

  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hsum

/-- Close the primitive branch with odd inputs and 5 dividing the output. -/
theorem no_primitive_fifth_solution_odd_inputs_five_dvd_output
    {a b z : ℤ}
    (hab : IsCoprime a b)
    (haOdd : Odd a)
    (hbOdd : Odd b)
    (hz : z ≠ 0)
    (hzFive : (5 : ℤ) ∣ z)
    (hc : a ^ 5 + b ^ 5 = z ^ 5) :
    False := by
  exact no_primitive_fifth_solution_odd_inputs_five_dvd_sum
    hab haOdd hbOdd hz
    (five_dvd_sum_of_fifth_solution hc hzFive)
    hc

/-- Factor the fifth-power sum using the full sum and difference. -/
theorem sixteen_mul_sum_fifth_powers (a b : ℤ) :
    16 * (a ^ 5 + b ^ 5) =
      (a + b) *
        ((a + b) ^ 4
          + 10 * (a + b) ^ 2 * (a - b) ^ 2
          + 5 * (a - b) ^ 4) := by
  ring

/-- Normalize the branch whose sum is 5r. -/
theorem odd_output_normalized_equation
    {a b z q r : ℤ}
    (hcenter : a + b = 5 * r)
    (hgap : a - b = q)
    (hc : a ^ 5 + b ^ 5 = z ^ 5) :
    (25 * r) *
        (q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4) =
      16 * z ^ 5 := by
  calc
    (25 * r) *
        (q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4) =
        (a + b) *
          ((a + b) ^ 4
            + 10 * (a + b) ^ 2 * (a - b) ^ 2
            + 5 * (a - b) ^ 4) := by
              rw [hcenter, hgap]
              ring
    _ = 16 * (a ^ 5 + b ^ 5) :=
      (sixteen_mul_sum_fifth_powers a b).symm
    _ = 16 * z ^ 5 := by rw [hc]

/-- Expose the norm needed for the remaining parity branch. -/
theorem odd_output_quartic_norm
    {q r P : ℤ}
    (hP : 2 * P = q ^ 2 + 25 * r ^ 2) :
    4 * (P ^ 2 - 5 * (5 * r ^ 2) ^ 2) =
      q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4 := by
  have hsquare := congrArg (fun x : ℤ => x ^ 2) hP
  nlinarith [hsquare]

/-- Integer golden coordinates represent the half-integer norm. -/
theorem half_norm_goldenNorm
    {P Q c v : ℤ}
    (hP : P = 2 * c + Q)
    (hnorm : P ^ 2 - 5 * Q ^ 2 = 4 * v ^ 5) :
    goldenNorm ((c : G) + (Q : G) * phi) = v ^ 5 := by
  rw [goldenNorm_coordinates]
  unfold coordNorm
  rw [hP] at hnorm
  nlinarith [hnorm]

/-- The half-integer factor remains free of the exceptional prime. -/
theorem half_norm_residue_five_free
    {P Q c : ℤ}
    (hP : P = 2 * c + Q)
    (hPFive : ¬ (5 : ℤ) ∣ P)
    (hQFive : (5 : ℤ) ∣ Q) :
    ¬ (5 : ℤ) ∣ c + 3 * Q := by
  intro h

  have hc : (5 : ℤ) ∣ c := by
    have hmultiple : (5 : ℤ) ∣ 3 * Q :=
      dvd_mul_of_dvd_right hQFive 3
    have hd := dvd_sub h hmultiple
    simpa using hd

  apply hPFive
  rw [hP]
  exact dvd_add
    (dvd_mul_of_dvd_right hc 2)
    hQFive

/-- Extract a fifth-power root of the half-integer norm factor,
once coprimality with its conjugate has been established. -/
theorem half_norm_factor_is_fifth_power
    {P Q c v : ℤ}
    (hP : P = 2 * c + Q)
    (hPFive : ¬ (5 : ℤ) ∣ P)
    (hQFive : (5 : ℤ) ∣ Q)
    (hnorm : P ^ 2 - 5 * Q ^ 2 = 4 * v ^ 5)
    (hcop :
      IsCoprime
        ((c : G) + (Q : G) * phi)
        (goldenConj ((c : G) + (Q : G) * phi))) :
    ∃ V : G, (c : G) + (Q : G) * phi = V ^ 5 := by
  have hNorm := half_norm_goldenNorm hP hnorm

  have hproduct :
      ((c : G) + (Q : G) * phi) *
        goldenConj ((c : G) + (Q : G) * phi) =
          (v : G) ^ 5 := by
    rw [mul_goldenConj, hNorm]
    push_cast
    rfl

  obtain ⟨W, hW⟩ :=
    exists_associated_pow_of_mul_eq_pow' hcop hproduct

  obtain ⟨j, V, hV⟩ :=
    associated_fifth_power_normal_form hW

  obtain ⟨r, s, hcoords⟩ := exists_integer_coordinates V

  have hcoeff := hV
  rw [hcoords, twisted_fifth_power_coordinates] at hcoeff
  obtain ⟨hc, hQ⟩ := integer_coordinates_eq hcoeff

  have hsecond :
      (5 : ℤ) ∣
        (phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).2 := by
    rw [← hQ]
    exact hQFive

  have hfree :
      ¬ (5 : ℤ) ∣
        (phiTwistCoordinates (j : ℕ)
          (fifthConstant r s) (fifthPhiCoeff r s)).1
          + 3 *
            (phiTwistCoordinates (j : ℕ)
              (fifthConstant r s) (fifthPhiCoeff r s)).2 := by
    rw [← hc, ← hQ]
    exact half_norm_residue_five_free hP hPFive hQFive

  have hj : j = 0 :=
    norm_twist_index_eq_zero
      (five_dvd_fifthPhiCoeff r s) hsecond hfree

  refine ⟨V, ?_⟩
  rw [hj] at hV
  simpa using hV

/-- Primitive half-integer norm factors are coprime
to their conjugates. -/
theorem half_norm_factor_conjugates_coprime
    {P Q c : ℤ}
    (hP : P = 2 * c + Q)
    (hPQ : IsCoprime P Q)
    (hPFive : ¬ (5 : ℤ) ∣ P)
    (hQFive : (5 : ℤ) ∣ Q) :
    IsCoprime
      ((c : G) + (Q : G) * phi)
      (goldenConj ((c : G) + (Q : G) * phi)) := by
  let H : G := (c : G) + (Q : G) * phi

  have hsum : H + goldenConj H = (P : G) := by
    dsimp [H]
    rw [goldenConj_coordinates, hP]
    push_cast
    ring

  have hdiff : H - goldenConj H = (Q : G) * delta := by
    dsimp [H]
    rw [goldenConj_coordinates]
    unfold delta
    push_cast
    ring

  have hdeltaFree : ¬ delta ∣ H := by
    intro hd
    have hzero :=
      (goldenResidue_eq_zero_iff H).mpr hd
    dsimp [H] at hzero
    rw [goldenResidue_coordinates] at hzero

    have hz : ((c + 3 * Q : ℤ) : ZMod 5) = 0 := by
      push_cast
      simpa only [mul_comm] using hzero

    have hdiv : (5 : ℤ) ∣ c + 3 * Q := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz

    exact half_norm_residue_five_free hP hPFive hQFive hdiv

  have hcopDelta : IsCoprime delta H :=
    delta_prime.coprime_iff_not_dvd.mpr hdeltaFree

  obtain ⟨u, v, huv⟩ := hPQ

  have huvG :
      (u : G) * (P : G) + (v : G) * (Q : G) = 1 := by
    have h := congrArg (fun x : ℤ => (x : G)) huv
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using h

  have hrel : IsRelPrime H (goldenConj H) := by
    intro d hdH hdConj

    have hdP : d ∣ (P : G) := by
      rw [← hsum]
      exact dvd_add hdH hdConj

    have hdQdelta : d ∣ (Q : G) * delta := by
      rw [← hdiff]
      exact dvd_sub hdH hdConj

    have hfirst : d ∣ (u : G) * (P : G) * delta :=
      dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right hdP (u : G)) delta

    have hsecond : d ∣ (v : G) * ((Q : G) * delta) :=
      dvd_mul_of_dvd_right hdQdelta (v : G)

    have hdDelta : d ∣ delta := by
      have h := dvd_add hfirst hsecond
      have heq :
          (u : G) * (P : G) * delta
            + (v : G) * ((Q : G) * delta) = delta := by
        calc
          _ = ((u : G) * (P : G)
                + (v : G) * (Q : G)) * delta := by ring
          _ = delta := by rw [huvG, one_mul]
      rw [heq] at h
      exact h

    exact hcopDelta.isUnit_of_dvd' hdDelta hdH

  exact hrel.isCoprime

/-- Extract the half-integer fifth-power root from primitive data. -/
theorem half_norm_factor_is_fifth_power_of_coprime
    {P Q c v : ℤ}
    (hP : P = 2 * c + Q)
    (hPQ : IsCoprime P Q)
    (hPFive : ¬ (5 : ℤ) ∣ P)
    (hQFive : (5 : ℤ) ∣ Q)
    (hnorm : P ^ 2 - 5 * Q ^ 2 = 4 * v ^ 5) :
    ∃ V : G, (c : G) + (Q : G) * phi = V ^ 5 := by
  exact half_norm_factor_is_fifth_power
    hP hPFive hQFive hnorm
    (half_norm_factor_conjugates_coprime
      hP hPQ hPFive hQFive)

/-- Extract the scaled integer coordinate equations from the half-integer fifth-power root. -/
theorem half_norm_fifth_root_coefficient_equations
    {P Q c v : ℤ}
    (hP : P = 2 * c + Q)
    (hPQ : IsCoprime P Q)
    (hPFive : ¬ (5 : ℤ) ∣ P)
    (hQFive : (5 : ℤ) ∣ Q)
    (hnorm : P ^ 2 - 5 * Q ^ 2 = 4 * v ^ 5) :
    ∃ t s : ℤ,
      16 * P =
        t * (t ^ 4 + 50 * t ^ 2 * s ^ 2 + 125 * s ^ 4) ∧
      16 * Q = 5 * s * descentNormFactor t s := by
  obtain ⟨V, hV⟩ :=
    half_norm_factor_is_fifth_power_of_coprime
      hP hPQ hPFive hQFive hnorm

  obtain ⟨r, s, hcoords⟩ := exists_integer_coordinates V
  rw [hcoords, fifth_power_coordinates] at hV
  obtain ⟨hc, hQ⟩ := integer_coordinates_eq hV

  refine ⟨2 * r + s, s, ?_, ?_⟩
  · rw [hP, hc, hQ]
    unfold fifthConstant fifthPhiCoeff
    ring
  · rw [hQ]
    unfold fifthPhiCoeff descentNormFactor
    ring

/-- The new second coordinate s² is smaller than Q. -/
theorem half_norm_second_coordinate_decreases
    {Q t s : ℤ}
    (hs : 0 < s)
    (hQ : 16 * Q = 5 * s * descentNormFactor t s) :
    s ^ 2 < Q := by
  have hs1 : 1 ≤ s := by omega
  have hK := descentNormFactor_lower_bound t s

  have hcube : 1 ≤ s ^ 3 := by
    have hprod :
        0 ≤ (s - 1) * (s ^ 2 + s + 1) :=
      mul_nonneg (by omega) (by positivity)
    nlinarith [hprod]

  have hfifth : s ^ 2 ≤ s ^ 5 := by
    have hprod :
        0 ≤ s ^ 2 * (s ^ 3 - 1) :=
      mul_nonneg (sq_nonneg s) (by omega)
    nlinarith [hprod]

  have hscaled :
      0 ≤ s * (descentNormFactor t s - 5 * s ^ 4) :=
    mul_nonneg (by omega) (by linarith [hK])

  have hsquare : 0 < s ^ 2 := by positivity
  nlinarith [hQ, hscaled, hfifth, hsquare]

/-- Auxiliary solution for the odd-output branch. -/
structure HalfFifthNormSolution where
  P : ℤ
  Q : ℤ
  u : ℤ
  v : ℤ
  coprime : IsCoprime P Q
  odd_first : Odd P
  odd_second : Odd Q
  coefficient : Q = 25 * u ^ 5
  positive_second : 0 < Q
  norm_eq : P ^ 2 - 5 * Q ^ 2 = 4 * v ^ 5

/-- Odd root coordinates produce an odd new first coordinate,
and the quartic has the required factor of 16. -/
theorem half_descent_new_norm_coordinates
    {t s : ℤ}
    (htOdd : Odd t)
    (hsOdd : Odd s) :
    ∃ P H : ℤ,
      Odd P ∧
      2 * P = t ^ 2 + 5 * s ^ 2 ∧
      descentNormFactor t s = 16 * H ∧
      P ^ 2 - 5 * (s ^ 2) ^ 2 = 4 * H := by
  obtain ⟨m, hm⟩ := htOdd
  obtain ⟨n, hn⟩ := hsOdd

  let P : ℤ :=
    2 * m ^ 2 + 2 * m + 10 * n ^ 2 + 10 * n + 3

  let H : ℤ :=
    m ^ 4 + 2 * m ^ 3
      + 10 * m ^ 2 * n ^ 2
      + 10 * m ^ 2 * n + 4 * m ^ 2
      + 10 * m * n ^ 2 + 10 * m * n + 3 * m
      + 5 * n ^ 4 + 10 * n ^ 3
      + 10 * n ^ 2 + 5 * n + 1

  have hPodd : Odd P := by
    refine ⟨m ^ 2 + m + 5 * n ^ 2 + 5 * n + 1, ?_⟩
    dsimp [P]
    ring

  have hP : 2 * P = t ^ 2 + 5 * s ^ 2 := by
    rw [hm, hn]
    dsimp [P]
    ring

  have hK : descentNormFactor t s = 16 * H := by
    rw [hm, hn]
    unfold descentNormFactor
    dsimp [H]
    ring

  have hnorm : P ^ 2 - 5 * (s ^ 2) ^ 2 = 4 * H := by
    have hid := descentNormFactor_identity t s
    have hsquare := congrArg (fun x : ℤ => x ^ 2) hP
    nlinarith [hid, hsquare, hK]

  exact ⟨P, H, hPodd, hP, hK, hnorm⟩


/-- Allocate the exceptional factor 5 to s. -/
theorem five_mul_fifth_power_allocation
    {s H u : ℤ}
    (hcop : IsCoprime s H)
    (hHFive : ¬ (5 : ℤ) ∣ H)
    (hproduct : s * H = 5 * u ^ 5) :
    ∃ w v : ℤ, s = 5 * w ^ 5 ∧ H = v ^ 5 := by
  have hcopFive : IsCoprime (5 : ℤ) H :=
    (integer_coprime_five_of_five_free hHFive).symm

  have hcopPower : IsCoprime (5 ^ 4 : ℤ) H :=
    hcopFive.pow_left

  have hcop625 : IsCoprime (625 : ℤ) H := by
    norm_num at hcopPower
    exact hcopPower

  have hcopScaled : IsCoprime (625 * s) H :=
    hcop625.mul_left hcop

  have hscaled : (625 * s) * H = (5 * u) ^ 5 := by
    calc
      (625 * s) * H = 625 * (s * H) := by ring
      _ = 625 * (5 * u ^ 5) := by rw [hproduct]
      _ = (5 * u) ^ 5 := by ring

  obtain ⟨e, he⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcopScaled (by decide : Odd (5 : ℕ)) hscaled

  obtain ⟨v, hv⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcopScaled.symm (by decide : Odd (5 : ℕ))
      (by simpa only [mul_comm] using hscaled)

  have heFive : (5 : ℤ) ∣ e := by
    have hp : Prime (5 : ℤ) := by norm_num
    have hpow : (5 : ℤ) ∣ e ^ 5 := by
      rw [← he]
      refine ⟨125 * s, ?_⟩
      ring
    exact hp.dvd_of_dvd_pow hpow

  obtain ⟨w, hw⟩ := heFive
  refine ⟨w, v, ?_, hv⟩
  rw [hw] at he
  nlinarith [he]

/-- Allocate fifth powers in the second descent's quartic. -/
theorem half_descent_fifth_power_allocation
    {t s H u : ℤ}
    (hts : IsCoprime t s)
    (htFive : ¬ (5 : ℤ) ∣ t)
    (hK : descentNormFactor t s = 16 * H)
    (hproduct : s * descentNormFactor t s = 80 * u ^ 5) :
    ∃ w v : ℤ, s = 5 * w ^ 5 ∧ H = v ^ 5 := by
  have hHdvd : H ∣ descentNormFactor t s := by
    refine ⟨16, ?_⟩
    rw [hK]
    ring

  have hKcop : IsCoprime (descentNormFactor t s) s :=
    descentNormFactor_coprime_coordinate hts

  have hHcop : IsCoprime H s :=
    hKcop.of_isCoprime_of_dvd_left hHdvd

  have hcop : IsCoprime s H :=
    hHcop.symm

  have hHFive : ¬ (5 : ℤ) ∣ H := by
    intro hH
    apply five_not_dvd_descentNormFactor htFive
    rw [hK]
    exact dvd_mul_of_dvd_right hH 16

  have hremaining : s * H = 5 * u ^ 5 := by
    rw [hK] at hproduct
    nlinarith [hproduct]

  exact five_mul_fifth_power_allocation
    hcop hHFive hremaining

/-- An odd fifth-power phi coefficient forces the root's
phi coefficient to be odd. -/
theorem odd_coordinate_of_odd_fifthPhiCoeff
    {r s : ℤ}
    (hD : Odd (fifthPhiCoeff r s)) :
    Odd s := by
  have hcast : (fifthPhiCoeff r s : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hD
    rw [hk]
    push_cast
    have hfinite : ∀ x : ZMod 2, 2 * x + 1 = 1 := by
      decide
    exact hfinite (k : ZMod 2)

  rw [fifthPhiCoeff_cast_two] at hcast

  have hz : ((s - 1 : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_sub, hcast]
    norm_num

  have hdiv : (2 : ℤ) ∣ s - 1 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz

  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k, ?_⟩
  linarith [hk]

/-- Coprimality makes the first half-norm coordinate 5-free. -/
theorem halfFifthNormSolution_five_not_dvd_first
    (S : HalfFifthNormSolution) :
    ¬ (5 : ℤ) ∣ S.P := by
  have hQFive : (5 : ℤ) ∣ S.Q := by
    refine ⟨5 * S.u ^ 5, ?_⟩
    rw [S.coefficient]
    ring

  intro hPFive
  obtain ⟨a, b, hab⟩ := S.coprime

  have hone : (5 : ℤ) ∣ 1 := by
    rw [← hab]
    exact dvd_add
      (dvd_mul_of_dvd_right hPFive a)
      (dvd_mul_of_dvd_right hQFive b)

  norm_num at hone

/-- Extract root coordinates with every property required
for the second descent. -/
theorem halfFifthNormSolution_root_properties
    (S : HalfFifthNormSolution) :
    ∃ t s : ℤ,
      IsCoprime t s ∧
      Odd t ∧
      Odd s ∧
      ¬ (5 : ℤ) ∣ t ∧
      0 < s ∧
      16 * S.P =
        t * (t ^ 4 + 50 * t ^ 2 * s ^ 2 + 125 * s ^ 4) ∧
      16 * S.Q = 5 * s * descentNormFactor t s := by
  obtain ⟨m, hm⟩ := S.odd_first
  obtain ⟨n, hn⟩ := S.odd_second

  have hP : S.P = 2 * (m - n) + S.Q := by
    linarith [hm, hn]

  have hQFive : (5 : ℤ) ∣ S.Q := by
    refine ⟨5 * S.u ^ 5, ?_⟩
    rw [S.coefficient]
    ring

  have hPFive := halfFifthNormSolution_five_not_dvd_first S

  obtain ⟨V, hV⟩ :=
    half_norm_factor_is_fifth_power_of_coprime
      hP S.coprime hPFive hQFive S.norm_eq

  obtain ⟨r, s, hcoords⟩ := exists_integer_coordinates V
  rw [hcoords, fifth_power_coordinates] at hV
  obtain ⟨hc, hQ⟩ := integer_coordinates_eq hV

  have hrs : IsCoprime r s := by
    have hrel : IsRelPrime r s := by
      intro d hdr hds
      obtain ⟨hC, hD⟩ :=
        common_dvd_fifth_coordinates hdr hds

      have hdc : d ∣ m - n := by
        rw [hc]
        exact hC

      have hdQ : d ∣ S.Q := by
        rw [hQ]
        exact hD

      have hdP : d ∣ S.P := by
        rw [hP]
        exact dvd_add
          (dvd_mul_of_dvd_right hdc 2)
          hdQ

      exact S.coprime.isUnit_of_dvd' hdP hdQ

    exact hrel.isCoprime

  have hsOdd : Odd s := by
    apply odd_coordinate_of_odd_fifthPhiCoeff
    rw [← hQ]
    exact S.odd_second

  let t : ℤ := 2 * r + s

  have htOdd : Odd t := by
    obtain ⟨k, hk⟩ := hsOdd
    refine ⟨r + k, ?_⟩
    dsimp [t]
    linarith [hk]

  have htwo : IsCoprime (2 : ℤ) s :=
    hsOdd.isCoprime_two.symm

  have h2r : IsCoprime (2 * r) s :=
    htwo.mul_left hrs

  have hts : IsCoprime t s := by
    have h := h2r.add_mul_right_left 1
    simpa [t] using h

  have hfirst :
      16 * S.P =
        t * (t ^ 4 + 50 * t ^ 2 * s ^ 2 + 125 * s ^ 4) := by
    rw [hP, hc, hQ]
    dsimp [t]
    unfold fifthConstant fifthPhiCoeff
    ring

  have hsecond :
      16 * S.Q = 5 * s * descentNormFactor t s := by
    rw [hQ]
    dsimp [t]
    unfold fifthPhiCoeff descentNormFactor
    ring

  have htFive : ¬ (5 : ℤ) ∣ t := by
    intro ht
    have hdiv : (5 : ℤ) ∣ 16 * S.P := by
      rw [hfirst]
      exact dvd_mul_of_dvd_left ht
        (t ^ 4 + 50 * t ^ 2 * s ^ 2 + 125 * s ^ 4)

    have hp : Prime (5 : ℤ) := by norm_num
    rcases hp.dvd_mul.mp hdiv with h16 | hPdiv
    · norm_num at h16
    · exact hPFive hPdiv

  have hsPositive : 0 < s := by
    have hpositive : 0 < 16 * S.Q := by
      nlinarith [S.positive_second]
    exact sqrtFive_root_second_positive hpositive hsecond

  exact ⟨t, s, hts, htOdd, hsOdd, htFive,
    hsPositive, hfirst, hsecond⟩

/-- The new half-norm coordinates remain coprime. -/
theorem half_descent_new_pair_coprime
    {t s P : ℤ}
    (hts : IsCoprime t s)
    (hP : 2 * P = t ^ 2 + 5 * s ^ 2) :
    IsCoprime P (s ^ 2) := by
  have hsquares : IsCoprime (t ^ 2) (s ^ 2) :=
    hts.pow_left.pow_right

  have hrel : IsRelPrime P (s ^ 2) := by
    intro d hdP hds

    have hdTwo : d ∣ 2 * P :=
      dvd_mul_of_dvd_right hdP 2
    have hdFive : d ∣ 5 * s ^ 2 :=
      dvd_mul_of_dvd_right hds 5

    have hdt : d ∣ t ^ 2 := by
      have h := dvd_sub hdTwo hdFive
      have heq : 2 * P - 5 * s ^ 2 = t ^ 2 := by
        linarith [hP]
      rw [heq] at h
      exact h

    exact hsquares.isUnit_of_dvd' hdt hds

  exact hrel.isCoprime

/-- Every half-norm solution produces a smaller one. -/
theorem halfFifthNormSolution_descent
    (S : HalfFifthNormSolution) :
    ∃ S' : HalfFifthNormSolution, S'.Q < S.Q := by
  obtain ⟨t, s, hts, htOdd, hsOdd, htFive,
      hsPositive, _hfirst, hsecond⟩ :=
    halfFifthNormSolution_root_properties S

  obtain ⟨P, H, hPodd, hP, hK, hnorm⟩ :=
    half_descent_new_norm_coordinates htOdd hsOdd

  have hproduct :
      s * descentNormFactor t s = 80 * S.u ^ 5 := by
    rw [S.coefficient] at hsecond
    nlinarith [hsecond]

  obtain ⟨w, v, hw, hv⟩ :=
    half_descent_fifth_power_allocation
      hts htFive hK hproduct

  have hsquareOdd : Odd (s ^ 2) := by
    obtain ⟨k, hk⟩ := hsOdd
    refine ⟨2 * k ^ 2 + 2 * k, ?_⟩
    rw [hk]
    ring

  have hcoefficient : s ^ 2 = 25 * (w ^ 2) ^ 5 := by
    rw [hw]
    ring

  have hnormNew :
      P ^ 2 - 5 * (s ^ 2) ^ 2 = 4 * v ^ 5 := by
    rw [hv] at hnorm
    exact hnorm

  let S' : HalfFifthNormSolution := {
    P := P
    Q := s ^ 2
    u := w ^ 2
    v := v
    coprime := half_descent_new_pair_coprime hts hP
    odd_first := hPodd
    odd_second := hsquareOdd
    coefficient := hcoefficient
    positive_second := by positivity
    norm_eq := hnormNew
  }

  refine ⟨S', ?_⟩
  change s ^ 2 < S.Q
  exact half_norm_second_coordinate_decreases
    hsPositive hsecond

/-- Infinite descent rules out the second auxiliary norm solution. -/
theorem no_halfFifthNormSolution
    (S : HalfFifthNormSolution) : False := by
  have hall :
      ∀ n : ℕ, ∀ T : HalfFifthNormSolution,
        T.Q.natAbs = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro T hmeasure
        obtain ⟨T', hsmaller⟩ := halfFifthNormSolution_descent T

        have hnat : T'.Q.natAbs < T.Q.natAbs := by
          have hcast :
              (T'.Q.natAbs : ℤ) < (T.Q.natAbs : ℤ) := by
            simpa only [
              Int.natCast_natAbs,
              abs_of_pos T'.positive_second,
              abs_of_pos T.positive_second
            ] using hsmaller
          exact_mod_cast hcast

        have hlt : T'.Q.natAbs < n := by
          omega

        exact ih T'.Q.natAbs hlt T' rfl

  exact hall S.Q.natAbs S rfl

/-- Odd normalized coordinates give the initial half-norm shape. -/
theorem odd_output_initial_norm_coordinates
    {q r : ℤ}
    (hqOdd : Odd q)
    (hrOdd : Odd r) :
    ∃ P H : ℤ,
      Odd P ∧
      2 * P = q ^ 2 + 25 * r ^ 2 ∧
      q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4 = 16 * H ∧
      P ^ 2 - 5 * (5 * r ^ 2) ^ 2 = 4 * H := by
  obtain ⟨m, hm⟩ := hqOdd
  obtain ⟨n, hn⟩ := hrOdd

  let P : ℤ :=
    2 * m ^ 2 + 2 * m + 50 * n ^ 2 + 50 * n + 13

  let H : ℤ :=
    m ^ 4 + 2 * m ^ 3
      + 50 * m ^ 2 * n ^ 2
      + 50 * m ^ 2 * n + 14 * m ^ 2
      + 50 * m * n ^ 2 + 50 * m * n + 13 * m
      + 125 * n ^ 4 + 250 * n ^ 3
      + 200 * n ^ 2 + 75 * n + 11

  have hPodd : Odd P := by
    refine ⟨m ^ 2 + m + 25 * n ^ 2 + 25 * n + 6, ?_⟩
    dsimp [P]
    ring

  have hP : 2 * P = q ^ 2 + 25 * r ^ 2 := by
    rw [hm, hn]
    dsimp [P]
    ring

  have hquartic :
      q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4 =
        16 * H := by
    rw [hm, hn]
    dsimp [H]
    ring

  have hnorm :
      P ^ 2 - 5 * (5 * r ^ 2) ^ 2 = 4 * H := by
    have h := odd_output_quartic_norm hP
    rw [hquartic] at h
    nlinarith [h]

  exact ⟨P, H, hPodd, hP, hquartic, hnorm⟩

/-- Allocate fifth powers in the initial odd-output equation. -/
theorem twenty_five_mul_fifth_power_allocation
    {r H z : ℤ}
    (hcop : IsCoprime (25 * r) H)
    (hproduct : (25 * r) * H = z ^ 5) :
    ∃ u v : ℤ, r = 125 * u ^ 5 ∧ H = v ^ 5 := by
  obtain ⟨e, he⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcop (by decide : Odd (5 : ℕ)) hproduct

  obtain ⟨v, hv⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcop.symm (by decide : Odd (5 : ℕ))
      (by simpa only [mul_comm] using hproduct)

  have heFive : (5 : ℤ) ∣ e := by
    have hp : Prime (5 : ℤ) := by norm_num
    have hpow : (5 : ℤ) ∣ e ^ 5 := by
      rw [← he]
      refine ⟨5 * r, ?_⟩
      ring
    exact hp.dvd_of_dvd_pow hpow

  obtain ⟨u, hu⟩ := heFive
  refine ⟨u, v, ?_, hv⟩
  rw [hu] at he
  nlinarith [he]

/-- Removing the factor 16 leaves H coprime to 25r. -/
theorem odd_output_initial_factors_coprime
    {q r H : ℤ}
    (hqr : IsCoprime q r)
    (hqFive : ¬ (5 : ℤ) ∣ q)
    (hquartic :
      q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4 = 16 * H) :
    IsCoprime (25 * r) H := by
  let R : ℤ :=
    q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4

  have hRr : IsCoprime R r := by
    have hpow : IsCoprime (q ^ 4) r := hqr.pow_left
    have h :=
      hpow.add_mul_right_left
        (50 * r * q ^ 2 + 125 * r ^ 3)
    convert h using 1
    dsimp [R]
    ring

  have hHdvd : H ∣ R := by
    refine ⟨16, ?_⟩
    dsimp [R]
    rw [hquartic]
    ring

  have hHr : IsCoprime H r :=
    hRr.of_isCoprime_of_dvd_left hHdvd

  have hHFive : ¬ (5 : ℤ) ∣ H := by
    intro hH

    have hR : (5 : ℤ) ∣ R := by
      dsimp [R]
      rw [hquartic]
      exact dvd_mul_of_dvd_right hH 16

    have hmultiple :
        (5 : ℤ) ∣ 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4 := by
      refine ⟨10 * r ^ 2 * q ^ 2 + 25 * r ^ 4, ?_⟩
      ring

    have hqpow : (5 : ℤ) ∣ q ^ 4 := by
      have h := dvd_sub hR hmultiple
      dsimp [R] at h
      simpa using h

    have hp : Prime (5 : ℤ) := by norm_num
    exact hqFive (hp.dvd_of_dvd_pow hqpow)

  have hHfive : IsCoprime H 5 :=
    integer_coprime_five_of_five_free hHFive

  have hHpower : IsCoprime H (5 ^ 2) :=
    hHfive.pow_right

  have hH25 : IsCoprime H 25 := by
    norm_num at hHpower
    exact hHpower

  exact (hH25.mul_right hHr).symm

/-- The initial half-norm coordinates are coprime. -/
theorem odd_output_initial_norm_pair_coprime
    {q r P : ℤ}
    (hqr : IsCoprime q r)
    (hqFive : ¬ (5 : ℤ) ∣ q)
    (hP : 2 * P = q ^ 2 + 25 * r ^ 2) :
    IsCoprime P (5 * r ^ 2) := by
  have hsquares : IsCoprime (q ^ 2) (r ^ 2) :=
    hqr.pow_left.pow_right

  have hPr : IsCoprime P (r ^ 2) := by
    have hrel : IsRelPrime P (r ^ 2) := by
      intro d hdP hdr

      have hdTwo : d ∣ 2 * P :=
        dvd_mul_of_dvd_right hdP 2
      have hdTwentyFive : d ∣ 25 * r ^ 2 :=
        dvd_mul_of_dvd_right hdr 25

      have hdq : d ∣ q ^ 2 := by
        have h := dvd_sub hdTwo hdTwentyFive
        have heq : 2 * P - 25 * r ^ 2 = q ^ 2 := by
          linarith [hP]
        rw [heq] at h
        exact h

      exact hsquares.isUnit_of_dvd' hdq hdr

    exact hrel.isCoprime

  have hPFive : ¬ (5 : ℤ) ∣ P := by
    intro hdP

    have hdTwo : (5 : ℤ) ∣ 2 * P :=
      dvd_mul_of_dvd_right hdP 2
    have hdTwentyFive : (5 : ℤ) ∣ 25 * r ^ 2 := by
      refine ⟨5 * r ^ 2, ?_⟩
      ring

    have hdq : (5 : ℤ) ∣ q ^ 2 := by
      have h := dvd_sub hdTwo hdTwentyFive
      have heq : 2 * P - 25 * r ^ 2 = q ^ 2 := by
        linarith [hP]
      rw [heq] at h
      exact h

    have hp : Prime (5 : ℤ) := by norm_num
    exact hqFive (hp.dvd_of_dvd_pow hdq)

  have hPfive : IsCoprime P 5 :=
    integer_coprime_five_of_five_free hPFive

  exact hPfive.mul_right hPr

/-- Rule out the normalized equation for the odd-output branch. -/
theorem no_odd_output_normalized_fifth_solution
    {q r z : ℤ}
    (hr : r ≠ 0)
    (hqr : IsCoprime q r)
    (hqFive : ¬ (5 : ℤ) ∣ q)
    (hqOdd : Odd q)
    (hrOdd : Odd r)
    (hproduct :
      (25 * r) *
        (q ^ 4 + 50 * r ^ 2 * q ^ 2 + 125 * r ^ 4) =
          16 * z ^ 5) :
    False := by
  obtain ⟨P, H, hPodd, hP, hquartic, hnorm⟩ :=
    odd_output_initial_norm_coordinates hqOdd hrOdd

  have hcop : IsCoprime (25 * r) H :=
    odd_output_initial_factors_coprime hqr hqFive hquartic

  have hremaining : (25 * r) * H = z ^ 5 := by
    rw [hquartic] at hproduct
    nlinarith [hproduct]

  obtain ⟨w, v, hrw, hv⟩ :=
    twenty_five_mul_fifth_power_allocation hcop hremaining

  have hQodd : Odd (5 * r ^ 2) := by
    obtain ⟨k, hk⟩ := hrOdd
    refine ⟨10 * k ^ 2 + 10 * k + 2, ?_⟩
    rw [hk]
    ring

  have hcoefficient :
      5 * r ^ 2 = 25 * (5 * w ^ 2) ^ 5 := by
    rw [hrw]
    ring

  have hpositive : 0 < 5 * r ^ 2 := by
    have hr2 : 0 < r ^ 2 := by positivity
    nlinarith

  have hnormNew :
      P ^ 2 - 5 * (5 * r ^ 2) ^ 2 = 4 * v ^ 5 := by
    rw [hv] at hnorm
    exact hnorm

  let S : HalfFifthNormSolution := {
    P := P
    Q := 5 * r ^ 2
    u := 5 * w ^ 2
    v := v
    coprime := odd_output_initial_norm_pair_coprime hqr hqFive hP
    odd_first := hPodd
    odd_second := hQodd
    coefficient := hcoefficient
    positive_second := hpositive
    norm_eq := hnormNew
  }

  exact no_halfFifthNormSolution S

/-- Primitive inputs with an odd sum give the required odd-output normalized coordinates. -/
theorem odd_output_coordinates_properties
    {a b q r : ℤ}
    (hab : IsCoprime a b)
    (hOddSum : Odd (a + b))
    (hcenter : a + b = 5 * r)
    (hgap : a - b = q) :
    IsCoprime q r ∧
      ¬ (5 : ℤ) ∣ q ∧
      Odd q ∧ Odd r := by
  obtain ⟨k, hk⟩ := hOddSum

  have hqOdd : Odd q := by
    refine ⟨k - b, ?_⟩
    linarith [hk, hgap]

  have hrOdd : Odd r := by
    refine ⟨r / 2, ?_⟩
    omega

  have hTwoA : 2 * a = 5 * r + q := by
    linarith [hcenter, hgap]
  have hTwoB : 2 * b = 5 * r - q := by
    linarith [hcenter, hgap]

  obtain ⟨u, v, huv⟩ := hab

  have hqr : IsCoprime q r := by
    have hrel : IsRelPrime q r := by
      intro d hdq hdr

      have hdFiveR : d ∣ 5 * r :=
        dvd_mul_of_dvd_right hdr 5

      have hdTwoA : d ∣ 2 * a := by
        rw [hTwoA]
        exact dvd_add hdFiveR hdq

      have hdTwoB : d ∣ 2 * b := by
        rw [hTwoB]
        exact dvd_sub hdFiveR hdq

      have hdTwo : d ∣ (2 : ℤ) := by
        have h := dvd_add
          (dvd_mul_of_dvd_right hdTwoA u)
          (dvd_mul_of_dvd_right hdTwoB v)
        have heq : u * (2 * a) + v * (2 * b) = 2 := by
          nlinarith [huv]
        rw [heq] at h
        exact h

      have hqTwo : IsCoprime q 2 :=
        hqOdd.isCoprime_two
      have hdCoprimeTwo : IsCoprime d 2 :=
        hqTwo.of_isCoprime_of_dvd_left hdq

      exact hdCoprimeTwo.isUnit_of_dvd' (dvd_refl d) hdTwo

    exact hrel.isCoprime

  have hqFive : ¬ (5 : ℤ) ∣ q := by
    intro hdq
    have hp : Prime (5 : ℤ) := by norm_num

    have cancelTwo :
        ∀ x : ℤ, (5 : ℤ) ∣ 2 * x → (5 : ℤ) ∣ x := by
      intro x hx
      rcases hp.dvd_mul.mp hx with htwo | hx
      · norm_num at htwo
      · exact hx

    have hdFiveR : (5 : ℤ) ∣ 5 * r :=
      dvd_mul_right 5 r

    have hda : (5 : ℤ) ∣ a := by
      apply cancelTwo
      rw [hTwoA]
      exact dvd_add hdFiveR hdq

    have hdb : (5 : ℤ) ∣ b := by
      apply cancelTwo
      rw [hTwoB]
      exact dvd_sub hdFiveR hdq

    have hone : (5 : ℤ) ∣ 1 := by
      rw [← huv]
      exact dvd_add
        (dvd_mul_of_dvd_right hda u)
        (dvd_mul_of_dvd_right hdb v)

    norm_num at hone

  exact ⟨hqr, hqFive, hqOdd, hrOdd⟩

/-- Close the primitive branch with an odd sum divisible by 5. -/
theorem no_primitive_fifth_solution_odd_sum_five_dvd_sum
    {a b z : ℤ}
    (hab : IsCoprime a b)
    (hOddSum : Odd (a + b))
    (hz : z ≠ 0)
    (hfive : (5 : ℤ) ∣ a + b)
    (hc : a ^ 5 + b ^ 5 = z ^ 5) :
    False := by
  obtain ⟨r, hr⟩ := hfive

  have hrNonzero : r ≠ 0 := by
    intro hzero
    have hsum : a + b = 0 := by
      rw [hr, hzero]
      ring
    have hb : b = -a := by linarith [hsum]
    have hzpow : z ^ 5 = 0 := by
      calc
        z ^ 5 = a ^ 5 + b ^ 5 := hc.symm
        _ = 0 := by rw [hb]; ring
    exact (pow_ne_zero 5 hz) hzpow

  obtain ⟨hqr, hqFive, hqOdd, hrOdd⟩ :=
    odd_output_coordinates_properties hab hOddSum hr
      (rfl : a - b = a - b)

  exact no_odd_output_normalized_fifth_solution
    hrNonzero hqr hqFive hqOdd hrOdd
    (odd_output_normalized_equation hr
      (rfl : a - b = a - b) hc)

/-- Combine the two primitive parity branches. -/
theorem no_primitive_fifth_solution_five_dvd_sum
    {a b z : ℤ}
    (hab : IsCoprime a b)
    (hz : z ≠ 0)
    (hfive : (5 : ℤ) ∣ a + b)
    (hc : a ^ 5 + b ^ 5 = z ^ 5) :
    False := by
  rcases Int.even_or_odd (a + b) with hsumEven | hsumOdd
  · rcases Int.even_or_odd a with haEven | haOdd
    · obtain ⟨k, hk⟩ := hsumEven
      obtain ⟨l, hl⟩ := haEven

      have hbEven : Even b := by
        refine ⟨k - l, ?_⟩
        linarith [hk, hl]

      have hda : (2 : ℤ) ∣ a :=
        even_iff_two_dvd.mp ⟨l, hl⟩
      have hdb : (2 : ℤ) ∣ b :=
        even_iff_two_dvd.mp hbEven

      obtain ⟨u, v, huv⟩ := hab
      have hone : (2 : ℤ) ∣ 1 := by
        rw [← huv]
        exact dvd_add
          (dvd_mul_of_dvd_right hda u)
          (dvd_mul_of_dvd_right hdb v)

      norm_num at hone

    · have hbOdd : Odd b :=
        (Int.even_add'.mp hsumEven).mp haOdd

      exact no_primitive_fifth_solution_odd_inputs_five_dvd_sum
        hab haOdd hbOdd hz hfive hc

  · exact no_primitive_fifth_solution_odd_sum_five_dvd_sum
      hab hsumOdd hz hfive hc

/-- Coprime inputs also give coprimality with the output. -/
theorem fifth_solution_coprime_output_right
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hb : b ≠ 0)
    (hc : a ^ 5 + b ^ 5 = c ^ 5) :
    IsCoprime b c := by
  apply isCoprime_of_prime_dvd
  · intro h
    exact hb h.1
  · intro p hp hpb hpc

    have hpaPow : p ∣ a ^ 5 := by
      have hd := dvd_sub
        (dvd_pow hpc (by decide : (5 : ℕ) ≠ 0))
        (dvd_pow hpb (by decide : (5 : ℕ) ≠ 0))
      have heq : c ^ 5 - b ^ 5 = a ^ 5 := by
        linarith [hc]
      rw [heq] at hd
      exact hd

    have hpa : p ∣ a :=
      hp.dvd_of_dvd_pow hpaPow

    exact hp.not_isUnit (hab.isUnit_of_dvd' hpa hpb)

/-- No nonzero coprime integer fifth-power solution exists. -/
theorem no_coprime_integer_fifth_solution
    {a b c : ℤ}
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc0 : c ≠ 0)
    (hab : IsCoprime a b) :
    a ^ 5 + b ^ 5 ≠ c ^ 5 := by
  intro hc

  have hbc :=
    fifth_solution_coprime_output_right hab hb hc
  have hac : IsCoprime a c :=
    fifth_solution_coprime_output_right hab.symm ha
      (by simpa only [add_comm] using hc)

  rcases Hire.five_dvd_some_of_sum_fifth_powers hc with
    haFive | hbFive | hcFive

  · have heq : c ^ 5 + (-b) ^ 5 = a ^ 5 := by
      calc
        c ^ 5 + (-b) ^ 5 = c ^ 5 - b ^ 5 := by ring
        _ = a ^ 5 := by linarith [hc]

    exact no_primitive_fifth_solution_five_dvd_sum
      hbc.symm.neg_right ha
      (five_dvd_sum_of_fifth_solution heq haFive)
      heq

  · have heq : c ^ 5 + (-a) ^ 5 = b ^ 5 := by
      calc
        c ^ 5 + (-a) ^ 5 = c ^ 5 - a ^ 5 := by ring
        _ = b ^ 5 := by linarith [hc]

    exact no_primitive_fifth_solution_five_dvd_sum
      hac.symm.neg_right hb
      (five_dvd_sum_of_fifth_solution heq hbFive)
      heq

  · exact no_primitive_fifth_solution_five_dvd_sum
      hab hc0
      (five_dvd_sum_of_fifth_solution hc hcFive)
      hc

/-- Fermat's Last Theorem for exponent five,
using the two descents constructed in this file. -/
theorem fermatLastTheoremFive_via_descent :
    FermatLastTheoremFor 5 := by
  apply fermatLastTheoremFor_iff_int.mpr
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc0 hgcd heq

  have hab : IsCoprime a b := by
    apply isCoprime_of_prime_dvd
    · rintro ⟨haz, _⟩
      exact ha haz
    · intro p hp hpa hpb

      have pow_dvd :
          ∀ x : ℤ, p ∣ x → p ∣ x ^ 5 := by
        intro x hx
        obtain ⟨k, hk⟩ := hx
        refine ⟨p ^ 4 * k ^ 5, ?_⟩
        rw [hk]
        ring

      have hpcPow : p ∣ c ^ 5 := by
        rw [← heq]
        exact dvd_add (pow_dvd a hpa) (pow_dvd b hpb)

      have hpc : p ∣ c :=
        hp.dvd_of_dvd_pow hpcPow

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

  exact no_coprime_integer_fifth_solution ha hb hc0 hab heq

end GoldenBridge

end Hire
