import Hire.FLT.FivePrelim

namespace Hire

namespace GoldenBridge

noncomputable def goldenPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 2 - Polynomial.X - 1

abbrev G := AdjoinRoot goldenPolynomial

noncomputable def phi : G :=
  AdjoinRoot.root goldenPolynomial

theorem phi_relation : phi ^ 2 = phi + 1 := by
  have h := AdjoinRoot.eval₂_root goldenPolynomial

  change Polynomial.eval₂
    (AdjoinRoot.of goldenPolynomial) phi
    (Polynomial.X ^ 2 - Polynomial.X - 1) = 0 at h

  simp only [
    Polynomial.eval₂_sub,
    Polynomial.eval₂_pow,
    Polynomial.eval₂_X,
    Polynomial.eval₂_one
  ] at h

  linear_combination h

noncomputable def delta : G := 2 * phi - 1

theorem delta_sq : delta ^ 2 = 5 := by
  unfold delta
  linear_combination 4 * phi_relation

theorem phi_mul_inverse : phi * (phi - 1) = 1 := by
  linear_combination phi_relation

/-- The golden-ratio element is an explicit unit. -/
noncomputable def phiUnit : Gˣ where
  val := phi
  inv := phi - 1
  val_inv := phi_mul_inverse
  inv_val := by
    rw [mul_comm]
    exact phi_mul_inverse

/-- Norm of the integer coordinates r + sφ. -/
def coordNorm (r s : ℤ) : ℤ :=
  r ^ 2 + r * s - s ^ 2

/-- Coordinate multiplication preserves the norm multiplicatively. -/
theorem coordNorm_mul (r s t u : ℤ) :
    coordNorm (r * t + s * u) (r * u + s * t + s * u) =
      coordNorm r s * coordNorm t u := by
  unfold coordNorm
  ring

theorem goldenPolynomial_monic : goldenPolynomial.Monic := by
  unfold goldenPolynomial
  monicity!

theorem goldenPolynomial_natDegree :
    goldenPolynomial.natDegree = 2 := by
  unfold goldenPolynomial
  compute_degree!

noncomputable def goldenPowerBasis : PowerBasis ℤ G :=
  AdjoinRoot.powerBasis' goldenPolynomial_monic

theorem goldenPowerBasis_dim : goldenPowerBasis.dim = 2 := by
  change goldenPolynomial.natDegree = 2
  exact goldenPolynomial_natDegree

theorem goldenPowerBasis_gen : goldenPowerBasis.gen = phi := by
  rfl

noncomputable def goldenBasis : Module.Basis (Fin 2) ℤ G :=
  goldenPowerBasis.basis.reindex
    (finCongr goldenPowerBasis_dim)

theorem goldenBasis_apply (i : Fin 2) :
    goldenBasis i = phi ^ (i : ℕ) := by
  unfold goldenBasis
  rw [Module.Basis.reindex_apply,
    goldenPowerBasis.basis_eq_pow,
    goldenPowerBasis_gen]
  rfl

/-- Every golden-ring element has integer coordinates. -/
theorem exists_integer_coordinates (W : G) :
    ∃ r s : ℤ, W = (r : G) + (s : G) * phi := by
  refine ⟨goldenBasis.repr W 0, goldenBasis.repr W 1, ?_⟩
  have h := goldenBasis.sum_repr W
  simp only [Fin.sum_univ_two, goldenBasis_apply] at h
  simpa [Algebra.smul_def] using h.symm

/-- Read the coordinates of r + sφ. -/
theorem goldenBasis_repr_coordinates (r s : ℤ) :
    (goldenBasis.repr ((r : G) + (s : G) * phi)) 0 = r ∧
    (goldenBasis.repr ((r : G) + (s : G) * phi)) 1 = s := by
  have hzero : goldenBasis 0 = 1 := by
    simp [goldenBasis_apply]
  have hone : goldenBasis 1 = phi := by
    simp [goldenBasis_apply]

  have heq :
      (r : G) + (s : G) * phi =
        r • goldenBasis 0 + s • goldenBasis 1 := by
    rw [hzero, hone]
    simp [Algebra.smul_def]

  rw [heq]
  simp only [map_add, map_smul, Module.Basis.repr_self]
  constructor <;> simp

/-- Equal golden-ring elements have equal coordinates. -/
theorem integer_coordinates_eq
    {r s t u : ℤ}
    (h : (r : G) + (s : G) * phi =
      (t : G) + (u : G) * phi) :
    r = t ∧ s = u := by
  have hzero :=
    congrArg (fun W : G => (goldenBasis.repr W) 0) h
  have hone :=
    congrArg (fun W : G => (goldenBasis.repr W) 1) h

  obtain ⟨hr, hs⟩ := goldenBasis_repr_coordinates r s
  obtain ⟨ht, hu⟩ := goldenBasis_repr_coordinates t u

  exact ⟨by simpa only [hr, ht] using hzero,
    by simpa only [hs, hu] using hone⟩

/-- Multiplication in integer coordinates. -/
theorem multiply_integer_coordinates (r s t u : ℤ) :
    ((r : G) + (s : G) * phi) *
        ((t : G) + (u : G) * phi) =
      ((r * t + s * u : ℤ) : G) +
        ((r * u + s * t + s * u : ℤ) : G) * phi := by
  push_cast
  linear_combination (s : G) * (u : G) * phi_relation

/-- The integer norm of a golden-ring element. -/
noncomputable def goldenNorm (W : G) : ℤ :=
  coordNorm (goldenBasis.repr W 0) (goldenBasis.repr W 1)

/-- The ring norm agrees with the coordinate formula. -/
theorem goldenNorm_coordinates (r s : ℤ) :
    goldenNorm ((r : G) + (s : G) * phi) =
      coordNorm r s := by
  unfold goldenNorm
  obtain ⟨hr, hs⟩ := goldenBasis_repr_coordinates r s
  rw [hr, hs]

/-- The golden-ring norm is multiplicative. -/
theorem goldenNorm_mul (W V : G) :
    goldenNorm (W * V) = goldenNorm W * goldenNorm V := by
  obtain ⟨r, s, rfl⟩ := exists_integer_coordinates W
  obtain ⟨t, u, rfl⟩ := exists_integer_coordinates V
  rw [multiply_integer_coordinates]
  rw [goldenNorm_coordinates,
    goldenNorm_coordinates, goldenNorm_coordinates]
  exact coordNorm_mul r s t u

theorem goldenNorm_one : goldenNorm 1 = 1 := by
  have h := goldenNorm_coordinates 1 0
  simpa [coordNorm] using h

theorem goldenNorm_phi : goldenNorm phi = -1 := by
  have h := goldenNorm_coordinates 0 1
  simpa [coordNorm] using h

/-- The coordinate norm vanishes only at the zero pair. -/
theorem coordNorm_eq_zero
    {r s : ℤ}
    (h : coordNorm r s = 0) :
    r = 0 ∧ s = 0 := by
  have hdisc : (2 * r + s) ^ 2 = 5 * s ^ 2 := by
    unfold coordNorm at h
    nlinarith [h]

  have hs : s = 0 := by
    by_contra hs
    have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast hs

    let q : ℚ := (2 * r + s : ℤ) / (s : ℚ)
    have hq : q ^ 2 = 5 := by
      dsimp [q]
      field_simp
      exact_mod_cast (by
        simpa only [mul_comm] using hdisc :
          (2 * r + s) ^ 2 = s ^ 2 * 5)

    have hreal : (q : ℝ) ^ 2 = 5 := by
      exact_mod_cast hq

    have hsqrt : Real.sqrt 5 = |(q : ℝ)| := by
      rw [← hreal]
      exact Real.sqrt_sq_eq_abs (q : ℝ)

    have hirr : Irrational (Real.sqrt 5) := by
      simpa using
        (by norm_num : Nat.Prime 5).irrational_sqrt

    apply hirr.ne_rat |q|
    simpa using hsqrt

  have hr : r = 0 := by
    rw [hs] at hdisc
    nlinarith [sq_nonneg r]

  exact ⟨hr, hs⟩

/-- A golden-ring element with norm zero is zero. -/
theorem eq_zero_of_goldenNorm_eq_zero
    {W : G}
    (h : goldenNorm W = 0) :
    W = 0 := by
  obtain ⟨r, s, rfl⟩ := exists_integer_coordinates W
  rw [goldenNorm_coordinates] at h
  obtain ⟨hr, hs⟩ := coordNorm_eq_zero h
  simp [hr, hs]

theorem goldenNorm_zero : goldenNorm 0 = 0 := by
  have h := goldenNorm_coordinates 0 0
  simpa [coordNorm] using h

/-- A zero product has a zero factor. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero
    {W V : G}
    (h : W * V = 0) :
    W = 0 ∨ V = 0 := by
  have hnorm : goldenNorm W * goldenNorm V = 0 := by
    rw [← goldenNorm_mul, h, goldenNorm_zero]

  rcases mul_eq_zero.mp hnorm with hW | hV
  · exact Or.inl (eq_zero_of_goldenNorm_eq_zero hW)
  · exact Or.inr (eq_zero_of_goldenNorm_eq_zero hV)

instance : NoZeroDivisors G where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro W V h
    exact GoldenBridge.eq_zero_or_eq_zero_of_mul_eq_zero h

/-- The ring is nontrivial: its norm distinguishes 1 from 0. -/
theorem golden_one_ne_zero : (1 : G) ≠ 0 := by
  intro h
  have hn := congrArg goldenNorm h
  rw [goldenNorm_one, goldenNorm_zero] at hn
  norm_num at hn

instance : Nontrivial G :=
  ⟨⟨1, 0, golden_one_ne_zero⟩⟩

instance : IsDomain G where
  mul_left_cancel_of_ne_zero := by
    intro a ha b c h
    change a * b = a * c at h
    have hprod : a * (b - c) = 0 := by
      rw [mul_sub, h, sub_self]
    rcases GoldenBridge.eq_zero_or_eq_zero_of_mul_eq_zero hprod with
      hzero | hzero
    · exact False.elim (ha hzero)
    · exact sub_eq_zero.mp hzero

  mul_right_cancel_of_ne_zero := by
    intro a ha b c h
    change b * a = c * a at h
    have hprod : (b - c) * a = 0 := by
      rw [sub_mul, h, sub_self]
    rcases GoldenBridge.eq_zero_or_eq_zero_of_mul_eq_zero hprod with
      hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact False.elim (ha hzero)

  exists_pair_ne := ⟨1, 0, golden_one_ne_zero⟩

/-- Conjugation sends φ to 1 - φ. -/
noncomputable def goldenConj (W : G) : G :=
  ((goldenBasis.repr W 0 + goldenBasis.repr W 1 : ℤ) : G) -
    (goldenBasis.repr W 1 : G) * phi

theorem goldenConj_coordinates (r s : ℤ) :
    goldenConj ((r : G) + (s : G) * phi) =
      ((r + s : ℤ) : G) + ((-s : ℤ) : G) * phi := by
  unfold goldenConj
  obtain ⟨hr, hs⟩ := goldenBasis_repr_coordinates r s
  rw [hr, hs]
  push_cast
  ring

/-- Multiplication by the conjugate gives the integer norm. -/
theorem mul_goldenConj (W : G) :
    W * goldenConj W = (goldenNorm W : G) := by
  obtain ⟨r, s, rfl⟩ := exists_integer_coordinates W
  rw [goldenConj_coordinates,
    multiply_integer_coordinates,
    goldenNorm_coordinates]
  unfold coordNorm
  push_cast
  ring

/-- Nonzero elements have nonzero integer norm. -/
theorem goldenNorm_ne_zero
    {V : G} (hV : V ≠ 0) :
    goldenNorm V ≠ 0 := by
  intro hnorm
  exact hV (eq_zero_of_goldenNorm_eq_zero hnorm)

/-- Rounding both coordinates to within 1/2
makes the absolute norm strictly less than 1. -/
theorem rounded_coordinate_norm_lt_one
    {x y : ℚ}
    (hx : |x| ≤ (1 / 2 : ℚ))
    (hy : |y| ≤ (1 / 2 : ℚ)) :
    |x ^ 2 + x * y - y ^ 2| < 1 := by
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  obtain ⟨hylo, hyhi⟩ := abs_le.mp hy

  have hxSquare : x ^ 2 ≤ (1 / 4 : ℚ) := by
    have hprod :
        0 ≤ ((1 / 2 : ℚ) - x) * ((1 / 2 : ℚ) + x) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]

  have hySquare : y ^ 2 ≤ (1 / 4 : ℚ) := by
    have hprod :
        0 ≤ ((1 / 2 : ℚ) - y) * ((1 / 2 : ℚ) + y) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]

  have hxyUpper : x * y ≤ (1 / 4 : ℚ) := by
    nlinarith [sq_nonneg (x - y)]

  have hxyLower : -(1 / 4 : ℚ) ≤ x * y := by
    nlinarith [sq_nonneg (x + y)]

  apply abs_lt.mpr
  constructor
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg y]

  /-- Round the rational coordinates of W / V. -/
noncomputable def goldenQuotient (W V : G) : G :=
  let numerator := W * goldenConj V
  let d : ℚ := goldenNorm V
  let r : ℤ := round ((goldenBasis.repr numerator 0 : ℚ) / d)
  let s : ℤ := round ((goldenBasis.repr numerator 1 : ℚ) / d)
  (r : G) + (s : G) * phi

noncomputable def goldenRemainder (W V : G) : G :=
  W - goldenQuotient W V * V

/-- The rounded quotient has coordinate-error norm below 1. -/
theorem rounded_quotient_error_bound (x y : ℚ) :
    |(x - (round x : ℚ)) ^ 2 +
      (x - (round x : ℚ)) * (y - (round y : ℚ)) -
      (y - (round y : ℚ)) ^ 2| < 1 := by
  exact rounded_coordinate_norm_lt_one
    (abs_sub_round x) (abs_sub_round y)

/-- Multiplying the remainder by the conjugate clears
the quotient's norm denominator. -/
theorem remainder_mul_conjugate (W V : G) :
    goldenRemainder W V * goldenConj V =
      W * goldenConj V -
        goldenQuotient W V * (goldenNorm V : G) := by
  unfold goldenRemainder
  rw [sub_mul, mul_assoc, mul_goldenConj]

theorem goldenNorm_intCast (d : ℤ) :
    goldenNorm (d : G) = d ^ 2 := by
  have h := goldenNorm_coordinates d 0
  simpa [coordNorm] using h

theorem goldenNorm_conjugate (V : G) :
    goldenNorm (goldenConj V) = goldenNorm V := by
  obtain ⟨r, s, rfl⟩ := exists_integer_coordinates V
  rw [goldenConj_coordinates,
    goldenNorm_coordinates, goldenNorm_coordinates]
  unfold coordNorm
  ring

/-- Clearing the denominator scales the rounding-error norm by d². -/
theorem rounded_integer_norm_bound
    (r s d : ℤ)
    (hd : d ≠ 0) :
    |coordNorm
      (r - round ((r : ℚ) / d) * d)
      (s - round ((s : ℚ) / d) * d)| < d ^ 2 := by
  let p : ℤ := round ((r : ℚ) / d)
  let q : ℤ := round ((s : ℚ) / d)
  let x : ℚ := (r : ℚ) / d - p
  let y : ℚ := (s : ℚ) / d - q

  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hdPos : 0 < (d : ℚ) ^ 2 := sq_pos_of_ne_zero hdQ

  have hsmall : |x ^ 2 + x * y - y ^ 2| < 1 := by
    exact rounded_quotient_error_bound ((r : ℚ) / d) ((s : ℚ) / d)

  have hscale :
      (coordNorm (r - p * d) (s - q * d) : ℚ) =
        (d : ℚ) ^ 2 * (x ^ 2 + x * y - y ^ 2) := by
    unfold coordNorm
    push_cast
    dsimp [x, y]
    field_simp

  have hbound :
      |(coordNorm (r - p * d) (s - q * d) : ℚ)| <
        (d : ℚ) ^ 2 := by
    rw [hscale, abs_mul,
      abs_of_pos hdPos]
    have hmul := mul_lt_mul_of_pos_left hsmall hdPos
    simpa only [mul_one] using hmul

  have hboundInt :
      |coordNorm (r - p * d) (s - q * d)| < d ^ 2 := by
    exact_mod_cast hbound

  simpa only [p, q] using hboundInt

/-- Division by a nonzero element gives a remainder
with strictly smaller absolute norm. -/
theorem goldenRemainder_norm_lt
    (W V : G)
    (hV : V ≠ 0) :
    |goldenNorm (goldenRemainder W V)| < |goldenNorm V| := by
  obtain ⟨r, s, hnum⟩ :=
    exists_integer_coordinates (W * goldenConj V)

  let d : ℤ := goldenNorm V
  let p : ℤ := round ((r : ℚ) / d)
  let q : ℤ := round ((s : ℚ) / d)

  have hd : d ≠ 0 := goldenNorm_ne_zero hV

  have hquot :
      goldenQuotient W V = (p : G) + (q : G) * phi := by
    unfold goldenQuotient
    rw [hnum]
    dsimp only
    obtain ⟨hr, hs⟩ := goldenBasis_repr_coordinates r s
    rw [hr, hs]

  have hscaled :
      goldenRemainder W V * goldenConj V =
        ((r - p * d : ℤ) : G) +
          ((s - q * d : ℤ) : G) * phi := by
    rw [remainder_mul_conjugate, hnum, hquot]
    change
      (r : G) + (s : G) * phi -
          ((p : G) + (q : G) * phi) * (d : G) =
        ((r - p * d : ℤ) : G) +
          ((s - q * d : ℤ) : G) * phi
    push_cast
    ring

  have hnorm :
      coordNorm (r - p * d) (s - q * d) =
        goldenNorm (goldenRemainder W V) * d := by
    calc
      coordNorm (r - p * d) (s - q * d) =
          goldenNorm (goldenRemainder W V * goldenConj V) := by
            rw [hscaled, goldenNorm_coordinates]
      _ = goldenNorm (goldenRemainder W V) * d := by
        rw [goldenNorm_mul, goldenNorm_conjugate]

  have hbound :
      |coordNorm (r - p * d) (s - q * d)| < d ^ 2 :=
    rounded_integer_norm_bound r s d hd

  rw [hnorm, abs_mul, ← sq_abs d, pow_two] at hbound

  have hdpos : 0 < |d| := abs_pos.mpr hd
  change |goldenNorm (goldenRemainder W V)| < |d|
  by_contra h
  have hge :
      |d| ≤ |goldenNorm (goldenRemainder W V)| := by
    omega
  nlinarith [hbound]

theorem goldenQuotient_zero (W : G) :
    goldenQuotient W 0 = 0 := by
  simp [goldenQuotient, goldenNorm_zero]

theorem quotient_mul_add_remainder (W V : G) :
    V * goldenQuotient W V + goldenRemainder W V = W := by
  unfold goldenRemainder
  ring

noncomputable instance : EuclideanDomain G where
  toCommRing := inferInstance
  toNontrivial := inferInstance

  quotient := goldenQuotient
  quotient_zero := goldenQuotient_zero
  remainder := goldenRemainder
  quotient_mul_add_remainder_eq := quotient_mul_add_remainder

  r := fun W V => (goldenNorm W).natAbs < (goldenNorm V).natAbs
  r_wellFounded :=
    (measure (fun W : G => (goldenNorm W).natAbs)).wf

  remainder_lt := by
    intro W V hV
    have hlt := goldenRemainder_norm_lt W V hV
    have hcast :
        ((goldenNorm (goldenRemainder W V)).natAbs : ℤ) <
          ((goldenNorm V).natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs] using hlt
    exact_mod_cast hcast

  mul_left_not_lt := by
    intro W V hV
    change ¬ (goldenNorm (W * V)).natAbs < (goldenNorm W).natAbs
    rw [goldenNorm_mul, Int.natAbs_mul]
    have hpositive : 0 < (goldenNorm V).natAbs :=
      Int.natAbs_pos.mpr (goldenNorm_ne_zero hV)
    have hone : 1 ≤ (goldenNorm V).natAbs := by omega
    have hle :
        (goldenNorm W).natAbs ≤
          (goldenNorm W).natAbs * (goldenNorm V).natAbs := by
      calc
        (goldenNorm W).natAbs =
            (goldenNorm W).natAbs * 1 := by simp
        _ ≤ (goldenNorm W).natAbs * (goldenNorm V).natAbs :=
          Nat.mul_le_mul_left _ hone
    exact not_lt_of_ge hle

noncomputable instance : IsPrincipalIdealRing G := by
    infer_instance

noncomputable def leftFactor (a b : ℤ) : G :=
  (a : G) ^ 2 + (b : G) ^ 2 - phi * (a : G) * (b : G)

noncomputable def rightFactor (a b : ℤ) : G :=
  (a : G) ^ 2 + (b : G) ^ 2 +
    (phi - 1) * (a : G) * (b : G)

theorem factors_mul (a b : ℤ) :
    leftFactor a b * rightFactor a b =
      (Hire.fifthFactor a b : G) := by
  unfold leftFactor rightFactor Hire.fifthFactor
  push_cast
  exact (Hire.fifth_factor_golden_split
    phi (a : G) (b : G) phi_relation).symm

theorem coprime_intCast
    {a b : ℤ} (hab : IsCoprime a b) :
    IsCoprime (a : G) (b : G) := by
  obtain ⟨u, v, huv⟩ := hab
  refine ⟨(u : G), (v : G), ?_⟩
  have h := congrArg (fun z : ℤ => (z : G)) huv
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using h

theorem common_dvd_factors_dvd_delta
    {a b : ℤ} {d : G}
    (hab : IsCoprime a b)
    (hL : d ∣ leftFactor a b)
    (hM : d ∣ rightFactor a b) :
    d ∣ delta := by
  change d ∣ 2 * phi - 1
  apply Hire.common_dvd_golden_factors_dvd_exceptional
    (coprime_intCast hab)
  · exact hL
  · exact hM

/-- Multiplication by the exceptional element in coordinates. -/
theorem delta_mul_coordinates (r s : ℤ) :
    delta * ((r : G) + (s : G) * phi) =
      ((-r + 2 * s : ℤ) : G) +
        ((2 * r + s : ℤ) : G) * phi := by
  unfold delta
  push_cast
  linear_combination 2 * (s : G) * phi_relation

/-- Delta divides an embedded integer precisely when 5 divides it. -/
theorem delta_dvd_intCast_iff (n : ℤ) :
    delta ∣ (n : G) ↔ (5 : ℤ) ∣ n := by
  constructor
  · intro hd
    obtain ⟨W, hn⟩ := hd
    obtain ⟨r, s, hW⟩ := exists_integer_coordinates W

    have heq :
        (n : G) + ((0 : ℤ) : G) * phi =
          ((-r + 2 * s : ℤ) : G) +
            ((2 * r + s : ℤ) : G) * phi := by
      calc
        (n : G) + ((0 : ℤ) : G) * phi = (n : G) := by
          simp only [Int.cast_zero, zero_mul, add_zero]
        _ = delta * W := hn
        _ = delta * ((r : G) + (s : G) * phi) :=
          congrArg (fun X : G => delta * X) hW
        _ = _ := delta_mul_coordinates r s

    have hcoords : n = -r + 2 * s ∧ 0 = 2 * r + s :=
      integer_coordinates_eq
        (r := n) (s := 0)
        (t := -r + 2 * s) (u := 2 * r + s) heq

    refine ⟨-r, ?_⟩
    omega

  · intro hd
    obtain ⟨k, hk⟩ := hd
    refine ⟨delta * (k : G), ?_⟩
    calc
      (n : G) = ((5 * k : ℤ) : G) :=
        congrArg (fun z : ℤ => (z : G)) hk
      _ = (5 : G) * (k : G) := Int.cast_mul 5 k
      _ = delta ^ 2 * (k : G) :=
        congrArg (fun X : G => X * (k : G)) delta_sq.symm
      _ = delta * (delta * (k : G)) := by
        rw [pow_two, mul_assoc]

/-- Three satisfies the golden polynomial modulo five. -/
theorem goldenPolynomial_at_three :
    Polynomial.eval₂ (Int.castRingHom (ZMod 5))
      (3 : ZMod 5) goldenPolynomial = 0 := by
  norm_num [goldenPolynomial,
    Polynomial.eval₂_sub,
    Polynomial.eval₂_pow,
    Polynomial.eval₂_X,
    Polynomial.eval₂_one]
  all_goals decide

/-- Reduction modulo the exceptional element. -/
noncomputable def goldenResidue : G →+* ZMod 5 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 5))
    (3 : ZMod 5) goldenPolynomial_at_three

theorem goldenResidue_phi :
    goldenResidue phi = 3 := by
  simp only [goldenResidue, phi, AdjoinRoot.lift_root]

/-- In coordinates, reduction sends r + sφ to r + 3s. -/
theorem goldenResidue_coordinates (r s : ℤ) :
    goldenResidue ((r : G) + (s : G) * phi) =
      (r : ZMod 5) + (s : ZMod 5) * 3 := by
  simp only [map_add, map_mul, map_intCast, goldenResidue_phi]

theorem goldenResidue_delta :
    goldenResidue delta = 0 := by
  unfold delta
  rw [map_sub, map_mul, map_ofNat, map_one, goldenResidue_phi]
  norm_num
  all_goals decide

/-- An element reduces to zero exactly when delta divides it. -/
theorem goldenResidue_eq_zero_iff
    (W : G) :
    goldenResidue W = 0 ↔ delta ∣ W := by
  constructor
  · intro hzero
    obtain ⟨r, s, rfl⟩ := exists_integer_coordinates W

    have hcast : ((r + 3 * s : ℤ) : ZMod 5) = 0 := by
      calc
        ((r + 3 * s : ℤ) : ZMod 5) =
            (r : ZMod 5) + (s : ZMod 5) * 3 := by
          push_cast
          ring
        _ = 0 := by
          simpa only [goldenResidue_coordinates] using hzero

    have hdiv : (5 : ℤ) ∣ r + 3 * s := by
      simpa using
        (ZMod.intCast_zmod_eq_zero_iff_dvd (r + 3 * s) 5).mp hcast

    obtain ⟨k, hk⟩ := hdiv
    refine ⟨((s - k : ℤ) : G) +
      ((2 * k - s : ℤ) : G) * phi, ?_⟩

    have hr : r = -(s - k) + 2 * (2 * k - s) := by
      omega
    have hs : s = 2 * (s - k) + (2 * k - s) := by
      ring

    rw [delta_mul_coordinates, ← hr, ← hs]

  · rintro ⟨V, hV⟩
    rw [hV, map_mul, goldenResidue_delta, zero_mul]

theorem goldenNorm_delta : goldenNorm delta = -5 := by
  have hcoords :
      delta = ((-1 : ℤ) : G) + ((2 : ℤ) : G) * phi := by
    unfold delta
    push_cast
    ring
  rw [hcoords, goldenNorm_coordinates]
  norm_num [coordNorm]

theorem delta_ne_zero : delta ≠ 0 := by
  intro hzero
  have h := congrArg goldenNorm hzero
  rw [goldenNorm_delta, goldenNorm_zero] at h
  norm_num at h

theorem delta_not_isUnit : ¬ IsUnit delta := by
  intro hunit
  have hmap : IsUnit (goldenResidue delta) :=
    hunit.map goldenResidue
  rw [goldenResidue_delta] at hmap

  obtain ⟨e, he⟩ := hmap
  have hbad : (0 : ZMod 5) = 1 := by
    simpa only [he, zero_mul] using e.val_inv

  exact (by decide : (0 : ZMod 5) ≠ 1) hbad

/-- The exceptional element is prime in the golden ring. -/
theorem delta_prime : Prime delta := by
  have split :
      ∀ x y : ZMod 5, x * y = 0 → x = 0 ∨ y = 0 := by
    decide

  refine ⟨delta_ne_zero, delta_not_isUnit, ?_⟩
  intro W V hdiv

  have hzero : goldenResidue (W * V) = 0 :=
    (goldenResidue_eq_zero_iff (W * V)).mpr hdiv
  rw [map_mul] at hzero

  rcases split (goldenResidue W) (goldenResidue V) hzero with hW | hV
  · exact Or.inl ((goldenResidue_eq_zero_iff W).mp hW)
  · exact Or.inr ((goldenResidue_eq_zero_iff V).mp hV)

theorem goldenResidue_leftFactor (a b : ℤ) :
    goldenResidue (leftFactor a b) =
      ((a + b : ℤ) : ZMod 5) ^ 2 := by
  unfold leftFactor
  simp only [map_add, map_sub, map_pow, map_mul,
    map_intCast, goldenResidue_phi]
  push_cast
  linear_combination
    -(a : ZMod 5) * (b : ZMod 5) *
      (by decide : (5 : ZMod 5) = 0)

/-- The exceptional element cannot divide the first factor in the 5-free branch. -/
theorem delta_not_dvd_leftFactor
    {a b : ℤ}
    (hS : ¬ (5 : ℤ) ∣ a + b) :
    ¬ delta ∣ leftFactor a b := by
  intro hdiv
  have hzero : goldenResidue (leftFactor a b) = 0 :=
    (goldenResidue_eq_zero_iff _).mpr hdiv
  rw [goldenResidue_leftFactor] at hzero

  have square_zero :
      ∀ x : ZMod 5, x ^ 2 = 0 → x = 0 := by
    decide
  have hsumZero : ((a + b : ℤ) : ZMod 5) = 0 :=
    square_zero _ hzero

  apply hS
  simpa using
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 5).mp hsumZero

/-- The golden factors are coprime in the 5-free branch. -/
theorem factors_coprime_of_five_free_sum
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : ¬ (5 : ℤ) ∣ a + b) :
    IsCoprime (leftFactor a b) (rightFactor a b) := by
  have hdeltaCop : IsCoprime delta (leftFactor a b) :=
    delta_prime.coprime_iff_not_dvd.mpr
      (delta_not_dvd_leftFactor hS)

  have hrel : IsRelPrime (leftFactor a b) (rightFactor a b) := by
    intro d hdL hdM
    have hdDelta : d ∣ delta :=
      common_dvd_factors_dvd_delta hab hdL hdM
    exact hdeltaCop.isUnit_of_dvd' hdDelta hdL

  exact hrel.isCoprime

/-- In the 5-free branch, each golden factor is associated to a fifth power. -/
theorem factors_associated_fifth_powers
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : ¬ (5 : ℤ) ∣ a + b)
    (hc : a ^ 5 + b ^ 5 = c ^ 5) :
    (∃ W : G, Associated (W ^ 5) (leftFactor a b)) ∧
    (∃ V : G, Associated (V ^ 5) (rightFactor a b)) := by
  obtain ⟨u, v, hu, hv⟩ :=
    Hire.fifth_factors_are_fifth_powers_of_five_free_sum hab hS hc

  have hcop : IsCoprime (leftFactor a b) (rightFactor a b) :=
    factors_coprime_of_five_free_sum hab hS

  have hproduct :
      leftFactor a b * rightFactor a b = (v : G) ^ 5 := by
    rw [factors_mul, hv, Int.cast_pow]

  constructor
  · exact exists_associated_pow_of_mul_eq_pow' hcop hproduct
  · exact exists_associated_pow_of_mul_eq_pow' hcop.symm
      (by simpa only [mul_comm] using hproduct)

def fifthConstant (r s : ℤ) : ℤ :=
  r ^ 5 + 10 * r ^ 3 * s ^ 2 +
    10 * r ^ 2 * s ^ 3 + 10 * r * s ^ 4 + 3 * s ^ 5

def fifthPhiCoeff (r s : ℤ) : ℤ :=
  5 * r ^ 4 * s + 10 * r ^ 3 * s ^ 2 +
    20 * r ^ 2 * s ^ 3 + 15 * r * s ^ 4 + 5 * s ^ 5

theorem fifth_power_coordinates (r s : ℤ) :
    ((r : G) + (s : G) * phi) ^ 5 =
      (fifthConstant r s : G) +
        (fifthPhiCoeff r s : G) * phi := by
  unfold fifthConstant fifthPhiCoeff
  push_cast
  linear_combination
    (10 * (r : G) ^ 3 * (s : G) ^ 2 +
      10 * (r : G) ^ 2 * (s : G) ^ 3 * (phi + 1) +
      5 * (r : G) * (s : G) ^ 4 * (phi ^ 2 + phi + 2) +
      (s : G) ^ 5 * (phi ^ 3 + phi ^ 2 + 2 * phi + 3)) *
      phi_relation

theorem five_dvd_fifthPhiCoeff (r s : ℤ) :
    (5 : ℤ) ∣ fifthPhiCoeff r s := by
  refine ⟨r ^ 4 * s + 2 * r ^ 3 * s ^ 2 +
    4 * r ^ 2 * s ^ 3 + 3 * r * s ^ 4 + s ^ 5, ?_⟩
  unfold fifthPhiCoeff
  ring

/-- The left golden factor has norm equal to the integer fifth factor. -/
theorem goldenNorm_leftFactor (a b : ℤ) :
    goldenNorm (leftFactor a b) = Hire.fifthFactor a b := by
  have hcoords :
      leftFactor a b =
        ((a ^ 2 + b ^ 2 : ℤ) : G) +
          ((-(a * b) : ℤ) : G) * phi := by
    unfold leftFactor
    push_cast
    ring
  rw [hcoords, goldenNorm_coordinates]
  unfold coordNorm Hire.fifthFactor
  ring

theorem goldenNorm_delta_sq :
    goldenNorm (delta ^ 2) = 25 := by
  rw [pow_two, goldenNorm_mul, goldenNorm_delta]
  norm_num

/-- The exceptional branch makes delta divide the left factor. -/
theorem delta_dvd_leftFactor_of_five_dvd_sum
    {a b : ℤ}
    (hS : (5 : ℤ) ∣ a + b) :
    delta ∣ leftFactor a b := by
  have hsumZero : ((a + b : ℤ) : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 5).mpr
      (by simpa using hS)

  apply (goldenResidue_eq_zero_iff _).mp
  rw [goldenResidue_leftFactor, hsumZero]
  norm_num

/-- In the coprime exceptional branch, delta² cannot divide
the left golden factor. -/
theorem delta_sq_not_dvd_leftFactor
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (5 : ℤ) ∣ a + b) :
    ¬ delta ^ 2 ∣ leftFactor a b := by
  rintro ⟨W, hW⟩
  have hnorm := congrArg goldenNorm hW
  rw [goldenNorm_leftFactor, goldenNorm_mul,
    goldenNorm_delta_sq] at hnorm

  apply Hire.twenty_five_not_dvd_fifthFactor hab hS
  exact ⟨goldenNorm W, hnorm⟩

theorem goldenNorm_rightFactor (a b : ℤ) :
    goldenNorm (rightFactor a b) = Hire.fifthFactor a b := by
  have hcoords :
      rightFactor a b =
        ((a ^ 2 + b ^ 2 - a * b : ℤ) : G) +
          ((a * b : ℤ) : G) * phi := by
    unfold rightFactor
    push_cast
    ring
  rw [hcoords, goldenNorm_coordinates]
  unfold coordNorm Hire.fifthFactor
  ring

theorem goldenResidue_rightFactor (a b : ℤ) :
    goldenResidue (rightFactor a b) =
      ((a + b : ℤ) : ZMod 5) ^ 2 := by
  unfold rightFactor
  simp only [map_add, map_sub, map_pow, map_mul,
    map_intCast, map_one, goldenResidue_phi]
  push_cast
  ring

theorem delta_dvd_rightFactor_of_five_dvd_sum
    {a b : ℤ}
    (hS : (5 : ℤ) ∣ a + b) :
    delta ∣ rightFactor a b := by
  have hsumZero : ((a + b : ℤ) : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 5).mpr
      (by simpa using hS)
  apply (goldenResidue_eq_zero_iff _).mp
  rw [goldenResidue_rightFactor, hsumZero]
  norm_num

theorem delta_sq_not_dvd_rightFactor
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (5 : ℤ) ∣ a + b) :
    ¬ delta ^ 2 ∣ rightFactor a b := by
  rintro ⟨W, hW⟩
  have hnorm := congrArg goldenNorm hW
  rw [goldenNorm_rightFactor, goldenNorm_mul,
    goldenNorm_delta_sq] at hnorm
  apply Hire.twenty_five_not_dvd_fifthFactor hab hS
  exact ⟨goldenNorm W, hnorm⟩

theorem exists_delta_free_quotient
    {X : G}
    (hdiv : delta ∣ X)
    (hsq : ¬ delta ^ 2 ∣ X) :
    ∃ Y : G, X = delta * Y ∧ ¬ delta ∣ Y := by
  obtain ⟨Y, hY⟩ := hdiv
  refine ⟨Y, hY, ?_⟩
  rintro ⟨Z, hZ⟩
  apply hsq
  refine ⟨Z, ?_⟩
  calc
    X = delta * Y := hY
    _ = delta * (delta * Z) :=
      congrArg (fun T : G => delta * T) hZ
    _ = delta ^ 2 * Z := by ring

/-- Removing the single exceptional factor leaves coprime quotients. -/
theorem delta_free_factor_quotients_coprime
    {a b : ℤ} {Y Z : G}
    (hab : IsCoprime a b)
    (hY : leftFactor a b = delta * Y)
    (hZ : rightFactor a b = delta * Z)
    (hYfree : ¬ delta ∣ Y) :
    IsCoprime Y Z := by
  have hdeltaCop : IsCoprime delta Y :=
    delta_prime.coprime_iff_not_dvd.mpr hYfree

  have hrel : IsRelPrime Y Z := by
    intro d hdY hdZ

    have hdL : d ∣ leftFactor a b := by
      rw [hY]
      exact dvd_mul_of_dvd_right hdY delta

    have hdM : d ∣ rightFactor a b := by
      rw [hZ]
      exact dvd_mul_of_dvd_right hdZ delta

    have hdDelta : d ∣ delta :=
      common_dvd_factors_dvd_delta hab hdL hdM

    exact hdeltaCop.isUnit_of_dvd' hdDelta hdY

  exact hrel.isCoprime

/-- Dividing both golden factors by delta removes the exceptional factor of 5 from their product. -/
theorem delta_free_factor_quotients_product
    {a b v : ℤ} {Y Z : G}
    (hY : leftFactor a b = delta * Y)
    (hZ : rightFactor a b = delta * Z)
    (hQ : Hire.fifthFactor a b = 5 * v ^ 5) :
    Y * Z = (v : G) ^ 5 := by
  apply mul_left_cancel₀ (pow_ne_zero 2 delta_ne_zero)
  calc
    delta ^ 2 * (Y * Z) =
        (delta * Y) * (delta * Z) := by ring
    _ = leftFactor a b * rightFactor a b := by
      rw [hY, hZ]
    _ = (Hire.fifthFactor a b : G) :=
      factors_mul a b
    _ = delta ^ 2 * (v : G) ^ 5 := by
      rw [hQ, delta_sq]
      norm_num

/-- Each exceptional-factor quotient is associated
to a fifth power in the golden ring. -/
theorem delta_free_factor_quotients_associated_fifth_powers
    {a b v : ℤ} {Y Z : G}
    (hab : IsCoprime a b)
    (hY : leftFactor a b = delta * Y)
    (hZ : rightFactor a b = delta * Z)
    (hYfree : ¬ delta ∣ Y)
    (hQ : Hire.fifthFactor a b = 5 * v ^ 5) :
    (∃ W : G, Associated (W ^ 5) Y) ∧
      (∃ V : G, Associated (V ^ 5) Z) := by
  have hcop : IsCoprime Y Z :=
    delta_free_factor_quotients_coprime
      hab hY hZ hYfree

  have hproduct : Y * Z = (v : G) ^ 5 :=
    delta_free_factor_quotients_product hY hZ hQ

  constructor
  · exact exists_associated_pow_of_mul_eq_pow'
      hcop hproduct
  · exact exists_associated_pow_of_mul_eq_pow'
      hcop.symm (by simpa only [mul_comm] using hproduct)

/-- A golden-ring unit has integer norm 1 or -1. -/
theorem goldenNorm_unit_eq_one_or_neg_one (e : Gˣ) :
    goldenNorm (e : G) = 1 ∨
      goldenNorm (e : G) = -1 := by
  have hmul :
      goldenNorm (e : G) *
        goldenNorm ((e⁻¹ : Gˣ) : G) = 1 := by
    have h := congrArg goldenNorm e.val_inv
    rw [goldenNorm_mul, goldenNorm_one] at h
    exact h

  let n : ℤˣ :=
    { val := goldenNorm (e : G)
      inv := goldenNorm ((e⁻¹ : Gˣ) : G)
      val_inv := hmul
      inv_val := by
        simpa only [mul_comm] using hmul }

  rcases Int.units_eq_one_or n with h | h
  · left
    exact congrArg (fun u : ℤˣ => (u : ℤ)) h
  · right
    exact congrArg (fun u : ℤˣ => (u : ℤ)) h

/-- The same norm restriction for an element known to be a unit. -/
theorem goldenNorm_eq_one_or_neg_one_of_isUnit
    {W : G} (hW : IsUnit W) :
    goldenNorm W = 1 ∨ goldenNorm W = -1 := by
  obtain ⟨e, he⟩ := hW
  rw [← he]
  exact goldenNorm_unit_eq_one_or_neg_one e

/-- Unit coordinates satisfy this integer equation. -/
theorem unit_coordinates_norm_eq_one_or_neg_one
    {r s : ℤ}
    (hunit : IsUnit ((r : G) + (s : G) * phi)) :
    r ^ 2 + r * s - s ^ 2 = 1 ∨
      r ^ 2 + r * s - s ^ 2 = -1 := by
  have h := goldenNorm_eq_one_or_neg_one_of_isUnit hunit
  rw [goldenNorm_coordinates] at h
  simpa only [coordNorm] using h

/-- Positive unit coordinates satisfy r < 2s. -/
theorem positive_unit_coordinates_bound
    {r s : ℤ}
    (_hr : 0 < r)
    (hs : 0 < s)
    (hN : coordNorm r s = 1 ∨ coordNorm r s = -1) :
    r < 2 * s := by
  by_contra h
  have hge : 2 * s ≤ r := by omega
  have hs1 : 1 ≤ s := by omega

  have hprod :
      0 ≤ (r - 2 * s) * (r + 3 * s) :=
    mul_nonneg (by omega) (by omega)

  unfold coordNorm at hN
  rcases hN with hN | hN
  · nlinarith [sq_nonneg (s - 1)]
  · nlinarith [sq_nonneg (s - 1)]

/-- Multiplication by phi inverse decreases the coordinate
measure when both coordinates are positive. -/
theorem positive_unit_coordinates_decrease
    {r s : ℤ}
    (hr : 0 < r)
    (hs : 0 < s)
    (hN : coordNorm r s = 1 ∨ coordNorm r s = -1) :
    |s - r| + |r| < |r| + |s| := by
  have hbound := positive_unit_coordinates_bound hr hs hN

  have hsmall : |s - r| < s := by
    apply abs_lt.mpr
    constructor <;> omega

  rw [abs_of_pos hr, abs_of_pos hs]
  omega

/-- Opposite-sign unit coordinates satisfy s < 2r. -/
theorem opposite_unit_coordinates_bound
    {r s : ℤ}
    (hr : 0 < r)
    (_hs : 0 < s)
    (hN : coordNorm r (-s) = 1 ∨
      coordNorm r (-s) = -1) :
    s < 2 * r := by
  by_contra h
  have hge : 2 * r ≤ s := by omega
  have hr1 : 1 ≤ r := by omega

  have hprod :
      0 ≤ (s - 2 * r) * (s + 3 * r) :=
    mul_nonneg (by omega) (by omega)

  unfold coordNorm at hN
  rcases hN with hN | hN
  · nlinarith [sq_nonneg (r - 1)]
  · nlinarith [sq_nonneg (r - 1)]

/-- Multiplication by phi decreases the coordinate measure for opposite-sign coordinates. -/
theorem opposite_unit_coordinates_decrease
    {r s : ℤ}
    (hr : 0 < r)
    (hs : 0 < s)
    (hN : coordNorm r (-s) = 1 ∨
      coordNorm r (-s) = -1) :
    |-s| + |r - s| < |r| + |-s| := by
  have hbound := opposite_unit_coordinates_bound hr hs hN

  have hsmall : |r - s| < r := by
    apply abs_lt.mpr
    constructor <;> omega

  rw [abs_neg, abs_of_pos hr, abs_of_pos hs]
  omega

/-- Negating both coordinates preserves the norm. -/
theorem coordNorm_neg_neg (r s : ℤ) :
    coordNorm (-r) (-s) = coordNorm r s := by
  unfold coordNorm
  ring

/-- A unit coordinate pair either has a zero coordinate, or multiplication by phi or phi inverse decreases its measure. -/
theorem unit_coordinates_reduce
    {r s : ℤ}
    (hN : coordNorm r s = 1 ∨ coordNorm r s = -1) :
    r = 0 ∨ s = 0 ∨
      |s - r| + |r| < |r| + |s| ∨
      |s| + |r + s| < |r| + |s| := by
  by_cases hr0 : r = 0
  · exact Or.inl hr0

  by_cases hs0 : s = 0
  · exact Or.inr (Or.inl hs0)

  have hNneg :
      coordNorm (-r) (-s) = 1 ∨
        coordNorm (-r) (-s) = -1 := by
    rw [coordNorm_neg_neg]
    exact hN

  right
  right

  rcases lt_or_gt_of_ne hr0 with hr | hr
  · rcases lt_or_gt_of_ne hs0 with hs | hs
    · -- Both negative: negate, then use the positive case.
      left
      have h :=
        positive_unit_coordinates_decrease
          (neg_pos.mpr hr) (neg_pos.mpr hs) hNneg
      have heq : -s - -r = -(s - r) := by ring
      simpa only [heq, abs_neg] using h

    · -- r negative, s positive.
      right
      have h :=
        opposite_unit_coordinates_decrease
          (neg_pos.mpr hr) hs hNneg
      have heq : -r - s = -(r + s) := by ring
      simpa only [heq, abs_neg] using h

  · rcases lt_or_gt_of_ne hs0 with hs | hs
    · -- r positive, s negative.
      right
      have hNop :
          coordNorm r (-(-s)) = 1 ∨
            coordNorm r (-(-s)) = -1 := by
        simpa only [neg_neg] using hN
      have h :=
        opposite_unit_coordinates_decrease
          hr (neg_pos.mpr hs) hNop
      simpa only [neg_neg, sub_neg_eq_add] using h

    · -- Both positive.
      left
      exact positive_unit_coordinates_decrease hr hs hN

/-- A unit with a zero coordinate is one of 1, -1, phi, or -phi. -/
theorem unit_coordinates_zero_case
    {r s : ℤ}
    (hN : coordNorm r s = 1 ∨ coordNorm r s = -1)
    (hzero : r = 0 ∨ s = 0) :
    (r : G) + (s : G) * phi = 1 ∨
      (r : G) + (s : G) * phi = -1 ∨
      (r : G) + (s : G) * phi = phi ∨
      (r : G) + (s : G) * phi = -phi := by
  rcases hzero with hr | hs
  · subst r
    have hsquare : s ^ 2 = 1 := by
      unfold coordNorm at hN
      rcases hN with h | h <;> nlinarith [sq_nonneg s]
    have hproduct : (s - 1) * (s + 1) = 0 := by
      nlinarith [hsquare]
    rcases mul_eq_zero.mp hproduct with h | h
    · have hs : s = 1 := by linarith
      subst s
      simp
    · have hs : s = -1 := by linarith
      subst s
      simp

  · subst s
    have hsquare : r ^ 2 = 1 := by
      unfold coordNorm at hN
      rcases hN with h | h <;> nlinarith [sq_nonneg r]
    have hproduct : (r - 1) * (r + 1) = 0 := by
      nlinarith [hsquare]
    rcases mul_eq_zero.mp hproduct with h | h
    · have hr : r = 1 := by linarith
      subst r
      simp
    · have hr : r = -1 := by linarith
      subst r
      simp

/-- An integer power of the explicit golden unit, viewed in G. -/
noncomputable def phiPower (k : ℤ) : G :=
  ((phiUnit ^ k : Gˣ) : G)

/-- Equal to a power of phi, possibly with an overall minus sign. -/
def IsSignedPhiPower (W : G) : Prop :=
  ∃ k : ℤ, W = phiPower k ∨ W = -phiPower k

theorem phiPower_add_one (k : ℤ) :
    phiPower (k + 1) = phiPower k * phi := by
  unfold phiPower
  rw [zpow_add_one]
  rfl

theorem phiPower_sub_one (k : ℤ) :
    phiPower (k - 1) = phiPower k * (phi - 1) := by
  unfold phiPower
  rw [zpow_sub_one]
  rfl

theorem signedPhiPower_mul_phi
    {W : G} (hW : IsSignedPhiPower W) :
    IsSignedPhiPower (W * phi) := by
  obtain ⟨k, hk⟩ := hW
  refine ⟨k + 1, ?_⟩
  rcases hk with hk | hk
  · left
    rw [hk, phiPower_add_one]
  · right
    rw [hk, neg_mul, phiPower_add_one]

theorem signedPhiPower_mul_phi_inverse
    {W : G} (hW : IsSignedPhiPower W) :
    IsSignedPhiPower (W * (phi - 1)) := by
  obtain ⟨k, hk⟩ := hW
  refine ⟨k - 1, ?_⟩
  rcases hk with hk | hk
  · left
    rw [hk, phiPower_sub_one]
  · right
    rw [hk, neg_mul, phiPower_sub_one]

/-- Convert the absolute-value decrease to a natural-number decrease. -/
theorem coordinate_measure_lt
    {r s t u : ℤ}
    (h : |t| + |u| < |r| + |s|) :
    t.natAbs + u.natAbs < r.natAbs + s.natAbs := by
  have hcast :
      ((t.natAbs + u.natAbs : ℕ) : ℤ) <
        ((r.natAbs + s.natAbs : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Int.natCast_natAbs] using h
  exact_mod_cast hcast

/-- Every coordinate pair of norm 1 or -1 represents
a signed integer power of phi. -/
theorem signedPhiPower_of_coordinate_norm
    {r s : ℤ}
    (hN : coordNorm r s = 1 ∨ coordNorm r s = -1) :
    IsSignedPhiPower ((r : G) + (s : G) * phi) := by
  have hclass :
      ∀ n : ℕ, ∀ r s : ℤ,
        r.natAbs + s.natAbs = n →
        (coordNorm r s = 1 ∨ coordNorm r s = -1) →
        IsSignedPhiPower ((r : G) + (s : G) * phi) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r s hm hN

      by_cases hz : r = 0 ∨ s = 0
      · rcases unit_coordinates_zero_case hN hz with
          h | h | h | h
        · refine ⟨0, Or.inl ?_⟩
          simpa [phiPower] using h
        · refine ⟨0, Or.inr ?_⟩
          simpa [phiPower] using h
        · refine ⟨1, Or.inl ?_⟩
          simpa [phiPower, phiUnit] using h
        · refine ⟨1, Or.inr ?_⟩
          simpa [phiPower, phiUnit] using h

      · rcases unit_coordinates_reduce hN with
          hr | hs | hdown | hdown
        · exact False.elim (hz (Or.inl hr))
        · exact False.elim (hz (Or.inr hs))

        · -- Reduce by multiplying by phi inverse.
          have hlt :
              (s - r).natAbs + r.natAbs < n := by
            have h := coordinate_measure_lt hdown
            simpa only [hm] using h

          have hnorm :
              coordNorm (s - r) r = -coordNorm r s := by
            unfold coordNorm
            ring

          have hNsmall :
              coordNorm (s - r) r = 1 ∨
                coordNorm (s - r) r = -1 := by
            rw [hnorm]
            rcases hN with hN | hN
            · right
              rw [hN]
            · left
              rw [hN]
              norm_num

          have hsmall :=
            ih ((s - r).natAbs + r.natAbs) hlt
              (s - r) r rfl hNsmall

          have hback :
              (((s - r : ℤ) : G) + (r : G) * phi) * phi =
                (r : G) + (s : G) * phi := by
            push_cast
            linear_combination (r : G) * phi_relation

          have hresult := signedPhiPower_mul_phi hsmall
          rw [hback] at hresult
          exact hresult

        · -- Reduce by multiplying by phi.
          have hlt :
              s.natAbs + (r + s).natAbs < n := by
            have h := coordinate_measure_lt hdown
            simpa only [hm] using h

          have hnorm :
              coordNorm s (r + s) = -coordNorm r s := by
            unfold coordNorm
            ring

          have hNsmall :
              coordNorm s (r + s) = 1 ∨
                coordNorm s (r + s) = -1 := by
            rw [hnorm]
            rcases hN with hN | hN
            · right
              rw [hN]
            · left
              rw [hN]
              norm_num

          have hsmall :=
            ih (s.natAbs + (r + s).natAbs) hlt
              s (r + s) rfl hNsmall

          have hback :
              ((s : G) + ((r + s : ℤ) : G) * phi) *
                  (phi - 1) =
                (r : G) + (s : G) * phi := by
            push_cast
            linear_combination
              ((r : G) + (s : G)) * phi_relation

          have hresult := signedPhiPower_mul_phi_inverse hsmall
          rw [hback] at hresult
          exact hresult

  exact hclass (r.natAbs + s.natAbs) r s rfl hN

/-- Every golden-ring unit is a signed integer power of phi. -/
theorem isUnit_isSignedPhiPower
    {W : G} (hW : IsUnit W) :
    IsSignedPhiPower W := by
  obtain ⟨r, s, hcoords⟩ := exists_integer_coordinates W
  have hunit : IsUnit ((r : G) + (s : G) * phi) := by
    rw [← hcoords]
    exact hW
  have hN := unit_coordinates_norm_eq_one_or_neg_one hunit
  rw [hcoords]
  exact signedPhiPower_of_coordinate_norm hN

theorem phiPower_add (k l : ℤ) :
    phiPower (k + l) = phiPower k * phiPower l := by
  unfold phiPower
  rw [zpow_add]
  rfl

theorem phiPower_natCast (j : ℕ) :
    phiPower (j : ℤ) = phi ^ j := by
  simp [phiPower, phiUnit]

theorem phiPower_five_mul (q : ℤ) :
    phiPower (5 * q) = phiPower q ^ 5 := by
  unfold phiPower
  rw [show 5 * q = q * (5 : ℤ) by ring, zpow_mul]
  rfl

/-- A unit times a fifth power has one of five unit twists.
The sign and all multiples of five in the unit exponent are absorbed into the fifth power. -/
theorem unit_mul_fifth_power_normal_form
    {Y U W : G}
    (hU : IsUnit U)
    (hY : Y = U * W ^ 5) :
    ∃ j : Fin 5, ∃ V : G,
      Y = phi ^ (j : ℕ) * V ^ 5 := by
  obtain ⟨k, hk⟩ := isUnit_isSignedPhiPower hU

  let j : ℕ := (k % 5).toNat
  let q : ℤ := k / 5

  have hrem_nonneg : 0 ≤ k % 5 :=
    Int.emod_nonneg k (by norm_num)
  have hrem_lt : k % 5 < 5 :=
    Int.emod_lt_of_pos k (by norm_num)

  have hjcast : (j : ℤ) = k % 5 := by
    dsimp [j]
    omega

  have hjlt : j < 5 := by
    omega

  have hk_split : k = (j : ℤ) + 5 * q := by
    dsimp [q]
    omega

  have hpower :
      phiPower k = phi ^ j * phiPower q ^ 5 := by
    rw [hk_split, phiPower_add,
      phiPower_natCast, phiPower_five_mul]

  rcases hk with hk | hk
  · refine ⟨⟨j, hjlt⟩, phiPower q * W, ?_⟩
    change Y = phi ^ j * (phiPower q * W) ^ 5
    rw [hY, hk, hpower]
    ring

  · refine ⟨⟨j, hjlt⟩, -(phiPower q * W), ?_⟩
    change Y = phi ^ j * (-(phiPower q * W)) ^ 5
    rw [hY, hk, hpower]
    ring

/-- An element associated to a fifth power has one of the five normalized unit twists. -/
theorem associated_fifth_power_normal_form
    {Y W : G}
    (hA : Associated (W ^ 5) Y) :
    ∃ j : Fin 5, ∃ V : G,
      Y = phi ^ (j : ℕ) * V ^ 5 := by
  obtain ⟨e, he⟩ := hA

  have hY : Y = (e : G) * W ^ 5 := by
    rw [← he]
    ring

  exact unit_mul_fifth_power_normal_form e.isUnit hY

end GoldenBridge

end Hire
