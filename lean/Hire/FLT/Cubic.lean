import Mathlib.Tactic
import Mathlib.NumberTheory.FLT.Basic

namespace Hire

/-- The second factor in the sum-of-cubes factorisation. -/
def cubeFactor (a b : ℤ) : ℤ :=
  a ^ 2 - a * b + b ^ 2

/-- Rewrite that factor as a square plus three times a square. -/
theorem four_mul_cubeFactor (a b : ℤ) :
    4 * cubeFactor a b = (2 * a - b) ^ 2 + 3 * b ^ 2 := by
  unfold cubeFactor
  ring

theorem sum_cubes_factorisation (a b : ℤ) :
    a ^ 3 + b ^ 3 = (a + b) * cubeFactor a b := by
  unfold cubeFactor
  ring

/-- Express the cubic factor using the sum a + b. -/
theorem cubeFactor_eq_sum_expression (a b : ℤ) :
    cubeFactor a b =
      (a + b) ^ 2 - 3 * (a + b) * b + 3 * b ^ 2 := by
  unfold cubeFactor
  ring

/-- The two factors differ from 3b² by a multiple of a + b. -/
theorem cubeFactor_sub_three_mul_sq (a b : ℤ) :
    cubeFactor a b - 3 * b ^ 2 =
      (a + b) * (a - 2 * b) := by
  unfold cubeFactor
  ring

/-- A common divisor of the two cubic factors divides 3b². -/
theorem common_dvd_cubeFactor_dvd_three_mul_sq
    {a b d : ℤ}
    (hS : d ∣ a + b)
    (hQ : d ∣ cubeFactor a b) :
    d ∣ 3 * b ^ 2 := by
  have hprod : d ∣ (a + b) * (a - 2 * b) :=
    dvd_mul_of_dvd_left hS (a - 2 * b)

  rw [← cubeFactor_sub_three_mul_sq a b] at hprod

  have hdiff :
      d ∣ cubeFactor a b - (cubeFactor a b - 3 * b ^ 2) :=
    dvd_sub hQ hprod

  simpa only [sub_sub_cancel] using hdiff

/-- For coprime a and b, a common divisor of the cubic factors divides 3. -/
theorem common_dvd_cubeFactor_dvd_three
    {a b d : ℤ}
    (hab : IsCoprime a b)
    (hS : d ∣ a + b)
    (hQ : d ∣ cubeFactor a b) :
    d ∣ 3 := by
  have hthree : d ∣ 3 * b ^ 2 :=
    common_dvd_cubeFactor_dvd_three_mul_sq hS hQ

  obtain ⟨u, v, huv⟩ := hab
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hthree

  refine ⟨3 * u ^ 2 * d * s ^ 2
    + 6 * u * s * (v - u) * b
    + (v - u) ^ 2 * t, ?_⟩

  calc
    (3 : ℤ) = 3 * (u * a + v * b) ^ 2 := by
      rw [huv]
      norm_num
    _ = 3 * u ^ 2 * (a + b) ^ 2
        + 6 * u * (a + b) * (v - u) * b
        + (v - u) ^ 2 * (3 * b ^ 2) := by ring
    _ = d * (3 * u ^ 2 * d * s ^ 2
        + 6 * u * s * (v - u) * b
        + (v - u) ^ 2 * t) := by
      rw [hs, ht]
      ring

/-- If 3 divides the first cubic factor, it divides the second. -/
theorem three_dvd_cubeFactor_of_dvd_sum
    {a b : ℤ}
    (hS : (3 : ℤ) ∣ a + b) :
    (3 : ℤ) ∣ cubeFactor a b := by
  have hidentity :
      cubeFactor a b =
        (a + b) * (a - 2 * b) + 3 * b ^ 2 := by
    unfold cubeFactor
    ring

  rw [hidentity]

  exact dvd_add
    (dvd_mul_of_dvd_left hS (a - 2 * b))
    (dvd_mul_right 3 (b ^ 2))

/-- When a + b = 3t, expose the factor of 3 in the cubic factor. -/
theorem cubeFactor_of_sum_eq_three_mul
    {a b t : ℤ}
    (hS : a + b = 3 * t) :
    cubeFactor a b =
      3 * (3 * t ^ 2 - 3 * t * b + b ^ 2) := by
  rw [cubeFactor_eq_sum_expression, hS]
  ring

/-- Coprimality prevents 3 from dividing b when it divides a + b. -/
theorem three_not_dvd_right_of_coprime_of_dvd_sum
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    ¬ (3 : ℤ) ∣ b := by
  intro hb

  have ha : (3 : ℤ) ∣ a := by
    have h := dvd_sub hS hb
    simpa using h

  obtain ⟨u, v, huv⟩ := hab

  have hone : (3 : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add
      (dvd_mul_of_dvd_right ha u)
      (dvd_mul_of_dvd_right hb v)

  norm_num at hone

/-- After extracting 3, the remaining factor is 3-free. -/
theorem three_not_dvd_remaining_factor
    {t b : ℤ}
    (hb : ¬ (3 : ℤ) ∣ b) :
    ¬ (3 : ℤ) ∣ (3 * t ^ 2 - 3 * t * b + b ^ 2) := by
  intro hF

  have hmultiple : (3 : ℤ) ∣ 3 * (t ^ 2 - t * b) :=
    dvd_mul_right 3 (t ^ 2 - t * b)

  have hsquare : (3 : ℤ) ∣ b * b := by
    have hd := dvd_sub hF hmultiple
    have heq :
        (3 * t ^ 2 - 3 * t * b + b ^ 2)
          - 3 * (t ^ 2 - t * b) = b * b := by
      ring
    rw [heq] at hd
    exact hd

  have hprime : Prime (3 : ℤ) := by norm_num

  rcases hprime.dvd_mul.mp hsquare with h | h
  · exact hb h
  · exact hb h

/-- If 3 divides the sum of coprime inputs, the cubic factor
is 3 times a 3-free integer. -/
theorem cubeFactor_eq_three_mul_three_free
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    ∃ F : ℤ, cubeFactor a b = 3 * F ∧ ¬ (3 : ℤ) ∣ F := by
  have hb : ¬ (3 : ℤ) ∣ b :=
    three_not_dvd_right_of_coprime_of_dvd_sum hab hS

  obtain ⟨t, ht⟩ := hS

  refine ⟨3 * t ^ 2 - 3 * t * b + b ^ 2, ?_, ?_⟩
  · exact cubeFactor_of_sum_eq_three_mul ht
  · exact three_not_dvd_remaining_factor hb

/-- For coprime inputs whose sum is divisible by 3,
the cubic factor is not divisible by 9. -/
theorem nine_not_dvd_cubeFactor
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    ¬ (9 : ℤ) ∣ cubeFactor a b := by
  obtain ⟨F, hQ, hF⟩ :=
    cubeFactor_eq_three_mul_three_free hab hS

  intro h9
  obtain ⟨k, hk⟩ := h9

  apply hF
  refine ⟨k, ?_⟩
  nlinarith [hQ, hk]

/-- In the branch where 3 divides a + b, a coprime cube solution
forces 9 to divide a + b. -/
theorem nine_dvd_sum_of_sum_cubes
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b)
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    (9 : ℤ) ∣ a + b := by
  have hprime : Prime (3 : ℤ) := by norm_num

  have hproduct : (a + b) * cubeFactor a b = c ^ 3 := by
    calc
      (a + b) * cubeFactor a b = a ^ 3 + b ^ 3 :=
        (sum_cubes_factorisation a b).symm
      _ = c ^ 3 := hc

  have hc3 : (3 : ℤ) ∣ c ^ 3 := by
    rw [← hproduct]
    exact dvd_mul_of_dvd_left hS (cubeFactor a b)

  have hcdvd : (3 : ℤ) ∣ c :=
    hprime.dvd_of_dvd_pow hc3

  obtain ⟨F, hQ, hF⟩ :=
    cubeFactor_eq_three_mul_three_free hab hS
  obtain ⟨t, ht⟩ := hS
  obtain ⟨k, hk⟩ := hcdvd

  have htf : t * F = 3 * k ^ 3 := by
    rw [ht, hQ, hk] at hproduct
    nlinarith [hproduct]

  have hdiv : (3 : ℤ) ∣ t * F := by
    rw [htf]
    exact dvd_mul_right 3 (k ^ 3)

  have ht3 : (3 : ℤ) ∣ t := by
    rcases hprime.dvd_mul.mp hdiv with h | h
    · exact h
    · exact False.elim (hF h)

  obtain ⟨u, hu⟩ := ht3
  refine ⟨u, ?_⟩
  rw [ht, hu]
  ring


/-- In an integer sum-of-cubes solution, at least one input
is divisible by 3. -/
theorem three_dvd_some_of_sum_cubes
    {a b c : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    (3 : ℤ) ∣ a ∨ (3 : ℤ) ∣ b ∨ (3 : ℤ) ∣ c := by
  by_contra h
  have ha3 : a % 3 ≠ 0 := by
    intro ha
    exact h (Or.inl (Int.dvd_iff_emod_eq_zero.mpr ha))
  have hb3 : b % 3 ≠ 0 := by
    intro hb
    exact h (Or.inr (Or.inl (Int.dvd_iff_emod_eq_zero.mpr hb)))
  have hc3 : c % 3 ≠ 0 := by
    intro hz
    exact h (Or.inr (Or.inr (Int.dvd_iff_emod_eq_zero.mpr hz)))

  set ra := a % 9 with hra
  set rb := b % 9 with hrb
  set rc := c % 9 with hrc

  have ha_bounds : 0 ≤ ra ∧ ra < 9 := by
    dsimp [ra]
    omega
  have hb_bounds : 0 ≤ rb ∧ rb < 9 := by
    dsimp [rb]
    omega
  have hc_bounds : 0 ≤ rc ∧ rc < 9 := by
    dsimp [rc]
    omega

  have hmod :
      ((ra ^ 3) % 9 + (rb ^ 3) % 9) % 9 =
        (rc ^ 3) % 9 := by
    have heq := congrArg (fun x : ℤ => x % 9) hc
    simpa only [
      ra, rb, rc,
      pow_succ, pow_zero, mul_one,
      Int.add_emod, Int.mul_emod, Int.emod_emod
    ] using heq

  have hal : 0 ≤ ra := ha_bounds.1
  have hau : ra < 9 := ha_bounds.2
  have hbl : 0 ≤ rb := hb_bounds.1
  have hbu : rb < 9 := hb_bounds.2
  have hcl : 0 ≤ rc := hc_bounds.1
  have hcu : rc < 9 := hc_bounds.2

  interval_cases ra using hal, hau <;>
    interval_cases rb using hbl, hbu <;>
    interval_cases rc using hcl, hcu <;>
    norm_num at hmod <;>
    omega

/-- Extract a cube from the 3-free part of the cubic factor,
once the required coprimality has been established. -/
theorem cubeFactor_eq_three_mul_cube_of_coprime
    {a b c F : ℤ}
    (hQ : cubeFactor a b = 3 * F)
    (hcop : IsCoprime (3 * (a + b)) F)
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    ∃ u : ℤ, cubeFactor a b = 3 * u ^ 3 := by
  have hproduct : (3 * (a + b)) * F = c ^ 3 := by
    calc
      (3 * (a + b)) * F =
          (a + b) * cubeFactor a b := by
            rw [hQ]
            ring
      _ = a ^ 3 + b ^ 3 :=
        (sum_cubes_factorisation a b).symm
      _ = c ^ 3 := hc

  obtain ⟨u, hu⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_right
      hcop (by decide : Odd (3 : ℕ)) hproduct

  refine ⟨u, ?_⟩
  rw [hQ, hu]

/-- The 3-free part is coprime to three times the other factor. -/
theorem coprime_three_mul_sum_remaining
    {a b F : ℤ}
    (hab : IsCoprime a b)
    (hQ : cubeFactor a b = 3 * F)
    (hF : ¬ (3 : ℤ) ∣ F) :
    IsCoprime (3 * (a + b)) F := by
  have hprime : Prime (3 : ℤ) := by norm_num

  have hthree : IsCoprime (3 : ℤ) F :=
    hprime.coprime_iff_not_dvd.mpr hF

  have hsum : IsCoprime (a + b) F := by
    have hrel : IsRelPrime (a + b) F := by
      intro d hdS hdF
      have hdQ : d ∣ cubeFactor a b := by
        rw [hQ]
        exact dvd_mul_of_dvd_right hdF 3
      have hd3 : d ∣ (3 : ℤ) :=
        common_dvd_cubeFactor_dvd_three hab hdS hdQ
      exact hthree.isUnit_of_dvd' hd3 hdF
    exact hrel.isCoprime

  exact hthree.mul_left hsum

/-- A coprime cube solution in the branch 3 ∣ a + b
forces the quadratic factor to be three times a cube. -/
theorem cubeFactor_eq_three_mul_cube
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b)
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    ∃ u : ℤ, cubeFactor a b = 3 * u ^ 3 := by
  obtain ⟨F, hQ, hF⟩ :=
    cubeFactor_eq_three_mul_three_free hab hS

  have hcop : IsCoprime (3 * (a + b)) F :=
    coprime_three_mul_sum_remaining hab hQ hF

  exact cubeFactor_eq_three_mul_cube_of_coprime hQ hcop hc

/-- In the oriented coprime cube-solution branch,
the sum is nine times a cube. -/
theorem sum_eq_nine_mul_cube
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b)
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    ∃ v : ℤ, a + b = 9 * v ^ 3 := by
  obtain ⟨F, hQ, hF⟩ :=
    cubeFactor_eq_three_mul_three_free hab hS

  have hcop : IsCoprime (3 * (a + b)) F :=
    coprime_three_mul_sum_remaining hab hQ hF

  have hproduct : (3 * (a + b)) * F = c ^ 3 := by
    calc
      (3 * (a + b)) * F =
          (a + b) * cubeFactor a b := by
            rw [hQ]
            ring
      _ = a ^ 3 + b ^ 3 :=
        (sum_cubes_factorisation a b).symm
      _ = c ^ 3 := hc

  obtain ⟨w, hw⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcop (by decide : Odd (3 : ℕ)) hproduct

  have hprime : Prime (3 : ℤ) := by norm_num

  have hw3 : (3 : ℤ) ∣ w ^ 3 := by
    rw [← hw]
    exact dvd_mul_right 3 (a + b)

  have hwdvd : (3 : ℤ) ∣ w :=
    hprime.dvd_of_dvd_pow hw3

  obtain ⟨v, hv⟩ := hwdvd
  refine ⟨v, ?_⟩
  rw [hv] at hw
  nlinarith [hw]

/-- Convert the extracted factors into a square-plus-three-square equation. -/
theorem extracted_cube_square_equation
    {a b u v : ℤ}
    (hQ : cubeFactor a b = 3 * u ^ 3)
    (hS : a + b = 9 * v ^ 3) :
    (a - b) ^ 2 + 27 * v ^ 6 = 4 * u ^ 3 := by
  have hid :
      4 * cubeFactor a b =
        (a + b) ^ 2 + 3 * (a - b) ^ 2 := by
    unfold cubeFactor
    ring
  rw [hQ, hS] at hid
  nlinarith [hid]

/-- A nonzero right-hand input forces both extracted parameters to be nonzero. -/
theorem extracted_cube_parameters_ne_zero
    {a b c u v : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc0 : c ≠ 0)
    (hQ : cubeFactor a b = 3 * u ^ 3)
    (hS : a + b = 9 * v ^ 3) :
    u ≠ 0 ∧ v ≠ 0 := by
  have hp : (a + b) * cubeFactor a b = c ^ 3 := by
    rw [← sum_cubes_factorisation, hc]

  rw [hQ, hS] at hp

  constructor
  · intro hu
    rw [hu] at hp
    simp only [zero_pow (by decide : (3 : ℕ) ≠ 0),
      mul_zero] at hp
    exact (pow_ne_zero 3 hc0) hp.symm
  · intro hv
    rw [hv] at hp
    simp only [zero_pow (by decide : (3 : ℕ) ≠ 0),
      mul_zero, zero_mul] at hp
    exact (pow_ne_zero 3 hc0) hp.symm

/-- The extracted cube parameters inherit coprimality. -/
theorem extracted_cube_parameters_coprime
    {a b u v : ℤ}
    (hab : IsCoprime a b)
    (hS3 : (3 : ℤ) ∣ a + b)
    (hQ : cubeFactor a b = 3 * u ^ 3)
    (hS : a + b = 9 * v ^ 3) :
    IsCoprime u v := by
  obtain ⟨F, hFQ, hF3⟩ :=
    cubeFactor_eq_three_mul_three_free hab hS3

  have hFu : F = u ^ 3 := by
    nlinarith [hFQ, hQ]

  have hcop : IsCoprime (3 * (a + b)) (u ^ 3) := by
    have h :=
      coprime_three_mul_sum_remaining hab hFQ hF3
    rw [hFu] at h
    exact h

  have hrel : IsRelPrime u v := by
    intro d hdu hdv
    obtain ⟨r, hr⟩ := hdu
    obtain ⟨s, hs⟩ := hdv

    have hdU : d ∣ u ^ 3 := by
      refine ⟨d ^ 2 * r ^ 3, ?_⟩
      rw [hr]
      ring

    have hdS : d ∣ 3 * (a + b) := by
      refine ⟨27 * d ^ 2 * s ^ 3, ?_⟩
      rw [hS, hs]
      ring

    exact hcop.isUnit_of_dvd' hdS hdU

  exact hrel.isCoprime

/-- The first coefficient of an Eisenstein cube. -/
def descentA (x y : ℤ) : ℤ :=
  x ^ 3 - 3 * x * y ^ 2 + y ^ 3

/-- The second coefficient of an Eisenstein cube. -/
def descentB (x y : ℤ) : ℤ :=
  3 * x * y * (x - y)

/-- The parametrised inputs have sum 9xy(x-y). -/
theorem descent_sum (x y : ℤ) :
    (descentA x y + descentB x y)
      + (2 * descentB x y - descentA x y) =
        9 * x * y * (x - y) := by
  unfold descentA descentB
  ring

/-- Their cubic factor is three times a cube. -/
theorem descent_cubeFactor (x y : ℤ) :
    cubeFactor
      (descentA x y + descentB x y)
      (2 * descentB x y - descentA x y) =
        3 * (x ^ 2 - x * y + y ^ 2) ^ 3 := by
  unfold cubeFactor descentA descentB
  ring

/-- A root of ω² + ω + 1 = 0 has cube equal to one. -/
theorem door_root_cube_eq_one
    {R : Type*} [CommRing R]
    {ω : R} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 := by
  calc
    ω ^ 3 = (ω - 1) * (ω ^ 2 + ω + 1) + 1 := by ring
    _ = 1 := by rw [hω]; ring

/-- The two Eisenstein factors multiply to the quadratic factor. -/
theorem door_eisenstein_pair
    {R : Type*} [CommRing R]
    (a b ω : R) (hω : ω ^ 2 + ω + 1 = 0) :
    (a + ω * b) * (a + ω ^ 2 * b) =
      a ^ 2 - a * b + b ^ 2 := by
  have hcube : ω ^ 3 = 1 :=
    door_root_cube_eq_one hω
  calc
    (a + ω * b) * (a + ω ^ 2 * b) =
        (a ^ 2 - a * b + b ^ 2)
          + a * b * (ω ^ 2 + ω + 1)
          + b ^ 2 * (ω ^ 3 - 1) := by ring
    _ = a ^ 2 - a * b + b ^ 2 := by
      rw [hω, hcube]
      ring

/-- Split the sum of cubes into three linear factors. -/
theorem door_eisenstein_sum_cubes
    {R : Type*} [CommRing R]
    (a b ω : R) (hω : ω ^ 2 + ω + 1 = 0) :
    a ^ 3 + b ^ 3 =
      (a + b) * ((a + ω * b) * (a + ω ^ 2 * b)) := by
  rw [door_eisenstein_pair a b ω hω]
  ring

/-- A common divisor of two linear factors divides ω - 1. -/
theorem door_common_dvd_eisenstein
    {R : Type*} [CommRing R]
    {a b ω d : R}
    (hab : IsCoprime a b)
    (hS : d ∣ a + b)
    (hE : d ∣ a + ω * b) :
    d ∣ ω - 1 := by
  have hb : d ∣ (ω - 1) * b := by
    have hd := dvd_sub hE hS
    have heq :
        (a + ω * b) - (a + b) = (ω - 1) * b := by
      ring
    rw [heq] at hd
    exact hd

  have ha : d ∣ (ω - 1) * a := by
    have hd := dvd_sub
      (dvd_mul_of_dvd_right hS (ω - 1)) hb
    have heq :
        (ω - 1) * (a + b) - (ω - 1) * b =
          (ω - 1) * a := by
      ring
    rw [heq] at hd
    exact hd

  obtain ⟨u, v, huv⟩ := hab
  have hd :
      d ∣ u * ((ω - 1) * a) + v * ((ω - 1) * b) :=
    dvd_add
      (dvd_mul_of_dvd_right ha u)
      (dvd_mul_of_dvd_right hb v)

  have heq :
      u * ((ω - 1) * a) + v * ((ω - 1) * b) =
        (ω - 1) * (u * a + v * b) := by
    ring
  rw [heq, huv, mul_one] at hd
  exact hd

/-- The exceptional factor squared is three times a unit. -/
theorem door_eisenstein_exceptional_sq
    {R : Type*} [CommRing R]
    {ω : R} (hω : ω ^ 2 + ω + 1 = 0) :
    (ω - 1) ^ 2 = -3 * ω := by
  calc
    (ω - 1) ^ 2 =
        -3 * ω + (ω ^ 2 + ω + 1) := by ring
    _ = -3 * ω := by rw [hω]; ring

end Hire
