import Hire.Doors
import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Round
import Mathlib.Data.ZMod.Basic

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

/-- The cube shortfall of a parametrised Pythagorean triple. -/
theorem pythagorean_cube_shortfall (m k : ℤ) :
    (m ^ 2 + k ^ 2) ^ 3
      - (m ^ 2 - k ^ 2) ^ 3
      - (2 * m * k) ^ 3 =
    2 * (k * (m - k)) ^ 2 *
      (3 * m ^ 2 + 2 * m * k + k ^ 2) := by
  ring

/-- The remaining quadratic factor is a square plus twice a square. -/
theorem pythagorean_cube_remaining_factor (m k : ℤ) :
    3 * m ^ 2 + 2 * m * k + k ^ 2 =
      (m + k) ^ 2 + 2 * m ^ 2 := by
  ring

/-- For a Pythagorean triple, the fourth-power shortfall
is twice the square of the product of its legs. -/
theorem pythagorean_fourth_shortfall
    {a b c : ℤ}
    (h : a ^ 2 + b ^ 2 = c ^ 2) :
    c ^ 4 - a ^ 4 - b ^ 4 = 2 * (a * b) ^ 2 := by
  calc
    c ^ 4 - a ^ 4 - b ^ 4 =
        (c ^ 2) ^ 2 - a ^ 4 - b ^ 4 := by ring
    _ = (a ^ 2 + b ^ 2) ^ 2 - a ^ 4 - b ^ 4 := by
      rw [← h]
    _ = 2 * (a * b) ^ 2 := by ring

/-- For a Pythagorean triple, the sixth-power shortfall
is three times the square of abc. -/
theorem pythagorean_sixth_shortfall
    {a b c : ℤ}
    (h : a ^ 2 + b ^ 2 = c ^ 2) :
    c ^ 6 - a ^ 6 - b ^ 6 = 3 * (a * b * c) ^ 2 := by
  calc
    c ^ 6 - a ^ 6 - b ^ 6 =
        (c ^ 2) ^ 3 - a ^ 6 - b ^ 6 := by ring
    _ = (a ^ 2 + b ^ 2) ^ 3 - a ^ 6 - b ^ 6 := by
      rw [← h]
    _ = 3 * (a * b) ^ 2 * (a ^ 2 + b ^ 2) := by ring
    _ = 3 * (a * b) ^ 2 * c ^ 2 := by rw [h]
    _ = 3 * (a * b * c) ^ 2 := by ring

/-- The fifth-power shortfall of a parametrised Pythagorean triple. -/
theorem pythagorean_fifth_shortfall (m k : ℤ) :
    (m ^ 2 + k ^ 2) ^ 5
      - (m ^ 2 - k ^ 2) ^ 5
      - (2 * m * k) ^ 5 =
    2 * (k * (m - k)) ^ 2 *
      (5 * m ^ 6
        + 10 * m ^ 5 * k
        + 15 * m ^ 4 * k ^ 2
        + 4 * m ^ 3 * k ^ 3
        + 3 * m ^ 2 * k ^ 4
        + 2 * m * k ^ 5
        + k ^ 6) := by
  ring

/-- Every odd exponent at least 3 has the same square factor
in the parametrised Pythagorean shortfall. -/
theorem pythagorean_odd_shortfall_factor
    (m k : ℤ) (j : ℕ) :
    ∃ R : ℤ,
      (m ^ 2 + k ^ 2) ^ (2 * j + 3)
        - (m ^ 2 - k ^ 2) ^ (2 * j + 3)
        - (2 * m * k) ^ (2 * j + 3) =
      2 * (k * (m - k)) ^ 2 * R := by
  let a := m ^ 2 - k ^ 2
  let b := 2 * m * k
  let c := m ^ 2 + k ^ 2
  let d := 2 * (k * (m - k)) ^ 2

  have hpyth : c ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [a, b, c]
    ring

  have hab :
      a ^ 2 * b ^ 2 = d * (2 * m ^ 2 * (m + k) ^ 2) := by
    dsimp [a, b, d]
    ring

  change ∃ R : ℤ,
    c ^ (2 * j + 3) - a ^ (2 * j + 3)
      - b ^ (2 * j + 3) = d * R

  induction j with
  | zero =>
      refine ⟨3 * m ^ 2 + 2 * m * k + k ^ 2, ?_⟩
      simpa [a, b, c, d] using pythagorean_cube_shortfall m k
  | succ j ih =>
      obtain ⟨R, hR⟩ := ih

      have hnext : 2 * (j + 1) + 3 = (2 * j + 3) + 2 := by
        omega
      have hsplit : 2 * j + 3 = (2 * j + 1) + 2 := by
        omega

      have ha :
          a ^ (2 * j + 3) = a ^ (2 * j + 1) * a ^ 2 := by
        rw [hsplit, pow_add]
      have hb :
          b ^ (2 * j + 3) = b ^ (2 * j + 1) * b ^ 2 := by
        rw [hsplit, pow_add]

      refine ⟨c ^ 2 * R
        + 2 * m ^ 2 * (m + k) ^ 2 *
          (a ^ (2 * j + 1) + b ^ (2 * j + 1)), ?_⟩

      calc
        c ^ (2 * (j + 1) + 3)
            - a ^ (2 * (j + 1) + 3)
            - b ^ (2 * (j + 1) + 3) =
          c ^ 2 *
              (c ^ (2 * j + 3) - a ^ (2 * j + 3)
                - b ^ (2 * j + 3))
            + a ^ 2 * b ^ 2 *
              (a ^ (2 * j + 1) + b ^ (2 * j + 1)) := by
                rw [hnext]
                rw [pow_add c (2 * j + 3) 2,
                    pow_add a (2 * j + 3) 2,
                    pow_add b (2 * j + 3) 2]
                rw [ha, hb, hpyth]
                ring
        _ = d * (c ^ 2 * R
            + 2 * m ^ 2 * (m + k) ^ 2 *
              (a ^ (2 * j + 1) + b ^ (2 * j + 1))) := by
                rw [hR, hab]
                ring

/-- The mismatch at exponent r + 2, including the correction
from the square mismatch. Here r = n + 2. -/
theorem power_mismatch_recurrence
    (a b c : ℤ) (n : ℕ) :
    c ^ (n + 4) - a ^ (n + 4) - b ^ (n + 4) =
      c ^ 2 * (c ^ (n + 2) - a ^ (n + 2) - b ^ (n + 2))
      + a ^ 2 * b ^ 2 * (a ^ n + b ^ n)
      + (c ^ 2 - a ^ 2 - b ^ 2) *
          (a ^ (n + 2) + b ^ (n + 2)) := by
  have hexp : n + 4 = (n + 2) + 2 := by omega
  rw [hexp]
  rw [pow_add c (n + 2) 2,
      pow_add a (n + 2) 2,
      pow_add b (n + 2) 2]
  rw [pow_add a n 2, pow_add b n 2]
  ring

/-- Split the cube mismatch into the square mismatch
and the gaps between c and the two inputs. -/
theorem cube_mismatch_identity (a b c : ℤ) :
    c ^ 3 - a ^ 3 - b ^ 3 =
      c * (c ^ 2 - a ^ 2 - b ^ 2)
        + a ^ 2 * (c - a)
        + b ^ 2 * (c - b) := by
  ring

/-- A cube solution forces the square excess
to compensate exactly for the gap terms. -/
theorem square_excess_eq_gaps_of_sum_cubes
    {a b c : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    c * (a ^ 2 + b ^ 2 - c ^ 2) =
      a ^ 2 * (c - a) + b ^ 2 * (c - b) := by
  have h := cube_mismatch_identity a b c
  nlinarith [hc, h]

/-- A positive cube solution with both inputs below c
must have a strictly positive square excess. -/
theorem square_excess_pos_of_sum_cubes
    {a b c : ℤ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hac : a < c)
    (hbc : b < c)
    (hcubes : a ^ 3 + b ^ 3 = c ^ 3) :
    0 < a ^ 2 + b ^ 2 - c ^ 2 := by
  have hgapA : 0 < a ^ 2 * (c - a) :=
    mul_pos (sq_pos_of_pos ha) (sub_pos.mpr hac)

  have hgapB : 0 < b ^ 2 * (c - b) :=
    mul_pos (sq_pos_of_pos hb) (sub_pos.mpr hbc)

  have hbalance :=
    square_excess_eq_gaps_of_sum_cubes hcubes

  have hcpos : 0 < c := lt_trans ha hac

  by_contra h
  have hexcess : a ^ 2 + b ^ 2 - c ^ 2 ≤ 0 :=
    le_of_not_gt h

  have hnonpos :
      c * (a ^ 2 + b ^ 2 - c ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hcpos) hexcess

  linarith

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

namespace EisensteinBridge

abbrev K := CyclotomicField 3 ℚ

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

abbrev E := NumberField.RingOfIntegers K

noncomputable instance : NumberField K :=
  IsCyclotomicExtension.numberField {3} ℚ K

noncomputable instance : IsPrincipalIdealRing E :=
  IsCyclotomicExtension.Rat.three_pid K

/-- Our chosen cube root of unity, viewed inside the integer ring. -/
noncomputable def omega : E :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

/-- The exceptional prime factor. -/
noncomputable def lambda : E :=
  omega - 1

theorem omega_relation :
    omega ^ 2 + omega + 1 = 0 := by
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  change hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0
  simpa only [IsCyclotomicExtension.Rat.Three.coe_eta] using
    (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one hζ)

theorem omega_cube :
    omega ^ 3 = 1 :=
  door_root_cube_eq_one omega_relation

theorem lambda_sq :
    lambda ^ 2 = -3 * omega := by
  unfold lambda
  exact door_eisenstein_exceptional_sq omega_relation

/-- Unlike our generic ring setup, this exceptional factor is prime. -/
theorem lambda_prime :
    Prime lambda := by
  change Prime
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1)
  exact
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

/-- Our factorisation now lives in the actual Eisenstein ring. -/
theorem sum_cubes (a b : E) :
    a ^ 3 + b ^ 3 =
      (a + b) *
        ((a + omega * b) * (a + omega ^ 2 * b)) :=
  door_eisenstein_sum_cubes a b omega omega_relation

/-- Integer Bézout coprimality survives in the Eisenstein ring. -/
theorem coprime_intCast
    {a b : ℤ} (hab : IsCoprime a b) :
    IsCoprime (a : E) (b : E) := by
  obtain ⟨u, v, huv⟩ := hab
  refine ⟨(u : E), (v : E), ?_⟩
  exact_mod_cast huv

/-- Our integer cube equation becomes an Eisenstein product equation. -/
theorem factorisation_of_int_solution
    {a b c : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    ((a : E) + (b : E)) *
      (((a : E) + omega * (b : E)) *
        ((a : E) + omega ^ 2 * (b : E))) =
      (c : E) ^ 3 := by
  have hcast :
      (a : E) ^ 3 + (b : E) ^ 3 = (c : E) ^ 3 := by
    exact_mod_cast hc
  calc
    _ = (a : E) ^ 3 + (b : E) ^ 3 :=
      (sum_cubes (a : E) (b : E)).symm
    _ = (c : E) ^ 3 := hcast

/-- A common divisor of the first two factors divides λ. -/
theorem common_dvd_int_factors
    {a b : ℤ} {d : E}
    (hab : IsCoprime a b)
    (hS : d ∣ (a : E) + (b : E))
    (hE : d ∣ (a : E) + omega * (b : E)) :
    d ∣ lambda := by
  unfold lambda
  exact door_common_dvd_eisenstein
    (coprime_intCast hab) hS hE

/-- Divisibility of the integer sum by 3 gives divisibility by λ². -/
theorem lambda_sq_dvd_int_sum
    {a b : ℤ}
    (hS : (3 : ℤ) ∣ a + b) :
    lambda ^ 2 ∣ (a : E) + (b : E) := by
  obtain ⟨t, ht⟩ := hS
  have hs :
      (a : E) + (b : E) = 3 * (t : E) := by
    exact_mod_cast ht

  refine ⟨-omega ^ 2 * (t : E), ?_⟩
  rw [hs, lambda_sq]
  calc
    3 * (t : E) = 3 * omega ^ 3 * (t : E) := by
      rw [omega_cube]
      ring
    _ = (-3 * omega) * (-omega ^ 2 * (t : E)) := by
      ring

/-- The first Eisenstein factor contains λ. -/
theorem lambda_dvd_int_linear_factor
    {a b : ℤ}
    (hS : (3 : ℤ) ∣ a + b) :
    lambda ∣ (a : E) + omega * (b : E) := by
  have hsum : lambda ∣ (a : E) + (b : E) :=
    dvd_trans
      (dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0))
      (lambda_sq_dvd_int_sum hS)

  have hid :
      (a : E) + omega * (b : E) =
        ((a : E) + (b : E)) + lambda * (b : E) := by
    unfold lambda
    ring

  rw [hid]
  exact dvd_add hsum (dvd_mul_right lambda (b : E))

/-- The exceptional prime divides the integer 3. -/
theorem lambda_dvd_three :
    lambda ∣ (3 : E) := by
  have hsq : lambda ^ 2 ∣ (3 : E) := by
    simpa using
      (lambda_sq_dvd_int_sum
        (a := (3 : ℤ)) (b := (0 : ℤ)) (by norm_num))
  exact dvd_trans
    (dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0))
    hsq

/-- For ordinary integers, λ-divisibility is exactly 3-divisibility. -/
theorem lambda_dvd_intCast_iff (n : ℤ) :
    lambda ∣ (n : E) ↔ (3 : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra h3
    have hp : Prime (3 : ℤ) := by norm_num
    have hcopZ : IsCoprime (3 : ℤ) n :=
      hp.coprime_iff_not_dvd.mpr h3
    have hcopE : IsCoprime (3 : E) (n : E) :=
      coprime_intCast hcopZ
    exact lambda_prime.not_isUnit
      (hcopE.isUnit_of_dvd' lambda_dvd_three hn)
  · intro hn
    obtain ⟨t, ht⟩ := hn
    have hcast : (n : E) = 3 * (t : E) := by
      exact_mod_cast ht
    rw [hcast]
    exact dvd_mul_of_dvd_left lambda_dvd_three (t : E)

/-- For coprime integer inputs with 3 dividing their sum,
the linear factor contains no second factor of λ. -/
theorem lambda_sq_not_dvd_int_linear_factor
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    ¬ lambda ^ 2 ∣ (a : E) + omega * (b : E) := by
  have hbZ : ¬ (3 : ℤ) ∣ b :=
    three_not_dvd_right_of_coprime_of_dvd_sum hab hS
  have hbE : ¬ lambda ∣ (b : E) := by
    intro hb
    exact hbZ ((lambda_dvd_intCast_iff b).mp hb)

  intro hfactor
  have hsum : lambda ^ 2 ∣ (a : E) + (b : E) :=
    lambda_sq_dvd_int_sum hS
  have hd := dvd_sub hfactor hsum

  have hid :
      ((a : E) + omega * (b : E))
        - ((a : E) + (b : E)) =
          lambda * (b : E) := by
    unfold lambda
    ring

  rw [hid, pow_two] at hd
  exact hbE
    ((mul_dvd_mul_iff_left lambda_prime.ne_zero).mp hd)

/-- Remove λ from the linear factor; the quotient is λ-free. -/
theorem exists_lambda_free_linear_quotient
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    ∃ Y : E,
      (a : E) + omega * (b : E) = lambda * Y ∧
      ¬ lambda ∣ Y := by
  obtain ⟨Y, hY⟩ := lambda_dvd_int_linear_factor hS
  refine ⟨Y, hY, ?_⟩

  intro hd
  obtain ⟨t, ht⟩ := hd
  apply lambda_sq_not_dvd_int_linear_factor hab hS
  refine ⟨t, ?_⟩
  rw [hY, ht]
  ring

/-- Remove λ from the second linear factor as well. -/
theorem exists_lambda_free_second_quotient
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    ∃ Z : E,
      (a : E) + omega ^ 2 * (b : E) = lambda * Z ∧
      ¬ lambda ∣ Z := by
  have hS' : (3 : ℤ) ∣ b + a := by
    simpa only [add_comm] using hS

  obtain ⟨Y, hY, hfree⟩ :=
    exists_lambda_free_linear_quotient hab.symm hS'

  refine ⟨omega ^ 2 * Y, ?_, ?_⟩
  · calc
      (a : E) + omega ^ 2 * (b : E) =
          omega ^ 3 * (a : E) + omega ^ 2 * (b : E) := by
            rw [omega_cube]
            ring
      _ = omega ^ 2 * ((b : E) + omega * (a : E)) := by
        ring
      _ = lambda * (omega ^ 2 * Y) := by
        rw [hY]
        ring

  · intro hd
    have hd' := dvd_mul_of_dvd_right hd omega
    have heq : omega * (omega ^ 2 * Y) = Y := by
      calc
        omega * (omega ^ 2 * Y) = omega ^ 3 * Y := by ring
        _ = Y := by rw [omega_cube]; ring
    rw [heq] at hd'
    exact hfree hd'

/-- A common divisor of the two Eisenstein linear factors divides λ. -/
theorem common_dvd_two_int_linear_factors
    {a b : ℤ} {d : E}
    (hab : IsCoprime a b)
    (h₁ : d ∣ (a : E) + omega * (b : E))
    (h₂ : d ∣ (a : E) + omega ^ 2 * (b : E)) :
    d ∣ lambda := by
  have hfour : omega ^ 4 = omega := by
    calc
      omega ^ 4 = omega ^ 3 * omega := by ring
      _ = omega := by rw [omega_cube]; ring

  have hroot : omega ^ 2 + omega = -1 := by
    linear_combination omega_relation

  have hid :
      (-omega) * ((a : E) + omega * (b : E))
        - omega ^ 2 * ((a : E) + omega ^ 2 * (b : E)) =
          (a : E) + (b : E) := by
    calc
      _ = -(omega ^ 2 + omega) * (a : E)
          - (omega ^ 4 + omega ^ 2) * (b : E) := by ring
      _ = (a : E) + (b : E) := by
        rw [hfour, add_comm omega (omega ^ 2), hroot]
        ring

  have hsum : d ∣ (a : E) + (b : E) := by
    have hd := dvd_sub
      (dvd_mul_of_dvd_right h₁ (-omega))
      (dvd_mul_of_dvd_right h₂ (omega ^ 2))
    rw [hid] at hd
    exact hd

  exact common_dvd_int_factors hab hsum h₁

/-- After removing λ, the two quotients are coprime. -/
theorem linear_quotients_coprime
    {a b : ℤ} {Y Z : E}
    (hab : IsCoprime a b)
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hZ : (a : E) + omega ^ 2 * (b : E) = lambda * Z)
    (hYfree : ¬ lambda ∣ Y) :
    IsCoprime Y Z := by
  have hcop : IsCoprime lambda Y :=
    lambda_prime.coprime_iff_not_dvd.mpr hYfree

  have hrel : IsRelPrime Y Z := by
    intro d hdY hdZ

    have h₁ : d ∣ (a : E) + omega * (b : E) := by
      rw [hY]
      exact dvd_mul_of_dvd_right hdY lambda

    have h₂ : d ∣ (a : E) + omega ^ 2 * (b : E) := by
      rw [hZ]
      exact dvd_mul_of_dvd_right hdZ lambda

    have hdLambda : d ∣ lambda :=
      common_dvd_two_int_linear_factors hab h₁ h₂

    exact hcop.isUnit_of_dvd' hdLambda hdY

  exact hrel.isCoprime
/-- The reduced factors, with a unit adjustment, multiply to a cube. -/
theorem adjusted_quotients_product
    {a b u : ℤ} {Y Z : E}
    (hQ : cubeFactor a b = 3 * u ^ 3)
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hZ : (a : E) + omega ^ 2 * (b : E) = lambda * Z) :
    (-omega * Y) * Z = (u : E) ^ 3 := by
  have hQcast :
      (a : E) ^ 2 - (a : E) * (b : E) + (b : E) ^ 2 =
        3 * (u : E) ^ 3 := by
    unfold cubeFactor at hQ
    exact_mod_cast hQ

  have hprod :
      (3 : E) * ((-omega * Y) * Z) =
        3 * (u : E) ^ 3 := by
    calc
      _ = lambda ^ 2 * (Y * Z) := by
        rw [lambda_sq]
        ring
      _ = (lambda * Y) * (lambda * Z) := by ring
      _ = ((a : E) + omega * (b : E)) *
          ((a : E) + omega ^ 2 * (b : E)) := by
        rw [← hY, ← hZ]
      _ = (a : E) ^ 2 - (a : E) * (b : E)
          + (b : E) ^ 2 :=
        door_eisenstein_pair (a : E) (b : E)
          omega omega_relation
      _ = 3 * (u : E) ^ 3 := hQcast

  exact mul_left_cancel₀ (by norm_num : (3 : E) ≠ 0) hprod

/-- Multiplying the first quotient by -ω preserves coprimality. -/
theorem adjusted_quotients_coprime
    {Y Z : E}
    (hcop : IsCoprime Y Z) :
    IsCoprime (-omega * Y) Z := by
  obtain ⟨r, s, hrs⟩ := hcop
  refine ⟨r * (-omega ^ 2), s, ?_⟩
  calc
    (r * (-omega ^ 2)) * (-omega * Y) + s * Z =
        omega ^ 3 * (r * Y) + s * Z := by ring
    _ = 1 := by
      rw [omega_cube, one_mul]
      exact hrs

/-- Both adjusted quotients are cubes up to unit multipliers. -/
theorem adjusted_quotients_are_cubes
    {a b u : ℤ} {Y Z : E}
    (hab : IsCoprime a b)
    (hQ : cubeFactor a b = 3 * u ^ 3)
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hZ : (a : E) + omega ^ 2 * (b : E) = lambda * Z)
    (hYfree : ¬ lambda ∣ Y) :
    (∃ W : E, Associated (W ^ 3) (-omega * Y)) ∧
    (∃ V : E, Associated (V ^ 3) Z) := by
  have hcop : IsCoprime (-omega * Y) Z :=
    adjusted_quotients_coprime
      (linear_quotients_coprime hab hY hZ hYfree)

  have hprod : (-omega * Y) * Z = (u : E) ^ 3 :=
    adjusted_quotients_product hQ hY hZ

  constructor
  · exact exists_associated_pow_of_mul_eq_pow' hcop hprod
  · exact exists_associated_pow_of_mul_eq_pow'
      hcop.symm (by simpa only [mul_comm] using hprod)

/-- Mathlib's integral power basis for the Eisenstein ring. -/
noncomputable def integerPowerBasis : PowerBasis ℤ E :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

theorem integerPowerBasis_gen :
    integerPowerBasis.gen = omega := by
  exact
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen

theorem integerPowerBasis_dim :
    integerPowerBasis.dim = 2 := by
  change
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

/-- Index the two basis elements by 0 and 1. -/
noncomputable def integerBasis : Module.Basis (Fin 2) ℤ E :=
  integerPowerBasis.basis.reindex
    (finCongr integerPowerBasis_dim)

theorem integerBasis_apply (i : Fin 2) :
    integerBasis i = omega ^ (i : ℕ) := by
  unfold integerBasis
  rw [Module.Basis.reindex_apply,
      integerPowerBasis.basis_eq_pow,
      integerPowerBasis_gen]
  rfl

/-- Every Eisenstein integer has the form r + sω,
with ordinary integer coefficients. -/
theorem exists_integer_coordinates (W : E) :
    ∃ r s : ℤ, W = (r : E) + (s : E) * omega := by
  refine ⟨integerBasis.repr W 0, integerBasis.repr W 1, ?_⟩
  have h := integerBasis.sum_repr W
  simp only [Fin.sum_univ_two, integerBasis_apply] at h
  simpa [Algebra.smul_def] using h.symm

/-- Recover the two coordinates of r + sω. -/
theorem integerBasis_repr_coordinates (r s : ℤ) :
    integerBasis.repr ((r : E) + (s : E) * omega) 0 = r ∧
    integerBasis.repr ((r : E) + (s : E) * omega) 1 = s := by
  have hzero : integerBasis 0 = 1 := by
    simpa using integerBasis_apply (0 : Fin 2)
  have hone : integerBasis 1 = omega := by
    simpa using integerBasis_apply (1 : Fin 2)

  have heq :
      (r : E) + (s : E) * omega =
        r • integerBasis 0 + s • integerBasis 1 := by
    rw [hzero, hone]
    simp [Algebra.smul_def]

  rw [heq]
  simp only [map_add, map_smul, Module.Basis.repr_self]
  constructor <;> simp

/-- Equal Eisenstein integers have equal integer coordinates. -/
theorem integer_coordinates_eq
    {r s t v : ℤ}
    (h : (r : E) + (s : E) * omega =
      (t : E) + (v : E) * omega) :
    r = t ∧ s = v := by
  constructor
  · have hc := congrArg (fun W : E => integerBasis.repr W 0) h
    rw [(integerBasis_repr_coordinates r s).1,
        (integerBasis_repr_coordinates t v).1] at hc
    exact hc
  · have hc := congrArg (fun W : E => integerBasis.repr W 1) h
    rw [(integerBasis_repr_coordinates r s).2,
        (integerBasis_repr_coordinates t v).2] at hc
    exact hc

/-- Multiplication by λ in integer coordinates. -/
theorem lambda_mul_coordinates (r s : ℤ) :
    lambda * ((r : E) + (s : E) * omega) =
      ((-r - s : ℤ) : E) +
        ((r - 2 * s : ℤ) : E) * omega := by
  unfold lambda
  push_cast
  linear_combination (s : E) * omega_relation

/-- The factor of 9 forces the quotient's ω-coordinate
to be a multiple of 3. -/
theorem linear_quotient_second_coordinate
    {a b r s v : ℤ} {Y : E}
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hcoords : Y = (r : E) + (s : E) * omega)
    (hS : a + b = 9 * v ^ 3) :
    s = -3 * v ^ 3 := by
  have heq :
      (a : E) + (b : E) * omega =
        ((-r - s : ℤ) : E) +
          ((r - 2 * s : ℤ) : E) * omega := by
    calc
      _ = (a : E) + omega * (b : E) := by ring
      _ = lambda * Y := hY
      _ = lambda * ((r : E) + (s : E) * omega) := by
        rw [hcoords]
      _ = _ := lambda_mul_coordinates r s

  obtain ⟨ha, hb⟩ := integer_coordinates_eq heq
  nlinarith [ha, hb, hS]

/-- Expand an Eisenstein cube using our earlier coefficient formulas. -/
theorem cube_coordinates (x y : ℤ) :
    ((x : E) + (y : E) * omega) ^ 3 =
      (descentA x y : E) + (descentB x y : E) * omega := by
  unfold descentA descentB
  push_cast
  linear_combination
    (y : E) ^ 3 * omega_cube +
      3 * (x : E) * (y : E) ^ 2 * omega_relation

/-- Every Eisenstein cube is congruent to an integer modulo 3. -/
theorem cube_congruent_integer (W : E) :
    ∃ n : ℤ, (3 : E) ∣ W ^ 3 - (n : E) := by
  obtain ⟨x, y, hW⟩ := exists_integer_coordinates W
  refine ⟨descentA x y,
    (x : E) * (y : E) * ((x : E) - (y : E)) * omega, ?_⟩
  rw [hW, cube_coordinates]
  unfold descentB
  push_cast
  ring

/-- The factor of 9 makes our linear quotient congruent
to an integer modulo 3. -/
theorem linear_quotient_congruent_integer
    {a b v : ℤ} {Y : E}
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hS : a + b = 9 * v ^ 3) :
    ∃ n : ℤ, (3 : E) ∣ Y - (n : E) := by
  obtain ⟨r, s, hcoords⟩ := exists_integer_coordinates Y
  have hs : s = -3 * v ^ 3 :=
    linear_quotient_second_coordinate hY hcoords hS
  refine ⟨r, -(v : E) ^ 3 * omega, ?_⟩
  rw [hcoords, hs]
  push_cast
  ring

/-- Cancel a 3-free integer from a congruence in the Eisenstein ring. -/
theorem congruent_integer_of_mul_congruent_integer
    {e : E} {n m : ℤ}
    (hn : ¬ (3 : ℤ) ∣ n)
    (h : (3 : E) ∣ e * (n : E) - (m : E)) :
    ∃ k : ℤ, (3 : E) ∣ e - (k : E) := by
  have hp : Prime (3 : ℤ) := by norm_num
  have hcop : IsCoprime (3 : ℤ) n :=
    hp.coprime_iff_not_dvd.mpr hn
  obtain ⟨r, s, hrs⟩ := hcop

  have hcast :
      (r : E) * 3 + (s : E) * (n : E) = 1 := by
    exact_mod_cast hrs

  have hfirst : (3 : E) ∣ (r : E) * 3 * e := by
    refine ⟨(r : E) * e, ?_⟩
    ring

  have hd := dvd_add hfirst
    (dvd_mul_of_dvd_right h (s : E))

  have hid :
      (r : E) * 3 * e +
        (s : E) * (e * (n : E) - (m : E)) =
      ((r : E) * 3 + (s : E) * (n : E)) * e -
        ((s * m : ℤ) : E) := by
    push_cast
    ring

  rw [hid, hcast, one_mul] at hd
  exact ⟨s * m, hd⟩

/-- The integer residue of a λ-free cube is 3-free. -/
theorem cube_integer_residue_three_free
    {W : E} {n : ℤ}
    (hfree : ¬ lambda ∣ W)
    (hcong : (3 : E) ∣ W ^ 3 - (n : E)) :
    ¬ (3 : ℤ) ∣ n := by
  intro hn
  have hdiff : lambda ∣ W ^ 3 - (n : E) :=
    dvd_trans lambda_dvd_three hcong
  have hnE : lambda ∣ (n : E) :=
    (lambda_dvd_intCast_iff n).mpr hn
  have hcube : lambda ∣ W ^ 3 := by
    simpa only [sub_add_cancel] using dvd_add hdiff hnE
  exact hfree (lambda_prime.dvd_of_dvd_pow hcube)

/-- A λ-free quotient congruent to an integer forces
its cube-extraction unit to be congruent to an integer. -/
theorem cube_unit_congruent_integer
    {Y W : E} (e : Eˣ)
    (heq : Y = (e : E) * W ^ 3)
    (hfree : ¬ lambda ∣ Y)
    (hcong : ∃ m : ℤ, (3 : E) ∣ Y - (m : E)) :
    ∃ k : ℤ, (3 : E) ∣ (e : E) - (k : E) := by
  have hWfree : ¬ lambda ∣ W := by
    intro hd
    apply hfree
    rw [heq]
    exact dvd_mul_of_dvd_right
      (dvd_pow hd (by decide : (3 : ℕ) ≠ 0)) (e : E)

  obtain ⟨n, hn⟩ := cube_congruent_integer W
  have hnfree : ¬ (3 : ℤ) ∣ n :=
    cube_integer_residue_three_free hWfree hn
  obtain ⟨m, hm⟩ := hcong

  have hprod : (3 : E) ∣ (e : E) * (n : E) - (m : E) := by
    have hd := dvd_sub hm
      (dvd_mul_of_dvd_right hn (e : E))
    rw [heq] at hd
    have hid :
        ((e : E) * W ^ 3 - (m : E)) -
          (e : E) * (W ^ 3 - (n : E)) =
        (e : E) * (n : E) - (m : E) := by ring
    rw [hid] at hd
    exact hd

  exact congruent_integer_of_mul_congruent_integer hnfree hprod

/-- The remaining cube-extraction unit is only a sign. -/
theorem cube_unit_eq_one_or_neg_one
    {Y W : E} (e : Eˣ)
    (heq : Y = (e : E) * W ^ 3)
    (hfree : ¬ lambda ∣ Y)
    (hcong : ∃ m : ℤ, (3 : E) ∣ Y - (m : E)) :
    e = 1 ∨ e = -1 := by
  obtain ⟨n, hn⟩ :=
    cube_unit_congruent_integer e heq hfree hcong

  have hthree : lambda ^ 2 ∣ (3 : E) := by
    simpa using
      (lambda_sq_dvd_int_sum
        (a := (3 : ℤ)) (b := (0 : ℤ)) (by norm_num))

  apply
    IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) e
  change ∃ k : ℤ, lambda ^ 2 ∣ (e : E) - (k : E)
  exact ⟨n, dvd_trans hthree hn⟩

/-- ω is a unit, with inverse ω². -/
noncomputable def omegaUnit : Eˣ where
  val := omega
  inv := omega ^ 2
  val_inv := by
    calc
      omega * omega ^ 2 = omega ^ 3 := by ring
      _ = 1 := omega_cube
  inv_val := by
    calc
      omega ^ 2 * omega = omega ^ 3 := by ring
      _ = 1 := omega_cube

@[simp] theorem omegaUnit_coe :
    (omegaUnit : E) = omega := rfl

/-- Under the factor-of-9 condition, our original quotient
is an actual cube, with the sign absorbed into its root. -/
theorem linear_quotient_is_cube
    {a b v : ℤ} {Y : E}
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hS : a + b = 9 * v ^ 3)
    (hfree : ¬ lambda ∣ Y)
    (hAssociated :
      ∃ W : E, Associated (W ^ 3) (-omega * Y)) :
    ∃ T : E, Y = T ^ 3 := by
  obtain ⟨W, e, he⟩ := hAssociated

  let f : Eˣ := (-omegaUnit ^ 2) * e
  have hf : (f : E) = (-omega ^ 2) * (e : E) := by
    simp [f]

  have heq : Y = (f : E) * W ^ 3 := by
    rw [hf]
    calc
      Y = omega ^ 3 * Y := by rw [omega_cube]; ring
      _ = (-omega ^ 2) * (-omega * Y) := by ring
      _ = (-omega ^ 2) * (W ^ 3 * (e : E)) := by rw [he]
      _ = ((-omega ^ 2) * (e : E)) * W ^ 3 := by ring

  have hcong : ∃ n : ℤ, (3 : E) ∣ Y - (n : E) :=
    linear_quotient_congruent_integer hY hS

  rcases cube_unit_eq_one_or_neg_one f heq hfree hcong with hfOne | hfNeg
  · refine ⟨W, ?_⟩
    simpa [hfOne] using heq
  · refine ⟨-W, ?_⟩
    calc
      Y = -W ^ 3 := by simpa [hfNeg] using heq
      _ = (-W) ^ 3 := by ring

/-- Recover the integer parametrisation from the extracted cube. -/
theorem integer_parametrisation_of_linear_quotient
    {a b v : ℤ} {Y : E}
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hS : a + b = 9 * v ^ 3)
    (hfree : ¬ lambda ∣ Y)
    (hAssociated :
      ∃ W : E, Associated (W ^ 3) (-omega * Y)) :
    ∃ x y : ℤ,
      a = descentA x y + descentB x y ∧
      b = 2 * descentB x y - descentA x y := by
  obtain ⟨T, hT⟩ :=
    linear_quotient_is_cube hY hS hfree hAssociated
  obtain ⟨x, y, hcoords⟩ := exists_integer_coordinates (-T)

  have hfactor :
      (a : E) + (b : E) * omega =
        ((descentA x y + descentB x y : ℤ) : E) +
          ((2 * descentB x y - descentA x y : ℤ) : E) *
            omega := by
    calc
      _ = (a : E) + omega * (b : E) := by ring
      _ = lambda * Y := hY
      _ = lambda * T ^ 3 := by rw [hT]
      _ = (1 - omega) * (-T) ^ 3 := by
        unfold lambda
        ring
      _ = (1 - omega) *
          ((x : E) + (y : E) * omega) ^ 3 := by
        rw [hcoords]
      _ = (1 - omega) *
          ((descentA x y : E) +
            (descentB x y : E) * omega) := by
        rw [cube_coordinates]
      _ = _ := by
        push_cast
        linear_combination
          -(descentB x y : E) * omega_relation

  exact ⟨x, y, integer_coordinates_eq hfactor⟩

/-- A coprime cube solution in the 3-divisible-sum branch
admits our integer parametrisation and a new cube product. -/
theorem parametrisation_of_sum_cubes
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b)
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    ∃ x y v : ℤ,
      a = descentA x y + descentB x y ∧
      b = 2 * descentB x y - descentA x y ∧
      x * y * (x - y) = v ^ 3 := by
  obtain ⟨v, hv⟩ := sum_eq_nine_mul_cube hab hS hc
  obtain ⟨u, hu⟩ := cubeFactor_eq_three_mul_cube hab hS hc

  obtain ⟨Y, hY, hYfree⟩ :=
    exists_lambda_free_linear_quotient hab hS
  obtain ⟨Z, hZ, _hZfree⟩ :=
    exists_lambda_free_second_quotient hab hS

  have hAssociated :
      ∃ W : E, Associated (W ^ 3) (-omega * Y) :=
    (adjusted_quotients_are_cubes
      hab hu hY hZ hYfree).1

  obtain ⟨x, y, ha, hb⟩ :=
    integer_parametrisation_of_linear_quotient
      hY hv hYfree hAssociated

  refine ⟨x, y, v, ha, hb, ?_⟩
  have hsum := descent_sum x y
  rw [← ha, ← hb] at hsum
  nlinarith [hv, hsum]

/-- Coprimality of the original inputs forces coprimality
of the parametrisation coordinates. -/
theorem parametrisation_coordinates_coprime
    {a b x y : ℤ}
    (hab : IsCoprime a b)
    (ha : a = descentA x y + descentB x y)
    (hb : b = 2 * descentB x y - descentA x y) :
    IsCoprime x y := by
  have hrel : IsRelPrime x y := by
    intro d hdx hdy

    have hdA : d ∣ descentA x y := by
      unfold descentA
      exact dvd_add
        (dvd_sub
          (dvd_pow hdx (by decide : (3 : ℕ) ≠ 0))
          (dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_right hdx 3) (y ^ 2)))
        (dvd_pow hdy (by decide : (3 : ℕ) ≠ 0))

    have hdB : d ∣ descentB x y := by
      unfold descentB
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right hdx 3) y)
        (x - y)

    have hda : d ∣ a := by
      rw [ha]
      exact dvd_add hdA hdB

    have hdb : d ∣ b := by
      rw [hb]
      exact dvd_sub (dvd_mul_of_dvd_right hdB 2) hdA

    exact hab.isUnit_of_dvd' hda hdb

  exact hrel.isCoprime

/-- Coprime x and y make x, y, and x-y pairwise coprime. -/
theorem coordinates_pairwise_coprime
    {x y : ℤ}
    (hxy : IsCoprime x y) :
    IsCoprime x (x - y) ∧ IsCoprime y (x - y) := by
  obtain ⟨r, s, hrs⟩ := hxy
  constructor
  · refine ⟨r + s, -s, ?_⟩
    calc
      (r + s) * x + (-s) * (x - y) =
          r * x + s * y := by ring
      _ = 1 := hrs
  · refine ⟨r + s, r, ?_⟩
    calc
      (r + s) * y + r * (x - y) =
          r * x + s * y := by ring
      _ = 1 := hrs

/-- A cube product of these coprime factors yields
another sum-of-cubes equation. -/
theorem cube_solution_of_coordinate_product
    {x y v : ℤ}
    (hxy : IsCoprime x y)
    (hprod : x * y * (x - y) = v ^ 3) :
    ∃ r s t : ℤ,
      x = r ^ 3 ∧
      y = s ^ 3 ∧
      x - y = t ^ 3 ∧
      s ^ 3 + t ^ 3 = r ^ 3 := by
  obtain ⟨hxz, hyz⟩ := coordinates_pairwise_coprime hxy

  have hcop : IsCoprime (x * y) (x - y) :=
    hxz.mul_left hyz
  have hodd : Odd (3 : ℕ) := by decide

  obtain ⟨w, hw⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left hcop hodd hprod

  obtain ⟨r, hr⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left hxy hodd hw
  obtain ⟨s, hs⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_right hxy hodd hw
  obtain ⟨t, ht⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_right hcop hodd hprod

  refine ⟨r, s, t, hr, hs, ht, ?_⟩
  rw [← hr, ← hs, ← ht]
  ring

/-- A nonzero original solution makes the coordinate product nonzero. -/
theorem coordinate_product_ne_zero
    {a b c x y : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc0 : c ≠ 0)
    (ha : a = descentA x y + descentB x y)
    (hb : b = 2 * descentB x y - descentA x y) :
    x * y * (x - y) ≠ 0 := by
  have hsum : a + b = 9 * (x * y * (x - y)) := by
    calc
      a + b = 9 * x * y * (x - y) := by
        rw [ha, hb]
        exact descent_sum x y
      _ = 9 * (x * y * (x - y)) := by ring

  intro hzero
  have hcPow : c ^ 3 = 0 := by
    calc
      c ^ 3 = a ^ 3 + b ^ 3 := hc.symm
      _ = (a + b) * cubeFactor a b :=
        sum_cubes_factorisation a b
      _ = 0 := by
        rw [hsum, hzero]
        ring

  exact (pow_ne_zero 3 hc0) hcPow

/-- The extracted roots are nonzero, and the new inputs are coprime. -/
theorem coordinate_cube_roots_conditions
    {x y r s t : ℤ}
    (hxy : IsCoprime x y)
    (hprod : x * y * (x - y) ≠ 0)
    (hr : x = r ^ 3)
    (hs : y = s ^ 3)
    (ht : x - y = t ^ 3) :
    r ≠ 0 ∧ s ≠ 0 ∧ t ≠ 0 ∧ IsCoprime s t := by
  have hr0 : r ≠ 0 := by
    intro h
    apply hprod
    rw [hr, h]
    ring

  have hs0 : s ≠ 0 := by
    intro h
    apply hprod
    rw [hs, h]
    ring

  have ht0 : t ≠ 0 := by
    intro h
    apply hprod
    rw [ht, h]
    ring

  obtain ⟨_, hyz⟩ := coordinates_pairwise_coprime hxy
  rw [ht, hs] at hyz
  have hst : IsCoprime s t :=
    (IsCoprime.pow_iff
      (m := 3) (n := 3) (by decide) (by decide)).mp hyz

  exact ⟨hr0, hs0, ht0, hst⟩

/-- Construct another nonzero coprime cube solution.
A strict decrease remains to be proved separately. -/
theorem exists_new_coprime_cube_solution
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b)
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc0 : c ≠ 0) :
    ∃ r s t : ℤ,
      r ≠ 0 ∧ s ≠ 0 ∧ t ≠ 0 ∧
      IsCoprime s t ∧ s ^ 3 + t ^ 3 = r ^ 3 := by
  obtain ⟨x, y, v, ha, hb, hprod⟩ :=
    parametrisation_of_sum_cubes hab hS hc

  have hxy : IsCoprime x y :=
    parametrisation_coordinates_coprime hab ha hb
  have hnonzero : x * y * (x - y) ≠ 0 :=
    coordinate_product_ne_zero hc hc0 ha hb

  obtain ⟨r, s, t, hr, hs, ht, heq⟩ :=
    cube_solution_of_coordinate_product hxy hprod
  obtain ⟨hr0, hs0, ht0, hst⟩ :=
    coordinate_cube_roots_conditions hxy hnonzero hr hs ht

  exact ⟨r, s, t, hr0, hs0, ht0, hst, heq⟩

/-- Every positive factor is smaller than three times
the product of all four positive factors. -/
theorem factor_lt_three_product
    {A B C U : ℕ}
    (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hU : 0 < U) :
    A < 3 * U * A * B * C := by
  have hAB : A ≤ A * B := by
    simpa using Nat.mul_le_mul_left A (show 1 ≤ B by omega)
  have hABC : A * B ≤ A * B * C := by
    simpa using
      Nat.mul_le_mul_left (A * B) (show 1 ≤ C by omega)
  have hUABC : A * B * C ≤ U * (A * B * C) := by
    simpa using
      Nat.mul_le_mul_right (A * B * C) (show 1 ≤ U by omega)
  have hp : 0 < U * (A * B * C) := by positivity
  calc
    A ≤ A * B := hAB
    _ ≤ A * B * C := hABC
    _ ≤ U * (A * B * C) := hUABC
    _ < 3 * (U * (A * B * C)) := by omega
    _ = 3 * U * A * B * C := by ring

/-- All three extracted roots are smaller than the old output. -/
theorem coordinate_roots_strictly_smaller
    {a b c u v x y r s t : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc0 : c ≠ 0)
    (hQ : cubeFactor a b = 3 * u ^ 3)
    (hS : a + b = 9 * v ^ 3)
    (hprod : x * y * (x - y) = v ^ 3)
    (hr : x = r ^ 3)
    (hs : y = s ^ 3)
    (ht : x - y = t ^ 3)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0) (ht0 : t ≠ 0) :
    r.natAbs < c.natAbs ∧
    s.natAbs < c.natAbs ∧
    t.natAbs < c.natAbs := by
  have hodd : Odd (3 : ℕ) := by decide

  have hv : v = r * s * t := by
    apply hodd.pow_injective
    calc
      v ^ 3 = x * y * (x - y) := hprod.symm
      _ = (r * s * t) ^ 3 := by
        rw [ht, hr, hs]
        ring

  have hceq : c = 3 * u * v := by
    apply hodd.pow_injective
    calc
      c ^ 3 = a ^ 3 + b ^ 3 := hc.symm
      _ = (a + b) * cubeFactor a b :=
        sum_cubes_factorisation a b
      _ = (3 * u * v) ^ 3 := by
        rw [hS, hQ]
        ring

  have hu0 : u ≠ 0 := by
    intro hu
    apply hc0
    rw [hceq, hu]
    ring

  have hU : 0 < u.natAbs := Int.natAbs_pos.mpr hu0
  have hR : 0 < r.natAbs := Int.natAbs_pos.mpr hr0
  have hSpos : 0 < s.natAbs := Int.natAbs_pos.mpr hs0
  have hT : 0 < t.natAbs := Int.natAbs_pos.mpr ht0

  have hsize :
      c.natAbs =
        3 * u.natAbs * r.natAbs * s.natAbs * t.natAbs := by
    rw [hceq, hv]
    norm_num [Int.natAbs_mul]
    ring

  constructor
  · rw [hsize]
    exact factor_lt_three_product hR hSpos hT hU
  · constructor
    · rw [hsize]
      have h := factor_lt_three_product hSpos hR hT hU
      nlinarith [h]
    · rw [hsize]
      have h := factor_lt_three_product hT hR hSpos hU
      nlinarith [h]

/-- Construct roots with all inherited conditions and strict bounds. -/
theorem exists_smaller_cube_roots
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b)
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc0 : c ≠ 0) :
    ∃ r s t : ℤ,
      r ≠ 0 ∧ s ≠ 0 ∧ t ≠ 0 ∧
      IsCoprime r s ∧ IsCoprime r t ∧ IsCoprime s t ∧
      s ^ 3 + t ^ 3 = r ^ 3 ∧
      r.natAbs < c.natAbs ∧
      s.natAbs < c.natAbs ∧
      t.natAbs < c.natAbs := by
  obtain ⟨x, y, v, ha, hb, hprod⟩ :=
    parametrisation_of_sum_cubes hab hS hc
  obtain ⟨u, hu⟩ := cubeFactor_eq_three_mul_cube hab hS hc

  have hxy := parametrisation_coordinates_coprime hab ha hb
  have hnonzero := coordinate_product_ne_zero hc hc0 ha hb

  obtain ⟨r, s, t, hr, hs, ht, heq⟩ :=
    cube_solution_of_coordinate_product hxy hprod
  obtain ⟨hr0, hs0, ht0, hst⟩ :=
    coordinate_cube_roots_conditions hxy hnonzero hr hs ht

  have hrs : IsCoprime r s := by
    have h := hxy
    rw [hr, hs] at h
    exact
      (IsCoprime.pow_iff
        (m := 3) (n := 3) (by decide) (by decide)).mp h

  have hrt : IsCoprime r t := by
    have h := (coordinates_pairwise_coprime hxy).1
    rw [ht, hr] at h
    exact
      (IsCoprime.pow_iff
        (m := 3) (n := 3) (by decide) (by decide)).mp h

  have hv : a + b = 9 * v ^ 3 := by
    have hsum := descent_sum x y
    rw [← ha, ← hb] at hsum
    nlinarith [hsum, hprod]

  obtain ⟨hR, hSroot, hT⟩ :=
    coordinate_roots_strictly_smaller
      hc hc0 hu hv hprod hr hs ht hr0 hs0 ht0

  exact
    ⟨r, s, t, hr0, hs0, ht0, hrs, hrt, hst,
      heq, hR, hSroot, hT⟩

/-- Cubes equal their bases modulo 3, so a 3-divisible
output forces a 3-divisible input sum. -/
theorem three_dvd_sum_of_output
    {a b c : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc3 : (3 : ℤ) ∣ c) :
    (3 : ℤ) ∣ a + b := by
  have hcube : ∀ z : ZMod 3, z ^ 3 = z := by decide

  have hcast :
      (a : ZMod 3) ^ 3 + (b : ZMod 3) ^ 3 =
        (c : ZMod 3) ^ 3 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 3)) hc
    simpa only [Int.cast_add, Int.cast_pow] using h

  have hczero : (c : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd c 3).mpr
      (by simpa using hc3)

  have hs : (a : ZMod 3) + (b : ZMod 3) = 0 := by
    simpa only [hcube, hczero] using hcast

  have hsum : ((a + b : ℤ) : ZMod 3) = 0 := by
    simpa only [Int.cast_add] using hs

  simpa using
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 3).mp hsum

theorem coprime_neg_right_of_coprime
    {a b : ℤ} (hab : IsCoprime a b) :
    IsCoprime a (-b) := by
  obtain ⟨u, v, huv⟩ := hab
  refine ⟨u, -v, ?_⟩
  calc
    u * a + (-v) * (-b) = u * a + v * b := by ring
    _ = 1 := huv

/-- Reorient a solution into the 3-divisible-sum branch,
while retaining a bound on the output. -/
theorem reorient_cube_solution
    {a b c : ℤ} {M : ℕ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime a b)
    (hac : IsCoprime a c)
    (hbc : IsCoprime b c)
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (haM : a.natAbs < M)
    (hbM : b.natAbs < M)
    (hcM : c.natAbs < M) :
    ∃ A B C : ℤ,
      A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
      IsCoprime A B ∧
      (3 : ℤ) ∣ A + B ∧
      A ^ 3 + B ^ 3 = C ^ 3 ∧ C.natAbs < M := by
  rcases three_dvd_some_of_sum_cubes hc with ha3 | hb3 | hc3
  · have heq : c ^ 3 + (-b) ^ 3 = a ^ 3 := by
      calc
        c ^ 3 + (-b) ^ 3 = c ^ 3 - b ^ 3 := by ring
        _ = a ^ 3 := by linarith [hc]
    exact
      ⟨c, -b, a, hc0, neg_ne_zero.mpr hb0, ha0,
        coprime_neg_right_of_coprime hbc.symm,
        three_dvd_sum_of_output heq ha3, heq, haM⟩
  · have heq : c ^ 3 + (-a) ^ 3 = b ^ 3 := by
      calc
        c ^ 3 + (-a) ^ 3 = c ^ 3 - a ^ 3 := by ring
        _ = b ^ 3 := by linarith [hc]
    exact
      ⟨c, -a, b, hc0, neg_ne_zero.mpr ha0, hb0,
        coprime_neg_right_of_coprime hac.symm,
        three_dvd_sum_of_output heq hb3, heq, hbM⟩
  · exact
      ⟨a, b, c, ha0, hb0, hc0, hab,
        three_dvd_sum_of_output hc hc3, hc, hcM⟩

/-- Coprimality of the inputs of a cube equation also
gives coprimality of the second input and output. -/
theorem coprime_output_right
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hb0 : b ≠ 0)
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    IsCoprime b c := by
  apply isCoprime_of_prime_dvd
  · intro h
    exact hb0 h.1
  · intro p hp hpb hpc
    have hpaPow : p ∣ a ^ 3 := by
      have hd := dvd_sub
        (dvd_pow hpc (by decide : (3 : ℕ) ≠ 0))
        (dvd_pow hpb (by decide : (3 : ℕ) ≠ 0))
      have hid : c ^ 3 - b ^ 3 = a ^ 3 := by
        linarith [hc]
      rw [hid] at hd
      exact hd
    have hpa : p ∣ a := hp.dvd_of_dvd_pow hpaPow
    exact hp.not_isUnit (hab.isUnit_of_dvd' hpa hpb)

/-- Infinite descent on the output's absolute value. -/
theorem no_cube_solution_three_dvd_sum
    {a b c : ℤ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have H :
      ∀ n : ℕ, ∀ A B C : ℤ,
        C.natAbs = n →
        A ≠ 0 → B ≠ 0 → C ≠ 0 →
        IsCoprime A B →
        (3 : ℤ) ∣ A + B →
        A ^ 3 + B ^ 3 = C ^ 3 → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B C hsize hA hB hC hAB hsum heq

      obtain
        ⟨r, s, t, hr0, hs0, ht0, hrs, hrt, hst,
          hnew, hrM, hsM, htM⟩ :=
        exists_smaller_cube_roots hAB hsum heq hC

      obtain
        ⟨A', B', C', hA', hB', hC', hAB',
          hsum', heq', hlt⟩ :=
        reorient_cube_solution
          hs0 ht0 hr0 hst hrs.symm hrt.symm
          hnew hsM htM hrM

      have hlt' : C'.natAbs < n := by omega
      exact ih C'.natAbs hlt' A' B' C' rfl
        hA' hB' hC' hAB' hsum' heq'

  intro hc
  exact H c.natAbs a b c rfl ha0 hb0 hc0 hab hS hc

/-- No nonzero coprime integer cube solution exists. -/
theorem no_coprime_integer_cube_solution
    {a b c : ℤ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime a b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro hc
  have hbc := coprime_output_right hab hb0 hc
  have hac : IsCoprime a c :=
    coprime_output_right hab.symm ha0
      (by simpa only [add_comm] using hc)

  obtain
    ⟨A, B, C, hA, hB, hC, hAB, hsum, heq, _⟩ :=
    reorient_cube_solution
      (M := a.natAbs + b.natAbs + c.natAbs + 1)
      ha0 hb0 hc0 hab hac hbc hc
      (by omega) (by omega) (by omega)

  exact no_cube_solution_three_dvd_sum hA hB hC hAB hsum heq

/-- Fermat's Last Theorem for exponent three,
using the descent constructed in this file. -/
theorem fermatLastTheoremThree_via_descent :
    FermatLastTheoremFor 3 := by
  apply fermatLastTheoremFor_iff_int.mpr
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha0 hb0 hc0 hgcd hc

  have hgcdNeg : Finset.gcd {a, b, -c} id = 1 := by
    simpa [Finset.gcd_insert, Finset.gcd_singleton,
      ← Int.abs_eq_normalize] using hgcd

  have hzero : a ^ 3 + b ^ 3 + (-c) ^ 3 = 0 := by
    calc
      _ = (a ^ 3 + b ^ 3) - c ^ 3 := by ring
      _ = 0 := by rw [hc]; ring

  have hab : IsCoprime a b :=
    isCoprime_of_gcd_eq_one_of_FLT hgcdNeg hzero

  exact no_coprime_integer_cube_solution ha0 hb0 hc0 hab hc

/-- exponent-three proof covers every exponent divisible by three. -/
theorem fermatLastTheorem_of_three_dvd
    {n : ℕ} (hn : 3 ∣ n) :
    FermatLastTheoremFor n :=
  FermatLastTheoremFor.mono hn
    fermatLastTheoremThree_via_descent

end EisensteinBridge

/-- Relate the fourth-power mismatch to the cubic mismatch. -/
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

#print axioms Hire.EisensteinBridge.fermatLastTheoremThree_via_descent
#print axioms Hire.fermatLastTheoremFour_via_descent
#print axioms Hire.GoldenBridge.fermatLastTheoremFive_via_descent
