import Hire.FLT.Cubic

namespace Hire

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

end Hire
