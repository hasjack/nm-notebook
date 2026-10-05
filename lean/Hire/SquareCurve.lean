import Mathlib

namespace SquareCurve

/-- The cubic associated with the square lattice,
    after a suitable complex change of scale. -/
def OnCurve (x y : ℂ) : Prop :=
  y ^ 2 = x ^ 3 - x

/-- The square symmetry preserves the cubic. -/
theorem quarter_turn_preserves_curve
    {x y : ℂ} (h : OnCurve x y) :
    OnCurve (-x) (Complex.I * y) := by
  unfold OnCurve at *
  calc
    (Complex.I * y) ^ 2
        = Complex.I ^ 2 * y ^ 2 := by ring
    _ = -(y ^ 2) := by simp
    _ = -(x ^ 3 - x) := by rw [h]
    _ = (-x) ^ 3 - (-x) := by ring

/-- Two quarter-turns give reflection of the y-coordinate. -/
theorem two_quarter_turns (x y : ℂ) :
    (-(-x), Complex.I * (Complex.I * y)) = (x, -y) := by
  apply Prod.ext
  · simp
  · calc
      Complex.I * (Complex.I * y)
          = (Complex.I * Complex.I) * y := by ring
      _ = -y := by simp

end SquareCurve
