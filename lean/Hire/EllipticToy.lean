import Mathlib

namespace EllipticToy

/-- Rational points on our chosen cubic. -/
def OnCurve (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 - 2

/-- The tangent line at (3, 5). -/
def tangentAtP (x : ℚ) : ℚ :=
  5 + (27 / 10 : ℚ) * (x - 3)

/-- Our starting point lies on the curve. -/
theorem starting_point :
    OnCurve 3 5 := by
  norm_num [OnCurve]

/-- The tangent slope computed from 3x² / (2y). -/
theorem tangent_slope :
    (3 * (3 : ℚ) ^ 2) / (2 * 5) = 27 / 10 := by
  norm_num

/-- The tangent passes through our starting point. -/
theorem tangent_at_start :
    tangentAtP 3 = 5 := by
  norm_num [tangentAtP]

/-- Substituting the line into the curve gives this exact factorisation. -/
theorem tangent_intersection_factorisation (x : ℚ) :
    (x ^ 3 - 2) - (tangentAtP x) ^ 2 =
      (x - 3) ^ 2 * (x - (129 / 100 : ℚ)) := by
  unfold tangentAtP
  ring

/-- The other intersection has height +383/1000. -/
theorem other_intersection_height :
    tangentAtP (129 / 100) = 383 / 1000 := by
  norm_num [tangentAtP]

/-- The other intersection lies exactly on the curve. -/
theorem other_intersection_onCurve :
    OnCurve (129 / 100) (383 / 1000) := by
  norm_num [OnCurve]

/-- Reflection across the horizontal axis preserves the curve. -/
theorem reflection_preserves_curve
    {x y : ℚ} (h : OnCurve x y) :
    OnCurve x (-y) := by
  unfold OnCurve at *
  simpa using h

/-- The reflected point also lies exactly on the curve. -/
theorem doubled_point_onCurve :
    OnCurve (129 / 100) (-(383 / 1000)) := by
  exact reflection_preserves_curve other_intersection_onCurve

/-- The doubled point's x-coordinate is not an integer. -/
theorem doubled_x_not_integer :
    ¬ ∃ n : ℤ, (n : ℚ) = (129 / 100 : ℚ) := by
  rintro ⟨n, hn⟩
  have hlo : (1 : ℚ) < (n : ℚ) := by
    rw [hn]
    norm_num
  have hhi : (n : ℚ) < (2 : ℚ) := by
    rw [hn]
    norm_num
  have hloZ : (1 : ℤ) < n := by
    exact_mod_cast hlo
  have hhiZ : n < (2 : ℤ) := by
    exact_mod_cast hhi
  omega

/-- Our cubic expressed as a Mathlib Weierstrass curve. -/
def curve : WeierstrassCurve.Affine ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := -2

/-- Mathlib's tangent slope agrees with our calculation. -/
theorem mathlib_doubling_slope :
    curve.slope 3 3 5 5 = (27 / 10 : ℚ) := by
  norm_num [curve, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.negY]

/-- Mathlib's addition formula gives our x-coordinate. -/
theorem mathlib_doubling_x :
    curve.addX 3 3 (curve.slope 3 3 5 5) =
      (129 / 100 : ℚ) := by
  rw [mathlib_doubling_slope]
  norm_num [curve, WeierstrassCurve.Affine.addX]

/-- Mathlib's addition formula gives our reflected y-coordinate. -/
theorem mathlib_doubling_y :
    curve.addY 3 3 5 (curve.slope 3 3 5 5) =
      -(383 / 1000 : ℚ) := by
  rw [mathlib_doubling_slope]
  norm_num [curve, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY]

/-- The starting point is a nonsingular curve point. -/
theorem starting_point_nonsingular :
    curve.Nonsingular 3 5 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  norm_num [curve, WeierstrassCurve.Affine.equation_iff']

/-- The computed doubled point is also nonsingular. -/
theorem doubled_point_nonsingular :
    curve.Nonsingular (129 / 100) (-(383 / 1000)) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  norm_num [curve, WeierstrassCurve.Affine.equation_iff']

/-- Our starting point, packaged in Mathlib's point group. -/
def P : curve.Point :=
  WeierstrassCurve.Affine.Point.some
    3 5 starting_point_nonsingular

/-- Our computed point, packaged in the same group. -/
def doubledP : curve.Point :=
  WeierstrassCurve.Affine.Point.some
    (129 / 100) (-(383 / 1000)) doubled_point_nonsingular

/-- The geometric calculation really is group doubling. -/
theorem P_add_P :
    P + P = doubledP := by
  have hy : (5 : ℚ) ≠ curve.negY 3 5 := by
    norm_num [curve, WeierstrassCurve.Affine.negY]
  unfold P doubledP
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  simp only [mathlib_doubling_x, mathlib_doubling_y]

end EllipticToy
