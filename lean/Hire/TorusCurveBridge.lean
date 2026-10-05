import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic
import Hire.Torus

namespace TorusCurveBridge

/-- The cubic associated with a period pair, using y = ℘'/2. -/
noncomputable def latticeCurve (L : PeriodPair) :
    WeierstrassCurve.Affine ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -L.g₂ / 4
  a₆ := -L.g₃ / 4

/-- The analytic coordinates satisfy Mathlib's curve equation. -/
theorem weierstrass_coordinates_on_curve
    (L : PeriodPair) (z : ℂ)
    (hz : z ∉ L.lattice) :
    (latticeCurve L).Equation
      (L.weierstrassP z)
      (L.derivWeierstrassP z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [latticeCurve, zero_mul, add_zero]
  calc
    (L.derivWeierstrassP z / 2) ^ 2
        = (L.derivWeierstrassP z) ^ 2 / 4 := by ring
    _ = (4 * (L.weierstrassP z) ^ 3 -
          L.g₂ * L.weierstrassP z - L.g₃) / 4 := by
      rw [L.derivWeierstrassP_sq z hz]
    _ = _ := by ring

/-- The period pair for our square torus. -/
noncomputable def squarePeriods : PeriodPair where
  ω₁ := 1
  ω₂ := Complex.I
  indep := by
    simpa only [Complex.coe_basisOneI] using
      Complex.basisOneI.linearIndependent

/-- Mathlib's square lattice consists exactly of integer shifts. -/
theorem mem_square_lattice_iff (z : ℂ) :
    z ∈ squarePeriods.lattice ↔
      ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * Complex.I := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    simpa [squarePeriods] using h.symm
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    simpa [squarePeriods] using h.symm

/-- Our quotient relation uses precisely Mathlib's square lattice. -/
theorem samePoint_iff_sub_mem_square_lattice (z w : ℂ) :
    AlphabetTorus.SamePoint 1 Complex.I z w ↔
      z - w ∈ squarePeriods.lattice := by
  rw [mem_square_lattice_iff]
  simp only [AlphabetTorus.SamePoint, mul_one]

/-- The analytic coordinates for this square lattice lie on its cubic. -/
theorem square_coordinates_on_curve
    (z : ℂ) (hz : z ∉ squarePeriods.lattice) :
    (latticeCurve squarePeriods).Equation
      (squarePeriods.weierstrassP z)
      (squarePeriods.derivWeierstrassP z / 2) := by
  exact weierstrass_coordinates_on_curve squarePeriods z hz

/-- The analytic coordinate pair associated with the square lattice. -/
noncomputable def squareCoordinates (z : ℂ) : ℂ × ℂ :=
  (squarePeriods.weierstrassP z,
   squarePeriods.derivWeierstrassP z / 2)

/-- Equivalent representatives give identical analytic coordinates. -/
theorem squareCoordinates_of_samePoint
    {z w : ℂ}
    (h : AlphabetTorus.SamePoint 1 Complex.I z w) :
    squareCoordinates z = squareCoordinates w := by
  have hl : z - w ∈ squarePeriods.lattice :=
    (samePoint_iff_sub_mem_square_lattice z w).mp h
  let l : squarePeriods.lattice := ⟨z - w, hl⟩
  have hz : z = w + (l : ℂ) := by
    change z = w + (z - w)
    ring
  unfold squareCoordinates
  rw [hz]
  rw [squarePeriods.weierstrassP_add_coe w l,
      squarePeriods.derivWeierstrassP_add_coe w l]

/-- The analytic readings are well-defined on the square quotient. -/
noncomputable def quotientCoordinates :
    AlphabetTorus.PeriodQuotient 1 Complex.I → ℂ × ℂ :=
  Quotient.lift squareCoordinates
    (fun _ _ h => squareCoordinates_of_samePoint h)

/-- Reading a quotient point agrees with reading a representative. -/
theorem quotientCoordinates_point (z : ℂ) :
    quotientCoordinates (AlphabetTorus.point 1 Complex.I z) =
      squareCoordinates z := by
  rfl

/-- Lattice membership is independent of the representative. -/
theorem square_lattice_mem_iff_of_samePoint
    {z w : ℂ}
    (h : AlphabetTorus.SamePoint 1 Complex.I z w) :
    z ∈ squarePeriods.lattice ↔ w ∈ squarePeriods.lattice := by
  have hl : z - w ∈ squarePeriods.lattice :=
    (samePoint_iff_sub_mem_square_lattice z w).mp h
  constructor
  · intro hz
    have hw : w = z - (z - w) := by ring
    rw [hw]
    exact squarePeriods.lattice.sub_mem hz hl
  · intro hw
    have hz : z = w + (z - w) := by ring
    rw [hz]
    exact squarePeriods.lattice.add_mem hw hl

/-- Lattice points mark infinity; other points carry analytic coordinates. -/
noncomputable def squareReadout (z : ℂ) : Option (ℂ × ℂ) := by
  classical
  exact
    if z ∈ squarePeriods.lattice then
      none
    else
      some (squareCoordinates z)

/-- The infinity marker and ordinary coordinates respect the gluing. -/
theorem squareReadout_of_samePoint
    {z w : ℂ}
    (h : AlphabetTorus.SamePoint 1 Complex.I z w) :
    squareReadout z = squareReadout w := by
  classical
  have hm := square_lattice_mem_iff_of_samePoint h
  by_cases hz : z ∈ squarePeriods.lattice
  · have hw := hm.mp hz
    simp [squareReadout, hz, hw]
  · have hw : w ∉ squarePeriods.lattice := by
      intro hw
      exact hz (hm.mpr hw)
    simp [squareReadout, hz, hw,
      squareCoordinates_of_samePoint h]

/-- The readout with an infinity marker descends to the quotient. -/
noncomputable def quotientReadout :
    AlphabetTorus.PeriodQuotient 1 Complex.I →
      Option (ℂ × ℂ) :=
  Quotient.lift squareReadout
    (fun _ _ h => squareReadout_of_samePoint h)

/-- The lattice class is marked as infinity. -/
theorem quotientReadout_zero :
    quotientReadout (AlphabetTorus.point 1 Complex.I 0) = none := by
  change squareReadout 0 = none
  simp [squareReadout]

/-- Every ordinary readout satisfies the associated cubic equation. -/
theorem squareReadout_some_on_curve
    {z x y : ℂ}
    (h : squareReadout z = some (x, y)) :
    (latticeCurve squarePeriods).Equation x y := by
  classical
  by_cases hz : z ∈ squarePeriods.lattice
  · simp [squareReadout, hz] at h
  · have hc : squareCoordinates z = (x, y) := by
      simpa [squareReadout, hz] using h
    have hx : squarePeriods.weierstrassP z = x := by
      simpa [squareCoordinates] using congrArg Prod.fst hc
    have hy : squarePeriods.derivWeierstrassP z / 2 = y := by
      simpa [squareCoordinates] using congrArg Prod.snd hc
    simpa only [hx, hy] using square_coordinates_on_curve z hz

/-- The same curve-membership guarantee holds on the quotient. -/
theorem quotientReadout_some_on_curve
    (q : AlphabetTorus.PeriodQuotient 1 Complex.I)
    {x y : ℂ}
    (h : quotientReadout q = some (x, y)) :
    (latticeCurve squarePeriods).Equation x y := by
  revert h
  refine Quotient.inductionOn q ?_
  intro z h
  change squareReadout z = some (x, y) at h
  exact squareReadout_some_on_curve h

end TorusCurveBridge
