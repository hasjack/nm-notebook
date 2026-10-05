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

end TorusCurveBridge
