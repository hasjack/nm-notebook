import Hire.NormLift15
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

namespace HireCharacterReadout

section IdealNormLift

variable {R : Type*}
    [CommRing R] [IsDedekindDomain R] [Infinite R]

/-- Lift the door character to ideals by their absolute norm. -/
noncomputable def idealNormLift15 : Ideal R →*₀ ℂ where
  toFun I :=
    complexCharacter15 (Ideal.absNorm I : ZMod 15)
  map_zero' := by
    change complexCharacter15
      (Ideal.absNorm (0 : Ideal R) : ZMod 15) = 0
    rw [map_zero, Nat.cast_zero]
    simpa [complex15, quarticFive, Hire.chi3] using
      complexCharacter15_apply_nat 0
  map_one' := by
    simp
  map_mul' I J := by
    rw [map_mul, Nat.cast_mul, map_mul]

/-- The lift reproduces the original table at the ideal norm. -/
theorem idealNormLift15_apply (I : Ideal R) :
    idealNormLift15 I = complex15 (Ideal.absNorm I) := by
  exact complexCharacter15_apply_nat (Ideal.absNorm I)

/-- Ideal multiplication multiplies the character values. -/
theorem idealNormLift15_mul (I J : Ideal R) :
    idealNormLift15 (I * J) =
      idealNormLift15 I * idealNormLift15 J := by
  exact map_mul idealNormLift15 I J

/-- An ideal of norm p contributes the rational character value at p. -/
theorem idealNormLift15_of_norm_eq
    (I : Ideal R) (p : ℕ)
    (hI : Ideal.absNorm I = p) :
    idealNormLift15 I = complex15 p := by
  rw [idealNormLift15_apply, hI]

/-- An ideal of norm p² contributes the square of that value. -/
theorem idealNormLift15_of_norm_square
    (I : Ideal R) (p : ℕ)
    (hI : Ideal.absNorm I = p * p) :
    idealNormLift15 I = complex15 p ^ 2 := by
  rw [idealNormLift15_apply, hI, complex15_apply_square]

end IdealNormLift

end HireCharacterReadout
