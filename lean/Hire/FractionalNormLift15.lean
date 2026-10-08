import Hire.EisensteinNormLift15
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.GroupTheory.QuotientGroup.Defs

namespace HireCharacterReadout

/-- The ideal modulus used for the norm lift. -/
noncomputable def doorIdealModulus15 :
    Ideal DoorEisensteinIntegers :=
  Ideal.span ({(15 : DoorEisensteinIntegers)} :
    Set DoorEisensteinIntegers)

/-- On ideals coprime to the modulus, character values are nonzero. -/
theorem eisensteinIdealCharacter15_ne_zero
    (I : Ideal DoorEisensteinIntegers)
    (hI : IsCoprime I doorIdealModulus15) :
    eisensteinIdealCharacter15 I ≠ 0 := by
  have hpow := eisensteinIdealCharacter15_pow_four I hI
  intro hz
  rw [hz] at hpow
  norm_num at hpow

/-- The intended character value on a fraction of integral ideals. -/
noncomputable def idealFractionValue15
    (I J : Ideal DoorEisensteinIntegers) : ℂ :=
  eisensteinIdealCharacter15 I /
    eisensteinIdealCharacter15 J

/--
Equal cross-products give equal fraction values,
provided the denominators are coprime to the modulus.
-/
theorem idealFractionValue15_eq_of_cross_mul
    (I J I' J' : Ideal DoorEisensteinIntegers)
    (hJ : IsCoprime J doorIdealModulus15)
    (hJ' : IsCoprime J' doorIdealModulus15)
    (hcross : I * J' = I' * J) :
    idealFractionValue15 I J =
      idealFractionValue15 I' J' := by
  unfold idealFractionValue15
  apply (div_eq_div_iff
    (eisensteinIdealCharacter15_ne_zero J hJ)
    (eisensteinIdealCharacter15_ne_zero J' hJ')).mpr
  have h := congrArg eisensteinIdealCharacter15 hcross
  simpa only [eisensteinIdealCharacter15_mul] using h

/-- Multiplying fractions multiplies their character values. -/
theorem idealFractionValue15_mul
    (I J I' J' : Ideal DoorEisensteinIntegers) :
    idealFractionValue15 (I * I') (J * J') =
      idealFractionValue15 I J *
        idealFractionValue15 I' J' := by
  unfold idealFractionValue15
  rw [eisensteinIdealCharacter15_mul,
    eisensteinIdealCharacter15_mul]
  ring

/-- An integral ideal is represented by denominator 1. -/
theorem idealFractionValue15_denominator_one
    (I : Ideal DoorEisensteinIntegers) :
    idealFractionValue15 I 1 =
      eisensteinIdealCharacter15 I := by
  unfold idealFractionValue15
  rw [map_one, div_one]

/-- Fractions with coprime numerator and denominator have fourth power 1. -/
theorem idealFractionValue15_pow_four
    (I J : Ideal DoorEisensteinIntegers)
    (hI : IsCoprime I doorIdealModulus15)
    (hJ : IsCoprime J doorIdealModulus15) :
    idealFractionValue15 I J ^ 4 = 1 := by
  unfold idealFractionValue15
  rw [div_pow,
    eisensteinIdealCharacter15_pow_four I hI,
    eisensteinIdealCharacter15_pow_four J hJ]
  norm_num

open scoped nonZeroDivisors

/-- Fractional ideals in the Eisenstein field. -/
abbrev DoorFractionalIdeal :=
  FractionalIdeal DoorEisensteinIntegers⁰ DoorEisensteinField

/-- Coprimality to the modulus guarantees a nonzero ideal. -/
theorem doorIdeal_ne_zero_of_coprime
    (I : Ideal DoorEisensteinIntegers)
    (hI : IsCoprime I doorIdealModulus15) :
    I ≠ 0 := by
  intro hz
  have h := eisensteinIdealCharacter15_ne_zero I hI
  apply h
  rw [hz, map_zero]

/-- Equal fractional ideals give equal character values. -/
theorem idealFractionValue15_eq_of_fractionalIdeal_eq
    (I J I' J' : Ideal DoorEisensteinIntegers)
    (hJ : IsCoprime J doorIdealModulus15)
    (hJ' : IsCoprime J' doorIdealModulus15)
    (h :
      (I : DoorFractionalIdeal) / (J : DoorFractionalIdeal) =
        (I' : DoorFractionalIdeal) / (J' : DoorFractionalIdeal)) :
    idealFractionValue15 I J =
      idealFractionValue15 I' J' := by
  have hJ0 : (J : DoorFractionalIdeal) ≠ 0 := by
    intro hz
    apply doorIdeal_ne_zero_of_coprime J hJ
    simpa only [Ideal.zero_eq_bot] using
      FractionalIdeal.coeIdeal_eq_zero.mp hz
  have hJ'0 : (J' : DoorFractionalIdeal) ≠ 0 := by
    intro hz
    apply doorIdeal_ne_zero_of_coprime J' hJ'
    simpa only [Ideal.zero_eq_bot] using
      FractionalIdeal.coeIdeal_eq_zero.mp hz
  have hcross : I * J' = I' * J := by
    apply FractionalIdeal.coeIdeal_injective
      (R := DoorEisensteinIntegers)
      (K := DoorEisensteinField)
    simpa only [FractionalIdeal.coeIdeal_mul] using
      (div_eq_div_iff hJ0 hJ'0).mp h
  exact idealFractionValue15_eq_of_cross_mul
    I J I' J' hJ hJ' hcross

/-- Fractional ideals admitting a representation coprime to the modulus. -/
def DoorCoprimeFractionalIdeal :=
  {F : DoorFractionalIdeal //
    ∃ I J : Ideal DoorEisensteinIntegers,
      IsCoprime I doorIdealModulus15 ∧
      IsCoprime J doorIdealModulus15 ∧
      F = (I : DoorFractionalIdeal) / (J : DoorFractionalIdeal)}

/-- Character value on an actual fractional ideal,
using any chosen coprime representation. -/
noncomputable def fractionalDoorCharacter15
    (F : DoorCoprimeFractionalIdeal) : ℂ :=
  idealFractionValue15
    (Classical.choose F.property)
    (Classical.choose (Classical.choose_spec F.property))

/-- Every coprime representation computes the same value. -/
theorem fractionalDoorCharacter15_eq
    (F : DoorCoprimeFractionalIdeal)
    (I J : Ideal DoorEisensteinIntegers)
    (_hI : IsCoprime I doorIdealModulus15)
    (hJ : IsCoprime J doorIdealModulus15)
    (hF : F.val =
      (I : DoorFractionalIdeal) / (J : DoorFractionalIdeal)) :
    fractionalDoorCharacter15 F = idealFractionValue15 I J := by
  let I₀ := Classical.choose F.property
  let J₀ := Classical.choose (Classical.choose_spec F.property)
  have h₀ :
      IsCoprime I₀ doorIdealModulus15 ∧
      IsCoprime J₀ doorIdealModulus15 ∧
      F.val =
        (I₀ : DoorFractionalIdeal) / (J₀ : DoorFractionalIdeal) :=
    Classical.choose_spec (Classical.choose_spec F.property)
  change idealFractionValue15 I₀ J₀ = idealFractionValue15 I J
  exact idealFractionValue15_eq_of_fractionalIdeal_eq
    I₀ J₀ I J h₀.2.1 hJ (h₀.2.2.symm.trans hF)

/-- The fractional character still has order dividing 4. -/
theorem fractionalDoorCharacter15_pow_four
    (F : DoorCoprimeFractionalIdeal) :
    fractionalDoorCharacter15 F ^ 4 = 1 := by
  obtain ⟨I, J, hI, hJ, hF⟩ := F.property
  rw [fractionalDoorCharacter15_eq F I J hI hJ hF]
  exact idealFractionValue15_pow_four I J hI hJ

/-- Invertible fractional ideals represented away from the modulus. -/
noncomputable def doorCoprimeFractionalIdealGroup :
    Subgroup DoorFractionalIdealˣ where
  carrier F :=
    ∃ I J : Ideal DoorEisensteinIntegers,
      IsCoprime I doorIdealModulus15 ∧
      IsCoprime J doorIdealModulus15 ∧
      (F : DoorFractionalIdeal) =
        (I : DoorFractionalIdeal) / (J : DoorFractionalIdeal)
  one_mem' := by
    refine ⟨1, 1, isCoprime_one_left, isCoprime_one_left, ?_⟩
    simp [Ideal.one_eq_top]
  mul_mem' := by
    intro F G hF hG
    obtain ⟨I, J, hI, hJ, hFI⟩ := hF
    obtain ⟨I', J', hI', hJ', hGI⟩ := hG
    refine ⟨I * I', J * J',
      hI.mul_left hI', hJ.mul_left hJ', ?_⟩
    simp only [Units.val_mul, hFI, hGI,
      FractionalIdeal.coeIdeal_mul, mul_div_mul_comm]
  inv_mem' := by
    intro F hF
    obtain ⟨I, J, hI, hJ, hFI⟩ := hF
    refine ⟨J, I, hJ, hI, ?_⟩
    rw [Units.val_inv_eq_inv_val, hFI, inv_div]

/-- Regard a member of the group as our earlier represented fractional ideal. -/
noncomputable def doorFractionalGroupToRepresented
    (F : doorCoprimeFractionalIdealGroup) :
    DoorCoprimeFractionalIdeal :=
  ⟨((F : DoorFractionalIdealˣ) : DoorFractionalIdeal), F.property⟩

/-- The ideal character, now bundled as a group-domain homomorphism. -/
noncomputable def fractionalDoorCharacterHom15 :
    doorCoprimeFractionalIdealGroup →* ℂ where
  toFun F :=
    fractionalDoorCharacter15 (doorFractionalGroupToRepresented F)
  map_one' := by
    rw [fractionalDoorCharacter15_eq
      (doorFractionalGroupToRepresented 1)
      1 1 isCoprime_one_left isCoprime_one_left
      (by simp [doorFractionalGroupToRepresented,
        Ideal.one_eq_top])]
    rw [idealFractionValue15_denominator_one, map_one]
  map_mul' F G := by
    obtain ⟨I, J, hI, hJ, hF⟩ := F.property
    obtain ⟨I', J', hI', hJ', hG⟩ := G.property
    have hFG :
        (doorFractionalGroupToRepresented (F * G)).val =
          ((I * I' : Ideal DoorEisensteinIntegers) :
            DoorFractionalIdeal) /
          ((J * J' : Ideal DoorEisensteinIntegers) :
            DoorFractionalIdeal) := by
      change
        (((F : DoorFractionalIdealˣ) : DoorFractionalIdeal) *
          ((G : DoorFractionalIdealˣ) : DoorFractionalIdeal)) =
        ((I * I' : Ideal DoorEisensteinIntegers) :
          DoorFractionalIdeal) /
        ((J * J' : Ideal DoorEisensteinIntegers) :
          DoorFractionalIdeal)
      simp only [hF, hG, FractionalIdeal.coeIdeal_mul,
        mul_div_mul_comm]
    rw [fractionalDoorCharacter15_eq
      (doorFractionalGroupToRepresented (F * G))
      (I * I') (J * J')
      (hI.mul_left hI') (hJ.mul_left hJ') hFG]
    rw [fractionalDoorCharacter15_eq
      (doorFractionalGroupToRepresented F) I J hI hJ hF]
    rw [fractionalDoorCharacter15_eq
      (doorFractionalGroupToRepresented G) I' J' hI' hJ' hG]
    exact idealFractionValue15_mul I J I' J'

/-- The bundled fractional character has order dividing 4. -/
theorem fractionalDoorCharacterHom15_pow_four
    (F : doorCoprimeFractionalIdealGroup) :
    fractionalDoorCharacterHom15 F ^ 4 = 1 := by
  exact fractionalDoorCharacter15_pow_four
    (doorFractionalGroupToRepresented F)

/-- Ratios of principal ideals with generators congruent to 1
have character value 1. -/
theorem idealFractionValue15_principal_congruent_one
    (a b : DoorEisensteinIntegers)
    (ha : (15 : DoorEisensteinIntegers) ∣ a - 1)
    (hb : (15 : DoorEisensteinIntegers) ∣ b - 1) :
    idealFractionValue15
      (Ideal.span ({a} : Set DoorEisensteinIntegers))
      (Ideal.span ({b} : Set DoorEisensteinIntegers)) = 1 := by
  unfold idealFractionValue15
  rw [eisensteinIdealCharacter15_span_of_congruent_one_auto a ha,
    eisensteinIdealCharacter15_span_of_congruent_one_auto b hb]
  norm_num

/-- Principal fraction relations with both generators congruent to 1. -/
def doorPrincipalOneRelations15 :
    Set doorCoprimeFractionalIdealGroup :=
  {F | ∃ a b : DoorEisensteinIntegers,
    (15 : DoorEisensteinIntegers) ∣ a - 1 ∧
    (15 : DoorEisensteinIntegers) ∣ b - 1 ∧
    IsCoprime
      (Ideal.span ({a} : Set DoorEisensteinIntegers))
      doorIdealModulus15 ∧
    IsCoprime
      (Ideal.span ({b} : Set DoorEisensteinIntegers))
      doorIdealModulus15 ∧
    ((F : DoorFractionalIdealˣ) : DoorFractionalIdeal) =
      ((Ideal.span ({a} : Set DoorEisensteinIntegers)) :
        DoorFractionalIdeal) /
      ((Ideal.span ({b} : Set DoorEisensteinIntegers)) :
        DoorFractionalIdeal)}

/-- The character kills each specified principal relation. -/
theorem fractionalDoorCharacterHom15_principal_one
    (F : doorCoprimeFractionalIdealGroup)
    (hF : F ∈ doorPrincipalOneRelations15) :
    fractionalDoorCharacterHom15 F = 1 := by
  obtain ⟨a, b, ha, hb, hIa, hIb, hrep⟩ := hF
  change fractionalDoorCharacter15
    (doorFractionalGroupToRepresented F) = 1
  rw [fractionalDoorCharacter15_eq
    (doorFractionalGroupToRepresented F)
    (Ideal.span ({a} : Set DoorEisensteinIntegers))
    (Ideal.span ({b} : Set DoorEisensteinIntegers))
    hIa hIb hrep]
  exact idealFractionValue15_principal_congruent_one a b ha hb

/-- The subgroup generated by these principal relations. -/
noncomputable def doorPrincipalOneSubgroup15 :
    Subgroup doorCoprimeFractionalIdealGroup :=
  Subgroup.closure doorPrincipalOneRelations15

/-- Every generated principal relation lies in the character's kernel. -/
theorem doorPrincipalOneSubgroup15_le_ker :
    doorPrincipalOneSubgroup15 ≤ fractionalDoorCharacterHom15.ker := by
  unfold doorPrincipalOneSubgroup15
  apply (Subgroup.closure_le fractionalDoorCharacterHom15.ker).mpr
  intro F hF
  change fractionalDoorCharacterHom15 F = 1
  exact fractionalDoorCharacterHom15_principal_one F hF

/-- The character descended to the quotient by these principal relations. -/
noncomputable def descendedDoorCharacter15 :
    (doorCoprimeFractionalIdealGroup ⧸ doorPrincipalOneSubgroup15) →* ℂ :=
  QuotientGroup.lift doorPrincipalOneSubgroup15
    fractionalDoorCharacterHom15 doorPrincipalOneSubgroup15_le_ker

/-- Descent preserves the original character values. -/
theorem descendedDoorCharacter15_apply
    (F : doorCoprimeFractionalIdealGroup) :
    descendedDoorCharacter15
      (QuotientGroup.mk' doorPrincipalOneSubgroup15 F) =
        fractionalDoorCharacterHom15 F := by
  rfl

/-- A principal ratio with congruent generators has character value 1,
provided its denominator is coprime to the modulus. -/
theorem idealFractionValue15_principal_ray_relation
    (a b : DoorEisensteinIntegers)
    (hab : (15 : DoorEisensteinIntegers) ∣ a - b)
    (hb : IsCoprime
      (Ideal.span ({b} : Set DoorEisensteinIntegers))
      doorIdealModulus15) :
    idealFractionValue15
      (Ideal.span ({a} : Set DoorEisensteinIntegers))
      (Ideal.span ({b} : Set DoorEisensteinIntegers)) = 1 := by
  unfold idealFractionValue15
  rw [eisensteinIdealCharacter15_span_eq_of_congruent a b hab]
  exact div_self
    (eisensteinIdealCharacter15_ne_zero
      (Ideal.span ({b} : Set DoorEisensteinIntegers)) hb)

/-- Principal fractional relations with congruent, coprime generators. -/
def doorPrincipalRayRelations15 :
    Set doorCoprimeFractionalIdealGroup :=
  {F | ∃ a b : DoorEisensteinIntegers,
    (15 : DoorEisensteinIntegers) ∣ a - b ∧
    IsCoprime
      (Ideal.span ({a} : Set DoorEisensteinIntegers))
      doorIdealModulus15 ∧
    IsCoprime
      (Ideal.span ({b} : Set DoorEisensteinIntegers))
      doorIdealModulus15 ∧
    ((F : DoorFractionalIdealˣ) : DoorFractionalIdeal) =
      ((Ideal.span ({a} : Set DoorEisensteinIntegers)) :
        DoorFractionalIdeal) /
      ((Ideal.span ({b} : Set DoorEisensteinIntegers)) :
        DoorFractionalIdeal)}

/-- The character kills every specified principal ray relation. -/
theorem fractionalDoorCharacterHom15_principal_ray
    (F : doorCoprimeFractionalIdealGroup)
    (hF : F ∈ doorPrincipalRayRelations15) :
    fractionalDoorCharacterHom15 F = 1 := by
  obtain ⟨a, b, hab, hIa, hIb, hrep⟩ := hF
  change fractionalDoorCharacter15
    (doorFractionalGroupToRepresented F) = 1
  rw [fractionalDoorCharacter15_eq
    (doorFractionalGroupToRepresented F)
    (Ideal.span ({a} : Set DoorEisensteinIntegers))
    (Ideal.span ({b} : Set DoorEisensteinIntegers))
    hIa hIb hrep]
  exact idealFractionValue15_principal_ray_relation a b hab hIb

/-- The subgroup generated by principal ray relations. -/
noncomputable def doorPrincipalRaySubgroup15 :
    Subgroup doorCoprimeFractionalIdealGroup :=
  Subgroup.closure doorPrincipalRayRelations15

/-- The earlier relations are included among the general ray relations. -/
theorem doorPrincipalOneRelations15_subset_ray :
    doorPrincipalOneRelations15 ⊆ doorPrincipalRayRelations15 := by
  intro F hF
  obtain ⟨a, b, ha, hb, hIa, hIb, hrep⟩ := hF
  refine ⟨a, b, ?_, hIa, hIb, hrep⟩
  have h := dvd_sub ha hb
  simpa only [sub_sub_sub_cancel_right] using h

/-- The earlier subgroup is contained in the enlarged subgroup. -/
theorem doorPrincipalOneSubgroup15_le_ray :
    doorPrincipalOneSubgroup15 ≤ doorPrincipalRaySubgroup15 := by
  exact Subgroup.closure_mono doorPrincipalOneRelations15_subset_ray

/-- The enlarged subgroup lies in the character's kernel. -/
theorem doorPrincipalRaySubgroup15_le_ker :
    doorPrincipalRaySubgroup15 ≤ fractionalDoorCharacterHom15.ker := by
  unfold doorPrincipalRaySubgroup15
  apply (Subgroup.closure_le fractionalDoorCharacterHom15.ker).mpr
  intro F hF
  change fractionalDoorCharacterHom15 F = 1
  exact fractionalDoorCharacterHom15_principal_ray F hF

/-- Our quotient by the specified principal ray relations. -/
abbrev DoorRayQuotient15 :=
  doorCoprimeFractionalIdealGroup ⧸ doorPrincipalRaySubgroup15

/-- The character descends through the enlarged principal subgroup. -/
noncomputable def descendedDoorRayCharacter15 :
    DoorRayQuotient15 →* ℂ :=
  QuotientGroup.lift doorPrincipalRaySubgroup15
    fractionalDoorCharacterHom15 doorPrincipalRaySubgroup15_le_ker

/-- The descended character reproduces the fractional character values. -/
theorem descendedDoorRayCharacter15_apply
    (F : doorCoprimeFractionalIdealGroup) :
    descendedDoorRayCharacter15
      (QuotientGroup.mk' doorPrincipalRaySubgroup15 F) =
        fractionalDoorCharacterHom15 F := by
  rfl

/-- The descended ray character has order dividing 4. -/
theorem descendedDoorRayCharacter15_pow_four
    (x : DoorRayQuotient15) :
    descendedDoorRayCharacter15 x ^ 4 = 1 := by
  refine QuotientGroup.induction_on x ?_
  intro F
  change fractionalDoorCharacterHom15 F ^ 4 = 1
  exact fractionalDoorCharacterHom15_pow_four F

/-- Consequently, every descended character value is nonzero. -/
theorem descendedDoorRayCharacter15_ne_zero
    (x : DoorRayQuotient15) :
    descendedDoorRayCharacter15 x ≠ 0 := by
  intro hz
  have h := descendedDoorRayCharacter15_pow_four x
  rw [hz] at h
  norm_num at h

end HireCharacterReadout
