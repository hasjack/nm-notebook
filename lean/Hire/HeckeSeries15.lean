import Hire.FractionalNormLift15
import Mathlib.NumberTheory.NumberField.DedekindZeta

namespace HireCharacterReadout

/-- Nonzero integral ideals of the Eisenstein integers. -/
abbrev DoorNonzeroIntegralIdeal :=
  {I : Ideal DoorEisensteinIntegers // I ≠ ⊥}

/-- A term of the ideal series for our norm-lift character. -/
noncomputable def doorHeckeTerm15
    (s : ℂ) (I : DoorNonzeroIntegralIdeal) : ℂ :=
  eisensteinIdealCharacter15 I.val /
    (Ideal.absNorm I.val : ℂ) ^ s

/-- The ideal-indexed series of the norm-lift character. -/
noncomputable def doorHeckeSeries15 (s : ℂ) : ℂ :=
  ∑' I : DoorNonzeroIntegralIdeal, doorHeckeTerm15 s I

/-- The numerator is exactly our door character at the ideal norm. -/
theorem doorHeckeTerm15_eq
    (s : ℂ) (I : DoorNonzeroIntegralIdeal) :
    doorHeckeTerm15 s I =
      complex15 (Ideal.absNorm I.val) /
        (Ideal.absNorm I.val : ℂ) ^ s := by
  unfold doorHeckeTerm15
  rw [eisensteinIdealCharacter15_apply]

/-- Every ideal-character coefficient has modulus at most 1. -/
theorem norm_eisensteinIdealCharacter15_le_one
    (I : Ideal DoorEisensteinIntegers) :
    ‖eisensteinIdealCharacter15 I‖ ≤ 1 := by
  change
    ‖complexCharacter15 (Ideal.absNorm I : ZMod 15)‖ ≤ 1
  exact complexCharacter15.norm_le_one (Ideal.absNorm I)

/-- A nonzero integral ideal has positive absolute norm. -/
theorem doorIntegralIdeal_absNorm_pos
    (I : DoorNonzeroIntegralIdeal) :
    0 < Ideal.absNorm I.val := by
  apply Nat.pos_of_ne_zero
  intro h
  exact I.property (Ideal.absNorm_eq_zero_iff.mp h)

/-- The term is dominated by the unweighted ideal-norm term. -/
theorem norm_doorHeckeTerm15_le
    (s : ℂ) (I : DoorNonzeroIntegralIdeal) :
    ‖doorHeckeTerm15 s I‖ ≤
      1 / Real.rpow (Ideal.absNorm I.val : ℝ) s.re := by
  have hn :
      ‖(Ideal.absNorm I.val : ℂ) ^ s‖ =
        Real.rpow (Ideal.absNorm I.val : ℝ) s.re := by
    simpa only [← Real.rpow_eq_pow] using
      Complex.norm_natCast_cpow_of_pos
        (doorIntegralIdeal_absNorm_pos I) s
  unfold doorHeckeTerm15
  rw [norm_div, hn]
  exact div_le_div_of_nonneg_right
    (norm_eisensteinIdealCharacter15_le_one I.val)
    (le_of_lt
      (Real.rpow_pos_of_pos
        (by exact_mod_cast doorIntegralIdeal_absNorm_pos I)
        s.re))

open Filter Complex Asymptotics
open scoped Topology

/-- The number of Eisenstein integral ideals of norm n. -/
noncomputable def doorIdealCount15 (n : ℕ) : ℕ :=
  Nat.card
    {I : Ideal DoorEisensteinIntegers // Ideal.absNorm I = n}

/-- Partial sums of the ideal counts have a finite linear-growth limit. -/
theorem tendsto_doorIdealCount15_sum_div :
    Tendsto
      (fun n : ℕ =>
        (∑ k ∈ Finset.Icc 1 n, (doorIdealCount15 k : ℝ)) /
          (n : ℝ))
      atTop
      (nhds (NumberField.dedekindZeta_residue DoorEisensteinField)) := by
  unfold NumberField.dedekindZeta_residue
  refine
    ((NumberField.Ideal.tendsto_norm_le_div_atTop₀
      DoorEisensteinField).comp tendsto_natCast_atTop_atTop).congr
      (fun n => ?_)
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  unfold doorIdealCount15
  rw [← add_left_inj 1,
    ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from
      Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card
        {I : Ideal DoorEisensteinIntegers // Ideal.absNorm I = 0}
      by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ =>
        Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- The unweighted norm-grouped ideal series converges for Re(s) > 1. -/
theorem LSeriesSummable_doorIdealCount15
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n => (doorIdealCount15 n : ℂ)) s := by
  have h :
      LSeriesSummable
        (fun n => ((doorIdealCount15 n : ℝ) : ℂ)) s := by
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (r := 1)
    · exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
        (by simpa using tendsto_doorIdealCount15_sum_div)
    · intro n
      exact Nat.cast_nonneg _
    · norm_num
    · exact hs
  simpa only [Complex.ofReal_natCast] using h

end HireCharacterReadout
