import Hire.FractionalNormLift15
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Topology.Algebra.InfiniteSum.Real

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

/-- The unweighted norm term, with zero norm omitted. -/
noncomputable def doorIdealNormWeight15
    (s : ℂ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    1 / Real.rpow (n : ℝ) s.re

theorem doorIdealNormWeight15_nonneg
    (s : ℂ) (n : ℕ) :
    0 ≤ doorIdealNormWeight15 s n := by
  unfold doorIdealNormWeight15
  split_ifs
  · exact le_rfl
  · exact one_div_nonneg.mpr
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The grouped ideal majorant is summable. -/
theorem summable_doorIdealCount15_mul_weight
    {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun n =>
        (doorIdealCount15 n : ℝ) *
          doorIdealNormWeight15 s n) := by
  have h :=
    (LSeriesSummable_doorIdealCount15 hs).norm
  refine h.congr ?_
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp only [hn, doorIdealNormWeight15,
      ite_true, mul_zero]
  · simp only [hn, doorIdealNormWeight15,
      ite_false, Complex.norm_natCast,
      ← Real.rpow_eq_pow]
    ring

/-- Summability of norm-grouped weights transfers to integral ideals. -/
theorem summable_doorIdealNormWeight15_all
    {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun I : Ideal DoorEisensteinIntegers =>
        doorIdealNormWeight15 s (Ideal.absNorm I)) := by
  classical
  have hpartition :
      ∀ I : Ideal DoorEisensteinIntegers,
        ∃! n : ℕ, I ∈
          {J : Ideal DoorEisensteinIntegers |
            Ideal.absNorm J = n} := by
    intro I
    refine ⟨Ideal.absNorm I, rfl, ?_⟩
    intro n hn
    exact hn.symm

  refine
    (summable_partition
      (fun I =>
        doorIdealNormWeight15_nonneg s (Ideal.absNorm I))
      hpartition).mpr ⟨?_, ?_⟩
  · intro n
    let : Finite
        {I : Ideal DoorEisensteinIntegers //
          Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    let : Fintype
        {I : Ideal DoorEisensteinIntegers //
          Ideal.absNorm I = n} :=
      Fintype.ofFinite _
    change Summable
      (fun I :
        {I : Ideal DoorEisensteinIntegers //
          Ideal.absNorm I = n} =>
        doorIdealNormWeight15 s (Ideal.absNorm I.val))
    exact (hasSum_fintype _).summable
  · have hfiber :
        ∀ n : ℕ,
          (∑' I :
              {I : Ideal DoorEisensteinIntegers //
                Ideal.absNorm I = n},
            doorIdealNormWeight15 s
              (Ideal.absNorm I.val)) =
          (doorIdealCount15 n : ℝ) *
            doorIdealNormWeight15 s n := by
      intro n
      let : Finite
          {I : Ideal DoorEisensteinIntegers //
            Ideal.absNorm I = n} :=
        (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
      let : Fintype
          {I : Ideal DoorEisensteinIntegers //
            Ideal.absNorm I = n} :=
        Fintype.ofFinite _
      calc
        _ = ∑' I :
            {I : Ideal DoorEisensteinIntegers //
              Ideal.absNorm I = n},
            doorIdealNormWeight15 s n := by
          apply tsum_congr
          intro I
          rw [I.property]
        _ = _ := by
          change
            (∑' _ :
              {I : Ideal DoorEisensteinIntegers //
                Ideal.absNorm I = n},
              doorIdealNormWeight15 s n) =
            (Nat.card
              {I : Ideal DoorEisensteinIntegers //
                Ideal.absNorm I = n} : ℝ) *
              doorIdealNormWeight15 s n
          rw [tsum_fintype, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul,
            Nat.card_eq_fintype_card]
    refine
      (summable_doorIdealCount15_mul_weight hs).congr ?_
    intro n
    change
      (doorIdealCount15 n : ℝ) *
          doorIdealNormWeight15 s n =
        ∑' I :
          {I : Ideal DoorEisensteinIntegers //
            Ideal.absNorm I = n},
          doorIdealNormWeight15 s (Ideal.absNorm I.val)
    exact (hfiber n).symm

/-- The unweighted majorant over nonzero ideals is summable. -/
theorem summable_doorIdealNormMajorant15
    {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun I : DoorNonzeroIntegralIdeal =>
        1 / Real.rpow
          (Ideal.absNorm I.val : ℝ) s.re) := by
  have h :=
    (summable_doorIdealNormWeight15_all hs).comp_injective
      (Subtype.coe_injective :
        Function.Injective
          (fun I : DoorNonzeroIntegralIdeal => I.val))
  refine h.congr ?_
  intro I
  change doorIdealNormWeight15 s (Ideal.absNorm I.val) =
    1 / Real.rpow (Ideal.absNorm I.val : ℝ) s.re
  unfold doorIdealNormWeight15
  rw [ite_eq_right (ne_of_gt (doorIntegralIdeal_absNorm_pos I))]

/-- Absolute convergence of the ideal-indexed character series. -/
theorem summable_norm_doorHeckeTerm15
    {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun I : DoorNonzeroIntegralIdeal =>
        ‖doorHeckeTerm15 s I‖) := by
  exact
    (summable_doorIdealNormMajorant15 hs).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun I => norm_doorHeckeTerm15_le s I)

/-- The ideal-indexed character series converges for Re(s) > 1. -/
theorem summable_doorHeckeTerm15
    {s : ℂ} (hs : 1 < s.re) :
    Summable (doorHeckeTerm15 s) :=
  summable_norm_iff.mp
    (summable_norm_doorHeckeTerm15 hs)

theorem hasSum_doorHeckeTerm15
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (doorHeckeTerm15 s) (doorHeckeSeries15 s) :=
  (summable_doorHeckeTerm15 hs).hasSum

end HireCharacterReadout
