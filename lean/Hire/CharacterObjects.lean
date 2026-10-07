import Mathlib
import Hire.CharacterReadout

namespace HireCharacterReadout

/-- A nonunit modulo 15 has a representative not coprime to 15. -/
theorem not_coprime_val_of_not_isUnit15
    (z : ZMod 15) (hz : ¬ IsUnit z) :
    ¬ Nat.Coprime z.val 15 := by
  intro hc
  apply hz
  have hu : IsUnit (z.val : ZMod 15) :=
    (ZMod.isUnit_iff_coprime z.val 15).mpr hc
  simpa only [ZMod.natCast_zmod_val] using hu

set_option maxHeartbeats 2000000

/-- The quadratic table defines a Dirichlet character modulo 15. -/
noncomputable def quadraticCharacter15 :
    DirichletCharacter ℂ 15 where
  toFun z := (quadratic15 z.val : ℂ)
  map_one' := by
    change (quadratic15 1 : ℂ) = 1
    norm_num [quadratic15]
  map_mul' := by
    intro a b
    change
      (quadratic15 ((a.val * b.val) % 15) : ℂ) =
        (quadratic15 a.val : ℂ) * (quadratic15 b.val : ℂ)
    set r := a.val with hr
    set s := b.val with hs
    have hrlt : r < 15 := a.val_lt
    have hslt : s < 15 := b.val_lt
    interval_cases r <;> interval_cases s <;>
      norm_num [quadratic15, ← hr, ← hs]
  map_nonunit' := by
    intro z hz
    have hc := not_coprime_val_of_not_isUnit15 z hz
    set r := z.val with hr
    have hrlt : r < 15 := z.val_lt
    interval_cases r <;>
      norm_num [quadratic15, ← hr] at *

/-- The complex table defines a Dirichlet character modulo 15. -/
noncomputable def complexCharacter15 :
    DirichletCharacter ℂ 15 where
  toFun z := complex15 z.val
  map_one' := by
    change complex15 1 = 1
    norm_num [complex15, quarticFive, Hire.chi3]
  map_mul' := by
    intro a b
    change
      complex15 ((a.val * b.val) % 15) =
        complex15 a.val * complex15 b.val
    set r := a.val with hr
    set s := b.val with hs
    have hrlt : r < 15 := a.val_lt
    have hslt : s < 15 := b.val_lt
    interval_cases r <;> interval_cases s <;>
      norm_num [complex15, quarticFive, Hire.chi3, ← hr, ← hs]
  map_nonunit' := by
    intro z hz
    have hc := not_coprime_val_of_not_isUnit15 z hz
    set r := z.val with hr
    have hrlt : r < 15 := z.val_lt
    interval_cases r <;>
      norm_num [complex15, quarticFive, Hire.chi3, ← hr] at *

/-- Reducing modulo 15 preserves the quadratic table. -/
theorem quadratic15_mod_fifteen (n : ℕ) :
    quadratic15 (n % 15) = quadratic15 n := by
  have h3 : (n % 15) % 3 = n % 3 := by omega
  have h5 : (n % 15) % 5 = n % 5 := by omega
  simp only [quadratic15, h3, h5]

/-- Reducing modulo 15 preserves the complex table. -/
theorem complex15_mod_fifteen (n : ℕ) :
    complex15 (n % 15) = complex15 n := by
  have h3 : (n % 15) % 3 = n % 3 := by omega
  have h5 : (n % 15) % 5 = n % 5 := by omega
  simp only [complex15, quarticFive, Hire.chi3, h3, h5]

/-- The bundled quadratic character reproduces a natural-number table. -/
theorem quadraticCharacter15_apply_nat (n : ℕ) :
    quadraticCharacter15 (n : ZMod 15) =
      (quadratic15 n : ℂ) := by
  change (quadratic15 (n : ZMod 15).val : ℂ) =
    (quadratic15 n : ℂ)
  rw [ZMod.val_natCast, quadratic15_mod_fifteen]

/-- The bundled complex character reproduces a natural-number table. -/
theorem complexCharacter15_apply_nat (n : ℕ) :
    complexCharacter15 (n : ZMod 15) = complex15 n := by
  change complex15 (n : ZMod 15).val = complex15 n
  rw [ZMod.val_natCast, complex15_mod_fifteen]

/-- The real part of the negative logarithmic derivative of a character's L-series. -/
noncomputable def characterMangoldtValue15
    (χ : DirichletCharacter ℂ 15) (σ : ℝ) : ℝ :=
  (-deriv (LSeries (fun n => χ (n : ZMod 15))) (σ : ℂ) /
    LSeries (fun n => χ (n : ZMod 15)) (σ : ℂ)).re

/-- A character-weighted Mangoldt series converges to its analytic value. -/
theorem hasSum_weighted_character15
    (χ : DirichletCharacter ℂ 15)
    {σ : ℝ} (hσ : 1 < σ) :
    HasSum
      (fun n =>
        mangoldtDirichletWeight σ n *
          (χ (n : ZMod 15)).re)
      (characterMangoldtValue15 χ σ) := by
  have hσC : 1 < (σ : ℂ).re := by
    simpa using hσ

  have hterm (n : ℕ) :
      mangoldtDirichletWeight σ n *
          (χ (n : ZMod 15)).re =
        (LSeries.term
          (fun m =>
            χ (m : ZMod 15) *
              (ArithmeticFunction.vonMangoldt m : ℂ))
          (σ : ℂ) n).re := by
    by_cases hn : n = 0
    · subst n
      simp [mangoldtDirichletWeight]
    · rw [LSeries.term_of_ne_zero hn]
      have hpow :
          (n : ℂ) ^ (σ : ℂ) =
            (Real.rpow (n : ℝ) σ : ℂ) := by
        simpa only [Complex.ofReal_natCast,
          ← Real.rpow_eq_pow] using
          (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
      rw [hpow, mul_div_assoc, ← Complex.ofReal_div]
      simp [mangoldtDirichletWeight, Complex.mul_re, mul_comm]

  have hs :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hσC

  have hvalue :
      LSeries
        (fun n =>
          χ (n : ZMod 15) *
            (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ : ℂ) =
      -deriv (LSeries (fun n => χ (n : ZMod 15))) (σ : ℂ) /
        LSeries (fun n => χ (n : ZMod 15)) (σ : ℂ) := by
    have hf :
        ((fun n : ℕ => χ (n : ZMod 15)) *
          (fun n : ℕ =>
            (ArithmeticFunction.vonMangoldt n : ℂ))) =
        (fun n : ℕ =>
          χ (n : ZMod 15) *
            (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      funext n
      rfl
    have h :=
      DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hσC
    rw [hf] at h
    exact h

  have hc :
      HasSum
        (LSeries.term
          (fun n =>
            χ (n : ZMod 15) *
              (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ : ℂ))
        (-deriv (LSeries (fun n => χ (n : ZMod 15))) (σ : ℂ) /
          LSeries (fun n => χ (n : ZMod 15)) (σ : ℂ)) := by
    have h := hs.LSeriesHasSum
    change HasSum
      (LSeries.term
        (fun n =>
          χ (n : ZMod 15) *
            (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ : ℂ))
      (LSeries
        (fun n =>
          χ (n : ZMod 15) *
            (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ : ℂ)) at h
    rw [hvalue] at h
    exact h

  have hr := Complex.reCLM.hasSum hc
  simpa only [Complex.reCLM_apply, ← hterm,
    characterMangoldtValue15] using hr

/-- Finite character-weighted sums approach the same analytic value. -/
theorem tendsto_weighted_character15
    (χ : DirichletCharacter ℂ 15)
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          mangoldtDirichletWeight σ n *
            (χ (n : ZMod 15)).re)
      Filter.atTop
      (nhds (characterMangoldtValue15 χ σ)) := by
  apply tendsto_sum_Icc_one_of_hasSum
    (hasSum_weighted_character15 χ hσ)
  simp [mangoldtDirichletWeight]

/-- The quadratic contribution has its L-series limit. -/
theorem tendsto_quadraticMangoldtSum15
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          mangoldtDirichletWeight σ n *
            (quadratic15 n : ℝ))
      Filter.atTop
      (nhds (characterMangoldtValue15 quadraticCharacter15 σ)) := by
  simpa only [quadraticCharacter15_apply_nat,
    Complex.intCast_re] using
    tendsto_weighted_character15 quadraticCharacter15 hσ

/-- The complex contribution has its L-series limit. -/
theorem tendsto_complexMangoldtSum15
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          mangoldtDirichletWeight σ n * (complex15 n).re)
      Filter.atTop
      (nhds (characterMangoldtValue15 complexCharacter15 σ)) := by
  simpa only [complexCharacter15_apply_nat] using
    tendsto_weighted_character15 complexCharacter15 hσ

/-- The complete modulus-15 owner readout has an explicit analytic limit. -/
theorem tendsto_four_ownerMangoldtSum15
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ => 4 * ownerMangoldtSum15 N σ)
      Filter.atTop
      (nhds
        (zetaMangoldtValue σ -
          Real.log 3 / (Real.rpow 3 σ - 1) -
          Real.log 5 / (Real.rpow 5 σ - 1) +
          characterMangoldtValue15 quadraticCharacter15 σ -
          2 * characterMangoldtValue15 complexCharacter15 σ)) := by
  have hP := tendsto_principalMangoldtSum15 hσ
  have hQ := tendsto_quadraticMangoldtSum15 hσ
  have hC := tendsto_complexMangoldtSum15 hσ
  have hTwoC :
      Filter.Tendsto
        (fun N : ℕ =>
          2 * (∑ n ∈ Finset.Icc 1 N,
            mangoldtDirichletWeight σ n * (complex15 n).re))
        Filter.atTop
        (nhds
          (2 * characterMangoldtValue15 complexCharacter15 σ)) :=
    tendsto_const_nhds.mul hC
  simp_rw [ownerMangoldtSum15_decomposition]
  exact (hP.add hQ).sub hTwoC

/-- The quadratic character is nonprincipal: its value at 2 is -1. -/
theorem quadraticCharacter15_ne_one :
    quadraticCharacter15 ≠ 1 := by
  intro h
  have hu : IsUnit (2 : ZMod 15) :=
    (ZMod.isUnit_iff_coprime 2 15).mpr (by norm_num)
  have hv : quadraticCharacter15 (2 : ZMod 15) = (-1 : ℂ) := by
    simpa [quadratic15] using quadraticCharacter15_apply_nat 2
  have he := congrArg
    (fun χ : DirichletCharacter ℂ 15 => χ (2 : ZMod 15)) h
  rw [hv, MulChar.one_apply hu] at he
  norm_num at he

/-- The complex character is nonprincipal: its value at 2 is -i. -/
theorem complexCharacter15_ne_one :
    complexCharacter15 ≠ 1 := by
  intro h
  have hu : IsUnit (2 : ZMod 15) :=
    (ZMod.isUnit_iff_coprime 2 15).mpr (by norm_num)
  have hv :
      complexCharacter15 (2 : ZMod 15) = -Complex.I := by
    simpa [complex15, quarticFive, Hire.chi3] using
      complexCharacter15_apply_nat 2
  have he := congrArg
    (fun χ : DirichletCharacter ℂ 15 => χ (2 : ZMod 15)) h
  rw [hv, MulChar.one_apply hu] at he
  have hre := congrArg Complex.re he
  norm_num at hre

/-- The quadratic L-function does not vanish at 1. -/
theorem quadraticCharacter15_LFunction_one_ne_zero :
    quadraticCharacter15.LFunction 1 ≠ 0 := by
  exact DirichletCharacter.LFunction_apply_one_ne_zero
    quadraticCharacter15_ne_one

/-- The complex L-function does not vanish at 1. -/
theorem complexCharacter15_LFunction_one_ne_zero :
    complexCharacter15.LFunction 1 ≠ 0 := by
  exact DirichletCharacter.LFunction_apply_one_ne_zero
    complexCharacter15_ne_one

/-- The quadratic L-function is differentiable throughout the complex plane. -/
theorem quadraticCharacter15_LFunction_differentiable :
    Differentiable ℂ quadraticCharacter15.LFunction := by
  exact DirichletCharacter.differentiable_LFunction
    quadraticCharacter15_ne_one

/-- The complex L-function is differentiable throughout the complex plane. -/
theorem complexCharacter15_LFunction_differentiable :
    Differentiable ℂ complexCharacter15.LFunction := by
  exact DirichletCharacter.differentiable_LFunction
    complexCharacter15_ne_one

/-- The logarithmic-derivative readout using analytic continuation. -/
noncomputable def continuedCharacterMangoldtValue15
    (χ : DirichletCharacter ℂ 15) (σ : ℝ) : ℝ :=
  (-deriv χ.LFunction (σ : ℂ) /
    χ.LFunction (σ : ℂ)).re

/-- Above 1, the continued expression agrees with our series expression. -/
theorem continuedCharacterMangoldtValue15_eq
    (χ : DirichletCharacter ℂ 15)
    {σ : ℝ} (hσ : 1 < σ) :
    continuedCharacterMangoldtValue15 χ σ =
      characterMangoldtValue15 χ σ := by
  have hσC : 1 < (σ : ℂ).re := by
    simpa using hσ
  unfold continuedCharacterMangoldtValue15 characterMangoldtValue15
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hσC,
    DirichletCharacter.LFunction_eq_LSeries χ hσC]

/-- A nonprincipal character's continued readout is continuous at 1. -/
theorem continuousAt_continuedCharacterMangoldtValue15
    (χ : DirichletCharacter ℂ 15) (hχ : χ ≠ 1) :
    ContinuousAt (continuedCharacterMangoldtValue15 χ) 1 := by
  have hDiff : Differentiable ℂ χ.LFunction :=
    DirichletCharacter.differentiable_LFunction hχ
  have hD : Continuous (deriv χ.LFunction) :=
    hDiff.deriv.continuous
  have hnum :
      ContinuousAt
        (fun σ : ℝ => -deriv χ.LFunction (σ : ℂ)) 1 :=
    (hD.continuousAt.comp
      Complex.continuous_ofReal.continuousAt).neg
  have hden :
      ContinuousAt
        (fun σ : ℝ => χ.LFunction (σ : ℂ)) 1 :=
    hDiff.continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hne : χ.LFunction ((1 : ℝ) : ℂ) ≠ 0 := by
    simpa using DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hquot := hnum.div hden hne
  exact Complex.continuous_re.continuousAt.comp hquot

/-- From above 1, the series readout approaches a finite continued value. -/
theorem tendsto_characterMangoldtValue15_at_one
    (χ : DirichletCharacter ℂ 15) (hχ : χ ≠ 1) :
    Filter.Tendsto
      (characterMangoldtValue15 χ)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (continuedCharacterMangoldtValue15 χ 1)) := by
  have ht :
      Filter.Tendsto
        (continuedCharacterMangoldtValue15 χ)
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds (continuedCharacterMangoldtValue15 χ 1)) :=
    (continuousAt_continuedCharacterMangoldtValue15 χ hχ).tendsto.mono_left
      nhdsWithin_le_nhds
  have heq :
      continuedCharacterMangoldtValue15 χ =ᶠ[
        nhdsWithin 1 (Set.Ioi 1)] characterMangoldtValue15 χ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact continuedCharacterMangoldtValue15_eq χ hσ
  exact ht.congr' heq

/-- The quadratic contribution has a finite right-hand limit at 1. -/
theorem tendsto_quadraticMangoldtValue15_at_one :
    Filter.Tendsto
      (characterMangoldtValue15 quadraticCharacter15)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds
        (continuedCharacterMangoldtValue15 quadraticCharacter15 1)) := by
  exact tendsto_characterMangoldtValue15_at_one
    quadraticCharacter15 quadraticCharacter15_ne_one

/-- The complex contribution has a finite right-hand limit at 1. -/
theorem tendsto_complexMangoldtValue15_at_one :
    Filter.Tendsto
      (characterMangoldtValue15 complexCharacter15)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds
        (continuedCharacterMangoldtValue15 complexCharacter15 1)) := by
  exact tendsto_characterMangoldtValue15_at_one
    complexCharacter15 complexCharacter15_ne_one

/-- Scaling a finite right-hand limit by σ - 1 makes it vanish. -/
theorem tendsto_scaled_finite_limit_at_one
    {f : ℝ → ℝ} {A : ℝ}
    (hf : Filter.Tendsto f
      (nhdsWithin 1 (Set.Ioi 1)) (nhds A)) :
    Filter.Tendsto
      (fun σ : ℝ => (σ - 1) * f σ)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds 0) := by
  have hlin :
      Filter.Tendsto
        (fun σ : ℝ => σ - 1)
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds 0) := by
    have hc :
        ContinuousAt (fun σ : ℝ => σ - 1) 1 :=
      continuousAt_id.sub continuousAt_const
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa using hlin.mul hf

/-- The Euler correction contributed by powers of p. -/
noncomputable def primePowerCorrectionValue
    (p : ℕ) (σ : ℝ) : ℝ :=
  Real.log (p : ℝ) / (Real.rpow (p : ℝ) σ - 1)

/-- A prime-power correction has a finite limit at 1. -/
theorem tendsto_primePowerCorrectionValue_at_one
    {p : ℕ} (hp : p.Prime) :
    Filter.Tendsto
      (primePowerCorrectionValue p)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Real.log (p : ℝ) / ((p : ℝ) - 1))) := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by
    exact_mod_cast hp.ne_one
  have hpow :
      ContinuousAt (fun σ : ℝ => Real.rpow (p : ℝ) σ) 1 := by
    simpa only [← Real.rpow_eq_pow] using
      (Real.continuous_const_rpow (a := (p : ℝ)) hp0).continuousAt
  have hden :
      Real.rpow (p : ℝ) 1 - 1 ≠ 0 := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      sub_ne_zero.mpr hp1
  have hc :
      ContinuousAt (primePowerCorrectionValue p) 1 :=
    continuousAt_const.div
      (hpow.sub continuousAt_const) hden
  simpa only [primePowerCorrectionValue,
    Real.rpow_eq_pow, Real.rpow_one] using
    hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The scaled prime-power correction vanishes at 1. -/
theorem tendsto_scaled_primePowerCorrectionValue_at_one
    {p : ℕ} (hp : p.Prime) :
    Filter.Tendsto
      (fun σ : ℝ => (σ - 1) * primePowerCorrectionValue p σ)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds 0) := by
  exact tendsto_scaled_finite_limit_at_one
    (tendsto_primePowerCorrectionValue_at_one hp)

/-- The scaled quadratic contribution vanishes at 1. -/
theorem tendsto_scaled_quadraticMangoldtValue15_at_one :
    Filter.Tendsto
      (fun σ : ℝ =>
        (σ - 1) * characterMangoldtValue15 quadraticCharacter15 σ)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds 0) := by
  exact tendsto_scaled_finite_limit_at_one
    tendsto_quadraticMangoldtValue15_at_one

/-- The scaled complex contribution vanishes at 1. -/
theorem tendsto_scaled_complexMangoldtValue15_at_one :
    Filter.Tendsto
      (fun σ : ℝ =>
        (σ - 1) * characterMangoldtValue15 complexCharacter15 σ)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds 0) := by
  exact tendsto_scaled_finite_limit_at_one
    tendsto_complexMangoldtValue15_at_one

/-- Zeta with its pole at 1 multiplied away and its value there restored. -/
noncomputable def regularizedZetaAtOne : ℂ → ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 1

/-- The regularised function is differentiable everywhere. -/
theorem regularizedZetaAtOne_differentiable :
    Differentiable ℂ regularizedZetaAtOne := by
  exact DirichletCharacter.differentiable_LFunctionTrivChar₁ 1

/-- The restored value is the residue of zeta: 1. -/
theorem regularizedZetaAtOne_one :
    regularizedZetaAtOne 1 = 1 := by
  simp [regularizedZetaAtOne,
    DirichletCharacter.LFunctionTrivChar₁]

/-- Away from 1, regularisation is multiplication by s - 1. -/
theorem regularizedZetaAtOne_eq
    {s : ℂ} (hs : s ≠ 1) :
    regularizedZetaAtOne s = (s - 1) * riemannZeta s := by
  unfold regularizedZetaAtOne DirichletCharacter.LFunctionTrivChar₁
  rw [Function.update_of_ne hs]
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs]
  simp

/-- Differentiate the regularised identity away from the pole. -/
theorem deriv_regularizedZetaAtOne_eq
    {s : ℂ} (hs : s ≠ 1) :
    deriv regularizedZetaAtOne s =
      riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have hlocal :
      regularizedZetaAtOne =ᶠ[nhds s]
        (fun w : ℂ => (w - 1) * riemannZeta w) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with w hw
    exact regularizedZetaAtOne_eq hw
  rw [hlocal.deriv_eq]
  have hd :=
    ((hasDerivAt_id s).sub_const 1).mul
      (differentiableAt_riemannZeta hs).hasDerivAt
  have hf :
      ((fun x : ℂ => id x - 1) * riemannZeta) =
        (fun w : ℂ => (w - 1) * riemannZeta w) := by
    funext w
    rfl
  have he := hd.deriv
  rw [hf] at he
  simpa only [one_mul, id_eq] using he

/-- Isolate the leading pole term of the negative zeta log derivative. -/
theorem scaled_zeta_log_derivative_eq
    {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    (s - 1) * (-deriv riemannZeta s / riemannZeta s) =
      1 - (s - 1) *
        (deriv regularizedZetaAtOne s / regularizedZetaAtOne s) := by
  rw [regularizedZetaAtOne_eq hs, deriv_regularizedZetaAtOne_eq hs]
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  (field_simp [hs0, hz]; ring)

/-- The regularised logarithmic derivative has no pole at 1. -/
noncomputable def regularizedZetaLogReadout (σ : ℝ) : ℝ :=
  (deriv regularizedZetaAtOne (σ : ℂ) /
    regularizedZetaAtOne (σ : ℂ)).re

theorem continuousAt_regularizedZetaLogReadout :
    ContinuousAt regularizedZetaLogReadout 1 := by
  have hDiff := regularizedZetaAtOne_differentiable
  have hD : Continuous (deriv regularizedZetaAtOne) :=
    hDiff.deriv.continuous
  have hnum :
      ContinuousAt
        (fun σ : ℝ => deriv regularizedZetaAtOne (σ : ℂ)) 1 :=
    hD.continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hden :
      ContinuousAt
        (fun σ : ℝ => regularizedZetaAtOne (σ : ℂ)) 1 :=
    hDiff.continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hne : regularizedZetaAtOne ((1 : ℝ) : ℂ) ≠ 0 := by
    simp [regularizedZetaAtOne_one]
  exact Complex.continuous_re.continuousAt.comp
    (hnum.div hden hne)

/-- The complex pole identity expressed in our real readouts. -/
theorem scaled_zetaMangoldtValue_eq
    {σ : ℝ} (hσ : 1 < σ) :
    (σ - 1) * zetaMangoldtValue σ =
      1 - (σ - 1) * regularizedZetaLogReadout σ := by
  have hσC : 1 < (σ : ℂ).re := by
    simpa using hσ
  have hs : (σ : ℂ) ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    linarith
  have hz : riemannZeta (σ : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hσC
  have he :=
    congrArg Complex.re (scaled_zeta_log_derivative_eq hs hz)
  simpa [zetaMangoldtValue, regularizedZetaLogReadout,
    Complex.mul_re] using he

/-- Zeta supplies the leading coefficient 1. -/
theorem tendsto_scaled_zetaMangoldtValue_at_one :
    Filter.Tendsto
      (fun σ : ℝ => (σ - 1) * zetaMangoldtValue σ)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds 1) := by
  have hFinite :
      Filter.Tendsto regularizedZetaLogReadout
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds (regularizedZetaLogReadout 1)) :=
    continuousAt_regularizedZetaLogReadout.tendsto.mono_left
      nhdsWithin_le_nhds
  have hZero :=
    tendsto_scaled_finite_limit_at_one hFinite
  have hMain :
      Filter.Tendsto
        (fun σ : ℝ =>
          1 - (σ - 1) * regularizedZetaLogReadout σ)
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds 1) := by
    simpa using tendsto_const_nhds.sub hZero
  apply hMain.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (scaled_zetaMangoldtValue_eq hσ).symm

/-- The analytic limit of the first-level hub-5 Mangoldt readout. -/
noncomputable def ownerMangoldtLimit15 (σ : ℝ) : ℝ :=
  (zetaMangoldtValue σ -
    primePowerCorrectionValue 3 σ -
    primePowerCorrectionValue 5 σ +
    characterMangoldtValue15 quadraticCharacter15 σ -
    2 * characterMangoldtValue15 complexCharacter15 σ) / 4

/-- The finite owner readout converges to this analytic expression. -/
theorem tendsto_ownerMangoldtSum15
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ => ownerMangoldtSum15 N σ)
      Filter.atTop
      (nhds (ownerMangoldtLimit15 σ)) := by
  simpa [ownerMangoldtLimit15, primePowerCorrectionValue] using
    (tendsto_four_ownerMangoldtSum15 hσ).div_const 4

/-- The first-level hub-5 readout has leading coefficient 1/4 at 1. -/
theorem tendsto_scaled_ownerMangoldtLimit15_at_one :
    Filter.Tendsto
      (fun σ : ℝ => (σ - 1) * ownerMangoldtLimit15 σ)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (1 / 4 : ℝ)) := by
  have hZ := tendsto_scaled_zetaMangoldtValue_at_one
  have h3 :=
    tendsto_scaled_primePowerCorrectionValue_at_one
      (p := 3) (by norm_num)
  have h5 :=
    tendsto_scaled_primePowerCorrectionValue_at_one
      (p := 5) (by norm_num)
  have hQ := tendsto_scaled_quadraticMangoldtValue15_at_one
  have hC := tendsto_scaled_complexMangoldtValue15_at_one

  have hTwoC :
      Filter.Tendsto
        (fun σ : ℝ =>
          2 * ((σ - 1) *
            characterMangoldtValue15 complexCharacter15 σ))
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds 0) := by
    simpa using
      (show Filter.Tendsto
        (fun σ : ℝ =>
          2 * ((σ - 1) *
            characterMangoldtValue15 complexCharacter15 σ))
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((2 : ℝ) * 0)) from
          tendsto_const_nhds.mul hC)

  have hCombined :
      Filter.Tendsto
        (fun σ : ℝ =>
          ((σ - 1) * zetaMangoldtValue σ -
            (σ - 1) * primePowerCorrectionValue 3 σ -
            (σ - 1) * primePowerCorrectionValue 5 σ +
            (σ - 1) *
              characterMangoldtValue15 quadraticCharacter15 σ -
            2 * ((σ - 1) *
              characterMangoldtValue15 complexCharacter15 σ)) / 4)
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds (1 / 4 : ℝ)) := by
    simpa only [sub_zero, add_zero] using
      ((((hZ.sub h3).sub h5).add hQ).sub hTwoC).div_const 4

  convert hCombined using 1
  funext σ
  unfold ownerMangoldtLimit15
  ring

end HireCharacterReadout
