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

end HireCharacterReadout
