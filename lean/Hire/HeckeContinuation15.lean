import Hire.HeckeDirichletProduct15
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Nonvanishing

open scoped Topology
namespace HireCharacterReadout

/-- The companion character is nonprincipal: its value at 2 is i. -/
theorem companionCharacter15_ne_one :
    companionCharacter15 ≠ 1 := by
  intro h
  have hu : IsUnit (2 : ZMod 15) :=
    (ZMod.isUnit_iff_coprime 2 15).mpr (by norm_num)
  have hv :
      companionCharacter15 (2 : ZMod 15) = Complex.I := by
    simpa [companion15, complex15, quarticFive, Hire.chi3] using
      companionCharacter15_apply_nat 2
  have he := congrArg
    (fun χ : DirichletCharacter ℂ 15 =>
      χ (2 : ZMod 15)) h
  rw [hv, MulChar.one_apply hu] at he
  have hre := congrArg Complex.re he
  norm_num at hre

/-- The companion L-function is holomorphic everywhere. -/
theorem companionCharacter15_LFunction_differentiable :
    Differentiable ℂ companionCharacter15.LFunction := by
  exact DirichletCharacter.differentiable_LFunction
    companionCharacter15_ne_one

/-- The paired Dirichlet function is holomorphic everywhere. -/
theorem pairedDoorLFunction15_differentiable :
    Differentiable ℂ pairedDoorLFunction15 := by
  unfold pairedDoorLFunction15
  exact complexCharacter15_LFunction_differentiable.mul
    companionCharacter15_LFunction_differentiable

/-- The analytic continuation of the Eisenstein ideal character series. -/
noncomputable def doorHeckeLFunction15 (s : ℂ) : ℂ :=
  pairedDoorLFunction15 s

/-- The continued ideal L-function is entire. -/
theorem doorHeckeLFunction15_differentiable :
    Differentiable ℂ doorHeckeLFunction15 := by
  exact pairedDoorLFunction15_differentiable

/-- The continuation agrees with the ideal series
in its half-plane of absolute convergence. -/
theorem doorHeckeLFunction15_eq_series
    {s : ℂ} (hs : 1 < s.re) :
    doorHeckeLFunction15 s = doorHeckeSeries15 s := by
  exact (doorHeckeSeries15_eq_pairedDoorLFunction15 hs).symm

/-- In the positive half-plane, the continued ideal function
vanishes exactly when the door or quartic L-function vanishes. -/
theorem doorHeckeLFunction15_eq_zero_iff
    {s : ℂ} (hs : 0 < s.re) :
    doorHeckeLFunction15 s = 0 ↔
      complexCharacter15.LFunction s = 0 ∨
        quarticCharacter5.LFunction s = 0 := by
  exact pairedDoorLFunction15_eq_zero_iff hs

/-- The continued ideal L-function is analytic everywhere. -/
theorem doorHeckeLFunction15_analyticOnNhd :
    AnalyticOnNhd ℂ doorHeckeLFunction15 Set.univ := by
  intro s _
  exact doorHeckeLFunction15_differentiable.analyticAt s

/-- Any entire function agreeing with the ideal series in its
half-plane of absolute convergence equals our continuation everywhere. -/
theorem doorHeckeLFunction15_unique
    {F : ℂ → ℂ}
    (hF : Differentiable ℂ F)
    (hagree : ∀ s : ℂ, 1 < s.re →
      F s = doorHeckeSeries15 s) :
    F = doorHeckeLFunction15 := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := by
    intro s _
    exact hF.analyticAt s

  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re

  have hevent :
      F =ᶠ[𝓝 (2 : ℂ)] doorHeckeLFunction15 := by
    have hnear :
        ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      hopen.mem_nhds (by norm_num)
    filter_upwards [hnear] with s hs
    exact (hagree s hs).trans
      (doorHeckeLFunction15_eq_series hs).symm

  exact hFa.eq_of_eventuallyEq
    doorHeckeLFunction15_analyticOnNhd hevent

/-- The continued ideal L-function has no zeros
in the closed half-plane Re(s) ≥ 1. -/
theorem doorHeckeLFunction15_ne_zero_of_one_le_re
    {s : ℂ} (hs : 1 ≤ s.re) :
    doorHeckeLFunction15 s ≠ 0 := by
  have hC : complexCharacter15.LFunction s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re
      complexCharacter15
      (Or.inl complexCharacter15_ne_one) hs
  have hComp : companionCharacter15.LFunction s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re
      companionCharacter15
      (Or.inl companionCharacter15_ne_one) hs
  change
    complexCharacter15.LFunction s *
      companionCharacter15.LFunction s ≠ 0
  exact mul_ne_zero hC hComp

/-- In particular, the continuation is nonzero at 1. -/
theorem doorHeckeLFunction15_one_ne_zero :
    doorHeckeLFunction15 1 ≠ 0 := by
  apply doorHeckeLFunction15_ne_zero_of_one_le_re
  norm_num

/-- The original ideal series is nonzero
throughout its half-plane of absolute convergence. -/
theorem doorHeckeSeries15_ne_zero
    {s : ℂ} (hs : 1 < s.re) :
    doorHeckeSeries15 s ≠ 0 := by
  rw [← doorHeckeLFunction15_eq_series hs]
  exact doorHeckeLFunction15_ne_zero_of_one_le_re hs.le

/-- Every nonzero value of the continued ideal L-function
has a zero-free disk around it. -/
theorem doorHeckeLFunction15_exists_zero_free_ball
    {s : ℂ} (hs : doorHeckeLFunction15 s ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, dist z s < ε →
        doorHeckeLFunction15 z ≠ 0 := by
  have hc : ContinuousAt doorHeckeLFunction15 s :=
    doorHeckeLFunction15_differentiable.continuous.continuousAt
  have hnear :
      ∀ᶠ z in 𝓝 s, doorHeckeLFunction15 z ≠ 0 :=
    hc.eventually_ne hs
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.mp hnear
  exact ⟨ε, hε, fun z hz => hball hz⟩

/-- Every point on Re(s) = 1 has a zero-free disk,
which also extends to the left of that line. -/
theorem doorHeckeLFunction15_zero_free_neighbourhood_on_one
    {s : ℂ} (hs : s.re = 1) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ, dist z s < ε →
        doorHeckeLFunction15 z ≠ 0 := by
  apply doorHeckeLFunction15_exists_zero_free_ball
  apply doorHeckeLFunction15_ne_zero_of_one_le_re
  exact hs.ge

end HireCharacterReadout
