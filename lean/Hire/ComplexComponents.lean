import Hire.TwoDoorReadout
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order

namespace HireCharacterReadout

/-- The imaginary character weight, expressed through residue conditions. -/
def imaginaryWeight15 (n : ℕ) : ℤ :=
  if (n % 3 = 1 ∧ n % 5 = 2) ∨
      (n % 3 = 2 ∧ n % 5 = 3) then 1
  else if (n % 3 = 1 ∧ n % 5 = 3) ∨
      (n % 3 = 2 ∧ n % 5 = 2) then -1
  else 0

theorem imaginaryWeight15_eq_im (n : ℕ) :
    (imaginaryWeight15 n : ℝ) = (complex15 n).im := by
  set r3 := n % 3 with h3
  set r5 := n % 5 with h5
  have hr3 : r3 < 3 := Nat.mod_lt n (by norm_num)
  have hr5 : r5 < 5 := Nat.mod_lt n (by norm_num)
  interval_cases r3 <;> interval_cases r5 <;>
    norm_num [imaginaryWeight15, complex15,
      quarticFive, Hire.chi3, ← h3, ← h5]

noncomputable def complexWeightedReadout15
    (S : Finset ℕ) (w : ℕ → ℝ) : ℂ :=
  ∑ n ∈ S, (w n : ℂ) * complex15 n

noncomputable def realDoorWeightedReadout15
    (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S,
    w n * ((ownerIndicator15 n : ℝ) -
      (discardedIndicator15 n : ℝ))

noncomputable def imaginaryWeightedReadout15
    (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, w n * (imaginaryWeight15 n : ℝ)

theorem complexWeightedReadout15_re
    (S : Finset ℕ) (w : ℕ → ℝ) :
    (complexWeightedReadout15 S w).re =
      -realDoorWeightedReadout15 S w := by
  simp [complexWeightedReadout15, realDoorWeightedReadout15,
    twoDoorIndicator15_sub, Finset.sum_neg_distrib]

theorem complexWeightedReadout15_im
    (S : Finset ℕ) (w : ℕ → ℝ) :
    (complexWeightedReadout15 S w).im =
      imaginaryWeightedReadout15 S w := by
  simp [complexWeightedReadout15, imaginaryWeightedReadout15,
    imaginaryWeight15_eq_im]

/-- The full complex readout consists of the two signed components. -/
theorem complexWeightedReadout15_eq_components
    (S : Finset ℕ) (w : ℕ → ℝ) :
    complexWeightedReadout15 S w =
      (-(realDoorWeightedReadout15 S w) : ℂ) +
        (imaginaryWeightedReadout15 S w : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [complexWeightedReadout15_re]
  · simp [complexWeightedReadout15_im]

/-- Prime-only logarithmic weights, including the prime two. -/
noncomputable def primeLogWeight15 (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) else 0

/-- The prime-only complex sum has the same exact decomposition. -/
theorem complexPrimeReadout15_eq_components (X : ℕ) :
    complexWeightedReadout15
        (Finset.range (X + 1)) primeLogWeight15 =
      (-(realDoorWeightedReadout15
        (Finset.range (X + 1)) primeLogWeight15) : ℂ) +
      (imaginaryWeightedReadout15
        (Finset.range (X + 1)) primeLogWeight15 : ℂ) *
          Complex.I := by
  exact complexWeightedReadout15_eq_components
    (Finset.range (X + 1)) primeLogWeight15

/-- The full complex Mangoldt partial sum for the door character. -/
noncomputable def complexMangoldtPartialSum15 (N : ℕ) : ℂ :=
  complexWeightedReadout15
    (Finset.Icc 1 N) ArithmeticFunction.vonMangoldt

/-- Its negative real component, expressed through the two doors. -/
noncomputable def realMangoldtComponent15 (N : ℕ) : ℝ :=
  realDoorWeightedReadout15
    (Finset.Icc 1 N) ArithmeticFunction.vonMangoldt

/-- Its imaginary component. -/
noncomputable def imaginaryMangoldtComponent15 (N : ℕ) : ℝ :=
  imaginaryWeightedReadout15
    (Finset.Icc 1 N) ArithmeticFunction.vonMangoldt

theorem complexMangoldtPartialSum15_eq_components (N : ℕ) :
    complexMangoldtPartialSum15 N =
      (-(realMangoldtComponent15 N) : ℂ) +
        (imaginaryMangoldtComponent15 N : ℂ) * Complex.I := by
  exact complexWeightedReadout15_eq_components
    (Finset.Icc 1 N) ArithmeticFunction.vonMangoldt

/-- The arithmetic cancellation hypothesis for a zero-free boundary θ. -/
def DoorCharacterCancellation15 (θ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ N : ℕ, 1 ≤ N →
      ‖complexMangoldtPartialSum15 N‖ ≤
        K * Real.rpow (N : ℝ) θ

/-- Controlling both components controls the full complex sum. -/
theorem norm_complexMangoldtPartialSum15_le_components (N : ℕ) :
    ‖complexMangoldtPartialSum15 N‖ ≤
      |realMangoldtComponent15 N| +
        |imaginaryMangoldtComponent15 N| := by
  rw [complexMangoldtPartialSum15_eq_components]
  calc
    _ ≤ ‖(-(realMangoldtComponent15 N) : ℂ)‖ +
        ‖(imaginaryMangoldtComponent15 N : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = _ := by simp

/-- Separate power bounds for the two components supply cancellation. -/
theorem doorCharacterCancellation15_of_component_bounds
    (θ K₁ K₂ : ℝ)
    (hK₁ : 0 < K₁)
    (hK₂ : 0 < K₂)
    (hreal : ∀ N : ℕ, 1 ≤ N →
      |realMangoldtComponent15 N| ≤
        K₁ * Real.rpow (N : ℝ) θ)
    (himag : ∀ N : ℕ, 1 ≤ N →
      |imaginaryMangoldtComponent15 N| ≤
        K₂ * Real.rpow (N : ℝ) θ) :
    DoorCharacterCancellation15 θ := by
  refine ⟨K₁ + K₂, add_pos hK₁ hK₂, ?_⟩
  intro N hN
  calc
    _ ≤ |realMangoldtComponent15 N| +
        |imaginaryMangoldtComponent15 N| :=
      norm_complexMangoldtPartialSum15_le_components N
    _ ≤ K₁ * Real.rpow (N : ℝ) θ +
        K₂ * Real.rpow (N : ℝ) θ :=
      add_le_add (hreal N hN) (himag N hN)
    _ = (K₁ + K₂) * Real.rpow (N : ℝ) θ := by ring

open Filter Asymptotics MeasureTheory
open scoped Topology

/-- The complex coefficients of the door-character Mangoldt series. -/
noncomputable def doorMangoldtCoefficient15 (n : ℕ) : ℂ :=
  complexCharacter15 (n : ZMod 15) *
    (ArithmeticFunction.vonMangoldt n : ℂ)

/-- Cancellation supplies the partial-sum growth hypothesis
used in Abel summation. -/
theorem complexMangoldtPartialSum15_isBigO
    {θ : ℝ} (hcancel : DoorCharacterCancellation15 θ) :
    complexMangoldtPartialSum15 =O[Filter.atTop]
      (fun N : ℕ => Real.rpow (N : ℝ) θ) := by
  obtain ⟨K, hK, hbound⟩ := hcancel
  refine isBigO_iff.mpr ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hp : 0 ≤ Real.rpow (N : ℝ) θ :=
    Real.rpow_nonneg (Nat.cast_nonneg N) θ
  rw [Real.norm_eq_abs, abs_of_nonneg hp]
  exact hbound N hN

/-- The arithmetic readout is the partial sum of the
Dirichlet-character Mangoldt coefficients. -/
theorem sum_doorMangoldtCoefficient15_eq
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, doorMangoldtCoefficient15 n) =
      complexMangoldtPartialSum15 N := by
  unfold complexMangoldtPartialSum15 complexWeightedReadout15
  apply Finset.sum_congr rfl
  intro n hn
  simp only [doorMangoldtCoefficient15, htable n]
  exact mul_comm _ _

/-- Abel summation expresses the logarithmic derivative
through the full complex arithmetic readout. -/
theorem doorMangoldt_logDerivative_eq_integral
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hcancel : DoorCharacterCancellation15 θ)
    {s : ℂ}
    (hs : 1 < s.re)
    (hθs : θ < s.re) :
    -deriv
        (LSeries (fun n =>
          complexCharacter15 (n : ZMod 15))) s /
      LSeries (fun n =>
        complexCharacter15 (n : ZMod 15)) s =
    s * ∫ t in Set.Ioi (1 : ℝ),
      complexMangoldtPartialSum15 ⌊t⌋₊ *
        (t : ℂ) ^ (-(s + 1)) := by
  have hcoeff :
      doorMangoldtCoefficient15 =
        ((fun n : ℕ =>
          complexCharacter15 (n : ZMod 15)) *
         (fun n : ℕ =>
          (ArithmeticFunction.vonMangoldt n : ℂ))) := by
    funext n
    simp only [doorMangoldtCoefficient15, Pi.mul_apply]

  have hsum :
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N, doorMangoldtCoefficient15 n) =
        complexMangoldtPartialSum15 := by
    funext N
    exact sum_doorMangoldtCoefficient15_eq htable N

  have hO :
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N, doorMangoldtCoefficient15 n)
        =O[Filter.atTop]
          (fun N : ℕ => Real.rpow (N : ℝ) θ) := by
    rw [hsum]
    exact complexMangoldtPartialSum15_isBigO hcancel

  have hS : LSeriesSummable doorMangoldtCoefficient15 s := by
    rw [hcoeff]
    exact
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt
        complexCharacter15 hs

  have hlog :
      LSeries doorMangoldtCoefficient15 s =
        -deriv
            (LSeries (fun n =>
              complexCharacter15 (n : ZMod 15))) s /
          LSeries (fun n =>
            complexCharacter15 (n : ZMod 15)) s := by
    rw [hcoeff]
    exact
      DirichletCharacter.LSeries_twist_vonMangoldt_eq
        complexCharacter15 hs

  rw [← hlog]
  have hint :=
    LSeries_eq_mul_integral
      doorMangoldtCoefficient15 hθ hθs hS hO
  simpa only [sum_doorMangoldtCoefficient15_eq htable] using hint

/-- The partial-sum step function used in the Abel integral. -/
noncomputable def doorMangoldtStep15 (t : ℝ) : ℂ :=
  complexMangoldtPartialSum15 ⌊t⌋₊

/-- The candidate analytic extension of the logarithmic derivative. -/
noncomputable def doorMangoldtMellin15 (s : ℂ) : ℂ :=
  s * mellin doorMangoldtStep15 (-s)

/-- The arithmetic partial sum vanishes at cutoff zero. -/
theorem complexMangoldtPartialSum15_zero :
    complexMangoldtPartialSum15 0 = 0 := by
  simp [complexMangoldtPartialSum15, complexWeightedReadout15]

/-- The step function vanishes below the first positive integer. -/
theorem doorMangoldtStep15_eq_zero
    {t : ℝ} (ht : t < 1) :
    doorMangoldtStep15 t = 0 := by
  unfold doorMangoldtStep15
  rw [Nat.floor_eq_zero.mpr ht]
  exact complexMangoldtPartialSum15_zero

/-- Local integrability follows from the finite partial-sum structure. -/
theorem doorMangoldtStep15_locallyIntegrableOn
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n) :
    LocallyIntegrableOn doorMangoldtStep15
      (Set.Ioi (0 : ℝ)) := by
  have hlocal :
      LocallyIntegrableOn
        (fun t : ℝ =>
          (1 : ℂ) *
            ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
              doorMangoldtCoefficient15 n)
        (Set.Ici (0 : ℝ)) :=
    locallyIntegrableOn_mul_sum_Icc
      doorMangoldtCoefficient15
      (le_refl (0 : ℝ))
      (locallyIntegrableOn_const (1 : ℂ))
  have hstep :
      (fun t : ℝ =>
        (1 : ℂ) *
          ∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
            doorMangoldtCoefficient15 n) =
        doorMangoldtStep15 := by
    funext t
    simp only [
      one_mul,
      sum_doorMangoldtCoefficient15_eq htable,
      doorMangoldtStep15
    ]
  rw [hstep] at hlocal
  exact hlocal.mono_set Set.Ioi_subset_Ici_self

/-- Cancellation transfers from natural cutoffs to the real step function. -/
theorem doorMangoldtStep15_isBigO_atTop
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hcancel : DoorCharacterCancellation15 θ) :
    doorMangoldtStep15 =O[Filter.atTop]
      (fun t : ℝ => Real.rpow t θ) := by
  have hfloorlim :
      Tendsto (fun t : ℝ => ⌊t⌋₊)
        Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop

  have hfloor :=
    (complexMangoldtPartialSum15_isBigO hcancel).comp_tendsto
      hfloorlim

  have hnat :
      (fun t : ℝ => (⌊t⌋₊ : ℝ)) =O[Filter.atTop]
        (fun t : ℝ => t) :=
    isEquivalent_nat_floor.isBigO

  have hrpow :=
    hnat.rpow hθ (eventually_ge_atTop (0 : ℝ))

  have hstep :
      (complexMangoldtPartialSum15 ∘
        (fun t : ℝ => ⌊t⌋₊)) =
      doorMangoldtStep15 := by
    funext t
    rfl

  have h := hfloor.trans hrpow
  rw [hstep] at h
  exact h

/-- Vanishing near zero gives every power bound there. -/
theorem doorMangoldtStep15_isBigO_near_zero (b : ℝ) :
    doorMangoldtStep15 =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun t : ℝ => Real.rpow t (-b)) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  have hlt :
      ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hlt] with t ht
  rw [doorMangoldtStep15_eq_zero ht, norm_zero, one_mul]
  exact norm_nonneg _

/-- The Mellin expression is holomorphic to the right
of the cancellation exponent. -/
theorem doorMangoldtMellin15_differentiableAt
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hcancel : DoorCharacterCancellation15 θ)
    {s : ℂ}
    (hs : θ < s.re) :
    DifferentiableAt ℂ doorMangoldtMellin15 s := by
  have htop :
      doorMangoldtStep15 =O[Filter.atTop]
        (fun t : ℝ => Real.rpow t (-(-θ))) := by
    simpa only [neg_neg] using
      doorMangoldtStep15_isBigO_atTop hθ hcancel

  have hupper : (-s).re < -θ := by
    simpa only [Complex.neg_re] using neg_lt_neg hs

  have hlower : -s.re - 1 < (-s).re := by
    simp only [Complex.neg_re]
    linarith

  have hm :
      DifferentiableAt ℂ (mellin doorMangoldtStep15) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow
      (doorMangoldtStep15_locallyIntegrableOn htable)
      htop
      hupper
      (doorMangoldtStep15_isBigO_near_zero (-s.re - 1))
      hlower

  have hcomp :
      DifferentiableAt ℂ
        (fun z : ℂ => mellin doorMangoldtStep15 (-z)) s :=
    hm.comp s (differentiableAt_id.neg)

  have hmul := differentiableAt_id.mul hcomp
  have hfun :
      (id * (fun z : ℂ => mellin doorMangoldtStep15 (-z))) =
        doorMangoldtMellin15 := by
    funext z
    rfl
  rw [hfun] at hmul
  exact hmul

/-- Holomorphicity throughout the open half-plane. -/
theorem doorMangoldtMellin15_differentiableOn
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hcancel : DoorCharacterCancellation15 θ) :
    DifferentiableOn ℂ doorMangoldtMellin15
      {s : ℂ | θ < s.re} := by
  intro s hs
  exact
    (doorMangoldtMellin15_differentiableAt
      htable hθ hcancel hs).differentiableWithinAt

/-- The step function vanishes up to and including one. -/
theorem doorMangoldtStep15_eq_zero_of_le_one
    {t : ℝ} (ht : t ≤ 1) :
    doorMangoldtStep15 t = 0 := by
  have hf : ⌊t⌋₊ ≤ 1 := by
    simpa using Nat.floor_mono ht
  have hcases : ⌊t⌋₊ = 0 ∨ ⌊t⌋₊ = 1 := by
    omega
  rcases hcases with hn | hn
  · simp [doorMangoldtStep15, hn,
      complexMangoldtPartialSum15_zero]
  · simp [doorMangoldtStep15, hn,
      complexMangoldtPartialSum15, complexWeightedReadout15]

/-- Restricting the step function to t > 1 changes nothing. -/
theorem doorMangoldtStep15_eq_indicator :
    doorMangoldtStep15 =
      (Set.Ioi (1 : ℝ)).indicator doorMangoldtStep15 := by
  funext t
  by_cases ht : 1 < t
  · simp [Set.indicator_of_mem, ht]
  · have hz :=
      doorMangoldtStep15_eq_zero_of_le_one (le_of_not_gt ht)
    simp [Set.indicator_of_notMem, ht, hz]

/-- The Mellin expression is exactly the Abel integral. -/
theorem doorMangoldtMellin15_eq_integral (s : ℂ) :
    doorMangoldtMellin15 s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        complexMangoldtPartialSum15 ⌊t⌋₊ *
          (t : ℂ) ^ (-(s + 1)) := by
  unfold doorMangoldtMellin15
  congr 1
  unfold mellin
  rw [doorMangoldtStep15_eq_indicator]
  simp_rw [← Set.indicator_smul]
  rw [integral_indicator measurableSet_Ioi]
  have hsubset :
      Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) :=
    Set.Ioi_subset_Ioi (by norm_num)
  rw [Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.mpr hsubset]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul, doorMangoldtStep15]
  rw [show -s - 1 = -(s + 1) by ring]
  exact mul_comm _ _

/-- On the original convergence half-plane, the holomorphic
Mellin expression equals the logarithmic derivative. -/
theorem doorMangoldtMellin15_eq_logDerivative
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hcancel : DoorCharacterCancellation15 θ)
    {s : ℂ}
    (hs : 1 < s.re)
    (hθs : θ < s.re) :
    doorMangoldtMellin15 s =
      -deriv
          (LSeries (fun n =>
            complexCharacter15 (n : ZMod 15))) s /
        LSeries (fun n =>
          complexCharacter15 (n : ZMod 15)) s := by
  rw [doorMangoldtMellin15_eq_integral]
  exact
    (doorMangoldt_logDerivative_eq_integral
      htable hθ hcancel hs hθs).symm

/-- The Mellin expression agrees with the logarithmic derivative
of the continued L-function in the original convergence region. -/
theorem doorMangoldtMellin15_eq_continued_logDerivative
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hcancel : DoorCharacterCancellation15 θ)
    {s : ℂ}
    (hs : 1 < s.re)
    (hθs : θ < s.re) :
    doorMangoldtMellin15 s =
      -deriv
          (DirichletCharacter.LFunction complexCharacter15) s /
        DirichletCharacter.LFunction complexCharacter15 s := by
  rw [
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries
      complexCharacter15 hs,
    DirichletCharacter.LFunction_eq_LSeries
      complexCharacter15 hs
  ]
  exact
    doorMangoldtMellin15_eq_logDerivative
      htable hθ hcancel hs hθs

/-- The division-free differential identity on Re(s) > 1. -/
theorem doorMangoldtMellin15_differential_identity
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hcancel : DoorCharacterCancellation15 θ)
    {s : ℂ}
    (hs : 1 < s.re)
    (hθs : θ < s.re) :
    deriv (DirichletCharacter.LFunction complexCharacter15) s +
      doorMangoldtMellin15 s *
        DirichletCharacter.LFunction complexCharacter15 s = 0 := by
  have hsone : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs

  have hne :
      DirichletCharacter.LFunction complexCharacter15 s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re
      complexCharacter15 (Or.inr hsone) hs.le

  have hquot :=
    doorMangoldtMellin15_eq_continued_logDerivative
      htable hθ hcancel hs hθs

  have hmul :
      doorMangoldtMellin15 s *
          DirichletCharacter.LFunction complexCharacter15 s =
        -deriv
          (DirichletCharacter.LFunction complexCharacter15) s :=
    (eq_div_iff hne).mp hquot

  rw [hmul]
  exact add_neg_cancel _

/-- For a cancellation exponent below one, the differential
identity holds throughout the original convergence half-plane. -/
theorem doorMangoldtMellin15_differential_identity_of_theta_lt_one
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcancel : DoorCharacterCancellation15 θ)
    {s : ℂ}
    (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction complexCharacter15) s +
      doorMangoldtMellin15 s *
        DirichletCharacter.LFunction complexCharacter15 s = 0 := by
  exact
    doorMangoldtMellin15_differential_identity
      htable hθ hcancel hs (hθ1.trans hs)

/-- The cancellation half-plane is connected. -/
theorem doorCancellationHalfPlane_preconnected (θ : ℝ) :
    IsPreconnected {s : ℂ | θ < s.re} := by
  have hconvex : Convex ℝ {s : ℂ | θ < s.re} := by
    exact
      (convex_Ioi θ).linear_preimage Complex.reCLM.toLinearMap
  exact hconvex.isPreconnected

/-- The differential identity extends throughout the
half-plane supplied by the cancellation estimate. -/
theorem doorMangoldtMellin15_differential_identity_halfPlane
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcancel : DoorCharacterCancellation15 θ)
    {s : ℂ}
    (hs : θ < s.re) :
    deriv (DirichletCharacter.LFunction complexCharacter15) s +
      doorMangoldtMellin15 s *
        DirichletCharacter.LFunction complexCharacter15 s = 0 := by
  let U : Set ℂ := {z : ℂ | θ < z.re}
  let L : ℂ → ℂ :=
    DirichletCharacter.LFunction complexCharacter15
  let F : ℂ → ℂ :=
    fun z => deriv L z + doorMangoldtMellin15 z * L z

  have hopen : IsOpen U := by
    exact isOpen_lt continuous_const Complex.continuous_re

  have hL : AnalyticOnNhd ℂ L U := by
    intro z hz
    exact
      (DirichletCharacter.differentiable_LFunction
        complexCharacter15_ne_one).analyticAt z

  have hH : AnalyticOnNhd ℂ doorMangoldtMellin15 U :=
    (doorMangoldtMellin15_differentiableOn
      htable hθ hcancel).analyticOnNhd hopen

  have hF : AnalyticOnNhd ℂ F U := by
    have h := hL.deriv.add (hH.mul hL)
    have hfun :
        (deriv L +
          (fun z : ℂ => doorMangoldtMellin15 z * L z)) = F := by
      funext z
      rfl
    rw [hfun] at h
    exact h

  have htwo : (2 : ℂ) ∈ U := by
    change θ < (2 : ℂ).re
    norm_num
    linarith

  have horiginal :
      {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := by
    exact
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num)

  have hevent :
      ∀ᶠ z : ℂ in nhds (2 : ℂ), F z = 0 := by
    filter_upwards [horiginal] with z hz
    exact
      doorMangoldtMellin15_differential_identity_of_theta_lt_one
        htable hθ hθ1 hcancel hz

  have hfreq :
      ∃ᶠ z : ℂ in nhdsWithin (2 : ℂ) {2}ᶜ, F z = 0 :=
    (hevent.filter_mono nhdsWithin_le_nhds).frequently

  have hall : Set.EqOn F 0 U :=
    hF.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (doorCancellationHalfPlane_preconnected θ)
      htwo hfreq

  exact hall hs

/-- A holomorphic solution of L' + H L = 0 on a connected
open set is nowhere zero if it is nonzero at one point. -/
theorem analytic_solution_ne_zero_of_differential_identity
    {U : Set ℂ}
    (hopen : IsOpen U)
    (hconnected : IsPreconnected U)
    {L H : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L U)
    (hH : AnalyticOnNhd ℂ H U)
    (hode : ∀ z ∈ U, deriv L z + H z * L z = 0)
    {x : ℂ}
    (hx : x ∈ U)
    (hxne : L x ≠ 0)
    {s : ℂ}
    (hs : s ∈ U) :
    L s ≠ 0 := by
  have hxorder : analyticOrderAt L x = 0 :=
    (hL x hx).analyticOrderAt_eq_zero.mpr hxne

  have hxfinite : analyticOrderAt L x ≠ ⊤ := by
    rw [hxorder]
    simp

  have hsfinite : analyticOrderAt L s ≠ ⊤ :=
    hL.analyticOrderAt_ne_top_of_isPreconnected
      hconnected hx hs hxfinite

  intro hzero

  have hspositive : analyticOrderAt L s ≠ 0 :=
    (hL s hs).analyticOrderAt_ne_zero.mpr hzero

  have hevent :
      deriv L =ᶠ[nhds s] -(H * L) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hzode := hode z hz
    change deriv L z = -(H z * L z)
    linear_combination hzode

  have horders := analyticOrderAt_congr hevent

  cases horder : analyticOrderAt L s with
  | top =>
      exact hsfinite horder
  | coe n =>
      cases n with
      | zero =>
          exact hspositive (by simpa using horder)
      | succ m =>
          have hd :
              analyticOrderAt (deriv L) s = (m : ℕ∞) := by
            apply analyticOrderAt_deriv_of_pos (hL s hs)
            simpa only [Nat.cast_succ] using horder

          rw [
            analyticOrderAt_neg,
            analyticOrderAt_mul (hH s hs) (hL s hs),
            horder,
            hd
          ] at horders

          have hle :
              ((m + 1 : ℕ) : ℕ∞) ≤
                analyticOrderAt H s + ((m + 1 : ℕ) : ℕ∞) :=
            le_add_left le_rfl

          rw [← horders] at hle
          have hnat : m + 1 ≤ m := by
            exact_mod_cast hle
          omega

/-- Full-complex Mangoldt cancellation gives a zero-free
half-plane for the continued door-character L-function. -/
theorem complexCharacter15_LFunction_ne_zero_of_cancellation
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcancel : DoorCharacterCancellation15 θ)
    {s : ℂ}
    (hs : θ < s.re) :
    DirichletCharacter.LFunction complexCharacter15 s ≠ 0 := by
  let U : Set ℂ := {z : ℂ | θ < z.re}

  have hopen : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re

  have hL :
      AnalyticOnNhd ℂ
        (DirichletCharacter.LFunction complexCharacter15) U := by
    intro z hz
    exact
      (DirichletCharacter.differentiable_LFunction
        complexCharacter15_ne_one).analyticAt z

  have hH :
      AnalyticOnNhd ℂ doorMangoldtMellin15 U :=
    (doorMangoldtMellin15_differentiableOn
      htable hθ hcancel).analyticOnNhd hopen

  have hode :
      ∀ z ∈ U,
        deriv (DirichletCharacter.LFunction complexCharacter15) z +
          doorMangoldtMellin15 z *
            DirichletCharacter.LFunction complexCharacter15 z = 0 := by
    intro z hz
    exact
      doorMangoldtMellin15_differential_identity_halfPlane
        htable hθ hθ1 hcancel hz

  have htwo : (2 : ℂ) ∈ U := by
    change θ < (2 : ℂ).re
    norm_num
    linarith

  have htwo_ne :
      DirichletCharacter.LFunction complexCharacter15 (2 : ℂ) ≠ 0 := by
    exact
      DirichletCharacter.LFunction_ne_zero_of_one_le_re
        complexCharacter15
        (Or.inl complexCharacter15_ne_one)
        (by norm_num)

  exact
    analytic_solution_ne_zero_of_differential_identity
      hopen
      (doorCancellationHalfPlane_preconnected θ)
      hL hH hode htwo htwo_ne hs

/-- Every value of the door character has modulus at most one. -/
theorem norm_complex15_le_one (n : ℕ) :
    ‖complex15 n‖ ≤ 1 := by
  set r3 := n % 3 with h3
  set r5 := n % 5 with h5
  have hr3 : r3 < 3 := Nat.mod_lt n (by norm_num)
  have hr5 : r5 < 5 := Nat.mod_lt n (by norm_num)
  interval_cases r3 <;> interval_cases r5 <;>
    norm_num [
      complex15, quarticFive, Hire.chi3,
      ← h3, ← h5, norm_mul
    ]

/-- The full complex prime-only readout. -/
noncomputable def complexPrimeLogSum15 (N : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * complex15 p

/-- On primes, the Mangoldt and logarithmic weights agree. -/
theorem complexPrimeLogSum15_eq_mangoldt_sum (N : ℕ) :
    complexPrimeLogSum15 N =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (ArithmeticFunction.vonMangoldt p : ℂ) * complex15 p := by
  unfold complexPrimeLogSum15
  apply Finset.sum_congr rfl
  intro p hp
  rw [ArithmeticFunction.vonMangoldt_apply_prime
    (Finset.mem_filter.mp hp).2]

/-- Removing the prime-only readout leaves the higher-power terms. -/
theorem complexMangoldt_sub_prime_eq_nonprime_sum (N : ℕ) :
    complexMangoldtPartialSum15 N - complexPrimeLogSum15 N =
      ∑ n ∈ Finset.Icc 1 N,
        if n.Prime then 0
        else
          (ArithmeticFunction.vonMangoldt n : ℂ) * complex15 n := by
  classical
  rw [complexPrimeLogSum15_eq_mangoldt_sum]
  unfold complexMangoldtPartialSum15 complexWeightedReadout15
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> simp [hp]

/-- The complex higher-power correction is bounded by
the total nonprime Mangoldt weight. -/
theorem norm_complexMangoldt_sub_prime_le_psi_sub_theta
    (N : ℕ) :
    ‖complexMangoldtPartialSum15 N - complexPrimeLogSum15 N‖ ≤
      Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) := by
  classical
  rw [complexMangoldt_sub_prime_eq_nonprime_sum]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        ‖if n.Prime then (0 : ℂ)
          else
            (ArithmeticFunction.vonMangoldt n : ℂ) * complex15 n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        if n.Prime then 0
        else (ArithmeticFunction.vonMangoldt n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime
      · simp [hp]
      · simp only [hp, ite_false]
        have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
          ArithmeticFunction.vonMangoldt_nonneg
        have hnorm :
            ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
              (ArithmeticFunction.vonMangoldt n : ℝ) := by
          simp [Real.norm_eq_abs, abs_of_nonneg hΛ]
        rw [norm_mul, hnorm]
        calc
          _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left
              (norm_complex15_le_one n) hΛ
          _ = _ := mul_one _
    _ = _ := sum_nonprime_vonMangoldt_eq_psi_sub_theta N

/-- An explicit square-root-times-log correction for
the full complex readout. -/
theorem norm_complexMangoldt_sub_prime_le_sqrt_log
    (N : ℕ) (hN : 1 ≤ N) :
    ‖complexMangoldtPartialSum15 N - complexPrimeLogSum15 N‖ ≤
      2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  calc
    _ ≤ Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) :=
      norm_complexMangoldt_sub_prime_le_psi_sub_theta N
    _ ≤ |Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ)| :=
      le_abs_self _
    _ ≤ _ :=
      Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hNR

/-- A complex prime-only bound transfers to the analytic
Mangoldt readout. -/
theorem norm_complexMangoldt_le_of_prime_bound
    (N : ℕ) (hN : 1 ≤ N)
    (E : ℝ)
    (hPrime : ‖complexPrimeLogSum15 N‖ ≤ E) :
    ‖complexMangoldtPartialSum15 N‖ ≤
      E + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  calc
    _ = ‖complexPrimeLogSum15 N +
        (complexMangoldtPartialSum15 N -
          complexPrimeLogSum15 N)‖ := by
      congr 1
      ring
    _ ≤ ‖complexPrimeLogSum15 N‖ +
        ‖complexMangoldtPartialSum15 N -
          complexPrimeLogSum15 N‖ :=
      norm_add_le _ _
    _ ≤ _ :=
      add_le_add hPrime
        (norm_complexMangoldt_sub_prime_le_sqrt_log N hN)

/-- Above exponent one half, the higher-power correction
can be absorbed into the same power bound. -/
theorem sqrt_log_correction_le_rpow
    (N : ℕ)
    {θ : ℝ}
    (hθ : (1 / 2 : ℝ) < θ)
    (hN : 1 ≤ N) :
    2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤
      (2 / (θ - 1 / 2)) * Real.rpow (N : ℝ) θ := by
  have hε : 0 < θ - 1 / 2 := by
    linarith
  have hx : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hlog :
      Real.log (N : ℝ) ≤
        Real.rpow (N : ℝ) (θ - 1 / 2) / (θ - 1 / 2) :=
    Real.log_le_rpow_div hx.le hε
  calc
    _ ≤ 2 * Real.sqrt (N : ℝ) *
        (Real.rpow (N : ℝ) (θ - 1 / 2) / (θ - 1 / 2)) :=
      mul_le_mul_of_nonneg_left hlog
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = (2 / (θ - 1 / 2)) *
        (Real.rpow (N : ℝ) (1 / 2) *
          Real.rpow (N : ℝ) (θ - 1 / 2)) := by
      rw [Real.sqrt_eq_rpow]
      simp only [Real.rpow_eq_pow]
      ring
    _ = (2 / (θ - 1 / 2)) * Real.rpow (N : ℝ) θ := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hx]
      rw [show (1 / 2 : ℝ) + (θ - 1 / 2) = θ by ring]

/-- A full-complex prime-only power bound supplies the
Mangoldt cancellation hypothesis. -/
theorem doorCharacterCancellation15_of_prime_bound
    {θ K : ℝ}
    (hθ : (1 / 2 : ℝ) < θ)
    (hK : 0 < K)
    (hPrime : ∀ N : ℕ, 1 ≤ N →
      ‖complexPrimeLogSum15 N‖ ≤
        K * Real.rpow (N : ℝ) θ) :
    DoorCharacterCancellation15 θ := by
  have hε : 0 < θ - 1 / 2 := by
    linarith
  refine ⟨K + 2 / (θ - 1 / 2),
    add_pos hK (div_pos (by norm_num) hε), ?_⟩
  intro N hN
  calc
    _ ≤ K * Real.rpow (N : ℝ) θ +
        2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
      norm_complexMangoldt_le_of_prime_bound
        N hN (K * Real.rpow (N : ℝ) θ) (hPrime N hN)
    _ ≤ K * Real.rpow (N : ℝ) θ +
        (2 / (θ - 1 / 2)) * Real.rpow (N : ℝ) θ :=
      add_le_add
        (le_refl (K * Real.rpow (N : ℝ) θ))
        (sqrt_log_correction_le_rpow N hθ hN)
    _ = (K + 2 / (θ - 1 / 2)) *
        Real.rpow (N : ℝ) θ := by
      ring

/-- Complex prime cancellation at an exponent between
one half and one gives the corresponding zero-free half-plane. -/
theorem complexCharacter15_LFunction_ne_zero_of_prime_bound
    (htable : ∀ n : ℕ,
      complexCharacter15 (n : ZMod 15) = complex15 n)
    {θ K : ℝ}
    (hθ : (1 / 2 : ℝ) < θ)
    (hθ1 : θ < 1)
    (hK : 0 < K)
    (hPrime : ∀ N : ℕ, 1 ≤ N →
      ‖complexPrimeLogSum15 N‖ ≤
        K * Real.rpow (N : ℝ) θ)
    {s : ℂ}
    (hs : θ < s.re) :
    DirichletCharacter.LFunction complexCharacter15 s ≠ 0 := by
  have hθ0 : 0 ≤ θ := by
    linarith
  exact
    complexCharacter15_LFunction_ne_zero_of_cancellation
      htable hθ0 hθ1
      (doorCharacterCancellation15_of_prime_bound hθ hK hPrime)
      hs

end HireCharacterReadout
