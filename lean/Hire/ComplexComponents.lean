import Hire.TwoDoorReadout
import Mathlib.NumberTheory.LSeries.SumCoeff

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

end HireCharacterReadout
