import Hire.IdealCountMultiplicative15
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace HireCharacterReadout

/-- Multiplicativity of the unbundled door character. -/
theorem doorComplex15_mul (a b : ℕ) :
    complex15 (a * b) = complex15 a * complex15 b := by
  rw [← complexCharacter15_apply_nat,
    Nat.cast_mul, map_mul,
    complexCharacter15_apply_nat,
    complexCharacter15_apply_nat]

/-- The norm-grouped coefficient of the ideal character series. -/
noncomputable def doorHeckeCoefficient15 (n : ℕ) : ℂ :=
  (doorIdealCount15 n : ℂ) * complex15 n

/-- The grouped ideal coefficient is the convolution of the two characters. -/
theorem doorCharacter_convolution_eq_coefficient
    (n : ℕ) (hn : n ≠ 0) :
    LSeries.convolution complex15 companion15 n =
      doorHeckeCoefficient15 n := by
  classical
  have hcount :
      (doorIdealCount15 n : ℂ) =
        ∑ d ∈ n.divisors, (Hire.chi3 d : ℂ) := by
    exact_mod_cast doorIdealCount15_eq_sum_chi3_divisors n hn
  rw [LSeries.convolution_def]
  change
    (∑ d ∈ n.divisorsAntidiagonal,
      complex15 d.1 * companion15 d.2) =
      doorHeckeCoefficient15 n
  rw [Nat.sum_divisorsAntidiagonal'
    (fun a b => complex15 a * companion15 b)]
  calc
    _ = ∑ d ∈ n.divisors,
        complex15 n * (Hire.chi3 d : ℂ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [companion15, ← mul_assoc,
        ← doorComplex15_mul,
        Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
    _ = complex15 n *
        ∑ d ∈ n.divisors, (Hire.chi3 d : ℂ) := by
      rw [Finset.mul_sum]
    _ = doorHeckeCoefficient15 n := by
      rw [← hcount]
      unfold doorHeckeCoefficient15
      exact mul_comm _ _

/-- The ideal series is the L-series of its norm-grouped coefficients. -/
theorem doorHeckeSeries15_eq_coefficient_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    doorHeckeSeries15 s =
      LSeries doorHeckeCoefficient15 s := by
  rw [doorHeckeSeries15_eq_norm_grouped hs]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, mul_zero]
  · rw [LSeries.term_of_ne_zero hn,
      LSeries.term_of_ne_zero hn,
      complexCharacter15_apply_nat]
    unfold doorHeckeCoefficient15
    ring

/-- Factorization into the two absolutely convergent Dirichlet series. -/
theorem doorHeckeSeries15_eq_Dirichlet_product
    {s : ℂ} (hs : 1 < s.re) :
    doorHeckeSeries15 s =
      LSeries complex15 s * LSeries companion15 s := by
  have hC : LSeriesSummable complex15 s := by
    simpa only [complexCharacter15_apply_nat] using
      DirichletCharacter.LSeriesSummable_of_one_lt_re
        complexCharacter15 hs
  have hComp : LSeriesSummable companion15 s := by
    simpa only [companionCharacter15_apply_nat] using
      DirichletCharacter.LSeriesSummable_of_one_lt_re
        companionCharacter15 hs
  calc
    _ = LSeries doorHeckeCoefficient15 s :=
      doorHeckeSeries15_eq_coefficient_LSeries hs
    _ = LSeries
        (LSeries.convolution complex15 companion15) s := by
      apply LSeries_congr
      intro n hn
      exact (doorCharacter_convolution_eq_coefficient n hn).symm
    _ = LSeries complex15 s * LSeries companion15 s :=
      LSeries_convolution' hC hComp

/-- The ideal series agrees with the paired continued L-functions
in the half-plane of absolute convergence. -/
theorem doorHeckeSeries15_eq_pairedDoorLFunction15
    {s : ℂ} (hs : 1 < s.re) :
    doorHeckeSeries15 s = pairedDoorLFunction15 s := by
  have hC :
      LSeries complex15 s =
        complexCharacter15.LFunction s := by
    simpa only [complexCharacter15_apply_nat] using
      (DirichletCharacter.LFunction_eq_LSeries
        complexCharacter15 hs).symm
  have hComp :
      LSeries companion15 s =
        companionCharacter15.LFunction s := by
    simpa only [companionCharacter15_apply_nat] using
      (DirichletCharacter.LFunction_eq_LSeries
        companionCharacter15 hs).symm
  rw [doorHeckeSeries15_eq_Dirichlet_product hs,
    hC, hComp]
  rfl

end HireCharacterReadout
