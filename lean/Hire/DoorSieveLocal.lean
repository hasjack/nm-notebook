import Hire.Doors
import Mathlib

namespace HireDoorSieve

/-- A multiplier of a kept door cannot contain 3. -/
theorem kept_multiplier_three_free
    {p A r : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3)
    (hdoor : Hire.m0 p = A * r) :
    ¬ 3 ∣ A := by
  intro hA
  apply Hire.three_not_dvd_m0 hp hp3
  rw [hdoor]
  exact dvd_mul_of_dvd_left hA r

/-- If the remaining cofactor is prime other than 3,
the discarded door's factor of 3 lies in its multiplier. -/
theorem discarded_multiplier_three_dvd
    {p A r : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3)
    (hr : r.Prime) (hr3 : r ≠ 3)
    (hdoor : Hire.m1 p = A * r) :
    3 ∣ A := by
  have hd : 3 ∣ A * r := by
    rw [← hdoor]
    exact Hire.three_dvd_m1 hp hp3
  have hthree : Nat.Prime 3 := by norm_num
  rcases hthree.dvd_mul.mp hd with hA | hR
  · exact hA
  · exact False.elim
      (Hire.not_three_dvd_of_prime_ne_three hr hr3 hR)

section FiniteField

variable {F : Type*} [Field F]

/-- With A nonzero, the second linear form has one explicit root. -/
theorem linear_form_eq_zero_iff
    {A ε r : F} (hA : A ≠ 0) :
    A * r + ε = 0 ↔ r = -ε / A := by
  constructor
  · intro h
    apply (eq_div_iff hA).2
    linear_combination h
  · intro h
    have hr := (eq_div_iff hA).mp h
    linear_combination hr

variable [Fintype F] [DecidableEq F]

/-- Residues obstructing simultaneous primality of r and A*r+ε. -/
def localForbiddenResidues (A ε : F) : Finset F :=
  Finset.univ.filter
    (fun r => r = 0 ∨ A * r + ε = 0)

/-- The two forbidden residues are 0 and -ε/A. -/
theorem localForbiddenResidues_of_ne_zero
    {A ε : F} (hA : A ≠ 0) :
    localForbiddenResidues A ε =
      ({0, -ε / A} : Finset F) := by
  ext r
  simp only [localForbiddenResidues,
    Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  rw [linear_form_eq_zero_iff hA]

/-- If A=0, only r=0 is forbidden. -/
theorem localForbiddenResidues_card_of_zero
    {A ε : F} (hA : A = 0) (hε : ε ≠ 0) :
    (localForbiddenResidues A ε).card = 1 := by
  have hset :
      localForbiddenResidues A ε = ({0} : Finset F) := by
    ext r
    simp [localForbiddenResidues, hA, hε]
  rw [hset]
  simp

/-- Otherwise the two forbidden residues are distinct. -/
theorem localForbiddenResidues_card_of_ne_zero
    {A ε : F} (hA : A ≠ 0) (hε : ε ≠ 0) :
    (localForbiddenResidues A ε).card = 2 := by
  rw [localForbiddenResidues_of_ne_zero hA]
  have hroot : (0 : F) ≠ -ε / A :=
    Ne.symm (div_ne_zero (neg_ne_zero.mpr hε) hA)
  simp [hroot]

end FiniteField

/-- Local density correction at 3 with one forbidden residue. -/
theorem local_factor_three_one :
    (1 - (1 : ℝ) / 3) / (1 - 1 / 3) ^ 2 =
      3 / 2 := by
  norm_num

/-- Local density correction at 3 with two forbidden residues. -/
theorem local_factor_three_two :
    (1 - (2 : ℝ) / 3) / (1 - 1 / 3) ^ 2 =
      3 / 4 := by
  norm_num

section PrimeResidues

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]

/-- If ℓ divides A, there is one forbidden residue modulo ℓ. -/
theorem localForbiddenResidues_card_zmod_of_dvd
    (A : ℕ) (ε : ZMod ℓ)
    (hε : ε ≠ 0) (hd : ℓ ∣ A) :
    (localForbiddenResidues (A : ZMod ℓ) ε).card = 1 := by
  apply localForbiddenResidues_card_of_zero
  · exact (ZMod.natCast_eq_zero_iff A ℓ).mpr hd
  · exact hε

/-- If ℓ does not divide A, there are two forbidden residues. -/
theorem localForbiddenResidues_card_zmod_of_not_dvd
    (A : ℕ) (ε : ZMod ℓ)
    (hε : ε ≠ 0) (hd : ¬ ℓ ∣ A) :
    (localForbiddenResidues (A : ZMod ℓ) ε).card = 2 := by
  apply localForbiddenResidues_card_of_ne_zero
  · intro hz
    exact hd ((ZMod.natCast_eq_zero_iff A ℓ).mp hz)
  · exact hε

end PrimeResidues

/-- Doubling the local correction and summing over
the possible positive powers of 3 gives total weight 1. -/
theorem hasSum_discarded_three_weights :
    HasSum (fun b : ℕ => (2 : ℝ) / 3 ^ (b + 1)) 1 := by
  have hgeo :
      HasSum (fun b : ℕ => (1 / 3 : ℝ) ^ b)
        (1 - (1 / 3 : ℝ))⁻¹ :=
    hasSum_geometric_of_abs_lt_one (by norm_num)

  have hterm :
      (fun b : ℕ => (2 : ℝ) / 3 ^ (b + 1)) =
        (fun b : ℕ =>
          (2 / 3 : ℝ) * (1 / 3 : ℝ) ^ b) := by
    funext b
    simp [div_eq_mul_inv, pow_succ,
      mul_comm, mul_assoc]

  rw [hterm]
  convert hgeo.mul_left (2 / 3 : ℝ) using 1; norm_num

/-- The discarded family's normalized weights sum to 1. -/
theorem tsum_discarded_three_weights :
    (∑' b : ℕ, (2 : ℝ) / 3 ^ (b + 1)) = 1 :=
  hasSum_discarded_three_weights.tsum_eq

/-- Multiplying by any fixed coefficient preserves the balance. -/
theorem hasSum_scaled_discarded_three_weights (c : ℝ) :
    HasSum
      (fun b : ℕ => c * ((2 : ℝ) / 3 ^ (b + 1)))
      c := by
  simpa using hasSum_discarded_three_weights.mul_left c

/-- The first B positive powers of 3 carry weight 1 - 3⁻ᴮ. -/
theorem sum_discarded_three_weights (B : ℕ) :
    (∑ b ∈ Finset.range B,
      (2 : ℝ) / 3 ^ (b + 1)) =
        1 - 1 / (3 : ℝ) ^ B := by
  induction B with
  | zero =>
      simp
  | succ B ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [pow_succ, div_eq_mul_inv, mul_inv_rev]
      ring

/-- The coefficient weight omitted after B levels is exactly 3⁻ᴮ. -/
theorem discarded_three_weights_remainder (B : ℕ) :
    1 - (∑ b ∈ Finset.range B,
      (2 : ℝ) / 3 ^ (b + 1)) =
        1 / (3 : ℝ) ^ B := by
  rw [sum_discarded_three_weights]
  ring

/-- The same finite balance holds with any fixed coefficient. -/
theorem sum_scaled_discarded_three_weights
    (c : ℝ) (B : ℕ) :
    (∑ b ∈ Finset.range B,
      c * ((2 : ℝ) / 3 ^ (b + 1))) =
        c * (1 - 1 / (3 : ℝ) ^ B) := by
  rw [← Finset.mul_sum, sum_discarded_three_weights]

end HireDoorSieve
