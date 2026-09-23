/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett

Exploratory lab note (coverage nest / lcm lattice). Not part of the Hire.lean
import barrel. Public voice: no ζ; doors and hire classes only.
-/
import Hire.Doors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Tactic

/-!
# Coverage lattice (lab)

Not the hire-graph barrel. Nest and lcm identities for door coverage of odd
ingredients `Q` with `3 ∤ Q`: if `Q ∣ R` then every prime hiring `R` (i.e.
`R ∣ m0 p`) also hires `Q`, and `A` and `B` hire the same owner iff
`lcm A B` does.
-/

namespace Hire

/-! ### Nest -/

/-- If `Q ∣ R` and `R ∣ m0 p`, then `Q ∣ m0 p`. -/
theorem dvd_m0_of_dvd_of_dvd_m0 {Q R p : ℕ} (hQR : Q ∣ R) (hRm0 : R ∣ m0 p) :
    Q ∣ m0 p :=
  Nat.dvd_trans hQR hRm0

/-- **Coverage nest.** Divisor ingredients inherit every owner of a multiple. -/
theorem coverage_nest {Q R p : ℕ}
    (_hQ : 1 < Q) (_hQodd : Odd Q) (_hQ3 : ¬ 3 ∣ Q)
    (_hp : p.Prime) (_hp3 : p ≠ 3)
    (hQR : Q ∣ R) (hRm0 : R ∣ m0 p) : Q ∣ m0 p :=
  dvd_m0_of_dvd_of_dvd_m0 hQR hRm0

/-! ### LCM / intersection -/

/-- LCM of two odd naturals is odd. -/
lemma odd_lcm {A B : ℕ} (hA : Odd A) (hB : Odd B) : Odd (A.lcm B) := by
  refine Nat.not_even_iff_odd.mp fun hEven =>
    Nat.prime_two.not_dvd_lcm ?_ ?_ (even_iff_two_dvd.mp hEven)
  · exact fun h => (Nat.not_even_iff_odd.mpr hA) (even_iff_two_dvd.mpr h)
  · exact fun h => (Nat.not_even_iff_odd.mpr hB) (even_iff_two_dvd.mpr h)

/-- If `3 ∤ A` and `3 ∤ B`, then `3 ∤ lcm A B`. -/
lemma three_not_dvd_lcm {A B : ℕ} (hA : ¬ 3 ∣ A) (hB : ¬ 3 ∣ B) :
    ¬ 3 ∣ A.lcm B :=
  Nat.prime_three.not_dvd_lcm hA hB

/-- Joint hire implies lcm hire. -/
theorem dvd_m0_lcm {A B p : ℕ} (hA : A ∣ m0 p) (hB : B ∣ m0 p) :
    A.lcm B ∣ m0 p :=
  Nat.lcm_dvd hA hB

/-- **Coverage meet.** `A` and `B` both divide `m0 p` iff their lcm does. -/
theorem dvd_m0_and_iff_lcm {A B p : ℕ}
    (_hAodd : Odd A) (_hBodd : Odd B) (_hA3 : ¬ 3 ∣ A) (_hB3 : ¬ 3 ∣ B)
    (_hp : p.Prime) (_hp3 : p ≠ 3) :
    A ∣ m0 p ∧ B ∣ m0 p ↔ A.lcm B ∣ m0 p :=
  ⟨fun ⟨hA, hB⟩ => dvd_m0_lcm hA hB,
    fun h => ⟨Nat.dvd_of_lcm_right_dvd h, Nat.dvd_of_lcm_left_dvd h⟩⟩

end Hire
