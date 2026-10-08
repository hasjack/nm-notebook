import Hire.HeckeSeries15
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

namespace HireCharacterReadout

/-- The ideal term extended by zero at the zero ideal. -/
noncomputable def doorHeckeAllIdealTerm15
    (s : ℂ) (I : Ideal DoorEisensteinIntegers) : ℂ :=
  LSeries.term
    (fun n => complexCharacter15 (n : ZMod 15))
    s (Ideal.absNorm I)

/-- On nonzero ideals, the extended term is the original term. -/
theorem doorHeckeAllIdealTerm15_eq
    (s : ℂ) (I : DoorNonzeroIntegralIdeal) :
    doorHeckeAllIdealTerm15 s I.val =
      doorHeckeTerm15 s I := by
  unfold doorHeckeAllIdealTerm15 doorHeckeTerm15
  rw [LSeries.term_of_ne_zero
    (ne_of_gt (doorIntegralIdeal_absNorm_pos I))]
  rfl

/-- The extended term has the same summable majorant. -/
theorem norm_doorHeckeAllIdealTerm15_le
    (s : ℂ) (I : Ideal DoorEisensteinIntegers) :
    ‖doorHeckeAllIdealTerm15 s I‖ ≤
      doorIdealNormWeight15 s (Ideal.absNorm I) := by
  unfold doorHeckeAllIdealTerm15
  rw [LSeries.norm_term_eq]
  unfold doorIdealNormWeight15
  by_cases hn : Ideal.absNorm I = 0
  · simp only [hn, ite_true, le_refl]
  · simp only [hn, ite_false, ← Real.rpow_eq_pow]
    exact div_le_div_of_nonneg_right
      (complexCharacter15.norm_le_one (Ideal.absNorm I))
      (Real.rpow_nonneg
        (Nat.cast_nonneg (Ideal.absNorm I)) s.re)

/-- The extension to all integral ideals remains summable. -/
theorem summable_doorHeckeAllIdealTerm15
    {s : ℂ} (hs : 1 < s.re) :
    Summable (doorHeckeAllIdealTerm15 s) := by
  apply summable_norm_iff.mp
  exact
    (summable_doorIdealNormWeight15_all hs).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun I => norm_doorHeckeAllIdealTerm15_le s I)

/-- Adding the zero ideal does not change the series. -/
theorem doorHeckeSeries15_eq_allIdeal_tsum
    (s : ℂ) :
    doorHeckeSeries15 s =
      ∑' I : Ideal DoorEisensteinIntegers,
        doorHeckeAllIdealTerm15 s I := by
  classical
  have hsupport :
      Function.support (doorHeckeAllIdealTerm15 s) ⊆
        {I : Ideal DoorEisensteinIntegers | I ≠ ⊥} := by
    intro I hI
    change I ≠ ⊥
    intro hzero
    subst I
    have hz :
        doorHeckeAllIdealTerm15 s
          (⊥ : Ideal DoorEisensteinIntegers) = 0 := by
      simp [doorHeckeAllIdealTerm15]
    exact hI hz
  calc
    doorHeckeSeries15 s =
        ∑' I : DoorNonzeroIntegralIdeal,
          doorHeckeAllIdealTerm15 s I.val := by
      unfold doorHeckeSeries15
      apply tsum_congr
      intro I
      exact (doorHeckeAllIdealTerm15_eq s I).symm
    _ = _ := tsum_subtype_eq_of_support_subset hsupport

/-- A norm fiber contributes its cardinality times the common term. -/
theorem doorHecke_norm_fiber_sum15
    (s : ℂ) (n : ℕ) :
    (∑' I :
      {I : Ideal DoorEisensteinIntegers //
        Ideal.absNorm I = n},
      doorHeckeAllIdealTerm15 s I.val) =
    (doorIdealCount15 n : ℂ) *
      LSeries.term
        (fun m => complexCharacter15 (m : ZMod 15))
        s n := by
  classical
  let : Finite
      {I : Ideal DoorEisensteinIntegers //
        Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  let : Fintype
      {I : Ideal DoorEisensteinIntegers //
        Ideal.absNorm I = n} :=
    Fintype.ofFinite _
  calc
    _ = ∑' _ :
        {I : Ideal DoorEisensteinIntegers //
          Ideal.absNorm I = n},
        LSeries.term
          (fun m => complexCharacter15 (m : ZMod 15))
          s n := by
      apply tsum_congr
      intro I
      unfold doorHeckeAllIdealTerm15
      rw [I.property]
    _ = _ := by
      unfold doorIdealCount15
      rw [tsum_fintype, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]

/-- Regroup the absolutely convergent ideal series by norm. -/
theorem doorHeckeSeries15_eq_norm_grouped
    {s : ℂ} (hs : 1 < s.re) :
    doorHeckeSeries15 s =
      ∑' n : ℕ,
        (doorIdealCount15 n : ℂ) *
          LSeries.term
            (fun m => complexCharacter15 (m : ZMod 15))
            s n := by
  have h :=
    (summable_doorHeckeAllIdealTerm15 hs).hasSum.tsum_fiberwise
      (fun I : Ideal DoorEisensteinIntegers =>
        Ideal.absNorm I)
  rw [doorHeckeSeries15_eq_allIdeal_tsum]
  calc
    _ = ∑' n : ℕ,
        ∑' I :
          {I : Ideal DoorEisensteinIntegers //
            Ideal.absNorm I = n},
          doorHeckeAllIdealTerm15 s I.val := by
      exact h.tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro n
      exact doorHecke_norm_fiber_sum15 s n

/-- The proposed Eisenstein ideal-count coefficient. -/
def doorQuadraticIdealCoeff15 (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, Hire.chi3 d

/-- The divisor coefficient at 1 is 1. -/
theorem doorQuadraticIdealCoeff15_one :
    doorQuadraticIdealCoeff15 1 = 1 := by
  simp [doorQuadraticIdealCoeff15, Hire.chi3]

/-- The unique integral ideal of norm 1 is the unit ideal. -/
theorem doorIdealCount15_one :
    doorIdealCount15 1 = 1 := by
  simp [doorIdealCount15, Ideal.absNorm_eq_one_iff]

/-- The ideal count and divisor coefficient agree at 1. -/
theorem doorIdealCount15_eq_divisor_sum_one :
    (doorIdealCount15 1 : ℤ) =
      doorQuadraticIdealCoeff15 1 := by
  rw [doorIdealCount15_one,
    doorQuadraticIdealCoeff15_one]
  norm_num

/-- The inert residue class has multiplicative order 2 modulo 3. -/
theorem orderOf_mod_three_of_inert
    {p : ℕ} (hpmod : p % 3 = 2) :
    orderOf (p : ZMod 3) = 2 := by
  have hcast : (p : ZMod 3) = 2 := by
    calc
      _ = ((p % 3 : ℕ) : ZMod 3) := by simp
      _ = 2 := by norm_num [hpmod]
  rw [hcast]
  exact orderOf_eq_prime
    (show (2 : ZMod 3) ^ 2 = 1 by decide)
    (show (2 : ZMod 3) ≠ 1 by decide)

/-- An inert rational prime does not divide the conductor 3. -/
theorem inert_prime_not_dvd_three
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2) :
    ¬ p ∣ 3 := by
  intro hd
  rcases Nat.prime_three.eq_one_or_self_of_dvd p hd with h | h
  · exact hp.ne_one h
  · subst p
    norm_num at hpmod

/-- Prime ideals above an inert rational prime have residue degree 2. -/
theorem eisenstein_inertiaDeg_of_inert
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.inertiaDeg ℤ = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclotomicExtension {3} ℚ DoorEisensteinField := by
    let : NeZero (3 : ℚ) := ⟨by norm_num⟩
    exact CyclotomicField.isCyclotomicExtension 3 ℚ
  calc
    _ = orderOf (p : ZMod 3) :=
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        p DoorEisensteinField P
        (m := 3)
        (inert_prime_not_dvd_three hp hpmod)
    _ = 2 := orderOf_mod_three_of_inert hpmod

/-- Prime ideals above an inert rational prime have norm p². -/
theorem eisenstein_primeIdeal_absNorm_of_inert
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p ^ 2 := by
  calc
    _ = p ^ P.inertiaDeg ℤ :=
      (Ideal.pow_inertiaDeg p P).symm
    _ = p ^ 2 := by
      rw [eisenstein_inertiaDeg_of_inert hp hpmod P]

/-- Powers of an inert prime ideal have even norm exponents. -/
theorem eisenstein_primeIdeal_pow_absNorm_of_inert
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (j : ℕ) :
    Ideal.absNorm (P ^ j) = p ^ (2 * j) := by
  rw [map_pow,
    eisenstein_primeIdeal_absNorm_of_inert hp hpmod P,
    pow_mul]

end HireCharacterReadout
