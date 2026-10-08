import Hire.HeckeSeries15
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Multiplicity

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

/-- Exactly one prime ideal lies above an inert rational prime. -/
theorem eisenstein_ncard_primesOver_of_inert
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2) :
    (Ideal.primesOver
      (Ideal.span {(p : ℤ)})
      DoorEisensteinIntegers).ncard = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclotomicExtension {3} ℚ DoorEisensteinField := by
    let : NeZero (3 : ℚ) := ⟨by norm_num⟩
    exact CyclotomicField.isCyclotomicExtension 3 ℚ
  let : IsGalois ℚ DoorEisensteinField :=
    IsCyclotomicExtension.isGalois
      {3} ℚ DoorEisensteinField

  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (Ideal.span {(p : ℤ)})
      DoorEisensteinIntegers
      (Gal(DoorEisensteinField / ℚ))

  have he :
      (Ideal.span {(p : ℤ)}).ramificationIdxIn
        DoorEisensteinIntegers = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
      p DoorEisensteinField
      (m := 3)
      (inert_prime_not_dvd_three hp hpmod)

  have hf :
      (Ideal.span {(p : ℤ)}).inertiaDegIn
        DoorEisensteinIntegers = 2 := by
    rw [
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
        p DoorEisensteinField
        (m := 3)
        (inert_prime_not_dvd_three hp hpmod)]
    exact orderOf_mod_three_of_inert hpmod

  have hdegree :
      Module.finrank ℚ DoorEisensteinField = 2 := by
    rw [IsCyclotomicExtension.Rat.finrank
      3 DoorEisensteinField]
    exact Nat.totient_prime Nat.prime_three

  rw [he, hf,
    IsGaloisGroup.card_eq_finrank
      (Gal(DoorEisensteinField / ℚ))
      ℚ DoorEisensteinField,
    hdegree] at hfund
  omega

/-- Existence and uniqueness of the prime ideal above an inert prime. -/
theorem eisenstein_existsUnique_primeIdeal_of_inert
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2) :
    ∃! P : Ideal DoorEisensteinIntegers,
      P ∈ Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers := by
  obtain ⟨P, hP⟩ :=
    Set.ncard_eq_one.mp
      (eisenstein_ncard_primesOver_of_inert hp hpmod)
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    exact Set.mem_singleton P
  · intro Q hQ
    rw [hP] at hQ
    exact Set.mem_singleton_iff.mp hQ

/-- If p divides an ideal's norm, the unique prime above p divides it. -/
theorem eisenstein_inert_primeIdeal_dvd_of_dvd_norm
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (I : Ideal DoorEisensteinIntegers)
    (hI : p ∣ Ideal.absNorm I) :
    P ∣ I := by
  obtain ⟨Q, hQmax, hQunder, hQI⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hI
  let : Q.IsMaximal := hQmax
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hQunder.symm⟩
  obtain ⟨R, hR, huniq⟩ :=
    eisenstein_existsUnique_primeIdeal_of_inert hp hpmod
  have hPmem :
      P ∈ Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers :=
    ⟨inferInstance, inferInstance⟩
  have hQmem :
      Q ∈ Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers :=
    ⟨inferInstance, inferInstance⟩
  have hQP : Q = P :=
    (huniq Q hQmem).trans (huniq P hPmem).symm
  simpa only [hQP] using hQI

/-- No integral ideal has norm equal to an inert rational prime. -/
theorem eisenstein_no_ideal_norm_inert_prime
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (I : Ideal DoorEisensteinIntegers) :
    Ideal.absNorm I ≠ p := by
  intro hI
  obtain ⟨P, hP, _⟩ :=
    eisenstein_existsUnique_primeIdeal_of_inert hp hpmod
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hPI : P ∣ I :=
    eisenstein_inert_primeIdeal_dvd_of_dvd_norm
      hp hpmod P I (by rw [hI])
  have hdiv : p ^ 2 ∣ p := by
    have h := map_dvd Ideal.absNorm hPI
    rwa [eisenstein_primeIdeal_absNorm_of_inert
      hp hpmod P, hI] at h
  have hle : p ^ 2 ≤ p :=
    Nat.le_of_dvd hp.pos hdiv
  have hp2 := hp.two_le
  nlinarith

/-- The ideal-count coefficient at an inert prime is zero. -/
theorem doorIdealCount15_inert_prime
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2) :
    doorIdealCount15 p = 0 := by
  let : IsEmpty
      {I : Ideal DoorEisensteinIntegers //
        Ideal.absNorm I = p} :=
    ⟨fun I =>
      eisenstein_no_ideal_norm_inert_prime
        hp hpmod I.val I.property⟩
  unfold doorIdealCount15
  simp

/-- An ideal of norm p² is the unique prime ideal above inert p. -/
theorem eisenstein_ideal_norm_sq_iff_of_inert
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (I : Ideal DoorEisensteinIntegers) :
    Ideal.absNorm I = p ^ 2 ↔ I = P := by
  constructor
  · intro hI
    have hPI : P ∣ I :=
      eisenstein_inert_primeIdeal_dvd_of_dvd_norm
        hp hpmod P I
        (by
          rw [hI, pow_two]
          exact dvd_mul_right p p)
    obtain ⟨J, hIJ⟩ := hPI
    have hnorm :
        p ^ 2 * Ideal.absNorm J = p ^ 2 := by
      calc
        _ = Ideal.absNorm (P * J) := by
          rw [map_mul,
            eisenstein_primeIdeal_absNorm_of_inert
              hp hpmod P]
        _ = p ^ 2 := by rw [← hIJ, hI]
    have hJnorm : Ideal.absNorm J = 1 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hp.ne_zero)
      simpa only [mul_one] using hnorm
    have hJ : J = ⊤ :=
      Ideal.absNorm_eq_one_iff.mp hJnorm
    simpa only [hJ, ← Ideal.one_eq_top, mul_one] using hIJ
  · intro hI
    subst I
    exact eisenstein_primeIdeal_absNorm_of_inert hp hpmod P

/-- Exactly one integral ideal has norm p² for inert p. -/
theorem doorIdealCount15_inert_prime_sq
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2) :
    doorIdealCount15 (p ^ 2) = 1 := by
  obtain ⟨P, hP, _⟩ :=
    eisenstein_existsUnique_primeIdeal_of_inert hp hpmod
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hiff :
      ∀ I : Ideal DoorEisensteinIntegers,
        Ideal.absNorm I = p ^ 2 ↔ I = P :=
    eisenstein_ideal_norm_sq_iff_of_inert hp hpmod P
  simp [doorIdealCount15, hiff]

/-- Every ideal of inert prime-power norm is a power of the unique prime above p. -/
theorem eisenstein_ideal_eq_pow_of_inert_prime_power_norm
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∀ k : ℕ, ∀ I : Ideal DoorEisensteinIntegers,
      Ideal.absNorm I = p ^ k →
        ∃ j : ℕ, I = P ^ j ∧ 2 * j = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro I hI
    by_cases hk : k = 0
    · subst k
      have htop : I = ⊤ :=
        Ideal.absNorm_eq_one_iff.mp (by simpa using hI)
      exact ⟨0, by simpa using htop, rfl⟩
    · have hPI : P ∣ I :=
        eisenstein_inert_primeIdeal_dvd_of_dvd_norm
          hp hpmod P I
          (by
            rw [hI]
            exact dvd_pow_self p hk)
      obtain ⟨J, hIJ⟩ := hPI
      have hJdvd : Ideal.absNorm J ∣ p ^ k := by
        rw [← hI, hIJ, map_mul]
        exact dvd_mul_left _ _
      obtain ⟨l, hlk, hJl⟩ :=
        (Nat.dvd_prime_pow hp).mp hJdvd
      have hpow : p ^ (2 + l) = p ^ k := by
        calc
          _ = p ^ 2 * p ^ l := pow_add p 2 l
          _ = Ideal.absNorm (P * J) := by
            rw [map_mul,
              eisenstein_primeIdeal_absNorm_of_inert
                hp hpmod P,
              hJl]
          _ = p ^ k := by rw [← hIJ, hI]
      have hexp : 2 + l = k :=
        Nat.pow_right_injective hp.two_le hpow
      have hl : l < k := by omega
      obtain ⟨j, hJ, hj⟩ := ih l hl J hJl
      refine ⟨j + 1, ?_, ?_⟩
      · rw [hIJ, hJ, pow_succ']
      · omega

/-- At an even exponent, the ideal of that norm is uniquely P^j. -/
theorem eisenstein_ideal_norm_even_pow_iff_of_inert
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (j : ℕ) (I : Ideal DoorEisensteinIntegers) :
    Ideal.absNorm I = p ^ (2 * j) ↔ I = P ^ j := by
  constructor
  · intro hI
    obtain ⟨l, hIl, hl⟩ :=
      eisenstein_ideal_eq_pow_of_inert_prime_power_norm
        hp hpmod P (2 * j) I hI
    have hlj : l = j := by omega
    simpa only [hlj] using hIl
  · intro hI
    subst I
    exact eisenstein_primeIdeal_pow_absNorm_of_inert
      hp hpmod P j

/-- An inert prime has exactly one ideal at each even norm exponent. -/
theorem doorIdealCount15_inert_even_power
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (j : ℕ) :
    doorIdealCount15 (p ^ (2 * j)) = 1 := by
  obtain ⟨P, hP, _⟩ :=
    eisenstein_existsUnique_primeIdeal_of_inert hp hpmod
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hiff :
      ∀ I : Ideal DoorEisensteinIntegers,
        Ideal.absNorm I = p ^ (2 * j) ↔ I = P ^ j :=
    eisenstein_ideal_norm_even_pow_iff_of_inert
      hp hpmod P j
  simp [doorIdealCount15, hiff]

/-- An inert prime has no ideals at odd norm exponents. -/
theorem doorIdealCount15_inert_odd_power
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (j : ℕ) :
    doorIdealCount15 (p ^ (2 * j + 1)) = 0 := by
  obtain ⟨P, hP, _⟩ :=
    eisenstein_existsUnique_primeIdeal_of_inert hp hpmod
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  let : IsEmpty
      {I : Ideal DoorEisensteinIntegers //
        Ideal.absNorm I = p ^ (2 * j + 1)} :=
    ⟨fun I => by
      obtain ⟨l, _, hl⟩ :=
        eisenstein_ideal_eq_pow_of_inert_prime_power_norm
          hp hpmod P (2 * j + 1) I.val I.property
      omega⟩
  unfold doorIdealCount15
  simp

/-- The complete inert prime-power ideal count. -/
theorem doorIdealCount15_inert_prime_power
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (k : ℕ) :
    doorIdealCount15 (p ^ k) =
      if Even k then 1 else 0 := by
  classical
  by_cases hk : Even k
  · rw [ite_eq_left hk]
    obtain ⟨j, hj⟩ := hk
    have hkj : k = 2 * j := by omega
    rw [hkj]
    exact doorIdealCount15_inert_even_power hp hpmod j
  · rw [ite_eq_right hk]
    have hodd : Odd k := Nat.not_even_iff_odd.mp hk
    obtain ⟨j, hj⟩ := hodd
    have hkj : k = 2 * j + 1 := by omega
    rw [hkj]
    exact doorIdealCount15_inert_odd_power hp hpmod j

/-- Exactly one prime ideal lies above 3. -/
theorem eisenstein_ncard_primesOver_three :
    (Ideal.primesOver
      (Ideal.span {(3 : ℤ)})
      DoorEisensteinIntegers).ncard = 1 := by
  let : IsCyclotomicExtension {3} ℚ DoorEisensteinField := by
    let : NeZero (3 : ℚ) := ⟨by norm_num⟩
    exact CyclotomicField.isCyclotomicExtension 3 ℚ
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime
    3 DoorEisensteinField

/-- The prime ideal above 3 has norm 3. -/
theorem eisenstein_primeIdeal_absNorm_three
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(3 : ℤ)})] :
    Ideal.absNorm P = 3 := by
  let : IsCyclotomicExtension {3} ℚ DoorEisensteinField := by
    let : NeZero (3 : ℚ) := ⟨by norm_num⟩
    exact CyclotomicField.isCyclotomicExtension 3 ℚ
  have hf : P.inertiaDeg ℤ = 1 :=
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime
      3 DoorEisensteinField P
  calc
    _ = 3 ^ P.inertiaDeg ℤ :=
      (Ideal.pow_inertiaDeg 3 P).symm
    _ = 3 := by rw [hf, pow_one]

/-- Uniqueness above p identifies the prime divisor extracted from a norm. -/
theorem eisenstein_unique_primeIdeal_dvd_of_dvd_norm
    {p : ℕ} (hp : p.Prime)
    (hcount :
      (Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers).ncard = 1)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (I : Ideal DoorEisensteinIntegers)
    (hI : p ∣ Ideal.absNorm I) :
    P ∣ I := by
  obtain ⟨Q, hQmax, hQunder, hQI⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hI
  let : Q.IsMaximal := hQmax
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hQunder.symm⟩
  obtain ⟨R, hR⟩ := Set.ncard_eq_one.mp hcount
  have hPmem :
      P ∈ Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers :=
    ⟨inferInstance, inferInstance⟩
  have hQmem :
      Q ∈ Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers :=
    ⟨inferInstance, inferInstance⟩
  rw [hR] at hPmem hQmem
  have hQP : Q = P :=
    (Set.mem_singleton_iff.mp hQmem).trans
      (Set.mem_singleton_iff.mp hPmem).symm
  simpa only [hQP] using hQI

/-- With a unique prime above p of norm p, every ideal of norm p^k is P^k. -/
theorem eisenstein_ideal_eq_pow_of_unique_prime_norm
    {p : ℕ} (hp : p.Prime)
    (hcount :
      (Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers).ncard = 1)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hPnorm : Ideal.absNorm P = p) :
    ∀ k : ℕ, ∀ I : Ideal DoorEisensteinIntegers,
      Ideal.absNorm I = p ^ k → I = P ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro I hI
    by_cases hk : k = 0
    · subst k
      have htop : I = ⊤ :=
        Ideal.absNorm_eq_one_iff.mp (by simpa using hI)
      simpa using htop
    · have hPI : P ∣ I :=
        eisenstein_unique_primeIdeal_dvd_of_dvd_norm
          hp hcount P I
          (by
            rw [hI]
            exact dvd_pow_self p hk)
      obtain ⟨J, hIJ⟩ := hPI
      have hJdvd : Ideal.absNorm J ∣ p ^ k := by
        rw [← hI, hIJ, map_mul]
        exact dvd_mul_left _ _
      obtain ⟨l, _, hJl⟩ :=
        (Nat.dvd_prime_pow hp).mp hJdvd
      have hpow : p ^ (1 + l) = p ^ k := by
        calc
          _ = p * p ^ l := by rw [pow_add, pow_one]
          _ = Ideal.absNorm (P * J) := by
            rw [map_mul, hPnorm, hJl]
          _ = p ^ k := by rw [← hIJ, hI]
      have hexp : 1 + l = k :=
        Nat.pow_right_injective hp.two_le hpow
      have hl : l < k := by omega
      have hJ : J = P ^ l := ih l hl J hJl
      calc
        I = P * P ^ l := by rw [hIJ, hJ]
        _ = P ^ (l + 1) := (pow_succ' P l).symm
        _ = P ^ k := by congr 1; omega

/-- Exactly one integral ideal has norm 3^k, for every k. -/
theorem doorIdealCount15_three_power
    (k : ℕ) :
    doorIdealCount15 (3 ^ k) = 1 := by
  obtain ⟨P, hsingleton⟩ :=
    Set.ncard_eq_one.mp eisenstein_ncard_primesOver_three
  have hPmem :
      P ∈ Ideal.primesOver
        (Ideal.span {(3 : ℤ)})
        DoorEisensteinIntegers := by
    rw [hsingleton]
    exact Set.mem_singleton P
  let : P.IsPrime := hPmem.1
  let : P.LiesOver (Ideal.span {(3 : ℤ)}) := hPmem.2
  have hPnorm : Ideal.absNorm P = 3 :=
    eisenstein_primeIdeal_absNorm_three P
  have hiff :
      ∀ I : Ideal DoorEisensteinIntegers,
        Ideal.absNorm I = 3 ^ k ↔ I = P ^ k := by
    intro I
    constructor
    · exact eisenstein_ideal_eq_pow_of_unique_prime_norm
        Nat.prime_three eisenstein_ncard_primesOver_three
        P hPnorm k I
    · intro hI
      rw [hI, map_pow, hPnorm]
  simp [doorIdealCount15, hiff]

/-- The split residue class has multiplicative order 1 modulo 3. -/
theorem orderOf_mod_three_of_split
    {p : ℕ} (hpmod : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hcast : (p : ZMod 3) = 1 := by
    calc
      _ = ((p % 3 : ℕ) : ZMod 3) := by simp
      _ = 1 := by norm_num [hpmod]
  rw [hcast, orderOf_one]

/-- A split rational prime does not divide 3. -/
theorem split_prime_not_dvd_three
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1) :
    ¬ p ∣ 3 := by
  intro hd
  rcases Nat.prime_three.eq_one_or_self_of_dvd p hd with h | h
  · exact hp.ne_one h
  · subst p
    norm_num at hpmod

/-- A prime ideal above a split rational prime has norm p. -/
theorem eisenstein_primeIdeal_absNorm_of_split
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1)
    (P : Ideal DoorEisensteinIntegers)
    [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclotomicExtension {3} ℚ DoorEisensteinField := by
    let : NeZero (3 : ℚ) := ⟨by norm_num⟩
    exact CyclotomicField.isCyclotomicExtension 3 ℚ
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [
      IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        p DoorEisensteinField P
        (m := 3)
        (split_prime_not_dvd_three hp hpmod)]
    exact orderOf_mod_three_of_split hpmod
  calc
    _ = p ^ P.inertiaDeg ℤ :=
      (Ideal.pow_inertiaDeg p P).symm
    _ = p := by rw [hf, pow_one]

/-- Exactly two prime ideals lie above a split rational prime. -/
theorem eisenstein_ncard_primesOver_of_split
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1) :
    (Ideal.primesOver
      (Ideal.span {(p : ℤ)})
      DoorEisensteinIntegers).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclotomicExtension {3} ℚ DoorEisensteinField := by
    let : NeZero (3 : ℚ) := ⟨by norm_num⟩
    exact CyclotomicField.isCyclotomicExtension 3 ℚ
  let : IsGalois ℚ DoorEisensteinField :=
    IsCyclotomicExtension.isGalois
      {3} ℚ DoorEisensteinField
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (Ideal.span {(p : ℤ)})
      DoorEisensteinIntegers
      (Gal(DoorEisensteinField / ℚ))
  have he :
      (Ideal.span {(p : ℤ)}).ramificationIdxIn
        DoorEisensteinIntegers = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
      p DoorEisensteinField
      (m := 3)
      (split_prime_not_dvd_three hp hpmod)
  have hf :
      (Ideal.span {(p : ℤ)}).inertiaDegIn
        DoorEisensteinIntegers = 1 := by
    rw [
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd
        p DoorEisensteinField
        (m := 3)
        (split_prime_not_dvd_three hp hpmod)]
    exact orderOf_mod_three_of_split hpmod
  have hdegree :
      Module.finrank ℚ DoorEisensteinField = 2 := by
    rw [IsCyclotomicExtension.Rat.finrank
      3 DoorEisensteinField]
    exact Nat.totient_prime Nat.prime_three
  rw [he, hf,
    IsGaloisGroup.card_eq_finrank
      (Gal(DoorEisensteinField / ℚ))
      ℚ DoorEisensteinField,
    hdegree] at hfund
  simpa using hfund

/-- The two distinct prime ideals exhaust the primes above split p. -/
theorem eisenstein_split_prime_pair
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1) :
    ∃ P Q : Ideal DoorEisensteinIntegers,
      P ≠ Q ∧
      Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers = {P, Q} :=
  Set.ncard_eq_two.mp
    (eisenstein_ncard_primesOver_of_split hp hpmod)

/-- A product of powers of the split primes has the expected norm. -/
theorem eisenstein_split_prime_power_product_norm
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1)
    (P Q : Ideal DoorEisensteinIntegers)
    [P.IsPrime] [Q.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (i j : ℕ) :
    Ideal.absNorm (P ^ i * Q ^ j) = p ^ (i + j) := by
  rw [map_mul, map_pow, map_pow,
    eisenstein_primeIdeal_absNorm_of_split hp hpmod P,
    eisenstein_primeIdeal_absNorm_of_split hp hpmod Q,
    pow_add]

/-- Every ideal of split prime-power norm is a product of powers
of the two prime ideals above p. -/
theorem eisenstein_ideal_eq_split_prime_powers
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1)
    (P Q : Ideal DoorEisensteinIntegers)
    (hpair :
      Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers = {P, Q}) :
    ∀ k : ℕ, ∀ I : Ideal DoorEisensteinIntegers,
      Ideal.absNorm I = p ^ k →
        ∃ i j : ℕ,
          I = P ^ i * Q ^ j ∧ i + j = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro I hI
    by_cases hk : k = 0
    · subst k
      have htop : I = ⊤ :=
        Ideal.absNorm_eq_one_iff.mp (by simpa using hI)
      refine ⟨0, 0, ?_, rfl⟩
      simpa using htop
    · have hpI : p ∣ Ideal.absNorm I := by
        rw [hI]
        exact dvd_pow_self p hk
      obtain ⟨R, hRmax, hRunder, hRI⟩ :=
        Ideal.exists_isMaximal_dvd_of_dvd_absNorm'
          hp I hpI
      let : R.IsMaximal := hRmax
      let : R.LiesOver (Ideal.span {(p : ℤ)}) :=
        ⟨hRunder.symm⟩
      have hRmem :
          R ∈ Ideal.primesOver
            (Ideal.span {(p : ℤ)})
            DoorEisensteinIntegers :=
        ⟨inferInstance, inferInstance⟩
      have hRcases : R = P ∨ R = Q := by
        rw [hpair] at hRmem
        simpa only [
          Set.mem_insert_iff,
          Set.mem_singleton_iff] using hRmem
      have hRnorm : Ideal.absNorm R = p :=
        eisenstein_primeIdeal_absNorm_of_split
          hp hpmod R

      obtain ⟨J, hIJ⟩ := hRI
      have hJdvd : Ideal.absNorm J ∣ p ^ k := by
        rw [← hI, hIJ, map_mul]
        exact dvd_mul_left _ _
      obtain ⟨l, _, hJl⟩ :=
        (Nat.dvd_prime_pow hp).mp hJdvd
      have hpow : p ^ (1 + l) = p ^ k := by
        calc
          _ = p * p ^ l := by
            rw [pow_add, pow_one]
          _ = Ideal.absNorm (R * J) := by
            rw [map_mul, hRnorm, hJl]
          _ = p ^ k := by
            rw [← hIJ, hI]
      have hexp : 1 + l = k :=
        Nat.pow_right_injective hp.two_le hpow
      have hl : l < k := by omega

      obtain ⟨i, j, hJ, hij⟩ := ih l hl J hJl
      rcases hRcases with hRP | hRQ
      · refine ⟨i + 1, j, ?_, ?_⟩
        · rw [hIJ, hJ, hRP, pow_succ']
          ac_rfl
        · omega
      · refine ⟨i, j + 1, ?_, ?_⟩
        · rw [hIJ, hJ, hRQ, pow_succ']
          simp only [mul_left_comm]
        · omega

/-- The exponents of the two distinct split prime ideals are unique. -/
theorem eisenstein_split_prime_exponents_unique
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1)
    (P Q : Ideal DoorEisensteinIntegers)
    [P.IsPrime] [Q.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (hne : P ≠ Q)
    {i j r s : ℕ}
    (h : P ^ i * Q ^ j = P ^ r * Q ^ s) :
    i = r ∧ j = s := by
  have hPnorm : Ideal.absNorm P = p :=
    eisenstein_primeIdeal_absNorm_of_split hp hpmod P
  have hQnorm : Ideal.absNorm Q = p :=
    eisenstein_primeIdeal_absNorm_of_split hp hpmod Q
  have hP0 : P ≠ ⊥ := by
    intro hzero
    exact hp.ne_zero
      (hPnorm.symm.trans
        (Ideal.absNorm_eq_zero_iff.mpr hzero))
  have hQ0 : Q ≠ ⊥ := by
    intro hzero
    exact hp.ne_zero
      (hQnorm.symm.trans
        (Ideal.absNorm_eq_zero_iff.mpr hzero))

  have hPrimeP : Prime P :=
    Ideal.prime_of_isPrime hP0 inferInstance
  have hPrimeQ : Prime Q :=
    Ideal.prime_of_isPrime hQ0 inferInstance
  let : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal hP0
  let : Q.IsMaximal :=
    (inferInstance : Q.IsPrime).isMaximal hQ0

  have hPQ : ¬ P ∣ Q := by
    intro hd
    have hle : Q ≤ P := Ideal.dvd_iff_le.mp hd
    have heq : Q = P :=
      (inferInstance : Q.IsMaximal).eq_of_le
        (inferInstance : P.IsPrime).ne_top hle
    exact hne heq.symm
  have hQP : ¬ Q ∣ P := by
    intro hd
    have hle : P ≤ Q := Ideal.dvd_iff_le.mp hd
    have heq : P = Q :=
      (inferInstance : P.IsMaximal).eq_of_le
        (inferInstance : Q.IsPrime).ne_top hle
    exact hne heq

  have hreadP (a b : ℕ) :
      emultiplicity P (P ^ a * Q ^ b) = (a : ℕ∞) := by
    rw [emultiplicity_mul hPrimeP,
      emultiplicity_pow_self_of_prime hPrimeP,
      emultiplicity_pow hPrimeP,
      emultiplicity_eq_zero.mpr hPQ]
    simp
  have hreadQ (a b : ℕ) :
      emultiplicity Q (P ^ a * Q ^ b) = (b : ℕ∞) := by
    rw [emultiplicity_mul hPrimeQ,
      emultiplicity_pow hPrimeQ,
      emultiplicity_eq_zero.mpr hQP,
      emultiplicity_pow_self_of_prime hPrimeQ]
    simp

  have hi := congrArg (emultiplicity P) h
  have hj := congrArg (emultiplicity Q) h
  rw [hreadP, hreadP] at hi
  rw [hreadQ, hreadQ] at hj
  constructor
  · exact_mod_cast hi
  · exact_mod_cast hj

/-- Ideals of split prime-power norm are indexed by the exponent of P. -/
noncomputable def eisenstein_split_norm_fiber_equiv
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1)
    (P Q : Ideal DoorEisensteinIntegers)
    [P.IsPrime] [Q.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (hne : P ≠ Q)
    (hpair :
      Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers = {P, Q})
    (k : ℕ) :
    Fin (k + 1) ≃
      {I : Ideal DoorEisensteinIntegers //
        Ideal.absNorm I = p ^ k} := by
  let f :
      Fin (k + 1) →
        {I : Ideal DoorEisensteinIntegers //
          Ideal.absNorm I = p ^ k} :=
    fun a =>
      ⟨P ^ a.val * Q ^ (k - a.val), by
        rw [eisenstein_split_prime_power_product_norm
          hp hpmod P Q]
        congr 1
        have ha := a.isLt
        omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have heq :
        P ^ a.val * Q ^ (k - a.val) =
          P ^ b.val * Q ^ (k - b.val) :=
      congrArg Subtype.val hab
    have hexponents :=
      eisenstein_split_prime_exponents_unique
        hp hpmod P Q hne heq
    exact Fin.ext hexponents.1
  · intro I
    obtain ⟨i, j, hI, hij⟩ :=
      eisenstein_ideal_eq_split_prime_powers
        hp hpmod P Q hpair k I.val I.property
    have hi : i < k + 1 := by omega
    refine ⟨⟨i, hi⟩, ?_⟩
    apply Subtype.ext
    change P ^ i * Q ^ (k - i) = I.val
    have hsub : k - i = j := by omega
    simpa only [hsub] using hI.symm

/-- A split rational prime has k+1 ideals of norm p^k. -/
theorem doorIdealCount15_split_prime_power
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1)
    (k : ℕ) :
    doorIdealCount15 (p ^ k) = k + 1 := by
  obtain ⟨P, Q, hne, hpair⟩ :=
    eisenstein_split_prime_pair hp hpmod
  have hPmem :
      P ∈ Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers := by
    rw [hpair]
    simp
  have hQmem :
      Q ∈ Ideal.primesOver
        (Ideal.span {(p : ℤ)})
        DoorEisensteinIntegers := by
    rw [hpair]
    simp
  let : P.IsPrime := hPmem.1
  let : Q.IsPrime := hQmem.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPmem.2
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQmem.2
  let e :=
    eisenstein_split_norm_fiber_equiv
      hp hpmod P Q hne hpair k
  calc
    doorIdealCount15 (p ^ k) =
        Nat.card (Fin (k + 1)) :=
      (Nat.card_congr e).symm
    _ = k + 1 := by simp

/-- Multiplicativity of the integer-valued character modulo 3. -/
theorem doorChi3_mul (a b : ℕ) :
    Hire.chi3 (a * b) = Hire.chi3 a * Hire.chi3 b := by
  have ha : a % 3 < 3 := Nat.mod_lt a (by decide)
  have hb : b % 3 < 3 := Nat.mod_lt b (by decide)
  unfold Hire.chi3
  rw [Nat.mul_mod]
  interval_cases h₁ : a % 3 <;>
    interval_cases h₂ : b % 3 <;>
    norm_num

/-- Character values on powers are powers of character values. -/
theorem doorChi3_pow (p k : ℕ) :
    Hire.chi3 (p ^ k) = Hire.chi3 p ^ k := by
  induction k with
  | zero => simp [Hire.chi3]
  | succ k ih =>
    rw [pow_succ, doorChi3_mul, ih, pow_succ]

/-- The divisor coefficient at a prime power is a finite geometric sum. -/
theorem doorQuadraticIdealCoeff15_prime_power
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    doorQuadraticIdealCoeff15 (p ^ k) =
      ∑ j ∈ Finset.range (k + 1), Hire.chi3 p ^ j := by
  unfold doorQuadraticIdealCoeff15
  rw [Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  exact doorChi3_pow p j

/-- A convenient identity for the alternating finite sum. -/
theorem two_mul_sum_neg_one_powers (k : ℕ) :
    2 * (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j) =
      1 + (-1 : ℤ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [ih]

/-- The alternating coefficient is determined by the exponent's parity. -/
theorem sum_neg_one_powers_eq (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j) =
      if Even k then 1 else 0 := by
  have h := two_mul_sum_neg_one_powers k
  by_cases hk : Even k
  · rw [ite_eq_left hk]
    rw [hk.neg_one_pow] at h
    linarith
  · rw [ite_eq_right hk]
    have ho : Odd k := Nat.not_even_iff_odd.mp hk
    rw [ho.neg_one_pow] at h
    linarith

/-- The split divisor coefficient is k+1. -/
theorem doorQuadraticIdealCoeff15_split_prime_power
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 1)
    (k : ℕ) :
    doorQuadraticIdealCoeff15 (p ^ k) = (k + 1 : ℕ) := by
  rw [doorQuadraticIdealCoeff15_prime_power hp]
  simp [Hire.chi3, hpmod]

/-- The inert divisor coefficient alternates between 1 and 0. -/
theorem doorQuadraticIdealCoeff15_inert_prime_power
    {p : ℕ} (hp : p.Prime) (hpmod : p % 3 = 2)
    (k : ℕ) :
    doorQuadraticIdealCoeff15 (p ^ k) =
      if Even k then 1 else 0 := by
  rw [doorQuadraticIdealCoeff15_prime_power hp]
  have hχ : Hire.chi3 p = -1 := by
    simp [Hire.chi3, hpmod]
  rw [hχ]
  exact sum_neg_one_powers_eq k

/-- The ramified divisor coefficient is always 1. -/
theorem doorQuadraticIdealCoeff15_three_power
    (k : ℕ) :
    doorQuadraticIdealCoeff15 (3 ^ k) = 1 := by
  rw [doorQuadraticIdealCoeff15_prime_power Nat.prime_three]
  have hχ : Hire.chi3 3 = 0 := by
    norm_num [Hire.chi3]
  rw [hχ]
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp

/-- Agreement of the ideal count and divisor sum at every prime power. -/
theorem doorIdealCount15_eq_divisor_sum_prime_power
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (doorIdealCount15 (p ^ k) : ℤ) =
      doorQuadraticIdealCoeff15 (p ^ k) := by
  by_cases hp3 : p = 3
  · subst p
    rw [doorIdealCount15_three_power,
      doorQuadraticIdealCoeff15_three_power]
    norm_num
  · have hnotdvd : ¬ 3 ∣ p := by
      intro hd
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h
      · norm_num at h
      · exact hp3 h.symm
    have hmod0 : p % 3 ≠ 0 := by
      intro h
      exact hnotdvd (Nat.dvd_of_mod_eq_zero h)
    have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
    have hcases : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hcases with hsplit | hinert
    · rw [doorIdealCount15_split_prime_power hp hsplit,
        doorQuadraticIdealCoeff15_split_prime_power hp hsplit]
    · rw [doorIdealCount15_inert_prime_power hp hinert,
        doorQuadraticIdealCoeff15_inert_prime_power hp hinert]
      by_cases hk : Even k <;> simp [hk]

end HireCharacterReadout
