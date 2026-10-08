import Hire.HeckeFactorization15
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.Induction

namespace HireCharacterReadout

/-- A prime ideal has prime-power absolute norm. -/
theorem eisenstein_prime_absNorm_isPrimePow
    (P : Ideal DoorEisensteinIntegers)
    (hP : Prime P) :
    IsPrimePow (Ideal.absNorm P) := by
  let : P.IsMaximal :=
    (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨q, f, hf, _, hq, hnorm⟩ :=
    Ideal.exists_prime_and_absNorm_eq_pow P
  rw [hnorm]
  exact hq.isPrimePow.pow (ne_of_gt hf)

/-- An ideal whose norm is a coprime product splits into ideals
with the prescribed norms. -/
theorem eisenstein_exists_coprime_norm_decomposition
    (I : Ideal DoorEisensteinIntegers) :
    ∀ a b : ℕ,
      a ≠ 0 → b ≠ 0 → a.Coprime b →
      Ideal.absNorm I = a * b →
      ∃ A B : Ideal DoorEisensteinIntegers,
        I = A * B ∧
        Ideal.absNorm A = a ∧ Ideal.absNorm B = b := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro a b ha hb hab hnorm
    have hzero : a * b = 0 := by
      simpa using hnorm.symm
    exact (mul_ne_zero ha hb hzero).elim
  | h₂ I hunit =>
    intro a b ha hb hab hnorm
    have htop : I = ⊤ := by simpa using hunit
    have hone : a * b = 1 := by
      simpa only [htop, Ideal.absNorm_top] using hnorm.symm
    have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
    have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
    have ha1 : a = 1 := by nlinarith
    have hb1 : b = 1 := by nlinarith
    subst a
    subst b
    refine ⟨1, 1, ?_, ?_, ?_⟩
    · calc
        I = ⊤ := htop
        _ = (1 : Ideal DoorEisensteinIntegers) * 1 := by
          rw [mul_one, Ideal.one_eq_top]
    · exact map_one Ideal.absNorm
    · exact map_one Ideal.absNorm
  | h₃ J P hJ0 hP ih =>
    intro a b ha hb hab hnorm
    have hprimepow :
        IsPrimePow (Ideal.absNorm P) :=
      eisenstein_prime_absNorm_isPrimePow P hP
    have hPnorm0 : Ideal.absNorm P ≠ 0 :=
      hprimepow.ne_zero
    have hdiv : Ideal.absNorm P ∣ a * b := by
      rw [← hnorm, map_mul]
      exact dvd_mul_right _ _
    have hside :
        Ideal.absNorm P ∣ a ∨ Ideal.absNorm P ∣ b :=
      (hab.isPrimePow_dvd_mul hprimepow).mp hdiv
    rw [map_mul] at hnorm
    rcases hside with hPa | hPb
    · obtain ⟨c, hac⟩ := hPa
      have hc0 : c ≠ 0 := by
        intro hc
        apply ha
        rw [hac, hc, mul_zero]
      have hca : c ∣ a := by
        rw [hac]
        exact dvd_mul_left _ _
      have hcb : c.Coprime b :=
        hab.coprime_dvd_left hca
      have hJnorm : Ideal.absNorm J = c * b := by
        apply mul_left_cancel₀ hPnorm0
        simpa only [hac, mul_assoc] using hnorm
      obtain ⟨A, B, hJ, hA, hB⟩ :=
        ih c b hc0 hb hcb hJnorm
      refine ⟨P * A, B, ?_, ?_, hB⟩
      · rw [hJ, mul_assoc]
      · rw [map_mul, hA]
        exact hac.symm
    · obtain ⟨c, hbc⟩ := hPb
      have hc0 : c ≠ 0 := by
        intro hc
        apply hb
        rw [hbc, hc, mul_zero]
      have hcb : c ∣ b := by
        rw [hbc]
        exact dvd_mul_left _ _
      have hac : a.Coprime c :=
        hab.coprime_dvd_right hcb
      have hJnorm : Ideal.absNorm J = a * c := by
        apply mul_left_cancel₀ hPnorm0
        calc
          Ideal.absNorm P * Ideal.absNorm J = a * b :=
            hnorm
          _ = Ideal.absNorm P * (a * c) := by
            rw [hbc]
            ac_rfl
      obtain ⟨A, B, hJ, hA, hB⟩ :=
        ih a c ha hc0 hac hJnorm
      refine ⟨A, P * B, ?_, hA, ?_⟩
      · rw [hJ]
        simp only [mul_left_comm]
      · rw [map_mul, hB]
        exact hbc.symm

/-- Coprime absolute norms force ideals to be relatively prime. -/
theorem eisenstein_isRelPrime_of_coprime_norm
    (A B : Ideal DoorEisensteinIntegers)
    (hab : (Ideal.absNorm A).Coprime (Ideal.absNorm B)) :
    IsRelPrime A B := by
  intro D hDA hDB
  have hdA : Ideal.absNorm D ∣ Ideal.absNorm A :=
    map_dvd Ideal.absNorm hDA
  have hdB : Ideal.absNorm D ∣ Ideal.absNorm B :=
    map_dvd Ideal.absNorm hDB
  have hd1 : Ideal.absNorm D ∣ 1 := by
    rw [← hab.gcd_eq_one]
    exact Nat.dvd_gcd hdA hdB
  have hnorm : Ideal.absNorm D = 1 :=
    Nat.eq_one_of_dvd_one hd1
  exact Ideal.isUnit_iff.mpr
    (Ideal.absNorm_eq_one_iff.mp hnorm)

/-- The decomposition with prescribed coprime norms is unique. -/
theorem eisenstein_coprime_norm_decomposition_unique
    {a b : ℕ} (ha : a ≠ 0) (hab : a.Coprime b)
    (A B A' B' : Ideal DoorEisensteinIntegers)
    (hA : Ideal.absNorm A = a)
    (hB : Ideal.absNorm B = b)
    (hA' : Ideal.absNorm A' = a)
    (hB' : Ideal.absNorm B' = b)
    (hprod : A * B = A' * B') :
    A = A' ∧ B = B' := by
  have hrelAB' : IsRelPrime A B' := by
    apply eisenstein_isRelPrime_of_coprime_norm
    simpa only [hA, hB'] using hab
  have hrelA'B : IsRelPrime A' B := by
    apply eisenstein_isRelPrime_of_coprime_norm
    simpa only [hA', hB] using hab

  have hAA' : A ∣ A' := by
    apply hrelAB'.dvd_of_dvd_mul_right
    rw [← hprod]
    exact dvd_mul_right _ _
  have hA'A : A' ∣ A := by
    apply hrelA'B.dvd_of_dvd_mul_right
    rw [hprod]
    exact dvd_mul_right _ _
  have hAe : A = A' :=
    le_antisymm
      (Ideal.dvd_iff_le.mp hA'A)
      (Ideal.dvd_iff_le.mp hAA')

  have hA0 : A ≠ 0 := by
    intro hz
    have hnorm0 : Ideal.absNorm A = 0 := by
      rw [hz, map_zero]
    exact ha (hA.symm.trans hnorm0)
  have hBe : B = B' := by
    apply mul_left_cancel₀ hA0
    simpa only [← hAe] using hprod
  exact ⟨hAe, hBe⟩

/-- Existence and uniqueness of the coprime norm decomposition. -/
theorem eisenstein_existsUnique_coprime_norm_decomposition
    (I : Ideal DoorEisensteinIntegers)
    {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b)
    (hI : Ideal.absNorm I = a * b) :
    ∃! AB :
      Ideal DoorEisensteinIntegers × Ideal DoorEisensteinIntegers,
      I = AB.1 * AB.2 ∧
        Ideal.absNorm AB.1 = a ∧
        Ideal.absNorm AB.2 = b := by
  obtain ⟨A, B, hprod, hA, hB⟩ :=
    eisenstein_exists_coprime_norm_decomposition
      I a b ha hb hab hI
  refine ⟨(A, B), ⟨hprod, hA, hB⟩, ?_⟩
  intro AB hAB
  have heq :
      AB.1 = A ∧ AB.2 = B :=
    eisenstein_coprime_norm_decomposition_unique
      ha hab AB.1 AB.2 A B
      hAB.2.1 hAB.2.2 hA hB
      (hAB.1.symm.trans hprod)
  exact Prod.ext heq.1 heq.2

/-- Multiplication identifies the two coprime norm fibers
with the fiber of their product. -/
noncomputable def eisenstein_coprime_norm_fiber_equiv
    {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    ({A : Ideal DoorEisensteinIntegers //
        Ideal.absNorm A = a} ×
      {B : Ideal DoorEisensteinIntegers //
        Ideal.absNorm B = b}) ≃
    {I : Ideal DoorEisensteinIntegers //
      Ideal.absNorm I = a * b} := by
  let f :
      ({A : Ideal DoorEisensteinIntegers //
          Ideal.absNorm A = a} ×
        {B : Ideal DoorEisensteinIntegers //
          Ideal.absNorm B = b}) →
      {I : Ideal DoorEisensteinIntegers //
        Ideal.absNorm I = a * b} :=
    fun AB =>
      ⟨AB.1.val * AB.2.val, by
        rw [map_mul, AB.1.property, AB.2.property]⟩
  apply Equiv.ofBijective f
  constructor
  · intro AB CD h
    have hprod :
        AB.1.val * AB.2.val = CD.1.val * CD.2.val :=
      congrArg Subtype.val h
    have heq :=
      eisenstein_coprime_norm_decomposition_unique
        ha hab
        AB.1.val AB.2.val CD.1.val CD.2.val
        AB.1.property AB.2.property
        CD.1.property CD.2.property
        hprod
    exact Prod.ext
      (Subtype.ext heq.1)
      (Subtype.ext heq.2)
  · intro I
    obtain ⟨A, B, hprod, hA, hB⟩ :=
      eisenstein_exists_coprime_norm_decomposition
        I.val a b ha hb hab I.property
    refine ⟨(⟨A, hA⟩, ⟨B, hB⟩), ?_⟩
    apply Subtype.ext
    exact hprod.symm

/-- Ideal counts multiply at coprime positive norms. -/
theorem doorIdealCount15_mul_of_coprime
    {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    doorIdealCount15 (a * b) =
      doorIdealCount15 a * doorIdealCount15 b := by
  have h :=
    (Nat.card_congr
      (eisenstein_coprime_norm_fiber_equiv ha hb hab)).symm
  simpa only [doorIdealCount15, Nat.card_prod] using h

/-- The divisor-sum coefficient multiplies at coprime arguments. -/
theorem doorQuadraticIdealCoeff15_mul_of_coprime
    {a b : ℕ} (hab : a.Coprime b) :
    doorQuadraticIdealCoeff15 (a * b) =
      doorQuadraticIdealCoeff15 a *
        doorQuadraticIdealCoeff15 b := by
  classical
  unfold doorQuadraticIdealCoeff15
  rw [hab.divisors_mul, Finset.sum_map]
  change
    (∑ d ∈ (a.divisors ×ˢ b.divisors).attach,
      Hire.chi3 (d.val.1 * d.val.2)) =
    (∑ d ∈ a.divisors, Hire.chi3 d) *
      (∑ d ∈ b.divisors, Hire.chi3 d)
  rw [Finset.sum_attach
    (a.divisors ×ˢ b.divisors)
    (fun d : ℕ × ℕ => Hire.chi3 (d.1 * d.2))]
  rw [Finset.sum_product]
  simp_rw [doorChi3_mul]
  rw [Finset.sum_mul_sum]

/-- The Eisenstein ideal-count coefficient is the divisor sum of χ₃. -/
theorem doorIdealCount15_eq_divisor_sum
    (n : ℕ) (hn : n ≠ 0) :
    (doorIdealCount15 n : ℤ) =
      doorQuadraticIdealCoeff15 n := by
  refine Nat.recOnPrimeCoprime
    (motive := fun n =>
      n ≠ 0 →
        (doorIdealCount15 n : ℤ) =
          doorQuadraticIdealCoeff15 n)
    ?_ ?_ ?_ n hn
  · intro hzero
    exact (hzero rfl).elim
  · intro p k hp hnonzero
    exact doorIdealCount15_eq_divisor_sum_prime_power hp k
  · intro a b ha hb hab iha ihb hnonzero
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    rw [doorIdealCount15_mul_of_coprime ha0 hb0 hab,
      Nat.cast_mul,
      doorQuadraticIdealCoeff15_mul_of_coprime hab,
      iha ha0, ihb hb0]

/-- Expanded form of the coefficient identity. -/
theorem doorIdealCount15_eq_sum_chi3_divisors
    (n : ℕ) (hn : n ≠ 0) :
    (doorIdealCount15 n : ℤ) =
      ∑ d ∈ n.divisors, Hire.chi3 d := by
  exact doorIdealCount15_eq_divisor_sum n hn

end HireCharacterReadout
