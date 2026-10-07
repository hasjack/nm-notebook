import Mathlib
import Hire.Doors

namespace HireEulerDoor

/-- The local quadratic-field Euler factor, evaluated at 1.
    This is one finite factor, not the full Euler product at 1. -/
noncomputable def localEulerAtOne (p χ : ℝ) : ℝ :=
  1 / ((1 - 1 / p) * (1 - χ / p))

/-- The two complementary doors multiply to p² − 1. -/
theorem complementary_door_product
    (p χ : ℝ)
    (hχ : χ = 1 ∨ χ = -1) :
    (p + χ) * (p - χ) = p ^ 2 - 1 := by
  rcases hχ with rfl | rfl <;> ring

/-- The local Euler factor can be written using the discarded door. -/
theorem localEulerAtOne_eq_discarded_door
    (p χ : ℝ)
    (hp : 1 < p)
    (hχ : χ = 1 ∨ χ = -1) :
    localEulerAtOne p χ =
      p ^ 2 / ((p - 1) * (p - χ)) := by
  have hp0 : p ≠ 0 := by linarith
  have hm : p - 1 ≠ 0 := by linarith
  have hplus : p + 1 ≠ 0 := by linarith
  rcases hχ with rfl | rfl
  · unfold localEulerAtOne
    field_simp
  · unfold localEulerAtOne
    field_simp

/-- Equivalently, the kept door appears in the numerator. -/
theorem localEulerAtOne_eq_kept_door
    (p χ : ℝ)
    (hp : 1 < p)
    (hχ : χ = 1 ∨ χ = -1) :
    localEulerAtOne p χ =
      p ^ 2 * (p + χ) /
        ((p - 1) * (p ^ 2 - 1)) := by
  rw [localEulerAtOne_eq_discarded_door p χ hp hχ]
  have hm : p - 1 ≠ 0 := by linarith
  have hplus : p + 1 ≠ 0 := by linarith
  have hquad : p ^ 2 - 1 ≠ 0 := by
    nlinarith
  rcases hχ with rfl | rfl
  · field_simp [hm, hquad]
    ring
  · simp only [sub_neg_eq_add]
    field_simp [hm, hplus, hquad]
    ring

/-- Adding one gives residue zero exactly at residue Q − 1. -/
theorem add_one_mod_eq_zero_iff
    (n Q : ℕ) (hQ : 1 < Q) :
    (n + 1) % Q = 0 ↔ n % Q = Q - 1 := by
  have hone : 1 % Q = 1 :=
    Nat.mod_eq_of_lt hQ
  have hlt : n % Q < Q :=
    Nat.mod_lt n (by omega)
  rw [Nat.add_mod, hone]
  constructor
  · intro h
    by_cases hb : n % Q + 1 < Q
    · rw [Nat.mod_eq_of_lt hb] at h
      omega
    · omega
  · intro h
    have he : n % Q + 1 = Q := by omega
    rw [he, Nat.mod_self]

/-- Adding one gives residue one exactly at residue zero. -/
theorem add_one_mod_eq_one_iff
    (n Q : ℕ) (hQ : 1 < Q) :
    (n + 1) % Q = 1 ↔ n % Q = 0 := by
  have hone : 1 % Q = 1 :=
    Nat.mod_eq_of_lt hQ
  have hlt : n % Q < Q :=
    Nat.mod_lt n (by omega)
  rw [Nat.add_mod, hone]
  constructor
  · intro h
    by_cases hb : n % Q + 1 < Q
    · rw [Nat.mod_eq_of_lt hb] at h
      omega
    · have he : n % Q + 1 = Q := by omega
      rw [he, Nat.mod_self] at h
      omega
  · intro h
    rw [h, zero_add, hone]

/-- For positive p, divisibility of p − 1 means residue one. -/
theorem dvd_sub_one_iff_mod_eq_one
    (p Q : ℕ) (hp : 1 ≤ p) (hQ : 1 < Q) :
    Q ∣ p - 1 ↔ p % Q = 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have he : p - 1 + 1 = p := by omega
  have h :=
    add_one_mod_eq_one_iff (p - 1) Q hQ
  rw [he] at h
  exact h.symm

/-- A divisor of the kept door corresponds to one of two
    owner residue conditions. -/
theorem dvd_m0_iff_owner_residues
    {p Q : ℕ}
    (hp : p.Prime) (h3 : p ≠ 3)
    (hQ : 1 < Q) :
    Q ∣ Hire.m0 p ↔
      (p % 3 = 1 ∧ p % Q = Q - 1) ∨
      (p % 3 = 2 ∧ p % Q = 1) := by
  rcases Hire.prime_ne_three_mod_three_eq_one_or_two
      hp h3 with hmod | hmod
  · rw [Hire.m0_of_mod_one hmod]
    have hdiv :
        Q ∣ p + 1 ↔ p % Q = Q - 1 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact add_one_mod_eq_zero_iff p Q hQ
    simpa [hmod] using hdiv
  · rw [Hire.m0_of_mod_two hmod]
    have hdiv :
        Q ∣ p - 1 ↔ p % Q = 1 :=
      dvd_sub_one_iff_mod_eq_one
        p Q (by have := hp.two_le; omega) hQ
    simpa [hmod] using hdiv

/-- Owners whose kept door is divisible by Q. -/
def doorLevelOwners (T : Finset ℕ) (Q : ℕ) : Finset ℕ :=
  T.filter (fun p => Q ∣ Hire.m0 p)

/-- The same owners, selected by their residue conditions. -/
def residueLevelOwners (T : Finset ℕ) (Q : ℕ) : Finset ℕ :=
  T.filter (fun p =>
    (p % 3 = 1 ∧ p % Q = Q - 1) ∨
    (p % 3 = 2 ∧ p % Q = 1))

/-- The divisibility and residue selections agree exactly. -/
theorem doorLevelOwners_eq_residueLevelOwners
    (T : Finset ℕ) (Q : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hQ : 1 < Q) :
    doorLevelOwners T Q = residueLevelOwners T Q := by
  ext p
  simp only [doorLevelOwners, residueLevelOwners,
    Finset.mem_filter]
  constructor
  · rintro ⟨hpT, hd⟩
    exact ⟨hpT,
      (dvd_m0_iff_owner_residues
        (hP p hpT) (h3 p hpT) hQ).mp hd⟩
  · rintro ⟨hpT, hr⟩
    exact ⟨hpT,
      (dvd_m0_iff_owner_residues
        (hP p hpT) (h3 p hpT) hQ).mpr hr⟩

/-- Consequently, their counts agree. -/
theorem card_doorLevelOwners_eq_residueLevelOwners
    (T : Finset ℕ) (Q : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hQ : 1 < Q) :
    (doorLevelOwners T Q).card =
      (residueLevelOwners T Q).card := by
  rw [doorLevelOwners_eq_residueLevelOwners
    T Q hP h3 hQ]

/-- A prime owner's kept door is positive. -/
theorem m0_pos_of_prime
    {p : ℕ} (hp : p.Prime) :
    0 < Hire.m0 p := by
  have hp2 := hp.two_le
  unfold Hire.m0
  split_ifs <;> omega

/-- The exponent of q in one door equals the number of
    positive prime-power levels dividing that door.

    B must be large enough that the door is below q^B. -/
theorem door_multiplicity_eq_level_count
    {p q B : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hB : Hire.m0 p < q ^ B) :
    (Hire.m0 p).factorization q =
      ((Finset.Ico 1 B).filter
        (fun k => q ^ k ∣ Hire.m0 p)).card := by
  exact Nat.factorization_eq_card_pow_dvd_of_lt
    hq (m0_pos_of_prime hp) hB

/-- Incoming multiplicity at destination q. -/
def incomingMultiplicity (T : Finset ℕ) (q : ℕ) : ℕ :=
  ∑ p ∈ T, (Hire.m0 p).factorization q

/-- Count by owner or by prime-power level: the totals agree. -/
theorem incomingMultiplicity_eq_sum_level_counts
    (T : Finset ℕ) (q B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hq : q.Prime)
    (hB : ∀ p ∈ T, Hire.m0 p < q ^ B) :
    incomingMultiplicity T q =
      ∑ k ∈ Finset.Ico 1 B,
        (doorLevelOwners T (q ^ k)).card := by
  unfold incomingMultiplicity
  calc
    _ = ∑ p ∈ T, ∑ k ∈ Finset.Ico 1 B,
        if q ^ k ∣ Hire.m0 p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hpT
      rw [door_multiplicity_eq_level_count
        (hP p hpT) hq (hB p hpT)]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ k ∈ Finset.Ico 1 B, ∑ p ∈ T,
        if q ^ k ∣ Hire.m0 p then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Ico 1 B,
        (doorLevelOwners T (q ^ k)).card := by
      simp only [doorLevelOwners,
        Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Incoming multiplicity is exactly a sum of owner
    residue-class counts. -/
theorem incomingMultiplicity_eq_sum_residue_counts
    (T : Finset ℕ) (q B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hq : q.Prime)
    (hB : ∀ p ∈ T, Hire.m0 p < q ^ B) :
    incomingMultiplicity T q =
      ∑ k ∈ Finset.Ico 1 B,
        (residueLevelOwners T (q ^ k)).card := by
  rw [incomingMultiplicity_eq_sum_level_counts
    T q B hP hq hB]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hQ : 1 < q ^ k := by
    cases k with
    | zero => omega
    | succ k =>
        rw [pow_succ]
        have hpow : 0 < q ^ k := pow_pos hq.pos k
        have hq2 := hq.two_le
        nlinarith
  exact card_doorLevelOwners_eq_residueLevelOwners
    T (q ^ k) hP h3 hQ

/-- Incoming multiplicity is the exponent of q in the
    product of all selected doors. -/
theorem incomingMultiplicity_eq_product_factorization
    (T : Finset ℕ) (q : ℕ)
    (hP : ∀ p ∈ T, p.Prime) :
    incomingMultiplicity T q =
      (∏ p ∈ T, Hire.m0 p).factorization q := by
  unfold incomingMultiplicity
  symm
  apply Nat.factorization_prod_apply
  intro p hpT
  exact Nat.ne_of_gt (m0_pos_of_prime (hP p hpT))

/-- Adding door logarithms equals taking the logarithm
    of their product. -/
theorem sum_log_m0_eq_log_product
    (T : Finset ℕ)
    (hP : ∀ p ∈ T, p.Prime) :
    (∑ p ∈ T, Real.log (Hire.m0 p : ℝ)) =
      Real.log ((∏ p ∈ T, Hire.m0 p : ℕ) : ℝ) := by
  have hf : ∀ p ∈ T, (Hire.m0 p : ℝ) ≠ 0 := by
    intro p hpT
    exact_mod_cast
      (Nat.ne_of_gt (m0_pos_of_prime (hP p hpT)))
  have hlog := Real.log_prod hf
  simpa only [Nat.cast_prod] using hlog.symm

/-- Weighted Hire factors reconstruct the total door
    logarithm, grouped by destination.

    The support contains exactly the primes occurring
    in the product of the selected doors. -/
theorem sum_log_m0_eq_sum_incoming_log
    (T : Finset ℕ)
    (hP : ∀ p ∈ T, p.Prime) :
    (∑ p ∈ T, Real.log (Hire.m0 p : ℝ)) =
      ∑ q ∈ (∏ p ∈ T, Hire.m0 p).factorization.support,
        (incomingMultiplicity T q : ℝ) *
          Real.log (q : ℝ) := by
  rw [sum_log_m0_eq_log_product T hP,
    Real.log_nat_eq_sum_factorization]
  change
    (∑ q ∈ (∏ p ∈ T, Hire.m0 p).factorization.support,
      ((∏ p ∈ T, Hire.m0 p).factorization q : ℝ) *
        Real.log (q : ℝ)) = _
  apply Finset.sum_congr rfl
  intro q hq
  rw [incomingMultiplicity_eq_product_factorization T q hP]

end HireEulerDoor
