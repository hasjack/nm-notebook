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

/-- Incoming multiplicity retained through level K.
    B is the exclusive upper bound on the levels considered. -/
def truncatedIncomingMultiplicity
    (T : Finset ℕ) (q K B : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Ico 1 B).filter (fun k => k ≤ K),
    (doorLevelOwners T (q ^ k)).card

/-- Incoming multiplicity omitted after level K. -/
def incomingMultiplicityTail
    (T : Finset ℕ) (q K B : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Ico 1 B).filter (fun k => K < k),
    (doorLevelOwners T (q ^ k)).card

/-- Every level is either retained or omitted. -/
theorem sum_level_counts_eq_truncated_add_tail
    (T : Finset ℕ) (q K B : ℕ) :
    (∑ k ∈ Finset.Ico 1 B,
      (doorLevelOwners T (q ^ k)).card) =
      truncatedIncomingMultiplicity T q K B +
        incomingMultiplicityTail T q K B := by
  unfold truncatedIncomingMultiplicity incomingMultiplicityTail
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k ≤ K
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_ge h]

/-- Total incoming multiplicity is exactly the retained
    contribution plus its tail. -/
theorem incomingMultiplicity_eq_truncated_add_tail
    (T : Finset ℕ) (q K B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hq : q.Prime)
    (hB : ∀ p ∈ T, Hire.m0 p < q ^ B) :
    incomingMultiplicity T q =
      truncatedIncomingMultiplicity T q K B +
        incomingMultiplicityTail T q K B := by
  rw [incomingMultiplicity_eq_sum_level_counts
    T q B hP hq hB]
  exact sum_level_counts_eq_truncated_add_tail T q K B

/-- Truncation never exceeds the full multiplicity. -/
theorem truncatedIncomingMultiplicity_le
    (T : Finset ℕ) (q K B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hq : q.Prime)
    (hB : ∀ p ∈ T, Hire.m0 p < q ^ B) :
    truncatedIncomingMultiplicity T q K B ≤
      incomingMultiplicity T q := by
  have h :=
    incomingMultiplicity_eq_truncated_add_tail
      T q K B hP hq hB
  omega

/-- The tail is exactly the error made by truncating. -/
theorem incomingMultiplicityTail_eq_sub
    (T : Finset ℕ) (q K B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hq : q.Prime)
    (hB : ∀ p ∈ T, Hire.m0 p < q ^ B) :
    incomingMultiplicityTail T q K B =
      incomingMultiplicity T q -
        truncatedIncomingMultiplicity T q K B := by
  have h :=
    incomingMultiplicity_eq_truncated_add_tail
      T q K B hP hq hB
  omega

/-- Once every possible level is retained, the tail vanishes. -/
theorem incomingMultiplicityTail_eq_zero
    (T : Finset ℕ) (q K B : ℕ)
    (hKB : B ≤ K + 1) :
    incomingMultiplicityTail T q K B = 0 := by
  unfold incomingMultiplicityTail
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  have hinterval := Finset.mem_Ico.mp hk'.1
  omega

/-- The omitted multiplicity is exactly a sum of
    omitted owner residue-class counts. -/
theorem incomingMultiplicityTail_eq_sum_residue_counts
    (T : Finset ℕ) (q K B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hq : q.Prime) :
    incomingMultiplicityTail T q K B =
      ∑ k ∈ (Finset.Ico 1 B).filter (fun k => K < k),
        (residueLevelOwners T (q ^ k)).card := by
  unfold incomingMultiplicityTail
  apply Finset.sum_congr rfl
  intro k hk
  have hkIco : k ∈ Finset.Ico 1 B :=
    (Finset.mem_filter.mp hk).1
  have hkpos : 1 ≤ k :=
    (Finset.mem_Ico.mp hkIco).1
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

/-- Upper bounds for the omitted residue counts add up
    to an upper bound for the whole tail.

    The function bound may later come from an integer-slot
    estimate or a prime-counting inequality. -/
theorem incomingMultiplicityTail_le_sum_bounds
    (T : Finset ℕ) (q K B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hq : q.Prime)
    (bound : ℕ → ℝ)
    (hbound : ∀ k ∈ Finset.Ico 1 B, K < k →
      ((residueLevelOwners T (q ^ k)).card : ℝ) ≤
        bound k) :
    (incomingMultiplicityTail T q K B : ℝ) ≤
      ∑ k ∈ (Finset.Ico 1 B).filter (fun k => K < k),
        bound k := by
  rw [incomingMultiplicityTail_eq_sum_residue_counts
    T q K B hP h3 hq]
  push_cast
  apply Finset.sum_le_sum
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkIco, hkTail⟩
  exact hbound k hkIco hkTail

/-- A single residue class has at most X / Q + 1
    positions among selected integers at most X. -/
theorem card_filter_mod_eq_le
    (T : Finset ℕ) (X Q r : ℕ)
    (hX : ∀ p ∈ T, p ≤ X) :
    (T.filter (fun p => p % Q = r)).card ≤
      X / Q + 1 := by
  have hinj :
      Set.InjOn (fun p : ℕ => p / Q)
        (T.filter (fun p => p % Q = r)) := by
    intro a ha b hb hab
    change a / Q = b / Q at hab
    have har : a % Q = r :=
      (Finset.mem_filter.mp ha).2
    have hbr : b % Q = r :=
      (Finset.mem_filter.mp hb).2
    calc
      a = a % Q + Q * (a / Q) :=
        (Nat.mod_add_div a Q).symm
      _ = b % Q + Q * (b / Q) := by
        rw [har, hbr, hab]
      _ = b := Nat.mod_add_div b Q
  have hsub :
      (T.filter (fun p => p % Q = r)).image
          (fun p => p / Q) ⊆
        Finset.range (X / Q + 1) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
    have hpX : p ≤ X :=
      hX p (Finset.mem_filter.mp hp).1
    have hdiv : p / Q ≤ X / Q := by
      gcongr
    exact Finset.mem_range.mpr (by omega)
  calc
    _ = ((T.filter (fun p => p % Q = r)).image
        (fun p => p / Q)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (X / Q + 1)).card :=
      Finset.card_le_card hsub
    _ = X / Q + 1 := Finset.card_range _

/-- Discarding the mod-3 restrictions gives an elementary
    upper bound for the owner residue count. -/
theorem card_residueLevelOwners_le_slots
    (T : Finset ℕ) (X Q : ℕ)
    (hX : ∀ p ∈ T, p ≤ X) :
    (residueLevelOwners T Q).card ≤
      2 * (X / Q + 1) := by
  have hsub :
      residueLevelOwners T Q ⊆
        T.filter (fun p => p % Q = Q - 1) ∪
          T.filter (fun p => p % Q = 1) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpT, hr⟩
    rcases hr with hleft | hright
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hpT, hleft.2⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hpT, hright.2⟩))
  calc
    _ ≤ (T.filter (fun p => p % Q = Q - 1) ∪
        T.filter (fun p => p % Q = 1)).card :=
      Finset.card_le_card hsub
    _ ≤ (T.filter (fun p => p % Q = Q - 1)).card +
        (T.filter (fun p => p % Q = 1)).card :=
      Finset.card_union_le _ _
    _ ≤ (X / Q + 1) + (X / Q + 1) :=
      Nat.add_le_add
        (card_filter_mod_eq_le T X Q (Q - 1) hX)
        (card_filter_mod_eq_le T X Q 1 hX)
    _ = 2 * (X / Q + 1) := by omega

/-- The omitted multiplicity is bounded by the available
    integer slots at its omitted prime-power levels. -/
theorem incomingMultiplicityTail_le_slot_sum
    (T : Finset ℕ) (X q K B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hq : q.Prime)
    (hX : ∀ p ∈ T, p ≤ X) :
    (incomingMultiplicityTail T q K B : ℝ) ≤
      ∑ k ∈ (Finset.Ico 1 B).filter (fun k => K < k),
        (2 * (X / q ^ k + 1) : ℕ) := by
    rw [Nat.cast_sum]
    apply incomingMultiplicityTail_le_sum_bounds
      T q K B hP h3 hq
      (fun k => ((2 * (X / q ^ k + 1) : ℕ) : ℝ))
    intro k hk hkTail
    exact_mod_cast
      (card_residueLevelOwners_le_slots T X (q ^ k) hX)

/-- Omitted levels up to the splitting level J. -/
def incomingMultiplicityLowTail
    (T : Finset ℕ) (q K J B : ℕ) : ℕ :=
  ∑ k ∈ ((Finset.Ico 1 B).filter (fun k => K < k)).filter
      (fun k => k ≤ J),
    (doorLevelOwners T (q ^ k)).card

/-- Omitted levels above the splitting level J. -/
def incomingMultiplicityHighTail
    (T : Finset ℕ) (q K J B : ℕ) : ℕ :=
  ∑ k ∈ ((Finset.Ico 1 B).filter (fun k => K < k)).filter
      (fun k => J < k),
    (doorLevelOwners T (q ^ k)).card

/-- Splitting the omitted levels preserves the exact tail. -/
theorem incomingMultiplicityTail_eq_low_add_high
    (T : Finset ℕ) (q K J B : ℕ) :
    incomingMultiplicityTail T q K B =
      incomingMultiplicityLowTail T q K J B +
        incomingMultiplicityHighTail T q K J B := by
  unfold incomingMultiplicityTail
    incomingMultiplicityLowTail incomingMultiplicityHighTail
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k ≤ J
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_ge h]

/-- Use a supplied bound at lower omitted levels and the
    proved integer-slot bound at higher omitted levels. -/
theorem incomingMultiplicityTail_le_mixed_bounds
    (T : Finset ℕ) (X q K J B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hq : q.Prime)
    (hX : ∀ p ∈ T, p ≤ X)
    (lowBound : ℕ → ℝ)
    (hLow : ∀ k ∈ Finset.Ico 1 B,
      K < k → k ≤ J →
        ((residueLevelOwners T (q ^ k)).card : ℝ) ≤
          lowBound k) :
    (incomingMultiplicityTail T q K B : ℝ) ≤
      ∑ k ∈ (Finset.Ico 1 B).filter (fun k => K < k),
        if k ≤ J then lowBound k
        else ((2 * (X / q ^ k + 1) : ℕ) : ℝ) := by
  apply incomingMultiplicityTail_le_sum_bounds
    T q K B hP h3 hq
    (fun k =>
      if k ≤ J then lowBound k
      else ((2 * (X / q ^ k + 1) : ℕ) : ℝ))
  intro k hk hkTail
  by_cases hkLow : k ≤ J
  · simp only [hkLow, ite_true]
    exact hLow k hk hkTail hkLow
  · simp only [hkLow, ite_false]
    exact_mod_cast
      (card_residueLevelOwners_le_slots T X (q ^ k) hX)

/-- A finite geometric sum is bounded by the infinite
    geometric-series value. -/
theorem finite_geometric_sum_le
    (r : ℝ) (n : ℕ)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑ i ∈ Finset.range n, r ^ i) ≤
      1 / (1 - r) := by
  have hidentity : ∀ m : ℕ,
      (1 - r) * (∑ i ∈ Finset.range m, r ^ i) =
        1 - r ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, pow_succ]
        calc
          (1 - r) *
              ((∑ i ∈ Finset.range m, r ^ i) + r ^ m) =
            (1 - r) *
              (∑ i ∈ Finset.range m, r ^ i) +
                (1 - r) * r ^ m := by ring
          _ = 1 - r ^ m + (1 - r) * r ^ m := by
            rw [ih]
          _ = 1 - r ^ m * r := by ring
  have hden : 0 < 1 - r := by linarith
  have hpow : 0 ≤ r ^ n := pow_nonneg hr n
  have hid := hidentity n
  apply (le_div_iff₀ hden).mpr
  nlinarith

/-- Geometrically shrinking slot estimates have a bound
    independent of the number of terms, apart from the
    additive rounding allowance. -/
theorem geometric_slot_sum_le
    (X r : ℝ) (a n : ℕ)
    (hX : 0 ≤ X)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑ i ∈ Finset.range n,
      2 * (X * r ^ (a + i) + 1)) ≤
        2 * X * r ^ a / (1 - r) +
          2 * (n : ℝ) := by
  have hsum :
      (∑ i ∈ Finset.range n,
        2 * (X * r ^ (a + i) + 1)) =
      (2 * X * r ^ a) *
        (∑ i ∈ Finset.range n, r ^ i) +
          2 * (n : ℝ) := by
    calc
      _ = ∑ i ∈ Finset.range n,
          ((2 * X * r ^ a) * r ^ i + 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_add]
        ring
      _ = (2 * X * r ^ a) *
          (∑ i ∈ Finset.range n, r ^ i) +
            2 * (n : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        ring
  have hgeom := finite_geometric_sum_le r n hr hr1
  have hcoef : 0 ≤ 2 * X * r ^ a :=
    mul_nonneg (mul_nonneg (by norm_num) hX)
      (pow_nonneg hr a)
  calc
    _ = (2 * X * r ^ a) *
        (∑ i ∈ Finset.range n, r ^ i) +
          2 * (n : ℝ) := hsum
    _ ≤ (2 * X * r ^ a) * (1 / (1 - r)) +
        2 * (n : ℝ) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hgeom hcoef
      linarith
    _ = 2 * X * r ^ a / (1 - r) +
        2 * (n : ℝ) := by ring

/-- Integer-slot counts over an interval of levels satisfy
    the geometric bound. -/
theorem slot_sum_Ico_le_geometric
    (X q a B : ℕ)
    (hq : 1 < q) :
    (∑ k ∈ Finset.Ico a B,
      ((2 * (X / q ^ k + 1) : ℕ) : ℝ)) ≤
        2 * (X : ℝ) * (1 / (q : ℝ)) ^ a /
          (1 - 1 / (q : ℝ)) +
            2 * ((B - a : ℕ) : ℝ) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hr : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  have hr1 : (1 : ℝ) / q < 1 := by
    apply (div_lt_iff₀ hqpos).mpr
    simpa using hqR
  calc
    _ ≤ ∑ k ∈ Finset.Ico a B,
        2 * ((X : ℝ) * (1 / (q : ℝ)) ^ k + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hdiv :
          ((X / q ^ k : ℕ) : ℝ) ≤
            (X : ℝ) * (1 / (q : ℝ)) ^ k := by
        simpa only [Nat.cast_pow, div_eq_mul_inv,
          one_div, one_mul, inv_pow] using
          (Nat.cast_div_le (m := X) (n := q ^ k) :
            ((X / q ^ k : ℕ) : ℝ) ≤
              (X : ℝ) / ((q ^ k : ℕ) : ℝ))
      push_cast
      linarith
    _ = ∑ i ∈ Finset.range (B - a),
        2 * ((X : ℝ) *
          (1 / (q : ℝ)) ^ (a + i) + 1) :=
      Finset.sum_Ico_eq_sum_range _ a B
    _ ≤ _ :=
      geometric_slot_sum_le
        (X : ℝ) (1 / (q : ℝ)) a (B - a)
        (by positivity) hr hr1

/-- The actual high tail is bounded by a geometric term
    plus the rounding allowance for its remaining levels. -/
theorem incomingMultiplicityHighTail_le_geometric
    (T : Finset ℕ) (X q K J B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hq : q.Prime)
    (hX : ∀ p ∈ T, p ≤ X)
    (hKJ : K ≤ J) :
    (incomingMultiplicityHighTail T q K J B : ℝ) ≤
      2 * (X : ℝ) * (1 / (q : ℝ)) ^ (J + 1) /
        (1 - 1 / (q : ℝ)) +
          2 * ((B - (J + 1) : ℕ) : ℝ) := by
  have heq :
      incomingMultiplicityHighTail T q K J B =
        incomingMultiplicityTail T q J B := by
    unfold incomingMultiplicityHighTail incomingMultiplicityTail
    have hsets :
        ((Finset.Ico 1 B).filter (fun k => K < k)).filter
            (fun k => J < k) =
          (Finset.Ico 1 B).filter (fun k => J < k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [hsets]
  have hlevels :
      (Finset.Ico 1 B).filter (fun k => J < k) =
        Finset.Ico (J + 1) B := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  calc
    _ = (incomingMultiplicityTail T q J B : ℝ) := by
      rw [heq]
    _ ≤ ∑ k ∈ (Finset.Ico 1 B).filter
          (fun k => J < k),
        ((2 * (X / q ^ k + 1) : ℕ) : ℝ) := by
      simpa only [Nat.cast_sum] using
        (incomingMultiplicityTail_le_slot_sum
          T X q J B hP h3 hq hX)
    _ = ∑ k ∈ Finset.Ico (J + 1) B,
        ((2 * (X / q ^ k + 1) : ℕ) : ℝ) := by
      rw [hlevels]
    _ ≤ _ :=
      slot_sum_Ico_le_geometric
        X q (J + 1) B
        (by have := hq.two_le; omega)

/-- A weighted geometric sum over an interval is bounded
    by the full geometric tail beginning at its first level. -/
theorem weighted_geometric_Ico_le
    (C r : ℝ) (a b : ℕ)
    (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑ k ∈ Finset.Ico a b, C * r ^ k) ≤
      C * r ^ a / (1 - r) := by
  have hcoef : 0 ≤ C * r ^ a :=
    mul_nonneg hC (pow_nonneg hr a)
  have hgeom := finite_geometric_sum_le r (b - a) hr hr1
  calc
    _ = ∑ i ∈ Finset.range (b - a),
        C * r ^ (a + i) :=
      Finset.sum_Ico_eq_sum_range _ a b
    _ = ∑ i ∈ Finset.range (b - a),
        (C * r ^ a) * r ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_add]
      ring
    _ = (C * r ^ a) *
        (∑ i ∈ Finset.range (b - a), r ^ i) := by
      rw [Finset.mul_sum]
    _ ≤ (C * r ^ a) * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left hgeom hcoef
    _ = C * r ^ a / (1 - r) := by ring

/-- A geometric per-level residue-count estimate bounds
    the lower omitted multiplicity.

    hLow is the explicit analytic input. -/
theorem incomingMultiplicityLowTail_le_geometric
    (T : Finset ℕ) (q K J B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hq : q.Prime)
    (C r : ℝ)
    (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hLow : ∀ k ∈ Finset.Ico 1 B,
      K < k → k ≤ J →
        ((residueLevelOwners T (q ^ k)).card : ℝ) ≤
          C * r ^ k) :
    (incomingMultiplicityLowTail T q K J B : ℝ) ≤
      C * r ^ (K + 1) / (1 - r) := by
  have hsub :
      ((Finset.Ico 1 B).filter (fun k => K < k)).filter
          (fun k => k ≤ J) ⊆
        Finset.Ico (K + 1) (J + 1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
    omega
  unfold incomingMultiplicityLowTail
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ k ∈
        ((Finset.Ico 1 B).filter (fun k => K < k)).filter
          (fun k => k ≤ J),
        C * r ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkTail, hkJ⟩
      rcases Finset.mem_filter.mp hkTail with ⟨hkIco, hkK⟩
      have hkpos : 1 ≤ k :=
        (Finset.mem_Ico.mp hkIco).1
      have hQ : 1 < q ^ k := by
        cases k with
        | zero => omega
        | succ k =>
            rw [pow_succ]
            have hpow : 0 < q ^ k := pow_pos hq.pos k
            have hq2 := hq.two_le
            nlinarith
      rw [card_doorLevelOwners_eq_residueLevelOwners
        T (q ^ k) hP h3 hQ]
      exact hLow k hkIco hkK hkJ
    _ ≤ ∑ k ∈ Finset.Ico (K + 1) (J + 1),
        C * r ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k hk hkNot
      exact mul_nonneg hC (pow_nonneg hr k)
    _ ≤ C * r ^ (K + 1) / (1 - r) :=
      weighted_geometric_Ico_le
        C r (K + 1) (J + 1) hC hr hr1

/-- The full tail is bounded by a supplied lower-level
    estimate plus the proved high-level slot estimate. -/
theorem incomingMultiplicityTail_le_combined
    (T : Finset ℕ) (X q K J B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hq : q.Prime)
    (hX : ∀ p ∈ T, p ≤ X)
    (hKJ : K ≤ J)
    (C : ℝ) (hC : 0 ≤ C)
    (hLow : ∀ k ∈ Finset.Ico 1 B,
      K < k → k ≤ J →
        ((residueLevelOwners T (q ^ k)).card : ℝ) ≤
          C * (1 / (q : ℝ)) ^ k) :
    (incomingMultiplicityTail T q K B : ℝ) ≤
      C * (1 / (q : ℝ)) ^ (K + 1) /
        (1 - 1 / (q : ℝ)) +
      (2 * (X : ℝ) * (1 / (q : ℝ)) ^ (J + 1) /
        (1 - 1 / (q : ℝ)) +
          2 * ((B - (J + 1) : ℕ) : ℝ)) := by
  have hqR : (1 : ℝ) < q := by
    exact_mod_cast hq.one_lt
  have hqpos : (0 : ℝ) < q := by linarith
  have hr : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  have hr1 : (1 : ℝ) / q < 1 := by
    apply (div_lt_iff₀ hqpos).mpr
    simpa using hqR
  have hlow :=
    incomingMultiplicityLowTail_le_geometric
      T q K J B hP h3 hq
      C (1 / (q : ℝ)) hC hr hr1 hLow
  have hhigh :=
    incomingMultiplicityHighTail_le_geometric
      T X q K J B hP h3 hq hX hKJ
  have hsplit :
      (incomingMultiplicityTail T q K B : ℝ) =
        (incomingMultiplicityLowTail T q K J B : ℝ) +
          (incomingMultiplicityHighTail T q K J B : ℝ) := by
    exact_mod_cast
      (incomingMultiplicityTail_eq_low_add_high T q K J B)
  rw [hsplit]
  exact add_le_add hlow hhigh

/-- When B covers every possible level, the combined
    tail bound controls the exact truncation error. -/
theorem incomingMultiplicity_truncation_error_le
    (T : Finset ℕ) (X q K J B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3)
    (hq : q.Prime)
    (hX : ∀ p ∈ T, p ≤ X)
    (hKJ : K ≤ J)
    (hB : ∀ p ∈ T, Hire.m0 p < q ^ B)
    (C : ℝ) (hC : 0 ≤ C)
    (hLow : ∀ k ∈ Finset.Ico 1 B,
      K < k → k ≤ J →
        ((residueLevelOwners T (q ^ k)).card : ℝ) ≤
          C * (1 / (q : ℝ)) ^ k) :
    ((incomingMultiplicity T q -
        truncatedIncomingMultiplicity T q K B : ℕ) : ℝ) ≤
      C * (1 / (q : ℝ)) ^ (K + 1) /
        (1 - 1 / (q : ℝ)) +
      (2 * (X : ℝ) * (1 / (q : ℝ)) ^ (J + 1) /
        (1 - 1 / (q : ℝ)) +
          2 * ((B - (J + 1) : ℕ) : ℝ)) := by
  rw [← incomingMultiplicityTail_eq_sub T q K B hP hq hB]
  exact incomingMultiplicityTail_le_combined
    T X q K J B hP h3 hq hX hKJ C hC hLow

/-- Two reduced residue conditions combine into one
    reduced class modulo the product of coprime moduli. -/
theorem exists_reduced_crt_class
    (m n a b : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : Nat.Coprime m n)
    (ha : a < m) (hb : b < n)
    (haCop : Nat.Coprime a m)
    (hbCop : Nat.Coprime b n) :
    ∃ r : ℕ,
      r < m * n ∧
      Nat.Coprime r (m * n) ∧
      ∀ p : ℕ,
        (p % m = a ∧ p % n = b) ↔
          p % (m * n) = r := by
  let c := Nat.chineseRemainder hcop a b
  have hr : (c : ℕ) < m * n :=
    Nat.chineseRemainder_lt_mul hcop a b hm hn
  have hrm : (c : ℕ) % m = a := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha]
      using c.property.1
  have hrn : (c : ℕ) % n = b := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb]
      using c.property.2
  have hcm : Nat.Coprime (c : ℕ) m := by
    change Nat.gcd (c : ℕ) m = 1
    rw [c.property.1.gcd_eq]
    exact haCop
  have hcn : Nat.Coprime (c : ℕ) n := by
    change Nat.gcd (c : ℕ) n = 1
    rw [c.property.2.gcd_eq]
    exact hbCop
  refine ⟨(c : ℕ), hr, hcm.mul_right hcn, ?_⟩
  intro p
  simpa only [Nat.ModEq, hrm, hrn,
    Nat.mod_eq_of_lt hr] using
    (Nat.modEq_and_modEq_iff_modEq_mul
      (a := p) (b := (c : ℕ)) hcop)

/-- The owner conditions select two distinct reduced
    residue classes modulo 3Q. -/
theorem exists_owner_reduced_classes
    (Q : ℕ)
    (hQ : 1 < Q)
    (hcop : Nat.Coprime 3 Q) :
    ∃ rPlus rMinus : ℕ,
      rPlus < 3 * Q ∧
      rMinus < 3 * Q ∧
      Nat.Coprime rPlus (3 * Q) ∧
      Nat.Coprime rMinus (3 * Q) ∧
      rPlus ≠ rMinus ∧
      ∀ p : ℕ,
        ((p % 3 = 1 ∧ p % Q = Q - 1) ∨
          (p % 3 = 2 ∧ p % Q = 1)) ↔
        (p % (3 * Q) = rPlus ∨
          p % (3 * Q) = rMinus) := by
  have hQ0 : Q ≠ 0 := by omega
  have hpred : Nat.Coprime (Q - 1) Q := by
    apply (Nat.coprime_self_sub_left
      (m := 1) (n := Q) (by omega)).mpr
    simp
  obtain ⟨rPlus, hrPlus, hcPlus, hsPlus⟩ :=
    exists_reduced_crt_class
      3 Q 1 (Q - 1)
      (by norm_num) hQ0 hcop
      (by norm_num) (by omega)
      (by norm_num) hpred
  obtain ⟨rMinus, hrMinus, hcMinus, hsMinus⟩ :=
    exists_reduced_crt_class
      3 Q 2 1
      (by norm_num) hQ0 hcop
      (by norm_num) hQ
      (by norm_num) (by simp)
  have hPlusRead : rPlus % 3 = 1 :=
    ((hsPlus rPlus).mpr
      (Nat.mod_eq_of_lt hrPlus)).1
  have hMinusRead : rMinus % 3 = 2 :=
    ((hsMinus rMinus).mpr
      (Nat.mod_eq_of_lt hrMinus)).1
  have hne : rPlus ≠ rMinus := by
    intro h
    rw [h] at hPlusRead
    omega
  refine ⟨rPlus, rMinus, hrPlus, hrMinus,
    hcPlus, hcMinus, hne, ?_⟩
  intro p
  rw [hsPlus p, hsMinus p]

/-- A prime different from 3 has every power coprime to 3. -/
theorem three_coprime_prime_pow
    {q : ℕ} (hq : q.Prime) (h3 : q ≠ 3)
    (k : ℕ) :
    Nat.Coprime 3 (q ^ k) := by
  have hcop : Nat.Coprime 3 q :=
    (Nat.coprime_primes Nat.prime_three hq).mpr
      (Ne.symm h3)
  exact hcop.pow_right k

/-- Every positive power of a prime is greater than one. -/
theorem one_lt_prime_pow_level
    {q k : ℕ} (hq : q.Prime) (hk : 0 < k) :
    1 < q ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      rw [pow_succ]
      have hpow : 0 < q ^ k := pow_pos hq.pos k
      have hq2 := hq.two_le
      nlinarith

/-- Every positive prime-power level, away from 3,
    selects two distinct reduced owner classes. -/
theorem exists_owner_reduced_classes_prime_pow
    {q : ℕ}
    (hq : q.Prime) (h3 : q ≠ 3)
    (k : ℕ) (hk : 0 < k) :
    ∃ rPlus rMinus : ℕ,
      rPlus < 3 * q ^ k ∧
      rMinus < 3 * q ^ k ∧
      Nat.Coprime rPlus (3 * q ^ k) ∧
      Nat.Coprime rMinus (3 * q ^ k) ∧
      rPlus ≠ rMinus ∧
      ∀ p : ℕ,
        ((p % 3 = 1 ∧ p % (q ^ k) = q ^ k - 1) ∨
          (p % 3 = 2 ∧ p % (q ^ k) = 1)) ↔
        (p % (3 * q ^ k) = rPlus ∨
          p % (3 * q ^ k) = rMinus) := by
  exact exists_owner_reduced_classes
    (q ^ k)
    (one_lt_prime_pow_level hq hk)
    (three_coprime_prime_pow hq h3 k)

/-- Selected integers in one residue class. -/
def residueClassOwners
    (T : Finset ℕ) (M r : ℕ) : Finset ℕ :=
  T.filter (fun p => p % M = r)

/-- Number of primes at most X in one residue class.
    For a canonical residue r < M, this is π(X; M, r). -/
def primeResidueCount (X M r : ℕ) : ℕ :=
  (residueClassOwners (Nat.primesLE X) M r).card

/-- Selected prime owners are bounded by the full
    prime count in their residue class. -/
theorem card_residueClassOwners_le_primeResidueCount
    (T : Finset ℕ) (X M r : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hX : ∀ p ∈ T, p ≤ X) :
    (residueClassOwners T M r).card ≤
      primeResidueCount X M r := by
  unfold primeResidueCount
  apply Finset.card_le_card
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpT, hmod⟩
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_primesLE.mpr
    ⟨hX p hpT, hP p hpT⟩, hmod⟩

/-- Two distinct CRT classes partition the owner
    residue selection, so their counts add exactly. -/
theorem card_residueLevelOwners_eq_two_classes
    (T : Finset ℕ) (Q rPlus rMinus : ℕ)
    (hne : rPlus ≠ rMinus)
    (hspec : ∀ p : ℕ,
      ((p % 3 = 1 ∧ p % Q = Q - 1) ∨
        (p % 3 = 2 ∧ p % Q = 1)) ↔
      (p % (3 * Q) = rPlus ∨
        p % (3 * Q) = rMinus)) :
    (residueLevelOwners T Q).card =
      (residueClassOwners T (3 * Q) rPlus).card +
        (residueClassOwners T (3 * Q) rMinus).card := by
  have hsets :
      residueLevelOwners T Q =
        residueClassOwners T (3 * Q) rPlus ∪
          residueClassOwners T (3 * Q) rMinus := by
    ext p
    simp only [residueLevelOwners, residueClassOwners,
      Finset.mem_filter, Finset.mem_union]
    rw [hspec p]
    tauto
  have hdis :
      Disjoint (residueClassOwners T (3 * Q) rPlus)
        (residueClassOwners T (3 * Q) rMinus) := by
    apply Finset.disjoint_left.mpr
    intro p hpPlus hpMinus
    have hPlus : p % (3 * Q) = rPlus :=
      (Finset.mem_filter.mp hpPlus).2
    have hMinus : p % (3 * Q) = rMinus :=
      (Finset.mem_filter.mp hpMinus).2
    exact hne (hPlus.symm.trans hMinus)
  rw [hsets]
  exact Finset.card_union_of_disjoint hdis

/-- A Hire prime-power level is bounded by prime counts
    in two distinct reduced classes modulo 3q^k. -/
theorem doorLevel_count_le_two_primeResidueCounts
    (T : Finset ℕ) (X q k : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hOwner3 : ∀ p ∈ T, p ≠ 3)
    (hX : ∀ p ∈ T, p ≤ X)
    (hq : q.Prime) (hq3 : q ≠ 3)
    (hk : 0 < k) :
    ∃ rPlus rMinus : ℕ,
      rPlus < 3 * q ^ k ∧
      rMinus < 3 * q ^ k ∧
      Nat.Coprime rPlus (3 * q ^ k) ∧
      Nat.Coprime rMinus (3 * q ^ k) ∧
      rPlus ≠ rMinus ∧
      (doorLevelOwners T (q ^ k)).card ≤
        primeResidueCount X (3 * q ^ k) rPlus +
          primeResidueCount X (3 * q ^ k) rMinus := by
  obtain ⟨rPlus, rMinus, hrPlus, hrMinus,
      hcPlus, hcMinus, hne, hspec⟩ :=
    exists_owner_reduced_classes_prime_pow hq hq3 k hk
  refine ⟨rPlus, rMinus, hrPlus, hrMinus,
    hcPlus, hcMinus, hne, ?_⟩
  calc
    _ = (residueLevelOwners T (q ^ k)).card :=
      card_doorLevelOwners_eq_residueLevelOwners
        T (q ^ k) hP hOwner3
        (one_lt_prime_pow_level hq hk)
    _ = (residueClassOwners T (3 * q ^ k) rPlus).card +
        (residueClassOwners T (3 * q ^ k) rMinus).card :=
      card_residueLevelOwners_eq_two_classes
        T (q ^ k) rPlus rMinus hne hspec
    _ ≤ primeResidueCount X (3 * q ^ k) rPlus +
        primeResidueCount X (3 * q ^ k) rMinus :=
      Nat.add_le_add
        (card_residueClassOwners_le_primeResidueCount
          T X (3 * q ^ k) rPlus hP hX)
        (card_residueClassOwners_le_primeResidueCount
          T X (3 * q ^ k) rMinus hP hX)

/-- The CRT modulus has twice the prime-power totient. -/
theorem totient_owner_modulus
    {q : ℕ} (hq : q.Prime) (h3 : q ≠ 3)
    (k : ℕ) (hk : 0 < k) :
    Nat.totient (3 * q ^ k) =
      2 * (q ^ (k - 1) * (q - 1)) := by
  rw [Nat.totient_mul
    (three_coprime_prime_pow hq h3 k)]
  rw [Nat.totient_prime Nat.prime_three,
    Nat.totient_prime_pow hq hk]

/-- The coefficient for two reduced owner classes is
    exactly the reciprocal prime-power totient. -/
theorem owner_level_density_coefficient
    {q : ℕ} (hq : q.Prime) (h3 : q ≠ 3)
    (k : ℕ) (hk : 0 < k) :
    (2 : ℝ) / (Nat.totient (3 * q ^ k) : ℝ) =
      1 / ((q ^ (k - 1) * (q - 1) : ℕ) : ℝ) := by
  have hpred : 0 < q - 1 := by
    have := hq.two_le
    omega
  have hdenNat :
      0 < q ^ (k - 1) * (q - 1) :=
    Nat.mul_pos (pow_pos hq.pos _) hpred
  have hden :
      ((q ^ (k - 1) * (q - 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdenNat)
  rw [totient_owner_modulus hq h3 k hk]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hden' :
      (q ^ (k - 1) : ℝ) * ((q - 1 : ℕ) : ℝ) ≠ 0 := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using hden
  field_simp

/-- A prime-counting estimate for reduced classes transfers
    to the corresponding Hire prime-power level.

    hAP is the explicit analytic input. -/
theorem doorLevel_count_le_of_prime_class_bound
    (T : Finset ℕ) (X q k : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hOwner3 : ∀ p ∈ T, p ≠ 3)
    (hX : ∀ p ∈ T, p ≤ X)
    (hq : q.Prime) (hq3 : q ≠ 3)
    (hk : 0 < k)
    (A : ℝ)
    (hAP : ∀ r : ℕ,
      r < 3 * q ^ k →
      Nat.Coprime r (3 * q ^ k) →
        (primeResidueCount X (3 * q ^ k) r : ℝ) ≤
          A / (Nat.totient (3 * q ^ k) : ℝ)) :
    ((doorLevelOwners T (q ^ k)).card : ℝ) ≤
      A / ((q ^ (k - 1) * (q - 1) : ℕ) : ℝ) := by
  obtain ⟨rPlus, rMinus, hrPlus, hrMinus,
      hcPlus, hcMinus, hne, hcount⟩ :=
    doorLevel_count_le_two_primeResidueCounts
      T X q k hP hOwner3 hX hq hq3 hk
  have hcountR :
      ((doorLevelOwners T (q ^ k)).card : ℝ) ≤
        (primeResidueCount X (3 * q ^ k) rPlus : ℝ) +
          (primeResidueCount X (3 * q ^ k) rMinus : ℝ) := by
    exact_mod_cast hcount
  have hPlus := hAP rPlus hrPlus hcPlus
  have hMinus := hAP rMinus hrMinus hcMinus
  calc
    _ ≤ (primeResidueCount X (3 * q ^ k) rPlus : ℝ) +
        (primeResidueCount X (3 * q ^ k) rMinus : ℝ) :=
      hcountR
    _ ≤ A / (Nat.totient (3 * q ^ k) : ℝ) +
        A / (Nat.totient (3 * q ^ k) : ℝ) :=
      add_le_add hPlus hMinus
    _ = A *
        (2 / (Nat.totient (3 * q ^ k) : ℝ)) := by
      ring
    _ = A /
        ((q ^ (k - 1) * (q - 1) : ℕ) : ℝ) := by
      rw [owner_level_density_coefficient hq hq3 k hk]
      ring

/-- The prime-power denominator has the geometric form
    required by the lower-tail estimate. -/
theorem prime_power_bound_eq_geometric
    (A : ℝ) {q k : ℕ}
    (hq : q.Prime) (hk : 0 < k) :
    A / ((q ^ (k - 1) * (q - 1) : ℕ) : ℝ) =
      (A * (q : ℝ) / ((q : ℝ) - 1)) *
        (1 / (q : ℝ)) ^ k := by
  have hq1 : 1 ≤ q := by
    have := hq.two_le
    omega
  have hqR : (1 : ℝ) < q := by
    exact_mod_cast hq.one_lt
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  have hm0 : (q : ℝ) - 1 ≠ 0 := by linarith
  cases k with
  | zero => omega
  | succ n =>
      simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_pow]
      rw [Nat.cast_sub hq1]
      simp only [Nat.cast_one, one_div, pow_succ]
      have hinv :
          (q : ℝ) ^ n * ((q : ℝ)⁻¹) ^ n = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hq0, one_pow]
      field_simp [hq0, hm0]
      simp only [one_div, mul_assoc, hinv, mul_one]

/-- A reduced-class prime-counting estimate supplies
    a geometric bound for the owner residue count. -/
theorem residueLevel_count_le_geometric_of_prime_class_bound
    (T : Finset ℕ) (X q k : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hOwner3 : ∀ p ∈ T, p ≠ 3)
    (hX : ∀ p ∈ T, p ≤ X)
    (hq : q.Prime) (hq3 : q ≠ 3)
    (hk : 0 < k)
    (A : ℝ)
    (hAP : ∀ r : ℕ,
      r < 3 * q ^ k →
      Nat.Coprime r (3 * q ^ k) →
        (primeResidueCount X (3 * q ^ k) r : ℝ) ≤
          A / (Nat.totient (3 * q ^ k) : ℝ)) :
    ((residueLevelOwners T (q ^ k)).card : ℝ) ≤
      (A * (q : ℝ) / ((q : ℝ) - 1)) *
        (1 / (q : ℝ)) ^ k := by
  have hlevel :=
    doorLevel_count_le_of_prime_class_bound
      T X q k hP hOwner3 hX hq hq3 hk A hAP
  rw [card_doorLevelOwners_eq_residueLevelOwners
    T (q ^ k) hP hOwner3
    (one_lt_prime_pow_level hq hk)] at hlevel
  rw [prime_power_bound_eq_geometric A hq hk] at hlevel
  exact hlevel

/-- Reduced-class prime-counting bounds at the lower
    omitted levels control the full truncation error. -/
theorem truncation_error_le_of_prime_class_bounds
    (T : Finset ℕ) (X q K J B : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hOwner3 : ∀ p ∈ T, p ≠ 3)
    (hX : ∀ p ∈ T, p ≤ X)
    (hq : q.Prime) (hq3 : q ≠ 3)
    (hKJ : K ≤ J)
    (hB : ∀ p ∈ T, Hire.m0 p < q ^ B)
    (A : ℝ) (hA : 0 ≤ A)
    (hAP : ∀ k ∈ Finset.Ico 1 B,
      K < k → k ≤ J →
      ∀ r : ℕ,
        r < 3 * q ^ k →
        Nat.Coprime r (3 * q ^ k) →
          (primeResidueCount X (3 * q ^ k) r : ℝ) ≤
            A / (Nat.totient (3 * q ^ k) : ℝ)) :
    ((incomingMultiplicity T q -
        truncatedIncomingMultiplicity T q K B : ℕ) : ℝ) ≤
      (A * (q : ℝ) / ((q : ℝ) - 1)) *
        (1 / (q : ℝ)) ^ (K + 1) /
          (1 - 1 / (q : ℝ)) +
      (2 * (X : ℝ) * (1 / (q : ℝ)) ^ (J + 1) /
        (1 - 1 / (q : ℝ)) +
          2 * ((B - (J + 1) : ℕ) : ℝ)) := by
  have hqR : (1 : ℝ) < q := by
    exact_mod_cast hq.one_lt
  have hC :
      0 ≤ A * (q : ℝ) / ((q : ℝ) - 1) :=
    div_nonneg
      (mul_nonneg hA (Nat.cast_nonneg q))
      (by linarith)
  apply incomingMultiplicity_truncation_error_le
    T X q K J B hP hOwner3 hq hX hKJ hB
    (A * (q : ℝ) / ((q : ℝ) - 1)) hC
  intro k hk hkK hkJ
  have hkpos : 0 < k := by
    have := (Finset.mem_Ico.mp hk).1
    omega
  exact residueLevel_count_le_geometric_of_prime_class_bound
    T X q k hP hOwner3 hX hq hq3 hkpos A
    (hAP k hk hkK hkJ)

end HireEulerDoor
