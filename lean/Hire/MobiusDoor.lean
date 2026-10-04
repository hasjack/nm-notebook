import Hire.Mobius
import Hire.GoldDisconnects

open scoped BigOperators

namespace Hire

/-- The logarithm-weighted Möbius sum over divisors of the door. -/
noncomputable def doorMobiusWeight (p : ℕ) : ℝ :=
  ∑ d ∈ (m0 p).divisors,
    (ArithmeticFunction.moebius d : ℝ) *
      ArithmeticFunction.log d

/-- For odd primes other than 3, the weight detects 2-power doors. -/
theorem doorMobiusWeight_ne_zero_iff_twoPowerDoor
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) :
    doorMobiusWeight p ≠ 0 ↔ IsTwoPowerDoor p := by
  have heven : 2 ∣ m0 p :=
    even_iff_two_dvd.mp (even_m0 hp hodd h3)
  change
    (∑ d ∈ (m0 p).divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        ArithmeticFunction.log d) ≠ 0 ↔ IsTwoPowerDoor p
  rw [HireMobius.weighted_divisor_sum_ne_zero_iff_two_pow heven]
  constructor
  · rintro ⟨k, _hk, hpow⟩
    exact ⟨k, hpow⟩
  · rintro ⟨k, hpow⟩
    have hk : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      simp [hpow, hk0] at heven
    exact ⟨k, hk, hpow⟩

/-- A 2-power door has weight exactly `-log 2`. -/
theorem doorMobiusWeight_of_twoPowerDoor
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3)
    (hdoor : IsTwoPowerDoor p) :
    doorMobiusWeight p = -Real.log 2 := by
  obtain ⟨k, hpow⟩ := hdoor
  have heven : 2 ∣ m0 p :=
    even_iff_two_dvd.mp (even_m0 hp hodd h3)
  have hk : k ≠ 0 := by
    intro hk0
    simp [hpow, hk0] at heven
  unfold doorMobiusWeight
  rw [hpow]
  exact HireMobius.weighted_divisor_sum_two_pow hk

/-- Among non-hub hired vertices, nonzero weight detects sinks. -/
theorem doorMobiusWeight_ne_zero_iff_isSink
    {X p : ℕ} (hH : Hired (owners X) p) (h2 : p ≠ 2) :
    doorMobiusWeight p ≠ 0 ↔ IsSink X p := by
  have hp : p.Prime := prime_of_hired_ne_two hH h2
  have hodd : Odd p := odd_of_prime_ne_two hp h2
  have h3 : p ≠ 3 := hired_ne_three hH
  rw [doorMobiusWeight_ne_zero_iff_twoPowerDoor hp hodd h3]
  constructor
  · intro hdoor
    exact ⟨hH, h2, fun _ harc =>
      not_GoldArc_of_twoPowerDoor hdoor harc⟩
  · intro hsink
    exact (sinks_eq_twoPowerDoors.mp hsink).2.2.2.1

/-- The weight is `-log 2` at a sink. -/
theorem doorMobiusWeight_of_isSink
    {X p : ℕ} (hsink : IsSink X p) :
    doorMobiusWeight p = -Real.log 2 := by
  obtain ⟨hp, hodd, h3, hdoor, _⟩ :=
    sinks_eq_twoPowerDoors.mp hsink
  exact doorMobiusWeight_of_twoPowerDoor hp hodd h3 hdoor

/-- The weight vanishes at every non-hub hired vertex that is not a sink. -/
theorem doorMobiusWeight_of_not_isSink
    {X p : ℕ} (hH : Hired (owners X) p) (h2 : p ≠ 2)
    (hsink : ¬ IsSink X p) :
    doorMobiusWeight p = 0 := by
  by_contra hne
  exact hsink ((doorMobiusWeight_ne_zero_iff_isSink hH h2).mp hne)

open scoped Classical
/-- Summing door weights counts the sinks in a finite set of non-hub hired vertices. -/
theorem sum_doorMobiusWeight_eq_sink_count
    {X : ℕ} (T : Finset ℕ)
    (hH : ∀ p ∈ T, Hired (owners X) p)
    (h2 : ∀ p ∈ T, p ≠ 2) :
    (∑ p ∈ T, doorMobiusWeight p) =
      ((T.filter (fun p => IsSink X p)).card : ℝ) *
        (-Real.log 2) := by
  classical
  calc
    (∑ p ∈ T, doorMobiusWeight p)
        = ∑ p ∈ T.filter (fun p => IsSink X p),
            (-Real.log 2) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hs : IsSink X p
          · simp only [ite_eq_left hs]
            exact doorMobiusWeight_of_isSink hs
          · simp only [ite_eq_right hs]
            exact doorMobiusWeight_of_not_isSink
              (hH p hp) (h2 p hp) hs
    _ = ((T.filter (fun p => IsSink X p)).card : ℝ) *
          (-Real.log 2) := by
          simp [nsmul_eq_mul]

/-- All divisors appearing in doors of vertices in `T`. -/
def doorDivisorSet (T : Finset ℕ) : Finset ℕ :=
  T.biUnion (fun p => (m0 p).divisors)

/-- Number of doors in `T` whose divisor set contains `d`. -/
def doorDivisorCount (T : Finset ℕ) (d : ℕ) : ℕ :=
  (T.filter (fun p => d ∈ (m0 p).divisors)).card

/-- Reverse the finite Möbius-weighted door sum. -/
theorem sum_doorMobiusWeight_eq_divisor_counts
    (T : Finset ℕ) :
    (∑ p ∈ T, doorMobiusWeight p) =
      ∑ d ∈ doorDivisorSet T,
        (doorDivisorCount T d : ℝ) *
          ((ArithmeticFunction.moebius d : ℝ) *
            ArithmeticFunction.log d) := by
  classical
  let w : ℕ → ℝ := fun d =>
    (ArithmeticFunction.moebius d : ℝ) *
      ArithmeticFunction.log d
  change (∑ p ∈ T, ∑ d ∈ (m0 p).divisors, w d) =
    ∑ d ∈ doorDivisorSet T, (doorDivisorCount T d : ℝ) * w d
  calc
    (∑ p ∈ T, ∑ d ∈ (m0 p).divisors, w d)
        = ∑ p ∈ T, ∑ d ∈ doorDivisorSet T,
            if d ∈ (m0 p).divisors then w d else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          have hsub : (m0 p).divisors ⊆ doorDivisorSet T := by
            intro d hd
            exact Finset.mem_biUnion.mpr ⟨p, hp, hd⟩
          calc
            (∑ d ∈ (m0 p).divisors, w d)
                = ∑ d ∈ (m0 p).divisors,
                    if d ∈ (m0 p).divisors then w d else 0 := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  simp [hd]
            _ = ∑ d ∈ doorDivisorSet T,
                    if d ∈ (m0 p).divisors then w d else 0 := by
                  apply Finset.sum_subset hsub
                  intro d _hd hnot
                  simp [hnot]
    _ = ∑ d ∈ doorDivisorSet T, ∑ p ∈ T,
          if d ∈ (m0 p).divisors then w d else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ d ∈ doorDivisorSet T,
          (doorDivisorCount T d : ℝ) * w d := by
          apply Finset.sum_congr rfl
          intro d _hd
          rw [← Finset.sum_filter]
          simp [doorDivisorCount, nsmul_eq_mul]

/-- Divisor-count formulation of the gold sink count. -/
theorem divisor_counts_eq_sink_count
    {X : ℕ} (T : Finset ℕ)
    (hH : ∀ p ∈ T, Hired (owners X) p)
    (h2 : ∀ p ∈ T, p ≠ 2) :
    (∑ d ∈ doorDivisorSet T,
      (doorDivisorCount T d : ℝ) *
        ((ArithmeticFunction.moebius d : ℝ) *
          ArithmeticFunction.log d)) =
      ((T.filter (fun p => IsSink X p)).card : ℝ) *
        (-Real.log 2) := by
  rw [← sum_doorMobiusWeight_eq_divisor_counts]
  exact sum_doorMobiusWeight_eq_sink_count T hH h2

/-- Prime doors are positive. -/
theorem m0_pos_of_prime_for_mobius
    {p : ℕ} (hp : p.Prime) :
    0 < m0 p := by
  have hp2 := hp.two_le
  unfold m0
  split_ifs <;> omega

/-- On prime doors, divisor-set membership is ordinary divisibility. -/
theorem mem_door_divisors_iff_dvd
    {p d : ℕ} (hp : p.Prime) :
    d ∈ (m0 p).divisors ↔ d ∣ m0 p := by
  simp [Nat.mem_divisors,
    Nat.ne_of_gt (m0_pos_of_prime_for_mobius hp)]

/-- Door divisibility splits into the two mod-3 branches.
This holds for every natural divisor `d`, including even ones. -/
theorem dvd_m0_iff_mod_branches
    {p d : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    d ∣ m0 p ↔
      (p % 3 = 1 ∧ (p + 1) % d = 0) ∨
      (p % 3 = 2 ∧ (p - 1) % d = 0) := by
  rcases prime_ne_three_mod_three_eq_one_or_two hp h3
    with hmod | hmod
  · simp [m0, hmod, Nat.dvd_iff_mod_eq_zero]
  · simp [m0, hmod, Nat.dvd_iff_mod_eq_zero]

/-- The divisor count is exactly a count of the two congruence branches. -/
theorem doorDivisorCount_eq_mod_branch_count
    (T : Finset ℕ) (d : ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3) :
    doorDivisorCount T d =
      (T.filter (fun p =>
        (p % 3 = 1 ∧ (p + 1) % d = 0) ∨
        (p % 3 = 2 ∧ (p - 1) % d = 0))).card := by
  unfold doorDivisorCount
  congr 1
  apply Finset.filter_congr
  intro p hp
  exact (mem_door_divisors_iff_dvd (hP p hp)).trans
    (dvd_m0_iff_mod_branches (hP p hp) (h3 p hp))

/-- On odd-prime doors, divisibility by `2 * e` and by odd `e` are equivalent. -/
theorem two_mul_dvd_m0_iff
    {p e : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h3 : p ≠ 3) (he : Odd e) :
    2 * e ∣ m0 p ↔ e ∣ m0 p :=
  HireMobius.two_mul_dvd_iff_of_odd_of_even
    he (even_m0 hp hodd h3)

/-- Odd divisors and their doubles have identical door counts. -/
theorem doorDivisorCount_two_mul
    (T : Finset ℕ) {e : ℕ} (he : Odd e)
    (hP : ∀ p ∈ T, p.Prime)
    (hodd : ∀ p ∈ T, Odd p)
    (h3 : ∀ p ∈ T, p ≠ 3) :
    doorDivisorCount T (2 * e) = doorDivisorCount T e := by
  classical
  unfold doorDivisorCount
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [mem_door_divisors_iff_dvd (hP p hp),
    mem_door_divisors_iff_dvd (hP p hp)]
  exact two_mul_dvd_m0_iff
    (hP p hp) (hodd p hp) (h3 p hp) he

/-- Summing the odd/double pairs removes their logarithmic weights. -/
theorem sum_doorDivisorCount_weighted_pairs
    (T S : Finset ℕ)
    (hS : ∀ e ∈ S, Odd e)
    (hP : ∀ p ∈ T, p.Prime)
    (hodd : ∀ p ∈ T, Odd p)
    (h3 : ∀ p ∈ T, p ≠ 3) :
    (∑ e ∈ S,
      ((doorDivisorCount T e : ℝ) *
          ((ArithmeticFunction.moebius e : ℝ) *
            Real.log (e : ℝ)) +
        (doorDivisorCount T (2 * e) : ℝ) *
          ((ArithmeticFunction.moebius (2 * e) : ℝ) *
            Real.log ((2 * e : ℕ) : ℝ)))) =
      (-Real.log 2) *
        ∑ e ∈ S,
          (ArithmeticFunction.moebius e : ℝ) *
            (doorDivisorCount T e : ℝ) := by
  calc
    _ = ∑ e ∈ S,
        (-Real.log 2) *
          ((ArithmeticFunction.moebius e : ℝ) *
            (doorDivisorCount T e : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e he
      calc
        _ = (doorDivisorCount T e : ℝ) *
            (-(ArithmeticFunction.moebius e : ℝ) *
              Real.log 2) := by
          rw [doorDivisorCount_two_mul T (hS e he) hP hodd h3]
          rw [← mul_add]
          exact congrArg
            (fun x : ℝ => (doorDivisorCount T e : ℝ) * x)
            (HireMobius.weighted_moebius_pair (hS e he))
        _ = (-Real.log 2) *
            ((ArithmeticFunction.moebius e : ℝ) *
              (doorDivisorCount T e : ℝ)) := by
          ring
    _ = _ := by
      rw [Finset.mul_sum]

/-- Odd divisors and their doubles occur in the same door divisor set. -/
theorem two_mul_mem_doorDivisorSet_iff
    (T : Finset ℕ) {e : ℕ}
    (he : Odd e)
    (hP : ∀ p ∈ T, p.Prime)
    (hodd : ∀ p ∈ T, Odd p)
    (h3 : ∀ p ∈ T, p ≠ 3) :
    2 * e ∈ doorDivisorSet T ↔ e ∈ doorDivisorSet T := by
  unfold doorDivisorSet
  constructor
  · intro h
    obtain ⟨p, hp, hd⟩ := Finset.mem_biUnion.mp h
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hp, ?_⟩
    rw [mem_door_divisors_iff_dvd (hP p hp)] at hd ⊢
    exact
      (two_mul_dvd_m0_iff
        (hP p hp) (hodd p hp) (h3 p hp) he).mp hd
  · intro h
    obtain ⟨p, hp, hd⟩ := Finset.mem_biUnion.mp h
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hp, ?_⟩
    rw [mem_door_divisors_iff_dvd (hP p hp)] at hd ⊢
    exact
      (two_mul_dvd_m0_iff
        (hP p hp) (hodd p hp) (h3 p hp) he).mpr hd

/-- Divisors divisible by four contribute nothing to the weighted sum. -/
theorem sum_doorDivisorCount_filter_not_four
    (T : Finset ℕ) :
    (∑ d ∈ doorDivisorSet T,
      (doorDivisorCount T d : ℝ) *
        ((ArithmeticFunction.moebius d : ℝ) *
          Real.log (d : ℝ))) =
    ∑ d ∈ (doorDivisorSet T).filter (fun d => ¬ 4 ∣ d),
      (doorDivisorCount T d : ℝ) *
        ((ArithmeticFunction.moebius d : ℝ) *
          Real.log (d : ℝ)) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h4 : 4 ∣ d
  · have hz :
        (ArithmeticFunction.moebius d : ℝ) *
          Real.log (d : ℝ) = 0 :=
      HireMobius.weighted_moebius_eq_zero_of_four_dvd h4
    simp [h4, hz]
  · simp [h4]

/-- After removing multiples of four, the divisor set consists of odd divisors and their doubles. -/
theorem doorDivisorSet_filter_not_four
    (T : Finset ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hodd : ∀ p ∈ T, Odd p)
    (h3 : ∀ p ∈ T, p ≠ 3) :
    (doorDivisorSet T).filter (fun d => ¬ 4 ∣ d) =
      (doorDivisorSet T).filter Odd ∪
        ((doorDivisorSet T).filter Odd).image
          (fun e => 2 * e) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨hdD, h4⟩ := Finset.mem_filter.mp hd
    rcases
        (HireMobius.not_four_dvd_iff_odd_or_twice_odd d).mp h4
      with ho | ⟨e, he, hde⟩
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hdD, ho⟩))
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨e, Finset.mem_filter.mpr ⟨?_, he⟩, hde.symm⟩
      apply
        (two_mul_mem_doorDivisorSet_iff
          T he hP hodd h3).mp
      simpa only [hde] using hdD
  · intro hd
    rcases Finset.mem_union.mp hd with ho | ht
    · obtain ⟨hdD, hdOdd⟩ := Finset.mem_filter.mp ho
      apply Finset.mem_filter.mpr
      refine ⟨hdD, ?_⟩
      exact
        (HireMobius.not_four_dvd_iff_odd_or_twice_odd d).mpr
          (Or.inl hdOdd)
    · obtain ⟨e, heS, hed⟩ := Finset.mem_image.mp ht
      obtain ⟨heD, heOdd⟩ := Finset.mem_filter.mp heS
      apply Finset.mem_filter.mpr
      constructor
      · have hdouble : 2 * e ∈ doorDivisorSet T :=
          (two_mul_mem_doorDivisorSet_iff
            T heOdd hP hodd h3).mpr heD
        simpa only [hed] using hdouble
      · exact
          (HireMobius.not_four_dvd_iff_odd_or_twice_odd d).mpr
            (Or.inr ⟨e, heOdd, hed.symm⟩)

/-- Odd divisors are disjoint from doubles of odd divisors. -/
theorem doorDivisorSet_odd_disjoint_doubles
    (T : Finset ℕ) :
    Disjoint
      ((doorDivisorSet T).filter Odd)
      (((doorDivisorSet T).filter Odd).image
        (fun e => 2 * e)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdOdd hdDouble
  have ho : Odd d := (Finset.mem_filter.mp hdOdd).2
  obtain ⟨e, _, hed⟩ := Finset.mem_image.mp hdDouble
  have hmod : d % 2 = 1 := Nat.odd_iff.mp ho
  omega

/-- The full weighted divisor sum reduces to an odd-divisor Möbius sum. -/
theorem sum_doorDivisorCount_eq_odd_moebius_sum
    (T : Finset ℕ)
    (hP : ∀ p ∈ T, p.Prime)
    (hodd : ∀ p ∈ T, Odd p)
    (h3 : ∀ p ∈ T, p ≠ 3) :
    (∑ d ∈ doorDivisorSet T,
      (doorDivisorCount T d : ℝ) *
        ((ArithmeticFunction.moebius d : ℝ) *
          Real.log (d : ℝ))) =
    (-Real.log 2) *
      ∑ e ∈ (doorDivisorSet T).filter Odd,
        (ArithmeticFunction.moebius e : ℝ) *
          (doorDivisorCount T e : ℝ) := by
  classical
  rw [sum_doorDivisorCount_filter_not_four T]
  rw [doorDivisorSet_filter_not_four T hP hodd h3]
  rw [Finset.sum_union
    (doorDivisorSet_odd_disjoint_doubles T)]
  rw [Finset.sum_image (by
    intro a ha b hb hab
    change 2 * a = 2 * b at hab
    omega)]
  rw [← Finset.sum_add_distrib]
  exact sum_doorDivisorCount_weighted_pairs
    T ((doorDivisorSet T).filter Odd)
    (fun e he => (Finset.mem_filter.mp he).2)
    hP hodd h3

/-- The odd-divisor Möbius sum counts hired non-hub sinks exactly. -/
theorem odd_moebius_sum_eq_sink_count
    {X : ℕ} (T : Finset ℕ)
    (hH : ∀ p ∈ T, Hired (owners X) p)
    (h2 : ∀ p ∈ T, p ≠ 2) :
    (∑ e ∈ (doorDivisorSet T).filter Odd,
      (ArithmeticFunction.moebius e : ℝ) *
        (doorDivisorCount T e : ℝ)) =
    ((T.filter (fun p => IsSink X p)).card : ℝ) := by
  classical
  have hP : ∀ p ∈ T, p.Prime :=
    fun p hp => prime_of_hired_ne_two (hH p hp) (h2 p hp)
  have hodd : ∀ p ∈ T, Odd p :=
    fun p hp => odd_of_prime_ne_two (hP p hp) (h2 p hp)
  have h3 : ∀ p ∈ T, p ≠ 3 :=
    fun p hp => hired_ne_three (hH p hp)
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hneg : -Real.log (2 : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt hlog)
  apply mul_left_cancel₀ hneg
  calc
    _ = ∑ d ∈ doorDivisorSet T,
        (doorDivisorCount T d : ℝ) *
          ((ArithmeticFunction.moebius d : ℝ) *
            Real.log (d : ℝ)) :=
      (sum_doorDivisorCount_eq_odd_moebius_sum
        T hP hodd h3).symm
    _ = ((T.filter (fun p => IsSink X p)).card : ℝ) *
        (-Real.log 2) :=
      divisor_counts_eq_sink_count T hH h2
    _ = _ := by ring

end Hire
