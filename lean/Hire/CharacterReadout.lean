import Mathlib
import Hire.Doors
import Hire.EulerDoor

namespace HireCharacterReadout

/-- The two owner residue conditions for hub 5. -/
def ownerIndicator15 (n : ℕ) : ℕ :=
  if (n % 3 = 1 ∧ n % 5 = 4) ∨
      (n % 3 = 2 ∧ n % 5 = 1) then 1 else 0

/-- The principal character modulo 15. -/
def principal15 (n : ℕ) : ℕ :=
  if n % 3 = 0 ∨ n % 5 = 0 then 0 else 1

/-- The quadratic character modulo 5, extended to
    vanish on multiples of 3. -/
def quadratic15 (n : ℕ) : ℤ :=
  if n % 3 = 0 then 0
  else if n % 5 = 1 ∨ n % 5 = 4 then 1
  else if n % 5 = 2 ∨ n % 5 = 3 then -1
  else 0

/-- The quartic character modulo 5, with value I at 2. -/
noncomputable def quarticFive (n : ℕ) : ℂ :=
  match n % 5 with
  | 1 => 1
  | 2 => Complex.I
  | 3 => -Complex.I
  | 4 => -1
  | _ => 0

/-- The complex character used in the modulus-15 experiment. -/
noncomputable def complex15 (n : ℕ) : ℂ :=
  (Hire.chi3 n : ℂ) * quarticFive n

/-- The exact real-valued decomposition used by the
    numerical experiment, valid for every natural number. -/
theorem ownerIndicator15_decomposition (n : ℕ) :
    4 * (ownerIndicator15 n : ℝ) =
      (principal15 n : ℝ) +
        (quadratic15 n : ℝ) -
          2 * (complex15 n).re := by
  set r3 := n % 3 with h3
  set r5 := n % 5 with h5
  have hr3 : r3 < 3 := Nat.mod_lt n (by norm_num)
  have hr5 : r5 < 5 := Nat.mod_lt n (by norm_num)
  interval_cases r3 <;> interval_cases r5 <;>
    norm_num [ownerIndicator15, principal15, quadratic15,
      complex15, quarticFive, Hire.chi3, ← h3, ← h5]

/-- For prime owners other than 3, this indicator selects
    exactly the doors divisible by 5. -/
theorem ownerIndicator15_eq_door_indicator
    {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    ownerIndicator15 p =
      if 5 ∣ Hire.m0 p then 1 else 0 := by
  have hd :=
    HireEulerDoor.dvd_m0_iff_owner_residues
      (Q := 5) hp h3 (by norm_num)
  norm_num at hd
  simp [ownerIndicator15, hd]

/-- The modulus-15 decomposition holds for any finite real weighting. -/
theorem sum_weighted_ownerIndicator15_decomposition
    (S : Finset ℕ) (w : ℕ → ℝ) :
    4 * (∑ n ∈ S, w n * (ownerIndicator15 n : ℝ)) =
      (∑ n ∈ S, w n * (principal15 n : ℝ)) +
        (∑ n ∈ S, w n * (quadratic15 n : ℝ)) -
          2 * (∑ n ∈ S, w n * (complex15 n).re) := by
  calc
    _ = ∑ n ∈ S,
        w n * (4 * (ownerIndicator15 n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = ∑ n ∈ S,
        (w n * (principal15 n : ℝ) +
          w n * (quadratic15 n : ℝ) -
            2 * (w n * (complex15 n).re)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ownerIndicator15_decomposition]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The weighted indicator counts precisely the selected prime owners. -/
theorem sum_weighted_ownerIndicator15_eq_door_sum
    (T : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ T, p.Prime)
    (h3 : ∀ p ∈ T, p ≠ 3) :
    (∑ p ∈ T, w p * (ownerIndicator15 p : ℝ)) =
      ∑ p ∈ T.filter (fun p => 5 ∣ Hire.m0 p), w p := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ownerIndicator15_eq_door_indicator (hP p hp) (h3 p hp)]
  by_cases hd : 5 ∣ Hire.m0 p <;> simp [hd]

/-- The von Mangoldt Dirichlet weight at a real exponent. -/
noncomputable def mangoldtDirichletWeight
    (σ : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) /
    Real.rpow (n : ℝ) σ

/-- A finite Dirichlet sum for the selected modulus-15 classes. -/
noncomputable def ownerMangoldtSum15
    (N : ℕ) (σ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    mangoldtDirichletWeight σ n *
      (ownerIndicator15 n : ℝ)

/-- The finite Mangoldt sum splits into its character contributions. -/
theorem ownerMangoldtSum15_decomposition
    (N : ℕ) (σ : ℝ) :
    4 * ownerMangoldtSum15 N σ =
      (∑ n ∈ Finset.Icc 1 N,
        mangoldtDirichletWeight σ n *
          (principal15 n : ℝ)) +
      (∑ n ∈ Finset.Icc 1 N,
        mangoldtDirichletWeight σ n *
          (quadratic15 n : ℝ)) -
      2 * (∑ n ∈ Finset.Icc 1 N,
        mangoldtDirichletWeight σ n *
          (complex15 n).re) := by
  simpa only [ownerMangoldtSum15] using
    sum_weighted_ownerIndicator15_decomposition
      (Finset.Icc 1 N) (mangoldtDirichletWeight σ)

/-- Remove multiples of 3, then the remaining multiples of 5. -/
theorem sum_weighted_principal15
    (S : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ S, w n * (principal15 n : ℝ)) =
      (∑ n ∈ S, w n) -
      (∑ n ∈ S.filter (fun n => n % 3 = 0), w n) -
      (∑ n ∈ S.filter
        (fun n => n % 3 ≠ 0 ∧ n % 5 = 0), w n) := by
  classical
  simp only [Finset.sum_filter]
  calc
    _ = ∑ n ∈ S,
        (w n -
          (if n % 3 = 0 then w n else 0) -
          (if n % 3 ≠ 0 ∧ n % 5 = 0
            then w n else 0)) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h3 : n % 3 = 0 <;>
        by_cases h5 : n % 5 = 0 <;>
        simp [principal15, h3, h5]
    _ = _ := by
      simp only [Finset.sum_sub_distrib]

/-- The principal Mangoldt sum has an exact finite correction. -/
theorem principalMangoldtSum15_eq_sub_corrections
    (N : ℕ) (σ : ℝ) :
    (∑ n ∈ Finset.Icc 1 N,
      mangoldtDirichletWeight σ n *
        (principal15 n : ℝ)) =
      (∑ n ∈ Finset.Icc 1 N,
        mangoldtDirichletWeight σ n) -
      (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => n % 3 = 0),
        mangoldtDirichletWeight σ n) -
      (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => n % 3 ≠ 0 ∧ n % 5 = 0),
        mangoldtDirichletWeight σ n) := by
  exact sum_weighted_principal15
    (Finset.Icc 1 N) (mangoldtDirichletWeight σ)

/-- Every positive power of a prime carries the same logarithmic weight. -/
theorem mangoldtDirichletWeight_prime_pow
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (σ : ℝ) :
    mangoldtDirichletWeight σ (p ^ k) =
      Real.log (p : ℝ) /
        Real.rpow ((p ^ k : ℕ) : ℝ) σ := by
  unfold mangoldtDirichletWeight
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- A prime divisor identifies the base of a nonzero Mangoldt term. -/
theorem exists_prime_pow_of_dvd_of_vonMangoldt_ne_zero
    {p n : ℕ} (hp : p.Prime) (hd : p ∣ n)
    (hn : ArithmeticFunction.vonMangoldt n ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ n = p ^ k := by
  have hpow : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn
  obtain ⟨q, k, hq, hk, hqk⟩ :=
    (isPrimePow_nat_iff n).mp hpow
  have hpq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp
      (hp.dvd_of_dvd_pow (hqk ▸ hd))
  subst q
  exact ⟨k, hk, hqk.symm⟩

/-- Among multiples of a prime, precisely its positive powers contribute. -/
theorem vonMangoldt_ne_zero_iff_prime_pow_of_dvd
    {p n : ℕ} (hp : p.Prime) (hd : p ∣ n) :
    ArithmeticFunction.vonMangoldt n ≠ 0 ↔
      ∃ k : ℕ, 0 < k ∧ n = p ^ k := by
  constructor
  · exact exists_prime_pow_of_dvd_of_vonMangoldt_ne_zero hp hd
  · rintro ⟨k, hk, rfl⟩
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr
      (hp.isPrimePow.pow (Nat.ne_of_gt hk))

/-- Two distinct prime divisors force the Mangoldt weight to vanish. -/
theorem vonMangoldt_eq_zero_of_two_distinct_prime_divisors
    {p q n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n) :
    ArithmeticFunction.vonMangoldt n = 0 := by
  by_contra hn
  obtain ⟨k, hk, hnk⟩ :=
    exists_prime_pow_of_dvd_of_vonMangoldt_ne_zero hp hpn hn
  have hqp : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq hp).mp
      (hq.dvd_of_dvd_pow (hnk ▸ hqn))
  exact hpq hqp.symm

/-- Multiples of both 3 and 5 contribute nothing to the corrections. -/
theorem mangoldtDirichletWeight_eq_zero_of_three_and_five_dvd
    {n : ℕ} (h3 : 3 ∣ n) (h5 : 5 ∣ n) (σ : ℝ) :
    mangoldtDirichletWeight σ n = 0 := by
  have hn : ArithmeticFunction.vonMangoldt n = 0 :=
    vonMangoldt_eq_zero_of_two_distinct_prime_divisors
      (by norm_num) (by norm_num) (by norm_num) h3 h5
  simp [mangoldtDirichletWeight, hn]

/-- Positive exponents whose prime powers lie below the cutoff. -/
def primePowerExponents (p N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun k => p ^ k ≤ N)

/-- Reindex the Mangoldt correction over multiples of a prime
    as a sum over its positive powers. -/
theorem sum_mangoldtDirichletWeight_multiples_eq_prime_powers
    {p : ℕ} (hp : p.Prime) (N : ℕ) (σ : ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n),
      mangoldtDirichletWeight σ n) =
    ∑ k ∈ primePowerExponents p N,
      Real.log (p : ℝ) /
        Real.rpow ((p ^ k : ℕ) : ℝ) σ := by
  classical
  let E := primePowerExponents p N
  let A := (Finset.Icc 1 N).filter (fun n => p ∣ n)

  have hsub : E.image (fun k => p ^ k) ⊆ A := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have hk' :
        k ∈ Finset.Icc 1 N ∧ p ^ k ≤ N := by
      simpa only [E, primePowerExponents,
        Finset.mem_filter] using hk
    have hkpos : 0 < k :=
      (Finset.mem_Icc.mp hk'.1).1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨pow_pos hp.pos k, hk'.2⟩,
      dvd_pow_self p (Nat.ne_of_gt hkpos)⟩

  have hzero :
      ∀ n ∈ A, n ∉ E.image (fun k => p ^ k) →
        mangoldtDirichletWeight σ n = 0 := by
    intro n hn hnot
    obtain ⟨hnIcc, hpn⟩ := Finset.mem_filter.mp hn
    have hΛ : ArithmeticFunction.vonMangoldt n = 0 := by
      by_contra hne
      obtain ⟨k, hk, hnk⟩ :=
        exists_prime_pow_of_dvd_of_vonMangoldt_ne_zero
          hp hpn hne
      have hkN : k ≤ N := by
        calc
          k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
          _ = n := hnk.symm
          _ ≤ N := (Finset.mem_Icc.mp hnIcc).2
      have hkE : k ∈ E := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨hk, hkN⟩,
          by rw [← hnk]; exact (Finset.mem_Icc.mp hnIcc).2⟩
      exact hnot (Finset.mem_image.mpr ⟨k, hkE, hnk.symm⟩)
    simp [mangoldtDirichletWeight, hΛ]

  calc
    _ = ∑ n ∈ E.image (fun k => p ^ k),
        mangoldtDirichletWeight σ n := by
      exact (Finset.sum_subset hsub hzero).symm
    _ = ∑ k ∈ E,
        mangoldtDirichletWeight σ (p ^ k) := by
      apply Finset.sum_image
      intro a ha b hb hab
      have heq :=
        congrArg (fun n : ℕ => n.factorization p) hab
      simpa [hp.factorization_pow] using heq
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkpos : 0 < k :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
      exact mangoldtDirichletWeight_prime_pow
        hp (Nat.ne_of_gt hkpos) σ

/-- The positive-power geometric correction, including convergence. -/
theorem hasSum_positive_power_correction
    (a c : ℝ) (ha : 1 < a) :
    HasSum (fun k : ℕ => c / a ^ (k + 1))
      (c / (a - 1)) := by
  have ha0 : 0 < a := by linarith
  have hane : a ≠ 0 := ne_of_gt ha0
  have hsub : a - 1 ≠ 0 := by linarith
  have hr0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hr1 : a⁻¹ < 1 := by
    have hdiv : 1 / a < 1 := by
      apply (div_lt_iff₀ ha0).2
      linarith
    simpa only [one_div] using hdiv
  have hgeom :
      HasSum (fun k : ℕ => (a⁻¹) ^ k)
        (1 - a⁻¹)⁻¹ :=
    hasSum_geometric_of_abs_lt_one
      (by rwa [abs_of_nonneg hr0])
  have hterm (k : ℕ) :
      c / a ^ (k + 1) =
        (c / a) * (a⁻¹) ^ k := by
    simp [pow_succ, div_eq_mul_inv, mul_comm, mul_assoc]
  have hsum :
      HasSum (fun k : ℕ => c / a ^ (k + 1))
        ((c / a) * (1 - a⁻¹)⁻¹) := by
    simp_rw [hterm]
    exact hgeom.mul_left (c / a)
  have hvalue :
      (c / a) * (1 - a⁻¹)⁻¹ = c / (a - 1) := by
    field_simp [hane, hsub]
  rw [hvalue] at hsum
  exact hsum

/-- The Dirichlet denominator at a prime power is geometric in k. -/
theorem rpow_prime_pow
    (p k : ℕ) (σ : ℝ) :
    Real.rpow ((p ^ k : ℕ) : ℝ) σ =
      (Real.rpow (p : ℝ) σ) ^ k := by
  calc
    _ = Real.rpow
        (Real.rpow (p : ℝ) (k : ℝ)) σ := by
      have hkpow :
          Real.rpow (p : ℝ) (k : ℝ) = (p : ℝ) ^ k :=
        Real.rpow_natCast (p : ℝ) k
      rw [hkpow, Nat.cast_pow]
    _ = Real.rpow (p : ℝ) ((k : ℝ) * σ) :=
      (Real.rpow_mul (Nat.cast_nonneg p) (k : ℝ) σ).symm
    _ = Real.rpow (p : ℝ) (σ * (k : ℝ)) := by
      rw [mul_comm]
    _ = Real.rpow
        (Real.rpow (p : ℝ) σ) (k : ℝ) :=
      Real.rpow_mul (Nat.cast_nonneg p) σ (k : ℝ)
    _ = _ := Real.rpow_natCast _ k

/-- The infinite prime-power correction converges to its Euler expression. -/
theorem hasSum_mangoldt_prime_power_correction
    {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 1 < σ) :
    HasSum
      (fun k : ℕ =>
        Real.log (p : ℝ) /
          Real.rpow ((p ^ (k + 1) : ℕ) : ℝ) σ)
      (Real.log (p : ℝ) /
        (Real.rpow (p : ℝ) σ - 1)) := by
  have hpR : 1 < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hσ0 : 0 < σ := by linarith
  have ha : 1 < Real.rpow (p : ℝ) σ :=
    Real.one_lt_rpow hpR hσ0
  simp_rw [rpow_prime_pow]
  exact hasSum_positive_power_correction
    (Real.rpow (p : ℝ) σ) (Real.log (p : ℝ)) ha

/-- Cutting off prime powers by their size approaches the full correction. -/
theorem tendsto_prime_power_correction
    {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ k ∈ (Finset.range N).filter
            (fun k => p ^ (k + 1) ≤ N),
          Real.log (p : ℝ) /
            Real.rpow ((p ^ (k + 1) : ℕ) : ℝ) σ)
      Filter.atTop
      (nhds (Real.log (p : ℝ) /
        (Real.rpow (p : ℝ) σ - 1))) := by
  classical
  let F : ℕ → Finset ℕ := fun N =>
    (Finset.range N).filter (fun k => p ^ (k + 1) ≤ N)

  have hcut :
      Filter.Tendsto F Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro S
    apply Filter.eventually_atTop.2
    refine ⟨S.sup (fun k => max (k + 1) (p ^ (k + 1))), ?_⟩
    intro N hN k hk
    have hbound :
        max (k + 1) (p ^ (k + 1)) ≤
          S.sup (fun j => max (j + 1) (p ^ (j + 1))) :=
      Finset.le_sup
        (f := fun j : ℕ => max (j + 1) (p ^ (j + 1))) hk
    have hkN : k < N := by
      have hleft :
          k + 1 ≤ max (k + 1) (p ^ (k + 1)) :=
        le_max_left _ _
      omega
    have hpowN : p ^ (k + 1) ≤ N :=
      (le_max_right _ _).trans (hbound.trans hN)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hkN, hpowN⟩

  have hsum :=
    hasSum_mangoldt_prime_power_correction hp hσ
  simpa only [F, Function.comp_def] using hsum.comp hcut

/-- Positive exponents and shifted natural indices give the same cutoff sum. -/
theorem primePowerExponents_sum_eq_shifted
    (p N : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ primePowerExponents p N, f k) =
      ∑ k ∈ (Finset.range N).filter
        (fun k => p ^ (k + 1) ≤ N), f (k + 1) := by
  classical
  symm
  apply Finset.sum_bij (fun k _ => k + 1)
  · intro k hk
    obtain ⟨hkN, hpow⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨Nat.succ_pos k, Nat.succ_le_of_lt (Finset.mem_range.mp hkN)⟩,
      hpow⟩
  · intro a ha b hb hab
    omega
  · intro e he
    obtain ⟨heIcc, hpow⟩ := Finset.mem_filter.mp he
    obtain ⟨hepos, heN⟩ := Finset.mem_Icc.mp heIcc
    have hshift : e - 1 + 1 = e := by omega
    refine ⟨e - 1, ?_, hshift⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      omega
    · simpa only [hshift] using hpow
  · intro k hk
    rfl

/-- The correction over multiples of a prime approaches its Euler expression. -/
theorem tendsto_mangoldtDirichletWeight_multiples
    {p : ℕ} (hp : p.Prime)
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n),
          mangoldtDirichletWeight σ n)
      Filter.atTop
      (nhds (Real.log (p : ℝ) /
        (Real.rpow (p : ℝ) σ - 1))) := by
  have heq :
      (fun N : ℕ =>
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n),
          mangoldtDirichletWeight σ n) =
      (fun N : ℕ =>
        ∑ k ∈ (Finset.range N).filter
            (fun k => p ^ (k + 1) ≤ N),
          Real.log (p : ℝ) /
            Real.rpow ((p ^ (k + 1) : ℕ) : ℝ) σ) := by
    funext N
    rw [sum_mangoldtDirichletWeight_multiples_eq_prime_powers hp,
      primePowerExponents_sum_eq_shifted]
  rw [heq]
  exact tendsto_prime_power_correction hp hσ

/-- Excluding multiples of 3 does not change the multiples-of-5 correction. -/
theorem sum_mangoldt_five_correction_eq
    (N : ℕ) (σ : ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => n % 3 ≠ 0 ∧ n % 5 = 0),
      mangoldtDirichletWeight σ n) =
    ∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => n % 5 = 0),
      mangoldtDirichletWeight σ n := by
  classical
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hnIcc, h3, h5⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnIcc, h5⟩
  · intro n hn hnot
    obtain ⟨hnIcc, h5⟩ := Finset.mem_filter.mp hn
    by_cases h3 : n % 3 = 0
    · exact mangoldtDirichletWeight_eq_zero_of_three_and_five_dvd
        (Nat.dvd_of_mod_eq_zero h3)
        (Nat.dvd_of_mod_eq_zero h5) σ
    · exact False.elim
        (hnot (Finset.mem_filter.mpr ⟨hnIcc, h3, h5⟩))

/-- Transfer a full Mangoldt-sum limit to the principal contribution. -/
theorem tendsto_principalMangoldtSum15_of_full_limit
    {σ A : ℝ} (hσ : 1 < σ)
    (hFull :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.Icc 1 N,
            mangoldtDirichletWeight σ n)
        Filter.atTop (nhds A)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          mangoldtDirichletWeight σ n *
            (principal15 n : ℝ))
      Filter.atTop
      (nhds
        (A -
          Real.log 3 / (Real.rpow 3 σ - 1) -
          Real.log 5 / (Real.rpow 5 σ - 1))) := by
  have hthree :=
    tendsto_mangoldtDirichletWeight_multiples
      (p := 3) (by norm_num) hσ
  have hfive :=
    tendsto_mangoldtDirichletWeight_multiples
      (p := 5) (by norm_num) hσ

  have heq :
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          mangoldtDirichletWeight σ n *
            (principal15 n : ℝ)) =
      (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N,
          mangoldtDirichletWeight σ n) -
        (∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => 3 ∣ n),
          mangoldtDirichletWeight σ n) -
        (∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => 5 ∣ n),
          mangoldtDirichletWeight σ n)) := by
    funext N
    rw [principalMangoldtSum15_eq_sub_corrections,
      sum_mangoldt_five_correction_eq]
    simp only [Nat.dvd_iff_mod_eq_zero]

  rw [heq]
  exact (hFull.sub hthree).sub hfive

/-- The real-valued zeta logarithmic derivative used by our sums. -/
noncomputable def zetaMangoldtValue (σ : ℝ) : ℝ :=
  (-deriv riemannZeta (σ : ℂ) /
    riemannZeta (σ : ℂ)).re

/-- Our real weight is the real part of the complex L-series term. -/
theorem mangoldtDirichletWeight_eq_term_re
    (σ : ℝ) (n : ℕ) :
    mangoldtDirichletWeight σ n =
      (LSeries.term
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (σ : ℂ) n).re := by
  by_cases hn : n = 0
  · subst n
    simp [mangoldtDirichletWeight]
  · rw [LSeries.term_of_ne_zero hn]
    have hpow :
        (n : ℂ) ^ (σ : ℂ) =
          (Real.rpow (n : ℝ) σ : ℂ) := by
      simpa only [Complex.ofReal_natCast,
        ← Real.rpow_eq_pow] using
        (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
    rw [hpow, ← Complex.ofReal_div, Complex.ofReal_re]
    rfl

/-- Mathlib supplies convergence and the zeta value of the full series. -/
theorem hasSum_mangoldtDirichletWeight
    {σ : ℝ} (hσ : 1 < σ) :
    HasSum (mangoldtDirichletWeight σ)
      (zetaMangoldtValue σ) := by
  have hσC : 1 < (σ : ℂ).re := by
    simpa using hσ
  have hs :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσC
  have hc :
      HasSum
        (LSeries.term
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ : ℂ))
        (-deriv riemannZeta (σ : ℂ) /
          riemannZeta (σ : ℂ)) := by
    have h := hs.LSeriesHasSum
    change HasSum
      (LSeries.term
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ : ℂ))
      (LSeries
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ : ℂ)) at h
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      hσC] at h
    exact h
  have hr := Complex.reCLM.hasSum hc
  simpa only [Complex.reCLM_apply,
    ← mangoldtDirichletWeight_eq_term_re,
    zetaMangoldtValue] using hr

/-- A convergent series with zero initial term has these partial-sum limits. -/
theorem tendsto_sum_Icc_one_of_hasSum
    {f : ℕ → ℝ} {A : ℝ}
    (hs : HasSum f A) (hzero : f 0 = 0) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
      Filter.atTop (nhds A) := by
  classical
  have hcut :
      Filter.Tendsto
        (fun N : ℕ => Finset.Icc 0 N)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro S
    apply Filter.eventually_atTop.2
    refine ⟨S.sup (fun n : ℕ => n), ?_⟩
    intro N hN n hn
    exact Finset.mem_Icc.mpr
      ⟨Nat.zero_le n,
        (Finset.le_sup (f := fun n : ℕ => n) hn).trans hN⟩

  have heq :
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n) =
      (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, f n) := by
    funext N
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Icc.mpr
        ⟨Nat.zero_le n, (Finset.mem_Icc.mp hn).2⟩
    · intro n hn hnot
      by_cases hn0 : n = 0
      · simpa only [hn0] using hzero
      · exact False.elim
          (hnot (Finset.mem_Icc.mpr
            ⟨Nat.one_le_iff_ne_zero.mpr hn0,
              (Finset.mem_Icc.mp hn).2⟩))
  rw [heq]
  simpa only [Function.comp_def] using hs.comp hcut

/-- The full finite Mangoldt sums approach the zeta logarithmic derivative. -/
theorem tendsto_fullMangoldtSum
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          mangoldtDirichletWeight σ n)
      Filter.atTop (nhds (zetaMangoldtValue σ)) := by
  apply tendsto_sum_Icc_one_of_hasSum
    (hasSum_mangoldtDirichletWeight hσ)
  simp [mangoldtDirichletWeight]

/-- The principal contribution has its explicit zeta limit. -/
theorem tendsto_principalMangoldtSum15
    {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          mangoldtDirichletWeight σ n *
            (principal15 n : ℝ))
      Filter.atTop
      (nhds
        (zetaMangoldtValue σ -
          Real.log 3 / (Real.rpow 3 σ - 1) -
          Real.log 5 / (Real.rpow 5 σ - 1))) := by
  exact tendsto_principalMangoldtSum15_of_full_limit
    hσ (tendsto_fullMangoldtSum hσ)

end HireCharacterReadout
