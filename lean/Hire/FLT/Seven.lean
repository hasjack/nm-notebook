import Mathlib.Tactic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Int.Basic

namespace Hire

/-- The second factor in the sum-of-seventh-powers factorisation. -/
def seventhFactor (a b : ℤ) : ℤ :=
  a ^ 6 - a ^ 5 * b + a ^ 4 * b ^ 2
    - a ^ 3 * b ^ 3 + a ^ 2 * b ^ 4
    - a * b ^ 5 + b ^ 6

theorem sum_seventh_powers_factorisation (a b : ℤ) :
    a ^ 7 + b ^ 7 = (a + b) * seventhFactor a b := by
  unfold seventhFactor
  ring

/-- At a = -b, the second factor becomes 7b⁶. -/
theorem seventhFactor_neg_left (b : ℤ) :
    seventhFactor (-b) b = 7 * b ^ 6 := by
  unfold seventhFactor
  ring

/-- The difference from 7b⁶ contains the first factor a+b. -/
theorem seventhFactor_sub_seven_mul_pow (a b : ℤ) :
    seventhFactor a b - 7 * b ^ 6 =
      (a + b) *
        (a ^ 5 - 2 * a ^ 4 * b + 3 * a ^ 3 * b ^ 2
          - 4 * a ^ 2 * b ^ 3 + 5 * a * b ^ 4
          - 6 * b ^ 5) := by
  unfold seventhFactor
  ring

/-- A common divisor of the two factors divides 7b⁶. -/
theorem common_dvd_seventhFactor_dvd_seven_mul_pow
    {a b d : ℤ}
    (hS : d ∣ a + b)
    (hF : d ∣ seventhFactor a b) :
    d ∣ 7 * b ^ 6 := by
  have hprod :
      d ∣ (a + b) *
        (a ^ 5 - 2 * a ^ 4 * b + 3 * a ^ 3 * b ^ 2
          - 4 * a ^ 2 * b ^ 3 + 5 * a * b ^ 4
          - 6 * b ^ 5) :=
    dvd_mul_of_dvd_left hS _

  rw [← seventhFactor_sub_seven_mul_pow a b] at hprod

  have hdiff :=
    dvd_sub hF hprod

  simpa only [sub_sub_cancel] using hdiff

/-- For coprime inputs, a common divisor of the two factors divides 7. -/
theorem common_dvd_seventhFactor_dvd_seven
    {a b d : ℤ}
    (hab : IsCoprime a b)
    (hS : d ∣ a + b)
    (hF : d ∣ seventhFactor a b) :
    d ∣ 7 := by
  have hseven :=
    common_dvd_seventhFactor_dvd_seven_mul_pow hS hF

  obtain ⟨u, v, huv⟩ := hab
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hseven

  refine ⟨
    7 * (
      u ^ 6 * d ^ 5 * s ^ 6
      + 6 * u ^ 5 * d ^ 4 * s ^ 5 * (v - u) * b
      + 15 * u ^ 4 * d ^ 3 * s ^ 4 * (v - u) ^ 2 * b ^ 2
      + 20 * u ^ 3 * d ^ 2 * s ^ 3 * (v - u) ^ 3 * b ^ 3
      + 15 * u ^ 2 * d * s ^ 2 * (v - u) ^ 4 * b ^ 4
      + 6 * u * s * (v - u) ^ 5 * b ^ 5
    ) + (v - u) ^ 6 * t, ?_⟩

  calc
    (7 : ℤ) = 7 * (u * a + v * b) ^ 6 := by
      rw [huv]
      norm_num
    _ = 7 * (
          u ^ 6 * (a + b) ^ 6
          + 6 * u ^ 5 * (a + b) ^ 5 * (v - u) * b
          + 15 * u ^ 4 * (a + b) ^ 4 * (v - u) ^ 2 * b ^ 2
          + 20 * u ^ 3 * (a + b) ^ 3 * (v - u) ^ 3 * b ^ 3
          + 15 * u ^ 2 * (a + b) ^ 2 * (v - u) ^ 4 * b ^ 4
          + 6 * u * (a + b) * (v - u) ^ 5 * b ^ 5
        ) + (v - u) ^ 6 * (7 * b ^ 6) := by
      ring
    _ = d * (
        7 * (
          u ^ 6 * d ^ 5 * s ^ 6
          + 6 * u ^ 5 * d ^ 4 * s ^ 5 * (v - u) * b
          + 15 * u ^ 4 * d ^ 3 * s ^ 4 * (v - u) ^ 2 * b ^ 2
          + 20 * u ^ 3 * d ^ 2 * s ^ 3 * (v - u) ^ 3 * b ^ 3
          + 15 * u ^ 2 * d * s ^ 2 * (v - u) ^ 4 * b ^ 4
          + 6 * u * s * (v - u) ^ 5 * b ^ 5
        ) + (v - u) ^ 6 * t) := by
      rw [hs, ht]
      ring

/-- If 7 divides the first factor, it also divides the second. -/
theorem seven_dvd_seventhFactor_of_dvd_sum
    {a b : ℤ}
    (hS : (7 : ℤ) ∣ a + b) :
    (7 : ℤ) ∣ seventhFactor a b := by
  have hprod :
      (7 : ℤ) ∣ seventhFactor a b - 7 * b ^ 6 := by
    rw [seventhFactor_sub_seven_mul_pow]
    exact dvd_mul_of_dvd_left hS _

  have hseven : (7 : ℤ) ∣ 7 * b ^ 6 :=
    dvd_mul_right 7 (b ^ 6)

  have h := dvd_add hprod hseven
  simpa using h

/-- When a+b = 7t, extract one factor of 7 explicitly. -/
theorem seventhFactor_of_sum_eq_seven_mul
    {a b t : ℤ}
    (hS : a + b = 7 * t) :
    seventhFactor a b =
      7 * (
        16807 * t ^ 6
        - 16807 * t ^ 5 * b
        + 7203 * t ^ 4 * b ^ 2
        - 1715 * t ^ 3 * b ^ 3
        + 245 * t ^ 2 * b ^ 4
        - 21 * t * b ^ 5
        + b ^ 6) := by
  have ha : a = 7 * t - b := by
    linarith [hS]
  rw [ha]
  unfold seventhFactor
  ring

/-- Coprimality prevents 7 from dividing b when it divides a+b. -/
theorem seven_not_dvd_right_of_coprime_of_dvd_sum
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (7 : ℤ) ∣ a + b) :
    ¬ (7 : ℤ) ∣ b := by
  intro hb

  have ha : (7 : ℤ) ∣ a := by
    have h := dvd_sub hS hb
    simpa using h

  obtain ⟨u, v, huv⟩ := hab

  have hone : (7 : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add
      (dvd_mul_of_dvd_right ha u)
      (dvd_mul_of_dvd_right hb v)

  norm_num at hone

/-- For coprime inputs with 7 dividing their sum,
the second factor is not divisible by 49. -/
theorem fortyNine_not_dvd_seventhFactor
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (7 : ℤ) ∣ a + b) :
    ¬ (49 : ℤ) ∣ seventhFactor a b := by
  have hb :=
    seven_not_dvd_right_of_coprime_of_dvd_sum hab hS

  obtain ⟨t, ht⟩ := hS
  have hF := seventhFactor_of_sum_eq_seven_mul ht

  intro h49
  obtain ⟨k, hk⟩ := h49

  have hremaining :
      16807 * t ^ 6
        - 16807 * t ^ 5 * b
        + 7203 * t ^ 4 * b ^ 2
        - 1715 * t ^ 3 * b ^ 3
        + 245 * t ^ 2 * b ^ 4
        - 21 * t * b ^ 5
        + b ^ 6 = 7 * k := by
    nlinarith [hF, hk]

  have hbpow : (7 : ℤ) ∣ b ^ 6 := by
    refine ⟨
      k - (
        2401 * t ^ 6
        - 2401 * t ^ 5 * b
        + 1029 * t ^ 4 * b ^ 2
        - 245 * t ^ 3 * b ^ 3
        + 35 * t ^ 2 * b ^ 4
        - 3 * t * b ^ 5), ?_⟩
    nlinarith [hremaining]

  have hprime : Prime (7 : ℤ) := by
    norm_num

  exact hb (hprime.dvd_of_dvd_pow hbpow)

/-- Extract the exceptional prime from a seventh-power solution. -/
theorem seventh_solution_normalized_equation
    {a b c t F : ℤ}
    (hS : a + b = 7 * t)
    (hF : seventhFactor a b = 7 * F)
    (hc : a ^ 7 + b ^ 7 = c ^ 7) :
    ∃ k : ℤ, c = 7 * k ∧ t * F = 7 ^ 5 * k ^ 7 := by
  have hprime : Prime (7 : ℤ) := by
    norm_num

  have hproduct :
      (a + b) * seventhFactor a b = c ^ 7 := by
    calc
      (a + b) * seventhFactor a b = a ^ 7 + b ^ 7 :=
        (sum_seventh_powers_factorisation a b).symm
      _ = c ^ 7 := hc

  have hsumdvd : (7 : ℤ) ∣ a + b :=
    ⟨t, hS⟩

  have hcpow : (7 : ℤ) ∣ c ^ 7 := by
    rw [← hproduct]
    exact dvd_mul_of_dvd_left hsumdvd (seventhFactor a b)

  have hcdvd : (7 : ℤ) ∣ c :=
    hprime.dvd_of_dvd_pow hcpow

  obtain ⟨k, hk⟩ := hcdvd
  refine ⟨k, hk, ?_⟩

  rw [hS, hF, hk] at hproduct
  have hscaled :
      (49 : ℤ) * (t * F) =
        49 * (7 ^ 5 * k ^ 7) := by
    calc
      49 * (t * F) = (7 * t) * (7 * F) := by ring
      _ = (7 * k) ^ 7 := hproduct
      _ = 49 * (7 ^ 5 * k ^ 7) := by ring

  nlinarith [hscaled]

/-- A 7-free factor cannot absorb any powers of 7. -/
theorem seven_pow_dvd_left_of_mul_eq
    {t F z : ℤ}
    (hF : ¬ (7 : ℤ) ∣ F)
    (n : ℕ)
    (h : t * F = 7 ^ n * z) :
    (7 : ℤ) ^ n ∣ t := by
  have hprime : Prime (7 : ℤ) := by
    norm_num

  induction n generalizing t with
  | zero =>
      simp
  | succ n ih =>
      have hdiv : (7 : ℤ) ∣ t * F := by
        refine ⟨7 ^ n * z, ?_⟩
        rw [h, pow_succ]
        ring

      have ht : (7 : ℤ) ∣ t := by
        rcases hprime.dvd_mul.mp hdiv with ht | hfactor
        · exact ht
        · exact False.elim (hF hfactor)

      obtain ⟨u, hu⟩ := ht

      have hcancel : u * F = 7 ^ n * z := by
        rw [hu, pow_succ] at h
        nlinarith [h]

      obtain ⟨v, hv⟩ := ih hcancel

      refine ⟨v, ?_⟩
      rw [hu, hv, pow_succ]
      ring

/-- The normalized equation forces six factors of 7 into a+b. -/
theorem seven_pow_six_dvd_sum_of_normalized_equation
    {a b t F k : ℤ}
    (hS : a + b = 7 * t)
    (hF : ¬ (7 : ℤ) ∣ F)
    (h : t * F = 7 ^ 5 * k ^ 7) :
    (7 : ℤ) ^ 6 ∣ a + b := by
  have ht : (7 : ℤ) ^ 5 ∣ t :=
    seven_pow_dvd_left_of_mul_eq hF 5 h

  obtain ⟨u, hu⟩ := ht
  refine ⟨u, ?_⟩
  rw [hS, hu]
  ring

/-- If 7F is not divisible by 49, then F is 7-free. -/
theorem seven_free_of_scaled_not_dvd_fortyNine
    {Q F : ℤ}
    (hQ : Q = 7 * F)
    (h49 : ¬ (49 : ℤ) ∣ Q) :
    ¬ (7 : ℤ) ∣ F := by
  intro hF
  obtain ⟨u, hu⟩ := hF
  apply h49
  refine ⟨u, ?_⟩
  rw [hQ, hu]
  ring

/-- In the branch where 7 divides a+b, a coprime
seventh-power solution forces 7⁶ to divide a+b. -/
theorem seven_pow_six_dvd_sum_of_sum_seventh_powers
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (7 : ℤ) ∣ a + b)
    (hc : a ^ 7 + b ^ 7 = c ^ 7) :
    (7 : ℤ) ^ 6 ∣ a + b := by
  have h49 :=
    fortyNine_not_dvd_seventhFactor hab hS

  obtain ⟨t, ht⟩ := hS

  let F : ℤ :=
    16807 * t ^ 6
      - 16807 * t ^ 5 * b
      + 7203 * t ^ 4 * b ^ 2
      - 1715 * t ^ 3 * b ^ 3
      + 245 * t ^ 2 * b ^ 4
      - 21 * t * b ^ 5
      + b ^ 6

  have hQ : seventhFactor a b = 7 * F := by
    exact seventhFactor_of_sum_eq_seven_mul ht

  have hF : ¬ (7 : ℤ) ∣ F :=
    seven_free_of_scaled_not_dvd_fortyNine hQ h49

  obtain ⟨k, _hk, hnormalized⟩ :=
    seventh_solution_normalized_equation ht hQ hc

  exact seven_pow_six_dvd_sum_of_normalized_equation
    ht hF hnormalized

/-- A root of the alternating sextic has seventh power -1. -/
theorem seventh_sextic_root_pow
    {K : Type*} [CommRing K]
    {r : K}
    (h :
      r ^ 6 - r ^ 5 + r ^ 4 - r ^ 3
        + r ^ 2 - r + 1 = 0) :
    r ^ 7 = -1 := by
  linear_combination (r + 1) * h

/-- Such a root cannot be -1 when 7 is nonzero. -/
theorem seventh_sextic_root_ne_neg_one
    {K : Type*} [CommRing K]
    {r : K}
    (hseven : (7 : K) ≠ 0)
    (h :
      r ^ 6 - r ^ 5 + r ^ 4 - r ^ 3
        + r ^ 2 - r + 1 = 0) :
    r ≠ -1 := by
  intro hr
  rw [hr] at h
  have hzero : (7 : K) = 0 := by
    norm_num at h
    exact h
  exact hseven hzero

/-- These power conditions force multiplicative order exactly 14. -/
theorem orderOf_eq_fourteen_of_power_conditions
    {M : Type*} [Monoid M]
    {r : M}
    (hfourteen : r ^ 14 = 1)
    (htwo : r ^ 2 ≠ 1)
    (hseven : r ^ 7 ≠ 1) :
    orderOf r = 14 := by
  have hd : orderOf r ∣ 14 :=
    orderOf_dvd_of_pow_eq_one hfourteen

  have hbound : orderOf r ≤ 14 :=
    Nat.le_of_dvd (by decide : 0 < 14) hd

  have hcases :
      orderOf r = 1 ∨ orderOf r = 2 ∨
      orderOf r = 7 ∨ orderOf r = 14 := by
    interval_cases horder : orderOf r
    all_goals
      first
      | decide
      | norm_num at hd

  rcases hcases with h | h | h | h
  · have hdtwo : orderOf r ∣ 2 := by
      simpa only [h] using (by decide : (1 : ℕ) ∣ 2)
    exact False.elim
      (htwo (orderOf_dvd_iff_pow_eq_one.mp hdtwo))
  · have hdtwo : orderOf r ∣ 2 := by
      simpa only [h] using (by decide : (2 : ℕ) ∣ 2)
    exact False.elim
      (htwo (orderOf_dvd_iff_pow_eq_one.mp hdtwo))
  · have hdseven : orderOf r ∣ 7 := by
      simpa only [h] using (by decide : (7 : ℕ) ∣ 7)
    exact False.elim
      (hseven (orderOf_dvd_iff_pow_eq_one.mp hdseven))
  · exact h

/-- Over a field where 2 and 7 are nonzero, a root of the
alternating sextic has multiplicative order 14. -/
theorem seventh_sextic_root_order
    {K : Type*} [Field K]
    {r : K}
    (hseven : (7 : K) ≠ 0)
    (hnegone : (-1 : K) ≠ 1)
    (h :
      r ^ 6 - r ^ 5 + r ^ 4 - r ^ 3
        + r ^ 2 - r + 1 = 0) :
    orderOf r = 14 := by
  have hpow := seventh_sextic_root_pow h
  have hne := seventh_sextic_root_ne_neg_one hseven h

  have hfourteen : r ^ 14 = 1 := by
    calc
      r ^ 14 = (r ^ 7) ^ 2 := by ring
      _ = 1 := by rw [hpow]; norm_num

  have htwo : r ^ 2 ≠ 1 := by
    intro htwoeq
    have hprod : (r - 1) * (r + 1) = 0 := by
      linear_combination htwoeq

    rcases mul_eq_zero.mp hprod with hminus | hplus
    · have hr : r = 1 := sub_eq_zero.mp hminus
      rw [hr] at h
      norm_num at h
    · apply hne
      linear_combination hplus

  have hseventh : r ^ 7 ≠ 1 := by
    intro hone
    exact hnegone (hpow.symm.trans hone)

  exact orderOf_eq_fourteen_of_power_conditions
    hfourteen htwo hseventh

/-- A sextic root modulo a prime forces 14 to divide q-1. -/
theorem fourteen_dvd_pred_of_seventh_sextic_root
    {q : ℕ} [Fact q.Prime]
    {r : ZMod q}
    (hseven : (7 : ZMod q) ≠ 0)
    (hnegone : (-1 : ZMod q) ≠ 1)
    (h :
      r ^ 6 - r ^ 5 + r ^ 4 - r ^ 3
        + r ^ 2 - r + 1 = 0) :
    14 ∣ q - 1 := by
  have hr : r ≠ 0 := by
    intro hzero
    rw [hzero] at h
    norm_num at h

  have horder : orderOf r = 14 :=
    seventh_sextic_root_order hseven hnegone h

  have hd : orderOf r ∣ q - 1 :=
    ZMod.orderOf_dvd_card_sub_one hr

  simpa only [horder] using hd

/-- Dividing a homogeneous sextic by b⁶ produces the ratio equation. -/
theorem seventh_factor_ratio_root
    {K : Type*} [Field K]
    {a b : K}
    (hb : b ≠ 0)
    (hF :
      a ^ 6 - a ^ 5 * b + a ^ 4 * b ^ 2
        - a ^ 3 * b ^ 3 + a ^ 2 * b ^ 4
        - a * b ^ 5 + b ^ 6 = 0) :
    (a / b) ^ 6 - (a / b) ^ 5 + (a / b) ^ 4
      - (a / b) ^ 3 + (a / b) ^ 2 - a / b + 1 = 0 := by
  have hidentity :
      ((a / b) ^ 6 - (a / b) ^ 5 + (a / b) ^ 4
        - (a / b) ^ 3 + (a / b) ^ 2 - a / b + 1)
          * b ^ 6 =
        a ^ 6 - a ^ 5 * b + a ^ 4 * b ^ 2
          - a ^ 3 * b ^ 3 + a ^ 2 * b ^ 4
          - a * b ^ 5 + b ^ 6 := by
    field_simp [hb]

  rw [hF] at hidentity
  exact (mul_eq_zero.mp hidentity).resolve_right
    (pow_ne_zero 6 hb)

/-- A prime divisor of the second factor cannot divide b
when the inputs are coprime. -/
theorem prime_not_dvd_right_of_dvd_seventhFactor
    {a b q : ℤ}
    (hq : Prime q)
    (hab : IsCoprime a b)
    (hF : q ∣ seventhFactor a b) :
    ¬ q ∣ b := by
  intro hb

  have hidentity :
      seventhFactor a b - a ^ 6 =
        b * (
          -a ^ 5 + a ^ 4 * b - a ^ 3 * b ^ 2
            + a ^ 2 * b ^ 3 - a * b ^ 4 + b ^ 5) := by
    unfold seventhFactor
    ring

  have hdiff : q ∣ seventhFactor a b - a ^ 6 := by
    rw [hidentity]
    exact dvd_mul_of_dvd_left hb _

  have hapow : q ∣ a ^ 6 := by
    have h := dvd_sub hF hdiff
    simpa only [sub_sub_cancel] using h

  have ha : q ∣ a :=
    hq.dvd_of_dvd_pow hapow

  obtain ⟨u, v, huv⟩ := hab

  have hone : q ∣ 1 := by
    rw [← huv]
    exact dvd_add
      (dvd_mul_of_dvd_right ha u)
      (dvd_mul_of_dvd_right hb v)

  exact hq.not_isUnit (isUnit_of_dvd_one hone)

/-- A prime divisor of the second factor satisfies 14 ∣ q-1,
provided characteristics 2 and 7 are excluded. -/
theorem fourteen_dvd_pred_of_dvd_seventhFactor
    {a b : ℤ} {q : ℕ}
    (hq : q.Prime)
    (hab : IsCoprime a b)
    (hF : (q : ℤ) ∣ seventhFactor a b)
    (hseven : (7 : ZMod q) ≠ 0)
    (hnegone : (-1 : ZMod q) ≠ 1) :
    14 ∣ q - 1 := by
  let : Fact q.Prime := ⟨hq⟩

  have hqInt : Prime (q : ℤ) :=
    Nat.prime_iff_prime_int.mp hq

  have hbInt : ¬ (q : ℤ) ∣ b :=
    prime_not_dvd_right_of_dvd_seventhFactor hqInt hab hF

  have hb : (b : ZMod q) ≠ 0 := by
    intro hz
    have hdiv : (q : ℤ) ∣ b := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    exact hbInt hdiv

  have hcast : (seventhFactor a b : ZMod q) = 0 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]

  unfold seventhFactor at hcast
  push_cast at hcast

  have hroot :=
    seventh_factor_ratio_root hb hcast

  exact fourteen_dvd_pred_of_seventh_sextic_root
    hseven hnegone hroot

/-- After removing the exceptional powers of 7,
the remaining integer factors are coprime. -/
theorem seventh_integer_quotients_coprime
    {a b t F : ℤ}
    (hab : IsCoprime a b)
    (hS : a + b = 7 ^ 6 * t)
    (hQ : seventhFactor a b = 7 * F)
    (hF : ¬ (7 : ℤ) ∣ F) :
    IsCoprime t F := by
  have hprime : Prime (7 : ℤ) := by norm_num
  have hsevenCop : IsCoprime (7 : ℤ) F :=
    hprime.coprime_iff_not_dvd.mpr hF

  have hrel : IsRelPrime t F := by
    intro d hdt hdF

    have hdS : d ∣ a + b := by
      rw [hS]
      exact dvd_mul_of_dvd_right hdt _

    have hdQ : d ∣ seventhFactor a b := by
      rw [hQ]
      exact dvd_mul_of_dvd_right hdF 7

    have hdSeven : d ∣ (7 : ℤ) :=
      common_dvd_seventhFactor_dvd_seven hab hdS hdQ

    exact hsevenCop.isUnit_of_dvd' hdSeven hdF

  exact hrel.isCoprime

/-- Clean integer power extraction in the exceptional branch. -/
theorem seventh_integer_power_extraction_of_dvd_sum
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (7 : ℤ) ∣ a + b)
    (hc : a ^ 7 + b ^ 7 = c ^ 7) :
    ∃ u v : ℤ,
      a + b = 7 ^ 6 * u ^ 7 ∧
      seventhFactor a b = 7 * v ^ 7 ∧
      c = 7 * (u * v) := by
  have h49 := fortyNine_not_dvd_seventhFactor hab hS

  obtain ⟨s, hs⟩ := hS

  let F : ℤ :=
    16807 * s ^ 6
      - 16807 * s ^ 5 * b
      + 7203 * s ^ 4 * b ^ 2
      - 1715 * s ^ 3 * b ^ 3
      + 245 * s ^ 2 * b ^ 4
      - 21 * s * b ^ 5
      + b ^ 6

  have hQ : seventhFactor a b = 7 * F :=
    seventhFactor_of_sum_eq_seven_mul hs

  have hF : ¬ (7 : ℤ) ∣ F :=
    seven_free_of_scaled_not_dvd_fortyNine hQ h49

  obtain ⟨k, hk, hnormalized⟩ :=
    seventh_solution_normalized_equation hs hQ hc

  have hsFive : (7 : ℤ) ^ 5 ∣ s :=
    seven_pow_dvd_left_of_mul_eq hF 5 hnormalized

  obtain ⟨t, ht⟩ := hsFive

  have hsum : a + b = 7 ^ 6 * t := by
    rw [hs, ht]
    ring

  have hproduct : t * F = k ^ 7 := by
    rw [ht] at hnormalized
    nlinarith [hnormalized]

  have hcop : IsCoprime t F :=
    seventh_integer_quotients_coprime hab hsum hQ hF

  obtain ⟨u, hu⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left
      hcop (by decide : Odd (7 : ℕ)) hproduct

  obtain ⟨v, hv⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_right
      hcop (by decide : Odd (7 : ℕ)) hproduct

  have hpowers : (u * v) ^ 7 = k ^ 7 := by
    rw [mul_pow, ← hu, ← hv]
    exact hproduct

  have huv : u * v = k :=
    (by decide : Odd (7 : ℕ)).pow_injective hpowers

  refine ⟨u, v, ?_, ?_, ?_⟩
  · simpa only [hu] using hsum
  · simpa only [hv] using hQ
  · simpa only [← huv] using hk

/-- Three linear factors satisfy a cancellation identity. -/
theorem three_cyclotomic_factors_identity
    {R : Type*} [CommRing R]
    (x y eta0 eta1 eta2 : R) :
    (eta2 - eta0) * (x + eta1 * y)
      + (eta0 - eta1) * (x + eta2 * y) =
        (eta2 - eta1) * (x + eta0 * y) := by
  ring

end Hire
