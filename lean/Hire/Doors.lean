/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# The 3-free door of an odd prime

Elementary formalization of the χ₃ door package (hire graph).

* `chi3` — non-principal character mod 3 as `ℕ → ℤ`
* `m0 p` — unique **3-free** even neighbour for odd primes `p ≠ 3`
* `m1 p` — other face (divisible by 6)

Public voice: no ζ; doors and hire set only.
-/

namespace Hire

/-- Non-principal character mod 3: `+1` if `n ≡ 1 [MOD 3]`, `-1` if `n ≡ 2`, else `0`. -/
def chi3 (n : ℕ) : ℤ :=
  match n % 3 with
  | 1 => 1
  | 2 => -1
  | _ => 0

@[simp] lemma chi3_of_mod_one {n : ℕ} (h : n % 3 = 1) : chi3 n = 1 := by simp [chi3, h]
@[simp] lemma chi3_of_mod_two {n : ℕ} (h : n % 3 = 2) : chi3 n = -1 := by simp [chi3, h]
@[simp] lemma chi3_of_mod_zero {n : ℕ} (h : n % 3 = 0) : chi3 n = 0 := by simp [chi3, h]

lemma chi3_eq_zero_iff_dvd_three (n : ℕ) : chi3 n = 0 ↔ 3 ∣ n := by
  constructor
  · intro h
    rw [Nat.dvd_iff_mod_eq_zero]
    have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
    match hmod : n % 3 with
    | 0 => rfl
    | 1 => simp [chi3, hmod] at h
    | 2 => simp [chi3, hmod] at h
    | k + 3 =>
        have : n % 3 < 3 := hlt
        omega
  · intro h
    have : n % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    simp [chi3, this]

/-- 3-free door. For odd primes `p ≠ 3` this equals `p ± 1`. -/
def m0 (p : ℕ) : ℕ := if p % 3 = 1 then p + 1 else p - 1

/-- Other face. For odd primes `p ≠ 3` this is divisible by 6. -/
def m1 (p : ℕ) : ℕ := if p % 3 = 1 then p - 1 else p + 1

lemma m0_of_mod_one {p : ℕ} (h : p % 3 = 1) : m0 p = p + 1 := by simp [m0, h]
lemma m0_of_mod_two {p : ℕ} (h : p % 3 = 2) : m0 p = p - 1 := by simp [m0, h]
lemma m1_of_mod_one {p : ℕ} (h : p % 3 = 1) : m1 p = p - 1 := by simp [m1, h]
lemma m1_of_mod_two {p : ℕ} (h : p % 3 = 2) : m1 p = p + 1 := by simp [m1, h]

lemma not_three_dvd_of_prime_ne_three {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) : ¬ 3 ∣ p := by
  intro hd
  rcases hp.eq_one_or_self_of_dvd 3 hd with h | h
  · exact absurd h (by decide)
  · exact h3 h.symm

lemma prime_ne_three_mod_eq_one_or_two {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have hne : ¬ 3 ∣ p := not_three_dvd_of_prime_ne_three hp h3
  have hmod0 : p % 3 ≠ 0 := fun h0 => hne (Nat.dvd_iff_mod_eq_zero.mpr h0)
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  match h : p % 3 with
  | 0 => exact absurd h hmod0
  | 1 => exact Or.inl rfl
  | 2 => exact Or.inr rfl
  | k + 3 => omega

/-- **3-free:** if `p` is prime and `p ≠ 3`, then `3 ∤ m0 p`. -/
theorem three_not_dvd_m0 {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) : ¬ 3 ∣ m0 p := by
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with h | h
  · rw [m0_of_mod_one h, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h]
    decide
  · have : 2 ≤ p := hp.two_le
    rw [m0_of_mod_two h, Nat.dvd_iff_mod_eq_zero]
    have : (p - 1) % 3 = 1 := by omega
    simp [this]

/-- Odd prime `p ≠ 3` ⇒ `m0 p` is even. -/
theorem even_m0 {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) : Even (m0 p) := by
  rw [even_iff_two_dvd]
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with h | h
  · rw [m0_of_mod_one h]
    exact Nat.dvd_of_mod_eq_zero (by
      have := Nat.odd_iff.mp hodd
      omega)
  · rw [m0_of_mod_two h]
    have : 1 ≤ p := Nat.le_of_lt hp.one_lt
    exact Nat.dvd_of_mod_eq_zero (by
      have := Nat.odd_iff.mp hodd
      omega)

/-- An odd divisor of the door of an odd prime `p ≠ 3` brings the factor `2`. -/
theorem two_mul_dvd_m0 {p q : ℕ} (hp : p.Prime) (hodd : Odd p) (hp3 : p ≠ 3)
    (hq : Odd q) (hd : q ∣ m0 p) : 2 * q ∣ m0 p :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd hq.coprime_two_left
    (even_iff_two_dvd.mp (even_m0 hp hodd hp3)) hd

/-- Other face divisible by 3. -/
theorem three_dvd_m1 {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) : 3 ∣ m1 p := by
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with h | h
  · have hp2 : 2 ≤ p := hp.two_le
    simp [m1, h, Nat.dvd_iff_mod_eq_zero]
    omega
  · simp [m1, h, Nat.dvd_iff_mod_eq_zero, Nat.add_mod]

theorem even_m1 {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) : Even (m1 p) := by
  rw [even_iff_two_dvd]
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with h | h
  · have : 1 ≤ p := Nat.le_of_lt hp.one_lt
    rw [m1_of_mod_one h]
    exact Nat.dvd_of_mod_eq_zero (by
      have := Nat.odd_iff.mp hodd
      omega)
  · rw [m1_of_mod_two h]
    exact Nat.dvd_of_mod_eq_zero (by
      have := Nat.odd_iff.mp hodd
      omega)

/-- Other face divisible by 6. -/
theorem six_dvd_m1 {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) : 6 ∣ m1 p := by
  have h2 : 2 ∣ m1 p := even_iff_two_dvd.mp (even_m1 hp hodd h3)
  have h3d : 3 ∣ m1 p := three_dvd_m1 hp h3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) h2 h3d

/-- Swallow construction: if `r = 2^k * A + 1` is prime and `r ≡ 2 [MOD 3]`,
then `m0 r = 2^k * A`. Door arithmetic only; census purity is separate. -/
theorem m0_of_two_pow_mul_add_one {r A k : ℕ} (_hr : Nat.Prime r)
    (_hA : Odd A) (heq : r = 2 ^ k * A + 1) (hmod : r % 3 = 2) :
    m0 r = 2 ^ k * A := by
  rw [m0_of_mod_two hmod, heq, Nat.add_sub_cancel]

/-- Cube-minus-square is the door times a square when `p ≡ 2 [MOD 3]`. -/
theorem cube_sub_sq_eq_sq_mul_m0 {p : ℕ} (hmod : p % 3 = 2) :
    p ^ 3 - p ^ 2 = p ^ 2 * m0 p := by
  have : 1 ≤ p := by omega
  rw [m0_of_mod_two hmod]
  calc
    p ^ 3 - p ^ 2 = p ^ 2 * p - p ^ 2 := by rw [Nat.pow_succ, Nat.mul_comm]
    _ = p ^ 2 * (p - 1) := (Nat.mul_sub_one (p ^ 2) p).symm

/-- Poster checks after Lemma 1. -/
example : m0 11 = 10 := by native_decide
example : m0 13 = 14 := by native_decide
example : m1 11 = 12 := by native_decide
example : m1 13 = 12 := by native_decide
example : chi3 11 = -1 := by native_decide
example : chi3 13 = 1 := by native_decide


/-- Mid-gap identity for the 3-free door: the reciprocal of `m0 p` sits
halfway between the face reciprocals, offset by `-χ₃(p)/(p² - 1)`. -/
theorem mid_gap_m0 {p : ℕ} (hp : p.Prime) (_hodd : Odd p) (h3 : p ≠ 3) :
    (m0 p : ℚ)⁻¹ - (1 / 2 : ℚ) * (((p : ℚ) - 1)⁻¹ + ((p : ℚ) + 1)⁻¹) =
      - (chi3 p : ℚ) / ((p : ℚ) ^ 2 - 1) := by
  have hp_ge : 1 ≤ p := Nat.le_of_lt hp.one_lt
  have hpm1 : ((p : ℚ) - 1) ≠ 0 := sub_ne_zero.2 (ne_of_gt (Nat.one_lt_cast.2 hp.one_lt))
  have hpp1 : ((p : ℚ) + 1) ≠ 0 := by positivity
  have hden : ((p : ℚ) ^ 2 - 1) ≠ 0 := by
    rw [show (p : ℚ) ^ 2 - 1 = ((p : ℚ) - 1) * ((p : ℚ) + 1) by ring]
    exact mul_ne_zero hpm1 hpp1
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with hmod | hmod
  · -- p ≡ 1 [MOD 3]: m0 = p+1, χ₃ = 1
    rw [m0_of_mod_one hmod, chi3_of_mod_one hmod]
    push_cast
    have : ((p : ℚ) + 1)⁻¹ - (1 / 2 : ℚ) * (((p : ℚ) - 1)⁻¹ + ((p : ℚ) + 1)⁻¹) =
        - (1 : ℚ) / ((p : ℚ) ^ 2 - 1) := by
      field_simp [hpm1, hpp1, hden]
      ring
    simpa using this
  · -- p ≡ 2 [MOD 3]: m0 = p-1, χ₃ = -1
    rw [m0_of_mod_two hmod, chi3_of_mod_two hmod, Nat.cast_sub hp_ge]
    have : ((p : ℚ) - 1)⁻¹ - (1 / 2 : ℚ) * (((p : ℚ) - 1)⁻¹ + ((p : ℚ) + 1)⁻¹) =
        - (-1 : ℚ) / ((p : ℚ) ^ 2 - 1) := by
      field_simp [hpm1, hpp1, hden]
      ring
    simpa using this

/-- Helping identity: `(p / 3) = χ₃(p)` for primes `p ≠ 3`. -/
theorem chi3_eq_legendreSym_three {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    chi3 p = legendreSym 3 p := by
  rcases prime_ne_three_mod_eq_one_or_two hp h3 with hmod | hmod
  · -- p ≡ 1 → (p/3) = (1/3) = 1
    rw [chi3_of_mod_one hmod]
    have hmodZ : (p : ℤ) % 3 = 1 := by exact_mod_cast hmod
    calc
      (1 : ℤ) = legendreSym 3 (1 : ℤ) := (legendreSym.at_one 3).symm
      _ = legendreSym 3 ((p : ℤ) % 3) := by rw [hmodZ]
      _ = legendreSym 3 p := (legendreSym.mod (p := 3) (p : ℤ)).symm
  · -- p ≡ 2 → (p/3) = (2/3) = (−1/3) = χ₄(3) = -1
    rw [chi3_of_mod_two hmod]
    have hmodZ : (p : ℤ) % 3 = 2 := by exact_mod_cast hmod
    have h2 : legendreSym 3 (2 : ℤ) = -1 := by
      have hcong : legendreSym 3 (2 : ℤ) = legendreSym 3 (-1) := by
        have h : ((2 : ℤ) % (3 : ℤ)) = ((-1 : ℤ) % (3 : ℤ)) := by decide
        calc
          legendreSym 3 (2 : ℤ) = legendreSym 3 ((2 : ℤ) % 3) := legendreSym.mod (p := 3) 2
          _ = legendreSym 3 ((-1 : ℤ) % 3) := by rw [h]
          _ = legendreSym 3 (-1) := (legendreSym.mod (p := 3) (-1)).symm
      rw [hcong, legendreSym.at_neg_one (by decide : (3 : ℕ) ≠ 2)]
      exact ZMod.χ₄_nat_three_mod_four (by decide)
    calc
      (-1 : ℤ) = legendreSym 3 (2 : ℤ) := h2.symm
      _ = legendreSym 3 ((p : ℤ) % 3) := by rw [hmodZ]
      _ = legendreSym 3 p := (legendreSym.mod (p := 3) (p : ℤ)).symm

/-- Torus identity: `χ₃(p) = (−3 / p)` for odd primes `p ≠ 3`. -/
theorem chi3_eq_legendreSym_neg_three {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) :
    chi3 p = @legendreSym p ⟨hp⟩ (-3) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h; subst h; exact (by decide : ¬ Odd 2) hodd
  -- (−3 / p) = χ₄(p) · (3 / p)
  have hneg : legendreSym p (-3) = ZMod.χ₄ p * legendreSym p 3 :=
    legendreSym.at_neg hp2 3
  -- QR: instantiate modulus-first as 3, argument as p
  -- legendreSym p 3 = (−1)^(3/2 · p/2) · legendreSym 3 p
  have hqr : legendreSym p 3 =
      (-1 : ℤ) ^ ((3 : ℕ) / 2 * (p / 2)) * legendreSym 3 p := by
    simpa using
      (legendreSym.quadratic_reciprocity' (p := 3) (q := p)
        (by decide : (3 : ℕ) ≠ 2) hp2)
  have hpow : (-1 : ℤ) ^ ((3 : ℕ) / 2 * (p / 2)) = (-1 : ℤ) ^ (p / 2) := by
    have : (3 : ℕ) / 2 = 1 := by decide
    simp [this]
  have hchi4 : ZMod.χ₄ p = (-1 : ℤ) ^ (p / 2) :=
    ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd)
  have hsq : ZMod.χ₄ p * ZMod.χ₄ p = 1 := by
    rw [hchi4, ← pow_add, ← two_mul, pow_mul]
    simp
  calc
    chi3 p = legendreSym 3 p := chi3_eq_legendreSym_three hp h3
    _ = ZMod.χ₄ p * ZMod.χ₄ p * legendreSym 3 p := by rw [hsq, one_mul]
    _ = ZMod.χ₄ p * (ZMod.χ₄ p * legendreSym 3 p) := by ring
    _ = ZMod.χ₄ p * legendreSym p 3 := by
        rw [hqr, hpow, hchi4]
    _ = legendreSym p (-3) := hneg.symm

end Hire
