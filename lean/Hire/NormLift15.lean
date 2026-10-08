import Hire.CharacterObjects

namespace HireCharacterReadout

/-- The character value at a square is the square of its value. -/
theorem complex15_apply_square (n : ℕ) :
    complex15 (n * n) = complex15 n ^ 2 := by
  rw [← complexCharacter15_apply_nat,
    Nat.cast_mul, map_mul,
    complexCharacter15_apply_nat]
  simp only [pow_two]

/-- On the split branch, the splitting sign disappears. -/
theorem complex15_of_split
    {n : ℕ} (hn : n % 3 = 1) :
    complex15 n = quarticFive n := by
  simp [complex15, Hire.chi3, hn]

/-- On the inert branch, the splitting sign is negative. -/
theorem complex15_of_inert
    {n : ℕ} (hn : n % 3 = 2) :
    complex15 n = -quarticFive n := by
  simp [complex15, Hire.chi3, hn]

/-- At an inert prime, the norm-square removes the splitting sign. -/
theorem complex15_square_of_inert
    {n : ℕ} (hn : n % 3 = 2) :
    complex15 (n * n) = quarticFive n ^ 2 := by
  rw [complex15_apply_square, complex15_of_inert hn]
  ring

/--
The product of two rational local factors.
Here a is the character value, ε the splitting sign,
and x stands for p⁻ˢ.
-/
noncomputable def pairedLocalFactor15
    (a ε x : ℂ) : ℂ :=
  (1 - a * x)⁻¹ * (1 - (a * ε) * x)⁻¹

/-- Split primes contribute two identical local factors. -/
theorem pairedLocalFactor15_split (a x : ℂ) :
    pairedLocalFactor15 a 1 x =
      ((1 - a * x)⁻¹) ^ 2 := by
  simp [pairedLocalFactor15, pow_two]

/-- Inert primes contribute one factor at the squared norm. -/
theorem pairedLocalFactor15_inert (a x : ℂ) :
    pairedLocalFactor15 a (-1) x =
      (1 - a ^ 2 * x ^ 2)⁻¹ := by
  unfold pairedLocalFactor15
  rw [← mul_inv]
  congr 1
  ring

/-- The companion character table obtained by twisting by χ₃. -/
noncomputable def companion15 (n : ℕ) : ℂ :=
  complex15 n * (Hire.chi3 n : ℂ)

/-- Twisting again removes the splitting sign away from multiples of 3. -/
theorem companion15_eq_quarticFive (n : ℕ) :
    companion15 n =
      if n % 3 = 0 then 0 else quarticFive n := by
  have hn : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 3 <;>
    simp [companion15, complex15, Hire.chi3, h]

/-- The companion vanishes on multiples of 3. -/
theorem companion15_of_mod_three_zero
    {n : ℕ} (hn : n % 3 = 0) :
    companion15 n = 0 := by
  simp [companion15_eq_quarticFive, hn]

/-- Elsewhere, the companion agrees with the quartic character modulo 5. -/
theorem companion15_of_mod_three_ne_zero
    {n : ℕ} (hn : n % 3 ≠ 0) :
    companion15 n = quarticFive n := by
  simp [companion15_eq_quarticFive, hn]

/-- On split residues the companion equals the original character. -/
theorem companion15_of_split
    {n : ℕ} (hn : n % 3 = 1) :
    companion15 n = complex15 n := by
  simp [companion15, Hire.chi3, hn]

/-- On inert residues the companion negates the original character. -/
theorem companion15_of_inert
    {n : ℕ} (hn : n % 3 = 2) :
    companion15 n = -complex15 n := by
  simp [companion15, Hire.chi3, hn]

end HireCharacterReadout
