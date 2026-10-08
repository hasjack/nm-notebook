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

/-- The quartic table defines a Dirichlet character modulo 5. -/
noncomputable def quarticCharacter5 :
    DirichletCharacter ℂ 5 where
  toFun z := quarticFive z.val
  map_one' := by
    change quarticFive 1 = 1
    norm_num [quarticFive]
  map_mul' := by
    intro a b
    change
      quarticFive ((a.val * b.val) % 5) =
        quarticFive a.val * quarticFive b.val
    set r := a.val with hr
    set s := b.val with hs
    have hrlt : r < 5 := a.val_lt
    have hslt : s < 5 := b.val_lt
    interval_cases r <;> interval_cases s <;>
      norm_num [quarticFive, ← hr, ← hs,
        Complex.I_mul_I]
  map_nonunit' := by
    intro z hz
    have hc : ¬ Nat.Coprime z.val 5 := by
      intro h
      apply hz
      have hu : IsUnit (z.val : ZMod 5) :=
        (ZMod.isUnit_iff_coprime z.val 5).mpr h
      simpa only [ZMod.natCast_zmod_val] using hu
    set r := z.val with hr
    have hrlt : r < 5 := z.val_lt
    interval_cases r <;>
      norm_num [quarticFive, ← hr] at *

/-- Reduction modulo 5 preserves the quartic table. -/
theorem quarticFive_mod_five (n : ℕ) :
    quarticFive (n % 5) = quarticFive n := by
  simp [quarticFive]

/-- The bundled character reproduces the original table. -/
theorem quarticCharacter5_apply_nat (n : ℕ) :
    quarticCharacter5 (n : ZMod 5) = quarticFive n := by
  change quarticFive (n : ZMod 5).val = quarticFive n
  rw [ZMod.val_natCast, quarticFive_mod_five]

/-- The quartic character is nonprincipal: its value at 2 is i. -/
theorem quarticCharacter5_ne_one :
    quarticCharacter5 ≠ 1 := by
  intro h
  have hu : IsUnit (2 : ZMod 5) :=
    (ZMod.isUnit_iff_coprime 2 5).mpr (by norm_num)
  have hv :
      quarticCharacter5 (2 : ZMod 5) = Complex.I := by
    simpa [quarticFive] using quarticCharacter5_apply_nat 2
  have he := congrArg
    (fun χ : DirichletCharacter ℂ 5 =>
      χ (2 : ZMod 5)) h
  rw [hv, MulChar.one_apply hu] at he
  have hre := congrArg Complex.re he
  norm_num at hre

/-- Its analytically continued L-function does not vanish at 1. -/
theorem quarticCharacter5_LFunction_one_ne_zero :
    quarticCharacter5.LFunction 1 ≠ 0 := by
  exact DirichletCharacter.LFunction_apply_one_ne_zero
    quarticCharacter5_ne_one

/-- Its analytically continued L-function is differentiable everywhere. -/
theorem quarticCharacter5_LFunction_differentiable :
    Differentiable ℂ quarticCharacter5.LFunction := by
  exact DirichletCharacter.differentiable_LFunction
    quarticCharacter5_ne_one

/-- The quartic character lifted from modulus 5 to modulus 15. -/
noncomputable def companionCharacter15 :
    DirichletCharacter ℂ 15 :=
  DirichletCharacter.changeLevel
    (show 5 ∣ 15 by norm_num) quarticCharacter5

/-- Lifting to modulus 15 removes the quartic Euler factor at 3. -/
theorem companionCharacter15_LSeries_eq
    {s : ℂ} (hs : 1 < s.re) :
    LSeries
        (fun n => companionCharacter15 (n : ZMod 15)) s =
      (1 + Complex.I * (3 : ℂ) ^ (-s)) *
        LSeries
          (fun n => quarticCharacter5 (n : ZMod 5)) s := by
  have hpf : Nat.primeFactors 15 = {3, 5} := by
    ext p
    simp only [Nat.mem_primeFactors,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hd, _⟩
      have hle : p ≤ 15 :=
        Nat.le_of_dvd (by norm_num : 0 < 15) hd
      interval_cases p <;> norm_num at *
    · intro hp
      rcases hp with rfl | rfl <;> norm_num
  have h :=
    DirichletCharacter.LSeries_changeLevel
      (show 5 ∣ 15 by norm_num) quarticCharacter5 hs
  change
    LSeries
        (fun n => companionCharacter15 (n : ZMod 15)) s =
      LSeries
          (fun n => quarticCharacter5 (n : ZMod 5)) s *
        ∏ p ∈ Nat.primeFactors 15,
          (1 - quarticCharacter5 (p : ZMod 5) *
            (p : ℂ) ^ (-s)) at h
  simpa [hpf, quarticCharacter5_apply_nat,
    quarticFive, mul_comm] using h

/-- The same identity holds for the continued L-functions everywhere. -/
theorem companionCharacter15_LFunction_eq (s : ℂ) :
    companionCharacter15.LFunction s =
      (1 + Complex.I * (3 : ℂ) ^ (-s)) *
        quarticCharacter5.LFunction s := by
  have hpf : Nat.primeFactors 15 = {3, 5} := by
    ext p
    simp only [Nat.mem_primeFactors,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hd, _⟩
      have hle : p ≤ 15 :=
        Nat.le_of_dvd (by norm_num : 0 < 15) hd
      interval_cases p <;> norm_num at *
    · intro hp
      rcases hp with rfl | rfl <;> norm_num
  have h :=
    DirichletCharacter.LFunction_changeLevel
      (show 5 ∣ 15 by norm_num) quarticCharacter5
      (s := s) (Or.inl quarticCharacter5_ne_one)
  change
    companionCharacter15.LFunction s =
      quarticCharacter5.LFunction s *
        ∏ p ∈ Nat.primeFactors 15,
          (1 - quarticCharacter5 (p : ZMod 5) *
            (p : ℂ) ^ (-s)) at h
  simpa [hpf, quarticCharacter5_apply_nat,
    quarticFive, mul_comm] using h

/-- The bundled lift reproduces our companion table. -/
theorem companionCharacter15_apply_nat (n : ℕ) :
    companionCharacter15 (n : ZMod 15) = companion15 n := by
  classical
  have h3 : n % 3 = (n % 15) % 3 := by omega
  have h5 : n % 5 = (n % 15) % 5 := by omega
  have hlt : n % 15 < 15 := Nat.mod_lt n (by norm_num)

  by_cases hu : IsUnit (n : ZMod 15)
  · have he :
        companionCharacter15 (n : ZMod 15) =
          quarticFive n := by
      unfold companionCharacter15
      rw [← hu.unit_spec,
        DirichletCharacter.changeLevel_eq_cast_of_dvd]
      rw [hu.unit_spec,
        ZMod.cast_natCast (show 5 ∣ 15 by norm_num)]
      exact quarticCharacter5_apply_nat n

    have hc : Nat.Coprime n 15 :=
      (ZMod.isUnit_iff_coprime n 15).mp hu
    have hg : Nat.gcd 15 (n % 15) = 1 := by
      calc
        Nat.gcd 15 (n % 15) =
            Nat.gcd (n % 15) 15 := Nat.gcd_comm _ _
        _ = Nat.gcd 15 n := (Nat.gcd_rec 15 n).symm
        _ = Nat.gcd n 15 := Nat.gcd_comm _ _
        _ = 1 := hc.gcd_eq_one

    rw [he, companion15_eq_quarticFive]
    interval_cases h : n % 15 <;>
      norm_num [h] at hg <;>
      simp [h3, quarticFive]

  · rw [MulChar.map_nonunit companionCharacter15 hu]
    have hc : ¬ Nat.Coprime n 15 := by
      intro hc
      exact hu ((ZMod.isUnit_iff_coprime n 15).mpr hc)
    have hg : Nat.gcd 15 (n % 15) ≠ 1 := by
      intro h
      apply hc
      apply Nat.coprime_iff_gcd_eq_one.mpr
      calc
        Nat.gcd n 15 =
            Nat.gcd 15 n := Nat.gcd_comm _ _
        _ = Nat.gcd (n % 15) 15 := Nat.gcd_rec 15 n
        _ = Nat.gcd 15 (n % 15) := Nat.gcd_comm _ _
        _ = 1 := h

    rw [companion15_eq_quarticFive]
    interval_cases h : n % 15 <;>
      norm_num [h] at hg <;>
      norm_num [h3, h5, h, quarticFive]

/-- The original companion table has the Euler-factor removal identity. -/
theorem companion15_LSeries_eq
    {s : ℂ} (hs : 1 < s.re) :
    LSeries companion15 s =
      (1 + Complex.I * (3 : ℂ) ^ (-s)) *
        LSeries quarticFive s := by
  simpa only [companionCharacter15_apply_nat,
    quarticCharacter5_apply_nat] using
    companionCharacter15_LSeries_eq hs

/-- The table's convergent series agrees with the continued expression. -/
theorem companion15_LSeries_eq_LFunction
    {s : ℂ} (hs : 1 < s.re) :
    LSeries companion15 s =
      (1 + Complex.I * (3 : ℂ) ^ (-s)) *
        quarticCharacter5.LFunction s := by
  rw [companion15_LSeries_eq hs]
  have h :
      LSeries quarticFive s =
        quarticCharacter5.LFunction s := by
    simpa only [quarticCharacter5_apply_nat] using
      (DirichletCharacter.LFunction_eq_LSeries
        quarticCharacter5 hs).symm
  rw [h]

end HireCharacterReadout
