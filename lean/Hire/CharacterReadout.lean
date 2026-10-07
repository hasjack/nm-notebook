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

end HireCharacterReadout
