/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett

Exploratory stub only (FLT × two-door cheap-kill). Not part of the Hire.lean import
barrel. Papers frozen; no Mathlib PR from this file.
-/
import Hire.Doors
import Mathlib.Data.Nat.Prime.Basic

namespace Hire

/-- Sophie Germain–type auxiliary: odd prime `r = 2kℓ+1`. -/
def IsGermainAux (ℓ r : ℕ) : Prop :=
  r.Prime ∧ ∃ k : ℕ, k ≥ 1 ∧ r = 2 * k * ℓ + 1

/--
Door-of-residue (elementary from `m0`/`m1` defs):
if `ℓ ∣ r−1` and `r` is an odd prime `≠ 3`, then
`ℓ ∣ m0 r ↔ r % 3 = 2` and `ℓ ∣ m1 r ↔ r % 3 = 1`.

Python cheap-kill (`drafts/flt_two_door_cheap_kill.py`) verified this on all Germain
auxiliaries with `r ≤ 2e6` for `ℓ ∈ {5,7,11,13,17,19,23,29,31}` (0 mismatches).
-/
theorem doorOfResidue {ℓ r : ℕ} (hℓ : 2 < ℓ) (hr : r.Prime) (h3 : r ≠ 3)
    (hdvd : ℓ ∣ r - 1) :
    (ℓ ∣ m0 r ↔ r % 3 = 2) ∧ (ℓ ∣ m1 r ↔ r % 3 = 1) := by
  have hmod : r % 3 = 1 ∨ r % 3 = 2 := prime_ne_three_mod_eq_one_or_two hr h3
  have hr1 : 1 ≤ r := Nat.le_of_lt hr.one_lt
  -- ℓ odd (since ℓ > 2); used to separate m0/m1 = (r±1)
  have ℓ_ne_two : ℓ ≠ 2 := ne_of_gt hℓ
  rcases hmod with h1 | h2
  · -- r ≡ 1 (mod 3): m0 = r+1, m1 = r-1
    have hm0 : m0 r = r + 1 := m0_of_mod_one h1
    have hm1 : m1 r = r - 1 := m1_of_mod_one h1
    constructor
    · -- ℓ ∣ m0 ↔ False (since ↔ r%3=2 which is false)
      constructor
      · intro hdiv
        -- ℓ ∣ (r+1) and ℓ ∣ (r-1) ⇒ ℓ ∣ 2
        have hrm1 : ℓ ∣ r - 1 := hdvd
        have : ℓ ∣ (r + 1) - (r - 1) := by
          simpa [hm0] using Nat.dvd_sub hdiv (by simpa [hm1] using hrm1)
        -- (r+1)-(r-1)=2
        have eq2 : (r + 1) - (r - 1) = 2 := by omega
        rw [eq2] at this
        -- ℓ ∣ 2, ℓ > 2 ⇒ contradiction
        have : ℓ ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) this
        omega
      · intro h
        omega  -- r%3=2 contradicts h1
    · -- ℓ ∣ m1 ↔ True
      constructor
      · intro _; exact h1
      · intro _; simpa [hm1] using hdvd
  · -- r ≡ 2 (mod 3): m0 = r-1, m1 = r+1
    have hm0 : m0 r = r - 1 := m0_of_mod_two h2
    have hm1 : m1 r = r + 1 := m1_of_mod_two h2
    constructor
    · constructor
      · intro _; exact h2
      · intro _; simpa [hm0] using hdvd
    · constructor
      · intro hdiv
        have hrm1 : ℓ ∣ r - 1 := hdvd
        have : ℓ ∣ (r + 1) - (r - 1) := by
          simpa [hm1] using Nat.dvd_sub hdiv (by simpa [hm0] using hrm1)
        have eq2 : (r + 1) - (r - 1) = 2 := by omega
        rw [eq2] at this
        have : ℓ ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) this
        omega
      · intro h
        omega

/-- Germain auxiliaries satisfy `ℓ ∣ r−1` by construction. -/
theorem germainAux_dvd_sub_one {ℓ r : ℕ} (h : IsGermainAux ℓ r) : ℓ ∣ r - 1 := by
  rcases h with ⟨_, ⟨k, hk, hr⟩⟩
  -- r - 1 = 2 * k * ℓ
  have : r - 1 = 2 * k * ℓ := by
    have : r = 2 * k * ℓ + 1 := hr
    omega
  exact ⟨2 * k, by rw [this, Nat.mul_comm]⟩

end Hire
