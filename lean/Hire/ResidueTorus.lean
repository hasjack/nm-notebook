import Mathlib
import Hire.Doors

namespace Hire
namespace ResidueTorus

/-- A prime other than 5 cannot be divisible by 5. -/
theorem five_not_dvd_prime
    {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) :
    ¬ 5 ∣ p := by
  intro hd
  rcases hp.eq_one_or_self_of_dvd 5 hd with h | h
  · norm_num at h
  · exact h5 h.symm

/-- For the p+1 door, product residue 1 is forbidden. -/
theorem plus_door_product_ne_one
    {p a q : ℕ}
    (hp : p.Prime) (h5 : p ≠ 5)
    (hdoor : a * q = p + 1) :
    (a * q) % 5 ≠ 1 := by
  intro h
  apply five_not_dvd_prime hp h5
  apply Nat.dvd_of_mod_eq_zero
  omega

/-- For the p-1 door, product residue 4 is forbidden.
    We express the door equation without natural subtraction. -/
theorem minus_door_product_ne_four
    {p a q : ℕ}
    (hp : p.Prime) (h5 : p ≠ 5)
    (hdoor : a * q + 1 = p) :
    (a * q) % 5 ≠ 4 := by
  intro h
  apply five_not_dvd_prime hp h5
  apply Nat.dvd_of_mod_eq_zero
  omega

/-- The plus-door exclusion in the displayed residue coordinates. -/
theorem plus_door_residue_cell_forbidden
    {p a q : ℕ}
    (hp : p.Prime) (h5 : p ≠ 5)
    (hdoor : a * q = p + 1) :
    ((a % 5) * (q % 5)) % 5 ≠ 1 := by
  rw [← Nat.mul_mod]
  exact plus_door_product_ne_one hp h5 hdoor

/-- The minus-door exclusion in the displayed residue coordinates. -/
theorem minus_door_residue_cell_forbidden
    {p a q : ℕ}
    (hp : p.Prime) (h5 : p ≠ 5)
    (hdoor : a * q + 1 = p) :
    ((a % 5) * (q % 5)) % 5 ≠ 4 := by
  rw [← Nat.mul_mod]
  exact minus_door_product_ne_four hp h5 hdoor

/-- Integration with the repo's `m0`: the plus-door branch excludes residue 1. -/
theorem plus_m0_residue_cell_forbidden
    {p a q : ℕ}
    (hp : p.Prime) (h5 : p ≠ 5)
    (hmod : p % 3 = 1)
    (hm0 : a * q = m0 p) :
    ((a % 5) * (q % 5)) % 5 ≠ 1 := by
  have hdoor : a * q = p + 1 := by
    simpa [m0_of_mod_one hmod] using hm0
  exact plus_door_residue_cell_forbidden hp h5 hdoor

/-- Integration with the repo's `m0`: the minus-door branch excludes residue 4. -/
theorem minus_m0_residue_cell_forbidden
    {p a q : ℕ}
    (hp : p.Prime) (h5 : p ≠ 5)
    (hmod : p % 3 = 2)
    (hm0 : a * q = m0 p) :
    ((a % 5) * (q % 5)) % 5 ≠ 4 := by
  have hpred : a * q = p - 1 := by
    simpa [m0_of_mod_two hmod] using hm0
  have hdoor : a * q + 1 = p := by
    rw [hpred]
    exact Nat.sub_add_cancel (Nat.le_of_lt hp.one_lt)
  exact minus_door_residue_cell_forbidden hp h5 hdoor

end ResidueTorus
end Hire
