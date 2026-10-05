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

/-- A prime owner cannot be divisible by a different prime modulus. -/
theorem modulus_not_dvd_prime
    {p ℓ : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hne : p ≠ ℓ) :
    ¬ ℓ ∣ p := by
  intro hd
  rcases hp.eq_one_or_self_of_dvd ℓ hd with h | h
  · exact hℓ.ne_one h
  · exact hne h.symm

/-- For a p+1 door, product residue 1 is forbidden modulo ℓ. -/
theorem plus_door_product_ne_one_mod
    {p a q ℓ : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hne : p ≠ ℓ)
    (hdoor : a * q = p + 1) :
    (a * q) % ℓ ≠ 1 := by
  intro h
  have hpos : 0 < ℓ := hℓ.pos
  have hlt : p % ℓ < ℓ := Nat.mod_lt p hpos
  have hsum : (p % ℓ + 1) % ℓ = 1 := by
    calc
      _ = (p + 1) % ℓ := by
        symm
        rw [Nat.add_mod, Nat.mod_eq_of_lt hℓ.one_lt]
      _ = (a * q) % ℓ := by rw [hdoor]
      _ = 1 := h
  have hpzero : p % ℓ = 0 := by
    by_cases hb : p % ℓ + 1 < ℓ
    · rw [Nat.mod_eq_of_lt hb] at hsum
      omega
    · have he : p % ℓ + 1 = ℓ := by omega
      rw [he, Nat.mod_self] at hsum
      norm_num at hsum
  exact modulus_not_dvd_prime hp hℓ hne
    (Nat.dvd_of_mod_eq_zero hpzero)

/-- For a p-1 door, product residue ℓ-1 is forbidden modulo ℓ. -/
theorem minus_door_product_ne_neg_one_mod
    {p a q ℓ : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hne : p ≠ ℓ)
    (hdoor : a * q + 1 = p) :
    (a * q) % ℓ ≠ ℓ - 1 := by
  intro h
  have hone : 1 % ℓ = 1 :=
    Nat.mod_eq_of_lt hℓ.one_lt
  have he : ℓ - 1 + 1 = ℓ := by
    have := hℓ.two_le
    omega
  have hpzero : p % ℓ = 0 := by
    rw [← hdoor, Nat.add_mod, h, hone, he, Nat.mod_self]
  exact modulus_not_dvd_prime hp hℓ hne
    (Nat.dvd_of_mod_eq_zero hpzero)

/-- The general plus-door exclusion in residue coordinates. -/
theorem plus_door_residue_cell_forbidden_mod
    {p a q ℓ : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hne : p ≠ ℓ)
    (hdoor : a * q = p + 1) :
    ((a % ℓ) * (q % ℓ)) % ℓ ≠ 1 := by
  rw [← Nat.mul_mod]
  exact plus_door_product_ne_one_mod hp hℓ hne hdoor

/-- The general minus-door exclusion in residue coordinates. -/
theorem minus_door_residue_cell_forbidden_mod
    {p a q ℓ : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hne : p ≠ ℓ)
    (hdoor : a * q + 1 = p) :
    ((a % ℓ) * (q % ℓ)) % ℓ ≠ ℓ - 1 := by
  rw [← Nat.mul_mod]
  exact minus_door_product_ne_neg_one_mod hp hℓ hne hdoor

/-- Each invertible factor residue has exactly one cofactor
    giving a specified invertible product. -/
theorem forbidden_cofactor_unique
    {ℓ : ℕ}
    (q t : (ZMod ℓ)ˣ) :
    ∃! a : (ZMod ℓ)ˣ, q * a = t := by
  refine ⟨q⁻¹ * t, ?_, ?_⟩
  · simp
  · intro a ha
    calc
      a = q⁻¹ * (q * a) := by simp
      _ = q⁻¹ * t := by rw [ha]

/-- The cells with product t, written as (factor, cofactor). -/
noncomputable def forbiddenResidueCells
    (ℓ : ℕ) [Fact ℓ.Prime]
    (t : (ZMod ℓ)ˣ) :
    Finset ((ZMod ℓ)ˣ × (ZMod ℓ)ˣ) := by
  classical
  exact Finset.univ.image (fun q => (q, q⁻¹ * t))

/-- Membership means precisely that the two residues multiply to t. -/
theorem mem_forbiddenResidueCells
    {ℓ : ℕ} [Fact ℓ.Prime]
    (q a t : (ZMod ℓ)ˣ) :
    (q, a) ∈ forbiddenResidueCells ℓ t ↔ q * a = t := by
  classical
  unfold forbiddenResidueCells
  constructor
  · intro h
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp h
    have hrq : r = q := congrArg Prod.fst hr
    subst r
    have ha : q⁻¹ * t = a := congrArg Prod.snd hr
    rw [← ha]
    simp
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_univ q, ?_⟩
    apply Prod.ext
    · rfl
    · calc
        q⁻¹ * t = q⁻¹ * (q * a) := by rw [h]
        _ = a := by simp

/-- There are exactly ℓ − 1 forbidden cells for each product target. -/
theorem card_forbiddenResidueCells
    (ℓ : ℕ) [Fact ℓ.Prime]
    (t : (ZMod ℓ)ˣ) :
    (forbiddenResidueCells ℓ t).card = ℓ - 1 := by
  classical
  have hinj :
      Function.Injective
        (fun q : (ZMod ℓ)ˣ => (q, q⁻¹ * t)) := by
    intro q r h
    exact congrArg Prod.fst h
  unfold forbiddenResidueCells
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_univ]
  exact ZMod.card_units ℓ

theorem card_plus_forbiddenResidueCells
    (ℓ : ℕ) [Fact ℓ.Prime] :
    (forbiddenResidueCells ℓ 1).card = ℓ - 1 := by
  exact card_forbiddenResidueCells ℓ 1

theorem card_minus_forbiddenResidueCells
    (ℓ : ℕ) [Fact ℓ.Prime] :
    (forbiddenResidueCells ℓ (-1)).card = ℓ - 1 := by
  exact card_forbiddenResidueCells ℓ (-1)

/-- For a prime modulus other than 2, the two targets differ. -/
theorem plus_target_ne_minus_target
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ 2) :
    (1 : (ZMod ℓ)ˣ) ≠ -1 := by
  let : AddCommGroup (ZMod ℓ) :=
    (ZMod.commRing ℓ).toAddCommGroup
  intro h
  have hz : (-1 : ZMod ℓ) = 1 := by
    have hc :=
      congrArg (fun u : (ZMod ℓ)ˣ => (u : ZMod ℓ)) h.symm
    simpa only [Units.coe_neg_one, Units.val_one] using hc
  rcases ZMod.neg_one_eq_one_iff.mp hz with h1 | h2
  · exact (Fact.out : ℓ.Prime).ne_one h1
  · exact hℓ h2

/-- Distinct product targets give disjoint forbidden graphs. -/
theorem forbiddenResidueCells_disjoint
    {ℓ : ℕ} [Fact ℓ.Prime]
    {t u : (ZMod ℓ)ˣ}
    (htu : t ≠ u) :
    Disjoint
      (forbiddenResidueCells ℓ t)
      (forbiddenResidueCells ℓ u) := by
  classical
  apply Finset.disjoint_left.mpr
  intro cell ht hu
  have ht' : cell.1 * cell.2 = t :=
    (mem_forbiddenResidueCells cell.1 cell.2 t).mp ht
  have hu' : cell.1 * cell.2 = u :=
    (mem_forbiddenResidueCells cell.1 cell.2 u).mp hu
  exact htu (ht'.symm.trans hu')

/-- The plus and minus forbidden graphs are disjoint
    for every odd prime modulus. -/
theorem plus_minus_forbiddenResidueCells_disjoint
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ 2) :
    Disjoint
      (forbiddenResidueCells ℓ 1)
      (forbiddenResidueCells ℓ (-1)) := by
  exact forbiddenResidueCells_disjoint
    (plus_target_ne_minus_target hℓ)

/-- Modulo 2, the plus and minus forbidden graphs coincide. -/
theorem plus_minus_forbiddenResidueCells_eq_mod_two :
    forbiddenResidueCells 2 1 =
      forbiddenResidueCells 2 (-1) := by
  have h : (1 : (ZMod 2)ˣ) = -1 := by
    apply Units.ext
    change (1 : ZMod 2) = -1
    exact (ZMod.neg_eq_self_mod_two (1 : ZMod 2)).symm
  exact congrArg (forbiddenResidueCells 2) h

end ResidueTorus
end Hire
