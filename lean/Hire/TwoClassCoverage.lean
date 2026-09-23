/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett

Exploratory lab note (Albert two-class coverage). Not part of the Hire.lean
import barrel. Public voice: no ζ; doors and hire classes only.
-/
import Hire.Doors
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Two-class coverage (lab)

Not the hire-graph barrel. Albert's lemma: for odd `Q > 1` with `3 ∤ Q` and
`s = χ₃(Q) ∈ {-1,1}`, a prime `p > 3` hires `Q` (i.e. `Q ∣ m0 p`) exactly when
it lies in one of two residue classes mod `6Q`:

```
p ≡ 2Q − s  or  p ≡ 4Q + s   (mod 6Q)
```

Door arithmetic: a door divisible by `Q` is an even multiple of `Q`; excluding
multiples of 3 (doors are 3-free) leaves multipliers `≡ 2` or `4` (mod 6), so
`m0 p ≡ 2Q` or `4Q` (mod `6Q`). The sign `s = χ₃(Q)` picks which neighbour of
the door avoids 3, recovering the two owner classes.

**Gap corollary.** If `p < r` both hire `Q`, then
`(r − p) ≡ 0` or `±(2Q + 2s)` (mod `6Q`).
-/

namespace Hire

/-! ### Residue helpers -/

/-- Smaller hire class: `2Q − χ₃(Q)` as a natural. -/
def classA (Q : ℕ) : ℕ :=
  if chi3 Q = 1 then 2 * Q - 1 else 2 * Q + 1

/-- Larger hire class: `4Q + χ₃(Q)` as a natural. -/
def classB (Q : ℕ) : ℕ :=
  if chi3 Q = 1 then 4 * Q + 1 else 4 * Q - 1

lemma classA_of_one {Q : ℕ} (h : chi3 Q = 1) : classA Q = 2 * Q - 1 := by
  simp [classA, h]

lemma classA_of_neg {Q : ℕ} (h : chi3 Q = -1) : classA Q = 2 * Q + 1 := by
  simp [classA, h]

lemma classB_of_one {Q : ℕ} (h : chi3 Q = 1) : classB Q = 4 * Q + 1 := by
  simp [classB, h]

lemma classB_of_neg {Q : ℕ} (h : chi3 Q = -1) : classB Q = 4 * Q - 1 := by
  simp [classB, h]

lemma chi3_eq_one_or_neg_one {Q : ℕ} (h3 : ¬ 3 ∣ Q) :
    chi3 Q = 1 ∨ chi3 Q = -1 := by
  have hne : Q % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hlt : Q % 3 < 3 := Nat.mod_lt Q (by decide)
  match h : Q % 3 with
  | 0 => exact absurd h hne
  | 1 => exact Or.inl (by simp [chi3, h])
  | 2 => exact Or.inr (by simp [chi3, h])
  | k + 3 => omega

lemma Q_mod_eq_one_of_chi3_one {Q : ℕ} (h : chi3 Q = 1) : Q % 3 = 1 := by
  have hlt : Q % 3 < 3 := Nat.mod_lt Q (by decide)
  match hm : Q % 3 with
  | 0 => simp [chi3, hm] at h
  | 1 => rfl
  | 2 => simp [chi3, hm] at h
  | k + 3 => omega

lemma Q_mod_eq_two_of_chi3_neg {Q : ℕ} (h : chi3 Q = -1) : Q % 3 = 2 := by
  have hlt : Q % 3 < 3 := Nat.mod_lt Q (by decide)
  match hm : Q % 3 with
  | 0 => simp [chi3, hm] at h
  | 1 => simp [chi3, hm] at h
  | 2 => rfl
  | k + 3 => omega

lemma classA_lt {Q : ℕ} (_hQ : 0 < Q) : classA Q < 6 * Q := by
  simp [classA]; split_ifs <;> omega

lemma classB_lt {Q : ℕ} (_hQ : 0 < Q) : classB Q < 6 * Q := by
  simp [classB]; split_ifs <;> omega

lemma classA_lt_classB {Q : ℕ} (_hQ : 1 < Q) : classA Q < classB Q := by
  simp [classA, classB]; split_ifs <;> omega

lemma even_three_free_mod_six {t : ℕ} (h2 : Even t) (h3 : ¬ 3 ∣ t) :
    t % 6 = 2 ∨ t % 6 = 4 := by
  have h2m : t % 2 = 0 := Nat.even_iff.mp h2
  have h3m : t % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have h6_2 : (t % 6) % 2 = t % 2 := Nat.mod_mod_of_dvd t (by decide : 2 ∣ 6)
  have h6_3 : (t % 6) % 3 = t % 3 := Nat.mod_mod_of_dvd t (by decide : 3 ∣ 6)
  have : t % 6 < 6 := Nat.mod_lt t (by decide)
  interval_cases t % 6 <;> omega

lemma even_of_mul_odd_even {t Q : ℕ} (hQodd : Odd Q) (he : Even (Q * t)) : Even t := by
  have h2Qt : 2 ∣ Q * t := even_iff_two_dvd.mp he
  have hQn : ¬ 2 ∣ Q := fun h =>
    (Nat.not_even_iff_odd.mpr hQodd) (even_iff_two_dvd.mpr h)
  have hcop : Nat.Coprime 2 Q := (Nat.Prime.coprime_iff_not_dvd (n := Q) Nat.prime_two).mpr hQn
  exact even_iff_two_dvd.mpr (Nat.Coprime.dvd_of_dvd_mul_left hcop h2Qt)

/-- `(p+1) % m = b` with `0 < b < m` ⇒ `p % m = b - 1`. -/
lemma mod_pred_of_succ_mod {p m b : ℕ} (hm : 0 < m) (hb0 : 0 < b) (hbm : b < m)
    (h : (p + 1) % m = b) : p % m = b - 1 := by
  have hpmod : p % m < m := Nat.mod_lt p hm
  have hm1 : 1 < m := by omega
  have hadd : (p + 1) % m = (p % m + 1) % m := by
    have h1 : 1 % m = 1 := Nat.mod_eq_of_lt hm1
    rw [Nat.add_mod, h1]
  rw [hadd] at h
  have hne : p % m ≠ m - 1 := by
    intro heq
    rw [heq] at h
    have : (m - 1 + 1) % m = 0 := by
      have : m - 1 + 1 = m := by omega
      simp [this]
    omega
  have hlt : p % m + 1 < m := by omega
  have : (p % m + 1) % m = p % m + 1 := Nat.mod_eq_of_lt hlt
  omega

/-- `(p-1) % m = b` with `b+1 < m`, `1 ≤ p` ⇒ `p % m = b + 1`. -/
lemma mod_succ_of_pred_mod {p m b : ℕ} (hm : 0 < m) (hple : 1 ≤ p)
    (hbm : b + 1 < m) (h : (p - 1) % m = b) : p % m = b + 1 := by
  have hm1 : 1 < m := by omega
  have hp_eq : p = (p - 1) + 1 := (Nat.sub_add_cancel hple).symm
  have h2 : p % m = ((p - 1) + 1) % m := by rw [← hp_eq]
  have h1 : 1 % m = 1 := Nat.mod_eq_of_lt hm1
  have h3 : ((p - 1) + 1) % m = ((p - 1) % m + 1) % m := by
    rw [Nat.add_mod, h1]
  rw [h2, h3, h, Nat.mod_eq_of_lt hbm]

lemma mod_three_reduce (a Q : ℕ) (_ : 0 < Q) :
    (a % (6 * Q)) % 3 = a % 3 :=
  Nat.mod_mod_of_dvd a (by omega : 3 ∣ 6 * Q)

lemma m0_mod_three_of_prime {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    (p % 3 = 1 ∧ m0 p % 3 = 2) ∨ (p % 3 = 2 ∧ m0 p % 3 = 1) := by
  rcases prime_ne_three_mod_eq_one_or_two hp hp3 with h | h
  · left; exact ⟨h, by rw [m0_of_mod_one h]; omega⟩
  · right
    have : 1 ≤ p := Nat.le_of_lt hp.one_lt
    exact ⟨h, by rw [m0_of_mod_two h]; omega⟩

/-- If `Q ∣ m0 p`, then `m0 p ≡ 2Q` or `4Q` (mod `6Q`). -/
theorem m0_mod_six_mul_of_dvd {Q p : ℕ}
    (hQ : 1 < Q) (hQodd : Odd Q) (_hQ3 : ¬ 3 ∣ Q)
    (hp : p.Prime) (hp3 : p ≠ 3) (hodd : Odd p)
    (hdvd : Q ∣ m0 p) :
    m0 p % (6 * Q) = 2 * Q ∨ m0 p % (6 * Q) = 4 * Q := by
  obtain ⟨t, ht⟩ := hdvd
  have hm0_even : Even (m0 p) := even_m0 hp hodd hp3
  have h3m0 : ¬ 3 ∣ m0 p := three_not_dvd_m0 hp hp3
  have ht_even : Even t := by
    have : Even (Q * t) := by rwa [ht] at hm0_even
    exact even_of_mul_odd_even hQodd this
  have ht3 : ¬ 3 ∣ t := fun h =>
    h3m0 (by rw [ht]; exact dvd_mul_of_dvd_right h Q)
  have ht_mod : t % 6 = 2 ∨ t % 6 = 4 := even_three_free_mod_six ht_even ht3
  have h2Q_lt : 2 * Q < 6 * Q := by omega
  have h4Q_lt : 4 * Q < 6 * Q := by omega
  rcases ht_mod with h2 | h4
  · left
    have ht_eq : t = 6 * (t / 6) + 2 := by
      have := Nat.div_add_mod t 6; omega
    rw [ht, ht_eq]
    convert_to (6 * Q * (t / 6) + 2 * Q) % (6 * Q) = 2 * Q using 2
    · ring
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt h2Q_lt
  · right
    have ht_eq : t = 6 * (t / 6) + 4 := by
      have := Nat.div_add_mod t 6; omega
    rw [ht, ht_eq]
    convert_to (6 * Q * (t / 6) + 4 * Q) % (6 * Q) = 4 * Q using 2
    · ring
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt h4Q_lt

/-- From `m0 ≡ 2Q` (mod `6Q`), owner is class A. -/
theorem mod_classA_of_m0_two {Q p : ℕ}
    (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) (hp : p.Prime) (hp3 : p ≠ 3)
    (hm : m0 p % (6 * Q) = 2 * Q) :
    p % (6 * Q) = classA Q := by
  have hs := chi3_eq_one_or_neg_one hQ3
  have h2lt : 2 * Q < 6 * Q := by omega
  have hred : (m0 p % (6 * Q)) % 3 = m0 p % 3 := mod_three_reduce _ _ (by omega)
  have hm0_mod3 : m0 p % 3 = (2 * Q) % 3 := by omega
  rcases hs with hs1 | hs1
  · have hQ1 : Q % 3 = 1 := Q_mod_eq_one_of_chi3_one hs1
    have hm03 : m0 p % 3 = 2 := by omega
    rcases m0_mod_three_of_prime hp hp3 with ⟨hp1, _⟩ | ⟨_, hm1⟩
    · have hm0p : m0 p = p + 1 := m0_of_mod_one hp1
      have hsucc : (p + 1) % (6 * Q) = 2 * Q := by rwa [hm0p] at hm
      have := mod_pred_of_succ_mod (hm := by omega) (hb0 := by omega) (hbm := h2lt) hsucc
      simpa [classA_of_one hs1] using this
    · omega
  · have hQ2 : Q % 3 = 2 := Q_mod_eq_two_of_chi3_neg hs1
    have hm03 : m0 p % 3 = 1 := by omega
    rcases m0_mod_three_of_prime hp hp3 with ⟨_, hm2⟩ | ⟨hp2, _⟩
    · omega
    · have hm0p : m0 p = p - 1 := m0_of_mod_two hp2
      have hple : 1 ≤ p := Nat.le_of_lt hp.one_lt
      have hpred : (p - 1) % (6 * Q) = 2 * Q := by rwa [hm0p] at hm
      have := mod_succ_of_pred_mod (hm := by omega) hple (hbm := by omega) hpred
      simpa [classA_of_neg hs1] using this

/-- From `m0 ≡ 4Q` (mod `6Q`), owner is class B. -/
theorem mod_classB_of_m0_four {Q p : ℕ}
    (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) (hp : p.Prime) (hp3 : p ≠ 3)
    (hm : m0 p % (6 * Q) = 4 * Q) :
    p % (6 * Q) = classB Q := by
  have hs := chi3_eq_one_or_neg_one hQ3
  have h4lt : 4 * Q < 6 * Q := by omega
  have hred : (m0 p % (6 * Q)) % 3 = m0 p % 3 := mod_three_reduce _ _ (by omega)
  have hm0_mod3 : m0 p % 3 = (4 * Q) % 3 := by omega
  rcases hs with hs1 | hs1
  · have hQ1 : Q % 3 = 1 := Q_mod_eq_one_of_chi3_one hs1
    have hm03 : m0 p % 3 = 1 := by omega
    rcases m0_mod_three_of_prime hp hp3 with ⟨_, hm2⟩ | ⟨hp2, _⟩
    · omega
    · have hm0p : m0 p = p - 1 := m0_of_mod_two hp2
      have hple : 1 ≤ p := Nat.le_of_lt hp.one_lt
      have hpred : (p - 1) % (6 * Q) = 4 * Q := by rwa [hm0p] at hm
      have := mod_succ_of_pred_mod (hm := by omega) hple (hbm := by omega) hpred
      simpa [classB_of_one hs1] using this
  · have hQ2 : Q % 3 = 2 := Q_mod_eq_two_of_chi3_neg hs1
    have hm03 : m0 p % 3 = 2 := by omega
    rcases m0_mod_three_of_prime hp hp3 with ⟨hp1, _⟩ | ⟨_, hm1⟩
    · have hm0p : m0 p = p + 1 := m0_of_mod_one hp1
      have hsucc : (p + 1) % (6 * Q) = 4 * Q := by rwa [hm0p] at hm
      have := mod_pred_of_succ_mod (hm := by omega) (hb0 := by omega) (hbm := h4lt) hsucc
      simpa [classB_of_neg hs1] using this
    · omega

lemma dvd_of_modEq_mul {a Q k : ℕ} (h : a ≡ k * Q [MOD 6 * Q]) : Q ∣ a := by
  have : a ≡ 0 [MOD Q] := by
    have h1 : a ≡ k * Q [MOD Q] := h.of_dvd (dvd_mul_left Q 6)
    have h2 : k * Q ≡ 0 [MOD Q] := by
      change (k * Q) % Q = 0 % Q
      rw [Nat.mul_mod_left]; rfl
    exact h1.trans h2
  exact Nat.modEq_zero_iff_dvd.mp this

/-- Class A ⇒ `Q ∣ m0 p`. -/
theorem dvd_m0_of_mod_classA {Q p : ℕ}
    (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) (hp : p.Prime) (_hp3 : p ≠ 3)
    (hmod : p % (6 * Q) = classA Q) :
    Q ∣ m0 p := by
  have hs := chi3_eq_one_or_neg_one hQ3
  have hred : (p % (6 * Q)) % 3 = p % 3 := mod_three_reduce p Q (by omega)
  rcases hs with hs1 | hs1
  · rw [classA_of_one hs1] at hmod
    have hQ1 : Q % 3 = 1 := Q_mod_eq_one_of_chi3_one hs1
    have hp1 : p % 3 = 1 := by
      have : (2 * Q - 1) % 3 = 1 := by omega
      omega
    rw [m0_of_mod_one hp1]
    have h2lt : 2 * Q < 6 * Q := by omega
    have hge : 1 ≤ 2 * Q := by omega
    have hsucc : (p + 1) % (6 * Q) = 2 * Q := by
      have happ : (p + 1) % (6 * Q) = (p % (6 * Q) + 1) % (6 * Q) :=
        (Nat.add_mod p 1 (6 * Q)).trans (by rw [Nat.mod_eq_of_lt (by omega : 1 < 6 * Q)])
      rw [happ, hmod, show 2 * Q - 1 + 1 = 2 * Q by omega]
      exact Nat.mod_eq_of_lt h2lt
    have : p + 1 ≡ 2 * Q [MOD 6 * Q] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt h2lt] using hsucc
    exact dvd_of_modEq_mul (k := 2) this
  · rw [classA_of_neg hs1] at hmod
    have hQ2 : Q % 3 = 2 := Q_mod_eq_two_of_chi3_neg hs1
    have hp2 : p % 3 = 2 := by
      have : (2 * Q + 1) % 3 = 2 := by omega
      omega
    rw [m0_of_mod_two hp2]
    have hple : 1 ≤ p := Nat.le_of_lt hp.one_lt
    have h2lt : 2 * Q < 6 * Q := by omega
    have hpred : (p - 1) % (6 * Q) = 2 * Q := by
      have := mod_pred_of_succ_mod (p := p - 1) (m := 6 * Q) (b := 2 * Q + 1)
        (by omega) (by omega) (by omega)
        (by convert hmod; omega)
      exact this
    have : p - 1 ≡ 2 * Q [MOD 6 * Q] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt h2lt] using hpred
    exact dvd_of_modEq_mul (k := 2) this

/-- Class B ⇒ `Q ∣ m0 p`. -/
theorem dvd_m0_of_mod_classB {Q p : ℕ}
    (hQ : 1 < Q) (hQ3 : ¬ 3 ∣ Q) (hp : p.Prime) (_hp3 : p ≠ 3)
    (hmod : p % (6 * Q) = classB Q) :
    Q ∣ m0 p := by
  have hs := chi3_eq_one_or_neg_one hQ3
  have hred : (p % (6 * Q)) % 3 = p % 3 := mod_three_reduce p Q (by omega)
  rcases hs with hs1 | hs1
  · rw [classB_of_one hs1] at hmod
    have hQ1 : Q % 3 = 1 := Q_mod_eq_one_of_chi3_one hs1
    have hp2 : p % 3 = 2 := by
      have : (4 * Q + 1) % 3 = 2 := by omega
      omega
    rw [m0_of_mod_two hp2]
    have hple : 1 ≤ p := Nat.le_of_lt hp.one_lt
    have h4lt : 4 * Q < 6 * Q := by omega
    have hpred : (p - 1) % (6 * Q) = 4 * Q := by
      have := mod_pred_of_succ_mod (p := p - 1) (m := 6 * Q) (b := 4 * Q + 1)
        (by omega) (by omega) (by omega)
        (by convert hmod; omega)
      exact this
    have : p - 1 ≡ 4 * Q [MOD 6 * Q] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt h4lt] using hpred
    exact dvd_of_modEq_mul (k := 4) this
  · rw [classB_of_neg hs1] at hmod
    have hQ2 : Q % 3 = 2 := Q_mod_eq_two_of_chi3_neg hs1
    have hp1 : p % 3 = 1 := by
      have : (4 * Q - 1) % 3 = 1 := by omega
      omega
    rw [m0_of_mod_one hp1]
    have h4lt : 4 * Q < 6 * Q := by omega
    have hge : 1 ≤ 4 * Q := by omega
    have hsucc : (p + 1) % (6 * Q) = 4 * Q := by
      have happ : (p + 1) % (6 * Q) = (p % (6 * Q) + 1) % (6 * Q) :=
        (Nat.add_mod p 1 (6 * Q)).trans (by rw [Nat.mod_eq_of_lt (by omega : 1 < 6 * Q)])
      rw [happ, hmod, show 4 * Q - 1 + 1 = 4 * Q by omega]
      exact Nat.mod_eq_of_lt h4lt
    have : p + 1 ≡ 4 * Q [MOD 6 * Q] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt h4lt] using hsucc
    exact dvd_of_modEq_mul (k := 4) this

/-- **Two-class coverage.** -/
theorem two_class_coverage {Q p : ℕ}
    (hQ : 1 < Q) (hQodd : Odd Q) (hQ3 : ¬ 3 ∣ Q)
    (hp : p.Prime) (hp3 : 3 < p) :
    Q ∣ m0 p ↔ p % (6 * Q) = classA Q ∨ p % (6 * Q) = classB Q := by
  have hpne : p ≠ 3 := ne_of_gt hp3
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  constructor
  · intro hdvd
    rcases m0_mod_six_mul_of_dvd hQ hQodd hQ3 hp hpne hodd hdvd with h2 | h4
    · exact Or.inl (mod_classA_of_m0_two hQ hQ3 hp hpne h2)
    · exact Or.inr (mod_classB_of_m0_four hQ hQ3 hp hpne h4)
  · rintro (hA | hB)
    · exact dvd_m0_of_mod_classA hQ hQ3 hp hpne hA
    · exact dvd_m0_of_mod_classB hQ hQ3 hp hpne hB

/-! ### Gap corollary -/

/-- Forward gap `2Q + 2·χ₃(Q)` as a Nat. -/
def classGap (Q : ℕ) : ℕ :=
  if chi3 Q = 1 then 2 * Q + 2 else 2 * Q - 2

/-- Wrap-around gap `6Q − classGap`. -/
def classGap' (Q : ℕ) : ℕ := 6 * Q - classGap Q

lemma classB_sub_classA {Q : ℕ} (hQ : 1 < Q) :
    classB Q - classA Q = classGap Q := by
  simp [classA, classB, classGap]; split_ifs <;> omega

lemma classGap_lt {Q : ℕ} (hQ : 1 < Q) : classGap Q < 6 * Q := by
  simp [classGap]; split_ifs <;> omega

lemma classGap_pos {Q : ℕ} (hQ : 1 < Q) : 0 < classGap Q := by
  simp [classGap]; split_ifs <;> omega

lemma classGap'_lt {Q : ℕ} (hQ : 1 < Q) : classGap' Q < 6 * Q := by
  have hlt := classGap_lt (Q := Q) hQ
  have hpos := classGap_pos (Q := Q) hQ
  simp [classGap']; omega

lemma nat_sub_mod_eq {p r m a b c : ℕ} (hm : 0 < m) (hpr : p ≤ r)
    (hp : p % m = a) (hr : r % m = b)
    (hval : ((b : ℤ) - (a : ℤ)) % (m : ℤ) = (c : ℤ)) (_hc : c < m) :
    (r - p) % m = c := by
  have hr_p : ((r - p : ℕ) : ℤ) = (r : ℤ) - (p : ℤ) := Int.natCast_sub hpr
  have hsub : ((r : ℤ) - (p : ℤ)) % (m : ℤ) =
      ((r : ℤ) % m - (p : ℤ) % m) % m := Int.sub_emod _ _ _
  have hp' : (p : ℤ) % m = a := by rw [← Int.natCast_mod, hp]
  have hr' : (r : ℤ) % m = b := by rw [← Int.natCast_mod, hr]
  have : ((r - p : ℕ) : ℤ) % m = (c : ℤ) := by
    rw [hr_p, hsub, hr', hp', hval]
  have hcast : ((r - p : ℕ) : ℤ) % m = ↑((r - p) % m) := by
    rw [← Int.natCast_mod]
  have hlt : (r - p) % m < m := Nat.mod_lt _ hm
  omega

lemma int_neg_gap_emod {Q : ℕ} (hQ : 1 < Q) :
    (-(classGap Q : ℤ)) % (6 * Q : ℤ) = (classGap' Q : ℤ) := by
  have hg := classGap_pos hQ
  have hglt := classGap_lt (Q := Q) hQ
  simp only [classGap']
  -- -g ≡ m - g (mod m)
  have hcancel : ((-(classGap Q : ℤ) + ↑(6 * Q)) % ↑(6 * Q)) =
      ((-(classGap Q : ℤ)) % ↑(6 * Q)) := by
    rw [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
  have heq : (-(classGap Q : ℤ) + ↑(6 * Q)) = ↑(6 * Q - classGap Q) := by
    have : ((6 * Q - classGap Q : ℕ) : ℤ) =
        (6 * Q : ℤ) - classGap Q := Int.natCast_sub (Nat.le_of_lt hglt)
    omega
  have hmod : (↑(6 * Q - classGap Q) : ℤ) % ↑(6 * Q) =
      ↑(6 * Q - classGap Q) := by
    rw [← Int.natCast_mod, Nat.mod_eq_of_lt (by omega)]
  calc
    (-(classGap Q : ℤ)) % ↑(6 * Q)
        = (-(classGap Q : ℤ) + ↑(6 * Q)) % ↑(6 * Q) := hcancel.symm
    _ = ↑(6 * Q - classGap Q) % ↑(6 * Q) := by rw [heq]
    _ = ↑(6 * Q - classGap Q) := hmod

/-- **Gap corollary.** Any two primes `p < r` both hiring `Q` satisfy
`(r − p) ≡ 0`, `classGap Q`, or `classGap' Q` (mod `6Q`).
No successive-prime hypothesis is required. -/
theorem hire_gap_mod {Q p r : ℕ}
    (hQ : 1 < Q) (hQodd : Odd Q) (hQ3 : ¬ 3 ∣ Q)
    (hp : p.Prime) (hp3 : 3 < p)
    (hr : r.Prime) (hr3 : 3 < r)
    (hpr : p < r)
    (hpQ : Q ∣ m0 p) (hrQ : Q ∣ m0 r) :
    (r - p) % (6 * Q) = 0 ∨
      (r - p) % (6 * Q) = classGap Q ∨
        (r - p) % (6 * Q) = classGap' Q := by
  have hp_cls := (two_class_coverage hQ hQodd hQ3 hp hp3).mp hpQ
  have hr_cls := (two_class_coverage hQ hQodd hQ3 hr hr3).mp hrQ
  have hAB := classA_lt_classB (Q := Q) hQ
  have hGap := classB_sub_classA (Q := Q) hQ
  have hGaplt := classGap_lt (Q := Q) hQ
  have hGap'lt := classGap'_lt hQ
  have hm : 0 < 6 * Q := by omega
  rcases hp_cls with hpA | hpB <;> rcases hr_cls with hrA | hrB
  · left
    exact Nat.sub_mod_eq_zero_of_mod_eq (by omega)
  · right; left
    have hval : ((classB Q : ℤ) - (classA Q : ℤ)) % (6 * Q : ℤ) =
        (classGap Q : ℤ) := by
      have : ((classB Q - classA Q : ℕ) : ℤ) =
          (classB Q : ℤ) - classA Q := Int.natCast_sub (le_of_lt hAB)
      rw [← this, hGap]
      change (↑(classGap Q) : ℤ) % ↑(6 * Q) = ↑(classGap Q)
      rw [← Int.natCast_mod, Nat.mod_eq_of_lt hGaplt]
    exact nat_sub_mod_eq hm (le_of_lt hpr) hpA hrB hval hGaplt
  · right; right
    have hval : ((classA Q : ℤ) - (classB Q : ℤ)) % (6 * Q : ℤ) =
        (classGap' Q : ℤ) := by
      have : (classA Q : ℤ) - classB Q = - (classGap Q : ℤ) := by
        have hBA : ((classB Q - classA Q : ℕ) : ℤ) =
            (classB Q : ℤ) - classA Q := Int.natCast_sub (le_of_lt hAB)
        omega
      rw [this, int_neg_gap_emod hQ]
    exact nat_sub_mod_eq hm (le_of_lt hpr) hpB hrA hval hGap'lt
  · left
    exact Nat.sub_mod_eq_zero_of_mod_eq (by omega)

/-! ### Poster sanity checks -/

example : chi3 5 = -1 := by native_decide
example : classA 5 = 11 := by native_decide
example : classB 5 = 19 := by native_decide

example : chi3 7 = 1 := by native_decide
example : classA 7 = 13 := by native_decide
example : classB 7 = 29 := by native_decide

example : chi3 49 = 1 := by native_decide
example : classA 49 = 97 := by native_decide
example : classB 49 = 197 := by native_decide
example : classGap 49 = 100 := by native_decide
example : classGap' 49 = 194 := by native_decide

example : chi3 11 = -1 := by native_decide
example : classA 11 = 23 := by native_decide
example : classB 11 = 43 := by native_decide

example {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    5 ∣ m0 p ↔ p % 30 = 11 ∨ p % 30 = 19 := by
  simpa [classA, classB, show chi3 5 = -1 from by native_decide] using
    two_class_coverage (Q := 5) (by decide) (by decide) (by decide) hp hp3

example {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    7 ∣ m0 p ↔ p % 42 = 13 ∨ p % 42 = 29 := by
  simpa [classA, classB, show chi3 7 = 1 from by native_decide] using
    two_class_coverage (Q := 7) (by decide) (by decide) (by decide) hp hp3

example {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    49 ∣ m0 p ↔ p % 294 = 97 ∨ p % 294 = 197 := by
  simpa [classA, classB, show chi3 49 = 1 from by native_decide] using
    two_class_coverage (Q := 49) (by decide) (by decide) (by decide) hp hp3

example {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    11 ∣ m0 p ↔ p % 66 = 23 ∨ p % 66 = 43 := by
  simpa [classA, classB, show chi3 11 = -1 from by native_decide] using
    two_class_coverage (Q := 11) (by decide) (by decide) (by decide) hp hp3

end Hire
