/-
  The hire graph of the 3-free door.

  Arithmetic core for a Lean formalisation.
  Lemmas 1–4 and 9–10 are modular arithmetic.
  Lemma 5 is the gold-arc congruence.
  Infinitude of S (Dirichlet on two classes mod 3q) and the
  Laplacian statements (Lemmas 7–8) are separate.
  All spectra are taken on the finite window G_X.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace HireGraph

def chi3 (n : ℤ) : ℤ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

def m0 (p : ℕ) : ℤ := (p : ℤ) + chi3 p
def m1 (p : ℕ) : ℤ := (p : ℤ) - chi3 p

lemma chi3_of_mod_one {n : ℤ} (h : n % 3 = 1) : chi3 n = 1 := by
  simp [chi3, h]

lemma chi3_of_mod_two {n : ℤ} (h : n % 3 = 2) : chi3 n = -1 := by
  simp [chi3, h]

lemma chi3_of_mod_zero {n : ℤ} (h : n % 3 = 0) : chi3 n = 0 := by
  simp [chi3, h]

lemma chi3_eq_zero_iff (n : ℤ) : chi3 n = 0 ↔ n % 3 = 0 := by
  unfold chi3
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · omega

/-- Lemma 1. For an odd prime `p ≠ 3`, `m0 p` is even and not divisible by 3,
`m1 p` is divisible by 6, and `{m0 p, m1 p} = {p-1, p+1}`. -/
lemma lemma1_doors {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1)
    (hne3 : p ≠ 3) :
    Even (m0 p) ∧ ¬ (3 ∣ m0 p) ∧ (6 ∣ m1 p) ∧
      ({m0 p, m1 p} : Set ℤ) = {(p : ℤ) - 1, (p : ℤ) + 1} := by
  sorry

lemma three_not_divides_m0 {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1)
    (hne3 : p ≠ 3) : ¬ (3 ∣ m0 p) :=
  (lemma1_doors hp hodd hne3).2.1

/-- Examples after Lemma 1. -/
lemma m0_eleven : m0 11 = 10 := by native_decide
lemma m0_thirteen : m0 13 = 14 := by native_decide
lemma m1_eleven : m1 11 = 12 := by native_decide
lemma m1_thirteen : m1 13 = 12 := by native_decide

/-- Lemma 2, row `p ≡ 1 (mod 12)`. The other three rows are the same shape. -/
lemma lemma2_class_one {p : ℕ} (hp : p % 12 = 1) :
    chi3 p = 1 ∧ m0 p % 12 = 2 ∧ m1 p % 12 = 0 := by
  sorry

/-- Lemma 3. Twin primes greater than 3 share the 6-door. -/
lemma lemma3_twins {p : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime (p + 2))
    (hgt : 3 < p) :
    p % 3 = 2 ∧ m1 p = p + 1 ∧ m1 (p + 2) = p + 1 := by
  sorry

/-- Corollary: a 3-free even integer has at most one odd-prime neighbour > 3. -/
lemma corollary_one_neighbour {m : ℕ} (heven : Even m) (h3 : ¬ (3 ∣ m))
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpn : p = m - 1 ∨ p = m + 1) (hqn : q = m - 1 ∨ q = m + 1)
    (hp3 : 3 < p) (hq3 : 3 < q) :
    p = q := by
  sorry

/-- Lemma 4. Sophie Germain / safeprime: `m0 (2p+1) = 2p`. -/
lemma lemma4_safeprime {p : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime (2 * p + 1)) (hgt : 3 < p) :
    p % 3 = 2 ∧ m0 (2 * p + 1) = 2 * p := by
  sorry

/-- Lemma 5. Gold arc `p → q` iff `p ≡ -chi3 p (mod q)`. -/
lemma lemma5_gold_arc {p q : ℕ} (hq : Nat.Prime q) (hqodd : q ≠ 2) :
    (q : ℤ) ∣ m0 p ↔ (p : ℤ) ≡ -chi3 p [ZMOD q] := by
  unfold m0
  constructor
  · intro h
    exact Int.modEq_neg_iff_dvd.mpr (by
      simpa [Int.sub_eq_add_neg, add_comm] using h)
  · intro h
    simpa [Int.sub_eq_add_neg, add_comm] using
      (Int.modEq_neg_iff_dvd.mp h)

/-- Lemma 9. Sluice `Σ = {5}`: flip precisely on `p ≡ 11 or 19 (mod 30)`. -/
lemma lemma9_sack5 {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1)
    (hne3 : p ≠ 3) :
    (5 ∣ m0 p) ↔ p % 30 = 11 ∨ p % 30 = 19 := by
  sorry

lemma lemma9_sack5_other_door {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1)
    (hne3 : p ≠ 3) (hflip : p % 30 = 11 ∨ p % 30 = 19) :
    ¬ (5 ∣ m1 p) := by
  sorry

/-- Lemma 10. Sluice `Σ = {5,7}`: undefined on four classes mod 210. -/
lemma lemma10_sack57 {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1)
    (hne5 : p ≠ 5) (hne7 : p ≠ 7) :
    ((5 ∣ m0 p ∧ 7 ∣ m1 p) ∨ (7 ∣ m0 p ∧ 5 ∣ m1 p)) ↔
      p % 210 = 29 ∨ p % 210 = 41 ∨ p % 210 = 169 ∨ p % 210 = 181 := by
  sorry

/-
  Remaining, in increasing weight:

  * Finite hire graph `G_X`: vertices `S_X = {2} ∪ odd prime factors of
    `m0 p` for primes `5 ≤ p ≤ X`; spokes from 2; gold arcs as in Lemma 5
    with owner `p ≤ X`.
  * Lemma 6: every undirected gold edge spans a triangle with 2.
  * Lemma 7: the vector `(n-1)` at 2 and `-1` on the leaves is an
    eigenvector of eigenvalue `n = |S_X|`.
  * Lemma 8: `spec(H_X) = {0, n} ∪ {1+μ₂, …, 1+μ_{n-1}}`, hence
    `λ₂(H_X) = 1` iff undirected gold on the leaves is disconnected.
  * Infinitude of owners of a fixed `q ≠ 3`: Dirichlet on the two
    classes modulo `3q` displayed in the note.
-/

end HireGraph
