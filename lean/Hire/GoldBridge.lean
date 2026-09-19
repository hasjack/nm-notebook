/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Doors
import Hire.HireSet
import Hire.Dirichlet
import Hire.WeakQ2
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Strong Q2 — Dirichlet sideways gold bridge

Every odd prime `q ≠ 3` lies in the infinite undirected-gold component of `5`.

For `q ≠ 5`, CRT classes mod `15q`
* (A) `r ≡ 1 [MOD 3]` and `r ≡ -1 [MOD 5q]`
* (B) `r ≡ 2 [MOD 3]` and `r ≡ +1 [MOD 5q]`
are coprime to `15q`. Dirichlet supplies a prime bridge `r` in either class; then
`5q ∣ m0 r`, hence undirected gold edges `r—5` and `r—q`, so path `q–r–5`.

## Main results

* `five_mul_q_dvd_m0_of_classA` / `five_mul_q_dvd_m0_of_classB`
* `exists_bridge_prime_classA` / `exists_bridge_prime_classB`
* `exists_gold_bridge_prime`
* `strong_Q2`
* `two_power_door_in_gold_component_of_5`
* `mersenne_two_power_door_in_gold_component_of_5`
* `fermat_prime_in_gold_component_of_5`
* `finite_window_gold_path_of_bridge`
-/

namespace Hire

/-! ## Congruence half: `5q ∣ m0 r` on CRT classes A/B -/

/-- Class A: `r ≡ 1 [MOD 3]` and `r ≡ -1 [MOD 5q]` ⇒ `5q ∣ m0 r`. -/
theorem five_mul_q_dvd_m0_of_classA {q r : ℕ}
    (hmod3 : r % 3 = 1) (hmod : r ≡ 5 * q - 1 [MOD 5 * q]) (hq : 0 < q) :
    5 * q ∣ m0 r := by
  have hn : 1 ≤ 5 * q := by omega
  rw [m0_of_mod_one hmod3, Nat.dvd_iff_mod_eq_zero]
  have hlt : 5 * q - 1 < 5 * q := Nat.sub_lt (by omega) (by decide)
  have hr : r % (5 * q) = 5 * q - 1 := Nat.mod_eq_of_modEq hmod hlt
  rw [Nat.add_mod, hr, Nat.mod_eq_of_lt (show 1 < 5 * q by omega)]
  have : 5 * q - 1 + 1 = 5 * q := Nat.sub_add_cancel hn
  rw [this, Nat.mod_self]

/-- Class B: `r ≡ 2 [MOD 3]` and `r ≡ 1 [MOD 5q]` ⇒ `5q ∣ m0 r`. -/
theorem five_mul_q_dvd_m0_of_classB {q r : ℕ}
    (hmod3 : r % 3 = 2) (hmod : r ≡ 1 [MOD 5 * q]) (hr1 : 1 ≤ r) :
    5 * q ∣ m0 r := by
  rw [m0_of_mod_two hmod3]
  have h1 : (5 * q : ℤ) ∣ (1 - ↑r) := Nat.modEq_iff_dvd.mp hmod
  have h2 : (5 * q : ℤ) ∣ (↑r - 1) := by
    rw [← neg_sub]
    exact dvd_neg.mpr h1
  have : (5 * q : ℤ) ∣ ↑(r - 1) := by rwa [Int.natCast_sub hr1]
  exact Int.natCast_dvd_natCast.mp this

/-- Either CRT class yields `5q ∣ m0 r`. -/
theorem five_mul_q_dvd_m0_of_bridgeClass {q r : ℕ} (hq : 0 < q) (hr1 : 1 ≤ r)
    (h : (r % 3 = 1 ∧ r ≡ 5 * q - 1 [MOD 5 * q]) ∨
         (r % 3 = 2 ∧ r ≡ 1 [MOD 5 * q])) :
    5 * q ∣ m0 r := by
  rcases h with ⟨h3, hm⟩ | ⟨h3, hm⟩
  · exact five_mul_q_dvd_m0_of_classA h3 hm hq
  · exact five_mul_q_dvd_m0_of_classB h3 hm hr1

/-! ## CRT residues and coprimality -/

lemma coprime_three_five_mul_q {q : ℕ} (hq : q.Prime) (h3 : q ≠ 3) :
    Nat.Coprime 3 (5 * q) := by
  refine (Nat.coprime_mul_iff_right).2 ⟨by decide, ?_⟩
  exact (Nat.Prime.coprime_iff_not_dvd (by decide)).2
    (not_three_dvd_of_prime_ne_three hq h3)

lemma coprime_of_modeq_one {a n : ℕ} (hn : 1 < n) (h : a ≡ 1 [MOD n]) :
    a.Coprime n := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
  have : a % n = 1 := Nat.mod_eq_of_modEq h (by omega)
  rw [this, Nat.gcd_one_left]

lemma coprime_of_modeq_pred {a n : ℕ} (hn : 1 ≤ n) (h : a ≡ n - 1 [MOD n]) :
    a.Coprime n := by
  have hn0 : 0 < n := by omega
  have hlt : n - 1 < n := Nat.sub_lt hn0 (by decide)
  have ha : a % n = n - 1 := Nat.mod_eq_of_modEq h hlt
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, ha]
  exact (Nat.coprime_self_sub_left (Nat.succ_le_of_lt hn0)).2 (Nat.coprime_one_left _)

/-- Residue for class A: `≡ 1 [MOD 3]`, `≡ -1 [MOD 5q]`. -/
noncomputable def bridgeResidueA (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) : ℕ :=
  ↑(Nat.chineseRemainder (coprime_three_five_mul_q hq h3) 1 (5 * q - 1))

/-- Residue for class B: `≡ 2 [MOD 3]`, `≡ 1 [MOD 5q]`. -/
noncomputable def bridgeResidueB (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) : ℕ :=
  ↑(Nat.chineseRemainder (coprime_three_five_mul_q hq h3) 2 1)

lemma bridgeResidueA_mod3 (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) :
    bridgeResidueA q hq h3 ≡ 1 [MOD 3] :=
  (Nat.chineseRemainder (coprime_three_five_mul_q hq h3) 1 (5 * q - 1)).2.1

lemma bridgeResidueA_mod5q (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) :
    bridgeResidueA q hq h3 ≡ 5 * q - 1 [MOD 5 * q] :=
  (Nat.chineseRemainder (coprime_three_five_mul_q hq h3) 1 (5 * q - 1)).2.2

lemma bridgeResidueB_mod3 (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) :
    bridgeResidueB q hq h3 ≡ 2 [MOD 3] :=
  (Nat.chineseRemainder (coprime_three_five_mul_q hq h3) 2 1).2.1

lemma bridgeResidueB_mod5q (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) :
    bridgeResidueB q hq h3 ≡ 1 [MOD 5 * q] :=
  (Nat.chineseRemainder (coprime_three_five_mul_q hq h3) 2 1).2.2

lemma bridgeResidueA_coprime (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) :
    (bridgeResidueA q hq h3).Coprime (15 * q) := by
  have h15 : 15 * q = 3 * (5 * q) := by ring
  rw [h15]
  have c3 := coprime_of_modeq_one (by decide : 1 < 3) (bridgeResidueA_mod3 q hq h3)
  have c5q := coprime_of_modeq_pred (by have := hq.pos; omega : 1 ≤ 5 * q)
    (bridgeResidueA_mod5q q hq h3)
  exact Nat.Coprime.mul_right c3 c5q

lemma bridgeResidueB_coprime (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) :
    (bridgeResidueB q hq h3).Coprime (15 * q) := by
  have h15 : 15 * q = 3 * (5 * q) := by ring
  rw [h15]
  have c3 : (bridgeResidueB q hq h3).Coprime 3 := by
    have ha : bridgeResidueB q hq h3 % 3 = 2 :=
      Nat.mod_eq_of_modEq (bridgeResidueB_mod3 q hq h3) (by decide)
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, ha]
    decide
  have c5q := coprime_of_modeq_one (by have := hq.pos; omega : 1 < 5 * q)
    (bridgeResidueB_mod5q q hq h3)
  exact Nat.Coprime.mul_right c3 c5q

/-! ## Dirichlet: arbitrarily large bridge primes -/

/-- Arbitrarily large primes in class A. -/
theorem exists_bridge_prime_classA (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) (N : ℕ) :
    ∃ r : ℕ, N < r ∧ r.Prime ∧ r ≡ 1 [MOD 3] ∧ r ≡ 5 * q - 1 [MOD 5 * q] := by
  have hm : 15 * q ≠ 0 := Nat.mul_ne_zero (by decide) hq.ne_zero
  obtain ⟨r, hrN, hrP, hrEq⟩ :=
    exists_owner_prime_in_AP N hm (bridgeResidueA_coprime q hq h3)
  have h15 : 15 * q = 3 * (5 * q) := by ring
  have hco := coprime_three_five_mul_q hq h3
  have hmul : r ≡ bridgeResidueA q hq h3 [MOD 3 * (5 * q)] := by rwa [← h15]
  have ⟨h3r, h5r⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hco).mpr hmul
  exact ⟨r, hrN, hrP, h3r.trans (bridgeResidueA_mod3 q hq h3),
    h5r.trans (bridgeResidueA_mod5q q hq h3)⟩

/-- Arbitrarily large primes in class B. -/
theorem exists_bridge_prime_classB (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) (N : ℕ) :
    ∃ r : ℕ, N < r ∧ r.Prime ∧ r ≡ 2 [MOD 3] ∧ r ≡ 1 [MOD 5 * q] := by
  have hm : 15 * q ≠ 0 := Nat.mul_ne_zero (by decide) hq.ne_zero
  obtain ⟨r, hrN, hrP, hrEq⟩ :=
    exists_owner_prime_in_AP N hm (bridgeResidueB_coprime q hq h3)
  have h15 : 15 * q = 3 * (5 * q) := by ring
  have hco := coprime_three_five_mul_q hq h3
  have hmul : r ≡ bridgeResidueB q hq h3 [MOD 3 * (5 * q)] := by rwa [← h15]
  have ⟨h3r, h5r⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hco).mpr hmul
  exact ⟨r, hrN, hrP, h3r.trans (bridgeResidueB_mod3 q hq h3),
    h5r.trans (bridgeResidueB_mod5q q hq h3)⟩

/-- A prime bridge for `q` (class A), larger than `15q`, with `5q ∣ m0 r`. -/
theorem exists_gold_bridge_prime (q : ℕ) (hq : q.Prime) (h3 : q ≠ 3) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ 15 * q < r ∧ 5 * q ∣ m0 r := by
  obtain ⟨r, hrN, hrP, hmod3, hmod5q⟩ :=
    exists_bridge_prime_classA q hq h3 (15 * q)
  have h3mod : r % 3 = 1 := Nat.mod_eq_of_modEq hmod3 (by decide)
  refine ⟨r, hrP, ?_, hrN, five_mul_q_dvd_m0_of_classA h3mod hmod5q hq.pos⟩
  intro hreq
  rw [hreq] at h3mod
  exact absurd h3mod (by decide)

/-! ## Undirected gold edges from a bridge -/

theorem undirectedGold_five_of_bridge {q r : ℕ}
    (hr : r.Prime) (h3r : r ≠ 3) (hne5 : r ≠ 5)
    (hdvd : 5 * q ∣ m0 r) :
    UndirectedGold 5 r := by
  refine ⟨hne5.symm, Nat.prime_five, hr, by decide, h3r, Or.inr ?_⟩
  exact dvd_trans (Nat.dvd_mul_right 5 q) hdvd

theorem undirectedGold_q_of_bridge {q r : ℕ}
    (hq : q.Prime) (hr : r.Prime) (h3q : q ≠ 3) (h3r : r ≠ 3) (hneq : r ≠ q)
    (hdvd : 5 * q ∣ m0 r) :
    UndirectedGold r q := by
  refine ⟨hneq, hr, hq, h3r, h3q, Or.inl ?_⟩
  exact dvd_trans (Nat.dvd_mul_left q 5) hdvd

/-! ## Strong Q2 (infinite undirected-gold component of 5) -/

/-- **Strong Q2.** Every odd prime `q ≠ 3` is gold-connected to `5`. -/
theorem strong_Q2 (q : ℕ) (hq : q.Prime) (_hodd : Odd q) (h3 : q ≠ 3) :
    InGoldComponentOf5 q := by
  classical
  by_cases h5 : q = 5
  · subst h5
    exact Relation.ReflTransGen.refl
  · obtain ⟨r, hrP, h3r, hrBig, hdvd⟩ := exists_gold_bridge_prime q hq h3
    have hqpos : 0 < q := hq.pos
    have hne5 : r ≠ 5 := by
      intro h; subst h; omega
    have hneq : r ≠ q := by
      intro h; subst h; omega
    have e1 : UndirectedGold 5 r := undirectedGold_five_of_bridge hrP h3r hne5 hdvd
    have e2 : UndirectedGold r q := undirectedGold_q_of_bridge hq hrP h3 h3r hneq hdvd
    exact (Relation.ReflTransGen.single e1).trans (Relation.ReflTransGen.single e2)

/-- Alias: membership packaging of `strong_Q2`. -/
theorem odd_prime_ne_three_in_gold_component_of_5
    (q : ℕ) (hq : q.Prime) (hodd : Odd q) (h3 : q ≠ 3) :
    InGoldComponentOf5 q :=
  strong_Q2 q hq hodd h3

/-! ## Finite-window gold path via an owned bridge owner -/

lemma five_le_of_odd_prime_ne_three {q : ℕ}
    (hq : q.Prime) (hodd : Odd q) (h3 : q ≠ 3) : 5 ≤ q := by
  have h2 : q ≠ 2 := fun h => by rw [h] at hodd; exact (by decide : ¬ Odd 2) hodd
  have h2lt : 2 < q := lt_of_le_of_ne hq.two_le (Ne.symm h2)
  have h3le : 3 ≤ q := Nat.succ_le_of_lt h2lt
  have h3lt : 3 < q := lt_of_le_of_ne h3le (Ne.symm h3)
  have h4le : 4 ≤ q := Nat.succ_le_of_lt h3lt
  have h4 : q ≠ 4 := fun h => by rw [h] at hodd; exact (by decide : ¬ Odd 4) hodd
  exact Nat.succ_le_of_lt (lt_of_le_of_ne h4le (Ne.symm h4))

/-- If bridge `r` is an owner hiring `5` and `q`, and owner `p` hires `r`, then
`GoldArc` edges `r → 5` and `r → q` exist (length-2 gold path). -/
theorem goldArc_path_of_bridge_owner {O : Set ℕ} {p q r : ℕ}
    (hpO : p ∈ O) (hrO : r ∈ O)
    (hq : q.Prime) (h3q : q ≠ 3)
    (hr : r.Prime) (h3r : r ≠ 3) (hr_ne_two : r ≠ 2) (hq_ne_two : q ≠ 2)
    (hr_hired : r ∣ m0 p) (hdvd : 5 * q ∣ m0 r)
    (hne_rq : r ≠ q) (hne_r5 : r ≠ 5) :
    GoldArc O r 5 ∧ GoldArc O r q := by
  have h5hired : Hired O 5 :=
    Hired.ofDoor hrO Nat.prime_five (by decide)
      (dvd_trans (Nat.dvd_mul_right 5 q) hdvd)
  have hqhired : Hired O q :=
    Hired.ofDoor hrO hq h3q (dvd_trans (Nat.dvd_mul_left q 5) hdvd)
  have hrhired : Hired O r :=
    Hired.ofDoor hpO hr h3r hr_hired
  exact ⟨⟨hrhired, h5hired, hr_ne_two, by decide,
            dvd_trans (Nat.dvd_mul_right 5 q) hdvd, hne_r5⟩,
         ⟨hrhired, hqhired, hr_ne_two, hq_ne_two,
            dvd_trans (Nat.dvd_mul_left q 5) hdvd, hne_rq⟩⟩

/-- Finite window: `p, r ∈ owners X`, `r ∣ m0 p`, `5q ∣ m0 r` ⇒ hired triple and
gold arcs `r → 5`, `r → q`. Any such `X` already satisfies
`X ≥ max(p, r)` and `r ≥ 5` via the `owners` side-conditions. -/
theorem finite_window_gold_path_of_bridge
    (q r p X : ℕ)
    (hq : q.Prime) (hodd_q : Odd q) (h3q : q ≠ 3) (_h5q : q ≠ 5)
    (hr : r.Prime) (hodd_r : Odd r) (h3r : r ≠ 3)
    (hp : p ∈ owners X) (hrO : r ∈ owners X)
    (hr_hired : r ∣ m0 p) (hdvd : 5 * q ∣ m0 r) :
    Hired (owners X) 5 ∧ Hired (owners X) q ∧ Hired (owners X) r ∧
      GoldArc (owners X) r 5 ∧ GoldArc (owners X) r q := by
  have hr_ne_two : r ≠ 2 := fun h => by
    rw [h] at hodd_r; exact (by decide : ¬ Odd 2) hodd_r
  have hq_ne_two : q ≠ 2 := fun h => by
    rw [h] at hodd_q; exact (by decide : ¬ Odd 2) hodd_q
  have hq5 : 5 ≤ q := five_le_of_odd_prime_ne_three hq hodd_q h3q
  have hne_r5 : r ≠ 5 := by
    intro heq
    have hm05 : m0 5 = 4 := by native_decide
    have hdvd' : 5 * q ∣ m0 5 := by simpa [heq] using hdvd
    have hle : 5 * q ≤ m0 5 :=
      Nat.le_of_dvd (by native_decide : 0 < m0 5) hdvd'
    rw [hm05] at hle
    omega
  have hne_rq : r ≠ q := by
    intro heq
    have hpos : 0 < m0 q := by
      have : 1 ≤ q := Nat.le_of_lt hq.one_lt
      unfold m0; split_ifs <;> omega
    have hdvd' : 5 * q ∣ m0 q := by simpa [heq] using hdvd
    have hle : 5 * q ≤ m0 q := Nat.le_of_dvd hpos hdvd'
    have : m0 q ≤ q + 1 := m0_le_succ q
    omega
  have arcs := goldArc_path_of_bridge_owner hp hrO hq h3q hr h3r hr_ne_two hq_ne_two
    hr_hired hdvd hne_rq hne_r5
  exact ⟨arcs.1.2.1, arcs.2.2.1, arcs.1.1, arcs.1, arcs.2⟩

/-! ## Corollaries: Mersenne / Fermat 2-power doors -/

lemma odd_of_prime_ne_two {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) : Odd q :=
  Nat.odd_iff.mpr ((hq.eq_two_or_odd).resolve_left h2)

/-- Every odd prime 2-power door (≠ 3) is in the gold component of `5`. -/
theorem two_power_door_in_gold_component_of_5
    (q : ℕ) (hq : q.Prime) (hodd : Odd q) (h3 : q ≠ 3)
    (_hdoor : IsTwoPowerDoor q) :
    InGoldComponentOf5 q :=
  strong_Q2 q hq hodd h3

/-- Mersenne form: strengthens the statement of `weak_Q2`. -/
theorem mersenne_two_power_door_in_gold_component_of_5
    (p : ℕ) (_hp : p.Prime)
    (hM : Nat.Prime (2 ^ p - 1))
    (h3 : 2 ^ p - 1 ≠ 3)
    (_hdoor : IsTwoPowerDoor (2 ^ p - 1)) :
    InGoldComponentOf5 (2 ^ p - 1) := by
  have h2 : 2 ^ p - 1 ≠ 2 := by
    intro h
    have : 2 ^ p = 3 := by omega
    have hp2 : 2 ≤ p := _hp.two_le
    have : 4 ≤ 2 ^ p := Nat.pow_le_pow_right (by decide : 0 < 2) hp2
    omega
  exact strong_Q2 (2 ^ p - 1) hM (odd_of_prime_ne_two hM h2) h3

/-- Fermat prime `F_n = 2^{2^n} + 1` with `n ≥ 1` (hence ≠ 3) lies in the
gold component of `5`. -/
theorem fermat_prime_in_gold_component_of_5
    (n : ℕ) (hn : 0 < n) (hF : Nat.Prime (2 ^ (2 ^ n) + 1)) :
    InGoldComponentOf5 (2 ^ (2 ^ n) + 1) := by
  set F := 2 ^ (2 ^ n) + 1
  have h3 : F ≠ 3 := by
    intro h
    have hpow : 2 ^ (2 ^ n) = 2 := by omega
    have h2n : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    have h4 : 4 ≤ 2 ^ (2 ^ n) :=
      calc 4 = 2 ^ 2 := by decide
           _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by decide : 0 < 2) h2n
    omega
  have h2 : F ≠ 2 := by
    intro h
    have : 2 ^ (2 ^ n) = 1 := by omega
    have h2n : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    have : 4 ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by decide : 0 < 2) h2n
    omega
  exact strong_Q2 F hF (odd_of_prime_ne_two hF h2) h3

end Hire
