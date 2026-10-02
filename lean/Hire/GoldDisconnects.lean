/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.GoldBridge
import Hire.Graph
import Hire.InfiniteHire
import Mathlib.Data.Nat.Factors

/-!
# Sequel A — Q3 scaffolding (2-power doors ↔ gold-disconnected windows)

Toward

> Q3 (infinitely many gold-disconnected finite windows)
> ↔ infinitely many Mersenne / Fermat 2-power-door primes.

* **Lemma A1** (`goldIsolated_of_firstOwner_twoPowerDoor`)
* **Lemma A2** (`exists_twoPowerDoor_of_finite_closed`), discharged for the hire set by
  `exists_twoPowerDoor_of_hired`
* **Descent** (`gold_descent`)
* **Sink reduction** (`sinks_eq_twoPowerDoors`, `gold_path_to_sink`,
  `goldConnected_iff_sinks_reachable`, `componentsEquivSinkClasses`)
* **Bridge** (`owners_mono`, `goldReachable_mono`, `gold_bridge`)
* **Package** (`infinite_goldDisconnected_of_infinite_twoPowerDoors`)
* **Converse** (`gold_bridge_of_finset`, `goldConnected_of_finite_twoPowerDoors`,
  `goldDisconnected_arbitrarily_large_iff`)
-/

namespace Hire

/-! ## Owners -/

/-- `r` owns `M` when `r` is an owner-range prime with `M ∣ m0 r`. -/
def Owns (M r : ℕ) : Prop :=
  r.Prime ∧ Odd r ∧ r ≠ 3 ∧ 5 ≤ r ∧ M ∣ m0 r

/-- Least owner of `M`. -/
def IsFirstOwner (M r0 : ℕ) : Prop :=
  Owns M r0 ∧ ∀ r, Owns M r → r0 ≤ r

lemma owns_dvd {M r : ℕ} (h : Owns M r) : M ∣ m0 r := h.2.2.2.2

lemma owns_mem_owners {M r : ℕ} (h : Owns M r) : r ∈ owners r :=
  ⟨h.1, h.2.1, h.2.2.1, le_rfl, h.2.2.2.1⟩

lemma firstOwner_le_of_Owns {M r0 r : ℕ}
    (h : IsFirstOwner M r0) (hr : Owns M r) : r0 ≤ r :=
  h.2 r hr

/-! ## CRT / Dirichlet -/

lemma M_dvd_m0_of_classA {M r : ℕ}
    (hmod3 : r % 3 = 1) (hmod : r ≡ M - 1 [MOD M]) (hM : 1 < M) :
    M ∣ m0 r := by
  have hn : 1 ≤ M := Nat.le_of_lt hM
  rw [m0_of_mod_one hmod3, Nat.dvd_iff_mod_eq_zero]
  have hlt : M - 1 < M := Nat.sub_lt (Nat.zero_lt_of_lt hM) (by decide)
  have hr : r % M = M - 1 := Nat.mod_eq_of_modEq hmod hlt
  rw [Nat.add_mod, hr, Nat.mod_eq_of_lt hM]
  have : M - 1 + 1 = M := Nat.sub_add_cancel hn
  rw [this, Nat.mod_self]

lemma coprime_three_M {M : ℕ} (hM : M.Prime) (h3 : M ≠ 3) : Nat.Coprime 3 M :=
  (Nat.Prime.coprime_iff_not_dvd (by decide)).2
    (not_three_dvd_of_prime_ne_three hM h3)

noncomputable def ownerResidueA (M : ℕ) (hM : M.Prime) (h3 : M ≠ 3) : ℕ :=
  ↑(Nat.chineseRemainder (coprime_three_M hM h3) 1 (M - 1))

lemma ownerResidueA_mod3 (M : ℕ) (hM : M.Prime) (h3 : M ≠ 3) :
    ownerResidueA M hM h3 ≡ 1 [MOD 3] :=
  (Nat.chineseRemainder (coprime_three_M hM h3) 1 (M - 1)).2.1

lemma ownerResidueA_modM (M : ℕ) (hM : M.Prime) (h3 : M ≠ 3) :
    ownerResidueA M hM h3 ≡ M - 1 [MOD M] :=
  (Nat.chineseRemainder (coprime_three_M hM h3) 1 (M - 1)).2.2

lemma ownerResidueA_coprime (M : ℕ) (hM : M.Prime) (h3 : M ≠ 3) :
    (ownerResidueA M hM h3).Coprime (3 * M) := by
  have c3 := coprime_of_modeq_one (by decide : 1 < 3) (ownerResidueA_mod3 M hM h3)
  have cM :=
    coprime_of_modeq_pred (Nat.succ_le_of_lt hM.pos) (ownerResidueA_modM M hM h3)
  exact Nat.Coprime.mul_right c3 cM

theorem exists_owner_prime (M : ℕ) (hM : M.Prime) (h3 : M ≠ 3) (N : ℕ) :
    ∃ r : ℕ, N < r ∧ Owns M r := by
  have hm : 3 * M ≠ 0 := Nat.mul_ne_zero (by decide) hM.ne_zero
  obtain ⟨r, hrN, hrP, hrEq⟩ :=
    exists_owner_prime_in_AP N hm (ownerResidueA_coprime M hM h3)
  have hco := coprime_three_M hM h3
  have ⟨h3r, hMr⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hco).mpr hrEq
  have hmod3 : r % 3 = 1 :=
    Nat.mod_eq_of_modEq (h3r.trans (ownerResidueA_mod3 M hM h3)) (by decide)
  have hmodM : r ≡ M - 1 [MOD M] := hMr.trans (ownerResidueA_modM M hM h3)
  have hr2 : r ≠ 2 := by intro h; subst h; omega
  have hodd : Odd r := odd_of_prime_ne_two hrP hr2
  have hr3 : r ≠ 3 := by intro h; subst h; exact absurd hmod3 (by decide)
  have hr5 : 5 ≤ r := five_le_of_odd_prime_ne_three hrP hodd hr3
  exact ⟨r, hrN, hrP, hodd, hr3, hr5, M_dvd_m0_of_classA hmod3 hmodM hM.one_lt⟩

theorem exists_firstOwner (M : ℕ) (hM : M.Prime) (h3 : M ≠ 3) :
    ∃ r0 : ℕ, IsFirstOwner M r0 := by
  classical
  obtain ⟨r, _, hrOwns⟩ := exists_owner_prime M hM h3 0
  refine ⟨Nat.find (⟨r, hrOwns⟩ : ∃ n, Owns M n), Nat.find_spec _, ?_⟩
  intro t ht
  exact Nat.find_min' (⟨r, hrOwns⟩ : ∃ n, Owns M n) ht

/-! ## Hire facts at first-owner window -/

lemma hired_of_firstOwner {M r0 : ℕ}
    (hM : M.Prime) (h3 : M ≠ 3) (hfo : IsFirstOwner M r0) :
    Hired (owners r0) M :=
  Hired.ofDoor (owns_mem_owners hfo.1) hM h3 (owns_dvd hfo.1)

lemma not_dvd_m0_self {p : ℕ} (hp : 1 < p) : ¬ p ∣ m0 p := by
  intro h
  have hpos : 0 < m0 p := by unfold m0; split_ifs <;> omega
  have hge : p ≤ m0 p := Nat.le_of_dvd hpos h
  have hle : m0 p ≤ p + 1 := m0_le_succ p
  have : m0 p = p ∨ m0 p = p + 1 := by omega
  rcases this with hEq | hEq
  · unfold m0 at hEq; split_ifs at hEq <;> omega
  · have hp1 : p ∣ p + 1 := by simpa [hEq] using h
    have hmod0 : (p + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hp1
    have hp0 : 0 < p := Nat.zero_lt_of_lt hp
    have hmod1 : (p + 1) % p = 1 := by
      rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      exact Nat.mod_eq_of_lt hp
    omega

theorem not_hired_firstOwner {M r0 : ℕ}
    (hfo : IsFirstOwner M r0) : ¬ Hired (owners r0) r0 := by
  intro h
  cases h with
  | seed =>
      have h5 := hfo.1.2.2.2.1
      omega
  | @ofDoor p _q hp _hq _hne hd =>
      have hpX : p ≤ r0 := hp.2.2.2.1
      have hpos : 0 < m0 p := m0_pos_of_owners_mem hp
      have hle : r0 ≤ m0 p := Nat.le_of_dvd hpos hd
      have hm0 : m0 p ≤ p + 1 := m0_le_succ p
      have hcases : m0 p = r0 ∨ m0 p = r0 + 1 := by omega
      have heven : Even (m0 p) := even_m0 hp.1 hp.2.1 hp.2.2.1
      have hrodd : Odd r0 := hfo.1.2.1
      rcases hcases with hEq | hEq
      · rw [hEq] at heven
        exact Nat.not_even_iff_odd.mpr hrodd heven
      · have hp1 : r0 ∣ r0 + 1 := by simpa [hEq] using hd
        have hmod0 : (r0 + 1) % r0 = 0 := Nat.mod_eq_zero_of_dvd hp1
        have hr0pos : 0 < r0 := Nat.zero_lt_of_lt hfo.1.1.one_lt
        have hmod1 : (r0 + 1) % r0 = 1 := by
          rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt hfo.1.1.one_lt
        omega


lemma prime_of_hired_ne_two {O : Set ℕ} {q : ℕ}
    (h : Hired O q) (hne : q ≠ 2) : q.Prime := by
  cases h with
  | seed => exact (hne rfl).elim
  | ofDoor _ hqP _ _ => exact hqP

/-! ## Lemma A1 -/

theorem not_GoldArc_of_twoPowerDoor {O : Set ℕ} {M q : ℕ}
    (hdoor : IsTwoPowerDoor M) (h : GoldArc O M q) : False := by
  obtain ⟨k, hk⟩ := hdoor
  have hqdvd : q ∣ m0 M := h.2.2.2.2.1
  have hq2 : q ≠ 2 := h.2.2.2.1
  have hqP : q.Prime := prime_of_hired_ne_two h.2.1 hq2
  have hdiv : q ∣ 2 ^ k := by simpa [hk] using hqdvd
  have : q ∣ 2 := hqP.dvd_of_dvd_pow hdiv
  exact hq2 (((Nat.dvd_prime Nat.prime_two).mp this).resolve_left hqP.ne_one)

/-- **Lemma A1.** `M` is gold-isolated at its first-owner window. -/
theorem goldIsolated_of_firstOwner_twoPowerDoor
    {M r0 : ℕ}
    (hM : M.Prime) (_hodd : Odd M) (h3 : M ≠ 3)
    (hdoor : IsTwoPowerDoor M)
    (hfo : IsFirstOwner M r0) :
    ∃ hHired : Hired (owners r0) M,
      ∀ v : HireVertex (owners r0), ¬ GoldEdge (owners r0) ⟨M, hHired⟩ v := by
  refine ⟨hired_of_firstOwner hM h3 hfo, ?_⟩
  intro v hEdge
  rcases hEdge with hArc | hArc
  · exact not_GoldArc_of_twoPowerDoor hdoor hArc
  · have hv2 : v.val ≠ 2 := hArc.2.2.1
    have hvP : v.val.Prime := prime_of_hired_ne_two v.property hv2
    have hv3 : v.val ≠ 3 := hired_ne_three v.property
    have hvOdd : Odd v.val := odd_of_prime_ne_two hvP hv2
    have hv5 : 5 ≤ v.val := five_le_of_odd_prime_ne_three hvP hvOdd hv3
    have hOwns : Owns M v.val := ⟨hvP, hvOdd, hv3, hv5, hArc.2.2.2.2.1⟩
    have hr0le : r0 ≤ v.val := firstOwner_le_of_Owns hfo hOwns
    have hvBound : v.val ≤ max 2 (r0 + 1) := hired_le_max v.property
    have hvle : v.val ≤ r0 + 1 := le_trans hvBound (max_le (by omega) le_rfl)
    have : v.val = r0 ∨ v.val = r0 + 1 := by omega
    rcases this with hvEq | hvEq
    · exact not_hired_firstOwner hfo (by simpa [hvEq] using v.property)
    · have hEven : Even (r0 + 1) := (hfo.1.2.1).add_one
      have hOdd' : Odd (r0 + 1) := by simpa [hvEq] using hvOdd
      exact Nat.not_even_iff_odd.mpr hOdd' hEven

/-! ## Lemma A2 -/

def ClosedUnderOddDoorFactors (S : Set ℕ) : Prop :=
  ∀ p ∈ S, ∀ q : ℕ, q.Prime → q ≠ 3 → Odd q → q ∣ m0 p → q ∈ S

/-- **Lemma A2.** Finite nonempty odd-prime sets closed under odd door-factors
contain a 2-power door. -/
theorem exists_twoPowerDoor_of_finite_closed
    {S : Set ℕ} (_hfin : S.Finite) (hne : S.Nonempty)
    (hprimes : ∀ p ∈ S, p.Prime ∧ Odd p ∧ p ≠ 3)
    (hcl : ClosedUnderOddDoorFactors S) :
    ∃ p ∈ S, IsTwoPowerDoor p := by
  classical
  obtain ⟨p, hpS⟩ := hne
  let p0 := Nat.find (⟨p, hpS⟩ : ∃ n, n ∈ S)
  have hp0S : p0 ∈ S := Nat.find_spec (⟨p, hpS⟩ : ∃ n, n ∈ S)
  have hp0min : ∀ q ∈ S, p0 ≤ q := fun q hq =>
    Nat.find_min' (⟨p, hpS⟩ : ∃ n, n ∈ S) hq
  obtain ⟨hp0P, hp0Odd, hp03⟩ := hprimes p0 hp0S
  rcases (m0 p0).eq_two_pow_or_exists_odd_prime_and_dvd with ⟨k, hk⟩ | ⟨q, hqP, hqdvd, hqOdd⟩
  · exact ⟨p0, hp0S, ⟨k, hk⟩⟩
  · have hq3 : q ≠ 3 := fun h => by
      subst h; exact three_not_dvd_m0 hp0P hp03 hqdvd
    have hqS : q ∈ S := hcl p0 hp0S q hqP hq3 hqOdd hqdvd
    have hpos : 0 < m0 p0 := by
      have : 1 ≤ p0 := Nat.le_of_lt hp0P.one_lt
      unfold m0; split_ifs <;> omega
    have hqle : q ≤ m0 p0 := Nat.le_of_dvd hpos hqdvd
    have hm0 : m0 p0 ≤ p0 + 1 := m0_le_succ p0
    have hq_ne_p0 : q ≠ p0 := fun h => by
      subst h; exact not_dvd_m0_self hp0P.one_lt hqdvd
    have hq_ne_succ : q ≠ p0 + 1 := fun hEq => by
      have hOdd' : Odd (p0 + 1) := by simpa [hEq] using hqOdd
      have hEven : Even (p0 + 1) := hp0Odd.add_one
      exact Nat.not_even_iff_odd.mpr hOdd' hEven
    have hqlt : q < p0 := by omega
    exact absurd (hp0min q hqS) (not_le_of_gt hqlt)

/-- An odd gold target satisfies `2 * q ≤ p + 1`. -/
theorem goldArc_tgt_le_div_two {O : Set ℕ} {p q : ℕ}
    (h : GoldArc O p q) (hpOdd : Odd p) : 2 * q ≤ p + 1 := by
  have hq2 : q ≠ 2 := h.2.2.2.1
  have hqP : q.Prime := prime_of_hired_ne_two h.2.1 hq2
  have hqOdd : Odd q := odd_of_prime_ne_two hqP hq2
  have hp2 : p ≠ 2 := h.2.2.1
  have hpP : p.Prime := prime_of_hired_ne_two h.1 hp2
  have hdiv := two_mul_dvd_m0 hpP hpOdd (hired_ne_three h.1) hqOdd h.2.2.2.2.1
  have hpos : 0 < m0 p := by
    have : 1 ≤ p := Nat.le_of_lt hpP.one_lt
    unfold m0; split_ifs <;> omega
  exact (Nat.le_of_dvd hpos hdiv).trans (m0_le_succ p)

/-- A hired odd prime in the window `X` satisfies `2 * q ≤ X + 1`. -/
theorem two_mul_le_succ_of_hired {X q : ℕ}
    (h : Hired (owners X) q) (hqOdd : Odd q) : 2 * q ≤ X + 1 := by
  cases h with
  | seed => exact absurd hqOdd (by decide : ¬ Odd 2)
  | @ofDoor p _ hp _ _ hd =>
    have hdiv := two_mul_dvd_m0 hp.1 hp.2.1 hp.2.2.1 hqOdd hd
    have hle : 2 * q ≤ p + 1 :=
      (Nat.le_of_dvd (m0_pos_of_owners_mem hp) hdiv).trans (m0_le_succ p)
    have hpX : p ≤ X := hp.2.2.2.1
    omega

/-- Downward `GoldArc` on odd leaves is strictly decreasing. -/
theorem GoldArc_tgt_lt {O : Set ℕ} {p q : ℕ}
    (h : GoldArc O p q) (hpOdd : Odd p) : q < p := by
  have hp2 : p ≠ 2 := h.2.2.1
  have hpP : p.Prime := prime_of_hired_ne_two h.1 hp2
  have := goldArc_tgt_le_div_two h hpOdd
  have := hpP.two_le
  omega

/-! ## Door closure and descent -/

/-- A hired odd prime lies in the owner window. -/
theorem mem_owners_of_hired_odd {X q : ℕ}
    (h : Hired (owners X) q) (hodd : Odd q) : q ∈ owners X := by
  have hne : q ≠ 2 := by
    intro hq
    rw [hq] at hodd
    exact (by decide : ¬ Odd 2) hodd
  have hqP := prime_of_hired_ne_two h hne
  have h3 := hired_ne_three h
  have hle := two_mul_le_succ_of_hired h hodd
  have := hqP.two_le
  exact ⟨hqP, hodd, h3, by omega, five_le_of_odd_prime_ne_three hqP hodd h3⟩

/-- An odd prime factor of an owner's door is hired, and it is an owner. -/
theorem hired_of_dvd_m0 {X p q : ℕ} (hp : p ∈ owners X)
    (hq : q.Prime) (hodd : Odd q) (h3 : q ≠ 3) (hd : q ∣ m0 p) :
    Hired (owners X) q ∧ q ∈ owners X := by
  exact ⟨Hired.ofDoor hp hq h3 hd,
    mem_owners_of_hired_odd (Hired.ofDoor hp hq h3 hd) hodd⟩

/-- The odd part of a hire window is closed under odd door factors. -/
theorem hiredOdd_closedUnderOddDoorFactors (X : ℕ) :
    ClosedUnderOddDoorFactors {q | Hired (owners X) q ∧ Odd q} := by
  intro p hp q hqP hq3 hqOdd hdvd
  obtain ⟨hH, _⟩ := hired_of_dvd_m0 (mem_owners_of_hired_odd hp.1 hp.2) hqP hqOdd hq3 hdvd
  exact ⟨hH, hqOdd⟩

/-- A window that hires an odd prime hires a 2-power door. -/
theorem exists_twoPowerDoor_of_hired {X q : ℕ}
    (h : Hired (owners X) q) (hodd : Odd q) :
    ∃ p, Hired (owners X) p ∧ Odd p ∧ IsTwoPowerDoor p := by
  let S : Set ℕ := {n | Hired (owners X) n ∧ Odd n}
  have hfin : S.Finite :=
    (Set.finite_le_nat X).subset fun n ⟨hn, hodd⟩ =>
      (mem_owners_of_hired_odd hn hodd).2.2.2.1
  have hprimes : ∀ p ∈ S, p.Prime ∧ Odd p ∧ p ≠ 3 := by
    intro p hp
    have hne : p ≠ 2 := by
      intro h2
      rw [h2] at hp
      exact (by decide : ¬ Odd 2) hp.2
    exact ⟨prime_of_hired_ne_two hp.1 hne, hp.2, hired_ne_three hp.1⟩
  obtain ⟨p, hpS, hdoor⟩ := exists_twoPowerDoor_of_finite_closed hfin ⟨q, h, hodd⟩ hprimes
    (hiredOdd_closedUnderOddDoorFactors X)
  exact ⟨p, hpS.1, hpS.2, hdoor⟩

/-- One strict gold step in the window `X`. -/
def GoldDescentStep (X : ℕ) (a b : ℕ) : Prop :=
  GoldArc (owners X) a b ∧ b < a

/-- From a hired odd prime, a strictly decreasing gold path ends at a 2-power door. -/
theorem gold_descent {X : ℕ} :
    ∀ q, Hired (owners X) q → Odd q →
      ∃ M, IsTwoPowerDoor M ∧ Relation.ReflTransGen (GoldDescentStep X) q M := by
  intro q
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro h hodd
    have hmem := mem_owners_of_hired_odd h hodd
    rcases (m0 q).eq_two_pow_or_exists_odd_prime_and_dvd with ⟨k, hk⟩ | ⟨r, hrP, hdvd, hrOdd⟩
    · exact ⟨q, ⟨k, hk⟩, Relation.ReflTransGen.refl⟩
    · have hr3 : r ≠ 3 := by
        intro hr
        exact three_not_dvd_m0 hmem.1 hmem.2.2.1 (hr ▸ hdvd)
      obtain ⟨hrH, _⟩ := hired_of_dvd_m0 hmem hrP hrOdd hr3 hdvd
      have hne : q ≠ r := by
        intro heq
        exact not_dvd_m0_self hmem.1.one_lt (heq.symm ▸ hdvd)
      have hq2 : q ≠ 2 := by
        intro hq
        rw [hq] at hodd
        exact (by decide : ¬ Odd 2) hodd
      have hr2 : r ≠ 2 := by
        intro hr
        rw [hr] at hrOdd
        exact (by decide : ¬ Odd 2) hrOdd
      have harc : GoldArc (owners X) q r := ⟨h, hrH, hq2, hr2, hdvd, hne⟩
      have hrlt : r < q := GoldArc_tgt_lt harc hodd
      obtain ⟨M, hdoor, hpath⟩ := ih r hrlt hrH hrOdd
      exact ⟨M, hdoor, Relation.ReflTransGen.head ⟨harc, hrlt⟩ hpath⟩

/-! ## Sinks -/

/-- A sink of `Γ_X` is a non-seed hired vertex with no outgoing gold arc. -/
def IsSink (X q : ℕ) : Prop :=
  Hired (owners X) q ∧ q ≠ 2 ∧ ∀ r, ¬ GoldArc (owners X) q r

lemma hired_of_goldDescent {X a b : ℕ} (ha : Hired (owners X) a)
    (h : Relation.ReflTransGen (GoldDescentStep X) a b) : Hired (owners X) b := by
  induction h with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.1.2.1

lemma ne_two_of_goldDescent {X a b : ℕ} (ha2 : a ≠ 2)
    (h : Relation.ReflTransGen (GoldDescentStep X) a b) : b ≠ 2 := by
  induction h with
  | refl => exact ha2
  | tail _ hstep _ => exact hstep.1.2.2.2.1

lemma odd_of_goldDescent {X a b : ℕ} (ha : Odd a)
    (h : Relation.ReflTransGen (GoldDescentStep X) a b) : Odd b := by
  induction h with
  | refl => exact ha
  | tail _ hstep _ =>
    exact odd_of_prime_ne_two (prime_of_hired_ne_two hstep.1.2.1 hstep.1.2.2.2.1)
      hstep.1.2.2.2.1

/-- The sinks of `Γ_X` are the 2-power doors whose first owner is at most `X`. -/
theorem sinks_eq_twoPowerDoors {X q : ℕ} :
    IsSink X q ↔
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ IsTwoPowerDoor q ∧
        ∃ r0, IsFirstOwner q r0 ∧ r0 ≤ X := by
  constructor
  · intro h
    have hH := h.1
    have hq2 := h.2.1
    have hqP := prime_of_hired_ne_two hH hq2
    have hodd := odd_of_prime_ne_two hqP hq2
    have h3 := hired_ne_three hH
    have hdoor : IsTwoPowerDoor q := by
      rcases (m0 q).eq_two_pow_or_exists_odd_prime_and_dvd with ⟨k, hk⟩ | ⟨r, hrP, hdvd, hrOdd⟩
      · exact ⟨k, hk⟩
      · have hr3 : r ≠ 3 := fun hr =>
          three_not_dvd_m0 hqP h3 (hr ▸ hdvd)
        have hmem := mem_owners_of_hired_odd hH hodd
        obtain ⟨hrH, _⟩ := hired_of_dvd_m0 hmem hrP hrOdd hr3 hdvd
        have hr2 : r ≠ 2 := fun hr => by
          rw [hr] at hrOdd
          exact (by decide : ¬ Odd 2) hrOdd
        have hne : q ≠ r := fun heq =>
          not_dvd_m0_self hqP.one_lt (heq.symm ▸ hdvd)
        exact (h.2.2 r ⟨hH, hrH, hq2, hr2, hdvd, hne⟩).elim
    cases hH with
    | seed => exact absurd hodd (by decide : ¬ Odd 2)
    | @ofDoor p _ hp _ _ hd =>
      obtain ⟨r0, hfo⟩ := exists_firstOwner q hqP h3
      have hOwns : Owns q p := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.2, hd⟩
      exact ⟨hqP, hodd, h3, hdoor, r0, hfo,
        le_trans (firstOwner_le_of_Owns hfo hOwns) hp.2.2.2.1⟩
  · intro ⟨hqP, hodd, h3, hdoor, r0, hfo, hle⟩
    have hq2 : q ≠ 2 := fun hq => by
      rw [hq] at hodd
      exact (by decide : ¬ Odd 2) hodd
    have hr0O : r0 ∈ owners X :=
      ⟨hfo.1.1, hfo.1.2.1, hfo.1.2.2.1, hle, hfo.1.2.2.2.1⟩
    have hH : Hired (owners X) q := Hired.ofDoor hr0O hqP h3 (owns_dvd hfo.1)
    refine ⟨hH, hq2, ?_⟩
    intro r harc
    exact not_GoldArc_of_twoPowerDoor hdoor harc

/-- The first owner of `5` is `11`. -/
theorem firstOwner_five : IsFirstOwner 5 11 := by
  have hown : Owns 5 11 :=
    ⟨by decide, by decide, by decide, by decide, by native_decide⟩
  refine ⟨hown, ?_⟩
  intro r hr
  have hdiv := two_mul_dvd_m0 hr.1 hr.2.1 hr.2.2.1 (by decide : Odd 5) (owns_dvd hr)
  have hle : 2 * 5 ≤ r + 1 :=
    (Nat.le_of_dvd (m0_pos_of_owners_mem (owns_mem_owners hr)) hdiv).trans (m0_le_succ r)
  have h9 : 9 ≤ r := by omega
  by_contra hlt
  have : r < 11 := lt_of_not_ge hlt
  interval_cases r
  · exact absurd hr.1 (by decide : ¬ Nat.Prime 9)
  · exact absurd hr.1 (by decide : ¬ Nat.Prime 10)

/-- For `X ≥ 11`, the door `5` is a sink of `Γ_X`. -/
theorem five_isSink {X : ℕ} (hX : 11 ≤ X) : IsSink X 5 :=
  sinks_eq_twoPowerDoors.2
    ⟨by decide, by decide, by decide, ⟨2, by native_decide⟩, 11, firstOwner_five, hX⟩

/-- From a hired odd prime, a strictly decreasing gold path ends at a sink. -/
theorem gold_path_to_sink {X q : ℕ} (h : Hired (owners X) q) (hodd : Odd q) :
    ∃ M, IsSink X M ∧ Relation.ReflTransGen (GoldDescentStep X) q M := by
  obtain ⟨M, hdoor, hpath⟩ := gold_descent q h hodd
  have hH := hired_of_goldDescent h hpath
  have hOdd := odd_of_goldDescent hodd hpath
  have h2 : M ≠ 2 := ne_two_of_goldDescent (fun hM => by
    rw [hM] at hodd
    exact (by decide : ¬ Odd 2) hodd) hpath
  have hP := prime_of_hired_ne_two hH h2
  have h3 := hired_ne_three hH
  refine ⟨M, sinks_eq_twoPowerDoors.2 ⟨hP, hOdd, h3, hdoor, ?_⟩, hpath⟩
  cases hH with
  | seed => exact absurd hOdd (by decide : ¬ Odd 2)
  | @ofDoor p _ hp _ _ hd =>
    obtain ⟨r0, hfo⟩ := exists_firstOwner M hP h3
    exact ⟨r0, hfo, le_trans (firstOwner_le_of_Owns hfo
      ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.2, hd⟩) hp.2.2.2.1⟩

lemma goldEdge_symm {O : Set ℕ} {u v : HireVertex O} (h : GoldEdge O u v) :
    GoldEdge O v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

lemma goldReachable_symm {X : ℕ} {u v : HireVertex (owners X)}
    (h : Relation.ReflTransGen (GoldEdge (owners X)) u v) :
    Relation.ReflTransGen (GoldEdge (owners X)) v u := by
  induction h with
  | refl => exact .refl
  | tail _ hedge ih => exact Relation.ReflTransGen.head (goldEdge_symm hedge) ih

lemma goldReachable_of_descent {X a b : ℕ} (ha : Hired (owners X) a)
    (h : Relation.ReflTransGen (GoldDescentStep X) a b) :
    Relation.ReflTransGen (GoldEdge (owners X))
      ⟨a, ha⟩ ⟨b, hired_of_goldDescent ha h⟩ := by
  induction h with
  | refl => exact .refl
  | tail hprev hstep ih =>
    have hsrc : (⟨_, hired_of_goldDescent ha hprev⟩ : HireVertex (owners X)) =
        ⟨_, hstep.1.1⟩ := Subtype.ext rfl
    have htgt : (⟨_, hstep.1.2.1⟩ : HireVertex (owners X)) =
        ⟨_, hired_of_goldDescent ha (hprev.tail hstep)⟩ := Subtype.ext rfl
    exact htgt ▸ (hsrc ▸ ih).tail (Or.inl hstep.1)

/-! ## Gold-disconnected windows -/

def GoldDisconnectedWindow (X : ℕ) : Prop :=
  ∃ u v : HireVertex (owners X),
    u.val ≠ 2 ∧ v.val ≠ 2 ∧ u ≠ v ∧
      ¬ Relation.ReflTransGen (GoldEdge (owners X)) u v

/-- Gold on the non-seed vertices is connected iff every pair of sinks is joined
by an undirected gold path. For `X ≥ 11`, `five_isSink` puts `5` among them. -/
theorem goldConnected_iff_sinks_reachable {X : ℕ} :
    ¬ GoldDisconnectedWindow X ↔
      ∀ {q r : ℕ} (hq : IsSink X q) (hr : IsSink X r),
        Relation.ReflTransGen (GoldEdge (owners X)) ⟨q, hq.1⟩ ⟨r, hr.1⟩ := by
  constructor
  · intro hconn q r hq hr
    by_cases hqr : q = r
    · subst hqr
      exact .refl
    · by_contra hnot
      apply hconn
      refine ⟨⟨q, hq.1⟩, ⟨r, hr.1⟩, hq.2.1, hr.2.1, ?_, hnot⟩
      intro heq
      exact hqr (congrArg Subtype.val heq)
  · intro hsinks hdis
    obtain ⟨u, v, hu2, hv2, hne, hnot⟩ := hdis
    have huOdd := odd_of_prime_ne_two (prime_of_hired_ne_two u.property hu2) hu2
    have hvOdd := odd_of_prime_ne_two (prime_of_hired_ne_two v.property hv2) hv2
    obtain ⟨Mu, hsu, hpu⟩ := gold_path_to_sink u.property huOdd
    obtain ⟨Mv, hsv, hpv⟩ := gold_path_to_sink v.property hvOdd
    have hMu : (⟨Mu, hired_of_goldDescent u.property hpu⟩ : HireVertex (owners X)) =
        ⟨Mu, hsu.1⟩ := Subtype.ext rfl
    have hMv : (⟨Mv, hired_of_goldDescent v.property hpv⟩ : HireVertex (owners X)) =
        ⟨Mv, hsv.1⟩ := Subtype.ext rfl
    have hreachu := hMu ▸ goldReachable_of_descent u.property hpu
    have hreachv := hMv ▸ goldReachable_of_descent v.property hpv
    exact hnot (hreachu.trans ((hsinks hsu hsv).trans (goldReachable_symm hreachv)))

/-- Non-seed hired vertices: the vertices of gold. -/
abbrev GoldVertex (X : ℕ) := {v : HireVertex (owners X) // v.val ≠ 2}

/-- Connectivity of gold on the non-seed vertices. -/
def goldVertexSetoid (X : ℕ) : Setoid (GoldVertex X) where
  r u w := Relation.ReflTransGen (GoldEdge (owners X)) u.1 w.1
  iseqv := ⟨fun _ => .refl, fun h => goldReachable_symm h, fun h1 h2 => h1.trans h2⟩

/-- Connectivity of the sinks of `Γ_X`. -/
def sinkSetoid (X : ℕ) : Setoid {q // IsSink X q} where
  r s t := Relation.ReflTransGen (GoldEdge (owners X)) ⟨s.1, s.2.1⟩ ⟨t.1, t.2.1⟩
  iseqv := ⟨fun _ => .refl, fun h => goldReachable_symm h, fun h1 h2 => h1.trans h2⟩

private def sinkToGoldClass (X : ℕ) :
    Quotient (sinkSetoid X) → Quotient (goldVertexSetoid X) :=
  Quotient.lift
    (fun s => Quotient.mk (goldVertexSetoid X) ⟨⟨s.1, s.2.1⟩, s.2.2.1⟩)
    (fun _ _ hab => Quotient.sound hab)

private theorem sinkToGoldClass_bijective (X : ℕ) :
    Function.Bijective (sinkToGoldClass X) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | _ s =>
    induction b using Quotient.inductionOn with | _ t =>
    simp only [sinkToGoldClass, Quotient.lift_mk] at hab
    have hgold : Relation.ReflTransGen (GoldEdge (owners X)) ⟨s.1, s.2.1⟩ ⟨t.1, t.2.1⟩ :=
      Quotient.exact hab
    exact Quotient.sound hgold
  · intro c
    obtain ⟨v, rfl⟩ := Quotient.exists_rep c
    have hodd := odd_of_prime_ne_two (prime_of_hired_ne_two v.1.property v.2) v.2
    obtain ⟨M, hM, hpath⟩ := gold_path_to_sink v.1.property hodd
    refine ⟨Quotient.mk _ ⟨M, hM⟩, ?_⟩
    simp only [sinkToGoldClass, Quotient.lift_mk]
    apply Quotient.sound
    have hstart : (⟨v.1.val, v.1.property⟩ : HireVertex (owners X)) = v.1 :=
      Subtype.ext rfl
    have hend : (⟨M, hired_of_goldDescent v.1.property hpath⟩ : HireVertex (owners X)) =
        ⟨M, hM.1⟩ := Subtype.ext rfl
    have hraw := goldReachable_of_descent v.1.property hpath
    rw [hstart, hend] at hraw
    exact goldReachable_symm hraw

/-- The gold components are in bijection with the connectivity classes of the sinks. -/
noncomputable def componentsEquivSinkClasses (X : ℕ) :
    Quotient (goldVertexSetoid X) ≃ Quotient (sinkSetoid X) :=
  (Equiv.ofBijective (sinkToGoldClass X) (sinkToGoldClass_bijective X)).symm

lemma eq_of_reflTransGen_of_isolated
    {O : Set ℕ} {u v : HireVertex O}
    (hiso : ∀ w : HireVertex O, ¬ GoldEdge O u w)
    (h : Relation.ReflTransGen (GoldEdge O) u v) : u = v := by
  induction h with
  | refl => rfl
  | tail _ hEdge ih =>
    subst ih
    exact absurd hEdge (hiso _)

theorem goldDisconnected_of_firstOwner_twoPowerDoor
    {M r0 q : ℕ}
    (hM : M.Prime) (hodd : Odd M) (h3 : M ≠ 3)
    (hdoor : IsTwoPowerDoor M)
    (hfo : IsFirstOwner M r0)
    (hqHired : Hired (owners r0) q)
    (hq2 : q ≠ 2) (hne : q ≠ M) :
    GoldDisconnectedWindow r0 := by
  obtain ⟨hMHired, hiso⟩ :=
    goldIsolated_of_firstOwner_twoPowerDoor hM hodd h3 hdoor hfo
  refine ⟨⟨M, hMHired⟩, ⟨q, hqHired⟩, ?_, hq2, ?_, ?_⟩
  · intro hEq
    have : M = 2 := hEq
    rw [this] at hodd
    exact (by decide : ¬ Odd 2) hodd
  · intro hEq
    exact hne (Subtype.ext_iff.mp hEq).symm
  · intro hpath
    have heq := eq_of_reflTransGen_of_isolated hiso hpath
    exact hne (Subtype.ext_iff.mp heq).symm

theorem hired_five_of_eleven_le {r0 : ℕ} (h : 11 ≤ r0) :
    Hired (owners r0) 5 :=
  Hired.ofDoor ⟨by decide, by decide, by decide, h, by decide⟩
    (by decide) (by decide) (by native_decide : 5 ∣ m0 11)

/-- The first owner of an odd `q` is at least `2 * q - 1`. -/
theorem firstOwner_ge_two_mul_sub_one {q r0 : ℕ}
    (hodd : Odd q) (hfo : IsFirstOwner q r0) : 2 * q - 1 ≤ r0 := by
  have hown := hfo.1
  have hdiv := two_mul_dvd_m0 hown.1 hown.2.1 hown.2.2.1 hodd (owns_dvd hown)
  have hle : 2 * q ≤ r0 + 1 :=
    (Nat.le_of_dvd (m0_pos_of_owners_mem (owns_mem_owners hown)) hdiv).trans
      (m0_le_succ r0)
  omega

lemma firstOwner_ge_pred {M r0 : ℕ}
    (hfo : IsFirstOwner M r0) : M ≤ r0 + 1 := by
  have hdvd := owns_dvd hfo.1
  have hpos : 0 < m0 r0 := by
    have : 1 ≤ r0 := Nat.le_of_lt hfo.1.1.one_lt
    unfold m0; split_ifs <;> omega
  have hle : M ≤ m0 r0 := Nat.le_of_dvd hpos hdvd
  have : m0 r0 ≤ r0 + 1 := m0_le_succ r0
  omega

theorem goldDisconnected_firstOwner_of_twoPowerDoor_ge_twelve
    {M r0 : ℕ}
    (hM : M.Prime) (hodd : Odd M) (h3 : M ≠ 3)
    (hdoor : IsTwoPowerDoor M)
    (hfo : IsFirstOwner M r0)
    (hM12 : 12 ≤ M) :
    GoldDisconnectedWindow r0 := by
  have hr0 : 11 ≤ r0 := by
    have := firstOwner_ge_pred hfo
    omega
  exact goldDisconnected_of_firstOwner_twoPowerDoor hM hodd h3 hdoor hfo
    (hired_five_of_eleven_le hr0) (by decide) (by omega)

/-! ## Monotonicity and the finite bridge -/

/-- Larger windows contain the smaller owner sets. -/
theorem owners_mono {X Y : ℕ} (h : X ≤ Y) : owners X ⊆ owners Y :=
  fun _p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1.trans h, hp.2.2.2.2⟩

/-- A vertex hired in a window stays hired in every larger window. -/
theorem hired_mono {X Y q : ℕ} (h : X ≤ Y) (hq : Hired (owners X) q) :
    Hired (owners Y) q := by
  cases hq with
  | seed => exact .seed
  | @ofDoor p _ hp hqP hne hd => exact .ofDoor (owners_mono h hp) hqP hne hd

/-- A gold arc in a window remains a gold arc in every larger window. -/
theorem goldArc_mono {X Y p q : ℕ} (h : X ≤ Y) (harc : GoldArc (owners X) p q) :
    GoldArc (owners Y) p q :=
  ⟨hired_mono h harc.1, hired_mono h harc.2.1, harc.2.2.1, harc.2.2.2.1,
    harc.2.2.2.2.1, harc.2.2.2.2.2⟩

/-- A gold edge in a window remains a gold edge in every larger window. -/
theorem goldEdge_mono {X Y : ℕ} (h : X ≤ Y) {u v : HireVertex (owners X)}
    (he : GoldEdge (owners X) u v) :
    GoldEdge (owners Y) ⟨u.val, hired_mono h u.property⟩
      ⟨v.val, hired_mono h v.property⟩ := by
  rcases he with harc | harc
  · exact Or.inl (goldArc_mono h harc)
  · exact Or.inr (goldArc_mono h harc)

/-- Undirected gold reachability persists in every larger window. -/
theorem goldReachable_mono {X Y : ℕ} (hXY : X ≤ Y) {u v : HireVertex (owners X)}
    (h : Relation.ReflTransGen (GoldEdge (owners X)) u v) :
    Relation.ReflTransGen (GoldEdge (owners Y))
      ⟨u.val, hired_mono hXY u.property⟩
      ⟨v.val, hired_mono hXY v.property⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hedge ih =>
    exact ih.trans (Relation.ReflTransGen.single (goldEdge_mono hXY hedge))

/-- If `5 * q` divides the door of a prime `r ≠ 3` and `q` is odd, then `10 * q - 1 ≤ r`. -/
theorem ten_mul_sub_one_le_of_five_mul_dvd {q r : ℕ}
    (hq : Odd q) (hr : r.Prime) (hrOdd : Odd r) (hr3 : r ≠ 3)
    (hd : 5 * q ∣ m0 r) : 10 * q - 1 ≤ r := by
  have hdiv := two_mul_dvd_m0 hr hrOdd hr3 ((by decide : Odd 5).mul hq) hd
  have hpos : 0 < m0 r := by
    have : 1 ≤ r := Nat.le_of_lt hr.one_lt
    unfold m0; split_ifs <;> omega
  have hle : 2 * (5 * q) ≤ m0 r := Nat.le_of_dvd hpos hdiv
  have : 10 * q ≤ r + 1 := by
    have h10 : 10 * q = 2 * (5 * q) := by ring
    rw [h10]
    exact hle.trans (m0_le_succ r)
  omega

/-- Two odd primes other than `3` lie in one gold component of every sufficiently
large window. -/
theorem gold_bridge {q1 q2 : ℕ}
    (hq1 : q1.Prime) (ho1 : Odd q1) (h31 : q1 ≠ 3)
    (hq2 : q2.Prime) (ho2 : Odd q2) (h32 : q2 ≠ 3) :
    ∃ X, ∀ X', X ≤ X' →
      ∃ (h1 : Hired (owners X') q1) (h2 : Hired (owners X') q2),
        Relation.ReflTransGen (GoldEdge (owners X')) ⟨q1, h1⟩ ⟨q2, h2⟩ := by
  by_cases hEq : q1 = q2
  · subst hEq
    obtain ⟨X, hX⟩ := eventually_hired q1 hq1 ho1 h31
    refine ⟨X, fun X' hle => ?_⟩
    have h := hired_mono hle hX
    exact ⟨h, h, .refl⟩
  · have hQ : 1 < q1 * q2 := by
      have hmul : q1 * 1 < q1 * q2 := Nat.mul_lt_mul_of_pos_left hq2.one_lt hq1.pos
      exact hq1.one_lt.trans (by simpa using hmul)
    have hQ3 : ¬ 3 ∣ q1 * q2 := by
      intro hd
      rcases Nat.Prime.dvd_mul Nat.prime_three |>.mp hd with hd | hd
      · exact h31 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq1).mp hd).symm
      · exact h32 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq2).mp hd).symm
    obtain ⟨r, _, hrP, _, hdvd⟩ :=
      exists_prime_hire_gt (q1 * q2) hQ (ho1.mul ho2) hQ3 3
    have hr2 : r ≠ 2 := by omega
    have hr3 : r ≠ 3 := by omega
    have hrOdd : Odd r := odd_of_prime_ne_two hrP hr2
    have hr5 : 5 ≤ r := five_le_of_odd_prime_ne_three hrP hrOdd hr3
    have hr_not3 : ¬ 3 ∣ r := not_three_dvd_of_prime_ne_three hrP hr3
    obtain ⟨u, hru, huP, _, hudvd⟩ :=
      exists_prime_hire_gt r hrP.one_lt hrOdd hr_not3 r
    have hu2 : u ≠ 2 := by omega
    have hu3 : u ≠ 3 := by omega
    have huOdd : Odd u := odd_of_prime_ne_two huP hu2
    have hu5 : 5 ≤ u := five_le_of_odd_prime_ne_three huP huOdd hu3
    have huO : u ∈ owners u := ⟨huP, huOdd, hu3, le_rfl, hu5⟩
    have hrO : r ∈ owners u := ⟨hrP, hrOdd, hr3, le_of_lt hru, hr5⟩
    have hrH : Hired (owners u) r := Hired.ofDoor huO hrP hr3 hudvd
    have hd1 : q1 ∣ m0 r := dvd_trans (Nat.dvd_mul_right q1 q2) hdvd
    have hd2 : q2 ∣ m0 r := dvd_trans (Nat.dvd_mul_left q2 q1) hdvd
    obtain ⟨hq1H, _⟩ := hired_of_dvd_m0 hrO hq1 ho1 h31 hd1
    obtain ⟨hq2H, _⟩ := hired_of_dvd_m0 hrO hq2 ho2 h32 hd2
    have hq12 : q1 ≠ 2 := fun h => by rw [h] at ho1; exact (by decide : ¬ Odd 2) ho1
    have hq22 : q2 ≠ 2 := fun h => by rw [h] at ho2; exact (by decide : ¬ Odd 2) ho2
    have hne1 : r ≠ q1 := fun heq => not_dvd_m0_self hrP.one_lt (heq.symm ▸ hd1)
    have hne2 : r ≠ q2 := fun heq => not_dvd_m0_self hrP.one_lt (heq.symm ▸ hd2)
    have harc1 : GoldArc (owners u) r q1 := ⟨hrH, hq1H, hr2, hq12, hd1, hne1⟩
    have harc2 : GoldArc (owners u) r q2 := ⟨hrH, hq2H, hr2, hq22, hd2, hne2⟩
    have hedge1 : GoldEdge (owners u) ⟨q1, hq1H⟩ ⟨r, hrH⟩ := Or.inr harc1
    have hedge2 : GoldEdge (owners u) ⟨r, hrH⟩ ⟨q2, hq2H⟩ := Or.inl harc2
    have hpath : Relation.ReflTransGen (GoldEdge (owners u)) ⟨q1, hq1H⟩ ⟨q2, hq2H⟩ :=
      (Relation.ReflTransGen.single hedge1).trans (Relation.ReflTransGen.single hedge2)
    refine ⟨u, fun X' hle => ?_⟩
    have hmono := goldReachable_mono hle hpath
    exact ⟨hired_mono hle hq1H, hired_mono hle hq2H, hmono⟩

/-! ## Package -/

/-- A prime 2-power door other than `3` has shape `2^k - 1` or `2^k + 1`. -/
theorem twoPowerDoor_mersenne_or_fermat_shape
    {M : ℕ} (hM : M.Prime) (h3 : M ≠ 3) (hdoor : IsTwoPowerDoor M) :
    (∃ k : ℕ, M = 2 ^ k - 1) ∨ (∃ k : ℕ, M = 2 ^ k + 1) := by
  obtain ⟨k, hk⟩ := hdoor
  rcases prime_ne_three_mod_three_eq_one_or_two hM h3 with hmod | hmod
  · rw [m0_of_mod_one hmod] at hk
    exact Or.inl ⟨k, by omega⟩
  · rw [m0_of_mod_two hmod] at hk
    have h1 : 1 ≤ M := Nat.le_of_lt hM.one_lt
    exact Or.inr ⟨k, by omega⟩

/-- Infinitely many large 2-power-door primes ⇒ infinitely many gold-disconnected
windows. -/
theorem infinite_goldDisconnected_of_infinite_twoPowerDoors
    (hInf : {M : ℕ | M.Prime ∧ Odd M ∧ M ≠ 3 ∧ IsTwoPowerDoor M ∧ 12 ≤ M}.Infinite) :
    {X : ℕ | GoldDisconnectedWindow X}.Infinite := by
  classical
  refine (Set.infinite_iff_exists_gt).2 ?_
  intro N
  obtain ⟨M, hM, hMN⟩ := hInf.exists_gt (max (N + 2) 11)
  have hM12 : 12 ≤ M := hM.2.2.2.2
  obtain ⟨r0, hfo⟩ := exists_firstOwner M hM.1 hM.2.2.1
  have hr0N : N < r0 := by
    have := firstOwner_ge_pred hfo
    omega
  exact ⟨r0, goldDisconnected_firstOwner_of_twoPowerDoor_ge_twelve
    hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hfo hM12, hr0N⟩

/-- Package with Mersenne / Fermat door primes. -/
theorem infinite_goldDisconnected_of_infinite_mersenne_or_fermat_doors
    (hInf : {M : ℕ | M.Prime ∧ Odd M ∧ M ≠ 3 ∧ IsTwoPowerDoor M ∧ 12 ≤ M ∧
      ((∃ p : ℕ, p.Prime ∧ M = 2 ^ p - 1) ∨
        (∃ n : ℕ, 0 < n ∧ M = 2 ^ (2 ^ n) + 1))}.Infinite) :
    {X : ℕ | GoldDisconnectedWindow X}.Infinite :=
  infinite_goldDisconnected_of_infinite_twoPowerDoors <|
    hInf.mono fun _M h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-! ## The converse -/

/-- Each prime from a finite set of odd primes other than `3` lies on a gold path
to `5` in every sufficiently large window. -/
theorem gold_bridge_of_finset (T : Finset ℕ)
    (hT : ∀ M ∈ T, M.Prime ∧ Odd M ∧ M ≠ 3) :
    ∃ X₀, ∀ X, X₀ ≤ X → ∀ M ∈ T,
      ∃ (hM : Hired (owners X) M) (h5 : Hired (owners X) 5),
        Relation.ReflTransGen (GoldEdge (owners X)) ⟨M, hM⟩ ⟨5, h5⟩ := by
  let motive : Finset ℕ → Prop := fun T =>
    (∀ M ∈ T, M.Prime ∧ Odd M ∧ M ≠ 3) →
      ∃ X₀, ∀ X, X₀ ≤ X → ∀ M ∈ T,
        ∃ (hM : Hired (owners X) M) (h5 : Hired (owners X) 5),
          Relation.ReflTransGen (GoldEdge (owners X)) ⟨M, hM⟩ ⟨5, h5⟩
  refine Finset.induction_on (motive := motive) T ?empty ?insert hT
  · intro _
    exact ⟨0, fun _ _ M hM => (Finset.notMem_empty _ hM).elim⟩
  · intro M T _ ih hT
    obtain ⟨X₁, hX₁⟩ := ih fun N hN => hT N (Finset.mem_insert_of_mem hN)
    have hM := hT M (Finset.mem_insert_self _ _)
    obtain ⟨X₂, hX₂⟩ :=
      @gold_bridge M 5 hM.1 hM.2.1 hM.2.2 (by decide) (by decide) (by decide)
    refine ⟨max X₁ X₂, fun X hX N hN => ?_⟩
    rw [Finset.mem_insert] at hN
    rcases hN with rfl | hN
    · exact hX₂ X ((le_max_right _ _).trans hX)
    · exact hX₁ X ((le_max_left _ _).trans hX) N hN

/-- Finitely many 2-power doors imply that every sufficiently large window has
connected gold. -/
theorem goldConnected_of_finite_twoPowerDoors
    (hFin : {M : ℕ | M.Prime ∧ Odd M ∧ M ≠ 3 ∧ IsTwoPowerDoor M}.Finite) :
    ∃ X₀, ∀ X, X₀ ≤ X → ¬ GoldDisconnectedWindow X := by
  classical
  obtain ⟨X₀, hX₀⟩ := gold_bridge_of_finset hFin.toFinset fun M hM => by
    have hdoor := (hFin.mem_toFinset).mp hM
    exact ⟨hdoor.1, hdoor.2.1, hdoor.2.2.1⟩
  refine ⟨X₀, fun X hX => ?_⟩
  rw [goldConnected_iff_sinks_reachable]
  intro q r hq hr
  have hqD := sinks_eq_twoPowerDoors.mp hq
  have hrD := sinks_eq_twoPowerDoors.mp hr
  have hqmem : q ∈ hFin.toFinset :=
    hFin.mem_toFinset.mpr ⟨hqD.1, hqD.2.1, hqD.2.2.1, hqD.2.2.2.1⟩
  have hrmem : r ∈ hFin.toFinset :=
    hFin.mem_toFinset.mpr ⟨hrD.1, hrD.2.1, hrD.2.2.1, hrD.2.2.2.1⟩
  obtain ⟨hqH, h5q, hpathq⟩ := hX₀ X hX q hqmem
  obtain ⟨hrH, h5r, hpathr⟩ := hX₀ X hX r hrmem
  have hback := goldReachable_symm hpathr
  rw [show (⟨5, h5r⟩ : HireVertex (owners X)) = ⟨5, h5q⟩ from Subtype.ext rfl] at hback
  have hreach :
      Relation.ReflTransGen (GoldEdge (owners X)) ⟨q, hqH⟩ ⟨r, hrH⟩ :=
    hpathq.trans hback
  rw [show (⟨q, hqH⟩ : HireVertex (owners X)) = ⟨q, hq.1⟩ from Subtype.ext rfl,
      show (⟨r, hrH⟩ : HireVertex (owners X)) = ⟨r, hr.1⟩ from Subtype.ext rfl]
    at hreach
  exact hreach

/-- Gold is disconnected for arbitrarily large windows iff there are infinitely
many 2-power doors. -/
theorem goldDisconnected_arbitrarily_large_iff :
    {X : ℕ | GoldDisconnectedWindow X}.Infinite ↔
      {M : ℕ | M.Prime ∧ Odd M ∧ M ≠ 3 ∧ IsTwoPowerDoor M}.Infinite := by
  constructor
  · intro hX hFin
    obtain ⟨X₀, hconn⟩ := goldConnected_of_finite_twoPowerDoors hFin
    rw [Set.infinite_iff_exists_gt] at hX
    obtain ⟨X, hXmem, hgt⟩ := hX X₀
    exact hconn X (le_of_lt hgt) hXmem
  · intro hDoors
    apply infinite_goldDisconnected_of_infinite_twoPowerDoors
    rw [Set.infinite_iff_exists_gt] at hDoors ⊢
    intro N
    obtain ⟨M, hM, hgt⟩ := hDoors (max N 11)
    have h12 : 12 ≤ M := by omega
    exact ⟨M, ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2, h12⟩,
      lt_of_le_of_lt (le_max_left _ _) hgt⟩

end Hire
