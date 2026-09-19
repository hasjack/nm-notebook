/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.GoldBridge
import Hire.Graph
import Mathlib.Data.Nat.Factors

/-!
# Sequel A — Q3 scaffolding (2-power doors ↔ gold-disconnected windows)

Toward

> Q3 (infinitely many gold-disconnected finite windows)
> ↔ infinitely many Mersenne / Fermat 2-power-door primes.

* **Lemma A1** (`goldIsolated_of_firstOwner_twoPowerDoor`)
* **Lemma A2** (`exists_twoPowerDoor_of_finite_closed`)
* **Package** (`infinite_goldDisconnected_of_infinite_twoPowerDoors`)
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

/-- Downward `GoldArc` on odd leaves is strictly decreasing. -/
theorem GoldArc_tgt_lt {O : Set ℕ} {p q : ℕ}
    (h : GoldArc O p q) (hpOdd : Odd p) : q < p := by
  have hqdvd : q ∣ m0 p := h.2.2.2.2.1
  have hq2 : q ≠ 2 := h.2.2.2.1
  have hqH := h.2.1
  have hqP : q.Prime := prime_of_hired_ne_two hqH hq2
  have hqOdd : Odd q := odd_of_prime_ne_two hqP hq2
  have hp2 : p ≠ 2 := h.2.2.1
  have hpP : p.Prime := prime_of_hired_ne_two h.1 hp2
  have hpos : 0 < m0 p := by
    have : 1 ≤ p := Nat.le_of_lt hpP.one_lt
    unfold m0; split_ifs <;> omega
  have hqle : q ≤ m0 p := Nat.le_of_dvd hpos hqdvd
  have hm0 : m0 p ≤ p + 1 := m0_le_succ p
  have hne : p ≠ q := h.2.2.2.2.2
  have hq_ne_succ : q ≠ p + 1 := fun hEq => by
    have hOdd' : Odd (p + 1) := by simpa [hEq] using hqOdd
    have hEven : Even (p + 1) := hpOdd.add_one
    exact Nat.not_even_iff_odd.mpr hOdd' hEven
  omega

/-! ## Gold-disconnected windows -/

def GoldDisconnectedWindow (X : ℕ) : Prop :=
  ∃ u v : HireVertex (owners X),
    u.val ≠ 2 ∧ v.val ≠ 2 ∧ u ≠ v ∧
      ¬ Relation.ReflTransGen (GoldEdge (owners X)) u v

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

/-! ## Package -/

theorem twoPowerDoor_mersenne_or_fermat_shape
    {M : ℕ} (hM : M.Prime) (h3 : M ≠ 3) (hdoor : IsTwoPowerDoor M) :
    (∃ k : ℕ, M = 2 ^ k - 1) ∨ (∃ k : ℕ, M = 2 ^ k + 1) := by
  obtain ⟨k, hk⟩ := hdoor
  rcases prime_ne_three_mod_eq_one_or_two hM h3 with hmod | hmod
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

end Hire
