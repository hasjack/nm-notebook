/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.HireSet
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Prime.Basic

/-!
# Dirichlet stub — hire-everything

Paper direction: every odd prime `q ≠ 3` is eventually hired, because doors of
owners in a suitable arithmetic progression are divisible by `q`.

Mathlib supplies Dirichlet's theorem on primes in AP as
`Nat.forall_exists_prime_gt_and_eq_mod` / `Nat.forall_exists_prime_gt_and_modEq`
(from `PrimesInAP`).

This file only pins the citation and a placeholder statement. No deep proof yet.
Public voice: doors and hire set; no ζ.
-/

namespace Hire

/-- Mathlib's Dirichlet theorem on primes in arithmetic progressions
(coprime residue class). Pointed here for the hire-everything argument. -/
theorem exists_owner_prime_in_AP (n : ℕ) {m a : ℕ} (hm : m ≠ 0) (hcop : a.Coprime m) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p ≡ a [MOD m] := by
  obtain ⟨p, hp, hprime, heq⟩ := Nat.forall_exists_prime_gt_and_modEq n hm hcop
  exact ⟨p, hp, hprime, heq⟩

/-- Placeholder: every odd prime `q ≠ 3` appears as a hired door-factor for some
sufficiently large owner window. Proof deferred to a later slice. -/
theorem eventually_hired (q : ℕ) (_hq : q.Prime) (_hodd : Odd q) (_h3 : q ≠ 3) :
    ∃ X : ℕ, Hired (owners X) q := by
  -- Choose an owner `p ≡ ±1 [MOD q]` large enough so `q ∣ m0 p`, then close under hire.
  sorry

end Hire
