/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.HireSet
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Prime.Basic

/-!
# Dirichlet on owner residue classes

Mathlib's primes in arithmetic progression, packaged as
`exists_owner_prime_in_AP`. The hire-set conclusion `eventually_hired` is
proved in `InfiniteHire.lean`, which builds the owner and closes under `Hired.ofDoor`.
-/

namespace Hire

/-- Mathlib's Dirichlet theorem on primes in arithmetic progressions
(coprime residue class). -/
theorem exists_owner_prime_in_AP (n : ℕ) {m a : ℕ} (hm : m ≠ 0) (hcop : a.Coprime m) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p ≡ a [MOD m] := by
  obtain ⟨p, hp, hprime, heq⟩ := Nat.forall_exists_prime_gt_and_modEq n hm hcop
  exact ⟨p, hp, hprime, heq⟩

end Hire
