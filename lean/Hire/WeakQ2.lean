/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Doors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Relation

/-!
# Weak Q2 (statement)

Every Mersenne prime `M = 2^p - 1` that arises as a **2-power door**
(i.e. `m0 M` is a power of 2) lies in the infinite undirected-gold component of
`5`.

Thin scaffolding only: undirected gold on `ℕ`, its reflexive-transitive
closure, and the component of `5`. No full hire-graph rebuild. Proof deferred.
-/

namespace Hire

/-- `n` is a 2-power door when its 3-free door is a pure power of two. -/
def IsTwoPowerDoor (n : ℕ) : Prop :=
  ∃ k : ℕ, m0 n = 2 ^ k

/-- Undirected gold chord on naturals (no owner window): mutual door-factor
relation between primes other than `3`. -/
def UndirectedGold (a b : ℕ) : Prop :=
  a ≠ b ∧ a.Prime ∧ b.Prime ∧ a ≠ 3 ∧ b ≠ 3 ∧ (b ∣ m0 a ∨ a ∣ m0 b)

/-- Path-connected in the undirected gold graph. -/
def GoldConnected : ℕ → ℕ → Prop :=
  Relation.ReflTransGen UndirectedGold

/-- Membership in the infinite undirected-gold component of `5`. -/
def InGoldComponentOf5 (n : ℕ) : Prop :=
  GoldConnected 5 n

/-- **Weak Q2.** Every 2-power-door Mersenne prime (other than `3`) lies in the
infinite undirected-gold component of `5`. -/
theorem weak_Q2
    (p : ℕ) (_hp : p.Prime)
    (hM : Nat.Prime (2 ^ p - 1))
    (h3 : 2 ^ p - 1 ≠ 3)
    (hdoor : IsTwoPowerDoor (2 ^ p - 1)) :
    InGoldComponentOf5 (2 ^ p - 1) := by
  -- Strategy sketch: absorb the Mersenne island through a connecting bridge
  -- owner (cf. `WitnessXstar`), then path-connect to the mainland component of 5.
  -- Global persistence / infinitude of such bridges is not yet formalized.
  sorry

/-- Convenience: Mersenne form of a 2-power door that is prime. -/
abbrev IsMersenneTwoPowerDoor (M : ℕ) : Prop :=
  (∃ p : ℕ, p.Prime ∧ M = 2 ^ p - 1) ∧ Nat.Prime M ∧ IsTwoPowerDoor M ∧ M ≠ 3

/-- Equivalent packaging of weak Q2 on the Mersenne number itself. -/
theorem weak_Q2_of_mersenne
    (M : ℕ) (h : IsMersenneTwoPowerDoor M) :
    InGoldComponentOf5 M := by
  obtain ⟨⟨p, _hp, rfl⟩, hM, hdoor, h3⟩ := h
  exact weak_Q2 p _hp hM h3 hdoor

end Hire
