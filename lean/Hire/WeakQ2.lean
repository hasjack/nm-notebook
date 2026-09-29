/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Doors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Relation

/-!
# Infinite undirected gold

`UndirectedGold` is a door-factor chord between primes other than `2` and `3`.
The hub `2` divides every such door, so it is excluded: otherwise `5—2—q`
would put every odd prime in the component of `5`.
`InGoldComponentOf5` is the path-component of `5`. The membership theorem is
`mersenne_two_power_door_in_gold_component_of_5` in `GoldBridge.lean`.
-/

namespace Hire

/-- `n` is a 2-power door when its 3-free door is a pure power of two. -/
def IsTwoPowerDoor (n : ℕ) : Prop :=
  ∃ k : ℕ, m0 n = 2 ^ k

/-- Undirected gold chord on naturals (no owner window): mutual door-factor
relation between primes other than `2` and `3`. -/
def UndirectedGold (a b : ℕ) : Prop :=
  a ≠ b ∧ a.Prime ∧ b.Prime ∧ a ≠ 2 ∧ b ≠ 2 ∧ a ≠ 3 ∧ b ≠ 3 ∧
    (b ∣ m0 a ∨ a ∣ m0 b)

/-- The hub `2` is not a left endpoint of an undirected gold chord. -/
theorem not_undirectedGold_left_two (b : ℕ) : ¬ UndirectedGold 2 b :=
  fun h => h.2.2.2.1 rfl

/-- The hub `2` is not a right endpoint of an undirected gold chord. -/
theorem not_undirectedGold_right_two (a : ℕ) : ¬ UndirectedGold a 2 :=
  fun h => h.2.2.2.2.1 rfl

/-- Path-connected in the undirected gold graph. -/
def GoldConnected : ℕ → ℕ → Prop :=
  Relation.ReflTransGen UndirectedGold

/-- Membership in the infinite undirected-gold component of `5`. -/
def InGoldComponentOf5 (n : ℕ) : Prop :=
  GoldConnected 5 n

end Hire
