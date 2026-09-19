/-
Copyright (c) 2026 Jack Pickett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Pickett
-/
import Hire.Doors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Black-swan connecting witness `X*`

Hand-checkable witness at the first connecting window of the undirected-gold
hire graph (not the full scan). At `X* = 92274421` the Mersenne island
`524287 = 2^19 - 1` joins the mainland through the bridge prime
`q = 46137211`, via two new gold arcs `q → 11` and `q → 1048573`.

All primality and door-factor facts below are closed by `native_decide`.
-/

namespace Hire

/-- First connecting owner window from the gold-connect binary search. -/
def Xstar : ℕ := 92274421

/-- Bridge prime hired by `m0 Xstar`; source of the two connecting gold arcs. -/
def bridgePrime : ℕ := 46137211

/-- Mersenne island `2^19 - 1` (2-power door). -/
def islandM19 : ℕ := 524287

/-- Island satellite hired via `m0 bridgePrime`. -/
def islandSat : ℕ := 1048573

/-- Larger island satellite with door divisible by `islandM19`. -/
def islandSatBig : ℕ := 8388593

/-! ### Primality of the five witness primes -/

theorem Xstar_prime : Nat.Prime Xstar := by native_decide
theorem bridgePrime_prime : Nat.Prime bridgePrime := by native_decide
theorem islandM19_prime : Nat.Prime islandM19 := by native_decide
theorem islandSat_prime : Nat.Prime islandSat := by native_decide
theorem islandSatBig_prime : Nat.Prime islandSatBig := by native_decide

/-! ### Door factorizations via `m0` -/

theorem m0_Xstar : m0 Xstar = 2 * bridgePrime := by native_decide
theorem m0_bridgePrime : m0 bridgePrime = 2 ^ 2 * 11 * islandSat := by native_decide
theorem m0_islandM19 : m0 islandM19 = 2 ^ 19 := by native_decide
theorem islandM19_eq_Mersenne : islandM19 = 2 ^ 19 - 1 := by native_decide
theorem m0_islandSat : m0 islandSat = 2 * islandM19 := by native_decide
theorem m0_islandSatBig : m0 islandSatBig = 2 ^ 4 * islandM19 := by native_decide

/-! ### Connecting gold arcs at the window (door-divisibility) -/

/-- Mainland arc: `bridgePrime → 11`. -/
theorem bridgePrime_dvd_arc_mainland : 11 ∣ m0 bridgePrime := by native_decide

/-- Island arc: `bridgePrime → 1048573`. -/
theorem bridgePrime_dvd_arc_island : islandSat ∣ m0 bridgePrime := by native_decide

/-- Bridge itself is hired from the connecting owner. -/
theorem bridgePrime_dvd_m0_Xstar : bridgePrime ∣ m0 Xstar := by native_decide

end Hire
