import Mathlib
import Hire.Doors

namespace HireDoorSieve

/-- Ordered repeated-factor pairs with product at most Y,
restricted to a finite rectangle. -/
def repeatedFactorPairs (Y M V : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 V)).filter
    (fun t => t.1 ≤ t.2 ∧ t.1 * t.2 ^ 2 ≤ Y)

/-- The repeated-factor pairs occupy at most M * V slots. -/
theorem repeatedFactorPairs_card_le
    (Y M V : ℕ) :
    (repeatedFactorPairs Y M V).card ≤ M * V := by
  calc
    _ ≤ ((Finset.Icc 1 M) ×ˢ
        (Finset.Icc 1 V)).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = M * V := by
      simp

/-- Ordering forces the smaller factor's cube below the product. -/
theorem cube_le_repeated_product
    {u v Y : ℕ}
    (huv : u ≤ v)
    (hsize : u * v ^ 2 ≤ Y) :
    u ^ 3 ≤ Y := by
  have hsquare : u ^ 2 ≤ v ^ 2 := by
    nlinarith
  calc
    u ^ 3 = u * u ^ 2 := by ring
    _ ≤ u * v ^ 2 :=
      Nat.mul_le_mul_left u hsquare
    _ ≤ Y := hsize

/-- A positive smaller factor also bounds the larger factor's square. -/
theorem square_le_repeated_product
    {u v Y : ℕ}
    (hu : 1 ≤ u)
    (hsize : u * v ^ 2 ≤ Y) :
    v ^ 2 ≤ Y := by
  calc
    v ^ 2 = 1 * v ^ 2 := by simp
    _ ≤ u * v ^ 2 :=
      Nat.mul_le_mul_right (v ^ 2) hu
    _ ≤ Y := hsize

/-- Suitable cube and square cutoffs capture every admissible pair. -/
theorem mem_repeatedFactorPairs
    {u v Y M V : ℕ}
    (hu : 1 ≤ u)
    (hv : 1 ≤ v)
    (huv : u ≤ v)
    (hsize : u * v ^ 2 ≤ Y)
    (hM : ∀ n : ℕ, n ^ 3 ≤ Y → n ≤ M)
    (hV : ∀ n : ℕ, n ^ 2 ≤ Y → n ≤ V) :
    (u, v) ∈ repeatedFactorPairs Y M V := by
  have hum : u ≤ M :=
    hM u (cube_le_repeated_product huv hsize)
  have hvv : v ≤ V :=
    hV v (square_le_repeated_product hu hsize)
  simp [repeatedFactorPairs, hu, hv, hum, hvv, huv, hsize]

/-- A uniform per-pair weight bound gives a rectangle weight bound. -/
theorem sum_repeatedFactorPairs_weight_le
    (Y M V : ℕ)
    (w : ℕ × ℕ → ℝ)
    (L : ℝ)
    (hL : 0 ≤ L)
    (hw : ∀ t ∈ repeatedFactorPairs Y M V, w t ≤ L) :
    (∑ t ∈ repeatedFactorPairs Y M V, w t) ≤
      (M : ℝ) * (V : ℝ) * L := by
  have hcard :
      ((repeatedFactorPairs Y M V).card : ℝ) ≤
        (M : ℝ) * (V : ℝ) := by
    exact_mod_cast repeatedFactorPairs_card_le Y M V
  calc
    _ ≤ ∑ _t ∈ repeatedFactorPairs Y M V, L := by
      apply Finset.sum_le_sum
      intro t ht
      exact hw t ht
    _ = ((repeatedFactorPairs Y M V).card : ℝ) * L := by
      simp
    _ ≤ ((M : ℝ) * (V : ℝ)) * L :=
      mul_le_mul_of_nonneg_right hcard hL

/-- The same bound controls the absolute value of a signed sum. -/
theorem abs_sum_repeatedFactorPairs_weight_le
    (Y M V : ℕ)
    (w : ℕ × ℕ → ℝ)
    (L : ℝ)
    (hL : 0 ≤ L)
    (hw : ∀ t ∈ repeatedFactorPairs Y M V, |w t| ≤ L) :
    |∑ t ∈ repeatedFactorPairs Y M V, w t| ≤
      (M : ℝ) * (V : ℝ) * L := by
  calc
    _ ≤ ∑ t ∈ repeatedFactorPairs Y M V, |w t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ (M : ℝ) * (V : ℝ) * L :=
      sum_repeatedFactorPairs_weight_le
        Y M V (fun t => |w t|) L hL hw

/-- Integer cube-root cutoff, defined by a finite maximum. -/
def cubeRootCutoff (Y : ℕ) : ℕ :=
  ((Finset.range (Y + 1)).filter
    (fun n => n ^ 3 ≤ Y)).sup id

/-- Integer square-root cutoff, defined by a finite maximum. -/
def squareRootCutoff (Y : ℕ) : ℕ :=
  ((Finset.range (Y + 1)).filter
    (fun n => n ^ 2 ≤ Y)).sup id

theorem le_cubeRootCutoff
    {n Y : ℕ} (h : n ^ 3 ≤ Y) :
    n ≤ cubeRootCutoff Y := by
  have hsquare : n ≤ n ^ 2 := by
    nlinarith
  have hmul : n * n ≤ n * n ^ 2 :=
    Nat.mul_le_mul_left n hsquare
  have hnY : n ≤ Y := by
    nlinarith
  have hmem :
      n ∈ (Finset.range (Y + 1)).filter
        (fun j => j ^ 3 ≤ Y) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h⟩
  change n ≤
    ((Finset.range (Y + 1)).filter
      (fun j => j ^ 3 ≤ Y)).sup id
  exact Finset.le_sup (f := fun j : ℕ => j) hmem

theorem le_squareRootCutoff
    {n Y : ℕ} (h : n ^ 2 ≤ Y) :
    n ≤ squareRootCutoff Y := by
  have hnY : n ≤ Y := by
    nlinarith
  have hmem :
      n ∈ (Finset.range (Y + 1)).filter
        (fun j => j ^ 2 ≤ Y) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h⟩
  change n ≤
    ((Finset.range (Y + 1)).filter
      (fun j => j ^ 2 ≤ Y)).sup id
  exact Finset.le_sup (f := fun j : ℕ => j) hmem

/-- Every positive ordered repeated-factor pair fits in
the rectangle given by the integer root cutoffs. -/
theorem mem_repeatedFactorPairs_root_cutoffs
    {u v Y : ℕ}
    (hu : 1 ≤ u)
    (hv : 1 ≤ v)
    (huv : u ≤ v)
    (hsize : u * v ^ 2 ≤ Y) :
    (u, v) ∈ repeatedFactorPairs Y
      (cubeRootCutoff Y) (squareRootCutoff Y) := by
  exact mem_repeatedFactorPairs hu hv huv hsize
    (fun _ hn => le_cubeRootCutoff hn)
    (fun _ hn => le_squareRootCutoff hn)

/-- The weighted rectangle estimate with canonical root cutoffs. -/
theorem abs_sum_repeatedFactorPairs_root_cutoffs_le
    (Y : ℕ)
    (w : ℕ × ℕ → ℝ)
    (L : ℝ)
    (hL : 0 ≤ L)
    (hw : ∀ t ∈ repeatedFactorPairs Y
      (cubeRootCutoff Y) (squareRootCutoff Y),
      |w t| ≤ L) :
    |∑ t ∈ repeatedFactorPairs Y
        (cubeRootCutoff Y) (squareRootCutoff Y), w t| ≤
      (cubeRootCutoff Y : ℝ) *
        (squareRootCutoff Y : ℝ) * L := by
  exact abs_sum_repeatedFactorPairs_weight_le
    Y (cubeRootCutoff Y) (squareRootCutoff Y)
    w L hL hw

/-- A finite maximum preserves a common power bound. -/
theorem finset_sup_pow_le
    (k Y : ℕ)
    (hzero : (0 : ℕ) ^ k ≤ Y)
    (s : Finset ℕ)
    (h : ∀ n ∈ s, n ^ k ≤ Y) :
    (s.sup id) ^ k ≤ Y := by
  have hgeneral :
      ∀ t : Finset ℕ,
        (∀ n ∈ t, n ^ k ≤ Y) →
          (t.sup id) ^ k ≤ Y := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        simpa using hzero
    | @insert a t hat ih =>
        intro ht
        have ha : a ^ k ≤ Y :=
          ht a (by simp)
        have hrest : (t.sup id) ^ k ≤ Y := by
          apply ih
          intro n hn
          exact ht n (by simp [hn])
        rw [Finset.sup_insert]
        change (max a (t.sup id)) ^ k ≤ Y
        rcases le_total a (t.sup id) with hle | hle
        · rw [max_eq_right hle]
          exact hrest
        · rw [max_eq_left hle]
          exact ha
  exact hgeneral s h

theorem cubeRootCutoff_cube_le (Y : ℕ) :
    cubeRootCutoff Y ^ 3 ≤ Y := by
  unfold cubeRootCutoff
  apply finset_sup_pow_le 3 Y (by simp)
  intro n hn
  exact (Finset.mem_filter.mp hn).2

theorem squareRootCutoff_square_le (Y : ℕ) :
    squareRootCutoff Y ^ 2 ≤ Y := by
  unfold squareRootCutoff
  apply finset_sup_pow_le 2 Y (by simp)
  intro n hn
  exact (Finset.mem_filter.mp hn).2

/-- The root rectangle's area satisfies a sixth-power bound. -/
theorem rootCutoff_product_pow_six_le (Y : ℕ) :
    (cubeRootCutoff Y * squareRootCutoff Y) ^ 6 ≤
      Y ^ 5 := by
  have hcube := cubeRootCutoff_cube_le Y
  have hsquare := squareRootCutoff_square_le Y
  have hcube2 :
      (cubeRootCutoff Y ^ 3) ^ 2 ≤ Y ^ 2 := by
    gcongr
  have hsquare3 :
      (squareRootCutoff Y ^ 2) ^ 3 ≤ Y ^ 3 := by
    gcongr
  calc
    _ = (cubeRootCutoff Y ^ 3) ^ 2 *
        (squareRootCutoff Y ^ 2) ^ 3 := by
      ring
    _ ≤ Y ^ 2 * Y ^ 3 :=
      Nat.mul_le_mul hcube2 hsquare3
    _ = Y ^ 5 := by ring

/-- The number of admissible pairs satisfies the same bound. -/
theorem repeatedFactorPairs_card_pow_six_le (Y : ℕ) :
    (repeatedFactorPairs Y
      (cubeRootCutoff Y) (squareRootCutoff Y)).card ^ 6 ≤
        Y ^ 5 := by
  have hcard := repeatedFactorPairs_card_le
    Y (cubeRootCutoff Y) (squareRootCutoff Y)
  calc
    _ ≤ (cubeRootCutoff Y * squareRootCutoff Y) ^ 6 := by
      gcongr
    _ ≤ Y ^ 5 := rootCutoff_product_pow_six_le Y

/-- Translate a sixth-power bound into a real fractional-power bound. -/
theorem le_rpow_five_sixths_of_pow_six_le
    {C Y : ℝ}
    (hC : 0 ≤ C)
    (hY : 0 ≤ Y)
    (hpow : C ^ 6 ≤ Y ^ 5) :
    C ≤ Real.rpow Y (5 / 6 : ℝ) := by
  have hroot :=
    Real.rpow_le_rpow
      (pow_nonneg hC 6) hpow
      (by norm_num : (0 : ℝ) ≤ 1 / 6)
  rw [← Real.rpow_natCast, ← Real.rpow_natCast] at hroot
  rw [← Real.rpow_mul hC, ← Real.rpow_mul hY] at hroot
  convert hroot using 1 <;> norm_num

/-- The root rectangle has area at most Y^(5/6). -/
theorem rootCutoff_product_le_rpow (Y : ℕ) :
    (cubeRootCutoff Y : ℝ) *
      (squareRootCutoff Y : ℝ) ≤
        Real.rpow (Y : ℝ) (5 / 6 : ℝ) := by
  apply le_rpow_five_sixths_of_pow_six_le
    (by positivity) (by positivity)
  exact_mod_cast rootCutoff_product_pow_six_le Y

/-- The weighted repeated-factor rectangle has a sublinear bound. -/
theorem abs_sum_repeatedFactorPairs_le_rpow
    (Y : ℕ)
    (w : ℕ × ℕ → ℝ)
    (L : ℝ)
    (hL : 0 ≤ L)
    (hw : ∀ t ∈ repeatedFactorPairs Y
      (cubeRootCutoff Y) (squareRootCutoff Y),
      |w t| ≤ L) :
    |∑ t ∈ repeatedFactorPairs Y
        (cubeRootCutoff Y) (squareRootCutoff Y), w t| ≤
      Real.rpow (Y : ℝ) (5 / 6 : ℝ) * L := by
  calc
    _ ≤ (cubeRootCutoff Y : ℝ) *
        (squareRootCutoff Y : ℝ) * L :=
      abs_sum_repeatedFactorPairs_root_cutoffs_le
        Y w L hL hw
    _ ≤ Real.rpow (Y : ℝ) (5 / 6 : ℝ) * L :=
      mul_le_mul_of_nonneg_right
        (rootCutoff_product_le_rpow Y) hL

/-- Logarithmic weight of a prime owner inside the window. -/
noncomputable def primeOwnerLogWeight (X p : ℕ) : ℝ :=
  if p.Prime ∧ p ≤ X then Real.log (p : ℝ) else 0

theorem primeOwnerLogWeight_nonneg (X p : ℕ) :
    0 ≤ primeOwnerLogWeight X p := by
  unfold primeOwnerLogWeight
  split_ifs with h
  · apply Real.log_nonneg
    exact_mod_cast h.1.one_lt.le
  · rfl

theorem primeOwnerLogWeight_le_log
    {X : ℕ} (hX : 1 ≤ X) (p : ℕ) :
    primeOwnerLogWeight X p ≤ Real.log (X : ℝ) := by
  unfold primeOwnerLogWeight
  split_ifs with h
  · apply Real.log_le_log
    · exact_mod_cast h.1.pos
    · exact_mod_cast h.2
  · apply Real.log_nonneg
    exact_mod_cast hX

/-- Unsigned weight of both possible owners of A*u*v².
This can overcount; it supplies an upper bound. -/
noncomputable def repeatedPairOwnerMass
    (X A : ℕ) (t : ℕ × ℕ) : ℝ :=
  primeOwnerLogWeight X (A * t.1 * t.2 ^ 2 - 1) +
    primeOwnerLogWeight X (A * t.1 * t.2 ^ 2 + 1)

theorem repeatedPairOwnerMass_nonneg
    (X A : ℕ) (t : ℕ × ℕ) :
    0 ≤ repeatedPairOwnerMass X A t := by
  exact add_nonneg
    (primeOwnerLogWeight_nonneg _ _)
    (primeOwnerLogWeight_nonneg _ _)

theorem repeatedPairOwnerMass_le
    {X : ℕ} (hX : 1 ≤ X)
    (A : ℕ) (t : ℕ × ℕ) :
    repeatedPairOwnerMass X A t ≤
      2 * Real.log (X : ℝ) := by
  have hm := primeOwnerLogWeight_le_log hX
    (A * t.1 * t.2 ^ 2 - 1)
  have hp := primeOwnerLogWeight_le_log hX
    (A * t.1 * t.2 ^ 2 + 1)
  unfold repeatedPairOwnerMass
  linarith

/-- Prime-owner mass in the root rectangle has a sublinear bound. -/
theorem sum_repeatedPairOwnerMass_le
    {X : ℕ} (hX : 1 ≤ X)
    (A Y : ℕ) :
    (∑ t ∈ repeatedFactorPairs Y
        (cubeRootCutoff Y) (squareRootCutoff Y),
      repeatedPairOwnerMass X A t) ≤
      2 * Real.rpow (Y : ℝ) (5 / 6 : ℝ) *
        Real.log (X : ℝ) := by
  have hlog : 0 ≤ Real.log (X : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hX
  have hbound :=
    abs_sum_repeatedFactorPairs_le_rpow
      Y (repeatedPairOwnerMass X A)
      (2 * Real.log (X : ℝ))
      (by positivity)
      (by
        intro t ht
        rw [abs_of_nonneg
          (repeatedPairOwnerMass_nonneg X A t)]
        exact repeatedPairOwnerMass_le hX A t)
  have hsum :
      0 ≤ ∑ t ∈ repeatedFactorPairs Y
        (cubeRootCutoff Y) (squareRootCutoff Y),
        repeatedPairOwnerMass X A t := by
    apply Finset.sum_nonneg
    intro t ht
    exact repeatedPairOwnerMass_nonneg X A t
  rw [abs_of_nonneg hsum] at hbound
  calc
    _ ≤ Real.rpow (Y : ℝ) (5 / 6 : ℝ) *
        (2 * Real.log (X : ℝ)) := hbound
    _ = _ := by ring

/-- Either adjacent owner puts the factored door below X + 1. -/
theorem repeated_product_le_owner_window
    {p X A u v : ℕ}
    (hpX : p ≤ X)
    (hdoor :
      p + 1 = A * u * v ^ 2 ∨
      p = A * u * v ^ 2 + 1) :
    A * u * v ^ 2 ≤ X + 1 := by
  rcases hdoor with hplus | hminus
  · omega
  · omega

/-- Natural-number division supplies the correct cofactor cutoff. -/
theorem repeated_product_le_div_cutoff
    {p X A u v : ℕ}
    (hA : 0 < A)
    (hpX : p ≤ X)
    (hdoor :
      p + 1 = A * u * v ^ 2 ∨
      p = A * u * v ^ 2 + 1) :
    u * v ^ 2 ≤ (X + 1) / A := by
  apply (Nat.le_div_iff_mul_le hA).2
  calc
    u * v ^ 2 * A = A * u * v ^ 2 := by ring
    _ ≤ X + 1 :=
      repeated_product_le_owner_window hpX hdoor

/-- Every positive ordered pair with an owner in the window
is captured by the quotient's root rectangle. -/
theorem repeated_owner_pair_mem_window
    {p X A u v : ℕ}
    (hA : 0 < A)
    (hpX : p ≤ X)
    (hu : 1 ≤ u)
    (hv : 1 ≤ v)
    (huv : u ≤ v)
    (hdoor :
      p + 1 = A * u * v ^ 2 ∨
      p = A * u * v ^ 2 + 1) :
    (u, v) ∈ repeatedFactorPairs ((X + 1) / A)
      (cubeRootCutoff ((X + 1) / A))
      (squareRootCutoff ((X + 1) / A)) := by
  exact mem_repeatedFactorPairs_root_cutoffs
    hu hv huv
    (repeated_product_le_div_cutoff hA hpX hdoor)

/-- Owner mass for a fixed multiplier uses the quotient cutoff. -/
theorem sum_repeatedPairOwnerMass_window_le
    {X : ℕ} (hX : 1 ≤ X)
    (A : ℕ) :
    (∑ t ∈ repeatedFactorPairs ((X + 1) / A)
        (cubeRootCutoff ((X + 1) / A))
        (squareRootCutoff ((X + 1) / A)),
      repeatedPairOwnerMass X A t) ≤
      2 * Real.rpow (((X + 1) / A : ℕ) : ℝ)
        (5 / 6 : ℝ) * Real.log (X : ℝ) := by
  exact sum_repeatedPairOwnerMass_le
    hX A ((X + 1) / A)

/-- Remove the natural-number division from the fractional-power bound. -/
theorem div_cutoff_rpow_le
    (X A : ℕ) :
    Real.rpow (((X + 1) / A : ℕ) : ℝ) (5 / 6 : ℝ) ≤
      Real.rpow ((X : ℝ) + 1) (5 / 6 : ℝ) /
        Real.rpow (A : ℝ) (5 / 6 : ℝ) := by
  have hdiv :
      (((X + 1) / A : ℕ) : ℝ) ≤
        ((X : ℝ) + 1) / (A : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.cast_div_le :
        (((X + 1) / A : ℕ) : ℝ) ≤
          ((X + 1 : ℕ) : ℝ) / (A : ℝ))
  calc
    _ ≤ Real.rpow (((X : ℝ) + 1) / (A : ℝ))
        (5 / 6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hdiv (by norm_num)
    _ = _ := by
      have hx : 0 ≤ (X : ℝ) + 1 := by positivity
      have ha : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
      simpa only [Real.rpow_eq_pow] using
        (Real.div_rpow hx ha (5 / 6 : ℝ))

/-- The fixed-multiplier estimate with its decay factor explicit. -/
theorem sum_repeatedPairOwnerMass_window_le_explicit
    {X : ℕ} (hX : 1 ≤ X)
    (A : ℕ) :
    (∑ t ∈ repeatedFactorPairs ((X + 1) / A)
        (cubeRootCutoff ((X + 1) / A))
        (squareRootCutoff ((X + 1) / A)),
      repeatedPairOwnerMass X A t) ≤
      (2 * Real.rpow ((X : ℝ) + 1) (5 / 6 : ℝ) *
        Real.log (X : ℝ)) *
          (Real.rpow (A : ℝ) (5 / 6 : ℝ))⁻¹ := by
  have hlog : 0 ≤ Real.log (X : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hX
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (div_cutoff_rpow_le X A)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog)
  calc
    _ ≤ 2 *
        Real.rpow (((X + 1) / A : ℕ) : ℝ)
          (5 / 6 : ℝ) *
        Real.log (X : ℝ) :=
      sum_repeatedPairOwnerMass_window_le hX A
    _ ≤ (2 * Real.rpow ((X : ℝ) + 1) (5 / 6 : ℝ) *
        Real.log (X : ℝ)) *
          (Real.rpow (A : ℝ) (5 / 6 : ℝ))⁻¹ := by
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm,
        mul_left_comm] using hscaled

/-- A finite geometric sum is bounded by the infinite-series value. -/
theorem geometric_range_sum_le
    (r : ℝ) (n : ℕ)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑ i ∈ Finset.range n, r ^ i) ≤ 1 / (1 - r) := by
  have hidentity :
      (∑ i ∈ Finset.range n, r ^ i) * (1 - r) =
        1 - r ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        nlinarith [ih]
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  nlinarith [pow_nonneg hr n]

/-- Starting the exponent at one contributes an extra factor r. -/
theorem geometric_shifted_range_sum_le
    (r : ℝ) (n : ℕ)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (∑ i ∈ Finset.range n, r ^ (i + 1)) ≤
      r / (1 - r) := by
  calc
    _ = r * (∑ i ∈ Finset.range n, r ^ i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
    _ ≤ r * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left
        (geometric_range_sum_le r n hr hr1) hr
    _ = r / (1 - r) := by ring

/-- The three exponent sums factor exactly. -/
theorem smooth_geometric_box_eq
    (r₂ r₃ r₅ : ℝ) (na nb nc : ℕ) :
    (∑ a ∈ Finset.range na,
      ∑ b ∈ Finset.range nb,
        ∑ c ∈ Finset.range nc,
          r₂ ^ (a + 1) * r₃ ^ b * r₅ ^ (c + 1)) =
      (∑ a ∈ Finset.range na, r₂ ^ (a + 1)) *
        (∑ b ∈ Finset.range nb, r₃ ^ b) *
          (∑ c ∈ Finset.range nc, r₅ ^ (c + 1)) := by
  symm
  calc
    _ = ∑ a ∈ Finset.range na,
        r₂ ^ (a + 1) *
          ((∑ b ∈ Finset.range nb, r₃ ^ b) *
            (∑ c ∈ Finset.range nc, r₅ ^ (c + 1))) := by
      rw [mul_assoc, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring

/-- A uniform bound for every finite box of smooth exponents. -/
theorem smooth_geometric_box_le
    (r₂ r₃ r₅ : ℝ) (na nb nc : ℕ)
    (h₂ : 0 ≤ r₂) (h₂1 : r₂ < 1)
    (h₃ : 0 ≤ r₃) (h₃1 : r₃ < 1)
    (h₅ : 0 ≤ r₅) (h₅1 : r₅ < 1) :
    (∑ a ∈ Finset.range na,
      ∑ b ∈ Finset.range nb,
        ∑ c ∈ Finset.range nc,
          r₂ ^ (a + 1) * r₃ ^ b * r₅ ^ (c + 1)) ≤
      (r₂ / (1 - r₂)) *
        (1 / (1 - r₃)) *
          (r₅ / (1 - r₅)) := by
  rw [smooth_geometric_box_eq]
  have ha :=
    geometric_shifted_range_sum_le r₂ na h₂ h₂1
  have hb :=
    geometric_range_sum_le r₃ nb h₃ h₃1
  have hc :=
    geometric_shifted_range_sum_le r₅ nc h₅ h₅1
  have hab :
      (∑ a ∈ Finset.range na, r₂ ^ (a + 1)) *
        (∑ b ∈ Finset.range nb, r₃ ^ b) ≤
      (r₂ / (1 - r₂)) * (1 / (1 - r₃)) := by
    apply mul_le_mul ha hb
    · exact Finset.sum_nonneg
        (fun _ _ => pow_nonneg h₃ _)
    · exact div_nonneg h₂ (sub_pos.mpr h₂1).le
  apply mul_le_mul hab hc
  · exact Finset.sum_nonneg
      (fun _ _ => pow_nonneg h₅ _)
  · exact mul_nonneg
      (div_nonneg h₂ (sub_pos.mpr h₂1).le)
      (div_nonneg (by norm_num) (sub_pos.mpr h₃1).le)

/-- Real fractional powers commute with natural-number powers. -/
theorem rpow_nat_pow_eq
    (x t : ℝ) (n : ℕ)
    (hx : 0 ≤ x) :
    Real.rpow (x ^ n) t = (Real.rpow x t) ^ n := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [← Real.rpow_mul hx, ← Real.rpow_mul hx]
  congr 1
  ring

/-- The allowed smooth multiplier, with positive 2- and 5-exponents. -/
def repeatedDoorMultiplier (a b c : ℕ) : ℕ :=
  2 ^ (a + 1) * 3 ^ b * 5 ^ (c + 1)

/-- Its real fractional power separates into three factors. -/
theorem repeatedDoorMultiplier_rpow
    (a b c : ℕ) (t : ℝ) :
    Real.rpow (repeatedDoorMultiplier a b c : ℝ) t =
      (Real.rpow 2 t) ^ (a + 1) *
        (Real.rpow 3 t) ^ b *
          (Real.rpow 5 t) ^ (c + 1) := by
  have hcast :
      (repeatedDoorMultiplier a b c : ℝ) =
        (2 : ℝ) ^ (a + 1) *
          (3 : ℝ) ^ b * (5 : ℝ) ^ (c + 1) := by
    simp [repeatedDoorMultiplier]
  rw [hcast]
  have houter :
      Real.rpow
        ((2 : ℝ) ^ (a + 1) * (3 : ℝ) ^ b *
          (5 : ℝ) ^ (c + 1)) t =
      Real.rpow
        ((2 : ℝ) ^ (a + 1) * (3 : ℝ) ^ b) t *
      Real.rpow ((5 : ℝ) ^ (c + 1)) t := by
    simpa only [Real.rpow_eq_pow] using
      (Real.mul_rpow
        (show 0 ≤ (2 : ℝ) ^ (a + 1) * (3 : ℝ) ^ b
          from by positivity)
        (show 0 ≤ (5 : ℝ) ^ (c + 1) from by positivity))
  have hinner :
      Real.rpow ((2 : ℝ) ^ (a + 1) * (3 : ℝ) ^ b) t =
      Real.rpow ((2 : ℝ) ^ (a + 1)) t *
        Real.rpow ((3 : ℝ) ^ b) t := by
    simpa only [Real.rpow_eq_pow] using
      (Real.mul_rpow
        (show 0 ≤ (2 : ℝ) ^ (a + 1) from by positivity)
        (show 0 ≤ (3 : ℝ) ^ b from by positivity))
  rw [houter, hinner]
  rw [rpow_nat_pow_eq 2 t (a + 1) (by norm_num),
    rpow_nat_pow_eq 3 t b (by norm_num),
    rpow_nat_pow_eq 5 t (c + 1) (by norm_num)]

/-- Inverting exposes the geometric ratios for the multiplier weight. -/
theorem repeatedDoorMultiplier_inverse_rpow
    (a b c : ℕ) (t : ℝ) :
    (Real.rpow (repeatedDoorMultiplier a b c : ℝ) t)⁻¹ =
      ((Real.rpow 2 t)⁻¹) ^ (a + 1) *
        ((Real.rpow 3 t)⁻¹) ^ b *
          ((Real.rpow 5 t)⁻¹) ^ (c + 1) := by
  rw [repeatedDoorMultiplier_rpow]
  simp only [mul_inv_rev, inv_pow]
  ring

/-- Positive powers of a base above one have inverse between zero and one. -/
theorem inverse_rpow_between_zero_one
    {x t : ℝ}
    (hx : 1 < x) (ht : 0 < t) :
    0 ≤ (Real.rpow x t)⁻¹ ∧
      (Real.rpow x t)⁻¹ < 1 := by
  have hgt : 1 < Real.rpow x t := by
    simpa only [Real.rpow_eq_pow, Real.one_rpow] using
      (Real.rpow_lt_rpow
        (by norm_num : (0 : ℝ) ≤ 1) hx ht)
  have hpos : 0 < Real.rpow x t := lt_trans zero_lt_one hgt
  exact ⟨(inv_pos.mpr hpos).le, (inv_lt_one₀ hpos).2 hgt⟩

/-- The rectangle's unsigned owner mass for a fixed multiplier. -/
noncomputable def repeatedMultiplierOwnerMass
    (X A : ℕ) : ℝ :=
  ∑ t ∈ repeatedFactorPairs ((X + 1) / A)
      (cubeRootCutoff ((X + 1) / A))
      (squareRootCutoff ((X + 1) / A)),
    repeatedPairOwnerMass X A t

/-- The three geometric-series factors, without the owner-weight prefactor. -/
noncomputable def repeatedDoorGeometricConstant (t : ℝ) : ℝ :=
  let r₂ := (Real.rpow 2 t)⁻¹
  let r₃ := (Real.rpow 3 t)⁻¹
  let r₅ := (Real.rpow 5 t)⁻¹
  (r₂ / (1 - r₂)) *
    (1 / (1 - r₃)) *
      (r₅ / (1 - r₅))

/-- Every finite box of smooth multipliers has the same uniform ceiling. -/
theorem sum_repeatedMultiplierOwnerMass_box_le
    {X : ℕ} (hX : 1 ≤ X)
    (na nb nc : ℕ) :
    (∑ a ∈ Finset.range na,
      ∑ b ∈ Finset.range nb,
        ∑ c ∈ Finset.range nc,
          repeatedMultiplierOwnerMass X
            (repeatedDoorMultiplier a b c)) ≤
      (2 * Real.rpow ((X : ℝ) + 1) (5 / 6 : ℝ) *
        Real.log (X : ℝ)) *
          repeatedDoorGeometricConstant (5 / 6 : ℝ) := by
  let Q : ℝ :=
    2 * Real.rpow ((X : ℝ) + 1) (5 / 6 : ℝ) *
      Real.log (X : ℝ)
  let r₂ : ℝ := (Real.rpow 2 (5 / 6 : ℝ))⁻¹
  let r₃ : ℝ := (Real.rpow 3 (5 / 6 : ℝ))⁻¹
  let r₅ : ℝ := (Real.rpow 5 (5 / 6 : ℝ))⁻¹

  have hlog : 0 ≤ Real.log (X : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hX
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity

  have h₂ : 0 ≤ r₂ ∧ r₂ < 1 :=
    inverse_rpow_between_zero_one (by norm_num) (by norm_num)
  have h₃ : 0 ≤ r₃ ∧ r₃ < 1 :=
    inverse_rpow_between_zero_one (by norm_num) (by norm_num)
  have h₅ : 0 ≤ r₅ ∧ r₅ < 1 :=
    inverse_rpow_between_zero_one (by norm_num) (by norm_num)

  have hbox := smooth_geometric_box_le
    r₂ r₃ r₅ na nb nc
    h₂.1 h₂.2 h₃.1 h₃.2 h₅.1 h₅.2

  calc
    _ ≤ ∑ a ∈ Finset.range na,
        ∑ b ∈ Finset.range nb,
          ∑ c ∈ Finset.range nc,
            Q * (r₂ ^ (a + 1) * r₃ ^ b *
              r₅ ^ (c + 1)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      simpa only [repeatedMultiplierOwnerMass,
        repeatedDoorMultiplier_inverse_rpow, Q, r₂, r₃, r₅] using
        (sum_repeatedPairOwnerMass_window_le_explicit
          hX (repeatedDoorMultiplier a b c))
    _ = Q *
        (∑ a ∈ Finset.range na,
          ∑ b ∈ Finset.range nb,
            ∑ c ∈ Finset.range nc,
              r₂ ^ (a + 1) * r₃ ^ b *
                r₅ ^ (c + 1)) := by
      simp_rw [← Finset.mul_sum]
    _ ≤ Q *
        ((r₂ / (1 - r₂)) *
          (1 / (1 - r₃)) *
            (r₅ / (1 - r₅))) :=
      mul_le_mul_of_nonneg_left hbox hQ
    _ = _ := by
      rfl


/-- An exponent index is smaller than its power when the base is at least two. -/
theorem exponent_lt_power
    {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    n < q ^ n := by
  have h : n + 1 ≤ q ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        nlinarith
  omega

/-- Each exponent index is smaller than the smooth multiplier. -/
theorem repeatedDoorMultiplier_indices_lt
    (a b c : ℕ) :
    a < repeatedDoorMultiplier a b c ∧
      b < repeatedDoorMultiplier a b c ∧
        c < repeatedDoorMultiplier a b c := by
  let x := 2 ^ (a + 1)
  let y := 3 ^ b
  let z := 5 ^ (c + 1)
  have hx : 1 ≤ x := by
    dsimp [x]
    have h : 0 < (2 : ℕ) ^ (a + 1) := by positivity
    omega
  have hy : 1 ≤ y := by
    dsimp [y]
    have h : 0 < (3 : ℕ) ^ b := by positivity
    omega
  have hz : 1 ≤ z := by
    dsimp [z]
    have h : 0 < (5 : ℕ) ^ (c + 1) := by positivity
    omega
  have hxyx : x ≤ x * y := by nlinarith
  have hxyy : y ≤ x * y := by nlinarith
  have hxy : 1 ≤ x * y := by nlinarith
  have hxyz : x * y ≤ x * y * z := by nlinarith
  have hzz : z ≤ x * y * z := by nlinarith
  have ha : a + 1 < x :=
    exponent_lt_power (by norm_num) (a + 1)
  have hb : b < y :=
    exponent_lt_power (by norm_num) b
  have hc : c + 1 < z :=
    exponent_lt_power (by norm_num) (c + 1)
  change a < x * y * z ∧ b < x * y * z ∧ c < x * y * z
  omega

/-- A positive repeated-factor pair cannot have a multiplier
larger than its door. -/
theorem multiplier_le_repeated_product
    {A u v : ℕ}
    (hu : 1 ≤ u) (hv : 1 ≤ v) :
    A ≤ A * u * v ^ 2 := by
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  have hAu : A ≤ A * u := by nlinarith
  have hprod : A * u ≤ A * u * v ^ 2 := by nlinarith
  omega

/-- Every smooth multiplier producing an adjacent owner in the
window belongs to the exponent box of side X + 1. -/
theorem repeated_owner_multiplier_mem_box
    {p X a b c u v : ℕ}
    (hpX : p ≤ X)
    (hu : 1 ≤ u)
    (hv : 1 ≤ v)
    (hdoor :
      p + 1 = repeatedDoorMultiplier a b c * u * v ^ 2 ∨
      p = repeatedDoorMultiplier a b c * u * v ^ 2 + 1) :
    a ∈ Finset.range (X + 1) ∧
      b ∈ Finset.range (X + 1) ∧
        c ∈ Finset.range (X + 1) := by
  have hsize :=
    repeated_product_le_owner_window hpX hdoor
  have hA := multiplier_le_repeated_product
    (A := repeatedDoorMultiplier a b c) hu hv
  have hindices := repeatedDoorMultiplier_indices_lt a b c
  simp only [Finset.mem_range]
  omega

/-- A prime owner's signed contribution for a specified door value. -/
noncomputable def selectedDoorOwnerWeight
    (X d p : ℕ) : ℝ :=
  if p.Prime ∧ p ≤ X then
    (if Hire.m0 p = d then Real.log (p : ℝ) else 0) -
      (if Hire.m1 p = d then Real.log (p : ℝ) else 0)
  else 0

/-- Selecting either door never increases the owner's absolute weight. -/
theorem abs_selectedDoorOwnerWeight_le
    (X d p : ℕ) :
    |selectedDoorOwnerWeight X d p| ≤
      primeOwnerLogWeight X p := by
  by_cases hp : p.Prime ∧ p ≤ X
  · have hlog : 0 ≤ Real.log (p : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hp.1.one_lt.le
    simp only [selectedDoorOwnerWeight,
      primeOwnerLogWeight, ite_eq_left hp]
    split_ifs <;> simp_all [abs_of_nonneg hlog]
  · simp [selectedDoorOwnerWeight, primeOwnerLogWeight, hp]

/-- Signed contribution of the two possible owners of A*u*v².
Only prime remaining factors greater than five are selected. -/
noncomputable def selectedRepeatedPairWeight
    (X A : ℕ) (t : ℕ × ℕ) : ℝ :=
  if t.1.Prime ∧ t.2.Prime ∧ 5 < t.1 ∧ 5 < t.2 then
    let d := A * t.1 * t.2 ^ 2
    selectedDoorOwnerWeight X d (d - 1) +
      selectedDoorOwnerWeight X d (d + 1)
  else 0

/-- The unsigned candidate mass controls the selected signed pair. -/
theorem abs_selectedRepeatedPairWeight_le
    (X A : ℕ) (t : ℕ × ℕ) :
    |selectedRepeatedPairWeight X A t| ≤
      repeatedPairOwnerMass X A t := by
  unfold selectedRepeatedPairWeight
  split_ifs with ht
  · dsimp
    have hm := abs_selectedDoorOwnerWeight_le
      X (A * t.1 * t.2 ^ 2) (A * t.1 * t.2 ^ 2 - 1)
    have hp := abs_selectedDoorOwnerWeight_le
      X (A * t.1 * t.2 ^ 2) (A * t.1 * t.2 ^ 2 + 1)
    obtain ⟨hmlo, hmhi⟩ := abs_le.mp hm
    obtain ⟨hplo, hphi⟩ := abs_le.mp hp
    unfold repeatedPairOwnerMass
    apply abs_le.mpr
    constructor <;> linarith
  · simpa using repeatedPairOwnerMass_nonneg X A t

/-- The selected signed sum for a fixed multiplier is controlled
by its unsigned rectangle mass. -/
theorem abs_sum_selectedRepeatedPairWeight_le
    (X A : ℕ) :
    |∑ t ∈ repeatedFactorPairs ((X + 1) / A)
        (cubeRootCutoff ((X + 1) / A))
        (squareRootCutoff ((X + 1) / A)),
      selectedRepeatedPairWeight X A t| ≤
        repeatedMultiplierOwnerMass X A := by
  calc
    _ ≤ ∑ t ∈ repeatedFactorPairs ((X + 1) / A)
        (cubeRootCutoff ((X + 1) / A))
        (squareRootCutoff ((X + 1) / A)),
        |selectedRepeatedPairWeight X A t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ repeatedMultiplierOwnerMass X A := by
      unfold repeatedMultiplierOwnerMass
      apply Finset.sum_le_sum
      intro t ht
      exact abs_selectedRepeatedPairWeight_le X A t

/-- Selected repeated-factor contributions across the whole window box. -/
noncomputable def selectedRepeatedWindowSum (X : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (X + 1),
    ∑ b ∈ Finset.range (X + 1),
      ∑ c ∈ Finset.range (X + 1),
        ∑ t ∈ repeatedFactorPairs
            ((X + 1) / repeatedDoorMultiplier a b c)
            (cubeRootCutoff
              ((X + 1) / repeatedDoorMultiplier a b c))
            (squareRootCutoff
              ((X + 1) / repeatedDoorMultiplier a b c)),
          selectedRepeatedPairWeight X
            (repeatedDoorMultiplier a b c) t

/-- The complete window box satisfies the uniform sublinear bound. -/
theorem abs_selectedRepeatedWindowSum_le
    {X : ℕ} (hX : 1 ≤ X) :
    |selectedRepeatedWindowSum X| ≤
      (2 * Real.rpow ((X : ℝ) + 1) (5 / 6 : ℝ) *
        Real.log (X : ℝ)) *
          repeatedDoorGeometricConstant (5 / 6 : ℝ) := by
  unfold selectedRepeatedWindowSum
  calc
    _ ≤ ∑ a ∈ Finset.range (X + 1),
        |∑ b ∈ Finset.range (X + 1),
          ∑ c ∈ Finset.range (X + 1),
            ∑ t ∈ repeatedFactorPairs
                ((X + 1) / repeatedDoorMultiplier a b c)
                (cubeRootCutoff
                  ((X + 1) / repeatedDoorMultiplier a b c))
                (squareRootCutoff
                  ((X + 1) / repeatedDoorMultiplier a b c)),
              selectedRepeatedPairWeight X
                (repeatedDoorMultiplier a b c) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (X + 1),
        ∑ b ∈ Finset.range (X + 1),
          ∑ c ∈ Finset.range (X + 1),
            repeatedMultiplierOwnerMass X
              (repeatedDoorMultiplier a b c) := by
      apply Finset.sum_le_sum
      intro a ha
      calc
        _ ≤ ∑ b ∈ Finset.range (X + 1),
            |∑ c ∈ Finset.range (X + 1),
              ∑ t ∈ repeatedFactorPairs
                  ((X + 1) / repeatedDoorMultiplier a b c)
                  (cubeRootCutoff
                    ((X + 1) / repeatedDoorMultiplier a b c))
                  (squareRootCutoff
                    ((X + 1) / repeatedDoorMultiplier a b c)),
                selectedRepeatedPairWeight X
                  (repeatedDoorMultiplier a b c) t| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro b hb
          calc
            _ ≤ ∑ c ∈ Finset.range (X + 1),
                |∑ t ∈ repeatedFactorPairs
                    ((X + 1) / repeatedDoorMultiplier a b c)
                    (cubeRootCutoff
                      ((X + 1) / repeatedDoorMultiplier a b c))
                    (squareRootCutoff
                      ((X + 1) / repeatedDoorMultiplier a b c)),
                  selectedRepeatedPairWeight X
                    (repeatedDoorMultiplier a b c) t| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro c hc
              exact abs_sum_selectedRepeatedPairWeight_le
                X (repeatedDoorMultiplier a b c)
    _ ≤ _ :=
      sum_repeatedMultiplierOwnerMass_box_le
        hX (X + 1) (X + 1) (X + 1)

/-- Prime multiplicities in the repeated-factor cofactor. -/
theorem prime_pair_factorization_at
    {u v : ℕ}
    (hu : u.Prime) (hv : v.Prime)
    (q : ℕ) :
    (u * v ^ 2).factorization q =
      (if u = q then 1 else 0) +
        (if v = q then 2 else 0) := by
  rw [Nat.factorization_mul hu.ne_zero
    (pow_ne_zero 2 hv.ne_zero)]
  rw [hu.factorization, hv.factorization_pow]
  simp [Finsupp.add_apply, Finsupp.single_apply]

/-- Equal ordered repeated-prime products have equal largest factors. -/
theorem ordered_prime_pair_largest_eq
    {u v u' v' : ℕ}
    (hu : u.Prime) (hv : v.Prime)
    (hu' : u'.Prime) (hv' : v'.Prime)
    (huv : u ≤ v) (huv' : u' ≤ v')
    (h : u * v ^ 2 = u' * v' ^ 2) :
    v = v' := by
  have hle : v ≤ v' := by
    by_contra hn
    have hbig : v' < v := by omega
    have hune : u' ≠ v := by omega
    have hvne : v' ≠ v := by omega
    have hf := congrArg (fun n : ℕ => n.factorization v) h
    rw [prime_pair_factorization_at hu hv,
      prime_pair_factorization_at hu' hv'] at hf
    simp only [ite_eq_right hune, ite_eq_right hvne] at hf
    split_ifs at hf <;> omega
  have hle' : v' ≤ v := by
    by_contra hn
    have hbig : v < v' := by omega
    have hune : u ≠ v' := by omega
    have hvne : v ≠ v' := by omega
    have hf := congrArg (fun n : ℕ => n.factorization v') h
    rw [prime_pair_factorization_at hu hv,
      prime_pair_factorization_at hu' hv'] at hf
    simp only [ite_eq_right hune, ite_eq_right hvne] at hf
    split_ifs at hf <;> omega
  omega

/-- The ordered prime pair is uniquely determined by its product. -/
theorem ordered_prime_pair_unique
    {u v u' v' : ℕ}
    (hu : u.Prime) (hv : v.Prime)
    (hu' : u'.Prime) (hv' : v'.Prime)
    (huv : u ≤ v) (huv' : u' ≤ v')
    (h : u * v ^ 2 = u' * v' ^ 2) :
    u = u' ∧ v = v' := by
  have hvv :=
    ordered_prime_pair_largest_eq hu hv hu' hv' huv huv' h
  subst v'
  have huu : u = u' :=
    mul_right_cancel₀ (pow_ne_zero 2 hv.ne_zero) h
  exact ⟨huu, rfl⟩

/-- The two adjacent offsets cannot produce the same owner
when the door is positive. -/
theorem adjacent_owner_offsets_ne
    {d : ℕ} (hd : 0 < d) :
    d - 1 ≠ d + 1 := by
  omega

/-- Prime multiplicities of the complete factored door. -/
theorem repeated_door_factorization_at
    (a b c : ℕ)
    {u v : ℕ}
    (hu : u.Prime) (hv : v.Prime)
    (q : ℕ) :
    (repeatedDoorMultiplier a b c * u * v ^ 2).factorization q =
      (if 2 = q then a + 1 else 0) +
      (if 3 = q then b else 0) +
      (if 5 = q then c + 1 else 0) +
      (if u = q then 1 else 0) +
      (if v = q then 2 else 0) := by
  have h₂ : Nat.Prime 2 := by norm_num
  have h₃ : Nat.Prime 3 := by norm_num
  have h₅ : Nat.Prime 5 := by norm_num
  simp [repeatedDoorMultiplier, Nat.factorization_mul,
    h₂.factorization_pow, h₃.factorization_pow,
    h₅.factorization_pow, hu.factorization,
    hv.factorization_pow, hu.ne_zero, hv.ne_zero,
    Finsupp.add_apply, Finsupp.single_apply, eq_comm]
  split_ifs <;> omega

/-- The door uniquely records the three smooth exponents. -/
theorem repeated_door_smooth_exponents
    (a b c : ℕ)
    {u v : ℕ}
    (hu : u.Prime) (hv : v.Prime)
    (hu5 : 5 < u) (hv5 : 5 < v) :
    (repeatedDoorMultiplier a b c * u * v ^ 2).factorization 2 =
        a + 1 ∧
    (repeatedDoorMultiplier a b c * u * v ^ 2).factorization 3 =
        b ∧
    (repeatedDoorMultiplier a b c * u * v ^ 2).factorization 5 =
        c + 1 := by
  have hu2 : u ≠ 2 := by omega
  have hv2 : v ≠ 2 := by omega
  have hu3 : u ≠ 3 := by omega
  have hv3 : v ≠ 3 := by omega
  have hu5ne : u ≠ 5 := by omega
  have hv5ne : v ≠ 5 := by omega
  constructor
  · rw [repeated_door_factorization_at a b c hu hv 2]
    simp [hu2, hv2]
  constructor
  · rw [repeated_door_factorization_at a b c hu hv 3]
    simp [hu3, hv3]
  · rw [repeated_door_factorization_at a b c hu hv 5]
    simp [hu5ne, hv5ne]

/-- Equal factored doors have equal smooth exponent indices. -/
theorem repeated_door_smooth_indices_unique
    {a b c a' b' c' u v u' v' : ℕ}
    (hu : u.Prime) (hv : v.Prime)
    (hu' : u'.Prime) (hv' : v'.Prime)
    (hu5 : 5 < u) (hv5 : 5 < v)
    (hu'5 : 5 < u') (hv'5 : 5 < v')
    (h :
      repeatedDoorMultiplier a b c * u * v ^ 2 =
        repeatedDoorMultiplier a' b' c' * u' * v' ^ 2) :
    a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨h₂, h₃, h₅⟩ :=
    repeated_door_smooth_exponents a b c hu hv hu5 hv5
  obtain ⟨h₂', h₃', h₅'⟩ :=
    repeated_door_smooth_exponents a' b' c'
      hu' hv' hu'5 hv'5
  have he₂ := congrArg (fun n : ℕ => n.factorization 2) h
  have he₃ := congrArg (fun n : ℕ => n.factorization 3) h
  have he₅ := congrArg (fun n : ℕ => n.factorization 5) h
  rw [h₂, h₂'] at he₂
  rw [h₃, h₃'] at he₃
  rw [h₅, h₅'] at he₅
  omega

/-- A factored door uniquely determines the complete ordered tuple. -/
theorem repeated_door_tuple_unique
    {a b c a' b' c' u v u' v' : ℕ}
    (hu : u.Prime) (hv : v.Prime)
    (hu' : u'.Prime) (hv' : v'.Prime)
    (hu5 : 5 < u) (hv5 : 5 < v)
    (hu'5 : 5 < u') (hv'5 : 5 < v')
    (huv : u ≤ v) (huv' : u' ≤ v')
    (h :
      repeatedDoorMultiplier a b c * u * v ^ 2 =
        repeatedDoorMultiplier a' b' c' * u' * v' ^ 2) :
    a = a' ∧ b = b' ∧ c = c' ∧ u = u' ∧ v = v' := by
  obtain ⟨ha, hb, hc⟩ :=
    repeated_door_smooth_indices_unique
      hu hv hu' hv' hu5 hv5 hu'5 hv'5 h
  subst a'
  subst b'
  subst c'
  have hA : repeatedDoorMultiplier a b c ≠ 0 := by
    unfold repeatedDoorMultiplier
    positivity
  have hcofactor : u * v ^ 2 = u' * v' ^ 2 := by
    apply mul_left_cancel₀ hA
    simpa only [mul_assoc] using h
  obtain ⟨huu, hvv⟩ :=
    ordered_prime_pair_unique hu hv hu' hv' huv huv' hcofactor
  exact ⟨rfl, rfl, rfl, huu, hvv⟩

/-- Valid data for a repeated-largest-factor door. -/
structure RepeatedDoorData where
  a : ℕ
  b : ℕ
  c : ℕ
  u : ℕ
  v : ℕ
  hu : u.Prime
  hv : v.Prime
  hu5 : 5 < u
  hv5 : 5 < v
  huv : u ≤ v

def RepeatedDoorData.value (t : RepeatedDoorData) : ℕ :=
  repeatedDoorMultiplier t.a t.b t.c * t.u * t.v ^ 2

/-- A door value determines its valid tuple uniquely. -/
theorem repeatedDoorData_value_injective :
    Function.Injective RepeatedDoorData.value := by
  intro s t h
  obtain ⟨ha, hb, hc, hu, hv⟩ :=
    repeated_door_tuple_unique
      s.hu s.hv t.hu t.hv
      s.hu5 s.hv5 t.hu5 t.hv5 s.huv t.huv h
  cases s
  cases t
  simp_all

/-- true selects the kept door; false selects the discarded door. -/
def selectedDoorValue (p : ℕ) (kept : Bool) : ℕ :=
  if kept then Hire.m0 p else Hire.m1 p

/-- The repeated-factor condition stated directly on a prime and door. -/
def HasRepeatedDoor (p : ℕ) (kept : Bool) : Prop :=
  ∃ t : RepeatedDoorData, t.value = selectedDoorValue p kept

/-- Whenever a repeated-door representation exists, it is unique. -/
theorem hasRepeatedDoor_iff_existsUnique
    (p : ℕ) (kept : Bool) :
    HasRepeatedDoor p kept ↔
      ∃! t : RepeatedDoorData,
        t.value = selectedDoorValue p kept := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ht, ?_⟩
    intro s hs
    exact repeatedDoorData_value_injective (hs.trans ht.symm)
  · rintro ⟨t, ht, _⟩
    exact ⟨t, ht⟩

/-- Weight for one prime and one door. -/
noncomputable def signedDoorLog (p : ℕ) (kept : Bool) : ℝ :=
  if kept then Real.log (p : ℝ) else -Real.log (p : ℝ)

/-- Uniqueness turns a finite representation sum into an indicator. -/
theorem sum_repeatedDoorData_indicator
    (S : Finset RepeatedDoorData)
    (d : ℕ) (w : ℝ) :
    (∑ t ∈ S, if t.value = d then w else 0) =
      if (∃ t ∈ S, t.value = d) then w else 0 := by
  classical
  by_cases hex : ∃ t ∈ S, t.value = d
  · obtain ⟨t, htS, htd⟩ := hex
    rw [ite_eq_left ⟨t, htS, htd⟩]
    calc
      _ = (if t.value = d then w else 0) := by
        apply Finset.sum_eq_single t
        · intro s hsS hst
          have hsd : s.value ≠ d := by
            intro hsd
            apply hst
            exact repeatedDoorData_value_injective
              (hsd.trans htd.symm)
          simp [hsd]
        · intro ht
          exact (ht htS).elim
      _ = w := by simp [htd]
  · rw [ite_eq_right hex]
    apply Finset.sum_eq_zero
    intro t htS
    have htd : t.value ≠ d := by
      intro htd
      exact hex ⟨t, htS, htd⟩
    simp [htd]

/-- The repeated-factor contribution indexed directly by prime owners. -/
noncomputable def repeatedDoorPrimeSum
    (X : ℕ) (kept : Bool) : ℝ := by
  classical
  exact ∑ p ∈ Finset.range (X + 1),
    if p.Prime ∧ HasRepeatedDoor p kept then
      signedDoorLog p kept
    else 0

/-- The same contribution, indexed by a finite set of valid tuples. -/
noncomputable def repeatedDoorTupleSum
    (X : ℕ) (kept : Bool)
    (S : Finset RepeatedDoorData) : ℝ := by
  classical
  exact ∑ t ∈ S,
    ∑ p ∈ Finset.range (X + 1),
      if p.Prime ∧ t.value = selectedDoorValue p kept then
        signedDoorLog p kept
      else 0

/-- A complete finite tuple set gives exact reindexing by prime owners. -/
theorem repeatedDoorTupleSum_eq_primeSum
    (X : ℕ) (kept : Bool)
    (S : Finset RepeatedDoorData)
    (hcomplete :
      ∀ p ∈ Finset.range (X + 1), p.Prime →
        (HasRepeatedDoor p kept ↔
          ∃ t ∈ S, t.value = selectedDoorValue p kept)) :
    repeatedDoorTupleSum X kept S =
      repeatedDoorPrimeSum X kept := by
  classical
  unfold repeatedDoorTupleSum repeatedDoorPrimeSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · simp only [hprime, true_and]
    rw [sum_repeatedDoorData_indicator]
    simp only [← hcomplete p hp hprime]
  · simp [hprime]

/-- Only finitely many valid tuples have a door value in the window. -/
theorem repeatedDoorData_window_finite (X : ℕ) :
    (RepeatedDoorData.value ⁻¹'
      (↑(Finset.range (X + 2)) : Set ℕ)).Finite := by
  exact Set.Finite.preimage
    repeatedDoorData_value_injective.injOn
    (Finset.finite_toSet _)

/-- The complete finite set of repeated-factor tuples for the window. -/
noncomputable def repeatedDoorWindowTuples
    (X : ℕ) : Finset RepeatedDoorData :=
  (repeatedDoorData_window_finite X).toFinset

theorem mem_repeatedDoorWindowTuples
    (X : ℕ) (t : RepeatedDoorData) :
    t ∈ repeatedDoorWindowTuples X ↔ t.value ≤ X + 1 := by
  simp only [repeatedDoorWindowTuples,
    Set.Finite.mem_toFinset, Set.mem_preimage,
    Finset.mem_coe, Finset.mem_range]
  omega

/-- Both selected neighbours of an owner in the window
are bounded by X + 1. -/
theorem selectedDoorValue_le_window
    {p X : ℕ}
    (hpX : p ≤ X) (kept : Bool) :
    selectedDoorValue p kept ≤ X + 1 := by
  have hm0 : Hire.m0 p ≤ X + 1 := by
    unfold Hire.m0
    split_ifs <;> omega
  have hm1 : Hire.m1 p ≤ X + 1 := by
    unfold Hire.m1
    split_ifs <;> omega
  cases kept
  · simpa [selectedDoorValue] using hm1
  · simpa [selectedDoorValue] using hm0

/-- The canonical tuple set supplies the completeness hypothesis. -/
theorem repeatedDoorWindowTuples_complete
    (X : ℕ) (kept : Bool) :
    ∀ p ∈ Finset.range (X + 1), p.Prime →
      (HasRepeatedDoor p kept ↔
        ∃ t ∈ repeatedDoorWindowTuples X,
          t.value = selectedDoorValue p kept) := by
  intro p hp hprime
  have hpX : p ≤ X := by
    have hp' := Finset.mem_range.mp hp
    omega
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_, ht⟩
    apply (mem_repeatedDoorWindowTuples X t).2
    rw [ht]
    exact selectedDoorValue_le_window hpX kept
  · rintro ⟨t, htS, ht⟩
    exact ⟨t, ht⟩

/-- Exact reindexing with the canonical window tuple set. -/
theorem repeatedDoorWindowTupleSum_eq_primeSum
    (X : ℕ) (kept : Bool) :
    repeatedDoorTupleSum X kept (repeatedDoorWindowTuples X) =
      repeatedDoorPrimeSum X kept := by
  exact repeatedDoorTupleSum_eq_primeSum
    X kept (repeatedDoorWindowTuples X)
    (repeatedDoorWindowTuples_complete X kept)

/-- Combining kept and discarded contributions preserves the identity. -/
theorem repeatedDoorWindow_signed_reindex
    (X : ℕ) :
    repeatedDoorTupleSum X true (repeatedDoorWindowTuples X) +
      repeatedDoorTupleSum X false (repeatedDoorWindowTuples X) =
    repeatedDoorPrimeSum X true +
      repeatedDoorPrimeSum X false := by
  rw [repeatedDoorWindowTupleSum_eq_primeSum,
    repeatedDoorWindowTupleSum_eq_primeSum]

/-- A specified door contributes only at its adjacent owners. -/
theorem selectedDoorOwnerWeight_eq_zero_of_not_adjacent
    (X d p : ℕ)
    (hm : p ≠ d - 1)
    (hp : p ≠ d + 1) :
    selectedDoorOwnerWeight X d p = 0 := by
  by_cases hprime : p.Prime ∧ p ≤ X
  · have hp2 := hprime.1.two_le
    have hm0 : Hire.m0 p ≠ d := by
      intro h
      unfold Hire.m0 at h
      split_ifs at h <;> omega
    have hm1 : Hire.m1 p ≠ d := by
      intro h
      unfold Hire.m1 at h
      split_ifs at h <;> omega
    simp [selectedDoorOwnerWeight, hprime, hm0, hm1]
  · simp [selectedDoorOwnerWeight, hprime]

/-- Summing over prime owners recovers precisely the two offsets. -/
theorem sum_selectedDoorOwnerWeight_eq_adjacent
    (X d : ℕ) (hd : 0 < d) :
    (∑ p ∈ Finset.range (X + 1),
      selectedDoorOwnerWeight X d p) =
    selectedDoorOwnerWeight X d (d - 1) +
      selectedDoorOwnerWeight X d (d + 1) := by
  classical
  apply Finset.sum_eq_add (d - 1) (d + 1)
    (adjacent_owner_offsets_ne hd)
  · intro p hp hne
    exact selectedDoorOwnerWeight_eq_zero_of_not_adjacent
      X d p hne.1 hne.2
  · intro hm
    have houtside : ¬d - 1 ≤ X := by
      simp only [Finset.mem_range] at hm
      omega
    simp [selectedDoorOwnerWeight, houtside]
  · intro hp
    have houtside : ¬d + 1 ≤ X := by
      simp only [Finset.mem_range] at hp
      omega
    simp [selectedDoorOwnerWeight, houtside]

/-- The complete tuple sum equals the selected adjacent-pair sum. -/
theorem repeatedDoorTupleSum_signed_eq_pairs
    (X : ℕ) (S : Finset RepeatedDoorData) :
    repeatedDoorTupleSum X true S +
      repeatedDoorTupleSum X false S =
    ∑ t ∈ S,
      selectedRepeatedPairWeight X
        (repeatedDoorMultiplier t.a t.b t.c) (t.u, t.v) := by
  classical
  unfold repeatedDoorTupleSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_add_distrib]
  have hd : 0 < t.value := by
    have hu := t.hu.pos
    have hv := t.hv.pos
    dsimp [RepeatedDoorData.value, repeatedDoorMultiplier]
    positivity
  calc
    _ = ∑ p ∈ Finset.range (X + 1),
        selectedDoorOwnerWeight X t.value p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpX : p ≤ X := by
        have h := Finset.mem_range.mp hp
        omega
      by_cases hprime : p.Prime
      · simp [selectedDoorValue, signedDoorLog,
          selectedDoorOwnerWeight, hprime, hpX, eq_comm];
          split_ifs <;> ring
      · simp [selectedDoorValue,
          selectedDoorOwnerWeight, hprime]
    _ = selectedDoorOwnerWeight X t.value (t.value - 1) +
        selectedDoorOwnerWeight X t.value (t.value + 1) :=
      sum_selectedDoorOwnerWeight_eq_adjacent X t.value hd
    _ = _ := by
      simp [selectedRepeatedPairWeight, t.hu, t.hv,
        t.hu5, t.hv5, RepeatedDoorData.value]

/-- The actual prime-indexed contribution is bounded by tuple mass. -/
theorem abs_repeatedDoorPrimeSum_le_tuple_mass
    (X : ℕ) :
    |repeatedDoorPrimeSum X true +
      repeatedDoorPrimeSum X false| ≤
    ∑ t ∈ repeatedDoorWindowTuples X,
      repeatedPairOwnerMass X
        (repeatedDoorMultiplier t.a t.b t.c) (t.u, t.v) := by
  rw [← repeatedDoorWindow_signed_reindex,
    repeatedDoorTupleSum_signed_eq_pairs]
  calc
    _ ≤ ∑ t ∈ repeatedDoorWindowTuples X,
        |selectedRepeatedPairWeight X
          (repeatedDoorMultiplier t.a t.b t.c) (t.u, t.v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      exact abs_selectedRepeatedPairWeight_le X
        (repeatedDoorMultiplier t.a t.b t.c) (t.u, t.v)

/-- A slot records the three exponent indices and the remaining pair. -/
def repeatedDoorSlot (t : RepeatedDoorData) :
    Σ _ : ℕ × ℕ × ℕ, ℕ × ℕ :=
  ⟨(t.a, t.b, t.c), (t.u, t.v)⟩

theorem repeatedDoorSlot_injective :
    Function.Injective repeatedDoorSlot := by
  intro s t h
  have hv : s.value = t.value := by
    have hk := congrArg
      (fun z : Σ _ : ℕ × ℕ × ℕ, ℕ × ℕ =>
        repeatedDoorMultiplier z.1.1 z.1.2.1 z.1.2.2 *
          z.2.1 * z.2.2 ^ 2) h
    exact hk
  exact repeatedDoorData_value_injective hv

/-- All exponent-and-pair slots in the window box. -/
def repeatedDoorSlotBox (X : ℕ) :
    Finset (Σ _ : ℕ × ℕ × ℕ, ℕ × ℕ) :=
  ((Finset.range (X + 1)) ×ˢ
    ((Finset.range (X + 1)) ×ˢ
      (Finset.range (X + 1)))).sigma
    (fun abc =>
      repeatedFactorPairs
        ((X + 1) / repeatedDoorMultiplier abc.1 abc.2.1 abc.2.2)
        (cubeRootCutoff
          ((X + 1) / repeatedDoorMultiplier abc.1 abc.2.1 abc.2.2))
        (squareRootCutoff
          ((X + 1) / repeatedDoorMultiplier abc.1 abc.2.1 abc.2.2)))

theorem repeatedDoorSlot_mem_box
    (X : ℕ) (t : RepeatedDoorData)
    (ht : t ∈ repeatedDoorWindowTuples X) :
    repeatedDoorSlot t ∈ repeatedDoorSlotBox X := by
  have hd := (mem_repeatedDoorWindowTuples X t).1 ht
  have hu : 1 ≤ t.u := t.hu.one_lt.le
  have hv : 1 ≤ t.v := t.hv.one_lt.le
  have hA : 0 < repeatedDoorMultiplier t.a t.b t.c := by
    unfold repeatedDoorMultiplier
    positivity
  have hAle :=
    multiplier_le_repeated_product
      (A := repeatedDoorMultiplier t.a t.b t.c) hu hv
  have hindices :=
    repeatedDoorMultiplier_indices_lt t.a t.b t.c
  have ha : t.a < X + 1 := by
    dsimp [RepeatedDoorData.value] at hd
    omega
  have hb : t.b < X + 1 := by
    dsimp [RepeatedDoorData.value] at hd
    omega
  have hc : t.c < X + 1 := by
    dsimp [RepeatedDoorData.value] at hd
    omega
  have hcofactor :
      t.u * t.v ^ 2 ≤
        (X + 1) / repeatedDoorMultiplier t.a t.b t.c := by
    apply (Nat.le_div_iff_mul_le hA).2
    calc
      _ = t.value := by
        dsimp [RepeatedDoorData.value]
        ring
      _ ≤ X + 1 := hd
  have hpair :=
    mem_repeatedFactorPairs_root_cutoffs hu hv t.huv hcofactor
  simpa only [repeatedDoorSlotBox, repeatedDoorSlot,
    Finset.mem_sigma, Finset.mem_product, Finset.mem_range] using
    (show (t.a < X + 1 ∧
      t.b < X + 1 ∧ t.c < X + 1) ∧
      (t.u, t.v) ∈ repeatedFactorPairs
        ((X + 1) / repeatedDoorMultiplier t.a t.b t.c)
        (cubeRootCutoff
          ((X + 1) / repeatedDoorMultiplier t.a t.b t.c))
        (squareRootCutoff
          ((X + 1) / repeatedDoorMultiplier t.a t.b t.c))
      from ⟨⟨ha, hb, hc⟩, hpair⟩)

/-- Tuple mass is bounded by the mass of the complete slot box. -/
theorem repeatedDoorWindow_tuple_mass_le_box
    (X : ℕ) :
    (∑ t ∈ repeatedDoorWindowTuples X,
      repeatedPairOwnerMass X
        (repeatedDoorMultiplier t.a t.b t.c) (t.u, t.v)) ≤
    ∑ a ∈ Finset.range (X + 1),
      ∑ b ∈ Finset.range (X + 1),
        ∑ c ∈ Finset.range (X + 1),
          repeatedMultiplierOwnerMass X
            (repeatedDoorMultiplier a b c) := by
  classical
  let g : (Σ _ : ℕ × ℕ × ℕ, ℕ × ℕ) → ℝ :=
    fun z => repeatedPairOwnerMass X
      (repeatedDoorMultiplier z.1.1 z.1.2.1 z.1.2.2) z.2
  have hmap :
      (repeatedDoorWindowTuples X).image repeatedDoorSlot ⊆
        repeatedDoorSlotBox X := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact repeatedDoorSlot_mem_box X t ht
  have hsum :
      (∑ t ∈ repeatedDoorWindowTuples X,
        repeatedPairOwnerMass X
          (repeatedDoorMultiplier t.a t.b t.c) (t.u, t.v)) ≤
      ∑ z ∈ repeatedDoorSlotBox X, g z := by
    apply Finset.sum_le_sum_of_injOn
      repeatedDoorSlot repeatedDoorSlot_injective.injOn hmap
    · intro t ht
      exact le_rfl
    · intro z hz hnot
      exact repeatedPairOwnerMass_nonneg X _ _
  calc
    _ ≤ ∑ z ∈ repeatedDoorSlotBox X, g z := hsum
    _ = _ := by
      unfold repeatedDoorSlotBox
      rw [Finset.sum_sigma]
      simp only [Finset.sum_product]
      rfl

/-- The prime-indexed repeated-factor contribution has
the uniform sublinear window bound. -/
theorem abs_repeatedDoorPrimeSum_le
    {X : ℕ} (hX : 1 ≤ X) :
    |repeatedDoorPrimeSum X true +
      repeatedDoorPrimeSum X false| ≤
      (2 * Real.rpow ((X : ℝ) + 1) (5 / 6 : ℝ) *
        Real.log (X : ℝ)) *
          repeatedDoorGeometricConstant (5 / 6 : ℝ) := by
  calc
    _ ≤ ∑ t ∈ repeatedDoorWindowTuples X,
        repeatedPairOwnerMass X
          (repeatedDoorMultiplier t.a t.b t.c) (t.u, t.v) :=
      abs_repeatedDoorPrimeSum_le_tuple_mass X
    _ ≤ ∑ a ∈ Finset.range (X + 1),
        ∑ b ∈ Finset.range (X + 1),
          ∑ c ∈ Finset.range (X + 1),
            repeatedMultiplierOwnerMass X
              (repeatedDoorMultiplier a b c) :=
      repeatedDoorWindow_tuple_mass_le_box X
    _ ≤ _ :=
      sum_repeatedMultiplierOwnerMass_box_le
        hX (X + 1) (X + 1) (X + 1)

end HireDoorSieve
