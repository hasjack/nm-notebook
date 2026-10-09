import Mathlib

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

end HireDoorSieve
