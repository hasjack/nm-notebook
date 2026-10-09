import Hire.CharacterReadout

namespace HireCharacterReadout

/-- The quadratic sign modulo 5, including zero on multiples of 5. -/
def quadraticFiveSign (n : ℕ) : ℤ :=
  if n % 5 = 1 ∨ n % 5 = 4 then 1
  else if n % 5 = 2 ∨ n % 5 = 3 then -1
  else 0

/-- The quadratic sign is multiplicative. -/
theorem quadraticFiveSign_mul (a b : ℕ) :
    quadraticFiveSign (a * b) =
      quadraticFiveSign a * quadraticFiveSign b := by
  set ra := a % 5 with ha
  set rb := b % 5 with hb
  have hra : ra < 5 := Nat.mod_lt a (by norm_num)
  have hrb : rb < 5 := Nat.mod_lt b (by norm_num)
  have hab :
      (a * b) % 5 = (ra * rb) % 5 := by
    rw [Nat.mul_mod, ← ha, ← hb]
  interval_cases ra <;> interval_cases rb <;>
    norm_num [quadraticFiveSign, hab, ← ha, ← hb]

/--
For an imaginary contributor whose kept door is twice c,
the sign is the quadratic sign of c modulo 5.
-/
theorem complex15_im_eq_quadraticFiveSign_of_kept_door
    {p c : ℕ}
    (hp : p.Prime)
    (h3 : p ≠ 3)
    (hdoor : Hire.m0 p = 2 * c)
    (him : (complex15 p).im ≠ 0) :
    (complex15 p).im = (quadraticFiveSign c : ℝ) := by
  have hp2 : 2 ≤ p := hp.two_le
  set rp := p % 5 with hpr
  set rc := c % 5 with hcr
  have hrp : rp < 5 := Nat.mod_lt p (by norm_num)
  have hrc : rc < 5 := Nat.mod_lt c (by norm_num)
  rcases Hire.prime_ne_three_mod_three_eq_one_or_two hp h3
      with hp3 | hp3
  · simp [Hire.m0, hp3] at hdoor
    interval_cases rp <;>
    interval_cases rc <;>
    norm_num [complex15, quarticFive, Hire.chi3,
      quadraticFiveSign, hp3, ← hpr, ← hcr] at him <;>
    norm_num [complex15, quarticFive, Hire.chi3,
      quadraticFiveSign, hp3, ← hpr, ← hcr] <;>
    omega
  · simp [Hire.m0, hp3] at hdoor
    interval_cases rp <;>
    interval_cases rc <;>
    norm_num [complex15, quarticFive, Hire.chi3,
      quadraticFiveSign, hp3, ← hpr, ← hcr] at him <;>
    norm_num [complex15, quarticFive, Hire.chi3,
      quadraticFiveSign, hp3, ← hpr, ← hcr] <;>
    omega

/--
A kept door 2uvw carries the product of the three quadratic signs
whenever its owner contributes to the imaginary readout.
-/
theorem complex15_im_eq_three_factor_sign
    {p u v w : ℕ}
    (hp : p.Prime)
    (h3 : p ≠ 3)
    (hdoor : Hire.m0 p = 2 * (u * v * w))
    (him : (complex15 p).im ≠ 0) :
    (complex15 p).im =
      ((quadraticFiveSign u *
        quadraticFiveSign v *
        quadraticFiveSign w : ℤ) : ℝ) := by
  rw [complex15_im_eq_quadraticFiveSign_of_kept_door
    hp h3 hdoor him]
  rw [quadraticFiveSign_mul, quadraticFiveSign_mul]

/--
Rewrite the imaginary contribution of a finite family of door triples
as a sum weighted by the product of their quadratic signs.
-/
theorem sum_three_factor_imaginary_eq
    (T : Finset (ℕ × ℕ × ℕ))
    (owner : (ℕ × ℕ × ℕ) → ℕ)
    (hP : ∀ t ∈ T, (owner t).Prime)
    (h3 : ∀ t ∈ T, owner t ≠ 3)
    (hdoor : ∀ t ∈ T,
      Hire.m0 (owner t) =
        2 * (t.1 * t.2.1 * t.2.2)) :
    (∑ t ∈ T,
      Real.log (owner t : ℝ) *
        (complex15 (owner t)).im) =
    ∑ t ∈ T,
      if (complex15 (owner t)).im ≠ 0 then
        Real.log (owner t : ℝ) *
          ((quadraticFiveSign t.1 *
            quadraticFiveSign t.2.1 *
            quadraticFiveSign t.2.2 : ℤ) : ℝ)
      else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro t ht
  by_cases him : (complex15 (owner t)).im ≠ 0
  · rw [ite_eq_left him]
    rw [complex15_im_eq_three_factor_sign
      (hP t ht) (h3 t ht) (hdoor t ht) him]
  · have hz : (complex15 (owner t)).im = 0 := by
      simpa using him
    simp [hz]

/-- The finite box containing triples with coordinates at most X + 1. -/
def distinctDoorTripleBox15 (X : ℕ) :
    Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (X + 2)).product
    ((Finset.range (X + 2)).product
      (Finset.range (X + 2)))

/--
Distinct prime triples whose assigned prime owner lies below X
and has kept door 2uvw.
-/
noncomputable def distinctDoorTriples15
    (X : ℕ)
    (owner : (ℕ × ℕ × ℕ) → ℕ) :
    Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (distinctDoorTripleBox15 X).filter (fun t =>
    (owner t).Prime ∧
    owner t ≠ 3 ∧
    owner t ≤ X ∧
    t.1.Prime ∧
    t.2.1.Prime ∧
    t.2.2.Prime ∧
    5 < t.1 ∧
    t.1 < t.2.1 ∧
    t.2.1 < t.2.2 ∧
    Hire.m0 (owner t) =
      2 * (t.1 * t.2.1 * t.2.2))

/-- The bounded distinct-factor family has the quadratic-sign readout. -/
theorem sum_distinctDoorTriples15_imaginary_eq
    (X : ℕ)
    (owner : (ℕ × ℕ × ℕ) → ℕ) :
    (∑ t ∈ distinctDoorTriples15 X owner,
      Real.log (owner t : ℝ) *
        (complex15 (owner t)).im) =
    ∑ t ∈ distinctDoorTriples15 X owner,
      if (complex15 (owner t)).im ≠ 0 then
        Real.log (owner t : ℝ) *
          ((quadraticFiveSign t.1 *
            quadraticFiveSign t.2.1 *
            quadraticFiveSign t.2.2 : ℤ) : ℝ)
      else 0 := by
  classical
  apply sum_three_factor_imaginary_eq
  · intro t ht
    have h :=
      (Finset.mem_filter.mp
        (show t ∈ (distinctDoorTripleBox15 X).filter
          (fun t =>
            (owner t).Prime ∧
            owner t ≠ 3 ∧
            owner t ≤ X ∧
            t.1.Prime ∧
            t.2.1.Prime ∧
            t.2.2.Prime ∧
            5 < t.1 ∧
            t.1 < t.2.1 ∧
            t.2.1 < t.2.2 ∧
            Hire.m0 (owner t) =
              2 * (t.1 * t.2.1 * t.2.2))
          from ht)).2
    exact h.1
  · intro t ht
    have h := Finset.mem_filter.mp ht
    exact h.2.2.1
  · intro t ht
    have h := Finset.mem_filter.mp ht
    rcases h.2 with
      ⟨hp, h3, hX, hu, hv, hw, h5, huv, hvw, hdoor⟩
    exact hdoor

/-- The least of three prime factors is at most any prime divisor
of their product. -/
theorem least_prime_le_divisor_of_three
    {q a b c : ℕ}
    (hq : q.Prime)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hd : q ∣ a * b * c) :
    a ≤ q := by
  rcases hq.dvd_mul.mp hd with habdvd | hcdvd
  · rcases hq.dvd_mul.mp habdvd with hadvd | hbdvd
    · have heq : q = a :=
        (Nat.prime_dvd_prime_iff_eq hq ha).mp hadvd
      omega
    · have heq : q = b :=
        (Nat.prime_dvd_prime_iff_eq hq hb).mp hbdvd
      omega
  · have heq : q = c :=
      (Nat.prime_dvd_prime_iff_eq hq hc).mp hcdvd
    omega

/-- The least of two prime factors is at most any prime divisor
of their product. -/
theorem least_prime_le_divisor_of_two
    {q a b : ℕ}
    (hq : q.Prime)
    (ha : a.Prime) (hb : b.Prime)
    (hab : a ≤ b)
    (hd : q ∣ a * b) :
    a ≤ q := by
  rcases hq.dvd_mul.mp hd with hadvd | hbdvd
  · have heq : q = a :=
      (Nat.prime_dvd_prime_iff_eq hq ha).mp hadvd
    omega
  · have heq : q = b :=
      (Nat.prime_dvd_prime_iff_eq hq hb).mp hbdvd
    omega

/-- Increasing triples of primes are uniquely determined
by their product. -/
theorem ordered_prime_triple_unique
    {u v w u' v' w' : ℕ}
    (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (hu' : u'.Prime) (hv' : v'.Prime) (hw' : w'.Prime)
    (huv : u < v) (hvw : v < w)
    (huv' : u' < v') (hvw' : v' < w')
    (hprod : u * v * w = u' * v' * w') :
    u = u' ∧ v = v' ∧ w = w' := by
  have hdu : u ∣ u' * v' * w' := by
    rw [← hprod]
    refine ⟨v * w, ?_⟩
    ring
  have hdu' : u' ∣ u * v * w := by
    rw [hprod]
    refine ⟨v' * w', ?_⟩
    ring

  have hleft : u' ≤ u :=
    least_prime_le_divisor_of_three
      hu hu' hv' hw' huv'.le hvw'.le hdu
  have hright : u ≤ u' :=
    least_prime_le_divisor_of_three
      hu' hu hv hw huv.le hvw.le hdu'
  have huu : u = u' := Nat.le_antisymm hright hleft
  subst u'

  have htail : v * w = v' * w' :=
    Nat.eq_of_mul_eq_mul_left hu.pos
      (by simpa only [mul_assoc] using hprod)

  have hdv : v ∣ v' * w' := by
    rw [← htail]
    exact ⟨w, rfl⟩
  have hdv' : v' ∣ v * w := by
    rw [htail]
    exact ⟨w', rfl⟩

  have hvleft : v' ≤ v :=
    least_prime_le_divisor_of_two hv hv' hw' hvw'.le hdv
  have hvright : v ≤ v' :=
    least_prime_le_divisor_of_two hv' hv hw hvw.le hdv'
  have hvv : v = v' :=
    Nat.le_antisymm hvright hvleft
  subst v'

  have hww : w = w' :=
    Nat.eq_of_mul_eq_mul_left hv.pos htail
  exact ⟨rfl, rfl, hww⟩

/-- The same uniqueness holds when the common product
is written as an even door. -/
theorem ordered_prime_triple_unique_of_two_mul
    {u v w u' v' w' : ℕ}
    (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (hu' : u'.Prime) (hv' : v'.Prime) (hw' : w'.Prime)
    (huv : u < v) (hvw : v < w)
    (huv' : u' < v') (hvw' : v' < w')
    (hdoor :
      2 * (u * v * w) = 2 * (u' * v' * w')) :
    u = u' ∧ v = v' ∧ w = w' := by
  have hprod : u * v * w = u' * v' * w' := by
    omega
  exact ordered_prime_triple_unique
    hu hv hw hu' hv' hw' huv hvw huv' hvw' hprod

/-- Two triples in the bounded family with the same owner are equal. -/
theorem distinctDoorTriples15_owner_injective
    (X : ℕ)
    (owner : (ℕ × ℕ × ℕ) → ℕ)
    {t t' : ℕ × ℕ × ℕ}
    (ht : t ∈ distinctDoorTriples15 X owner)
    (ht' : t' ∈ distinctDoorTriples15 X owner)
    (heq : owner t = owner t') :
    t = t' := by
  classical
  have h := (Finset.mem_filter.mp ht).2
  have h' := (Finset.mem_filter.mp ht').2
  rcases h with
    ⟨hp, h3, hX, hu, hv, hw, h5, huv, hvw, hd⟩
  rcases h' with
    ⟨hp', h3', hX', hu', hv', hw', h5', huv', hvw', hd'⟩

  have hproduct :
      2 * (t.1 * t.2.1 * t.2.2) =
        2 * (t'.1 * t'.2.1 * t'.2.2) := by
    calc
      _ = Hire.m0 (owner t) := hd.symm
      _ = Hire.m0 (owner t') := congrArg Hire.m0 heq
      _ = _ := hd'

  obtain ⟨hfirst, hsecond, hthird⟩ :=
    ordered_prime_triple_unique_of_two_mul
      hu hv hw hu' hv' hw' huv hvw huv' hvw' hproduct
  apply Prod.ext
  · exact hfirst
  · exact Prod.ext hsecond hthird

/-- Reindex an owner-weighted triple sum over its distinct owners. -/
theorem sum_distinctDoorTriples15_eq_sum_owner_image
    (X : ℕ)
    (owner : (ℕ × ℕ × ℕ) → ℕ)
    (f : ℕ → ℝ) :
    (∑ t ∈ distinctDoorTriples15 X owner, f (owner t)) =
      ∑ p ∈ (distinctDoorTriples15 X owner).image owner,
        f p := by
  classical
  symm
  apply Finset.sum_image
  intro t ht t' ht' heq
  exact distinctDoorTriples15_owner_injective
    X owner ht ht' heq

/-- The imaginary triple readout equals the readout over its owner image. -/
theorem sum_distinctDoorTriples15_imaginary_eq_owner_image
    (X : ℕ)
    (owner : (ℕ × ℕ × ℕ) → ℕ) :
    (∑ t ∈ distinctDoorTriples15 X owner,
      Real.log (owner t : ℝ) *
        (complex15 (owner t)).im) =
      ∑ p ∈ (distinctDoorTriples15 X owner).image owner,
        Real.log (p : ℝ) * (complex15 p).im := by
  exact sum_distinctDoorTriples15_eq_sum_owner_image
    X owner
    (fun p => Real.log (p : ℝ) * (complex15 p).im)

/-- The candidate owner determined by a triple's kept door. -/
def distinctDoorOwner15 (t : ℕ × ℕ × ℕ) : ℕ :=
  let c := t.1 * t.2.1 * t.2.2
  if c % 3 = 1 then 2 * c - 1 else 2 * c + 1

/-- A prime owner of 2uvw equals the explicit candidate owner. -/
theorem distinctDoorOwner15_eq_of_door
    {p u v w : ℕ}
    (hp : p.Prime)
    (h3 : p ≠ 3)
    (hd : Hire.m0 p = 2 * (u * v * w)) :
    distinctDoorOwner15 (u, v, w) = p := by
  have hp2 : 2 ≤ p := hp.two_le
  rcases Hire.prime_ne_three_mod_three_eq_one_or_two hp h3
      with hp3 | hp3
  · simp [Hire.m0, hp3] at hd
    have hc : (u * v * w) % 3 = 1 := by omega
    simp only [distinctDoorOwner15, hc, ite_true]
    omega
  · simp [Hire.m0, hp3] at hd
    have hc : (u * v * w) % 3 ≠ 1 := by omega
    simp only [distinctDoorOwner15, hc, ite_false]
    omega

/-- A prime has a distinct three-factor kept door above the small primes. -/
def HasDistinctDoorTriple15 (p : ℕ) : Prop :=
  ∃ u v w : ℕ,
    u.Prime ∧ v.Prime ∧ w.Prime ∧
    5 < u ∧ u < v ∧ v < w ∧
    Hire.m0 p = 2 * (u * v * w)

/-- The qualifying prime owners below X. -/
noncomputable def distinctDoorPrimeOwners15 (X : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun p =>
    p.Prime ∧ p ≠ 3 ∧ HasDistinctDoorTriple15 p)

/-- Every factor of a qualifying door fits in the finite triple box. -/
theorem distinctDoorTriple_factors_le
    {X p u v w : ℕ}
    (hpX : p ≤ X)
    (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (hd : Hire.m0 p = 2 * (u * v * w)) :
    u ≤ X + 1 ∧ v ≤ X + 1 ∧ w ≤ X + 1 := by
  have hdoor : Hire.m0 p ≤ X + 1 := by
    unfold Hire.m0
    split <;> omega
  have hprod : u * v * w ≤ X + 1 := by omega

  have hub : u ≤ u * v * w := by
    calc
      u = u * 1 * 1 := by ring
      _ ≤ u * v * w :=
        Nat.mul_le_mul
          (Nat.mul_le_mul_left u hv.one_lt.le)
          hw.one_lt.le

  have hvb : v ≤ u * v * w := by
    calc
      v = 1 * v * 1 := by ring
      _ ≤ u * v * w :=
        Nat.mul_le_mul
          (Nat.mul_le_mul hu.one_lt.le (le_refl v))
          hw.one_lt.le

  have hwb : w ≤ u * v * w := by
    calc
      w = 1 * 1 * w := by ring
      _ ≤ u * v * w :=
        Nat.mul_le_mul
          (Nat.mul_le_mul hu.one_lt.le hv.one_lt.le)
          (le_refl w)

  exact ⟨hub.trans hprod, hvb.trans hprod, hwb.trans hprod⟩

/-- The explicit triple family enumerates precisely the qualifying owners. -/
theorem distinctDoorTriples15_owner_image_eq
    (X : ℕ) :
    (distinctDoorTriples15 X distinctDoorOwner15).image
        distinctDoorOwner15 =
      distinctDoorPrimeOwners15 X := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, htp⟩ := Finset.mem_image.mp hp
    have h := (Finset.mem_filter.mp ht).2
    rcases h with
      ⟨hprime, h3, hX, hu, hv, hw, h5, huv, hvw, hd⟩
    subst p
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega),
      hprime, h3, ?_⟩
    exact ⟨t.1, t.2.1, t.2.2,
      hu, hv, hw, h5, huv, hvw, hd⟩

  · intro hp
    obtain ⟨hpRange, hprime, h3, htriple⟩ :=
      Finset.mem_filter.mp hp
    have hpX : p ≤ X := by
      have := Finset.mem_range.mp hpRange
      omega
    obtain ⟨u, v, w, hu, hv, hw, h5, huv, hvw, hd⟩ :=
      htriple
    have heq :
        distinctDoorOwner15 (u, v, w) = p :=
      distinctDoorOwner15_eq_of_door hprime h3 hd
    obtain ⟨huX, hvX, hwX⟩ :=
      distinctDoorTriple_factors_le hpX hu hv hw hd

    apply Finset.mem_image.mpr
    refine ⟨(u, v, w), ?_, heq⟩
    apply Finset.mem_filter.mpr
    constructor
    · change
        (u, v, w) ∈
          (Finset.range (X + 2)).product
            ((Finset.range (X + 2)).product
              (Finset.range (X + 2)))
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_range.mpr
        change u < X + 2
        omega
      · apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_range.mpr
          change v < X + 2
          omega
        · apply Finset.mem_range.mpr
          change w < X + 2
          omega
    · simpa only [heq] using
        (show p.Prime ∧ p ≠ 3 ∧ p ≤ X ∧
          u.Prime ∧ v.Prime ∧ w.Prime ∧
          5 < u ∧ u < v ∧ v < w ∧
          Hire.m0 p = 2 * (u * v * w) from
          ⟨hprime, h3, hpX, hu, hv, hw, h5, huv, hvw, hd⟩)

/-- The triple-indexed imaginary readout equals the prime-indexed one. -/
theorem sum_distinctDoorTriples15_eq_prime_readout
    (X : ℕ) :
    (∑ t ∈ distinctDoorTriples15 X distinctDoorOwner15,
      Real.log (distinctDoorOwner15 t : ℝ) *
        (complex15 (distinctDoorOwner15 t)).im) =
    ∑ p ∈ distinctDoorPrimeOwners15 X,
      Real.log (p : ℝ) * (complex15 p).im := by
  rw [sum_distinctDoorTriples15_imaginary_eq_owner_image,
    distinctDoorTriples15_owner_image_eq]

end HireCharacterReadout
