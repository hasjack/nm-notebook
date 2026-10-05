import Mathlib

namespace AlphabetTorus

/-- Two points differ by integer steps along the two periods. -/
def SamePoint (ω₁ ω₂ z w : ℂ) : Prop :=
  ∃ m n : ℤ,
    z - w = (m : ℂ) * ω₁ + (n : ℂ) * ω₂

theorem samePoint_refl (ω₁ ω₂ z : ℂ) :
    SamePoint ω₁ ω₂ z z := by
  refine ⟨0, 0, ?_⟩
  simp

theorem samePoint_symm {ω₁ ω₂ z w : ℂ}
    (h : SamePoint ω₁ ω₂ z w) :
    SamePoint ω₁ ω₂ w z := by
  obtain ⟨m, n, hmn⟩ := h
  refine ⟨-m, -n, ?_⟩
  push_cast
  calc
    w - z = -(z - w) := by ring
    _ = -((m : ℂ) * ω₁ + (n : ℂ) * ω₂) := by rw [hmn]
    _ = _ := by ring

theorem samePoint_trans {ω₁ ω₂ z w v : ℂ}
    (hzw : SamePoint ω₁ ω₂ z w)
    (hwv : SamePoint ω₁ ω₂ w v) :
    SamePoint ω₁ ω₂ z v := by
  obtain ⟨m, n, hmn⟩ := hzw
  obtain ⟨r, s, hrs⟩ := hwv
  refine ⟨m + r, n + s, ?_⟩
  push_cast
  calc
    z - v = (z - w) + (w - v) := by ring
    _ = ((m : ℂ) * ω₁ + (n : ℂ) * ω₂) +
        ((r : ℂ) * ω₁ + (s : ℂ) * ω₂) := by
      rw [hmn, hrs]
    _ = _ := by ring

def latticeSetoid (ω₁ ω₂ : ℂ) : Setoid ℂ where
  r := SamePoint ω₁ ω₂
  iseqv := ⟨samePoint_refl ω₁ ω₂,
    samePoint_symm, samePoint_trans⟩

/-- Complex points, identified modulo the two periods. -/
def PeriodQuotient (ω₁ ω₂ : ℂ) :=
  Quotient (latticeSetoid ω₁ ω₂)

def point (ω₁ ω₂ z : ℂ) : PeriodQuotient ω₁ ω₂ :=
  Quotient.mk (latticeSetoid ω₁ ω₂) z

/-- Any integer combination of periods leaves the quotient point unchanged. -/
theorem point_translate (ω₁ ω₂ z : ℂ) (m n : ℤ) :
    point ω₁ ω₂
      (z + (m : ℂ) * ω₁ + (n : ℂ) * ω₂) =
    point ω₁ ω₂ z := by
  apply Quotient.sound
  change SamePoint ω₁ ω₂
    (z + (m : ℂ) * ω₁ + (n : ℂ) * ω₂) z
  refine ⟨m, n, ?_⟩
  ring

/-- Independent periods give unique integer lattice coordinates. -/
theorem lattice_coordinates_unique
    {τ : ℂ} (hτ : 0 < τ.im)
    {m n r s : ℤ}
    (h : (m : ℂ) + (n : ℂ) * τ =
         (r : ℂ) + (s : ℂ) * τ) :
    m = r ∧ n = s := by
  have him : (n : ℝ) * τ.im = (s : ℝ) * τ.im := by
    simpa using congrArg Complex.im h
  have hnR : (n : ℝ) = (s : ℝ) :=
    mul_right_cancel₀ (ne_of_gt hτ) him
  have hn : n = s := by
    exact_mod_cast hnR
  subst s
  have hm : m = r := by
    have hre := congrArg Complex.re h
    simpa using hre
  exact ⟨hm, rfl⟩

/-- One circular dial: the complex exponential of its angle. -/
noncomputable def dial (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))

/-- Adding any integer makes whole turns and leaves the dial unchanged. -/
theorem dial_add_int (x : ℝ) (m : ℤ) :
    dial (x + (m : ℝ)) = dial x := by
  unfold dial
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨m, ?_⟩
  push_cast
  ring

/-- Two independent circular dials. -/
noncomputable def twoDials (x y : ℝ) : ℂ × ℂ :=
  (dial x, dial y)

/-- Whole turns in either direction leave the pair unchanged. -/
theorem twoDials_add_int
    (x y : ℝ) (m n : ℤ) :
    twoDials (x + (m : ℝ)) (y + (n : ℝ)) =
      twoDials x y := by
  unfold twoDials
  rw [dial_add_int, dial_add_int]

/-- Read the real and imaginary coordinates as two circular dials. -/
noncomputable def squareDials (z : ℂ) : ℂ × ℂ :=
  twoDials z.re z.im

/-- Points identified by the square lattice have identical dial readings. -/
theorem squareDials_of_samePoint
    {z w : ℂ} (h : SamePoint 1 Complex.I z w) :
    squareDials z = squareDials w := by
  obtain ⟨m, n, hmn⟩ := h
  have hx : z.re - w.re = (m : ℝ) := by
    simpa using congrArg Complex.re hmn
  have hy : z.im - w.im = (n : ℝ) := by
    simpa using congrArg Complex.im hmn
  have hx' : z.re = w.re + (m : ℝ) := by
    linarith
  have hy' : z.im = w.im + (n : ℝ) := by
    linarith
  unfold squareDials
  rw [hx', hy']
  exact twoDials_add_int w.re w.im m n

/-- Dial readings defined on quotient points, independent of representative. -/
noncomputable def quotientDials :
    PeriodQuotient 1 Complex.I → ℂ × ℂ :=
  Quotient.lift squareDials
    (fun _ _ h => squareDials_of_samePoint h)

/-- Reading a quotient point agrees with reading its coordinates directly. -/
theorem quotientDials_point (z : ℂ) :
    quotientDials (point 1 Complex.I z) = squareDials z := by
  rfl

/-- Equal dial readings differ by an integer number of turns. -/
theorem dial_eq_iff (x y : ℝ) :
    dial x = dial y ↔
      ∃ m : ℤ, x = y + (m : ℝ) := by
  constructor
  · intro h
    unfold dial at h
    obtain ⟨m, hm⟩ :=
      Complex.exp_eq_exp_iff_exists_int.mp h
    have hc : (x : ℂ) = (y : ℂ) + (m : ℂ) := by
      apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
      calc
        _ = (y : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
            (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hm
        _ = _ := by ring
    refine ⟨m, ?_⟩
    simpa using congrArg Complex.re hc
  · rintro ⟨m, hm⟩
    rw [hm]
    exact dial_add_int y m

/-- Identical dial readings mean exactly the same square-lattice point. -/
theorem squareDials_eq_iff (z w : ℂ) :
    squareDials z = squareDials w ↔
      SamePoint 1 Complex.I z w := by
  constructor
  · intro h
    have hx : dial z.re = dial w.re :=
      congrArg Prod.fst h
    have hy : dial z.im = dial w.im :=
      congrArg Prod.snd h
    obtain ⟨m, hm⟩ := (dial_eq_iff z.re w.re).mp hx
    obtain ⟨n, hn⟩ := (dial_eq_iff z.im w.im).mp hy
    refine ⟨m, n, ?_⟩
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith
  · intro h
    exact squareDials_of_samePoint h

/-- A dial reading varies continuously with its input. -/
theorem continuous_dial : Continuous dial := by
  unfold dial
  fun_prop

/-- Both dial readings vary continuously with the plane point. -/
theorem continuous_squareDials : Continuous squareDials := by
  unfold squareDials twoDials
  exact
    (continuous_dial.comp Complex.continuous_re).prodMk
      (continuous_dial.comp Complex.continuous_im)

/-- Equip the period quotient with the standard quotient topology. -/
noncomputable instance periodQuotientTopologicalSpace
    (ω₁ ω₂ : ℂ) :
    TopologicalSpace (PeriodQuotient ω₁ ω₂) := by
  unfold PeriodQuotient
  infer_instance

/-- Passing from the plane to its glued points is continuous. -/
theorem continuous_point (ω₁ ω₂ : ℂ) :
    Continuous (point ω₁ ω₂) := by
  change Continuous
    (@Quotient.mk' ℂ (latticeSetoid ω₁ ω₂))
  exact continuous_quotient_mk'

/-- The two dial readings remain continuous after gluing. -/
theorem continuous_quotientDials :
    Continuous quotientDials := by
  unfold quotientDials
  exact continuous_squareDials.quotient_lift
    (fun _ _ h => squareDials_of_samePoint h)

/-- A quarter-turn preserves square-lattice equivalence. -/
theorem samePoint_quarter_turn
    {z w : ℂ} (h : SamePoint 1 Complex.I z w) :
    SamePoint 1 Complex.I (Complex.I * z) (Complex.I * w) := by
  obtain ⟨m, n, hmn⟩ := h
  refine ⟨-n, m, ?_⟩
  calc
    Complex.I * z - Complex.I * w
        = Complex.I * (z - w) := by ring
    _ = Complex.I *
        ((m : ℂ) * 1 + (n : ℂ) * Complex.I) := by
          rw [hmn]
    _ = (m : ℂ) * Complex.I +
        (n : ℂ) * (Complex.I * Complex.I) := by ring
    _ = ((-n : ℤ) : ℂ) * 1 + (m : ℂ) * Complex.I := by
      simp
      ring

/-- Quarter-turn rotation on the square-lattice quotient. -/
def quarterTurn :
    PeriodQuotient 1 Complex.I → PeriodQuotient 1 Complex.I :=
  Quotient.lift
    (fun z : ℂ => point 1 Complex.I (Complex.I * z))
    (by
      intro z w h
      apply Quotient.sound
      exact samePoint_quarter_turn h)

/-- The quotient rotation acts as expected on representatives. -/
theorem quarterTurn_point (z : ℂ) :
    quarterTurn (point 1 Complex.I z) =
      point 1 Complex.I (Complex.I * z) := by
  rfl

/-- Quarter-turn rotation is continuous. -/
theorem continuous_quarterTurn :
    Continuous quarterTurn := by
  unfold quarterTurn
  exact
    ((continuous_point 1 Complex.I).comp
      (continuous_const.mul continuous_id)).quotient_lift _

/-- Four quarter-turns return every quotient point to itself. -/
theorem quarterTurn_four
    (q : PeriodQuotient 1 Complex.I) :
    quarterTurn (quarterTurn (quarterTurn (quarterTurn q))) = q := by
  refine Quotient.inductionOn q ?_
  intro z
  change
    quarterTurn (quarterTurn (quarterTurn
      (quarterTurn (point 1 Complex.I z)))) =
      point 1 Complex.I z
  simp only [quarterTurn_point]
  have hfour :
      Complex.I * (Complex.I * (Complex.I * (Complex.I * z))) = z := by
    calc
      _ = (Complex.I * Complex.I) *
          ((Complex.I * Complex.I) * z) := by ring
      _ = z := by simp
  rw [hfour]

end AlphabetTorus
