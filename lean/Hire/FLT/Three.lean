import Hire.Doors
import Hire.FLT.Cubic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

namespace Hire

namespace EisensteinBridge

abbrev K := CyclotomicField 3 ℚ

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

abbrev E := NumberField.RingOfIntegers K

noncomputable instance : NumberField K :=
  IsCyclotomicExtension.numberField {3} ℚ K

noncomputable instance : IsPrincipalIdealRing E :=
  IsCyclotomicExtension.Rat.three_pid K

/-- Our chosen cube root of unity, viewed inside the integer ring. -/
noncomputable def omega : E :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

/-- The exceptional prime factor. -/
noncomputable def lambda : E :=
  omega - 1

theorem omega_relation :
    omega ^ 2 + omega + 1 = 0 := by
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  change hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0
  simpa only [IsCyclotomicExtension.Rat.Three.coe_eta] using
    (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one hζ)

theorem omega_cube :
    omega ^ 3 = 1 :=
  door_root_cube_eq_one omega_relation

theorem lambda_sq :
    lambda ^ 2 = -3 * omega := by
  unfold lambda
  exact door_eisenstein_exceptional_sq omega_relation

/-- Unlike our generic ring setup, this exceptional factor is prime. -/
theorem lambda_prime :
    Prime lambda := by
  change Prime
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1)
  exact
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

/-- Our factorisation now lives in the actual Eisenstein ring. -/
theorem sum_cubes (a b : E) :
    a ^ 3 + b ^ 3 =
      (a + b) *
        ((a + omega * b) * (a + omega ^ 2 * b)) :=
  door_eisenstein_sum_cubes a b omega omega_relation

/-- Integer Bézout coprimality survives in the Eisenstein ring. -/
theorem coprime_intCast
    {a b : ℤ} (hab : IsCoprime a b) :
    IsCoprime (a : E) (b : E) := by
  obtain ⟨u, v, huv⟩ := hab
  refine ⟨(u : E), (v : E), ?_⟩
  exact_mod_cast huv

/-- Our integer cube equation becomes an Eisenstein product equation. -/
theorem factorisation_of_int_solution
    {a b c : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    ((a : E) + (b : E)) *
      (((a : E) + omega * (b : E)) *
        ((a : E) + omega ^ 2 * (b : E))) =
      (c : E) ^ 3 := by
  have hcast :
      (a : E) ^ 3 + (b : E) ^ 3 = (c : E) ^ 3 := by
    exact_mod_cast hc
  calc
    _ = (a : E) ^ 3 + (b : E) ^ 3 :=
      (sum_cubes (a : E) (b : E)).symm
    _ = (c : E) ^ 3 := hcast

/-- A common divisor of the first two factors divides λ. -/
theorem common_dvd_int_factors
    {a b : ℤ} {d : E}
    (hab : IsCoprime a b)
    (hS : d ∣ (a : E) + (b : E))
    (hE : d ∣ (a : E) + omega * (b : E)) :
    d ∣ lambda := by
  unfold lambda
  exact door_common_dvd_eisenstein
    (coprime_intCast hab) hS hE

/-- Divisibility of the integer sum by 3 gives divisibility by λ². -/
theorem lambda_sq_dvd_int_sum
    {a b : ℤ}
    (hS : (3 : ℤ) ∣ a + b) :
    lambda ^ 2 ∣ (a : E) + (b : E) := by
  obtain ⟨t, ht⟩ := hS
  have hs :
      (a : E) + (b : E) = 3 * (t : E) := by
    exact_mod_cast ht

  refine ⟨-omega ^ 2 * (t : E), ?_⟩
  rw [hs, lambda_sq]
  calc
    3 * (t : E) = 3 * omega ^ 3 * (t : E) := by
      rw [omega_cube]
      ring
    _ = (-3 * omega) * (-omega ^ 2 * (t : E)) := by
      ring

/-- The first Eisenstein factor contains λ. -/
theorem lambda_dvd_int_linear_factor
    {a b : ℤ}
    (hS : (3 : ℤ) ∣ a + b) :
    lambda ∣ (a : E) + omega * (b : E) := by
  have hsum : lambda ∣ (a : E) + (b : E) :=
    dvd_trans
      (dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0))
      (lambda_sq_dvd_int_sum hS)

  have hid :
      (a : E) + omega * (b : E) =
        ((a : E) + (b : E)) + lambda * (b : E) := by
    unfold lambda
    ring

  rw [hid]
  exact dvd_add hsum (dvd_mul_right lambda (b : E))

/-- The exceptional prime divides the integer 3. -/
theorem lambda_dvd_three :
    lambda ∣ (3 : E) := by
  have hsq : lambda ^ 2 ∣ (3 : E) := by
    simpa using
      (lambda_sq_dvd_int_sum
        (a := (3 : ℤ)) (b := (0 : ℤ)) (by norm_num))
  exact dvd_trans
    (dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0))
    hsq

/-- For ordinary integers, λ-divisibility is exactly 3-divisibility. -/
theorem lambda_dvd_intCast_iff (n : ℤ) :
    lambda ∣ (n : E) ↔ (3 : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra h3
    have hp : Prime (3 : ℤ) := by norm_num
    have hcopZ : IsCoprime (3 : ℤ) n :=
      hp.coprime_iff_not_dvd.mpr h3
    have hcopE : IsCoprime (3 : E) (n : E) :=
      coprime_intCast hcopZ
    exact lambda_prime.not_isUnit
      (hcopE.isUnit_of_dvd' lambda_dvd_three hn)
  · intro hn
    obtain ⟨t, ht⟩ := hn
    have hcast : (n : E) = 3 * (t : E) := by
      exact_mod_cast ht
    rw [hcast]
    exact dvd_mul_of_dvd_left lambda_dvd_three (t : E)

/-- For coprime integer inputs with 3 dividing their sum,
the linear factor contains no second factor of λ. -/
theorem lambda_sq_not_dvd_int_linear_factor
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    ¬ lambda ^ 2 ∣ (a : E) + omega * (b : E) := by
  have hbZ : ¬ (3 : ℤ) ∣ b :=
    three_not_dvd_right_of_coprime_of_dvd_sum hab hS
  have hbE : ¬ lambda ∣ (b : E) := by
    intro hb
    exact hbZ ((lambda_dvd_intCast_iff b).mp hb)

  intro hfactor
  have hsum : lambda ^ 2 ∣ (a : E) + (b : E) :=
    lambda_sq_dvd_int_sum hS
  have hd := dvd_sub hfactor hsum

  have hid :
      ((a : E) + omega * (b : E))
        - ((a : E) + (b : E)) =
          lambda * (b : E) := by
    unfold lambda
    ring

  rw [hid, pow_two] at hd
  exact hbE
    ((mul_dvd_mul_iff_left lambda_prime.ne_zero).mp hd)

/-- Remove λ from the linear factor; the quotient is λ-free. -/
theorem exists_lambda_free_linear_quotient
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    ∃ Y : E,
      (a : E) + omega * (b : E) = lambda * Y ∧
      ¬ lambda ∣ Y := by
  obtain ⟨Y, hY⟩ := lambda_dvd_int_linear_factor hS
  refine ⟨Y, hY, ?_⟩

  intro hd
  obtain ⟨t, ht⟩ := hd
  apply lambda_sq_not_dvd_int_linear_factor hab hS
  refine ⟨t, ?_⟩
  rw [hY, ht]
  ring

/-- Remove λ from the second linear factor as well. -/
theorem exists_lambda_free_second_quotient
    {a b : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    ∃ Z : E,
      (a : E) + omega ^ 2 * (b : E) = lambda * Z ∧
      ¬ lambda ∣ Z := by
  have hS' : (3 : ℤ) ∣ b + a := by
    simpa only [add_comm] using hS

  obtain ⟨Y, hY, hfree⟩ :=
    exists_lambda_free_linear_quotient hab.symm hS'

  refine ⟨omega ^ 2 * Y, ?_, ?_⟩
  · calc
      (a : E) + omega ^ 2 * (b : E) =
          omega ^ 3 * (a : E) + omega ^ 2 * (b : E) := by
            rw [omega_cube]
            ring
      _ = omega ^ 2 * ((b : E) + omega * (a : E)) := by
        ring
      _ = lambda * (omega ^ 2 * Y) := by
        rw [hY]
        ring

  · intro hd
    have hd' := dvd_mul_of_dvd_right hd omega
    have heq : omega * (omega ^ 2 * Y) = Y := by
      calc
        omega * (omega ^ 2 * Y) = omega ^ 3 * Y := by ring
        _ = Y := by rw [omega_cube]; ring
    rw [heq] at hd'
    exact hfree hd'

/-- A common divisor of the two Eisenstein linear factors divides λ. -/
theorem common_dvd_two_int_linear_factors
    {a b : ℤ} {d : E}
    (hab : IsCoprime a b)
    (h₁ : d ∣ (a : E) + omega * (b : E))
    (h₂ : d ∣ (a : E) + omega ^ 2 * (b : E)) :
    d ∣ lambda := by
  have hfour : omega ^ 4 = omega := by
    calc
      omega ^ 4 = omega ^ 3 * omega := by ring
      _ = omega := by rw [omega_cube]; ring

  have hroot : omega ^ 2 + omega = -1 := by
    linear_combination omega_relation

  have hid :
      (-omega) * ((a : E) + omega * (b : E))
        - omega ^ 2 * ((a : E) + omega ^ 2 * (b : E)) =
          (a : E) + (b : E) := by
    calc
      _ = -(omega ^ 2 + omega) * (a : E)
          - (omega ^ 4 + omega ^ 2) * (b : E) := by ring
      _ = (a : E) + (b : E) := by
        rw [hfour, add_comm omega (omega ^ 2), hroot]
        ring

  have hsum : d ∣ (a : E) + (b : E) := by
    have hd := dvd_sub
      (dvd_mul_of_dvd_right h₁ (-omega))
      (dvd_mul_of_dvd_right h₂ (omega ^ 2))
    rw [hid] at hd
    exact hd

  exact common_dvd_int_factors hab hsum h₁

/-- After removing λ, the two quotients are coprime. -/
theorem linear_quotients_coprime
    {a b : ℤ} {Y Z : E}
    (hab : IsCoprime a b)
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hZ : (a : E) + omega ^ 2 * (b : E) = lambda * Z)
    (hYfree : ¬ lambda ∣ Y) :
    IsCoprime Y Z := by
  have hcop : IsCoprime lambda Y :=
    lambda_prime.coprime_iff_not_dvd.mpr hYfree

  have hrel : IsRelPrime Y Z := by
    intro d hdY hdZ

    have h₁ : d ∣ (a : E) + omega * (b : E) := by
      rw [hY]
      exact dvd_mul_of_dvd_right hdY lambda

    have h₂ : d ∣ (a : E) + omega ^ 2 * (b : E) := by
      rw [hZ]
      exact dvd_mul_of_dvd_right hdZ lambda

    have hdLambda : d ∣ lambda :=
      common_dvd_two_int_linear_factors hab h₁ h₂

    exact hcop.isUnit_of_dvd' hdLambda hdY

  exact hrel.isCoprime
/-- The reduced factors, with a unit adjustment, multiply to a cube. -/
theorem adjusted_quotients_product
    {a b u : ℤ} {Y Z : E}
    (hQ : cubeFactor a b = 3 * u ^ 3)
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hZ : (a : E) + omega ^ 2 * (b : E) = lambda * Z) :
    (-omega * Y) * Z = (u : E) ^ 3 := by
  have hQcast :
      (a : E) ^ 2 - (a : E) * (b : E) + (b : E) ^ 2 =
        3 * (u : E) ^ 3 := by
    unfold cubeFactor at hQ
    exact_mod_cast hQ

  have hprod :
      (3 : E) * ((-omega * Y) * Z) =
        3 * (u : E) ^ 3 := by
    calc
      _ = lambda ^ 2 * (Y * Z) := by
        rw [lambda_sq]
        ring
      _ = (lambda * Y) * (lambda * Z) := by ring
      _ = ((a : E) + omega * (b : E)) *
          ((a : E) + omega ^ 2 * (b : E)) := by
        rw [← hY, ← hZ]
      _ = (a : E) ^ 2 - (a : E) * (b : E)
          + (b : E) ^ 2 :=
        door_eisenstein_pair (a : E) (b : E)
          omega omega_relation
      _ = 3 * (u : E) ^ 3 := hQcast

  exact mul_left_cancel₀ (by norm_num : (3 : E) ≠ 0) hprod

/-- Multiplying the first quotient by -ω preserves coprimality. -/
theorem adjusted_quotients_coprime
    {Y Z : E}
    (hcop : IsCoprime Y Z) :
    IsCoprime (-omega * Y) Z := by
  obtain ⟨r, s, hrs⟩ := hcop
  refine ⟨r * (-omega ^ 2), s, ?_⟩
  calc
    (r * (-omega ^ 2)) * (-omega * Y) + s * Z =
        omega ^ 3 * (r * Y) + s * Z := by ring
    _ = 1 := by
      rw [omega_cube, one_mul]
      exact hrs

/-- Both adjusted quotients are cubes up to unit multipliers. -/
theorem adjusted_quotients_are_cubes
    {a b u : ℤ} {Y Z : E}
    (hab : IsCoprime a b)
    (hQ : cubeFactor a b = 3 * u ^ 3)
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hZ : (a : E) + omega ^ 2 * (b : E) = lambda * Z)
    (hYfree : ¬ lambda ∣ Y) :
    (∃ W : E, Associated (W ^ 3) (-omega * Y)) ∧
    (∃ V : E, Associated (V ^ 3) Z) := by
  have hcop : IsCoprime (-omega * Y) Z :=
    adjusted_quotients_coprime
      (linear_quotients_coprime hab hY hZ hYfree)

  have hprod : (-omega * Y) * Z = (u : E) ^ 3 :=
    adjusted_quotients_product hQ hY hZ

  constructor
  · exact exists_associated_pow_of_mul_eq_pow' hcop hprod
  · exact exists_associated_pow_of_mul_eq_pow'
      hcop.symm (by simpa only [mul_comm] using hprod)

/-- Mathlib's integral power basis for the Eisenstein ring. -/
noncomputable def integerPowerBasis : PowerBasis ℤ E :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

theorem integerPowerBasis_gen :
    integerPowerBasis.gen = omega := by
  exact
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen

theorem integerPowerBasis_dim :
    integerPowerBasis.dim = 2 := by
  change
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

/-- Index the two basis elements by 0 and 1. -/
noncomputable def integerBasis : Module.Basis (Fin 2) ℤ E :=
  integerPowerBasis.basis.reindex
    (finCongr integerPowerBasis_dim)

theorem integerBasis_apply (i : Fin 2) :
    integerBasis i = omega ^ (i : ℕ) := by
  unfold integerBasis
  rw [Module.Basis.reindex_apply,
      integerPowerBasis.basis_eq_pow,
      integerPowerBasis_gen]
  rfl

/-- Every Eisenstein integer has the form r + sω,
with ordinary integer coefficients. -/
theorem exists_integer_coordinates (W : E) :
    ∃ r s : ℤ, W = (r : E) + (s : E) * omega := by
  refine ⟨integerBasis.repr W 0, integerBasis.repr W 1, ?_⟩
  have h := integerBasis.sum_repr W
  simp only [Fin.sum_univ_two, integerBasis_apply] at h
  simpa [Algebra.smul_def] using h.symm

/-- Recover the two coordinates of r + sω. -/
theorem integerBasis_repr_coordinates (r s : ℤ) :
    integerBasis.repr ((r : E) + (s : E) * omega) 0 = r ∧
    integerBasis.repr ((r : E) + (s : E) * omega) 1 = s := by
  have hzero : integerBasis 0 = 1 := by
    simpa using integerBasis_apply (0 : Fin 2)
  have hone : integerBasis 1 = omega := by
    simpa using integerBasis_apply (1 : Fin 2)

  have heq :
      (r : E) + (s : E) * omega =
        r • integerBasis 0 + s • integerBasis 1 := by
    rw [hzero, hone]
    simp [Algebra.smul_def]

  rw [heq]
  simp only [map_add, map_smul, Module.Basis.repr_self]
  constructor <;> simp

/-- Equal Eisenstein integers have equal integer coordinates. -/
theorem integer_coordinates_eq
    {r s t v : ℤ}
    (h : (r : E) + (s : E) * omega =
      (t : E) + (v : E) * omega) :
    r = t ∧ s = v := by
  constructor
  · have hc := congrArg (fun W : E => integerBasis.repr W 0) h
    rw [(integerBasis_repr_coordinates r s).1,
        (integerBasis_repr_coordinates t v).1] at hc
    exact hc
  · have hc := congrArg (fun W : E => integerBasis.repr W 1) h
    rw [(integerBasis_repr_coordinates r s).2,
        (integerBasis_repr_coordinates t v).2] at hc
    exact hc

/-- Multiplication by λ in integer coordinates. -/
theorem lambda_mul_coordinates (r s : ℤ) :
    lambda * ((r : E) + (s : E) * omega) =
      ((-r - s : ℤ) : E) +
        ((r - 2 * s : ℤ) : E) * omega := by
  unfold lambda
  push_cast
  linear_combination (s : E) * omega_relation

/-- The factor of 9 forces the quotient's ω-coordinate
to be a multiple of 3. -/
theorem linear_quotient_second_coordinate
    {a b r s v : ℤ} {Y : E}
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hcoords : Y = (r : E) + (s : E) * omega)
    (hS : a + b = 9 * v ^ 3) :
    s = -3 * v ^ 3 := by
  have heq :
      (a : E) + (b : E) * omega =
        ((-r - s : ℤ) : E) +
          ((r - 2 * s : ℤ) : E) * omega := by
    calc
      _ = (a : E) + omega * (b : E) := by ring
      _ = lambda * Y := hY
      _ = lambda * ((r : E) + (s : E) * omega) := by
        rw [hcoords]
      _ = _ := lambda_mul_coordinates r s

  obtain ⟨ha, hb⟩ := integer_coordinates_eq heq
  nlinarith [ha, hb, hS]

/-- Expand an Eisenstein cube using our earlier coefficient formulas. -/
theorem cube_coordinates (x y : ℤ) :
    ((x : E) + (y : E) * omega) ^ 3 =
      (descentA x y : E) + (descentB x y : E) * omega := by
  unfold descentA descentB
  push_cast
  linear_combination
    (y : E) ^ 3 * omega_cube +
      3 * (x : E) * (y : E) ^ 2 * omega_relation

/-- Every Eisenstein cube is congruent to an integer modulo 3. -/
theorem cube_congruent_integer (W : E) :
    ∃ n : ℤ, (3 : E) ∣ W ^ 3 - (n : E) := by
  obtain ⟨x, y, hW⟩ := exists_integer_coordinates W
  refine ⟨descentA x y,
    (x : E) * (y : E) * ((x : E) - (y : E)) * omega, ?_⟩
  rw [hW, cube_coordinates]
  unfold descentB
  push_cast
  ring

/-- The factor of 9 makes our linear quotient congruent
to an integer modulo 3. -/
theorem linear_quotient_congruent_integer
    {a b v : ℤ} {Y : E}
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hS : a + b = 9 * v ^ 3) :
    ∃ n : ℤ, (3 : E) ∣ Y - (n : E) := by
  obtain ⟨r, s, hcoords⟩ := exists_integer_coordinates Y
  have hs : s = -3 * v ^ 3 :=
    linear_quotient_second_coordinate hY hcoords hS
  refine ⟨r, -(v : E) ^ 3 * omega, ?_⟩
  rw [hcoords, hs]
  push_cast
  ring

/-- Cancel a 3-free integer from a congruence in the Eisenstein ring. -/
theorem congruent_integer_of_mul_congruent_integer
    {e : E} {n m : ℤ}
    (hn : ¬ (3 : ℤ) ∣ n)
    (h : (3 : E) ∣ e * (n : E) - (m : E)) :
    ∃ k : ℤ, (3 : E) ∣ e - (k : E) := by
  have hp : Prime (3 : ℤ) := by norm_num
  have hcop : IsCoprime (3 : ℤ) n :=
    hp.coprime_iff_not_dvd.mpr hn
  obtain ⟨r, s, hrs⟩ := hcop

  have hcast :
      (r : E) * 3 + (s : E) * (n : E) = 1 := by
    exact_mod_cast hrs

  have hfirst : (3 : E) ∣ (r : E) * 3 * e := by
    refine ⟨(r : E) * e, ?_⟩
    ring

  have hd := dvd_add hfirst
    (dvd_mul_of_dvd_right h (s : E))

  have hid :
      (r : E) * 3 * e +
        (s : E) * (e * (n : E) - (m : E)) =
      ((r : E) * 3 + (s : E) * (n : E)) * e -
        ((s * m : ℤ) : E) := by
    push_cast
    ring

  rw [hid, hcast, one_mul] at hd
  exact ⟨s * m, hd⟩

/-- The integer residue of a λ-free cube is 3-free. -/
theorem cube_integer_residue_three_free
    {W : E} {n : ℤ}
    (hfree : ¬ lambda ∣ W)
    (hcong : (3 : E) ∣ W ^ 3 - (n : E)) :
    ¬ (3 : ℤ) ∣ n := by
  intro hn
  have hdiff : lambda ∣ W ^ 3 - (n : E) :=
    dvd_trans lambda_dvd_three hcong
  have hnE : lambda ∣ (n : E) :=
    (lambda_dvd_intCast_iff n).mpr hn
  have hcube : lambda ∣ W ^ 3 := by
    simpa only [sub_add_cancel] using dvd_add hdiff hnE
  exact hfree (lambda_prime.dvd_of_dvd_pow hcube)

/-- A λ-free quotient congruent to an integer forces
its cube-extraction unit to be congruent to an integer. -/
theorem cube_unit_congruent_integer
    {Y W : E} (e : Eˣ)
    (heq : Y = (e : E) * W ^ 3)
    (hfree : ¬ lambda ∣ Y)
    (hcong : ∃ m : ℤ, (3 : E) ∣ Y - (m : E)) :
    ∃ k : ℤ, (3 : E) ∣ (e : E) - (k : E) := by
  have hWfree : ¬ lambda ∣ W := by
    intro hd
    apply hfree
    rw [heq]
    exact dvd_mul_of_dvd_right
      (dvd_pow hd (by decide : (3 : ℕ) ≠ 0)) (e : E)

  obtain ⟨n, hn⟩ := cube_congruent_integer W
  have hnfree : ¬ (3 : ℤ) ∣ n :=
    cube_integer_residue_three_free hWfree hn
  obtain ⟨m, hm⟩ := hcong

  have hprod : (3 : E) ∣ (e : E) * (n : E) - (m : E) := by
    have hd := dvd_sub hm
      (dvd_mul_of_dvd_right hn (e : E))
    rw [heq] at hd
    have hid :
        ((e : E) * W ^ 3 - (m : E)) -
          (e : E) * (W ^ 3 - (n : E)) =
        (e : E) * (n : E) - (m : E) := by ring
    rw [hid] at hd
    exact hd

  exact congruent_integer_of_mul_congruent_integer hnfree hprod

/-- The remaining cube-extraction unit is only a sign. -/
theorem cube_unit_eq_one_or_neg_one
    {Y W : E} (e : Eˣ)
    (heq : Y = (e : E) * W ^ 3)
    (hfree : ¬ lambda ∣ Y)
    (hcong : ∃ m : ℤ, (3 : E) ∣ Y - (m : E)) :
    e = 1 ∨ e = -1 := by
  obtain ⟨n, hn⟩ :=
    cube_unit_congruent_integer e heq hfree hcong

  have hthree : lambda ^ 2 ∣ (3 : E) := by
    simpa using
      (lambda_sq_dvd_int_sum
        (a := (3 : ℤ)) (b := (0 : ℤ)) (by norm_num))

  apply
    IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) e
  change ∃ k : ℤ, lambda ^ 2 ∣ (e : E) - (k : E)
  exact ⟨n, dvd_trans hthree hn⟩

/-- ω is a unit, with inverse ω². -/
noncomputable def omegaUnit : Eˣ where
  val := omega
  inv := omega ^ 2
  val_inv := by
    calc
      omega * omega ^ 2 = omega ^ 3 := by ring
      _ = 1 := omega_cube
  inv_val := by
    calc
      omega ^ 2 * omega = omega ^ 3 := by ring
      _ = 1 := omega_cube

@[simp] theorem omegaUnit_coe :
    (omegaUnit : E) = omega := rfl

/-- Under the factor-of-9 condition, our original quotient
is an actual cube, with the sign absorbed into its root. -/
theorem linear_quotient_is_cube
    {a b v : ℤ} {Y : E}
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hS : a + b = 9 * v ^ 3)
    (hfree : ¬ lambda ∣ Y)
    (hAssociated :
      ∃ W : E, Associated (W ^ 3) (-omega * Y)) :
    ∃ T : E, Y = T ^ 3 := by
  obtain ⟨W, e, he⟩ := hAssociated

  let f : Eˣ := (-omegaUnit ^ 2) * e
  have hf : (f : E) = (-omega ^ 2) * (e : E) := by
    simp [f]

  have heq : Y = (f : E) * W ^ 3 := by
    rw [hf]
    calc
      Y = omega ^ 3 * Y := by rw [omega_cube]; ring
      _ = (-omega ^ 2) * (-omega * Y) := by ring
      _ = (-omega ^ 2) * (W ^ 3 * (e : E)) := by rw [he]
      _ = ((-omega ^ 2) * (e : E)) * W ^ 3 := by ring

  have hcong : ∃ n : ℤ, (3 : E) ∣ Y - (n : E) :=
    linear_quotient_congruent_integer hY hS

  rcases cube_unit_eq_one_or_neg_one f heq hfree hcong with hfOne | hfNeg
  · refine ⟨W, ?_⟩
    simpa [hfOne] using heq
  · refine ⟨-W, ?_⟩
    calc
      Y = -W ^ 3 := by simpa [hfNeg] using heq
      _ = (-W) ^ 3 := by ring

/-- Recover the integer parametrisation from the extracted cube. -/
theorem integer_parametrisation_of_linear_quotient
    {a b v : ℤ} {Y : E}
    (hY : (a : E) + omega * (b : E) = lambda * Y)
    (hS : a + b = 9 * v ^ 3)
    (hfree : ¬ lambda ∣ Y)
    (hAssociated :
      ∃ W : E, Associated (W ^ 3) (-omega * Y)) :
    ∃ x y : ℤ,
      a = descentA x y + descentB x y ∧
      b = 2 * descentB x y - descentA x y := by
  obtain ⟨T, hT⟩ :=
    linear_quotient_is_cube hY hS hfree hAssociated
  obtain ⟨x, y, hcoords⟩ := exists_integer_coordinates (-T)

  have hfactor :
      (a : E) + (b : E) * omega =
        ((descentA x y + descentB x y : ℤ) : E) +
          ((2 * descentB x y - descentA x y : ℤ) : E) *
            omega := by
    calc
      _ = (a : E) + omega * (b : E) := by ring
      _ = lambda * Y := hY
      _ = lambda * T ^ 3 := by rw [hT]
      _ = (1 - omega) * (-T) ^ 3 := by
        unfold lambda
        ring
      _ = (1 - omega) *
          ((x : E) + (y : E) * omega) ^ 3 := by
        rw [hcoords]
      _ = (1 - omega) *
          ((descentA x y : E) +
            (descentB x y : E) * omega) := by
        rw [cube_coordinates]
      _ = _ := by
        push_cast
        linear_combination
          -(descentB x y : E) * omega_relation

  exact ⟨x, y, integer_coordinates_eq hfactor⟩

/-- A coprime cube solution in the 3-divisible-sum branch
admits our integer parametrisation and a new cube product. -/
theorem parametrisation_of_sum_cubes
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b)
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    ∃ x y v : ℤ,
      a = descentA x y + descentB x y ∧
      b = 2 * descentB x y - descentA x y ∧
      x * y * (x - y) = v ^ 3 := by
  obtain ⟨v, hv⟩ := sum_eq_nine_mul_cube hab hS hc
  obtain ⟨u, hu⟩ := cubeFactor_eq_three_mul_cube hab hS hc

  obtain ⟨Y, hY, hYfree⟩ :=
    exists_lambda_free_linear_quotient hab hS
  obtain ⟨Z, hZ, _hZfree⟩ :=
    exists_lambda_free_second_quotient hab hS

  have hAssociated :
      ∃ W : E, Associated (W ^ 3) (-omega * Y) :=
    (adjusted_quotients_are_cubes
      hab hu hY hZ hYfree).1

  obtain ⟨x, y, ha, hb⟩ :=
    integer_parametrisation_of_linear_quotient
      hY hv hYfree hAssociated

  refine ⟨x, y, v, ha, hb, ?_⟩
  have hsum := descent_sum x y
  rw [← ha, ← hb] at hsum
  nlinarith [hv, hsum]

/-- Coprimality of the original inputs forces coprimality
of the parametrisation coordinates. -/
theorem parametrisation_coordinates_coprime
    {a b x y : ℤ}
    (hab : IsCoprime a b)
    (ha : a = descentA x y + descentB x y)
    (hb : b = 2 * descentB x y - descentA x y) :
    IsCoprime x y := by
  have hrel : IsRelPrime x y := by
    intro d hdx hdy

    have hdA : d ∣ descentA x y := by
      unfold descentA
      exact dvd_add
        (dvd_sub
          (dvd_pow hdx (by decide : (3 : ℕ) ≠ 0))
          (dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_right hdx 3) (y ^ 2)))
        (dvd_pow hdy (by decide : (3 : ℕ) ≠ 0))

    have hdB : d ∣ descentB x y := by
      unfold descentB
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right hdx 3) y)
        (x - y)

    have hda : d ∣ a := by
      rw [ha]
      exact dvd_add hdA hdB

    have hdb : d ∣ b := by
      rw [hb]
      exact dvd_sub (dvd_mul_of_dvd_right hdB 2) hdA

    exact hab.isUnit_of_dvd' hda hdb

  exact hrel.isCoprime

/-- Coprime x and y make x, y, and x-y pairwise coprime. -/
theorem coordinates_pairwise_coprime
    {x y : ℤ}
    (hxy : IsCoprime x y) :
    IsCoprime x (x - y) ∧ IsCoprime y (x - y) := by
  obtain ⟨r, s, hrs⟩ := hxy
  constructor
  · refine ⟨r + s, -s, ?_⟩
    calc
      (r + s) * x + (-s) * (x - y) =
          r * x + s * y := by ring
      _ = 1 := hrs
  · refine ⟨r + s, r, ?_⟩
    calc
      (r + s) * y + r * (x - y) =
          r * x + s * y := by ring
      _ = 1 := hrs

/-- A cube product of these coprime factors yields
another sum-of-cubes equation. -/
theorem cube_solution_of_coordinate_product
    {x y v : ℤ}
    (hxy : IsCoprime x y)
    (hprod : x * y * (x - y) = v ^ 3) :
    ∃ r s t : ℤ,
      x = r ^ 3 ∧
      y = s ^ 3 ∧
      x - y = t ^ 3 ∧
      s ^ 3 + t ^ 3 = r ^ 3 := by
  obtain ⟨hxz, hyz⟩ := coordinates_pairwise_coprime hxy

  have hcop : IsCoprime (x * y) (x - y) :=
    hxz.mul_left hyz
  have hodd : Odd (3 : ℕ) := by decide

  obtain ⟨w, hw⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left hcop hodd hprod

  obtain ⟨r, hr⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left hxy hodd hw
  obtain ⟨s, hs⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_right hxy hodd hw
  obtain ⟨t, ht⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_right hcop hodd hprod

  refine ⟨r, s, t, hr, hs, ht, ?_⟩
  rw [← hr, ← hs, ← ht]
  ring

/-- A nonzero original solution makes the coordinate product nonzero. -/
theorem coordinate_product_ne_zero
    {a b c x y : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc0 : c ≠ 0)
    (ha : a = descentA x y + descentB x y)
    (hb : b = 2 * descentB x y - descentA x y) :
    x * y * (x - y) ≠ 0 := by
  have hsum : a + b = 9 * (x * y * (x - y)) := by
    calc
      a + b = 9 * x * y * (x - y) := by
        rw [ha, hb]
        exact descent_sum x y
      _ = 9 * (x * y * (x - y)) := by ring

  intro hzero
  have hcPow : c ^ 3 = 0 := by
    calc
      c ^ 3 = a ^ 3 + b ^ 3 := hc.symm
      _ = (a + b) * cubeFactor a b :=
        sum_cubes_factorisation a b
      _ = 0 := by
        rw [hsum, hzero]
        ring

  exact (pow_ne_zero 3 hc0) hcPow

/-- The extracted roots are nonzero, and the new inputs are coprime. -/
theorem coordinate_cube_roots_conditions
    {x y r s t : ℤ}
    (hxy : IsCoprime x y)
    (hprod : x * y * (x - y) ≠ 0)
    (hr : x = r ^ 3)
    (hs : y = s ^ 3)
    (ht : x - y = t ^ 3) :
    r ≠ 0 ∧ s ≠ 0 ∧ t ≠ 0 ∧ IsCoprime s t := by
  have hr0 : r ≠ 0 := by
    intro h
    apply hprod
    rw [hr, h]
    ring

  have hs0 : s ≠ 0 := by
    intro h
    apply hprod
    rw [hs, h]
    ring

  have ht0 : t ≠ 0 := by
    intro h
    apply hprod
    rw [ht, h]
    ring

  obtain ⟨_, hyz⟩ := coordinates_pairwise_coprime hxy
  rw [ht, hs] at hyz
  have hst : IsCoprime s t :=
    (IsCoprime.pow_iff
      (m := 3) (n := 3) (by decide) (by decide)).mp hyz

  exact ⟨hr0, hs0, ht0, hst⟩

/-- Construct another nonzero coprime cube solution.
A strict decrease remains to be proved separately. -/
theorem exists_new_coprime_cube_solution
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b)
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc0 : c ≠ 0) :
    ∃ r s t : ℤ,
      r ≠ 0 ∧ s ≠ 0 ∧ t ≠ 0 ∧
      IsCoprime s t ∧ s ^ 3 + t ^ 3 = r ^ 3 := by
  obtain ⟨x, y, v, ha, hb, hprod⟩ :=
    parametrisation_of_sum_cubes hab hS hc

  have hxy : IsCoprime x y :=
    parametrisation_coordinates_coprime hab ha hb
  have hnonzero : x * y * (x - y) ≠ 0 :=
    coordinate_product_ne_zero hc hc0 ha hb

  obtain ⟨r, s, t, hr, hs, ht, heq⟩ :=
    cube_solution_of_coordinate_product hxy hprod
  obtain ⟨hr0, hs0, ht0, hst⟩ :=
    coordinate_cube_roots_conditions hxy hnonzero hr hs ht

  exact ⟨r, s, t, hr0, hs0, ht0, hst, heq⟩

/-- Every positive factor is smaller than three times
the product of all four positive factors. -/
theorem factor_lt_three_product
    {A B C U : ℕ}
    (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hU : 0 < U) :
    A < 3 * U * A * B * C := by
  have hAB : A ≤ A * B := by
    simpa using Nat.mul_le_mul_left A (show 1 ≤ B by omega)
  have hABC : A * B ≤ A * B * C := by
    simpa using
      Nat.mul_le_mul_left (A * B) (show 1 ≤ C by omega)
  have hUABC : A * B * C ≤ U * (A * B * C) := by
    simpa using
      Nat.mul_le_mul_right (A * B * C) (show 1 ≤ U by omega)
  have hp : 0 < U * (A * B * C) := by positivity
  calc
    A ≤ A * B := hAB
    _ ≤ A * B * C := hABC
    _ ≤ U * (A * B * C) := hUABC
    _ < 3 * (U * (A * B * C)) := by omega
    _ = 3 * U * A * B * C := by ring

/-- All three extracted roots are smaller than the old output. -/
theorem coordinate_roots_strictly_smaller
    {a b c u v x y r s t : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc0 : c ≠ 0)
    (hQ : cubeFactor a b = 3 * u ^ 3)
    (hS : a + b = 9 * v ^ 3)
    (hprod : x * y * (x - y) = v ^ 3)
    (hr : x = r ^ 3)
    (hs : y = s ^ 3)
    (ht : x - y = t ^ 3)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0) (ht0 : t ≠ 0) :
    r.natAbs < c.natAbs ∧
    s.natAbs < c.natAbs ∧
    t.natAbs < c.natAbs := by
  have hodd : Odd (3 : ℕ) := by decide

  have hv : v = r * s * t := by
    apply hodd.pow_injective
    calc
      v ^ 3 = x * y * (x - y) := hprod.symm
      _ = (r * s * t) ^ 3 := by
        rw [ht, hr, hs]
        ring

  have hceq : c = 3 * u * v := by
    apply hodd.pow_injective
    calc
      c ^ 3 = a ^ 3 + b ^ 3 := hc.symm
      _ = (a + b) * cubeFactor a b :=
        sum_cubes_factorisation a b
      _ = (3 * u * v) ^ 3 := by
        rw [hS, hQ]
        ring

  have hu0 : u ≠ 0 := by
    intro hu
    apply hc0
    rw [hceq, hu]
    ring

  have hU : 0 < u.natAbs := Int.natAbs_pos.mpr hu0
  have hR : 0 < r.natAbs := Int.natAbs_pos.mpr hr0
  have hSpos : 0 < s.natAbs := Int.natAbs_pos.mpr hs0
  have hT : 0 < t.natAbs := Int.natAbs_pos.mpr ht0

  have hsize :
      c.natAbs =
        3 * u.natAbs * r.natAbs * s.natAbs * t.natAbs := by
    rw [hceq, hv]
    norm_num [Int.natAbs_mul]
    ring

  constructor
  · rw [hsize]
    exact factor_lt_three_product hR hSpos hT hU
  · constructor
    · rw [hsize]
      have h := factor_lt_three_product hSpos hR hT hU
      nlinarith [h]
    · rw [hsize]
      have h := factor_lt_three_product hT hR hSpos hU
      nlinarith [h]

/-- Construct roots with all inherited conditions and strict bounds. -/
theorem exists_smaller_cube_roots
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b)
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc0 : c ≠ 0) :
    ∃ r s t : ℤ,
      r ≠ 0 ∧ s ≠ 0 ∧ t ≠ 0 ∧
      IsCoprime r s ∧ IsCoprime r t ∧ IsCoprime s t ∧
      s ^ 3 + t ^ 3 = r ^ 3 ∧
      r.natAbs < c.natAbs ∧
      s.natAbs < c.natAbs ∧
      t.natAbs < c.natAbs := by
  obtain ⟨x, y, v, ha, hb, hprod⟩ :=
    parametrisation_of_sum_cubes hab hS hc
  obtain ⟨u, hu⟩ := cubeFactor_eq_three_mul_cube hab hS hc

  have hxy := parametrisation_coordinates_coprime hab ha hb
  have hnonzero := coordinate_product_ne_zero hc hc0 ha hb

  obtain ⟨r, s, t, hr, hs, ht, heq⟩ :=
    cube_solution_of_coordinate_product hxy hprod
  obtain ⟨hr0, hs0, ht0, hst⟩ :=
    coordinate_cube_roots_conditions hxy hnonzero hr hs ht

  have hrs : IsCoprime r s := by
    have h := hxy
    rw [hr, hs] at h
    exact
      (IsCoprime.pow_iff
        (m := 3) (n := 3) (by decide) (by decide)).mp h

  have hrt : IsCoprime r t := by
    have h := (coordinates_pairwise_coprime hxy).1
    rw [ht, hr] at h
    exact
      (IsCoprime.pow_iff
        (m := 3) (n := 3) (by decide) (by decide)).mp h

  have hv : a + b = 9 * v ^ 3 := by
    have hsum := descent_sum x y
    rw [← ha, ← hb] at hsum
    nlinarith [hsum, hprod]

  obtain ⟨hR, hSroot, hT⟩ :=
    coordinate_roots_strictly_smaller
      hc hc0 hu hv hprod hr hs ht hr0 hs0 ht0

  exact
    ⟨r, s, t, hr0, hs0, ht0, hrs, hrt, hst,
      heq, hR, hSroot, hT⟩

/-- Cubes equal their bases modulo 3, so a 3-divisible
output forces a 3-divisible input sum. -/
theorem three_dvd_sum_of_output
    {a b c : ℤ}
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (hc3 : (3 : ℤ) ∣ c) :
    (3 : ℤ) ∣ a + b := by
  have hcube : ∀ z : ZMod 3, z ^ 3 = z := by decide

  have hcast :
      (a : ZMod 3) ^ 3 + (b : ZMod 3) ^ 3 =
        (c : ZMod 3) ^ 3 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 3)) hc
    simpa only [Int.cast_add, Int.cast_pow] using h

  have hczero : (c : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd c 3).mpr
      (by simpa using hc3)

  have hs : (a : ZMod 3) + (b : ZMod 3) = 0 := by
    simpa only [hcube, hczero] using hcast

  have hsum : ((a + b : ℤ) : ZMod 3) = 0 := by
    simpa only [Int.cast_add] using hs

  simpa using
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 3).mp hsum

theorem coprime_neg_right_of_coprime
    {a b : ℤ} (hab : IsCoprime a b) :
    IsCoprime a (-b) := by
  obtain ⟨u, v, huv⟩ := hab
  refine ⟨u, -v, ?_⟩
  calc
    u * a + (-v) * (-b) = u * a + v * b := by ring
    _ = 1 := huv

/-- Reorient a solution into the 3-divisible-sum branch,
while retaining a bound on the output. -/
theorem reorient_cube_solution
    {a b c : ℤ} {M : ℕ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime a b)
    (hac : IsCoprime a c)
    (hbc : IsCoprime b c)
    (hc : a ^ 3 + b ^ 3 = c ^ 3)
    (haM : a.natAbs < M)
    (hbM : b.natAbs < M)
    (hcM : c.natAbs < M) :
    ∃ A B C : ℤ,
      A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
      IsCoprime A B ∧
      (3 : ℤ) ∣ A + B ∧
      A ^ 3 + B ^ 3 = C ^ 3 ∧ C.natAbs < M := by
  rcases three_dvd_some_of_sum_cubes hc with ha3 | hb3 | hc3
  · have heq : c ^ 3 + (-b) ^ 3 = a ^ 3 := by
      calc
        c ^ 3 + (-b) ^ 3 = c ^ 3 - b ^ 3 := by ring
        _ = a ^ 3 := by linarith [hc]
    exact
      ⟨c, -b, a, hc0, neg_ne_zero.mpr hb0, ha0,
        coprime_neg_right_of_coprime hbc.symm,
        three_dvd_sum_of_output heq ha3, heq, haM⟩
  · have heq : c ^ 3 + (-a) ^ 3 = b ^ 3 := by
      calc
        c ^ 3 + (-a) ^ 3 = c ^ 3 - a ^ 3 := by ring
        _ = b ^ 3 := by linarith [hc]
    exact
      ⟨c, -a, b, hc0, neg_ne_zero.mpr ha0, hb0,
        coprime_neg_right_of_coprime hac.symm,
        three_dvd_sum_of_output heq hb3, heq, hbM⟩
  · exact
      ⟨a, b, c, ha0, hb0, hc0, hab,
        three_dvd_sum_of_output hc hc3, hc, hcM⟩

/-- Coprimality of the inputs of a cube equation also
gives coprimality of the second input and output. -/
theorem coprime_output_right
    {a b c : ℤ}
    (hab : IsCoprime a b)
    (hb0 : b ≠ 0)
    (hc : a ^ 3 + b ^ 3 = c ^ 3) :
    IsCoprime b c := by
  apply isCoprime_of_prime_dvd
  · intro h
    exact hb0 h.1
  · intro p hp hpb hpc
    have hpaPow : p ∣ a ^ 3 := by
      have hd := dvd_sub
        (dvd_pow hpc (by decide : (3 : ℕ) ≠ 0))
        (dvd_pow hpb (by decide : (3 : ℕ) ≠ 0))
      have hid : c ^ 3 - b ^ 3 = a ^ 3 := by
        linarith [hc]
      rw [hid] at hd
      exact hd
    have hpa : p ∣ a := hp.dvd_of_dvd_pow hpaPow
    exact hp.not_isUnit (hab.isUnit_of_dvd' hpa hpb)

/-- Infinite descent on the output's absolute value. -/
theorem no_cube_solution_three_dvd_sum
    {a b c : ℤ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime a b)
    (hS : (3 : ℤ) ∣ a + b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have H :
      ∀ n : ℕ, ∀ A B C : ℤ,
        C.natAbs = n →
        A ≠ 0 → B ≠ 0 → C ≠ 0 →
        IsCoprime A B →
        (3 : ℤ) ∣ A + B →
        A ^ 3 + B ^ 3 = C ^ 3 → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A B C hsize hA hB hC hAB hsum heq

      obtain
        ⟨r, s, t, hr0, hs0, ht0, hrs, hrt, hst,
          hnew, hrM, hsM, htM⟩ :=
        exists_smaller_cube_roots hAB hsum heq hC

      obtain
        ⟨A', B', C', hA', hB', hC', hAB',
          hsum', heq', hlt⟩ :=
        reorient_cube_solution
          hs0 ht0 hr0 hst hrs.symm hrt.symm
          hnew hsM htM hrM

      have hlt' : C'.natAbs < n := by omega
      exact ih C'.natAbs hlt' A' B' C' rfl
        hA' hB' hC' hAB' hsum' heq'

  intro hc
  exact H c.natAbs a b c rfl ha0 hb0 hc0 hab hS hc

/-- No nonzero coprime integer cube solution exists. -/
theorem no_coprime_integer_cube_solution
    {a b c : ℤ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime a b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro hc
  have hbc := coprime_output_right hab hb0 hc
  have hac : IsCoprime a c :=
    coprime_output_right hab.symm ha0
      (by simpa only [add_comm] using hc)

  obtain
    ⟨A, B, C, hA, hB, hC, hAB, hsum, heq, _⟩ :=
    reorient_cube_solution
      (M := a.natAbs + b.natAbs + c.natAbs + 1)
      ha0 hb0 hc0 hab hac hbc hc
      (by omega) (by omega) (by omega)

  exact no_cube_solution_three_dvd_sum hA hB hC hAB hsum heq

/-- Fermat's Last Theorem for exponent three,
using the descent constructed in this file. -/
theorem fermatLastTheoremThree_via_descent :
    FermatLastTheoremFor 3 := by
  apply fermatLastTheoremFor_iff_int.mpr
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha0 hb0 hc0 hgcd hc

  have hgcdNeg : Finset.gcd {a, b, -c} id = 1 := by
    simpa [Finset.gcd_insert, Finset.gcd_singleton,
      ← Int.abs_eq_normalize] using hgcd

  have hzero : a ^ 3 + b ^ 3 + (-c) ^ 3 = 0 := by
    calc
      _ = (a ^ 3 + b ^ 3) - c ^ 3 := by ring
      _ = 0 := by rw [hc]; ring

  have hab : IsCoprime a b :=
    isCoprime_of_gcd_eq_one_of_FLT hgcdNeg hzero

  exact no_coprime_integer_cube_solution ha0 hb0 hc0 hab hc

/-- exponent-three proof covers every exponent divisible by three. -/
theorem fermatLastTheorem_of_three_dvd
    {n : ℕ} (hn : 3 ∣ n) :
    FermatLastTheoremFor n :=
  FermatLastTheoremFor.mono hn
    fermatLastTheoremThree_via_descent

end EisensteinBridge


end Hire
