import Mathlib.Tactic

namespace Hire
namespace ClassObstruction

/-- In the minus part, subtracting the conjugate doubles the class. -/
theorem sub_conjugate_eq_two_smul
    {G : Type*} [AddCommGroup G]
    (conj : G → G) (c : G)
    (hminus : conj c = -c) :
    c - conj c = (2 : ℕ) • c := by
  rw [hminus, sub_neg_eq_add, two_nsmul]

/-- A class killed by both 37 and 2 must vanish. -/
theorem eq_zero_of_thirty_seven_smul_eq_zero_of_two_smul_eq_zero
    {G : Type*} [AddCommGroup G]
    {c : G}
    (h37 : (37 : ℕ) • c = 0)
    (h2 : (2 : ℕ) • c = 0) :
    c = 0 := by
  have h36 : (36 : ℕ) • c = 0 := by
    calc
      (36 : ℕ) • c = (18 : ℕ) • ((2 : ℕ) • c) := by
        simp only [smul_smul]
        norm_num
      _ = 0 := by rw [h2, smul_zero]

  have h37' : (36 : ℕ) • c + c = 0 := by
    simpa only [show (37 : ℕ) = 36 + 1 from rfl,
      add_nsmul, one_nsmul] using h37

  simpa only [h36, zero_add] using h37'

/-- For a 37-torsion class in the minus part, the conjugate
difference vanishes exactly when the original class vanishes. -/
theorem sub_conjugate_eq_zero_iff
    {G : Type*} [AddCommGroup G]
    (conj : G → G) (c : G)
    (hminus : conj c = -c)
    (h37 : (37 : ℕ) • c = 0) :
    c - conj c = 0 ↔ c = 0 := by
  rw [sub_conjugate_eq_two_smul conj c hminus]
  constructor
  · intro h2
    exact
      eq_zero_of_thirty_seven_smul_eq_zero_of_two_smul_eq_zero
        h37 h2
  · intro hc
    rw [hc, smul_zero]

/-- An element-power representation gives an exact conjugate-ratio
identity, retaining the unit and ramified-factor contributions. -/
theorem conjugate_ratio_of_element_power
    {K : Type*} [Field K]
    (conj : K ≃+* K)
    {L u lam alpha : K} {m p : ℕ}
    (hL : L = u * lam ^ m * alpha ^ p) :
    L / conj L =
      (u / conj u) *
        (lam / conj lam) ^ m *
        (alpha / conj alpha) ^ p := by
  rw [hL]
  simp only [map_mul, map_pow]
  rw [mul_div_mul_comm, mul_div_mul_comm,
    ← div_pow, ← div_pow]

/-- If the first two conjugate ratios are N-th roots of unity,
the remaining discrepancy from a p-th power is also an
N-th root of unity. -/
theorem conjugate_ratio_eq_root_mul_power
    {K : Type*} [Field K]
    (conj : K ≃+* K)
    {L u lam alpha : K} {m p N : ℕ}
    (hL : L = u * lam ^ m * alpha ^ p)
    (hu : (u / conj u) ^ N = 1)
    (hlam : (lam / conj lam) ^ N = 1) :
    ∃ eta gamma : K,
      eta ^ N = 1 ∧
        L / conj L = eta * gamma ^ p := by
  refine ⟨(u / conj u) * (lam / conj lam) ^ m,
    alpha / conj alpha, ?_, ?_⟩
  · calc
      ((u / conj u) * (lam / conj lam) ^ m) ^ N =
          (u / conj u) ^ N *
            ((lam / conj lam) ^ m) ^ N := by
              rw [mul_pow]
      _ = 1 := by
        rw [← pow_mul, Nat.mul_comm m N, pow_mul, hu, hlam]
        simp
  · exact conjugate_ratio_of_element_power conj hL

end ClassObstruction
end Hire
