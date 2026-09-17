import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! The universal phase-balanced polynomial pair in Section 3. -/

namespace MathieuProperty.Hopf

abbrev Space := ℂ × ℂ

def a (z : Space) : ℝ := Complex.normSq z.1 + Complex.normSq z.2
def tau (z : Space) : ℝ := Complex.normSq z.1 - Complex.normSq z.2
def u (z : Space) : ℂ := 2 * z.1 * star z.2
def v (z : Space) : ℂ := 2 * z.2 * star z.1
def P (z : Space) : ℂ :=
  (a z + u z) * ((a z : ℂ) ^ 2 * v z - (2 * a z + u z) * (tau z : ℂ) ^ 2)
def Q (z : Space) : ℂ := u z

/-- The manuscript's Euclidean unit sphere, specified by its quadratic equation.
The ambient product norm on `Space` is not used to define this sphere. -/
def Sphere := {z : Space // a z = 1}
def p (z : Sphere) : ℂ := P z.val
def q (z : Sphere) : ℂ := Q z.val

theorem a_nonneg (z : Space) : 0 ≤ a z :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem a_eq_zero_iff (z : Space) : a z = 0 ↔ z = 0 := by
  simp only [a, add_eq_zero_iff_of_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _),
    Complex.normSq_eq_zero, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]

/-- Equation (3.2). -/
theorem relation (z : Space) : (a z : ℂ) ^ 2 = u z * v z + (tau z : ℂ) ^ 2 := by
  apply Complex.ext <;> simp [a, tau, u, v, Complex.normSq_apply, pow_two] <;> ring

/-- The homogeneous version of the defect-one identity. -/
theorem homogeneous_defect_one (z : Space) :
    u z * P z = (a z + u z) * ((a z : ℂ) ^ 4 - (a z + u z) ^ 2 * (tau z : ℂ) ^ 2) := by
  have h := relation z
  dsimp [P]
  linear_combination -(a z + u z) * (a z : ℂ) ^ 2 * h

/-- Equation (3.7), stated globally on the sphere without localization. -/
theorem defect_one (z : Space) (hz : a z = 1) :
    u z * P z = (1 + u z) * (1 - (1 + u z) ^ 2 * (tau z : ℂ) ^ 2) := by
  simpa [hz] using homogeneous_defect_one z

theorem a_smul (c : ℂ) (z : Space) : a (c • z) = Complex.normSq c * a z := by
  simp [a, Complex.normSq_mul, mul_add]

theorem tau_smul (c : ℂ) (z : Space) : tau (c • z) = Complex.normSq c * tau z := by
  simp [tau, Complex.normSq_mul, mul_sub]

theorem u_smul (c : ℂ) (z : Space) : u (c • z) = (Complex.normSq c : ℂ) * u z := by
  simp only [u, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, star_mul,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

theorem v_smul (c : ℂ) (z : Space) : v (c • z) = (Complex.normSq c : ℂ) * v z := by
  simp only [v, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, star_mul,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

theorem P_smul (c : ℂ) (z : Space) :
    P (c • z) = (Complex.normSq c : ℂ) ^ 4 * P z := by
  simp only [P, a_smul, tau_smul, u_smul, v_smul, Complex.ofReal_mul]
  ring

theorem Q_smul (c : ℂ) (z : Space) :
    Q (c • z) = (Complex.normSq c : ℂ) * Q z := u_smul c z

/-- Real homogeneity holds for every real scalar, hence for the manuscript's r≥0. -/
theorem homogeneity (r : ℝ) (z : Space) :
    P ((r : ℂ) • z) = (r : ℂ) ^ 8 * P z ∧
    Q ((r : ℂ) • z) = (r : ℂ) ^ 2 * Q z := by
  rw [P_smul, Q_smul, Complex.normSq_ofReal, Complex.ofReal_mul]
  constructor <;> ring

/-- Common unit phases fix each quadratic quantity and both universal polynomials. -/
theorem phase_balance (c : ℂ) (hc : Complex.normSq c = 1) (z : Space) :
    a (c • z) = a z ∧ tau (c • z) = tau z ∧
    u (c • z) = u z ∧ v (c • z) = v z ∧ P (c • z) = P z ∧ Q (c • z) = Q z := by
  simp [a_smul, tau_smul, u_smul, v_smul, P_smul, Q_smul, hc]

theorem phase_balance_of_norm_eq_one (c : ℂ) (hc : ‖c‖ = 1) (z : Space) :
    a (c • z) = a z ∧ tau (c • z) = tau z ∧
    u (c • z) = u z ∧ v (c • z) = v z ∧ P (c • z) = P z ∧ Q (c • z) = Q z :=
  phase_balance c (by simp [Complex.normSq_eq_norm_sq, hc]) z

end MathieuProperty.Hopf
