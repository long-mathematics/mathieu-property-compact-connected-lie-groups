import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Normalized phase integration extracts the constant term of any finite Laurent
polynomial, including negative exponents and every nonzero complex radius. -/

noncomputable section
open MeasureTheory

namespace MathieuProperty

theorem integral_integer_frequency (n : ℤ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((n : ℂ) * Complex.I * θ)) =
      if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn, integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero)]
    have hperiod : (n : ℂ) * Complex.I * (2 * Real.pi : ℝ) =
        (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [hperiod, Complex.exp_int_mul_two_pi_mul_I]
    simp

theorem phase_monomial_eq (r : ℂ) (n : ℤ) (θ : ℝ) :
    (r * Complex.exp (Complex.I * θ)) ^ n =
      r ^ n * Complex.exp ((n : ℂ) * Complex.I * θ) := by
  rw [mul_zpow, ← Complex.exp_int_mul]
  congr 2
  ring

theorem continuous_phase_monomial (r : ℂ) (n : ℤ) :
    Continuous fun θ : ℝ => (r * Complex.exp (Complex.I * θ)) ^ n := by
  simp_rw [phase_monomial_eq]
  fun_prop

theorem integral_phase_monomial (r : ℂ) (n : ℤ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), (r * Complex.exp (Complex.I * θ)) ^ n) =
      if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  simp_rw [phase_monomial_eq]
  rw [intervalIntegral.integral_const_mul, integral_integer_frequency]
  split_ifs with hn <;> simp [hn]

/-- Finite Laurent evaluation along a phase circle. -/
def laurentPhase (p : LaurentPolynomial ℂ) (r : ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ p.coeff.support, p.coeff n * (r * Complex.exp (Complex.I * θ)) ^ n

/-- Agreement with mathlib's Laurent evaluation at a unit; nonzero radius is
essential to interpret negative powers as Laurent evaluation. -/
theorem laurentPhase_eq_smeval (p : LaurentPolynomial ℂ) (r : ℂ) (hr : r ≠ 0) (θ : ℝ) :
    laurentPhase p r θ = p.smeval
      (Units.mk0 (r * Complex.exp (Complex.I * θ)) (mul_ne_zero hr (Complex.exp_ne_zero _))) := by
  simp [laurentPhase, LaurentPolynomial.smeval, Finsupp.sum, smul_eq_mul]

theorem continuous_laurentPhase (p : LaurentPolynomial ℂ) (r : ℂ) :
    Continuous (laurentPhase p r) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_phase_monomial r n)

/-- Manuscript phase extraction identity, with the exact `1/(2π)` normalization. -/
theorem phase_integral_constantTerm (p : LaurentPolynomial ℂ) (r : ℂ) :
    (1 / (2 * Real.pi : ℂ)) *
      (∫ θ in (0 : ℝ)..(2 * Real.pi), laurentPhase p r θ) = p.coeff 0 := by
  unfold laurentPhase
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_phase_monomial, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    by_cases hp : 0 ∈ p.coeff.support
    · rw [ite_eq_left hp]
      have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi))
      field_simp
    · rw [ite_eq_right hp, mul_zero]
      exact (Finsupp.notMem_support_iff.mp hp).symm
  · intro n hn
    exact (continuous_const.mul (continuous_phase_monomial r n)).intervalIntegrable 0 (2 * Real.pi)

end MathieuProperty
