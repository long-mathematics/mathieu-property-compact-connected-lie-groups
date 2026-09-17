import MathieuProperty.PhaseAverage

/-! Coefficient extraction by phase averaging after division by a monomial. -/

noncomputable section
open MeasureTheory Polynomial
namespace MathieuProperty

theorem polynomial_phase_expansion (H : Polynomial ℂ) (r : ℂ) (hr : r ≠ 0)
    (m : ℕ) (θ : ℝ) :
    (r * Complex.exp (Complex.I * θ)) ^ (-(m : ℤ)) *
        H.eval (r * Complex.exp (Complex.I * θ)) =
      ∑ n ∈ H.support, H.coeff n *
        (r * Complex.exp (Complex.I * θ)) ^ ((n : ℤ) - m) := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hz : r * Complex.exp (Complex.I * θ) ≠ 0 := mul_ne_zero hr (Complex.exp_ne_zero _)
  rw [zpow_sub₀ hz, zpow_natCast, zpow_natCast, zpow_neg, zpow_natCast]
  ring

theorem polynomial_phase_coefficient (H : Polynomial ℂ) (r : ℂ) (hr : r ≠ 0) (m : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (r * Complex.exp (Complex.I * θ)) ^ (-(m : ℤ)) *
        H.eval (r * Complex.exp (Complex.I * θ))) = (2 * Real.pi : ℂ) * H.coeff m := by
  simp_rw [polynomial_phase_expansion H r hr]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_phase_monomial,
      sub_eq_zero, Int.natCast_inj, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    by_cases hm : m ∈ H.support
    · simp [hm, mul_comm]
    · simp [hm, notMem_support_iff.mp hm]
  · intro n hn
    exact (continuous_const.mul (continuous_phase_monomial r ((n : ℤ) - m))).intervalIntegrable _ _

end MathieuProperty
