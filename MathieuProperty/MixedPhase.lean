import MathieuProperty.AbelianConjectures
import Mathlib.MeasureTheory.Integral.Pi

/-! Product circle integration agrees with the multivariate constant-term functional
used in the universal abelian conjectures. -/

noncomputable section
open MeasureTheory
namespace MathieuProperty.Abelian

def phaseMonomial {M : ℕ} (a : Fin M → ℤ) (θ : Fin M → ℝ) : ℂ :=
  ∏ i, Complex.exp ((a i : ℂ) * Complex.I * θ i)

theorem phaseMonomial_eq {M : ℕ} (a : Fin M → ℤ) (θ : Fin M → ℝ) :
    phaseMonomial a θ = ∏ i, Complex.exp (Complex.I * θ i) ^ (a i) := by
  simp only [phaseMonomial, ← Complex.exp_int_mul, mul_assoc]

theorem continuous_phaseMonomial {M : ℕ} (a : Fin M → ℤ) : Continuous (phaseMonomial a) := by
  unfold phaseMonomial
  fun_prop

theorem phaseMonomial_integral {M : ℕ} (a : Fin M → ℤ) :
    (∫ θ in Set.Icc (0 : Fin M → ℝ) (fun _ => 2 * Real.pi), phaseMonomial a θ) =
      if a = 0 then (2 * Real.pi : ℂ) ^ M else 0 := by
  rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  unfold phaseMonomial
  rw [integral_fintype_prod_eq_prod (fun (i : Fin M) (θ : ℝ) =>
    Complex.exp ((a i : ℂ) * Complex.I * θ))]
  have hi (n : ℤ) : (∫ θ in Set.Icc (0 : ℝ) (2*Real.pi),
      Complex.exp ((n : ℂ)*Complex.I*θ)) = if n = 0 then (2*Real.pi : ℂ) else 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
    exact integral_integer_frequency n
  simp_rw [Pi.zero_apply, hi]
  by_cases ha : a = 0
  · simp [ha]
  · rw [ite_eq_right ha]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

def mixedPhase {N M : ℕ} (f : MixedLaurent N M) (x : Fin N → ℝ) (θ : Fin M → ℝ) : ℂ :=
  ∑ a ∈ f.coeff.support, MvPolynomial.eval (fun i => (x i : ℂ)) (f.coeff a) * phaseMonomial a θ

theorem mixedPhase_integral {N M : ℕ} (f : MixedLaurent N M) (x : Fin N → ℝ) :
    (∫ θ in Set.Icc (0 : Fin M → ℝ) (fun _ => 2 * Real.pi), mixedPhase f x θ) =
      (2*Real.pi : ℂ)^M * MvPolynomial.eval (fun i => (x i : ℂ)) (f.coeff 0) := by
  unfold mixedPhase
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, phaseMonomial_integral]
    rw [Finset.sum_eq_single 0]
    · simp [mul_comm]
    · intro a ha ha0
      simp [ha0]
    · intro h0
      have hz : f.coeff 0 = 0 := Finsupp.notMem_support_iff.mp h0
      simp [hz]
  · intro a ha
    exact (continuous_const.mul (continuous_phaseMonomial a)).integrableOn_Icc

/-- Circle averages use one factor 1/(2π) for each Laurent variable, including
M=0. Thus the conjectures use the actual unit-cube/product-circle integral. -/
theorem mixedIntegral_eq_circle_integral {N M : ℕ} (δ : MvPolynomial (Fin N) ℂ)
    (f : MixedLaurent N M) :
    mixedIntegral δ f = ∫ x in Set.Icc (0 : Fin N → ℝ) 1,
      ((2*Real.pi : ℂ)^M)⁻¹ *
        (∫ θ in Set.Icc (0 : Fin M → ℝ) (fun _ => 2*Real.pi), mixedPhase f x θ) *
        MvPolynomial.eval (fun i => (x i : ℂ)) δ := by
  unfold mixedIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  rw [mixedPhase_integral, MvPolynomial.eval_mul, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero M (by exact_mod_cast (show (2 : ℝ)*Real.pi ≠ 0 by positivity))),
    one_mul]

end MathieuProperty.Abelian
