import MathieuProperty.SphereMomentRecurrence
import MathieuProperty.HopfIntegralKernel

/-! Polynomial integration against the first-coordinate and Hopf-height marginals. -/

noncomputable section
open MeasureTheory Polynomial
namespace MathieuProperty.Hopf

theorem sphereMonomial_diagonal (p q : ℕ) (z : Sphere) :
    sphereMonomial p p q q z =
      (Complex.normSq z.val.1 : ℂ) ^ p * (Complex.normSq z.val.2 : ℂ) ^ q := by
  simp only [sphereMonomial, coordinateMonomial, Complex.normSq_eq_conj_mul_self, mul_pow,
    Complex.star_def]
  ring

theorem firstCoordinate_moment (n : ℕ) :
    (∫ z : Sphere, (Complex.normSq z.val.1 : ℂ) ^ n ∂surfaceMeasure) = 1 / (n + 1 : ℂ) := by
  have heq : (fun z : Sphere => (Complex.normSq z.val.1 : ℂ) ^ n) =
      sphereMonomial n n 0 0 := by funext z; simp [sphereMonomial_diagonal]
  rw [heq, ← mixedMoment, mixedMoment_factorial]
  simp only [Nat.add_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

@[fun_prop] theorem continuous_first_normSq :
    Continuous (fun z : Sphere => (Complex.normSq z.val.1 : ℂ)) := by fun_prop

theorem firstCoordinate_polynomial_integral (H : Polynomial ℂ) :
    (∫ z : Sphere, H.eval (Complex.normSq z.val.1 : ℂ) ∂surfaceMeasure) =
      ∫ t in (0 : ℝ)..1, H.eval (t : ℂ) := by
  have hi (f : Polynomial ℂ) :
      Integrable (fun z : Sphere => f.eval (Complex.normSq z.val.1 : ℂ)) surfaceMeasure :=
    (f.continuous.comp continuous_first_normSq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj (f : Polynomial ℂ) : IntervalIntegrable (fun t : ℝ => f.eval (t : ℂ)) volume 0 1 :=
    (f.continuous.comp Complex.continuous_ofReal).intervalIntegrable 0 1
  induction H using Polynomial.induction_on' with
  | add H K ih ik =>
    simp only [eval_add]
    rw [integral_add (hi H) (hi K), intervalIntegral.integral_add (hj H) (hj K), ih, ik]
  | monomial n c =>
    simp only [eval_monomial]
    rw [integral_const_mul, intervalIntegral.integral_const_mul, firstCoordinate_moment,
      integral_complex_pow]

theorem tau_eq_first_normSq (z : Sphere) : tau z.val = 2 * Complex.normSq z.val.1 - 1 := by
  have hz := z.property
  dsimp [a] at hz
  dsimp [tau]
  linarith

/-- The Hopf height has the uniform marginal on [-1,1], for every complex polynomial. -/
theorem tau_polynomial_integral (H : Polynomial ℂ) :
    (∫ z : Sphere, H.eval (tau z.val : ℂ) ∂surfaceMeasure) =
      (1 / 2 : ℂ) * ∫ t in (-1 : ℝ)..1, H.eval (t : ℂ) := by
  have h := firstCoordinate_polynomial_integral (H.comp (C 2 * X - 1))
  simp only [eval_comp, eval_sub, eval_mul, eval_C, eval_X, eval_one] at h
  have hpoint (z : Sphere) : (tau z.val : ℂ) = 2 * (Complex.normSq z.val.1 : ℂ) - 1 := by
    rw [tau_eq_first_normSq]
    push_cast
    rfl
  simp_rw [hpoint]
  rw [h]
  have hc := intervalIntegral.integral_comp_mul_add (fun t : ℝ => H.eval (t : ℂ))
    (a := 0) (b := 1) (c := 2) (by norm_num) (-1)
  simpa [Complex.real_smul, sub_eq_add_neg, show (2 : ℝ) + -1 = 1 by norm_num] using hc

end MathieuProperty.Hopf
