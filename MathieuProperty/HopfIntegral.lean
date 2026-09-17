import MathieuProperty.SpherePhaseAverage
import MathieuProperty.SphereMarginal

/-! The manuscript's full Hopf coefficient identity for normalized Euclidean surface measure. -/

noncomputable section
open MeasureTheory Polynomial
namespace MathieuProperty.Hopf

/-- The extracted coefficient is an even polynomial in the real height. -/
def hopfHeightPolynomial (H : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (m + 1),
    C ((-1 : ℂ) ^ k * (m.choose k : ℂ) *
      (H * (1 + X) ^ m * (1 + X) ^ (2 * k)).coeff m) * X ^ (2 * k)

theorem hopfHeightPolynomial_eval (H : Polynomial ℂ) (m : ℕ) (t : ℝ) :
    (hopfHeightPolynomial H m).eval (t : ℂ) = (hopfKernel H m t).coeff m := by
  simpa only [hopfHeightPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    hopfKernel, map_pow, mul_pow] using (hopf_integrand_coeff_expansion m m H t).symm

theorem hopfHeightPolynomial_even (H : Polynomial ℂ) (m : ℕ) (t : ℝ) :
    (hopfHeightPolynomial H m).eval ((-t : ℝ) : ℂ) = (hopfHeightPolynomial H m).eval (t : ℂ) := by
  rw [hopfHeightPolynomial_eval H m (-t), hopfHeightPolynomial_eval]
  simp [hopfKernel]

theorem sphere_hopf_real_integral (H : Polynomial ℂ) (m : ℕ) :
    (∫ z, H.eval (q z) * p z ^ m ∂surfaceMeasure) =
      ∫ t in (0 : ℝ)..1, (hopfKernel H m t).coeff m := by
  rw [sphere_hopf_constantTerm]
  simp_rw [← hopfHeightPolynomial_eval]
  rw [tau_polynomial_integral]
  have hc : Continuous (fun t : ℝ => (hopfHeightPolynomial H m).eval (t : ℂ)) :=
    (hopfHeightPolynomial H m).continuous.comp Complex.continuous_ofReal
  have hneg := intervalIntegral.integral_comp_neg
    (fun t : ℝ => (hopfHeightPolynomial H m).eval (t : ℂ)) (a := 0) (b := 1)
  simp only [hopfHeightPolynomial_even, neg_zero] at hneg
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1), ← hneg]
  ring

/-- Theorem 3.1: the exact coefficient formula, for every complex polynomial H
and every positive integer m, on the actual normalized Euclidean sphere measure. -/
theorem hopf_coefficient (H : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, H.eval (q z) * p z ^ m ∂surfaceMeasure) =
      (momentConstant m : ℂ) * (H * (1 + X) ^ (m - 1)).coeff m := by
  rw [sphere_hopf_real_integral]
  exact hopf_integrated_coefficient m hm H

theorem sphere_pure (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, p z ^ m ∂surfaceMeasure) = 0 := by
  have h := hopf_coefficient 1 m hm
  simpa [pure_pascal_coefficient m hm] using h

theorem sphere_marked (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (∫ z, q z ^ s * p z ^ m ∂surfaceMeasure) =
      (momentConstant m : ℂ) * ((m - 1).choose (s - 1) : ℂ) := by
  have h := hopf_coefficient (X ^ s) m hm
  simpa [pascal_coefficient m s hm hs] using h

theorem sphere_marked_zero (m s : ℕ) (hm : 1 ≤ m) (hsm : m < s) :
    (∫ z, q z ^ s * p z ^ m ∂surfaceMeasure) = 0 := by
  rw [sphere_marked m s hm (by omega), Nat.choose_eq_zero_of_lt (by omega),
    Nat.cast_zero, mul_zero]

/-- Positivity of a complex moment means that it is a strictly positive real number. -/
theorem sphere_marked_positive (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∃ c : ℝ, 0 < c ∧ (∫ z, q z ^ s * p z ^ m ∂surfaceMeasure) = (c : ℂ) := by
  refine ⟨momentConstant m * ((m - 1).choose (s - 1) : ℝ),
    pascal_marker_pos m s hm hs hsm, ?_⟩
  rw [sphere_marked m s hm hs]
  push_cast
  rfl

/-- Corollary 3.2, with all markers in a single fixed tower. -/
theorem sphere_marker_tower :
    (∀ m : ℕ, 1 ≤ m → (∫ z, p z ^ m ∂surfaceMeasure) = 0) ∧
    (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
      (∫ z, q z ^ s * p z ^ m ∂surfaceMeasure) =
        (momentConstant m : ℂ) * ((m - 1).choose (s - 1) : ℂ)) ∧
    (∀ m s : ℕ, 1 ≤ m → m < s → (∫ z, q z ^ s * p z ^ m ∂surfaceMeasure) = 0) ∧
    (∀ m s : ℕ, 1 ≤ m → 1 ≤ s → s ≤ m →
      ∃ c : ℝ, 0 < c ∧ (∫ z, q z ^ s * p z ^ m ∂surfaceMeasure) = (c : ℂ)) :=
  ⟨sphere_pure, sphere_marked, sphere_marked_zero, sphere_marked_positive⟩

end MathieuProperty.Hopf
