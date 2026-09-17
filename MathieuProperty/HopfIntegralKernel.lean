import MathieuProperty.MomentConstant
import Mathlib.Analysis.Complex.RealDeriv

/-! The analytic substitution and coefficient integration in the Hopf calculation.
The identification with normalized sphere integration is a separate obligation. -/

noncomputable section
open Polynomial MeasureTheory
namespace MathieuProperty

theorem hopfPrimitive_eval_integral (m : ℕ) (y : ℝ) :
    (hopfPrimitive (K := ℝ) m).eval y = ∫ t in (0 : ℝ)..y, (1 - t ^ 2) ^ m := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := y)
    (f := fun t => (hopfPrimitive (K := ℝ) m).eval t)
    (f' := fun t => (1 - t ^ 2) ^ m)
    (fun t _ => by simpa [derivative_hopfPrimitive] using
      (hopfPrimitive (K := ℝ) m).hasDerivAt t)
    ((by fun_prop : Continuous (fun t : ℝ => (1 - t ^ 2) ^ m)).intervalIntegrable 0 y)
  simpa [hopfPrimitive] using h.symm

theorem hopfPrimitive_complex_substitution (m : ℕ) (c : ℂ) :
    c * (∫ t in (0 : ℝ)..1, (1 - (c * (t : ℂ)) ^ 2) ^ m) =
      (hopfPrimitive (K := ℂ) m).eval c := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => (hopfPrimitive (K := ℂ) m).eval (c * s))
      (c * (1 - (c * t) ^ 2) ^ m) t := by
    have h := ((hopfPrimitive (K := ℂ) m).hasDerivAt (c * (t : ℂ))).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).const_mul c)
    simpa [derivative_hopfPrimitive, mul_comm] using h.comp_ofReal
  have hi : IntervalIntegrable (fun t : ℝ => c * (1 - (c * (t : ℂ)) ^ 2) ^ m) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => c * (1 - (c * (t : ℂ)) ^ 2) ^ m)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun t _ => hd t) hi
  simpa [intervalIntegral.integral_const_mul, hopfPrimitive] using h

theorem hopfPrimitive_complex_eval_one (m : ℕ) :
    (hopfPrimitive (K := ℂ) m).eval 1 = (momentConstant m : ℂ) := by
  rw [← hopfPrimitive_complex_substitution m 1]
  simp only [one_mul]
  unfold momentConstant
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  push_cast
  rfl

theorem one_sub_sq_pow_expansion {R : Type*} [CommRing R] (m : ℕ) (x : R) :
    (1 - x ^ 2) ^ m =
      ∑ k ∈ Finset.range (m + 1), (-1) ^ k * x ^ (2 * k) * (m.choose k : R) := by
  rw [show (1 - x ^ 2) = -x ^ 2 + 1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [neg_pow]
  simp only [one_pow, mul_one, ← pow_mul]

/-- The polynomial obtained by integrating `(1-c²t²)^m` over `0 ≤ t ≤ 1`. -/
def quadraticIntegral (m : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    C ((-1 : ℂ) ^ k * (m.choose k : ℂ) / (2 * k + 1)) * X ^ (2 * k)

theorem integral_complex_pow (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (t : ℂ) ^ n) = 1 / (n + 1 : ℂ) := by
  have h := intervalIntegral.integral_ofReal (f := fun t : ℝ => t ^ n) (a := 0) (b := 1)
    (μ := volume)
  simpa using h

theorem quadraticIntegral_eval (m : ℕ) (c : ℂ) :
    (quadraticIntegral m).eval c = ∫ t in (0 : ℝ)..1, (1 - (c * (t : ℂ)) ^ 2) ^ m := by
  simp_rw [one_sub_sq_pow_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [quadraticIntegral, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [mul_pow]
    rw [intervalIntegral.integral_mul_const]
    rw [show (fun t : ℝ => (-1 : ℂ) ^ k * (c ^ (2 * k) * (t : ℂ) ^ (2 * k))) =
      (fun t : ℝ => ((-1 : ℂ) ^ k * c ^ (2 * k)) * (t : ℂ) ^ (2 * k)) by
        funext t; ring]
    rw [intervalIntegral.integral_const_mul, integral_complex_pow]
    push_cast
    ring
  · intro k hk
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (-1 : ℂ) ^ k * (c * (t : ℂ)) ^ (2 * k) * (m.choose k : ℂ))).intervalIntegrable 0 1

theorem X_mul_quadraticIntegral (m : ℕ) :
    X * quadraticIntegral m = hopfPrimitive (K := ℂ) m := by
  apply Polynomial.funext
  intro c
  simp only [eval_mul, eval_X, quadraticIntegral_eval]
  exact hopfPrimitive_complex_substitution m c

theorem hopf_integrand_coeff_expansion (m n : ℕ) (H : ℂ[X]) (t : ℝ) :
    (H * (1 + X) ^ m * (1 - (C (t : ℂ) * (1 + X)) ^ 2) ^ m).coeff n =
      ∑ k ∈ Finset.range (m + 1),
        ((-1 : ℂ) ^ k * (m.choose k : ℂ) *
          (H * (1 + X) ^ m * (1 + X) ^ (2 * k)).coeff n) * (t : ℂ) ^ (2 * k) := by
  rw [one_sub_sq_pow_expansion, Finset.mul_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  have hp : H * (1 + X) ^ m *
      ((-1 : ℂ[X]) ^ k * (C (t : ℂ) * (1 + X)) ^ (2 * k) * (m.choose k : ℂ[X])) =
      C ((-1 : ℂ) ^ k * (m.choose k : ℂ) * (t : ℂ) ^ (2 * k)) *
        (H * (1 + X) ^ m * (1 + X) ^ (2 * k)) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, mul_pow]
    ring
  rw [hp, coeff_C_mul]
  ring

/-- Finite coefficient extraction commutes with the real integral in the CT step.
The proof explicitly expands a finite binomial sum and verifies its integrability. -/
theorem integral_hopf_integrand_coeff (m n : ℕ) (H : ℂ[X]) :
    (∫ t in (0 : ℝ)..1,
      (H * (1 + X) ^ m * (1 - (C (t : ℂ) * (1 + X)) ^ 2) ^ m).coeff n) =
      (H * (1 + X) ^ m * (quadraticIntegral m).comp (1 + X)).coeff n := by
  simp_rw [hopf_integrand_coeff_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [quadraticIntegral, sum_comp, mul_comp, C_comp, pow_comp, X_comp,
      Finset.mul_sum, finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_complex_pow]
    rw [show H * (1 + X) ^ m *
        (C ((-1 : ℂ) ^ k * (m.choose k : ℂ) / (2 * k + 1)) * (1 + X) ^ (2 * k)) =
      C ((-1 : ℂ) ^ k * (m.choose k : ℂ) / (2 * k + 1)) *
        (H * (1 + X) ^ m * (1 + X) ^ (2 * k)) by ring,
      coeff_C_mul]
    push_cast
    ring
  · intro k hk
    exact (continuous_const.mul (Complex.continuous_ofReal.pow (2 * k))).intervalIntegrable 0 1

/-- The fully integrated coefficient kernel of the Hopf theorem, for all complex H
and every positive m. Its identification with the sphere integral is still separate. -/
theorem hopf_integrated_coefficient (m : ℕ) (hm : 1 ≤ m) (H : ℂ[X]) :
    (∫ t in (0 : ℝ)..1,
      (H * (1 + X) ^ m * (1 - C ((t : ℂ) ^ 2) * (1 + X) ^ 2) ^ m).coeff m) =
      (momentConstant m : ℂ) * (H * (1 + X) ^ (m - 1)).coeff m := by
  simp only [map_pow, ← mul_pow]
  rw [integral_hopf_integrand_coeff]
  have hj : (1 + X) * (quadraticIntegral m).comp (1 + X) =
      (hopfPrimitive (K := ℂ) m).comp (1 + X) := by
    rw [← X_mul_quadraticIntegral, mul_comp, X_comp]
  have hp : H * (1 + X) ^ m * (quadraticIntegral m).comp (1 + X) =
      H * (1 + X) ^ (m - 1) * (hopfPrimitive (K := ℂ) m).comp (1 + X) := by
    have hpow : (1 + X : ℂ[X]) ^ m = (1 + X) ^ (m - 1) * (1 + X) := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [hpow, ← hj]
    ring
  rw [hp, hopf_primitive_coefficient, hopfPrimitive_complex_eval_one]

end MathieuProperty
