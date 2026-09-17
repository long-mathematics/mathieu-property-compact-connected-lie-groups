import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-! The polynomial kernel of the Hopf coefficient identity.
This module proves the divisibility and coefficient assertions independently of
the remaining sphere-measure correspondence.
-/

noncomputable section

open Polynomial

namespace MathieuProperty

variable {K : Type*} [Field K] [CharZero K]

/-- The unique zero-constant polynomial primitive. -/
def primitive (p : K[X]) : K[X] :=
  ∑ n ∈ p.support, monomial (n + 1) (p.coeff n / (n + 1))

theorem derivative_primitive (p : K[X]) : (primitive p).derivative = p := by
  unfold primitive
  rw [derivative_sum]
  conv_rhs => rw [← p.sum_monomial_eq]
  simp only [Polynomial.sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [derivative_monomial]
  simp [Nat.cast_add, Nat.cast_one, Nat.cast_add_one_ne_zero]

omit [CharZero K] in
@[simp] theorem primitive_eval_zero (p : K[X]) : (primitive p).eval 0 = 0 := by
  simp [primitive, eval_finsetSum]

/-- J_m as an actual polynomial, not an assumed antiderivative. -/
def hopfPrimitive (m : ℕ) : K[X] := primitive ((1 - X ^ 2) ^ m)

theorem derivative_hopfPrimitive (m : ℕ) :
    (hopfPrimitive (K := K) m).derivative = (1 - X ^ 2) ^ m :=
  derivative_primitive _

/-- If the derivative starts at degree m, the polynomial minus its constant
starts at degree m+1. Characteristic zero is essential here. -/
theorem pow_X_dvd_sub_constant_of_derivative (F : K[X]) (m : ℕ)
    (hF : X ^ m ∣ F.derivative) : X ^ (m + 1) ∣ F - C (F.eval 0) := by
  rw [X_pow_dvd_iff] at hF ⊢
  intro n hn
  cases n with
  | zero => simp [coeff_zero_eq_eval_zero]
  | succ n =>
    have h := hF n (by omega)
    rw [coeff_derivative] at h
    have hcoeff : F.coeff (n + 1) = 0 :=
      (mul_eq_zero.mp h).resolve_right (Nat.cast_add_one_ne_zero n)
    simpa using hcoeff

/-- Equation (3.11): the order m+1 zero after translating the primitive. -/
theorem primitive_congruence (m : ℕ) :
    X ^ (m + 1) ∣
      (hopfPrimitive (K := K) m).comp (1 + X) - C ((hopfPrimitive (K := K) m).eval 1) := by
  have hderiv : X ^ m ∣ ((hopfPrimitive (K := K) m).comp (1 + X)).derivative := by
    rw [derivative_comp, derivative_hopfPrimitive]
    simp only [derivative_add, derivative_one, derivative_X, zero_add, one_mul,
      pow_comp, sub_comp, one_comp, pow_comp, X_comp]
    have hfactor : (1 - (1 + X) ^ 2 : K[X]) = X * (-(2 + X)) := by ring
    rw [hfactor, mul_pow]
    exact dvd_mul_right _ _
  simpa using pow_X_dvd_sub_constant_of_derivative
    ((hopfPrimitive (K := K) m).comp (1 + X)) m hderiv

omit [CharZero K] in
/-- Multiplying a congruence modulo X^(m+1) preserves coefficient m. -/
theorem coefficient_congruence (F H : K[X]) (c : K) (m : ℕ)
    (hF : X ^ (m + 1) ∣ F - C c) : (H * F).coeff m = c * H.coeff m := by
  obtain ⟨D, hD⟩ := hF
  have hF' : F = C c + X ^ (m + 1) * D := by rw [← hD]; ring
  rw [hF', mul_add, coeff_add, coeff_mul_C]
  have hzero : (H * (X ^ (m + 1) * D)).coeff m = 0 := by
    rw [show H * (X ^ (m + 1) * D) = X ^ (m + 1) * (H * D) by ring,
      coeff_X_pow_mul']
    simp
  rw [hzero, add_zero, mul_comm]

/-- The exact J-step coefficient simplification for every polynomial H. -/
theorem hopf_primitive_coefficient (m : ℕ) (H : K[X]) :
    (H * (1 + X) ^ (m - 1) * (hopfPrimitive (K := K) m).comp (1 + X)).coeff m =
      (hopfPrimitive (K := K) m).eval 1 * (H * (1 + X) ^ (m - 1)).coeff m :=
  coefficient_congruence _ _ _ _ (primitive_congruence m)

omit [CharZero K] in
/-- All marked Pascal coefficients, including s>m with value zero. -/
theorem pascal_coefficient (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (X ^ s * (1 + X) ^ (m - 1) : K[X]).coeff m = ((m - 1).choose (s - 1) : K) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_one_add_X_pow]
    congr 1
    have hsub : m - s = (m - 1) - (s - 1) := by omega
    rw [hsub, Nat.choose_symm (by omega)]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

omit [CharZero K] in
theorem pure_pascal_coefficient (m : ℕ) (hm : 1 ≤ m) :
    ((1 + X) ^ (m - 1) : K[X]).coeff m = 0 := by
  rw [coeff_one_add_X_pow, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

end MathieuProperty
