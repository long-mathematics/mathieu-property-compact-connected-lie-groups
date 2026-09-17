import MathieuProperty.HopfCoefficient
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The real integral defining c_m and its exact factorial value. -/

noncomputable section

open Polynomial MeasureTheory

namespace MathieuProperty

def momentConstant (m : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ m

theorem hopfPrimitive_eval_one (m : ℕ) :
    (hopfPrimitive (K := ℝ) m).eval 1 = momentConstant m := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun t => (hopfPrimitive (K := ℝ) m).eval t)
    (f' := fun t => (1 - t ^ 2) ^ m)
    (fun t _ => by simpa [derivative_hopfPrimitive] using
      (hopfPrimitive (K := ℝ) m).hasDerivAt t)
    ((by fun_prop : Continuous (fun t : ℝ => (1 - t ^ 2) ^ m)).intervalIntegrable 0 1)
  simpa [hopfPrimitive, momentConstant] using h.symm

@[simp] theorem momentConstant_zero : momentConstant 0 = 1 := by
  simp [momentConstant]

/-- Integration of the derivative of t(1-t²)^(m+1). -/
theorem momentConstant_recurrence (m : ℕ) :
    (2 * m + 3 : ℝ) * momentConstant (m + 1) =
      (2 * m + 2 : ℝ) * momentConstant m := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => t * (1 - t ^ 2) ^ (m + 1))
      ((2 * m + 3 : ℝ) * (1 - x ^ 2) ^ (m + 1) -
        (2 * m + 2 : ℝ) * (1 - x ^ 2) ^ m) x := by
    convert (hasDerivAt_id x).mul
      (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).pow (m + 1)) using 1
    · rfl
    · dsimp
      push_cast
      simp only [pow_succ]
      ring
  have hi (n : ℕ) : IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ n) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => (1 - t ^ 2) ^ n)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun x _ => hd x)
    (((hi (m + 1)).const_mul _).sub ((hi m).const_mul _))
  rw [intervalIntegral.integral_sub ((hi (m + 1)).const_mul _) ((hi m).const_mul _)] at h
  simp only [intervalIntegral.integral_const_mul] at h
  simpa [momentConstant, sub_eq_zero] using h

theorem momentConstant_pos (m : ℕ) : 0 < momentConstant m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := momentConstant_recurrence m
    have hc : (0 : ℝ) < 2 * m + 2 := by positivity
    have hd : (0 : ℝ) < 2 * m + 3 := by positivity
    exact (mul_pos_iff_of_pos_left hd).mp (h.symm ▸ mul_pos hc ih)

/-- The factorial form in equation (3.5). -/
theorem momentConstant_factorial (m : ℕ) :
    momentConstant m = 4 ^ m * (m.factorial : ℝ) ^ 2 / ((2 * m + 1).factorial : ℝ) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have h := momentConstant_recurrence m
    rw [ih] at h
    have hd : (2 * m + 3 : ℝ) ≠ 0 := by positivity
    have hf : ((2 * m + 1).factorial : ℝ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hd)
    rw [h]
    have he : 2 * (m + 1) + 1 = (2 * m + 1 + 1) + 1 := by omega
    simp only [he, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, pow_succ]
    field_simp
    ring

theorem pascal_marker_pos (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    0 < momentConstant m * ((m - 1).choose (s - 1) : ℝ) :=
  mul_pos (momentConstant_pos m) (by exact_mod_cast Nat.choose_pos (by omega : s - 1 ≤ m - 1))

theorem pascal_marker_zero (m s : ℕ) (hm : 1 ≤ m) (hsm : m < s) :
    momentConstant m * ((m - 1).choose (s - 1) : ℝ) = 0 := by
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]

end MathieuProperty
