import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-! Moments of the actual beta probability measure.

Multiplying its density by a natural power shifts the first shape parameter.
Normalization gives the beta-function ratio; Gamma recurrence yields the rising
product, and for integer parameters the ascending-factorial ratio. Integrability
is proved for every moment. Identifying these laws with classical-group radial
pushforwards is a separate obligation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace MathieuProperty

theorem betaPDFReal_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 hα hβ).le
  · simp [betaPDFReal, hx]

theorem betaPDF_toReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    (betaPDF α β x).toReal = betaPDFReal α β x :=
  ENNReal.toReal_ofReal (betaPDFReal_nonneg hα hβ x)

theorem integral_betaPDFReal {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, betaPDFReal α β x = 1 := by
  let := isProbabilityMeasureBeta hα hβ
  have h : (∫ x : ℝ, (1 : ℝ) ∂betaMeasure α β) = 1 := by simp
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul] at h
  · simpa only [smul_eq_mul, mul_one, betaPDF_toReal hα hβ] using h
  · exact ENNReal.measurable_ofReal.comp (measurable_betaPDFReal α β)
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

theorem betaPDFReal_mul_pow {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) (x : ℝ) :
    betaPDFReal α β x * x ^ k =
      (beta (α + k) β / beta α β) * betaPDFReal (α + k) β x := by
  have hak : 0 < α + k := by positivity
  by_cases hx : 0 < x ∧ x < 1
  · have hp : x ^ (α - 1) * x ^ k = x ^ (α + (k : ℝ) - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx.1]
      congr 1
      ring
    simp only [betaPDFReal, ite_eq_left hx]
    field_simp [ne_of_gt (beta_pos hα hβ), ne_of_gt (beta_pos hak hβ)]
    rw [← hp]
    ring
  · simp [betaPDFReal, hx]

theorem beta_moment_ratio {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    ∫ x : ℝ, x ^ k ∂betaMeasure α β = beta (α + k) β / beta α β := by
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp only [smul_eq_mul, betaPDF_toReal hα hβ, betaPDFReal_mul_pow hα hβ]
    rw [integral_const_mul, integral_betaPDFReal (by positivity) hβ, mul_one]
  · exact ENNReal.measurable_ofReal.comp (measurable_betaPDFReal α β)
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

theorem beta_moment_integrable {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (betaMeasure α β) := by
  apply Integrable.of_integral_ne_zero
  rw [beta_moment_ratio hα hβ]
  exact ne_of_gt (div_pos (beta_pos (by positivity) hβ) (beta_pos hα hβ))

theorem gamma_add_nat_product {α : ℝ} (hα : 0 < α) (k : ℕ) :
    Real.Gamma (α + k) = (∏ i ∈ Finset.range k, (α + i)) * Real.Gamma α := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity), hk, Finset.prod_range_succ]
    ring

theorem beta_moment_product {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    ∫ x : ℝ, x ^ k ∂betaMeasure α β =
      (∏ i ∈ Finset.range k, (α + i)) / (∏ i ∈ Finset.range k, (α + β + i)) := by
  rw [beta_moment_ratio hα hβ]
  unfold beta
  have harg : α + (k : ℝ) + β = (α + β) + k := by ring
  rw [harg, gamma_add_nat_product hα, gamma_add_nat_product (add_pos hα hβ)]
  have hprod : (∏ i ∈ Finset.range k, (α + β + i)) ≠ 0 := by
    apply ne_of_gt
    exact Finset.prod_pos (fun i _ => by positivity)
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα), ne_of_gt (Real.Gamma_pos_of_pos hβ),
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ)), hprod]

theorem beta_moment_nat (a b k : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x : ℝ, x ^ k ∂betaMeasure a b =
      (a.ascFactorial k : ℝ) / ((a + b).ascFactorial k : ℝ) := by
  rw [beta_moment_product (by exact_mod_cast ha) (by exact_mod_cast hb)]
  simp [Nat.ascFactorial_eq_prod_range]

theorem beta_two_moment (n k : ℕ) (hn : 3 ≤ n) :
    ∫ x : ℝ, x ^ k ∂betaMeasure 2 (n - 2 : ℕ) =
      ((2 : ℕ).ascFactorial k : ℝ) / (n.ascFactorial k : ℝ) := by
  have hh : 2 + (n - 2) = n := by omega
  simpa only [hh, Nat.cast_ofNat] using beta_moment_nat 2 (n - 2) k (by omega) (by omega)

end MathieuProperty
