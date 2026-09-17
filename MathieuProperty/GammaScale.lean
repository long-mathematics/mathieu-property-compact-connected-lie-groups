import MathieuProperty.GammaBeta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Positive scaling of shape-one gamma laws to unit rate. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace MathieuProperty

theorem positive_scale_lintegral {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y, f y = ∫⁻ x, ENNReal.ofReal r * f (r * x) := by
  have himg : (fun x : ℝ => r * x) '' univ = univ := by
    ext y
    constructor
    · simp
    · intro _
      exact ⟨y / r, mem_univ _, mul_div_cancel₀ y hr.ne'⟩
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => r * x) r x := by
    simpa using (hasDerivAt_id x).const_mul r
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (hd x).hasDerivWithinAt)
    (fun x _ y _ hxy => mul_left_cancel₀ hr.ne' hxy) f
  simpa only [himg, setLIntegral_univ, abs_of_pos hr] using hh

theorem gamma_one_density_scale {r : ℝ} (hr : 0 < r) (x : ℝ) :
    gammaPDFReal 1 r x = r * gammaPDFReal 1 1 (r * x) := by
  have hs : 0 ≤ r * x ↔ 0 ≤ x := mul_nonneg_iff_of_pos_left hr
  simp only [gammaPDFReal, Real.rpow_one, Real.Gamma_one, div_one, sub_self,
    Real.rpow_zero, mul_one, one_mul, hs]
  split_ifs <;> ring

theorem gamma_one_pdf_scale {r : ℝ} (hr : 0 < r) (x : ℝ) :
    gammaPDF 1 r x = ENNReal.ofReal r * gammaPDF 1 1 (r * x) := by
  rw [gammaPDF, gamma_one_density_scale hr, ENNReal.ofReal_mul hr.le]
  rfl

theorem gamma_one_scale_rate {r : ℝ} (hr : 0 < r) :
    (gammaMeasure 1 r).map (fun x => r * x) = gammaMeasure 1 1 := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hfm : Measurable (fun x : ℝ => f (r * x)) := hf.comp (by fun_prop)
  have hd₁ : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal _ _).ennreal_ofReal
  have hd₂ : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal _ _).ennreal_ofReal
  rw [lintegral_map hf (by fun_prop), gammaMeasure, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hd₁ hfm,
    lintegral_withDensity_eq_lintegral_mul _ hd₂ hf]
  simp only [Pi.mul_apply]
  conv_rhs => rw [positive_scale_lintegral hr]
  apply lintegral_congr
  intro x
  rw [gamma_one_pdf_scale hr]
  exact mul_assoc _ _ _

end MathieuProperty
