import MathieuProperty.GammaBeta
import MathieuProperty.GaussianSphere
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Squared standard real Gaussians have Gamma(1/2,1/2) law.

The proof uses symmetry, the change of variables y=x² on the positive
half-line, and the exact Gamma(1/2)=sqrt(pi) normalization. Combining two
independent squares yields Gamma(1,1/2), the squared modulus of one complex
Gaussian coordinate in our common real/imaginary variance-one convention.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace MathieuProperty

theorem gaussian_square_density (x : ℝ) (hx : 0 < x) :
    (2 * x) * gammaPDFReal (1 / 2) (1 / 2) (x ^ 2) = 2 * gaussianPDFReal 0 1 x := by
  have hp : (x ^ 2) ^ ((1 : ℝ) / 2 - 1) = x⁻¹ := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  simp only [gammaPDFReal, ite_eq_left (sq_nonneg x), Real.Gamma_one_half_eq, hp,
    gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_div zero_le_one, Real.sqrt_one,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  have hs₂ := Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  have hsπ := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have he : -(1 / 2 * x ^ 2) = -x ^ 2 / 2 := by ring
  rw [he]
  field_simp

theorem lintegral_even_real (f : ℝ → ℝ≥0∞) (hf : ∀ x, f (-x) = f x) :
    ∫⁻ x, f x = 2 * ∫⁻ x in Ioi (0 : ℝ), f x := by
  have hn : (∫⁻ x in Iio (0 : ℝ), f x) = ∫⁻ x in Ioi (0 : ℝ), f x := by
    calc
      _ = ∫⁻ x : ℝ, (Ioi (0 : ℝ)).indicator f (-x) := by
        rw [← lintegral_indicator measurableSet_Iio]
        apply lintegral_congr
        intro x
        simp [Set.indicator, hf]
      _ = _ := by rw [lintegral_neg_eq_self, lintegral_indicator measurableSet_Ioi]
  have hboundary : (∫⁻ x in Ici (0 : ℝ), f x) = ∫⁻ x in Ioi (0 : ℝ), f x := by
    apply setLIntegral_congr
    exact Ioi_ae_eq_Ici.symm
  rw [← lintegral_add_compl f measurableSet_Iio, compl_Iio, hboundary, hn, two_mul]

theorem positive_square_lintegral (f : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioi (0 : ℝ), f y = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * x) * f (x ^ 2) := by
  have himg : (fun x : ℝ => x ^ 2) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact sq_pos_of_pos (show 0 < x from hx)
    · intro hy
      exact ⟨Real.sqrt y, Real.sqrt_pos.mpr hy, Real.sq_sqrt hy.le⟩
  conv_lhs => rw [← himg]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun x _ => (hasDerivAt_pow 2 x).hasDerivWithinAt)]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [abs_of_pos (show 0 < x from hx)]
  · intro x hx y hy hxy
    exact (sq_eq_sq₀ (le_of_lt hx) (le_of_lt hy)).mp hxy

theorem gaussian_square_density_ennreal (x : ℝ) (hx : 0 < x) :
    ENNReal.ofReal (2 * x) * gammaPDF (1 / 2) (1 / 2) (x ^ 2) =
      2 * gaussianPDF 0 1 x := by
  rw [gammaPDF, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * x), gaussian_square_density x hx,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [gaussianPDF]

theorem gaussian_square_gamma :
    (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) = gammaMeasure (1 / 2) (1 / 2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop), gaussianReal_of_var_ne_zero _ (by norm_num)]
  have hfm : Measurable (fun x : ℝ => f (x ^ 2)) := hf.comp (by fun_prop)
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hfm]
  simp only [Pi.mul_apply]
  rw [lintegral_even_real (fun x => gaussianPDF 0 1 x * f (x ^ 2)) (by
    intro x
    simp [gaussianPDF, gaussianPDFReal])]
  conv_rhs => rw [← gammaMeasure_restrict_positive (1 / 2) (1 / 2), gammaMeasure,
    restrict_withDensity measurableSet_Ioi]
  have hd : Measurable (gammaPDF (1 / 2) (1 / 2)) :=
    (measurable_gammaPDFReal _ _).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hf]
  simp only [Pi.mul_apply]
  conv_rhs => rw [positive_square_lintegral]
  calc
    _ = ∫⁻ x in Ioi (0 : ℝ), 2 * (gaussianPDF 0 1 x * f (x ^ 2)) := by
      rw [lintegral_const_mul' _ _ (by norm_num)]
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simpa only [mul_assoc] using congrArg (fun c : ℝ≥0∞ => c * f (x ^ 2))
        (gaussian_square_density_ennreal x hx).symm

theorem gaussian_pair_squares_gamma :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) =
      gammaMeasure 1 (1 / 2) := by
  have hq : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
  calc
    _ = (((gaussianReal 0 1).map (fun x : ℝ => x ^ 2)).prod
        ((gaussianReal 0 1).map (fun x : ℝ => x ^ 2))).map (fun p : ℝ × ℝ => p.1 + p.2) := by
      rw [Measure.map_prod_map _ _ hq hq, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [gaussian_square_gamma, gamma_sum_gamma (by norm_num) (by norm_num) (by norm_num)]
      norm_num

end MathieuProperty
