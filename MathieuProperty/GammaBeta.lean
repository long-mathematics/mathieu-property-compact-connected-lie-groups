import MathieuProperty.BetaMoments
import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Gamma sums and beta ratios for the actual mathlib probability measures.

The split map (u,t) ↦ (ut,(1-u)t) parametrizes the positive quadrant with
Jacobian t. Its density factorization identifies independent gamma variables
with an independent beta ratio and gamma sum. This supplies distribution
infrastructure for the classical sphere radial laws.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace MathieuProperty

def gammaSplit (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * p.2, (1 - p.1) * p.2)

def gammaSplitDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem gammaSplit_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt gammaSplit (gammaSplitDerivative p) p := by
  have h₁ : HasFDerivAt (fun q : ℝ × ℝ => q.1 * q.2)
      (p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    by
      convert! (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul
        (hasFDerivAt_snd (𝕜 := ℝ) (p := p)) using 1
      simp only [add_comm]
  convert h₁.prodMk ((hasFDerivAt_snd (p := p)).sub h₁) using 1
  · funext q
    dsimp [gammaSplit]
    ext <;> ring
  · ext <;> simp [gammaSplitDerivative]

theorem gammaSplitDerivative_det (p : ℝ × ℝ) :
    (gammaSplitDerivative p).det = p.2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, gammaSplitDerivative, Module.Basis.finTwoProd_zero,
    Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr]
  ring

theorem gammaSplit_image :
    gammaSplit '' ((Ioo (0 : ℝ) 1) ×ˢ Ioi 0) = (Ioi (0 : ℝ)) ×ˢ Ioi 0 := by
  ext p
  constructor
  · rintro ⟨⟨u,t⟩, ⟨hu, ht⟩, rfl⟩
    exact ⟨mul_pos hu.1 ht, mul_pos (sub_pos.mpr hu.2) ht⟩
  · rintro ⟨hx, hy⟩
    change 0 < p.1 at hx
    change 0 < p.2 at hy
    have ht : 0 < p.1 + p.2 := add_pos hx hy
    refine ⟨(p.1 / (p.1 + p.2), p.1 + p.2), ?_, ?_⟩
    · exact ⟨⟨div_pos hx ht, (div_lt_one ht).mpr (by linarith)⟩, ht⟩
    · dsimp [gammaSplit]
      ext <;> field_simp; ring

theorem gammaSplit_injOn : InjOn gammaSplit ((Ioo (0 : ℝ) 1) ×ˢ Ioi 0) := by
  rintro ⟨u,t⟩ hu ⟨v,s⟩ hv h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [gammaSplit] at h₁ h₂
  have hts : t = s := by nlinarith
  subst s
  have huv : u = v := (mul_left_inj' (ne_of_gt hu.2)).mp h₁
  subst v
  rfl

theorem gammaSplit_lintegral (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p in (Ioi (0 : ℝ)) ×ˢ Ioi 0, f p =
      ∫⁻ p in (Ioo (0 : ℝ) 1) ×ˢ Ioi 0, ENNReal.ofReal p.2 * f (gammaSplit p) := by
  rw [← gammaSplit_image]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_Ioo.prod measurableSet_Ioi)
    (fun p _ => (gammaSplit_hasFDerivAt p).hasFDerivWithinAt) gammaSplit_injOn]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioi)
  intro p hp
  change ENNReal.ofReal |(gammaSplitDerivative p).det| * f (gammaSplit p) = _
  rw [gammaSplitDerivative_det, abs_of_pos hp.2]

theorem gamma_beta_density_factor {a b r u t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hu : u ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) :
    t * gammaPDFReal a r (u * t) * gammaPDFReal b r ((1 - u) * t) =
      betaPDFReal a b u * gammaPDFReal (a + b) r t := by
  have hu0 : 0 < u := hu.1
  have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
  have hpow : t * (t ^ (a - 1) * t ^ (b - 1)) = t ^ (a + b - 1) := by
    calc
      _ = t ^ (1 : ℝ) * (t ^ (a - 1) * t ^ (b - 1)) := by rw [Real.rpow_one]
      _ = t ^ (1 + ((a - 1) + (b - 1))) := by rw [← Real.rpow_add ht, ← Real.rpow_add ht]
      _ = _ := by congr 1; ring
  have hexp : Real.exp (-(r * (u * t))) * Real.exp (-(r * ((1 - u) * t))) =
      Real.exp (-(r * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [gammaPDFReal, betaPDFReal, ite_eq_left (mul_pos hu0 ht).le,
    ite_eq_left (mul_pos hu1 ht).le, ite_eq_left ht.le, ite_eq_left (show 0 < u ∧ u < 1 from hu)]
  rw [Real.mul_rpow hu0.le ht.le, Real.mul_rpow hu1.le ht.le]
  have hGa := (Real.Gamma_pos_of_pos ha).ne'
  have hGb := (Real.Gamma_pos_of_pos hb).ne'
  have hGab := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  calc
    _ = (r ^ a * r ^ b) / (Real.Gamma a * Real.Gamma b) *
        (u ^ (a - 1) * (1 - u) ^ (b - 1)) *
        (t * (t ^ (a - 1) * t ^ (b - 1))) *
        (Real.exp (-(r * (u * t))) * Real.exp (-(r * ((1 - u) * t)))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hr, hpow, hexp]
      simp only [beta]
      field_simp

theorem gammaMeasure_restrict_positive (a r : ℝ) :
    (gammaMeasure a r).restrict (Ioi 0) = gammaMeasure a r := by
  rw [gammaMeasure, restrict_withDensity measurableSet_Ioi, ← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  by_cases hxp : 0 < x
  · simp [hxp]
  · have hxn : x < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx
    simp [hxp, gammaPDF_of_neg hxn]

theorem betaMeasure_restrict_unit (a b : ℝ) :
    (betaMeasure a b).restrict (Ioo 0 1) = betaMeasure a b := by
  rw [betaMeasure, restrict_withDensity measurableSet_Ioo, ← withDensity_indicator measurableSet_Ioo]
  congr 1
  funext x
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · simp [hx]
  · simp [hx, betaPDF, betaPDFReal, show ¬ (0 < x ∧ x < 1) from hx]

theorem gamma_product_density_restrict (a b r : ℝ) :
    (gammaMeasure a r).prod (gammaMeasure b r) =
      (volume.restrict ((Ioi (0 : ℝ)) ×ˢ Ioi 0)).withDensity
        (fun p : ℝ × ℝ => gammaPDF a r p.1 * gammaPDF b r p.2) := by
  calc
    _ = ((gammaMeasure a r).restrict (Ioi 0)).prod
        ((gammaMeasure b r).restrict (Ioi 0)) := by
      rw [gammaMeasure_restrict_positive, gammaMeasure_restrict_positive]
    _ = _ := by
      simp only [gammaMeasure, restrict_withDensity measurableSet_Ioi]
      rw [prod_withDensity, Measure.prod_restrict]
      · rfl
      · exact (measurable_gammaPDFReal a r).ennreal_ofReal
      · exact (measurable_gammaPDFReal b r).ennreal_ofReal

theorem beta_gamma_product_density_restrict (a b r : ℝ) :
    (betaMeasure a b).prod (gammaMeasure (a + b) r) =
      (volume.restrict ((Ioo (0 : ℝ) 1) ×ˢ Ioi 0)).withDensity
        (fun p : ℝ × ℝ => betaPDF a b p.1 * gammaPDF (a + b) r p.2) := by
  calc
    _ = ((betaMeasure a b).restrict (Ioo 0 1)).prod
        ((gammaMeasure (a + b) r).restrict (Ioi 0)) := by
      rw [betaMeasure_restrict_unit, gammaMeasure_restrict_positive]
    _ = _ := by
      simp only [gammaMeasure, betaMeasure, restrict_withDensity measurableSet_Ioi,
        restrict_withDensity measurableSet_Ioo]
      rw [prod_withDensity, Measure.prod_restrict]
      · rfl
      · exact (measurable_betaPDFReal a b).ennreal_ofReal
      · exact (measurable_gammaPDFReal (a + b) r).ennreal_ofReal

theorem gamma_beta_density_factor_ennreal {a b r u t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hu : u ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) :
    ENNReal.ofReal t * gammaPDF a r (u * t) * gammaPDF b r ((1 - u) * t) =
      betaPDF a b u * gammaPDF (a + b) r t := by
  simp only [gammaPDF, betaPDF, ← ENNReal.ofReal_mul ht.le,
    ← ENNReal.ofReal_mul (mul_nonneg ht.le (gammaPDFReal_nonneg ha hr _)),
    ← ENNReal.ofReal_mul (betaPDFReal_nonneg ha hb _)]
  rw [gamma_beta_density_factor ha hb hr hu ht]

theorem gammaSplit_map {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((betaMeasure a b).prod (gammaMeasure (a + b) r)).map gammaSplit =
      (gammaMeasure a r).prod (gammaMeasure b r) := by
  have hm : Measurable gammaSplit := by unfold gammaSplit; fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm, beta_gamma_product_density_restrict, gamma_product_density_restrict]
  have hd₁ : Measurable (fun p : ℝ × ℝ => betaPDF a b p.1 * gammaPDF (a + b) r p.2) :=
    (((measurable_betaPDFReal a b).ennreal_ofReal.comp measurable_fst).mul
      ((measurable_gammaPDFReal (a + b) r).ennreal_ofReal.comp measurable_snd))
  have hd₂ : Measurable (fun p : ℝ × ℝ => gammaPDF a r p.1 * gammaPDF b r p.2) :=
    (((measurable_gammaPDFReal a r).ennreal_ofReal.comp measurable_fst).mul
      ((measurable_gammaPDFReal b r).ennreal_ofReal.comp measurable_snd))
  have hfm : Measurable (fun p => f (gammaSplit p)) := hf.comp hm
  rw [lintegral_withDensity_eq_lintegral_mul _ hd₁ hfm,
    lintegral_withDensity_eq_lintegral_mul _ hd₂ hf]
  rw [gammaSplit_lintegral]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioi)
  intro p hp
  change (betaPDF a b p.1 * gammaPDF (a + b) r p.2) * f (gammaSplit p) =
    ENNReal.ofReal p.2 * ((gammaPDF a r (p.1 * p.2) *
      gammaPDF b r ((1 - p.1) * p.2)) * f (gammaSplit p))
  rw [← gamma_beta_density_factor_ennreal ha hb hr hp.1 hp.2]
  ring

def gammaRatioSum (p : ℝ × ℝ) : ℝ × ℝ := (p.1 / (p.1 + p.2), p.1 + p.2)

theorem gammaRatioSum_gammaSplit (p : ℝ × ℝ) (ht : p.2 ≠ 0) :
    gammaRatioSum (gammaSplit p) = p := by
  dsimp [gammaRatioSum, gammaSplit]
  have h : p.1 * p.2 + (1 - p.1) * p.2 = p.2 := by ring
  rw [h, mul_div_cancel_right₀ _ ht]

theorem gammaRatioSum_map {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map gammaRatioSum =
      (betaMeasure a b).prod (gammaMeasure (a + b) r) := by
  let := isProbabilityMeasureBeta ha hb
  let := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hm : Measurable gammaSplit := by unfold gammaSplit; fun_prop
  have hn : Measurable gammaRatioSum := by unfold gammaRatioSum; fun_prop
  have hsupport : ∀ᵐ p ∂(betaMeasure a b).prod (gammaMeasure (a + b) r),
      p ∈ (Ioo (0 : ℝ) 1) ×ˢ Ioi 0 := by
    have heq : ((betaMeasure a b).prod (gammaMeasure (a + b) r)).restrict
        ((Ioo (0 : ℝ) 1) ×ˢ Ioi 0) = (betaMeasure a b).prod (gammaMeasure (a + b) r) := by
      rw [← Measure.prod_restrict, betaMeasure_restrict_unit, gammaMeasure_restrict_positive]
    rw [← heq]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioi)
  rw [← gammaSplit_map ha hb hr, Measure.map_map hn hm]
  have heq : (gammaRatioSum ∘ gammaSplit) =ᵐ[(betaMeasure a b).prod (gammaMeasure (a + b) r)] id := by
    filter_upwards [hsupport] with p hp
    exact gammaRatioSum_gammaSplit p (ne_of_gt hp.2)
  rw [Measure.map_congr heq, Measure.map_id]

theorem gamma_ratio_beta {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map (fun p => p.1 / (p.1 + p.2)) =
      betaMeasure a b := by
  let := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hm : Measurable gammaRatioSum := by unfold gammaRatioSum; fun_prop
  have hh := congrArg (Measure.map (Prod.fst : ℝ × ℝ → ℝ)) (gammaRatioSum_map ha hb hr)
  rw [Measure.map_map measurable_fst hm] at hh
  exact hh.trans (Measure.fst_prod (μ := betaMeasure a b) (ν := gammaMeasure (a + b) r))

theorem gamma_sum_gamma {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map (fun p => p.1 + p.2) =
      gammaMeasure (a + b) r := by
  let := isProbabilityMeasureBeta ha hb
  let := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hm : Measurable gammaRatioSum := by unfold gammaRatioSum; fun_prop
  have hh := congrArg (Measure.map (Prod.snd : ℝ × ℝ → ℝ)) (gammaRatioSum_map ha hb hr)
  rw [Measure.map_map measurable_snd hm] at hh
  exact hh.trans (Measure.snd_prod (μ := betaMeasure a b) (ν := gammaMeasure (a + b) r))

end MathieuProperty
