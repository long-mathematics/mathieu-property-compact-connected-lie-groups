import MathieuProperty.HopfAlgebra
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Measure.Support

/-! The Euclidean sphere model, normalized surface measure, and integrability
and positivity facts required by the Hopf and radial-transfer theorems. -/

noncomputable section
open MeasureTheory Metric
open scoped Pointwise
namespace MathieuProperty.Hopf

abbrev EuclideanPair := WithLp 2 Space

instance : TopologicalSpace Sphere := inferInstanceAs (TopologicalSpace {z : Space // a z = 1})
instance : MeasurableSpace Sphere := inferInstanceAs (MeasurableSpace {z : Space // a z = 1})
instance : BorelSpace Sphere := inferInstanceAs (BorelSpace {z : Space // a z = 1})
instance : T2Space Sphere := inferInstanceAs (T2Space {z : Space // a z = 1})

theorem norm_sq_eq_a (z : EuclideanPair) : ‖z‖ ^ 2 = a (WithLp.ofLp z) := by
  simp [a, Complex.normSq_eq_norm_sq, WithLp.prod_norm_sq_eq_of_L2]

def sphereHomeomorph : Metric.sphere (0 : EuclideanPair) 1 ≃ₜ Sphere where
  toFun z := ⟨WithLp.ofLp z.val, by
    rw [← norm_sq_eq_a]
    have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
    simp [hz]⟩
  invFun z := ⟨WithLp.toLp 2 z.val, by
    change dist (WithLp.toLp 2 z.val) 0 = 1
    rw [dist_zero_right]
    have h : ‖WithLp.toLp 2 z.val‖ ^ 2 = 1 := by rw [norm_sq_eq_a]; exact z.property
    nlinarith [norm_nonneg (WithLp.toLp 2 z.val)]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.mpr
    ((WithLp.prod_continuous_ofLp 2 ℂ ℂ).comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.mpr
    ((WithLp.prod_continuous_toLp 2 ℂ ℂ).comp continuous_subtype_val)

instance : CompactSpace Sphere := sphereHomeomorph.compactSpace

@[fun_prop] theorem continuous_a : Continuous a := by unfold a; fun_prop
@[fun_prop] theorem continuous_tau : Continuous tau := by unfold tau; fun_prop
@[fun_prop] theorem continuous_u : Continuous u := by unfold u; fun_prop
@[fun_prop] theorem continuous_v : Continuous v := by unfold v; fun_prop
@[fun_prop] theorem continuous_P : Continuous P := by unfold P; fun_prop
@[fun_prop] theorem continuous_Q : Continuous Q := continuous_u

@[fun_prop] theorem continuous_p : Continuous p := continuous_P.comp continuous_subtype_val
@[fun_prop] theorem continuous_q : Continuous q := continuous_Q.comp continuous_subtype_val

/-- Unnormalized Euclidean surface measure, from the cone construction. -/
def euclideanSurface : Measure (Metric.sphere (0 : EuclideanPair) 1) :=
  (volume : Measure EuclideanPair).toSphere

instance : IsFiniteMeasure euclideanSurface := by
  unfold euclideanSurface
  infer_instance

theorem euclideanSurface_ne_zero : euclideanSurface ≠ 0 :=
  Measure.toSphere_ne_zero _

/-- The manuscript's normalized Euclidean surface measure transported to `a(z)=1`. -/
def surfaceMeasure : Measure Sphere :=
  Measure.map sphereHomeomorph ((euclideanSurface Set.univ)⁻¹ • euclideanSurface)

instance : IsProbabilityMeasure ((euclideanSurface Set.univ)⁻¹ • euclideanSurface) where
  measure_univ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simpa using euclideanSurface_ne_zero) (measure_ne_top _ _)

instance : IsProbabilityMeasure surfaceMeasure := by
  unfold surfaceMeasure
  exact Measure.isProbabilityMeasure_map_iff sphereHomeomorph.measurable.aemeasurable |>.mpr inferInstance

/-- All polynomial Hopf moments are integrable for any finite measure on the sphere. -/
theorem sphere_polynomial_integrable (μ : Measure Sphere) [IsFiniteMeasure μ]
    (H : Polynomial ℂ) (m : ℕ) : Integrable (fun z => H.eval (q z) * p z ^ m) μ :=
  ((H.continuous.comp continuous_q).mul (continuous_p.pow m)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem volume_u_zero : (volume : Measure Space) {z | u z = 0} = 0 := by
  have hset : {z : Space | u z = 0} =
      ({0} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {0}) := by
    ext z
    simp [u, mul_eq_zero]
  rw [hset]
  apply measure_union_null
  · change (volume : Measure ℂ).prod volume ({0} ×ˢ Set.univ) = 0
    simp
  · change (volume : Measure ℂ).prod volume (Set.univ ×ˢ {0}) = 0
    simp

theorem euclidean_volume_u_zero :
    (volume : Measure EuclideanPair) {z | u (WithLp.ofLp z) = 0} = 0 := by
  have hm := (WithLp.volume_preserving_ofLp ℂ ℂ).map_eq
  have hs : MeasurableSet {z : Space | u z = 0} := continuous_u.measurable (measurableSet_singleton 0)
  have hz := volume_u_zero
  rw [← hm, Measure.map_apply (WithLp.prod_continuous_ofLp 2 ℂ ℂ).measurable hs] at hz
  exact hz

/-- The endpoint circles have zero Euclidean surface measure, proved from the
cone definition and the ambient null coordinate planes. -/
theorem euclideanSurface_u_zero :
    euclideanSurface {z | u (WithLp.ofLp z.val) = 0} = 0 := by
  have hs : MeasurableSet {z : Metric.sphere (0 : EuclideanPair) 1 |
      u (WithLp.ofLp z.val) = 0} :=
    ((continuous_u.comp (WithLp.prod_continuous_ofLp 2 ℂ ℂ)).comp
      continuous_subtype_val).measurable (measurableSet_singleton 0)
  rw [euclideanSurface, Measure.toSphere_apply' _ hs]
  have hc : (volume : Measure EuclideanPair)
      (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' {z : Metric.sphere (0 : EuclideanPair) 1 |
        u (WithLp.ofLp z.val) = 0})) = 0 := by
    apply measure_mono_null _ euclidean_volume_u_zero
    rintro y ⟨r, hr, w, ⟨z, hz, rfl⟩, rfl⟩
    change u (r • WithLp.ofLp z.val) = 0
    have heq : (r • WithLp.ofLp z.val : Space) = (r : ℂ) • WithLp.ofLp z.val := by
      ext <;> simp [Complex.real_smul]
    rw [heq, u_smul, hz, mul_zero]
  rw [hc, mul_zero]

theorem surfaceMeasure_u_zero : surfaceMeasure {z | u z.val = 0} = 0 := by
  have hs : MeasurableSet {z : Sphere | u z.val = 0} :=
    (continuous_u.comp continuous_subtype_val).measurable (measurableSet_singleton 0)
  rw [surfaceMeasure, Measure.map_apply sphereHomeomorph.measurable hs,
    Measure.smul_apply, smul_eq_mul]
  change (euclideanSurface Set.univ)⁻¹ *
    euclideanSurface {z | u (WithLp.ofLp z.val) = 0} = 0
  rw [euclideanSurface_u_zero, mul_zero]

/-- The apparent denominator in the Hopf calculation is nonzero almost everywhere. -/
theorem u_ne_zero_ae : ∀ᵐ z ∂surfaceMeasure, u z.val ≠ 0 := by
  simpa only [ae_iff, not_not] using surfaceMeasure_u_zero

theorem p_localization_ae : ∀ᵐ z ∂surfaceMeasure,
    p z = (u z.val)⁻¹ * (1 + u z.val) * (1 - (1 + u z.val) ^ 2 * (tau z.val : ℂ) ^ 2) := by
  filter_upwards [u_ne_zero_ae] with z hz
  have h := defect_one z.val z.property
  change P z.val = _
  apply mul_left_cancel₀ hz
  rw [h]
  field_simp

/-- Compact support of the measure, not of the integrand, gives integrability. -/
theorem integrable_of_compact_measure_support {E : Type*} [NormedAddCommGroup E]
    (μ : Measure Space) [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {f : Space → E} (hf : Continuous f) : Integrable f μ := by
  have h := ContinuousOn.integrableOn_compact (μ := μ) hμ hf.continuousOn
  change Integrable f (μ.restrict μ.support) at h
  rw [Measure.restrict_eq_self_of_ae_mem (μ := μ) (s := μ.support) μ.support_mem_ae] at h
  exact h

theorem integrable_polynomial_compactSupport (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) (H : Polynomial ℂ) (m : ℕ) :
    Integrable (fun z => H.eval (Q z) * P z ^ m) μ :=
  integrable_of_compact_measure_support μ hμ
    ((H.continuous.comp continuous_Q).mul (continuous_P.pow m))

theorem radial_integral_pos (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) (hzero : 0 < μ ({0}ᶜ : Set Space))
    (n : ℕ) (hn : 1 ≤ n) : 0 < ∫ z, a z ^ n ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun z => pow_nonneg (a_nonneg z) n)
    (integrable_of_compact_measure_support μ hμ (continuous_a.pow n))]
  have hs : Function.support (fun z => a z ^ n) = ({0}ᶜ : Set Space) := by
    ext z
    simp [Function.mem_support, pow_eq_zero_iff (by omega : n ≠ 0), a_eq_zero_iff]
  rw [hs]
  exact hzero

/-- Radial powers have exactly the exponent `4m+s`, including the zero vector
obtained by taking a zero scalar. -/
theorem radial_power (c : ℂ) (z : Sphere) (m s : ℕ) :
    Q (c • z.val) ^ s * P (c • z.val) ^ m =
      (a (c • z.val) : ℂ) ^ (4 * m + s) * (q z ^ s * p z ^ m) := by
  simp only [Q_smul, P_smul, a_smul, z.property, mul_one, mul_pow, pow_mul, pow_add, p, q]
  ring

theorem radial_real_exponent (r : ℝ) (z : Sphere) (m s : ℕ) :
    a ((r : ℂ) • z.val) ^ (4 * m + s) = r ^ (8 * m + 2 * s) := by
  rw [a_smul, z.property, mul_one, Complex.normSq_ofReal]
  rw [← pow_two, ← pow_mul]
  congr 1
  ring

end MathieuProperty.Hopf
