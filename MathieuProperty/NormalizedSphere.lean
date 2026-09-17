import MathieuProperty.SphereSymmetry

/-! Normalized cone surface measure in every finite-dimensional real inner product space. -/

noncomputable section
open MeasureTheory Metric
open scoped Pointwise
namespace MathieuProperty
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def linearSphereAction (e : E ≃ₗᵢ[ℝ] E) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 where
  toFun z := ⟨e z.val, by
    rw [mem_sphere_zero_iff_norm, e.norm_map]
    exact mem_sphere_zero_iff_norm.mp z.property⟩
  invFun z := ⟨e.symm z.val, by
    rw [mem_sphere_zero_iff_norm, e.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp z.property⟩
  left_inv z := by ext; exact e.symm_apply_apply z.val
  right_inv z := by ext; exact e.apply_symm_apply z.val
  continuous_toFun := continuous_induced_rng.mpr (e.continuous.comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.mpr (e.symm.continuous.comp continuous_subtype_val)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem linearSphere_cone_preimage (e : E ≃ₗᵢ[ℝ] E) (S : Set (Metric.sphere (0 : E) 1)) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (linearSphereAction e ⁻¹' S)) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' S)) := by
  ext y
  constructor
  · rintro ⟨r, hr, w, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨r, hr, e z.val, ⟨linearSphereAction e z, hz, rfl⟩, (e.map_smul r z.val).symm⟩
  · rintro ⟨r, hr, w, ⟨z, hz, rfl⟩, heq⟩
    refine ⟨r, hr, e.symm z.val, ⟨linearSphereAction e.symm z, ?_, rfl⟩, ?_⟩
    · have hz' : linearSphereAction e (linearSphereAction e.symm z) = z := by
        ext; exact e.apply_symm_apply z.val
      simpa only [Set.mem_preimage, hz'] using hz
    · apply e.injective
      simpa using heq

theorem sphereSurface_preserving (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (linearSphereAction e) (volume : Measure E).toSphere (volume : Measure E).toSphere := by
  refine ⟨(linearSphereAction e).measurable, ?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (linearSphereAction e).measurable hS]
  rw [Measure.toSphere_apply' _ ((linearSphereAction e).measurable hS),
    Measure.toSphere_apply' _ hS, linearSphere_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

def normalizedSphereMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Metric.sphere (0 : E) 1) :=
  (((volume : Measure E).toSphere) Set.univ)⁻¹ • (volume : Measure E).toSphere

instance [Nontrivial E] : IsProbabilityMeasure (normalizedSphereMeasure E) where
  measure_univ := by
    rw [normalizedSphereMeasure, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero (volume : Measure E)))
      (measure_ne_top _ _)

theorem normalizedSphere_preserving (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (linearSphereAction e) (normalizedSphereMeasure E) (normalizedSphereMeasure E) := by
  refine ⟨(linearSphereAction e).measurable, ?_⟩
  rw [normalizedSphereMeasure, Measure.map_smul, (sphereSurface_preserving e).map_eq]
  exact (linearSphereAction e).measurable.aemeasurable

end MathieuProperty
