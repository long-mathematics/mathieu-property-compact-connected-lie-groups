import MathieuProperty.ClassicalOrbit
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Normalizing independent complex Gaussian coordinates gives normalized
Euclidean sphere measure in complex dimension n≥2.

The real and imaginary components below each have variance one. A common
positive rescaling gives the alternative variance-one complex convention and
leaves the normalized direction unchanged. The zero vector is a null set; the
measurable direction function takes an arbitrary fixed sphere value there.
-/

noncomputable section
open MeasureTheory Metric ProbabilityTheory
namespace MathieuProperty
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sphereDirection (z : Metric.sphere (0 : E) 1) (x : E) : Metric.sphere (0 : E) 1 := by
  classical
  exact if hx : x = 0 then z else
    ⟨‖x‖⁻¹ • x, by rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem sphereDirection_measurable (z : Metric.sphere (0 : E) 1) :
    Measurable (sphereDirection z) := by
  classical
  apply measurable_comap_iff.mpr
  have heq : Subtype.val ∘ sphereDirection z =
      (fun x : E => if x = 0 then z.val else ‖x‖⁻¹ • x) := by
    funext x
    by_cases hx : x = 0 <;> simp [sphereDirection, hx]
  rw [heq]
  exact measurable_const.ite (measurableSet_singleton 0) (measurable_norm.inv.smul measurable_id)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sphereDirection_isometry (z : Metric.sphere (0 : E) 1)
    (e : E ≃ₗᵢ[ℝ] E) (x : E) (hx : x ≠ 0) :
    sphereDirection z (e x) = linearSphereAction e (sphereDirection z x) := by
  have he : e x ≠ 0 := fun h => hx (e.injective (by simpa using h))
  apply Subtype.ext
  simp [sphereDirection, hx, he, linearSphereAction, e.norm_map]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem sphereDirection_pos_smul (z : Metric.sphere (0 : E) 1) (x : E)
    {r : ℝ} (hr : 0 < r) : sphereDirection z (r • x) = sphereDirection z x := by
  by_cases hx : x = 0
  · simp [hx, sphereDirection]
  have hrx : r • x ≠ 0 := smul_ne_zero hr.ne' hx
  apply Subtype.ext
  simp [sphereDirection, hx, hrx, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    smul_smul, mul_inv_rev, hr.ne']

instance stdGaussian_nullSingleton [Nontrivial E] : NullSingletonClass (stdGaussian E) := by
  apply IsGaussian.nullSingletonClass
  intro x hx
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hL : innerSL ℝ v ≠ 0 := by
    intro h
    have hh := congrArg (fun L : StrongDual ℝ E => L v) h
    exact hv (by simpa using hh)
  have hh := variance_dual_stdGaussian (E := E) (innerSL ℝ v)
  rw [hx, variance_dirac] at hh
  exact (sq_pos_of_pos (norm_pos_iff.mpr hL)).ne' hh.symm

theorem sphereDirection_gaussian_invariant [Nontrivial E]
    (z : Metric.sphere (0 : E) 1) (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (linearSphereAction e)
      ((stdGaussian E).map (sphereDirection z))
      ((stdGaussian E).map (sphereDirection z)) := by
  refine ⟨(linearSphereAction e).measurable, ?_⟩
  rw [Measure.map_map (linearSphereAction e).measurable (sphereDirection_measurable z)]
  have heq : (linearSphereAction e ∘ sphereDirection z) =ᵐ[stdGaussian E]
      (sphereDirection z ∘ e) := by
    filter_upwards [(stdGaussian E).ae_ne 0] with x hx
    exact (sphereDirection_isometry z e x hx).symm
  rw [Measure.map_congr heq, ← Measure.map_map (sphereDirection_measurable z) e.continuous.measurable,
    stdGaussian_map]

theorem gaussian_sphere (n : ℕ) (hn : 2 ≤ n) (z : ClassicalSphere n) :
    (stdGaussian (EuclideanSpace ℂ (Fin n))).map (sphereDirection z) =
      normalizedSphereMeasure (EuclideanSpace ℂ (Fin n)) := by
  let : NeZero n := ⟨by omega⟩
  let μ := (stdGaussian (EuclideanSpace ℂ (Fin n))).map (sphereDirection z)
  have : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let : SMulInvariantMeasure (Matrix.specialUnitaryGroup (Fin n) ℂ) (ClassicalSphere n) μ := {
    measure_preimage_smul := fun g S hS =>
      (sphereDirection_gaussian_invariant z (specialUnitaryRealIsometry n g)).measure_preimage
        hS.nullMeasurableSet }
  exact (measurePreserving_transitive_orbit μ (specialUnitarySphere_transitive n hn) z).map_eq.symm.trans
    (specialUnitarySphere_orbit n hn z).map_eq

def complexGaussianCoordinates (n : ℕ) (x : ((_i : Fin n) × Fin 2) → ℝ) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => (x ⟨i, 0⟩ : ℂ) + (x ⟨i, 1⟩ : ℂ) * Complex.I)

theorem complexGaussianCoordinates_map (n : ℕ) :
    (Measure.pi (fun _ : (_i : Fin n) × Fin 2 => gaussianReal 0 1)).map
      (complexGaussianCoordinates n) = stdGaussian (EuclideanSpace ℂ (Fin n)) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis
    (Pi.orthonormalBasis (fun _ : Fin n => Complex.orthonormalBasisOneI))]
  congr 1
  funext x
  ext i
  simp [complexGaussianCoordinates, Fintype.sum_sigma, Complex.coe_orthonormalBasisOneI,
    Fin.sum_univ_two, Pi.single_apply, Finset.sum_add_distrib]

theorem normalized_independent_complex_gaussian (n : ℕ) (hn : 2 ≤ n)
    (z : ClassicalSphere n) :
    (Measure.pi (fun _ : (_i : Fin n) × Fin 2 => gaussianReal 0 1)).map
      (sphereDirection z ∘ complexGaussianCoordinates n) =
      normalizedSphereMeasure (EuclideanSpace ℂ (Fin n)) := by
  have hc : Measurable (complexGaussianCoordinates n) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).measurable.comp
    apply Measurable.of_eval
    intro i
    exact ((Complex.continuous_ofReal.measurable.comp (measurable_pi_apply (⟨i, 0⟩ : (_i : Fin n) × Fin 2)))).add
      ((Complex.continuous_ofReal.measurable.comp (measurable_pi_apply (⟨i, 1⟩ : (_i : Fin n) × Fin 2))).mul_const _)
  rw [← Measure.map_map (sphereDirection_measurable z) hc, complexGaussianCoordinates_map]
  exact gaussian_sphere n hn z

end MathieuProperty
