import MathieuProperty.BilinearDefect
import MathieuProperty.DerivationExponential
import MathieuProperty.FiniteDimensionalSlice
/-! Local logarithms for automorphisms of a continuous bilinear operation.
The implicit function theorem and derivation exponentials show that the full
bracket-preservation equations locally equal their projected equations. -/

noncomputable section
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace BilinearAutomorphism
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
open NormedSpace

def exponential (B : V →L[ℝ] V →L[ℝ] V) (D : derivations B) : V →L[ℝ] V := exp D.val

omit [FiniteDimensional ℝ V] in
@[simp] theorem exponential_zero (B : V →L[ℝ] V →L[ℝ] V) : exponential B 0 = 1 := by
  exact exp_zero

theorem exponential_defect (B : V →L[ℝ] V →L[ℝ] V) (D : derivations B) :
    defect B (exponential B D) = 0 := by
  ext x y
  change exp D.val (B x y) - B (exp D.val x) (exp D.val y) = 0
  exact sub_eq_zero.mpr (DerivationExponential.exp_preserves_bilinear B D.val
    ((mem_derivations_iff B D.val).mp D.property) x y)

theorem exponential_strictDeriv (B : V →L[ℝ] V →L[ℝ] V) :
    HasStrictFDerivAt (exponential B) (derivations B).subtypeL 0 := by
  have h := HasStrictFDerivAt.comp (𝕜 := ℝ)
    (f := fun D : derivations B => D.val) (f' := (derivations B).subtypeL)
    (g := exp) (g' := (1 : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)) (0 : derivations B)
    (by simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := V →L[ℝ] V)))
    (derivations B).subtypeL.hasStrictFDerivAt
  simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using! h

def exponentialProjection (B : V →L[ℝ] V →L[ℝ] V) (D : derivations B) : derivations B :=
  FiniteSlice.projection (derivations B) (exponential B D - 1)

@[simp] theorem exponentialProjection_zero (B : V →L[ℝ] V →L[ℝ] V) :
    exponentialProjection B 0 = 0 := by simp [exponentialProjection]

theorem exponentialProjection_strictDeriv (B : V →L[ℝ] V →L[ℝ] V) :
    HasStrictFDerivAt (exponentialProjection B) ((ContinuousLinearEquiv.refl ℝ (derivations B)) : derivations B →L[ℝ] derivations B) 0 := by
  have hp : (FiniteSlice.projection (derivations B)).comp (derivations B).subtypeL =
      ((ContinuousLinearEquiv.refl ℝ (derivations B)) : derivations B →L[ℝ] derivations B) := by
    apply ContinuousLinearMap.ext
    intro D
    exact FiniteSlice.projection_self (derivations B) D
  have h := (FiniteSlice.projection (derivations B)).hasStrictFDerivAt.comp (0 : derivations B)
    ((exponential_strictDeriv B).sub_const 1)
  simpa only [hp] using! h

def exponentialCoordinates (B : V →L[ℝ] V →L[ℝ] V) :
    OpenPartialHomeomorph (derivations B) (derivations B) :=
  (exponentialProjection_strictDeriv B).toOpenPartialHomeomorph (exponentialProjection B)


theorem exponential_smooth (B : V →L[ℝ] V →L[ℝ] V) : ContDiff ℝ ∞ (exponential B) := by
  have he : ContDiff ℝ ∞ (exp : (V →L[ℝ] V) → V →L[ℝ] V) :=
    (show AnalyticOnNhd ℝ exp Set.univ from fun x _ => exp_analytic x).contDiff
  exact he.comp (derivations B).subtypeL.contDiff

theorem exponentialProjection_smooth (B : V →L[ℝ] V →L[ℝ] V) :
    ContDiff ℝ ∞ (exponentialProjection B) :=
  (FiniteSlice.projection (derivations B)).contDiff.comp ((exponential_smooth B).sub contDiff_const)

def ambientCoordinates (B : V →L[ℝ] V →L[ℝ] V) :
    OpenPartialHomeomorph (V →L[ℝ] V) ((linearDefect B).range × derivations B) :=
  FiniteSlice.coordinates (defect B) (linearDefect B) 1
    ((defect_smooth B).contDiffAt.hasStrictFDerivAt (by simp))

theorem ambientCoordinates_one_mem (B : V →L[ℝ] V →L[ℝ] V) :
    (1 : V →L[ℝ] V) ∈ (ambientCoordinates B).source :=
  FiniteSlice.mem_coordinates_source _ _ _ _

def logarithm (B : V →L[ℝ] V →L[ℝ] V) (T : V →L[ℝ] V) : derivations B :=
  (exponentialCoordinates B).symm (FiniteSlice.projection (derivations B) (T-1))

@[simp] theorem logarithm_one (B : V →L[ℝ] V →L[ℝ] V) : logarithm B 1 = 0 := by
  have h := (exponentialProjection_strictDeriv B).localInverse_apply_image
  simpa only [exponentialProjection_zero, logarithm, sub_self, map_zero,
    exponentialCoordinates, HasStrictFDerivAt.localInverse_def] using! h

theorem logarithm_continuousAt_one (B : V →L[ℝ] V →L[ℝ] V) :
    ContinuousAt (logarithm B) 1 := by
  have h : ContinuousAt (exponentialCoordinates B).symm 0 := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_strictDeriv B).localInverse_continuousAt
  have hp : ContinuousAt (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B) (T-1)) 1 :=
    (FiniteSlice.projection (derivations B)).continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
  exact h.comp_of_eq hp (by simp)


theorem exponential_logarithm_eventually (B : V →L[ℝ] V →L[ℝ] V) :
    ∀ᶠ T in 𝓝 (1 : V →L[ℝ] V),
      FiniteSlice.projection (linearDefect B).range (defect B T) = 0 →
        exponential B (logarithm B T) = T := by
  have hp : ContinuousAt (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B) (T-1)) 1 :=
    (FiniteSlice.projection (derivations B)).continuous.continuousAt.comp
      (continuousAt_id.sub continuousAt_const)
  have hp₀ : Filter.Tendsto (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B) (T-1)) (𝓝 1) (𝓝 0) := by
    simpa only [ContinuousAt, sub_self, map_zero] using! hp
  have hr : ∀ᶠ D in 𝓝 (0 : derivations B),
      exponentialProjection B ((exponentialCoordinates B).symm D) = D := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_strictDeriv B).eventually_right_inverse
  have hs : (ambientCoordinates B).source ∈ 𝓝 (1 : V →L[ℝ] V) :=
    (ambientCoordinates B).open_source.mem_nhds (ambientCoordinates_one_mem B)
  have he : ContinuousAt (fun T => exponential B (logarithm B T)) 1 :=
    (exponential_smooth B).continuous.continuousAt.comp (logarithm_continuousAt_one B)
  have he₁ : Filter.Tendsto (fun T => exponential B (logarithm B T)) (𝓝 1) (𝓝 1) := by
    simpa only [ContinuousAt, logarithm_one, exponential_zero] using! he
  filter_upwards [hs, he₁ hs, hp₀ hr] with T hT hE hP
  intro hF
  apply (ambientCoordinates B).injOn hE hT
  apply Prod.ext
  · change FiniteSlice.projection (linearDefect B).range
      (defect B (exponential B (logarithm B T))) = _
    rw [exponential_defect, map_zero]
    exact hF.symm
  · exact hP

theorem defect_zero_iff_projected_eventually (B : V →L[ℝ] V →L[ℝ] V) :
    ∀ᶠ T in 𝓝 (1 : V →L[ℝ] V), defect B T = 0 ↔
      FiniteSlice.projection (linearDefect B).range (defect B T) = 0 := by
  filter_upwards [exponential_logarithm_eventually B] with T hT
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    rw [← hT h]
    exact exponential_defect B _


theorem logarithm_exponential_eventually (B : V →L[ℝ] V →L[ℝ] V) :
    ∀ᶠ D in 𝓝 (0 : derivations B), logarithm B (exponential B D) = D :=
  (exponentialProjection_strictDeriv B).eventually_left_inverse

theorem logarithm_smoothAt_one (B : V →L[ℝ] V →L[ℝ] V) :
    ContDiffAt ℝ ∞ (logarithm B) 1 := by
  have hi : ContDiffAt ℝ ∞ (exponentialCoordinates B).symm 0 := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_smooth B).contDiffAt.to_localInverse
        (exponentialProjection_strictDeriv B).hasFDerivAt (by simp)
  have hp : ContDiff ℝ ∞ (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B) (T-1)) :=
    (FiniteSlice.projection (derivations B)).contDiff.comp (contDiff_id.sub contDiff_const)
  have hi' : ContDiffAt ℝ ∞ (exponentialCoordinates B).symm
      (FiniteSlice.projection (derivations B) (1-1)) := by simpa using! hi
  exact hi'.comp (1 : V →L[ℝ] V) hp.contDiffAt

end BilinearAutomorphism
end MathieuProperty
