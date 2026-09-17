import MathieuProperty.BilinearStabilizer
/-! Local logarithms for bilinear automorphisms fixing a subspace pointwise.
The implicit function theorem and derivation exponentials show that the full
bracket-preservation equations locally equal their projected equations. -/

noncomputable section
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace BilinearStabilizer
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
open NormedSpace

def exponential (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (D : derivations B W) : V →L[ℝ] V := exp D.val

omit [FiniteDimensional ℝ V] in
@[simp] theorem exponential_zero (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : exponential B W 0 = 1 := by
  exact exp_zero

theorem exponential_defect (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (D : derivations B W) :
    defect B W (exponential B W D) = 0 := by
  exact group_defect B W ⟨DerivationExponential.expUnit D.val, exp_mem_group B W D⟩

theorem exponential_strictDeriv (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    HasStrictFDerivAt (exponential B W) (derivations B W).subtypeL 0 := by
  have h := HasStrictFDerivAt.comp (𝕜 := ℝ)
    (f := fun D : derivations B W => D.val) (f' := (derivations B W).subtypeL)
    (g := exp) (g' := (1 : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)) (0 : derivations B W)
    (by simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := V →L[ℝ] V)))
    (derivations B W).subtypeL.hasStrictFDerivAt
  simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using! h

def exponentialProjection (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (D : derivations B W) : derivations B W :=
  FiniteSlice.projection (derivations B W) (exponential B W D - 1)

@[simp] theorem exponentialProjection_zero (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    exponentialProjection B W 0 = 0 := by simp [exponentialProjection]

theorem exponentialProjection_strictDeriv (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    HasStrictFDerivAt (exponentialProjection B W) ((ContinuousLinearEquiv.refl ℝ (derivations B W)) : derivations B W →L[ℝ] derivations B W) 0 := by
  have hp : (FiniteSlice.projection (derivations B W)).comp (derivations B W).subtypeL =
      ((ContinuousLinearEquiv.refl ℝ (derivations B W)) : derivations B W →L[ℝ] derivations B W) := by
    apply ContinuousLinearMap.ext
    intro D
    exact FiniteSlice.projection_self (derivations B W) D
  have h := (FiniteSlice.projection (derivations B W)).hasStrictFDerivAt.comp (0 : derivations B W)
    ((exponential_strictDeriv B W).sub_const 1)
  simpa only [hp] using! h

def exponentialCoordinates (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    OpenPartialHomeomorph (derivations B W) (derivations B W) :=
  (exponentialProjection_strictDeriv B W).toOpenPartialHomeomorph (exponentialProjection B W)


theorem exponential_smooth (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : ContDiff ℝ ∞ (exponential B W) := by
  have he : ContDiff ℝ ∞ (exp : (V →L[ℝ] V) → V →L[ℝ] V) :=
    (show AnalyticOnNhd ℝ exp Set.univ from fun x _ => exp_analytic x).contDiff
  exact he.comp (derivations B W).subtypeL.contDiff

theorem exponentialProjection_smooth (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ContDiff ℝ ∞ (exponentialProjection B W) :=
  (FiniteSlice.projection (derivations B W)).contDiff.comp ((exponential_smooth B W).sub contDiff_const)

set_option maxHeartbeats 800000 in
def ambientCoordinates (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    OpenPartialHomeomorph (V →L[ℝ] V) ((linearDefect B W).range × derivations B W) := by
  exact FiniteSlice.coordinates (E := V →L[ℝ] V)
    (F := (V →L[ℝ] V →L[ℝ] V) × (W →L[ℝ] V)) (defect B W) (linearDefect B W) 1
    (defect_strictDeriv B W)

theorem ambientCoordinates_one_mem (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    (1 : V →L[ℝ] V) ∈ (ambientCoordinates B W).source :=
  FiniteSlice.mem_coordinates_source _ _ _ _

def logarithm (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (T : V →L[ℝ] V) : derivations B W :=
  (exponentialCoordinates B W).symm (FiniteSlice.projection (derivations B W) (T-1))

@[simp] theorem logarithm_one (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : logarithm B W 1 = 0 := by
  have h := (exponentialProjection_strictDeriv B W).localInverse_apply_image
  simpa only [exponentialProjection_zero, logarithm, sub_self, map_zero,
    exponentialCoordinates, HasStrictFDerivAt.localInverse_def] using! h

theorem logarithm_continuousAt_one (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ContinuousAt (logarithm B W) 1 := by
  have h : ContinuousAt (exponentialCoordinates B W).symm 0 := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_strictDeriv B W).localInverse_continuousAt
  have hp : ContinuousAt (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B W) (T-1)) 1 :=
    (FiniteSlice.projection (derivations B W)).continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
  exact h.comp_of_eq hp (by simp)


theorem exponential_logarithm_eventually (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ∀ᶠ T in 𝓝 (1 : V →L[ℝ] V),
      FiniteSlice.projection (linearDefect B W).range (defect B W T) = 0 →
        exponential B W (logarithm B W T) = T := by
  have hp : ContinuousAt (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B W) (T-1)) 1 :=
    (FiniteSlice.projection (derivations B W)).continuous.continuousAt.comp
      (continuousAt_id.sub continuousAt_const)
  have hp₀ : Filter.Tendsto (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B W) (T-1)) (𝓝 1) (𝓝 0) := by
    simpa only [ContinuousAt, sub_self, map_zero] using! hp
  have hr : ∀ᶠ D in 𝓝 (0 : derivations B W),
      exponentialProjection B W ((exponentialCoordinates B W).symm D) = D := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_strictDeriv B W).eventually_right_inverse
  have hs : (ambientCoordinates B W).source ∈ 𝓝 (1 : V →L[ℝ] V) :=
    (ambientCoordinates B W).open_source.mem_nhds (ambientCoordinates_one_mem B W)
  have he : ContinuousAt (fun T => exponential B W (logarithm B W T)) 1 :=
    (exponential_smooth B W).continuous.continuousAt.comp (logarithm_continuousAt_one B W)
  have he₁ : Filter.Tendsto (fun T => exponential B W (logarithm B W T)) (𝓝 1) (𝓝 1) := by
    simpa only [ContinuousAt, logarithm_one, exponential_zero] using! he
  filter_upwards [hs, he₁ hs, hp₀ hr] with T hT hE hP
  intro hF
  apply (ambientCoordinates B W).injOn hE hT
  apply Prod.ext
  · change FiniteSlice.projection (linearDefect B W).range
      (defect B W (exponential B W (logarithm B W T))) = _
    rw [exponential_defect, map_zero]
    exact hF.symm
  · exact hP

theorem defect_zero_iff_projected_eventually (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ∀ᶠ T in 𝓝 (1 : V →L[ℝ] V), defect B W T = 0 ↔
      FiniteSlice.projection (linearDefect B W).range (defect B W T) = 0 := by
  filter_upwards [exponential_logarithm_eventually B W] with T hT
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    rw [← hT h]
    exact exponential_defect B W _


theorem logarithm_exponential_eventually (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ∀ᶠ D in 𝓝 (0 : derivations B W), logarithm B W (exponential B W D) = D :=
  (exponentialProjection_strictDeriv B W).eventually_left_inverse

theorem logarithm_smoothAt_one (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ContDiffAt ℝ ∞ (logarithm B W) 1 := by
  have hi : ContDiffAt ℝ ∞ (exponentialCoordinates B W).symm 0 := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_smooth B W).contDiffAt.to_localInverse
        (exponentialProjection_strictDeriv B W).hasFDerivAt (by simp)
  have hp : ContDiff ℝ ∞ (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B W) (T-1)) :=
    (FiniteSlice.projection (derivations B W)).contDiff.comp (contDiff_id.sub contDiff_const)
  have hi' : ContDiffAt ℝ ∞ (exponentialCoordinates B W).symm
      (FiniteSlice.projection (derivations B W) (1-1)) := by simpa using! hi
  exact hi'.comp (1 : V →L[ℝ] V) hp.contDiffAt

end BilinearStabilizer
end MathieuProperty
