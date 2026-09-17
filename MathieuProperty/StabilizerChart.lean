import MathieuProperty.StabilizerParametrization
import MathieuProperty.BilinearStabilizer
import MathieuProperty.LocalInverseChart
/-! A local chart on the actual pointwise stabilizer group, modeled on derivations.
The inverse chart is exponentiation; its forward map is the ambient local logarithm. -/

noncomputable section
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace BilinearStabilizer
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def groupExponential (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (D : derivations B W) : group B W :=
  ⟨DerivationExponential.expUnit D.val, exp_mem_group B W D⟩

def groupLogarithm (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (u : group B W) : derivations B W := logarithm B W u.val.val

@[simp] theorem groupLogarithm_one (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : groupLogarithm B W 1 = 0 :=
  logarithm_one B W

theorem groupExponential_continuous (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : Continuous (groupExponential B W) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact (exponential_smooth B W).continuous
  · exact (exponential_smooth B W).continuous.comp continuous_neg

theorem groupExponential_logarithm_eventually (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ∀ᶠ u in 𝓝 (1 : group B W), groupExponential B W (groupLogarithm B W u) = u := by
  have hc : Continuous (fun u : group B W => u.val.val) := Units.continuous_val.comp continuous_subtype_val
  have ht : Filter.Tendsto (fun u : group B W => u.val.val) (𝓝 (1 : group B W)) (𝓝 (1 : V →L[ℝ] V)) := hc.continuousAt
  have h := ht (exponential_logarithm_eventually B W)
  filter_upwards [h] with u hu
  apply Subtype.ext
  apply Units.ext
  exact hu (by rw [group_defect, map_zero])

theorem groupLogarithm_exponential_eventually (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ∀ᶠ D in 𝓝 (0 : derivations B W), groupLogarithm B W (groupExponential B W D) = D :=
  logarithm_exponential_eventually B W

theorem exists_identity_chart (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ∃ e : OpenPartialHomeomorph (group B W) (derivations B W),
      (1 : group B W) ∈ e.source ∧ (e : group B W → derivations B W) = groupLogarithm B W ∧
        (e.symm : derivations B W → group B W) = groupExponential B W := by
  let p : group B W → derivations B W := fun u => FiniteSlice.projection (derivations B W) (u.val.val - 1)
  have hp : Continuous p :=
    (FiniteSlice.projection (derivations B W)).continuous.comp
      ((Units.continuous_val.comp continuous_subtype_val).sub continuous_const)
  let U := p ⁻¹' (exponentialCoordinates B W).target
  have h0 : (0 : derivations B W) ∈ (exponentialCoordinates B W).target := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_strictDeriv B W).image_mem_toOpenPartialHomeomorph_target
  have h1 : (1 : group B W) ∈ U := by
    change p 1 ∈ (exponentialCoordinates B W).target
    simpa only [p, Units.val_one, OneMemClass.coe_one, sub_self, map_zero] using h0
  have hU : U ∈ 𝓝 (1 : group B W) := ((exponentialCoordinates B W).open_target.preimage hp).mem_nhds h1
  have hf : ContinuousOn (groupLogarithm B W) U :=
    (exponentialCoordinates B W).symm.continuousOn.comp hp.continuousOn (fun _ hu => hu)
  apply LocalInverseChart.exists_of_eventually_inverse (groupLogarithm B W) (groupExponential B W) 1 U hU hf
    (groupExponential_continuous B W) (groupExponential_logarithm_eventually B W)
  simpa only [groupLogarithm_one] using groupLogarithm_exponential_eventually B W
end BilinearStabilizer
end MathieuProperty
