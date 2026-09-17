import MathieuProperty.AutomorphismParametrization
import MathieuProperty.BilinearAutomorphism
import MathieuProperty.LocalInverseChart
/-! A local chart on the actual automorphism group, modeled on derivations.
The inverse chart is exponentiation; its forward map is the ambient local logarithm. -/

noncomputable section
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace BilinearAutomorphism
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def groupExponential (B : V →L[ℝ] V →L[ℝ] V) (D : derivations B) : group B :=
  ⟨DerivationExponential.expUnit D.val, exp_mem_group B D.val ((mem_derivations_iff B D.val).mp D.property)⟩

def groupLogarithm (B : V →L[ℝ] V →L[ℝ] V) (u : group B) : derivations B := logarithm B u.val.val

@[simp] theorem groupLogarithm_one (B : V →L[ℝ] V →L[ℝ] V) : groupLogarithm B 1 = 0 :=
  logarithm_one B

theorem groupExponential_continuous (B : V →L[ℝ] V →L[ℝ] V) : Continuous (groupExponential B) := by
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · exact (exponential_smooth B).continuous
  · exact (exponential_smooth B).continuous.comp continuous_neg

omit [FiniteDimensional ℝ V] in
theorem group_defect (B : V →L[ℝ] V →L[ℝ] V) (u : group B) : defect B u.val.val = 0 := by
  ext x y
  exact sub_eq_zero.mpr (u.property x y)

theorem groupExponential_logarithm_eventually (B : V →L[ℝ] V →L[ℝ] V) :
    ∀ᶠ u in 𝓝 (1 : group B), groupExponential B (groupLogarithm B u) = u := by
  have hc : Continuous (fun u : group B => u.val.val) := Units.continuous_val.comp continuous_subtype_val
  have ht : Filter.Tendsto (fun u : group B => u.val.val) (𝓝 (1 : group B)) (𝓝 (1 : V →L[ℝ] V)) := hc.continuousAt
  have h := ht (exponential_logarithm_eventually B)
  filter_upwards [h] with u hu
  apply Subtype.ext
  apply Units.ext
  exact hu (by rw [group_defect, map_zero])

theorem groupLogarithm_exponential_eventually (B : V →L[ℝ] V →L[ℝ] V) :
    ∀ᶠ D in 𝓝 (0 : derivations B), groupLogarithm B (groupExponential B D) = D :=
  logarithm_exponential_eventually B

theorem exists_identity_chart (B : V →L[ℝ] V →L[ℝ] V) :
    ∃ e : OpenPartialHomeomorph (group B) (derivations B),
      (1 : group B) ∈ e.source ∧ (e : group B → derivations B) = groupLogarithm B ∧
        (e.symm : derivations B → group B) = groupExponential B := by
  let p : group B → derivations B := fun u => FiniteSlice.projection (derivations B) (u.val.val - 1)
  have hp : Continuous p :=
    (FiniteSlice.projection (derivations B)).continuous.comp
      ((Units.continuous_val.comp continuous_subtype_val).sub continuous_const)
  let U := p ⁻¹' (exponentialCoordinates B).target
  have h0 : (0 : derivations B) ∈ (exponentialCoordinates B).target := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_strictDeriv B).image_mem_toOpenPartialHomeomorph_target
  have h1 : (1 : group B) ∈ U := by
    change p 1 ∈ (exponentialCoordinates B).target
    simpa only [p, Units.val_one, OneMemClass.coe_one, sub_self, map_zero] using h0
  have hU : U ∈ 𝓝 (1 : group B) := ((exponentialCoordinates B).open_target.preimage hp).mem_nhds h1
  have hf : ContinuousOn (groupLogarithm B) U :=
    (exponentialCoordinates B).symm.continuousOn.comp hp.continuousOn (fun _ hu => hu)
  apply LocalInverseChart.exists_of_eventually_inverse (groupLogarithm B) (groupExponential B) 1 U hU hf
    (groupExponential_continuous B) (groupExponential_logarithm_eventually B)
  simpa only [groupLogarithm_one] using groupLogarithm_exponential_eventually B
end BilinearAutomorphism
end MathieuProperty
