import MathieuProperty.AutomorphismChart
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
/-! An analytic manifold structure on bilinear automorphism groups.
Shrink the local logarithm chart to its analytic domain and translate by group multiplication. -/

noncomputable section
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace BilinearAutomorphism
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem defect_analytic (B : V →L[ℝ] V →L[ℝ] V) : ContDiff ℝ ω (defect B) := by
  unfold defect
  exact ((ContinuousLinearMap.compL ℝ V V V).contDiff.clm_comp contDiff_const).sub
    ((B.precompR V).flip.contDiff.clm_comp contDiff_id)

theorem exponential_analytic (B : V →L[ℝ] V →L[ℝ] V) : ContDiff ℝ ω (exponential B) := by
  have he : ContDiff ℝ ω (NormedSpace.exp : (V →L[ℝ] V) → V →L[ℝ] V) :=
    (show AnalyticOnNhd ℝ NormedSpace.exp Set.univ from fun x _ => NormedSpace.exp_analytic x).contDiff
  exact he.comp (derivations B).subtypeL.contDiff

theorem exponentialProjection_analytic (B : V →L[ℝ] V →L[ℝ] V) :
    ContDiff ℝ ω (exponentialProjection B) :=
  (FiniteSlice.projection (derivations B)).contDiff.comp ((exponential_analytic B).sub contDiff_const)

theorem logarithm_analyticAt_one (B : V →L[ℝ] V →L[ℝ] V) :
    ContDiffAt ℝ ω (logarithm B) 1 := by
  have hi : ContDiffAt ℝ ω (exponentialCoordinates B).symm 0 := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_analytic B).contDiffAt.to_localInverse
        (exponentialProjection_strictDeriv B).hasFDerivAt (by simp)
  have hp : ContDiff ℝ ω (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B) (T-1)) :=
    (FiniteSlice.projection (derivations B)).contDiff.comp (contDiff_id.sub contDiff_const)
  have hi' : ContDiffAt ℝ ω (exponentialCoordinates B).symm
      (FiniteSlice.projection (derivations B) (1-1)) := by simpa using! hi
  exact hi'.comp (1 : V →L[ℝ] V) hp.contDiffAt

theorem exists_analytic_identity_chart (B : V →L[ℝ] V →L[ℝ] V) :
    ∃ e : OpenPartialHomeomorph (group B) (derivations B),
      (1 : group B) ∈ e.source ∧ (e : group B → derivations B) = groupLogarithm B ∧
        (e.symm : derivations B → group B) = groupExponential B ∧
        ∀ u ∈ e.source, ContDiffAt ℝ ω (logarithm B) u.val.val := by
  obtain ⟨e, he, hf, hg⟩ := exists_identity_chart B
  have ha := (logarithm_analyticAt_one B).eventually (by simp)
  obtain ⟨W, hW, hWo, h1W⟩ := mem_nhds_iff.mp ha
  have hc : Continuous (fun u : group B => u.val.val) := Units.continuous_val.comp continuous_subtype_val
  let e' := e.restrOpen ((fun u : group B => u.val.val) ⁻¹' W) (hWo.preimage hc)
  refine ⟨e', ⟨he, h1W⟩, hf, hg, ?_⟩
  intro u hu
  exact hW hu.2

def identityChart (B : V →L[ℝ] V →L[ℝ] V) :
    OpenPartialHomeomorph (group B) (derivations B) :=
  Classical.choose (exists_analytic_identity_chart B)

theorem identityChart_one_mem (B : V →L[ℝ] V →L[ℝ] V) :
    (1 : group B) ∈ (identityChart B).source :=
  (Classical.choose_spec (exists_analytic_identity_chart B)).1

theorem identityChart_apply (B : V →L[ℝ] V →L[ℝ] V) (u : group B) :
    identityChart B u = groupLogarithm B u :=
  congrFun (Classical.choose_spec (exists_analytic_identity_chart B)).2.1 u

theorem identityChart_symm_apply (B : V →L[ℝ] V →L[ℝ] V) (D : derivations B) :
    (identityChart B).symm D = groupExponential B D :=
  congrFun (Classical.choose_spec (exists_analytic_identity_chart B)).2.2.1 D

theorem identityChart_analytic (B : V →L[ℝ] V →L[ℝ] V) (u : group B)
    (hu : u ∈ (identityChart B).source) : ContDiffAt ℝ ω (logarithm B) u.val.val :=
  (Classical.choose_spec (exists_analytic_identity_chart B)).2.2.2 u hu

def translatedChart (B : V →L[ℝ] V →L[ℝ] V) (g : group B) :
    OpenPartialHomeomorph (group B) (derivations B) :=
  (Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph.trans (identityChart B)

theorem translatedChart_apply (B : V →L[ℝ] V →L[ℝ] V) (g u : group B) :
    translatedChart B g u = groupLogarithm B (g⁻¹ * u) :=
  identityChart_apply B _

theorem translatedChart_symm_apply (B : V →L[ℝ] V →L[ℝ] V) (g : group B) (D : derivations B) :
    (translatedChart B g).symm D = g * groupExponential B D := by
  change g⁻¹⁻¹ * (identityChart B).symm D = _
  rw [inv_inv, identityChart_symm_apply]

theorem mem_translatedChart_source (B : V →L[ℝ] V →L[ℝ] V) (g u : group B) :
    u ∈ (translatedChart B g).source ↔ g⁻¹*u ∈ (identityChart B).source := by
  change (u ∈ Set.univ ∧ g⁻¹*u ∈ (identityChart B).source) ↔ _
  simp only [Set.mem_univ, true_and]

instance chartedSpace (B : V →L[ℝ] V →L[ℝ] V) : ChartedSpace (derivations B) (group B) where
  atlas := Set.range (translatedChart B)
  chartAt := translatedChart B
  mem_chart_source g := by
    rw [mem_translatedChart_source, inv_mul_cancel]
    exact identityChart_one_mem B
  chart_mem_atlas g := ⟨g,rfl⟩

instance isManifold (B : V →L[ℝ] V →L[ℝ] V) : IsManifold 𝓘(ℝ,derivations B) ω (group B) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨g, rfl⟩ ⟨h, rfl⟩ D hD
  have hu : h⁻¹ * (g * groupExponential B D) ∈ (identityChart B).source := by
    apply (mem_translatedChart_source B h _).mp
    have hx := hD.1.2
    change (translatedChart B g).symm D ∈ (translatedChart B h).source at hx
    simpa only [translatedChart_symm_apply] using hx
  have hl := identityChart_analytic B _ hu
  have hm : ContDiff ℝ ω (fun D : derivations B => h.val.inv * (g.val.val * exponential B D)) :=
    contDiff_const.mul (contDiff_const.mul (exponential_analytic B))
  have hc := hl.comp D hm.contDiffAt
  simpa only [Function.comp_def, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_eq,
    OpenPartialHomeomorph.trans_apply, translatedChart_apply, translatedChart_symm_apply,
    groupLogarithm, groupExponential, DerivationExponential.expUnit, exponential] using! hc.contDiffWithinAt


end BilinearAutomorphism
end MathieuProperty
