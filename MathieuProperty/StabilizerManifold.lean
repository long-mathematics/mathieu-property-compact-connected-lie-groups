import MathieuProperty.StabilizerChart
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
/-! An analytic manifold structure on pointwise bilinear stabilizer groups.
Shrink the local logarithm chart to its analytic domain and translate by group multiplication. -/

noncomputable section
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace BilinearStabilizer
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exponential_analytic (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : ContDiff ℝ ω (exponential B W) := by
  have he : ContDiff ℝ ω (NormedSpace.exp : (V →L[ℝ] V) → V →L[ℝ] V) :=
    (show AnalyticOnNhd ℝ NormedSpace.exp Set.univ from fun x _ => NormedSpace.exp_analytic x).contDiff
  exact he.comp (derivations B W).subtypeL.contDiff

theorem exponentialProjection_analytic (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ContDiff ℝ ω (exponentialProjection B W) :=
  (FiniteSlice.projection (derivations B W)).contDiff.comp ((exponential_analytic B W).sub contDiff_const)

theorem logarithm_analyticAt_one (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ContDiffAt ℝ ω (logarithm B W) 1 := by
  have hi : ContDiffAt ℝ ω (exponentialCoordinates B W).symm 0 := by
    simpa only [exponentialProjection_zero] using!
      (exponentialProjection_analytic B W).contDiffAt.to_localInverse
        (exponentialProjection_strictDeriv B W).hasFDerivAt (by simp)
  have hp : ContDiff ℝ ω (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B W) (T-1)) :=
    (FiniteSlice.projection (derivations B W)).contDiff.comp (contDiff_id.sub contDiff_const)
  have hi' : ContDiffAt ℝ ω (exponentialCoordinates B W).symm
      (FiniteSlice.projection (derivations B W) (1-1)) := by simpa using! hi
  exact hi'.comp (1 : V →L[ℝ] V) hp.contDiffAt

theorem exists_analytic_identity_chart (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ∃ e : OpenPartialHomeomorph (group B W) (derivations B W),
      (1 : group B W) ∈ e.source ∧ (e : group B W → derivations B W) = groupLogarithm B W ∧
        (e.symm : derivations B W → group B W) = groupExponential B W ∧
        ∀ u ∈ e.source, ContDiffAt ℝ ω (logarithm B W) u.val.val := by
  obtain ⟨e, he, hf, hg⟩ := exists_identity_chart B W
  have ha := (logarithm_analyticAt_one B W).eventually (by simp)
  obtain ⟨U, hW, hWo, h1W⟩ := mem_nhds_iff.mp ha
  have hc : Continuous (fun u : group B W => u.val.val) := Units.continuous_val.comp continuous_subtype_val
  let e' := e.restrOpen ((fun u : group B W => u.val.val) ⁻¹' U) (hWo.preimage hc)
  refine ⟨e', ⟨he, h1W⟩, hf, hg, ?_⟩
  intro u hu
  exact hW hu.2

def identityChart (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    OpenPartialHomeomorph (group B W) (derivations B W) :=
  Classical.choose (exists_analytic_identity_chart B W)

theorem identityChart_one_mem (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    (1 : group B W) ∈ (identityChart B W).source :=
  (Classical.choose_spec (exists_analytic_identity_chart B W)).1

theorem identityChart_apply (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (u : group B W) :
    identityChart B W u = groupLogarithm B W u :=
  congrFun (Classical.choose_spec (exists_analytic_identity_chart B W)).2.1 u

theorem identityChart_symm_apply (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (D : derivations B W) :
    (identityChart B W).symm D = groupExponential B W D :=
  congrFun (Classical.choose_spec (exists_analytic_identity_chart B W)).2.2.1 D

theorem identityChart_analytic (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (u : group B W)
    (hu : u ∈ (identityChart B W).source) : ContDiffAt ℝ ω (logarithm B W) u.val.val :=
  (Classical.choose_spec (exists_analytic_identity_chart B W)).2.2.2 u hu

def translatedChart (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (g : group B W) :
    OpenPartialHomeomorph (group B W) (derivations B W) :=
  (Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph.trans (identityChart B W)

theorem translatedChart_apply (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (g u : group B W) :
    translatedChart B W g u = groupLogarithm B W (g⁻¹ * u) :=
  identityChart_apply B W _

theorem translatedChart_symm_apply (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (g : group B W) (D : derivations B W) :
    (translatedChart B W g).symm D = g * groupExponential B W D := by
  change g⁻¹⁻¹ * (identityChart B W).symm D = _
  rw [inv_inv, identityChart_symm_apply]

theorem mem_translatedChart_source (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (g u : group B W) :
    u ∈ (translatedChart B W g).source ↔ g⁻¹*u ∈ (identityChart B W).source := by
  change (u ∈ Set.univ ∧ g⁻¹*u ∈ (identityChart B W).source) ↔ _
  simp only [Set.mem_univ, true_and]

instance chartedSpace (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : ChartedSpace (derivations B W) (group B W) where
  atlas := Set.range (translatedChart B W)
  chartAt := translatedChart B W
  mem_chart_source g := by
    rw [mem_translatedChart_source, inv_mul_cancel]
    exact identityChart_one_mem B W
  chart_mem_atlas g := ⟨g,rfl⟩

instance isManifold (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : IsManifold 𝓘(ℝ,derivations B W) ω (group B W) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨g, rfl⟩ ⟨h, rfl⟩ D hD
  have hu : h⁻¹ * (g * groupExponential B W D) ∈ (identityChart B W).source := by
    apply (mem_translatedChart_source B W h _).mp
    have hx := hD.1.2
    change (translatedChart B W g).symm D ∈ (translatedChart B W h).source at hx
    simpa only [translatedChart_symm_apply] using hx
  have hl := identityChart_analytic B W _ hu
  have hm : ContDiff ℝ ω (fun D : derivations B W => h.val.inv * (g.val.val * exponential B W D)) :=
    contDiff_const.mul (contDiff_const.mul (exponential_analytic B W))
  have hc := hl.comp D hm.contDiffAt
  simpa only [Function.comp_def, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_eq,
    OpenPartialHomeomorph.trans_apply, translatedChart_apply, translatedChart_symm_apply,
    groupLogarithm, groupExponential, DerivationExponential.expUnit, exponential] using! hc.contDiffWithinAt


end BilinearStabilizer
end MathieuProperty
