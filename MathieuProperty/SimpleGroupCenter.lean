import MathieuProperty.DiscreteFibers
import MathieuProperty.NormedLieModel
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Topology.Covering.Quotient

/-! Finiteness of the center of a compact Lie group with simple Lie algebra.
The checked adjoint differential is injective, so its identity fiber is locally
isolated. Central elements belong to that fiber. The center is therefore
discrete, and closedness plus compactness makes it finite. This does not prove
finiteness of the fundamental group or construct a simply connected cover. -/

noncomputable section
open Set Filter
namespace MathieuProperty.SimpleGroupCenter
open scoped Manifold ContDiff Topology
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
local instance centerGroupNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ, E) G) :=
  groupLieAlgebraNormed
local instance centerGroupFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ, E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ, E) G)]

set_option backward.isDefEq.respectTransparency false in
/-- Simplicity makes infinitesimal conjugation injective. -/
theorem adjoint_derivative_injective :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (ConnectedLie.adjoint (E := E) (G := G)) 1) := by
  intro x y h
  apply LieModule.ext_of_isFaithful (R := ℝ) (L := GroupLieAlgebra 𝓘(ℝ, E) G)
    (GroupLieAlgebra 𝓘(ℝ, E) G)
  intro v
  have he := congrArg (fun T : E →L[ℝ] E => T v) h
  simpa only [ConnectedLie.adjoint_mfderiv] using he

include E in
/-- The identity is isolated among the central group elements. -/
theorem center_near_one : ∀ᶠ g in 𝓝 (1 : G), g ∈ Subgroup.center G → g = 1 := by
  have hloc := DiscreteFibers.fiber_isolated
    ((ConnectedLie.adjoint_smooth (E := E) (G := G)).mdifferentiableAt (by simp))
    (adjoint_derivative_injective (E := E) (G := G))
  filter_upwards [hloc] with g hg
  intro hgc
  apply hg
  have he : (fun x : G => g * x * g⁻¹) = id := by
    funext x
    rw [← Subgroup.mem_center_iff.mp hgc x, mul_assoc, mul_inv_cancel, mul_one]
    rfl
  change CompactAdjoint.adjointLinear g = CompactAdjoint.adjointLinear (1 : G)
  rw [CompactAdjoint.adjointLinear_one, CompactAdjoint.adjointLinear, he, mfderiv_id]

include E in
/-- Translation of the isolated identity makes the whole center discrete. -/
theorem center_discrete : DiscreteTopology (Subgroup.center G) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ, E) ∞
  apply discreteTopology_of_isOpen_singleton_one
  obtain ⟨s, hs, ho, h1⟩ := mem_nhds_iff.mp (center_near_one (E := E) (G := G))
  have he : Subtype.val ⁻¹' s = ({1} : Set (Subgroup.center G)) := by
    ext g
    constructor
    · intro hg
      exact Set.mem_singleton_iff.mpr (Subtype.ext (hs hg g.property))
    · intro hg
      rw [Set.mem_singleton_iff.mp hg]
      exact h1
  rw [← he]
  exact ho.preimage continuous_subtype_val

include E in
/-- Every compact Hausdorff Lie group with simple Lie algebra has finite center. -/
theorem center_finite [CompactSpace G] [T2Space G] : Finite (Subgroup.center G) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ, E) ∞
  have hc : IsClosed (Subgroup.center G : Set G) := by
    have he : (Subgroup.center G : Set G) = ⋂ x : G, {g : G | x * g = g * x} := by
      ext g
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_center_iff]
    rw [he]
    exact isClosed_iInter fun x => isClosed_eq (continuous_const.mul continuous_id)
      (continuous_id.mul continuous_const)
  let : CompactSpace (Subgroup.center G) := isCompact_iff_compactSpace.mp hc.isCompact
  let : DiscreteTopology (Subgroup.center G) := center_discrete (E := E)
  exact finite_of_compact_of_discrete

include E in
/-- The actual quotient by the center is a covering map; compactness is unnecessary here. -/
theorem center_quotient_covering :
    IsCoveringMap (QuotientGroup.mk : G → G ⧸ Subgroup.center G) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ, E) ∞
  have hd : IsDiscrete (Subgroup.center G : Set G) :=
    isDiscrete_iff_discreteTopology.mpr (center_discrete (E := E))
  exact ((Subgroup.center G).isQuotientCoveringMap hd).isCoveringMap

end MathieuProperty.SimpleGroupCenter
