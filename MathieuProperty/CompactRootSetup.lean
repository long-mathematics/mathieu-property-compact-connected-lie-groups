import MathieuProperty.CartanDifferential
import MathieuProperty.CompatibleRootData

/-! The manuscript's maximal-torus and root/weight setup for an actual compact
connected simple Lie group. The torus is smoothly included in the group; its
tangent image is the real Cartan used to construct the complex root system.
The highest-weight group representation and root subgroup integration remain
separate obligations. -/

noncomputable section
open scoped Manifold ContDiff TensorProduct
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CompactRootSetup
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [ConnectedSpace G]
local instance setupNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance setupFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [IsTopologicalGroup G]
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)] [T2Space G]

theorem real_mem_complexCartan_iff_tangent (x : GroupLieAlgebra 𝓘(ℝ,E) G) :
    (1 : ℂ) ⊗ₜ[ℝ] x ∈ CompactCartanRootData.complexCartan (E := E) (G := G) ↔
      x ∈ (CartanLift.tangentInclusion (E := E) (G := G)).range := by
  rw [CompactCartanRootData.real_mem_complexCartan]
  erw [CartanLift.tangentInclusion_range]
  rfl

/-- The maximal torus, its actual tangent Cartan, and the fundamental weight
normalization all belong to one compatible construction. -/
theorem maximal_torus_root_setup :
    Nonempty (CartanLift.Lift (E := E) (G := G) ≃ₜ*
      Torus (Module.finrank ℝ (CartanLift.Cartan (E := E) (G := G)))) ∧
    ContMDiff 𝓘(ℝ,CartanLift.Tangent (E := E) (G := G)) 𝓘(ℝ,E) ∞
      (CartanLift.inclusion (E := E) (G := G)) ∧
    Function.Injective (CartanLift.inclusion (E := E) (G := G)) ∧
    Function.Injective (CartanLift.tangentInclusion (E := E) (G := G)) ∧
    (CartanLift.tangentInclusion (E := E) (G := G)).range =
      (CartanLift.Cartan (E := E) (G := G)).toSubmodule ∧
    (∀ x : GroupLieAlgebra 𝓘(ℝ,E) G,
      (1 : ℂ) ⊗ₜ[ℝ] x ∈ CompactCartanRootData.complexCartan (E := E) (G := G) ↔
        x ∈ (CartanLift.tangentInclusion (E := E) (G := G)).range) ∧
    (∀ S : Subgroup G, ConnectedSpace S → (∀ x ∈ S, ∀ y ∈ S, x*y=y*x) →
      (CartanLift.inclusion (E := E) (G := G)).range ≤ S →
      S = (CartanLift.inclusion (E := E) (G := G)).range) ∧
    CompactCartanRootData.fundamentalWeight (E := E) (G := G)
      (LieAlgebra.IsKilling.coroot (CompactCartanRootData.simpleRoot (E := E) (G := G)).val.val) = 1 := by
  refine ⟨CartanLift.lift_torus, CartanLift.inclusion_smooth, CartanLift.inclusion_injective,
    CartanLift.tangentInclusion_injective, CartanLift.tangentInclusion_range,
    real_mem_complexCartan_iff_tangent, ?_, CompactCartanRootData.fundamentalWeight_pairing⟩
  intro S hconn hc hT
  let := hconn
  exact CartanLift.maximal_connected_abelian S hc hT

end MathieuProperty.CompactRootSetup
