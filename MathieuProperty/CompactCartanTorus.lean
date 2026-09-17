import MathieuProperty.FullAdjoint
import MathieuProperty.StabilizerTorus

/-! A concrete torus in the automorphism group of the actual compact simple
 group Lie algebra. The Cartan is constructed from the group; compactness is
 supplied by its adjoint image. No torus or compactness input is assumed. The
 lift to a maximal torus in the original group is still a separate obligation. -/

noncomputable section
namespace MathieuProperty.CompactCartanTorus
open scoped Manifold ContDiff
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [ConnectedSpace G]
local instance tangentNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance tangentFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

abbrev Cartan := CompactAdjoint.realCartan (E := E) (G := G)
abbrev Component := CartanStabilizer.Component (Cartan (E := E) (G := G))

/-- The actual pointwise Cartan stabilizer component of the adjoint algebra is a torus. -/
theorem component_torus :
    Nonempty (Component (E := E) (G := G) ≃ₜ*
      Torus (Module.finrank ℝ (Cartan (E := E) (G := G)))) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  exact CartanStabilizer.component_torus_rank _ (FullAdjoint.component_compact (E := E) (G := G))

end MathieuProperty.CompactCartanTorus
