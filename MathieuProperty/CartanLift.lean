import MathieuProperty.CompactCartanTorus
import MathieuProperty.CartanMaximal
import MathieuProperty.AdjointCovering
import MathieuProperty.DiscreteKernel

/-! The connected preimage of the constructed adjoint Cartan torus.
Its identity component is compact, connected, and abelian and embeds
continuously in the original group. CartanCovering and CartanLiftMaximal
provide its Lie-group structure, torus identification, and maximality. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CartanLift
open scoped Manifold ContDiff Topology
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [ConnectedSpace G]
local instance liftNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance liftFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [IsTopologicalGroup G]
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

abbrev Cartan := CompactCartanTorus.Cartan (E := E) (G := G)
def image : Subgroup (FullAdjoint.Target (E := E) (G := G)) :=
  CartanStabilizer.componentImage (Cartan (E := E) (G := G))
def preimage : Subgroup G := (image (E := E) (G := G)).comap (FullAdjoint.toAutomorphisms (E := E) (G := G))
abbrev Lift := Subgroup.connectedComponentOfOne (preimage (E := E) (G := G))

theorem image_compact : IsCompact (image (E := E) (G := G) : Set (FullAdjoint.Target (E := E) (G := G))) := by
  let : CompactSpace (CartanStabilizer.Component (Cartan (E := E) (G := G))) :=
    CartanStabilizer.component_compact _ (FullAdjoint.component_compact (E := E) (G := G))
  exact isCompact_range (CartanStabilizer.componentInclusion_continuous _)

instance preimage_compact : CompactSpace (preimage (E := E) (G := G)) := by
  apply isCompact_iff_compactSpace.mp
  exact ((image_compact (E := E) (G := G)).isClosed.preimage
    (FullAdjoint.toAutomorphisms_continuous (E := E) (G := G))).isCompact

instance lift_compact : CompactSpace (Lift (E := E) (G := G)) :=
  isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact

instance lift_connected : ConnectedSpace (Lift (E := E) (G := G)) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

def inclusion : Lift (E := E) (G := G) →* G :=
  (preimage (E := E) (G := G)).subtype.comp
    (Subgroup.connectedComponentOfOne (preimage (E := E) (G := G))).subtype

omit [CompactSpace G] [ConnectedSpace G]
  [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)] in
theorem inclusion_continuous : Continuous (inclusion (E := E) (G := G)) :=
  continuous_subtype_val.comp continuous_subtype_val

omit [CompactSpace G] [ConnectedSpace G]
  [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)] in
theorem inclusion_injective : Function.Injective (inclusion (E := E) (G := G)) := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

theorem mul_comm (x y : Lift (E := E) (G := G)) : x * y = y * x := by
  let : DiscreteTopology (FullAdjoint.toAutomorphisms (E := E) (G := G)).ker := by
    rw [FullAdjoint.ker_eq_center]
    exact SimpleGroupCenter.center_discrete (E := E)
  apply Subtype.ext
  apply Subtype.ext
  apply DiscreteKernel.commute_image (inclusion (E := E) (G := G)) inclusion_continuous
    (FullAdjoint.toAutomorphisms (E := E) (G := G)) _ x y
  intro u v
  exact CartanStabilizer.componentImage_mul_comm _ _ _ u.val.property v.val.property

end MathieuProperty.CartanLift
