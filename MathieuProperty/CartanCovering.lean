import MathieuProperty.CartanLift
import MathieuProperty.CoveringCharts

/-! Restrict the actual adjoint covering to the constructed Cartan component
and pull back its Lie-group charts to the subgroup preimage. -/

noncomputable section
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CartanLift
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [ConnectedSpace G]
local instance coverNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance coverFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [IsTopologicalGroup G]
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)] [T2Space G]

theorem adjoint_covering : IsCoveringMap (FullAdjoint.toAutomorphisms (E := E) (G := G)) := by
  apply isLocalHomeomorph_iff_isCoveringMap.mp
  exact (FullAdjoint.toAutomorphisms_range_open (E := E) (G := G)).isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
    (FullAdjoint.ontoImage_covering (E := E) (G := G)).isLocalHomeomorph

def toImage : preimage (E := E) (G := G) →* image (E := E) (G := G) :=
  { toFun := fun x => ⟨FullAdjoint.toAutomorphisms (E := E) (G := G) x.val, x.property⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun x y => Subtype.ext (map_mul _ x.val y.val) }

theorem toImage_covering : IsCoveringMap (toImage (E := E) (G := G)) :=
  (adjoint_covering (E := E) (G := G)).restrictPreimage (image (E := E) (G := G))

def imageEquiv : CartanStabilizer.Component (Cartan (E := E) (G := G)) ≃ₜ* image (E := E) (G := G) := by
  let : CompactSpace (CartanStabilizer.Component (Cartan (E := E) (G := G))) :=
    CartanStabilizer.component_compact _ (FullAdjoint.component_compact (E := E) (G := G))
  let f := CartanStabilizer.componentInclusion (Cartan (E := E) (G := G))
  have hi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun u : FullAdjoint.Target (E := E) (G := G) => u.val) h))
  let e : CartanStabilizer.Component (Cartan (E := E) (G := G)) ≃* image (E := E) (G := G) :=
    MulEquiv.ofBijective f.rangeRestrict ⟨fun x y h => hi (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hc : Continuous e := (CartanStabilizer.componentInclusion_continuous _).subtype_mk _
  exact { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

def toComponent : preimage (E := E) (G := G) →* CartanStabilizer.Component (Cartan (E := E) (G := G)) :=
  (imageEquiv (E := E) (G := G)).symm.toMonoidHom.comp (toImage (E := E) (G := G))

theorem toComponent_covering : IsCoveringMap (toComponent (E := E) (G := G)) :=
  (toImage_covering (E := E) (G := G)).homeomorph_comp (imageEquiv (E := E) (G := G)).symm.toHomeomorph

instance preimage_chartedSpace :
    ChartedSpace (CartanStabilizer.tangent (Cartan (E := E) (G := G))) (preimage (E := E) (G := G)) :=
  CoveringCharts.chartedSpace (toComponent (E := E) (G := G)) toComponent_covering.isLocalHomeomorph

instance preimage_lieGroup : LieGroup 𝓘(ℝ,CartanStabilizer.tangent (Cartan (E := E) (G := G))) ∞
    (preimage (E := E) (G := G)) :=
  CoveringCharts.lieGroup (toComponent (E := E) (G := G)) toComponent_covering.isLocalHomeomorph

instance preimage_locallyConnected : LocallyConnectedSpace (preimage (E := E) (G := G)) :=
  ChartedSpace.locallyConnectedSpace (CartanStabilizer.tangent (Cartan (E := E) (G := G))) _

def liftOpen : OpenSubgroup (preimage (E := E) (G := G)) :=
  ⟨Subgroup.connectedComponentOfOne _, isOpen_connectedComponent⟩

instance lift_chartedSpace :
    ChartedSpace (CartanStabilizer.tangent (Cartan (E := E) (G := G))) (Lift (E := E) (G := G)) :=
  OpenLieSubgroup.chartedSpace (liftOpen (E := E) (G := G))

instance lift_lieGroup : LieGroup 𝓘(ℝ,CartanStabilizer.tangent (Cartan (E := E) (G := G))) ∞
    (Lift (E := E) (G := G)) :=
  OpenLieSubgroup.lieGroup (E := CartanStabilizer.tangent (Cartan (E := E) (G := G))) (liftOpen (E := E) (G := G))

theorem lift_torus : Nonempty (Lift (E := E) (G := G) ≃ₜ* Torus (Module.finrank ℝ (Cartan (E := E) (G := G)))) := by
  rw [← CartanStabilizer.tangent_finrank (Cartan (E := E) (G := G))]
  exact CompactLieTorus.exists_torus_equiv (E := CartanStabilizer.tangent (Cartan (E := E) (G := G))) mul_comm

end MathieuProperty.CartanLift
