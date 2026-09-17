import MathieuProperty.BilinearStabilizer

/-! The pointwise stabilizer embeds as a closed subgroup of the automorphism group.
Compactness of the automorphism identity component therefore implies compactness
of the stabilizer identity component. -/

noncomputable section
open scoped Topology
namespace MathieuProperty.BilinearStabilizer
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V)

def inclusion : group B W →* BilinearAutomorphism.group B where
  toFun u := ⟨u.val, u.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem inclusion_continuous : Continuous (inclusion B W) :=
  continuous_subtype_val.subtype_mk _

theorem inclusion_closedEmbedding : Topology.IsClosedEmbedding (inclusion B W) := by
  have he : Topology.IsEmbedding (inclusion B W) :=
    Topology.IsEmbedding.of_comp (inclusion_continuous B W) continuous_subtype_val
      (show Topology.IsEmbedding (Subtype.val ∘ inclusion B W) from Topology.IsEmbedding.subtypeVal)
  refine ⟨he, ?_⟩
  have hr : Set.range (inclusion B W) =
      ⋂ w : W, {u : BilinearAutomorphism.group B | u.val.val w = w} := by
    ext u
    constructor
    · rintro ⟨v, rfl⟩
      exact Set.mem_iInter.mpr fun w => v.property.2 w
    · intro hu
      exact ⟨⟨u.val, u.property, fun w => Set.mem_iInter.mp hu w⟩, rfl⟩
  rw [hr]
  exact isClosed_iInter fun w => isClosed_eq
    ((Units.continuous_val.comp continuous_subtype_val).clm_apply continuous_const) continuous_const

theorem component_compact
    (hc : IsCompact (connectedComponent (1 : BilinearAutomorphism.group B))) :
    IsCompact (connectedComponent (1 : group B W)) := by
  apply ((inclusion_closedEmbedding B W).isCompact_preimage hc).of_isClosed_subset
    isClosed_connectedComponent
  intro u hu
  have hi := (inclusion_continuous B W).image_connectedComponent_subset (1 : group B W)
  exact hi ⟨u, hu, rfl⟩

end MathieuProperty.BilinearStabilizer
