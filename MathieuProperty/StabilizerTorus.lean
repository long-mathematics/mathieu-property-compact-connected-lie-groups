import MathieuProperty.StabilizerCompact
import MathieuProperty.CartanTangent
import MathieuProperty.AbelianTorus
import MathieuProperty.OpenLieSubgroup

/-! The pointwise Cartan stabilizer component is a torus when the ambient
 automorphism identity component is compact. Its open-subgroup charts give the
 Lie structure, and the already proved compact abelian classification applies. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace MathieuProperty.CartanStabilizer
open scoped Manifold ContDiff
variable {V : Type*} [NormedRealLieAlgebra V] [FiniteDimensional ℝ V]
variable (H : LieSubalgebra ℝ V) [H.IsCartanSubalgebra] [IsLieAbelian H]

local instance stabilizer_smooth : LieGroup 𝓘(ℝ,tangent H) ∞ (Group H) :=
  LieGroup.of_le (show (∞ : ℕ∞ω) ≤ ω by simp)

def componentOpen : OpenSubgroup (Group H) := by
  let : LocallyConnectedSpace (Group H) := ChartedSpace.locallyConnectedSpace (tangent H) (Group H)
  exact ⟨Subgroup.connectedComponentOfOne (Group H), isOpen_connectedComponent⟩

abbrev Component := ↥(componentOpen H)

instance component_lieGroup : LieGroup 𝓘(ℝ,tangent H) ∞ (Component H) :=
  OpenLieSubgroup.lieGroup (E := tangent H) (componentOpen H)

instance component_connected : ConnectedSpace (Component H) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

omit [H.IsCartanSubalgebra] [IsLieAbelian H] in
theorem component_compact
    (hc : IsCompact (connectedComponent (1 : LieAutomorphism.Group V))) :
    CompactSpace (Component H) :=
  isCompact_iff_compactSpace.mp (BilinearStabilizer.component_compact _ H.toSubmodule hc)

theorem component_torus [LieAlgebra.IsKilling ℝ V]
    (hc : IsCompact (connectedComponent (1 : LieAutomorphism.Group V))) :
    Nonempty (Component H ≃ₜ* Torus (Module.finrank ℝ (tangent H))) := by
  let : CompactSpace (Component H) := component_compact H hc
  apply CompactLieTorus.exists_torus_equiv (E := tangent H)
  intro x y
  exact Subtype.ext (identity_component_commute H x.property y.property)


theorem component_torus_rank [LieAlgebra.IsKilling ℝ V]
    (hc : IsCompact (connectedComponent (1 : LieAutomorphism.Group V))) :
    Nonempty (Component H ≃ₜ* Torus (Module.finrank ℝ H)) := by
  rw [← tangent_finrank H]
  exact component_torus H hc

end MathieuProperty.CartanStabilizer
