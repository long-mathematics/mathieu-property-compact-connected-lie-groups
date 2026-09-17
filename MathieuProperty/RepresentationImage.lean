import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Basic
/-! A finite-dimensional representation gives a concrete image subgroup of
invertible continuous endomorphisms. The quotient map onto this image is
continuous and surjective; compactness and connectedness pass from the source. -/

noncomputable section
namespace MathieuProperty
namespace RepresentationImage
variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
def unitHom (ρ : Representation ℝ G V) : G →* (V →L[ℝ] V)ˣ :=
  (Units.map (Module.End.toContinuousLinearMap V).toMonoidHom).comp ρ.asGroupHom

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem unitHom_val (ρ : Representation ℝ G V) (g : G) :
    (unitHom ρ g).val = LinearMap.toContinuousLinearMap (ρ g) := rfl

theorem unitHom_continuous (ρ : Representation ℝ G V)
    (hρ : Continuous (fun g => LinearMap.toContinuousLinearMap (ρ g))) : Continuous (unitHom ρ) := by
  apply Units.continuous_iff.mpr
  refine ⟨hρ,?_⟩
  have he : (fun g : G => ((unitHom ρ g)⁻¹).val) =
      (fun g : G => LinearMap.toContinuousLinearMap (ρ g⁻¹)) := by
    funext g
    rw [← map_inv]
    rfl
  rw [he]
  exact hρ.comp continuous_inv

def image (ρ : Representation ℝ G V) : Subgroup (V →L[ℝ] V)ˣ := (unitHom ρ).range

def ontoImage (ρ : Representation ℝ G V) : G →* image ρ := (unitHom ρ).rangeRestrict

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem ontoImage_surjective (ρ : Representation ℝ G V) : Function.Surjective (ontoImage ρ) :=
  (unitHom ρ).rangeRestrict_surjective

theorem ontoImage_continuous (ρ : Representation ℝ G V)
    (hρ : Continuous (fun g => LinearMap.toContinuousLinearMap (ρ g))) : Continuous (ontoImage ρ) :=
  (unitHom_continuous ρ hρ).subtype_mk _

theorem image_compact [CompactSpace G] (ρ : Representation ℝ G V)
    (hρ : Continuous (fun g => LinearMap.toContinuousLinearMap (ρ g))) : CompactSpace (image ρ) := by
  exact isCompact_iff_compactSpace.mp (isCompact_range (unitHom_continuous ρ hρ))

theorem image_connected [ConnectedSpace G] (ρ : Representation ℝ G V)
    (hρ : Continuous (fun g => LinearMap.toContinuousLinearMap (ρ g))) : ConnectedSpace (image ρ) := by
  exact (ontoImage_surjective ρ).connectedSpace (ontoImage_continuous ρ hρ)
end RepresentationImage
end MathieuProperty
