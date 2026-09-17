import MathieuProperty.ConnectedLie
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
/-! Restricting the adjoint action through a linear projection preserves
smoothness. Its differential is the projected actual Lie bracket. The compact
application constructs the projection from an orthogonal ideal complement. -/

noncomputable section
open scoped Manifold ContDiff
namespace MathieuProperty
namespace RestrictedAdjoint
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
local instance projectedAdjointSmoothness : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
variable (J : Submodule ℝ E) (p : E →L[ℝ] J)
def restrictionMap : (E →L[ℝ] E) →L[ℝ] (J →L[ℝ] J) :=
  (ContinuousLinearMap.compL ℝ J E J p).comp
    ((ContinuousLinearMap.compL ℝ J E E).flip J.subtypeL)
def projectedAdjoint (g : G) : J →L[ℝ] J :=
  restrictionMap J p (ConnectedLie.adjoint (E := E) g)

set_option backward.isDefEq.respectTransparency false in
theorem projectedAdjoint_smooth : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,J →L[ℝ] J) ∞
    (projectedAdjoint (G := G) J p) := by
  change ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,J →L[ℝ] J) ∞
    ((restrictionMap J p) ∘ ConnectedLie.adjoint (E := E) (G := G))
  have hT : ContDiff ℝ ∞ (restrictionMap J p) := ContinuousLinearMap.contDiff _
  exact hT.contMDiff.comp (ConnectedLie.adjoint_smooth (E := E) (G := G))

set_option backward.isDefEq.respectTransparency false in
theorem projectedAdjoint_mfderiv [CompleteSpace E] (x : GroupLieAlgebra 𝓘(ℝ,E) G) (v : J) :
    (show J →L[ℝ] J from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,J →L[ℝ] J)
      (projectedAdjoint (G := G) J p) 1 x) v = p (@Bracket.bracket (GroupLieAlgebra 𝓘(ℝ,E) G) (GroupLieAlgebra 𝓘(ℝ,E) G) _ x v.val) := by
  have hT : ContDiff ℝ ∞ (restrictionMap J p) := ContinuousLinearMap.contDiff _
  have hd := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E →L[ℝ] E))
    (I'' := 𝓘(ℝ,J →L[ℝ] J)) (f := ConnectedLie.adjoint (E := E) (G := G))
    (g := restrictionMap J p) (1 : G)
    (hT.contMDiff.mdifferentiableAt (by simp))
    (ConnectedLie.adjoint_smooth.mdifferentiableAt (by simp))
  erw [mfderiv_eq_fderiv, (restrictionMap J p).fderiv] at hd
  have hv := congrArg (fun q : E →L[ℝ] (J →L[ℝ] J) => q x v) hd
  change (show J →L[ℝ] J from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,J →L[ℝ] J)
      (projectedAdjoint (G := G) J p) 1 x) v =
    p ((show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E)
      (ConnectedLie.adjoint (E := E) (G := G)) 1 x) v.val) at hv
  rw [ConnectedLie.adjoint_mfderiv] at hv
  exact hv
end RestrictedAdjoint
end MathieuProperty
