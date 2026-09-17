import Mathlib.Algebra.Lie.Abelian
import MathieuProperty.LieLocalCoordinates
import MathieuProperty.LieHomCalculus
/-! The differential of the adjoint action is the actual Lie bracket.
On a connected real Lie group, an abelian Lie algebra therefore forces the
adjoint action to be trivial. Uniqueness of smooth homomorphisms then shows
that every conjugation map is the identity, so the group is abelian. -/

noncomputable section
open scoped Manifold ContDiff
namespace MathieuProperty
namespace ConnectedLie
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
local instance : NormedAddCommGroup (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance : NormedSpace ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedSpace ℝ E)
local instance : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
/-- The adjoint action expressed on the fixed normed chart model. -/
def adjoint (g : G) : E →L[ℝ] E := CompactAdjoint.adjointLinear (E := E) g

set_option backward.isDefEq.respectTransparency false in
theorem adjoint_smooth : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞ (adjoint (E := E) (G := G)) := by
  exact CompactAdjoint.adjointLinear_contMDiff

set_option backward.isDefEq.respectTransparency false in
/-- Infinitesimal conjugation is the Lie bracket. -/
theorem adjoint_mfderiv [CompleteSpace E] (x v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E)
      (adjoint (E := E) (G := G)) 1 x) v = ⁅x,v⁆ := by
  have hd := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E →L[ℝ] E))
    (f := (LieLocalChart.chart (E := E) (G := G)).symm)
    (g := adjoint (E := E) (G := G))
    (LieLocalChart.origin (E := E) (G := G))
    ((adjoint_smooth (E := E) (G := G)).mdifferentiableAt (by simp))
    ((LieLocalChart.chart_symm_smooth (E := E) (G := G)).mdifferentiableAt (by simp))
  rw [LieLocalChart.chart_symm_mfderiv_origin, LieLocalChart.chart_symm_origin] at hd
  erw [ContinuousLinearMap.comp_id, mfderiv_eq_fderiv] at hd
  rw [← hd]
  exact LieLocalChart.adjointCoordinates_fderiv x v
set_option backward.isDefEq.respectTransparency false in
theorem adjoint_eq_id_of_abelian [CompleteSpace E] [PreconnectedSpace G]
    [IsLieAbelian (GroupLieAlgebra 𝓘(ℝ,E) G)] (g : G) :
    adjoint (E := E) g = ContinuousLinearMap.id ℝ E := by
  have h₀ : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) (adjoint (E := E) (G := G)) 1 = 0 := by
    ext x
    change (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E)
      (adjoint (E := E) (G := G)) 1 x) = 0
    ext v
    rw [adjoint_mfderiv]
    exact LieModule.IsTrivial.trivial (L := GroupLieAlgebra 𝓘(ℝ,E) G)
      (M := GroupLieAlgebra 𝓘(ℝ,E) G) x v
  have hz : ∀ g, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) (adjoint (E := E) (G := G)) g = 0 := by
    apply LieHomCalculus.mfderiv_zero_of_translate_relation _
      ((adjoint_smooth (E := E) (G := G)).mdifferentiable (by simp)) h₀
    intro k
    refine ⟨fun a : E →L[ℝ] E => (adjoint (E := E) k).comp a, ?_, ?_⟩
    · exact ((contDiff_const.clm_comp contDiff_id : ContDiff ℝ ∞
        (fun a : E →L[ℝ] E => (adjoint (E := E) k).comp a)).contMDiff).mdifferentiableAt (by simp)
    · funext x
      exact CompactAdjoint.adjointLinear_mul k x
  have hc := ManifoldZeroDerivative.eq_of_mfderiv_zero
    ((adjoint_smooth (E := E) (G := G)).mdifferentiable (by simp)) hz g 1
  exact hc.trans CompactAdjoint.adjointLinear_one

set_option backward.isDefEq.respectTransparency false in
/-- A connected real Lie group with abelian Lie algebra is abelian. -/
theorem mul_comm_of_lie_abelian [CompleteSpace E] [PreconnectedSpace G]
    [IsLieAbelian (GroupLieAlgebra 𝓘(ℝ,E) G)] (g h : G) : g*h = h*g := by
  let c : G →* G := (MulAut.conj g).toMonoidHom
  have hc : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c := CompactAdjoint.conjugation_contMDiff g
  have hd : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c 1 =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (MonoidHom.id G) 1 := by
    rw [show (MonoidHom.id G : G → G) = id from rfl, mfderiv_id]
    exact adjoint_eq_id_of_abelian (E := E) g
  have he := LieHomCalculus.hom_eq_of_mfderiv_eq c (MonoidHom.id G) hc contMDiff_id hd
  have hx := DFunLike.congr_fun he h
  change g*h*g⁻¹ = h at hx
  exact mul_inv_eq_iff_eq_mul.mp hx

end ConnectedLie
end MathieuProperty
