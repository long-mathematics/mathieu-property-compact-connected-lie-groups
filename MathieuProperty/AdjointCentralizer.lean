import Mathlib.Algebra.Lie.Abelian
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
/-! Commutation with a smooth operator family passes to its differential.
A Lie automorphism commuting with every adjoint operator of a centerless
Lie algebra is the identity. These lemmas are used to identify the center
of the compact restricted-adjoint image. -/

noncomputable section
open scoped Manifold ContDiff
namespace MathieuProperty
namespace AdjointCentralizer
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M]
set_option backward.isDefEq.respectTransparency false in
theorem commutes_mfderiv (A : M → V →L[ℝ] V) (U : V →L[ℝ] V) (a : M)
    (hA : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,V →L[ℝ] V) A a)
    (hc : ∀ g, U.comp (A g) = (A g).comp U)
    (x : E) (v : V) :
    U ((show V →L[ℝ] V from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V →L[ℝ] V) A a x) v) =
    (show V →L[ℝ] V from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V →L[ℝ] V) A a x) (U v) := by
  let l := ContinuousLinearMap.compL ℝ V V V U
  let r := (ContinuousLinearMap.compL ℝ V V V).flip U
  have hl : ContDiff ℝ 1 l := ContinuousLinearMap.contDiff _
  have hr : ContDiff ℝ 1 r := ContinuousLinearMap.contDiff _
  have he : l ∘ A = r ∘ A := funext hc
  have hd := congrArg (fun f : M → V →L[ℝ] V =>
    (show E →L[ℝ] (V →L[ℝ] V) from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V →L[ℝ] V) f a)) he
  rw [mfderiv_comp (I' := 𝓘(ℝ,V →L[ℝ] V)) _ (hl.contMDiff.mdifferentiableAt one_ne_zero) hA,
    mfderiv_comp (I' := 𝓘(ℝ,V →L[ℝ] V)) _ (hr.contMDiff.mdifferentiableAt one_ne_zero) hA] at hd
  erw [mfderiv_eq_fderiv, l.fderiv, mfderiv_eq_fderiv, r.fderiv] at hd
  exact congrArg (fun q : E →L[ℝ] (V →L[ℝ] V) => q x v) hd
end AdjointCentralizer
end MathieuProperty

namespace MathieuProperty
namespace AdjointCentralizer
variable {R V : Type*} [CommRing R] [LieRing V] [LieAlgebra R V]
theorem equiv_eq_refl (e : V ≃ₗ⁅R⁆ V) (hz : LieAlgebra.center R V = ⊥)
    (hc : ∀ x y : V, e ⁅x,y⁆ = ⁅x,e y⁆) : e = LieEquiv.refl := by
  apply DFunLike.ext
  intro x
  have hm : e x-x ∈ LieAlgebra.center R V := by
    apply (LieModule.mem_maxTrivSubmodule R V V _).mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    have h : ⁅e x,e z⁆ = ⁅x,e z⁆ := (e.map_lie x z).symm.trans (hc x z)
    change ⁅e z,e x-x⁆ = 0
    rw [← lie_skew, sub_lie, h, sub_self, neg_zero]
  rw [hz] at hm
  have he : e x-x = 0 := hm
  exact sub_eq_zero.mp he
end AdjointCentralizer
end MathieuProperty

