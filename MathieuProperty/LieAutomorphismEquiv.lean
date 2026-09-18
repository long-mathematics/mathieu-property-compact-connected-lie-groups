import MathieuProperty.LieAutomorphism
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! Transport of the concrete automorphism topological group along a
finite-dimensional real Lie-algebra equivalence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.LieAutomorphism
variable {V W : Type*} [NormedRealLieAlgebra V] [NormedRealLieAlgebra W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

/-- Conjugation transports bracket-preserving invertible operators. -/
def congrHom (e : V ≃ₗ⁅ℝ⁆ W) : Group V →* Group W where
  toFun u := ⟨Units.map e.toLinearEquiv.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toMonoidHom u.val,by
    intro x y
    change e (u.val.val (e.symm ⁅x,y⁆)) = ⁅e (u.val.val (e.symm x)),e (u.val.val (e.symm y))⁆
    have hu : u.val.val ⁅e.symm x,e.symm y⁆ = ⁅u.val.val (e.symm x),u.val.val (e.symm y)⁆ :=
      u.property (e.symm x) (e.symm y)
    rw [e.symm.map_lie,hu,e.map_lie]⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' u v := by apply Subtype.ext; exact map_mul _ _ _

@[simp] theorem congrHom_apply (e : V ≃ₗ⁅ℝ⁆ W) (u : Group V) (x : W) :
    (congrHom e u).val.val x = e (u.val.val (e.symm x)) := rfl

theorem congrHom_symm_apply (e : V ≃ₗ⁅ℝ⁆ W) (u : Group V) :
    congrHom e.symm (congrHom e u) = u := by
  apply Subtype.ext
  apply Units.ext
  apply ContinuousLinearMap.ext
  intro x
  simp

theorem congrHom_continuous (e : V ≃ₗ⁅ℝ⁆ W) : Continuous (congrHom e) := by
  apply Continuous.subtype_mk
  exact (Units.continuous_map e.toLinearEquiv.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous).comp
    continuous_subtype_val

/-- Lie-algebra equivalence gives topological group equivalence of automorphisms. -/
def congr (e : V ≃ₗ⁅ℝ⁆ W) : Group V ≃ₜ* Group W :=
  { congrHom e with
    invFun := congrHom e.symm
    left_inv := congrHom_symm_apply e
    right_inv := congrHom_symm_apply e.symm
    continuous_toFun := congrHom_continuous e
    continuous_invFun := congrHom_continuous e.symm }

end MathieuProperty.LieAutomorphism
