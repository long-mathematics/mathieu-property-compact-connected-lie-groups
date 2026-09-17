import MathieuProperty.CartanStabilizer

/-! The tangent model of the Cartan stabilizer has the Cartan's dimension.
The adjoint map from an abelian Cartan is a linear equivalence onto derivations
vanishing on it, when the ambient Killing form is nondegenerate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CartanStabilizer
variable {V : Type*} [NormedRealLieAlgebra V] [FiniteDimensional ℝ V]
variable (H : LieSubalgebra ℝ V) [H.IsCartanSubalgebra] [IsLieAbelian H]

def fromCartan : H →ₗ[ℝ] tangent H where
  toFun x := ⟨LieAutomorphism.bracket x.val, by
    apply (BilinearStabilizer.mem_derivations_iff _ _ _).mpr
    constructor
    · apply (BilinearAutomorphism.mem_derivations_iff _ _).mpr
      intro y z
      exact leibniz_lie x.val y z
    · intro y
      exact congrArg Subtype.val (LieModule.IsTrivial.trivial x y)⟩
  map_add' x y := Subtype.ext (map_add LieAutomorphism.bracket x.val y.val)
  map_smul' t x := Subtype.ext (map_smul LieAutomorphism.bracket t x.val)

theorem fromCartan_bijective [LieAlgebra.IsKilling ℝ V] : Function.Bijective (fromCartan H) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (LieAutomorphism.innerDerivationEquiv (V := V)).injective
    ext v
    change -⁅v,x.val⁆ = -⁅v,y.val⁆
    rw [lie_skew x.val v, lie_skew y.val v]
    exact congrArg (fun D : tangent H => D.val v) h
  · intro D
    obtain ⟨x,hx⟩ := exists_inner H D
    exact ⟨x, Subtype.ext (ContinuousLinearMap.ext fun v => (hx v).symm)⟩

def tangentEquiv [LieAlgebra.IsKilling ℝ V] : H ≃ₗ[ℝ] tangent H :=
  LinearEquiv.ofBijective (fromCartan H) (fromCartan_bijective H)

theorem tangent_finrank [LieAlgebra.IsKilling ℝ V] :
    Module.finrank ℝ (tangent H) = Module.finrank ℝ H := (tangentEquiv H).finrank_eq.symm

end MathieuProperty.CartanStabilizer
