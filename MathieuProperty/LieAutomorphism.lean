import MathieuProperty.AutomorphismBracket
import MathieuProperty.NormedLieModel
import MathieuProperty.NonabelianCompactLie
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
/-! The Lie algebra of the actual automorphism group is the derivation algebra.
For a finite-dimensional Killing algebra, inner derivations identify it with the
original algebra; a simple real algebra therefore gives a simple group Lie algebra. -/

noncomputable section
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace LieAutomorphism
variable {V : Type*} [NormedRealLieAlgebra V] [FiniteDimensional ℝ V]
attribute [local instance 100] LieRing.ofAssociativeRing

def bracket : V →L[ℝ] V →L[ℝ] V := (LieAlgebra.ad ℝ V).toLinearMap.toContinuousBilinearMap

abbrev Group (V : Type*) [NormedRealLieAlgebra V] [FiniteDimensional ℝ V] :=
  BilinearAutomorphism.group (bracket (V := V))

abbrev Algebra (V : Type*) [NormedRealLieAlgebra V] [FiniteDimensional ℝ V] :=
  GroupLieAlgebra 𝓘(ℝ,BilinearAutomorphism.derivations (bracket (V := V))) (Group V)

def tangentDerivation (X : Algebra V) : LieDerivation ℝ V V where
  toLinearMap := (BilinearAutomorphism.tangentVal bracket X).toLinearMap
  leibniz' x y := by
    have h := (BilinearAutomorphism.mem_derivations_iff bracket
      (BilinearAutomorphism.tangentVal bracket X)).mp (show BilinearAutomorphism.derivations bracket from X).property x y
    change BilinearAutomorphism.tangentVal bracket X ⁅x,y⁆ = _ at h
    change BilinearAutomorphism.tangentVal bracket X ⁅x,y⁆ = _
    rw [h]
    change ⁅(BilinearAutomorphism.tangentVal bracket X) x,y⁆ +
      ⁅x,(BilinearAutomorphism.tangentVal bracket X) y⁆ = _
    rw [sub_eq_add_neg, lie_skew, add_comm]
    rfl


def derivationTangent (D : LieDerivation ℝ V V) : Algebra V :=
  (show BilinearAutomorphism.derivations bracket from
    ⟨D.toLinearMap.toContinuousLinearMap, by
      apply (BilinearAutomorphism.mem_derivations_iff bracket _).mpr
      intro x y
      change D ⁅x,y⁆ = ⁅D x,y⁆ + ⁅x,D y⁆
      simpa only [add_comm] using D.apply_lie_eq_add x y⟩)

def tangentLinearEquiv : Algebra V ≃ₗ[ℝ] LieDerivation ℝ V V where
  toFun := tangentDerivation
  invFun := derivationTangent
  left_inv X := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  right_inv D := by ext x; rfl
  map_add' X Y := by ext x; rfl
  map_smul' t X := by ext x; rfl

def tangentLieEquiv : Algebra V ≃ₗ⁅ℝ⁆ LieDerivation ℝ V V :=
  { tangentLinearEquiv with
    map_lie' := by
      intro X Y
      apply LieDerivation.ext
      intro v
      exact congrArg (fun T : V →L[ℝ] V => T v)
        (BilinearAutomorphism.tangentVal_lie bracket X Y) }



def innerDerivationEquiv [LieAlgebra.IsKilling ℝ V] : V ≃ₗ⁅ℝ⁆ LieDerivation ℝ V V :=
  LieEquiv.ofBijective (LieDerivation.ad ℝ V)
    ⟨LieDerivation.injective_ad_of_center_eq_bot (by simp),
      fun D => LieDerivation.IsKilling.exists_eq_ad D⟩

def algebraEquiv [LieAlgebra.IsKilling ℝ V] : Algebra V ≃ₗ⁅ℝ⁆ V :=
  tangentLieEquiv.trans innerDerivationEquiv.symm



theorem algebra_isSimple [LieAlgebra.IsSimple ℝ V] : LieAlgebra.IsSimple ℝ (Algebra V) :=
  CompactLieForm.isSimple_of_equiv (algebraEquiv (V := V)).symm

end LieAutomorphism
end MathieuProperty
