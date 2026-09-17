import Mathlib.Algebra.Lie.Killing
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Scalar extension of the Killing form.
Nondegeneracy is preserved because the Gram determinant is mapped by an
injective field homomorphism. This supplies complexification of the real
semisimple Lie algebras already constructed from compact Lie groups. -/

noncomputable section
open scoped TensorProduct
open Module
namespace MathieuProperty.KillingBaseChange
variable {K A L : Type*} [Field K] [Field A] [Algebra K A]
  [AddCommGroup L] [Module K L] [FiniteDimensional K L]

/-- Extending scalars along a field extension preserves nondegeneracy. -/
theorem bilinear_nondegenerate (B : LinearMap.BilinForm K L) (hB : B.Nondegenerate) :
    (B.baseChange A).Nondegenerate := by
  classical
  let b := Module.finBasis K L
  have hm : LinearMap.BilinForm.toMatrix (b.baseChange A) (B.baseChange A) =
      (LinearMap.BilinForm.toMatrix b B).map (algebraMap K A) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Algebra.algebraMap_eq_smul_one]
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange A), hm,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero (algebraMap K A)).mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB)

end MathieuProperty.KillingBaseChange

namespace MathieuProperty.KillingBaseChange
open LieAlgebra
variable {K A L : Type*} [Field K] [Field A] [Algebra K A]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]

/-- The Killing form of the extended Lie algebra is still nondegenerate. -/
instance isKilling : IsKilling A (A ⊗[K] L) where
  killingCompl_top_eq_bot := by
    have hb := bilinear_nondegenerate (A := A) (killingForm K L)
      (IsKilling.killingForm_nondegenerate K L)
    rw [← LieModule.traceForm_baseChange] at hb
    apply le_antisymm _ bot_le
    intro x hx
    have hx' := (LieIdeal.mem_killingCompl A (A ⊗[K] L) ⊤).mp hx
    have hz : x = 0 := hb.2 x (fun y => hx' y (LieSubmodule.mem_top y))
    simpa only [LieSubmodule.mem_bot] using hz

end MathieuProperty.KillingBaseChange
