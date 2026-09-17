import MathieuProperty.ComplexRootData
import Mathlib.LinearAlgebra.Complex.Module

/-! Real and imaginary projections identify the complex scalar extension of
a real Lie subalgebra. An abelian real Cartan remains a Cartan after this
extension: normalizer membership descends to both real components. -/

noncomputable section
open scoped TensorProduct
namespace MathieuProperty.ComplexParts
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

def re : ℂ ⊗[ℝ] L →ₗ[ℝ] L :=
  TensorProduct.lift (Complex.reLm.smulRight (LinearMap.id : L →ₗ[ℝ] L))
def im : ℂ ⊗[ℝ] L →ₗ[ℝ] L :=
  TensorProduct.lift (Complex.imLm.smulRight (LinearMap.id : L →ₗ[ℝ] L))

@[simp] theorem re_tmul (z : ℂ) (x : L) : re (z ⊗ₜ[ℝ] x) = z.re • x := rfl
@[simp] theorem im_tmul (z : ℂ) (x : L) : im (z ⊗ₜ[ℝ] x) = z.im • x := rfl

theorem decomposition (x : ℂ ⊗[ℝ] L) : x = (1 : ℂ) ⊗ₜ[ℝ] re x + Complex.I ⊗ₜ[ℝ] im x := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    rw [re_tmul, im_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
    congr 1
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add]
    rw [← add_add_add_comm, ← hx, ← hy]

theorem re_lie_real (x : ℂ ⊗[ℝ] L) (y : L) : re ⁅x, (1 : ℂ) ⊗ₜ[ℝ] y⁆ = ⁅re x,y⁆ := by
  induction x using TensorProduct.inductionOn with
  | tmul z x => simp [smul_lie]
  | add x z hx hz => simp [add_lie,hx,hz]

theorem im_lie_real (x : ℂ ⊗[ℝ] L) (y : L) : im ⁅x, (1 : ℂ) ⊗ₜ[ℝ] y⁆ = ⁅im x,y⁆ := by
  induction x using TensorProduct.inductionOn with
  | tmul z x => simp [smul_lie]
  | add x z hx hz => simp [add_lie,hx,hz]

theorem re_smul (z : ℂ) (x : ℂ ⊗[ℝ] L) :
    re (z • x) = z.re • re x - z.im • im x := by
  induction x using TensorProduct.inductionOn with
  | tmul w x => simp [TensorProduct.smul_tmul', Complex.mul_re, sub_smul, mul_smul]
  | add x y hx hy => simp [smul_add, hx,hy]; abel

theorem im_smul (z : ℂ) (x : ℂ ⊗[ℝ] L) :
    im (z • x) = z.re • im x + z.im • re x := by
  induction x using TensorProduct.inductionOn with
  | tmul w x => simp [TensorProduct.smul_tmul', Complex.mul_im, add_smul, mul_smul]
  | add x y hx hy => simp [smul_add, hx,hy]; abel

theorem re_lie (x y : ℂ ⊗[ℝ] L) :
    re ⁅x,y⁆ = ⁅re x,re y⁆ - ⁅im x,im y⁆ := by
  conv_lhs => rw [decomposition x, decomposition y]
  simp [add_lie,lie_add,sub_eq_add_neg]

theorem im_lie (x y : ℂ ⊗[ℝ] L) :
    im ⁅x,y⁆ = ⁅re x,im y⁆ + ⁅im x,re y⁆ := by
  conv_lhs => rw [decomposition x, decomposition y]
  simp [add_lie,lie_add]

def subalgebra (H : LieSubalgebra ℝ L) : LieSubalgebra ℂ (ℂ ⊗[ℝ] L) where
  carrier := {x | re x ∈ H ∧ im x ∈ H}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨by simpa using H.add_mem hx.1 hy.1, by simpa using H.add_mem hx.2 hy.2⟩
  smul_mem' := by
    intro z x hx
    exact ⟨by rw [re_smul]; exact H.sub_mem (H.smul_mem z.re hx.1) (H.smul_mem z.im hx.2),
      by rw [im_smul]; exact H.add_mem (H.smul_mem z.re hx.2) (H.smul_mem z.im hx.1)⟩
  lie_mem' := by
    intro x y hx hy
    exact ⟨by rw [re_lie]; exact H.sub_mem (H.lie_mem hx.1 hy.1) (H.lie_mem hx.2 hy.2),
      by rw [im_lie]; exact H.add_mem (H.lie_mem hx.1 hy.2) (H.lie_mem hx.2 hy.1)⟩

@[simp] theorem mem_subalgebra (H : LieSubalgebra ℝ L) (x : ℂ ⊗[ℝ] L) :
    x ∈ subalgebra H ↔ re x ∈ H ∧ im x ∈ H := Iff.rfl

@[simp] theorem real_mem_subalgebra (H : LieSubalgebra ℝ L) (x : L) :
    (1 : ℂ) ⊗ₜ[ℝ] x ∈ subalgebra H ↔ x ∈ H := by simp

theorem normalizer_eq (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] :
    (subalgebra H).normalizer = subalgebra H := by
  apply le_antisymm _ (subalgebra H).le_normalizer
  intro x hx
  have hn (y : L) (hy : y ∈ H) :=
    ((subalgebra H).mem_normalizer_iff x).mp hx ((1 : ℂ) ⊗ₜ[ℝ] y)
      ((real_mem_subalgebra H y).mpr hy)
  have hr : re x ∈ H.normalizer := (H.mem_normalizer_iff _).mpr fun y hy => by
    have h := (hn y hy).1
    rwa [re_lie_real] at h
  have hi : im x ∈ H.normalizer := (H.mem_normalizer_iff _).mpr fun y hy => by
    have h := (hn y hy).2
    rwa [im_lie_real] at h
  rw [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at hr hi
  exact ⟨hr,hi⟩

instance subalgebra_abelian (H : LieSubalgebra ℝ L) [IsLieAbelian H] : IsLieAbelian (subalgebra H) := by
  constructor
  intro x y
  apply Subtype.ext
  have hzero (a b : L) (ha : a ∈ H) (hb : b ∈ H) : ⁅a,b⁆ = 0 := by
    exact congrArg Subtype.val (LieModule.IsTrivial.trivial (⟨a,ha⟩ : H) ⟨b,hb⟩)
  have hr : re ⁅x.val,y.val⁆ = 0 := by
    rw [re_lie, hzero _ _ x.property.1 y.property.1, hzero _ _ x.property.2 y.property.2, sub_self]
  have hi : im ⁅x.val,y.val⁆ = 0 := by
    rw [im_lie, hzero _ _ x.property.1 y.property.2, hzero _ _ x.property.2 y.property.1, add_zero]
  have hd := decomposition ⁅x.val,y.val⁆
  simpa only [hr,hi,TensorProduct.tmul_zero,add_zero] using! hd

instance subalgebra_cartan (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] [IsLieAbelian H] :
    (subalgebra H).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := normalizer_eq H

theorem subalgebra_eq_baseChange (H : LieSubalgebra ℝ L) :
    (subalgebra H).toSubmodule = H.toSubmodule.baseChange ℂ := by
  apply le_antisymm
  · intro x hx
    rw [decomposition x]
    exact (H.toSubmodule.baseChange ℂ).add_mem
      (H.toSubmodule.tmul_mem_baseChange_of_mem 1 hx.1)
      (H.toSubmodule.tmul_mem_baseChange_of_mem Complex.I hx.2)
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y,hy,rfl⟩
    exact (real_mem_subalgebra H y).mpr hy

end MathieuProperty.ComplexParts
