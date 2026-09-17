import MathieuProperty.CompactRootReality
import Mathlib.Algebra.Lie.Weights.IsSimple

/-! Ideals of the complexified compact real algebra are stable under real-form
conjugation. Descent of ideals then transfers real simplicity to complex
simplicity, without a classification of complex simple Lie algebras. -/
noncomputable section
open scoped TensorProduct
namespace MathieuProperty.CompactRootReality
open ComplexParts LieAlgebra LieAlgebra.IsKilling LieModule
set_option backward.isDefEq.respectTransparency false
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (B : LinearMap.BilinForm ℝ L) (hB : B.IsSymm)
  (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) (hinv : B.lieInvariant L)
variable [FiniteDimensional ℝ L] [IsKilling ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] [IsLieAbelian H]

include B hB hpos hinv in
/-- Each root sl₂ subspace is stable under compact-real conjugation. -/
theorem conj_mem_root_sl2 (α : Weight ℂ (subalgebra H) (ℂ ⊗[ℝ] L)) (hα : α.IsNonZero)
    {x : ℂ ⊗[ℝ] L} (hx : x ∈ sl2SubmoduleOfRoot hα) :
    conj x ∈ sl2SubmoduleOfRoot hα := by
  obtain ⟨h,e,f,t,hh,he,hf,hcon⟩ := exists_normalized_root_triple B hB hpos hinv H α hα
  have hce : conj e = -f := by rw [hcon, neg_neg]
  have hcf : conj f = -e := by simp [hcon]
  change x ∈ sl2SubalgebraOfRoot hα at hx
  obtain ⟨a,b,c,rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα t he hf).mp hx
  change _ ∈ sl2SubalgebraOfRoot hα
  apply (mem_sl2SubalgebraOfRoot_iff hα t he hf).mpr
  refine ⟨-star b,-star a,-star c,?_⟩
  simp only [map_add, conj_smul, conj_lie, hce, hcf, neg_lie, lie_neg, neg_neg]
  rw [← lie_skew f e]
  simp only [smul_neg, neg_smul]
  abel

include B hB hpos hinv H in
/-- Every complex ideal is stable under conjugation. This uses the library's
root-sl₂ decomposition of ideals, and the proved compact-real normalization. -/
theorem ideal_conj_mem (I : LieIdeal ℂ (ℂ ⊗[ℝ] L)) {x : ℂ ⊗[ℝ] L} (hx : x ∈ I) :
    conj x ∈ I := by
  have hd := I.restr_eq_iSup_sl2SubmoduleOfRoot (H := subalgebra H)
  change x ∈ I.restr (subalgebra H) at hx
  rw [hd] at hx
  induction hx using LieSubmodule.iSup_induction' with
  | mem α x hx =>
    induction hx using LieSubmodule.iSup_induction' with
    | mem hα x hx =>
      have hc := conj_mem_root_sl2 B hB hpos hinv H α.val
        ((subalgebra H).isNonZero_coe_root α) hx
      change conj x ∈ I.restr (subalgebra H)
      rw [hd]
      apply LieSubmodule.mem_iSup_of_mem α
      exact LieSubmodule.mem_iSup_of_mem hα hc
    | zero => simp
    | add x y hx hy ihx ihy => rw [map_add]; exact I.add_mem ihx ihy
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add]; exact I.add_mem ihx ihy

/-- Descent of a complex ideal along the canonical real embedding. -/
def realIdeal (I : LieIdeal ℂ (ℂ ⊗[ℝ] L)) : LieIdeal ℝ L where
  carrier := {x | (1 : ℂ) ⊗ₜ[ℝ] x ∈ I}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (1 : ℂ) ⊗ₜ[ℝ] (x+y) ∈ I
    rw [TensorProduct.tmul_add]
    exact I.add_mem hx hy
  smul_mem' := by
    intro c x hx
    change (1 : ℂ) ⊗ₜ[ℝ] (c • x) ∈ I
    rw [TensorProduct.tmul_smul]
    exact (I.toSubmodule.restrictScalars ℝ).smul_mem c hx
  lie_mem := by
    intro x y hy
    simpa using I.lie_mem (x := (1 : ℂ) ⊗ₜ[ℝ] x) hy

include B hB hpos hinv H in
/-- Stability under conjugation puts both real components of an ideal vector
in the descended real ideal. -/
theorem parts_mem_realIdeal (I : LieIdeal ℂ (ℂ ⊗[ℝ] L)) {x : ℂ ⊗[ℝ] L} (hx : x ∈ I) :
    re x ∈ realIdeal I ∧ im x ∈ realIdeal I := by
  have hreal {v : ℂ ⊗[ℝ] L} (hv : v ∈ I) : re v ∈ realIdeal I := by
    have hsum := I.add_mem hv (ideal_conj_mem B hB hpos hinv H I hv)
    have he : v + conj v = (2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] re v) := by
      apply ext_parts <;> norm_num [re_smul, im_smul, two_smul]
    rw [he] at hsum
    exact (I.toSubmodule.smul_mem_iff (by norm_num : (2 : ℂ) ≠ 0)).mp hsum
  refine ⟨hreal hx, ?_⟩
  simpa [re_smul] using hreal (I.smul_mem (-Complex.I) hx)

include B hB hpos hinv H in
/-- A real simple algebra with positive invariant form has simple
complexification. Ideals descend by conjugation, avoiding Dynkin classification. -/
theorem complexification_isSimple [LieAlgebra.IsSimple ℝ L] :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] L) where
  eq_bot_or_eq_top I := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (realIdeal I) with hI | hI
    · left
      apply le_antisymm _ bot_le
      intro x hx
      have hp := parts_mem_realIdeal B hB hpos hinv H I hx
      rw [hI] at hp
      have hr : re x = 0 := hp.1
      have hi : im x = 0 := hp.2
      change x = 0
      simpa [hr,hi] using decomposition x
    · right
      apply top_unique
      intro x _
      have hm (y : L) : (1 : ℂ) ⊗ₜ[ℝ] y ∈ I := by
        change y ∈ realIdeal I
        rw [hI]
        trivial
      rw [decomposition x]
      apply I.add_mem (hm _)
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using I.smul_mem Complex.I (hm (im x))
  non_abelian := by
    intro hab
    apply LieAlgebra.IsSimple.non_abelian ℝ (L := L)
    constructor
    intro x y
    have hh := congrArg re (LieModule.IsTrivial.trivial
      (L := ℂ ⊗[ℝ] L) (M := ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y))
    simpa using hh

end MathieuProperty.CompactRootReality

namespace MathieuProperty.ComplexParts
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

/-- The compatible complex Cartan has the original real Cartan's dimension. -/
theorem subalgebra_finrank (H : LieSubalgebra ℝ L) :
    Module.finrank ℂ (subalgebra H) = Module.finrank ℝ H := by
  change Module.finrank ℂ (subalgebra H).toSubmodule = _
  rw [subalgebra_eq_baseChange]
  rw [← (Submodule.toBaseChange.toLinearEquiv ℂ H.toSubmodule).finrank_eq]
  exact Module.finrank_baseChange

end MathieuProperty.ComplexParts
