import MathieuProperty.InvariantLieDecomposition
/-! In a finite-dimensional real Lie algebra with a positive invariant form,
every ideal has an ideal complement. The complement commutes with the ideal,
so the ambient adjoint action restricts to exactly the ideal's own adjoint image. -/

noncomputable section
namespace MathieuProperty
namespace CompactLieForm
attribute [local instance 100] LieRing.ofAssociativeRing
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
variable (B : LinearMap.BilinForm ℝ L) (hB : B.IsSymm)
variable (hB_aniso : ∀ x : L, B x x = 0 → x = 0) (hinv : B.lieInvariant L)
include B hB hB_aniso hinv
theorem exists_restricted_adjoint (I : LieIdeal ℝ L) (x : L) :
    ∃ z : I, ∀ v : I, ⁅x,v.val⁆ = ⁅z.val,v.val⁆ := by
  let J := LieAlgebra.InvariantForm.orthogonal B hinv I
  have hc : IsCompl I J := ideal_orthogonal_isCompl B hB hB_aniso hinv I
  have hx : x ∈ I ⊔ J := by rw [hc.sup_eq_top]; trivial
  obtain ⟨z,hz,w,hw,rfl⟩ := (LieSubmodule.mem_sup _ _ _).mp hx
  refine ⟨⟨z,hz⟩, fun v => ?_⟩
  have hbr : ⁅w,v.val⁆ ∈ I ⊓ J := ⟨lie_mem_right ℝ L I _ _ v.property, lie_mem_left ℝ L J _ _ hw⟩
  have hzero : ⁅w,v.val⁆ = 0 := by
    rw [hc.inf_eq_bot] at hbr
    exact hbr
  rw [add_lie,hzero,add_zero]

theorem restricted_adjoint_range (I : LieIdeal ℝ L) :
    (LieModule.toEnd ℝ L I).range = (LieAlgebra.ad ℝ I).range := by
  ext f
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨z,hz⟩ := exists_restricted_adjoint B hB hB_aniso hinv I x
    refine ⟨z,?_⟩
    ext v
    exact (hz v).symm
  · rintro ⟨z,rfl⟩
    exact ⟨z.val,rfl⟩
end CompactLieForm
end MathieuProperty
