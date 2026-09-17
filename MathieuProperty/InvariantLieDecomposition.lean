import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Lie.Prod
import Mathlib.LinearAlgebra.Projection
/-! The algebraic center/semisimple decomposition for a symmetric anisotropic
invariant real bilinear form. Positive definiteness implies the anisotropy
hypothesis. The form on the actual Lie algebra of a compact Lie group is constructed
and proved invariant in `CompactLieStructure`, which applies this algebraic
result to prove the compact-group decomposition.
-/

noncomputable section
namespace MathieuProperty
namespace CompactLieForm
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (B : LinearMap.BilinForm ℝ L) (hB : B.IsSymm)
variable (hB_aniso : ∀ x : L, B x x = 0 → x = 0) (hinv : B.lieInvariant L)

include hB_aniso in
theorem nondegenerate : B.Nondegenerate := by
  constructor
  · intro x hx
    exact hB_aniso x (hx x)
  · intro x hx
    exact hB_aniso x (hx x)

include hB_aniso hinv in
theorem abelian_ideal_le_center (I : LieIdeal ℝ L) [IsLieAbelian I] :
    I ≤ LieAlgebra.center ℝ L := by
  intro x hx
  apply (LieModule.mem_maxTrivSubmodule ℝ L L x).mpr
  intro y
  apply hB_aniso ⁅y,x⁆
  have ht : ⁅y,x⁆ ∈ I := I.lie_mem hx
  have hz : ⁅x,⁅y,x⁆⁆ = 0 := by
    have he := LieModule.IsTrivial.trivial (⟨x,hx⟩ : I) (⟨⁅y,x⁆,ht⟩ : I)
    exact congrArg Subtype.val he
  calc
    B ⁅y,x⁆ ⁅y,x⁆ = B (-⁅x,y⁆) ⁅y,x⁆ := congrArg (fun v => B v ⁅y,x⁆) (lie_skew y x).symm
    _ = -B ⁅x,y⁆ ⁅y,x⁆ := by simp only [map_neg, LinearMap.neg_apply]
    _ = B y ⁅x,⁅y,x⁆⁆ := by rw [hinv, neg_neg]
    _ = 0 := by rw [hz, map_zero]

include hB_aniso in
theorem ideal_orthogonal_disjoint (I : LieIdeal ℝ L) :
    Disjoint I (LieAlgebra.InvariantForm.orthogonal B hinv I) := by
  rw [disjoint_iff]
  apply le_antisymm
  · intro x hx
    have ho := (LieAlgebra.InvariantForm.mem_orthogonal B hinv I x).mp hx.2
    have hz := hB_aniso x (ho x hx.1)
    simpa only [LieSubmodule.mem_bot] using hz
  · exact bot_le

variable [FiniteDimensional ℝ L]

include hB hB_aniso in
theorem ideal_orthogonal_isCompl (I : LieIdeal ℝ L) :
    IsCompl I (LieAlgebra.InvariantForm.orthogonal B hinv I) := by
  rw [← LieSubmodule.isCompl_toSubmodule, LieAlgebra.InvariantForm.orthogonal_toSubmodule,
    LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hB.isRefl,
    ← LieAlgebra.InvariantForm.orthogonal_toSubmodule B hinv,
    LieSubmodule.disjoint_toSubmodule]
  exact ideal_orthogonal_disjoint B hB_aniso hinv I
def centerComplement : LieIdeal ℝ L :=
  LieAlgebra.InvariantForm.orthogonal B hinv (LieAlgebra.center ℝ L)

include hB hB_aniso in
theorem center_complement_isCompl : IsCompl (LieAlgebra.center ℝ L) (centerComplement B hinv) :=
  ideal_orthogonal_isCompl B hB hB_aniso hinv _

include hB hB_aniso in
theorem center_complement_center_eq_bot :
    LieAlgebra.center ℝ (centerComplement B hinv) = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  intro x hx
  have hc := center_complement_isCompl B hB hB_aniso hinv
  have hcent : (x : L) ∈ LieAlgebra.center ℝ L := by
    apply (LieModule.mem_maxTrivSubmodule ℝ L L (x : L)).mpr
    intro y
    have hym : y ∈ LieAlgebra.center ℝ L ⊔ centerComplement B hinv := by rw [hc.sup_eq_top]; trivial
    obtain ⟨z,hz,k,hk,rfl⟩ := (LieSubmodule.mem_sup _ _ _).mp hym
    rw [add_lie]
    have hz0 : ⁅z,(x : L)⁆ = 0 := by
      rw [← lie_skew]
      simp only [(LieModule.mem_maxTrivSubmodule ℝ L L z).mp hz (x : L), neg_zero]
    have hk0 : ⁅k,(x : L)⁆ = 0 := by
      have ht := (LieModule.mem_maxTrivSubmodule ℝ (centerComplement B hinv)
        (centerComplement B hinv) x).mp hx ⟨k,hk⟩
      exact congrArg Subtype.val ht
    rw [hz0, hk0, add_zero]
  have hi : (x : L) ∈ LieAlgebra.center ℝ L ⊓ centerComplement B hinv := ⟨hcent,x.property⟩
  rw [hc.inf_eq_bot] at hi
  exact Subtype.ext (by simpa using hi)

include hinv in
theorem restrict_invariant (I : LieIdeal ℝ L) : (B.restrict I.toSubmodule).lieInvariant I := by
  intro x y z
  exact hinv x y z

include hB_aniso in
theorem restrict_anisotropic (I : LieIdeal ℝ L) :
    ∀ x : I, (B.restrict I.toSubmodule) x x = 0 → x = 0 := by
  intro x hx
  exact Subtype.ext (hB_aniso x hx)

include hB hB_aniso in
theorem center_complement_semisimple : LieAlgebra.IsSemisimple ℝ (centerComplement B hinv) := by
  let K := centerComplement B hinv
  let BK := B.restrict K.toSubmodule
  have hkpos := restrict_anisotropic B hB_aniso K
  have hkinv := restrict_invariant B hinv K
  have hkSymm := hB.restrict K.toSubmodule
  apply LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate BK
    (nondegenerate (L := K) BK hkpos) hkinv hkSymm.isRefl
  intro I hI hab
  letI := hab
  have hc := abelian_ideal_le_center BK hkpos hkinv I
  rw [center_complement_center_eq_bot B hB hB_aniso hinv] at hc
  exact hI.ne_bot (le_antisymm hc bot_le)

def centerDecomposition :
    (LieAlgebra.center ℝ L × centerComplement B hinv) ≃ₗ⁅ℝ⁆ L where
  __ := Submodule.prodEquivOfIsCompl (LieAlgebra.center ℝ L).toSubmodule
    (centerComplement B hinv).toSubmodule
    ((LieSubmodule.isCompl_toSubmodule).mpr (center_complement_isCompl B hB hB_aniso hinv))
  map_lie' {x y} := by
    change ⁅(x.1 : L),(y.1 : L)⁆ + ⁅(x.2 : L),(y.2 : L)⁆ =
      ⁅(x.1 : L)+(x.2 : L),(y.1 : L)+(y.2 : L)⁆
    have hx := (LieModule.mem_maxTrivSubmodule ℝ L L (x.1 : L)).mp x.1.property
    have hy := (LieModule.mem_maxTrivSubmodule ℝ L L (y.1 : L)).mp y.1.property
    have hcross : ⁅(x.1 : L),(y.2 : L)⁆ = 0 := by rw [← lie_skew, hx, neg_zero]
    rw [add_lie, lie_add, lie_add, hy, hy, hcross]
    simp

include hB hB_aniso hinv in
theorem exists_central_semisimple_complement :
    ∃ K : LieIdeal ℝ L, IsCompl (LieAlgebra.center ℝ L) K ∧ LieAlgebra.IsSemisimple ℝ K :=
  ⟨centerComplement B hinv, center_complement_isCompl B hB hB_aniso hinv,
    center_complement_semisimple B hB hB_aniso hinv⟩

end CompactLieForm
end MathieuProperty
