import MathieuProperty.CompactRootNormalization
/-! The algebraic rank-one reduction: all roots are ±α, the root triple spans,
and the compact real algebra has dimension three. The compact generators form
a spanning cyclic bracket triple. This does not yet identify the group adjoint
form with SU(2)/{±1}. -/
noncomputable section
open LieAlgebra LieAlgebra.IsKilling LieModule
namespace MathieuProperty.AdjointRankOne
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  [IsKilling ℂ L] (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
  [IsTriangularizable ℂ H L]

/-- A reduced root system in a one-dimensional Cartan dual has only two roots. -/
theorem root_eq_or_neg_of_rank_one (hr : Module.finrank ℂ H = 1) (α β : H.root) :
    β.val = α.val ∨ β.val = -α.val := by
  have hn : ¬ LinearIndependent ℂ ![(rootSystem H).root β,(rootSystem H).root α] := by
    intro hi
    have hc := hi.fintype_card_le_finrank
    simp [Subspace.dual_finrank_eq, hr] at hc
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := rootSystem H) β α hn with he | he
  · left
    ext x
    exact LinearMap.congr_fun he x
  · right
    ext x
    exact LinearMap.congr_fun he x

/-- In rank one, the root sl₂ submodule is the whole algebra. -/
theorem root_sl2_eq_top_of_rank_one (hr : Module.finrank ℂ H = 1) (α : H.root) :
    sl2SubmoduleOfRoot (H.isNonZero_coe_root α) = ⊤ := by
  apply top_unique
  have hd := (⊤ : LieIdeal ℂ L).restr_eq_iSup_sl2SubmoduleOfRoot (H := H)
  change (⊤ : LieSubmodule ℂ H L) = _ at hd
  rw [hd]
  apply iSup₂_le
  intro β hβ
  rcases root_eq_or_neg_of_rank_one H hr α β with he | he
  · simp only [sl2SubmoduleOfRoot_eq_sup, he]
    exact le_rfl
  · simp only [sl2SubmoduleOfRoot_eq_sup, he, Weight.coe_neg, neg_neg]
    have hc : corootSubmodule (-α.val) = corootSubmodule α.val := by
      apply congrArg (LieSubmodule.map H.toLieSubmodule.incl)
      apply LieSubmodule.toSubmodule_injective
      rw [coe_corootSpace_eq_span_singleton, coe_corootSpace_eq_span_singleton, coroot_neg]
      apply le_antisymm <;> apply Submodule.span_le.mpr <;> intro x hx <;>
        simp only [Set.mem_singleton_iff] at hx <;> subst x
      · exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
      · simpa using Submodule.neg_mem (ℂ ∙ -coroot α.val) (Submodule.subset_span (by simp : -coroot α.val ∈ ({-coroot α.val} : Set H)))
    rw [hc]
    exact le_of_eq (by rw [sup_comm (genWeightSpace L (-(α.val : H → ℂ)))])

omit [FiniteDimensional ℂ L] [IsKilling ℂ L] in
/-- The three sl₂ vectors are independent, by their distinct adjoint eigenvalues. -/
theorem triple_linearIndependent {h e f : L} (t : IsSl2Triple h e f) :
    LinearIndependent ℂ ![e,f,h] := by
  apply (LieAlgebra.ad ℂ L h).eigenvectors_linearIndependent' ![2,-2,0]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals rfl
  · intro i
    rw [Module.End.hasEigenvector_iff]
    fin_cases i
    · refine ⟨?_,t.e_ne_zero⟩
      rw [Module.End.mem_eigenspace_iff]
      exact t.lie_h_e_smul ℂ
    · refine ⟨?_,t.f_ne_zero⟩
      rw [Module.End.mem_eigenspace_iff]
      change ⁅h,f⁆ = (-2 : ℂ) • f
      simpa [neg_smul, two_smul] using t.lie_h_f_nsmul
    · exact ⟨by simp,t.h_ne_zero⟩

/-- Every root triple spans the entire complex rank-one algebra. -/
theorem root_triple_span_of_rank_one (hr : Module.finrank ℂ H = 1)
    (α : H.root) {h e f : L} (t : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α.val) (hf : f ∈ rootSpace H (-α.val)) :
    Submodule.span ℂ (Set.range ![e,f,h]) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
    rw [root_sl2_eq_top_of_rank_one H hr α]
    trivial
  change x ∈ sl2SubalgebraOfRoot (H.isNonZero_coe_root α) at hx
  obtain ⟨a,b,c,hx⟩ := (mem_sl2SubalgebraOfRoot_iff (H.isNonZero_coe_root α) t he hf).mp hx
  rw [t.lie_e_f] at hx
  rw [hx]
  apply Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    apply Submodule.smul_mem
  · exact Submodule.subset_span ⟨0,rfl⟩
  · exact Submodule.subset_span ⟨1,rfl⟩
  · exact Submodule.subset_span ⟨2,rfl⟩

/-- A splitting Killing algebra of rank one has complex dimension three. -/
theorem finrank_eq_three_of_rank_one (hr : Module.finrank ℂ H = 1) (α : H.root) :
    Module.finrank ℂ L = 3 := by
  obtain ⟨h,e,f,t,he,hf⟩ := exists_isSl2Triple_of_weight_isNonZero (H.isNonZero_coe_root α)
  have hb := Module.Basis.mk (triple_linearIndependent t)
    (le_of_eq (root_triple_span_of_rank_one H hr α t he hf).symm)
  simpa using Module.finrank_eq_card_basis hb

end MathieuProperty.AdjointRankOne

open scoped Manifold ContDiff TensorProduct
namespace MathieuProperty.AdjointRankOne
open CompactCartanRootData
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G]
local instance rankOneNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance rankOneFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

/-- The actual compact real simple group algebra has dimension three at rank one. -/
theorem real_finrank_eq_three (hr : Module.finrank ℝ (realCartan (E := E) (G := G)) = 1) :
    Module.finrank ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) = 3 := by
  have hc : Module.finrank ℂ (complexCartan (E := E) (G := G)) = 1 := by
    rwa [complexCartan_finrank]
  let b := simpleBase (E := E) (G := G)
  have hb : Fintype.card b.support = 1 := by
    rwa [Module.finrank_eq_card_basis b.toCoweightBasis] at hc
  let : Nonempty b.support := Fintype.card_pos_iff.mp (by omega)
  let α : b.support := Classical.arbitrary _
  have hd := finrank_eq_three_of_rank_one (complexCartan (E := E) (G := G)) hc α.val
  simpa only [Module.finrank_baseChange] using hd

end MathieuProperty.AdjointRankOne

namespace MathieuProperty.CompactRootReality
open ComplexParts
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The compact-real generators satisfy the cyclic su₂ bracket relations. -/
theorem compact_triple_relations {h e f : ℂ ⊗[ℝ] L} (t : IsSl2Triple h e f)
    (X Y Z : L) (hX : (1 : ℂ) ⊗ₜ[ℝ] X = e-f)
    (hY : (1 : ℂ) ⊗ₜ[ℝ] Y = Complex.I • (e+f))
    (hZ : (1 : ℂ) ⊗ₜ[ℝ] Z = Complex.I • h) :
    ⁅X,Y⁆ = (2 : ℝ) • Z ∧ ⁅Y,Z⁆ = (2 : ℝ) • X ∧ ⁅Z,X⁆ = (2 : ℝ) • Y := by
  have hfe : ⁅f,e⁆ = -h := by rw [← lie_skew f e,t.lie_e_f]
  have heh : ⁅e,h⁆ = -(2 : ℂ) • e := by rw [← lie_skew e h,t.lie_h_e_smul ℂ,neg_smul]
  have hfh : ⁅f,h⁆ = (2 : ℂ) • f := by
    rw [← lie_skew f h,t.lie_h_f_nsmul,neg_neg]
    simp only [two_smul]
  have hxy : ⁅(1 : ℂ) ⊗ₜ[ℝ] X,(1 : ℂ) ⊗ₜ[ℝ] Y⁆ =
      (2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] Z) := by
    rw [hX,hY,hZ]
    simp [lie_smul,sub_lie,lie_add,t.lie_e_f,hfe,two_smul,smul_add]
  have hyz : ⁅(1 : ℂ) ⊗ₜ[ℝ] Y,(1 : ℂ) ⊗ₜ[ℝ] Z⁆ =
      (2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
    rw [hX,hY,hZ,smul_lie Complex.I (e+f) (Complex.I • h),lie_smul,add_lie,heh,hfh]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq]
  have hzx : ⁅(1 : ℂ) ⊗ₜ[ℝ] Z,(1 : ℂ) ⊗ₜ[ℝ] X⁆ =
      (2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] Y) := by
    rw [hX,hY,hZ,smul_lie Complex.I h (e-f),lie_sub,t.lie_h_e_nsmul,t.lie_h_f_nsmul]
    simp only [two_smul,sub_neg_eq_add,smul_add]
  exact ⟨by simpa [re_smul] using congrArg re hxy,
    by simpa [re_smul] using congrArg re hyz,by simpa [re_smul] using congrArg re hzx⟩

/-- When the complex root triple spans, its compact-real generators span the real algebra. -/
theorem compact_triple_span {h e f : ℂ ⊗[ℝ] L}
    (hspan : Submodule.span ℂ (Set.range ![e,f,h]) = ⊤)
    (X Y Z : L) (hX : (1 : ℂ) ⊗ₜ[ℝ] X = e-f)
    (hY : (1 : ℂ) ⊗ₜ[ℝ] Y = Complex.I • (e+f))
    (hZ : (1 : ℂ) ⊗ₜ[ℝ] Z = Complex.I • h) :
    Submodule.span ℝ (Set.range ![X,Y,Z]) = ⊤ := by
  have hXR := congrArg re hX
  have hXI := congrArg im hX
  have hYR := congrArg re hY
  have hYI := congrArg im hY
  have hZR := congrArg re hZ
  have hZI := congrArg im hZ
  simp only [map_sub,map_add,re_tmul,im_tmul,Complex.one_re,Complex.one_im,
    one_smul,zero_smul,re_smul,im_smul,Complex.I_re,Complex.I_im,zero_sub,zero_add] at *
  have hrf : re f = -re e := eq_neg_of_add_eq_zero_right hYI.symm
  have hif : im f = im e := (sub_eq_zero.mp hXI.symm).symm
  have hrh : re h = 0 := hZI.symm
  apply top_unique
  intro x _
  have hm : (1 : ℂ) ⊗ₜ[ℝ] x ∈ Submodule.span ℂ (Set.range ![e,f,h]) := by rw [hspan]; trivial
  have hs : Set.range ![e,f,h] = {e,f,h} := by ext y; simp [or_comm,or_left_comm]
  rw [hs,Submodule.mem_span_triple] at hm
  obtain ⟨a,b,c,habc⟩ := hm
  have hx := congrArg re habc
  simp only [map_add,re_smul,re_tmul,Complex.one_re,one_smul,hrf,hif,hrh,smul_zero,zero_sub] at hx
  have hex : x = ((a.re-b.re)/2) • X + ((a.im+b.im)/2) • Y + c.im • Z := by
    rw [hXR,hYR,hZR,hrf,hif,← hx]
    module
  rw [hex]
  apply Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    apply Submodule.smul_mem
  · exact Submodule.subset_span ⟨0,rfl⟩
  · exact Submodule.subset_span ⟨1,rfl⟩
  · exact Submodule.subset_span ⟨2,rfl⟩

end MathieuProperty.CompactRootReality

namespace MathieuProperty.AdjointRankOne
open CompactCartanRootData
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G]
local instance basisNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance basisFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

/-- Every actual rank-one compact simple algebra has a basis with the standard
cyclic compact bracket constants. -/
theorem exists_compact_basis (hr : Module.finrank ℝ (realCartan (E := E) (G := G)) = 1) :
    ∃ b : Module.Basis (Fin 3) ℝ (GroupLieAlgebra 𝓘(ℝ,E) G),
      ⁅b 0,b 1⁆ = (2 : ℝ) • b 2 ∧ ⁅b 1,b 2⁆ = (2 : ℝ) • b 0 ∧
      ⁅b 2,b 0⁆ = (2 : ℝ) • b 1 := by
  have hc : Module.finrank ℂ (complexCartan (E := E) (G := G)) = 1 := by
    rwa [complexCartan_finrank]
  let sb := simpleBase (E := E) (G := G)
  have hb : Fintype.card sb.support = 1 := by
    rwa [Module.finrank_eq_card_basis sb.toCoweightBasis] at hc
  let : Nonempty sb.support := Fintype.card_pos_iff.mp (by omega)
  let α : sb.support := Classical.arbitrary _
  obtain ⟨h,e,f,t,_,he,hf,X,Y,Z,hX,hY,hZ⟩ := exists_compact_root_triple α
  have hs := CompactRootReality.compact_triple_span
    (root_triple_span_of_rank_one (complexCartan (E := E) (G := G)) hc α.val t he hf)
    X Y Z hX hY hZ
  let b := basisOfTopLeSpanOfCardEqFinrank ![X,Y,Z] (le_of_eq hs.symm)
    (by simpa using (real_finrank_eq_three (E := E) (G := G) hr).symm)
  refine ⟨b,?_⟩
  simpa [b] using CompactRootReality.compact_triple_relations t X Y Z hX hY hZ

end MathieuProperty.AdjointRankOne
