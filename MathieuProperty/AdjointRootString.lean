import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.Algebra.Lie.Weights.IsSimple
import MathieuProperty.RootDoubletModule

/-! A root-string doublet in the adjoint representation. No highest-weight
representation is constructed. The abstract root-system results use irreducibility
explicitly; applying them to a compact real simple algebra's complexification
requires the separate compact-real compatibility bridge. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.AdjointRootString
open LieAlgebra LieAlgebra.IsKilling LieModule

section RootPairing
variable {ι M N : Type*} [Finite ι] [AddCommGroup M] [Module ℂ M]
  [AddCommGroup N] [Module ℂ N]
  (P : RootPairing ι ℂ M N) [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
  (b : P.Base) [Nontrivial b.support]

/-- Connectedness supplies an edge; the finite crystallographic pairing list
forces one orientation to have Cartan integer -1. No Dynkin classification. -/
theorem exists_simple_pair_neg_one :
    ∃ α β : b.support, α ≠ β ∧ P.pairingIn ℤ β α = -1 := by
  classical
  have hedge : ∃ i j : b.support, i ≠ j ∧ b.cartanMatrix i j ≠ 0 := by
    by_contra! hn
    obtain ⟨i,j,hij⟩ := exists_pair_ne b.support
    have hji : j = i := b.induction_on_cartanMatrix (fun k => k = i) rfl (fun u v hu hv => by
      by_contra hvi
      exact hv (hn v u (by simpa [hu] using hvi)))
    exact hij hji.symm
  obtain ⟨i,j,hij,hij0⟩ := hedge
  have hi : (i : ι) ≠ j := fun h => hij (Subtype.ext h)
  have hcases := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' (i := (i : ι)) (j := (j : ι))
    (fun h => hi (P.root.injective h)) (b.root_ne_neg_of_ne i.property j.property hi)
  have hnonpos := b.cartanMatrix_le_zero_of_ne i j hij
  change P.pairingIn ℤ i j ≤ 0 at hnonpos
  change P.pairingIn ℤ i j ≠ 0 at hij0
  have h : P.pairingIn ℤ i j = -1 ∨ P.pairingIn ℤ j i = -1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hcases
    omega
  rcases h with h | h
  · exact ⟨j,i,hij.symm,h⟩
  · exact ⟨i,j,hij,h⟩

omit [P.IsReduced] [P.IsIrreducible] [Nontrivial b.support] in
/-- For the selected orientation the complete integer root string is {0,1}. -/
theorem simple_root_string {α β : b.support} (hne : α ≠ β)
    (hpair : P.pairingIn ℤ β α = -1) (z : ℤ) :
    P.root β + z • P.root α ∈ Set.range P.root ↔ z = 0 ∨ z = 1 := by
  have htop : P.chainTopCoeff α β = 1 := by
    have h := b.chainTopCoeff_eq_of_ne hne
    rw [hpair] at h
    norm_num at h
    exact_mod_cast h
  rw [P.root_add_zsmul_mem_range_iff (b.linearIndependent_pair_of_ne hne),
    b.chainBotCoeff_eq_zero, htop]
  simp only [Nat.cast_zero, neg_zero, Nat.cast_one, Set.mem_Icc]
  omega
end RootPairing

section LieAlgebra
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [IsKilling ℂ L]
  [FiniteDimensional ℂ L] {H : LieSubalgebra ℂ L} [H.IsCartanSubalgebra]
  [IsTriangularizable ℂ H L]

/-- A nonzero functional outside the root system has zero root space. -/
theorem rootSpace_eq_bot_of_not_root (χ : Module.Dual ℂ H) (hχ : χ ≠ 0)
    (hn : χ ∉ Set.range (rootSystem H).root) : rootSpace H χ = ⊥ := by
  by_contra hb
  let w : Weight ℂ H L := ⟨χ, hb⟩
  have hw : w.IsNonZero := by
    intro h
    apply hχ
    exact DFunLike.coe_injective h
  apply hn
  exact ⟨⟨w, by simpa using hw⟩, by ext x; rfl⟩

/-- Any supplied alpha root triple has a weight-one primitive vector in the
beta root space. This also applies to the compact-real normalized triple. -/
theorem primitive_for_root_triple (b : (rootSystem H).Base) {α β : b.support}
    (hne : α ≠ β) (hpair : (rootSystem H).pairingIn ℤ β α = -1)
    {h e f : L} (t : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α.val.val) (hf : f ∈ rootSpace H (-α.val.val)) :
    ∃ v : L, v ∈ rootSpace H β.val.val ∧ t.symm.HasPrimitiveVectorWith v (1 : ℂ) := by
  have hh := t.h_eq_coroot (H.isNonZero_coe_root α.val) he hf
  obtain ⟨v,hv,hv0⟩ := β.val.val.exists_ne_zero
  have hp : β.val.val (coroot α.val.val) = (-1 : ℂ) := by
    exact ((rootSystem H).algebraMap_pairingIn ℤ β.val α.val).symm.trans
      ((congrArg (algebraMap ℤ ℂ) hpair).trans (by simp))
  have hsub : rootSpace H ((β.val.val : Module.Dual ℂ H) - (α.val.val : Module.Dual ℂ H)) = ⊥ := by
    apply rootSpace_eq_bot_of_not_root (H := H)
      ((β.val.val : Module.Dual ℂ H) - (α.val.val : Module.Dual ℂ H))
    · intro h
      have heq : (rootSystem H).root β.val = (rootSystem H).root α.val := sub_eq_zero.mp h
      exact hne (Subtype.ext ((rootSystem H).root.injective heq).symm)
    · exact b.sub_notMem_range_root β.property α.property
  refine ⟨v,hv,hv0,?_,?_⟩
  · rw [neg_lie, hh]
    change -(⁅coroot α.val.val, v⁆ : L) = (1 : ℂ) • v
    rw [lie_eq_smul_of_mem_rootSpace hv, hp]
    simp
  · have hm := lie_mem_genWeightSpace_of_mem_genWeightSpace hf hv
    have heq : (-(α.val.val : H → ℂ) + (β.val.val : H → ℂ)) =
        ((β.val.val : Module.Dual ℂ H) - (α.val.val : Module.Dual ℂ H) : Module.Dual ℂ H) := by
      ext x
      simp [sub_eq_add_neg, add_comm]
    rw [heq] at hm
    change ⁅f, v⁆ ∈ rootSpace H ((β.val.val : Module.Dual ℂ H) - (α.val.val : Module.Dual ℂ H)) at hm
    rw [hsub] at hm
    exact hm
/-- A vector in the beta root space is a primitive weight-one vector for the
reversed alpha triple, in the actual adjoint module. -/
theorem adjoint_primitive (b : (rootSystem H).Base) {α β : b.support}
    (hne : α ≠ β) (hpair : (rootSystem H).pairingIn ℤ β α = -1) :
    ∃ (h e f v : L) (t : IsSl2Triple h e f),
      h = (coroot α.val.val : L) ∧ e ∈ rootSpace H α.val.val ∧
      f ∈ rootSpace H (-α.val.val) ∧ v ∈ rootSpace H β.val.val ∧
      t.symm.HasPrimitiveVectorWith v (1 : ℂ) := by
  obtain ⟨h,e,f,t,he,hf⟩ := exists_isSl2Triple_of_weight_isNonZero (H.isNonZero_coe_root α.val)
  obtain ⟨v,hv,hp⟩ := primitive_for_root_triple b hne hpair t he hf
  exact ⟨h,e,f,v,t,t.h_eq_coroot (H.isNonZero_coe_root α.val) he hf,he,hf,hv,hp⟩

/-- The cyclic doublet is exactly the sum of the two one-dimensional root spaces. -/
theorem adjoint_doublet_space (b : (rootSystem H).Base) {α β : b.support}
    (hne : α ≠ β) {h e f v : L} (t : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α.val.val) (hv : v ∈ rootSpace H β.val.val)
    (hp : t.symm.HasPrimitiveVectorWith v (1 : ℂ)) :
    sl2DoubletSpace (f := e) (v := v) =
      (rootSpace H β.val.val).toSubmodule ⊔
      (rootSpace H ((α.val.val : H → ℂ) + (β.val.val : H → ℂ))).toSubmodule := by
  have hraised := (highest_weight_one_lowering t.symm hp).1
  have hm := lie_mem_genWeightSpace_of_mem_genWeightSpace he hv
  let γ : Weight ℂ H L := ⟨(α.val.val : H → ℂ) + (β.val.val : H → ℂ), by
    intro hz
    rw [hz] at hm
    exact hraised hm⟩
  have hγ : γ.IsNonZero := by
    intro hz
    apply b.root_ne_neg_of_ne α.property β.property (fun h => hne (Subtype.ext h))
    ext x
    have hx := congrFun hz x
    change α.val.val x + β.val.val x = 0 at hx
    exact eq_neg_of_add_eq_zero_left hx
  have hb := toSubmodule_rootSpace_eq_span β.val.val (H.isNonZero_coe_root β.val) v hp.ne_zero hv
  have hg := toSubmodule_rootSpace_eq_span γ hγ ⁅e,v⁆ hraised hm
  change sl2DoubletSpace (f := e) (v := v) = (rootSpace H β.val.val).toSubmodule ⊔
    (rootSpace H γ).toSubmodule
  rw [hb,hg]
  simp [sl2DoubletSpace, sl2DoubletVectors, Submodule.span_insert, sup_comm]

/-- The actual adjoint root-string doublet has dimension two and the standard
sl₂ matrices, by reuse of the existing weight-one module calculations. -/
theorem adjoint_doublet (b : (rootSystem H).Base) {α β : b.support}
    (hne : α ≠ β) (hpair : (rootSystem H).pairingIn ℤ β α = -1) :
    ∃ (h e f v : L) (t : IsSl2Triple h e f)
      (hp : t.symm.HasPrimitiveVectorWith v (1 : ℂ)),
      h = (coroot α.val.val : L) ∧ e ∈ rootSpace H α.val.val ∧
      f ∈ rootSpace H (-α.val.val) ∧ v ∈ rootSpace H β.val.val ∧
      sl2DoubletSpace (f := e) (v := v) =
        (rootSpace H β.val.val).toSubmodule ⊔
        (rootSpace H ((α.val.val : H → ℂ) + (β.val.val : H → ℂ))).toSubmodule ∧
      Module.finrank ℂ (sl2DoubletSpace (f := e) (v := v)) = 2 ∧
      (∀ A B C : ℂ, LinearMap.toMatrix (sl2DoubletBasis t.symm hp) (sl2DoubletBasis t.symm hp)
        (LieModule.toEnd ℂ (t.symm.toLieSubalgebra ℂ) (sl2DoubletSubmodule t.symm hp)
          (sl2Element t.symm A B C)) = !![C,A;B,-C]) := by
  obtain ⟨h,e,f,v,t,hh,he,hf,hv,hp⟩ := adjoint_primitive b hne hpair
  exact ⟨h,e,f,v,t,hp,hh,he,hf,hv,adjoint_doublet_space b hne t he hv hp,
    sl2Doublet_finrank t.symm hp, sl2Doublet_matrix t.symm hp⟩

/-- Rank at least two in a complex simple algebra supplies the oriented pair
and an actual primitive vector in the adjoint representation. -/
theorem exists_adjoint_primitive [LieAlgebra.IsSimple ℂ L]
    (b : (rootSystem H).Base) (hrank : 1 < Module.finrank ℂ H) :
    ∃ (α β : b.support), α ≠ β ∧ (rootSystem H).pairingIn ℤ β α = -1 ∧
      ∃ (h e f v : L) (t : IsSl2Triple h e f),
        h = (coroot α.val.val : L) ∧ e ∈ rootSpace H α.val.val ∧
        f ∈ rootSpace H (-α.val.val) ∧ v ∈ rootSpace H β.val.val ∧
        t.symm.HasPrimitiveVectorWith v (1 : ℂ) := by
  have hc : 1 < Fintype.card b.support := by
    rwa [Module.finrank_eq_card_basis b.toCoweightBasis] at hrank
  let : Nontrivial b.support := Fintype.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨α,β,hne,hp⟩ := exists_simple_pair_neg_one (rootSystem H) b
  exact ⟨α,β,hne,hp,adjoint_primitive b hne hp⟩

end LieAlgebra

end MathieuProperty.AdjointRootString
