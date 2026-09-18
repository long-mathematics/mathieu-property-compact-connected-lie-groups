import MathieuProperty.ComplexCartan
import MathieuProperty.CompactLieStructure

/-! Conjugation and root reality in the complexification of a real Lie algebra
with a positive invariant form. These are compact-real compatibility results,
not an assumption that an algebraic root triple is already a compact triple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace MathieuProperty.ComplexParts
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Real and imaginary parts determine a complexified vector. -/
theorem ext_parts {x y : ℂ ⊗[ℝ] L} (hr : re x = re y) (hi : im x = im y) : x = y := by
  rw [decomposition x, decomposition y, hr, hi]

/-- Conjugation relative to the given real form. -/
def conj : ℂ ⊗[ℝ] L →ₗ[ℝ] ℂ ⊗[ℝ] L :=
  (TensorProduct.mk ℝ ℂ L 1).comp re - (TensorProduct.mk ℝ ℂ L Complex.I).comp im

@[simp] theorem re_conj (x : ℂ ⊗[ℝ] L) : re (conj x) = re x := by
  simp [conj]
@[simp] theorem im_conj (x : ℂ ⊗[ℝ] L) : im (conj x) = -im x := by
  simp [conj]
@[simp] theorem conj_conj (x : ℂ ⊗[ℝ] L) : conj (conj x) = x :=
  ext_parts (by simp) (by simp)

theorem conj_smul (z : ℂ) (x : ℂ ⊗[ℝ] L) : conj (z • x) = star z • conj x := by
  apply ext_parts <;> simp [re_smul, im_smul, sub_eq_add_neg, add_comm]

@[simp] theorem conj_tmul (z : ℂ) (x : L) : conj (z ⊗ₜ[ℝ] x) = star z ⊗ₜ[ℝ] x := by
  apply ext_parts <;> simp

@[simp] theorem conj_lie (x y : ℂ ⊗[ℝ] L) : conj ⁅x,y⁆ = ⁅conj x,conj y⁆ := by
  apply ext_parts <;> simp [re_lie, im_lie, add_comm]

/-- A fixed vector lies in the image of the actual real algebra. -/
theorem conj_eq_self_iff (x : ℂ ⊗[ℝ] L) :
    conj x = x ↔ ∃ v : L, (1 : ℂ) ⊗ₜ[ℝ] v = x := by
  constructor
  · intro h
    have hi := congrArg im h
    have hz : (2 : ℝ) • im x = 0 := by
      simp only [im_conj] at hi
      rw [two_smul]
      exact neg_eq_iff_add_eq_zero.mp hi
    have hzero : im x = 0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
    exact ⟨re x, by simpa [hzero] using (decomposition x).symm⟩
  · rintro ⟨v,rfl⟩
    simp

/-- An anti-fixed vector becomes real after multiplication by i. -/
theorem real_of_conj_eq_neg {x : ℂ ⊗[ℝ] L} (hx : conj x = -x) :
    ∃ v : L, (1 : ℂ) ⊗ₜ[ℝ] v = Complex.I • x := by
  apply (conj_eq_self_iff _).mp
  simp [conj_smul, hx]

/-- Conjugation preserves the sl₂ relations, whose constants are real. -/
theorem conj_sl2Triple {h e f : ℂ ⊗[ℝ] L} (t : IsSl2Triple h e f) :
    IsSl2Triple (conj h) (conj e) (conj f) where
  h_ne_zero := by
    intro hz
    have hh := congrArg conj hz
    simpa using t.h_ne_zero (by simpa using hh)
  lie_e_f := by rw [← conj_lie, t.lie_e_f]
  lie_h_e_nsmul := by rw [← conj_lie, t.lie_h_e_nsmul, map_nsmul]
  lie_h_f_nsmul := by rw [← conj_lie, t.lie_h_f_nsmul, map_neg, map_nsmul]

/-- The real subalgebra embeds in its compatible complexification. -/
def realElement (H : LieSubalgebra ℝ L) (x : H) : subalgebra H :=
  ⟨(1 : ℂ) ⊗ₜ[ℝ] x.val, (real_mem_subalgebra H x.val).mpr x.property⟩

theorem cartan_decomposition (H : LieSubalgebra ℝ L) (x : subalgebra H) :
    x = realElement H ⟨re x.val,x.property.1⟩ +
      Complex.I • realElement H ⟨im x.val,x.property.2⟩ := by
  apply Subtype.ext
  change x.val = (1 : ℂ) ⊗ₜ[ℝ] re x.val + Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] im x.val)
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using decomposition x.val

end MathieuProperty.ComplexParts

namespace MathieuProperty.CompactRootReality
open ComplexParts
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (B : LinearMap.BilinForm ℝ L) (hB : B.IsSymm)
  (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) (hinv : B.lieInvariant L)

include B hB hpos hinv in
/-- Skew invariance forces a real adjoint operator's complex eigenvalues to
be purely imaginary. The proof uses the two real components, without a choice
of Hermitian norm on the tensor product. -/
theorem eigenvalue_re_eq_zero (X : L) {v : ℂ ⊗[ℝ] L} (hv : v ≠ 0) {z : ℂ}
    (hz : ⁅(1 : ℂ) ⊗ₜ[ℝ] X,v⁆ = z • v) : z.re = 0 := by
  have hn (x : L) : 0 ≤ B x x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  have hsum : 0 < B (re v) (re v) + B (im v) (im v) := by
    by_cases hr : re v = 0
    · have hi : im v ≠ 0 := by
        intro hi
        exact hv (by simpa [hr,hi] using decomposition v)
      simpa [hr] using hpos (im v) hi
    · exact add_pos_of_pos_of_nonneg (hpos (re v) hr) (hn _)
  have hr := congrArg re hz
  have hi := congrArg im hz
  simp only [re_lie, im_lie, re_tmul, im_tmul, Complex.one_re, Complex.one_im,
    one_smul, zero_smul, zero_lie, sub_zero, add_zero, re_smul, im_smul] at hr hi
  have hs (w : L) : B ⁅X,w⁆ w = 0 := by
    have h := hinv X w w
    have hh := hB.eq w ⁅X,w⁆
    linarith
  have hu := hs (re v)
  have hw := hs (im v)
  rw [hr] at hu
  rw [hi] at hw
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul] at hu hw
  have he := hB.eq (im v) (re v)
  rw [he] at hu
  have hz0 : z.re * (B (re v) (re v) + B (im v) (im v)) = 0 := by
    nlinarith [hu,hw]
  exact (mul_eq_zero.mp hz0).resolve_right hsum.ne'

include B hB hpos hinv in
/-- The scalar relating opposite vectors in a compact real sl₂ triple has
negative real value. Positivity fixes the sign needed for compact normalization. -/
theorem opposite_scalar_negative {h e f : ℂ ⊗[ℝ] L} (t : IsSl2Triple h e f)
    (hh : conj h = -h) {c : ℝ} (hf : f = (c : ℂ) • conj e) : c < 0 := by
  have hrh : re h = 0 := by
    have he := congrArg re hh
    simp only [re_conj, map_neg] at he
    have hz : (2 : ℝ) • re h = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp he
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have him : im h = (-2*c) • ⁅re e,im e⁆ := by
    rw [← t.lie_e_f, hf, lie_smul, im_smul]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero,
      im_lie, re_conj, im_conj, lie_neg]
    rw [← lie_skew (im e) (re e)]
    module
  have hrel := t.lie_h_e_smul ℂ
  have hr := congrArg re hrel
  have hi := congrArg im hrel
  norm_num [re_lie, im_lie, hrh, re_smul, im_smul] at hr hi
  have hv : im e ≠ 0 := by
    intro hv
    have hu : re e = 0 := by
      simp only [hv, lie_zero, zero_lie, neg_zero] at hr
      exact (smul_eq_zero.mp hr.symm).resolve_left (by norm_num)
    exact t.e_ne_zero (by simpa [hu,hv] using decomposition e)
  have hposv := hpos (im e) hv
  have hnonneg : 0 ≤ B ⁅re e,im e⁆ ⁅re e,im e⁆ := by
    by_cases hz : ⁅re e,im e⁆ = 0
    · simp [hz]
    · exact (hpos _ hz).le
  have hform := hinv (re e) (im h) (im e)
  rw [← lie_skew (re e) (im h), hi, him] at hform
  simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply,
    smul_eq_mul] at hform
  by_contra hc
  have hc' : 0 ≤ c := le_of_not_gt hc
  have hmul := mul_nonneg hc' hnonneg
  nlinarith [hform]

section Roots
open LieAlgebra LieAlgebra.IsKilling LieModule
variable [FiniteDimensional ℝ L] [IsKilling ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] [IsLieAbelian H]

include B hB hpos hinv in
/-- Every complex root takes purely imaginary values on the actual real Cartan. -/
theorem root_re_eq_zero (α : Weight ℂ (subalgebra H) (ℂ ⊗[ℝ] L)) (x : H) :
    (α (realElement H x)).re = 0 := by
  obtain ⟨v,hv,hv0⟩ := α.exists_ne_zero
  apply eigenvalue_re_eq_zero B hB hpos hinv x.val hv0
  exact lie_eq_smul_of_mem_rootSpace hv (realElement H x)

include B hB hpos hinv in
/-- Conjugation sends each root space to the opposite root space in the same
compatible Cartan, using positivity of the given real invariant form. -/
theorem conj_mem_opposite_rootSpace
    (α : Weight ℂ (subalgebra H) (ℂ ⊗[ℝ] L)) {v : ℂ ⊗[ℝ] L}
    (hv : v ∈ rootSpace (subalgebra H) α) :
    conj v ∈ rootSpace (subalgebra H) (-α) := by
  apply weightSpace_le_genWeightSpace _
  apply (mem_weightSpace _ _).mpr
  have hr (x : H) : ⁅realElement H x, conj v⁆ = -(α (realElement H x)) • conj v := by
    have he := congrArg conj (lie_eq_smul_of_mem_rootSpace hv (realElement H x))
    have hs : star (α (realElement H x)) = -(α (realElement H x)) := by
      apply Complex.ext <;> simp [root_re_eq_zero B hB hpos hinv H α x]
    change conj ⁅(1 : ℂ) ⊗ₜ[ℝ] x.val,v⁆ = conj (α (realElement H x) • v) at he
    change ⁅(1 : ℂ) ⊗ₜ[ℝ] x.val,conj v⁆ = -(α (realElement H x)) • conj v
    simpa only [conj_lie, conj_tmul, star_one, conj_smul, hs] using he
  intro h
  change ⁅h,conj v⁆ = -((α : Module.Dual ℂ (subalgebra H)) h) • conj v
  rw [cartan_decomposition H h]
  simp only [add_lie, smul_lie, map_add, map_smul, Weight.toLinear_apply, hr,
    neg_add, add_smul, neg_smul, smul_neg, smul_smul, smul_eq_mul]


include B hB hpos hinv in
/-- The coroot of a compact root triple is anti-fixed by real conjugation. -/
theorem conj_coroot_eq_neg
    (α : Weight ℂ (subalgebra H) (ℂ ⊗[ℝ] L)) (hα : α.IsNonZero) :
    conj (coroot α : ℂ ⊗[ℝ] L) = -(coroot α : ℂ ⊗[ℝ] L) := by
  obtain ⟨h,e,f,t,he,hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have hh := t.h_eq_coroot hα he hf
  have hce := conj_mem_opposite_rootSpace B hB hpos hinv H α he
  have hcf := conj_mem_opposite_rootSpace B hB hpos hinv H (-α) hf
  have ht := (conj_sl2Triple t).h_eq_coroot hα.neg hce hcf
  rw [hh, coroot_neg] at ht
  exact ht

include B hB hpos hinv in
/-- The compact-real Cartan generator i*h is an actual real vector. -/
theorem exists_real_coroot_generator
    (α : Weight ℂ (subalgebra H) (ℂ ⊗[ℝ] L)) (hα : α.IsNonZero) :
    ∃ Z : L, (1 : ℂ) ⊗ₜ[ℝ] Z = Complex.I • (coroot α : ℂ ⊗[ℝ] L) :=
  real_of_conj_eq_neg (conj_coroot_eq_neg B hB hpos hinv H α hα)

include B hB hpos hinv in
/-- Opposite vectors of any algebraic root triple are related by a strictly
negative real multiple of conjugation. -/
theorem root_triple_opposite_scalar
    (α : Weight ℂ (subalgebra H) (ℂ ⊗[ℝ] L)) (hα : α.IsNonZero)
    {h e f : ℂ ⊗[ℝ] L} (t : IsSl2Triple h e f)
    (he : e ∈ rootSpace (subalgebra H) α) (hf : f ∈ rootSpace (subalgebra H) (-α)) :
    ∃ c : ℝ, c < 0 ∧ f = (c : ℂ) • conj e := by
  have hce := conj_mem_opposite_rootSpace B hB hpos hinv H α he
  have hne : conj e ≠ 0 := by
    intro hz
    have hh := congrArg conj hz
    exact t.e_ne_zero (by simpa using hh)
  have hspan := toSubmodule_rootSpace_eq_span (-α) hα.neg (conj e) hne hce
  have hmem : f ∈ Submodule.span ℂ {conj e} := by
    rw [← hspan]
    exact hf
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hh : conj h = -h := by
    rw [t.h_eq_coroot hα he hf]
    exact conj_coroot_eq_neg B hB hpos hinv H α hα
  have heq : h = c • ⁅e,conj e⁆ := by rw [← t.lie_e_f, ← hc, lie_smul]
  have hbr : ⁅e,conj e⁆ ≠ 0 := by
    intro hz
    exact t.h_ne_zero (by simpa [hz] using heq)
  have hcon := congrArg conj heq
  rw [hh, conj_smul, conj_lie, conj_conj, ← lie_skew (conj e) e, smul_neg, heq] at hcon
  have hreal : star c = c := smul_left_injective ℂ hbr (neg_injective hcon).symm
  have hcim : c.im = 0 := by
    have h := congrArg Complex.im hreal
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have hco : c = (c.re : ℂ) := Complex.ext rfl (by simpa using hcim)
  have hfreal : f = (c.re : ℂ) • conj e := by rw [← hco]; exact hc.symm
  exact ⟨c.re, opposite_scalar_negative B hB hpos hinv t hh hfreal, hfreal⟩

include B hB hpos hinv in
/-- A compact root triple can be normalized so its lowering vector is minus
the real-form conjugate of its raising vector. -/
theorem exists_normalized_root_triple
    (α : Weight ℂ (subalgebra H) (ℂ ⊗[ℝ] L)) (hα : α.IsNonZero) :
    ∃ (h e f : ℂ ⊗[ℝ] L), IsSl2Triple h e f ∧
      h = (coroot α : ℂ ⊗[ℝ] L) ∧ e ∈ rootSpace (subalgebra H) α ∧
      f ∈ rootSpace (subalgebra H) (-α) ∧ f = -conj e := by
  obtain ⟨h,e,f,t,he,hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain ⟨c,hc,hcf⟩ := root_triple_opposite_scalar B hB hpos hinv H α hα t he hf
  let r : ℝ := Real.sqrt (-c)
  have hr : 0 < r := Real.sqrt_pos.mpr (neg_pos.mpr hc)
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hsqr : r^2 = -c := Real.sq_sqrt (neg_nonneg.mpr hc.le)
  have hsqc : (r : ℂ)^2 = -(c : ℂ) := by exact_mod_cast hsqr
  have hsc : (r : ℂ)⁻¹ * (c : ℂ) = -(r : ℂ) := by
    apply (mul_left_cancel₀ hr0)
    rw [← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
    linear_combination hsqc
  have ht : IsSl2Triple h ((r : ℂ) • e) ((r : ℂ)⁻¹ • f) := {
    h_ne_zero := t.h_ne_zero
    lie_e_f := by rw [smul_lie (r : ℂ) e ((r : ℂ)⁻¹ • f), lie_smul, smul_smul, mul_inv_cancel₀ hr0, one_smul, t.lie_e_f]
    lie_h_e_nsmul := by rw [lie_smul, t.lie_h_e_nsmul]; simp only [two_smul, smul_add]
    lie_h_f_nsmul := by rw [lie_smul, t.lie_h_f_nsmul]; simp only [two_smul, smul_add, smul_neg] }
  refine ⟨h,(r : ℂ) • e,(r : ℂ)⁻¹ • f,ht,t.h_eq_coroot hα he hf,
    (rootSpace (subalgebra H) α).smul_mem _ he,
    (rootSpace (subalgebra H) (-α)).smul_mem _ hf,?_⟩
  rw [hcf, smul_smul, hsc, conj_smul]
  simp

include B hB hpos hinv in
/-- Compact-real generators for the normalized root triple, with the exact
complexification identities needed in the adjoint-route target AR02a. -/
theorem exists_compact_root_triple
    (α : Weight ℂ (subalgebra H) (ℂ ⊗[ℝ] L)) (hα : α.IsNonZero) :
    ∃ (h e f : ℂ ⊗[ℝ] L), IsSl2Triple h e f ∧
      h = (coroot α : ℂ ⊗[ℝ] L) ∧ e ∈ rootSpace (subalgebra H) α ∧
      f ∈ rootSpace (subalgebra H) (-α) ∧
      ∃ X Y Z : L, (1 : ℂ) ⊗ₜ[ℝ] X = e-f ∧
        (1 : ℂ) ⊗ₜ[ℝ] Y = Complex.I • (e+f) ∧
        (1 : ℂ) ⊗ₜ[ℝ] Z = Complex.I • h := by
  obtain ⟨h,e,f,t,hh,he,hf,hcon⟩ := exists_normalized_root_triple B hB hpos hinv H α hα
  have hx : conj (e-f) = e-f := by simp [hcon, sub_eq_add_neg, add_comm]
  have hy : conj (e+f) = -(e+f) := by simp [hcon, sub_eq_add_neg, add_comm]
  obtain ⟨X,hX⟩ := (conj_eq_self_iff _).mp hx
  obtain ⟨Y,hY⟩ := real_of_conj_eq_neg hy
  obtain ⟨Z,hZ⟩ := exists_real_coroot_generator B hB hpos hinv H α hα
  exact ⟨h,e,f,t,hh,he,hf,X,Y,Z,hX,hY,by simpa [hh] using hZ⟩

end Roots

end MathieuProperty.CompactRootReality
