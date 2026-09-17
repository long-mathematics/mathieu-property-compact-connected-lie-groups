import MathieuProperty.BilinearDefect
import MathieuProperty.BilinearAutomorphism
import MathieuProperty.FiniteDimensionalSlice

/-! Automorphisms of a bilinear operation fixing a subspace pointwise.
The joint defect consists of bracket preservation and restriction minus identity.
Its linearization is the subspace of derivations vanishing on the fixed subspace;
exponentials satisfy both full equations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open NormedSpace
open scoped ContDiff Topology
namespace MathieuProperty.BilinearStabilizer
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def restriction (W : Submodule ℝ V) : (V →L[ℝ] V) →L[ℝ] W →L[ℝ] V :=
  (ContinuousLinearMap.compL ℝ W V V).flip W.subtypeL

@[simp]
theorem restriction_apply (W : Submodule ℝ V) (D : V →L[ℝ] V) (w : W) :
    restriction W D w = D w := rfl

def defect (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (T : V →L[ℝ] V) :
    (V →L[ℝ] V →L[ℝ] V) × (W →L[ℝ] V) :=
  (BilinearAutomorphism.defect B T, restriction W (T - 1))

def linearDefect (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V →L[ℝ] V) × (W →L[ℝ] V) :=
  (BilinearAutomorphism.linearDefect B).prod (restriction W)

def derivations (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    Submodule ℝ (V →L[ℝ] V) := (linearDefect B W).ker

theorem mem_derivations_iff (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V)
    (D : V →L[ℝ] V) :
    D ∈ derivations B W ↔ D ∈ BilinearAutomorphism.derivations B ∧ ∀ w : W, D w = 0 := by
  change (BilinearAutomorphism.linearDefect B D, restriction W D) = (0, 0) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hb, hw⟩
    exact ⟨hb, fun w => congrArg (fun T : W →L[ℝ] V => T w) hw⟩
  · rintro ⟨hb, hw⟩
    exact ⟨hb, ContinuousLinearMap.ext hw⟩

theorem defect_smooth (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    ContDiff ℝ ∞ (defect B W) := by
  have hw : ContDiff ℝ ∞ (fun T : V →L[ℝ] V => restriction W (T - 1)) := by
    have hr : ContDiff ℝ ∞ (restriction W) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := V →L[ℝ] V) (F := W →L[ℝ] V) (restriction W)
    exact hr.comp (contDiff_id.sub contDiff_const)
  simpa only [defect] using! (BilinearAutomorphism.defect_smooth B).prodMk hw

theorem defect_one (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : defect B W 1 = 0 := by
  simp [defect, BilinearAutomorphism.defect_one]

theorem defect_hasFDerivAt (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    HasFDerivAt (defect B W) (linearDefect B W) 1 := by
  have hb : HasFDerivAt (BilinearAutomorphism.defect B) (BilinearAutomorphism.linearDefect B) 1 :=
    ((BilinearAutomorphism.defect_smooth B).differentiable (by simp) 1).hasFDerivAt
  have hw : HasFDerivAt (fun T : V →L[ℝ] V => restriction W (T - 1)) (restriction W) 1 := by
    simpa only [ContinuousLinearMap.comp_id] using!
      HasFDerivAt.comp (𝕜 := ℝ) (f := fun T : V →L[ℝ] V => T - 1)
        (g := restriction W) (1 : V →L[ℝ] V)
        (restriction W).hasFDerivAt ((hasFDerivAt_id (1 : V →L[ℝ] V)).sub_const 1)
  exact HasFDerivAt.prodMk (𝕜 := ℝ) (f₁ := BilinearAutomorphism.defect B)
    (f₂ := fun T : V →L[ℝ] V => restriction W (T - 1)) hb hw

theorem defect_strictDeriv (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    HasStrictFDerivAt (defect B W) (linearDefect B W) 1 := by
  have h : HasStrictFDerivAt (defect B W) (fderiv ℝ (defect B W) 1) 1 :=
    (defect_smooth B W).contDiffAt.hasStrictFDerivAt (by simp)
  rwa [(defect_hasFDerivAt B W).fderiv] at h

variable [CompleteSpace V]

theorem exp_fixes (D : V →L[ℝ] V) {v : V} (hv : D v = 0) : exp D v = v := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => exp (s • D) v) 0 t := by
    simpa only [mul_apply_eq_comp, hv, map_zero, add_zero] using
      (hasDerivAt_exp_smul_const D t).clm_apply (hasDerivAt_const t v)
  have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) (1 : ℝ) 0
  simpa only [one_smul, zero_smul, exp_zero, one_apply_eq_self] using he

def group (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) : Subgroup (V →L[ℝ] V)ˣ where
  carrier := {u | u ∈ BilinearAutomorphism.group B ∧ ∀ w : W, u.val w = w}
  one_mem' := ⟨(BilinearAutomorphism.group B).one_mem, fun _ => rfl⟩
  mul_mem' {u v} hu hv := by
    refine ⟨(BilinearAutomorphism.group B).mul_mem hu.1 hv.1, ?_⟩
    intro w
    change u.val (v.val w) = w
    rw [hv.2, hu.2]
  inv_mem' {u} hu := by
    refine ⟨(BilinearAutomorphism.group B).inv_mem hu.1, ?_⟩
    intro w
    apply (ContinuousLinearEquiv.ofUnit u).injective
    change u.val (u.inv w) = u.val w
    have he : u.val (u.inv w) = w := by
      change (u.val * u.inv) w = w
      rw [u.val_inv]
      rfl
    rw [he, hu.2]

theorem exp_mem_group (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V)
    (D : derivations B W) : DerivationExponential.expUnit D.val ∈ group B W := by
  have hD := (mem_derivations_iff B W D.val).mp D.property
  exact ⟨BilinearAutomorphism.exp_mem_group B D.val
    ((BilinearAutomorphism.mem_derivations_iff B D.val).mp hD.1), fun w => exp_fixes D.val (hD.2 w)⟩

omit [CompleteSpace V] in
theorem group_closed (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) :
    IsClosed (group B W : Set (V →L[ℝ] V)ˣ) := by
  have he : (group B W : Set (V →L[ℝ] V)ˣ) = (BilinearAutomorphism.group B : Set _) ∩
      ⋂ w : W, {u : (V →L[ℝ] V)ˣ | u.val w = w} := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [he]
  exact (BilinearAutomorphism.group_closed B).inter (isClosed_iInter fun w =>
    isClosed_eq (Units.continuous_val.clm_apply continuous_const) continuous_const)

omit [CompleteSpace V] in
theorem group_defect (B : V →L[ℝ] V →L[ℝ] V) (W : Submodule ℝ V) (u : group B W) :
    defect B W u.val.val = 0 := by
  apply Prod.ext
  · ext x y
    exact sub_eq_zero.mpr (u.property.1 x y)
  · ext w
    exact sub_eq_zero.mpr (u.property.2 w)

end MathieuProperty.BilinearStabilizer
