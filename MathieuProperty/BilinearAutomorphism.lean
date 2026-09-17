import MathieuProperty.DerivationExponential
/-! The closed matrix subgroup preserving a continuous bilinear operation. -/

noncomputable section
namespace MathieuProperty
namespace BilinearAutomorphism
open DerivationExponential
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def group (B : V →L[ℝ] V →L[ℝ] V) : Subgroup (V →L[ℝ] V)ˣ where
  carrier := {u | ∀ x y, u.val (B x y) = B (u.val x) (u.val y)}
  one_mem' := by intro x y; rfl
  mul_mem' {u v} hu hv := by
    intro x y
    change u.val (v.val (B x y)) = B (u.val (v.val x)) (u.val (v.val y))
    rw [hv,hu]
  inv_mem' {u} hu := by
    intro x y
    apply (ContinuousLinearEquiv.ofUnit u).injective
    change u.val (u.inv (B x y)) = u.val (B (u.inv x) (u.inv y))
    rw [hu]
    have hi (v : V) : u.val (u.inv v) = v := by
      change (u.val*u.inv) v = v
      rw [u.val_inv]
      rfl
    simp only [hi]

theorem exp_mem_group (B : V →L[ℝ] V →L[ℝ] V) (D : V →L[ℝ] V)
    (hD : ∀ x y, D (B x y) = B (D x) y + B x (D y)) : expUnit D ∈ group B :=
  exp_preserves_bilinear B D hD

omit [CompleteSpace V] in
theorem group_closed (B : V →L[ℝ] V →L[ℝ] V) : IsClosed (group B : Set (V →L[ℝ] V)ˣ) := by
  have he : (group B : Set (V →L[ℝ] V)ˣ) =
      ⋂ x : V, ⋂ y : V, {u : (V →L[ℝ] V)ˣ | u.val (B x y) = B (u.val x) (u.val y)} := by
    ext u
    change (∀ x y, u.val (B x y) = B (u.val x) (u.val y)) ↔ _
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [he]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  exact isClosed_eq (Units.continuous_val.clm_apply continuous_const)
    ((B.continuous.comp (Units.continuous_val.clm_apply continuous_const)).clm_apply
      (Units.continuous_val.clm_apply continuous_const))
end BilinearAutomorphism
end MathieuProperty
