import MathieuProperty.AutomorphismLieGroup
import MathieuProperty.ConnectedLie
/-! The local logarithm derivative and the actual adjoint action on derivations.
Conjugation by an automorphism preserves derivations, and infinitesimal conjugation
has the operator commutator as its derivative. -/

noncomputable section
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace BilinearAutomorphism
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem logarithm_hasFDerivAt_one (B : V →L[ℝ] V →L[ℝ] V) :
    HasFDerivAt (logarithm B) (FiniteSlice.projection (derivations B)) 1 := by
  have hi : HasFDerivAt (exponentialCoordinates B).symm
      (ContinuousLinearMap.id ℝ (derivations B)) 0 := by
    simpa only [exponentialProjection_zero, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.coe_refl] using! (exponentialProjection_strictDeriv B).to_localInverse.hasFDerivAt
  have hp : HasFDerivAt (fun T : V →L[ℝ] V =>
      FiniteSlice.projection (derivations B) (T-1)) (FiniteSlice.projection (derivations B)) 1 := by
    simpa only [ContinuousLinearMap.comp_id] using!
      (FiniteSlice.projection (derivations B)).hasFDerivAt.comp (1 : V →L[ℝ] V)
        ((hasFDerivAt_id (1 : V →L[ℝ] V)).sub_const 1)
  have hi' : HasFDerivAt (exponentialCoordinates B).symm
      (ContinuousLinearMap.id ℝ (derivations B)) (FiniteSlice.projection (derivations B) (1-1)) := by
    simpa using! hi
  simpa only [ContinuousLinearMap.id_comp] using! hi'.comp (1 : V →L[ℝ] V) hp

def conjugationOperator (B : V →L[ℝ] V →L[ℝ] V) (g : group B) :
    (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V :=
  (ContinuousLinearMap.compL ℝ V V V g.val.val).comp
    ((ContinuousLinearMap.compL ℝ V V V).flip g.val.inv)

omit [FiniteDimensional ℝ V] in
theorem conjugationOperator_apply (B : V →L[ℝ] V →L[ℝ] V) (g : group B) (D : V →L[ℝ] V) :
    conjugationOperator B g D = g.val.val * D * g.val.inv := rfl

theorem adjoint_eq_projection (B : V →L[ℝ] V →L[ℝ] V) (g : group B) :
    ConnectedLie.adjoint (E := derivations B) g =
      (FiniteSlice.projection (derivations B)).comp
        ((conjugationOperator B g).comp (derivations B).subtypeL) := by
  let c : group B → group B := fun u => g*u*g⁻¹
  have hc : ContMDiff 𝓘(ℝ,derivations B) 𝓘(ℝ,derivations B) ∞ c :=
    contMDiff_mul_right.comp contMDiff_mul_left
  have hw : writtenInExtChartAt 𝓘(ℝ,derivations B) 𝓘(ℝ,derivations B) (1 : group B) c =
      fun D => logarithm B (conjugationOperator B g (exponential B D)) := by
    funext D
    simp only [writtenInExtChartAt, Function.comp_def, extChart_symm_apply, one_mul]
    have h1 : c 1 = 1 := by simp [c]
    rw [h1, extChart_apply]
    simp only [inv_one, one_mul]
    rfl
  have hi : conjugationOperator B g (exponential B 0) = 1 := by
    rw [conjugationOperator_apply, exponential_zero, mul_one, g.val.val_inv]
  have hlog : HasFDerivAt (logarithm B) (FiniteSlice.projection (derivations B))
      (conjugationOperator B g (exponential B 0)) := hi.symm ▸ logarithm_hasFDerivAt_one B
  have he := (conjugationOperator B g).hasFDerivAt.comp (0 : derivations B)
    (exponential_strictDeriv B).hasFDerivAt
  have hd := hlog.comp (0 : derivations B) he
  have ho : extChartAt 𝓘(ℝ,derivations B) (1 : group B) 1 = 0 := by
    rw [extChart_apply, inv_mul_cancel, groupLogarithm_one]
  change (show derivations B →L[ℝ] derivations B from
    mfderiv 𝓘(ℝ,derivations B) 𝓘(ℝ,derivations B) c 1) = _
  simpa only [mfderiv,
    ite_eq_left (hc.mdifferentiableAt (by simp)), hw, ho,
    ModelWithCorners.range_eq_univ, fderivWithin_univ,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using! hd.fderiv


omit [FiniteDimensional ℝ V] in
theorem conjugationOperator_mem (B : V →L[ℝ] V →L[ℝ] V) (g : group B) (D : derivations B) :
    conjugationOperator B g D.val ∈ derivations B := by
  rw [mem_derivations_iff]
  intro x y
  change g.val.val (D.val (g.val.inv (B x y))) =
    B (g.val.val (D.val (g.val.inv x))) y + B x (g.val.val (D.val (g.val.inv y)))
  have hi (z : V) : g.val.val (g.val.inv z) = z := by
    change (g.val.val * g.val.inv) z = z
    rw [g.val.val_inv]
    rfl
  have hgi : g.val.inv (B x y) = B (g.val.inv x) (g.val.inv y) := (g⁻¹).property x y
  rw [hgi, (mem_derivations_iff B D.val).mp D.property, map_add,
    g.property, g.property, hi, hi]

theorem adjoint_val (B : V →L[ℝ] V →L[ℝ] V) (g : group B) (D : derivations B) :
    (ConnectedLie.adjoint (E := derivations B) g D).val = g.val.val * D.val * g.val.inv := by
  rw [adjoint_eq_projection]
  exact congrArg Subtype.val (FiniteSlice.projection_self (derivations B)
    ⟨conjugationOperator B g D.val, conjugationOperator_mem B g D⟩)


theorem fderiv_exponential_conjugation_apply (B : V →L[ℝ] V →L[ℝ] V)
    (Y : V →L[ℝ] V) (D : derivations B) :
    fderiv ℝ (fun X : derivations B => exponential B X * Y * exponential B (-X)) 0 D =
      D.val * Y - Y * D.val := by
  have hn := HasFDerivAt.comp (𝕜 := ℝ) (f := fun X : derivations B => -X)
    (f' := -(ContinuousLinearMap.id ℝ (derivations B)))
    (g := exponential B) (g' := (derivations B).subtypeL) (0 : derivations B)
    (by simpa using! (exponential_strictDeriv B).hasFDerivAt)
    ((hasFDerivAt_id (0 : derivations B)).neg)
  have hp := ((exponential_strictDeriv B).hasFDerivAt.clm_comp
    (hasFDerivAt_const Y (0 : derivations B))).clm_comp hn
  change HasFDerivAt (fun X : derivations B => exponential B X * Y * exponential B (-X)) _ 0 at hp
  rw [hp.fderiv]
  ext v
  simp [sub_eq_add_neg, add_comm]


end BilinearAutomorphism
end MathieuProperty
