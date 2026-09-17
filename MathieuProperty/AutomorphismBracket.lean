import MathieuProperty.AutomorphismDifferential
/-! The Lie bracket of the actual automorphism group is the derivation commutator.
This is proved by differentiating the actual adjoint representation. -/

noncomputable section
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace BilinearAutomorphism
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def tangentVal (B : V →L[ℝ] V →L[ℝ] V)
    (X : GroupLieAlgebra 𝓘(ℝ,derivations B) (group B)) : V →L[ℝ] V :=
  (show derivations B from X).val

set_option maxHeartbeats 800000 in
theorem tangentVal_lie (B : V →L[ℝ] V →L[ℝ] V)
    (X Y : GroupLieAlgebra 𝓘(ℝ,derivations B) (group B)) :
    tangentVal B ⁅X,Y⁆ = tangentVal B X * tangentVal B Y - tangentVal B Y * tangentVal B X := by
  let ev : (derivations B →L[ℝ] derivations B) →L[ℝ] V →L[ℝ] V :=
    (derivations B).subtypeL.comp (ContinuousLinearMap.apply ℝ (derivations B) (show derivations B from Y))
  let A : group B → derivations B →L[ℝ] derivations B := ConnectedLie.adjoint
  let F : group B → V →L[ℝ] V := ev ∘ A
  have hA : ContMDiff 𝓘(ℝ,derivations B) 𝓘(ℝ,derivations B →L[ℝ] derivations B) ∞ A :=
    ConnectedLie.adjoint_smooth
  have hev : ContDiff ℝ ∞ ev := by
    exact ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := derivations B →L[ℝ] derivations B) (F := V →L[ℝ] V) ev
  have hF : ContMDiff 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) ∞ F := hev.contMDiff.comp hA
  have hd : (show V →L[ℝ] V from mfderiv 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) F 1 X) =
      tangentVal B ⁅X,Y⁆ := by
    rw [show F = ev ∘ A from rfl,
      mfderiv_comp (I' := 𝓘(ℝ,derivations B →L[ℝ] derivations B)) _
        (hev.contMDiff.mdifferentiableAt (by simp)) (hA.mdifferentiableAt (by simp))]
    erw [mfderiv_eq_fderiv]
    have hevD : fderiv ℝ ev (A 1) = ev :=
      (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
        (E := derivations B →L[ℝ] derivations B) (F := V →L[ℝ] V) ev).fderiv
    rw [hevD]
    exact congrArg (fun Z : derivations B => Z.val)
      (ConnectedLie.adjoint_mfderiv (G := group B) X Y)
  have hw : writtenInExtChartAt 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) (1 : group B) F =
      fun D => exponential B D * tangentVal B Y * exponential B (-D) := by
    funext D
    simp only [writtenInExtChartAt, Function.comp_def, extChart_symm_apply, one_mul,
      ext_chart_model_space_apply]
    change (ConnectedLie.adjoint (groupExponential B D) (show derivations B from Y)).val = _
    rw [adjoint_val]
    rfl
  have ho : extChartAt 𝓘(ℝ,derivations B) (1 : group B) 1 = 0 := by
    rw [extChart_apply, inv_mul_cancel, groupLogarithm_one]
  have hd' : (show derivations B →L[ℝ] V →L[ℝ] V from
      mfderiv 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) F 1) =
      fderiv ℝ (fun D => exponential B D * tangentVal B Y * exponential B (-D)) 0 := by
    simp only [mfderiv, ite_eq_left (hF.mdifferentiableAt (by simp)), hw, ho,
      ModelWithCorners.range_eq_univ, fderivWithin_univ]
    rfl
  calc
    tangentVal B ⁅X,Y⁆ = (show V →L[ℝ] V from
        mfderiv 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) F 1 X) := hd.symm
    _ = fderiv ℝ (fun D => exponential B D * tangentVal B Y * exponential B (-D)) 0 X :=
      congrArg (fun q : derivations B →L[ℝ] V →L[ℝ] V => q X) hd'
    _ = _ := fderiv_exponential_conjugation_apply B (tangentVal B Y) X

end BilinearAutomorphism
end MathieuProperty
