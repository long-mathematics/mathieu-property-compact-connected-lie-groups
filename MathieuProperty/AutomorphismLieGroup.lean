import MathieuProperty.AutomorphismManifold
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
/-! The actual bilinear automorphism group is a real-analytic Lie group.
Its matrix embedding is smooth and its differential at identity is inclusion of derivations. -/

noncomputable section
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace BilinearAutomorphism
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem extChart_apply (B : V →L[ℝ] V →L[ℝ] V) (g u : group B) :
    extChartAt 𝓘(ℝ,derivations B) g u = groupLogarithm B (g⁻¹*u) :=
  translatedChart_apply B g u

theorem extChart_symm_apply (B : V →L[ℝ] V →L[ℝ] V) (g : group B) (D : derivations B) :
    (extChartAt 𝓘(ℝ,derivations B) g).symm D = g * groupExponential B D :=
  translatedChart_symm_apply B g D

theorem val_contMDiff (B : V →L[ℝ] V →L[ℝ] V) :
    ContMDiff 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) ω (fun u : group B => u.val.val) := by
  intro u
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  have hm : ContDiff ℝ ω (fun D : derivations B => u.val.val * exponential B D) :=
    contDiff_const.mul (exponential_analytic B)
  simpa only [Function.comp_def, extChart_symm_apply] using! hm.contDiffWithinAt


theorem contMDiffAt_of_val (B : V →L[ℝ] V →L[ℝ] V)
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ∞ω} {f : M → group B} {x : M} (hc : ContinuousAt f x)
    (hf : ContMDiffAt I 𝓘(ℝ,V →L[ℝ] V) n (fun y => (f y).val.val) x) :
    ContMDiffAt I 𝓘(ℝ,derivations B) n f x := by
  apply contMDiffAt_iff_target.mpr
  refine ⟨hc, ?_⟩
  have hm : ContMDiffAt I 𝓘(ℝ,V →L[ℝ] V) n
      (fun y => (f x).val.inv * (f y).val.val) x := contMDiffAt_const.clm_comp hf
  have hl : ContMDiffAt 𝓘(ℝ,V →L[ℝ] V) 𝓘(ℝ,derivations B) n (logarithm B)
      ((f x).val.inv * (f x).val.val) := by
    rw [(f x).val.inv_val, contMDiffAt_iff_contDiffAt]
    exact (logarithm_analyticAt_one B).of_le le_top
  simpa only [Function.comp_def, extChart_apply, groupLogarithm] using! hl.comp x hm

theorem units_contMDiff (B : V →L[ℝ] V →L[ℝ] V) :
    ContMDiff 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) ω
      (fun u : group B => u.val) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact val_contMDiff B

theorem inverse_val_contMDiff (B : V →L[ℝ] V →L[ℝ] V) :
    ContMDiff 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) ω (fun u : group B => u.val.inv) :=
  Units.contMDiff_val.comp ((contMDiff_inv 𝓘(ℝ,V →L[ℝ] V) ω).comp (units_contMDiff B))

instance lieGroup (B : V →L[ℝ] V →L[ℝ] V) : LieGroup 𝓘(ℝ,derivations B) ω (group B) where
  contMDiff_mul := by
    intro p
    apply contMDiffAt_of_val B continuous_mul.continuousAt
    exact ((val_contMDiff B).comp contMDiff_fst).contMDiffAt.clm_comp
      ((val_contMDiff B).comp contMDiff_snd).contMDiffAt
  contMDiff_inv := by
    intro u
    exact contMDiffAt_of_val B continuous_inv.continuousAt ((inverse_val_contMDiff B) u)


theorem val_mfderiv_one (B : V →L[ℝ] V →L[ℝ] V) :
    (show derivations B →L[ℝ] V →L[ℝ] V from
      mfderiv 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) (fun u : group B => u.val.val) 1) =
      (derivations B).subtypeL := by
  have hf := (val_contMDiff B (1 : group B)).mdifferentiableAt (by simp)
  have hw : writtenInExtChartAt 𝓘(ℝ,derivations B) 𝓘(ℝ,V →L[ℝ] V) (1 : group B)
      (fun u : group B => u.val.val) = exponential B := by
    funext D
    simp only [writtenInExtChartAt, Function.comp_def, extChart_symm_apply, one_mul,
      ext_chart_model_space_apply]
    rfl
  have ho : extChartAt 𝓘(ℝ,derivations B) (1 : group B) 1 = 0 := by
    rw [extChart_apply, inv_mul_cancel, groupLogarithm_one]
  simpa only [mfderiv, ite_eq_left hf, hw, ho, ModelWithCorners.range_eq_univ,
    fderivWithin_univ,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using!
      (exponential_strictDeriv B).hasFDerivAt.fderiv

end BilinearAutomorphism
end MathieuProperty
