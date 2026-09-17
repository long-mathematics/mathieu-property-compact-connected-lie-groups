import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
/-! Mixed derivatives used in the infinitesimal adjoint calculation.
The final generic lemma differentiates a local identity `R(a) A(a) = L(a)`.
It does not assume or state the compact-group decomposition theorem.
-/
noncomputable section
namespace MathieuProperty
namespace LieMixed
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def leftPartial (μ : E × E → F) (a₀ v a : E) : F := fderiv ℝ μ (a,a₀) (0,v)
def rightPartial (μ : E × E → F) (a₀ v a : E) : F := fderiv ℝ μ (a₀,a) (v,0)

omit [CompleteSpace F] in
theorem leftPartial_eq_deriv (μ : E × E → F) (a₀ v a : E)
    (hμ : DifferentiableAt ℝ μ (a,a₀)) :
    leftPartial μ a₀ v a = fderiv ℝ (fun b => μ (a,b)) a₀ v := by
  have hc := hμ.hasFDerivAt.comp (f := fun b : E => (a,b)) a₀
    ((hasFDerivAt_const a a₀).prodMk (hasFDerivAt_id a₀))
  have hv := congrArg (fun f : E →L[ℝ] F => f v) hc.fderiv
  unfold leftPartial
  simpa [Function.comp_def] using hv.symm

omit [CompleteSpace F] in
theorem rightPartial_eq_deriv (μ : E × E → F) (a₀ v a : E)
    (hμ : DifferentiableAt ℝ μ (a₀,a)) :
    rightPartial μ a₀ v a = fderiv ℝ (fun b => μ (b,a)) a₀ v := by
  have hc := hμ.hasFDerivAt.comp (f := fun b : E => (b,a)) a₀
    ((hasFDerivAt_id a₀).prodMk (hasFDerivAt_const a a₀))
  have hv := congrArg (fun f : E →L[ℝ] F => f v) hc.fderiv
  unfold rightPartial
  simpa [Function.comp_def] using hv.symm

omit [CompleteSpace F] in
theorem leftPartial_fderiv (μ : E × E → F) (a₀ v x : E)
    (hμ : ContDiffAt ℝ 2 μ (a₀,a₀)) :
    fderiv ℝ (leftPartial μ a₀ v) a₀ x =
      fderiv ℝ (fderiv ℝ μ) (a₀,a₀) (x,0) (0,v) := by
  have hd := (hμ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc := hd.hasFDerivAt.comp (f := fun a : E => (a,a₀)) a₀ ((hasFDerivAt_id a₀).prodMk (hasFDerivAt_const a₀ a₀))
  have he := hc.clm_apply (hasFDerivAt_const (0,v) a₀)
  have hv := congrArg (fun f : E →L[ℝ] F => f x) he.fderiv
  unfold leftPartial
  simpa [ContinuousLinearMap.comp_apply] using hv

omit [CompleteSpace F] in
theorem rightPartial_fderiv (μ : E × E → F) (a₀ v x : E)
    (hμ : ContDiffAt ℝ 2 μ (a₀,a₀)) :
    fderiv ℝ (rightPartial μ a₀ v) a₀ x =
      fderiv ℝ (fderiv ℝ μ) (a₀,a₀) (0,x) (v,0) := by
  have hd := (hμ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc := hd.hasFDerivAt.comp (f := fun a : E => (a₀,a)) a₀ ((hasFDerivAt_const a₀ a₀).prodMk (hasFDerivAt_id a₀))
  have he := hc.clm_apply (hasFDerivAt_const (v,0) a₀)
  have hv := congrArg (fun f : E →L[ℝ] F => f x) he.fderiv
  unfold rightPartial
  simpa [ContinuousLinearMap.comp_apply] using hv

theorem mixed_commute (μ : E × E → F) (a₀ v x : E)
    (hμ : ContDiffAt ℝ 2 μ (a₀,a₀)) :
    fderiv ℝ (leftPartial μ a₀ v) a₀ x =
      fderiv ℝ (rightPartial μ a₀ x) a₀ v := by
  rw [leftPartial_fderiv μ a₀ v x hμ, rightPartial_fderiv μ a₀ x v hμ]
  exact hμ.isSymmSndFDerivAt (by simp) (x,0) (0,v)
theorem adjoint_derivative (μ : E × E → E) (a₀ v x : E)
    (A : E → E →L[ℝ] E) (hμ : ContDiffAt ℝ 2 μ (a₀,a₀))
    (hA : DifferentiableAt ℝ A a₀) (hA₀ : A a₀ = ContinuousLinearMap.id ℝ E)
    (hR₀ : ∀ w : E, fderiv ℝ μ (a₀,a₀) (w,0) = w)
    (hrel : (fun a => rightPartial μ a₀ (A a v) a) =ᶠ[nhds a₀] leftPartial μ a₀ v)
    [CompleteSpace E] :
    fderiv ℝ A a₀ x v = fderiv ℝ (leftPartial μ a₀ v) a₀ x -
      fderiv ℝ (leftPartial μ a₀ x) a₀ v := by
  have hd := (hμ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hr := hd.hasFDerivAt.comp (f := fun a : E => (a₀,a)) a₀
    ((hasFDerivAt_const a₀ a₀).prodMk (hasFDerivAt_id a₀))
  have ha := hA.hasFDerivAt.clm_apply (hasFDerivAt_const v a₀)
  have hp := ha.prodMk (hasFDerivAt_const (0 : E) a₀)
  have he := (hr.clm_apply hp).fderiv
  have he' := congrArg (fun f : E →L[ℝ] E => f x) he
  have hh := hrel.fderiv_eq (𝕜 := ℝ)
  unfold rightPartial at hh
  dsimp only [Function.comp_def] at he'
  rw [hh] at he'
  simp [hA₀, hR₀, ContinuousLinearMap.comp_apply] at he'
  rw [← rightPartial_fderiv μ a₀ v x hμ,
    ← mixed_commute μ a₀ x v hμ] at he'
  exact eq_sub_of_add_eq (by simpa [add_comm] using he'.symm)
end LieMixed
end MathieuProperty
