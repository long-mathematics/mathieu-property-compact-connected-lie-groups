import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
/-! The smooth bracket-preservation equations and their linearization at identity.
Their derivative kernel is exactly the subspace of bounded derivations. -/

noncomputable section
open scoped ContDiff
namespace MathieuProperty
namespace BilinearAutomorphism
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def defect (B : V →L[ℝ] V →L[ℝ] V) (T : V →L[ℝ] V) : V →L[ℝ] V →L[ℝ] V :=
  (ContinuousLinearMap.compL ℝ V V V T).comp B - ((B.precompR V).flip T).comp T

theorem defect_apply (B : V →L[ℝ] V →L[ℝ] V) (T : V →L[ℝ] V) (x y : V) :
    defect B T x y = T (B x y) - B (T x) (T y) := rfl

theorem defect_smooth (B : V →L[ℝ] V →L[ℝ] V) : ContDiff ℝ ∞ (defect B) := by
  unfold defect
  exact ((ContinuousLinearMap.compL ℝ V V V).contDiff.clm_comp contDiff_const).sub
    ((B.precompR V).flip.contDiff.clm_comp contDiff_id)

theorem defect_one (B : V →L[ℝ] V →L[ℝ] V) : defect B 1 = 0 := by
  ext x y
  simp [defect_apply]

def linearDefect (B : V →L[ℝ] V →L[ℝ] V) :
    (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V →L[ℝ] V := fderiv ℝ (defect B) 1

set_option backward.isDefEq.respectTransparency false in
theorem linearDefect_apply (B : V →L[ℝ] V →L[ℝ] V) (D : V →L[ℝ] V) (x y : V) :
    linearDefect B D x y = D (B x y) - (B x (D y) + B (D x) y) := by
  let ex := ContinuousLinearMap.apply ℝ V x
  let ey := ContinuousLinearMap.apply ℝ V y
  let ex₂ := ContinuousLinearMap.apply ℝ (V →L[ℝ] V) x
  have hd : HasFDerivAt (defect B) (linearDefect B) 1 :=
    ((defect_smooth B).differentiable (by simp) 1).hasFDerivAt
  have hx : HasFDerivAt (fun T : V →L[ℝ] V => defect B T x)
      (ex₂.comp (linearDefect B)) (1 : V →L[ℝ] V) := by
    have hx₀ : HasFDerivAt (fun A : V →L[ℝ] V →L[ℝ] V => ex₂ A) ex₂ (defect B 1) := ex₂.hasFDerivAt
    exact HasFDerivAt.comp (𝕜 := ℝ) (f := defect B) (f' := linearDefect B) (g := fun A => ex₂ A) (g' := ex₂) (1 : V →L[ℝ] V) hx₀ hd
  have he : HasFDerivAt (fun T : V →L[ℝ] V => defect B T x y)
      (ey.comp (ex₂.comp (linearDefect B))) (1 : V →L[ℝ] V) := by
    have hy₀ : HasFDerivAt (fun A : V →L[ℝ] V => ey A) ey (defect B 1 x) := ey.hasFDerivAt
    exact HasFDerivAt.comp (𝕜 := ℝ) (1 : V →L[ℝ] V) hy₀ hx
  have hc := ((ContinuousLinearMap.apply ℝ V (B x y)).hasFDerivAt (x := (1 : V →L[ℝ] V))).sub
    (B.hasFDerivAt_of_bilinear (ex.hasFDerivAt (x := (1 : V →L[ℝ] V))) (ey.hasFDerivAt (x := (1 : V →L[ℝ] V))))
  change HasFDerivAt (fun T : V →L[ℝ] V => defect B T x y) _ 1 at he hc
  have h := congrArg (fun q : (V →L[ℝ] V) →L[ℝ] V => q D) (he.unique hc)
  simpa [ex,ey,ex₂] using h
def derivations (B : V →L[ℝ] V →L[ℝ] V) : Submodule ℝ (V →L[ℝ] V) := (linearDefect B).ker

theorem mem_derivations_iff (B : V →L[ℝ] V →L[ℝ] V) (D : V →L[ℝ] V) :
    D ∈ derivations B ↔ ∀ x y, D (B x y) = B (D x) y + B x (D y) := by
  change linearDefect B D = 0 ↔ _
  constructor
  · intro h x y
    have hxy := congrArg (fun A : V →L[ℝ] V →L[ℝ] V => A x y) h
    change linearDefect B D x y = 0 at hxy
    rw [linearDefect_apply] at hxy
    simpa only [add_comm] using sub_eq_zero.mp hxy
  · intro h
    ext x y
    simp only [linearDefect_apply, h, zero_apply]
    abel

theorem derivations_closed (B : V →L[ℝ] V →L[ℝ] V) : IsClosed (derivations B : Set (V →L[ℝ] V)) :=
  (linearDefect B).isClosed_ker
end BilinearAutomorphism
end MathieuProperty
