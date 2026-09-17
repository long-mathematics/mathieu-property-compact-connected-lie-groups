import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
/-! Exponentials of bounded derivations preserve a continuous bilinear operation.
The proof differentiates the conjugated operation along the exponential curve. -/

noncomputable section
namespace MathieuProperty
namespace DerivationExponential
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
open NormedSpace

theorem exp_mul_exp_neg (D : V →L[ℝ] V) : exp D * exp (-D) = (1 : V →L[ℝ] V) := by
  have hD : D ∈ Metric.eball (0 : V →L[ℝ] V) (expSeries ℝ (V →L[ℝ] V)).radius := by
    simp [expSeries_radius_eq_top]
  have hn : -D ∈ Metric.eball (0 : V →L[ℝ] V) (expSeries ℝ (V →L[ℝ] V)).radius := by
    simp [expSeries_radius_eq_top]
  rw [← exp_add_of_commute_of_mem_ball (Commute.refl D).neg_right hD hn, add_neg_cancel, exp_zero]

theorem exp_preserves_bilinear (B : V →L[ℝ] V →L[ℝ] V) (D : V →L[ℝ] V)
    (hD : ∀ x y, D (B x y) = B (D x) y + B x (D y)) (x y : V) :
    exp D (B x y) = B (exp D x) (exp D y) := by
  let u : ℝ → V →L[ℝ] V := fun t => exp (t • D)
  let i : ℝ → V →L[ℝ] V := fun t => exp (t • (-D))
  let w : ℝ → V := fun t => B (u t x) (u t y)
  let φ : ℝ → V := fun t => i t (w t)
  have hu (t : ℝ) (z : V) : HasDerivAt (fun s => u s z) (D (u t z)) t := by
    simpa only [mul_apply_eq_comp, map_zero, add_zero] using
      (hasDerivAt_exp_smul_const' D t).clm_apply (hasDerivAt_const t z)
  have hw (t : ℝ) : HasDerivAt w (D (w t)) t := by
    have h := B.hasDerivAt_of_bilinear (fun _ => hu t x) (fun _ => hu t y)
    simpa only [w, hD, add_comm] using h
  have hφ (t : ℝ) : HasDerivAt φ 0 t := by
    have h := (hasDerivAt_exp_smul_const (-D) t).clm_apply (hw t)
    simpa only [mul_apply_eq_comp, neg_apply, map_neg,
      neg_add_cancel] using h
  have he := is_const_of_deriv_eq_zero (fun t => (hφ t).differentiableAt)
    (fun t => (hφ t).deriv) (1 : ℝ) 0
  simp only [φ,i,w,u,one_smul,zero_smul,exp_zero,one_apply_eq_self] at he
  have hi := exp_mul_exp_neg D
  have h := congrArg (fun z => exp D z) he
  change (exp D * exp (-D)) (B (exp D x) (exp D y)) = exp D (B x y) at h
  rw [hi] at h
  exact h.symm

def expUnit (D : V →L[ℝ] V) : (V →L[ℝ] V)ˣ where
  val := exp D
  inv := exp (-D)
  val_inv := exp_mul_exp_neg D
  inv_val := by simpa only [neg_neg] using exp_mul_exp_neg (-D)

end DerivationExponential
end MathieuProperty
