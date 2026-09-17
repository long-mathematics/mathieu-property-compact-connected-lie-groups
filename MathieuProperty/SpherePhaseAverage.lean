import MathieuProperty.SphereMonomials
import MathieuProperty.PolynomialPhase

/-! Continuous phase averaging on the actual sphere measure and its coefficient extraction. -/

noncomputable section
open MeasureTheory Polynomial
namespace MathieuProperty.Hopf

@[fun_prop] theorem continuous_diagonalPhase : Continuous diagonalPhase := by
  apply su2SphereHomeomorph.symm.continuous.comp
  apply continuous_induced_rng.mpr
  change Continuous (fun θ : ℝ => (Complex.exp (Complex.I * θ), (0 : ℂ)))
  fun_prop

def phaseAction (θ : ℝ) (z : Sphere) : Sphere := diagonalPhase (θ / 2) • z

@[fun_prop] theorem continuous_phaseAction :
    Continuous (fun p : ℝ × Sphere => phaseAction p.1 p.2) := by
  unfold phaseAction
  fun_prop

theorem phaseAction_tau (θ : ℝ) (z : Sphere) : tau (phaseAction θ z).val = tau z.val := by
  have hc : Complex.normSq (Complex.exp (Complex.I * (θ / 2))) = 1 := by
    simpa using normSq_phase 1 (θ / 2)
  simp [phaseAction, diagonalPhase_smul, tau, Complex.normSq_mul, hc]

theorem phaseAction_u (θ : ℝ) (z : Sphere) :
    u (phaseAction θ z).val = u z.val * Complex.exp (Complex.I * θ) := by
  have hc : Complex.exp (Complex.I * (θ / 2)) * Complex.exp (Complex.I * (θ / 2)) =
      Complex.exp (Complex.I * θ) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [phaseAction, diagonalPhase_smul, u, star_mul, star_star]
  push_cast
  calc
    _ = (2 * z.val.1 * star z.val.2) *
        (Complex.exp (Complex.I * (θ / 2)) * Complex.exp (Complex.I * (θ / 2))) := by ring
    _ = _ := by rw [hc]

theorem sphere_phase_average {f : Sphere → ℂ} (hf : Continuous f) :
    (∫ z, (∫ θ in (0 : ℝ)..(2 * Real.pi), f (phaseAction θ z)) ∂surfaceMeasure) =
      (2 * Real.pi : ℂ) * ∫ z, f z ∂surfaceMeasure := by
  have hL : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hi : Integrable (fun p : ℝ × Sphere => f (phaseAction p.1 p.2))
      ((volume.restrict (Set.Icc 0 (2 * Real.pi))).prod surfaceMeasure) := by
    have h := ContinuousOn.integrableOn_compact (μ := volume.prod surfaceMeasure)
      ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi))).prod isCompact_univ) (hf.comp continuous_phaseAction).continuousOn
    change Integrable _ ((volume.prod surfaceMeasure).restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.univ)) at h
    rw [← Measure.prod_restrict, Measure.restrict_univ] at h
    exact h
  simp_rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
  rw [← integral_integral_swap (f := fun θ z => f (phaseAction θ z)) hi]
  simp only [phaseAction, integral_smul_eq_self]
  simp [Complex.real_smul, mul_comm, max_eq_left (by positivity : (0 : ℝ) ≤ Real.pi * 2)]

def hopfKernel (H : Polynomial ℂ) (m : ℕ) (t : ℝ) : Polynomial ℂ :=
  H * (1 + X) ^ m * (1 - C ((t : ℂ) ^ 2) * (1 + X) ^ 2) ^ m

theorem p_eq_localization (z : Sphere) (hz : u z.val ≠ 0) :
    p z = (u z.val)⁻¹ * (1 + u z.val) *
      (1 - (1 + u z.val) ^ 2 * (tau z.val : ℂ) ^ 2) := by
  apply mul_left_cancel₀ hz
  change u z.val * P z.val = _
  rw [defect_one z.val z.property]
  field_simp

theorem phase_hopf_integrand (H : Polynomial ℂ) (m : ℕ) (z : Sphere)
    (hz : u z.val ≠ 0) (θ : ℝ) :
    H.eval (q (phaseAction θ z)) * p (phaseAction θ z) ^ m =
      (u z.val * Complex.exp (Complex.I * θ)) ^ (-(m : ℤ)) *
        (hopfKernel H m (tau z.val)).eval (u z.val * Complex.exp (Complex.I * θ)) := by
  have hphase : u (phaseAction θ z).val ≠ 0 := by
    rw [phaseAction_u]
    exact mul_ne_zero hz (Complex.exp_ne_zero _)
  rw [p_eq_localization _ hphase, phaseAction_tau]
  simp only [q, Q, phaseAction_u, hopfKernel, eval_mul, eval_pow, eval_sub, eval_one,
    eval_add, eval_X, eval_C, mul_pow, zpow_neg, zpow_natCast]
  ring

theorem phase_hopf_integral (H : Polynomial ℂ) (m : ℕ) (z : Sphere) (hz : u z.val ≠ 0) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), H.eval (q (phaseAction θ z)) * p (phaseAction θ z) ^ m) =
      (2 * Real.pi : ℂ) * (hopfKernel H m (tau z.val)).coeff m := by
  simp_rw [phase_hopf_integrand H m z hz]
  exact polynomial_phase_coefficient _ _ hz m

/-- The rigorous phase-extraction step, with the exceptional endpoint circles removed
only almost everywhere, and Fubini justified for the continuous polynomial integrand. -/
theorem sphere_hopf_constantTerm (H : Polynomial ℂ) (m : ℕ) :
    (∫ z, H.eval (q z) * p z ^ m ∂surfaceMeasure) =
      ∫ z, (hopfKernel H m (tau z.val)).coeff m ∂surfaceMeasure := by
  have havg := sphere_phase_average (f := fun z => H.eval (q z) * p z ^ m)
    ((H.continuous.comp continuous_q).mul (continuous_p.pow m))
  have hae : (fun z : Sphere => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      H.eval (q (phaseAction θ z)) * p (phaseAction θ z) ^ m) =ᵐ[surfaceMeasure]
      (fun z => (2 * Real.pi : ℂ) * (hopfKernel H m (tau z.val)).coeff m) := by
    filter_upwards [u_ne_zero_ae] with z hz
    exact phase_hopf_integral H m z hz
  rw [integral_congr_ae hae, integral_const_mul] at havg
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi))
  exact (mul_left_cancel₀ hpi havg).symm

end MathieuProperty.Hopf
