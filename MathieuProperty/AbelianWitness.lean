import MathieuProperty.AbelianConstantTerm

/-! The exact weighted constant-term functional and Pascal moments of the transformed witness. -/
noncomputable section
open MeasureTheory Polynomial
namespace MathieuProperty.Abelian

theorem weighted_quadratic_substitution (f : ℝ → ℂ) (hf : Continuous f)
    (heven : ∀ t : ℝ, f (-t) = f t) :
    2 * (∫ x in (0 : ℝ)..1, f (1 - 2*x^2) * (x : ℂ)) = ∫ t in (0 : ℝ)..1, f t := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => 1-2*x^2) (-4*x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (((hasDerivAt_id x).pow 2).const_mul 2) using 1
    · funext y; simp
    · simp; ring
  have hc := intervalIntegral.integral_deriv_smul_comp (a := (0 : ℝ)) (b := 1)
    (fun x _ => hd x) (by fun_prop : ContinuousOn (fun x : ℝ => -4*x) (Set.uIcc 0 1)) hf
  have hg : (fun x : ℝ => (-4*x) • (f ∘ (fun x => 1-2*x^2)) x) =
      (fun x : ℝ => (-4 : ℂ) * (f (1-2*x^2)*(x : ℂ))) := by
    funext x
    simp only [Function.comp_apply, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    ring
  rw [hg, intervalIntegral.integral_const_mul] at hc
  norm_num only [zero_pow (by omega : 2 ≠ 0), mul_zero, sub_zero, one_pow, mul_one,
    show (1 : ℝ)-2 = -1 by norm_num] at hc
  have hn := intervalIntegral.integral_comp_neg f (a := 0) (b := 1)
  simp only [heven, neg_zero] at hn
  have ha : (∫ t in (-1 : ℝ)..0, f t) + (∫ t in (0 : ℝ)..1, f t) =
      ∫ t in (-1 : ℝ)..1, f t := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-1) 0) (hf.intervalIntegrable 0 1)
  rw [← hn] at ha
  rw [intervalIntegral.integral_symm (a := (-1 : ℝ)) (b := 1)] at hc
  rw [← ha] at hc
  linear_combination (-1/2 : ℂ) * hc


/-- The normalized weighted constant-term functional printed in Proposition 9.1. -/
def weightedCT (f : Laurent) : ℂ :=
  2 * ∫ x in (0 : ℝ)..1, (f.coeff 0).eval (x : ℂ) * (x : ℂ)

theorem weightedCT_moment (m s : ℕ) :
    weightedCT (formalQ ^ s * formalP ^ m) =
      ∫ t in (0 : ℝ)..1, (Hopf.hopfKernel (X ^ s) m t).coeff m := by
  unfold weightedCT
  have hi : (∫ x in (0 : ℝ)..1, ((formalQ^s*formalP^m).coeff 0).eval (x : ℂ)*(x : ℂ)) =
      ∫ x in (0 : ℝ)..1, (Hopf.hopfKernel (X^s) m (1-2*x^2)).coeff m*(x : ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    exact congrArg (fun z : ℂ => z * (x : ℂ)) (formal_moment_coeff x hx m s)
  rw [hi]
  simp_rw [← Hopf.hopfHeightPolynomial_eval]
  exact weighted_quadratic_substitution _
    ((Hopf.hopfHeightPolynomial (X^s) m).continuous.comp Complex.continuous_ofReal)
    (Hopf.hopfHeightPolynomial_even (X^s) m)

theorem weightedCT_pure (m : ℕ) (hm : 1 ≤ m) : weightedCT (formalP ^ m) = 0 := by
  have h := weightedCT_moment m 0
  simp only [pow_zero, one_mul] at h
  rw [h]
  unfold Hopf.hopfKernel
  rw [hopf_integrated_coefficient m hm 1, one_mul, pure_pascal_coefficient m hm, mul_zero]

theorem weightedCT_marked (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    weightedCT (formalQ ^ s * formalP ^ m) =
      (momentConstant m : ℂ) * ((m-1).choose (s-1) : ℂ) := by
  rw [weightedCT_moment]
  unfold Hopf.hopfKernel
  rw [hopf_integrated_coefficient m hm, pascal_coefficient m s hm hs]

theorem weightedCT_marked_zero (m s : ℕ) (hm : 1 ≤ m) (hsm : m < s) :
    weightedCT (formalQ ^ s * formalP ^ m) = 0 := by
  rw [weightedCT_marked m s hm (by omega), Nat.choose_eq_zero_of_lt (by omega),
    Nat.cast_zero, mul_zero]

theorem weightedCT_marked_positive (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∃ c : ℝ, 0 < c ∧ weightedCT (formalQ ^ s * formalP ^ m) = (c : ℂ) := by
  refine ⟨momentConstant m * ((m-1).choose (s-1) : ℝ), pascal_marker_pos m s hm hs hsm, ?_⟩
  rw [weightedCT_marked m s hm hs]
  push_cast
  rfl

/-- The full moment and spectrum assertions of the explicit Laurent-witness proposition.
The separate external group-coordinate transform correspondence remains tracked in the ledger. -/
theorem explicit_laurent_witness :
    (∀ m : ℕ, 1 ≤ m → weightedCT (formalP ^ m) = 0) ∧
    (∀ m s : ℕ, 1 ≤ m → 1 ≤ s → weightedCT (formalQ ^ s * formalP ^ m) =
      (momentConstant m : ℂ) * ((m-1).choose (s-1) : ℂ)) ∧
    formalP.coeff.support = {-1, 0, 1, 2} :=
  ⟨weightedCT_pure, weightedCT_marked, formal_spectrum⟩

end MathieuProperty.Abelian
