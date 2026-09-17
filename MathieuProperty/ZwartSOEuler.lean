import MathieuProperty.ZwartSignedCube
/-! The radial weights obtained from the well-defined SO Euler blocks.

This module deliberately does not define the malformed printed recurrence
as a conjecture. See FORMALIZATION_STATUS.md for the external indexing issue.
The cosine substitution, dimensions, half-integer powers, and flat-coordinate
counterexample for this separately specified family are all proved here.
-/

noncomputable section
open MeasureTheory
namespace MathieuProperty.Zwart

theorem cosine_weight_substitution (F : ℝ → ℂ) (hF : Continuous F) (k : ℕ) :
    (∫ φ in (0 : ℝ)..Real.pi, F (Real.cos φ) * (Real.sin φ : ℂ)^(k+1)) =
      ∫ x in (-1 : ℝ)..1, F x * (Real.sqrt (1-x^2) : ℂ)^k := by
  have hc : Continuous (fun x : ℝ => F x * (Real.sqrt (1-x^2) : ℂ)^k) := by fun_prop
  have ht := intervalIntegral.integral_deriv_smul_comp (a := (0 : ℝ)) (b := Real.pi)
    (fun x _ => Real.hasDerivAt_cos x) (by fun_prop : ContinuousOn (fun x : ℝ => -Real.sin x) (Set.uIcc 0 Real.pi)) hc
  have hs (φ : ℝ) (hφ : φ ∈ Set.uIcc (0 : ℝ) Real.pi) :
      Real.sqrt (1-(Real.cos φ)^2) = Real.sin φ := by
    rw [Set.uIcc_of_le Real.pi_pos.le] at hφ
    have hsq : 1-(Real.cos φ)^2 = (Real.sin φ)^2 := by nlinarith [Real.sin_sq_add_cos_sq φ]
    rw [hsq, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 hφ.2)]
  have he : (∫ φ in (0 : ℝ)..Real.pi,
      (-Real.sin φ) • (fun x : ℝ => F x * (Real.sqrt (1-x^2) : ℂ)^k) (Real.cos φ)) =
      -(∫ φ in (0 : ℝ)..Real.pi, F (Real.cos φ) * (Real.sin φ : ℂ)^(k+1)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro φ hφ
    dsimp only
    rw [hs φ hφ, Complex.real_smul, Complex.ofReal_neg, pow_succ]
    ring
  change (∫ φ in (0 : ℝ)..Real.pi,
      (-Real.sin φ) • (fun x : ℝ => F x * (Real.sqrt (1-x^2) : ℂ)^k) (Real.cos φ)) = _ at ht
  rw [he] at ht
  simp only [Real.cos_zero, Real.cos_pi] at ht
  rw [intervalIntegral.integral_symm (a := (-1 : ℝ)) (b := 1)] at ht
  exact neg_injective ht
def soEulerPowers : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | 2 => []
  | n+3 => List.ofFn (fun j : Fin (n+1) => j.val) ++ soEulerPowers (n+2)

theorem soEulerPowers_length (n : ℕ) : (soEulerPowers (n+2)).length = (n+1).choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [soEulerPowers, ih, Nat.choose_succ_succ]; omega

def soEulerTail (n : ℕ) := (soEulerPowers (n+3)).tail

theorem soEulerPowers_head (n : ℕ) : soEulerPowers (n+3) = 0 :: soEulerTail n := by
  simp [soEulerPowers, soEulerTail, List.ofFn_succ]

abbrev soEulerRadialCount (n : ℕ) := (soEulerTail n).length+1

theorem soEulerRadialCount_eq (n : ℕ) : soEulerRadialCount n = (n+2)*(n+1)/2 := by
  have h := soEulerPowers_length (n+1)
  rw [soEulerPowers_head, List.length_cons] at h
  rw [soEulerRadialCount, h, Nat.choose_two_right]
  simp

def soEulerTailWeight (n : ℕ) (c : ℂ) (x : SignedCube (soEulerTail n).length) : ℂ :=
  c * ∏ i, (Real.sqrt (1-(x i).val^2) : ℂ)^((soEulerTail n).get i)

def soEulerDensity (n : ℕ) (c : ℂ) (x : SignedCube (soEulerRadialCount n)) : ℂ :=
  c * ∏ i, (Real.sqrt (1-(x i).val^2) : ℂ)^((0::soEulerTail n).get i)

theorem soEulerDensity_eq (n : ℕ) (c : ℂ) :
    soEulerDensity n c = (fun x => soEulerTailWeight n c (Fin.tail x)) := by
  funext x
  unfold soEulerDensity soEulerTailWeight
  rw [Fin.prod_univ_succ]
  simp [List.get_eq_getElem, Fin.tail]

theorem signed_sqrt_pow (x : SignedInterval) (k : ℕ) :
    (Real.sqrt (1-x.val^2))^k = (1-x.val^2)^((k : ℝ)/2) := by
  have hb : 0 ≤ 1-x.val^2 := by nlinarith [x.property.1, x.property.2]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb]
  congr 1
  ring

theorem soEulerDensity_rpow (n : ℕ) (c : ℂ) (x : SignedCube (soEulerRadialCount n)) :
    soEulerDensity n c x = c * ∏ i,
      ((1-(x i).val^2)^((((0::soEulerTail n).get i : ℕ) : ℝ)/2) : ℝ) := by
  unfold soEulerDensity
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Complex.ofReal_pow, signed_sqrt_pow]

/-- A separately specified radial conjecture obtained from the well-defined
Euler angular blocks. It is not identified with the malformed printed SO recurrence. -/
def SOEulerConvexSupportConjecture (n : ℕ) (c : ℂ) : Prop :=
  ConvexSupportConjecture (n+2) (signedRadialAlgebra (soEulerRadialCount n)) volume (soEulerDensity n c)

theorem soEuler_convexSupport_false (n : ℕ) (c : ℂ) : ¬ SOEulerConvexSupportConjecture n c := by
  unfold SOEulerConvexSupportConjecture
  rw [soEulerDensity_eq]
  exact signedCube_convexSupport_false (soEulerTail n).length ⟨0,by omega⟩ (soEulerTailWeight n c)

theorem soEuler_convexSupport_circles_false (n : ℕ) (c : ℂ) :
    ¬ (∀ f : FunctionLaurent (SignedCube (soEulerRadialCount n)) (n+2),
      Admissible (signedRadialAlgebra (soEulerRadialCount n)) f →
      (∀ m : ℕ, 1 ≤ m → (∫ x : SignedCube (soEulerRadialCount n),
        haarIntegral (Torus (n+2)) (circleEvaluation f x ^ m) * soEulerDensity n c x) = 0) →
      0 ∉ newtonPolytope f) := by
  intro h
  apply soEuler_convexSupport_false n c
  intro f hf hm
  apply h f hf
  intro m hmp
  have he := hm m hmp
  rw [weightedMoment_circles] at he
  simpa only [circleEvaluation_pow] using he
end MathieuProperty.Zwart
