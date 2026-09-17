import MathieuProperty.SphereDetermination
import MathieuProperty.EarlierXZ
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! The full normalized Hopf-coordinate measure formula.

A unit cube parametrizes the sphere by one squared radius and two phases.
Its coordinate moments factor into beta and integer-frequency integrals and
agree with the actual Euclidean surface moments. Moment determination proves
equality of measures. Affine substitutions recover the manuscript parameters
τ∈[-1,1], α,β∈[0,2π], with exact density 1/(8π²).
-/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Hopf

abbrev HopfUnitParameters := I × (I × I)

def unitHopfCoordinates (x : HopfUnitParameters) : Sphere :=
  ⟨((Real.sqrt (x.1 : ℝ) : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * (x.2.1 : ℝ) : ℝ) : ℂ)),
    (Real.sqrt (1 - (x.1 : ℝ)) : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * (x.2.2 : ℝ) : ℝ) : ℂ))), by
    simp only [a, normSq_phase]
    rw [Real.sq_sqrt x.1.property.1, Real.sq_sqrt (by linarith [x.1.property.2])]
    ring⟩

theorem unitHopfCoordinates_continuous : Continuous unitHopfCoordinates := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : HopfUnitParameters =>
    ((Real.sqrt (x.1 : ℝ) : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * (x.2.1 : ℝ) : ℝ) : ℂ)),
    (Real.sqrt (1 - (x.1 : ℝ)) : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi * (x.2.2 : ℝ) : ℝ) : ℂ))))
  fun_prop

theorem integral_unitInterval (f : ℝ → ℂ) :
    (∫ t : I, f t) = ∫ t in (0 : ℝ)..1, f t := by
  rw [unitInterval.volume_def, integral_subtype_comap measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

theorem integral_unit_phase (n : ℤ) :
    (∫ t : I, Complex.exp ((n : ℂ) * Complex.I * ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ))) =
      if n = 0 then 1 else 0 := by
  rw [integral_unitInterval (fun t => Complex.exp ((n : ℂ) * Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)))]
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn]
    have hc : (n : ℂ) * Complex.I * (2 * Real.pi : ℝ) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero)
      exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi))
    have he (t : ℝ) : (n : ℂ) * Complex.I * (2 * Real.pi * t : ℝ) =
        ((n : ℂ) * Complex.I * (2 * Real.pi : ℝ)) * t := by push_cast; ring
    simp_rw [he]
    rw [integral_exp_mul_complex hc]
    have hp : (n : ℂ) * Complex.I * (2 * Real.pi : ℝ) =
        (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
    rw [hp, Complex.exp_int_mul_two_pi_mul_I]
    simp

theorem phase_pair_power (r θ : ℝ) (a b : ℕ) :
    ((r : ℂ) * Complex.exp (Complex.I * θ)) ^ a *
      star ((r : ℂ) * Complex.exp (Complex.I * θ)) ^ b =
    (r : ℂ) ^ (a + b) * Complex.exp (((a : ℂ) - b) * Complex.I * θ) := by
  have hc : star (Complex.exp (Complex.I * θ)) = Complex.exp (-Complex.I * θ) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  have hp : Complex.exp (Complex.I * θ) ^ a * star (Complex.exp (Complex.I * θ)) ^ b =
      Complex.exp (((a : ℂ) - b) * Complex.I * θ) := by
    rw [hc, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  rw [← hp]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, mul_pow, pow_add]
  ring

theorem unitHopfCoordinates_monomial (α β γ δ : ℕ) (x : HopfUnitParameters) :
    sphereMonomial α β γ δ (unitHopfCoordinates x) =
      (Real.sqrt (x.1 : ℝ) : ℂ) ^ (α + β) *
      (Real.sqrt (1 - (x.1 : ℝ)) : ℂ) ^ (γ + δ) *
      Complex.exp (((α : ℤ) - β : ℤ) * Complex.I * ((2 * Real.pi * (x.2.1 : ℝ) : ℝ) : ℂ)) *
      Complex.exp (((γ : ℤ) - δ : ℤ) * Complex.I * ((2 * Real.pi * (x.2.2 : ℝ) : ℝ) : ℂ)) := by
  simp only [sphereMonomial, coordinateMonomial, unitHopfCoordinates]
  rw [mul_assoc (_ * _) _ _, phase_pair_power, phase_pair_power]
  push_cast
  ring

theorem integral_unit_beta (p q : ℕ) :
    (∫ t : I, ((t : ℝ) : ℂ) ^ p * (1 - ((t : ℝ) : ℂ)) ^ q) = mixedMoment p q := by
  rw [integral_unitInterval (fun t => (t : ℂ)^p * (1-(t : ℂ))^q)]
  have hb := Abelian.bernstein_integral (p + q) p (by omega)
  simp only [Nat.add_sub_cancel_left] at hb
  simp_rw [mul_assoc ((p + q).choose p : ℂ)] at hb
  rw [intervalIntegral.integral_const_mul] at hb
  have hc : ((p + q).choose p : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show p ≤ p + q by omega)).ne'
  apply mul_left_cancel₀ hc
  rw [hb, mixedMoment_factorial]
  have hfac : ((p + q).choose p : ℂ) * p.factorial * q.factorial = (p + q).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p ≤ p + q by omega)
    simp only [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  have hn : (p + q + 1 : ℂ) ≠ 0 := by exact_mod_cast (show p + q + 1 ≠ 0 by omega)
  have hf : ((p + q).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (p + q)
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  exact hfac.symm

def hopfCoordinateMeasure : Measure Sphere := (volume : Measure HopfUnitParameters).map unitHopfCoordinates

instance : IsProbabilityMeasure hopfCoordinateMeasure := by unfold hopfCoordinateMeasure; infer_instance

theorem hopfCoordinateMeasure_monomial (α β γ δ : ℕ) :
    (∫ z, sphereMonomial α β γ δ z ∂hopfCoordinateMeasure) =
      (∫ t : I, (Real.sqrt (t : ℝ) : ℂ) ^ (α + β) * (Real.sqrt (1 - (t : ℝ)) : ℂ) ^ (γ + δ)) *
        (if α = β then 1 else 0) * (if γ = δ then 1 else 0) := by
  rw [hopfCoordinateMeasure, integral_map unitHopfCoordinates_continuous.measurable.aemeasurable
    (continuous_sphereMonomial α β γ δ).measurable.aestronglyMeasurable]
  let R (t : I) : ℂ := (Real.sqrt (t : ℝ) : ℂ) ^ (α + β) * (Real.sqrt (1 - (t : ℝ)) : ℂ) ^ (γ + δ)
  let F (n : ℤ) (t : I) := Complex.exp ((n : ℂ) * Complex.I * ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ))
  have he (x : HopfUnitParameters) : sphereMonomial α β γ δ (unitHopfCoordinates x) =
      R x.1 * (F ((α : ℤ) - β) x.2.1 * F ((γ : ℤ) - δ) x.2.2) := by
    rw [unitHopfCoordinates_monomial]
    dsimp [R, F]
    ring
  simp_rw [he]
  change (∫ x : HopfUnitParameters, R x.1 * (F ((α : ℤ) - β) x.2.1 * F ((γ : ℤ) - δ) x.2.2)
    ∂(volume : Measure I).prod ((volume : Measure I).prod volume)) = _
  rw [integral_prod_mul R (fun v : I × I => F ((α : ℤ) - β) v.1 * F ((γ : ℤ) - δ) v.2),
    integral_prod_mul (F ((α : ℤ) - β)) (F ((γ : ℤ) - δ))]
  simp only [F, integral_unit_phase, sub_eq_zero, Int.natCast_inj]
  ring

theorem hopfCoordinateMeasure_monomial_eq_surface (α β γ δ : ℕ) :
    (∫ z, sphereMonomial α β γ δ z ∂hopfCoordinateMeasure) =
      ∫ z, sphereMonomial α β γ δ z ∂surfaceMeasure := by
  rw [hopfCoordinateMeasure_monomial]
  by_cases hab : α = β
  · subst β
    by_cases hgd : γ = δ
    · subst δ
      simp only [ite_true, mul_one]
      have he (t : I) : (Real.sqrt (t : ℝ) : ℂ) ^ (α + α) *
          (Real.sqrt (1 - (t : ℝ)) : ℂ) ^ (γ + γ) =
          ((t : ℝ) : ℂ) ^ α * (1 - ((t : ℝ) : ℂ)) ^ γ := by
        rw [← two_mul α, ← two_mul γ, pow_mul, pow_mul]
        have h0 := congrArg Complex.ofReal (Real.sq_sqrt t.property.1)
        have h1 := congrArg Complex.ofReal (Real.sq_sqrt (by linarith [t.property.2] : 0 ≤ 1 - (t : ℝ)))
        push_cast at h0 h1
        rw [h0, h1]
      simp_rw [he]
      exact integral_unit_beta α γ
    · rw [ite_eq_right hgd, mul_zero, sphereMonomial_integral_zero_of_unbalanced _ _ _ _ (Or.inr hgd)]
  · rw [ite_eq_right hab, mul_zero, zero_mul,
      sphereMonomial_integral_zero_of_unbalanced _ _ _ _ (Or.inl hab)]

theorem hopfCoordinateMeasure_eq_surface : hopfCoordinateMeasure = surfaceMeasure :=
  sphere_measure_eq_of_monomials _ _ hopfCoordinateMeasure_monomial_eq_surface

theorem unitHopfCoordinates_eq (x : HopfUnitParameters) :
    (unitHopfCoordinates x).val = coordinatePoint (2 * (x.1 : ℝ) - 1)
      (2 * Real.pi * (x.2.1 : ℝ)) (2 * Real.pi * (x.2.2 : ℝ)) := by
  have ha : (1 + (2 * (x.1 : ℝ) - 1)) / 2 = (x.1 : ℝ) := by ring
  have hb : (1 - (2 * (x.1 : ℝ) - 1)) / 2 = 1 - (x.1 : ℝ) := by ring
  simp only [unitHopfCoordinates, coordinatePoint, ha, hb]

theorem hopf_coordinates_integral_unitCube (f : Sphere → ℂ) (hf : Continuous f) :
    (∫ z, f z ∂surfaceMeasure) =
      ∫ t : I, ∫ α : I, ∫ β : I, f (unitHopfCoordinates (t, α, β)) := by
  rw [← hopfCoordinateMeasure_eq_surface, hopfCoordinateMeasure,
    integral_map unitHopfCoordinates_continuous.measurable.aemeasurable hf.measurable.aestronglyMeasurable]
  have hi : Integrable (fun x : HopfUnitParameters => f (unitHopfCoordinates x)) volume :=
    (hf.comp unitHopfCoordinates_continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x : HopfUnitParameters, f (unitHopfCoordinates x)
    ∂(volume : Measure I).prod (volume : Measure (I × I))) = _
  rw [integral_prod (fun x : HopfUnitParameters => f (unitHopfCoordinates x)) hi]
  apply integral_congr_ae
  filter_upwards [] with t
  have hc : Continuous (fun v : I × I => f (unitHopfCoordinates (t, v))) :=
    (hf.comp unitHopfCoordinates_continuous).comp (continuous_const.prodMk continuous_id)
  exact integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem integral_unit_scale (c : ℝ) (hc : c ≠ 0) (f : ℝ → ℂ) :
    (∫ u : I, f (c * (u : ℝ))) = (c : ℂ)⁻¹ * ∫ t in (0 : ℝ)..c, f t := by
  rw [integral_unitInterval (fun u => f (c * u)), intervalIntegral.integral_comp_mul_left f hc]
  simp [Complex.real_smul]

theorem integral_unit_height (f : ℝ → ℂ) :
    (∫ u : I, f (2 * (u : ℝ) - 1)) = (1 / 2 : ℂ) * ∫ t in (-1 : ℝ)..1, f t := by
  rw [integral_unitInterval (fun u => f (2 * u - 1))]
  have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1) f
    (show (2 : ℝ) ≠ 0 by norm_num) (-1)
  convert! h using 1
  norm_num [sub_eq_add_neg, Complex.real_smul]

theorem hopf_cube_change_of_variables (F : ℝ → ℝ → ℝ → ℂ) :
    (∫ t : I, ∫ α : I, ∫ β : I,
      F (2 * (t : ℝ) - 1) (2 * Real.pi * (α : ℝ)) (2 * Real.pi * (β : ℝ))) =
    (1 / (8 * Real.pi ^ 2 : ℂ)) *
      ∫ t in (-1 : ℝ)..1, ∫ α in (0 : ℝ)..(2 * Real.pi), ∫ β in (0 : ℝ)..(2 * Real.pi), F t α β := by
  have hc : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hb (t α : I) := integral_unit_scale (2 * Real.pi) hc
    (fun β => F (2 * (t : ℝ) - 1) (2 * Real.pi * (α : ℝ)) β)
  simp_rw [hb, integral_const_mul]
  have ha (t : I) := integral_unit_scale (2 * Real.pi) hc
    (fun α => ∫ β in (0 : ℝ)..(2 * Real.pi), F (2 * (t : ℝ) - 1) α β)
  simp_rw [ha, integral_const_mul]
  rw [integral_unit_height (fun t => ∫ α in (0 : ℝ)..(2 * Real.pi), ∫ β in (0 : ℝ)..(2 * Real.pi), F t α β)]
  push_cast
  ring

/-- The manuscript Hopf-coordinate density dτ dα dβ/(8π²), for continuous test functions. -/
theorem hopf_coordinates_integral (f : Space → ℂ) (hf : Continuous f) :
    (∫ z : Sphere, f z.val ∂surfaceMeasure) =
      (1 / (8 * Real.pi ^ 2 : ℂ)) *
        ∫ t in (-1 : ℝ)..1, ∫ α in (0 : ℝ)..(2 * Real.pi), ∫ β in (0 : ℝ)..(2 * Real.pi),
          f (coordinatePoint t α β) := by
  have h := hopf_coordinates_integral_unitCube (fun z : Sphere => f z.val) (hf.comp continuous_subtype_val)
  refine h.trans ?_
  simp_rw [unitHopfCoordinates_eq]
  exact hopf_cube_change_of_variables (fun t α β => f (coordinatePoint t α β))

end MathieuProperty.Hopf
