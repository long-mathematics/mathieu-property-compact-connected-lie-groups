import Mathlib.Analysis.Complex.Circle
import MathieuProperty.HopfCoordinateMeasure
import MathieuProperty.MixedPhase

/-! Circle averaging and the square-root elimination in Müger–Tuset Lemma 5.2.
The proof is polynomial linearity and integer-frequency cancellation. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Abelian

def unitPhase (t : I) : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ))

@[fun_prop] theorem continuous_unitPhase : Continuous unitPhase := by unfold unitPhase; fun_prop

theorem integral_unitPhase_pair (a b : ℕ) :
    (∫ t : I, unitPhase t ^ a * star (unitPhase t) ^ b) = if a = b then 1 else 0 := by
  have he (t : I) : unitPhase t ^ a * star (unitPhase t) ^ b =
      Complex.exp ((((a : ℤ) - b : ℤ) : ℂ) * Complex.I * ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ)) := by
    have h := Hopf.phase_pair_power 1 (2 * Real.pi * (t : ℝ)) a b
    simpa [unitPhase] using h
  simp_rw [he, Hopf.integral_unit_phase, sub_eq_zero, Int.natCast_inj]

theorem circle_monomial_integral (a b c d : ℂ) (α β γ δ : ℕ) :
    (∫ t : I, (a * unitPhase t)^α * b^β * c^γ * (d * star (unitPhase t))^δ) =
      a^α * b^β * c^γ * d^δ * if α = δ then 1 else 0 := by
  have he (t : I) : (a * unitPhase t)^α * b^β * c^γ * (d * star (unitPhase t))^δ =
      (a^α * b^β * c^γ * d^δ) * (unitPhase t^α * star (unitPhase t)^δ) := by ring
  simp_rw [he]
  rw [integral_const_mul, integral_unitPhase_pair]

theorem circle_monomial_rescale (a b c d r : ℂ) (α β γ δ : ℕ) :
    (∫ t : I, (a * r * unitPhase t)^α * b^β * c^γ * (d * r * star (unitPhase t))^δ) =
      ∫ t : I, (a * r^2 * unitPhase t)^α * b^β * c^γ * (d * star (unitPhase t))^δ := by
  rw [circle_monomial_integral, circle_monomial_integral]
  by_cases h : α = δ
  · subst δ
    simp only [ite_true, mul_one]
    ring
  · simp [h]

theorem eval_entry_monomial (u : Fin 4 →₀ ℕ) (k a b c d : ℂ) :
    MvPolynomial.eval ![a,b,c,d] (MvPolynomial.monomial u k) =
      k * (a ^ u 0 * b ^ u 1 * c ^ u 2 * d ^ u 3) := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  · simp [Fin.prod_univ_succ, mul_assoc]
  · intro i
    simp

theorem continuous_entry_eval (p : MvPolynomial (Fin 4) ℂ) (a b c d : ℂ) :
    Continuous (fun t : I => MvPolynomial.eval ![a * unitPhase t,b,c,d * star (unitPhase t)] p) := by
  apply p.continuous_eval.comp
  exact continuous_pi (by intro i; fin_cases i <;> simp <;> fun_prop)

theorem circle_polynomial_rescale (p : MvPolynomial (Fin 4) ℂ) (a b c d r : ℂ) :
    (∫ t : I, MvPolynomial.eval ![a * r * unitPhase t,b,c,d * r * star (unitPhase t)] p) =
      ∫ t : I, MvPolynomial.eval ![a * r^2 * unitPhase t,b,c,d * star (unitPhase t)] p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u k =>
    simp_rw [eval_entry_monomial]
    rw [integral_const_mul, integral_const_mul, circle_monomial_rescale]
  | add p q hp hq =>
    simp only [map_add]
    rw [integral_add, integral_add, hp, hq]
    all_goals exact (continuous_entry_eval _ _ _ _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The square-root elimination in Müger–Tuset Lemma 5.2, at each radius. -/
theorem square_root_free_circle_integral (p : MvPolynomial (Fin 4) ℂ)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ t : I, MvPolynomial.eval
      ![Complex.I * (Real.sqrt (1 - x^2) : ℂ) * unitPhase t,
        Complex.I * x, Complex.I * x,
        -Complex.I * (Real.sqrt (1 - x^2) : ℂ) * star (unitPhase t)] p) =
    ∫ t : I, MvPolynomial.eval
      ![Complex.I * (1 - (x : ℂ)^2) * unitPhase t,
        Complex.I * x, Complex.I * x, -Complex.I * star (unitPhase t)] p := by
  have hr : (Real.sqrt (1 - x^2) : ℂ)^2 = 1 - (x : ℂ)^2 := by
    have h := congrArg Complex.ofReal (Real.sq_sqrt (by nlinarith [hx.1, hx.2] : 0 ≤ 1 - x^2))
    simpa using h
  have h := circle_polynomial_rescale p Complex.I (Complex.I*x)
    (Complex.I*x) (-Complex.I) (Real.sqrt (1-x^2))
  convert h using 1
  simp only [hr]

/-- The equality survives any radial weight, using actual interval integrals. -/
theorem square_root_free_weighted_integral (p : MvPolynomial (Fin 4) ℂ) (δ : ℝ → ℂ) :
    (∫ x in (0 : ℝ)..1, (∫ t : I, MvPolynomial.eval
      ![Complex.I * (Real.sqrt (1 - x^2) : ℂ) * unitPhase t,
        Complex.I * x, Complex.I * x,
        -Complex.I * (Real.sqrt (1 - x^2) : ℂ) * star (unitPhase t)] p) * δ x) =
    ∫ x in (0 : ℝ)..1, (∫ t : I, MvPolynomial.eval
      ![Complex.I * (1 - (x : ℂ)^2) * unitPhase t,
        Complex.I * x, Complex.I * x, -Complex.I * star (unitPhase t)] p) * δ x := by
  apply intervalIntegral.integral_congr
  intro x hx
  exact congrArg (fun z : ℂ => z * δ x) (square_root_free_circle_integral p x (by simpa using hx))

def unitPhaseUnit (t : I) : ℂˣ := Units.mk0 (unitPhase t) (Complex.exp_ne_zero _)

theorem unitPhaseUnit_zpow (t : I) (n : ℤ) :
    ((unitPhaseUnit t ^ n : ℂˣ) : ℂ) =
      Complex.exp ((n : ℂ) * Complex.I * ((2*Real.pi*(t : ℝ) : ℝ) : ℂ)) := by
  simp [unitPhaseUnit, unitPhase, ← Complex.exp_int_mul, mul_assoc]

theorem continuous_laurent_unit (p : LaurentPolynomial ℂ) :
    Continuous (fun t : I => LaurentPolynomial.eval₂ (RingHom.id ℂ) (unitPhaseUnit t) p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | C_mul_T n a =>
    simp only [LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, unitPhaseUnit_zpow]
    fun_prop

theorem integral_laurent_unit (p : LaurentPolynomial ℂ) :
    (∫ t : I, LaurentPolynomial.eval₂ (RingHom.id ℂ) (unitPhaseUnit t) p) = p.coeff 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [integral_add, hp, hq]
    all_goals exact (continuous_laurent_unit _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  | C_mul_T n a =>
    simp only [LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, unitPhaseUnit_zpow]
    rw [integral_const_mul, Hopf.integral_unit_phase]
    simp [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      mul_ite]

theorem unitPhase_star (t : I) : star (unitPhase t) = (unitPhase t)⁻¹ := by
  simpa [unitPhase, Circle.coe_exp, mul_comm] using (Circle.coe_inv_eq_conj (Circle.exp (2*Real.pi*(t : ℝ)))).symm

theorem unitPhase_mul_star (t : I) : unitPhase t * star (unitPhase t) = 1 := by
  rw [unitPhase_star]
  exact mul_inv_cancel₀ (Complex.exp_ne_zero _)

end MathieuProperty.Abelian

