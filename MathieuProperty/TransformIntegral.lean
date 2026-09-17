import MathieuProperty.EntryTransform
import MathieuProperty.SU2Witness

/-! The normalized SU(2) Haar integral equals the square-root-free polynomial
transform integral, including both circle variables and the radial weight 2x.
The proof compares all entry monomials and extends by polynomial linearity. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Abelian

def torusEntryValue (p : MvPolynomial (Fin 4) ℂ) (x : ℝ) (w z : I) : ℂ :=
  MvPolynomial.eval
    ![Complex.I * (1-(x : ℂ)^2) * unitPhase w * unitPhase z,
      Complex.I*x * star (unitPhase z), Complex.I*x * unitPhase z,
      -Complex.I * star (unitPhase w) * star (unitPhase z)] p

theorem integral_torus_monomial (α β γ δ : ℕ) (x : ℝ) :
    (∫ z : I, ∫ w : I,
      (Complex.I * (1-(x : ℂ)^2) * unitPhase w * unitPhase z)^α *
      (Complex.I*x * star (unitPhase z))^β * (Complex.I*x * unitPhase z)^γ *
      (-Complex.I * star (unitPhase w) * star (unitPhase z))^δ) =
      (Complex.I * (1-(x : ℂ)^2))^α * (Complex.I*x)^β * (Complex.I*x)^γ * (-Complex.I)^δ *
        (if α = δ then 1 else 0) * (if α+γ = β+δ then 1 else 0) := by
  have h (z w : I) :
      (Complex.I * (1-(x : ℂ)^2) * unitPhase w * unitPhase z)^α *
      (Complex.I*x * star (unitPhase z))^β * (Complex.I*x * unitPhase z)^γ *
      (-Complex.I * star (unitPhase w) * star (unitPhase z))^δ =
      ((Complex.I * (1-(x : ℂ)^2) * unitPhase z) * unitPhase w)^α *
      (Complex.I*x * star (unitPhase z))^β * (Complex.I*x * unitPhase z)^γ *
      ((-Complex.I * star (unitPhase z)) * star (unitPhase w))^δ := by ring
  simp_rw [h, circle_monomial_integral]
  have he (z : I) :
      (Complex.I * (1-(x : ℂ)^2) * unitPhase z)^α *
      (Complex.I*x * star (unitPhase z))^β * (Complex.I*x * unitPhase z)^γ *
      (-Complex.I * star (unitPhase z))^δ * (if α = δ then 1 else 0) =
      ((Complex.I * (1-(x : ℂ)^2))^α * (Complex.I*x)^β * (Complex.I*x)^γ * (-Complex.I)^δ *
        (if α = δ then 1 else 0)) * (unitPhase z^(α+γ) * star (unitPhase z)^(β+δ)) := by
    simp only [pow_add, mul_pow]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_unitPhase_pair]

theorem imaginary_pair_power (a : ℂ) (m : ℕ) :
    (Complex.I*a)^m * (-Complex.I)^m = a^m := by
  rw [← mul_pow]
  congr 1
  calc (Complex.I*a)*(-Complex.I) = -(Complex.I^2)*a := by ring
       _ = a := by rw [Complex.I_sq]; ring

theorem imaginary_square_power (a : ℂ) (m : ℕ) :
    (Complex.I*a)^m * (Complex.I*a)^m = (-1 : ℂ)^m*a^(2*m) := by
  rw [← mul_pow]
  have h : Complex.I*a*(Complex.I*a) = (-1 : ℂ)*a^2 := by
    calc Complex.I*a*(Complex.I*a) = Complex.I^2*a^2 := by ring
         _ = (-1 : ℂ)*a^2 := by rw [Complex.I_sq]
  rw [h, mul_pow, pow_mul]

theorem integral_torus_monomial_balanced (α β γ δ : ℕ) (x : ℝ) :
    (∫ z : I, ∫ w : I,
      (Complex.I * (1-(x : ℂ)^2) * unitPhase w * unitPhase z)^α *
      (Complex.I*x * star (unitPhase z))^β * (Complex.I*x * unitPhase z)^γ *
      (-Complex.I * star (unitPhase w) * star (unitPhase z))^δ) =
      if α = δ ∧ β = γ then (-1 : ℂ)^β * (1-(x : ℂ)^2)^α * (x : ℂ)^(2*β) else 0 := by
  rw [integral_torus_monomial]
  by_cases ha : α = δ
  · subst δ
    by_cases hb : β = γ
    · subst γ
      simp only [Nat.add_comm α β, ite_true, true_and, mul_one]
      calc _ = ((Complex.I * (1-(x : ℂ)^2))^α * (-Complex.I)^α) *
          ((Complex.I*x)^β * (Complex.I*x)^β) := by ring
           _ = _ := by rw [imaginary_pair_power, imaginary_square_power]; ring
    · have hz : α+γ ≠ β+α := by omega
      simp [hb,hz]
  · simp [ha]

theorem weighted_radial_monomial (α β : ℕ) :
    2 * (∫ x in (0 : ℝ)..1, (1-(x : ℂ)^2)^α * (x : ℂ)^(2*β) * (x : ℂ)) =
      Hopf.mixedMoment α β := by
  have h := weighted_square_substitution (fun t => (1-(t : ℂ))^α * (t : ℂ)^β) (by fun_prop)
  simp only [Complex.ofReal_pow, pow_mul] at h ⊢
  rw [h, ← Hopf.integral_unitInterval]
  have he (t : I) : (1-((t : ℝ) : ℂ))^α * ((t : ℝ) : ℂ)^β =
      ((t : ℝ) : ℂ)^β * (1-((t : ℝ) : ℂ))^α := mul_comm _ _
  simp_rw [he]
  rw [Hopf.integral_unit_beta, Hopf.mixedMoment_factorial, Hopf.mixedMoment_factorial]
  simp [mul_comm, Nat.add_comm]

def torusAverage (p : MvPolynomial (Fin 4) ℂ) (x : ℝ) : ℂ :=
  ∫ z : I, ∫ w : I, torusEntryValue p x w z

theorem continuous_integral_unit {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] {f : X → I → ℂ}
    (hf : Continuous f.uncurry) : Continuous (fun x => ∫ t : I, f x t) := by
  simpa using continuous_parametric_integral_of_continuous hf (s := Set.univ) isCompact_univ

theorem continuous_torusAverage (p : MvPolynomial (Fin 4) ℂ) : Continuous (torusAverage p) := by
  apply continuous_integral_unit
  apply continuous_integral_unit
  apply p.continuous_eval.comp
  exact continuous_pi (by intro i; fin_cases i <;> simp <;> fun_prop)

theorem continuous_torusEntryValue (p : MvPolynomial (Fin 4) ℂ) (x : ℝ) (z : I) :
    Continuous (fun w : I => torusEntryValue p x w z) := by
  apply p.continuous_eval.comp
  exact continuous_pi (by intro i; fin_cases i <;> simp <;> fun_prop)

theorem continuous_torusEntryIntegral (p : MvPolynomial (Fin 4) ℂ) (x : ℝ) :
    Continuous (fun z : I => ∫ w : I, torusEntryValue p x w z) := by
  apply continuous_integral_unit
  apply p.continuous_eval.comp
  exact continuous_pi (by intro i; fin_cases i <;> simp <;> fun_prop)

theorem torusAverage_add (p q : MvPolynomial (Fin 4) ℂ) (x : ℝ) :
    torusAverage (p+q) x = torusAverage p x + torusAverage q x := by
  unfold torusAverage
  have h (z : I) : (∫ w : I, torusEntryValue (p+q) x w z) =
      (∫ w : I, torusEntryValue p x w z) + ∫ w : I, torusEntryValue q x w z := by
    simp only [torusEntryValue, map_add]
    apply integral_add
    all_goals exact (continuous_torusEntryValue _ _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [h]
  apply integral_add
  all_goals exact (continuous_torusEntryIntegral _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def transformedIntegral (p : MvPolynomial (Fin 4) ℂ) : ℂ :=
  2 * ∫ x in (0 : ℝ)..1, torusAverage p x * (x : ℂ)

theorem transformedIntegral_add (p q : MvPolynomial (Fin 4) ℂ) :
    transformedIntegral (p+q) = transformedIntegral p + transformedIntegral q := by
  unfold transformedIntegral
  simp_rw [torusAverage_add, add_mul]
  rw [intervalIntegral.integral_add, mul_add]
  all_goals exact ((continuous_torusAverage _).mul Complex.continuous_ofReal).intervalIntegrable _ _

theorem transformedIntegral_monomial (u : Fin 4 →₀ ℕ) (k : ℂ) :
    transformedIntegral (MvPolynomial.monomial u k) =
      k * if u 0 = u 3 ∧ u 1 = u 2 then (-1 : ℂ)^(u 1) * Hopf.mixedMoment (u 0) (u 1) else 0 := by
  unfold transformedIntegral torusAverage torusEntryValue
  simp_rw [eval_entry_monomial, integral_const_mul, integral_torus_monomial_balanced]
  by_cases h : u 0 = u 3 ∧ u 1 = u 2
  · simp_rw [ite_eq_left h]
    have he (x : ℝ) : (k * ((-1 : ℂ)^(u 1) * (1-(x : ℂ)^2)^(u 0) * (x : ℂ)^(2*u 1))) * (x : ℂ) =
        (k * (-1 : ℂ)^(u 1)) * ((1-(x : ℂ)^2)^(u 0) * (x : ℂ)^(2*u 1) * (x : ℂ)) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul]
    calc _ = (k * (-1 : ℂ)^(u 1)) * (2 * ∫ x in (0 : ℝ)..1,
          (1-(x : ℂ)^2)^(u 0) * (x : ℂ)^(2*u 1) * (x : ℂ)) := by ring
         _ = _ := by rw [weighted_radial_monomial]; ring
  · simp [h]

def sphereEntryValue (p : MvPolynomial (Fin 4) ℂ) (z : Hopf.Sphere) : ℂ :=
  MvPolynomial.eval ![z.val.1, -star z.val.2, z.val.2, star z.val.1] p

theorem continuous_sphereEntryValue (p : MvPolynomial (Fin 4) ℂ) : Continuous (sphereEntryValue p) := by
  apply p.continuous_eval.comp
  exact continuous_pi (by intro i; fin_cases i <;> simp <;> fun_prop)

theorem entryPolynomialValue_eq_sphere (p : MvPolynomial (Fin 4) ℂ) (g : Hopf.SU2) :
    entryPolynomialValue p g = sphereEntryValue p (Hopf.su2ToSphere g) := by
  simp only [entryPolynomialValue, sphereEntryValue, Hopf.su2ToSphere, (Hopf.su2_entries g).1,
    (Hopf.su2_entries g).2]

theorem haar_entryIntegral_eq_sphere (p : MvPolynomial (Fin 4) ℂ) :
    (∫ g : Hopf.SU2, entryPolynomialValue p g ∂normalizedHaar Hopf.SU2) =
      ∫ z : Hopf.Sphere, sphereEntryValue p z ∂Hopf.surfaceMeasure := by
  simp_rw [entryPolynomialValue_eq_sphere]
  exact Hopf.su2_firstColumn_integral (continuous_sphereEntryValue p)

theorem sphereEntryValue_monomial (u : Fin 4 →₀ ℕ) (k : ℂ) (z : Hopf.Sphere) :
    sphereEntryValue (MvPolynomial.monomial u k) z =
      (k * (-1 : ℂ)^(u 1)) * Hopf.sphereMonomial (u 0) (u 3) (u 2) (u 1) z := by
  rw [sphereEntryValue, eval_entry_monomial]
  have h (a c : ℂ) : k * (a^(u 0) * (-star c)^(u 1) * c^(u 2) * star a^(u 3)) =
      (k * (-1 : ℂ)^(u 1)) * (a^(u 0) * star a^(u 3) * c^(u 2) * star c^(u 1)) := by
    rw [neg_pow]
    ring
  exact h z.val.1 z.val.2

theorem sphere_entryIntegral_monomial (u : Fin 4 →₀ ℕ) (k : ℂ) :
    (∫ z : Hopf.Sphere, sphereEntryValue (MvPolynomial.monomial u k) z ∂Hopf.surfaceMeasure) =
      k * if u 0 = u 3 ∧ u 1 = u 2 then (-1 : ℂ)^(u 1) * Hopf.mixedMoment (u 0) (u 1) else 0 := by
  simp_rw [sphereEntryValue_monomial]
  rw [integral_const_mul]
  by_cases h : u 0 = u 3 ∧ u 1 = u 2
  · rw [ite_eq_left h]
    rw [← h.1, ← h.2]
    change k * (-1 : ℂ)^(u 1) * Hopf.mixedMoment (u 0) (u 1) = _
    ring
  · have hn : u 0 ≠ u 3 ∨ u 2 ≠ u 1 := by omega
    rw [Hopf.sphereMonomial_integral_zero_of_unbalanced _ _ _ _ hn, ite_eq_right h, mul_zero, mul_zero]

theorem haar_entryIntegral_eq_transformedIntegral (p : MvPolynomial (Fin 4) ℂ) :
    (∫ g : Hopf.SU2, entryPolynomialValue p g ∂normalizedHaar Hopf.SU2) = transformedIntegral p := by
  rw [haar_entryIntegral_eq_sphere]
  induction p using MvPolynomial.induction_on' with
  | monomial u k => rw [sphere_entryIntegral_monomial, transformedIntegral_monomial]
  | add p q hp hq =>
    simp only [sphereEntryValue, map_add]
    rw [integral_add, transformedIntegral_add]
    · exact congrArg₂ (fun a b : ℂ => a+b) hp hq
    all_goals exact (continuous_sphereEntryValue _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end MathieuProperty.Abelian
