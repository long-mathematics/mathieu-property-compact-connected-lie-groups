import MathieuProperty.OneVariableDvK.OneVariableDvK
import MathieuProperty.TorusLaurent

/-! One-variable DvK and the Mathieu property of the circle.
The valuation/partial-fraction proof is adapted with attribution in
`OneVariableDvK/`. This module supplies the unconditional manuscript-facing
specializations and connects them to actual representative Haar integration.
The multivariate DvK theorem remains a separate obligation. -/

namespace MathieuProperty

open LaurentPolynomial

noncomputable section

/-- One-variable DvK: a two-sided support forces a nonzero positive moment. -/
theorem one_variable_nonzero_constant_power (f : LaurentPolynomial ℂ)
    (hn : ∃ i ∈ f.coeff.support, i < 0)
    (hp : ∃ i ∈ f.coeff.support, 0 < i) :
    ∃ m : ℕ, 1 ≤ m ∧ (f ^ m).coeff 0 ≠ 0 :=
  DvK.hasNonzeroConstantPower_of_dvkCoefficientExtraction
    DvK.dvkCoefficientExtraction f hn hp

/-- Vanishing positive moments force all exponents onto one strict side of zero. -/
theorem one_variable_support_one_sided (f : LaurentPolynomial ℂ)
    (hf : ∀ m : ℕ, 1 ≤ m → (f ^ m).coeff 0 = 0) :
    (∀ i ∈ f.coeff.support, 0 < i) ∨ (∀ i ∈ f.coeff.support, i < 0) := by
  classical
  have hzero : f.coeff 0 = 0 := by simpa using hf 1 le_rfl
  have hne : ∀ i ∈ f.coeff.support, i ≠ 0 := by
    intro i hi hiz
    subst i
    exact Finsupp.mem_support_iff.mp hi hzero
  by_cases hn : ∃ i ∈ f.coeff.support, i < 0
  · right
    intro i hi
    by_contra hneg
    have hp : 0 < i := lt_of_le_of_ne (le_of_not_gt hneg) (hne i hi).symm
    obtain ⟨m, hm, hmoment⟩ := one_variable_nonzero_constant_power f hn ⟨i, hi, hp⟩
    exact hmoment (hf m hm)
  · left
    intro i hi
    have hnonneg : 0 ≤ i := le_of_not_gt (fun h => hn ⟨i,hi,h⟩)
    exact lt_of_le_of_ne hnonneg (hne i hi).symm

/-- The literal one-dimensional Newton convex-hull conclusion of DvK. -/
theorem duistermaat_van_der_kallen_one_variable (f : LaurentPolynomial ℂ)
    (hf : ∀ m : ℕ, 1 ≤ m → (f ^ m).coeff 0 = 0) :
    (0 : ℝ) ∉ convexHull ℝ ((fun i : ℤ => (i : ℝ)) ''
      (f.coeff.support : Set ℤ)) := by
  rcases one_variable_support_one_sided f hf with hp | hn
  · have hs : convexHull ℝ ((fun i : ℤ => (i : ℝ)) ''
        (f.coeff.support : Set ℤ)) ⊆ Set.Ioi (0 : ℝ) :=
      (convex_Ioi (𝕜 := ℝ) 0).convexHull_subset_iff.mpr (by
        rintro x ⟨i,hi,rfl⟩
        change (0 : ℝ) < (i : ℝ)
        exact_mod_cast hp i hi)
    exact fun h => (lt_irrefl (0 : ℝ)) (hs h)
  · have hs : convexHull ℝ ((fun i : ℤ => (i : ℝ)) ''
        (f.coeff.support : Set ℤ)) ⊆ Set.Iio (0 : ℝ) :=
      (convex_Iio (𝕜 := ℝ) 0).convexHull_subset_iff.mpr (by
        rintro x ⟨i,hi,rfl⟩
        change (i : ℝ) < (0 : ℝ)
        exact_mod_cast hn i hi)
    exact fun h => (lt_irrefl (0 : ℝ)) (hs h)

def oneVariableConstantTerm : LaurentPolynomial ℂ →ₗ[ℂ] ℂ where
  toFun f := f.coeff 0
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The constant-term kernel in ℂ[z,z⁻¹] is a Mathieu subspace. -/
theorem one_variable_constantTerm_mathieu :
    IsMathieuSubspace (LinearMap.ker oneVariableConstantTerm) := by
  intro f hf h
  have hf' : ∀ m : ℕ, 1 ≤ m → (f ^ m).coeff 0 = 0 := hf
  rcases one_variable_support_one_sided f hf' with hp | hn
  · exact eventual_constantTerm_zero_of_lower_bound (Int.castAddHom ℝ) f h 1
      zero_lt_one (by
        intro i hi
        change (1 : ℝ) ≤ (i : ℝ)
        have : (1 : ℤ) ≤ i := hp i hi
        exact_mod_cast this)
  · exact eventual_constantTerm_zero_of_lower_bound (-Int.castAddHom ℝ) f h 1
      zero_lt_one (by
        intro i hi
        change (1 : ℝ) ≤ -(i : ℝ)
        have : (1 : ℤ) ≤ -i := by have := hn i hi; omega
        exact_mod_cast this)

/-- Reindex the sole Laurent exponent by the unique coordinate. -/
def oneVariableLaurentEquiv : MultiLaurent 1 ≃ₐ[ℂ] LaurentPolynomial ℂ :=
  AddMonoidAlgebra.domCongr ℂ ℂ (AddEquiv.piUnique (fun _ : Fin 1 => ℤ))

theorem oneVariableLaurentEquiv_constantTerm (f : MultiLaurent 1) :
    (oneVariableLaurentEquiv f).coeff 0 = constantTerm f := by
  rw [oneVariableLaurentEquiv, AddMonoidAlgebra.coeff_domCongr]
  rfl

/-- The one-dimensional torus has the Mathieu property for actual Haar integration. -/
theorem torus_one_mathieu : HasMathieuProperty (Torus 1) := by
  apply (torus_mathieu_iff_constantTerm 1).mpr
  have h := one_variable_constantTerm_mathieu.comap oneVariableLaurentEquiv.toAlgHom
  have he : (LinearMap.ker oneVariableConstantTerm).comap
      oneVariableLaurentEquiv.toLinearMap = LinearMap.ker (constantTermLinear 1) := by
    ext f
    change (oneVariableLaurentEquiv f).coeff 0 = 0 ↔ constantTerm f = 0
    rw [oneVariableLaurentEquiv_constantTerm]
  exact he ▸ h

instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- The actual unit-circle group has the Mathieu property. -/
theorem circle_mathieu : HasMathieuProperty Circle := by
  let π : Torus 1 →* Circle :=
    { toFun := fun g => g 0
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact torus_one_mathieu.of_surjective π (continuous_apply 0)
    (fun z => ⟨fun _ => z, rfl⟩)

end

end MathieuProperty
