import MathieuProperty.Haar
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! Continuous Haar integration and character orthogonality on compact
abelian groups. The inverse character is formed using group inversion,
so the argument does not presume a classification of characters. -/

noncomputable section
open MeasureTheory
open scoped Classical
namespace MathieuProperty
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

def haarIntegralContinuous : C(G,ℂ) →L[ℂ] ℂ :=
  (haarIntegralLinear G).mkContinuous 1 (fun f => by
    have h := norm_integral_le_of_norm_le_const (μ := normalizedHaar G)
      (Filter.Eventually.of_forall f.norm_coe_le_norm)
    change ‖∫ x, f x ∂normalizedHaar G‖ ≤ 1 * ‖f‖
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one, one_mul] using h)

theorem haar_character_zero (χ : G →ₜ* ℂ) (hχ : χ ≠ 1) : haarIntegral G χ.toContinuousMap = 0 := by
  obtain ⟨g,hg⟩ : ∃ g : G, χ g ≠ 1 := by
    by_contra! h
    exact hχ (ContinuousMonoidHom.ext h)
  have h := integral_mul_left_eq_self (μ := normalizedHaar G) (fun x => χ x) g
  simp only [map_mul, integral_const_mul] at h
  change χ g * haarIntegral G χ.toContinuousMap = haarIntegral G χ.toContinuousMap at h
  have hz : (χ g - 1) * haarIntegral G χ.toContinuousMap = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hg)

theorem haar_character (χ : G →ₜ* ℂ) :
    haarIntegral G χ.toContinuousMap = if χ = 1 then 1 else 0 := by
  by_cases h : χ = 1
  · subst χ
    simp [haarIntegral]
  · rw [ite_eq_right h]
    exact haar_character_zero χ h

def inverseCharacter (χ : G →ₜ* ℂ) : G →ₜ* ℂ where
  toFun g := χ g⁻¹
  map_one' := by simp
  map_mul' g h := by simp [mul_comm]
  continuous_toFun := χ.continuous.comp continuous_inv

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem character_mul_inverse (χ : G →ₜ* ℂ) (g : G) : χ g * inverseCharacter χ g = 1 := by
  change χ g * χ g⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem character_ratio_one_iff (φ χ : G →ₜ* ℂ) : φ * inverseCharacter χ = 1 ↔ φ = χ := by
  constructor
  · intro h
    ext g
    have he := congrArg (fun f : G →ₜ* ℂ => f g) h
    have hχ := character_mul_inverse χ g
    change φ g * inverseCharacter χ g = 1 at he
    calc φ g = φ g * (inverseCharacter χ g * χ g) := by rw [mul_comm (inverseCharacter χ g), hχ, mul_one]
         _ = χ g := by rw [← mul_assoc, he, one_mul]
  · rintro rfl
    ext g
    exact character_mul_inverse φ g

theorem haar_character_orthogonality (φ χ : G →ₜ* ℂ) :
    haarIntegral G (φ.toContinuousMap * (inverseCharacter χ).toContinuousMap) =
      if φ = χ then 1 else 0 := by
  have hf : (φ * inverseCharacter χ).toContinuousMap = φ.toContinuousMap * (inverseCharacter χ).toContinuousMap := by ext g; rfl
  rw [← hf]
  simpa only [character_ratio_one_iff] using haar_character (φ * inverseCharacter χ)

end MathieuProperty
