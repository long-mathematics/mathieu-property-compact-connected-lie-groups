import MathieuProperty.SU2Witness

noncomputable section
namespace MathieuProperty

/-- The numerical expression in the classical closed forms. Its identification
with Haar moments on higher-dimensional groups remains a separate obligation. -/
def classicalMomentFormula (n m s : ℕ) : ℝ :=
  momentConstant m * ((m - 1).choose (s - 1) : ℝ) *
    ((2 : ℕ).ascFactorial (4 * m + s) : ℝ) / (n.ascFactorial (4 * m + s) : ℝ)

theorem classical_small_values :
    classicalMomentFormula 2 1 1 = 2 / 3 ∧
    classicalMomentFormula 2 2 1 = 8 / 15 ∧
    classicalMomentFormula 2 3 1 = 16 / 35 ∧
    classicalMomentFormula 3 1 1 = 4 / 21 ∧
    classicalMomentFormula 3 2 1 = 16 / 165 ∧
    classicalMomentFormula 3 3 1 = 32 / 525 ∧
    classicalMomentFormula 4 1 1 = 1 / 14 ∧
    classicalMomentFormula 4 2 1 = 4 / 165 ∧
    classicalMomentFormula 4 3 1 = 2 / 175 := by
  norm_num [classicalMomentFormula, momentConstant_factorial, Nat.ascFactorial]

open Hopf in
theorem su2_small_values :
    representativeIntegral SU2 (su2Q * su2P ^ 1) = (2 / 3 : ℂ) ∧
    representativeIntegral SU2 (su2Q * su2P ^ 2) = (8 / 15 : ℂ) ∧
    representativeIntegral SU2 (su2Q * su2P ^ 3) = (16 / 35 : ℂ) := by
  have h₁ := su2_representative_marked 1 1 (by omega) (by omega)
  have h₂ := su2_representative_marked 2 1 (by omega) (by omega)
  have h₃ := su2_representative_marked 3 1 (by omega) (by omega)
  norm_num [momentConstant_factorial] at h₁ h₂ h₃ ⊢
  exact ⟨h₁, h₂, h₃⟩

end MathieuProperty
