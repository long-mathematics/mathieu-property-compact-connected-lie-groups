import MathieuProperty.GaussianSquare
import Mathlib.Probability.ProductMeasure

/-! Independent squared moduli of complex Gaussian coordinates.

The real/imaginary pairs are grouped using the product-measure curry theorem.
Their squared sums have independent Gamma(1,1/2) laws. The final theorem
identifies these with the actual standard Gaussian measure on complex
Euclidean n-space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace MathieuProperty

theorem gaussian_fin_two_squares_gamma :
    (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map (fun x => x 0 ^ 2 + x 1 ^ 2) =
      gammaMeasure 1 (1 / 2) := by
  have hh := gaussian_pair_squares_gamma
  rw [← (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)).map_eq,
    Measure.map_map (by fun_prop) (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurable] at hh
  exact hh

def complexGaussianRadii (n : ℕ) (x : ((_i : Fin n) × Fin 2) → ℝ) : Fin n → ℝ :=
  fun i => x ⟨i, 0⟩ ^ 2 + x ⟨i, 1⟩ ^ 2

theorem complexGaussianRadii_map (n : ℕ) :
    (Measure.pi (fun _ : (_i : Fin n) × Fin 2 => gaussianReal 0 1)).map (complexGaussianRadii n) =
      Measure.pi (fun _ : Fin n => gammaMeasure 1 (1 / 2)) := by
  have hc := Measure.infinitePi_map_piCurry (fun (_ : Fin n) (_ : Fin 2) => gaussianReal 0 1)
  simp_rw [Measure.infinitePi_eq_pi] at hc
  have hms : Measurable (fun x : Fin 2 → ℝ => x 0 ^ 2 + x 1 ^ 2) := by fun_prop
  have hp := Measure.pi_map_pi (μ := fun _ : Fin n => Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))
    (f := fun _ : Fin n => fun x : Fin 2 → ℝ => x 0 ^ 2 + x 1 ^ 2)
    (fun _ => hms.aemeasurable)
  simp_rw [gaussian_fin_two_squares_gamma] at hp
  rw [← hc, Measure.map_map (by fun_prop) (MeasurableEquiv.piCurry (fun (_ : Fin n) (_ : Fin 2) => ℝ)).measurable] at hp
  exact hp

theorem complexGaussianCoordinates_normSq (n : ℕ)
    (x : ((_i : Fin n) × Fin 2) → ℝ) (i : Fin n) :
    Complex.normSq (complexGaussianCoordinates n x i) = complexGaussianRadii n x i := by
  simp [complexGaussianCoordinates, complexGaussianRadii, Complex.normSq_apply]
  ring

theorem complexGaussian_normSq_map (n : ℕ) :
    (stdGaussian (EuclideanSpace ℂ (Fin n))).map (fun z i => Complex.normSq (z i)) =
      Measure.pi (fun _ : Fin n => gammaMeasure 1 (1 / 2)) := by
  have hm : Measurable (complexGaussianCoordinates n) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).measurable.comp
    fun_prop
  have hr : Measurable (fun z : EuclideanSpace ℂ (Fin n) => fun i => Complex.normSq (z i)) := by
    apply Measurable.of_eval
    intro i
    exact Complex.continuous_normSq.measurable.comp
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).measurable
  rw [← complexGaussianCoordinates_map, Measure.map_map hr hm]
  have heq : (fun z : EuclideanSpace ℂ (Fin n) => fun i => Complex.normSq (z i)) ∘
      complexGaussianCoordinates n = complexGaussianRadii n := by
    funext x i
    exact complexGaussianCoordinates_normSq n x i
  rw [heq, complexGaussianRadii_map]

end MathieuProperty
