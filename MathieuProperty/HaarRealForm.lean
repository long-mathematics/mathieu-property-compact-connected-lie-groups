import MathieuProperty.Haar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.MeasureTheory.Group.Integral
/-! Haar averaging for arbitrary finite-dimensional real representations.
A Euclidean coordinate model supplies a positive form without imposing an
inner-product norm on the original space. Positivity follows from continuity
and positivity of Haar measure on open sets; invariance uses right Haar
invariance. This module asserts group-action invariance, not Lie invariance.
-/

noncomputable section
open MeasureTheory
namespace MathieuProperty
namespace HaarRealForm
variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ρ : Representation ℝ G V) (hρ : ∀ v, Continuous (fun g => ρ g v))

def euclideanEquiv : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
  (LinearEquiv.ofFinrankEq (R := ℝ) V (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))
    (by simp)).toContinuousLinearEquiv

def average (v w : V) : ℝ := ∫ g,
  inner ℝ (euclideanEquiv (ρ g v)) (euclideanEquiv (ρ g w)) ∂normalizedHaar G

include hρ in
theorem integrable (v w : V) : Integrable (fun g =>
    inner ℝ (euclideanEquiv (ρ g v)) (euclideanEquiv (ρ g w))) (normalizedHaar G) :=
  (((euclideanEquiv (V := V)).continuous.comp (hρ v)).inner
    ((euclideanEquiv (V := V)).continuous.comp (hρ w))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

include hρ in
def form : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ (average ρ)
  (fun v w z => by
    simp only [average, map_add, inner_add_left]
    exact integral_add (integrable ρ hρ v z) (integrable ρ hρ w z))
  (fun c v w => by
    simp only [average, map_smul, real_inner_smul_left, smul_eq_mul]
    exact integral_const_mul _ _)
  (fun v w z => by
    simp only [average, map_add, inner_add_right]
    exact integral_add (integrable ρ hρ v w) (integrable ρ hρ v z))
  (fun c v w => by
    simp only [average, map_smul, real_inner_smul_right, smul_eq_mul]
    exact integral_const_mul _ _)

theorem form_apply (v w : V) : form ρ hρ v w = average ρ v w := rfl

theorem symmetric : (form ρ hρ).IsSymm := by
  constructor
  intro v w
  simp only [form_apply, average, real_inner_comm]

theorem positive {v : V} (hv : v ≠ 0) : 0 < form ρ hρ v v := by
  rw [form_apply, average]
  apply integral_pos_of_integrable_nonneg_nonzero
    (((euclideanEquiv (V := V)).continuous.comp (hρ v)).inner
      ((euclideanEquiv (V := V)).continuous.comp (hρ v)))
    (integrable ρ hρ v v) (fun _ => real_inner_self_nonneg) (x := (1 : G))
  have hv' : euclideanEquiv v ≠ 0 := by
    intro h
    apply hv
    apply (euclideanEquiv (V := V)).injective
    simpa using h
  simpa [Function.comp_def] using (ne_of_gt (real_inner_self_pos.mpr hv'))

theorem anisotropic (v : V) (hv : form ρ hρ v v = 0) : v = 0 := by
  by_contra h
  exact (ne_of_gt (positive ρ hρ h)) hv

theorem invariant (k : G) (v w : V) :
    form ρ hρ (ρ k v) (ρ k w) = form ρ hρ v w := by
  simpa only [form_apply, average, map_mul, Module.End.mul_apply] using
    integral_mul_right_eq_self (μ := normalizedHaar G)
      (fun g => inner ℝ (euclideanEquiv (ρ g v)) (euclideanEquiv (ρ g w))) k
end HaarRealForm
end MathieuProperty
