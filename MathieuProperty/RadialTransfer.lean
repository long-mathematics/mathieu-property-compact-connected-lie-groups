import MathieuProperty.HopfIntegral

/-! Universal radial transfer for every finite compactly supported SU(2)-invariant Borel measure. -/

noncomputable section
open MeasureTheory
namespace MathieuProperty.Hopf

theorem orbit_pure (z : Space) (m : ℕ) (hm : 1 ≤ m) :
    (∫ g : SU2, P (g • z) ^ m ∂normalizedHaar SU2) = 0 := by
  simpa [sphere_pure m hm] using su2_orbit_moment z m 0

theorem orbit_marked (z : Space) (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (∫ g : SU2, Q (g • z) ^ s * P (g • z) ^ m ∂normalizedHaar SU2) =
      (momentConstant m : ℂ) * ((m - 1).choose (s - 1) : ℂ) * (a z : ℂ) ^ (4 * m + s) := by
  rw [su2_orbit_moment, sphere_marked m s hm hs]
  ring

variable (μ : Measure Space) [IsFiniteMeasure μ] [SMulInvariantMeasure SU2 Space μ]
  (hμ : IsCompact μ.support)

include hμ

theorem radial_pure (m : ℕ) (hm : 1 ≤ m) : (∫ z, P z ^ m ∂μ) = 0 := by
  simpa [sphere_pure m hm] using radial_moment_factorization μ hμ m 0

theorem radial_marked (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (∫ z, Q z ^ s * P z ^ m ∂μ) =
      (momentConstant m : ℂ) * ((m - 1).choose (s - 1) : ℂ) *
        ((∫ z, a z ^ (4 * m + s) ∂μ : ℝ) : ℂ) := by
  rw [radial_moment_factorization μ hμ, sphere_marked m s hm hs]
  simp only [← Complex.ofReal_pow, integral_complex_ofReal]
  ring

theorem radial_marked_zero (m s : ℕ) (hm : 1 ≤ m) (hsm : m < s) :
    (∫ z, Q z ^ s * P z ^ m ∂μ) = 0 := by
  rw [radial_marked μ hμ m s hm (by omega), Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem radial_marked_positive (hzero : 0 < μ ({0}ᶜ : Set Space))
    (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∃ c : ℝ, 0 < c ∧ (∫ z, Q z ^ s * P z ^ m ∂μ) = (c : ℂ) := by
  refine ⟨momentConstant m * ((m - 1).choose (s - 1) : ℝ) *
    ∫ z, a z ^ (4 * m + s) ∂μ, ?_, ?_⟩
  · exact mul_pos (pascal_marker_pos m s hm hs hsm)
      (radial_integral_pos μ hμ hzero _ (by omega))
  · rw [radial_marked μ hμ m s hm hs]
    push_cast
    rfl

/-- The complete universal radial-transfer theorem, including nonconcentration,
radial positivity, and the exact vanishing and strict positivity ranges. -/
theorem radial_transfer :
    (∀ m : ℕ, 1 ≤ m → (∫ z, P z ^ m ∂μ) = 0) ∧
    (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
      (∫ z, Q z ^ s * P z ^ m ∂μ) =
        (momentConstant m : ℂ) * ((m - 1).choose (s - 1) : ℂ) *
          ((∫ z, a z ^ (4 * m + s) ∂μ : ℝ) : ℂ)) ∧
    (∀ m s : ℕ, 1 ≤ m → m < s → (∫ z, Q z ^ s * P z ^ m ∂μ) = 0) ∧
    (0 < μ ({0}ᶜ : Set Space) →
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s → 0 < ∫ z, a z ^ (4 * m + s) ∂μ) ∧
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s → s ≤ m →
        ∃ c : ℝ, 0 < c ∧ (∫ z, Q z ^ s * P z ^ m ∂μ) = (c : ℂ))) := by
  refine ⟨radial_pure μ hμ, radial_marked μ hμ, radial_marked_zero μ hμ, ?_⟩
  intro hzero
  exact ⟨fun m s hm hs => radial_integral_pos μ hμ hzero _ (by omega),
    radial_marked_positive μ hμ hzero⟩

end MathieuProperty.Hopf
