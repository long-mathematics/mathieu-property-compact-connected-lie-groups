import MathieuProperty.ProjectedRepresentatives

/-! The complete representative-function tower for a supplied unitary defining doublet.
This proves the transfer step; existence of the doublet on general simple groups
is a separate, still open obligation. -/

noncomputable section
open MeasureTheory
namespace MathieuProperty
open Hopf
variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (hρ : ∀ v, Continuous (fun g => ρ g v))
  (W : Submodule ℂ E) (e : W ≃ₗᵢ[ℂ] EuclideanPair)

theorem doublet_radial_integral (n : ℕ) :
    representativeIntegral G (doubletA ρ hρ W e ^ n) =
      ((∫ g, a (doubletCoordinates W e ρ g)^n ∂normalizedHaar G : ℝ) : ℂ) := by
  change (∫ g, (doubletA ρ hρ W e).val g ^ n ∂normalizedHaar G) = _
  simp_rw [doubletA_apply, ← Complex.ofReal_pow]
  rw [integral_complex_ofReal]

variable (φ : SU2 →* G)
  (hW : ∀ k, W.map (ρ (φ k)).toLinearEquiv.toLinearMap = W)
  (he : ∀ k (w : W), doubletProjection W e (ρ (φ k) w) = k • WithLp.ofLp (e w))

include hρ hW he

theorem doublet_pure (m : ℕ) (hm : 1 ≤ m) :
    representativeIntegral G (doubletP ρ hρ W e ^ m) = 0 := by
  change (∫ g, (doubletP ρ hρ W e).val g ^ m ∂normalizedHaar G) = 0
  simp_rw [doubletP_apply]
  exact (projected_haar_moments _ (doubletCoordinates_continuous W e ρ (hρ _)) φ
    (doubletCoordinates_equivariant W e ρ φ hW he)).1 m hm

theorem doublet_marked (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    representativeIntegral G (doubletQ ρ hρ W e ^ s * doubletP ρ hρ W e ^ m) =
      (momentConstant m : ℂ) * ((m-1).choose (s-1) : ℂ) *
        representativeIntegral G (doubletA ρ hρ W e ^ (4*m+s)) := by
  rw [doublet_radial_integral]
  change (∫ g, (doubletQ ρ hρ W e).val g ^ s * (doubletP ρ hρ W e).val g ^ m
    ∂normalizedHaar G) = _
  simp_rw [doubletQ_apply, doubletP_apply]
  exact (projected_haar_moments _ (doubletCoordinates_continuous W e ρ (hρ _)) φ
    (doubletCoordinates_equivariant W e ρ φ hW he)).2 m s hm hs

theorem doublet_marked_zero (m s : ℕ) (hm : 1 ≤ m) (hsm : m < s) :
    representativeIntegral G (doubletQ ρ hρ W e ^ s * doubletP ρ hρ W e ^ m) = 0 := by
  rw [doublet_marked ρ hρ W e φ hW he m s hm (by omega), Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem doublet_marked_positive (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∃ c : ℝ, 0 < c ∧
      representativeIntegral G (doubletQ ρ hρ W e ^ s * doubletP ρ hρ W e ^ m) = (c : ℂ) := by
  obtain ⟨c, hc, hi⟩ := projected_haar_positive _ (doubletCoordinates_continuous W e ρ (hρ _)) φ
    (doubletCoordinates_equivariant W e ρ φ hW he) (by simp) m s hm hs hsm
  refine ⟨c, hc, ?_⟩
  change (∫ g, (doubletQ ρ hρ W e).val g ^ s * (doubletP ρ hρ W e).val g ^ m
    ∂normalizedHaar G) = _
  simp_rw [doubletQ_apply, doubletP_apply]
  exact hi

/-- A transfer theorem with explicit representation data, not an existence theorem
for root subgroups or a classification of compact Lie groups. -/
theorem unitary_doublet_not_mathieu : ¬ HasMathieuProperty G := by
  apply not_isMathieuSubspace_of_witness (LinearMap.ker (representativeIntegral G))
    (doubletP ρ hρ W e) (doubletQ ρ hρ W e)
  · exact doublet_pure ρ hρ W e φ hW he
  · intro m hm
    change representativeIntegral G (doubletQ ρ hρ W e * doubletP ρ hρ W e ^ m) ≠ 0
    obtain ⟨c, hc, hi⟩ := doublet_marked_positive ρ hρ W e φ hW he m 1 hm (by omega) hm
    simp only [pow_one] at hi
    rw [hi]
    exact Complex.ofReal_ne_zero.mpr hc.ne'

end MathieuProperty
