import MathieuProperty.ProjectedRepresentatives
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Haar transfer from generator-wise lifts. The lifts need not constitute a
homomorphism from SU(2). The resulting representative-function counterexample
uses full invariance of the coordinate pushforward, not root integration. -/

noncomputable section
open MeasureTheory
namespace MathieuProperty
open Hopf
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Symmetries of coordinates which can individually be realized by a left
translation. No compatibility of chosen lifts is required. -/
def coordinateLiftSubgroup (Φ : G → Space) : Subgroup SU2 where
  carrier := {k | ∃ h : G, ∀ g, Φ (h*g) = k • Φ g}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro k l ⟨h,hh⟩ ⟨j,hj⟩
    refine ⟨h*j, fun g => ?_⟩
    rw [mul_assoc, hh, hj, mul_smul]
  inv_mem' := by
    rintro k ⟨h,hh⟩
    refine ⟨h⁻¹, fun g => ?_⟩
    have he := hh (h⁻¹*g)
    rw [← mul_assoc, mul_inv_cancel, one_mul] at he
    rw [he, inv_smul_smul]

/-- Generator-wise coordinate lifts imply invariance under the whole SU(2) action. -/
theorem haar_pushforward_invariant_of_generators (Φ : G → Space) (hΦ : Continuous Φ)
    (S : Set SU2) (hS : Subgroup.closure S = ⊤)
    (hlift : ∀ k ∈ S, ∃ h : G, ∀ g, Φ (h*g) = k • Φ g) :
    SMulInvariantMeasure SU2 Space (Measure.map Φ (normalizedHaar G)) := by
  have hall : ∀ k : SU2, ∃ h : G, ∀ g, Φ (h*g) = k • Φ g := by
    have hc : Subgroup.closure S ≤ coordinateLiftSubgroup Φ :=
      (Subgroup.closure_le (coordinateLiftSubgroup Φ)).mpr hlift
    rw [hS] at hc
    intro k
    exact hc (Subgroup.mem_top k)
  constructor
  intro k A hA
  obtain ⟨h,hh⟩ := hall k
  have hmap : Measure.map (fun z : Space => k • z) (Measure.map Φ (normalizedHaar G)) =
      Measure.map Φ (normalizedHaar G) := by
    rw [Measure.map_map (by fun_prop) hΦ.measurable]
    have he : (fun z : Space => k • z) ∘ Φ = Φ ∘ (fun g => h*g) := funext (fun g => (hh g).symm)
    rw [he, ← Measure.map_map hΦ.measurable (by fun_prop), map_mul_left_eq_self]
  rw [← Measure.map_apply (by fun_prop) hA, hmap]

/-- Any nonzero representative coordinate pair with SU(2)-invariant Haar
pushforward supplies the manuscript's pure and Pascal-row marked moments. -/
theorem representative_invariant_tower (f₀ f₁ : representativeFunctions (G := G))
    [SMulInvariantMeasure SU2 Space
      (Measure.map (fun g => (f₀.val g, f₁.val g)) (normalizedHaar G))] :
    (∀ m : ℕ, 1 ≤ m → representativeIntegral G (representativeP f₀ f₁ ^ m) = 0) ∧
    (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
      representativeIntegral G (representativeQ f₀ f₁ ^ s * representativeP f₀ f₁ ^ m) =
        (momentConstant m : ℂ) * ((m-1).choose (s-1) : ℂ) *
          representativeIntegral G (representativeA f₀ f₁ ^ (4*m+s))) := by
  have hc : Continuous (fun g => (f₀.val g, f₁.val g)) := f₀.val.continuous.prodMk f₁.val.continuous
  have ht := projected_haar_moments_of_invariant _ hc
  constructor
  · intro m hm
    change (∫ g, (representativeP f₀ f₁).val g ^ m ∂normalizedHaar G) = 0
    simp_rw [representativeP_apply]
    exact ht.1 m hm
  · intro m s hm hs
    have ha : representativeIntegral G (representativeA f₀ f₁ ^ (4*m+s)) =
        ((∫ g, a (f₀.val g, f₁.val g)^(4*m+s) ∂normalizedHaar G : ℝ) : ℂ) := by
      change (∫ g, (representativeA f₀ f₁).val g ^ (4*m+s) ∂normalizedHaar G) = _
      simp_rw [representativeA_apply, ← Complex.ofReal_pow]
      rw [integral_complex_ofReal]
    rw [ha]
    change (∫ g, (representativeQ f₀ f₁).val g ^ s * (representativeP f₀ f₁).val g ^ m
      ∂normalizedHaar G) = _
    simp_rw [representativeQ_apply, representativeP_apply]
    exact ht.2 m s hm hs

/-- Strict positivity follows from nonconcentration, without a root subgroup. -/
theorem representative_invariant_positive (f₀ f₁ : representativeFunctions (G := G))
    [SMulInvariantMeasure SU2 Space
      (Measure.map (fun g => (f₀.val g, f₁.val g)) (normalizedHaar G))]
    (h1 : (f₀.val 1, f₁.val 1) ≠ 0) (m s : ℕ)
    (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∃ c : ℝ, 0 < c ∧ representativeIntegral G
      (representativeQ f₀ f₁ ^ s * representativeP f₀ f₁ ^ m) = (c : ℂ) := by
  obtain ⟨c,hc,he⟩ := projected_haar_positive_of_invariant
    (fun g => (f₀.val g, f₁.val g)) (f₀.val.continuous.prodMk f₁.val.continuous) h1 m s hm hs hsm
  refine ⟨c,hc,?_⟩
  change (∫ g, (representativeQ f₀ f₁).val g ^ s * (representativeP f₀ f₁).val g ^ m
    ∂normalizedHaar G) = _
  simpa only [representativeQ_apply, representativeP_apply] using he

theorem representative_invariant_not_mathieu (f₀ f₁ : representativeFunctions (G := G))
    [SMulInvariantMeasure SU2 Space
      (Measure.map (fun g => (f₀.val g, f₁.val g)) (normalizedHaar G))]
    (h1 : (f₀.val 1, f₁.val 1) ≠ 0) : ¬ HasMathieuProperty G := by
  apply not_isMathieuSubspace_of_witness (LinearMap.ker (representativeIntegral G))
    (representativeP f₀ f₁) (representativeQ f₀ f₁)
  · exact (representative_invariant_tower f₀ f₁).1
  · intro m hm
    change representativeIntegral G (representativeQ f₀ f₁ * representativeP f₀ f₁ ^ m) ≠ 0
    obtain ⟨c,hc,he⟩ := representative_invariant_positive f₀ f₁ h1 m 1 hm (by omega) hm
    simp only [pow_one] at he
    rw [he]
    exact Complex.ofReal_ne_zero.mpr hc.ne'

end MathieuProperty
