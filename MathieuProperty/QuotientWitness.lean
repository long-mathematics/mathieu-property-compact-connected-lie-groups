import MathieuProperty.CenterDescent
import MathieuProperty.DoubletWitness

/-! Exact witness towers on central quotients of a supplied irreducible doublet.

Center descent constructs the quotient representative functions. Normalized Haar
pushforward transports all moments, including nonnegativity, nonvanishing, and
the zero/positive ranges. Universal existence of the source representation and
of a simply connected simple cover remains a separate obligation.
-/

noncomputable section
namespace MathieuProperty
open Hopf
variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (hρ : ∀ v, Continuous (fun g => ρ g v))
  [Representation.IsIrreducible (unitaryToRepresentation ρ)]
  (W : Submodule ℂ E) (e : W ≃ₗᵢ[ℂ] EuclideanPair)
  (φ : SU2 →* G) (hW : ∀ k, W.map (ρ (φ k)).toLinearEquiv.toLinearMap = W)
  (he : ∀ k (w : W), doubletProjection W e (ρ (φ k) w) = k • WithLp.ofLp (e w))
  (N : Subgroup G) (hN : N ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ N)] [BorelSpace (G ⧸ N)]

include hρ hW he in
theorem center_quotient_tower :
    letI : N.Normal := Subgroup.normal_of_le_center hN
    ∃ A P Q : representativeFunctions (G := G ⧸ N),
      (∀ x, ∃ r : ℝ, 0 ≤ r ∧ A.val x = (r : ℂ)) ∧ A ≠ 0 ∧
      (∀ m : ℕ, 1 ≤ m → representativeIntegral (G ⧸ N) (P ^ m) = 0) ∧
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
        representativeIntegral (G ⧸ N) (Q ^ s * P ^ m) =
          (momentConstant m : ℂ) * ((m - 1).choose (s - 1) : ℂ) *
            representativeIntegral (G ⧸ N) (A ^ (4 * m + s))) ∧
      (∀ m s : ℕ, 1 ≤ m → m < s →
        representativeIntegral (G ⧸ N) (Q ^ s * P ^ m) = 0) ∧
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s → s ≤ m → ∃ r : ℝ, 0 < r ∧
        representativeIntegral (G ⧸ N) (Q ^ s * P ^ m) = (r : ℂ)) ∧
      ¬ HasMathieuProperty (G ⧸ N) := by
  let : N.Normal := Subgroup.normal_of_le_center hN
  obtain ⟨A, T, U, V, P, Q, h⟩ := center_descent ρ hρ W e N hN
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hA : representativePullback q hq A = doubletA ρ hρ W e := by
    apply Subtype.ext
    ext g
    exact (h g).1.trans (doubletA_apply ρ hρ W e g).symm
  have hP : representativePullback q hq P = doubletP ρ hρ W e := by
    apply Subtype.ext
    ext g
    exact (h g).2.2.2.2.1.trans (doubletP_apply ρ hρ W e g).symm
  have hQ : representativePullback q hq Q = doubletQ ρ hρ W e := by
    apply Subtype.ext
    ext g
    exact (h g).2.2.2.2.2.trans (doubletQ_apply ρ hρ W e g).symm
  have hpure (m : ℕ) (hm : 1 ≤ m) : representativeIntegral (G ⧸ N) (P ^ m) = 0 := by
    rw [← representativeIntegral_pullback q hq hqs, map_pow, hP]
    exact doublet_pure ρ hρ W e φ hW he m hm
  have hmark (m s : ℕ) :
      representativeIntegral (G ⧸ N) (Q ^ s * P ^ m) =
        representativeIntegral G (doubletQ ρ hρ W e ^ s * doubletP ρ hρ W e ^ m) := by
    rw [← representativeIntegral_pullback q hq hqs, map_mul, map_pow, map_pow, hQ, hP]
  refine ⟨A, P, Q, ?_, ?_, hpure, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨g, rfl⟩ := hqs x
    refine ⟨a (doubletCoordinates W e ρ g), a_nonneg _, (h g).1⟩
  · intro hz
    have hh := congrArg (representativePullback q hq) hz
    rw [hA, map_zero] at hh
    exact doubletA_ne_zero ρ hρ W e hh
  · intro m s hm hs
    rw [hmark, doublet_marked ρ hρ W e φ hW he m s hm hs]
    rw [← representativeIntegral_pullback q hq hqs,
      map_pow (representativePullback q hq) A (4 * m + s), hA]
  · intro m s hm hsm
    rw [hmark]
    exact doublet_marked_zero ρ hρ W e φ hW he m s hm hsm
  · intro m s hm hs hsm
    rw [hmark]
    exact doublet_marked_positive ρ hρ W e φ hW he m s hm hs hsm
  · apply not_isMathieuSubspace_of_witness (LinearMap.ker (representativeIntegral (G ⧸ N))) P Q hpure
    intro m hm
    change representativeIntegral (G ⧸ N) (Q * P ^ m) ≠ 0
    obtain ⟨r, hr, hi⟩ := doublet_marked_positive ρ hρ W e φ hW he m 1 hm (by omega) hm
    have hi' := hmark m 1
    simp only [pow_one] at hi hi'
    rw [hi', hi]
    exact Complex.ofReal_ne_zero.mpr hr.ne'

end MathieuProperty
