import MathieuProperty.Projection

/-! Haar pushforward through continuous equivariant coordinates: compact support,
invariance, nonconcentration, and the resulting moment formulas. -/
noncomputable section
open MeasureTheory
namespace MathieuProperty
open Hopf
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem haar_pushforward_compact_support (Φ : G → Space) (hΦ : Continuous Φ) :
    IsCompact (Measure.map Φ (normalizedHaar G)).support := by
  have hc : IsCompact (Set.range Φ) := isCompact_range hΦ
  apply hc.of_isClosed_subset Measure.isClosed_support
  apply Measure.support_subset_of_isClosed hc.isClosed
  rw [mem_ae_map_iff hΦ.measurable.aemeasurable hc.measurableSet]
  exact Filter.Eventually.of_forall (fun g => Set.mem_range_self g)

theorem haar_pushforward_nonconcentration (Φ : G → Space) (hΦ : Continuous Φ) (h1 : Φ 1 ≠ 0) :
    0 < (Measure.map Φ (normalizedHaar G)) ({0}ᶜ : Set Space) := by
  rw [Measure.map_apply hΦ.measurable (measurableSet_singleton 0).compl]
  have ho : IsOpen (Φ ⁻¹' ({0}ᶜ : Set Space)) := isClosed_singleton.isOpen_compl.preimage hΦ
  exact ho.measure_pos (normalizedHaar G) ⟨1, h1⟩

theorem haar_pushforward_smul_invariant (Φ : G → Space) (hΦ : Continuous Φ)
    (φ : SU2 →* G) (heq : ∀ k g, Φ (φ k * g) = k • Φ g) :
    SMulInvariantMeasure SU2 Space (Measure.map Φ (normalizedHaar G)) := by
  constructor
  intro k S hS
  have hmap : Measure.map (fun z : Space => k • z) (Measure.map Φ (normalizedHaar G)) =
      Measure.map Φ (normalizedHaar G) := by
    rw [Measure.map_map (by fun_prop) hΦ.measurable]
    have he : (fun z : Space => k • z) ∘ Φ = Φ ∘ (fun g => φ k * g) := by
      funext g
      exact (heq k g).symm
    rw [he, ← Measure.map_map hΦ.measurable (by fun_prop), map_mul_left_eq_self]
  rw [← Measure.map_apply (by fun_prop) hS, hmap]

theorem haar_pushforward_ball_support (Φ : G → Space) (hΦ : Continuous Φ)
    (hb : ∀ g, a (Φ g) ≤ 1) :
    (Measure.map Φ (normalizedHaar G)).support ⊆ {z | a z ≤ 1} := by
  have hc : IsClosed {z : Space | a z ≤ 1} := isClosed_le continuous_a continuous_const
  apply Measure.support_subset_of_isClosed hc
  rw [mem_ae_map_iff hΦ.measurable.aemeasurable hc.measurableSet]
  exact Filter.Eventually.of_forall hb


/-- The radial-pushforward lemma for the coordinates constructed from a given
unitary defining doublet. Existence of that doublet on general simple groups is
not asserted here. -/
theorem doublet_radial_pushforward {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (W : Submodule ℂ E) [W.HasOrthogonalProjection]
    (e : W ≃ₗᵢ[ℂ] EuclideanPair) (φ : SU2 →* G)
    (hρ : Continuous (fun g => ρ g (doubletBaseVector W e)))
    (hW : ∀ k, W.map (ρ (φ k)).toLinearEquiv.toLinearMap = W)
    (he : ∀ k (w : W), doubletProjection W e (ρ (φ k) w) = k • WithLp.ofLp (e w)) :
    let μ := Measure.map (doubletCoordinates W e ρ) (normalizedHaar G)
    IsProbabilityMeasure μ ∧ IsCompact μ.support ∧ SMulInvariantMeasure SU2 Space μ ∧
      μ.support ⊆ {z | a z ≤ 1} ∧ 0 < μ ({0}ᶜ : Set Space) := by
  have hc := doubletCoordinates_continuous W e ρ hρ
  refine ⟨inferInstance, haar_pushforward_compact_support _ hc,
    haar_pushforward_smul_invariant _ hc φ (doubletCoordinates_equivariant W e ρ φ hW he),
    haar_pushforward_ball_support _ hc (doubletCoordinates_a_le W e ρ), ?_⟩
  apply haar_pushforward_nonconcentration _ hc
  simp

/-- The original group integrals equal the radial-transfer formulas for any
continuous equivariant coordinate map. -/
theorem projected_haar_moments (Φ : G → Space) (hΦ : Continuous Φ) (φ : SU2 →* G)
    (heq : ∀ k g, Φ (φ k * g) = k • Φ g) :
    (∀ m : ℕ, 1 ≤ m → (∫ g, P (Φ g)^m ∂normalizedHaar G) = 0) ∧
    (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
      (∫ g, Q (Φ g)^s * P (Φ g)^m ∂normalizedHaar G) =
        (momentConstant m : ℂ) * ((m-1).choose (s-1) : ℂ) *
          ((∫ g, a (Φ g)^(4*m+s) ∂normalizedHaar G : ℝ) : ℂ)) := by
  let μ := Measure.map Φ (normalizedHaar G)
  have : SMulInvariantMeasure SU2 Space μ := haar_pushforward_smul_invariant Φ hΦ φ heq
  have hc := haar_pushforward_compact_support Φ hΦ
  constructor
  · intro m hm
    have h := radial_pure μ hc m hm
    dsimp [μ] at h
    rw [integral_map (f := fun z => P z ^ m) hΦ.measurable.aemeasurable
      (continuous_P.pow m).aestronglyMeasurable] at h
    exact h
  · intro m s hm hs
    have h := radial_marked μ hc m s hm hs
    dsimp [μ] at h
    rw [integral_map (f := fun z => Q z ^ s * P z ^ m) hΦ.measurable.aemeasurable
      ((continuous_Q.pow s).mul (continuous_P.pow m)).aestronglyMeasurable,
      integral_map (f := fun z => a z ^ (4*m+s)) hΦ.measurable.aemeasurable
        (continuous_a.pow (4*m+s)).aestronglyMeasurable] at h
    exact h

theorem projected_haar_positive (Φ : G → Space) (hΦ : Continuous Φ) (φ : SU2 →* G)
    (heq : ∀ k g, Φ (φ k * g) = k • Φ g) (h1 : Φ 1 ≠ 0)
    (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∃ c : ℝ, 0 < c ∧ (∫ g, Q (Φ g)^s * P (Φ g)^m ∂normalizedHaar G) = (c : ℂ) := by
  let μ := Measure.map Φ (normalizedHaar G)
  have : SMulInvariantMeasure SU2 Space μ := haar_pushforward_smul_invariant Φ hΦ φ heq
  have h := radial_marked_positive μ (haar_pushforward_compact_support Φ hΦ)
    (haar_pushforward_nonconcentration Φ hΦ h1) m s hm hs hsm
  dsimp [μ] at h
  rw [integral_map (f := fun z => Q z ^ s * P z ^ m) hΦ.measurable.aemeasurable
    ((continuous_Q.pow s).mul (continuous_P.pow m)).aestronglyMeasurable] at h
  exact h

end MathieuProperty
