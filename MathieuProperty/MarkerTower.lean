import MathieuProperty.Haar
import MathieuProperty.MomentConstant

/-! The full manuscript marker-tower property and its normalized-Haar pullback.
This is a conclusion to be proved, not a structural typeclass assumption. -/
noncomputable section
namespace MathieuProperty
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Exactly the nonnegative, nonzero representative triple and all moment ranges
in the manuscript's uniform nonabelian theorem. -/
def HasMarkerTower : Prop :=
  ∃ A P Q : representativeFunctions (G := G),
    (∀ g, ∃ r : ℝ, 0 ≤ r ∧ A.val g = (r : ℂ)) ∧ A ≠ 0 ∧
    (∀ m : ℕ, 1 ≤ m → representativeIntegral G (P^m) = 0) ∧
    (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
      representativeIntegral G (Q^s*P^m) =
        (momentConstant m : ℂ)*((m-1).choose (s-1) : ℂ)*
          representativeIntegral G (A^(4*m+s))) ∧
    (∀ m s : ℕ, 1 ≤ m → m < s → representativeIntegral G (Q^s*P^m) = 0) ∧
    (∀ m s : ℕ, 1 ≤ m → 1 ≤ s → s ≤ m → ∃ r : ℝ, 0 < r ∧
      representativeIntegral G (Q^s*P^m) = (r : ℂ))

variable {G}

/-- The positive first marker contradicts the Mathieu condition. -/
theorem HasMarkerTower.not_mathieu (h : HasMarkerTower G) : ¬ HasMathieuProperty G := by
  obtain ⟨A,P,Q,_,_,hp,_,_,hq⟩ := h
  apply not_mathieu_of_representative_witness G P Q hp
  intro m hm
  obtain ⟨r,hr,he⟩ := hq m 1 hm (by omega) hm
  simp only [pow_one] at he
  rw [he]
  exact Complex.ofReal_ne_zero.mpr hr.ne'

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]

/-- Every component of the exact tower pulls back along a continuous surjection. -/
theorem HasMarkerTower.pullback (h : HasMarkerTower H) (π : G →* H)
    (hc : Continuous π) (hs : Function.Surjective π) : HasMarkerTower G := by
  obtain ⟨A,P,Q,hA,hA0,hp,hm,hz,hpos⟩ := h
  let p := representativePullback π hc
  refine ⟨p A,p P,p Q,?_,?_,?_,?_,?_,?_⟩
  · intro g
    exact hA (π g)
  · intro he
    apply hA0
    apply Subtype.ext
    ext x
    obtain ⟨g,rfl⟩ := hs x
    exact congrArg (fun f : representativeFunctions (G := G) => f.val g) he
  · intro m hml
    rw [← map_pow,representativeIntegral_pullback π hc hs]
    exact hp m hml
  · intro m s hml hsl
    rw [← map_pow,← map_pow,← map_mul,representativeIntegral_pullback π hc hs,
      ← map_pow,representativeIntegral_pullback π hc hs]
    exact hm m s hml hsl
  · intro m s hml hsm
    rw [← map_pow,← map_pow,← map_mul,representativeIntegral_pullback π hc hs]
    exact hz m s hml hsm
  · intro m s hml hsl hsm
    rw [← map_pow,← map_pow,← map_mul,representativeIntegral_pullback π hc hs]
    exact hpos m s hml hsl hsm

end MathieuProperty
