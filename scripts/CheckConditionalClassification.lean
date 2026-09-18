import MathieuProperty.ConditionalClassification

/-! Independently check the exact external interface and conditional endpoint.
The examples prove implications; none supplies or proves multivariate DvK. -/

open MathieuProperty
open scoped Manifold ContDiff

/-- The interface is definitionally the original T04 / thm:dvdk target. -/
example : MultivariateDvK =
    (∀ (d : ℕ) (f : MultiLaurent d), f ≠ 0 →
      (∀ m : ℕ, 1 ≤ m → constantTerm (f ^ m) = 0) →
      (0 : Fin d → ℝ) ∉ newtonPolytope f) := rfl

/-- A theorem in the native Laurent representation needs no structural adapter. -/
example (hExternal : ∀ (d : ℕ) (f : MultiLaurent d), f ≠ 0 →
    (∀ m : ℕ, 1 ≤ m → constantTerm (f ^ m) = 0) →
    (0 : Fin d → ℝ) ∉ newtonPolytope f) :
    ∀ d : ℕ, HasMathieuProperty (Torus d) :=
  torus_mathieu_of_dvk hExternal

section CompactConnectedLieGroup
variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G]
  [CompactSpace G] [ConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

include E in
/-- The entire main equivalence, expanding the Mathieu predicate and assuming
only the original DvK formula in addition to the standing group hypotheses. -/
example (hExternal : ∀ (d : ℕ) (f : MultiLaurent d), f ≠ 0 →
    (∀ m : ℕ, 1 ≤ m → constantTerm (f ^ m) = 0) →
    (0 : Fin d → ℝ) ∉ newtonPolytope f) :
    (IsMathieuSubspace (LinearMap.ker (representativeIntegral G)) ↔
      ∀ g h : G, g * h = h * g) ∧
    ((∀ g h : G, g * h = h * g) ↔ ∃ d : ℕ, Nonempty (G ≃ₜ* Torus d)) :=
  classification_of_dvk (E := E) hExternal

end CompactConnectedLieGroup
