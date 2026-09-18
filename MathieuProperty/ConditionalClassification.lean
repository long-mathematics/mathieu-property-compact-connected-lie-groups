import MathieuProperty.ConditionalTorus
import MathieuProperty.AbelianTorus
import MathieuProperty.UniformNonabelian

/-! The full main classification relative to the single explicit multivariate
DvK proposition. No root representation, root integration, simple covering,
or further unproved mathematical input is assumed. This does not assert DvK
or the unconditional classification. -/

open scoped Manifold ContDiff
namespace MathieuProperty

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G]
  [CompactSpace G] [ConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

include E

/-- Conditional Mathieu iff abelian: the nonabelian direction is unconditional;
the abelian direction uses only the explicit DvK input and proved torus identification. -/
theorem mathieu_iff_abelian_of_dvk (hDvK : MultivariateDvK) :
    HasMathieuProperty G ↔ ∀ g h : G, g * h = h * g := by
  constructor
  · exact fun h => h.mul_comm (E := E)
  · intro hc
    obtain ⟨e⟩ := CompactLieTorus.exists_torus_equiv (E := E) hc
    exact mathieu_of_torus_equiv_of_dvk hDvK e

/-- Conditional Mathieu iff torus, with an actual topological group equivalence. -/
theorem mathieu_iff_torus_of_dvk (hDvK : MultivariateDvK) :
    HasMathieuProperty G ↔ ∃ d : ℕ, Nonempty (G ≃ₜ* Torus d) :=
  (mathieu_iff_abelian_of_dvk (E := E) hDvK).trans
    (CompactLieTorus.abelian_iff_torus (E := E))

/-- The manuscript's three-way compact-connected-Lie-group classification,
conditional on exactly the Laurent-polynomial multivariate DvK statement.
The second equivalence is already unconditional. -/
theorem classification_of_dvk (hDvK : MultivariateDvK) :
    (HasMathieuProperty G ↔ ∀ g h : G, g * h = h * g) ∧
    ((∀ g h : G, g * h = h * g) ↔ ∃ d : ℕ, Nonempty (G ≃ₜ* Torus d)) :=
  ⟨mathieu_iff_abelian_of_dvk (E := E) hDvK,
    CompactLieTorus.abelian_iff_torus (E := E)⟩

end MathieuProperty
