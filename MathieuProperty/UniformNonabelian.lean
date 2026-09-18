import MathieuProperty.SimpleGroupMarkerTower
import MathieuProperty.AdjointQuotient

/-! The full uniform nonabelian marker-tower theorem. The adjoint simple
quotient is constructed, and its tower is pulled back with normalized Haar
measure. No simply connected cover or root subgroup is assumed. -/
noncomputable section
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
open CompactAdjoint
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G]
  [CompactSpace G] [ConnectedSpace G] [MeasurableSpace G] [BorelSpace G]
local instance uniformNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance uniformFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)

include E

/-- Manuscript uniform nonabelian theorem, with all quantifiers and moment
ranges expanded by `HasMarkerTower`. The quotient and its simple-group tower
are proved constructions, not hypotheses. -/
theorem uniform_nonabelian (hn : ¬ ∀ g h : G, g*h = h*g) : HasMarkerTower G := by
  obtain ⟨I,hI,_⟩ := exists_simple_factor (E := E) hn
  let : NormedRealLieAlgebra (idealModel (ambientSimpleFactor I)) :=
    inferInstanceAs (NormedRealLieAlgebra (ambientSimpleFactor I))
  let : IsTopologicalGroup (AdjointSimpleGroup I hI) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ,simpleAutomorphismModel I) ∞
  let : MeasurableSpace (AdjointSimpleGroup I hI) := borel _
  let : BorelSpace (AdjointSimpleGroup I hI) := ⟨rfl⟩
  exact (compact_simple_marker_tower (E := simpleAutomorphismModel I)
    (G := AdjointSimpleGroup I hI)).pullback (adjointQuotientMap I hI)
    (adjointQuotientMap_continuous I hI) (adjointQuotientMap_surjective I hI)

/-- The nonabelian half of the classification is unconditional. -/
theorem nonabelian_not_mathieu (hn : ¬ ∀ g h : G, g*h = h*g) : ¬ HasMathieuProperty G :=
  (uniform_nonabelian (E := E) hn).not_mathieu

/-- The Mathieu property forces a compact connected Lie group to be abelian. -/
theorem HasMathieuProperty.mul_comm (h : HasMathieuProperty G) : ∀ g k : G, g*k = k*g := by
  by_contra hn
  exact nonabelian_not_mathieu (E := E) hn h

end MathieuProperty
