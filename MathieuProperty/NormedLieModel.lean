import MathieuProperty.ConnectedLie
/-! Compatible normed and Lie structures, without an extra structural hypothesis.
The actual group Lie algebra inherits the chart model norm; ideals inherit that norm. -/

noncomputable section
open scoped Manifold ContDiff
namespace MathieuProperty
/-- Shared additive/module data for a normed real Lie algebra. No bracket norm bound is assumed. -/
class NormedRealLieAlgebra (V : Type*) extends LieRing V, NormedAddCommGroup V,
    LieAlgebra ℝ V, NormedSpace ℝ V

@[instance_reducible]
def groupLieAlgebraNormed {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G] :
    NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := by
  letI : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G := LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
  exact { (inferInstance : LieRing (GroupLieAlgebra 𝓘(ℝ,E) G)),
    (inferInstance : NormedAddCommGroup E),
    (inferInstance : LieAlgebra ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)),
    (inferInstance : NormedSpace ℝ E) with }


instance idealNormedRealLieAlgebra {V : Type*} [NormedRealLieAlgebra V] (I : LieIdeal ℝ V) :
    NormedRealLieAlgebra I :=
  { (inferInstance : LieRing I), (inferInstance : NormedAddCommGroup I),
    (inferInstance : LieAlgebra ℝ I), (inferInstance : NormedSpace ℝ I) with }
end MathieuProperty
