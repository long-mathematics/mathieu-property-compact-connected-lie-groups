import MathieuProperty.MarkerTower
import MathieuProperty.RankOneAdjoint
import MathieuProperty.AdjointRankTwo

/-! The complete compact-simple-group marker tower, split into rank one and
rank at least two. No highest-weight existence, root integration, or simply
connected covering hypothesis occurs. -/
noncomputable section
namespace MathieuProperty

/-- The central SU(2) quotient has the full tower with constant radial function 1. -/
theorem Hopf.su2_adjoint_marker_tower : HasMarkerTower Hopf.SU2Adjoint := by
  obtain ⟨P,Q,hp,hm,_⟩ := Hopf.su2_central_quotient_tower
    (Subgroup.center Hopf.SU2) le_rfl
  refine ⟨1,P,Q,?_,one_ne_zero,hp,?_,?_,?_⟩
  · intro g
    exact ⟨1,by norm_num,by simp⟩
  · intro m s hml hsl
    simpa only [one_pow,representativeIntegral_one,mul_one] using hm m s hml hsl
  · intro m s hml hsm
    rw [hm m s hml (by omega),Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · intro m s hml hsl hsm
    refine ⟨momentConstant m*((m-1).choose (s-1) : ℝ),pascal_marker_pos m s hml hsl hsm,?_⟩
    rw [hm m s hml hsl]
    push_cast
    rfl

open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [ConnectedSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
local instance simpleTowerNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance simpleTowerFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

/-- Full rank-one tower, pulled back from the concrete adjoint form. -/
theorem AdjointRankOne.marker_tower
    (hr : Module.finrank ℝ (CompactCartanRootData.realCartan (E := E) (G := G)) = 1) :
    HasMarkerTower G := by
  let e := (AdjointRankOne.exists_center_quotient_equiv hr).some
  let π : G →* Hopf.SU2Adjoint := e.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)
  exact Hopf.su2_adjoint_marker_tower.pullback π
    (e.continuous.comp QuotientGroup.continuous_mk)
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

include E

/-- Full manuscript tower for every compact connected group with simple real
Lie algebra, including all central forms and the simply connected case. -/
theorem compact_simple_marker_tower : HasMarkerTower G := by
  let : Nontrivial (GroupLieAlgebra 𝓘(ℝ,E) G) := LieAlgebra.IsSimple.nontrivial ℝ _
  have hp : 0 < Module.finrank ℝ (CompactCartanRootData.realCartan (E := E) (G := G)) :=
    Module.finrank_pos
  by_cases hr : Module.finrank ℝ (CompactCartanRootData.realCartan (E := E) (G := G)) = 1
  · exact AdjointRankOne.marker_tower hr
  · obtain ⟨A,P,Q,hA,hA0,hpure,hmark,hzero,hpos,_⟩ := AdjointRankTwo.marker_tower (E := E) (G := G) (by omega)
    exact ⟨A,P,Q,hA,hA0,hpure,hmark,hzero,hpos⟩

/-- Every compact connected simple group fails the Mathieu property. -/
theorem compact_simple_not_mathieu : ¬ HasMathieuProperty G :=
  (compact_simple_marker_tower (E := E) (G := G)).not_mathieu

end MathieuProperty
