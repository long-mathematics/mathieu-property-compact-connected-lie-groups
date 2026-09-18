import MathieuProperty.SU2AdjointAction
import MathieuProperty.LieAutomorphismEquiv
import MathieuProperty.AdjointCovering

/-! Identification of the adjoint form of an actual rank-one compact connected
simple Lie group with SU(2)/{±1}, without a simply connected covering theorem. -/
noncomputable section
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.AdjointRankOne
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [ConnectedSpace G]
local instance rankOneAdjointNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance rankOneAdjointFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

/-- The exact rank-one obligation AR03: the adjoint form is concretely
SU(2)/center(SU(2)), with center {±1}. -/
theorem exists_center_quotient_equiv
    (hr : Module.finrank ℝ (CompactCartanRootData.realCartan (E := E) (G := G)) = 1) :
    Nonempty ((G ⧸ Subgroup.center G) ≃ₜ* Hopf.SU2Adjoint) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  obtain ⟨a⟩ := exists_matrix_equiv hr
  let c := LieAutomorphism.congr a
  let : ConnectedSpace (LieAutomorphism.Group SU2AdjointAlgebra.Algebra) :=
    SU2AdjointAlgebra.automorphism_connected
  let : ConnectedSpace (FullAdjoint.Target (E := E) (G := G)) :=
    c.symm.surjective.connectedSpace c.symm.continuous
  let f := FullAdjoint.toAutomorphisms (E := E) (G := G)
  have hs : Function.Surjective f := by
    have hh : f.range = ⊤ := by
      apply SetLike.coe_injective
      rw [FullAdjoint.toAutomorphisms_range_eq_component,
        PreconnectedSpace.connectedComponent_eq_univ]
      rfl
    exact MonoidHom.range_eq_top.mp hh
  let e := (QuotientGroup.quotientMulEquivOfEq
      (FullAdjoint.ker_eq_center (E := E) (G := G)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hs)
  have he : Continuous e := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous f
    exact FullAdjoint.toAutomorphisms_continuous
  let q : (G ⧸ Subgroup.center G) ≃ₜ* FullAdjoint.Target (E := E) (G := G) :=
    { e with
      continuous_toFun := he
      continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 }
  exact ⟨(q.trans c).trans SU2AdjointAlgebra.quotientEquiv.symm⟩

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- Every rank-one compact connected simple group fails the Mathieu property,
by pulling back the already proved SU(2)/{±1} witness. -/
theorem not_mathieu
    (hr : Module.finrank ℝ (CompactCartanRootData.realCartan (E := E) (G := G)) = 1) :
    ¬ HasMathieuProperty G :=
  Hopf.not_mathieu_of_center_quotient_equiv (exists_center_quotient_equiv hr).some

end MathieuProperty.AdjointRankOne
