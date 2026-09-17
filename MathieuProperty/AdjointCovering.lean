import MathieuProperty.FullAdjoint
import MathieuProperty.SimpleGroupCenter
import MathieuProperty.CentralCovering

/-! The actual adjoint homomorphism is a covering onto its image.
On a connected group its kernel equals the center, by uniqueness of smooth
homomorphisms with the same differential. The topological quotient equivalence
and the discrete center of a simple group give the covering map. This does not
construct a simply connected cover. -/

noncomputable section
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.FullAdjoint
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [PreconnectedSpace G]

/-- On a connected group, the kernel of the actual adjoint map is exactly the center. -/
theorem ker_eq_center : (toAutomorphisms (E := E) (G := G)).ker = Subgroup.center G := by
  ext g
  constructor
  · intro hg
    have had : CompactAdjoint.adjointLinear (E := E) g = ContinuousLinearMap.id ℝ _ :=
      congrArg (fun u : Target (E := E) (G := G) => u.val.val) hg
    let c : G →* G := (MulAut.conj g).toMonoidHom
    have hc : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c := CompactAdjoint.conjugation_contMDiff g
    have hd : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c 1 =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (MonoidHom.id G) 1 := by
      rw [show (MonoidHom.id G : G → G) = id from rfl, mfderiv_id]
      exact had
    have he := LieHomCalculus.hom_eq_of_mfderiv_eq c (MonoidHom.id G) hc contMDiff_id hd
    apply Subgroup.mem_center_iff.mpr
    intro h
    have hx := DFunLike.congr_fun he h
    change g*h*g⁻¹ = h at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  · intro hg
    apply Subtype.ext
    apply Units.ext
    have he : (fun x : G => g*x*g⁻¹) = id := by
      funext x
      rw [← Subgroup.mem_center_iff.mp hg x, mul_assoc, mul_inv_cancel, mul_one]
      rfl
    change CompactAdjoint.adjointLinear (E := E) g = 1
    rw [CompactAdjoint.adjointLinear, he, mfderiv_id]
    rfl

variable [IsTopologicalGroup G] [CompactSpace G]

def ontoImage : G →* (toAutomorphisms (E := E) (G := G)).range :=
  (toAutomorphisms (E := E) (G := G)).rangeRestrict

omit [PreconnectedSpace G] [CompactSpace G] in
theorem ontoImage_continuous : Continuous (ontoImage (E := E) (G := G)) :=
  (toAutomorphisms_continuous (E := E) (G := G)).subtype_mk _

omit [PreconnectedSpace G] in
def quotientRangeEquiv :
    G ⧸ (toAutomorphisms (E := E) (G := G)).ker ≃ₜ* (toAutomorphisms (E := E) (G := G)).range := by
  let e := QuotientGroup.quotientKerEquivRange (toAutomorphisms (E := E) (G := G))
  have hc : Continuous e := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact ontoImage_continuous (E := E) (G := G)
  exact
    { e with
      continuous_toFun := hc
      continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

local instance adjointCoverNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  groupLieAlgebraNormed
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)] [T2Space G]

theorem ontoImage_covering : IsCoveringMap (ontoImage (E := E) (G := G)) := by
  have hd : IsDiscrete ((toAutomorphisms (E := E) (G := G)).ker : Set G) := by
    rw [ker_eq_center]
    exact isDiscrete_iff_discreteTopology.mpr (SimpleGroupCenter.center_discrete (E := E))
  have hq := ((toAutomorphisms (E := E) (G := G)).ker.isQuotientCoveringMap hd).isCoveringMap
  apply isLocalHomeomorph_iff_isCoveringMap.mp
  exact (quotientRangeEquiv (E := E) (G := G)).toHomeomorph.isLocalHomeomorph.comp hq.isLocalHomeomorph

end MathieuProperty.FullAdjoint
