import MathieuProperty.AbelianLattice
import MathieuProperty.LatticeTorus
import MathieuProperty.TorusCharacters
/-! Compact connected abelian real Lie groups are finite-dimensional tori.
The actual vector-group parametrization and the circle map in a basis of its
kernel lattice have the same kernel. Their quotient isomorphisms give a group
isomorphism, the quotient topology gives continuity, and compactness gives a
continuous inverse. The resulting torus has exactly the tangent-space dimension,
including the zero-dimensional case. -/

noncomputable section
open scoped Manifold ContDiff
open Module
namespace MathieuProperty
namespace AbelianParameters
set_option backward.isDefEq.respectTransparency false
variable {E G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CommGroup G] [TopologicalSpace G] [T2Space G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Fintype ι] [ConnectedSpace G] [CompactSpace G]

def circleMap (b : Basis ι ℝ E) : Multiplicative (ι → ℝ) →* (ι → Circle) :=
  LatticeTorus.map (kernel (G := G) b) (IsZLattice.basis (kernel (G := G) b))

theorem circleMap_continuous (b : Basis ι ℝ E) : Continuous (circleMap (G := G) b) :=
  LatticeTorus.map_continuous _ _

theorem circleMap_surjective (b : Basis ι ℝ E) : Function.Surjective (circleMap (G := G) b) :=
  LatticeTorus.map_surjective _ _

theorem circleMap_ker (b : Basis ι ℝ E) : (parameterMap (G := G) b).ker = (circleMap (G := G) b).ker := by
  ext x
  change parameterMap (G := G) b x = 1 ↔ x ∈ (circleMap (G := G) b).ker
  rw [circleMap,LatticeTorus.mem_map_ker,mem_kernel]
  rfl

def torusMulEquiv (b : Basis ι ℝ E) : G ≃* (ι → Circle) :=
  (QuotientGroup.quotientKerEquivOfSurjective (parameterMap (G := G) b) (parameterMap_surjective b)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (circleMap_ker (G := G) b)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (circleMap (G := G) b) (circleMap_surjective b)))

theorem torusMulEquiv_apply_parameter (b : Basis ι ℝ E) (x : Multiplicative (ι → ℝ)) :
    torusMulEquiv (G := G) b (parameterMap (G := G) b x) = circleMap (G := G) b x := by
  let e := QuotientGroup.quotientKerEquivOfSurjective (parameterMap (G := G) b) (parameterMap_surjective b)
  have he : e.symm (parameterMap (G := G) b x) = QuotientGroup.mk x :=
    e.symm_apply_eq.mpr rfl
  change ((QuotientGroup.quotientMulEquivOfEq (circleMap_ker (G := G) b)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (circleMap (G := G) b) (circleMap_surjective b)))
      (e.symm (parameterMap (G := G) b x)) = _
  rw [he,MulEquiv.trans_apply,QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem torusMulEquiv_continuous (b : Basis ι ℝ E) : Continuous (torusMulEquiv (G := G) b) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  let : SigmaCompactSpace (Multiplicative (ι → ℝ)) := inferInstanceAs (SigmaCompactSpace (ι → ℝ))
  have hs := parameterMap_surjective (G := G) b
  have hc := (parameterMap_smooth (G := G) b).continuous
  have ho := (parameterMap (G := G) b).isOpenMap_of_sigmaCompact hs hc
  apply (ho.isQuotientMap hc hs).continuous_iff.mpr
  have he : torusMulEquiv (G := G) b ∘ parameterMap (G := G) b = circleMap (G := G) b :=
    funext (torusMulEquiv_apply_parameter b)
  rw [he]
  exact circleMap_continuous b

/-- A compact connected abelian Lie group is a finite-dimensional torus. -/
def torusEquiv (b : Basis ι ℝ E) : G ≃ₜ* (ι → Circle) :=
  { torusMulEquiv (G := G) b with
    continuous_toFun := torusMulEquiv_continuous b
    continuous_invFun := (torusMulEquiv_continuous (G := G) b).continuous_symm_of_equiv_compact_to_t2 }

end AbelianParameters

namespace CompactLieTorus
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [ConnectedSpace G] [CompactSpace G]

/-- The torus has exactly the dimension of the group's tangent space, including dimension zero. -/
theorem exists_torus_equiv (hc : ∀ g h : G, g*h = h*g) :
    Nonempty (G ≃ₜ* Torus (finrank ℝ E)) := by
  let : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact ⟨AbelianParameters.torusEquiv (G := G) (Module.finBasis ℝ E)⟩

include E in
/-- Manuscript compact abelian Lie-group classification. -/
theorem abelian_iff_torus :
    (∀ g h : G, g*h = h*g) ↔ ∃ d : ℕ, Nonempty (G ≃ₜ* Torus d) := by
  constructor
  · intro hc
    exact ⟨finrank ℝ E,exists_torus_equiv (E := E) hc⟩
  · rintro ⟨d,⟨e⟩⟩ g h
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
end CompactLieTorus

end MathieuProperty
