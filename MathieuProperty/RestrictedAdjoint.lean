import MathieuProperty.ProjectedAdjoint
import MathieuProperty.AdjointIdeals
import MathieuProperty.CompactLieStructure
import MathieuProperty.RestrictedAdjointAlgebra
/-! The actual differential of the restricted adjoint representation.

The compact invariant form supplies a projection onto every ideal. Projected
Ad is smooth and differentiates to the restricted bracket. For the simple
factors, G03 identifies projected Ad with the actual restricted representation.
The differential image is exactly the ideal's own adjoint image. -/

noncomputable section
open scoped Manifold ContDiff
namespace MathieuProperty
namespace CompactAdjoint
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
local instance projectionSmoothness : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
local instance projectionTangentNorm : NormedAddCommGroup (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance projectionTangentNormedSpace : NormedSpace ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedSpace ℝ E)
local instance projectionTangentFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
def idealModel (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) : Submodule ℝ E := J.toSubmodule

def idealComplement (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) :
    LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  LieAlgebra.InvariantForm.orthogonal invariantForm invariantForm_lieInvariant J

theorem idealModel_isCompl (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) :
    IsCompl (idealModel J) (idealModel (idealComplement J)) := by
  exact (LieSubmodule.isCompl_toSubmodule).mpr
    (CompactLieForm.ideal_orthogonal_isCompl _ invariantForm_symmetric invariantForm_anisotropic
      invariantForm_lieInvariant J)

def idealProjection (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) : E →L[ℝ] idealModel J :=
  LinearMap.toContinuousLinearMap ((idealModel J).projectionOnto
    (idealModel (idealComplement J)) (idealModel_isCompl J))

theorem idealProjection_apply (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) (v : idealModel J) :
    idealProjection J v.val = v := by
  exact Submodule.projectionOnto_apply_left (idealModel_isCompl J) v
def restrictedAdjoint (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) (g : G) :
    idealModel J →L[ℝ] idealModel J :=
  RestrictedAdjoint.projectedAdjoint (idealModel J) (idealProjection J) g

def restrictedBracket (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G))
    (x : GroupLieAlgebra 𝓘(ℝ,E) G) : idealModel J →L[ℝ] idealModel J :=
  LinearMap.toContinuousLinearMap
    (show idealModel J →ₗ[ℝ] idealModel J from LieModule.toEnd ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) J x)

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem restrictedBracket_self (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) (z : J) :
    (restrictedBracket J z.val).toLinearMap = (LieAlgebra.ad ℝ J z) := by
  rfl

theorem restrictedAdjoint_smooth (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,idealModel J →L[ℝ] idealModel J) ∞ (restrictedAdjoint J) :=
  RestrictedAdjoint.projectedAdjoint_smooth _ _

set_option backward.isDefEq.respectTransparency false in
theorem restrictedAdjoint_mfderiv (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G))
    (x : GroupLieAlgebra 𝓘(ℝ,E) G) :
    (show idealModel J →L[ℝ] idealModel J from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,idealModel J →L[ℝ] idealModel J) (restrictedAdjoint J) 1 x) =
    restrictedBracket J x := by
  apply ContinuousLinearMap.ext
  intro v
  change (show idealModel J →L[ℝ] idealModel J from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,idealModel J →L[ℝ] idealModel J)
        (RestrictedAdjoint.projectedAdjoint (G := G) (idealModel J) (idealProjection J)) 1 x) v = _
  rw [RestrictedAdjoint.projectedAdjoint_mfderiv]
  exact idealProjection_apply J (restrictedBracket J x v)

set_option backward.isDefEq.respectTransparency false in
theorem restricted_adjoint_differential_range (J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) :
    Set.range (fun x : GroupLieAlgebra 𝓘(ℝ,E) G =>
      (show idealModel J →L[ℝ] idealModel J from
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,idealModel J →L[ℝ] idealModel J) (restrictedAdjoint J) 1 x)) =
    Set.range (fun z : J => restrictedBracket J z.val) := by
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨z,hz⟩ := CompactLieForm.exists_restricted_adjoint _ invariantForm_symmetric
      invariantForm_anisotropic invariantForm_lieInvariant J x
    refine ⟨z,?_⟩
    apply Eq.trans _ (restrictedAdjoint_mfderiv J x).symm
    ext v
    exact (hz v).symm
  · rintro ⟨z,rfl⟩
    exact ⟨z.val,restrictedAdjoint_mfderiv J z.val⟩
set_option backward.isDefEq.respectTransparency false in
theorem restrictedAdjoint_eq_simple [PreconnectedSpace G]
    (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I) (g : G) :
    (restrictedAdjoint (CompactLieForm.liftCentralIdeal (semisimpleIdeal (E := E) (G := G))
      semisimpleIdeal_isCompl I) g).toLinearMap = simpleAdjointRepresentation I hI g := by
  let J := CompactLieForm.liftCentralIdeal (semisimpleIdeal (E := E) (G := G))
    semisimpleIdeal_isCompl I
  apply LinearMap.ext
  intro v
  have hv := adjoint_preserves_simple_ideal I hI g v.property
  change idealProjection J (adjointLinear g v.val) = _
  exact idealProjection_apply J ⟨adjointLinear g v.val,hv⟩
end CompactAdjoint
end MathieuProperty
