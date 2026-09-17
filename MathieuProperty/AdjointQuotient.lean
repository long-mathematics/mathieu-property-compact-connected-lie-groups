import MathieuProperty.AdjointAutomorphism
import MathieuProperty.OpenLieSubgroup
/-! The manuscript's adjoint simple quotient.
The actual restricted adjoint image is the automorphism identity component.
Its open-subgroup charts give a smooth Lie group with the original simple-factor
Lie algebra. Compactness and connectedness come from the source group, and
centerlessness is transported from the previously constructed matrix image. -/

noncomputable section
namespace MathieuProperty
namespace CompactAdjoint
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G] [CompactSpace G] [ConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
local instance quotientTangentNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  groupLieAlgebraNormed
local instance quotientTangentFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I)
local instance quotientFactorNormed : NormedRealLieAlgebra (idealModel (ambientSimpleFactor I)) :=
  inferInstanceAs (NormedRealLieAlgebra (ambientSimpleFactor I))

abbrev AdjointSimpleGroup := ↥(simpleAdjointOpenImage I hI)

/-- The restricted adjoint homomorphism onto its actual open image. -/
def adjointQuotientMap : G →* AdjointSimpleGroup I hI :=
  (toSimpleAutomorphisms I hI).rangeRestrict

theorem adjointQuotientMap_continuous : Continuous (adjointQuotientMap I hI) :=
  (toSimpleAutomorphisms_continuous I hI).subtype_mk _

theorem adjointQuotientMap_surjective : Function.Surjective (adjointQuotientMap I hI) :=
  (toSimpleAutomorphisms I hI).rangeRestrict_surjective

theorem adjointQuotientMap_smooth :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,simpleAutomorphismModel I) ∞ (adjointQuotientMap I hI) := by
  apply (ContMDiff.subtypeVal_comp_iff (simpleAdjointOpenImage I hI).toOpens _).mp
  exact toSimpleAutomorphisms_smooth I hI

instance adjointSimpleGroup_compact : CompactSpace (AdjointSimpleGroup I hI) :=
  isCompact_iff_compactSpace.mp (isCompact_range (toSimpleAutomorphisms_continuous I hI))

instance adjointSimpleGroup_connected : ConnectedSpace (AdjointSimpleGroup I hI) :=
  (adjointQuotientMap_surjective I hI).connectedSpace (adjointQuotientMap_continuous I hI)

/-- Forgetting the redundant automorphism proof identifies the two concrete image constructions. -/
def adjointImageHom : AdjointSimpleGroup I hI →* simpleAdjointImage I hI where
  toFun u := ⟨u.val.val, by
    obtain ⟨g,hg⟩ := u.property
    rw [← hg]
    exact (simpleAdjointOnto I hI g).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem adjointImageHom_bijective : Function.Bijective (adjointImageHom I hI) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : simpleAdjointImage I hI => w.val) h
  · intro u
    obtain ⟨g,rfl⟩ := simpleAdjointOnto_surjective I hI u
    exact ⟨adjointQuotientMap I hI g,rfl⟩

def adjointImageEquiv : AdjointSimpleGroup I hI ≃* simpleAdjointImage I hI :=
  MulEquiv.ofBijective (adjointImageHom I hI) (adjointImageHom_bijective I hI)

theorem adjointSimpleGroup_center_eq_bot : Subgroup.center (AdjointSimpleGroup I hI) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro u hu
  apply (adjointImageEquiv I hI).injective
  have hc : adjointImageEquiv I hI u ∈ Subgroup.center (simpleAdjointImage I hI) :=
    Subgroup.map_center_le_center (adjointImageEquiv I hI).surjective ⟨u,hu,rfl⟩
  simpa using simpleAdjointImage_central_eq_one I hI _ hc

local instance quotientImageSmoothness :
    LieGroup 𝓘(ℝ,simpleAutomorphismModel I) (minSmoothness ℝ 3) (AdjointSimpleGroup I hI) :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)

/-- The image Lie algebra is the original simple factor, with its actual bracket. -/
def adjointSimpleGroup_algebraEquiv :
    GroupLieAlgebra 𝓘(ℝ,simpleAutomorphismModel I) (AdjointSimpleGroup I hI) ≃ₗ⁅ℝ⁆
      idealModel (ambientSimpleFactor I) := by
  let : LieAlgebra.IsSimple ℝ (idealModel (ambientSimpleFactor I)) := simpleFactorModel_isSimple I hI
  exact (OpenLieSubgroup.lieEquiv (E := simpleAutomorphismModel I)
    (simpleAdjointOpenImage I hI)).trans LieAutomorphism.algebraEquiv

instance adjointSimpleGroup_isSimple :
    LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,simpleAutomorphismModel I) (AdjointSimpleGroup I hI)) := by
  let : LieAlgebra.IsSimple ℝ (idealModel (ambientSimpleFactor I)) := simpleFactorModel_isSimple I hI
  exact CompactLieForm.isSimple_of_equiv (adjointSimpleGroup_algebraEquiv I hI).symm


/-- Manuscript proposition: a nonabelian compact connected Lie group has a
continuous surjection onto a compact connected centerless Lie group with simple
Lie algebra. The target is the actual automorphism identity component of a
simple ideal, by `toSimpleAutomorphisms_range_eq_component`. -/
theorem adjoint_simple_quotient (hn : ¬ ∀ g h : G, g*h = h*g) :
    ∃ (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I),
      CompactSpace (AdjointSimpleGroup I hI) ∧
      ConnectedSpace (AdjointSimpleGroup I hI) ∧
      LieGroup 𝓘(ℝ,simpleAutomorphismModel I) ∞ (AdjointSimpleGroup I hI) ∧
      Subgroup.center (AdjointSimpleGroup I hI) = ⊥ ∧
      LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,simpleAutomorphismModel I) (AdjointSimpleGroup I hI)) ∧
      ∃ π : G →* AdjointSimpleGroup I hI, Continuous π ∧ Function.Surjective π := by
  obtain ⟨I,hI,_⟩ := exists_simple_factor (E := E) hn
  exact ⟨I,hI,inferInstance,inferInstance,inferInstance,
    adjointSimpleGroup_center_eq_bot I hI,inferInstance,
    adjointQuotientMap I hI,adjointQuotientMap_continuous I hI,adjointQuotientMap_surjective I hI⟩

end CompactAdjoint
end MathieuProperty
