import MathieuProperty.AdjointImage
import MathieuProperty.LieAutomorphism
import MathieuProperty.LieSurjective
/-! The restricted adjoint representation as a smooth homomorphism into the
actual automorphism Lie group. Innerness of derivations makes its differential
surjective; consequently its image is open and equals the identity component. -/

noncomputable section
namespace MathieuProperty
namespace CompactAdjoint
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G] [CompactSpace G] [ConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
local instance autTangentNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  groupLieAlgebraNormed
local instance autTangentFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I)
local instance autFactorNormed : NormedRealLieAlgebra (idealModel (ambientSimpleFactor I)) :=
  inferInstanceAs (NormedRealLieAlgebra (ambientSimpleFactor I))

abbrev simpleAutomorphismTarget := LieAutomorphism.Group (idealModel (ambientSimpleFactor I))

abbrev simpleAutomorphismModel := BilinearAutomorphism.derivations
  (LieAutomorphism.bracket (V := idealModel (ambientSimpleFactor I)))

def toSimpleAutomorphisms : G →* simpleAutomorphismTarget I where
  toFun g := ⟨(simpleAdjointOnto I hI g).val, by
    intro x y
    exact simpleAdjointImage_map_lie I hI (simpleAdjointOnto I hI g) x y⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun u : simpleAdjointImage I hI => u.val) (map_one (simpleAdjointOnto I hI))
  map_mul' g h := by
    apply Subtype.ext
    exact congrArg (fun u : simpleAdjointImage I hI => u.val) (map_mul (simpleAdjointOnto I hI) g h)

theorem toSimpleAutomorphisms_continuous : Continuous (toSimpleAutomorphisms I hI) := by
  exact ((simpleAdjointOnto_continuous I hI).subtype_val).subtype_mk _

theorem toSimpleAutomorphisms_val (g : G) :
    (toSimpleAutomorphisms I hI g).val.val = restrictedAdjoint (ambientSimpleFactor I) g :=
  simpleAdjointOnto_val I hI g

theorem toSimpleAutomorphisms_smooth :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,BilinearAutomorphism.derivations
      (LieAutomorphism.bracket (V := idealModel (ambientSimpleFactor I)))) ∞
      (toSimpleAutomorphisms I hI) := by
  intro g
  apply BilinearAutomorphism.contMDiffAt_of_val _ (toSimpleAutomorphisms_continuous I hI).continuousAt
  simpa only [toSimpleAutomorphisms_val] using! (restrictedAdjoint_smooth (ambientSimpleFactor I)) g


include hI in
omit [ConnectedSpace G] in
theorem restrictedAdjoint_derivative_hits_derivation
    (D : BilinearAutomorphism.derivations (LieAutomorphism.bracket
      (V := idealModel (ambientSimpleFactor I)))) :
    ∃ x : E, (show idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I) from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I))
        (restrictedAdjoint (ambientSimpleFactor I)) 1 x) = D.val := by
  let : LieAlgebra.IsSimple ℝ (idealModel (ambientSimpleFactor I)) := simpleFactorModel_isSimple I hI
  obtain ⟨z,hz⟩ := LieDerivation.IsKilling.exists_eq_ad (LieAutomorphism.tangentDerivation
    (V := idealModel (ambientSimpleFactor I)) D)
  refine ⟨z.val, ?_⟩
  rw [restrictedAdjoint_mfderiv]
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun T : LieDerivation ℝ (idealModel (ambientSimpleFactor I))
    (idealModel (ambientSimpleFactor I)) => T v) hz
  convert! h using 1
  change ⁅z,v⁆ = -⁅v,z⁆
  exact (lie_skew z v).symm



theorem toSimpleAutomorphisms_mfderiv_val (x : E) :
    (show simpleAutomorphismModel I from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,simpleAutomorphismModel I)
      (toSimpleAutomorphisms I hI) 1 x).val =
    (show idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I) from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I))
        (restrictedAdjoint (ambientSimpleFactor I)) 1 x) := by
  let valF : simpleAutomorphismTarget I →
      idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I) := fun u => u.val.val
  have he : valF ∘ toSimpleAutomorphisms I hI = restrictedAdjoint (ambientSimpleFactor I) :=
    funext (toSimpleAutomorphisms_val I hI)
  have hv : ContMDiff 𝓘(ℝ,simpleAutomorphismModel I)
      𝓘(ℝ,idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I)) ∞ valF :=
    (BilinearAutomorphism.val_contMDiff _).of_le le_top
  have hd := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,simpleAutomorphismModel I))
    (I'' := 𝓘(ℝ,idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I)))
    (f := toSimpleAutomorphisms I hI) (g := valF) (1 : G)
    (hv.mdifferentiableAt (by simp)) ((toSimpleAutomorphisms_smooth I hI).mdifferentiableAt (by simp))
  have hvd : (show simpleAutomorphismModel I →L[ℝ]
      idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I) from
      mfderiv 𝓘(ℝ,simpleAutomorphismModel I)
        𝓘(ℝ,idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I)) valF
          (toSimpleAutomorphisms I hI 1)) =
      (simpleAutomorphismModel I).subtypeL := by
    rw [map_one]
    exact BilinearAutomorphism.val_mfderiv_one
      (LieAutomorphism.bracket (V := idealModel (ambientSimpleFactor I)))
  have hxv := congrArg (fun q : simpleAutomorphismModel I →L[ℝ]
    idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I) =>
      q (show simpleAutomorphismModel I from
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,simpleAutomorphismModel I) (toSimpleAutomorphisms I hI) 1 x)) hvd
  have hxd := congrArg (fun q : E →L[ℝ] idealModel (ambientSimpleFactor I) →L[ℝ]
    idealModel (ambientSimpleFactor I) => q x) hd
  have heD := congrArg (fun f : G → idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I) =>
    (show E →L[ℝ] idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I) from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,idealModel (ambientSimpleFactor I) →L[ℝ] idealModel (ambientSimpleFactor I)) f 1)) he
  exact hxv.symm.trans (hxd.symm.trans (congrArg (fun q => q x) heD))

theorem toSimpleAutomorphisms_mfderiv_surjective :
    Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,simpleAutomorphismModel I) (toSimpleAutomorphisms I hI) 1) := by
  intro D
  obtain ⟨x,hx⟩ := restrictedAdjoint_derivative_hits_derivation I hI D
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact (toSimpleAutomorphisms_mfderiv_val I hI x).trans hx

/-- The actual adjoint representation has open image in the automorphism Lie group. -/
theorem toSimpleAutomorphisms_range_open :
    IsOpen ((toSimpleAutomorphisms I hI).range : Set (simpleAutomorphismTarget I)) := by
  have hn : ((toSimpleAutomorphisms I hI).range : Set (simpleAutomorphismTarget I)) ∈
      𝓝 (1 : simpleAutomorphismTarget I) := by
    simpa using LieSurjective.range_mem_nhds_of_surjective_mfderiv
      ((toSimpleAutomorphisms_smooth I hI 1).of_le (by simp))
      (toSimpleAutomorphisms_mfderiv_surjective I hI)
  exact (toSimpleAutomorphisms I hI).range.isOpen_of_mem_nhds hn

/-- The image is exactly the identity component of the automorphism group. -/
theorem toSimpleAutomorphisms_range_eq_component :
    ((toSimpleAutomorphisms I hI).range : Set (simpleAutomorphismTarget I)) =
      connectedComponent (1 : simpleAutomorphismTarget I) := by
  apply Set.Subset.antisymm
  · exact (isConnected_range (toSimpleAutomorphisms_continuous I hI)).subset_connectedComponent
      ⟨1, map_one (toSimpleAutomorphisms I hI)⟩
  · exact (show IsClopen ((toSimpleAutomorphisms I hI).range : Set (simpleAutomorphismTarget I)) from
      ⟨(toSimpleAutomorphisms I hI).range.isClosed_of_isOpen
        (toSimpleAutomorphisms_range_open I hI), toSimpleAutomorphisms_range_open I hI⟩).connectedComponent_subset (toSimpleAutomorphisms I hI).range.one_mem

/-- The actual image, bundled as an open subgroup. -/
def simpleAdjointOpenImage : OpenSubgroup (simpleAutomorphismTarget I) :=
  ⟨(toSimpleAutomorphisms I hI).range, toSimpleAutomorphisms_range_open I hI⟩

end CompactAdjoint
end MathieuProperty
