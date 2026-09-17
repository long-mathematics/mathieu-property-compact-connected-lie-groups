import MathieuProperty.RepresentationImage
import MathieuProperty.CompactAdjoint
import MathieuProperty.LieAutomorphism
import MathieuProperty.LieSurjective
/-! The full adjoint representation as a smooth homomorphism into the
actual automorphism Lie group. Innerness of derivations makes its differential
surjective; consequently its image is open and equals the identity component. -/

noncomputable section
namespace MathieuProperty
namespace FullAdjoint
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G]
local instance autTangentNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  groupLieAlgebraNormed
local instance autTangentFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
abbrev Target := LieAutomorphism.Group (GroupLieAlgebra 𝓘(ℝ,E) G)

abbrev Model := BilinearAutomorphism.derivations
  (LieAutomorphism.bracket (V := GroupLieAlgebra 𝓘(ℝ,E) G))

def toAutomorphisms : G →* Target (E := E) (G := G) where
  toFun g := ⟨RepresentationImage.unitHom (CompactAdjoint.adjointRepresentation (E := E)) g, by
    intro x y
    exact CompactAdjoint.adjointLinear_lie g x y⟩
  map_one' := Subtype.ext (map_one (RepresentationImage.unitHom CompactAdjoint.adjointRepresentation))
  map_mul' g h := Subtype.ext (map_mul (RepresentationImage.unitHom CompactAdjoint.adjointRepresentation) g h)

theorem toAutomorphisms_continuous : Continuous (toAutomorphisms (E := E) (G := G)) := by
  apply Continuous.subtype_mk
  apply RepresentationImage.unitHom_continuous
  exact (CompactAdjoint.adjointLinear_contMDiff (E := E) (G := G)).continuous

omit [IsTopologicalGroup G] in
theorem toAutomorphisms_val (g : G) :
    (toAutomorphisms (E := E) g).val.val = CompactAdjoint.adjointLinear (E := E) g := rfl

theorem toAutomorphisms_smooth :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,BilinearAutomorphism.derivations
      (LieAutomorphism.bracket (V := GroupLieAlgebra 𝓘(ℝ,E) G))) ∞
      (toAutomorphisms (E := E) (G := G)) := by
  intro g
  apply BilinearAutomorphism.contMDiffAt_of_val _ (toAutomorphisms_continuous (E := E) (G := G)).continuousAt
  simpa only [toAutomorphisms_val] using! (CompactAdjoint.adjointLinear_contMDiff (E := E) (G := G)) g


variable [LieAlgebra.IsKilling ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

omit [IsTopologicalGroup G] in
theorem adjoint_derivative_hits_derivation
    (D : BilinearAutomorphism.derivations (LieAutomorphism.bracket
      (V := GroupLieAlgebra 𝓘(ℝ,E) G))) :
    ∃ x : E, (show GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G)
        (CompactAdjoint.adjointLinear (E := E) (G := G)) 1 x) = D.val := by
  obtain ⟨z,hz⟩ := LieDerivation.IsKilling.exists_eq_ad (LieAutomorphism.tangentDerivation
    (V := GroupLieAlgebra 𝓘(ℝ,E) G) D)
  refine ⟨z, ?_⟩
  change (show GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G from
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) (ConnectedLie.adjoint (E := E)) 1 z) = D.val
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun T : LieDerivation ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)
    (GroupLieAlgebra 𝓘(ℝ,E) G) => T v) hz
  have had := ConnectedLie.adjoint_mfderiv (E := E) (G := G) z v
  change -⁅v,z⁆ = D.val v at h
  exact had.trans ((lie_skew z v).symm.trans h)



omit [LieAlgebra.IsKilling ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)] in
theorem toAutomorphisms_mfderiv_val (x : E) :
    (show Model (E := E) (G := G) from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Model (E := E) (G := G))
      (toAutomorphisms (E := E) (G := G)) 1 x).val =
    (show GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G)
        (CompactAdjoint.adjointLinear (E := E) (G := G)) 1 x) := by
  let valF : Target (E := E) (G := G) →
      GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G := fun u => u.val.val
  have he : valF ∘ toAutomorphisms (E := E) (G := G) = CompactAdjoint.adjointLinear (E := E) (G := G) :=
    funext (toAutomorphisms_val)
  have hv : ContMDiff 𝓘(ℝ,Model (E := E) (G := G))
      𝓘(ℝ,GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) ∞ valF :=
    (BilinearAutomorphism.val_contMDiff _).of_le le_top
  have hd := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,Model (E := E) (G := G)))
    (I'' := 𝓘(ℝ,GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G))
    (f := toAutomorphisms (E := E) (G := G)) (g := valF) (1 : G)
    (hv.mdifferentiableAt (by simp)) ((toAutomorphisms_smooth (E := E) (G := G)).mdifferentiableAt (by simp))
  have hvd : (show Model (E := E) (G := G) →L[ℝ]
      GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G from
      mfderiv 𝓘(ℝ,Model (E := E) (G := G))
        𝓘(ℝ,GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) valF
          (toAutomorphisms (E := E) (G := G) 1)) =
      (Model (E := E) (G := G)).subtypeL := by
    rw [map_one]
    exact BilinearAutomorphism.val_mfderiv_one
      (LieAutomorphism.bracket (V := GroupLieAlgebra 𝓘(ℝ,E) G))
  have hxv := congrArg (fun q : Model (E := E) (G := G) →L[ℝ]
    GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G =>
      q (show Model (E := E) (G := G) from
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Model (E := E) (G := G)) (toAutomorphisms (E := E) (G := G)) 1 x)) hvd
  have hxd := congrArg (fun q : E →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ]
    GroupLieAlgebra 𝓘(ℝ,E) G => q x) hd
  have heD := congrArg (fun f : G → GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G =>
    (show E →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) f 1)) he
  exact hxv.symm.trans (hxd.symm.trans (congrArg (fun q => q x) heD))

theorem toAutomorphisms_mfderiv_surjective :
    Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Model (E := E) (G := G)) (toAutomorphisms (E := E) (G := G)) 1) := by
  intro D
  obtain ⟨x,hx⟩ := adjoint_derivative_hits_derivation D
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact (toAutomorphisms_mfderiv_val (E := E) (G := G) x).trans hx

/-- The actual adjoint representation has open image in the automorphism Lie group. -/
theorem toAutomorphisms_range_open :
    IsOpen ((toAutomorphisms (E := E) (G := G)).range : Set (Target (E := E) (G := G))) := by
  have hn : ((toAutomorphisms (E := E) (G := G)).range : Set (Target (E := E) (G := G))) ∈
      𝓝 (1 : Target (E := E) (G := G)) := by
    simpa using LieSurjective.range_mem_nhds_of_surjective_mfderiv
      ((toAutomorphisms_smooth (E := E) (G := G) 1).of_le (by simp))
      (toAutomorphisms_mfderiv_surjective (E := E) (G := G))
  exact (toAutomorphisms (E := E) (G := G)).range.isOpen_of_mem_nhds hn

variable [ConnectedSpace G]

/-- The image is exactly the identity component of the automorphism group. -/
theorem toAutomorphisms_range_eq_component :
    ((toAutomorphisms (E := E) (G := G)).range : Set (Target (E := E) (G := G))) =
      connectedComponent (1 : Target (E := E) (G := G)) := by
  apply Set.Subset.antisymm
  · exact (isConnected_range (toAutomorphisms_continuous (E := E) (G := G))).subset_connectedComponent
      ⟨1, map_one (toAutomorphisms (E := E) (G := G))⟩
  · exact (show IsClopen ((toAutomorphisms (E := E) (G := G)).range : Set (Target (E := E) (G := G))) from
      ⟨(toAutomorphisms (E := E) (G := G)).range.isClosed_of_isOpen
        (toAutomorphisms_range_open (E := E) (G := G)), toAutomorphisms_range_open (E := E) (G := G)⟩).connectedComponent_subset (toAutomorphisms (E := E) (G := G)).range.one_mem

/-- The actual image, bundled as an open subgroup. -/
def openImage : OpenSubgroup (Target (E := E) (G := G)) :=
  ⟨(toAutomorphisms (E := E) (G := G)).range, toAutomorphisms_range_open (E := E) (G := G)⟩


theorem component_compact [CompactSpace G] :
    IsCompact (connectedComponent (1 : Target (E := E) (G := G))) := by
  rw [← toAutomorphisms_range_eq_component]
  exact isCompact_range (toAutomorphisms_continuous (E := E) (G := G))

end FullAdjoint
end MathieuProperty
