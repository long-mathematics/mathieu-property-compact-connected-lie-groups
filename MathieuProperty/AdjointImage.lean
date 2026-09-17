import MathieuProperty.RepresentationImage
import MathieuProperty.AdjointCentralizer
import MathieuProperty.NonabelianCompactLie
import MathieuProperty.RestrictedAdjoint
import Mathlib.GroupTheory.Subgroup.Center
/-! The concrete compact connected image of a simple-factor adjoint action.

This constructs a continuous surjection onto a nontrivial compact connected
centerless topological group of Lie automorphisms. Centerlessness follows by
differentiating commutation and using the simple factor's zero Lie center.
No manifold structure on this image, or simple Lie-group conclusion, is asserted
here; those are separate remaining parts of the quotient construction. -/

noncomputable section
namespace MathieuProperty
namespace CompactAdjoint
open scoped Manifold ContDiff
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G] [CompactSpace G] [ConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
local instance imageSmoothness : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
local instance imageTangentNorm : NormedAddCommGroup (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance imageTangentNormedSpace : NormedSpace ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedSpace ℝ E)
local instance imageTangentFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I)
abbrev ambientSimpleFactor := CompactLieForm.liftCentralIdeal (semisimpleIdeal (E := E) (G := G))
  semisimpleIdeal_isCompl I

def simpleModelRepresentation : Representation ℝ G (idealModel (ambientSimpleFactor I)) :=
  simpleAdjointRepresentation I hI

set_option backward.isDefEq.respectTransparency false in
theorem simpleModelRepresentation_clm (g : G) :
    LinearMap.toContinuousLinearMap (simpleModelRepresentation I hI g) =
      restrictedAdjoint (ambientSimpleFactor I) g := by
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun (restrictedAdjoint_eq_simple I hI g).symm v

theorem simpleModelRepresentation_continuous :
    Continuous (fun g => LinearMap.toContinuousLinearMap (simpleModelRepresentation I hI g)) := by
  simp_rw [simpleModelRepresentation_clm]
  exact (restrictedAdjoint_smooth _).continuous

def simpleAdjointImage := RepresentationImage.image (simpleModelRepresentation I hI)
def simpleAdjointOnto : G →* simpleAdjointImage I hI :=
  RepresentationImage.ontoImage (simpleModelRepresentation I hI)

theorem simpleAdjointImage_compact : CompactSpace (simpleAdjointImage I hI) :=
  RepresentationImage.image_compact _ (simpleModelRepresentation_continuous I hI)

theorem simpleAdjointImage_connected : ConnectedSpace (simpleAdjointImage I hI) :=
  RepresentationImage.image_connected _ (simpleModelRepresentation_continuous I hI)

theorem simpleAdjointOnto_continuous : Continuous (simpleAdjointOnto I hI) :=
  RepresentationImage.ontoImage_continuous _ (simpleModelRepresentation_continuous I hI)

theorem simpleAdjointOnto_surjective : Function.Surjective (simpleAdjointOnto I hI) :=
  RepresentationImage.ontoImage_surjective _
local instance imageIdealLieRing : LieRing (idealModel (ambientSimpleFactor I)) :=
  inferInstanceAs (LieRing (ambientSimpleFactor I))
local instance imageIdealLieAlgebra : LieAlgebra ℝ (idealModel (ambientSimpleFactor I)) :=
  inferInstanceAs (LieAlgebra ℝ (ambientSimpleFactor I))

include hI in
omit [ConnectedSpace G] in
theorem simpleFactorModel_isSimple : LieAlgebra.IsSimple ℝ (idealModel (ambientSimpleFactor I)) := by
  have hS : LieAlgebra.IsSimple ℝ I :=
    (semisimpleIdeal_finite_simple_factors (E := E) (G := G)).2.2.2 I hI
  exact CompactLieForm.isSimple_of_equiv (simpleFactorAmbientEquiv I)

set_option backward.isDefEq.respectTransparency false in
theorem simpleAdjointImage_map_lie (u : simpleAdjointImage I hI)
    (v w : idealModel (ambientSimpleFactor I)) :
    u.val.val ⁅v,w⁆ = ⁅u.val.val v,u.val.val w⁆ := by
  obtain ⟨u,⟨g,rfl⟩⟩ := u
  apply Subtype.ext
  exact adjointLinear_lie g v.val w.val

def simpleImageLieEquiv (u : simpleAdjointImage I hI) :
    idealModel (ambientSimpleFactor I) ≃ₗ⁅ℝ⁆ idealModel (ambientSimpleFactor I) where
  __ := (ContinuousLinearEquiv.ofUnit u.val).toLinearEquiv
  map_lie' := simpleAdjointImage_map_lie I hI u _ _

theorem simpleAdjointOnto_val (g : G) :
    (simpleAdjointOnto I hI g).val.val = restrictedAdjoint (ambientSimpleFactor I) g :=
  simpleModelRepresentation_clm I hI g
set_option backward.isDefEq.respectTransparency false in
theorem simpleAdjointImage_central_eq_one (u : simpleAdjointImage I hI)
    (hu : u ∈ Subgroup.center (simpleAdjointImage I hI)) : u = 1 := by
  let J := ambientSimpleFactor I
  let V := idealModel J
  let U : V →L[ℝ] V := u.val.val
  have hcomm (g : G) : U.comp (restrictedAdjoint J g) = (restrictedAdjoint J g).comp U := by
    have hg := Subgroup.mem_center_iff.mp hu (simpleAdjointOnto I hI g)
    have hv := congrArg (fun h : simpleAdjointImage I hI => h.val.val) hg
    change (simpleAdjointOnto I hI g).val.val * U = U * (simpleAdjointOnto I hI g).val.val at hv
    rw [simpleAdjointOnto_val] at hv
    exact hv.symm
  have : LieAlgebra.IsSimple ℝ V := simpleFactorModel_isSimple I hI
  have hz : LieAlgebra.center ℝ V = ⊥ := LieAlgebra.center_eq_bot ℝ V
  have hc : ∀ x y : V, simpleImageLieEquiv I hI u ⁅x,y⁆ = ⁅x,simpleImageLieEquiv I hI u y⁆ := by
    intro x y
    have hd := restrictedAdjoint_mfderiv J (show GroupLieAlgebra 𝓘(ℝ,E) G from x.val)
    have h := AdjointCentralizer.commutes_mfderiv (restrictedAdjoint J) U (1 : G)
      ((restrictedAdjoint_smooth J).mdifferentiableAt (by simp)) hcomm x.val y
    have hy := congrArg (fun q : V →L[ℝ] V => q y) hd
    have hUy := congrArg (fun q : V →L[ℝ] V => q (U y)) hd
    change U ((restrictedBracket J x.val) y) = (restrictedBracket J x.val) (U y)
    exact ((congrArg U hy).symm.trans h).trans hUy
  have he := AdjointCentralizer.equiv_eq_refl (simpleImageLieEquiv I hI u) hz hc
  apply Subtype.ext
  apply Units.ext
  apply ContinuousLinearMap.ext
  intro v
  exact DFunLike.congr_fun he v

theorem simpleAdjointImage_center_eq_bot : Subgroup.center (simpleAdjointImage I hI) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  exact simpleAdjointImage_central_eq_one I hI
set_option backward.isDefEq.respectTransparency false in
theorem simpleAdjointImage_nontrivial : Nontrivial (simpleAdjointImage I hI) := by
  classical
  by_contra hn
  have : Subsingleton (simpleAdjointImage I hI) := not_nontrivial_iff_subsingleton.mp hn
  let J := ambientSimpleFactor I
  let V := idealModel J
  have hA : restrictedAdjoint J = (fun _ : G => (1 : V →L[ℝ] V)) := by
    funext g
    have h := congrArg (fun u : simpleAdjointImage I hI => u.val.val)
      (Subsingleton.elim (simpleAdjointOnto I hI g) 1)
    rw [simpleAdjointOnto_val] at h
    exact h
  have hb (x : GroupLieAlgebra 𝓘(ℝ,E) G) : restrictedBracket J x = 0 := by
    apply Eq.trans (restrictedAdjoint_mfderiv J x).symm
    have hd0 := congrArg (fun f : G → V →L[ℝ] V =>
      (show E →L[ℝ] (V →L[ℝ] V) from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V →L[ℝ] V) f 1)) hA
    erw [mfderiv_const] at hd0
    exact congrArg (fun q : E →L[ℝ] (V →L[ℝ] V) => q x) hd0
  have hS : LieAlgebra.IsSimple ℝ V := simpleFactorModel_isSimple I hI
  apply LieAlgebra.IsSimple.non_abelian (R := ℝ) (L := V)
  constructor
  intro x y
  change (restrictedBracket J x.val) y = 0
  rw [hb]
  rfl
end CompactAdjoint
end MathieuProperty
