import MathieuProperty.LieLocalCoordinates
import MathieuProperty.InvariantLieDecomposition
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
/-! The center/simple-ideal decomposition for actual compact Lie groups.

The adjoint-invariant Haar form is differentiated using the proved local
identity `D Ad(x) v = [x,v]`. This supplies Lie invariance and discharges the
form hypothesis in the algebraic orthogonal decomposition. The semisimple
complement is a sum of finitely many independent simple ideals. The
manuscript-facing wrapper constructs all of these objects from the group;
it assumes no invariant form or structural decomposition.
-/
noncomputable section
open scoped Manifold ContDiff
namespace MathieuProperty
namespace CompactLieForm
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

def liftCentralIdeal (K : LieIdeal ℝ L) (hK : IsCompl (LieAlgebra.center ℝ L) K)
    (I : LieIdeal ℝ K) : LieIdeal ℝ L where
  __ := I.toSubmodule.map K.incl.toLinearMap
  lie_mem {x y} hy := by
    rcases hy with ⟨y', hy', rfl⟩
    have hx : x ∈ LieAlgebra.center ℝ L ⊔ K := by rw [hK.sup_eq_top]; trivial
    obtain ⟨z,hz,k,hk,rfl⟩ := (LieSubmodule.mem_sup _ _ _).mp hx
    refine ⟨⁅(⟨k,hk⟩ : K),y'⁆, I.lie_mem hy', ?_⟩
    change ⁅k,(y' : L)⁆ = ⁅z+k,(y' : L)⁆
    rw [add_lie]
    have hz' := (LieModule.mem_maxTrivSubmodule ℝ L L z).mp hz (y' : L)
    rw [← lie_skew z (y' : L), hz', neg_zero, zero_add]

def liftCentralIdealHom (K : LieIdeal ℝ L) (hK : IsCompl (LieAlgebra.center ℝ L) K)
    (I : LieIdeal ℝ K) : I →ₗ⁅ℝ⁆ liftCentralIdeal K hK I where
  toFun v := ⟨v.val.val, ⟨v.val,v.property,rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {x y} := rfl

def liftCentralIdealEquiv (K : LieIdeal ℝ L) (hK : IsCompl (LieAlgebra.center ℝ L) K)
    (I : LieIdeal ℝ K) : I ≃ₗ⁅ℝ⁆ liftCentralIdeal K hK I :=
  LieEquiv.ofBijective (liftCentralIdealHom K hK I) ⟨by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : liftCentralIdeal K hK I => (z : L)) h, by
    intro v
    rcases v.property with ⟨w,hw,hv⟩
    exact ⟨⟨w,hw⟩, Subtype.ext hv⟩⟩
end CompactLieForm

namespace CompactAdjoint
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
local instance : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
local instance : NormedAddCommGroup (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance : NormedSpace ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedSpace ℝ E)
local instance : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)

set_option backward.isDefEq.respectTransparency false in
theorem invariantForm_lieInvariant :
    (invariantForm (E := E) (G := G)).lieInvariant (GroupLieAlgebra 𝓘(ℝ,E) G) := by
  intro x v w
  let B := invariantForm (E := E) (G := G)
  let Bc : E →L[ℝ] E →L[ℝ] ℝ := by exact B.toContinuousBilinearMap
  let A := LieLocalChart.adjointCoordinates (E := E) (G := G)
  let a₀ := LieLocalChart.origin (E := E) (G := G)
  have hA := (LieLocalChart.adjointCoordinates_smooth (E := E) (G := G)).differentiableAt (by simp)
  have hv := hA.hasFDerivAt.clm_apply (hasFDerivAt_const (F := E) v a₀)
  have hw := hA.hasFDerivAt.clm_apply (hasFDerivAt_const (F := E) w a₀)
  have hd := (Bc.hasFDerivAt_of_bilinear hv hw).fderiv
  have he : (fun a : E => Bc (A a v) (A a w)) = (fun _ : E => B v w) := by
    funext a
    exact invariantForm_adjoint ((LieLocalChart.chart (E := E) (G := G)).symm a) v w
  change fderiv ℝ (fun a : E => Bc (A a v) (A a w)) a₀ = _ at hd
  erw [he, fderiv_const] at hd
  have hz := congrArg (fun f : E →L[ℝ] ℝ => f x) hd
  simp [a₀, Bc, LieLocalChart.adjointCoordinates_origin,
    LieLocalChart.adjointCoordinates_fderiv, ContinuousLinearMap.comp_apply] at hz
  dsimp only [B] at hz
  exact eq_neg_of_add_eq_zero_right hz.symm
def semisimpleIdeal : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  CompactLieForm.centerComplement (invariantForm (E := E) (G := G)) invariantForm_lieInvariant

theorem semisimpleIdeal_isSemisimple : LieAlgebra.IsSemisimple ℝ (semisimpleIdeal (E := E) (G := G)) :=
  CompactLieForm.center_complement_semisimple _ invariantForm_symmetric invariantForm_anisotropic
    invariantForm_lieInvariant

theorem semisimpleIdeal_isCompl :
    IsCompl (LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) (semisimpleIdeal (E := E) (G := G)) :=
  CompactLieForm.center_complement_isCompl _ invariantForm_symmetric invariantForm_anisotropic
    invariantForm_lieInvariant

def compactLieDecomposition :
    (LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) × semisimpleIdeal (E := E) (G := G)) ≃ₗ⁅ℝ⁆
      GroupLieAlgebra 𝓘(ℝ,E) G :=
  CompactLieForm.centerDecomposition _ invariantForm_symmetric invariantForm_anisotropic
    invariantForm_lieInvariant

theorem semisimpleIdeal_finite_simple_factors :
    Set.Finite {I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G)) | IsAtom I} ∧
    sSup {I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G)) | IsAtom I} = ⊤ ∧
    sSupIndep {I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G)) | IsAtom I} ∧
    ∀ I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G)), IsAtom I → LieAlgebra.IsSimple ℝ I := by
  let := semisimpleIdeal_isSemisimple (E := E) (G := G)
  exact ⟨WellFoundedGT.finite_of_sSupIndep LieAlgebra.IsSemisimple.sSupIndep_isAtom,
    LieAlgebra.IsSemisimple.sSup_atoms_eq_top, LieAlgebra.IsSemisimple.sSupIndep_isAtom,
    LieAlgebra.IsSemisimple.isSimple_of_isAtom⟩

theorem simple_factor_positive_form (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) :
    ∃ B : LinearMap.BilinForm ℝ I, B.IsSymm ∧ (∀ v : I, v ≠ 0 → 0 < B v v) ∧ B.lieInvariant I := by
  let K := semisimpleIdeal (E := E) (G := G)
  let B := invariantForm (E := E) (G := G)
  let BK := B.restrict K.toSubmodule
  refine ⟨BK.restrict I.toSubmodule,
    ((invariantForm_symmetric (E := E) (G := G)).restrict K.toSubmodule).restrict I.toSubmodule, ?_, ?_⟩
  · intro v hv
    apply invariantForm_positive (E := E) (G := G)
    intro h
    exact hv (Subtype.ext (Subtype.ext h))
  · intro x y z
    exact invariantForm_lieInvariant (E := E) (G := G) x.val.val y.val.val z.val.val

def simpleFactorAmbientEquiv (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) :
    I ≃ₗ⁅ℝ⁆ CompactLieForm.liftCentralIdeal (semisimpleIdeal (E := E) (G := G))
      semisimpleIdeal_isCompl I :=
  CompactLieForm.liftCentralIdealEquiv _ _ I

omit [IsTopologicalGroup G] in
/-- The manuscript's compact Lie algebra decomposition, with a finite independent
family of simple factors, their ambient ideal embeddings, and positive invariant
forms certifying compact type. The center complement and all certificates are
constructed from the actual compact Lie group. -/
theorem compact_lie_decomposition :
    ∃ (K : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G))
      (hK : IsCompl (LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)) K),
      Nonempty ((LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) × K) ≃ₗ⁅ℝ⁆ GroupLieAlgebra 𝓘(ℝ,E) G) ∧
      LieAlgebra.IsSemisimple ℝ K ∧
      Set.Finite {I : LieIdeal ℝ K | IsAtom I} ∧
      sSup {I : LieIdeal ℝ K | IsAtom I} = ⊤ ∧
      sSupIndep {I : LieIdeal ℝ K | IsAtom I} ∧
      ∀ I : LieIdeal ℝ K, IsAtom I → LieAlgebra.IsSimple ℝ I ∧
        Nonempty (I ≃ₗ⁅ℝ⁆ CompactLieForm.liftCentralIdeal K hK I) ∧
        ∃ B : LinearMap.BilinForm ℝ I, B.IsSymm ∧ (∀ v : I, v ≠ 0 → 0 < B v v) ∧ B.lieInvariant I := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  obtain ⟨hfin, hsup, hind, hsimple⟩ := semisimpleIdeal_finite_simple_factors (E := E) (G := G)
  refine ⟨semisimpleIdeal, semisimpleIdeal_isCompl, ⟨compactLieDecomposition⟩,
    semisimpleIdeal_isSemisimple, hfin, hsup, hind, ?_⟩
  intro I hI
  exact ⟨hsimple I hI, ⟨simpleFactorAmbientEquiv I⟩, simple_factor_positive_form I⟩
end CompactAdjoint
end MathieuProperty
