import MathieuProperty.Haar
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.MeasureTheory.Group.Integral

/-! Haar unitarization of finite-dimensional complex representations.

The averaged form is positive definite because Haar measure is positive on
nonempty open sets. Right invariance makes the form invariant. A separate
carrier holds its induced norm, and finite dimensionality supplies a continuous
linear equivalence with the original topology. Arbitrary normed complex spaces
are first transported to Euclidean coordinates; no compatible inner product on
the original norm is assumed. Inner products follow Lean's convention: linear
in the second argument.
-/

noncomputable section
open MeasureTheory
namespace MathieuProperty
variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (ρ : Representation ℂ G V) (hρ : ∀ v, Continuous (fun g => ρ g v))

def averagedInner (v w : V) : ℂ := ∫ g, inner ℂ (ρ g v) (ρ g w) ∂normalizedHaar G

include hρ in
theorem averagedInner_integrable (v w : V) :
    Integrable (fun g => inner ℂ (ρ g v) (ρ g w)) (normalizedHaar G) :=
  ((hρ v).inner (hρ w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include hρ in
theorem averagedInner_re_pos {v : V} (hv : v ≠ 0) : 0 < (averagedInner ρ v v).re := by
  change 0 < RCLike.re (averagedInner ρ v v)
  rw [averagedInner, ← integral_re (averagedInner_integrable ρ hρ v v)]
  apply integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp ((hρ v).inner (𝕜 := ℂ) (hρ v)))
    (averagedInner_integrable ρ hρ v v).re
    (fun g => by simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow])
    (x := (1 : G))
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)

include hρ in
@[instance_reducible]
def averagedInnerCore : InnerProductSpace.Core ℂ V where
  inner := averagedInner ρ
  conj_inner_symm v w := by
    rw [averagedInner, ← integral_conj]
    simp only [inner_conj_symm, averagedInner]
  re_inner_nonneg v := by
    by_cases hv : v = 0
    · simp [hv, averagedInner]
    · exact (averagedInner_re_pos ρ hρ hv).le
  add_left v w z := by
    simp only [averagedInner, map_add, inner_add_left]
    exact integral_add (averagedInner_integrable ρ hρ v z) (averagedInner_integrable ρ hρ w z)
  smul_left v w c := by
    simp only [averagedInner, map_smul, inner_smul_left]
    exact integral_const_mul _ _
  definite v hv := by
    by_contra h
    have hp := averagedInner_re_pos ρ hρ h
    change averagedInner ρ v v = 0 at hv
    rw [hv] at hp
    exact (lt_irrefl 0) hp

theorem averagedInner_invariant (k : G) (v w : V) :
    averagedInner ρ (ρ k v) (ρ k w) = averagedInner ρ v w := by
  simpa only [averagedInner, map_mul, Module.End.mul_apply] using
    integral_mul_right_eq_self (μ := normalizedHaar G)
      (fun g => inner ℂ (ρ g v) (ρ g w)) k

/-- A separate carrier prevents the averaged norm from conflicting with the original norm. -/
def AveragedSpace (_ρ : Representation ℂ G V) (_hρ : ∀ v, Continuous (fun g => _ρ g v)) := V

instance : AddCommGroup (AveragedSpace ρ hρ) := inferInstanceAs (AddCommGroup V)
instance : Module ℂ (AveragedSpace ρ hρ) := inferInstanceAs (Module ℂ V)

instance : NormedAddCommGroup (AveragedSpace ρ hρ) :=
  letI : InnerProductSpace.Core ℂ (AveragedSpace ρ hρ) := averagedInnerCore (V := V) ρ hρ
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (AveragedSpace ρ hρ) :=
  letI : InnerProductSpace.Core ℂ (AveragedSpace ρ hρ) := averagedInnerCore (V := V) ρ hρ
  InnerProductSpace.ofCore (averagedInnerCore (V := V) ρ hρ).toCore

instance : NormedSpace ℂ (AveragedSpace ρ hρ) := InnerProductSpace.toNormedSpace (𝕜 := ℂ) (E := AveragedSpace ρ hρ)

def averagedSpaceEquiv : V ≃ₗ[ℂ] AveragedSpace ρ hρ := LinearEquiv.refl ℂ V

theorem averagedSpace_inner (v w : V) :
    inner ℂ (averagedSpaceEquiv ρ hρ v) (averagedSpaceEquiv ρ hρ w) = averagedInner ρ v w := rfl

instance [FiniteDimensional ℂ V] : FiniteDimensional ℂ (AveragedSpace ρ hρ) :=
  inferInstanceAs (FiniteDimensional ℂ V)

def averagedUnitaryRepresentation : G →* (AveragedSpace ρ hρ ≃ₗᵢ[ℂ] AveragedSpace ρ hρ) where
  toFun g := (show AveragedSpace ρ hρ ≃ₗ[ℂ] AveragedSpace ρ hρ from
    LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).isometryOfInner
      (fun v w => averagedInner_invariant ρ g v w)
  map_one' := by
    ext v
    change ρ 1 v = v
    rw [map_one]
    rfl
  map_mul' g k := by
    ext v
    change ρ (g * k) v = ρ g (ρ k v)
    rw [map_mul]
    rfl

theorem averagedUnitaryRepresentation_intertwines (g : G) (v : V) :
    averagedUnitaryRepresentation ρ hρ g (averagedSpaceEquiv ρ hρ v) =
      averagedSpaceEquiv ρ hρ (ρ g v) := rfl

instance : IsBoundedSMul ℂ (AveragedSpace ρ hρ) := by
  exact NormedSpace.toIsBoundedSMul

instance : ContinuousSMul ℂ (AveragedSpace ρ hρ) := by
  infer_instance

def averagedSpaceContinuousEquiv [FiniteDimensional ℂ V] : V ≃L[ℂ] AveragedSpace ρ hρ :=
  (averagedSpaceEquiv ρ hρ).toContinuousLinearEquiv

theorem averagedUnitaryRepresentation_continuous [FiniteDimensional ℂ V]
    (v : AveragedSpace ρ hρ) :
    Continuous (fun g => averagedUnitaryRepresentation ρ hρ g v) :=
  (averagedSpaceContinuousEquiv ρ hρ).continuous.comp (hρ (show V from v))

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (π : Representation ℂ G E) (hπ : ∀ v, Continuous (fun g => π g v))

/-- An arbitrary finite-dimensional complex normed space has a Euclidean coordinate model. -/
def euclideanModelEquiv : E ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) :=
  (LinearEquiv.ofFinrankEq (R := ℂ) E (EuclideanSpace ℂ (Fin (Module.finrank ℂ E))) (by simp)).toContinuousLinearEquiv

def euclideanModelRepresentation : Representation ℂ G (EuclideanSpace ℂ (Fin (Module.finrank ℂ E))) :=
  (euclideanModelEquiv (E := E)).toLinearEquiv.conjRingEquiv.toMonoidHom.comp π

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
include hπ in
theorem euclideanModelRepresentation_continuous
    (v : EuclideanSpace ℂ (Fin (Module.finrank ℂ E))) :
    Continuous (fun g => euclideanModelRepresentation π g v) := by
  exact (euclideanModelEquiv (E := E)).continuous.comp
    (hπ ((euclideanModelEquiv (E := E)).symm v))

abbrev UnitaryModel := AveragedSpace (euclideanModelRepresentation π)
  (euclideanModelRepresentation_continuous π hπ)

def unitaryModelEquiv : E ≃L[ℂ] UnitaryModel π hπ :=
  (euclideanModelEquiv (E := E)).trans
    (averagedSpaceContinuousEquiv (euclideanModelRepresentation π)
      (euclideanModelRepresentation_continuous π hπ))

def unitaryModelRepresentation : G →* (UnitaryModel π hπ ≃ₗᵢ[ℂ] UnitaryModel π hπ) :=
  averagedUnitaryRepresentation (euclideanModelRepresentation π)
    (euclideanModelRepresentation_continuous π hπ)

theorem unitaryModel_intertwines (g : G) (v : E) :
    unitaryModelRepresentation π hπ g (unitaryModelEquiv π hπ v) =
      unitaryModelEquiv π hπ (π g v) := by
  change (euclideanModelEquiv (E := E))
    (π g ((euclideanModelEquiv (E := E)).symm ((euclideanModelEquiv (E := E)) v))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem unitaryModel_continuous (v : UnitaryModel π hπ) :
    Continuous (fun g => unitaryModelRepresentation π hπ g v) :=
  averagedUnitaryRepresentation_continuous _ _ v

/-- The invariant positive-definite Hermitian form on the original vector space. -/
@[instance_reducible]
def invariantInnerProduct : InnerProductSpace.Core ℂ E where
  inner v w := inner ℂ (unitaryModelEquiv π hπ v) (unitaryModelEquiv π hπ w)
  conj_inner_symm _ _ := inner_conj_symm _ _
  re_inner_nonneg _ := inner_self_nonneg
  add_left _ _ _ := by simp only [map_add, inner_add_left]
  smul_left v w c := by
    simp only [map_smul]
    exact inner_smul_left _ _ _
  definite v hv := by
    apply (unitaryModelEquiv π hπ).injective
    rw [map_zero]
    exact inner_self_eq_zero.mp hv

theorem invariantInnerProduct_invariant (g : G) (v w : E) :
    (invariantInnerProduct π hπ).inner (π g v) (π g w) =
      (invariantInnerProduct π hπ).inner v w := by
  change inner ℂ (unitaryModelEquiv π hπ (π g v)) (unitaryModelEquiv π hπ (π g w)) = _
  rw [← unitaryModel_intertwines, ← unitaryModel_intertwines]
  exact (unitaryModelRepresentation π hπ g).inner_map_map _ _

theorem invariantInnerProduct_continuous :
    Continuous (fun p : E × E => (invariantInnerProduct π hπ).inner p.1 p.2) :=
  ((unitaryModelEquiv π hπ).continuous.comp continuous_fst).inner
    ((unitaryModelEquiv π hπ).continuous.comp continuous_snd)

end General
end MathieuProperty
