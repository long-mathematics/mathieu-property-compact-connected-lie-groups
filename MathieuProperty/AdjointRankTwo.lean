import MathieuProperty.CompactRootNormalization
import MathieuProperty.CompactDoubletProjection
import MathieuProperty.AdjointRootString
import MathieuProperty.AdjointCoordinates
import MathieuProperty.AdjointQuotient

/-! The adjoint root-string route for an actual compact real simple Lie group
of Cartan rank at least two. All certificate data are constructed from the
compatible Cartan and the Haar-averaged invariant form. -/
noncomputable section
open scoped Manifold ContDiff TensorProduct
namespace MathieuProperty.AdjointRankTwo
open LieAlgebra LieAlgebra.IsKilling LieModule ComplexParts CompactCartanRootData
set_option backward.isDefEq.respectTransparency false
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G]
local instance rankTwoNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance rankTwoFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

/-- The exact algebraic existence target AR02, with no highest-weight,
root-integration, or covering assumption. -/
theorem exists_certificate
    (hrank : 1 < Module.finrank ℝ (realCartan (E := E) (G := G))) :
    Nonempty (AdjointCoordinates.Certificate (E := E) (G := G)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) :=
    complexification_isSimple (E := E) (G := G)
  let b := simpleBase (E := E) (G := G)
  have hr : 1 < Module.finrank ℂ (complexCartan (E := E) (G := G)) := by
    rwa [complexCartan_finrank]
  have hc : 1 < Fintype.card b.support := by
    rwa [Module.finrank_eq_card_basis b.toCoweightBasis] at hr
  let : Nontrivial b.support := Fintype.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨α,β,hne,hpair⟩ := AdjointRootString.exists_simple_pair_neg_one
    (rootSystem (complexCartan (E := E) (G := G))) b
  let B := CompactAdjoint.invariantForm (E := E) (G := G)
  have hB : B.IsSymm := CompactAdjoint.invariantForm_symmetric
  have hpos : ∀ x : GroupLieAlgebra 𝓘(ℝ,E) G, x ≠ 0 → 0 < B x x :=
    fun _ hx => CompactAdjoint.invariantForm_positive hx
  have hinv : B.lieInvariant (GroupLieAlgebra 𝓘(ℝ,E) G) := CompactAdjoint.invariantForm_lieInvariant
  obtain ⟨h,e,f,t,hh,he,hf,hcon⟩ := CompactRootReality.exists_normalized_root_triple
    B hB hpos hinv (realCartan (E := E) (G := G)) α.val.val
    ((complexCartan (E := E) (G := G)).isNonZero_coe_root α.val)
  obtain ⟨v,hv,hp⟩ := AdjointRootString.primitive_for_root_triple b hne hpair t he hf
  have hx : conj (e-f) = e-f := by simp [hcon, sub_eq_add_neg, add_comm]
  obtain ⟨X,hX⟩ := (conj_eq_self_iff _).mp hx
  have hhc : conj h = -h := by
    rw [hh]
    exact CompactRootReality.conj_coroot_eq_neg B hB hpos hinv _ α.val.val
      ((complexCartan (E := E) (G := G)).isNonZero_coe_root α.val)
  obtain ⟨Z,hZ⟩ := real_of_conj_eq_neg hhc
  have hZ' : (1 : ℂ) ⊗ₜ[ℝ] (-Z) = -Complex.I • h := by rw [TensorProduct.tmul_neg, hZ, neg_smul]
  obtain ⟨v₀,hv₀⟩ := CompactDoubletProjection.exists_real_coordinates_ne_zero B hB hpos hp.ne_zero ⁅e,v⁆
  let p : E →ₗ[ℝ] Hopf.Space := CompactDoubletProjection.realCoordinates B v ⁅e,v⁆
  refine ⟨{
    projection := p.toContinuousLinearMap
    phase := -Z
    rotation := X
    vector := v₀
    nonzero := hv₀
    phase_lie := ?_
    rotation_lie := ?_ }⟩
  · intro x
    exact (CompactDoubletProjection.real_coordinate_actions B hinv t hp hcon X (-Z) hX hZ' x).2
  · intro x
    exact (CompactDoubletProjection.real_coordinate_actions B hinv t hp hcon X (-Z) hX hZ' x).1

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- Mathieu failure in every compact real simple Lie group of rank at least two,
proved directly in its adjoint representation. -/
theorem not_mathieu
    (hrank : 1 < Module.finrank ℝ (realCartan (E := E) (G := G))) : ¬ HasMathieuProperty G :=
  AdjointCoordinates.not_mathieu (exists_certificate hrank).some

/-- The complete manuscript marker tower at rank at least two, with actual
representative functions and normalized Haar integration. -/
theorem marker_tower
    (hrank : 1 < Module.finrank ℝ (realCartan (E := E) (G := G))) :
    ∃ A P Q : representativeFunctions (G := G),
      (∀ g, ∃ r : ℝ, 0 ≤ r ∧ A.val g = (r : ℂ)) ∧ A ≠ 0 ∧
      (∀ m : ℕ, 1 ≤ m → representativeIntegral G (P ^ m) = 0) ∧
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
        representativeIntegral G (Q ^ s * P ^ m) =
          (momentConstant m : ℂ) * ((m-1).choose (s-1) : ℂ) *
            representativeIntegral G (A ^ (4*m+s))) ∧
      (∀ m s : ℕ, 1 ≤ m → m < s →
        representativeIntegral G (Q ^ s * P ^ m) = 0) ∧
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s → s ≤ m → ∃ r : ℝ, 0 < r ∧
        representativeIntegral G (Q ^ s * P ^ m) = (r : ℂ)) ∧
      ¬ HasMathieuProperty G := by
  let c := (exists_certificate hrank).some
  refine ⟨representativeA (AdjointCoordinates.first c) (AdjointCoordinates.second c),
    representativeP (AdjointCoordinates.first c) (AdjointCoordinates.second c),
    representativeQ (AdjointCoordinates.first c) (AdjointCoordinates.second c),
    ?_, AdjointCoordinates.radial_nonzero c, (AdjointCoordinates.marker_tower c).1,
    (AdjointCoordinates.marker_tower c).2, AdjointCoordinates.marked_zero c,
    AdjointCoordinates.marked_positive c, AdjointCoordinates.not_mathieu c⟩
  intro g
  exact ⟨Hopf.a (AdjointCoordinates.coordinates c g),
    (AdjointCoordinates.radial_nonnegative c g).2, (AdjointCoordinates.radial_nonnegative c g).1⟩

end MathieuProperty.AdjointRankTwo

namespace MathieuProperty.CompactAdjoint
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G] [CompactSpace G] [ConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
local instance quotientRankNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  groupLieAlgebraNormed
local instance quotientRankFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I)
local instance quotientRankFactorNormed : NormedRealLieAlgebra (idealModel (ambientSimpleFactor I)) :=
  inferInstanceAs (NormedRealLieAlgebra (ambientSimpleFactor I))

/-- The rank-at-least-two construction applies directly to the already
constructed adjoint simple quotient; no compact simply connected cover enters. -/
theorem not_mathieu_of_adjoint_rank_two
    (hrank : 1 < Module.finrank ℝ (CompactCartanRootData.realCartan
      (E := simpleAutomorphismModel I) (G := AdjointSimpleGroup I hI))) :
    ¬ HasMathieuProperty G := by
  let : IsTopologicalGroup (AdjointSimpleGroup I hI) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ,simpleAutomorphismModel I) ∞
  let : MeasurableSpace (AdjointSimpleGroup I hI) := borel _
  let : BorelSpace (AdjointSimpleGroup I hI) := ⟨rfl⟩
  exact not_mathieuProperty_of_quotient (adjointQuotientMap I hI)
    (adjointQuotientMap_continuous I hI) (adjointQuotientMap_surjective I hI)
    (AdjointRankTwo.not_mathieu hrank)

end MathieuProperty.CompactAdjoint
