import MathieuProperty.CompactLieStructure
import MathieuProperty.NormedLieModel
import MathieuProperty.InvariantLieDecomposition
import Mathlib.Algebra.Lie.CartanExists

/-! Real Cartan subalgebras of compact Lie groups.
An anisotropic symmetric invariant form makes a nilpotent Lie algebra abelian:
its semisimple center complement is also solvable, hence zero. Applying this to
a Cartan subalgebra and the actual Haar-averaged form gives a maximal abelian,
self-centralizing Cartan subalgebra. No subgroup integration is asserted. -/

noncomputable section
namespace MathieuProperty.CompactLieForm
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
variable (B : LinearMap.BilinForm ℝ L) (hB : B.IsSymm)
  (hB_aniso : ∀ x : L, B x x = 0 → x = 0) (hinv : B.lieInvariant L)

include hB hB_aniso hinv in
/-- A nilpotent Lie algebra carrying the compact invariant-form data is abelian. -/
theorem nilpotent_abelian [LieRing.IsNilpotent L] : IsLieAbelian L := by
  obtain ⟨K, hc, hs⟩ := exists_central_semisimple_complement B hB hB_aniso hinv
  let := hs
  have htop : (⊤ : LieIdeal ℝ K) = ⊥ := by
    rw [← LieAlgebra.radical_eq_top_of_isSolvable ℝ K,
      LieAlgebra.HasTrivialRadical.radical_eq_bot]
  have hzero : ∀ x : K, x = 0 := by
    intro x
    have hx : x ∈ (⊤ : LieIdeal ℝ K) := LieSubmodule.mem_top x
    simpa only [htop, LieSubmodule.mem_bot] using hx
  have hk : K = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hz := congrArg Subtype.val (hzero ⟨x, hx⟩)
    simpa using hz
  have hcent : LieAlgebra.center ℝ L = ⊤ := by simpa [hk] using hc.sup_eq_top
  constructor
  intro x y
  have hy : y ∈ LieAlgebra.center ℝ L := by rw [hcent]; exact LieSubmodule.mem_top y
  exact (LieModule.mem_maxTrivSubmodule ℝ L L y).mp hy x


include hB hB_aniso hinv in
/-- The invariant form restricts to make any Cartan subalgebra abelian. -/
theorem cartan_abelian (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] :
    IsLieAbelian H := by
  apply nilpotent_abelian (B.restrict H.toSubmodule) (hB.restrict H.toSubmodule)
  · intro x hx
    exact Subtype.ext (hB_aniso x hx)
  · intro x y z
    exact hinv x y z

omit B hB hB_aniso hinv [FiniteDimensional ℝ L] in
/-- No abelian Lie subalgebra properly contains a Cartan subalgebra. -/
theorem cartan_maximal_abelian (H S : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
    [IsLieAbelian S] (hHS : H ≤ S) : S ≤ H := by
  intro x hx
  rw [← LieSubalgebra.IsCartanSubalgebra.self_normalizing (H := H)]
  rw [LieSubalgebra.mem_normalizer_iff]
  intro y hy
  have hxy := LieModule.IsTrivial.trivial (⟨x, hx⟩ : S) (⟨y, hHS hy⟩ : S)
  have hz : ⁅x, y⁆ = 0 := congrArg Subtype.val hxy
  rw [hz]
  exact H.zero_mem


omit B hB hB_aniso hinv [FiniteDimensional ℝ L] in
/-- An abelian Cartan subalgebra equals its centralizer. -/
theorem cartan_mem_iff_commutes (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
    [IsLieAbelian H] (x : L) : x ∈ H ↔ ∀ y ∈ H, ⁅x, y⁆ = 0 := by
  constructor
  · intro hx y hy
    exact congrArg Subtype.val (LieModule.IsTrivial.trivial (⟨x, hx⟩ : H) (⟨y, hy⟩ : H))
  · intro hx
    rw [← LieSubalgebra.IsCartanSubalgebra.self_normalizing (H := H),
      LieSubalgebra.mem_normalizer_iff]
    intro y hy
    rw [hx y hy]
    exact H.zero_mem

end MathieuProperty.CompactLieForm

namespace MathieuProperty.CompactAdjoint
open scoped Manifold ContDiff
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
local instance cartanGroupNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ, E) G) :=
  groupLieAlgebraNormed
local instance cartanGroupFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ, E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- A real Cartan subalgebra of the actual group Lie algebra. -/
def realCartan : LieSubalgebra ℝ (GroupLieAlgebra 𝓘(ℝ, E) G) :=
  LieSubalgebra.engel ℝ (LieAlgebra.exists_isCartanSubalgebra_engel ℝ
    (GroupLieAlgebra 𝓘(ℝ, E) G)).choose

instance realCartan_isCartan : (realCartan (E := E) (G := G)).IsCartanSubalgebra :=
  (LieAlgebra.exists_isCartanSubalgebra_engel ℝ (GroupLieAlgebra 𝓘(ℝ, E) G)).choose_spec

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- Compactness supplies the invariant form used to prove abelianness. -/
instance realCartan_abelian : IsLieAbelian (realCartan (E := E) (G := G)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ, E) ∞
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  exact CompactLieForm.cartan_abelian (invariantForm (E := E) (G := G))
    invariantForm_symmetric invariantForm_anisotropic invariantForm_lieInvariant _

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The constructed real Cartan admits no larger abelian Lie subalgebra. -/
theorem realCartan_maximal_abelian (S : LieSubalgebra ℝ (GroupLieAlgebra 𝓘(ℝ, E) G))
    [IsLieAbelian S] (hS : realCartan (E := E) (G := G) ≤ S) :
    S = realCartan (E := E) (G := G) :=
  le_antisymm (CompactLieForm.cartan_maximal_abelian _ S hS) hS

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- The constructed real Cartan is its own Lie-algebra centralizer. -/
theorem realCartan_mem_iff (x : GroupLieAlgebra 𝓘(ℝ, E) G) :
    x ∈ realCartan (E := E) (G := G) ↔
      ∀ y ∈ realCartan (E := E) (G := G), ⁅x, y⁆ = 0 :=
  CompactLieForm.cartan_mem_iff_commutes _ x

end MathieuProperty.CompactAdjoint
