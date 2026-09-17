import MathieuProperty.KillingBaseChange
import MathieuProperty.FundamentalRootWeight
import MathieuProperty.NormedLieModel
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Algebraic root data from a real Lie algebra with nondegenerate Killing form.

We construct its complexification, a splitting Cartan subalgebra, a simple-root
base, a chosen fundamental weight, and the associated root triple. The final
wrapper applies to the actual Lie algebra of a simple Lie group. This does not
identify a maximal torus, choose a compatible compact real root form, integrate
a root subgroup, or construct a highest-weight group representation. -/

noncomputable section
open scoped TensorProduct

namespace MathieuProperty.ComplexRootData
open LieAlgebra LieAlgebra.IsKilling
variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L] [IsKilling ℝ L]

/-- Scalar extension of the actual real Lie algebra to the complex numbers. -/
abbrev Complexification := ℂ ⊗[ℝ] L

/-- A Cartan subalgebra, constructed by the regular-element existence theorem. -/
def cartan : LieSubalgebra ℂ (Complexification L) :=
  LieSubalgebra.engel ℂ (exists_isCartanSubalgebra_engel ℂ (Complexification L)).choose

instance cartan_isCartan : (cartan L).IsCartanSubalgebra :=
  (exists_isCartanSubalgebra_engel ℂ (Complexification L)).choose_spec

/-- A simple-root base of the complexified Lie algebra. -/
def simpleBase : (rootSystem (cartan L)).Base :=
  Classical.choice (rootSystem (cartan L)).nonempty_base

variable [Nontrivial L]

instance simpleBase_nonempty : Nonempty (simpleBase L).support :=
  (simpleBase L).toCoweightBasis.index_nonempty

/-- Nontriviality ensures that the simple-root base has an element. -/
def simpleRoot : (simpleBase L).support := Classical.choice inferInstance

/-- The fundamental weight dual to the chosen simple coroot. -/
def fundamentalWeight : Module.Dual ℂ (cartan L) :=
  FundamentalRootWeight.fundamentalWeight (simpleBase L) (simpleRoot L)

/-- The manuscript weight-coroot pairing for the constructed data. -/
theorem fundamentalWeight_pairing :
    fundamentalWeight L (coroot (simpleRoot L).val.val) = 1 :=
  FundamentalRootWeight.fundamentalWeight_coroot_self _ _

/-- A root triple belonging to the constructed Cartan and chosen simple root. -/
theorem exists_root_triple :
    ∃ (h e f : Complexification L), IsSl2Triple h e f ∧
      h = (coroot (simpleRoot L).val.val : Complexification L) ∧
      e ∈ rootSpace (cartan L) (simpleRoot L).val.val ∧
      f ∈ rootSpace (cartan L) (-(simpleRoot L).val.val) := by
  have hα := (cartan L).isNonZero_coe_root (simpleRoot L).val
  obtain ⟨h, e, f, t, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  exact ⟨h, e, f, t, t.h_eq_coroot hα he hf, he, hf⟩

end MathieuProperty.ComplexRootData

namespace MathieuProperty.CompactLieRoots
open scoped Manifold ContDiff
open LieAlgebra
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
local instance rootsGroupNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ, E) G) :=
  groupLieAlgebraNormed
local instance rootsGroupFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ, E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ, E) G)]

/-- A simple Lie group supplies an algebraic root triple in its complexified Lie algebra. -/
theorem simple_group_root_triple :
    ∃ h e f : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G, IsSl2Triple h e f := by
  let : Nontrivial (GroupLieAlgebra 𝓘(ℝ, E) G) := IsSimple.nontrivial ℝ _
  obtain ⟨h, e, f, t, _⟩ := ComplexRootData.exists_root_triple (GroupLieAlgebra 𝓘(ℝ, E) G)
  exact ⟨h, e, f, t⟩

end MathieuProperty.CompactLieRoots
