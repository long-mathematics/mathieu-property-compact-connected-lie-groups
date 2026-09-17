import MathieuProperty
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.LinearAlgebra.UnitaryGroup

/-! Type-check the precise outstanding targets. `#check` does not prove them.
No declaration in this file is supplied as a hypothesis to a project theorem.
-/

open MathieuProperty

/- The manuscript's multivariate Duistermaat--van der Kallen obligation. -/
#check (∀ (d : ℕ) (f : MultiLaurent d), f ≠ 0 →
  (∀ m : ℕ, 1 ≤ m → constantTerm (f ^ m) = 0) →
  (0 : Fin d → ℝ) ∉ newtonPolytope f : Prop)

/- Even this two-variable special case needs the missing noncancellation proof. -/
#check (∀ f : MultiLaurent 2, f ≠ 0 →
  (0 : Fin 2 → ℝ) ∈ newtonPolytope f →
  ∃ m : ℕ, 1 ≤ m ∧ constantTerm (f ^ m) ≠ 0 : Prop)

section RootEmbedding
open scoped Manifold ContDiff
variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
  [CompactSpace G] [ConnectedSpace G] [SimplyConnectedSpace G]

local instance : LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)

variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ, E) G)]

/- A necessary fragment of the visible-root-doublet lemma; it does not yet
include the fundamental representation or its invariant two-dimensional space. -/
#check (∃ φ : Matrix.specialUnitaryGroup (Fin 2) ℂ →* G,
  Continuous φ ∧ Function.Injective φ : Prop)

end RootEmbedding

section SimpleCover
open scoped Manifold ContDiff
variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
  [CompactSpace G] [ConnectedSpace G]

local instance : LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)

variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ, E) G)]

/- A necessary fragment of Z05: compactness of a simply connected cover of a
compact simple group requires finitely many sheets. The source group here is
not assumed simply connected. This command is only a type check. -/
#check (Finite (FundamentalGroup G (1 : G)) : Prop)

end SimpleCover

section FundamentalModule
open scoped TensorProduct
variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L] [LieAlgebra.IsKilling ℝ L] [Nontrivial L]
variable (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] [IsLieAbelian H]

/- A necessary algebraic fragment of L02, now using the compatible Cartan:
construct a finite-dimensional module containing the fundamental highest-weight
vector. Even this statement omits irreducibility, unitarity, and integration to
a group representation. It is type-checked only, not proved or assumed. -/
#check (∃ (n : ℕ) (a : LieRingModule (ℂ ⊗[ℝ] L) (Fin n → ℂ)),
  letI := a
  ∃ b : LieModule ℂ (ℂ ⊗[ℝ] L) (Fin n → ℂ),
  letI := b
  ∃ v : Fin n → ℂ,
    FundamentalRootWeight.IsHighestWeightVector
      (CompatibleRootData.simpleBase H) (CompatibleRootData.fundamentalWeight H) v : Prop)

end FundamentalModule
