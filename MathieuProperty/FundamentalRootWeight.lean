import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Base
import MathieuProperty.RootDoubletAlgebra

/-! The algebraic restriction of a fundamental highest weight to its root `sl₂`.

The Cartan subalgebra, root base, and highest-weight vector are the standing
data of the manuscript's root-doublet argument. This module constructs the
root triple and proves its weight is one. It does not construct a compact-group
fundamental representation or integrate the root triple to a group map.
-/

noncomputable section

namespace MathieuProperty.FundamentalRootWeight

open Classical LieAlgebra LieAlgebra.IsKilling LieModule Module

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  [IsKilling ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} [H.IsCartanSubalgebra]
  [IsTriangularizable ℂ H L]

/-- The fundamental weight dual to a chosen simple coroot. -/
def fundamentalWeight (b : (rootSystem H).Base) (α : b.support) : Dual ℂ H :=
  b.toCoweightBasis.coord α

/-- All simple-coroot pairings of a fundamental weight are Kronecker deltas. -/
theorem fundamentalWeight_coroot (b : (rootSystem H).Base) (α β : b.support) :
    fundamentalWeight b α (coroot β.val.val) = if α = β then 1 else 0 := by
  classical
  change b.toCoweightBasis.repr ((rootSystem H).coroot β.val) α = _
  rw [b.toCoweightBasis_repr_coroot]
  simp [Finsupp.single_apply, eq_comm]

@[simp]
theorem fundamentalWeight_coroot_self (b : (rootSystem H).Base) (α : b.support) :
    fundamentalWeight b α (coroot α.val.val) = 1 := by
  simp [fundamentalWeight_coroot]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule L V] [LieModule ℂ L V]

/-- A highest-weight vector: a nonzero Cartan weight vector annihilated by
every positive root space. Existence is a separate representation-theory problem. -/
structure IsHighestWeightVector (b : (rootSystem H).Base) (χ : Dual ℂ H)
    (v : V) : Prop where
  ne_zero : v ≠ 0
  mem_weightSpace : v ∈ weightSpace V χ
  positive_lie : ∀ (β : H.root), b.IsPos β → ∀ e ∈ rootSpace H β.val, ⁅e, v⁆ = 0

/-- Absence of higher root-shifted generalized weight spaces gives the usual
positive-root annihilation condition. -/
theorem highestWeightVector_of_no_higher_weights (b : (rootSystem H).Base)
    (χ : Dual ℂ H) {v : V} (hv : v ≠ 0) (hχ : v ∈ weightSpace V χ)
    (htop : ∀ (β : H.root), b.IsPos β →
      genWeightSpace V ((β.val : H → ℂ) + (χ : H → ℂ)) = ⊥) :
    IsHighestWeightVector b χ v := by
  refine ⟨hv, hχ, ?_⟩
  intro β hβ e he
  have hm := lie_mem_genWeightSpace_of_mem_genWeightSpace he
    (weightSpace_le_genWeightSpace V χ hχ)
  rwa [htop β hβ] at hm

/-- For a fundamental highest-weight vector, the actual root triple has
primitive weight one, so the existing algebraic doublet theorem applies. -/
theorem root_highest_weight_one (b : (rootSystem H).Base) (α : b.support)
    {v : V} (hv : IsHighestWeightVector b (fundamentalWeight b α) v) :
    ∃ (h e f : L) (t : IsSl2Triple h e f),
      h = (coroot α.val.val : L) ∧ e ∈ rootSpace H α.val.val ∧
      f ∈ rootSpace H (-α.val.val) ∧ t.HasPrimitiveVectorWith v (1 : ℂ) := by
  obtain ⟨h, e, f, t, he, hf⟩ :=
    exists_isSl2Triple_of_weight_isNonZero (H.isNonZero_coe_root α.val)
  have hh := t.h_eq_coroot (H.isNonZero_coe_root α.val) he hf
  refine ⟨h, e, f, t, hh, he, hf, hv.ne_zero, ?_, ?_⟩
  · rw [hh]
    change ⁅coroot α.val.val, v⁆ = (1 : ℂ) • v
    rw [(LieModule.mem_weightSpace _ _).mp hv.mem_weightSpace]
    rw [fundamentalWeight_coroot_self]
  · exact hv.positive_lie α.val (b.isPos_of_mem_support α.property) e he

/-- The first lowering is nonzero and the second vanishes for the root triple
constructed from a fundamental highest-weight vector. -/
theorem fundamental_lowering [FiniteDimensional ℂ V]
    (b : (rootSystem H).Base) (α : b.support)
    {v : V} (hv : IsHighestWeightVector b (fundamentalWeight b α) v) :
    ∃ (h e f : L) (t : IsSl2Triple h e f),
      h = (coroot α.val.val : L) ∧ e ∈ rootSpace H α.val.val ∧
      f ∈ rootSpace H (-α.val.val) ∧ t.HasPrimitiveVectorWith v (1 : ℂ) ∧
      ⁅f, v⁆ ≠ 0 ∧ ⁅f, ⁅f, v⁆⁆ = 0 := by
  obtain ⟨h, e, f, t, hh, he, hf, hp⟩ := root_highest_weight_one b α hv
  exact ⟨h, e, f, t, hh, he, hf, hp, highest_weight_one_lowering t hp⟩

end MathieuProperty.FundamentalRootWeight
