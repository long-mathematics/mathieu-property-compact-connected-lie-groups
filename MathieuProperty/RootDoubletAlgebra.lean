import Mathlib.Algebra.Lie.Sl2
import Mathlib.Basic.Complex.Basic

/-! Algebraic part of the visible root doublet argument.
This does not construct a compact-group fundamental representation or integrate
a root Lie algebra. Those remain separate ledger obligations.
-/

namespace MathieuProperty

open LieModule

variable {L V : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
  [FiniteDimensional ℂ V]

/-- A highest-weight-one vector has precisely the required first two lowering steps. -/
theorem highest_weight_one_lowering {h e f : L} (t : IsSl2Triple h e f)
    {v : V} (hv : t.HasPrimitiveVectorWith v (1 : ℂ)) :
    ⁅f, v⁆ ≠ 0 ∧ ⁅f, ⁅f, v⁆⁆ = 0 := by
  constructor
  · simpa using hv.pow_toEnd_f_ne_zero_of_eq_nat (n := 1) (by simp) (i := 1) le_rfl
  · simpa [pow_two, Module.End.mul_apply] using
      hv.pow_toEnd_f_eq_zero_of_eq_nat (n := 1) (by simp)

end MathieuProperty
