import MathieuProperty.LaurentSupport

/-! The exact Laurent-polynomial interface for the external multivariate
Duistermaat–van der Kallen theorem. This module defines a proposition, not a
proof of it. Conditional consumers take its proof as an explicit parameter. -/

namespace MathieuProperty

/-- The manuscript's general multivariate Duistermaat–van der Kallen statement:
a nonzero complex Laurent polynomial whose positive powers all have zero
constant term has Newton convex hull avoiding the origin. All finite dimensions,
including dimension zero, and all positive natural powers are quantified. -/
def MultivariateDvK : Prop :=
  ∀ (d : ℕ) (f : MultiLaurent d), f ≠ 0 →
    (∀ m : ℕ, 1 ≤ m → constantTerm (f ^ m) = 0) →
    (0 : Fin d → ℝ) ∉ newtonPolytope f

end MathieuProperty
