import MathieuProperty.AbelianConjectures
import MathieuProperty.ZwartSOSource
import MathieuProperty.ZwartOldSU
import MathieuProperty.ZwartOldSp
import MathieuProperty.ZwartOldG2
import MathieuProperty.ZwartSU
import MathieuProperty.ZwartSp
import MathieuProperty.ZwartG2

/-! Manuscript corollary `cor:abelian-reductions`, with the explicitly approved
Euler-consistent interpretation of Zwart 2023's SO formula. All failures are
proved by direct witnesses, without assuming the general classification or
the external group-reduction implication theorems. -/

namespace MathieuProperty

/-- Failure of every specified abelian conjecture. The SO clause is the corrected
Euler interpretation, not the malformed recurrence as printed in the source.
The separate Sp(1) clauses cover the rank-one endpoint of both Sp families. -/
theorem abelian_reductions :
    (¬ Abelian.UniversalMomentConjecture) ∧
    (¬ Abelian.UniversalConvexSupportConjecture) ∧
    (¬ Abelian.UniversalGrowthConjecture) ∧
    (∀ n c, ¬ Zwart.SUNConjecture2023 n c) ∧
    (∀ n c, ¬ Zwart.SOConjecture2023Euler n c) ∧
    (∀ n c, ¬ Zwart.SpConjecture2024 n c) ∧
    (∀ c, ¬ Zwart.SpOneConjecture2024 c) ∧
    (∀ c, ¬ Zwart.G2Conjecture2024 c) ∧
    (∀ n c, ¬ Zwart.SUNConjecture2025 n c) ∧
    (∀ n c, ¬ Zwart.SpConjecture2025 n c) ∧
    (∀ c, ¬ Zwart.SpOneConjecture2025 c) ∧
    (∀ c, ¬ Zwart.G2Conjecture2025 c) :=
  ⟨Abelian.universal_moment_conjecture_false,
    Abelian.universal_convex_support_conjecture_false,
    Abelian.universal_growth_conjecture_false,
    Zwart.sun_conjecture_2023_false, Zwart.so_conjecture_2023_euler_false,
    Zwart.sp_conjecture_2024_false, Zwart.sp_one_conjecture_2024_false,
    Zwart.g2_conjecture_2024_false, Zwart.sun_conjecture_2025_false,
    Zwart.sp_conjecture_2025_false, Zwart.sp_one_conjecture_2025_false,
    Zwart.g2_conjecture_2025_false⟩

end MathieuProperty
