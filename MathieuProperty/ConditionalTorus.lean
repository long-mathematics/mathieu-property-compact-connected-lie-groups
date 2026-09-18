import MathieuProperty.DvKStatement
import MathieuProperty.TorusLaurent

/-! The torus Mathieu theorem relative to exactly one explicit multivariate
DvK input. The separation argument, zero case, representative algebra, and
normalized Haar correspondence are already proved unconditionally. -/

namespace MathieuProperty

/-- DvK and the proved separation argument imply the Laurent Mathieu condition. -/
theorem constantTerm_mathieu_of_dvk (hDvK : MultivariateDvK) (d : ℕ) :
    IsMathieuSubspace (LinearMap.ker (constantTermLinear d)) := by
  intro f hf h
  have hp : ∀ m : ℕ, 1 ≤ m → constantTerm (f ^ m) = 0 := hf
  change ∃ N : ℕ, ∀ m : ℕ, N ≤ m → constantTerm (h * f ^ m) = 0
  by_cases hf0 : f = 0
  · subst f
    exact zero_laurent_eventual d h
  · exact eventual_constantTerm_zero_of_newton f h (hDvK d f hf0 hp)

/-- Every finite-dimensional compact torus has the Mathieu property if the
explicit Laurent-polynomial DvK statement holds. This includes dimension zero. -/
theorem torus_mathieu_of_dvk (hDvK : MultivariateDvK) (d : ℕ) :
    HasMathieuProperty (Torus d) :=
  (torus_mathieu_iff_constantTerm d).mpr (constantTerm_mathieu_of_dvk hDvK d)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The conditional torus result transfers along any topological group
equivalence using the proved normalized-Haar pullback theorem. -/
theorem mathieu_of_torus_equiv_of_dvk (hDvK : MultivariateDvK) {d : ℕ}
    (e : G ≃ₜ* Torus d) : HasMathieuProperty G :=
  (torus_mathieu_of_dvk hDvK d).of_surjective e.symm.toMulEquiv.toMonoidHom
    e.symm.continuous e.symm.surjective

end MathieuProperty
