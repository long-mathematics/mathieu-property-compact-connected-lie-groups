import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-! Uniqueness of finite Laurent polynomials from their values on the unit circle. -/
noncomputable section
open Polynomial LaurentPolynomial
namespace MathieuProperty.Abelian

theorem infinite_complex_unitCircle : (Set.range (fun z : Circle => (z : ℂ))).Infinite := by
  have hI : (Set.Ioc (-Real.pi) Real.pi).Infinite := Set.Ioc_infinite (by linarith [Real.pi_pos])
  let : Infinite (Set.Ioc (-Real.pi) Real.pi) := hI.to_subtype
  let : Infinite Circle := Infinite.of_injective Circle.argEquiv.symm Circle.argEquiv.symm.injective
  exact Set.infinite_range_of_injective Circle.coe_injective

theorem laurent_eq_zero_of_circle (f : LaurentPolynomial ℂ)
    (h : ∀ z : Circle, LaurentPolynomial.eval₂ (RingHom.id ℂ) (Circle.toUnits z) f = 0) : f = 0 := by
  obtain ⟨n, p, hp⟩ := f.exists_T_pow
  have hroot (z : Circle) : p.eval (z : ℂ) = 0 := by
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℂ) (Circle.toUnits z)) hp
    rw [map_mul, h z, zero_mul] at he
    simpa using he
  have hp0 : p = 0 := p.eq_zero_of_infinite_isRoot
    (infinite_complex_unitCircle.mono (by rintro _ ⟨z,rfl⟩; exact hroot z))
  rw [hp0, map_zero] at hp
  have he := congrArg (fun q : LaurentPolynomial ℂ => q * LaurentPolynomial.T (-(n : ℤ))) hp
  rw [zero_mul, mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, mul_one] at he
  exact he.symm

end MathieuProperty.Abelian
