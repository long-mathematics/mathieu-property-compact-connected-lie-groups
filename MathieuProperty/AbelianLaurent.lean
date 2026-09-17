import MathieuProperty.AbelianAlgebra

/-! Formal Laurent polynomial and its exact coefficient-polynomial spectrum. -/

noncomputable section

namespace MathieuProperty.Abelian

open Polynomial

abbrev Laurent := LaurentPolynomial ℂ[X]

def formalX : Laurent := LaurentPolynomial.C X
def formalP : Laurent := P formalX (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))
def formalQ : Laurent := Q formalX (LaurentPolynomial.T 1)

def coeffNegOne : ℂ[X] := 2 * X
def coeffZero : ℂ[X] := -2 * (6 * X ^ 4 - 6 * X ^ 2 + 1)
def coeffOne : ℂ[X] := 6 * X * (X ^ 2 - 1) * (2 * X ^ 2 - 1) ^ 2
def coeffTwo : ℂ[X] := -4 * X ^ 2 * (X ^ 2 - 1) ^ 2 * (2 * X ^ 2 - 1) ^ 2

/-- The printed Laurent expansion as an equality in ℂ[x][w,w⁻¹]. -/
theorem formal_expansion : formalP =
    LaurentPolynomial.C coeffNegOne * LaurentPolynomial.T (-1) +
    LaurentPolynomial.C coeffZero +
    LaurentPolynomial.C coeffOne * LaurentPolynomial.T 1 +
    LaurentPolynomial.C coeffTwo * LaurentPolynomial.T 2 := by
  rw [formalP, expansion]
  · simp only [coeffNegOne, coeffZero, coeffOne, coeffTwo, map_mul, map_sub, map_add,
      map_pow, map_neg, map_ofNat, map_one, formalX]
    rw [show (LaurentPolynomial.T (1 : ℤ) : Laurent) ^ 2 = LaurentPolynomial.T 2 by simp]
    ring
  · rw [← LaurentPolynomial.T_add]
    norm_num

theorem coefficient_polynomials_ne_zero :
    coeffNegOne ≠ 0 ∧ coeffZero ≠ 0 ∧ coeffOne ≠ 0 ∧ coeffTwo ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
    have he := congrArg (Polynomial.eval (2 : ℂ)) h <;>
    norm_num [coeffNegOne, coeffZero, coeffOne, coeffTwo] at he

theorem formal_coeff (n : ℤ) : formalP.coeff n =
    (if n = -1 then coeffNegOne else 0) +
    (if n = 0 then coeffZero else 0) +
    (if n = 1 then coeffOne else 0) +
    (if n = 2 then coeffTwo else 0) := by
  rw [formal_expansion]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    LaurentPolynomial.C_apply, Finsupp.single_apply]
  simp [eq_comm]

/-- The formal w-spectrum; it is not a claim about each specialized endpoint x. -/
theorem formal_spectrum : formalP.coeff.support = {-1, 0, 1, 2} := by
  classical
  obtain ⟨h₁, h₀, h₂, h₃⟩ := coefficient_polynomials_ne_zero
  ext n
  simp only [Finsupp.mem_support_iff, formal_coeff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hn₁ : n = -1
  · subst n; simpa using h₁
  by_cases hn₀ : n = 0
  · subst n; simpa using h₀
  by_cases hn₂ : n = 1
  · subst n; simpa using h₂
  by_cases hn₃ : n = 2
  · subst n; simpa using h₃
  · simp [hn₁, hn₀, hn₂, hn₃]

end MathieuProperty.Abelian
