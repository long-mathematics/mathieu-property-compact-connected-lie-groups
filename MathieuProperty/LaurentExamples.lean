import MathieuProperty.LaurentSupport

/-! Small exact cases used while investigating the torus obstruction. -/

noncomputable section

namespace MathieuProperty

theorem constantTerm_monomial_pow {d : ℕ} (a : Fin d → ℤ) (c : ℂ) (m : ℕ) :
    constantTerm ((AddMonoidAlgebra.single a c : MultiLaurent d) ^ m) =
      if m • a = 0 then c ^ m else 0 := by
  classical
  simp [constantTerm, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Complex coefficient cancellation already defeats the naive positive-count
argument in two variables: all four monomials occur, but CT(f²)=0. -/
def cancellationExample : AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  .single (1, 0) 1 + .single (-1, 0) 1 +
    .single (0, 1) Complex.I + .single (0, -1) Complex.I

theorem cancellationExample_square : (cancellationExample ^ 2).coeff 0 = 0 := by
  norm_num [cancellationExample, pow_two, add_mul, mul_add,
    AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single, Complex.I_mul_I]

end MathieuProperty
