import MathieuProperty.AbelianLaurent
import MathieuProperty.HopfIntegral

/-! Coefficient extraction for the explicit Laurent witness after specializing its polynomial variable. -/

noncomputable section
open Polynomial
namespace MathieuProperty.Abelian

local notation "LC" => LaurentPolynomial.C
local notation "LT" => LaurentPolynomial.T

def scaledLaurentEval (c : ℂ) : Polynomial ℂ →+* LaurentPolynomial ℂ :=
  Polynomial.eval₂RingHom LC (LC c * LT 1)

theorem scaledLaurentEval_monomial (c b : ℂ) (n : ℕ) :
    scaledLaurentEval c (Polynomial.monomial n b) = LC (b * c ^ n) * LT n := by
  simp [scaledLaurentEval, Polynomial.eval₂_monomial, mul_pow, map_mul, map_pow, mul_assoc]

theorem scaledLaurentEval_coeff (H : Polynomial ℂ) (c : ℂ) (n : ℕ) :
    (scaledLaurentEval c H).coeff n = H.coeff n * c ^ n := by
  induction H using Polynomial.induction_on' with
  | add H K ih ik =>
    simp [map_add, AddMonoidAlgebra.coeff_add, ih, ik, add_mul]
  | monomial k b =>
    rw [scaledLaurentEval_monomial]
    simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Polynomial.coeff_monomial]
    by_cases h : k = n
    · subst n; simp
    · simp [h]

theorem scaledLaurentEval_moment_coeff (H : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0)
    (p : LaurentPolynomial ℂ) (t : ℝ) (m : ℕ)
    (hp : LC c * LT 1 * p = (1 + LC c * LT 1) *
      (1 - LC ((t : ℂ)^2) * (1 + LC c * LT 1)^2)) :
    (scaledLaurentEval c H * p ^ m).coeff 0 = (Hopf.hopfKernel H m t).coeff m := by
  have he : scaledLaurentEval c (Hopf.hopfKernel H m t) =
      (LC c * LT 1)^m * (scaledLaurentEval c H * p^m) := by
    simp only [Hopf.hopfKernel, map_mul, map_pow, map_sub, map_one, map_add]
    have hx : scaledLaurentEval c X = LC c * LT 1 := by simp [scaledLaurentEval]
    have ht : scaledLaurentEval c (C (t : ℂ)) = LC (t : ℂ) := by
      exact Polynomial.eval₂_C _ _
    rw [hx, ht, ← map_pow]
    rw [show (LC c * LT 1)^m * (scaledLaurentEval c H * p^m) =
      scaledLaurentEval c H * (LC c * LT 1 * p)^m by ring, hp, mul_pow]
    ring
  have hcoeff := congrArg (fun f : LaurentPolynomial ℂ => f.coeff (m : ℤ)) he
  rw [scaledLaurentEval_coeff] at hcoeff
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.single_pow,
    nsmul_eq_mul, mul_one, AddMonoidAlgebra.coeff_single_mul_apply] at hcoeff
  exact (mul_left_cancel₀ (pow_ne_zero m hc) (by simpa [mul_comm] using hcoeff)).symm

/-- Specialization of the coefficient polynomials, retaining the Laurent variable. -/
def specialize (x : ℂ) : Laurent →+* LaurentPolynomial ℂ :=
  AddMonoidAlgebra.mapRingHom ℤ (Polynomial.evalRingHom x)

@[simp] theorem specialize_coeff (x : ℂ) (f : Laurent) (n : ℤ) :
    (specialize x f).coeff n = (f.coeff n).eval x := by
  simp [specialize]

@[simp] theorem specialize_C (x : ℂ) (f : ℂ[X]) :
    specialize x (LC f) = LC (f.eval x) := by
  ext n
  simp only [specialize_coeff, LaurentPolynomial.C_apply]
  split_ifs <;> simp

@[simp] theorem specialize_T (x : ℂ) (n : ℤ) :
    specialize x (LT n) = LT n := by
  change AddMonoidAlgebra.mapRingHom ℤ (Polynomial.evalRingHom x)
    (AddMonoidAlgebra.single n 1) = AddMonoidAlgebra.single n 1
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

theorem specialize_P (x : ℂ) :
    specialize x formalP = P (LC x) (LT 1) (LT (-1)) := by
  simp [formalP, P, U, V, T, formalX, map_ofNat]

theorem specialize_Q (x : ℂ) : specialize x formalQ = LC (2*x*(1-x^2)) * LT 1 := by
  simp [formalQ, Q, U, formalX, map_ofNat]


theorem formal_moment_coeff (x : ℝ) (hx : x ∈ Set.Ioo 0 1) (m s : ℕ) :
    ((formalQ ^ s * formalP ^ m).coeff 0).eval (x : ℂ) =
      (Hopf.hopfKernel (X ^ s) m (1 - 2*x^2)).coeff m := by
  let c : ℂ := 2*(x : ℂ)*(1-(x : ℂ)^2)
  have hc : c ≠ 0 := by
    have hr : 0 < 2*x*(1-x^2) := by nlinarith [hx.1, hx.2, sq_nonneg x]
    have he : c = ((2*x*(1-x^2) : ℝ) : ℂ) := by dsimp [c]; push_cast; rfl
    rw [he]
    exact Complex.ofReal_ne_zero.mpr hr.ne'
  have hu : U (LC (x : ℂ)) (LT 1) = LC c * LT 1 := by
    simp [U, c, map_ofNat]
  have ht : T (LC (x : ℂ)) = LC ((1-2*x^2 : ℝ) : ℂ) := by
    simp [T, map_ofNat]
  have hd := defect_one (LC (x : ℂ)) (LT 1) (LT (-1))
    (by rw [← LaurentPolynomial.T_add]; norm_num)
  rw [hu, ht] at hd
  have hp : LC c * LT 1 * P (LC (x : ℂ)) (LT 1) (LT (-1)) =
      (1 + LC c * LT 1) *
        (1 - LC (((1-2*x^2 : ℝ) : ℂ)^2) * (1 + LC c * LT 1)^2) := by
    rw [hd, map_pow]; ring
  have h := scaledLaurentEval_moment_coeff (X^s) c hc
    (P (LC (x : ℂ)) (LT 1) (LT (-1))) (1-2*x^2) m hp
  rw [← specialize_coeff (x : ℂ), map_mul, map_pow, map_pow,
    specialize_Q, specialize_P]
  have hX : scaledLaurentEval c X = LC c * LT 1 := Polynomial.eval₂_X _ _
  simpa only [map_pow, hX] using h

end MathieuProperty.Abelian
