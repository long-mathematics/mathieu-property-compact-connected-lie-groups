import MathieuProperty.CircleTransform
import MathieuProperty.SU2Orbit
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! The square-root-free entry substitution is independent of polynomial
representatives on SU(2). Laurent interpolation on the circle extends a
unitary phase identity to complex scaling; interval interpolation then gives
equality of formal Laurent polynomials with polynomial coefficients. -/

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

def circleEntryLaurent (p : MvPolynomial (Fin 4) ℂ) (a b c d : ℂ) : LaurentPolynomial ℂ :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C
    ![LaurentPolynomial.C a * LaurentPolynomial.T 1, LaurentPolynomial.C b,
      LaurentPolynomial.C c, LaurentPolynomial.C d * LaurentPolynomial.T (-1)] p

theorem eval_circleEntryLaurent (p : MvPolynomial (Fin 4) ℂ) (a b c d : ℂ) (z : ℂˣ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) z (circleEntryLaurent p a b c d) =
      MvPolynomial.eval ![a * (z : ℂ), b, c, d * ((z⁻¹ : ℂˣ) : ℂ)] p := by
  unfold circleEntryLaurent
  rw [MvPolynomial.map_eval₂Hom]
  have hC : (LaurentPolynomial.eval₂ (RingHom.id ℂ) z).comp LaurentPolynomial.C = RingHom.id ℂ := by
    ext k
    simp
  rw [hC]
  congr 2
  funext i
  fin_cases i <;> simp

def entryPolynomialValue (p : MvPolynomial (Fin 4) ℂ) (g : Hopf.SU2) : ℂ :=
  MvPolynomial.eval ![g.val 0 0, g.val 0 1, g.val 1 0, g.val 1 1] p

theorem circleEntryLaurent_eq_zero_of_su2 (p : MvPolynomial (Fin 4) ℂ)
    (hp : ∀ g : Hopf.SU2, entryPolynomialValue p g = 0) (z : Hopf.Sphere) :
    circleEntryLaurent p z.val.1 (-star z.val.2) z.val.2 (star z.val.1) = 0 := by
  apply laurent_eq_zero_of_circle
  intro w
  rw [eval_circleEntryLaurent]
  let y : Hopf.Sphere := ⟨(z.val.1 * (w : ℂ), z.val.2), by
    simpa [Hopf.a, Complex.normSq_mul] using z.property⟩
  have he := hp (Hopf.sphereToSU2 y)
  simpa [entryPolynomialValue, Hopf.sphereToSU2, Hopf.sphereMatrix, y,
    star_mul, ← Circle.coe_inv_eq_conj, mul_comm] using he

theorem entry_polynomial_zero_complex_scale (p : MvPolynomial (Fin 4) ℂ)
    (hp : ∀ g : Hopf.SU2, entryPolynomialValue p g = 0) (z : Hopf.Sphere) (u : ℂˣ) :
    MvPolynomial.eval ![z.val.1 * (u : ℂ), -star z.val.2, z.val.2,
      star z.val.1 * ((u⁻¹ : ℂˣ) : ℂ)] p = 0 := by
  rw [← eval_circleEntryLaurent, circleEntryLaurent_eq_zero_of_su2 p hp z, map_zero]

def squareFreeEntryValue (p : MvPolynomial (Fin 4) ℂ) (x w : ℂ) : ℂ :=
  MvPolynomial.eval ![Complex.I * w * (1-x^2), Complex.I*x,
    Complex.I*x, -Complex.I*w⁻¹] p

theorem squareFreeEntryValue_zero_interior (p : MvPolynomial (Fin 4) ℂ)
    (hp : ∀ g : Hopf.SU2, entryPolynomialValue p g = 0)
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) (w : Circle) :
    squareFreeEntryValue p x w = 0 := by
  have hrpos : 0 < Real.sqrt (1 - x^2) := Real.sqrt_pos.mpr (by nlinarith [hx.1,hx.2])
  have hr : (Real.sqrt (1-x^2) : ℂ)^2 = 1-(x : ℂ)^2 := by
    have he := congrArg Complex.ofReal (Real.sq_sqrt (le_of_lt (by nlinarith [hx.1,hx.2] : 0 < 1-x^2)))
    simpa using he
  let z : Hopf.Sphere := ⟨(Complex.I * (w : ℂ) * Real.sqrt (1-x^2), Complex.I*x), by
    simp only [Hopf.a, Complex.normSq_mul, Complex.normSq_I, Circle.normSq_coe, one_mul, Complex.normSq_ofReal]
    nlinarith [Real.sq_sqrt (by nlinarith [hx.1,hx.2] : 0 ≤ 1-x^2)]⟩
  let u : ℂˣ := Units.mk0 (Real.sqrt (1-x^2) : ℂ) (by exact_mod_cast hrpos.ne')
  have he := entry_polynomial_zero_complex_scale p hp z u
  have ht : ![z.val.1 * (u : ℂ), -star z.val.2, z.val.2,
      star z.val.1 * ((u⁻¹ : ℂˣ) : ℂ)] =
      ![Complex.I * (w : ℂ) * (1-(x : ℂ)^2), Complex.I*x, Complex.I*x, -Complex.I*(w : ℂ)⁻¹] := by
    funext i
    have hc : (Real.sqrt (1-x^2) : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    fin_cases i <;> simp [z, u, star_mul, ← Circle.coe_inv_eq_conj, mul_assoc, ← pow_two, hr] <;> field_simp [hc]
  rw [ht] at he
  exact he

theorem squareFreeEntryValue_zero_on_unit (p : MvPolynomial (Fin 4) ℂ)
    (hp : ∀ g : Hopf.SU2, entryPolynomialValue p g = 0)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (w : Circle) :
    squareFreeEntryValue p x w = 0 := by
  have h : Set.EqOn (fun t : ℝ => squareFreeEntryValue p t w) (fun _ => 0) (Set.Ioo 0 1) :=
    fun t ht => squareFreeEntryValue_zero_interior p hp t ht w
  have hc : Continuous (fun t : ℝ => squareFreeEntryValue p t w) := by
    apply p.continuous_eval.comp
    exact continuous_pi (by intro i; fin_cases i <;> simp <;> fun_prop)
  exact h.closure hc continuous_const (by simpa [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)] using hx)

def entryTransform : MvPolynomial (Fin 4) ℂ →+* Laurent :=
  MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp Polynomial.C)
    ![LaurentPolynomial.C (Polynomial.C Complex.I * (1-Polynomial.X^2)) * LaurentPolynomial.T 1,
      LaurentPolynomial.C (Polynomial.C Complex.I * Polynomial.X),
      LaurentPolynomial.C (Polynomial.C Complex.I * Polynomial.X),
      LaurentPolynomial.C (Polynomial.C (-Complex.I)) * LaurentPolynomial.T (-1)]

theorem specialize_entryTransform (p : MvPolynomial (Fin 4) ℂ) (x : ℂ) :
    specialize x (entryTransform p) = circleEntryLaurent p (Complex.I*(1-x^2))
      (Complex.I*x) (Complex.I*x) (-Complex.I) := by
  unfold entryTransform circleEntryLaurent
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (specialize x).comp (LaurentPolynomial.C.comp Polynomial.C) = LaurentPolynomial.C := by
    ext k
    simp
  rw [hc]
  congr 2
  funext i
  fin_cases i <;> simp

theorem eval_entryTransform (p : MvPolynomial (Fin 4) ℂ) (x : ℂ) (w : ℂˣ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) w (specialize x (entryTransform p)) =
      squareFreeEntryValue p x w := by
  rw [specialize_entryTransform, eval_circleEntryLaurent]
  unfold squareFreeEntryValue
  congr 2
  funext i
  fin_cases i <;> simp
  ring

theorem entryTransform_zero_of_su2 (p : MvPolynomial (Fin 4) ℂ)
    (hp : ∀ g : Hopf.SU2, entryPolynomialValue p g = 0) : entryTransform p = 0 := by
  have hs (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : specialize x (entryTransform p) = 0 := by
    apply laurent_eq_zero_of_circle
    intro w
    rw [eval_entryTransform]
    exact squareFreeEntryValue_zero_on_unit p hp x hx w
  ext n : 1
  have hc : (entryTransform p).coeff n = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).image Complex.ofReal_injective.injOn).mono
    rintro _ ⟨x,hx,rfl⟩
    have h := congrArg (fun q : LaurentPolynomial ℂ => q.coeff n) (hs x ⟨hx.1.le,hx.2.le⟩)
    change Polynomial.eval (x : ℂ) ((entryTransform p).coeff n) = 0
    simpa only [specialize_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h
  simpa using hc

/-- Square-root-free substitution is independent of the polynomial representative
of a function on SU(2), as an equality of formal Laurent polynomials. -/
theorem entryTransform_representative_independent (p q : MvPolynomial (Fin 4) ℂ)
    (hpq : ∀ g : Hopf.SU2, entryPolynomialValue p g = entryPolynomialValue q g) :
    entryTransform p = entryTransform q := by
  have hz : entryTransform (p-q) = 0 := entryTransform_zero_of_su2 (p-q) (by
    intro g
    simp only [entryPolynomialValue, map_sub]
    exact sub_eq_zero.mpr (hpq g))
  simpa only [map_sub, sub_eq_zero] using hz

end MathieuProperty.Abelian
