import MathieuProperty.TransformIntegral

/-! The polynomial-entry Hopf pair is exactly the square-root-free Laurent
pair. Right torus invariance removes the second circle, and the actual Haar
functional becomes the weighted constant-term functional for every marker power. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Abelian

def RightTorusInvariant (p : MvPolynomial (Fin 4) ℂ) : Prop :=
  ∀ a b c d z zi : ℂ, z*zi = 1 →
    MvPolynomial.eval ![a*z,b*zi,c*z,d*zi] p = MvPolynomial.eval ![a,b,c,d] p

theorem torusAverage_invariant (p : MvPolynomial (Fin 4) ℂ) (hp : RightTorusInvariant p) (x : ℝ) :
    torusAverage p x = ((entryTransform p).coeff 0).eval (x : ℂ) := by
  have he (w z : I) : torusEntryValue p x w z =
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (unitPhaseUnit w) (specialize x (entryTransform p)) := by
    rw [eval_entryTransform]
    unfold torusEntryValue
    rw [hp _ _ _ _ _ _ (unitPhase_mul_star z)]
    unfold squareFreeEntryValue
    congr 2
    funext i
    fin_cases i <;> simp [unitPhaseUnit, unitPhase_star]
    · change Complex.I * (1-(x : ℂ)^2) * unitPhase w = Complex.I * unitPhase w * (1-(x : ℂ)^2)
      ring
    · rfl
  unfold torusAverage
  simp_rw [he, integral_laurent_unit]
  simp [specialize_coeff]

theorem haar_invariant_entryIntegral_eq_weightedCT (p : MvPolynomial (Fin 4) ℂ)
    (hp : RightTorusInvariant p) :
    (∫ g : Hopf.SU2, entryPolynomialValue p g ∂normalizedHaar Hopf.SU2) =
      weightedCT (entryTransform p) := by
  rw [haar_entryIntegral_eq_transformedIntegral]
  unfold transformedIntegral weightedCT
  simp_rw [torusAverage_invariant p hp]

def polynomialP : MvPolynomial (Fin 4) ℂ :=
  entryP (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)

def polynomialQ : MvPolynomial (Fin 4) ℂ := U₀ (MvPolynomial.X 0) (MvPolynomial.X 1)

theorem eval_polynomialP (a b c d : ℂ) : MvPolynomial.eval ![a,b,c,d] polynomialP = entryP a b c d := by
  simp [polynomialP, entryP, A₀, U₀, V₀, T₀]

theorem eval_polynomialQ (a b c d : ℂ) : MvPolynomial.eval ![a,b,c,d] polynomialQ = U₀ a b := by
  simp [polynomialQ, U₀]

theorem polynomialP_torusInvariant : RightTorusInvariant polynomialP := by
  intro a b c d z zi hz
  rw [eval_polynomialP, eval_polynomialP]
  exact entryP_torus_invariance a b c d z zi hz

theorem polynomialQ_torusInvariant : RightTorusInvariant polynomialQ := by
  intro a b c d z zi hz
  rw [eval_polynomialQ, eval_polynomialQ]
  exact (torus_invariance a b c d z zi hz).2.1

theorem square_root_free_ring {R : Type*} [CommRing R] (i x w wi : R)
    (hi : i^2 = -1) (hw : w*wi = 1) :
    A₀ (i*w*(1-x^2)) (i*x) (i*x) (-i*wi) = 1 ∧
    U₀ (i*w*(1-x^2)) (i*x) = U x w ∧
    V₀ (i*x) (-i*wi) = V x wi ∧
    T₀ (i*w*(1-x^2)) (i*x) (i*x) (-i*wi) = T x := by
  dsimp [A₀,U₀,V₀,T₀,U,V,T]
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination -(i^2)*(1-x^2)*hw-hi
  · linear_combination (-2*x*w*(1-x^2))*hi
  · linear_combination (-2*x*wi)*hi
  · linear_combination -(i^2)*(1-x^2)*hw+(-1+2*x^2)*hi

def formalI : Laurent := LaurentPolynomial.C (Polynomial.C Complex.I)

theorem formalI_sq : formalI^2 = -1 := by
  unfold formalI
  rw [← map_pow, ← map_pow, Complex.I_sq, map_neg, map_one, map_neg, map_one]

theorem entryTransform_X :
    (fun k : Fin 4 => entryTransform (MvPolynomial.X k)) =
      ![formalI * LaurentPolynomial.T 1 * (1-formalX^2), formalI*formalX,
        formalI*formalX, -formalI*LaurentPolynomial.T (-1)] := by
  funext i
  fin_cases i <;> simp [entryTransform, formalI, formalX, map_mul, map_sub, map_pow]
  ring

theorem entryTransform_pair : entryTransform polynomialP = formalP ∧ entryTransform polynomialQ = formalQ := by
  have hw : (LaurentPolynomial.T 1 : Laurent)*LaurentPolynomial.T (-1) = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  obtain ⟨hA,hU,hV,hT⟩ := square_root_free_ring formalI formalX (LaurentPolynomial.T 1)
    (LaurentPolynomial.T (-1)) formalI_sq hw
  have he (k : Fin 4) := congrFun entryTransform_X k
  constructor
  · simp only [polynomialP, entryP, A₀,U₀,V₀,T₀, map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat]
    simp only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    change entryP _ _ _ _ = _
    simp only [entryP,hA,hU,hV,hT,one_pow,mul_one,one_mul,formalP,P]
  · simp only [polynomialQ,U₀,map_mul,map_neg,map_ofNat,he,Matrix.cons_val_zero,Matrix.cons_val_one]
    exact hU

theorem RightTorusInvariant.mul {p q : MvPolynomial (Fin 4) ℂ}
    (hp : RightTorusInvariant p) (hq : RightTorusInvariant q) : RightTorusInvariant (p*q) := by
  intro a b c d z zi hz
  simp only [map_mul, hp a b c d z zi hz, hq a b c d z zi hz]

theorem RightTorusInvariant.pow {p : MvPolynomial (Fin 4) ℂ}
    (hp : RightTorusInvariant p) (m : ℕ) : RightTorusInvariant (p^m) := by
  intro a b c d z zi hz
  simp only [map_pow, hp a b c d z zi hz]

theorem entryPolynomialValue_P (g : Hopf.SU2) :
    entryPolynomialValue polynomialP g = Hopf.su2P.val g := by
  exact eval_polynomialP _ _ _ _

theorem entryPolynomialValue_Q (g : Hopf.SU2) :
    entryPolynomialValue polynomialQ g = Hopf.su2Q.val g := by
  exact eval_polynomialQ _ _ _ _

/-- The actual normalized Haar functional of the universal Hopf pair agrees
with the square-root-free weighted constant-term functional, for all powers. -/
theorem transform_correspondence (m s : ℕ) :
    representativeIntegral Hopf.SU2 (Hopf.su2Q^s * Hopf.su2P^m) =
      weightedCT (formalQ^s * formalP^m) := by
  have h := haar_invariant_entryIntegral_eq_weightedCT (polynomialQ^s * polynomialP^m)
    ((polynomialQ_torusInvariant.pow s).mul (polynomialP_torusInvariant.pow m))
  rw [map_mul, map_pow, map_pow, entryTransform_pair.1, entryTransform_pair.2] at h
  have he (g : Hopf.SU2) : entryPolynomialValue (polynomialQ^s * polynomialP^m) g =
      Hopf.su2Q.val g ^ s * Hopf.su2P.val g ^ m := by
    change MvPolynomial.eval _ _ = _
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (fun a b : ℂ => a^s*b^m) (entryPolynomialValue_Q g) (entryPolynomialValue_P g)
  simp_rw [he] at h
  exact h

end MathieuProperty.Abelian
