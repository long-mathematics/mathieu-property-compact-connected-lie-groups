import MathieuProperty.ZwartSOEuler

/-! Zwart 2023, interpreted with the explicitly approved Euler indexing correction.

This is a correction of Lemma 3.3 / (16)–(17) / Conjecture 3.5, not an
identification with the malformed printed recurrence. At stage N = n+3,
there are n+1 new radial variables, with square-root powers 0,...,n.
The recursive radial block starts at one-based x_(n+2); its circle block
starts at z_2. The transformed finite sum uses these same block splits.

The counterexample directly refutes the corrected abelian conjecture. It does
not require the general SO Haar parametrization or its implication theorem.
-/

noncomputable section
open MeasureTheory
namespace MathieuProperty.Zwart

def soRadialListWeight (L : List ℕ) (x : SignedCube L.length) : ℂ :=
  ∏ i, (Real.sqrt (1-(x i).val^2) : ℂ)^(L.get i)

theorem soRadialListWeight_append (L K : List ℕ) (x : SignedCube (L.length+K.length)) :
    soRadialListWeight (L++K) (fun i => x (i.cast List.length_append)) =
      soRadialListWeight L (fun i => x (i.castAdd K.length)) *
      soRadialListWeight K (fun i => x (i.natAdd L.length)) := by
  unfold soRadialListWeight
  have he := Fin.prod_congr'
    (fun i : Fin (L.length+K.length) =>
      (Real.sqrt (1-(x i).val^2) : ℂ)^((L++K).get (i.cast List.length_append.symm)))
    List.length_append
  simp only [Fin.cast_cast, Fin.cast_eq_self] at he
  rw [he, Fin.prod_univ_add]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro i hi <;> simp [List.get_eq_getElem]

theorem soRadialListWeight_cast {L K : List ℕ} (h : L = K) (x : SignedCube L.length) :
    soRadialListWeight L x =
      soRadialListWeight K (fun i => x (i.cast (congrArg List.length h).symm)) := by
  subst h
  rfl

/-- The approved dimension split: d_(n+3) = (n+1) + d_(n+2). -/
theorem soEuler_stage_length (n : ℕ) :
    (soEulerPowers (n+3)).length = (n+1)+(soEulerPowers (n+2)).length := by
  simp [soEulerPowers]
  omega

/-- The corrected density recurrence, before multiplying its normalization constants.
With one-based indices the factors have powers (k-1)/2, k=1,...,N-2,
and the recursive block begins at x_(N-1). -/
theorem soEuler_density_recursion (n : ℕ)
    (x : SignedCube ((n+1)+(soEulerPowers (n+2)).length)) :
    soRadialListWeight (soEulerPowers (n+3))
      (fun i => x (i.cast (soEuler_stage_length n))) =
      (∏ j : Fin (n+1), (Real.sqrt (1-(x (j.castAdd _)).val^2) : ℂ)^j.val) *
      soRadialListWeight (soEulerPowers (n+2)) (fun i => x (i.natAdd (n+1))) := by
  unfold soRadialListWeight
  have he := Fin.prod_congr'
    (fun i : Fin ((n+1)+(soEulerPowers (n+2)).length) =>
      (Real.sqrt (1-(x i).val^2) : ℂ)^((soEulerPowers (n+3)).get
        (i.cast (soEuler_stage_length n).symm))) (soEuler_stage_length n)
  simp only [Fin.cast_cast, Fin.cast_eq_self] at he
  rw [he, Fin.prod_univ_add]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro i hi
  · change _ ^ ((List.ofFn (fun j : Fin (n+1) => j.val) ++
        soEulerPowers (n+2))[i.val]) = _
    rw [List.getElem_append_left (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
  · change _ ^ ((List.ofFn (fun j : Fin (n+1) => j.val) ++
        soEulerPowers (n+2))[n+1+i.val]) = _
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rfl

theorem soEuler_density_source (n : ℕ) (c : ℂ) (x : SignedCube (soEulerRadialCount n)) :
    soEulerDensity n c x = c * soRadialListWeight (soEulerPowers (n+3))
      (fun i => x (i.cast (congrArg List.length (soEulerPowers_head n)))) := by
  change c * soRadialListWeight (0::soEulerTail n) x = _
  rw [soRadialListWeight_cast (soEulerPowers_head n).symm]

abbrev SOEulerAngle := Set.Icc (0 : ℝ) Real.pi

def soEulerCosine (φ : SOEulerAngle) : SignedInterval :=
  ⟨Real.cos φ.val, Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem soEulerCosine_radical (φ : SOEulerAngle) :
    Real.sqrt (1-(soEulerCosine φ).val^2) = Real.sin φ.val := by
  have hs : 1-(Real.cos φ.val)^2 = (Real.sin φ.val)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ.val]
  change Real.sqrt (1-(Real.cos φ.val)^2) = _
  rw [hs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi φ.property.1 φ.property.2)]

/-- One term of corrected (17). For SO(N), r=N-2, s=d_(N-1), M=N-2.
The recursive transform h receives precisely the tail radial and circle blocks.
The source exponents epsilon are 0 or 1; natural b also allows unreduced terms. -/
def soEulerTransformTerm {r s M : ℕ} (c : ℂ) (k : ℤ) (a b : Fin r → ℕ)
    (h : SignedCube s → Torus M → ℂ) (x : SignedCube (r+s)) (z : Torus (M+1)) : ℂ :=
  c * (z 0 : ℂ)^k *
    (∏ j, ((x (j.castAdd s)).val : ℂ)^(a j) *
      (Real.sqrt (1-(x (j.castAdd s)).val^2) : ℂ)^(b j)) *
    h (fun i => x (i.natAdd r)) (Fin.tail z)

/-- Substitution into each finite-type summand is exact, including its recursive tail. -/
theorem soEulerTransformTerm_angles {r s M : ℕ} (c : ℂ) (k : ℤ) (a b : Fin r → ℕ)
    (h : SignedCube s → Torus M → ℂ) (φ : Fin (r+s) → SOEulerAngle)
    (z : Torus (M+1)) :
    soEulerTransformTerm c k a b h (fun i => soEulerCosine (φ i)) z =
      c * (z 0 : ℂ)^k *
        (∏ j, (Real.cos (φ (j.castAdd s)).val : ℂ)^(a j) *
          (Real.sin (φ (j.castAdd s)).val : ℂ)^(b j)) *
        h (fun i => soEulerCosine (φ (i.natAdd r))) (Fin.tail z) := by
  unfold soEulerTransformTerm
  simp only [soEulerCosine_radical]
  rfl

/-- Corrected recursive finite-type function. Its SO stage parameters are fixed here,
so an extra radial variable or a displaced recursive circle block cannot be inserted. -/
def soEulerTransformStep {ι : Type*} [Fintype ι] (n : ℕ)
    (c : ι → ℂ) (k : ι → ℤ) (a : ι → Fin (n+1) → ℕ)
    (ε : ι → Fin (n+1) → Fin 2)
    (h : ι → SignedCube (soEulerPowers (n+2)).length → Torus (n+1) → ℂ)
    (x : SignedCube ((n+1)+(soEulerPowers (n+2)).length)) (z : Torus (n+2)) : ℂ :=
  ∑ t, soEulerTransformTerm (c t) (k t) (a t) (fun j => (ε t j).val) (h t) x z

theorem soEulerTransformStep_angles {ι : Type*} [Fintype ι] (n : ℕ)
    (c : ι → ℂ) (k : ι → ℤ) (a : ι → Fin (n+1) → ℕ)
    (ε : ι → Fin (n+1) → Fin 2)
    (h : ι → SignedCube (soEulerPowers (n+2)).length → Torus (n+1) → ℂ)
    (φ : Fin ((n+1)+(soEulerPowers (n+2)).length) → SOEulerAngle)
    (z : Torus (n+2)) :
    soEulerTransformStep n c k a ε h (fun i => soEulerCosine (φ i)) z =
      ∑ t, c t * (z 0 : ℂ)^(k t) *
        (∏ j, (Real.cos (φ (j.castAdd _)).val : ℂ)^(a t j) *
          (Real.sin (φ (j.castAdd _)).val : ℂ)^((ε t j).val)) *
        h t (fun i => soEulerCosine (φ (i.natAdd (n+1)))) (Fin.tail z) := by
  unfold soEulerTransformStep
  simp_rw [soEulerTransformTerm_angles]

theorem rationalMonomial_integer_angles {M : ℕ} (a : Fin M → ℤ) (θ : Cube M) :
    rationalMonomial (integerFrequency M a) θ =
      torusMonomial a (fun i => unitCircleAngle (θ i)) := by
  change (∏ i, Complex.exp (((a i : ℚ) : ℂ)*Complex.I*(2*Real.pi*(θ i).val))) =
    ∏ i, (unitCircleAngle (θ i) : ℂ)^(a i)
  apply Finset.prod_congr rfl
  intro i hi
  rw [unitCircleAngle, Circle.coe_exp, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem angleMap_rationalize_circleEvaluation {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : FunctionLaurent X M) (x : X) (θ : Cube M) :
    angleMap x (rationalize M f) θ = circleEvaluation f x (fun i => unitCircleAngle (θ i)) := by
  classical
  have he : f = ∑ a ∈ f.coeff.support, AddMonoidAlgebra.single a (f.coeff a) :=
    (AddMonoidAlgebra.sum_coeff_single f).symm
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  simp only [map_sum, rationalize_single, angleMap_single, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, rationalMonomial_integer_angles]
  simp only [circleEvaluation, map_sum, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  change _ = circleEvaluation (AddMonoidAlgebra.single a (f.coeff a)) x _
  rw [circleEvaluation_single]
  rfl
/-- Equation (16)'s global i^(-(N-1)) factor and the actual contour integral. -/
def soEulerSourceMoment (n : ℕ) (c : ℂ)
    (f : FunctionLaurent (SignedCube (soEulerRadialCount n)) (n+2)) : ℂ :=
  (Complex.I^(n+2))⁻¹ * fractionalContourMoment volume (soEulerDensity n c)
    (rationalize (n+2) f)

theorem soEulerSourceMoment_eq (n : ℕ) (c : ℂ)
    (f : FunctionLaurent (SignedCube (soEulerRadialCount n)) (n+2)) :
    soEulerSourceMoment n c f = (2*Real.pi : ℂ)^(n+2) *
      weightedMoment volume (soEulerDensity n c) f := by
  rw [soEulerSourceMoment, fractionalContourMoment_eq, fractionalMoment_rationalize,
    mul_pow]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]

theorem soEulerSourceMoment_eq_zero_iff (n : ℕ) (c : ℂ)
    (f : FunctionLaurent (SignedCube (soEulerRadialCount n)) (n+2)) :
    soEulerSourceMoment n c f = 0 ↔ weightedMoment volume (soEulerDensity n c) f = 0 := by
  rw [soEulerSourceMoment_eq, mul_eq_zero]
  have hc : (2*Real.pi : ℂ)^(n+2) ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp only [hc, false_or]

/-- Corrected Conjecture 3.5 in actual circle-contour form. Only integer Laurent
frequencies are quantified; rationalize embeds them without changing exponents.
The global i^(-(N-1)) factor is retained in soEulerSourceMoment. -/
def SOConjecture2023Euler (n : ℕ) (c : ℂ) : Prop :=
  ∀ f : FunctionLaurent (SignedCube (soEulerRadialCount n)) (n+2),
    Admissible (signedRadialAlgebra (soEulerRadialCount n)) f →
    (∀ m : ℕ, 1 ≤ m → soEulerSourceMoment n c (f^m) = 0) → 0 ∉ newtonPolytope f

theorem so_conjecture_2023_euler_iff (n : ℕ) (c : ℂ) :
    SOConjecture2023Euler n c ↔ SOEulerConvexSupportConjecture n c := by
  unfold SOConjecture2023Euler SOEulerConvexSupportConjecture ConvexSupportConjecture
  simp only [soEulerSourceMoment_eq_zero_iff]

theorem so_conjecture_2023_euler_false (n : ℕ) (c : ℂ) :
    ¬ SOConjecture2023Euler n c :=
  fun h => soEuler_convexSupport_false n c ((so_conjecture_2023_euler_iff n c).mp h)

end MathieuProperty.Zwart
