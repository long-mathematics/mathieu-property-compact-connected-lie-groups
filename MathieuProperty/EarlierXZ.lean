import MathieuProperty.AbelianWitness

/-! The earlier weighted xz counterexample quoted in the manuscript.

Expand ((1-t)+tw)^m in the Bernstein basis. Its beta integral makes each
binomial-weighted term equal to 1/(m+1). The resulting Laurent geometric sum
telescopes; support bounds and the lowest coefficient give the two moments.
The substitution t=x² supplies the weight x and the factor 1/2. Every identity
is proved here, without assuming the cited earlier paper's moment theorem.
-/

noncomputable section
open MeasureTheory Polynomial
namespace MathieuProperty.Abelian

theorem bernstein_integral (m j : ℕ) (hj : j ≤ m) :
    ∫ t in (0 : ℝ)..1, (m.choose j : ℂ) * (t : ℂ) ^ j * (1 - (t : ℂ)) ^ (m - j) =
      1 / (m + 1 : ℂ) := by
  have hb : (∫ t in (0 : ℝ)..1, (t : ℂ) ^ j * (1 - (t : ℂ)) ^ (m - j)) =
      Complex.betaIntegral (j + 1) (m - j + 1 : ℕ) := by
    unfold Complex.betaIntegral
    congr 1
    funext t
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Complex.cpow_natCast]
  have hs : (j + 1 : ℂ) + (m - j + 1 : ℕ) = ((m + 1 : ℕ) + 1 : ℂ) := by
    push_cast
    rw [Nat.cast_sub hj]
    ring
  have hfac : (m.choose j : ℂ) * j.factorial * (m - j).factorial = m.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  simp_rw [mul_assoc (m.choose j : ℂ)]
  rw [intervalIntegral.integral_const_mul, hb,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simp; positivity) (by simp; positivity), hs]
  simp only [Nat.cast_add, Nat.cast_one, Complex.Gamma_nat_eq_factorial]
  have hg : Complex.Gamma ((m : ℂ) + 1 + 1) = ((m + 1).factorial : ℂ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.Gamma_nat_eq_factorial (m + 1)
  rw [hg]
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  exact hfac

abbrev ScalarLaurent := LaurentPolynomial ℂ

def xzA : ScalarLaurent := 1 - LaurentPolynomial.T (-1)
def xzFamily (t : ℂ) : ScalarLaurent :=
  xzA * (LaurentPolynomial.C t * LaurentPolynomial.T 1 + LaurentPolynomial.C (1 - t))

theorem xzFamily_pow (t : ℂ) (m : ℕ) :
    xzFamily t ^ m = ∑ j ∈ Finset.range (m + 1),
      LaurentPolynomial.C ((m.choose j : ℂ) * t ^ j * (1 - t) ^ (m - j)) *
        (xzA ^ m * LaurentPolynomial.T (j : ℤ)) := by
  rw [xzFamily, mul_pow, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_pow, LaurentPolynomial.T_pow, mul_one, map_mul, map_pow, map_natCast]
  ring

theorem scalarLaurent_C_mul_coeff (c : ℂ) (f : ScalarLaurent) (k : ℤ) :
    (LaurentPolynomial.C c * f).coeff k = c * f.coeff k := by
  change (AddMonoidAlgebra.single 0 c * f).coeff k = _
  rw [AddMonoidAlgebra.coeff_single_mul_apply]
  simp

theorem xzFamily_integrated_coeff (m : ℕ) (k : ℤ) :
    ∫ t in (0 : ℝ)..1, (xzFamily (t : ℂ) ^ m).coeff k =
      (1 / (m + 1 : ℂ)) * (xzA ^ m * ∑ j ∈ Finset.range (m + 1), LaurentPolynomial.T (j : ℤ)).coeff k := by
  simp_rw [xzFamily_pow, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, scalarLaurent_C_mul_coeff]
  rw [intervalIntegral.integral_finsetSum (μ := volume)]
  · simp_rw [intervalIntegral.integral_mul_const]
    rw [Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [bernstein_integral m j (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  · intro j _
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (m.choose j : ℂ) * (t : ℂ)^j * (1 - (t : ℂ))^(m-j) *
        (xzA^m * LaurentPolynomial.T (j : ℤ)).coeff k)).intervalIntegrable (μ := volume) 0 1

theorem scalarLaurent_mul_T_coeff (f : ScalarLaurent) (i k : ℤ) :
    (f * LaurentPolynomial.T i).coeff k = f.coeff (k - i) := by
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

theorem xzA_pow_coeff_succ (m : ℕ) (k : ℤ) :
    (xzA ^ (m + 1)).coeff k = (xzA ^ m).coeff k - (xzA ^ m).coeff (k + 1) := by
  rw [pow_succ, xzA, mul_sub, mul_one, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    scalarLaurent_mul_T_coeff]
  rfl

theorem xzA_pow_coeff_outside (m : ℕ) (k : ℤ) (hk : k < -(m : ℤ) ∨ 0 < k) :
    (xzA ^ m).coeff k = 0 := by
  induction m generalizing k with
  | zero =>
    have hk0 : k ≠ 0 := by omega
    change (LaurentPolynomial.T (0 : ℤ) : ScalarLaurent).coeff k = 0
    rw [LaurentPolynomial.T_apply, ite_eq_right (Ne.symm hk0)]
  | succ m ih =>
    rw [xzA_pow_coeff_succ, ih k (by omega), ih (k + 1) (by omega), sub_self]

theorem xzA_pow_coeff_bottom (m : ℕ) : (xzA ^ m).coeff (-(m : ℤ)) = (-1 : ℂ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [xzA_pow_coeff_succ, xzA_pow_coeff_outside m _ (Or.inl (by omega))]
    have hk : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by omega
    rw [hk, ih, pow_succ]
    ring

theorem xzA_geometric_sum (m : ℕ) :
    xzA * ∑ j ∈ Finset.range (m + 1), (LaurentPolynomial.T (j : ℤ) : ScalarLaurent) =
      LaurentPolynomial.T (m : ℤ) - LaurentPolynomial.T (-1) := by
  induction m with
  | zero => simp [xzA]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hh : (LaurentPolynomial.T (-1) : ScalarLaurent) * LaurentPolynomial.T ((m + 1 : ℕ) : ℤ) =
        LaurentPolynomial.T (m : ℤ) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      omega
    rw [xzA, sub_mul, one_mul, hh]
    ring

theorem xzFamily_integral_pure (m : ℕ) (hm : 1 ≤ m) :
    ∫ t in (0 : ℝ)..1, (xzFamily (t : ℂ) ^ m).coeff 0 = 0 := by
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  rw [xzFamily_integrated_coeff, pow_succ, mul_assoc, xzA_geometric_sum,
    mul_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  simp only [scalarLaurent_mul_T_coeff]
  rw [xzA_pow_coeff_outside l _ (Or.inl (by omega)),
    xzA_pow_coeff_outside l _ (Or.inr (by omega)), sub_self, mul_zero]

theorem xzFamily_integral_marked (m : ℕ) (hm : 1 ≤ m) :
    ∫ t in (0 : ℝ)..1, (xzFamily (t : ℂ) ^ m).coeff 1 = (-1 : ℂ) ^ (m - 1) / (m + 1 : ℂ) := by
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  rw [xzFamily_integrated_coeff, pow_succ, mul_assoc, xzA_geometric_sum,
    mul_sub, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  simp only [scalarLaurent_mul_T_coeff]
  rw [xzA_pow_coeff_outside l (1 - -1) (Or.inr (by omega))]
  have hk : (1 : ℤ) - (l + 1 : ℕ) = -(l : ℤ) := by omega
  rw [hk, xzA_pow_coeff_bottom]
  simp [div_eq_mul_inv, mul_comm]

theorem weighted_square_substitution (f : ℝ → ℂ) (hf : Continuous f) :
    2 * (∫ x in (0 : ℝ)..1, f (x ^ 2) * (x : ℂ)) = ∫ t in (0 : ℝ)..1, f t := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    convert! (hasDerivAt_id x).pow 2 using 1
    simp
  have hc := intervalIntegral.integral_deriv_smul_comp (a := (0 : ℝ)) (b := 1)
    (fun x _ => hd x) (by fun_prop : ContinuousOn (fun x : ℝ => 2*x) (Set.uIcc 0 1)) hf
  have he : (fun x : ℝ => (2*x) • (f ∘ (fun y : ℝ => y^2)) x) =
      (fun x : ℝ => (2 : ℂ) * (f (x^2) * (x : ℂ))) := by
    funext x
    simp only [Function.comp_apply, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [he, intervalIntegral.integral_const_mul] at hc
  simpa using hc

def earlierXZ : Laurent :=
  (1 - LaurentPolynomial.T (-1)) *
    (LaurentPolynomial.C (1 - X ^ 2) + LaurentPolynomial.C (X ^ 2) * LaurentPolynomial.T 1)

theorem earlierXZ_specialize (x : ℂ) : specialize x earlierXZ = xzFamily (x ^ 2) := by
  simp [earlierXZ, xzFamily, xzA, add_comm]

theorem xzFamily_coeff_continuous (m : ℕ) (k : ℤ) :
    Continuous (fun t : ℝ => (xzFamily (t : ℂ) ^ m).coeff k) := by
  simp_rw [xzFamily_pow, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, scalarLaurent_C_mul_coeff]
  fun_prop

theorem earlierXZ_weighted_substitution (m : ℕ) (k : ℤ) :
    2 * (∫ x in (0 : ℝ)..1, ((earlierXZ ^ m).coeff k).eval (x : ℂ) * (x : ℂ)) =
      ∫ t in (0 : ℝ)..1, (xzFamily (t : ℂ) ^ m).coeff k := by
  have he (x : ℝ) : ((earlierXZ ^ m).coeff k).eval (x : ℂ) =
      (xzFamily ((x ^ 2 : ℝ) : ℂ) ^ m).coeff k := by
    rw [← specialize_coeff, map_pow, earlierXZ_specialize, Complex.ofReal_pow]
  simp_rw [he]
  exact weighted_square_substitution _ (xzFamily_coeff_continuous m k)

theorem earlierXZ_pure (m : ℕ) (hm : 1 ≤ m) :
    ∫ x in (0 : ℝ)..1, ((earlierXZ ^ m).coeff 0).eval (x : ℂ) * (x : ℂ) = 0 := by
  have h := earlierXZ_weighted_substitution m 0
  rw [xzFamily_integral_pure m hm] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

theorem earlierXZ_marked (m : ℕ) (hm : 1 ≤ m) :
    ∫ x in (0 : ℝ)..1, ((LaurentPolynomial.T (-1) * earlierXZ ^ m).coeff 0).eval (x : ℂ) * (x : ℂ) =
      (-1 : ℂ) ^ (m - 1) / (2 * (m + 1 : ℂ)) := by
  have he : (LaurentPolynomial.T (-1) * earlierXZ ^ m).coeff 0 = (earlierXZ ^ m).coeff 1 := by
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
    rfl
  simp_rw [he]
  have h := earlierXZ_weighted_substitution m 1
  rw [xzFamily_integral_marked m hm] at h
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  rw [h]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem earlierXZ_marked_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (0 : ℝ)..1, ((LaurentPolynomial.T (-1) * earlierXZ ^ m).coeff 0).eval (x : ℂ) * (x : ℂ)) ≠ 0 := by
  rw [earlierXZ_marked m hm]
  apply div_ne_zero (pow_ne_zero _ (by norm_num))
  apply mul_ne_zero (by norm_num)
  exact_mod_cast Nat.succ_ne_zero m

theorem earlierXZ_expansion : earlierXZ =
    LaurentPolynomial.C (X ^ 2 - 1) * LaurentPolynomial.T (-1) +
    LaurentPolynomial.C (1 - 2 * X ^ 2) +
    LaurentPolynomial.C (X ^ 2) * LaurentPolynomial.T 1 := by
  have ht : (LaurentPolynomial.T (-1) : Laurent) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  simp only [earlierXZ, map_sub, map_one, map_mul, map_ofNat]
  linear_combination -LaurentPolynomial.C (X ^ 2) * ht

theorem earlierXZ_coeff (k : ℤ) : earlierXZ.coeff k =
    (if k = -1 then X ^ 2 - 1 else 0) +
    (if k = 0 then 1 - 2 * X ^ 2 else 0) +
    (if k = 1 then X ^ 2 else 0) := by
  rw [earlierXZ_expansion]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    LaurentPolynomial.C_apply, Finsupp.single_apply]
  simp [eq_comm]

theorem earlierXZ_spectrum : earlierXZ.coeff.support = {-1, 0, 1} := by
  classical
  have hneg : (X ^ 2 - 1 : ℂ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (2 : ℂ)) h
    norm_num at hh
  have hzero : (1 - 2 * X ^ 2 : ℂ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (2 : ℂ)) h
    norm_num at hh
  ext k
  simp only [Finsupp.mem_support_iff, earlierXZ_coeff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hkneg : k = -1
  · subst k; simpa using hneg
  by_cases hkzero : k = 0
  · subst k; simpa using hzero
  by_cases hkpos : k = 1
  · subst k; simp
  · simp [hkneg, hkzero, hkpos]

/-- The exact earlier weighted xz witness cited in the manuscript. -/
theorem weighted_xz_witness :
    (∀ m : ℕ, 1 ≤ m →
      (∫ x in (0 : ℝ)..1, ((earlierXZ ^ m).coeff 0).eval (x : ℂ) * (x : ℂ)) = 0) ∧
    (∀ m : ℕ, 1 ≤ m →
      (∫ x in (0 : ℝ)..1, ((LaurentPolynomial.T (-1) * earlierXZ ^ m).coeff 0).eval (x : ℂ) * (x : ℂ)) =
        (-1 : ℂ) ^ (m - 1) / (2 * (m + 1 : ℂ))) ∧
    (∀ m : ℕ, 1 ≤ m →
      (∫ x in (0 : ℝ)..1, ((LaurentPolynomial.T (-1) * earlierXZ ^ m).coeff 0).eval (x : ℂ) * (x : ℂ)) ≠ 0) ∧
    earlierXZ.coeff.support = {-1, 0, 1} :=
  ⟨earlierXZ_pure, earlierXZ_marked, earlierXZ_marked_ne_zero, earlierXZ_spectrum⟩

end MathieuProperty.Abelian
