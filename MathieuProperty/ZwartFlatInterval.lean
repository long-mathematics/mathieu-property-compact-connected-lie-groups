import MathieuProperty.ZwartLaurent
import MathieuProperty.EarlierXZ
/-! Exact flat-coordinate moments on [-1,1] and arbitrary product domains. -/

noncomputable section
open MeasureTheory Polynomial
open scoped unitInterval
namespace MathieuProperty.Zwart

def flatXZ : Abelian.Laurent :=
  (1 - LaurentPolynomial.T (-1)) *
    (LaurentPolynomial.C X * LaurentPolynomial.T 1 + LaurentPolynomial.C (1-X))

theorem flatXZ_specialize (t : ℂ) : Abelian.specialize t flatXZ = Abelian.xzFamily t := by
  simp [flatXZ, Abelian.xzFamily, Abelian.xzA]

theorem flatXZ_expansion : flatXZ =
    LaurentPolynomial.C (X-1) * LaurentPolynomial.T (-1) +
    LaurentPolynomial.C (1-2*X) + LaurentPolynomial.C X * LaurentPolynomial.T 1 := by
  have ht : (LaurentPolynomial.T (-1) : Abelian.Laurent) * LaurentPolynomial.T 1 = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  simp only [flatXZ, map_sub, map_one, map_mul, map_ofNat]
  linear_combination -LaurentPolynomial.C X * ht

theorem flatXZ_coeff_zero : flatXZ.coeff 0 = 1-2*X := by
  rw [flatXZ_expansion]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    LaurentPolynomial.C_apply, Finsupp.single_apply]
  norm_num

abbrev SignedInterval := Set.Icc (-1 : ℝ) 1
instance signedIntervalMeasureSpace : MeasureSpace SignedInterval := Measure.Subtype.measureSpace
instance signedIntervalFinite : IsFiniteMeasure (volume : Measure SignedInterval) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ (measurableSet_Icc.nullMeasurableSet : NullMeasurableSet (Set.Icc (-1 : ℝ) 1))]
    exact isCompact_Icc.measure_lt_top
instance signedIntervalNonempty : Nonempty SignedInterval := ⟨⟨0,by norm_num⟩⟩

theorem integral_signedInterval (f : ℝ → ℂ) :
    (∫ x : SignedInterval, f x.val) = ∫ x in (-1 : ℝ)..1, f x := by
  rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

def signedCoordinate (Y : Type*) [TopologicalSpace Y] : C(SignedInterval × Y,ℂ) :=
  ⟨fun x => (x.1.val : ℂ), by fun_prop⟩

def signedParameter (Y : Type*) [TopologicalSpace Y] : C(SignedInterval × Y,ℂ) :=
  (signedCoordinate Y + 1) * ContinuousMap.const _ (1/2)

theorem flatXZ_signed_integral (m : ℕ) (hm : 1 ≤ m) :
    (∫ x : SignedInterval, ((flatXZ^m).coeff 0).eval (((x.val : ℂ)+1)/2)) = 0 := by
  have he (x : ℝ) : ((flatXZ^m).coeff 0).eval (((x : ℂ)+1)/2) =
      (Abelian.xzFamily ((x/2+1/2 : ℝ) : ℂ)^m).coeff 0 := by
    rw [← Abelian.specialize_coeff, map_pow, flatXZ_specialize]
    push_cast
    rw [add_div]
  rw [integral_signedInterval (fun x : ℝ => ((flatXZ^m).coeff 0).eval (((x : ℂ)+1)/2))]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_div_add (fun t : ℝ => (Abelian.xzFamily (t : ℂ)^m).coeff 0)
    (by norm_num : (2 : ℝ) ≠ 0) (1/2)]
  norm_num [Abelian.xzFamily_integral_pure m hm]

theorem signedParameter_mem {Y : Type*} [TopologicalSpace Y]
    (A : Subalgebra ℂ C(SignedInterval × Y,ℂ)) (hx : signedCoordinate Y ∈ A) :
    signedParameter Y ∈ A := by
  exact A.mul_mem (A.add_mem hx A.one_mem) (A.algebraMap_mem (1/2))

theorem signed_product_pure {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] (W : Y → ℂ) {M : ℕ} (i : Fin M)
    (m : ℕ) (hm : 1 ≤ m) :
    weightedMoment ((volume : Measure SignedInterval).prod ν)
      (fun x : SignedInterval × Y => W x.2) (embed (signedParameter Y) i flatXZ ^ m) = 0 := by
  rw [← map_pow]
  unfold weightedMoment
  simp_rw [embed_coeff_zero, aeval_continuousMap_apply]
  change (∫ x : SignedInterval × Y,
    ((flatXZ^m).coeff 0).eval (((x.1.val : ℂ)+1)*(1/2)) * W x.2 ∂volume.prod ν) = 0
  simp only [one_div, ← div_eq_mul_inv]
  rw [integral_prod_mul (fun t : SignedInterval => ((flatXZ^m).coeff 0).eval (((t.val : ℂ)+1)/2)) W,
    flatXZ_signed_integral m hm, zero_mul]

theorem signed_witness_zero_mem {Y : Type*} [TopologicalSpace Y] [Nonempty Y]
    {M : ℕ} (i : Fin M) : 0 ∈ newtonPolytope (embed (signedParameter Y) i flatXZ) := by
  apply subset_convexHull ℝ _
  refine ⟨0, ?_, by ext j; simp [exponentVector]⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, embed_coeff_zero]
  intro h
  have he := congrArg (fun g : C(SignedInterval × Y,ℂ) =>
    g (⟨1,by norm_num⟩, Classical.choice ‹Nonempty Y›)) h
  rw [aeval_continuousMap_apply, flatXZ_coeff_zero] at he
  norm_num [signedParameter, signedCoordinate] at he

theorem signed_product_convexSupport_false {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [Nonempty Y] (ν : Measure Y) [SFinite ν] (W : Y → ℂ)
    {M : ℕ} (i : Fin M) (A : Subalgebra ℂ C(SignedInterval × Y,ℂ))
    (hx : signedCoordinate Y ∈ A) :
    ¬ ConvexSupportConjecture M A ((volume : Measure SignedInterval).prod ν)
      (fun x : SignedInterval × Y => W x.2) := by
  intro h
  exact h (embed (signedParameter Y) i flatXZ)
    (embed_admissible A _ (signedParameter_mem A hx) i _)
    (signed_product_pure ν W i) (signed_witness_zero_mem i)
end MathieuProperty.Zwart
