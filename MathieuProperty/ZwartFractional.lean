import MathieuProperty.ZwartCube
import Mathlib.MeasureTheory.Integral.Pi

/-! Rational angular frequencies with actual exponential integration. Integer
frequency embeddings preserve moments, coefficient admissibility, and Newton polytopes. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Zwart

abbrev RationalLaurent (X : Type*) [TopologicalSpace X] (M : ℕ) :=
  AddMonoidAlgebra C(X,ℂ) (Fin M → ℚ)

def integerFrequency (M : ℕ) : (Fin M → ℤ) →+ (Fin M → ℚ) where
  toFun a i := a i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

theorem integerFrequency_injective (M : ℕ) : Function.Injective (integerFrequency M) := by
  intro a b h
  ext i
  have hi : (a i : ℚ) = b i := congrFun h i
  exact_mod_cast hi

def rationalize {X : Type*} [TopologicalSpace X] (M : ℕ) :
    FunctionLaurent X M →+* RationalLaurent X M :=
  AddMonoidAlgebra.mapDomainRingHom _ (integerFrequency M)

def rationalMonomial {M : ℕ} (a : Fin M → ℚ) : C(Cube M,ℂ) :=
  ⟨fun θ => ∏ i, Complex.exp ((a i : ℂ)*Complex.I*(2*Real.pi*(θ i).val)), by fun_prop⟩

def rationalMonomialHom (M : ℕ) : Multiplicative (Fin M → ℚ) →* C(Cube M,ℂ) where
  toFun a := rationalMonomial a.toAdd
  map_one' := by ext θ; simp [rationalMonomial]
  map_mul' a b := by
    ext θ
    simp only [rationalMonomial, ContinuousMap.coe_mk, ContinuousMap.mul_apply,
      toAdd_mul, Pi.add_apply, Rat.cast_add, add_mul, Complex.exp_add]
    exact Finset.prod_mul_distrib

def angleMap {X : Type*} [TopologicalSpace X] {M : ℕ} (x : X) :
    RationalLaurent X M →+* C(Cube M,ℂ) :=
  (AddMonoidAlgebra.lift ℂ C(Cube M,ℂ) (Fin M → ℚ) (rationalMonomialHom M)).toRingHom.comp
    (AddMonoidAlgebra.mapRingHom _ (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom)

theorem angleMap_single {X : Type*} [TopologicalSpace X] {M : ℕ}
    (x : X) (a : Fin M → ℚ) (c : C(X,ℂ)) :
    angleMap x (AddMonoidAlgebra.single a c) = (c x) • rationalMonomial a := by
  simp [angleMap, AddMonoidAlgebra.lift_single, rationalMonomialHom]

theorem rationalMonomial_integer_integral {M : ℕ} (a : Fin M → ℤ) :
    (∫ θ : Cube M, rationalMonomial (integerFrequency M a) θ) = if a = 0 then 1 else 0 := by
  change (∫ θ : Cube M, ∏ i, Complex.exp (((a i : ℚ) : ℂ)*Complex.I*(2*Real.pi*(θ i).val))) = _
  rw [integral_fintype_prod_volume_eq_prod (fun (i : Fin M) (t : I) =>
    Complex.exp (((a i : ℚ) : ℂ)*Complex.I*(2*Real.pi*t.val)))]

  simp_rw [Rat.cast_intCast]
  have hi (n : ℤ) : (∫ t : I, Complex.exp ((n : ℂ)*Complex.I*(2*Real.pi*t.val))) =
      if n = 0 then 1 else 0 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using Hopf.integral_unit_phase n
  simp_rw [hi]
  classical
  by_cases ha : a = 0
  · simp [ha]
  · rw [ite_eq_right ha]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem rationalize_single {X : Type*} [TopologicalSpace X] {M : ℕ}
    (a : Fin M → ℤ) (c : C(X,ℂ)) :
    rationalize M (AddMonoidAlgebra.single a c) = AddMonoidAlgebra.single (integerFrequency M a) c := by
  simp [rationalize]

theorem angleMap_rationalize_integral {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : FunctionLaurent X M) (x : X) :
    (∫ θ : Cube M, angleMap x (rationalize M f) θ) = f.coeff 0 x := by
  classical
  have he : f = ∑ n ∈ f.coeff.support, AddMonoidAlgebra.single n (f.coeff n) :=
    (AddMonoidAlgebra.sum_coeff_single f).symm
  conv_lhs => rw [he]
  simp only [map_sum, rationalize_single, angleMap_single,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, rationalMonomial_integer_integral]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro a ha ha0
      simp [ha0]
    · intro h0
      simp [Finsupp.notMem_support_iff.mp h0]
  · intro a ha
    exact (continuous_const.mul (rationalMonomial (integerFrequency M a)).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def fractionalMoment {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (δ : X → ℂ) (f : RationalLaurent X M) : ℂ :=
  ∫ x, (∫ θ : Cube M, angleMap x f θ) * δ x ∂μ

theorem fractionalMoment_rationalize {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {M : ℕ} (μ : Measure X) (δ : X → ℂ) (f : FunctionLaurent X M) :
    fractionalMoment μ δ (rationalize M f) = weightedMoment μ δ f := by
  simp only [fractionalMoment, angleMap_rationalize_integral, weightedMoment]

def rationalNewtonPolytope {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) : Set (Fin M → ℝ) :=
  convexHull ℝ ((fun a : Fin M → ℚ => fun i => (a i : ℝ)) '' (f.coeff.support : Set (Fin M → ℚ)))

theorem rationalize_support {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : FunctionLaurent X M) :
    (rationalize M f).coeff.support = f.coeff.support.image (integerFrequency M) := by
  exact Finsupp.mapDomain_support_of_injective (integerFrequency_injective M) f.coeff

theorem rationalNewtonPolytope_rationalize {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : FunctionLaurent X M) : rationalNewtonPolytope (rationalize M f) = newtonPolytope f := by
  unfold rationalNewtonPolytope newtonPolytope
  rw [rationalize_support, Finset.coe_image, Set.image_image]
  congr 2

def FractionalAdmissible {X : Type*} [TopologicalSpace X] {M : ℕ}
    (D : ℕ) (A : Subalgebra ℂ C(X,ℂ)) (f : RationalLaurent X M) : Prop :=
  (∀ a, f.coeff a ∈ A) ∧ ∀ a ∈ f.coeff.support, ∀ i,
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ ∃ z : ℤ, a i = (z : ℚ) / j

theorem rationalize_admissible {X : Type*} [TopologicalSpace X] {M D : ℕ}
    (hD : 1 ≤ D) (A : Subalgebra ℂ C(X,ℂ)) (f : FunctionLaurent X M) (hf : Admissible A f) :
    FractionalAdmissible D A (rationalize M f) := by
  classical
  constructor
  · intro a
    change (Finsupp.mapDomain (integerFrequency M) f.coeff) a ∈ A
    rw [Finsupp.mapDomain_apply]
    apply A.sum_mem
    intro b hb
    by_cases he : integerFrequency M b = a
    · simpa [Finsupp.single_apply, he] using hf b
    · simpa [Finsupp.single_apply, he] using A.zero_mem
  · intro a ha i
    rw [rationalize_support, Finset.mem_image] at ha
    obtain ⟨b,hb,rfl⟩ := ha
    exact ⟨1,le_rfl,hD,b i, by simp [integerFrequency]⟩

def FractionalConvexSupportConjecture {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (D M : ℕ) (A : Subalgebra ℂ C(X,ℂ)) (μ : Measure X) (δ : X → ℂ) : Prop :=
  ∀ f : RationalLaurent X M, FractionalAdmissible D A f →
    (∀ m : ℕ, 1 ≤ m → fractionalMoment μ δ (f^m) = 0) → 0 ∉ rationalNewtonPolytope f

theorem fractional_conjecture_implies_integer {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {D M : ℕ} (hD : 1 ≤ D) (A : Subalgebra ℂ C(X,ℂ)) (μ : Measure X) (δ : X → ℂ) :
    FractionalConvexSupportConjecture D M A μ δ → ConvexSupportConjecture M A μ δ := by
  intro h f hf hm
  have he := h (rationalize M f) (rationalize_admissible hD A f hf)
    (fun m hmp => by rw [← map_pow, fractionalMoment_rationalize]; exact hm m hmp)
  simpa only [rationalNewtonPolytope_rationalize] using he

def openAngleCube (M : ℕ) : Set (Cube M) := Set.pi Set.univ (fun _ => Set.Ioo (0 : I) 1)

theorem openAngleCube_measure (M : ℕ) : volume (openAngleCube M) = 1 := by
  change (Measure.pi (fun _ : Fin M => (volume : Measure I)))
    (Set.pi Set.univ (fun _ => Set.Ioo (0 : I) 1)) = 1
  rw [Measure.pi_pi]
  simp

theorem restrict_openAngleCube (M : ℕ) :
    (volume : Measure (Cube M)).restrict (openAngleCube M) = volume := by
  apply Measure.restrict_eq_self_of_ae_mem
  apply ae_iff.mpr
  change volume (openAngleCube M)ᶜ = 0
  have hS : MeasurableSet (openAngleCube M) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  rw [measure_compl hS (measure_ne_top _ _),
    measure_univ, openAngleCube_measure, tsub_self]

theorem fractionalMoment_open_angles {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {M : ℕ} (μ : Measure X) (δ : X → ℂ) (f : RationalLaurent X M) :
    fractionalMoment μ δ f =
      ∫ x, (∫ θ in openAngleCube M, angleMap x f θ) * δ x ∂μ := by
  simp only [fractionalMoment, restrict_openAngleCube]

theorem continuous_angleMap {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) : Continuous (fun p : X × Cube M => angleMap p.1 f p.2) := by
  classical
  have he : f = ∑ n ∈ f.coeff.support, AddMonoidAlgebra.single n (f.coeff n) :=
    (AddMonoidAlgebra.sum_coeff_single f).symm
  rw [he]
  simp only [map_sum, angleMap_single, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply continuous_finsetSum
  intro n hn
  exact ((f.coeff n).continuous.comp continuous_fst).mul
    ((rationalMonomial n).continuous.comp continuous_snd)

theorem fractionalMoment_angles_outer {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] {M : ℕ}
    (μ : Measure X) [IsFiniteMeasure μ] (δ : X → ℂ) (hδ : Continuous δ)
    (f : RationalLaurent X M) :
    fractionalMoment μ δ f = ∫ θ : Cube M, ∫ x, angleMap x f θ * δ x ∂μ := by
  unfold fractionalMoment
  have hc := (continuous_angleMap f).mul (hδ.comp continuous_fst)
  have hi := hc.integrable_of_hasCompactSupport (μ := μ.prod volume)
    (HasCompactSupport.of_compactSpace _)
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_mul_const]
end MathieuProperty.Zwart
