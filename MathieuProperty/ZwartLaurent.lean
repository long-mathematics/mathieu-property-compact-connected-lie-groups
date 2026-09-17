import MathieuProperty.TorusLaurent
import MathieuProperty.AbelianWitness
import MathieuProperty.HopfCoordinateMeasure

/-! Continuous-coefficient Laurent functions and exact product-weight counterexamples.
The coefficient algebra retains equality as functions on the radial domain.
This supports the admissible radical-polynomial algebras in Zwart's reductions. -/

noncomputable section
open MeasureTheory Polynomial
open scoped unitInterval
namespace MathieuProperty.Zwart

abbrev FunctionLaurent (X : Type*) [TopologicalSpace X] (M : ℕ) :=
  AddMonoidAlgebra C(X, ℂ) (Fin M → ℤ)

def coefficientEval {X : Type*} [TopologicalSpace X] {M : ℕ} (x : X) :
    FunctionLaurent X M →+* MultiLaurent M :=
  AddMonoidAlgebra.mapRingHom _ (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom

def circleEvaluation {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : FunctionLaurent X M) (x : X) : C(Torus M, ℂ) :=
  torusLaurentMap M (coefficientEval x f)

theorem circleEvaluation_integral {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : FunctionLaurent X M) (x : X) :
    haarIntegral (Torus M) (circleEvaluation f x) = f.coeff 0 x := by
  rw [circleEvaluation, torusLaurent_integral_constantTerm]
  rfl

theorem circleEvaluation_pow {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : FunctionLaurent X M) (x : X) (m : ℕ) :
    circleEvaluation (f ^ m) x = circleEvaluation f x ^ m := by
  unfold circleEvaluation
  rw [map_pow, map_pow]

/-- Integer Fourier coefficients are uniquely determined by the represented
function, including coefficients that vanish identically on the radial domain. -/
theorem circleEvaluation_injective {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f g : FunctionLaurent X M)
    (h : ∀ x, circleEvaluation f x = circleEvaluation g x) : f = g := by
  ext a x
  have he := torusLaurentMap_injective M (h x)
  exact congrArg (fun p : MultiLaurent M => p.coeff a) he

def exponentInclusion {M : ℕ} (i : Fin M) : ℤ →+ (Fin M → ℤ) where
  toFun n := Pi.single i n
  map_zero' := by ext j; simp
  map_add' a b := by ext j; simp [Pi.single_add]

theorem exponentInclusion_injective {M : ℕ} (i : Fin M) :
    Function.Injective (exponentInclusion i) := by
  intro a b h
  have := congrFun h i
  simpa [exponentInclusion] using this

def embed {X : Type*} [TopologicalSpace X] {M : ℕ}
    (x : C(X,ℂ)) (i : Fin M) : Abelian.Laurent →+* FunctionLaurent X M :=
  (AddMonoidAlgebra.mapDomainRingHom _ (exponentInclusion i)).comp
    (AddMonoidAlgebra.mapRingHom ℤ (aeval x).toRingHom)

theorem embed_coeff {X : Type*} [TopologicalSpace X] {M : ℕ}
    (x : C(X,ℂ)) (i : Fin M) (f : Abelian.Laurent) (n : ℤ) :
    (embed x i f).coeff (exponentInclusion i n) = aeval x (f.coeff n) := by
  change Finsupp.mapDomain (exponentInclusion i)
    ((AddMonoidAlgebra.mapRingHom ℤ (aeval x).toRingHom f).coeff) (exponentInclusion i n) = _
  rw [Finsupp.mapDomain_apply_of_injective (exponentInclusion_injective i)]
  rfl

theorem embed_coeff_zero {X : Type*} [TopologicalSpace X] {M : ℕ}
    (x : C(X,ℂ)) (i : Fin M) (f : Abelian.Laurent) :
    (embed x i f).coeff 0 = aeval x (f.coeff 0) := by
  simpa only [map_zero] using embed_coeff x i f 0

theorem aeval_continuousMap_apply {X : Type*} [TopologicalSpace X]
    (x : C(X,ℂ)) (f : ℂ[X]) (y : X) : aeval x f y = f.eval (x y) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n c => simp [Polynomial.aeval_monomial]

def weightedMoment {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {M : ℕ} (μ : Measure X) (δ : X → ℂ) (f : FunctionLaurent X M) : ℂ :=
  ∫ x, f.coeff 0 x * δ x ∂μ

theorem weightedMoment_circles {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {M : ℕ} (μ : Measure X) (δ : X → ℂ) (f : FunctionLaurent X M) :
    weightedMoment μ δ f = ∫ x, haarIntegral (Torus M) (circleEvaluation f x) * δ x ∂μ := by
  simp [weightedMoment, circleEvaluation_integral]

def firstCoordinate (Y : Type*) [TopologicalSpace Y] : C(I × Y,ℂ) :=
  ⟨fun x => (x.1.val : ℂ), by fun_prop⟩

theorem product_weight_moments {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] (W : Y → ℂ) {M : ℕ} (i : Fin M)
    (f : Abelian.Laurent) :
    weightedMoment (volume.prod ν) (fun x : I × Y => (x.1.val : ℂ) * W x.2)
      (embed (firstCoordinate Y) i f) = (Abelian.weightedCT f / 2) * ∫ y, W y ∂ν := by
  unfold weightedMoment
  simp_rw [embed_coeff_zero, aeval_continuousMap_apply]
  change (∫ x : I × Y, (f.coeff 0).eval (x.1.val : ℂ) * ((x.1.val : ℂ) * W x.2) ∂volume.prod ν) = _
  simp_rw [← mul_assoc]
  rw [integral_prod_mul (fun t : I => (f.coeff 0).eval (t.val : ℂ) * (t.val : ℂ)) W]
  congr 1
  rw [Hopf.integral_unitInterval (fun t : ℝ => (f.coeff 0).eval (t : ℂ) * (t : ℂ))]
  unfold Abelian.weightedCT
  ring

theorem product_weight_pure {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] (W : Y → ℂ) {M : ℕ} (i : Fin M)
    (m : ℕ) (hm : 1 ≤ m) :
    weightedMoment (volume.prod ν) (fun x : I × Y => (x.1.val : ℂ) * W x.2)
      (embed (firstCoordinate Y) i Abelian.formalP ^ m) = 0 := by
  rw [← map_pow, product_weight_moments, Abelian.weightedCT_pure m hm, zero_div, zero_mul]


def newtonPolytope {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : FunctionLaurent X M) : Set (Fin M → ℝ) :=
  convexHull ℝ (exponentVector '' (f.coeff.support : Set (Fin M → ℤ)))

def Admissible {X : Type*} [TopologicalSpace X] {M : ℕ}
    (A : Subalgebra ℂ C(X,ℂ)) (f : FunctionLaurent X M) : Prop :=
  ∀ n, f.coeff n ∈ A

theorem aeval_mem {X : Type*} [TopologicalSpace X]
    (A : Subalgebra ℂ C(X,ℂ)) (x : C(X,ℂ)) (hx : x ∈ A) (p : ℂ[X]) :
    aeval x p ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using A.add_mem hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    exact A.mul_mem (A.algebraMap_mem c) (A.pow_mem hx n)

theorem embed_admissible {X : Type*} [TopologicalSpace X] {M : ℕ}
    (A : Subalgebra ℂ C(X,ℂ)) (x : C(X,ℂ)) (hx : x ∈ A)
    (i : Fin M) (p : Abelian.Laurent) : Admissible A (embed x i p) := by
  classical
  intro n
  change (Finsupp.mapDomain (exponentInclusion i)
    (AddMonoidAlgebra.mapRingHom ℤ (aeval x).toRingHom p).coeff) n ∈ A
  rw [Finsupp.mapDomain_apply]
  apply A.sum_mem
  intro k hk
  by_cases h : exponentInclusion i k = n
  · simp only [Finsupp.single_apply, if_pos h]
    exact aeval_mem A x hx (p.coeff k)
  · simpa [Finsupp.single_apply, h] using A.zero_mem

theorem product_witness_zero_mem {Y : Type*} [TopologicalSpace Y] [Nonempty Y]
    {M : ℕ} (i : Fin M) :
    0 ∈ newtonPolytope (embed (firstCoordinate Y) i Abelian.formalP) := by
  apply subset_convexHull ℝ _
  refine ⟨0, ?_, by ext j; simp [exponentVector]⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, embed_coeff_zero]
  intro h
  have he := congrArg (fun g : C(I × Y,ℂ) => g (0, Classical.choice ‹Nonempty Y›)) h
  rw [aeval_continuousMap_apply] at he
  norm_num [firstCoordinate, Abelian.formal_coeff, Abelian.coeffZero] at he

def ConvexSupportConjecture {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (M : ℕ) (A : Subalgebra ℂ C(X,ℂ)) (μ : Measure X) (δ : X → ℂ) : Prop :=
  ∀ f : FunctionLaurent X M, Admissible A f →
    (∀ m : ℕ, 1 ≤ m → weightedMoment μ δ (f ^ m) = 0) →
    0 ∉ newtonPolytope f

/-- Any radial coefficient algebra containing the first coordinate admits the
explicit counterexample for a density x times an arbitrary remaining weight. -/
theorem product_convexSupport_false {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [Nonempty Y] (ν : Measure Y) [SFinite ν] (W : Y → ℂ)
    {M : ℕ} (i : Fin M) (A : Subalgebra ℂ C(I × Y,ℂ))
    (hx : firstCoordinate Y ∈ A) :
    ¬ ConvexSupportConjecture M A (volume.prod ν)
      (fun x : I × Y => (x.1.val : ℂ) * W x.2) := by
  intro h
  exact h (embed (firstCoordinate Y) i Abelian.formalP)
    (embed_admissible A _ hx i _)
    (product_weight_pure ν W i) (product_witness_zero_mem i)


theorem circleEvaluation_single {X : Type*} [TopologicalSpace X] {M : ℕ}
    (n : Fin M → ℤ) (c : C(X,ℂ)) (x : X) :
    circleEvaluation (AddMonoidAlgebra.single n c) x = (c x) • torusMonomial n := by
  simp [circleEvaluation, coefficientEval, torusLaurentMap_single]

theorem continuous_circleEvaluation {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : FunctionLaurent X M) : Continuous (fun p : X × Torus M => circleEvaluation f p.1 p.2) := by
  classical
  have he : f = ∑ n ∈ f.coeff.support, AddMonoidAlgebra.single n (f.coeff n) :=
    (AddMonoidAlgebra.sum_coeff_single f).symm
  rw [he]
  simp only [circleEvaluation, map_sum, coefficientEval,
    AddMonoidAlgebra.mapRingHom_single, torusLaurentMap_single, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply continuous_finsetSum
  intro n hn
  exact ((f.coeff n).continuous.comp continuous_fst).mul
    ((torusMonomial n).continuous.comp continuous_snd)

theorem weightedMoment_circles_outer {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] {M : ℕ}
    (μ : Measure X) [IsFiniteMeasure μ] (δ : X → ℂ) (hδ : Continuous δ)
    (f : FunctionLaurent X M) :
    weightedMoment μ δ f = ∫ z : Torus M, ∫ x,
      circleEvaluation f x z * δ x ∂μ ∂normalizedHaar (Torus M) := by
  rw [weightedMoment_circles]
  have hc := (continuous_circleEvaluation f).mul (hδ.comp continuous_fst)
  have hi := hc.integrable_of_hasCompactSupport
    (μ := μ.prod (normalizedHaar (Torus M))) (HasCompactSupport.of_compactSpace _)
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_mul_const]
  rfl

end MathieuProperty.Zwart
