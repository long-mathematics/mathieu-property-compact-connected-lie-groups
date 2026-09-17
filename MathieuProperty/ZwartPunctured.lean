import MathieuProperty.ZwartFractional
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
noncomputable section
open MeasureTheory Set
open scoped unitInterval
namespace MathieuProperty.Zwart

theorem exp_bijOn_punctured : Set.BijOn Circle.exp (Set.Ioo 0 (2*Real.pi)) {z : Circle | z ≠ 1} := by
  have hi : Set.InjOn Circle.exp (Set.Ioc 0 (2*Real.pi)) := Circle.exp_injOn_Ioc (by simp)
  have hs : Circle.exp '' Set.Ioc 0 (2*Real.pi) = Set.univ := by
    rw [← zero_add (2*Real.pi), Circle.periodic_exp.image_Ioc (by positivity)]
    exact Set.range_eq_univ.mpr (fun z => ⟨Complex.arg z, Circle.exp_arg z⟩)
  refine ⟨?_, hi.mono Set.Ioo_subset_Ioc_self, ?_⟩
  · intro t ht he
    have hte : Circle.exp t = Circle.exp (2*Real.pi) := by simpa using he
    have h := hi ⟨ht.1,ht.2.le⟩ ⟨by positivity,le_rfl⟩ hte
    exact (ne_of_lt ht.2) h
  · intro z hz
    have hm : z ∈ Circle.exp '' Set.Ioc 0 (2*Real.pi) := by rw [hs]; trivial
    obtain ⟨t,ht,he⟩ := hm
    refine ⟨t,⟨ht.1,lt_of_le_of_ne ht.2 ?_⟩,he⟩
    intro h
    apply hz
    rw [← he, h, Circle.exp_two_pi]

def unitCircleAngle (t : I) : Circle := Circle.exp (2*Real.pi*t.val)

theorem unitCircleAngle_bijOn : Set.BijOn unitCircleAngle (Set.Ioo (0 : I) 1) {z : Circle | z ≠ 1} := by
  have hp : (0 : ℝ) < 2*Real.pi := by positivity
  have hmem (t : I) (ht : t ∈ Set.Ioo (0 : I) 1) :
      2*Real.pi*t.val ∈ Set.Ioo 0 (2*Real.pi) := by
    constructor
    · exact mul_pos hp ht.1
    · simpa only [mul_one] using mul_lt_mul_of_pos_left (show t.val < 1 from ht.2) hp
  refine ⟨fun t ht => exp_bijOn_punctured.mapsTo (hmem t ht), ?_, ?_⟩
  · intro a ha b hb he
    apply Subtype.ext
    exact mul_left_cancel₀ hp.ne' (exp_bijOn_punctured.injOn (hmem a ha) (hmem b hb) he)
  · intro z hz
    obtain ⟨t,ht,he⟩ := exp_bijOn_punctured.surjOn hz
    let u : I := ⟨t/(2*Real.pi), by constructor; exact (div_pos ht.1 hp).le; exact (div_le_one hp).mpr ht.2.le⟩
    refine ⟨u,⟨?_,?_⟩,?_⟩
    · exact div_pos ht.1 hp
    · exact (div_lt_one hp).mpr ht.2
    · change Circle.exp (2*Real.pi*(t/(2*Real.pi))) = z
      rwa [mul_div_cancel₀ _ hp.ne']

abbrev PuncturedCircle := {z : Circle // z ≠ 1}

def puncturedAngleEquiv : Set.Ioo (0 : I) 1 ≃ PuncturedCircle :=
  Set.BijOn.equiv unitCircleAngle unitCircleAngle_bijOn

def puncturedEvaluation {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (x : X) (z : Fin M → PuncturedCircle) : ℂ :=
  angleMap x f (fun i => (puncturedAngleEquiv.symm (z i)).val)

def parametrizedPunctured (M : ℕ) (θ : openAngleCube M) : Fin M → PuncturedCircle :=
  fun i => puncturedAngleEquiv ⟨θ.val i, θ.property i (Set.mem_univ i)⟩

theorem puncturedEvaluation_parametrized {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (x : X) (θ : openAngleCube M) :
    puncturedEvaluation f x (parametrizedPunctured M θ) = angleMap x f θ.val := by
  simp [puncturedEvaluation, parametrizedPunctured]

theorem puncturedEvaluation_pow {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (x : X) (z : Fin M → PuncturedCircle) (m : ℕ) :
    puncturedEvaluation (f^m) x z = puncturedEvaluation f x z ^ m := by
  simp [puncturedEvaluation, map_pow]

instance openAngleCubeMeasureSpace (M : ℕ) : MeasureSpace (openAngleCube M) :=
  Measure.Subtype.measureSpace

theorem fractionalMoment_punctured {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {M : ℕ} (μ : Measure X) (δ : X → ℂ) (f : RationalLaurent X M) :
    fractionalMoment μ δ f =
      ∫ x, (∫ θ : openAngleCube M, puncturedEvaluation f x (parametrizedPunctured M θ)) * δ x ∂μ := by
  unfold fractionalMoment
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [puncturedEvaluation_parametrized]
  rw [integral_subtype (show MeasurableSet (openAngleCube M) from
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo) (fun θ => angleMap x f θ),
    restrict_openAngleCube]

/-- The branch of z^q selected by the unique argument between zero and 2*pi. -/
def puncturedPower (q : ℚ) (z : PuncturedCircle) : ℂ :=
  Complex.exp ((q : ℂ)*Complex.I*(2*Real.pi*(puncturedAngleEquiv.symm z).val.val))

theorem puncturedEvaluation_expansion {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (x : X) (z : Fin M → PuncturedCircle) :
    puncturedEvaluation f x z =
      ∑ a ∈ f.coeff.support, f.coeff a x * ∏ i, puncturedPower (a i) (z i) := by
  classical
  have he : f = ∑ a ∈ f.coeff.support, AddMonoidAlgebra.single a (f.coeff a) :=
    (AddMonoidAlgebra.sum_coeff_single f).symm
  unfold puncturedEvaluation
  conv_lhs => rw [he]
  simp only [map_sum, angleMap_single, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  rfl

def circleCurve (t : ℝ) : ℂ := Complex.exp ((Complex.I*(2*Real.pi))*t)

theorem circleCurve_hasDerivAt (t : ℝ) :
    HasDerivAt circleCurve (circleCurve t * (Complex.I*(2*Real.pi))) t := by
  convert! ((hasDerivAt_id t).ofReal_comp.const_mul (Complex.I*(2*Real.pi))).cexp using 1 <;>
    simp [circleCurve]

theorem circleCurve_logDerivative (t : ℝ) :
    deriv circleCurve t / circleCurve t = Complex.I*(2*Real.pi) := by
  rw [(circleCurve_hasDerivAt t).deriv]
  exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)

theorem circleCurve_unitCircleAngle (t : unitInterval) :
    circleCurve t.val = (unitCircleAngle t : ℂ) := by
  simp only [circleCurve, unitCircleAngle, Circle.coe_exp, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  congr 1
  ring

/-- Parametrized product dz/z integral, with the proven logarithmic Jacobian. -/
def fractionalContourMoment {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {M : ℕ} (μ : Measure X) (δ : X → ℂ) (f : RationalLaurent X M) : ℂ :=
  ∫ x, (∫ θ : openAngleCube M, puncturedEvaluation f x (parametrizedPunctured M θ) *
    ∏ i, deriv circleCurve (θ.val i).val / circleCurve (θ.val i).val) * δ x ∂μ

theorem fractionalContourMoment_eq {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {M : ℕ} (μ : Measure X) (δ : X → ℂ) (f : RationalLaurent X M) :
    fractionalContourMoment μ δ f = (Complex.I*(2*Real.pi))^M * fractionalMoment μ δ f := by
  unfold fractionalContourMoment
  simp_rw [circleCurve_logDerivative, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [integral_mul_const]
  rw [fractionalMoment_punctured, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem fractionalContourMoment_eq_zero_iff {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {M : ℕ} (μ : Measure X) (δ : X → ℂ) (f : RationalLaurent X M) :
    fractionalContourMoment μ δ f = 0 ↔ fractionalMoment μ δ f = 0 := by
  rw [fractionalContourMoment_eq, mul_eq_zero]
  have hc : (Complex.I*(2*Real.pi))^M ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)))
  simp [hc]
end MathieuProperty.Zwart
