import MathieuProperty.ZwartPunctured
import Mathlib.Analysis.Analytic.Uniqueness
/-! Uniqueness of finite rational-frequency expansions on punctured circles.

Real-analytic continuation from the angular cube and Dedekind independence
of characters prove that evaluation is injective. The coefficient support
therefore belongs to the represented function, independently of its expansion.
-/

noncomputable section
open MeasureTheory
open scoped Topology
namespace MathieuProperty.Zwart

def entireMonomial {M : ℕ} (a : Fin M → ℚ) (θ : Fin M → ℝ) : ℂ :=
  ∏ i, Complex.exp ((a i : ℂ)*Complex.I*(2*Real.pi*θ i))

def entireMonomialHom {M : ℕ} (a : Fin M → ℚ) : Multiplicative (Fin M → ℝ) →* ℂ where
  toFun θ := entireMonomial a θ.toAdd
  map_one' := by simp [entireMonomial]
  map_mul' θ η := by
    simp only [entireMonomial, toAdd_mul, Pi.add_apply, Complex.ofReal_add, mul_add, Complex.exp_add]
    exact Finset.prod_mul_distrib

theorem entireMonomial_single {M : ℕ} (a : Fin M → ℚ) (i : Fin M) (t : ℝ) :
    entireMonomial a (Pi.single i t) = Complex.exp ((a i : ℂ)*Complex.I*(2*Real.pi*t)) := by
  classical
  unfold entireMonomial
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem entireMonomialHom_injective {M : ℕ} :
    Function.Injective (entireMonomialHom (M := M)) := by
  intro a b h
  ext i
  have he : (fun t : ℝ => Complex.exp ((a i : ℂ)*Complex.I*(2*Real.pi*t))) =
      (fun t : ℝ => Complex.exp ((b i : ℂ)*Complex.I*(2*Real.pi*t))) := by
    funext t
    have hh := congrArg (fun χ : Multiplicative (Fin M → ℝ) →* ℂ => χ (Multiplicative.ofAdd (Pi.single i t))) h
    change entireMonomial a (Pi.single i t) = entireMonomial b (Pi.single i t) at hh
    simpa only [entireMonomial_single] using hh
  have hd (q : ℚ) : HasDerivAt (fun t : ℝ => Complex.exp ((q : ℂ)*Complex.I*(2*Real.pi*t)))
      ((q : ℂ)*Complex.I*(2*Real.pi)) 0 := by
    convert! (((hasDerivAt_id (0 : ℂ)).const_mul ((q : ℂ)*Complex.I*(2*Real.pi))).cexp).comp_ofReal using 1
    · funext t
      dsimp only [id_eq]
      congr 1
      ring
    · simp
  have ha := hd (a i)
  rw [he] at ha
  have hab := ha.unique (hd (b i))
  have hn : Complex.I * (2*Real.pi : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
  have hc : (a i : ℂ) = b i := mul_right_cancel₀ hn (by simpa only [mul_assoc] using hab)
  exact_mod_cast hc

theorem entireMonomial_analytic {M : ℕ} (a : Fin M → ℚ) :
    AnalyticOnNhd ℝ (entireMonomial a) Set.univ := by
  intro θ hθ
  unfold entireMonomial
  apply Finset.analyticAt_fun_prod
  intro i hi
  apply analyticAt_cexp.restrictScalars.comp
  have hp : AnalyticAt ℝ (fun θ : Fin M → ℝ => (θ i : ℂ)) θ :=
    (Complex.ofRealCLM.analyticAt _).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) i).analyticAt θ)
  fun_prop

def entireAngleMap {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (x : X) (θ : Fin M → ℝ) : ℂ :=
  ∑ a ∈ f.coeff.support, f.coeff a x * entireMonomial a θ

theorem entireAngleMap_analytic {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (x : X) : AnalyticOnNhd ℝ (entireAngleMap f x) Set.univ := by
  unfold entireAngleMap
  apply Finset.analyticOnNhd_fun_sum
  intro a ha
  exact analyticOnNhd_const.mul (entireMonomial_analytic a)

theorem entireAngleMap_cube {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (x : X) (θ : Cube M) :
    entireAngleMap f x (fun i => (θ i).val) = angleMap x f θ := by
  classical
  have he : f = ∑ a ∈ f.coeff.support, AddMonoidAlgebra.single a (f.coeff a) :=
    (AddMonoidAlgebra.sum_coeff_single f).symm
  conv_rhs => rw [he]
  simp only [map_sum, angleMap_single, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  rfl

theorem entireAngleMap_eq_zero_of_open {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (x : X) (h : ∀ θ : openAngleCube M, angleMap x f θ.val = 0) :
    entireAngleMap f x = 0 := by
  apply (entireAngleMap_analytic f x).eq_of_eventuallyEq analyticOnNhd_const
    (z₀ := fun _ => (1/2 : ℝ))
  have hn (i : Fin M) : ∀ᶠ θ : Fin M → ℝ in 𝓝 (fun _ => (1/2 : ℝ)),
      θ i ∈ Set.Ioo (0 : ℝ) 1 :=
    (isOpen_Ioo.preimage (continuous_apply i)).mem_nhds (by norm_num)
  filter_upwards [Filter.eventually_all.mpr hn] with θ hθ
  have he := entireAngleMap_cube f x (fun i => ⟨θ i, (hθ i).1.le, (hθ i).2.le⟩)
  apply he.trans
  apply h ⟨_, ?_⟩
  intro i hi
  exact ⟨(hθ i).1, (hθ i).2⟩

theorem angleMap_eq_zero_of_open {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (h : ∀ x (θ : openAngleCube M), angleMap x f θ.val = 0) : f = 0 := by
  classical
  have hl := (linearIndependent_monoidHom (Multiplicative (Fin M → ℝ)) ℂ).comp
    entireMonomialHom entireMonomialHom_injective
  ext a x
  by_cases ha : a ∈ f.coeff.support
  · have hz : ∑ b ∈ f.coeff.support, f.coeff b x •
        (entireMonomialHom b : Multiplicative (Fin M → ℝ) → ℂ) = 0 := by
      ext θ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      change entireAngleMap f x θ.toAdd = 0
      exact congrFun (entireAngleMap_eq_zero_of_open f x (h x)) θ.toAdd
    exact (linearIndependent_iff'.mp hl) f.coeff.support (fun b => f.coeff b x) hz a ha
  · simp [Finsupp.notMem_support_iff.mp ha]

theorem angleMap_eq_zero {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f : RationalLaurent X M) (h : ∀ x θ, angleMap x f θ = 0) : f = 0 :=
  angleMap_eq_zero_of_open f (fun x θ => h x θ.val)

theorem angleMap_injective {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f g : RationalLaurent X M) (h : ∀ x θ, angleMap x f θ = angleMap x g θ) : f = g := by
  apply sub_eq_zero.mp
  apply angleMap_eq_zero
  intro x θ
  simp only [map_sub, ContinuousMap.sub_apply, h x θ, sub_self]

theorem puncturedEvaluation_injective {X : Type*} [TopologicalSpace X] {M : ℕ}
    (f g : RationalLaurent X M)
    (h : ∀ x z, puncturedEvaluation f x z = puncturedEvaluation g x z) : f = g := by
  apply sub_eq_zero.mp
  apply angleMap_eq_zero_of_open
  intro x θ
  have he := h x (parametrizedPunctured M θ)
  rw [puncturedEvaluation_parametrized, puncturedEvaluation_parametrized] at he
  simp only [map_sub, ContinuousMap.sub_apply, he, sub_self]

def puncturedFunctionHom (X : Type*) [TopologicalSpace X] (M : ℕ) :
    RationalLaurent X M →+* (X → (Fin M → PuncturedCircle) → ℂ) where
  toFun f := puncturedEvaluation f
  map_one' := by ext x z; simp [puncturedEvaluation]
  map_mul' f g := by ext x z; simp [puncturedEvaluation]
  map_zero' := by ext x z; simp [puncturedEvaluation]
  map_add' f g := by ext x z; simp [puncturedEvaluation]

theorem puncturedFunctionHom_injective (X : Type*) [TopologicalSpace X] (M : ℕ) :
    Function.Injective (puncturedFunctionHom X M) := by
  intro f g h
  exact puncturedEvaluation_injective f g (fun x z => congrFun (congrFun h x) z)

/-- The bijection with actual represented functions; `puncturedFunctionHom`
also proves compatibility with the ring operations. -/
def puncturedFunctionEquiv (X : Type*) [TopologicalSpace X] (M : ℕ) :
    RationalLaurent X M ≃ Set.range (puncturedFunctionHom X M) :=
  Equiv.ofInjective (puncturedFunctionHom X M) (puncturedFunctionHom_injective X M)

end MathieuProperty.Zwart
