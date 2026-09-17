import MathieuProperty.AbelianWitness
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Algebra.MvPolynomial

/-! The universal abelian moment, convex-support, and growth conjectures, with
explicit counterexamples at N=M=1 and admissible weight δ=x.
The circle integrations use normalized constant-term extraction; the surrounding
polynomial integration is the actual Lebesgue integral over the unit cube. Definitions follow Müger–Tuset, arXiv:2410.11622v2, §6.
See `MixedPhase.lean` for the product-circle correspondence. -/

noncomputable section
open MeasureTheory Polynomial
namespace MathieuProperty.Abelian
abbrev MixedLaurent (N M : ℕ) := AddMonoidAlgebra (MvPolynomial (Fin N) ℂ) (Fin M → ℤ)

def mixedIntegral {N M : ℕ} (δ : MvPolynomial (Fin N) ℂ) (f : MixedLaurent N M) : ℂ :=
  ∫ x in Set.Icc (0 : Fin N → ℝ) 1,
    MvPolynomial.eval (fun i => (x i : ℂ)) (f.coeff 0 * δ)

/-- Every integrand in the universal conjectures is integrable on the unit cube. -/
theorem mixedIntegral_integrable {N M : ℕ} (δ : MvPolynomial (Fin N) ℂ)
    (f : MixedLaurent N M) :
    IntegrableOn (fun x : Fin N → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) (f.coeff 0 * δ))
      (Set.Icc (0 : Fin N → ℝ) 1) := by
  apply Continuous.integrableOn_Icc
  exact (f.coeff 0 * δ).continuous_eval.comp (by fun_prop)

def AdmissibleWeight {N : ℕ} (δ : MvPolynomial (Fin N) ℂ) : Prop :=
  ∃ d : Fin N →₀ ℕ, ∃ c : ℂ, c ≠ 0 ∧ (∀ i, Odd (d i)) ∧ δ = MvPolynomial.monomial d c

def mixedNewtonPolytope {N M : ℕ} (f : MixedLaurent N M) : Set (Fin M → ℝ) :=
  convexHull ℝ ((fun a : Fin M → ℤ => fun i => (a i : ℝ)) '' (↑f.coeff.support : Set (Fin M → ℤ)))

def UniversalMomentConjecture : Prop := ∀ N M (δ : MvPolynomial (Fin N) ℂ),
  AdmissibleWeight δ → ∀ f g : MixedLaurent N M,
    (∀ m : ℕ, 1 ≤ m → mixedIntegral δ (f ^ m) = 0) →
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m → mixedIntegral δ (g * f ^ m) = 0

def UniversalConvexSupportConjecture : Prop := ∀ N M (δ : MvPolynomial (Fin N) ℂ),
  AdmissibleWeight δ → ∀ f : MixedLaurent N M,
    (∀ m : ℕ, 1 ≤ m → mixedIntegral δ (f ^ m) = 0) → 0 ∉ mixedNewtonPolytope f

def singleExponent : ℤ ≃+ (Fin 1 → ℤ) where
  toFun n := fun _ => n
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by ext i; exact congrArg f (Subsingleton.elim 0 i)
  map_add' _ _ := rfl

def singleMixed : Laurent ≃+* MixedLaurent 1 1 :=
  (AddMonoidAlgebra.mapRingEquiv ℤ (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm.toRingEquiv).trans
    (AddMonoidAlgebra.mapDomainRingEquiv _ singleExponent)

theorem singleMixed_coeff (f : Laurent) (a : Fin 1 → ℤ) :
    (singleMixed f).coeff a = (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (f.coeff (a 0)) := by
  simp [singleMixed, Finsupp.equivMapDomain_apply, singleExponent]

theorem singleMixed_eval (f : Laurent) (x : Fin 1 → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) ((singleMixed f).coeff 0 * MvPolynomial.X 0) =
      (f.coeff 0).eval (x 0 : ℂ) * (x 0 : ℂ) := by
  rw [singleMixed_coeff]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
  change MvPolynomial.eval₂ (RingHom.id ℂ) _ _ * _ = _
  rw [MvPolynomial.eval₂_uniqueAlgEquiv_symm]
  rfl

theorem mixedIntegral_single (f : Laurent) :
    mixedIntegral (MvPolynomial.X (0 : Fin 1)) (singleMixed f) = weightedCT f / 2 := by
  unfold mixedIntegral weightedCT
  simp_rw [singleMixed_eval]
  let e := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have hs : e ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc (0 : Fin 1 → ℝ) 1 := by
    ext x
    change (0 ≤ x 0 ∧ x 0 ≤ 1) ↔ (∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ 1)
    simp [Fin.forall_fin_one]
  have hp := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).restrict_preimage
    (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc
  rw [hs] at hp
  have hi := hp.integral_comp' (fun x : ℝ => (f.coeff 0).eval (x : ℂ) * (x : ℂ))
  change (∫ x in Set.Icc (0 : Fin 1 → ℝ) 1, (f.coeff 0).eval (x 0 : ℂ)*(x 0 : ℂ)) =
    ∫ x in Set.Icc (0 : ℝ) 1, (f.coeff 0).eval (x : ℂ)*(x : ℂ) at hi
  rw [hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  ring

theorem coordinate_weight_admissible :
    AdmissibleWeight (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ) := by
  refine ⟨Finsupp.single 0 1, 1, one_ne_zero, ?_, rfl⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp

theorem universal_moment_conjecture_false : ¬ UniversalMomentConjecture := by
  intro h
  obtain ⟨k, hk⟩ := h 1 1 (MvPolynomial.X 0) coordinate_weight_admissible
    (singleMixed formalP) (singleMixed formalQ) (by
      intro m hm
      rw [← map_pow, mixedIntegral_single, weightedCT_pure m hm, zero_div])
  let m := max k 1
  have hm : 1 ≤ m := le_max_right _ _
  have hz := hk m (le_max_left _ _)
  rw [← map_pow, ← map_mul, mixedIntegral_single] at hz
  have hf := weightedCT_marked m 1 hm (by omega)
  simp only [pow_one, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one] at hf
  rw [hf] at hz
  have hn : (momentConstant m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (momentConstant_pos m).ne'
  exact (div_ne_zero hn (by norm_num)) hz

theorem singleMixed_formalP_zero_mem : (0 : Fin 1 → ℝ) ∈ mixedNewtonPolytope (singleMixed formalP) := by
  apply subset_convexHull ℝ _
  refine ⟨0, ?_, by ext i; simp⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, singleMixed_coeff]
  have hz : formalP.coeff 0 ≠ 0 := by
    simp only [formal_coeff]
    simpa using coefficient_polynomials_ne_zero.2.1
  intro h
  apply hz
  apply (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm.injective
  exact h.trans (map_zero _).symm

theorem universal_convex_support_conjecture_false : ¬ UniversalConvexSupportConjecture := by
  intro h
  apply h 1 1 (MvPolynomial.X 0) coordinate_weight_admissible (singleMixed formalP)
    (fun m hm => by rw [← map_pow, mixedIntegral_single, weightedCT_pure m hm, zero_div])
  exact singleMixed_formalP_zero_mem

def UniversalGrowthConjecture : Prop := ∀ N M (δ : MvPolynomial (Fin N) ℂ),
  AdmissibleWeight δ → ∀ f : MixedLaurent N M, 0 ∈ mixedNewtonPolytope f →
    0 < Filter.limsup (fun m : ℕ => ‖mixedIntegral δ (f ^ m)‖ ^ ((1 : ℝ) / m)) Filter.atTop

theorem zero_moments_limsup (u : ℕ → ℂ) (hu : ∀ m : ℕ, 1 ≤ m → u m = 0) :
    Filter.limsup (fun m : ℕ => ‖u m‖ ^ ((1 : ℝ) / m)) Filter.atTop = 0 := by
  have he : (fun m : ℕ => ‖u m‖ ^ ((1 : ℝ) / m)) =ᶠ[Filter.atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    rw [hu m hm, norm_zero, Real.zero_rpow (one_div_ne_zero (by exact_mod_cast (show m ≠ 0 by omega)))]
  rw [Filter.limsup_congr he]
  simp

theorem weightedCT_growth_zero :
    Filter.limsup (fun m : ℕ => ‖weightedCT (formalP ^ m)‖ ^ ((1 : ℝ) / m)) Filter.atTop = 0 :=
  zero_moments_limsup _ weightedCT_pure

theorem universal_growth_conjecture_false : ¬ UniversalGrowthConjecture := by
  intro h
  have hp := h 1 1 (MvPolynomial.X 0) coordinate_weight_admissible (singleMixed formalP)
    singleMixed_formalP_zero_mem
  have hz := zero_moments_limsup (fun m => mixedIntegral (MvPolynomial.X 0) (singleMixed formalP ^ m))
    (fun m hm => by rw [← map_pow, mixedIntegral_single, weightedCT_pure m hm, zero_div])
  rw [hz] at hp
  exact lt_irrefl _ hp

end MathieuProperty.Abelian
