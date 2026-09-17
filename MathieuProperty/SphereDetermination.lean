import MathieuProperty.SphereMomentRecurrence
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! Mixed coordinate moments determine a finite measure on the complex unit sphere.

Coordinate conjugation completes the phase-cancellation criterion. The span
of coordinate/star-coordinate monomials forms a point-separating star algebra.
Stone–Weierstrass and continuity of integration extend agreement on moments
to every continuous function; regular-measure uniqueness then identifies the
measures. This will be used to prove the Hopf-coordinate measure formula.
-/

noncomputable section
open MeasureTheory
namespace MathieuProperty.Hopf

def conjugateFirstIsometry : EuclideanPair ≃ₗᵢ[ℝ] EuclideanPair :=
  Complex.conjLIE.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℂ)

theorem conjugateFirstIsometry_apply (z : Sphere) :
    (sphereAction conjugateFirstIsometry z).val = (star z.val.1, z.val.2) := rfl

theorem sphereMonomial_integral_zero_of_unbalanced (α β γ δ : ℕ)
    (h : α ≠ β ∨ γ ≠ δ) :
    (∫ z, sphereMonomial α β γ δ z ∂surfaceMeasure) = 0 := by
  by_cases he : α + δ = β + γ
  · have hne : β + δ ≠ α + γ := by omega
    have hp := (surfaceMeasure_preserving conjugateFirstIsometry).integral_comp
      (sphereAction conjugateFirstIsometry).measurableEmbedding (sphereMonomial α β γ δ)
    have heq (z : Sphere) : sphereMonomial α β γ δ (sphereAction conjugateFirstIsometry z) =
        sphereMonomial β α γ δ z := by
      simp only [sphereMonomial, coordinateMonomial, conjugateFirstIsometry_apply, star_star]
      ring
    simp_rw [heq] at hp
    rw [← hp]
    exact sphereMonomial_integral_zero β α γ δ hne
  · exact sphereMonomial_integral_zero α β γ δ he

def monomialMap (v : Fin 4 → ℕ) : C(Sphere, ℂ) :=
  ⟨sphereMonomial (v 0) (v 1) (v 2) (v 3), continuous_sphereMonomial _ _ _ _⟩

theorem monomialMap_zero : monomialMap 0 = 1 := by
  ext z
  simp [monomialMap, sphereMonomial, coordinateMonomial]

theorem monomialMap_add (v w : Fin 4 → ℕ) : monomialMap (v + w) = monomialMap v * monomialMap w := by
  ext z
  simp only [monomialMap, ContinuousMap.coe_mk, sphereMonomial, coordinateMonomial,
    Pi.add_apply, pow_add, ContinuousMap.mul_apply]
  ring

theorem monomialMap_star (v : Fin 4 → ℕ) :
    star (monomialMap v) = monomialMap ![v 1, v 0, v 3, v 2] := by
  ext z
  simp [monomialMap, sphereMonomial, coordinateMonomial, star_mul]
  ring

def sphereMonomialSpan : Submodule ℂ C(Sphere, ℂ) := Submodule.span ℂ (Set.range monomialMap)

theorem monomialMap_mem (v : Fin 4 → ℕ) : monomialMap v ∈ sphereMonomialSpan :=
  Submodule.subset_span (Set.mem_range_self v)

theorem sphereMonomialSpan_mul {f g : C(Sphere, ℂ)}
    (hf : f ∈ sphereMonomialSpan) (hg : g ∈ sphereMonomialSpan) : f * g ∈ sphereMonomialSpan := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      rw [← monomialMap_add]
      exact monomialMap_mem _
    | zero => simp only [mul_zero]; exact sphereMonomialSpan.zero_mem
    | add x y hx hy hx' hy' => simpa only [mul_add] using sphereMonomialSpan.add_mem hx' hy'
    | smul c x hx hx' => simpa only [mul_smul_comm] using sphereMonomialSpan.smul_mem c hx'
  | zero => simp only [zero_mul]; exact sphereMonomialSpan.zero_mem
  | add x y hx hy hx' hy' => simpa only [add_mul] using sphereMonomialSpan.add_mem hx' hy'
  | smul c x hx hx' => simpa only [smul_mul_assoc] using sphereMonomialSpan.smul_mem c hx'

theorem sphereMonomialSpan_star {f : C(Sphere, ℂ)} (hf : f ∈ sphereMonomialSpan) :
    star f ∈ sphereMonomialSpan := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [monomialMap_star]
    exact monomialMap_mem _
  | zero => simp only [star_zero]; exact sphereMonomialSpan.zero_mem
  | add x y hx hy hx' hy' => simpa only [star_add] using sphereMonomialSpan.add_mem hx' hy'
  | smul c x hx hx' => simpa only [star_smul] using sphereMonomialSpan.smul_mem (star c) hx'

def spherePolynomialAlgebra : StarSubalgebra ℂ C(Sphere, ℂ) where
  carrier := sphereMonomialSpan
  zero_mem' := sphereMonomialSpan.zero_mem
  add_mem' := sphereMonomialSpan.add_mem
  mul_mem' := sphereMonomialSpan_mul
  algebraMap_mem' c := by
    have h := sphereMonomialSpan.smul_mem c (monomialMap_mem 0)
    simpa [monomialMap_zero, Algebra.algebraMap_eq_smul_one] using h
  star_mem' := sphereMonomialSpan_star

theorem spherePolynomialAlgebra_separates : spherePolynomialAlgebra.SeparatesPoints := by
  intro x y hxy
  by_cases hx : x.val.1 = y.val.1
  · have hy : x.val.2 ≠ y.val.2 := by
      intro hy
      apply hxy
      exact Subtype.ext (Prod.ext hx hy)
    refine ⟨monomialMap ![0, 0, 1, 0], ⟨_, monomialMap_mem _, rfl⟩, ?_⟩
    simpa [monomialMap, sphereMonomial, coordinateMonomial] using hy
  · refine ⟨monomialMap ![1, 0, 0, 0], ⟨_, monomialMap_mem _, rfl⟩, ?_⟩
    simpa [monomialMap, sphereMonomial, coordinateMonomial] using hx

theorem spherePolynomialAlgebra_dense : spherePolynomialAlgebra.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ spherePolynomialAlgebra_separates

def sphereIntegralLinear (μ : Measure Sphere) [IsFiniteMeasure μ] : C(Sphere, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ z, f z ∂μ
  map_add' f g := integral_add
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_smul' c f := integral_smul c f

def sphereIntegralContinuous (μ : Measure Sphere) [IsFiniteMeasure μ] : C(Sphere, ℂ) →L[ℂ] ℂ :=
  (sphereIntegralLinear μ).mkContinuous (μ.real Set.univ) (fun f => by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall f.norm_coe_le_norm)
    change ‖∫ z, f z ∂μ‖ ≤ μ.real Set.univ * ‖f‖
    simpa only [mul_comm] using h)

theorem sphere_integral_eq_of_monomials (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ α β γ δ : ℕ,
      (∫ z, sphereMonomial α β γ δ z ∂μ) = ∫ z, sphereMonomial α β γ δ z ∂ν)
    (f : C(Sphere, ℂ)) : (∫ z, f z ∂μ) = ∫ z, f z ∂ν := by
  have heq : ∀ g ∈ sphereMonomialSpan, sphereIntegralLinear μ g = sphereIntegralLinear ν g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      exact h _ _ _ _
    | zero => simp
    | add x y hx hy hx' hy' => simp only [map_add, hx', hy']
    | smul c x hx hx' => simp only [map_smul, hx']
  have hc : IsClosed {g : C(Sphere, ℂ) | sphereIntegralContinuous μ g = sphereIntegralContinuous ν g} :=
    isClosed_eq (sphereIntegralContinuous μ).continuous (sphereIntegralContinuous ν).continuous
  have hin : f ∈ closure (spherePolynomialAlgebra : Set C(Sphere, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, spherePolynomialAlgebra_dense]
    trivial
  exact hc.closure_subset_iff.mpr heq hin

theorem sphere_measure_eq_of_monomials (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ α β γ δ : ℕ,
      (∫ z, sphereMonomial α β γ δ z ∂μ) = ∫ z, sphereMonomial α β γ δ z ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hc : Continuous (fun z : Sphere => (f z : ℂ)) := Complex.continuous_ofReal.comp f.continuous
  have hi := sphere_integral_eq_of_monomials μ ν h ⟨_, hc⟩
  change (∫ z, (f z : ℂ) ∂μ) = ∫ z, (f z : ℂ) ∂ν at hi
  rw [integral_complex_ofReal, integral_complex_ofReal] at hi
  exact Complex.ofReal_injective hi

end MathieuProperty.Hopf
