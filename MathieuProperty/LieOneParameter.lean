import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
/-! Continuous one-parameter subgroups with prescribed tangent vector.
Local integral curves for the left-invariant field have uniform existence time
by translation. Mathlib's uniform-time theorem extends them globally, and
uniqueness gives the homomorphism law. The curve is C¹ in manifold charts and
has the prescribed differential at zero. -/

noncomputable section
open scoped Manifold ContDiff Topology
open Set Filter
namespace MathieuProperty
namespace LieOneParameter
set_option backward.isDefEq.respectTransparency false
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
local instance parameterSmoothness : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)

abbrev field (v : GroupLieAlgebra 𝓘(ℝ,E) G) (g : G) := mulInvariantVectorField v g

omit [CompleteSpace E] [T2Space G] in
theorem field_smooth (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E).tangent 1
      (fun g : G => (⟨g,field v g⟩ : TangentBundle 𝓘(ℝ,E) G)) := by
  exact (contMDiff_mulInvariantVectorField v).of_le (by simp)

omit [CompleteSpace E] [T2Space G] in
theorem translate_field (v : GroupLieAlgebra 𝓘(ℝ,E) G) (g h : G) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x) h (field v h) = field v (g*h) := by
  have hd := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E))
    (f := fun x : G => h*x) (g := fun x : G => g*x) (1 : G)
    (contMDiff_mul_left.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp))
    (contMDiff_mul_left.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp))
  dsimp only [Function.comp_def] at hd
  rw [mul_one,show (fun x : G => g*(h*x)) = (fun x : G => (g*h)*x) from
    funext (fun x => (mul_assoc g h x).symm)] at hd
  exact (congrArg (fun D : E →L[ℝ] E => D v) hd).symm


omit [CompleteSpace E] [T2Space G] in
theorem curve_translate (v : GroupLieAlgebra 𝓘(ℝ,E) G) {γ : ℝ → G} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (field v) s) (g : G) :
    IsMIntegralCurveOn (fun t => g*γ t) (field v) s := by
  intro t ht
  have hl : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : G => g*x) := contMDiff_mul_left
  have hd := (hl.mdifferentiableAt
    (show (∞ : ℕ∞ω) ≠ 0 by simp)).hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)
  have he : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x) (γ t)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (field v (γ t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (field v (g*γ t)) := by
    apply ContinuousLinearMap.ext
    intro r
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
    rw [map_smul,translate_field]
  exact he ▸ hd

theorem exists_global_curve (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    ∃ γ : ℝ → G, γ 0 = 1 ∧ IsMIntegralCurve γ (field v) := by
  obtain ⟨γ,h0,hγ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (I := 𝓘(ℝ,E)) (x₀ := (1 : G)) 0 ((field_smooth v) 1)
  obtain ⟨ε,hε,hεγ⟩ := isMIntegralCurveAt_iff'.mp hγ
  have hlocal : IsMIntegralCurveOn γ (field v) (Ioo (-ε) ε) := by
    simpa only [Real.ball_eq_Ioo,zero_sub,zero_add] using hεγ
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn (field_smooth v) hε _ (1 : G)
  intro g
  exact ⟨fun t => g*γ t,by simp [h0],curve_translate v hlocal g⟩


/-- The integral curve of the left-invariant vector field starting at the identity. -/
def curve (v : GroupLieAlgebra 𝓘(ℝ,E) G) : ℝ → G :=
  (exists_global_curve v).choose

theorem curve_zero (v : GroupLieAlgebra 𝓘(ℝ,E) G) : curve v 0 = 1 :=
  (exists_global_curve v).choose_spec.1

theorem curve_integral (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    IsMIntegralCurve (curve v) (field v) :=
  (exists_global_curve v).choose_spec.2

theorem curve_continuous (v : GroupLieAlgebra 𝓘(ℝ,E) G) : Continuous (curve v) :=
  (curve_integral v).continuous

theorem curve_add (v : GroupLieAlgebra 𝓘(ℝ,E) G) (a b : ℝ) :
    curve v (a+b) = curve v a * curve v b := by
  have ht : IsMIntegralCurve (fun t => curve v a * curve v t) (field v) :=
    isMIntegralCurve_iff_isMIntegralCurveOn.mpr
      (curve_translate v ((curve_integral v).isMIntegralCurveOn univ) (curve v a))
  have hs := (curve_integral v).comp_add a
  have he : (curve v ∘ (fun t : ℝ => t+a)) 0 = (fun t => curve v a * curve v t) 0 := by
    simp [curve_zero]
  have hfun := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (field_smooth v) hs ht he
  simpa only [Function.comp_apply,add_comm] using congrFun hfun b

/-- Every tangent vector generates a continuous one-parameter subgroup. -/
def hom (v : GroupLieAlgebra 𝓘(ℝ,E) G) : Multiplicative ℝ →* G where
  toFun t := curve v t.toAdd
  map_one' := curve_zero v
  map_mul' a b := curve_add v a.toAdd b.toAdd

theorem hom_continuous (v : GroupLieAlgebra 𝓘(ℝ,E) G) : Continuous (hom v) :=
  curve_continuous v

omit [CompleteSpace E] [T2Space G] [LieGroup 𝓘(ℝ,E) ∞ G] in
theorem field_one (v : GroupLieAlgebra 𝓘(ℝ,E) G) : field v (1 : G) = v := by
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => 1*x) 1 v = v
  rw [show (fun x : G => 1*x) = id from funext one_mul, mfderiv_id]
  rfl

theorem curve_mfderiv_zero (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    (show ℝ →L[ℝ] E from mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (curve v) 0) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (show E from v) := by
  have h := (curve_integral v 0).mfderiv
  calc
    _ = (1 : ℝ →L[ℝ] ℝ).smulRight (show E from field v (curve v 0)) := h
    _ = _ := by
      congr 1
      rw [curve_zero]
      exact field_one v


/-- The generated one-parameter subgroup is continuously differentiable. -/
theorem curve_contMDiff_one (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 (curve v) := by
  intro t₀
  let Vt : ℝ → TangentBundle 𝓘(ℝ,E) G := fun t => ⟨curve v t,field v (curve v t)⟩
  let c := chartAt (ModelProd E E) (Vt t₀)
  let F : ℝ → E := fun t => (c (Vt t)).2
  let s : Set ℝ := Vt ⁻¹' c.source
  have hV : Continuous Vt := (field_smooth v).continuous.comp (curve_continuous v)
  have hs : s ∈ 𝓝 t₀ := hV.continuousAt.preimage_mem_nhds
    (c.open_source.mem_nhds (mem_chart_source _ _))
  have hF : ContinuousOn F s := (c.continuousOn.comp hV.continuousOn (fun _ h => h)).snd
  have hd := ((curve_integral v).isMIntegralCurveAt t₀).eventually_hasDerivAt
  change ∀ᶠ t in 𝓝 t₀, HasDerivAt (extChartAt 𝓘(ℝ,E) (curve v t₀) ∘ curve v) (F t) t at hd
  obtain ⟨u,hu,hud⟩ := hd.exists_mem
  have hc : ContDiffAt ℝ 1 (extChartAt 𝓘(ℝ,E) (curve v t₀) ∘ curve v) t₀ := by
    apply contDiffAt_one_iff.mpr
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (F t), s ∩ u, inter_mem hs hu, ?_, ?_⟩
    · exact (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous.comp_continuousOn
        (hF.mono inter_subset_left)
    · intro t ht
      exact (hud t ht.2).hasFDerivAt
  exact contMDiffAt_iff_target.mpr ⟨(curve_continuous v).continuousAt,hc.contMDiffAt⟩

end LieOneParameter
end MathieuProperty
