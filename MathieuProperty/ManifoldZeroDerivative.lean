import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.MeanValue
/-! A zero differential forces local constancy on real manifolds.
The local proof passes to chart coordinates and uses the normed-space mean
value theorem on a ball. A second chart handles manifold-valued maps. The
connected-domain consequence requires no group or compactness hypothesis.
-/
noncomputable section
open Set Filter
open scoped Manifold Topology
namespace MathieuProperty
namespace ManifoldZeroDerivative
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) 1 M]

set_option backward.isDefEq.respectTransparency false in
theorem eventually_eq_of_mfderiv_zero {f : M → F} (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f y ∧
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y = 0) : ∀ᶠ y in 𝓝 x, f y = f x := by
  let c := extChartAt 𝓘(ℝ,E) x
  let a₀ := c x
  let u := f ∘ c.symm
  have hx : x ∈ c.source := mem_extChartAt_source x
  have ha₀ : a₀ ∈ c.target := c.map_source hx
  have hcx : c.symm a₀ = x := c.left_inv hx
  have hi (a : E) (ha : a ∈ c.target) : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) c.symm a := by
    rw [← mdifferentiableWithinAt_univ]
    simpa [c] using mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ,E)) ha
  have ht : Tendsto c.symm (𝓝 a₀) (𝓝 x) := by
    simpa only [hcx] using (hi a₀ ha₀).continuousAt.tendsto
  have hgood : ∀ᶠ a in 𝓝 a₀, a ∈ c.target ∧
      (MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f (c.symm a) ∧
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f (c.symm a) = 0) :=
    by
      filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ,E)) x, ht.eventually hf] with a ha hb
      exact ⟨ha,hb⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hu (a : E) (ha : a ∈ Metric.ball a₀ r) :
      DifferentiableAt ℝ u a ∧ fderiv ℝ u a = 0 := by
    obtain ⟨hca,hfa,hza⟩ := hball ha
    refine ⟨(hfa.comp a (hi a hca)).differentiableAt, ?_⟩
    have hd := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,F)) a hfa (hi a hca)
    rw [hza, ContinuousLinearMap.zero_comp] at hd
    simpa only [mfderiv_eq_fderiv] using! hd
  have heq (a : E) (ha : a ∈ Metric.ball a₀ r) : u a = u a₀ := by
    apply (convex_ball a₀ r).is_const_of_fderivWithin_eq_zero
      (fun b hb => (hu b hb).1.differentiableWithinAt) _ ha (Metric.mem_ball_self hr)
    intro b hb
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hb]
    exact (hu b hb).2
  have hc : ContinuousAt c x := (contMDiffAt_extChartAt (I := 𝓘(ℝ,E)) (x := x) (n := 1)).continuousAt
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ,E)) x,
    hc.preimage_mem_nhds (Metric.ball_mem_nhds a₀ hr)] with y hy hby
  have h := heq (c y) hby
  simpa only [u, Function.comp_apply, c.left_inv hy, hcx] using h

theorem isLocallyConstant_of_mfderiv_zero {f : M → F}
    (hf : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,F) f)
    (hz : ∀ x, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x = 0) : IsLocallyConstant f :=
  (IsLocallyConstant.iff_eventually_eq f).mpr fun x => eventually_eq_of_mfderiv_zero x
    (Eventually.of_forall fun y => ⟨hf y,hz y⟩)

section ManifoldTarget
variable {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) 1 N]
set_option backward.isDefEq.respectTransparency false in
theorem eventually_eq_of_mfderiv_zero_manifold {f : M → N} (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f y ∧
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y = 0) : ∀ᶠ y in 𝓝 x, f y = f x := by
  let d := extChartAt 𝓘(ℝ,F) (f x)
  have hx := hf.self_of_nhds
  have hn : ∀ᶠ y in 𝓝 x, f y ∈ d.source :=
    hx.1.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ,F)) (f x))
  have hc : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) (d ∘ f) y ∧
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (d ∘ f) y = 0 := by
    filter_upwards [hf,hn] with y hfy hy
    have hd : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,F) d (f y) :=
      (contMDiffAt_extChartAt' (I := 𝓘(ℝ,F)) (n := 1) (by simpa [d] using hy)).mdifferentiableAt one_ne_zero
    refine ⟨hd.comp y hfy.1, ?_⟩
    rw [mfderiv_comp (I' := 𝓘(ℝ,F)) y hd hfy.1, hfy.2, ContinuousLinearMap.comp_zero]
  have he := eventually_eq_of_mfderiv_zero (E := E) (F := F) x hc
  filter_upwards [hn,he] with y hy hxy
  exact d.injOn hy (mem_extChartAt_source (f x)) hxy

theorem isLocallyConstant_of_mfderiv_zero_manifold {f : M → N}
    (hf : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,F) f)
    (hz : ∀ x, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x = 0) : IsLocallyConstant f :=
  (IsLocallyConstant.iff_eventually_eq f).mpr fun x => eventually_eq_of_mfderiv_zero_manifold x
    (Eventually.of_forall fun y => ⟨hf y,hz y⟩)

theorem eq_of_mfderiv_zero [PreconnectedSpace M] {f : M → N}
    (hf : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,F) f)
    (hz : ∀ x, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x = 0) (x y : M) : f x = f y :=
  (isLocallyConstant_of_mfderiv_zero_manifold hf hz).apply_eq_of_preconnectedSpace x y
end ManifoldTarget
end ManifoldZeroDerivative
end MathieuProperty
