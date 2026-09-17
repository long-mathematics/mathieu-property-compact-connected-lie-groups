import MathieuProperty.LieSurjective
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! An injective differential isolates the point in its fiber.
Finite-dimensional injective linear maps are bounded below. The corresponding
punctured-neighborhood derivative estimate transfers through manifold charts.
This is a local fiber statement, not a closed-subgroup theorem. -/

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace MathieuProperty.DiscreteFibers
variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
set_option backward.isDefEq.respectTransparency false in
/-- Near a point with injective differential, its fiber contains only that point. -/
theorem fiber_isolated {f : M → N} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f x)
    (hi : Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) :
    ∀ᶠ y in 𝓝 x, f y = f x → y = x := by
  let c := extChartAt 𝓘(ℝ,E) x
  let d := extChartAt 𝓘(ℝ,F) (f x)
  let u := d ∘ f ∘ c.symm
  let a := c x
  have hc : c.symm a = x := c.left_inv (mem_extChartAt_source x)
  have hu : DifferentiableAt ℝ u a := by
    simpa [u, a, c, d, DifferentiableWithinAtProp_self, differentiableWithinAt_univ] using hf.2
  have hd : Function.Injective (fderiv ℝ u a) := by
    simpa [mfderiv, hf, writtenInExtChartAt, u, a, c, d] using! hi
  have hl := (fderiv ℝ u a).antilipschitz_of_injective_of_isClosed_range hd
    (Submodule.closed_of_finiteDimensional (fderiv ℝ u a).range)
  have hn : ∀ᶠ z in 𝓝[≠] a, u z ≠ u a := hu.hasFDerivAt.eventually_ne hl
  rw [eventually_nhdsWithin_iff] at hn
  have hnear : ∀ᶠ z in 𝓝 a, u z = u a → z = a := by
    filter_upwards [hn] with z hz he
    by_contra hza
    exact hz hza he
  have hcc : ContinuousAt c x := (contMDiffAt_extChartAt (I := 𝓘(ℝ,E))
    (x := x) (n := 1)).continuousAt
  filter_upwards [hcc.preimage_mem_nhds hnear, extChartAt_source_mem_nhds (I := 𝓘(ℝ,E)) x]
    with y hy hys
  intro he
  apply c.injOn hys (mem_extChartAt_source x)
  apply hy
  simp only [u, Function.comp_apply, c.left_inv hys, hc, he]

end MathieuProperty.DiscreteFibers
