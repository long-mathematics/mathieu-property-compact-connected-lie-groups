import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen
/-! A surjective differential gives local openness in real Banach manifold
charts. Consequently a homomorphism that is C¹ at the identity, with surjective
differential there, is surjective onto a connected topological group.
This avoids invoking a closed-subgroup theorem for the surjectivity step. -/

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace MathieuProperty
namespace LieSurjective
variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
set_option backward.isDefEq.respectTransparency false in
/-- The image contains a neighborhood of the image point when the derivative is onto. -/
theorem range_mem_nhds_of_surjective_mfderiv {f : M → N} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f x)
    (hs : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) : range f ∈ 𝓝 (f x) := by
  let c := extChartAt 𝓘(ℝ,E) x
  let d := extChartAt 𝓘(ℝ,F) (f x)
  let u := d ∘ f ∘ c.symm
  let a := c x
  have hc : c.symm a = x := c.left_inv (mem_extChartAt_source x)
  have hu : ContDiffAt ℝ 1 u a := by
    rw [← contDiffWithinAt_univ]
    simpa [u,a,c,d] using (contMDiffAt_iff.mp hf).2
  have hd : Function.Surjective (fderiv ℝ u a) := by
    simpa [mfderiv, hf.mdifferentiableAt one_ne_zero, writtenInExtChartAt, u,a,c,d] using! hs
  have hm := (hu.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr hd)
  have hui : u a = d (f x) := by simp [u,Function.comp_def,hc]
  rw [hui] at hm
  have hci : ContinuousAt c.symm a := by
    exact continuousAt_extChartAt_symm x
  have hfi : ContinuousAt (f ∘ c.symm) a := hf.continuousAt.comp_of_eq hci hc
  have hn : ∀ᶠ z in 𝓝 a, f (c.symm z) ∈ d.source :=
    hfi.preimage_mem_nhds (by simpa only [Function.comp_apply,hc] using
      extChartAt_source_mem_nhds (I := 𝓘(ℝ,F)) (f x))
  have hr : d.symm ⁻¹' range f ∈ 𝓝 (d (f x)) := by
    rw [← hm]
    change ∀ᶠ z in 𝓝 a, d.symm (u z) ∈ range f
    filter_upwards [hn] with z hz
    exact ⟨c.symm z, (d.left_inv hz).symm⟩
  have hdc : ContinuousAt d (f x) :=
    (contMDiffAt_extChartAt (I := 𝓘(ℝ,F)) (x := f x) (n := 1)).continuousAt
  filter_upwards [hdc.preimage_mem_nhds hr,
    extChartAt_source_mem_nhds (I := 𝓘(ℝ,F)) (f x)] with y hy hys
  simpa only [mem_preimage, d.left_inv hys] using hy
section Homomorphism
variable [Group M] [Group N] [IsTopologicalGroup N] [PreconnectedSpace N]
/-- A C¹ homomorphism with surjective differential is onto a connected target. -/
theorem surjective_of_surjective_mfderiv (f : M →* N)
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f 1)
    (hs : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1)) : Function.Surjective f := by
  have hn : (f.range : Set N) ∈ 𝓝 (1 : N) := by
    simpa using range_mem_nhds_of_surjective_mfderiv hf hs
  have ho : IsOpen (f.range : Set N) := f.range.isOpen_of_mem_nhds hn
  have he : (f.range : Set N) = univ :=
    (show IsClopen (f.range : Set N) from ⟨f.range.isClosed_of_isOpen ho,ho⟩).eq_univ
      ⟨1,f.range.one_mem⟩
  intro y
  have hy : y ∈ (f.range : Set N) := by rw [he]; trivial
  exact hy
end Homomorphism
end LieSurjective
end MathieuProperty
