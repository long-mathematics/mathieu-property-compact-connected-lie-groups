import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! A continuous map is smooth locally if its composition with a smooth map
with invertible differential is smooth. This is the inverse function theorem
in finite-dimensional manifold charts, without assuming a smooth inverse. -/

noncomputable section
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.SmoothLift
variable {E F D H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace H]
  (I : ModelWithCorners ℝ D H) [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω}

theorem of_comp {f : E → F} {g : M → E} {x : M} {e : E ≃L[ℝ] F}
    (hn : n ≠ 0) (hf : ContDiffAt ℝ n f (g x)) (hd : HasFDerivAt f (e : E →L[ℝ] F) (g x))
    (hg : ContinuousAt g x) (hfg : ContMDiffAt I 𝓘(ℝ,F) n (f ∘ g) x) :
    ContMDiffAt I 𝓘(ℝ,E) n g x := by
  have hi := contMDiffAt_iff_contDiffAt.mpr (hf.to_localInverse hd hn)
  have hs := hi.comp x hfg
  have he := (hf.toOpenPartialHomeomorph f hd hn).eventually_left_inverse
    (hf.mem_toOpenPartialHomeomorph_source hd hn)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hg.eventually he] with z hz
  exact hz.symm

variable {N P : Type*} [TopologicalSpace N] [ChartedSpace E N]
  [TopologicalSpace P] [ChartedSpace F P]

theorem manifold_of_comp {f : N → P} {g : M → N} {x : M}
    (hn : n ≠ 0) (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) n f (g x))
    (e : E ≃L[ℝ] F) (hd : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f (g x) = (e : E →L[ℝ] F))
    (hg : ContinuousAt g x) (hfg : ContMDiffAt I 𝓘(ℝ,F) n (f ∘ g) x) :
    ContMDiffAt I 𝓘(ℝ,E) n g x := by
  let c := extChartAt 𝓘(ℝ,E) (g x)
  let d := extChartAt 𝓘(ℝ,F) (f (g x))
  let u := d ∘ f ∘ c.symm
  have hc : ContinuousAt (c ∘ g) x := (continuousAt_extChartAt _).comp hg
  have hu : ContDiffAt ℝ n u (c (g x)) := by
    simpa [u,c,d,contDiffWithinAt_univ] using (contMDiffAt_iff.mp hf).2
  have hdu : HasFDerivAt u (e : E →L[ℝ] F) (c (g x)) := by
    have he : fderiv ℝ u (c (g x)) = (e : E →L[ℝ] F) := by
      simpa [mfderiv, hf.mdifferentiableAt hn, writtenInExtChartAt,u,c,d] using! hd
    rw [← he]
    exact (hu.differentiableAt hn).hasFDerivAt
  have ht : ContMDiffAt I 𝓘(ℝ,F) n (d ∘ f ∘ g) x :=
    (contMDiffAt_iff_target.mp hfg).2
  have heq : (d ∘ f ∘ g) =ᶠ[𝓝 x] (u ∘ (c ∘ g)) := by
    filter_upwards [hg.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ,E)) (g x))] with z hz
    simp only [Function.comp_apply,u,c]
    rw [(extChartAt 𝓘(ℝ,E) (g x)).left_inv hz]
  apply contMDiffAt_iff_target.mpr
  refine ⟨hg, ?_⟩
  exact of_comp I hn hu hdu hc (ht.congr_of_eventuallyEq heq.symm)

end MathieuProperty.SmoothLift
