import MathieuProperty.CoveringCharts
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! The differential of the covering map is identity in the pulled-back charts. -/

noncomputable section
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CoveringCharts
variable {F X Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace F Y]
  [IsManifold 𝓘(ℝ,F) ∞ Y]
variable (f : X → Y) (hf : IsLocalHomeomorph f)

theorem mfderiv_eq_id (x : X) : letI := chartedSpace (F := F) f hf;
    (show F →L[ℝ] F from mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) f x) = ContinuousLinearMap.id ℝ F := by
  let := chartedSpace (F := F) f hf
  have hd := (contMDiff (F := F) (n := ∞) f hf x).mdifferentiableAt (by simp)
  have hx : chart f hf x x ∈ (chart f hf x).target :=
    (chart f hf x).map_source (mem_chart_source F x)
  have hi := apply_chart_symm_eventually f hf x hx
  have hr := (chartAt F (f x)).eventually_right_inverse hx.1
  have hw : writtenInExtChartAt 𝓘(ℝ,F) 𝓘(ℝ,F) x f =ᶠ[𝓝 (extChartAt 𝓘(ℝ,F) x x)] id := by
    filter_upwards [hi,hr] with v hv hvr
    change chartAt F (f x) (f ((chart f hf x).symm v)) = v
    rw [hv]
    exact hvr
  simpa only [mfderiv, ite_eq_left hd, ModelWithCorners.range_eq_univ,
    fderivWithin_univ, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    using! hw.fderiv_eq.trans (fderiv_id (𝕜 := ℝ))

end MathieuProperty.CoveringCharts
