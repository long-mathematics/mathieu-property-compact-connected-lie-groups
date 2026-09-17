import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! Pull back smooth charts along a local homeomorphism to a real manifold.
The resulting atlas makes the map smooth. A covering homomorphism into a Lie
group then gives its topological source group a Lie-group structure. -/

noncomputable section
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CoveringCharts
variable {F X Y : Type*} [NormedAddCommGroup F]
  [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace F Y]
variable (f : X → Y) (hf : IsLocalHomeomorph f)

def chart (x : X) : OpenPartialHomeomorph X F :=
  (hf.localInverseAt x).symm.trans (chartAt F (f x))

theorem chart_apply (x z : X) : chart f hf x z = chartAt F (f x) (f z) := by
  simp only [chart, OpenPartialHomeomorph.trans_apply, hf.localInverseAt_symm]

theorem chart_symm_apply (x : X) (v : F) :
    (chart f hf x).symm v = hf.localInverseAt x ((chartAt F (f x)).symm v) := rfl

@[instance_reducible]
def chartedSpace : ChartedSpace F X where
  atlas := Set.range (chart f hf)
  chartAt := chart f hf
  mem_chart_source x := by
    refine ⟨hf.self_mem_localInverseAt_target, ?_⟩
    change (hf.localInverseAt x).symm x ∈ (chartAt F (f x)).source
    simpa only [hf.localInverseAt_symm] using mem_chart_source F (f x)
  chart_mem_atlas x := ⟨x,rfl⟩

theorem apply_chart_symm (x : X) {v : F} (hv : v ∈ (chart f hf x).target) :
    f ((chart f hf x).symm v) = (chartAt F (f x)).symm v :=
  hf.apply_localInverseAt_of_mem hv.2

theorem apply_chart_symm_eventually (x : X) {v : F} (hv : v ∈ (chart f hf x).target) :
    (fun w => f ((chart f hf x).symm w)) =ᶠ[𝓝 v] (chartAt F (f x)).symm := by
  filter_upwards [(chart f hf x).open_target.mem_nhds hv] with w hw
  exact apply_chart_symm f hf x hw

variable [NormedSpace ℝ F]
variable {n : ℕ∞ω} [IsManifold 𝓘(ℝ,F) n Y]

theorem isManifold : letI := chartedSpace (F := F) f hf; IsManifold 𝓘(ℝ,F) n X := by
  let := chartedSpace (F := F) f hf
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x,rfl⟩ ⟨y,rfl⟩ v hv
  have hx : v ∈ (chart f hf x).target := hv.1.1
  have hy : (chart f hf x).symm v ∈ (chart f hf y).source := hv.1.2
  have hxN : v ∈ (chartAt F (f x)).target := hx.1
  have hyN : (chartAt F (f x)).symm v ∈ (chartAt F (f y)).source := by
    rw [← apply_chart_symm f hf x hx]
    have hh := hy.2
    change (hf.localInverseAt y).symm ((chart f hf x).symm v) ∈ (chartAt F (f y)).source at hh
    rwa [hf.localInverseAt_symm] at hh
  have ha := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,F))
    (IsManifold.chart_mem_maximalAtlas (n := n) (f x)) hxN
  have hb := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,F))
    (IsManifold.chart_mem_maximalAtlas (n := n) (f y)) hyN
  have hc : ContDiffAt ℝ n (fun w => chartAt F (f y) ((chartAt F (f x)).symm w)) v := by
    exact contMDiffAt_iff_contDiffAt.mp (hb.comp v ha)
  have he : (fun w => chart f hf y ((chart f hf x).symm w)) =ᶠ[𝓝 v]
      (fun w => chartAt F (f y) ((chartAt F (f x)).symm w)) := by
    filter_upwards [apply_chart_symm_eventually f hf x hx] with w hw
    rw [chart_apply, hw]
  simpa only [Function.comp_def, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    id_eq, OpenPartialHomeomorph.trans_apply] using (hc.congr_of_eventuallyEq he).contDiffWithinAt

theorem contMDiff : letI := chartedSpace (F := F) f hf;
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) n f := by
  let := chartedSpace (F := F) f hf
  intro x
  rw [contMDiffAt_iff_source]
  have hx : chart f hf x x ∈ (chart f hf x).target :=
    (chart f hf x).map_source (mem_chart_source F x)
  have ha := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,F))
    (IsManifold.chart_mem_maximalAtlas (n := n) (f x)) hx.1
  have he := apply_chart_symm_eventually f hf x hx
  exact (ha.congr_of_eventuallyEq he).contMDiffWithinAt

variable {D H M : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [TopologicalSpace H] (I : ModelWithCorners ℝ D H)
  [TopologicalSpace M] [ChartedSpace H M]

omit [IsManifold 𝓘(ℝ,F) n Y] in
theorem contMDiffAt_of_comp {g : M → X} {x : M} (hg : ContinuousAt g x)
    (hfg : ContMDiffAt I 𝓘(ℝ,F) n (f ∘ g) x) :
    letI := chartedSpace (F := F) f hf; ContMDiffAt I 𝓘(ℝ,F) n g x := by
  let := chartedSpace (F := F) f hf
  apply contMDiffAt_iff_target.mpr
  refine ⟨hg, ?_⟩
  have ht := (contMDiffAt_iff_target.mp hfg).2
  convert ht using 1
  ext z
  exact chart_apply f hf (g x) (g z)

end MathieuProperty.CoveringCharts

namespace MathieuProperty.CoveringCharts
variable {F X Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [Group Y] [TopologicalSpace Y] [ChartedSpace F Y]
  {n : ℕ∞ω} [LieGroup 𝓘(ℝ,F) n Y]
variable (f : X →* Y) (hf : IsLocalHomeomorph f)

theorem lieGroup : letI := chartedSpace (F := F) f hf; LieGroup 𝓘(ℝ,F) n X := by
  let := chartedSpace (F := F) f hf
  let := isManifold (F := F) (n := n) f hf
  have hs : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,F) n f := contMDiff f hf
  refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · intro p
    apply contMDiffAt_of_comp f hf _ continuous_mul.continuousAt
    simpa only [Function.comp_def, map_mul, Pi.mul_apply] using!
      ((hs.comp contMDiff_fst).mul (hs.comp contMDiff_snd)) p
  · intro x
    apply contMDiffAt_of_comp f hf _ continuous_inv.continuousAt
    simpa only [Function.comp_def, map_inv] using hs.inv x

end MathieuProperty.CoveringCharts
