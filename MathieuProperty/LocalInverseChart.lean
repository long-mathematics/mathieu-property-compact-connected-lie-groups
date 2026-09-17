import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
/-! A local chart from continuous maps that are inverse near the base point. -/

noncomputable section
open scoped Topology
namespace MathieuProperty
namespace LocalInverseChart
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
def ofNeighborhoods (f : X → Y) (g : Y → X) (U : Set X) (V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (hgf : ∀ x ∈ U, g (f x) = x) (hfg : ∀ y ∈ V, f (g y) = y) :
    OpenPartialHomeomorph X Y where
  toFun := f
  invFun := g
  source := U ∩ f ⁻¹' V
  target := V ∩ g ⁻¹' U
  map_source' x hx := ⟨hx.2, by change g (f x) ∈ U; rw [hgf x hx.1]; exact hx.1⟩
  map_target' y hy := ⟨hy.2, by change f (g y) ∈ V; rw [hfg y hy.1]; exact hy.1⟩
  left_inv' x hx := hgf x hx.1
  right_inv' y hy := hfg y hy.1
  open_source := hf.isOpen_inter_preimage hU hV
  open_target := hg.isOpen_inter_preimage hV hU
  continuousOn_toFun := hf.mono Set.inter_subset_left
  continuousOn_invFun := hg.mono Set.inter_subset_left

theorem exists_of_eventually_inverse (f : X → Y) (g : Y → X) (a : X)
    (U : Set X) (hU : U ∈ 𝓝 a) (hf : ContinuousOn f U) (hg : Continuous g)
    (hgf : ∀ᶠ x in 𝓝 a, g (f x) = x) (hfg : ∀ᶠ y in 𝓝 (f a), f (g y) = y) :
    ∃ e : OpenPartialHomeomorph X Y, a ∈ e.source ∧ (e : X → Y) = f ∧
      (e.symm : Y → X) = g := by
  obtain ⟨u, hu, huo, hau⟩ := mem_nhds_iff.mp (Filter.inter_mem hU hgf)
  obtain ⟨v, hv, hvo, hav⟩ := mem_nhds_iff.mp hfg
  let e := ofNeighborhoods f g u v huo hvo
    (hf.mono fun x hx => (hu hx).1) hg.continuousOn
    (fun x hx => (hu hx).2) (fun y hy => hv hy)
  exact ⟨e, ⟨hau, hav⟩, rfl, rfl⟩
end LocalInverseChart
end MathieuProperty
