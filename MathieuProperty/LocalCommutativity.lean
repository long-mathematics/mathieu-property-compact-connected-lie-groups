import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Local commutativity forces an abelian identity component.
An open centralizer is clopen and contains the identity component. Applying
this first to elements of the commuting neighborhood and then to elements of
the identity component proves the claim without a Lie-group hypothesis. -/

open scoped Topology
namespace MathieuProperty.LocalCommutativity
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem identity_component_commute {U : Set G} (hU : U ∈ 𝓝 (1 : G))
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    {x y : G} (hx : x ∈ connectedComponent (1 : G))
    (hy : y ∈ connectedComponent (1 : G)) : x * y = y * x := by
  have hc (g : G) (hg : ∀ u ∈ U, g * u = u * g) :
      connectedComponent (1 : G) ⊆ (Subgroup.centralizer {g} : Set G) := by
    have hn : (Subgroup.centralizer {g} : Set G) ∈ 𝓝 (1 : G) := by
      apply Filter.mem_of_superset hU
      intro u hu
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hg u hu).symm
    have ho := (Subgroup.centralizer {g}).isOpen_of_mem_nhds hn
    exact (show IsClopen (Subgroup.centralizer {g} : Set G) from
      ⟨(Subgroup.centralizer {g}).isClosed_of_isOpen ho, ho⟩).connectedComponent_subset
        (Subgroup.centralizer {g}).one_mem
  have hxu (u : G) (hu : u ∈ U) : x * u = u * x :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hc u (hcomm u hu) hx))
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hc x hxu hy)).symm

end MathieuProperty.LocalCommutativity
