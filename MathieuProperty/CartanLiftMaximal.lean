import MathieuProperty.CartanCovering

/-! The constructed torus in the original compact group maps onto the Cartan
component and is maximal among connected abelian subgroups. -/

noncomputable section
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CartanLift
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [ConnectedSpace G]
local instance maximalNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance maximalFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [IsTopologicalGroup G]
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)] [T2Space G]

def liftToComponent : Lift (E := E) (G := G) →* CartanStabilizer.Component (Cartan (E := E) (G := G)) :=
  (toComponent (E := E) (G := G)).comp (liftOpen (E := E) (G := G)).toSubgroup.subtype

theorem liftToComponent_localHomeomorph : IsLocalHomeomorph (liftToComponent (E := E) (G := G)) :=
  (toComponent_covering (E := E) (G := G)).isLocalHomeomorph.comp
    (liftOpen (E := E) (G := G)).isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph

theorem liftToComponent_surjective : Function.Surjective (liftToComponent (E := E) (G := G)) := by
  let : IsTopologicalGroup (CartanStabilizer.Component (Cartan (E := E) (G := G))) :=
    topologicalGroup_of_lieGroup 𝓘(ℝ,CartanStabilizer.tangent (Cartan (E := E) (G := G))) ∞
  let f := liftToComponent (E := E) (G := G)
  have ho : IsOpen (f.range : Set (CartanStabilizer.Component (Cartan (E := E) (G := G)))) := by
    simpa only [Set.image_univ] using! (liftToComponent_localHomeomorph (E := E) (G := G)).isOpenMap Set.univ isOpen_univ
  have he : (f.range : Set (CartanStabilizer.Component (Cartan (E := E) (G := G)))) = Set.univ :=
    (show IsClopen (f.range : Set (CartanStabilizer.Component (Cartan (E := E) (G := G)))) from ⟨f.range.isClosed_of_isOpen ho,ho⟩).eq_univ
      ⟨1,f.range.one_mem⟩
  intro y
  have hy : y ∈ (f.range : Set (CartanStabilizer.Component (Cartan (E := E) (G := G)))) := by rw [he]; trivial
  exact hy

omit [T2Space G] in
theorem componentInclusion_toComponent (x : preimage (E := E) (G := G)) :
    CartanStabilizer.componentInclusion (Cartan (E := E) (G := G))
      (toComponent (E := E) (G := G) x) = FullAdjoint.toAutomorphisms (E := E) (G := G) x.val :=
  congrArg Subtype.val ((imageEquiv (E := E) (G := G)).apply_symm_apply (toImage (E := E) (G := G) x))

theorem maximal_connected_abelian (S : Subgroup G) [ConnectedSpace S]
    (hc : ∀ x ∈ S, ∀ y ∈ S, x*y=y*x)
    (hS : (inclusion (E := E) (G := G)).range ≤ S) :
    S = (inclusion (E := E) (G := G)).range := by
  let a := FullAdjoint.toAutomorphisms (E := E) (G := G)
  let j : S →* FullAdjoint.Target (E := E) (G := G) := a.comp S.subtype
  have hj : Continuous j := FullAdjoint.toAutomorphisms_continuous.comp continuous_subtype_val
  let : ConnectedSpace j.range := isConnected_iff_connectedSpace.mp (isConnected_range hj)
  have hjc : ∀ u ∈ j.range, ∀ v ∈ j.range, u*v=v*u := by
    rintro u ⟨x,rfl⟩ v ⟨y,rfl⟩
    exact (map_mul a x.val y.val).symm.trans ((congrArg a (hc _ x.property _ y.property)).trans (map_mul a y.val x.val))
  have hT : CartanStabilizer.componentImage (Cartan (E := E) (G := G)) ≤ j.range := by
    rintro t ⟨z,rfl⟩
    obtain ⟨x,hx⟩ := liftToComponent_surjective (E := E) (G := G) z
    refine ⟨⟨inclusion (E := E) (G := G) x, hS ⟨x,rfl⟩⟩, ?_⟩
    have h := componentInclusion_toComponent (E := E) (G := G) x.val
    change a (inclusion (E := E) (G := G) x) = _
    exact h.symm.trans (congrArg (CartanStabilizer.componentInclusion (Cartan (E := E) (G := G))) hx)
  have he := CartanStabilizer.maximal_connected_abelian (Cartan (E := E) (G := G)) j.range hjc hT
  have hp (s : S) : a s.val ∈ image (E := E) (G := G) := by
    change j s ∈ CartanStabilizer.componentImage (Cartan (E := E) (G := G))
    rw [← he]
    exact ⟨s,rfl⟩
  let k : S → preimage (E := E) (G := G) := fun s => ⟨s.val,hp s⟩
  have hk : Continuous k := continuous_subtype_val.subtype_mk _
  have h1 : (1 : preimage (E := E) (G := G)) ∈ Set.range k := ⟨1,rfl⟩
  have hkC := (isConnected_range hk).subset_connectedComponent h1
  apply le_antisymm _ hS
  intro s hs
  exact ⟨⟨k ⟨s,hs⟩, hkC ⟨⟨s,hs⟩,rfl⟩⟩,rfl⟩

def subgroupEquiv : Lift (E := E) (G := G) ≃ₜ* (inclusion (E := E) (G := G)).range := by
  let f := inclusion (E := E) (G := G)
  have hi : Function.Injective f := inclusion_injective (E := E) (G := G)
  let e := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hi (congrArg (fun z : f.range => z.val) h), f.rangeRestrict_surjective⟩
  have hc : Continuous e := inclusion_continuous.subtype_mk _
  exact { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

omit [IsTopologicalGroup G] in
/-- A maximal torus in the actual compact connected simple Lie group, constructed
without assuming a maximal torus, a closed-subgroup theorem, or root integration. -/
theorem exists_maximal_torus : ∃ T : Subgroup G,
    Nonempty (T ≃ₜ* Torus (Module.finrank ℝ (Cartan (E := E) (G := G)))) ∧
    (∀ S : Subgroup G, ConnectedSpace S → (∀ x ∈ S, ∀ y ∈ S, x*y=y*x) → T ≤ S → S = T) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  refine ⟨(inclusion (E := E) (G := G)).range, ?_, ?_⟩
  · obtain ⟨e⟩ := lift_torus (E := E) (G := G)
    exact ⟨(subgroupEquiv (E := E) (G := G)).symm.trans e⟩
  · intro S hconn hc hT
    let := hconn
    exact maximal_connected_abelian S hc hT

end MathieuProperty.CartanLift
