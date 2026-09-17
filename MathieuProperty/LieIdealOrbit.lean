import Mathlib.Algebra.Lie.Abelian
import Mathlib.Order.Atoms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.LocallyConstant.Basic
/-! Connected continuous families of finite-dimensional Lie automorphisms
cannot move an atomic ideal in a finite family of atoms. The orbit map has
closed fibers, hence is locally constant with finite discrete codomain. -/

noncomputable section
open Set
namespace MathieuProperty
namespace LieIdealOrbit
variable {R L M : Type*} [CommRing R] [LieRing L] [LieRing M]
  [LieAlgebra R L] [LieAlgebra R M]
/-- Transport of ideals under a Lie algebra equivalence. -/
def idealOrderIso (e : L ≃ₗ⁅R⁆ M) : LieIdeal R L ≃o LieIdeal R M where
  toFun I := I.comap e.symm.toLieHom
  invFun J := J.comap e.toLieHom
  left_inv I := by ext x; simp
  right_inv J := by ext x; simp
  map_rel_iff' := by
    intro I J
    constructor
    · intro h x hx
      have := h (show e x ∈ I.comap e.symm.toLieHom by simpa using hx)
      simpa using this
    · intro h x hx
      exact h hx

theorem mem_idealOrderIso (e : L ≃ₗ⁅R⁆ M) (I : LieIdeal R L) (x : L) :
    e x ∈ idealOrderIso e I ↔ x ∈ I := by
  change e.symm (e x) ∈ I ↔ _
  simp

theorem equiv_mem_center (e : L ≃ₗ⁅R⁆ M) {v : L}
    (hv : v ∈ LieAlgebra.center R L) : e v ∈ LieAlgebra.center R M := by
  apply (LieModule.mem_maxTrivSubmodule R M M (e v)).mpr
  intro z
  obtain ⟨y,rfl⟩ := e.surjective z
  change ⁅e y,e v⁆ = 0
  rw [← e.map_lie, (LieModule.mem_maxTrivSubmodule R L L v).mp hv y, map_zero]

section Topology
variable {X ι : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Finite ι]
theorem eq_of_closed_fibers (f : X → ι) (hf : ∀ i, IsClosed {x | f x = i}) (x y : X) : f x = f y := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  have hc : Continuous f := continuous_iff_isClosed.mpr fun s _ => by
    have he : f ⁻¹' s = ⋃ i : s, {x | f x = i.val} := by ext x; simp
    rw [he]
    exact isClosed_iUnion_of_finite fun i => hf i.val
  exact ((IsLocallyConstant.iff_continuous f).mpr hc).apply_eq_of_preconnectedSpace x y
end Topology
section FiniteAtoms
variable {V X : Type*} [LieRing V] [LieAlgebra ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
  [TopologicalSpace X] [PreconnectedSpace X]
/-- A connected continuous family acts constantly on a finite atomic-ideal set. -/
theorem atom_image_eq (e : X → V ≃ₗ⁅ℝ⁆ V) (he : ∀ v, Continuous (fun x => e x v))
    (hfin : Set.Finite {I : LieIdeal ℝ V | IsAtom I}) (I : LieIdeal ℝ V) (hI : IsAtom I)
    (x y : X) : idealOrderIso (e x) I = idealOrderIso (e y) I := by
  let A := {J : LieIdeal ℝ V // IsAtom J}
  let : Finite A := hfin.to_subtype
  let f : X → A := fun x => ⟨idealOrderIso (e x) I, ((idealOrderIso (e x)).isAtom_iff I).mpr hI⟩
  have hf : ∀ J : A, IsClosed {x | f x = J} := by
    intro J
    have heq : {x | f x = J} = ⋂ v : I, {x | e x v.val ∈ J.val} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h v
        have hv := (mem_idealOrderIso (e x) I v.val).mpr v.property
        change e x v.val ∈ (f x).val at hv
        rw [h] at hv
        exact hv
      · intro h
        apply Subtype.ext
        apply (J.property.le_iff_eq (f x).property.ne_bot).mp
        intro v hv
        have hw : (e x).symm v ∈ I := hv
        simpa using h ⟨(e x).symm v,hw⟩
    rw [heq]
    exact isClosed_iInter fun v => J.val.toSubmodule.closed_of_finiteDimensional.preimage (he v.val)
  exact congrArg Subtype.val (eq_of_closed_fibers f hf x y)
end FiniteAtoms
end LieIdealOrbit
end MathieuProperty
