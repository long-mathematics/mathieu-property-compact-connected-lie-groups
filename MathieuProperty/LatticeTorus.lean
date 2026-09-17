import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.ContinuousMonoidHom
/-! A full integer lattice is the kernel of a continuous surjective map to a
finite product of circles. The map sends coordinates in a lattice basis to the
unit additive circle and then to the usual complex unit circle. -/

noncomputable section
open Module Set
namespace MathieuProperty
namespace LatticeTorus
set_option backward.isDefEq.respectTransparency false
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)

def map : Multiplicative E →* (ι → Circle) where
  toFun x i := AddCircle.toCircle ((b.ofZLatticeBasis ℝ L).equivFun x.toAdd i : AddCircle (1 : ℝ))
  map_one' := by ext i; simp
  map_mul' x y := by
    ext i
    simp only [toAdd_mul,map_add,Pi.add_apply,AddCircle.coe_add,AddCircle.toCircle_add,Pi.mul_apply]

theorem map_continuous : Continuous (map L b) := by
  apply continuous_pi
  intro i
  exact AddCircle.continuous_toCircle.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_apply i).comp (b.ofZLatticeBasis ℝ L).equivFun.toContinuousLinearEquiv.continuous))

lemma real_circle_surjective : Function.Surjective (fun x : ℝ => AddCircle.toCircle (x : AddCircle (1 : ℝ))) := by
  intro y
  obtain ⟨z,hz⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective y
  obtain ⟨r,rfl⟩ := QuotientAddGroup.mk_surjective z
  exact ⟨r, (AddCircle.homeomorphCircle_apply one_ne_zero _).symm.trans hz⟩

theorem map_surjective : Function.Surjective (map L b) := by
  intro y
  choose r hr using fun i => real_circle_surjective (y i)
  refine ⟨Multiplicative.ofAdd ((b.ofZLatticeBasis ℝ L).equivFun.symm r), ?_⟩
  funext i
  change AddCircle.toCircle (((b.ofZLatticeBasis ℝ L).equivFun
    ((b.ofZLatticeBasis ℝ L).equivFun.symm r)) i : AddCircle (1 : ℝ)) = y i
  rw [LinearEquiv.apply_symm_apply]
  exact hr i

theorem mem_map_ker (x : Multiplicative E) : x ∈ (map L b).ker ↔ x.toAdd ∈ L := by
  have hi (i : ι) : AddCircle.toCircle ((b.ofZLatticeBasis ℝ L).repr x.toAdd i : AddCircle (1 : ℝ)) = 1 ↔
      (b.ofZLatticeBasis ℝ L).repr x.toAdd i ∈ Set.range (algebraMap ℤ ℝ) := by
    rw [← AddCircle.toCircle_zero (T := (1 : ℝ)),(AddCircle.injective_toCircle one_ne_zero).eq_iff,
      AddCircle.coe_eq_zero_iff]
    simp
  change (map L b x = 1) ↔ _
  conv_rhs => rw [← b.ofZLatticeBasis_span ℝ]
  rw [Basis.mem_span_iff_repr_mem]
  constructor
  · intro hx i
    exact (hi i).mp (congrFun hx i)
  · intro hx
    funext i
    exact (hi i).mpr (hx i)

end LatticeTorus
end MathieuProperty
