import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-! Central kernels and quotient identification for existing covering homomorphisms.
The conjugation orbit of an element of a discrete normal subgroup is constant
on a connected group. Covering fibers are discrete, so covering kernels are
central. A surjective covering homomorphism identifies the target with the
actual topological group quotient. No existence of a universal cover is assumed
by the project or proved in this module. -/

noncomputable section
namespace MathieuProperty.CentralCovering
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [PreconnectedSpace G] [Group H] [TopologicalSpace H]

/-- A discrete normal subgroup of a connected topological group is central. -/
theorem discrete_normal_le_center (K : Subgroup G) [K.Normal] [DiscreteTopology K] :
    K ≤ Subgroup.center G := by
  intro z hz
  apply Subgroup.mem_center_iff.mpr
  intro g
  let c : G → K := fun x => ⟨x * z * x⁻¹, (inferInstance : K.Normal).conj_mem z hz x⟩
  have hc : Continuous c :=
    ((continuous_id.mul continuous_const).mul continuous_inv).subtype_mk _
  have he := (IsLocallyConstant.iff_continuous c).mpr hc |>.apply_eq_of_preconnectedSpace g 1
  have hval := congrArg Subtype.val he
  change g * z * g⁻¹ = 1 * z * (1 : G)⁻¹ at hval
  simpa only [one_mul, inv_one, mul_one, mul_assoc, inv_mul_cancel] using
    congrArg (fun x : G => x * g) hval

/-- A covering homomorphism with connected source has central kernel. -/
theorem covering_kernel_central (f : G →* H) (hf : IsCoveringMap f) :
    f.ker ≤ Subgroup.center G := by
  let : DiscreteTopology f.ker := (hf 1).discreteTopology_fiber
  exact discrete_normal_le_center f.ker

omit [PreconnectedSpace G] in
/-- The topological first isomorphism theorem for a surjective covering homomorphism. -/
def quotientEquiv (f : G →* H) (hf : IsCoveringMap f) (hs : Function.Surjective f) :
    G ⧸ f.ker ≃ₜ* H := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hs
  refine { e with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact hf.continuous
  · apply (hf.isOpenMap.isQuotientMap hf.continuous hs).continuous_iff.mpr
    have he : e.symm ∘ f = (QuotientGroup.mk : G → G ⧸ f.ker) := by
      funext g
      exact e.symm_apply_eq.mpr rfl
    change Continuous (e.symm ∘ f)
    rw [he]
    exact continuous_quot_mk

end MathieuProperty.CentralCovering
