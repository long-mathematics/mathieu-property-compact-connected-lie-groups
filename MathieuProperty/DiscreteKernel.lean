import MathieuProperty.CentralCovering

/-! Commutativity lifts through a discrete kernel on a connected source.
The commutator defines a continuous map into the discrete kernel, hence is
constant and equal to its value at identity. -/

namespace MathieuProperty.DiscreteKernel
variable {P G A : Type*} [Group P] [TopologicalSpace P] [PreconnectedSpace P]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group A]

theorem commute_image (j : P →* G) (hj : Continuous j) (f : G →* A)
    [DiscreteTopology f.ker] (hc : ∀ x y : P, f (j x) * f (j y) = f (j y) * f (j x))
    (x y : P) : j x * j y = j y * j x := by
  let c : P → f.ker := fun z => ⟨j x * j z * (j x)⁻¹ * (j z)⁻¹, by
    change f (j x * j z * (j x)⁻¹ * (j z)⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hc x z]
    simp [mul_assoc]⟩
  have hcont : Continuous c :=
    (((continuous_const.mul hj).mul continuous_const).mul hj.inv).subtype_mk _
  have he := (IsLocallyConstant.iff_continuous c).mpr hcont |>.apply_eq_of_preconnectedSpace y 1
  have hv := congrArg Subtype.val he
  change j x * j y * (j x)⁻¹ * (j y)⁻¹ = j x * j 1 * (j x)⁻¹ * (j 1)⁻¹ at hv
  simp only [map_one, mul_one, inv_one, mul_inv_cancel] at hv
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hv)

end MathieuProperty.DiscreteKernel
