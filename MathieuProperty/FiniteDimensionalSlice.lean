import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-! Finite-dimensional coordinates separating the derivative image and kernel.
The implicit function theorem supplies an ambient local coordinate map. -/

noncomputable section
open scoped Topology ContDiff
namespace MathieuProperty
namespace FiniteSlice
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
def projection (p : Submodule ℝ E) : E →L[ℝ] p :=
  (p.projectionOnto (Classical.choose p.exists_isCompl) (Classical.choose_spec p.exists_isCompl)).toContinuousLinearMap
@[simp] theorem projection_self (p : Submodule ℝ E) (x : p) : projection p x = x :=
  Submodule.projectionOnto_apply_left (Classical.choose_spec p.exists_isCompl) x

omit [FiniteDimensional ℝ E] in
theorem projection_comp (L : E →L[ℝ] F) : (projection L.range).comp L = L.rangeRestrict := by
  ext x
  exact congrArg Subtype.val (projection_self L.range (L.rangeRestrict x))

def data (f : E → F) (L : E →L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f L a) : ImplicitFunctionData ℝ E L.range L.ker where
  leftFun x := projection L.range (f x)
  leftDeriv := L.rangeRestrict
  rightFun x := projection L.ker (x-a)
  rightDeriv := projection L.ker
  pt := a
  hasStrictFDerivAt_leftFun := by
    simpa only [projection_comp] using (projection L.range).hasStrictFDerivAt.comp a hf
  hasStrictFDerivAt_rightFun :=
    (projection L.ker).hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
  range_leftDeriv := L.range_rangeRestrict
  range_rightDeriv := LinearMap.range_eq_of_proj (projection_self L.ker)
  isCompl_ker := by
    have hk : L.rangeRestrict.ker = L.ker := by
      ext x
      change (L.rangeRestrict x = 0) ↔ L x = 0
      exact Subtype.ext_iff
    rw [hk]
    exact LinearMap.isCompl_of_proj (projection_self L.ker)

def coordinates (f : E → F) (L : E →L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f L a) : OpenPartialHomeomorph E (L.range × L.ker) :=
  (data f L a hf).toOpenPartialHomeomorph

theorem coordinates_apply (f : E → F) (L : E →L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f L a) (x : E) :
    coordinates f L a hf x = (projection L.range (f x), projection L.ker (x-a)) := rfl

theorem mem_coordinates_source (f : E → F) (L : E →L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f L a) : a ∈ (coordinates f L a hf).source :=
  (data f L a hf).pt_mem_toOpenPartialHomeomorph_source
end FiniteSlice
end MathieuProperty
