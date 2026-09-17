import MathieuProperty.LieOneParameter
import MathieuProperty.ConnectedLie
import MathieuProperty.ComplexCartan
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! The existing one-parameter curves act through the actual adjoint representation.
The complexified representation is constructed by scalar extension, not by
highest-weight existence. -/
noncomputable section
open scoped Manifold ContDiff TensorProduct
namespace MathieuProperty.AdjointOneParameter
set_option backward.isDefEq.respectTransparency false
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
local instance smoothness : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)

abbrev Algebra := GroupLieAlgebra 𝓘(ℝ,E) G
local instance algebraNormed : NormedAddCommGroup (Algebra (E := E) (G := G)) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance algebraNormedSpace : NormedSpace ℝ (Algebra (E := E) (G := G)) :=
  inferInstanceAs (NormedSpace ℝ E)

def complexAdjoint : Representation ℂ G (ℂ ⊗[ℝ] Algebra (E := E) (G := G)) where
  toFun g := (CompactAdjoint.adjointRepresentation (E := E) (G := G) g).baseChange ℂ
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' g h := by rw [map_mul, LinearMap.baseChange_mul]

omit [CompleteSpace E] [T2Space G] in
@[simp] theorem complexAdjoint_tmul (g : G) (c : ℂ) (v : Algebra (E := E) (G := G)) :
    complexAdjoint g (c ⊗ₜ[ℝ] v) = c ⊗ₜ[ℝ] CompactAdjoint.adjointRepresentation g v := rfl

/-- The differential along the actual generated subgroup is ad(X), at zero. -/
theorem adjoint_curve_hasDerivAt_zero (X v : Algebra (E := E) (G := G)) :
    HasDerivAt (fun t : ℝ => ConnectedLie.adjoint (E := E) (G := G) (LieOneParameter.curve (E := E) X t) v) (show E from (⁅X,v⁆ : Algebra (E := E) (G := G))) 0 := by
  have hcurve := LieOneParameter.curve_integral (E := E) X 0
  have hA := (ConnectedLie.adjoint_smooth (E := E) (G := G)).mdifferentiableAt (x := LieOneParameter.curve X 0)
    (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hd := hA.hasMFDerivAt.comp 0 hcurve
  have hlin := hd.hasFDerivAt.hasDerivAt
  have hv := hlin.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simp only [map_zero, add_zero] at hv
  change HasDerivAt (fun t : ℝ => ConnectedLie.adjoint (E := E) (G := G)
      (LieOneParameter.curve X t) v)
    ((show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) (ConnectedLie.adjoint (E := E) (G := G))
      (LieOneParameter.curve X 0) ((1 : ℝ) • LieOneParameter.field X (LieOneParameter.curve X 0))) v) 0 at hv
  rw [one_smul, LieOneParameter.curve_zero, LieOneParameter.field_one,
    ConnectedLie.adjoint_mfderiv] at hv
  exact hv

/-- The actual adjoint orbit solves the constant linear ODE ad(X) at every time. -/
theorem adjoint_curve_hasDerivAt (X v : Algebra (E := E) (G := G)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ConnectedLie.adjoint (E := E) (G := G)
      (LieOneParameter.curve X s) v)
      (show E from (⁅X, CompactAdjoint.adjointRepresentation (LieOneParameter.curve X t) v⁆ :
        Algebra (E := E) (G := G))) t := by
  have h := adjoint_curve_hasDerivAt_zero X
    (CompactAdjoint.adjointRepresentation (LieOneParameter.curve X t) v)
  have he : (fun s : ℝ => ConnectedLie.adjoint (E := E) (G := G)
      (LieOneParameter.curve X s)
      (CompactAdjoint.adjointRepresentation (LieOneParameter.curve X t) v)) =
      (fun s : ℝ => ConnectedLie.adjoint (E := E) (G := G) (LieOneParameter.curve X (s+t)) v) := by
    funext s
    rw [LieOneParameter.curve_add]
    change _ = CompactAdjoint.adjointLinear (LieOneParameter.curve X s * LieOneParameter.curve X t) v
    rw [CompactAdjoint.adjointLinear_mul]
    rfl
  rw [he] at h
  have hshift := HasDerivAt.comp_sub_const t t (by simpa using h)
  simpa using hshift

/-- A coordinate map intertwining ad(X) with A intertwines the actual group
curve with any solution of the corresponding linear ODE. -/
theorem coordinate_curve_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E →L[ℝ] F) (A : F →L[ℝ] F) (X v : Algebra (E := E) (G := G))
    (hp : ∀ w : Algebra (E := E) (G := G), p (⁅X,w⁆ : Algebra (E := E) (G := G)) = A (p w))
    (f : ℝ → F) (hf : ∀ t, HasDerivAt f (A (f t)) t) (h0 : f 0 = p v) :
    (fun t => p (ConnectedLie.adjoint (E := E) (G := G) (LieOneParameter.curve X t) v)) = f := by
  apply ODE_solution_unique_univ (s := fun _ => Set.univ)
    (K := ‖A‖₊) (v := fun _ => A) (t₀ := 0)
  · intro t
    exact A.lipschitzWith.lipschitzOnWith
  · intro t
    refine ⟨?_, Set.mem_univ _⟩
    have hd := p.hasFDerivAt.comp_hasDerivAt t (adjoint_curve_hasDerivAt X v t)
    rw [hp] at hd
    exact hd
  · intro t
    exact ⟨hf t, Set.mem_univ _⟩
  · change p (CompactAdjoint.adjointLinear (LieOneParameter.curve X 0) v) = f 0
    rw [LieOneParameter.curve_zero, CompactAdjoint.adjointLinear_one]
    exact h0.symm

end MathieuProperty.AdjointOneParameter
