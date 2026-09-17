import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import MathieuProperty.HaarRealForm
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
/-! The actual adjoint action of a real smooth Lie group.

Conjugation fixes the identity, so its derivative acts on `GroupLieAlgebra`.
The chain rule gives a representation, smooth parameter differentiation gives
continuity, and naturality of vector-field brackets gives Lie automorphisms.
For compact finite-dimensional groups, Haar averaging supplies a positive
symmetric form invariant under this group action. Infinitesimal invariance
under the Lie bracket is proved separately in `CompactLieStructure`.

The local norm on the tangent space is the fixed chart-model norm, used for
calculus and finite-dimensional averaging. It is not asserted to be invariant.
-/

noncomputable section
open scoped Manifold ContDiff
namespace MathieuProperty
namespace CompactAdjoint
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
local instance : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)

/-- The derivative at the identity of conjugation by `g`. -/
def adjointLinear (g : G) : GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x*g⁻¹) 1

omit [LieGroup 𝓘(ℝ,E) ∞ G] in
theorem adjointLinear_one : adjointLinear (E := E) (1 : G) = ContinuousLinearMap.id ℝ _ := by
  have he : (fun x : G => (1 : G)*x*(1 : G)⁻¹) = id := by funext x; simp
  rw [adjointLinear, he, mfderiv_id]

theorem adjointLinear_mul (g h : G) : adjointLinear (E := E) (g*h) =
    (adjointLinear (E := E) g).comp (adjointLinear (E := E) h) := by
  have he : (fun x : G => (g*h)*x*(g*h)⁻¹) =
      (fun x : G => g*x*g⁻¹) ∘ (fun x : G => h*x*h⁻¹) := by
    funext x
    simp [mul_assoc]
  rw [adjointLinear, he, mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E))]
  · unfold adjointLinear
    rw [show h*1*h⁻¹ = (1 : G) by simp]
    rfl
  · exact (show ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : G => g*x*g⁻¹) from contMDiff_mul_right.comp contMDiff_mul_left).mdifferentiable (by simp) _
  · exact (show ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : G => h*x*h⁻¹) from contMDiff_mul_right.comp contMDiff_mul_left).mdifferentiable (by simp) _

def adjointRepresentation : Representation ℝ G (GroupLieAlgebra 𝓘(ℝ,E) G) where
  toFun g := (adjointLinear g).toLinearMap
  map_one' := congrArg ContinuousLinearMap.toLinearMap adjointLinear_one
  map_mul' g h := congrArg ContinuousLinearMap.toLinearMap (adjointLinear_mul g h)
local instance : NormedAddCommGroup (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance : NormedSpace ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedSpace ℝ E)
set_option backward.isDefEq.respectTransparency false in
theorem adjointLinear_contMDiff :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ, GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) ∞ (adjointLinear (E := E) (G := G)) := by
  intro g₀
  have hc : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
      (fun p : G × G => p.1 * p.2 * p.1⁻¹) :=
    (contMDiff_fst.mul contMDiff_snd).mul contMDiff_fst.inv
  have hd := hc.contMDiffAt.mfderiv (fun g x : G => g*x*g⁻¹) (fun _ : G => (1 : G))
    (m := ∞) (x₀ := g₀) contMDiffAt_const (by simp)
  have he : inTangentCoordinates 𝓘(ℝ,E) 𝓘(ℝ,E) (fun _ : G => (1 : G))
      (fun g : G => g*1*g⁻¹)
      (fun g : G => mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x*g⁻¹) 1) g₀ =
      adjointLinear (E := E) (G := G) := by
    funext g
    rw [inTangentCoordinates_eq _ _ _ (by simp)
      (by simp)]
    simp only [mul_one, mul_inv_cancel]
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    erw [(tangentBundleCore 𝓘(ℝ,E) G).coordChange_self,
      (tangentBundleCore 𝓘(ℝ,E) G).coordChange_self]
    · rfl
    · exact mem_chart_source E (1 : G)
    · exact mem_chart_source E (1 : G)
  rw [he] at hd
  exact hd
set_option backward.isDefEq.respectTransparency false in
theorem adjointRepresentation_continuous (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    Continuous (fun g : G => adjointRepresentation (E := E) g v) := by
  change Continuous (fun g : G => adjointLinear (E := E) g v)
  exact (adjointLinear_contMDiff (E := E) (G := G)).continuous.clm_apply continuous_const

theorem conjugation_contMDiff (g : G) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : G => g*x*g⁻¹) :=
  contMDiff_mul_right.comp contMDiff_mul_left

set_option backward.isDefEq.respectTransparency false in
theorem conjugation_vectorField (g x : G) (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y : G => g*y*g⁻¹) x
      (mulInvariantVectorField v x) =
    mulInvariantVectorField (adjointLinear (E := E) g v) (g*x*g⁻¹) := by
  have he : (fun y : G => g*y*g⁻¹) ∘ (fun y : G => x*y) =
      (fun y : G => (g*x*g⁻¹)*y) ∘ (fun y : G => g*y*g⁻¹) := by
    funext y
    simp [mul_assoc]
  have hd := congrArg (fun f : G → G => (show E →L[ℝ] E from by exact mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f (1 : G))) he
  rw [mfderiv_comp (I' := 𝓘(ℝ,E)) _
    ((conjugation_contMDiff (E := E) g).mdifferentiableAt (by simp))
    (contMDiff_mul_left.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)),
    mfderiv_comp (I' := 𝓘(ℝ,E)) _
    (contMDiff_mul_left.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp))
    ((conjugation_contMDiff (E := E) g).mdifferentiableAt (by simp))] at hd
  dsimp only at hd
  rw [mul_one x, show g*1*g⁻¹ = (1 : G) by simp] at hd
  exact congrArg (fun f : GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] TangentSpace 𝓘(ℝ,E) (g*x*g⁻¹) => f v) hd

set_option backward.isDefEq.respectTransparency false in
theorem inverse_mfderiv_conjugation (g x : G) :
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y : G => g*y*g⁻¹) x).inverse =
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y : G => g⁻¹*y*g) (g*x*g⁻¹) := by
  have he : (fun y : G => g⁻¹*y*g) ∘ (fun y : G => g*y*g⁻¹) = id := by
    funext y; simp [mul_assoc]
  have he' : (fun y : G => g*y*g⁻¹) ∘ (fun y : G => g⁻¹*y*g) = id := by
    funext y; simp [mul_assoc]
  have h₁ : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y : G => g*y*g⁻¹) :=
    (conjugation_contMDiff g).mdifferentiable (by simp)
  have h₂ : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y : G => g⁻¹*y*g) := by
    simpa using (conjugation_contMDiff (E := E) g⁻¹).mdifferentiable (by simp)
  have ha := congrArg (fun f : G → G => (show E →L[ℝ] E from by exact mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x)) he
  have hb := congrArg (fun f : G → G => (show E →L[ℝ] E from by exact mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f (g*x*g⁻¹))) he'
  rw [mfderiv_comp (I' := 𝓘(ℝ,E)) _ (h₂ _) (h₁ _), mfderiv_id] at ha
  rw [mfderiv_comp (I' := 𝓘(ℝ,E)) _ (h₁ _) (h₂ _), mfderiv_id] at hb
  dsimp only at hb ha
  rw [show g⁻¹*(g*x*g⁻¹)*g = x by group] at hb
  exact ContinuousLinearMap.inverse_eq hb ha

set_option backward.isDefEq.respectTransparency false in
theorem conjugation_pullback (g : G) (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    VectorField.mpullback 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x*g⁻¹)
      (mulInvariantVectorField v) = mulInvariantVectorField (adjointLinear (E := E) g⁻¹ v) := by
  funext x
  rw [VectorField.mpullback, inverse_mfderiv_conjugation]
  have h := conjugation_vectorField g⁻¹ (g*x*g⁻¹) v
  rw [show g⁻¹*(g*x*g⁻¹)*(g⁻¹)⁻¹ = x by group] at h
  erw [inv_inv] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem adjointLinear_lie [CompleteSpace E] (g : G) (v w : GroupLieAlgebra 𝓘(ℝ,E) G) :
    adjointLinear (E := E) g ⁅v,w⁆ =
      ⁅adjointLinear (E := E) g v, adjointLinear (E := E) g w⁆ := by
  have h := VectorField.mpullback_mlieBracket
    (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (x₀ := (1 : G))
    (mdifferentiableAt_mulInvariantVectorField v)
    (mdifferentiableAt_mulInvariantVectorField w)
    (conjugation_contMDiff (E := E) g⁻¹).contMDiffAt (by simp)
  rw [conjugation_pullback, conjugation_pullback] at h
  simp only [inv_inv] at h
  rw [VectorField.mpullback] at h
  have hi := inverse_mfderiv_conjugation (E := E) g⁻¹ (1 : G)
  erw [inv_inv] at hi
  rw [hi] at h
  rw [show g⁻¹*1*g = (1 : G) by simp] at h
  exact h

/-- Conjugation induces an automorphism of the actual group Lie algebra. -/
def adjointLieEquiv [CompleteSpace E] (g : G) :
    GroupLieAlgebra 𝓘(ℝ,E) G ≃ₗ⁅ℝ⁆ GroupLieAlgebra 𝓘(ℝ,E) G where
  __ := LinearMap.GeneralLinearGroup.toLinearEquiv ((adjointRepresentation (E := E) (G := G)).asGroupHom g)
  map_lie' {v w} := adjointLinear_lie g v w

section Compact
variable [IsTopologicalGroup G] [FiniteDimensional ℝ E] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
local instance : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)

def invariantForm : LinearMap.BilinForm ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  HaarRealForm.form (adjointRepresentation (E := E) (G := G))
    adjointRepresentation_continuous

theorem invariantForm_symmetric : (invariantForm (E := E) (G := G)).IsSymm :=
  HaarRealForm.symmetric _ _

theorem invariantForm_positive {v : GroupLieAlgebra 𝓘(ℝ,E) G} (hv : v ≠ 0) :
    0 < invariantForm (E := E) (G := G) v v :=
  HaarRealForm.positive _ _ hv

theorem invariantForm_anisotropic (v : GroupLieAlgebra 𝓘(ℝ,E) G)
    (hv : invariantForm (E := E) (G := G) v v = 0) : v = 0 :=
  HaarRealForm.anisotropic _ _ v hv

theorem invariantForm_adjoint (g : G) (v w : GroupLieAlgebra 𝓘(ℝ,E) G) :
    invariantForm (E := E) (G := G) (adjointRepresentation g v) (adjointRepresentation g w) =
      invariantForm (E := E) (G := G) v w :=
  HaarRealForm.invariant _ _ g v w
omit [IsTopologicalGroup G] in
/-- A compact Lie group has an adjoint-invariant positive form on its tangent
Lie algebra. The topological-group instance is derived from smoothness. -/
theorem exists_positive_adjoint_form :
    ∃ B : LinearMap.BilinForm ℝ (GroupLieAlgebra 𝓘(ℝ,E) G), B.IsSymm ∧
      (∀ v, v ≠ 0 → 0 < B v v) ∧
      ∀ g : G, ∀ v w, B (adjointRepresentation g v) (adjointRepresentation g w) = B v w := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  exact ⟨invariantForm, invariantForm_symmetric, fun _ hv => invariantForm_positive hv,
    invariantForm_adjoint⟩
end Compact

end CompactAdjoint
end MathieuProperty
