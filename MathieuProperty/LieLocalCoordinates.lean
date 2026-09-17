import MathieuProperty.CompactAdjoint
import MathieuProperty.LieMixedDerivatives
/-! Local coordinates at the identity of a real smooth Lie group.
The coordinate origin need not be zero. Multiplication and the adjoint action
are smooth at that point, and both first partial derivatives of multiplication
are identities. Mixed derivatives and the exact chart pullback of invariant
vector fields prove the infinitesimal adjoint/Lie-bracket correspondence.
-/
noncomputable section
open scoped Manifold ContDiff
namespace MathieuProperty
namespace LieLocalChart
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]

def chart := extChartAt 𝓘(ℝ,E) (1 : G)
def origin : E := chart (E := E) (G := G) 1
def multiplication (p : E × E) : E :=
  chart (E := E) (G := G) ((chart (E := E) (G := G)).symm p.1 *
    (chart (E := E) (G := G)).symm p.2)

omit [LieGroup 𝓘(ℝ,E) ∞ G] in
theorem chart_symm_origin : (chart (E := E) (G := G)).symm (origin (E := E) (G := G)) = 1 :=
  (extChartAt 𝓘(ℝ,E) (1 : G)).left_inv (mem_extChartAt_source (1 : G))

omit [LieGroup 𝓘(ℝ,E) ∞ G] in
theorem chart_smooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (chart (E := E) (G := G)) (1 : G) :=
  contMDiffAt_extChartAt

omit [LieGroup 𝓘(ℝ,E) ∞ G] in
theorem chart_symm_smooth : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
    (chart (E := E) (G := G)).symm (origin (E := E) (G := G)) := by
  have h := contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ,E)) (n := ∞) (1 : G)
  rw [← contMDiffWithinAt_univ]
  simpa [chart, origin] using! h

theorem multiplication_smooth : ContDiffAt ℝ ∞ (multiplication (E := E) (G := G))
    (origin (E := E) (G := G), origin (E := E) (G := G)) := by
  have h₁ : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => (chart (E := E) (G := G)).symm p.1)
      (origin (E := E) (G := G), origin (E := E) (G := G)) := (chart_symm_smooth (E := E) (G := G)).comp (I := 𝓘(ℝ, E × E)) (I' := 𝓘(ℝ,E))
    (origin (E := E) (G := G), origin (E := E) (G := G)) (contDiffAt_fst (𝕜 := ℝ)).contMDiffAt
  have h₂ : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => (chart (E := E) (G := G)).symm p.2)
      (origin (E := E) (G := G), origin (E := E) (G := G)) := (chart_symm_smooth (E := E) (G := G)).comp (I := 𝓘(ℝ, E × E)) (I' := 𝓘(ℝ,E))
    (origin (E := E) (G := G), origin (E := E) (G := G)) (contDiffAt_snd (𝕜 := ℝ)).contMDiffAt
  have hc := (chart_smooth (E := E) (G := G)).comp_of_eq (h₁.mul h₂) (by simp [chart_symm_origin])
  exact hc.contDiffAt
omit [LieGroup 𝓘(ℝ,E) ∞ G] in
theorem origin_mem_target : origin (E := E) (G := G) ∈ (chart (E := E) (G := G)).target :=
  mem_extChartAt_target (1 : G)

omit [LieGroup 𝓘(ℝ,E) ∞ G] in
theorem target_mem_nhds : (chart (E := E) (G := G)).target ∈ nhds (origin (E := E) (G := G)) :=
  extChartAt_target_mem_nhds (1 : G)

theorem multiplication_origin_left (a : E) (ha : a ∈ (chart (E := E) (G := G)).target) :
    multiplication (E := E) (G := G) (origin (E := E) (G := G), a) = a := by
  unfold multiplication
  rw [chart_symm_origin, one_mul]
  exact (chart (E := E) (G := G)).right_inv ha

theorem multiplication_origin_right (a : E) (ha : a ∈ (chart (E := E) (G := G)).target) :
    multiplication (E := E) (G := G) (a, origin (E := E) (G := G)) = a := by
  unfold multiplication
  rw [chart_symm_origin, mul_one]
  exact (chart (E := E) (G := G)).right_inv ha
theorem multiplication_fderiv_first (v : E) :
    fderiv ℝ (multiplication (E := E) (G := G))
      (origin (E := E) (G := G), origin (E := E) (G := G)) (v,0) = v := by
  let a₀ := origin (E := E) (G := G)
  have he : (fun a => multiplication (E := E) (G := G) (a,a₀)) =ᶠ[nhds a₀] id := by
    filter_upwards [target_mem_nhds (E := E) (G := G)] with a ha
    exact multiplication_origin_right a ha
  have hd := (multiplication_smooth (E := E) (G := G)).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp (f := fun a : E => (a,a₀)) a₀
    ((hasFDerivAt_id a₀).prodMk (hasFDerivAt_const a₀ a₀))
  have hh := he.fderiv_eq (𝕜 := ℝ)
  have hv := congrArg (fun f : E →L[ℝ] E => f v) hc.fderiv
  dsimp only [Function.comp_def] at hv
  rw [hh, fderiv_id] at hv
  simpa using hv.symm

theorem multiplication_fderiv_second (v : E) :
    fderiv ℝ (multiplication (E := E) (G := G))
      (origin (E := E) (G := G), origin (E := E) (G := G)) (0,v) = v := by
  let a₀ := origin (E := E) (G := G)
  have he : (fun a => multiplication (E := E) (G := G) (a₀,a)) =ᶠ[nhds a₀] id := by
    filter_upwards [target_mem_nhds (E := E) (G := G)] with a ha
    exact multiplication_origin_left a ha
  have hd := (multiplication_smooth (E := E) (G := G)).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp (f := fun a : E => (a₀,a)) a₀
    ((hasFDerivAt_const a₀ a₀).prodMk (hasFDerivAt_id a₀))
  have hh := he.fderiv_eq (𝕜 := ℝ)
  have hv := congrArg (fun f : E →L[ℝ] E => f v) hc.fderiv
  dsimp only [Function.comp_def] at hv
  rw [hh, fderiv_id] at hv
  simpa using hv.symm
def adjointCoordinates (a : E) : E →L[ℝ] E := by
  exact CompactAdjoint.adjointLinear (E := E) ((chart (E := E) (G := G)).symm a)

theorem adjointCoordinates_origin : adjointCoordinates (E := E) (G := G)
    (origin (E := E) (G := G)) = ContinuousLinearMap.id ℝ E := by
  unfold adjointCoordinates
  rw [chart_symm_origin]
  exact CompactAdjoint.adjointLinear_one

local instance : NormedAddCommGroup (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance : NormedSpace ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedSpace ℝ E)

set_option backward.isDefEq.respectTransparency false in
theorem adjointCoordinates_smooth : ContDiffAt ℝ ∞ (adjointCoordinates (E := E) (G := G))
    (origin (E := E) (G := G)) := by
  have h := (CompactAdjoint.adjointLinear_contMDiff (E := E) (G := G)).contMDiffAt.comp
    (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (origin (E := E) (G := G))
    (chart_symm_smooth (E := E) (G := G))
  exact h.contDiffAt
theorem chart_smooth_at (g : G) (hg : g ∈ (chart (E := E) (G := G)).source) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (chart (E := E) (G := G)) g :=
  contMDiffAt_extChartAt' (by simpa [chart] using hg)

theorem chart_symm_smooth_at (a : E) (ha : a ∈ (chart (E := E) (G := G)).target) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (chart (E := E) (G := G)).symm a := by
  rw [← contMDiffWithinAt_univ]
  simpa [chart] using contMDiffWithinAt_extChartAt_symm_range (I := 𝓘(ℝ,E))
    (n := ∞) (1 : G) ha

theorem multiplication_smooth_at (a b : E)
    (ha : a ∈ (chart (E := E) (G := G)).target)
    (hb : b ∈ (chart (E := E) (G := G)).target)
    (hab : (chart (E := E) (G := G)).symm a * (chart (E := E) (G := G)).symm b ∈
      (chart (E := E) (G := G)).source) :
    ContDiffAt ℝ ∞ (multiplication (E := E) (G := G)) (a,b) := by
  have h₁ : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => (chart (E := E) (G := G)).symm p.1) (a,b) :=
    (chart_symm_smooth_at a ha).comp (I := 𝓘(ℝ,E × E)) (I' := 𝓘(ℝ,E)) (a,b)
      (contDiffAt_fst (𝕜 := ℝ)).contMDiffAt
  have h₂ : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E) ∞
      (fun p : E × E => (chart (E := E) (G := G)).symm p.2) (a,b) :=
    (chart_symm_smooth_at b hb).comp (I := 𝓘(ℝ,E × E)) (I' := 𝓘(ℝ,E)) (a,b)
      (contDiffAt_snd (𝕜 := ℝ)).contMDiffAt
  exact ((chart_smooth_at _ hab).comp (a,b) (h₁.mul h₂)).contDiffAt

theorem multiplication_smooth_left (a : E) (ha : a ∈ (chart (E := E) (G := G)).target) :
    ContDiffAt ℝ ∞ (multiplication (E := E) (G := G)) (a,origin (E := E) (G := G)) := by
  apply multiplication_smooth_at a _ ha origin_mem_target
  rw [chart_symm_origin, mul_one]
  exact (chart (E := E) (G := G)).map_target ha

theorem multiplication_smooth_right (a : E) (ha : a ∈ (chart (E := E) (G := G)).target) :
    ContDiffAt ℝ ∞ (multiplication (E := E) (G := G)) (origin (E := E) (G := G),a) := by
  apply multiplication_smooth_at _ a origin_mem_target ha
  rw [chart_symm_origin, one_mul]
  exact (chart (E := E) (G := G)).map_target ha
set_option backward.isDefEq.respectTransparency false in
theorem chart_symm_mfderiv_origin :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chart (E := E) (G := G)).symm
      (origin (E := E) (G := G)) = ContinuousLinearMap.id ℝ E := by
  have h := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ,E)) (x := (1 : G))
  simpa [chart, origin] using! h

set_option backward.isDefEq.respectTransparency false in
theorem leftPartial_vectorField (a : E) (ha : a ∈ (chart (E := E) (G := G)).target)
    (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    LieMixed.leftPartial (multiplication (E := E) (G := G)) (origin (E := E) (G := G)) v a =
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chart (E := E) (G := G)) ((chart (E := E) (G := G)).symm a)
      (mulInvariantVectorField v ((chart (E := E) (G := G)).symm a)) := by
  let c := chart (E := E) (G := G)
  let g := c.symm a
  let a₀ := origin (E := E) (G := G)
  have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) c g :=
    (chart_smooth_at g (c.map_target ha)).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x) (1 : G) :=
    contMDiff_mul_left.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hi := (chart_symm_smooth (E := E) (G := G)).mdifferentiableAt (by simp)
  rw [LieMixed.leftPartial_eq_deriv _ _ _ _ ((multiplication_smooth_left a ha).differentiableAt (by simp))]
  change fderiv ℝ ((c ∘ (fun x : G => g*x)) ∘ c.symm) a₀ v = _
  rw [← mfderiv_eq_fderiv]
  rw [mfderiv_comp (I' := 𝓘(ℝ,E))]
  · rw [show c.symm a₀ = (1 : G) from chart_symm_origin]
    rw [mfderiv_comp (I' := 𝓘(ℝ,E))]
    · rw [mul_one, chart_symm_mfderiv_origin]
      rfl
    · simpa using hc
    · exact hl
  · rw [show c.symm a₀ = (1 : G) from chart_symm_origin]
    exact hc.comp_of_eq (1 : G) hl (mul_one g)
  · exact hi
set_option backward.isDefEq.respectTransparency false in
theorem rightPartial_vectorField (a : E) (ha : a ∈ (chart (E := E) (G := G)).target)
    (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    LieMixed.rightPartial (multiplication (E := E) (G := G)) (origin (E := E) (G := G)) v a =
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chart (E := E) (G := G)) ((chart (E := E) (G := G)).symm a)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => x * (chart (E := E) (G := G)).symm a) 1 v) := by
  let c := chart (E := E) (G := G)
  let g := c.symm a
  let a₀ := origin (E := E) (G := G)
  have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) c g :=
    (chart_smooth_at g (c.map_target ha)).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => x*g) (1 : G) :=
    contMDiff_mul_right.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hi := (chart_symm_smooth (E := E) (G := G)).mdifferentiableAt (by simp)
  rw [LieMixed.rightPartial_eq_deriv _ _ _ _ ((multiplication_smooth_right a ha).differentiableAt (by simp))]
  change fderiv ℝ ((c ∘ (fun x : G => x*g)) ∘ c.symm) a₀ v = _
  rw [← mfderiv_eq_fderiv]
  rw [mfderiv_comp (I' := 𝓘(ℝ,E))]
  · rw [show c.symm a₀ = (1 : G) from chart_symm_origin]
    rw [mfderiv_comp (I' := 𝓘(ℝ,E))]
    · rw [one_mul, chart_symm_mfderiv_origin]
      rfl
    · simpa using hc
    · exact hl
  · rw [show c.symm a₀ = (1 : G) from chart_symm_origin]
    exact hc.comp_of_eq (1 : G) hl (one_mul g)
  · exact hi
set_option backward.isDefEq.respectTransparency false in
theorem rightTranslation_adjoint (g : G) (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => x*g) 1
      (CompactAdjoint.adjointLinear (E := E) g v) = mulInvariantVectorField v g := by
  have he : (fun x : G => x*g) ∘ (fun x : G => g*x*g⁻¹) = (fun x : G => g*x) := by
    funext x
    simp [mul_assoc]
  have hd := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E))
    (f := fun x : G => g*x*g⁻¹) (g := fun x : G => x*g) (1 : G)
    (contMDiff_mul_right.mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp))
    ((CompactAdjoint.conjugation_contMDiff (E := E) g).mdifferentiableAt (by simp))
  rw [he, show g*1*g⁻¹ = (1 : G) by simp] at hd
  exact congrArg (fun f : E →L[ℝ] E => f v) hd.symm

set_option backward.isDefEq.respectTransparency false in
theorem coordinate_adjoint_identity (a v : E) (ha : a ∈ (chart (E := E) (G := G)).target) :
    LieMixed.rightPartial (multiplication (E := E) (G := G)) (origin (E := E) (G := G))
      (adjointCoordinates (E := E) (G := G) a v) a =
    LieMixed.leftPartial (multiplication (E := E) (G := G)) (origin (E := E) (G := G)) v a := by
  rw [rightPartial_vectorField a ha, leftPartial_vectorField a ha]
  unfold adjointCoordinates
  erw [rightTranslation_adjoint]
set_option backward.isDefEq.respectTransparency false in
theorem chart_symm_mfderiv_inverse (a : E) (ha : a ∈ (chart (E := E) (G := G)).target) :
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chart (E := E) (G := G)).symm a).inverse =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chart (E := E) (G := G)) ((chart (E := E) (G := G)).symm a) := by
  have h₁ := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ,E)) (x := (1 : G)) ha
  have h₂ := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ,E)) (x := (1 : G)) ha
  simp at h₁ h₂
  exact ContinuousLinearMap.inverse_eq h₁ h₂

set_option backward.isDefEq.respectTransparency false in
theorem leftPartial_eq_pullback (a : E) (ha : a ∈ (chart (E := E) (G := G)).target)
    (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    LieMixed.leftPartial (multiplication (E := E) (G := G)) (origin (E := E) (G := G)) v a =
    VectorField.mpullback 𝓘(ℝ,E) 𝓘(ℝ,E) (chart (E := E) (G := G)).symm
      (mulInvariantVectorField v) a := by
  rw [VectorField.mpullback, chart_symm_mfderiv_inverse a ha]
  exact leftPartial_vectorField a ha v
set_option backward.isDefEq.respectTransparency false in
theorem leftPartial_eventually_pullback (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    LieMixed.leftPartial (multiplication (E := E) (G := G)) (origin (E := E) (G := G)) v =ᶠ[
      nhds (origin (E := E) (G := G))]
    VectorField.mpullback 𝓘(ℝ,E) 𝓘(ℝ,E) (chart (E := E) (G := G)).symm
      (mulInvariantVectorField v) := by
  filter_upwards [target_mem_nhds (E := E) (G := G)] with a ha
  exact leftPartial_eq_pullback a ha v

set_option backward.isDefEq.respectTransparency false in
theorem bracket_coordinates (v w : GroupLieAlgebra 𝓘(ℝ,E) G) :
    ⁅v,w⁆ = fderiv ℝ (LieMixed.leftPartial (multiplication (E := E) (G := G))
      (origin (E := E) (G := G)) w) (origin (E := E) (G := G)) v -
    fderiv ℝ (LieMixed.leftPartial (multiplication (E := E) (G := G))
      (origin (E := E) (G := G)) v) (origin (E := E) (G := G)) w := by
  have hb : ⁅v,w⁆ = VectorField.lieBracket ℝ
      (VectorField.mpullback 𝓘(ℝ,E) 𝓘(ℝ,E) (chart (E := E) (G := G)).symm (mulInvariantVectorField v))
      (VectorField.mpullback 𝓘(ℝ,E) 𝓘(ℝ,E) (chart (E := E) (G := G)).symm (mulInvariantVectorField w))
      (origin (E := E) (G := G)) := by
    rw [GroupLieAlgebra.bracket_def, VectorField.mlieBracket, VectorField.mlieBracketWithin_apply,
      mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id]
    erw [ContinuousLinearMap.id_apply]
    simp [chart, origin]
  rw [hb, ← (leftPartial_eventually_pullback v).lieBracket_vectorField_eq
    (leftPartial_eventually_pullback w), VectorField.lieBracket]
  have hv : LieMixed.leftPartial (multiplication (E := E) (G := G))
      (origin (E := E) (G := G)) v (origin (E := E) (G := G)) = v :=
    multiplication_fderiv_second (E := E) (G := G) v
  have hw : LieMixed.leftPartial (multiplication (E := E) (G := G))
      (origin (E := E) (G := G)) w (origin (E := E) (G := G)) = w :=
    multiplication_fderiv_second (E := E) (G := G) w
  rw [hv, hw]

set_option backward.isDefEq.respectTransparency false in
theorem adjointCoordinates_fderiv [CompleteSpace E] (x v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    fderiv ℝ (adjointCoordinates (E := E) (G := G)) (origin (E := E) (G := G)) x v = ⁅x,v⁆ := by
  rw [bracket_coordinates]
  apply LieMixed.adjoint_derivative
  · exact (multiplication_smooth (E := E) (G := G)).of_le (by simp)
  · exact (adjointCoordinates_smooth (E := E) (G := G)).differentiableAt (by simp)
  · exact adjointCoordinates_origin
  · exact multiplication_fderiv_first
  · filter_upwards [target_mem_nhds (E := E) (G := G)] with a ha
    exact coordinate_adjoint_identity a v ha
end LieLocalChart
end MathieuProperty
