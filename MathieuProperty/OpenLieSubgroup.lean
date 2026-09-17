import MathieuProperty.ConnectedLie
import Mathlib.Topology.Algebra.OpenSubgroup
/-! Open subgroups inherit a smooth Lie-group structure by restricting charts.
The derivative of inclusion is the identity on the common chart model.
Differentiating conjugation identifies the actual group Lie brackets, yielding
a canonical Lie-algebra equivalence with the ambient Lie group. -/

noncomputable section
open scoped Manifold ContDiff Topology
open Filter
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty
namespace OpenLieSubgroup
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]

instance chartedSpace (U : OpenSubgroup G) : ChartedSpace E U :=
  inferInstanceAs (ChartedSpace E U.toOpens)

instance isManifold (U : OpenSubgroup G) :
    IsManifold 𝓘(ℝ,E) ∞ U := by
  let : HasGroupoid U (contDiffGroupoid ∞ 𝓘(ℝ,E)) :=
    inferInstanceAs (HasGroupoid U.toOpens (contDiffGroupoid ∞ 𝓘(ℝ,E)))
  exact IsManifold.mk' _ _ _

omit [LieGroup 𝓘(ℝ,E) ∞ G] in
theorem inclusion_smooth (U : OpenSubgroup G) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun x : U => (x : G)) :=
  contMDiff_subtype_val (U := U.toOpens)

instance lieGroup (U : OpenSubgroup G) : LieGroup 𝓘(ℝ,E) ∞ U where
  contMDiff_mul := by
    apply (ContMDiff.subtypeVal_comp_iff U.toOpens _).mp
    exact ((inclusion_smooth U).comp contMDiff_fst).mul
      ((inclusion_smooth U).comp contMDiff_snd)
  contMDiff_inv := by
    apply (ContMDiff.subtypeVal_comp_iff U.toOpens _).mp
    exact (inclusion_smooth U).inv

omit [LieGroup 𝓘(ℝ,E) ∞ G] in
/-- Restriction charts make the differential of inclusion the identity on the model. -/
theorem inclusion_mfderiv (U : OpenSubgroup G) (x : U) :
    (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y : U => (y : G)) x) =
      ContinuousLinearMap.id ℝ E := by
  have hf := (inclusion_smooth (E := E) U x).mdifferentiableAt (by simp)
  have hc := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := E) U.toOpens (x := x)
  have hr := (chartAt E (x : G)).eventually_right_inverse
    (mem_chart_target E (x : G))
  have hw : writtenInExtChartAt 𝓘(ℝ,E) 𝓘(ℝ,E) x (fun y : U => (y : G)) =ᶠ[
      𝓝 (extChartAt 𝓘(ℝ,E) x x)] id := by
    change (fun v => chartAt E (x : G) (((chartAt E x).symm v : U) : G)) =ᶠ[
      𝓝 (chartAt E (x : G) (x : G))] id
    filter_upwards [hc,hr] with v hv hvr
    change chartAt E (x : G) (((chartAt E x).symm v : U) : G) = v
    exact (congrArg (chartAt E (x : G)) hv.symm).trans hvr
  simpa only [mfderiv, ite_eq_left hf, ModelWithCorners.range_eq_univ,
    fderivWithin_univ, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    using! hw.fderiv_eq.trans (fderiv_id (𝕜 := ℝ))


/-- Conjugation in an open subgroup has the ambient adjoint operator. -/
theorem adjoint_eq (U : OpenSubgroup G) (g : U) :
    ConnectedLie.adjoint (E := E) g = ConnectedLie.adjoint (E := E) (g : G) := by
  let j : U → G := fun x => x.val
  let c : U → U := fun x => g*x*g⁻¹
  let d : G → G := fun x => (g : G)*x*(g : G)⁻¹
  have hc : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c :=
    contMDiff_mul_right.comp contMDiff_mul_left
  have hd : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ d :=
    contMDiff_mul_right.comp contMDiff_mul_left
  have he : j ∘ c = d ∘ j := rfl
  have hl := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E))
    (f := c) (g := j) (1 : U) ((inclusion_smooth (E := E) U).mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp))
  have hr := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E))
    (f := j) (g := d) (1 : U) (hd.mdifferentiableAt (by simp))
      ((inclusion_smooth (E := E) U).mdifferentiableAt (by simp))
  have hjc : (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) j (c 1)) =
      ContinuousLinearMap.id ℝ E := inclusion_mfderiv U (c 1)
  have hj : (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) j 1) =
      ContinuousLinearMap.id ℝ E := inclusion_mfderiv U 1
  change (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c 1) =
    (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d 1)
  simpa only [hjc,hj,ContinuousLinearMap.id_comp,ContinuousLinearMap.comp_id] using!
    hl.symm.trans hr


local instance openAmbientSmoothness : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
local instance openSubgroupSmoothness (U : OpenSubgroup G) :
    LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) U :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)

/-- The actual group Lie bracket on an open subgroup is the ambient bracket. -/
theorem lie_eq [CompleteSpace E] (U : OpenSubgroup G)
    (x y : GroupLieAlgebra 𝓘(ℝ,E) U) :
    (show E from (⁅x,y⁆ : GroupLieAlgebra 𝓘(ℝ,E) U)) =
      (show E from (⁅(show GroupLieAlgebra 𝓘(ℝ,E) G from x),
        (show GroupLieAlgebra 𝓘(ℝ,E) G from y)⁆ : GroupLieAlgebra 𝓘(ℝ,E) G)) := by
  let A := ConnectedLie.adjoint (E := E) (G := G)
  let B := ConnectedLie.adjoint (E := E) (G := U)
  let j : U → G := fun u => u.val
  have he : A ∘ j = B := funext (fun u => (adjoint_eq U u).symm)
  have hd := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E →L[ℝ] E))
    (f := j) (g := A) (1 : U)
    ((ConnectedLie.adjoint_smooth (E := E) (G := G)).mdifferentiableAt (by simp))
    ((inclusion_smooth (E := E) U).mdifferentiableAt (by simp))
  have hj : (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) j 1) =
      ContinuousLinearMap.id ℝ E := inclusion_mfderiv U 1
  have hd' : (show E →L[ℝ] E →L[ℝ] E from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) B 1) =
      (show E →L[ℝ] E →L[ℝ] E from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) A 1) := by
    have hdmodel : (show E →L[ℝ] E →L[ℝ] E from
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) (A ∘ j) 1) =
        (show E →L[ℝ] E →L[ℝ] E from
          mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) A 1).comp
        (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) j 1) := hd
    rw [he,hj,ContinuousLinearMap.comp_id] at hdmodel
    exact hdmodel
  have hxy := congrArg (fun T : E →L[ℝ] E →L[ℝ] E => T x y) hd'
  exact (ConnectedLie.adjoint_mfderiv (G := U) x y).symm.trans
    (hxy.trans (ConnectedLie.adjoint_mfderiv (G := G) x y))

/-- An open subgroup and its ambient Lie group have canonically identical Lie algebras. -/
def lieEquiv [CompleteSpace E] (U : OpenSubgroup G) :
    GroupLieAlgebra 𝓘(ℝ,E) U ≃ₗ⁅ℝ⁆ GroupLieAlgebra 𝓘(ℝ,E) G where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := by
    intro x y
    exact lie_eq (E := E) U x y

end OpenLieSubgroup
end MathieuProperty
