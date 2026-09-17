import MathieuProperty.CartanLiftMaximal
import MathieuProperty.CoveringDifferential
import MathieuProperty.SmoothLift

/-! Smoothness and differentials of the constructed Cartan torus maps. -/

noncomputable section
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CartanStabilizer
variable {V : Type*} [NormedRealLieAlgebra V] [FiniteDimensional ℝ V]
variable (H : LieSubalgebra ℝ V) [H.IsCartanSubalgebra] [IsLieAbelian H]
local instance stabilizerInfinity : LieGroup 𝓘(ℝ,tangent H) ∞ (Group H) :=
  LieGroup.of_le (show (∞ : ℕ∞ω) ≤ ω by simp)

omit [H.IsCartanSubalgebra] [IsLieAbelian H] in
theorem component_val_smooth : ContMDiff 𝓘(ℝ,tangent H) 𝓘(ℝ,V →L[ℝ] V) ∞
    (fun x : Component H => x.val.val.val) :=
  ((BilinearStabilizer.val_contMDiff LieAutomorphism.bracket H.toSubmodule).of_le le_top).comp
    (OpenLieSubgroup.inclusion_smooth (E := tangent H) (componentOpen H))

omit [H.IsCartanSubalgebra] [IsLieAbelian H] in
theorem componentInclusion_smooth : ContMDiff 𝓘(ℝ,tangent H)
    𝓘(ℝ,BilinearAutomorphism.derivations (LieAutomorphism.bracket (V := V))) ∞ (componentInclusion H) := by
  intro x
  apply BilinearAutomorphism.contMDiffAt_of_val LieAutomorphism.bracket
    ((componentInclusion_continuous H).continuousAt)
  exact component_val_smooth H x

omit [H.IsCartanSubalgebra] [IsLieAbelian H] in
theorem component_val_mfderiv :
    (show tangent H →L[ℝ] V →L[ℝ] V from mfderiv 𝓘(ℝ,tangent H) 𝓘(ℝ,V →L[ℝ] V)
      (fun x : Component H => x.val.val.val) 1) = (tangent H).subtypeL := by
  have hc := mfderiv_comp (I := 𝓘(ℝ,tangent H)) (I' := 𝓘(ℝ,tangent H))
    (I'' := 𝓘(ℝ,V →L[ℝ] V))
    (f := fun x : Component H => (x.val : Group H))
    (g := fun x : Group H => x.val.val) (1 : Component H)
    ((BilinearStabilizer.val_contMDiff LieAutomorphism.bracket H.toSubmodule).mdifferentiableAt (by simp))
    ((OpenLieSubgroup.inclusion_smooth (E := tangent H) (componentOpen H)).mdifferentiableAt (by simp))
  have hv : (show tangent H →L[ℝ] V →L[ℝ] V from
      mfderiv 𝓘(ℝ,tangent H) 𝓘(ℝ,V →L[ℝ] V)
        (fun x : Group H => x.val.val) ((1 : Component H).val)) = (tangent H).subtypeL :=
    BilinearStabilizer.val_mfderiv_one LieAutomorphism.bracket H.toSubmodule
  dsimp only at hv
  rw [hv] at hc
  simpa only [OpenLieSubgroup.inclusion_mfderiv,
    ContinuousLinearMap.comp_id] using! hc

end MathieuProperty.CartanStabilizer

namespace MathieuProperty.CartanLift
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [ConnectedSpace G]
local instance differentialNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance differentialFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [IsTopologicalGroup G]
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)] [T2Space G]

abbrev Tangent := CartanStabilizer.tangent (Cartan (E := E) (G := G))

theorem liftToComponent_smooth : ContMDiff 𝓘(ℝ,Tangent (E := E) (G := G))
    𝓘(ℝ,Tangent (E := E) (G := G)) ∞ (liftToComponent (E := E) (G := G)) :=
  (CoveringCharts.contMDiff (F := Tangent (E := E) (G := G)) (n := ∞)
    (toComponent (E := E) (G := G)) toComponent_covering.isLocalHomeomorph).comp
    (OpenLieSubgroup.inclusion_smooth (E := Tangent (E := E) (G := G)) (liftOpen (E := E) (G := G)))

set_option maxHeartbeats 800000 in
theorem liftToComponent_mfderiv :
    (show Tangent (E := E) (G := G) →L[ℝ] Tangent (E := E) (G := G) from
      mfderiv 𝓘(ℝ,Tangent (E := E) (G := G)) 𝓘(ℝ,Tangent (E := E) (G := G))
        (liftToComponent (E := E) (G := G)) 1) = ContinuousLinearMap.id ℝ _ := by
  have hc := mfderiv_comp (I := 𝓘(ℝ,Tangent (E := E) (G := G)))
    (I' := 𝓘(ℝ,Tangent (E := E) (G := G))) (I'' := 𝓘(ℝ,Tangent (E := E) (G := G)))
    (f := fun x : Lift (E := E) (G := G) => x.val)
    (g := toComponent (E := E) (G := G)) (1 : Lift (E := E) (G := G))
    ((CoveringCharts.contMDiff (F := Tangent (E := E) (G := G)) (n := ∞)
      (toComponent (E := E) (G := G)) toComponent_covering.isLocalHomeomorph).mdifferentiableAt (by simp))
    ((OpenLieSubgroup.inclusion_smooth (E := Tangent (E := E) (G := G)) (liftOpen (E := E) (G := G))).mdifferentiableAt (by simp))
  have hd := CoveringCharts.mfderiv_eq_id (F := Tangent (E := E) (G := G))
    (toComponent (E := E) (G := G)) toComponent_covering.isLocalHomeomorph ((1 : Lift (E := E) (G := G)).val)
  dsimp only at hd
  have hj := OpenLieSubgroup.inclusion_mfderiv (E := Tangent (E := E) (G := G))
    (liftOpen (E := E) (G := G)) (1 : Lift (E := E) (G := G))
  dsimp only at hj
  erw [hd,hj,ContinuousLinearMap.id_comp] at hc
  exact hc

theorem inclusion_smoothAt_one : ContMDiffAt 𝓘(ℝ,Tangent (E := E) (G := G)) 𝓘(ℝ,E) ∞
    (inclusion (E := E) (G := G)) 1 := by
  let a := FullAdjoint.toAutomorphisms (E := E) (G := G)
  let D : E →L[ℝ] FullAdjoint.Model (E := E) (G := G) :=
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,FullAdjoint.Model (E := E) (G := G)) a 1
  have hi : Function.Injective D := by
    intro x y h
    apply SimpleGroupCenter.adjoint_derivative_injective (E := E) (G := G)
    exact (FullAdjoint.toAutomorphisms_mfderiv_val (E := E) (G := G) x).symm.trans
      ((congrArg Subtype.val h).trans (FullAdjoint.toAutomorphisms_mfderiv_val (E := E) (G := G) y))
  let e : E ≃L[ℝ] FullAdjoint.Model (E := E) (G := G) :=
    (LinearEquiv.ofBijective D.toLinearMap ⟨hi,FullAdjoint.toAutomorphisms_mfderiv_surjective (E := E) (G := G)⟩).toContinuousLinearEquiv
  have hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,FullAdjoint.Model (E := E) (G := G)) ∞ a
      (inclusion (E := E) (G := G) 1) := by
    rw [map_one]
    exact FullAdjoint.toAutomorphisms_smooth 1
  have hd : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,FullAdjoint.Model (E := E) (G := G)) a
      (inclusion (E := E) (G := G) 1) = (e : E →L[ℝ] FullAdjoint.Model (E := E) (G := G)) := by
    rw [map_one]
    rfl
  have hs := (CartanStabilizer.componentInclusion_smooth (Cartan (E := E) (G := G))).comp
    (liftToComponent_smooth (E := E) (G := G))
  have he : a ∘ inclusion (E := E) (G := G) =
      CartanStabilizer.componentInclusion (Cartan (E := E) (G := G)) ∘ liftToComponent (E := E) (G := G) := by
    funext x
    exact (componentInclusion_toComponent (E := E) (G := G) x.val).symm
  apply SmoothLift.manifold_of_comp 𝓘(ℝ,Tangent (E := E) (G := G)) (by simp) hf e hd
    (inclusion_continuous (E := E) (G := G)).continuousAt
  rw [he]
  exact hs 1

theorem inclusion_smooth : ContMDiff 𝓘(ℝ,Tangent (E := E) (G := G)) 𝓘(ℝ,E) ∞
    (inclusion (E := E) (G := G)) := by
  intro x
  have h1 : ContMDiffAt 𝓘(ℝ,Tangent (E := E) (G := G)) 𝓘(ℝ,E) ∞
      (inclusion (E := E) (G := G)) (x⁻¹*x) := by
    simpa only [inv_mul_cancel] using inclusion_smoothAt_one (E := E) (G := G)
  have h := h1.comp x (contMDiff_mul_left (a := x⁻¹) x)
  have hs := (contMDiffAt_const (c := inclusion (E := E) (G := G) x)).mul h
  convert hs using 1
  ext y
  simp only [Function.comp_def, Pi.mul_apply, map_mul, map_inv, mul_inv_cancel_left]

def tangentInclusion : Tangent (E := E) (G := G) →L[ℝ] E :=
  mfderiv 𝓘(ℝ,Tangent (E := E) (G := G)) 𝓘(ℝ,E) (inclusion (E := E) (G := G)) 1

set_option maxHeartbeats 800000 in
theorem adjoint_tangentInclusion (D : Tangent (E := E) (G := G)) :
    (show GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G from
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,GroupLieAlgebra 𝓘(ℝ,E) G →L[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G)
        (CompactAdjoint.adjointLinear (E := E) (G := G)) 1 (tangentInclusion (E := E) (G := G) D)) = D.val := by
  let V := GroupLieAlgebra 𝓘(ℝ,E) G
  let c : CartanStabilizer.Component (Cartan (E := E) (G := G)) → V →L[ℝ] V := fun x => x.val.val.val
  have he : CompactAdjoint.adjointLinear (E := E) (G := G) ∘ inclusion (E := E) (G := G) =
      c ∘ liftToComponent (E := E) (G := G) := by
    funext x
    exact (congrArg (fun u : FullAdjoint.Target (E := E) (G := G) => u.val.val)
      (componentInclusion_toComponent (E := E) (G := G) x.val)).symm
  have hl := mfderiv_comp (I := 𝓘(ℝ,Tangent (E := E) (G := G))) (I' := 𝓘(ℝ,E))
    (I'' := 𝓘(ℝ,V →L[ℝ] V))
    (f := inclusion (E := E) (G := G)) (g := CompactAdjoint.adjointLinear (E := E) (G := G)) 1
    (CompactAdjoint.adjointLinear_contMDiff.mdifferentiableAt (by simp))
    ((inclusion_smoothAt_one (E := E) (G := G)).mdifferentiableAt (by simp))
  have hr := mfderiv_comp (I := 𝓘(ℝ,Tangent (E := E) (G := G)))
    (I' := 𝓘(ℝ,Tangent (E := E) (G := G))) (I'' := 𝓘(ℝ,V →L[ℝ] V))
    (f := liftToComponent (E := E) (G := G)) (g := c) 1
    ((CartanStabilizer.component_val_smooth (Cartan (E := E) (G := G))).mdifferentiableAt (by simp))
    ((liftToComponent_smooth (E := E) (G := G)).mdifferentiableAt (by simp))
  have hv : (show Tangent (E := E) (G := G) →L[ℝ] V →L[ℝ] V from
      mfderiv 𝓘(ℝ,Tangent (E := E) (G := G)) 𝓘(ℝ,V →L[ℝ] V) c
        (liftToComponent (E := E) (G := G) 1)) = (Tangent (E := E) (G := G)).subtypeL := by
    rw [map_one]
    exact CartanStabilizer.component_val_mfderiv (Cartan (E := E) (G := G))
  dsimp only at hv
  have ht := liftToComponent_mfderiv (E := E) (G := G)
  dsimp only at ht
  erw [hv, ht, ContinuousLinearMap.comp_id] at hr
  erw [he, hr, map_one] at hl
  exact (congrArg (fun q : Tangent (E := E) (G := G) →L[ℝ] V →L[ℝ] V => q D) hl).symm

theorem tangentInclusion_fromCartan (x : Cartan (E := E) (G := G)) :
    tangentInclusion (E := E) (G := G) (CartanStabilizer.fromCartan (Cartan (E := E) (G := G)) x) = x.val := by
  apply SimpleGroupCenter.adjoint_derivative_injective (E := E) (G := G)
  have ht := adjoint_tangentInclusion (E := E) (G := G)
    (CartanStabilizer.fromCartan (Cartan (E := E) (G := G)) x)
  dsimp only at ht
  refine ht.trans ?_
  apply ContinuousLinearMap.ext
  intro v
  exact (ConnectedLie.adjoint_mfderiv (E := E) (G := G) x.val v).symm

theorem tangentInclusion_range : (tangentInclusion (E := E) (G := G)).range =
    (Cartan (E := E) (G := G)).toSubmodule := by
  ext x
  constructor
  · rintro ⟨D,rfl⟩
    obtain ⟨y,rfl⟩ := (CartanStabilizer.fromCartan_bijective (Cartan (E := E) (G := G))).2 D
    erw [tangentInclusion_fromCartan]
    exact y.property
  · intro hx
    exact ⟨CartanStabilizer.fromCartan (Cartan (E := E) (G := G)) ⟨x,hx⟩,
      tangentInclusion_fromCartan ⟨x,hx⟩⟩

theorem tangentInclusion_injective : Function.Injective (tangentInclusion (E := E) (G := G)) := by
  intro D D' h
  obtain ⟨x,rfl⟩ := (CartanStabilizer.fromCartan_bijective (Cartan (E := E) (G := G))).2 D
  obtain ⟨y,rfl⟩ := (CartanStabilizer.fromCartan_bijective (Cartan (E := E) (G := G))).2 D'
  have he : x.val = y.val := (tangentInclusion_fromCartan x).symm.trans
    (h.trans (tangentInclusion_fromCartan y))
  exact congrArg (CartanStabilizer.fromCartan (Cartan (E := E) (G := G))) (Subtype.ext he)

end MathieuProperty.CartanLift
