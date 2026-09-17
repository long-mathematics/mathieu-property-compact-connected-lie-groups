import MathieuProperty.ManifoldZeroDerivative
import Mathlib.Geometry.Manifold.GroupLieAlgebra
/-! Smooth homomorphisms on a connected real Lie group are determined by their
differential at the identity. A translation identity propagates a vanishing
differential, and local constancy then gives global uniqueness. -/

noncomputable section
open scoped Manifold

namespace MathieuProperty
namespace LieHomCalculus
open scoped ContDiff
variable {E F G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [TopologicalSpace N] [ChartedSpace F N]

set_option backward.isDefEq.respectTransparency false in
/-- A smooth translation relation propagates zero differential from the identity. -/
theorem mfderiv_zero_of_translate_relation (f : G → N)
    (hf : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,F) f)
    (h₀ : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f (1 : G) = 0)
    (htrans : ∀ g : G, ∃ φ : N → N, MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,F) φ (f 1) ∧
      f ∘ (fun x : G => g*x) = φ ∘ f) (g : G) : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f g = 0 := by
  obtain ⟨φ,hφ,he⟩ := htrans g
  have hl (k : G) : MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => k*x) :=
    contMDiff_mul_left.mdifferentiable (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hd := congrArg (fun u : G → N => (show E →L[ℝ] F from by exact mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) u (1 : G))) he
  rw [mfderiv_comp (I' := 𝓘(ℝ,E)) _ (hf _) (hl g _),
    mfderiv_comp (I' := 𝓘(ℝ,F)) _ hφ (hf _), h₀, ContinuousLinearMap.comp_zero] at hd
  dsimp only at hd
  rw [mul_one] at hd
  have he' : (fun x : G => g*x) ∘ (fun x : G => g⁻¹*x) = id := by funext x; simp
  have hb := mfderiv_comp (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E))
    (f := fun x : G => g⁻¹*x) (g := fun x : G => g*x) g (hl g _) (hl g⁻¹ _)
  rw [he', mfderiv_id, inv_mul_cancel] at hb
  calc
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f g = (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f g).comp (ContinuousLinearMap.id ℝ _) := by
      rw [ContinuousLinearMap.comp_id]
    _ = (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f g).comp
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x) 1).comp
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g⁻¹*x) g)) := by rw [← hb]
    _ = ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f g).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g*x) 1)).comp
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun x : G => g⁻¹*x) g) := rfl
    _ = 0 := by rw [hd, ContinuousLinearMap.zero_comp]
section TargetGroup
variable [Group N] [LieGroup 𝓘(ℝ,F) ∞ N]

set_option backward.isDefEq.respectTransparency false in
/-- The differential of multiplication at the identity pair is addition. -/
theorem mfderiv_mul_one_apply (v w : GroupLieAlgebra 𝓘(ℝ,F) N) :
    mfderiv (𝓘(ℝ,F).prod 𝓘(ℝ,F)) 𝓘(ℝ,F) (fun p : N × N => p.1*p.2)
      (1,1) (v,w) = v+w := by
  rw [mfderiv_prod_eq_add_apply ((contMDiff_mul 𝓘(ℝ,F) ∞).mdifferentiableAt (by simp))]
  have hr : (fun x : N => x*1) = id := by funext x; simp
  have hl : (fun x : N => 1*x) = id := by funext x; simp
  dsimp only
  rw [hr, hl, mfderiv_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [LieGroup 𝓘(ℝ,E) ∞ G] in
/-- Product differentiation when both maps take the identity to the identity. -/
theorem mfderiv_mul_at_one {f h : G → N}
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) f 1)
    (hh : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,F) h 1)
    (hf₁ : f 1 = 1) (hh₁ : h 1 = 1) (v : GroupLieAlgebra 𝓘(ℝ,E) G) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (fun x => f x*h x) 1 v =
      @HAdd.hAdd F F F _ (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1 v) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) h 1 v) := by
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F)
    ((fun p : N × N => p.1*p.2) ∘ (fun x : G => (f x,h x))) 1 v = _
  rw [mfderiv_comp (I' := 𝓘(ℝ,F).prod 𝓘(ℝ,F)) _
    ((contMDiff_mul 𝓘(ℝ,F) ∞).mdifferentiableAt (by simp)) (hf.prodMk hh),
    hf.mfderiv_prod hh]
  dsimp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  rw [hf₁, hh₁]
  exact mfderiv_mul_one_apply (F := F) (N := N) _ _
set_option backward.isDefEq.respectTransparency false in
/-- Smooth homomorphisms from a connected group agree if their differentials agree. -/
theorem hom_eq_of_mfderiv_eq [PreconnectedSpace G] (f h : G →* N)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (hh : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ h)
    (he : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f 1 = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) h 1) : f = h := by
  let δ : G → N := fun x => f x*(h x)⁻¹
  have hδ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ δ := hf.mul hh.inv
  have hδ₁ : δ 1 = 1 := by simp [δ]
  have hprod : (fun x => δ x*h x) = f := by funext x; simp [δ, mul_assoc]
  have hzero : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) δ 1 = 0 := by
    ext v
    have hd := mfderiv_mul_at_one (hδ.mdifferentiableAt (by simp))
      (hh.mdifferentiableAt (by simp)) hδ₁ (map_one h) v
    rw [hprod, he] at hd
    exact add_eq_right.mp hd.symm
  have hglobal : ∀ x, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) δ x = 0 := by
    apply mfderiv_zero_of_translate_relation δ (hδ.mdifferentiable (by simp)) hzero
    intro g
    refine ⟨fun y : N => f g*y*(h g)⁻¹,
      (contMDiff_mul_right.comp contMDiff_mul_left).mdifferentiableAt (show (∞ : ℕ∞ω) ≠ 0 by simp), ?_⟩
    funext x
    simp [δ, map_mul, mul_assoc]
  have hc := ManifoldZeroDerivative.eq_of_mfderiv_zero (hδ.mdifferentiable (by simp)) hglobal
  ext x
  have hx := hc x 1
  rw [hδ₁] at hx
  exact mul_inv_eq_one.mp hx
end TargetGroup
end LieHomCalculus
end MathieuProperty
