import MathieuProperty.LieOneParameter
import MathieuProperty.LieHomCalculus
import MathieuProperty.LieSurjective
/-! Coordinates for connected abelian real Lie groups.
Multiplying the one-parameter subgroups associated with a tangent basis gives
a C¹ homomorphism from a real vector group. Its differential is the basis
coordinate equivalence, and local openness makes it surjective onto a connected
group. Compactness and lattice classification are not used here. -/

noncomputable section
open scoped Manifold ContDiff
open Module
namespace MathieuProperty
namespace AbelianParameters
set_option backward.isDefEq.respectTransparency false
variable {E G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CommGroup G] [TopologicalSpace G] [T2Space G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Fintype ι]

instance parameterDomainCharts : ChartedSpace (ι → ℝ) (Multiplicative (ι → ℝ)) :=
  inferInstanceAs (ChartedSpace (ι → ℝ) (ι → ℝ))

/-- The product of the one-parameter subgroups associated with a tangent basis. -/
def parameterMap (b : Basis ι ℝ E) : Multiplicative (ι → ℝ) →* G where
  toFun t := ∏ i, LieOneParameter.curve (show GroupLieAlgebra 𝓘(ℝ,E) G from b i) (t.toAdd i)
  map_one' := by simp [LieOneParameter.curve_zero]
  map_mul' t u := by simp only [toAdd_mul,Pi.add_apply,LieOneParameter.curve_add,
    Finset.prod_mul_distrib]

theorem parameterMap_smooth (b : Basis ι ℝ E) :
    ContMDiff 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) 1 (parameterMap (G := G) b) := by
  apply ContMDiff.prod
  intro i _
  exact (LieOneParameter.curve_contMDiff_one (show GroupLieAlgebra 𝓘(ℝ,E) G from b i)).comp
    (show ContMDiff 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,ℝ) 1 (fun t : Multiplicative (ι → ℝ) => t.toAdd i) from
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.contMDiff)


omit [FiniteDimensional ℝ E] [T2Space G] in
/-- At an identity-valued tuple, the differential of a finite product is the sum. -/
theorem finite_product_mfderiv (s : Finset ι) (f : ι → Multiplicative (ι → ℝ) → G)
    (hf : ∀ i, ContMDiff 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) 1 (f i))
    (h₁ : ∀ i, f i 1 = 1) (x : ι → ℝ) :
    (show E from mfderiv 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) (fun t => ∏ i ∈ s, f i t) 1 x) =
      ∑ i ∈ s, (show E from mfderiv 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) (f i) 1 x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty,mfderiv_const]
    rfl
  | @insert i s hi ih =>
    have he : (fun t => ∏ j ∈ insert i s, f j t) =
        (fun t => f i t * ∏ j ∈ s, f j t) := funext (fun _ => Finset.prod_insert hi)
    rw [he,Finset.sum_insert hi]
    have hs : ContMDiff 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) 1 (fun t => ∏ j ∈ s, f j t) :=
      ContMDiff.prod (fun j _ => hf j)
    have hs₁ : (∏ j ∈ s, f j 1) = 1 := by simp [h₁]
    have hd := LieHomCalculus.mfderiv_mul_at_one
      ((hf i).mdifferentiableAt one_ne_zero) (hs.mdifferentiableAt one_ne_zero)
      (h₁ i) hs₁ x
    exact hd.trans (congrArg (fun y : E =>
      (show E from mfderiv 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) (f i) 1 x) + y) ih)


theorem coordinate_mfderiv (b : Basis ι ℝ E) (i : ι) (x : ι → ℝ) :
    (show E from mfderiv 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E)
      (fun t : Multiplicative (ι → ℝ) =>
        LieOneParameter.curve (show GroupLieAlgebra 𝓘(ℝ,E) G from b i) (t.toAdd i)) 1 x) =
      (x i) • b i := by
  let v : GroupLieAlgebra 𝓘(ℝ,E) G := b i
  let p : Multiplicative (ι → ℝ) → ℝ := fun t => t.toAdd i
  have hp : HasMFDerivAt 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,ℝ) p 1 (ContinuousLinearMap.proj i) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.hasMFDerivAt
  have hd := mfderiv_comp (I := 𝓘(ℝ,ι → ℝ)) (I' := 𝓘(ℝ,ℝ)) (I'' := 𝓘(ℝ,E))
    (f := p) (g := LieOneParameter.curve v) (1 : Multiplicative (ι → ℝ))
    ((LieOneParameter.curve_contMDiff_one v).mdifferentiableAt one_ne_zero) hp.mdifferentiableAt
  have hdmodel : (show (ι → ℝ) →L[ℝ] E from
      mfderiv 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) (LieOneParameter.curve v ∘ p) 1) =
      (show ℝ →L[ℝ] E from mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (LieOneParameter.curve v) 0).comp
      (ContinuousLinearMap.proj i) := by
    exact hd.trans (congrArg (fun D : (ι → ℝ) →L[ℝ] ℝ =>
      (show ℝ →L[ℝ] E from mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (LieOneParameter.curve v) 0).comp D) hp.mfderiv)
  rw [LieOneParameter.curve_mfderiv_zero] at hdmodel
  exact congrArg (fun D : (ι → ℝ) →L[ℝ] E => D x) hdmodel

theorem parameterMap_mfderiv (b : Basis ι ℝ E) (x : ι → ℝ) :
    (show E from mfderiv 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) (parameterMap (G := G) b) 1 x) =
      b.equivFun.symm x := by
  rw [Basis.equivFun_symm_apply]
  have h := finite_product_mfderiv (E := E) (G := G) Finset.univ
    (fun i t => LieOneParameter.curve (show GroupLieAlgebra 𝓘(ℝ,E) G from b i) (t.toAdd i))
    (fun i => (LieOneParameter.curve_contMDiff_one _).comp
      (show ContMDiff 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,ℝ) 1 (fun t : Multiplicative (ι → ℝ) => t.toAdd i) from
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.contMDiff))
    (fun _ => LieOneParameter.curve_zero _) x
  exact h.trans (Finset.sum_congr rfl (fun i _ => coordinate_mfderiv (G := G) b i x))


theorem parameterMap_mfderiv_bijective (b : Basis ι ℝ E) :
    Function.Bijective (mfderiv 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) (parameterMap (G := G) b) 1) := by
  constructor
  · intro x y h
    apply b.equivFun.symm.injective
    rw [← parameterMap_mfderiv (G := G) b x,← parameterMap_mfderiv (G := G) b y]
    exact h
  · intro y
    refine ⟨b.equivFun y, ?_⟩
    exact (parameterMap_mfderiv (G := G) b (b.equivFun y)).trans (b.equivFun.symm_apply_apply y)

/-- A connected abelian Lie group is a continuous quotient of its real tangent vector group. -/
theorem parameterMap_surjective [ConnectedSpace G] (b : Basis ι ℝ E) :
    Function.Surjective (parameterMap (G := G) b) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  exact LieSurjective.surjective_of_surjective_mfderiv (parameterMap b)
    (parameterMap_smooth b 1) (parameterMap_mfderiv_bijective b).2

end AbelianParameters
end MathieuProperty
