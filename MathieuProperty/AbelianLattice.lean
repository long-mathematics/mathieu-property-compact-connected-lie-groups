import MathieuProperty.AbelianParameters
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
/-! The kernel of the abelian vector-group parametrization is a full lattice.
The inverse function theorem isolates zero in the kernel. Compactness forces
its real span to be the whole space: otherwise a nonzero real linear functional
annihilating the kernel descends continuously to the compact target, contradicting
its surjectivity onto the real line. -/

noncomputable section
open scoped Manifold ContDiff Topology
open Module Set
namespace MathieuProperty
namespace AbelianParameters
set_option backward.isDefEq.respectTransparency false
variable {E G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CommGroup G] [TopologicalSpace G] [T2Space G] [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Fintype ι]

def parameterAddMap (b : Basis ι ℝ E) : (ι → ℝ) →+ Additive G where
  toFun x := Additive.ofMul (parameterMap (G := G) b (Multiplicative.ofAdd x))
  map_zero' := congrArg Additive.ofMul (map_one (parameterMap (G := G) b))
  map_add' x y := congrArg Additive.ofMul
    (map_mul (parameterMap (G := G) b) (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

def kernel (b : Basis ι ℝ E) : Submodule ℤ (ι → ℝ) :=
  (parameterAddMap (G := G) b).ker.toIntSubmodule

theorem mem_kernel (b : Basis ι ℝ E) (x : ι → ℝ) :
    x ∈ kernel (G := G) b ↔ parameterMap (G := G) b (Multiplicative.ofAdd x) = 1 := Iff.rfl

theorem kernel_isolated (b : Basis ι ℝ E) :
    ∃ s : Set (ι → ℝ), IsOpen s ∧ (0 : ι → ℝ) ∈ s ∧
      ∀ x ∈ s, x ∈ kernel (G := G) b → x = 0 := by
  let f := parameterMap (G := G) b
  let ψ : (ι → ℝ) → E := fun x => extChartAt 𝓘(ℝ,E) (1 : G) (f (Multiplicative.ofAdd x))
  have hw : writtenInExtChartAt 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) (1 : Multiplicative (ι → ℝ)) f = ψ := by
    funext x
    change extChartAt 𝓘(ℝ,E) (f 1) (f (Multiplicative.ofAdd x)) = _
    rw [map_one]
  have h0 : extChartAt 𝓘(ℝ,ι → ℝ) (1 : Multiplicative (ι → ℝ)) 1 = (0 : ι → ℝ) := rfl
  have hm := parameterMap_smooth (G := G) b (1 : Multiplicative (ι → ℝ))
  have hf := hm.mdifferentiableAt one_ne_zero
  have hψ : ContDiffAt ℝ 1 ψ 0 := by
    have h := (contMDiffAt_iff.mp hm).2
    rw [ModelWithCorners.range_eq_univ] at h
    change ContDiffWithinAt ℝ 1
      (writtenInExtChartAt 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) (1 : Multiplicative (ι → ℝ)) f)
      Set.univ (extChartAt 𝓘(ℝ,ι → ℝ) (1 : Multiplicative (ι → ℝ)) 1) at h
    simpa only [hw,h0,contDiffWithinAt_univ] using h
  have hD : (show (ι → ℝ) →L[ℝ] E from mfderiv 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) f 1) =
      fderiv ℝ ψ 0 := by
    rw [mfderiv,ite_eq_left (show MDifferentiableAt 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) f 1 from hf)]
    change fderivWithin ℝ (writtenInExtChartAt 𝓘(ℝ,ι → ℝ) 𝓘(ℝ,E) (1 : Multiplicative (ι → ℝ)) f)
      (Set.range 𝓘(ℝ,ι → ℝ)) (extChartAt 𝓘(ℝ,ι → ℝ) (1 : Multiplicative (ι → ℝ)) 1) = _
    rw [hw,h0,ModelWithCorners.range_eq_univ,fderivWithin_univ]
  let e : (ι → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv
  have heD : fderiv ℝ ψ 0 = e.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact (congrArg (fun D : (ι → ℝ) →L[ℝ] E => D x) hD).symm.trans
      (parameterMap_mfderiv (G := G) b x)
  have hstrict : HasStrictFDerivAt ψ e.toContinuousLinearMap 0 := by
    rw [← heD]
    exact hψ.hasStrictFDerivAt one_ne_zero
  let c := hstrict.toOpenPartialHomeomorph ψ
  have hc0 : (0 : ι → ℝ) ∈ c.source := hstrict.mem_toOpenPartialHomeomorph_source
  refine ⟨c.source,c.open_source,hc0,?_⟩
  intro x hx hk
  apply c.injOn hx hc0
  change ψ x = ψ 0
  change extChartAt 𝓘(ℝ,E) (1 : G) (f (Multiplicative.ofAdd x)) =
    extChartAt 𝓘(ℝ,E) (1 : G) (f 1)
  rw [(mem_kernel b x).mp hk,map_one]


instance kernel_discrete (b : Basis ι ℝ E) : DiscreteTopology (kernel (G := G) b) := by
  obtain ⟨s,hs,h0,hk⟩ := kernel_isolated (G := G) b
  apply discreteTopology_of_isOpen_singleton_zero
  have he : (Subtype.val ⁻¹' s : Set (kernel (G := G) b)) = {0} := by
    ext x
    constructor
    · intro hx
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact hk x.val hx x.property
    · intro hx
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      rw [hx0]
      exact h0
  rw [← he]
  exact hs.preimage continuous_subtype_val


/-- Compactness forces the kernel of the vector-group quotient to span the whole vector space. -/
theorem kernel_span [ConnectedSpace G] [CompactSpace G] (b : Basis ι ℝ E) :
    Submodule.span ℝ (kernel (G := G) b : Set (ι → ℝ)) = ⊤ := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  let : SigmaCompactSpace (Multiplicative (ι → ℝ)) := inferInstanceAs (SigmaCompactSpace (ι → ℝ))
  let f := parameterMap (G := G) b
  have hf : Function.Surjective f := parameterMap_surjective b
  have hfc : Continuous f := (parameterMap_smooth b).continuous
  have hfo : IsOpenMap f := f.isOpenMap_of_sigmaCompact hf hfc
  by_contra htop
  obtain ⟨l,hl,hker⟩ := (Submodule.span ℝ (kernel (G := G) b : Set (ι → ℝ))).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr htop)
  have hfiber (x y : ι → ℝ) (hxy : f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd y)) :
      l x = l y := by
    have hk : x-y ∈ kernel (G := G) b := by
      apply (mem_kernel b _).mpr
      change f (Multiplicative.ofAdd x / Multiplicative.ofAdd y) = 1
      rw [map_div,hxy]
      exact div_self' _
    have hz : l (x-y) = 0 := hker (Submodule.subset_span hk)
    exact sub_eq_zero.mp ((map_sub l x y).symm.trans hz)
  let pre : G → (ι → ℝ) := fun g => (hf g).choose.toAdd
  have hpre (g : G) : f (Multiplicative.ofAdd (pre g)) = g := (hf g).choose_spec
  let q : G → ℝ := fun g => l (pre g)
  have he (x : Multiplicative (ι → ℝ)) : q (f x) = l x.toAdd :=
    hfiber _ _ (hpre (f x))
  have hq : Continuous q := by
    apply (hfo.isQuotientMap hfc hf).continuous_iff.mpr
    have hefun : q ∘ f = (fun x : Multiplicative (ι → ℝ) => l x.toAdd) := funext he
    rw [hefun]
    exact l.toContinuousLinearMap.continuous
  have hls : Function.Surjective l := surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (by simp) hl
  have hqs : Function.Surjective q := by
    intro r
    obtain ⟨x,hx⟩ := hls r
    exact ⟨f (Multiplicative.ofAdd x),(he _).trans hx⟩
  exact (isCompact_range hq).ne_univ (Set.range_eq_univ.mpr hqs)

instance kernel_isZLattice [ConnectedSpace G] [CompactSpace G] (b : Basis ι ℝ E) :
    IsZLattice ℝ (kernel (G := G) b) := ⟨kernel_span b⟩

end AbelianParameters
end MathieuProperty
