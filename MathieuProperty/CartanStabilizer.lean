import MathieuProperty.StabilizerLieGroup
import MathieuProperty.LieAutomorphism
import MathieuProperty.CompactCartan
import MathieuProperty.LocalCommutativity

/-! The pointwise stabilizer of an abelian Cartan in a real Killing Lie algebra.
Every tangent derivation is inner from the Cartan. These derivations commute,
so their exponentials give a commuting neighborhood of identity. The actual
identity component is therefore abelian. Compactness and maximal-torus
identification in the original group are separate obligations. -/

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CartanStabilizer
variable {V : Type*} [NormedRealLieAlgebra V] [FiniteDimensional ℝ V]
variable (H : LieSubalgebra ℝ V) [H.IsCartanSubalgebra] [IsLieAbelian H]

abbrev tangent := BilinearStabilizer.derivations (LieAutomorphism.bracket (V := V)) H.toSubmodule

def toDerivation (D : tangent H) : LieDerivation ℝ V V where
  toLinearMap := D.val.toLinearMap
  leibniz' x y := by
    have hD := (BilinearStabilizer.mem_derivations_iff _ _ D.val).mp D.property
    have h := (BilinearAutomorphism.mem_derivations_iff _ D.val).mp hD.1 x y
    change D.val ⁅x,y⁆ = ⁅D.val x,y⁆ + ⁅x,D.val y⁆ at h
    change D.val ⁅x,y⁆ = _
    rw [h]
    rw [sub_eq_add_neg, lie_skew, add_comm]
    rfl

theorem exists_inner [LieAlgebra.IsKilling ℝ V] (D : tangent H) :
    ∃ x : H, ∀ v : V, D.val v = ⁅x.val,v⁆ := by
  obtain ⟨x, hx⟩ := LieDerivation.IsKilling.exists_eq_ad (toDerivation H D)
  have hxD (v : V) : ⁅x,v⁆ = D.val v := by
    have he := congrArg (fun d : LieDerivation ℝ V V => d v) hx
    change -⁅v,x⁆ = D.val v at he
    exact (lie_skew x v).symm.trans he
  have hxH : x ∈ H := by
    apply (CompactLieForm.cartan_mem_iff_commutes H x).mpr
    intro y hy
    rw [hxD]
    exact ((BilinearStabilizer.mem_derivations_iff _ _ D.val).mp D.property).2 ⟨y, hy⟩
  exact ⟨⟨x,hxH⟩, fun v => (hxD v).symm⟩

theorem tangent_commute [LieAlgebra.IsKilling ℝ V] (D E : tangent H) :
    Commute D.val E.val := by
  obtain ⟨x, hx⟩ := exists_inner H D
  obtain ⟨y, hy⟩ := exists_inner H E
  change D.val * E.val = E.val * D.val
  ext v
  change D.val (E.val v) = E.val (D.val v)
  rw [hx, hy, hy, hx]
  have hxy : ⁅x.val,y.val⁆ = 0 :=
    congrArg Subtype.val (LieModule.IsTrivial.trivial x y)
  simpa only [hxy, zero_lie, zero_add] using (leibniz_lie x.val y.val v)


theorem exponential_commute [LieAlgebra.IsKilling ℝ V] (D E : tangent H) :
    Commute (BilinearStabilizer.groupExponential LieAutomorphism.bracket H.toSubmodule D)
      (BilinearStabilizer.groupExponential LieAutomorphism.bracket H.toSubmodule E) := by
  apply Subtype.ext
  apply Units.ext
  change NormedSpace.exp D.val * NormedSpace.exp E.val =
    NormedSpace.exp E.val * NormedSpace.exp D.val
  have hb (A : V →L[ℝ] V) : A ∈ Metric.eball (0 : V →L[ℝ] V)
      (NormedSpace.expSeries ℝ (V →L[ℝ] V)).radius := by
    simp [NormedSpace.expSeries_radius_eq_top]
  rw [← NormedSpace.exp_add_of_commute_of_mem_ball (tangent_commute H D E) (hb _) (hb _),
    ← NormedSpace.exp_add_of_commute_of_mem_ball (tangent_commute H E D) (hb _) (hb _), add_comm]


abbrev Group := BilinearStabilizer.group (LieAutomorphism.bracket (V := V)) H.toSubmodule

theorem exists_commuting_neighborhood [LieAlgebra.IsKilling ℝ V] :
    ∃ U ∈ 𝓝 (1 : Group H), ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
  let f := BilinearStabilizer.groupExponential (LieAutomorphism.bracket (V := V)) H.toSubmodule
  let l := BilinearStabilizer.groupLogarithm (LieAutomorphism.bracket (V := V)) H.toSubmodule
  refine ⟨{u | f (l u) = u}, BilinearStabilizer.groupExponential_logarithm_eventually _ _, ?_⟩
  intro x hx y hy
  change f (l x) = x at hx
  change f (l y) = y at hy
  rw [← hx, ← hy]
  exact exponential_commute H _ _

theorem identity_component_commute [LieAlgebra.IsKilling ℝ V]
    {x y : Group H} (hx : x ∈ connectedComponent (1 : Group H))
    (hy : y ∈ connectedComponent (1 : Group H)) : x * y = y * x := by
  obtain ⟨U, hU, hc⟩ := exists_commuting_neighborhood H
  exact LocalCommutativity.identity_component_commute hU hc hx hy

end MathieuProperty.CartanStabilizer
