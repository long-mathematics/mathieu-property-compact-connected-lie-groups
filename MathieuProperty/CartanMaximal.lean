import MathieuProperty.StabilizerTorus

/-! Maximality of the Cartan stabilizer component among connected abelian subgroups.
Every Cartan exponential lies in the component. Differentiating commutation
with these exponentials shows that a commuting automorphism fixes the Cartan.
Connectedness then places any larger abelian subgroup back in the component. -/

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.CartanStabilizer
variable {V : Type*} [NormedRealLieAlgebra V] [FiniteDimensional ℝ V]
variable (H : LieSubalgebra ℝ V)

def componentInclusion : Component H →* LieAutomorphism.Group V :=
  (BilinearStabilizer.inclusion LieAutomorphism.bracket H.toSubmodule).comp
    (componentOpen H).toSubgroup.subtype

def componentImage : Subgroup (LieAutomorphism.Group V) := (componentInclusion H).range

theorem componentInclusion_continuous : Continuous (componentInclusion H) :=
  (BilinearStabilizer.inclusion_continuous _ _).comp continuous_subtype_val

theorem exponential_mem_component (D : tangent H) :
    BilinearStabilizer.groupExponential LieAutomorphism.bracket H.toSubmodule D ∈
      connectedComponent (1 : Group H) := by
  let f := BilinearStabilizer.groupExponential (LieAutomorphism.bracket (V := V)) H.toSubmodule
  have h1 : (1 : Group H) ∈ Set.range f := by
    refine ⟨0, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact NormedSpace.exp_zero
  exact (isConnected_range (BilinearStabilizer.groupExponential_continuous (LieAutomorphism.bracket (V := V)) H.toSubmodule)).subset_connectedComponent
    h1 ⟨D,rfl⟩

theorem commute_tangent_of_centralizes_component (u : LieAutomorphism.Group V)
    (hu : ∀ t ∈ componentImage H, u * t = t * u) (D : tangent H) :
    u.val.val * D.val = D.val * u.val.val := by
  have he (s : ℝ) : u.val.val * NormedSpace.exp (s • D.val) =
      NormedSpace.exp (s • D.val) * u.val.val := by
    let t : Component H := ⟨BilinearStabilizer.groupExponential LieAutomorphism.bracket H.toSubmodule (s • D),
      exponential_mem_component H (s • D)⟩
    exact congrArg (fun a : LieAutomorphism.Group V => a.val.val)
      (hu (componentInclusion H t) ⟨t,rfl⟩)
  have hd : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • D.val)) D.val 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const D.val (0 : ℝ)
  have hl := hd.const_mul u.val.val
  have hr := hd.mul_const u.val.val
  have hf : (fun s : ℝ => u.val.val * NormedSpace.exp (s • D.val)) =
      (fun s : ℝ => NormedSpace.exp (s • D.val) * u.val.val) := funext he
  rw [hf] at hl
  exact hl.unique hr


variable [IsLieAbelian H] [LieAlgebra.IsKilling ℝ V]

theorem fixes_cartan_of_centralizes_component (u : LieAutomorphism.Group V)
    (hu : ∀ t ∈ componentImage H, u * t = t * u) (x : H) : u.val.val x.val = x.val := by
  apply LieModule.ext_of_isFaithful (R := ℝ) (L := V) V
  intro v
  have hi : u.val.val (u.val.inv v) = v := by
    change (u.val.val * u.val.inv) v = v
    rw [u.val.val_inv]
    rfl
  have hb := u.property x.val (u.val.inv v)
  change u.val.val ⁅x.val,u.val.inv v⁆ = ⁅u.val.val x.val,u.val.val (u.val.inv v)⁆ at hb
  have hd := congrArg (fun T : V →L[ℝ] V => T (u.val.inv v))
    (commute_tangent_of_centralizes_component H u hu (fromCartan H x))
  change u.val.val ⁅x.val,u.val.inv v⁆ = ⁅x.val,u.val.val (u.val.inv v)⁆ at hd
  rw [hi] at hb hd
  exact hb.symm.trans hd


theorem maximal_connected_abelian (S : Subgroup (LieAutomorphism.Group V))
    [ConnectedSpace S] (hc : ∀ u ∈ S, ∀ v ∈ S, u * v = v * u)
    (hT : componentImage H ≤ S) : S = componentImage H := by
  have hfix (u : S) (x : H) : u.val.val.val x.val = x.val :=
    fixes_cartan_of_centralizes_component H u.val (fun t ht => hc u.val u.property t (hT ht)) x
  let f : S → Group H := fun u => ⟨u.val.val, u.val.property, hfix u⟩
  have hf : Continuous f := (continuous_subtype_val.subtype_val).subtype_mk _
  have h1 : (1 : Group H) ∈ Set.range f := ⟨1,rfl⟩
  have hcomp (u : S) : f u ∈ connectedComponent (1 : Group H) :=
    (isConnected_range hf).subset_connectedComponent h1 ⟨u,rfl⟩
  apply le_antisymm _ hT
  intro u hu
  exact ⟨⟨f ⟨u,hu⟩, hcomp ⟨u,hu⟩⟩,rfl⟩


theorem componentImage_mul_comm [H.IsCartanSubalgebra]
    (u v : LieAutomorphism.Group V) (hu : u ∈ componentImage H) (hv : v ∈ componentImage H) :
    u * v = v * u := by
  obtain ⟨x,rfl⟩ := hu
  obtain ⟨y,rfl⟩ := hv
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (identity_component_commute H x.property y.property)

end MathieuProperty.CartanStabilizer
