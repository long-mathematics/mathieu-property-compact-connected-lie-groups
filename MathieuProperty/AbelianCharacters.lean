import MathieuProperty.HaarUnitarization
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-! Continuous finite-dimensional representations of compact abelian groups
have finite character expansions. Haar unitarization reduces to unitary
representations. The two Hermitian parts of every group operator commute;
mathlib joint eigenspaces span the space, and each joint space acts by a
continuous character. Conversely, characters are one-dimensional representations. -/

noncomputable section
open scoped InnerProductSpace
namespace MathieuProperty
variable {G E : Type*} [CommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (π : Representation ℂ G E)

def hermitianPart (i : G × Bool) : E →ₗ[ℂ] E :=
  if i.2 then Complex.I • (π i.1 - π i.1⁻¹) else π i.1 + π i.1⁻¹

theorem representation_inner_adjoint
    (hπ : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) (g : G) (x y : E) :
    inner ℂ (π g x) y = inner ℂ x (π g⁻¹ y) := by
  have h := hπ g x (π g⁻¹ y)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] using h

theorem hermitianPart_symmetric
    (hπ : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) (i : G × Bool) :
    (hermitianPart π i).IsSymmetric := by
  intro x y
  rcases i with ⟨g,b⟩
  cases b
  · simp only [hermitianPart, Bool.false_eq_true, ite_false, LinearMap.add_apply, inner_add_left,
      inner_add_right, representation_inner_adjoint π hπ, inv_inv]
    ring
  · simp only [hermitianPart, ite_true, LinearMap.smul_apply, LinearMap.sub_apply,
      inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
      representation_inner_adjoint π hπ, inv_inv, Complex.conj_I]
    ring

theorem representation_commute (g h : G) : Commute (π g) (π h) := by
  exact (Commute.all g h).map π

theorem hermitianPart_commute (i j : G × Bool) : Commute (hermitianPart π i) (hermitianPart π j) := by
  rcases i with ⟨g,b⟩
  rcases j with ⟨h,c⟩
  cases b <;> cases c <;> simp only [hermitianPart, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    repeat' first
      | apply Commute.smul_left
      | apply Commute.smul_right
      | apply Commute.add_left
      | apply Commute.add_right
      | apply Commute.sub_left
      | apply Commute.sub_right
    all_goals exact representation_commute π _ _

def jointEigenspace (χ : G × Bool → ℂ) : Submodule ℂ E :=
  ⨅ i, Module.End.eigenspace (hermitianPart π i) (χ i)

def jointEigenvalue (χ : G × Bool → ℂ) (g : G) : ℂ := (χ (g,false)-Complex.I*χ (g,true))/2

theorem jointEigenspaces_span [FiniteDimensional ℂ E]
    (hπ : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) :
    ⨆ χ, jointEigenspace π χ = ⊤ :=
  LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (hermitianPart_symmetric π hπ)
    (fun i j _ => hermitianPart_commute π i j)

theorem jointEigenspace_apply (χ : G × Bool → ℂ) {v : E} (hv : v ∈ jointEigenspace π χ) (g : G) :
    π g v = jointEigenvalue χ g • v := by
  have hall : ∀ i, v ∈ Module.End.eigenspace (hermitianPart π i) (χ i) := by
    exact (Submodule.mem_iInf _).mp hv
  have hh := Module.End.mem_eigenspace_iff.mp (hall (g,false))
  have hk := Module.End.mem_eigenspace_iff.mp (hall (g,true))
  have hr : hermitianPart π (g,false) v - Complex.I • hermitianPart π (g,true) v = (2 : ℂ) • π g v := by
    simp [hermitianPart, smul_sub, smul_smul, ← pow_two, Complex.I_sq]
    module
  rw [hh,hk] at hr
  have he := congrArg (fun x : E => (1/2 : ℂ) • x) hr
  simp only [smul_sub, smul_smul] at he
  norm_num at he
  rw [← he]
  unfold jointEigenvalue
  module

section Continuous
variable [TopologicalSpace G] (hπ : ∀ v, Continuous (fun g => π g v))

def jointCharacter (χ : G × Bool → ℂ) {v : E} (hv : v ∈ jointEigenspace π χ) (hv0 : v ≠ 0) : G →ₜ* ℂ where
  toFun := jointEigenvalue χ
  map_one' := by
    apply smul_left_injective ℂ hv0
    change jointEigenvalue χ 1 • v = (1 : ℂ) • v
    rw [← jointEigenspace_apply π χ hv, map_one, Module.End.one_apply, one_smul]
  map_mul' g h := by
    apply smul_left_injective ℂ hv0
    change jointEigenvalue χ (g*h) • v = (jointEigenvalue χ g * jointEigenvalue χ h) • v
    rw [← jointEigenspace_apply π χ hv, map_mul, Module.End.mul_apply,
      jointEigenspace_apply π χ hv, map_smul, jointEigenspace_apply π χ hv, smul_smul]
    rw [mul_comm]
  continuous_toFun := by
    have he (g : G) : jointEigenvalue χ g = inner ℂ v (π g v) / inner ℂ v v := by
      rw [jointEigenspace_apply π χ hv, inner_smul_right]
      exact (mul_div_cancel_right₀ _ (inner_self_ne_zero.mpr hv0)).symm
    change Continuous (fun g : G => jointEigenvalue χ g)
    simp_rw [he]
    exact (continuous_const.inner (hπ v)).div_const _

def characterSpan : Submodule ℂ C(G,ℂ) :=
  Submodule.span ℂ (Set.range (fun χ : G →ₜ* ℂ => χ.toContinuousMap))

def linearCoefficient (l : E →L[ℂ] ℂ) (v : E) : C(G,ℂ) :=
  ⟨fun g => l (π g v), l.continuous.comp (hπ v)⟩

theorem joint_coefficient_mem_characterSpan (l : E →L[ℂ] ℂ) (χ : G × Bool → ℂ)
    {v : E} (hv : v ∈ jointEigenspace π χ) : linearCoefficient π hπ l v ∈ characterSpan (G := G) := by
  by_cases hv0 : v = 0
  · subst v
    have he : linearCoefficient π hπ l 0 = 0 := by ext g; simp [linearCoefficient]
    rw [he]
    exact Submodule.zero_mem _
  · have he : linearCoefficient π hπ l v = l v • (jointCharacter π hπ χ hv hv0).toContinuousMap := by
      ext g
      simp only [linearCoefficient, ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul]
      change l (π g v) = l v * jointEigenvalue χ g
      rw [jointEigenspace_apply π χ hv, map_smul, smul_eq_mul, mul_comm]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨jointCharacter π hπ χ hv hv0,rfl⟩)

theorem unitary_coefficient_mem_characterSpan [FiniteDimensional ℂ E]
    (hunit : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y) (l : E →L[ℂ] ℂ) (v : E) :
    linearCoefficient π hπ l v ∈ characterSpan (G := G) := by
  have hv : v ∈ ⨆ χ, jointEigenspace π χ := by rw [jointEigenspaces_span π hunit]; trivial
  refine Submodule.iSup_induction (fun χ => jointEigenspace π χ)
    (motive := fun v => linearCoefficient π hπ l v ∈ characterSpan (G := G)) hv ?_ ?_ ?_
  · intro χ v hv
    exact joint_coefficient_mem_characterSpan π hπ l χ hv
  ·
    have he : linearCoefficient π hπ l 0 = 0 := by ext g; simp [linearCoefficient]
    rw [he]
    exact Submodule.zero_mem _
  · intro v w hv hw
    have he : linearCoefficient π hπ l (v+w) = linearCoefficient π hπ l v + linearCoefficient π hπ l w := by
      ext g
      simp [linearCoefficient]
    rw [he]
    exact Submodule.add_mem _ hv hw

end Continuous

section General
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V) (hρ : ∀ v, Continuous (fun g => ρ g v))

theorem coefficient_mem_characterSpan (l : V →ₗ[ℂ] ℂ) (v : V) :
    (⟨fun g => l (ρ g v), l.continuous_of_finiteDimensional.comp (hρ v)⟩ : C(G,ℂ)) ∈
      characterSpan (G := G) := by
  let e := unitaryModelEquiv ρ hρ
  let ρ' : Representation ℂ G (UnitaryModel ρ hρ) :=
    e.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : G) (w : UnitaryModel ρ hρ) : ρ' g w = unitaryModelRepresentation ρ hρ g w := by
    change e (ρ g (e.symm w)) = _
    rw [← unitaryModel_intertwines, ContinuousLinearEquiv.apply_symm_apply]
  have hc (w : UnitaryModel ρ hρ) : Continuous (fun g => ρ' g w) := by
    simp_rw [he]
    exact unitaryModel_continuous ρ hρ w
  have hu (g : G) (w z : UnitaryModel ρ hρ) : inner ℂ (ρ' g w) (ρ' g z) = inner ℂ w z := by
    rw [he,he]
    exact (unitaryModelRepresentation ρ hρ g).inner_map_map w z
  let l' : UnitaryModel ρ hρ →L[ℂ] ℂ := l.toContinuousLinearMap.comp e.symm.toContinuousLinearMap
  let fd : FiniteDimensional ℂ (UnitaryModel ρ hρ) := FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  have h := @unitary_coefficient_mem_characterSpan G (UnitaryModel ρ hρ) _ _ _ ρ' _ hc (by convert! fd) hu l' (e v)
  convert h using 1
  ext g
  change l (ρ g v) = l (e.symm (e (ρ g (e.symm (e v)))))
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]

end General

section CharacterRepresentation
variable [TopologicalSpace G]

def characterRepresentation (χ : G →ₜ* ℂ) : Representation ℂ G ℂ where
  toFun g := χ g • (1 : Module.End ℂ ℂ)
  map_one' := by simp
  map_mul' g h := by
    apply LinearMap.ext
    intro z
    simp [mul_comm, mul_left_comm]

theorem characterRepresentation_continuous (χ : G →ₜ* ℂ) (z : ℂ) :
    Continuous (fun g => characterRepresentation χ g z) := χ.continuous.mul continuous_const

theorem character_mem_representative (χ : G →ₜ* ℂ) : χ.toContinuousMap ∈ representativeSubmodule G := by
  have h := representation_coefficient_mem (characterRepresentation χ)
    (characterRepresentation_continuous χ) (LinearMap.id : ℂ →ₗ[ℂ] ℂ) 1
  have he : χ.toContinuousMap = (⟨fun g => LinearMap.id (characterRepresentation χ g 1),
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ).continuous_of_finiteDimensional.comp (characterRepresentation_continuous χ 1)⟩ : C(G,ℂ)) := by
    ext g
    simp [characterRepresentation]
  rw [he]
  exact h

end CharacterRepresentation

section CompactAbelian
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Every representative function on a compact abelian group is exactly a finite
complex linear combination of continuous characters, and conversely. -/
theorem representative_eq_characterSpan : representativeSubmodule G = characterSpan (G := G) := by
  rw [representative_eq_span_coefficients]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨n,ρ,hρ,l,v,hf⟩
    have he : f = (⟨fun g => l (ρ g v), l.continuous_of_finiteDimensional.comp (hρ v)⟩ : C(G,ℂ)) :=
      ContinuousMap.ext hf
    rw [he]
    exact coefficient_mem_characterSpan ρ hρ l v
  · apply Submodule.span_le.mpr
    rintro _ ⟨χ,rfl⟩
    rw [← representative_eq_span_coefficients]
    exact character_mem_representative χ

end CompactAbelian
end MathieuProperty
