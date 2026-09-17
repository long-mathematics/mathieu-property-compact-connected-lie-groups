import MathieuProperty.ProjectedRepresentatives
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-! Center descent of the six Hopf representative functions.

Schur's lemma gives unit scalar action on an irreducible unitary representation.
The tensor product with its conjugate is trivial on every central subgroup and
factors continuously through the quotient. Its coefficients construct all six
functions in the actual quotient representative algebra. The final wrapper uses
the orthogonal-projection coordinates from the manuscript. This assumes the
standing irreducible representation, not its still unproved universal existence.
-/

noncomputable section
namespace MathieuProperty
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

def centerIntertwiner (z : Subgroup.center G) : Representation.IntertwiningMap ρ ρ where
  toLinearMap := ρ z
  isIntertwining' g := by
    change ρ z * ρ g = ρ g * ρ z
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp z.property g)]

theorem center_scalar [FiniteDimensional ℂ V] [Representation.IsIrreducible ρ]
    (z : Subgroup.center G) : ∃ c : ℂ, ∀ v, ρ z v = c • v := by
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective (centerIntertwiner ρ z)
  refine ⟨c, fun v => ?_⟩
  have h := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc
  simpa [centerIntertwiner, Representation.IntertwiningMap.algebraMap_apply] using h.symm

theorem unitary_center_scalar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (π : G →* (E ≃ₗᵢ[ℂ] E))
    [Representation.IsIrreducible (unitaryToRepresentation π)]
    (z : Subgroup.center G) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v := by
  let σ := unitaryToRepresentation π
  obtain ⟨c, hc⟩ := center_scalar σ z
  have : Nontrivial σ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : σ.asModule)
  have hn : σ.asModuleEquiv v ≠ 0 := by
    simpa using (σ.asModuleEquiv.map_ne_zero_iff.mpr hv)
  have hh : ‖c‖ * ‖σ.asModuleEquiv v‖ = 1 * ‖σ.asModuleEquiv v‖ := by
    rw [one_mul, ← norm_smul, ← hc]
    exact (π z).norm_map _
  exact ⟨c, (mul_right_cancel₀ (norm_ne_zero_iff.mpr hn)) hh, hc⟩

open Hopf in
theorem doubletCoordinates_center_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (π : G →* (E ≃ₗᵢ[ℂ] E)) (W : Submodule ℂ E) [W.HasOrthogonalProjection]
    (e : W ≃ₗᵢ[ℂ] EuclideanPair) (z : G) (c : ℂ) (hc : ∀ v, π z v = c • v) (g : G) :
    doubletCoordinates W e π (z * g) = c • doubletCoordinates W e π g := by
  simp only [doubletCoordinates, map_mul]
  change doubletProjection W e (π z (π g (doubletBaseVector W e))) = _
  rw [hc, map_smul]

open Hopf in
theorem doublet_center_invariant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (π : G →* (E ≃ₗᵢ[ℂ] E))
    [Representation.IsIrreducible (unitaryToRepresentation π)]
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] (e : W ≃ₗᵢ[ℂ] EuclideanPair)
    (z : Subgroup.center G) (g : G) :
    let Φ := doubletCoordinates W e π
    a (Φ (z * g)) = a (Φ g) ∧ tau (Φ (z * g)) = tau (Φ g) ∧
    u (Φ (z * g)) = u (Φ g) ∧ v (Φ (z * g)) = v (Φ g) ∧
    P (Φ (z * g)) = P (Φ g) ∧ Q (Φ (z * g)) = Q (Φ g) := by
  obtain ⟨c, hc, hcv⟩ := unitary_center_scalar π z
  dsimp only
  rw [doubletCoordinates_center_smul π W e z c hcv]
  exact phase_balance_of_norm_eq_one c hc _

namespace MatrixRepresentation
variable [TopologicalSpace G] {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Kronecker in
theorem balanced_tensor_trivial (π : MatrixRepresentation G ι) (z : G) (c : ℂ)
    (hc : ‖c‖ = 1) (hz : π.toMonoidHom z = c • 1) :
    (π.tensor π.conjugate).toMonoidHom z = 1 := by
  have hc' : c * (starRingEnd ℂ) c = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  ext i j
  change π.toMonoidHom z i.1 j.1 * star (π.toMonoidHom z i.2 j.2) = (1 : Matrix (ι × ι) (ι × ι) ℂ) i j
  rw [hz]
  by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
    simp [Matrix.smul_apply, Matrix.one_apply, Prod.ext_iff, h₁, h₂, hc']

def descend (π : MatrixRepresentation G ι) (N : Subgroup G) [N.Normal]
    (hN : N ≤ π.toMonoidHom.ker) : MatrixRepresentation (G ⧸ N) ι where
  toMonoidHom := QuotientGroup.lift N π.toMonoidHom hN
  continuous_entry i j := by
    apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
    exact π.continuous_entry i j

theorem descend_coefficient (π : MatrixRepresentation G ι) (N : Subgroup G) [N.Normal]
    (hN : N ≤ π.toMonoidHom.ker) (a v : ι → ℂ) (g : G) :
    (π.descend N hN).coefficient a v (QuotientGroup.mk g) = π.coefficient a v g := by
  simp only [coefficient_apply, descend, QuotientGroup.lift_mk]

theorem ofRepresentation_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (b : Module.Basis ι ℂ E) (π : Representation ℂ G E)
    (hπ : ∀ v, Continuous (fun g => π g v)) (z : G) (c : ℂ)
    (hc : ∀ v, π z v = c • v) :
    (ofRepresentation b π hπ).toMonoidHom z = c • 1 := by
  have hz : π z = c • (1 : Module.End ℂ E) := by ext v; exact hc v
  change LinearMap.toMatrix b b (π z) = _
  rw [hz]
  simp

def balancedDescend (π : MatrixRepresentation G ι) (N : Subgroup G) [N.Normal]
    (hN : ∀ z ∈ N, ∃ c : ℂ, ‖c‖ = 1 ∧ π.toMonoidHom z = c • 1) :
    MatrixRepresentation (G ⧸ N) (ι × ι) :=
  (π.tensor π.conjugate).descend N (by
    intro z hz
    obtain ⟨c, hc, hz'⟩ := hN z hz
    exact balanced_tensor_trivial π z c hc hz')

def descendedBalancedCoefficient (π : MatrixRepresentation G ι) (N : Subgroup G) [N.Normal]
    (hN : ∀ z ∈ N, ∃ c : ℂ, ‖c‖ = 1 ∧ π.toMonoidHom z = c • 1)
    (a v b w : ι → ℂ) : representativeFunctions (G := G ⧸ N) :=
  ⟨(π.balancedDescend N hN).coefficient (fun p => a p.1 * star (b p.2))
      (fun p => v p.1 * star (w p.2)), coefficient_mem_representative _ _ _⟩

theorem descendedBalancedCoefficient_apply (π : MatrixRepresentation G ι) (N : Subgroup G)
    [N.Normal] (hN : ∀ z ∈ N, ∃ c : ℂ, ‖c‖ = 1 ∧ π.toMonoidHom z = c • 1)
    (a v b w : ι → ℂ) (g : G) :
    (descendedBalancedCoefficient π N hN a v b w).val (QuotientGroup.mk g) =
      π.coefficient a v g * star (π.coefficient b w g) := by
  change ((π.tensor π.conjugate).descend N _).coefficient _ _ (QuotientGroup.mk g) = _
  rw [descend_coefficient]
  have h := congrArg (fun f : C(G, ℂ) => f g) (π.coefficient_mul π.conjugate a v (star b) (star w))
  rw [← coefficient_conj] at h
  exact h.symm

theorem descended_hopf_functions (π : MatrixRepresentation G ι) (N : Subgroup G)
    [N.Normal] (hN : ∀ z ∈ N, ∃ c : ℂ, ‖c‖ = 1 ∧ π.toMonoidHom z = c • 1)
    (a₀ a₁ w : ι → ℂ) :
    ∃ A T U V P Q : representativeFunctions (G := G ⧸ N), ∀ g : G,
      let Φ := (π.coefficient a₀ w g, π.coefficient a₁ w g)
      A.val (QuotientGroup.mk g) = (Hopf.a Φ : ℂ) ∧
      T.val (QuotientGroup.mk g) = (Hopf.tau Φ : ℂ) ∧
      U.val (QuotientGroup.mk g) = Hopf.u Φ ∧
      V.val (QuotientGroup.mk g) = Hopf.v Φ ∧
      P.val (QuotientGroup.mk g) = Hopf.P Φ ∧
      Q.val (QuotientGroup.mk g) = Hopf.Q Φ := by
  let B₀₀ := descendedBalancedCoefficient π N hN a₀ w a₀ w
  let B₁₁ := descendedBalancedCoefficient π N hN a₁ w a₁ w
  let B₀₁ := descendedBalancedCoefficient π N hN a₀ w a₁ w
  let B₁₀ := descendedBalancedCoefficient π N hN a₁ w a₀ w
  let A := B₀₀ + B₁₁
  let T := B₀₀ - B₁₁
  let U := 2 * B₀₁
  let V := 2 * B₁₀
  let P := (A + U) * (A ^ 2 * V - (2 * A + U) * T ^ 2)
  refine ⟨A, T, U, V, P, U, fun g => ?_⟩
  dsimp only
  let Φ := (π.coefficient a₀ w g, π.coefficient a₁ w g)
  have hA : A.val (QuotientGroup.mk g) = (Hopf.a Φ : ℂ) := by
    change B₀₀.val (QuotientGroup.mk g) + B₁₁.val (QuotientGroup.mk g) = _
    simp only [B₀₀, B₁₁, descendedBalancedCoefficient_apply]
    simp [Φ, Hopf.a, Complex.normSq_eq_conj_mul_self, mul_comm]
  have hT : T.val (QuotientGroup.mk g) = (Hopf.tau Φ : ℂ) := by
    change B₀₀.val (QuotientGroup.mk g) - B₁₁.val (QuotientGroup.mk g) = _
    simp only [B₀₀, B₁₁, descendedBalancedCoefficient_apply]
    simp [Φ, Hopf.tau, Complex.normSq_eq_conj_mul_self, mul_comm]
  have hU : U.val (QuotientGroup.mk g) = Hopf.u Φ := by
    change 2 * B₀₁.val (QuotientGroup.mk g) = _
    simp only [B₀₁, descendedBalancedCoefficient_apply]
    simp [Φ, Hopf.u, mul_assoc]
  have hV : V.val (QuotientGroup.mk g) = Hopf.v Φ := by
    change 2 * B₁₀.val (QuotientGroup.mk g) = _
    simp only [B₁₀, descendedBalancedCoefficient_apply]
    simp [Φ, Hopf.v, mul_assoc]
  refine ⟨hA, hT, hU, hV, ?_, hU⟩
  change (A.val (QuotientGroup.mk g) + U.val (QuotientGroup.mk g)) *
    (A.val (QuotientGroup.mk g) ^ 2 * V.val (QuotientGroup.mk g) -
      (2 * A.val (QuotientGroup.mk g) + U.val (QuotientGroup.mk g)) *
        T.val (QuotientGroup.mk g) ^ 2) = _
  rw [hA, hT, hU, hV]
  rfl

end MatrixRepresentation
open Hopf in
theorem center_descent [TopologicalSpace G] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (π : G →* (E ≃ₗᵢ[ℂ] E)) (hπ : ∀ v, Continuous (fun g => π g v))
    [Representation.IsIrreducible (unitaryToRepresentation π)]
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] (e : W ≃ₗᵢ[ℂ] EuclideanPair)
    (N : Subgroup G) (hN : N ≤ Subgroup.center G) :
    letI : N.Normal := Subgroup.normal_of_le_center hN
    ∃ A T U V P Q : representativeFunctions (G := G ⧸ N), ∀ g : G,
      let Φ := doubletCoordinates W e π g
      A.val (QuotientGroup.mk g) = (Hopf.a Φ : ℂ) ∧
      T.val (QuotientGroup.mk g) = (Hopf.tau Φ : ℂ) ∧
      U.val (QuotientGroup.mk g) = Hopf.u Φ ∧
      V.val (QuotientGroup.mk g) = Hopf.v Φ ∧
      P.val (QuotientGroup.mk g) = Hopf.P Φ ∧
      Q.val (QuotientGroup.mk g) = Hopf.Q Φ := by
  let : N.Normal := Subgroup.normal_of_le_center hN
  let b := Module.finBasis ℂ E
  let σ := unitaryToRepresentation π
  let ψ := MatrixRepresentation.ofRepresentation b σ hπ
  have hs : ∀ z ∈ N, ∃ c : ℂ, ‖c‖ = 1 ∧ ψ.toMonoidHom z = c • 1 := by
    intro z hz
    obtain ⟨c, hc, hcv⟩ := unitary_center_scalar π ⟨z, hN hz⟩
    exact ⟨c, hc, MatrixRepresentation.ofRepresentation_scalar b σ hπ z c hcv⟩
  let l₀ : E →ₗ[ℂ] ℂ := (LinearMap.fst ℂ ℂ ℂ).comp (doubletProjection W e)
  let l₁ : E →ₗ[ℂ] ℂ := (LinearMap.snd ℂ ℂ ℂ).comp (doubletProjection W e)
  obtain ⟨A, T, U, V, P, Q, h⟩ := ψ.descended_hopf_functions N hs
    (fun i => l₀ (b i)) (fun i => l₁ (b i)) (b.repr (doubletBaseVector W e))
  refine ⟨A, T, U, V, P, Q, fun g => ?_⟩
  have hh := h g
  have h₀ := MatrixRepresentation.coefficient_ofRepresentation b σ hπ l₀ (doubletBaseVector W e) g
  have h₁ := MatrixRepresentation.coefficient_ofRepresentation b σ hπ l₁ (doubletBaseVector W e) g
  change ψ.coefficient _ _ g = _ at h₀ h₁
  dsimp only at hh
  rw [h₀, h₁] at hh
  exact hh

end MathieuProperty
