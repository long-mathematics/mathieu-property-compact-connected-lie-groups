import MathieuProperty.RadialTransfer
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
/-! Equivariant orthogonal projection and coordinates for a given unitary defining doublet. -/

noncomputable section
open MeasureTheory
namespace MathieuProperty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An invariant subspace of a unitary operator has invariant orthogonal complement. -/
theorem invariant_orthogonal_complement (W : Submodule ℂ E) (u : E ≃ₗᵢ[ℂ] E)
    (hW : W.map u.toLinearEquiv.toLinearMap = W) :
    Wᗮ.map u.toLinearEquiv.toLinearMap = Wᗮ := by
  rw [W.map_orthogonal_equiv, hW]

theorem projection_commutes (W : Submodule ℂ E) [W.HasOrthogonalProjection]
    (u : E ≃ₗᵢ[ℂ] E) (hW : W.map u.toLinearEquiv.toLinearMap = W) (v : E) :
    W.starProjection (u v) = u (W.starProjection v) := by
  have h := Submodule.starProjection_map_apply u W (u v)
  simpa only [hW, u.symm_apply_apply] using h

variable {G : Type*} [Group G]

/-- Orthogonal projection of the orbit of the distinguished unit vector. -/
def projectionOrbit (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (W : Submodule ℂ E)
    [W.HasOrthogonalProjection] (v : E) (g : G) : W :=
  W.orthogonalProjectionOnto (ρ g v)

theorem projectionOrbit_continuous [TopologicalSpace G] (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (W : Submodule ℂ E)
    [W.HasOrthogonalProjection] (v : E) (hρ : Continuous (fun g => ρ g v)) :
    Continuous (projectionOrbit ρ W v) := W.orthogonalProjectionOnto.continuous.comp hρ

theorem projectionOrbit_norm_le (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (W : Submodule ℂ E)
    [W.HasOrthogonalProjection] (v : E) (g : G) : ‖projectionOrbit ρ W v g‖ ≤ ‖v‖ := by
  exact (W.norm_orthogonalProjectionOnto_apply_le (ρ g v)).trans_eq ((ρ g).norm_map v)

theorem projectionOrbit_one (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (W : Submodule ℂ E)
    [W.HasOrthogonalProjection] (v : W) : projectionOrbit ρ W v 1 = v := by
  simp [projectionOrbit]

theorem projectionOrbit_equivariant (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (W : Submodule ℂ E)
    [W.HasOrthogonalProjection] (v : E) (k g : G)
    (hW : W.map (ρ k).toLinearEquiv.toLinearMap = W) :
    (projectionOrbit ρ W v (k*g) : E) = ρ k (projectionOrbit ρ W v g) := by
  change W.starProjection (ρ (k*g) v) = ρ k (W.starProjection (ρ g v))
  rw [map_mul]
  exact projection_commutes W (ρ k) hW (ρ g v)

end MathieuProperty

namespace MathieuProperty
open Hopf
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (W : Submodule ℂ E) [W.HasOrthogonalProjection]
  (e : W ≃ₗᵢ[ℂ] EuclideanPair)

def doubletProjection : E →ₗ[ℂ] Space :=
  (WithLp.linearEquiv 2 ℂ Space).toLinearMap.comp
    (e.toLinearEquiv.toLinearMap.comp W.orthogonalProjectionOnto.toLinearMap)

theorem doubletProjection_apply (v : E) :
    doubletProjection W e v = WithLp.ofLp (e (W.orthogonalProjectionOnto v)) := rfl

theorem doubletProjection_continuous : Continuous (doubletProjection W e) :=
  (WithLp.prod_continuous_ofLp 2 ℂ ℂ).comp
    (e.continuous.comp W.orthogonalProjectionOnto.continuous)

theorem doubletProjection_a_le (v : E) : a (doubletProjection W e v) ≤ ‖v‖^2 := by
  rw [doubletProjection_apply, ← norm_sq_eq_a, e.norm_map]
  exact pow_le_pow_left₀ (norm_nonneg _) (W.norm_orthogonalProjectionOnto_apply_le v) 2

@[simp] theorem doubletProjection_starProjection (v : E) :
    doubletProjection W e (W.starProjection v) = doubletProjection W e v := by
  change WithLp.ofLp (e (W.orthogonalProjectionOnto (W.orthogonalProjectionOnto v : E))) = _
  rw [W.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

def doubletBaseVector : W := e.symm (WithLp.toLp 2 ((1, 0) : Space))

omit [W.HasOrthogonalProjection] in
theorem doubletBaseVector_norm : ‖doubletBaseVector W e‖ = 1 := by
  rw [doubletBaseVector, e.symm.norm_map]
  norm_num

@[simp] theorem doubletProjection_base :
    doubletProjection W e (doubletBaseVector W e) = ((1, 0) : Space) := by
  simp [doubletProjection, doubletBaseVector]

/-- Lean's inner product is linear in its second argument. This is the
inner-product coordinate formula with that convention. -/
theorem doubletProjection_inner (v : E) (w : W) :
    inner ℂ (e w) (WithLp.toLp 2 (doubletProjection W e v)) = inner ℂ (w : E) v := by
  change inner ℂ (e w) (e (W.orthogonalProjectionOnto v)) = _
  rw [e.inner_map_map, W.inner_orthogonalProjectionOnto_eq_of_mem_left]

theorem doubletProjection_first_inner (v : E) :
    (doubletProjection W e v).1 = inner ℂ (doubletBaseVector W e : E) v := by
  have h := doubletProjection_inner W e v (doubletBaseVector W e)
  simpa [doubletBaseVector, WithLp.prod_inner_apply] using h

theorem doubletProjection_second_inner (v : E) :
    (doubletProjection W e v).2 =
      inner ℂ ((e.symm (WithLp.toLp 2 ((0, 1) : Space))) : E) v := by
  have h := doubletProjection_inner W e v (e.symm (WithLp.toLp 2 ((0, 1) : Space)))
  simpa [WithLp.prod_inner_apply] using h

variable {G : Type*} [Group G]

def doubletCoordinates (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (g : G) : Space :=
  doubletProjection W e (ρ g (doubletBaseVector W e))

theorem doubletCoordinates_continuous [TopologicalSpace G] (ρ : G →* (E ≃ₗᵢ[ℂ] E))
    (hρ : Continuous (fun g => ρ g (doubletBaseVector W e))) :
    Continuous (doubletCoordinates W e ρ) := (doubletProjection_continuous W e).comp hρ

theorem doubletCoordinates_a_le (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (g : G) :
    a (doubletCoordinates W e ρ g) ≤ 1 := by
  apply (doubletProjection_a_le W e _).trans_eq
  rw [(ρ g).norm_map]
  change ‖doubletBaseVector W e‖^2 = 1
  rw [doubletBaseVector_norm]
  norm_num

@[simp] theorem doubletCoordinates_one (ρ : G →* (E ≃ₗᵢ[ℂ] E)) :
    doubletCoordinates W e ρ 1 = ((1, 0) : Space) := by
  simp [doubletCoordinates]

theorem doubletCoordinates_equivariant (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (φ : SU2 →* G)
    (hW : ∀ k, W.map (ρ (φ k)).toLinearEquiv.toLinearMap = W)
    (he : ∀ k (w : W), doubletProjection W e (ρ (φ k) w) = k • WithLp.ofLp (e w))
    (k : SU2) (g : G) : doubletCoordinates W e ρ (φ k * g) = k • doubletCoordinates W e ρ g := by
  have h := he k (W.orthogonalProjectionOnto (ρ g (doubletBaseVector W e)))
  change doubletProjection W e (ρ (φ k) (W.starProjection (ρ g (doubletBaseVector W e)))) = _ at h
  rw [← projection_commutes W (ρ (φ k)) (hW k), doubletProjection_starProjection] at h
  unfold doubletCoordinates
  rw [map_mul]
  exact h

end MathieuProperty
