import MathieuProperty.Projection

/-! Faithfulness and unitary coordinate changes for an existing root doublet.

A homomorphism acting by the defining SU(2) action on a supplied doublet is
injective. Unitary changes of coordinates preserve the full special unitary
matrix subgroup. These statements do not construct a root homomorphism.
-/

noncomputable section
namespace MathieuProperty
open Hopf

theorem su2_base_action_injective : Function.Injective (fun k : SU2 => k • ((1, 0) : Space)) := by
  intro k l h
  apply su2SphereHomeomorph.injective
  apply Subtype.ext
  change (k.val 0 0, k.val 1 0) = (l.val 0 0, l.val 1 0)
  simpa [su2_smul_apply] using h

theorem root_hom_injective {G E : Type*} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* (E ≃ₗᵢ[ℂ] E))
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] (e : W ≃ₗᵢ[ℂ] EuclideanPair)
    (φ : SU2 →* G)
    (he : ∀ k (w : W), doubletProjection W e (ρ (φ k) w) = k • WithLp.ofLp (e w)) :
    Function.Injective φ := by
  intro k l hkl
  apply su2_base_action_injective
  have hk := he k (doubletBaseVector W e)
  rw [hkl] at hk
  have hl := he l (doubletBaseVector W e)
  simpa [doubletBaseVector] using hk.symm.trans hl

theorem unitary_conjugate_specialUnitary (U : Matrix.unitaryGroup (Fin 2) ℂ) (g : SU2) :
    U.val * g.val * (star U).val ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  constructor
  · exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem U.property g.property.1) (star U).property
  · change Matrix.det (U.val * g.val * (star U).val) = 1
    have hg : Matrix.det g.val = 1 := g.property.2
    have hu : U.val * (star U).val = 1 := by
      change ((U * star U : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1
      simp
    have hd := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_one] at hd
    simpa only [Matrix.det_mul, hg, mul_one] using hd

theorem specialUnitary_change_basis (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    (fun g : Matrix (Fin 2) (Fin 2) ℂ => U.val * g * (star U).val) ''
      (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
        Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact unitary_conjugate_specialUnitary U ⟨g, hg⟩
  · intro g hg
    refine ⟨(star U).val * g * U.val, ?_, ?_⟩
    · simpa using unitary_conjugate_specialUnitary (star U) ⟨g, hg⟩
    · have hu : U.val * (star U).val = 1 := by
        change ((U * star U : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1
        simp
      simp only [← Matrix.mul_assoc, hu, one_mul]
      rw [Matrix.mul_assoc, hu, mul_one]

end MathieuProperty
