import MathieuProperty.RepresentativeFunctions

/-! Real finite-dimensional representation coefficients, with complex-valued
real-linear covectors, are actual complex representative functions. -/
noncomputable section
namespace MathieuProperty
namespace MatrixRepresentation
variable {G V ι : Type*} [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]

/-- Scalar extension of real coordinate matrices. -/
def ofRealRepresentation (b : Module.Basis ι ℝ V) (ρ : Representation ℝ G V)
    (hρ : ∀ v, Continuous fun g => ρ g v) : MatrixRepresentation G ι where
  toMonoidHom := Complex.ofRealHom.mapMatrix.toMonoidHom.comp
    ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ)
  continuous_entry i j := by
    change Continuous fun g => (((LinearMap.toMatrixAlgEquiv b) (ρ g)) i j : ℂ)
    simp only [LinearMap.toMatrixAlgEquiv_apply]
    let := b.finiteDimensional_of_finite
    exact Complex.continuous_ofReal.comp
      (((b.coord i).continuous_of_finiteDimensional).comp (hρ (b j)))

theorem coefficient_ofRealRepresentation (b : Module.Basis ι ℝ V) (ρ : Representation ℝ G V)
    (hρ : ∀ v, Continuous fun g => ρ g v) (l : V →ₗ[ℝ] ℂ) (v : V) (g : G) :
    (ofRealRepresentation b ρ hρ).coefficient (fun i => l (b i))
      (fun j => (b.repr v j : ℂ)) g = l (ρ g v) := by
  rw [coefficient_apply]
  change (∑ i, ∑ j, l (b i) * (((LinearMap.toMatrixAlgEquiv b) (ρ g)) i j : ℂ) *
    (b.repr v j : ℂ)) = _
  simp only [LinearMap.toMatrixAlgEquiv_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_mul]
  have h : (∑ i, l (b i) * (b.repr (ρ g (b j)) i : ℂ)) = l (ρ g (b j)) := by
    conv_rhs => rw [← b.sum_repr (ρ g (b j))]
    simp only [map_sum, map_smul, Complex.real_smul, mul_comm]
  rw [h]
  simp [Complex.real_smul, mul_comm]
end MatrixRepresentation

/-- A real adjoint coefficient needs no highest-weight existence theorem. -/
theorem real_representation_coefficient_mem
    {G V : Type*} [Monoid G] [TopologicalSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : Representation ℝ G V) (hρ : ∀ v, Continuous fun g => ρ g v)
    (l : V →L[ℝ] ℂ) (v : V) :
    (⟨fun g => l (ρ g v), l.continuous.comp (hρ v)⟩ : C(G,ℂ)) ∈ representativeFunctions (G := G) := by
  let b := Module.finBasis ℝ V
  convert coefficient_mem_representative (MatrixRepresentation.ofRealRepresentation b ρ hρ)
    (fun i => l (b i)) (fun j => (b.repr v j : ℂ)) using 1
  ext g
  exact (MatrixRepresentation.coefficient_ofRealRepresentation b ρ hρ l.toLinearMap v g).symm

end MathieuProperty
