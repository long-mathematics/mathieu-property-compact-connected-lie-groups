import MathieuProperty.ZwartLaurent
import Mathlib.Algebra.MvPolynomial.Eval

/-! Zwart's radical-polynomial coefficient algebra on a unit cube, with a
proved direct counterexample whenever a radial coordinate has linear weight.
The actual circle Haar integral is connected to the coefficient functional in
`ZwartLaurent.lean`. -/

noncomputable section
open MeasureTheory Polynomial
open scoped unitInterval
namespace MathieuProperty.Zwart

abbrev Cube (N : ℕ) := Fin N → I

def coordinate (N : ℕ) (i : Fin N) : C(Cube N,ℂ) :=
  ⟨fun x => ((x i).val : ℂ), by fun_prop⟩

def radical (N : ℕ) (i : Fin N) : C(Cube N,ℂ) :=
  ⟨fun x => (Real.sqrt (1 - (x i).val ^ 2) : ℂ), by fun_prop⟩

/-- The algebra in Zwart 2025, Definition 2.8, with coefficient equality
interpreted as equality of functions on the cube. -/
def radialAlgebra (N : ℕ) : Subalgebra ℂ C(Cube N,ℂ) :=
  Algebra.adjoin ℂ (Set.range (coordinate N) ∪ Set.range (radical N))

theorem radialAlgebra_eq_range (N : ℕ) : radialAlgebra N =
    (MvPolynomial.aeval (Sum.elim (coordinate N) (radical N))).range := by
  rw [radialAlgebra, ← Set.Sum.elim_range, Algebra.adjoin_range_eq_range_aeval]

theorem mem_radialAlgebra_iff (N : ℕ) (f : C(Cube N,ℂ)) :
    f ∈ radialAlgebra N ↔ ∃ p : MvPolynomial (Fin N ⊕ Fin N) ℂ,
      MvPolynomial.aeval (Sum.elim (coordinate N) (radical N)) p = f := by
  rw [radialAlgebra_eq_range]
  rfl

theorem coordinate_mem (N : ℕ) (i : Fin N) : coordinate N i ∈ radialAlgebra N :=
  Algebra.subset_adjoin (Or.inl ⟨i,rfl⟩)

theorem cube_integral_first (N : ℕ) (f : I → ℂ) (W : Cube N → ℂ) :
    (∫ x : Cube (N+1), f (x 0) * W (Fin.tail x)) =
      (∫ t : I, f t) * ∫ y : Cube N, W y := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (N+1) => I) 0).symm
  have hi := hp.integral_comp' (fun x : Cube (N+1) => f (x 0) * W (Fin.tail x))
  rw [← hi]
  convert integral_prod_mul (μ := (volume : Measure I))
    (ν := (volume : Measure (Cube N))) f W using 1
  congr 1

def cubeLinearWeight {N : ℕ} (W : Cube N → ℂ) (x : Cube (N+1)) : ℂ :=
  ((x 0).val : ℂ) * W (Fin.tail x)

theorem cube_weight_moments (N : ℕ) {M : ℕ} (i : Fin M)
    (W : Cube N → ℂ) (f : Abelian.Laurent) :
    weightedMoment volume (cubeLinearWeight W) (embed (coordinate (N+1) 0) i f) =
      (Abelian.weightedCT f / 2) * ∫ y : Cube N, W y := by
  unfold weightedMoment
  simp_rw [embed_coeff_zero, aeval_continuousMap_apply]
  change (∫ x : Cube (N+1), (f.coeff 0).eval ((x 0).val : ℂ) *
    (((x 0).val : ℂ) * W (Fin.tail x))) = _
  simp_rw [← mul_assoc]
  rw [cube_integral_first N (fun t : I => (f.coeff 0).eval (t.val : ℂ) * (t.val : ℂ)) W]
  congr 1
  rw [Hopf.integral_unitInterval (fun t : ℝ => (f.coeff 0).eval (t : ℂ) * (t : ℂ))]
  unfold Abelian.weightedCT
  ring

theorem cube_witness_zero_mem (N : ℕ) {M : ℕ} (i : Fin M) :
    0 ∈ newtonPolytope (embed (coordinate (N+1) 0) i Abelian.formalP) := by
  apply subset_convexHull ℝ _
  refine ⟨0, ?_, by ext j; simp [exponentVector]⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, embed_coeff_zero]
  intro h
  have he := congrArg (fun g : C(Cube (N+1),ℂ) => g 0) h
  rw [aeval_continuousMap_apply] at he
  norm_num [coordinate, Abelian.formal_coeff, Abelian.coeffZero] at he

/-- A direct counterexample for every remaining radial weight W; no group
parametrization or conjecture-to-group implication is assumed. -/
theorem cube_convexSupport_false (N : ℕ) {M : ℕ} (i : Fin M) (W : Cube N → ℂ) :
    ¬ ConvexSupportConjecture M (radialAlgebra (N+1)) volume (cubeLinearWeight W) := by
  intro h
  apply h (embed (coordinate (N+1) 0) i Abelian.formalP)
    (embed_admissible _ _ (coordinate_mem (N+1) 0) i _)
    (fun m hm => ?_) (cube_witness_zero_mem N i)
  rw [← map_pow, cube_weight_moments, Abelian.weightedCT_pure m hm, zero_div, zero_mul]

end MathieuProperty.Zwart
