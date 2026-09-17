import MathieuProperty.ZwartFlatInterval
import MathieuProperty.ZwartPunctured

/-! Flat-coordinate counterexamples on signed cubes, independently of a group Jacobian. -/

noncomputable section
open MeasureTheory Polynomial
namespace MathieuProperty.Zwart

abbrev SignedCube (N : ℕ) := Fin N → SignedInterval

def signedCubeCoordinate (N : ℕ) (i : Fin N) : C(SignedCube N,ℂ) :=
  ⟨fun x => ((x i).val : ℂ), by fun_prop⟩

def signedCubeRadical (N : ℕ) (i : Fin N) : C(SignedCube N,ℂ) :=
  ⟨fun x => (Real.sqrt (1-(x i).val^2) : ℂ), by fun_prop⟩

def signedRadialAlgebra (N : ℕ) : Subalgebra ℂ C(SignedCube N,ℂ) :=
  Algebra.adjoin ℂ (Set.range (signedCubeCoordinate N) ∪ Set.range (signedCubeRadical N))

theorem signedRadialAlgebra_eq_range (N : ℕ) : signedRadialAlgebra N =
    (MvPolynomial.aeval (Sum.elim (signedCubeCoordinate N) (signedCubeRadical N))).range := by
  rw [signedRadialAlgebra, ← Set.Sum.elim_range, Algebra.adjoin_range_eq_range_aeval]

def signedCubeParameter (N : ℕ) : C(SignedCube (N+1),ℂ) :=
  (signedCubeCoordinate (N+1) 0 + 1) * ContinuousMap.const _ (1/2)

theorem signedCubeParameter_mem (N : ℕ) : signedCubeParameter N ∈ signedRadialAlgebra (N+1) := by
  apply (signedRadialAlgebra (N+1)).mul_mem
  · apply (signedRadialAlgebra (N+1)).add_mem
    · exact Algebra.subset_adjoin (Or.inl ⟨0,rfl⟩)
    · exact (signedRadialAlgebra (N+1)).one_mem
  · exact (signedRadialAlgebra (N+1)).algebraMap_mem (1/2)

theorem signedCube_integral_first (N : ℕ) (f : SignedInterval → ℂ) (W : SignedCube N → ℂ) :
    (∫ x : SignedCube (N+1), f (x 0) * W (Fin.tail x)) =
      (∫ t : SignedInterval, f t) * ∫ y : SignedCube N, W y := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (N+1) => SignedInterval) 0).symm
  have hi := hp.integral_comp' (fun x : SignedCube (N+1) => f (x 0) * W (Fin.tail x))
  rw [← hi]
  convert integral_prod_mul (μ := (volume : Measure SignedInterval))
    (ν := (volume : Measure (SignedCube N))) f W using 1
  congr 1

theorem signedCube_pure (N : ℕ) {M : ℕ} (i : Fin M) (W : SignedCube N → ℂ)
    (m : ℕ) (hm : 1 ≤ m) :
    weightedMoment volume (fun x : SignedCube (N+1) => W (Fin.tail x))
      (embed (signedCubeParameter N) i flatXZ ^ m) = 0 := by
  rw [← map_pow]
  unfold weightedMoment
  simp_rw [embed_coeff_zero, aeval_continuousMap_apply]
  change (∫ x : SignedCube (N+1),
    ((flatXZ^m).coeff 0).eval ((((x 0).val : ℂ)+1)*(1/2)) * W (Fin.tail x)) = 0
  simp only [one_div, ← div_eq_mul_inv]
  rw [signedCube_integral_first N
    (fun t : SignedInterval => ((flatXZ^m).coeff 0).eval (((t.val : ℂ)+1)/2)) W,
    flatXZ_signed_integral m hm, zero_mul]

theorem signedCube_witness_zero_mem (N : ℕ) {M : ℕ} (i : Fin M) :
    0 ∈ newtonPolytope (embed (signedCubeParameter N) i flatXZ) := by
  apply subset_convexHull ℝ _
  refine ⟨0, ?_, by ext j; simp [exponentVector]⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, embed_coeff_zero]
  intro h
  have he := congrArg (fun g : C(SignedCube (N+1),ℂ) => g (fun _ => ⟨1,by norm_num⟩)) h
  rw [aeval_continuousMap_apply, flatXZ_coeff_zero] at he
  norm_num [signedCubeParameter, signedCubeCoordinate] at he

theorem signedCube_convexSupport_false (N : ℕ) {M : ℕ} (i : Fin M) (W : SignedCube N → ℂ) :
    ¬ ConvexSupportConjecture M (signedRadialAlgebra (N+1)) volume
      (fun x : SignedCube (N+1) => W (Fin.tail x)) := by
  intro h
  exact h (embed (signedCubeParameter N) i flatXZ)
    (embed_admissible _ _ (signedCubeParameter_mem N) i _)
    (signedCube_pure N i W) (signedCube_witness_zero_mem N i)

theorem signedCube_fractionalConvexSupport_false (N : ℕ) {D M : ℕ} (hD : 1 ≤ D)
    (i : Fin M) (W : SignedCube N → ℂ) :
    ¬ FractionalConvexSupportConjecture D M (signedRadialAlgebra (N+1)) volume
      (fun x : SignedCube (N+1) => W (Fin.tail x)) := by
  intro h
  exact signedCube_convexSupport_false N i W (fractional_conjecture_implies_integer hD _ _ _ h)
end MathieuProperty.Zwart
