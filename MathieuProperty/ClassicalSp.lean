import MathieuProperty.SymplecticOrbit
import MathieuProperty.ClassicalSU

/-! Defining-representation marker towers and closed forms for compact Sp(n).

For n≥2, the SU(2) block in the first two complex coordinates is doubled as
(A, conjugate A), giving the standard first-simple-root action in Sp(n).
The corresponding projection is equivariant and consists of actual matrix
coefficients. Radial transfer and the Haar moments give the exact marker
formula, strict positivity, vanishing range, and failure of the Mathieu
property. The n=1 case is transported through the proved Sp(1)=SU(2)
equivalence. The final wrapper includes every positive rank, and the printed
Sp(2) values are actual representative Haar moments.
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace MathieuProperty
open Hopf

def su2Symplectic (n : ℕ) : SU2 →* CompactSymplecticGroup (2 + n) :=
  (unitaryToCompactSymplectic (2 + n)).comp
    ((Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup).comp (su2Block n))

theorem su2Symplectic_matrix (n : ℕ) (k : SU2) :
    compactSymplecticMatrix (2 + n) (su2Symplectic n k) =
      unitaryDoubleMatrix (2 + n) (su2BlockMatrix n k) := by
  change symplecticReindex _ ((symplecticReindex _).symm _) = _
  exact RingEquiv.apply_symm_apply _ _

def symplecticProjection (n : ℕ) (g : CompactSymplecticGroup (2 + n)) : Space :=
  (compactSymplecticMatrix (2 + n) g (Sum.inl (Fin.castAdd n 0)) (Sum.inl (Fin.castAdd n 0)),
   compactSymplecticMatrix (2 + n) g (Sum.inl (Fin.castAdd n 1)) (Sum.inl (Fin.castAdd n 0)))

theorem symplecticProjection_equivariant (n : ℕ) (k : SU2)
    (g : CompactSymplecticGroup (2 + n)) :
    symplecticProjection n (su2Symplectic n k * g) = k • symplecticProjection n g := by
  rw [su2_smul_apply]
  simp only [symplecticProjection, map_mul, su2Symplectic_matrix]
  ext <;> simp [unitaryDoubleMatrix, su2BlockMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_add, Fin.sum_univ_two, Matrix.reindexRingEquiv, Matrix.reindex_apply]

theorem compactSymplecticMatrix_continuous (n : ℕ) : Continuous (compactSymplecticMatrix n) :=
  (continuous_subtype_val.comp continuous_subtype_val).matrix_reindex _ _

theorem symplecticProjection_continuous (n : ℕ) : Continuous (symplecticProjection n) :=
  ((compactSymplecticMatrix_continuous (2 + n)).matrix_elem _ _).prodMk
    ((compactSymplecticMatrix_continuous (2 + n)).matrix_elem _ _)

theorem symplecticProjection_radial (n : ℕ) (g : CompactSymplecticGroup (2 + n)) :
    a (symplecticProjection n g) = compactSymplecticRadialA (2 + n) (by omega) g := by
  rfl

theorem symplecticProjection_one (n : ℕ) : symplecticProjection n 1 = (1, 0) := by
  simp [symplecticProjection]

def symplecticDefiningRepresentation (n : ℕ) :
    MatrixRepresentation (CompactSymplecticGroup (2 + n)) (Fin (2 + n) ⊕ Fin (2 + n)) where
  toMonoidHom := compactSymplecticMatrix (2 + n)
  continuous_entry i j := (compactSymplecticMatrix_continuous (2 + n)).matrix_elem i j

def symplecticEntry (n : ℕ) (i : Fin 2) :
    representativeFunctions (G := CompactSymplecticGroup (2 + n)) :=
  ⟨(symplecticDefiningRepresentation n).entry (Sum.inl (Fin.castAdd n i)) (Sum.inl (Fin.castAdd n 0)),
    entry_mem_representative _ _ _⟩

def symplecticA (n : ℕ) := representativeA (symplecticEntry n 0) (symplecticEntry n 1)
def symplecticP (n : ℕ) := representativeP (symplecticEntry n 0) (symplecticEntry n 1)
def symplecticQ (n : ℕ) := representativeQ (symplecticEntry n 0) (symplecticEntry n 1)

theorem symplecticA_apply (n : ℕ) (g : CompactSymplecticGroup (2 + n)) :
    (symplecticA n).val g = (a (symplecticProjection n g) : ℂ) := representativeA_apply _ _ _

theorem symplecticP_apply (n : ℕ) (g : CompactSymplecticGroup (2 + n)) :
    (symplecticP n).val g = P (symplecticProjection n g) := representativeP_apply _ _ _

theorem symplecticQ_apply (n : ℕ) (g : CompactSymplecticGroup (2 + n)) :
    (symplecticQ n).val g = Q (symplecticProjection n g) := representativeQ_apply _ _ _

theorem symplectic_representative_pure (n m : ℕ) (hm : 1 ≤ m) :
    representativeIntegral (CompactSymplecticGroup (2 + n)) (symplecticP n ^ m) = 0 := by
  change (∫ g, (symplecticP n).val g ^ m ∂normalizedHaar _) = 0
  simp_rw [symplecticP_apply]
  exact (projected_haar_moments _ (symplecticProjection_continuous n) (su2Symplectic n)
    (symplecticProjection_equivariant n)).1 m hm

theorem symplectic_representative_marked (n m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    representativeIntegral (CompactSymplecticGroup (2 + n))
      (symplecticQ n ^ s * symplecticP n ^ m) = (classicalMomentFormula ((2 + n) + (2 + n)) m s : ℂ) := by
  change (∫ g, (symplecticQ n).val g ^ s * (symplecticP n).val g ^ m ∂normalizedHaar _) = _
  simp_rw [symplecticP_apply, symplecticQ_apply]
  rw [(projected_haar_moments _ (symplecticProjection_continuous n) (su2Symplectic n)
    (symplecticProjection_equivariant n)).2 m s hm hs]
  simp_rw [symplecticProjection_radial]
  rw [compactSymplecticRadialA_moment (2 + n) (4 * m + s) (by omega)]
  simp only [classicalMomentFormula, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

theorem symplectic_representative_radial (n k : ℕ) :
    representativeIntegral (CompactSymplecticGroup (2 + n)) (symplecticA n ^ k) =
      (((2 : ℕ).ascFactorial k : ℝ) / (((2 + n) + (2 + n)).ascFactorial k : ℝ) : ℂ) := by
  change (∫ g, (symplecticA n).val g ^ k ∂normalizedHaar _) = _
  simp_rw [symplecticA_apply, ← Complex.ofReal_pow, symplecticProjection_radial]
  rw [integral_complex_ofReal, compactSymplecticRadialA_moment (2 + n) k (by omega)]
  push_cast
  rfl

theorem symplectic_marker_tower (n m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    representativeIntegral (CompactSymplecticGroup (2 + n))
      (symplecticQ n ^ s * symplecticP n ^ m) =
      (momentConstant m : ℂ) * ((m - 1).choose (s - 1) : ℂ) *
        representativeIntegral (CompactSymplecticGroup (2 + n)) (symplecticA n ^ (4 * m + s)) := by
  rw [symplectic_representative_marked n m s hm hs, symplectic_representative_radial]
  simp only [classicalMomentFormula, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

theorem symplectic_marked_positive (n m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∃ c : ℝ, 0 < c ∧ representativeIntegral (CompactSymplecticGroup (2 + n))
      (symplecticQ n ^ s * symplecticP n ^ m) = (c : ℂ) := by
  obtain ⟨c, hc, heq⟩ := projected_haar_positive _ (symplecticProjection_continuous n) (su2Symplectic n)
    (symplecticProjection_equivariant n) (by rw [symplecticProjection_one]; simp) m s hm hs hsm
  refine ⟨c, hc, ?_⟩
  change (∫ g, (symplecticQ n).val g ^ s * (symplecticP n).val g ^ m ∂normalizedHaar _) = (c : ℂ)
  simpa only [symplecticQ_apply, symplecticP_apply] using heq

theorem symplectic_marked_zero (n m s : ℕ) (hm : 1 ≤ m) (hsm : m < s) :
    representativeIntegral (CompactSymplecticGroup (2 + n))
      (symplecticQ n ^ s * symplecticP n ^ m) = 0 := by
  have hz : classicalMomentFormula ((2 + n) + (2 + n)) m s = 0 := by
    unfold classicalMomentFormula
    rw [Nat.choose_eq_zero_of_lt (show m - 1 < s - 1 by omega)]
    simp
  calc
    _ = (classicalMomentFormula ((2 + n) + (2 + n)) m s : ℂ) := symplectic_representative_marked n m s hm (by omega)
    _ = 0 := by rw [hz]; rfl

theorem symplectic_not_mathieu (n : ℕ) :
    ¬ HasMathieuProperty (CompactSymplecticGroup (2 + n)) := by
  apply not_mathieu_of_representative_witness (CompactSymplecticGroup (2 + n))
    (symplecticP n) (symplecticQ n)
  · intro m hm
    exact symplectic_representative_pure n m hm
  · intro m hm
    obtain ⟨c, hc, heq⟩ := symplectic_marked_positive n m 1 hm (by omega) hm
    simp only [pow_one] at heq
    rw [heq]
    exact Complex.ofReal_ne_zero.mpr hc.ne'

theorem symplectic_first_marker (n m : ℕ) (hm : 1 ≤ m) :
    representativeIntegral (CompactSymplecticGroup (2 + n))
      (symplecticQ n * symplecticP n ^ m) = (classicalMomentFormula ((2 + n) + (2 + n)) m 1 : ℂ) := by
  simpa only [pow_one] using symplectic_representative_marked n m 1 hm (by omega)

theorem unitaryToCompactSymplectic_continuous (n : ℕ) : Continuous (unitaryToCompactSymplectic n) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (fun A : Matrix.unitaryGroup (Fin n) ℂ =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv (unitaryDoubleMatrix n A.val))
  exact (continuous_subtype_val.matrix_fromBlocks continuous_const continuous_const
    (continuous_subtype_val.matrix_map continuous_star)).matrix_reindex _ _

theorem su2Symplectic_continuous (n : ℕ) : Continuous (su2Symplectic n) :=
  (unitaryToCompactSymplectic_continuous (2 + n)).comp
    ((continuous_subtype_val.comp (su2Block_continuous n)).subtype_mk _)

theorem su2Symplectic_injective (n : ℕ) : Function.Injective (su2Symplectic n) := by
  intro k h heq
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun g : CompactSymplecticGroup (2 + n) =>
    compactSymplecticMatrix (2 + n) g (Sum.inl (Fin.castAdd n i)) (Sum.inl (Fin.castAdd n j))) heq
  simpa [su2Symplectic_matrix, unitaryDoubleMatrix, su2BlockMatrix,
    Matrix.reindexRingEquiv, Matrix.reindex_apply] using hh

theorem compactSymplectic_small_values :
    representativeIntegral _ (symplecticQ 0 * symplecticP 0 ^ 1) = (1 / 14 : ℂ) ∧
    representativeIntegral _ (symplecticQ 0 * symplecticP 0 ^ 2) = (4 / 165 : ℂ) ∧
    representativeIntegral _ (symplecticQ 0 * symplecticP 0 ^ 3) = (2 / 175 : ℂ) := by
  simp only [symplectic_first_marker _ 1 (by omega), symplectic_first_marker _ 2 (by omega),
    symplectic_first_marker _ 3 (by omega)]
  norm_num [classicalMomentFormula, momentConstant_factorial, Nat.ascFactorial]

theorem compactSymplecticInclusion_one_surjective : Function.Surjective (compactSymplecticInclusion 1) :=
  su2CompactSymplecticOne.symm.surjective

theorem compactSymplectic_not_mathieu (n : ℕ) (hn : 1 ≤ n) :
    ¬ HasMathieuProperty (CompactSymplecticGroup n) := by
  by_cases hn1 : n = 1
  · subst n
    exact not_mathieuProperty_of_quotient (compactSymplecticInclusion 1) continuous_subtype_val
      compactSymplecticInclusion_one_surjective SU2_not_mathieu
  · obtain ⟨l, rfl⟩ : ∃ l, n = 2 + l := ⟨n - 2, by omega⟩
    exact symplectic_not_mathieu l

private theorem compactSymplectic_closed_forms_one :
    ∃ A P Q : representativeFunctions (G := CompactSymplecticGroup 1),
      (∀ g, A.val g = (compactSymplecticRadialA 1 (by omega) g : ℂ)) ∧
      (∀ g, P.val g = Hopf.P ((compactSymplecticInclusion 1 g).val ⟨0, by omega⟩ ⟨0, by omega⟩,
        (compactSymplecticInclusion 1 g).val ⟨1, by omega⟩ ⟨0, by omega⟩)) ∧
      (∀ g, Q.val g = Hopf.Q ((compactSymplecticInclusion 1 g).val ⟨0, by omega⟩ ⟨0, by omega⟩,
        (compactSymplecticInclusion 1 g).val ⟨1, by omega⟩ ⟨0, by omega⟩)) ∧
      (∀ m : ℕ, 1 ≤ m → representativeIntegral (CompactSymplecticGroup 1) (P ^ m) = 0) ∧
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
        representativeIntegral (CompactSymplecticGroup 1) (Q ^ s * P ^ m) =
          (classicalMomentFormula 2 m s : ℂ)) := by
  obtain ⟨A, P, Q, hA, hP, hQ, hpure, hmarked⟩ := specialUnitary_closed_forms 2 (by omega)
  let F := representativePullback (compactSymplecticInclusion 1) (compactSymplecticInclusion_continuous 1)
  refine ⟨F A, F P, F Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact hA (compactSymplecticInclusion 1 g)
  · intro g
    exact hP (compactSymplecticInclusion 1 g)
  · intro g
    exact hQ (compactSymplecticInclusion 1 g)
  · intro m hm
    rw [← map_pow]
    exact (representativeIntegral_pullback _ _ compactSymplecticInclusion_one_surjective (P ^ m)).trans (hpure m hm)
  · intro m s hm hs
    rw [← map_pow, ← map_pow, ← map_mul]
    exact (representativeIntegral_pullback _ _ compactSymplecticInclusion_one_surjective (Q ^ s * P ^ m)).trans (hmarked m s hm hs)

/-- Manuscript-facing defining-representation closed forms for all compact Sp(n), n≥1. -/
theorem compactSymplectic_closed_forms (n : ℕ) (hn : 1 ≤ n) :
    ∃ A P Q : representativeFunctions (G := CompactSymplecticGroup n),
      (∀ g, A.val g = (compactSymplecticRadialA n hn g : ℂ)) ∧
      (∀ g, P.val g = Hopf.P ((compactSymplecticInclusion n g).val ⟨0, by omega⟩ ⟨0, by omega⟩,
        (compactSymplecticInclusion n g).val ⟨1, by omega⟩ ⟨0, by omega⟩)) ∧
      (∀ g, Q.val g = Hopf.Q ((compactSymplecticInclusion n g).val ⟨0, by omega⟩ ⟨0, by omega⟩,
        (compactSymplecticInclusion n g).val ⟨1, by omega⟩ ⟨0, by omega⟩)) ∧
      (∀ m : ℕ, 1 ≤ m → representativeIntegral (CompactSymplecticGroup n) (P ^ m) = 0) ∧
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
        representativeIntegral (CompactSymplecticGroup n) (Q ^ s * P ^ m) =
          (classicalMomentFormula (n + n) m s : ℂ)) := by
  by_cases hn1 : n = 1
  · subst n
    exact compactSymplectic_closed_forms_one
  · obtain ⟨l, rfl⟩ : ∃ l, n = 2 + l := ⟨n - 2, by omega⟩
    refine ⟨symplecticA l, symplecticP l, symplecticQ l, ?_, ?_, ?_,
      symplectic_representative_pure l, symplectic_representative_marked l⟩
    · intro g
      rw [symplecticA_apply, symplecticProjection_radial]
    · intro g
      exact symplecticP_apply l g
    · intro g
      exact symplecticQ_apply l g

end MathieuProperty
