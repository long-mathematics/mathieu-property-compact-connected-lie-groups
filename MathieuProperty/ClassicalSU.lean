import MathieuProperty.SphereBeta
import MathieuProperty.ProjectedRepresentatives
import MathieuProperty.ClassicalConstants
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Defining-representation marker towers and closed forms for every SU(n), n≥2.

The explicit continuous injective block embedding SU(2)→SU(2+n) makes the
first-two-coordinate projection equivariant. Its entries are actual matrix
coefficients. Radial transfer and the checked beta moments give the fixed
representative-function tower, strict positivity, exact vanishing ranges,
and failure of the Mathieu property. The final wrapper uses the manuscript
index n≥2, and the printed SU(2), SU(3), and SU(4) values are actual Haar moments.
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace MathieuProperty
open Hopf

def su2BlockMatrix (n : ℕ) (k : SU2) : Matrix (Fin (2 + n)) (Fin (2 + n)) ℂ :=
  Matrix.reindexRingEquiv ℂ finSumFinEquiv
    (Matrix.fromBlocks k.val 0 0 (1 : Matrix (Fin n) (Fin n) ℂ))

theorem su2BlockMatrix_mem (n : ℕ) (k : SU2) :
    su2BlockMatrix n k ∈ Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ := by
  let B := Matrix.fromBlocks k.val 0 0 (1 : Matrix (Fin n) (Fin n) ℂ)
  let e := Matrix.reindexRingEquiv ℂ (finSumFinEquiv : Fin 2 ⊕ Fin n ≃ Fin (2 + n))
  have hk : k.val * k.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp k.property.1
  have hB : B * Bᴴ = 1 := by
    simp [B, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hk]
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    change e B * e (Bᴴ) = 1
    rw [← map_mul, hB, map_one]
  · change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv B) = 1
    rw [Matrix.det_reindex_self]
    simpa [B] using k.property.2

def su2Block (n : ℕ) : SU2 →* Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ where
  toFun k := ⟨su2BlockMatrix n k, su2BlockMatrix_mem n k⟩
  map_one' := by
    apply Subtype.ext
    change su2BlockMatrix n 1 = 1
    simp [su2BlockMatrix]
  map_mul' k h := by
    apply Subtype.ext
    change su2BlockMatrix n (k * h) = su2BlockMatrix n k * su2BlockMatrix n h
    unfold su2BlockMatrix
    rw [← map_mul]
    congr 1
    simp [Matrix.fromBlocks_multiply]

def classicalProjection (n : ℕ) (g : Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) : Space :=
  (g.val (Fin.castAdd n 0) (Fin.castAdd n 0), g.val (Fin.castAdd n 1) (Fin.castAdd n 0))

theorem classicalProjection_equivariant (n : ℕ) (k : SU2)
    (g : Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) :
    classicalProjection n (su2Block n k * g) = k • classicalProjection n g := by
  rw [su2_smul_apply]
  ext <;> simp [classicalProjection, su2Block, su2BlockMatrix, Matrix.mul_apply,
    Fin.sum_univ_add, Fin.sum_univ_two, Matrix.reindexRingEquiv, Matrix.reindex_apply]

theorem classicalProjection_continuous (n : ℕ) : Continuous (classicalProjection n) :=
  (continuous_subtype_val.matrix_elem (Fin.castAdd n (0 : Fin 2)) (Fin.castAdd n (0 : Fin 2))).prodMk
    (continuous_subtype_val.matrix_elem (Fin.castAdd n (1 : Fin 2)) (Fin.castAdd n (0 : Fin 2)))

theorem classicalProjection_radial (n : ℕ)
    (g : Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) :
    a (classicalProjection n g) = specialUnitaryRadialA (2 + n) (by omega) g := rfl

def classicalDefiningRepresentation (n : ℕ) :
    MatrixRepresentation (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) (Fin (2 + n)) where
  toMonoidHom := (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ).subtype
  continuous_entry i j := continuous_subtype_val.matrix_elem i j

def classicalEntry (n : ℕ) (i : Fin 2) :
    representativeFunctions (G := Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) :=
  ⟨(classicalDefiningRepresentation n).entry (Fin.castAdd n i) (Fin.castAdd n 0),
    entry_mem_representative _ _ _⟩

def classicalA (n : ℕ) := representativeA (classicalEntry n 0) (classicalEntry n 1)
def classicalP (n : ℕ) := representativeP (classicalEntry n 0) (classicalEntry n 1)
def classicalQ (n : ℕ) := representativeQ (classicalEntry n 0) (classicalEntry n 1)

theorem classicalA_apply (n : ℕ) (g : Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) :
    (classicalA n).val g = (a (classicalProjection n g) : ℂ) := representativeA_apply _ _ _

theorem classicalP_apply (n : ℕ) (g : Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) :
    (classicalP n).val g = P (classicalProjection n g) := representativeP_apply _ _ _

theorem classicalQ_apply (n : ℕ) (g : Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) :
    (classicalQ n).val g = Q (classicalProjection n g) := representativeQ_apply _ _ _

theorem classical_representative_pure (n m : ℕ) (hm : 1 ≤ m) :
    representativeIntegral (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) (classicalP n ^ m) = 0 := by
  change (∫ g, (classicalP n).val g ^ m ∂normalizedHaar _) = 0
  simp_rw [classicalP_apply]
  exact (projected_haar_moments _ (classicalProjection_continuous n) (su2Block n)
    (classicalProjection_equivariant n)).1 m hm

theorem classical_representative_marked (n m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    representativeIntegral (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ)
      (classicalQ n ^ s * classicalP n ^ m) = (classicalMomentFormula (2 + n) m s : ℂ) := by
  change (∫ g, (classicalQ n).val g ^ s * (classicalP n).val g ^ m ∂normalizedHaar _) = _
  simp_rw [classicalP_apply, classicalQ_apply]
  rw [(projected_haar_moments _ (classicalProjection_continuous n) (su2Block n)
    (classicalProjection_equivariant n)).2 m s hm hs]
  simp_rw [classicalProjection_radial]
  rw [specialUnitaryRadialA_moment (2 + n) (4 * m + s) (by omega)]
  simp only [classicalMomentFormula, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

theorem su2Block_continuous (n : ℕ) : Continuous (su2Block n) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun k : SU2 => Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks k.val 0 0 (1 : Matrix (Fin n) (Fin n) ℂ)))
  exact (continuous_subtype_val.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _

theorem su2Block_injective (n : ℕ) : Function.Injective (su2Block n) := by
  intro k h heq
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun g : Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ =>
    g.val (Fin.castAdd n i) (Fin.castAdd n j)) heq
  simpa [su2Block, su2BlockMatrix, Matrix.reindexRingEquiv, Matrix.reindex_apply] using hh

theorem classicalProjection_one (n : ℕ) : classicalProjection n 1 = (1, 0) := by
  ext <;> simp [classicalProjection, Fin.ext_iff]

theorem classical_representative_radial (n k : ℕ) :
    representativeIntegral (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) (classicalA n ^ k) =
      (((2 : ℕ).ascFactorial k : ℝ) / ((2 + n).ascFactorial k : ℝ) : ℂ) := by
  change (∫ g, (classicalA n).val g ^ k ∂normalizedHaar _) = _
  simp_rw [classicalA_apply, ← Complex.ofReal_pow, classicalProjection_radial]
  rw [integral_complex_ofReal, specialUnitaryRadialA_moment (2 + n) k (by omega)]
  push_cast
  rfl

theorem classical_marker_tower (n m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    representativeIntegral (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ)
      (classicalQ n ^ s * classicalP n ^ m) =
      (momentConstant m : ℂ) * ((m - 1).choose (s - 1) : ℂ) *
        representativeIntegral (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) (classicalA n ^ (4 * m + s)) := by
  rw [classical_representative_marked n m s hm hs, classical_representative_radial]
  simp only [classicalMomentFormula, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

theorem classical_marked_positive (n m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∃ c : ℝ, 0 < c ∧ representativeIntegral (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ)
      (classicalQ n ^ s * classicalP n ^ m) = (c : ℂ) := by
  obtain ⟨c, hc, heq⟩ := projected_haar_positive _ (classicalProjection_continuous n) (su2Block n)
    (classicalProjection_equivariant n) (by rw [classicalProjection_one]; simp) m s hm hs hsm
  refine ⟨c, hc, ?_⟩
  change (∫ g, (classicalQ n).val g ^ s * (classicalP n).val g ^ m ∂normalizedHaar _) = (c : ℂ)
  simpa only [classicalQ_apply, classicalP_apply] using heq

theorem classical_marked_zero (n m s : ℕ) (hm : 1 ≤ m) (hsm : m < s) :
    representativeIntegral (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ)
      (classicalQ n ^ s * classicalP n ^ m) = 0 := by
  have hz : classicalMomentFormula (2 + n) m s = 0 := by
    unfold classicalMomentFormula
    rw [Nat.choose_eq_zero_of_lt (show m - 1 < s - 1 by omega)]
    simp
  calc
    _ = (classicalMomentFormula (2 + n) m s : ℂ) := classical_representative_marked n m s hm (by omega)
    _ = 0 := by rw [hz]; rfl

theorem classical_not_mathieu (n : ℕ) :
    ¬ HasMathieuProperty (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ) := by
  apply not_mathieu_of_representative_witness (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ)
    (classicalP n) (classicalQ n)
  · intro m hm
    exact classical_representative_pure n m hm
  · intro m hm
    obtain ⟨c, hc, heq⟩ := classical_marked_positive n m 1 hm (by omega) hm
    simp only [pow_one] at heq
    rw [heq]
    exact Complex.ofReal_ne_zero.mpr hc.ne'

theorem specialUnitary_not_mathieu (n : ℕ) (hn : 2 ≤ n) :
    ¬ HasMathieuProperty (Matrix.specialUnitaryGroup (Fin n) ℂ) := by
  obtain ⟨l, rfl⟩ : ∃ l, n = 2 + l := ⟨n - 2, by omega⟩
  exact classical_not_mathieu l

theorem classical_first_marker (n m : ℕ) (hm : 1 ≤ m) :
    representativeIntegral (Matrix.specialUnitaryGroup (Fin (2 + n)) ℂ)
      (classicalQ n * classicalP n ^ m) = (classicalMomentFormula (2 + n) m 1 : ℂ) := by
  simpa only [pow_one] using classical_representative_marked n m 1 hm (by omega)

theorem specialUnitary_small_values :
    representativeIntegral _ (classicalQ 0 * classicalP 0 ^ 1) = (2 / 3 : ℂ) ∧
    representativeIntegral _ (classicalQ 0 * classicalP 0 ^ 2) = (8 / 15 : ℂ) ∧
    representativeIntegral _ (classicalQ 0 * classicalP 0 ^ 3) = (16 / 35 : ℂ) ∧
    representativeIntegral _ (classicalQ 1 * classicalP 1 ^ 1) = (4 / 21 : ℂ) ∧
    representativeIntegral _ (classicalQ 1 * classicalP 1 ^ 2) = (16 / 165 : ℂ) ∧
    representativeIntegral _ (classicalQ 1 * classicalP 1 ^ 3) = (32 / 525 : ℂ) ∧
    representativeIntegral _ (classicalQ 2 * classicalP 2 ^ 1) = (1 / 14 : ℂ) ∧
    representativeIntegral _ (classicalQ 2 * classicalP 2 ^ 2) = (4 / 165 : ℂ) ∧
    representativeIntegral _ (classicalQ 2 * classicalP 2 ^ 3) = (2 / 175 : ℂ) := by
  simp only [classical_first_marker _ 1 (by omega), classical_first_marker _ 2 (by omega),
    classical_first_marker _ 3 (by omega)]
  norm_num [classicalMomentFormula, momentConstant_factorial, Nat.ascFactorial]

/-- Manuscript-facing defining-representation closed forms for every SU(n), n≥2. -/
theorem specialUnitary_closed_forms (n : ℕ) (hn : 2 ≤ n) :
    ∃ A P Q : representativeFunctions (G := Matrix.specialUnitaryGroup (Fin n) ℂ),
      (∀ g, A.val g = (specialUnitaryRadialA n hn g : ℂ)) ∧
      (∀ g, P.val g = Hopf.P (g.val ⟨0, by omega⟩ ⟨0, by omega⟩,
        g.val ⟨1, by omega⟩ ⟨0, by omega⟩)) ∧
      (∀ g, Q.val g = Hopf.Q (g.val ⟨0, by omega⟩ ⟨0, by omega⟩,
        g.val ⟨1, by omega⟩ ⟨0, by omega⟩)) ∧
      (∀ m : ℕ, 1 ≤ m → representativeIntegral (Matrix.specialUnitaryGroup (Fin n) ℂ) (P ^ m) = 0) ∧
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
        representativeIntegral (Matrix.specialUnitaryGroup (Fin n) ℂ) (Q ^ s * P ^ m) =
          (classicalMomentFormula n m s : ℂ)) := by
  obtain ⟨l, rfl⟩ : ∃ l, n = 2 + l := ⟨n - 2, by omega⟩
  refine ⟨classicalA l, classicalP l, classicalQ l, ?_, ?_, ?_,
    classical_representative_pure l, classical_representative_marked l⟩
  · intro g
    rw [classicalA_apply, classicalProjection_radial]
  · intro g
    exact classicalP_apply l g
  · intro g
    exact classicalQ_apply l g

end MathieuProperty
