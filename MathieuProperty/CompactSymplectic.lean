import MathieuProperty.ClassicalOrbit
import MathieuProperty.SU2Orbit
import Mathlib.LinearAlgebra.SymplecticGroup

/-! The compact symplectic matrix group and its first-column geometry.

The group is the closed unitary symplectic subgroup, represented inside SU(2n).
Mathlib's determinant theorem proves that the determinant-one condition adds
no restriction. Every complex unit vector is a first column: a real orthogonal
matrix supplies the pair radii, and independent SU(2) rotations supply each
pair. This construction includes zero pairs without dividing by their radii.
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace MathieuProperty
open Hopf

def symplecticReindex (n : ℕ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℂ ≃+* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.reindexRingEquiv ℂ finSumFinEquiv.symm

def compactSymplecticSubgroup (n : ℕ) :
    Subgroup (Matrix.specialUnitaryGroup (Fin (n + n)) ℂ) where
  carrier := {g | symplecticReindex n g.val ∈ Matrix.symplecticGroup (Fin n) ℂ}
  one_mem' := by
    change symplecticReindex n 1 ∈ Matrix.symplecticGroup (Fin n) ℂ
    rw [map_one]
    exact (Matrix.symplecticGroup (Fin n) ℂ).one_mem
  mul_mem' {g h} hg hh := by
    change symplecticReindex n (g.val * h.val) ∈ Matrix.symplecticGroup (Fin n) ℂ
    rw [map_mul]
    exact (Matrix.symplecticGroup (Fin n) ℂ).mul_mem hg hh
  inv_mem' {g} hg := by
    change (symplecticReindex n g.val)ᴴ ∈ Matrix.symplecticGroup (Fin n) ℂ
    exact SymplecticGroup.map_mem (SymplecticGroup.transpose_mem hg) (starRingEnd ℂ)

abbrev CompactSymplecticGroup (n : ℕ) := compactSymplecticSubgroup n

def compactSymplecticInclusion (n : ℕ) :
    CompactSymplecticGroup n →* Matrix.specialUnitaryGroup (Fin (n + n)) ℂ :=
  (compactSymplecticSubgroup n).subtype

theorem compactSymplectic_closed (n : ℕ) :
    IsClosed (compactSymplecticSubgroup n : Set (Matrix.specialUnitaryGroup (Fin (n + n)) ℂ)) := by
  have hc : Continuous (fun g : Matrix.specialUnitaryGroup (Fin (n + n)) ℂ => symplecticReindex n g.val) :=
    continuous_subtype_val.matrix_reindex _ _
  change IsClosed {g : Matrix.specialUnitaryGroup (Fin (n + n)) ℂ |
    symplecticReindex n g.val * Matrix.J (Fin n) ℂ * (symplecticReindex n g.val)ᵀ = Matrix.J (Fin n) ℂ}
  exact isClosed_eq ((hc.mul continuous_const).mul hc.matrix_transpose) continuous_const

instance compactSymplecticCompactSpace (n : ℕ) : CompactSpace (CompactSymplecticGroup n) :=
  isCompact_iff_compactSpace.mp (compactSymplectic_closed n).isCompact

theorem compactSymplecticInclusion_continuous (n : ℕ) : Continuous (compactSymplecticInclusion n) :=
  continuous_subtype_val

theorem symplecticReindex_symm_mem_specialUnitary (n : ℕ)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ)
    (hs : M ∈ Matrix.symplecticGroup (Fin n) ℂ) :
    (symplecticReindex n).symm M ∈ Matrix.specialUnitaryGroup (Fin (n + n)) ℂ := by
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    change (symplecticReindex n).symm M * (symplecticReindex n).symm (Mᴴ) = 1
    have hu' : M * Mᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hu
    rw [← map_mul, hu', map_one]
  · change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv M) = 1
    rw [Matrix.det_reindex_self]
    exact SymplecticGroup.det_eq_one hs

def compactSymplecticOfMatrix (n : ℕ)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ)
    (hs : M ∈ Matrix.symplecticGroup (Fin n) ℂ) : CompactSymplecticGroup n :=
  ⟨⟨(symplecticReindex n).symm M, symplecticReindex_symm_mem_specialUnitary n M hu hs⟩,
    by
      change symplecticReindex n ((symplecticReindex n).symm M) ∈ Matrix.symplecticGroup (Fin n) ℂ
      simpa using hs⟩

def compactSymplecticMatrix (n : ℕ) :
    CompactSymplecticGroup n →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (symplecticReindex n).toMonoidHom.comp
    ((Matrix.specialUnitaryGroup (Fin (n + n)) ℂ).subtype.comp (compactSymplecticInclusion n))

theorem compactSymplecticOfMatrix_apply (n : ℕ)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ)
    (hs : M ∈ Matrix.symplecticGroup (Fin n) ℂ) :
    compactSymplecticMatrix n (compactSymplecticOfMatrix n M hu hs) = M := by
  change symplecticReindex n ((symplecticReindex n).symm M) = M
  exact RingEquiv.apply_symm_apply _ _

def pairedMatrix (n : ℕ) (k : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks (Matrix.diagonal fun i => k i 0 0)
    (Matrix.diagonal fun i => k i 0 1) (Matrix.diagonal fun i => k i 1 0)
    (Matrix.diagonal fun i => k i 1 1)

theorem pairedMatrix_mul (n : ℕ) (k h : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    pairedMatrix n (fun i => k i * h i) = pairedMatrix n k * pairedMatrix n h := by
  simp only [pairedMatrix, Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal]
  congr 1 <;> funext i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem pairedMatrix_one (n : ℕ) : pairedMatrix n (fun _ => 1) = 1 := by
  simp [pairedMatrix]

theorem pairedMatrix_star (n : ℕ) (k : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    pairedMatrix n (fun i => (k i)ᴴ) = (pairedMatrix n k)ᴴ := by
  simp [pairedMatrix, Matrix.fromBlocks_conjTranspose]

theorem pairedMatrix_unitary (n : ℕ) (k : Fin n → SU2) :
    pairedMatrix n (fun i => (k i).val) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change pairedMatrix n (fun i => (k i).val) * (pairedMatrix n (fun i => (k i).val))ᴴ = 1
  rw [← pairedMatrix_star, ← pairedMatrix_mul]
  have hk : (fun i => (k i).val * ((k i).val)ᴴ) = fun _ => 1 := by
    funext i
    exact Matrix.mem_unitaryGroup_iff.mp (k i).property.1
  rw [hk, pairedMatrix_one]

theorem pairedMatrix_symplectic (n : ℕ) (k : Fin n → SU2) :
    pairedMatrix n (fun i => (k i).val) ∈ Matrix.symplecticGroup (Fin n) ℂ := by
  rw [pairedMatrix, SymplecticGroup.fromBlocks_mem_iff]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  refine ⟨?_, ?_, ?_⟩
  · congr 1; funext i; exact mul_comm _ _
  · congr 1; funext i; exact mul_comm _ _
  · have hd : (fun i => (k i).val 0 0 * (k i).val 1 1 - (k i).val 1 0 * (k i).val 0 1) = fun _ => (1 : ℂ) := by
      funext i
      have hk := (k i).property.2
      change (k i).val.det = 1 at hk
      simpa [Matrix.det_fin_two, mul_comm] using hk
    rw [Matrix.diagonal_sub, hd, Matrix.diagonal_one]

theorem exists_real_unitary_firstColumn {n : ℕ} [NeZero n]
    (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℝ, ∀ i, U.val i 0 = z i := by
  have hv : Orthonormal ℝ (({0} : Set (Fin n)).domRestrict (fun _ => z)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hz
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let a := EuclideanSpace.basisFun (Fin n) ℝ
  refine ⟨⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b⟩, fun i => ?_⟩
  change a.toBasis.repr (b 0) i = z i
  rw [hb 0 (by simp)]
  rfl

def unitaryDoubleMatrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ))

theorem unitaryDoubleMatrix_unitary (n : ℕ) (A : Matrix.unitaryGroup (Fin n) ℂ) :
    unitaryDoubleMatrix n A.val ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  have hA : A.val * A.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp A.property
  have hb : A.val.map (starRingEnd ℂ) * (A.val.map (starRingEnd ℂ))ᴴ = 1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)) hA
    rw [Matrix.map_mul, Matrix.conjTranspose_map (starRingEnd ℂ) (by intro x; rfl)] at h
    simpa using h
  apply Matrix.mem_unitaryGroup_iff.mpr
  change unitaryDoubleMatrix n A.val * (unitaryDoubleMatrix n A.val)ᴴ = 1
  simp [unitaryDoubleMatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hA, hb]

theorem unitaryDoubleMatrix_symplectic (n : ℕ) (A : Matrix.unitaryGroup (Fin n) ℂ) :
    unitaryDoubleMatrix n A.val ∈ Matrix.symplecticGroup (Fin n) ℂ := by
  have hA : A.valᴴ * A.val = 1 := Matrix.mem_unitaryGroup_iff'.mp A.property
  have ht : A.valᵀ * A.val.map (starRingEnd ℂ) = 1 := by
    have h := congrArg Matrix.transpose hA
    rw [Matrix.transpose_mul] at h
    change A.valᵀ * A.val.map (starRingEnd ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ at h
    simpa using h
  simpa [unitaryDoubleMatrix, SymplecticGroup.fromBlocks_mem_iff] using ht

def unitaryToCompactSymplectic (n : ℕ) :
    Matrix.unitaryGroup (Fin n) ℂ →* CompactSymplecticGroup n where
  toFun A := compactSymplecticOfMatrix n (unitaryDoubleMatrix n A.val)
    (unitaryDoubleMatrix_unitary n A) (unitaryDoubleMatrix_symplectic n A)
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    change (symplecticReindex n).symm (unitaryDoubleMatrix n 1) = 1
    simp [unitaryDoubleMatrix, map_one]
  map_mul' A B := by
    apply Subtype.ext; apply Subtype.ext
    change (symplecticReindex n).symm (unitaryDoubleMatrix n (A.val * B.val)) =
      (symplecticReindex n).symm (unitaryDoubleMatrix n A.val) *
      (symplecticReindex n).symm (unitaryDoubleMatrix n B.val)
    rw [← map_mul]
    congr 1
    simp [unitaryDoubleMatrix, Matrix.fromBlocks_multiply, Matrix.map_mul]

def realUnitaryComplexify {n : ℕ} (O : Matrix.unitaryGroup (Fin n) ℝ) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨O.val.map Complex.ofRealHom, by
    apply Matrix.mem_unitaryGroup_iff.mpr
    have hO : O.val * O.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp O.property
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.map Complex.ofRealHom) hO
    rw [Matrix.map_mul, Matrix.conjTranspose_map Complex.ofRealHom (by intro x; simp)] at h
    exact h.trans (by simp)⟩

theorem exists_unitary_symplectic_firstColumn {n : ℕ} [NeZero n]
    (z : EuclideanSpace ℂ (Fin n ⊕ Fin n)) (hz : ‖z‖ = 1) :
    ∃ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ,
      M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ ∧
      M ∈ Matrix.symplecticGroup (Fin n) ℂ ∧ ∀ i, M i (Sum.inl 0) = z i := by
  let r : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i =>
    Real.sqrt (Complex.normSq (z (Sum.inl i)) + Complex.normSq (z (Sum.inr i))))
  have hr (i : Fin n) : (r i) ^ 2 =
      Complex.normSq (z (Sum.inl i)) + Complex.normSq (z (Sum.inr i)) :=
    Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  have hsum : ∑ i, (r i) ^ 2 = 1 := by
    simp_rw [hr, Finset.sum_add_distrib, Complex.normSq_eq_norm_sq]
    have h := EuclideanSpace.norm_sq_eq z
    rw [hz, one_pow] at h
    simpa only [Fintype.sum_sum_type] using h.symm
  have hrnorm : ‖r‖ = 1 := by
    have h := EuclideanSpace.norm_sq_eq r
    simp only [Real.norm_eq_abs, sq_abs] at h
    rw [hsum] at h
    nlinarith [norm_nonneg r]
  obtain ⟨O, hO⟩ := exists_real_unitary_firstColumn r hrnorm
  have hk (i : Fin n) : ∃ k : SU2,
      k • ((r i : ℂ), 0) = (z (Sum.inl i), z (Sum.inr i)) := by
    apply SU2_transitive_equal_a
    simpa [a, Complex.normSq_ofReal, pow_two] using hr i
  choose k hk using hk
  let D := pairedMatrix n (fun i => (k i).val)
  let B := unitaryDoubleMatrix n (realUnitaryComplexify O).val
  refine ⟨D * B, (Matrix.unitaryGroup _ ℂ).mul_mem (pairedMatrix_unitary n k)
    (unitaryDoubleMatrix_unitary n _), (Matrix.symplecticGroup _ ℂ).mul_mem
    (pairedMatrix_symplectic n k) (unitaryDoubleMatrix_symplectic n _), ?_⟩
  intro i
  have htop (j : Fin n) : (k j).val 0 0 * (r j : ℂ) = z (Sum.inl j) := by
    have h := congrArg Prod.fst (hk j)
    simpa [su2_smul_apply] using h
  have hbot (j : Fin n) : (k j).val 1 0 * (r j : ℂ) = z (Sum.inr j) := by
    have h := congrArg Prod.snd (hk j)
    simpa [su2_smul_apply] using h
  cases i with
  | inl i =>
    simpa [D, B, pairedMatrix, unitaryDoubleMatrix, Matrix.fromBlocks_multiply,
      Matrix.diagonal_mul, realUnitaryComplexify, hO] using htop i
  | inr i =>
    simpa [D, B, pairedMatrix, unitaryDoubleMatrix, Matrix.fromBlocks_multiply,
      Matrix.diagonal_mul, realUnitaryComplexify, hO] using hbot i

theorem exists_compactSymplectic_firstColumn {n : ℕ} [NeZero n]
    (z : EuclideanSpace ℂ (Fin (n + n))) (hz : ‖z‖ = 1) :
    ∃ g : CompactSymplecticGroup n, ∀ i, (compactSymplecticInclusion n g).val i 0 = z i := by
  let w : EuclideanSpace ℂ (Fin n ⊕ Fin n) := WithLp.toLp 2 (fun i => z (finSumFinEquiv i))
  have hw : ‖w‖ = 1 := by
    have h := EuclideanSpace.norm_sq_eq w
    change ‖w‖ ^ 2 = ∑ i, ‖z (finSumFinEquiv i)‖ ^ 2 at h
    rw [Equiv.sum_comp finSumFinEquiv (fun i => ‖z i‖ ^ 2), ← EuclideanSpace.norm_sq_eq, hz, one_pow] at h
    nlinarith [norm_nonneg w]
  obtain ⟨M, hu, hs, hM⟩ := exists_unitary_symplectic_firstColumn w hw
  refine ⟨compactSymplecticOfMatrix n M hu hs, fun i => ?_⟩
  change Matrix.reindex finSumFinEquiv finSumFinEquiv M i 0 = z i
  have hzero : finSumFinEquiv.symm (0 : Fin (n + n)) = Sum.inl (0 : Fin n) := by
    apply finSumFinEquiv.injective
    simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left]
    apply Fin.ext
    rfl
  simpa [Matrix.reindex_apply, hzero, w] using hM (finSumFinEquiv.symm i)

theorem compactSymplectic_rank_one_mem (g : SU2) :
    g ∈ compactSymplecticSubgroup 1 := by
  have he : symplecticReindex 1 g.val = pairedMatrix 1 (fun _ => g.val) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [symplecticReindex, pairedMatrix, Matrix.reindexRingEquiv, Matrix.reindex_apply] <;> rfl
  change symplecticReindex 1 g.val ∈ Matrix.symplecticGroup (Fin 1) ℂ
  rw [he]
  exact pairedMatrix_symplectic 1 (fun _ => g)

theorem compactSymplectic_rank_one_top : compactSymplecticSubgroup 1 = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  exact compactSymplectic_rank_one_mem g

def su2CompactSymplecticOne : SU2 ≃* CompactSymplecticGroup 1 where
  toFun g := ⟨g, compactSymplectic_rank_one_mem g⟩
  invFun := compactSymplecticInclusion 1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem su2CompactSymplecticOne_continuous : Continuous su2CompactSymplecticOne :=
  continuous_id.subtype_mk _

theorem su2CompactSymplecticOne_symm_continuous : Continuous su2CompactSymplecticOne.symm :=
  continuous_subtype_val

end MathieuProperty
