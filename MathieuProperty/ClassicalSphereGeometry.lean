import MathieuProperty.SU2Action
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Geometric preliminaries for classical first-column distributions.

Extend one unit vector to an orthonormal basis, then correct the determinant
in another column. This realizes every unit vector as the first column of an
SU(n) matrix for n≥2. The actual defining action is a continuous unitary action.
The normalized Haar/surface correspondence is developed separately.
-/

noncomputable section
namespace MathieuProperty

theorem exists_unitary_firstColumn {n : ℕ} [NeZero n]
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ, ∀ i, U.val i 0 = z i := by
  have hv : Orthonormal ℂ (({0} : Set (Fin n)).domRestrict (fun _ => z)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hz
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let a := EuclideanSpace.basisFun (Fin n) ℂ
  refine ⟨⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b⟩, fun i => ?_⟩
  change a.toBasis.repr (b 0) i = z i
  rw [hb 0 (by simp)]
  rfl

theorem exists_specialUnitary_firstColumn {n : ℕ} (hn : 2 ≤ n)
    (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1) :
    letI : NeZero n := ⟨by omega⟩
    ∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ, ∀ i, U.val i 0 = z i := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨U, hU⟩ := exists_unitary_firstColumn z hz
  let j : Fin n := ⟨1, by omega⟩
  have hj : j ≠ 0 := by
    intro h
    have hh := congrArg Fin.val h
    simp [j] at hh
  let d : Fin n → ℂ := fun i => if i = j then star U.val.det else 1
  let D := Matrix.diagonal d
  have hD : D ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i k
    by_cases hik : i = k
    · subst k
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      change star (d i) * d i = 1
      by_cases hi : i = j
      · simpa only [d, ite_eq_left hi, star_star] using (Matrix.det_of_mem_unitary U.property).2
      · simp [d, hi]
    · simp [Matrix.diagonal_apply_ne _ hik, Matrix.one_apply_ne hik]
  have hdet : Matrix.det D = star U.val.det := by
    simp [D, d, Matrix.det_diagonal]
  have hUD : U.val * D ∈ Matrix.specialUnitaryGroup (Fin n) ℂ := by
    constructor
    · exact (Matrix.unitaryGroup (Fin n) ℂ).mul_mem U.property hD
    · change Matrix.det (U.val * D) = 1
      rw [Matrix.det_mul, hdet]
      exact (Matrix.det_of_mem_unitary U.property).2
  refine ⟨⟨U.val * D, hUD⟩, fun i => ?_⟩
  change (U.val * Matrix.diagonal d) i 0 = _
  simp [Matrix.mul_diagonal, d, Ne.symm hj, hU]

def specialUnitaryRepresentation (n : ℕ) :
    Matrix.specialUnitaryGroup (Fin n) ℂ →*
      (EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) where
  toFun g := Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := EuclideanSpace ℂ (Fin n))
    ⟨(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) g.val, Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) g.property.1⟩
  map_one' := by
    ext x : 1
    change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (1 : Matrix (Fin n) (Fin n) ℂ) x = x
    simp
  map_mul' g h := by
    ext x : 1
    change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) (g.val * h.val) x =
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) g.val ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) h.val x)
    rw [map_mul]
    rfl

theorem specialUnitaryRepresentation_apply (n : ℕ)
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    specialUnitaryRepresentation n g x = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)) g.val x := rfl

theorem specialUnitaryRepresentation_continuous (n : ℕ) :
    Continuous (fun p : Matrix.specialUnitaryGroup (Fin n) ℂ × EuclideanSpace ℂ (Fin n) =>
      specialUnitaryRepresentation n p.1 p.2) := by
  simp_rw [specialUnitaryRepresentation_apply]
  change Continuous (fun p : Matrix.specialUnitaryGroup (Fin n) ℂ × EuclideanSpace ℂ (Fin n) =>
    WithLp.toLp 2 (fun i => ∑ j, p.1.val i j * p.2 j))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem i j).mul
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp continuous_snd)

end MathieuProperty
