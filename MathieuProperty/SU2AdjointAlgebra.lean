import MathieuProperty.RankOneRootAlgebra
import MathieuProperty.SU2Generators
import MathieuProperty.LieAutomorphism
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Normed

/-! The concrete compact three-dimensional matrix Lie algebra and its relation
to the normalized compact root basis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.SU2AdjointAlgebra
open Matrix
open scoped Matrix.Norms.Elementwise
attribute [local instance] LieRing.ofAssociativeRing
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- The actual real Lie algebra of traceless skew-Hermitian 2×2 matrices. -/
def compactAlgebra : LieSubalgebra ℝ Mat where
  carrier := {A | star A = -A ∧ Matrix.trace A = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    simp only [Set.mem_ofPred_eq] at *
    exact ⟨by simp [hA.1,hB.1,add_comm],by simp [hA.2,hB.2]⟩
  smul_mem' := by
    intro r A hA
    exact ⟨by simp [hA.1],by simp [hA.2]⟩
  lie_mem' := by
    intro A B hA hB
    refine ⟨?_,?_⟩
    · simp only [Ring.lie_def,star_sub,star_mul,hA.1,hB.1,neg_mul_neg,neg_sub]
    · rw [Ring.lie_def,Matrix.trace_sub,Matrix.trace_mul_comm A B,sub_self]

abbrev Algebra := ↥compactAlgebra

/-- Real coordinates with cyclic bracket constants 2. -/
def matrixCoordinates : (Fin 3 → ℝ) →ₗ[ℝ] Mat where
  toFun x := !![Complex.I*x 2, (x 0 : ℂ)+Complex.I*x 1;
    -(x 0 : ℂ)+Complex.I*x 1, -Complex.I*x 2]
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring

theorem matrixCoordinates_mem (x : Fin 3 → ℝ) : matrixCoordinates x ∈ compactAlgebra := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixCoordinates,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply] <;> ring
  · simp [matrixCoordinates,Matrix.trace,Fin.sum_univ_two]

def coordinates : (Fin 3 → ℝ) →ₗ[ℝ] Algebra :=
  matrixCoordinates.codRestrict compactAlgebra.toSubmodule matrixCoordinates_mem

@[simp] theorem coordinates_val (x : Fin 3 → ℝ) : (coordinates x).val = matrixCoordinates x := rfl

/-- Reading the three independent real entries. -/
def readCoordinates : Algebra →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun A := ![(A.val 0 1).re,(A.val 0 1).im,(A.val 0 0).im]
  map_add' A B := by ext i; fin_cases i <;> simp
  map_smul' r A := by ext i; fin_cases i <;> simp [Complex.real_smul]

theorem read_coordinates (x : Fin 3 → ℝ) : readCoordinates (coordinates x) = x := by
  ext i
  fin_cases i <;> simp [readCoordinates,matrixCoordinates]

theorem coordinates_read (A : Algebra) : coordinates (readCoordinates A) = A := by
  have ha := congrArg (fun M : Mat => (M 0 0).re) A.property.1
  have hb := congrArg (fun M : Mat => M 1 0) A.property.1
  have ht := A.property.2
  simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Complex.star_def,
    Complex.conj_re,Matrix.neg_apply,Complex.neg_re] at ha
  have ha0 : (A.val 0 0).re = 0 := by linarith
  simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Matrix.neg_apply] at hb
  simp only [Matrix.trace,Fin.sum_univ_two] at ht
  apply Subtype.ext
  change matrixCoordinates (readCoordinates A) = A.val
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [coordinates,readCoordinates,matrixCoordinates,ha0]
  · apply Complex.ext <;> simp [coordinates,readCoordinates,matrixCoordinates]
  · have he : A.val 1 0 = -star (A.val 0 1) := neg_eq_iff_eq_neg.mp hb.symm
    change -(A.val 0 1).re + Complex.I * (A.val 0 1).im = A.val 1 0
    rw [he]
    apply Complex.ext <;> simp
  · have he : A.val 1 1 = -A.val 0 0 := eq_neg_of_add_eq_zero_right ht
    change -Complex.I * (A.val 0 0).im = A.val 1 1
    rw [he]
    apply Complex.ext <;> simp [ha0]

/-- The concrete algebra has its usual three real coordinates. -/
def coordinateEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] Algebra :=
  { coordinates with
    invFun := readCoordinates
    left_inv := read_coordinates
    right_inv := coordinates_read }

instance : NormedAddCommGroup Algebra :=
  inferInstanceAs (NormedAddCommGroup compactAlgebra.toSubmodule)
instance : NormedSpace ℝ Algebra := inferInstanceAs (NormedSpace ℝ compactAlgebra.toSubmodule)
instance : NormedRealLieAlgebra Algebra :=
  { (inferInstance : LieRing Algebra), (inferInstance : NormedAddCommGroup Algebra),
    (inferInstance : LieAlgebra ℝ Algebra), (inferInstance : NormedSpace ℝ Algebra) with }

/-- The matrix commutator is twice the usual cyclic cross-product formula. -/
theorem coordinates_lie (x y : Fin 3 → ℝ) :
    ⁅coordinates x,coordinates y⁆ = coordinates
      ![2*(x 1*y 2-x 2*y 1),2*(x 2*y 0-x 0*y 2),2*(x 0*y 1-x 1*y 0)] := by
  apply Subtype.ext
  change matrixCoordinates x * matrixCoordinates y - matrixCoordinates y * matrixCoordinates x = _
  rw [coordinates_val]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [matrixCoordinates,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

/-- The standard ordered compact basis. -/
def basis : Module.Basis (Fin 3) ℝ Algebra := (Pi.basisFun ℝ (Fin 3)).map coordinateEquiv

@[simp] theorem basis_apply (i : Fin 3) : basis i = coordinates (Pi.single i 1) := by
  simp [basis,coordinateEquiv]

theorem basis_cyclic : ⁅basis 0,basis 1⁆ = (2 : ℝ) • basis 2 ∧
    ⁅basis 1,basis 2⁆ = (2 : ℝ) • basis 0 ∧ ⁅basis 2,basis 0⁆ = (2 : ℝ) • basis 1 := by
  simp only [basis_apply,coordinates_lie,← map_smul]
  constructor
  · congr 1
    ext i; fin_cases i <;> norm_num
  constructor <;> congr 1 <;> ext i <;> fin_cases i <;> norm_num

@[simp] theorem basis_repr_coordinates (x : Fin 3 → ℝ) (i : Fin 3) :
    basis.repr (coordinates x) i = x i := by
  simp [basis,coordinateEquiv,read_coordinates]

/-- The concrete Killing form is minus eight times the coordinate dot product. -/
theorem killing_coordinates (x y : Fin 3 → ℝ) :
    killingForm ℝ Algebra (coordinates x) (coordinates y) =
      -8 * (x 0*y 0+x 1*y 1+x 2*y 2) := by
  rw [killingForm_apply_apply,LinearMap.trace_eq_matrix_trace ℝ basis]
  simp [Matrix.trace,LinearMap.toMatrix_apply,LinearMap.comp_apply,LieAlgebra.ad_apply,
    basis_apply,coordinates_lie,Fin.sum_univ_succ]
  ring

/-- Every Lie-algebra automorphism preserves the coordinate norm squared. -/
theorem equiv_norm_sq (e : Algebra ≃ₗ⁅ℝ⁆ Algebra) (x : Fin 3 → ℝ) :
    let y := readCoordinates (e (coordinates x))
    y 0^2+y 1^2+y 2^2 = x 0^2+x 1^2+x 2^2 := by
  have he := LieAlgebra.killingForm_of_equiv_apply e (coordinates x) (coordinates x)
  have hy := coordinates_read (e (coordinates x))
  rw [← hy,killing_coordinates,killing_coordinates] at he
  dsimp
  nlinarith [he]

/-- A cyclic compact basis identifies any real Lie algebra with this concrete
matrix model; the bracket check is reduced to the nine basis pairs. -/
def ofCompactBasis {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (b : Module.Basis (Fin 3) ℝ L)
    (hb : ⁅b 0,b 1⁆ = (2 : ℝ) • b 2 ∧ ⁅b 1,b 2⁆ = (2 : ℝ) • b 0 ∧
      ⁅b 2,b 0⁆ = (2 : ℝ) • b 1) : L ≃ₗ⁅ℝ⁆ Algebra := by
  let l := b.equiv basis (Equiv.refl _)
  have hl (i : Fin 3) : l (b i) = basis i := b.equiv_apply i _ _
  have hb10 : ⁅b 1,b 0⁆ = -((2 : ℝ) • b 2) := by rw [← lie_skew (b 1) (b 0),hb.1]
  have hb21 : ⁅b 2,b 1⁆ = -((2 : ℝ) • b 0) := by rw [← lie_skew (b 2) (b 1),hb.2.1]
  have hb02 : ⁅b 0,b 2⁆ = -((2 : ℝ) • b 1) := by rw [← lie_skew (b 0) (b 2),hb.2.2]
  have ht10 : ⁅basis 1,basis 0⁆ = -((2 : ℝ) • basis 2) := by rw [← lie_skew (basis 1) (basis 0),basis_cyclic.1]
  have ht21 : ⁅basis 2,basis 1⁆ = -((2 : ℝ) • basis 0) := by rw [← lie_skew (basis 2) (basis 1),basis_cyclic.2.1]
  have ht02 : ⁅basis 0,basis 2⁆ = -((2 : ℝ) • basis 1) := by rw [← lie_skew (basis 0) (basis 2),basis_cyclic.2.2]
  have hh : (LieAlgebra.ad ℝ L).toLinearMap.compr₂ l.toLinearMap =
      ((LieAlgebra.ad ℝ Algebra).toLinearMap.comp l.toLinearMap).compl₂ l.toLinearMap := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change l ⁅b i,b j⁆ = ⁅l (b i),l (b j)⁆
    rw [hl,hl]
    fin_cases i <;> fin_cases j
    · simp only [lie_self,map_zero]
    · change l ⁅b 0,b 1⁆ = ⁅basis 0,basis 1⁆
      rw [hb.1,basis_cyclic.1]
      simp only [map_neg,map_smul,hl]
    · change l ⁅b 0,b 2⁆ = ⁅basis 0,basis 2⁆
      rw [hb02,ht02]
      simp only [map_neg,map_smul,hl]
    · change l ⁅b 1,b 0⁆ = ⁅basis 1,basis 0⁆
      rw [hb10,ht10]
      simp only [map_neg,map_smul,hl]
    · simp only [lie_self,map_zero]
    · change l ⁅b 1,b 2⁆ = ⁅basis 1,basis 2⁆
      rw [hb.2.1,basis_cyclic.2.1]
      simp only [map_neg,map_smul,hl]
    · change l ⁅b 2,b 0⁆ = ⁅basis 2,basis 0⁆
      rw [hb.2.2,basis_cyclic.2.2]
      simp only [map_neg,map_smul,hl]
    · change l ⁅b 2,b 1⁆ = ⁅basis 2,basis 1⁆
      rw [hb21,ht21]
      simp only [map_neg,map_smul,hl]
    · simp only [lie_self,map_zero]
  exact { l with map_lie' := fun {x} {y} => LinearMap.congr_fun (LinearMap.congr_fun hh x) y }

end MathieuProperty.SU2AdjointAlgebra

open scoped Manifold ContDiff
namespace MathieuProperty.AdjointRankOne
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G]
local instance matrixModelNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance matrixModelFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

/-- The actual rank-one algebra is the concrete compact matrix algebra. -/
theorem exists_matrix_equiv
    (hr : Module.finrank ℝ (CompactCartanRootData.realCartan (E := E) (G := G)) = 1) :
    Nonempty (GroupLieAlgebra 𝓘(ℝ,E) G ≃ₗ⁅ℝ⁆ SU2AdjointAlgebra.Algebra) := by
  obtain ⟨b,hb⟩ := exists_compact_basis hr
  exact ⟨SU2AdjointAlgebra.ofCompactBasis b hb⟩

end MathieuProperty.AdjointRankOne
