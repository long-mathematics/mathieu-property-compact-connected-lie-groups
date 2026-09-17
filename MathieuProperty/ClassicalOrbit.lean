import MathieuProperty.ClassicalTopology
import MathieuProperty.NormalizedSphere
import MathieuProperty.OrbitMeasure

/-! The first column of a Haar-distributed SU(n) matrix is uniform on the
complex unit sphere for n≥2. Uniform measure here is the normalized cone
surface measure obtained from Euclidean volume, not an abstract invariant
measure. Transitivity and isometry invariance identify the two measures.
-/

noncomputable section
open MeasureTheory Metric
open scoped Matrix
namespace MathieuProperty
abbrev ClassicalSphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1

instance specialUnitaryMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin n) ℂ) := borel _
instance specialUnitaryBorelSpace (n : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin n) ℂ) := ⟨rfl⟩

instance specialUnitarySphereAction (n : ℕ) :
    MulAction (Matrix.specialUnitaryGroup (Fin n) ℂ) (ClassicalSphere n) where
  smul g z := ⟨specialUnitaryRepresentation n g z.val, by
    rw [mem_sphere_zero_iff_norm, (specialUnitaryRepresentation n g).norm_map]
    exact mem_sphere_zero_iff_norm.mp z.property⟩
  one_smul z := by
    apply Subtype.ext
    change specialUnitaryRepresentation n 1 z.val = z.val
    rw [map_one]
    rfl
  mul_smul g h z := by
    apply Subtype.ext
    change specialUnitaryRepresentation n (g * h) z.val =
      specialUnitaryRepresentation n g (specialUnitaryRepresentation n h z.val)
    rw [map_mul]
    rfl

theorem specialUnitarySphere_smul_val (n : ℕ)
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) (z : ClassicalSphere n) :
    (g • z).val = specialUnitaryRepresentation n g z.val := rfl

instance specialUnitarySphereContinuousSMul (n : ℕ) :
    ContinuousSMul (Matrix.specialUnitaryGroup (Fin n) ℂ) (ClassicalSphere n) where
  continuous_smul := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : Matrix.specialUnitaryGroup (Fin n) ℂ × ClassicalSphere n => (p.1 • p.2).val)
    simp_rw [specialUnitarySphere_smul_val]
    simp_rw [specialUnitaryRepresentation_apply]
    change Continuous (fun p : Matrix.specialUnitaryGroup (Fin n) ℂ × ClassicalSphere n =>
      WithLp.toLp 2 (fun i => ∑ j, p.1.val i j * p.2.val j))
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    exact ((continuous_subtype_val.comp continuous_fst).matrix_elem i j).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
        (continuous_subtype_val.comp continuous_snd))

def classicalBasePoint (n : ℕ) [NeZero n] : ClassicalSphere n :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

theorem specialUnitarySphere_transitive (n : ℕ) (hn : 2 ≤ n)
    (x y : ClassicalSphere n) : ∃ g : Matrix.specialUnitaryGroup (Fin n) ℂ, g • x = y := by
  let : NeZero n := ⟨by omega⟩
  have hreach (z : ClassicalSphere n) :
      ∃ g : Matrix.specialUnitaryGroup (Fin n) ℂ, g • classicalBasePoint n = z := by
    obtain ⟨g, hg⟩ := exists_specialUnitary_firstColumn hn z.val (mem_sphere_zero_iff_norm.mp z.property)
    refine ⟨g, ?_⟩
    apply Subtype.ext
    ext i
    change (g.val *ᵥ Pi.single 0 1) i = z.val i
    simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] using hg i
  obtain ⟨g, hg⟩ := hreach x
  obtain ⟨h, hh⟩ := hreach y
  refine ⟨h * g⁻¹, ?_⟩
  rw [← hg, mul_smul, inv_smul_smul, hh]

def specialUnitaryRealIsometry (n : ℕ) (g : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  __ := (specialUnitaryRepresentation n g).toLinearEquiv.restrictScalars ℝ
  norm_map' := (specialUnitaryRepresentation n g).norm_map

instance specialUnitarySphereInvariant (n : ℕ) :
    SMulInvariantMeasure (Matrix.specialUnitaryGroup (Fin n) ℂ) (ClassicalSphere n)
      (normalizedSphereMeasure (EuclideanSpace ℂ (Fin n))) where
  measure_preimage_smul g S hS := by
    have hp := normalizedSphere_preserving (specialUnitaryRealIsometry n g)
    exact hp.measure_preimage hS.nullMeasurableSet 

theorem specialUnitarySphere_orbit (n : ℕ) (hn : 2 ≤ n) (z : ClassicalSphere n) :
    MeasurePreserving (fun g : Matrix.specialUnitaryGroup (Fin n) ℂ => g • z)
      (normalizedHaar (Matrix.specialUnitaryGroup (Fin n) ℂ))
      (normalizedSphereMeasure (EuclideanSpace ℂ (Fin n))) := by
  let : NeZero n := ⟨by omega⟩
  exact measurePreserving_transitive_orbit _ (specialUnitarySphere_transitive n hn) z

def specialUnitaryFirstColumn (n : ℕ) [NeZero n]
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) : ClassicalSphere n :=
  g • classicalBasePoint n

theorem specialUnitaryFirstColumn_apply (n : ℕ) [NeZero n]
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) (i : Fin n) :
    (specialUnitaryFirstColumn n g).val i = g.val i 0 := by
  change (g.val *ᵥ Pi.single 0 1) i = g.val i 0
  simp only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply]

theorem specialUnitaryFirstColumn_map (n : ℕ) (hn : 2 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    Measure.map (specialUnitaryFirstColumn n)
      (normalizedHaar (Matrix.specialUnitaryGroup (Fin n) ℂ)) =
      normalizedSphereMeasure (EuclideanSpace ℂ (Fin n)) := by
  let : NeZero n := ⟨by omega⟩
  exact (specialUnitarySphere_orbit n hn (classicalBasePoint n)).map_eq

end MathieuProperty
