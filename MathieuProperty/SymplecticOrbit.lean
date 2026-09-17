import MathieuProperty.CompactSymplectic
import MathieuProperty.SphereBeta

/-! The compact Sp(n) first-column distribution and radial moments.

The defining action is transitive and preserves the normalized Euclidean
sphere measure. Haar orbit averaging identifies the first-column law, so the
first two squared coordinate norms have Beta(2,2n-2) law for n≥2. For n=1
their sum is identically one. All nonnegative integer radial moments are the
rising-factorial ratio (2)ₖ/(2n)ₖ, with actual Haar integration throughout.
-/

noncomputable section
open MeasureTheory Metric ProbabilityTheory
open scoped Matrix
namespace MathieuProperty

instance compactSymplecticMeasurableSpace (n : ℕ) : MeasurableSpace (CompactSymplecticGroup n) := borel _
instance compactSymplecticBorelSpace (n : ℕ) : BorelSpace (CompactSymplecticGroup n) := ⟨rfl⟩

theorem compactSymplecticSphere_transitive (n : ℕ) (hn : 1 ≤ n)
    (x y : ClassicalSphere (n + n)) : ∃ g : CompactSymplecticGroup n, g • x = y := by
  let : NeZero n := ⟨by omega⟩
  let : NeZero (n + n) := ⟨by omega⟩
  have hreach (z : ClassicalSphere (n + n)) :
      ∃ g : CompactSymplecticGroup n, g • classicalBasePoint (n + n) = z := by
    obtain ⟨g, hg⟩ := exists_compactSymplectic_firstColumn z.val (mem_sphere_zero_iff_norm.mp z.property)
    refine ⟨g, ?_⟩
    apply Subtype.ext
    ext i
    change ((compactSymplecticInclusion n g).val *ᵥ Pi.single 0 1) i = z.val i
    simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] using hg i
  obtain ⟨g, hg⟩ := hreach x
  obtain ⟨h, hh⟩ := hreach y
  refine ⟨h * g⁻¹, ?_⟩
  rw [← hg, mul_smul, inv_smul_smul, hh]

instance compactSymplecticSphereInvariant (n : ℕ) :
    SMulInvariantMeasure (CompactSymplecticGroup n) (ClassicalSphere (n + n))
      (normalizedSphereMeasure (EuclideanSpace ℂ (Fin (n + n)))) where
  measure_preimage_smul g _S hS :=
    SMulInvariantMeasure.measure_preimage_smul (compactSymplecticInclusion n g) hS

theorem compactSymplecticSphere_orbit (n : ℕ) (hn : 1 ≤ n) (z : ClassicalSphere (n + n)) :
    MeasurePreserving (fun g : CompactSymplecticGroup n => g • z)
      (normalizedHaar (CompactSymplecticGroup n))
      (normalizedSphereMeasure (EuclideanSpace ℂ (Fin (n + n)))) := by
  let : NeZero (n + n) := ⟨by omega⟩
  exact measurePreserving_transitive_orbit _ (compactSymplecticSphere_transitive n hn) z

def compactSymplecticFirstColumn (n : ℕ) [NeZero n]
    (g : CompactSymplecticGroup n) : ClassicalSphere (n + n) :=
  specialUnitaryFirstColumn (n + n) (compactSymplecticInclusion n g)

theorem compactSymplecticFirstColumn_apply (n : ℕ) [NeZero n]
    (g : CompactSymplecticGroup n) (i : Fin (n + n)) :
    (compactSymplecticFirstColumn n g).val i = (compactSymplecticInclusion n g).val i 0 :=
  specialUnitaryFirstColumn_apply _ _ _

theorem compactSymplecticFirstColumn_map (n : ℕ) (hn : 1 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    Measure.map (compactSymplecticFirstColumn n) (normalizedHaar (CompactSymplecticGroup n)) =
      normalizedSphereMeasure (EuclideanSpace ℂ (Fin (n + n))) := by
  let : NeZero n := ⟨by omega⟩
  exact (compactSymplecticSphere_orbit n hn (classicalBasePoint (n + n))).map_eq

def compactSymplecticRadialA (n : ℕ) (hn : 1 ≤ n) (g : CompactSymplecticGroup n) : ℝ :=
  specialUnitaryRadialA (n + n) (by omega) (compactSymplecticInclusion n g)

theorem compactSymplecticRadialA_continuous (n : ℕ) (hn : 1 ≤ n) :
    Continuous (compactSymplecticRadialA n hn) :=
  (specialUnitaryRadialA_continuous (n + n) (by omega)).comp continuous_subtype_val

theorem compactSymplecticRadialA_firstColumn (n : ℕ) (hn : 1 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∀ g : CompactSymplecticGroup n, compactSymplecticRadialA n hn g =
      firstTwoSphereMass (n + n) (by omega) (compactSymplecticFirstColumn n g) := by
  let : NeZero n := ⟨by omega⟩
  intro g
  exact specialUnitaryRadialA_firstColumn (n + n) (by omega) (compactSymplecticInclusion n g)

theorem compactSymplecticRadialA_map (n : ℕ) (hn : 2 ≤ n) :
    (normalizedHaar (CompactSymplecticGroup n)).map (compactSymplecticRadialA n (by omega)) =
      betaMeasure 2 (n + n - 2 : ℕ) := by
  let : NeZero n := ⟨by omega⟩
  have hf : compactSymplecticRadialA n (by omega) =
      firstTwoSphereMass (n + n) (by omega) ∘ compactSymplecticFirstColumn n := by
    funext g
    exact compactSymplecticRadialA_firstColumn n (by omega) g
  have hc : Measurable (compactSymplecticFirstColumn n) :=
    (compactSymplecticSphere_orbit n (by omega) (classicalBasePoint (n + n))).measurable
  rw [hf, ← Measure.map_map (firstTwoSphereMass_continuous (n + n) (by omega)).measurable hc,
    compactSymplecticFirstColumn_map n (by omega), sphere_two_coordinates_beta (n + n) (by omega)]

theorem compactSymplecticRadialA_one (g : CompactSymplecticGroup 1) :
    compactSymplecticRadialA 1 (by omega) g = 1 :=
  specialUnitaryRadialA_two (compactSymplecticInclusion 1 g)

theorem compactSymplecticRadialA_moment (n k : ℕ) (hn : 1 ≤ n) :
    ∫ g : CompactSymplecticGroup n, compactSymplecticRadialA n hn g ^ k
      ∂normalizedHaar (CompactSymplecticGroup n) =
      ((2 : ℕ).ascFactorial k : ℝ) / ((n + n).ascFactorial k : ℝ) := by
  by_cases hn1 : n = 1
  · subst n
    have hp : ((2 : ℕ).ascFactorial k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ascFactorial_pos 1 k).ne'
    simp [compactSymplecticRadialA_one, hp]
  · have hh := congrArg (fun μ : Measure ℝ => ∫ x, x ^ k ∂μ)
      (compactSymplecticRadialA_map n (by omega))
    rw [integral_map (compactSymplecticRadialA_continuous n hn).measurable.aemeasurable
      (by fun_prop)] at hh
    exact hh.trans (beta_two_moment (n + n) k (by omega))

theorem compactSymplecticRadialA_integrable (n k : ℕ) (hn : 1 ≤ n) :
    Integrable (fun g : CompactSymplecticGroup n => compactSymplecticRadialA n hn g ^ k)
      (normalizedHaar (CompactSymplecticGroup n)) :=
  ((compactSymplecticRadialA_continuous n hn).pow k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end MathieuProperty
