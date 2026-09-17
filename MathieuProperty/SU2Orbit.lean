import MathieuProperty.SU2Action
import MathieuProperty.OrbitMeasure

/-! Identification of SU(2) Haar orbits with normalized Euclidean sphere measure. -/

noncomputable section
open MeasureTheory
namespace MathieuProperty.Hopf

/-- Haar orbits give the manuscript's actual surface measure, at every base point. -/
theorem su2_orbit_measurePreserving (z : Sphere) :
    MeasurePreserving (fun g : SU2 => g • z) (normalizedHaar SU2) surfaceMeasure :=
  measurePreserving_transitive_orbit surfaceMeasure SU2_transitive_sphere z

theorem su2_orbit_map (z : Sphere) :
    Measure.map (fun g : SU2 => g • z) (normalizedHaar SU2) = surfaceMeasure :=
  (su2_orbit_measurePreserving z).map_eq

theorem su2_orbit_integral (z : Sphere) {f : Sphere → ℂ} (hf : Continuous f) :
    (∫ g : SU2, f (g • z) ∂normalizedHaar SU2) = ∫ w, f w ∂surfaceMeasure := by
  rw [← su2_orbit_map z]
  exact (integral_map_of_stronglyMeasurable
    (su2_orbit_measurePreserving z).measurable hf.stronglyMeasurable).symm

/-- Every vector has a nonnegative radius and a unit direction; zero is included. -/
theorem exists_radial_direction (z : Space) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ w : Sphere, z = (r : ℂ) • w.val ∧ r ^ 2 = a z := by
  by_cases hz : z = 0
  · subst z
    refine ⟨0, le_rfl, ⟨(1, 0), by simp [a]⟩, ?_, ?_⟩ <;> simp [a]
  · let r := Real.sqrt (a z)
    have ha : 0 < a z := lt_of_le_of_ne (a_nonneg z) (Ne.symm ((a_eq_zero_iff z).not.mpr hz))
    have hr : 0 < r := Real.sqrt_pos.mpr ha
    have hr2 : r ^ 2 = a z := Real.sq_sqrt ha.le
    have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hw : a ((r : ℂ)⁻¹ • z) = 1 := by
      rw [a_smul, map_inv₀, Complex.normSq_ofReal]
      rw [← pow_two, ← hr2]
      exact inv_mul_cancel₀ (pow_ne_zero _ hr.ne')
    refine ⟨r, hr.le, ⟨(r : ℂ)⁻¹ • z, hw⟩, ?_, hr2⟩
    simp [smul_smul, hc]

theorem su2_smul_complex (g : SU2) (c : ℂ) (z : Space) :
    g • (c • z) = c • (g • z) := (su2Linear g).map_smul c z

/-- Transitivity on every Euclidean sphere, stated in the manuscript's coordinates. -/
theorem SU2_transitive_equal_a (z w : Space) (h : a z = a w) : ∃ g : SU2, g • z = w := by
  obtain ⟨r, hr, z', hz, hr2⟩ := exists_radial_direction z
  obtain ⟨s, hs, w', hw, hs2⟩ := exists_radial_direction w
  have hrs : r = s := (sq_eq_sq₀ hr hs).mp (hr2.trans (h.trans hs2.symm))
  obtain ⟨g, hg⟩ := SU2_transitive_sphere z' w'
  refine ⟨g, ?_⟩
  rw [hz, hw, hrs, su2_smul_complex]
  exact congrArg (fun x : Sphere => (s : ℂ) • x.val) hg

/-- The exact radial factor in every pure or marked polynomial orbit moment. -/
theorem su2_orbit_moment (z : Space) (m s : ℕ) :
    (∫ g : SU2, Q (g • z) ^ s * P (g • z) ^ m ∂normalizedHaar SU2) =
      (a z : ℂ) ^ (4 * m + s) * ∫ w, q w ^ s * p w ^ m ∂surfaceMeasure := by
  obtain ⟨r, _hr, w, hz, hr2⟩ := exists_radial_direction z
  have hpoint (g : SU2) : Q (g • z) ^ s * P (g • z) ^ m =
      (a z : ℂ) ^ (4 * m + s) * (q (g • w) ^ s * p (g • w) ^ m) := by
    conv_lhs => rw [hz, su2_smul_complex]
    change Q ((r : ℂ) • (g • w).val) ^ s * P ((r : ℂ) • (g • w).val) ^ m = _
    rw [radial_power, a_smul, (g • w).property, mul_one,
      Complex.normSq_ofReal, ← pow_two, hr2]
  simp_rw [hpoint]
  rw [integral_const_mul, su2_orbit_integral w (f := fun w => q w ^ s * p w ^ m)
    ((continuous_q.pow s).mul (continuous_p.pow m))]

/-- Radial reduction for every finite compactly supported invariant measure.
The remaining sphere moment is identified with the coefficient formula separately. -/
theorem radial_moment_factorization (μ : Measure Space) [IsFiniteMeasure μ]
    [SMulInvariantMeasure SU2 Space μ] (hμ : IsCompact μ.support) (m s : ℕ) :
    (∫ z, Q z ^ s * P z ^ m ∂μ) =
      (∫ z, (a z : ℂ) ^ (4 * m + s) ∂μ) *
        ∫ w, q w ^ s * p w ^ m ∂surfaceMeasure := by
  rw [← orbit_average (G := SU2) μ hμ (f := fun z => Q z ^ s * P z ^ m)
    ((continuous_Q.pow s).mul (continuous_P.pow m))]
  simp_rw [su2_orbit_moment]
  exact integral_mul_const _ _

end MathieuProperty.Hopf
