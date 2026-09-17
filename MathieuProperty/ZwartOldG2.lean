import MathieuProperty.ZwartPunctured
import MathieuProperty.ZwartG2

/-! Direct refutation of Zwart 2024, Conjecture 3.5. The coefficient algebra,
bounded denominators, radial domain, and density agree with the cited source.
The arbitrary constant absorbs the older density's overall factor four. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Zwart

def G2Conjecture2024 (c : ℂ) : Prop :=
  FractionalConvexSupportConjecture 4 8 (radialAlgebra 6)
    (volume.restrict (Fin.tail ⁻¹' g2TailRegion)) (g2Density c)

theorem g2_conjecture_2024_false (c : ℂ) : ¬ G2Conjecture2024 c := by
  intro h
  exact g2_conjecture_2025_false c (fractional_conjecture_implies_integer (by norm_num) _ _ _ h)

theorem g2_fractionalMoment_nested (c : ℂ) (f : RationalLaurent (Cube 6) 8) :
    fractionalMoment (volume.restrict (Fin.tail ⁻¹' g2TailRegion)) (g2Density c) f =
      ∫ θ : Cube 8, ∫ y : Cube 5,
        ∫ t in {t : I | t.val ≤ g2Boundary (y 4).val},
          angleMap (Fin.snoc y t) f θ * g2Density c (Fin.snoc y t) := by
  rw [fractionalMoment_angles_outer _ _ (continuous_g2Density c), g2_region_eq]
  apply integral_congr_ae
  filter_upwards [] with θ
  exact cube_integral_last_restrict 5 (fun y => g2Boundary (y 4).val)
    (by unfold g2Boundary; fun_prop)
    (fun x => angleMap x f θ * g2Density c x)
    (((continuous_angleMap f).comp (continuous_id.prodMk continuous_const)).mul
      (continuous_g2Density c))

theorem g2_conjecture_2024_nested_false (c : ℂ) :
    ¬ (∀ f : RationalLaurent (Cube 6) 8, FractionalAdmissible 4 (radialAlgebra 6) f →
      (∀ m : ℕ, 1 ≤ m →
        (∫ θ : Cube 8, ∫ y : Cube 5,
          ∫ t in {t : I | t.val ≤ g2Boundary (y 4).val},
            (angleMap (Fin.snoc y t) f θ)^m * g2Density c (Fin.snoc y t)) = 0) →
      0 ∉ rationalNewtonPolytope f) := by
  intro h
  apply g2_conjecture_2024_false c
  intro f hf hm
  apply h f hf
  intro m hmp
  have he := hm m hmp
  rw [g2_fractionalMoment_nested] at he
  simpa only [map_pow, ContinuousMap.pow_apply] using he

/-- The actual parametrized product dz/z functional has the same counterexample. -/
theorem g2_conjecture_2024_contour_false (c : ℂ) :
    ¬ (∀ f : RationalLaurent (Cube 6) 8, FractionalAdmissible 4 (radialAlgebra 6) f →
      (∀ m : ℕ, 1 ≤ m → fractionalContourMoment
        (volume.restrict (Fin.tail ⁻¹' g2TailRegion)) (g2Density c) (f^m) = 0) →
      0 ∉ rationalNewtonPolytope f) := by
  intro h
  apply g2_conjecture_2024_false c
  intro f hf hm
  apply h f hf
  intro m hmp
  exact (fractionalContourMoment_eq_zero_iff _ _ _).mpr (hm m hmp)
end MathieuProperty.Zwart
