import MathieuProperty.ZwartRestricted

/-! Direct counterexample for Zwart 2025, Conjecture 3.3. The boundary is
written using the real inverse sine, with its source substitution identity. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Zwart

def g2Boundary (t : ℝ) : ℝ := Real.sin (Real.arcsin t / 3)

theorem g2Boundary_sin {y : ℝ} (hy : y ∈ Set.Icc 0 (Real.pi / 2)) :
    g2Boundary (Real.sin y) = Real.sin (y / 3) := by
  unfold g2Boundary
  rw [Real.arcsin_sin (by linarith [Real.pi_pos, hy.1]) hy.2]

def g2TailRegion : Set (Cube 5) := {y | (y 4).val ≤ g2Boundary (y 3).val}

theorem g2TailRegion_measurable : MeasurableSet g2TailRegion := by
  unfold g2TailRegion g2Boundary
  apply measurableSet_le <;> fun_prop

def g2CoreDensity (u v : ℂ) : ℂ :=
  u*v * (u^2*(16*(1-v^2)^3+9*(1-v^2)-24*(1-v^2)^2) -
    (1-u^2)*(3*v-4*v^2)^2) * (u^2*(1-v^2)-(1-u^2)*v^2)

def g2Density (c : ℂ) (x : Cube 6) : ℂ :=
  c * g2CoreDensity (x 4).val (x 5).val *
    (x 0).val * (x 1).val * (x 2).val * (x 3).val

def g2TailWeight (c : ℂ) (y : Cube 5) : ℂ :=
  c * g2CoreDensity (y 3).val (y 4).val * (y 0).val * (y 1).val * (y 2).val

theorem g2Density_eq (c : ℂ) : g2Density c = cubeLinearWeight (g2TailWeight c) := by
  funext x
  simp only [g2Density, cubeLinearWeight, g2TailWeight, Fin.tail]
  norm_num [Fin.succ]
  ring

def G2Conjecture2025 (c : ℂ) : Prop :=
  ConvexSupportConjecture 8 (radialAlgebra 6)
    (volume.restrict (Fin.tail ⁻¹' g2TailRegion)) (g2Density c)

theorem g2_conjecture_2025_false (c : ℂ) : ¬ G2Conjecture2025 c := by
  unfold G2Conjecture2025
  rw [g2Density_eq]
  exact cube_restricted_convexSupport_false 5 (0 : Fin 8)
    g2TailRegion g2TailRegion_measurable (g2TailWeight c)

theorem g2_region_eq : Fin.tail ⁻¹' g2TailRegion =
    {x : Cube 6 | (x (Fin.last 5)).val ≤ g2Boundary ((Fin.init x) 4).val} := by
  ext x
  rfl

theorem continuous_g2Density (c : ℂ) : Continuous (g2Density c) := by
  unfold g2Density g2CoreDensity
  fun_prop

/-- The restricted-cube functional is exactly the source's order of integration:
normalized circles, five unit coordinates, and the final bounded coordinate. -/
theorem g2_weightedMoment_nested (c : ℂ) (f : FunctionLaurent (Cube 6) 8) :
    weightedMoment (volume.restrict (Fin.tail ⁻¹' g2TailRegion)) (g2Density c) f =
      ∫ z : Torus 8, ∫ y : Cube 5,
        ∫ t in {t : I | t.val ≤ g2Boundary (y 4).val},
          circleEvaluation f (Fin.snoc y t) z * g2Density c (Fin.snoc y t)
          ∂volume ∂volume ∂normalizedHaar (Torus 8) := by
  rw [weightedMoment_circles_outer _ _ (continuous_g2Density c), g2_region_eq]
  apply integral_congr_ae
  filter_upwards [] with z
  exact cube_integral_last_restrict 5 (fun y => g2Boundary (y 4).val)
    (by unfold g2Boundary; fun_prop)
    (fun x => circleEvaluation f x z * g2Density c x)
    (((continuous_circleEvaluation f).comp (continuous_id.prodMk continuous_const)).mul
      (continuous_g2Density c))

/-- Manuscript-facing form with positive powers of the actual Laurent function
inside the nested circle/radial integral. -/
theorem g2_conjecture_2025_nested_false (c : ℂ) :
    ¬ (∀ f : FunctionLaurent (Cube 6) 8, Admissible (radialAlgebra 6) f →
      (∀ m : ℕ, 1 ≤ m →
        (∫ z : Torus 8, ∫ y : Cube 5,
          ∫ t in {t : I | t.val ≤ g2Boundary (y 4).val},
            (circleEvaluation f (Fin.snoc y t) z)^m * g2Density c (Fin.snoc y t)
            ∂volume ∂volume ∂normalizedHaar (Torus 8)) = 0) →
      0 ∉ newtonPolytope f) := by
  intro h
  apply g2_conjecture_2025_false c
  intro f hf hm
  apply h f hf
  intro m hmp
  have he := hm m hmp
  rw [g2_weightedMoment_nested] at he
  simpa only [circleEvaluation_pow, ContinuousMap.pow_apply] using he
end MathieuProperty.Zwart
