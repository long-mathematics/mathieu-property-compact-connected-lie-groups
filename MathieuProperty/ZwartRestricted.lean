import MathieuProperty.ZwartCube

/-! Counterexamples on restricted cubes, and a Fubini correspondence with
nested integrals whose final coordinate has a variable upper bound. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Zwart

theorem weightedMoment_restrict {N M : ℕ} (S : Set (Cube N))
    (hS : MeasurableSet S) (W : Cube N → ℂ) (f : FunctionLaurent (Cube (N+1)) M) :
    weightedMoment (volume.restrict (Fin.tail ⁻¹' S)) (cubeLinearWeight W) f =
      weightedMoment volume (cubeLinearWeight (S.indicator W)) f := by
  classical
  have hm : Measurable (Fin.tail : Cube (N+1) → Cube N) := by fun_prop
  unfold weightedMoment
  rw [← integral_indicator (hS.preimage hm)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : Fin.tail x ∈ S <;> simp [cubeLinearWeight, hx]

theorem cube_restricted_convexSupport_false (N : ℕ) {M : ℕ} (i : Fin M)
    (S : Set (Cube N)) (hS : MeasurableSet S) (W : Cube N → ℂ) :
    ¬ ConvexSupportConjecture M (radialAlgebra (N+1))
      (volume.restrict (Fin.tail ⁻¹' S)) (cubeLinearWeight W) := by
  intro h
  apply cube_convexSupport_false N i (S.indicator W)
  intro f hf hm
  apply h f hf
  intro m hmp
  rw [weightedMoment_restrict S hS]
  exact hm m hmp


theorem cube_integral_last_restrict (N : ℕ) (B : Cube N → ℝ) (hB : Continuous B)
    (f : Cube (N+1) → ℂ) (hf : Continuous f) :
    (∫ x in {x : Cube (N+1) | (x (Fin.last N)).val ≤ B (Fin.init x)}, f x) =
      ∫ y : Cube N, ∫ t in {t : I | t.val ≤ B y}, f (Fin.snoc y t) := by
  classical
  let S : Set (Cube (N+1)) := {x | (x (Fin.last N)).val ≤ B (Fin.init x)}
  have hS : MeasurableSet S := by
    apply measurableSet_le
    · fun_prop
    · exact (hB.comp (by fun_prop)).measurable
  rw [← integral_indicator hS]
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (N+1) => I) (Fin.last N)).symm
  rw [← hp.integral_comp' (S.indicator f)]
  have hcont : Continuous (fun p : I × Cube N => f (Fin.snoc p.2 p.1)) := hf.comp (by fun_prop)
  have hmeas : MeasurableSet {p : I × Cube N | p.1.val ≤ B p.2} :=
    measurableSet_le (by fun_prop) (hB.comp continuous_snd).measurable
  have hi := hcont.integrable_of_hasCompactSupport (μ := (volume : Measure I).prod volume)
    (HasCompactSupport.of_compactSpace _)
  have hi' := hi.indicator hmeas
  have he : (fun p => S.indicator f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => I) (Fin.last N)).symm p)) =
      {p : I × Cube N | p.1.val ≤ B p.2}.indicator (fun p => f (Fin.snoc p.2 p.1)) := by
    funext p
    by_cases h : p.1.val ≤ B p.2
    all_goals simp [S, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv, Set.indicator, h]
  rw [he]
  change (∫ p : I × Cube N, _ ∂(volume : Measure I).prod volume) = _
  rw [integral_prod _ hi', integral_integral_swap
    (f := fun t y => {p : I × Cube N | p.1.val ≤ B p.2}.indicator
      (fun p => f (Fin.snoc p.2 p.1)) (t,y)) hi']
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
  congr 1

end MathieuProperty.Zwart
