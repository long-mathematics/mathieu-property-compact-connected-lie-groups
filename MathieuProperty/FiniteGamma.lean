import MathieuProperty.GammaBeta
import Mathlib.MeasureTheory.Constructions.Pi

/-! Sums and block ratios of finite independent gamma families. -/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace MathieuProperty

theorem finite_gamma_sum_succ (n : ℕ) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (Measure.pi (fun _ : Fin (n + 1) => gammaMeasure a r)).map (fun x => ∑ i, x i) =
      gammaMeasure ((n + 1 : ℕ) * a) r := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  induction n with
  | zero =>
    simpa [Fin.sum_univ_one] using
      (measurePreserving_eval (fun _ : Fin 1 => gammaMeasure a r) 0).map_eq
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 1) => ℝ) 0
    have he : (Measure.pi (fun _ : Fin (n + 1 + 1) => gammaMeasure a r)).map e =
        (gammaMeasure a r).prod (Measure.pi (fun _ : Fin (n + 1) => gammaMeasure a r)) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1 + 1) => gammaMeasure a r) 0).map_eq
    have hm : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => p.1 + ∑ i, p.2 i) := by fun_prop
    have hh := congrArg (Measure.map (fun p : ℝ × (Fin (n + 1) → ℝ) => p.1 + ∑ i, p.2 i)) he
    rw [Measure.map_map hm e.measurable] at hh
    have heq : (fun p : ℝ × (Fin (n + 1) → ℝ) => p.1 + ∑ i, p.2 i) ∘ e =
        (fun x : Fin (n + 1 + 1) → ℝ => ∑ i, x i) := by
      funext x
      simp [e, Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove]
      rfl
    rw [heq] at hh
    have hprod : ((gammaMeasure a r).prod (Measure.pi (fun _ : Fin (n + 1) => gammaMeasure a r))).map
        (fun p : ℝ × (Fin (n + 1) → ℝ) => p.1 + ∑ i, p.2 i) =
        ((gammaMeasure a r).prod (gammaMeasure ((n + 1 : ℕ) * a) r)).map
          (fun p : ℝ × ℝ => p.1 + p.2) := by
      have hp := Measure.map_prod_map (gammaMeasure a r)
        (Measure.pi (fun _ : Fin (n + 1) => gammaMeasure a r))
        measurable_id (show Measurable (fun x : Fin (n + 1) → ℝ => ∑ i, x i) by fun_prop)
      rw [Measure.map_id, ih] at hp
      rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [hh, hprod, gamma_sum_gamma ha (by positivity) hr]
    congr 1
    push_cast
    ring

theorem finite_gamma_sum {n : ℕ} (hn : 1 ≤ n) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (Measure.pi (fun _ : Fin n => gammaMeasure a r)).map (fun x => ∑ i, x i) =
      gammaMeasure ((n : ℝ) * a) r := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact finite_gamma_sum_succ k ha hr

theorem gamma_block_ratio {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ((Measure.pi (fun _ : Fin k => gammaMeasure a r)).prod
      (Measure.pi (fun _ : Fin l => gammaMeasure a r))).map
      (fun p => (∑ i, p.1 i) / ((∑ i, p.1 i) + (∑ j, p.2 j))) =
      betaMeasure ((k : ℝ) * a) ((l : ℝ) * a) := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  have hs₁ : Measurable (fun x : Fin k → ℝ => ∑ i, x i) := by fun_prop
  have hs₂ : Measurable (fun x : Fin l → ℝ => ∑ i, x i) := by fun_prop
  have hp := Measure.map_prod_map (Measure.pi (fun _ : Fin k => gammaMeasure a r))
    (Measure.pi (fun _ : Fin l => gammaMeasure a r)) hs₁ hs₂
  rw [finite_gamma_sum hk ha hr, finite_gamma_sum hl ha hr] at hp
  have heq := gamma_ratio_beta (show 0 < (k : ℝ) * a by positivity)
    (show 0 < (l : ℝ) * a by positivity) hr
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)] at heq
  exact heq

def splitFiniteCoordinates (k l : ℕ) : (Fin (k + l) → ℝ) ≃ᵐ
    (Fin k → ℝ) × (Fin l → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin l => ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l => ℝ))

theorem splitFiniteCoordinates_map (k l : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : Fin (k + l) => μ)).map (splitFiniteCoordinates k l) =
      (Measure.pi (fun _ : Fin k => μ)).prod (Measure.pi (fun _ : Fin l => μ)) := by
  exact ((measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l => μ)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin k ⊕ Fin l => μ) finSumFinEquiv.symm)).map_eq

theorem finite_gamma_ratio_beta {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (Measure.pi (fun _ : Fin (k + l) => gammaMeasure a r)).map
      (fun x => (∑ i : Fin k, x (Fin.castAdd l i)) / (∑ i, x i)) =
      betaMeasure ((k : ℝ) * a) ((l : ℝ) * a) := by
  let := isProbabilityMeasure_gammaMeasure ha hr
  have hh := gamma_block_ratio hk hl ha hr
  rw [← splitFiniteCoordinates_map k l (gammaMeasure a r),
    Measure.map_map (by fun_prop) (splitFiniteCoordinates k l).measurable] at hh
  convert hh using 1
  congr 1
  funext x
  simp [splitFiniteCoordinates, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
    Fin.sum_univ_add, Equiv.piCongrLeft]

end MathieuProperty
