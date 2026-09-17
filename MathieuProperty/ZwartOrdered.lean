import MathieuProperty.ZwartRestricted

/-! Ordered-cube and block-coordinate Fubini identities for the Zwart Sp(N)
radial integral. Every restricted domain uses ordinary product Lebesgue measure. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Zwart

def orderedCube (N : ℕ) (b : I) : Set (Cube N) :=
  {x | Monotone x ∧ ∀ i, x i ≤ b}

theorem monotone_snoc_iff {N : ℕ} (y : Cube N) (t : I) :
    Monotone (Fin.snoc y t) ↔ Monotone y ∧ ∀ i, y i ≤ t := by
  constructor
  · intro h
    constructor
    · intro i j hij
      simpa using h (Fin.castSucc_le_castSucc_iff.mpr hij)
    · intro i
      simpa using h (Fin.le_last i.castSucc)
  · rintro ⟨hy, ht⟩ i j hij
    induction i using Fin.lastCases with
    | last =>
      have hj : j = Fin.last N := le_antisymm (Fin.le_last _) hij
      subst j
      rfl
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa using ht i
      | cast j => simpa using hy (Fin.castSucc_le_castSucc_iff.mp hij)

theorem orderedCube_snoc {N : ℕ} (y : Cube N) (t b : I) :
    Fin.snoc y t ∈ orderedCube (N+1) b ↔ t ≤ b ∧ y ∈ orderedCube N t := by
  simp only [orderedCube, Set.mem_ofPred_eq, monotone_snoc_iff]
  constructor
  · rintro ⟨⟨hm, ht⟩, hb⟩
    exact ⟨by simpa using hb (Fin.last N), hm, ht⟩
  · rintro ⟨ht,hm,hy⟩
    refine ⟨⟨hm,hy⟩,?_⟩
    intro i
    induction i using Fin.lastCases with
    | last => simpa using ht
    | cast i => simpa using (hy i).trans ht

theorem orderedCube_measurable (N : ℕ) (b : I) : MeasurableSet (orderedCube N b) := by
  change MeasurableSet ({x : Cube N | Monotone x} ∩ {x | ∀ i, x i ≤ b})
  apply MeasurableSet.inter
  · unfold Monotone
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun hij => measurableSet_le (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const

def orderedIntegral : (N : ℕ) → I → (Cube N → ℂ) → ℂ
  | 0, _, f => f (fun i => Fin.elim0 i)
  | n+1, b, f => ∫ t in Set.Iic b, orderedIntegral n t (fun y => f (Fin.snoc y t))

theorem integral_orderedCube_succ (N : ℕ) (b : I) (f : Cube (N+1) → ℂ)
    (hf : Continuous f) :
    (∫ x in orderedCube (N+1) b, f x) =
      ∫ t in Set.Iic b, ∫ y in orderedCube N t, f (Fin.snoc y t) := by
  classical
  rw [← integral_indicator (orderedCube_measurable (N+1) b)]
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => I) (Fin.last N)).symm
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (N+1) => I) (Fin.last N)).symm
  rw [← hp.integral_comp' ((orderedCube (N+1) b).indicator f)]
  have hi := (hf.integrable_of_hasCompactSupport (μ := volume)
    (HasCompactSupport.of_compactSpace _)).indicator (orderedCube_measurable (N+1) b)
  have hi' := hp.integrable_comp_of_integrable hi
  change (∫ p : I × Cube N, ((orderedCube (N+1) b).indicator f) (e p) ∂volume.prod volume) = _
  rw [integral_prod (fun p : I × Cube N => (orderedCube (N+1) b).indicator f (e p))
    (by exact hi'), ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ≤ b
  · rw [Set.indicator_of_mem (show t ∈ Set.Iic b from ht), ← integral_indicator (orderedCube_measurable N t)]
    apply integral_congr_ae
    filter_upwards [] with y
    have he : e (t,y) = Fin.snoc y t := by simp [e, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv]
    rw [he]
    by_cases hy : y ∈ orderedCube N t <;> simp [Set.indicator, orderedCube_snoc, ht, hy]
  · rw [Set.indicator_of_notMem (show t ∉ Set.Iic b from ht)]
    apply integral_eq_zero_of_ae
    filter_upwards [] with y
    have he : e (t,y) = Fin.snoc y t := by simp [e, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv]
    rw [he]
    simp [Set.indicator, orderedCube_snoc, ht]

theorem integral_orderedCube (N : ℕ) (b : I) (f : Cube N → ℂ) (hf : Continuous f) :
    (∫ x in orderedCube N b, f x) = orderedIntegral N b f := by
  induction N generalizing b with
  | zero =>
    have hs : orderedCube 0 b = Set.univ := by ext x; simp [orderedCube, Monotone]
    rw [hs, Measure.restrict_univ, integral_unique]
    simp [orderedIntegral]
    congr 1
  | succ N ih =>
    rw [integral_orderedCube_succ N b f hf]
    apply integral_congr_ae
    filter_upwards [] with t
    exact ih t (fun y => f (Fin.snoc y t)) (hf.comp (by fun_prop))

def cubeAppendEquiv (N K : ℕ) : Cube (N+K) ≃ᵐ Cube N × Cube K :=
  (MeasurableEquiv.arrowCongr' (finSumFinEquiv.symm : Fin (N+K) ≃ Fin N ⊕ Fin K)
    (MeasurableEquiv.refl I)).trans (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin K => I))

theorem cubeAppendEquiv_preserving (N K : ℕ) : MeasurePreserving (cubeAppendEquiv N K) := by
  exact (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin N ⊕ Fin K => I)).comp
    (volume_preserving_arrowCongr' finSumFinEquiv.symm (MeasurableEquiv.refl I)
      (MeasurePreserving.id _))

theorem cubeAppendEquiv_symm (N K : ℕ) (x : Cube N) (y : Cube K) :
    (cubeAppendEquiv N K).symm (x,y) = Fin.append x y := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  all_goals simp [cubeAppendEquiv, MeasurableEquiv.arrowCongr',
    MeasurableEquiv.sumPiEquivProdPi, Equiv.arrowCongr', Equiv.arrowCongr]
  all_goals rfl

theorem cube_integral_append_restrict (N K : ℕ) (S : Set (Cube K)) (hS : MeasurableSet S)
    (f : Cube (N+K) → ℂ) (hf : Continuous f) :
    (∫ x in {x : Cube (N+K) | (fun i => x (i.natAdd N)) ∈ S}, f x) =
      ∫ x : Cube N, ∫ y in S, f (Fin.append x y) := by
  classical
  let T : Set (Cube (N+K)) := {x | (fun i => x (i.natAdd N)) ∈ S}
  have hT : MeasurableSet T := hS.preimage (by fun_prop)
  rw [← integral_indicator hT]
  have hp := (cubeAppendEquiv_preserving N K).symm
  rw [← hp.integral_comp' (T.indicator f)]
  have hi := (hf.integrable_of_hasCompactSupport (μ := volume)
    (HasCompactSupport.of_compactSpace _)).indicator hT
  have hi' := hp.integrable_comp_of_integrable hi
  change (∫ p : Cube N × Cube K, T.indicator f ((cubeAppendEquiv N K).symm p)
    ∂volume.prod volume) = _
  rw [integral_prod (fun p : Cube N × Cube K => T.indicator f ((cubeAppendEquiv N K).symm p))
    (by exact hi')]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [cubeAppendEquiv_symm]
  by_cases hy : y ∈ S <;> simp [T, Set.indicator, Fin.append_right, hy]


theorem cube_integral_restrict_cast {N K : ℕ} (h : N = K) (S : Set (Cube N)) (f : Cube N → ℂ) :
    (∫ x in S, f x) =
      ∫ y in {y : Cube K | (fun i => y (i.cast h)) ∈ S}, f (fun i => y (i.cast h)) := by
  subst h
  rfl
end MathieuProperty.Zwart
