import MathieuProperty.ZwartSU
import MathieuProperty.ZwartOrdered

/-! Direct counterexamples to Zwart 2025 Conjecture 3.1, including rank one,
ordered radial domains, the printed Jacobian, and exact nested integrals. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Zwart

def listWeight (L : List ℕ) (x : Cube L.length) : ℂ := ∏ i, ((x i).val : ℂ) ^ L.get i

theorem listWeight_append (L K : List ℕ) (x : Cube (L.length+K.length)) :
    listWeight (L++K) (fun i => x (Fin.cast List.length_append i)) =
      listWeight L (fun i => x (i.castAdd K.length)) *
      listWeight K (fun i => x (i.natAdd L.length)) := by
  unfold listWeight
  have he := Fin.prod_congr'
    (fun i : Fin (L.length+K.length) => ((x i).val : ℂ) ^
      (L++K).get (i.cast List.length_append.symm)) List.length_append
  simp only [Fin.cast_cast, Fin.cast_eq_self] at he
  rw [he]
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [List.get_eq_getElem]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [List.get_eq_getElem]


def spTailPowers (n : ℕ) := sunTailPowers n ++ sunPowers (n+2) ++ List.replicate (n+2) 1

abbrev spRadialCount (n : ℕ) := (spTailPowers n).length + 1

theorem twice_sunRadialCount (n : ℕ) : 2 * sunRadialCount n = (n+2)*(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ha := sunPowers_length (n+2)
    have hb := sunPowers_length (n+3)
    rw [sunPowers_head, List.length_cons] at ha hb
    change sunRadialCount n = (n+2).choose 2 at ha
    change sunRadialCount (n+1) = (n+3).choose 2 at hb
    have hc : (n+3).choose 2 = (n+2)+(n+2).choose 2 := by
      simpa using Nat.choose_succ_succ (n+2) 1
    rw [hb, hc, ← ha]
    nlinarith

theorem spRadialCount_eq (n : ℕ) : spRadialCount n = (n+2)^2 := by
  unfold spRadialCount spTailPowers
  simp only [List.length_append, List.length_replicate]
  rw [sunPowers_head, List.length_cons]
  have h := twice_sunRadialCount n
  unfold sunRadialCount at h
  nlinarith

def spTailXi (n : ℕ) (y : Cube (spTailPowers n).length) (i : Fin (n+2)) : I :=
  y ⟨(sunTailPowers n).length + (sunPowers (n+2)).length + i.val,
    by simp [spTailPowers]; omega⟩

def spTailRegion (n : ℕ) : Set (Cube (spTailPowers n).length) :=
  {y | Monotone (spTailXi n y)}

theorem spTailRegion_measurable (n : ℕ) : MeasurableSet (spTailRegion n) := by
  unfold spTailRegion Monotone
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hij
  exact measurableSet_le (by unfold spTailXi; fun_prop) (by unfold spTailXi; fun_prop)

/-- The pair factor as printed in Zwart 2025 Conjecture 3.1. -/
def spPairFactor (n : ℕ) (ξ : Fin (n+2) → I) : ℂ :=
  ∏ j, ∏ k ∈ Finset.univ.filter (fun k => k < j),
    (((ξ j).val : ℂ)^2 * (1-((ξ k).val : ℂ)^2) -
      (1-((ξ j).val : ℂ)^2) * ((ξ k).val : ℂ))

def spTailWeight (n : ℕ) (c : ℂ) (y : Cube (spTailPowers n).length) : ℂ :=
  c * (∏ i, ((y i).val : ℂ) ^ (spTailPowers n).get i) * spPairFactor n (spTailXi n y)

def spDensity (n : ℕ) (c : ℂ) (x : Cube (spRadialCount n)) : ℂ :=
  c * (∏ i, ((x i).val : ℂ) ^ (1 :: spTailPowers n).get i) *
    spPairFactor n (spTailXi n (Fin.tail x))

theorem spDensity_eq (n : ℕ) (c : ℂ) : spDensity n c = cubeLinearWeight (spTailWeight n c) := by
  funext x
  unfold spDensity cubeLinearWeight spTailWeight
  change c * (∏ i : Fin ((spTailPowers n).length+1),
    ((x i).val : ℂ) ^ (1 :: spTailPowers n).get i) *
      spPairFactor n (spTailXi n (Fin.tail x)) =
    ((x (0 : Fin ((spTailPowers n).length+1))).val : ℂ) *
      (c * (∏ i : Fin (spTailPowers n).length, ((x i.succ).val : ℂ) ^
        (spTailPowers n).get i) * spPairFactor n (spTailXi n (Fin.tail x)))
  rw [Fin.prod_univ_succ]
  simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
    List.getElem_cons_zero, List.getElem_cons_succ, pow_one]
  ring

def SpConjecture2025 (n : ℕ) (c : ℂ) : Prop :=
  ConvexSupportConjecture ((n+2)*(n+3)) (radialAlgebra (spRadialCount n))
    (volume.restrict (Fin.tail ⁻¹' spTailRegion n)) (spDensity n c)

theorem sp_conjecture_2025_false (n : ℕ) (c : ℂ) : ¬ SpConjecture2025 n c := by
  unfold SpConjecture2025
  rw [spDensity_eq]
  exact cube_restricted_convexSupport_false (spTailPowers n).length
    ⟨0, by positivity⟩ (spTailRegion n) (spTailRegion_measurable n) (spTailWeight n c)

theorem spPowers_as_blocks (n : ℕ) :
    1 :: spTailPowers n = sunPowers (n+2) ++ sunPowers (n+2) ++ List.replicate (n+2) 1 := by
  simp only [spTailPowers, sunPowers_head, List.cons_append]

abbrev spXCount (n : ℕ) : ℕ := (sunPowers (n+2)).length + (sunPowers (n+2)).length

theorem spRadialCount_blocks (n : ℕ) : spRadialCount n = spXCount n + (n+2) := by
  unfold spRadialCount spXCount spTailPowers
  simp only [List.length_append, List.length_replicate]
  rw [sunPowers_head, List.length_cons]
  omega

def spRadialPoint (n : ℕ) (x : Cube (spXCount n)) (ξ : Cube (n+2)) : Cube (spRadialCount n) :=
  fun i => Fin.append x ξ (i.cast (spRadialCount_blocks n))

theorem spRadialPoint_xi (n : ℕ) (x : Cube (spXCount n)) (ξ : Cube (n+2)) :
    spTailXi n (Fin.tail (spRadialPoint n x ξ)) = ξ := by
  funext i
  unfold spTailXi spRadialPoint Fin.tail
  have he : (Fin.succ ⟨(sunTailPowers n).length + (sunPowers (n+2)).length + i.val,
      by simp [spTailPowers]; omega⟩).cast (spRadialCount_blocks n) = i.natAdd (spXCount n) := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_succ, Fin.val_natAdd, spXCount]
    rw [sunPowers_head, List.length_cons]
    omega
  simpa only [he, Fin.append_right]

/-- Rank one has just the single radial factor xi and two circle variables. -/
def SpOneConjecture2025 (c : ℂ) : Prop :=
  ConvexSupportConjecture 2 (radialAlgebra 1) volume (fun x : Cube 1 => c * ((x 0).val : ℂ))

theorem sp_one_conjecture_2025_false (c : ℂ) : ¬ SpOneConjecture2025 c := by
  have h := cube_convexSupport_false 0 (0 : Fin 2) (fun _ => c)
  have he : (fun x : Cube 1 => c * ((x 0).val : ℂ)) =
      cubeLinearWeight (N := 0) (fun _ => c) := by
    funext x
    exact mul_comm _ _
  unfold SpOneConjecture2025
  rw [he]
  exact h

theorem sp_cast_region (n : ℕ) :
    {y : Cube (spXCount n+(n+2)) |
      (fun i => y (i.cast (spRadialCount_blocks n))) ∈ Fin.tail ⁻¹' spTailRegion n} =
    {y | (fun i => y (i.natAdd (spXCount n))) ∈ orderedCube (n+2) 1} := by
  ext y
  have he : spTailXi n (Fin.tail (fun i => y (i.cast (spRadialCount_blocks n)))) =
      (fun i => y (i.natAdd (spXCount n))) := by
    funext i
    unfold spTailXi Fin.tail
    apply congrArg y
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_succ, Fin.val_natAdd, spXCount]
    rw [sunPowers_head, List.length_cons]
    omega
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, spTailRegion, he, orderedCube,
    ]
  constructor
  · intro hm
    exact ⟨hm, fun i => (y (i.natAdd (spXCount n))).property.2⟩
  · exact And.left

theorem sp_integral_nested (n : ℕ) (F : Cube (spRadialCount n) → ℂ) (hF : Continuous F) :
    (∫ x in Fin.tail ⁻¹' spTailRegion n, F x) =
      ∫ x : Cube (spXCount n), orderedIntegral (n+2) 1 (fun ξ => F (spRadialPoint n x ξ)) := by
  rw [cube_integral_restrict_cast (spRadialCount_blocks n), sp_cast_region,
    cube_integral_append_restrict (spXCount n) (n+2) (orderedCube (n+2) 1)
      (orderedCube_measurable _ _) (fun y => F (fun i => y (i.cast (spRadialCount_blocks n))))
      (hF.comp (by fun_prop))]
  apply integral_congr_ae
  filter_upwards [] with x
  exact integral_orderedCube (n+2) 1 (fun ξ => F (spRadialPoint n x ξ))
    (hF.comp (by unfold spRadialPoint; fun_prop))

theorem continuous_spDensity (n : ℕ) (c : ℂ) : Continuous (spDensity n c) := by
  unfold spDensity spPairFactor spTailXi
  fun_prop

theorem sp_weightedMoment_nested (n : ℕ) (c : ℂ)
    (f : FunctionLaurent (Cube (spRadialCount n)) ((n+2)*(n+3))) :
    weightedMoment (volume.restrict (Fin.tail ⁻¹' spTailRegion n)) (spDensity n c) f =
      ∫ z : Torus ((n+2)*(n+3)), ∫ x : Cube (spXCount n),
        orderedIntegral (n+2) 1 (fun ξ => circleEvaluation f (spRadialPoint n x ξ) z *
          spDensity n c (spRadialPoint n x ξ)) ∂volume ∂normalizedHaar (Torus ((n+2)*(n+3))) := by
  rw [weightedMoment_circles_outer _ _ (continuous_spDensity n c)]
  apply integral_congr_ae
  filter_upwards [] with z
  exact sp_integral_nested n (fun x => circleEvaluation f x z * spDensity n c x)
    (((continuous_circleEvaluation f).comp (continuous_id.prodMk continuous_const)).mul
      (continuous_spDensity n c))

/-- Source-facing powers inside the ordered radial and actual circle integral. -/
theorem sp_conjecture_2025_nested_false (n : ℕ) (c : ℂ) :
    ¬ (∀ f : FunctionLaurent (Cube (spRadialCount n)) ((n+2)*(n+3)),
      Admissible (radialAlgebra (spRadialCount n)) f →
      (∀ m : ℕ, 1 ≤ m →
        (∫ z : Torus ((n+2)*(n+3)), ∫ x : Cube (spXCount n),
          orderedIntegral (n+2) 1 (fun ξ => (circleEvaluation f (spRadialPoint n x ξ) z)^m *
            spDensity n c (spRadialPoint n x ξ)) ∂volume ∂normalizedHaar (Torus ((n+2)*(n+3)))) = 0) →
      0 ∉ newtonPolytope f) := by
  intro h
  apply sp_conjecture_2025_false n c
  intro f hf hm
  apply h f hf
  intro m hmp
  have he := hm m hmp
  rw [sp_weightedMoment_nested] at he
  simpa only [circleEvaluation_pow, ContinuousMap.pow_apply] using he

theorem spXCount_eq (n : ℕ) : spXCount n = (n+2)*(n+1) := by
  have h := twice_sunRadialCount n
  unfold spXCount
  rw [sunPowers_head, List.length_cons]
  unfold sunRadialCount at h
  omega

/-- Exact source order: the x cube, circle variables, then ordered xi integrals. -/
theorem sp_weightedMoment_source (n : ℕ) (c : ℂ)
    (f : FunctionLaurent (Cube (spRadialCount n)) ((n+2)*(n+3))) :
    weightedMoment (volume.restrict (Fin.tail ⁻¹' spTailRegion n)) (spDensity n c) f =
      ∫ x : Cube (spXCount n), ∫ z : Torus ((n+2)*(n+3)),
        orderedIntegral (n+2) 1 (fun ξ => circleEvaluation f (spRadialPoint n x ξ) z *
          spDensity n c (spRadialPoint n x ξ)) ∂normalizedHaar (Torus ((n+2)*(n+3))) := by
  unfold weightedMoment
  rw [sp_integral_nested n (fun x => f.coeff 0 x * spDensity n c x)
    ((f.coeff 0).continuous.mul (continuous_spDensity n c))]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : Continuous (spRadialPoint n x) := by unfold spRadialPoint; fun_prop
  have hcoeff := ((f.coeff 0).continuous.mul (continuous_spDensity n c)).comp hp
  rw [← integral_orderedCube (n+2) 1
    (fun ξ => f.coeff 0 (spRadialPoint n x ξ) * spDensity n c (spRadialPoint n x ξ)) hcoeff]
  rw [coefficientIntegral_circles_outer (volume.restrict (orderedCube (n+2) 1))
    (spRadialPoint n x) hp (fun ξ => spDensity n c (spRadialPoint n x ξ))
    ((continuous_spDensity n c).comp hp) f]
  apply integral_congr_ae
  filter_upwards [] with z
  exact integral_orderedCube (n+2) 1 _
    (((continuous_circleEvaluation f).comp (hp.prodMk continuous_const)).mul
      ((continuous_spDensity n c).comp hp))

theorem listWeight_cast {L K : List ℕ} (h : L = K) (x : Cube L.length) :
    listWeight L x = listWeight K (fun i => x (i.cast (congrArg List.length h).symm)) := by
  subst h
  rfl

/-- The monomial weight is exactly the concatenation of the two SU blocks and
N linear xi factors. `listWeight_append` factors these into the printed products. -/
theorem spDensity_blocks (n : ℕ) (c : ℂ) (x : Cube (spRadialCount n)) :
    spDensity n c x = c *
      listWeight (sunPowers (n+2) ++ sunPowers (n+2) ++ List.replicate (n+2) 1)
        (fun i => x (i.cast (congrArg List.length (spPowers_as_blocks n)).symm)) *
      spPairFactor n (spTailXi n (Fin.tail x)) := by
  change c * listWeight (1 :: spTailPowers n) x * _ = _
  rw [listWeight_cast (spPowers_as_blocks n)]

theorem sp_conjecture_2025_source_false (n : ℕ) (c : ℂ) :
    ¬ (∀ f : FunctionLaurent (Cube (spRadialCount n)) ((n+2)*(n+3)),
      Admissible (radialAlgebra (spRadialCount n)) f →
      (∀ m : ℕ, 1 ≤ m →
        (∫ x : Cube (spXCount n), ∫ z : Torus ((n+2)*(n+3)),
          orderedIntegral (n+2) 1 (fun ξ => (circleEvaluation f (spRadialPoint n x ξ) z)^m *
            spDensity n c (spRadialPoint n x ξ)) ∂normalizedHaar (Torus ((n+2)*(n+3)))) = 0) →
      0 ∉ newtonPolytope f) := by
  intro h
  apply sp_conjecture_2025_false n c
  intro f hf hm
  apply h f hf
  intro m hmp
  have he := hm m hmp
  rw [sp_weightedMoment_source] at he
  simpa only [circleEvaluation_pow, ContinuousMap.pow_apply] using he
end MathieuProperty.Zwart
