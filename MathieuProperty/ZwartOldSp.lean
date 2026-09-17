import MathieuProperty.ZwartOldSU
import MathieuProperty.ZwartSp

/-! The 2024 Sp(N) rational-frequency conjecture with its original radial density. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Zwart

theorem oldSunTail_length (n : ℕ) : (oldSunTail n).length = (sunTailPowers n).length := by
  have h := oldSunPowers_length (n+2)
  have k := sunPowers_length (n+2)
  rw [oldSunPowers_head, List.length_cons] at h
  rw [sunPowers_head, List.length_cons] at k
  omega

def oldSpTailPowers (n : ℕ) := oldSunTail n ++ oldSunPowers (n+2) ++ List.replicate (n+2) (1,0)

theorem oldSpTailPowers_length (n : ℕ) : (oldSpTailPowers n).length = (spTailPowers n).length := by
  simp [oldSpTailPowers, spTailPowers, oldSunTail_length, oldSunPowers_length, sunPowers_length]

def oldSpPair (n : ℕ) (i : Fin (spTailPowers n).length) : ℕ × ℕ :=
  (oldSpTailPowers n).get (i.cast (oldSpTailPowers_length n).symm)

def oldSpTailWeight (n : ℕ) (c : ℂ) (y : Cube (spTailPowers n).length) : ℂ :=
  c * (∏ i, ((y i).val : ℂ)^(oldSpPair n i).1 * (1-((y i).val : ℂ)^2)^(oldSpPair n i).2) *
    spPairFactor n (spTailXi n y)

def oldSpFullPair (n : ℕ) : Fin (spRadialCount n) → ℕ × ℕ :=
  Fin.cases (1,0) (oldSpPair n)

def oldSpDensity (n : ℕ) (c : ℂ) (x : Cube (spRadialCount n)) : ℂ :=
  c * (∏ i, ((x i).val : ℂ)^(oldSpFullPair n i).1 *
    (1-((x i).val : ℂ)^2)^(oldSpFullPair n i).2) *
    spPairFactor n (spTailXi n (Fin.tail x))

theorem oldSpDensity_eq (n : ℕ) (c : ℂ) : oldSpDensity n c = cubeLinearWeight (oldSpTailWeight n c) := by
  funext x
  unfold oldSpDensity cubeLinearWeight oldSpTailWeight oldSpFullPair
  rw [Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, pow_zero, pow_one, mul_one, Fin.tail]
  ring

theorem oldSpPowers_as_blocks (n : ℕ) : (1,0) :: oldSpTailPowers n =
    oldSunPowers (n+2) ++ oldSunPowers (n+2) ++ List.replicate (n+2) (1,0) := by
  simp only [oldSpTailPowers, oldSunPowers_head, List.cons_append]

def SpConjecture2024 (n : ℕ) (c : ℂ) : Prop :=
  FractionalConvexSupportConjecture (n+2) ((n+2)*(n+3)) (radialAlgebra (spRadialCount n))
    (volume.restrict (Fin.tail ⁻¹' spTailRegion n)) (oldSpDensity n c)

theorem sp_conjecture_2024_false (n : ℕ) (c : ℂ) : ¬ SpConjecture2024 n c := by
  intro h
  have hi := fractional_conjecture_implies_integer (by omega : 1 ≤ n+2) _ _ _ h
  rw [oldSpDensity_eq] at hi
  exact cube_restricted_convexSupport_false (spTailPowers n).length
    ⟨0, by positivity⟩ (spTailRegion n) (spTailRegion_measurable n) (oldSpTailWeight n c) hi

def SpOneConjecture2024 (c : ℂ) : Prop :=
  FractionalConvexSupportConjecture 1 2 (radialAlgebra 1) volume (fun x : Cube 1 => c*((x 0).val : ℂ))

theorem sp_one_conjecture_2024_false (c : ℂ) : ¬ SpOneConjecture2024 c := by
  intro h
  exact sp_one_conjecture_2025_false c (fractional_conjecture_implies_integer le_rfl _ _ _ h)

theorem oldSpFullPair_get (n : ℕ) (i : Fin (spRadialCount n)) :
    oldSpFullPair n i = ((1,0) :: oldSpTailPowers n).get
      (i.cast (congrArg Nat.succ (oldSpTailPowers_length n)).symm) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [oldSpFullPair, List.get_eq_getElem]
  · simp [oldSpFullPair, oldSpPair, List.get_eq_getElem]

theorem oldSpDensity_list (n : ℕ) (c : ℂ) (x : Cube (spRadialCount n)) :
    oldSpDensity n c x = c * pairedListWeight ((1,0)::oldSpTailPowers n)
      (fun i => x (i.cast (congrArg Nat.succ (oldSpTailPowers_length n)))) *
      spPairFactor n (spTailXi n (Fin.tail x)) := by
  unfold oldSpDensity pairedListWeight
  simp_rw [oldSpFullPair_get]
  congr 2
  exact (Fin.prod_congr' _ (congrArg Nat.succ (oldSpTailPowers_length n))).symm

theorem oldSpDensity_blocks (n : ℕ) (c : ℂ) (x : Cube (spRadialCount n)) :
    oldSpDensity n c x = c * pairedListWeight
      (oldSunPowers (n+2) ++ oldSunPowers (n+2) ++ List.replicate (n+2) (1,0))
      (fun i => x (i.cast ((congrArg List.length (oldSpPowers_as_blocks n)).symm.trans
        (congrArg Nat.succ (oldSpTailPowers_length n))))) *
      spPairFactor n (spTailXi n (Fin.tail x)) := by
  rw [oldSpDensity_list, pairedListWeight_cast (oldSpPowers_as_blocks n)]
  rfl

theorem continuous_oldSpDensity (n : ℕ) (c : ℂ) : Continuous (oldSpDensity n c) := by
  unfold oldSpDensity spPairFactor spTailXi
  fun_prop

theorem sp_fractionalMoment_source (n : ℕ) (c : ℂ)
    (f : RationalLaurent (Cube (spRadialCount n)) ((n+2)*(n+3))) :
    fractionalMoment (volume.restrict (Fin.tail ⁻¹' spTailRegion n)) (oldSpDensity n c) f =
      ∫ x : Cube (spXCount n), ∫ θ : Cube ((n+2)*(n+3)),
        orderedIntegral (n+2) 1 (fun ξ => angleMap (spRadialPoint n x ξ) f θ *
          oldSpDensity n c (spRadialPoint n x ξ)) := by
  unfold fractionalMoment
  rw [sp_integral_nested n (fun x => (∫ θ, angleMap x f θ) * oldSpDensity n c x)
    ((continuous_angleIntegral f).mul (continuous_oldSpDensity n c))]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : Continuous (spRadialPoint n x) := by unfold spRadialPoint; fun_prop
  have hc := ((continuous_angleIntegral f).mul (continuous_oldSpDensity n c)).comp hp
  rw [← integral_orderedCube (n+2) 1
    (fun ξ => (∫ θ, angleMap (spRadialPoint n x ξ) f θ) * oldSpDensity n c (spRadialPoint n x ξ)) hc]
  rw [angleIntegral_pullback_outer (volume.restrict (orderedCube (n+2) 1))
    (spRadialPoint n x) hp (fun ξ => oldSpDensity n c (spRadialPoint n x ξ))
    ((continuous_oldSpDensity n c).comp hp) f]
  apply integral_congr_ae
  filter_upwards [] with θ
  exact integral_orderedCube (n+2) 1 _
    (((continuous_angleMap f).comp (hp.prodMk continuous_const)).mul
      ((continuous_oldSpDensity n c).comp hp))

theorem sp_fractionalContourMoment_source (n : ℕ) (c : ℂ)
    (f : RationalLaurent (Cube (spRadialCount n)) ((n+2)*(n+3))) :
    fractionalContourMoment (volume.restrict (Fin.tail ⁻¹' spTailRegion n)) (oldSpDensity n c) f =
      (Complex.I*(2*Real.pi))^((n+2)*(n+3)) *
      ∫ x : Cube (spXCount n), ∫ θ : Cube ((n+2)*(n+3)),
        orderedIntegral (n+2) 1 (fun ξ => angleMap (spRadialPoint n x ξ) f θ *
          oldSpDensity n c (spRadialPoint n x ξ)) := by
  rw [fractionalContourMoment_eq, sp_fractionalMoment_source]

theorem sp_conjecture_2024_source_false (n : ℕ) (c : ℂ) :
    ¬ (∀ f : RationalLaurent (Cube (spRadialCount n)) ((n+2)*(n+3)),
      FractionalAdmissible (n+2) (radialAlgebra (spRadialCount n)) f →
      (∀ m : ℕ, 1 ≤ m →
        (∫ x : Cube (spXCount n), ∫ θ : Cube ((n+2)*(n+3)),
          orderedIntegral (n+2) 1 (fun ξ => (angleMap (spRadialPoint n x ξ) f θ)^m *
            oldSpDensity n c (spRadialPoint n x ξ))) = 0) →
      0 ∉ rationalNewtonPolytope f) := by
  intro h
  apply sp_conjecture_2024_false n c
  intro f hf hm
  apply h f hf
  intro m hmp
  have he := hm m hmp
  rw [sp_fractionalMoment_source] at he
  simpa only [map_pow, ContinuousMap.pow_apply] using he

theorem sp_conjecture_2024_contour_false (n : ℕ) (c : ℂ) :
    ¬ (∀ f : RationalLaurent (Cube (spRadialCount n)) ((n+2)*(n+3)),
      FractionalAdmissible (n+2) (radialAlgebra (spRadialCount n)) f →
      (∀ m : ℕ, 1 ≤ m → fractionalContourMoment
        (volume.restrict (Fin.tail ⁻¹' spTailRegion n)) (oldSpDensity n c) (f^m) = 0) →
      0 ∉ rationalNewtonPolytope f) := by
  intro h
  apply sp_conjecture_2024_false n c
  intro f hf hm
  apply h f hf
  intro m hmp
  exact (fractionalContourMoment_eq_zero_iff _ _ _).mpr (hm m hmp)

theorem sp_one_conjecture_2024_contour_false (c : ℂ) :
    ¬ (∀ f : RationalLaurent (Cube 1) 2, FractionalAdmissible 1 (radialAlgebra 1) f →
      (∀ m : ℕ, 1 ≤ m → fractionalContourMoment volume
        (fun x : Cube 1 => c*((x 0).val : ℂ)) (f^m) = 0) →
      0 ∉ rationalNewtonPolytope f) := by
  intro h
  apply sp_one_conjecture_2024_false c
  intro f hf hm
  apply h f hf
  intro m hmp
  exact (fractionalContourMoment_eq_zero_iff _ _ _).mpr (hm m hmp)

end MathieuProperty.Zwart
