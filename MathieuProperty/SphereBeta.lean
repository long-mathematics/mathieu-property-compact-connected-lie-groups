import MathieuProperty.GaussianRadii
import MathieuProperty.FiniteGamma
import MathieuProperty.GammaScale

/-! Dirichlet coordinate masses, beta marginals, and SU(n) radial Haar moments.

The Dirichlet(1,…,1) law uses its normalized independent unit-rate gamma
construction. Gaussian-coordinate squares have common rate 1/2; a proved
positive-scaling correspondence identifies their normalized vector with that
standard construction. Summing a block gives the actual mathlib beta measure.
For the first two coordinates this yields Beta(2,n−2), and the Haar first-column
correspondence gives the displayed rising-factorial radial moments. The n=2
endpoint is handled directly by unit norm.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Metric
namespace MathieuProperty

def simplexNormalize (n : ℕ) (x : Fin n → ℝ) : Fin n → ℝ := fun i => x i / (∑ j, x j)

def complexSphereMasses (n : ℕ) (z : ClassicalSphere n) : Fin n → ℝ :=
  fun i => Complex.normSq (z.val i)

/-- The uniform Dirichlet law, using its normalized independent gamma construction.
The construction uses unit-rate shape-one gamma variables. -/
def dirichletOne (n : ℕ) : Measure (Fin n → ℝ) :=
  (Measure.pi (fun _ : Fin n => gammaMeasure 1 1)).map (simplexNormalize n)

theorem sphereDirection_normSq (n : ℕ) (z : ClassicalSphere n)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ≠ 0) (i : Fin n) :
    complexSphereMasses n (sphereDirection z x) i =
      simplexNormalize n (fun j => Complex.normSq (x j)) i := by
  have hs : ∑ j, Complex.normSq (x j) = ‖x‖ ^ 2 := by
    simp only [Complex.normSq_eq_norm_sq]
    exact (EuclideanSpace.norm_sq_eq x).symm
  simp [complexSphereMasses, simplexNormalize, sphereDirection, hx, hs,
    Complex.normSq_ofReal, div_eq_mul_inv, mul_comm, pow_two, mul_inv_rev]

theorem complexSphereMasses_measurable (n : ℕ) : Measurable (complexSphereMasses n) := by
  apply Measurable.of_eval
  intro i
  exact Complex.continuous_normSq.measurable.comp
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).measurable.comp measurable_subtype_coe)

theorem simplexNormalize_measurable (n : ℕ) : Measurable (simplexNormalize n) := by
  unfold simplexNormalize
  fun_prop

theorem simplexNormalize_pos_scale (n : ℕ) (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    simplexNormalize n (fun i => r * x i) = simplexNormalize n x := by
  funext i
  simp only [simplexNormalize, ← Finset.mul_sum]
  exact mul_div_mul_left (x i) _ hr.ne'

theorem normalized_gamma_one_eq_dirichletOne (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (Measure.pi (fun _ : Fin n => gammaMeasure 1 r)).map (simplexNormalize n) = dirichletOne n := by
  let := isProbabilityMeasure_gammaMeasure (by norm_num : (0 : ℝ) < 1) hr
  have hm : Measurable (fun x : ℝ => r * x) := by fun_prop
  have hp := Measure.pi_map_pi (μ := fun _ : Fin n => gammaMeasure 1 r)
    (f := fun _ : Fin n => fun x : ℝ => r * x) (fun _ => hm.aemeasurable)
  simp_rw [gamma_one_scale_rate hr] at hp
  rw [dirichletOne, ← hp, Measure.map_map (simplexNormalize_measurable n) (by fun_prop)]
  congr 1
  funext x
  exact (simplexNormalize_pos_scale n x hr).symm

theorem sphere_dirichletOne (n : ℕ) (hn : 2 ≤ n) :
    (normalizedSphereMeasure (EuclideanSpace ℂ (Fin n))).map (complexSphereMasses n) =
      dirichletOne n := by
  let : NeZero n := ⟨by omega⟩
  let z := classicalBasePoint n
  have hm : Measurable (fun x : EuclideanSpace ℂ (Fin n) => fun i => Complex.normSq (x i)) := by
    apply Measurable.of_eval
    intro i
    exact Complex.continuous_normSq.measurable.comp
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).measurable
  rw [← gaussian_sphere n hn z, Measure.map_map (complexSphereMasses_measurable n)
    (sphereDirection_measurable z), ← normalized_gamma_one_eq_dirichletOne n (r := 1 / 2) (by norm_num),
    ← complexGaussian_normSq_map n,
    Measure.map_map (simplexNormalize_measurable n) hm]
  apply Measure.map_congr
  filter_upwards [(stdGaussian (EuclideanSpace ℂ (Fin n))).ae_ne 0] with x hx
  funext i
  exact sphereDirection_normSq n z x hx i

theorem dirichletOne_block_beta {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (dirichletOne (k + l)).map (fun x => ∑ i : Fin k, x (Fin.castAdd l i)) =
      betaMeasure k l := by
  have hm : Measurable (fun x : Fin (k + l) → ℝ => ∑ i : Fin k, x (Fin.castAdd l i)) := by fun_prop
  rw [dirichletOne, Measure.map_map hm (simplexNormalize_measurable (k + l))]
  have hh := finite_gamma_ratio_beta hk hl (a := 1) (r := 1) (by norm_num) (by norm_num)
  simpa [simplexNormalize, Function.comp_def, Finset.sum_div] using hh

theorem sphere_block_beta {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (normalizedSphereMeasure (EuclideanSpace ℂ (Fin (k + l)))).map
      (fun z => ∑ i : Fin k, Complex.normSq (z.val (Fin.castAdd l i))) = betaMeasure k l := by
  have hm : Measurable (fun x : Fin (k + l) → ℝ => ∑ i : Fin k, x (Fin.castAdd l i)) := by fun_prop
  have hh := congrArg (Measure.map (fun x : Fin (k + l) → ℝ => ∑ i : Fin k, x (Fin.castAdd l i)))
    (sphere_dirichletOne (k + l) (by omega))
  rw [Measure.map_map hm (complexSphereMasses_measurable (k + l)), dirichletOne_block_beta hk hl] at hh
  exact hh

def firstTwoSphereMass (n : ℕ) (hn : 2 ≤ n) (z : ClassicalSphere n) : ℝ :=
  Complex.normSq (z.val ⟨0, by omega⟩) + Complex.normSq (z.val ⟨1, by omega⟩)

theorem sphere_two_coordinates_beta (n : ℕ) (hn : 3 ≤ n) :
    (normalizedSphereMeasure (EuclideanSpace ℂ (Fin n))).map
      (firstTwoSphereMass n (by omega)) = betaMeasure 2 (n - 2 : ℕ) := by
  obtain ⟨l, rfl, hl⟩ : ∃ l, n = 2 + l ∧ 1 ≤ l := ⟨n - 2, by omega, by omega⟩
  have hh := sphere_block_beta (k := 2) (l := l) (by omega) hl
  have heq : firstTwoSphereMass (2 + l) (by omega) =
      (fun z : ClassicalSphere (2 + l) => ∑ i : Fin 2, Complex.normSq (z.val (Fin.castAdd l i))) := by
    funext z
    simp only [Fin.sum_univ_two]
    rfl
  rw [heq]
  simpa using hh

theorem complexSphereMasses_nonneg (n : ℕ) (z : ClassicalSphere n) (i : Fin n) :
    0 ≤ complexSphereMasses n z i := Complex.normSq_nonneg _

theorem complexSphereMasses_sum (n : ℕ) (z : ClassicalSphere n) :
    ∑ i, complexSphereMasses n z i = 1 := by
  simp only [complexSphereMasses, Complex.normSq_eq_norm_sq]
  rw [← EuclideanSpace.norm_sq_eq, mem_sphere_zero_iff_norm.mp z.property, one_pow]

theorem firstTwoSphereMass_continuous (n : ℕ) (hn : 2 ≤ n) :
    Continuous (firstTwoSphereMass n hn) := by
  unfold firstTwoSphereMass
  exact (Complex.continuous_normSq.comp
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) ⟨0, by omega⟩).comp continuous_subtype_val)).add
      (Complex.continuous_normSq.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) ⟨1, by omega⟩).comp continuous_subtype_val))

theorem sphere_two_coordinates_moment (n k : ℕ) (hn : 3 ≤ n) :
    ∫ z : ClassicalSphere n, firstTwoSphereMass n (by omega) z ^ k
      ∂normalizedSphereMeasure (EuclideanSpace ℂ (Fin n)) =
      ((2 : ℕ).ascFactorial k : ℝ) / (n.ascFactorial k : ℝ) := by
  have hh := congrArg (fun μ : Measure ℝ => ∫ x, x ^ k ∂μ) (sphere_two_coordinates_beta n hn)
  rw [integral_map (firstTwoSphereMass_continuous n (by omega)).measurable.aemeasurable
    (by fun_prop)] at hh
  exact hh.trans (beta_two_moment n k hn)

def specialUnitaryRadialA (n : ℕ) (hn : 2 ≤ n)
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) : ℝ :=
  Complex.normSq (g.val ⟨0, by omega⟩ ⟨0, by omega⟩) +
    Complex.normSq (g.val ⟨1, by omega⟩ ⟨0, by omega⟩)

theorem specialUnitaryRadialA_firstColumn (n : ℕ) (hn : 2 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∀ g : Matrix.specialUnitaryGroup (Fin n) ℂ,
      specialUnitaryRadialA n hn g = firstTwoSphereMass n hn (specialUnitaryFirstColumn n g) := by
  let : NeZero n := ⟨by omega⟩
  intro g
  simp only [firstTwoSphereMass, specialUnitaryFirstColumn_apply, specialUnitaryRadialA]
  rfl

theorem specialUnitaryRadialA_continuous (n : ℕ) (hn : 2 ≤ n) :
    Continuous (specialUnitaryRadialA n hn) := by
  unfold specialUnitaryRadialA
  exact (Complex.continuous_normSq.comp
    (continuous_subtype_val.matrix_elem (⟨0, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n))).add
      (Complex.continuous_normSq.comp
        (continuous_subtype_val.matrix_elem (⟨1, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n)))

theorem specialUnitaryRadialA_map (n : ℕ) (hn : 3 ≤ n) :
    (normalizedHaar (Matrix.specialUnitaryGroup (Fin n) ℂ)).map
      (specialUnitaryRadialA n (by omega)) = betaMeasure 2 (n - 2 : ℕ) := by
  let : NeZero n := ⟨by omega⟩
  have hf : specialUnitaryRadialA n (by omega) =
      firstTwoSphereMass n (by omega) ∘ specialUnitaryFirstColumn n := by
    funext g
    exact specialUnitaryRadialA_firstColumn n (by omega) g
  have hc : Measurable (specialUnitaryFirstColumn n) :=
    (specialUnitarySphere_orbit n (by omega) (classicalBasePoint n)).measurable
  rw [hf, ← Measure.map_map (firstTwoSphereMass_continuous n (by omega)).measurable hc,
    specialUnitaryFirstColumn_map n (by omega), sphere_two_coordinates_beta n hn]

theorem specialUnitaryRadialA_moment_of_three_le (n k : ℕ) (hn : 3 ≤ n) :
    ∫ g : Matrix.specialUnitaryGroup (Fin n) ℂ, specialUnitaryRadialA n (by omega) g ^ k
      ∂normalizedHaar (Matrix.specialUnitaryGroup (Fin n) ℂ) =
      ((2 : ℕ).ascFactorial k : ℝ) / (n.ascFactorial k : ℝ) := by
  have hh := congrArg (fun μ : Measure ℝ => ∫ x, x ^ k ∂μ) (specialUnitaryRadialA_map n hn)
  rw [integral_map (specialUnitaryRadialA_continuous n (by omega)).measurable.aemeasurable
    (by fun_prop)] at hh
  exact hh.trans (beta_two_moment n k hn)

theorem firstTwoSphereMass_two (z : ClassicalSphere 2) : firstTwoSphereMass 2 (by omega) z = 1 := by
  have hh := complexSphereMasses_sum 2 z
  simpa [complexSphereMasses, Fin.sum_univ_two, firstTwoSphereMass] using hh

theorem specialUnitaryRadialA_two (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    specialUnitaryRadialA 2 (by omega) g = 1 := by
  rw [specialUnitaryRadialA_firstColumn 2 (by omega) g]
  exact firstTwoSphereMass_two _

theorem specialUnitaryRadialA_moment (n k : ℕ) (hn : 2 ≤ n) :
    ∫ g : Matrix.specialUnitaryGroup (Fin n) ℂ, specialUnitaryRadialA n hn g ^ k
      ∂normalizedHaar (Matrix.specialUnitaryGroup (Fin n) ℂ) =
      ((2 : ℕ).ascFactorial k : ℝ) / (n.ascFactorial k : ℝ) := by
  by_cases hn2 : n = 2
  · subst n
    have hp : ((2 : ℕ).ascFactorial k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ascFactorial_pos 1 k).ne'
    simp [specialUnitaryRadialA_two, hp]
  · exact specialUnitaryRadialA_moment_of_three_le n k (by omega)

theorem specialUnitaryRadialA_integrable (n k : ℕ) (hn : 2 ≤ n) :
    Integrable (fun g : Matrix.specialUnitaryGroup (Fin n) ℂ => specialUnitaryRadialA n hn g ^ k)
      (normalizedHaar (Matrix.specialUnitaryGroup (Fin n) ℂ)) :=
  ((specialUnitaryRadialA_continuous n hn).pow k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end MathieuProperty
