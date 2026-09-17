import MathieuProperty.SphereMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! The Hopf parametrization and its polynomial coordinates. The pushforward
formula identifying the parameter measure with surface measure is separate. -/

noncomputable section
namespace MathieuProperty.Hopf

def coordinatePoint (t α β : ℝ) : Space :=
  ((Real.sqrt ((1 + t) / 2) : ℂ) * Complex.exp (Complex.I * α),
   (Real.sqrt ((1 - t) / 2) : ℂ) * Complex.exp (Complex.I * β))

theorem normSq_phase (r θ : ℝ) :
    Complex.normSq ((r : ℂ) * Complex.exp (Complex.I * θ)) = r ^ 2 := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  simp [Complex.normSq_eq_norm_sq, Complex.norm_exp, pow_two]

theorem coordinatePoint_a (t α β : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    a (coordinatePoint t α β) = 1 := by
  simp only [a, coordinatePoint, normSq_phase]
  rw [Real.sq_sqrt (by linarith : 0 ≤ (1 + t) / 2),
    Real.sq_sqrt (by linarith : 0 ≤ (1 - t) / 2)]
  ring

theorem coordinatePoint_tau (t α β : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    tau (coordinatePoint t α β) = t := by
  simp only [tau, coordinatePoint, normSq_phase]
  rw [Real.sq_sqrt (by linarith : 0 ≤ (1 + t) / 2),
    Real.sq_sqrt (by linarith : 0 ≤ (1 - t) / 2)]
  ring

theorem two_sqrt_product (t : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    2 * Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 - t) / 2) = Real.sqrt (1 - t ^ 2) := by
  have ha : 0 ≤ (1 + t) / 2 := by linarith
  have hb : 0 ≤ (1 - t) / 2 := by linarith
  have hc : 0 ≤ 1 - t ^ 2 := by nlinarith
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc]
  ring

theorem phase_difference (α β : ℝ) :
    Complex.exp (Complex.I * α) * star (Complex.exp (Complex.I * β)) =
      Complex.exp (Complex.I * (α - β)) := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem coordinatePoint_u (t α β : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    u (coordinatePoint t α β) =
      (Real.sqrt (1 - t ^ 2) : ℂ) * Complex.exp (Complex.I * (α - β)) := by
  unfold u coordinatePoint
  dsimp
  rw [map_mul]
  simp only [Complex.conj_ofReal]
  have h := phase_difference α β
  simp only [Complex.star_def] at h
  calc
    _ = (2 * (Real.sqrt ((1 + t) / 2) : ℂ) * Real.sqrt ((1 - t) / 2)) *
        (Complex.exp (Complex.I * α) * starRingEnd ℂ (Complex.exp (Complex.I * β))) := by ring
    _ = _ := by
      have hr := congrArg (fun x : ℝ => (x : ℂ)) (two_sqrt_product t ht0 ht1)
      push_cast at hr
      rw [h, hr]

def hopfCoordinates (t : Set.Icc (-1 : ℝ) 1) (α β : ℝ) : Sphere :=
  ⟨coordinatePoint t α β, coordinatePoint_a t α β t.property.1 t.property.2⟩

theorem continuous_coordinatePoint :
    Continuous fun x : ℝ × (ℝ × ℝ) => coordinatePoint x.1 x.2.1 x.2.2 := by
  unfold coordinatePoint
  fun_prop

theorem continuous_hopfCoordinates :
    Continuous fun x : Set.Icc (-1 : ℝ) 1 × (ℝ × ℝ) => hopfCoordinates x.1 x.2.1 x.2.2 := by
  apply continuous_induced_rng.mpr
  exact continuous_coordinatePoint.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem coordinatePoint_u_ne_zero (t α β : ℝ) (ht0 : -1 < t) (ht1 : t < 1) :
    u (coordinatePoint t α β) ≠ 0 := by
  rw [coordinatePoint_u t α β ht0.le ht1.le]
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by nlinarith : 0 < 1 - t ^ 2))

theorem hopfCoordinates_surjective (z : Sphere) :
    ∃ (t : Set.Icc (-1 : ℝ) 1) (α β : ℝ), hopfCoordinates t α β = z := by
  have hs : Complex.normSq z.val.1 + Complex.normSq z.val.2 = 1 := z.property
  have h0 := Complex.normSq_nonneg z.val.1
  have h1 := Complex.normSq_nonneg z.val.2
  have ht : tau z.val ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> dsimp [tau] <;> linarith
  have ha : (1 + tau z.val) / 2 = ‖z.val.1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    dsimp [tau]
    linarith
  have hb : (1 - tau z.val) / 2 = ‖z.val.2‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    dsimp [tau]
    linarith
  refine ⟨⟨tau z.val, ht⟩, z.val.1.arg, z.val.2.arg, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (Real.sqrt ((1 + tau z.val) / 2) : ℂ) * Complex.exp (Complex.I * z.val.1.arg) = _
    rw [ha, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simpa only [mul_comm Complex.I] using Complex.norm_mul_exp_arg_mul_I z.val.1
  · change (Real.sqrt ((1 - tau z.val) / 2) : ℂ) * Complex.exp (Complex.I * z.val.2.arg) = _
    rw [hb, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simpa only [mul_comm Complex.I] using Complex.norm_mul_exp_arg_mul_I z.val.2

end MathieuProperty.Hopf
