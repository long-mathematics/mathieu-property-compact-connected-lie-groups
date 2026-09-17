import Mathlib.Analysis.Calculus.Deriv.Star
import MathieuProperty.SphereMonomials
import MathieuProperty.RootDoubletFaithfulness
import MathieuProperty.InvariantHaarTransfer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Two explicit one-parameter subgroups generate SU(2). Euler factorization
then upgrades generator-wise Haar-coordinate lifts to full SU(2) invariance. -/
noncomputable section
namespace MathieuProperty.Hopf

/-- The real rotation subgroup, with infinitesimal matrix [[0,-1],[1,0]]. -/
def realRotation (t : ℝ) : SU2 := sphereToSU2 ⟨(Real.cos t, Real.sin t), by
  simpa only [a, Complex.normSq_ofReal, ← pow_two] using Real.cos_sq_add_sin_sq t⟩

theorem diagonalPhase_space_smul (t : ℝ) (z : Space) :
    diagonalPhase t • z = (Complex.exp (Complex.I*t)*z.1,
      star (Complex.exp (Complex.I*t))*z.2) := by
  simp [su2_smul_apply, diagonalPhase, sphereToSU2, sphereMatrix]

theorem realRotation_space_smul (t : ℝ) (z : Space) :
    realRotation t • z = ((Real.cos t : ℂ)*z.1 - (Real.sin t : ℂ)*z.2,
      (Real.sin t : ℂ)*z.1 + (Real.cos t : ℂ)*z.2) := by
  simp [su2_smul_apply, realRotation, sphereToSU2, sphereMatrix, sub_eq_add_neg,
    -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem diagonalPhase_add (s t : ℝ) : diagonalPhase (s+t) = diagonalPhase s * diagonalPhase t := by
  apply su2_base_action_injective
  simp only [mul_smul, diagonalPhase_space_smul, mul_one, mul_zero]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realRotation_add (s t : ℝ) : realRotation (s+t) = realRotation s * realRotation t := by
  apply su2_base_action_injective
  simp [mul_smul, realRotation_space_smul, Real.cos_add, Real.sin_add, sub_eq_add_neg]

/-- Exact Euler factorization, including the cases where a first-column entry is zero. -/
theorem su2_euler_factorization (g : SU2) :
    ∃ u t v : ℝ, g = diagonalPhase u * realRotation t * diagonalPhase v := by
  let a := g.val 0 0
  let b := g.val 1 0
  have hab : ‖a‖^2 + ‖b‖^2 = 1 := by
    simpa [Hopf.a, Complex.normSq_eq_norm_sq] using su2_first_column g
  have ha : ‖a‖ ≤ 1 := by nlinarith [sq_nonneg ‖b‖, norm_nonneg a]
  have hcos : Real.cos (Real.arccos ‖a‖) = ‖a‖ :=
    Real.cos_arccos (by linarith [norm_nonneg a]) ha
  have hsin : Real.sin (Real.arccos ‖a‖) = ‖b‖ := by
    rw [Real.sin_arccos, show 1-‖a‖^2 = ‖b‖^2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg b)]
  let u := (a.arg-b.arg)/2
  let v := (a.arg+b.arg)/2
  have hsum : u+v = a.arg := by dsimp [u,v]; ring
  have hdiff : v-u = b.arg := by dsimp [u,v]; ring
  refine ⟨u, Real.arccos ‖a‖, v, ?_⟩
  apply su2_base_action_injective
  simp only [mul_smul, diagonalPhase_space_smul, realRotation_space_smul,
    mul_one, mul_zero, sub_zero, add_zero, hcos, hsin]
  have hg : g • ((1,0) : Space) = (a,b) := by simp [su2_smul_apply, a,b]
  rw [hg]
  apply Prod.ext
  · change a = Complex.exp (Complex.I*u) * ((‖a‖ : ℂ)*Complex.exp (Complex.I*v))
    calc
      a = (‖a‖ : ℂ) * Complex.exp (Complex.I*a.arg) := by
        simpa [mul_comm Complex.I] using (Complex.norm_mul_exp_arg_mul_I a).symm
      _ = _ := by
        rw [← hsum, Complex.ofReal_add, mul_add, Complex.exp_add]
        ring
  · change b = star (Complex.exp (Complex.I*u)) * ((‖b‖ : ℂ)*Complex.exp (Complex.I*v))
    calc
      b = (‖b‖ : ℂ) * Complex.exp (Complex.I*b.arg) := by
        simpa [mul_comm Complex.I] using (Complex.norm_mul_exp_arg_mul_I b).symm
      _ = _ := by rw [← hdiff, Complex.ofReal_sub, ← phase_difference]; ring

theorem phase_rotation_generate :
    Subgroup.closure (Set.range diagonalPhase ∪ Set.range realRotation) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨u,t,v,rfl⟩ := su2_euler_factorization g
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.subset_closure (Or.inl ⟨u,rfl⟩))
    (Subgroup.subset_closure (Or.inr ⟨t,rfl⟩)))
    (Subgroup.subset_closure (Or.inl ⟨v,rfl⟩))

/-- Infinitesimal actions used by the coordinate ODE comparison. -/
def phaseGenerator : Space →L[ℝ] Space :=
  (Complex.I • ContinuousLinearMap.fst ℝ ℂ ℂ).prod
    (-Complex.I • ContinuousLinearMap.snd ℝ ℂ ℂ)

def rotationGenerator : Space →L[ℝ] Space :=
  (-ContinuousLinearMap.snd ℝ ℂ ℂ).prod (ContinuousLinearMap.fst ℝ ℂ ℂ)

@[simp] theorem phaseGenerator_apply (z : Space) :
    phaseGenerator z = (Complex.I*z.1, -Complex.I*z.2) := rfl
@[simp] theorem rotationGenerator_apply (z : Space) :
    rotationGenerator z = (-z.2,z.1) := rfl

theorem diagonalPhase_zero_action (z : Space) : diagonalPhase 0 • z = z := by
  simp [diagonalPhase_space_smul]
theorem realRotation_zero_action (z : Space) : realRotation 0 • z = z := by
  simp [realRotation_space_smul]

theorem diagonalPhase_action_deriv (z : Space) (t : ℝ) :
    HasDerivAt (fun s : ℝ => diagonalPhase s • z)
      (phaseGenerator (diagonalPhase t • z)) t := by
  have he := (((hasDerivAt_id t).ofReal_comp).const_mul Complex.I).cexp
  have h := (he.mul_const z.1).prodMk ((he.star).mul_const z.2)
  convert h using 1 <;> simp [diagonalPhase_space_smul, phaseGenerator_apply,
    mul_comm, mul_left_comm]

theorem realRotation_action_deriv (z : Space) (t : ℝ) :
    HasDerivAt (fun s : ℝ => realRotation s • z)
      (rotationGenerator (realRotation t • z)) t := by
  have hc := (Real.hasDerivAt_cos t).ofReal_comp
  have hs := (Real.hasDerivAt_sin t).ofReal_comp
  have h := ((hc.mul_const z.1).sub (hs.mul_const z.2)).prodMk
    ((hs.mul_const z.1).add (hc.mul_const z.2))
  convert h using 1 <;> simp [realRotation_space_smul, rotationGenerator_apply,
    neg_add_rev, sub_eq_add_neg, add_comm]

/-- Two families of coordinate lifts suffice; no SU(2) homomorphism is required. -/
theorem haar_pushforward_invariant_of_phase_rotation
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (Φ : G → Space) (hΦ : Continuous Φ)
    (hd : ∀ t : ℝ, ∃ h : G, ∀ g, Φ (h*g) = diagonalPhase t • Φ g)
    (hr : ∀ t : ℝ, ∃ h : G, ∀ g, Φ (h*g) = realRotation t • Φ g) :
    MeasureTheory.SMulInvariantMeasure SU2 Space (MeasureTheory.Measure.map Φ (normalizedHaar G)) := by
  apply haar_pushforward_invariant_of_generators Φ hΦ _ phase_rotation_generate
  rintro k (⟨t,rfl⟩ | ⟨t,rfl⟩)
  · exact hd t
  · exact hr t

end MathieuProperty.Hopf
