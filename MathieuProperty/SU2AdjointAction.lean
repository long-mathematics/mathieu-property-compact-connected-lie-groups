import MathieuProperty.SU2AdjointAlgebra
import MathieuProperty.RepresentationImage
import MathieuProperty.SU2CentralQuotient

/-! Actual SU(2) conjugation on the compact three-dimensional matrix algebra. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathieuProperty.SU2AdjointAlgebra
open Hopf Matrix
attribute [local instance] LieRing.ofAssociativeRing

/-- Conjugation by a determinant-one unitary matrix preserves the compact algebra. -/
theorem conjugate_mem (g : SU2) (A : Algebra) :
    g.val * A.val * star g.val ∈ compactAlgebra := by
  refine ⟨?_,?_⟩
  · simp [star_mul,A.property.1,mul_assoc]
  · rw [Matrix.trace_mul_cycle, g.property.1.1, one_mul, A.property.2]

/-- The real-linear adjoint action, as actual matrix conjugation. -/
def conjugate (g : SU2) : Algebra →ₗ[ℝ] Algebra where
  toFun A := ⟨g.val * A.val * star g.val,conjugate_mem g A⟩
  map_add' A B := by apply Subtype.ext; simp [mul_add,add_mul]
  map_smul' r A := by apply Subtype.ext; simp

@[simp] theorem conjugate_val (g : SU2) (A : Algebra) :
    (conjugate g A).val = g.val * A.val * star g.val := rfl

@[simp] theorem conjugate_one (A : Algebra) : conjugate 1 A = A := by
  apply Subtype.ext
  change (1 : Mat) * A.val * star (1 : Mat) = A.val
  simp

theorem conjugate_mul (g h : SU2) (A : Algebra) :
    conjugate (g*h) A = conjugate g (conjugate h A) := by
  apply Subtype.ext
  change (g.val*h.val) * A.val * star (g.val*h.val) =
    g.val * (h.val*A.val*star h.val) * star g.val
  simp [star_mul,mul_assoc]

/-- The actual finite-dimensional real adjoint representation of SU(2). -/
def representation : Representation ℝ SU2 Algebra where
  toFun := conjugate
  map_one' := by apply LinearMap.ext; intro A; exact conjugate_one A
  map_mul' g h := by apply LinearMap.ext; intro A; exact conjugate_mul g h A

/-- Matrix conjugation preserves the Lie bracket. -/
theorem conjugate_lie (g : SU2) (A B : Algebra) :
    conjugate g ⁅A,B⁆ = ⁅conjugate g A,conjugate g B⁆ := by
  apply Subtype.ext
  change g.val * (A.val*B.val-B.val*A.val) * star g.val =
    (g.val*A.val*star g.val)*(g.val*B.val*star g.val) -
      (g.val*B.val*star g.val)*(g.val*A.val*star g.val)
  simp only [mul_sub,sub_mul,mul_assoc]
  simp only [← mul_assoc (star g.val) g.val,g.property.1.1,one_mul]

/-- Each group element acts by a Lie-algebra automorphism. -/
def conjugateEquiv (g : SU2) : Algebra ≃ₗ⁅ℝ⁆ Algebra :=
  { conjugate g with
    invFun := conjugate g⁻¹
    left_inv A := by
      change conjugate g⁻¹ (conjugate g A) = A
      rw [← conjugate_mul,inv_mul_cancel,conjugate_one]
    right_inv A := by
      change conjugate g (conjugate g⁻¹ A) = A
      rw [← conjugate_mul,mul_inv_cancel,conjugate_one]
    map_lie' := fun {A} {B} => conjugate_lie g A B }

/-- The adjoint orbit of the third compact basis vector is the Hopf sphere. -/
theorem conjugate_basis_two (z : Sphere) :
    conjugate (sphereToSU2 z) (basis 2) =
      coordinates ![-(Hopf.u z.val).im,(Hopf.u z.val).re,Hopf.tau z.val] := by
  apply Subtype.ext
  simp only [conjugate_val,basis_apply,coordinates_val]
  change sphereMatrix z * matrixCoordinates (Pi.single 2 1) * star (sphereMatrix z) = _
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [sphereMatrix,matrixCoordinates,Hopf.u,Hopf.tau,Complex.normSq_apply,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply] <;> ring

/-- Every unit vector in the compact algebra lies in that adjoint orbit. -/
theorem conjugate_basis_two_surjective (x : Fin 3 → ℝ)
    (hx : x 0^2+x 1^2+x 2^2 = 1) :
    ∃ g : SU2, conjugate g (basis 2) = coordinates x := by
  have ht0 : -1 ≤ x 2 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  have ht1 : x 2 ≤ 1 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  let w : ℂ := (x 1 : ℂ)-Complex.I*x 0
  have hn : ‖w‖^2 = 1-x 2^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [w,Complex.normSq_apply]
    nlinarith [hx]
  have hs : Real.sqrt (1-x 2^2) = ‖w‖ := by rw [← hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  let z : Sphere := hopfCoordinates ⟨x 2,ht0,ht1⟩ w.arg 0
  have hu : Hopf.u z.val = w := by
    rw [show z.val = coordinatePoint (x 2) w.arg 0 from rfl,
      coordinatePoint_u _ _ _ ht0 ht1,Complex.ofReal_zero,sub_zero,hs]
    simpa [mul_comm Complex.I] using (Complex.norm_mul_exp_arg_mul_I w).symm
  have ht : Hopf.tau z.val = x 2 := coordinatePoint_tau _ _ _ ht0 ht1
  refine ⟨sphereToSU2 z,?_⟩
  rw [conjugate_basis_two,hu,ht]
  congr 1
  ext i; fin_cases i <;> simp [w]

/-- Diagonal phases fix the third compact basis vector. -/
theorem conjugate_phase_basis_two (t : ℝ) : conjugate (diagonalPhase t) (basis 2) = basis 2 := by
  rw [diagonalPhase,conjugate_basis_two,basis_apply]
  congr 1
  ext i; fin_cases i <;> simp [Hopf.u,Hopf.tau,Complex.normSq_eq_norm_sq,Complex.norm_exp]

/-- A diagonal phase rotates the first two compact coordinates by twice its angle. -/
theorem conjugate_phase_basis_zero (t : ℝ) :
    conjugate (diagonalPhase t) (basis 0) =
      coordinates ![(Complex.exp (Complex.I*t)^2).re,(Complex.exp (Complex.I*t)^2).im,0] := by
  apply Subtype.ext
  simp only [conjugate_val,basis_apply,coordinates_val]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [diagonalPhase,sphereToSU2,sphereMatrix,matrixCoordinates,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,pow_two] <;> ring

/-- Fixing the third basis vector forces the first image into its equatorial plane. -/
theorem equiv_fix_two_read_zero (e : Algebra ≃ₗ⁅ℝ⁆ Algebra) (he : e (basis 2) = basis 2) :
    readCoordinates (e (basis 0)) 2 = 0 := by
  have hk := LieAlgebra.killingForm_of_equiv_apply e (basis 0) (basis 2)
  rw [he,← coordinates_read (e (basis 0))] at hk
  simp only [basis_apply,killing_coordinates] at hk
  norm_num at hk
  simpa only [basis_apply] using hk

/-- The first and third basis vectors determine an automorphism, since their
bracket is twice the second. -/
theorem equiv_ext_zero_two (e f : Algebra ≃ₗ⁅ℝ⁆ Algebra)
    (h0 : e (basis 0) = f (basis 0)) (h2 : e (basis 2) = f (basis 2)) : e = f := by
  have h1 : e (basis 1) = f (basis 1) := by
    have he := congrArg e basis_cyclic.2.2
    have hf := congrArg f basis_cyclic.2.2
    simp only [LieEquiv.map_lie,map_smul,h0,h2] at he hf
    have hs : (2 : ℝ) • (e (basis 1)-f (basis 1)) = 0 := by
      rw [smul_sub,← he,← hf,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_left (by norm_num))
  have hh : e.toLinearMap = f.toLinearMap := by
    apply basis.ext
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  apply LieEquiv.ext
  intro x
  exact LinearMap.congr_fun hh x

/-- An automorphism fixing the third basis vector is conjugation by a diagonal phase. -/
theorem equiv_fix_two_is_phase (e : Algebra ≃ₗ⁅ℝ⁆ Algebra) (he : e (basis 2) = basis 2) :
    ∃ t : ℝ, conjugateEquiv (diagonalPhase t) = e := by
  let x := readCoordinates (e (basis 0))
  have hx2 : x 2 = 0 := equiv_fix_two_read_zero e he
  have hn : x 0^2+x 1^2 = 1 := by
    have hh := equiv_norm_sq e (Pi.single 0 1)
    simp only [← basis_apply] at hh
    change x 0^2+x 1^2+x 2^2 = _ at hh
    norm_num [hx2] at hh
    exact hh
  let w : ℂ := (x 0 : ℂ)+Complex.I*x 1
  have hwn : ‖w‖ = 1 := by
    have hs : ‖w‖^2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simpa [w,Complex.normSq_apply,pow_two] using hn
    nlinarith [norm_nonneg w]
  let t := w.arg/2
  have ht : Complex.exp (Complex.I*t)^2 = w := by
    rw [pow_two,← Complex.exp_add]
    have ha : Complex.I*(t:ℂ)+Complex.I*(t:ℂ) = w.arg*Complex.I := by dsimp [t]; push_cast; ring
    rw [ha]
    simpa [hwn] using Complex.norm_mul_exp_arg_mul_I w
  refine ⟨t,?_⟩
  apply equiv_ext_zero_two
  · change conjugate (diagonalPhase t) (basis 0) = e (basis 0)
    rw [conjugate_phase_basis_zero,ht,← coordinates_read (e (basis 0))]
    congr 1
    change ![w.re,w.im,0] = x
    ext i; fin_cases i <;> simp [w,hx2]
  · change conjugate (diagonalPhase t) (basis 2) = e (basis 2)
    rw [conjugate_phase_basis_two,he]

/-- Every automorphism of the compact three-dimensional algebra is realized
by actual SU(2) conjugation. -/
theorem conjugateEquiv_surjective : Function.Surjective conjugateEquiv := by
  intro e
  let x := readCoordinates (e (basis 2))
  have hx : x 0^2+x 1^2+x 2^2 = 1 := by
    have hh := equiv_norm_sq e (Pi.single 2 1)
    simp only [← basis_apply] at hh
    simpa [x,basis_apply] using hh
  obtain ⟨g,hg⟩ := conjugate_basis_two_surjective x hx
  have hg' : conjugateEquiv g (basis 2) = e (basis 2) := by
    change conjugate g (basis 2) = _
    rw [hg]
    exact coordinates_read _
  let f := e.trans (conjugateEquiv g).symm
  have hf : f (basis 2) = basis 2 := by
    change (conjugateEquiv g).symm (e (basis 2)) = basis 2
    rw [← hg',(conjugateEquiv g).symm_apply_apply]
  obtain ⟨t,ht⟩ := equiv_fix_two_is_phase f hf
  refine ⟨g*diagonalPhase t,?_⟩
  apply LieEquiv.ext
  intro A
  change conjugate (g*diagonalPhase t) A = e A
  rw [conjugate_mul]
  change conjugateEquiv g (conjugateEquiv (diagonalPhase t) A) = e A
  rw [ht]
  exact (conjugateEquiv g).apply_symm_apply (e A)

/-- SU(2) conjugation lands in the repository's concrete automorphism group. -/
def automorphismHom : SU2 →* LieAutomorphism.Group Algebra where
  toFun g := ⟨RepresentationImage.unitHom representation g,fun A B => conjugate_lie g A B⟩
  map_one' := by apply Subtype.ext; exact map_one (RepresentationImage.unitHom representation)
  map_mul' g h := by apply Subtype.ext; exact map_mul (RepresentationImage.unitHom representation) g h

@[simp] theorem automorphismHom_apply (g : SU2) (A : Algebra) :
    (automorphismHom g).val.val A = conjugate g A := rfl

theorem automorphismHom_surjective : Function.Surjective automorphismHom := by
  intro u
  let e : Algebra ≃ₗ⁅ℝ⁆ Algebra :=
    { (ContinuousLinearEquiv.ofUnit u.val).toLinearEquiv with
      map_lie' := fun {A} {B} => u.property A B }
  obtain ⟨g,hg⟩ := conjugateEquiv_surjective e
  refine ⟨g,?_⟩
  apply Subtype.ext
  apply Units.ext
  apply ContinuousLinearMap.ext
  intro A
  change conjugateEquiv g A = e A
  rw [hg]

theorem automorphismHom_continuous : Continuous automorphismHom := by
  apply Continuous.subtype_mk
  apply RepresentationImage.unitHom_continuous
  apply continuous_clm_apply.mpr
  intro A
  change Continuous (fun g : SU2 => conjugate g A)
  apply Continuous.subtype_mk
  change Continuous (fun g : SU2 => g.val * A.val * star g.val)
  fun_prop

/-- The conjugation kernel is exactly the concrete SU(2) center, already
identified with the two scalar matrices ±1. -/
theorem automorphismHom_ker : automorphismHom.ker = Subgroup.center SU2 := by
  ext g
  constructor
  · intro hg
    have hfix (A : Algebra) : conjugate g A = A := by
      have hh := congrArg (fun u : LieAutomorphism.Group Algebra => u.val.val A) hg
      exact hh
    have hcomm (A : Algebra) : g.val * A.val = A.val * g.val := by
      have hh := congrArg (fun A : Algebra => A.val * g.val) (hfix A)
      simpa only [conjugate_val,mul_assoc,g.property.1.1,mul_one] using hh
    have hz := congrArg (fun M : Mat => M 0 1) (hcomm (basis 2))
    have hx := congrArg (fun M : Mat => M 0 1) (hcomm (basis 0))
    simp [basis_apply,coordinates_val,matrixCoordinates,Matrix.mul_apply,Fin.sum_univ_two] at hz hx
    have h01 : g.val 0 1 = 0 := by
      have h : g.val 0 1 * Complex.I = 0 := by linear_combination -hz / 2
      exact (mul_eq_zero.mp h).resolve_right Complex.I_ne_zero
    have h10 : g.val 1 0 = 0 := by
      have he := (su2_entries g).1
      rw [h01] at he
      simpa using he.symm
    have hm : g.val = (g.val 0 0) • (1 : Mat) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply,h01,h10,← hx]
    apply Subgroup.mem_center_iff.mpr
    intro h
    apply Subtype.ext
    change h.val*g.val = g.val*h.val
    rw [hm]
    simp only [Matrix.mul_smul,Matrix.smul_mul,mul_one,one_mul]
  · intro hg
    change automorphismHom g = 1
    apply Subtype.ext
    apply Units.ext
    apply ContinuousLinearMap.ext
    intro A
    change conjugate g A = A
    apply Subtype.ext
    change g.val*A.val*star g.val = A.val
    rcases (su2_mem_center_iff g).mp hg with h | h <;> simp [h]

/-- The concrete adjoint form is precisely SU(2)/{±1}, as a topological group. -/
def quotientEquiv : SU2Adjoint ≃ₜ* LieAutomorphism.Group Algebra := by
  let e := (QuotientGroup.quotientMulEquivOfEq automorphismHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective automorphismHom automorphismHom_surjective)
  have hc : Continuous e := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous automorphismHom
    exact automorphismHom_continuous
  exact { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

/-- Euler parameters exhibit SU(2) as a continuous image of connected Euclidean space. -/
theorem su2_connected : ConnectedSpace SU2 := by
  have hr : Continuous realRotation := by
    apply su2SphereHomeomorph.symm.continuous.comp
    apply continuous_induced_rng.mpr
    change Continuous (fun t : ℝ => ((Real.cos t : ℂ),(Real.sin t : ℂ)))
    fun_prop
  let f : ℝ × (ℝ × ℝ) → SU2 := fun x => diagonalPhase x.1 * realRotation x.2.1 * diagonalPhase x.2.2
  have hf : Continuous f := (continuous_diagonalPhase.comp continuous_fst).mul
    (hr.comp (continuous_fst.comp continuous_snd)) |>.mul
      (continuous_diagonalPhase.comp (continuous_snd.comp continuous_snd))
  have hs : Function.Surjective f := by
    intro g
    obtain ⟨u,t,v,hg⟩ := su2_euler_factorization g
    exact ⟨(u,(t,v)),hg.symm⟩
  exact hs.connectedSpace hf

/-- The full compact three-dimensional automorphism group is connected. -/
theorem automorphism_connected : ConnectedSpace (LieAutomorphism.Group Algebra) := by
  let : ConnectedSpace SU2 := su2_connected
  exact automorphismHom_surjective.connectedSpace automorphismHom_continuous

end MathieuProperty.SU2AdjointAlgebra
