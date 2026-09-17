import MathieuProperty.RadialTransfer
import MathieuProperty.AbelianAlgebra

/-! Polynomial matrix-entry representatives and the exact Mathieu counterexample on SU(2). -/

noncomputable section
open MeasureTheory
namespace MathieuProperty
namespace Abelian

theorem matrix_entry_representatives (g : Hopf.SU2) :
    A₀ (g.val 0 0) (g.val 0 1) (g.val 1 0) (g.val 1 1) =
      (Hopf.a (Hopf.su2ToSphere g).val : ℂ) ∧
    U₀ (g.val 0 0) (g.val 0 1) = Hopf.u (Hopf.su2ToSphere g).val ∧
    V₀ (g.val 1 0) (g.val 1 1) = Hopf.v (Hopf.su2ToSphere g).val ∧
    T₀ (g.val 0 0) (g.val 0 1) (g.val 1 0) (g.val 1 1) =
      (Hopf.tau (Hopf.su2ToSphere g).val : ℂ) := by
  rw [(Hopf.su2_entries g).1, (Hopf.su2_entries g).2]
  simp only [A₀, U₀, V₀, T₀, Hopf.su2ToSphere, Hopf.a, Hopf.u, Hopf.v, Hopf.tau,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first | trivial | ring

theorem matrix_entry_pair (g : Hopf.SU2) :
    entryP (g.val 0 0) (g.val 0 1) (g.val 1 0) (g.val 1 1) = Hopf.p (Hopf.su2ToSphere g) ∧
    U₀ (g.val 0 0) (g.val 0 1) = Hopf.q (Hopf.su2ToSphere g) := by
  obtain ⟨hA, hU, hV, hT⟩ := matrix_entry_representatives g
  constructor
  · simp only [entryP, hA, hU, hV, hT, Hopf.p, Hopf.P]
  · exact hU

end Abelian
namespace Hopf

def definingMatrixRepresentation : MatrixRepresentation SU2 (Fin 2) where
  toMonoidHom := (Matrix.specialUnitaryGroup (Fin 2) ℂ).subtype
  continuous_entry i j := continuous_subtype_val.matrix_elem i j

def su2Entry (i j : Fin 2) : representativeFunctions (G := SU2) :=
  ⟨definingMatrixRepresentation.entry i j, entry_mem_representative _ i j⟩

@[simp] theorem su2Entry_apply (i j : Fin 2) (g : SU2) : (su2Entry i j).val g = g.val i j := rfl

def su2P : representativeFunctions (G := SU2) :=
  Abelian.entryP (su2Entry 0 0) (su2Entry 0 1) (su2Entry 1 0) (su2Entry 1 1)

def su2Q : representativeFunctions (G := SU2) := Abelian.U₀ (su2Entry 0 0) (su2Entry 0 1)

theorem su2P_apply (g : SU2) : su2P.val g = p (su2ToSphere g) := by
  change Abelian.entryP (g.val 0 0) (g.val 0 1) (g.val 1 0) (g.val 1 1) = _
  exact (Abelian.matrix_entry_pair g).1

theorem su2Q_apply (g : SU2) : su2Q.val g = q (su2ToSphere g) := by
  change Abelian.U₀ (g.val 0 0) (g.val 0 1) = _
  exact (Abelian.matrix_entry_pair g).2

def basePoint : Sphere := ⟨(1, 0), by simp [a]⟩

theorem su2_smul_basePoint (g : SU2) : g • basePoint = su2ToSphere g := by
  apply Subtype.ext
  change g • ((1, 0) : Space) = (g.val 0 0, g.val 1 0)
  simp [su2_smul_apply]

theorem su2_firstColumn_integral {f : Sphere → ℂ} (hf : Continuous f) :
    (∫ g : SU2, f (su2ToSphere g) ∂normalizedHaar SU2) = ∫ z, f z ∂surfaceMeasure := by
  simpa only [su2_smul_basePoint] using su2_orbit_integral basePoint hf

theorem su2_representative_pure (m : ℕ) (hm : 1 ≤ m) :
    representativeIntegral SU2 (su2P ^ m) = 0 := by
  change (∫ g : SU2, su2P.val g ^ m ∂normalizedHaar SU2) = 0
  simp_rw [su2P_apply]
  rw [su2_firstColumn_integral (f := fun z => p z ^ m) (continuous_p.pow m), sphere_pure m hm]

theorem su2_representative_marked (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
    representativeIntegral SU2 (su2Q ^ s * su2P ^ m) =
      (momentConstant m : ℂ) * ((m - 1).choose (s - 1) : ℂ) := by
  change (∫ g : SU2, su2Q.val g ^ s * su2P.val g ^ m ∂normalizedHaar SU2) = _
  simp_rw [su2P_apply, su2Q_apply]
  rw [su2_firstColumn_integral (f := fun z => q z ^ s * p z ^ m)
    ((continuous_q.pow s).mul (continuous_p.pow m)), sphere_marked m s hm hs]

theorem SU2_not_mathieu : ¬ HasMathieuProperty SU2 := by
  apply not_isMathieuSubspace_of_witness (LinearMap.ker (representativeIntegral SU2)) su2P su2Q
  · intro m hm
    exact su2_representative_pure m hm
  · intro m hm
    change representativeIntegral SU2 (su2Q * su2P ^ m) ≠ 0
    have h := su2_representative_marked m 1 hm (by omega)
    simp only [pow_one, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one] at h
    rw [h]
    exact Complex.ofReal_ne_zero.mpr (momentConstant_pos m).ne'

end Hopf
end MathieuProperty
