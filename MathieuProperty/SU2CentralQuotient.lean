import MathieuProperty.CenterDescent
import MathieuProperty.SU2Witness

/-! Concrete center descent for the defining SU(2) witness. This does not
identify an arbitrary rank-one compact simple group with the adjoint quotient. -/
noncomputable section
namespace MathieuProperty.Hopf

/-- Every central SU(2) matrix acts by a unit scalar, proved from two explicit
matrices rather than an assumed irreducible representation. -/
theorem su2_center_scalar (z : Subgroup.center SU2) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ z.val.val = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  let d : SU2 := sphereToSU2 ⟨(Complex.I,0), by norm_num [a]⟩
  let j : SU2 := sphereToSU2 ⟨(0,1), by norm_num [a]⟩
  have hd := congrArg (fun k : SU2 => k.val 1 0) (Subgroup.mem_center_iff.mp z.property d)
  have hj := congrArg (fun k : SU2 => k.val 1 0) (Subgroup.mem_center_iff.mp z.property j)
  simp [d, j, sphereToSU2, sphereMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    (su2_entries z.val).2] at hd hj
  have hb : z.val.val 1 0 = 0 := by
    have hh : z.val.val 1 0 * Complex.I = 0 := by linear_combination -hd / 2
    exact (mul_eq_zero.mp hh).resolve_right Complex.I_ne_zero
  have ha : ‖z.val.val 0 0‖ = 1 := by
    have h := su2_first_column z.val
    simp only [a, hb, map_zero, add_zero, Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (z.val.val 0 0)]
  refine ⟨z.val.val 0 0,ha,?_⟩
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.smul_apply, (su2_entries z.val).1,
      (su2_entries z.val).2, hb, ← hj]

/-- The concrete center consists precisely of the two scalar matrices ±1. -/
theorem su2_mem_center_iff (g : SU2) :
    g ∈ Subgroup.center SU2 ↔
      g.val = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∨ g.val = -1 := by
  constructor
  · intro hg
    obtain ⟨c,_,hc⟩ := su2_center_scalar ⟨g,hg⟩
    have hd : c^2 = 1 := by
      have h := g.property.2
      change Matrix.det g.val = 1 at h
      rw [hc, Matrix.det_smul] at h
      simpa using h
    rcases sq_eq_one_iff.mp hd with rfl | rfl
    · exact Or.inl (by simpa using hc)
    · exact Or.inr (by simpa using hc)
  · intro hg
    apply Subgroup.mem_center_iff.mpr
    intro h
    apply Subtype.ext
    change h.val * g.val = g.val * h.val
    rcases hg with hg | hg <;> simp [hg]

/-- Pure and marked moments descend to every central quotient of SU(2). -/
theorem su2_central_quotient_tower (N : Subgroup SU2) [N.Normal]
    (hN : N ≤ Subgroup.center SU2)
    [MeasurableSpace (SU2 ⧸ N)] [BorelSpace (SU2 ⧸ N)] :
    ∃ P Q : representativeFunctions (G := SU2 ⧸ N),
      (∀ m : ℕ, 1 ≤ m → representativeIntegral (SU2 ⧸ N) (P^m) = 0) ∧
      (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
        representativeIntegral (SU2 ⧸ N) (Q^s * P^m) =
          (momentConstant m : ℂ) * ((m-1).choose (s-1) : ℂ)) ∧
      ¬ HasMathieuProperty (SU2 ⧸ N) := by
  have hs : ∀ z ∈ N, ∃ c : ℂ, ‖c‖ = 1 ∧ definingMatrixRepresentation.toMonoidHom z = c • 1 := by
    intro z hz
    exact su2_center_scalar ⟨z,hN hz⟩
  obtain ⟨A,T,U,V,P,Q,h⟩ := MatrixRepresentation.descended_hopf_functions
    definingMatrixRepresentation N hs ![1,0] ![0,1] ![1,0]
  let q : SU2 →* SU2 ⧸ N := QuotientGroup.mk' N
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hP : representativePullback q hq P = su2P := by
    apply Subtype.ext
    ext g
    have hh := (h g).2.2.2.2.1
    simpa [q, representativePullback, su2P_apply, p, su2ToSphere,
      MatrixRepresentation.coefficient_apply, Fin.sum_univ_two, definingMatrixRepresentation] using hh
  have hQ : representativePullback q hq Q = su2Q := by
    apply Subtype.ext
    ext g
    have hh := (h g).2.2.2.2.2
    simpa [q, representativePullback, su2Q_apply, Hopf.q, su2ToSphere,
      MatrixRepresentation.coefficient_apply, Fin.sum_univ_two, definingMatrixRepresentation] using hh
  have hpure (m : ℕ) (hm : 1 ≤ m) : representativeIntegral (SU2 ⧸ N) (P^m) = 0 := by
    rw [← representativeIntegral_pullback q hq hqs, map_pow, hP]
    exact su2_representative_pure m hm
  have hmarked (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) :
      representativeIntegral (SU2 ⧸ N) (Q^s * P^m) =
        (momentConstant m : ℂ) * ((m-1).choose (s-1) : ℂ) := by
    rw [← representativeIntegral_pullback q hq hqs, map_mul, map_pow, map_pow, hQ, hP]
    exact su2_representative_marked m s hm hs
  refine ⟨P,Q,hpure,hmarked,?_⟩
  apply not_isMathieuSubspace_of_witness (LinearMap.ker (representativeIntegral (SU2 ⧸ N))) P Q hpure
  intro m hm
  change representativeIntegral (SU2 ⧸ N) (Q * P^m) ≠ 0
  have hh := hmarked m 1 hm (by omega)
  simp only [pow_one, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one] at hh
  rw [hh]
  exact Complex.ofReal_ne_zero.mpr (momentConstant_pos m).ne'

abbrev SU2Adjoint := SU2 ⧸ Subgroup.center SU2
instance : MeasurableSpace SU2Adjoint := borel SU2Adjoint
instance : BorelSpace SU2Adjoint := ⟨rfl⟩

theorem su2_adjoint_not_mathieu : ¬ HasMathieuProperty SU2Adjoint :=
  (su2_central_quotient_tower (Subgroup.center SU2) le_rfl).choose_spec.choose_spec.2.2

/-- The exact rank-one geometric identification needed for the main proof
suffices without any simply connected covering theorem. -/
theorem not_mathieu_of_center_quotient_equiv
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : (G ⧸ Subgroup.center G) ≃ₜ* SU2Adjoint) : ¬ HasMathieuProperty G := by
  let π : G →* SU2Adjoint := e.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)
  apply not_mathieuProperty_of_quotient π
    (e.continuous.comp QuotientGroup.continuous_mk)
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) su2_adjoint_not_mathieu

end MathieuProperty.Hopf
