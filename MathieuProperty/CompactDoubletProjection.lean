import MathieuProperty.CompactRootReality
import MathieuProperty.RootDoubletModule
import MathieuProperty.SU2Generators

/-! Global coordinate covectors obtained from the complexified invariant form.
Pairing against conjugate doublet vectors avoids constructing a complement
while still proving the intertwining identities on the whole algebra. -/
noncomputable section
open scoped TensorProduct
namespace MathieuProperty.CompactDoubletProjection
open ComplexParts Hopf
set_option backward.isDefEq.respectTransparency false
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (B : LinearMap.BilinForm ℝ L)

/-- Invariance of the real form extends to the complexification. -/
theorem baseChange_lieInvariant (hinv : B.lieInvariant L) :
    (B.baseChange ℂ).lieInvariant (ℂ ⊗[ℝ] L) := by
  intro x y z
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      induction z using TensorProduct.inductionOn with
      | tmul c z =>
        simp [Complex.real_smul]
        rw [hinv x y z]
        push_cast
        ring
      | add z w hz hw => simp only [lie_add, map_add, hz, hw]; ring
    | add y w hy hw =>
      simp only [lie_add, map_add, LinearMap.add_apply, hy, hw]; ring
  | add x w hx hw =>
    simp only [add_lie, map_add, LinearMap.add_apply, hx, hw]; ring

/-- The Hermitian self-pairing is the sum of the two positive real squares. -/
theorem pairing_self (hB : B.IsSymm) (v : ℂ ⊗[ℝ] L) :
    B.baseChange ℂ (conj v) v = ((B (re v) (re v) + B (im v) (im v) : ℝ) : ℂ) := by
  conv_lhs => rw [decomposition v]
  simp only [map_add, LinearMap.add_apply, conj_tmul, star_one, Complex.star_def,
    Complex.conj_I, LinearMap.BilinForm.baseChange_tmul, Complex.real_smul]
  rw [hB.eq (im v) (re v)]
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem pairing_self_ne_zero (hB : B.IsSymm)
    (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) {v : ℂ ⊗[ℝ] L} (hv : v ≠ 0) :
    B.baseChange ℂ (conj v) v ≠ 0 := by
  rw [pairing_self B hB]
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  have hn (x : L) : 0 ≤ B x x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  by_cases hr : re v = 0
  · have hi : im v ≠ 0 := by
      intro hi
      exact hv (by simpa [hr,hi] using decomposition v)
    simpa [hr] using hpos (im v) hi
  · exact add_pos_of_pos_of_nonneg (hpos (re v) hr) (hn _)

/-- The global complex-linear coordinate pair. -/
def coordinates (v w : ℂ ⊗[ℝ] L) : (ℂ ⊗[ℝ] L) →ₗ[ℂ] Space :=
  (B.baseChange ℂ (conj v)).prod (B.baseChange ℂ (conj w))

/-- Its restriction to the actual real algebra. -/
def realCoordinates (v w : ℂ ⊗[ℝ] L) : L →ₗ[ℝ] Space :=
  ((coordinates B v w).restrictScalars ℝ).comp (TensorProduct.mk ℝ ℂ L 1)

/-- Invariance and conjugation turn a known doublet action into a global
coordinate identity, not just an identity on the doublet subspace. -/
theorem pairing_lie_of_conj_eq_neg (hinv : B.lieInvariant L)
    {a b v y : ℂ ⊗[ℝ] L} (ha : conj a = -b) (hv : ⁅b,v⁆ = y) (x : ℂ ⊗[ℝ] L) :
    B.baseChange ℂ (conj v) ⁅a,x⁆ = B.baseChange ℂ (conj y) x := by
  have hb : conj b = -a := by
    have h := congrArg conj ha
    simpa only [conj_conj, map_neg, neg_eq_iff_eq_neg] using h.symm
  have hy := congrArg conj hv
  rw [conj_lie, hb, neg_lie] at hy
  have hi := baseChange_lieInvariant B hinv a (conj v) x
  rw [← hy, map_neg, LinearMap.neg_apply]
  linear_combination hi

/-- The standard adjoint-doublet covectors intertwine on the entire algebra. -/
theorem doublet_coordinate_actions [FiniteDimensional ℝ L] (hinv : B.lieInvariant L)
    {h e f v : ℂ ⊗[ℝ] L} (t : IsSl2Triple h e f)
    (hp : t.symm.HasPrimitiveVectorWith v (1 : ℂ)) (hcon : f = -conj e)
    (x : ℂ ⊗[ℝ] L) :
    coordinates B v ⁅e,v⁆ ⁅e,x⁆ = (0,(coordinates B v ⁅e,v⁆ x).1) ∧
    coordinates B v ⁅e,v⁆ ⁅f,x⁆ = ((coordinates B v ⁅e,v⁆ x).2,0) ∧
    coordinates B v ⁅e,v⁆ ⁅h,x⁆ = (-(coordinates B v ⁅e,v⁆ x).1,(coordinates B v ⁅e,v⁆ x).2) := by
  have hce : conj e = -f := by rw [hcon, neg_neg]
  have hcf : conj f = -e := by simp [hcon]
  have hh : conj h = -h := by
    rw [← t.lie_e_f, conj_lie, hce, hcf, neg_lie, lie_neg, neg_neg, ← lie_skew f e]
  obtain ⟨hhv,hfv,hhw,hfw⟩ := highest_weight_one_action t.symm hp
  have hhv' : ⁅h,v⁆ = -v := by simpa only [neg_lie, neg_eq_iff_eq_neg] using hhv
  have hhw' : ⁅h,⁅e,v⁆⁆ = ⁅e,v⁆ := by simpa only [neg_lie, neg_inj] using hhw
  have hew := (highest_weight_one_lowering t.symm hp).2
  have h00 := pairing_lie_of_conj_eq_neg B hinv hce hfv x
  have h01 := pairing_lie_of_conj_eq_neg B hinv hce hfw x
  have h10 := pairing_lie_of_conj_eq_neg B hinv hcf (rfl : ⁅e,v⁆ = ⁅e,v⁆) x
  have h11 := pairing_lie_of_conj_eq_neg B hinv hcf hew x
  have h20 := pairing_lie_of_conj_eq_neg B hinv hh hhv' x
  have h21 := pairing_lie_of_conj_eq_neg B hinv hh hhw' x
  refine ⟨Prod.ext ?_ h01, Prod.ext h10 ?_, Prod.ext ?_ h21⟩
  · simpa [coordinates] using h00
  · simpa [coordinates] using h11
  · simpa [coordinates] using h20

/-- Real compact generators have the required phase and rotation actions. -/
theorem real_coordinate_actions [FiniteDimensional ℝ L] (hinv : B.lieInvariant L)
    {h e f v : ℂ ⊗[ℝ] L} (t : IsSl2Triple h e f)
    (hp : t.symm.HasPrimitiveVectorWith v (1 : ℂ)) (hcon : f = -conj e)
    (X Z : L) (hX : (1 : ℂ) ⊗ₜ[ℝ] X = e-f) (hZ : (1 : ℂ) ⊗ₜ[ℝ] Z = -Complex.I • h)
    (x : L) :
    realCoordinates B v ⁅e,v⁆ ⁅X,x⁆ = rotationGenerator (realCoordinates B v ⁅e,v⁆ x) ∧
    realCoordinates B v ⁅e,v⁆ ⁅Z,x⁆ = phaseGenerator (realCoordinates B v ⁅e,v⁆ x) := by
  have hacts := doublet_coordinate_actions B hinv t hp hcon ((1 : ℂ) ⊗ₜ[ℝ] x)
  have ht (Y : L) : (1 : ℂ) ⊗ₜ[ℝ] ⁅Y,x⁆ = ⁅(1 : ℂ) ⊗ₜ[ℝ] Y,(1 : ℂ) ⊗ₜ[ℝ] x⁆ := by simp
  constructor
  · change coordinates B v ⁅e,v⁆ ((1 : ℂ) ⊗ₜ[ℝ] ⁅X,x⁆) = _
    rw [ht, hX, sub_lie, map_sub, hacts.1, hacts.2.1]
    simp [rotationGenerator, realCoordinates, coordinates]
  · change coordinates B v ⁅e,v⁆ ((1 : ℂ) ⊗ₜ[ℝ] ⁅Z,x⁆) = _
    rw [ht, hZ, smul_lie (-Complex.I) h ((1 : ℂ) ⊗ₜ[ℝ] x), map_smul, hacts.2.2]
    ext <;> simp [phaseGenerator, realCoordinates, coordinates, mul_neg]

/-- Some actual real vector has nonzero coordinates, since the Hermitian
self-pairing of the nonzero first doublet vector is positive. -/
theorem exists_real_coordinates_ne_zero (hB : B.IsSymm)
    (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) {v : ℂ ⊗[ℝ] L} (hv : v ≠ 0)
    (w : ℂ ⊗[ℝ] L) : ∃ x : L, realCoordinates B v w x ≠ 0 := by
  by_contra! hn
  have hzero : coordinates B v w v = 0 := by
    have hd := congrArg (coordinates B v w) (decomposition v)
    rw [hd, map_add]
    have hI : Complex.I ⊗ₜ[ℝ] im v = Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] im v) := by
      simp [TensorProduct.smul_tmul']
    rw [hI, map_smul]
    change realCoordinates B v w (re v) + Complex.I • realCoordinates B v w (im v) = 0
    simp [hn]
  have hf := congrArg Prod.fst hzero
  exact pairing_self_ne_zero B hB hpos hv hf

end MathieuProperty.CompactDoubletProjection
