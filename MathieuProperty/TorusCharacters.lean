import MathieuProperty.AbelianCharacters
import MathieuProperty.HaarCharacters
import MathieuProperty.LaurentInterpolation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! The exact character lattice of the product of d unit circles.
Laurent monomials form a dense star algebra. Haar orthogonality forces every
continuous complex character to be one of them; interpolation proves uniqueness. -/

noncomputable section
open scoped Classical
namespace MathieuProperty

abbrev Torus (d : ℕ) := Fin d → Circle

instance torusMeasurableSpace (d : ℕ) : MeasurableSpace (Torus d) := borel (Torus d)
instance torusBorelSpace (d : ℕ) : BorelSpace (Torus d) := ⟨rfl⟩

def torusCharacter {d : ℕ} (n : Fin d → ℤ) : Torus d →ₜ* ℂ where
  toFun g := ∏ i, (g i : ℂ)^(n i)
  map_one' := by simp
  map_mul' g h := by simp [mul_zpow, Finset.prod_mul_distrib]
  continuous_toFun := by
    apply continuous_finsetProd
    intro i hi
    have hc : Continuous (fun g : Torus d => (g i : ℂ)) := continuous_subtype_val.comp (continuous_apply i)
    exact hc.zpow₀ (n i) (fun g => Or.inl (Circle.coe_ne_zero (g i)))

theorem torusCharacter_zero (d : ℕ) : torusCharacter (0 : Fin d → ℤ) = 1 := by
  ext g
  change (∏ i : Fin d, (g i : ℂ)^(0 : ℤ)) = 1
  simp

theorem torusCharacter_add {d : ℕ} (n m : Fin d → ℤ) : torusCharacter (n+m) = torusCharacter n * torusCharacter m := by
  ext g
  change (∏ i, (g i : ℂ)^(n i+m i)) = (∏ i, (g i : ℂ)^(n i)) * ∏ i, (g i : ℂ)^(m i)
  simp [zpow_add₀ (Circle.coe_ne_zero _), Finset.prod_mul_distrib]

def torusMonomial {d : ℕ} (n : Fin d → ℤ) : C(Torus d,ℂ) := (torusCharacter n).toContinuousMap

theorem torusMonomial_zero (d : ℕ) : torusMonomial (0 : Fin d → ℤ) = 1 := congrArg _ (torusCharacter_zero d)

theorem torusMonomial_add {d : ℕ} (n m : Fin d → ℤ) : torusMonomial (n+m) = torusMonomial n * torusMonomial m :=
  congrArg ContinuousMonoidHom.toContinuousMap (torusCharacter_add n m)

theorem torusMonomial_neg {d : ℕ} (n : Fin d → ℤ) : torusMonomial (-n) = star (torusMonomial n) := by
  ext g
  change (∏ i, (g i : ℂ)^(-n i)) = star (∏ i, (g i : ℂ)^(n i))
  simp only [map_prod, map_zpow₀, Complex.star_def,
    ← Circle.coe_inv_eq_conj, Circle.coe_inv, zpow_neg, inv_zpow]

theorem torusMonomial_single {d : ℕ} (i : Fin d) (g : Torus d) : torusMonomial (Pi.single i 1) g = (g i : ℂ) := by
  change (∏ j, (g j : ℂ)^((Pi.single i 1 : Fin d → ℤ) j)) = (g i : ℂ)
  simp [Pi.single_apply, Finset.prod_ite_eq']

def torusMonomialSpan (d : ℕ) : Submodule ℂ C(Torus d,ℂ) :=
  Submodule.span ℂ (Set.range torusMonomial)

theorem torusMonomial_mem {d : ℕ} (n : Fin d → ℤ) : torusMonomial n ∈ torusMonomialSpan d :=
  Submodule.subset_span ⟨n,rfl⟩

theorem torusMonomialSpan_mul {d : ℕ} {f g : C(Torus d,ℂ)}
    (hf : f ∈ torusMonomialSpan d) (hg : g ∈ torusMonomialSpan d) : f*g ∈ torusMonomialSpan d := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,rfl⟩ := hx
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m,rfl⟩ := hy
      rw [← torusMonomial_add]
      exact torusMonomial_mem _
    | zero => simp only [mul_zero]; exact (torusMonomialSpan d).zero_mem
    | add x y hx hy hx' hy' => simpa only [mul_add] using (torusMonomialSpan d).add_mem hx' hy'
    | smul c x hx hx' => simpa only [mul_smul_comm] using (torusMonomialSpan d).smul_mem c hx'
  | zero => simp only [zero_mul]; exact (torusMonomialSpan d).zero_mem
  | add x y hx hy hx' hy' => simpa only [add_mul] using (torusMonomialSpan d).add_mem hx' hy'
  | smul c x hx hx' => simpa only [smul_mul_assoc] using (torusMonomialSpan d).smul_mem c hx'

theorem torusMonomialSpan_star {d : ℕ} {f : C(Torus d,ℂ)} (hf : f ∈ torusMonomialSpan d) :
    star f ∈ torusMonomialSpan d := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,rfl⟩ := hx
    rw [← torusMonomial_neg]
    exact torusMonomial_mem _
  | zero => simp only [star_zero]; exact (torusMonomialSpan d).zero_mem
  | add x y hx hy hx' hy' => simpa only [star_add] using (torusMonomialSpan d).add_mem hx' hy'
  | smul c x hx hx' => simpa only [star_smul] using (torusMonomialSpan d).smul_mem (star c) hx'

def torusPolynomialAlgebra (d : ℕ) : StarSubalgebra ℂ C(Torus d,ℂ) where
  carrier := torusMonomialSpan d
  zero_mem' := (torusMonomialSpan d).zero_mem
  add_mem' := (torusMonomialSpan d).add_mem
  mul_mem' := torusMonomialSpan_mul
  algebraMap_mem' c := by
    have h := (torusMonomialSpan d).smul_mem c (torusMonomial_mem (0 : Fin d → ℤ))
    simpa [torusMonomial_zero, Algebra.algebraMap_eq_smul_one] using h
  star_mem' := torusMonomialSpan_star

theorem torusPolynomialAlgebra_separates (d : ℕ) : (torusPolynomialAlgebra d).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  refine ⟨torusMonomial (Pi.single i 1), ⟨_,torusMonomial_mem _,rfl⟩,?_⟩
  rw [torusMonomial_single,torusMonomial_single]
  exact fun h => hi (Subtype.ext h)

theorem torusPolynomialAlgebra_dense (d : ℕ) : (torusPolynomialAlgebra d).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ (torusPolynomialAlgebra_separates d)

/-- Every continuous complex character on the finite-dimensional torus is an
integer Laurent monomial. Density and Haar orthogonality supply the classification. -/
theorem torus_character_exists {d : ℕ} (χ : Torus d →ₜ* ℂ) : ∃ n : Fin d → ℤ, torusCharacter n = χ := by
  by_contra! hn
  let F (f : C(Torus d,ℂ)) : ℂ := haarIntegral (Torus d) (f * (inverseCharacter χ).toContinuousMap)
  have hc : Continuous F := (haarIntegralContinuous (G := Torus d)).continuous.comp
    (continuous_id.mul continuous_const)
  have hm (n : Fin d → ℤ) : F (torusMonomial n) = 0 := by
    exact (haar_character_orthogonality (torusCharacter n) χ).trans (ite_eq_right (hn n))
  have hs : ∀ f ∈ torusMonomialSpan d, F f = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨n,rfl⟩ := hf; exact hm n
    | zero => simp [F,haarIntegral]
    | add f g hf hg hf' hg' =>
      change (haarIntegralLinear (Torus d)) ((f+g)*(inverseCharacter χ).toContinuousMap) = 0
      rw [add_mul,map_add]
      change F f + F g = 0
      rw [hf',hg',add_zero]
    | smul c f hf hf' =>
      change (haarIntegralLinear (Torus d)) ((c • f)*(inverseCharacter χ).toContinuousMap) = 0
      rw [smul_mul_assoc,map_smul]
      exact smul_eq_zero_of_right c hf'
  have hclosed : IsClosed {f : C(Torus d,ℂ) | F f = 0} := isClosed_eq hc continuous_const
  have hmem : χ.toContinuousMap ∈ closure (torusPolynomialAlgebra d : Set C(Torus d,ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe,torusPolynomialAlgebra_dense]
    trivial
  have hz : F χ.toContinuousMap = 0 := hclosed.closure_subset_iff.mpr hs hmem
  have ho : F χ.toContinuousMap = 1 := by
    exact (haar_character_orthogonality χ χ).trans (ite_eq_left rfl)
  exact one_ne_zero (ho.symm.trans hz)

theorem torusCharacter_on_coordinate {d : ℕ} (n : Fin d → ℤ) (i : Fin d) (z : Circle) :
    torusCharacter n (Function.update (1 : Torus d) i z) = (z : ℂ)^(n i) := by
  change (∏ j, ((Function.update (1 : Torus d) i z) j : ℂ)^(n j)) = (z : ℂ)^(n i)
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Function.update_of_ne hji]
  · simp

theorem torusCharacter_injective (d : ℕ) : Function.Injective (@torusCharacter d) := by
  intro n m h
  funext i
  have he (z : Circle) : (z : ℂ)^(n i) = (z : ℂ)^(m i) := by
    have h' := congrArg (fun χ : Torus d →ₜ* ℂ => χ (Function.update (1 : Torus d) i z)) h
    simpa only [torusCharacter_on_coordinate] using h'
  have hz : (LaurentPolynomial.T (n i) - LaurentPolynomial.T (m i) : LaurentPolynomial ℂ) = 0 := by
    apply Abelian.laurent_eq_zero_of_circle
    intro z
    simp [he z]
  have heq := sub_eq_zero.mp hz
  have hc := congrArg (fun q : LaurentPolynomial ℂ => q.coeff (n i)) heq
  by_contra hnm
  simp [LaurentPolynomial.T_apply, eq_comm, hnm] at hc

/-- The continuous complex character lattice is exactly ℤ^d, including d=0. -/
def torusCharacterEquiv (d : ℕ) : (Fin d → ℤ) ≃ (Torus d →ₜ* ℂ) :=
  Equiv.ofBijective torusCharacter ⟨torusCharacter_injective d,torus_character_exists⟩

end MathieuProperty
