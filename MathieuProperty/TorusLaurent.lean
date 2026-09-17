import MathieuProperty.TorusCharacters
import MathieuProperty.LaurentSupport

/-! The actual representative-function algebra of the finite-dimensional
torus is isomorphic to the multivariate complex Laurent algebra. Haar character
orthogonality proves coefficient recovery, injectivity, and the constant-term
identity. The Mathieu predicates correspond exactly, including zero cases. -/

noncomputable section
open MeasureTheory
open scoped Classical
namespace MathieuProperty

def torusMonomialHom (d : ℕ) : Multiplicative (Fin d → ℤ) →* C(Torus d,ℂ) where
  toFun n := torusMonomial n.toAdd
  map_one' := torusMonomial_zero d
  map_mul' n m := torusMonomial_add n.toAdd m.toAdd

def torusLaurentMap (d : ℕ) : MultiLaurent d →ₐ[ℂ] C(Torus d,ℂ) :=
  AddMonoidAlgebra.lift ℂ C(Torus d,ℂ) (Fin d → ℤ) (torusMonomialHom d)

theorem torusLaurentMap_apply {d : ℕ} (f : MultiLaurent d) :
    torusLaurentMap d f = ∑ n ∈ f.coeff.support, f.coeff n • torusMonomial n := by
  rw [torusLaurentMap, AddMonoidAlgebra.lift_apply]
  rfl

theorem torusLaurentMap_single {d : ℕ} (n : Fin d → ℤ) (c : ℂ) :
    torusLaurentMap d (AddMonoidAlgebra.single n c) = c • torusMonomial n := by
  exact AddMonoidAlgebra.lift_single _ _ _

def torusCoefficientIntegral {d : ℕ} (n : Fin d → ℤ) : C(Torus d,ℂ) →ₗ[ℂ] ℂ where
  toFun f := haarIntegral (Torus d) (f * (inverseCharacter (torusCharacter n)).toContinuousMap)
  map_add' f g := by
    change (haarIntegralLinear (Torus d)) ((f+g)*_) = _
    rw [add_mul,map_add]
    rfl
  map_smul' c f := by
    change (haarIntegralLinear (Torus d)) ((c • f)*_) = _
    rw [smul_mul_assoc,map_smul]
    rfl

theorem torusCoefficientIntegral_monomial {d : ℕ} (m n : Fin d → ℤ) :
    torusCoefficientIntegral n (torusMonomial m) = if m = n then 1 else 0 := by
  change haarIntegral (Torus d) ((torusCharacter m).toContinuousMap * (inverseCharacter (torusCharacter n)).toContinuousMap) = _
  have h := haar_character_orthogonality (torusCharacter m) (torusCharacter n)
  simpa only [(torusCharacter_injective d).eq_iff] using h

theorem torusCoefficientIntegral_laurent {d : ℕ} (f : MultiLaurent d) (n : Fin d → ℤ) :
    torusCoefficientIntegral n (torusLaurentMap d f) = f.coeff n := by
  rw [torusLaurentMap_apply, map_sum]
  simp_rw [map_smul, torusCoefficientIntegral_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hn : n ∈ f.coeff.support
  · simp [hn]
  · simp [hn,Finsupp.notMem_support_iff.mp hn]

theorem torusLaurentMap_injective (d : ℕ) : Function.Injective (torusLaurentMap d) := by
  intro f g h
  ext n
  have he := congrArg (torusCoefficientIntegral n) h
  simpa only [torusCoefficientIntegral_laurent] using he

theorem torusLaurentMap_mem {d : ℕ} (f : MultiLaurent d) :
    torusLaurentMap d f ∈ representativeSubmodule (Torus d) := by
  rw [torusLaurentMap_apply]
  apply Submodule.sum_mem
  intro n hn
  exact Submodule.smul_mem _ _ (character_mem_representative (torusCharacter n))

theorem torusLaurentMap_range (d : ℕ) :
    (torusLaurentMap d).toLinearMap.range = representativeSubmodule (Torus d) := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    exact torusLaurentMap_mem f
  · rw [representative_eq_characterSpan]
    apply Submodule.span_le.mpr
    rintro _ ⟨χ,rfl⟩
    obtain ⟨n,rfl⟩ := torus_character_exists χ
    refine ⟨AddMonoidAlgebra.single n 1,?_⟩
    simp only [AlgHom.toLinearMap_apply,torusLaurentMap_single,one_smul]
    rfl

def torusRepresentativeMap (d : ℕ) : MultiLaurent d →ₐ[ℂ] representativeFunctions (G := Torus d) :=
  (torusLaurentMap d).codRestrict (representativeFunctions (G := Torus d)) torusLaurentMap_mem

theorem torusRepresentativeMap_bijective (d : ℕ) : Function.Bijective (torusRepresentativeMap d) := by
  constructor
  · intro f g h
    exact torusLaurentMap_injective d (congrArg Subtype.val h)
  · intro f
    have hm : f.val ∈ (torusLaurentMap d).toLinearMap.range := by
      rw [torusLaurentMap_range]
      exact f.property
    obtain ⟨p,hp⟩ := hm
    refine ⟨p,Subtype.ext hp⟩

/-- Exact algebra identification with the actual representative-function algebra. -/
def torus_representative_laurent (d : ℕ) : MultiLaurent d ≃ₐ[ℂ] representativeFunctions (G := Torus d) :=
  AlgEquiv.ofBijective (torusRepresentativeMap d) (torusRepresentativeMap_bijective d)

theorem torusCoefficientIntegral_zero (d : ℕ) :
    torusCoefficientIntegral (0 : Fin d → ℤ) = haarIntegralLinear (Torus d) := by
  ext f
  change haarIntegral (Torus d) (f * (inverseCharacter (torusCharacter (0 : Fin d → ℤ))).toContinuousMap) = _
  rw [torusCharacter_zero]
  have he : (inverseCharacter (1 : Torus d →ₜ* ℂ)).toContinuousMap = 1 := by ext g; rfl
  rw [he,mul_one]
  rfl

theorem torusLaurent_integral_constantTerm {d : ℕ} (f : MultiLaurent d) :
    haarIntegral (Torus d) (torusLaurentMap d f) = constantTerm f := by
  have h := torusCoefficientIntegral_laurent f 0
  rw [torusCoefficientIntegral_zero] at h
  exact h

/-- Haar integration on representative functions is precisely the Laurent constant term. -/
theorem torus_integral_constantTerm {d : ℕ} (f : MultiLaurent d) :
    representativeIntegral (Torus d) (torus_representative_laurent d f) = constantTerm f :=
  torusLaurent_integral_constantTerm f

def constantTermLinear (d : ℕ) : MultiLaurent d →ₗ[ℂ] ℂ where
  toFun := constantTerm
  map_add' f g := by simp [constantTerm]
  map_smul' c f := by simp [constantTerm]

theorem torus_constantTerm_kernel (d : ℕ) :
    (LinearMap.ker (representativeIntegral (Torus d))).comap (torus_representative_laurent d).toLinearMap =
      LinearMap.ker (constantTermLinear d) := by
  ext f
  simp only [Submodule.mem_comap, LinearMap.mem_ker, AlgEquiv.toLinearMap_apply, torus_integral_constantTerm]
  rfl

/-- This is an unconditional equivalence of the two Mathieu predicates, not
an assumption of the missing Duistermaat–van der Kallen theorem. -/
theorem torus_mathieu_iff_constantTerm (d : ℕ) : HasMathieuProperty (Torus d) ↔
    IsMathieuSubspace (LinearMap.ker (constantTermLinear d)) := by
  constructor
  · intro h
    rw [← torus_constantTerm_kernel]
    exact h.comap (torus_representative_laurent d).toAlgHom
  · intro h
    rw [← torus_constantTerm_kernel] at h
    have h' := h.comap (torus_representative_laurent d).symm.toAlgHom
    have he : ((LinearMap.ker (representativeIntegral (Torus d))).comap
        (torus_representative_laurent d).toLinearMap).comap
        (torus_representative_laurent d).symm.toAlgHom.toLinearMap =
        LinearMap.ker (representativeIntegral (Torus d)) := by
      ext f
      simp
    rw [he] at h'
    exact h'

theorem zero_laurent_eventual (d : ℕ) (h : MultiLaurent d) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → constantTerm (h * (0 : MultiLaurent d)^m) = 0 := by
  refine ⟨1,?_⟩
  intro m hm
  simp [zero_pow (by omega : m ≠ 0), constantTerm]

theorem zero_laurent_multiplier {d : ℕ} (f : MultiLaurent d) (m : ℕ) :
    constantTerm ((0 : MultiLaurent d)*f^m) = 0 := by simp [constantTerm]

end MathieuProperty
