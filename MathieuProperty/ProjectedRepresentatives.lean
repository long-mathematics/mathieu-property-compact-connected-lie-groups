import MathieuProperty.ProjectedHaar
/-! All six Hopf quantities as genuine representative functions of projected unitary orbits. -/

noncomputable section
open MeasureTheory
namespace MathieuProperty
variable {G : Type*} [Group G] [TopologicalSpace G]

def representativeConjugate (f : representativeFunctions (G := G)) : representativeFunctions (G := G) :=
  ⟨star f.val, representative_star f.property⟩

@[simp] theorem representativeConjugate_apply (f : representativeFunctions (G := G)) (g : G) :
    (representativeConjugate f).val g = star (f.val g) := rfl

def representativeA (f₀ f₁ : representativeFunctions (G := G)) : representativeFunctions (G := G) :=
  f₀ * representativeConjugate f₀ + f₁ * representativeConjugate f₁

def representativeU (f₀ f₁ : representativeFunctions (G := G)) : representativeFunctions (G := G) :=
  2 * f₀ * representativeConjugate f₁

def representativeV (f₀ f₁ : representativeFunctions (G := G)) : representativeFunctions (G := G) :=
  2 * f₁ * representativeConjugate f₀

def representativeTau (f₀ f₁ : representativeFunctions (G := G)) : representativeFunctions (G := G) :=
  f₀ * representativeConjugate f₀ - f₁ * representativeConjugate f₁

def representativeP (f₀ f₁ : representativeFunctions (G := G)) : representativeFunctions (G := G) :=
  (representativeA f₀ f₁ + representativeU f₀ f₁) *
    (representativeA f₀ f₁ ^ 2 * representativeV f₀ f₁ -
      (2 * representativeA f₀ f₁ + representativeU f₀ f₁) * representativeTau f₀ f₁ ^ 2)

def representativeQ (f₀ f₁ : representativeFunctions (G := G)) : representativeFunctions (G := G) :=
  representativeU f₀ f₁

theorem representativeA_apply (f₀ f₁ : representativeFunctions (G := G)) (g : G) :
    (representativeA f₀ f₁).val g = (Hopf.a (f₀.val g, f₁.val g) : ℂ) := by
  change f₀.val g * star (f₀.val g) + f₁.val g * star (f₁.val g) = _
  simp [Hopf.a, Complex.normSq_eq_conj_mul_self, mul_comm]

theorem representativeU_apply (f₀ f₁ : representativeFunctions (G := G)) (g : G) :
    (representativeU f₀ f₁).val g = Hopf.u (f₀.val g, f₁.val g) := rfl

theorem representativeV_apply (f₀ f₁ : representativeFunctions (G := G)) (g : G) :
    (representativeV f₀ f₁).val g = Hopf.v (f₀.val g, f₁.val g) := rfl

theorem representativeTau_apply (f₀ f₁ : representativeFunctions (G := G)) (g : G) :
    (representativeTau f₀ f₁).val g = (Hopf.tau (f₀.val g, f₁.val g) : ℂ) := by
  change f₀.val g * star (f₀.val g) - f₁.val g * star (f₁.val g) = _
  simp [Hopf.tau, Complex.normSq_eq_conj_mul_self, mul_comm]

theorem representativeP_apply (f₀ f₁ : representativeFunctions (G := G)) (g : G) :
    (representativeP f₀ f₁).val g = Hopf.P (f₀.val g, f₁.val g) := by
  change ((representativeA f₀ f₁).val g + (representativeU f₀ f₁).val g) *
    ((representativeA f₀ f₁).val g ^ 2 * (representativeV f₀ f₁).val g -
      (2 * (representativeA f₀ f₁).val g + (representativeU f₀ f₁).val g) *
        (representativeTau f₀ f₁).val g ^ 2) = _
  rw [representativeA_apply, representativeU_apply, representativeV_apply, representativeTau_apply]
  rfl

theorem representativeQ_apply (f₀ f₁ : representativeFunctions (G := G)) (g : G) :
    (representativeQ f₀ f₁).val g = Hopf.Q (f₀.val g, f₁.val g) := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Forget only the metric structure of a unitary representation. -/
def unitaryToRepresentation (ρ : G →* (E ≃ₗᵢ[ℂ] E)) : Representation ℂ G E where
  toFun g := (ρ g).toLinearEquiv.toLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

variable [FiniteDimensional ℂ E] (ρ : G →* (E ≃ₗᵢ[ℂ] E))
  (hρ : ∀ v, Continuous (fun g => ρ g v)) (W : Submodule ℂ E)
  (e : W ≃ₗᵢ[ℂ] Hopf.EuclideanPair)

def doubletFirst : representativeFunctions (G := G) :=
  let l := (LinearMap.fst ℂ ℂ ℂ).comp (doubletProjection W e)
  let v := (doubletBaseVector W e : E)
  ⟨⟨fun g => l (ρ g v), l.continuous_of_finiteDimensional.comp (hρ v)⟩,
    representation_coefficient_mem (unitaryToRepresentation ρ) hρ l v⟩

def doubletSecond : representativeFunctions (G := G) :=
  let l := (LinearMap.snd ℂ ℂ ℂ).comp (doubletProjection W e)
  let v := (doubletBaseVector W e : E)
  ⟨⟨fun g => l (ρ g v), l.continuous_of_finiteDimensional.comp (hρ v)⟩,
    representation_coefficient_mem (unitaryToRepresentation ρ) hρ l v⟩


theorem doubletCoordinate_pair (g : G) :
    ((doubletFirst ρ hρ W e).val g, (doubletSecond ρ hρ W e).val g) = doubletCoordinates W e ρ g := rfl

def doubletA : representativeFunctions (G := G) :=
  representativeA (doubletFirst ρ hρ W e) (doubletSecond ρ hρ W e)

def doubletP : representativeFunctions (G := G) :=
  representativeP (doubletFirst ρ hρ W e) (doubletSecond ρ hρ W e)

def doubletQ : representativeFunctions (G := G) :=
  representativeQ (doubletFirst ρ hρ W e) (doubletSecond ρ hρ W e)

theorem doubletA_apply (g : G) :
    (doubletA ρ hρ W e).val g = (Hopf.a (doubletCoordinates W e ρ g) : ℂ) :=
  representativeA_apply _ _ _

theorem doubletP_apply (g : G) :
    (doubletP ρ hρ W e).val g = Hopf.P (doubletCoordinates W e ρ g) :=
  representativeP_apply _ _ _

theorem doubletQ_apply (g : G) :
    (doubletQ ρ hρ W e).val g = Hopf.Q (doubletCoordinates W e ρ g) :=
  representativeQ_apply _ _ _


theorem doubletA_real_nonneg (g : G) :
    ∃ r : ℝ, 0 ≤ r ∧ (doubletA ρ hρ W e).val g = (r : ℂ) :=
  ⟨Hopf.a (doubletCoordinates W e ρ g), Hopf.a_nonneg _, doubletA_apply ρ hρ W e g⟩

@[simp] theorem doubletA_one : (doubletA ρ hρ W e).val 1 = 1 := by
  rw [doubletA_apply, doubletCoordinates_one]
  norm_num [Hopf.a]

theorem doubletA_ne_zero : doubletA ρ hρ W e ≠ 0 := by
  intro h
  have hv := congrArg (fun f : representativeFunctions (G := G) => f.val 1) h
  rw [doubletA_one] at hv
  exact one_ne_zero hv

end MathieuProperty
