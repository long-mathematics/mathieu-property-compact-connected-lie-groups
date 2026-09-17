import MathieuProperty.ZwartPunctured
import MathieuProperty.ZwartSU
/-! The 2023 SU(N) rational-frequency conjecture and its original recursive radial density. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Zwart

def oldSunPowers : ℕ → List (ℕ × ℕ)
  | 0 => []
  | 1 => []
  | n+2 => List.ofFn (fun j : Fin n => (1,j.val)) ++ [(2*n+1,0)] ++ oldSunPowers (n+1)

theorem oldSunPowers_length (n : ℕ) : (oldSunPowers n).length = n.choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [oldSunPowers, ih, Nat.choose_succ_succ]; omega

def oldSunTail (n : ℕ) := (oldSunPowers (n+2)).tail

theorem oldSunPowers_head (n : ℕ) : oldSunPowers (n+2) = (1,0) :: oldSunTail n := by
  cases n with
  | zero => rfl
  | succ n => simp [oldSunPowers, oldSunTail, List.ofFn_succ]

abbrev oldSunRadialCount (n : ℕ) := (oldSunTail n).length+1

theorem oldSunRadialCount_eq (n : ℕ) : oldSunRadialCount n = (n+2)*(n+1)/2 := by
  have h := oldSunPowers_length (n+2)
  rw [oldSunPowers_head, List.length_cons] at h
  rw [oldSunRadialCount, h, Nat.choose_two_right]
  simp

def oldSunTailWeight (n : ℕ) (c : ℂ) (x : Cube (oldSunTail n).length) : ℂ :=
  c * ∏ i, ((x i).val : ℂ)^((oldSunTail n).get i).1 *
    (1-((x i).val : ℂ)^2)^((oldSunTail n).get i).2

def oldSunDensity (n : ℕ) (c : ℂ) (x : Cube (oldSunRadialCount n)) : ℂ :=
  c * ∏ i, ((x i).val : ℂ)^(((1,0)::oldSunTail n).get i).1 *
    (1-((x i).val : ℂ)^2)^(((1,0)::oldSunTail n).get i).2

theorem oldSunDensity_eq (n : ℕ) (c : ℂ) :
    oldSunDensity n c = cubeLinearWeight (oldSunTailWeight n c) := by
  funext x
  unfold oldSunDensity cubeLinearWeight oldSunTailWeight
  rw [Fin.prod_univ_succ]
  simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
    List.getElem_cons_zero, List.getElem_cons_succ, pow_one, pow_zero, mul_one, Fin.tail]
  ring

def SUNConjecture2023 (n : ℕ) (c : ℂ) : Prop :=
  FractionalConvexSupportConjecture (n+2) (sunLaurentCount n)
    (radialAlgebra (oldSunRadialCount n)) volume (oldSunDensity n c)

theorem sun_conjecture_2023_false (n : ℕ) (c : ℂ) : ¬ SUNConjecture2023 n c := by
  intro h
  have hi := fractional_conjecture_implies_integer (by omega : 1 ≤ n+2) _ _ _ h
  rw [oldSunDensity_eq] at hi
  exact cube_convexSupport_false (oldSunTail n).length
    ⟨0, by unfold sunLaurentCount; omega⟩ (oldSunTailWeight n c) hi

def pairedListWeight (L : List (ℕ × ℕ)) (x : Cube L.length) : ℂ :=
  ∏ i, ((x i).val : ℂ)^(L.get i).1 * (1-((x i).val : ℂ)^2)^(L.get i).2

theorem pairedListWeight_append (L K : List (ℕ × ℕ)) (x : Cube (L.length+K.length)) :
    pairedListWeight (L++K) (fun i => x (Fin.cast List.length_append i)) =
      pairedListWeight L (fun i => x (i.castAdd K.length)) *
      pairedListWeight K (fun i => x (i.natAdd L.length)) := by
  unfold pairedListWeight
  have he := Fin.prod_congr'
    (fun i : Fin (L.length+K.length) =>
      ((x i).val : ℂ)^((L++K).get (i.cast List.length_append.symm)).1 *
      (1-((x i).val : ℂ)^2)^((L++K).get (i.cast List.length_append.symm)).2)
    List.length_append
  simp only [Fin.cast_cast, Fin.cast_eq_self] at he
  rw [he, Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [List.get_eq_getElem]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [List.get_eq_getElem]

theorem pairedListWeight_cast {L K : List (ℕ × ℕ)} (h : L = K) (x : Cube L.length) :
    pairedListWeight L x = pairedListWeight K (fun i => x (i.cast (congrArg List.length h).symm)) := by
  subst h
  rfl

theorem oldSunDensity_source (n : ℕ) (c : ℂ) (x : Cube (oldSunRadialCount n)) :
    oldSunDensity n c x = c * pairedListWeight (oldSunPowers (n+2))
      (fun i => x (i.cast (congrArg List.length (oldSunPowers_head n)))) := by
  change c * pairedListWeight ((1,0)::oldSunTail n) x = _
  rw [pairedListWeight_cast (oldSunPowers_head n).symm]

theorem sun_conjecture_2023_contour_false (n : ℕ) (c : ℂ) :
    ¬ (∀ f : RationalLaurent (Cube (oldSunRadialCount n)) (sunLaurentCount n),
      FractionalAdmissible (n+2) (radialAlgebra (oldSunRadialCount n)) f →
      (∀ m : ℕ, 1 ≤ m → fractionalContourMoment volume (oldSunDensity n c) (f^m) = 0) →
      0 ∉ rationalNewtonPolytope f) := by
  intro h
  apply sun_conjecture_2023_false n c
  intro f hf hm
  apply h f hf
  intro m hmp
  exact (fractionalContourMoment_eq_zero_iff _ _ _).mpr (hm m hmp)
end MathieuProperty.Zwart
