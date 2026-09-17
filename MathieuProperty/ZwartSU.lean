import MathieuProperty.ZwartCube
import MathieuProperty.ClassicalSU

/-! Direct refutation of Zwart 2025, Conjecture 2.9, for every SU(N), N ≥ 2.
The recursive exponent list is the printed radial Jacobian of Corollary 2.7.
An arbitrary overall constant includes all choices of Haar/circle normalization.
This proves the failure directly; it does not need the Euler decomposition. -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace MathieuProperty.Zwart

/-- Powers in the recursively ordered SU(N) density of the 2025 addendum. -/
def sunPowers : ℕ → List ℕ
  | 0 => []
  | n+1 => List.ofFn (fun j : Fin n => 2*j.val+1) ++ sunPowers n

theorem sunPowers_length (n : ℕ) : (sunPowers n).length = n.choose 2 := by
  induction n with
  | zero => simp [sunPowers]
  | succ n ih => simp [sunPowers, ih, Nat.choose_succ_succ]

def sunTailPowers (n : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin n => 2*(j.val+1)+1) ++ sunPowers (n+1)

theorem sunPowers_head (n : ℕ) : sunPowers (n+2) = 1 :: sunTailPowers n := by
  rw [sunPowers, List.ofFn_succ, List.cons_append]
  rfl

def sunRadialCount (n : ℕ) : ℕ := (sunTailPowers n).length + 1

theorem sunRadialCount_eq (n : ℕ) : sunRadialCount n = (n+2)*(n+1)/2 := by
  have h := sunPowers_length (n+2)
  rw [sunPowers_head, List.length_cons] at h
  rw [sunRadialCount, h, Nat.choose_two_right]
  simp

def sunLaurentCount (n : ℕ) : ℕ := (n+2).choose 2 + (n+1)

theorem sunLaurentCount_eq (n : ℕ) : sunLaurentCount n = (n+2)*(n+3)/2 - 1 := by
  have h : (n+3).choose 2 = (n+2) + (n+2).choose 2 := by
    simpa using Nat.choose_succ_succ (n+2) 1
  have he : sunLaurentCount n = (n+3).choose 2 - 1 := by unfold sunLaurentCount; omega
  rw [he, Nat.choose_two_right]
  simp [Nat.mul_comm]

def sunTailWeight (n : ℕ) (c : ℂ) (x : Cube (sunTailPowers n).length) : ℂ :=
  c * ∏ i, ((x i).val : ℂ) ^ (sunTailPowers n).get i

/-- The full printed product density, with its arbitrary overall constant. -/
def sunDensity (n : ℕ) (c : ℂ) (x : Cube (sunRadialCount n)) : ℂ :=
  c * ∏ i, ((x i).val : ℂ) ^ (1 :: sunTailPowers n).get i

theorem sunDensity_eq (n : ℕ) (c : ℂ) :
    sunDensity n c = cubeLinearWeight (sunTailWeight n c) := by
  funext x
  unfold sunDensity cubeLinearWeight sunTailWeight
  change c * (∏ i : Fin ((sunTailPowers n).length + 1),
    ((x i).val : ℂ) ^ (1 :: sunTailPowers n).get i) =
    ((x (0 : Fin ((sunTailPowers n).length + 1))).val : ℂ) * (c * ∏ i : Fin (sunTailPowers n).length,
      ((x i.succ).val : ℂ) ^ (sunTailPowers n).get i)
  rw [Fin.prod_univ_succ]
  simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
    List.getElem_cons_zero, List.getElem_cons_succ, pow_one]
  ring

/-- Zwart 2025 Conjecture 2.9 in the source's exact radial and Laurent dimensions,
with the radical-polynomial coefficient algebra and actual normalized circles. -/
def SUNConjecture2025 (n : ℕ) (c : ℂ) : Prop :=
  ConvexSupportConjecture (sunLaurentCount n) (radialAlgebra (sunRadialCount n))
    volume (sunDensity n c)

theorem sun_conjecture_2025_false (n : ℕ) (c : ℂ) : ¬ SUNConjecture2025 n c := by
  unfold SUNConjecture2025
  rw [sunDensity_eq]
  exact cube_convexSupport_false (sunTailPowers n).length
    ⟨0, by unfold sunLaurentCount; omega⟩ (sunTailWeight n c)

/-- The cited implication follows as well, here by the stronger direct
refutation of its abelian premise rather than an Euler-angle proof. -/
theorem sun_reduction_2025 (n : ℕ) (c : ℂ) :
    SUNConjecture2025 n c →
      HasMathieuProperty (Matrix.specialUnitaryGroup (Fin (n+2)) ℂ) := by
  intro h
  exact (sun_conjecture_2025_false n c h).elim

end MathieuProperty.Zwart
