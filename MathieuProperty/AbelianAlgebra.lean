import MathieuProperty.HopfAlgebra
import Mathlib.Algebra.Polynomial.Laurent

/-! Exact algebra underlying Proposition 9.1. The integral and formal-spectrum
claims are tracked separately from these algebraic identities.
-/

namespace MathieuProperty.Abelian

section Ring
variable {R : Type*} [CommRing R]

def U (x w : R) : R := 2 * x * (1 - x ^ 2) * w
def V (x wi : R) : R := 2 * x * wi
def T (x : R) : R := 1 - 2 * x ^ 2
def P (x w wi : R) : R := (1 + U x w) * (V x wi - (2 + U x w) * T x ^ 2)
def Q (x w : R) : R := U x w

theorem relation (x w wi : R) (hw : w * wi = 1) :
    U x w * V x wi + T x ^ 2 = 1 := by
  dsimp [U, V, T]
  linear_combination 4 * x ^ 2 * (1 - x ^ 2) * hw

theorem defect_one (x w wi : R) (hw : w * wi = 1) :
    U x w * P x w wi = (1 + U x w) * (1 - (1 + U x w) ^ 2 * T x ^ 2) := by
  have h := relation x w wi hw
  dsimp [P]
  linear_combination (1 + U x w) * h

theorem expansion (x w wi : R) (hw : w * wi = 1) :
    P x w wi = 2 * x * wi - 2 * (6 * x ^ 4 - 6 * x ^ 2 + 1) +
      6 * x * (x ^ 2 - 1) * (2 * x ^ 2 - 1) ^ 2 * w -
      4 * x ^ 2 * (x ^ 2 - 1) ^ 2 * (2 * x ^ 2 - 1) ^ 2 * w ^ 2 := by
  dsimp [P, U, V, T]
  linear_combination 4 * x ^ 2 * (1 - x ^ 2) * hw

def A₀ (a b c d : R) : R := a * d - b * c
def U₀ (a b : R) : R := -2 * a * b
def V₀ (c d : R) : R := 2 * c * d
def T₀ (a b c d : R) : R := a * d + b * c
def entryP (a b c d : R) : R :=
  (A₀ a b c d + U₀ a b) *
    ((A₀ a b c d) ^ 2 * V₀ c d - (2 * A₀ a b c d + U₀ a b) * (T₀ a b c d) ^ 2)

theorem entry_relation (a b c d : R) :
    A₀ a b c d ^ 2 = U₀ a b * V₀ c d + T₀ a b c d ^ 2 := by
  dsimp [A₀, U₀, V₀, T₀]
  ring

theorem torus_invariance (a b c d z zi : R) (hz : z * zi = 1) :
    A₀ (a * z) (b * zi) (c * z) (d * zi) = A₀ a b c d ∧
    U₀ (a * z) (b * zi) = U₀ a b ∧ V₀ (c * z) (d * zi) = V₀ c d ∧
    T₀ (a * z) (b * zi) (c * z) (d * zi) = T₀ a b c d := by
  dsimp [A₀, U₀, V₀, T₀]
  constructor
  · linear_combination (a * d - b * c) * hz
  constructor
  · linear_combination (-2 * a * b) * hz
  constructor
  · linear_combination (2 * c * d) * hz
  · linear_combination (a * d + b * c) * hz

theorem entryP_torus_invariance (a b c d z zi : R) (hz : z * zi = 1) :
    entryP (a * z) (b * zi) (c * z) (d * zi) = entryP a b c d := by
  obtain ⟨hA, hU, hV, hT⟩ := torus_invariance a b c d z zi hz
  simp only [entryP, hA, hU, hV, hT]

end Ring

theorem square_root_free (x w : ℂ) (hw : w ≠ 0) :
    A₀ (Complex.I * w * (1 - x ^ 2)) (Complex.I * x) (Complex.I * x)
      (-Complex.I * w⁻¹) = 1 ∧
    U₀ (Complex.I * w * (1 - x ^ 2)) (Complex.I * x) = U x w ∧
    V₀ (Complex.I * x) (-Complex.I * w⁻¹) = V x w⁻¹ ∧
    T₀ (Complex.I * w * (1 - x ^ 2)) (Complex.I * x) (Complex.I * x)
      (-Complex.I * w⁻¹) = T x := by
  dsimp [A₀, U₀, V₀, T₀, U, V, T]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring_nf <;> simp [Complex.I_sq, sub_eq_add_neg]

theorem square_root_free_pair (x w : ℂ) (hw : w ≠ 0) :
    entryP (Complex.I * w * (1 - x ^ 2)) (Complex.I * x) (Complex.I * x)
      (-Complex.I * w⁻¹) = P x w w⁻¹ := by
  obtain ⟨hA, hU, hV, hT⟩ := square_root_free x w hw
  simp only [entryP, hA, hU, hV, hT, one_pow, mul_one, one_mul, P]

end MathieuProperty.Abelian
