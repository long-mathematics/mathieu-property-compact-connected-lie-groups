import MathieuProperty.AdjointOneParameter
import MathieuProperty.SU2Generators
import MathieuProperty.RealRepresentative

/-! A precise algebraic certificate suffices for the adjoint-only route.
The certificate is an explicit hypothesis, not an existence assertion.
Actual one-parameter subgroups, Haar invariance, representative coefficients,
and the radial witness are constructed from it. -/
noncomputable section
open scoped Manifold ContDiff
open MeasureTheory
namespace MathieuProperty.AdjointCoordinates
open Hopf
set_option backward.isDefEq.respectTransparency false
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G]
local instance smoothness : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
abbrev Algebra := GroupLieAlgebra 𝓘(ℝ,E) G

/-- The remaining compact-real coordinate data. Only two generators are needed.
The identities hold on the whole algebra, not just on the root doublet; this
ensures that projection of an arbitrary adjoint orbit intertwines the action. -/
structure Certificate where
  projection : E →L[ℝ] Space
  phase : Algebra (E := E) (G := G)
  rotation : Algebra (E := E) (G := G)
  vector : Algebra (E := E) (G := G)
  nonzero : projection vector ≠ 0
  phase_lie : ∀ w : Algebra (E := E) (G := G),
    projection (⁅phase,w⁆ : Algebra (E := E) (G := G)) = phaseGenerator (projection w)
  rotation_lie : ∀ w : Algebra (E := E) (G := G),
    projection (⁅rotation,w⁆ : Algebra (E := E) (G := G)) = rotationGenerator (projection w)

def coordinates (c : Certificate (E := E) (G := G)) (g : G) : Space :=
  c.projection (ConnectedLie.adjoint (E := E) (G := G) g c.vector)

omit [FiniteDimensional ℝ E] [T2Space G] in
theorem coordinates_continuous (c : Certificate (E := E) (G := G)) :
    Continuous (coordinates c) :=
  c.projection.continuous.comp (CompactAdjoint.adjointRepresentation_continuous c.vector)

theorem phase_lift (c : Certificate (E := E) (G := G)) (t : ℝ) (g : G) :
    coordinates c (LieOneParameter.curve c.phase t * g) = diagonalPhase t • coordinates c g := by
  have h := AdjointOneParameter.coordinate_curve_eq c.projection phaseGenerator c.phase
    (CompactAdjoint.adjointRepresentation g c.vector) c.phase_lie
    (fun s => diagonalPhase s • coordinates c g)
    (diagonalPhase_action_deriv (coordinates c g)) (diagonalPhase_zero_action _)
  have ht := congrFun h t
  change c.projection (CompactAdjoint.adjointLinear (LieOneParameter.curve c.phase t * g) c.vector) = _
  rw [CompactAdjoint.adjointLinear_mul]
  exact ht

theorem rotation_lift (c : Certificate (E := E) (G := G)) (t : ℝ) (g : G) :
    coordinates c (LieOneParameter.curve c.rotation t * g) = realRotation t • coordinates c g := by
  have h := AdjointOneParameter.coordinate_curve_eq c.projection rotationGenerator c.rotation
    (CompactAdjoint.adjointRepresentation g c.vector) c.rotation_lie
    (fun s => realRotation s • coordinates c g)
    (realRotation_action_deriv (coordinates c g)) (realRotation_zero_action _)
  have ht := congrFun h t
  change c.projection (CompactAdjoint.adjointLinear (LieOneParameter.curve c.rotation t * g) c.vector) = _
  rw [CompactAdjoint.adjointLinear_mul]
  exact ht

omit [T2Space G] in
theorem coordinate_mem (c : Certificate (E := E) (G := G)) (l : Space →L[ℝ] ℂ) :
    (⟨fun g => l (coordinates c g), l.continuous.comp (coordinates_continuous c)⟩ : C(G,ℂ)) ∈
      representativeFunctions (G := G) :=
  real_representation_coefficient_mem
    (show Representation ℝ G E from CompactAdjoint.adjointRepresentation (E := E) (G := G))
    (CompactAdjoint.adjointRepresentation_continuous (E := E) (G := G))
    (l.comp c.projection) c.vector

def first (c : Certificate (E := E) (G := G)) : representativeFunctions (G := G) :=
  ⟨⟨fun g => (coordinates c g).1, (coordinates_continuous c).fst⟩,
    coordinate_mem c (ContinuousLinearMap.fst ℝ ℂ ℂ)⟩
def second (c : Certificate (E := E) (G := G)) : representativeFunctions (G := G) :=
  ⟨⟨fun g => (coordinates c g).2, (coordinates_continuous c).snd⟩,
    coordinate_mem c (ContinuousLinearMap.snd ℝ ℂ ℂ)⟩

variable [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem pushforward_invariant (c : Certificate (E := E) (G := G)) :
    SMulInvariantMeasure SU2 Space (Measure.map (coordinates c) (normalizedHaar G)) :=
  haar_pushforward_invariant_of_phase_rotation _ (coordinates_continuous c)
    (fun t => ⟨LieOneParameter.curve c.phase t, phase_lift c t⟩)
    (fun t => ⟨LieOneParameter.curve c.rotation t, rotation_lift c t⟩)

omit [FiniteDimensional ℝ E] [T2Space G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem coordinates_one_ne_zero (c : Certificate (E := E) (G := G)) : coordinates c 1 ≠ 0 := by
  change c.projection (CompactAdjoint.adjointLinear (1 : G) c.vector) ≠ 0
  rw [CompactAdjoint.adjointLinear_one]
  exact c.nonzero

/-- The full pure and Pascal-row marked formulas for the actual adjoint coordinates. -/
theorem marker_tower (c : Certificate (E := E) (G := G)) :
    (∀ m : ℕ, 1 ≤ m → representativeIntegral G
      (representativeP (first c) (second c) ^ m) = 0) ∧
    (∀ m s : ℕ, 1 ≤ m → 1 ≤ s →
      representativeIntegral G (representativeQ (first c) (second c) ^ s *
        representativeP (first c) (second c) ^ m) =
        (momentConstant m : ℂ) * ((m-1).choose (s-1) : ℂ) *
          representativeIntegral G (representativeA (first c) (second c) ^ (4*m+s))) := by
  let : SMulInvariantMeasure SU2 Space (Measure.map
      (fun g => ((first c).val g, (second c).val g)) (normalizedHaar G)) := by
    change SMulInvariantMeasure SU2 Space (Measure.map (coordinates c) (normalizedHaar G))
    exact pushforward_invariant c
  exact representative_invariant_tower (first c) (second c)

theorem marked_positive (c : Certificate (E := E) (G := G)) (m s : ℕ)
    (hm : 1 ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∃ r : ℝ, 0 < r ∧ representativeIntegral G
      (representativeQ (first c) (second c) ^ s * representativeP (first c) (second c) ^ m) =
        (r : ℂ) := by
  let : SMulInvariantMeasure SU2 Space (Measure.map
      (fun g => ((first c).val g, (second c).val g)) (normalizedHaar G)) := by
    change SMulInvariantMeasure SU2 Space (Measure.map (coordinates c) (normalizedHaar G))
    exact pushforward_invariant c
  exact representative_invariant_positive (first c) (second c) (coordinates_one_ne_zero c) m s hm hs hsm

theorem marked_zero (c : Certificate (E := E) (G := G)) (m s : ℕ)
    (hm : 1 ≤ m) (hsm : m < s) :
    representativeIntegral G (representativeQ (first c) (second c) ^ s *
      representativeP (first c) (second c) ^ m) = 0 := by
  rw [(marker_tower c).2 m s hm (by omega), Nat.choose_eq_zero_of_lt (by omega)]
  simp

omit [T2Space G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem radial_nonnegative (c : Certificate (E := E) (G := G)) (g : G) :
    (representativeA (first c) (second c)).val g = (a (coordinates c g) : ℂ) ∧
      0 ≤ a (coordinates c g) :=
  ⟨representativeA_apply _ _ _, a_nonneg _⟩

theorem radial_nonzero (c : Certificate (E := E) (G := G)) :
    representativeA (first c) (second c) ≠ 0 := by
  intro h
  have he := congrArg (fun f : representativeFunctions (G := G) => f.val 1) h
  change (representativeA (first c) (second c)).val 1 = 0 at he
  rw [(radial_nonnegative c 1).1] at he
  exact coordinates_one_ne_zero c ((a_eq_zero_iff _).mp (Complex.ofReal_eq_zero.mp he))

/-- Conditional only on the explicitly displayed algebraic certificate; no
highest-weight representation, root integration, or covering hypothesis occurs. -/
theorem not_mathieu (c : Certificate (E := E) (G := G)) : ¬ HasMathieuProperty G := by
  let : SMulInvariantMeasure SU2 Space (Measure.map
      (fun g => ((first c).val g, (second c).val g)) (normalizedHaar G)) := by
    change SMulInvariantMeasure SU2 Space (Measure.map (coordinates c) (normalizedHaar G))
    exact pushforward_invariant c
  exact representative_invariant_not_mathieu (first c) (second c) (coordinates_one_ne_zero c)

end MathieuProperty.AdjointCoordinates
