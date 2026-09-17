import MathieuProperty.ClassicalSphereGeometry
import Mathlib.Topology.Algebra.Star.Unitary

/-! Compactness and the topological-group structure of the actual special unitary matrix group. -/

noncomputable section
namespace MathieuProperty

instance specialUnitaryTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin n) ℂ) where
  continuous_mul := continuous_induced_rng.mpr
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

open scoped Matrix.Norms.Elementwise in
instance specialUnitaryCompactSpace (n : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin n) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hc : IsClosed (Matrix.specialUnitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isClosed_unitary.inter (isClosed_eq continuous_id.matrix_det continuous_const)
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨hc, (Metric.isBounded_closedBall (x := (0 : Matrix (Fin n) (Fin n) ℂ)) (r := 1)).subset ?_⟩
  intro M hM
  change dist M 0 ≤ (1 : ℝ)
  rw [dist_zero_right]
  exact entrywise_sup_norm_bound_of_unitary hM.1

end MathieuProperty
