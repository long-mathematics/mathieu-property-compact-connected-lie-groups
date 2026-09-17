import MathieuProperty

/-! Checked existence results and the remaining target for the adjoint alternative.
The AR01/AR02/AR02a examples are proofs; AR03 remains only a type-checked target. -/
open MathieuProperty
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [T2Space G]
  [ChartedSpace E G] [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G] [ConnectedSpace G]
local instance rootNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance rootFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

/- AR01: proved for the actual compact real simple Lie algebra. -/
example : LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) :=
  CompactCartanRootData.complexification_isSimple

/- AR02: this is the exact sufficient algebraic certificate at rank at least two.
The fields specify nonzero coordinates and the two standard infinitesimal
intertwining identities on the WHOLE real algebra. AdjointCoordinates constructs
actual group actions, representative functions, Haar invariance and all moments
from these data; no general root integration theorem remains in that implication. -/
example : 1 < Module.finrank ℝ (CompactCartanRootData.realCartan (E := E) (G := G)) →
  Nonempty (AdjointCoordinates.Certificate (E := E) (G := G)) :=
  AdjointRankTwo.exists_certificate

/- AR02a: proved compact-real normalization of every simple-root triple. -/
example : ∀ α : (CompactCartanRootData.simpleBase (E := E) (G := G)).support,
  ∃ (h e f : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G),
    IsSl2Triple h e f ∧
    h = (LieAlgebra.IsKilling.coroot α.val.val : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) ∧
    e ∈ LieAlgebra.rootSpace (CompactCartanRootData.complexCartan (E := E) (G := G)) α.val.val ∧
    f ∈ LieAlgebra.rootSpace (CompactCartanRootData.complexCartan (E := E) (G := G)) (-α.val.val) ∧
    ∃ X Y Z : GroupLieAlgebra 𝓘(ℝ,E) G,
      (1 : ℂ) ⊗ₜ[ℝ] X = e-f ∧
      (1 : ℂ) ⊗ₜ[ℝ] Y = Complex.I • (e+f) ∧
      (1 : ℂ) ⊗ₜ[ℝ] Z = Complex.I • h :=
  CompactCartanRootData.exists_compact_root_triple

/- AR03: exact remaining rank-one identification. The SU(2)/{±1} witness,
center calculation, and pullback implication are already proved. This target
asks only for the adjoint form, with no simply connected covering source. -/
#check (Module.finrank ℝ (CompactCartanRootData.realCartan (E := E) (G := G)) = 1 →
  Nonempty ((G ⧸ Subgroup.center G) ≃ₜ* Hopf.SU2Adjoint) : Prop)
