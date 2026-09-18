import MathieuProperty.CompactComplexSimple
import MathieuProperty.CompatibleRootData

/-! Compact-real root triples for the actual compatible Cartan of a compact
simple Lie group. The positive invariant form is constructed from Haar measure;
there is no supplied compact-real-form or root-integration hypothesis. -/
noncomputable section
open scoped Manifold ContDiff TensorProduct
namespace MathieuProperty.CompactCartanRootData
open LieAlgebra LieAlgebra.IsKilling
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G]
local instance normalizationNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance normalizationFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]

/-- The exact complex-simplicity target AR01 for the actual compact real
simple Lie algebra, proved using its constructed positive invariant form. -/
theorem complexification_isSimple :
    LieAlgebra.IsSimple ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  exact CompactRootReality.complexification_isSimple
    (CompactAdjoint.invariantForm (E := E) (G := G))
    CompactAdjoint.invariantForm_symmetric
    (fun x hx => CompactAdjoint.invariantForm_positive hx)
    CompactAdjoint.invariantForm_lieInvariant (realCartan (E := E) (G := G))

/-- Cartan rank is unchanged by the compatible complexification. -/
theorem complexCartan_finrank :
    Module.finrank ℂ (complexCartan (E := E) (G := G)) =
      Module.finrank ℝ (realCartan (E := E) (G := G)) :=
  ComplexParts.subalgebra_finrank _

/-- The exact compact-real root normalization target AR02a for every simple
root of the already constructed compatible maximal-torus/Cartan root data. -/
theorem exists_compact_root_triple
    (α : (simpleBase (E := E) (G := G)).support) :
    ∃ (h e f : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G), IsSl2Triple h e f ∧
      h = (coroot α.val.val : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) ∧
      e ∈ rootSpace (complexCartan (E := E) (G := G)) α.val.val ∧
      f ∈ rootSpace (complexCartan (E := E) (G := G)) (-α.val.val) ∧
      ∃ X Y Z : GroupLieAlgebra 𝓘(ℝ,E) G,
        (1 : ℂ) ⊗ₜ[ℝ] X = e-f ∧
        (1 : ℂ) ⊗ₜ[ℝ] Y = Complex.I • (e+f) ∧
        (1 : ℂ) ⊗ₜ[ℝ] Z = Complex.I • h := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  exact CompactRootReality.exists_compact_root_triple
    (CompactAdjoint.invariantForm (E := E) (G := G))
    CompactAdjoint.invariantForm_symmetric
    (fun x hx => CompactAdjoint.invariantForm_positive hx)
    CompactAdjoint.invariantForm_lieInvariant (realCartan (E := E) (G := G))
    α.val.val ((complexCartan (E := E) (G := G)).isNonZero_coe_root α.val)

end MathieuProperty.CompactCartanRootData
