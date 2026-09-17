import MathieuProperty.ComplexCartan
import MathieuProperty.CompactCartanTorus

/-! Complex root data built from the same real Cartan used in the compact torus
construction. The complex Cartan is its scalar extension, with real membership
and the fundamental weight/coroot normalization recorded explicitly. -/

noncomputable section
open scoped TensorProduct
namespace MathieuProperty.CompatibleRootData
open LieAlgebra LieAlgebra.IsKilling
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L] [IsKilling ℝ L]
variable (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] [IsLieAbelian H]

abbrev cartan := ComplexParts.subalgebra H

def simpleBase : (rootSystem (cartan H)).Base :=
  Classical.choice (rootSystem (cartan H)).nonempty_base

variable [Nontrivial L]

instance simpleBase_nonempty : Nonempty (simpleBase H).support :=
  (simpleBase H).toCoweightBasis.index_nonempty

def simpleRoot : (simpleBase H).support := Classical.choice inferInstance

def fundamentalWeight : Module.Dual ℂ (cartan H) :=
  FundamentalRootWeight.fundamentalWeight (simpleBase H) (simpleRoot H)

theorem fundamentalWeight_pairing :
    fundamentalWeight H (coroot (simpleRoot H).val.val) = 1 :=
  FundamentalRootWeight.fundamentalWeight_coroot_self _ _

theorem exists_root_triple : ∃ (h e f : ℂ ⊗[ℝ] L), IsSl2Triple h e f ∧
    h = (coroot (simpleRoot H).val.val : ℂ ⊗[ℝ] L) ∧
    e ∈ rootSpace (cartan H) (simpleRoot H).val.val ∧
    f ∈ rootSpace (cartan H) (-(simpleRoot H).val.val) := by
  have hα := (cartan H).isNonZero_coe_root (simpleRoot H).val
  obtain ⟨h,e,f,t,he,hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  exact ⟨h,e,f,t,t.h_eq_coroot hα he hf,he,hf⟩

end MathieuProperty.CompatibleRootData

namespace MathieuProperty.CompactCartanRootData
open scoped Manifold ContDiff
open LieAlgebra
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [CompactSpace G]
local instance rootNormed : NormedRealLieAlgebra (GroupLieAlgebra 𝓘(ℝ,E) G) := groupLieAlgebraNormed
local instance rootFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)
variable [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)]
local instance rootNontrivial : Nontrivial (GroupLieAlgebra 𝓘(ℝ,E) G) := IsSimple.nontrivial ℝ _

abbrev realCartan := CompactCartanTorus.Cartan (E := E) (G := G)
abbrev complexCartan := CompatibleRootData.cartan (realCartan (E := E) (G := G))

def simpleBase := CompatibleRootData.simpleBase (realCartan (E := E) (G := G))
def simpleRoot := CompatibleRootData.simpleRoot (realCartan (E := E) (G := G))
def fundamentalWeight := CompatibleRootData.fundamentalWeight (realCartan (E := E) (G := G))

omit [CompactSpace G] [LieAlgebra.IsSimple ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)] in
theorem real_mem_complexCartan (x : GroupLieAlgebra 𝓘(ℝ,E) G) :
    (1 : ℂ) ⊗ₜ[ℝ] x ∈ complexCartan (E := E) (G := G) ↔ x ∈ realCartan (E := E) (G := G) :=
  ComplexParts.real_mem_subalgebra _ x

theorem fundamentalWeight_pairing :
    fundamentalWeight (E := E) (G := G) (LieAlgebra.IsKilling.coroot (simpleRoot (E := E) (G := G)).val.val) = 1 :=
  CompatibleRootData.fundamentalWeight_pairing _

theorem exists_root_triple : ∃ (h e f : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G), IsSl2Triple h e f ∧
    h = (LieAlgebra.IsKilling.coroot (simpleRoot (E := E) (G := G)).val.val : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,E) G) ∧
    e ∈ rootSpace (complexCartan (E := E) (G := G)) (simpleRoot (E := E) (G := G)).val.val ∧
    f ∈ rootSpace (complexCartan (E := E) (G := G)) (-(simpleRoot (E := E) (G := G)).val.val) :=
  CompatibleRootData.exists_root_triple _

end MathieuProperty.CompactCartanRootData
