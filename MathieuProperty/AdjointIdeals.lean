import MathieuProperty.CompactLieStructure
import MathieuProperty.LieIdealOrbit
/-! The adjoint action of a compact connected Lie group preserves each simple
factor of the compact Lie algebra decomposition. We first restrict to the
semisimple complement, use its finite family of atomic ideals, then lift the
restricted action to the actual ambient simple ideals. -/

noncomputable section
namespace MathieuProperty
namespace CompactAdjoint
open scoped Manifold ContDiff
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
local instance adjointIdealsSmoothness : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
local instance adjointIdealsTangentNorm : NormedAddCommGroup (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance adjointIdealsTangentNormedSpace : NormedSpace ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedSpace ℝ E)
local instance adjointIdealsTangentFinite : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)

local instance adjointIdealsSemisimpleNorm : NormedAddCommGroup (semisimpleIdeal (E := E) (G := G)) :=
  inferInstanceAs (NormedAddCommGroup (semisimpleIdeal (E := E) (G := G)).toSubmodule)
local instance adjointIdealsSemisimpleNormedSpace : NormedSpace ℝ (semisimpleIdeal (E := E) (G := G)) :=
  inferInstanceAs (NormedSpace ℝ (semisimpleIdeal (E := E) (G := G)).toSubmodule)

local instance adjointIdealsSemisimpleTopologicalAdd : IsTopologicalAddGroup (semisimpleIdeal (E := E) (G := G)) :=
  inferInstanceAs (IsTopologicalAddGroup (semisimpleIdeal (E := E) (G := G)).toSubmodule)
local instance adjointIdealsSemisimpleContinuousSMul : ContinuousSMul ℝ (semisimpleIdeal (E := E) (G := G)) :=
  inferInstanceAs (ContinuousSMul ℝ (semisimpleIdeal (E := E) (G := G)).toSubmodule)

theorem adjoint_mem_semisimpleIdeal (g : G) {v : GroupLieAlgebra 𝓘(ℝ,E) G}
    (hv : v ∈ semisimpleIdeal (E := E) (G := G)) :
    adjointLieEquiv g v ∈ semisimpleIdeal (E := E) (G := G) := by
  apply (LieAlgebra.InvariantForm.mem_orthogonal _ invariantForm_lieInvariant _ _).mpr
  intro z hz
  let e := adjointLieEquiv (E := E) g
  have hw := LieIdealOrbit.equiv_mem_center e.symm hz
  have hb := invariantForm_adjoint g (e.symm z) v
  change invariantForm (e (e.symm z)) (e v) = invariantForm (e.symm z) v at hb
  rw [e.apply_symm_apply] at hb
  exact hb.trans ((LieAlgebra.InvariantForm.mem_orthogonal _ invariantForm_lieInvariant _ _).mp hv (e.symm z) hw)

def semisimpleAdjointEquiv (g : G) :
    semisimpleIdeal (E := E) (G := G) ≃ₗ⁅ℝ⁆ semisimpleIdeal (E := E) (G := G) where
  toFun v := ⟨adjointLieEquiv g v.val, adjoint_mem_semisimpleIdeal g v.property⟩
  invFun v := ⟨(adjointLieEquiv g).symm v.val, adjoint_mem_semisimpleIdeal g⁻¹ v.property⟩
  left_inv v := Subtype.ext ((adjointLieEquiv g).left_inv v.val)
  right_inv v := Subtype.ext ((adjointLieEquiv g).right_inv v.val)
  map_add' v w := Subtype.ext ((adjointLieEquiv g).map_add v.val w.val)
  map_smul' a v := Subtype.ext ((adjointLieEquiv g).map_smul a v.val)
  map_lie' {v w} := Subtype.ext ((adjointLieEquiv g).map_lie v.val w.val)
theorem semisimpleAdjointEquiv_one : semisimpleAdjointEquiv (E := E) (1 : G) = LieEquiv.refl := by
  apply DFunLike.ext
  intro v
  apply Subtype.ext
  change adjointLinear (E := E) (1 : G) v.val = v.val
  rw [adjointLinear_one]
  rfl

theorem semisimpleAdjointEquiv_continuous (v : semisimpleIdeal (E := E) (G := G)) :
    Continuous (fun g : G => semisimpleAdjointEquiv (E := E) g v) := by
  exact (adjointRepresentation_continuous v.val).subtype_mk _

theorem adjoint_preserves_atom [PreconnectedSpace G]
    (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I) (g : G) :
    LieIdealOrbit.idealOrderIso (semisimpleAdjointEquiv (E := E) g) I = I := by
  have h := LieIdealOrbit.atom_image_eq (semisimpleAdjointEquiv (E := E) (G := G))
    semisimpleAdjointEquiv_continuous (semisimpleIdeal_finite_simple_factors (E := E) (G := G)).1 I hI g 1
  rw [semisimpleAdjointEquiv_one] at h
  exact h

/-- Each ambient simple factor from the compact decomposition is Ad-invariant. -/
theorem adjoint_preserves_simple_ideal [PreconnectedSpace G]
    (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I) (g : G)
    {v : GroupLieAlgebra 𝓘(ℝ,E) G}
    (hv : v ∈ CompactLieForm.liftCentralIdeal (semisimpleIdeal (E := E) (G := G))
      semisimpleIdeal_isCompl I) :
    adjointLinear g v ∈ CompactLieForm.liftCentralIdeal (semisimpleIdeal (E := E) (G := G))
      semisimpleIdeal_isCompl I := by
  obtain ⟨w,hw,rfl⟩ := hv
  refine ⟨semisimpleAdjointEquiv g w, ?_, rfl⟩
  rw [← adjoint_preserves_atom I hI g]
  exact (LieIdealOrbit.mem_idealOrderIso _ _ _).mpr hw
/-- The actual restricted adjoint representation on an ambient simple factor. -/
def simpleAdjointRepresentation [PreconnectedSpace G]
    (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I) :
    Representation ℝ G (CompactLieForm.liftCentralIdeal (semisimpleIdeal (E := E) (G := G))
      semisimpleIdeal_isCompl I) where
  toFun g :=
    { toFun := fun v => ⟨adjointLinear g v.val, adjoint_preserves_simple_ideal I hI g v.property⟩
      map_add' := fun v w => Subtype.ext ((adjointLinear g).map_add v.val w.val)
      map_smul' := fun a v => Subtype.ext ((adjointLinear g).map_smul a v.val) }
  map_one' := by
    ext v
    exact congrArg (fun f => f v.val) (adjointLinear_one (E := E) (G := G))
  map_mul' g h := by
    ext v
    exact congrArg (fun f => f v.val) (adjointLinear_mul (E := E) g h)

theorem simpleAdjointRepresentation_continuous [PreconnectedSpace G]
    (I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) (hI : IsAtom I)
    (v : CompactLieForm.liftCentralIdeal (semisimpleIdeal (E := E) (G := G))
      semisimpleIdeal_isCompl I) :
    Continuous (fun g : G => simpleAdjointRepresentation I hI g v) := by
  exact (adjointRepresentation_continuous v.val).subtype_mk _
end CompactAdjoint
end MathieuProperty
