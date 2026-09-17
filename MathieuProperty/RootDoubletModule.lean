import MathieuProperty.RootDoubletAlgebra
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-! The cyclic highest-weight-one module.

Starting from an actual primitive vector in a finite-dimensional Lie module,
we construct its two-dimensional cyclic submodule, prove irreducibility, and
compute the defining matrices. Existence of the ambient highest-weight
representation and integration to a compact root subgroup remain separate.
-/

noncomputable section
namespace MathieuProperty
open LieModule
variable {L V : Type*} [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
  [FiniteDimensional ℂ V]
variable {h e f : L} (t : IsSl2Triple h e f) {v : V}
  (hv : t.HasPrimitiveVectorWith v (1 : ℂ))

omit [FiniteDimensional ℂ V] in
include hv in
theorem highest_weight_one_action :
    ⁅h, v⁆ = v ∧ ⁅e, v⁆ = 0 ∧ ⁅h, ⁅f, v⁆⁆ = -⁅f, v⁆ ∧ ⁅e, ⁅f, v⁆⁆ = v := by
  refine ⟨by simpa using hv.lie_h, hv.lie_e, ?_, ?_⟩
  · have hh := hv.lie_h_pow_toEnd_f 1
    norm_num at hh
    exact hh
  · simpa using hv.lie_e_pow_succ_toEnd_f 0

def sl2DoubletVectors (f : L) (v : V) : Fin 2 → V := ![v, ⁅f, v⁆]

include hv in
theorem sl2Doublet_linearIndependent : LinearIndependent ℂ (sl2DoubletVectors f v) := by
  rw [linearIndependent_fin2]
  refine ⟨(highest_weight_one_lowering t hv).1, ?_⟩
  intro c hc
  have hh := congrArg (fun w : V => ⁅f, w⁆) hc
  change ⁅f, c • ⁅f, v⁆⁆ = ⁅f, v⁆ at hh
  rw [lie_smul, (highest_weight_one_lowering t hv).2, smul_zero] at hh
  exact (highest_weight_one_lowering t hv).1 hh.symm

include hv in
theorem sl2Doublet_action (α β γ x y : ℂ) :
    ⁅α • e + β • f + γ • h, x • v + y • ⁅f, v⁆⁆ =
      (γ*x + α*y) • v + (β*x - γ*y) • ⁅f, v⁆ := by
  obtain ⟨hh, he, hhf, hef⟩ := highest_weight_one_action t hv
  simp only [add_lie, smul_lie, lie_add, lie_smul, hh, he, hhf, hef,
    (highest_weight_one_lowering t hv).2, smul_zero, add_zero, zero_add]
  module

def sl2DoubletSpace : Submodule ℂ V := Submodule.span ℂ (Set.range (sl2DoubletVectors f v))

omit [LieAlgebra ℂ L] [LieModule ℂ L V] [FiniteDimensional ℂ V] in
theorem mem_sl2DoubletSpace (w : V) : w ∈ sl2DoubletSpace (f := f) (v := v) ↔
    ∃ x y : ℂ, x • v + y • ⁅f, v⁆ = w := by
  have hr : Set.range (sl2DoubletVectors f v) = {v, ⁅f, v⁆} := by
    ext w
    simp [sl2DoubletVectors, or_comm]
  rw [sl2DoubletSpace, hr, Submodule.mem_span_pair]

def sl2DoubletBasis : Module.Basis (Fin 2) ℂ (sl2DoubletSpace (f := f) (v := v)) :=
  Module.Basis.span (sl2Doublet_linearIndependent t hv)

include hv in
theorem sl2Doublet_finrank : Module.finrank ℂ (sl2DoubletSpace (f := f) (v := v)) = 2 := by
  rw [Module.finrank_eq_card_basis (sl2DoubletBasis t hv)]
  simp

def sl2DoubletSubmodule : LieSubmodule ℂ (t.toLieSubalgebra ℂ) V where
  __ := sl2DoubletSpace (f := f) (v := v)
  lie_mem {l w} hw := by
    obtain ⟨α, β, γ, hl⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp l.property
    obtain ⟨x, y, rfl⟩ := (mem_sl2DoubletSpace _).mp hw
    change ⁅(l : L), x • v + y • ⁅f, v⁆⁆ ∈ sl2DoubletSpace
    rw [hl, t.lie_e_f, sl2Doublet_action t hv]
    exact (mem_sl2DoubletSpace _).mpr ⟨_, _, rfl⟩

theorem sl2Doublet_cyclic : LieSubmodule.lieSpan ℂ (t.toLieSubalgebra ℂ) {v} = sl2DoubletSubmodule t hv := by
  apply le_antisymm
  · rw [LieSubmodule.lieSpan_le]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (mem_sl2DoubletSpace v).mpr ⟨1, 0, by simp⟩
  · change Submodule.span ℂ (Set.range (sl2DoubletVectors f v)) ≤
      (LieSubmodule.lieSpan ℂ (t.toLieSubalgebra ℂ) {v}).toSubmodule
    apply Submodule.span_le.mpr
    rintro w ⟨i, rfl⟩
    have hv' : v ∈ LieSubmodule.lieSpan ℂ (t.toLieSubalgebra ℂ) {v} :=
      LieSubmodule.subset_lieSpan (by simp)
    fin_cases i
    · exact hv'
    · have hf : f ∈ t.toLieSubalgebra ℂ := by
        apply IsSl2Triple.mem_toLieSubalgebra_iff.mpr
        exact ⟨0, 1, 0, by simp⟩
      exact (LieSubmodule.lieSpan ℂ (t.toLieSubalgebra ℂ) {v}).lie_mem (x := ⟨f, hf⟩) hv'


theorem sl2Doublet_irreducible (N : LieSubmodule ℂ (t.toLieSubalgebra ℂ) V)
    (hNW : N ≤ sl2DoubletSubmodule t hv) : N = ⊥ ∨ N = sl2DoubletSubmodule t hv := by
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  rw [LieSubmodule.eq_bot_iff] at hN
  push Not at hN
  obtain ⟨w, hw, hwn⟩ := hN
  obtain ⟨x, y, hxy⟩ := (mem_sl2DoubletSpace w).mp (hNW hw)
  have hvN : v ∈ N := by
    by_cases hy : y = 0
    · have hx : x ≠ 0 := by
        intro hx
        apply hwn
        rw [← hxy, hx, hy]
        simp
      rw [← hxy, hy, zero_smul, add_zero] at hw
      exact (N.toSubmodule.smul_mem_iff hx).mp hw
    · have he : e ∈ t.toLieSubalgebra ℂ := by
        apply IsSl2Triple.mem_toLieSubalgebra_iff.mpr
        exact ⟨1, 0, 0, by simp⟩
      have hew := N.lie_mem (x := ⟨e, he⟩) hw
      change ⁅e, w⁆ ∈ N at hew
      rw [← hxy, lie_add, lie_smul, lie_smul, hv.lie_e,
        (highest_weight_one_action t hv).2.2.2, smul_zero, zero_add] at hew
      exact (N.toSubmodule.smul_mem_iff hy).mp hew
  apply le_antisymm hNW
  rw [← sl2Doublet_cyclic t hv, LieSubmodule.lieSpan_le]
  exact Set.singleton_subset_iff.mpr hvN


def sl2Element (α β γ : ℂ) : t.toLieSubalgebra ℂ :=
  ⟨α • e + β • f + γ • h, IsSl2Triple.mem_toLieSubalgebra_iff.mpr
    ⟨α, β, γ, by rw [t.lie_e_f]⟩⟩

/-- The exact standard two-dimensional sl₂ matrices in the cyclic basis (v,Fv). -/
theorem sl2Doublet_matrix (α β γ : ℂ) :
    LinearMap.toMatrix (sl2DoubletBasis t hv) (sl2DoubletBasis t hv)
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) (sl2DoubletSubmodule t hv) (sl2Element t α β γ)) =
        !![γ, α; β, -γ] := by
  let b : Module.Basis (Fin 2) ℂ (sl2DoubletSubmodule t hv) := sl2DoubletBasis t hv
  let A := LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) (sl2DoubletSubmodule t hv) (sl2Element t α β γ)
  have hb0 : (b 0 : V) = v := Module.Basis.coe_span_apply _ _
  have hb1 : (b 1 : V) = ⁅f, v⁆ := Module.Basis.coe_span_apply _ _
  have h0 : A (b 0) = γ • b 0 + β • b 1 := by
    apply Subtype.ext
    change ⁅α • e + β • f + γ • h, (b 0 : V)⁆ = γ • (b 0 : V) + β • (b 1 : V)
    rw [hb0, hb1]
    simpa using sl2Doublet_action t hv α β γ 1 0
  have h1 : A (b 1) = α • b 0 + (-γ) • b 1 := by
    apply Subtype.ext
    change ⁅α • e + β • f + γ • h, (b 1 : V)⁆ = α • (b 0 : V) + (-γ) • (b 1 : V)
    rw [hb0, hb1]
    simpa using sl2Doublet_action t hv α β γ 0 1
  change LinearMap.toMatrix b b A = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, h0, h1]

end MathieuProperty
