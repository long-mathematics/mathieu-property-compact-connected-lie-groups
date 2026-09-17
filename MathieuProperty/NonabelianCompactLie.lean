import MathieuProperty.ConnectedLie
import MathieuProperty.CompactLieStructure
/-! A nonabelian compact connected real Lie group has a simple Lie ideal.

Connectedness rules out an abelian Lie algebra. The compact decomposition
therefore has a nonzero semisimple complement, hence at least one atomic
simple factor. Its inclusion into the ambient Lie algebra is an actual ideal. -/

noncomputable section
open scoped Manifold ContDiff
namespace MathieuProperty
namespace CompactLieForm
variable {R L M : Type*} [CommRing R] [LieRing L] [LieRing M]
  [LieAlgebra R L] [LieAlgebra R M]
/-- Lie simplicity transports along a Lie algebra equivalence. -/
theorem isSimple_of_equiv (e : L ≃ₗ⁅R⁆ M) [LieAlgebra.IsSimple R L] : LieAlgebra.IsSimple R M where
  eq_bot_or_eq_top J := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (J.comap e.toLieHom) with h | h
    · left
      apply (LieSubmodule.eq_bot_iff _).mpr
      intro y hy
      obtain ⟨x,rfl⟩ := e.surjective y
      have hx : x ∈ J.comap e.toLieHom := hy
      rw [h] at hx
      have hx₀ : x = 0 := hx
      simp [hx₀]
    · right
      apply top_unique
      intro y _
      obtain ⟨x,rfl⟩ := e.surjective y
      have hx : x ∈ J.comap e.toLieHom := by rw [h]; trivial
      exact hx
  non_abelian h := LieAlgebra.IsSimple.non_abelian (R := R) (L := L)
    ((lie_abelian_iff_equiv_lie_abelian e).mpr h)
end CompactLieForm
namespace CompactAdjoint
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ,E) ∞ G] [IsTopologicalGroup G] [CompactSpace G] [PreconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
local instance : LieGroup 𝓘(ℝ,E) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by simp)
local instance : NormedAddCommGroup (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance : NormedSpace ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (NormedSpace ℝ E)
local instance : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ,E) G) :=
  inferInstanceAs (FiniteDimensional ℝ E)

theorem semisimpleIdeal_ne_bot (hn : ¬ ∀ g h : G, g*h = h*g) :
    semisimpleIdeal (E := E) (G := G) ≠ ⊥ := by
  intro hK
  have hc := (semisimpleIdeal_isCompl (E := E) (G := G)).sup_eq_top
  rw [hK, sup_bot_eq] at hc
  have :=  (LieAlgebra.isLieAbelian_iff_center_eq_top ℝ (GroupLieAlgebra 𝓘(ℝ,E) G)).mpr hc
  exact hn (ConnectedLie.mul_comm_of_lie_abelian (E := E))

theorem exists_simple_factor (hn : ¬ ∀ g h : G, g*h = h*g) :
    ∃ I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G)), IsAtom I ∧ LieAlgebra.IsSimple ℝ I := by
  classical
  obtain ⟨_,hsup,_,hsimple⟩ := semisimpleIdeal_finite_simple_factors (E := E) (G := G)
  have ha : ∃ I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G)), IsAtom I := by
    by_contra h
    have he : {I : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G)) | IsAtom I} = ∅ := by
      ext I
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hI => h ⟨I,hI⟩
    rw [he, sSup_empty] at hsup
    apply semisimpleIdeal_ne_bot (E := E) hn
    apply (LieSubmodule.eq_bot_iff _).mpr
    intro x hx
    have hz : (⟨x,hx⟩ : semisimpleIdeal (E := E) (G := G)) ∈
        (⊥ : LieIdeal ℝ (semisimpleIdeal (E := E) (G := G))) := by rw [hsup]; trivial
    have hz₀ : (⟨x,hx⟩ : semisimpleIdeal (E := E) (G := G)) = 0 := hz
    exact congrArg Subtype.val hz₀
  obtain ⟨I,hI⟩ := ha
  exact ⟨I,hI,hsimple I hI⟩

omit [IsTopologicalGroup G] in
/-- The nonzero simple factor required by the manuscript's adjoint quotient construction. -/
theorem nonabelian_simple_ideal (hn : ¬ ∀ g h : G, g*h = h*g) :
    ∃ J : LieIdeal ℝ (GroupLieAlgebra 𝓘(ℝ,E) G), LieAlgebra.IsSimple ℝ J := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E) ∞
  obtain ⟨I,hI,hS⟩ := exists_simple_factor (E := E) hn
  let := hS
  exact ⟨CompactLieForm.liftCentralIdeal (semisimpleIdeal (E := E) (G := G))
    semisimpleIdeal_isCompl I, CompactLieForm.isSimple_of_equiv (simpleFactorAmbientEquiv I)⟩
end CompactAdjoint
end MathieuProperty
