import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Compact

/-! Normalized Haar measure and the integral identity in Lemma 2.3.
The representative-function correspondence is developed separately.
-/

noncomputable section

open MeasureTheory TopologicalSpace

namespace MathieuProperty

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized on the entire compact group, not an arbitrary compact set. -/
def normalizedHaar : Measure G :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)

instance : (normalizedHaar G).IsHaarMeasure := by
  unfold normalizedHaar
  infer_instance

instance : IsProbabilityMeasure (normalizedHaar G) where
  measure_univ := Measure.haarMeasure_self

/-- Normalized Haar integration on continuous complex-valued functions. -/
def haarIntegral (f : C(G, ℂ)) : ℂ := ∫ g, f g ∂normalizedHaar G

variable {G} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]

theorem map_normalizedHaar (π : G →* H) (hπ : Continuous π) (hs : Function.Surjective π) :
    Measure.map π (normalizedHaar G) = normalizedHaar H :=
  (π.measurePreserving hπ hs (by simp)).map_eq

/-- The exact normalized integral pullback identity for continuous functions. -/
theorem haar_pullback (π : G →* H) (hπ : Continuous π) (hs : Function.Surjective π)
    (f : C(H, ℂ)) :
    (∫ g, f (π g) ∂normalizedHaar G) = ∫ h, f h ∂normalizedHaar H := by
  rw [← map_normalizedHaar π hπ hs]
  exact (integral_map_of_stronglyMeasurable hπ.measurable
    f.continuous.stronglyMeasurable).symm

end MathieuProperty
