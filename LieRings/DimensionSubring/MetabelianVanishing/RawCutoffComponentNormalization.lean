import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffProvenanceFrontier
import LieRings.DimensionSubring.MetabelianVanishing.ProvenancedComponentNormalization

/-!
# Ordered component normalization below the raw complete cutoff

The whole relation is first moved to the right and the ordinary neighbours
are sorted by `rawCutoffFullLabelFrontier`. Only then is the row fed to the
provenance collector. This file records that the ordering invariant survives
the entire provenance trace and specializes the generic component PBW reads
to that exact signed occurrence ledger.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffComponentNormalizationFintype : Fintype L :=
  Fintype.ofFinite L

/-- The single PBW-normalized component frontier belonging to the full raw
cutoff provenance trace. -/
def GoverningWitness.rawCutoffFullNormalizedComponentFrontier
    {a : L} (w : GoverningWitness n L data a) :
    ComponentPBWState n L data hn →₀ ℤ :=
  normalizedComponentFrontier n L data hn
    (w.rawCutoffFullProvenancedCells n L data hn)

/-- Exact factor-number read of the raw full-provenance component ledger. -/
theorem GoverningWitness.rawCutoffFullNormalizedFactor_eq_trace
    {a : L} (w : GoverningWitness n L data a)
    (q k : ℕ) (hk : k ≤ n + 1) :
    (w.rawCutoffFullNormalizedComponentFrontier n L data hn).sum
        (fun s z ↦ z • rightSymbol n L data hn q k hk
          (s.value n L data hn)) =
      (w.rawCutoffFullProvenancedCells n L data hn).sum
        (fun c z ↦ z • c.factorEdge n L data hn q k hk) := by
  exact normalizedComponentFactor_eq_trace n L data hn q k hk
    (w.rawCutoffFullProvenancedCells n L data hn)

/-- Exact primitive read of the same raw full-provenance component ledger. -/
theorem GoverningWitness.rawCutoffFullNormalizedPrimitive_eq_trace
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawCutoffFullNormalizedComponentFrontier n L data hn).sum
        (fun s z ↦ z • pbwPrimitive n L data hn
          (s.value n L data hn)) =
      (w.rawCutoffFullProvenancedCells n L data hn).sum
        (fun c z ↦ z • c.primitive n L data hn) := by
  exact normalizedComponentPrimitive_eq_trace n L data hn
    (w.rawCutoffFullProvenancedCells n L data hn)

/-- In the raw cutoff normalization, the primitive is supported only on
literal one-factor PBW leaves. -/
theorem GoverningWitness.rawCutoffFullNormalizedPrimitive_eq_factorOne
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawCutoffFullNormalizedComponentFrontier n L data hn).sum
        (fun s z ↦ z • pbwPrimitive n L data hn
          (s.value n L data hn)) =
      (w.rawCutoffFullNormalizedComponentFrontier n L data hn).sum
        (fun s z ↦ if s.factorCount n L data hn = 1 then
          z • pbwPrimitive n L data hn (s.value n L data hn) else 0) := by
  exact normalizedComponentPrimitive_eq_factorOne n L data hn
    (w.rawCutoffFullProvenancedCells n L data hn)
    (w.rawCutoffFullProvenancedCells_left_pairwise n L data hn)

end

end LieRings.MetabelianVanishing
