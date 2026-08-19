import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalComb
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffPrimitiveStokes

/-!
# The mark-one exceptional trace, occurrence by occurrence

An exceptional raw-cutoff cell is itself the unique truncation occurrence
below its mark-one marked row.  This small specialization keeps that fact at
the level of the actual `ProvenancedRow` trace; in particular, no coefficient
of the later component PBW normal form is used to count the full relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalTraceFintype : Fintype L :=
  Fintype.ofFinite L

@[simp] theorem ProvenancedCell.provenancedCell?_markedRow
    (c : ProvenancedCell n L data hn) :
    provenancedCell? n L data hn c.markedRow = some c := by
  simp [ProvenancedCell.markedRow, provenancedCell?, c.mark_pos, c.not_wall]

theorem ProvenancedCell.provenancedExpansion_markedRow
    (c : ProvenancedCell n L data hn) :
    provenancedExpansion n L data hn c.markedRow =
      some [(1, .marked c.root c.context
          ⟨c.mark.val - 1, by omega⟩ c.left []),
        (1, c.componentRow)] := by
  simp [ProvenancedCell.markedRow, ProvenancedCell.componentRow,
    provenancedExpansion, Nat.ne_of_gt c.mark_pos, c.not_wall]

/-- At mark one the predecessor has mark zero and contributes no cell.  The
component branch never contributes truncation cells, so the source cell is
the unique labelled occurrence in the complete contextual trace. -/
theorem ProvenancedCell.provenancedTrace_markedRow_eq_single
    (c : ProvenancedCell n L data hn)
    (hmark : c.mark.val = 1) :
    provenancedTrace n L data hn c.markedRow = Finsupp.single c 1 := by
  have hexp := c.provenancedExpansion_markedRow n L data hn
  rw [provenancedTrace_eq_of_expansion_some
    n L data hn c.markedRow _ hexp]
  let predMark : Fin (n + 2) := ⟨c.mark.val - 1, by omega⟩
  have hpredMark : predMark = ⟨0, by omega⟩ := Fin.ext (by
    dsimp only [predMark]
    omega)
  let pred : ProvenancedRow n L data hn :=
    .marked c.root c.context predMark c.left []
  have hpredExpansion :
      provenancedExpansion n L data hn pred = some [] := by
    simp [pred, hpredMark, provenancedExpansion]
  have hpredTrace : provenancedTrace n L data hn pred = 0 := by
    rw [provenancedTrace_eq_of_expansion_some
      n L data hn pred [] hpredExpansion]
    have hnone : provenancedCell? n L data hn pred = none := by
      simp [pred, hpredMark, provenancedCell?]
    rw [hnone]
    rfl
  rw [c.provenancedCell?_markedRow n L data hn]
  simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, one_smul, add_zero]
  change Finsupp.single c 1 +
      (provenancedTrace n L data hn pred +
        provenancedTrace n L data hn c.componentRow) = Finsupp.single c 1
  rw [hpredTrace]
  simp [ProvenancedCell.componentRow,
    provenancedTrace_component_eq_zero]

/-- The word-valued Stokes theorem therefore reads one exceptional
occurrence exactly once.  This is the occurrence-level identity needed
before replacing its Smith head by the genuine full relation. -/
theorem ProvenancedCell.normalFormComponentFullLabelWord_markOne
    (c : ProvenancedCell n L data hn)
    (hmark : c.mark.val = 1) :
    normalFormProvenancedComponentFullLabelWord n L data hn c.markedRow =
      contextualFullRelationWord n L data hn
        c.root c.context c.left [] := by
  rw [normalFormProvenancedComponentFullLabelWord_eq_trace]
  unfold provenancedTraceMarkOneFullLabelWord
  rw [c.provenancedTrace_markedRow_eq_single n L data hn hmark]
  simp [ProvenancedCell.markedRow,
    provenancedComponentFullLabelWordSeed,
    provenancedTraceMarkOneFullLabelWord,
    ProvenancedCell.markOneFullLabelWord, hmark]

/-- The corresponding factor-two specialization follows by applying the
literal symbol projection to the same occurrence identity. -/
theorem ProvenancedCell.normalFormComponentFullLabelRead_markOne
    (c : ProvenancedCell n L data hn)
    (hmark : c.mark.val = 1) :
    normalFormProvenancedComponentFullLabelRead n L data hn c.markedRow =
      rightSymbol n L data hn 2 n (by omega)
        (contextualFullRelationWord n L data hn
          c.root c.context c.left []) := by
  rw [normalFormProvenancedComponentFullLabelRead_eq_trace]
  unfold provenancedTraceMarkOneFullLabelRead
  rw [c.provenancedTrace_markedRow_eq_single n L data hn hmark]
  simp [ProvenancedCell.markedRow, provenancedComponentFullLabelSeed,
    provenancedTraceMarkOneFullLabelRead,
    ProvenancedCell.markOneFullLabelRead, hmark]

end

end LieRings.MetabelianVanishing
