import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffFullLabelStokes
import LieRings.DimensionSubring.MetabelianVanishing.RelationSubsetCorrection

/-!
# The non-hole part of the raw terminal correction

Every mark-one truncation cell with a nonempty bracket context carries a full
contextual relation in the derived tail.  The relation-on-the-right collector
therefore realizes its exact factor-two full-label read by a Koszul chain.  Its
source primitive differs from the literal PBW primitive only by a genuine full
relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffNonHoleCorrectionFintype : Fintype L :=
  Fintype.ofFinite L

/-- The exact full-label factor-two read of one non-hole mark-one cell. -/
def ProvenancedCell.nonHoleMarkOneFullLabelFactor
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  if c.mark.val = 1 ∧ c.context ≠ .hole then
    rightSymbol n L data hn 2 n (by omega)
      (contextualFullRelationWord n L data hn
        c.root c.context c.left [])
  else 0

/-- Its literal complete one-factor PBW read. -/
def ProvenancedCell.nonHoleMarkOneFullLabelPrimitive
    (c : ProvenancedCell n L data hn) : FreeModel n L :=
  if c.mark.val = 1 ∧ c.context ≠ .hole then
    pbwPrimitive n L data hn
      (contextualFullRelationWord n L data hn
        c.root c.context c.left [])
  else 0

/-- The complementary full-label factor-two read: mark one with the original
empty bracket context.  This definition is deliberately kept separate from
the correction chain, since this is the unique family whose relation can
still have a weight-one component. -/
def ProvenancedCell.holeMarkOneFullLabelFactor
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  if c.mark.val = 1 ∧ c.context = .hole then
    rightSymbol n L data hn 2 n (by omega)
      (contextualFullRelationWord n L data hn
        c.root c.context c.left [])
  else 0

/-- Literal complete one-factor PBW read of the complementary hole cell. -/
def ProvenancedCell.holeMarkOneFullLabelPrimitive
    (c : ProvenancedCell n L data hn) : FreeModel n L :=
  if c.mark.val = 1 ∧ c.context = .hole then
    pbwPrimitive n L data hn
      (contextualFullRelationWord n L data hn
        c.root c.context c.left [])
  else 0

/-- The factor-two Koszul correction attached to one non-hole mark-one cell. -/
def ProvenancedCell.nonHoleMarkOneFactorTwoChain
    (c : ProvenancedCell n L data hn) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  if c.mark.val = 1 ∧ c.context ≠ .hole then
    (c.fullLabelRightRow n L data hn).factorTwoChain n L data hn
  else 0

/-- The genuine relation created by changing the source placement in the
cellwise correction. -/
def ProvenancedCell.nonHoleMarkOnePrimitiveError
    (c : ProvenancedCell n L data hn) : Relations n L data :=
  if c.mark.val = 1 ∧ c.context ≠ .hole then
    (c.fullLabelRightRow n L data hn).primitiveError n L data hn
  else 0

theorem ProvenancedCell.dOne_nonHoleMarkOneFactorTwoChain
    (c : ProvenancedCell n L data hn)
    (hordered : c.left.Pairwise (· ≤ ·)) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (c.nonHoleMarkOneFactorTwoChain n L data hn) =
      c.nonHoleMarkOneFullLabelFactor n L data hn := by
  classical
  by_cases hcell : c.mark.val = 1 ∧ c.context ≠ .hole
  · have htail := RelationContext.relation_mem_tail_one_of_ne_hole
      n L data hn c.context c.root hcell.2
    have hrow := relationRightRow_factorTwoChain_boundary
      n L data hn (c.fullLabelRightRow n L data hn) hordered htail
    simpa [ProvenancedCell.nonHoleMarkOneFactorTwoChain,
      ProvenancedCell.nonHoleMarkOneFullLabelFactor, hcell,
      ProvenancedCell.fullLabelRightRow_value] using hrow
  · simp [ProvenancedCell.nonHoleMarkOneFactorTwoChain,
      ProvenancedCell.nonHoleMarkOneFullLabelFactor, hcell]
    rfl

theorem ProvenancedCell.terminalSourcePrimitive_nonHoleMarkOneFactorTwoChain
    (c : ProvenancedCell n L data hn)
    (hordered : c.left.Pairwise (· ≤ ·)) :
    terminalSourcePrimitive n L data hn
        (c.nonHoleMarkOneFactorTwoChain n L data hn) =
      c.nonHoleMarkOneFullLabelPrimitive n L data hn +
        (c.nonHoleMarkOnePrimitiveError n L data hn : FreeModel n L) := by
  classical
  by_cases hcell : c.mark.val = 1 ∧ c.context ≠ .hole
  · have htail := RelationContext.relation_mem_tail_one_of_ne_hole
      n L data hn c.context c.root hcell.2
    have hrow := relationRightRow_factorTwoChain_primitive
      n L data hn (c.fullLabelRightRow n L data hn) hordered htail
    simpa [ProvenancedCell.nonHoleMarkOneFactorTwoChain,
      ProvenancedCell.nonHoleMarkOneFullLabelPrimitive,
      ProvenancedCell.nonHoleMarkOnePrimitiveError, hcell,
      ProvenancedCell.fullLabelRightRow_value] using hrow
  · simp [ProvenancedCell.nonHoleMarkOneFactorTwoChain,
      ProvenancedCell.nonHoleMarkOneFullLabelPrimitive,
      ProvenancedCell.nonHoleMarkOnePrimitiveError, hcell]

/-- Aggregate non-hole correction over the exact signed raw truncation
ledger. -/
def GoverningWitness.rawCutoffNonHoleCorrectionChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.nonHoleMarkOneFactorTwoChain n L data hn

/-- Aggregate factor-two target of the same signed cells. -/
def GoverningWitness.rawCutoffNonHoleFullLabelFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.nonHoleMarkOneFullLabelFactor n L data hn

/-- Aggregate literal PBW primitive of the same signed cells. -/
def GoverningWitness.rawCutoffNonHoleFullLabelPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.nonHoleMarkOneFullLabelPrimitive n L data hn

/-- Aggregate factor-two target of the complementary hole cells. -/
def GoverningWitness.rawCutoffHoleFullLabelFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeMarkOneFullLabelFactor n L data hn

/-- Aggregate literal PBW primitive of the complementary hole cells. -/
def GoverningWitness.rawCutoffHoleFullLabelPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeMarkOneFullLabelPrimitive n L data hn

/-- The non-hole and hole predicates partition the exact mark-one
full-label factor ledger. -/
theorem GoverningWitness.rawCutoffMarkOneFullLabelFactor_split
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffNonHoleFullLabelFactor n L data hn +
        w.rawCutoffHoleFullLabelFactor n L data hn =
      w.rawCutoffTraceMarkOneFullLabel n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffNonHoleFullLabelFactor,
    GoverningWitness.rawCutoffHoleFullLabelFactor,
    GoverningWitness.rawCutoffTraceMarkOneFullLabel,
    ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hmark : c.mark.val = 1
  · by_cases hcontext : c.context = .hole
    · simp [ProvenancedCell.nonHoleMarkOneFullLabelFactor,
        ProvenancedCell.holeMarkOneFullLabelFactor,
        ProvenancedCell.markOneFullLabelRead, hmark, hcontext]
      module
    · simp [ProvenancedCell.nonHoleMarkOneFullLabelFactor,
        ProvenancedCell.holeMarkOneFullLabelFactor,
        ProvenancedCell.markOneFullLabelRead, hmark, hcontext]
      module
  · simp [ProvenancedCell.nonHoleMarkOneFullLabelFactor,
      ProvenancedCell.holeMarkOneFullLabelFactor,
      ProvenancedCell.markOneFullLabelRead, hmark]
    module

/-- The same exact partition for the complete one-factor PBW read. -/
theorem GoverningWitness.rawCutoffMarkOneFullLabelPrimitive_split
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffNonHoleFullLabelPrimitive n L data hn +
        w.rawCutoffHoleFullLabelPrimitive n L data hn =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
        z • if c.mark.val = 1 then
          pbwPrimitive n L data hn
            (contextualFullRelationWord n L data hn
              c.root c.context c.left [])
        else 0) := by
  classical
  rw [GoverningWitness.rawCutoffNonHoleFullLabelPrimitive,
    GoverningWitness.rawCutoffHoleFullLabelPrimitive, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hmark : c.mark.val = 1
  · by_cases hcontext : c.context = .hole
    · simp [ProvenancedCell.nonHoleMarkOneFullLabelPrimitive,
        ProvenancedCell.holeMarkOneFullLabelPrimitive, hmark, hcontext]
    · simp [ProvenancedCell.nonHoleMarkOneFullLabelPrimitive,
        ProvenancedCell.holeMarkOneFullLabelPrimitive, hmark, hcontext]
  · simp [ProvenancedCell.nonHoleMarkOneFullLabelPrimitive,
      ProvenancedCell.holeMarkOneFullLabelPrimitive, hmark]

/-- Aggregate source-placement error, still an honest element of the full
relation submodule. -/
def GoverningWitness.rawCutoffNonHolePrimitiveError
    {a : L} (w : GoverningWitness n L data a) : Relations n L data :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.nonHoleMarkOnePrimitiveError n L data hn

theorem GoverningWitness.dOne_rawCutoffNonHoleCorrectionChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffNonHoleCorrectionChain n L data hn) =
      w.rawCutoffNonHoleFullLabelFactor n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffNonHoleCorrectionChain,
    GoverningWitness.rawCutoffNonHoleFullLabelFactor, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul,
    c.dOne_nonHoleMarkOneFactorTwoChain n L data hn
      (w.rawCutoffFullProvenancedCells_left_pairwise
        n L data hn c (Finsupp.mem_support_iff.mp hc))]
  rfl

theorem GoverningWitness.terminalSourcePrimitive_rawCutoffNonHoleCorrectionChain
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (w.rawCutoffNonHoleCorrectionChain n L data hn) =
      w.rawCutoffNonHoleFullLabelPrimitive n L data hn +
        (w.rawCutoffNonHolePrimitiveError n L data hn : FreeModel n L) := by
  classical
  rw [GoverningWitness.rawCutoffNonHoleCorrectionChain,
    GoverningWitness.rawCutoffNonHoleFullLabelPrimitive, map_finsuppSum]
  have hcoe :
      (w.rawCutoffNonHolePrimitiveError n L data hn : FreeModel n L) =
        (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
          z • (c.nonHoleMarkOnePrimitiveError n L data hn :
            FreeModel n L)) := by
    rw [GoverningWitness.rawCutoffNonHolePrimitiveError]
    change (Relations n L data).subtype
        ((w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
          z • c.nonHoleMarkOnePrimitiveError n L data hn)) = _
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro c hc
    rw [map_zsmul]
    rfl
  rw [hcoe, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul]
  simpa only [smul_add] using congrArg
    (fun x ↦ w.rawCutoffFullProvenancedCells n L data hn c • x)
      (c.terminalSourcePrimitive_nonHoleMarkOneFactorTwoChain
        n L data hn
        (w.rawCutoffFullProvenancedCells_left_pairwise
          n L data hn c (Finsupp.mem_support_iff.mp hc)))

end

end LieRings.MetabelianVanishing
