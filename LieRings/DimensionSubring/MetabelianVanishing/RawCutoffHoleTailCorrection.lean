import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffNonHoleCorrection

/-!
# The derived-tail part of the raw hole correction

The raw cutoff trace has one remaining mark-one family with empty relation
context.  This file separates that family according to whether its stored
*full* relation already belongs to the derived tail.  The tail-one part is
handled by the literal relation-on-the-right collector.  The complementary
definitions retain exactly the exceptional full relations with a nonzero
weight-one Smith head; no homogeneous component is promoted to a relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffHoleTailCorrectionFintype : Fintype L :=
  Fintype.ofFinite L

local instance rawCutoffHoleTailCorrectionPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

/-! ## The exact cellwise split -/

/-- A mark-one hole cell whose stored whole relation is already in the
derived tail. -/
def ProvenancedCell.IsHoleTailOne
    (c : ProvenancedCell n L data hn) : Prop :=
  c.mark.val = 1 ∧ c.context = .hole ∧
    (c.root : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1

/-- Factor-two full-label read of one tail-one hole cell. -/
def ProvenancedCell.holeTailOneFullLabelFactor
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  if c.IsHoleTailOne n L data hn then
    rightSymbol n L data hn 2 n (by omega)
      (contextualFullRelationWord n L data hn
        c.root c.context c.left [])
  else 0

/-- Complete one-factor PBW read of one tail-one hole cell. -/
def ProvenancedCell.holeTailOneFullLabelPrimitive
    (c : ProvenancedCell n L data hn) : FreeModel n L :=
  if c.IsHoleTailOne n L data hn then
    pbwPrimitive n L data hn
      (contextualFullRelationWord n L data hn
        c.root c.context c.left [])
  else 0

/-- Factor-two source chain attached to one tail-one hole cell. -/
def ProvenancedCell.holeTailOneFactorTwoChain
    (c : ProvenancedCell n L data hn) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  if c.IsHoleTailOne n L data hn then
    (c.fullLabelRightRow n L data hn).factorTwoChain n L data hn
  else 0

/-- Whole source-placement relation created by the cellwise tail-one
correction. -/
def ProvenancedCell.holeTailOnePrimitiveError
    (c : ProvenancedCell n L data hn) : Relations n L data :=
  if c.IsHoleTailOne n L data hn then
    (c.fullLabelRightRow n L data hn).primitiveError n L data hn
  else 0

/-- Complementary factor-two read.  It consists exactly of mark-one hole
cells whose stored full relation is not in the derived tail. -/
def ProvenancedCell.holeExceptionalFullLabelFactor
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  if c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 then
    rightSymbol n L data hn 2 n (by omega)
      (contextualFullRelationWord n L data hn
        c.root c.context c.left [])
  else 0

/-- Complete one-factor PBW read of the same exceptional cell. -/
def ProvenancedCell.holeExceptionalFullLabelPrimitive
    (c : ProvenancedCell n L data hn) : FreeModel n L :=
  if c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 then
    pbwPrimitive n L data hn
      (contextualFullRelationWord n L data hn
        c.root c.context c.left [])
  else 0

theorem ProvenancedCell.dOne_holeTailOneFactorTwoChain
    (c : ProvenancedCell n L data hn)
    (hordered : c.left.Pairwise (· ≤ ·)) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (c.holeTailOneFactorTwoChain n L data hn) =
      c.holeTailOneFullLabelFactor n L data hn := by
  classical
  by_cases hcell : c.IsHoleTailOne n L data hn
  · have htail : ((c.fullLabelRightRow n L data hn).relation :
        FreeModel n L) ∈
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
      simpa [ProvenancedCell.fullLabelRightRow, hcell.2.1] using hcell.2.2
    have hrow := relationRightRow_factorTwoChain_boundary
      n L data hn (c.fullLabelRightRow n L data hn) hordered htail
    simpa [ProvenancedCell.holeTailOneFactorTwoChain,
      ProvenancedCell.holeTailOneFullLabelFactor, hcell,
      ProvenancedCell.fullLabelRightRow_value] using hrow
  · simp [ProvenancedCell.holeTailOneFactorTwoChain,
      ProvenancedCell.holeTailOneFullLabelFactor, hcell]
    rfl

theorem ProvenancedCell.terminalSourcePrimitive_holeTailOneFactorTwoChain
    (c : ProvenancedCell n L data hn)
    (hordered : c.left.Pairwise (· ≤ ·)) :
    terminalSourcePrimitive n L data hn
        (c.holeTailOneFactorTwoChain n L data hn) =
      c.holeTailOneFullLabelPrimitive n L data hn +
        (c.holeTailOnePrimitiveError n L data hn : FreeModel n L) := by
  classical
  by_cases hcell : c.IsHoleTailOne n L data hn
  · have htail : ((c.fullLabelRightRow n L data hn).relation :
        FreeModel n L) ∈
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
      simpa [ProvenancedCell.fullLabelRightRow, hcell.2.1] using hcell.2.2
    have hrow := relationRightRow_factorTwoChain_primitive
      n L data hn (c.fullLabelRightRow n L data hn) hordered htail
    simpa [ProvenancedCell.holeTailOneFactorTwoChain,
      ProvenancedCell.holeTailOneFullLabelPrimitive,
      ProvenancedCell.holeTailOnePrimitiveError, hcell,
      ProvenancedCell.fullLabelRightRow_value] using hrow
  · simp [ProvenancedCell.holeTailOneFactorTwoChain,
      ProvenancedCell.holeTailOneFullLabelPrimitive,
      ProvenancedCell.holeTailOnePrimitiveError, hcell]

/-! ## Aggregate signed correction -/

/-- Aggregate source chain over the exact signed tail-one hole ledger. -/
def GoverningWitness.rawCutoffHoleTailOneCorrectionChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeTailOneFactorTwoChain n L data hn

/-- Aggregate factor-two target of the tail-one hole cells. -/
def GoverningWitness.rawCutoffHoleTailOneFullLabelFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeTailOneFullLabelFactor n L data hn

/-- Aggregate literal primitive of the tail-one hole cells. -/
def GoverningWitness.rawCutoffHoleTailOneFullLabelPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeTailOneFullLabelPrimitive n L data hn

/-- Aggregate full-relation placement error of the tail-one hole cells. -/
def GoverningWitness.rawCutoffHoleTailOnePrimitiveError
    {a : L} (w : GoverningWitness n L data a) : Relations n L data :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeTailOnePrimitiveError n L data hn

/-- Aggregate factor-two target of the complementary exceptional cells. -/
def GoverningWitness.rawCutoffHoleExceptionalFullLabelFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeExceptionalFullLabelFactor n L data hn

/-- Aggregate literal primitive of the complementary exceptional cells. -/
def GoverningWitness.rawCutoffHoleExceptionalFullLabelPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeExceptionalFullLabelPrimitive n L data hn

/-- The tail-one and exceptional predicates partition the hole factor read
without projecting the stored full relation. -/
theorem GoverningWitness.rawCutoffHoleFullLabelFactor_split
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffHoleTailOneFullLabelFactor n L data hn +
        w.rawCutoffHoleExceptionalFullLabelFactor n L data hn =
      w.rawCutoffHoleFullLabelFactor n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffHoleTailOneFullLabelFactor,
    GoverningWitness.rawCutoffHoleExceptionalFullLabelFactor,
    GoverningWitness.rawCutoffHoleFullLabelFactor, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hmark : c.mark.val = 1
  · by_cases hcontext : c.context = .hole
    · by_cases htail : (c.root : FreeModel n L) ∈
          FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1
      · simp [ProvenancedCell.holeTailOneFullLabelFactor,
          ProvenancedCell.holeExceptionalFullLabelFactor,
          ProvenancedCell.holeMarkOneFullLabelFactor,
          ProvenancedCell.IsHoleTailOne, hmark, hcontext, htail]
        module
      · simp [ProvenancedCell.holeTailOneFullLabelFactor,
          ProvenancedCell.holeExceptionalFullLabelFactor,
          ProvenancedCell.holeMarkOneFullLabelFactor,
          ProvenancedCell.IsHoleTailOne, hmark, hcontext, htail]
        module
    · simp [ProvenancedCell.holeTailOneFullLabelFactor,
        ProvenancedCell.holeExceptionalFullLabelFactor,
        ProvenancedCell.holeMarkOneFullLabelFactor,
        ProvenancedCell.IsHoleTailOne, hmark, hcontext]
      module
  · simp [ProvenancedCell.holeTailOneFullLabelFactor,
      ProvenancedCell.holeExceptionalFullLabelFactor,
      ProvenancedCell.holeMarkOneFullLabelFactor,
      ProvenancedCell.IsHoleTailOne, hmark]
    module

/-- The same exact partition for the complete one-factor PBW read. -/
theorem GoverningWitness.rawCutoffHoleFullLabelPrimitive_split
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffHoleTailOneFullLabelPrimitive n L data hn +
        w.rawCutoffHoleExceptionalFullLabelPrimitive n L data hn =
      w.rawCutoffHoleFullLabelPrimitive n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffHoleTailOneFullLabelPrimitive,
    GoverningWitness.rawCutoffHoleExceptionalFullLabelPrimitive,
    GoverningWitness.rawCutoffHoleFullLabelPrimitive, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hmark : c.mark.val = 1
  · by_cases hcontext : c.context = .hole
    · by_cases htail : (c.root : FreeModel n L) ∈
          FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1
      · simp [ProvenancedCell.holeTailOneFullLabelPrimitive,
          ProvenancedCell.holeExceptionalFullLabelPrimitive,
          ProvenancedCell.holeMarkOneFullLabelPrimitive,
          ProvenancedCell.IsHoleTailOne, hmark, hcontext, htail]
      · simp [ProvenancedCell.holeTailOneFullLabelPrimitive,
          ProvenancedCell.holeExceptionalFullLabelPrimitive,
          ProvenancedCell.holeMarkOneFullLabelPrimitive,
          ProvenancedCell.IsHoleTailOne, hmark, hcontext, htail]
    · simp [ProvenancedCell.holeTailOneFullLabelPrimitive,
        ProvenancedCell.holeExceptionalFullLabelPrimitive,
        ProvenancedCell.holeMarkOneFullLabelPrimitive,
        ProvenancedCell.IsHoleTailOne, hmark, hcontext]
  · simp [ProvenancedCell.holeTailOneFullLabelPrimitive,
      ProvenancedCell.holeExceptionalFullLabelPrimitive,
      ProvenancedCell.holeMarkOneFullLabelPrimitive,
      ProvenancedCell.IsHoleTailOne, hmark]

/-- Exact aggregate boundary of the tail-one hole correction. -/
theorem GoverningWitness.dOne_rawCutoffHoleTailOneCorrectionChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffHoleTailOneCorrectionChain n L data hn) =
      w.rawCutoffHoleTailOneFullLabelFactor n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffHoleTailOneCorrectionChain,
    GoverningWitness.rawCutoffHoleTailOneFullLabelFactor,
    map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul,
    c.dOne_holeTailOneFactorTwoChain n L data hn
      (w.rawCutoffFullProvenancedCells_left_pairwise
        n L data hn c (Finsupp.mem_support_iff.mp hc))]
  rfl

/-- Exact aggregate primitive equation of the same tail-one correction. -/
theorem GoverningWitness.terminalSourcePrimitive_rawCutoffHoleTailOneCorrectionChain
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (w.rawCutoffHoleTailOneCorrectionChain n L data hn) =
      w.rawCutoffHoleTailOneFullLabelPrimitive n L data hn +
        (w.rawCutoffHoleTailOnePrimitiveError n L data hn :
          FreeModel n L) := by
  classical
  rw [GoverningWitness.rawCutoffHoleTailOneCorrectionChain,
    GoverningWitness.rawCutoffHoleTailOneFullLabelPrimitive,
    map_finsuppSum]
  have hcoe :
      (w.rawCutoffHoleTailOnePrimitiveError n L data hn :
          FreeModel n L) =
        (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
          z • (c.holeTailOnePrimitiveError n L data hn :
            FreeModel n L)) := by
    rw [GoverningWitness.rawCutoffHoleTailOnePrimitiveError]
    change (Relations n L data).subtype
        ((w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
          z • c.holeTailOnePrimitiveError n L data hn)) = _
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
      (c.terminalSourcePrimitive_holeTailOneFactorTwoChain
        n L data hn
        (w.rawCutoffFullProvenancedCells_left_pairwise
          n L data hn c (Finsupp.mem_support_iff.mp hc)))

end

end LieRings.MetabelianVanishing
