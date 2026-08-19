import LieRings.DimensionSubring.MetabelianVanishing.RelationSubsetTailCorrection
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalCoordinateAssembly

/-!
# Occurrence-level exceptional subset correction

This is the literal subset-collection step in the exceptional row of the
closed-square calculation.  The coefficient of a truncation occurrence is
kept outside the PBW component expansion.  Consequently a Smith diagonal is
read exactly once: no coefficient of a normalized component is used to count
the stored full relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalSubsetChainFintype : Fintype L :=
  Fintype.ofFinite L

local instance rawCutoffExceptionalSubsetChainPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

/-- The exceptional condition, kept at the original truncation occurrence. -/
def ProvenancedCell.IsHoleExceptional
    (c : ProvenancedCell n L data hn) : Prop :=
  c.mark.val = 1 ∧ c.context = .hole ∧
    (c.root : FreeModel n L) ∉
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1

/-- Cell-oriented form of the exceptional top-coordinate theorem. -/
theorem ProvenancedCell.topCoord_weightProject_primitive_eq_zero_of_rawCutoffHoleExceptional
    (c : ProvenancedCell n L data hn)
    {a : L} (w : GoverningWitness n L data a)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0)
    (hexceptional : c.IsHoleExceptional n L data hn) :
    topCoord n L data
        (FreeMetabelian.Free.weightProject n (by omega)
          (c.primitive n L data hn)) = 0 := by
  apply w.topCoord_weightProject_primitive_eq_zero_of_rawCutoffHoleExceptional
    n L data hn c hc
  simpa only [ProvenancedCell.IsHoleExceptional] using hexceptional

/-- The proper-subset correction for one exceptional occurrence.  Its sign is
opposite to the tail in
`rho * xs = xs * rho + properSubsetTail`. -/
def ProvenancedCell.holeExceptionalSubsetTailChain
    (c : ProvenancedCell n L data hn) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  if c.IsHoleExceptional n L data hn then
    -relationSubsetTailFactorTwoChain n L data hn c.root c.left
  else 0

/-- The relation-on-the-left factor-two read left by subset collection. -/
def ProvenancedCell.holeExceptionalRelationLeftFactor
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  if c.IsHoleExceptional n L data hn then
    rightSymbol n L data hn 2 n (by omega)
      (UniversalEnvelopingAlgebra.ι ℤ (c.root : FreeModel n L) *
        MarkedRow.basisWord n L data hn c.left)
  else 0

/-- The complete PBW primitive of the same relation-on-the-left word. -/
def ProvenancedCell.holeExceptionalRelationLeftPrimitive
    (c : ProvenancedCell n L data hn) : FreeModel n L :=
  if c.IsHoleExceptional n L data hn then
    pbwPrimitive n L data hn
      (UniversalEnvelopingAlgebra.ι ℤ (c.root : FreeModel n L) *
        MarkedRow.basisWord n L data hn c.left)
  else 0

/-- The genuine full-relation placement error of the proper-subset chain,
with the sign used by the exceptional correction. -/
def ProvenancedCell.holeExceptionalSubsetTailPrimitiveError
    (c : ProvenancedCell n L data hn) : Relations n L data :=
  if c.IsHoleExceptional n L data hn then
    -relationSubsetTailPrimitiveError n L data hn c.root c.left
  else 0

/-- One occurrence of the subset identity, after factor-two projection. -/
theorem ProvenancedCell.dOne_holeExceptionalSubsetTailChain
    (c : ProvenancedCell n L data hn)
    (hordered : c.left.Pairwise (· ≤ ·))
    (hlen : c.IsHoleExceptional n L data hn → 2 ≤ c.left.length) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (c.holeExceptionalSubsetTailChain n L data hn) =
      c.holeExceptionalComponentFactor n L data hn -
        c.holeExceptionalRelationLeftFactor n L data hn := by
  classical
  by_cases h : c.IsHoleExceptional n L data hn
  · have hraw : c.mark.val = 1 ∧ c.context = .hole ∧
        (c.root : FreeModel n L) ∉
          FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
      simpa [ProvenancedCell.IsHoleExceptional] using h
    rw [ProvenancedCell.holeExceptionalSubsetTailChain,
      if_pos h, map_neg,
      dOne_relationSubsetTailFactorTwoChain n L data hn
        c.root c.left hordered]
    rw [ProvenancedCell.holeExceptionalComponentFactor, if_pos hraw,
      ProvenancedCell.holeExceptionalRelationLeftFactor, if_pos h]
    have hright :=
      c.rightSymbol_fullLabelRightRow_eq_factorEdge_of_markOne_hole
        n L data hn h.1 h.2.1 hordered (hlen h)
    have hcollection := congrArg
      (rightSymbol n L data hn 2 n (by omega))
      (relationSubsetCollection_value n L data hn c.root c.left)
    rw [relationSubsetCollection_value_eq_unbracketed_add_tail,
      map_add] at hcollection
    have hunbracketed :
        RelationRightRow.value n L data hn
            ⟨c.root, c.left⟩ =
          (c.fullLabelRightRow n L data hn).value n L data hn := by
      simp [RelationRightRow.value, ProvenancedCell.fullLabelRightRow,
        h.2.1, contextualFullRelationWord, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.word]
    rw [hunbracketed, hright] at hcollection
    apply (eq_sub_iff_add_eq).2
    rw [← hcollection]
    abel
  · have hraw : ¬ (c.mark.val = 1 ∧ c.context = .hole ∧
        (c.root : FreeModel n L) ∉
          FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) := by
      simpa [ProvenancedCell.IsHoleExceptional] using h
    rw [ProvenancedCell.holeExceptionalSubsetTailChain,
      if_neg h, map_zero,
      ProvenancedCell.holeExceptionalComponentFactor, if_neg hraw,
      ProvenancedCell.holeExceptionalRelationLeftFactor, if_neg h,
      sub_zero]
    rfl

/-- The same occurrence-level subset identity after complete primitive
projection.  The only extra summand is a genuine full relation. -/
theorem ProvenancedCell.terminalSourcePrimitive_holeExceptionalSubsetTailChain
    (c : ProvenancedCell n L data hn)
    (hordered : c.left.Pairwise (· ≤ ·))
    (hlen : c.IsHoleExceptional n L data hn → 2 ≤ c.left.length) :
    terminalSourcePrimitive n L data hn
        (c.holeExceptionalSubsetTailChain n L data hn) =
      c.holeExceptionalComponentPrimitive n L data hn -
          c.holeExceptionalRelationLeftPrimitive n L data hn +
        (c.holeExceptionalSubsetTailPrimitiveError n L data hn :
          FreeModel n L) := by
  classical
  by_cases h : c.IsHoleExceptional n L data hn
  · have hraw : c.mark.val = 1 ∧ c.context = .hole ∧
        (c.root : FreeModel n L) ∉
          FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
      simpa [ProvenancedCell.IsHoleExceptional] using h
    rw [ProvenancedCell.holeExceptionalSubsetTailChain,
      if_pos h, map_neg,
      terminalSourcePrimitive_relationSubsetTailFactorTwoChain
        n L data hn c.root c.left hordered]
    rw [ProvenancedCell.holeExceptionalComponentPrimitive, if_pos hraw,
      ProvenancedCell.holeExceptionalRelationLeftPrimitive, if_pos h,
      ProvenancedCell.holeExceptionalSubsetTailPrimitiveError, if_pos h]
    have hright :=
      c.pbwPrimitive_fullLabelRightRow_eq_primitive_of_markOne_hole
        n L data hn h.1 h.2.1 hordered (hlen h)
    have hcollection := congrArg (pbwPrimitive n L data hn)
      (relationSubsetCollection_value n L data hn c.root c.left)
    rw [relationSubsetCollection_value_eq_unbracketed_add_tail,
      map_add] at hcollection
    have hunbracketed :
        RelationRightRow.value n L data hn
            ⟨c.root, c.left⟩ =
          (c.fullLabelRightRow n L data hn).value n L data hn := by
      simp [RelationRightRow.value, ProvenancedCell.fullLabelRightRow,
        h.2.1, contextualFullRelationWord, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.word]
    rw [hunbracketed, hright] at hcollection
    change -(_ + _) = _ - _ + ((-relationSubsetTailPrimitiveError
      n L data hn c.root c.left : Relations n L data) : FreeModel n L)
    change -(_ + _) = _ - _ + -((relationSubsetTailPrimitiveError
      n L data hn c.root c.left : Relations n L data) : FreeModel n L)
    rw [← hcollection]
    module
  · have hraw : ¬ (c.mark.val = 1 ∧ c.context = .hole ∧
        (c.root : FreeModel n L) ∉
          FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) := by
      simpa [ProvenancedCell.IsHoleExceptional] using h
    rw [ProvenancedCell.holeExceptionalSubsetTailChain,
      if_neg h, map_zero,
      ProvenancedCell.holeExceptionalComponentPrimitive, if_neg hraw,
      ProvenancedCell.holeExceptionalRelationLeftPrimitive, if_neg h,
      ProvenancedCell.holeExceptionalSubsetTailPrimitiveError, if_neg h]
    simp

/-! ## Signed aggregate over the raw truncation occurrences -/

def GoverningWitness.rawCutoffExceptionalSubsetTailChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeExceptionalSubsetTailChain n L data hn

def GoverningWitness.rawCutoffExceptionalRelationLeftFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeExceptionalRelationLeftFactor n L data hn

def GoverningWitness.rawCutoffExceptionalRelationLeftPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeExceptionalRelationLeftPrimitive n L data hn

def GoverningWitness.rawCutoffExceptionalSubsetTailPrimitiveError
    {a : L} (w : GoverningWitness n L data a) : Relations n L data :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
    z • c.holeExceptionalSubsetTailPrimitiveError n L data hn

theorem GoverningWitness.dOne_rawCutoffExceptionalSubsetTailChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffExceptionalSubsetTailChain n L data hn) =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
          z • c.holeExceptionalComponentFactor n L data hn) -
        w.rawCutoffExceptionalRelationLeftFactor n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffExceptionalSubsetTailChain,
    GoverningWitness.rawCutoffExceptionalRelationLeftFactor,
    map_finsuppSum]
  simp_rw [map_zsmul]
  calc
    _ = (w.rawCutoffFullProvenancedCells n L data hn).sum
        (fun c z ↦ z •
          (c.holeExceptionalComponentFactor n L data hn -
            c.holeExceptionalRelationLeftFactor n L data hn)) := by
      apply Finsupp.sum_congr
      intro c hc
      exact congrArg
        (fun x ↦ w.rawCutoffFullProvenancedCells n L data hn c • x)
        (c.dOne_holeExceptionalSubsetTailChain n L data hn
          (w.rawCutoffFullProvenancedCells_left_pairwise
            n L data hn c (Finsupp.mem_support_iff.mp hc))
          (fun he ↦
            w.rawCutoffFullProvenancedCells_markOne_left_length
              n L data hn c (Finsupp.mem_support_iff.mp hc) he.1))
    _ = (w.rawCutoffFullProvenancedCells n L data hn).sum
          (fun c z ↦ z • c.holeExceptionalComponentFactor
            n L data hn -
            z • c.holeExceptionalRelationLeftFactor n L data hn) := by
      apply Finsupp.sum_congr
      intro c hc
      module
    _ = _ := Finsupp.sum_sub

theorem GoverningWitness.terminalSourcePrimitive_rawCutoffExceptionalSubsetTailChain
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (w.rawCutoffExceptionalSubsetTailChain n L data hn) =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
          z • c.holeExceptionalComponentPrimitive n L data hn) -
          w.rawCutoffExceptionalRelationLeftPrimitive n L data hn +
        (w.rawCutoffExceptionalSubsetTailPrimitiveError n L data hn :
          FreeModel n L) := by
  classical
  rw [GoverningWitness.rawCutoffExceptionalSubsetTailChain,
    GoverningWitness.rawCutoffExceptionalRelationLeftPrimitive,
    GoverningWitness.rawCutoffExceptionalSubsetTailPrimitiveError,
    map_finsuppSum]
  simp_rw [map_zsmul]
  calc
    _ = (w.rawCutoffFullProvenancedCells n L data hn).sum
        (fun c z ↦ z •
          (c.holeExceptionalComponentPrimitive n L data hn -
              c.holeExceptionalRelationLeftPrimitive n L data hn +
            (c.holeExceptionalSubsetTailPrimitiveError n L data hn :
              FreeModel n L))) := by
      apply Finsupp.sum_congr
      intro c hc
      exact congrArg
        (fun x ↦ w.rawCutoffFullProvenancedCells n L data hn c • x)
        (c.terminalSourcePrimitive_holeExceptionalSubsetTailChain
          n L data hn
          (w.rawCutoffFullProvenancedCells_left_pairwise
            n L data hn c (Finsupp.mem_support_iff.mp hc))
          (fun he ↦
            w.rawCutoffFullProvenancedCells_markOne_left_length
              n L data hn c (Finsupp.mem_support_iff.mp hc) he.1))
    _ = (w.rawCutoffFullProvenancedCells n L data hn).sum
          (fun c z ↦
            z • c.holeExceptionalComponentPrimitive n L data hn -
              z • c.holeExceptionalRelationLeftPrimitive n L data hn +
            z • (c.holeExceptionalSubsetTailPrimitiveError
              n L data hn : FreeModel n L)) := by
      apply Finsupp.sum_congr
      intro c hc
      module
    _ = _ := by
      rw [Finsupp.sum_add, Finsupp.sum_sub]
      change _ = _ - _ +
        (Relations n L data).subtype
          ((w.rawCutoffFullProvenancedCells n L data hn).sum fun c z ↦
            z • c.holeExceptionalSubsetTailPrimitiveError n L data hn)
      rw [map_finsuppSum]
      apply congrArg (fun x ↦ _ - _ + x)
      apply Finsupp.sum_congr
      intro c hc
      rw [map_zsmul]
      rfl

/-- The part of the canonical exceptional boundary which compensates the
relation-on-the-left upper edge of subset collection. -/
def GoverningWitness.rawCutoffExceptionalRelationLeftChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  w.rawCutoffExceptionalBoundaryChain n L data hn -
    w.rawCutoffExceptionalSubsetTailChain n L data hn

theorem GoverningWitness.dOne_rawCutoffExceptionalRelationLeftChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffExceptionalRelationLeftChain n L data hn) =
      w.rawCutoffExceptionalRelationLeftFactor n L data hn := by
  rw [GoverningWitness.rawCutoffExceptionalRelationLeftChain, map_sub,
    w.dOne_rawCutoffExceptionalBoundaryChain n L data hn,
    w.dOne_rawCutoffExceptionalSubsetTailChain n L data hn]
  abel

/-- Closed-square endpoint after the compensating relation-on-the-left chain
has been read.  This is deliberately not stated by claiming that its boundary
vanishes: the nonzero upper edge is canceled by the signed proper-subset
chain. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalRelationLeftCoordinate
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (leftError : TopPreimage n L data)
    (hleftBoundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 leftChain =
      w.rawCutoffExceptionalRelationLeftFactor n L data hn)
    (hleftPrimitive : terminalSourcePrimitive n L data hn leftChain =
      w.rawCutoffExceptionalRelationLeftPrimitive n L data hn +
        (leftError : FreeModel n L))
    (hleftZero : terminalEval n L data leftError = 0) :
    a = 0 := by
  let exceptionalChain :=
    w.rawCutoffExceptionalSubsetTailChain n L data hn + leftChain
  let error : TopPreimage n L data :=
    relationTopPreimage n L data
        (w.rawCutoffExceptionalSubsetTailPrimitiveError n L data hn) +
      leftError
  apply w.eq_zero_of_rawCutoffExceptionalComponentCoordinate
    n L data hn exceptionalChain error
  · change Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffExceptionalSubsetTailChain n L data hn + leftChain) = _
    rw [map_add,
      w.dOne_rawCutoffExceptionalSubsetTailChain n L data hn,
      hleftBoundary]
    abel
  · change terminalSourcePrimitive n L data hn
        (w.rawCutoffExceptionalSubsetTailChain n L data hn + leftChain) = _
    rw [map_add,
      w.terminalSourcePrimitive_rawCutoffExceptionalSubsetTailChain
        n L data hn,
      hleftPrimitive]
    change _ - _ + _ + (_ + (leftError : FreeModel n L)) = _ +
      (((relationTopPreimage n L data
          (w.rawCutoffExceptionalSubsetTailPrimitiveError
            n L data hn) + leftError : TopPreimage n L data)) :
        FreeModel n L)
    change _ - _ + _ + (_ + (leftError : FreeModel n L)) = _ +
      ((w.rawCutoffExceptionalSubsetTailPrimitiveError
          n L data hn : FreeModel n L) + (leftError : FreeModel n L))
    abel
  · change terminalEval n L data
      (relationTopPreimage n L data
          (w.rawCutoffExceptionalSubsetTailPrimitiveError n L data hn) +
        leftError) = 0
    rw [map_add, terminalEval_relationTopPreimage, hleftZero, zero_add]

end

end LieRings.MetabelianVanishing
