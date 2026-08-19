import LieRings.DimensionSubring.MetabelianVanishing.GlobalHorizontalFrontier
import LieRings.DimensionSubring.MetabelianVanishing.OrderedPBWPrimitive

/-!
# Exhaustive stopping rules for the global closed-square trace

This file formalizes Rules (1), (4), and the syntactic part of Rule (5) in
the corrected manuscript.  The marked/component transfer pass and the
component PBW pass are kept as two genuinely different phases.  In
particular, a vertically normal component is not called Hall-normal until it
has passed through `componentPBWCollector`.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.DegreeFive

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalStoppingRulesFintype : Fintype L :=
  Fintype.ofFinite L

namespace ProvenancedRow

/-- The full relation root carried by a provenance row.  This datum is never
changed by either direction of the marked-row square. -/
def HasRoot (root : Relations n L data) :
    ProvenancedRow n L data hn → Prop
  | .marked rowRoot _ _ _ _ | .component rowRoot _ _ _ _ =>
      rowRoot = root

/-- The context and the two ordinary-factor lists carried along the
horizontal truncation spine. -/
def HasHorizontalFrame
    (context : RelationContext n L data hn)
    (left right : List (AdaptedIndex n L data hn)) :
    ProvenancedRow n L data hn → Prop
  | .marked _ rowContext _ rowLeft rowRight
  | .component _ rowContext _ rowLeft rowRight =>
      rowContext = context ∧ rowLeft = left ∧ rowRight = right

/-- Horizontal truncation preserves the literal full-relation root. -/
theorem horizontalExpansion_preserves_HasRoot
    (root : Relations n L data)
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : horizontalExpansion n L data hn r = some rows)
    (hr : r.HasRoot n L data hn root) :
    ∀ q ∈ rows, q.2.HasRoot n L data hn root := by
  cases r with
  | component => simp [horizontalExpansion] at h
  | marked rowRoot context mark left right =>
      simp only [horizontalExpansion] at h
      split at h
      · contradiction
      · rw [Option.some.injEq] at h
        subst rows
        simpa [HasRoot] using hr

/-- Horizontal truncation changes only the mark and constructor, so it
preserves the complete ordinary-factor frame. -/
theorem horizontalExpansion_preserves_HasHorizontalFrame
    (context : RelationContext n L data hn)
    (left right : List (AdaptedIndex n L data hn))
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : horizontalExpansion n L data hn r = some rows)
    (hr : r.HasHorizontalFrame n L data hn context left right) :
    ∀ q ∈ rows,
      q.2.HasHorizontalFrame n L data hn context left right := by
  cases r with
  | component => simp [horizontalExpansion] at h
  | marked rowRoot rowContext mark rowLeft rowRight =>
      simp only [horizontalExpansion] at h
      split at h
      · contradiction
      · rw [Option.some.injEq] at h
        subst rows
        simpa [HasHorizontalFrame] using hr

/-- Vertical transfer preserves the literal full-relation root. -/
theorem verticalExpansion_preserves_HasRoot
    (root : Relations n L data)
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows)
    (hr : r.HasRoot n L data hn root) :
    ∀ q ∈ rows, q.2.HasRoot n L data hn root := by
  cases r with
  | component rowRoot context mark left right =>
      simp only [verticalExpansion] at h
      split at h
      · contradiction
      · rw [Option.some.injEq] at h
        subst rows
        simpa [HasRoot] using hr
  | marked rowRoot context mark left right =>
      cases right with
      | nil => simp [verticalExpansion] at h
      | cons x right =>
          rw [show rows =
              [(1, .marked rowRoot context mark (left ++ [x]) right),
                (1, .marked rowRoot (RelationContext.lieRight context x)
                  mark left right)] by
            simpa [verticalExpansion] using (Option.some.inj h).symm]
          simpa [HasRoot] using hr

/-- The constructor of a row is part of its occurrence provenance. -/
def IsComponent : ProvenancedRow n L data hn → Prop
  | .component _ _ _ _ _ => True
  | .marked _ _ _ _ _ => False

/-- The quotient-tower mark, independently of the row constructor. -/
def markValue : ProvenancedRow n L data hn → ℕ
  | .component _ _ mark _ _ | .marked _ _ mark _ _ => mark.val

noncomputable instance (r : ProvenancedRow n L data hn) :
    Decidable (r.IsComponent n L data hn) := Classical.propDecidable _

/-- Both children of a vertical transfer retain the row constructor. -/
theorem verticalExpansion_preserves_isComponent
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows)
    (hr : r.IsComponent n L data hn) :
    ∀ q ∈ rows, q.2.IsComponent n L data hn := by
  cases r with
  | component root context mark left right =>
      simp only [verticalExpansion] at h
      split at h
      · contradiction
      · rw [Option.some.injEq] at h
        subst rows
        simp [IsComponent]
  | marked => simp [IsComponent] at hr

/-- A vertical transfer never changes the quotient-tower mark. -/
theorem verticalExpansion_preserves_markValue
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows) :
    ∀ q ∈ rows,
      q.2.markValue n L data hn = r.markValue n L data hn := by
  cases r with
  | component root context mark left right =>
      simp only [verticalExpansion] at h
      split at h
      · contradiction
      · rw [Option.some.injEq] at h
        subst rows
        simp [markValue]
  | marked root context mark left right =>
      cases right with
      | nil => simp [verticalExpansion] at h
      | cons x right =>
          rw [show rows =
              [(1, .marked root context mark (left ++ [x]) right),
                (1, .marked root (RelationContext.lieRight context x)
                  mark left right)] by
            simpa [verticalExpansion] using (Option.some.inj h).symm]
          simp [markValue]

/-- Ordered ordinary neighbours are stable under the separated vertical
pass. -/
theorem verticalExpansion_ordinaryNeighbors_pairwise
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows)
    (hr : (r.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·)) :
    ∀ q ∈ rows,
      (q.2.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·) :=
  provenancedExpansion_ordinaryNeighbors_pairwise n L data hn
    (verticalExpansion_eq_provenancedExpansion_of_some n L data hn h) hr

/-- Ordered ordinary neighbours are also stable under the literal
two-child truncation. -/
theorem horizontalExpansion_ordinaryNeighbors_pairwise
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : horizontalExpansion n L data hn r = some rows)
    (hr : (r.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·)) :
    ∀ q ∈ rows,
      (q.2.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·) := by
  cases r with
  | component => simp [horizontalExpansion] at h
  | marked root context mark left right =>
      simp only [horizontalExpansion] at h
      split at h
      · contradiction
      · rw [Option.some.injEq] at h
        subst rows
        simpa [ordinaryNeighbors] using hr

/-- Every component child emitted by a genuine horizontal truncation carries
the positive mark which was truncated. -/
theorem horizontalExpansion_component_mark_pos
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : horizontalExpansion n L data hn r = some rows)
    (q : ℤ × ProvenancedRow n L data hn) (hq : q ∈ rows)
    (root : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2))
    (left right : List (AdaptedIndex n L data hn))
    (heq : q.2 = .component root context mark left right) :
    0 < mark.val := by
  cases r with
  | component => simp [horizontalExpansion] at h
  | marked parentRoot parentContext parentMark parentLeft parentRight =>
      simp only [horizontalExpansion] at h
      split at h
      · contradiction
      · rename_i hmark
        rw [Option.some.injEq] at h
        subst rows
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · simp at heq
        · cases heq
          exact Nat.pos_of_ne_zero hmark

/-- If a numbered horizontal output is not the homogeneous component and
is not internal although the parent has a vertical step, then it is exactly
the lower-mark child at mark zero. -/
theorem horizontalExpansion_external_noncomponent_markValue_eq_zero
    {r : ProvenancedRow n L data hn}
    {horizontalRows verticalRows :
      List (ℤ × ProvenancedRow n L data hn)}
    (hhorizontal : horizontalExpansion n L data hn r = some horizontalRows)
    (hvertical : verticalExpansion n L data hn r = some verticalRows)
    (q : ℤ × ProvenancedRow n L data hn) (hq : q ∈ horizontalRows)
    (hcomponent : ¬q.2.IsComponent n L data hn)
    (hexternal : ¬((horizontalExpansion n L data hn q.2).isSome ∧
      (verticalExpansion n L data hn q.2).isSome)) :
    q.2.markValue n L data hn = 0 := by
  cases r with
  | component => simp [horizontalExpansion] at hhorizontal
  | marked root context mark left right =>
      simp only [horizontalExpansion] at hhorizontal
      split at hhorizontal
      · contradiction
      · rename_i hmark
        rw [Option.some.injEq] at hhorizontal
        subst horizontalRows
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · have hvchild :
              (verticalExpansion n L data hn
                (.marked root context ⟨mark.val - 1, by omega⟩
                  left right)).isSome := by
            cases right with
            | nil => simp [verticalExpansion] at hvertical
            | cons x right => simp [verticalExpansion]
          have hhchild :
              ¬(horizontalExpansion n L data hn
                (.marked root context ⟨mark.val - 1, by omega⟩
                  left right)).isSome := by
            intro hh
            exact hexternal ⟨hh, hvchild⟩
          simp only [horizontalExpansion] at hhchild
          split at hhchild
          · rename_i hzero
            exact hzero
          · simp at hhchild
        · exfalso
          exact hcomponent (by simp [IsComponent])

/-- Every row of mark zero evaluates to zero, for both constructors. -/
theorem value_eq_zero_of_markValue_eq_zero
    (r : ProvenancedRow n L data hn)
    (hmark : r.markValue n L data hn = 0) :
    r.value = 0 := by
  cases r with
  | marked root context mark left right =>
      have hzero : mark.val = 0 := by
        simpa [markValue] using hmark
      have hmarkEq : mark = ⟨0, by omega⟩ := Fin.ext hzero
      rw [hmarkEq]
      change MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            (RelationContext.markedPrefix n L data hn context root
              ⟨0, by omega⟩) *
          MarkedRow.basisWord n L data hn right = 0
      rw [RelationContext.markedPrefix,
        rowTruncation_zero n L hn, map_zero, map_zero]
      simp
  | component root context mark left right =>
      have hzero : mark.val = 0 := by
        simpa [markValue] using hmark
      have hmarkEq : mark = ⟨0, by omega⟩ := Fin.ext hzero
      rw [hmarkEq]
      change MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            (RelationContext.component n L data hn context root
              ⟨0, by omega⟩) *
          MarkedRow.basisWord n L data hn right = 0
      rw [RelationContext.component_zero n L data hn context root
        ⟨0, by omega⟩ rfl, map_zero]
      simp

/-- A row is either still vertically processable or is in the exact
syntactic vertical normal form stated in Rule (1). -/
theorem vertical_step_or_normal
    (r : ProvenancedRow n L data hn) :
    (∃ rows, verticalExpansion n L data hn r = some rows) ∨
      r.IsVerticalNormal n L data hn := by
  cases h : verticalExpansion n L data hn r with
  | none =>
      exact Or.inr ((verticalExpansion_eq_none_iff n L data hn r).mp h)
  | some rows => exact Or.inl ⟨rows, rfl⟩

end ProvenancedRow

/-- Every literal initial row begins with an ordered PBW word. -/
theorem GlobalInitialPacketLabel.row_ordinaryNeighbors_pairwise
    (label : GlobalInitialPacketLabel n L data hn) :
    ((label.row n L data hn).ordinaryNeighbors n L data hn).Pairwise
      (· ≤ ·) := by
  simpa [GlobalInitialPacketLabel.row, ProvenancedRow.ordinaryNeighbors] using
    exponentWord_pairwise n L data hn label.exponent

/-- The initial row carries the triangular full relation named by its source
tag. -/
theorem GlobalInitialPacketLabel.row_hasRoot
    (label : GlobalInitialPacketLabel n L data hn) :
    (label.row n L data hn).HasRoot n L data hn
      (triangularRelationOfIndex n L data label.relationTag) := by
  simp [GlobalInitialPacketLabel.row, ProvenancedRow.HasRoot]

/-- The initial horizontal frame is the hole context with the relation at
the far left and the complete PBW exponent word on its right. -/
theorem GlobalInitialPacketLabel.row_hasHorizontalFrame
    (label : GlobalInitialPacketLabel n L data hn) :
    (label.row n L data hn).HasHorizontalFrame n L data hn .hole []
      (exponentWord n L data hn label.exponent) := by
  simp [GlobalInitialPacketLabel.row, ProvenancedRow.HasHorizontalFrame]

/-- Every comparison-cell input in the horizontal trace of an ordered root
still has ordered ordinary neighbours. -/
theorem LabelledComparisonCell.input_ordinaryNeighbors_pairwise_of_mem
    (root : ProvenancedRow n L data hn)
    (hroot : (root.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·))
    (path : List ℕ) (coefficient : ℤ)
    (c : LabelledComparisonCell n L data hn)
    (hc : c ∈ uncutComparisonTrace n L data hn root path coefficient) :
    (c.input.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·) := by
  rw [uncutComparisonTrace, List.mem_filterMap] at hc
  obtain ⟨cell, hcell, hcellEq⟩ := hc
  unfold comparisonCellOfHorizontal? at hcellEq
  split at hcellEq
  · contradiction
  · have hinput : c.input = cell.input := congrArg
        (fun d : LabelledComparisonCell n L data hn ↦ d.input)
        (Option.some.inj hcellEq).symm
    rw [hinput]
    exact collectorTrace_input_invariant
      (horizontalCollector n L data hn)
      (fun r ↦ (r.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·))
      (fun h hr ↦ ProvenancedRow.horizontalExpansion_ordinaryNeighbors_pairwise
        n L data hn h hr)
      root hroot path coefficient cell hcell

/-- Every comparison-cell input in a horizontal trace retains the literal
full-relation root of that trace. -/
theorem LabelledComparisonCell.input_hasRoot_of_mem
    (root : ProvenancedRow n L data hn)
    (relation : Relations n L data)
    (hroot : root.HasRoot n L data hn relation)
    (path : List ℕ) (coefficient : ℤ)
    (c : LabelledComparisonCell n L data hn)
    (hc : c ∈ uncutComparisonTrace n L data hn root path coefficient) :
    c.input.HasRoot n L data hn relation := by
  rw [uncutComparisonTrace, List.mem_filterMap] at hc
  obtain ⟨cell, hcell, hcellEq⟩ := hc
  unfold comparisonCellOfHorizontal? at hcellEq
  split at hcellEq
  · contradiction
  · have hinput : c.input = cell.input := congrArg
        (fun d : LabelledComparisonCell n L data hn ↦ d.input)
        (Option.some.inj hcellEq).symm
    rw [hinput]
    exact collectorTrace_input_invariant
      (horizontalCollector n L data hn)
      (fun r ↦ r.HasRoot n L data hn relation)
      (fun h hr ↦ ProvenancedRow.horizontalExpansion_preserves_HasRoot
        n L data hn relation h hr)
      root hroot path coefficient cell hcell

/-- The complete horizontal frame is inherited by every comparison input in
the horizontal trace. -/
theorem LabelledComparisonCell.input_hasHorizontalFrame_of_mem
    (root : ProvenancedRow n L data hn)
    (context : RelationContext n L data hn)
    (left right : List (AdaptedIndex n L data hn))
    (hroot : root.HasHorizontalFrame n L data hn context left right)
    (path : List ℕ) (coefficient : ℤ)
    (c : LabelledComparisonCell n L data hn)
    (hc : c ∈ uncutComparisonTrace n L data hn root path coefficient) :
    c.input.HasHorizontalFrame n L data hn context left right := by
  rw [uncutComparisonTrace, List.mem_filterMap] at hc
  obtain ⟨cell, hcell, hcellEq⟩ := hc
  unfold comparisonCellOfHorizontal? at hcellEq
  split at hcellEq
  · contradiction
  · have hinput : c.input = cell.input := congrArg
        (fun d : LabelledComparisonCell n L data hn ↦ d.input)
        (Option.some.inj hcellEq).symm
    rw [hinput]
    exact collectorTrace_input_invariant
      (horizontalCollector n L data hn)
      (fun r ↦ r.HasHorizontalFrame n L data hn context left right)
      (fun h hr ↦
        ProvenancedRow.horizontalExpansion_preserves_HasHorizontalFrame
          n L data hn context left right h hr)
      root hroot path coefficient cell hcell

/-- Source-labelled comparison cells inherit the ordered PBW word of their
exact initial occurrence. -/
theorem GoverningWitness.globalComparisonCell_input_pairwise
    {a : L} (w : GoverningWitness n L data a)
    (c : GoverningComparisonCell n L data hn)
    (hc : c ∈ w.globalLabelledComparisonTrace n L data hn) :
    (c.cell.input.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·) := by
  rw [GoverningWitness.globalLabelledComparisonTrace,
    List.mem_flatten] at hc
  obtain ⟨branch, hbranch, hc⟩ := hc
  rw [List.mem_ofFn] at hbranch
  obtain ⟨i, rfl⟩ := hbranch
  rw [List.mem_map] at hc
  obtain ⟨cell, hcell, rfl⟩ := hc
  exact LabelledComparisonCell.input_ordinaryNeighbors_pairwise_of_mem
    n L data hn
    ((w.globalInitialLabels n L data hn).get i).2.row
    (GlobalInitialPacketLabel.row_ordinaryNeighbors_pairwise n L data hn
      ((w.globalInitialLabels n L data hn).get i).2)
    [i.1] ((w.globalInitialLabels n L data hn).get i).1 cell hcell

/-- A source-labelled global cell retains exactly the triangular relation
root named by that source. -/
theorem GoverningWitness.globalComparisonCell_input_hasRoot
    {a : L} (w : GoverningWitness n L data a)
    (c : GoverningComparisonCell n L data hn)
    (hc : c ∈ w.globalLabelledComparisonTrace n L data hn) :
    c.cell.input.HasRoot n L data hn
      (triangularRelationOfIndex n L data c.source.relationTag) := by
  rw [GoverningWitness.globalLabelledComparisonTrace,
    List.mem_flatten] at hc
  obtain ⟨branch, hbranch, hc⟩ := hc
  rw [List.mem_ofFn] at hbranch
  obtain ⟨i, rfl⟩ := hbranch
  rw [List.mem_map] at hc
  obtain ⟨cell, hcell, rfl⟩ := hc
  exact LabelledComparisonCell.input_hasRoot_of_mem
    n L data hn
    ((w.globalInitialLabels n L data hn).get i).2.row
    (triangularRelationOfIndex n L data
      ((w.globalInitialLabels n L data hn).get i).2.relationTag)
    (GlobalInitialPacketLabel.row_hasRoot n L data hn
      ((w.globalInitialLabels n L data hn).get i).2)
    [i.1] ((w.globalInitialLabels n L data hn).get i).1 cell hcell

/-- Every numbered horizontal output of a global comparison cell has the
same triangular full-relation root as its source label. -/
theorem GoverningWitness.globalComparisonCell_horizontalOutput_hasRoot
    {a : L} (w : GoverningWitness n L data a)
    (c : GoverningComparisonCell n L data hn)
    (hc : c ∈ w.globalLabelledComparisonTrace n L data hn)
    (i : Fin c.cell.horizontalOutputs.length) :
    (c.cell.horizontalOutputs.get i).2.HasRoot n L data hn
      (triangularRelationOfIndex n L data c.source.relationTag) :=
  ProvenancedRow.horizontalExpansion_preserves_HasRoot
    n L data hn
    (triangularRelationOfIndex n L data c.source.relationTag)
    c.cell.horizontal_eq
    (w.globalComparisonCell_input_hasRoot n L data hn c hc)
    (c.cell.horizontalOutputs.get i) (List.get_mem _ i)

/-- A global comparison cell retains the exact initial hole/right-word
frame named by its source label. -/
theorem GoverningWitness.globalComparisonCell_input_hasHorizontalFrame
    {a : L} (w : GoverningWitness n L data a)
    (c : GoverningComparisonCell n L data hn)
    (hc : c ∈ w.globalLabelledComparisonTrace n L data hn) :
    c.cell.input.HasHorizontalFrame n L data hn .hole []
      (exponentWord n L data hn c.source.exponent) := by
  rw [GoverningWitness.globalLabelledComparisonTrace,
    List.mem_flatten] at hc
  obtain ⟨branch, hbranch, hc⟩ := hc
  rw [List.mem_ofFn] at hbranch
  obtain ⟨i, rfl⟩ := hbranch
  rw [List.mem_map] at hc
  obtain ⟨cell, hcell, rfl⟩ := hc
  exact LabelledComparisonCell.input_hasHorizontalFrame_of_mem
    n L data hn
    ((w.globalInitialLabels n L data hn).get i).2.row .hole []
    (exponentWord n L data hn
      ((w.globalInitialLabels n L data hn).get i).2.exponent)
    (GlobalInitialPacketLabel.row_hasHorizontalFrame n L data hn
      ((w.globalInitialLabels n L data hn).get i).2)
    [i.1] ((w.globalInitialLabels n L data hn).get i).1 cell hcell

/-- Every numbered horizontal output retains that exact frame. -/
theorem GoverningWitness.globalComparisonCell_horizontalOutput_hasHorizontalFrame
    {a : L} (w : GoverningWitness n L data a)
    (c : GoverningComparisonCell n L data hn)
    (hc : c ∈ w.globalLabelledComparisonTrace n L data hn)
    (i : Fin c.cell.horizontalOutputs.length) :
    (c.cell.horizontalOutputs.get i).2.HasHorizontalFrame
      n L data hn .hole []
        (exponentWord n L data hn c.source.exponent) :=
  ProvenancedRow.horizontalExpansion_preserves_HasHorizontalFrame
    n L data hn .hole [] (exponentWord n L data hn c.source.exponent)
    c.cell.horizontal_eq
    (w.globalComparisonCell_input_hasHorizontalFrame n L data hn c hc)
    (c.cell.horizontalOutputs.get i) (List.get_mem _ i)

namespace GoverningComparisonCell

/-- An invariant of the selected horizontal child which is stable under
vertical transfer holds for every nonzero descendant occurrence. -/
theorem horizontalSuccessorVerticalFrontier_invariant
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length)
    (I : ProvenancedRow n L data hn → Prop)
    (hpreserves : ∀ {r rows},
      verticalExpansion n L data hn r = some rows → I r →
        ∀ q ∈ rows, I q.2)
    (hchild : I (c.cell.horizontalOutputs.get i).2)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : c.horizontalSuccessorVerticalFrontier n L data hn i o ≠ 0) :
    I o.row := by
  have hs : o ∈ (c.horizontalSuccessorVerticalFrontier
      n L data hn i).support := Finsupp.mem_support_iff.mpr ho
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_apply
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at ho
  exact collectorFrontier_invariant_of_ne
    (verticalCollector n L data hn) I hpreserves
    (c.cell.horizontalOutputs.get i).2 hchild
    (i.1 :: c.cell.path)
    (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1) source ho

/-- Every vertically normalized descendant of a numbered horizontal child
retains the ordered ordinary-neighbour list of that child. -/
theorem horizontalSuccessorVerticalFrontier_pairwise
    (c : GoverningComparisonCell n L data hn)
    (hinput : (c.cell.input.ordinaryNeighbors n L data hn).Pairwise
      (· ≤ ·))
    (i : Fin c.cell.horizontalOutputs.length)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : c.horizontalSuccessorVerticalFrontier n L data hn i o ≠ 0) :
    (o.row.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·) := by
  apply c.horizontalSuccessorVerticalFrontier_invariant n L data hn i
    (fun r ↦ (r.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·))
    (fun h hr ↦ ProvenancedRow.verticalExpansion_ordinaryNeighbors_pairwise
      n L data hn h hr)
  · exact ProvenancedRow.horizontalExpansion_ordinaryNeighbors_pairwise
      n L data hn c.cell.horizontal_eq hinput
        (c.cell.horizontalOutputs.get i) (List.get_mem _ i)
  · exact ho

/-- A homogeneous horizontal child remains a component throughout its
complete vertical pass.  No homogeneous component is reclassified as a
full relation. -/
theorem horizontalSuccessorVerticalFrontier_isComponent
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : c.horizontalSuccessorVerticalFrontier n L data hn i o ≠ 0)
    (hhomogeneous : o.IsHomogeneousChild n L data hn) :
    o.row.IsComponent n L data hn := by
  have hs : o ∈ (c.horizontalSuccessorVerticalFrontier
      n L data hn i).support := Finsupp.mem_support_iff.mpr ho
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_apply
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at ho
  apply collectorFrontier_invariant_of_ne
    (verticalCollector n L data hn)
    (ProvenancedRow.IsComponent n L data hn)
    (fun h hr ↦ ProvenancedRow.verticalExpansion_preserves_isComponent
      n L data hn h hr)
    (c.cell.horizontalOutputs.get i).2
  · rcases hhomogeneous with ⟨root, context, mark, left, right, heq⟩
    change (c.cell.horizontalOutputs.get i).2 =
      .component root context mark left right at heq
    rw [heq]
    trivial
  · exact ho

/-- The positive mark of a homogeneous truncation child is retained by all
of its vertical descendants. -/
theorem horizontalSuccessorVerticalFrontier_mark_pos
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : c.horizontalSuccessorVerticalFrontier n L data hn i o ≠ 0)
    (hhomogeneous : o.IsHomogeneousChild n L data hn) :
    0 < o.row.markValue n L data hn := by
  have hs : o ∈ (c.horizontalSuccessorVerticalFrontier
      n L data hn i).support := Finsupp.mem_support_iff.mpr ho
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_apply
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at ho
  rcases hhomogeneous with ⟨root, context, mark, left, right, heq⟩
  change (c.cell.horizontalOutputs.get i).2 =
    .component root context mark left right at heq
  have hchild : 0 <
      ((c.cell.horizontalOutputs.get i).2.markValue n L data hn) := by
    rw [heq]
    apply ProvenancedRow.horizontalExpansion_component_mark_pos
      n L data hn c.cell.horizontal_eq
      (c.cell.horizontalOutputs.get i) (List.get_mem _ i)
      root context mark left right heq
  exact collectorFrontier_invariant_of_ne
    (verticalCollector n L data hn)
    (fun r ↦ 0 < r.markValue n L data hn)
    (fun {p rows} h hr q hq ↦ by
      change verticalExpansion n L data hn p = some rows at h
      change 0 < q.2.markValue n L data hn
      change 0 < p.markValue n L data hn at hr
      rw [ProvenancedRow.verticalExpansion_preserves_markValue
        n L data hn h q hq]
      exact hr)
    (c.cell.horizontalOutputs.get i).2 hchild
    (i.1 :: c.cell.path)
    (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1) source ho

/-- An external horizontal child which is not homogeneous is the zero-mark
lower child, and the mark remains zero along its vertical descendants. -/
theorem horizontalSuccessorVerticalFrontier_nonhomogeneous_mark_zero
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : c.horizontalSuccessorVerticalFrontier n L data hn i o ≠ 0)
    (hexternal : o.IsExternal n L data hn)
    (hhomogeneous : ¬o.IsHomogeneousChild n L data hn) :
    o.row.markValue n L data hn = 0 := by
  have hs : o ∈ (c.horizontalSuccessorVerticalFrontier
      n L data hn i).support := Finsupp.mem_support_iff.mpr ho
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_apply
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at ho
  have hselectedComponent :
      ¬(c.cell.horizontalOutputs.get i).2.IsComponent n L data hn := by
    intro hcomponent
    cases hrow : (c.cell.horizontalOutputs.get i).2 with
    | marked =>
        rw [hrow] at hcomponent
        exact hcomponent
    | component root context mark left right =>
        apply hhomogeneous
        change ∃ root context mark left right,
          (c.cell.horizontalOutputs.get i).2 =
            .component root context mark left right
        exact ⟨root, context, mark, left, right, hrow⟩
  have hchild :
      (c.cell.horizontalOutputs.get i).2.markValue n L data hn = 0 := by
    apply ProvenancedRow.horizontalExpansion_external_noncomponent_markValue_eq_zero
      n L data hn c.cell.horizontal_eq c.cell.vertical_eq
      (c.cell.horizontalOutputs.get i) (List.get_mem _ i) hselectedComponent
    change ¬((horizontalExpansion n L data hn
        (c.cell.horizontalOutputs.get i).2).isSome ∧
      (verticalExpansion n L data hn
        (c.cell.horizontalOutputs.get i).2).isSome) at hexternal
    exact hexternal
  exact collectorFrontier_invariant_of_ne
    (verticalCollector n L data hn)
    (fun r ↦ r.markValue n L data hn = 0)
    (fun {p rows} h hp q hq ↦ by
      change verticalExpansion n L data hn p = some rows at h
      change q.2.markValue n L data hn = 0
      rw [ProvenancedRow.verticalExpansion_preserves_markValue
        n L data hn h q hq]
      exact hp)
    (c.cell.horizontalOutputs.get i).2 hchild
    (i.1 :: c.cell.path)
    (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1) source ho

end GoverningComparisonCell

/-- A nonzero occurrence in the complete `V(HR)` ledger remembers a parent
cell which genuinely belongs to the source-labelled global trace. -/
theorem GoverningWitness.globalHorizontalVerticalOccurrence_parent_mem
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0) :
    o.parent ∈ w.globalLabelledComparisonTrace n L data hn := by
  let childFrontiers (c : GoverningComparisonCell n L data hn) :=
    List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i
  let cellFrontier (c : GoverningComparisonCell n L data hn) :=
    (childFrontiers c).sum
  rw [GoverningWitness.globalHorizontalVerticalOccurrences] at ho
  change ((w.globalLabelledComparisonTrace n L data hn).map
    cellFrontier).sum o ≠ 0 at ho
  obtain ⟨cellSum, hcellSum, hcellSumO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      ((w.globalLabelledComparisonTrace n L data hn).map cellFrontier) o ho
  rw [List.mem_map] at hcellSum
  obtain ⟨c, hc, rfl⟩ := hcellSum
  change (childFrontiers c).sum o ≠ 0 at hcellSumO
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      (childFrontiers c) o hcellSumO
  change front ∈ (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i) at hfront
  rw [List.mem_ofFn] at hfront
  obtain ⟨i, rfl⟩ := hfront
  have hs : o ∈ (c.horizontalSuccessorVerticalFrontier
      n L data hn i).support := Finsupp.mem_support_iff.mpr hfrontO
  rw [GoverningComparisonCell.horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding_injective
        n L data hn c i)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  exact hc

/-- A nonzero global occurrence has a nonzero coefficient already in the
vertical frontier indexed by its own parent and child fields.  The dependent
occurrence label prevents a different cell or child from contributing to
this same coordinate. -/
theorem GoverningWitness.globalHorizontalVerticalOccurrence_ownFrontier_ne
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0) :
    o.parent.horizontalSuccessorVerticalFrontier
      n L data hn o.childIndex o ≠ 0 := by
  let childFrontiers (c : GoverningComparisonCell n L data hn) :=
    List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i
  let cellFrontier (c : GoverningComparisonCell n L data hn) :=
    (childFrontiers c).sum
  rw [GoverningWitness.globalHorizontalVerticalOccurrences] at ho
  change ((w.globalLabelledComparisonTrace n L data hn).map
    cellFrontier).sum o ≠ 0 at ho
  obtain ⟨cellSum, hcellSum, hcellSumO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      ((w.globalLabelledComparisonTrace n L data hn).map cellFrontier) o ho
  rw [List.mem_map] at hcellSum
  obtain ⟨c, hc, rfl⟩ := hcellSum
  change (childFrontiers c).sum o ≠ 0 at hcellSumO
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      (childFrontiers c) o hcellSumO
  change front ∈ (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i) at hfront
  rw [List.mem_ofFn] at hfront
  obtain ⟨i, rfl⟩ := hfront
  have hs : o ∈ (c.horizontalSuccessorVerticalFrontier
      n L data hn i).support := Finsupp.mem_support_iff.mpr hfrontO
  rw [GoverningComparisonCell.horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding_injective
        n L data hn c i)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  exact hfrontO

/-- Every nonzero coefficient copy in the complete `V(HR)` ledger has an
ordered ordinary-neighbour list.  The statement is occurrence-level even
when equal rows later cancel algebraically. -/
theorem GoverningWitness.globalHorizontalVerticalOccurrence_pairwise_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0) :
    (o.row.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·) := by
  let childFrontiers (c : GoverningComparisonCell n L data hn) :=
    List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i
  let cellFrontier (c : GoverningComparisonCell n L data hn) :=
    (childFrontiers c).sum
  rw [GoverningWitness.globalHorizontalVerticalOccurrences] at ho
  change ((w.globalLabelledComparisonTrace n L data hn).map
    cellFrontier).sum o ≠ 0 at ho
  obtain ⟨cellSum, hcellSum, hcellSumO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      ((w.globalLabelledComparisonTrace n L data hn).map cellFrontier) o ho
  rw [List.mem_map] at hcellSum
  obtain ⟨c, hc, rfl⟩ := hcellSum
  change (childFrontiers c).sum o ≠ 0 at hcellSumO
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero (childFrontiers c) o hcellSumO
  change front ∈ (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i) at hfront
  rw [List.mem_ofFn] at hfront
  obtain ⟨i, rfl⟩ := hfront
  exact c.horizontalSuccessorVerticalFrontier_pairwise n L data hn
    (w.globalComparisonCell_input_pairwise n L data hn c hc) i o hfrontO

/-- Every nonzero occurrence below an external homogeneous truncation child
is still a component occurrence after the complete vertical pass. -/
theorem GoverningWitness.globalHorizontalVerticalOccurrence_isComponent
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0)
    (hhomogeneous : o.IsHomogeneousChild n L data hn) :
    o.row.IsComponent n L data hn := by
  let childFrontiers (c : GoverningComparisonCell n L data hn) :=
    List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i
  let cellFrontier (c : GoverningComparisonCell n L data hn) :=
    (childFrontiers c).sum
  rw [GoverningWitness.globalHorizontalVerticalOccurrences] at ho
  change ((w.globalLabelledComparisonTrace n L data hn).map
    cellFrontier).sum o ≠ 0 at ho
  obtain ⟨cellSum, hcellSum, hcellSumO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      ((w.globalLabelledComparisonTrace n L data hn).map cellFrontier) o ho
  rw [List.mem_map] at hcellSum
  obtain ⟨c, hc, rfl⟩ := hcellSum
  change (childFrontiers c).sum o ≠ 0 at hcellSumO
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero (childFrontiers c) o hcellSumO
  change front ∈ (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i) at hfront
  rw [List.mem_ofFn] at hfront
  obtain ⟨i, rfl⟩ := hfront
  exact c.horizontalSuccessorVerticalFrontier_isComponent
    n L data hn i o hfrontO hhomogeneous

/-- Every nonzero homogeneous child in the complete global ledger retains a
positive quotient-tower mark. -/
theorem GoverningWitness.globalHorizontalVerticalOccurrence_mark_pos
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0)
    (hhomogeneous : o.IsHomogeneousChild n L data hn) :
    0 < o.row.markValue n L data hn := by
  let childFrontiers (c : GoverningComparisonCell n L data hn) :=
    List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i
  let cellFrontier (c : GoverningComparisonCell n L data hn) :=
    (childFrontiers c).sum
  rw [GoverningWitness.globalHorizontalVerticalOccurrences] at ho
  change ((w.globalLabelledComparisonTrace n L data hn).map
    cellFrontier).sum o ≠ 0 at ho
  obtain ⟨cellSum, hcellSum, hcellSumO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      ((w.globalLabelledComparisonTrace n L data hn).map cellFrontier) o ho
  rw [List.mem_map] at hcellSum
  obtain ⟨c, hc, rfl⟩ := hcellSum
  change (childFrontiers c).sum o ≠ 0 at hcellSumO
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero (childFrontiers c) o hcellSumO
  change front ∈ (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i) at hfront
  rw [List.mem_ofFn] at hfront
  obtain ⟨i, rfl⟩ := hfront
  exact c.horizontalSuccessorVerticalFrontier_mark_pos
    n L data hn i o hfrontO hhomogeneous

/-- Every external nonhomogeneous horizontal descendant is literally a
zero-valued mark-zero row. -/
theorem GoverningWitness.globalExternalNonhomogeneous_value_eq_zero
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0)
    (hexternal : o.IsExternal n L data hn)
    (hhomogeneous : ¬o.IsHomogeneousChild n L data hn) :
    o.row.value = 0 := by
  let childFrontiers (c : GoverningComparisonCell n L data hn) :=
    List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i
  let cellFrontier (c : GoverningComparisonCell n L data hn) :=
    (childFrontiers c).sum
  have hmark : o.row.markValue n L data hn = 0 := by
    rw [GoverningWitness.globalHorizontalVerticalOccurrences] at ho
    change ((w.globalLabelledComparisonTrace n L data hn).map
      cellFrontier).sum o ≠ 0 at ho
    obtain ⟨cellSum, hcellSum, hcellSumO⟩ :=
      exists_finsupp_in_list_of_sum_apply_ne_zero
        ((w.globalLabelledComparisonTrace n L data hn).map cellFrontier) o ho
    rw [List.mem_map] at hcellSum
    obtain ⟨c, hc, rfl⟩ := hcellSum
    change (childFrontiers c).sum o ≠ 0 at hcellSumO
    obtain ⟨front, hfront, hfrontO⟩ :=
      exists_finsupp_in_list_of_sum_apply_ne_zero
        (childFrontiers c) o hcellSumO
    change front ∈ (List.ofFn
      fun i : Fin c.cell.horizontalOutputs.length ↦
        c.horizontalSuccessorVerticalFrontier n L data hn i) at hfront
    rw [List.mem_ofFn] at hfront
    obtain ⟨i, rfl⟩ := hfront
    exact c.horizontalSuccessorVerticalFrontier_nonhomogeneous_mark_zero
      n L data hn i o hfrontO hexternal hhomogeneous
  exact o.row.value_eq_zero_of_markValue_eq_zero n L data hn hmark

/-! ## Literal absorption of ordinary `M`-inputs

The component collector never forgets an ordinary input when it lowers the
factor number: the input is appended to the stored relation context.  The
following small relation records only the information needed by stopping
rule (4), namely the number of appended positive homogeneous inputs. -/

/-- Number of ordinary positive-homogeneous (`M`) copies in a literal list.
Equal basis indices are counted with their occurrence multiplicity. -/
noncomputable def ordinaryPieceMCount
    (xs : List (AdaptedIndex n L data hn)) : ℕ :=
  xs.countP fun x ↦ decide (0 < x.1.val)

@[simp] theorem ordinaryPieceMCount_nil :
    ordinaryPieceMCount n L data hn [] = 0 := rfl

@[simp] theorem ordinaryPieceMCount_append
    (xs ys : List (AdaptedIndex n L data hn)) :
    ordinaryPieceMCount n L data hn (xs ++ ys) =
      ordinaryPieceMCount n L data hn xs +
        ordinaryPieceMCount n L data hn ys := by
  exact List.countP_append

@[simp] theorem ordinaryPieceMCount_cons
    (x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn)) :
    ordinaryPieceMCount n L data hn (x :: xs) =
      (if 0 < x.1.val then 1 else 0) +
        ordinaryPieceMCount n L data hn xs := by
  rw [ordinaryPieceMCount, List.countP_cons]
  by_cases hx : 0 < x.1.val
  · have hxTrue : decide (0 < x.1.val) = true := by simp [hx]
    rw [hxTrue]
    simp [ordinaryPieceMCount, hx, Nat.add_comm]
  · have hxFalse : decide (0 < x.1.val) = false := by simp [hx]
    rw [hxFalse]
    simp [ordinaryPieceMCount, hx]

/-- A context obtained from `base` by a literal sequence of right-bracket
insertions, together with the number of inserted `M`-inputs. -/
inductive RelationContext.MExtension
    (base : RelationContext n L data hn) :
    RelationContext n L data hn → ℕ → Prop
  | refl : RelationContext.MExtension base base 0
  | lieRight {context : RelationContext n L data hn} {q : ℕ}
      (h : RelationContext.MExtension base context q)
      (x : AdaptedIndex n L data hn) :
      RelationContext.MExtension base (.lieRight context x)
        (q + if 0 < x.1.val then 1 else 0)

/-- Literal context extensions compose, and their absorbed occurrence counts
add. -/
theorem RelationContext.MExtension.trans
    {base middle final : RelationContext n L data hn} {q r : ℕ}
    (h₁ : RelationContext.MExtension n L data hn base middle q)
    (h₂ : RelationContext.MExtension n L data hn middle final r) :
    RelationContext.MExtension n L data hn base final (q + r) := by
  induction h₂ with
  | refl => simpa using h₁
  | @lieRight context r hcontext x ih =>
      simpa [Nat.add_assoc] using
        (RelationContext.MExtension.lieRight ih x)

/-- The absorbed `M`-occurrence count is bounded by the manuscript weight
added to the context. -/
theorem RelationContext.MExtension.count_le_weight
    {base context : RelationContext n L data hn} {q : ℕ}
    (h : RelationContext.MExtension n L data hn base context q) :
    RelationContext.weight n L data hn base + q ≤
      RelationContext.weight n L data hn context := by
  induction h with
  | refl => simp
  | @lieRight context q hcontext x ih =>
      have hx : (if 0 < x.1.val then 1 else 0) ≤
          (adaptedWeightedBasis n L data hn).weight x := by
        by_cases hpos : 0 < x.1.val
        · simp [hpos, adaptedWeightedBasis]
        · simp [hpos, adaptedWeightedBasis]
      simp only [RelationContext.weight]
      omega

/-- The corresponding occurrence invariant for the separated vertical pass.
It starts at the homogeneous horizontal child, before any ordinary factor
has been absorbed into the relation context. -/
def ProvenancedRow.ComponentMAbsorptionInvariant
    (root : Relations n L data) (mark : Fin (n + 2))
    (base : RelationContext n L data hn) (total : ℕ) :
    ProvenancedRow n L data hn → Prop
  | .component rowRoot context rowMark left right =>
      rowRoot = root ∧ rowMark = mark ∧
        ∃ q, RelationContext.MExtension n L data hn base context q ∧
          q + ordinaryPieceMCount n L data hn (left ++ right) = total
  | .marked _ _ _ _ _ => False

/-- One vertical transfer preserves the exact number and origin of absorbed
ordinary `M`-inputs. -/
theorem ProvenancedRow.verticalExpansion_preserves_ComponentMAbsorptionInvariant
    (root : Relations n L data) (mark : Fin (n + 2))
    (base : RelationContext n L data hn) (total : ℕ)
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (hexp : verticalExpansion n L data hn r = some rows)
    (hr : r.ComponentMAbsorptionInvariant n L data hn
      root mark base total) :
    ∀ z ∈ rows,
      z.2.ComponentMAbsorptionInvariant n L data hn
        root mark base total := by
  classical
  intro z hz
  cases r with
  | marked => exact hr.elim
  | component rowRoot context rowMark left right =>
      rcases hr with ⟨hroot, hmark, q, hcontext, hcount⟩
      simp only [verticalExpansion] at hexp
      split at hexp
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at hexp
        subst rows
        have hleftEq : left = leftRev.reverse ++ [x] := by
          have hrev := congrArg List.reverse hleft
          simpa using hrev
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · refine ⟨hroot, hmark, q, hcontext, ?_⟩
          simpa [hleftEq, ordinaryPieceMCount, List.countP_append,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount
        · refine ⟨hroot, hmark,
            q + (if 0 < x.1.val then 1 else 0),
            RelationContext.MExtension.lieRight hcontext x, ?_⟩
          rw [hleftEq, List.append_assoc] at hcount
          simp only [ordinaryPieceMCount_append,
            ordinaryPieceMCount_cons, ordinaryPieceMCount_nil,
            Nat.add_zero] at hcount ⊢
          omega

/-- Exact total homogeneous weight carried by a component row during the
separated vertical pass. -/
def ProvenancedRow.ComponentWeightInvariant
    (root : Relations n L data) (mark : Fin (n + 2))
    (baseWeight : ℕ) : ProvenancedRow n L data hn → Prop
  | .component rowRoot context rowMark left right =>
      rowRoot = root ∧ rowMark = mark ∧
        RelationContext.weight n L data hn context +
            (left.map (adaptedWeightedBasis n L data hn).weight).sum +
            (right.map (adaptedWeightedBasis n L data hn).weight).sum =
          baseWeight
  | .marked _ _ _ _ _ => False

theorem ProvenancedRow.verticalExpansion_preserves_ComponentWeightInvariant
    (root : Relations n L data) (mark : Fin (n + 2))
    (baseWeight : ℕ)
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (hexp : verticalExpansion n L data hn r = some rows)
    (hr : r.ComponentWeightInvariant n L data hn root mark baseWeight) :
    ∀ z ∈ rows,
      z.2.ComponentWeightInvariant n L data hn root mark baseWeight := by
  classical
  intro z hz
  cases r with
  | marked => exact hr.elim
  | component rowRoot context rowMark left right =>
      rcases hr with ⟨hroot, hmark, hweight⟩
      simp only [verticalExpansion] at hexp
      split at hexp
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at hexp
        subst rows
        have hleftEq : left = leftRev.reverse ++ [x] := by
          have hrev := congrArg List.reverse hleft
          simpa using hrev
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · refine ⟨hroot, hmark, ?_⟩
          simpa [hleftEq, List.map_append, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hweight
        · refine ⟨hroot, hmark, ?_⟩
          simp only [RelationContext.weight, List.map_append,
            List.map_singleton, List.sum_append, List.sum_singleton] at hweight ⊢
          rw [hleftEq, List.map_append, List.sum_append] at hweight
          simp only [List.map_singleton, List.sum_singleton] at hweight
          omega

/-- The exact origin ledger descends through the complete separated vertical
pass.  The statement is formulated for an explicit component presentation
so it can be applied to the origin fields stored in a source occurrence. -/
theorem GoverningWitness.globalHorizontalVerticalOccurrence_originMInvariant
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0)
    (originRoot : Relations n L data)
    (originContext : RelationContext n L data hn)
    (originMark : Fin (n + 2))
    (originLeft originRight : List (AdaptedIndex n L data hn))
    (horigin :
      (o.parent.cell.horizontalOutputs.get o.childIndex).2 =
        .component originRoot originContext originMark originLeft originRight) :
    o.row.ComponentMAbsorptionInvariant n L data hn
      originRoot originMark originContext
        (ordinaryPieceMCount n L data hn (originLeft ++ originRight)) := by
  let childFrontiers (c : GoverningComparisonCell n L data hn) :=
    List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i
  let cellFrontier (c : GoverningComparisonCell n L data hn) :=
    (childFrontiers c).sum
  rw [GoverningWitness.globalHorizontalVerticalOccurrences] at ho
  change ((w.globalLabelledComparisonTrace n L data hn).map
    cellFrontier).sum o ≠ 0 at ho
  obtain ⟨cellSum, hcellSum, hcellSumO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      ((w.globalLabelledComparisonTrace n L data hn).map cellFrontier) o ho
  rw [List.mem_map] at hcellSum
  obtain ⟨c, hc, rfl⟩ := hcellSum
  change (childFrontiers c).sum _ ≠ 0 at hcellSumO
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero (childFrontiers c) _ hcellSumO
  change front ∈ (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i) at hfront
  rw [List.mem_ofFn] at hfront
  obtain ⟨i, rfl⟩ := hfront
  have hs : o ∈ (c.horizontalSuccessorVerticalFrontier
      n L data hn i).support := Finsupp.mem_support_iff.mpr hfrontO
  rw [GoverningComparisonCell.horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding_injective
        n L data hn c i)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  simp only [GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding]
    at horigin
  apply c.horizontalSuccessorVerticalFrontier_invariant n L data hn i
    (ProvenancedRow.ComponentMAbsorptionInvariant n L data hn
      originRoot originMark originContext
        (ordinaryPieceMCount n L data hn (originLeft ++ originRight)))
    (fun hexp hinvariant ↦
      ProvenancedRow.verticalExpansion_preserves_ComponentMAbsorptionInvariant
        n L data hn originRoot originMark originContext
          (ordinaryPieceMCount n L data hn (originLeft ++ originRight))
          hexp hinvariant)
  · rw [horigin]
    refine ⟨rfl, rfl, 0, RelationContext.MExtension.refl, ?_⟩
    simp
  · exact hfrontO

/-- Global occurrence form of exact source-weight preservation. -/
theorem GoverningWitness.globalHorizontalVerticalOccurrence_originWeightInvariant
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0)
    (originRoot : Relations n L data)
    (originContext : RelationContext n L data hn)
    (originMark : Fin (n + 2))
    (originLeft originRight : List (AdaptedIndex n L data hn))
    (horigin :
      (o.parent.cell.horizontalOutputs.get o.childIndex).2 =
        .component originRoot originContext originMark originLeft originRight) :
    o.row.ComponentWeightInvariant n L data hn originRoot originMark
      (RelationContext.weight n L data hn originContext +
        (originLeft.map (adaptedWeightedBasis n L data hn).weight).sum +
        (originRight.map (adaptedWeightedBasis n L data hn).weight).sum) := by
  let childFrontiers (c : GoverningComparisonCell n L data hn) :=
    List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i
  let cellFrontier (c : GoverningComparisonCell n L data hn) :=
    (childFrontiers c).sum
  rw [GoverningWitness.globalHorizontalVerticalOccurrences] at ho
  change ((w.globalLabelledComparisonTrace n L data hn).map
    cellFrontier).sum o ≠ 0 at ho
  obtain ⟨cellSum, hcellSum, hcellSumO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      ((w.globalLabelledComparisonTrace n L data hn).map cellFrontier) o ho
  rw [List.mem_map] at hcellSum
  obtain ⟨c, hc, rfl⟩ := hcellSum
  change (childFrontiers c).sum _ ≠ 0 at hcellSumO
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero (childFrontiers c) _ hcellSumO
  change front ∈ (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i) at hfront
  rw [List.mem_ofFn] at hfront
  obtain ⟨i, rfl⟩ := hfront
  have hs : o ∈ (c.horizontalSuccessorVerticalFrontier
      n L data hn i).support := Finsupp.mem_support_iff.mpr hfrontO
  rw [GoverningComparisonCell.horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding_injective
        n L data hn c i)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  simp only [GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding]
    at horigin
  apply c.horizontalSuccessorVerticalFrontier_invariant n L data hn i
    (ProvenancedRow.ComponentWeightInvariant n L data hn originRoot originMark
      (RelationContext.weight n L data hn originContext +
        (originLeft.map (adaptedWeightedBasis n L data hn).weight).sum +
        (originRight.map (adaptedWeightedBasis n L data hn).weight).sum))
    (fun hexp hinvariant ↦
      ProvenancedRow.verticalExpansion_preserves_ComponentWeightInvariant
        n L data hn originRoot originMark _ hexp hinvariant)
  · rw [horigin]
    exact ⟨rfl, rfl, rfl⟩
  · exact hfrontO

/-- During component PBW collection, absorbed `M`-inputs plus the ordinary
`M`-inputs still displayed in the word equal the fixed source count. -/
def ComponentPBWState.MAbsorptionInvariant
    (root : Relations n L data) (mark : Fin (n + 2))
    (base : RelationContext n L data hn) (total : ℕ)
    (s : ComponentPBWState n L data hn) : Prop :=
  s.root = root ∧ s.mark = mark ∧
    ∃ q, RelationContext.MExtension n L data hn base s.context q ∧
      q + ordinaryPieceMCount n L data hn (s.left ++ s.right) = total

private theorem componentPBWBracketChildren_MAbsorptionInvariant
    (root : Relations n L data) (mark : Fin (n + 2))
    (base : RelationContext n L data hn) (total : ℕ)
    (s : ComponentPBWState n L data hn)
    (x y factor : AdaptedIndex n L data hn)
    (left right : List (AdaptedIndex n L data hn))
    (hs : s.MAbsorptionInvariant n L data hn root mark base total)
    (hremaining :
      (if 0 < factor.1.val then 1 else 0) +
          ordinaryPieceMCount n L data hn (left ++ right) =
        ordinaryPieceMCount n L data hn (s.left ++ s.right))
    (z : ℤ × ComponentPBWState n L data hn)
    (hz : z ∈ componentPBWBracketChildren n L data hn s
      (.lieRight s.context factor) x y left right) :
    z.2.MAbsorptionInvariant n L data hn root mark base total := by
  rcases hs with ⟨hroot, hmark, q, hcontext, hcount⟩
  simp only [componentPBWBracketChildren, List.mem_map] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  refine ⟨hroot, hmark, q + (if 0 < factor.1.val then 1 else 0),
    RelationContext.MExtension.lieRight hcontext factor, ?_⟩
  simp only [ComponentPBWState.left, ComponentPBWState.right,
    Nat.add_assoc]
  omega

/-- One deterministic component-PBW step preserves the exact absorbed-versus-
displayed `M` occurrence count. -/
theorem componentPBWExpansion_preserves_MAbsorptionInvariant
    (root : Relations n L data) (mark : Fin (n + 2))
    (base : RelationContext n L data hn) (total : ℕ)
    {s : ComponentPBWState n L data hn}
    {rows : List (ℤ × ComponentPBWState n L data hn)}
    (hexp : componentPBWExpansion n L data hn s = some rows)
    (hs : s.MAbsorptionInvariant n L data hn root mark base total) :
    ∀ z ∈ rows,
      z.2.MAbsorptionInvariant n L data hn root mark base total := by
  classical
  intro z hz
  unfold componentPBWExpansion at hexp
  split at hexp
  · rename_i x leftRev hleft
    have hleftEq : s.left = leftRev.reverse ++ [x] := by
      have hrev := congrArg List.reverse hleft
      simpa using hrev
    split at hexp
    · rw [Option.some.injEq] at hexp
      subst rows
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · rcases hs with ⟨hroot, hmark, q, hcontext, hcount⟩
        refine ⟨hroot, hmark, q, hcontext, ?_⟩
        simpa [ordinaryPieceMCount, hleftEq, List.countP_append,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount
      · apply componentPBWBracketChildren_MAbsorptionInvariant
          n L data hn root mark base total s x s.distinguished x
            leftRev.reverse s.right hs _ z hz
        simp only [hleftEq, ordinaryPieceMCount_append,
          ordinaryPieceMCount_cons, ordinaryPieceMCount_nil, Nat.add_zero]
        omega
    · split at hexp
      · contradiction
      · rename_i y right hright
        split at hexp
        · rw [Option.some.injEq] at hexp
          subst rows
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · rcases hs with ⟨hroot, hmark, q, hcontext, hcount⟩
            refine ⟨hroot, hmark, q, hcontext, ?_⟩
            simpa [ordinaryPieceMCount, hright, List.countP_append,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount
          · apply componentPBWBracketChildren_MAbsorptionInvariant
              n L data hn root mark base total s s.distinguished y y s.left right
                hs _ z hz
            simp only [hright, ordinaryPieceMCount_append,
              ordinaryPieceMCount_cons]
            omega
        · contradiction
  · rename_i hleft
    have hleftNil : s.left = [] := by
      have hrev := congrArg List.reverse hleft
      simpa using hrev
    split at hexp
    · contradiction
    · rename_i y right hright
      split at hexp
      · rw [Option.some.injEq] at hexp
        subst rows
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · rcases hs with ⟨hroot, hmark, q, hcontext, hcount⟩
          refine ⟨hroot, hmark, q, hcontext, ?_⟩
          simpa [ordinaryPieceMCount, hleftNil, hright,
            List.countP_append, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hcount
        · apply componentPBWBracketChildren_MAbsorptionInvariant
            n L data hn root mark base total s s.distinguished y y s.left right
              hs _ z hz
          simp only [hleftNil, hright, ordinaryPieceMCount_append,
            ordinaryPieceMCount_cons, ordinaryPieceMCount_nil,
            zero_add]
      · contradiction

private theorem global_lie_mem_derived (x y : FreeModel n L) :
    ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  have hone : ⁅x, y⁆ ∈ lowerCentralSeries ℤ (FreeModel n L) 1 := by
    rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp) (by simp)
  simpa [LieAlgebra.derivedSeries_def,
    LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero,
    lowerCentralSeries, LieModule.lowerCentralSeries_succ,
    LieSubmodule.lie_comm] using hone

private theorem global_adaptedBasis_mem_derived_of_piece_pos
    (i : AdaptedIndex n L data hn) (hi : 0 < i.1.val) :
    adaptedBasis n L data hn i ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  have hweight := FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
    (generatorBasis L) i.1.val i.1.isLt
      (pieceAdaptedBasis n L data hn i.1 i.2)
  have hone : adaptedBasis n L data hn i ∈
      lowerCentralSeries ℤ (FreeModel n L) 1 := by
    rw [adaptedBasis_apply]
    exact LieModule.antitone_lowerCentralSeries ℤ
      (FreeModel n L) (FreeModel n L) (by omega) hweight
  simpa [LieAlgebra.derivedSeries_def,
    LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero,
    lowerCentralSeries, LieModule.lowerCentralSeries_succ,
    LieSubmodule.lie_comm] using hone

private theorem global_mem_derived_of_mem_tail_one
    (d : FreeModel n L)
    (hd : d ∈ FreeMetabelian.Free.tail
      (X := Generator L) (c := n + 1) 1) :
    d ∈ LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  have hone : d ∈ lowerCentralSeries ℤ (FreeModel n L) 1 := by
    rw [← FreeMetabelian.Free.sum_incl_project d]
    apply Submodule.sum_mem
    intro i hi
    by_cases hi0 : i.val < 1
    · rw [FreeMetabelian.Free.project_apply, hd i hi0, map_zero]
      exact Submodule.zero_mem _
    · exact LieModule.antitone_lowerCentralSeries ℤ
        (FreeModel n L) (FreeModel n L) (by omega)
          (FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
            (generatorBasis L) i.val i.isLt
            (FreeMetabelian.Free.project i d))
  simpa [LieAlgebra.derivedSeries_def,
    LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero,
    lowerCentralSeries, LieModule.lowerCentralSeries_succ,
    LieSubmodule.lie_comm] using hone

/-- Context-level version of the source support lemma: a positive component
whose active manuscript weight is at least two lies in `M = F_{≥2}`. -/
theorem RelationContext.component_mem_tail_one_of_activeWeight_ge_two
    (context : RelationContext n L data hn)
    (root : Relations n L data) (mark : Fin (n + 2))
    (hmark : 0 < mark.val)
    (hactive : 2 ≤ mark.val +
      RelationContext.weight n L data hn context) :
    RelationContext.component n L data hn context root mark ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) 1 := by
  rw [FreeMetabelian.Free.mem_tail_iff]
  intro i hi
  apply RelationContext.component_apply_eq_zero_of_ne
    n L data hn context root mark hmark
  omega

theorem RelationContext.component_mem_derived_of_activeWeight_ge_two
    (context : RelationContext n L data hn)
    (root : Relations n L data) (mark : Fin (n + 2))
    (hmark : 0 < mark.val)
    (hactive : 2 ≤ mark.val +
      RelationContext.weight n L data hn context) :
    RelationContext.component n L data hn context root mark ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 :=
  global_mem_derived_of_mem_tail_one n L _
    (RelationContext.component_mem_tail_one_of_activeWeight_ge_two
      n L data hn context root mark hmark hactive)

private theorem global_derived_lie_adaptedBasis_mem_derived
    (d : FreeModel n L)
    (hd : d ∈ LieAlgebra.derivedSeries ℤ (FreeModel n L) 1)
    (i : AdaptedIndex n L data hn) :
    ⁅d, adaptedBasis n L data hn i⁆ ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  rw [← lie_skew]
  exact (LieAlgebra.derivedSeries ℤ (FreeModel n L) 1).neg_mem
    ((LieAlgebra.derivedSeries ℤ (FreeModel n L) 1).lie_mem hd)

/-- Once an arbitrary contextual component has absorbed one ordinary
`M`-input, it lies in the derived ideal. -/
theorem RelationContext.component_mem_derived_of_MExtension_of_one_le
    (base context : RelationContext n L data hn) (q : ℕ)
    (hcontext : RelationContext.MExtension n L data hn base context q)
    (root : Relations n L data) (mark : Fin (n + 2))
    (hq : 1 ≤ q) :
    RelationContext.component n L data hn context root mark ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  induction hcontext with
  | refl => omega
  | @lieRight context q hcontext x ih =>
      rw [RelationContext.component_lieRight]
      by_cases hx : 0 < x.1.val
      · exact global_lie_mem_derived n L
          (RelationContext.component n L data hn context root mark)
          ((adaptedWeightedBasis n L data hn).basis x)
      · apply global_derived_lie_adaptedBasis_mem_derived n L data hn
        · apply ih
          simp [hx] at hq
          exact hq

/-- Appending arbitrary homogeneous inputs to a component already in the
derived ideal keeps it in the derived ideal. -/
theorem RelationContext.component_mem_derived_of_MExtension_of_base_derived
    (base context : RelationContext n L data hn) (q : ℕ)
    (hcontext : RelationContext.MExtension n L data hn base context q)
    (root : Relations n L data) (mark : Fin (n + 2))
    (hbase : RelationContext.component n L data hn base root mark ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1) :
    RelationContext.component n L data hn context root mark ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  induction hcontext with
  | refl => exact hbase
  | @lieRight context q hcontext x ih =>
      rw [RelationContext.component_lieRight]
      exact global_derived_lie_adaptedBasis_mem_derived
        n L data hn _ ih x

/-- A component already in `M` is killed after one additional absorbed
ordinary `M`-input. -/
theorem RelationContext.component_eq_zero_of_MExtension_of_base_derived
    (base context : RelationContext n L data hn) (q : ℕ)
    (hcontext : RelationContext.MExtension n L data hn base context q)
    (root : Relations n L data) (mark : Fin (n + 2))
    (hbase : RelationContext.component n L data hn base root mark ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1)
    (hq : 1 ≤ q) :
    RelationContext.component n L data hn context root mark = 0 := by
  induction hcontext with
  | refl => omega
  | @lieRight context q hcontext x ih =>
      rw [RelationContext.component_lieRight]
      by_cases hx : 0 < x.1.val
      · exact IsMetabelian.bracket_eq_zero
          (FreeMetabelian.Free.isMetabelian
            (X := Generator L) (c := n + 1))
          (RelationContext.component_mem_derived_of_MExtension_of_base_derived
            n L data hn base context q hcontext root mark hbase)
          (by
            change adaptedBasis n L data hn x ∈ _
            exact global_adaptedBasis_mem_derived_of_piece_pos
              n L data hn x hx)
      · have hprev : 1 ≤ q := by
          simp [hx] at hq
          exact hq
        rw [ih hprev, zero_lie]

/-- Two absorbed ordinary `M`-inputs kill a contextual component even when
the base component has manuscript weight one. -/
theorem RelationContext.component_eq_zero_of_MExtension_of_two_le
    (base context : RelationContext n L data hn) (q : ℕ)
    (hcontext : RelationContext.MExtension n L data hn base context q)
    (root : Relations n L data) (mark : Fin (n + 2))
    (hq : 2 ≤ q) :
    RelationContext.component n L data hn context root mark = 0 := by
  induction hcontext with
  | refl => omega
  | @lieRight context q hcontext x ih =>
      rw [RelationContext.component_lieRight]
      by_cases hx : 0 < x.1.val
      · have hprev : 1 ≤ q := by
          simp [hx] at hq
          omega
        exact IsMetabelian.bracket_eq_zero
          (FreeMetabelian.Free.isMetabelian
            (X := Generator L) (c := n + 1))
          (RelationContext.component_mem_derived_of_MExtension_of_one_le
            n L data hn base context q hcontext root mark hprev)
          (by
            change adaptedBasis n L data hn x ∈ _
            exact global_adaptedBasis_mem_derived_of_piece_pos
              n L data hn x hx)
      · have hprev : 2 ≤ q := by
          simp [hx] at hq
          exact hq
        rw [ih hprev, zero_lie]

/-- The data displayed by a component row.  This small record lets us retain
the horizontal source constructor without eliminating a propositional
existential into the occurrence structure. -/
structure ComponentRowData where
  root : Relations n L data
  context : RelationContext n L data hn
  mark : Fin (n + 2)
  left : List (AdaptedIndex n L data hn)
  right : List (AdaptedIndex n L data hn)

namespace ComponentRowData

def row (d : ComponentRowData n L data hn) :
    ProvenancedRow n L data hn :=
  .component d.root d.context d.mark d.left d.right

end ComponentRowData

/-- One nonzero external homogeneous child, with its component constructor
opened but its full relation ancestry retained.  The proof fields certify
that this is an actual coefficient copy of the global ledger. -/
structure GoverningComponentSource {a : L}
    (w : GoverningWitness n L data a) where
  occurrence : CellHorizontalVerticalOccurrence n L data hn
  coefficient_ne :
    w.globalHorizontalVerticalOccurrences n L data hn occurrence ≠ 0
  external : occurrence.IsExternal n L data hn
  homogeneous : occurrence.IsHomogeneousChild n L data hn
  /-- The homogeneous horizontal child before the complete vertical pass.
  These fields are deliberately retained separately from the terminal row:
  a vertical correction may absorb an ordinary input into the context. -/
  originRoot : Relations n L data
  originContext : RelationContext n L data hn
  originMark : Fin (n + 2)
  originLeft : List (AdaptedIndex n L data hn)
  originRight : List (AdaptedIndex n L data hn)
  originRow_eq :
    (occurrence.parent.cell.horizontalOutputs.get occurrence.childIndex).2 =
      .component originRoot originContext originMark originLeft originRight
  root : Relations n L data
  context : RelationContext n L data hn
  mark : Fin (n + 2)
  mark_pos : 0 < mark.val
  left : List (AdaptedIndex n L data hn)
  right : List (AdaptedIndex n L data hn)
  row_eq : occurrence.row = .component root context mark left right
  ordinary_pairwise : (left ++ right).Pairwise (· ≤ ·)

noncomputable instance {a : L} (w : GoverningWitness n L data a) :
    DecidableEq (GoverningComponentSource n L data hn w) :=
  Classical.decEq _

/-- Open one supported external homogeneous occurrence as a genuine
component source. -/
def GoverningWitness.componentSource?
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0) :
    Option (GoverningComponentSource n L data hn w) := by
  classical
  by_cases hext : o.IsExternal n L data hn
  · by_cases hhom : o.IsHomogeneousChild n L data hn
    · have horiginExists : ∃ d : ComponentRowData n L data hn,
          (o.parent.cell.horizontalOutputs.get o.childIndex).2 = d.row := by
        rcases hhom with ⟨root, context, mark, left, right, hrow⟩
        exact ⟨⟨root, context, mark, left, right⟩, hrow⟩
      let origin := Classical.choose horiginExists
      have horigin :
          (o.parent.cell.horizontalOutputs.get o.childIndex).2 = origin.row :=
        Classical.choose_spec horiginExists
      have hhom' : o.IsHomogeneousChild n L data hn :=
        ⟨origin.root, origin.context, origin.mark,
          origin.left, origin.right, horigin⟩
      have hcomponent :=
        w.globalHorizontalVerticalOccurrence_isComponent
          n L data hn o ho hhom'
      cases hrow : o.row with
      | marked root context mark left right =>
          simp [ProvenancedRow.IsComponent, hrow] at hcomponent
      | component root context mark left right =>
          exact some
            { occurrence := o
              coefficient_ne := ho
              external := hext
              homogeneous := hhom'
              originRoot := origin.root
              originContext := origin.context
              originMark := origin.mark
              originLeft := origin.left
              originRight := origin.right
              originRow_eq := horigin
              root := root
              context := context
              mark := mark
              mark_pos := by
                have hp :=
                  w.globalHorizontalVerticalOccurrence_mark_pos
                    n L data hn o ho hhom
                simpa [ProvenancedRow.markValue, hrow] using hp
              left := left
              right := right
              row_eq := hrow
              ordinary_pairwise := by
                have hp :=
                  w.globalHorizontalVerticalOccurrence_pairwise_of_ne
                    n L data hn o ho
                simpa [ProvenancedRow.ordinaryNeighbors, hrow] using hp }
    · exact none
  · exact none

/-- Literal list of all nonzero external homogeneous component sources.
It is formed from the support before any component PBW descendants are
combined. -/
def GoverningWitness.globalComponentSources
    {a : L} (w : GoverningWitness n L data a) :
    List (GoverningComponentSource n L data hn w) :=
  (w.globalHorizontalVerticalOccurrences n L data hn).support.attach.toList.filterMap
    fun o ↦ w.componentSource? n L data hn o.1
      (Finsupp.mem_support_iff.mp o.2)

namespace GoverningComponentSource

/-- Vertical terminality places every external homogeneous component at the
left edge, exactly as in the manuscript's terminal-source convention. -/
theorem left_eq_nil
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.left = [] := by
  have hterminal :=
    w.globalHorizontalVerticalOccurrence_terminal_of_ne
      n L data hn s.occurrence s.coefficient_ne
  have hnormal :=
    (ProvenancedRow.verticalExpansion_eq_none_iff
      n L data hn s.occurrence.row).mp hterminal
  rw [s.row_eq] at hnormal
  simpa [ProvenancedRow.IsVerticalNormal] using hnormal

/-- Integer coefficient of this exact external source occurrence. -/
def coefficient {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : ℤ :=
  w.globalHorizontalVerticalOccurrences n L data hn s.occurrence

/-- The exact homogeneous component expanded at this source. -/
def component {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : FreeModel n L :=
  RelationContext.component n L data hn s.context s.root s.mark

/-- The homogeneous source has not merely retained some relation root: it is
exactly the tagged triangular relation from its initial occurrence.  This is
the ancestry datum needed by the manuscript's Smith-head replacement. -/
theorem originRoot_eq_triangularRelation
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.originRoot = triangularRelationOfIndex n L data
      s.occurrence.parent.source.relationTag := by
  have hroot := w.globalComparisonCell_horizontalOutput_hasRoot
    n L data hn s.occurrence.parent
      (w.globalHorizontalVerticalOccurrence_parent_mem
        n L data hn s.occurrence s.coefficient_ne)
      s.occurrence.childIndex
  rw [s.originRow_eq] at hroot
  simpa [ProvenancedRow.HasRoot] using hroot

/-- The horizontal ancestry also identifies the exact frame of the
homogeneous source: no context or left factor has yet been introduced, and
the complete initial exponent word remains on the right. -/
theorem originHorizontalFrame
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.originContext = .hole ∧ s.originLeft = [] ∧
      s.originRight = exponentWord n L data hn
        s.occurrence.parent.source.exponent := by
  have hframe := w.globalComparisonCell_horizontalOutput_hasHorizontalFrame
    n L data hn s.occurrence.parent
      (w.globalHorizontalVerticalOccurrence_parent_mem
        n L data hn s.occurrence s.coefficient_ne)
      s.occurrence.childIndex
  rw [s.originRow_eq] at hframe
  simpa [ProvenancedRow.HasHorizontalFrame] using hframe

/-- Because the source component has no left factor, its separated vertical
pass is already terminal.  Hence the supported terminal occurrence is
literally the homogeneous child, not merely an equal evaluated sum. -/
theorem occurrence_row_eq_originRow
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.occurrence.row =
      (s.occurrence.parent.cell.horizontalOutputs.get
        s.occurrence.childIndex).2 := by
  have hleft := (s.originHorizontalFrame n L data hn).2.1
  have hnone : verticalExpansion n L data hn
      (s.occurrence.parent.cell.horizontalOutputs.get
        s.occurrence.childIndex).2 = none := by
    rw [s.originRow_eq, hleft]
    simp [verticalExpansion]
  have hfront := w.globalHorizontalVerticalOccurrence_ownFrontier_ne
    n L data hn s.occurrence s.coefficient_ne
  have hs : s.occurrence ∈
      (s.occurrence.parent.horizontalSuccessorVerticalFrontier
        n L data hn s.occurrence.childIndex).support :=
    Finsupp.mem_support_iff.mpr hfront
  rw [GoverningComparisonCell.horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding_injective
        n L data hn s.occurrence.parent s.occurrence.childIndex),
    collectorFrontier_eq_of_expansion_none
      (verticalCollector n L data hn)
      (s.occurrence.parent.cell.horizontalOutputs.get
        s.occurrence.childIndex).2
      (s.occurrence.childIndex.1 :: s.occurrence.parent.cell.path)
      (s.occurrence.parent.cell.coefficient *
        (s.occurrence.parent.cell.horizontalOutputs.get
          s.occurrence.childIndex).1) hnone] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  have hsourceValue := Finsupp.mem_support_iff.mp hsource
  have hpairEq :
      (s.occurrence.childIndex.1 :: s.occurrence.parent.cell.path,
        (s.occurrence.parent.cell.horizontalOutputs.get
      s.occurrence.childIndex).2) = source := by
    by_contra hne
    simp [Finsupp.single_apply] at hsourceValue
    exact hne hsourceValue.1
  have hsourceRow : source.2 =
      (s.occurrence.parent.cell.horizontalOutputs.get
        s.occurrence.childIndex).2 :=
    (congrArg Prod.snd hpairEq).symm
  have hrow := congrArg
    (fun o : CellHorizontalVerticalOccurrence n L data hn ↦ o.row)
      hsourceEq
  symm
  simpa [GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding,
    hsourceRow] using hrow

/-- Opened constructor form of the preceding literal equality. -/
theorem terminal_eq_origin
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.root = s.originRoot ∧ s.context = s.originContext ∧
      s.mark = s.originMark ∧ s.left = s.originLeft ∧
        s.right = s.originRight := by
  have hrow :
      ProvenancedRow.component s.root s.context s.mark s.left s.right =
        ProvenancedRow.component s.originRoot s.originContext s.originMark
          s.originLeft s.originRight :=
    s.row_eq.symm.trans
      ((s.occurrence_row_eq_originRow n L data hn).trans s.originRow_eq)
  injection hrow with hroot hcontext hmark hleft hright
  exact ⟨hroot, hcontext, hmark, hleft, hright⟩

/-- The complete vertical pass relates the terminal component row to the
actual homogeneous child from which it started.  In particular, ordinary
`M`-inputs absorbed before the independent PBW pass remain counted at their
original source. -/
theorem originMInvariant
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.occurrence.row.ComponentMAbsorptionInvariant n L data hn
      s.originRoot s.originMark s.originContext
        (ordinaryPieceMCount n L data hn
          (s.originLeft ++ s.originRight)) :=
  w.globalHorizontalVerticalOccurrence_originMInvariant
    n L data hn s.occurrence s.coefficient_ne
      s.originRoot s.originContext s.originMark
      s.originLeft s.originRight s.originRow_eq

/-- Opened form of `originMInvariant` at the terminal component row. -/
theorem terminal_eq_origin_extension
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.root = s.originRoot ∧ s.mark = s.originMark ∧
      ∃ q, RelationContext.MExtension n L data hn
          s.originContext s.context q ∧
        q + ordinaryPieceMCount n L data hn (s.left ++ s.right) =
          ordinaryPieceMCount n L data hn
            (s.originLeft ++ s.originRight) := by
  have h := s.originMInvariant n L data hn
  rw [s.row_eq] at h
  exact h

/-- Exact source-weight preservation, opened at the terminal vertical row. -/
theorem terminalWeight_eq_originWeight
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    RelationContext.weight n L data hn s.context +
          (s.left.map (adaptedWeightedBasis n L data hn).weight).sum +
          (s.right.map (adaptedWeightedBasis n L data hn).weight).sum =
      RelationContext.weight n L data hn s.originContext +
          (s.originLeft.map (adaptedWeightedBasis n L data hn).weight).sum +
          (s.originRight.map (adaptedWeightedBasis n L data hn).weight).sum := by
  have h := w.globalHorizontalVerticalOccurrence_originWeightInvariant
    n L data hn s.occurrence s.coefficient_ne
      s.originRoot s.originContext s.originMark
      s.originLeft s.originRight s.originRow_eq
  rw [s.row_eq] at h
  exact h.2.2

/-- Initial component-PBW state belonging to one fixed basis coordinate.
Both ordinary neighbour lists are retained literally. -/
def coordinateState {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (i : AdaptedIndex n L data hn) : ComponentPBWState n L data hn :=
  { root := s.root
    context := s.context
    mark := s.mark
    distinguished := i
    left := s.left
    right := s.right }

end GoverningComponentSource

/-- One path-labelled terminal state of the independent component PBW pass.
The source occurrence and initial basis coordinate remain separate fields. -/
structure GoverningComponentPBWOccurrence {a : L}
    (w : GoverningWitness n L data a) where
  source : GoverningComponentSource n L data hn w
  coordinate : AdaptedIndex n L data hn
  path : List ℕ
  state : ComponentPBWState n L data hn

noncomputable instance {a : L} (w : GoverningWitness n L data a) :
    DecidableEq (GoverningComponentPBWOccurrence n L data hn w) :=
  Classical.decEq _

namespace GoverningComponentSource

/-- Embed the collector route below one source and one initial basis
coordinate. -/
def pbwOccurrenceEmbedding
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (i : AdaptedIndex n L data hn)
    (o : CollectorOccurrence (ComponentPBWState n L data hn)) :
    GoverningComponentPBWOccurrence n L data hn w :=
  { source := s, coordinate := i, path := o.1, state := o.2 }

theorem pbwOccurrenceEmbedding_injective
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (i : AdaptedIndex n L data hn) :
    Function.Injective (s.pbwOccurrenceEmbedding n L data hn i) := by
  intro x y h
  cases x with
  | mk xp xs =>
    cases y with
    | mk yp ys =>
      have hpath : xp = yp := congrArg
        (fun z : GoverningComponentPBWOccurrence n L data hn w ↦ z.path) h
      have hstate : xs = ys := congrArg
        (fun z : GoverningComponentPBWOccurrence n L data hn w ↦ z.state) h
      subst yp
      subst ys
      rfl

/-- Path-labelled PBW frontier below one initial basis coordinate. -/
def coordinatePBWFrontier
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (i : AdaptedIndex n L data hn) :
    GoverningComponentPBWOccurrence n L data hn w →₀ ℤ :=
  Finsupp.mapDomain (s.pbwOccurrenceEmbedding n L data hn i)
    (collectorFrontier (componentPBWCollector n L data hn)
      (s.coordinateState n L data hn i) []
      (s.coefficient n L data hn *
        ((adaptedBasis n L data hn).repr (s.component n L data hn)) i))

/-- Expanding the distinguished component in the adapted basis recovers the
literal source word, with both ordinary neighbour lists unchanged. -/
theorem coordinateState_sum_value
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    ((adaptedBasis n L data hn).repr (s.component n L data hn)).sum
        (fun i z ↦ z • (s.coordinateState n L data hn i).value
          n L data hn) = s.occurrence.row.value := by
  classical
  let contextMap : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    { toFun := fun z ↦ MarkedRow.basisWord n L data hn s.left *
          UniversalEnvelopingAlgebra.ι ℤ z *
          MarkedRow.basisWord n L data hn s.right
      map_add' := by intro x y; rw [map_add, mul_add, add_mul]
      map_smul' := by
        intro z x
        rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
        rfl }
  have hcoordinates := congrArg contextMap
    ((adaptedBasis n L data hn).linearCombination_repr
      (s.component n L data hn))
  change contextMap
      (((adaptedBasis n L data hn).repr (s.component n L data hn)).sum
        (fun i z ↦ z • adaptedBasis n L data hn i)) =
    contextMap (s.component n L data hn) at hcoordinates
  rw [map_finsuppSum] at hcoordinates
  rw [s.row_eq]
  simpa [coordinateState, ComponentPBWState.value,
    ProvenancedRow.value, component, contextMap, map_zsmul] using hcoordinates

/-- Complete occurrence-preserving PBW frontier of one component source. -/
def componentPBWFrontier
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    GoverningComponentPBWOccurrence n L data hn w →₀ ℤ :=
  ((adaptedBasis n L data hn).repr (s.component n L data hn)).sum
    fun i _ ↦ s.coordinatePBWFrontier n L data hn i

/-- Every supported descendant retains the exact source root, mark, context
extension, and literal number of absorbed ordinary `M`-inputs. -/
theorem componentPBWFrontier_MAbsorptionInvariant_of_ne
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (o : GoverningComponentPBWOccurrence n L data hn w)
    (ho : s.componentPBWFrontier n L data hn o ≠ 0) :
    o.state.MAbsorptionInvariant n L data hn
      o.source.root o.source.mark o.source.context
      (ordinaryPieceMCount n L data hn
        (o.source.left ++ o.source.right)) := by
  classical
  rw [componentPBWFrontier, Finsupp.sum_apply] at ho
  have hexists : ∃ i ∈
      ((adaptedBasis n L data hn).repr (s.component n L data hn)).support,
      s.coordinatePBWFrontier n L data hn i o ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ho (Finset.sum_eq_zero (fun i hi ↦ hall i hi))
  obtain ⟨i, hi, hio⟩ := hexists
  have hsupp : o ∈ (s.coordinatePBWFrontier n L data hn i).support :=
    Finsupp.mem_support_iff.mpr hio
  rw [coordinatePBWFrontier,
    Finsupp.mapDomain_support_of_injective
      (s.pbwOccurrenceEmbedding_injective n L data hn i)] at hsupp
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hsupp
  subst o
  rw [coordinatePBWFrontier,
    Finsupp.mapDomain_apply
      (s.pbwOccurrenceEmbedding_injective n L data hn i)] at hio
  exact collectorFrontier_invariant_of_ne
    (componentPBWCollector n L data hn)
    (ComponentPBWState.MAbsorptionInvariant n L data hn
      s.root s.mark s.context
      (ordinaryPieceMCount n L data hn (s.left ++ s.right)))
    (fun hexp hinvariant ↦
      componentPBWExpansion_preserves_MAbsorptionInvariant
        n L data hn s.root s.mark s.context
          (ordinaryPieceMCount n L data hn (s.left ++ s.right))
          hexp hinvariant)
    (s.coordinateState n L data hn i)
    (by
      refine ⟨rfl, rfl, 0, RelationContext.MExtension.refl, ?_⟩
      simp [coordinateState])
    []
    (s.coefficient n L data hn *
      ((adaptedBasis n L data hn).repr (s.component n L data hn)) i)
    source hio

/-- A source frontier never changes its source label. -/
theorem componentPBWFrontier_source_eq_of_ne
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (o : GoverningComponentPBWOccurrence n L data hn w)
    (ho : s.componentPBWFrontier n L data hn o ≠ 0) :
    o.source = s := by
  classical
  rw [componentPBWFrontier, Finsupp.sum_apply] at ho
  have hexists : ∃ i ∈
      ((adaptedBasis n L data hn).repr (s.component n L data hn)).support,
      s.coordinatePBWFrontier n L data hn i o ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ho (Finset.sum_eq_zero (fun i hi ↦ hall i hi))
  obtain ⟨i, hi, hio⟩ := hexists
  have hsupp : o ∈ (s.coordinatePBWFrontier n L data hn i).support :=
    Finsupp.mem_support_iff.mpr hio
  rw [coordinatePBWFrontier,
    Finsupp.mapDomain_support_of_injective
      (s.pbwOccurrenceEmbedding_injective n L data hn i)] at hsupp
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hsupp
  subst o
  rfl

/-- Complete component PBW normalization preserves the exact coefficient-
weighted value of one source occurrence. -/
theorem evaluate_componentPBWFrontier
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    (s.componentPBWFrontier n L data hn).sum
        (fun o z ↦ z • o.state.value n L data hn) =
      s.coefficient n L data hn • s.occurrence.row.value := by
  classical
  rw [componentPBWFrontier, Finsupp.sum_sum_index
    (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  calc
    _ = ((adaptedBasis n L data hn).repr
          (s.component n L data hn)).sum (fun i z ↦
        (s.coordinatePBWFrontier n L data hn i).sum
          (fun o c ↦ c • o.state.value n L data hn)) := by
      apply Finsupp.sum_congr
      intro i hi
      rfl
    _ = ((adaptedBasis n L data hn).repr
          (s.component n L data hn)).sum (fun i z ↦
        (s.coefficient n L data hn * z) •
          (s.coordinateState n L data hn i).value n L data hn) := by
      apply Finsupp.sum_congr
      intro i hi
      rw [coordinatePBWFrontier,
        Finsupp.sum_mapDomain_index_inj
          (s.pbwOccurrenceEmbedding_injective n L data hn i)]
      exact evaluate_collectorFrontier
        (componentPBWCollector n L data hn)
        (s.coordinateState n L data hn i) []
        (s.coefficient n L data hn *
          ((adaptedBasis n L data hn).repr
            (s.component n L data hn)) i)
    _ = s.coefficient n L data hn •
          ((adaptedBasis n L data hn).repr
            (s.component n L data hn)).sum (fun i z ↦
              z • (s.coordinateState n L data hn i).value n L data hn) := by
      rw [Finsupp.smul_sum]
      apply Finsupp.sum_congr
      intro i hi
      rw [mul_smul]
    _ = _ := by rw [s.coordinateState_sum_value n L data hn]

/-- Complete one-factor read of one grouped component source. -/
def componentPBWPrimitive
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : FreeModel n L :=
  (s.componentPBWFrontier n L data hn).sum fun o z ↦
    z • pbwPrimitive n L data hn (o.state.value n L data hn)

/-- PBW collection preserves the grouped source primitive, including its
integer occurrence coefficient. -/
theorem componentPBWPrimitive_eq_coefficient_smul
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.componentPBWPrimitive n L data hn =
      s.coefficient n L data hn •
        pbwPrimitive n L data hn s.occurrence.row.value := by
  have h := congrArg (pbwPrimitive n L data hn)
    (s.evaluate_componentPBWFrontier n L data hn)
  rw [map_finsuppSum, map_zsmul] at h
  simpa only [GoverningComponentSource.componentPBWPrimitive,
    map_zsmul] using h

/-- Every nonzero terminal occurrence of a source PBW frontier is terminal
for the independent component collector. -/
theorem componentPBWFrontier_terminal_of_ne
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (o : GoverningComponentPBWOccurrence n L data hn w)
    (ho : s.componentPBWFrontier n L data hn o ≠ 0) :
    componentPBWExpansion n L data hn o.state = none := by
  classical
  rw [componentPBWFrontier, Finsupp.sum_apply] at ho
  have hexists : ∃ i ∈
      ((adaptedBasis n L data hn).repr (s.component n L data hn)).support,
      s.coordinatePBWFrontier n L data hn i o ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ho (Finset.sum_eq_zero (fun i hi ↦ hall i hi))
  obtain ⟨i, hi, hio⟩ := hexists
  have hsupp : o ∈ (s.coordinatePBWFrontier n L data hn i).support :=
    Finsupp.mem_support_iff.mpr hio
  rw [coordinatePBWFrontier,
    Finsupp.mapDomain_support_of_injective
      (s.pbwOccurrenceEmbedding_injective n L data hn i)] at hsupp
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hsupp
  subst o
  rw [coordinatePBWFrontier,
    Finsupp.mapDomain_apply
      (s.pbwOccurrenceEmbedding_injective n L data hn i)] at hio
  exact collectorFrontier_terminal_of_ne
    (componentPBWCollector n L data hn)
    (s.coordinateState n L data hn i) []
    (s.coefficient n L data hn *
      ((adaptedBasis n L data hn).repr (s.component n L data hn)) i)
    source hio

/-- Every terminal state of the occurrence-preserving component PBW pass is
in the fixed ordered adapted basis.  This is Rule (4)'s integral Hall/PBW
normal form before the one-factor read. -/
theorem componentPBWFrontier_word_pairwise_of_ne
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (o : GoverningComponentPBWOccurrence n L data hn w)
    (ho : s.componentPBWFrontier n L data hn o ≠ 0) :
    (o.state.word n L data hn).Pairwise (· ≤ ·) := by
  classical
  rw [componentPBWFrontier, Finsupp.sum_apply] at ho
  have hexists : ∃ i ∈
      ((adaptedBasis n L data hn).repr (s.component n L data hn)).support,
      s.coordinatePBWFrontier n L data hn i o ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ho (Finset.sum_eq_zero (fun i hi ↦ hall i hi))
  obtain ⟨i, hi, hio⟩ := hexists
  have hsupp : o ∈ (s.coordinatePBWFrontier n L data hn i).support :=
    Finsupp.mem_support_iff.mpr hio
  rw [coordinatePBWFrontier,
    Finsupp.mapDomain_support_of_injective
      (s.pbwOccurrenceEmbedding_injective n L data hn i)] at hsupp
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hsupp
  subst o
  rw [coordinatePBWFrontier,
    Finsupp.mapDomain_apply
      (s.pbwOccurrenceEmbedding_injective n L data hn i)] at hio
  have hneighbors :
      (source.2.left ++ source.2.right).Pairwise (· ≤ ·) :=
    collectorFrontier_invariant_of_ne
      (componentPBWCollector n L data hn)
      (fun state ↦ (state.left ++ state.right).Pairwise (· ≤ ·))
      (fun h hr ↦ componentPBWExpansion_neighbors_pairwise
        n L data hn h hr)
      (s.coordinateState n L data hn i)
      (by simpa [coordinateState] using s.ordinary_pairwise)
      []
      (s.coefficient n L data hn *
        ((adaptedBasis n L data hn).repr (s.component n L data hn)) i)
      source hio
  exact componentPBW_terminal_word_pairwise n L data hn source.2 hneighbors
    (collectorFrontier_terminal_of_ne
      (componentPBWCollector n L data hn)
      (s.coordinateState n L data hn i) []
      (s.coefficient n L data hn *
        ((adaptedBasis n L data hn).repr (s.component n L data hn)) i)
      source hio)

end GoverningComponentSource

/-- Complete occurrence-level component PBW frontier of the global trace. -/
def GoverningWitness.globalComponentPBWOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    GoverningComponentPBWOccurrence n L data hn w →₀ ℤ :=
  (w.globalComponentSources n L data hn |>.map fun s ↦
    s.componentPBWFrontier n L data hn).sum

/-- The literal absorption ledger descends to every supported occurrence of
the global component frontier.  Source labels prevent different copies from
being combined here. -/
theorem GoverningWitness.globalComponentPBWOccurrence_MAbsorptionInvariant
    {a : L} (w : GoverningWitness n L data a)
    (o : GoverningComponentPBWOccurrence n L data hn w)
    (ho : w.globalComponentPBWOccurrences n L data hn o ≠ 0) :
    o.state.MAbsorptionInvariant n L data hn
      o.source.root o.source.mark o.source.context
      (ordinaryPieceMCount n L data hn
        (o.source.left ++ o.source.right)) := by
  rw [GoverningWitness.globalComponentPBWOccurrences] at ho
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      (w.globalComponentSources n L data hn |>.map fun s ↦
        s.componentPBWFrontier n L data hn) o ho
  rw [List.mem_map] at hfront
  obtain ⟨s, hs, rfl⟩ := hfront
  exact s.componentPBWFrontier_MAbsorptionInvariant_of_ne
    n L data hn o hfrontO

/-- Exact evaluated value of the occurrence-preserving global component
PBW frontier. -/
theorem GoverningWitness.evaluate_globalComponentPBWOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    (w.globalComponentPBWOccurrences n L data hn).sum
        (fun o z ↦ z • o.state.value n L data hn) =
      (w.globalComponentSources n L data hn |>.map fun s ↦
        s.coefficient n L data hn • s.occurrence.row.value).sum := by
  classical
  rw [GoverningWitness.globalComponentPBWOccurrences]
  induction w.globalComponentSources n L data hn with
  | nil => simp
  | cons s sources ih =>
      simp only [List.map_cons, List.sum_cons]
      change (Finsupp.linearCombination ℤ
          (fun o : GoverningComponentPBWOccurrence n L data hn w ↦
            o.state.value n L data hn))
          (s.componentPBWFrontier n L data hn +
            (sources.map fun t : GoverningComponentSource n L data hn w ↦
              t.componentPBWFrontier n L data hn).sum) = _
      rw [map_add]
      change
        (s.componentPBWFrontier n L data hn).sum
              (fun o z ↦ z • o.state.value n L data hn) +
            ((sources.map fun t : GoverningComponentSource n L data hn w ↦
              t.componentPBWFrontier n L data hn).sum).sum
              (fun o z ↦ z • o.state.value n L data hn) = _
      rw [s.evaluate_componentPBWFrontier n L data hn, ih]

/-- Every nonzero coefficient of the global component PBW ledger is a
genuine terminal state of the component collector. -/
theorem GoverningWitness.globalComponentPBWOccurrence_terminal_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (o : GoverningComponentPBWOccurrence n L data hn w)
    (ho : w.globalComponentPBWOccurrences n L data hn o ≠ 0) :
    componentPBWExpansion n L data hn o.state = none := by
  rw [GoverningWitness.globalComponentPBWOccurrences] at ho
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      (w.globalComponentSources n L data hn |>.map fun s ↦
        s.componentPBWFrontier n L data hn) o ho
  rw [List.mem_map] at hfront
  obtain ⟨s, hs, rfl⟩ := hfront
  exact s.componentPBWFrontier_terminal_of_ne n L data hn o hfrontO

/-- Every nonzero global component PBW occurrence is in the fixed ordered
adapted basis. -/
theorem GoverningWitness.globalComponentPBWOccurrence_word_pairwise_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (o : GoverningComponentPBWOccurrence n L data hn w)
    (ho : w.globalComponentPBWOccurrences n L data hn o ≠ 0) :
    (o.state.word n L data hn).Pairwise (· ≤ ·) := by
  rw [GoverningWitness.globalComponentPBWOccurrences] at ho
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_finsupp_in_list_of_sum_apply_ne_zero
      (w.globalComponentSources n L data hn |>.map fun s ↦
        s.componentPBWFrontier n L data hn) o ho
  rw [List.mem_map] at hfront
  obtain ⟨s, hs, rfl⟩ := hfront
  exact s.componentPBWFrontier_word_pairwise_of_ne
    n L data hn o hfrontO

/-- A terminal component occurrence with a displayed spectator has zero
complete one-factor primitive. -/
theorem GoverningWitness.globalComponentPBWOccurrence_primitive_eq_zero
    {a : L} (w : GoverningWitness n L data a)
    (o : GoverningComponentPBWOccurrence n L data hn w)
    (ho : w.globalComponentPBWOccurrences n L data hn o ≠ 0)
    (hfactor : o.state.factorCount n L data hn ≠ 1) :
    pbwPrimitive n L data hn (o.state.value n L data hn) = 0 :=
  o.state.pbwPrimitive_value_eq_zero_of_factorCount_ne_one n L data hn
    (w.globalComponentPBWOccurrence_word_pairwise_of_ne
      n L data hn o ho) hfactor

/-- The one-factor read of the global component ledger. -/
def GoverningWitness.globalComponentPBWPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.globalComponentPBWOccurrences n L data hn).sum fun o z ↦
    z • pbwPrimitive n L data hn (o.state.value n L data hn)

/-- Rule (5), spectator clause: after complete PBW collection the global
component primitive is supported only on literal factor-one occurrences. -/
theorem GoverningWitness.globalComponentPBWPrimitive_eq_factorOne
    {a : L} (w : GoverningWitness n L data a) :
    w.globalComponentPBWPrimitive n L data hn =
      (w.globalComponentPBWOccurrences n L data hn).sum (fun o z ↦
        if o.state.factorCount n L data hn = 1 then
          z • pbwPrimitive n L data hn (o.state.value n L data hn)
        else 0) := by
  classical
  rw [GoverningWitness.globalComponentPBWPrimitive]
  apply Finsupp.sum_congr
  intro o ho
  by_cases hone : o.state.factorCount n L data hn = 1
  · simp [hone]
  · rw [if_neg hone,
      w.globalComponentPBWOccurrence_primitive_eq_zero
        n L data hn o (Finsupp.mem_support_iff.mp ho) hone]
    simp

/-- The three syntactic terminal walls after complete component PBW
collection.  Factor two is passed to the Smith block, factor one to the
terminal read, and factor at least three is a canonical vertical product. -/
inductive ComponentPBWStoppingRule
    (s : ComponentPBWState n L data hn) : Prop
  | factorOne (h : s.factorCount n L data hn = 1)
  | factorTwo (h : s.factorCount n L data hn = 2)
  | factorAtLeastThree (h : 3 ≤ s.factorCount n L data hn)

/-- The terminal factor walls are exhaustive because every component state
contains its distinguished factor. -/
theorem ComponentPBWState.stoppingRule_exhaustive
    (s : ComponentPBWState n L data hn) :
    ComponentPBWStoppingRule n L data hn s := by
  have hpos : 1 ≤ s.factorCount n L data hn := by
    simp only [ComponentPBWState.factorCount]
    omega
  by_cases hone : s.factorCount n L data hn = 1
  · exact .factorOne hone
  by_cases htwo : s.factorCount n L data hn = 2
  · exact .factorTwo htwo
  exact .factorAtLeastThree (by omega)

namespace RelationContext

/-- The literal right-normed bracket context associated to an ordered list
of ordinary inputs.  This is the context used in the manuscript's terminal
full-commutator replacement. -/
def rightComb (xs : List (AdaptedIndex n L data hn)) :
    RelationContext n L data hn :=
  xs.foldl (fun c x ↦ .lieRight c x) .hole

private theorem rightComb_weight_aux
    (c : RelationContext n L data hn)
    (xs : List (AdaptedIndex n L data hn)) :
    RelationContext.weight n L data hn
        (xs.foldl (fun c x ↦ RelationContext.lieRight c x) c) =
      RelationContext.weight n L data hn c +
        (xs.map (adaptedWeightedBasis n L data hn).weight).sum := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [RelationContext.weight, Nat.add_assoc]

theorem rightComb_weight
    (xs : List (AdaptedIndex n L data hn)) :
    RelationContext.weight n L data hn
        (RelationContext.rightComb n L data hn xs) =
      (xs.map (adaptedWeightedBasis n L data hn).weight).sum := by
  simpa [RelationContext.rightComb, RelationContext.weight] using
    rightComb_weight_aux n L data hn
      (.hole : RelationContext n L data hn) xs

private theorem rightComb_apply_aux
    (c : RelationContext n L data hn) (d : FreeModel n L)
    (xs : List (AdaptedIndex n L data hn)) :
    RelationContext.apply n L data hn
        (xs.foldl (fun c x ↦ RelationContext.lieRight c x) c) d =
      adaptedRightComb n L data hn
        (RelationContext.apply n L data hn c d) xs := by
  induction xs generalizing c d with
  | nil => simp [adaptedRightComb]
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      rfl

theorem rightComb_apply
    (d : FreeModel n L) (xs : List (AdaptedIndex n L data hn)) :
    RelationContext.apply n L data hn
        (RelationContext.rightComb n L data hn xs) d =
      adaptedRightComb n L data hn d xs := by
  simpa [RelationContext.rightComb] using
    rightComb_apply_aux n L data hn
      (.hole : RelationContext n L data hn) d xs

end RelationContext

/-- A contextual application of a homogeneous weight-one input in a
weight-`n` right-comb context is entirely supported in the top homogeneous
piece. -/
private theorem weightIncl_weightProject_apply_rightComb_head
    (c : RelationContext n L data hn)
    (hc : RelationContext.weight n L data hn c = n)
    (z : FreeMetabelian.Piece (Generator L) 0) :
    FreeMetabelian.Free.weightIncl n (by omega)
        (FreeMetabelian.Free.weightProject n (by omega)
          (RelationContext.apply n L data hn c
            (FreeMetabelian.Free.weightIncl 0 (by omega) z))) =
      RelationContext.apply n L data hn c
        (FreeMetabelian.Free.weightIncl 0 (by omega) z) := by
  let y := RelationContext.apply n L data hn c
    (FreeMetabelian.Free.weightIncl 0 (by omega) z)
  change FreeMetabelian.Free.incl (⟨n, by omega⟩ : Fin (n + 1))
      (FreeMetabelian.Free.project (⟨n, by omega⟩ : Fin (n + 1)) y) = y
  calc
    _ = ∑ j : Fin (n + 1),
        FreeMetabelian.Free.incl j (FreeMetabelian.Free.project j y) := by
      symm
      apply Finset.sum_eq_single (⟨n, by omega⟩ : Fin (n + 1))
      · intro j _ hj
        have hjval : j.val ≠ n := by
          intro hval
          exact hj (Fin.ext hval)
        have hz : FreeMetabelian.Free.project j y = 0 :=
          RelationContext.apply_weightIncl_apply_eq_zero_of_ne
            n L data hn c 0 (by omega) z j (by omega)
        rw [hz, map_zero]
      · simp
    _ = y := FreeMetabelian.Free.sum_incl_project y

/-- The terminal coordinate kills a top-homogeneous element once it has
been identified with a genuine full relation. -/
private theorem topCoord_weightProject_eq_zero_of_fullRelation
    (x : FreeModel n L) (rho : Relations n L data)
    (hhom : FreeMetabelian.Free.weightIncl n (by omega)
        (FreeMetabelian.Free.weightProject n (by omega) x) = x)
    (hrho : x = (rho : FreeModel n L)) :
    topCoord n L data
        (FreeMetabelian.Free.weightProject n (by omega) x) = 0 := by
  change terminalEval n L data
    (topInclPreimage n L data
      (FreeMetabelian.Free.weightProject n (by omega) x)) = 0
  have heq : topInclPreimage n L data
      (FreeMetabelian.Free.weightProject n (by omega) x) =
        relationTopPreimage n L data rho := by
    apply Subtype.ext
    exact hhom.trans hrho
  rw [heq, terminalEval_relationTopPreimage]

namespace GoverningComponentSource

/-- Manuscript weight of the distinguished relation component at the
homogeneous horizontal child, before the vertical pass absorbs any ordinary
inputs. -/
def originActiveWeight {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : ℕ :=
  s.originMark.val + RelationContext.weight n L data hn s.originContext

/-- Ordinary input occurrences at the homogeneous horizontal child. -/
def originOrdinaryInputs {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    List (AdaptedIndex n L data hn) :=
  s.originLeft ++ s.originRight

/-- Number of ordinary source inputs in `M = F_{≥2}`.  This is the count
used in the corrected manuscript; it is deliberately taken before vertical
absorption. -/
noncomputable def originOrdinaryMCount
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : ℕ :=
  ordinaryPieceMCount n L data hn s.originOrdinaryInputs

/-- Factor number of the homogeneous horizontal child. -/
def originFactorCount {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : ℕ :=
  s.originLeft.length + 1 + s.originRight.length

/-- Total manuscript weight of the homogeneous horizontal child. -/
def originTotalWeight {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : ℕ :=
  s.originActiveWeight n L data hn +
    (s.originOrdinaryInputs n L data hn |>.map
      (adaptedWeightedBasis n L data hn).weight).sum

/-- The original horizontal component has positive mark, even if later
vertical corrections enlarge its context. -/
theorem originMark_pos
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    0 < s.originMark.val := by
  have h := s.terminal_eq_origin_extension n L data hn
  rw [← h.2.1]
  exact s.mark_pos

theorem originActiveWeight_pos
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    0 < s.originActiveWeight n L data hn := by
  rw [originActiveWeight]
  have hmark := s.originMark_pos n L data hn
  omega

/-- Origin count zero is exactly the all-weight-one ordinary-input case. -/
theorem originOrdinaryMCount_eq_zero_iff
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.originOrdinaryMCount n L data hn = 0 ↔
      ∀ x ∈ s.originOrdinaryInputs n L data hn,
        (adaptedWeightedBasis n L data hn).weight x = 1 := by
  classical
  rw [originOrdinaryMCount, ordinaryPieceMCount, List.countP_eq_zero]
  constructor
  · intro hall x hx
    have hfalse : decide (0 < x.1.val) = false :=
      Bool.eq_false_of_not_eq_true (hall x hx)
    have hnot : ¬0 < x.1.val := of_decide_eq_false hfalse
    change x.1.val + 1 = 1
    omega
  · intro hall x hx htrue
    have hpos : 0 < x.1.val := of_decide_eq_true htrue
    have hone := hall x hx
    change x.1.val + 1 = 1 at hone
    omega

private theorem originWeightSum_eq_length_of_all_one
    (xs : List (AdaptedIndex n L data hn))
    (h : ∀ x ∈ xs,
      (adaptedWeightedBasis n L data hn).weight x = 1) :
    (xs.map (adaptedWeightedBasis n L data hn).weight).sum = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons,
        h x (by simp), ih (fun y hy ↦ h y (by simp [hy]))]
      omega

/-- With no ordinary `M`-input, total weight is active weight plus one for
each remaining source factor. -/
theorem originTotalWeight_eq_active_add_ordinaryLength
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hzero : s.originOrdinaryMCount n L data hn = 0) :
    s.originTotalWeight n L data hn =
      s.originActiveWeight n L data hn +
        (s.originOrdinaryInputs n L data hn).length := by
  rw [originTotalWeight,
    originWeightSum_eq_length_of_all_one n L data hn
      s.originOrdinaryInputs
      ((s.originOrdinaryMCount_eq_zero_iff n L data hn).mp hzero)]

/-- Manuscript weight of the distinguished relation component. -/
def activeWeight {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : ℕ :=
  s.mark.val + RelationContext.weight n L data hn s.context

/-- Number of ordinary homogeneous input occurrences lying in
`M = F_{≥2}`.  Repeated equal basis vectors are counted with their list
multiplicity. -/
noncomputable def ordinaryMCount
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : ℕ :=
  (s.left ++ s.right).countP fun x ↦
    decide (2 ≤ (adaptedWeightedBasis n L data hn).weight x)

theorem activeWeight_pos
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    0 < s.activeWeight n L data hn := by
  rw [activeWeight]
  have hmark := s.mark_pos
  omega

/-- The terminal row and its homogeneous horizontal origin have exactly the
same total manuscript weight; absorbed factors have moved from the ordinary
word into the context and nowhere else. -/
theorem terminalTotalWeight_eq_originTotalWeight
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.activeWeight n L data hn +
        ((s.left ++ s.right).map
          (adaptedWeightedBasis n L data hn).weight).sum =
      s.originTotalWeight n L data hn := by
  have hmark := (s.terminal_eq_origin_extension n L data hn).2.1
  have hmarkval := congrArg Fin.val hmark
  have hweight := s.terminalWeight_eq_originWeight n L data hn
  unfold activeWeight originTotalWeight originActiveWeight
    originOrdinaryInputs
  simp only [List.map_append, List.sum_append]
  omega

/-- The manuscript count and the zero-based homogeneous-index count are
literally the same count. -/
theorem ordinaryMCount_eq_ordinaryPieceMCount
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.ordinaryMCount n L data hn =
      ordinaryPieceMCount n L data hn (s.left ++ s.right) := by
  unfold ordinaryMCount ordinaryPieceMCount
  apply List.countP_congr
  intro x hx
  by_cases hM : 0 < x.1.val
  · have hw : 2 ≤ (adaptedWeightedBasis n L data hn).weight x := by
      change 2 ≤ x.1.val + 1
      omega
    simp [hM, hw]
  · have hw : ¬2 ≤ (adaptedWeightedBasis n L data hn).weight x := by
      change ¬2 ≤ x.1.val + 1
      omega
    simp [hM, hw]

/-- An active component of manuscript weight at least two lies in
`M = F_{≥2}`. -/
theorem component_mem_tail_one_of_activeWeight_ge_two
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hactive : 2 ≤ s.activeWeight n L data hn) :
    s.component n L data hn ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) 1 := by
  rw [FreeMetabelian.Free.mem_tail_iff]
  intro i hi
  apply RelationContext.component_apply_eq_zero_of_ne
    n L data hn s.context s.root s.mark s.mark_pos
  change i.val + 1 ≠ s.activeWeight n L data hn
  omega

/-- Hence an active component of weight at least two is in the derived
ideal. -/
theorem component_mem_derived_of_activeWeight_ge_two
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hactive : 2 ≤ s.activeWeight n L data hn) :
    s.component n L data hn ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 :=
  global_mem_derived_of_mem_tail_one n L _
    (s.component_mem_tail_one_of_activeWeight_ge_two
      n L data hn hactive)

/-- An active-weight-one component is exactly its grouped homogeneous
weight-one coordinate. -/
theorem component_eq_weightIncl_zero_of_activeWeight_eq_one
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hactive : s.activeWeight n L data hn = 1) :
    s.component n L data hn =
      FreeMetabelian.Free.weightIncl 0 (by omega)
        (FreeMetabelian.Free.weightProject 0 (by omega)
          (s.component n L data hn)) := by
  funext i
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  by_cases hi : i = i0
  · subst i
    exact (FreeMetabelian.Free.incl_apply_same i0 _).symm
  · have hleft : s.component n L data hn i = 0 := by
      apply RelationContext.component_apply_eq_zero_of_ne
        n L data hn s.context s.root s.mark s.mark_pos
      change i.val + 1 ≠ s.activeWeight n L data hn
      intro heq
      have hi0 : i.val = 0 := by omega
      exact hi (Fin.ext hi0)
    change s.component n L data hn i =
      FreeMetabelian.Free.incl i0
        (FreeMetabelian.Free.project i0 (s.component n L data hn)) i
    rw [hleft, FreeMetabelian.Free.incl_apply_of_ne i0 i hi]

/-- At an active-weight-one homogeneous source, triangularity leaves exactly
the two cases used in the corrected proof.  A row whose leading triangular
weight is positive has zero weight-one component; a row beginning in weight
one contributes its single Smith diagonal times the corresponding adapted
basis vector. -/
theorem component_eq_zero_or_zeroLeadingSmithHead
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hactive : s.originActiveWeight n L data hn = 1) :
    s.component n L data hn = 0 ∨
      ∃ i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) 0,
        s.originRoot = triangularRelationOfIndex n L data
            ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ ∧
          s.component n L data hn =
          ((triangularSmith n L data 0 (by omega)).diagonal
              i : ℤ) •
            adaptedBasis n L data hn
              ⟨⟨0, by omega⟩, i⟩ := by
  classical
  rcases s.terminal_eq_origin n L data hn with
    ⟨hroot, hcontext, hmark, hleft, hright⟩
  rcases s.originHorizontalFrame n L data hn with
    ⟨horiginContext, horiginLeft, horiginRight⟩
  have horiginMark : s.originMark.val = 1 := by
    unfold originActiveWeight at hactive
    rw [horiginContext] at hactive
    simp only [RelationContext.weight] at hactive
    omega
  have hterminalMark : s.mark.val = 1 := by
    rw [hmark, horiginMark]
  rcases htagEq : s.occurrence.parent.source.relationTag with
    ⟨⟨q, hq⟩, i⟩
  by_cases hqzero : q = 0
  · subst q
    have hproof : hq = (by omega : 0 < n + 1) := Subsingleton.elim _ _
    cases hproof
    right
    have horiginRoot : s.originRoot = triangularRelationOfIndex n L data
        ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ := by
      rw [s.originRoot_eq_triangularRelation n L data hn, htagEq]
    refine ⟨i, horiginRoot, ?_⟩
    have hrootTag : s.root = triangularRelationOfIndex n L data
        ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :=
      hroot.trans horiginRoot
    have hcontextHole : s.context = .hole := hcontext.trans horiginContext
    have hmarkOne : s.mark = (⟨1, by omega⟩ : Fin (n + 2)) :=
      Fin.ext hterminalMark
    unfold GoverningComponentSource.component
    rw [hrootTag, hcontextHole, hmarkOne, RelationContext.component,
      dif_neg (by omega)]
    change FreeMetabelian.Free.weightIncl 0 (by omega)
        (FreeMetabelian.Free.weightProject 0 (by omega)
          (triangularRelationOfIndex n L data
            ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ : FreeModel n L)) = _
    have hhead := triangularRelationOfIndex_head n L data
      (⟨(⟨0, hq⟩ : Fin (n + 1)), i⟩ : TriangularRelationIndex n L)
    rw [hhead, map_zsmul, adaptedBasis_apply]
    congr 2
  · left
    let tag : TriangularRelationIndex n L := ⟨⟨q, hq⟩, i⟩
    have horiginRoot : s.originRoot = triangularRelationOfIndex n L data tag := by
      rw [s.originRoot_eq_triangularRelation n L data hn, htagEq]
    have hrootTag : s.root = triangularRelationOfIndex n L data tag :=
      hroot.trans horiginRoot
    have hcontextHole : s.context = .hole := hcontext.trans horiginContext
    have hmarkOne : s.mark = (⟨1, by omega⟩ : Fin (n + 2)) :=
      Fin.ext hterminalMark
    unfold GoverningComponentSource.component
    rw [hrootTag, hcontextHole, hmarkOne, RelationContext.component,
      dif_neg (by omega)]
    have htail := triangularRelationOfIndex_mem_tail n L data tag
    change FreeMetabelian.Free.weightIncl 0 (by omega)
        (FreeMetabelian.Free.weightProject 0 (by omega)
          (triangularRelationOfIndex n L data tag : FreeModel n L)) = 0
    have hzero : FreeMetabelian.Free.weightProject 0 (by omega)
        (triangularRelationOfIndex n L data tag : FreeModel n L) = 0 :=
      htail (⟨0, by omega⟩ : Fin (n + 1))
        (Nat.pos_of_ne_zero hqzero)
    rw [hzero, map_zero]

/-- Having no ordinary `M`-input is equivalent to every ordinary input
having manuscript weight one. -/
theorem ordinaryMCount_eq_zero_iff
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.ordinaryMCount n L data hn = 0 ↔
      ∀ x ∈ s.left ++ s.right,
        (adaptedWeightedBasis n L data hn).weight x = 1 := by
  classical
  rw [ordinaryMCount, List.countP_eq_zero]
  constructor
  · intro hall x hx
    have hfalse : decide
        (2 ≤ (adaptedWeightedBasis n L data hn).weight x) = false :=
      Bool.eq_false_of_not_eq_true (hall x hx)
    have hnot : ¬(2 ≤ (adaptedWeightedBasis n L data hn).weight x) :=
      of_decide_eq_false hfalse
    have hpos := (adaptedWeightedBasis n L data hn).weight_pos x
    omega
  · intro hall x hx htrue
    have hM : 2 ≤ (adaptedWeightedBasis n L data hn).weight x :=
      of_decide_eq_true htrue
    have hone := hall x hx
    omega

private theorem occurrence_value_eq_component_mul_right
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.occurrence.row.value =
      UniversalEnvelopingAlgebra.ι ℤ (s.component n L data hn) *
        MarkedRow.basisWord n L data hn s.right := by
  rw [s.row_eq, s.left_eq_nil n L data hn]
  simp [ProvenancedRow.value, GoverningComponentSource.component,
    MarkedRow.basisWord, LieRings.PBW.basisWord,
    LieRings.PBW.word]

private theorem right_pairwise
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.right.Pairwise (· ≤ ·) := by
  simpa [s.left_eq_nil n L data hn] using s.ordinary_pairwise

/-- A homogeneous source of the wrong total manuscript weight has no
weight-`n+1` one-factor PBW coordinate.  The proof is coefficientwise only
inside the fixed homogeneous component; the source occurrence itself stays
grouped. -/
theorem weightProject_pbwPrimitive_occurrence_value_eq_zero_of_originWeight_ne
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hne : s.originTotalWeight n L data hn ≠ n + 1) :
    FreeMetabelian.Free.weightProject n (by omega)
      (pbwPrimitive n L data hn s.occurrence.row.value) = 0 := by
  classical
  let B := adaptedWeightedBasis n L data hn
  let x := s.component n L data hn
  have htotal := s.terminalTotalWeight_eq_originTotalWeight n L data hn
  rw [s.left_eq_nil n L data hn] at htotal
  simp only [List.nil_append] at htotal
  have hrow : B.proj (n + 1) 1 s.occurrence.row.value = 0 := by
    rw [s.occurrence_value_eq_component_mul_right n L data hn]
    change B.proj (n + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ x *
        MarkedRow.basisWord n L data hn s.right) = 0
    rw [← (adaptedBasis n L data hn).sum_repr x, map_sum,
      Finset.sum_mul, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_zsmul, smul_mul_assoc, map_zsmul]
    by_cases hiw : B.weight i = s.activeWeight n L data hn
    · have hword :
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) *
              MarkedRow.basisWord n L data hn s.right =
            MarkedRow.basisWord n L data hn (i :: s.right) := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      rw [hword]
      have hweight :
          (((i :: s.right).map B.weight).sum) ≠ n + 1 := by
        simp only [List.map_cons, List.sum_cons]
        intro heq
        apply hne
        rw [← htotal]
        rw [hiw] at heq
        simpa [B] using heq
      have hzero : B.proj (n + 1) 1
          (MarkedRow.basisWord n L data hn (i :: s.right)) = 0 := by
        change B.proj (n + 1) 1
          (LieRings.PBW.basisWord ℤ (FreeModel n L)
            (AdaptedIndex n L data hn) B.basis (i :: s.right)) = 0
        exact B.proj_basisWord_eq_zero_of_weight_ne
          (i :: s.right) (n + 1) 1 hweight
      rw [hzero, smul_zero]
    · have hcoeff : ((adaptedBasis n L data hn).repr x) i = 0 := by
        change ((pieceAdaptedBasis n L data hn i.1).repr (x i.1)) i.2 = 0
        have hx : x i.1 = 0 := by
          apply RelationContext.component_apply_eq_zero_of_ne
            n L data hn s.context s.root s.mark s.mark_pos i.1
          simpa [B, adaptedWeightedBasis,
            GoverningComponentSource.activeWeight] using hiw
        rw [hx, map_zero]
        rfl
      rw [hcoeff, zero_smul]
  have hprimitive : B.proj (n + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ
        (pbwPrimitive n L data hn s.occurrence.row.value)) = 0 := by
    rw [← factorProj_one_eq_iota_pbwPrimitive n L data hn]
    rw [B.proj_factorProj]
    exact hrow
  rw [adapted_proj_top_iota n L data hn] at hprimitive
  have hfree : FreeMetabelian.Free.weightIncl (c := n + 1)
      n (Nat.lt_succ_self n)
      (FreeMetabelian.Free.weightProject (c := n + 1)
        n (Nat.lt_succ_self n)
        (pbwPrimitive n L data hn s.occurrence.row.value)) = 0 := by
    apply LieRings.PBW.canonicalMap_injective_of_freeModulePBW
      ℤ (FreeModel n L) (AdaptedIndex n L data hn)
      B.basis
      (LieRings.PBW.freeModulePBW_int
        (FreeModel n L) (AdaptedIndex n L data hn)
        B.basis)
    simpa using hprimitive
  have hp := congrArg (FreeMetabelian.Free.weightProject (c := n + 1)
    n (Nat.lt_succ_self n)) hfree
  simpa using hp

/-- Wrong total weight is therefore silent for the single target read map. -/
theorem terminalPrimitiveRead_occurrence_value_eq_zero_of_originWeight_ne
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hne : s.originTotalWeight n L data hn ≠ n + 1) :
    terminalPrimitiveRead n L data hn s.occurrence.row.value = 0 := by
  rw [terminalPrimitiveRead, LinearMap.comp_apply, LinearMap.comp_apply,
    s.weightProject_pbwPrimitive_occurrence_value_eq_zero_of_originWeight_ne
      n L data hn hne, map_zero]

/-- Vanishing of the component itself kills the grouped source primitive. -/
private theorem pbwPrimitive_occurrence_value_eq_zero_of_component_eq_zero
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hcomponent : s.component n L data hn = 0) :
    pbwPrimitive n L data hn s.occurrence.row.value = 0 := by
  rw [s.occurrence_value_eq_component_mul_right n L data hn,
    hcomponent, map_zero, zero_mul, map_zero]

private theorem exists_right_piece_pos_of_ordinaryMCount_pos
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hordinary : 1 ≤ s.ordinaryMCount n L data hn) :
    ∃ i ∈ s.right, 0 < i.1.val := by
  have hcount : 1 ≤ ordinaryPieceMCount n L data hn s.right := by
    have heq := s.ordinaryMCount_eq_ordinaryPieceMCount n L data hn
    rw [s.left_eq_nil n L data hn] at heq
    simp only [List.nil_append] at heq
    rw [← heq]
    exact hordinary
  change 1 ≤ s.right.countP (fun i ↦ decide (0 < i.1.val)) at hcount
  by_contra hnone
  have hzero : s.right.countP (fun i ↦ decide (0 < i.1.val)) = 0 :=
    List.countP_eq_zero.mpr (by
      intro i hi htrue
      exact hnone ⟨i, hi, of_decide_eq_true htrue⟩)
  omega

/-- The first half of stopping rule (4): an active relation component in
`M`, together with one ordinary `M`-input, has zero complete primitive. -/
theorem pbwPrimitive_occurrence_value_eq_zero_of_relationM_and_ordinaryM
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hactive : 2 ≤ s.activeWeight n L data hn)
    (hordinary : 1 ≤ s.ordinaryMCount n L data hn) :
    pbwPrimitive n L data hn s.occurrence.row.value = 0 := by
  rw [s.occurrence_value_eq_component_mul_right n L data hn,
    pbwPrimitive_iota_mul_basisWord_of_mem_tail_one
      n L data hn (s.component n L data hn)
        (s.component_mem_tail_one_of_activeWeight_ge_two
          n L data hn hactive) s.right (s.right_pairwise n L data hn)]
  exact adaptedRightComb_eq_zero_of_derived_of_exists_piece_pos
    n L data hn (s.component n L data hn)
      (s.component_mem_derived_of_activeWeight_ge_two
        n L data hn hactive) s.right
      (s.exists_right_piece_pos_of_ordinaryMCount_pos
        n L data hn hordinary)

/-- The second half of stopping rule (4): a grouped active-weight-one
component followed by two ordinary `M`-inputs has zero complete primitive. -/
theorem pbwPrimitive_occurrence_value_eq_zero_of_weightOne_and_two_ordinaryM
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hactive : s.activeWeight n L data hn = 1)
    (hordinary : 2 ≤ s.ordinaryMCount n L data hn) :
    pbwPrimitive n L data hn s.occurrence.row.value = 0 := by
  have hcount :
      2 ≤ s.right.countP (fun i ↦ decide (0 < i.1.val)) := by
    change 2 ≤ ordinaryPieceMCount n L data hn s.right
    have heq := s.ordinaryMCount_eq_ordinaryPieceMCount n L data hn
    rw [s.left_eq_nil n L data hn] at heq
    simp only [List.nil_append] at heq
    rw [← heq]
    exact hordinary
  rw [s.occurrence_value_eq_component_mul_right n L data hn,
    s.component_eq_weightIncl_zero_of_activeWeight_eq_one
      n L data hn hactive]
  exact pbwPrimitive_iota_weightIncl_zero_mul_basisWord_eq_zero_of_twoM
    n L data hn _ s.right (s.right_pairwise n L data hn) hcount

end GoverningComponentSource

/-- Four-way input partition at the homogeneous horizontal source, before
any vertical correction can move an ordinary input into the context. -/
inductive OriginInputProfileTag
  | relationM
  | ordinaryM
  | twoMInputs
  | allWeightOne
  deriving DecidableEq

/-- The corrected manuscript's input tag. -/
def GoverningComponentSource.originInputProfileTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    OriginInputProfileTag :=
  if s.originActiveWeight n L data hn = 1 then
    if s.originOrdinaryMCount n L data hn = 0 then .allWeightOne
    else if s.originOrdinaryMCount n L data hn = 1 then .ordinaryM
    else .twoMInputs
  else if s.originOrdinaryMCount n L data hn = 0 then .relationM
  else .twoMInputs

/-- Exact mathematical content of the origin tag. -/
theorem GoverningComponentSource.originInputProfileTag_spec
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    match s.originInputProfileTag n L data hn with
    | .relationM =>
        2 ≤ s.originActiveWeight n L data hn ∧
          s.originOrdinaryMCount n L data hn = 0
    | .ordinaryM =>
        s.originActiveWeight n L data hn = 1 ∧
          s.originOrdinaryMCount n L data hn = 1
    | .twoMInputs =>
        (2 ≤ s.originActiveWeight n L data hn ∧
            1 ≤ s.originOrdinaryMCount n L data hn) ∨
          2 ≤ s.originOrdinaryMCount n L data hn
    | .allWeightOne =>
        s.originActiveWeight n L data hn = 1 ∧
          s.originOrdinaryMCount n L data hn = 0 := by
  have hactive := s.originActiveWeight_pos n L data hn
  by_cases ha : s.originActiveWeight n L data hn = 1
  · by_cases hzero : s.originOrdinaryMCount n L data hn = 0
    · simp [GoverningComponentSource.originInputProfileTag, ha, hzero]
    · by_cases hone : s.originOrdinaryMCount n L data hn = 1
      · simp [GoverningComponentSource.originInputProfileTag,
          ha, hzero, hone]
      · have htwo : 2 ≤ s.originOrdinaryMCount n L data hn := by omega
        simp [GoverningComponentSource.originInputProfileTag,
          ha, hzero, hone, htwo]
  · have ha2 : 2 ≤ s.originActiveWeight n L data hn := by omega
    by_cases hzero : s.originOrdinaryMCount n L data hn = 0
    · simp [GoverningComponentSource.originInputProfileTag,
        ha, hzero, ha2]
    · have hone : 1 ≤ s.originOrdinaryMCount n L data hn := by omega
      simp [GoverningComponentSource.originInputProfileTag,
        ha, hzero, ha2, hone]

namespace GoverningComponentSource

theorem originFactorCount_eq_inputs_length_add_one
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.originFactorCount n L data hn =
      (s.originOrdinaryInputs n L data hn).length + 1 := by
  simp [originFactorCount, originOrdinaryInputs]
  omega

/-- First bullet of the terminal classification: if the unique `M`-input is
the relation component and the target weight is `n+1`, the source factor
number is exactly `m_k = n-k+2`. -/
theorem originFactorCount_eq_m_of_relationM_target
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.originInputProfileTag n L data hn = .relationM)
    (htarget : s.originTotalWeight n L data hn = n + 1)
    (hactive_le : s.originActiveWeight n L data hn ≤ n) :
    s.originFactorCount n L data hn =
      n - s.originActiveWeight n L data hn + 2 := by
  have hprofile := s.originInputProfileTag_spec n L data hn
  rw [htag] at hprofile
  have hweight :=
    s.originTotalWeight_eq_active_add_ordinaryLength
      n L data hn hprofile.2
  rw [htarget] at hweight
  have hfactor := s.originFactorCount_eq_inputs_length_add_one
    n L data hn
  omega

/-- Third bullet of the terminal classification: if every source input has
weight one, target weight forces factor number `n+1`. -/
theorem originFactorCount_eq_top_of_allWeightOne_target
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.originInputProfileTag n L data hn = .allWeightOne)
    (htarget : s.originTotalWeight n L data hn = n + 1) :
    s.originFactorCount n L data hn = n + 1 := by
  have hprofile := s.originInputProfileTag_spec n L data hn
  rw [htag] at hprofile
  have hweight :=
    s.originTotalWeight_eq_active_add_ordinaryLength
      n L data hn hprofile.2
  rw [htarget] at hweight
  have hfactor := s.originFactorCount_eq_inputs_length_add_one
    n L data hn
  omega

/-- The three surviving walls of a target-weight relation-`M` source.
The distinguished component has active weight at least two and every
ordinary source input has weight one.  Hence active weight `n+1` leaves one
factor, active weight `n` leaves two factors, and every smaller active weight
`k` lies on the intermediate `(n-k+2,k)` diagonal. -/
theorem relationM_target_wall_classification
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.originInputProfileTag n L data hn = .relationM)
    (htarget : s.originTotalWeight n L data hn = n + 1) :
    (s.originActiveWeight n L data hn = n + 1 ∧
        s.originFactorCount n L data hn = 1) ∨
      (s.originActiveWeight n L data hn = n ∧
        s.originFactorCount n L data hn = 2) ∨
      ∃ k, s.originActiveWeight n L data hn = k ∧
        s.originFactorCount n L data hn = n - k + 2 ∧
        2 ≤ k ∧ k < n := by
  have hprofile := s.originInputProfileTag_spec n L data hn
  rw [htag] at hprofile
  have hweight :=
    s.originTotalWeight_eq_active_add_ordinaryLength
      n L data hn hprofile.2
  rw [htarget] at hweight
  have hfactor := s.originFactorCount_eq_inputs_length_add_one
    n L data hn
  by_cases houtside : s.originActiveWeight n L data hn = n + 1
  · exact Or.inl ⟨houtside, by omega⟩
  by_cases htwo : s.originActiveWeight n L data hn = n
  · exact Or.inr (Or.inl ⟨htwo, by omega⟩)
  · refine Or.inr (Or.inr
      ⟨s.originActiveWeight n L data hn, rfl, ?_, hprofile.1, by omega⟩)
    exact s.originFactorCount_eq_m_of_relationM_target
      n L data hn htag htarget (by omega)

/-- In the intermediate case the source occurrence belongs literally to
the horizontal side of the corresponding global diagonal cut. -/
theorem occurrence_isDiagonalHorizontal_of_relationM_target
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.originInputProfileTag n L data hn = .relationM)
    (htarget : s.originTotalWeight n L data hn = n + 1)
    (hlt : s.originActiveWeight n L data hn < n) :
    s.occurrence.IsDiagonalHorizontal n L data hn
      (s.originActiveWeight n L data hn) := by
  have hprofile := s.originInputProfileTag_spec n L data hn
  rw [htag] at hprofile
  refine ⟨s.external, s.homogeneous, ?_, ?_, hprofile.1, hlt⟩
  · rw [s.originRow_eq]
    have hfactor := s.originFactorCount_eq_m_of_relationM_target
      n L data hn htag htarget (Nat.le_of_lt hlt)
    simpa [ProvenancedRow.factorCount,
      GoverningComponentSource.originFactorCount, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hfactor
  · rw [s.originRow_eq]
    rfl

/-- Corrected occurrence-source form of the two-`M` stopping rule.  It
counts inputs at the homogeneous horizontal child, and then considers how
many of those inputs were absorbed by the vertical pass. -/
theorem pbwPrimitive_occurrence_value_eq_zero_of_origin_twoMTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.originInputProfileTag n L data hn = .twoMInputs) :
    pbwPrimitive n L data hn s.occurrence.row.value = 0 := by
  have hprofile := s.originInputProfileTag_spec n L data hn
  rw [htag] at hprofile
  rcases s.terminal_eq_origin_extension n L data hn with
    ⟨hroot, hmark, q, hcontext, hcount⟩
  have hcontextWeight := hcontext.count_le_weight n L data hn
  have hmarkval := congrArg Fin.val hmark
  have hterminalCount : q + s.ordinaryMCount n L data hn =
      s.originOrdinaryMCount n L data hn := by
    rw [s.ordinaryMCount_eq_ordinaryPieceMCount n L data hn]
    exact hcount
  have component_zero_of_two_absorbed (hq : 2 ≤ q) :
      s.component n L data hn = 0 := by
    have hz := RelationContext.component_eq_zero_of_MExtension_of_two_le
      n L data hn s.originContext s.context q hcontext
        s.originRoot s.originMark hq
    unfold component
    rw [hroot, hmark]
    exact hz
  rcases hprofile with ⟨horiginActive, horiginOrdinary⟩ |
      horiginOrdinary
  · have hbase :=
      RelationContext.component_mem_derived_of_activeWeight_ge_two
        n L data hn s.originContext s.originRoot s.originMark
          (s.originMark_pos n L data hn) horiginActive
    by_cases hq : 1 ≤ q
    · have hz :=
        RelationContext.component_eq_zero_of_MExtension_of_base_derived
          n L data hn s.originContext s.context q hcontext
            s.originRoot s.originMark hbase hq
      apply s.pbwPrimitive_occurrence_value_eq_zero_of_component_eq_zero
        n L data hn
      unfold component
      rw [hroot, hmark]
      exact hz
    · apply s.pbwPrimitive_occurrence_value_eq_zero_of_relationM_and_ordinaryM
        n L data hn
      · unfold originActiveWeight at horiginActive
        change 2 ≤ s.mark.val +
          RelationContext.weight n L data hn s.context
        omega
      · omega
  · by_cases hqTwo : 2 ≤ q
    · exact s.pbwPrimitive_occurrence_value_eq_zero_of_component_eq_zero
        n L data hn (component_zero_of_two_absorbed hqTwo)
    · by_cases hactive : s.activeWeight n L data hn = 1
      · apply
          s.pbwPrimitive_occurrence_value_eq_zero_of_weightOne_and_two_ordinaryM
            n L data hn hactive
        unfold activeWeight at hactive
        have hmarkPos := s.mark_pos
        have hqZero : q = 0 := by omega
        omega
      · apply
          s.pbwPrimitive_occurrence_value_eq_zero_of_relationM_and_ordinaryM
            n L data hn
        · have hpos := s.activeWeight_pos n L data hn
          omega
        · omega

end GoverningComponentSource

/-- The four mutually exclusive input profiles in the corrected manuscript.
The `twoMInputs` case includes either a derived relation component together
with an ordinary derived input, or at least two ordinary derived inputs. -/
inductive ComponentInputProfile
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : Prop
  | relationM
      (hactive : 2 ≤ s.activeWeight n L data hn)
      (hordinary : s.ordinaryMCount n L data hn = 0)
  | ordinaryM
      (hactive : s.activeWeight n L data hn = 1)
      (hordinary : s.ordinaryMCount n L data hn = 1)
  | twoMInputs
      (h : (2 ≤ s.activeWeight n L data hn ∧
              1 ≤ s.ordinaryMCount n L data hn) ∨
            2 ≤ s.ordinaryMCount n L data hn)
  | allWeightOne
      (hactive : s.activeWeight n L data hn = 1)
      (hordinary : s.ordinaryMCount n L data hn = 0)

/-- The number and source of the `M`-inputs give an exhaustive occurrence
partition before any terminal values are combined. -/
theorem GoverningComponentSource.inputProfile_exhaustive
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    ComponentInputProfile n L data hn s := by
  have hactive := s.activeWeight_pos n L data hn
  by_cases ha : s.activeWeight n L data hn = 1
  · by_cases hzero : s.ordinaryMCount n L data hn = 0
    · exact .allWeightOne ha hzero
    · by_cases hone : s.ordinaryMCount n L data hn = 1
      · exact .ordinaryM ha hone
      · exact .twoMInputs (Or.inr (by omega))
  · have ha2 : 2 ≤ s.activeWeight n L data hn := by omega
    by_cases hzero : s.ordinaryMCount n L data hn = 0
    · exact .relationM ha2 hzero
    · exact .twoMInputs (Or.inl ⟨ha2, by omega⟩)

/-- Computable four-way tag used to partition the actual finite occurrence
ledger. -/
inductive ComponentInputProfileTag
  | relationM
  | ordinaryM
  | twoMInputs
  | allWeightOne
  deriving DecidableEq

/-- Canonical tag of a component source.  The order of the tests is the
case split in the corrected manuscript. -/
def GoverningComponentSource.inputProfileTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    ComponentInputProfileTag :=
  if s.activeWeight n L data hn = 1 then
    if s.ordinaryMCount n L data hn = 0 then .allWeightOne
    else if s.ordinaryMCount n L data hn = 1 then .ordinaryM
    else .twoMInputs
  else if s.ordinaryMCount n L data hn = 0 then .relationM
  else .twoMInputs

/-- The canonical tag carries exactly the corresponding mathematical input
profile. -/
theorem GoverningComponentSource.inputProfileTag_spec
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    match s.inputProfileTag n L data hn with
    | .relationM =>
        2 ≤ s.activeWeight n L data hn ∧
          s.ordinaryMCount n L data hn = 0
    | .ordinaryM =>
        s.activeWeight n L data hn = 1 ∧
          s.ordinaryMCount n L data hn = 1
    | .twoMInputs =>
        (2 ≤ s.activeWeight n L data hn ∧
            1 ≤ s.ordinaryMCount n L data hn) ∨
          2 ≤ s.ordinaryMCount n L data hn
    | .allWeightOne =>
          s.activeWeight n L data hn = 1 ∧
          s.ordinaryMCount n L data hn = 0 := by
  have hactive := s.activeWeight_pos n L data hn
  by_cases ha : s.activeWeight n L data hn = 1
  · by_cases hzero : s.ordinaryMCount n L data hn = 0
    · simp [GoverningComponentSource.inputProfileTag, ha, hzero]
    · by_cases hone : s.ordinaryMCount n L data hn = 1
      · simp [GoverningComponentSource.inputProfileTag, ha, hzero, hone]
      · have htwo : 2 ≤ s.ordinaryMCount n L data hn := by omega
        simp [GoverningComponentSource.inputProfileTag, ha, hzero, hone, htwo]
  · have ha2 : 2 ≤ s.activeWeight n L data hn := by omega
    by_cases hzero : s.ordinaryMCount n L data hn = 0
    · simp [GoverningComponentSource.inputProfileTag, ha, hzero, ha2]
    · have hone : 1 ≤ s.ordinaryMCount n L data hn := by omega
      simp [GoverningComponentSource.inputProfileTag, ha, hzero, ha2, hone]

/-- Stopping rule (4), grouped source form: every source in the `twoMInputs`
family has zero complete one-factor PBW read. -/
theorem GoverningComponentSource.pbwPrimitive_occurrence_value_eq_zero_of_twoMTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.inputProfileTag n L data hn = .twoMInputs) :
    pbwPrimitive n L data hn s.occurrence.row.value = 0 := by
  have hprofile := s.inputProfileTag_spec n L data hn
  rw [htag] at hprofile
  rcases hprofile with ⟨hactive, hordinary⟩ | hordinary
  · exact s.pbwPrimitive_occurrence_value_eq_zero_of_relationM_and_ordinaryM
      n L data hn hactive hordinary
  · by_cases hactive : s.activeWeight n L data hn = 1
    · exact s.pbwPrimitive_occurrence_value_eq_zero_of_weightOne_and_two_ordinaryM
        n L data hn hactive hordinary
    · have hactiveTwo : 2 ≤ s.activeWeight n L data hn := by
        have hpos := s.activeWeight_pos n L data hn
        omega
      exact s.pbwPrimitive_occurrence_value_eq_zero_of_relationM_and_ordinaryM
        n L data hn hactiveTwo (by omega)

/-- The completely collected grouped source primitive is silent in the
two-`M` family. -/
theorem GoverningComponentSource.componentPBWPrimitive_eq_zero_of_twoMTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.inputProfileTag n L data hn = .twoMInputs) :
    s.componentPBWPrimitive n L data hn = 0 := by
  rw [s.componentPBWPrimitive_eq_coefficient_smul n L data hn,
    s.pbwPrimitive_occurrence_value_eq_zero_of_twoMTag
      n L data hn htag, smul_zero]

/-- Filtering one grouped source frontier by a source tag either keeps the
whole frontier or removes it.  No coordinate descendant is split away from
the homogeneous component to which it belongs. -/
theorem GoverningComponentSource.componentPBWFrontier_filter_sourceTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (tag : ComponentInputProfileTag) :
    (s.componentPBWFrontier n L data hn).filter (fun o ↦
        o.source.inputProfileTag n L data hn = tag) =
      if s.inputProfileTag n L data hn = tag then
        s.componentPBWFrontier n L data hn
      else 0 := by
  classical
  by_cases htag : s.inputProfileTag n L data hn = tag
  · rw [if_pos htag]
    rw [Finsupp.filter_eq_self_iff]
    intro o ho
    rw [s.componentPBWFrontier_source_eq_of_ne n L data hn o ho]
    exact htag
  · rw [if_neg htag]
    rw [Finsupp.filter_eq_zero_iff]
    intro o hsource
    by_contra ho
    apply htag
    simpa [s.componentPBWFrontier_source_eq_of_ne n L data hn o ho]
      using hsource

/-- The terminal component PBW occurrences in one of the four disjoint
input-profile families. -/
def GoverningWitness.globalComponentPBWProfileOccurrences
    {a : L} (w : GoverningWitness n L data a)
    (tag : ComponentInputProfileTag) :
    GoverningComponentPBWOccurrence n L data hn w →₀ ℤ :=
  (w.globalComponentPBWOccurrences n L data hn).filter fun o ↦
    o.source.inputProfileTag n L data hn = tag

/-- A profile filter acts on whole grouped source frontiers. -/
theorem GoverningWitness.globalComponentPBWProfileOccurrences_eq_sourceSum
    {a : L} (w : GoverningWitness n L data a)
    (tag : ComponentInputProfileTag) :
    w.globalComponentPBWProfileOccurrences n L data hn tag =
      (w.globalComponentSources n L data hn |>.map fun s ↦
        if s.inputProfileTag n L data hn = tag then
          s.componentPBWFrontier n L data hn
        else 0).sum := by
  classical
  rw [GoverningWitness.globalComponentPBWProfileOccurrences,
    GoverningWitness.globalComponentPBWOccurrences]
  induction w.globalComponentSources n L data hn with
  | nil =>
      rw [List.map_nil, List.sum_nil, Finsupp.filter_zero]
      simp only [List.map_nil, List.sum_nil]
  | cons s sources ih =>
      simp only [List.map_cons, List.sum_cons, Finsupp.filter_add, ih]
      rw [s.componentPBWFrontier_filter_sourceTag n L data hn tag]

/-- Complete one-factor read of one global input-profile family. -/
def GoverningWitness.globalComponentPBWProfilePrimitive
    {a : L} (w : GoverningWitness n L data a)
    (tag : ComponentInputProfileTag) : FreeModel n L :=
  (w.globalComponentPBWProfileOccurrences n L data hn tag).sum
    fun o z ↦ z • pbwPrimitive n L data hn (o.state.value n L data hn)

/-- The profile primitive is the sum of grouped source primitives, never a
sum of independently interpreted basis-coordinate descendants. -/
theorem GoverningWitness.globalComponentPBWProfilePrimitive_eq_sourceSum
    {a : L} (w : GoverningWitness n L data a)
    (tag : ComponentInputProfileTag) :
    w.globalComponentPBWProfilePrimitive n L data hn tag =
      (w.globalComponentSources n L data hn |>.map fun s ↦
        if s.inputProfileTag n L data hn = tag then
          s.componentPBWPrimitive n L data hn
        else 0).sum := by
  classical
  rw [GoverningWitness.globalComponentPBWProfilePrimitive,
    w.globalComponentPBWProfileOccurrences_eq_sourceSum n L data hn tag]
  induction w.globalComponentSources n L data hn with
  | nil => simp
  | cons s sources ih =>
      simp only [List.map_cons, List.sum_cons]
      change (Finsupp.linearCombination ℤ
          (fun o : GoverningComponentPBWOccurrence n L data hn w ↦
            pbwPrimitive n L data hn (o.state.value n L data hn)))
          ((if s.inputProfileTag n L data hn = tag then
              s.componentPBWFrontier n L data hn else 0) +
            (sources.map fun t : GoverningComponentSource n L data hn w ↦
              if t.inputProfileTag n L data hn = tag then
                t.componentPBWFrontier n L data hn else 0).sum) = _
      rw [map_add]
      by_cases htag : s.inputProfileTag n L data hn = tag
      · simp only [if_pos htag]
        change s.componentPBWPrimitive n L data hn +
            (sources.map fun t : GoverningComponentSource n L data hn w ↦
              if t.inputProfileTag n L data hn = tag then
                t.componentPBWFrontier n L data hn else 0).sum.sum
              (fun o z ↦ z • pbwPrimitive n L data hn
                (o.state.value n L data hn)) =
          s.componentPBWPrimitive n L data hn +
            (sources.map fun t : GoverningComponentSource n L data hn w ↦
              if t.inputProfileTag n L data hn = tag then
                t.componentPBWPrimitive n L data hn else 0).sum
        rw [ih]
      · simp only [if_neg htag, map_zero, zero_add]
        exact ih

/-- The complete global two-`M` profile is silent. -/
theorem GoverningWitness.globalComponentPBWProfilePrimitive_twoMInputs_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    w.globalComponentPBWProfilePrimitive n L data hn .twoMInputs = 0 := by
  rw [w.globalComponentPBWProfilePrimitive_eq_sourceSum
    n L data hn .twoMInputs]
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  by_cases htag : s.inputProfileTag n L data hn = .twoMInputs
  · rw [if_pos htag,
      s.componentPBWPrimitive_eq_zero_of_twoMTag n L data hn htag]
  · rw [if_neg htag]

/-- The four profile ledgers are a literal, disjoint, exhaustive
decomposition of the terminal component PBW ledger. -/
theorem GoverningWitness.globalComponentPBWProfileOccurrences_partition
    {a : L} (w : GoverningWitness n L data a) :
    w.globalComponentPBWProfileOccurrences n L data hn .relationM +
        w.globalComponentPBWProfileOccurrences n L data hn .ordinaryM +
        w.globalComponentPBWProfileOccurrences n L data hn .twoMInputs +
        w.globalComponentPBWProfileOccurrences n L data hn .allWeightOne =
      w.globalComponentPBWOccurrences n L data hn := by
  classical
  ext o
  cases htag : o.source.inputProfileTag n L data hn <;>
    simp [GoverningWitness.globalComponentPBWProfileOccurrences, htag]

/-! ## Correct source-origin partition

The preceding terminal tag is retained for the already compiled collector
API.  The corrected proof must instead tag the homogeneous horizontal child:
vertical collection is allowed to absorb ordinary inputs into the relation
context.  The following ledger is therefore the one used downstream. -/

/-- Grouped source primitive vanishes when its homogeneous horizontal origin
contains two `M`-inputs. -/
theorem GoverningComponentSource.componentPBWPrimitive_eq_zero_of_origin_twoMTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.originInputProfileTag n L data hn = .twoMInputs) :
    s.componentPBWPrimitive n L data hn = 0 := by
  rw [s.componentPBWPrimitive_eq_coefficient_smul n L data hn,
    s.pbwPrimitive_occurrence_value_eq_zero_of_origin_twoMTag
      n L data hn htag, smul_zero]

/-- The ordinary-`M` full-commutator family is silent.  The triangular
weight-one head is collected from the left through the ordered ordinary
word.  If it is already ordered, its one-factor primitive is zero.  In the
only transfer branch, the crossed factor still has weight one, so the unique
ordinary `M`-input remains in the suffix and kills the derived right-comb by
metabelianity. -/
theorem GoverningComponentSource.pbwPrimitive_occurrence_value_eq_zero_of_origin_ordinaryMTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.originInputProfileTag n L data hn = .ordinaryM) :
    pbwPrimitive n L data hn s.occurrence.row.value = 0 := by
  classical
  have hprofile := s.originInputProfileTag_spec n L data hn
  rw [htag] at hprofile
  rcases s.component_eq_zero_or_zeroLeadingSmithHead
      n L data hn hprofile.1 with hzero | ⟨i, hroot, hcomponent⟩
  · exact s.pbwPrimitive_occurrence_value_eq_zero_of_component_eq_zero
      n L data hn hzero
  · have hrightEq := (s.terminal_eq_origin n L data hn).2.2.2.2
    have horiginLeft := (s.originHorizontalFrame n L data hn).2.1
    have hcount :
        s.right.countP (fun j ↦ decide (0 < j.1.val)) = 1 := by
      have hc := hprofile.2
      unfold originOrdinaryMCount originOrdinaryInputs
        ordinaryPieceMCount at hc
      rw [horiginLeft, List.nil_append, ← hrightEq] at hc
      exact hc
    have hrightNe : s.right ≠ [] := by
      intro hnil
      rw [hnil] at hcount
      simp at hcount
    obtain ⟨x, xs, hright⟩ := List.exists_cons_of_ne_nil hrightNe
    let h : AdaptedIndex n L data hn :=
      ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩
    let d : ℤ :=
      ((triangularSmith n L data 0 (by omega)).diagonal i : ℤ)
    have hordered : (x :: xs).Pairwise (· ≤ ·) := by
      rw [← hright]
      exact s.right_pairwise n L data hn
    rw [s.occurrence_value_eq_component_mul_right n L data hn,
      hcomponent, hright, map_zsmul, smul_mul_assoc, map_zsmul]
    change d • pbwPrimitive n L data hn
        (UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn h) *
          MarkedRow.basisWord n L data hn (x :: xs)) = 0
    rw [pbwPrimitive_iota_basis_mul_basisWord_cons
      n L data hn h x xs hordered]
    by_cases hhx : h ≤ x
    · rw [if_pos hhx, smul_zero]
    · rw [if_neg hhx]
      have hxh : x ≤ h := le_of_not_ge hhx
      have hx0 : x.1.val = 0 := by
        change toLex (x.1.val, x.2.val) ≤
          toLex (h.1.val, h.2.val) at hxh
        have hxle : x.1.val ≤ h.1.val :=
          Prod.Lex.monotone_fst _ _ hxh
        have hh0 : h.1.val = 0 := by rfl
        omega
      have hxFalse : decide (0 < x.1.val) = false := by simp [hx0]
      rw [hright, List.countP_cons, hxFalse] at hcount
      simp only [Bool.false_eq_true, ite_false, add_zero] at hcount
      have hpos : ∃ j ∈ xs, 0 < j.1.val := by
        by_contra hnone
        have hxsZero :
            xs.countP (fun j ↦ decide (0 < j.1.val)) = 0 :=
          List.countP_eq_zero.mpr (by
            intro j hj htrue
            exact hnone ⟨j, hj, of_decide_eq_true htrue⟩)
        omega
      have hcomb : adaptedRightComb n L data hn
          ⁅adaptedBasis n L data hn h,
            adaptedBasis n L data hn x⁆ xs = 0 :=
        adaptedRightComb_eq_zero_of_derived_of_exists_piece_pos
          n L data hn
            ⁅adaptedBasis n L data hn h,
              adaptedBasis n L data hn x⁆
            (lie_mem_derived n L _ _) xs hpos
      rw [hcomb, smul_zero]

/-- Consequently the whole grouped ordinary-`M` source primitive vanishes
before the terminal coordinate is taken. -/
theorem GoverningComponentSource.componentPBWPrimitive_eq_zero_of_origin_ordinaryMTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.originInputProfileTag n L data hn = .ordinaryM) :
    s.componentPBWPrimitive n L data hn = 0 := by
  rw [s.componentPBWPrimitive_eq_coefficient_smul n L data hn,
    s.pbwPrimitive_occurrence_value_eq_zero_of_origin_ordinaryMTag
      n L data hn htag, smul_zero]

/-- The all-weight-one full-commutator family has zero terminal read.  At
the target total weight its unique left-edge PBW correction is the complete
right-comb application of the triangular Smith head.  The triangular tail
overshoots the nilpotence cutoff in this weight-`n` context, so this head may
be replaced by the complete contextual relation; the terminal coordinate
then vanishes because it is a genuine relation. -/
theorem GoverningComponentSource.terminalPrimitiveRead_occurrence_value_eq_zero_of_origin_allWeightOneTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (htag : s.originInputProfileTag n L data hn = .allWeightOne) :
    terminalPrimitiveRead n L data hn s.occurrence.row.value = 0 := by
  classical
  by_cases htarget : s.originTotalWeight n L data hn = n + 1
  · have hprofile := s.originInputProfileTag_spec n L data hn
    rw [htag] at hprofile
    rcases s.component_eq_zero_or_zeroLeadingSmithHead
        n L data hn hprofile.1 with hzero | ⟨i, hroot, hcomponent⟩
    · rw [terminalPrimitiveRead, LinearMap.comp_apply,
        LinearMap.comp_apply,
        s.pbwPrimitive_occurrence_value_eq_zero_of_component_eq_zero
          n L data hn hzero, map_zero, map_zero]
    · have hrightEq := (s.terminal_eq_origin n L data hn).2.2.2.2
      have horiginLeft := (s.originHorizontalFrame n L data hn).2.1
      have hrightWeight :
          (s.right.map (adaptedWeightedBasis n L data hn).weight).sum = n := by
        unfold originTotalWeight originOrdinaryInputs at htarget
        rw [hprofile.1, horiginLeft, List.nil_append, ← hrightEq] at htarget
        omega
      have hrightNe : s.right ≠ [] := by
        intro hnil
        rw [hnil] at hrightWeight
        simp at hrightWeight
        omega
      obtain ⟨x, xs, hright⟩ := List.exists_cons_of_ne_nil hrightNe
      let h : AdaptedIndex n L data hn :=
        ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩
      let d : ℤ :=
        ((triangularSmith n L data 0 (by omega)).diagonal i : ℤ)
      let tag : TriangularRelationIndex n L :=
        ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩
      let c : RelationContext n L data hn :=
        RelationContext.rightComb n L data hn s.right
      have hordered : (x :: xs).Pairwise (· ≤ ·) := by
        rw [← hright]
        exact s.right_pairwise n L data hn
      have hc : RelationContext.weight n L data hn c = n := by
        simp only [c, RelationContext.rightComb_weight, hrightWeight]
      have hprimitive :
          pbwPrimitive n L data hn s.occurrence.row.value =
            if h ≤ x then 0 else
              d • adaptedRightComb n L data hn
                ⁅adaptedBasis n L data hn h,
                  adaptedBasis n L data hn x⁆ xs := by
        rw [s.occurrence_value_eq_component_mul_right n L data hn,
          hcomponent, hright, map_zsmul, smul_mul_assoc, map_zsmul]
        change d • pbwPrimitive n L data hn
            (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn h) *
              MarkedRow.basisWord n L data hn (x :: xs)) = _
        rw [pbwPrimitive_iota_basis_mul_basisWord_cons
          n L data hn h x xs hordered]
        by_cases hhx : h ≤ x <;> simp [hhx]
      by_cases hhx : h ≤ x
      · rw [terminalPrimitiveRead, LinearMap.comp_apply,
          LinearMap.comp_apply, hprimitive, if_pos hhx, map_zero, map_zero]
      · have hhead : d • adaptedBasis n L data hn h =
            FreeMetabelian.Free.weightIncl 0 (by omega)
              (d • triangularPieceBasis n L data 0 (by omega) i) := by
          rw [adaptedBasis_apply, map_zsmul]
          rfl
        have hprimitiveComb :
            pbwPrimitive n L data hn s.occurrence.row.value =
              RelationContext.apply n L data hn c
                (FreeMetabelian.Free.weightIncl 0 (by omega)
                  (d • triangularPieceBasis n L data 0 (by omega) i)) := by
          rw [hprimitive, if_neg hhx]
          calc
            d • adaptedRightComb n L data hn
                ⁅adaptedBasis n L data hn h,
                  adaptedBasis n L data hn x⁆ xs =
                adaptedRightComb n L data hn
                  (d • adaptedBasis n L data hn h) (x :: xs) := by
                    rw [adaptedRightComb, smul_lie,
                      adaptedRightComb_zsmul]
            _ = RelationContext.apply n L data hn c
                  (d • adaptedBasis n L data hn h) := by
                    simp only [c, RelationContext.rightComb_apply, hright]
            _ = _ := by rw [hhead]
        have hfull :=
          RelationContext.apply_triangularRelationOfIndex_eq_apply_head
            n L data hn tag (by rfl) c hc
        let rho : Relations n L data :=
          RelationContext.relation n L data hn c s.originRoot
        have hrho : pbwPrimitive n L data hn s.occurrence.row.value =
            (rho : FreeModel n L) := by
          rw [hprimitiveComb]
          change RelationContext.apply n L data hn c
              (FreeMetabelian.Free.weightIncl 0 (by omega)
                (d • triangularPieceBasis n L data 0 (by omega) i)) =
            RelationContext.apply n L data hn c (s.originRoot : FreeModel n L)
          rw [hroot]
          exact hfull.symm
        have hhomHead := weightIncl_weightProject_apply_rightComb_head
          n L data hn c hc
            (d • triangularPieceBasis n L data 0 (by omega) i)
        have hhom : FreeMetabelian.Free.weightIncl n (by omega)
              (FreeMetabelian.Free.weightProject n (by omega)
                (pbwPrimitive n L data hn s.occurrence.row.value)) =
            pbwPrimitive n L data hn s.occurrence.row.value := by
          rw [hprimitiveComb]
          exact hhomHead
        rw [terminalPrimitiveRead, LinearMap.comp_apply,
          LinearMap.comp_apply]
        exact topCoord_weightProject_eq_zero_of_fullRelation
          n L data (pbwPrimitive n L data hn s.occurrence.row.value)
            rho hhom hrho
  · exact s.terminalPrimitiveRead_occurrence_value_eq_zero_of_originWeight_ne
      n L data hn htarget

/-- Exhaustive stopping statement in the form used by the global
closed-square ledger.  If the terminal coordinate of a source occurrence is
nonzero, then the source is a target-weight relation-`M` copy and it lies on
exactly one of the outside-one, factor-two, or intermediate diagonal walls.
All other source tags and all wrong weights have already been killed by the
preceding stopping rules. -/
theorem GoverningComponentSource.relationM_wall_classification_of_terminalPrimitiveRead_ne_zero
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (hne : terminalPrimitiveRead n L data hn
      s.occurrence.row.value ≠ 0) :
    s.originInputProfileTag n L data hn = .relationM ∧
      s.originTotalWeight n L data hn = n + 1 ∧
      ((s.originActiveWeight n L data hn = n + 1 ∧
          s.originFactorCount n L data hn = 1) ∨
        (s.originActiveWeight n L data hn = n ∧
          s.originFactorCount n L data hn = 2) ∨
        ∃ k, s.originActiveWeight n L data hn = k ∧
          s.originFactorCount n L data hn = n - k + 2 ∧
          2 ≤ k ∧ k < n) := by
  cases htag : s.originInputProfileTag n L data hn with
  | relationM =>
      have htarget : s.originTotalWeight n L data hn = n + 1 := by
        by_contra hwrong
        exact hne
          (s.terminalPrimitiveRead_occurrence_value_eq_zero_of_originWeight_ne
            n L data hn hwrong)
      exact ⟨rfl, htarget,
        s.relationM_target_wall_classification
          n L data hn htag htarget⟩
  | ordinaryM =>
      exfalso
      apply hne
      rw [terminalPrimitiveRead, LinearMap.comp_apply,
        LinearMap.comp_apply,
        s.pbwPrimitive_occurrence_value_eq_zero_of_origin_ordinaryMTag
          n L data hn htag,
        map_zero, map_zero]
  | twoMInputs =>
      exfalso
      apply hne
      rw [terminalPrimitiveRead, LinearMap.comp_apply,
        LinearMap.comp_apply,
        s.pbwPrimitive_occurrence_value_eq_zero_of_origin_twoMTag
          n L data hn htag,
        map_zero, map_zero]
  | allWeightOne =>
      exfalso
      exact hne
        (s.terminalPrimitiveRead_occurrence_value_eq_zero_of_origin_allWeightOneTag
          n L data hn htag)

/-- An origin tag keeps or removes a whole grouped source frontier. -/
theorem GoverningComponentSource.componentPBWFrontier_filter_originTag
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w)
    (tag : OriginInputProfileTag) :
    (s.componentPBWFrontier n L data hn).filter (fun o ↦
        o.source.originInputProfileTag n L data hn = tag) =
      if s.originInputProfileTag n L data hn = tag then
        s.componentPBWFrontier n L data hn
      else 0 := by
  classical
  by_cases htag : s.originInputProfileTag n L data hn = tag
  · rw [if_pos htag, Finsupp.filter_eq_self_iff]
    intro o ho
    rw [s.componentPBWFrontier_source_eq_of_ne n L data hn o ho]
    exact htag
  · rw [if_neg htag, Finsupp.filter_eq_zero_iff]
    intro o hsource
    by_contra ho
    apply htag
    simpa [s.componentPBWFrontier_source_eq_of_ne n L data hn o ho]
      using hsource

/-- Terminal PBW occurrences partitioned by the input profile of their
homogeneous horizontal ancestor. -/
def GoverningWitness.globalComponentPBWOriginProfileOccurrences
    {a : L} (w : GoverningWitness n L data a)
    (tag : OriginInputProfileTag) :
    GoverningComponentPBWOccurrence n L data hn w →₀ ℤ :=
  (w.globalComponentPBWOccurrences n L data hn).filter fun o ↦
    o.source.originInputProfileTag n L data hn = tag

/-- Origin filtering commutes with the grouped-source sum. -/
theorem GoverningWitness.globalComponentPBWOriginProfileOccurrences_eq_sourceSum
    {a : L} (w : GoverningWitness n L data a)
    (tag : OriginInputProfileTag) :
    w.globalComponentPBWOriginProfileOccurrences n L data hn tag =
      (w.globalComponentSources n L data hn |>.map fun s ↦
        if s.originInputProfileTag n L data hn = tag then
          s.componentPBWFrontier n L data hn
        else 0).sum := by
  classical
  rw [GoverningWitness.globalComponentPBWOriginProfileOccurrences,
    GoverningWitness.globalComponentPBWOccurrences]
  induction w.globalComponentSources n L data hn with
  | nil =>
      rw [List.map_nil, List.sum_nil, Finsupp.filter_zero]
      simp only [List.map_nil, List.sum_nil]
  | cons s sources ih =>
      simp only [List.map_cons, List.sum_cons, Finsupp.filter_add, ih]
      rw [s.componentPBWFrontier_filter_originTag n L data hn tag]

/-- Complete primitive of one origin-profile family. -/
def GoverningWitness.globalComponentPBWOriginProfilePrimitive
    {a : L} (w : GoverningWitness n L data a)
    (tag : OriginInputProfileTag) : FreeModel n L :=
  (w.globalComponentPBWOriginProfileOccurrences n L data hn tag).sum
    fun o z ↦ z • pbwPrimitive n L data hn (o.state.value n L data hn)

/-- The origin-profile primitive remains a sum of whole homogeneous source
frontiers, never of separately interpreted coordinate descendants. -/
theorem GoverningWitness.globalComponentPBWOriginProfilePrimitive_eq_sourceSum
    {a : L} (w : GoverningWitness n L data a)
    (tag : OriginInputProfileTag) :
    w.globalComponentPBWOriginProfilePrimitive n L data hn tag =
      (w.globalComponentSources n L data hn |>.map fun s ↦
        if s.originInputProfileTag n L data hn = tag then
          s.componentPBWPrimitive n L data hn
        else 0).sum := by
  classical
  rw [GoverningWitness.globalComponentPBWOriginProfilePrimitive,
    w.globalComponentPBWOriginProfileOccurrences_eq_sourceSum
      n L data hn tag]
  induction w.globalComponentSources n L data hn with
  | nil => simp
  | cons s sources ih =>
      simp only [List.map_cons, List.sum_cons]
      change (Finsupp.linearCombination ℤ
          (fun o : GoverningComponentPBWOccurrence n L data hn w ↦
            pbwPrimitive n L data hn (o.state.value n L data hn)))
          ((if s.originInputProfileTag n L data hn = tag then
              s.componentPBWFrontier n L data hn else 0) +
            (sources.map fun t : GoverningComponentSource n L data hn w ↦
              if t.originInputProfileTag n L data hn = tag then
                t.componentPBWFrontier n L data hn else 0).sum) = _
      rw [map_add]
      by_cases htag : s.originInputProfileTag n L data hn = tag
      · simp only [if_pos htag]
        change s.componentPBWPrimitive n L data hn +
            (sources.map fun t : GoverningComponentSource n L data hn w ↦
              if t.originInputProfileTag n L data hn = tag then
                t.componentPBWFrontier n L data hn else 0).sum.sum
              (fun o z ↦ z • pbwPrimitive n L data hn
                (o.state.value n L data hn)) =
          s.componentPBWPrimitive n L data hn +
            (sources.map fun t : GoverningComponentSource n L data hn w ↦
              if t.originInputProfileTag n L data hn = tag then
                t.componentPBWPrimitive n L data hn else 0).sum
        rw [ih]
      · simp only [if_neg htag, map_zero, zero_add]
        exact ih

/-- The common terminal read on already collected one-factor primitives. -/
def terminalComponentRead : FreeModel n L →ₗ[ℤ]
    ZMod (2 ^ data.exponent) :=
  (topCoord n L data).comp
    (FreeMetabelian.Free.weightProject n (by omega))

/-- The complete ordinary-`M` origin family vanishes already in the free
metabelian model. -/
theorem GoverningWitness.globalComponentPBWOriginProfilePrimitive_ordinaryM_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    w.globalComponentPBWOriginProfilePrimitive n L data hn .ordinaryM = 0 := by
  rw [w.globalComponentPBWOriginProfilePrimitive_eq_sourceSum
    n L data hn .ordinaryM]
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  by_cases htag : s.originInputProfileTag n L data hn = .ordinaryM
  · rw [if_pos htag,
      s.componentPBWPrimitive_eq_zero_of_origin_ordinaryMTag
        n L data hn htag]
  · rw [if_neg htag]

/-- The terminal read of the complete all-weight-one origin family is zero;
the proof sums the full-relation replacement proved for each retained source
occurrence, with its original integer coefficient. -/
theorem GoverningWitness.terminalComponentRead_globalComponentPBWOriginProfilePrimitive_allWeightOne_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    terminalComponentRead n L data
        (w.globalComponentPBWOriginProfilePrimitive
          n L data hn .allWeightOne) = 0 := by
  rw [w.globalComponentPBWOriginProfilePrimitive_eq_sourceSum
    n L data hn .allWeightOne, map_list_sum]
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  rw [List.mem_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  by_cases htag : s.originInputProfileTag n L data hn = .allWeightOne
  · rw [if_pos htag,
      s.componentPBWPrimitive_eq_coefficient_smul n L data hn, map_zsmul]
    have hzero :=
      s.terminalPrimitiveRead_occurrence_value_eq_zero_of_origin_allWeightOneTag
        n L data hn htag
    change terminalComponentRead n L data
        (pbwPrimitive n L data hn s.occurrence.row.value) = 0 at hzero
    rw [hzero, smul_zero]
  · rw [if_neg htag, map_zero]

/-- The complete two-`M` origin family is silent. -/
theorem GoverningWitness.globalComponentPBWOriginProfilePrimitive_twoMInputs_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    w.globalComponentPBWOriginProfilePrimitive n L data hn .twoMInputs = 0 := by
  rw [w.globalComponentPBWOriginProfilePrimitive_eq_sourceSum
    n L data hn .twoMInputs]
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  by_cases htag : s.originInputProfileTag n L data hn = .twoMInputs
  · rw [if_pos htag,
      s.componentPBWPrimitive_eq_zero_of_origin_twoMTag n L data hn htag]
  · rw [if_neg htag]

/-- Applying the primitive linear map to the literal occurrence partition
gives the corresponding four-family decomposition of the complete terminal
component primitive. -/
theorem GoverningWitness.globalComponentPBWPrimitive_originProfile_partition
    {a : L} (w : GoverningWitness n L data a) :
    w.globalComponentPBWOriginProfilePrimitive n L data hn .relationM +
        w.globalComponentPBWOriginProfilePrimitive n L data hn .ordinaryM +
        w.globalComponentPBWOriginProfilePrimitive n L data hn .twoMInputs +
        w.globalComponentPBWOriginProfilePrimitive n L data hn .allWeightOne =
      w.globalComponentPBWPrimitive n L data hn := by
  have hpartition :
      w.globalComponentPBWOriginProfileOccurrences n L data hn .relationM +
          w.globalComponentPBWOriginProfileOccurrences n L data hn .ordinaryM +
          w.globalComponentPBWOriginProfileOccurrences n L data hn .twoMInputs +
          w.globalComponentPBWOriginProfileOccurrences n L data hn .allWeightOne =
        w.globalComponentPBWOccurrences n L data hn := by
    classical
    ext o
    cases htag : o.source.originInputProfileTag n L data hn <;>
      simp [GoverningWitness.globalComponentPBWOriginProfileOccurrences, htag]
  rw [GoverningWitness.globalComponentPBWOriginProfilePrimitive,
    GoverningWitness.globalComponentPBWOriginProfilePrimitive,
    GoverningWitness.globalComponentPBWOriginProfilePrimitive,
    GoverningWitness.globalComponentPBWOriginProfilePrimitive,
    GoverningWitness.globalComponentPBWPrimitive]
  change (Finsupp.linearCombination ℤ
        (fun o : GoverningComponentPBWOccurrence n L data hn w ↦
          pbwPrimitive n L data hn (o.state.value n L data hn)))
          (w.globalComponentPBWOriginProfileOccurrences
            n L data hn .relationM) +
      (Finsupp.linearCombination ℤ
        (fun o : GoverningComponentPBWOccurrence n L data hn w ↦
          pbwPrimitive n L data hn (o.state.value n L data hn)))
          (w.globalComponentPBWOriginProfileOccurrences
            n L data hn .ordinaryM) +
      (Finsupp.linearCombination ℤ
        (fun o : GoverningComponentPBWOccurrence n L data hn w ↦
          pbwPrimitive n L data hn (o.state.value n L data hn)))
          (w.globalComponentPBWOriginProfileOccurrences
            n L data hn .twoMInputs) +
      (Finsupp.linearCombination ℤ
        (fun o : GoverningComponentPBWOccurrence n L data hn w ↦
          pbwPrimitive n L data hn (o.state.value n L data hn)))
          (w.globalComponentPBWOriginProfileOccurrences
            n L data hn .allWeightOne) =
      (Finsupp.linearCombination ℤ
        (fun o : GoverningComponentPBWOccurrence n L data hn w ↦
          pbwPrimitive n L data hn (o.state.value n L data hn)))
          (w.globalComponentPBWOccurrences n L data hn)
  rw [← hpartition, map_add, map_add, map_add]

/-- Capstone silence statement for the corrected stopping-rule partition:
after the one terminal read, only the relation-`M` family can remain. -/
theorem GoverningWitness.terminalComponentRead_globalComponentPBWPrimitive_eq_relationM
    {a : L} (w : GoverningWitness n L data a) :
    terminalComponentRead n L data
        (w.globalComponentPBWPrimitive n L data hn) =
      terminalComponentRead n L data
        (w.globalComponentPBWOriginProfilePrimitive
          n L data hn .relationM) := by
  rw [← w.globalComponentPBWPrimitive_originProfile_partition
      n L data hn,
    w.globalComponentPBWOriginProfilePrimitive_ordinaryM_eq_zero
      n L data hn,
    w.globalComponentPBWOriginProfilePrimitive_twoMInputs_eq_zero
      n L data hn,
    add_zero, add_zero, map_add,
    w.terminalComponentRead_globalComponentPBWOriginProfilePrimitive_allWeightOne_eq_zero
      n L data hn, add_zero]

/-- The source-origin profiles are a literal disjoint exhaustive occurrence
partition of the complete terminal PBW ledger. -/
theorem GoverningWitness.globalComponentPBWOriginProfileOccurrences_partition
    {a : L} (w : GoverningWitness n L data a) :
    w.globalComponentPBWOriginProfileOccurrences n L data hn .relationM +
        w.globalComponentPBWOriginProfileOccurrences n L data hn .ordinaryM +
        w.globalComponentPBWOriginProfileOccurrences n L data hn .twoMInputs +
        w.globalComponentPBWOriginProfileOccurrences n L data hn .allWeightOne =
      w.globalComponentPBWOccurrences n L data hn := by
  classical
  ext o
  cases htag : o.source.originInputProfileTag n L data hn <;>
    simp [GoverningWitness.globalComponentPBWOriginProfileOccurrences, htag]

end

end LieRings.MetabelianVanishing
