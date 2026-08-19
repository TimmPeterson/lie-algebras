import LieRings.DimensionSubring.MetabelianVanishing.GlobalComparisonCell

/-!
# The finite uncut comparison trace

The horizontal occurrence collector supplies the well-founded spine of the
two-dimensional trace.  A comparison cell is adjoined at precisely those
labelled horizontal inputs at which the vertical operation is also
available.  Paths and coefficients are retained in the cell data; equal
underlying rows reached through different children are not combined.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.DegreeFive

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalSaturatedTraceFintype : Fintype L :=
  Fintype.ofFinite L

/-- One path-labelled cell of the uncut global trace.  Both partial
replacement equalities are stored, so availability is syntactic and cannot
be inferred later from a possibly cancelling evaluated sum. -/
structure LabelledComparisonCell where
  path : List ℕ
  coefficient : ℤ
  input : ProvenancedRow n L data hn
  horizontalOutputs : List (ℤ × ProvenancedRow n L data hn)
  horizontal_eq : horizontalExpansion n L data hn input =
    some horizontalOutputs
  verticalOutputs : List (ℤ × ProvenancedRow n L data hn)
  vertical_eq : verticalExpansion n L data hn input = some verticalOutputs

namespace LabelledComparisonCell

/-- Forget the route metadata only when forming the algebraic comparison
cell.  The inherited integer coefficient remains in its base list. -/
def cell (c : LabelledComparisonCell n L data hn) :
    ComparisonCell n L data hn where
  base := Finsupp.single c.input c.coefficient

/-- Canonical PBW boundary of one labelled cell. -/
def canonicalBoundary (c : LabelledComparisonCell n L data hn) :
    MvPolynomial (AdaptedIndex n L data hn) ℤ :=
  canonicalPlacedExpansion n L data hn
    (c.cell n L data hn).boundary

@[simp] theorem canonicalBoundary_eq_zero
    (c : LabelledComparisonCell n L data hn) :
    c.canonicalBoundary n L data hn = 0 :=
  ComparisonCell.canonicalPlacedExpansion_boundary_eq_zero
    n L data hn (c.cell n L data hn)

/-- A numbered horizontal output is internal precisely when both operations
remain available on that literal child.  This is a property of the child
occurrence, not of its value after equal rows have been combined. -/
def IsInternalHorizontalSuccessor
    (c : LabelledComparisonCell n L data hn)
    (i : Fin c.horizontalOutputs.length) : Prop :=
  (horizontalExpansion n L data hn (c.horizontalOutputs.get i).2).isSome ∧
    (verticalExpansion n L data hn (c.horizontalOutputs.get i).2).isSome

/-- Literal adjacency data for the `i`th horizontal coefficient copy.  The
path equation prevents two equal-valued outputs from being identified. -/
def IsHorizontalSuccessor
    (c d : LabelledComparisonCell n L data hn)
    (i : Fin c.horizontalOutputs.length) : Prop :=
  d.path = i.1 :: c.path ∧
    d.coefficient = c.coefficient * (c.horizontalOutputs.get i).1 ∧
    d.input = (c.horizontalOutputs.get i).2

/-- The adjacent comparison cell determined by an internal numbered
horizontal successor. -/
def horizontalSuccessorCell
    (c : LabelledComparisonCell n L data hn)
    (i : Fin c.horizontalOutputs.length)
    (horizontalOutputs : List (ℤ × ProvenancedRow n L data hn))
    (hhorizontal : horizontalExpansion n L data hn
      (c.horizontalOutputs.get i).2 = some horizontalOutputs)
    (verticalOutputs : List (ℤ × ProvenancedRow n L data hn))
    (hvertical : verticalExpansion n L data hn
      (c.horizontalOutputs.get i).2 = some verticalOutputs) :
    LabelledComparisonCell n L data hn where
  path := i.1 :: c.path
  coefficient := c.coefficient * (c.horizontalOutputs.get i).1
  input := (c.horizontalOutputs.get i).2
  horizontalOutputs := horizontalOutputs
  horizontal_eq := hhorizontal
  verticalOutputs := verticalOutputs
  vertical_eq := hvertical

/-- The path, propagated coefficient, and input row uniquely determine an
adjacent cell.  The remaining fields are forced by the two deterministic
partial operations. -/
theorem horizontalSuccessorCell_unique
    (c : LabelledComparisonCell n L data hn)
    (i : Fin c.horizontalOutputs.length)
    (horizontalOutputs : List (ℤ × ProvenancedRow n L data hn))
    (hhorizontal : horizontalExpansion n L data hn
      (c.horizontalOutputs.get i).2 = some horizontalOutputs)
    (verticalOutputs : List (ℤ × ProvenancedRow n L data hn))
    (hvertical : verticalExpansion n L data hn
      (c.horizontalOutputs.get i).2 = some verticalOutputs)
    (d : LabelledComparisonCell n L data hn)
    (hpath : d.path = i.1 :: c.path)
    (hcoefficient : d.coefficient =
      c.coefficient * (c.horizontalOutputs.get i).1)
    (hinput : d.input = (c.horizontalOutputs.get i).2) :
    d = c.horizontalSuccessorCell n L data hn i horizontalOutputs
      hhorizontal verticalOutputs hvertical := by
  rcases d with ⟨path, coefficient, input, dHorizontalOutputs,
    dHorizontalEq, dVerticalOutputs, dVerticalEq⟩
  simp only at hpath hcoefficient hinput ⊢
  subst path
  subst coefficient
  subst input
  have hhorizontalOutputs : dHorizontalOutputs = horizontalOutputs := by
    rw [dHorizontalEq] at hhorizontal
    exact Option.some.inj hhorizontal
  have hverticalOutputs : dVerticalOutputs = verticalOutputs := by
    rw [dVerticalEq] at hvertical
    exact Option.some.inj hvertical
  subst dHorizontalOutputs
  subst dVerticalOutputs
  rfl

end LabelledComparisonCell

/-- Adjoin the comparison square at one horizontal trace cell exactly when
the vertical operation is also available. -/
def comparisonCellOfHorizontal?
    (c : CollectorRewriteCell (horizontalCollector n L data hn)) :
    Option (LabelledComparisonCell n L data hn) :=
  match h : verticalExpansion n L data hn c.input with
  | none => none
  | some outputs => some
      { path := c.path
        coefficient := c.coefficient
        input := c.input
        horizontalOutputs := c.outputs
        horizontal_eq := c.expansion_eq
        verticalOutputs := outputs
        vertical_eq := h }

/-- Finite saturated uncut trace below one distinctly labelled row.  The
underlying `collectorTrace` is defined by well-founded recursion on the
lexicographic row measure and visits every horizontal output occurrence. -/
def uncutComparisonTrace (r : ProvenancedRow n L data hn)
    (path : List ℕ) (coefficient : ℤ) :
    List (LabelledComparisonCell n L data hn) :=
  (collectorTrace (horizontalCollector n L data hn) r path coefficient).filterMap
    (comparisonCellOfHorizontal? n L data hn)

/-- Every numbered child on which both operations remain available is
literally the root of its uniquely numbered recursive subtrace. -/
theorem LabelledComparisonCell.horizontalSuccessorCell_mem_uncutTrace
    (c : LabelledComparisonCell n L data hn)
    (i : Fin c.horizontalOutputs.length)
    (horizontalOutputs : List (ℤ × ProvenancedRow n L data hn))
    (hhorizontal : horizontalExpansion n L data hn
      (c.horizontalOutputs.get i).2 = some horizontalOutputs)
    (verticalOutputs : List (ℤ × ProvenancedRow n L data hn))
    (hvertical : verticalExpansion n L data hn
      (c.horizontalOutputs.get i).2 = some verticalOutputs) :
    c.horizontalSuccessorCell n L data hn i horizontalOutputs hhorizontal
        verticalOutputs hvertical ∈
      uncutComparisonTrace n L data hn c.input c.path c.coefficient := by
  classical
  let childRewriteCell :
      CollectorRewriteCell (horizontalCollector n L data hn) :=
    { path := i.1 :: c.path
      coefficient := c.coefficient * (c.horizontalOutputs.get i).1
      input := (c.horizontalOutputs.get i).2
      outputs := horizontalOutputs
      expansion_eq := hhorizontal }
  rw [uncutComparisonTrace, List.mem_filterMap]
  refine ⟨childRewriteCell, ?_, ?_⟩
  · rw [collectorTrace_eq_of_expansion_some
      (horizontalCollector n L data hn) c.input c.path c.coefficient
        c.horizontalOutputs c.horizontal_eq]
    simp only [List.mem_cons]
    right
    rw [List.mem_flatten]
    refine ⟨collectorTrace (horizontalCollector n L data hn)
      (c.horizontalOutputs.get i).2 (i.1 :: c.path)
      (c.coefficient * (c.horizontalOutputs.get i).1), ?_, ?_⟩
    · rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    · rw [collectorTrace_eq_of_expansion_some
          (horizontalCollector n L data hn)
          (c.horizontalOutputs.get i).2 (i.1 :: c.path)
          (c.coefficient * (c.horizontalOutputs.get i).1)
          horizontalOutputs hhorizontal]
      exact List.mem_cons_self
  · unfold comparisonCellOfHorizontal?
    split
    · rename_i he
      rw [hvertical] at he
      contradiction
    · rename_i outputs he
      have houtputs : outputs = verticalOutputs := by
        rw [hvertical] at he
        exact Option.some.inj he.symm
      subst outputs
      rfl

/-- Saturation attaches every non-cut numbered successor to exactly one
adjacent cell.  Existence is literal membership in the recursive subtrace;
uniqueness follows from the numbered path and determinism of both partial
operations. -/
theorem LabelledComparisonCell.existsUnique_horizontalSuccessor
    (c : LabelledComparisonCell n L data hn)
    (i : Fin c.horizontalOutputs.length)
    (hi : c.IsInternalHorizontalSuccessor n L data hn i) :
    ∃! d : LabelledComparisonCell n L data hn,
      c.IsHorizontalSuccessor n L data hn d i ∧
        d ∈ uncutComparisonTrace n L data hn c.input c.path c.coefficient := by
  classical
  cases hhorizontal : horizontalExpansion n L data hn
      (c.horizontalOutputs.get i).2 with
  | none =>
      have hfalse := hi.1
      rw [hhorizontal] at hfalse
      simp at hfalse
  | some horizontalOutputs =>
      cases hvertical : verticalExpansion n L data hn
          (c.horizontalOutputs.get i).2 with
      | none =>
          have hfalse := hi.2
          rw [hvertical] at hfalse
          simp at hfalse
      | some verticalOutputs =>
          let d := c.horizontalSuccessorCell n L data hn i
            horizontalOutputs hhorizontal verticalOutputs hvertical
          refine ⟨d, ?_, ?_⟩
          · constructor
            · exact ⟨rfl, rfl, rfl⟩
            · exact c.horizontalSuccessorCell_mem_uncutTrace n L data hn i
                horizontalOutputs hhorizontal verticalOutputs hvertical
          · intro e he
            rcases he.1 with ⟨hpath, hcoefficient, hinput⟩
            exact c.horizontalSuccessorCell_unique n L data hn i
              horizontalOutputs hhorizontal verticalOutputs hvertical e
              hpath hcoefficient hinput

/-- Start the uncut trace from a literal signed occurrence list.  The root
index is appended to the ancestry word before recursion, so duplicate rows
in the input remain distinct. -/
def uncutComparisonTraceOfList
  (initial : List (ℤ × ProvenancedRow n L data hn)) :
    List (LabelledComparisonCell n L data hn) :=
  (List.ofFn fun i : Fin initial.length ↦
    uncutComparisonTrace n L data hn (initial.get i).2 [i.1]
      (initial.get i).1).flatten

/-- Canonically expanded sum of the boundaries of a finite cell list. -/
def canonicalTraceBoundary
    (cells : List (LabelledComparisonCell n L data hn)) :
    MvPolynomial (AdaptedIndex n L data hn) ℤ :=
  (cells.map fun c ↦ c.canonicalBoundary n L data hn).sum

/-- Uncut finite Stokes: every comparison cell has zero canonical boundary,
hence so does the complete finite saturated trace. -/
theorem canonicalTraceBoundary_eq_zero
    (cells : List (LabelledComparisonCell n L data hn)) :
    canonicalTraceBoundary n L data hn cells = 0 := by
  classical
  rw [canonicalTraceBoundary]
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  exact c.canonicalBoundary_eq_zero n L data hn

theorem canonicalTraceBoundary_uncutComparisonTraceOfList_eq_zero
    (initial : List (ℤ × ProvenancedRow n L data hn)) :
    canonicalTraceBoundary n L data hn
        (uncutComparisonTraceOfList n L data hn initial) = 0 :=
  canonicalTraceBoundary_eq_zero n L data hn _

end


end LieRings.MetabelianVanishing
