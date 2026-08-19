import LieRings.DimensionSubring.MetabelianVanishing.GlobalFiniteStokes

/-!
# Vertical frontiers of horizontal successor copies

The left incidence `V (H R)` contains two kinds of horizontal children.
Internal lower-mark children are roots of adjacent comparison cells.  The
remaining children are external and must still undergo the complete vertical
pass.  In particular, homogeneous truncation children on a support diagonal
live in this ledger; they are not contained in the `V R` ledger.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.DegreeFive

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalHorizontalFrontierFintype : Fintype L :=
  Fintype.ofFinite L

/-- One vertically normalized occurrence below a numbered horizontal child.
The dependent child index records the exact output copy of `H`. -/
structure CellHorizontalVerticalOccurrence where
  parent : GoverningComparisonCell n L data hn
  childIndex : Fin parent.cell.horizontalOutputs.length
  verticalPath : List ℕ
  row : ProvenancedRow n L data hn

noncomputable instance :
    DecidableEq (CellHorizontalVerticalOccurrence n L data hn) :=
  Classical.decEq _

namespace GoverningComparisonCell

/-- Embed a vertical route below one fixed numbered horizontal child. -/
def horizontalVerticalOccurrenceEmbedding
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length)
    (o : CollectorOccurrence (ProvenancedRow n L data hn)) :
    CellHorizontalVerticalOccurrence n L data hn :=
  { parent := c
    childIndex := i
    verticalPath := o.1
    row := o.2 }

theorem horizontalVerticalOccurrenceEmbedding_injective
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length) :
    Function.Injective
      (horizontalVerticalOccurrenceEmbedding n L data hn c i) := by
  intro x y h
  cases x with
  | mk xp xr =>
    cases y with
    | mk yp yr =>
      have hpath : xp = yp := congrArg
        (fun z : CellHorizontalVerticalOccurrence n L data hn ↦
          z.verticalPath) h
      have hrow : xr = yr := congrArg
        (fun z : CellHorizontalVerticalOccurrence n L data hn ↦ z.row) h
      subst yp
      subst yr
      rfl

/-- Complete vertical frontier below one numbered horizontal child. -/
def horizontalSuccessorVerticalFrontier
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length) :
    CellHorizontalVerticalOccurrence n L data hn →₀ ℤ :=
  Finsupp.mapDomain
    (horizontalVerticalOccurrenceEmbedding n L data hn c i)
    (collectorFrontier (verticalCollector n L data hn)
      (c.cell.horizontalOutputs.get i).2 (i.1 :: c.cell.path)
      (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1))

/-- Forgetting route labels gives the vertical normal form of exactly this
numbered coefficient copy. -/
theorem forget_horizontalSuccessorVerticalFrontier
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length) :
    (c.horizontalSuccessorVerticalFrontier n L data hn i).sum
        (fun o z ↦ z • Finsupp.single o.row (1 : ℤ)) =
      verticalOperation n L data hn
        (Finsupp.single (c.cell.horizontalOutputs.get i).2
          (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1)) := by
  classical
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.sum_mapDomain_index_inj
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)]
  change
    (collectorFrontier (verticalCollector n L data hn)
      (c.cell.horizontalOutputs.get i).2 (i.1 :: c.cell.path)
      (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1)).sum
        (fun o z ↦ z • Finsupp.single o.2 (1 : ℤ)) = _
  have hforget := forgetCollectorPaths_frontier
    (verticalCollector n L data hn) (c.cell.horizontalOutputs.get i).2
      (i.1 :: c.cell.path)
      (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1)
  change forgetCollectorPaths
      (collectorFrontier (verticalCollector n L data hn)
        (c.cell.horizontalOutputs.get i).2 (i.1 :: c.cell.path)
        (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1)) = _
    at hforget
  rw [verticalOperation]
  simpa [forgetCollectorPaths, Finsupp.lmapDomain_apply,
    Finsupp.smul_single] using hforget

/-- Every nonzero normalized occurrence below a fixed horizontal child is
terminal for the complete vertical pass. -/
theorem horizontalSuccessorVerticalFrontier_terminal_of_ne
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : c.horizontalSuccessorVerticalFrontier n L data hn i o ≠ 0) :
    verticalExpansion n L data hn o.row = none := by
  have hs : o ∈ (c.horizontalSuccessorVerticalFrontier n L data hn i).support :=
    Finsupp.mem_support_iff.mpr ho
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_support_of_injective
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  rw [horizontalSuccessorVerticalFrontier,
    Finsupp.mapDomain_apply
      (horizontalVerticalOccurrenceEmbedding_injective n L data hn c i)] at ho
  exact collectorFrontier_terminal_of_ne
    (verticalCollector n L data hn) (c.cell.horizontalOutputs.get i).2
      (i.1 :: c.cell.path)
      (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1) source ho

end GoverningComparisonCell

private theorem exists_list_coefficient_ne_zero_horizontal
    {I : Type*} (rows : List (I →₀ ℤ)) (i : I)
    (h : rows.sum i ≠ 0) :
    ∃ row ∈ rows, row i ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h
  let ev : (I →₀ ℤ) →+ ℤ := Finsupp.applyAddHom i
  change ev rows.sum = 0
  rw [map_list_sum]
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨row, hrow, rfl⟩ := hz
  exact hall row hrow

/-- Complete `V(HR)` occurrence ledger, before internal successors are
removed by their unique adjacent-cell gluing. -/
def GoverningWitness.globalHorizontalVerticalOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    CellHorizontalVerticalOccurrence n L data hn →₀ ℤ :=
  (w.globalLabelledComparisonTrace n L data hn |>.map fun c ↦
    (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i).sum).sum

/-- Every occurrence of the complete `V(HR)` ledger is vertically terminal,
before internal and external horizontal children are separated. -/
theorem GoverningWitness.globalHorizontalVerticalOccurrence_terminal_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0) :
    verticalExpansion n L data hn o.row = none := by
  let childFrontiers (c : GoverningComparisonCell n L data hn) :
      List (CellHorizontalVerticalOccurrence n L data hn →₀ ℤ) :=
    List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i
  let cellFrontier (c : GoverningComparisonCell n L data hn) :
      CellHorizontalVerticalOccurrence n L data hn →₀ ℤ :=
    (childFrontiers c).sum
  rw [GoverningWitness.globalHorizontalVerticalOccurrences] at ho
  change ((w.globalLabelledComparisonTrace n L data hn).map
    cellFrontier).sum o ≠ 0 at ho
  obtain ⟨cellSum, hcellSum, hcellSumO⟩ :=
    exists_list_coefficient_ne_zero_horizontal
      ((w.globalLabelledComparisonTrace n L data hn).map cellFrontier) o ho
  rw [List.mem_map] at hcellSum
  obtain ⟨c, hc, rfl⟩ := hcellSum
  change (childFrontiers c).sum o ≠ 0 at hcellSumO
  obtain ⟨front, hfront, hfrontO⟩ :=
    exists_list_coefficient_ne_zero_horizontal
      (childFrontiers c) o hcellSumO
  change front ∈ (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i) at hfront
  rw [List.mem_ofFn] at hfront
  obtain ⟨i, rfl⟩ := hfront
  exact c.horizontalSuccessorVerticalFrontier_terminal_of_ne
    n L data hn i o hfrontO

namespace CellHorizontalVerticalOccurrence

/-- The horizontal child below this occurrence is glued to another
comparison cell exactly in the internal case. -/
def IsInternal (o : CellHorizontalVerticalOccurrence n L data hn) : Prop :=
  o.parent.cell.IsInternalHorizontalSuccessor n L data hn o.childIndex

/-- External horizontal children are precisely the copies left after the
unique internal right-edge gluings. -/
def IsExternal (o : CellHorizontalVerticalOccurrence n L data hn) : Prop :=
  ¬o.IsInternal n L data hn

/-- The child selected by this occurrence is a homogeneous truncation child,
as opposed to the lower-mark child. -/
def IsHomogeneousChild
    (o : CellHorizontalVerticalOccurrence n L data hn) : Prop :=
  ∃ root context mark left right,
    (o.parent.cell.horizontalOutputs.get o.childIndex).2 =
      ProvenancedRow.component root context mark left right

/-- Horizontal side of the intermediate `(m_k,k)` cut.  The source row,
not its eventual one-factor value, determines the diagonal. -/
def IsDiagonalHorizontal
    (o : CellHorizontalVerticalOccurrence n L data hn) (k : ℕ) : Prop :=
  o.IsExternal n L data hn ∧ o.IsHomogeneousChild n L data hn ∧
    (o.parent.cell.horizontalOutputs.get o.childIndex).2.factorCount
        n L data hn = n - k + 2 ∧
    (o.parent.cell.horizontalOutputs.get o.childIndex).2.activeWeight
        n L data hn = k ∧
    2 ≤ k ∧ k < n

noncomputable instance (o : CellHorizontalVerticalOccurrence n L data hn) :
    Decidable (o.IsInternal n L data hn) := Classical.propDecidable _

noncomputable instance (o : CellHorizontalVerticalOccurrence n L data hn) :
    Decidable (o.IsExternal n L data hn) := Classical.propDecidable _

noncomputable instance (o : CellHorizontalVerticalOccurrence n L data hn) :
    Decidable (o.IsHomogeneousChild n L data hn) := Classical.propDecidable _

noncomputable instance (o : CellHorizontalVerticalOccurrence n L data hn)
    (k : ℕ) : Decidable (o.IsDiagonalHorizontal n L data hn k) :=
  Classical.propDecidable _

end CellHorizontalVerticalOccurrence

/-- Signed external `V(HR)` ledger.  Equal normalized rows reached through
different horizontal or vertical paths remain distinct subtype indices. -/
def GoverningWitness.externalHorizontalOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    {o : CellHorizontalVerticalOccurrence n L data hn //
      o.IsExternal n L data hn} →₀ ℤ :=
  (w.globalHorizontalVerticalOccurrences n L data hn).sum fun o z ↦
    if h : o.IsExternal n L data hn then Finsupp.single ⟨o, h⟩ z else 0

/-- Signed horizontal side of the intermediate diagonal cut. -/
def GoverningWitness.diagonalHorizontalOccurrences
    {a : L} (w : GoverningWitness n L data a) (k : ℕ) :
    {o : CellHorizontalVerticalOccurrence n L data hn //
      o.IsDiagonalHorizontal n L data hn k} →₀ ℤ :=
  (w.globalHorizontalVerticalOccurrences n L data hn).sum fun o z ↦
    if h : o.IsDiagonalHorizontal n L data hn k then
      Finsupp.single ⟨o, h⟩ z
    else 0

end

end LieRings.MetabelianVanishing
