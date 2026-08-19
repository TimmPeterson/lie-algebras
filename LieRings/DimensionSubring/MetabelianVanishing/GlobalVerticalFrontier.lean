import LieRings.DimensionSubring.MetabelianVanishing.GlobalInitialTrace
import LieRings.DimensionSubring.MetabelianVanishing.GlobalInternalGluing

/-!
# Occurrence-level vertical frontiers and the two designated cuts

For every comparison cell we now run the complete deterministic vertical
pass without combining its child paths.  This is the literal lower route
`V R` of the corrected proof.  The factor-two wall and every intermediate
support diagonal are selected from this one common occurrence ledger.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.DegreeFive

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalVerticalFrontierFintype : Fintype L :=
  Fintype.ofFinite L

namespace ProvenancedRow

/-- Syntactic assertion that a provenance row still carries a genuine full
relation mark, rather than one homogeneous component of that relation. -/
def IsMarked : ProvenancedRow n L data hn → Prop
  | .marked _ _ _ _ _ => True
  | .component _ _ _ _ _ => False

/-- Syntactic normality for the complete vertical pass: a marked relation
has reached the left wall, while a homogeneous component has returned to
the right wall. -/
def IsVerticalNormal : ProvenancedRow n L data hn → Prop
  | .marked _ _ _ _ right => right = []
  | .component _ _ _ left _ => left = []

noncomputable instance (r : ProvenancedRow n L data hn) :
    Decidable (r.IsVerticalNormal n L data hn) :=
  Classical.propDecidable _

theorem verticalExpansion_eq_none_iff
    (r : ProvenancedRow n L data hn) :
    verticalExpansion n L data hn r = none ↔
      r.IsVerticalNormal n L data hn := by
  cases r with
  | marked root context mark left right =>
      cases right <;> simp [verticalExpansion, IsVerticalNormal]
  | component root context mark left right =>
      cases hleft : left.reverse with
      | nil =>
          have : left = [] := by
            simpa using congrArg List.reverse hleft
          subst left
          simp [verticalExpansion, IsVerticalNormal]
      | cons x xs =>
          have hne : left ≠ [] := by
            intro h
            subst left
            simp at hleft
          simp [verticalExpansion, IsVerticalNormal, hleft, hne]

/-- A vertical transfer never turns a genuine marked relation into one of
its homogeneous component rows. -/
theorem verticalExpansion_preserves_isMarked
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows)
    (hr : r.IsMarked n L data hn) :
    ∀ q ∈ rows, q.2.IsMarked n L data hn := by
  cases r with
  | component => simp [IsMarked] at hr
  | marked root context mark left right =>
      cases right with
      | nil => simp [verticalExpansion] at h
      | cons x rest =>
          rw [show rows =
              [(1, .marked root context mark (left ++ [x]) rest),
                (1, .marked root (RelationContext.lieRight context x)
                  mark left rest)] by
            simpa [verticalExpansion] using (Option.some.inj h).symm]
          simp [IsMarked]

end ProvenancedRow

/-- A vertical normal-form occurrence together with the comparison cell
from which its route starts. -/
structure CellVerticalOccurrence where
  parent : GoverningComparisonCell n L data hn
  verticalPath : List ℕ
  row : ProvenancedRow n L data hn

noncomputable instance :
    DecidableEq (CellVerticalOccurrence n L data hn) :=
  Classical.decEq _

namespace GoverningComparisonCell

/-- Availability of the horizontal operation certifies that the input of a
comparison cell is a genuinely marked row. -/
theorem input_isMarked (c : GoverningComparisonCell n L data hn) :
    c.cell.input.IsMarked n L data hn := by
  cases hrow : c.cell.input with
  | component =>
      have hhorizontal := c.cell.horizontal_eq
      rw [hrow] at hhorizontal
      simp [horizontalExpansion] at hhorizontal
  | marked => trivial

/-- Embed a vertical child path under its uniquely labelled parent cell. -/
def verticalOccurrenceEmbedding
    (c : GoverningComparisonCell n L data hn)
    (o : CollectorOccurrence (ProvenancedRow n L data hn)) :
    CellVerticalOccurrence n L data hn :=
  { parent := c, verticalPath := o.1, row := o.2 }

theorem verticalOccurrenceEmbedding_injective
    (c : GoverningComparisonCell n L data hn) :
    Function.Injective (verticalOccurrenceEmbedding n L data hn c) := by
  intro x y h
  cases x with
  | mk xp xr =>
    cases y with
    | mk yp yr =>
      have hfields : xp = yp ∧ xr = yr := by
        simpa only [verticalOccurrenceEmbedding,
          CellVerticalOccurrence.mk.injEq, true_and] using h
      rcases hfields with ⟨rfl, rfl⟩
      rfl

/-- Complete vertical occurrence frontier below one comparison-cell input.
The parent path is prefixed to the vertical path, so the same normal row
reached from different comparison cells remains a different occurrence. -/
def verticalOccurrenceFrontier
    (c : GoverningComparisonCell n L data hn) :
    CellVerticalOccurrence n L data hn →₀ ℤ :=
  Finsupp.mapDomain (verticalOccurrenceEmbedding n L data hn c)
    (collectorFrontier (verticalCollector n L data hn) c.cell.input c.cell.path
      c.cell.coefficient)

/-- Forgetting the vertical paths and parent label gives exactly the
complete vertical operation used in the comparison cell. -/
theorem forget_verticalOccurrenceFrontier
    (c : GoverningComparisonCell n L data hn) :
    (c.verticalOccurrenceFrontier n L data hn).sum (fun o z ↦
      z • Finsupp.single o.row (1 : ℤ)) =
      verticalOperation n L data hn (c.cell.cell n L data hn).base := by
  classical
  rw [verticalOccurrenceFrontier,
    Finsupp.sum_mapDomain_index_inj
      (verticalOccurrenceEmbedding_injective n L data hn c)]
  change
    (collectorFrontier (verticalCollector n L data hn) c.cell.input c.cell.path
      c.cell.coefficient).sum (fun o z ↦
        z • Finsupp.single o.2 (1 : ℤ)) = _
  have hforget := forgetCollectorPaths_frontier
    (verticalCollector n L data hn) c.cell.input c.cell.path c.cell.coefficient
  change forgetCollectorPaths
      (collectorFrontier (verticalCollector n L data hn) c.cell.input c.cell.path
        c.cell.coefficient) = _ at hforget
  rw [verticalOperation, LabelledComparisonCell.cell]
  simpa [forgetCollectorPaths, Finsupp.lmapDomain_apply,
    Finsupp.smul_single] using hforget

/-- Reading the lower-mark summand on the complete path-labelled vertical
frontier gives exactly the inherited coefficient times the lower-mark value
of the cell input.  All lower-context correction paths are retained in the
sum on the left. -/
theorem lowerMarkedValue_verticalOccurrenceFrontier
    (c : GoverningComparisonCell n L data hn) :
    (c.verticalOccurrenceFrontier n L data hn).sum (fun o z ↦
        z • lowerMarkedValue n L data hn o.row) =
      c.cell.coefficient •
        lowerMarkedValue n L data hn c.cell.input := by
  classical
  have hforget := congrArg (lowerMarkedLinear n L data hn)
    (c.forget_verticalOccurrenceFrontier n L data hn)
  rw [map_finsuppSum] at hforget
  calc
    _ = c.cell.coefficient •
        lowerMarkedLinear n L data hn
          ((verticalCollector n L data hn).normalForm c.cell.input) := by
      simpa only [map_zsmul, lowerMarkedLinear,
        Finsupp.linearCombination_single, one_smul, verticalOperation,
        LabelledComparisonCell.cell] using hforget
    _ = _ := by rw [lowerMarkedLinear_normalForm]

/-- The analogous frontier formula for the complementary homogeneous
summand. -/
theorem horizontalComponentValue_verticalOccurrenceFrontier
    (c : GoverningComparisonCell n L data hn) :
    (c.verticalOccurrenceFrontier n L data hn).sum (fun o z ↦
        z • horizontalComponentValue n L data hn o.row) =
      c.cell.coefficient •
        horizontalComponentValue n L data hn c.cell.input := by
  classical
  have hforget := congrArg (horizontalComponentLinear n L data hn)
    (c.forget_verticalOccurrenceFrontier n L data hn)
  rw [map_finsuppSum] at hforget
  calc
    _ = c.cell.coefficient •
        horizontalComponentLinear n L data hn
          ((verticalCollector n L data hn).normalForm c.cell.input) := by
      simpa only [map_zsmul, horizontalComponentLinear,
        Finsupp.linearCombination_single, one_smul, verticalOperation,
        LabelledComparisonCell.cell] using hforget
    _ = _ := by rw [horizontalComponentLinear_normalForm]

/-- Every nonzero occurrence in a cell's vertical frontier is vertically
terminal before any two-dimensional cut is applied. -/
theorem verticalOccurrenceFrontier_terminal_of_ne
    (c : GoverningComparisonCell n L data hn)
    (o : CollectorOccurrence (ProvenancedRow n L data hn))
    (ho : c.verticalOccurrenceFrontier n L data hn
        (verticalOccurrenceEmbedding n L data hn c o) ≠ 0) :
    verticalExpansion n L data hn o.2 = none := by
  rw [verticalOccurrenceFrontier,
    Finsupp.mapDomain_apply
      (verticalOccurrenceEmbedding_injective n L data hn c)] at ho
  exact collectorFrontier_terminal_of_ne
    (verticalCollector n L data hn) c.cell.input c.cell.path c.cell.coefficient o ho

/-- Intrinsic form of the preceding theorem, for an arbitrary labelled
occurrence known to occur below `c`. -/
theorem verticalOccurrenceFrontier_row_terminal_of_ne
    (c : GoverningComparisonCell n L data hn)
    (o : CellVerticalOccurrence n L data hn)
    (ho : c.verticalOccurrenceFrontier n L data hn o ≠ 0) :
    verticalExpansion n L data hn o.row = none := by
  have hs : o ∈ (c.verticalOccurrenceFrontier n L data hn).support :=
    Finsupp.mem_support_iff.mpr ho
  rw [verticalOccurrenceFrontier,
    Finsupp.mapDomain_support_of_injective
      (verticalOccurrenceEmbedding_injective n L data hn c)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  rw [verticalOccurrenceFrontier,
    Finsupp.mapDomain_apply
      (verticalOccurrenceEmbedding_injective n L data hn c)] at ho
  exact collectorFrontier_terminal_of_ne
    (verticalCollector n L data hn) c.cell.input c.cell.path c.cell.coefficient source ho

/-- Every supported occurrence in the complete vertical pass below a
comparison cell still carries its genuine full relation mark. -/
theorem verticalOccurrenceFrontier_row_isMarked_of_ne
    (c : GoverningComparisonCell n L data hn)
    (o : CellVerticalOccurrence n L data hn)
    (ho : c.verticalOccurrenceFrontier n L data hn o ≠ 0) :
    o.row.IsMarked n L data hn := by
  have hs : o ∈ (c.verticalOccurrenceFrontier n L data hn).support :=
    Finsupp.mem_support_iff.mpr ho
  rw [verticalOccurrenceFrontier,
    Finsupp.mapDomain_support_of_injective
      (verticalOccurrenceEmbedding_injective n L data hn c)] at hs
  obtain ⟨source, hsource, hsourceEq⟩ := Finset.mem_image.mp hs
  subst o
  rw [verticalOccurrenceFrontier,
    Finsupp.mapDomain_apply
      (verticalOccurrenceEmbedding_injective n L data hn c)] at ho
  exact collectorFrontier_invariant_of_ne
    (verticalCollector n L data hn)
    (ProvenancedRow.IsMarked n L data hn)
    (fun h hr ↦ ProvenancedRow.verticalExpansion_preserves_isMarked
      n L data hn h hr)
    c.cell.input (c.input_isMarked n L data hn) c.cell.path
    c.cell.coefficient source ho

end GoverningComparisonCell

private theorem exists_list_coefficient_ne_zero
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

/-- The complete vertical occurrence ledger of the governing comparison
trace.  It is formed before either designated cut is selected. -/
def GoverningWitness.globalVerticalOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    CellVerticalOccurrence n L data hn →₀ ℤ :=
  (w.globalLabelledComparisonTrace n L data hn |>.map fun c ↦
    c.verticalOccurrenceFrontier n L data hn).sum

/-- Every nonzero occurrence in the complete governing vertical ledger is
terminal for the literal vertical pass. -/
theorem GoverningWitness.globalVerticalOccurrence_terminal_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (o : CellVerticalOccurrence n L data hn)
    (ho : w.globalVerticalOccurrences n L data hn o ≠ 0) :
    verticalExpansion n L data hn o.row = none := by
  rw [GoverningWitness.globalVerticalOccurrences] at ho
  obtain ⟨front, hfront, hfronto⟩ :=
    exists_list_coefficient_ne_zero
      ((w.globalLabelledComparisonTrace n L data hn).map fun c ↦
        c.verticalOccurrenceFrontier n L data hn) o ho
  rw [List.mem_map] at hfront
  obtain ⟨c, hc, rfl⟩ := hfront
  exact c.verticalOccurrenceFrontier_row_terminal_of_ne
    n L data hn o hfronto

theorem GoverningWitness.globalVerticalOccurrence_isVerticalNormal
    {a : L} (w : GoverningWitness n L data a)
    (o : CellVerticalOccurrence n L data hn)
    (ho : w.globalVerticalOccurrences n L data hn o ≠ 0) :
    o.row.IsVerticalNormal n L data hn :=
  (ProvenancedRow.verticalExpansion_eq_none_iff n L data hn o.row).mp
    (w.globalVerticalOccurrence_terminal_of_ne n L data hn o ho)

/-- The global vertical frontier contains only genuine marked relation
rows.  This is proved occurrencewise before equal terminal rows can be
combined. -/
theorem GoverningWitness.globalVerticalOccurrence_isMarked
    {a : L} (w : GoverningWitness n L data a)
    (o : CellVerticalOccurrence n L data hn)
    (ho : w.globalVerticalOccurrences n L data hn o ≠ 0) :
    o.row.IsMarked n L data hn := by
  rw [GoverningWitness.globalVerticalOccurrences] at ho
  obtain ⟨front, hfront, hfronto⟩ :=
    exists_list_coefficient_ne_zero
      ((w.globalLabelledComparisonTrace n L data hn).map fun c ↦
        c.verticalOccurrenceFrontier n L data hn) o ho
  rw [List.mem_map] at hfront
  obtain ⟨c, hc, rfl⟩ := hfront
  exact c.verticalOccurrenceFrontier_row_isMarked_of_ne
    n L data hn o hfronto

namespace CellVerticalOccurrence

/-- The terminal factor-two wall in the corrected proof. -/
def IsFactorTwoCut (o : CellVerticalOccurrence n L data hn) : Prop :=
  o.row.factorCount n L data hn = 2 ∧
    o.row.activeWeight n L data hn = n

/-- The `(m_k,k)` support diagonal, where `m_k=n-k+2`. -/
def IsDiagonalCut (k : ℕ) (o : CellVerticalOccurrence n L data hn) : Prop :=
  2 ≤ k ∧ k < n ∧
    o.row.factorCount n L data hn = n - k + 2 ∧
    o.row.activeWeight n L data hn = k ∧
    ∃ c : ProvenancedCell n L data hn,
      provenancedCell? n L data hn o.row = some c

/-- The outside factor-one, weight-`n+1` frontier retained by the cut. -/
def IsOutsideOne (o : CellVerticalOccurrence n L data hn) : Prop :=
  o.row.factorCount n L data hn = 1 ∧
    o.row.activeWeight n L data hn = n + 1

/-- A designated intermediate cut, with its wall index retained as data. -/
def IsSomeDiagonalCut (o : CellVerticalOccurrence n L data hn) : Prop :=
  ∃ k, o.IsDiagonalCut n L data hn k

/-- External occurrences on the side of the cut containing the factor-one
frontier.  The subsequent stopping-rule theorem will show that every other
external occurrence has zero target read; at this stage no such semantic
silence is built into the definition. -/
def IsRetainedBoundary (o : CellVerticalOccurrence n L data hn) : Prop :=
  o.IsOutsideOne n L data hn ∨
    o.IsFactorTwoCut n L data hn ∨
      o.IsSomeDiagonalCut n L data hn

noncomputable instance (o : CellVerticalOccurrence n L data hn) :
    Decidable (o.IsFactorTwoCut n L data hn) :=
  Classical.propDecidable _

noncomputable instance (k : ℕ) (o : CellVerticalOccurrence n L data hn) :
    Decidable (o.IsDiagonalCut n L data hn k) :=
  Classical.propDecidable _

noncomputable instance (o : CellVerticalOccurrence n L data hn) :
    Decidable (o.IsOutsideOne n L data hn) :=
  Classical.propDecidable _

noncomputable instance (o : CellVerticalOccurrence n L data hn) :
    Decidable (o.IsSomeDiagonalCut n L data hn) :=
  Classical.propDecidable _

noncomputable instance (o : CellVerticalOccurrence n L data hn) :
    Decidable (o.IsRetainedBoundary n L data hn) :=
  Classical.propDecidable _

/-- The two designated cut families cannot overlap. -/
theorem not_factorTwo_and_diagonal
    (o : CellVerticalOccurrence n L data hn) (k : ℕ) :
    ¬ (o.IsFactorTwoCut n L data hn ∧
      o.IsDiagonalCut n L data hn k) := by
  rintro ⟨⟨hfactor, hactive⟩, hk, hkn, hfactor', hactive', hc⟩
  omega

/-- The outside edge is disjoint from the factor-two cut. -/
theorem not_outside_and_factorTwo
    (o : CellVerticalOccurrence n L data hn) :
    ¬ (o.IsOutsideOne n L data hn ∧
      o.IsFactorTwoCut n L data hn) := by
  rintro ⟨⟨hfactor, hactive⟩, hfactor', hactive'⟩
  omega

/-- The outside edge is disjoint from every intermediate diagonal. -/
theorem not_outside_and_diagonal
    (o : CellVerticalOccurrence n L data hn) (k : ℕ) :
    ¬ (o.IsOutsideOne n L data hn ∧
      o.IsDiagonalCut n L data hn k) := by
  rintro ⟨⟨hfactor, hactive⟩, hk, hkn, hfactor', hactive', hc⟩
  omega

/-- The factor-one side, factor-two cut, and intermediate diagonal cuts are
pairwise separated at occurrence level. -/
theorem retainedBoundary_cases_disjoint
    (o : CellVerticalOccurrence n L data hn) :
    (o.IsOutsideOne n L data hn → ¬o.IsFactorTwoCut n L data hn) ∧
      (o.IsOutsideOne n L data hn → ¬o.IsSomeDiagonalCut n L data hn) ∧
      (o.IsFactorTwoCut n L data hn →
        ¬o.IsSomeDiagonalCut n L data hn) := by
  constructor
  · intro hout htwo
    exact o.not_outside_and_factorTwo n L data hn ⟨hout, htwo⟩
  constructor
  · intro hout hdiag
    obtain ⟨k, hk⟩ := hdiag
    exact o.not_outside_and_diagonal n L data hn k ⟨hout, hk⟩
  · intro htwo hdiag
    obtain ⟨k, hk⟩ := hdiag
    exact o.not_factorTwo_and_diagonal n L data hn k ⟨htwo, hk⟩

end CellVerticalOccurrence

/-- A supported factor-two cut occurrence opens uniquely as an actual
marked terminal wall with one ordinary factor and a genuine full contextual
relation.  This is the pre-Smith object denoted by `B` in the manuscript. -/
theorem GoverningWitness.factorTwoCut_exists_terminalTwo
    {a : L} (w : GoverningWitness n L data a)
    (o : CellVerticalOccurrence n L data hn)
    (ho : w.globalVerticalOccurrences n L data hn o ≠ 0)
    (hcut : o.IsFactorTwoCut n L data hn) :
    ∃ c : ProvenancedTerminalTwo n L data hn,
      o.row = c.row n L data hn := by
  have hmarked := w.globalVerticalOccurrence_isMarked n L data hn o ho
  have hnormal := w.globalVerticalOccurrence_isVerticalNormal
    n L data hn o ho
  cases hrow : o.row with
  | component =>
      rw [hrow] at hmarked
      exact False.elim hmarked
  | marked root context mark left right =>
      rw [hrow] at hnormal
      unfold CellVerticalOccurrence.IsFactorTwoCut at hcut
      rw [hrow] at hcut
      have hright : right = [] := by
        simpa [ProvenancedRow.IsVerticalNormal] using hnormal
      subst right
      have hfactor : left.length + 1 = 2 := by
        simpa [ProvenancedRow.factorCount] using hcut.1
      cases left with
      | nil => simp at hfactor
      | cons factor tail =>
          cases tail with
          | nil =>
              refine ⟨⟨root, context, mark, factor, ?_⟩, ?_⟩
              · simpa [ProvenancedRow.activeWeight] using hcut.2
              · simp [ProvenancedTerminalTwo.row, hrow]
          | cons x xs => simp at hfactor

/-- Signed factor-two cut, with every vertical occurrence retained as a
distinct subtype index. -/
def GoverningWitness.factorTwoCutOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    {o : CellVerticalOccurrence n L data hn //
      o.IsFactorTwoCut n L data hn} →₀ ℤ :=
  (w.globalVerticalOccurrences n L data hn).sum fun o z ↦
    if h : o.IsFactorTwoCut n L data hn then
      Finsupp.single ⟨o, h⟩ z
    else 0

/-- Signed intermediate diagonal cut at `k`, again retaining all source and
vertical path labels. -/
def GoverningWitness.diagonalCutOccurrences
    {a : L} (w : GoverningWitness n L data a) (k : ℕ) :
    {o : CellVerticalOccurrence n L data hn //
      o.IsDiagonalCut n L data hn k} →₀ ℤ :=
  (w.globalVerticalOccurrences n L data hn).sum fun o z ↦
    if h : o.IsDiagonalCut n L data hn k then
      Finsupp.single ⟨o, h⟩ z
    else 0

/-- Signed outside factor-one frontier on the retained side. -/
def GoverningWitness.outsideOneOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    {o : CellVerticalOccurrence n L data hn //
      o.IsOutsideOne n L data hn} →₀ ℤ :=
  (w.globalVerticalOccurrences n L data hn).sum fun o z ↦
    if h : o.IsOutsideOne n L data hn then
      Finsupp.single ⟨o, h⟩ z
    else 0

/-- The complete signed external occurrence list on the side containing the
factor-one frontier, before the remaining external occurrences are proved
silent. -/
def GoverningWitness.retainedBoundaryOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    {o : CellVerticalOccurrence n L data hn //
      o.IsRetainedBoundary n L data hn} →₀ ℤ :=
  (w.globalVerticalOccurrences n L data hn).sum fun o z ↦
    if h : o.IsRetainedBoundary n L data hn then
      Finsupp.single ⟨o, h⟩ z
    else 0

end

end LieRings.MetabelianVanishing
