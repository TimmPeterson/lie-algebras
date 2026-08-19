import LieRings.DimensionSubring.MetabelianVanishing.GlobalFactorTwoPacket
import LieRings.DimensionSubring.MetabelianVanishing.GlobalFiniteStokes
import LieRings.DimensionSubring.MetabelianVanishing.GlobalIndexedReads
import LieRings.DimensionSubring.MetabelianVanishing.GlobalStoppingRules

/-!
# The single terminal read on the global incidence ledger

This is the map `P` in the corrected manuscript.  It first forgets only the
row-list bookkeeping by evaluating the complete placed word, and then takes
the one-factor PBW primitive in weight `n+1` and its cyclic terminal
coordinate.  No external family is assigned a separate functional.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalClosedSquareReadFintype : Fintype L :=
  Fintype.ofFinite L

/-- The one and only terminal read on a signed list of placed provenance
rows. -/
def terminalIncidenceRead :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
  (terminalPrimitiveRead n L data hn).comp
    (Finsupp.linearCombination ℤ
      (ProvenancedRow.value n L data hn))

@[simp] theorem terminalIncidenceRead_apply
    (rows : ProvenancedRow n L data hn →₀ ℤ) :
    terminalIncidenceRead n L data hn rows =
      terminalPrimitiveRead n L data hn
        (rows.sum fun r z ↦ z • r.value n L data hn) := rfl

/-- The common read is genuinely a read of the evaluated placed word, so a
literal horizontal truncation does not change it. -/
@[simp] theorem terminalIncidenceRead_horizontalOperation
    (rows : ProvenancedRow n L data hn →₀ ℤ) :
    terminalIncidenceRead n L data hn
        (horizontalOperation n L data hn rows) =
      terminalIncidenceRead n L data hn rows := by
  change terminalPrimitiveRead n L data hn
      (Finsupp.linearCombination ℤ
        (ProvenancedRow.value n L data hn)
          (horizontalOperation n L data hn rows)) = _
  rw [evaluate_horizontalOperation]
  rfl

/-- The complete deterministic vertical pass also leaves the one common
read unchanged.  This is the formal reason that no family-specific
functional is introduced at a cut. -/
@[simp] theorem terminalIncidenceRead_verticalOperation
    (rows : ProvenancedRow n L data hn →₀ ℤ) :
    terminalIncidenceRead n L data hn
        (verticalOperation n L data hn rows) =
      terminalIncidenceRead n L data hn rows := by
  change terminalPrimitiveRead n L data hn
      (Finsupp.linearCombination ℤ
        (ProvenancedRow.value n L data hn)
          (verticalOperation n L data hn rows)) = _
  rw [evaluate_verticalOperation]
  rfl

/-- A comparison cell has zero read because its four incidences evaluate to
the literal closed square `H(VR)-V(HR)`. -/
theorem ComparisonCell.terminalIncidenceRead_boundary_eq_zero
    (c : ComparisonCell n L data hn) :
    terminalIncidenceRead n L data hn (c.boundary n L data hn) = 0 := by
  rw [terminalIncidenceRead, LinearMap.comp_apply,
    c.evaluate_boundary_eq_zero n L data hn, map_zero]

/-- The common read is unchanged by each numbered internal gluing. -/
theorem LabelledComparisonCell.terminalIncidenceRead_internal_gluing
    (c : LabelledComparisonCell n L data hn) :
    terminalIncidenceRead n L data hn
        ((c.cell n L data hn).left n L data hn +
          c.horizontalSuccessorRightIncidence n L data hn) = 0 := by
  rw [c.left_add_horizontalSuccessorRightIncidence_eq_zero n L data hn,
    map_zero]

/-- The read of the complete four-incidence trace is zero before any
external-family classification is used. -/
theorem terminalIncidenceRead_traceIncidenceBoundary_eq_zero
    (cells : List (LabelledComparisonCell n L data hn)) :
    terminalIncidenceRead n L data hn
        (traceIncidenceBoundary n L data hn cells) = 0 := by
  rw [traceIncidenceBoundary_eq]
  induction cells with
  | nil => simp
  | cons c cells ih =>
      simp only [List.map_cons, List.sum_cons, map_add]
      rw [(c.cell n L data hn).terminalIncidenceRead_boundary_eq_zero
        n L data hn, ih, add_zero]

/-- On the literal governing initial ledger, the common read is the cyclic
coordinate of the governing top-layer element. -/
theorem GoverningWitness.terminalIncidenceRead_globalInitial
    {a : L} (w : GoverningWitness n L data a) :
    terminalIncidenceRead n L data hn
        (w.globalTriangularInitial n L data hn) =
      data.topEquiv ⟨a, by
        rw [← w.evaluates]
        change evaluation n L data
          (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
            lowerCentralSeries ℤ L n
        rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
        change FreeMetabelian.Evaluation.linear data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
            (FreeMetabelian.Free.incl
              (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
        rw [FreeMetabelian.Evaluation.linear_incl]
        cases n with
        | zero => simp
        | succ t =>
            exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
              data.metabelian
              (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ := by
  change terminalPrimitiveRead n L data hn
      ((provenancedCollector n L data hn).evaluate
        (w.globalTriangularInitial n L data hn)) = _
  rw [
    w.evaluate_globalTriangularInitial n L data,
    w.terminalPrimitiveRead_theta n L data hn]

/-! ## The horizontal outside-edge telescope -/

/-- With a nonempty ordinary right word, the uncut horizontal trace consists
of the current comparison cell followed by the trace of its lower-mark
child.  The homogeneous child is terminal for the horizontal collector and
is retained as the exposed horizontal incidence. -/
theorem uncutComparisonTrace_marked_cons
    (root : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2))
    (left : List (AdaptedIndex n L data hn))
    (x : AdaptedIndex n L data hn)
    (right : List (AdaptedIndex n L data hn))
    (path : List ℕ) (coefficient : ℤ)
    (hmark : mark.val ≠ 0) :
    uncutComparisonTrace n L data hn
        (.marked root context mark left (x :: right)) path coefficient =
      ({ path := path
         coefficient := coefficient
         input := .marked root context mark left (x :: right)
         horizontalOutputs :=
           [(1, .marked root context ⟨mark.val - 1, by omega⟩
              left (x :: right)),
            (1, .component root context mark left (x :: right))]
         horizontal_eq := by simp [horizontalExpansion, hmark]
         verticalOutputs :=
           [(1, .marked root context mark (left ++ [x]) right),
            (1, .marked root (RelationContext.lieRight context x)
              mark left right)]
         vertical_eq := by simp [verticalExpansion] } :
          LabelledComparisonCell n L data hn) ::
        uncutComparisonTrace n L data hn
          (.marked root context ⟨mark.val - 1, by omega⟩
            left (x :: right)) (0 :: path) coefficient := by
  rw [uncutComparisonTrace]
  rw [collectorTrace_eq_of_expansion_some
    (horizontalCollector n L data hn)
    (.marked root context mark left (x :: right)) path coefficient
    [(1, .marked root context ⟨mark.val - 1, by omega⟩ left (x :: right)),
      (1, .component root context mark left (x :: right))]
    (by simp [horizontalCollector, horizontalExpansion, hmark])]
  have hcomponentTrace : collectorTrace (horizontalCollector n L data hn)
      (.component root context mark left (x :: right)) (1 :: path)
        coefficient = [] :=
    collectorTrace_eq_of_expansion_none (horizontalCollector n L data hn)
      (.component root context mark left (x :: right)) (1 :: path)
        coefficient (by rfl)
  simp [uncutComparisonTrace, comparisonCellOfHorizontal?, hcomponentTrace,
    verticalExpansion]

/-- Successive quotient marks telescope integrally: the signed sum of all
homogeneous incidences in one nonempty-right-word branch is the common read
of its original top-marked row. -/
theorem sum_uncutComparisonTrace_componentRead
    (root : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2))
    (left : List (AdaptedIndex n L data hn))
    (x : AdaptedIndex n L data hn)
    (right : List (AdaptedIndex n L data hn))
    (path : List ℕ) (coefficient : ℤ) :
    ((uncutComparisonTrace n L data hn
        (.marked root context mark left (x :: right)) path coefficient).map
      fun c ↦ c.coefficient • terminalPrimitiveRead n L data hn
        (horizontalComponentValue n L data hn c.input)).sum =
      coefficient • terminalPrimitiveRead n L data hn
        (ProvenancedRow.marked root context mark left (x :: right)).value := by
  generalize hm : mark.val = m
  induction m using Nat.strong_induction_on generalizing mark path coefficient with
  | h m ih =>
      by_cases hm0 : m = 0
      · have hmark0 : mark.val = 0 := hm.trans hm0
        rw [uncutComparisonTrace,
          collectorTrace_eq_of_expansion_none
            (horizontalCollector n L data hn)
            (.marked root context mark left (x :: right)) path coefficient
            (by simp [horizontalCollector, horizontalExpansion, hmark0])]
        have hvalue :
            (ProvenancedRow.marked root context mark left (x :: right) :
              ProvenancedRow n L data hn).value = 0 :=
          ProvenancedRow.value_eq_zero_of_markValue_eq_zero
            n L data hn _ (by simpa [ProvenancedRow.markValue] using hmark0)
        simp [hvalue]
      · have hmark : mark.val ≠ 0 := by omega
        rw [uncutComparisonTrace_marked_cons n L data hn
          root context mark left x right path coefficient hmark]
        simp only [List.map_cons, List.sum_cons]
        rw [ih (m - 1) (by omega)
          (⟨mark.val - 1, by omega⟩ : Fin (n + 2))
          (0 :: path) coefficient (by simp [hm])]
        have hdecomp :=
          value_eq_lowerMarkedValue_add_horizontalComponentValue
            n L data hn
              (ProvenancedRow.marked root context mark left (x :: right))
        rw [lowerMarkedValue, dif_neg hmark] at hdecomp
        rw [hdecomp, map_add, smul_add]
        abel

/-- A factor-one initial row has no comparison cell: all rows in its
horizontal trace retain the empty left/right frame, so the vertical
operation is unavailable.  This is precisely the outside edge. -/
theorem uncutComparisonTrace_marked_nil
    (root : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2))
    (path : List ℕ) (coefficient : ℤ) :
    uncutComparisonTrace n L data hn
        (.marked root context mark [] []) path coefficient = [] := by
  rw [uncutComparisonTrace, List.filterMap_eq_nil_iff]
  intro cell hcell
  have hframe := collectorTrace_input_invariant
    (horizontalCollector n L data hn)
    (ProvenancedRow.HasHorizontalFrame n L data hn context [] [])
    (fun h hr ↦ ProvenancedRow.horizontalExpansion_preserves_HasHorizontalFrame
      n L data hn context [] [] h hr)
    (.marked root context mark [] [])
    (by simp [ProvenancedRow.HasHorizontalFrame])
    path coefficient cell hcell
  rcases cell with ⟨cellPath, cellCoefficient, cellInput, outputs, hexp⟩
  simp only at hframe ⊢
  have hvertical : verticalExpansion n L data hn cellInput = none := by
    cases hinput : cellInput with
    | marked rowRoot rowContext rowMark rowLeft rowRight =>
        rw [hinput] at hframe
        rcases hframe with ⟨rfl, rfl, rfl⟩
        simp [verticalExpansion]
    | component rowRoot rowContext rowMark rowLeft rowRight =>
        rw [hinput] at hframe
        rcases hframe with ⟨rfl, rfl, rfl⟩
        simp [verticalExpansion]
  unfold comparisonCellOfHorizontal?
  split
  · rfl
  · rename_i next hnext
    rw [hvertical] at hnext
    contradiction

/-- The literal factor-one initial branches.  They have no comparison cell
and hence form the outside edge of the global trace. -/
def GoverningWitness.outsideInitialRead
    {a : L} (w : GoverningWitness n L data a) :
    ZMod (2 ^ data.exponent) :=
  (List.ofFn fun i : Fin (w.globalInitialLabels n L data hn).length ↦
    let q := (w.globalInitialLabels n L data hn).get i
    if exponentWord n L data hn q.2.exponent = [] then
      q.1 • terminalPrimitiveRead n L data hn (q.2.row n L data hn).value
    else 0).sum

/-- Reading the aggregated initial provenance ledger is the signed sum of
the common read on its literal source copies. -/
theorem GoverningWitness.terminalIncidenceRead_globalInitial_eq_labelSum
    {a : L} (w : GoverningWitness n L data a) :
    terminalIncidenceRead n L data hn
        (w.globalTriangularInitial n L data hn) =
      (w.globalInitialLabels n L data hn |>.map fun q ↦
        q.1 • terminalPrimitiveRead n L data hn
          (q.2.row n L data hn).value).sum := by
  have h := congrArg (terminalIncidenceRead n L data hn)
    (w.sum_globalInitialRows n L data hn)
  rw [map_list_sum] at h
  rw [GoverningWitness.globalInitialRows, List.map_map] at h
  have hsingle (q : ℤ × GlobalInitialPacketLabel n L data hn) :
      terminalIncidenceRead n L data hn
          (Finsupp.single (q.2.row n L data hn) q.1) =
        q.1 • terminalPrimitiveRead n L data hn
          (q.2.row n L data hn).value := by
    rw [terminalIncidenceRead_apply]
    rw [Finsupp.sum_single_index (by simp)]
    rw [map_zsmul]
  rw [List.map_map] at h
  change ((w.globalInitialLabels n L data hn |>.map fun q ↦
      terminalIncidenceRead n L data hn
        (Finsupp.single (q.2.row n L data hn) q.1)).sum) =
    terminalIncidenceRead n L data hn
      (w.globalTriangularInitial n L data hn) at h
  simp_rw [hsingle] at h
  exact h.symm

/-- Sourcewise outside/telescope decomposition.  A factor-one source is
left on the outside edge; every source with an ordinary factor is read by
the complete quotient-mark telescope. -/
theorem GoverningWitness.outside_add_branchComponentRead
    {a : L} (w : GoverningWitness n L data a)
    (i : Fin (w.globalInitialLabels n L data hn).length) :
    let q := (w.globalInitialLabels n L data hn).get i
    (if exponentWord n L data hn q.2.exponent = [] then
        q.1 • terminalPrimitiveRead n L data hn (q.2.row n L data hn).value
      else 0) +
      ((uncutComparisonTrace n L data hn (q.2.row n L data hn)
          [i.1] q.1).map fun c ↦
        c.coefficient • terminalPrimitiveRead n L data hn
          (horizontalComponentValue n L data hn c.input)).sum =
      q.1 • terminalPrimitiveRead n L data hn
        (q.2.row n L data hn).value := by
  let q := (w.globalInitialLabels n L data hn).get i
  change
    (if exponentWord n L data hn q.2.exponent = [] then
        q.1 • terminalPrimitiveRead n L data hn (q.2.row n L data hn).value
      else 0) +
      ((uncutComparisonTrace n L data hn (q.2.row n L data hn)
          [i.1] q.1).map fun c ↦
        c.coefficient • terminalPrimitiveRead n L data hn
          (horizontalComponentValue n L data hn c.input)).sum =
      q.1 • terminalPrimitiveRead n L data hn
        (q.2.row n L data hn).value
  cases hword : exponentWord n L data hn q.2.exponent with
  | nil =>
      rw [if_pos (by simp)]
      rw [show q.2.row n L data hn =
          .marked (triangularRelationOfIndex n L data q.2.relationTag)
            .hole ⟨n + 1, by omega⟩ [] [] by
        simp [GlobalInitialPacketLabel.row, hword]]
      rw [uncutComparisonTrace_marked_nil n L data hn]
      simp
  | cons x right =>
      rw [if_neg (by simp)]
      simp only [zero_add]
      rw [show q.2.row n L data hn =
          .marked (triangularRelationOfIndex n L data q.2.relationTag)
            .hole ⟨n + 1, by omega⟩ [] (x :: right) by
        simp [GlobalInitialPacketLabel.row, hword]]
      exact sum_uncutComparisonTrace_componentRead n L data hn
        (triangularRelationOfIndex n L data q.2.relationTag)
        .hole ⟨n + 1, by omega⟩ [] x right [i.1] q.1

/-- The global horizontal telescope.  It is the evaluated finite-Stokes
outside edge before the component walls are classified. -/
theorem GoverningWitness.terminalIncidenceRead_globalInitial_eq_outside_add_cells
    {a : L} (w : GoverningWitness n L data a) :
    terminalIncidenceRead n L data hn
        (w.globalTriangularInitial n L data hn) =
      w.outsideInitialRead n L data hn +
        ((w.globalLabelledComparisonTrace n L data hn).map fun c ↦
          c.cell.coefficient • terminalPrimitiveRead n L data hn
            (horizontalComponentValue n L data hn c.cell.input)).sum := by
  have htrace :
      ((w.globalLabelledComparisonTrace n L data hn).map fun c ↦
          c.cell.coefficient • terminalPrimitiveRead n L data hn
            (horizontalComponentValue n L data hn c.cell.input)).sum =
        (List.ofFn fun i : Fin (w.globalInitialLabels n L data hn).length ↦
          ((uncutComparisonTrace n L data hn
            (((w.globalInitialLabels n L data hn).get i).2.row n L data hn)
            [i.1] ((w.globalInitialLabels n L data hn).get i).1).map fun c ↦
              c.coefficient • terminalPrimitiveRead n L data hn
                (horizontalComponentValue n L data hn c.input)).sum).sum := by
    rw [GoverningWitness.globalLabelledComparisonTrace,
      List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn]
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    rw [List.map_map]
    rfl
  rw [w.terminalIncidenceRead_globalInitial_eq_labelSum n L data hn]
  symm
  rw [GoverningWitness.outsideInitialRead, htrace]
  let labels := w.globalInitialLabels n L data hn
  change
    (List.ofFn fun i : Fin labels.length ↦
      let q := labels.get i
      if exponentWord n L data hn q.2.exponent = [] then
        q.1 • terminalPrimitiveRead n L data hn (q.2.row n L data hn).value
      else 0).sum +
      (List.ofFn fun i : Fin labels.length ↦
        ((uncutComparisonTrace n L data hn
          ((labels.get i).2.row n L data hn) [i.1] (labels.get i).1).map
            fun c ↦ c.coefficient • terminalPrimitiveRead n L data hn
              (horizontalComponentValue n L data hn c.input)).sum).sum =
      (labels.map fun q ↦ q.1 • terminalPrimitiveRead n L data hn
        (q.2.row n L data hn).value).sum
  have sum_ofFn_add (m : ℕ)
      (f g : Fin m → ZMod (2 ^ data.exponent)) :
      (List.ofFn f).sum + (List.ofFn g).sum =
        (List.ofFn fun i ↦ f i + g i).sum := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
        simp only [List.sum_cons]
        rw [← ih (fun i ↦ f i.succ) (fun i ↦ g i.succ)]
        abel
  rw [sum_ofFn_add]
  have hroot :
      (labels.map fun q ↦ q.1 • terminalPrimitiveRead n L data hn
          (q.2.row n L data hn).value).sum =
        (List.ofFn fun i : Fin labels.length ↦
          (labels.get i).1 • terminalPrimitiveRead n L data hn
            ((labels.get i).2.row n L data hn).value).sum := by
    apply congrArg List.sum
    calc
      labels.map (fun q ↦ q.1 • terminalPrimitiveRead n L data hn
          (q.2.row n L data hn).value) =
          (List.ofFn labels.get).map (fun q ↦
            q.1 • terminalPrimitiveRead n L data hn
              (q.2.row n L data hn).value) := by
            rw [List.ofFn_get]
      _ = _ := by
        rw [List.map_ofFn]
        apply congrArg List.ofFn
        funext i
        rfl
  rw [hroot]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext i
  exact w.outside_add_branchComponentRead n L data hn i

/-! ## The exhaustive signed component-wall read -/

namespace GoverningComponentSource

/-- Contribution of one literal homogeneous horizontal source to the
common terminal read, with its inherited signed coefficient. -/
def terminalRead
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    ZMod (2 ^ data.exponent) :=
  s.coefficient n L data hn •
    terminalPrimitiveRead n L data hn s.occurrence.row.value

/-- A homogeneous source belonging to a comparison cell still has at least
one ordinary input.  If its initial right word were empty, the vertical
operation on the parent marked row would be unavailable, so there would be
no comparison cell.  This is the syntactic reason that the factor-one
outside edge comes only from the original initial list, never from a
homogeneous component child. -/
theorem originRight_ne_nil
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.originRight ≠ [] := by
  have hparent := w.globalHorizontalVerticalOccurrence_parent_mem
    n L data hn s.occurrence s.coefficient_ne
  have hframe := w.globalComparisonCell_input_hasHorizontalFrame
    n L data hn s.occurrence.parent hparent
  have hmarked := s.occurrence.parent.input_isMarked n L data hn
  have horigin := s.originHorizontalFrame n L data hn
  cases hinput : s.occurrence.parent.cell.input with
  | component root context mark left right =>
      rw [hinput] at hmarked
      exact False.elim hmarked
  | marked root context mark left right =>
      rw [hinput] at hframe
      rcases hframe with ⟨rfl, rfl, hright⟩
      rw [horigin.2.2, ← hright]
      intro hnil
      subst right
      have hvertical := s.occurrence.parent.cell.vertical_eq
      rw [hinput, hnil] at hvertical
      simp [verticalExpansion] at hvertical

/-- The outside one-factor wall of the relation-`M` source partition. -/
def IsOutsideWall
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : Prop :=
  s.originInputProfileTag n L data hn = .relationM ∧
    s.originTotalWeight n L data hn = n + 1 ∧
    s.originActiveWeight n L data hn = n + 1 ∧
    s.originFactorCount n L data hn = 1

/-- Consequently no homogeneous component source belongs to the
factor-one outside wall. -/
theorem not_isOutsideWall
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    ¬ s.IsOutsideWall n L data hn := by
  intro h
  have hright := s.originRight_ne_nil n L data hn
  have hframe := s.originHorizontalFrame n L data hn
  rcases h with ⟨_, _, _, hfactor⟩
  rw [GoverningComponentSource.originFactorCount,
    hframe.2.1] at hfactor
  simp only [List.length_nil, zero_add] at hfactor
  have : s.originRight.length = 0 := by omega
  exact hright (List.length_eq_zero_iff.mp this)

/-- The factor-two wall of the relation-`M` source partition. -/
def IsFactorTwoWall
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) : Prop :=
  s.originInputProfileTag n L data hn = .relationM ∧
    s.originTotalWeight n L data hn = n + 1 ∧
    s.originActiveWeight n L data hn = n ∧
    s.originFactorCount n L data hn = 2

/-- The horizontal side of the intermediate `(n-k+2,k)` wall. -/
def IsIntermediateWall
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) (k : ℕ) : Prop :=
  s.originInputProfileTag n L data hn = .relationM ∧
    s.originTotalWeight n L data hn = n + 1 ∧
    s.originActiveWeight n L data hn = k ∧
    s.originFactorCount n L data hn = n - k + 2 ∧
    2 ≤ k ∧ k < n

noncomputable instance
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    Decidable (s.IsOutsideWall n L data hn) := Classical.propDecidable _

noncomputable instance
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    Decidable (s.IsFactorTwoWall n L data hn) := Classical.propDecidable _

noncomputable instance
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) (k : ℕ) :
    Decidable (s.IsIntermediateWall n L data hn k) :=
  Classical.propDecidable _

/-- Pointwise form of the exhaustive terminal partition.  This is stated as
an equality, rather than only a classification implication, so it can be
summed without choosing a surviving wall. -/
theorem terminalRead_eq_wall_sum
    {a : L} {w : GoverningWitness n L data a}
    (s : GoverningComponentSource n L data hn w) :
    s.terminalRead n L data hn =
      (if s.IsOutsideWall n L data hn then
          s.terminalRead n L data hn else 0) +
        (if s.IsFactorTwoWall n L data hn then
          s.terminalRead n L data hn else 0) +
        ∑ k ∈ Finset.Ico 2 n,
          if s.IsIntermediateWall n L data hn k then
            s.terminalRead n L data hn else 0 := by
  classical
  by_cases hread : terminalPrimitiveRead n L data hn
      s.occurrence.row.value = 0
  · simp [terminalRead, hread]
  · obtain ⟨htag, htarget, hwalls⟩ :=
      s.relationM_wall_classification_of_terminalPrimitiveRead_ne_zero
        n L data hn hread
    rcases hwalls with hout | htwo | hintermediate
    · have hout' : s.IsOutsideWall n L data hn :=
        ⟨htag, htarget, hout⟩
      have houtActive := hout.1
      have hnotTwo : ¬s.IsFactorTwoWall n L data hn := by
        intro h
        rcases h with ⟨_, _, hactive, _⟩
        omega
      have hnotIntermediate : ∀ k ∈ Finset.Ico 2 n,
          ¬s.IsIntermediateWall n L data hn k := by
        intro k hk h
        rcases h with ⟨_, _, hactive, _, _, _⟩
        omega
      simp only [hout', if_true, hnotTwo, if_false]
      have hsum : (∑ k ∈ Finset.Ico 2 n,
          if s.IsIntermediateWall n L data hn k then
            s.terminalRead n L data hn else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [if_neg (hnotIntermediate k hk)]
      rw [hsum]
      simp
    · have htwo' : s.IsFactorTwoWall n L data hn :=
        ⟨htag, htarget, htwo⟩
      have htwoActive := htwo.1
      have hnotOutside : ¬s.IsOutsideWall n L data hn := by
        intro h
        rcases h with ⟨_, _, hactive, _⟩
        omega
      have hnotIntermediate : ∀ k ∈ Finset.Ico 2 n,
          ¬s.IsIntermediateWall n L data hn k := by
        intro k hk h
        rcases h with ⟨_, _, hactive, _, _, _⟩
        omega
      simp only [hnotOutside, if_false, htwo', if_true, zero_add]
      have hsum : (∑ k ∈ Finset.Ico 2 n,
          if s.IsIntermediateWall n L data hn k then
            s.terminalRead n L data hn else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [if_neg (hnotIntermediate k hk)]
      rw [hsum]
      simp
    · obtain ⟨k, hactive, hfactor, hk, hkn⟩ := hintermediate
      have hdiag : s.IsIntermediateWall n L data hn k :=
        ⟨htag, htarget, hactive, hfactor, hk, hkn⟩
      have hkmem : k ∈ Finset.Ico 2 n := by simpa using ⟨hk, hkn⟩
      have hnotOutside : ¬s.IsOutsideWall n L data hn := by
        intro h
        rcases h with ⟨_, _, hactive', _⟩
        omega
      have hnotTwo : ¬s.IsFactorTwoWall n L data hn := by
        intro h
        rcases h with ⟨_, _, hactive', _⟩
        omega
      simp only [hnotOutside, if_false, hnotTwo, zero_add]
      rw [Finset.sum_eq_single k]
      · rw [if_pos hdiag]
      · intro j hj hjk
        rw [if_neg]
        intro h
        rcases h with ⟨_, _, hactive', _, _, _⟩
        apply hjk
        omega
      · intro hknot
        exact (hknot hkmem).elim

end GoverningComponentSource

/-- Signed outside component-wall contribution. -/
def GoverningWitness.outsideComponentRead
    {a : L} (w : GoverningWitness n L data a) :
    ZMod (2 ^ data.exponent) :=
  (w.globalComponentSources n L data hn).map (fun s ↦
    if s.IsOutsideWall n L data hn then s.terminalRead n L data hn else 0)
    |>.sum

/-- There is no factor-one component edge: such a row has no ordinary
factor, hence cannot be the homogeneous output of a comparison cell on
which the vertical operation was available. -/
@[simp] theorem GoverningWitness.outsideComponentRead_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    w.outsideComponentRead n L data hn = 0 := by
  rw [GoverningWitness.outsideComponentRead]
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  rw [if_neg (s.not_isOutsideWall n L data hn)]

/-- Signed factor-two component-wall contribution. -/
def GoverningWitness.factorTwoComponentRead
    {a : L} (w : GoverningWitness n L data a) :
    ZMod (2 ^ data.exponent) :=
  (w.globalComponentSources n L data hn).map (fun s ↦
    if s.IsFactorTwoWall n L data hn then s.terminalRead n L data hn else 0)
    |>.sum

/-- Signed horizontal contribution at the intermediate `k`-wall. -/
def GoverningWitness.intermediateComponentRead
    {a : L} (w : GoverningWitness n L data a) (k : ℕ) :
    ZMod (2 ^ data.exponent) :=
  (w.globalComponentSources n L data hn).map (fun s ↦
    if s.IsIntermediateWall n L data hn k then
      s.terminalRead n L data hn else 0) |>.sum

/-- Before the wall partition, the complete homogeneous external read is
literally the signed sum of the common read on the source occurrences.
This equality keeps each source as a whole through its independent PBW
collection. -/
theorem GoverningWitness.terminalComponentRead_globalComponentPBWPrimitive_eq_sourceRead
    {a : L} (w : GoverningWitness n L data a) :
    terminalComponentRead n L data
        (w.globalComponentPBWPrimitive n L data hn) =
      ((w.globalComponentSources n L data hn).map (fun s ↦
        GoverningComponentSource.terminalRead n L data hn s)).sum := by
  unfold GoverningWitness.globalComponentPBWPrimitive
  unfold GoverningWitness.globalComponentPBWOccurrences
  induction w.globalComponentSources n L data hn with
  | nil => simp
  | cons s sources ih =>
      simp only [List.map_cons, List.sum_cons]
      change terminalComponentRead n L data
          ((Finsupp.linearCombination ℤ
            (fun o : GoverningComponentPBWOccurrence n L data hn w ↦
              pbwPrimitive n L data hn (o.state.value n L data hn)))
              (s.componentPBWFrontier n L data hn +
                (sources.map fun t : GoverningComponentSource n L data hn w ↦
                  t.componentPBWFrontier n L data hn).sum)) = _
      rw [map_add, map_add]
      change terminalComponentRead n L data
          (s.componentPBWPrimitive n L data hn) + _ = _
      have hsread : terminalComponentRead n L data
            (s.componentPBWPrimitive n L data hn) =
          s.terminalRead n L data hn := by
        rw [s.componentPBWPrimitive_eq_coefficient_smul n L data hn,
          map_zsmul]
        rfl
      rw [hsread]
      congr 1

/-- The pointwise stopping rules give a literal disjoint exhaustive sum
decomposition of the complete signed homogeneous-component read. -/
theorem GoverningWitness.terminalComponentRead_wall_partition
    {a : L} (w : GoverningWitness n L data a) :
    terminalComponentRead n L data
        (w.globalComponentPBWPrimitive n L data hn) =
      w.outsideComponentRead n L data hn +
        w.factorTwoComponentRead n L data hn +
        ∑ k ∈ Finset.Ico 2 n,
          w.intermediateComponentRead n L data hn k := by
  classical
  rw [w.terminalComponentRead_globalComponentPBWPrimitive_eq_relationM
    n L data hn]
  rw [w.globalComponentPBWOriginProfilePrimitive_eq_sourceSum
    n L data hn .relationM, map_list_sum]
  simp only [List.map_map]
  simp only [GoverningWitness.outsideComponentRead,
    GoverningWitness.factorTwoComponentRead,
    GoverningWitness.intermediateComponentRead]
  generalize w.globalComponentSources n L data hn = sources
  induction sources with
  | nil => simp
  | cons s sources ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib]
      have hsource :
          terminalComponentRead n L data
              (if s.originInputProfileTag n L data hn = .relationM then
                s.componentPBWPrimitive n L data hn else 0) =
            (if s.IsOutsideWall n L data hn then
                s.terminalRead n L data hn else 0) +
              (if s.IsFactorTwoWall n L data hn then
                s.terminalRead n L data hn else 0) +
              ∑ k ∈ Finset.Ico 2 n,
                if s.IsIntermediateWall n L data hn k then
                  s.terminalRead n L data hn else 0 := by
        by_cases htag :
            s.originInputProfileTag n L data hn = .relationM
        · rw [if_pos htag, s.componentPBWPrimitive_eq_coefficient_smul
              n L data hn, map_zsmul]
          change s.terminalRead n L data hn = _
          exact s.terminalRead_eq_wall_sum n L data hn
        · simp [htag, GoverningComponentSource.IsOutsideWall,
            GoverningComponentSource.IsFactorTwoWall,
            GoverningComponentSource.IsIntermediateWall]
      simp only [Function.comp_apply]
      rw [hsource, ih]
      abel

/-! ## The occurrence-level global closed square -/

/-- The complete upper-route lower-mark ledger, evaluated without erasing
the path-labelled vertical occurrences.  These are exactly the terms which
continue to the next quotient mark in the manuscript's global square. -/
def GoverningWitness.globalVerticalLowerMarkedValue
    {a : L} (w : GoverningWitness n L data a) :
    UEA ℤ (FreeModel n L) :=
  (w.globalVerticalOccurrences n L data hn).sum fun o z ↦
    z • lowerMarkedValue n L data hn o.row

/-- The complementary upper-route ledger.  On every supported marked row
this is literally its homogeneous truncation child, but all lower-context
rows produced by the vertical pass are still present as separate copies. -/
def GoverningWitness.globalVerticalComponentValue
    {a : L} (w : GoverningWitness n L data a) :
    UEA ℤ (FreeModel n L) :=
  (w.globalVerticalOccurrences n L data hn).sum fun o z ↦
    z • horizontalComponentValue n L data hn o.row

/-- Cellwise summation of the transfer--truncation square for the lower-mark
summand.  This is an equality of evaluated occurrence ledgers; no lower
context has been discarded or interpreted as a relation. -/
theorem GoverningWitness.globalVerticalLowerMarkedValue_eq_cell_sum
    {a : L} (w : GoverningWitness n L data a) :
    w.globalVerticalLowerMarkedValue n L data hn =
      ((w.globalLabelledComparisonTrace n L data hn).map fun c ↦
        c.cell.coefficient •
          lowerMarkedValue n L data hn c.cell.input).sum := by
  classical
  unfold GoverningWitness.globalVerticalLowerMarkedValue
    GoverningWitness.globalVerticalOccurrences
  change (Finsupp.linearCombination ℤ
      (fun o : CellVerticalOccurrence n L data hn ↦
        lowerMarkedValue n L data hn o.row))
      ((w.globalLabelledComparisonTrace n L data hn |>.map fun c ↦
        c.verticalOccurrenceFrontier n L data hn).sum) = _
  rw [map_list_sum]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  exact c.lowerMarkedValue_verticalOccurrenceFrontier n L data hn

/-- The same global summation for the homogeneous child.  This is the
formal occurrence-level statement that the complete marked vertical pass
retains every intermediate diagonal/Phi/T correction until they cancel in
the global ledger. -/
theorem GoverningWitness.globalVerticalComponentValue_eq_cell_sum
    {a : L} (w : GoverningWitness n L data a) :
    w.globalVerticalComponentValue n L data hn =
      ((w.globalLabelledComparisonTrace n L data hn).map fun c ↦
        c.cell.coefficient •
          horizontalComponentValue n L data hn c.cell.input).sum := by
  classical
  unfold GoverningWitness.globalVerticalComponentValue
    GoverningWitness.globalVerticalOccurrences
  change (Finsupp.linearCombination ℤ
      (fun o : CellVerticalOccurrence n L data hn ↦
        horizontalComponentValue n L data hn o.row))
      ((w.globalLabelledComparisonTrace n L data hn |>.map fun c ↦
        c.verticalOccurrenceFrontier n L data hn).sum) = _
  rw [map_list_sum]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  exact c.horizontalComponentValue_verticalOccurrenceFrontier
    n L data hn

/-- The upper vertical route is the literal sum of its continuing marked
part and its homogeneous part. -/
theorem GoverningWitness.globalVerticalValue_eq_lower_add_component
    {a : L} (w : GoverningWitness n L data a) :
    (w.globalVerticalOccurrences n L data hn).sum (fun o z ↦
        z • o.row.value) =
      w.globalVerticalLowerMarkedValue n L data hn +
        w.globalVerticalComponentValue n L data hn := by
  classical
  rw [GoverningWitness.globalVerticalLowerMarkedValue,
    GoverningWitness.globalVerticalComponentValue, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro o ho
  rw [value_eq_lowerMarkedValue_add_horizontalComponentValue, smul_add]

/-- Forget only the path and parent labels on the complete `V R`
occurrence ledger. -/
def GoverningWitness.globalVerticalRows
    {a : L} (w : GoverningWitness n L data a) :
    ProvenancedRow n L data hn →₀ ℤ :=
  (w.globalVerticalOccurrences n L data hn).sum fun o z ↦
    z • Finsupp.single o.row (1 : ℤ)

/-- Forget only the child and path labels on the complete `V (H R)`
occurrence ledger. -/
def GoverningWitness.globalHorizontalVerticalRows
    {a : L} (w : GoverningWitness n L data a) :
    ProvenancedRow n L data hn →₀ ℤ :=
  (w.globalHorizontalVerticalOccurrences n L data hn).sum fun o z ↦
    z • Finsupp.single o.row (1 : ℤ)

/-- Reading the forgotten `V R` ledger is exactly the signed sum of the
same read on its occurrence copies.  In particular, equal terminal rows
with different ancestry have not been merged before their coefficients are
applied. -/
theorem GoverningWitness.terminalIncidenceRead_globalVerticalRows
    {a : L} (w : GoverningWitness n L data a) :
    terminalIncidenceRead n L data hn
        (w.globalVerticalRows n L data hn) =
      (w.globalVerticalOccurrences n L data hn).sum fun o z ↦
        z • terminalPrimitiveRead n L data hn o.row.value := by
  classical
  rw [GoverningWitness.globalVerticalRows, map_finsuppSum]
  apply Finsupp.sum_congr
  intro o ho
  rw [map_zsmul, terminalIncidenceRead_apply]
  simp

/-- The analogous occurrence formula on the `V (H R)` route. -/
theorem GoverningWitness.terminalIncidenceRead_globalHorizontalVerticalRows
    {a : L} (w : GoverningWitness n L data a) :
    terminalIncidenceRead n L data hn
        (w.globalHorizontalVerticalRows n L data hn) =
      (w.globalHorizontalVerticalOccurrences n L data hn).sum fun o z ↦
        z • terminalPrimitiveRead n L data hn o.row.value := by
  classical
  rw [GoverningWitness.globalHorizontalVerticalRows, map_finsuppSum]
  apply Finsupp.sum_congr
  intro o ho
  rw [map_zsmul, terminalIncidenceRead_apply]
  simp

/-- Common read of the lower route copies which are still internally glued
to a subsequent comparison cell. -/
def GoverningWitness.internalHorizontalVerticalRead
    {a : L} (w : GoverningWitness n L data a) :
    ZMod (2 ^ data.exponent) :=
  (w.globalHorizontalVerticalOccurrences n L data hn).sum fun o z ↦
    if o.IsInternal n L data hn then
      z • terminalPrimitiveRead n L data hn o.row.value else 0

/-- Common read of the external homogeneous children, before their source
wall is classified. -/
def GoverningWitness.externalHomogeneousRead
    {a : L} (w : GoverningWitness n L data a) :
    ZMod (2 ^ data.exponent) :=
  (w.globalHorizontalVerticalOccurrences n L data hn).sum fun o z ↦
    if o.IsExternal n L data hn ∧ o.IsHomogeneousChild n L data hn then
      z • terminalPrimitiveRead n L data hn o.row.value else 0

/-- Linear form of the external homogeneous occurrence read. -/
def externalHomogeneousOccurrenceReadLinear :
    (CellHorizontalVerticalOccurrence n L data hn →₀ ℤ) →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
  Finsupp.linearCombination ℤ fun o ↦
    if o.IsExternal n L data hn ∧ o.IsHomogeneousChild n L data hn then
      terminalPrimitiveRead n L data hn o.row.value else 0

theorem externalHomogeneousOccurrenceReadLinear_apply
    (v : CellHorizontalVerticalOccurrence n L data hn →₀ ℤ) :
    externalHomogeneousOccurrenceReadLinear n L data hn v =
      v.sum (fun o z ↦
        if o.IsExternal n L data hn ∧ o.IsHomogeneousChild n L data hn then
          z • terminalPrimitiveRead n L data hn o.row.value else 0) := by
  classical
  rw [externalHomogeneousOccurrenceReadLinear]
  apply Finsupp.sum_congr
  intro o ho
  by_cases h : o.IsExternal n L data hn ∧
      o.IsHomogeneousChild n L data hn <;> simp [h]

/-- On the vertical frontier below one numbered horizontal child, the
external-homogeneous filter is either the complete common read (for the
literal component child) or zero (for the continuing marked child).  The
test depends only on the retained parent and child index, not on a later
equality of evaluated rows. -/
theorem GoverningComparisonCell.externalHomogeneousRead_childFrontier
    (c : GoverningComparisonCell n L data hn)
    (i : Fin c.cell.horizontalOutputs.length) :
    (c.horizontalSuccessorVerticalFrontier n L data hn i).sum (fun o z ↦
        if o.IsExternal n L data hn ∧ o.IsHomogeneousChild n L data hn then
          z • terminalPrimitiveRead n L data hn o.row.value else 0) =
      if (c.cell.horizontalOutputs.get i).2.IsComponent n L data hn then
        (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1) •
          terminalPrimitiveRead n L data hn
            (c.cell.horizontalOutputs.get i).2.value
      else 0 := by
  classical
  rw [GoverningComparisonCell.horizontalSuccessorVerticalFrontier,
    Finsupp.sum_mapDomain_index_inj
      (GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding_injective
        n L data hn c i)]
  let child := (c.cell.horizontalOutputs.get i).2
  let coefficient :=
    c.cell.coefficient * (c.cell.horizontalOutputs.get i).1
  have hread := congrArg (terminalPrimitiveRead n L data hn)
    (evaluate_collectorFrontier (verticalCollector n L data hn)
      child (i.1 :: c.cell.path) coefficient)
  rw [map_finsuppSum] at hread
  simp only [map_zsmul] at hread
  cases hchild : child with
  | marked root context mark left right =>
      have hchild' : (c.cell.horizontalOutputs.get i).2 =
          .marked root context mark left right := by
        simpa only [child] using hchild
      have hnotHom (o : CollectorOccurrence (ProvenancedRow n L data hn)) :
          ¬(CellHorizontalVerticalOccurrence.IsHomogeneousChild n L data hn
            (c.horizontalVerticalOccurrenceEmbedding n L data hn i o)) := by
        rintro ⟨r, q, m, l, s, heq⟩
        simp only [GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding]
          at heq
        rw [hchild'] at heq
        contradiction
      have hnotComponent :
          ¬(c.cell.horizontalOutputs.get i).2.IsComponent n L data hn := by
        rw [hchild']
        simp [ProvenancedRow.IsComponent]
      rw [if_neg hnotComponent]
      simp only [hnotHom, and_false, if_false]
      exact Finsupp.sum_fun_zero _
  | component root context mark left right =>
      have hchild' : (c.cell.horizontalOutputs.get i).2 =
          .component root context mark left right := by
        simpa only [child] using hchild
      have hhom (o : CollectorOccurrence (ProvenancedRow n L data hn)) :
          CellHorizontalVerticalOccurrence.IsHomogeneousChild n L data hn
            (c.horizontalVerticalOccurrenceEmbedding n L data hn i o) := by
        refine ⟨root, context, mark, left, right, ?_⟩
        simpa only [GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding]
          using hchild'
      have hext (o : CollectorOccurrence (ProvenancedRow n L data hn)) :
          CellHorizontalVerticalOccurrence.IsExternal n L data hn
            (c.horizontalVerticalOccurrenceEmbedding n L data hn i o) := by
        intro hint
        exact (by
          change (horizontalExpansion n L data hn child).isSome ∧ _ at hint
          rw [hchild] at hint
          simp [horizontalExpansion] at hint)
      have hcomponent :
          (c.cell.horizontalOutputs.get i).2.IsComponent n L data hn := by
        rw [hchild']
        trivial
      rw [if_pos hcomponent]
      simp only [hhom, hext, and_self, if_true]
      simpa only [GoverningComparisonCell.horizontalVerticalOccurrenceEmbedding,
        child, coefficient, verticalCollector] using hread

/-- Summing over the two literal outputs of one marked truncation leaves
exactly its homogeneous component value. -/
theorem GoverningComparisonCell.externalHomogeneousRead_cellFrontier
    (c : GoverningComparisonCell n L data hn) :
    ((List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
      c.horizontalSuccessorVerticalFrontier n L data hn i).sum).sum
        (fun o z ↦
          if o.IsExternal n L data hn ∧ o.IsHomogeneousChild n L data hn then
            z • terminalPrimitiveRead n L data hn o.row.value else 0) =
      c.cell.coefficient • terminalPrimitiveRead n L data hn
        (horizontalComponentValue n L data hn c.cell.input) := by
  classical
  rw [← externalHomogeneousOccurrenceReadLinear_apply n L data hn]
  rw [map_list_sum]
  rw [List.map_ofFn]
  change (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
    externalHomogeneousOccurrenceReadLinear n L data hn
      (c.horizontalSuccessorVerticalFrontier n L data hn i)).sum = _
  have hchildren :
      (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
        externalHomogeneousOccurrenceReadLinear n L data hn
          (c.horizontalSuccessorVerticalFrontier n L data hn i)) =
      List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
        if (c.cell.horizontalOutputs.get i).2.IsComponent n L data hn then
          (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1) •
            terminalPrimitiveRead n L data hn
              (c.cell.horizontalOutputs.get i).2.value
        else 0 := by
    apply congrArg List.ofFn
    funext i
    rw [externalHomogeneousOccurrenceReadLinear_apply]
    exact c.externalHomogeneousRead_childFrontier n L data hn i
  rw [hchildren]
  cases hinput : c.cell.input with
  | component =>
      have h := c.cell.horizontal_eq
      rw [hinput] at h
      simp [horizontalExpansion] at h
  | marked root context mark left right =>
      have h := c.cell.horizontal_eq
      rw [hinput] at h
      simp only [horizontalExpansion] at h
      split at h
      · contradiction
      · rename_i hmark
        rw [Option.some.injEq] at h
        let readChild (q : ℤ × ProvenancedRow n L data hn) :=
          if q.2.IsComponent n L data hn then
            (c.cell.coefficient * q.1) •
              terminalPrimitiveRead n L data hn q.2.value
          else 0
        have hofFn :
            (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
              if (c.cell.horizontalOutputs.get i).2.IsComponent n L data hn then
                (c.cell.coefficient * (c.cell.horizontalOutputs.get i).1) •
                  terminalPrimitiveRead n L data hn
                    (c.cell.horizontalOutputs.get i).2.value
              else 0) = c.cell.horizontalOutputs.map readChild := by
          calc
            _ = (List.ofFn c.cell.horizontalOutputs.get).map readChild := by
              rw [List.map_ofFn]
              apply congrArg List.ofFn
              funext i
              rfl
            _ = _ := by rw [List.ofFn_get]
        rw [hofFn, ← h]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          readChild, ProvenancedRow.IsComponent, if_false, if_true,
          zero_add, one_mul]
        rw [horizontalComponentValue_marked_of_pos n L data hn
          root context mark left right hmark]
        simp

/-- The lower route's complete external homogeneous read is exactly the
common read of the upper route's homogeneous summand.  This is the global
marked-row/closed-square cancellation missing from the old local proof. -/
theorem GoverningWitness.externalHomogeneousRead_eq_globalVerticalComponentRead
    {a : L} (w : GoverningWitness n L data a) :
    w.externalHomogeneousRead n L data hn =
      terminalPrimitiveRead n L data hn
        (w.globalVerticalComponentValue n L data hn) := by
  classical
  rw [GoverningWitness.externalHomogeneousRead,
    GoverningWitness.globalHorizontalVerticalOccurrences]
  rw [← externalHomogeneousOccurrenceReadLinear_apply n L data hn]
  rw [map_list_sum]
  rw [w.globalVerticalComponentValue_eq_cell_sum n L data hn,
    map_list_sum]
  apply congrArg List.sum
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro c hc
  change externalHomogeneousOccurrenceReadLinear n L data hn
      ((List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
        c.horizontalSuccessorVerticalFrontier n L data hn i).sum) = _
  rw [externalHomogeneousOccurrenceReadLinear_apply,
    c.externalHomogeneousRead_cellFrontier n L data hn]
  change c.cell.coefficient • terminalPrimitiveRead n L data hn
      (horizontalComponentValue n L data hn c.cell.input) =
    terminalPrimitiveRead n L data hn
      (c.cell.coefficient •
        horizontalComponentValue n L data hn c.cell.input)
  rw [map_zsmul]

/-- Closed-square outside-edge identity before the wall partition.  The
initial governing read is the factor-one outside edge plus the complete
homogeneous external read; all lower-context marked terms have cancelled
globally in the preceding transfer--truncation calculation. -/
theorem GoverningWitness.terminalIncidenceRead_globalInitial_eq_outside_add_external
    {a : L} (w : GoverningWitness n L data a) :
    terminalIncidenceRead n L data hn
        (w.globalTriangularInitial n L data hn) =
      w.outsideInitialRead n L data hn +
        w.externalHomogeneousRead n L data hn := by
  rw [w.terminalIncidenceRead_globalInitial_eq_outside_add_cells
    n L data hn,
    w.externalHomogeneousRead_eq_globalVerticalComponentRead n L data hn,
    w.globalVerticalComponentValue_eq_cell_sum n L data hn,
    map_list_sum]
  congr 1
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  change c.cell.coefficient • terminalPrimitiveRead n L data hn
      (horizontalComponentValue n L data hn c.cell.input) =
    terminalPrimitiveRead n L data hn
      (c.cell.coefficient •
        horizontalComponentValue n L data hn c.cell.input)
  rw [map_zsmul]

/-- Internal copies and external homogeneous children exhaust the lower
route after the literal mark-zero children are killed. -/
theorem GoverningWitness.globalHorizontalVerticalRead_partition
    {a : L} (w : GoverningWitness n L data a) :
    (w.globalHorizontalVerticalOccurrences n L data hn).sum (fun o z ↦
        z • terminalPrimitiveRead n L data hn o.row.value) =
      w.internalHorizontalVerticalRead n L data hn +
        w.externalHomogeneousRead n L data hn := by
  classical
  rw [GoverningWitness.internalHorizontalVerticalRead,
    GoverningWitness.externalHomogeneousRead, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro o ho
  have hone := Finsupp.mem_support_iff.mp ho
  by_cases hint : o.IsInternal n L data hn
  · have hnotext : ¬o.IsExternal n L data hn := by
      exact not_not_intro hint
    simp [hint, hnotext]
  · have hext : o.IsExternal n L data hn := hint
    by_cases hhom : o.IsHomogeneousChild n L data hn
    · simp [hint, hext, hhom]
    · have hzero := w.globalExternalNonhomogeneous_value_eq_zero
          n L data hn o hone hext hhom
      simp [hint, hext, hhom, hzero]

/-- The source opener changes no coefficient or occurrence read.  This is
the local round trip needed to replace the external homogeneous filter by
the literal `globalComponentSources` list. -/
theorem GoverningWitness.componentSource?_terminalRead
    {a : L} (w : GoverningWitness n L data a)
    (o : CellHorizontalVerticalOccurrence n L data hn)
    (ho : w.globalHorizontalVerticalOccurrences n L data hn o ≠ 0) :
    (w.componentSource? n L data hn o ho).elim 0
        (GoverningComponentSource.terminalRead n L data hn) =
      if o.IsExternal n L data hn ∧ o.IsHomogeneousChild n L data hn then
        w.globalHorizontalVerticalOccurrences n L data hn o •
          terminalPrimitiveRead n L data hn o.row.value
      else 0 := by
  classical
  by_cases hext : o.IsExternal n L data hn
  · by_cases hhom : o.IsHomogeneousChild n L data hn
    · have hcomponent :=
          w.globalHorizontalVerticalOccurrence_isComponent
            n L data hn o ho hhom
      rcases o with ⟨parent, childIndex, verticalPath, row⟩
      cases row with
      | marked root context mark left right =>
          simp [ProvenancedRow.IsComponent] at hcomponent
      | component root context mark left right =>
          simp only [hext, hhom, and_self, if_true]
          unfold GoverningWitness.componentSource?
          simp only [hext, hhom]
          rfl
    · simp [GoverningWitness.componentSource?, hext, hhom]
  · simp [GoverningWitness.componentSource?, hext]

/-- The list of grouped component sources is an exact reindexing of the
external homogeneous occurrence filter.  The statement is at the level of
the common read, so proof fields introduced by opening a component row are
irrelevant and no equal-valued copies are combined. -/
theorem GoverningWitness.externalHomogeneousRead_eq_terminalComponentRead
    {a : L} (w : GoverningWitness n L data a) :
    w.externalHomogeneousRead n L data hn =
      terminalComponentRead n L data
        (w.globalComponentPBWPrimitive n L data hn) := by
  classical
  rw [w.terminalComponentRead_globalComponentPBWPrimitive_eq_sourceRead
    n L data hn]
  symm
  unfold GoverningWitness.externalHomogeneousRead
  unfold GoverningWitness.globalComponentSources
  let v := w.globalHorizontalVerticalOccurrences n L data hn
  let source? (o : {x // x ∈ v.support}) :=
    w.componentSource? n L data hn o.1
      (Finsupp.mem_support_iff.mp o.2)
  have filterMap_sum (xs : List {x // x ∈ v.support}) :
      ((xs.filterMap source?).map
          (GoverningComponentSource.terminalRead n L data hn)).sum =
        (xs.map fun o ↦
          (source? o).elim 0
            (GoverningComponentSource.terminalRead n L data hn)).sum := by
    induction xs with
    | nil => simp
    | cons o xs ih =>
        cases hsource : source? o with
        | none => simp [hsource, ih]
        | some s => simp [hsource, ih]
  change ((v.support.attach.toList.filterMap source?).map
      (GoverningComponentSource.terminalRead n L data hn)).sum = _
  rw [filterMap_sum]
  dsimp only [source?]
  simp_rw [w.componentSource?_terminalRead n L data hn]
  change (v.support.attach.toList.map (fun o ↦
      if o.1.IsExternal n L data hn ∧
          o.1.IsHomogeneousChild n L data hn then
        v o.1 • terminalPrimitiveRead n L data hn o.1.row.value
      else 0)).sum = _
  have htoList (s : Finset {x // x ∈ v.support})
      (f : {x // x ∈ v.support} → ZMod (2 ^ data.exponent)) :
      (s.toList.map f).sum = ∑ x ∈ s, f x := by
    induction s using Finset.induction with
    | empty => simp
    | insert x s hx ih => simp [hx, ih]
  rw [htoList]
  let read (o : CellHorizontalVerticalOccurrence n L data hn) :=
    if o.IsExternal n L data hn ∧ o.IsHomogeneousChild n L data hn then
      v o • terminalPrimitiveRead n L data hn o.row.value else 0
  calc
    _ = ∑ o ∈ v.support, read o := by
      simpa only [read] using Finset.sum_attach v.support read
    _ = _ := rfl

/-- Exact lower-route decomposition used by finite Stokes: the only part
not internally glued is the grouped complete PBW read of the homogeneous
children. -/
theorem GoverningWitness.globalHorizontalVerticalRead_eq_internal_add_component
    {a : L} (w : GoverningWitness n L data a) :
    (w.globalHorizontalVerticalOccurrences n L data hn).sum (fun o z ↦
        z • terminalPrimitiveRead n L data hn o.row.value) =
      w.internalHorizontalVerticalRead n L data hn +
        terminalComponentRead n L data
          (w.globalComponentPBWPrimitive n L data hn) := by
  rw [w.globalHorizontalVerticalRead_partition n L data hn,
    w.externalHomogeneousRead_eq_terminalComponentRead n L data hn]

/-- Exhaustive external-family form of the lower route. -/
theorem GoverningWitness.externalHomogeneousRead_wall_partition
    {a : L} (w : GoverningWitness n L data a) :
    w.externalHomogeneousRead n L data hn =
      w.outsideComponentRead n L data hn +
        w.factorTwoComponentRead n L data hn +
        ∑ k ∈ Finset.Ico 2 n,
          w.intermediateComponentRead n L data hn k := by
  rw [w.externalHomogeneousRead_eq_terminalComponentRead n L data hn,
    w.terminalComponentRead_wall_partition n L data hn]

/-- The path-labelled vertical ledger forgets to the sum of the literal
complete vertical operations at all comparison cells. -/
theorem GoverningWitness.globalVerticalRows_eq_cell_sum
    {a : L} (w : GoverningWitness n L data a) :
    w.globalVerticalRows n L data hn =
      ((w.globalLabelledComparisonTrace n L data hn).map
        (fun c : GoverningComparisonCell n L data hn ↦
        verticalOperation n L data hn (c.cell.cell n L data hn).base)).sum := by
  classical
  rw [GoverningWitness.globalVerticalRows,
    GoverningWitness.globalVerticalOccurrences]
  induction w.globalLabelledComparisonTrace n L data hn with
  | nil => simp
  | cons c cells ih =>
      simp only [List.map_cons, List.sum_cons]
      change (Finsupp.linearCombination ℤ
          (fun o : CellVerticalOccurrence n L data hn ↦
            Finsupp.single o.row (1 : ℤ)))
          (cells.map fun d ↦ d.verticalOccurrenceFrontier
            n L data hn).sum = _ at ih
      have hc := c.forget_verticalOccurrenceFrontier n L data hn
      change (Finsupp.linearCombination ℤ
          (fun o : CellVerticalOccurrence n L data hn ↦
            Finsupp.single o.row (1 : ℤ)))
          (c.verticalOccurrenceFrontier n L data hn) = _ at hc
      change (Finsupp.linearCombination ℤ
          (fun o : CellVerticalOccurrence n L data hn ↦
            Finsupp.single o.row (1 : ℤ)))
          (c.verticalOccurrenceFrontier n L data hn +
            (cells.map fun d ↦ d.verticalOccurrenceFrontier n L data hn).sum) = _
      rw [map_add, hc, ih]

/-- The path-labelled lower route forgets to `V (H R)` cell by cell. -/
theorem GoverningWitness.globalHorizontalVerticalRows_eq_cell_sum
    {a : L} (w : GoverningWitness n L data a) :
    w.globalHorizontalVerticalRows n L data hn =
      ((w.globalLabelledComparisonTrace n L data hn).map
        (fun c : GoverningComparisonCell n L data hn ↦
        verticalOperation n L data hn
          (horizontalOperation n L data hn
            (c.cell.cell n L data hn).base))).sum := by
  classical
  rw [GoverningWitness.globalHorizontalVerticalRows,
    GoverningWitness.globalHorizontalVerticalOccurrences]
  induction w.globalLabelledComparisonTrace n L data hn with
  | nil => simp
  | cons c cells ih =>
      simp only [List.map_cons, List.sum_cons]
      change (Finsupp.linearCombination ℤ
          (fun o : CellHorizontalVerticalOccurrence n L data hn ↦
            Finsupp.single o.row (1 : ℤ)))
          (cells.map fun d ↦
            (List.ofFn fun i : Fin d.cell.horizontalOutputs.length ↦
              d.horizontalSuccessorVerticalFrontier n L data hn i).sum).sum = _
        at ih
      change (Finsupp.linearCombination ℤ
          (fun o : CellHorizontalVerticalOccurrence n L data hn ↦
            Finsupp.single o.row (1 : ℤ)))
          ((List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
              c.horizontalSuccessorVerticalFrontier n L data hn i).sum +
            (cells.map fun d ↦
              (List.ofFn fun i : Fin d.cell.horizontalOutputs.length ↦
                d.horizontalSuccessorVerticalFrontier n L data hn i).sum).sum) = _
      rw [map_add, ih]
      congr 1
      rw [map_list_sum]
      calc
        ((List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
            c.horizontalSuccessorVerticalFrontier n L data hn i).map
            (Finsupp.linearCombination ℤ
              (fun o : CellHorizontalVerticalOccurrence n L data hn ↦
                Finsupp.single o.row (1 : ℤ)))).sum =
            (List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
              verticalOperation n L data hn
                (Finsupp.single
                  (c.cell.horizontalOutputs.get i).2
                  (c.cell.coefficient *
                    (c.cell.horizontalOutputs.get i).1))).sum := by
              apply congrArg List.sum
              rw [List.map_ofFn]
              apply congrArg List.ofFn
              funext i
              exact c.forget_horizontalSuccessorVerticalFrontier
                n L data hn i
        _ = verticalOperation n L data hn
              ((List.ofFn fun i : Fin c.cell.horizontalOutputs.length ↦
                Finsupp.single
                  (c.cell.horizontalOutputs.get i).2
                  (c.cell.coefficient *
                    (c.cell.horizontalOutputs.get i).1)).sum) := by
              rw [map_list_sum]
              apply congrArg List.sum
              rw [List.map_ofFn]
              apply congrArg List.ofFn
              funext i
              rfl
        _ = verticalOperation n L data hn
              (c.cell.horizontalSuccessorAggregate n L data hn) := by
              congr 1
              rw [LabelledComparisonCell.horizontalSuccessorAggregate,
                LabelledComparisonCell.horizontalSuccessorBases]
              apply congrArg List.sum
              calc
                List.ofFn (fun i : Fin c.cell.horizontalOutputs.length ↦
                    Finsupp.single (c.cell.horizontalOutputs.get i).2
                      (c.cell.coefficient *
                        (c.cell.horizontalOutputs.get i).1)) =
                    (List.ofFn c.cell.horizontalOutputs.get).map
                      (fun q ↦ Finsupp.single q.2
                        (c.cell.coefficient * q.1)) := by
                          rw [List.map_ofFn]
                          apply congrArg List.ofFn
                          funext i
                          rfl
                _ = _ := by rw [List.ofFn_get]
        _ = verticalOperation n L data hn
              (horizontalOperation n L data hn
                (c.cell.cell n L data hn).base) := by
              rw [c.cell.horizontalSuccessorAggregate_eq n L data hn]

/-- After all occurrence labels are retained and then forgotten, the sum of
the comparison-cell boundaries is exactly the difference between the two
routes `H(VR)` and `V(HR)`. -/
theorem GoverningWitness.globalTraceBoundary_eq_routes
    {a : L} (w : GoverningWitness n L data a) :
    traceIncidenceBoundary n L data hn
        ((w.globalLabelledComparisonTrace n L data hn).map
          GoverningComparisonCell.cell) =
      horizontalOperation n L data hn
          (w.globalVerticalRows n L data hn) -
        w.globalHorizontalVerticalRows n L data hn := by
  classical
  rw [traceIncidenceBoundary_eq]
  simp only [List.map_map]
  rw [w.globalVerticalRows_eq_cell_sum n L data hn,
    w.globalHorizontalVerticalRows_eq_cell_sum n L data hn,
    map_list_sum]
  induction w.globalLabelledComparisonTrace n L data hn with
  | nil => simp
  | cons c cells ih =>
      simp only [List.map_cons, List.sum_cons]
      simp only [Function.comp_apply] at ih ⊢
      rw [(c.cell.cell n L data hn).boundary_eq_horizontal_vertical_sub
        n L data hn, ih]
      abel

/-- Read form of the global closed square, still before any external-family
filter is applied. -/
theorem GoverningWitness.terminalIncidenceRead_global_routes_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    terminalIncidenceRead n L data hn
      (horizontalOperation n L data hn
          (w.globalVerticalRows n L data hn) -
        w.globalHorizontalVerticalRows n L data hn) = 0 := by
  rw [← w.globalTraceBoundary_eq_routes n L data hn]
  exact terminalIncidenceRead_traceIncidenceBoundary_eq_zero
    n L data hn _

/-- Occurrence-level read form of the uncut closed square.  This is the
starting equality for the external-family cancellation: the two sides use
one and the same functional, and every inherited integer coefficient is
still attached to its route occurrence. -/
theorem GoverningWitness.globalVerticalRead_eq_globalHorizontalVerticalRead
    {a : L} (w : GoverningWitness n L data a) :
    (w.globalVerticalOccurrences n L data hn).sum (fun o z ↦
        z • terminalPrimitiveRead n L data hn o.row.value) =
      (w.globalHorizontalVerticalOccurrences n L data hn).sum (fun o z ↦
        z • terminalPrimitiveRead n L data hn o.row.value) := by
  have h := w.terminalIncidenceRead_global_routes_eq_zero n L data hn
  rw [map_sub, terminalIncidenceRead_horizontalOperation,
    w.terminalIncidenceRead_globalVerticalRows n L data hn,
    w.terminalIncidenceRead_globalHorizontalVerticalRows n L data hn,
    sub_eq_zero] at h
  exact h

/-- All continuing lower-mark copies are accounted for by the numbered
internal gluings.  This is the read-level finite-Stokes cancellation after
the homogeneous child has been kept separate on both routes.  In
particular, no component term is discarded in deriving this equality. -/
theorem GoverningWitness.globalVerticalLowerMarkedRead_eq_internal
    {a : L} (w : GoverningWitness n L data a) :
    terminalPrimitiveRead n L data hn
        (w.globalVerticalLowerMarkedValue n L data hn) =
      w.internalHorizontalVerticalRead n L data hn := by
  have hroute := w.globalVerticalRead_eq_globalHorizontalVerticalRead
    n L data hn
  have hupper :
      (w.globalVerticalOccurrences n L data hn).sum (fun o z ↦
          z • terminalPrimitiveRead n L data hn o.row.value) =
        terminalPrimitiveRead n L data hn
            (w.globalVerticalLowerMarkedValue n L data hn) +
          terminalPrimitiveRead n L data hn
            (w.globalVerticalComponentValue n L data hn) := by
    calc
      _ = terminalPrimitiveRead n L data hn
          ((w.globalVerticalOccurrences n L data hn).sum (fun o z ↦
            z • o.row.value)) := by
              rw [map_finsuppSum]
              apply Finsupp.sum_congr
              intro o ho
              rw [map_zsmul]
      _ = _ := by
        rw [w.globalVerticalValue_eq_lower_add_component n L data hn,
          map_add]
  have hlower :
      (w.globalHorizontalVerticalOccurrences n L data hn).sum (fun o z ↦
          z • terminalPrimitiveRead n L data hn o.row.value) =
        w.internalHorizontalVerticalRead n L data hn +
          w.externalHomogeneousRead n L data hn :=
    w.globalHorizontalVerticalRead_partition n L data hn
  rw [hupper, hlower,
    w.externalHomogeneousRead_eq_globalVerticalComponentRead n L data hn]
    at hroute
  exact add_right_cancel hroute

end

end LieRings.MetabelianVanishing
