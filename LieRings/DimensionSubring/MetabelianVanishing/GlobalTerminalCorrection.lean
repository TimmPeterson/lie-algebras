import LieRings.DimensionSubring.MetabelianVanishing.GlobalClosedSquareRead
import LieRings.DimensionSubring.MetabelianVanishing.StepSeven

/-!
# Source primitive of the global terminal packet

The signed packet `B^(n)` was constructed from genuine full contextual
relations.  This file records its source primitive before any terminal
coordinate is taken.  The only discrepancy introduced by the canonical
terminal source lifts is the sum of the literal full-relation placement
commutators; no homogeneous component is promoted to a relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalTerminalCorrectionFintype : Fintype L :=
  Fintype.ofFinite L

/-! ## The exact uncut horizontal telescope -/

/-- The factor-one initial branches before applying any PBW or terminal
read.  Keeping the value in the enveloping algebra makes the ensuing
identity available simultaneously to the factor and primitive reads. -/
def GoverningWitness.outsideInitialWord
    {a : L} (w : GoverningWitness n L data a) :
    UEA ℤ (FreeModel n L) :=
  (List.ofFn fun i : Fin (w.globalInitialLabels n L data hn).length ↦
    let q := (w.globalInitialLabels n L data hn).get i
    if exponentWord n L data hn q.2.exponent = [] then
      q.1 • (q.2.row n L data hn).value
    else 0).sum

/-- Successive marks telescope before any read is chosen.  This is the
word-valued version of the horizontal part of the corrected closed square. -/
theorem sum_uncutComparisonTrace_componentValue
    (root : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2))
    (left : List (AdaptedIndex n L data hn))
    (x : AdaptedIndex n L data hn)
    (right : List (AdaptedIndex n L data hn))
    (path : List ℕ) (coefficient : ℤ) :
    ((uncutComparisonTrace n L data hn
        (.marked root context mark left (x :: right)) path coefficient).map
      fun c ↦ c.coefficient •
        horizontalComponentValue n L data hn c.input).sum =
      coefficient •
        (ProvenancedRow.marked root context mark left (x :: right) :
          ProvenancedRow n L data hn).value := by
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
            n L data hn _ (by
              simpa [ProvenancedRow.markValue] using hmark0)
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
        rw [hdecomp, smul_add]
        abel

/-- Sourcewise word-valued outside/telescope decomposition. -/
theorem GoverningWitness.outsideWord_add_branchComponentValue
    {a : L} (w : GoverningWitness n L data a)
    (i : Fin (w.globalInitialLabels n L data hn).length) :
    let q := (w.globalInitialLabels n L data hn).get i
    (if exponentWord n L data hn q.2.exponent = [] then
        q.1 • (q.2.row n L data hn).value
      else 0) +
      ((uncutComparisonTrace n L data hn (q.2.row n L data hn)
          [i.1] q.1).map fun c ↦
        c.coefficient • horizontalComponentValue n L data hn c.input).sum =
      q.1 • (q.2.row n L data hn).value := by
  let q := (w.globalInitialLabels n L data hn).get i
  change
    (if exponentWord n L data hn q.2.exponent = [] then
        q.1 • (q.2.row n L data hn).value
      else 0) +
      ((uncutComparisonTrace n L data hn (q.2.row n L data hn)
          [i.1] q.1).map fun c ↦
        c.coefficient • horizontalComponentValue n L data hn c.input).sum =
      q.1 • (q.2.row n L data hn).value
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
      exact sum_uncutComparisonTrace_componentValue n L data hn
        (triangularRelationOfIndex n L data q.2.relationTag)
        .hole ⟨n + 1, by omega⟩ [] x right [i.1] q.1

/-- The literal source-labelled initial list evaluates to the governing
word before equal source copies are combined. -/
theorem GoverningWitness.globalInitialLabelWordSum_eq_theta
    {a : L} (w : GoverningWitness n L data a) :
    (w.globalInitialLabels n L data hn |>.map fun q ↦
      q.1 • (q.2.row n L data hn).value).sum = w.theta := by
  have h := congrArg
    (Finsupp.linearCombination ℤ
      (ProvenancedRow.value n L data hn))
    (w.sum_globalInitialRows n L data hn)
  rw [map_list_sum] at h
  rw [GoverningWitness.globalInitialRows, List.map_map] at h
  have hsingle (q : ℤ × GlobalInitialPacketLabel n L data hn) :
      (Finsupp.linearCombination ℤ
          (ProvenancedRow.value n L data hn))
          (Finsupp.single (q.2.row n L data hn) q.1) =
        q.1 • (q.2.row n L data hn).value := by
    rw [Finsupp.linearCombination_single]
  rw [List.map_map] at h
  change ((w.globalInitialLabels n L data hn |>.map fun q ↦
      (Finsupp.linearCombination ℤ
        (ProvenancedRow.value n L data hn))
        (Finsupp.single (q.2.row n L data hn) q.1)).sum) =
    (Finsupp.linearCombination ℤ
      (ProvenancedRow.value n L data hn))
      (w.globalTriangularInitial n L data hn) at h
  simp_rw [hsingle] at h
  exact h.trans (w.evaluate_globalTriangularInitial n L data hn)

/-- Exact enveloping-word form of the global horizontal telescope.  Every
lower-context term is still present in `globalVerticalComponentValue`; no
homogeneous component has been declared to be a relation. -/
theorem GoverningWitness.theta_eq_outsideInitialWord_add_globalVerticalComponentValue
    {a : L} (w : GoverningWitness n L data a) :
    w.theta = w.outsideInitialWord n L data hn +
      w.globalVerticalComponentValue n L data hn := by
  have htrace :
      ((w.globalLabelledComparisonTrace n L data hn).map fun c ↦
          c.cell.coefficient •
            horizontalComponentValue n L data hn c.cell.input).sum =
        (List.ofFn fun i : Fin (w.globalInitialLabels n L data hn).length ↦
          ((uncutComparisonTrace n L data hn
            (((w.globalInitialLabels n L data hn).get i).2.row n L data hn)
            [i.1] ((w.globalInitialLabels n L data hn).get i).1).map fun c ↦
              c.coefficient •
                horizontalComponentValue n L data hn c.input).sum).sum := by
    rw [GoverningWitness.globalLabelledComparisonTrace,
      List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn]
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    rw [List.map_map]
    rfl
  rw [← w.globalInitialLabelWordSum_eq_theta n L data hn]
  symm
  rw [GoverningWitness.outsideInitialWord,
    w.globalVerticalComponentValue_eq_cell_sum n L data hn, htrace]
  let labels := w.globalInitialLabels n L data hn
  change
    (List.ofFn fun i : Fin labels.length ↦
      let q := labels.get i
      if exponentWord n L data hn q.2.exponent = [] then
        q.1 • (q.2.row n L data hn).value
      else 0).sum +
      (List.ofFn fun i : Fin labels.length ↦
        ((uncutComparisonTrace n L data hn
          ((labels.get i).2.row n L data hn) [i.1] (labels.get i).1).map
            fun c ↦ c.coefficient •
              horizontalComponentValue n L data hn c.input).sum).sum =
      (labels.map fun q ↦ q.1 • (q.2.row n L data hn).value).sum
  have sum_ofFn_add (m : ℕ)
      (f g : Fin m → UEA ℤ (FreeModel n L)) :
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
      (labels.map fun q ↦ q.1 • (q.2.row n L data hn).value).sum =
        (List.ofFn fun i : Fin labels.length ↦
          (labels.get i).1 •
            ((labels.get i).2.row n L data hn).value).sum := by
    apply congrArg List.sum
    calc
      labels.map (fun q ↦ q.1 • (q.2.row n L data hn).value) =
          (List.ofFn labels.get).map (fun q ↦
            q.1 • (q.2.row n L data hn).value) := by
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
  exact w.outsideWord_add_branchComponentValue n L data hn i

/-- The outside branch has only one displayed factor, so it is invisible to
the factor-two PBW symbol. -/
theorem GoverningWitness.rightSymbol_outsideInitialWord_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.outsideInitialWord n L data hn) = 0 := by
  classical
  rw [GoverningWitness.outsideInitialWord, map_list_sum]
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [List.mem_ofFn] at hy
  obtain ⟨i, rfl⟩ := hy
  let q := (w.globalInitialLabels n L data hn).get i
  change rightSymbol n L data hn 2 n (by omega)
    (if exponentWord n L data hn q.2.exponent = [] then
      q.1 • (q.2.row n L data hn).value else 0) = 0
  by_cases hword : exponentWord n L data hn q.2.exponent = []
  · rw [if_pos hword, map_zsmul]
    have hrow : q.2.row n L data hn =
        .marked (triangularRelationOfIndex n L data q.2.relationTag)
          .hole ⟨n + 1, by omega⟩ [] [] := by
      simp [GlobalInitialPacketLabel.row, hword]
    rw [hrow,
      rightSymbol_provenancedRow_eq_zero_of_factorCount_lt
        n L data hn 2 n (by omega) _ (by
          simp [ProvenancedRow.factorCount])]
    exact smul_zero _
  · rw [if_neg hword, map_zero]

/-- The complete upper-route component word has zero factor-two symbol.
This is the governing PBW coefficient equation after the exact horizontal
telescope; no individual lower-context component is asserted to vanish. -/
theorem GoverningWitness.rightSymbol_globalVerticalComponentValue_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.globalVerticalComponentValue n L data hn) = 0 := by
  have h := congrArg (rightSymbol n L data hn 2 n (by omega))
    (w.theta_eq_outsideInitialWord_add_globalVerticalComponentValue
      n L data hn)
  rw [map_add, rightSymbol_theta_terminal_eq_zero n L data hn w,
    w.rightSymbol_outsideInitialWord_eq_zero n L data hn, zero_add] at h
  exact h.symm

/-! ## The single placed word carried by the factor-two cut -/

/-- The evaluated placed word of the exact pre-Smith cut `B`.  This is kept
as one aggregate because its factor-two and one-factor PBW reads must be
taken from the same labelled occurrences. -/
def GoverningWitness.globalFactorTwoPlacedWord
    {a : L} (w : GoverningWitness n L data a) :
  UEA ℤ (FreeModel n L) :=
  (w.factorTwoPreSmithOccurrences n L data hn).sum fun o z ↦
    z • (o.terminal.row n L data hn).value

/-- The factor-two read of that same placed word is exactly the Koszul
boundary of `B^(n)`.  No second lift or independently chosen coefficient
family occurs here. -/
theorem GoverningWitness.rightSymbol_globalFactorTwoPlacedWord
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.globalFactorTwoPlacedWord n L data hn) =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.globalFactorTwoChain n L data hn) := by
  classical
  rw [GoverningWitness.globalFactorTwoPlacedWord, map_finsuppSum,
    w.globalFactorTwoChain_eq_preSmithSum n L data hn,
    map_finsuppSum]
  apply Finsupp.sum_congr
  intro o ho
  rw [map_zsmul, map_zsmul, ProvenancedTerminalTwo.dOne_chain]
  congr 1

/-- Forgetting the subtype label on the factor-two cut gives the literal
conditional read on the complete vertical occurrence ledger.  This is the
form in which the global marked-row telescope is applied below. -/
theorem GoverningWitness.dOne_globalFactorTwoChain_eq_globalVerticalCutRead
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.globalFactorTwoChain n L data hn) =
      (w.globalVerticalOccurrences n L data hn).sum fun o z ↦
        if o.IsFactorTwoCut n L data hn then
          z • rightSymbol n L data hn 2 n (by omega) o.row.value
        else 0 := by
  classical
  rw [w.dOne_globalFactorTwoChain_eq_cut_read n L data hn,
    GoverningWitness.factorTwoCutOccurrences,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro o ho
  by_cases hcut : o.IsFactorTwoCut n L data hn
  · rw [dif_pos hcut, Finsupp.sum_single_index (by simp), if_pos hcut]
  · rw [dif_neg hcut, if_neg hcut]
    simp

/-- Complete one-factor PBW primitive of the literal placed factor-two
occurrences in `B`, before the harmless source-lift relations are added. -/
def GoverningWitness.globalFactorTwoPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.factorTwoPreSmithOccurrences n L data hn).sum fun o z ↦
    z • o.terminal.primitive n L data hn

/-- The complete primitive of the placed cut word is the primitive retained
occurrence by occurrence below. -/
theorem GoverningWitness.pbwPrimitive_globalFactorTwoPlacedWord
    {a : L} (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn
        (w.globalFactorTwoPlacedWord n L data hn) =
      w.globalFactorTwoPrimitive n L data hn := by
  classical
  rw [GoverningWitness.globalFactorTwoPlacedWord,
    GoverningWitness.globalFactorTwoPrimitive, map_finsuppSum]
  apply Finsupp.sum_congr
  intro o ho
  rw [map_zsmul]
  rfl

/-- The aggregate genuine relation introduced when the canonical source
presentation places every full contextual relation on the left. -/
def GoverningWitness.globalFactorTwoPlacementRelation
    {a : L} (w : GoverningWitness n L data a) : Relations n L data :=
  (w.factorTwoPreSmithOccurrences n L data hn).sum fun o z ↦
    z • o.terminal.sourcePlacementRelation n L data hn

/-- Exact source-primitive formula for the manuscript's `B^(n)`.  The
formula is obtained occurrence by occurrence from the retained full
relation, so it does not use a component-head replacement at a lower
context. -/
theorem GoverningWitness.terminalSourcePrimitive_globalFactorTwoChain
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (w.globalFactorTwoChain n L data hn) =
      w.globalFactorTwoPrimitive n L data hn +
        (w.globalFactorTwoPlacementRelation n L data hn : FreeModel n L) := by
  classical
  unfold GoverningWitness.globalFactorTwoPrimitive
    GoverningWitness.globalFactorTwoPlacementRelation
  rw [w.globalFactorTwoChain_eq_preSmithSum n L data hn,
    map_finsuppSum]
  simp_rw [map_zsmul,
    ProvenancedTerminalTwo.terminalSourcePrimitive_chain,
    smul_add]
  rw [Finsupp.sum_add]
  congr 1
  change _ = (Relations n L data).subtype
    ((w.factorTwoPreSmithOccurrences n L data hn).sum fun o z ↦
      z • o.terminal.sourcePlacementRelation n L data hn)
  rw [map_finsuppSum]
  rfl

/-- Once the factor-two boundary calculation has made `B^(n)` a genuine
cycle, subtracting its aggregate source-placement relation leaves the
literal PBW primitive of the same terminal occurrences as a certified
top-layer preimage. -/
def GoverningWitness.globalFactorTwoPrimitivePreimage
    {a : L} (w : GoverningWitness n L data a)
    (hcycle : Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.globalFactorTwoChain n L data hn) = 0) :
    TopPreimage n L data :=
  terminalSourceCyclePreimage n L data hn
      ⟨w.globalFactorTwoChain n L data hn, hcycle⟩ -
    relationTopPreimage n L data
      (w.globalFactorTwoPlacementRelation n L data hn)

@[simp] theorem GoverningWitness.globalFactorTwoPrimitivePreimage_coe
    {a : L} (w : GoverningWitness n L data a)
    (hcycle : Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.globalFactorTwoChain n L data hn) = 0) :
    (w.globalFactorTwoPrimitivePreimage n L data hn hcycle :
        FreeModel n L) = w.globalFactorTwoPrimitive n L data hn := by
  rw [GoverningWitness.globalFactorTwoPrimitivePreimage]
  change (terminalSourceCyclePreimage n L data hn
      ⟨w.globalFactorTwoChain n L data hn, hcycle⟩ : FreeModel n L) -
      (relationTopPreimage n L data
        (w.globalFactorTwoPlacementRelation n L data hn) : FreeModel n L) = _
  rw [terminalSourceCyclePreimage_coe]
  change terminalSourcePrimitive n L data hn
      (w.globalFactorTwoChain n L data hn) -
        (w.globalFactorTwoPlacementRelation n L data hn : FreeModel n L) = _
  rw [w.terminalSourcePrimitive_globalFactorTwoChain n L data hn]
  abel

/-- Source placement does not change the terminal cyclic coordinate.  This
is the coordinate form of the primitive read `alpha(T)=[sigma z]` for the
single terminal chain read from `B^(n)`. -/
theorem GoverningWitness.terminalEval_globalFactorTwoCycle_eq_primitive
    {a : L} (w : GoverningWitness n L data a)
    (hcycle : Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.globalFactorTwoChain n L data hn) = 0) :
    terminalEval n L data
        (terminalSourceCyclePreimage n L data hn
          ⟨w.globalFactorTwoChain n L data hn, hcycle⟩) =
      terminalEval n L data
        (w.globalFactorTwoPrimitivePreimage n L data hn hcycle) := by
  rw [GoverningWitness.globalFactorTwoPrimitivePreimage, map_sub,
    terminalEval_relationTopPreimage, sub_zero]

end

end LieRings.MetabelianVanishing
