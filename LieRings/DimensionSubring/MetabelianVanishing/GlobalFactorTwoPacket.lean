import LieRings.DimensionSubring.MetabelianVanishing.GlobalCutPackets
import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmithCollector

/-!
# The exact factor-two occurrence packet

This file constructs the manuscript's signed pre-Smith list `B` from the
actual global factor-two cut.  It then projects each occurrence to
`D_n \otimes A_n` and expands both entries in the fixed terminal Smith
bases, retaining the source occurrence in every resulting index.  Thus
equal algebraic summands with different ancestry remain different copies.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalFactorTwoPacketFintype : Fintype L :=
  Fintype.ofFinite L

/-- Recognize the genuine terminal relation wall carried by a vertical
factor-two occurrence, returning its literal row equality as part of the
result. -/
def factorTwoTerminalData?
    (o : CellVerticalOccurrence n L data hn) :
    Option (ProvenancedTerminalTwo n L data hn) :=
  match o.row with
  | .marked root context mark [factor] [] =>
      if hactive :
          mark.val + RelationContext.weight n L data hn context = n then
        some ⟨root, context, mark, factor, hactive⟩
      else none
  | _ => none

/-- Successful recognition records the literal row it recognized. -/
theorem factorTwoTerminalData?_row_eq
    (o : CellVerticalOccurrence n L data hn)
    (c : ProvenancedTerminalTwo n L data hn)
    (h : factorTwoTerminalData? n L data hn o = some c) :
    o.row = c.row n L data hn := by
  classical
  cases hrow : o.row with
  | component =>
      simp [factorTwoTerminalData?, hrow] at h
  | marked root context mark left right =>
      cases left with
      | nil => simp [factorTwoTerminalData?, hrow] at h
      | cons factor tail =>
          cases tail with
          | cons x xs => simp [factorTwoTerminalData?, hrow] at h
          | nil =>
              cases right with
              | cons x xs => simp [factorTwoTerminalData?, hrow] at h
              | nil =>
                  by_cases hactive :
                      mark.val + RelationContext.weight n L data hn context = n
                  · simp [factorTwoTerminalData?, hrow, hactive] at h
                    subst c
                    simp [ProvenancedTerminalTwo.row]
                  · simp [factorTwoTerminalData?, hrow, hactive] at h

/-- One coefficient copy in the signed pre-Smith list `B`.  The raw cut
occurrence, the full contextual relation wall, and their literal row
equality are all retained. -/
structure GlobalFactorTwoOccurrence where
  cutOccurrence : {o : CellVerticalOccurrence n L data hn //
    o.IsFactorTwoCut n L data hn}
  terminal : ProvenancedTerminalTwo n L data hn
  row_eq : cutOccurrence.1.row = terminal.row n L data hn

noncomputable instance :
    DecidableEq (GlobalFactorTwoOccurrence n L data hn) :=
  Classical.decEq _

/-- The factor-two subtype ledger is a literal restriction: at every cut
index its coefficient is the coefficient of the underlying vertical
occurrence. -/
theorem GoverningWitness.factorTwoCutOccurrences_apply
    {a : L} (w : GoverningWitness n L data a)
    (o : {o : CellVerticalOccurrence n L data hn //
      o.IsFactorTwoCut n L data hn}) :
    w.factorTwoCutOccurrences n L data hn o =
      w.globalVerticalOccurrences n L data hn o.1 := by
  classical
  rw [GoverningWitness.factorTwoCutOccurrences, Finsupp.sum_apply]
  let v := w.globalVerticalOccurrences n L data hn
  change v.sum (fun a z ↦
      (if h : a.IsFactorTwoCut n L data hn then
        Finsupp.single ⟨a, h⟩ z else 0) o) = v o.1
  have hsum :
      v.sum (fun a z ↦ (Finsupp.single a z :
        CellVerticalOccurrence n L data hn →₀ ℤ)) = v := by
    exact Finsupp.sum_single v
  have happ := congrArg (fun q ↦ q o.1) hsum
  change (v.sum (fun a z ↦ Finsupp.single a z)) o.1 = v o.1 at happ
  rw [Finsupp.sum_apply] at happ
  apply Eq.trans ?_ happ
  apply Finsupp.sum_congr
  intro a ha
  by_cases hcut : a.IsFactorTwoCut n L data hn
  · by_cases hao : a = o.1
    · subst a
      simp [hcut]
    · have hsub :
          (⟨a, hcut⟩ : {r : CellVerticalOccurrence n L data hn //
            r.IsFactorTwoCut n L data hn}) ≠ o := by
        intro h
        exact hao (congrArg Subtype.val h)
      simp [hcut, hao, hsub]
  · have hao : a ≠ o.1 := by
      intro h
      subst a
      exact hcut o.2
    simp [hcut, hao]

/-- The terminal-wall recognizer accepts every supported factor-two cut.
Thus the definition of `B` below discards only formal zero indices. -/
theorem GoverningWitness.factorTwoTerminalData?_isSome_of_mem_support
    {a : L} (w : GoverningWitness n L data a)
    (o : {o : CellVerticalOccurrence n L data hn //
      o.IsFactorTwoCut n L data hn})
    (ho : o ∈ (w.factorTwoCutOccurrences n L data hn).support) :
    (factorTwoTerminalData? n L data hn o.1).isSome := by
  have hvertical : w.globalVerticalOccurrences n L data hn o.1 ≠ 0 := by
    rw [← w.factorTwoCutOccurrences_apply n L data hn o]
    exact Finsupp.mem_support_iff.mp ho
  have hmarked := w.globalVerticalOccurrence_isMarked
    n L data hn o.1 hvertical
  have hnormal := w.globalVerticalOccurrence_isVerticalNormal
    n L data hn o.1 hvertical
  cases hrow : o.1.row with
  | component =>
      rw [hrow] at hmarked
      exact False.elim hmarked
  | marked root context mark left right =>
      rw [hrow] at hnormal
      have hcut := o.2
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
              have hactive :
                  mark.val + RelationContext.weight n L data hn context = n := by
                simpa [ProvenancedRow.activeWeight] using hcut.2
              simp [factorTwoTerminalData?, hrow, hactive]
          | cons x xs => simp at hfactor

/-- The signed pre-Smith factor-two list `B`.  Unsupported formal subtype
values are discarded by the syntactic terminal-wall recognizer; the support
theorem below proves that no actual cut occurrence is lost. -/
def GoverningWitness.factorTwoPreSmithOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    GlobalFactorTwoOccurrence n L data hn →₀ ℤ :=
  (w.factorTwoCutOccurrences n L data hn).sum fun o z ↦
    match h : factorTwoTerminalData? n L data hn o.1 with
    | none => 0
    | some c => Finsupp.single
        { cutOccurrence := o
          terminal := c
          row_eq := factorTwoTerminalData?_row_eq n L data hn o.1 c
            h }
        z

/-- Projection of the full contextual relation carried by one `B`
occurrence to `D_n`. -/
def GlobalFactorTwoOccurrence.relationPrefix
    (o : GlobalFactorTwoOccurrence n L data hn) :
    D n L data n (by omega) :=
  fullRelationToD n L data n (by omega)
    (RelationContext.relation n L data hn
      o.terminal.context o.terminal.root)

/-- Projection of its ordinary factor to `A_n`. -/
def GlobalFactorTwoOccurrence.factorPrefix
    (o : GlobalFactorTwoOccurrence n L data hn) : A L n :=
  prLE n L n (by omega)
    (adaptedBasis n L data hn o.terminal.factor)

/-- A two-input descendant of target weight `n+1` cannot use the deleted
top homogeneous coordinate: positivity forces both input weights to be at
most `n`.  The conclusion records the two literal prefix formulas, so this
is exactly the no-loss statement needed before the quadratic block. -/
theorem factorTwo_target_projection_preserves_inputs
    (i j : AdaptedIndex n L data hn)
    (htarget :
      (adaptedWeightedBasis n L data hn).weight i +
        (adaptedWeightedBasis n L data hn).weight j = n + 1) :
    ∃ (hi : i.1.val < n) (hj : j.1.val < n),
      prLE n L n (by omega) (adaptedBasis n L data hn i) =
          FreeMetabelian.Free.weightIncl i.1.val hi
            (pieceAdaptedBasis n L data hn i.1 i.2) ∧
        prLE n L n (by omega) (adaptedBasis n L data hn j) =
          FreeMetabelian.Free.weightIncl j.1.val hj
            (pieceAdaptedBasis n L data hn j.1 j.2) := by
  have hi : i.1.val < n := by
    have hjpos := (adaptedWeightedBasis n L data hn).weight_pos j
    change i.1.val + 1 + (j.1.val + 1) = n + 1 at htarget
    omega
  have hj : j.1.val < n := by
    have hipos := (adaptedWeightedBasis n L data hn).weight_pos i
    change i.1.val + 1 + (j.1.val + 1) = n + 1 at htarget
    omega
  refine ⟨hi, hj, ?_, ?_⟩
  · rw [adaptedBasis_apply]
    exact FreeMetabelian.Free.projectPrefix_weightIncl_of_lt
      n i.1.val (by omega) i.1.isLt hi _
  · rw [adaptedBasis_apply]
    exact FreeMetabelian.Free.projectPrefix_weightIncl_of_lt
      n j.1.val (by omega) j.1.isLt hj _

namespace GlobalFactorTwoOccurrence

/-- Canonical two-basis expansion of one projected pre-Smith occurrence,
still indexed by its original source copy. -/
def smithExpandedChain (o : GlobalFactorTwoOccurrence n L data hn) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  ((terminalSmith n L data hn).relationBasis.repr
      (o.relationPrefix n L data hn)).sum fun i di ↦
    ((terminalSmith n L data hn).ambientBasis.repr
      (o.factorPrefix n L data hn)).sum fun j xj ↦
      (di * xj) •
        ((terminalSmith n L data hn).relationBasis i ⊗ₜ[ℤ]
          SymmetricPower.degreeOne
            ((terminalSmith n L data hn).ambientBasis j))

/-- Expanding both projected entries in the Smith bases loses no value.
This is the local sign-and-multiplicity statement behind the passage
`B \mapsto B^(n)`. -/
theorem smithExpandedChain_eq_terminal_chain
    (o : GlobalFactorTwoOccurrence n L data hn) :
    o.smithExpandedChain n L data hn =
      o.terminal.chain n L data hn := by
  classical
  let RB := (terminalSmith n L data hn).relationBasis
  let AB := (terminalSmith n L data hn).ambientBasis
  let d := o.relationPrefix n L data hn
  let x := o.factorPrefix n L data hn
  have hd : (RB.repr d).sum (fun i z ↦ z • RB i) = d := by
    rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
    exact RB.sum_repr d
  have hx : (AB.repr x).sum (fun j z ↦ z • AB j) = x := by
    rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
    exact AB.sum_repr x
  have hdegree :
      (AB.repr x).sum (fun j z ↦
          z • SymmetricPower.degreeOne (R := ℤ) (AB j)) =
        SymmetricPower.degreeOne (R := ℤ) x := by
    calc
      _ = SymmetricPower.degreeOne (R := ℤ)
          ((AB.repr x).sum (fun j z ↦ z • AB j)) := by
        rw [map_finsuppSum]
        apply Finsupp.sum_congr
        intro j hj
        rw [map_zsmul]
      _ = _ := by rw [hx]
  change (RB.repr d).sum (fun i di ↦
      (AB.repr x).sum (fun j xj ↦
        (di * xj) • (RB i ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (AB j)))) = _
  calc
    _ = (RB.repr d).sum (fun i di ↦
          di • (RB i ⊗ₜ[ℤ]
            SymmetricPower.degreeOne x)) := by
      apply Finsupp.sum_congr
      intro i hi
      calc
        (AB.repr x).sum (fun j xj ↦
            ((RB.repr d) i * xj) •
              (RB i ⊗ₜ[ℤ] SymmetricPower.degreeOne (AB j))) =
            (AB.repr x).sum (fun j xj ↦
              (RB.repr d) i •
                (RB i ⊗ₜ[ℤ]
                  (xj • SymmetricPower.degreeOne (AB j)))) := by
          apply Finsupp.sum_congr
          intro j hj
          exact (TensorProduct.smul_tmul_smul
            ((RB.repr d) i) ((AB.repr x) j) (RB i)
              (SymmetricPower.degreeOne (AB j))).symm
        _ = (RB.repr d) i •
              (AB.repr x).sum (fun j xj ↦
                RB i ⊗ₜ[ℤ]
                  (xj • SymmetricPower.degreeOne (AB j))) := by
          exact Finsupp.smul_sum.symm
        _ = (RB.repr d) i •
              (RB i ⊗ₜ[ℤ]
                (AB.repr x).sum (fun j xj ↦
                  xj • SymmetricPower.degreeOne (AB j))) := by
          congr 1
          simp only [Finsupp.sum, TensorProduct.tmul_sum]
        _ = _ := by rw [hdegree]
    _ = ((RB.repr d).sum (fun i di ↦ di • RB i)) ⊗ₜ[ℤ]
          SymmetricPower.degreeOne x := by
      simp only [Finsupp.sum, TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl
      intro i hi
      exact TensorProduct.smul_tmul' _ _ _
    _ = d ⊗ₜ[ℤ] SymmetricPower.degreeOne x := by rw [hd]
    _ = _ := by
      unfold d x GlobalFactorTwoOccurrence.relationPrefix
        GlobalFactorTwoOccurrence.factorPrefix ProvenancedTerminalTwo.chain
      rw [SymmetricPower.degreeOne_apply]
      congr 2
      funext i
      fin_cases i
      rfl

end GlobalFactorTwoOccurrence

/-- One coefficient copy after projection and canonical expansion in both
terminal Smith bases.  The source occurrence is part of the index. -/
structure GlobalFactorTwoSmithOccurrence where
  source : GlobalFactorTwoOccurrence n L data hn
  relationIndex : TerminalSmithIndex n L data hn
  factorIndex : TerminalSmithIndex n L data hn

noncomputable instance :
    DecidableEq (GlobalFactorTwoSmithOccurrence n L data hn) :=
  Classical.decEq _

/-- The manuscript's `B^(n)`: project `B`, delete zero coefficients, and
expand both entries in the fixed relation and ambient Smith bases. -/
def GoverningWitness.factorTwoSmithOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    GlobalFactorTwoSmithOccurrence n L data hn →₀ ℤ :=
  (w.factorTwoPreSmithOccurrences n L data hn).sum fun o z ↦
    ((terminalSmith n L data hn).relationBasis.repr
      (o.relationPrefix n L data hn)).sum fun i di ↦
    ((terminalSmith n L data hn).ambientBasis.repr
      (o.factorPrefix n L data hn)).sum fun j xj ↦
      Finsupp.single
        ({ source := o, relationIndex := i, factorIndex := j } :
          GlobalFactorTwoSmithOccurrence n L data hn)
        (z * di * xj)

namespace GlobalFactorTwoSmithOccurrence

/-- Genuine degree-one Koszul row represented by one expanded occurrence
of `B^(n)`. -/
def realization (o : GlobalFactorTwoSmithOccurrence n L data hn) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (terminalSmith n L data hn).relationBasis o.relationIndex ⊗ₜ[ℤ]
    SymmetricPower.degreeOne
      ((terminalSmith n L data hn).ambientBasis o.factorIndex)

/-- Its literal symmetric boundary. -/
def boundary (o : GlobalFactorTwoSmithOccurrence n L data hn) :
    Sym[ℤ] (Fin 2) (A L n) :=
  SymmetricPower.insert ℤ (A L n) 1
    ((terminalSmith n L data hn).relationBasis o.relationIndex : A L n)
    (SymmetricPower.degreeOne
      ((terminalSmith n L data hn).ambientBasis o.factorIndex))

@[simp] theorem dOne_realization
    (o : GlobalFactorTwoSmithOccurrence n L data hn) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (o.realization n L data hn) = o.boundary n L data hn := by
  rw [realization, boundary, Koszul.dOne_tmul]
  rfl

end GlobalFactorTwoSmithOccurrence

/-- The terminal packet `chi_n`, definitionally the signed sum of the exact
expanded occurrence list `B^(n)`. -/
def GoverningWitness.globalFactorTwoChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (w.factorTwoSmithOccurrences n L data hn).sum fun o z ↦
    z • o.realization n L data hn

/-- Passing from the signed pre-Smith list `B` to the doubly expanded
list `B^(n)` preserves every source coefficient, sign, and multiplicity.
In particular, the resulting Koszul chain is exactly the sum of the
genuine terminal chains carried by the original occurrences. -/
theorem GoverningWitness.globalFactorTwoChain_eq_preSmithSum
    {a : L} (w : GoverningWitness n L data a) :
    w.globalFactorTwoChain n L data hn =
      (w.factorTwoPreSmithOccurrences n L data hn).sum fun o z ↦
        z • o.terminal.chain n L data hn := by
  classical
  rw [GoverningWitness.globalFactorTwoChain,
    GoverningWitness.factorTwoSmithOccurrences,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro o ho
  rw [Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  rw [← o.smithExpandedChain_eq_terminal_chain n L data hn,
    GlobalFactorTwoOccurrence.smithExpandedChain]
  have houter :
      (w.factorTwoPreSmithOccurrences n L data hn) o •
          ((terminalSmith n L data hn).relationBasis.repr
            (o.relationPrefix n L data hn)).sum (fun i di ↦
              ((terminalSmith n L data hn).ambientBasis.repr
                (o.factorPrefix n L data hn)).sum (fun j xj ↦
                  (di * xj) •
                    ((terminalSmith n L data hn).relationBasis i ⊗ₜ[ℤ]
                      SymmetricPower.degreeOne (R := ℤ)
                        ((terminalSmith n L data hn).ambientBasis j)))) =
        ((terminalSmith n L data hn).relationBasis.repr
          (o.relationPrefix n L data hn)).sum (fun i di ↦
            (w.factorTwoPreSmithOccurrences n L data hn) o •
              ((terminalSmith n L data hn).ambientBasis.repr
                (o.factorPrefix n L data hn)).sum (fun j xj ↦
                  (di * xj) •
                    ((terminalSmith n L data hn).relationBasis i ⊗ₜ[ℤ]
                      SymmetricPower.degreeOne (R := ℤ)
                        ((terminalSmith n L data hn).ambientBasis j)))) := by
    exact Finsupp.smul_sum
  refine Eq.trans ?_ houter.symm
  apply Finsupp.sum_congr
  intro i hi
  rw [Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  have hinner :
      (w.factorTwoPreSmithOccurrences n L data hn) o •
          ((terminalSmith n L data hn).ambientBasis.repr
            (o.factorPrefix n L data hn)).sum (fun j xj ↦
              (((terminalSmith n L data hn).relationBasis.repr
                  (o.relationPrefix n L data hn)) i * xj) •
                ((terminalSmith n L data hn).relationBasis i ⊗ₜ[ℤ]
                  SymmetricPower.degreeOne (R := ℤ)
                    ((terminalSmith n L data hn).ambientBasis j))) =
        ((terminalSmith n L data hn).ambientBasis.repr
          (o.factorPrefix n L data hn)).sum (fun j xj ↦
            (w.factorTwoPreSmithOccurrences n L data hn) o •
              ((((terminalSmith n L data hn).relationBasis.repr
                  (o.relationPrefix n L data hn)) i * xj) •
                ((terminalSmith n L data hn).relationBasis i ⊗ₜ[ℤ]
                  SymmetricPower.degreeOne (R := ℤ)
                    ((terminalSmith n L data hn).ambientBasis j)))) := by
    exact Finsupp.smul_sum
  refine Eq.trans ?_ hinner.symm
  apply Finsupp.sum_congr
  intro j hj
  rw [Finsupp.sum_single_index (by simp)]
  dsimp [GlobalFactorTwoSmithOccurrence.realization]
  rw [smul_smul]
  congr 1
  ring

/-- Exact factor-two boundary, with the same occurrence indices,
coefficients, signs, and multiplicities as `B^(n)`. -/
theorem GoverningWitness.dOne_globalFactorTwoChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.globalFactorTwoChain n L data hn) =
      (w.factorTwoSmithOccurrences n L data hn).sum fun o z ↦
        z • o.boundary n L data hn := by
  classical
  rw [GoverningWitness.globalFactorTwoChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro o ho
  rw [map_zsmul, GlobalFactorTwoSmithOccurrence.dOne_realization]
  rfl

/-- Boundary of `B^(n)` read directly on the actual signed factor-two cut.
This removes the Smith coordinates but retains every cut occurrence and its
coefficient. -/
theorem GoverningWitness.dOne_globalFactorTwoChain_eq_cut_read
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.globalFactorTwoChain n L data hn) =
      (w.factorTwoCutOccurrences n L data hn).sum fun o z ↦
        z • rightSymbol n L data hn 2 n (by omega) o.1.row.value := by
  classical
  rw [w.globalFactorTwoChain_eq_preSmithSum n L data hn,
    map_finsuppSum]
  simp_rw [map_zsmul, ProvenancedTerminalTwo.dOne_chain]
  rw [GoverningWitness.factorTwoPreSmithOccurrences,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro o ho
  split
  · rename_i hterminal
    have himpossible := w.factorTwoTerminalData?_isSome_of_mem_support
      n L data hn o ho
    simp [hterminal] at himpossible
  · rename_i c hterminal
    rw [Finsupp.sum_single_index (by simp)]
    rw [factorTwoTerminalData?_row_eq n L data hn o.1 c hterminal]
    rfl

end

end LieRings.MetabelianVanishing
