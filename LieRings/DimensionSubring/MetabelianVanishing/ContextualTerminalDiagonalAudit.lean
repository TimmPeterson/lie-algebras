import LieRings.DimensionSubring.MetabelianVanishing.ExceptionalTriangularComb

/-!
# Exact audit of the terminal contextual diagonal

The boundary of `contextualSymbolChain` on `(q,k) = (1,n)` is not, by
itself, the complete terminal component defect.  At one truncation cell the
marked prefix is the sum of the preceding prefix and the newly exposed
component.  Moreover, the complete factor-two defect also contains PBW
factor-two reads of cells away from that literal diagonal.

This file records the exact finite identity, with both omitted terms visible.
It is deliberately only an audit: neither omitted term is asserted to vanish.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance contextualTerminalDiagonalAuditFintype : Fintype L :=
  Fintype.ofFinite L

/-- The same marked occurrence one truncation step earlier. -/
def ProvenancedCell.previousMarkedRow
    (c : ProvenancedCell n L data hn) : ProvenancedRow n L data hn :=
  .marked c.root c.context ⟨c.mark.val - 1, by omega⟩ c.left []

/-- The factor-two terminal-prefix symbol which precedes the component
exposed by this cell. -/
def ProvenancedCell.previousPrefixFactorTwo
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  rightSymbol n L data hn 2 n (by omega)
    (c.previousMarkedRow n L data hn).value

/-- Cellwise transfer--truncation identity in the exact terminal factor
number.  This is just `prefix_step`, with no component promoted to a
relation. -/
theorem ProvenancedCell.markedFactorTwo_eq_previous_add_component
    (c : ProvenancedCell n L data hn) :
    rightSymbol n L data hn 2 n (by omega) c.markedRow.value =
      c.previousPrefixFactorTwo n L data hn +
        c.factorEdge n L data hn 2 n (by omega) := by
  have hstep := RelationContext.prefix_step n L data hn
    c.context c.root c.mark c.mark_pos
  have hvalue : c.markedRow.value =
      (c.previousMarkedRow n L data hn).value + c.componentRow.value := by
    simp only [ProvenancedCell.markedRow,
      ProvenancedCell.previousMarkedRow, ProvenancedCell.componentRow,
      ProvenancedRow.value, MarkedRow.basisWord,
      LieRings.PBW.basisWord, LieRings.PBW.word,
      List.map_nil, List.prod_nil, mul_one]
    rw [hstep, map_add, mul_add]
  rw [hvalue, map_add]
  rfl

/-- The component side of the literal `(1,n)` terminal diagonal. -/
def GoverningWitness.terminalDiagonalComponentFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.provenancedCells n L data hn).sum (fun c z ↦ z •
    if hlen : c.left.length = 1 then
      if hactive : c.activeWeight n L data hn = n then
        c.factorEdge n L data hn 2 n (by omega)
      else 0
    else 0)

/-- The preceding-prefix contribution on exactly the same signed diagonal. -/
def GoverningWitness.terminalDiagonalPreviousPrefix
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.provenancedCells n L data hn).sum (fun c z ↦ z •
    if hlen : c.left.length = 1 then
      if hactive : c.activeWeight n L data hn = n then
        c.previousPrefixFactorTwo n L data hn
      else 0
    else 0)

/-- Every factor-two component read not lying on the literal `(1,n)`
diagonal.  Such a read can occur because PBW commutator corrections lower
factor number. -/
def GoverningWitness.terminalOffDiagonalComponentFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.provenancedCells n L data hn).sum (fun c z ↦ z •
    if hlen : c.left.length = 1 then
      if hactive : c.activeWeight n L data hn = n then 0
      else c.factorEdge n L data hn 2 n (by omega)
    else c.factorEdge n L data hn 2 n (by omega))

/-- Exact partition of the complete terminal defect into the literal
terminal diagonal and its complement. -/
theorem GoverningWitness.terminalFactorDefect_eq_diagonal_add_offDiagonal
    {a : L} (w : GoverningWitness n L data a) :
    w.terminalFactorDefect n L data hn =
      w.terminalDiagonalComponentFactor n L data hn +
        w.terminalOffDiagonalComponentFactor n L data hn := by
  classical
  rw [GoverningWitness.terminalFactorDefect,
    GoverningWitness.terminalDiagonalComponentFactor,
    GoverningWitness.terminalOffDiagonalComponentFactor,
    ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hlen : c.left.length = 1
  · rw [dif_pos hlen, dif_pos hlen]
    by_cases hactive : c.activeWeight n L data hn = n
    · rw [dif_pos hactive, dif_pos hactive]
      module
    · rw [dif_neg hactive, dif_neg hactive]
      module
  · rw [dif_neg hlen, dif_neg hlen]
    module

/-- Boundary of the literal terminal diagonal, with the exact
previous-prefix correction retained. -/
theorem GoverningWitness.dOne_contextualSymbolChain_terminal_eq
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (contextualSymbolChain n L data hn w 1 n (by omega) (by omega)) =
      w.terminalDiagonalPreviousPrefix n L data hn +
        w.terminalDiagonalComponentFactor n L data hn := by
  classical
  rw [dOne_contextualSymbolChain,
    GoverningWitness.terminalDiagonalPreviousPrefix,
    GoverningWitness.terminalDiagonalComponentFactor,
    ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hlen : c.left.length = 1
  · rw [dif_pos hlen, dif_pos hlen, dif_pos hlen]
    by_cases hactive : c.activeWeight n L data hn = n
    · rw [dif_pos hactive, dif_pos hactive, dif_pos hactive]
      simpa only [Nat.reduceAdd, zsmul_add] using congrArg
        (fun x ↦ w.provenancedCells n L data hn c • x)
        (c.markedFactorTwo_eq_previous_add_component n L data hn)
    · rw [dif_neg hactive, dif_neg hactive, dif_neg hactive]
      simp only [zsmul_zero, add_zero]
  · rw [dif_neg hlen, dif_neg hlen, dif_neg hlen]
    simp only [zsmul_zero, add_zero]

/-- The exact comparison with the complete terminal defect.  The naive
identity with only `dOne (contextualSymbolChain ... 1 n)` drops the negative
previous-prefix term and the off-diagonal PBW term. -/
theorem GoverningWitness.terminalFactorDefect_eq_dOne_terminalDiagonal_sub_previous_add_offDiagonal
    {a : L} (w : GoverningWitness n L data a) :
    w.terminalFactorDefect n L data hn =
      (show Sym[ℤ] (Fin 2) (A L n) from
        Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (contextualSymbolChain n L data hn w 1 n (by omega) (by omega))) -
        w.terminalDiagonalPreviousPrefix n L data hn +
        w.terminalOffDiagonalComponentFactor n L data hn := by
  rw [w.terminalFactorDefect_eq_diagonal_add_offDiagonal n L data hn,
    w.dOne_contextualSymbolChain_terminal_eq n L data hn]
  module

/-! ## The omitted aggregate is itself an honest Koszul boundary -/

/-- The chain formed by adjoining the complete terminal frontier to the
literal `(1,n)` diagonal.  Both summands carry genuine full relations in the
terminal source presentation. -/
def GoverningWitness.terminalDiagonalRemainderChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 := by
  have hk : 1 ≤ n := by omega
  have hkn : n < n + 1 := by omega
  exact contextualSymbolChain n L data hn w 1 n hk hkn +
    w.contextualTerminalChain n L data hn

/-- Exact aggregate cancellation left out by the naive terminal-diagonal
read.  The preceding-prefix term minus every off-diagonal factor-two
component is the boundary of an explicit chain of genuine relation rows.

This is the strongest statement supplied merely by the contextual collector:
it does not assert that the displayed remainder chain has zero primitive. -/
@[simp] theorem GoverningWitness.dOne_terminalDiagonalRemainderChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.terminalDiagonalRemainderChain n L data hn) =
      w.terminalDiagonalPreviousPrefix n L data hn -
        w.terminalOffDiagonalComponentFactor n L data hn := by
  have hk : 1 ≤ n := by omega
  have hkn : n < n + 1 := by omega
  change Koszul.dOne (terminalSourcePresentation n L data hn) 1
      (contextualSymbolChain n L data hn w 1 n hk hkn +
        w.contextualTerminalChain n L data hn) = _
  rw [map_add, w.dOne_contextualSymbolChain_terminal_eq n L data hn,
    w.dOne_contextualTerminalChain_eq_neg_defect n L data hn,
    w.terminalFactorDefect_eq_diagonal_add_offDiagonal n L data hn]
  abel

end

end LieRings.MetabelianVanishing
