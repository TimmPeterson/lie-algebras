import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalSupport
import LieRings.DimensionSubring.MetabelianVanishing.ContextualTerminalDiagonalAudit

/-!
# Exact raw contextual terminal aggregate

The literal `(1,n)` diagonal of the raw cutoff trace does not by itself read
the complete factor-two component frontier.  This file records the exact
aggregate correction.  Unlike the governing contextual trace, the raw trace
has a nonzero initial word.  Its factor-two symbol is canceled by the already
constructed complete factor-first chain; after adjoining that chain, the two
remaining terms are precisely the previous-prefix and off-diagonal reads.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawContextualTerminalAggregateFintype : Fintype L :=
  Fintype.ofFinite L

/-! ## Literal raw terminal diagonal -/

/-- The genuine terminal-source chain on the literal `(1,n)` diagonal of
the raw cutoff truncation-cell ledger. -/
def GoverningWitness.rawCutoffTerminalDiagonalChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
    z • c.one n L data hn 1 n (by omega) (by omega))

/-- Exposed component contribution on the literal raw `(1,n)` diagonal. -/
def GoverningWitness.rawCutoffTerminalDiagonalComponentFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦ z •
    if hlen : c.left.length = 1 then
      if hactive : c.activeWeight n L data hn = n then
        c.factorEdge n L data hn 2 n (by omega)
      else 0
    else 0)

/-- Prefix immediately preceding the exposed component on the same raw
diagonal. -/
def GoverningWitness.rawCutoffTerminalDiagonalPreviousPrefix
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦ z •
    if hlen : c.left.length = 1 then
      if hactive : c.activeWeight n L data hn = n then
        c.previousPrefixFactorTwo n L data hn
      else 0
    else 0)

/-- Every raw factor-two component read away from the literal `(1,n)`
diagonal. -/
def GoverningWitness.rawCutoffTerminalOffDiagonalComponentFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦ z •
    if hlen : c.left.length = 1 then
      if hactive : c.activeWeight n L data hn = n then 0
      else c.factorEdge n L data hn 2 n (by omega)
    else c.factorEdge n L data hn 2 n (by omega))

/-- Exact partition of the raw component frontier into its terminal diagonal
and complement. -/
theorem GoverningWitness.rawCutoffTerminalComponentFactor_eq_diagonal_add_offDiagonal
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffTerminalComponentFactor n L data hn =
      w.rawCutoffTerminalDiagonalComponentFactor n L data hn +
        w.rawCutoffTerminalOffDiagonalComponentFactor n L data hn := by
  classical
  rw [w.rawCutoffTerminalComponentFactor_eq_trace n L data hn,
    GoverningWitness.rawCutoffTerminalDiagonalComponentFactor,
    GoverningWitness.rawCutoffTerminalOffDiagonalComponentFactor,
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

/-- Boundary of the literal raw diagonal, retaining its preceding prefix. -/
theorem GoverningWitness.dOne_rawCutoffTerminalDiagonalChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffTerminalDiagonalChain n L data hn) =
      w.rawCutoffTerminalDiagonalPreviousPrefix n L data hn +
        w.rawCutoffTerminalDiagonalComponentFactor n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffTerminalDiagonalChain, map_finsuppSum,
    GoverningWitness.rawCutoffTerminalDiagonalPreviousPrefix,
    GoverningWitness.rawCutoffTerminalDiagonalComponentFactor,
    ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, c.dOne_one]
  by_cases hlen : c.left.length = 1
  · rw [dif_pos hlen, dif_pos hlen, dif_pos hlen]
    by_cases hactive : c.activeWeight n L data hn = n
    · rw [dif_pos hactive, dif_pos hactive, dif_pos hactive]
      simpa only [Nat.reduceAdd, zsmul_add] using congrArg
        (fun x ↦ w.rawCutoffFullProvenancedCells n L data hn c • x)
        (c.markedFactorTwo_eq_previous_add_component n L data hn)
    · rw [dif_neg hactive, dif_neg hactive, dif_neg hactive]
      change w.rawCutoffFullProvenancedCells n L data hn c •
          (0 : Sym[ℤ] (Fin 2)
            (terminalSourcePresentation n L data hn).gen) =
        w.rawCutoffFullProvenancedCells n L data hn c • 0 +
          w.rawCutoffFullProvenancedCells n L data hn c • 0
      rw [zsmul_zero, zero_add]
  · rw [dif_neg hlen, dif_neg hlen, dif_neg hlen]
    change w.rawCutoffFullProvenancedCells n L data hn c •
        (0 : Sym[ℤ] (Fin 2)
          (terminalSourcePresentation n L data hn).gen) =
      w.rawCutoffFullProvenancedCells n L data hn c • 0 +
        w.rawCutoffFullProvenancedCells n L data hn c • 0
    rw [zsmul_zero, zero_add]

/-! ## Cancellation of the nonzero raw initial edge -/

/-- The complete factor-first chain has boundary equal to the negative
factor-two symbol of the raw cutoff word. -/
theorem GoverningWitness.dOne_completeFactorTwoChain_eq_neg_rawCutoffSymbol
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.completeFactorTwoChain n L data hn) =
      -rightSymbol n L data hn 2 n (by omega)
        (w.rawCompleteCutoffWord n L data) := by
  calc
    _ = -w.completeFactorTwoCutoffFullLabel n L data hn := by
      rw [← w.completeNormalFormFullLabelRead_eq_dOne_completeFactorTwoChain
        n L data hn]
      exact w.completeNormalFullLabel_eq_neg_cutoff n L data hn
    _ = _ := by rw [w.rightSymbol_rawCompleteCutoffWord n L data hn]

/-- The complete raw aggregate which cancels the nonzero initial edge:
literal `(1,n)` diagonal, placed raw terminal wall, and the original complete
factor-first chain. -/
def GoverningWitness.rawCutoffTerminalRemainderChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  w.rawCutoffTerminalDiagonalChain n L data hn +
    w.rawCutoffContextualTerminalChain n L data hn +
    w.completeFactorTwoChain n L data hn

/-- Exact raw analogue of `dOne_terminalDiagonalRemainderChain`.  After the
complete factor-first boundary cancels the raw initial word, the aggregate
boundary is precisely the preceding-prefix read minus every off-diagonal
component read.  No component is promoted to a relation. -/
@[simp] theorem GoverningWitness.dOne_rawCutoffTerminalRemainderChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffTerminalRemainderChain n L data hn) =
      w.rawCutoffTerminalDiagonalPreviousPrefix n L data hn -
        w.rawCutoffTerminalOffDiagonalComponentFactor n L data hn := by
  rw [GoverningWitness.rawCutoffTerminalRemainderChain, map_add, map_add,
    w.dOne_rawCutoffTerminalDiagonalChain n L data hn,
    ← w.rawCutoffTerminalTwoFullLabel_eq_dOne n L data hn,
    w.dOne_completeFactorTwoChain_eq_neg_rawCutoffSymbol n L data hn,
    w.rightSymbol_rawCutoff_terminal_decomposition n L data hn,
    w.rawCutoffTerminalComponentFactor_eq_diagonal_add_offDiagonal
      n L data hn]
  abel

end

end LieRings.MetabelianVanishing
