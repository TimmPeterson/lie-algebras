import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalSubsetChain

/-!
# Full-relation trace below the exceptional relation-left word

The proper-subset identity leaves one word with the genuine relation on the
left.  This file feeds that word back into the already verified provenance
collector.  The construction is independent of the canonical exceptional
boundary remainder: its input is the literal full relation and its terminal
degree-one rows are the genuine contextual full-relation rows of the
collector.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalFullRelationTraceFintype : Fintype L :=
  Fintype.ofFinite L

/-- Terminal provenance frontier obtained by collecting the literal word
`iota(root) * basisWord(left)` attached to one exceptional occurrence. -/
def ProvenancedCell.exceptionalRelationLeftFrontier
    (c : ProvenancedCell n L data hn) :
    ProvenancedRow n L data hn →₀ ℤ :=
  (provenancedRowsOfRightFactor n L data hn c.root
      (MarkedRow.basisWord n L data hn c.left)).sum fun r z ↦
    z • (provenancedCollector n L data hn).normalForm r

/-- Component full-label read left in the terminal frontier. -/
def ProvenancedCell.exceptionalRelationLeftComponentRead
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  (c.exceptionalRelationLeftFrontier n L data hn).sum fun r z ↦
    z • provenancedComponentFullLabelSeed n L data hn r

/-- Placed terminal factor-two rows in the same frontier. -/
def ProvenancedCell.exceptionalRelationLeftTerminalTwo
    (c : ProvenancedCell n L data hn) :
    ProvenancedTerminalTwo n L data hn →₀ ℤ :=
  (c.exceptionalRelationLeftFrontier n L data hn).sum fun r z ↦
    z • provenancedTerminalTwoPart n L data hn r

/-- Genuine terminal-source chain carried by those placed full-relation
rows. -/
def ProvenancedCell.exceptionalRelationLeftTraceChain
    (c : ProvenancedCell n L data hn) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (c.exceptionalRelationLeftTerminalTwo n L data hn).sum fun t z ↦
    z • t.chain n L data hn

private theorem ProvenancedCell.exceptionalRelationLeftFrontier_terminal
    (c : ProvenancedCell n L data hn)
    (r : ProvenancedRow n L data hn)
    (hr : c.exceptionalRelationLeftFrontier n L data hn r ≠ 0) :
    provenancedExpansion n L data hn r = none := by
  classical
  by_contra hnonterminal
  apply hr
  rw [ProvenancedCell.exceptionalRelationLeftFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro s hs
  change (provenancedRowsOfRightFactor n L data hn c.root
      (MarkedRow.basisWord n L data hn c.left)) s *
        (provenancedCollector n L data hn).normalForm s r = 0
  rw [(provenancedCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
    s r hnonterminal, mul_zero]

/-- The full-label read of the collected frontier is the exact factor-two
symbol of the literal relation-left input word. -/
theorem ProvenancedCell.exceptionalRelationLeftFrontier_fullLabelRead
    (c : ProvenancedCell n L data hn) :
    (c.exceptionalRelationLeftFrontier n L data hn).sum (fun r z ↦
        z • provenancedFullLabelRead n L data hn r) =
      rightSymbol n L data hn 2 n (by omega)
        (UniversalEnvelopingAlgebra.ι ℤ (c.root : FreeModel n L) *
          MarkedRow.basisWord n L data hn c.left) := by
  classical
  have heval :
      (provenancedFullLabelCollector n L data hn).evaluate
          (c.exceptionalRelationLeftFrontier n L data hn) =
        UniversalEnvelopingAlgebra.ι ℤ (c.root : FreeModel n L) *
          MarkedRow.basisWord n L data hn c.left := by
    rw [ProvenancedCell.exceptionalRelationLeftFrontier, map_finsuppSum]
    calc
      _ = (provenancedFullLabelCollector n L data hn).evaluate
          (provenancedRowsOfRightFactor n L data hn c.root
            (MarkedRow.basisWord n L data hn c.left)) := by
        change (provenancedRowsOfRightFactor n L data hn c.root
              (MarkedRow.basisWord n L data hn c.left)).sum
            (fun r z ↦
              (provenancedFullLabelCollector n L data hn).evaluate
                (z • (provenancedCollector n L data hn).normalForm r)) =
          (provenancedRowsOfRightFactor n L data hn c.root
              (MarkedRow.basisWord n L data hn c.left)).sum
            (fun r z ↦ z • provenancedFullLabelWord n L data hn r)
        apply Finsupp.sum_congr
        intro r hr
        rw [map_zsmul, provenancedFullLabelCollector_evaluate]
      _ = _ := evaluateFullLabel_provenancedRowsOfRightFactor
        n L data hn c.root (MarkedRow.basisWord n L data hn c.left)
  have h := congrArg (rightSymbol n L data hn 2 n (by omega)) heval
  change rightSymbol n L data hn 2 n (by omega)
      ((c.exceptionalRelationLeftFrontier n L data hn).sum
        (fun r z ↦ z • provenancedFullLabelWord n L data hn r)) = _ at h
  rw [map_finsuppSum] at h
  simpa only [map_zsmul, provenancedFullLabelRead] using h

/-- Terminal decomposition of the independently collected relation-left
word. -/
theorem ProvenancedCell.exceptionalRelationLeft_terminal_decomposition
    (c : ProvenancedCell n L data hn) :
    rightSymbol n L data hn 2 n (by omega)
        (UniversalEnvelopingAlgebra.ι ℤ (c.root : FreeModel n L) *
          MarkedRow.basisWord n L data hn c.left) =
      c.exceptionalRelationLeftComponentRead n L data hn +
        (c.exceptionalRelationLeftFrontier n L data hn).sum (fun r z ↦
          z • terminalTwoFullLabelSeed n L data hn r) := by
  classical
  rw [← c.exceptionalRelationLeftFrontier_fullLabelRead n L data hn,
    ProvenancedCell.exceptionalRelationLeftComponentRead]
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hterminal := c.exceptionalRelationLeftFrontier_terminal
    n L data hn r (Finsupp.mem_support_iff.mp hr)
  change (c.exceptionalRelationLeftFrontier n L data hn r) •
      provenancedFullLabelRead n L data hn r =
    (c.exceptionalRelationLeftFrontier n L data hn r) •
        provenancedComponentFullLabelSeed n L data hn r +
      (c.exceptionalRelationLeftFrontier n L data hn r) •
        terminalTwoFullLabelSeed n L data hn r
  rw [fullLabelRead_terminal_decomposition n L data hn r hterminal,
    zsmul_add]

/-- Exact Stokes boundary of the independent full-relation trace.  The only
unrealized edge is displayed explicitly as the terminal component read. -/
theorem ProvenancedCell.dOne_exceptionalRelationLeftTraceChain
    (c : ProvenancedCell n L data hn)
    (hc : c.IsHoleExceptional n L data hn) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (c.exceptionalRelationLeftTraceChain n L data hn) =
      c.holeExceptionalRelationLeftFactor n L data hn -
        c.exceptionalRelationLeftComponentRead n L data hn := by
  classical
  rw [ProvenancedCell.exceptionalRelationLeftTraceChain, map_finsuppSum,
    ProvenancedCell.exceptionalRelationLeftTerminalTwo]
  simp_rw [map_zsmul, ProvenancedTerminalTwo.dOne_chain]
  rw [Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  have hsmul (z : ℤ) (f : ProvenancedTerminalTwo n L data hn →₀ ℤ) :
      (z • f).sum (fun t a ↦ a •
          rightSymbol n L data hn 2 n (by omega) t.row.value) =
        z • f.sum (fun t a ↦ a •
          rightSymbol n L data hn 2 n (by omega) t.row.value) := by
    change Finsupp.linearCombination ℤ
        (fun t ↦ rightSymbol n L data hn 2 n (by omega) t.row.value)
          (z • f) =
      z • Finsupp.linearCombination ℤ
        (fun t ↦ rightSymbol n L data hn 2 n (by omega) t.row.value) f
    rw [map_zsmul]
  have hterminalTwo :
      (c.exceptionalRelationLeftFrontier n L data hn).sum (fun r z ↦
          z • (provenancedTerminalTwoPart n L data hn r).sum
            (fun t a ↦ a • rightSymbol n L data hn 2 n (by omega)
              t.row.value)) =
        (c.exceptionalRelationLeftFrontier n L data hn).sum (fun r z ↦
          z • terminalTwoFullLabelSeed n L data hn r) := by
    apply Finsupp.sum_congr
    intro r hr
    congr 1
    cases hc : provenancedTerminal? n L data hn r with
    | none => simp [provenancedTerminalTwoPart, terminalTwoFullLabelSeed, hc]
    | some t =>
        cases t with
        | inl t =>
            simp [provenancedTerminalTwoPart, terminalTwoFullLabelSeed, hc]
        | inr t =>
            simp [provenancedTerminalTwoPart, terminalTwoFullLabelSeed, hc]
  calc
    _ = (c.exceptionalRelationLeftFrontier n L data hn).sum (fun r z ↦
        z • (provenancedTerminalTwoPart n L data hn r).sum
          (fun t a ↦ a • rightSymbol n L data hn 2 n (by omega)
            t.row.value)) := by
      apply Finsupp.sum_congr
      intro r hr
      exact hsmul (c.exceptionalRelationLeftFrontier n L data hn r)
        (provenancedTerminalTwoPart n L data hn r)
    _ = (c.exceptionalRelationLeftFrontier n L data hn).sum (fun r z ↦
        z • terminalTwoFullLabelSeed n L data hn r) := hterminalTwo
    _ = c.holeExceptionalRelationLeftFactor n L data hn -
        c.exceptionalRelationLeftComponentRead n L data hn := by
      rw [ProvenancedCell.holeExceptionalRelationLeftFactor, if_pos hc]
      rw [c.exceptionalRelationLeft_terminal_decomposition n L data hn]
      abel

end

end LieRings.MetabelianVanishing
