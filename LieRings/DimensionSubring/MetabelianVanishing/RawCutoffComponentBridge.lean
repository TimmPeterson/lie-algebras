import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffProvenance

/-!
# PBW-normalized component frontier of the raw cutoff

The raw cutoff trace is already a signed family of contextual truncation
cells.  This file applies the existing provenance-preserving component PBW
collector to that family.  The resulting single frontier has two exact
reads: its factor-two read is the ordinary cutoff boundary, and its
factor-one read is the ordinary cutoff primitive.  Thus the two quantities
which must be lifted in the terminal correction are not independent sums.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffComponentBridgeFintype : Fintype L :=
  Fintype.ofFinite L

/-- Complete PBW normalization of every homogeneous component exposed by
the raw cutoff trace.  The root relation, context, and mark remain attached
to every state through `ComponentPBWState`. -/
def GoverningWitness.rawCutoffCompleteComponentPBWFrontier {a : L}
    (w : GoverningWitness n L data a) :
    ComponentPBWState n L data hn →₀ ℤ :=
  (w.rawCutoffProvenancedCells n L data hn).sum (fun c z ↦
    z • c.componentPBWFrontier n L data hn)

/-- Every actual factor-two state in the normalized ordinary cutoff ledger
has acquired a nonempty bracket context.  The source truncation cells all
have at least three factors, so the collector must use a factor-lowering
bracket correction before reaching factor two. -/
theorem GoverningWitness.rawCutoffCompleteComponentPBWFrontier_factorTwo_context_ne_hole
    {a : L} (w : GoverningWitness n L data a)
    (s : ComponentPBWState n L data hn)
    (hs : w.rawCutoffCompleteComponentPBWFrontier n L data hn s ≠ 0)
    (htwo : s.factorCount n L data hn = 2) :
    s.context ≠ .hole := by
  classical
  rw [GoverningWitness.rawCutoffCompleteComponentPBWFrontier,
    Finsupp.sum_apply] at hs
  have hcell : ∃ c ∈
      (w.rawCutoffProvenancedCells n L data hn).support,
      (w.rawCutoffProvenancedCells n L data hn c •
        c.componentPBWFrontier n L data hn) s ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hs (Finset.sum_eq_zero (fun c hc ↦ hall c hc))
  obtain ⟨c, hc, hcs⟩ := hcell
  have hfront : c.componentPBWFrontier n L data hn s ≠ 0 := by
    intro hzero
    simp [hzero] at hcs
  have hleft : 2 ≤ c.left.length := by
    have hcne : w.rawCutoffProvenancedCells n L data hn c ≠ 0 :=
      Finsupp.mem_support_iff.mp hc
    rw [GoverningWitness.rawCutoffProvenancedCells,
      Finsupp.sum_apply] at hcne
    have hsource : ∃ t ∈ (w.rawCutoffTraceCells n L data hn).support,
        (Finsupp.single (t.toProvenancedCell n L data hn)
          (w.rawCutoffTraceCells n L data hn t)) c ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hcne (Finset.sum_eq_zero (fun t ht ↦ hall t ht))
    obtain ⟨t, ht, htc⟩ := hsource
    have hct : c = t.toProvenancedCell n L data hn := by
      by_contra hne
      simp [Finsupp.single_apply, hne] at htc
    subst c
    change 2 ≤ t.left.length
    have hthree := t.factor_ge_three
    omega
  exact c.componentPBWFrontier_factorTwo_context_ne_hole
    n L data hn hleft s hfront htwo

/-- Evaluation of the normalized frontier is the literal aggregate of the
component words in the raw cutoff trace. -/
theorem GoverningWitness.evaluate_rawCutoffCompleteComponentPBWFrontier
    {a : L} (w : GoverningWitness n L data a) :
    (componentPBWCollector n L data hn).evaluate
        (w.rawCutoffCompleteComponentPBWFrontier n L data hn) =
      (w.rawCutoffProvenancedCells n L data hn).sum
        (fun c z ↦ z • c.componentRow.value) := by
  classical
  rw [GoverningWitness.rawCutoffCompleteComponentPBWFrontier,
    map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, c.evaluate_componentPBWFrontier]

/-- Exact factor-two read of the common normalized frontier. -/
def GoverningWitness.rawCutoffCompleteComponentPBWFactorTwo {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffCompleteComponentPBWFrontier n L data hn).sum (fun s z ↦
    z • rightSymbol n L data hn 2 n (by omega) (s.value n L data hn))

/-- The factor-two read is exactly the ordinary cutoff boundary. -/
theorem GoverningWitness.rawCutoffCompleteComponentPBWFactorTwo_eq
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffCompleteComponentPBWFactorTwo n L data hn =
      w.rawCutoffOrdinaryFactorTwo n L data hn := by
  have h := congrArg (rightSymbol n L data hn 2 n (by omega))
    (w.evaluate_rawCutoffCompleteComponentPBWFrontier n L data hn)
  change rightSymbol n L data hn 2 n (by omega)
      ((w.rawCutoffCompleteComponentPBWFrontier n L data hn).sum
        (fun s z ↦ z • s.value n L data hn)) =
    rightSymbol n L data hn 2 n (by omega)
      ((w.rawCutoffProvenancedCells n L data hn).sum
        (fun c z ↦ z • c.componentRow.value)) at h
  rw [map_finsuppSum, map_finsuppSum] at h
  rw [w.rawCutoffOrdinaryFactorTwo_eq_provenancedCells n L data hn]
  simpa only [map_zsmul,
    GoverningWitness.rawCutoffCompleteComponentPBWFactorTwo,
    ProvenancedCell.factorEdge] using h

/-- Exact factor-one read of the common normalized frontier. -/
def GoverningWitness.rawCutoffCompleteComponentPBWPrimitive {a : L}
    (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffCompleteComponentPBWFrontier n L data hn).sum (fun s z ↦
    z • pbwPrimitive n L data hn (s.value n L data hn))

/-- The factor-one read is exactly the ordinary cutoff primitive. -/
theorem GoverningWitness.rawCutoffCompleteComponentPBWPrimitive_eq
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffCompleteComponentPBWPrimitive n L data hn =
      w.rawCutoffOrdinaryPrimitive n L data hn := by
  have h := congrArg (pbwPrimitive n L data hn)
    (w.evaluate_rawCutoffCompleteComponentPBWFrontier n L data hn)
  change pbwPrimitive n L data hn
      ((w.rawCutoffCompleteComponentPBWFrontier n L data hn).sum
        (fun s z ↦ z • s.value n L data hn)) =
    pbwPrimitive n L data hn
      ((w.rawCutoffProvenancedCells n L data hn).sum
        (fun c z ↦ z • c.componentRow.value)) at h
  rw [map_finsuppSum, map_finsuppSum] at h
  rw [w.rawCutoffOrdinaryPrimitive_eq_provenancedCells n L data hn]
  simpa only [map_zsmul,
    GoverningWitness.rawCutoffCompleteComponentPBWPrimitive,
    ProvenancedCell.primitive] using h

end

end LieRings.MetabelianVanishing
