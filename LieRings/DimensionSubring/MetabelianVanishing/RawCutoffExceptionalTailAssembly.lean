import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalTailProjection
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalAssembly

/-!
# Aggregate exceptional tail projection

The exceptional whole-relation ledger has the same factor-two and primitive
reads as its exposed component ledger.  This file packages that cellwise
comparison at the exact signed aggregate consumed by the final assembly.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalTailAssemblyFintype : Fintype L :=
  Fintype.ofFinite L

local instance rawCutoffExceptionalTailAssemblyPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

def ProvenancedCell.holeExceptionalComponentFactor
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  if c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 then
    c.factorEdge n L data hn 2 n (by omega)
  else 0

def ProvenancedCell.holeExceptionalComponentPrimitive
    (c : ProvenancedCell n L data hn) : FreeModel n L :=
  if c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 then
    c.primitive n L data hn
  else 0

/-- The cellwise tail comparison, summed with the actual signed occurrence
coefficients of the raw cutoff. -/
theorem GoverningWitness.rawCutoffHoleExceptionalFullLabelFactor_eq_component
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffHoleExceptionalFullLabelFactor n L data hn =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
        z • c.holeExceptionalComponentFactor n L data hn) := by
  classical
  rw [GoverningWitness.rawCutoffHoleExceptionalFullLabelFactor]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hexceptional : c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1
  · have hshape := w.rawCutoffHoleExceptional_left_cases
      n L data hn c (Finsupp.mem_support_iff.mp hc) hexceptional
    have hcomparison :=
      c.rightSymbol_fullLabelRightRow_eq_factorEdge_of_markOne_hole
        n L data hn hexceptional.1 hexceptional.2.1 hshape.1 hshape.2.1
    simp only [ProvenancedCell.fullLabelRightRow_value] at hcomparison
    rw [ProvenancedCell.holeExceptionalFullLabelFactor,
      if_pos hexceptional, ProvenancedCell.holeExceptionalComponentFactor,
      if_pos hexceptional]
    simpa only [hexceptional.2.1] using
      congrArg (fun x ↦
        (w.rawCutoffFullProvenancedCells n L data hn c) • x) hcomparison
  · rw [ProvenancedCell.holeExceptionalFullLabelFactor,
      if_neg hexceptional, ProvenancedCell.holeExceptionalComponentFactor,
      if_neg hexceptional]

/-- The identical aggregate comparison for the complete one-factor PBW
primitive. -/
theorem GoverningWitness.rawCutoffHoleExceptionalFullLabelPrimitive_eq_component
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffHoleExceptionalFullLabelPrimitive n L data hn =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
        z • c.holeExceptionalComponentPrimitive n L data hn) := by
  classical
  rw [GoverningWitness.rawCutoffHoleExceptionalFullLabelPrimitive]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hexceptional : c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1
  · have hshape := w.rawCutoffHoleExceptional_left_cases
      n L data hn c (Finsupp.mem_support_iff.mp hc) hexceptional
    have hcomparison :=
      c.pbwPrimitive_fullLabelRightRow_eq_primitive_of_markOne_hole
        n L data hn hexceptional.1 hexceptional.2.1 hshape.1 hshape.2.1
    simp only [ProvenancedCell.fullLabelRightRow_value] at hcomparison
    rw [ProvenancedCell.holeExceptionalFullLabelPrimitive,
      if_pos hexceptional, ProvenancedCell.holeExceptionalComponentPrimitive,
      if_pos hexceptional]
    simpa only [hexceptional.2.1] using
      congrArg (fun x ↦
        (w.rawCutoffFullProvenancedCells n L data hn c) • x) hcomparison
  · rw [ProvenancedCell.holeExceptionalFullLabelPrimitive,
      if_neg hexceptional, ProvenancedCell.holeExceptionalComponentPrimitive,
      if_neg hexceptional]

/-- Minimal remaining exceptional-cycle interface.  After the tail
projection, the sought chain only has to realize the genuine exposed
component reads; the existing raw-cutoff assembly supplies every other
family and all final PBW identities. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalComponentChain
    {a : L} (w : GoverningWitness n L data a)
    (exceptionalChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (exceptionalRelation : Relations n L data)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 exceptionalChain =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
        z • c.holeExceptionalComponentFactor n L data hn))
    (hprimitive : terminalSourcePrimitive n L data hn exceptionalChain =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
          z • c.holeExceptionalComponentPrimitive n L data hn) +
        (exceptionalRelation : FreeModel n L)) :
    a = 0 := by
  apply w.eq_zero_of_rawCutoffExceptionalChain n L data hn
    exceptionalChain exceptionalRelation
  · rw [hboundary]
    exact (w.rawCutoffHoleExceptionalFullLabelFactor_eq_component
      n L data hn).symm
  · rw [hprimitive]
    exact congrArg (fun x : FreeModel n L ↦
      x + (exceptionalRelation : FreeModel n L))
        (w.rawCutoffHoleExceptionalFullLabelPrimitive_eq_component
          n L data hn).symm

end

end LieRings.MetabelianVanishing
