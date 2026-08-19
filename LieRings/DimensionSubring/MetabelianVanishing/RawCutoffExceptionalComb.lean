import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalSupport
import LieRings.DimensionSubring.MetabelianVanishing.ExceptionalTriangularComb

/-!
# The surviving exceptional top comb

This file joins the two independent facts needed at the last primitive wall:
an exceptional raw cell retains a weight-one triangular Smith root, and a
one-factor descendant in the top homogeneous piece has absorbed all ordinary
factors into a context of weight `n`.  At that weight the exposed homogeneous
component is the whole contextual relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalCombFintype : Fintype L :=
  Fintype.ofFinite L

/-- Exact shape of a top-weight one-factor descendant of an exceptional
mark-one cell.  No assumption on the weights or the length of the spectator
word is needed: the top coordinate and the collector's distinguished-weight
invariant force the final context weight to be `n`.

The last equality is the manuscript's full-relation replacement.  It is an
equality in the free metabelian Lie ring, before evaluation in `L`. -/
theorem GoverningWitness.rawCutoffHoleExceptional_factorOne_top_shape
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0)
    (hexceptional : c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1)
    (q : ComponentPBWState n L data hn)
    (hq : c.componentPBWFrontier n L data hn q ≠ 0)
    (hone : q.factorCount n L data hn = 1)
    (htop : q.distinguished.1.val = n) :
    ∃ tag : TriangularRelationIndex n L,
      tag.1.val = 0 ∧
        q.root = triangularRelationOfIndex n L data tag ∧
        q.mark.val = 1 ∧ q.left = [] ∧ q.right = [] ∧
        RelationContext.weight n L data hn q.context = n ∧
        RelationContext.relation n L data hn q.context q.root =
          RelationContext.component n L data hn q.context q.root q.mark := by
  obtain ⟨tag, htag, hcroot⟩ :=
    w.rawCutoffHoleExceptional_root n L data hn c hc hexceptional
  have hprov := c.componentPBWFrontier_provenance_weight
    n L data hn q hq
  have hdist := c.componentPBWFrontier_distinguished_weight
    n L data hn q hq
  have hleftLength : q.left.length = 0 := by
    simp only [ComponentPBWState.factorCount] at hone
    omega
  have hrightLength : q.right.length = 0 := by
    simp only [ComponentPBWState.factorCount] at hone
    omega
  have hleft : q.left = [] := List.length_eq_zero_iff.mp hleftLength
  have hright : q.right = [] := List.length_eq_zero_iff.mp hrightLength
  have hroot : q.root = triangularRelationOfIndex n L data tag :=
    hprov.1.trans hcroot
  have hmarkVal : q.mark.val = 1 := by
    rw [hprov.2.1, hexceptional.1]
  have hcontextWeight :
      RelationContext.weight n L data hn q.context = n := by
    change q.distinguished.1.val + 1 =
      q.mark.val + RelationContext.weight n L data hn q.context at hdist
    omega
  have hmark : q.mark = ⟨1, by omega⟩ := Fin.ext hmarkVal
  have hfull := RelationContext.apply_triangularRelationOfIndex_eq_component_one
    n L data hn tag htag q.context hcontextWeight
  refine ⟨tag, htag, hroot, hmarkVal, hleft, hright, hcontextWeight, ?_⟩
  rw [RelationContext.relation, hroot, hmark]
  exact hfull

/-- Exact shape of a factor-two descendant at the terminal top-factor wall.
The distinguished factor has zero-based weight `n - 1`, hence the stored
context has manuscript weight `n - 1`.  At precisely this weight the
terminal prefix of the contextual triangular relation sees only its Smith
head.  Unlike the factor-one statement above, the equality is therefore
correctly stated after `prLE n`; the possibly nonzero weight-`n` tail is not
discarded in the full free model. -/
theorem GoverningWitness.rawCutoffHoleExceptional_factorTwo_top_shape
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0)
    (hexceptional : c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1)
    (q : ComponentPBWState n L data hn)
    (hq : c.componentPBWFrontier n L data hn q ≠ 0)
    (_htwo : q.factorCount n L data hn = 2)
    (htop : q.distinguished.1.val = n - 1) :
    ∃ tag : TriangularRelationIndex n L,
      tag.1.val = 0 ∧
        q.root = triangularRelationOfIndex n L data tag ∧
        q.mark.val = 1 ∧
        RelationContext.weight n L data hn q.context = n - 1 ∧
        prLE n L n (by omega)
            (RelationContext.relation n L data hn q.context q.root :
              FreeModel n L) =
          prLE n L n (by omega)
            (RelationContext.apply n L data hn q.context
              (FreeMetabelian.Free.weightIncl tag.1.val tag.1.isLt
                (((triangularSmith n L data tag.1.val tag.1.isLt).diagonal
                    tag.2 : ℤ) •
                  triangularPieceBasis n L data
                    tag.1.val tag.1.isLt tag.2))) := by
  obtain ⟨tag, htag, hcroot⟩ :=
    w.rawCutoffHoleExceptional_root n L data hn c hc hexceptional
  have hprov := c.componentPBWFrontier_provenance_weight
    n L data hn q hq
  have hdist := c.componentPBWFrontier_distinguished_weight
    n L data hn q hq
  have hroot : q.root = triangularRelationOfIndex n L data tag :=
    hprov.1.trans hcroot
  have hmarkVal : q.mark.val = 1 := by
    rw [hprov.2.1, hexceptional.1]
  have hcontextWeight :
      RelationContext.weight n L data hn q.context = n - 1 := by
    change q.distinguished.1.val + 1 =
      q.mark.val + RelationContext.weight n L data hn q.context at hdist
    omega
  refine ⟨tag, htag, hroot, hmarkVal, hcontextWeight, ?_⟩
  rw [RelationContext.relation, hroot]
  exact RelationContext.prLE_apply_triangularRelationOfIndex_eq_apply_head
    n L data hn tag htag q.context hcontextWeight

end

end LieRings.MetabelianVanishing
