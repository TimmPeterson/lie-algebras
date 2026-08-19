import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalComb

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

example {a : L} (w : GoverningWitness n L data a)
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
