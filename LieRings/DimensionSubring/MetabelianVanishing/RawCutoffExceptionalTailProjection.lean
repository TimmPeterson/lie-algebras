import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalSupport

/-!
# The exceptional full label and its weight-one component

At a mark-one hole cell, the difference between the stored full relation
and the exposed component starts in the derived tail.  If at least two
ordered spectators occur on the left, this difference is invisible both to
the terminal factor-two symbol and to the complete PBW primitive.  This is
the exact comparison needed before the exceptional occurrence ledger is
assembled; it does not assert that the homogeneous component is a relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalTailProjectionFintype : Fintype L :=
  Fintype.ofFinite L

/-- At a mark-one hole cell, the full root minus the exposed component lies
in the derived tail. -/
theorem ProvenancedCell.root_sub_component_mem_tail_one_of_markOne_hole
    (c : ProvenancedCell n L data hn)
    (hmark : c.mark.val = 1)
    (hcontext : c.context = .hole) :
    (c.root : FreeModel n L) -
        RelationContext.component n L data hn c.context c.root c.mark ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
  have htail := RelationContext.sub_rowTruncation_mem_tail
    n L (c.root : FreeModel n L) 1 (by omega)
  have hmarkEq : c.mark = ⟨1, by omega⟩ := Fin.ext hmark
  have hcomponent : RelationContext.component n L data hn
      c.context c.root c.mark =
        rowTruncation n L 1 (by omega) (c.root : FreeModel n L) := by
    rw [hcontext, hmarkEq]
    simp only [RelationContext.component, Fin.val_one,
      ↓reduceDIte, RelationContext.apply]
    have hstep := rowTruncation_succ n L 0 (by omega)
      (c.root : FreeModel n L)
    rw [rowTruncation_zero n L hn] at hstep
    simpa only [Nat.zero_add, zero_add] using hstep.symm
  rw [hcomponent]
  exact htail

/-- For an exceptional word with at least two ordered spectators, replacing
the full root on the right by its mark-one component does not change the
terminal factor-two symbol. -/
theorem ProvenancedCell.rightSymbol_fullLabelRightRow_eq_factorEdge_of_markOne_hole
    (c : ProvenancedCell n L data hn)
    (hmark : c.mark.val = 1)
    (hcontext : c.context = .hole)
    (hordered : c.left.Pairwise (· ≤ ·))
    (hlen : 2 ≤ c.left.length) :
    rightSymbol n L data hn 2 n (by omega)
        ((c.fullLabelRightRow n L data hn).value n L data hn) =
      c.factorEdge n L data hn 2 n (by omega) := by
  let tail : FreeModel n L :=
    (c.root : FreeModel n L) -
      RelationContext.component n L data hn c.context c.root c.mark
  have htail : tail ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
    exact c.root_sub_component_mem_tail_one_of_markOne_hole
      n L data hn hmark hcontext
  have hroot : (c.root : FreeModel n L) =
      RelationContext.component n L data hn c.context c.root c.mark + tail := by
    dsimp only [tail]
    abel
  have hzero : fullRightSymbol n L data hn 2
      (MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ tail) = 0 := by
    apply fullRightSymbol_basisWord_mul_iota_of_mem_tail_one_eq_zero
      n L data hn 2 tail c.left hordered htail
    omega
  have hfullWord : (c.fullLabelRightRow n L data hn).value n L data hn =
      MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ (c.root : FreeModel n L) := by
    rw [ProvenancedCell.fullLabelRightRow_value]
    simp [contextualFullRelationWord, hcontext, MarkedRow.basisWord,
      LieRings.PBW.basisWord, LieRings.PBW.word]
  have hcomponentWord : c.componentRow.value =
      MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.component n L data hn
            c.context c.root c.mark) := by
    simp [ProvenancedCell.componentRow, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word]
  rw [hfullWord, hroot, map_add, mul_add]
  unfold rightSymbol
  simp only [LinearMap.comp_apply]
  rw [map_add, hzero, add_zero]
  exact congrArg (SymmetricPower.map (R := ℤ) (prLE n L n (by omega)))
    (congrArg (fullRightSymbol n L data hn 2) hcomponentWord.symm)

/-- The same tail comparison for the complete one-factor PBW primitive. -/
theorem ProvenancedCell.pbwPrimitive_fullLabelRightRow_eq_primitive_of_markOne_hole
    (c : ProvenancedCell n L data hn)
    (hmark : c.mark.val = 1)
    (hcontext : c.context = .hole)
    (hordered : c.left.Pairwise (· ≤ ·))
    (hlen : 2 ≤ c.left.length) :
    pbwPrimitive n L data hn
        ((c.fullLabelRightRow n L data hn).value n L data hn) =
      c.primitive n L data hn := by
  let tail : FreeModel n L :=
    (c.root : FreeModel n L) -
      RelationContext.component n L data hn c.context c.root c.mark
  have htail : tail ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
    exact c.root_sub_component_mem_tail_one_of_markOne_hole
      n L data hn hmark hcontext
  have hroot : (c.root : FreeModel n L) =
      RelationContext.component n L data hn c.context c.root c.mark + tail := by
    dsimp only [tail]
    abel
  have hzero : fullRightSymbol n L data hn 1
      (MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ tail) = 0 := by
    apply fullRightSymbol_basisWord_mul_iota_of_mem_tail_one_eq_zero
      n L data hn 1 tail c.left hordered htail
    omega
  have hfullWord : (c.fullLabelRightRow n L data hn).value n L data hn =
      MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ (c.root : FreeModel n L) := by
    rw [ProvenancedCell.fullLabelRightRow_value]
    simp [contextualFullRelationWord, hcontext, MarkedRow.basisWord,
      LieRings.PBW.basisWord, LieRings.PBW.word]
  have hcomponentWord : c.componentRow.value =
      MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.component n L data hn
            c.context c.root c.mark) := by
    simp [ProvenancedCell.componentRow, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word]
  rw [hfullWord, hroot, map_add, mul_add]
  unfold pbwPrimitive
  simp only [LinearMap.comp_apply]
  rw [map_add, hzero, add_zero]
  exact congrArg (SymmetricPower.degreeOneLinearEquiv
    (adaptedBasis n L data hn))
      (congrArg (fullRightSymbol n L data hn 1) hcomponentWord.symm)

end

end LieRings.MetabelianVanishing
