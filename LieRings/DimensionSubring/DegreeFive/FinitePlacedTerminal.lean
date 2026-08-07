import LieRings.DimensionSubring.DegreeFive.FinitePlacedResolution

/-!
# Terminal placed packets

The finite collector stops below weight five precisely when the virtual PBW word obtained by
replacing the relation mark by its Smith head is ordered.  This file records that consequence
in a form usable by the PBW extraction.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X
local notation "Factor" => LowHomogeneousBasisIndex X

/-- A terminal row packet below weight five has no inversion in either external word. -/
theorem finitePlacedPacket_terminal_external_order
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : finitePlacedPacketExpansion X L evaluation p = none) :
    p.left.Pairwise (· ≤ ·) ∧ p.right.Pairwise (· ≤ ·) := by
  unfold finitePlacedPacketExpansion at hterminal
  split at hterminal
  · rename_i hlow'
    split at hterminal
    · rename_i r hr hhigh
      have hbad : (FiniteCollectedRelation.row i :
          FiniteCollectedRelation X L evaluation) = .high r hr :=
        hrel.symm.trans hhigh
      cases hbad
    · rename_i j hrow
      have hji : j = i := FiniteCollectedRelation.row.inj
        (hrow.symm.trans hrel)
      subst j
      split at hterminal
      · rename_i d hleftSome
        split at hterminal
        · contradiction
        · rename_i hnweight
          have hreal := chooseAdjacentInversion?_eq_some_realizes hleftSome
          exact (hnweight (adjacent_external_weight_le_four
            X L evaluation p d hreal hlow)).elim
      · rename_i hleftNone
        have hleftOrdered :=
          (chooseAdjacentInversion?_eq_none_iff_pairwise p.left).mp hleftNone
        split at hterminal
        · rename_i front x hlast
          split at hterminal
          · contradiction
          · split at hterminal
            · rename_i hrightNil
              exact ⟨hleftOrdered, by rw [hrightNil]; simp⟩
            · rename_i y tail hrightShape
              split at hterminal
              · contradiction
              · split at hterminal
                · rename_i d hrightSome
                  split at hterminal
                  · contradiction
                  · rename_i hnweight
                    have hreal := chooseAdjacentInversion?_eq_some_realizes
                      hrightSome
                    exact (hnweight (adjacent_external_weight_le_four_right
                      X L evaluation p d hreal hlow)).elim
                · rename_i hrightNone
                  exact ⟨hleftOrdered,
                    (chooseAdjacentInversion?_eq_none_iff_pairwise p.right).mp
                      hrightNone⟩
        · rename_i hlastNone
          split at hterminal
          · rename_i hrightNil
            exact ⟨hleftOrdered, by rw [hrightNil]; simp⟩
          · rename_i y tail hrightShape
            split at hterminal
            · contradiction
            · split at hterminal
              · rename_i d hrightSome
                split at hterminal
                · contradiction
                · rename_i hnweight
                  have hreal := chooseAdjacentInversion?_eq_some_realizes
                    hrightSome
                  exact (hnweight (adjacent_external_weight_le_four_right
                    X L evaluation p d hreal hlow)).elim
              · rename_i hrightNone
                exact ⟨hleftOrdered,
                  (chooseAdjacentInversion?_eq_none_iff_pairwise p.right).mp
                    hrightNone⟩
  · rename_i hnlow
    exact (hnlow hlow).elim

/-- At a terminal row mark, the final factor on the left does not exceed the Smith head. -/
theorem finitePlacedPacket_terminal_last_le_head
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : finitePlacedPacketExpansion X L evaluation p = none)
    (front : List Factor) (x : Factor)
    (hlast : splitLast? p.left = some (front, x)) :
    x ≤ lowRelationSmithHead X L evaluation i := by
  apply not_lt.mp
  intro hx
  unfold finitePlacedPacketExpansion at hterminal
  split at hterminal
  · split at hterminal
    · rename_i r hr hhigh
      have hbad : (FiniteCollectedRelation.row i :
          FiniteCollectedRelation X L evaluation) = .high r hr :=
        hrel.symm.trans hhigh
      cases hbad
    · rename_i j hrow
      have hji : j = i := FiniteCollectedRelation.row.inj
        (hrow.symm.trans hrel)
      subst j
      split at hterminal
      · rename_i d hleftSome
        split at hterminal
        · contradiction
        · rename_i hnweight
          have hreal := chooseAdjacentInversion?_eq_some_realizes hleftSome
          exact (hnweight (adjacent_external_weight_le_four
            X L evaluation p d hreal hlow)).elim
      · rename_i hleftNone
        split at hterminal
        · rename_i front' x' hlast'
          have hp : (front', x') = (front, x) := Option.some.inj
            (hlast'.symm.trans hlast)
          cases hp
          split at hterminal
          · contradiction
          · contradiction
        · rename_i hlastNone
          rw [hlastNone] at hlast
          contradiction
  · rename_i hnlow
    exact (hnlow hlow).elim

/-- At a terminal row mark, the Smith head does not exceed the first factor on the right. -/
theorem finitePlacedPacket_terminal_head_le_first
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : finitePlacedPacketExpansion X L evaluation p = none)
    (y : Factor) (tail : List Factor)
    (hright : p.right = y :: tail) :
    lowRelationSmithHead X L evaluation i ≤ y := by
  apply not_lt.mp
  intro hy
  unfold finitePlacedPacketExpansion at hterminal
  split at hterminal
  · split at hterminal
    · rename_i r hr hhigh
      have hbad : (FiniteCollectedRelation.row i :
          FiniteCollectedRelation X L evaluation) = .high r hr :=
        hrel.symm.trans hhigh
      cases hbad
    · rename_i j hrow
      have hji : j = i := FiniteCollectedRelation.row.inj
        (hrow.symm.trans hrel)
      subst j
      split at hterminal
      · rename_i d hleftSome
        split at hterminal
        · contradiction
        · rename_i hnweight
          have hreal := chooseAdjacentInversion?_eq_some_realizes hleftSome
          exact (hnweight (adjacent_external_weight_le_four
            X L evaluation p d hreal hlow)).elim
      · rename_i hleftNone
        split at hterminal
        · rename_i front x hlast
          split at hterminal
          · contradiction
          · split at hterminal
            · rename_i hrightNil
              rw [hright] at hrightNil
              contradiction
            · rename_i y' tail' hright'
              have hp : y' :: tail' = y :: tail := hright'.symm.trans hright
              cases List.cons.inj hp with
              | intro hy' htail' =>
                  subst y'
                  subst tail'
                  split at hterminal
                  · contradiction
                  · contradiction
        · rename_i hlastNone
          split at hterminal
          · rename_i hrightNil
            rw [hright] at hrightNil
            contradiction
          · rename_i y' tail' hright'
            have hp : y' :: tail' = y :: tail := hright'.symm.trans hright
            cases List.cons.inj hp with
            | intro hy' htail' =>
                subst y'
                subst tail'
                split at hterminal
                · contradiction
                · contradiction
  · rename_i hnlow
    exact (hnlow hlow).elim

/-- The complete virtual word of a terminal low row packet is in PBW order. -/
theorem finitePlacedPacket_terminal_virtualFactors_pairwise
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : finitePlacedPacketExpansion X L evaluation p = none) :
    (p.virtualFactors X L evaluation).Pairwise (· ≤ ·) := by
  have horders := finitePlacedPacket_terminal_external_order
    X L evaluation p i hrel hlow hterminal
  let head := lowRelationSmithHead X L evaluation i
  have hleftHead : ∀ x ∈ p.left, x ≤ head := by
    intro x hx
    have hne : p.left ≠ [] := List.ne_nil_of_mem hx
    have hsplit : splitLast? p.left =
        some (p.left.dropLast, p.left.getLast hne) := by
      unfold splitLast?
      rw [List.getLast?_eq_getLast_of_ne_nil hne]
      rfl
    exact (horders.1.rel_getLast hx).trans
      (finitePlacedPacket_terminal_last_le_head X L evaluation p i hrel
        hlow hterminal p.left.dropLast (p.left.getLast hne) hsplit)
  have hheadRight : ∀ y ∈ p.right, head ≤ y := by
    intro y hy
    cases hright : p.right with
    | nil => simp [hright] at hy
    | cons first tail =>
        have hfirst := finitePlacedPacket_terminal_head_le_first
          X L evaluation p i hrel hlow hterminal first tail hright
        have hpair : (first :: tail).Pairwise (· ≤ ·) := by
          simpa [hright] using horders.2
        rw [hright] at hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · simpa [head, hy] using hfirst
        · exact (show head ≤ first by simpa [head] using hfirst).trans
            ((List.pairwise_cons.mp hpair).1 y hy)
  rw [FiniteSmithPlacedPacket.virtualFactors, hrel]
  apply List.pairwise_append.mpr
  refine ⟨horders.1, ?_, ?_⟩
  · rw [List.pairwise_cons]
    exact ⟨hheadRight, horders.2⟩
  · intro x hx y hy
    have hxhead := hleftHead x hx
    simp only [List.mem_cons] at hy
    rcases hy with hy | hy
    · simpa [hy]
    · exact hxhead.trans (hheadRight y hy)

end

end DegreeFive

end LieRings
