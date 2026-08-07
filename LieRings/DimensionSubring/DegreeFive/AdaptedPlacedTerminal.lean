import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedInput

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
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X
local notation "Factor" => AdaptedLowBasisIndex X

/-- A terminal row packet below weight five has no inversion in either external word. -/
theorem adaptedPlacedPacket_terminal_external_order
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : adaptedPlacedPacketExpansion X L evaluation p = none) :
    p.left.Pairwise (· ≤ ·) ∧ p.right.Pairwise (· ≤ ·) := by
  unfold adaptedPlacedPacketExpansion at hterminal
  split at hterminal
  · rename_i hlow'
    split at hterminal
    · rename_i r hr hhigh
      have hbad : (AdaptedCollectedRelation.row i :
          AdaptedCollectedRelation X L evaluation) = .high r hr :=
        hrel.symm.trans hhigh
      cases hbad
    · rename_i j hrow
      have hji : j = i := AdaptedCollectedRelation.row.inj
        (hrow.symm.trans hrel)
      subst j
      split at hterminal
      · rename_i d hleftSome
        split at hterminal
        · contradiction
        · rename_i hnweight
          have hreal := chooseAdjacentInversion?_eq_some_realizes hleftSome
          exact (hnweight (adapted_adjacent_external_weight_le_four
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
                    exact (hnweight (adapted_adapted_adjacent_external_weight_le_four_right
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
                  exact (hnweight (adapted_adapted_adjacent_external_weight_le_four_right
                    X L evaluation p d hreal hlow)).elim
              · rename_i hrightNone
                exact ⟨hleftOrdered,
                  (chooseAdjacentInversion?_eq_none_iff_pairwise p.right).mp
                    hrightNone⟩
  · rename_i hnlow
    exact (hnlow hlow).elim

/-- At a terminal row mark, the final factor on the left does not exceed the Smith head. -/
theorem adaptedPlacedPacket_terminal_last_le_head
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : adaptedPlacedPacketExpansion X L evaluation p = none)
    (front : List Factor) (x : Factor)
    (hlast : splitLast? p.left = some (front, x)) :
    x ≤ adaptedLowRelationHead X i := by
  apply not_lt.mp
  intro hx
  unfold adaptedPlacedPacketExpansion at hterminal
  split at hterminal
  · split at hterminal
    · rename_i r hr hhigh
      have hbad : (AdaptedCollectedRelation.row i :
          AdaptedCollectedRelation X L evaluation) = .high r hr :=
        hrel.symm.trans hhigh
      cases hbad
    · rename_i j hrow
      have hji : j = i := AdaptedCollectedRelation.row.inj
        (hrow.symm.trans hrel)
      subst j
      split at hterminal
      · rename_i d hleftSome
        split at hterminal
        · contradiction
        · rename_i hnweight
          have hreal := chooseAdjacentInversion?_eq_some_realizes hleftSome
          exact (hnweight (adapted_adjacent_external_weight_le_four
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
theorem adaptedPlacedPacket_terminal_head_le_first
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : adaptedPlacedPacketExpansion X L evaluation p = none)
    (y : Factor) (tail : List Factor)
    (hright : p.right = y :: tail) :
    adaptedLowRelationHead X i ≤ y := by
  apply not_lt.mp
  intro hy
  unfold adaptedPlacedPacketExpansion at hterminal
  split at hterminal
  · split at hterminal
    · rename_i r hr hhigh
      have hbad : (AdaptedCollectedRelation.row i :
          AdaptedCollectedRelation X L evaluation) = .high r hr :=
        hrel.symm.trans hhigh
      cases hbad
    · rename_i j hrow
      have hji : j = i := AdaptedCollectedRelation.row.inj
        (hrow.symm.trans hrel)
      subst j
      split at hterminal
      · rename_i d hleftSome
        split at hterminal
        · contradiction
        · rename_i hnweight
          have hreal := chooseAdjacentInversion?_eq_some_realizes hleftSome
          exact (hnweight (adapted_adjacent_external_weight_le_four
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
theorem adaptedPlacedPacket_terminal_virtualFactors_pairwise
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : adaptedPlacedPacketExpansion X L evaluation p = none) :
    (p.virtualFactors X L evaluation).Pairwise (· ≤ ·) := by
  have horders := adaptedPlacedPacket_terminal_external_order
    X L evaluation p i hrel hlow hterminal
  let head := adaptedLowRelationHead X i
  have hleftHead : ∀ x ∈ p.left, x ≤ head := by
    intro x hx
    have hne : p.left ≠ [] := List.ne_nil_of_mem hx
    have hsplit : splitLast? p.left =
        some (p.left.dropLast, p.left.getLast hne) := by
      unfold splitLast?
      rw [List.getLast?_eq_getLast_of_ne_nil hne]
      rfl
    exact (horders.1.rel_getLast hx).trans
      (adaptedPlacedPacket_terminal_last_le_head X L evaluation p i hrel
        hlow hterminal p.left.dropLast (p.left.getLast hne) hsplit)
  have hheadRight : ∀ y ∈ p.right, head ≤ y := by
    intro y hy
    cases hright : p.right with
    | nil => simp [hright] at hy
    | cons first tail =>
        have hfirst := adaptedPlacedPacket_terminal_head_le_first
          X L evaluation p i hrel hlow hterminal first tail hright
        have hpair : (first :: tail).Pairwise (· ≤ ·) := by
          simpa [hright] using horders.2
        rw [hright] at hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · simpa [head, hy] using hfirst
        · exact (show head ≤ first by simpa [head] using hfirst).trans
            ((List.pairwise_cons.mp hpair).1 y hy)
  rw [AdaptedSmithPlacedPacket.virtualFactors, hrel]
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

/-! ## Exhaustive numerical table -/

/-- External weights of an adapted placed packet, with the relation mark omitted. -/
def AdaptedSmithPlacedPacket.externalWeights
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) : List ℕ :=
  (p.left ++ p.right).map (adaptedLowBasisWeight X)

/-- The adapted weight is monotone for the collector's weight-first order. -/
theorem adaptedLowBasisWeight_mono {i j : AdaptedLowBasisIndex X} (hij : i ≤ j) :
    adaptedLowBasisWeight X i ≤ adaptedLowBasisWeight X j := by
  exact lowHomogeneousBasisWeight_mono X hij

/-- Removing the row head from an ordered virtual word leaves the external word ordered. -/
theorem adaptedPlacedPacket_terminal_externalFactors_pairwise
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : adaptedPlacedPacketExpansion X L evaluation p = none) :
    (p.left ++ p.right).Pairwise (· ≤ ·) := by
  have hv := adaptedPlacedPacket_terminal_virtualFactors_pairwise
    X L evaluation p i hrel hlow hterminal
  rw [AdaptedSmithPlacedPacket.virtualFactors, hrel] at hv
  rw [List.pairwise_append] at hv ⊢
  refine ⟨hv.1, ?_, ?_⟩
  · exact (List.pairwise_cons.mp hv.2.1).2
  · intro x hx y hy
    exact hv.2.2 x hx y (by simp [hy])

/-- Every terminal row packet below weight five lies in the paper's exhaustive weight table. -/
theorem adaptedPlacedPacket_terminal_low_packet_table
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (hrel : p.relation = .row i)
    (hlow : p.totalWeight X < 5)
    (hterminal : adaptedPlacedPacketExpansion X L evaluation p = none) :
    let s := p.relation.weight X L evaluation
    let ws := p.externalWeights X
    (s = 1 ∧
      (ws = [] ∨ ws = [1] ∨ ws = [2] ∨ ws = [1, 1] ∨
        ws = [3] ∨ ws = [1, 2] ∨ ws = [1, 1, 1])) ∨
    (s = 2 ∧ (ws = [] ∨ ws = [1] ∨ ws = [2] ∨ ws = [1, 1])) ∨
    (s = 3 ∧ (ws = [] ∨ ws = [1])) ∨
    (s = 4 ∧ ws = []) := by
  apply lowPacketWeightSequence_complete
      (p.relation.weight_pos X L evaluation)
  refine ⟨?_, ?_, ?_⟩
  · rw [AdaptedSmithPlacedPacket.externalWeights, List.pairwise_map]
    exact (adaptedPlacedPacket_terminal_externalFactors_pairwise
      X L evaluation p i hrel hlow hterminal).imp
        (fun hij ↦ adaptedLowBasisWeight_mono X hij)
  · intro n hn
    rw [AdaptedSmithPlacedPacket.externalWeights] at hn
    simp only [List.mem_map] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    exact adaptedLowBasisWeight_pos X x
  · simpa [AdaptedSmithPlacedPacket.totalWeight,
      AdaptedSmithPlacedPacket.externalWeight,
      AdaptedSmithPlacedPacket.externalWeights, List.map_append,
      List.sum_append]

end

end DegreeFive

end LieRings
