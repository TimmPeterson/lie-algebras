import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedExpansion

/-!
# The coherent adapted placed Smith-row collector

This is the deterministic collector used in the degree-five calculation.  Its virtual PBW
word is obtained by replacing the relation mark by the row's Smith head.  The rewrite priority
is left word, left/mark crossing, mark/right crossing, then right word.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X
local notation "Factor" => AdaptedLowBasisIndex X

/-- Inversion count in the fixed finite homogeneous basis order. -/
def adaptedFactorInversionCount (X : Type u) [Finite X] :
    List (AdaptedLowBasisIndex X) → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + adaptedFactorInversionCount X xs

/-- Swapping an adjacent inverted pair removes exactly one inversion. -/
theorem adaptedFactorInversionCount_swap
    (left right : List Factor) (x y : Factor) (hxy : y < x) :
    adaptedFactorInversionCount X (left ++ x :: y :: right) =
      adaptedFactorInversionCount X (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnx : ¬x < y := not_lt_of_ge (le_of_lt hxy)
      simp [adaptedFactorInversionCount, hxy, hnx, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, adaptedFactorInversionCount]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp <;> omega
      rw [hfilter, ih]
      omega

/-- The virtual PBW word of a row packet.  A weight-five remainder is terminal and therefore
has no virtual head. -/
def AdaptedSmithPlacedPacket.virtualFactors
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) : List Factor :=
  match p.relation with
  | .row i => p.left ++ adaptedLowRelationHead X i :: p.right
  | .high _ _ => []

/-- The paper's complete termination datum attached to an exact placed packet. -/
def AdaptedSmithPlacedPacket.weightedPacket
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) : WeightedPacket :=
  ⟨p.relation.weight X L evaluation,
    (p.left ++ p.right).map (adaptedLowBasisWeight X),
    adaptedFactorInversionCount X (p.virtualFactors X L evaluation)⟩

/-- Deterministic one-step expansion.  Packets of total weight at least five and exact
weight-five relation remainders are terminal. -/
def adaptedPlacedPacketExpansion
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) :
    Option (List (ℤ × AdaptedSmithPlacedPacket X L evaluation)) :=
  if hlow : p.totalWeight X < 5 then
    match hrow : p.relation with
    | .high _ _ => none
    | .row i =>
        match hleftInv : chooseAdjacentInversion? p.left with
        | some d =>
            if hw : adaptedLowBasisWeight X d.x +
                adaptedLowBasisWeight X d.y ≤ 4 then
              some (adaptedLeftSwapExpansion X L evaluation p d hw)
            else none
        | none =>
            match hlast : splitLast? p.left with
            | some (front, x) =>
                if hx : adaptedLowRelationHead X i < x then
                  some (adaptedMoveLeftExpansion X L evaluation p front i x)
                else
                  match p.right with
                  | [] => none
                  | y :: tail =>
                      if hy : y < adaptedLowRelationHead X i then
                        some (adaptedMoveRightExpansion X L evaluation p i y tail)
                      else
                        match hrightInv : chooseAdjacentInversion? p.right with
                        | some d =>
                            if hw : adaptedLowBasisWeight X d.x +
                                adaptedLowBasisWeight X d.y ≤ 4 then
                              some (adaptedRightSwapExpansion X L evaluation p d hw)
                            else none
                        | none => none
            | none =>
                match p.right with
                | [] => none
                | y :: tail =>
                    if hy : y < adaptedLowRelationHead X i then
                      some (adaptedMoveRightExpansion X L evaluation p i y tail)
                    else
                      match hrightInv : chooseAdjacentInversion? p.right with
                      | some d =>
                          if hw : adaptedLowBasisWeight X d.x +
                              adaptedLowBasisWeight X d.y ≤ 4 then
                            some (adaptedRightSwapExpansion X L evaluation p d hw)
                          else none
                      | none => none
  else none

/-- Every chosen local expansion preserves the exact packet value. -/
theorem adaptedPlacedPacketExpansion_preserves
    (evaluation : LieHom ℤ F L)
    {p : AdaptedSmithPlacedPacket X L evaluation}
    {qs : List (ℤ × AdaptedSmithPlacedPacket X L evaluation)}
    (h : adaptedPlacedPacketExpansion X L evaluation p = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value X L evaluation).sum =
      p.value X L evaluation := by
  classical
  unfold adaptedPlacedPacketExpansion at h
  split at h
  · rename_i hlow
    split at h
    · contradiction
    · rename_i i hrow
      split at h
      · rename_i d hchosen
        split at h
        · rename_i hw
          simp only [Option.some.injEq] at h
          subst qs
          have hd := chooseAdjacentInversion?_eq_some_realizes hchosen
          exact (adaptedLeftSwapExpansion_value X L evaluation p d hd.1 hw).symm
        · contradiction
      · rename_i hleftNone
        split at h
        · rename_i front x hlast
          split at h
          · rename_i hx
            simp only [Option.some.injEq] at h
            subst qs
            exact (adaptedMoveLeftExpansion_value X L evaluation p front i x
              (splitLast?_eq_some hlast) hrow).symm
          · rename_i hnx
            split at h
            · contradiction
            · rename_i y tail hright
              split at h
              · rename_i hy
                simp only [Option.some.injEq] at h
                subst qs
                exact (adaptedMoveRightExpansion_value X L evaluation p i y tail
                  hright hrow).symm
              · rename_i hny
                split at h
                · rename_i d hchosenRight
                  split at h
                  · rename_i hw
                    simp only [Option.some.injEq] at h
                    subst qs
                    have hd := chooseAdjacentInversion?_eq_some_realizes hchosenRight
                    exact (adaptedRightSwapExpansion_value X L evaluation p d hd.1 hw).symm
                  · contradiction
                · contradiction
        · rename_i hlastNone
          split at h
          · contradiction
          · rename_i y tail hright
            split at h
            · rename_i hy
              simp only [Option.some.injEq] at h
              subst qs
              exact (adaptedMoveRightExpansion_value X L evaluation p i y tail
                hright hrow).symm
            · rename_i hny
              split at h
              · rename_i d hchosenRight
                split at h
                · rename_i hw
                  simp only [Option.some.injEq] at h
                  subst qs
                  have hd := chooseAdjacentInversion?_eq_some_realizes hchosenRight
                  exact (adaptedRightSwapExpansion_value X L evaluation p d hd.1 hw).symm
                · contradiction
              · contradiction
  · contradiction

/-- Strict descent induced from the exact packet's weighted datum. -/
def AdaptedPlacedPacketDescent
    (evaluation : LieHom ℤ F L)
    (new old : AdaptedSmithPlacedPacket X L evaluation) : Prop :=
  WeightedPacketDescent
    (new.weightedPacket X L evaluation) (old.weightedPacket X L evaluation)

theorem adaptedPlacedPacketDescent_wellFounded
    (evaluation : LieHom ℤ F L) :
    WellFounded (AdaptedPlacedPacketDescent X L evaluation) :=
  InvImage.wf (AdaptedSmithPlacedPacket.weightedPacket X L evaluation)
    weightedPacketDescent_wellFounded

/-- Raising a normalized row's least weight strictly decreases the first collector
coordinate. -/
theorem adaptedPlacedPacketDescent_withRow
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i j : AdaptedLowRelationRowIndex X)
    (left right oldLeft oldRight : List Factor)
    (hij : adaptedLowRelationRowWeight X i <
      adaptedLowRelationRowWeight X j) :
    AdaptedPlacedPacketDescent X L evaluation
      (p.withRow X L evaluation j left right)
      (p.withRow X L evaluation i oldLeft oldRight) := by
  unfold AdaptedPlacedPacketDescent WeightedPacketDescent
  apply Prod.Lex.left
  simp only [AdaptedSmithPlacedPacket.weightedPacket,
    AdaptedSmithPlacedPacket.withRow, AdaptedCollectedRelation.weight,
    weightedPacketComplexity]
  have hj4 := adaptedLowBasisWeight_le_four X j
  unfold adaptedLowRelationRowWeight at hij ⊢
  omega

/-- Every exact high remainder is below every low Smith row in the first coordinate. -/
theorem adaptedPlacedPacketDescent_withHigh
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (r : LinearMap.ker evaluation.toLinearMap)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh X 5)
    (left right oldLeft oldRight : List Factor) :
    adaptedLowRelationRowWeight X i < 4 →
    AdaptedPlacedPacketDescent X L evaluation
      (p.withHigh X L evaluation r hr left right)
      (p.withRow X L evaluation i oldLeft oldRight) := by
  intro hi
  unfold AdaptedPlacedPacketDescent WeightedPacketDescent
  apply Prod.Lex.left
  simp only [AdaptedSmithPlacedPacket.weightedPacket,
    AdaptedSmithPlacedPacket.withHigh, AdaptedSmithPlacedPacket.withRow,
    AdaptedCollectedRelation.weight, weightedPacketComplexity]
  norm_num
  omega

/-- With the row fixed, strictly fewer external factors decrease the second coordinate. -/
theorem adaptedPlacedPacketDescent_sameRow_length
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (newLeft newRight oldLeft oldRight : List Factor)
    (hlen : (newLeft ++ newRight).length < (oldLeft ++ oldRight).length) :
    AdaptedPlacedPacketDescent X L evaluation
      (p.withRow X L evaluation i newLeft newRight)
      (p.withRow X L evaluation i oldLeft oldRight) := by
  unfold AdaptedPlacedPacketDescent WeightedPacketDescent
  apply Prod.Lex.right
  apply Prod.Lex.left
  simpa [AdaptedSmithPlacedPacket.weightedPacket] using hlen

/-- With row and factor count fixed, a smaller virtual inversion count decreases the final
coordinate. -/
theorem adaptedPlacedPacketDescent_sameRow_inversions
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (newLeft newRight oldLeft oldRight : List Factor)
    (hlen : (newLeft ++ newRight).length = (oldLeft ++ oldRight).length)
    (hinv : adaptedFactorInversionCount X
        (newLeft ++ adaptedLowRelationHead X i :: newRight) <
      adaptedFactorInversionCount X
        (oldLeft ++ adaptedLowRelationHead X i :: oldRight)) :
    AdaptedPlacedPacketDescent X L evaluation
      (p.withRow X L evaluation i newLeft newRight)
      (p.withRow X L evaluation i oldLeft oldRight) := by
  unfold AdaptedPlacedPacketDescent WeightedPacketDescent
  apply Prod.Lex.right
  have heq :
      (AdaptedSmithPlacedPacket.weightedPacket X L evaluation
        (p.withRow X L evaluation i newLeft newRight)).externalWeights.length =
      (AdaptedSmithPlacedPacket.weightedPacket X L evaluation
        (p.withRow X L evaluation i oldLeft oldRight)).externalWeights.length := by
    simpa [AdaptedSmithPlacedPacket.weightedPacket] using hlen
  rw [heq]
  apply Prod.Lex.right
  simpa [AdaptedSmithPlacedPacket.weightedPacket,
    AdaptedSmithPlacedPacket.virtualFactors] using hinv

@[simp]
theorem AdaptedSmithPlacedPacket.withRow_eq_self
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (hrow : p.relation = .row i) :
    p.withRow X L evaluation i p.left p.right = p := by
  rcases p with ⟨left, relation, right⟩
  simp only at hrow
  subst relation
  rfl

theorem adaptedLeftSwapExpansion_decreases
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (d : AdjacentInversionData Factor)
    (hrow : p.relation = .row i)
    (hd : d.Realizes p.left)
    (hw : adaptedLowBasisWeight X d.x +
      adaptedLowBasisWeight X d.y ≤ 4) :
    ∀ q ∈ adaptedLeftSwapExpansion X L evaluation p d hw,
      AdaptedPlacedPacketDescent X L evaluation q.2 p := by
  classical
  intro q hq
  simp only [adaptedLeftSwapExpansion, List.mem_cons] at hq
  rcases hq with rfl | hq
  · have hinv0 := adaptedFactorInversionCount_swap X d.left
      (d.right ++ adaptedLowRelationHead X i :: p.right)
      d.x d.y hd.2
    have hinv' : adaptedFactorInversionCount X
          (d.left ++ d.y :: d.x ::
            (d.right ++ adaptedLowRelationHead X i :: p.right)) <
        adaptedFactorInversionCount X
          (d.left ++ d.x :: d.y ::
            (d.right ++ adaptedLowRelationHead X i :: p.right)) := by
      omega
    have hinv : adaptedFactorInversionCount X
          ((d.left ++ d.y :: d.x :: d.right) ++
            adaptedLowRelationHead X i :: p.right) <
        adaptedFactorInversionCount X
          (p.left ++ adaptedLowRelationHead X i :: p.right) := by
      rw [hd.1]
      simpa only [List.append_assoc, List.cons_append] using hinv'
    simpa [AdaptedSmithPlacedPacket.swapLeft,
      AdaptedSmithPlacedPacket.withFactors, hrow,
      AdaptedSmithPlacedPacket.withRow_eq_self] using
      adaptedPlacedPacketDescent_sameRow_inversions X L evaluation p i
        (d.left ++ d.y :: d.x :: d.right) p.right p.left p.right
        (by simp [hd.1]) hinv
  · unfold finsuppTaggedList at hq
    simp only [List.mem_map] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    simpa [AdaptedSmithPlacedPacket.bracketLeft,
      AdaptedSmithPlacedPacket.withFactors, hrow,
      AdaptedSmithPlacedPacket.withRow_eq_self] using
      adaptedPlacedPacketDescent_sameRow_length X L evaluation p i
        (d.left ++ z :: d.right) p.right p.left p.right (by simp [hd.1])

theorem adaptedRightSwapExpansion_decreases
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (d : AdjacentInversionData Factor)
    (hrow : p.relation = .row i)
    (hd : d.Realizes p.right)
    (hw : adaptedLowBasisWeight X d.x +
      adaptedLowBasisWeight X d.y ≤ 4) :
    ∀ q ∈ adaptedRightSwapExpansion X L evaluation p d hw,
      AdaptedPlacedPacketDescent X L evaluation q.2 p := by
  classical
  intro q hq
  simp only [adaptedRightSwapExpansion, List.mem_cons] at hq
  rcases hq with rfl | hq
  · have hinv0 := adaptedFactorInversionCount_swap X
      (p.left ++ [adaptedLowRelationHead X i] ++ d.left)
      d.right d.x d.y hd.2
    have hinv' : adaptedFactorInversionCount X
          ((p.left ++ [adaptedLowRelationHead X i] ++ d.left) ++
            d.y :: d.x :: d.right) <
        adaptedFactorInversionCount X
          ((p.left ++ [adaptedLowRelationHead X i] ++ d.left) ++
            d.x :: d.y :: d.right) := by
      omega
    have hinv : adaptedFactorInversionCount X
          (p.left ++ adaptedLowRelationHead X i ::
            (d.left ++ d.y :: d.x :: d.right)) <
        adaptedFactorInversionCount X
          (p.left ++ adaptedLowRelationHead X i :: p.right) := by
      rw [hd.1]
      simpa only [List.append_assoc, List.cons_append,
        List.singleton_append] using hinv'
    simpa [AdaptedSmithPlacedPacket.swapRight,
      AdaptedSmithPlacedPacket.withFactors, hrow,
      AdaptedSmithPlacedPacket.withRow_eq_self] using
      adaptedPlacedPacketDescent_sameRow_inversions X L evaluation p i
        p.left (d.left ++ d.y :: d.x :: d.right) p.left p.right
        (by simp [hd.1]) hinv
  · unfold finsuppTaggedList at hq
    simp only [List.mem_map] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    simpa [AdaptedSmithPlacedPacket.bracketRight,
      AdaptedSmithPlacedPacket.withFactors, hrow,
      AdaptedSmithPlacedPacket.withRow_eq_self] using
      adaptedPlacedPacketDescent_sameRow_length X L evaluation p i
        p.left (d.left ++ z :: d.right) p.left p.right (by simp [hd.1])

theorem adaptedMoveLeftExpansion_decreases
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (front : List Factor) (i : AdaptedLowRelationRowIndex X)
    (x : Factor)
    (hrow : p.relation = .row i)
    (hleft : p.left = front ++ [x])
    (hx : adaptedLowRelationHead X i < x)
    (hlow : p.totalWeight X < 5) :
    ∀ q ∈ adaptedMoveLeftExpansion X L evaluation p front i x,
      AdaptedPlacedPacketDescent X L evaluation q.2 p := by
  classical
  intro q hq
  simp only [adaptedMoveLeftExpansion, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_singleton] at hq
  rcases hq with hmain | hhigh
  · rcases hmain with hprincipal | hq
    · rcases hprincipal with rfl
      have hinv0 := adaptedFactorInversionCount_swap X front p.right x
        (adaptedLowRelationHead X i) hx
      have hinv : adaptedFactorInversionCount X
          (front ++ adaptedLowRelationHead X i :: x :: p.right) <
        adaptedFactorInversionCount X
          (p.left ++ adaptedLowRelationHead X i :: p.right) := by
        rw [hleft]
        simpa only [List.append_assoc, List.singleton_append] using
          (show adaptedFactorInversionCount X
                (front ++ adaptedLowRelationHead X i :: x :: p.right) <
              adaptedFactorInversionCount X
                (front ++ x :: adaptedLowRelationHead X i :: p.right) by
            omega)
      simpa [AdaptedSmithPlacedPacket.moveLeftAcross,
        AdaptedSmithPlacedPacket.withFactors, hrow,
        AdaptedSmithPlacedPacket.withRow_eq_self] using
        adaptedPlacedPacketDescent_sameRow_inversions X L evaluation p i
          front (x :: p.right) p.left p.right (by simp [hleft]) hinv
    · obtain ⟨tag, htag, htagq⟩ := hq
      subst q
      unfold finsuppTaggedList at htag
      simp only [List.mem_map] at htag
      obtain ⟨j, hj, rfl⟩ := htag
      have hj' : j ∈ (adaptedLowRelationBracketRowCoefficients X L evaluation i x).support := by
        simpa using hj
      have hnonzero : adaptedLowRelationBracketRowCoefficients X L evaluation i x j ≠ 0 :=
        Finsupp.mem_support_iff.mp hj'
      have hge : adaptedLowRelationRowWeight X i +
          adaptedLowBasisWeight X x ≤
            adaptedLowRelationRowWeight X j := by
        apply le_of_not_gt
        intro hlt
        exact hnonzero (adaptedLowRelationBracketRowCoefficients_apply_eq_zero_of_lt
          X L evaluation i j x hlt)
      have hgt : adaptedLowRelationRowWeight X i <
          adaptedLowRelationRowWeight X j :=
        lt_of_lt_of_le (Nat.lt_add_of_pos_right
          (adaptedLowBasisWeight_pos X x)) hge
      simpa [AdaptedSmithPlacedPacket.leftRelationCorrection, hrow,
        AdaptedSmithPlacedPacket.withRow_eq_self] using
        adaptedPlacedPacketDescent_withRow X L evaluation p i j front p.right
          p.left p.right hgt
  · rcases hhigh with hhigh | hnil
    · rcases hhigh with rfl
      have hi : adaptedLowRelationRowWeight X i < 4 := by
        simp [AdaptedSmithPlacedPacket.totalWeight,
          AdaptedSmithPlacedPacket.externalWeight, hrow,
          AdaptedCollectedRelation.weight, hleft] at hlow
        have hxpos := adaptedLowBasisWeight_pos X x
        omega
      simpa [AdaptedSmithPlacedPacket.leftHighCorrection, hrow,
        AdaptedSmithPlacedPacket.withRow_eq_self] using
        adaptedPlacedPacketDescent_withHigh X L evaluation p i
          (adaptedLowRelationBracketWeightFiveRemainder X L evaluation i x)
          (adaptedLowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
          front p.right p.left p.right hi
    · simp at hnil

theorem adaptedMoveRightExpansion_decreases
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X) (x : Factor)
    (tail : List Factor)
    (hrow : p.relation = .row i)
    (hright : p.right = x :: tail)
    (hx : x < adaptedLowRelationHead X i)
    (hlow : p.totalWeight X < 5) :
    ∀ q ∈ adaptedMoveRightExpansion X L evaluation p i x tail,
      AdaptedPlacedPacketDescent X L evaluation q.2 p := by
  classical
  intro q hq
  simp only [adaptedMoveRightExpansion, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_singleton] at hq
  rcases hq with hmain | hhigh
  · rcases hmain with hprincipal | hq
    · rcases hprincipal with rfl
      have hinv0 := adaptedFactorInversionCount_swap X p.left tail
        (adaptedLowRelationHead X i) x hx
      have hinv : adaptedFactorInversionCount X
          ((p.left ++ [x]) ++ adaptedLowRelationHead X i :: tail) <
        adaptedFactorInversionCount X
          (p.left ++ adaptedLowRelationHead X i :: p.right) := by
        rw [hright]
        simpa only [List.append_assoc, List.singleton_append] using
          (show adaptedFactorInversionCount X
                (p.left ++ x :: adaptedLowRelationHead X i :: tail) <
              adaptedFactorInversionCount X
                (p.left ++ adaptedLowRelationHead X i :: x :: tail) by
            omega)
      simpa [AdaptedSmithPlacedPacket.moveRightAcross,
        AdaptedSmithPlacedPacket.withFactors, hrow,
        AdaptedSmithPlacedPacket.withRow_eq_self] using
        adaptedPlacedPacketDescent_sameRow_inversions X L evaluation p i
          (p.left ++ [x]) tail p.left p.right (by simp [hright]) hinv
    · unfold finsuppTaggedList at hq
      simp only [List.mem_map] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      have hj' : j ∈ (adaptedLowRelationBracketRowCoefficients X L evaluation i x).support := by
        simpa using hj
      have hnonzero : adaptedLowRelationBracketRowCoefficients X L evaluation i x j ≠ 0 :=
        Finsupp.mem_support_iff.mp hj'
      have hge : adaptedLowRelationRowWeight X i +
          adaptedLowBasisWeight X x ≤
            adaptedLowRelationRowWeight X j := by
        apply le_of_not_gt
        intro hlt
        exact hnonzero (adaptedLowRelationBracketRowCoefficients_apply_eq_zero_of_lt
          X L evaluation i j x hlt)
      have hgt : adaptedLowRelationRowWeight X i <
          adaptedLowRelationRowWeight X j :=
        lt_of_lt_of_le (Nat.lt_add_of_pos_right
          (adaptedLowBasisWeight_pos X x)) hge
      simpa [AdaptedSmithPlacedPacket.rightRelationCorrection, hrow,
        AdaptedSmithPlacedPacket.withRow_eq_self] using
        adaptedPlacedPacketDescent_withRow X L evaluation p i j p.left tail
          p.left p.right hgt
  · rcases hhigh with hhigh | hnil
    · rcases hhigh with rfl
      have hi : adaptedLowRelationRowWeight X i < 4 := by
        simp [AdaptedSmithPlacedPacket.totalWeight,
          AdaptedSmithPlacedPacket.externalWeight, hrow,
          AdaptedCollectedRelation.weight, hright] at hlow
        have hxpos := adaptedLowBasisWeight_pos X x
        omega
      simpa [AdaptedSmithPlacedPacket.rightHighCorrection, hrow,
        AdaptedSmithPlacedPacket.withRow_eq_self] using
        adaptedPlacedPacketDescent_withHigh X L evaluation p i
          (adaptedLowRelationBracketWeightFiveRemainder X L evaluation i x)
          (adaptedLowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
          p.left tail p.left p.right hi
    · simp at hnil

theorem adaptedPlacedPacketExpansion_decreases
    (evaluation : LieHom ℤ F L)
    {p : AdaptedSmithPlacedPacket X L evaluation}
    {qs : List (ℤ × AdaptedSmithPlacedPacket X L evaluation)}
    (h : adaptedPlacedPacketExpansion X L evaluation p = some qs) :
    ∀ q ∈ qs, AdaptedPlacedPacketDescent X L evaluation q.2 p := by
  classical
  unfold adaptedPlacedPacketExpansion at h
  split at h
  · rename_i hlow
    split at h
    · contradiction
    · rename_i i hrow
      split at h
      · rename_i d hchosen
        split at h
        · rename_i hw
          simp only [Option.some.injEq] at h
          subst qs
          exact adaptedLeftSwapExpansion_decreases X L evaluation p i d hrow
            (chooseAdjacentInversion?_eq_some_realizes hchosen) hw
        · contradiction
      · rename_i hleftNone
        split at h
        · rename_i front x hlast
          split at h
          · rename_i hx
            simp only [Option.some.injEq] at h
            subst qs
            exact adaptedMoveLeftExpansion_decreases X L evaluation p front i x hrow
              (splitLast?_eq_some hlast) hx hlow
          · rename_i hnx
            split at h
            · contradiction
            · rename_i y tail hright
              split at h
              · rename_i hy
                simp only [Option.some.injEq] at h
                subst qs
                exact adaptedMoveRightExpansion_decreases X L evaluation p i y tail hrow
                  hright hy hlow
              · rename_i hny
                split at h
                · rename_i d hchosenRight
                  split at h
                  · rename_i hw
                    simp only [Option.some.injEq] at h
                    subst qs
                    exact adaptedRightSwapExpansion_decreases X L evaluation p i d hrow
                      (chooseAdjacentInversion?_eq_some_realizes hchosenRight) hw
                  · contradiction
                · contradiction
        · rename_i hlastNone
          split at h
          · contradiction
          · rename_i y tail hright
            split at h
            · rename_i hy
              simp only [Option.some.injEq] at h
              subst qs
              exact adaptedMoveRightExpansion_decreases X L evaluation p i y tail hrow
                hright hy hlow
            · rename_i hny
              split at h
              · rename_i d hchosenRight
                split at h
                · rename_i hw
                  simp only [Option.some.injEq] at h
                  subst qs
                  exact adaptedRightSwapExpansion_decreases X L evaluation p i d hrow
                    (chooseAdjacentInversion?_eq_some_realizes hchosenRight) hw
                · contradiction
              · contradiction
  · contradiction

/-- The exact adapted placed collector. -/
def adaptedPlacedPacketCollector
    (evaluation : LieHom ℤ F L) :
    FiniteTaggedCollector
      (AdaptedSmithPlacedPacket X L evaluation) (UEA ℤ F) where
  relation := AdaptedPlacedPacketDescent X L evaluation
  wellFounded := adaptedPlacedPacketDescent_wellFounded X L evaluation
  expansion := adaptedPlacedPacketExpansion X L evaluation
  value := AdaptedSmithPlacedPacket.value X L evaluation
  decreases := adaptedPlacedPacketExpansion_decreases X L evaluation
  preserves := adaptedPlacedPacketExpansion_preserves X L evaluation

theorem adaptedPlacedPacketCollector_evaluate_normalForm
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) :
    (adaptedPlacedPacketCollector X L evaluation).evaluate
        ((adaptedPlacedPacketCollector X L evaluation).normalForm p) =
      p.value X L evaluation :=
  (adaptedPlacedPacketCollector X L evaluation).evaluate_normalForm p

/-! ## Shape of terminal low packets -/

/-- In a packet of total weight below five, every adjacent pair of external factors has
combined weight at most four.  This is the small numerical observation which ensures that
none of the ordinary PBW swaps can become stuck at the truncation boundary. -/
theorem adapted_adjacent_external_weight_le_four
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor)
    (hd : d.Realizes p.left)
    (hlow : p.totalWeight X < 5) :
    adaptedLowBasisWeight X d.x +
        adaptedLowBasisWeight X d.y ≤ 4 := by
  have hrel := p.relation.weight_pos X L evaluation
  simp only [AdaptedSmithPlacedPacket.totalWeight,
    AdaptedSmithPlacedPacket.externalWeight, hd.1, List.map_append,
    List.map_cons, List.sum_append, List.sum_cons] at hlow
  omega

theorem adapted_adapted_adjacent_external_weight_le_four_right
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor)
    (hd : d.Realizes p.right)
    (hlow : p.totalWeight X < 5) :
    adaptedLowBasisWeight X d.x +
        adaptedLowBasisWeight X d.y ≤ 4 := by
  have hrel := p.relation.weight_pos X L evaluation
  simp only [AdaptedSmithPlacedPacket.totalWeight,
    AdaptedSmithPlacedPacket.externalWeight, hd.1, List.map_append,
    List.map_cons, List.sum_append, List.sum_cons] at hlow
  omega

end

end DegreeFive

end LieRings
