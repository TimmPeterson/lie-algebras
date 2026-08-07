import LieRings.DimensionSubring.DegreeFive.FinitePlacedExpansion

/-!
# The finite placed Smith-row collector

This is the deterministic collector used in the degree-five calculation.  Its virtual PBW
word is obtained by replacing the relation mark by the row's Smith head.  The rewrite priority
is left word, left/mark crossing, mark/right crossing, then right word.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X
local notation "Factor" => LowHomogeneousBasisIndex X

/-- Inversion count in the fixed finite homogeneous basis order. -/
def finiteFactorInversionCount (X : Type u) [Finite X] :
    List (LowHomogeneousBasisIndex X) → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + finiteFactorInversionCount X xs

/-- Swapping an adjacent inverted pair removes exactly one inversion. -/
theorem finiteFactorInversionCount_swap
    (left right : List Factor) (x y : Factor) (hxy : y < x) :
    finiteFactorInversionCount X (left ++ x :: y :: right) =
      finiteFactorInversionCount X (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnx : ¬x < y := not_lt_of_ge (le_of_lt hxy)
      simp [finiteFactorInversionCount, hxy, hnx, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, finiteFactorInversionCount]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp <;> omega
      rw [hfilter, ih]
      omega

/-- The virtual PBW word of a row packet.  A weight-five remainder is terminal and therefore
has no virtual head. -/
def FiniteSmithPlacedPacket.virtualFactors
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) : List Factor :=
  match p.relation with
  | .row i => p.left ++ lowRelationSmithHead X L evaluation i :: p.right
  | .high _ _ => []

/-- The paper's complete termination datum attached to an exact placed packet. -/
def FiniteSmithPlacedPacket.weightedPacket
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) : WeightedPacket :=
  ⟨p.relation.weight X L evaluation,
    (p.left ++ p.right).map (lowHomogeneousBasisWeight X),
    finiteFactorInversionCount X (p.virtualFactors X L evaluation)⟩

/-- Deterministic one-step expansion.  Packets of total weight at least five and exact
weight-five relation remainders are terminal. -/
def finitePlacedPacketExpansion
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) :
    Option (List (ℤ × FiniteSmithPlacedPacket X L evaluation)) :=
  if hlow : p.totalWeight X < 5 then
    match hrow : p.relation with
    | .high _ _ => none
    | .row i =>
        match hleftInv : chooseAdjacentInversion? p.left with
        | some d =>
            if hw : lowHomogeneousBasisWeight X d.x +
                lowHomogeneousBasisWeight X d.y ≤ 4 then
              some (leftSwapExpansion X L evaluation p d hw)
            else none
        | none =>
            match hlast : splitLast? p.left with
            | some (front, x) =>
                if hx : lowRelationSmithHead X L evaluation i < x then
                  some (moveLeftExpansion X L evaluation p front i x)
                else
                  match p.right with
                  | [] => none
                  | y :: tail =>
                      if hy : y < lowRelationSmithHead X L evaluation i then
                        some (moveRightExpansion X L evaluation p i y tail)
                      else
                        match hrightInv : chooseAdjacentInversion? p.right with
                        | some d =>
                            if hw : lowHomogeneousBasisWeight X d.x +
                                lowHomogeneousBasisWeight X d.y ≤ 4 then
                              some (rightSwapExpansion X L evaluation p d hw)
                            else none
                        | none => none
            | none =>
                match p.right with
                | [] => none
                | y :: tail =>
                    if hy : y < lowRelationSmithHead X L evaluation i then
                      some (moveRightExpansion X L evaluation p i y tail)
                    else
                      match hrightInv : chooseAdjacentInversion? p.right with
                      | some d =>
                          if hw : lowHomogeneousBasisWeight X d.x +
                              lowHomogeneousBasisWeight X d.y ≤ 4 then
                            some (rightSwapExpansion X L evaluation p d hw)
                          else none
                      | none => none
  else none

/-- Every chosen local expansion preserves the exact packet value. -/
theorem finitePlacedPacketExpansion_preserves
    (evaluation : LieHom ℤ F L)
    {p : FiniteSmithPlacedPacket X L evaluation}
    {qs : List (ℤ × FiniteSmithPlacedPacket X L evaluation)}
    (h : finitePlacedPacketExpansion X L evaluation p = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value X L evaluation).sum =
      p.value X L evaluation := by
  classical
  unfold finitePlacedPacketExpansion at h
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
          exact (leftSwapExpansion_value X L evaluation p d hd.1 hw).symm
        · contradiction
      · rename_i hleftNone
        split at h
        · rename_i front x hlast
          split at h
          · rename_i hx
            simp only [Option.some.injEq] at h
            subst qs
            exact (moveLeftExpansion_value X L evaluation p front i x
              (splitLast?_eq_some hlast) hrow).symm
          · rename_i hnx
            split at h
            · contradiction
            · rename_i y tail hright
              split at h
              · rename_i hy
                simp only [Option.some.injEq] at h
                subst qs
                exact (moveRightExpansion_value X L evaluation p i y tail
                  hright hrow).symm
              · rename_i hny
                split at h
                · rename_i d hchosenRight
                  split at h
                  · rename_i hw
                    simp only [Option.some.injEq] at h
                    subst qs
                    have hd := chooseAdjacentInversion?_eq_some_realizes hchosenRight
                    exact (rightSwapExpansion_value X L evaluation p d hd.1 hw).symm
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
              exact (moveRightExpansion_value X L evaluation p i y tail
                hright hrow).symm
            · rename_i hny
              split at h
              · rename_i d hchosenRight
                split at h
                · rename_i hw
                  simp only [Option.some.injEq] at h
                  subst qs
                  have hd := chooseAdjacentInversion?_eq_some_realizes hchosenRight
                  exact (rightSwapExpansion_value X L evaluation p d hd.1 hw).symm
                · contradiction
              · contradiction
  · contradiction

/-- Strict descent induced from the exact packet's weighted datum. -/
def FinitePlacedPacketDescent
    (evaluation : LieHom ℤ F L)
    (new old : FiniteSmithPlacedPacket X L evaluation) : Prop :=
  WeightedPacketDescent
    (new.weightedPacket X L evaluation) (old.weightedPacket X L evaluation)

theorem finitePlacedPacketDescent_wellFounded
    (evaluation : LieHom ℤ F L) :
    WellFounded (FinitePlacedPacketDescent X L evaluation) :=
  InvImage.wf (FiniteSmithPlacedPacket.weightedPacket X L evaluation)
    weightedPacketDescent_wellFounded

/-- Raising a normalized row's least weight strictly decreases the first collector
coordinate. -/
theorem finitePlacedPacketDescent_withRow
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i j : LowRelationSmithRowIndex X L evaluation)
    (left right oldLeft oldRight : List Factor)
    (hij : lowRelationSmithRowWeight X L evaluation i <
      lowRelationSmithRowWeight X L evaluation j) :
    FinitePlacedPacketDescent X L evaluation
      (p.withRow X L evaluation j left right)
      (p.withRow X L evaluation i oldLeft oldRight) := by
  unfold FinitePlacedPacketDescent WeightedPacketDescent
  apply Prod.Lex.left
  simp only [FiniteSmithPlacedPacket.weightedPacket,
    FiniteSmithPlacedPacket.withRow, FiniteCollectedRelation.weight,
    weightedPacketComplexity]
  have hj4 := lowRelationSmithRowWeight_le_four X L evaluation j
  omega

/-- Every exact high remainder is below every low Smith row in the first coordinate. -/
theorem finitePlacedPacketDescent_withHigh
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (r : LinearMap.ker evaluation.toLinearMap)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh X 5)
    (left right oldLeft oldRight : List Factor) :
    lowRelationSmithRowWeight X L evaluation i < 4 →
    FinitePlacedPacketDescent X L evaluation
      (p.withHigh X L evaluation r hr left right)
      (p.withRow X L evaluation i oldLeft oldRight) := by
  intro hi
  unfold FinitePlacedPacketDescent WeightedPacketDescent
  apply Prod.Lex.left
  simp only [FiniteSmithPlacedPacket.weightedPacket,
    FiniteSmithPlacedPacket.withHigh, FiniteSmithPlacedPacket.withRow,
    FiniteCollectedRelation.weight, weightedPacketComplexity]
  norm_num
  omega

/-- With the row fixed, strictly fewer external factors decrease the second coordinate. -/
theorem finitePlacedPacketDescent_sameRow_length
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (newLeft newRight oldLeft oldRight : List Factor)
    (hlen : (newLeft ++ newRight).length < (oldLeft ++ oldRight).length) :
    FinitePlacedPacketDescent X L evaluation
      (p.withRow X L evaluation i newLeft newRight)
      (p.withRow X L evaluation i oldLeft oldRight) := by
  unfold FinitePlacedPacketDescent WeightedPacketDescent
  apply Prod.Lex.right
  apply Prod.Lex.left
  simpa [FiniteSmithPlacedPacket.weightedPacket] using hlen

/-- With row and factor count fixed, a smaller virtual inversion count decreases the final
coordinate. -/
theorem finitePlacedPacketDescent_sameRow_inversions
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (newLeft newRight oldLeft oldRight : List Factor)
    (hlen : (newLeft ++ newRight).length = (oldLeft ++ oldRight).length)
    (hinv : finiteFactorInversionCount X
        (newLeft ++ lowRelationSmithHead X L evaluation i :: newRight) <
      finiteFactorInversionCount X
        (oldLeft ++ lowRelationSmithHead X L evaluation i :: oldRight)) :
    FinitePlacedPacketDescent X L evaluation
      (p.withRow X L evaluation i newLeft newRight)
      (p.withRow X L evaluation i oldLeft oldRight) := by
  unfold FinitePlacedPacketDescent WeightedPacketDescent
  apply Prod.Lex.right
  have heq :
      (FiniteSmithPlacedPacket.weightedPacket X L evaluation
        (p.withRow X L evaluation i newLeft newRight)).externalWeights.length =
      (FiniteSmithPlacedPacket.weightedPacket X L evaluation
        (p.withRow X L evaluation i oldLeft oldRight)).externalWeights.length := by
    simpa [FiniteSmithPlacedPacket.weightedPacket] using hlen
  rw [heq]
  apply Prod.Lex.right
  simpa [FiniteSmithPlacedPacket.weightedPacket,
    FiniteSmithPlacedPacket.virtualFactors] using hinv

@[simp]
theorem FiniteSmithPlacedPacket.withRow_eq_self
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (hrow : p.relation = .row i) :
    p.withRow X L evaluation i p.left p.right = p := by
  rcases p with ⟨left, relation, right⟩
  simp only at hrow
  subst relation
  rfl

theorem leftSwapExpansion_decreases
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (d : AdjacentInversionData Factor)
    (hrow : p.relation = .row i)
    (hd : d.Realizes p.left)
    (hw : lowHomogeneousBasisWeight X d.x +
      lowHomogeneousBasisWeight X d.y ≤ 4) :
    ∀ q ∈ leftSwapExpansion X L evaluation p d hw,
      FinitePlacedPacketDescent X L evaluation q.2 p := by
  classical
  intro q hq
  simp only [leftSwapExpansion, List.mem_cons] at hq
  rcases hq with rfl | hq
  · have hinv0 := finiteFactorInversionCount_swap X d.left
      (d.right ++ lowRelationSmithHead X L evaluation i :: p.right)
      d.x d.y hd.2
    have hinv' : finiteFactorInversionCount X
          (d.left ++ d.y :: d.x ::
            (d.right ++ lowRelationSmithHead X L evaluation i :: p.right)) <
        finiteFactorInversionCount X
          (d.left ++ d.x :: d.y ::
            (d.right ++ lowRelationSmithHead X L evaluation i :: p.right)) := by
      omega
    have hinv : finiteFactorInversionCount X
          ((d.left ++ d.y :: d.x :: d.right) ++
            lowRelationSmithHead X L evaluation i :: p.right) <
        finiteFactorInversionCount X
          (p.left ++ lowRelationSmithHead X L evaluation i :: p.right) := by
      rw [hd.1]
      simpa only [List.append_assoc, List.cons_append] using hinv'
    simpa [FiniteSmithPlacedPacket.swapLeft,
      FiniteSmithPlacedPacket.withFactors, hrow,
      FiniteSmithPlacedPacket.withRow_eq_self] using
      finitePlacedPacketDescent_sameRow_inversions X L evaluation p i
        (d.left ++ d.y :: d.x :: d.right) p.right p.left p.right
        (by simp [hd.1]) hinv
  · unfold finsuppTaggedList at hq
    simp only [List.mem_map] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    simpa [FiniteSmithPlacedPacket.bracketLeft,
      FiniteSmithPlacedPacket.withFactors, hrow,
      FiniteSmithPlacedPacket.withRow_eq_self] using
      finitePlacedPacketDescent_sameRow_length X L evaluation p i
        (d.left ++ z :: d.right) p.right p.left p.right (by simp [hd.1])

theorem rightSwapExpansion_decreases
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (d : AdjacentInversionData Factor)
    (hrow : p.relation = .row i)
    (hd : d.Realizes p.right)
    (hw : lowHomogeneousBasisWeight X d.x +
      lowHomogeneousBasisWeight X d.y ≤ 4) :
    ∀ q ∈ rightSwapExpansion X L evaluation p d hw,
      FinitePlacedPacketDescent X L evaluation q.2 p := by
  classical
  intro q hq
  simp only [rightSwapExpansion, List.mem_cons] at hq
  rcases hq with rfl | hq
  · have hinv0 := finiteFactorInversionCount_swap X
      (p.left ++ [lowRelationSmithHead X L evaluation i] ++ d.left)
      d.right d.x d.y hd.2
    have hinv' : finiteFactorInversionCount X
          ((p.left ++ [lowRelationSmithHead X L evaluation i] ++ d.left) ++
            d.y :: d.x :: d.right) <
        finiteFactorInversionCount X
          ((p.left ++ [lowRelationSmithHead X L evaluation i] ++ d.left) ++
            d.x :: d.y :: d.right) := by
      omega
    have hinv : finiteFactorInversionCount X
          (p.left ++ lowRelationSmithHead X L evaluation i ::
            (d.left ++ d.y :: d.x :: d.right)) <
        finiteFactorInversionCount X
          (p.left ++ lowRelationSmithHead X L evaluation i :: p.right) := by
      rw [hd.1]
      simpa only [List.append_assoc, List.cons_append,
        List.singleton_append] using hinv'
    simpa [FiniteSmithPlacedPacket.swapRight,
      FiniteSmithPlacedPacket.withFactors, hrow,
      FiniteSmithPlacedPacket.withRow_eq_self] using
      finitePlacedPacketDescent_sameRow_inversions X L evaluation p i
        p.left (d.left ++ d.y :: d.x :: d.right) p.left p.right
        (by simp [hd.1]) hinv
  · unfold finsuppTaggedList at hq
    simp only [List.mem_map] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    simpa [FiniteSmithPlacedPacket.bracketRight,
      FiniteSmithPlacedPacket.withFactors, hrow,
      FiniteSmithPlacedPacket.withRow_eq_self] using
      finitePlacedPacketDescent_sameRow_length X L evaluation p i
        p.left (d.left ++ z :: d.right) p.left p.right (by simp [hd.1])

theorem moveLeftExpansion_decreases
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (front : List Factor) (i : LowRelationSmithRowIndex X L evaluation)
    (x : Factor)
    (hrow : p.relation = .row i)
    (hleft : p.left = front ++ [x])
    (hx : lowRelationSmithHead X L evaluation i < x)
    (hlow : p.totalWeight X < 5) :
    ∀ q ∈ moveLeftExpansion X L evaluation p front i x,
      FinitePlacedPacketDescent X L evaluation q.2 p := by
  classical
  intro q hq
  simp only [moveLeftExpansion, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_singleton] at hq
  rcases hq with hmain | hhigh
  · rcases hmain with hprincipal | hq
    · rcases hprincipal with rfl
      have hinv0 := finiteFactorInversionCount_swap X front p.right x
        (lowRelationSmithHead X L evaluation i) hx
      have hinv : finiteFactorInversionCount X
          (front ++ lowRelationSmithHead X L evaluation i :: x :: p.right) <
        finiteFactorInversionCount X
          (p.left ++ lowRelationSmithHead X L evaluation i :: p.right) := by
        rw [hleft]
        simpa only [List.append_assoc, List.singleton_append] using
          (show finiteFactorInversionCount X
                (front ++ lowRelationSmithHead X L evaluation i :: x :: p.right) <
              finiteFactorInversionCount X
                (front ++ x :: lowRelationSmithHead X L evaluation i :: p.right) by
            omega)
      simpa [FiniteSmithPlacedPacket.moveLeftAcross,
        FiniteSmithPlacedPacket.withFactors, hrow,
        FiniteSmithPlacedPacket.withRow_eq_self] using
        finitePlacedPacketDescent_sameRow_inversions X L evaluation p i
          front (x :: p.right) p.left p.right (by simp [hleft]) hinv
    · obtain ⟨tag, htag, htagq⟩ := hq
      subst q
      unfold finsuppTaggedList at htag
      simp only [List.mem_map] at htag
      obtain ⟨j, hj, rfl⟩ := htag
      have hj' : j ∈ (lowRelationBracketRowCoefficients X L evaluation i x).support := by
        simpa using hj
      have hnonzero : lowRelationBracketRowCoefficients X L evaluation i x j ≠ 0 :=
        Finsupp.mem_support_iff.mp hj'
      have hge : lowRelationSmithRowWeight X L evaluation i +
          lowHomogeneousBasisWeight X x ≤
            lowRelationSmithRowWeight X L evaluation j := by
        apply le_of_not_gt
        intro hlt
        exact hnonzero (lowRelationBracketRowCoefficients_apply_eq_zero_of_lt
          X L evaluation i j x hlt)
      have hgt : lowRelationSmithRowWeight X L evaluation i <
          lowRelationSmithRowWeight X L evaluation j :=
        lt_of_lt_of_le (Nat.lt_add_of_pos_right
          (lowHomogeneousBasisWeight_pos X x)) hge
      simpa [FiniteSmithPlacedPacket.leftRelationCorrection, hrow,
        FiniteSmithPlacedPacket.withRow_eq_self] using
        finitePlacedPacketDescent_withRow X L evaluation p i j front p.right
          p.left p.right hgt
  · rcases hhigh with hhigh | hnil
    · rcases hhigh with rfl
      have hi : lowRelationSmithRowWeight X L evaluation i < 4 := by
        simp [FiniteSmithPlacedPacket.totalWeight,
          FiniteSmithPlacedPacket.externalWeight, hrow,
          FiniteCollectedRelation.weight, hleft] at hlow
        have hxpos := lowHomogeneousBasisWeight_pos X x
        omega
      simpa [FiniteSmithPlacedPacket.leftHighCorrection, hrow,
        FiniteSmithPlacedPacket.withRow_eq_self] using
        finitePlacedPacketDescent_withHigh X L evaluation p i
          (lowRelationBracketWeightFiveRemainder X L evaluation i x)
          (lowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
          front p.right p.left p.right hi
    · simp at hnil

theorem moveRightExpansion_decreases
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation) (x : Factor)
    (tail : List Factor)
    (hrow : p.relation = .row i)
    (hright : p.right = x :: tail)
    (hx : x < lowRelationSmithHead X L evaluation i)
    (hlow : p.totalWeight X < 5) :
    ∀ q ∈ moveRightExpansion X L evaluation p i x tail,
      FinitePlacedPacketDescent X L evaluation q.2 p := by
  classical
  intro q hq
  simp only [moveRightExpansion, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_singleton] at hq
  rcases hq with hmain | hhigh
  · rcases hmain with hprincipal | hq
    · rcases hprincipal with rfl
      have hinv0 := finiteFactorInversionCount_swap X p.left tail
        (lowRelationSmithHead X L evaluation i) x hx
      have hinv : finiteFactorInversionCount X
          ((p.left ++ [x]) ++ lowRelationSmithHead X L evaluation i :: tail) <
        finiteFactorInversionCount X
          (p.left ++ lowRelationSmithHead X L evaluation i :: p.right) := by
        rw [hright]
        simpa only [List.append_assoc, List.singleton_append] using
          (show finiteFactorInversionCount X
                (p.left ++ x :: lowRelationSmithHead X L evaluation i :: tail) <
              finiteFactorInversionCount X
                (p.left ++ lowRelationSmithHead X L evaluation i :: x :: tail) by
            omega)
      simpa [FiniteSmithPlacedPacket.moveRightAcross,
        FiniteSmithPlacedPacket.withFactors, hrow,
        FiniteSmithPlacedPacket.withRow_eq_self] using
        finitePlacedPacketDescent_sameRow_inversions X L evaluation p i
          (p.left ++ [x]) tail p.left p.right (by simp [hright]) hinv
    · unfold finsuppTaggedList at hq
      simp only [List.mem_map] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      have hj' : j ∈ (lowRelationBracketRowCoefficients X L evaluation i x).support := by
        simpa using hj
      have hnonzero : lowRelationBracketRowCoefficients X L evaluation i x j ≠ 0 :=
        Finsupp.mem_support_iff.mp hj'
      have hge : lowRelationSmithRowWeight X L evaluation i +
          lowHomogeneousBasisWeight X x ≤
            lowRelationSmithRowWeight X L evaluation j := by
        apply le_of_not_gt
        intro hlt
        exact hnonzero (lowRelationBracketRowCoefficients_apply_eq_zero_of_lt
          X L evaluation i j x hlt)
      have hgt : lowRelationSmithRowWeight X L evaluation i <
          lowRelationSmithRowWeight X L evaluation j :=
        lt_of_lt_of_le (Nat.lt_add_of_pos_right
          (lowHomogeneousBasisWeight_pos X x)) hge
      simpa [FiniteSmithPlacedPacket.rightRelationCorrection, hrow,
        FiniteSmithPlacedPacket.withRow_eq_self] using
        finitePlacedPacketDescent_withRow X L evaluation p i j p.left tail
          p.left p.right hgt
  · rcases hhigh with hhigh | hnil
    · rcases hhigh with rfl
      have hi : lowRelationSmithRowWeight X L evaluation i < 4 := by
        simp [FiniteSmithPlacedPacket.totalWeight,
          FiniteSmithPlacedPacket.externalWeight, hrow,
          FiniteCollectedRelation.weight, hright] at hlow
        have hxpos := lowHomogeneousBasisWeight_pos X x
        omega
      simpa [FiniteSmithPlacedPacket.rightHighCorrection, hrow,
        FiniteSmithPlacedPacket.withRow_eq_self] using
        finitePlacedPacketDescent_withHigh X L evaluation p i
          (lowRelationBracketWeightFiveRemainder X L evaluation i x)
          (lowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
          p.left tail p.left p.right hi
    · simp at hnil

theorem finitePlacedPacketExpansion_decreases
    (evaluation : LieHom ℤ F L)
    {p : FiniteSmithPlacedPacket X L evaluation}
    {qs : List (ℤ × FiniteSmithPlacedPacket X L evaluation)}
    (h : finitePlacedPacketExpansion X L evaluation p = some qs) :
    ∀ q ∈ qs, FinitePlacedPacketDescent X L evaluation q.2 p := by
  classical
  unfold finitePlacedPacketExpansion at h
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
          exact leftSwapExpansion_decreases X L evaluation p i d hrow
            (chooseAdjacentInversion?_eq_some_realizes hchosen) hw
        · contradiction
      · rename_i hleftNone
        split at h
        · rename_i front x hlast
          split at h
          · rename_i hx
            simp only [Option.some.injEq] at h
            subst qs
            exact moveLeftExpansion_decreases X L evaluation p front i x hrow
              (splitLast?_eq_some hlast) hx hlow
          · rename_i hnx
            split at h
            · contradiction
            · rename_i y tail hright
              split at h
              · rename_i hy
                simp only [Option.some.injEq] at h
                subst qs
                exact moveRightExpansion_decreases X L evaluation p i y tail hrow
                  hright hy hlow
              · rename_i hny
                split at h
                · rename_i d hchosenRight
                  split at h
                  · rename_i hw
                    simp only [Option.some.injEq] at h
                    subst qs
                    exact rightSwapExpansion_decreases X L evaluation p i d hrow
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
              exact moveRightExpansion_decreases X L evaluation p i y tail hrow
                hright hy hlow
            · rename_i hny
              split at h
              · rename_i d hchosenRight
                split at h
                · rename_i hw
                  simp only [Option.some.injEq] at h
                  subst qs
                  exact rightSwapExpansion_decreases X L evaluation p i d hrow
                    (chooseAdjacentInversion?_eq_some_realizes hchosenRight) hw
                · contradiction
              · contradiction
  · contradiction

/-- The exact finite placed collector. -/
def finitePlacedPacketCollector
    (evaluation : LieHom ℤ F L) :
    FiniteTaggedCollector
      (FiniteSmithPlacedPacket X L evaluation) (UEA ℤ F) where
  relation := FinitePlacedPacketDescent X L evaluation
  wellFounded := finitePlacedPacketDescent_wellFounded X L evaluation
  expansion := finitePlacedPacketExpansion X L evaluation
  value := FiniteSmithPlacedPacket.value X L evaluation
  decreases := finitePlacedPacketExpansion_decreases X L evaluation
  preserves := finitePlacedPacketExpansion_preserves X L evaluation

theorem finitePlacedPacketCollector_evaluate_normalForm
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) :
    (finitePlacedPacketCollector X L evaluation).evaluate
        ((finitePlacedPacketCollector X L evaluation).normalForm p) =
      p.value X L evaluation :=
  (finitePlacedPacketCollector X L evaluation).evaluate_normalForm p

/-! ## Shape of terminal low packets -/

/-- In a packet of total weight below five, every adjacent pair of external factors has
combined weight at most four.  This is the small numerical observation which ensures that
none of the ordinary PBW swaps can become stuck at the truncation boundary. -/
theorem adjacent_external_weight_le_four
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor)
    (hd : d.Realizes p.left)
    (hlow : p.totalWeight X < 5) :
    lowHomogeneousBasisWeight X d.x +
        lowHomogeneousBasisWeight X d.y ≤ 4 := by
  have hrel := p.relation.weight_pos X L evaluation
  simp only [FiniteSmithPlacedPacket.totalWeight,
    FiniteSmithPlacedPacket.externalWeight, hd.1, List.map_append,
    List.map_cons, List.sum_append, List.sum_cons] at hlow
  omega

theorem adjacent_external_weight_le_four_right
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor)
    (hd : d.Realizes p.right)
    (hlow : p.totalWeight X < 5) :
    lowHomogeneousBasisWeight X d.x +
        lowHomogeneousBasisWeight X d.y ≤ 4 := by
  have hrel := p.relation.weight_pos X L evaluation
  simp only [FiniteSmithPlacedPacket.totalWeight,
    FiniteSmithPlacedPacket.externalWeight, hd.1, List.map_append,
    List.map_cons, List.sum_append, List.sum_cons] at hlow
  omega

end

end DegreeFive

end LieRings
