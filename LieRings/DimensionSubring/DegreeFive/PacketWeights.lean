import Mathlib.Data.List.Sort
import Mathlib.Order.RelClasses
import Mathlib.Tactic

/-!
# The finite packet table below weight five

The placed PBW collector attaches to a relation row of least weight `s` the nondecreasing list
of weights of its external PBW factors.  This file proves, rather than assumes, the exhaustive
table of possibilities whose total weight is below five.
-/

namespace LieRings

namespace DegreeFive

/-- A legal external-factor weight sequence for a relation row of least weight `s`. -/
def IsLowPacketWeightSequence (s : ℕ) (ws : List ℕ) : Prop :=
  ws.Pairwise (· ≤ ·) ∧
    (∀ w ∈ ws, 0 < w) ∧
    s + ws.sum < 5

theorem length_le_sum_of_forall_pos {ws : List ℕ}
    (hpos : ∀ w ∈ ws, 0 < w) : ws.length ≤ ws.sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      have hw : 1 ≤ w := hpos w (by simp)
      have htail : ∀ x ∈ ws, 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      have hi := ih htail
      simp only [List.length_cons, List.sum_cons]
      omega

/-- The source table for a least-weight-one relation row. -/
theorem lowPacketWeightSequence_one_iff (ws : List ℕ) :
    IsLowPacketWeightSequence 1 ws ↔
      ws = [] ∨ ws = [1] ∨ ws = [2] ∨ ws = [1, 1] ∨
        ws = [3] ∨ ws = [1, 2] ∨ ws = [1, 1, 1] := by
  constructor
  · rintro ⟨hsorted, hpos, hweight⟩
    have hlen : ws.length ≤ ws.sum := length_le_sum_of_forall_pos hpos
    have hsum : ws.sum ≤ 3 := by omega
    have hlength : ws.length ≤ 3 := hlen.trans hsum
    cases ws with
    | nil => exact Or.inl rfl
    | cons a ws =>
        cases ws with
        | nil =>
            have ha : 0 < a := hpos a (by simp)
            simp only [List.sum_cons, List.sum_nil, add_zero] at hweight
            have ha' : a = 1 ∨ a = 2 ∨ a = 3 := by omega
            rcases ha' with rfl | rfl | rfl <;> simp
        | cons b ws =>
            cases ws with
            | nil =>
                have ha : 0 < a := hpos a (by simp)
                have hb : 0 < b := hpos b (by simp)
                have hab : a ≤ b := by simpa using hsorted
                simp only [List.sum_cons, List.sum_nil, add_zero] at hweight
                have hab' : (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) := by omega
                rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
            | cons c ws =>
                cases ws with
                | nil =>
                    have ha : 0 < a := hpos a (by simp)
                    have hb : 0 < b := hpos b (by simp)
                    have hc : 0 < c := hpos c (by simp)
                    simp only [List.sum_cons, List.sum_nil, add_zero] at hweight
                    have habc : a = 1 ∧ b = 1 ∧ c = 1 := by omega
                    rcases habc with ⟨rfl, rfl, rfl⟩
                    simp
                | cons d ws =>
                    simp at hlength
                    omega
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [IsLowPacketWeightSequence]

/-- The source table for a least-weight-two relation row. -/
theorem lowPacketWeightSequence_two_iff (ws : List ℕ) :
    IsLowPacketWeightSequence 2 ws ↔
      ws = [] ∨ ws = [1] ∨ ws = [2] ∨ ws = [1, 1] := by
  constructor
  · rintro ⟨hsorted, hpos, hweight⟩
    have hlen : ws.length ≤ ws.sum := length_le_sum_of_forall_pos hpos
    have hsum : ws.sum ≤ 2 := by omega
    have hlength : ws.length ≤ 2 := hlen.trans hsum
    cases ws with
    | nil => exact Or.inl rfl
    | cons a ws =>
        cases ws with
        | nil =>
            have ha : 0 < a := hpos a (by simp)
            simp only [List.sum_cons, List.sum_nil, add_zero] at hweight
            have ha' : a = 1 ∨ a = 2 := by omega
            rcases ha' with rfl | rfl <;> simp
        | cons b ws =>
            cases ws with
            | nil =>
                have ha : 0 < a := hpos a (by simp)
                have hb : 0 < b := hpos b (by simp)
                simp only [List.sum_cons, List.sum_nil, add_zero] at hweight
                have hab : a = 1 ∧ b = 1 := by omega
                rcases hab with ⟨rfl, rfl⟩
                simp
            | cons c ws =>
                simp at hlength
  · rintro (rfl | rfl | rfl | rfl) <;>
      simp [IsLowPacketWeightSequence]

/-- The source table for a least-weight-three relation row. -/
theorem lowPacketWeightSequence_three_iff (ws : List ℕ) :
    IsLowPacketWeightSequence 3 ws ↔ ws = [] ∨ ws = [1] := by
  constructor
  · rintro ⟨hsorted, hpos, hweight⟩
    have hlen : ws.length ≤ ws.sum := length_le_sum_of_forall_pos hpos
    have hsum : ws.sum ≤ 1 := by omega
    have hlength : ws.length ≤ 1 := hlen.trans hsum
    cases ws with
    | nil => exact Or.inl rfl
    | cons a ws =>
        cases ws with
        | nil =>
            have ha : 0 < a := hpos a (by simp)
            simp only [List.sum_cons, List.sum_nil, add_zero] at hweight
            have ha' : a = 1 := by omega
            subst a
            simp
        | cons b ws =>
            simp at hlength
  · rintro (rfl | rfl) <;> simp [IsLowPacketWeightSequence]

/-- A least-weight-four relation row cannot have an external factor below total weight five. -/
theorem lowPacketWeightSequence_four_iff (ws : List ℕ) :
    IsLowPacketWeightSequence 4 ws ↔ ws = [] := by
  constructor
  · rintro ⟨hsorted, hpos, hweight⟩
    cases ws with
    | nil => rfl
    | cons a ws =>
        have ha : 0 < a := hpos a (by simp)
        simp only [List.sum_cons] at hweight
        omega
  · rintro rfl
    simp [IsLowPacketWeightSequence]

/-- Every packet below weight five occurs in one of the four proved finite rows. -/
theorem lowPacketWeightSequence_complete {s : ℕ} {ws : List ℕ}
    (hs : 0 < s) (h : IsLowPacketWeightSequence s ws) :
    (s = 1 ∧
      (ws = [] ∨ ws = [1] ∨ ws = [2] ∨ ws = [1, 1] ∨
        ws = [3] ∨ ws = [1, 2] ∨ ws = [1, 1, 1])) ∨
    (s = 2 ∧ (ws = [] ∨ ws = [1] ∨ ws = [2] ∨ ws = [1, 1])) ∨
    (s = 3 ∧ (ws = [] ∨ ws = [1])) ∨
    (s = 4 ∧ ws = []) := by
  have hslt : s < 5 := by
    exact lt_of_le_of_lt (Nat.le_add_right s ws.sum) h.2.2
  have hs_cases : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by omega
  rcases hs_cases with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, (lowPacketWeightSequence_one_iff ws).mp h⟩
  · exact Or.inr (Or.inl ⟨rfl, (lowPacketWeightSequence_two_iff ws).mp h⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨rfl, (lowPacketWeightSequence_three_iff ws).mp h⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨rfl, (lowPacketWeightSequence_four_iff ws).mp h⟩))

/-! ## Termination data for collection -/

/-- The number of inverted pairs in an external-factor weight word. -/
def packetInversionCount : List ℕ → ℕ
  | [] => 0
  | w :: ws => (ws.filter (· < w)).length + packetInversionCount ws

/-- Swapping an adjacent inverted pair removes exactly one inversion. -/
theorem packetInversionCount_swap
    (left right : List ℕ) (x y : ℕ) (hxy : y < x) :
    packetInversionCount (left ++ x :: y :: right) =
      packetInversionCount (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnx : ¬x < y := not_lt_of_ge (le_of_lt hxy)
      simp [packetInversionCount, hxy, hnx, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, packetInversionCount]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp
      rw [hfilter, ih]
      omega

/-- Lexicographic collector complexity: first the number of external factors, then their
inversion count. -/
def packetComplexity (ws : List ℕ) : ℕ × ℕ :=
  (ws.length, packetInversionCount ws)

/-- Moving a marked relation through one external factor creates a commutator packet with
strictly fewer external factors. -/
theorem packetComplexity_relationCorrection_lt
    (left right : List ℕ) (w : ℕ) :
    Prod.Lex (· < ·) (· < ·)
      (packetComplexity (left ++ right))
      (packetComplexity (left ++ w :: right)) := by
  apply Prod.Lex.left
  simp

/-- Replacing two external Lie factors by their bracket also strictly lowers collector
complexity. -/
theorem packetComplexity_bracketCorrection_lt
    (left right : List ℕ) (x y : ℕ) :
    Prod.Lex (· < ·) (· < ·)
      (packetComplexity (left ++ (x + y) :: right))
      (packetComplexity (left ++ x :: y :: right)) := by
  apply Prod.Lex.left
  simp

/-- The ordered branch of an adjacent PBW swap keeps the number of factors and strictly lowers
the inversion count. -/
theorem packetComplexity_swap_lt
    (left right : List ℕ) (x y : ℕ) (hxy : y < x) :
    Prod.Lex (· < ·) (· < ·)
      (packetComplexity (left ++ y :: x :: right))
      (packetComplexity (left ++ x :: y :: right)) := by
  unfold packetComplexity
  simp only [List.length_append, List.length_cons]
  apply Prod.Lex.right
  have hcount := packetInversionCount_swap left right x y hxy
  omega

/-- The strict complexity relation used by the collector. -/
def PacketDescent (new old : List ℕ) : Prop :=
  Prod.Lex (· < ·) (· < ·) (packetComplexity new) (packetComplexity old)

/-- Lexicographic packet descent is well founded. -/
theorem packetDescent_wellFounded : WellFounded PacketDescent := by
  exact InvImage.wf packetComplexity
    (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

/-- The three recursive branches occurring in placed PBW collection.  The arguments are ordered
as `(newPacket, oldPacket)`, as required by a well-founded recursion relation. -/
inductive PacketStep : List ℕ → List ℕ → Prop
  | relationCorrection (left right : List ℕ) (w : ℕ) :
      PacketStep (left ++ right) (left ++ w :: right)
  | bracketCorrection (left right : List ℕ) (x y : ℕ) :
      PacketStep (left ++ (x + y) :: right) (left ++ x :: y :: right)
  | swap (left right : List ℕ) (x y : ℕ) (hxy : y < x) :
      PacketStep (left ++ y :: x :: right) (left ++ x :: y :: right)

/-- Every collector branch strictly lowers lexicographic packet complexity. -/
theorem packetStep_subrelation : Subrelation PacketStep PacketDescent := by
  intro new old h
  cases h with
  | relationCorrection left right w =>
      exact packetComplexity_relationCorrection_lt left right w
  | bracketCorrection left right x y =>
      exact packetComplexity_bracketCorrection_lt left right x y
  | swap left right x y hxy =>
      exact packetComplexity_swap_lt left right x y hxy

/-- Hence the placed PBW packet collector cannot generate an infinite correction chain. -/
theorem packetStep_wellFounded : WellFounded PacketStep :=
  Subrelation.wf packetStep_subrelation packetDescent_wellFounded

/-- Packet legality before the external factors have been sorted. -/
def IsLowRawPacket (s : ℕ) (ws : List ℕ) : Prop :=
  (∀ w ∈ ws, 0 < w) ∧ s + ws.sum < 5

/-- The commutator produced by moving a relation of weight `s` past a factor of weight `w`
has relation weight `s+w`, the same total weight, and one fewer external factor. -/
theorem isLowRawPacket_relationCorrection
    (s w : ℕ) (left right : List ℕ)
    (h : IsLowRawPacket s (left ++ w :: right)) :
    IsLowRawPacket (s + w) (left ++ right) := by
  constructor
  · intro x hx
    exact h.1 x (by simp only [List.mem_append, List.mem_cons] at hx ⊢; aesop)
  · have := h.2
    simp only [List.sum_append, List.sum_cons] at this ⊢
    omega

/-- The bracket correction in an ordinary PBW swap preserves positivity and total weight while
removing one external factor. -/
theorem isLowRawPacket_bracketCorrection
    (s x y : ℕ) (left right : List ℕ)
    (h : IsLowRawPacket s (left ++ x :: y :: right)) :
    IsLowRawPacket s (left ++ (x + y) :: right) := by
  have hx : 0 < x := h.1 x (by simp)
  have hy : 0 < y := h.1 y (by simp)
  constructor
  · intro w hw
    simp only [List.mem_append, List.mem_cons] at hw
    rcases hw with hw | rfl | hw
    · exact h.1 w (by simp [hw])
    · omega
    · exact h.1 w (by simp [hw])
  · have := h.2
    simp only [List.sum_append, List.sum_cons] at this ⊢
    omega

/-- The ordered branch of an ordinary PBW swap preserves packet legality. -/
theorem isLowRawPacket_swap
    (s x y : ℕ) (left right : List ℕ)
    (h : IsLowRawPacket s (left ++ x :: y :: right)) :
    IsLowRawPacket s (left ++ y :: x :: right) := by
  constructor
  · intro w hw
    simp only [List.mem_append, List.mem_cons] at hw
    rcases hw with hw | hwy | hwx | hw
    · exact h.1 w (by simp [hw])
    · exact h.1 w (by simp [hwy])
    · exact h.1 w (by simp [hwx])
    · exact h.1 w (by simp [hw])
  · have := h.2
    simp only [List.sum_append, List.sum_cons] at this ⊢
    omega

/-! ## The full placed-collection measure -/

/-- A marked relation packet, retaining the least weight of its relation row, the weights of its
external factors, and the inversion count in the full PBW basis order.  The last field is
separate because equal-weight basis factors can still be inverted. -/
structure WeightedPacket where
  relationWeight : ℕ
  externalWeights : List ℕ
  inversions : ℕ
  deriving DecidableEq

/-- The paper's complete lexicographic measure `(4-s, r, I)`. -/
def weightedPacketComplexity (p : WeightedPacket) : ℕ × (ℕ × ℕ) :=
  (4 - p.relationWeight, (p.externalWeights.length, p.inversions))

/-- Strict descent for the complete placed collector. -/
def WeightedPacketDescent (new old : WeightedPacket) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
    (weightedPacketComplexity new) (weightedPacketComplexity old)

/-- The complete collector measure is well founded. -/
theorem weightedPacketDescent_wellFounded : WellFounded WeightedPacketDescent := by
  exact InvImage.wf weightedPacketComplexity
    (Nat.lt_wfRel.wf.prod_lex
      (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))

/-- All recursive branches of the placed collector, now including replacement of a relation-row
remainder by rows of strictly greater least weight. -/
inductive WeightedPacketStep : WeightedPacket → WeightedPacket → Prop
  | rowRemainder (s t : ℕ) (ws : List ℕ) (inv : ℕ)
      (hst : s < t) (ht : t ≤ 4) :
      WeightedPacketStep ⟨t, ws, inv⟩ ⟨s, ws, inv⟩
  | relationCorrection (s w : ℕ) (left right : List ℕ)
      (oldInv newInv : ℕ) (hw : 0 < w) (hsw : s + w ≤ 4) :
      WeightedPacketStep ⟨s + w, left ++ right, newInv⟩
        ⟨s, left ++ w :: right, oldInv⟩
  | bracketCorrection (s x y : ℕ) (left right : List ℕ)
      (oldInv newInv : ℕ) :
      WeightedPacketStep ⟨s, left ++ (x + y) :: right, newInv⟩
        ⟨s, left ++ x :: y :: right, oldInv⟩
  | swap (s x y : ℕ) (left right : List ℕ) (newInv : ℕ) :
      WeightedPacketStep ⟨s, left ++ y :: x :: right, newInv⟩
        ⟨s, left ++ x :: y :: right, newInv + 1⟩

/-- A row remainder strictly lowers the first component `4-s`. -/
theorem weightedPacketComplexity_rowRemainder_lt
    (s t : ℕ) (ws : List ℕ) (inv : ℕ) (hst : s < t) (ht : t ≤ 4) :
    WeightedPacketDescent ⟨t, ws, inv⟩ ⟨s, ws, inv⟩ := by
  apply Prod.Lex.left
  change 4 - t < 4 - s
  omega

/-- Moving a relation past a positive-weight factor raises its least weight and therefore lowers
the first component of the complete measure. -/
theorem weightedPacketComplexity_relationCorrection_lt
    (s w : ℕ) (left right : List ℕ) (oldInv newInv : ℕ)
    (hw : 0 < w) (hsw : s + w ≤ 4) :
    WeightedPacketDescent
      ⟨s + w, left ++ right, newInv⟩
        ⟨s, left ++ w :: right, oldInv⟩ := by
  apply Prod.Lex.left
  change 4 - (s + w) < 4 - s
  omega

/-- An ordinary bracket correction leaves `4-s` fixed and lowers the external-factor measure. -/
theorem weightedPacketComplexity_bracketCorrection_lt
    (s x y : ℕ) (left right : List ℕ) (oldInv newInv : ℕ) :
    WeightedPacketDescent
      ⟨s, left ++ (x + y) :: right, newInv⟩
        ⟨s, left ++ x :: y :: right, oldInv⟩ := by
  apply Prod.Lex.right
  apply Prod.Lex.left
  simp

/-- An ordered PBW swap leaves `4-s` and the number of factors fixed and removes an inversion. -/
theorem weightedPacketComplexity_swap_lt
    (s x y : ℕ) (left right : List ℕ) (newInv : ℕ) :
    WeightedPacketDescent
      ⟨s, left ++ y :: x :: right, newInv⟩
        ⟨s, left ++ x :: y :: right, newInv + 1⟩ := by
  apply Prod.Lex.right
  change Prod.Lex (· < ·) (· < ·)
    ((left ++ y :: x :: right).length, newInv)
    ((left ++ x :: y :: right).length, newInv + 1)
  simp only [List.length_append, List.length_cons]
  apply Prod.Lex.right
  omega

/-- Every branch of the full placed collector strictly descends in `(4-s,r,I)`. -/
theorem weightedPacketStep_subrelation :
    Subrelation WeightedPacketStep WeightedPacketDescent := by
  intro new old h
  cases h with
  | rowRemainder s t ws inv hst ht =>
      exact weightedPacketComplexity_rowRemainder_lt s t ws inv hst ht
  | relationCorrection s w left right oldInv newInv hw hsw =>
      exact weightedPacketComplexity_relationCorrection_lt
        s w left right oldInv newInv hw hsw
  | bracketCorrection s x y left right oldInv newInv =>
      exact weightedPacketComplexity_bracketCorrection_lt
        s x y left right oldInv newInv
  | swap s x y left right newInv =>
      exact weightedPacketComplexity_swap_lt s x y left right newInv

/-- The complete marked packet rewrite system terminates. -/
theorem weightedPacketStep_wellFounded : WellFounded WeightedPacketStep :=
  Subrelation.wf weightedPacketStep_subrelation weightedPacketDescent_wellFounded

end DegreeFive

end LieRings
