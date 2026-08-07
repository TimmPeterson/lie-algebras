import LieRings.DimensionSubring.DegreeFive.SemanticPackets

/-!
# The terminating semantic PBW collector

This file turns the semantic adjacent-swap identities into the finite tagged collector used by
the degree-five argument.  A rewrite retains the actual relation and actual free-Lie factors:
an inverted pair is replaced by its ordered pair and by the bracket correction.  Both outputs
strictly descend in the already-proved placed-packet measure.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

local notation "Packet" => FilteredRelationPacket L
local notation "Factor" => FilteredLieFactor L

variable {α : Type u}

/-- Data locating one inverted adjacent pair in a list. -/
structure AdjacentInversionData (α : Type u) where
  left : List α
  x : α
  y : α
  right : List α

/-- The data really locate an inverted adjacent pair in `xs`. -/
def AdjacentInversionData.Realizes [LT α]
    (d : AdjacentInversionData α) (xs : List α) : Prop :=
  xs = d.left ++ d.x :: d.y :: d.right ∧ d.y < d.x

/-- Choose one adjacent inversion when one exists.  No computational choice of a basis is
needed; the collector only needs a fixed choice to define its normal form. -/
noncomputable def chooseAdjacentInversion? [LinearOrder α]
    (xs : List α) : Option (AdjacentInversionData α) := by
  classical
  exact if h : ∃ d : AdjacentInversionData α,
      AdjacentInversionData.Realizes d xs then
    some (Classical.choose h) else none

theorem chooseAdjacentInversion?_eq_some_realizes [LinearOrder α]
    {xs : List α} {d : AdjacentInversionData α}
    (h : chooseAdjacentInversion? xs = some d) : d.Realizes xs := by
  unfold chooseAdjacentInversion? at h
  split at h
  · rename_i hexists
    have hd := Classical.choose_spec hexists
    have heq : Classical.choose hexists = d := Option.some.inj h
    simpa [← heq] using hd
  · contradiction

theorem chooseAdjacentInversion?_eq_none_iff [LinearOrder α]
    (xs : List α) :
    chooseAdjacentInversion? xs = none ↔
      ¬∃ d : AdjacentInversionData α, d.Realizes xs := by
  classical
  unfold chooseAdjacentInversion?
  split
  · rename_i hexists
    constructor
    · intro hbad
      contradiction
    · intro hnot
      exact (hnot hexists).elim
  · simp_all

/-- A list with no inverted adjacent pair is globally nondecreasing. -/
theorem pairwise_le_of_no_adjacent_inversion [LinearOrder α]
    (xs : List α)
    (h : ¬∃ d : AdjacentInversionData α, d.Realizes xs) :
    xs.Pairwise (· ≤ ·) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ¬∃ d : AdjacentInversionData α, d.Realizes xs := by
        rintro ⟨d, hd, hlt⟩
        apply h
        exact ⟨⟨x :: d.left, d.x, d.y, d.right⟩, by
          simp only [AdjacentInversionData.Realizes, List.cons_append]
          exact ⟨congrArg (x :: ·) hd, hlt⟩⟩
      have ih' := ih htail
      rw [List.pairwise_cons]
      refine ⟨?_, ih'⟩
      intro y hy
      cases xs with
      | nil => simp at hy
      | cons z zs =>
          have hxz : x ≤ z := by
            apply not_lt.mp
            intro hzx
            apply h
            exact ⟨⟨[], x, z, zs⟩, by simp [AdjacentInversionData.Realizes, hzx]⟩
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hxz
          · exact hxz.trans ((List.pairwise_cons.mp ih').1 y hy)

/-- Conversely, a nondecreasing list contains no inverted adjacent pair. -/
theorem no_adjacent_inversion_of_pairwise_le [LinearOrder α]
    {xs : List α} (h : xs.Pairwise (· ≤ ·)) :
    ¬∃ d : AdjacentInversionData α, d.Realizes xs := by
  rintro ⟨d, hd, hlt⟩
  rw [hd] at h
  have hxy : d.x ≤ d.y := by
    simp only [List.pairwise_append, List.pairwise_cons] at h
    exact h.2.1.1 d.y (by simp)
  exact (not_lt_of_ge hxy) hlt

theorem chooseAdjacentInversion?_eq_none_iff_pairwise [LinearOrder α]
    (xs : List α) :
    chooseAdjacentInversion? xs = none ↔ xs.Pairwise (· ≤ ·) := by
  rw [chooseAdjacentInversion?_eq_none_iff]
  exact ⟨pairwise_le_of_no_adjacent_inversion xs,
    no_adjacent_inversion_of_pairwise_le⟩

/-- Replace the factors of a packet without changing its certified relation. -/
def FilteredRelationPacket.replaceFactors
    (p : Packet) (factors : List Factor) : Packet :=
  FilteredRelationPacket.withFactors L p.relation p.relationWeight
    p.relationWeight_pos p.relation_filtered factors

/-- One deterministic PBW expansion. -/
def semanticPacketExpansion (p : Packet) : Option (List (ℤ × Packet)) :=
  letI : LinearOrder Factor := filteredFactorLinearOrder L
  match chooseAdjacentInversion? p.factors with
  | none => none
  | some d => some
      [(1, FilteredRelationPacket.replaceFactors L p
          (d.left ++ d.y :: d.x :: d.right)),
       (1, FilteredRelationPacket.replaceFactors L p
          (d.left ++ FilteredLieFactor.bracket L d.x d.y :: d.right))]

/-- Terminal semantic packets are exactly the packets with PBW-ordered factor lists. -/
theorem semanticPacketExpansion_eq_none_iff (p : Packet) :
    semanticPacketExpansion L p = none ↔
      letI : LinearOrder Factor := filteredFactorLinearOrder L
      p.factors.Pairwise (· ≤ ·) := by
  letI : LinearOrder Factor := filteredFactorLinearOrder L
  unfold semanticPacketExpansion
  split
  · rename_i hnone
    exact ⟨fun _ ↦ (chooseAdjacentInversion?_eq_none_iff_pairwise
      p.factors).mp hnone, fun _ ↦ rfl⟩
  · rename_i d hsome
    constructor
    · intro h
      contradiction
    · intro hordered
      have hnone := (chooseAdjacentInversion?_eq_none_iff_pairwise
        p.factors).mpr hordered
      rw [hsome] at hnone
      contradiction

/-- The weight-first order really makes terminal external weights nondecreasing. -/
theorem filteredFactor_weight_mono
    (x y : Factor)
    (hxy : letI : LinearOrder Factor := filteredFactorLinearOrder L; x ≤ y) :
    x.weight ≤ y.weight := by
  letI : LinearOrder Factor := filteredFactorLinearOrder L
  by_contra hweight
  have hyx : y < x := by
    change filteredFactorLT L y x
    exact Prod.Lex.left y x (Nat.lt_of_not_ge hweight)
  exact (not_lt_of_ge hxy) hyx

/-- Hence every terminal packet satisfies the numerical PBW ordering condition. -/
theorem externalWeights_pairwise_of_expansion_eq_none
    (p : Packet) (hp : semanticPacketExpansion L p = none) :
    p.externalWeights.Pairwise (· ≤ ·) := by
  letI : LinearOrder Factor := filteredFactorLinearOrder L
  have hordered := (semanticPacketExpansion_eq_none_iff L p).mp hp
  unfold FilteredRelationPacket.externalWeights filteredFactorWeights
  rw [List.pairwise_map]
  exact hordered.imp (fun {x y} h ↦ filteredFactor_weight_mono L x y h)

/-- A semantic collector output is smaller when its numerical placed packet is smaller. -/
def SemanticPacketDescent (new old : Packet) : Prop :=
  WeightedPacketStep new.weightedPacket old.weightedPacket

theorem semanticPacketDescent_wellFounded :
    WellFounded (SemanticPacketDescent L) :=
  InvImage.wf (FilteredRelationPacket.weightedPacket L)
    weightedPacketStep_wellFounded

/-- Every output of `semanticPacketExpansion` strictly descends. -/
theorem semanticPacketExpansion_decreases
    {p : Packet} {qs : List (ℤ × Packet)}
    (hexpand : semanticPacketExpansion L p = some qs) :
    ∀ q ∈ qs, SemanticPacketDescent L q.2 p := by
  letI : LinearOrder Factor := filteredFactorLinearOrder L
  unfold semanticPacketExpansion at hexpand
  split at hexpand
  · contradiction
  · rename_i d hchosen
    have hd := chooseAdjacentInversion?_eq_some_realizes hchosen
    rcases hd with ⟨hfactor, hlt⟩
    simp only [Option.some.injEq] at hexpand
    subst qs
    have hp : p = FilteredRelationPacket.withFactors L p.relation
        p.relationWeight p.relationWeight_pos p.relation_filtered p.factors := by
      cases p
      rfl
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · rw [hp, hfactor]
      simpa [SemanticPacketDescent, FilteredRelationPacket.replaceFactors] using
        (FilteredRelationPacket.orderedSwap_weightedStep L
          p.relation p.relationWeight p.relationWeight_pos
          p.relation_filtered d.left d.right d.x d.y hlt)
    · rcases hq with rfl | hq
      · rw [hp, hfactor]
        simpa [SemanticPacketDescent, FilteredRelationPacket.replaceFactors] using
          (FilteredRelationPacket.bracketCorrection_weightedStep L
            p.relation p.relationWeight p.relationWeight_pos
            p.relation_filtered d.left d.right d.x d.y)
      · simp at hq

/-- One semantic expansion preserves the exact enveloping-algebra value. -/
theorem semanticPacketExpansion_preserves
    {p : Packet} {qs : List (ℤ × Packet)}
    (hexpand : semanticPacketExpansion L p = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value).sum = p.value := by
  letI : LinearOrder Factor := filteredFactorLinearOrder L
  unfold semanticPacketExpansion at hexpand
  split at hexpand
  · contradiction
  · rename_i d hchosen
    have hd := chooseAdjacentInversion?_eq_some_realizes hchosen
    rcases hd with ⟨hfactor, hlt⟩
    simp only [Option.some.injEq] at hexpand
    subst qs
    have hp : p = FilteredRelationPacket.withFactors L p.relation
        p.relationWeight p.relationWeight_pos p.relation_filtered p.factors := by
      cases p
      rfl
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, one_zsmul]
    rw [hp, hfactor]
    simpa [FilteredRelationPacket.replaceFactors] using
      (FilteredRelationPacket.adjacent_swap_value L
        p.relation p.relationWeight p.relationWeight_pos
        p.relation_filtered d.left d.right d.x d.y).symm

/-- The genuine finite PBW collector on relation packets. -/
def semanticPacketCollector :
    FiniteTaggedCollector Packet (UEA ℤ (CanonicalFreeLie L)) where
  relation := SemanticPacketDescent L
  wellFounded := semanticPacketDescent_wellFounded L
  expansion := semanticPacketExpansion L
  value := FilteredRelationPacket.value L
  decreases := semanticPacketExpansion_decreases L
  preserves := semanticPacketExpansion_preserves L

/-- Collection preserves the exact value of every semantic packet. -/
theorem semanticPacketCollector_evaluate_normalForm (p : Packet) :
    (semanticPacketCollector L).evaluate
        ((semanticPacketCollector L).normalForm p) = p.value :=
  (semanticPacketCollector L).evaluate_normalForm p

/-- Every packet actually occurring in a semantic normal form is PBW-ordered. -/
theorem externalWeights_pairwise_of_mem_normalForm_support
    (p q : Packet)
    (hq : q ∈ ((semanticPacketCollector L).normalForm p).support) :
    q.externalWeights.Pairwise (· ≤ ·) := by
  apply externalWeights_pairwise_of_expansion_eq_none L q
  exact (semanticPacketCollector L).expansion_eq_none_of_mem_normalForm_support hq

/-- A surviving packet below total weight five satisfies the exact numerical packet predicate. -/
theorem isLowPacketWeightSequence_of_mem_normalForm_support
    (p q : Packet)
    (hq : q ∈ ((semanticPacketCollector L).normalForm p).support)
    (hlow : q.relationWeight + q.externalWeights.sum < 5) :
    IsLowPacketWeightSequence q.relationWeight q.externalWeights := by
  refine ⟨externalWeights_pairwise_of_mem_normalForm_support L p q hq, ?_, hlow⟩
  intro n hn
  unfold FilteredRelationPacket.externalWeights filteredFactorWeights at hn
  simp only [List.mem_map] at hn
  obtain ⟨x, hx, rfl⟩ := hn
  exact x.weight_pos

/-- Therefore the previously proved finite source table exhausts every surviving low packet. -/
theorem normalForm_low_packet_table
    (p q : Packet)
    (hq : q ∈ ((semanticPacketCollector L).normalForm p).support)
    (hlow : q.relationWeight + q.externalWeights.sum < 5) :
    (q.relationWeight = 1 ∧
      (q.externalWeights = [] ∨ q.externalWeights = [1] ∨
        q.externalWeights = [2] ∨ q.externalWeights = [1, 1] ∨
        q.externalWeights = [3] ∨ q.externalWeights = [1, 2] ∨
        q.externalWeights = [1, 1, 1])) ∨
    (q.relationWeight = 2 ∧
      (q.externalWeights = [] ∨ q.externalWeights = [1] ∨
        q.externalWeights = [2] ∨ q.externalWeights = [1, 1])) ∨
    (q.relationWeight = 3 ∧
      (q.externalWeights = [] ∨ q.externalWeights = [1])) ∨
    (q.relationWeight = 4 ∧ q.externalWeights = []) := by
  exact lowPacketWeightSequence_complete q.relationWeight_pos
    (isLowPacketWeightSequence_of_mem_normalForm_support L p q hq hlow)

/-- First split an arbitrary defining relation into its chosen class-two row and its
weight-three remainder, then PBW-collect both branches. -/
def preprocessedSemanticNormalForm (p : Packet) : Packet →₀ ℤ :=
  (semanticPacketCollector L).normalForm p.row +
    (semanticPacketCollector L).normalForm p.rowRemainder

/-- Row preprocessing and semantic collection preserve the marked packet exactly. -/
theorem evaluate_preprocessedSemanticNormalForm (p : Packet) :
    (semanticPacketCollector L).evaluate
        (preprocessedSemanticNormalForm L p) = p.value := by
  rw [preprocessedSemanticNormalForm, map_add,
    semanticPacketCollector_evaluate_normalForm,
    semanticPacketCollector_evaluate_normalForm]
  exact p.value_eq_row_add_rowRemainder.symm

/-- The finite normal form obtained from every initial generator-word packet in a ledger. -/
def FinitePlacedRelationLedger.semanticNormalForm
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) : Packet →₀ ℤ :=
  ledger.lowWeight.coefficients.sum (fun p n ↦ n •
    (placedWordCoefficients p).sum (fun word m ↦ m •
      preprocessedSemanticNormalForm L
        (FilteredRelationPacket.initial L p word)))

/-- The collected semantic ledger has exactly the original relation-side value. -/
theorem FinitePlacedRelationLedger.evaluate_semanticNormalForm
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    (semanticPacketCollector L).evaluate ledger.semanticNormalForm =
      ledger.initialPacketValue := by
  unfold FinitePlacedRelationLedger.semanticNormalForm
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_smul, map_finsuppSum]
  congr 1
  apply Finsupp.sum_congr
  intro word hword
  rw [map_smul, evaluate_preprocessedSemanticNormalForm]
  exact congrArg (fun z ↦ (placedWordCoefficients p) word • z)
    (FilteredRelationPacket.initial_value L p word)

/-- Thus the collected semantic ledger is the original fifth-dimension relation difference. -/
theorem FinitePlacedRelationLedger.evaluate_semanticNormalForm_eq_relationDifference
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    (semanticPacketCollector L).evaluate ledger.semanticNormalForm =
      UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord := by
  rw [ledger.evaluate_semanticNormalForm,
    ledger.initialPacketValue_eq_relationDifference]

end

end DegreeFive

end LieRings
