import LieRings.DimensionSubring.DegreeFive.FilteredPackets

/-!
# Semantic packets and the actual PBW correction

The numerical packet measure is connected here to packets carrying genuine free-Lie factors.
The adjacent swap is proved simultaneously at the algebra level and at the filtration level:
the principal word loses one inversion, while the bracket correction has one fewer factor and
its certified weight is the sum of the two input weights.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

local notation "F" => CanonicalFreeLie L
local notation "Rel" => CanonicalLieRelationsIdeal L
local notation "Factor" => FilteredLieFactor L

/-- The inversion count needed here, stated without the extraneous additive-group parameter of
the original Higgins collector. -/
def factorInversionCount [LinearOrder Factor] : List Factor → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + factorInversionCount xs

/-- An inverted adjacent swap removes exactly one semantic-factor inversion. -/
theorem factorInversionCount_swap [LinearOrder Factor]
    (left right : List Factor) (x y : Factor) (hxy : y < x) :
    factorInversionCount L (left ++ x :: y :: right) =
      factorInversionCount L (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnx : ¬x < y := not_lt_of_ge (le_of_lt hxy)
      simp [factorInversionCount, hxy, hnx, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, factorInversionCount]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp <;> omega
      rw [hfilter, ih]
      omega

/-- A relation packet with semantic minimum-weight proofs on the relation and every factor. -/
structure FilteredRelationPacket where
  relation : Rel
  relationWeight : ℕ
  relationWeight_pos : 0 < relationWeight
  relation_filtered : (relation : F) ∈
    FreeLieDimension.lieHigh L relationWeight
  factors : List Factor

namespace FilteredRelationPacket

/-- Forget the filtration proofs, retaining the marked algebra packet. -/
def toAlgebraPacket (p : FilteredRelationPacket L) : AlgebraPacket ℤ F Rel :=
  ⟨[], p.relation, filteredFactorValues L p.factors⟩

/-- Evaluation in the free enveloping algebra. -/
def value (p : FilteredRelationPacket L) : UEA ℤ F :=
  AlgebraPacket.value ℤ F Rel p.toAlgebraPacket

/-- External weights of a semantic packet. -/
def externalWeights (p : FilteredRelationPacket L) : List ℕ :=
  filteredFactorWeights L p.factors

/-- Inversion count in the fixed weight-first PBW order. -/
def inversions (p : FilteredRelationPacket L) : ℕ :=
  letI : LinearOrder Factor := filteredFactorLinearOrder L
  factorInversionCount L p.factors

/-- The underlying numerical packet used by the termination proof. -/
def weightedPacket (p : FilteredRelationPacket L) : WeightedPacket :=
  ⟨p.relationWeight, p.externalWeights, p.inversions⟩

/-- Initial generator-word packets have relation weight one and all external weights one. -/
def initial (p : Rel × UEA ℤ F) (word : FreeMonoid L) :
    FilteredRelationPacket L where
  relation := p.1
  relationWeight := 1
  relationWeight_pos := by omega
  relation_filtered := by
    rw [FreeLieDimension.lieHigh_one]
    trivial
  factors := (FreeMonoid.toList word).map (FilteredLieFactor.generator L)

@[simp]
theorem initial_externalWeights (p : Rel × UEA ℤ F) (word : FreeMonoid L) :
    (initial L p word).externalWeights =
      (FreeMonoid.toList word).map (fun _ ↦ 1) := by
  simp [initial, externalWeights]

/-- Initial semantic evaluation is the initial marked packet evaluation already used by the
finite ledger. -/
theorem initial_value (p : Rel × UEA ℤ F) (word : FreeMonoid L) :
    (initial L p word).value =
      AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word) := by
  simp [value, toAlgebraPacket, initial, initialAlgebraPacket,
    filteredFactorValues, Function.comp_def]

/-- A chosen low row, ready to be frozen by the placed collector. -/
def row (p : FilteredRelationPacket L) : FilteredRelationPacket L where
  relation := relationIdealRow L p.relation
  relationWeight := 1
  relationWeight_pos := by omega
  relation_filtered := by
    rw [FreeLieDimension.lieHigh_one]
    trivial
  factors := p.factors

/-- The row remainder is a packet whose relation has certified minimum weight three. -/
def rowRemainder (p : FilteredRelationPacket L) : FilteredRelationPacket L where
  relation := relationRowRemainder L p.relation
  relationWeight := 3
  relationWeight_pos := by omega
  relation_filtered := by
    rw [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 2]
    exact relationRowRemainder_mem_lowerCentralSeries_two L p.relation
  factors := p.factors

/-- Semantic form of the exact row preprocessing step.  The row branch is frozen rather than
recursively normalized; only the weight-three remainder enters recursive collection. -/
theorem value_eq_row_add_rowRemainder (p : FilteredRelationPacket L) :
    p.value = p.row.value + p.rowRemainder.value := by
  simpa [value, toAlgebraPacket, row, rowRemainder,
    AlgebraPacket.row, AlgebraPacket.rowRemainder] using
      AlgebraPacket.value_eq_row_add_rowRemainder
        (L := L) p.toAlgebraPacket

/-- Build a packet from already-certified relation data and a factor list. -/
def withFactors (r : Rel) (s : ℕ) (hs : 0 < s)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh L s)
    (factors : List Factor) : FilteredRelationPacket L :=
  ⟨r, s, hs, hr, factors⟩

/-- Exact algebra identity for swapping two adjacent semantic factors. -/
theorem adjacent_swap_value
    (r : Rel) (s : ℕ) (hs : 0 < s)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh L s)
    (left right : List Factor) (x y : Factor) :
    (withFactors L r s hs hr (left ++ x :: y :: right)).value =
      (withFactors L r s hs hr (left ++ y :: x :: right)).value +
        (withFactors L r s hs hr
          (left ++ FilteredLieFactor.bracket L x y :: right)).value := by
  simpa [value, toAlgebraPacket, withFactors, filteredFactorValues,
    List.map_append, Function.comp_def] using
      AlgebraPacket.swap_right_value ℤ F Rel []
        (filteredFactorValues L left) (filteredFactorValues L right)
        x.value y.value r

/-- The bracket-correction semantic packet follows the proved shorter-factor branch of the
full numerical termination relation. -/
theorem bracketCorrection_weightedStep
    (r : Rel) (s : ℕ) (hs : 0 < s)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh L s)
    (left right : List Factor) (x y : Factor) :
    WeightedPacketStep
      (withFactors L r s hs hr
        (left ++ FilteredLieFactor.bracket L x y :: right)).weightedPacket
      (withFactors L r s hs hr (left ++ x :: y :: right)).weightedPacket := by
  letI : LinearOrder Factor := filteredFactorLinearOrder L
  unfold weightedPacket externalWeights inversions
  simp only [withFactors, filteredFactorWeights, List.map_append, List.map_cons,
    FilteredLieFactor.bracket_weight]
  exact WeightedPacketStep.bracketCorrection s x.weight y.weight
    (filteredFactorWeights L left) (filteredFactorWeights L right)
    (factorInversionCount L (left ++ x :: y :: right))
    (factorInversionCount L
      (left ++ FilteredLieFactor.bracket L x y :: right))

/-- In the fixed weight-first PBW order, the ordered branch of a semantic adjacent swap loses
exactly one inversion and hence follows the final branch of `WeightedPacketStep`. -/
theorem orderedSwap_weightedStep
    (r : Rel) (s : ℕ) (hs : 0 < s)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh L s)
    (left right : List Factor) (x y : Factor)
    (hxy : letI : LinearOrder Factor := filteredFactorLinearOrder L; y < x) :
    WeightedPacketStep
      (withFactors L r s hs hr (left ++ y :: x :: right)).weightedPacket
      (withFactors L r s hs hr (left ++ x :: y :: right)).weightedPacket := by
  letI : LinearOrder Factor := filteredFactorLinearOrder L
  have hinv := factorInversionCount_swap L left right x y hxy
  unfold weightedPacket externalWeights inversions
  simp only [withFactors, filteredFactorWeights, List.map_append, List.map_cons]
  rw [hinv]
  exact WeightedPacketStep.swap s x.weight y.weight
    (filteredFactorWeights L left) (filteredFactorWeights L right)
    (factorInversionCount L (left ++ y :: x :: right))

end FilteredRelationPacket

end

end DegreeFive

end LieRings
