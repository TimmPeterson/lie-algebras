import LieRings.DimensionSubring.DegreeFive.PlacedLedger

/-!
# Filtered Lie factors for the placed collector

Collector factors carry both their actual free-Lie value and a proof of their minimum bracket
weight.  The bracket correction therefore adds weights by construction.  This is the semantic
counterpart of the numerical termination ledger in `PacketWeights`.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u)

local notation "F" => FreeLieAlgebra ℤ X

/-- A free-Lie element with a positive certified minimum bracket weight. -/
structure FilteredLieFactor where
  value : F
  weight : ℕ
  weight_pos : 0 < weight
  filtered : value ∈ FreeLieDimension.lieHigh X weight

/-- Weight-first PBW order, with a classical well-order used only to break ties. -/
def filteredFactorLT (x y : FilteredLieFactor X) : Prop :=
  Prod.Lex (· < ·) WellOrderingRel (x.weight, x) (y.weight, y)

instance filteredFactorLT_isStrictTotalOrder :
    IsStrictTotalOrder (FilteredLieFactor X) (filteredFactorLT X) where
  trichotomous :=
    (InvImage.trichotomous (fun _ _ h ↦ Prod.ext_iff.mp h |>.2)).trichotomous
  irrefl := fun x h ↦ by
    exact (irrefl (x.weight, x)) h
  trans := fun a b c hab hbc ↦ by
    change Prod.Lex (· < ·) WellOrderingRel
      (a.weight, a) (b.weight, b) at hab
    change Prod.Lex (· < ·) WellOrderingRel
      (b.weight, b) (c.weight, c) at hbc
    change Prod.Lex (· < ·) WellOrderingRel
      (a.weight, a) (c.weight, c)
    exact _root_.trans hab hbc

/-- A noncomputable linear order realizing `filteredFactorLT`.  Collection needs only a fixed
order, never a computational enumeration of the generator type. -/
@[reducible] noncomputable def filteredFactorLinearOrder :
    LinearOrder (FilteredLieFactor X) := by
  classical
  exact linearOrderOfSTO (filteredFactorLT X)

namespace FilteredLieFactor

/-- A free generator has bracket weight one. -/
def generator (x : X) : FilteredLieFactor X where
  value := FreeLieAlgebra.of ℤ x
  weight := 1
  weight_pos := by omega
  filtered := by
    rw [FreeLieDimension.lieHigh_one]
    trivial

@[simp]
theorem generator_value (x : X) : (generator X x).value = FreeLieAlgebra.of ℤ x :=
  rfl

@[simp]
theorem generator_weight (x : X) : (generator X x).weight = 1 :=
  rfl

/-- The collector's commutator correction is filtered in the sum of the two input weights. -/
def bracket (x y : FilteredLieFactor X) : FilteredLieFactor X where
  value := ⁅x.value, y.value⁆
  weight := x.weight + y.weight
  weight_pos := Nat.add_pos_left x.weight_pos y.weight
  filtered := FreeLieDimension.lieHigh_lie_mem X x.filtered y.filtered

@[simp]
theorem bracket_value (x y : FilteredLieFactor X) :
    (bracket X x y).value = ⁅x.value, y.value⁆ :=
  rfl

@[simp]
theorem bracket_weight (x y : FilteredLieFactor X) :
    (bracket X x y).weight = x.weight + y.weight :=
  rfl

/-- A filtered free-Lie factor has no associative word below its certified weight. -/
theorem freeLieToFreeAlgebra_mem_associativeHigh (x : FilteredLieFactor X) :
    PBW.freeLieToFreeAlgebra ℤ X x.value ∈
      FreeLieDimension.associativeHigh X x.weight := by
  obtain ⟨p, hp, hpval⟩ := x.filtered
  rw [← hpval, FreeLieDimension.freeLieToFreeAlgebra_mk]
  exact FreeLieDimension.magmaToFreeAlgebra_mem_high X hp

/-- Hence every homogeneous projection below the certified weight vanishes. -/
theorem associativeLengthComponent_eq_zero_of_lt
    (x : FilteredLieFactor X) {n : ℕ} (hn : n < x.weight) :
    associativeLengthComponent X n
        (PBW.freeLieToFreeAlgebra ℤ X x.value) = 0 :=
  DegreeFive.associativeLengthComponent_eq_zero_of_mem_high X
    (freeLieToFreeAlgebra_mem_associativeHigh X x) hn

end FilteredLieFactor

/-- Values of a list of filtered factors, for evaluation as an enveloping word. -/
def filteredFactorValues (xs : List (FilteredLieFactor X)) : List F :=
  xs.map FilteredLieFactor.value

/-- The numerical external-weight word attached to filtered factors. -/
def filteredFactorWeights (xs : List (FilteredLieFactor X)) : List ℕ :=
  xs.map FilteredLieFactor.weight

@[simp]
theorem filteredFactorWeights_generatorList (xs : List X) :
    filteredFactorWeights X (xs.map (FilteredLieFactor.generator X)) =
      xs.map (fun _ ↦ 1) := by
  simp [filteredFactorWeights, Function.comp_def]

@[simp]
theorem filteredFactorWeights_bracket_cons
    (left right : List (FilteredLieFactor X)) (x y : FilteredLieFactor X) :
    filteredFactorWeights X
        (left ++ FilteredLieFactor.bracket X x y :: right) =
      (filteredFactorWeights X left) ++
        (x.weight + y.weight) :: filteredFactorWeights X right := by
  simp [filteredFactorWeights]

end

end DegreeFive

end LieRings
