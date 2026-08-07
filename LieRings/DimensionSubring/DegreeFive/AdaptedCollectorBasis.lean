import LieRings.DimensionSubring.DegreeFive.StandingReduction
import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneousFactors

/-!
# The single adapted basis seen by the finite collector

This file is the compatibility boundary between the adapted Smith presentation and the already
proved finite PBW collector.  It deliberately keeps the collector's finite weight-index type,
but changes its interpretation to the one positive, sorted Smith basis constructed in
`AdaptedPresentation`.

Most importantly, an adapted relation-row tag and its PBW head have *the same index*.  There is
no independently chosen embedding of row indices into factor indices.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X

/-- The collector keeps the established finite sum of weights one through four. -/
abbrev AdaptedLowBasisIndex := LowHomogeneousBasisIndex X

/-- The value of a collector factor in the shared sorted Smith basis. -/
def adaptedLowBasisValue (evaluation : LieHom ℤ F L)
    (i : AdaptedLowBasisIndex X) : F :=
  (collectedHomogeneousBasis X L evaluation (i.1.1 + 1) i.2 :
    freeLieExact X (i.1.1 + 1))

/-- Its homogeneous weight. -/
def adaptedLowBasisWeight (i : AdaptedLowBasisIndex X) : ℕ := i.1.1 + 1

theorem adaptedLowBasisWeight_pos (i : AdaptedLowBasisIndex X) :
    0 < adaptedLowBasisWeight X i := by
  simp [adaptedLowBasisWeight]

theorem adaptedLowBasisWeight_le_four (i : AdaptedLowBasisIndex X) :
    adaptedLowBasisWeight X i ≤ 4 := by
  have hi := i.1.2
  simp [adaptedLowBasisWeight] at hi ⊢

theorem adaptedLowBasisValue_mem_exact
    (evaluation : LieHom ℤ F L) (i : AdaptedLowBasisIndex X) :
    adaptedLowBasisValue X L evaluation i ∈
      freeLieExact X (adaptedLowBasisWeight X i) :=
  (collectedHomogeneousBasis X L evaluation (i.1.1 + 1) i.2).property

/-- Embed one exact homogeneous index into the common low-weight index. -/
def adaptedLowBasisIndexOf {n : ℕ} (hn : 0 < n) (hn4 : n ≤ 4)
    (i : FreeLieExactBasisIndex X n) : AdaptedLowBasisIndex X := by
  cases n with
  | zero => omega
  | succ k => exact ⟨⟨k, by omega⟩, i⟩

@[simp]
theorem adaptedLowBasisWeight_indexOf {n : ℕ} (hn : 0 < n) (hn4 : n ≤ 4)
    (i : FreeLieExactBasisIndex X n) :
    adaptedLowBasisWeight X (adaptedLowBasisIndexOf X hn hn4 i) = n := by
  cases n with
  | zero => omega
  | succ k => simp [adaptedLowBasisWeight, adaptedLowBasisIndexOf]

theorem adaptedLowBasisValue_indexOf
    (evaluation : LieHom ℤ F L) {n : ℕ} (hn : 0 < n) (hn4 : n ≤ 4)
    (i : FreeLieExactBasisIndex X n) :
    adaptedLowBasisValue X L evaluation (adaptedLowBasisIndexOf X hn hn4 i) =
      ((collectedHomogeneousBasis X L evaluation n i : freeLieExact X n) : F) := by
  cases n with
  | zero => omega
  | succ k =>
      simp [adaptedLowBasisValue, adaptedLowBasisIndexOf]
      rfl

/-! ## Bracket coordinates in that same basis -/

/-- Coordinates of a homogeneous bracket in the shared collected basis. -/
def adaptedHomogeneousBracketCoefficients
    (evaluation : LieHom ℤ F L) {m n : ℕ}
    (x : freeLieExact X m) (y : freeLieExact X n) :
    FreeLieExactBasisIndex X (m + n) →₀ ℤ :=
  (collectedHomogeneousBasis X L evaluation (m + n)).repr
    ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩

theorem adaptedHomogeneousBracketCoefficients_sum
    (evaluation : LieHom ℤ F L) {m n : ℕ}
    (x : freeLieExact X m) (y : freeLieExact X n) :
    (adaptedHomogeneousBracketCoefficients X L evaluation x y).sum
        (fun i c ↦ c •
          (((collectedHomogeneousBasis X L evaluation (m + n) i :
            freeLieExact X (m + n))) : F)) =
      ⁅(x : F), (y : F)⁆ := by
  change ((collectedHomogeneousBasis X L evaluation (m + n)).repr
      ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩).sum
        (fun i c ↦ c •
          ((collectedHomogeneousBasis X L evaluation (m + n) i :
            freeLieExact X (m + n)) : F)) = _
  have h := (collectedHomogeneousBasis X L evaluation (m + n)).linearCombination_repr
    ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩
  let c := (collectedHomogeneousBasis X L evaluation (m + n)).repr
    ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩
  calc
    c.sum (fun i z ↦ z •
        (((collectedHomogeneousBasis X L evaluation (m + n) i :
          freeLieExact X (m + n))) : F)) =
        (freeLieExact X (m + n)).subtype
          (c.sum (fun i z ↦ z •
            collectedHomogeneousBasis X L evaluation (m + n) i)) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro i hi
      rw [map_zsmul]
      rfl
    _ = ⁅(x : F), (y : F)⁆ := congrArg Subtype.val h

/-- Bracket coordinates embedded in the common low-factor type. -/
def adaptedLowBracketCoefficients
    (evaluation : LieHom ℤ F L) (x y : AdaptedLowBasisIndex X)
    (hxy : adaptedLowBasisWeight X x + adaptedLowBasisWeight X y ≤ 4) :
    AdaptedLowBasisIndex X →₀ ℤ :=
  (adaptedHomogeneousBracketCoefficients X L evaluation
      ⟨adaptedLowBasisValue X L evaluation x,
        adaptedLowBasisValue_mem_exact X L evaluation x⟩
      ⟨adaptedLowBasisValue X L evaluation y,
        adaptedLowBasisValue_mem_exact X L evaluation y⟩).mapDomain
    (adaptedLowBasisIndexOf X
      (Nat.add_pos_left (adaptedLowBasisWeight_pos X x) _) hxy)

theorem adaptedLowBracketCoefficients_sum
    (evaluation : LieHom ℤ F L) (x y : AdaptedLowBasisIndex X)
    (hxy : adaptedLowBasisWeight X x + adaptedLowBasisWeight X y ≤ 4) :
    (adaptedLowBracketCoefficients X L evaluation x y hxy).sum
        (fun i c ↦ c • adaptedLowBasisValue X L evaluation i) =
      ⁅adaptedLowBasisValue X L evaluation x,
        adaptedLowBasisValue X L evaluation y⁆ := by
  unfold adaptedLowBracketCoefficients
  rw [Finsupp.sum_mapDomain_index]
  · simpa only [adaptedLowBasisValue_indexOf] using
      adaptedHomogeneousBracketCoefficients_sum X L evaluation
        (⟨adaptedLowBasisValue X L evaluation x,
          adaptedLowBasisValue_mem_exact X L evaluation x⟩ :
            freeLieExact X (adaptedLowBasisWeight X x))
        (⟨adaptedLowBasisValue X L evaluation y,
          adaptedLowBasisValue_mem_exact X L evaluation y⟩ :
            freeLieExact X (adaptedLowBasisWeight X y))
  · intro i
    simp
  · intro i a b
    simp [add_smul]

/-! ## Relation rows with literally identical heads -/

/-- A low adapted relation row uses exactly the same index type as a low PBW factor. -/
abbrev AdaptedLowRelationRowIndex := AdaptedLowBasisIndex X

/-- The actual positive, sorted adapted relation row. -/
def adaptedLowRelationRow (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X) : F :=
  collectedRelationRow X L evaluation (i.1.1 + 1) i.2

/-- Its certified least weight. -/
def adaptedLowRelationRowWeight (i : AdaptedLowRelationRowIndex X) : ℕ :=
  adaptedLowBasisWeight X i

/-- Its positive Smith diagonal. -/
def adaptedLowRelationDiagonal (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X) : ℕ :=
  collectedDiagonal X L evaluation (i.1.1 + 1) i.2

/-- The head is not an independently chosen map: it is the row index itself. -/
def adaptedLowRelationHead (i : AdaptedLowRelationRowIndex X) :
    AdaptedLowBasisIndex X := i

@[simp]
theorem adaptedLowRelationHead_eq (i : AdaptedLowRelationRowIndex X) :
    adaptedLowRelationHead X i = i := rfl

theorem adaptedLowRelationRow_head
    (evaluation : LieHom ℤ F L) (i : AdaptedLowRelationRowIndex X) :
    freeLieExactProjection X (adaptedLowRelationRowWeight X i)
        (adaptedLowRelationRow X L evaluation i) =
      (adaptedLowRelationDiagonal X L evaluation i : ℤ) •
        ⟨adaptedLowBasisValue X L evaluation i,
          adaptedLowBasisValue_mem_exact X L evaluation i⟩ := by
  exact collectedRelationRow_head X L evaluation (i.1.1 + 1) i.2

theorem adaptedLowRelationRow_mem_ker
    (evaluation : LieHom ℤ F L) (i : AdaptedLowRelationRowIndex X) :
    evaluation (adaptedLowRelationRow X L evaluation i) = 0 :=
  collectedRelationRow_mem_ker X L evaluation (i.1.1 + 1) i.2

theorem adaptedLowRelationRow_mem_lieHigh
    (evaluation : LieHom ℤ F L) (i : AdaptedLowRelationRowIndex X) :
    adaptedLowRelationRow X L evaluation i ∈
      FreeLieDimension.lieHigh X (adaptedLowRelationRowWeight X i) :=
  collectedRelationRow_mem_lieHigh X L evaluation (i.1.1 + 1) i.2

end


end DegreeFive

end LieRings
