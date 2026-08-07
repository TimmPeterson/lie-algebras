import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedWitness
import LieRings.DimensionSubring.DegreeFive.CoordinateTheta

/-!
# Coordinate coefficients of the coherent terminal ledger

This file is the syntactic boundary between the adapted placed collector and the existing
coordinate calculation. It makes no new basis choices.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X

/-- The weight-one collector factor belonging to a coordinate index. -/
def adaptedCoordinateXFactor (i : FreeLieExactBasisIndex X 1) :
    AdaptedLowBasisIndex X :=
  adaptedLowBasisIndexOf X (by omega) (by omega) i

/-- The weight-two collector factor belonging to a coordinate index. -/
def adaptedCoordinateYFactor (k : FreeLieExactBasisIndex X 2) :
    AdaptedLowBasisIndex X :=
  adaptedLowBasisIndexOf X (by omega) (by omega) k

@[simp]
theorem adaptedCoordinateXFactor_weight (i : FreeLieExactBasisIndex X 1) :
    adaptedLowBasisWeight X (adaptedCoordinateXFactor X i) = 1 :=
  adaptedLowBasisWeight_indexOf X (by omega) (by omega) i

@[simp]
theorem adaptedCoordinateYFactor_weight (k : FreeLieExactBasisIndex X 2) :
    adaptedLowBasisWeight X (adaptedCoordinateYFactor X k) = 2 :=
  adaptedLowBasisWeight_indexOf X (by omega) (by omega) k

/-- Every collector factor of weight one is one of the named coordinate factors. -/
theorem exists_eq_adaptedCoordinateXFactor
    (x : AdaptedLowBasisIndex X) (hx : adaptedLowBasisWeight X x = 1) :
    ∃ i : FreeLieExactBasisIndex X 1, x = adaptedCoordinateXFactor X i := by
  rcases x with ⟨⟨n, hn⟩, i⟩
  simp [adaptedLowBasisWeight] at hx
  subst n
  exact ⟨i, rfl⟩

/-- Every collector factor of weight two is one of the named coordinate factors. -/
theorem exists_eq_adaptedCoordinateYFactor
    (x : AdaptedLowBasisIndex X) (hx : adaptedLowBasisWeight X x = 2) :
    ∃ k : FreeLieExactBasisIndex X 2, x = adaptedCoordinateYFactor X k := by
  rcases x with ⟨⟨n, hn⟩, i⟩
  simp [adaptedLowBasisWeight] at hx
  subst n
  exact ⟨i, rfl⟩

/-- A literal terminal packet with a specified row and factor lists. -/
def IsAdaptedRowPacket
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X)
    (left right : List (AdaptedLowBasisIndex X))
    (p : AdaptedSmithPlacedPacket X L evaluation) : Prop :=
  p.left = left ∧ p.relation = .row i ∧ p.right = right

/-- Sum the coefficients of all packets having a prescribed literal shape. -/
def adaptedLedgerRowCoefficient
    (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ)
    (i : AdaptedLowRelationRowIndex X)
    (left right : List (AdaptedLowBasisIndex X)) : ℤ := by
  classical
  exact ledger.sum fun p n ↦
    if IsAdaptedRowPacket X L evaluation i left right p then n else 0

namespace AdaptedTerminalCoordinates

local notation "I" => FreeLieExactBasisIndex X 1
local notation "K" => FreeLieExactBasisIndex X 2

/-- Scalar weight-one row coefficient. -/
def r (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) (i : I) : ℤ :=
  adaptedLedgerRowCoefficient X L evaluation ledger
    (adaptedCoordinateXFactor X i) [] []

/-- Scalar weight-two row coefficient. -/
def s (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) (k : K) : ℤ :=
  adaptedLedgerRowCoefficient X L evaluation ledger
    (adaptedCoordinateYFactor X k) [] []

/-- Both equal-head placements have the same low PBW word. -/
def rxx (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) (i : I) : ℤ :=
  adaptedLedgerRowCoefficient X L evaluation ledger
      (adaptedCoordinateXFactor X i) [] [adaptedCoordinateXFactor X i] +
    adaptedLedgerRowCoefficient X L evaluation ledger
      (adaptedCoordinateXFactor X i) [adaptedCoordinateXFactor X i] []

/-- Coefficient of the ordered placement r_i x_j. -/
def rx (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) (i j : I) : ℤ :=
  adaptedLedgerRowCoefficient X L evaluation ledger
    (adaptedCoordinateXFactor X i) [] [adaptedCoordinateXFactor X j]

/-- Coefficient of the ordered placement x_i r_j. -/
def xr (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) (i j : I) : ℤ :=
  adaptedLedgerRowCoefficient X L evaluation ledger
    (adaptedCoordinateXFactor X j) [adaptedCoordinateXFactor X i] []

/-- Coefficient of r_i y_k. -/
def v (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ)
    (i : I) (k : K) : ℤ :=
  adaptedLedgerRowCoefficient X L evaluation ledger
    (adaptedCoordinateXFactor X i) [] [adaptedCoordinateYFactor X k]

/-- Coefficient of x_i s_k. -/
def v' (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ)
    (i : I) (k : K) : ℤ :=
  adaptedLedgerRowCoefficient X L evaluation ledger
    (adaptedCoordinateYFactor X k) [adaptedCoordinateXFactor X i] []

/-- Coefficient of s_k y_l. -/
def sY (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) (k l : K) : ℤ :=
  adaptedLedgerRowCoefficient X L evaluation ledger
    (adaptedCoordinateYFactor X k) [] [adaptedCoordinateYFactor X l]

/-- Coefficient of y_k s_l. -/
def Ys (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) (k l : K) : ℤ :=
  adaptedLedgerRowCoefficient X L evaluation ledger
    (adaptedCoordinateYFactor X l) [adaptedCoordinateYFactor X k] []

/-- The visible part of PreTheta. The scalar weight-three correction and exhaustive
zero-projection table remainder are supplied by the projection/classification theorem. -/
def visiblePreTheta (evaluation : LieHom ℤ F L)
    (ledger : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) (t : ℤ)
    (remainder : @Coordinate.Data.CollectedExpression.TableRemainder
      I K inferInstance) :
    @Coordinate.Data.CollectedExpression.PreTheta I K inferInstance where
  r := r X L evaluation ledger
  s := s X L evaluation ledger
  rxx := rxx X L evaluation ledger
  rx := rx X L evaluation ledger
  xr := xr X L evaluation ledger
  v := v X L evaluation ledger
  v' := v' X L evaluation ledger
  t := t
  sY := sY X L evaluation ledger
  Ys := Ys X L evaluation ledger
  remainder := remainder

end AdaptedTerminalCoordinates

end

end DegreeFive

end LieRings
