import LieRings.DimensionSubring.DegreeFive.AdaptedCollectedCorrections

/-!
# Placed packets in the common adapted presentation

The relation mark and every external factor are indexed by the same sorted collected basis.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X

/-- Relation tags surviving exact normalization. -/
inductive AdaptedCollectedRelation (evaluation : LieHom ℤ F L)
  | row (i : AdaptedLowRelationRowIndex X)
  | high (r : LinearMap.ker evaluation.toLinearMap)
      (filtered : (r : F) ∈ FreeLieDimension.lieHigh X 5)

namespace AdaptedCollectedRelation

/-- Actual defining relation carried by a tag. -/
def value (evaluation : LieHom ℤ F L) :
    AdaptedCollectedRelation X L evaluation → F
  | row i => adaptedLowRelationRow X L evaluation i
  | high r _ => (r : F)

/-- Certified minimum weight of a relation tag. -/
def weight (evaluation : LieHom ℤ F L) :
    AdaptedCollectedRelation X L evaluation → ℕ
  | row i => adaptedLowRelationRowWeight X i
  | high _ _ => 5

theorem weight_pos (evaluation : LieHom ℤ F L)
    (r : AdaptedCollectedRelation X L evaluation) : 0 < r.weight X L evaluation := by
  cases r with
  | row i => exact adaptedLowBasisWeight_pos X i
  | high r hr => simp [weight]

theorem value_mem_lieHigh (evaluation : LieHom ℤ F L)
    (r : AdaptedCollectedRelation X L evaluation) :
    r.value X L evaluation ∈ FreeLieDimension.lieHigh X (r.weight X L evaluation) := by
  cases r with
  | row i => exact adaptedLowRelationRow_mem_lieHigh X L evaluation i
  | high r hr => exact hr

end AdaptedCollectedRelation

/-- A relation retained at an arbitrary position among homogeneous basis factors. -/
structure AdaptedSmithPlacedPacket (evaluation : LieHom ℤ F L) where
  left : List (AdaptedLowBasisIndex X)
  relation : AdaptedCollectedRelation X L evaluation
  right : List (AdaptedLowBasisIndex X)

namespace AdaptedSmithPlacedPacket

variable (evaluation : LieHom ℤ F L)

/-- Underlying algebra packet. -/
def toAlgebraPacket (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) :
    AlgebraPacket ℤ F evaluation.ker where
  left := p.left.map (adaptedLowBasisValue X L evaluation)
  relation := ⟨p.relation.value X L evaluation, by
    cases p.relation with
    | row i => exact adaptedLowRelationRow_mem_ker X L evaluation i
    | high r hr => exact r.property⟩
  right := p.right.map (adaptedLowBasisValue X L evaluation)

/-- Exact enveloping-algebra value of a placed packet. -/
def value (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) : UEA ℤ F :=
  AlgebraPacket.value ℤ F evaluation.ker
    (p.toAlgebraPacket X L evaluation)

/-- Sum of the certified external weights. -/
def externalWeight (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) : ℕ :=
  (p.left.map (adaptedLowBasisWeight X)).sum +
    (p.right.map (adaptedLowBasisWeight X)).sum

/-- Total bracket weight of the packet. -/
def totalWeight (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) : ℕ :=
  p.relation.weight X L evaluation + p.externalWeight X

/-- Replace only the factor lists. -/
def withFactors (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (left right : List (AdaptedLowBasisIndex X)) :
    AdaptedSmithPlacedPacket X L evaluation :=
  ⟨left, p.relation, right⟩

/-- Replace a row relation by another normalized row. -/
def withRow (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X)
    (left := p.left) (right := p.right) : AdaptedSmithPlacedPacket X L evaluation :=
  ⟨left, .row i, right⟩

/-- Replace a row relation by a terminal weight-five remainder. -/
def withHigh (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (r : LinearMap.ker evaluation.toLinearMap)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh X 5)
    (left := p.left) (right := p.right) : AdaptedSmithPlacedPacket X L evaluation :=
  ⟨left, .high r hr, right⟩

end AdaptedSmithPlacedPacket

end

end DegreeFive

end LieRings

