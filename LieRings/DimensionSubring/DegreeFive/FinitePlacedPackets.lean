import LieRings.DimensionSubring.DegreeFive.FiniteRelationCorrections
import LieRings.DimensionSubring.DegreeFive.SemanticCollector

/-!
# Smith-tagged placed packets

This file defines the actual packet type used by the finite placed collector.  A packet retains
the position of one distinguished Smith relation among homogeneous free-Lie basis factors.
Weight-five relation remainders are retained as exact terminal tags, so normalization preserves
equality in the enveloping algebra rather than only a congruence modulo weight five.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X

/-- Numerical code of a homogeneous basis factor. -/
def lowHomogeneousBasisCode (i : LowHomogeneousBasisIndex X) : ℕ × ℕ :=
  (i.1.1, i.2.1)

theorem lowHomogeneousBasisCode_injective :
    Function.Injective (lowHomogeneousBasisCode X) := by
  intro i j hij
  cases i with
  | mk ik ii =>
      cases j with
      | mk jk ji =>
          simp only [lowHomogeneousBasisCode, Prod.mk.injEq] at hij
          obtain ⟨hweight, hindex⟩ := hij
          have hk : ik = jk := Fin.ext hweight
          subst jk
          have hi : ii = ji := Fin.ext hindex
          subst ji
          rfl

/-- Weight-first order on the finite homogeneous basis. -/
noncomputable instance lowHomogeneousBasisLinearOrder :
    LinearOrder (LowHomogeneousBasisIndex X) :=
  LinearOrder.lift' (fun i ↦ toLex (lowHomogeneousBasisCode X i))
    (toLex.injective.comp (lowHomogeneousBasisCode_injective X))

theorem lowHomogeneousBasisWeight_mono
    {i j : LowHomogeneousBasisIndex X} (hij : i ≤ j) :
    lowHomogeneousBasisWeight X i ≤ lowHomogeneousBasisWeight X j := by
  change toLex (lowHomogeneousBasisCode X i) ≤
    toLex (lowHomogeneousBasisCode X j) at hij
  have hlex := Prod.Lex.toLex_le_toLex.mp hij
  rcases hlex with h | ⟨h, h'⟩
  · simpa [lowHomogeneousBasisWeight, lowHomogeneousBasisCode] using
      Nat.add_le_add_right h.le 1
  · simpa [lowHomogeneousBasisWeight, lowHomogeneousBasisCode] using
      Nat.add_le_add_right h.le 1

/-- The homogeneous Smith head, viewed as a factor in the common low basis. -/
def lowRelationSmithHead
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) :
    LowHomogeneousBasisIndex X :=
  ⟨i.1, (homogeneousRelationSmithForm X L evaluation (i.1.1 + 1)).f i.2⟩

@[simp]
theorem lowRelationSmithHead_weight
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) :
    lowHomogeneousBasisWeight X (lowRelationSmithHead X L evaluation i) =
      lowRelationSmithRowWeight X L evaluation i :=
  rfl

/-- Relation tags surviving exact normalization. -/
inductive FiniteCollectedRelation (evaluation : LieHom ℤ F L)
  | row (i : LowRelationSmithRowIndex X L evaluation)
  | high (r : LinearMap.ker evaluation.toLinearMap)
      (filtered : (r : F) ∈ FreeLieDimension.lieHigh X 5)

namespace FiniteCollectedRelation

/-- Actual defining relation carried by a tag. -/
def value (evaluation : LieHom ℤ F L) :
    FiniteCollectedRelation X L evaluation → F
  | row i => lowRelationSmithRow X L evaluation i
  | high r _ => (r : F)

/-- Certified minimum weight of a relation tag. -/
def weight (evaluation : LieHom ℤ F L) :
    FiniteCollectedRelation X L evaluation → ℕ
  | row i => lowRelationSmithRowWeight X L evaluation i
  | high _ _ => 5

theorem weight_pos (evaluation : LieHom ℤ F L)
    (r : FiniteCollectedRelation X L evaluation) : 0 < r.weight X L evaluation := by
  cases r with
  | row i => exact lowRelationSmithRowWeight_pos X L evaluation i
  | high r hr => simp [weight]

theorem value_mem_lieHigh (evaluation : LieHom ℤ F L)
    (r : FiniteCollectedRelation X L evaluation) :
    r.value X L evaluation ∈ FreeLieDimension.lieHigh X (r.weight X L evaluation) := by
  cases r with
  | row i => exact lowRelationSmithRow_mem_lieHigh X L evaluation i
  | high r hr => exact hr

end FiniteCollectedRelation

/-- A relation retained at an arbitrary position among homogeneous basis factors. -/
structure FiniteSmithPlacedPacket (evaluation : LieHom ℤ F L) where
  left : List (LowHomogeneousBasisIndex X)
  relation : FiniteCollectedRelation X L evaluation
  right : List (LowHomogeneousBasisIndex X)

namespace FiniteSmithPlacedPacket

variable (evaluation : LieHom ℤ F L)

/-- Underlying algebra packet. -/
def toAlgebraPacket (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) :
    AlgebraPacket ℤ F evaluation.ker where
  left := p.left.map (lowHomogeneousBasisValue X)
  relation := ⟨p.relation.value X L evaluation, by
    cases p.relation with
    | row i => exact lowRelationSmithRow_mem_ker X L evaluation i
    | high r hr => exact r.property⟩
  right := p.right.map (lowHomogeneousBasisValue X)

/-- Exact enveloping-algebra value of a placed packet. -/
def value (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) : UEA ℤ F :=
  AlgebraPacket.value ℤ F evaluation.ker
    (p.toAlgebraPacket X L evaluation)

/-- Sum of the certified external weights. -/
def externalWeight (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) : ℕ :=
  (p.left.map (lowHomogeneousBasisWeight X)).sum +
    (p.right.map (lowHomogeneousBasisWeight X)).sum

/-- Total bracket weight of the packet. -/
def totalWeight (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) : ℕ :=
  p.relation.weight X L evaluation + p.externalWeight X

/-- Replace only the factor lists. -/
def withFactors (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (left right : List (LowHomogeneousBasisIndex X)) :
    FiniteSmithPlacedPacket X L evaluation :=
  ⟨left, p.relation, right⟩

/-- Replace a row relation by another normalized row. -/
def withRow (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation)
    (left := p.left) (right := p.right) : FiniteSmithPlacedPacket X L evaluation :=
  ⟨left, .row i, right⟩

/-- Replace a row relation by a terminal weight-five remainder. -/
def withHigh (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (r : LinearMap.ker evaluation.toLinearMap)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh X 5)
    (left := p.left) (right := p.right) : FiniteSmithPlacedPacket X L evaluation :=
  ⟨left, .high r hr, right⟩

end FiniteSmithPlacedPacket

end

end DegreeFive

end LieRings
