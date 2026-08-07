import LieRings.DimensionSubring.DegreeFive.PacketCollector
import LieRings.DimensionSubring.DegreeFive.RelationIdeal
import Mathlib.Tactic.NoncommRing

/-!
# Exact identities used by placed PBW collection

These are equality-level, coefficient-sensitive forms of the two collector rewrites.  They hold
in the universal enveloping algebra itself, not merely modulo a filtration or an ideal.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (R : Type u) (F : Type v)
variable [CommRing R] [LieRing F] [LieAlgebra R F]

/-- The enveloping word associated with a list of Lie factors. -/
def envelopingWord (xs : List F) : UEA R F :=
  (xs.map (UniversalEnvelopingAlgebra.ι R)).prod

@[simp]
theorem envelopingWord_nil : envelopingWord R F [] = 1 :=
  rfl

@[simp]
theorem envelopingWord_cons (x : F) (xs : List F) :
    envelopingWord R F (x :: xs) =
      UniversalEnvelopingAlgebra.ι R x * envelopingWord R F xs :=
  rfl

@[simp]
theorem envelopingWord_append (xs ys : List F) :
    envelopingWord R F (xs ++ ys) =
      envelopingWord R F xs * envelopingWord R F ys := by
  simp [envelopingWord, List.map_append]

/-- Moving one Lie factor past another creates their Lie bracket. -/
theorem iota_mul_iota_swap (x y : F) :
    UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y =
      UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x +
        UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ := by
  have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι R) x y
  change UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ =
    UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
      UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x at h
  rw [h]
  noncomm_ring

/-- Exact PBW swap inside arbitrary surrounding words. -/
theorem envelopingWord_adjacent_swap
    (left right : List F) (x y : F) :
    envelopingWord R F (left ++ x :: y :: right) =
      envelopingWord R F (left ++ y :: x :: right) +
        envelopingWord R F left *
          UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ *
            envelopingWord R F right := by
  simp only [envelopingWord_append, envelopingWord_cons]
  rw [← mul_assoc (UniversalEnvelopingAlgebra.ι R x)
    (UniversalEnvelopingAlgebra.ι R y) (envelopingWord R F right)]
  rw [iota_mul_iota_swap R F x y]
  noncomm_ring

variable (I : LieIdeal R F)

/-- The bracket correction created while moving a factor past a marked relation is again a
marked relation. -/
def relationBracketLeft (x : F) (r : I) : I :=
  ⟨⁅x, (r : F)⁆, I.lie_mem r.property⟩

@[simp]
theorem relationBracketLeft_coe (x : F) (r : I) :
    (relationBracketLeft R F I x r : F) = ⁅x, (r : F)⁆ :=
  rfl

/-- Exact relation-movement identity inside arbitrary surrounding words. -/
theorem envelopingWord_move_relation
    (left right : List F) (x : F) (r : I) :
    envelopingWord R F left * UniversalEnvelopingAlgebra.ι R x *
          UniversalEnvelopingAlgebra.ι R (r : F) * envelopingWord R F right =
      envelopingWord R F left * UniversalEnvelopingAlgebra.ι R (r : F) *
          UniversalEnvelopingAlgebra.ι R x * envelopingWord R F right +
        envelopingWord R F left *
          UniversalEnvelopingAlgebra.ι R (relationBracketLeft R F I x r : F) *
            envelopingWord R F right := by
  rw [relationBracketLeft_coe]
  calc
    _ = (envelopingWord R F left *
          (UniversalEnvelopingAlgebra.ι R x *
            UniversalEnvelopingAlgebra.ι R (r : F))) *
          envelopingWord R F right := by noncomm_ring
    _ = _ := by
      rw [iota_mul_iota_swap R F x (r : F)]
      noncomm_ring

/-- A packet with its relation tag retained at an arbitrary position. -/
structure AlgebraPacket where
  left : List F
  relation : I
  right : List F

/-- Evaluation of a tagged packet in the enveloping algebra. -/
def AlgebraPacket.value (p : AlgebraPacket R F I) : UEA R F :=
  envelopingWord R F p.left *
    UniversalEnvelopingAlgebra.ι R (p.relation : F) *
      envelopingWord R F p.right

/-- Moving the final factor of the left word across the relation is a coefficient-retaining
two-packet expansion. -/
theorem AlgebraPacket.move_last_value
    (left right : List F) (x : F) (r : I) :
    (AlgebraPacket.value R F I
        (⟨left ++ [x], r, right⟩ : AlgebraPacket R F I)) =
      AlgebraPacket.value R F I
          (⟨left, r, x :: right⟩ : AlgebraPacket R F I) +
        AlgebraPacket.value R F I
          (⟨left, relationBracketLeft R F I x r, right⟩ : AlgebraPacket R F I) := by
  simp only [AlgebraPacket.value, envelopingWord_append, envelopingWord_cons,
    envelopingWord_nil, mul_one]
  simpa only [mul_assoc] using
    envelopingWord_move_relation R F I left right x r

/-- Swapping an inverted adjacent pair on the right of a relation is a coefficient-retaining
two-packet expansion, with the commutator as the shorter correction packet. -/
theorem AlgebraPacket.swap_right_value
    (left middle right : List F) (x y : F) (r : I) :
    AlgebraPacket.value R F I
        (⟨left, r, middle ++ x :: y :: right⟩ : AlgebraPacket R F I) =
      AlgebraPacket.value R F I
          (⟨left, r, middle ++ y :: x :: right⟩ : AlgebraPacket R F I) +
        AlgebraPacket.value R F I
          (⟨left, r, middle ++ ⁅x, y⁆ :: right⟩ : AlgebraPacket R F I) := by
  simp only [AlgebraPacket.value, envelopingWord_append, envelopingWord_cons]
  rw [← mul_assoc (UniversalEnvelopingAlgebra.ι R x)
    (UniversalEnvelopingAlgebra.ι R y) (envelopingWord R F right)]
  rw [iota_mul_iota_swap R F x y]
  noncomm_ring

/-- Swapping an inverted adjacent pair on the left of a marked relation.  This is the
left-hand counterpart of `AlgebraPacket.swap_right_value`; keeping it at the packet level
avoids reassociating a long enveloping-algebra word in every finite collector proof. -/
theorem AlgebraPacket.swap_left_value
    (left middle right : List F) (x y : F) (r : I) :
    AlgebraPacket.value R F I
        (⟨left ++ x :: y :: middle, r, right⟩ : AlgebraPacket R F I) =
      AlgebraPacket.value R F I
          (⟨left ++ y :: x :: middle, r, right⟩ : AlgebraPacket R F I) +
        AlgebraPacket.value R F I
          (⟨left ++ ⁅x, y⁆ :: middle, r, right⟩ : AlgebraPacket R F I) := by
  simp only [AlgebraPacket.value, envelopingWord_append, envelopingWord_cons]
  rw [← mul_assoc (UniversalEnvelopingAlgebra.ι R x)
    (UniversalEnvelopingAlgebra.ι R y) (envelopingWord R F middle)]
  rw [iota_mul_iota_swap R F x y]
  noncomm_ring

/-- The relation bracket produced when a marked relation crosses the first factor on its
right. -/
def relationBracketRight (r : I) (x : F) : I :=
  ⟨⁅(r : F), x⁆, lie_mem_left R F I (r : F) x r.property⟩

@[simp]
theorem relationBracketRight_coe (r : I) (x : F) :
    (relationBracketRight R F I r x : F) = ⁅(r : F), x⁆ :=
  rfl

/-- Moving the first right factor to the left of a marked relation gives the principal
crossed packet plus the bracket `[r,x]`. -/
theorem AlgebraPacket.move_first_value
    (left right : List F) (r : I) (x : F) :
    AlgebraPacket.value R F I
        (⟨left, r, x :: right⟩ : AlgebraPacket R F I) =
      AlgebraPacket.value R F I
          (⟨left ++ [x], r, right⟩ : AlgebraPacket R F I) +
        AlgebraPacket.value R F I
          (⟨left, relationBracketRight R F I r x, right⟩ : AlgebraPacket R F I) := by
  simp only [AlgebraPacket.value, envelopingWord_append, envelopingWord_cons,
    envelopingWord_nil, mul_one, relationBracketRight_coe]
  calc
    _ = (envelopingWord R F left *
          (UniversalEnvelopingAlgebra.ι R (r : F) *
            UniversalEnvelopingAlgebra.ι R x)) *
          envelopingWord R F right := by noncomm_ring
    _ = _ := by
      rw [iota_mul_iota_swap R F (r : F) x]
      noncomm_ring

end

end DegreeFive

end LieRings
