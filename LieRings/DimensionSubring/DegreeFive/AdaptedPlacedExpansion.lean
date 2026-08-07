import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedPackets
import LieRings.DimensionSubring.DegreeFive.FinitePlacedExpansion

/-!
# One-step expansion of common adapted placed packets

This is the existing placed rewrite with every semantic operation interpreted in the common
sorted Smith basis.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X

variable (evaluation : LieHom ℤ F L)

local notation "Packet" => AdaptedSmithPlacedPacket X L evaluation
local notation "Factor" => AdaptedLowBasisIndex X
local notation "Row" => AdaptedLowRelationRowIndex X

/-- Replace an ordinary inverted pair by the ordered pair. -/
def AdaptedSmithPlacedPacket.swapLeft
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor) : AdaptedSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation (d.left ++ d.y :: d.x :: d.right) p.right

/-- One basis summand of the ordinary bracket correction on the left. -/
def AdaptedSmithPlacedPacket.bracketLeft
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor) (z : Factor) :
    AdaptedSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation (d.left ++ z :: d.right) p.right

/-- Replace an ordinary inverted pair by the ordered pair on the right. -/
def AdaptedSmithPlacedPacket.swapRight
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor) : AdaptedSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation p.left (d.left ++ d.y :: d.x :: d.right)

/-- One basis summand of the ordinary bracket correction on the right. -/
def AdaptedSmithPlacedPacket.bracketRight
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor) (z : Factor) :
    AdaptedSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation p.left (d.left ++ z :: d.right)

/-- Move the last left factor to the right of the relation. -/
def AdaptedSmithPlacedPacket.moveLeftAcross
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (front : List Factor) (x : Factor) : AdaptedSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation front (x :: p.right)

/-- A normalized row summand of the correction created while moving the last left factor. -/
def AdaptedSmithPlacedPacket.leftRelationCorrection
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (front : List Factor) (j : AdaptedLowRelationRowIndex X) :
    AdaptedSmithPlacedPacket X L evaluation :=
  p.withRow X L evaluation j front p.right

/-- The exact weight-five correction created while moving the last left factor. -/
def AdaptedSmithPlacedPacket.leftHighCorrection
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (front : List Factor) (i : AdaptedLowRelationRowIndex X)
    (x : Factor) : AdaptedSmithPlacedPacket X L evaluation :=
  p.withHigh X L evaluation
    (adaptedLowRelationBracketWeightFiveRemainder X L evaluation i x)
    (adaptedLowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
    front p.right

/-- Move the first right factor to the left of the relation. -/
def AdaptedSmithPlacedPacket.moveRightAcross
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (x : Factor) (tail : List Factor) : AdaptedSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation (p.left ++ [x]) tail

/-- A normalized row summand of the correction created while moving the first right factor. -/
def AdaptedSmithPlacedPacket.rightRelationCorrection
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (tail : List Factor) (j : AdaptedLowRelationRowIndex X) :
    AdaptedSmithPlacedPacket X L evaluation :=
  p.withRow X L evaluation j p.left tail

/-- The exact weight-five correction created while moving the first right factor. -/
def AdaptedSmithPlacedPacket.rightHighCorrection
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (tail : List Factor) (i : AdaptedLowRelationRowIndex X)
    (x : Factor) : AdaptedSmithPlacedPacket X L evaluation :=
  p.withHigh X L evaluation
    (adaptedLowRelationBracketWeightFiveRemainder X L evaluation i x)
    (adaptedLowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
    p.left tail

/-- Ordinary left-factor PBW expansion. -/
def adaptedLeftSwapExpansion (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) (d : AdjacentInversionData Factor)
    (hweight : adaptedLowBasisWeight X d.x +
      adaptedLowBasisWeight X d.y ≤ 4) :
    List (ℤ × AdaptedSmithPlacedPacket X L evaluation) :=
  (1, p.swapLeft X L evaluation d) ::
    finsuppTaggedList (adaptedLowBracketCoefficients X L evaluation d.x d.y hweight)
      (p.bracketLeft X L evaluation d)

/-- Ordinary right-factor PBW expansion. -/
def adaptedRightSwapExpansion (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) (d : AdjacentInversionData Factor)
    (hweight : adaptedLowBasisWeight X d.x +
      adaptedLowBasisWeight X d.y ≤ 4) :
    List (ℤ × AdaptedSmithPlacedPacket X L evaluation) :=
  (1, p.swapRight X L evaluation d) ::
    finsuppTaggedList (adaptedLowBracketCoefficients X L evaluation d.x d.y hweight)
      (p.bracketRight X L evaluation d)

/-- Expansion for `x ρ = ρ x - [ρ,x]`, including immediate Smith normalization. -/
def adaptedMoveLeftExpansion (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation) (front : List Factor)
    (i : AdaptedLowRelationRowIndex X) (x : Factor) :
    List (ℤ × AdaptedSmithPlacedPacket X L evaluation) :=
  (1, p.moveLeftAcross X L evaluation front x) ::
    (finsuppTaggedList (adaptedLowRelationBracketRowCoefficients X L evaluation i x)
      (p.leftRelationCorrection X L evaluation front)).map
        (fun q ↦ (-q.1, q.2)) ++
    [(-1, p.leftHighCorrection X L evaluation front i x)]

/-- Expansion for `ρ x = x ρ + [ρ,x]`, including immediate Smith normalization. -/
def adaptedMoveRightExpansion (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X) (x : Factor) (tail : List Factor) :
    List (ℤ × AdaptedSmithPlacedPacket X L evaluation) :=
  (1, p.moveRightAcross X L evaluation x tail) ::
    finsuppTaggedList (adaptedLowRelationBracketRowCoefficients X L evaluation i x)
      (p.rightRelationCorrection X L evaluation tail) ++
    [(1, p.rightHighCorrection X L evaluation tail i x)]

/-- Multiplication by fixed enveloping words on both sides is additive in the marked Lie
factor.  This is the common linear context used to transport all finite coefficient
expansions into packet values. -/
def adaptedEnvelopingLinearContext (left right : List F) : F →+ UEA ℤ F where
  toFun z := envelopingWord ℤ F left *
    UniversalEnvelopingAlgebra.ι ℤ z * envelopingWord ℤ F right
  map_zero' := by simp
  map_add' x y := by simp [map_add, mul_add, add_mul]

@[simp]
theorem adaptedEnvelopingLinearContext_apply (left right : List F) (z : F) :
    adaptedEnvelopingLinearContext X left right z =
      envelopingWord ℤ F left * UniversalEnvelopingAlgebra.ι ℤ z *
        envelopingWord ℤ F right :=
  rfl

/-- Evaluation commutes with a finite integral coefficient expansion in the marked slot. -/
theorem adaptedEnvelopingLinearContext_finsupp_sum {I : Type*}
    (left right : List F) (c : I →₀ ℤ) (f : I → F) :
    adaptedEnvelopingLinearContext X left right
        (c.sum (fun i z ↦ z • f i)) =
      c.sum (fun i z ↦ z • adaptedEnvelopingLinearContext X left right (f i)) := by
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  exact map_zsmul (adaptedEnvelopingLinearContext X left right) (c i) (f i)

/-- The ordinary left PBW expansion preserves the exact enveloping-algebra value. -/
theorem adaptedLeftSwapExpansion_value
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor)
    (hleft : p.left = d.left ++ d.x :: d.y :: d.right)
    (hweight : adaptedLowBasisWeight X d.x +
      adaptedLowBasisWeight X d.y ≤ 4) :
    p.value X L evaluation =
      ((adaptedLeftSwapExpansion X L evaluation p d hweight).map
        (fun q ↦ q.1 • q.2.value X L evaluation)).sum := by
  classical
  change p.value X L evaluation =
    (1 : ℤ) • (p.swapLeft X L evaluation d).value X L evaluation +
      ((finsuppTaggedList
        (adaptedLowBracketCoefficients X L evaluation d.x d.y hweight)
        (p.bracketLeft X L evaluation d)).map
          (fun q ↦ q.1 • q.2.value X L evaluation)).sum
  rw [one_smul, finsuppTaggedList_value_sum]
  have hcoeff := adaptedLowBracketCoefficients_sum X L evaluation d.x d.y hweight
  have hcontext := congrArg
    (adaptedEnvelopingLinearContext X
      (d.left.map (adaptedLowBasisValue X L evaluation))
      (d.right.map (adaptedLowBasisValue X L evaluation) ++
        p.relation.value X L evaluation ::
          p.right.map (adaptedLowBasisValue X L evaluation))) hcoeff
  rw [adaptedEnvelopingLinearContext_finsupp_sum] at hcontext
  have hcorrection :
      (adaptedLowBracketCoefficients X L evaluation d.x d.y hweight).sum
          (fun z c ↦ c •
            (p.bracketLeft X L evaluation d z).value X L evaluation) =
        adaptedEnvelopingLinearContext X
          (d.left.map (adaptedLowBasisValue X L evaluation))
          (d.right.map (adaptedLowBasisValue X L evaluation) ++
            p.relation.value X L evaluation ::
              p.right.map (adaptedLowBasisValue X L evaluation))
          ⁅adaptedLowBasisValue X L evaluation d.x,
            adaptedLowBasisValue X L evaluation d.y⁆ := by
    rw [← hcontext]
    apply Finsupp.sum_congr
    intro z hz
    simp [AdaptedSmithPlacedPacket.value,
      AdaptedSmithPlacedPacket.toAlgebraPacket,
      AdaptedSmithPlacedPacket.bracketLeft,
      AdaptedSmithPlacedPacket.withFactors, AlgebraPacket.value,
      adaptedEnvelopingLinearContext, List.map_append, envelopingWord_append]
    noncomm_ring
  rw [hcorrection]
  rw [adaptedEnvelopingLinearContext_apply]
  rw [LieHom.map_lie]
  have hswap := AlgebraPacket.swap_left_value ℤ F evaluation.ker
    (d.left.map (adaptedLowBasisValue X L evaluation))
    (d.right.map (adaptedLowBasisValue X L evaluation))
    (p.right.map (adaptedLowBasisValue X L evaluation))
    (adaptedLowBasisValue X L evaluation d.x)
    (adaptedLowBasisValue X L evaluation d.y)
    (p.toAlgebraPacket X L evaluation).relation
  simp [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket,
    AdaptedSmithPlacedPacket.swapLeft,
    AdaptedSmithPlacedPacket.withFactors, AlgebraPacket.value,
    List.map_append, hleft] at hswap ⊢
  convert hswap using 1 <;> noncomm_ring

/-- The ordinary right PBW expansion preserves the exact enveloping-algebra value. -/
theorem adaptedRightSwapExpansion_value
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor)
    (hright : p.right = d.left ++ d.x :: d.y :: d.right)
    (hweight : adaptedLowBasisWeight X d.x +
      adaptedLowBasisWeight X d.y ≤ 4) :
    p.value X L evaluation =
      ((adaptedRightSwapExpansion X L evaluation p d hweight).map
        (fun q ↦ q.1 • q.2.value X L evaluation)).sum := by
  classical
  change p.value X L evaluation =
    (1 : ℤ) • (p.swapRight X L evaluation d).value X L evaluation +
      ((finsuppTaggedList
        (adaptedLowBracketCoefficients X L evaluation d.x d.y hweight)
        (p.bracketRight X L evaluation d)).map
          (fun q ↦ q.1 • q.2.value X L evaluation)).sum
  rw [one_smul, finsuppTaggedList_value_sum]
  have hcoeff := adaptedLowBracketCoefficients_sum X L evaluation d.x d.y hweight
  have hcontext := congrArg
    (adaptedEnvelopingLinearContext X
      (p.left.map (adaptedLowBasisValue X L evaluation) ++
        p.relation.value X L evaluation ::
          d.left.map (adaptedLowBasisValue X L evaluation))
      (d.right.map (adaptedLowBasisValue X L evaluation))) hcoeff
  rw [adaptedEnvelopingLinearContext_finsupp_sum] at hcontext
  have hcorrection :
      (adaptedLowBracketCoefficients X L evaluation d.x d.y hweight).sum
          (fun z c ↦ c •
            (p.bracketRight X L evaluation d z).value X L evaluation) =
        adaptedEnvelopingLinearContext X
          (p.left.map (adaptedLowBasisValue X L evaluation) ++
            p.relation.value X L evaluation ::
              d.left.map (adaptedLowBasisValue X L evaluation))
          (d.right.map (adaptedLowBasisValue X L evaluation))
          ⁅adaptedLowBasisValue X L evaluation d.x,
            adaptedLowBasisValue X L evaluation d.y⁆ := by
    rw [← hcontext]
    apply Finsupp.sum_congr
    intro z hz
    simp [AdaptedSmithPlacedPacket.value,
      AdaptedSmithPlacedPacket.toAlgebraPacket,
      AdaptedSmithPlacedPacket.bracketRight,
      AdaptedSmithPlacedPacket.withFactors, AlgebraPacket.value,
      adaptedEnvelopingLinearContext, List.map_append, envelopingWord_append]
    noncomm_ring
  rw [hcorrection, adaptedEnvelopingLinearContext_apply, LieHom.map_lie]
  have hswap := AlgebraPacket.swap_right_value ℤ F evaluation.ker
    (p.left.map (adaptedLowBasisValue X L evaluation))
    (d.left.map (adaptedLowBasisValue X L evaluation))
    (d.right.map (adaptedLowBasisValue X L evaluation))
    (adaptedLowBasisValue X L evaluation d.x)
    (adaptedLowBasisValue X L evaluation d.y)
    (p.toAlgebraPacket X L evaluation).relation
  simp [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket,
    AdaptedSmithPlacedPacket.swapRight,
    AdaptedSmithPlacedPacket.withFactors, AlgebraPacket.value,
    List.map_append, hright] at hswap ⊢
  convert hswap using 1 <;> noncomm_ring

/-- Exact Smith normalization of a relation bracket after inserting it into arbitrary
surrounding enveloping words. -/
theorem adaptedNormalizedRelationBracket_value
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X) (x : Factor)
    (left right : List Factor) :
    adaptedEnvelopingLinearContext X
        (left.map (adaptedLowBasisValue X L evaluation))
        (right.map (adaptedLowBasisValue X L evaluation))
        ⁅adaptedLowRelationRow X L evaluation i,
          adaptedLowBasisValue X L evaluation x⁆ =
      (adaptedLowRelationBracketRowCoefficients X L evaluation i x).sum
          (fun j c ↦ c •
            (p.withRow X L evaluation j left right).value X L evaluation) +
        (p.withHigh X L evaluation
          (adaptedLowRelationBracketWeightFiveRemainder X L evaluation i x)
          (adaptedLowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
          left right).value X L evaluation := by
  classical
  let ctx := adaptedEnvelopingLinearContext X
    (left.map (adaptedLowBasisValue X L evaluation))
    (right.map (adaptedLowBasisValue X L evaluation))
  have hrelation :=
    adaptedLowRelationRow_bracket_eq_rows_add_weightFiveRemainder
      X L evaluation i x
  have hcontext := congrArg ctx hrelation
  change ctx ⁅adaptedLowRelationRow X L evaluation i,
      adaptedLowBasisValue X L evaluation x⁆ = _
  rw [hcontext, map_add, adaptedEnvelopingLinearContext_finsupp_sum]
  congr 1

/-- Crossing the final left factor through a normalized Smith row preserves the exact value,
including all renormalized row coefficients and the terminal weight-five remainder. -/
theorem adaptedMoveLeftExpansion_value
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (front : List Factor) (i : AdaptedLowRelationRowIndex X)
    (x : Factor)
    (hleft : p.left = front ++ [x])
    (hrow : p.relation = .row i) :
    p.value X L evaluation =
      ((adaptedMoveLeftExpansion X L evaluation p front i x).map
        (fun q ↦ q.1 • q.2.value X L evaluation)).sum := by
  classical
  let rows :=
    (adaptedLowRelationBracketRowCoefficients X L evaluation i x).sum
      (fun j c ↦ c •
        (p.leftRelationCorrection X L evaluation front j).value X L evaluation)
  let high := (p.leftHighCorrection X L evaluation front i x).value X L evaluation
  have hnormalized := adaptedNormalizedRelationBracket_value X L evaluation p i x front p.right
  change adaptedEnvelopingLinearContext X
      (front.map (adaptedLowBasisValue X L evaluation))
      (p.right.map (adaptedLowBasisValue X L evaluation))
      ⁅adaptedLowRelationRow X L evaluation i,
        adaptedLowBasisValue X L evaluation x⁆ = rows + high at hnormalized
  let ctx := adaptedEnvelopingLinearContext X
    (front.map (adaptedLowBasisValue X L evaluation))
    (p.right.map (adaptedLowBasisValue X L evaluation))
  have hskew :
      ctx ⁅adaptedLowBasisValue X L evaluation x,
          adaptedLowRelationRow X L evaluation i⁆ =
        -ctx ⁅adaptedLowRelationRow X L evaluation i,
          adaptedLowBasisValue X L evaluation x⁆ := by
    rw [← lie_skew, map_neg]
  have hmove :
      p.value X L evaluation =
        (p.moveLeftAcross X L evaluation front x).value X L evaluation +
          ctx ⁅adaptedLowBasisValue X L evaluation x,
            adaptedLowRelationRow X L evaluation i⁆ := by
    simp only [AdaptedSmithPlacedPacket.value,
      AdaptedSmithPlacedPacket.toAlgebraPacket,
      AdaptedSmithPlacedPacket.moveLeftAcross,
      AdaptedSmithPlacedPacket.withFactors,
      AlgebraPacket.value,
      FiniteCollectedRelation.value, ctx, adaptedEnvelopingLinearContext,
      hleft, hrow, List.map_append, List.map_cons, List.map_nil,
      envelopingWord_append, envelopingWord_cons, envelopingWord_nil,
      mul_one]
    change envelopingWord ℤ F (front.map (adaptedLowBasisValue X L evaluation)) *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedLowBasisValue X L evaluation x) *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedLowRelationRow X L evaluation i) *
          envelopingWord ℤ F (p.right.map (adaptedLowBasisValue X L evaluation)) = _
    calc
      _ = (envelopingWord ℤ F (front.map (adaptedLowBasisValue X L evaluation)) *
            (UniversalEnvelopingAlgebra.ι ℤ (adaptedLowBasisValue X L evaluation x) *
              UniversalEnvelopingAlgebra.ι ℤ
                (adaptedLowRelationRow X L evaluation i))) *
            envelopingWord ℤ F (p.right.map (adaptedLowBasisValue X L evaluation)) := by
          noncomm_ring
      _ = _ := by
        rw [iota_mul_iota_swap]
        noncomm_ring
  simp only [adaptedMoveLeftExpansion, List.map_cons, List.sum_cons,
    List.map_append, List.sum_append, one_smul, List.map_nil,
    List.map_singleton, List.sum_singleton, List.sum_nil, add_zero,
    neg_one_zsmul]
  rw [finsuppTaggedList_neg_value_sum]
  rw [hmove, hskew, hnormalized]
  abel

/-- Crossing the first right factor through a normalized Smith row preserves the exact value,
with the positive bracket `[r,x]` normalized immediately. -/
theorem adaptedMoveRightExpansion_value
    (evaluation : LieHom ℤ F L)
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (i : AdaptedLowRelationRowIndex X) (x : Factor)
    (tail : List Factor)
    (hright : p.right = x :: tail)
    (hrow : p.relation = .row i) :
    p.value X L evaluation =
      ((adaptedMoveRightExpansion X L evaluation p i x tail).map
        (fun q ↦ q.1 • q.2.value X L evaluation)).sum := by
  classical
  let rows :=
    (adaptedLowRelationBracketRowCoefficients X L evaluation i x).sum
      (fun j c ↦ c •
        (p.rightRelationCorrection X L evaluation tail j).value X L evaluation)
  let high := (p.rightHighCorrection X L evaluation tail i x).value X L evaluation
  have hnormalized := adaptedNormalizedRelationBracket_value X L evaluation p i x p.left tail
  change adaptedEnvelopingLinearContext X
      (p.left.map (adaptedLowBasisValue X L evaluation))
      (tail.map (adaptedLowBasisValue X L evaluation))
      ⁅adaptedLowRelationRow X L evaluation i,
        adaptedLowBasisValue X L evaluation x⁆ = rows + high at hnormalized
  let ctx := adaptedEnvelopingLinearContext X
    (p.left.map (adaptedLowBasisValue X L evaluation))
    (tail.map (adaptedLowBasisValue X L evaluation))
  have hmove :
      p.value X L evaluation =
        (p.moveRightAcross X L evaluation x tail).value X L evaluation +
          ctx ⁅adaptedLowRelationRow X L evaluation i,
            adaptedLowBasisValue X L evaluation x⁆ := by
    simp only [AdaptedSmithPlacedPacket.value,
      AdaptedSmithPlacedPacket.toAlgebraPacket,
      AdaptedSmithPlacedPacket.moveRightAcross,
      AdaptedSmithPlacedPacket.withFactors,
      AlgebraPacket.value, FiniteCollectedRelation.value,
      ctx, adaptedEnvelopingLinearContext, hright, hrow,
      List.map_append, List.map_cons, List.map_nil,
      envelopingWord_append, envelopingWord_cons, envelopingWord_nil,
      mul_one]
    change envelopingWord ℤ F (p.left.map (adaptedLowBasisValue X L evaluation)) *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedLowRelationRow X L evaluation i) *
          (UniversalEnvelopingAlgebra.ι ℤ (adaptedLowBasisValue X L evaluation x) *
            envelopingWord ℤ F (tail.map (adaptedLowBasisValue X L evaluation))) =
      envelopingWord ℤ F (p.left.map (adaptedLowBasisValue X L evaluation)) *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedLowBasisValue X L evaluation x) *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedLowRelationRow X L evaluation i) *
          envelopingWord ℤ F (tail.map (adaptedLowBasisValue X L evaluation)) +
        envelopingWord ℤ F (p.left.map (adaptedLowBasisValue X L evaluation)) *
          UniversalEnvelopingAlgebra.ι ℤ
            ⁅adaptedLowRelationRow X L evaluation i,
              adaptedLowBasisValue X L evaluation x⁆ *
          envelopingWord ℤ F (tail.map (adaptedLowBasisValue X L evaluation))
    calc
      _ = (envelopingWord ℤ F (p.left.map (adaptedLowBasisValue X L evaluation)) *
            (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedLowRelationRow X L evaluation i) *
              UniversalEnvelopingAlgebra.ι ℤ (adaptedLowBasisValue X L evaluation x))) *
            envelopingWord ℤ F (tail.map (adaptedLowBasisValue X L evaluation)) := by
          noncomm_ring
      _ = _ := by
        rw [iota_mul_iota_swap]
        noncomm_ring
  simp only [adaptedMoveRightExpansion, List.map_cons, List.sum_cons,
    List.map_append, List.sum_append, one_smul, List.map_nil,
    List.map_singleton, List.sum_singleton, List.sum_nil, add_zero,
    one_zsmul]
  rw [finsuppTaggedList_value_sum]
  rw [hmove, hnormalized]
  abel

end

end DegreeFive

end LieRings
