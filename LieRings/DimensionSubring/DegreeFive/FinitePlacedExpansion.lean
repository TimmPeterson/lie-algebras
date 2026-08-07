import LieRings.DimensionSubring.DegreeFive.FinitePlacedPackets

/-!
# One-step expansion of finite Smith-tagged packets

The expansion fixes a deterministic rewrite priority.  It first orders factors on the left,
then crosses the relation head with the adjacent factor when necessary, and finally orders the
right.  Every commutator is immediately expanded in the relevant finite homogeneous or Smith
basis.  Weight-five relation remainders are exact terminal terms.
-/

namespace LieRings

universe u v w

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X

/-- Convert a finitely supported coefficient family to the literal finite tagged list consumed
by `FiniteTaggedCollector`. -/
def finsuppTaggedList {I : Type u} {P : Type w}
    (c : I →₀ ℤ) (f : I → P) : List (ℤ × P) :=
  c.support.toList.map fun i ↦ (c i, f i)

theorem finsuppTaggedList_value_sum {I : Type u} {P : Type w}
    {A : Type*} [AddCommGroup A]
    (c : I →₀ ℤ) (f : I → P) (value : P → A) :
    ((finsuppTaggedList c f).map fun q ↦ q.1 • value q.2).sum =
      c.sum (fun i z ↦ z • value (f i)) := by
  classical
  simp [finsuppTaggedList, Finsupp.sum]

/-- Negating the integer tag negates the evaluated finite sum. -/
theorem finsuppTaggedList_neg_value_sum {I : Type u} {P : Type w}
    {A : Type*} [AddCommGroup A]
    (c : I →₀ ℤ) (f : I → P) (value : P → A) :
    (((finsuppTaggedList c f).map fun q ↦ (-q.1, q.2)).map
        (fun q ↦ q.1 • value q.2)).sum =
      -c.sum (fun i z ↦ z • value (f i)) := by
  classical
  have hlist : ∀ xs : List (ℤ × P),
      (((xs.map fun q ↦ (-q.1, q.2)).map
          (fun q ↦ q.1 • value q.2)).sum) =
        -((xs.map fun q ↦ q.1 • value q.2).sum) := by
    intro xs
    induction xs with
    | nil => simp
    | cons q xs ih =>
        simp only [List.map_cons, List.sum_cons, neg_smul]
        rw [ih]
        abel
  rw [hlist, finsuppTaggedList_value_sum]

/-- Split a nonempty list into its initial segment and final entry. -/
def splitLast? {A : Type*} (xs : List A) : Option (List A × A) :=
  xs.getLast?.map fun last ↦ (xs.dropLast, last)

theorem splitLast?_eq_some {A : Type*} {xs front : List A} {last : A}
    (h : splitLast? xs = some (front, last)) : xs = front ++ [last] := by
  unfold splitLast? at h
  cases hlast : xs.getLast? with
  | none => simp [hlast] at h
  | some y =>
      simp only [hlast, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact (List.dropLast_append_getLast? y (by simp [hlast])).symm

variable (evaluation : LieHom ℤ F L)

local notation "Packet" => FiniteSmithPlacedPacket X L evaluation
local notation "Factor" => LowHomogeneousBasisIndex X
local notation "Row" => LowRelationSmithRowIndex X L evaluation

/-- Replace an ordinary inverted pair by the ordered pair. -/
def FiniteSmithPlacedPacket.swapLeft
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor) : FiniteSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation (d.left ++ d.y :: d.x :: d.right) p.right

/-- One basis summand of the ordinary bracket correction on the left. -/
def FiniteSmithPlacedPacket.bracketLeft
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor) (z : Factor) :
    FiniteSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation (d.left ++ z :: d.right) p.right

/-- Replace an ordinary inverted pair by the ordered pair on the right. -/
def FiniteSmithPlacedPacket.swapRight
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor) : FiniteSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation p.left (d.left ++ d.y :: d.x :: d.right)

/-- One basis summand of the ordinary bracket correction on the right. -/
def FiniteSmithPlacedPacket.bracketRight
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor) (z : Factor) :
    FiniteSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation p.left (d.left ++ z :: d.right)

/-- Move the last left factor to the right of the relation. -/
def FiniteSmithPlacedPacket.moveLeftAcross
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (front : List Factor) (x : Factor) : FiniteSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation front (x :: p.right)

/-- A normalized row summand of the correction created while moving the last left factor. -/
def FiniteSmithPlacedPacket.leftRelationCorrection
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (front : List Factor) (j : LowRelationSmithRowIndex X L evaluation) :
    FiniteSmithPlacedPacket X L evaluation :=
  p.withRow X L evaluation j front p.right

/-- The exact weight-five correction created while moving the last left factor. -/
def FiniteSmithPlacedPacket.leftHighCorrection
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (front : List Factor) (i : LowRelationSmithRowIndex X L evaluation)
    (x : Factor) : FiniteSmithPlacedPacket X L evaluation :=
  p.withHigh X L evaluation
    (lowRelationBracketWeightFiveRemainder X L evaluation i x)
    (lowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
    front p.right

/-- Move the first right factor to the left of the relation. -/
def FiniteSmithPlacedPacket.moveRightAcross
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (x : Factor) (tail : List Factor) : FiniteSmithPlacedPacket X L evaluation :=
  p.withFactors X L evaluation (p.left ++ [x]) tail

/-- A normalized row summand of the correction created while moving the first right factor. -/
def FiniteSmithPlacedPacket.rightRelationCorrection
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (tail : List Factor) (j : LowRelationSmithRowIndex X L evaluation) :
    FiniteSmithPlacedPacket X L evaluation :=
  p.withRow X L evaluation j p.left tail

/-- The exact weight-five correction created while moving the first right factor. -/
def FiniteSmithPlacedPacket.rightHighCorrection
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (tail : List Factor) (i : LowRelationSmithRowIndex X L evaluation)
    (x : Factor) : FiniteSmithPlacedPacket X L evaluation :=
  p.withHigh X L evaluation
    (lowRelationBracketWeightFiveRemainder X L evaluation i x)
    (lowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
    p.left tail

/-- Ordinary left-factor PBW expansion. -/
def leftSwapExpansion (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) (d : AdjacentInversionData Factor)
    (hweight : lowHomogeneousBasisWeight X d.x +
      lowHomogeneousBasisWeight X d.y ≤ 4) :
    List (ℤ × FiniteSmithPlacedPacket X L evaluation) :=
  (1, p.swapLeft X L evaluation d) ::
    finsuppTaggedList (lowHomogeneousBracketCoefficients X d.x d.y hweight)
      (p.bracketLeft X L evaluation d)

/-- Ordinary right-factor PBW expansion. -/
def rightSwapExpansion (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) (d : AdjacentInversionData Factor)
    (hweight : lowHomogeneousBasisWeight X d.x +
      lowHomogeneousBasisWeight X d.y ≤ 4) :
    List (ℤ × FiniteSmithPlacedPacket X L evaluation) :=
  (1, p.swapRight X L evaluation d) ::
    finsuppTaggedList (lowHomogeneousBracketCoefficients X d.x d.y hweight)
      (p.bracketRight X L evaluation d)

/-- Expansion for `x ρ = ρ x - [ρ,x]`, including immediate Smith normalization. -/
def moveLeftExpansion (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) (front : List Factor)
    (i : LowRelationSmithRowIndex X L evaluation) (x : Factor) :
    List (ℤ × FiniteSmithPlacedPacket X L evaluation) :=
  (1, p.moveLeftAcross X L evaluation front x) ::
    (finsuppTaggedList (lowRelationBracketRowCoefficients X L evaluation i x)
      (p.leftRelationCorrection X L evaluation front)).map
        (fun q ↦ (-q.1, q.2)) ++
    [(-1, p.leftHighCorrection X L evaluation front i x)]

/-- Expansion for `ρ x = x ρ + [ρ,x]`, including immediate Smith normalization. -/
def moveRightExpansion (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation) (x : Factor) (tail : List Factor) :
    List (ℤ × FiniteSmithPlacedPacket X L evaluation) :=
  (1, p.moveRightAcross X L evaluation x tail) ::
    finsuppTaggedList (lowRelationBracketRowCoefficients X L evaluation i x)
      (p.rightRelationCorrection X L evaluation tail) ++
    [(1, p.rightHighCorrection X L evaluation tail i x)]

/-- Multiplication by fixed enveloping words on both sides is additive in the marked Lie
factor.  This is the common linear context used to transport all finite coefficient
expansions into packet values. -/
def envelopingLinearContext (left right : List F) : F →+ UEA ℤ F where
  toFun z := envelopingWord ℤ F left *
    UniversalEnvelopingAlgebra.ι ℤ z * envelopingWord ℤ F right
  map_zero' := by simp
  map_add' x y := by simp [map_add, mul_add, add_mul]

@[simp]
theorem envelopingLinearContext_apply (left right : List F) (z : F) :
    envelopingLinearContext X left right z =
      envelopingWord ℤ F left * UniversalEnvelopingAlgebra.ι ℤ z *
        envelopingWord ℤ F right :=
  rfl

/-- Evaluation commutes with a finite integral coefficient expansion in the marked slot. -/
theorem envelopingLinearContext_finsupp_sum {I : Type*}
    (left right : List F) (c : I →₀ ℤ) (f : I → F) :
    envelopingLinearContext X left right
        (c.sum (fun i z ↦ z • f i)) =
      c.sum (fun i z ↦ z • envelopingLinearContext X left right (f i)) := by
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  exact map_zsmul (envelopingLinearContext X left right) (c i) (f i)

/-- The ordinary left PBW expansion preserves the exact enveloping-algebra value. -/
theorem leftSwapExpansion_value
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor)
    (hleft : p.left = d.left ++ d.x :: d.y :: d.right)
    (hweight : lowHomogeneousBasisWeight X d.x +
      lowHomogeneousBasisWeight X d.y ≤ 4) :
    p.value X L evaluation =
      ((leftSwapExpansion X L evaluation p d hweight).map
        (fun q ↦ q.1 • q.2.value X L evaluation)).sum := by
  classical
  change p.value X L evaluation =
    (1 : ℤ) • (p.swapLeft X L evaluation d).value X L evaluation +
      ((finsuppTaggedList
        (lowHomogeneousBracketCoefficients X d.x d.y hweight)
        (p.bracketLeft X L evaluation d)).map
          (fun q ↦ q.1 • q.2.value X L evaluation)).sum
  rw [one_smul, finsuppTaggedList_value_sum]
  have hcoeff := lowHomogeneousBracketCoefficients_sum X d.x d.y hweight
  have hcontext := congrArg
    (envelopingLinearContext X
      (d.left.map (lowHomogeneousBasisValue X))
      (d.right.map (lowHomogeneousBasisValue X) ++
        p.relation.value X L evaluation ::
          p.right.map (lowHomogeneousBasisValue X))) hcoeff
  rw [envelopingLinearContext_finsupp_sum] at hcontext
  have hcorrection :
      (lowHomogeneousBracketCoefficients X d.x d.y hweight).sum
          (fun z c ↦ c •
            (p.bracketLeft X L evaluation d z).value X L evaluation) =
        envelopingLinearContext X
          (d.left.map (lowHomogeneousBasisValue X))
          (d.right.map (lowHomogeneousBasisValue X) ++
            p.relation.value X L evaluation ::
              p.right.map (lowHomogeneousBasisValue X))
          ⁅lowHomogeneousBasisValue X d.x,
            lowHomogeneousBasisValue X d.y⁆ := by
    rw [← hcontext]
    apply Finsupp.sum_congr
    intro z hz
    simp [FiniteSmithPlacedPacket.value,
      FiniteSmithPlacedPacket.toAlgebraPacket,
      FiniteSmithPlacedPacket.bracketLeft,
      FiniteSmithPlacedPacket.withFactors, AlgebraPacket.value,
      envelopingLinearContext, List.map_append, envelopingWord_append]
    noncomm_ring
  rw [hcorrection]
  rw [envelopingLinearContext_apply]
  rw [LieHom.map_lie]
  have hswap := AlgebraPacket.swap_left_value ℤ F evaluation.ker
    (d.left.map (lowHomogeneousBasisValue X))
    (d.right.map (lowHomogeneousBasisValue X))
    (p.right.map (lowHomogeneousBasisValue X))
    (lowHomogeneousBasisValue X d.x)
    (lowHomogeneousBasisValue X d.y)
    (p.toAlgebraPacket X L evaluation).relation
  simp [FiniteSmithPlacedPacket.value,
    FiniteSmithPlacedPacket.toAlgebraPacket,
    FiniteSmithPlacedPacket.swapLeft,
    FiniteSmithPlacedPacket.withFactors, AlgebraPacket.value,
    List.map_append, hleft] at hswap ⊢
  convert hswap using 1 <;> noncomm_ring

/-- The ordinary right PBW expansion preserves the exact enveloping-algebra value. -/
theorem rightSwapExpansion_value
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (d : AdjacentInversionData Factor)
    (hright : p.right = d.left ++ d.x :: d.y :: d.right)
    (hweight : lowHomogeneousBasisWeight X d.x +
      lowHomogeneousBasisWeight X d.y ≤ 4) :
    p.value X L evaluation =
      ((rightSwapExpansion X L evaluation p d hweight).map
        (fun q ↦ q.1 • q.2.value X L evaluation)).sum := by
  classical
  change p.value X L evaluation =
    (1 : ℤ) • (p.swapRight X L evaluation d).value X L evaluation +
      ((finsuppTaggedList
        (lowHomogeneousBracketCoefficients X d.x d.y hweight)
        (p.bracketRight X L evaluation d)).map
          (fun q ↦ q.1 • q.2.value X L evaluation)).sum
  rw [one_smul, finsuppTaggedList_value_sum]
  have hcoeff := lowHomogeneousBracketCoefficients_sum X d.x d.y hweight
  have hcontext := congrArg
    (envelopingLinearContext X
      (p.left.map (lowHomogeneousBasisValue X) ++
        p.relation.value X L evaluation ::
          d.left.map (lowHomogeneousBasisValue X))
      (d.right.map (lowHomogeneousBasisValue X))) hcoeff
  rw [envelopingLinearContext_finsupp_sum] at hcontext
  have hcorrection :
      (lowHomogeneousBracketCoefficients X d.x d.y hweight).sum
          (fun z c ↦ c •
            (p.bracketRight X L evaluation d z).value X L evaluation) =
        envelopingLinearContext X
          (p.left.map (lowHomogeneousBasisValue X) ++
            p.relation.value X L evaluation ::
              d.left.map (lowHomogeneousBasisValue X))
          (d.right.map (lowHomogeneousBasisValue X))
          ⁅lowHomogeneousBasisValue X d.x,
            lowHomogeneousBasisValue X d.y⁆ := by
    rw [← hcontext]
    apply Finsupp.sum_congr
    intro z hz
    simp [FiniteSmithPlacedPacket.value,
      FiniteSmithPlacedPacket.toAlgebraPacket,
      FiniteSmithPlacedPacket.bracketRight,
      FiniteSmithPlacedPacket.withFactors, AlgebraPacket.value,
      envelopingLinearContext, List.map_append, envelopingWord_append]
    noncomm_ring
  rw [hcorrection, envelopingLinearContext_apply, LieHom.map_lie]
  have hswap := AlgebraPacket.swap_right_value ℤ F evaluation.ker
    (p.left.map (lowHomogeneousBasisValue X))
    (d.left.map (lowHomogeneousBasisValue X))
    (d.right.map (lowHomogeneousBasisValue X))
    (lowHomogeneousBasisValue X d.x)
    (lowHomogeneousBasisValue X d.y)
    (p.toAlgebraPacket X L evaluation).relation
  simp [FiniteSmithPlacedPacket.value,
    FiniteSmithPlacedPacket.toAlgebraPacket,
    FiniteSmithPlacedPacket.swapRight,
    FiniteSmithPlacedPacket.withFactors, AlgebraPacket.value,
    List.map_append, hright] at hswap ⊢
  convert hswap using 1 <;> noncomm_ring

/-- Exact Smith normalization of a relation bracket after inserting it into arbitrary
surrounding enveloping words. -/
theorem normalizedRelationBracket_value
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation) (x : Factor)
    (left right : List Factor) :
    envelopingLinearContext X
        (left.map (lowHomogeneousBasisValue X))
        (right.map (lowHomogeneousBasisValue X))
        ⁅lowRelationSmithRow X L evaluation i,
          lowHomogeneousBasisValue X x⁆ =
      (lowRelationBracketRowCoefficients X L evaluation i x).sum
          (fun j c ↦ c •
            (p.withRow X L evaluation j left right).value X L evaluation) +
        (p.withHigh X L evaluation
          (lowRelationBracketWeightFiveRemainder X L evaluation i x)
          (lowRelationBracketWeightFiveRemainder_mem_lieHigh X L evaluation i x)
          left right).value X L evaluation := by
  classical
  let ctx := envelopingLinearContext X
    (left.map (lowHomogeneousBasisValue X))
    (right.map (lowHomogeneousBasisValue X))
  have hrelation :=
    lowRelationSmithRow_bracket_eq_rows_add_weightFiveRemainder
      X L evaluation i x
  have hcontext := congrArg ctx hrelation
  change ctx ⁅lowRelationSmithRow X L evaluation i,
      lowHomogeneousBasisValue X x⁆ = _
  rw [hcontext, map_add, envelopingLinearContext_finsupp_sum]
  congr 1

/-- Crossing the final left factor through a normalized Smith row preserves the exact value,
including all renormalized row coefficients and the terminal weight-five remainder. -/
theorem moveLeftExpansion_value
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (front : List Factor) (i : LowRelationSmithRowIndex X L evaluation)
    (x : Factor)
    (hleft : p.left = front ++ [x])
    (hrow : p.relation = .row i) :
    p.value X L evaluation =
      ((moveLeftExpansion X L evaluation p front i x).map
        (fun q ↦ q.1 • q.2.value X L evaluation)).sum := by
  classical
  let rows :=
    (lowRelationBracketRowCoefficients X L evaluation i x).sum
      (fun j c ↦ c •
        (p.leftRelationCorrection X L evaluation front j).value X L evaluation)
  let high := (p.leftHighCorrection X L evaluation front i x).value X L evaluation
  have hnormalized := normalizedRelationBracket_value X L evaluation p i x front p.right
  change envelopingLinearContext X
      (front.map (lowHomogeneousBasisValue X))
      (p.right.map (lowHomogeneousBasisValue X))
      ⁅lowRelationSmithRow X L evaluation i,
        lowHomogeneousBasisValue X x⁆ = rows + high at hnormalized
  let ctx := envelopingLinearContext X
    (front.map (lowHomogeneousBasisValue X))
    (p.right.map (lowHomogeneousBasisValue X))
  have hskew :
      ctx ⁅lowHomogeneousBasisValue X x,
          lowRelationSmithRow X L evaluation i⁆ =
        -ctx ⁅lowRelationSmithRow X L evaluation i,
          lowHomogeneousBasisValue X x⁆ := by
    rw [← lie_skew, map_neg]
  have hmove :
      p.value X L evaluation =
        (p.moveLeftAcross X L evaluation front x).value X L evaluation +
          ctx ⁅lowHomogeneousBasisValue X x,
            lowRelationSmithRow X L evaluation i⁆ := by
    simp only [FiniteSmithPlacedPacket.value,
      FiniteSmithPlacedPacket.toAlgebraPacket,
      FiniteSmithPlacedPacket.moveLeftAcross,
      FiniteSmithPlacedPacket.withFactors,
      AlgebraPacket.value,
      FiniteCollectedRelation.value, ctx, envelopingLinearContext,
      hleft, hrow, List.map_append, List.map_cons, List.map_nil,
      envelopingWord_append, envelopingWord_cons, envelopingWord_nil,
      mul_one]
    change envelopingWord ℤ F (front.map (lowHomogeneousBasisValue X)) *
          UniversalEnvelopingAlgebra.ι ℤ (lowHomogeneousBasisValue X x) *
          UniversalEnvelopingAlgebra.ι ℤ (lowRelationSmithRow X L evaluation i) *
          envelopingWord ℤ F (p.right.map (lowHomogeneousBasisValue X)) = _
    calc
      _ = (envelopingWord ℤ F (front.map (lowHomogeneousBasisValue X)) *
            (UniversalEnvelopingAlgebra.ι ℤ (lowHomogeneousBasisValue X x) *
              UniversalEnvelopingAlgebra.ι ℤ
                (lowRelationSmithRow X L evaluation i))) *
            envelopingWord ℤ F (p.right.map (lowHomogeneousBasisValue X)) := by
          noncomm_ring
      _ = _ := by
        rw [iota_mul_iota_swap]
        noncomm_ring
  simp only [moveLeftExpansion, List.map_cons, List.sum_cons,
    List.map_append, List.sum_append, one_smul, List.map_nil,
    List.map_singleton, List.sum_singleton, List.sum_nil, add_zero,
    neg_one_zsmul]
  rw [finsuppTaggedList_neg_value_sum]
  rw [hmove, hskew, hnormalized]
  abel

/-- Crossing the first right factor through a normalized Smith row preserves the exact value,
with the positive bracket `[r,x]` normalized immediately. -/
theorem moveRightExpansion_value
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (i : LowRelationSmithRowIndex X L evaluation) (x : Factor)
    (tail : List Factor)
    (hright : p.right = x :: tail)
    (hrow : p.relation = .row i) :
    p.value X L evaluation =
      ((moveRightExpansion X L evaluation p i x tail).map
        (fun q ↦ q.1 • q.2.value X L evaluation)).sum := by
  classical
  let rows :=
    (lowRelationBracketRowCoefficients X L evaluation i x).sum
      (fun j c ↦ c •
        (p.rightRelationCorrection X L evaluation tail j).value X L evaluation)
  let high := (p.rightHighCorrection X L evaluation tail i x).value X L evaluation
  have hnormalized := normalizedRelationBracket_value X L evaluation p i x p.left tail
  change envelopingLinearContext X
      (p.left.map (lowHomogeneousBasisValue X))
      (tail.map (lowHomogeneousBasisValue X))
      ⁅lowRelationSmithRow X L evaluation i,
        lowHomogeneousBasisValue X x⁆ = rows + high at hnormalized
  let ctx := envelopingLinearContext X
    (p.left.map (lowHomogeneousBasisValue X))
    (tail.map (lowHomogeneousBasisValue X))
  have hmove :
      p.value X L evaluation =
        (p.moveRightAcross X L evaluation x tail).value X L evaluation +
          ctx ⁅lowRelationSmithRow X L evaluation i,
            lowHomogeneousBasisValue X x⁆ := by
    simp only [FiniteSmithPlacedPacket.value,
      FiniteSmithPlacedPacket.toAlgebraPacket,
      FiniteSmithPlacedPacket.moveRightAcross,
      FiniteSmithPlacedPacket.withFactors,
      AlgebraPacket.value, FiniteCollectedRelation.value,
      ctx, envelopingLinearContext, hright, hrow,
      List.map_append, List.map_cons, List.map_nil,
      envelopingWord_append, envelopingWord_cons, envelopingWord_nil,
      mul_one]
    change envelopingWord ℤ F (p.left.map (lowHomogeneousBasisValue X)) *
          UniversalEnvelopingAlgebra.ι ℤ (lowRelationSmithRow X L evaluation i) *
          (UniversalEnvelopingAlgebra.ι ℤ (lowHomogeneousBasisValue X x) *
            envelopingWord ℤ F (tail.map (lowHomogeneousBasisValue X))) =
      envelopingWord ℤ F (p.left.map (lowHomogeneousBasisValue X)) *
          UniversalEnvelopingAlgebra.ι ℤ (lowHomogeneousBasisValue X x) *
          UniversalEnvelopingAlgebra.ι ℤ (lowRelationSmithRow X L evaluation i) *
          envelopingWord ℤ F (tail.map (lowHomogeneousBasisValue X)) +
        envelopingWord ℤ F (p.left.map (lowHomogeneousBasisValue X)) *
          UniversalEnvelopingAlgebra.ι ℤ
            ⁅lowRelationSmithRow X L evaluation i,
              lowHomogeneousBasisValue X x⁆ *
          envelopingWord ℤ F (tail.map (lowHomogeneousBasisValue X))
    calc
      _ = (envelopingWord ℤ F (p.left.map (lowHomogeneousBasisValue X)) *
            (UniversalEnvelopingAlgebra.ι ℤ
                (lowRelationSmithRow X L evaluation i) *
              UniversalEnvelopingAlgebra.ι ℤ (lowHomogeneousBasisValue X x))) *
            envelopingWord ℤ F (tail.map (lowHomogeneousBasisValue X)) := by
          noncomm_ring
      _ = _ := by
        rw [iota_mul_iota_swap]
        noncomm_ring
  simp only [moveRightExpansion, List.map_cons, List.sum_cons,
    List.map_append, List.sum_append, one_smul, List.map_nil,
    List.map_singleton, List.sum_singleton, List.sum_nil, add_zero,
    one_zsmul]
  rw [finsuppTaggedList_value_sum]
  rw [hmove, hnormalized]
  abel

end

end DegreeFive

end LieRings
