import LieRings.DimensionSubring.DegreeFive.CoordinateSymplectic
import LieRings.DimensionSubring.DegreeFive.SemanticCollector

/-!
# Coordinate PBW collection in degree five

This file formalizes the coefficient-comparison part of Sections 2--4 of
`complete_proof_delta5_subset_gamma4.tex`, including the diagonal symmetric-square
coefficient omitted from Ionin's shorter class-three exposition.

The names `typeII`, `typeIII`, ..., `typeVII` below are the seven families in Ionin's
Definition 7.  The additional `sY` coordinates record the exceptional words
`s_k y_l`, `y_k s_l`, and `s_k y_k`.  These are precisely the terms that are invisible to
the `x_i y_k` and `z` comparisons but contribute multiples of `e_k` and `e_l` to the
pure symmetric-square words.
-/

namespace LieRings

namespace DegreeFive

namespace Coordinate

open scoped BigOperators

noncomputable section

variable {I K : Type*} [Fintype I] [Fintype K] [LinearOrder I] [LinearOrder K]
variable {q : ℕ}

namespace Data

variable (D : Data I K q)

/-! ## The named normal words -/

/-- The seven normal relation-word families.  Coefficients of types V--VII are retained in
the normal form even though they do not enter the four decisive PBW coordinates. -/
inductive CoreWord where
  | typeI
  | typeII (i j : I)
  | typeIII (i : I) (k : K)
  | typeIV (i : I) (k : K)
  | typeV (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
  | typeVI (i j k : I) (hij : i < j) (hjk : j ≤ k)
  | typeVII (i j k : I) (hij : i ≤ j) (hjk : j < k)

/-- Exceptional weight-four words from Ionin's subgroup `K`.  The first two constructors
include the diagonal case and therefore record both `(C1)` and `(C2)`. -/
inductive ExceptionalWord where
  | sY (k l : K)
  | Ys (k l : K)
  | rXY (i j : I) (k : K)
  | XXs (i j : I) (k : K)
  | rZ (i : I)
  | Xt (i : I)

/-- The four PBW coordinates which survive the coefficient comparison.  `yy k l` is the
off-diagonal coordinate (it will only be projected under `k ≠ l`); keeping both orders here
avoids imposing an irrelevant order on the Smith basis of the degree-two component. -/
inductive RelevantCoordinate where
  | xy (i : I) (k : K)
  | z
  | yy (k l : K)
  | ySquare (k : K)
  deriving DecidableEq

/-- Contribution of one of the seven canonical relation words to the relevant PBW
coordinates.  These are the four displayed calculations immediately following `Theta` in the
coordinate proof.  Types V--VII have no relevant coordinate. -/
def coreWordContribution (w : @CoreWord I K _) : @RelevantCoordinate I K → ℤ := by
  classical
  exact fun c ↦ match w, c with
  | .typeI, .z => q
  | .typeII i j, .xy a k =>
      (if a = i then D.B j k else 0) -
        (if a = j then (D.dRatio i j : ℤ) * D.B i k else 0)
  | .typeII i j, .z =>
      (D.dRatio i j : ℤ) * (∑ k, D.B i k * D.G j k)
  | .typeIII i k, .xy a l =>
      if a = i ∧ l = k then (D.d i : ℤ) else 0
  | .typeIII i k, .yy a b =>
      -(if a = k then D.B i b else 0) -
        (if b = k then D.B i a else 0)
  | .typeIII i k, .ySquare a =>
      if a = k then -D.B i a else 0
  | .typeIV i k, .xy a l =>
      if a = i ∧ l = k then (D.e k : ℤ) else 0
  | _, _ => 0

/-- Contribution of an exceptional weight-four word.  Only the products of a degree-two
Smith relation with a named `y` can meet a pure `yy` coordinate. -/
def exceptionalWordContribution (w : @ExceptionalWord I K) :
    @RelevantCoordinate I K → ℤ := by
  classical
  exact fun c ↦ match w, c with
  | .sY k l, .yy a b => if a = k ∧ b = l then (D.e k : ℤ) else 0
  | .Ys k l, .yy a b => if a = k ∧ b = l then (D.e l : ℤ) else 0
  | .sY k l, .ySquare a => if k = l ∧ a = k then (D.e k : ℤ) else 0
  | .Ys k l, .ySquare a => if k = l ∧ a = k then (D.e k : ℤ) else 0
  | _, _ => 0

/-! ## Literal relation words

The following small free-associative syntax keeps the distinction between a relation word and
its collected PBW coordinates.  It is deliberately independent of a particular Lie algebra:
after adapted Smith bases have been chosen, every reduced presentation has these same words and
the same collection rules in the four coordinates of interest. -/

inductive AdaptedLetter where
  | x (i : I)
  | y (k : K)
  | z
  deriving DecidableEq

/-- Integral noncommutative polynomials in the adapted letters. -/
abbrev RawExpression := MonoidAlgebra ℤ (FreeMonoid (@AdaptedLetter I K))

/-- One literal associative word. -/
def rawWord (xs : List (@AdaptedLetter I K)) : @RawExpression I K :=
  Finsupp.single (FreeMonoid.ofList xs) 1

/-- A word with an integral coefficient, kept as a single monoid-algebra term. -/
def rawTerm (n : ℤ) (xs : List (@AdaptedLetter I K)) : @RawExpression I K :=
  Finsupp.single (FreeMonoid.ofList xs) n

/-- Opaque scalar multiplication, used so collection rewrites coefficients linearly rather than
turning them into constant noncommutative polynomials. -/
def rawScale (n : ℤ) (p : @RawExpression I K) : @RawExpression I K := n • p

@[simp]
theorem rawWord_mul_rawWord (xs ys : List (@AdaptedLetter I K)) :
    rawWord xs * rawWord ys = rawWord (xs ++ ys) := by
  classical
  simp [rawWord, MonoidAlgebra.single_mul_single]

@[simp]
theorem rawTerm_mul_rawTerm (a b : ℤ)
    (xs ys : List (@AdaptedLetter I K)) :
    rawTerm a xs * rawTerm b ys = rawTerm (a * b) (xs ++ ys) := by
  classical
  simp [rawTerm, MonoidAlgebra.single_mul_single]

@[simp]
theorem rawTerm_mul_rawWord (a : ℤ)
    (xs ys : List (@AdaptedLetter I K)) :
    rawTerm a xs * rawWord ys = rawTerm a (xs ++ ys) := by
  rw [show rawWord ys = rawTerm 1 ys by rfl, rawTerm_mul_rawTerm, mul_one]

@[simp]
theorem rawWord_mul_rawTerm (a : ℤ)
    (xs ys : List (@AdaptedLetter I K)) :
    rawWord xs * rawTerm a ys = rawTerm a (xs ++ ys) := by
  rw [show rawWord xs = rawTerm 1 xs by rfl, rawTerm_mul_rawTerm, one_mul]

/-- The lower-weight tails `c_i z` and `m_k z` in the adapted Smith relations.  They are kept
literally in the words even though the four relevant PBW projections do not depend on them. -/
structure RelationTails where
  c : I → ℤ
  m : K → ℤ

/-- `r_i = d_i x_i - B_i - c_i z`. -/
def rRelation (T : RelationTails (I := I) (K := K)) (i : I) : @RawExpression I K :=
  rawTerm (D.d i : ℤ) [.x i] -
    (∑ k, rawTerm (D.B i k) [.y k]) - rawTerm (T.c i) [.z]

/-- `s_k = e_k y_k - m_k z`. -/
def sRelation (T : RelationTails (I := I) (K := K)) (k : K) : @RawExpression I K :=
  rawTerm (D.e k : ℤ) [.y k] - rawTerm (T.m k) [.z]

/-- `t = qz`. -/
def tRelation : @RawExpression I K := rawTerm (q : ℤ) [.z]

/-- The literal relation product belonging to one of Ionin's seven normal families. -/
def coreWordExpression (T : RelationTails (I := I) (K := K))
    (w : @CoreWord I K _) : @RawExpression I K :=
  match w with
  | .typeI => tRelation (I := I) (K := K) (q := q)
  | .typeII i j =>
      rawScale (D.dRatio i j : ℤ) (rRelation D T i * rawWord [.x j]) -
        rawWord [.x i] * rRelation D T j
  | .typeIII i k => rRelation D T i * rawWord [.y k]
  | .typeIV i k => rawWord [.x i] * sRelation D T k
  | .typeV i j k _ _ => rRelation D T i * rawWord [.x j] * rawWord [.x k]
  | .typeVI i j k _ _ => rawWord [.x i] * rRelation D T j * rawWord [.x k]
  | .typeVII i j k _ _ => rawWord [.x i] * rawWord [.x j] * rRelation D T k

/-- The literal exceptional relation products used in the weight-four table. -/
def exceptionalWordExpression (T : RelationTails (I := I) (K := K))
    (w : @ExceptionalWord I K) : @RawExpression I K :=
  match w with
  | .sY k l => sRelation D T k * rawWord [.y l]
  | .Ys k l => rawWord [.y k] * sRelation D T l
  | .rXY i j k => rRelation D T i * rawWord [.x j, .y k]
  | .XXs i j k => rawWord [.x i, .x j] * sRelation D T k
  | .rZ i => rRelation D T i * rawWord [.z]
  | .Xt i => rawWord [.x i] * tRelation (I := I) (K := K) (q := q)

/-- PBW collection of one raw word in a relevant coordinate.  The only non-ordered case which
survives is `y_k x_i = x_i y_k - G_{ik}z`.  Products of named `y`'s are read symmetrically;
the degree-four bracket correction is a single Lie factor and hence invisible here. -/
def rawWordCoordinate (xs : List (@AdaptedLetter I K))
    (c : @RelevantCoordinate I K) : ℤ :=
  match xs, c with
  | [.x i, .y k], .xy a b => if a = i ∧ b = k then 1 else 0
  | [.y k, .x i], .xy a b => if a = i ∧ b = k then 1 else 0
  | [.y k, .x i], .z => -D.G i k
  | [.z], .z => 1
  | [.y a, .y b], .yy k l =>
      if k ≠ l ∧ ((a = k ∧ b = l) ∨ (a = l ∧ b = k)) then 1 else 0
  | [.y a, .y b], .ySquare k => if a = k ∧ b = k then 1 else 0
  | _, _ => 0

/-- Linear PBW-coordinate projection on raw relation polynomials. -/
def rawPBWProjection (c : @RelevantCoordinate I K) :
    (@RawExpression I K) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun w ↦ D.rawWordCoordinate w.toList c)

@[simp]
theorem rawPBWProjection_rawWord (xs : List (@AdaptedLetter I K))
    (c : @RelevantCoordinate I K) :
    D.rawPBWProjection c (rawWord xs) = D.rawWordCoordinate xs c := by
  classical
  unfold rawPBWProjection rawWord
  change (Finsupp.single (FreeMonoid.ofList xs) (1 : ℤ)).sum
    (fun w a ↦ a • D.rawWordCoordinate w.toList c) = _
  simp

@[simp]
theorem rawPBWProjection_rawTerm (n : ℤ)
    (xs : List (@AdaptedLetter I K)) (c : @RelevantCoordinate I K) :
    D.rawPBWProjection c (rawTerm n xs) = n * D.rawWordCoordinate xs c := by
  classical
  unfold rawPBWProjection rawTerm
  change (Finsupp.single (FreeMonoid.ofList xs) n).sum
    (fun w a ↦ a • D.rawWordCoordinate w.toList c) = _
  simp [smul_eq_mul]

@[simp]
theorem rawPBWProjection_rawScale (n : ℤ) (p : @RawExpression I K)
    (c : @RelevantCoordinate I K) :
    D.rawPBWProjection c (rawScale n p) = n * D.rawPBWProjection c p := by
  simpa only [rawScale, smul_eq_mul] using
    (map_smul (D.rawPBWProjection c) n p)

theorem rawExpression_intCast_mul (n : ℤ) (p : @RawExpression I K) :
    (n : @RawExpression I K) * p = n • p := by
  ext w
  simp

@[simp]
theorem rawPBWProjection_intCast_mul (n : ℤ) (p : @RawExpression I K)
    (c : @RelevantCoordinate I K) :
    D.rawPBWProjection c ((n : @RawExpression I K) * p) =
      n * D.rawPBWProjection c p := by
  rw [rawExpression_intCast_mul, map_smul]
  rfl

theorem rawExpression_natCast_mul (n : ℕ) (p : @RawExpression I K) :
    (n : @RawExpression I K) * p = (n : ℤ) • p := by
  ext w
  simp

@[simp]
theorem rawPBWProjection_natCast_mul (n : ℕ) (p : @RawExpression I K)
    (c : @RelevantCoordinate I K) :
    D.rawPBWProjection c ((n : @RawExpression I K) * p) =
      (n : ℤ) * D.rawPBWProjection c p := by
  rw [rawExpression_natCast_mul, map_smul]
  rfl

theorem rawExpression_mul_intCast_mul (p q' : @RawExpression I K) (n : ℤ) :
    p * ((n : @RawExpression I K) * q') =
      (n : @RawExpression I K) * (p * q') := by
  rw [rawExpression_intCast_mul, mul_smul_comm,
    rawExpression_intCast_mul]

theorem rawExpression_mul_natCast_mul (p q' : @RawExpression I K) (n : ℕ) :
    p * ((n : @RawExpression I K) * q') =
      (n : @RawExpression I K) * (p * q') := by
  rw [rawExpression_natCast_mul, mul_smul_comm,
    rawExpression_natCast_mul]

theorem rawExpression_intCast_mul_mul (p q' : @RawExpression I K) (n : ℤ) :
    ((n : @RawExpression I K) * p) * q' =
      (n : @RawExpression I K) * (p * q') := by
  rw [mul_assoc]

theorem rawExpression_natCast_mul_mul (p q' : @RawExpression I K) (n : ℕ) :
    ((n : @RawExpression I K) * p) * q' =
      (n : @RawExpression I K) * (p * q') := by
  rw [mul_assoc]

/-- A completely collected expression, with one integer coordinate for every family which
can affect `(B)`, `(Z)`, `(C1)`, or `(C2)`.  `u`, `v`, and `v'` are exactly the matrices in
the paper.  `t` is the coefficient of `qz`.  The two `sY` matrices record left and right
placements of the degree-two relations. -/
structure CollectedExpression (_D : Data I K q) where
  u : I → I → ℤ
  v : I → K → ℤ
  v' : I → K → ℤ
  t : ℤ
  sY : K → K → ℤ
  Ys : K → K → ℤ

/-- The integral entry of `B Gᵀ` before reduction modulo `q`. -/
def bgEntry (i j : I) : ℤ :=
  ∑ k, D.B i k * D.G j k

@[simp]
theorem intCast_bgEntry (i j : I) :
    (D.bgEntry i j : ZMod q) = D.gamma i j := by
  simp [bgEntry, gamma]

namespace CollectedExpression

variable (E : D.CollectedExpression)

/-- Coefficient of the ordered PBW monomial `x_i y_k`, formula (3.8)/(B). -/
def xyCoefficient (i : I) (k : K) : ℤ :=
  D.upperSkewMul E.u i k + (D.d i : ℤ) * E.v i k +
    E.v' i k * (D.e k : ℤ)

/-- Coefficient of the named degree-three basis vector `z`, formula (3.9)/(Z), including
the only possible ambiguity: an integral multiple of the relation `qz`. -/
def zCoefficient : ℤ :=
  (∑ ij ∈ upperPairs I,
      E.u ij.1 ij.2 * (D.dRatio ij.1 ij.2 : ℤ) * D.bgEntry ij.1 ij.2) +
    (q : ℤ) * E.t

/-- Pure off-diagonal symmetric-square coefficient.  The first summand is the contribution
of `-∑ v_{ik} B_i y_k`; the remaining two summands are exactly `s_k y_l` and `y_k s_l`.
This formula is valid without choosing an order on `K`. -/
def yyCoefficient (k l : K) : ℤ :=
  -(∑ i, (E.v i k * D.B i l + D.B i k * E.v i l)) +
    (D.e k : ℤ) * E.sY k l + (D.e l : ℤ) * E.Ys k l

/-- Diagonal symmetric-square coefficient.  This is the calculation absent from Ionin's
note and is the source of `(C2)`. -/
def ySquareCoefficient (k : K) : ℤ :=
  -(∑ i, E.v i k * D.B i k) +
    (D.e k : ℤ) * (E.sY k k + E.Ys k k)

/-- The literal sum of the relevant coordinates of all named normal words.  Thus this is not
an assumed matrix formula: it is obtained by summing the word-by-word PBW contributions above
with the coefficients `u`, `v`, `v'`, `t`, `sY`, and `Ys`. -/
def explicitWordSum (c : @RelevantCoordinate I K) : ℤ :=
  E.t * coreWordContribution D .typeI c +
    (∑ ij ∈ upperPairs I,
      E.u ij.1 ij.2 * coreWordContribution D (.typeII ij.1 ij.2) c) +
    (∑ i, ∑ k, E.v i k * coreWordContribution D (.typeIII i k) c) +
    (∑ i, ∑ k, E.v' i k * coreWordContribution D (.typeIV i k) c) +
    (∑ k, ∑ l, E.sY k l * exceptionalWordContribution D (.sY k l) c) +
    ∑ k, ∑ l, E.Ys k l * exceptionalWordContribution D (.Ys k l) c

@[simp]
theorem sum_mul_indicator (a : K) (f : K → ℤ) (c : ℤ) :
    (∑ x, f x * (if a = x then c else 0)) = f a * c := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro x hx hxa
    simp [Ne.symm hxa]
  · simp

@[simp]
theorem sum_sum_indicator (a b : K) (f : K → K → ℤ) :
    (∑ x, ∑ y, if a = x ∧ b = y then f x y else 0) = f a b := by
  classical
  have houter :
      (∑ x, ∑ y, if a = x ∧ b = y then f x y else 0) =
        ∑ y, if a = a ∧ b = y then f a y else 0 := by
    apply Finset.sum_eq_single a
    · intro x hx hxa
      simp [Ne.symm hxa]
    · simp
  rw [houter]
  simp only [true_and]
  rw [Finset.sum_eq_single b]
  · simp
  · intro y hy hyb
    simp [Ne.symm hyb]
  · simp

@[simp]
theorem sum_sum_indicator_mixed (a : I) (b : K) (f : I → K → ℤ) :
    (∑ x, ∑ y, if a = x ∧ b = y then f x y else 0) = f a b := by
  classical
  have houter :
      (∑ x, ∑ y, if a = x ∧ b = y then f x y else 0) =
        ∑ y, if a = a ∧ b = y then f a y else 0 := by
    apply Finset.sum_eq_single a
    · intro x hx hxa
      simp [Ne.symm hxa]
    · simp
  rw [houter]
  simp only [true_and]
  rw [Finset.sum_eq_single b]
  · simp
  · intro y hy hyb
    simp [Ne.symm hyb]
  · simp

@[simp]
theorem sum_sum_diagonal_indicator (a : K) (f : K → K → ℤ) :
    (∑ x, ∑ y, if x = y ∧ a = x then f x y else 0) = f a a := by
  classical
  convert sum_sum_indicator a a f using 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxy : x = y <;> by_cases hax : a = x <;>
    simp [hxy, hax]

@[simp]
theorem sum_sum_two_negative_indicators
    (v : I → K → ℤ) (b : I → K → ℤ) (k l : K) :
    (∑ i, ∑ a,
      (-(v i a * (if k = a then b i l else 0)) -
        v i a * (if l = a then b i k else 0))) =
      -(∑ i, (v i k * b i l + b i k * v i l)) := by
  classical
  have hinner : ∀ i,
      (∑ a,
        (-(v i a * (if k = a then b i l else 0)) -
          v i a * (if l = a then b i k else 0))) =
        -(v i k * b i l) - v i l * b i k := by
    intro i
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      sum_mul_indicator, sum_mul_indicator]
  simp_rw [hinner]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hcomm : (∑ i, v i l * b i k) = ∑ i, b i k * v i l := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hcomm, Finset.sum_add_distrib]
  ring

/-- The type-II relation words give precisely the `ūB` entry.  This is the sign-sensitive
calculation: the first endpoint contributes `u_ij B_j`, while the second contributes
`-(d_i/d_j)u_ji B_j`. -/
theorem upperPair_xyContribution (u : I → I → ℤ) (i : I) (k : K) :
    (∑ ij ∈ upperPairs I, (
      (if i = ij.1 then u ij.1 ij.2 * D.B ij.2 k else 0) -
        (if i = ij.2 then
          u ij.1 ij.2 * ((D.dRatio ij.1 ij.2 : ℤ) * D.B ij.1 k) else 0))) =
      D.upperSkewMul u i k := by
  classical
  let pos : ℤ := ∑ ij ∈ upperPairs I,
    if i = ij.1 then u ij.1 ij.2 * D.B ij.2 k else 0
  let neg : ℤ := ∑ ij ∈ upperPairs I,
    if i = ij.2 then
      (D.dRatio ij.1 ij.2 : ℤ) * u ij.1 ij.2 * D.B ij.1 k else 0
  have hsplit :
      (∑ ij ∈ upperPairs I, (
        (if i = ij.1 then u ij.1 ij.2 * D.B ij.2 k else 0) -
          (if i = ij.2 then
            u ij.1 ij.2 * ((D.dRatio ij.1 ij.2 : ℤ) * D.B ij.1 k) else 0))) =
        pos - neg := by
    dsimp only [pos, neg]
    rw [Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ij hij
    by_cases hsecond : i = ij.2 <;> simp [hsecond]
    ring
  rw [hsplit]
  dsimp only [pos, neg]
  unfold Data.upperSkewMul
  congr 1
  · rw [show
        (∑ ij ∈ upperPairs I,
          if i = ij.1 then u ij.1 ij.2 * D.B ij.2 k else 0) =
          ∑ a, ∑ b ∈ Finset.univ.filter (a < ·),
            (if i = a then u a b * D.B b k else 0) from
        sum_upperPairs (fun a b ↦ if i = a then u a b * D.B b k else 0)]
    rw [Finset.sum_eq_single i]
    · simp
    · intro a ha hai
      simp [Ne.symm hai]
    · simp
  · rw [show
        (∑ ij ∈ upperPairs I,
          if i = ij.2 then
            (D.dRatio ij.1 ij.2 : ℤ) * u ij.1 ij.2 * D.B ij.1 k else 0) =
          ∑ b, ∑ a ∈ Finset.univ.filter (· < b),
            (if i = b then (D.dRatio a b : ℤ) * u a b * D.B a k else 0) from
        sum_upperPairs_right (fun a b ↦
          if i = b then (D.dRatio a b : ℤ) * u a b * D.B a k else 0)]
    rw [Finset.sum_eq_single i]
    · simp [mul_assoc]
    · intro b hb hbi
      simp [Ne.symm hbi]
    · simp

theorem upperPair_xyContribution_factored
    (u : I → I → ℤ) (i : I) (k : K) :
    (∑ ij ∈ upperPairs I,
      u ij.1 ij.2 *
        ((if i = ij.1 then D.B ij.2 k else 0) -
          (if i = ij.2 then
            (D.dRatio ij.1 ij.2 : ℤ) * D.B ij.1 k else 0))) =
      D.upperSkewMul u i k := by
  rw [← upperPair_xyContribution D u i k]
  apply Finset.sum_congr rfl
  intro ij hij
  have hne : ij.1 ≠ ij.2 := ne_of_lt (mem_upperPairs.mp hij)
  by_cases hfirst : i = ij.1 <;> by_cases hsecond : i = ij.2 <;>
    simp [hfirst, hsecond, hne, Ne.symm hne] <;> ring

@[simp]
theorem sum_indicator_value (a : K) (f : K → ℤ) :
    (∑ x, if a = x then f x else 0) = f a := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro x hx hxa
    simp [Ne.symm hxa]
  · simp

@[simp]
theorem sum_if_and_indicator (P : Prop) [Decidable P]
    (a : K) (f : K → ℤ) :
    (∑ x, if P ∧ a = x then f x else 0) = if P then f a else 0 := by
  by_cases hP : P <;> simp [hP]

theorem sum_unordered_indicator (a k l : K) (hkl : k ≠ l) (f : K → ℤ) :
    (∑ x, if (x = k ∧ a = l) ∨ (x = l ∧ a = k) then f x else 0) =
      (if a = l then f k else 0) + (if a = k then f l else 0) := by
  classical
  by_cases hal : a = l <;> by_cases hak : a = k <;>
    simp [hal, hak, hkl, Ne.symm hkl]

@[simp]
theorem sum_unordered_indicator_rev (a k l : K) (hkl : k ≠ l) (f : K → ℤ) :
    (∑ x, if (k = x ∧ l = a) ∨ (l = x ∧ k = a) then f x else 0) =
      (if a = l then f k else 0) + (if a = k then f l else 0) := by
  simpa only [eq_comm] using sum_unordered_indicator a k l hkl f

/-- Direct `xy` collection of each of the seven literal relation words. -/
theorem rawPBWProjection_coreWordExpression_xy
    (T : RelationTails (I := I) (K := K))
    (w : @CoreWord I K _) (i : I) (k : K) :
    D.rawPBWProjection (.xy i k) (D.coreWordExpression T w) =
      D.coreWordContribution w (.xy i k) := by
  classical
  cases w <;>
    simp [coreWordExpression, rRelation, sRelation, tRelation,
      sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
      rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
      rawWord_mul_rawWord, rawWordCoordinate, coreWordContribution] <;>
    ring

/-- Direct `z` collection of each of the seven literal relation words. -/
theorem rawPBWProjection_coreWordExpression_z
    (T : RelationTails (I := I) (K := K))
    (w : @CoreWord I K _) :
    D.rawPBWProjection .z (D.coreWordExpression T w) =
      D.coreWordContribution w .z := by
  classical
  cases w <;>
    simp [coreWordExpression, rRelation, sRelation, tRelation,
      sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
      rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
      rawWord_mul_rawWord, rawWordCoordinate, coreWordContribution,
      Finset.mul_sum]

/-- Direct off-diagonal `yy` collection. -/
theorem rawPBWProjection_coreWordExpression_yy
    (T : RelationTails (I := I) (K := K))
    (w : @CoreWord I K _) (k l : K) (hkl : k ≠ l) :
    D.rawPBWProjection (.yy k l) (D.coreWordExpression T w) =
      D.coreWordContribution w (.yy k l) := by
  classical
  cases w <;>
    simp [coreWordExpression, rRelation, sRelation, tRelation,
      sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
      rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
      rawWord_mul_rawWord, rawWordCoordinate, coreWordContribution, hkl,
      sum_unordered_indicator, sum_unordered_indicator_rev] <;>
    simp [eq_comm] <;>
    ring

/-- Direct diagonal `y²` collection. -/
theorem rawPBWProjection_coreWordExpression_ySquare
    (T : RelationTails (I := I) (K := K))
    (w : @CoreWord I K _) (k : K) :
    D.rawPBWProjection (.ySquare k) (D.coreWordExpression T w) =
      D.coreWordContribution w (.ySquare k) := by
  classical
  cases w <;>
    simp [coreWordExpression, rRelation, sRelation, tRelation,
      sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
      rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
      rawWord_mul_rawWord, rawWordCoordinate, coreWordContribution,
      and_comm, eq_comm] <;>
    split_ifs <;> simp_all <;>
    ring

/-- The two exceptional products give exactly the indicated off-diagonal multiples. -/
theorem rawPBWProjection_sY_yy (T : RelationTails (I := I) (K := K))
    {k l : K} (hkl : k ≠ l) :
    D.rawPBWProjection (.yy k l) (D.exceptionalWordExpression T (.sY k l)) =
      (D.e k : ℤ) := by
  simp [exceptionalWordExpression, sRelation, sub_mul, rawWordCoordinate, hkl]

theorem rawPBWProjection_Ys_yy (T : RelationTails (I := I) (K := K))
    {k l : K} (hkl : k ≠ l) :
    D.rawPBWProjection (.yy k l) (D.exceptionalWordExpression T (.Ys k l)) =
      (D.e l : ℤ) := by
  simp [exceptionalWordExpression, sRelation, mul_sub, rawWordCoordinate, hkl]

/-- The diagonal row is the missing `(C2)` calculation. -/
theorem rawPBWProjection_sY_ySquare (T : RelationTails (I := I) (K := K)) (k : K) :
    D.rawPBWProjection (.ySquare k) (D.exceptionalWordExpression T (.sY k k)) =
      (D.e k : ℤ) := by
  simp [exceptionalWordExpression, sRelation, sub_mul, rawWordCoordinate]

@[simp]
theorem explicitWordSum_z :
    explicitWordSum D E .z = zCoefficient D E := by
  classical
  simp [explicitWordSum, coreWordContribution, exceptionalWordContribution,
    zCoefficient, bgEntry]
  ring

@[simp]
theorem explicitWordSum_yy (k l : K) :
    explicitWordSum D E (.yy k l) = yyCoefficient D E k l := by
  classical
  simp [explicitWordSum, coreWordContribution, exceptionalWordContribution,
    yyCoefficient]
  simp_rw [mul_sub, mul_neg]
  rw [sum_sum_two_negative_indicators E.v D.B k l]
  ring

@[simp]
theorem explicitWordSum_ySquare (k : K) :
    explicitWordSum D E (.ySquare k) = ySquareCoefficient D E k := by
  classical
  simp [explicitWordSum, coreWordContribution, exceptionalWordContribution,
    ySquareCoefficient]
  ring

@[simp]
theorem explicitWordSum_xy (i : I) (k : K) :
    explicitWordSum D E (.xy i k) = xyCoefficient D E i k := by
  classical
  simp [explicitWordSum, coreWordContribution, exceptionalWordContribution,
    xyCoefficient]
  rw [upperPair_xyContribution_factored D E.u i k]
  ring

/-- The fully collected literal relation polynomial.  The last two lines are respectively the
off-diagonal and diagonal pure-`yy` rows of the shape table. -/
def literalCollectedPolynomial (T : RelationTails (I := I) (K := K)) :
    @RawExpression I K :=
  rawScale E.t (D.coreWordExpression T .typeI) +
    (∑ ij ∈ upperPairs I,
      rawScale (E.u ij.1 ij.2) (D.coreWordExpression T (.typeII ij.1 ij.2))) +
    (∑ i, ∑ k, rawScale (E.v i k) (D.coreWordExpression T (.typeIII i k))) +
    (∑ i, ∑ k, rawScale (E.v' i k) (D.coreWordExpression T (.typeIV i k))) +
    (∑ kl ∈ upperPairs K,
      rawTerm ((D.e kl.1 : ℤ) * E.sY kl.1 kl.2 +
        (D.e kl.2 : ℤ) * E.Ys kl.1 kl.2) [.y kl.1, .y kl.2]) +
    ∑ k, rawTerm ((D.e k : ℤ) * (E.sY k k + E.Ys k k)) [.y k, .y k]

/-- A single ordered off-diagonal word is selected from the upper-pair sum. -/
theorem upperPairs_rawTerm_yy_projection
    (a : K → K → ℤ) {k l : K} (hkl : k < l) :
    D.rawPBWProjection (.yy k l)
        (∑ ij ∈ upperPairs K, rawTerm (a ij.1 ij.2) [.y ij.1, .y ij.2]) =
      a k l := by
  classical
  rw [map_sum]
  rw [Finset.sum_eq_single (k, l)]
  · simp [rawWordCoordinate, hkl.ne]
  · intro ij hij hne
    have hijlt : ij.1 < ij.2 := mem_upperPairs.mp hij
    simp only [rawPBWProjection_rawTerm, rawWordCoordinate]
    have hnot : ¬(k ≠ l ∧
        (ij.1 = k ∧ ij.2 = l ∨ ij.1 = l ∧ ij.2 = k)) := by
      intro hbad
      rcases hbad.2 with hsame | hrev
      · apply hne
        exact Prod.ext hsame.1 hsame.2
      · have : l < k := hrev.1 ▸ hrev.2 ▸ hijlt
        exact (not_lt_of_ge hkl.le this).elim
    rw [if_neg hnot]
    simp
  · simp [mem_upperPairs, hkl]

@[simp]
theorem upperPairs_unordered_indicator (a : K → K → ℤ)
    {k l : K} (hkl : k < l) :
    (∑ ij ∈ upperPairs K,
      if (ij.1 = k ∧ ij.2 = l) ∨ (ij.1 = l ∧ ij.2 = k)
      then a ij.1 ij.2 else 0) = a k l := by
  classical
  rw [Finset.sum_eq_single (k, l)]
  · simp
  · intro ij hij hne
    have hijlt := mem_upperPairs.mp hij
    rw [if_neg]
    intro hbad
    rcases hbad with hsame | hrev
    · exact hne (Prod.ext hsame.1 hsame.2)
    · have : l < k := hrev.1 ▸ hrev.2 ▸ hijlt
      exact (not_lt_of_ge hkl.le this).elim
  · simp [mem_upperPairs, hkl]

@[simp]
theorem upperPairs_diagonal_indicator_zero (a : K → K → ℤ) (k : K) :
    (∑ ij ∈ upperPairs K,
      if ij.1 = k ∧ ij.2 = k then a ij.1 ij.2 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro ij hij
  have hne : ij.1 ≠ ij.2 := ne_of_lt (mem_upperPairs.mp hij)
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact hne (h1.trans h2.symm)

/-- A diagonal word `y_j²` cannot contribute to the off-diagonal coordinate `y_k y_l`
when `k ≠ l`. -/
@[simp]
theorem diagonal_unordered_indicator_zero (a : K → ℤ) {k l : K} (hkl : k ≠ l) :
    (∑ j, if (j = k ∧ j = l) ∨ (j = l ∧ j = k) then a j else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [if_neg]
  rintro (⟨hjk, hjl⟩ | ⟨hjl, hjk⟩)
  · exact hkl (hjk.symm.trans hjl)
  · exact hkl (hjk.symm.trans hjl)

/-- The diagonal sum selects exactly its `k`-th term. -/
theorem diagonal_rawTerm_ySquare_projection (a : K → ℤ) (k : K) :
    D.rawPBWProjection (.ySquare k)
        (∑ l, rawTerm (a l) [.y l, .y l]) = a k := by
  classical
  rw [map_sum, Finset.sum_eq_single k]
  · simp [rawWordCoordinate]
  · intro l hl hlk
    simp [rawWordCoordinate, hlk]
  · simp

theorem rawPBWProjection_literalCollectedPolynomial_xy
    (T : RelationTails (I := I) (K := K)) (i : I) (k : K) :
    D.rawPBWProjection (.xy i k) (literalCollectedPolynomial D E T) =
      explicitWordSum D E (.xy i k) := by
  classical
  simp [literalCollectedPolynomial, explicitWordSum,
    rawPBWProjection_coreWordExpression_xy, rawWordCoordinate,
    coreWordContribution, exceptionalWordContribution]

theorem rawPBWProjection_literalCollectedPolynomial_z
    (T : RelationTails (I := I) (K := K)) :
    D.rawPBWProjection .z (literalCollectedPolynomial D E T) =
      explicitWordSum D E .z := by
  classical
  simp [literalCollectedPolynomial, explicitWordSum,
    rawPBWProjection_coreWordExpression_z, rawWordCoordinate,
    coreWordContribution, exceptionalWordContribution]

theorem rawPBWProjection_literalCollectedPolynomial_yy
    (T : RelationTails (I := I) (K := K)) {k l : K} (hkl : k < l) :
    D.rawPBWProjection (.yy k l) (literalCollectedPolynomial D E T) =
      explicitWordSum D E (.yy k l) := by
  classical
  simp [literalCollectedPolynomial, explicitWordSum,
    rawPBWProjection_coreWordExpression_yy, rawWordCoordinate, hkl.ne,
    upperPairs_rawTerm_yy_projection,
    coreWordContribution,
    exceptionalWordContribution]
  rw [upperPairs_unordered_indicator
    (fun a b ↦ (D.e a : ℤ) * E.sY a b + (D.e b : ℤ) * E.Ys a b) hkl]
  ring

theorem rawPBWProjection_literalCollectedPolynomial_ySquare
    (T : RelationTails (I := I) (K := K)) (k : K) :
    D.rawPBWProjection (.ySquare k) (literalCollectedPolynomial D E T) =
      explicitWordSum D E (.ySquare k) := by
  classical
  simp [literalCollectedPolynomial, explicitWordSum,
    rawPBWProjection_coreWordExpression_ySquare, rawWordCoordinate,
    diagonal_rawTerm_ySquare_projection,
    coreWordContribution,
    exceptionalWordContribution]
  rw [upperPairs_diagonal_indicator_zero
    (fun a b ↦ (D.e a : ℤ) * E.sY a b + (D.e b : ℤ) * E.Ys a b) k]
  ring

/-- A genuine PBW coordinate: off-diagonal symmetric-square monomials are indexed only in
increasing order. -/
def isCanonicalCoordinate : @RelevantCoordinate I K → Prop
  | .yy k l => k < l
  | _ => True

/-! ## The rows omitted from the decisive polynomial -/

/-- Formal linear combinations of precisely the rows in the displayed shape table that have
zero contribution to all four decisive PBW coordinates.  The two `sY` rows are not here: their
off-diagonal and diagonal contributions are retained explicitly in
`literalCollectedPolynomial`. -/
inductive TableRemainder where
  | zero
  | add (p q : TableRemainder)
  | scale (n : ℤ) (p : TableRemainder)
  | typeV (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
  | typeVI (i j k : I) (hij : i < j) (hjk : j ≤ k)
  | typeVII (i j k : I) (hij : i ≤ j) (hjk : j < k)
  | rXY (i j : I) (k : K)
  | XXs (i j : I) (k : K)
  | rZ (i : I)
  | Xt (i : I)

/-- Interpret an omitted table row as its literal relation polynomial. -/
def TableRemainder.expression (T : RelationTails (I := I) (K := K)) :
    TableRemainder (I := I) (K := K) → @RawExpression I K
  | .zero => 0
  | .add p r => expression T p + expression T r
  | .scale n p => rawScale n (expression T p)
  | .typeV i j k hij hjk => D.coreWordExpression T (.typeV i j k hij hjk)
  | .typeVI i j k hij hjk => D.coreWordExpression T (.typeVI i j k hij hjk)
  | .typeVII i j k hij hjk => D.coreWordExpression T (.typeVII i j k hij hjk)
  | .rXY i j k => D.exceptionalWordExpression T (.rXY i j k)
  | .XXs i j k => D.exceptionalWordExpression T (.XXs i j k)
  | .rZ i => D.exceptionalWordExpression T (.rZ i)
  | .Xt i => D.exceptionalWordExpression T (.Xt i)

/-- A core row with zero contribution function has zero literal projection. -/
theorem rawPBWProjection_coreWordExpression_zero
    (T : RelationTails (I := I) (K := K)) (w : @CoreWord I K _)
    (hw : ∀ c : @RelevantCoordinate I K, D.coreWordContribution w c = 0)
    (c : @RelevantCoordinate I K) (hc : isCanonicalCoordinate c) :
    D.rawPBWProjection c (D.coreWordExpression T w) = 0 := by
  cases c with
  | xy i k =>
      rw [rawPBWProjection_coreWordExpression_xy]
      exact hw _
  | z =>
      rw [rawPBWProjection_coreWordExpression_z]
      exact hw _
  | yy k l =>
      rw [rawPBWProjection_coreWordExpression_yy (hkl := ne_of_lt hc)]
      exact hw _
  | ySquare k =>
      rw [rawPBWProjection_coreWordExpression_ySquare]
      exact hw _

/-- Every exceptional row other than `sY` and `Ys` is invisible in the four decisive
coordinates. -/
theorem rawPBWProjection_exceptional_rXY_zero
    (T : RelationTails (I := I) (K := K)) (i j : I) (k : K)
    (c : @RelevantCoordinate I K) :
    D.rawPBWProjection c (D.exceptionalWordExpression T (.rXY i j k)) = 0 := by
  classical
  cases c <;>
    simp [exceptionalWordExpression, rRelation, sub_mul, Finset.sum_mul,
      rawTerm_mul_rawWord, rawWordCoordinate]

theorem rawPBWProjection_exceptional_XXs_zero
    (T : RelationTails (I := I) (K := K)) (i j : I) (k : K)
    (c : @RelevantCoordinate I K) :
    D.rawPBWProjection c (D.exceptionalWordExpression T (.XXs i j k)) = 0 := by
  cases c <;>
    simp [exceptionalWordExpression, sRelation, mul_sub, rawWord_mul_rawTerm,
      rawWordCoordinate]

theorem rawPBWProjection_exceptional_rZ_zero
    (T : RelationTails (I := I) (K := K)) (i : I)
    (c : @RelevantCoordinate I K) :
    D.rawPBWProjection c (D.exceptionalWordExpression T (.rZ i)) = 0 := by
  classical
  cases c <;>
    simp [exceptionalWordExpression, rRelation, sub_mul, Finset.sum_mul,
      rawTerm_mul_rawWord, rawWordCoordinate]

theorem rawPBWProjection_exceptional_Xt_zero
    (T : RelationTails (I := I) (K := K)) (i : I)
    (c : @RelevantCoordinate I K) :
    D.rawPBWProjection c (D.exceptionalWordExpression T (.Xt i)) = 0 := by
  cases c <;>
    simp [exceptionalWordExpression, tRelation, rawWord_mul_rawTerm,
      rawWordCoordinate]

/-- The omitted-row table is invisible by construction.  This theorem, rather than a field in
the standing reduction, is what removes every unlisted PBW coefficient. -/
theorem rawPBWProjection_tableRemainder_zero
    (T : RelationTails (I := I) (K := K))
    (R : TableRemainder (I := I) (K := K))
    (c : @RelevantCoordinate I K) (hc : isCanonicalCoordinate c) :
    D.rawPBWProjection c (TableRemainder.expression (D := D) T R) = 0 := by
  induction R with
  | zero => simp [TableRemainder.expression]
  | add p r hp hr => simp [TableRemainder.expression, hp, hr]
  | scale n p hp => simp [TableRemainder.expression, hp]
  | typeV i j k hij hjk =>
      apply rawPBWProjection_coreWordExpression_zero D T _ _ c hc
      intro c'
      cases c' <;> simp [coreWordContribution]
  | typeVI i j k hij hjk =>
      apply rawPBWProjection_coreWordExpression_zero D T _ _ c hc
      intro c'
      cases c' <;> simp [coreWordContribution]
  | typeVII i j k hij hjk =>
      apply rawPBWProjection_coreWordExpression_zero D T _ _ c hc
      intro c'
      cases c' <;> simp [coreWordContribution]
  | rXY i j k => exact rawPBWProjection_exceptional_rXY_zero D T i j k c
  | XXs i j k => exact rawPBWProjection_exceptional_XXs_zero D T i j k c
  | rZ i => exact rawPBWProjection_exceptional_rZ_zero D T i c
  | Xt i => exact rawPBWProjection_exceptional_Xt_zero D T i c

/-- The standing class-three reduction after the exhaustive relation-word collection.

`literalCollectedPolynomial` contains the only table rows that can affect the four decisive
PBW coordinates.  `remainder` is built from the other displayed rows; terms of filtered weight
at least five have already vanished in the truncated equality.  Its irrelevance is the theorem
`rawPBWProjection_tableRemainder_zero`, not an assumption.  The last field is the collected
equality with the lifted Lie element, whose only relevant PBW coordinate is its coefficient of
the chosen generator `z`. -/
structure StandingPBWReduction
    (T : RelationTails (I := I) (K := K)) (ζ : ZMod q) where
  lieZ : ℤ
  lieZ_mod : (lieZ : ZMod q) = ζ
  remainder : TableRemainder (I := I) (K := K)
  collected_eq : literalCollectedPolynomial D E T +
      TableRemainder.expression (D := D) T remainder =
    rawTerm lieZ [.z]

/-- One equality of PBW coordinate vectors after collection.  The right-hand side is a Lie
element in `γ₃`: it has a possibly nonzero single-factor `z` coordinate and no `xy`, `yy`, or
`y²` coordinate.  Its integral `z` coefficient represents `ζ` modulo the relation `qz`.

Unlike `Comparison`, this structure does not assume any of `(B)`, `(Z)`, `(C1)`, or `(C2)`;
they are obtained below by applying the four coordinate projections to `coordinate_eq`. -/
structure PBWNormalFormEquation (ζ : ZMod q) where
  lieZ : ℤ
  lieZ_mod : (lieZ : ZMod q) = ζ
  coordinate_eq : ∀ c : @RelevantCoordinate I K, isCanonicalCoordinate c →
    explicitWordSum D E c = match c with
      | .z => lieZ
      | _ => 0

/-- Apply the four PBW projections to the literal collected equality.  This is where the
normal-form word table is converted into coefficient equalities; no matrix conclusion is
assumed. -/
def StandingPBWReduction.toPBWNormalFormEquation
    {T : RelationTails (I := I) (K := K)} {ζ : ZMod q}
    (h : StandingPBWReduction D E T ζ) : PBWNormalFormEquation D E ζ where
  lieZ := h.lieZ
  lieZ_mod := h.lieZ_mod
  coordinate_eq := by
    intro c hc
    have heq := congrArg (D.rawPBWProjection c) h.collected_eq
    rw [map_add, rawPBWProjection_tableRemainder_zero D T h.remainder c hc, add_zero] at heq
    cases c with
    | xy i k =>
        rw [rawPBWProjection_literalCollectedPolynomial_xy] at heq
        simpa [rawWordCoordinate] using heq
    | z =>
        rw [rawPBWProjection_literalCollectedPolynomial_z] at heq
        simpa [rawWordCoordinate] using heq
    | yy k l =>
        rw [rawPBWProjection_literalCollectedPolynomial_yy (hkl := hc)] at heq
        simpa [rawWordCoordinate] using heq
    | ySquare k =>
        rw [rawPBWProjection_literalCollectedPolynomial_ySquare] at heq
        simpa [rawWordCoordinate] using heq

/-- The four literal PBW comparisons obtained after subtracting a Lie element.  A Lie element
has no multi-factor PBW coefficient; its named `z` coordinate is `ζ` modulo `q`.

This structure is deliberately a record of *equalities*, not divisibility conclusions.  The
theorem below derives `(B)`, `(Z)`, `(C1)`, and `(C2)` from these equalities. -/
structure Comparison (ζ : ZMod q) : Prop where
  xy_zero : ∀ i k, xyCoefficient D E i k = 0
  z_mod : (zCoefficient D E : ZMod q) = ζ
  yy_zero : ∀ k l, k < l → yyCoefficient D E k l = 0
  ySquare_zero : ∀ k, ySquareCoefficient D E k = 0

theorem gcd_dvd_linearCombination (a b x y : ℤ) :
    (Int.gcd a b : ℤ) ∣ a * x + b * y := by
  exact dvd_add (Int.gcd_dvd_left a b |>.mul_right x)
    (Int.gcd_dvd_right a b |>.mul_right y)

/-- **PBW coefficient extraction.**  Literal vanishing of the four PBW coordinates produces
exactly the `CoefficientSystem` consumed by the certificate criterion.  In particular both
`(C1)` and the indispensable diagonal equation `(C2)` are included. -/
def toCoefficientSystem {ζ : ZMod q} (h : Comparison D E ζ) :
    D.CoefficientSystem ζ where
  u := E.u
  v := E.v
  v' := E.v'
  B_eq := h.xy_zero
  Z_eq := by
    have hz := h.z_mod
    unfold zCoefficient at hz
    push_cast at hz
    simpa [mul_assoc] using hz
  C1 := by
    intro k l hkl
    have horder : k < l ∨ l < k := lt_or_gt_of_ne hkl
    rcases horder with hlt | hlt
    · have hzero := h.yy_zero k l hlt
      unfold yyCoefficient at hzero
      have heq :
          ∑ i, (E.v i k * D.B i l + D.B i k * E.v i l) =
            (D.e k : ℤ) * E.sY k l + (D.e l : ℤ) * E.Ys k l := by
        linarith
      rw [heq]
      have hgcd : (Nat.gcd (D.e k) (D.e l) : ℤ) =
          Int.gcd (D.e k : ℤ) (D.e l : ℤ) := by
        simp [Int.gcd_eq_natAbs]
      rw [hgcd]
      exact gcd_dvd_linearCombination _ _ _ _
    · have hzero := h.yy_zero l k hlt
      unfold yyCoefficient at hzero
      have heq :
          ∑ i, (E.v i l * D.B i k + D.B i l * E.v i k) =
            (D.e l : ℤ) * E.sY l k + (D.e k : ℤ) * E.Ys l k := by
        linarith
      have hsym :
          (∑ i, (E.v i k * D.B i l + D.B i k * E.v i l)) =
            ∑ i, (E.v i l * D.B i k + D.B i l * E.v i k) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsym, heq, Nat.gcd_comm]
      have hgcd : (Nat.gcd (D.e l) (D.e k) : ℤ) =
          Int.gcd (D.e l : ℤ) (D.e k : ℤ) := by
        simp [Int.gcd_eq_natAbs]
      rw [hgcd]
      exact gcd_dvd_linearCombination _ _ _ _
  C2 := by
    intro k
    have hzero := h.ySquare_zero k
    unfold ySquareCoefficient at hzero
    refine ⟨E.sY k k + E.Ys k k, ?_⟩
    linarith

/-- Extract the four literal comparisons from the single PBW normal-form equality. -/
def PBWNormalFormEquation.toComparison {ζ : ZMod q}
    (h : PBWNormalFormEquation D E ζ) : Comparison D E ζ where
  xy_zero i k := by
    rw [← explicitWordSum_xy D E i k]
    simpa using h.coordinate_eq (.xy i k) (by trivial)
  z_mod := by
    rw [← explicitWordSum_z D E, h.coordinate_eq .z (by trivial)]
    exact h.lieZ_mod
  yy_zero k l hkl := by
    rw [← explicitWordSum_yy D E k l]
    simpa using h.coordinate_eq (.yy k l) hkl
  ySquare_zero k := by
    rw [← explicitWordSum_ySquare D E k]
    simpa using h.coordinate_eq (.ySquare k) (by trivial)

/-- **PBW normal form implies `(B)`, `(Z)`, `(C1)`, `(C2)`.**  This is the final
coefficient-extraction theorem: its sole mathematical input is the one collected PBW-vector
identity, and its output is exactly the coefficient system used by the certificate theorem. -/
def coefficientSystemOfPBWNormalForm {ζ : ZMod q}
    (h : PBWNormalFormEquation D E ζ) : D.CoefficientSystem ζ :=
  toCoefficientSystem D E h.toComparison

/-- **Coordinate PBW collection theorem (class-three standing reduction).**  For every
adapted datum and every collected relation identity satisfying the standing reduction, the
matrices extracted from the literal relation words satisfy all four conclusions `(B)`, `(Z)`,
`(C1)`, and `(C2)`.  In particular, `(C2)` comes from the separately checked `y_k²`
coefficient and is not folded into the off-diagonal argument. -/
def coefficientSystemOfStandingPBWReduction
    {T : RelationTails (I := I) (K := K)} {ζ : ZMod q}
    (h : StandingPBWReduction D E T ζ) : D.CoefficientSystem ζ :=
  coefficientSystemOfPBWNormalForm D E h.toPBWNormalFormEquation

end CollectedExpression

end Data

/-! ## The exhaustive numerical source table -/

/-- Names for the rows of the relation-product shape table in the complete proof. -/
inductive RelationShape where
  | rScalar | rX | rY | rXX | rZ | rXY | rXXX
  | sScalar | sX | sY | sXX
  | tScalar | tX
  | qScalar
  deriving DecidableEq

/-- Translate a relation weight and its ordered external-weight word to the corresponding
row of the displayed shape table. -/
def relationShape? (relationWeight : ℕ) (externalWeights : List ℕ) :
    Option RelationShape :=
  match relationWeight, externalWeights with
  | 1, [] => some .rScalar
  | 1, [1] => some .rX
  | 1, [2] => some .rY
  | 1, [1, 1] => some .rXX
  | 1, [3] => some .rZ
  | 1, [1, 2] => some .rXY
  | 1, [1, 1, 1] => some .rXXX
  | 2, [] => some .sScalar
  | 2, [1] => some .sX
  | 2, [2] => some .sY
  | 2, [1, 1] => some .sXX
  | 3, [] => some .tScalar
  | 3, [1] => some .tX
  | 4, [] => some .qScalar
  | _, _ => none

theorem relationShape?_isSome_of_lowPacketWeightSequence
    (relationWeight : ℕ) (externalWeights : List ℕ)
    (hpos : 0 < relationWeight)
    (h : IsLowPacketWeightSequence relationWeight externalWeights) :
    (relationShape? relationWeight externalWeights).isSome := by
  have ht := lowPacketWeightSequence_complete hpos h
  rcases ht with h1 | h2 | h3 | h4
  · rcases h1 with ⟨rfl, hs⟩
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases h2 with ⟨rfl, hs⟩
    rcases hs with rfl | rfl | rfl | rfl <;> decide
  · rcases h3 with ⟨rfl, hs⟩
    rcases hs with rfl | rfl <;> decide
  · rcases h4 with ⟨rfl, rfl⟩
    decide

/-- The actual terminating semantic collector has no unlisted low-weight output: every packet
in a normal-form support with total weight below five lands in one and only one row of the
displayed table. -/
theorem semanticNormalForm_shape_table_exhaustive
    {L : Type*} [LieRing L]
    (p q' : FilteredRelationPacket L)
    (hq' : q' ∈ ((semanticPacketCollector L).normalForm p).support)
    (hlow : q'.relationWeight + q'.externalWeights.sum < 5) :
    (relationShape? q'.relationWeight q'.externalWeights).isSome := by
  apply relationShape?_isSome_of_lowPacketWeightSequence
    q'.relationWeight q'.externalWeights q'.relationWeight_pos
  exact isLowPacketWeightSequence_of_mem_normalForm_support L p q' hq' hlow

end

end Coordinate

end DegreeFive

end LieRings
