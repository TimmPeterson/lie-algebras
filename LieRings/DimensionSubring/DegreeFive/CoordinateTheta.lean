import LieRings.DimensionSubring.DegreeFive.CoordinatePBW

/-!
# Construction of Theta from the fully collected adapted ledger

This file formalizes the weight-one and weight-two cancellation in the PBW collection lemma.
Its input is the exhaustive adapted word ledger before those cancellations.  Its output is the
`StandingPBWReduction` consumed by the coordinate calculations in `CoordinatePBW`.

The coordinate family `PreThetaEquation.collected_eq` is deliberately the boundary of the
*adapted-presentation* step: it says that the terminal semantic ledger has been read by the
relevant PBW coefficient functionals.  It is not an equality in a free monoid algebra (which
would be false before PBW normalization).  No cancellation, Type-II divisibility, Theta normal
form, or conclusion `(B)`, `(Z)`, `(C1)`, `(C2)` is assumed there.
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

namespace CollectedExpression

/-! ## Exact coefficients of raw adapted words -/

/-- Coefficient of one literal word in the free associative adapted-word expression. -/
def rawCoefficient (xs : List (@AdaptedLetter I K)) :
    (@RawExpression I K) →ₗ[ℤ] ℤ where
  toFun p := p (FreeMonoid.ofList xs)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem rawCoefficient_rawTerm (xs ys : List (@AdaptedLetter I K)) (n : ℤ) :
    rawCoefficient xs (rawTerm n ys) = if xs = ys then n else 0 := by
  classical
  unfold rawCoefficient rawTerm
  by_cases h : xs = ys
  · subst ys
    simp
  · have hmono : FreeMonoid.ofList xs ≠ FreeMonoid.ofList ys := by
      intro heq
      apply h
      simpa using congrArg FreeMonoid.toList heq
    simp [hmono]
    exact fun hxy ↦ (h hxy).elim

@[simp]
theorem rawCoefficient_rawWord (xs ys : List (@AdaptedLetter I K)) :
    rawCoefficient xs (rawWord ys) = if xs = ys then 1 else 0 := by
  simpa only [rawWord] using rawCoefficient_rawTerm (I := I) (K := K) xs ys 1

@[simp]
theorem rawCoefficient_rawScale (xs : List (@AdaptedLetter I K))
    (n : ℤ) (p : @RawExpression I K) :
    rawCoefficient xs (rawScale n p) = n * rawCoefficient xs p := by
  simpa only [rawScale, smul_eq_mul] using map_smul (rawCoefficient xs) n p

/-! ## The exhaustive collected ledger before forming Type II -/

/-- Coefficients of every named row which can survive collection below weight five before the
weight-one and weight-two cancellations are performed.

`rx i j` and `xr i j` are used only for `i < j`; they multiply `r_i x_j` and `x_i r_j`.
`rxx i` is the diagonal coefficient of `r_i x_i`.  The remaining fields are already the
coefficients of Types I, III, IV and the two pure-`yy` exceptional rows. -/
structure PreTheta where
  r : I → ℤ
  s : K → ℤ
  rxx : I → ℤ
  rx : I → I → ℤ
  xr : I → I → ℤ
  v : I → K → ℤ
  v' : I → K → ℤ
  t : ℤ
  sY : K → K → ℤ
  Ys : K → K → ℤ
  remainder : TableRemainder (I := I) (K := K)

/-- The literal exhaustive polynomial represented by `PreTheta`.  This is the displayed
relation-word table before the scalar and two-factor leading terms are cancelled. -/
def PreTheta.polynomial (P : PreTheta (I := I) (K := K))
    (T : RelationTails (I := I) (K := K)) : @RawExpression I K :=
  (∑ i, rawScale (P.r i) (D.rRelation T i)) +
    (∑ k, rawScale (P.s k) (D.sRelation T k)) +
    (∑ i, rawScale (P.rxx i) (D.rRelation T i * rawWord [.x i])) +
    (∑ ij ∈ upperPairs I, (
      rawScale (P.rx ij.1 ij.2) (D.rRelation T ij.1 * rawWord [.x ij.2]) +
      rawScale (P.xr ij.1 ij.2) (rawWord [.x ij.1] * D.rRelation T ij.2))) +
    rawScale P.t (D.coreWordExpression T .typeI) +
    (∑ i, ∑ k, rawScale (P.v i k) (D.coreWordExpression T (.typeIII i k))) +
    (∑ i, ∑ k, rawScale (P.v' i k) (D.coreWordExpression T (.typeIV i k))) +
    (∑ kl ∈ upperPairs K,
      rawTerm ((D.e kl.1 : ℤ) * P.sY kl.1 kl.2 +
        (D.e kl.2 : ℤ) * P.Ys kl.1 kl.2) [.y kl.1, .y kl.2]) +
    (∑ k, rawTerm ((D.e k : ℤ) * (P.sY k k + P.Ys k k)) [.y k, .y k]) +
    TableRemainder.expression (D := D) T P.remainder

/-- Coefficients needed from the semantic PBW collection.  The first three families perform
the low-weight cancellation; `pbw` contains the four decisive normalized PBW coordinates. -/
inductive PreThetaCoordinate where
  | x (i : I)
  | y (k : K)
  | xx (i j : I)
  | pbw (c : @RelevantCoordinate I K)

/-- The correct coefficient functional on a pre-Theta polynomial.  In the `pbw` case this is
the PBW-normalized coefficient, so in particular it incorporates `yx = xy - [x,y]`. -/
def preThetaProjection (D : Data I K q) :
    (@PreThetaCoordinate I K) → (@RawExpression I K) →ₗ[ℤ] ℤ
  | .x i => rawCoefficient [.x i]
  | .y k => rawCoefficient [.y k]
  | .xx i j => rawCoefficient [.x i, .x j]
  | .pbw c => D.rawPBWProjection c

/-- A degree-three Lie lift has only its named `z` coordinate among the coordinates read here. -/
def preThetaRightCoefficient (lieZ : ℤ) : @PreThetaCoordinate I K → ℤ
  | .pbw .z => lieZ
  | _ => 0

/-- The coordinate interpretation of the terminal semantic ledger, before the adjacent
weight-two syzygies are resolved.  This is a family of genuine PBW coefficient equalities,
not the stronger and generally false assertion that the unnormalized words are literally equal
in a free monoid algebra. -/
structure PreThetaEquation (P : PreTheta (I := I) (K := K))
    (T : RelationTails (I := I) (K := K)) (ζ : ZMod q) where
  lieZ : ℤ
  lieZ_mod : (lieZ : ZMod q) = ζ
  collected_eq : ∀ c : @PreThetaCoordinate I K,
    preThetaProjection D c (P.polynomial D T) = preThetaRightCoefficient lieZ c

/-! ## Low PBW coefficients -/

theorem rawCoefficient_tableRemainder_x
    (T : RelationTails (I := I) (K := K))
    (R : TableRemainder (I := I) (K := K)) (i : I) :
    rawCoefficient [.x i] (TableRemainder.expression (D := D) T R) = 0 := by
  induction R with
  | zero => simp [TableRemainder.expression]
  | add p r hp hr => simp [TableRemainder.expression, hp, hr]
  | scale n p hp => simp [TableRemainder.expression, hp]
  | typeV a b c hab hbc =>
      simp [TableRemainder.expression, coreWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
        rawTerm_mul_rawWord, rawWord_mul_rawTerm]
  | typeVI a b c hab hbc =>
      simp [TableRemainder.expression, coreWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
        rawTerm_mul_rawWord, rawWord_mul_rawTerm]
  | typeVII a b c hab hbc =>
      simp [TableRemainder.expression, coreWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
        rawTerm_mul_rawWord, rawWord_mul_rawTerm]
  | rXY a b k =>
      simp [TableRemainder.expression, exceptionalWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawTerm_mul_rawWord]
  | XXs a b k =>
      simp [TableRemainder.expression, exceptionalWordExpression, sRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawWord_mul_rawTerm]
  | rZ a =>
      simp [TableRemainder.expression, exceptionalWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawTerm_mul_rawWord]
  | Xt a =>
      simp [TableRemainder.expression, exceptionalWordExpression, tRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawWord_mul_rawTerm]

theorem rawCoefficient_tableRemainder_y
    (T : RelationTails (I := I) (K := K))
    (R : TableRemainder (I := I) (K := K)) (k : K) :
    rawCoefficient [.y k] (TableRemainder.expression (D := D) T R) = 0 := by
  induction R with
  | zero => simp [TableRemainder.expression]
  | add p r hp hr => simp [TableRemainder.expression, hp, hr]
  | scale n p hp => simp [TableRemainder.expression, hp]
  | typeV a b c hab hbc =>
      simp [TableRemainder.expression, coreWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
        rawTerm_mul_rawWord, rawWord_mul_rawTerm]
  | typeVI a b c hab hbc =>
      simp [TableRemainder.expression, coreWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
        rawTerm_mul_rawWord, rawWord_mul_rawTerm]
  | typeVII a b c hab hbc =>
      simp [TableRemainder.expression, coreWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
        rawTerm_mul_rawWord, rawWord_mul_rawTerm]
  | rXY a b l =>
      simp [TableRemainder.expression, exceptionalWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawTerm_mul_rawWord]
  | XXs a b l =>
      simp [TableRemainder.expression, exceptionalWordExpression, sRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawWord_mul_rawTerm]
  | rZ a =>
      simp [TableRemainder.expression, exceptionalWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawTerm_mul_rawWord]
  | Xt a =>
      simp [TableRemainder.expression, exceptionalWordExpression, tRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawWord_mul_rawTerm]

theorem rawCoefficient_tableRemainder_xx
    (T : RelationTails (I := I) (K := K))
    (R : TableRemainder (I := I) (K := K)) (i j : I) :
    rawCoefficient [.x i, .x j] (TableRemainder.expression (D := D) T R) = 0 := by
  induction R with
  | zero => simp [TableRemainder.expression]
  | add p r hp hr => simp [TableRemainder.expression, hp, hr]
  | scale n p hp => simp [TableRemainder.expression, hp]
  | typeV a b c hab hbc =>
      simp [TableRemainder.expression, coreWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
        rawTerm_mul_rawWord, rawWord_mul_rawTerm]
  | typeVI a b c hab hbc =>
      simp [TableRemainder.expression, coreWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
        rawTerm_mul_rawWord, rawWord_mul_rawTerm]
  | typeVII a b c hab hbc =>
      simp [TableRemainder.expression, coreWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
        rawTerm_mul_rawWord, rawWord_mul_rawTerm]
  | rXY a b k =>
      simp [TableRemainder.expression, exceptionalWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawTerm_mul_rawWord]
  | XXs a b k =>
      simp [TableRemainder.expression, exceptionalWordExpression, sRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawWord_mul_rawTerm]
  | rZ a =>
      simp [TableRemainder.expression, exceptionalWordExpression, rRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawTerm_mul_rawWord]
  | Xt a =>
      simp [TableRemainder.expression, exceptionalWordExpression, tRelation,
        sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, rawWord_mul_rawTerm]

/- The three following formulas are the literal PBW comparisons in weights one and two. -/

@[simp]
theorem upperPairs_equal_indicator_zero (a : I → I → ℤ) (i : I) :
    (∑ ij ∈ upperPairs I,
      if i = ij.1 ∧ i = ij.2 then a ij.1 ij.2 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro ij hij
  rw [if_neg]
  rintro ⟨hi, hj⟩
  have hne : ij.1 ≠ ij.2 := ne_of_lt (mem_upperPairs.mp hij)
  exact hne (hi.symm.trans hj)

@[simp]
theorem diagonal_ordered_indicator_zero (a : I → ℤ) {i j : I} (hij : i ≠ j) :
    (∑ x, if i = x ∧ j = x then a x else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [if_neg]
  rintro ⟨hi, hj⟩
  exact hij (hi.trans hj.symm)

@[simp]
theorem upperPairs_ordered_indicator (a : I → I → ℤ) {i j : I} (hij : i < j) :
    (∑ xy ∈ upperPairs I,
      if i = xy.1 ∧ j = xy.2 then a xy.1 xy.2 else 0) = a i j := by
  classical
  rw [Finset.sum_eq_single (i, j)]
  · simp
  · intro xy hxy hne
    rw [if_neg]
    rintro ⟨hi, hj⟩
    exact hne (Prod.ext hi.symm hj.symm)
  · simp [mem_upperPairs, hij]

theorem rawCoefficient_preTheta_x
    (P : PreTheta (I := I) (K := K)) (T : RelationTails (I := I) (K := K))
    (i : I) :
    rawCoefficient [.x i] (P.polynomial D T) = (D.d i : ℤ) * P.r i := by
  classical
  simp [PreTheta.polynomial, rRelation, sRelation, tRelation, coreWordExpression,
    sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
    rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
    rawWord_mul_rawWord,
    rawCoefficient_tableRemainder_x]
  ring

theorem rawCoefficient_preTheta_y
    (P : PreTheta (I := I) (K := K)) (T : RelationTails (I := I) (K := K))
    (k : K) :
    rawCoefficient [.y k] (P.polynomial D T) =
      -(∑ i, P.r i * D.B i k) + (D.e k : ℤ) * P.s k := by
  classical
  simp [PreTheta.polynomial, rRelation, sRelation, tRelation, coreWordExpression,
    sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
    rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
    rawWord_mul_rawWord,
    rawCoefficient_tableRemainder_y]
  ring

theorem rawCoefficient_preTheta_xx_diag
    (P : PreTheta (I := I) (K := K)) (T : RelationTails (I := I) (K := K))
    (i : I) :
    rawCoefficient [.x i, .x i] (P.polynomial D T) =
      (D.d i : ℤ) * P.rxx i := by
  classical
  simp [PreTheta.polynomial, rRelation, sRelation, tRelation, coreWordExpression,
    sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
    rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
    rawWord_mul_rawWord,
    rawCoefficient_tableRemainder_xx]
  simp_rw [Finset.sum_add_distrib]
  rw [upperPairs_equal_indicator_zero
    (fun a b ↦ P.rx a b * (D.d a : ℤ)) i]
  rw [upperPairs_equal_indicator_zero
    (fun a b ↦ P.xr a b * (D.d b : ℤ)) i]
  ring

theorem rawCoefficient_preTheta_xx
    (P : PreTheta (I := I) (K := K)) (T : RelationTails (I := I) (K := K))
    {i j : I} (hij : i < j) :
    rawCoefficient [.x i, .x j] (P.polynomial D T) =
      (D.d i : ℤ) * P.rx i j + (D.d j : ℤ) * P.xr i j := by
  classical
  simp [PreTheta.polynomial, rRelation, sRelation, tRelation, coreWordExpression,
    sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
    rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
    rawWord_mul_rawWord,
    rawCoefficient_tableRemainder_xx, hij.ne, hij]
  simp_rw [Finset.sum_add_distrib]
  rw [upperPairs_ordered_indicator
    (fun a b ↦ P.rx a b * (D.d a : ℤ)) hij]
  rw [upperPairs_ordered_indicator
    (fun a b ↦ P.xr a b * (D.d b : ℤ)) hij]
  ring

/-! ## Cancellation and construction of Theta -/

/-- Cancellation in the torsion-free group `ℤ`. -/
theorem int_mul_eq_zero_cancel {d a : ℤ} (hd : d ≠ 0) (h : d * a = 0) : a = 0 := by
  exact (mul_eq_zero.mp h).resolve_left hd

/-- The adjacent Smith syzygy used to form Type II. -/
theorem adjacent_smith_syzygy
    {di dj : ℕ} (hdi : 0 < di) (hdiv : di ∣ dj) {a c : ℤ}
    (h : (di : ℤ) * a + (dj : ℤ) * c = 0) :
    a = (dj / di : ℕ) * (-c) := by
  obtain ⟨r, rfl⟩ := hdiv
  have hratio : di * r / di = r := by
    simpa [Nat.mul_comm] using Nat.mul_div_left r hdi
  rw [Nat.cast_mul] at h
  have hfactor : (di : ℤ) * (a + (r : ℤ) * c) = 0 := by
    nlinarith
  have hzero : a + (r : ℤ) * c = 0 :=
    int_mul_eq_zero_cancel (by exact_mod_cast hdi.ne') hfactor
  rw [hratio]
  push_cast
  linarith

/-- The Type-II coefficient extracted from a pre-Theta ledger. -/
def PreTheta.typeIICoefficient (P : PreTheta (I := I) (K := K)) (i j : I) : ℤ :=
  -P.xr i j

/-- The collected expression obtained after deleting the vanishing low rows and replacing every
upper-pair placement by its Type-II adjacent syzygy. -/
def PreTheta.collectedExpression (P : PreTheta (I := I) (K := K)) :
    D.CollectedExpression where
  u := P.typeIICoefficient
  v := P.v
  v' := P.v'
  t := P.t
  sY := P.sY
  Ys := P.Ys

/-- **Construction of Theta.**  A fully collected adapted ledger whose right side is a
degree-three Lie element canonically produces the Type-I--VII normal form required by the PBW
coefficient comparison. -/
def PreThetaEquation.toPBWNormalFormEquation
    (P : PreTheta (I := I) (K := K))
    (T : RelationTails (I := I) (K := K)) {ζ : ZMod q}
    (hD : D.Identities) (hd : ∀ i, 0 < D.d i) (he : ∀ k, 0 < D.e k)
    (h : PreThetaEquation D P T ζ) :
    PBWNormalFormEquation D (P.collectedExpression D) ζ := by
  have hr : ∀ i, P.r i = 0 := by
    intro i
    have heq := h.collected_eq (.x i)
    change rawCoefficient [.x i] (P.polynomial D T) = 0 at heq
    rw [rawCoefficient_preTheta_x D P T] at heq
    exact int_mul_eq_zero_cancel (by exact_mod_cast (hd i).ne') heq
  have hs : ∀ k, P.s k = 0 := by
    intro k
    have heq := h.collected_eq (.y k)
    change rawCoefficient [.y k] (P.polynomial D T) = 0 at heq
    rw [rawCoefficient_preTheta_y D P T] at heq
    simp only [hr, zero_mul, Finset.sum_const_zero, neg_zero, zero_add] at heq
    exact int_mul_eq_zero_cancel (by exact_mod_cast (he k).ne') heq
  have hrxx : ∀ i, P.rxx i = 0 := by
    intro i
    have heq := h.collected_eq (.xx i i)
    change rawCoefficient [.x i, .x i] (P.polynomial D T) = 0 at heq
    rw [rawCoefficient_preTheta_xx_diag D P T] at heq
    exact int_mul_eq_zero_cancel (by exact_mod_cast (hd i).ne') heq
  have hpair : ∀ {i j}, i < j →
      P.rx i j = (D.dRatio i j : ℤ) * P.typeIICoefficient i j := by
    intro i j hij
    have heq := h.collected_eq (.xx i j)
    change rawCoefficient [.x i, .x j] (P.polynomial D T) = 0 at heq
    rw [rawCoefficient_preTheta_xx D P T hij] at heq
    have hsyz := adjacent_smith_syzygy (hd i) (hD.d_dvd hij.le) heq
    simpa [PreTheta.typeIICoefficient, dRatio] using hsyz
  have hupper :
      (∑ ij ∈ upperPairs I, (
        rawScale (P.rx ij.1 ij.2) (D.rRelation T ij.1 * rawWord [.x ij.2]) +
        rawScale (P.xr ij.1 ij.2) (rawWord [.x ij.1] * D.rRelation T ij.2))) =
      ∑ ij ∈ upperPairs I,
        rawScale (P.typeIICoefficient ij.1 ij.2)
          (D.coreWordExpression T (.typeII ij.1 ij.2)) := by
    apply Finset.sum_congr rfl
    intro ij hijmem
    have hij := mem_upperPairs.mp hijmem
    rw [hpair hij]
    unfold coreWordExpression PreTheta.typeIICoefficient rawScale
    module
  have hupper' :
      (∑ ij ∈ upperPairs I, (
        P.rx ij.1 ij.2 • (D.rRelation T ij.1 * rawWord [.x ij.2]) +
        P.xr ij.1 ij.2 • (rawWord [.x ij.1] * D.rRelation T ij.2))) =
      ∑ ij ∈ upperPairs I,
        (-P.xr ij.1 ij.2) • D.coreWordExpression T (.typeII ij.1 ij.2) := by
    simpa only [rawScale, PreTheta.typeIICoefficient] using hupper
  have hpolynomial :
      P.polynomial D T =
        literalCollectedPolynomial D (P.collectedExpression D) T +
          TableRemainder.expression (D := D) T P.remainder := by
    classical
    simp only [PreTheta.polynomial, literalCollectedPolynomial,
      PreTheta.collectedExpression, PreTheta.typeIICoefficient]
    simp_rw [hr, hs, hrxx]
    simp only [rawScale, zero_smul, Finset.sum_const_zero, zero_add]
    rw [hupper']
    abel
  refine
    { lieZ := h.lieZ
      lieZ_mod := h.lieZ_mod
      coordinate_eq := ?_ }
  intro c hc
  cases c with
  | xy i k =>
      have heq := h.collected_eq (.pbw (.xy i k))
      change D.rawPBWProjection (.xy i k) (P.polynomial D T) = 0 at heq
      rw [hpolynomial, map_add,
        rawPBWProjection_tableRemainder_zero D T P.remainder (.xy i k) hc,
        add_zero] at heq
      rw [rawPBWProjection_literalCollectedPolynomial_xy] at heq
      exact heq
  | z =>
      have heq := h.collected_eq (.pbw .z)
      change D.rawPBWProjection .z (P.polynomial D T) = h.lieZ at heq
      rw [hpolynomial, map_add,
        rawPBWProjection_tableRemainder_zero D T P.remainder .z hc,
        add_zero] at heq
      rw [rawPBWProjection_literalCollectedPolynomial_z] at heq
      exact heq
  | yy k l =>
      have heq := h.collected_eq (.pbw (.yy k l))
      change D.rawPBWProjection (.yy k l) (P.polynomial D T) = 0 at heq
      rw [hpolynomial, map_add,
        rawPBWProjection_tableRemainder_zero D T P.remainder (.yy k l) hc,
        add_zero] at heq
      rw [rawPBWProjection_literalCollectedPolynomial_yy (hkl := hc)] at heq
      exact heq
  | ySquare k =>
      have heq := h.collected_eq (.pbw (.ySquare k))
      change D.rawPBWProjection (.ySquare k) (P.polynomial D T) = 0 at heq
      rw [hpolynomial, map_add,
        rawPBWProjection_tableRemainder_zero D T P.remainder (.ySquare k) hc,
        add_zero] at heq
      rw [rawPBWProjection_literalCollectedPolynomial_ySquare] at heq
      exact heq

/-- **Full coefficient system from the unreduced collected ledger.**  This is the composite
form of the PBW collection lemma: the low rows are cancelled, Type II is constructed, and all
four equations `(B)`, `(Z)`, `(C1)`, `(C2)` are returned. -/
def PreThetaEquation.toCoefficientSystem
    (P : PreTheta (I := I) (K := K))
    (T : RelationTails (I := I) (K := K)) {ζ : ZMod q}
    (hD : D.Identities) (hd : ∀ i, 0 < D.d i) (he : ∀ k, 0 < D.e k)
    (h : PreThetaEquation D P T ζ) : D.CoefficientSystem ζ :=
  coefficientSystemOfPBWNormalForm D (P.collectedExpression D)
    (PreThetaEquation.toPBWNormalFormEquation D P T hD hd he h)

end CollectedExpression

end Data

end

end Coordinate

end DegreeFive

end LieRings
