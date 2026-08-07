import LieRings.DimensionSubring.DegreeFive.AdaptedPBWBridge

/-!
# Reading terminal adapted packets by PBW coordinates

The lemmas in this file are the semantic half of `PreThetaEquation`: they partition the
terminal ledger by its literal row/factor shape and evaluate the corresponding genuine PBW
coefficient.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable {L : Type u} [LieRing L] [Finite L]

private theorem adaptedWeightSum_eq_zero_iff
    (xs : List (AdaptedLowBasisIndex L)) :
    (xs.map (adaptedLowBasisWeight L)).sum = 0 ↔ xs = [] := by
  constructor
  · intro h
    cases xs with
    | nil => rfl
    | cons x xs =>
        simp only [List.map_cons, List.sum_cons] at h
        have hx := adaptedLowBasisWeight_pos L x
        omega
  · rintro rfl
    rfl

private theorem adaptedWeightSum_eq_one_iff
    (xs : List (AdaptedLowBasisIndex L)) :
    (xs.map (adaptedLowBasisWeight L)).sum = 1 ↔
      ∃ x, xs = [x] ∧ adaptedLowBasisWeight L x = 1 := by
  constructor
  · intro h
    cases xs with
    | nil => simp at h
    | cons x xs =>
        have hx := adaptedLowBasisWeight_pos L x
        have htail : (xs.map (adaptedLowBasisWeight L)).sum = 0 := by
          simp only [List.map_cons, List.sum_cons] at h
          omega
        have hxone : adaptedLowBasisWeight L x = 1 := by
          simp only [List.map_cons, List.sum_cons] at h
          omega
        rw [(adaptedWeightSum_eq_zero_iff (L := L) xs).mp htail]
        exact ⟨x, rfl, hxone⟩
  · rintro ⟨x, rfl, hx⟩
    simpa using hx

private theorem adaptedWeightSum_eq_two_iff
    (xs : List (AdaptedLowBasisIndex L)) :
    (xs.map (adaptedLowBasisWeight L)).sum = 2 ↔
      (∃ x, xs = [x] ∧ adaptedLowBasisWeight L x = 2) ∨
      (∃ x y, xs = [x, y] ∧ adaptedLowBasisWeight L x = 1 ∧
        adaptedLowBasisWeight L y = 1) := by
  constructor
  · intro h
    cases xs with
    | nil => simp at h
    | cons x tail =>
      simp only [List.map_cons, List.sum_cons] at h
      have hx := adaptedLowBasisWeight_pos L x
      rcases Nat.eq_zero_or_pos ((tail.map (adaptedLowBasisWeight L)).sum) with
        htailzero | htailpos
      · have htail : tail = [] :=
          (adaptedWeightSum_eq_zero_iff (L := L) tail).mp htailzero
        left
        exact ⟨x, by simp [htail], by omega⟩
      · have hxone : adaptedLowBasisWeight L x = 1 := by omega
        have htailone : (tail.map (adaptedLowBasisWeight L)).sum = 1 := by omega
        obtain ⟨y, rfl, hy⟩ :=
          (adaptedWeightSum_eq_one_iff (L := L) tail).mp htailone
        right
        exact ⟨x, y, rfl, hxone, hy⟩
  · rintro (⟨x, rfl, hx⟩ | ⟨x, y, rfl, hx, hy⟩)
    · simp [hx]
    · simp [hx, hy]

private theorem adaptedWeightSum_eq_three_iff
    (xs : List (AdaptedLowBasisIndex L)) :
    (xs.map (adaptedLowBasisWeight L)).sum = 3 ↔
      (∃ x, xs = [x] ∧ adaptedLowBasisWeight L x = 3) ∨
      (∃ x y, xs = [x, y] ∧ adaptedLowBasisWeight L x = 1 ∧
        adaptedLowBasisWeight L y = 2) ∨
      (∃ x y, xs = [x, y] ∧ adaptedLowBasisWeight L x = 2 ∧
        adaptedLowBasisWeight L y = 1) ∨
      (∃ x y z, xs = [x, y, z] ∧ adaptedLowBasisWeight L x = 1 ∧
        adaptedLowBasisWeight L y = 1 ∧ adaptedLowBasisWeight L z = 1) := by
  constructor
  · intro h
    cases xs with
    | nil => simp at h
    | cons x tail =>
      simp only [List.map_cons, List.sum_cons] at h
      have hx := adaptedLowBasisWeight_pos L x
      rcases Nat.eq_zero_or_pos ((tail.map (adaptedLowBasisWeight L)).sum) with
        htailzero | htailpos
      · have htail := (adaptedWeightSum_eq_zero_iff (L := L) tail).mp htailzero
        exact Or.inl ⟨x, by simp [htail], by omega⟩
      · by_cases htailone : (tail.map (adaptedLowBasisWeight L)).sum = 1
        · obtain ⟨y, rfl, hy⟩ :=
            (adaptedWeightSum_eq_one_iff (L := L) tail).mp htailone
          have hxtwo : adaptedLowBasisWeight L x = 2 := by omega
          exact Or.inr (Or.inr (Or.inl ⟨x, y, rfl, hxtwo, hy⟩))
        · have htailtwo : (tail.map (adaptedLowBasisWeight L)).sum = 2 := by
            omega
          have hxone : adaptedLowBasisWeight L x = 1 := by omega
          rcases (adaptedWeightSum_eq_two_iff (L := L) tail).mp htailtwo with
            ⟨y, rfl, hy⟩ | ⟨y, z, rfl, hy, hz⟩
          · exact Or.inr (Or.inl ⟨x, y, rfl, hxone, hy⟩)
          · exact Or.inr (Or.inr (Or.inr ⟨x, y, z, rfl, hxone, hy, hz⟩))
  · rintro (⟨x, rfl, hx⟩ | ⟨x, y, rfl, hx, hy⟩ |
      ⟨x, y, rfl, hx, hy⟩ | ⟨x, y, z, rfl, hx, hy, hz⟩)
    all_goals simp_all

theorem AdaptedSmithPlacedPacket.externalWeight_eq_zero_iff
    (p : AdaptedSmithPlacedPacket L L (canonicalFreeLieEvaluation L)) :
    p.externalWeight L = 0 ↔ p.left = [] ∧ p.right = [] := by
  rw [AdaptedSmithPlacedPacket.externalWeight, Nat.add_eq_zero]
  simp only [adaptedWeightSum_eq_zero_iff]

theorem AdaptedSmithPlacedPacket.externalWeight_eq_one_iff
    (p : AdaptedSmithPlacedPacket L L (canonicalFreeLieEvaluation L)) :
    p.externalWeight L = 1 ↔
      (∃ x, p.left = [x] ∧ p.right = [] ∧ adaptedLowBasisWeight L x = 1) ∨
      (∃ x, p.left = [] ∧ p.right = [x] ∧ adaptedLowBasisWeight L x = 1) := by
  rw [AdaptedSmithPlacedPacket.externalWeight]
  constructor
  · intro h
    rcases Nat.add_eq_one_iff.mp h with h | h
    · right
      have hl := (adaptedWeightSum_eq_zero_iff (L := L) p.left).mp h.1
      obtain ⟨x, hr, hx⟩ :=
        (adaptedWeightSum_eq_one_iff (L := L) p.right).mp h.2
      exact ⟨x, hl, hr, hx⟩
    · left
      obtain ⟨x, hl, hx⟩ :=
        (adaptedWeightSum_eq_one_iff (L := L) p.left).mp h.1
      have hr := (adaptedWeightSum_eq_zero_iff (L := L) p.right).mp h.2
      exact ⟨x, hl, hr, hx⟩
  · rintro (⟨x, hl, hr, hx⟩ | ⟨x, hl, hr, hx⟩)
    · simp [hl, hr, hx]
    · simp [hl, hr, hx]

theorem AdaptedSmithPlacedPacket.externalWeight_eq_two_iff
    (p : AdaptedSmithPlacedPacket L L (canonicalFreeLieEvaluation L)) :
    p.externalWeight L = 2 ↔
      (∃ x, p.left = [x] ∧ p.right = [] ∧ adaptedLowBasisWeight L x = 2) ∨
      (∃ x, p.left = [] ∧ p.right = [x] ∧ adaptedLowBasisWeight L x = 2) ∨
      (∃ x y, p.left = [x, y] ∧ p.right = [] ∧
        adaptedLowBasisWeight L x = 1 ∧ adaptedLowBasisWeight L y = 1) ∨
      (∃ x y, p.left = [x] ∧ p.right = [y] ∧
        adaptedLowBasisWeight L x = 1 ∧ adaptedLowBasisWeight L y = 1) ∨
      (∃ x y, p.left = [] ∧ p.right = [x, y] ∧
        adaptedLowBasisWeight L x = 1 ∧ adaptedLowBasisWeight L y = 1) := by
  rw [AdaptedSmithPlacedPacket.externalWeight]
  let A := (p.left.map (adaptedLowBasisWeight L)).sum
  let B := (p.right.map (adaptedLowBasisWeight L)).sum
  constructor
  · intro h
    have hcases : A = 0 ∨ A = 1 ∨ A = 2 := by omega
    rcases hcases with hA | hA | hA
    · have hB : B = 2 := by omega
      have hl := (adaptedWeightSum_eq_zero_iff (L := L) p.left).mp hA
      rcases (adaptedWeightSum_eq_two_iff (L := L) p.right).mp hB with
        ⟨x, hr, hx⟩ | ⟨x, y, hr, hx, hy⟩
      · exact Or.inr (Or.inl ⟨x, hl, hr, hx⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, y, hl, hr, hx, hy⟩)))
    · have hB : B = 1 := by omega
      obtain ⟨x, hl, hx⟩ :=
        (adaptedWeightSum_eq_one_iff (L := L) p.left).mp hA
      obtain ⟨y, hr, hy⟩ :=
        (adaptedWeightSum_eq_one_iff (L := L) p.right).mp hB
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, hl, hr, hx, hy⟩)))
    · have hB : B = 0 := by omega
      have hr := (adaptedWeightSum_eq_zero_iff (L := L) p.right).mp hB
      rcases (adaptedWeightSum_eq_two_iff (L := L) p.left).mp hA with
        ⟨x, hl, hx⟩ | ⟨x, y, hl, hx, hy⟩
      · exact Or.inl ⟨x, hl, hr, hx⟩
      · exact Or.inr (Or.inr (Or.inl ⟨x, y, hl, hr, hx, hy⟩))
  · rintro (⟨x, hl, hr, hx⟩ | ⟨x, hl, hr, hx⟩ |
      ⟨x, y, hl, hr, hx, hy⟩ | ⟨x, y, hl, hr, hx, hy⟩ |
      ⟨x, y, hl, hr, hx, hy⟩)
    · simp [A, B, hl, hr, hx]
    · simp [A, B, hl, hr, hx]
    · simp [A, B, hl, hr, hx, hy]
    · simp [A, B, hl, hr, hx, hy]
    · simp [A, B, hl, hr, hx, hy]

@[simp] theorem adaptedCoordinateXFactor_inj_iff
    (i j : FreeLieExactBasisIndex L 1) :
    adaptedCoordinateXFactor L i = adaptedCoordinateXFactor L j ↔ i = j := by
  constructor
  · intro h
    have hv := congrArg (adaptedLowBasisValue L L
      (canonicalFreeLieEvaluation L)) h
    simp only [adaptedCoordinateXFactor,
      adaptedLowBasisValue_indexOf] at hv
    exact (collectedHomogeneousBasis L L (canonicalFreeLieEvaluation L) 1).injective
      (Subtype.ext hv)
  · rintro rfl
    rfl

@[simp] theorem adaptedCoordinateYFactor_inj_iff
    (k l : FreeLieExactBasisIndex L 2) :
    adaptedCoordinateYFactor L k = adaptedCoordinateYFactor L l ↔ k = l := by
  constructor
  · intro h
    have hv := congrArg (adaptedLowBasisValue L L
      (canonicalFreeLieEvaluation L)) h
    simp only [adaptedCoordinateYFactor,
      adaptedLowBasisValue_indexOf] at hv
    exact (collectedHomogeneousBasis L L (canonicalFreeLieEvaluation L) 2).injective
      (Subtype.ext hv)
  · rintro rfl
    rfl

@[simp] theorem adaptedCoordinateXFactor_ne_y
    (i : FreeLieExactBasisIndex L 1) (k : FreeLieExactBasisIndex L 2) :
    adaptedCoordinateXFactor L i ≠ adaptedCoordinateYFactor L k := by
  intro h
  have hw := congrArg (adaptedLowBasisWeight L) h
  simp at hw

@[simp] theorem adaptedCoordinateYFactor_ne_x
    (k : FreeLieExactBasisIndex L 2) (i : FreeLieExactBasisIndex L 1) :
    adaptedCoordinateYFactor L k ≠ adaptedCoordinateXFactor L i :=
  Ne.symm (adaptedCoordinateXFactor_ne_y (L := L) i k)

@[simp] theorem adaptedCoordinateXFactor_le_iff
    (i j : FreeLieExactBasisIndex L 1) :
    adaptedCoordinateXFactor L i ≤ adaptedCoordinateXFactor L j ↔ i ≤ j := by
  change toLex ((0 : ℕ), i.1) ≤ toLex ((0 : ℕ), j.1) ↔ i.1 ≤ j.1
  rw [Prod.Lex.le_iff]
  simp

@[simp] theorem adaptedCoordinateYFactor_le_iff
    (k l : FreeLieExactBasisIndex L 2) :
    adaptedCoordinateYFactor L k ≤ adaptedCoordinateYFactor L l ↔ k ≤ l := by
  change toLex ((1 : ℕ), k.1) ≤ toLex ((1 : ℕ), l.1) ↔ k.1 ≤ l.1
  rw [Prod.Lex.le_iff]
  simp

@[simp] theorem adaptedCoordinateXFactor_le_y
    (i : FreeLieExactBasisIndex L 1) (k : FreeLieExactBasisIndex L 2) :
    adaptedCoordinateXFactor L i ≤ adaptedCoordinateYFactor L k := by
  change toLex ((0 : ℕ), i.1) ≤ toLex ((1 : ℕ), k.1)
  exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (by omega))

@[simp] theorem adaptedCoordinateYFactor_not_le_x
    (k : FreeLieExactBasisIndex L 2) (i : FreeLieExactBasisIndex L 1) :
    ¬ adaptedCoordinateYFactor L k ≤ adaptedCoordinateXFactor L i := by
  change ¬ toLex ((1 : ℕ), k.1) ≤ toLex ((0 : ℕ), i.1)
  rw [Prod.Lex.le_iff]
  simp

namespace StandingReductionData

local notation "F" => CanonicalFreeLie L
local notation "ev" => canonicalFreeLieEvaluation L
local notation "I" => CoordinateI L
local notation "K" => CoordinateK L

variable (R : StandingReductionData L)

@[simp] private theorem classTwoWeightOne_le_iff (i j : I) :
    (FiniteClassTwoBasisIndex.weightOne i : FiniteClassTwoBasisIndex L) ≤
        .weightOne j ↔ i ≤ j := by
  change toLex ((0 : ℕ), i.1) ≤ toLex ((0 : ℕ), j.1) ↔ i.1 ≤ j.1
  rw [Prod.Lex.le_iff]
  simp

@[simp] private theorem classTwoWeightOne_le_weightTwo (i : I) (k : K) :
    (FiniteClassTwoBasisIndex.weightOne i : FiniteClassTwoBasisIndex L) ≤
        .weightTwo k := by
  change toLex ((0 : ℕ), i.1) ≤ toLex ((1 : ℕ), k.1)
  exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (by omega))

private theorem adaptedTriangular_toLieHom_apply
    (x : FreeClassTwo (GeneratorModule L))
    (p : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) :
    (adaptedHomogeneousClassTwoTriangularRepresentation L L ev).toLieHom x p =
      adaptedHomogeneousClassTwoAction L L ev x p := rfl

private theorem moduleEnd_zsmul_apply
    (n : ℤ)
    (f : Module.End ℤ (MvPolynomial (FiniteClassTwoBasisIndex L) ℤ))
    (p : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) :
    (n • f) p = n • f p := by
  rfl

private theorem coefficient_X_mul_zsmul_X
    (u v : FiniteClassTwoBasisIndex L) (n : ℤ)
    (e : FiniteClassTwoBasisIndex L →₀ ℕ) :
    MvPolynomial.coeff e
        ((MvPolynomial.X u : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
          n • MvPolynomial.X v) =
      if Finsupp.single u 1 + Finsupp.single v 1 = e then n else 0 := by
  classical
  by_cases he : Finsupp.single u 1 + Finsupp.single v 1 = e
  · rw [if_pos he, ← he, MvPolynomial.coeff_X_mul]
    change (MvPolynomial.lcoeff ℤ (Finsupp.single v 1))
      (n • (MvPolynomial.X v :
        MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) = n
    rw [map_zsmul (MvPolynomial.lcoeff ℤ (Finsupp.single v 1))]
    simp
  · rw [if_neg he]
    by_contra hc
    have hs := MvPolynomial.mem_support_iff.mpr hc
    have hs' := MvPolynomial.support_mul
      (MvPolynomial.X u : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) _ hs
    rw [Finset.mem_add] at hs'
    obtain ⟨f, hf, g, hg, hfg⟩ := hs'
    rw [MvPolynomial.support_X] at hf
    simp only [Finset.mem_singleton] at hf
    subst f
    have hg' := MvPolynomial.support_smul hg
    rw [MvPolynomial.support_X] at hg'
    simp only [Finset.mem_singleton] at hg'
    subst g
    exact he hfg

private theorem coefficient_zsmul_X
    (u : FiniteClassTwoBasisIndex L) (n : ℤ)
    (e : FiniteClassTwoBasisIndex L →₀ ℕ) :
    MvPolynomial.coeff e
        (n • (MvPolynomial.X u :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) =
      if Finsupp.single u 1 = e then n else 0 := by
  change (MvPolynomial.lcoeff ℤ e)
      (n • (MvPolynomial.X u :
        MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) = _
  rw [map_zsmul (MvPolynomial.lcoeff ℤ e)]
  change n • MvPolynomial.coeff e (MvPolynomial.X u) = _
  rw [MvPolynomial.coeff_X']
  by_cases h : Finsupp.single u 1 = e <;> simp [h]

private theorem xExponent_add_eq_diag_iff (i j a : I) :
    xExponent (L := L) i + xExponent (L := L) j = xxExponent (L := L) a a ↔
      i = a ∧ j = a := by
  simp only [xxExponent, xExponent]
  rw [
    Finsupp.single_add_single_eq_single_add_single (one_ne_zero : (1 : ℕ) ≠ 0)
      (one_ne_zero : (1 : ℕ) ≠ 0)]
  simp

private theorem yExponent_add_eq_diag_iff (h b k : K) :
    yExponent (L := L) h + yExponent (L := L) b = yyExponent (L := L) k k ↔
      h = k ∧ b = k := by
  simp only [yyExponent, yExponent]
  rw [
    Finsupp.single_add_single_eq_single_add_single (one_ne_zero : (1 : ℕ) ≠ 0)
      (one_ne_zero : (1 : ℕ) ≠ 0)]
  simp

private theorem yExponent_add_eq_offdiag_iff
    {h b k l : K} (hkl : k ≠ l) :
    yExponent (L := L) h + yExponent (L := L) b = yyExponent (L := L) k l ↔
      (h = k ∧ b = l) ∨ (h = l ∧ b = k) := by
  simp only [yyExponent, yExponent]
  rw [
    Finsupp.single_add_single_eq_single_add_single (one_ne_zero : (1 : ℕ) ≠ 0)
      (one_ne_zero : (1 : ℕ) ≠ 0)]
  simp [hkl]

private theorem sum_sum_offdiag_indicator
    (f : K → K → ℤ) {k l : K} (hkl : k ≠ l) :
    (∑ h : K, ∑ b : K,
      if (h = k ∧ b = l) ∨ (h = l ∧ b = k) then f h b else 0) =
      f k l + f l k := by
  classical
  rw [Finset.sum_comm]
  simp_rw [Coordinate.Data.CollectedExpression.sum_unordered_indicator _ k l hkl]
  rw [Finset.sum_add_distrib]
  simp [eq_comm]

private theorem sum_sum_diag_indicator
    (f : K → K → ℤ) (k : K) :
    (∑ h : K, ∑ b : K, if h = k ∧ b = k then f h b else 0) = f k k := by
  classical
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hne
      simp [hne]
    · simp
  · intro h hh hne
    simp [hne]
  · simp

private theorem xExponent_add_eq_offdiag_of_le
    {i j a b : I} (hij : i ≤ j) (hab : a < b)
    (h : xExponent (L := L) i + xExponent (L := L) j =
      xxExponent (L := L) a b) :
    i = a ∧ j = b := by
  simp only [xxExponent, xExponent] at h
  rw [
    Finsupp.single_add_single_eq_single_add_single (one_ne_zero : (1 : ℕ) ≠ 0)
      (one_ne_zero : (1 : ℕ) ≠ 0)] at h
  rcases h with h | h | h
  · exact ⟨FiniteClassTwoBasisIndex.weightOne.inj h.1,
      FiniteClassTwoBasisIndex.weightOne.inj h.2⟩
  · have hi := FiniteClassTwoBasisIndex.weightOne.inj h.2.1
    have hj := FiniteClassTwoBasisIndex.weightOne.inj h.2.2
    subst i
    subst j
    exact (not_le_of_gt hab hij).elim
  · omega

private theorem scalarFirstRow_xCoefficient
    (i j : I) :
    adaptedPBWCoefficient L L ev (xExponent (L := L) i)
        ((⟨[], .row (adaptedCoordinateXFactor L j), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      if i = j then (R.coordinateD i : ℤ) else 0 := by
  classical
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one, adaptedLowRelationRow, adaptedCoordinateXFactor,
    adaptedLowBasisIndexOf]
  change MvPolynomial.coeff (xExponent (L := L) i)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 1 j : F))) = _
  rw [R.firstRow_PBWSymbol]
  change (MvPolynomial.lcoeff ℤ (xExponent (L := L) i))
      ((R.coordinateD j : ℤ) • MvPolynomial.X (.weightOne j) -
        ∑ k, R.coordinateB j k • MvPolynomial.X (.weightTwo k)) = _
  rw [map_sub, map_sum]
  rw [map_zsmul (MvPolynomial.lcoeff ℤ (xExponent (L := L) i))]
  have hcross (k : K) :
      MvPolynomial.coeff (xExponent (L := L) i)
          (R.coordinateB j k • MvPolynomial.X
            (FiniteClassTwoBasisIndex.weightTwo k) :
              MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) = 0 := by
    change (MvPolynomial.lcoeff ℤ (xExponent (L := L) i))
        (R.coordinateB j k • MvPolynomial.X
          (FiniteClassTwoBasisIndex.weightTwo k) :
            MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) = 0
    rw [map_zsmul (MvPolynomial.lcoeff ℤ (xExponent (L := L) i))]
    change R.coordinateB j k •
      MvPolynomial.coeff (xExponent (L := L) i)
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) = 0
    rw [MvPolynomial.coeff_X']
    have hne : Finsupp.single (FiniteClassTwoBasisIndex.weightTwo k) 1 ≠
        xExponent (L := L) i := by
      intro h
      have hval := congrArg
        (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦
          e (FiniteClassTwoBasisIndex.weightTwo k)) h
      simp [xExponent] at hval
    rw [if_neg hne]
    simp
  change (R.coordinateD j : ℤ) •
        MvPolynomial.coeff (xExponent (L := L) i)
          (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j)) -
      ∑ k, MvPolynomial.coeff (xExponent (L := L) i)
        (R.coordinateB j k •
          (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k) :
            MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) = _
  simp_rw [hcross]
  by_cases hij : i = j
  · subst j
    simp [xExponent]
  · have hji : j ≠ i := Ne.symm hij
    simp [xExponent, hij, hji]

private theorem scalarFirstRow_yCoefficient
    (i : I) (k : K) :
    adaptedPBWCoefficient L L ev (yExponent (L := L) k)
        ((⟨[], .row (adaptedCoordinateXFactor L i), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      -R.coordinateB i k := by
  classical
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one, adaptedLowRelationRow, adaptedCoordinateXFactor,
    adaptedLowBasisIndexOf]
  change MvPolynomial.coeff (yExponent (L := L) k)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 1 i : F))) = _
  rw [R.firstRow_PBWSymbol]
  change MvPolynomial.coeff (yExponent (L := L) k)
      ((R.coordinateD i : ℤ) • MvPolynomial.X
          (FiniteClassTwoBasisIndex.weightOne i) -
        ∑ l, R.coordinateB i l • MvPolynomial.X
          (FiniteClassTwoBasisIndex.weightTwo l)) = _
  change (MvPolynomial.lcoeff ℤ (yExponent (L := L) k))
      ((R.coordinateD i : ℤ) • MvPolynomial.X
          (FiniteClassTwoBasisIndex.weightOne i) -
        ∑ l, R.coordinateB i l • MvPolynomial.X
          (FiniteClassTwoBasisIndex.weightTwo l)) = _
  rw [map_sub, map_sum,
    map_zsmul (MvPolynomial.lcoeff ℤ (yExponent (L := L) k))]
  have hx : Finsupp.single (FiniteClassTwoBasisIndex.weightOne i) 1 ≠
      yExponent (L := L) k := by
    intro h
    have hval := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦
      e (FiniteClassTwoBasisIndex.weightOne i)) h
    simp [yExponent] at hval
  change (R.coordinateD i : ℤ) •
        MvPolynomial.coeff (yExponent (L := L) k)
          (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) :
            MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) -
      ∑ l, MvPolynomial.coeff (yExponent (L := L) k)
        (R.coordinateB i l •
          (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l) :
            MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) = _
  rw [MvPolynomial.coeff_X', if_neg hx]
  simp only [smul_eq_mul, mul_zero, zero_sub]
  rw [Finset.sum_eq_single k]
  · congr 1
    change (MvPolynomial.lcoeff ℤ (yExponent (L := L) k))
      (R.coordinateB i k •
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k) :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) = R.coordinateB i k
    rw [map_zsmul (MvPolynomial.lcoeff ℤ (yExponent (L := L) k))]
    change R.coordinateB i k • MvPolynomial.coeff (yExponent (L := L) k)
      (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) = R.coordinateB i k
    simp [yExponent]
  · intro l _ hl
    have hne : Finsupp.single (FiniteClassTwoBasisIndex.weightTwo l) 1 ≠
        yExponent (L := L) k := by
      intro h
      have hval := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦
        e (FiniteClassTwoBasisIndex.weightTwo l)) h
      simp [yExponent, hl] at hval
    change MvPolynomial.coeff (yExponent (L := L) k)
      (R.coordinateB i l •
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l)) = 0
    change (MvPolynomial.lcoeff ℤ (yExponent (L := L) k))
      (R.coordinateB i l •
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l)) = 0
    rw [map_zsmul (MvPolynomial.lcoeff ℤ (yExponent (L := L) k))]
    change R.coordinateB i l • MvPolynomial.coeff (yExponent (L := L) k)
      (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l)) = 0
    rw [MvPolynomial.coeff_X', if_neg hne]
    simp
  · simp

private theorem scalarSecondRow_yCoefficient
    (k l : K) :
    adaptedPBWCoefficient L L ev (yExponent (L := L) k)
        ((⟨[], .row (adaptedCoordinateYFactor L l), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      if k = l then (R.coordinateE k : ℤ) else 0 := by
  classical
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one, adaptedLowRelationRow, adaptedCoordinateYFactor,
    adaptedLowBasisIndexOf]
  change MvPolynomial.coeff (yExponent (L := L) k)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 2 l : F))) = _
  rw [R.secondRow_PBWSymbol]
  change (MvPolynomial.lcoeff ℤ (yExponent (L := L) k))
      ((R.coordinateE l : ℤ) •
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l)) = _
  rw [map_zsmul (MvPolynomial.lcoeff ℤ (yExponent (L := L) k))]
  change (R.coordinateE l : ℤ) •
      MvPolynomial.coeff (yExponent (L := L) k)
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l)) = _
  rw [MvPolynomial.coeff_X']
  by_cases hkl : k = l
  · subst l
    simp [yExponent]
  · have hlk : l ≠ k := Ne.symm hkl
    have hne : Finsupp.single (FiniteClassTwoBasisIndex.weightTwo l) 1 ≠
        yExponent (L := L) k := by
      intro h
      have hval := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦
        e (FiniteClassTwoBasisIndex.weightTwo l)) h
      simp [yExponent, hlk] at hval
    simp [hkl, hne]

private theorem scalarFirstRow_xxCoefficient
    (R : StandingReductionData L) (i a b : I) :
    adaptedPBWCoefficient L L ev (xxExponent (L := L) a b)
        ((⟨[], .row (adaptedCoordinateXFactor L i), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  classical
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one, adaptedLowRelationRow, adaptedCoordinateXFactor,
    adaptedLowBasisIndexOf]
  change MvPolynomial.coeff (xxExponent (L := L) a b)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 1 i : F))) = 0
  rw [R.firstRow_PBWSymbol, MvPolynomial.coeff_sub,
    coefficient_zsmul_X (L := L), MvPolynomial.coeff_sum]
  simp_rw [coefficient_zsmul_X (L := L)]
  have hone (u : FiniteClassTwoBasisIndex L) :
      Finsupp.single u 1 ≠ xxExponent (L := L) a b := by
    intro h
    by_cases hau : (FiniteClassTwoBasisIndex.weightOne a :
        FiniteClassTwoBasisIndex L) = u
    · by_cases hbu : (FiniteClassTwoBasisIndex.weightOne b :
          FiniteClassTwoBasisIndex L) = u
      · have hu := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e u) h
        simp [xxExponent, xExponent, hau, hbu] at hu
      · have hab : (FiniteClassTwoBasisIndex.weightOne a :
            FiniteClassTwoBasisIndex L) ≠ .weightOne b := by
          intro hab
          exact hbu (hab.symm.trans hau)
        have hb := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦
          e (FiniteClassTwoBasisIndex.weightOne b)) h
        simp [xxExponent, xExponent, hau, hbu, hab] at hb
    · by_cases hbu : (FiniteClassTwoBasisIndex.weightOne b :
          FiniteClassTwoBasisIndex L) = u
      · have hab : (FiniteClassTwoBasisIndex.weightOne b :
            FiniteClassTwoBasisIndex L) ≠ .weightOne a := by
          intro hab
          exact hau (hab.symm.trans hbu)
        have ha := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦
          e (FiniteClassTwoBasisIndex.weightOne a)) h
        simp [xxExponent, xExponent, hau, hbu, hab] at ha
      · have hu := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e u) h
        simp [xxExponent, xExponent, hau, hbu] at hu
  simp [hone]

private theorem scalarSecondRow_xxCoefficient
    (R : StandingReductionData L) (k : K) (a b : I) :
    adaptedPBWCoefficient L L ev (xxExponent (L := L) a b)
        ((⟨[], .row (adaptedCoordinateYFactor L k), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  classical
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one, adaptedLowRelationRow, adaptedCoordinateYFactor,
    adaptedLowBasisIndexOf]
  change MvPolynomial.coeff (xxExponent (L := L) a b)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 2 k : F))) = 0
  rw [R.secondRow_PBWSymbol, coefficient_zsmul_X (L := L)]
  have hne : Finsupp.single (FiniteClassTwoBasisIndex.weightTwo k) 1 ≠
      xxExponent (L := L) a b := by
    intro h
    have hval := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦
      e (FiniteClassTwoBasisIndex.weightTwo k)) h
    simp [xxExponent, xExponent] at hval
  simp [hne]

private theorem leftX_firstRow_PBWSymbol
    (i j : I) (hji : j ≤ i) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[adaptedCoordinateXFactor L j],
            .row (adaptedCoordinateXFactor L i), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j) *
        ((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ k, R.coordinateB i k •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) := by
  classical
  have hfactor : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L j) =
      ((collectedHomogeneousBasis L L ev 1 j : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) j
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateXFactor L i) =
      (collectedRelationRow L L ev 1 i : F) := by
    rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, mul_one, hfactor, hrow]
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
    show adaptedFreeEnvelopingToClassTwoEnveloping L
        (UniversalEnvelopingAlgebra.ι ℤ
          ((collectedHomogeneousBasis L L ev 1 j : freeLieExact L 1) : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (adaptedHomogeneousClassTwoBasis L L ev (.weightOne j)) by
          unfold adaptedFreeEnvelopingToClassTwoEnveloping
          rw [UniversalEnvelopingAlgebra.lift_ι_apply,
            adaptedHomogeneousClassTwoBasis_weightOne]
          rfl,
    LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
  change adaptedHomogeneousClassTwoAction L L ev
      (adaptedHomogeneousClassTwoBasis L L ev (.weightOne j))
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 1 i : F))) = _
  rw [adaptedHomogeneousClassTwoAction_weightOne_apply, R.firstRow_PBWSymbol]
  have hji' : (FiniteClassTwoBasisIndex.weightOne j :
      FiniteClassTwoBasisIndex L) ≤ .weightOne i := by
    change toLex ((0 : ℕ), j.1) ≤ toLex ((0 : ℕ), i.1)
    rw [Prod.Lex.le_iff]
    simpa using hji
  have hnot : ¬(FiniteClassTwoBasisIndex.weightOne i :
      FiniteClassTwoBasisIndex L) < .weightOne j := not_lt_of_ge hji'
  simp only [map_sub, map_sum, map_zsmul,
    adaptedCorrectionDerivation_X_weightOne,
    adaptedCorrectionDerivation_X_weightTwo, hnot, if_false,
    Derivation.map_zero, sub_zero]
  simp

private theorem leftX_firstRow_yCoefficient
    (R : StandingReductionData L) (i j : I) (hji : j ≤ i) (k : K) :
    adaptedPBWCoefficient L L ev (yExponent (L := L) k)
        ((⟨[adaptedCoordinateXFactor L j],
            .row (adaptedCoordinateXFactor L i), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  change MvPolynomial.coeff (yExponent (L := L) k)
    (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
  rw [leftX_firstRow_PBWSymbol (R := R) i j hji]
  have hxadd (e : FiniteClassTwoBasisIndex L →₀ ℕ) :
      Finsupp.single (FiniteClassTwoBasisIndex.weightOne j) 1 + e ≠
        yExponent (L := L) k := by
    intro h
    have hval := congrArg (fun f : FiniteClassTwoBasisIndex L →₀ ℕ ↦
      f (FiniteClassTwoBasisIndex.weightOne j)) h
    simp [yExponent] at hval
  by_contra hc
  have hs := MvPolynomial.mem_support_iff.mpr hc
  have hs' := MvPolynomial.support_mul
    (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j) :
      MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) _ hs
  rw [Finset.mem_add] at hs'
  obtain ⟨f, hf, g, hg, hfg⟩ := hs'
  rw [MvPolynomial.support_X] at hf
  simp only [Finset.mem_singleton] at hf
  subst f
  exact hxadd g hfg

private theorem leftX_firstRow_xxCoefficient
    (R : StandingReductionData L) (i j : I) (hji : j ≤ i) (a b : I) :
    adaptedPBWCoefficient L L ev (xxExponent (L := L) a b)
        ((⟨[adaptedCoordinateXFactor L j],
            .row (adaptedCoordinateXFactor L i), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      if xExponent (L := L) j + xExponent (L := L) i =
          xxExponent (L := L) a b
        then (R.coordinateD i : ℤ) else 0 := by
  classical
  change MvPolynomial.coeff (xxExponent (L := L) a b)
    (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = _
  rw [leftX_firstRow_PBWSymbol (R := R) i j hji]
  rw [mul_sub, MvPolynomial.coeff_sub,
    coefficient_X_mul_zsmul_X (L := L)]
  rw [Finset.mul_sum, MvPolynomial.coeff_sum]
  simp_rw [coefficient_X_mul_zsmul_X (L := L)]
  have hne (l : K) : xExponent (L := L) j + yExponent (L := L) l ≠
      xxExponent (L := L) a b := by
    intro h
    have hval := congrArg (fun f : FiniteClassTwoBasisIndex L →₀ ℕ ↦
      f (FiniteClassTwoBasisIndex.weightTwo l)) h
    simp [xExponent, yExponent, xxExponent] at hval
  have hzero (l : K) :
      (if Finsupp.single (FiniteClassTwoBasisIndex.weightOne j) 1 +
            Finsupp.single (FiniteClassTwoBasisIndex.weightTwo l) 1 =
          xxExponent (L := L) a b
        then R.coordinateB i l else 0) = 0 := by
    rw [if_neg]
    exact hne l
  simp_rw [hzero]
  simp [xExponent]

private theorem firstRowPolynomial_xxCoefficient
    (R : StandingReductionData L) (i j a b : I) :
    MvPolynomial.coeff (xxExponent (L := L) a b)
      ((MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j) :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        ((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ l, R.coordinateB i l •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l))) =
      if xExponent (L := L) j + xExponent (L := L) i =
          xxExponent (L := L) a b
        then (R.coordinateD i : ℤ) else 0 := by
  classical
  rw [mul_sub, MvPolynomial.coeff_sub,
    coefficient_X_mul_zsmul_X (L := L)]
  rw [Finset.mul_sum, MvPolynomial.coeff_sum]
  simp_rw [coefficient_X_mul_zsmul_X (L := L)]
  have hne (l : K) : xExponent (L := L) j + yExponent (L := L) l ≠
      xxExponent (L := L) a b := by
    intro h
    have hval := congrArg (fun f : FiniteClassTwoBasisIndex L →₀ ℕ ↦
      f (FiniteClassTwoBasisIndex.weightTwo l)) h
    simp [xExponent, yExponent, xxExponent] at hval
  have hzero (l : K) :
      (if Finsupp.single (FiniteClassTwoBasisIndex.weightOne j) 1 +
            Finsupp.single (FiniteClassTwoBasisIndex.weightTwo l) 1 =
          xxExponent (L := L) a b
        then R.coordinateB i l else 0) = 0 := by
    rw [if_neg]
    exact hne l
  simp_rw [hzero]
  simp [xExponent]

private theorem rightX_firstRow_PBWSymbol
    (i j : I) (hij : i ≤ j) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[], .row (adaptedCoordinateXFactor L i),
            [adaptedCoordinateXFactor L j]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      ((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ k, R.coordinateB i k •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j) := by
  classical
  have hfactor : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L j) =
      ((collectedHomogeneousBasis L L ev 1 j : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) j
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateXFactor L i) =
      (collectedRelationRow L L ev 1 i : F) := by rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hfactor, hrow]
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul]
  have hmap : adaptedFreeEnvelopingToClassTwoEnveloping L
      (UniversalEnvelopingAlgebra.ι ℤ
        (collectedRelationRow L L ev 1 i : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (freeClassTwoTruncation L
          (collectedRelationRow L L ev 1 i : F)) := by
    unfold adaptedFreeEnvelopingToClassTwoEnveloping
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  rw [hmap, LieRings.PBW.TriangularRepresentation.envelopingAction_ι,
    adaptedFreeEnvelopingToClassTwoPBWSymbol_iota]
  change adaptedHomogeneousClassTwoAction L L ev
      (freeClassTwoTruncation L (collectedRelationRow L L ev 1 i : F))
      (adaptedHomogeneousClassTwoPolynomial L L ev
        (freeClassTwoTruncation L
          ((collectedHomogeneousBasis L L ev 1 j : freeLieExact L 1) : F))) = _
  rw [← adaptedHomogeneousClassTwoBasis_weightOne L L ev j,
    adaptedHomogeneousClassTwoPolynomial_basis,
    R.freeClassTwoTruncation_firstRow,
    R.finiteLowExactToClassTwo_firstRow_coordinates]
  change adaptedHomogeneousClassTwoAction L L ev
      ((R.coordinateD i : ℤ) •
          adaptedHomogeneousClassTwoBasis L L ev (.weightOne i) -
        ∑ k, R.coordinateB i k •
          adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k))
      (MvPolynomial.X (.weightOne j)) = _
  rw [map_sub, map_sum, map_zsmul]
  simp_rw [map_zsmul]
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  change (R.coordinateD i : ℤ) •
      adaptedHomogeneousClassTwoAction L L ev
        (adaptedHomogeneousClassTwoBasis L L ev (.weightOne i))
        (MvPolynomial.X (.weightOne j)) -
    ∑ k, R.coordinateB i k •
      adaptedHomogeneousClassTwoAction L L ev
        (adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k))
        (MvPolynomial.X (.weightOne j)) = _
  rw [adaptedHomogeneousClassTwoAction_weightOne_apply]
  simp_rw [adaptedHomogeneousClassTwoAction_weightTwo_apply]
  have hij' : (FiniteClassTwoBasisIndex.weightOne i :
      FiniteClassTwoBasisIndex L) ≤ .weightOne j := by
    change toLex ((0 : ℕ), i.1) ≤ toLex ((0 : ℕ), j.1)
    rw [Prod.Lex.le_iff]
    simpa using hij
  rw [adaptedCorrectionDerivation_X_weightOne]
  simp only [if_neg (not_lt_of_ge hij'), add_zero, smul_eq_mul]
  rw [sub_mul, Finset.sum_mul]
  ring_nf

private theorem rightX_firstRow_yCoefficient
    (R : StandingReductionData L) (i j : I) (hij : i ≤ j) (k : K) :
    adaptedPBWCoefficient L L ev (yExponent (L := L) k)
        ((⟨[], .row (adaptedCoordinateXFactor L i),
            [adaptedCoordinateXFactor L j]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  change MvPolynomial.coeff (yExponent (L := L) k)
    (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
  rw [rightX_firstRow_PBWSymbol (R := R) i j hij]
  rw [mul_comm]
  have hxadd (e : FiniteClassTwoBasisIndex L →₀ ℕ) :
      Finsupp.single (FiniteClassTwoBasisIndex.weightOne j) 1 + e ≠
        yExponent (L := L) k := by
    intro h
    have hval := congrArg (fun f : FiniteClassTwoBasisIndex L →₀ ℕ ↦
      f (FiniteClassTwoBasisIndex.weightOne j)) h
    simp [yExponent] at hval
  by_contra hc
  have hs := MvPolynomial.mem_support_iff.mpr hc
  have hs' := MvPolynomial.support_mul
    (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j) :
      MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) _ hs
  rw [Finset.mem_add] at hs'
  obtain ⟨f, hf, g, hg, hfg⟩ := hs'
  rw [MvPolynomial.support_X] at hf
  simp only [Finset.mem_singleton] at hf
  subst f
  exact hxadd g hfg

private theorem rightX_firstRow_xxCoefficient
    (R : StandingReductionData L) (i j : I) (hij : i ≤ j) (a b : I) :
    adaptedPBWCoefficient L L ev (xxExponent (L := L) a b)
        ((⟨[], .row (adaptedCoordinateXFactor L i),
            [adaptedCoordinateXFactor L j]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      if xExponent (L := L) j + xExponent (L := L) i =
          xxExponent (L := L) a b
        then (R.coordinateD i : ℤ) else 0 := by
  change MvPolynomial.coeff (xxExponent (L := L) a b)
    (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = _
  rw [rightX_firstRow_PBWSymbol (R := R) i j hij, mul_comm]
  exact firstRowPolynomial_xxCoefficient R i j a b

private theorem rightY_firstRow_PBWSymbol
    (i : I) (l : K) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[], .row (adaptedCoordinateXFactor L i),
            [adaptedCoordinateYFactor L l]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      ((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ k, R.coordinateB i k •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l) := by
  classical
  have hfactor : adaptedLowBasisValue L L ev (adaptedCoordinateYFactor L l) =
      ((collectedHomogeneousBasis L L ev 2 l : freeLieExact L 2) : F) := by
    simpa [adaptedCoordinateYFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 2) (by omega) (by omega) l
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateXFactor L i) =
      (collectedRelationRow L L ev 1 i : F) := by rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hfactor, hrow]
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul]
  rw [show adaptedFreeEnvelopingToClassTwoEnveloping L
      (UniversalEnvelopingAlgebra.ι ℤ
        (collectedRelationRow L L ev 1 i : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (freeClassTwoTruncation L
          (collectedRelationRow L L ev 1 i : F)) by
    exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ _ _]
  rw [LieRings.PBW.TriangularRepresentation.envelopingAction_ι,
    adaptedFreeEnvelopingToClassTwoPBWSymbol_iota,
    ← adaptedHomogeneousClassTwoBasis_weightTwo L L ev l,
    adaptedHomogeneousClassTwoPolynomial_basis,
    R.freeClassTwoTruncation_firstRow,
    R.finiteLowExactToClassTwo_firstRow_coordinates]
  change adaptedHomogeneousClassTwoAction L L ev
      ((R.coordinateD i : ℤ) •
          adaptedHomogeneousClassTwoBasis L L ev (.weightOne i) -
        ∑ k, R.coordinateB i k •
          adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k))
      (MvPolynomial.X (.weightTwo l)) = _
  rw [map_sub, map_sum, map_zsmul]
  simp_rw [map_zsmul]
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  change (R.coordinateD i : ℤ) •
        adaptedHomogeneousClassTwoAction L L ev
          (adaptedHomogeneousClassTwoBasis L L ev (.weightOne i))
          (MvPolynomial.X (.weightTwo l)) -
      ∑ k, R.coordinateB i k •
        adaptedHomogeneousClassTwoAction L L ev
          (adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k))
          (MvPolynomial.X (.weightTwo l)) = _
  rw [adaptedHomogeneousClassTwoAction_weightOne_apply]
  simp_rw [adaptedHomogeneousClassTwoAction_weightTwo_apply]
  rw [adaptedCorrectionDerivation_X_weightTwo]
  simp
  conv_rhs => rw [sub_mul, Finset.sum_mul]
  ring

private theorem leftX_secondRow_PBWSymbol
    (i : I) (k : K) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[adaptedCoordinateXFactor L i],
            .row (adaptedCoordinateYFactor L k), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) *
        ((R.coordinateE k : ℤ) •
          MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) := by
  classical
  have hfactor : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L i) =
      ((collectedHomogeneousBasis L L ev 1 i : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) i
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateYFactor L k) =
      (collectedRelationRow L L ev 2 k : F) := by rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hfactor, hrow]
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
    show adaptedFreeEnvelopingToClassTwoEnveloping L
        (UniversalEnvelopingAlgebra.ι ℤ
          ((collectedHomogeneousBasis L L ev 1 i : freeLieExact L 1) : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (adaptedHomogeneousClassTwoBasis L L ev (.weightOne i)) by
          unfold adaptedFreeEnvelopingToClassTwoEnveloping
          rw [UniversalEnvelopingAlgebra.lift_ι_apply,
            adaptedHomogeneousClassTwoBasis_weightOne]
          rfl,
    LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
  change adaptedHomogeneousClassTwoAction L L ev
      (adaptedHomogeneousClassTwoBasis L L ev (.weightOne i))
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 2 k : F))) = _
  rw [adaptedHomogeneousClassTwoAction_weightOne_apply, R.secondRow_PBWSymbol]
  rw [map_zsmul, adaptedCorrectionDerivation_X_weightTwo]
  simp

private theorem rightY_secondRow_PBWSymbol
    (k l : K) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[], .row (adaptedCoordinateYFactor L k),
            [adaptedCoordinateYFactor L l]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      ((R.coordinateE k : ℤ) •
          MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l) := by
  classical
  have hfactor : adaptedLowBasisValue L L ev (adaptedCoordinateYFactor L l) =
      ((collectedHomogeneousBasis L L ev 2 l : freeLieExact L 2) : F) := by
    simpa [adaptedCoordinateYFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 2) (by omega) (by omega) l
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateYFactor L k) =
      (collectedRelationRow L L ev 2 k : F) := by rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hfactor, hrow]
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul]
  rw [show adaptedFreeEnvelopingToClassTwoEnveloping L
      (UniversalEnvelopingAlgebra.ι ℤ
        (collectedRelationRow L L ev 2 k : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (freeClassTwoTruncation L
          (collectedRelationRow L L ev 2 k : F)) by
    exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ _ _]
  rw [LieRings.PBW.TriangularRepresentation.envelopingAction_ι,
    adaptedFreeEnvelopingToClassTwoPBWSymbol_iota,
    ← adaptedHomogeneousClassTwoBasis_weightTwo L L ev l,
    adaptedHomogeneousClassTwoPolynomial_basis,
    R.freeClassTwoTruncation_secondRow,
    R.finiteLowExactToClassTwo_secondRow_coordinates]
  rw [map_zsmul]
  change (R.coordinateE k : ℤ) •
      adaptedHomogeneousClassTwoAction L L ev
        (adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k))
        (MvPolynomial.X (.weightTwo l)) = _
  rw [adaptedHomogeneousClassTwoAction_weightTwo_apply]
  simp [smul_eq_mul]
  ring

private theorem leftY_secondRow_PBWSymbol
    (k l : K) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[adaptedCoordinateYFactor L k],
            .row (adaptedCoordinateYFactor L l), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k) *
        ((R.coordinateE l : ℤ) •
          MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l)) := by
  classical
  have hfactor : adaptedLowBasisValue L L ev (adaptedCoordinateYFactor L k) =
      ((collectedHomogeneousBasis L L ev 2 k : freeLieExact L 2) : F) := by
    simpa [adaptedCoordinateYFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 2) (by omega) (by omega) k
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateYFactor L l) =
      (collectedRelationRow L L ev 2 l : F) := by rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hfactor, hrow]
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
    show adaptedFreeEnvelopingToClassTwoEnveloping L
        (UniversalEnvelopingAlgebra.ι ℤ
          ((collectedHomogeneousBasis L L ev 2 k : freeLieExact L 2) : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k)) by
          unfold adaptedFreeEnvelopingToClassTwoEnveloping
          rw [UniversalEnvelopingAlgebra.lift_ι_apply,
            adaptedHomogeneousClassTwoBasis_weightTwo]
          rfl,
    LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
  change adaptedHomogeneousClassTwoAction L L ev
      (adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k))
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 2 l : F))) = _
  rw [adaptedHomogeneousClassTwoAction_weightTwo_apply, R.secondRow_PBWSymbol]

private theorem xyExponent_eq_iff (i a : I) (k b : K) :
    xExponent (L := L) i + yExponent (L := L) k =
        xyExponent (L := L) a b ↔ i = a ∧ k = b := by
  simp only [xyExponent, xExponent, yExponent]
  rw [Finsupp.single_add_single_eq_single_add_single
    (one_ne_zero : (1 : ℕ) ≠ 0) (one_ne_zero : (1 : ℕ) ≠ 0)]
  simp

private theorem xxExponent_ne_xyExponent (i j a : I) (k : K) :
    xExponent (L := L) i + xExponent (L := L) j ≠
      xyExponent (L := L) a k := by
  intro h
  have hy := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦
    e (.weightTwo k)) h
  simp [xExponent, yExponent, xyExponent] at hy

private theorem yyExponent_ne_xyExponent (k l : K) (a : I) (b : K) :
    yExponent (L := L) k + yExponent (L := L) l ≠
      xyExponent (L := L) a b := by
  intro h
  have hx := congrArg (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦
    e (.weightOne a)) h
  simp [xExponent, yExponent, xyExponent] at hx

private theorem coefficient_three_variables_yy_zero
    (u v w : FiniteClassTwoBasisIndex L) (k l : K) :
    MvPolynomial.coeff (yyExponent (L := L) k l)
      ((MvPolynomial.X u : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        MvPolynomial.X v * MvPolynomial.X w) = 0 := by
  classical
  rw [show (MvPolynomial.X u : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        MvPolynomial.X v * MvPolynomial.X w =
      MvPolynomial.monomial
        (Finsupp.single u 1 + Finsupp.single v 1 + Finsupp.single w 1) 1 by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro h
  have hsum := congrArg
    (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e.sum fun _ n ↦ n) h
  simp [yyExponent, yExponent, Finsupp.sum_add_index] at hsum

private theorem firstRowWithY_yyCoefficient
    (i : I) (b k l : K) :
    MvPolynomial.coeff (yyExponent (L := L) k l)
      (((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ h, R.coordinateB i h •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo h)) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo b)) =
      -∑ h, if yExponent (L := L) h + yExponent (L := L) b =
          yyExponent (L := L) k l then R.coordinateB i h else 0 := by
  classical
  rw [sub_mul, MvPolynomial.coeff_sub, Finset.sum_mul,
    MvPolynomial.coeff_sum]
  have hx : MvPolynomial.coeff (yyExponent (L := L) k l)
      (((R.coordinateD i : ℤ) •
          (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) :
            MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo b)) = 0 := by
    rw [show ((R.coordinateD i : ℤ) •
          (MvPolynomial.X (.weightOne i) :
            MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) *
          MvPolynomial.X (.weightTwo b) =
        MvPolynomial.X (.weightTwo b) *
          ((R.coordinateD i : ℤ) • MvPolynomial.X (.weightOne i)) by ring,
      coefficient_X_mul_zsmul_X (L := L)]
    rw [if_neg]
    intro heq
    have hv := congrArg
      (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e (.weightOne i)) heq
    simp [yyExponent, yExponent] at hv
  rw [hx, zero_sub]
  simp_rw [show ∀ h,
      MvPolynomial.coeff (yyExponent (L := L) k l)
          ((R.coordinateB i h •
              (MvPolynomial.X (.weightTwo h) :
                MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) *
            MvPolynomial.X (.weightTwo b)) =
        if yExponent (L := L) h + yExponent (L := L) b =
            yyExponent (L := L) k l then R.coordinateB i h else 0 by
      intro h
      rw [show (R.coordinateB i h •
            (MvPolynomial.X (.weightTwo h) :
              MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) *
            MvPolynomial.X (.weightTwo b) =
          MvPolynomial.X (.weightTwo b) *
            (R.coordinateB i h • MvPolynomial.X (.weightTwo h)) by ring,
        coefficient_X_mul_zsmul_X (L := L)]
      change (if yExponent (L := L) b + yExponent (L := L) h = _
        then _ else _) = _
      simp [add_comm]]

private theorem secondRowWithY_yyCoefficient
    (h b k l : K) :
    MvPolynomial.coeff (yyExponent (L := L) k l)
      (((R.coordinateE h : ℤ) •
          MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo h)) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo b)) =
      if yExponent (L := L) h + yExponent (L := L) b =
          yyExponent (L := L) k l then (R.coordinateE h : ℤ) else 0 := by
  rw [show ((R.coordinateE h : ℤ) •
        (MvPolynomial.X (.weightTwo h) :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) *
        MvPolynomial.X (.weightTwo b) =
      MvPolynomial.X (.weightTwo b) *
        ((R.coordinateE h : ℤ) • MvPolynomial.X (.weightTwo h)) by ring,
    coefficient_X_mul_zsmul_X (L := L)]
  change (if yExponent (L := L) b + yExponent (L := L) h = _
    then _ else _) = _
  simp [add_comm]

private theorem rightY_firstRow_yyCoefficient
    (i : I) (b k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨[], .row (adaptedCoordinateXFactor L i),
            [adaptedCoordinateYFactor L b]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      -∑ h, if yExponent (L := L) h + yExponent (L := L) b =
          yyExponent (L := L) k l then R.coordinateB i h else 0 := by
  change MvPolynomial.coeff (yyExponent (L := L) k l)
    (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = _
  rw [rightY_firstRow_PBWSymbol R i b]
  exact firstRowWithY_yyCoefficient R i b k l

private theorem rightY_secondRow_yyCoefficient
    (h b k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨[], .row (adaptedCoordinateYFactor L h),
            [adaptedCoordinateYFactor L b]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      if yExponent (L := L) h + yExponent (L := L) b =
          yyExponent (L := L) k l then (R.coordinateE h : ℤ) else 0 := by
  change MvPolynomial.coeff (yyExponent (L := L) k l)
    (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = _
  rw [rightY_secondRow_PBWSymbol R h b]
  simpa [add_comm] using secondRowWithY_yyCoefficient R h b k l

private theorem leftY_secondRow_yyCoefficient
    (b h k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨[adaptedCoordinateYFactor L b],
            .row (adaptedCoordinateYFactor L h), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      if yExponent (L := L) b + yExponent (L := L) h =
          yyExponent (L := L) k l then (R.coordinateE h : ℤ) else 0 := by
  change MvPolynomial.coeff (yyExponent (L := L) k l)
    (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = _
  rw [leftY_secondRow_PBWSymbol R b h]
  rw [show MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo b) *
      ((R.coordinateE h : ℤ) •
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo h) :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) =
      ((R.coordinateE h : ℤ) •
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo h)) *
          MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo b) by ring]
  rw [add_comm (yExponent (L := L) b) (yExponent (L := L) h)]
  exact secondRowWithY_yyCoefficient R h b k l

private theorem firstRowTriple_yyCoefficient_zero
    (u v : FiniteClassTwoBasisIndex L) (i : I) (k l : K) :
    MvPolynomial.coeff (yyExponent (L := L) k l)
      ((MvPolynomial.X u : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        MvPolynomial.X v *
        ((R.coordinateD i : ℤ) • MvPolynomial.X (.weightOne i) -
          ∑ h, R.coordinateB i h • MvPolynomial.X (.weightTwo h))) = 0 := by
  classical
  rw [mul_sub, Finset.mul_sum]
  simp_rw [mul_smul_comm]
  change (MvPolynomial.lcoeff ℤ (yyExponent (L := L) k l))
      ((R.coordinateD i : ℤ) •
          (MvPolynomial.X u * MvPolynomial.X v * MvPolynomial.X (.weightOne i)) -
        ∑ h, R.coordinateB i h •
          (MvPolynomial.X u * MvPolynomial.X v * MvPolynomial.X (.weightTwo h))) = 0
  rw [map_sub, map_zsmul, map_sum]
  simp_rw [map_zsmul]
  simp [coefficient_three_variables_yy_zero]

private theorem firstRowWithX_xyCoefficient
    (i j a : I) (k : K) :
    MvPolynomial.coeff (xyExponent (L := L) a k)
      ((MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j) :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        ((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ l, R.coordinateB i l •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l))) =
      if j = a then -R.coordinateB i k else 0 := by
  classical
  rw [mul_sub, MvPolynomial.coeff_sub,
    coefficient_X_mul_zsmul_X (L := L), Finset.mul_sum,
    MvPolynomial.coeff_sum]
  simp_rw [coefficient_X_mul_zsmul_X (L := L)]
  have hxx :
      Finsupp.single (FiniteClassTwoBasisIndex.weightOne j) 1 +
          Finsupp.single (FiniteClassTwoBasisIndex.weightOne i) 1 ≠
        xyExponent (L := L) a k := by
    simpa [xExponent] using xxExponent_ne_xyExponent (L := L) j i a k
  have hxy (l : K) :
      Finsupp.single (FiniteClassTwoBasisIndex.weightOne j) 1 +
          Finsupp.single (FiniteClassTwoBasisIndex.weightTwo l) 1 =
        xyExponent (L := L) a k ↔ j = a ∧ l = k := by
    simpa [xExponent, yExponent] using
      xyExponent_eq_iff (L := L) j a l k
  rw [if_neg hxx]
  simp_rw [hxy]
  simp only [zero_sub]
  by_cases hja : j = a
  · subst j
    simp
  · simp [hja]

private theorem firstRowWithY_xyCoefficient
    (i a : I) (l k : K) :
    MvPolynomial.coeff (xyExponent (L := L) a k)
      (((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ b, R.coordinateB i b •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo b)) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l)) =
      if i = a ∧ l = k then (R.coordinateD i : ℤ) else 0 := by
  classical
  rw [sub_mul, MvPolynomial.coeff_sub,
    show ((R.coordinateD i : ℤ) •
        (MvPolynomial.X (.weightOne i) :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) *
          MvPolynomial.X (.weightTwo l) =
        MvPolynomial.X (.weightTwo l) *
          ((R.coordinateD i : ℤ) • MvPolynomial.X (.weightOne i)) by
            ring,
    coefficient_X_mul_zsmul_X (L := L), Finset.sum_mul,
    MvPolynomial.coeff_sum]
  have hzero (b : K) :
      MvPolynomial.coeff (xyExponent (L := L) a k)
        ((R.coordinateB i b •
            (MvPolynomial.X (.weightTwo b) :
              MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) *
          MvPolynomial.X (.weightTwo l)) = 0 := by
    rw [show (R.coordinateB i b •
          (MvPolynomial.X (.weightTwo b) :
            MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) *
          MvPolynomial.X (.weightTwo l) =
        MvPolynomial.X (.weightTwo l) *
          (R.coordinateB i b • MvPolynomial.X (.weightTwo b)) by ring,
      coefficient_X_mul_zsmul_X (L := L),
      if_neg (by simpa [yExponent] using
        yyExponent_ne_xyExponent (L := L) l b a k)]
  simp_rw [hzero]
  simp only [Finset.sum_const_zero, sub_zero]
  have hmain :
      Finsupp.single (FiniteClassTwoBasisIndex.weightTwo l) 1 +
          Finsupp.single (FiniteClassTwoBasisIndex.weightOne i) 1 =
        xyExponent (L := L) a k ↔ i = a ∧ l = k := by
    change yExponent (L := L) l + xExponent (L := L) i =
        xyExponent (L := L) a k ↔ _
    rw [add_comm]
    exact xyExponent_eq_iff (L := L) i a l k
  by_cases h : i = a ∧ l = k
  · rw [if_pos ((hmain).mpr h), if_pos h]
  · rw [if_neg (fun heq ↦ h (hmain.mp heq)), if_neg h]

private theorem secondRowWithX_xyCoefficient
    (i a : I) (l k : K) :
    MvPolynomial.coeff (xyExponent (L := L) a k)
      ((MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        ((R.coordinateE l : ℤ) •
          MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo l))) =
      if i = a ∧ l = k then (R.coordinateE l : ℤ) else 0 := by
  rw [coefficient_X_mul_zsmul_X (L := L)]
  change (if xExponent (L := L) i + yExponent (L := L) l =
      xyExponent (L := L) a k then (R.coordinateE l : ℤ) else 0) = _
  by_cases h : i = a ∧ l = k
  · rw [if_pos ((xyExponent_eq_iff (L := L) i a l k).mpr h), if_pos h]
  · rw [if_neg (fun heq ↦ h ((xyExponent_eq_iff (L := L) i a l k).mp heq)),
      if_neg h]

private theorem leftLeftXX_firstRow_PBWSymbol
    (i a b : I) (hab : a ≤ b) (hbi : b ≤ i) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b],
            .row (adaptedCoordinateXFactor L i), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne a) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne b) *
        ((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ k, R.coordinateB i k •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) := by
  classical
  have ha : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L a) =
      ((collectedHomogeneousBasis L L ev 1 a : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) a
  have hb : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L b) =
      ((collectedHomogeneousBasis L L ev 1 b : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) b
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateXFactor L i) =
      (collectedRelationRow L L ev 1 i : F) := by rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_cons, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, ha, hb, hrow]
  rw [mul_assoc, adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
    show adaptedFreeEnvelopingToClassTwoEnveloping L
        (UniversalEnvelopingAlgebra.ι ℤ
          ((collectedHomogeneousBasis L L ev 1 a : freeLieExact L 1) : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (adaptedHomogeneousClassTwoBasis L L ev (.weightOne a)) by
          unfold adaptedFreeEnvelopingToClassTwoEnveloping
          rw [UniversalEnvelopingAlgebra.lift_ι_apply,
            adaptedHomogeneousClassTwoBasis_weightOne]
          rfl,
    LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
  change adaptedHomogeneousClassTwoAction L L ev
      (adaptedHomogeneousClassTwoBasis L L ev (.weightOne a))
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
            ((collectedHomogeneousBasis L L ev 1 b : freeLieExact L 1) : F) *
          UniversalEnvelopingAlgebra.ι ℤ
            (collectedRelationRow L L ev 1 i : F))) = _
  have hinner :
      adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
            ((collectedHomogeneousBasis L L ev 1 b : freeLieExact L 1) : F) *
          UniversalEnvelopingAlgebra.ι ℤ
            (collectedRelationRow L L ev 1 i : F)) =
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne b) *
          ((R.coordinateD i : ℤ) • MvPolynomial.X (.weightOne i) -
            ∑ k, R.coordinateB i k • MvPolynomial.X (.weightTwo k)) := by
    simpa only [AdaptedSmithPlacedPacket.value,
      AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
      AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
      envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hb, hrow] using
      leftX_firstRow_PBWSymbol (R := R) i b hbi
  rw [hinner, adaptedHomogeneousClassTwoAction_weightOne_apply]
  have hab' : (FiniteClassTwoBasisIndex.weightOne a :
      FiniteClassTwoBasisIndex L) ≤ .weightOne b := by
    change toLex ((0 : ℕ), a.1) ≤ toLex ((0 : ℕ), b.1)
    rw [Prod.Lex.le_iff]
    simpa using hab
  have hai' : (FiniteClassTwoBasisIndex.weightOne a :
      FiniteClassTwoBasisIndex L) ≤ .weightOne i :=
    hab'.trans (by
      change toLex ((0 : ℕ), b.1) ≤ toLex ((0 : ℕ), i.1)
      rw [Prod.Lex.le_iff]
      simpa using hbi)
  rw [Derivation.leibniz, map_sub, map_zsmul, map_sum]
  simp_rw [map_zsmul, adaptedCorrectionDerivation_X_weightTwo]
  simp only [adaptedCorrectionDerivation_X_weightOne]
  simp [not_lt_of_ge hab', not_lt_of_ge hai']
  ring

private theorem splitXX_firstRow_PBWSymbol
    (i a b : I) (hai : a ≤ i) (hib : i ≤ b) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[adaptedCoordinateXFactor L a],
            .row (adaptedCoordinateXFactor L i),
            [adaptedCoordinateXFactor L b]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne a) *
        (((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ k, R.coordinateB i k •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) *
          MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne b)) := by
  classical
  have ha : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L a) =
      ((collectedHomogeneousBasis L L ev 1 a : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) a
  have hb : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L b) =
      ((collectedHomogeneousBasis L L ev 1 b : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) b
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateXFactor L i) =
      (collectedRelationRow L L ev 1 i : F) := by rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, ha, hb, hrow]
  rw [mul_assoc, adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
    show adaptedFreeEnvelopingToClassTwoEnveloping L
        (UniversalEnvelopingAlgebra.ι ℤ
          ((collectedHomogeneousBasis L L ev 1 a : freeLieExact L 1) : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (adaptedHomogeneousClassTwoBasis L L ev (.weightOne a)) by
          unfold adaptedFreeEnvelopingToClassTwoEnveloping
          rw [UniversalEnvelopingAlgebra.lift_ι_apply,
            adaptedHomogeneousClassTwoBasis_weightOne]
          rfl,
    LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
  change adaptedHomogeneousClassTwoAction L L ev
      (adaptedHomogeneousClassTwoBasis L L ev (.weightOne a))
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
            (collectedRelationRow L L ev 1 i : F) *
          UniversalEnvelopingAlgebra.ι ℤ
            ((collectedHomogeneousBasis L L ev 1 b : freeLieExact L 1) : F))) = _
  have hinner := rightX_firstRow_PBWSymbol (R := R) i b hib
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hb, hrow] at hinner
  rw [hinner, adaptedHomogeneousClassTwoAction_weightOne_apply]
  have hai' : (FiniteClassTwoBasisIndex.weightOne a :
      FiniteClassTwoBasisIndex L) ≤ .weightOne i := by
    change toLex ((0 : ℕ), a.1) ≤ toLex ((0 : ℕ), i.1)
    rw [Prod.Lex.le_iff]
    simpa using hai
  have hab' : (FiniteClassTwoBasisIndex.weightOne a :
      FiniteClassTwoBasisIndex L) ≤ .weightOne b := hai'.trans (by
    change toLex ((0 : ℕ), i.1) ≤ toLex ((0 : ℕ), b.1)
    rw [Prod.Lex.le_iff]
    simpa using hib)
  rw [Derivation.leibniz, map_sub, map_zsmul, map_sum]
  simp_rw [map_zsmul, adaptedCorrectionDerivation_X_weightTwo]
  simp only [adaptedCorrectionDerivation_X_weightOne]
  simp [not_lt_of_ge hai', not_lt_of_ge hab']

set_option maxHeartbeats 1000000 in
private theorem rightRightXX_firstRow_PBWSymbol
    (i a b : I) (hia : i ≤ a) (hab : a ≤ b) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[], .row (adaptedCoordinateXFactor L i),
            [adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      ((R.coordinateD i : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) -
          ∑ k, R.coordinateB i k •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo k)) *
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne a) *
          MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne b)) := by
  classical
  have ha : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L a) =
      ((collectedHomogeneousBasis L L ev 1 a : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) a
  have hb : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L b) =
      ((collectedHomogeneousBasis L L ev 1 b : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) b
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateXFactor L i) =
      (collectedRelationRow L L ev 1 i : F) := by rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_cons, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, ha, hb, hrow]
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul]
  have hmaprow : adaptedFreeEnvelopingToClassTwoEnveloping L
      (UniversalEnvelopingAlgebra.ι ℤ
        (collectedRelationRow L L ev 1 i : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (freeClassTwoTruncation L
          (collectedRelationRow L L ev 1 i : F)) := by
    exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ _ _
  rw [hmaprow, LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
  have hword : adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
      (UniversalEnvelopingAlgebra.ι ℤ
          ((collectedHomogeneousBasis L L ev 1 a : freeLieExact L 1) : F) *
        UniversalEnvelopingAlgebra.ι ℤ
          ((collectedHomogeneousBasis L L ev 1 b : freeLieExact L 1) : F)) =
      MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne a) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne b) := by
    rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
      show adaptedFreeEnvelopingToClassTwoEnveloping L
          (UniversalEnvelopingAlgebra.ι ℤ
            ((collectedHomogeneousBasis L L ev 1 a : freeLieExact L 1) : F)) =
        UniversalEnvelopingAlgebra.ι ℤ
          (adaptedHomogeneousClassTwoBasis L L ev (.weightOne a)) by
            unfold adaptedFreeEnvelopingToClassTwoEnveloping
            rw [UniversalEnvelopingAlgebra.lift_ι_apply,
              adaptedHomogeneousClassTwoBasis_weightOne]
            rfl,
      LieRings.PBW.TriangularRepresentation.envelopingAction_ι,
      adaptedFreeEnvelopingToClassTwoPBWSymbol_iota,
      ← adaptedHomogeneousClassTwoBasis_weightOne L L ev b,
      adaptedHomogeneousClassTwoPolynomial_basis]
    change adaptedHomogeneousClassTwoAction L L ev
        (adaptedHomogeneousClassTwoBasis L L ev (.weightOne a))
        (MvPolynomial.X (.weightOne b)) = _
    rw [adaptedHomogeneousClassTwoAction_weightOne_apply]
    have hab' : (FiniteClassTwoBasisIndex.weightOne a :
        FiniteClassTwoBasisIndex L) ≤ .weightOne b := by
      change toLex ((0 : ℕ), a.1) ≤ toLex ((0 : ℕ), b.1)
      rw [Prod.Lex.le_iff]
      simpa using hab
    rw [adaptedCorrectionDerivation_X_weightOne,
      if_neg (not_lt_of_ge hab')]
    simp
  rw [hword, R.freeClassTwoTruncation_firstRow,
    R.finiteLowExactToClassTwo_firstRow_coordinates]
  rw [adaptedTriangular_toLieHom_apply]
  rw [map_sub, map_sum, map_zsmul]
  simp_rw [map_zsmul]
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [moduleEnd_zsmul_apply]
  rw [adaptedHomogeneousClassTwoAction_weightOne_apply]
  simp_rw [adaptedHomogeneousClassTwoAction_weightTwo_apply]
  have hia' : (FiniteClassTwoBasisIndex.weightOne i :
      FiniteClassTwoBasisIndex L) ≤ .weightOne a := by
    change toLex ((0 : ℕ), i.1) ≤ toLex ((0 : ℕ), a.1)
    rw [Prod.Lex.le_iff]
    simpa using hia
  have hib' : (FiniteClassTwoBasisIndex.weightOne i :
      FiniteClassTwoBasisIndex L) ≤ .weightOne b := hia'.trans (by
    change toLex ((0 : ℕ), a.1) ≤ toLex ((0 : ℕ), b.1)
    rw [Prod.Lex.le_iff]
    simpa using hab)
  rw [Derivation.leibniz]
  simp only [adaptedCorrectionDerivation_X_weightOne]
  simp [not_lt_of_ge hia', not_lt_of_ge hib']
  rw [sub_mul, Finset.sum_mul Finset.univ]
  ring

private theorem coefficient_three_X_xy_zero
    (u v w : FiniteClassTwoBasisIndex L) (a : I) (k : K) :
    MvPolynomial.coeff (xyExponent (L := L) a k)
      ((MvPolynomial.X u : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        MvPolynomial.X v * MvPolynomial.X w) = 0 := by
  classical
  rw [show (MvPolynomial.X u : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        MvPolynomial.X v * MvPolynomial.X w =
      MvPolynomial.monomial
        (Finsupp.single u 1 + Finsupp.single v 1 + Finsupp.single w 1) 1 by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro h
  have hsum := congrArg
    (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e.sum fun _ n ↦ n) h
  simp [xyExponent, xExponent, yExponent, Finsupp.sum_add_index] at hsum

private theorem coefficient_C_mul_three_X_xy_zero
    (n : ℤ) (u v w : FiniteClassTwoBasisIndex L) (a : I) (k : K) :
    MvPolynomial.coeff (xyExponent (L := L) a k)
      ((n : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        (MvPolynomial.X u * MvPolynomial.X v * MvPolynomial.X w)) = 0 := by
  rw [show (n : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) =
      MvPolynomial.C n by simp]
  rw [MvPolynomial.coeff_C_mul, coefficient_three_X_xy_zero (L := L)]
  simp

private theorem firstRowTriple_xyCoefficient_zero
    (u v : FiniteClassTwoBasisIndex L) (i a : I) (k : K) :
    MvPolynomial.coeff (xyExponent (L := L) a k)
      ((MvPolynomial.X u : MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        MvPolynomial.X v *
        ((R.coordinateD i : ℤ) • MvPolynomial.X (.weightOne i) -
          ∑ l, R.coordinateB i l • MvPolynomial.X (.weightTwo l))) = 0 := by
  classical
  rw [mul_sub, Finset.mul_sum]
  simp_rw [mul_smul_comm]
  change (MvPolynomial.lcoeff ℤ (xyExponent (L := L) a k))
      ((R.coordinateD i : ℤ) •
          (MvPolynomial.X u * MvPolynomial.X v * MvPolynomial.X (.weightOne i)) -
        ∑ l, R.coordinateB i l •
          (MvPolynomial.X u * MvPolynomial.X v * MvPolynomial.X (.weightTwo l))) = 0
  rw [map_sub, map_zsmul, map_sum]
  simp [coefficient_three_X_xy_zero, coefficient_C_mul_three_X_xy_zero]

private theorem terminal_firstRow_twoX_xyCoefficient_zero
    (R : StandingReductionData L) (i a b : I)
    (placement : Fin 3)
    (h₀ : placement = 0 → a ≤ b ∧ b ≤ i)
    (h₁ : placement = 1 → a ≤ i ∧ i ≤ b)
    (h₂ : placement = 2 → i ≤ a ∧ a ≤ b)
    (target : I) (k : K) :
    let p : AdaptedSmithPlacedPacket L L ev :=
      if placement = 0 then
        ⟨[adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b],
          .row (adaptedCoordinateXFactor L i), []⟩
      else if placement = 1 then
        ⟨[adaptedCoordinateXFactor L a], .row (adaptedCoordinateXFactor L i),
          [adaptedCoordinateXFactor L b]⟩
      else
        ⟨[], .row (adaptedCoordinateXFactor L i),
          [adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b]⟩
    adaptedPBWCoefficient L L ev (xyExponent (L := L) target k)
      (p.value L L ev) = 0 := by
  classical
  dsimp only
  by_cases hp₀ : placement = 0
  · rw [if_pos hp₀]
    rcases h₀ hp₀ with ⟨hab, hbi⟩
    change MvPolynomial.coeff (xyExponent (L := L) target k)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
    rw [leftLeftXX_firstRow_PBWSymbol R i a b hab hbi]
    exact firstRowTriple_xyCoefficient_zero R (.weightOne a) (.weightOne b) i target k
  · rw [if_neg hp₀]
    by_cases hp₁ : placement = 1
    · rw [if_pos hp₁]
      rcases h₁ hp₁ with ⟨hai, hib⟩
      change MvPolynomial.coeff (xyExponent (L := L) target k)
        (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
      rw [splitXX_firstRow_PBWSymbol R i a b hai hib]
      convert firstRowTriple_xyCoefficient_zero R
        (.weightOne a) (.weightOne b) i target k using 1 <;> ring
    · rw [if_neg hp₁]
      have hp₂ : placement = 2 := by fin_cases placement <;> simp_all
      rcases h₂ hp₂ with ⟨hia, hab⟩
      change MvPolynomial.coeff (xyExponent (L := L) target k)
        (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
      rw [rightRightXX_firstRow_PBWSymbol R i a b hia hab]
      convert firstRowTriple_xyCoefficient_zero R
        (.weightOne a) (.weightOne b) i target k using 1 <;> ring

private theorem terminal_firstRow_twoX_yyCoefficient_zero
    (R : StandingReductionData L) (i a b : I)
    (placement : Fin 3)
    (h₀ : placement = 0 → a ≤ b ∧ b ≤ i)
    (h₁ : placement = 1 → a ≤ i ∧ i ≤ b)
    (h₂ : placement = 2 → i ≤ a ∧ a ≤ b)
    (k l : K) :
    let p : AdaptedSmithPlacedPacket L L ev :=
      if placement = 0 then
        ⟨[adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b],
          .row (adaptedCoordinateXFactor L i), []⟩
      else if placement = 1 then
        ⟨[adaptedCoordinateXFactor L a], .row (adaptedCoordinateXFactor L i),
          [adaptedCoordinateXFactor L b]⟩
      else
        ⟨[], .row (adaptedCoordinateXFactor L i),
          [adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b]⟩
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
      (p.value L L ev) = 0 := by
  classical
  dsimp only
  by_cases hp₀ : placement = 0
  · rw [if_pos hp₀]
    rcases h₀ hp₀ with ⟨hab, hbi⟩
    change MvPolynomial.coeff (yyExponent (L := L) k l)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
    rw [leftLeftXX_firstRow_PBWSymbol R i a b hab hbi]
    exact firstRowTriple_yyCoefficient_zero R (.weightOne a) (.weightOne b) i k l
  · rw [if_neg hp₀]
    by_cases hp₁ : placement = 1
    · rw [if_pos hp₁]
      rcases h₁ hp₁ with ⟨hai, hib⟩
      change MvPolynomial.coeff (yyExponent (L := L) k l)
        (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
      rw [splitXX_firstRow_PBWSymbol R i a b hai hib]
      convert firstRowTriple_yyCoefficient_zero R
        (.weightOne a) (.weightOne b) i k l using 1 <;> ring
    · rw [if_neg hp₁]
      have hp₂ : placement = 2 := by fin_cases placement <;> simp_all
      rcases h₂ hp₂ with ⟨hia, hab⟩
      change MvPolynomial.coeff (yyExponent (L := L) k l)
        (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
      rw [rightRightXX_firstRow_PBWSymbol R i a b hia hab]
      convert firstRowTriple_yyCoefficient_zero R
        (.weightOne a) (.weightOne b) i k l using 1 <;> ring

private theorem firstRowWithX_yyCoefficient_zero
    (i j : I) (k l : K) :
    MvPolynomial.coeff (yyExponent (L := L) k l)
      ((MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j) :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        ((R.coordinateD i : ℤ) • MvPolynomial.X (.weightOne i) -
          ∑ h, R.coordinateB i h • MvPolynomial.X (.weightTwo h))) = 0 := by
  classical
  by_contra hc
  have hs := MvPolynomial.mem_support_iff.mpr hc
  have hs' := MvPolynomial.support_mul
    (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j) :
      MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) _ hs
  rw [Finset.mem_add] at hs'
  obtain ⟨f, hf, g, hg, hfg⟩ := hs'
  rw [MvPolynomial.support_X] at hf
  simp only [Finset.mem_singleton] at hf
  subst f
  have hv := congrArg
    (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e (.weightOne j)) hfg
  simp [yyExponent, yExponent] at hv

private theorem secondRowWithX_yyCoefficient_zero
    (i : I) (h k l : K) :
    MvPolynomial.coeff (yyExponent (L := L) k l)
      ((MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) :
          MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) *
        ((R.coordinateE h : ℤ) • MvPolynomial.X (.weightTwo h))) = 0 := by
  classical
  by_contra hc
  have hs := MvPolynomial.mem_support_iff.mpr hc
  have hs' := MvPolynomial.support_mul
    (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i) :
      MvPolynomial (FiniteClassTwoBasisIndex L) ℤ) _ hs
  rw [Finset.mem_add] at hs'
  obtain ⟨f, hf, g, hg, hfg⟩ := hs'
  rw [MvPolynomial.support_X] at hf
  simp only [Finset.mem_singleton] at hf
  subst f
  have hv := congrArg
    (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e (.weightOne i)) hfg
  simp [yyExponent, yExponent] at hv

private theorem leftLeftXX_secondRow_PBWSymbol
    (a b : I) (h : K) (hab : a ≤ b) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        ((⟨[adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b],
            .row (adaptedCoordinateYFactor L h), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) =
      MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne a) *
        MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne b) *
          ((R.coordinateE h : ℤ) •
            MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo h)) := by
  classical
  have ha : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L a) =
      ((collectedHomogeneousBasis L L ev 1 a : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) a
  have hb : adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L b) =
      ((collectedHomogeneousBasis L L ev 1 b : freeLieExact L 1) : F) := by
    simpa [adaptedCoordinateXFactor] using
      adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) b
  have hrow : adaptedLowRelationRow L L ev (adaptedCoordinateYFactor L h) =
      (collectedRelationRow L L ev 2 h : F) := by rfl
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_cons, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, ha, hb, hrow]
  rw [mul_assoc, adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
    show adaptedFreeEnvelopingToClassTwoEnveloping L
        (UniversalEnvelopingAlgebra.ι ℤ
          ((collectedHomogeneousBasis L L ev 1 a : freeLieExact L 1) : F)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (adaptedHomogeneousClassTwoBasis L L ev (.weightOne a)) by
          unfold adaptedFreeEnvelopingToClassTwoEnveloping
          rw [UniversalEnvelopingAlgebra.lift_ι_apply,
            adaptedHomogeneousClassTwoBasis_weightOne]
          rfl,
    LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
  change adaptedHomogeneousClassTwoAction L L ev
      (adaptedHomogeneousClassTwoBasis L L ev (.weightOne a))
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
            ((collectedHomogeneousBasis L L ev 1 b : freeLieExact L 1) : F) *
          UniversalEnvelopingAlgebra.ι ℤ
            (collectedRelationRow L L ev 2 h : F))) = _
  have hinner := leftX_secondRow_PBWSymbol (R := R) b h
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
    envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hb, hrow] at hinner
  rw [hinner, adaptedHomogeneousClassTwoAction_weightOne_apply,
    Derivation.leibniz, map_zsmul,
    adaptedCorrectionDerivation_X_weightOne,
    adaptedCorrectionDerivation_X_weightTwo]
  have hab' : (FiniteClassTwoBasisIndex.weightOne a :
      FiniteClassTwoBasisIndex L) ≤ .weightOne b := by
    change toLex ((0 : ℕ), a.1) ≤ toLex ((0 : ℕ), b.1)
    rw [Prod.Lex.le_iff]
    simpa using hab
  simp [not_lt_of_ge hab']
  ring

private theorem leftLeftXX_secondRow_yyCoefficient_zero
    (R : StandingReductionData L)
    (a b : I) (h : K) (hab : a ≤ b) (k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨[adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b],
            .row (adaptedCoordinateYFactor L h), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  change MvPolynomial.coeff (yyExponent (L := L) k l)
    (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
  rw [leftLeftXX_secondRow_PBWSymbol R a b h hab]
  rw [show MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne a) *
      MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne b) *
        ((R.coordinateE h : ℤ) •
          (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo h) :
            MvPolynomial (FiniteClassTwoBasisIndex L) ℤ)) =
      (R.coordinateE h : ℤ) •
        (MvPolynomial.X (.weightOne a) * MvPolynomial.X (.weightOne b) *
          MvPolynomial.X (.weightTwo h)) by
            rw [mul_smul_comm]]
  change (MvPolynomial.lcoeff ℤ (yyExponent (L := L) k l))
      ((R.coordinateE h : ℤ) •
        (MvPolynomial.X (.weightOne a) * MvPolynomial.X (.weightOne b) *
          MvPolynomial.X (.weightTwo h))) = 0
  rw [map_zsmul]
  simp [coefficient_three_variables_yy_zero]

/-- At total adapted weight four, only the certified weight-one head of a first
relation row can contribute: its higher tail starts in weight two and hence gives
weight at least five after multiplication by an external word of weight three. -/
private theorem firstRow_externalWeight_three_headCoefficient
    (i : I) (p : AdaptedSmithPlacedPacket L L ev)
    (hrel : p.relation = .row (adaptedCoordinateXFactor L i))
    (hext : p.externalWeight L = 3) (k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l) (p.value L L ev) =
      (R.coordinateD i : ℤ) *
        adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
          (envelopingWord ℤ F
              (p.left.map (adaptedLowBasisValue L L ev)) *
            UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
            envelopingWord ℤ F
              (p.right.map (adaptedLowBasisValue L L ev))) := by
  rcases p with ⟨left, relation, right⟩
  simp only at hrel hext ⊢
  subst relation
  let uL : UEA ℤ F := envelopingWord ℤ F
    (left.map (adaptedLowBasisValue L L ev))
  let uR : UEA ℤ F := envelopingWord ℤ F
    (right.map (adaptedLowBasisValue L L ev))
  let tail : F := (collectedRelationRow L L ev 1 i : F) -
    (R.coordinateD i : ℤ) • R.coordinateX i
  have htail : tail ∈ FreeLieDimension.lieHigh L 2 := by
    simpa [tail, coordinateD, coordinateX] using
      R.collectedRelationRow_sub_head_mem_lieHigh_succ 1 i
  have hleft := adaptedLowEnvelopingWord_mem_associativeHigh L L ev left
  have hright := adaptedLowEnvelopingWord_mem_associativeHigh L L ev right
  have hiota :
      FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
          (UniversalEnvelopingAlgebra.ι ℤ tail) ∈
        FreeLieDimension.associativeHigh L 2 := by
    have hfree := freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh L htail
    exact (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
      L tail).symm ▸ hfree
  have hdiff :
      FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
          (uL * UniversalEnvelopingAlgebra.ι ℤ tail * uR) ∈
        FreeLieDimension.associativeHigh L 5 := by
    have hext' : (left.map (adaptedLowBasisWeight L)).sum +
        (right.map (adaptedLowBasisWeight L)).sum = 3 := by
      simpa [AdaptedSmithPlacedPacket.externalWeight] using hext
    rw [show FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
          (uL * UniversalEnvelopingAlgebra.ι ℤ tail * uR) =
        FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L uL *
          FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
            (UniversalEnvelopingAlgebra.ι ℤ tail) *
          FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L uR by
            exact (map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
              (uL * UniversalEnvelopingAlgebra.ι ℤ tail) uR).trans
                (congrArg (fun z ↦ z *
                    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L uR)
                  (map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                    uL (UniversalEnvelopingAlgebra.ι ℤ tail)))]
    have hmul := FreeLieDimension.associativeHigh_mul L
      (FreeLieDimension.associativeHigh_mul L hleft hiota) hright
    have hind : (left.map (adaptedLowBasisWeight L)).sum + 2 +
        (right.map (adaptedLowBasisWeight L)).sum = 5 := by omega
    simpa [hind] using hmul
  have hcoeffTail : adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
      (uL * UniversalEnvelopingAlgebra.ι ℤ tail * uR) = 0 := by
    apply adaptedPBWCoefficient_eq_zero_of_mem_associativeHigh L L ev hdiff
    simp
  have hvalue :
      ((⟨left, .row (adaptedCoordinateXFactor L i), right⟩ :
        AdaptedSmithPlacedPacket L L ev).value L L ev) =
      (R.coordinateD i : ℤ) •
        (uL * UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) * uR) +
      (uL * UniversalEnvelopingAlgebra.ι ℤ tail * uR) := by
    simp only [AdaptedSmithPlacedPacket.value,
      AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
      AdaptedCollectedRelation.value]
    change uL * UniversalEnvelopingAlgebra.ι ℤ
        (collectedRelationRow L L ev 1 i : F) * uR = _
    have hdecomp : (collectedRelationRow L L ev 1 i : F) =
        (R.coordinateD i : ℤ) • R.coordinateX i + tail := by
      simp [tail]
    rw [hdecomp, map_add, map_zsmul]
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [hvalue, map_add, map_zsmul, hcoeffTail, add_zero]
  rfl

/-- The free representative of one variable in the shared class-two PBW basis. -/
private def adaptedCoordinateFreeValue
    (j : FiniteClassTwoBasisIndex L) : F :=
  match j with
  | .weightOne i => R.coordinateX i
  | .weightTwo k => R.coordinateY k

@[simp] private theorem freeClassTwoTruncation_adaptedCoordinateFreeValue
    (j : FiniteClassTwoBasisIndex L) :
    freeClassTwoTruncation L (R.adaptedCoordinateFreeValue j) =
      adaptedHomogeneousClassTwoBasis L L ev j := by
  cases j with
  | weightOne i =>
      simp [adaptedCoordinateFreeValue, coordinateX,
        adaptedHomogeneousClassTwoBasis_weightOne, finiteLowExactToClassTwo]
  | weightTwo k =>
      simp [adaptedCoordinateFreeValue, coordinateY,
        adaptedHomogeneousClassTwoBasis_weightTwo, finiteLowExactToClassTwo]

private theorem adaptedCoordinateWord_PBWSymbol
    (js : List (FiniteClassTwoBasisIndex L)) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (envelopingWord ℤ F (js.map R.adaptedCoordinateFreeValue)) =
      adaptedHomogeneousBasisWordAction L L ev js 1 := by
  induction js with
  | nil =>
      change (adaptedHomogeneousClassTwoTriangularRepresentation L L ev).envelopingAction
          (adaptedFreeEnvelopingToClassTwoEnveloping L 1) 1 = 1
      rw [map_one (adaptedFreeEnvelopingToClassTwoEnveloping L)]
      have hone := map_one
        (adaptedHomogeneousClassTwoTriangularRepresentation L L ev).envelopingAction
      rw [hone]
      rfl
  | cons j js ih =>
      simp only [List.map_cons, envelopingWord_cons]
      rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
        show adaptedFreeEnvelopingToClassTwoEnveloping L
            (UniversalEnvelopingAlgebra.ι ℤ (R.adaptedCoordinateFreeValue j)) =
          UniversalEnvelopingAlgebra.ι ℤ
            (adaptedHomogeneousClassTwoBasis L L ev j) by
              unfold adaptedFreeEnvelopingToClassTwoEnveloping
              rw [UniversalEnvelopingAlgebra.lift_ι_apply]
              change UniversalEnvelopingAlgebra.ι ℤ
                  (freeClassTwoTruncation L (R.adaptedCoordinateFreeValue j)) = _
              rw [R.freeClassTwoTruncation_adaptedCoordinateFreeValue],
        LieRings.PBW.TriangularRepresentation.envelopingAction_ι, ih,
        adaptedHomogeneousBasisWordAction_cons, Module.End.mul_apply]
      rfl

private theorem adaptedCoordinateWord_PBWSymbol_of_pairwise
    (js : List (FiniteClassTwoBasisIndex L)) (hjs : js.Pairwise (.≤.)) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (envelopingWord ℤ F (js.map R.adaptedCoordinateFreeValue)) =
      adaptedClassTwoVariableWord L js := by
  rw [R.adaptedCoordinateWord_PBWSymbol,
    adaptedHomogeneousBasisWordAction_apply_one L L ev js hjs]

private theorem adaptedCoordinateWord_yyCoefficient_zero_of_length_ne_two
    (js : List (FiniteClassTwoBasisIndex L)) (hjs : js.Pairwise (.≤.))
    (hlen : js.length ≠ 2) (k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        (envelopingWord ℤ F (js.map R.adaptedCoordinateFreeValue)) = 0 := by
  classical
  change MvPolynomial.coeff (yyExponent (L := L) k l)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
  rw [R.adaptedCoordinateWord_PBWSymbol_of_pairwise js hjs,
    adaptedClassTwoVariableWord_eq_monomial]
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro heq
  have hsum := congrArg
    (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e.sum fun _ n ↦ n) heq
  have hcard : (Multiset.toFinsupp
      (js : Multiset (FiniteClassTwoBasisIndex L))).sum (fun _ n ↦ n) =
      js.length := by
    simpa only [id_eq] using Multiset.toFinsupp_sum_eq
      (js : Multiset (FiniteClassTwoBasisIndex L))
  change (Multiset.toFinsupp
      (js : Multiset (FiniteClassTwoBasisIndex L))).sum (fun _ n ↦ n) = _ at hsum
  rw [hcard] at hsum
  simp [yyExponent, yExponent, Finsupp.sum_add_index] at hsum
  exact hlen hsum

private theorem freeClassTwoTruncation_adaptedLowBasisValue_eq_zero
    (x : AdaptedLowBasisIndex L) (hx : 3 ≤ adaptedLowBasisWeight L x) :
    freeClassTwoTruncation L (adaptedLowBasisValue L L ev x) = 0 := by
  apply (freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two L _).mpr
  have hmem := freeLieExact_mem_lieHigh L
    ⟨adaptedLowBasisValue L L ev x,
      adaptedLowBasisValue_mem_exact L L ev x⟩
  have hmem3 : adaptedLowBasisValue L L ev x ∈
      FreeLieDimension.lieHigh L 3 := by
    rcases hmem with ⟨p, hp, hpeq⟩
    exact ⟨p, FreeLieDimension.magmaHigh_mono L hx hp, hpeq⟩
  simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries] using hmem3

private theorem firstRow_rightHigh_yyCoefficient_zero
    (i : I) (x : AdaptedLowBasisIndex L)
    (hx : 3 ≤ adaptedLowBasisWeight L x) (k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
          UniversalEnvelopingAlgebra.ι ℤ
            (adaptedLowBasisValue L L ev x)) = 0 := by
  change MvPolynomial.coeff (yyExponent (L := L) k l)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
    show adaptedFreeEnvelopingToClassTwoEnveloping L
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (freeClassTwoTruncation L (R.coordinateX i)) by
          exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ _ _,
    LieRings.PBW.TriangularRepresentation.envelopingAction_ι,
    adaptedFreeEnvelopingToClassTwoPBWSymbol_iota,
    freeClassTwoTruncation_adaptedLowBasisValue_eq_zero x hx,
    map_zero]
  simp

private theorem terminal_firstRow_externalWeight_three_yyCoefficient_zero
    (R : StandingReductionData L) (i : I)
    (p : AdaptedSmithPlacedPacket L L ev)
    (hrel : p.relation = .row (adaptedCoordinateXFactor L i))
    (hext : p.externalWeight L = 3)
    (hterminal : adaptedPlacedPacketExpansion L L ev p = none)
    (k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        (p.value L L ev) = 0 := by
  classical
  rw [R.firstRow_externalWeight_three_headCoefficient i p hrel hext k l]
  suffices adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
      (envelopingWord ℤ F (p.left.map (adaptedLowBasisValue L L ev)) *
        UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
        envelopingWord ℤ F
      (p.right.map (adaptedLowBasisValue L L ev))) = 0 by rw [this, mul_zero]
  have hlow : p.totalWeight L < 5 := by
    rw [AdaptedSmithPlacedPacket.totalWeight, hrel]
    simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight, hext]
  have hv := adaptedPlacedPacket_terminal_virtualFactors_pairwise
    L L ev p (adaptedCoordinateXFactor L i) hrel hlow hterminal
  have horders := adaptedPlacedPacket_terminal_external_order
    L L ev p (adaptedCoordinateXFactor L i) hrel hlow hterminal
  let A := (p.left.map (adaptedLowBasisWeight L)).sum
  let B := (p.right.map (adaptedLowBasisWeight L)).sum
  have hAB : A + B = 3 := by
    simpa [A, B, AdaptedSmithPlacedPacket.externalWeight] using hext
  rcases (show A = 0 ∨ A = 1 ∨ A = 2 ∨ A = 3 by omega) with
    hA | hA | hA | hA
  · have hl := (adaptedWeightSum_eq_zero_iff (L := L) p.left).mp hA
    have hB : B = 3 := by omega
    rcases (adaptedWeightSum_eq_three_iff (L := L) p.right).mp hB with
      ⟨x, hr, hx⟩ | ⟨x, y, hr, hx, hy⟩ |
      ⟨x, y, hr, hx, hy⟩ | ⟨x, y, z, hr, hx, hy, hz⟩
    · rw [hl, hr]
      simpa [envelopingWord] using R.firstRow_rightHigh_yyCoefficient_zero i x
        (by omega) k l
    · obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
      obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateYFactor L y hy
      have hjs : ([FiniteClassTwoBasisIndex.weightOne i,
          .weightOne a, .weightTwo b] : List (FiniteClassTwoBasisIndex L)).Pairwise (.≤.) := by
        simpa [AdaptedSmithPlacedPacket.virtualFactors, hrel, hl, hr,
          adaptedCoordinateXFactor_le_iff, adaptedCoordinateXFactor_le_y] using hv
      have hz := R.adaptedCoordinateWord_yyCoefficient_zero_of_length_ne_two
        [.weightOne i, .weightOne a, .weightTwo b] hjs (by simp) k l
      simpa [hl, hr, envelopingWord, adaptedCoordinateFreeValue, coordinateX,
        coordinateY, adaptedCoordinateXFactor, adaptedCoordinateYFactor,
        adaptedLowBasisValue_indexOf, mul_assoc] using hz
    · have hord : x ≤ y := by
        have hp : (p.right).Pairwise (.≤.) := horders.2
        simpa [hr] using hp
      have hw := adaptedLowBasisWeight_mono L hord
      omega
    · obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
      obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
      obtain ⟨c, rfl⟩ := exists_eq_adaptedCoordinateXFactor L z hz
      have hjs : ([FiniteClassTwoBasisIndex.weightOne i,
          .weightOne a, .weightOne b, .weightOne c] :
            List (FiniteClassTwoBasisIndex L)).Pairwise (.≤.) := by
        simpa [AdaptedSmithPlacedPacket.virtualFactors, hrel, hl, hr,
          adaptedCoordinateXFactor_le_iff] using hv
      have hzero := R.adaptedCoordinateWord_yyCoefficient_zero_of_length_ne_two
        [.weightOne i, .weightOne a, .weightOne b, .weightOne c]
        hjs (by simp) k l
      simpa [hl, hr, envelopingWord, adaptedCoordinateFreeValue, coordinateX,
        adaptedCoordinateXFactor, adaptedLowBasisValue_indexOf, mul_assoc] using hzero

  · obtain ⟨x, hl, hx⟩ :=
      (adaptedWeightSum_eq_one_iff (L := L) p.left).mp hA
    obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
    have hB : B = 2 := by omega
    rcases (adaptedWeightSum_eq_two_iff (L := L) p.right).mp hB with
      ⟨y, hr, hy⟩ | ⟨y, z, hr, hy, hz⟩
    · obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateYFactor L y hy
      have hjs : ([FiniteClassTwoBasisIndex.weightOne a,
          .weightOne i, .weightTwo b] : List (FiniteClassTwoBasisIndex L)).Pairwise (.≤.) := by
        simpa [AdaptedSmithPlacedPacket.virtualFactors, hrel, hl, hr,
          adaptedCoordinateXFactor_le_iff, adaptedCoordinateXFactor_le_y] using hv
      have hzero := R.adaptedCoordinateWord_yyCoefficient_zero_of_length_ne_two
        [.weightOne a, .weightOne i, .weightTwo b] hjs (by simp) k l
      simpa [hl, hr, envelopingWord, adaptedCoordinateFreeValue, coordinateX,
        coordinateY, adaptedCoordinateXFactor, adaptedCoordinateYFactor,
        adaptedLowBasisValue_indexOf, mul_assoc] using hzero
    · obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
      obtain ⟨c, rfl⟩ := exists_eq_adaptedCoordinateXFactor L z hz
      have hjs : ([FiniteClassTwoBasisIndex.weightOne a, .weightOne i,
          .weightOne b, .weightOne c] :
            List (FiniteClassTwoBasisIndex L)).Pairwise (.≤.) := by
        simpa [AdaptedSmithPlacedPacket.virtualFactors, hrel, hl, hr,
          adaptedCoordinateXFactor_le_iff] using hv
      have hzero := R.adaptedCoordinateWord_yyCoefficient_zero_of_length_ne_two
        [.weightOne a, .weightOne i, .weightOne b, .weightOne c]
        hjs (by simp) k l
      simpa [hl, hr, envelopingWord, adaptedCoordinateFreeValue, coordinateX,
        adaptedCoordinateXFactor, adaptedLowBasisValue_indexOf, mul_assoc] using hzero
  · have hB : B = 1 := by omega
    obtain ⟨z, hr, hz⟩ :=
      (adaptedWeightSum_eq_one_iff (L := L) p.right).mp hB
    obtain ⟨c, rfl⟩ := exists_eq_adaptedCoordinateXFactor L z hz
    rcases (adaptedWeightSum_eq_two_iff (L := L) p.left).mp hA with
      ⟨x, hl, hx⟩ | ⟨x, y, hl, hx, hy⟩
    · have hbad := adaptedPlacedPacket_terminal_last_le_head
        L L ev p (adaptedCoordinateXFactor L i) hrel hlow hterminal [] x
          (by rw [hl]; rfl)
      have hw := adaptedLowBasisWeight_mono L hbad
      simp at hw
      omega
    · obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
      obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
      have hjs : ([FiniteClassTwoBasisIndex.weightOne a, .weightOne b,
          .weightOne i, .weightOne c] :
            List (FiniteClassTwoBasisIndex L)).Pairwise (.≤.) := by
        simpa [AdaptedSmithPlacedPacket.virtualFactors, hrel, hl, hr,
          adaptedCoordinateXFactor_le_iff] using hv
      have hzero := R.adaptedCoordinateWord_yyCoefficient_zero_of_length_ne_two
        [.weightOne a, .weightOne b, .weightOne i, .weightOne c]
        hjs (by simp) k l
      simpa [hl, hr, envelopingWord, adaptedCoordinateFreeValue, coordinateX,
        adaptedCoordinateXFactor, adaptedLowBasisValue_indexOf, mul_assoc] using hzero
  · have hB : B = 0 := by omega
    have hr := (adaptedWeightSum_eq_zero_iff (L := L) p.right).mp hB
    rcases (adaptedWeightSum_eq_three_iff (L := L) p.left).mp hA with
      ⟨x, hl, hx⟩ | ⟨x, y, hl, hx, hy⟩ |
      ⟨x, y, hl, hx, hy⟩ | ⟨x, y, z, hl, hx, hy, hz⟩
    · have hbad := adaptedPlacedPacket_terminal_last_le_head
        L L ev p (adaptedCoordinateXFactor L i) hrel hlow hterminal [] x
          (by rw [hl]; rfl)
      have hw := adaptedLowBasisWeight_mono L hbad
      simp at hw
      omega
    · have hbad := adaptedPlacedPacket_terminal_last_le_head
        L L ev p (adaptedCoordinateXFactor L i) hrel hlow hterminal [x] y
          (by rw [hl]; rfl)
      have hw := adaptedLowBasisWeight_mono L hbad
      simp at hw
      omega
    · have hord : x ≤ y := by
        have hp : p.left.Pairwise (.≤.) := horders.1
        simpa [hl] using hp
      have hw := adaptedLowBasisWeight_mono L hord
      omega
    · obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
      obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
      obtain ⟨c, rfl⟩ := exists_eq_adaptedCoordinateXFactor L z hz
      have hjs : ([FiniteClassTwoBasisIndex.weightOne a, .weightOne b,
          .weightOne c, .weightOne i] :
            List (FiniteClassTwoBasisIndex L)).Pairwise (.≤.) := by
        simpa [AdaptedSmithPlacedPacket.virtualFactors, hrel, hl, hr,
          adaptedCoordinateXFactor_le_iff] using hv
      have hzero := R.adaptedCoordinateWord_yyCoefficient_zero_of_length_ne_two
        [.weightOne a, .weightOne b, .weightOne c, .weightOne i]
        hjs (by simp) k l
      simpa [hl, hr, envelopingWord, adaptedCoordinateFreeValue, coordinateX,
        adaptedCoordinateXFactor, adaptedLowBasisValue_indexOf, mul_assoc] using hzero

private theorem scalarFirstRow_yyCoefficient_zero
    (R : StandingReductionData L) (i : I) (k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨[], .row (adaptedCoordinateXFactor L i), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  classical
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one, adaptedLowRelationRow, adaptedCoordinateXFactor,
    adaptedLowBasisIndexOf]
  change MvPolynomial.coeff (yyExponent (L := L) k l)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 1 i : F))) = 0
  rw [R.firstRow_PBWSymbol, MvPolynomial.coeff_sub,
    coefficient_zsmul_X (L := L), MvPolynomial.coeff_sum]
  simp_rw [coefficient_zsmul_X (L := L)]
  have hone (u : FiniteClassTwoBasisIndex L) :
      Finsupp.single u 1 ≠ yyExponent (L := L) k l := by
    intro h
    have hsum := congrArg
      (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e.sum fun _ n ↦ n) h
    simp [yyExponent, yExponent, Finsupp.sum_add_index] at hsum
  simp [hone]

private theorem scalarSecondRow_yyCoefficient_zero
    (R : StandingReductionData L) (h k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨[], .row (adaptedCoordinateYFactor L h), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one, adaptedLowRelationRow, adaptedCoordinateYFactor,
    adaptedLowBasisIndexOf]
  change MvPolynomial.coeff (yyExponent (L := L) k l)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 2 h : F))) = 0
  rw [R.secondRow_PBWSymbol, coefficient_zsmul_X (L := L)]
  rw [if_neg]
  intro heq
  have hsum := congrArg
    (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e.sum fun _ n ↦ n) heq
  simp [yyExponent, yExponent, Finsupp.sum_add_index] at hsum

private theorem leftX_firstRow_yyCoefficient_zero
    (R : StandingReductionData L)
    (i j : I) (hji : j ≤ i) (k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨[adaptedCoordinateXFactor L j],
            .row (adaptedCoordinateXFactor L i), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  change MvPolynomial.coeff (yyExponent (L := L) k l)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
  rw [leftX_firstRow_PBWSymbol (R := R) i j hji]
  exact firstRowWithX_yyCoefficient_zero R i j k l

private theorem rightX_firstRow_yyCoefficient_zero
    (R : StandingReductionData L)
    (i j : I) (hij : i ≤ j) (k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨[], .row (adaptedCoordinateXFactor L i),
            [adaptedCoordinateXFactor L j]⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  change MvPolynomial.coeff (yyExponent (L := L) k l)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
  rw [rightX_firstRow_PBWSymbol (R := R) i j hij, mul_comm]
  exact firstRowWithX_yyCoefficient_zero R i j k l

private theorem leftX_secondRow_yyCoefficient_zero
    (R : StandingReductionData L) (i : I) (h k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨[adaptedCoordinateXFactor L i],
            .row (adaptedCoordinateYFactor L h), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  change MvPolynomial.coeff (yyExponent (L := L) k l)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = 0
  rw [leftX_secondRow_PBWSymbol R i h]
  exact secondRowWithX_yyCoefficient_zero R i h k l

private theorem highRow_packet_yyCoefficient_zero
    (R : StandingReductionData L) (row : AdaptedLowRelationRowIndex L)
    (hrow : 3 ≤ adaptedLowBasisWeight L row)
    (left right : List (AdaptedLowBasisIndex L)) (k l : K) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
        ((⟨left, .row row, right⟩ : AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value]
  let u := envelopingWord ℤ F (left.map (adaptedLowBasisValue L L ev)) *
      UniversalEnvelopingAlgebra.ι ℤ (adaptedLowRelationRow L L ev row) *
      envelopingWord ℤ F (right.map (adaptedLowBasisValue L L ev))
  have hz : freeClassTwoTruncation L (adaptedLowRelationRow L L ev row) = 0 := by
    apply (freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two L _).mpr
    have hr := adaptedLowRelationRow_mem_lieHigh L L ev row
    have hr3 : adaptedLowRelationRow L L ev row ∈
        FreeLieDimension.lieHigh L 3 := by
      rcases hr with ⟨p, hp, hpeq⟩
      exact ⟨p, FreeLieDimension.magmaHigh_mono L hrow hp, hpeq⟩
    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries] using hr3
  have hmap : adaptedFreeEnvelopingToClassTwoEnveloping L u = 0 := by
    dsimp only [u]
    rw [map_mul, map_mul,
      show adaptedFreeEnvelopingToClassTwoEnveloping L
          (UniversalEnvelopingAlgebra.ι ℤ
            (adaptedLowRelationRow L L ev row)) =
        UniversalEnvelopingAlgebra.ι ℤ
          (freeClassTwoTruncation L (adaptedLowRelationRow L L ev row)) by
            exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ _ _,
      hz, map_zero, mul_zero, zero_mul]
  change MvPolynomial.coeff (yyExponent (L := L) k l)
      ((adaptedHomogeneousClassTwoTriangularRepresentation L L ev).vacuumEvaluation
        (adaptedFreeEnvelopingToClassTwoEnveloping L u)) = 0
  rw [hmap, map_zero]
  rfl

private theorem scalarFirstRow_xyCoefficient
    (R : StandingReductionData L) (i a : I) (k : K) :
    adaptedPBWCoefficient L L ev (xyExponent (L := L) a k)
        ((⟨[], .row (adaptedCoordinateXFactor L i), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  classical
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one, adaptedLowRelationRow, adaptedCoordinateXFactor,
    adaptedLowBasisIndexOf]
  change MvPolynomial.coeff (xyExponent (L := L) a k)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 1 i : F))) = 0
  rw [R.firstRow_PBWSymbol, MvPolynomial.coeff_sub,
    coefficient_zsmul_X (L := L), MvPolynomial.coeff_sum]
  simp_rw [coefficient_zsmul_X (L := L)]
  have hone (u : FiniteClassTwoBasisIndex L) :
      Finsupp.single u 1 ≠ xyExponent (L := L) a k := by
    intro h
    have hsum := congrArg
      (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e.sum fun _ n ↦ n) h
    simp [xyExponent, xExponent, yExponent, Finsupp.sum_add_index] at hsum
  simp [hone]

private theorem scalarSecondRow_xyCoefficient
    (R : StandingReductionData L) (l : K) (a : I) (k : K) :
    adaptedPBWCoefficient L L ev (xyExponent (L := L) a k)
        ((⟨[], .row (adaptedCoordinateYFactor L l), []⟩ :
          AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  classical
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one, adaptedLowRelationRow, adaptedCoordinateYFactor,
    adaptedLowBasisIndexOf]
  change MvPolynomial.coeff (xyExponent (L := L) a k)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 2 l : F))) = 0
  rw [R.secondRow_PBWSymbol, coefficient_zsmul_X (L := L)]
  have hone : Finsupp.single (FiniteClassTwoBasisIndex.weightTwo l) 1 ≠
      xyExponent (L := L) a k := by
    intro h
    have hsum := congrArg
      (fun e : FiniteClassTwoBasisIndex L →₀ ℕ ↦ e.sum fun _ n ↦ n) h
    simp [xyExponent, xExponent, yExponent, Finsupp.sum_add_index] at hsum
  simp [hone]

private theorem scalarRow_weightThree_xyCoefficient
    (row : AdaptedLowRelationRowIndex L)
    (hrow : adaptedLowBasisWeight L row = 3) (a : I) (k : K) :
    adaptedPBWCoefficient L L ev (xyExponent (L := L) a k)
        ((⟨[], .row row, []⟩ : AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
  simp only [AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
    one_mul, mul_one]
  change MvPolynomial.coeff (xyExponent (L := L) a k)
      (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (adaptedLowRelationRow L L ev row : F))) = 0
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_iota]
  have hz : freeClassTwoTruncation L (adaptedLowRelationRow L L ev row) = 0 :=
    (freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two L _).mpr (by
      have hr := adaptedLowRelationRow_mem_lieHigh L L ev row
      simpa [adaptedLowRelationRowWeight, hrow,
        FreeLieDimension.lieHigh_eq_lowerCentralSeries] using hr)
  rw [hz, map_zero]
  rfl


local instance adaptedRowPacketDecidable
    (i : AdaptedLowRelationRowIndex L)
    (left right : List (AdaptedLowBasisIndex L))
    (p : AdaptedSmithPlacedPacket L L ev) :
    Decidable (IsAdaptedRowPacket L L ev i left right p) :=
  Classical.propDecidable _

private theorem terminalPacket_xyCoefficient
    (R : StandingReductionData L)
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    (a : I) (k : K) (p : AdaptedSmithPlacedPacket L L ev)
    (hp : p ∈ w.terminalPackets.support) :
    adaptedPBWCoefficient L L ev (xyExponent (L := L) a k) (p.value L L ev) =
      ( (∑ i : I, ∑ j : I,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [adaptedCoordinateXFactor L j] [] p
            then if j = a then -R.coordinateB i k else 0 else 0) +
        (∑ i : I, ∑ j : I,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [] [adaptedCoordinateXFactor L j] p
            then if j = a then -R.coordinateB i k else 0 else 0)) +
      ( (∑ i : I, ∑ l : K,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [] [adaptedCoordinateYFactor L l] p
            then if i = a ∧ l = k then (R.coordinateD i : ℤ) else 0 else 0) +
        (∑ i : I, ∑ l : K,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L l)
              [adaptedCoordinateXFactor L i] [] p
            then if i = a ∧ l = k then (R.coordinateE l : ℤ) else 0 else 0)) := by
  classical
  by_cases hhigh : 3 < p.totalWeight L
  · have hcoeff := adaptedPBWCoefficient_packet_eq_zero_of_lt L L ev p
      (xyExponent (L := L) a k) (by simpa using hhigh)
    rw [hcoeff]
    have hLX (i j : I) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateXFactor L i) [adaptedCoordinateXFactor L j] [] p := by
      rintro ⟨hl, hr, hh⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hr,
        AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
    have hRX (i j : I) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateXFactor L i) [] [adaptedCoordinateXFactor L j] p := by
      rintro ⟨hl, hr, hh⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hr,
        AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
    have hRY (i : I) (l : K) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateXFactor L i) [] [adaptedCoordinateYFactor L l] p := by
      rintro ⟨hl, hr, hh⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hr,
        AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
    have hLY (i : I) (l : K) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateYFactor L l) [adaptedCoordinateXFactor L i] [] p := by
      rintro ⟨hl, hr, hh⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hr,
        AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
    simp [hLX, hRX, hRY, hLY]
  · have hle : p.totalWeight L ≤ 3 := Nat.le_of_not_gt hhigh
    have hterminal := w.terminalPackets_terminal p hp
    cases hrel : p.relation with
    | high r hr =>
        exfalso
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
        simp [AdaptedCollectedRelation.weight] at hle
        omega
    | row row =>
      have hrowle : adaptedLowBasisWeight L row ≤ 3 := by
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
        simp only [AdaptedCollectedRelation.weight,
          adaptedLowRelationRowWeight] at hle
        omega
      have hrowpos := adaptedLowBasisWeight_pos L row
      rcases (show adaptedLowBasisWeight L row = 1 ∨
          adaptedLowBasisWeight L row = 2 ∨
          adaptedLowBasisWeight L row = 3 by omega) with hrowone | hrowtwo | hrowthree
      · obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L row hrowone
        have hextle : p.externalWeight L ≤ 2 := by
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp only [AdaptedCollectedRelation.weight,
            adaptedLowRelationRowWeight, adaptedCoordinateXFactor_weight] at hle
          omega
        rcases (show p.externalWeight L = 0 ∨ p.externalWeight L = 1 ∨
            p.externalWeight L = 2 by omega) with hextzero | hextone | hexttwo
        · obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hextzero
          rcases p with ⟨left, relation, right⟩
          simp only at hl hr hrel
          subst left; subst relation; subst right
          rw [scalarFirstRow_xyCoefficient R i a k]
          simp [IsAdaptedRowPacket]
        · rcases p.externalWeight_eq_one_iff.mp hextone with hleft | hright
          · obtain ⟨x, hl, hr, hx⟩ := hleft
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hji := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [] (adaptedCoordinateXFactor L j) (by rw [hl]; rfl)
            have hji' : j ≤ i := (adaptedCoordinateXFactor_le_iff j i).mp hji
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            change MvPolynomial.coeff (xyExponent (L := L) a k)
              (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = _
            rw [leftX_firstRow_PBWSymbol (R := R) i j hji',
              firstRowWithX_xyCoefficient R i j a k]
            by_cases haj : a = j <;>
              simp [haj, IsAdaptedRowPacket, adaptedCoordinateXFactor_inj_iff, eq_comm]
            all_goals
              rw [Finset.sum_eq_single i]
              · rw [Finset.sum_eq_single j]
                · simp_all
                · intro x _ hxj
                  simp [hxj, Ne.symm hxj]
                · simp
              · intro x _ hxi
                apply Finset.sum_eq_zero
                intro y _
                simp [hxi, Ne.symm hxi]
              · simp
          · obtain ⟨x, hl, hr, hx⟩ := hright
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hij := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L j) [] (by simp [hr])
            have hij' : i ≤ j := (adaptedCoordinateXFactor_le_iff i j).mp hij
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            change MvPolynomial.coeff (xyExponent (L := L) a k)
              (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = _
            rw [rightX_firstRow_PBWSymbol (R := R) i j hij', mul_comm,
              firstRowWithX_xyCoefficient R i j a k]
            by_cases haj : a = j <;>
              simp [haj, IsAdaptedRowPacket, adaptedCoordinateXFactor_inj_iff, eq_comm]
            all_goals
              rw [Finset.sum_eq_single i]
              · rw [Finset.sum_eq_single j]
                · simp_all
                · intro x _ hxj
                  simp [hxj, Ne.symm hxj]
                · simp
              · intro x _ hxi
                apply Finset.sum_eq_zero
                intro y _
                simp [hxi, Ne.symm hxi]
              · simp
        · rcases p.externalWeight_eq_two_iff.mp hexttwo with
            hYleft | hYright | hXXleft | hXXsplit | hXXright
          · obtain ⟨x, hl, hr, hx⟩ := hYleft
            obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateYFactor L x hx
            have hbad := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [] (adaptedCoordinateYFactor L l) (by rw [hl]; rfl)
            exact (adaptedCoordinateYFactor_not_le_x l i hbad).elim
          · obtain ⟨x, hl, hr, hx⟩ := hYright
            obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateYFactor L x hx
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            change MvPolynomial.coeff (xyExponent (L := L) a k)
              (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = _
            rw [rightY_firstRow_PBWSymbol R i l,
              firstRowWithY_xyCoefficient R i a l k]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXleft
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
            have hord := adaptedPlacedPacket_terminal_external_order
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega) hterminal
            have hjl : j ≤ l := by
              have := (by simpa [hl] using hord.1 :
                [adaptedCoordinateXFactor L j, adaptedCoordinateXFactor L l].Pairwise (.≤.))
              exact (adaptedCoordinateXFactor_le_iff j l).mp (by simpa using this)
            have hli := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [adaptedCoordinateXFactor L j]
                (adaptedCoordinateXFactor L l) (by rw [hl]; rfl)
            have hli' := (adaptedCoordinateXFactor_le_iff l i).mp hli
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            have hzero := terminal_firstRow_twoX_xyCoefficient_zero R i j l 0
              (by intro; exact ⟨hjl, hli'⟩) (by simp) (by simp) a k
            norm_num at hzero
            rw [hzero]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXsplit
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
            have hji := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [] (adaptedCoordinateXFactor L j) (by rw [hl]; rfl)
            have hil := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L l) [] (by rw [hr])
            have hji' := (adaptedCoordinateXFactor_le_iff j i).mp hji
            have hil' := (adaptedCoordinateXFactor_le_iff i l).mp hil
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            have hzero := terminal_firstRow_twoX_xyCoefficient_zero R i j l 1
              (by simp) (by intro; exact ⟨hji', hil'⟩) (by simp) a k
            norm_num at hzero
            rw [hzero]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXright
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
            have hij := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L j)
                [adaptedCoordinateXFactor L l] (by rw [hr])
            have hord := adaptedPlacedPacket_terminal_external_order
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega) hterminal
            have hjl : j ≤ l := by
              have := (by simpa [hr] using hord.2 :
                [adaptedCoordinateXFactor L j, adaptedCoordinateXFactor L l].Pairwise (.≤.))
              exact (adaptedCoordinateXFactor_le_iff j l).mp (by simpa using this)
            have hij' := (adaptedCoordinateXFactor_le_iff i j).mp hij
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            have hzero := terminal_firstRow_twoX_xyCoefficient_zero R i j l 2
              (by simp) (by simp) (by intro; exact ⟨hij', hjl⟩) a k
            have hzero' : adaptedPBWCoefficient L L ev (xyExponent (L := L) a k)
                ((⟨[], .row (adaptedCoordinateXFactor L i),
                  [adaptedCoordinateXFactor L j, adaptedCoordinateXFactor L l]⟩ :
                    AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
              simpa using hzero
            rw [hzero']
            simp [IsAdaptedRowPacket]
      · obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateYFactor L row hrowtwo
        have hextle : p.externalWeight L ≤ 1 := by
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp only [AdaptedCollectedRelation.weight,
            adaptedLowRelationRowWeight, adaptedCoordinateYFactor_weight] at hle
          omega
        rcases (show p.externalWeight L = 0 ∨ p.externalWeight L = 1 by omega) with
          hextzero | hextone
        · obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hextzero
          rcases p with ⟨left, relation, right⟩
          simp only at hl hr hrel
          subst left; subst relation; subst right
          rw [scalarSecondRow_xyCoefficient R l a k]
          simp [IsAdaptedRowPacket]
        · rcases p.externalWeight_eq_one_iff.mp hextone with hleft | hright
          · obtain ⟨x, hl, hr, hx⟩ := hleft
            obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            change MvPolynomial.coeff (xyExponent (L := L) a k)
              (adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev _) = _
            rw [leftX_secondRow_PBWSymbol R i l,
              secondRowWithX_xyCoefficient R i a l k]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, hl, hr, hx⟩ := hright
            obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hbad := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateYFactor L l) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L i) [] (by rw [hr])
            exact (adaptedCoordinateYFactor_not_le_x l i hbad).elim
      · have hext : p.externalWeight L = 0 := by
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp only [AdaptedCollectedRelation.weight,
            adaptedLowRelationRowWeight, hrowthree] at hle
          omega
        obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hext
        rcases p with ⟨left, relation, right⟩
        simp only at hl hr hrel
        subst left; subst relation; subst right
        rw [scalarRow_weightThree_xyCoefficient row hrowthree a k]
        simp [IsAdaptedRowPacket]

private theorem terminalPacket_yyCoefficient
    (R : StandingReductionData L)
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    (k l : K) (p : AdaptedSmithPlacedPacket L L ev)
    (hp : p ∈ w.terminalPackets.support) :
    adaptedPBWCoefficient L L ev (yyExponent (L := L) k l) (p.value L L ev) =
      (∑ i : I, ∑ b : K,
        if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [] [adaptedCoordinateYFactor L b] p then
          -∑ h : K, if yExponent (L := L) h + yExponent (L := L) b =
              yyExponent (L := L) k l then R.coordinateB i h else 0
        else 0) +
      (∑ h : K, ∑ b : K,
        if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L h)
            [] [adaptedCoordinateYFactor L b] p then
          if yExponent (L := L) h + yExponent (L := L) b =
              yyExponent (L := L) k l then (R.coordinateE h : ℤ) else 0
        else 0) +
      (∑ b : K, ∑ h : K,
        if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L h)
            [adaptedCoordinateYFactor L b] [] p then
          if yExponent (L := L) b + yExponent (L := L) h =
              yyExponent (L := L) k l then (R.coordinateE h : ℤ) else 0
        else 0) := by
  classical
  by_cases hhigh : 4 < p.totalWeight L
  · have hcoeff := adaptedPBWCoefficient_packet_eq_zero_of_lt L L ev p
      (yyExponent (L := L) k l) (by simpa using hhigh)
    rw [hcoeff]
    have hrY (i : I) (b : K) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateXFactor L i) [] [adaptedCoordinateYFactor L b] p := by
      rintro ⟨hl, hrel, hr⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr] at hhigh
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
    have hsY (h b : K) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateYFactor L h) [] [adaptedCoordinateYFactor L b] p := by
      rintro ⟨hl, hrel, hr⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr] at hhigh
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
    have hYs (b h : K) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateYFactor L h) [adaptedCoordinateYFactor L b] [] p := by
      rintro ⟨hl, hrel, hr⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr] at hhigh
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
    simp [hrY, hsY, hYs]
  · have hle : p.totalWeight L ≤ 4 := Nat.le_of_not_gt hhigh
    have hterminal := w.terminalPackets_terminal p hp
    cases hrel : p.relation with
    | high r hr =>
        exfalso
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
        simp [AdaptedCollectedRelation.weight] at hle
        omega
    | row row =>
      have hrowle : adaptedLowBasisWeight L row ≤ 4 := by
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
        simp only [AdaptedCollectedRelation.weight,
          adaptedLowRelationRowWeight] at hle
        omega
      have hrowpos := adaptedLowBasisWeight_pos L row
      rcases (show adaptedLowBasisWeight L row = 1 ∨
          adaptedLowBasisWeight L row = 2 ∨
          adaptedLowBasisWeight L row = 3 ∨
          adaptedLowBasisWeight L row = 4 by omega) with
        hrowone | hrowtwo | hrowthree | hrowfour
      · obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L row hrowone
        have hextle : p.externalWeight L ≤ 3 := by
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp only [AdaptedCollectedRelation.weight,
            adaptedLowRelationRowWeight, adaptedCoordinateXFactor_weight] at hle
          omega
        rcases (show p.externalWeight L = 0 ∨ p.externalWeight L = 1 ∨
            p.externalWeight L = 2 ∨ p.externalWeight L = 3 by omega) with
          hextzero | hextone | hexttwo | hextthree
        · obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hextzero
          rcases p with ⟨left, relation, right⟩
          simp only at hl hr hrel
          subst left; subst relation; subst right
          rw [R.scalarFirstRow_yyCoefficient_zero i k l]
          simp [IsAdaptedRowPacket]
        · rcases p.externalWeight_eq_one_iff.mp hextone with hleft | hright
          · obtain ⟨x, hl, hr, hx⟩ := hleft
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hji := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [] (adaptedCoordinateXFactor L j) (by rw [hl]; rfl)
            have hji' := (adaptedCoordinateXFactor_le_iff j i).mp hji
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            rw [R.leftX_firstRow_yyCoefficient_zero i j hji' k l]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, hl, hr, hx⟩ := hright
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hij := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L j) [] (by rw [hr])
            have hij' := (adaptedCoordinateXFactor_le_iff i j).mp hij
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            rw [R.rightX_firstRow_yyCoefficient_zero i j hij' k l]
            simp [IsAdaptedRowPacket]
        · rcases p.externalWeight_eq_two_iff.mp hexttwo with
            hYleft | hYright | hXXleft | hXXsplit | hXXright
          · obtain ⟨x, hl, hr, hx⟩ := hYleft
            obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateYFactor L x hx
            have hbad := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [] (adaptedCoordinateYFactor L b) (by rw [hl]; rfl)
            exact (adaptedCoordinateYFactor_not_le_x b i hbad).elim
          · obtain ⟨x, hl, hr, hx⟩ := hYright
            obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateYFactor L x hx
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            rw [R.rightY_firstRow_yyCoefficient i b k l]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXleft
            obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
            have hord := adaptedPlacedPacket_terminal_external_order
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega) hterminal
            have hab : a ≤ b := (adaptedCoordinateXFactor_le_iff a b).mp (by
              have := (by simpa [hl] using hord.1 :
                [adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b].Pairwise (.≤.))
              simpa using this)
            have hbi := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [adaptedCoordinateXFactor L a]
                (adaptedCoordinateXFactor L b) (by rw [hl]; rfl)
            have hbi' := (adaptedCoordinateXFactor_le_iff b i).mp hbi
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            have hz := terminal_firstRow_twoX_yyCoefficient_zero R i a b 0
              (by intro; exact ⟨hab, hbi'⟩) (by simp) (by simp) k l
            norm_num at hz
            rw [hz]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXsplit
            obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
            have hai := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [] (adaptedCoordinateXFactor L a) (by rw [hl]; rfl)
            have hib := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L b) [] (by rw [hr])
            have hai' := (adaptedCoordinateXFactor_le_iff a i).mp hai
            have hib' := (adaptedCoordinateXFactor_le_iff i b).mp hib
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            have hz := terminal_firstRow_twoX_yyCoefficient_zero R i a b 1
              (by simp) (by intro; exact ⟨hai', hib'⟩) (by simp) k l
            norm_num at hz
            rw [hz]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXright
            obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
            have hia := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L a)
                [adaptedCoordinateXFactor L b] (by rw [hr])
            have hord := adaptedPlacedPacket_terminal_external_order
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega) hterminal
            have hab : a ≤ b := (adaptedCoordinateXFactor_le_iff a b).mp (by
              have := (by simpa [hr] using hord.2 :
                [adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b].Pairwise (.≤.))
              simpa using this)
            have hia' := (adaptedCoordinateXFactor_le_iff i a).mp hia
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            have hz := terminal_firstRow_twoX_yyCoefficient_zero R i a b 2
              (by simp) (by simp) (by intro; exact ⟨hia', hab⟩) k l
            have hz' : adaptedPBWCoefficient L L ev (yyExponent (L := L) k l)
                ((⟨[], .row (adaptedCoordinateXFactor L i),
                  [adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b]⟩ :
                    AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 := by
              simpa using hz
            rw [hz']
            simp [IsAdaptedRowPacket]
        · rw [R.terminal_firstRow_externalWeight_three_yyCoefficient_zero
            i p hrel hextthree hterminal k l]
          have hrY (j : I) (b : K) : ¬IsAdaptedRowPacket L L ev
              (adaptedCoordinateXFactor L j) [] [adaptedCoordinateYFactor L b] p := by
            rintro ⟨hl, hrow, hr⟩
            rw [AdaptedSmithPlacedPacket.externalWeight, hl, hr] at hextthree
            simp at hextthree
          have hsY (a b : K) : ¬IsAdaptedRowPacket L L ev
              (adaptedCoordinateYFactor L a) [] [adaptedCoordinateYFactor L b] p := by
            rintro ⟨hl, hrow, hr⟩
            exact (by simpa [hrel] using hrow)
          have hYs (a b : K) : ¬IsAdaptedRowPacket L L ev
              (adaptedCoordinateYFactor L b) [adaptedCoordinateYFactor L a] [] p := by
            rintro ⟨hl, hrow, hr⟩
            exact (by simpa [hrel] using hrow)
          simp [hrY, hsY, hYs]
      · obtain ⟨h, rfl⟩ := exists_eq_adaptedCoordinateYFactor L row hrowtwo
        have hextle : p.externalWeight L ≤ 2 := by
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp only [AdaptedCollectedRelation.weight,
            adaptedLowRelationRowWeight, adaptedCoordinateYFactor_weight] at hle
          omega
        rcases (show p.externalWeight L = 0 ∨ p.externalWeight L = 1 ∨
            p.externalWeight L = 2 by omega) with hextzero | hextone | hexttwo
        · obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hextzero
          rcases p with ⟨left, relation, right⟩
          simp only at hl hr hrel
          subst left; subst relation; subst right
          rw [R.scalarSecondRow_yyCoefficient_zero h k l]
          simp [IsAdaptedRowPacket]
        · rcases p.externalWeight_eq_one_iff.mp hextone with hleft | hright
          · obtain ⟨x, hl, hr, hx⟩ := hleft
            obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            rw [R.leftX_secondRow_yyCoefficient_zero i h k l]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, hl, hr, hx⟩ := hright
            obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hbad := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateYFactor L h) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L i) [] (by rw [hr])
            exact (adaptedCoordinateYFactor_not_le_x h i hbad).elim
        · rcases p.externalWeight_eq_two_iff.mp hexttwo with
            hYleft | hYright | hXXleft | hXXsplit | hXXright
          · obtain ⟨x, hl, hr, hx⟩ := hYleft
            obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateYFactor L x hx
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            rw [R.leftY_secondRow_yyCoefficient b h k l]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, hl, hr, hx⟩ := hYright
            obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateYFactor L x hx
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            rw [R.rightY_secondRow_yyCoefficient h b k l]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXleft
            obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
            have hord := adaptedPlacedPacket_terminal_external_order
              L L ev p (adaptedCoordinateYFactor L h) hrel (by omega) hterminal
            have hab : a ≤ b := (adaptedCoordinateXFactor_le_iff a b).mp (by
              have := (by simpa [hl] using hord.1 :
                [adaptedCoordinateXFactor L a, adaptedCoordinateXFactor L b].Pairwise (.≤.))
              simpa using this)
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            rw [R.leftLeftXX_secondRow_yyCoefficient_zero a b h hab k l]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXsplit
            obtain ⟨b, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
            have hbad := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateYFactor L h) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L b) [] (by rw [hr])
            exact (adaptedCoordinateYFactor_not_le_x h b hbad).elim
          · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXright
            obtain ⟨a, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hbad := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateYFactor L h) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L a)
                [y] (by rw [hr])
            exact (adaptedCoordinateYFactor_not_le_x h a hbad).elim
      · rcases p with ⟨left, relation, right⟩
        simp only at hrel
        subst relation
        rw [R.highRow_packet_yyCoefficient_zero row (by omega) left right k l]
        have hx (i : I) : row ≠ adaptedCoordinateXFactor L i := by
          intro heq
          rw [heq, adaptedCoordinateXFactor_weight] at hrowthree
          omega
        have hy (h : K) : row ≠ adaptedCoordinateYFactor L h := by
          intro heq
          rw [heq, adaptedCoordinateYFactor_weight] at hrowthree
          omega
        simp [IsAdaptedRowPacket, hx, hy]
      · rcases p with ⟨left, relation, right⟩
        simp only at hrel
        subst relation
        rw [R.highRow_packet_yyCoefficient_zero row (by omega) left right k l]
        have hx (i : I) : row ≠ adaptedCoordinateXFactor L i := by
          intro heq
          rw [heq, adaptedCoordinateXFactor_weight] at hrowfour
          omega
        have hy (h : K) : row ≠ adaptedCoordinateYFactor L h := by
          intro heq
          rw [heq, adaptedCoordinateYFactor_weight] at hrowfour
          omega
        simp [IsAdaptedRowPacket, hx, hy]

private theorem terminalPacket_xxCoefficient
    (R : StandingReductionData L)
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    (a b : I) (p : AdaptedSmithPlacedPacket L L ev)
    (hp : p ∈ w.terminalPackets.support) :
    adaptedPBWCoefficient L L ev (xxExponent (L := L) a b) (p.value L L ev) =
      (∑ i : I, ∑ j : I,
        if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [adaptedCoordinateXFactor L j] [] p then
          if xExponent (L := L) j + xExponent (L := L) i =
              xxExponent (L := L) a b
            then (R.coordinateD i : ℤ) else 0
        else 0) +
      (∑ i : I, ∑ j : I,
        if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [] [adaptedCoordinateXFactor L j] p then
          if xExponent (L := L) j + xExponent (L := L) i =
              xxExponent (L := L) a b
            then (R.coordinateD i : ℤ) else 0
        else 0) := by
  classical
  by_cases hhigh : 2 < p.totalWeight L
  · have hcoeff := adaptedPBWCoefficient_packet_eq_zero_of_lt L L ev p
      (xxExponent (L := L) a b) (by simpa using hhigh)
    rw [hcoeff]
    have hleft (i j : I) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateXFactor L i) [adaptedCoordinateXFactor L j] [] p := by
      rintro ⟨hl, hrel, hr⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr] at hhigh
      simpa [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] using hhigh
    have hright (i j : I) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateXFactor L i) [] [adaptedCoordinateXFactor L j] p := by
      rintro ⟨hl, hrel, hr⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr] at hhigh
      simpa [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] using hhigh
    simp [hleft, hright]
  · have hle : p.totalWeight L ≤ 2 := Nat.le_of_not_gt hhigh
    have hterminal := w.terminalPackets_terminal p hp
    cases hrel : p.relation with
    | high r hr =>
        exfalso
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
        simp [AdaptedCollectedRelation.weight] at hle
        omega
    | row row =>
      have hrowle : adaptedLowBasisWeight L row ≤ 2 := by
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
        simp only [AdaptedCollectedRelation.weight,
          adaptedLowRelationRowWeight] at hle
        omega
      have hrowpos := adaptedLowBasisWeight_pos L row
      rcases (show adaptedLowBasisWeight L row = 1 ∨
          adaptedLowBasisWeight L row = 2 by omega) with hrowone | hrowtwo
      · obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L row hrowone
        have hextle : p.externalWeight L ≤ 1 := by
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp only [AdaptedCollectedRelation.weight,
            adaptedLowRelationRowWeight, adaptedCoordinateXFactor_weight] at hle
          omega
        rcases Nat.eq_zero_or_pos (p.externalWeight L) with hextzero | hextpos
        · obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hextzero
          rcases p with ⟨left, relation, right⟩
          simp only at hl hr hrel
          subst left
          subst relation
          subst right
          rw [scalarFirstRow_xxCoefficient R i a b]
          simp [IsAdaptedRowPacket]
        · have hextone : p.externalWeight L = 1 := by omega
          rcases p.externalWeight_eq_one_iff.mp hextone with hleft | hright
          · obtain ⟨x, hl, hr, hx⟩ := hleft
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hjiLow := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [] (adaptedCoordinateXFactor L j) (by rw [hl]; rfl)
            have hji : j ≤ i := by
              change toLex ((0 : ℕ), j.1) ≤ toLex ((0 : ℕ), i.1) at hjiLow
              rcases Prod.Lex.toLex_le_toLex.mp hjiLow with hbad | hsame
              · omega
              · exact hsame.2
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left
            subst relation
            subst right
            rw [leftX_firstRow_xxCoefficient R i j hji a b]
            simp only [IsAdaptedRowPacket, List.cons.injEq, and_true,
              AdaptedCollectedRelation.row.injEq,
              adaptedCoordinateXFactor_inj_iff, List.nil_eq]
            rw [Finset.sum_eq_single i]
            · rw [Finset.sum_eq_single j]
              · simp
              · intro x hx hxj
                simp [Ne.symm hxj]
              · simp
            · intro x hx hxi
              simp [Ne.symm hxi]
            · simp
          · obtain ⟨x, hl, hr, hx⟩ := hright
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hijLow := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L j) [] (by simp [hr])
            have hij : i ≤ j := by
              change toLex ((0 : ℕ), i.1) ≤ toLex ((0 : ℕ), j.1) at hijLow
              rcases Prod.Lex.toLex_le_toLex.mp hijLow with hbad | hsame
              · omega
              · exact hsame.2
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left
            subst relation
            subst right
            rw [rightX_firstRow_xxCoefficient R i j hij a b]
            simp only [IsAdaptedRowPacket, List.cons.injEq, and_true,
              AdaptedCollectedRelation.row.injEq,
              adaptedCoordinateXFactor_inj_iff, List.nil_eq]
            rw [Finset.sum_eq_single i]
            · rw [Finset.sum_eq_single j]
              · simp
              · intro x hx hxj
                simp [Ne.symm hxj]
              · simp
            · intro x hx hxi
              simp [Ne.symm hxi]
            · simp
      · obtain ⟨k, rfl⟩ := exists_eq_adaptedCoordinateYFactor L row hrowtwo
        have hext : p.externalWeight L = 0 := by
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp only [AdaptedCollectedRelation.weight,
            adaptedLowRelationRowWeight, adaptedCoordinateYFactor_weight] at hle
          omega
        obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hext
        rcases p with ⟨left, relation, right⟩
        simp only at hl hr hrel
        subst left
        subst relation
        subst right
        rw [scalarSecondRow_xxCoefficient R k a b]
        simp [IsAdaptedRowPacket]

private theorem terminalPacket_yCoefficient
    (R : StandingReductionData L)
    {a : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a)
    (k : K) (p : AdaptedSmithPlacedPacket L L ev)
    (hp : p ∈ w.terminalPackets.support) :
    adaptedPBWCoefficient L L ev (yExponent (L := L) k) (p.value L L ev) =
      (∑ i : I, if IsAdaptedRowPacket L L ev
          (adaptedCoordinateXFactor L i) [] [] p
        then -R.coordinateB i k else 0) +
      (if IsAdaptedRowPacket L L ev
          (adaptedCoordinateYFactor L k) [] [] p
        then (R.coordinateE k : ℤ) else 0) := by
  classical
  by_cases hhigh : 2 < p.totalWeight L
  · have hcoeff := adaptedPBWCoefficient_packet_eq_zero_of_lt L L ev p
      (yExponent (L := L) k) (by simpa using hhigh)
    rw [hcoeff]
    have hshapeX (i : I) : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateXFactor L i) [] [] p := by
      rintro ⟨hl, hrel, hr⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr] at hhigh
      simpa [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] using hhigh
    have hshapeY : ¬IsAdaptedRowPacket L L ev
        (adaptedCoordinateYFactor L k) [] [] p := by
      rintro ⟨hl, hrel, hr⟩
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr] at hhigh
      simpa [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] using hhigh
    simp [hshapeX, hshapeY]
  · have hle : p.totalWeight L ≤ 2 := Nat.le_of_not_gt hhigh
    have hterminal := w.terminalPackets_terminal p hp
    cases hrel : p.relation with
    | high r hr =>
        exfalso
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
        simp [AdaptedCollectedRelation.weight] at hle
        omega
    | row row =>
      have hrowle : adaptedLowBasisWeight L row ≤ 2 := by
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
        simp only [AdaptedCollectedRelation.weight,
          adaptedLowRelationRowWeight] at hle
        omega
      have hrowpos := adaptedLowBasisWeight_pos L row
      rcases (show adaptedLowBasisWeight L row = 1 ∨
          adaptedLowBasisWeight L row = 2 by omega) with hrowone | hrowtwo
      · obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L row hrowone
        have hextle : p.externalWeight L ≤ 1 := by
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp only [AdaptedCollectedRelation.weight,
            adaptedLowRelationRowWeight, adaptedCoordinateXFactor_weight] at hle
          omega
        rcases Nat.eq_zero_or_pos (p.externalWeight L) with hextzero | hextpos
        · obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hextzero
          rcases p with ⟨left, relation, right⟩
          simp only at hl hr hrel
          subst left
          subst relation
          subst right
          rw [scalarFirstRow_yCoefficient (R := R) i k]
          simp [IsAdaptedRowPacket]
        · have hextone : p.externalWeight L = 1 := by omega
          rcases p.externalWeight_eq_one_iff.mp hextone with hleft | hright
          · obtain ⟨x, hl, hr, hx⟩ := hleft
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hjiLow := adaptedPlacedPacket_terminal_last_le_head
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal [] (adaptedCoordinateXFactor L j) (by
                rw [hl]
                rfl)
            have hji : j ≤ i := by
              change toLex ((0 : ℕ), j.1) ≤ toLex ((0 : ℕ), i.1) at hjiLow
              rcases Prod.Lex.toLex_le_toLex.mp hjiLow with hbad | hsame
              · omega
              · exact hsame.2
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left
            subst relation
            subst right
            rw [leftX_firstRow_yCoefficient R i j hji k]
            simp [IsAdaptedRowPacket]
          · obtain ⟨x, hl, hr, hx⟩ := hright
            obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
            have hijLow := adaptedPlacedPacket_terminal_head_le_first
              L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
              hterminal (adaptedCoordinateXFactor L j) [] (by simp [hr])
            have hij : i ≤ j := by
              change toLex ((0 : ℕ), i.1) ≤ toLex ((0 : ℕ), j.1) at hijLow
              rcases Prod.Lex.toLex_le_toLex.mp hijLow with hbad | hsame
              · omega
              · exact hsame.2
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left
            subst relation
            subst right
            rw [rightX_firstRow_yCoefficient R i j hij k]
            simp [IsAdaptedRowPacket]
      · obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateYFactor L row hrowtwo
        have hext : p.externalWeight L = 0 := by
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp only [AdaptedCollectedRelation.weight,
            adaptedLowRelationRowWeight, adaptedCoordinateYFactor_weight] at hle
          omega
        obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hext
        rcases p with ⟨left, relation, right⟩
        simp only at hl hr hrel
        subst left
        subst relation
        subst right
        rw [scalarSecondRow_yCoefficient (R := R) k l]
        by_cases hkl : k = l
        · subst l
          simp [IsAdaptedRowPacket]
        · have hlk : l ≠ k := Ne.symm hkl
          simp [IsAdaptedRowPacket, hkl, hlk]

private theorem terminalPacket_xxDiagCoefficient
    (R : StandingReductionData L)
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    (a : I) (p : AdaptedSmithPlacedPacket L L ev)
    (hp : p ∈ w.terminalPackets.support) :
    adaptedPBWCoefficient L L ev (xxExponent (L := L) a a) (p.value L L ev) =
      (if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
          [adaptedCoordinateXFactor L a] [] p
        then (R.coordinateD a : ℤ) else 0) +
      (if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
          [] [adaptedCoordinateXFactor L a] p
        then (R.coordinateD a : ℤ) else 0) := by
  classical
  rw [terminalPacket_xxCoefficient R w a a p hp]
  simp_rw [xExponent_add_eq_diag_iff (L := L)]
  apply congrArg₂ (.+.)
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · simp [IsAdaptedRowPacket]
      · intro x hx hxa
        simp [hxa]
      · simp
    · intro x hx hxa
      simp [hxa]
    · simp
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · simp [IsAdaptedRowPacket]
      · intro x hx hxa
        simp [hxa]
      · simp
    · intro x hx hxa
      simp [hxa]
    · simp

private theorem terminalPacket_xxOffdiagCoefficient
    (R : StandingReductionData L)
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    (a b : I) (hab : a < b) (p : AdaptedSmithPlacedPacket L L ev)
    (hp : p ∈ w.terminalPackets.support) :
    adaptedPBWCoefficient L L ev (xxExponent (L := L) a b) (p.value L L ev) =
      (if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L b)
          [adaptedCoordinateXFactor L a] [] p
        then (R.coordinateD b : ℤ) else 0) +
      (if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
          [] [adaptedCoordinateXFactor L b] p
        then (R.coordinateD a : ℤ) else 0) := by
  classical
  rw [terminalPacket_xxCoefficient R w a b p hp]
  have hterminal := w.terminalPackets_terminal p hp
  have hleftCond (i j : I)
      (hs : IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
        [adaptedCoordinateXFactor L j] [] p) :
      xExponent (L := L) j + xExponent (L := L) i = xxExponent (L := L) a b ↔
        i = b ∧ j = a := by
    rcases hs with ⟨hl, hrel, hr⟩
    have hjiLow := adaptedPlacedPacket_terminal_last_le_head
      L L ev p (adaptedCoordinateXFactor L i) hrel (by
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
          AdaptedSmithPlacedPacket.externalWeight, hl, hr]
        simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight,
          adaptedCoordinateXFactor_weight]) hterminal []
        (adaptedCoordinateXFactor L j) (by rw [hl]; rfl)
    have hji : j ≤ i := by
      change toLex ((0 : ℕ), j.1) ≤ toLex ((0 : ℕ), i.1) at hjiLow
      rcases Prod.Lex.toLex_le_toLex.mp hjiLow with hbad | hsame
      · omega
      · exact hsame.2
    constructor
    · intro h
      have hij := xExponent_add_eq_offdiag_of_le (L := L) hji hab h
      exact ⟨hij.2, hij.1⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hrightCond (i j : I)
      (hs : IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
        [] [adaptedCoordinateXFactor L j] p) :
      xExponent (L := L) j + xExponent (L := L) i = xxExponent (L := L) a b ↔
        i = a ∧ j = b := by
    rcases hs with ⟨hl, hrel, hr⟩
    have hijLow := adaptedPlacedPacket_terminal_head_le_first
      L L ev p (adaptedCoordinateXFactor L i) hrel (by
        rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
          AdaptedSmithPlacedPacket.externalWeight, hl, hr]
        simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight,
          adaptedCoordinateXFactor_weight]) hterminal
        (adaptedCoordinateXFactor L j) [] (by simp [hr])
    have hij : i ≤ j := by
      change toLex ((0 : ℕ), i.1) ≤ toLex ((0 : ℕ), j.1) at hijLow
      rcases Prod.Lex.toLex_le_toLex.mp hijLow with hbad | hsame
      · omega
      · exact hsame.2
    constructor
    · intro h
      have h' : xExponent (L := L) i + xExponent (L := L) j =
          xxExponent (L := L) a b := by simpa [add_comm] using h
      exact xExponent_add_eq_offdiag_of_le (L := L) hij hab h'
    · rintro ⟨rfl, rfl⟩
      simp [xxExponent, add_comm]
  have hleftTerm (i j : I) :
      (if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [adaptedCoordinateXFactor L j] [] p then
          if xExponent (L := L) j + xExponent (L := L) i =
              xxExponent (L := L) a b
            then (R.coordinateD i : ℤ) else 0
        else 0) =
      if i = b ∧ j = a ∧ IsAdaptedRowPacket L L ev
          (adaptedCoordinateXFactor L b) [adaptedCoordinateXFactor L a] [] p
        then (R.coordinateD b : ℤ) else 0 := by
    by_cases hs : IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
        [adaptedCoordinateXFactor L j] [] p
    · rw [if_pos hs]
      by_cases heq : xExponent (L := L) j + xExponent (L := L) i =
          xxExponent (L := L) a b
      · rw [if_pos heq]
        rcases (hleftCond i j hs).mp heq with ⟨rfl, rfl⟩
        simp [hs]
      · rw [if_neg heq]
        split
        · rename_i h
          rcases h with ⟨rfl, rfl, hs'⟩
          exact (heq rfl).elim
        · rfl
    · rw [if_neg hs]
      split
      · rename_i h
        rcases h with ⟨rfl, rfl, hs'⟩
        exact (hs hs').elim
      · rfl
  have hrightTerm (i j : I) :
      (if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [] [adaptedCoordinateXFactor L j] p then
          if xExponent (L := L) j + xExponent (L := L) i =
              xxExponent (L := L) a b
            then (R.coordinateD i : ℤ) else 0
        else 0) =
      if i = a ∧ j = b ∧ IsAdaptedRowPacket L L ev
          (adaptedCoordinateXFactor L a) [] [adaptedCoordinateXFactor L b] p
        then (R.coordinateD a : ℤ) else 0 := by
    by_cases hs : IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
        [] [adaptedCoordinateXFactor L j] p
    · rw [if_pos hs]
      by_cases heq : xExponent (L := L) j + xExponent (L := L) i =
          xxExponent (L := L) a b
      · rw [if_pos heq]
        rcases (hrightCond i j hs).mp heq with ⟨rfl, rfl⟩
        simp [hs]
      · rw [if_neg heq]
        split
        · rename_i h
          rcases h with ⟨rfl, rfl, hs'⟩
          exact (heq (by simp [xxExponent, add_comm])).elim
        · rfl
    · rw [if_neg hs]
      split
      · rename_i h
        rcases h with ⟨rfl, rfl, hs'⟩
        exact (hs hs').elim
      · rfl
  simp_rw [hleftTerm, hrightTerm]
  apply congrArg₂ (.+.)
  · rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single a]
      · simp
      · intro j _ hja
        simp [hja]
      · simp
    · intro i _ hib
      apply Finset.sum_eq_zero
      intro j _
      simp [hib]
    · simp
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro j _ hjb
        simp [hjb]
      · simp
    · intro i _ hia
      apply Finset.sum_eq_zero
      intro j _
      simp [hia]
    · simp

private theorem terminalPacket_xCoefficient
    {a : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a)
    (i : I) (p : AdaptedSmithPlacedPacket L L ev)
    (hp : p ∈ w.terminalPackets.support) :
    (IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i) [] [] p →
      adaptedPBWCoefficient L L ev (xExponent (L := L) i) (p.value L L ev) =
        (R.coordinateD i : ℤ)) ∧
    (¬IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i) [] [] p →
      adaptedPBWCoefficient L L ev (xExponent (L := L) i) (p.value L L ev) = 0) := by
  classical
  constructor
  · intro hshape
    rcases hshape with ⟨hl, hrel, hr⟩
    rcases p with ⟨left, relation, right⟩
    simp only at hl hrel hr
    subst left
    subst relation
    subst right
    simpa using R.scalarFirstRow_xCoefficient i i
  · intro hshape
    by_cases hhigh : 1 < p.totalWeight L
    · exact adaptedPBWCoefficient_packet_eq_zero_of_lt L L ev p
        (xExponent (L := L) i) (by simpa using hhigh)
    · have hle : p.totalWeight L ≤ 1 := Nat.le_of_not_gt hhigh
      cases hrel : p.relation with
      | high r hr =>
          exfalso
          rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
          simp [AdaptedCollectedRelation.weight] at hle
          omega
      | row j =>
          have hjpos := adaptedLowBasisWeight_pos L j
          have hext : p.externalWeight L = 0 := by
            rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
            simp only [AdaptedCollectedRelation.weight,
              adaptedLowRelationRowWeight] at hle
            omega
          have hjweight : adaptedLowBasisWeight L j = 1 := by
            rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
            simp only [AdaptedCollectedRelation.weight,
              adaptedLowRelationRowWeight] at hle hjpos
            omega
          obtain ⟨j', rfl⟩ := exists_eq_adaptedCoordinateXFactor L j hjweight
          have hfactors := p.externalWeight_eq_zero_iff.mp hext
          by_cases hij : i = j'
          · subst j'
            exact (hshape ⟨hfactors.1, hrel, hfactors.2⟩).elim
          · rcases p with ⟨left, relation, right⟩
            rcases hfactors with ⟨hl, hr⟩
            simp only at hl hr hrel
            subst left
            subst relation
            subst right
            simpa [hij] using R.scalarFirstRow_xCoefficient i j'

/-- The semantic `x_i` projection is exactly `d_i` times the scalar `r_i` packet
coefficient. -/
theorem terminalPackets_xProjection
    {a : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a) (i : I) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (xExponent (L := L) i) (p.value L L ev)) =
      (R.coordinateD i : ℤ) *
        AdaptedTerminalCoordinates.r L L ev w.terminalPackets i := by
  classical
  unfold AdaptedTerminalCoordinates.r adaptedLedgerRowCoefficient
  calc
    _ = w.terminalPackets.sum (fun p n ↦
        if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i) [] [] p
        then n * (R.coordinateD i : ℤ) else 0) := by
      apply Finsupp.sum_congr
      intro p hp
      by_cases hshape : IsAdaptedRowPacket L L ev
          (adaptedCoordinateXFactor L i) [] [] p
      · rw [(terminalPacket_xCoefficient (R := R) w i p hp).1 hshape,
          if_pos hshape]
        simp [smul_eq_mul]
      · rw [(terminalPacket_xCoefficient (R := R) w i p hp).2 hshape,
          if_neg hshape]
        simp
    _ = _ := by
      rw [Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro p hp
      by_cases hshape : IsAdaptedRowPacket L L ev
          (adaptedCoordinateXFactor L i) [] [] p
      · simp [hshape]
        ring
      · simp [hshape]

/-- The actual terminal `y_k` coefficient is the scalar-row expression
`-∑ᵢ Bᵢₖ rᵢ + eₖ sₖ`. -/
theorem terminalPackets_yProjection
    {a : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a) (k : K) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (yExponent (L := L) k) (p.value L L ev)) =
      -(∑ i : I, AdaptedTerminalCoordinates.r L L ev w.terminalPackets i *
          R.coordinateB i k) +
        (R.coordinateE k : ℤ) *
          AdaptedTerminalCoordinates.s L L ev w.terminalPackets k := by
  classical
  calc
    _ = w.terminalPackets.sum (fun p n ↦ n *
        ((∑ i : I, if IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L i) [] [] p
          then -R.coordinateB i k else 0) +
        (if IsAdaptedRowPacket L L ev
            (adaptedCoordinateYFactor L k) [] [] p
          then (R.coordinateE k : ℤ) else 0))) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [terminalPacket_yCoefficient R w k p hp]
      rfl
    _ = _ := by
      unfold AdaptedTerminalCoordinates.r AdaptedTerminalCoordinates.s
        adaptedLedgerRowCoefficient Finsupp.sum
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      apply congrArg₂ (.+.)
      · rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∑ p ∈ w.terminalPackets.support,
              -((if IsAdaptedRowPacket L L ev
                  (adaptedCoordinateXFactor L i) [] [] p
                then w.terminalPackets p else 0) * R.coordinateB i k) := by
                apply Finset.sum_congr rfl
                intro p hp
                by_cases hshape : IsAdaptedRowPacket L L ev
                    (adaptedCoordinateXFactor L i) [] [] p
                · simp [hshape]
                · simp [hshape]
          _ = -((∑ p ∈ w.terminalPackets.support,
                if IsAdaptedRowPacket L L ev
                    (adaptedCoordinateXFactor L i) [] [] p
                  then w.terminalPackets p else 0) * R.coordinateB i k) := by
                rw [Finset.sum_neg_distrib, Finset.sum_mul]
      · apply Finset.sum_congr rfl
        intro p hp
        by_cases hshape : IsAdaptedRowPacket L L ev
            (adaptedCoordinateYFactor L k) [] [] p
        · simp [hshape]
          ring
        · simp [hshape]

/-- Diagonal two-`x` projection, giving the `rxx` coefficient. -/
theorem terminalPackets_xxDiagProjection
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (a : I) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (xxExponent (L := L) a a) (p.value L L ev)) =
      (R.coordinateD a : ℤ) *
        AdaptedTerminalCoordinates.rxx L L ev w.terminalPackets a := by
  classical
  calc
    _ = w.terminalPackets.sum (fun p n ↦ n *
        ((if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
            [] [adaptedCoordinateXFactor L a] p
          then (R.coordinateD a : ℤ) else 0) +
        (if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
            [adaptedCoordinateXFactor L a] [] p
          then (R.coordinateD a : ℤ) else 0))) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [terminalPacket_xxDiagCoefficient R w a p hp]
      ring
    _ = _ := by
      unfold AdaptedTerminalCoordinates.rxx adaptedLedgerRowCoefficient Finsupp.sum
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (.+.)
      · apply Finset.sum_congr rfl
        intro p hp
        by_cases hshape : IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L a) [] [adaptedCoordinateXFactor L a] p
        · simp [hshape]
          ring
        · simp [hshape]
      · apply Finset.sum_congr rfl
        intro p hp
        by_cases hshape : IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L a) [adaptedCoordinateXFactor L a] [] p
        · simp [hshape]
          ring
        · simp [hshape]

/-- Off-diagonal two-`x` projection.  Terminal ordering leaves exactly the
placements `r_a x_b` and `x_a r_b`. -/
theorem terminalPackets_xxOffdiagProjection
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    {a b : I} (hab : a < b) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (xxExponent (L := L) a b) (p.value L L ev)) =
      (R.coordinateD a : ℤ) *
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets a b +
        (R.coordinateD b : ℤ) *
          AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a b := by
  classical
  calc
    _ = w.terminalPackets.sum (fun p n ↦ n *
        ((if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
            [] [adaptedCoordinateXFactor L b] p
          then (R.coordinateD a : ℤ) else 0) +
        (if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L b)
            [adaptedCoordinateXFactor L a] [] p
          then (R.coordinateD b : ℤ) else 0))) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [terminalPacket_xxOffdiagCoefficient R w a b hab p hp]
      simp [smul_eq_mul, add_comm]
    _ = _ := by
      unfold AdaptedTerminalCoordinates.rx AdaptedTerminalCoordinates.xr
        adaptedLedgerRowCoefficient Finsupp.sum
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (.+.)
      · apply Finset.sum_congr rfl
        intro p hp
        by_cases hshape : IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L a) [] [adaptedCoordinateXFactor L b] p
        · simp [hshape]
          ring
        · simp [hshape]
      · apply Finset.sum_congr rfl
        intro p hp
        by_cases hshape : IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L b) [adaptedCoordinateXFactor L a] [] p
        · simp [hshape]
          ring
        · simp [hshape]

/-- The semantic `x_a y_k` coefficient, before restricting the ordered two-factor
placements to the upper triangle. -/
theorem terminalPackets_xyProjection
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    (a : I) (k : K) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (xyExponent (L := L) a k) (p.value L L ev)) =
      -(∑ i : I,
          (adaptedLedgerRowCoefficient L L ev w.terminalPackets
              (adaptedCoordinateXFactor L i) [adaptedCoordinateXFactor L a] [] +
            adaptedLedgerRowCoefficient L L ev w.terminalPackets
              (adaptedCoordinateXFactor L i) [] [adaptedCoordinateXFactor L a]) *
            R.coordinateB i k) +
        (R.coordinateD a : ℤ) *
          AdaptedTerminalCoordinates.v L L ev w.terminalPackets a k +
        AdaptedTerminalCoordinates.v' L L ev w.terminalPackets a k *
          (R.coordinateE k : ℤ) := by
  classical
  rw [show w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (xyExponent (L := L) a k) (p.value L L ev)) =
      w.terminalPackets.sum (fun p n ↦ n *
        (((∑ i : I, ∑ j : I,
            if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
                [adaptedCoordinateXFactor L j] [] p
              then if j = a then -R.coordinateB i k else 0 else 0) +
          (∑ i : I, ∑ j : I,
            if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
                [] [adaptedCoordinateXFactor L j] p
              then if j = a then -R.coordinateB i k else 0 else 0)) +
        ((∑ i : I, ∑ l : K,
            if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
                [] [adaptedCoordinateYFactor L l] p
              then if i = a ∧ l = k then (R.coordinateD i : ℤ) else 0 else 0) +
          (∑ i : I, ∑ l : K,
            if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L l)
                [adaptedCoordinateXFactor L i] [] p
              then if i = a ∧ l = k then (R.coordinateE l : ℤ) else 0 else 0)))) by
    apply Finsupp.sum_congr
    intro p hp
    rw [terminalPacket_xyCoefficient R w a k p hp]
    rfl]
  have hLX (p : AdaptedSmithPlacedPacket L L ev) :
      (∑ i : I, ∑ j : I,
        if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [adaptedCoordinateXFactor L j] [] p
          then if j = a then -R.coordinateB i k else 0 else 0) =
      ∑ i : I, if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
          [adaptedCoordinateXFactor L a] [] p then -R.coordinateB i k else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single a]
    · simp
    · intro j _ hja
      simp [hja]
    · simp
  have hRX (p : AdaptedSmithPlacedPacket L L ev) :
      (∑ i : I, ∑ j : I,
        if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [] [adaptedCoordinateXFactor L j] p
          then if j = a then -R.coordinateB i k else 0 else 0) =
      ∑ i : I, if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
          [] [adaptedCoordinateXFactor L a] p then -R.coordinateB i k else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single a]
    · simp
    · intro j _ hja
      simp [hja]
    · simp
  have hRY (p : AdaptedSmithPlacedPacket L L ev) :
      (∑ i : I, ∑ l : K,
        if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [] [adaptedCoordinateYFactor L l] p
          then if i = a ∧ l = k then (R.coordinateD i : ℤ) else 0 else 0) =
      if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
          [] [adaptedCoordinateYFactor L k] p then (R.coordinateD a : ℤ) else 0 := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hlk
        simp [hlk]
      · simp
    · intro i _ hia
      apply Finset.sum_eq_zero
      intro l _
      simp [hia]
    · simp
  have hLY (p : AdaptedSmithPlacedPacket L L ev) :
      (∑ i : I, ∑ l : K,
        if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L l)
            [adaptedCoordinateXFactor L i] [] p
          then if i = a ∧ l = k then (R.coordinateE l : ℤ) else 0 else 0) =
      if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k)
          [adaptedCoordinateXFactor L a] [] p then (R.coordinateE k : ℤ) else 0 := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hlk
        simp [hlk]
      · simp
    · intro i _ hia
      apply Finset.sum_eq_zero
      intro l _
      simp [hia]
    · simp
  simp_rw [hLX, hRX, hRY, hLY]
  unfold adaptedLedgerRowCoefficient AdaptedTerminalCoordinates.v
    AdaptedTerminalCoordinates.v' Finsupp.sum
  simp only [mul_add, Finset.sum_add_distrib]
  have hleft :
      (∑ p ∈ w.terminalPackets.support, w.terminalPackets p *
        ∑ i : I, if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [adaptedCoordinateXFactor L a] [] p then -R.coordinateB i k else 0) =
      -∑ i : I, (∑ p ∈ w.terminalPackets.support,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [adaptedCoordinateXFactor L a] [] p
            then w.terminalPackets p else 0) * R.coordinateB i k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ i : I, ∑ p ∈ w.terminalPackets.support, w.terminalPackets p *
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [adaptedCoordinateXFactor L a] [] p then -R.coordinateB i k else 0) =
        ∑ i : I, -((∑ p ∈ w.terminalPackets.support,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [adaptedCoordinateXFactor L a] [] p then w.terminalPackets p else 0) *
            R.coordinateB i k) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
          rw [← Finset.sum_neg_distrib (s := w.terminalPackets.support)]
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hshape : IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L i) [adaptedCoordinateXFactor L a] [] p <;>
            simp [hshape]
      _ = -∑ i : I, (∑ p ∈ w.terminalPackets.support,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [adaptedCoordinateXFactor L a] [] p then w.terminalPackets p else 0) *
            R.coordinateB i k := by rw [Finset.sum_neg_distrib]
  have hright :
      (∑ p ∈ w.terminalPackets.support, w.terminalPackets p *
        ∑ i : I, if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
            [] [adaptedCoordinateXFactor L a] p then -R.coordinateB i k else 0) =
      -∑ i : I, (∑ p ∈ w.terminalPackets.support,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [] [adaptedCoordinateXFactor L a] p
            then w.terminalPackets p else 0) * R.coordinateB i k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ i : I, ∑ p ∈ w.terminalPackets.support, w.terminalPackets p *
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [] [adaptedCoordinateXFactor L a] p then -R.coordinateB i k else 0) =
        ∑ i : I, -((∑ p ∈ w.terminalPackets.support,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [] [adaptedCoordinateXFactor L a] p then w.terminalPackets p else 0) *
            R.coordinateB i k) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
          rw [← Finset.sum_neg_distrib (s := w.terminalPackets.support)]
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hshape : IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L i) [] [adaptedCoordinateXFactor L a] p <;>
            simp [hshape]
      _ = -∑ i : I, (∑ p ∈ w.terminalPackets.support,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [] [adaptedCoordinateXFactor L a] p then w.terminalPackets p else 0) *
            R.coordinateB i k := by rw [Finset.sum_neg_distrib]
  have hv :
      (∑ p ∈ w.terminalPackets.support, w.terminalPackets p *
        if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
            [] [adaptedCoordinateYFactor L k] p then (R.coordinateD a : ℤ) else 0) =
      (R.coordinateD a : ℤ) *
        ∑ p ∈ w.terminalPackets.support,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
              [] [adaptedCoordinateYFactor L k] p then w.terminalPackets p else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hshape : IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L a)
        [] [adaptedCoordinateYFactor L k] p <;> simp [hshape, mul_comm]
  have hv' :
      (∑ p ∈ w.terminalPackets.support, w.terminalPackets p *
        if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k)
            [adaptedCoordinateXFactor L a] [] p then (R.coordinateE k : ℤ) else 0) =
      (∑ p ∈ w.terminalPackets.support,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k)
              [adaptedCoordinateXFactor L a] [] p then w.terminalPackets p else 0) *
        (R.coordinateE k : ℤ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hshape : IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k)
        [adaptedCoordinateXFactor L a] [] p <;> simp [hshape]
  rw [hleft, hright, hv, hv']
  simp only [adaptedLedgerRowCoefficient, Finsupp.sum]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring

/-- The pure-`yy` projection of the terminal ledger, in its literal indicator form.
This is the finite sum of precisely the three packet shapes retained by
`terminalPacket_yyCoefficient`; no coordinate equation is assumed here. -/
theorem terminalPackets_yyProjection
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    (k l : K) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (yyExponent (L := L) k l) (p.value L L ev)) =
      (∑ i : I, ∑ b : K,
        AdaptedTerminalCoordinates.v L L ev w.terminalPackets i b *
          (-∑ h : K, if yExponent (L := L) h + yExponent (L := L) b =
              yyExponent (L := L) k l then R.coordinateB i h else 0)) +
      (∑ h : K, ∑ b : K,
        AdaptedTerminalCoordinates.sY L L ev w.terminalPackets h b *
          (if yExponent (L := L) h + yExponent (L := L) b =
              yyExponent (L := L) k l then (R.coordinateE h : ℤ) else 0)) +
      (∑ b : K, ∑ h : K,
        AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets b h *
          (if yExponent (L := L) b + yExponent (L := L) h =
              yyExponent (L := L) k l then (R.coordinateE h : ℤ) else 0)) := by
  classical
  rw [show w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (yyExponent (L := L) k l) (p.value L L ev)) =
      w.terminalPackets.sum (fun p n ↦ n *
        ((∑ i : I, ∑ b : K,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [] [adaptedCoordinateYFactor L b] p then
            -∑ h : K, if yExponent (L := L) h + yExponent (L := L) b =
                yyExponent (L := L) k l then R.coordinateB i h else 0
          else 0) +
        (∑ h : K, ∑ b : K,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L h)
              [] [adaptedCoordinateYFactor L b] p then
            if yExponent (L := L) h + yExponent (L := L) b =
                yyExponent (L := L) k l then (R.coordinateE h : ℤ) else 0
          else 0) +
        (∑ b : K, ∑ h : K,
          if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L h)
              [adaptedCoordinateYFactor L b] [] p then
            if yExponent (L := L) b + yExponent (L := L) h =
                yyExponent (L := L) k l then (R.coordinateE h : ℤ) else 0
          else 0))) by
    apply Finsupp.sum_congr
    intro p hp
    rw [terminalPacket_yyCoefficient R w k l p hp]
    simp [smul_eq_mul]]
  unfold AdaptedTerminalCoordinates.v AdaptedTerminalCoordinates.sY
    AdaptedTerminalCoordinates.Ys adaptedLedgerRowCoefficient Finsupp.sum
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := w.terminalPackets.support)]
  apply congrArg₂ (.+.)
  · apply congrArg₂ (.+.)
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hshape : IsAdaptedRowPacket L L ev
          (adaptedCoordinateXFactor L i) [] [adaptedCoordinateYFactor L b] p <;>
        simp [hshape]
    · apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hshape : IsAdaptedRowPacket L L ev
          (adaptedCoordinateYFactor L h) [] [adaptedCoordinateYFactor L b] p <;>
        simp [hshape]
  · apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hshape : IsAdaptedRowPacket L L ev
        (adaptedCoordinateYFactor L h) [adaptedCoordinateYFactor L b] [] p <;>
      simp [hshape]

/-- A terminal ledger has no left placement `x_a r_i` below the row head. -/
theorem terminalPackets_leftXCoefficient_eq_zero_of_lt
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    {i a : I} (hia : i < a) :
    adaptedLedgerRowCoefficient L L ev w.terminalPackets
      (adaptedCoordinateXFactor L i) [adaptedCoordinateXFactor L a] [] = 0 := by
  classical
  unfold adaptedLedgerRowCoefficient Finsupp.sum
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hshape : IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
      [adaptedCoordinateXFactor L a] [] p
  · rcases hshape with ⟨hl, hrel, hr⟩
    have hterminal := w.terminalPackets_terminal p hp
    have hlow : p.totalWeight L < 5 := by
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr]
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight]
    have hlast : splitLast? p.left =
        some ([], adaptedCoordinateXFactor L a) := by
      rw [hl]
      rfl
    have hai := adaptedPlacedPacket_terminal_last_le_head
      L L ev p (adaptedCoordinateXFactor L i) hrel hlow
      hterminal [] (adaptedCoordinateXFactor L a) hlast
    have hai' : a ≤ i := (adaptedCoordinateXFactor_le_iff a i).mp hai
    exact (not_le_of_gt hia hai').elim
  · simp [hshape]

/-- A terminal ledger has no right placement `r_i x_a` above the row head. -/
theorem terminalPackets_rightXCoefficient_eq_zero_of_lt
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    {i a : I} (hai : a < i) :
    adaptedLedgerRowCoefficient L L ev w.terminalPackets
      (adaptedCoordinateXFactor L i) [] [adaptedCoordinateXFactor L a] = 0 := by
  classical
  unfold adaptedLedgerRowCoefficient Finsupp.sum
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hshape : IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
      [] [adaptedCoordinateXFactor L a] p
  · rcases hshape with ⟨hl, hrel, hr⟩
    have hterminal := w.terminalPackets_terminal p hp
    have hlow : p.totalWeight L < 5 := by
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr]
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight]
    have hia := adaptedPlacedPacket_terminal_head_le_first
      L L ev p (adaptedCoordinateXFactor L i) hrel hlow
      hterminal (adaptedCoordinateXFactor L a) [] (by rw [hr])
    have hia' : i ≤ a := (adaptedCoordinateXFactor_le_iff i a).mp hia
    exact (not_le_of_gt hai hia').elim
  · simp [hshape]

/-- A terminal ledger has no placement `s_l y_k` with the right factor below
the row head. -/
theorem terminalPackets_sYCoefficient_eq_zero_of_lt
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    {k l : K} (hkl : k < l) :
    AdaptedTerminalCoordinates.sY L L ev w.terminalPackets l k = 0 := by
  classical
  unfold AdaptedTerminalCoordinates.sY adaptedLedgerRowCoefficient Finsupp.sum
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hshape : IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L l)
      [] [adaptedCoordinateYFactor L k] p
  · rcases hshape with ⟨hl, hrel, hr⟩
    have hterminal := w.terminalPackets_terminal p hp
    have hlow : p.totalWeight L < 5 := by
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr]
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight]
    have hlk := adaptedPlacedPacket_terminal_head_le_first
      L L ev p (adaptedCoordinateYFactor L l) hrel hlow
      hterminal (adaptedCoordinateYFactor L k) [] (by rw [hr])
    have hlk' : l ≤ k := (adaptedCoordinateYFactor_le_iff l k).mp hlk
    exact (not_le_of_gt hkl hlk').elim
  · simp [hshape]

/-- A terminal ledger has no placement `y_l s_k` with the left factor above
the row head. -/
theorem terminalPackets_YsCoefficient_eq_zero_of_lt
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    {k l : K} (hkl : k < l) :
    AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets l k = 0 := by
  classical
  unfold AdaptedTerminalCoordinates.Ys adaptedLedgerRowCoefficient Finsupp.sum
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hshape : IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k)
      [adaptedCoordinateYFactor L l] [] p
  · rcases hshape with ⟨hl, hrel, hr⟩
    have hterminal := w.terminalPackets_terminal p hp
    have hlow : p.totalWeight L < 5 := by
      rw [AdaptedSmithPlacedPacket.totalWeight, hrel,
        AdaptedSmithPlacedPacket.externalWeight, hl, hr]
      simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight]
    have hlast : splitLast? p.left =
        some ([], adaptedCoordinateYFactor L l) := by
      rw [hl]
      rfl
    have hlk := adaptedPlacedPacket_terminal_last_le_head
      L L ev p (adaptedCoordinateYFactor L k) hrel hlow
      hterminal [] (adaptedCoordinateYFactor L l) hlast
    have hlk' : l ≤ k := (adaptedCoordinateYFactor_le_iff l k).mp hlk
    exact (not_le_of_gt hkl hlk').elim
  · simp [hshape]

/-- Off-diagonal pure-`yy` projection in the ordered coordinate convention. -/
theorem terminalPackets_yyOffdiagProjection
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    {k l : K} (hkl : k < l) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (yyExponent (L := L) k l) (p.value L L ev)) =
      -(∑ i : I, (
          AdaptedTerminalCoordinates.v L L ev w.terminalPackets i k *
              R.coordinateB i l +
            AdaptedTerminalCoordinates.v L L ev w.terminalPackets i l *
              R.coordinateB i k)) +
        (R.coordinateE k : ℤ) *
          AdaptedTerminalCoordinates.sY L L ev w.terminalPackets k l +
        (R.coordinateE l : ℤ) *
          AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets k l := by
  classical
  rw [R.terminalPackets_yyProjection w k l]
  simp_rw [yExponent_add_eq_offdiag_iff (L := L) hkl.ne]
  have hv (i : I) :
      (∑ b : K, AdaptedTerminalCoordinates.v L L ev w.terminalPackets i b *
        (-∑ h : K, if (h = k ∧ b = l) ∨ (h = l ∧ b = k)
          then R.coordinateB i h else 0)) =
        -(AdaptedTerminalCoordinates.v L L ev w.terminalPackets i k *
            R.coordinateB i l +
          AdaptedTerminalCoordinates.v L L ev w.terminalPackets i l *
            R.coordinateB i k) := by
    simp only [mul_neg]
    rw [Finset.sum_neg_distrib]
    congr 1
    simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simpa [add_comm] using sum_sum_offdiag_indicator
      (fun h b ↦ AdaptedTerminalCoordinates.v L L ev w.terminalPackets i b *
        R.coordinateB i h) hkl.ne
  have hsY :
      (∑ h : K, ∑ b : K,
        AdaptedTerminalCoordinates.sY L L ev w.terminalPackets h b *
          (if (h = k ∧ b = l) ∨ (h = l ∧ b = k) then
            (R.coordinateE h : ℤ) else 0)) =
        AdaptedTerminalCoordinates.sY L L ev w.terminalPackets k l *
            (R.coordinateE k : ℤ) +
          AdaptedTerminalCoordinates.sY L L ev w.terminalPackets l k *
            (R.coordinateE l : ℤ) := by
    simp only [mul_ite, mul_zero]
    exact sum_sum_offdiag_indicator
      (fun h b ↦ AdaptedTerminalCoordinates.sY L L ev w.terminalPackets h b *
        (R.coordinateE h : ℤ)) hkl.ne
  have hYs :
      (∑ b : K, ∑ h : K,
        AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets b h *
          (if (b = k ∧ h = l) ∨ (b = l ∧ h = k) then
            (R.coordinateE h : ℤ) else 0)) =
        AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets k l *
            (R.coordinateE l : ℤ) +
          AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets l k *
            (R.coordinateE k : ℤ) := by
    simp only [mul_ite, mul_zero]
    exact sum_sum_offdiag_indicator
      (fun b h ↦ AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets b h *
        (R.coordinateE h : ℤ)) hkl.ne
  simp_rw [hv]
  rw [Finset.sum_neg_distrib]
  rw [hsY, hYs]
  rw [terminalPackets_sYCoefficient_eq_zero_of_lt w hkl,
    terminalPackets_YsCoefficient_eq_zero_of_lt w hkl]
  ring

/-- Diagonal pure-`yy` projection (the `(C2)` coordinate). -/
theorem terminalPackets_ySquareProjection
    {a₀ : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a₀)
    (k : K) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient L L ev (yyExponent (L := L) k k) (p.value L L ev)) =
      -(∑ i : I,
          AdaptedTerminalCoordinates.v L L ev w.terminalPackets i k *
            R.coordinateB i k) +
        (R.coordinateE k : ℤ) *
          (AdaptedTerminalCoordinates.sY L L ev w.terminalPackets k k +
            AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets k k) := by
  classical
  rw [R.terminalPackets_yyProjection w k k]
  simp_rw [yExponent_add_eq_diag_iff (L := L)]
  have hv (i : I) :
      (∑ b : K, AdaptedTerminalCoordinates.v L L ev w.terminalPackets i b *
        (-∑ h : K, if h = k ∧ b = k then R.coordinateB i h else 0)) =
        -(AdaptedTerminalCoordinates.v L L ev w.terminalPackets i k *
          R.coordinateB i k) := by
    simp only [mul_neg]
    rw [Finset.sum_neg_distrib]
    congr 1
    simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    exact sum_sum_diag_indicator
      (fun h b ↦ AdaptedTerminalCoordinates.v L L ev w.terminalPackets i b *
        R.coordinateB i h) k
  have hsY :
      (∑ h : K, ∑ b : K,
        AdaptedTerminalCoordinates.sY L L ev w.terminalPackets h b *
          (if h = k ∧ b = k then (R.coordinateE h : ℤ) else 0)) =
        AdaptedTerminalCoordinates.sY L L ev w.terminalPackets k k *
          (R.coordinateE k : ℤ) := by
    simp only [mul_ite, mul_zero]
    exact sum_sum_diag_indicator
      (fun h b ↦ AdaptedTerminalCoordinates.sY L L ev w.terminalPackets h b *
        (R.coordinateE h : ℤ)) k
  have hYs :
      (∑ b : K, ∑ h : K,
        AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets b h *
          (if b = k ∧ h = k then (R.coordinateE h : ℤ) else 0)) =
        AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets k k *
          (R.coordinateE k : ℤ) := by
    simp only [mul_ite, mul_zero]
    exact sum_sum_diag_indicator
      (fun b h ↦ AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets b h *
        (R.coordinateE h : ℤ)) k
  simp_rw [hv]
  rw [Finset.sum_neg_distrib]
  rw [hsY, hYs]
  ring

end StandingReductionData

end

end DegreeFive

end LieRings
