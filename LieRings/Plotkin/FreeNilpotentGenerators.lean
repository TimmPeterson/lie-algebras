import LieRings.DimensionSubring.DegreeFive.FiniteClassTwoBasis
import LieRings.DimensionSubring.DegreeFive.FiniteRelationRowExpansion
import LieRings.DimensionSubring.DegreeFive.AdaptedPresentation
import LieRings.DimensionSubring.Centrality
import LieRings.PBW.WeightedGraded
import LieRings.Plotkin.Rees
import LieRings.Plotkin.WordFiltration
import Mathlib.LinearAlgebra.StdBasis

/-!
# Homogeneous generators of a finite free nilpotent Lie ring

This file supplies the finite homogeneous input used in the Rees argument for Plotkin's
conjecture.  If `X` is finite, the free nilpotent Lie ring of class at most `c` is the quotient
of the free Lie ring on `X` by its `c`th (Mathlib-indexed) lower-central term.  Its underlying
abelian group is the direct sum of the homogeneous free-Lie pieces of weights `1, ..., c`.

We make that statement an actual integral basis, rather than retaining only a finite spanning
family.  This permits the weighted integral PBW theorem to be applied without choosing any
additional generators or making a freeness assumption.
-/

namespace LieRings.Plotkin

noncomputable section

open scoped BigOperators

universe u

open LieRings.DegreeFive

variable (X : Type u) [Finite X]

local notation "FL" => FreeLieAlgebra ℤ X

/-- The free nilpotent Lie ring on `X`, with homogeneous weights `1, ..., c`. -/
abbrev FreeNilpotent (c : ℕ) :=
  FL ⧸ lowerCentralSeries ℤ FL c

/-- The finite product of the first `c` homogeneous free-Lie pieces. -/
abbrev FreeNilpotentPieces (c : ℕ) :=
  (i : Fin c) → freeLieExact X (i.1 + 1)

/-- The finite index set obtained by putting together the chosen bases of the first `c`
homogeneous free-Lie pieces. -/
abbrev FreeNilpotentBasisIndex (c : ℕ) :=
  Σ i : Fin c, FreeLieExactBasisIndex X (i.1 + 1)

/-- A fixed order on the finite homogeneous index set, used only to order PBW monomials. -/
noncomputable instance freeNilpotentBasisIndexLinearOrder (c : ℕ) :
    LinearOrder (FreeNilpotentBasisIndex X c) :=
  LinearOrder.lift' (Fintype.equivFin (FreeNilpotentBasisIndex X c))
    (Fintype.equivFin (FreeNilpotentBasisIndex X c)).injective

/-- The bracket weight of a homogeneous basis vector. -/
def freeNilpotentWeight {c : ℕ} (i : FreeNilpotentBasisIndex X c) : ℕ :=
  i.1.1 + 1

theorem freeNilpotentWeight_pos {c : ℕ} (i : FreeNilpotentBasisIndex X c) :
    0 < freeNilpotentWeight X i := by
  simp [freeNilpotentWeight]

/-- Sum the first `c` homogeneous components in the free Lie ring. -/
def freeNilpotentPieceSum (c : ℕ) : FreeNilpotentPieces X c →ₗ[ℤ] FL where
  toFun a := ∑ i, (a i : FL)
  map_add' a b := by
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' z a := by
    change ∑ i, z • (a i : FL) = z • ∑ i, (a i : FL)
    exact Finset.smul_sum.symm

/-- Sum homogeneous pieces and pass to the free nilpotent quotient. -/
def freeNilpotentPieceMap (c : ℕ) :
    FreeNilpotentPieces X c →ₗ[ℤ] FreeNilpotent X c :=
  (lowerCentralSeries ℤ FL c).toSubmodule.mkQ.comp
    (freeNilpotentPieceSum X c)

private theorem component_sub_sum_range_mem_lieHigh
    (f : FL) (k : ℕ) :
    f - ∑ n ∈ Finset.range k, freeLieLengthComponent X (n + 1) f ∈
      FreeLieDimension.lieHigh X (k + 1) := by
  induction k with
  | zero =>
      simpa [FreeLieDimension.lieHigh_one]
  | succ k ih =>
      apply mem_lieHigh_succ_of_component_eq_zero X
      · rw [Finset.sum_range_succ]
        have hh : f - ∑ n ∈ Finset.range k,
            freeLieLengthComponent X (n + 1) f -
              freeLieLengthComponent X (k + 1) f ∈
            FreeLieDimension.lieHigh X (k + 1) := by
          apply (FreeLieDimension.lieHigh X (k + 1)).sub_mem ih
          let e : freeLieExact X (k + 1) :=
            ⟨freeLieLengthComponent X (k + 1) f,
              freeLieLengthComponent_mem_exact X (k + 1) f⟩
          exact freeLieExact_mem_lieHigh X e
        convert hh using 1 <;> abel
      · rw [map_sub]
        have hlast : freeLieLengthComponent X (k + 1)
              (freeLieLengthComponent X (k + 1) f) =
            freeLieLengthComponent X (k + 1) f := by
          let e : freeLieExact X (k + 1) :=
            ⟨freeLieLengthComponent X (k + 1) f,
              freeLieLengthComponent_mem_exact X (k + 1) f⟩
          simpa using freeLieLengthComponent_coe_exact X (k + 1) e
        have hprior : freeLieLengthComponent X (k + 1)
              (∑ n ∈ Finset.range k, freeLieLengthComponent X (n + 1) f) = 0 := by
          rw [map_sum]
          apply Finset.sum_eq_zero
          intro n hn
          let e : freeLieExact X (n + 1) :=
            ⟨freeLieLengthComponent X (n + 1) f,
              freeLieLengthComponent_mem_exact X (n + 1) f⟩
          rw [show freeLieLengthComponent X (k + 1)
                (freeLieLengthComponent X (n + 1) f) =
              freeLieLengthComponent X (k + 1) (e : FL) by rfl]
          apply freeLieLengthComponent_coe_exact_of_ne X e
          have hnk : n < k := Finset.mem_range.mp hn
          omega
        rw [Finset.sum_range_succ]
        rw [map_add, hprior, hlast]
        abel

private theorem freeNilpotentPieceMap_surjective (c : ℕ) :
    Function.Surjective (freeNilpotentPieceMap X c) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
      let a : FreeNilpotentPieces X c := fun i ↦
        ⟨freeLieLengthComponent X (i.1 + 1) f,
          freeLieLengthComponent_mem_exact X (i.1 + 1) f⟩
      refine ⟨a, ?_⟩
      apply (Submodule.Quotient.eq
        (lowerCentralSeries ℤ FL c : Submodule ℤ FL)).mpr
      change (∑ i : Fin c, (a i : FL)) - f ∈ lowerCentralSeries ℤ FL c
      change (∑ i : Fin c, (a i : FL)) - f ∈
        (lowerCentralSeries ℤ FL c : Submodule ℤ FL)
      rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries X c]
      have h := component_sub_sum_range_mem_lieHigh X f c
      have hneg := (FreeLieDimension.lieHigh X (c + 1)).neg_mem h
      have hsum : (∑ i : Fin c, freeLieLengthComponent X (i.1 + 1) f) =
          ∑ n ∈ Finset.range c, freeLieLengthComponent X (n + 1) f :=
        Fin.sum_univ_eq_sum_range
          (fun n ↦ freeLieLengthComponent X (n + 1) f) c
      rw [show (∑ i : Fin c, (a i : FL)) =
          ∑ i : Fin c, freeLieLengthComponent X (i.1 + 1) f by rfl,
        hsum]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

private theorem component_pieceSum (c : ℕ)
    (a : FreeNilpotentPieces X c) (i : Fin c) :
    freeLieLengthComponent X (i.1 + 1) (freeNilpotentPieceSum X c a) = a i := by
  change freeLieLengthComponent X (i.1 + 1) (∑ j : Fin c, (a j : FL)) = (a i : FL)
  rw [map_sum]
  classical
  rw [Finset.sum_eq_single i]
  · exact freeLieLengthComponent_coe_exact X (i.1 + 1) (a i)
  · intro j _ hji
    apply freeLieLengthComponent_coe_exact_of_ne X (a j)
    intro hweight
    apply hji
    apply Fin.ext
    omega
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem freeNilpotentPieceMap_injective (c : ℕ) :
    Function.Injective (freeNilpotentPieceMap X c) := by
  intro a b hab
  apply sub_eq_zero.mp
  let d := a - b
  have hdmap : freeNilpotentPieceMap X c d = 0 := by
    rw [map_sub, hab, sub_self]
  change d = 0
  apply funext
  intro i
  apply Subtype.ext
  have hsum : freeNilpotentPieceSum X c d ∈ lowerCentralSeries ℤ FL c := by
    change Submodule.Quotient.mk (freeNilpotentPieceSum X c d) = 0 at hdmap
    exact (Submodule.Quotient.mk_eq_zero
      (lowerCentralSeries ℤ FL c : Submodule ℤ FL)).mp hdmap
  change freeNilpotentPieceSum X c d ∈
    (lowerCentralSeries ℤ FL c : Submodule ℤ FL) at hsum
  rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries X c] at hsum
  have hzero := freeLieLengthComponent_eq_zero_of_mem_lieHigh X hsum
    (show i.1 + 1 < c + 1 by omega)
  rw [component_pieceSum X c d i] at hzero
  exact hzero

/-- The integral homogeneous decomposition of a finite free nilpotent Lie ring. -/
def freeNilpotentPiecesEquiv (c : ℕ) :
    FreeNilpotentPieces X c ≃ₗ[ℤ] FreeNilpotent X c :=
  LinearEquiv.ofBijective (freeNilpotentPieceMap X c)
    ⟨freeNilpotentPieceMap_injective X c, freeNilpotentPieceMap_surjective X c⟩

/-- The homogeneous integral basis of a finite free nilpotent Lie ring. -/
def freeNilpotentBasis (c : ℕ) :
    Module.Basis (FreeNilpotentBasisIndex X c) ℤ (FreeNilpotent X c) :=
  (Pi.basis (fun i : Fin c ↦ freeLieExactBasis X (i.1 + 1))).map
    (freeNilpotentPiecesEquiv X c)

/-- The image in the nilpotent quotient of one chosen exact homogeneous basis vector. -/
def freeNilpotentGenerator {c : ℕ} (i : FreeNilpotentBasisIndex X c) :
    FreeNilpotent X c :=
  LieSubmodule.Quotient.mk
    ((freeLieExactBasis X (i.1.1 + 1) i.2 : freeLieExact X (i.1.1 + 1)) : FL)

@[simp]
theorem freeNilpotentBasis_apply (c : ℕ) (i : FreeNilpotentBasisIndex X c) :
    freeNilpotentBasis X c i = freeNilpotentGenerator X i := by
  classical
  rw [freeNilpotentBasis, Module.Basis.map_apply, Pi.basis_apply]
  change freeNilpotentPieceMap X c
      (Pi.single i.1 (freeLieExactBasis X (i.1.1 + 1) i.2)) =
    LieSubmodule.Quotient.mk
      ((freeLieExactBasis X (i.1.1 + 1) i.2 :
        freeLieExact X (i.1.1 + 1)) : FL)
  let v : FreeNilpotentPieces X c :=
    Pi.single i.1 (freeLieExactBasis X (i.1.1 + 1) i.2)
  change LieSubmodule.Quotient.mk (∑ j : Fin c, (v j : FL)) = _
  rw [Finset.sum_eq_single i.1]
  · simp [v]
  · intro j _ hji
    simp [v, hji]
  · intro hi
    exact (hi (Finset.mem_univ i.1)).elim

/-- Bracketing exact free-Lie elements adds their homogeneous weights. -/
theorem freeLieExact_lie_mem {m n : ℕ}
    (x : freeLieExact X m) (y : freeLieExact X n) :
    ⁅(x : FL), (y : FL)⁆ ∈ freeLieExact X (m + n) := by
  have himage : LieRings.PBW.freeLieToFreeAlgebra ℤ X ⁅(x : FL), (y : FL)⁆ ∈
      FreeLieDimension.associativeExact X (m + n) := by
    rw [LieHom.map_lie]
    exact FreeLieDimension.associativeExact_lie X
      (freeLieToFreeAlgebra_mem_exact X x)
      (freeLieToFreeAlgebra_mem_exact X y)
  let e : freeLieExact X (m + n) :=
    ⟨freeLieLengthComponent X (m + n) ⁅(x : FL), (y : FL)⁆,
      freeLieLengthComponent_mem_exact X (m + n) ⁅(x : FL), (y : FL)⁆⟩
  have heq : (e : FL) = ⁅(x : FL), (y : FL)⁆ := by
    apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
    change LieRings.PBW.freeLieToFreeAlgebra ℤ X
        (freeLieLengthComponent X (m + n) ⁅(x : FL), (y : FL)⁆) = _
    rw [freeLieToFreeAlgebra_freeLieLengthComponent]
    exact associativeLengthComponent_eq_self_of_mem_exact X himage
  exact heq ▸ e.property

private theorem freeNilpotentPieceMap_components (c : ℕ) (f : FL) :
    freeNilpotentPieceMap X c (fun i ↦
      ⟨freeLieLengthComponent X (i.1 + 1) f,
        freeLieLengthComponent_mem_exact X (i.1 + 1) f⟩) =
      LieSubmodule.Quotient.mk f := by
  apply (Submodule.Quotient.eq
    (lowerCentralSeries ℤ FL c : Submodule ℤ FL)).mpr
  change (∑ i : Fin c, freeLieLengthComponent X (i.1 + 1) f) - f ∈
    (lowerCentralSeries ℤ FL c : Submodule ℤ FL)
  rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries X c]
  have h := component_sub_sum_range_mem_lieHigh X f c
  have hneg := (FreeLieDimension.lieHigh X (c + 1)).neg_mem h
  have hsum : (∑ i : Fin c, freeLieLengthComponent X (i.1 + 1) f) =
      ∑ n ∈ Finset.range c, freeLieLengthComponent X (n + 1) f :=
    Fin.sum_univ_eq_sum_range
      (fun n ↦ freeLieLengthComponent X (n + 1) f) c
  rw [hsum]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

/-- Reading the homogeneous-product coordinates of a quotient class amounts to reading the
homogeneous components of any free-Lie representative. -/
theorem freeNilpotentPiecesEquiv_symm_mk_apply (c : ℕ) (f : FL) (i : Fin c) :
    ((freeNilpotentPiecesEquiv X c).symm (LieSubmodule.Quotient.mk f) i : FL) =
      freeLieLengthComponent X (i.1 + 1) f := by
  let a : FreeNilpotentPieces X c := fun j ↦
    ⟨freeLieLengthComponent X (j.1 + 1) f,
      freeLieLengthComponent_mem_exact X (j.1 + 1) f⟩
  have ha : (freeNilpotentPiecesEquiv X c).symm
      (LieSubmodule.Quotient.mk f) = a := by
    apply (freeNilpotentPiecesEquiv X c).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (freeNilpotentPieceMap_components X c f).symm
  exact congrArg Subtype.val (congrFun ha i)

/-- The homogeneous generators are in their prescribed lower-central terms. -/
theorem freeNilpotentGenerator_mem_lowerCentral {c : ℕ}
    (i : FreeNilpotentBasisIndex X c) :
    freeNilpotentGenerator X i ∈
      lowerCentralSeries ℤ (FreeNilpotent X c) (freeNilpotentWeight X i - 1) := by
  let x : freeLieExact X (i.1.1 + 1) :=
    freeLieExactBasis X (i.1.1 + 1) i.2
  have hxHigh : (x : FL) ∈
      FreeLieDimension.lieHigh X (freeNilpotentWeight X i) := by
    simpa [x, freeNilpotentWeight] using freeLieExact_mem_lieHigh X x
  have hxLcs : (x : FL) ∈
      lowerCentralSeries ℤ FL (freeNilpotentWeight X i - 1) := by
    change (x : FL) ∈
      (lowerCentralSeries ℤ FL (freeNilpotentWeight X i - 1) : Submodule ℤ FL)
    rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries X
      (freeNilpotentWeight X i - 1)]
    simpa [Nat.sub_add_cancel (freeNilpotentWeight_pos X i)] using hxHigh
  let q : FL →ₗ⁅ℤ⁆ FreeNilpotent X c :=
    UEA.lieIdealQuotientMk ℤ FL (lowerCentralSeries ℤ FL c)
  have hmap := LieIdeal.map_lowerCentralSeries_le
    (R := ℤ) (f := q) (freeNilpotentWeight X i - 1)
      (LieIdeal.mem_map hxLcs)
  simpa [q, x, freeNilpotentGenerator] using hmap

/-- Each homogeneous basis vector has at least its homogeneous augmentation order. -/
theorem freeNilpotentGenerator_iota_mem_augmentation_pow {c : ℕ}
    (i : FreeNilpotentBasisIndex X c) :
    UniversalEnvelopingAlgebra.ι ℤ (freeNilpotentGenerator X i) ∈
      UEA.augmentationIdeal ℤ (FreeNilpotent X c) ^ freeNilpotentWeight X i := by
  have hdim := lowerCentralSeries_le_dimensionSubring ℤ (FreeNilpotent X c)
    (freeNilpotentWeight X i - 1)
    (freeNilpotentGenerator_mem_lowerCentral X i)
  rw [mem_dimensionSubring] at hdim
  simpa [Nat.sub_add_cancel (freeNilpotentWeight_pos X i)] using hdim

/-- A convenient explicit statement that the finite homogeneous family spans additively. -/
theorem span_freeNilpotentGenerator (c : ℕ) :
    Submodule.span ℤ (Set.range (freeNilpotentGenerator X :
      FreeNilpotentBasisIndex X c → FreeNilpotent X c)) = ⊤ := by
  have hrange : Set.range (freeNilpotentGenerator X :
      FreeNilpotentBasisIndex X c → FreeNilpotent X c) =
      Set.range (freeNilpotentBasis X c) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, freeNilpotentBasis_apply X c i⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, (freeNilpotentBasis_apply X c i).symm⟩
  rw [hrange]
  exact (freeNilpotentBasis X c).span_eq

/-- The homogeneous basis, packaged for the weighted integral PBW theorem. -/
def freeNilpotentWeightedBasis (c : ℕ) :
    LieRings.PBW.WeightedBasis
      (L := FreeNilpotent X c) (ι := FreeNilpotentBasisIndex X c) where
  basis := freeNilpotentBasis X c
  weight := freeNilpotentWeight X
  weight_pos := freeNilpotentWeight_pos X
  bracket_homogeneous := by
    intro i j k hk
    let xi : freeLieExact X (i.1.1 + 1) :=
      freeLieExactBasis X (i.1.1 + 1) i.2
    let xj : freeLieExact X (j.1.1 + 1) :=
      freeLieExactBasis X (j.1.1 + 1) j.2
    let bracketExact : freeLieExact X ((i.1.1 + 1) + (j.1.1 + 1)) :=
      ⟨⁅(xi : FL), (xj : FL)⁆, freeLieExact_lie_mem X xi xj⟩
    rw [freeNilpotentBasis_apply, freeNilpotentBasis_apply,
      freeNilpotentGenerator, freeNilpotentGenerator,
      ← LieSubmodule.Quotient.mk_bracket] at hk
    rw [freeNilpotentBasis, Module.Basis.map_repr] at hk
    change ((Pi.basis (fun r : Fin c ↦
        freeLieExactBasis X (r.1 + 1))).repr
          ((freeNilpotentPiecesEquiv X c).symm
            (LieSubmodule.Quotient.mk ⁅(xi : FL), (xj : FL)⁆))) k ≠ 0 at hk
    rw [Pi.basis_repr] at hk
    let componentExact : freeLieExact X (k.1.1 + 1) :=
      ⟨freeLieLengthComponent X (k.1.1 + 1) ⁅(xi : FL), (xj : FL)⁆,
        freeLieLengthComponent_mem_exact X (k.1.1 + 1) ⁅(xi : FL), (xj : FL)⁆⟩
    have hcoordinate :
        (freeNilpotentPiecesEquiv X c).symm
            (LieSubmodule.Quotient.mk ⁅(xi : FL), (xj : FL)⁆) k.1 =
          componentExact := by
      apply Subtype.ext
      exact freeNilpotentPiecesEquiv_symm_mk_apply X c ⁅(xi : FL), (xj : FL)⁆ k.1
    rw [hcoordinate] at hk
    by_contra hweight
    have hcomponent : freeLieLengthComponent X (k.1.1 + 1)
        ⁅(xi : FL), (xj : FL)⁆ = 0 := by
      change freeLieLengthComponent X (k.1.1 + 1) (bracketExact : FL) = 0
      apply freeLieLengthComponent_coe_exact_of_ne X bracketExact
      intro heq
      apply hweight
      simpa [freeNilpotentWeight] using heq.symm
    have hcomponentExact : componentExact = 0 := by
      apply Subtype.ext
      exact hcomponent
    rw [hcomponentExact, map_zero, Finsupp.zero_apply] at hk
    exact hk rfl
  iota_mem_augmentation_pow := by
    intro i
    rw [freeNilpotentBasis_apply]
    exact freeNilpotentGenerator_iota_mem_augmentation_pow X i

/-- Weighted PBW normal form for the augmentation powers of a finite free nilpotent Lie ring. -/
theorem freeNilpotent_augmentationIdeal_pow_eq_weightGE (c r : ℕ) :
    (UEA.augmentationIdeal ℤ (FreeNilpotent X c) ^ r).restrictScalars ℤ =
      (freeNilpotentWeightedBasis X c).weightGE r :=
  (freeNilpotentWeightedBasis X c).augmentationIdeal_pow_eq_weightGE r

/-! ## Finite generators for the augmentation Rees ring -/

/-- An atom consists of a homogeneous basis vector and a Rees degree no larger than its
homogeneous weight. -/
abbrev FreeNilpotentReesAtomIndex (c : ℕ) :=
  Σ i : FreeNilpotentBasisIndex X c, Fin (freeNilpotentWeight X i + 1)

/-- The Rees degree of an atom. -/
def freeNilpotentReesAtomDegree {c : ℕ}
    (a : FreeNilpotentReesAtomIndex X c) : ℕ := a.2.1

/-- The finite Rees generator `ι(e_i) t^j`, for `0 ≤ j ≤ weight(e_i)`. -/
def freeNilpotentReesAtom {c : ℕ}
    (a : FreeNilpotentReesAtomIndex X c) :
    ReesRing (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) := by
  let B := freeNilpotentWeightedBasis X c
  let I := UEA.augmentationIdeal ℤ (FreeNilpotent X c)
  have ha : UniversalEnvelopingAlgebra.ι ℤ (B.basis a.1) ∈
      I ^ freeNilpotentReesAtomDegree X a := by
    exact Ideal.pow_le_pow_right (Nat.le_of_lt_succ a.2.2)
      (B.iota_mem_augmentation_pow a.1)
  exact DirectSum.of (fun n ↦ ↑(reesPiece I n))
    (freeNilpotentReesAtomDegree X a) ⟨_, ha⟩

private def freeNilpotentReesWordDegree {c : ℕ}
    (as : List (FreeNilpotentReesAtomIndex X c)) : ℕ :=
  (as.map (freeNilpotentReesAtomDegree X)).sum

private theorem freeNilpotentReesBasisWord_mem {c : ℕ}
    (as : List (FreeNilpotentReesAtomIndex X c)) :
    LieRings.PBW.basisWord ℤ (FreeNilpotent X c)
        (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c)
        (as.map Sigma.fst) ∈
      UEA.augmentationIdeal ℤ (FreeNilpotent X c) ^
        freeNilpotentReesWordDegree X as := by
  let B := freeNilpotentWeightedBasis X c
  let I := UEA.augmentationIdeal ℤ (FreeNilpotent X c)
  induction as with
  | nil =>
      change (1 : UEA ℤ (FreeNilpotent X c)) ∈ I ^ 0
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | cons a as ih =>
      rw [List.map_cons, LieRings.PBW.basisWord_cons]
      change UniversalEnvelopingAlgebra.ι ℤ (B.basis a.1) * _ ∈
        I ^ (freeNilpotentReesAtomDegree X a +
          freeNilpotentReesWordDegree X as)
      rw [Ideal.IsTwoSided.pow_add]
      exact Submodule.mul_mem_mul
        (Ideal.pow_le_pow_right (Nat.le_of_lt_succ a.2.2)
          (B.iota_mem_augmentation_pow a.1)) ih

/-- A word in Rees atoms is the homogeneous Rees class of the corresponding PBW basis word. -/
private theorem freeNilpotentReesAtom_word_eq {c : ℕ}
    (as : List (FreeNilpotentReesAtomIndex X c)) :
    WordFiltration.word (freeNilpotentReesAtom X) as =
      DirectSum.of
        (fun n ↦ ↑(reesPiece
          (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) n))
        (freeNilpotentReesWordDegree X as)
        ⟨LieRings.PBW.basisWord ℤ (FreeNilpotent X c)
            (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c)
            (as.map Sigma.fst),
          freeNilpotentReesBasisWord_mem X as⟩ := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      rw [WordFiltration.word_cons, ih, freeNilpotentReesAtom]
      rw [DirectSum.of_mul_of]
      rfl

/-- Distribute a total Rees degree among a list of homogeneous basis factors without exceeding
the weight of any factor. -/
private theorem exists_reesAtomList {c : ℕ}
    (xs : List (FreeNilpotentBasisIndex X c)) (n : ℕ)
    (hn : n ≤ (xs.map (freeNilpotentWeight X)).sum) :
    ∃ as : List (FreeNilpotentReesAtomIndex X c),
      as.map Sigma.fst = xs ∧ freeNilpotentReesWordDegree X as = n := by
  induction xs generalizing n with
  | nil =>
      have hn0 : n = 0 := by simpa using hn
      subst n
      exact ⟨[], rfl, rfl⟩
  | cons i xs ih =>
      let d := min n (freeNilpotentWeight X i)
      let r := n - d
      have hd : d ≤ freeNilpotentWeight X i := min_le_right _ _
      have hr : r ≤ (xs.map (freeNilpotentWeight X)).sum := by
        dsimp only [r, d]
        by_cases hni : n ≤ freeNilpotentWeight X i
        · rw [min_eq_left hni, Nat.sub_self]
          exact Nat.zero_le _
        · rw [min_eq_right (Nat.le_of_not_ge hni)]
          simpa [add_comm] using hn
      obtain ⟨as, has, hdegree⟩ := ih r hr
      change (as.map (freeNilpotentReesAtomDegree X)).sum = r at hdegree
      let a : FreeNilpotentReesAtomIndex X c :=
        ⟨i, ⟨d, Nat.lt_succ_of_le hd⟩⟩
      refine ⟨a :: as, ?_, ?_⟩
      · simp [a, has]
      · simp only [freeNilpotentReesWordDegree, List.map_cons, List.sum_cons,
          freeNilpotentReesAtomDegree, a, hdegree]
        dsimp only [r, d]
        omega

private def freeNilpotentPBWList {c : ℕ}
    (e : FreeNilpotentBasisIndex X c →₀ ℕ) :
    List (FreeNilpotentBasisIndex X c) :=
  (Finsupp.toMultiset e).sort (· ≤ ·)

private theorem freeNilpotentPBWList_pairwise {c : ℕ}
    (e : FreeNilpotentBasisIndex X c →₀ ℕ) :
    (freeNilpotentPBWList X e).Pairwise (· ≤ ·) :=
  Multiset.sort_sorted _ _

private theorem bracketWeight_toMultiset {c : ℕ}
    (e : FreeNilpotentBasisIndex X c →₀ ℕ) :
    (freeNilpotentWeightedBasis X c).bracketWeight e =
      (Finsupp.toMultiset e |>.map (freeNilpotentWeight X)).sum := by
  let B := freeNilpotentWeightedBasis X c
  rw [B.bracketWeight_eq_finsupp_weight]
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | @single_add i m e hi hm ih =>
      rw [map_add, Finsupp.toMultiset_add, Multiset.map_add,
        Multiset.sum_add, ih, Finsupp.toMultiset_single,
        Finsupp.weight_single, Multiset.map_nsmul, Multiset.sum_nsmul,
        Multiset.map_singleton, Multiset.sum_singleton]
      simp [B, freeNilpotentWeightedBasis]

private theorem freeNilpotentPBWList_weight {c : ℕ}
    (e : FreeNilpotentBasisIndex X c →₀ ℕ) :
    ((freeNilpotentPBWList X e).map (freeNilpotentWeight X)).sum =
      (freeNilpotentWeightedBasis X c).bracketWeight e := by
  rw [bracketWeight_toMultiset X e]
  change ((↑(freeNilpotentPBWList X e) :
      Multiset (FreeNilpotentBasisIndex X c)).map
        (freeNilpotentWeight X)).sum = _
  rw [freeNilpotentPBWList, Multiset.sort_eq]

private theorem freeNilpotentPBWList_length {c : ℕ}
    (e : FreeNilpotentBasisIndex X c →₀ ℕ) :
    (freeNilpotentPBWList X e).length =
      LieRings.PBW.WeightedBasis.factorNumber e := by
  let xs := freeNilpotentPBWList X e
  have he : Multiset.toFinsupp (↑xs :
      Multiset (FreeNilpotentBasisIndex X c)) = e := by
    dsimp only [xs, freeNilpotentPBWList]
    rw [Multiset.sort_eq, Finsupp.toMultiset_toFinsupp]
  change xs.length = e.sum fun _ m ↦ m
  rw [← he]
  simpa only [Multiset.card_coe] using
    (Multiset.toFinsupp_sum_eq (↑xs :
      Multiset (FreeNilpotentBasisIndex X c))).symm

private theorem orderedMonomial_eq_freeNilpotentPBWList {c : ℕ}
    (e : FreeNilpotentBasisIndex X c →₀ ℕ) :
    LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
        (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e =
      LieRings.PBW.basisWord ℤ (FreeNilpotent X c)
        (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c)
        (freeNilpotentPBWList X e) := by
  simp [LieRings.PBW.orderedMonomial, LieRings.PBW.basisWord,
    LieRings.PBW.word, freeNilpotentPBWList, Function.comp_def]

private theorem freeNilpotentReesPBWMonomial_mem_term {c n : ℕ}
    (e : FreeNilpotentBasisIndex X c →₀ ℕ)
    (hn : n ≤ (freeNilpotentWeightedBasis X c).bracketWeight e)
    (z : ℤ) :
    ∃ hm : z • LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
          (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e ∈
        UEA.augmentationIdeal ℤ (FreeNilpotent X c) ^ n,
      DirectSum.of
          (fun q ↦ ↑(reesPiece
            (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) q)) n
          ⟨z • LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
              (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e, hm⟩ ∈
        WordFiltration.term (freeNilpotentReesAtom X)
          (LieRings.PBW.WeightedBasis.factorNumber e) := by
  let xs := freeNilpotentPBWList X e
  have hnxs : n ≤ (xs.map (freeNilpotentWeight X)).sum := by
    simpa [xs, freeNilpotentPBWList_weight X e] using hn
  obtain ⟨as, has, hdegree⟩ := exists_reesAtomList X xs n hnxs
  have hlength : as.length = LieRings.PBW.WeightedBasis.factorNumber e := by
    have := congrArg List.length has
    simpa [xs, freeNilpotentPBWList_length X e] using this
  have hterm := WordFiltration.word_mem_term
    (freeNilpotentReesAtom X) as (show as.length ≤
      LieRings.PBW.WeightedBasis.factorNumber e by omega)
  rw [freeNilpotentReesAtom_word_eq X as] at hterm
  have hordered := orderedMonomial_eq_freeNilpotentPBWList X e
  have hbasis : LieRings.PBW.basisWord ℤ (FreeNilpotent X c)
        (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c)
        (as.map Sigma.fst) =
      LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
        (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e := by
    rw [has, ← hordered]
  have hmono : LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
        (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e ∈
      UEA.augmentationIdeal ℤ (FreeNilpotent X c) ^ n := by
    have hmem := freeNilpotentReesBasisWord_mem X as
    rw [hdegree, hbasis] at hmem
    exact hmem
  have hm : z • LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
        (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e ∈
      UEA.augmentationIdeal ℤ (FreeNilpotent X c) ^ n :=
    ((UEA.augmentationIdeal ℤ (FreeNilpotent X c) ^ n).restrictScalars ℤ).smul_mem z hmono
  refine ⟨hm, ?_⟩
  have hsigma :
      GradedMonoid.mk (A := fun q ↦ ↑(reesPiece
          (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) q))
          (freeNilpotentReesWordDegree X as)
          ⟨LieRings.PBW.basisWord ℤ (FreeNilpotent X c)
              (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c)
              (as.map Sigma.fst), freeNilpotentReesBasisWord_mem X as⟩ =
        GradedMonoid.mk (A := fun q ↦ ↑(reesPiece
          (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) q)) n
          ⟨LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
              (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e,
            hmono⟩ := by
    apply Sigma.subtype_ext hdegree
    exact hbasis
  have hof := DirectSum.of_eq_of_gradedMonoid_eq hsigma
  rw [hof] at hterm
  have hz := (WordFiltration.term (freeNilpotentReesAtom X)
      (LieRings.PBW.WeightedBasis.factorNumber e)).smul_mem z hterm
  have hsub : z • (⟨LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
          (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e,
        hmono⟩ : reesPiece
          (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) n) =
      ⟨z • LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
          (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e, hm⟩ := by
    rfl
  have hsmul : z •
        DirectSum.of (fun q ↦ ↑(reesPiece
          (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) q)) n
          ⟨LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
              (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e,
            hmono⟩ =
      DirectSum.of (fun q ↦ ↑(reesPiece
          (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) q)) n
        ⟨z • LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
            (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e, hm⟩ := by
    calc
      _ = DirectSum.of (fun q ↦ ↑(reesPiece
            (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) q)) n
          (z • (⟨LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
              (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e,
            hmono⟩ : reesPiece
              (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) n)) :=
        (map_zsmul (DirectSum.of (fun q ↦ ↑(reesPiece
          (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) q)) n) z _).symm
      _ = _ := congrArg (DirectSum.of (fun q ↦ ↑(reesPiece
        (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) q)) n) hsub
  rw [hsmul] at hz
  exact hz

/-- Every homogeneous Rees class is an integral combination of atom words of uniformly bounded
length. -/
private theorem freeNilpotentRees_homogeneous_mem_term (c n : ℕ)
    (u : reesPiece (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) n) :
    ∃ N, DirectSum.of
        (fun q ↦ ↑(reesPiece
          (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) q)) n u ∈
      WordFiltration.term (freeNilpotentReesAtom X) N := by
  let B := freeNilpotentWeightedBasis X c
  let f : MvPolynomial (FreeNilpotentBasisIndex X c) ℤ :=
    B.pbwEquiv.symm (u : UEA ℤ (FreeNilpotent X c))
  let N := f.support.sup LieRings.PBW.WeightedBasis.factorNumber
  have huWeight : (u : UEA ℤ (FreeNilpotent X c)) ∈ B.weightGE n := by
    rw [← B.augmentationIdeal_pow_eq_weightGE n]
    exact u.property
  have hweight (e : FreeNilpotentBasisIndex X c →₀ ℕ)
      (he : e ∈ f.support) : n ≤ B.bracketWeight e := by
    by_contra hnot
    have hlow := (B.mem_weightGE_iff n (u : UEA ℤ (FreeNilpotent X c))).mp
      huWeight e (Nat.lt_of_not_ge hnot)
    have hcoeff : B.coeff e (u : UEA ℤ (FreeNilpotent X c)) ≠ 0 := by
      change MvPolynomial.coeff e f ≠ 0
      exact Finsupp.mem_support_iff.mp he
    exact hcoeff hlow
  have hmem (e : FreeNilpotentBasisIndex X c →₀ ℕ) :
      MvPolynomial.coeff e f •
          LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
            (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e ∈
        UEA.augmentationIdeal ℤ (FreeNilpotent X c) ^ n := by
    by_cases he : e ∈ f.support
    · exact (freeNilpotentReesPBWMonomial_mem_term X
        (e := e) (hweight e he) (MvPolynomial.coeff e f)).choose
    · have hz : MvPolynomial.coeff e f = 0 := by
        by_contra hnz
        exact he (Finsupp.mem_support_iff.mpr hnz)
      rw [hz, zero_smul]
      exact (UEA.augmentationIdeal ℤ (FreeNilpotent X c) ^ n).zero_mem
  let p : (FreeNilpotentBasisIndex X c →₀ ℕ) →
      reesPiece (UEA.augmentationIdeal ℤ (FreeNilpotent X c)) n :=
    fun e ↦ ⟨MvPolynomial.coeff e f •
        LieRings.PBW.orderedMonomial ℤ (FreeNilpotent X c)
          (FreeNilpotentBasisIndex X c) (freeNilpotentBasis X c) e,
      hmem e⟩
  have huExpansion : (u : UEA ℤ (FreeNilpotent X c)) =
      ∑ e ∈ f.support, (p e : UEA ℤ (FreeNilpotent X c)) := by
    calc
      (u : UEA ℤ (FreeNilpotent X c)) = B.pbwEquiv f :=
        (B.pbwEquiv.apply_symm_apply (u : UEA ℤ (FreeNilpotent X c))).symm
      _ = B.pbwEquiv (∑ e ∈ f.support,
          MvPolynomial.monomial e (MvPolynomial.coeff e f)) := by
        rw [← f.as_sum]
      _ = ∑ e ∈ f.support, (p e : UEA ℤ (FreeNilpotent X c)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro e he
        change B.pbwEquiv (MvPolynomial.monomial e
            (MvPolynomial.coeff e f)) = _
        rw [B.pbwEquiv_monomial]
        simp [p, B, freeNilpotentWeightedBasis]
  have hupiece : u = ∑ e ∈ f.support, p e := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact huExpansion
  refine ⟨N, ?_⟩
  rw [hupiece, map_sum]
  apply (WordFiltration.term (freeNilpotentReesAtom X) N).sum_mem
  intro e he
  have heterm := (freeNilpotentReesPBWMonomial_mem_term X
    (e := e) (hweight e he) (MvPolynomial.coeff e f)).choose_spec
  have hmonoTerm := WordFiltration.term_mono (freeNilpotentReesAtom X)
    (Finset.le_sup he) heterm
  simpa only [p] using hmonoTerm

/-- The finite atoms `ι(e_i)t^j`, `0 ≤ j ≤ weight(e_i)`, exhaust the augmentation Rees
ring by bounded word length. -/
theorem freeNilpotentReesAtom_exhaustive (c : ℕ) :
    ∀ a : ReesRing (UEA.augmentationIdeal ℤ (FreeNilpotent X c)),
      ∃ n, a ∈ WordFiltration.term (freeNilpotentReesAtom X) n := by
  intro a
  induction a using DirectSum.induction_on with
  | zero =>
      exact ⟨0, (WordFiltration.term (freeNilpotentReesAtom X) 0).zero_mem⟩
  | add a b ha hb =>
      obtain ⟨m, ha⟩ := ha
      obtain ⟨n, hb⟩ := hb
      refine ⟨max m n, (WordFiltration.term
        (freeNilpotentReesAtom X) (max m n)).add_mem ?_ ?_⟩
      · exact WordFiltration.term_mono (freeNilpotentReesAtom X)
          (le_max_left m n) ha
      · exact WordFiltration.term_mono (freeNilpotentReesAtom X)
          (le_max_right m n) hb
  | of n u =>
      exact freeNilpotentRees_homogeneous_mem_term X c n u

/-- Pairwise commutators of the finite Rees atoms have atom-word length at most one.  This is
the exact almost-commutativity input for `WordFiltration`. -/
theorem freeNilpotentReesAtom_commutator_mem_term_one (c : ℕ)
    (a b : FreeNilpotentReesAtomIndex X c) :
    freeNilpotentReesAtom X a * freeNilpotentReesAtom X b -
        freeNilpotentReesAtom X b * freeNilpotentReesAtom X a ∈
      WordFiltration.term (freeNilpotentReesAtom X) 1 := by
  let B := freeNilpotentWeightedBasis X c
  let I := UEA.augmentationIdeal ℤ (FreeNilpotent X c)
  let da := freeNilpotentReesAtomDegree X a
  let db := freeNilpotentReesAtomDegree X b
  let d := da + db
  let x : FreeNilpotent X c := ⁅B.basis a.1, B.basis b.1⁆
  have haPow : UniversalEnvelopingAlgebra.ι ℤ (B.basis a.1) ∈ I ^ da :=
    Ideal.pow_le_pow_right (Nat.le_of_lt_succ a.2.2)
      (B.iota_mem_augmentation_pow a.1)
  have hbPow : UniversalEnvelopingAlgebra.ι ℤ (B.basis b.1) ∈ I ^ db :=
    Ideal.pow_le_pow_right (Nat.le_of_lt_succ b.2.2)
      (B.iota_mem_augmentation_pow b.1)
  have hxPow : UniversalEnvelopingAlgebra.ι ℤ x ∈ I ^ d := by
    rw [show UniversalEnvelopingAlgebra.ι ℤ x =
        ⁅UniversalEnvelopingAlgebra.ι ℤ (B.basis a.1),
          UniversalEnvelopingAlgebra.ι ℤ (B.basis b.1)⁆ by
      exact LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℤ)
        (B.basis a.1) (B.basis b.1)]
    rw [LieRing.of_associative_ring_bracket]
    apply (I ^ d).sub_mem
    · change _ * _ ∈ I ^ (da + db)
      rw [Ideal.IsTwoSided.pow_add]
      exact Submodule.mul_mem_mul haPow hbPow
    · change _ * _ ∈ I ^ (da + db)
      rw [show da + db = db + da by omega, Ideal.IsTwoSided.pow_add]
      exact Submodule.mul_mem_mul hbPow haPow
  have habPow : UniversalEnvelopingAlgebra.ι ℤ (B.basis a.1) *
      UniversalEnvelopingAlgebra.ι ℤ (B.basis b.1) ∈ I ^ d := by
    change _ * _ ∈ I ^ (da + db)
    rw [Ideal.IsTwoSided.pow_add]
    exact Submodule.mul_mem_mul haPow hbPow
  have hbaPow : UniversalEnvelopingAlgebra.ι ℤ (B.basis b.1) *
      UniversalEnvelopingAlgebra.ι ℤ (B.basis a.1) ∈ I ^ d := by
    change _ * _ ∈ I ^ (da + db)
    rw [show da + db = db + da by omega, Ideal.IsTwoSided.pow_add]
    exact Submodule.mul_mem_mul hbPow haPow
  have habEq : freeNilpotentReesAtom X a * freeNilpotentReesAtom X b =
      DirectSum.of (fun q ↦ ↑(reesPiece I q)) d
        ⟨UniversalEnvelopingAlgebra.ι ℤ (B.basis a.1) *
          UniversalEnvelopingAlgebra.ι ℤ (B.basis b.1), habPow⟩ := by
    rw [freeNilpotentReesAtom, freeNilpotentReesAtom,
      DirectSum.of_mul_of]
    rfl
  have hbaEq : freeNilpotentReesAtom X b * freeNilpotentReesAtom X a =
      DirectSum.of (fun q ↦ ↑(reesPiece I q)) d
        ⟨UniversalEnvelopingAlgebra.ι ℤ (B.basis b.1) *
          UniversalEnvelopingAlgebra.ι ℤ (B.basis a.1), hbaPow⟩ := by
    rw [freeNilpotentReesAtom, freeNilpotentReesAtom,
      DirectSum.of_mul_of]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.subtype_ext (show db + da = d by simp [d, add_comm])
    rfl
  have hcommEq :
      freeNilpotentReesAtom X a * freeNilpotentReesAtom X b -
          freeNilpotentReesAtom X b * freeNilpotentReesAtom X a =
        DirectSum.of (fun q ↦ ↑(reesPiece I q)) d
          ⟨UniversalEnvelopingAlgebra.ι ℤ x, hxPow⟩ := by
    rw [habEq, hbaEq, ← map_sub]
    apply congrArg (DirectSum.of (fun q ↦ ↑(reesPiece I q)) d)
    apply Subtype.ext
    exact ((LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℤ)
      (B.basis a.1) (B.basis b.1)).trans
        (LieRing.of_associative_ring_bracket _ _)).symm
  rw [hcommEq]
  let r := B.basis.repr x
  have hcoordinatePow (k : FreeNilpotentBasisIndex X c) :
      r k • UniversalEnvelopingAlgebra.ι ℤ (B.basis k) ∈ I ^ d := by
    by_cases hk : r k = 0
    · rw [hk, zero_smul]
      exact (I ^ d).zero_mem
    · have hw := B.bracket_homogeneous a.1 b.1 k hk
      have hd : d ≤ B.weight k := by
        dsimp only [d, da, db, freeNilpotentReesAtomDegree]
        have hda : a.2.1 ≤ B.weight a.1 := by
          simpa [B, freeNilpotentWeightedBasis] using
            (Nat.le_of_lt_succ a.2.2)
        have hdb : b.2.1 ≤ B.weight b.1 := by
          simpa [B, freeNilpotentWeightedBasis] using
            (Nat.le_of_lt_succ b.2.2)
        rw [hw]
        omega
      exact ((I ^ d).restrictScalars ℤ).smul_mem (r k)
        (Ideal.pow_le_pow_right hd (B.iota_mem_augmentation_pow k))
  let q : FreeNilpotentBasisIndex X c → reesPiece I d := fun k ↦
    ⟨r k • UniversalEnvelopingAlgebra.ι ℤ (B.basis k), hcoordinatePow k⟩
  have hsum : ⟨UniversalEnvelopingAlgebra.ι ℤ x, hxPow⟩ =
      ∑ k : FreeNilpotentBasisIndex X c, q k := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    have hbasis := B.basis.sum_repr x
    have hiota := congrArg (UniversalEnvelopingAlgebra.ι ℤ) hbasis
    simpa only [map_sum, map_smul] using hiota.symm
  rw [hsum, map_sum]
  apply (WordFiltration.term (freeNilpotentReesAtom X) 1).sum_mem
  intro k hk
  by_cases hrk : r k = 0
  · have hq : q k = 0 := by
      apply Subtype.ext
      simp [q, hrk]
    rw [hq, map_zero]
    exact (WordFiltration.term (freeNilpotentReesAtom X) 1).zero_mem
  · have hw := B.bracket_homogeneous a.1 b.1 k hrk
    have hd : d ≤ B.weight k := by
      dsimp only [d, da, db, freeNilpotentReesAtomDegree]
      have hda : a.2.1 ≤ B.weight a.1 := by
        simpa [B, freeNilpotentWeightedBasis] using
          (Nat.le_of_lt_succ a.2.2)
      have hdb : b.2.1 ≤ B.weight b.1 := by
        simpa [B, freeNilpotentWeightedBasis] using
          (Nat.le_of_lt_succ b.2.2)
      rw [hw]
      omega
    let atom : FreeNilpotentReesAtomIndex X c :=
      ⟨k, ⟨d, Nat.lt_succ_of_le hd⟩⟩
    have hatom := WordFiltration.word_mem_term
      (freeNilpotentReesAtom X) [atom] (le_refl 1)
    have hatom' : freeNilpotentReesAtom X atom ∈
        WordFiltration.term (freeNilpotentReesAtom X) 1 := by
      simpa using hatom
    have hsmul := (WordFiltration.term (freeNilpotentReesAtom X) 1).smul_mem
      (r k) hatom'
    have hq : r k • freeNilpotentReesAtom X atom =
        DirectSum.of (fun p ↦ ↑(reesPiece I p)) d (q k) := by
      rw [freeNilpotentReesAtom]
      calc
        r k • DirectSum.of (fun p ↦ ↑(reesPiece I p)) d
            ⟨UniversalEnvelopingAlgebra.ι ℤ (B.basis k),
              Ideal.pow_le_pow_right hd (B.iota_mem_augmentation_pow k)⟩ =
          DirectSum.of (fun p ↦ ↑(reesPiece I p)) d
            (r k • ⟨UniversalEnvelopingAlgebra.ι ℤ (B.basis k),
              Ideal.pow_le_pow_right hd (B.iota_mem_augmentation_pow k)⟩) :=
            (map_zsmul (DirectSum.of (fun p ↦ ↑(reesPiece I p)) d) (r k) _).symm
        _ = _ := by
          apply congrArg (DirectSum.of (fun p ↦ ↑(reesPiece I p)) d)
          apply Subtype.ext
          rfl
    rw [hq] at hsmul
    exact hsmul

/-- The augmentation Rees ring of a finitely generated free nilpotent Lie ring is left
Noetherian. -/
theorem isNoetherianRing_freeNilpotentRees (c : ℕ) :
    IsNoetherianRing
      (ReesRing (UEA.augmentationIdeal ℤ (FreeNilpotent X c))) :=
  WordFiltration.isNoetherianRing_of_finite_generators
    (freeNilpotentReesAtom X)
    (freeNilpotentReesAtom_exhaustive X c)
    (freeNilpotentReesAtom_commutator_mem_term_one X c)

end

end LieRings.Plotkin
