import LieRings.DimensionSubring.DegreeFive.AdaptedSmith
import LieRings.DimensionSubring.DegreeFive.FiniteClassTwoBasis
import LieRings.DimensionSubring.DegreeFive.FiniteRelationRows
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The adapted homogeneous presentation

This file constructs the common Smith basis used by the degree-four collection argument and
chooses genuine defining relations with the prescribed leading terms.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X

/-- An exact homogeneous element has at least its declared bracket weight. -/
theorem freeLieExact_mem_lieHigh {n : ℕ} (x : freeLieExact X n) :
    (x : F) ∈ FreeLieDimension.lieHigh X n := by
  obtain ⟨p, hp, hpx⟩ := x.property
  refine ⟨p, ?_, hpx⟩
  intro w hw
  exact (hp hw).ge

/-- Multiplication by the cardinality of the finite target lands in the leading relation
submodule, in every homogeneous weight. -/
def homogeneousCardMultipleToLeading
    (evaluation : LieHom ℤ F L) (n : ℕ) :
    freeLieExact X n →ₗ[ℤ] homogeneousRelationLeading X L evaluation n where
  toFun x := by
    letI := Fintype.ofFinite L
    let r : filteredPresentationRelations X L evaluation n :=
      ⟨Nat.card L • (x : F), by
        change evaluation (Nat.card L • (x : F)) = 0
        rw [map_nsmul, Nat.card_eq_fintype_card, card_nsmul_eq_zero],
        (FreeLieDimension.lieHigh X n).nsmul_mem (freeLieExact_mem_lieHigh X x)
          (Nat.card L)⟩
    exact ⟨Nat.card L • x, ⟨r, r.property, by
      apply Subtype.ext
      change freeLieLengthComponent X n (Nat.card L • (x : F)) =
        (Nat.card L • x : freeLieExact X n)
      rw [map_nsmul]
      change Nat.card L • freeLieLengthComponent X n (x : F) =
        Nat.card L • (x : F)
      rw [freeLieLengthComponent_coe_exact X n x]⟩⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' a x := by
    apply Subtype.ext
    change Nat.card L • (a • x) = a • (Nat.card L • x)
    simp only [← Nat.cast_smul_eq_nsmul ℤ]
    module

/-- The cardinality-multiple map is injective. -/
theorem homogeneousCardMultipleToLeading_injective
    (evaluation : LieHom ℤ F L) (n : ℕ) :
    Function.Injective (homogeneousCardMultipleToLeading X L evaluation n) := by
  intro x y hxy
  have hval := congrArg
    (fun z : homogeneousRelationLeading X L evaluation n ↦
      (z : freeLieExact X n)) hxy
  change Nat.card L • x = Nat.card L • y at hval
  rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ] at hval
  exact smul_right_injective (freeLieExact X n)
    (by exact_mod_cast Nat.card_pos.ne') hval

/-- The homogeneous leading-relation module has the same integral rank as its ambient exact
component. -/
theorem homogeneousRelationLeading_finrank_eq
    (evaluation : LieHom ℤ F L) (n : ℕ) :
    Module.finrank ℤ (homogeneousRelationLeading X L evaluation n) =
      Module.finrank ℤ (freeLieExact X n) := by
  apply le_antisymm
  · exact Submodule.finrank_le _
  · exact (homogeneousCardMultipleToLeading X L evaluation n).finrank_le_finrank_of_injective
      (homogeneousCardMultipleToLeading_injective X L evaluation n)

/-- Every homogeneous relation quotient occurring in the adapted presentation is finite. -/
theorem homogeneousRelationLeading_quotient_finite
    (evaluation : LieHom ℤ F L) (n : ℕ) :
    Finite (freeLieExact X n ⧸ homogeneousRelationLeading X L evaluation n) := by
  exact Submodule.finiteQuotientOfFreeOfRankEq
    (homogeneousRelationLeading X L evaluation n)
    (homogeneousRelationLeading_finrank_eq X L evaluation n)

/-- The positive square Smith presentation in homogeneous weight `n`. -/
def homogeneousPositiveSmithPresentation
    (evaluation : LieHom ℤ F L) (n : ℕ) :
    PositiveSmithPresentation
      (ι := FreeLieExactBasisIndex X n)
      (homogeneousRelationLeading X L evaluation n) :=
  PositiveSmithPresentation.ofFiniteQuotient
    (freeLieExactBasis X n)
    (homogeneousRelationLeading X L evaluation n)
    (homogeneousRelationLeading_quotient_finite X L evaluation n)

/-- The adapted homogeneous basis in weight `n`. -/
def adaptedHomogeneousBasis (evaluation : LieHom ℤ F L) (n : ℕ) :
    Module.Basis (FreeLieExactBasisIndex X n) ℤ (freeLieExact X n) :=
  (homogeneousPositiveSmithPresentation X L evaluation n).ambientBasis

/-- The positive diagonal coefficient of an adapted relation row. -/
def adaptedDiagonal (evaluation : LieHom ℤ F L) (n : ℕ) :
    FreeLieExactBasisIndex X n → ℕ :=
  (homogeneousPositiveSmithPresentation X L evaluation n).diagonal

/-- The adapted basis of the leading-relation submodule. -/
def adaptedLeadingRelationBasis (evaluation : LieHom ℤ F L) (n : ℕ) :
    Module.Basis (FreeLieExactBasisIndex X n) ℤ
      (homogeneousRelationLeading X L evaluation n) :=
  (homogeneousPositiveSmithPresentation X L evaluation n).relationBasis

/-- The permutation which puts the positive Smith diagonal in nondecreasing order. -/
def adaptedDiagonalSort (evaluation : LieHom ℤ F L) (n : ℕ) :
    Equiv.Perm (FreeLieExactBasisIndex X n) :=
  Tuple.sort (adaptedDiagonal X L evaluation n)

/-- The single homogeneous basis used by the collector. -/
def collectedHomogeneousBasis (evaluation : LieHom ℤ F L) (n : ℕ) :
    Module.Basis (FreeLieExactBasisIndex X n) ℤ (freeLieExact X n) :=
  (adaptedHomogeneousBasis X L evaluation n).reindex
    (adaptedDiagonalSort X L evaluation n).symm

/-- The relation basis transported by the same sorting permutation. -/
def collectedLeadingRelationBasis (evaluation : LieHom ℤ F L) (n : ℕ) :
    Module.Basis (FreeLieExactBasisIndex X n) ℤ
      (homogeneousRelationLeading X L evaluation n) :=
  (adaptedLeadingRelationBasis X L evaluation n).reindex
    (adaptedDiagonalSort X L evaluation n).symm

/-- The positive diagonal attached to the shared collected basis. -/
def collectedDiagonal (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) : ℕ :=
  adaptedDiagonal X L evaluation n (adaptedDiagonalSort X L evaluation n i)

/-- Choose an actual defining relation lifting one adapted leading row. -/
def adaptedRelationRow (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    filteredPresentationRelations X L evaluation n := by
  let d : homogeneousRelationLeading X L evaluation n :=
    adaptedLeadingRelationBasis X L evaluation n i
  exact ⟨Classical.choose d.property, (Classical.choose_spec d.property).1⟩

/-- The chosen relation projects to the chosen leading-relation basis vector. -/
theorem freeLieExactProjection_adaptedRelationRow
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    freeLieExactProjection X n (adaptedRelationRow X L evaluation n i : F) =
      (adaptedLeadingRelationBasis X L evaluation n i :
        homogeneousRelationLeading X L evaluation n) := by
  unfold adaptedRelationRow
  dsimp only
  exact (Classical.choose_spec
    (adaptedLeadingRelationBasis X L evaluation n i).property).2

/-- The positive single-head equation in the adapted ambient basis. -/
theorem adaptedRelationRow_head
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    freeLieExactProjection X n (adaptedRelationRow X L evaluation n i : F) =
      (adaptedDiagonal X L evaluation n i : ℤ) •
        adaptedHomogeneousBasis X L evaluation n i := by
  rw [freeLieExactProjection_adaptedRelationRow]
  exact (homogeneousPositiveSmithPresentation X L evaluation n).relation_eq i

theorem adaptedRelationRow_mem_ker
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    evaluation (adaptedRelationRow X L evaluation n i : F) = 0 :=
  (adaptedRelationRow X L evaluation n i).property.1

theorem adaptedRelationRow_mem_lieHigh
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    (adaptedRelationRow X L evaluation n i : F) ∈
      FreeLieDimension.lieHigh X n :=
  (adaptedRelationRow X L evaluation n i).property.2

/-- The actual relation row corresponding to a collected-basis index. -/
def collectedRelationRow (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    filteredPresentationRelations X L evaluation n :=
  adaptedRelationRow X L evaluation n (adaptedDiagonalSort X L evaluation n i)

/-- The sorted row has its head in the identically indexed sorted ambient basis. -/
theorem collectedRelationRow_head
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    freeLieExactProjection X n (collectedRelationRow X L evaluation n i : F) =
      (collectedDiagonal X L evaluation n i : ℤ) •
        collectedHomogeneousBasis X L evaluation n i := by
  rw [collectedRelationRow, adaptedRelationRow_head]
  simp only [collectedDiagonal, collectedHomogeneousBasis,
    Module.Basis.reindex_apply, Equiv.symm_symm]

theorem collectedRelationRow_mem_ker
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    evaluation (collectedRelationRow X L evaluation n i : F) = 0 :=
  adaptedRelationRow_mem_ker X L evaluation n _

theorem collectedRelationRow_mem_lieHigh
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    (collectedRelationRow X L evaluation n i : F) ∈
      FreeLieDimension.lieHigh X n :=
  adaptedRelationRow_mem_lieHigh X L evaluation n _

end

end DegreeFive

end LieRings
