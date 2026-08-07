import LieRings.DimensionSubring.DegreeFive.AdaptedSmith
import LieRings.DimensionSubring.DegreeFive.FiniteClassTwoBasis
import LieRings.DimensionSubring.DegreeFive.CoordinateTheta
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The adapted homogeneous presentation

For a finite target Lie ring, multiplication by its cardinality sends every homogeneous free-Lie
component into the leading relation module.  Consequently that relation module has full rank.
This supplies genuine positive Smith bases in every weight used by the degree-five collection.
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

/-- The positive square Smith presentation in homogeneous weight `n`.  Its ambient basis is the
actual adapted basis; its relation basis consists of actual defining relations' leading terms. -/
def homogeneousPositiveSmithPresentation
    (evaluation : LieHom ℤ F L) (n : ℕ) :
    PositiveSmithPresentation
      (ι := FreeLieExactBasisIndex X n)
      (homogeneousRelationLeading X L evaluation n) :=
  PositiveSmithPresentation.ofFiniteQuotient
    (freeLieExactBasis X n)
    (homogeneousRelationLeading X L evaluation n)
    (homogeneousRelationLeading_quotient_finite X L evaluation n)

/-! ## Actual adapted basis vectors and relation lifts

The definitions below deliberately use the ambient basis returned by the *same* Smith
presentation as the relation basis.  This avoids the invalid identification of a Smith head
with an index in the basis supplied to the Smith algorithm.
-/

/-- The adapted homogeneous basis in weight `n`. -/
def adaptedHomogeneousBasis (evaluation : LieHom ℤ F L) (n : ℕ) :
    Module.Basis (FreeLieExactBasisIndex X n) ℤ (freeLieExact X n) :=
  (homogeneousPositiveSmithPresentation X L evaluation n).ambientBasis

/-- The positive diagonal coefficient of an adapted relation row. -/
def adaptedDiagonal (evaluation : LieHom ℤ F L) (n : ℕ) :
    FreeLieExactBasisIndex X n → ℕ :=
  (homogeneousPositiveSmithPresentation X L evaluation n).diagonal

theorem adaptedDiagonal_pos (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    0 < adaptedDiagonal X L evaluation n i :=
  (homogeneousPositiveSmithPresentation X L evaluation n).diagonal_pos i

/-- Every adapted invariant factor divides the cardinality of the finite target. -/
theorem adaptedDiagonal_dvd_card (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    adaptedDiagonal X L evaluation n i ∣ Nat.card L := by
  let P := homogeneousPositiveSmithPresentation X L evaluation n
  have hmemNat : Nat.card L • P.ambientBasis i ∈
      homogeneousRelationLeading X L evaluation n :=
    (homogeneousCardMultipleToLeading X L evaluation n (P.ambientBasis i)).property
  have hmemInt : (Nat.card L : ℤ) • P.ambientBasis i ∈
      homogeneousRelationLeading X L evaluation n := by
    simpa only [Nat.cast_smul_eq_nsmul ℤ] using hmemNat
  have hdiv := P.diagonal_dvd_of_smul_mem i (Nat.card L : ℤ) hmemInt
  exact_mod_cast hdiv

/-- The adapted basis of the leading-relation submodule. -/
def adaptedLeadingRelationBasis (evaluation : LieHom ℤ F L) (n : ℕ) :
    Module.Basis (FreeLieExactBasisIndex X n) ℤ
      (homogeneousRelationLeading X L evaluation n) :=
  (homogeneousPositiveSmithPresentation X L evaluation n).relationBasis

/-! ## One sorted presentation shared by collection and coordinates

The following permutation is the only reindexing performed in the adapted presentation.  Both
the ambient basis and the relation basis are transported by this same permutation.  Every later
consumer must use the definitions in this section; this makes it impossible to combine a Smith
head with a vector from the pre-Smith basis.
-/

/-- The permutation which puts the positive Smith diagonal in nondecreasing order. -/
def adaptedDiagonalSort (evaluation : LieHom ℤ F L) (n : ℕ) :
    Equiv.Perm (FreeLieExactBasisIndex X n) :=
  Tuple.sort (adaptedDiagonal X L evaluation n)

/-- The single homogeneous basis used by the placed collector and by coordinate extraction. -/
def collectedHomogeneousBasis (evaluation : LieHom ℤ F L) (n : ℕ) :
    Module.Basis (FreeLieExactBasisIndex X n) ℤ (freeLieExact X n) :=
  (adaptedHomogeneousBasis X L evaluation n).reindex
    (adaptedDiagonalSort X L evaluation n).symm

/-- The relation basis transported by exactly the same sorting permutation. -/
def collectedLeadingRelationBasis (evaluation : LieHom ℤ F L) (n : ℕ) :
    Module.Basis (FreeLieExactBasisIndex X n) ℤ
      (homogeneousRelationLeading X L evaluation n) :=
  (adaptedLeadingRelationBasis X L evaluation n).reindex
    (adaptedDiagonalSort X L evaluation n).symm

/-- The positive diagonal attached to the shared collected basis. -/
def collectedDiagonal (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) : ℕ :=
  adaptedDiagonal X L evaluation n (adaptedDiagonalSort X L evaluation n i)

theorem collectedDiagonal_pos (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    0 < collectedDiagonal X L evaluation n i :=
  adaptedDiagonal_pos X L evaluation n _

/-- The collected diagonal is numerically monotone in the ordinary `Fin` order. -/
theorem collectedDiagonal_mono (evaluation : LieHom ℤ F L) (n : ℕ) :
    Monotone (collectedDiagonal X L evaluation n) := by
  exact Tuple.monotone_sort (adaptedDiagonal X L evaluation n)

/-- Choose an actual defining relation lifting one adapted leading row. -/
def adaptedRelationRow (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    filteredPresentationRelations X L evaluation n := by
  let d : homogeneousRelationLeading X L evaluation n :=
    adaptedLeadingRelationBasis X L evaluation n i
  exact ⟨Classical.choose d.property, (Classical.choose_spec d.property).1⟩

/-- The chosen relation really projects to the chosen leading-relation basis vector. -/
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

/-- The genuine positive single-head equation in the genuine adapted ambient basis. -/
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

/-! ## Elimination in the collected (sorted) presentation

The earlier Smith construction first produces an adapted basis and then sorts its positive
diagonal.  The collector must eliminate relations in the *sorted* presentation as well.  The
definitions below make that compatibility literal.  They are propositionally equal to the
unsorted elimination maps, but their basis theorem is stated with
`collectedLeadingRelationBasis`, so downstream code never has to identify two permutations by
hand.
-/

/-- Linear recombination of the sorted collected relation rows. -/
def collectedRelationRowLift (evaluation : LieHom ℤ F L) (n : ℕ) :
    homogeneousRelationLeading X L evaluation n →ₗ[ℤ] F :=
  (collectedLeadingRelationBasis X L evaluation n).constr ℤ
    (fun i ↦ (collectedRelationRow X L evaluation n i : F))

@[simp]
theorem collectedRelationRowLift_basis
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (i : FreeLieExactBasisIndex X n) :
    collectedRelationRowLift X L evaluation n
        (collectedLeadingRelationBasis X L evaluation n i) =
      (collectedRelationRow X L evaluation n i : F) := by
  rw [collectedRelationRowLift, Module.Basis.constr_basis]

/-- Recombining sorted rows and taking the leading component is inclusion. -/
theorem freeLieExactProjection_comp_collectedRelationRowLift
    (evaluation : LieHom ℤ F L) (n : ℕ) :
    (freeLieExactProjection X n).comp
        (collectedRelationRowLift X L evaluation n) =
      (homogeneousRelationLeading X L evaluation n).subtype := by
  apply LinearMap.ext_on_range
    (collectedLeadingRelationBasis X L evaluation n).span_eq
  intro i
  rw [LinearMap.comp_apply, collectedRelationRowLift_basis]
  change freeLieExactProjection X n
      (adaptedRelationRow X L evaluation n
        (adaptedDiagonalSort X L evaluation n i) : F) =
    ((adaptedLeadingRelationBasis X L evaluation n).reindex
      (adaptedDiagonalSort X L evaluation n).symm i :
        homogeneousRelationLeading X L evaluation n)
  rw [freeLieExactProjection_adaptedRelationRow]
  simp [Module.Basis.reindex_apply]

/-- Remove the sorted collected row combination with the prescribed leading component. -/
def collectedRelationRemainder
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) : F :=
  (r : F) - collectedRelationRowLift X L evaluation n
    (filteredRelationLeading X L evaluation n r)

theorem collectedRelationRemainder_mem_ker
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    evaluation (collectedRelationRemainder X L evaluation n r) = 0 := by
  unfold collectedRelationRemainder
  rw [map_sub, show evaluation (r : F) = 0 from r.property.1]
  suffices evaluation (collectedRelationRowLift X L evaluation n
      (filteredRelationLeading X L evaluation n r)) = 0 by rw [this, sub_zero]
  let N : Submodule ℤ (homogeneousRelationLeading X L evaluation n) :=
    LinearMap.ker (evaluation.toLinearMap.comp
      (collectedRelationRowLift X L evaluation n))
  have hbasis : ∀ i, collectedLeadingRelationBasis X L evaluation n i ∈ N := by
    intro i
    change evaluation (collectedRelationRowLift X L evaluation n
      (collectedLeadingRelationBasis X L evaluation n i)) = 0
    rw [collectedRelationRowLift_basis]
    exact collectedRelationRow_mem_ker X L evaluation n i
  have htop : N = ⊤ := by
    apply top_unique
    rw [← (collectedLeadingRelationBasis X L evaluation n).span_eq,
      Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hbasis i
  change filteredRelationLeading X L evaluation n r ∈ N
  rw [htop]
  trivial

theorem collectedRelationRemainder_mem_lieHigh_succ
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    collectedRelationRemainder X L evaluation n r ∈
      FreeLieDimension.lieHigh X (n + 1) := by
  apply mem_lieHigh_succ_of_component_eq_zero X
  · unfold collectedRelationRemainder
    apply (FreeLieDimension.lieHigh X n).sub_mem r.property.2
    let N : Submodule ℤ (homogeneousRelationLeading X L evaluation n) :=
      (FreeLieDimension.lieHigh X n).comap
        (collectedRelationRowLift X L evaluation n)
    have hbasis : ∀ i, collectedLeadingRelationBasis X L evaluation n i ∈ N := by
      intro i
      change collectedRelationRowLift X L evaluation n
          (collectedLeadingRelationBasis X L evaluation n i) ∈
        FreeLieDimension.lieHigh X n
      rw [collectedRelationRowLift_basis]
      exact collectedRelationRow_mem_lieHigh X L evaluation n i
    have htop : N = ⊤ := by
      apply top_unique
      rw [← (collectedLeadingRelationBasis X L evaluation n).span_eq,
        Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hbasis i
    change filteredRelationLeading X L evaluation n r ∈ N
    rw [htop]
    trivial
  · have hzero : freeLieExactProjection X n
        (collectedRelationRemainder X L evaluation n r) = 0 := by
      rw [collectedRelationRemainder, map_sub]
      have hcomp := LinearMap.congr_fun
        (freeLieExactProjection_comp_collectedRelationRowLift X L evaluation n)
          (filteredRelationLeading X L evaluation n r)
      change freeLieExactProjection X n
          (collectedRelationRowLift X L evaluation n
            (filteredRelationLeading X L evaluation n r)) =
        (filteredRelationLeading X L evaluation n r : freeLieExact X n) at hcomp
      rw [hcomp]
      change freeLieExactProjection X n (r : F) -
        freeLieExactProjection X n (r : F) = 0
      exact sub_self _
    exact congrArg Subtype.val hzero

/-- The sorted remainder, bundled for the following homogeneous elimination. -/
def collectedRelationRemainderFilteredSucc
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    filteredPresentationRelations X L evaluation (n + 1) :=
  ⟨collectedRelationRemainder X L evaluation n r,
    collectedRelationRemainder_mem_ker X L evaluation n r,
    collectedRelationRemainder_mem_lieHigh_succ X L evaluation n r⟩

/-- Successive elimination, always using the common sorted collected presentation. -/
def iteratedCollectedRelationRemainder (evaluation : LieHom ℤ F L) :
    (k : ℕ) → LinearMap.ker evaluation.toLinearMap →
      filteredPresentationRelations X L evaluation (k + 1)
  | 0, r => presentationRelationAsFilteredOne X L evaluation r
  | k + 1, r => collectedRelationRemainderFilteredSucc X L evaluation (k + 1)
      (iteratedCollectedRelationRemainder evaluation k r)

/-- The sorted row contribution removed at stage `k`. -/
def iteratedCollectedRelationRowPart
    (evaluation : LieHom ℤ F L) (k : ℕ)
    (r : LinearMap.ker evaluation.toLinearMap) : F :=
  collectedRelationRowLift X L evaluation (k + 1)
    (filteredRelationLeading X L evaluation (k + 1)
      (iteratedCollectedRelationRemainder X L evaluation k r))

theorem iteratedCollectedRelationRemainder_eq_rowPart_add_succ
    (evaluation : LieHom ℤ F L) (k : ℕ)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (iteratedCollectedRelationRemainder X L evaluation k r : F) =
      iteratedCollectedRelationRowPart X L evaluation k r +
        (iteratedCollectedRelationRemainder X L evaluation (k + 1) r : F) := by
  change (iteratedCollectedRelationRemainder X L evaluation k r : F) =
    collectedRelationRowLift X L evaluation (k + 1)
        (filteredRelationLeading X L evaluation (k + 1)
          (iteratedCollectedRelationRemainder X L evaluation k r)) +
      collectedRelationRemainder X L evaluation (k + 1)
        (iteratedCollectedRelationRemainder X L evaluation k r)
  unfold collectedRelationRemainder
  abel

/-- Every defining relation through weight four, expanded in the very same sorted rows used by
the coordinate data and the collector. -/
theorem relation_eq_four_collected_rowParts_add_weightFiveRemainder
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (r : F) = iteratedCollectedRelationRowPart X L evaluation 0 r +
      iteratedCollectedRelationRowPart X L evaluation 1 r +
      iteratedCollectedRelationRowPart X L evaluation 2 r +
      iteratedCollectedRelationRowPart X L evaluation 3 r +
      (iteratedCollectedRelationRemainder X L evaluation 4 r : F) := by
  have h0 := iteratedCollectedRelationRemainder_eq_rowPart_add_succ
    X L evaluation 0 r
  have h1 := iteratedCollectedRelationRemainder_eq_rowPart_add_succ
    X L evaluation 1 r
  have h2 := iteratedCollectedRelationRemainder_eq_rowPart_add_succ
    X L evaluation 2 r
  have h3 := iteratedCollectedRelationRemainder_eq_rowPart_add_succ
    X L evaluation 3 r
  simpa [iteratedCollectedRelationRemainder, presentationRelationAsFilteredOne] using
    h0.trans (by rw [h1, h2, h3]; abel)

/-- Linear recombination of the actual adapted relation rows. -/
def adaptedRelationRowLift (evaluation : LieHom ℤ F L) (n : ℕ) :
    homogeneousRelationLeading X L evaluation n →ₗ[ℤ] F :=
  (adaptedLeadingRelationBasis X L evaluation n).constr ℤ
    (fun i ↦ (adaptedRelationRow X L evaluation n i : F))

/-- Recombining adapted rows and taking the leading component is inclusion. -/
theorem freeLieExactProjection_comp_adaptedRelationRowLift
    (evaluation : LieHom ℤ F L) (n : ℕ) :
    (freeLieExactProjection X n).comp
        (adaptedRelationRowLift X L evaluation n) =
      (homogeneousRelationLeading X L evaluation n).subtype := by
  apply LinearMap.ext_on_range
    (adaptedLeadingRelationBasis X L evaluation n).span_eq
  intro i
  rw [LinearMap.comp_apply, adaptedRelationRowLift,
    Module.Basis.constr_basis, freeLieExactProjection_adaptedRelationRow]
  rfl

/-- Remove the adapted row combination having the same leading homogeneous component. -/
def adaptedRelationRemainder
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) : F :=
  (r : F) - adaptedRelationRowLift X L evaluation n
    (filteredRelationLeading X L evaluation n r)

theorem adaptedRelationRemainder_mem_ker
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    evaluation (adaptedRelationRemainder X L evaluation n r) = 0 := by
  unfold adaptedRelationRemainder
  rw [map_sub, show evaluation (r : F) = 0 from r.property.1]
  suffices evaluation (adaptedRelationRowLift X L evaluation n
      (filteredRelationLeading X L evaluation n r)) = 0 by rw [this, sub_zero]
  let N : Submodule ℤ (homogeneousRelationLeading X L evaluation n) :=
    LinearMap.ker (evaluation.toLinearMap.comp
      (adaptedRelationRowLift X L evaluation n))
  have hbasis : ∀ i, adaptedLeadingRelationBasis X L evaluation n i ∈ N := by
    intro i
    change evaluation (adaptedRelationRowLift X L evaluation n
      (adaptedLeadingRelationBasis X L evaluation n i)) = 0
    rw [adaptedRelationRowLift, Module.Basis.constr_basis]
    exact adaptedRelationRow_mem_ker X L evaluation n i
  have htop : N = ⊤ := by
    apply top_unique
    rw [← (adaptedLeadingRelationBasis X L evaluation n).span_eq,
      Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hbasis i
  change filteredRelationLeading X L evaluation n r ∈ N
  rw [htop]
  trivial

theorem freeLieLengthComponent_adaptedRelationRemainder_eq_zero
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    freeLieLengthComponent X n
      (adaptedRelationRemainder X L evaluation n r) = 0 := by
  have hzero : freeLieExactProjection X n
      (adaptedRelationRemainder X L evaluation n r) = 0 := by
    rw [adaptedRelationRemainder, map_sub]
    have hcomp := LinearMap.congr_fun
      (freeLieExactProjection_comp_adaptedRelationRowLift X L evaluation n)
        (filteredRelationLeading X L evaluation n r)
    change freeLieExactProjection X n
        (adaptedRelationRowLift X L evaluation n
          (filteredRelationLeading X L evaluation n r)) =
      (filteredRelationLeading X L evaluation n r : freeLieExact X n) at hcomp
    rw [hcomp]
    change freeLieExactProjection X n (r : F) -
      freeLieExactProjection X n (r : F) = 0
    exact sub_self _
  exact congrArg Subtype.val hzero

/-- Integral elimination with the actual adapted rows raises the filtration by one. -/
theorem adaptedRelationRemainder_mem_lieHigh_succ
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    adaptedRelationRemainder X L evaluation n r ∈
      FreeLieDimension.lieHigh X (n + 1) := by
  apply mem_lieHigh_succ_of_component_eq_zero X
  · unfold adaptedRelationRemainder
    apply (FreeLieDimension.lieHigh X n).sub_mem r.property.2
    let N : Submodule ℤ (homogeneousRelationLeading X L evaluation n) :=
      (FreeLieDimension.lieHigh X n).comap
        (adaptedRelationRowLift X L evaluation n)
    have hbasis : ∀ i, adaptedLeadingRelationBasis X L evaluation n i ∈ N := by
      intro i
      change adaptedRelationRowLift X L evaluation n
          (adaptedLeadingRelationBasis X L evaluation n i) ∈
        FreeLieDimension.lieHigh X n
      rw [adaptedRelationRowLift, Module.Basis.constr_basis]
      exact adaptedRelationRow_mem_lieHigh X L evaluation n i
    have htop : N = ⊤ := by
      apply top_unique
      rw [← (adaptedLeadingRelationBasis X L evaluation n).span_eq,
        Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hbasis i
    change filteredRelationLeading X L evaluation n r ∈ N
    rw [htop]
    trivial
  · exact freeLieLengthComponent_adaptedRelationRemainder_eq_zero
      X L evaluation n r

/-- The adapted remainder, bundled for the next homogeneous elimination. -/
def adaptedRelationRemainderFilteredSucc
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    filteredPresentationRelations X L evaluation (n + 1) :=
  ⟨adaptedRelationRemainder X L evaluation n r,
    adaptedRelationRemainder_mem_ker X L evaluation n r,
    adaptedRelationRemainder_mem_lieHigh_succ X L evaluation n r⟩

/-- Successive adapted elimination of an arbitrary defining relation. -/
def iteratedAdaptedRelationRemainder (evaluation : LieHom ℤ F L) :
    (k : ℕ) → LinearMap.ker evaluation.toLinearMap →
      filteredPresentationRelations X L evaluation (k + 1)
  | 0, r => presentationRelationAsFilteredOne X L evaluation r
  | k + 1, r => adaptedRelationRemainderFilteredSucc X L evaluation (k + 1)
      (iteratedAdaptedRelationRemainder evaluation k r)

/-- Adapted row contribution removed at stage `k`. -/
def iteratedAdaptedRelationRowPart
    (evaluation : LieHom ℤ F L) (k : ℕ)
    (r : LinearMap.ker evaluation.toLinearMap) : F :=
  adaptedRelationRowLift X L evaluation (k + 1)
    (filteredRelationLeading X L evaluation (k + 1)
      (iteratedAdaptedRelationRemainder X L evaluation k r))

theorem iteratedAdaptedRelationRemainder_eq_rowPart_add_succ
    (evaluation : LieHom ℤ F L) (k : ℕ)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (iteratedAdaptedRelationRemainder X L evaluation k r : F) =
      iteratedAdaptedRelationRowPart X L evaluation k r +
        (iteratedAdaptedRelationRemainder X L evaluation (k + 1) r : F) := by
  change (iteratedAdaptedRelationRemainder X L evaluation k r : F) =
    adaptedRelationRowLift X L evaluation (k + 1)
        (filteredRelationLeading X L evaluation (k + 1)
          (iteratedAdaptedRelationRemainder X L evaluation k r)) +
      adaptedRelationRemainder X L evaluation (k + 1)
        (iteratedAdaptedRelationRemainder X L evaluation k r)
  unfold adaptedRelationRemainder
  abel

/-- Relations through weight four in the actual adapted presentation. -/
theorem relation_eq_four_adapted_rowParts_add_weightFiveRemainder
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (r : F) = iteratedAdaptedRelationRowPart X L evaluation 0 r +
      iteratedAdaptedRelationRowPart X L evaluation 1 r +
      iteratedAdaptedRelationRowPart X L evaluation 2 r +
      iteratedAdaptedRelationRowPart X L evaluation 3 r +
      (iteratedAdaptedRelationRemainder X L evaluation 4 r : F) := by
  have h0 := iteratedAdaptedRelationRemainder_eq_rowPart_add_succ
    X L evaluation 0 r
  have h1 := iteratedAdaptedRelationRemainder_eq_rowPart_add_succ
    X L evaluation 1 r
  have h2 := iteratedAdaptedRelationRemainder_eq_rowPart_add_succ
    X L evaluation 2 r
  have h3 := iteratedAdaptedRelationRemainder_eq_rowPart_add_succ
    X L evaluation 3 r
  simpa [iteratedAdaptedRelationRemainder, presentationRelationAsFilteredOne] using
    h0.trans (by rw [h1, h2, h3]; abel)

end

end DegreeFive

end LieRings
