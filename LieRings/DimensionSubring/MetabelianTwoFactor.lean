import LieRings.Metabelian.FreeEvaluation
import LieRings.PBW.WeightedGraded
import LieRings.PBW.FactorSymbol
import LieRings.Homological.IntegralPolarization
import LieRings.LinearAlgebra.InvariantFactorSmith
import LieRings.DimensionSubring.Functoriality
import LieRings.UniversalEnveloping.RelationCollection
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Lie.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Util.AssertNoSorry

/-!
# The ordered two-factor proof for metabelian Lie rings

This module follows `lit/obstacle/short_natural_proof.tex`.  Its main result is the
nilpotent form of the odd-dimensional inclusion: a metabelian Lie ring of class at most
`c ≥ 2` has zero `(2c-1)`st dimension subring.  The proof uses a PBW functional supported
on monomials with at most two Lie factors.

The namespace and all presentation data in this file are self-contained.
-/

namespace LieRings.MetabelianTwoFactor

noncomputable section

set_option maxHeartbeats 2000000

open scoped BigOperators
open FreeMetabelian
open LieRings.PBW

universe u v

/-! ## Canonical free presentations -/

/-- The canonical free Lie ring on the underlying type of `L`. -/
private abbrev CanonicalFreeLie (L : Type u) := FreeLieAlgebra ℤ L

/-- Evaluation of the canonical free Lie ring at its named generators. -/
private def canonicalFreeLieEvaluation (L : Type u) [LieRing L] :
    CanonicalFreeLie L →ₗ⁅ℤ⁆ L :=
  FreeLieAlgebra.lift ℤ id

@[simp]
private theorem canonicalFreeLieEvaluation_of
    (L : Type u) [LieRing L] (x : L) :
    canonicalFreeLieEvaluation L (FreeLieAlgebra.of ℤ x) = x := by
  exact FreeLieAlgebra.lift_of_apply _ _

private theorem canonicalFreeLieEvaluation_surjective
    (L : Type u) [LieRing L] :
    Function.Surjective (canonicalFreeLieEvaluation L) := by
  intro x
  exact ⟨FreeLieAlgebra.of ℤ x, canonicalFreeLieEvaluation_of L x⟩

/-! ## Partial-rank ordered Smith coordinates -/

/-- An invariant-factor presentation of an arbitrary submodule of a finite free integral
module.  The relation directions occupy the first `relationRank` ambient basis vectors;
the remaining ambient basis vectors are unrestricted. -/
structure PartialInvariantFactorPresentation
    {M : Type u} [AddCommGroup M]
    (N : Submodule ℤ M) where
  ambientRank : ℕ
  relationRank : ℕ
  relationRank_le : relationRank ≤ ambientRank
  ambientBasis : Module.Basis (Fin ambientRank) ℤ M
  relationBasis : Module.Basis (Fin relationRank) ℤ N
  diagonal : Fin relationRank → ℕ
  diagonal_pos : ∀ i, 0 < diagonal i
  relation_eq : ∀ i, (relationBasis i : M) =
    (diagonal i : ℤ) • ambientBasis (Fin.castLE relationRank_le i)
  diagonal_dvd : ∀ i j, i ≤ j → diagonal i ∣ diagonal j

namespace PartialInvariantFactorPresentation

variable {M : Type u} [AddCommGroup M]

section Construction

variable {m : ℕ} (b : Module.Basis (Fin m) ℤ M) (N : Submodule ℤ M)

/-- Mathlib's rectangular diagonal presentation, before ordering the nonzero diagonal. -/
private def rawSmithData :
    Σ r : ℕ, Module.Basis.SmithNormalForm N (Fin m) r :=
  Submodule.smithNormalForm b N

private abbrev rawRank : ℕ := (rawSmithData b N).1

private def rawSmithForm :
    Module.Basis.SmithNormalForm N (Fin m) (rawRank b N) :=
  (rawSmithData b N).2

private abbrev support : Set (Fin m) :=
  Set.range (rawSmithForm b N).f

private abbrev complementSupport : Set (Fin m) := (support b N)ᶜ

private def supportVector (i : support b N) : M :=
  (rawSmithForm b N).bM i.1

private def complementVector (i : complementSupport b N) : M :=
  (rawSmithForm b N).bM i.1

/-- The direct summand of the ambient module occupied by the nonzero Smith directions. -/
private abbrev occupied : Submodule ℤ M :=
  Submodule.span ℤ (Set.range (supportVector b N))

private abbrev complement : Submodule ℤ M :=
  Submodule.span ℤ (Set.range (complementVector b N))

private def occupiedBasis :
    Module.Basis (support b N) ℤ (occupied b N) :=
  by
    simpa only [occupied, supportVector] using
      Module.Basis.span ((rawSmithForm b N).bM.linearIndependent.comp
        ((↑) : support b N → Fin m) Subtype.val_injective)

private def complementBasis :
    Module.Basis (complementSupport b N) ℤ (complement b N) :=
  by
    simpa only [complement, complementVector] using
      Module.Basis.span ((rawSmithForm b N).bM.linearIndependent.comp
        ((↑) : complementSupport b N → Fin m) Subtype.val_injective)

private theorem relation_le_occupied : N ≤ occupied b N := by
  intro x hx
  let xN : N := ⟨x, hx⟩
  have hsum := congrArg ((↑) : N → M) ((rawSmithForm b N).bN.sum_repr xN)
  change (↑(∑ i, ((rawSmithForm b N).bN.repr xN) i •
      (rawSmithForm b N).bN i) : M) = x at hsum
  rw [Submodule.coe_sum] at hsum
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  change ((rawSmithForm b N).bN.repr xN) i •
      ((rawSmithForm b N).bN i : M) ∈ occupied b N
  rw [(rawSmithForm b N).snf]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact Submodule.subset_span
    (Set.mem_range_self
      (⟨(rawSmithForm b N).f i, ⟨i, rfl⟩⟩ : support b N))

private theorem occupied_isCompl_complement :
    IsCompl (occupied b N) (complement b N) := by
  let S : Set (Fin m) := support b N
  have hset : IsCompl S Sᶜ :=
    ⟨disjoint_compl_right, codisjoint_iff.mpr sup_compl_eq_top⟩
  have h := (rawSmithForm b N).bM.linearIndependent.isCompl_span_image
    (rawSmithForm b N).bM.span_eq hset
  have hsupp : Set.range (supportVector b N) =
      (rawSmithForm b N).bM '' S := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hcompl : Set.range (complementVector b N) =
      (rawSmithForm b N).bM '' Sᶜ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  simpa only [occupied, complement, hsupp, hcompl] using h

/-- The relation module, regarded as a full-rank submodule of its occupied direct summand. -/
private abbrev relationInOccupied : Submodule ℤ (occupied b N) :=
  N.comap (occupied b N).subtype

private def relationInOccupiedBasis :
    Module.Basis (Fin (rawRank b N)) ℤ (relationInOccupied b N) :=
  (rawSmithForm b N).bN.map
    (Submodule.comapSubtypeEquivOfLe (relation_le_occupied b N)).symm

private theorem relationInOccupied_fullRank :
    Module.finrank ℤ (relationInOccupied b N) =
      Module.finrank ℤ (occupied b N) := by
  rw [Module.finrank_eq_card_basis (relationInOccupiedBasis b N),
    Module.finrank_eq_card_basis (occupiedBasis b N)]
  simp only [Fintype.card_fin]
  simpa only [Fintype.card_fin] using
    Fintype.card_congr (Equiv.ofInjective (rawSmithForm b N).f
      (rawSmithForm b N).f.injective)

private def occupiedInvariantFactors :
    InvariantFactorPresentation (relationInOccupied b N) := by
  letI : Module.Free ℤ (occupied b N) := Module.Free.of_basis (occupiedBasis b N)
  letI : Module.Finite ℤ (occupied b N) := Module.Finite.of_basis (occupiedBasis b N)
  let hfinite : Finite ((occupied b N) ⧸ relationInOccupied b N) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ (relationInOccupied_fullRank b N)
  exact InvariantFactorPresentation.ofFiniteQuotient _ hfinite

private abbrev complementRank : ℕ := Nat.card (complementSupport b N)

private def complementFinBasis :
    Module.Basis (Fin (complementRank b N)) ℤ (complement b N) :=
  (complementBasis b N).reindex (Finite.equivFin (complementSupport b N))

private def splitBasis :
    Module.Basis
      (Fin (occupiedInvariantFactors b N).rank ⊕ Fin (complementRank b N)) ℤ M :=
  ((occupiedInvariantFactors b N).ambientBasis.prod (complementFinBasis b N)).map
    ((occupied b N).prodEquivOfIsCompl (complement b N)
      (occupied_isCompl_complement b N))

private def ambientInvariantBasis :
    Module.Basis
      (Fin ((occupiedInvariantFactors b N).rank + complementRank b N)) ℤ M :=
  (splitBasis b N).reindex finSumFinEquiv

private def relationInvariantBasis :
    Module.Basis (Fin (occupiedInvariantFactors b N).rank) ℤ N :=
  (occupiedInvariantFactors b N).relationBasis.map
    (Submodule.comapSubtypeEquivOfLe (relation_le_occupied b N))

private theorem relationInvariantBasis_eq (i : Fin (occupiedInvariantFactors b N).rank) :
    (relationInvariantBasis b N i : M) =
      ((occupiedInvariantFactors b N).diagonal i : ℤ) •
        ambientInvariantBasis b N
          (Fin.castLE (Nat.le_add_right _ _) i) := by
  change (((Submodule.comapSubtypeEquivOfLe (relation_le_occupied b N))
      ((occupiedInvariantFactors b N).relationBasis i) : N) : M) = _
  simp only [Submodule.comapSubtypeEquivOfLe_apply_coe]
  rw [(occupiedInvariantFactors b N).relation_eq]
  change (((occupiedInvariantFactors b N).diagonal i : ℤ) •
      (((occupiedInvariantFactors b N).ambientBasis i : occupied b N) : M)) = _
  congr 1
  change (((occupiedInvariantFactors b N).ambientBasis i : occupied b N) : M) =
    ambientInvariantBasis b N (Fin.castLE (Nat.le_add_right _ _) i)
  rw [ambientInvariantBasis, Module.Basis.coe_reindex]
  change _ = splitBasis b N
    (finSumFinEquiv.symm (Fin.castLE (Nat.le_add_right _ _) i))
  have hindex : Fin.castLE (Nat.le_add_right
      (occupiedInvariantFactors b N).rank (complementRank b N)) i =
      Fin.castAdd (complementRank b N) i := rfl
  rw [hindex, finSumFinEquiv_symm_apply_castAdd]
  rw [splitBasis, Module.Basis.map_apply, Module.Basis.prod_apply]
  simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply]
  symm
  simpa using Submodule.coe_prodEquivOfIsCompl'
    (occupied b N) (complement b N) (occupied_isCompl_complement b N)
      ((occupiedInvariantFactors b N).ambientBasis i, 0)

/-- Every submodule of a finite free integral module has invariant-factor coordinates in
which its diagonal directions occur first. -/
def ofSubmodule [Module.Free ℤ M] [Module.Finite ℤ M]
    (N : Submodule ℤ M) : PartialInvariantFactorPresentation N := by
  let ⟨m, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  exact
    { ambientRank := (occupiedInvariantFactors b N).rank + complementRank b N
      relationRank := (occupiedInvariantFactors b N).rank
      relationRank_le := Nat.le_add_right _ _
      ambientBasis := ambientInvariantBasis b N
      relationBasis := relationInvariantBasis b N
      diagonal := (occupiedInvariantFactors b N).diagonal
      diagonal_pos := (occupiedInvariantFactors b N).diagonal_pos
      relation_eq := relationInvariantBasis_eq b N
      diagonal_dvd := (occupiedInvariantFactors b N).diagonal_dvd }

end Construction

end PartialInvariantFactorPresentation

/-! ## The finite relatively-free presentation -/

namespace Presentation

variable {X : Type u} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (c : ℕ) (hc : 0 < c)

/-- The relatively free metabelian Lie ring of class at most `c`. -/
abbrev FreeRing := FreeMetabelian.Free X c

variable (R : LieIdeal ℤ (FreeRing (X := X) c))

/-- The image of the relation ideal in the degree-one summand. -/
def degreeOneImage : Submodule ℤ X :=
  R.toSubmodule.map (FreeMetabelian.Free.degreeOneLinear hc)

/-- Smith coordinates for the degree-one heads of the relations. -/
def smith : PartialInvariantFactorPresentation (degreeOneImage c hc R) :=
  PartialInvariantFactorPresentation.ofSubmodule (degreeOneImage c hc R)

abbrev generatorRank : ℕ := (smith c hc R).ambientRank
abbrev relationRank : ℕ := (smith c hc R).relationRank

/-- The Smith-ordered degree-one basis `x₁,...,xₘ`. -/
def generatorBasis : Module.Basis (Fin (generatorRank c hc R)) ℤ X :=
  (smith c hc R).ambientBasis

/-- A degree-one basis vector, embedded in the free metabelian ring. -/
def generator (i : Fin (generatorRank c hc R)) : FreeRing (X := X) c :=
  FreeMetabelian.Free.weightIncl 0 hc (generatorBasis c hc R i)

@[simp] theorem degreeOne_generator (i : Fin (generatorRank c hc R)) :
    FreeMetabelian.Free.degreeOneLinear hc (generator c hc R i) =
      generatorBasis c hc R i := by
  rfl

private theorem rowWitness_exists (i : Fin (relationRank c hc R)) :
    ∃ rho : FreeRing (X := X) c,
      rho ∈ R ∧ FreeMetabelian.Free.degreeOneLinear hc rho =
        ((smith c hc R).relationBasis i : degreeOneImage c hc R) :=
  ((smith c hc R).relationBasis i).property

private def rowWitness (i : Fin (relationRank c hc R)) :
    {rho : FreeRing (X := X) c //
      rho ∈ R ∧ FreeMetabelian.Free.degreeOneLinear hc rho =
        ((smith c hc R).relationBasis i : degreeOneImage c hc R)} :=
  ⟨Classical.choose (rowWitness_exists c hc R i),
    (Classical.choose_spec (rowWitness_exists c hc R i)).1,
    (Classical.choose_spec (rowWitness_exists c hc R i)).2⟩

/-- The chosen full relation row above one invariant-factor generator. -/
def row (i : Fin (relationRank c hc R)) : R :=
  ⟨(rowWitness c hc R i).1, (rowWitness c hc R i).2.1⟩

@[simp] theorem degreeOne_row (i : Fin (relationRank c hc R)) :
    FreeMetabelian.Free.degreeOneLinear hc (row c hc R i : FreeRing (X := X) c) =
      ((smith c hc R).diagonal i : ℤ) •
        generatorBasis c hc R (Fin.castLE (smith c hc R).relationRank_le i) := by
  rw [show FreeMetabelian.Free.degreeOneLinear hc
      (row c hc R i : FreeRing (X := X) c) =
      ((smith c hc R).relationBasis i : degreeOneImage c hc R) from
    (rowWitness c hc R i).2.2]
  exact (smith c hc R).relation_eq i

/-- The derived tail `bᵢ` in the row `ρᵢ = dᵢxᵢ+bᵢ`. -/
def rowTail (i : Fin (relationRank c hc R)) : FreeRing (X := X) c :=
  (row c hc R i : FreeRing (X := X) c) -
    ((smith c hc R).diagonal i : ℤ) •
      generator c hc R (Fin.castLE (smith c hc R).relationRank_le i)

@[simp] theorem degreeOne_rowTail (i : Fin (relationRank c hc R)) :
    FreeMetabelian.Free.degreeOneLinear hc (rowTail c hc R i) = 0 := by
  rw [rowTail, map_sub, degreeOne_row, map_zsmul, degreeOne_generator, sub_self]

theorem row_eq_head_add_tail (i : Fin (relationRank c hc R)) :
    (row c hc R i : FreeRing (X := X) c) =
      ((smith c hc R).diagonal i : ℤ) •
          generator c hc R (Fin.castLE (smith c hc R).relationRank_le i) +
        rowTail c hc R i := by
  simp only [rowTail]
  abel

/-- Relations with zero degree-one head: this is `N=R∩M` in the manuscript. -/
def derivedRelations : Submodule ℤ (FreeRing (X := X) c) :=
  R.toSubmodule ⊓ LinearMap.ker (FreeMetabelian.Free.degreeOneLinear hc)

theorem mem_derivedRelations_iff {x : FreeRing (X := X) c} :
    x ∈ derivedRelations c hc R ↔
      x ∈ R ∧ FreeMetabelian.Free.degreeOneLinear hc x = 0 := by
  rfl

/-- Additively, every relation is a zero-head relation plus an integral combination of the
chosen Smith rows. -/
theorem relation_decomposition (rho : R) :
    ∃ (n : derivedRelations c hc R) (a : Fin (relationRank c hc R) → ℤ),
      (rho : FreeRing (X := X) c) =
        (n : FreeRing (X := X) c) + ∑ i, a i • (row c hc R i : FreeRing (X := X) c) := by
  let e : degreeOneImage c hc R :=
    ⟨FreeMetabelian.Free.degreeOneLinear hc (rho : FreeRing (X := X) c),
      ⟨(rho : FreeRing (X := X) c), rho.property, rfl⟩⟩
  let a : Fin (relationRank c hc R) → ℤ :=
    fun i ↦ (smith c hc R).relationBasis.repr e i
  let rows : FreeRing (X := X) c :=
    ∑ i, a i • (row c hc R i : FreeRing (X := X) c)
  let n : FreeRing (X := X) c := (rho : FreeRing (X := X) c) - rows
  have hnR : n ∈ R := by
    apply R.sub_mem rho.property
    apply R.sum_mem
    intro i hi
    exact R.smul_mem (a i) (row c hc R i).property
  have hndegree : FreeMetabelian.Free.degreeOneLinear hc n = 0 := by
    change FreeMetabelian.Free.degreeOneLinear hc
      ((rho : FreeRing (X := X) c) - rows) = 0
    rw [map_sub]
    have he := congrArg ((↑) : degreeOneImage c hc R → X)
      ((smith c hc R).relationBasis.sum_repr e)
    change (↑(∑ i, ((smith c hc R).relationBasis.repr e) i •
      (smith c hc R).relationBasis i) : X) =
        FreeMetabelian.Free.degreeOneLinear hc (rho : FreeRing (X := X) c) at he
    rw [Submodule.coe_sum] at he
    have hrows : FreeMetabelian.Free.degreeOneLinear hc rows =
        FreeMetabelian.Free.degreeOneLinear hc (rho : FreeRing (X := X) c) := by
      change FreeMetabelian.Free.degreeOneLinear hc
        (∑ i, a i • (row c hc R i : FreeRing (X := X) c)) = _
      rw [map_sum]
      simp_rw [map_zsmul, degreeOne_row]
      change (∑ i, a i •
        (((smith c hc R).relationBasis i : degreeOneImage c hc R) : X)) =
          FreeMetabelian.Free.degreeOneLinear hc
            (rho : FreeRing (X := X) c) at he
      simpa only [a, (smith c hc R).relation_eq, smul_smul] using he
    rw [hrows, sub_self]
  refine ⟨⟨n, hnR, hndegree⟩, a, ?_⟩
  change (rho : FreeRing (X := X) c) = n + rows
  simp only [n]
  abel

/-! ### The central Smith corrections -/

/-- In the explicit free metabelian model, two elements with zero degree-one coordinate
commute.  This is the exact `M`-is-abelian form used below. -/
theorem bracket_eq_zero_of_degreeOne_eq_zero
    {x y : FreeRing (X := X) c}
    (hx : FreeMetabelian.Free.degreeOneLinear hc x = 0)
    (hy : FreeMetabelian.Free.degreeOneLinear hc y = 0) :
    ⁅x, y⁆ = 0 := by
  funext i
  rcases i with ⟨(_ | _ | q), hi⟩
  · exact FreeMetabelian.Free.bracket_apply_zero x y hi
  · change FreeMetabelian.generatorBracket X
      (FreeMetabelian.Free.degreeOne x (by omega))
      (FreeMetabelian.Free.degreeOne y (by omega)) = 0
    rw [show FreeMetabelian.Free.degreeOne x (by omega) = 0 by exact hx,
      show FreeMetabelian.Free.degreeOne y (by omega) = 0 by exact hy]
    simp
  · change FreeMetabelian.Action.apply X q
        (FreeMetabelian.Free.degreeOne y (by omega))
        (FreeMetabelian.Free.derived x q (by omega)) -
      FreeMetabelian.Action.apply X q
        (FreeMetabelian.Free.degreeOne x (by omega))
        (FreeMetabelian.Free.derived y q (by omega)) = 0
    rw [show FreeMetabelian.Free.degreeOne x (by omega) = 0 by exact hx,
      show FreeMetabelian.Free.degreeOne y (by omega) = 0 by exact hy]
    simp

/-- Conversely, in the relatively free model the zero degree-one block is precisely the
first derived ideal. -/
theorem mem_derivedSeries_one_of_degreeOne_eq_zero
    (R : LieIdeal ℤ (FreeRing (X := X) c))
    (x : FreeRing (X := X) c)
    (hx : FreeMetabelian.Free.degreeOneLinear hc x = 0) :
    x ∈ LieAlgebra.derivedSeries ℤ (FreeRing (X := X) c) 1 := by
  rw [← FreeMetabelian.Free.sum_incl_project x]
  apply (LieAlgebra.derivedSeries ℤ (FreeRing (X := X) c) 1).sum_mem
  intro i hi
  by_cases hi0 : i.val = 0
  · have hieq : i = (⟨0, hc⟩ : Fin c) := Fin.ext hi0
    subst i
    have hproject : FreeMetabelian.Free.project (⟨0, hc⟩ : Fin c) x = 0 := hx
    rw [hproject, map_zero]
    exact (LieAlgebra.derivedSeries ℤ (FreeRing (X := X) c) 1).zero_mem
  · have hiPos : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi0
    have hweight := FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
      (generatorBasis c hc R) i.val i.isLt
        (FreeMetabelian.Free.project i x)
    have hfirst : FreeMetabelian.Free.weightIncl i.val i.isLt
          (FreeMetabelian.Free.project i x) ∈
        lowerCentralSeries ℤ (FreeRing (X := X) c) 1 :=
      LieModule.antitone_lowerCentralSeries ℤ (FreeRing (X := X) c)
        (FreeRing (X := X) c) hiPos hweight
    change FreeMetabelian.Free.incl i (FreeMetabelian.Free.project i x) ∈ _
    change FreeMetabelian.Free.weightIncl i.val i.isLt
      (FreeMetabelian.Free.project i x) ∈ _
    rwa [show lowerCentralSeries ℤ (FreeRing (X := X) c) 1 =
        LieAlgebra.derivedSeries ℤ (FreeRing (X := X) c) 1 by
      rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ,
        LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ]
      rfl] at hfirst

/-- Right adjoint actions commute on a derived element in a metabelian Lie ring. -/
theorem derived_right_actions_commute {L : Type v} [LieRing L]
    (hmeta : IsMetabelian L) {d x y : L}
    (hd : d ∈ LieAlgebra.derivedSeries ℤ L 1) :
    ⁅⁅d, x⁆, y⁆ = ⁅⁅d, y⁆, x⁆ := by
  have hxy : ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ L 1 := by
    change ⁅x, y⁆ ∈ ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆
    exact LieSubmodule.lie_mem_lie (by simp) (by simp)
  have hz : ⁅d, ⁅x, y⁆⁆ = 0 := hmeta.bracket_eq_zero hd hxy
  have hj := leibniz_lie d x y
  have hs : ⁅x, ⁅d, y⁆⁆ = -⁅⁅d, y⁆, x⁆ :=
    (lie_skew x ⁅d, y⁆).symm
  rw [hz, hs] at hj
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg]
  exact hj.symm

/-- The quadratic correction created when the `i`th Smith head crosses the `j`th one. -/
def correction (i j : Fin (relationRank c hc R)) : FreeRing (X := X) c :=
  ((smith c hc R).diagonal i : ℤ) •
    ⁅generator c hc R (Fin.castLE (smith c hc R).relationRank_le i),
      generator c hc R (Fin.castLE (smith c hc R).relationRank_le j)⁆

@[simp] theorem degreeOne_correction (i j : Fin (relationRank c hc R)) :
    FreeMetabelian.Free.degreeOneLinear hc (correction c hc R i j) = 0 := by
  rw [correction, map_zsmul]
  change ((smith c hc R).diagonal i : ℤ) • 0 = 0
  simp

/-- The quotient presented by `R`. -/
abbrev Quotient := FreeRing (X := X) c ⧸ R

/-- The canonical presentation map. -/
def quotientMap : FreeRing (X := X) c →ₗ⁅ℤ⁆ Quotient c R :=
  UEA.lieIdealQuotientMk ℤ (FreeRing (X := X) c) R

theorem quotientMap_surjective : Function.Surjective (quotientMap c R) :=
  LieSubmodule.Quotient.surjective_mk' R

theorem quotient_isMetabelian : IsMetabelian (Quotient c R) := by
  have hmap := LieIdeal.derivedSeries_map_eq
    (f := quotientMap c R) 2 (quotientMap_surjective c R)
  change LieAlgebra.derivedSeries ℤ (Quotient c R) 2 = ⊥
  rw [← hmap]
  have hfree : LieAlgebra.derivedSeries ℤ (FreeRing (X := X) c) 2 = ⊥ :=
    FreeMetabelian.Free.isMetabelian
  rw [hfree]
  simp

@[simp] theorem quotientMap_row (i : Fin (relationRank c hc R)) :
    quotientMap c R (row c hc R i : FreeRing (X := X) c) = 0 := by
  apply (LieSubmodule.Quotient.mk_eq_zero' (N := R)).mpr
  exact (row c hc R i).property

theorem quotient_head_eq_neg_tail (i : Fin (relationRank c hc R)) :
    ((smith c hc R).diagonal i : ℤ) •
        quotientMap c R
          (generator c hc R (Fin.castLE (smith c hc R).relationRank_le i)) =
      -quotientMap c R (rowTail c hc R i) := by
  have h := congrArg (quotientMap c R) (row_eq_head_add_tail c hc R i)
  rw [map_add, map_zsmul, quotientMap_row] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem quotient_tail_mem_derived (i : Fin (relationRank c hc R)) :
    quotientMap c R (rowTail c hc R i) ∈
      LieAlgebra.derivedSeries ℤ (Quotient c R) 1 := by
  have htail : rowTail c hc R i ∈
      LieAlgebra.derivedSeries ℤ (FreeRing (X := X) c) 1 :=
    mem_derivedSeries_one_of_degreeOne_eq_zero c hc R _
      (degreeOne_rowTail c hc R i)
  apply (LieIdeal.derivedSeries_map_le (f := quotientMap c R) 1)
  exact LieIdeal.mem_map htail

/-- If `j ≤ i`, divisibility of the Smith diagonal makes `dᵢ xⱼ` a derived element
in the quotient. -/
theorem quotient_scaled_generator_mem_derived
    (j i : Fin (relationRank c hc R)) (hji : j ≤ i) :
    ((smith c hc R).diagonal i : ℤ) •
        quotientMap c R
          (generator c hc R (Fin.castLE (smith c hc R).relationRank_le j)) ∈
      LieAlgebra.derivedSeries ℤ (Quotient c R) 1 := by
  obtain ⟨t, ht⟩ := (smith c hc R).diagonal_dvd j i hji
  have hj := quotient_head_eq_neg_tail c hc R j
  rw [ht, Nat.cast_mul, mul_comm, mul_smul]
  apply (LieAlgebra.derivedSeries ℤ (Quotient c R) 1).smul_mem
  rw [hj]
  exact (LieAlgebra.derivedSeries ℤ (Quotient c R) 1).neg_mem
    (quotient_tail_mem_derived c hc R j)

/-- **Central Smith corrections.**  For `j<i`, the image of
`qᵢⱼ=dᵢ[xᵢ,xⱼ]` is central in the presented quotient. -/
theorem correction_mem_center
    (j i : Fin (relationRank c hc R)) (hji : j < i) :
    quotientMap c R (correction c hc R i j) ∈
      LieAlgebra.center ℤ (Quotient c R) := by
  let ii : Fin (generatorRank c hc R) :=
    Fin.castLE (smith c hc R).relationRank_le i
  let jj : Fin (generatorRank c hc R) :=
    Fin.castLE (smith c hc R).relationRank_le j
  let Xi : Quotient c R := quotientMap c R (generator c hc R ii)
  let Xj : Quotient c R := quotientMap c R (generator c hc R jj)
  let Bi : Quotient c R := quotientMap c R (rowTail c hc R i)
  have hBi : Bi ∈ LieAlgebra.derivedSeries ℤ (Quotient c R) 1 :=
    quotient_tail_mem_derived c hc R i
  have hhead : ((smith c hc R).diagonal i : ℤ) • Xi = -Bi := by
    exact quotient_head_eq_neg_tail c hc R i
  have hq : quotientMap c R (correction c hc R i j) = -⁅Bi, Xj⁆ := by
    rw [correction, map_zsmul, LieHom.map_lie]
    change ((smith c hc R).diagonal i : ℤ) • ⁅Xi, Xj⁆ = -⁅Bi, Xj⁆
    calc
      ((smith c hc R).diagonal i : ℤ) • ⁅Xi, Xj⁆ =
          ⁅((smith c hc R).diagonal i : ℤ) • Xi, Xj⁆ :=
        (zsmul_lie Xi Xj ((smith c hc R).diagonal i : ℤ)).symm
      _ = ⁅-Bi, Xj⁆ := by rw [hhead]
      _ = -⁅Bi, Xj⁆ := neg_lie Bi Xj
  have hgenerator (k : Fin (generatorRank c hc R)) :
      ⁅quotientMap c R (correction c hc R i j),
        quotientMap c R (generator c hc R k)⁆ = 0 := by
    let Xk : Quotient c R := quotientMap c R (generator c hc R k)
    have hbr : ((smith c hc R).diagonal i : ℤ) • ⁅Xi, Xk⁆ =
        -⁅Bi, Xk⁆ := by
      calc
        ((smith c hc R).diagonal i : ℤ) • ⁅Xi, Xk⁆ =
            ⁅((smith c hc R).diagonal i : ℤ) • Xi, Xk⁆ :=
          (zsmul_lie Xi Xk ((smith c hc R).diagonal i : ℤ)).symm
        _ = ⁅-Bi, Xk⁆ := by rw [hhead]
        _ = -⁅Bi, Xk⁆ := neg_lie Bi Xk
    have hcommute : ⁅⁅Bi, Xj⁆, Xk⁆ = ⁅⁅Bi, Xk⁆, Xj⁆ :=
      derived_right_actions_commute (quotient_isMetabelian c R) hBi
    have hleftDerived : ⁅Xi, Xk⁆ ∈
        LieAlgebra.derivedSeries ℤ (Quotient c R) 1 := by
      change ⁅Xi, Xk⁆ ∈ ⁅(⊤ : LieIdeal ℤ (Quotient c R)),
        (⊤ : LieIdeal ℤ (Quotient c R))⁆
      exact LieSubmodule.lie_mem_lie (by simp) (by simp)
    have hrightDerived : ((smith c hc R).diagonal i : ℤ) • Xj ∈
        LieAlgebra.derivedSeries ℤ (Quotient c R) 1 := by
      exact quotient_scaled_generator_mem_derived c hc R j i hji.le
    have hzero : ⁅⁅Xi, Xk⁆,
        ((smith c hc R).diagonal i : ℤ) • Xj⁆ = 0 :=
      (quotient_isMetabelian c R).bracket_eq_zero hleftDerived hrightDerived
    calc
      ⁅quotientMap c R (correction c hc R i j), Xk⁆ =
          -⁅⁅Bi, Xj⁆, Xk⁆ := by rw [hq, neg_lie]
      _ = -⁅⁅Bi, Xk⁆, Xj⁆ := by rw [hcommute]
      _ = ⁅((smith c hc R).diagonal i : ℤ) • ⁅Xi, Xk⁆, Xj⁆ := by
        rw [hbr, neg_lie]
      _ = ⁅⁅Xi, Xk⁆,
          ((smith c hc R).diagonal i : ℤ) • Xj⁆ := by
        rw [zsmul_lie, lie_zsmul]
      _ = 0 := hzero
  have hdegreeLinear :
      (fun x : X ↦ ⁅quotientMap c R (correction c hc R i j),
        quotientMap c R (FreeMetabelian.Free.weightIncl 0 hc x)⁆) = 0 := by
    let g : X →ₗ[ℤ] Quotient c R :=
      { toFun := fun x ↦ ⁅quotientMap c R (correction c hc R i j),
          quotientMap c R (FreeMetabelian.Free.weightIncl 0 hc x)⁆
        map_add' := by
          intro x y
          change ⁅quotientMap c R (correction c hc R i j),
            quotientMap c R
              (FreeMetabelian.Free.weightIncl 0 hc (x + y))⁆ = _
          rw [show FreeMetabelian.Free.weightIncl 0 hc (x + y) =
              FreeMetabelian.Free.weightIncl 0 hc x +
                FreeMetabelian.Free.weightIncl 0 hc y by
              exact map_add _ x y]
          rw [map_add, lie_add]
        map_smul' := by
          intro z x
          change ⁅quotientMap c R (correction c hc R i j),
            quotientMap c R
              (FreeMetabelian.Free.weightIncl 0 hc (z • x))⁆ = _
          rw [show FreeMetabelian.Free.weightIncl 0 hc (z • x) =
              z • FreeMetabelian.Free.weightIncl 0 hc x by
              exact map_zsmul _ z x]
          rw [map_zsmul, lie_zsmul]
          rfl }
    have hg : g = 0 := by
      apply (generatorBasis c hc R).ext
      intro k
      change ⁅quotientMap c R (correction c hc R i j),
        quotientMap c R (generator c hc R k)⁆ = 0
      exact hgenerator k
    exact funext fun x ↦ LinearMap.congr_fun hg x
  rw [LieModule.mem_maxTrivSubmodule]
  intro y
  obtain ⟨z, rfl⟩ := quotientMap_surjective c R y
  let z₁ : FreeRing (X := X) c :=
    FreeMetabelian.Free.weightIncl 0 hc
      (FreeMetabelian.Free.degreeOneLinear hc z)
  let zM : FreeRing (X := X) c := z - z₁
  have hzM : FreeMetabelian.Free.degreeOneLinear hc zM = 0 := by
    change FreeMetabelian.Free.degreeOneLinear hc (z - z₁) = 0
    rw [map_sub]
    change FreeMetabelian.Free.degreeOneLinear hc z -
      FreeMetabelian.Free.degreeOneLinear hc
        (FreeMetabelian.Free.weightIncl 0 hc
          (FreeMetabelian.Free.degreeOneLinear hc z)) = 0
    rw [show FreeMetabelian.Free.degreeOneLinear hc
        (FreeMetabelian.Free.weightIncl 0 hc
          (FreeMetabelian.Free.degreeOneLinear hc z)) =
        FreeMetabelian.Free.degreeOneLinear hc z by rfl, sub_self]
  have hqM : ⁅correction c hc R i j, zM⁆ = 0 :=
    bracket_eq_zero_of_degreeOne_eq_zero c hc
      (degreeOne_correction c hc R i j) hzM
  have hzsplit : z = z₁ + zM := by
    simp only [zM]
    abel
  have hright : ⁅quotientMap c R (correction c hc R i j),
      quotientMap c R z⁆ = 0 := by
    rw [hzsplit, map_add, lie_add]
    have hdegree := congrFun hdegreeLinear
      (FreeMetabelian.Free.degreeOneLinear hc z)
    change ⁅quotientMap c R (correction c hc R i j),
        quotientMap c R z₁⁆ +
      ⁅quotientMap c R (correction c hc R i j),
        quotientMap c R zM⁆ = 0
    rw [show ⁅quotientMap c R (correction c hc R i j),
        quotientMap c R z₁⁆ = 0 by exact hdegree]
    rw [← LieHom.map_lie, hqM, map_zero, zero_add]
  rw [← lie_skew]
  simpa using congrArg Neg.neg hright

/-! ### The alternating bracket character and its integral polarization -/

abbrev RatCircle := LieRings.IntegralPolarization.RatCircle

/-- The quotient `W=K/Z`, where `Z` is a chosen central Lie ideal. -/
abbrev CentralQuotient (Z : LieIdeal ℤ (Quotient c R)) :=
  Quotient c R ⧸ Z

/-- The canonical map `K → K/Z`. -/
def centralQuotientMap (Z : LieIdeal ℤ (Quotient c R)) :
    Quotient c R →ₗ⁅ℤ⁆ CentralQuotient c R Z :=
  UEA.lieIdealQuotientMk ℤ (Quotient c R) Z

/-- Before descending to `K/Z`, the form is simply `(x,y) ↦ ℓ([x,y])`. -/
def omegaAmbient (ell : CharacterModule (Quotient c R)) :
    Quotient c R →ₗ[ℤ] Quotient c R →ₗ[ℤ] RatCircle where
  toFun x :=
    { toFun := fun y ↦ ell ⁅x, y⁆
      map_add' := by intro y z; rw [lie_add, map_add]
      map_smul' := by
        intro a y
        rw [lie_zsmul, map_zsmul]
        rfl }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change ell ⁅x + y, z⁆ = ell ⁅x, z⁆ + ell ⁅y, z⁆
    rw [add_lie, map_add]
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    change ell ⁅a • x, y⁆ = a • ell ⁅x, y⁆
    rw [zsmul_lie, map_zsmul]

private theorem omegaAmbient_kills_left
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R)) :
    Z.toSubmodule ≤ (omegaAmbient c R ell).ker := by
  intro z hz
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change ell ⁅z, y⁆ = 0
  have hzcenter := hZ hz
  rw [LieModule.mem_maxTrivSubmodule] at hzcenter
  rw [← lie_skew z y, hzcenter y, neg_zero, map_zero]

private theorem omegaAmbient_kills_right
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R)) :
    Z.toSubmodule ≤ (omegaAmbient c R ell).flip.ker := by
  intro z hz
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro x
  change ell ⁅x, z⁆ = 0
  have hzcenter := hZ hz
  rw [LieModule.mem_maxTrivSubmodule] at hzcenter
  rw [hzcenter x, map_zero]

/-- The well-defined form `Ω(x̄,ȳ)=ℓ([x,y])` on `W=K/Z`. -/
def omega
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R)) :
    CentralQuotient c R Z →ₗ[ℤ] CentralQuotient c R Z →ₗ[ℤ] RatCircle :=
  (omegaAmbient c R ell).liftQ₂ Z.toSubmodule Z.toSubmodule
    (omegaAmbient_kills_left c R Z hZ ell)
    (omegaAmbient_kills_right c R Z hZ ell)

@[simp] theorem omega_mk
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (x y : Quotient c R) :
    omega c R Z hZ ell (centralQuotientMap c R Z x)
        (centralQuotientMap c R Z y) = ell ⁅x, y⁆ := by
  rfl

theorem omega_self
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (x : CentralQuotient c R Z) :
    omega c R Z hZ ell x x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change ell ⁅x, x⁆ = 0
      rw [lie_self, map_zero]

private def omegaAlternating
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R)) :
    CentralQuotient c R Z [⋀^Fin 2]→ₗ[ℤ] RatCircle :=
  AlternatingMap.mk
    (MultilinearMap.mk'
      (fun v ↦ omega c R Z hZ ell (v 0) (v 1))
      (by intro v i x y; fin_cases i <;> simp)
      (by intro v i z x; fin_cases i <;> simp))
    (by
      intro v i j hij hne
      fin_cases i <;> fin_cases j
      · exact (hne rfl).elim
      · change omega c R Z hZ ell (v 0) (v 1) = 0
        have : v 0 = v 1 := by simpa using hij
        rw [this, omega_self]
      · change omega c R Z hZ ell (v 0) (v 1) = 0
        have : v 1 = v 0 := by simpa using hij
        rw [this, omega_self]
      · exact (hne rfl).elim)

private def omegaExterior
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R)) :
    (⋀[ℤ]^2 (CentralQuotient c R Z)) →ₗ[ℤ] RatCircle :=
  exteriorPower.alternatingMapLinearEquiv
    (omegaAlternating c R Z hZ ell)

/-- The manuscript polarization, oriented so that
`H(u,v)-H(v,u)=Ω(u,v)`. -/
def polarization
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R)) :
    CentralQuotient c R Z →ₗ[ℤ] CentralQuotient c R Z →ₗ[ℤ] RatCircle :=
  (Classical.choose
    (LieRings.IntegralPolarization.exists_bilinear_skew_eq
      (CentralQuotient c R Z) (omegaExterior c R Z hZ ell))).flip

theorem polarization_sub_swap
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (x y : CentralQuotient c R Z) :
    polarization c R Z hZ ell x y - polarization c R Z hZ ell y x =
      omega c R Z hZ ell x y := by
  have h := Classical.choose_spec
    (LieRings.IntegralPolarization.exists_bilinear_skew_eq
      (CentralQuotient c R Z) (omegaExterior c R Z hZ ell)) x y
  change polarization c R Z hZ ell x y -
      polarization c R Z hZ ell y x =
    omegaExterior c R Z hZ ell
      (exteriorPower.ιMulti ℤ 2 ![x, y]) at h
  have hext := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (omegaAlternating c R Z hZ ell) ![x, y]
  change omegaExterior c R Z hZ ell
      (exteriorPower.ιMulti ℤ 2 ![x, y]) =
    omega c R Z hZ ell x y at hext
  exact h.trans hext

/-! ### A PBW order with the derived block before the Smith generators -/

/-- The ordinary homogeneous Hall index before its order is changed. -/
abbrev GradedIndex :=
  (s : Fin c) ×
    FreeMetabelian.Free.PieceIndex (Fin (generatorRank c hc R)) s.val

/-- The indices of all homogeneous basis vectors of weight at least two. -/
abbrev DerivedIndex :=
  {i : GradedIndex c hc R // i.1.val ≠ 0}

/-- The manuscript PBW index: every derived basis vector comes first, followed by
`x₁<⋯<xₘ`. -/
abbrev PBWIndex := DerivedIndex c hc R ⊕ Fin (generatorRank c hc R)

private def zeroPieceIndex (i : GradedIndex c hc R) (hi : i.1.val = 0) :
    Fin (generatorRank c hc R) := by
  rcases i with ⟨s, k⟩
  have hs : s = ⟨0, hc⟩ := Fin.ext hi
  subst s
  exact k

/-- Identifies the reordered index with the usual graded Hall index. -/
def pbwIndexEquiv : PBWIndex c hc R ≃ GradedIndex c hc R where
  toFun
    | Sum.inl i => i.1
    | Sum.inr i => ⟨⟨0, hc⟩, i⟩
  invFun i := if hi : i.1.val = 0 then
      Sum.inr (zeroPieceIndex c hc R i hi)
    else Sum.inl ⟨i, hi⟩
  left_inv i := by
    cases i with
    | inl i => simp [i.2]
    | inr i => rfl
  right_inv i := by
    by_cases hi : i.1.val = 0
    · simp only [hi, dite_true]
      rcases i with ⟨s, k⟩
      have hs : s = ⟨0, hc⟩ := Fin.ext hi
      subst s
      rfl
    · simp [hi]

private def pbwIndexCode : PBWIndex c hc R → ℕ ×ₗ ℕ
  | Sum.inl i => toLex (0, (Finite.equivFin (DerivedIndex c hc R) i).val)
  | Sum.inr i => toLex (1, i.val)

private theorem pbwIndexCode_injective :
    Function.Injective (pbwIndexCode c hc R) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [pbwIndexCode, EmbeddingLike.apply_eq_iff_eq,
            Prod.mk.injEq] at hij
          have hfin : Finite.equivFin (DerivedIndex c hc R) i =
              Finite.equivFin (DerivedIndex c hc R) j := Fin.ext hij.2
          exact congrArg Sum.inl ((Finite.equivFin _).injective hfin)
      | inr j =>
          simp only [pbwIndexCode, EmbeddingLike.apply_eq_iff_eq,
            Prod.mk.injEq] at hij
          omega
  | inr i =>
      cases j with
      | inl j =>
          simp only [pbwIndexCode, EmbeddingLike.apply_eq_iff_eq,
            Prod.mk.injEq] at hij
          omega
      | inr j =>
          simp only [pbwIndexCode, EmbeddingLike.apply_eq_iff_eq,
            Prod.mk.injEq] at hij
          exact congrArg Sum.inr (Fin.ext hij.2)

noncomputable instance pbwIndexLinearOrder :
    LinearOrder (PBWIndex c hc R) :=
  LinearOrder.lift' (pbwIndexCode c hc R)
    (pbwIndexCode_injective c hc R)

theorem derivedIndex_lt_generator (i : DerivedIndex c hc R)
    (j : Fin (generatorRank c hc R)) :
    (Sum.inl i : PBWIndex c hc R) < Sum.inr j := by
  change pbwIndexCode c hc R (Sum.inl i) <
    pbwIndexCode c hc R (Sum.inr j)
  simp only [pbwIndexCode]
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl (by omega)

theorem generatorIndex_le_generatorIndex
    (i j : Fin (generatorRank c hc R)) :
    (Sum.inr i : PBWIndex c hc R) ≤ Sum.inr j ↔ i ≤ j := by
  change pbwIndexCode c hc R (Sum.inr i) ≤
      pbwIndexCode c hc R (Sum.inr j) ↔ _
  simp only [pbwIndexCode]
  rw [Prod.Lex.toLex_le_toLex]
  simp

theorem generatorIndex_lt_generatorIndex
    (i j : Fin (generatorRank c hc R)) :
    (Sum.inr i : PBWIndex c hc R) < Sum.inr j ↔ i < j := by
  change pbwIndexCode c hc R (Sum.inr i) <
      pbwIndexCode c hc R (Sum.inr j) ↔ _
  simp only [pbwIndexCode]
  rw [Prod.Lex.toLex_lt_toLex]
  simp

private def gradedBasis :
    Module.Basis (GradedIndex c hc R) ℤ (FreeRing (X := X) c) :=
  Pi.basis (fun s : Fin c ↦
    FreeMetabelian.Free.pieceBasis (generatorBasis c hc R) s.val)

/-- The homogeneous PBW basis ordered exactly as in (3). -/
def pbwBasis :
    Module.Basis (PBWIndex c hc R) ℤ (FreeRing (X := X) c) :=
  (gradedBasis c hc R).reindex (pbwIndexEquiv c hc R).symm

@[simp] theorem pbwBasis_apply (i : PBWIndex c hc R) :
    pbwBasis c hc R i =
      FreeMetabelian.Free.weightIncl
        (pbwIndexEquiv c hc R i).1.val
        (pbwIndexEquiv c hc R i).1.isLt
        (FreeMetabelian.Free.pieceBasis (generatorBasis c hc R)
          (pbwIndexEquiv c hc R i).1.val
          (pbwIndexEquiv c hc R i).2) := by
  rw [pbwBasis, Module.Basis.coe_reindex]
  change gradedBasis c hc R (pbwIndexEquiv c hc R i) = _
  rw [gradedBasis, Pi.basis_apply]
  rfl

@[simp] theorem pbwBasis_generator
    (i : Fin (generatorRank c hc R)) :
    pbwBasis c hc R (Sum.inr i) = generator c hc R i := by
  rw [pbwBasis_apply]
  rfl

/-- Manuscript bracket weight of a PBW basis vector. -/
def pbwWeight (i : PBWIndex c hc R) : ℕ :=
  (pbwIndexEquiv c hc R i).1.val + 1

private theorem pbw_bracket_homogeneous
    (i j k : PBWIndex c hc R)
    (h : (pbwBasis c hc R).repr
      ⁅pbwBasis c hc R i, pbwBasis c hc R j⁆ k ≠ 0) :
    pbwWeight c hc R k = pbwWeight c hc R i + pbwWeight c hc R j := by
  by_contra hweight
  apply h
  have hv : ⁅pbwBasis c hc R i, pbwBasis c hc R j⁆
      (pbwIndexEquiv c hc R k).1 = 0 := by
    rw [pbwBasis_apply, pbwBasis_apply]
    exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
      (pbwIndexEquiv c hc R i).1.val
      (pbwIndexEquiv c hc R j).1.val
      (pbwIndexEquiv c hc R i).1.isLt
      (pbwIndexEquiv c hc R j).1.isLt
      _ _ (pbwIndexEquiv c hc R k).1 (by
        intro heq
        apply hweight
        simp only [pbwWeight]
        omega)
  change ((FreeMetabelian.Free.pieceBasis (generatorBasis c hc R)
      (pbwIndexEquiv c hc R k).1.val).repr
        (⁅pbwBasis c hc R i, pbwBasis c hc R j⁆
          (pbwIndexEquiv c hc R k).1))
      (pbwIndexEquiv c hc R k).2 = 0
  rw [hv, map_zero]
  rfl

private theorem iota_mem_augmentation_pow_of_lcs
    (s : ℕ) {x : FreeRing (X := X) c}
    (hx : x ∈ lowerCentralSeries ℤ (FreeRing (X := X) c) s) :
    UniversalEnvelopingAlgebra.ι ℤ x ∈
      UEA.augmentationIdeal ℤ (FreeRing (X := X) c) ^ (s + 1) := by
  exact (mem_dimensionSubring ℤ (FreeRing (X := X) c)).mp
    (lowerCentralSeries_le_dimensionSubring ℤ
      (FreeRing (X := X) c) s hx)

/-- The weighted PBW basis used in the cutoff argument. -/
def weightedPBWBasis :
    LieRings.PBW.WeightedBasis
      (L := FreeRing (X := X) c) (ι := PBWIndex c hc R) where
  basis := pbwBasis c hc R
  weight := pbwWeight c hc R
  weight_pos i := by simp [pbwWeight]
  bracket_homogeneous := pbw_bracket_homogeneous c hc R
  iota_mem_augmentation_pow i := by
    apply iota_mem_augmentation_pow_of_lcs c
      (pbwIndexEquiv c hc R i).1.val
    rw [pbwBasis_apply]
    exact FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
      (generatorBasis c hc R)
      (pbwIndexEquiv c hc R i).1.val
      (pbwIndexEquiv c hc R i).1.isLt _

/-! ### The ordered two-factor functional -/

private def symTwoFirst (s : Sym (PBWIndex c hc R) 2) :
    PBWIndex c hc R :=
  (s.1.sort (· ≤ ·)).get ⟨0, by
    simpa using congrArg id s.2⟩

private def symTwoSecond (s : Sym (PBWIndex c hc R) 2) :
    PBWIndex c hc R :=
  (s.1.sort (· ≤ ·)).get ⟨1, by
    simpa using congrArg id s.2⟩

/-- The image in `W` of one basis factor of `F`. -/
def centralImage
    (Z : LieIdeal ℤ (Quotient c R)) :
    FreeRing (X := X) c →ₗ[ℤ] CentralQuotient c R Z :=
  (centralQuotientMap c R Z).toLinearMap.comp
    (quotientMap c R).toLinearMap

/-- The image in `W` of one basis factor of `F`. -/
def basisImage
    (Z : LieIdeal ℤ (Quotient c R))
    (i : PBWIndex c hc R) : CentralQuotient c R Z :=
  centralQuotientMap c R Z (quotientMap c R (pbwBasis c hc R i))

@[simp] theorem centralImage_basis
    (Z : LieIdeal ℤ (Quotient c R)) (i : PBWIndex c hc R) :
    centralImage c R Z (pbwBasis c hc R i) = basisImage c hc R Z i := by
  rfl

private def quadraticBasisValue
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (s : Sym (PBWIndex c hc R) 2) : RatCircle :=
  polarization c R Z hZ ell
    (basisImage c hc R Z (symTwoFirst c hc R s))
    (basisImage c hc R Z (symTwoSecond c hc R s))

/-- Read the one-factor PBW symbol by the character `ℓ`. -/
def linearRead (ell : CharacterModule (Quotient c R)) :
    SymmetricPower ℤ (Fin 1) (FreeRing (X := X) c) →ₗ[ℤ] RatCircle :=
  ell.toIntLinearMap.comp
    ((quotientMap c R).toLinearMap.comp
      (SymmetricPower.degreeOneLinearEquiv
        (pbwBasis c hc R)).toLinearMap)

/-- Read a two-factor symmetric PBW coordinate in its unique increasing order. -/
def quadraticRead
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R)) :
    SymmetricPower ℤ (Fin 2) (FreeRing (X := X) c) →ₗ[ℤ] RatCircle :=
  (SymmetricPower.monomialBasis (pbwBasis c hc R) 2).constr ℤ
    (quadraticBasisValue c hc R Z hZ ell)

/-- The functional (4): retain exactly one and two Lie factors. -/
def functional
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R)) :
    UEA ℤ (FreeRing (X := X) c) →ₗ[ℤ] RatCircle :=
  (linearRead c hc R ell).comp
      (factorSymbol (pbwBasis c hc R) 1) +
    (quadraticRead c hc R Z hZ ell).comp
      (factorSymbol (pbwBasis c hc R) 2)

theorem functional_iota
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (x : FreeRing (X := X) c) :
    functional c hc R Z hZ ell (UniversalEnvelopingAlgebra.ι ℤ x) =
      ell (quotientMap c R x) := by
  rw [functional, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, factorSymbol_one_iota,
    factorSymbol_iota_of_ne_one (pbwBasis c hc R) 2 (by omega),
    map_zero, add_zero]
  change ell (quotientMap c R
    (SymmetricPower.degreeOneLinearEquiv (pbwBasis c hc R)
      (SymmetricPower.degreeOne x))) = _
  rw [SymmetricPower.degreeOneLinearEquiv_degreeOne]

theorem functional_basisWord_two
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (i j : PBWIndex c hc R) (hij : i ≤ j) :
    functional c hc R Z hZ ell
      (UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
        UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R j)) =
      polarization c R Z hZ ell
        (basisImage c hc R Z i) (basisImage c hc R Z j) := by
  have hordered : ([i, j] : List (PBWIndex c hc R)).Pairwise (· ≤ ·) := by
    simp [hij]
  have hword : basisWord ℤ (FreeRing (X := X) c) (PBWIndex c hc R)
      (pbwBasis c hc R) [i, j] =
      UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
        UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R j) := by
    simp [basisWord, word]
  have htwo : factorSymbol (pbwBasis c hc R) 2
      (basisWord ℤ (FreeRing (X := X) c) (PBWIndex c hc R)
        (pbwBasis c hc R) [i, j]) =
      SymmetricPower.monomialBasis (pbwBasis c hc R) 2
        (listSym [i, j]) := by
    exact factorSymbol_basisWord_sorted
      (pbwBasis c hc R) [i, j] hordered
  have hfirst : symTwoFirst c hc R (listSym [i, j]) = i := by
    simp [symTwoFirst, listSym,
      List.mergeSort_eq_self _ hordered]
  have hsecond : symTwoSecond c hc R (listSym [i, j]) = j := by
    simp [symTwoSecond, listSym,
      List.mergeSort_eq_self _ hordered]
  rw [← hword, functional, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    factorSymbol_basisWord_sorted_of_length_ne
      (pbwBasis c hc R) 1 [i, j] hordered (by simp),
    htwo,
    map_zero, zero_add, quadraticRead, Module.Basis.constr_basis]
  change polarization c R Z hZ ell
      (basisImage c hc R Z (symTwoFirst c hc R (listSym [i, j])))
      (basisImage c hc R Z (symTwoSecond c hc R (listSym [i, j]))) = _
  rw [hfirst, hsecond]

theorem functional_basisWord_eq_zero
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (is : List (PBWIndex c hc R)) (his : is.Pairwise (· ≤ ·))
    (h1 : is.length ≠ 1) (h2 : is.length ≠ 2) :
    functional c hc R Z hZ ell
      (basisWord ℤ (FreeRing (X := X) c) (PBWIndex c hc R)
        (pbwBasis c hc R) is) = 0 := by
  rw [functional, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply,
    factorSymbol_basisWord_sorted_of_length_ne
      (pbwBasis c hc R) 1 is his h1,
    factorSymbol_basisWord_sorted_of_length_ne
      (pbwBasis c hc R) 2 is his h2,
    map_zero, map_zero, add_zero]

/-- Equation (5): after exact PBW collection, the displayed order of the two
Lie arguments is retained by the polarization. -/
theorem functional_iota_mul_iota
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (x y : FreeRing (X := X) c) :
    functional c hc R Z hZ ell
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ y) =
      polarization c R Z hZ ell
        (centralImage c R Z x) (centralImage c R Z y) := by
  let lhs : FreeRing (X := X) c →ₗ[ℤ]
      FreeRing (X := X) c →ₗ[ℤ] RatCircle :=
    { toFun := fun x ↦
        { toFun := fun y ↦ functional c hc R Z hZ ell
              (UniversalEnvelopingAlgebra.ι ℤ x *
                UniversalEnvelopingAlgebra.ι ℤ y)
          map_add' := by
            intro y z
            rw [map_add, mul_add, map_add]
          map_smul' := by
            intro a y
            rw [map_zsmul, mul_smul_comm, map_zsmul]
            rfl }
      map_add' := by
        intro x z
        apply LinearMap.ext
        intro y
        change functional c hc R Z hZ ell
            (UniversalEnvelopingAlgebra.ι ℤ (x + z) *
              UniversalEnvelopingAlgebra.ι ℤ y) = _
        rw [map_add, add_mul, map_add]
        rfl
      map_smul' := by
        intro a x
        apply LinearMap.ext
        intro y
        change functional c hc R Z hZ ell
            (UniversalEnvelopingAlgebra.ι ℤ (a • x) *
              UniversalEnvelopingAlgebra.ι ℤ y) = _
        rw [map_zsmul, smul_mul_assoc, map_zsmul]
        rfl }
  let rhs : FreeRing (X := X) c →ₗ[ℤ]
      FreeRing (X := X) c →ₗ[ℤ] RatCircle :=
    { toFun := fun x ↦
        (polarization c R Z hZ ell (centralImage c R Z x)).comp
          (centralImage c R Z)
      map_add' := by
        intro x z
        apply LinearMap.ext
        intro y
        simp
      map_smul' := by
        intro a x
        apply LinearMap.ext
        intro y
        simp }
  have hlr : lhs = rhs := by
    apply (pbwBasis c hc R).ext
    intro i
    apply (pbwBasis c hc R).ext
    intro j
    change functional c hc R Z hZ ell
        (UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
          UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R j)) =
      polarization c R Z hZ ell
        (basisImage c hc R Z i) (basisImage c hc R Z j)
    by_cases hij : i ≤ j
    · exact functional_basisWord_two c hc R Z hZ ell i j hij
    · have hji : j ≤ i := le_of_not_ge hij
      have hswap :
          UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
              UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R j) =
            UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R j) *
                UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) +
              UniversalEnvelopingAlgebra.ι ℤ
                ⁅pbwBasis c hc R i, pbwBasis c hc R j⁆ := by
        have hbr := LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℤ)
          (pbwBasis c hc R i) (pbwBasis c hc R j)
        change UniversalEnvelopingAlgebra.ι ℤ
            ⁅pbwBasis c hc R i, pbwBasis c hc R j⁆ =
          UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
              UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R j) -
            UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R j) *
              UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) at hbr
        rw [hbr]
        noncomm_ring
      have hpol := polarization_sub_swap c R Z hZ ell
        (basisImage c hc R Z i) (basisImage c hc R Z j)
      have homega : omega c R Z hZ ell
          (basisImage c hc R Z i) (basisImage c hc R Z j) =
        ell (quotientMap c R
          ⁅pbwBasis c hc R i, pbwBasis c hc R j⁆) := by
        rw [basisImage, basisImage, omega_mk, LieHom.map_lie]
      rw [homega] at hpol
      rw [hswap, map_add,
        functional_basisWord_two c hc R Z hZ ell j i hji,
        functional_iota]
      rw [← hpol]
      abel
  change lhs x y = rhs x y
  rw [hlr]

/-! ### Exact insertion lemmas for the relation rows -/

/-- An ordered PBW word in the basis fixed above. -/
def pbwWord (is : List (PBWIndex c hc R)) :
    UEA ℤ (FreeRing (X := X) c) :=
  basisWord ℤ (FreeRing (X := X) c) (PBWIndex c hc R)
    (pbwBasis c hc R) is

@[simp] theorem pbwWord_nil : pbwWord c hc R [] = 1 := rfl

@[simp] theorem pbwWord_cons (i : PBWIndex c hc R)
    (is : List (PBWIndex c hc R)) :
    pbwWord c hc R (i :: is) =
      UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
        pbwWord c hc R is := by
  exact basisWord_cons ℤ (FreeRing (X := X) c)
    (PBWIndex c hc R) (pbwBasis c hc R) i is

@[simp] theorem pbwWord_append (is js : List (PBWIndex c hc R)) :
    pbwWord c hc R (is ++ js) = pbwWord c hc R is * pbwWord c hc R js := by
  simp [pbwWord, basisWord, List.map_append]

@[simp] theorem degreeOne_pbwBasis_derived (i : DerivedIndex c hc R) :
    FreeMetabelian.Free.degreeOneLinear hc
      (pbwBasis c hc R (Sum.inl i)) = 0 := by
  rw [pbwBasis_apply]
  change FreeMetabelian.Free.weightIncl i.1.1.val i.1.1.isLt _
      ⟨0, hc⟩ = 0
  exact FreeMetabelian.Free.incl_apply_of_ne i.1.1 ⟨0, hc⟩ (by
    intro h
    apply i.2
    simpa using (congrArg Fin.val h).symm) _

/-- The generator coordinates of the global PBW basis are exactly the
coordinates of the degree-one projection. -/
theorem pbw_repr_generator (x : FreeRing (X := X) c)
    (i : Fin (generatorRank c hc R)) :
    (pbwBasis c hc R).repr x (Sum.inr i) =
      (generatorBasis c hc R).repr
        (FreeMetabelian.Free.degreeOneLinear hc x) i := by
  let lhs : FreeRing (X := X) c →ₗ[ℤ] ℤ :=
    (pbwBasis c hc R).coord (Sum.inr i)
  let rhs : FreeRing (X := X) c →ₗ[ℤ] ℤ :=
    ((generatorBasis c hc R).coord i).comp
      (FreeMetabelian.Free.degreeOneLinear hc)
  have hmaps : lhs = rhs := by
    apply (pbwBasis c hc R).ext
    intro k
    cases k with
    | inl k =>
        change (pbwBasis c hc R).repr
            (pbwBasis c hc R (Sum.inl k)) (Sum.inr i) =
          (generatorBasis c hc R).repr
            (FreeMetabelian.Free.degreeOneLinear hc
              (pbwBasis c hc R (Sum.inl k))) i
        rw [degreeOne_pbwBasis_derived, map_zero,
          Module.Basis.repr_self_apply]
        simp
    | inr k =>
        change (pbwBasis c hc R).repr
            (pbwBasis c hc R (Sum.inr k)) (Sum.inr i) =
          (generatorBasis c hc R).repr
            (FreeMetabelian.Free.degreeOneLinear hc
              (pbwBasis c hc R (Sum.inr k))) i
        have hdegree : FreeMetabelian.Free.degreeOneLinear hc
            (pbwBasis c hc R (Sum.inr k)) = generatorBasis c hc R k := by
          rw [pbwBasis_generator, degreeOne_generator]
        rw [hdegree, Module.Basis.repr_self_apply,
          Module.Basis.repr_self_apply]
        simp
  exact LinearMap.congr_fun hmaps x

theorem bracket_pbwBasis_derived
    (i j : DerivedIndex c hc R) :
    ⁅pbwBasis c hc R (Sum.inl i), pbwBasis c hc R (Sum.inl j)⁆ = 0 := by
  rw [pbwBasis_apply, pbwBasis_apply]
  apply FreeMetabelian.Free.bracket_weightIncl_eq_zero_of_pos
  · exact Nat.pos_of_ne_zero i.2
  · exact Nat.pos_of_ne_zero j.2

/-- Inserting a homogeneous derived basis vector into the initial derived
block produces no commutator correction. -/
theorem iota_derived_mul_pbwWord
    (i : DerivedIndex c hc R)
    (is : List (PBWIndex c hc R)) (his : is.Pairwise (· ≤ ·)) :
    UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R (Sum.inl i)) *
        pbwWord c hc R is =
      pbwWord c hc R (is.orderedInsert (· ≤ ·) (Sum.inl i)) := by
  induction is with
  | nil => simp
  | cons j js ih =>
      have hjs : js.Pairwise (· ≤ ·) := his.tail
      by_cases hij : (Sum.inl i : PBWIndex c hc R) ≤ j
      · rw [List.orderedInsert_cons_of_le (· ≤ ·) js hij]
        simp only [pbwWord_cons]
      · have hjDerived : ∃ d : DerivedIndex c hc R, j = Sum.inl d := by
          cases j with
          | inl d => exact ⟨d, rfl⟩
          | inr k =>
              exact (hij (derivedIndex_lt_generator c hc R i k).le).elim
        obtain ⟨d, rfl⟩ := hjDerived
        rw [List.orderedInsert_of_not_le (· ≤ ·) js hij]
        simp only [pbwWord_cons]
        rw [← mul_assoc, UEA.iota_mul_iota_swap,
          bracket_pbwBasis_derived, map_zero, add_zero, mul_assoc,
          ih hjs]

/-- Once two ordinary factors follow a derived element, every collected PBW
word has at least three factors and is invisible to the functional. -/
theorem functional_degreeZero_mul_pbwWord_of_two_le
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (p : FreeRing (X := X) c)
    (hp : FreeMetabelian.Free.degreeOneLinear hc p = 0)
    (is : List (PBWIndex c hc R)) (his : is.Pairwise (· ≤ ·))
    (hlen : 2 ≤ is.length) :
    functional c hc R Z hZ ell
      (UniversalEnvelopingAlgebra.ι ℤ p * pbwWord c hc R is) = 0 := by
  rw [← (pbwBasis c hc R).sum_repr p, map_sum]
  simp only [map_zsmul, Finset.sum_mul, smul_mul_assoc, map_sum,
    map_zsmul]
  apply Finset.sum_eq_zero
  intro k hk
  cases k with
  | inl k =>
      rw [iota_derived_mul_pbwWord c hc R k is his]
      have hzero : functional c hc R Z hZ ell
          (pbwWord c hc R
            (is.orderedInsert (· ≤ ·) (Sum.inl k))) = 0 := by
        apply functional_basisWord_eq_zero c hc R Z hZ ell
        · exact his.orderedInsert _ is
        · rw [List.orderedInsert_length]
          omega
        · rw [List.orderedInsert_length]
          omega
      rw [hzero, smul_zero]
  | inr k =>
      have hcoeff : (pbwBasis c hc R).repr p (Sum.inr k) = 0 := by
        rw [pbw_repr_generator c hc R p k, hp, map_zero]
        rfl
      rw [hcoeff, zero_smul]

@[simp] theorem quotientMap_derivedRelation
    (n : derivedRelations c hc R) :
    quotientMap c R (n : FreeRing (X := X) c) = 0 := by
  apply (LieSubmodule.Quotient.mk_eq_zero' (N := R)).mpr
  exact n.2.1

/-- A zero-head relation on the left of an ordered PBW word is invisible.
This is the first paragraph of the row lemma. -/
theorem functional_derivedRelation_mul_pbwWord
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (n : derivedRelations c hc R)
    (is : List (PBWIndex c hc R)) (his : is.Pairwise (· ≤ ·)) :
    functional c hc R Z hZ ell
      (UniversalEnvelopingAlgebra.ι ℤ (n : FreeRing (X := X) c) *
        pbwWord c hc R is) = 0 := by
  cases is with
  | nil =>
      rw [pbwWord_nil, mul_one, functional_iota,
        quotientMap_derivedRelation, map_zero]
  | cons i is =>
      cases is with
      | nil =>
          rw [pbwWord_cons, pbwWord_nil, mul_one,
            functional_iota_mul_iota]
          simp [centralImage, quotientMap_derivedRelation]
      | cons j js =>
          apply functional_degreeZero_mul_pbwWord_of_two_le
            c hc R Z hZ ell (n : FreeRing (X := X) c) n.2.2
              (i :: j :: js) his
          simp

/-- Bracketing a zero-head relation on the left by an arbitrary element
again gives a zero-head relation. -/
def derivedRelationLeftBracket
    (x : FreeRing (X := X) c) (n : derivedRelations c hc R) :
    derivedRelations c hc R :=
  ⟨⁅x, (n : FreeRing (X := X) c)⁆,
    R.lie_mem n.2.1,
    by
      change 0 = 0
      rfl⟩

/-- If an `N`-factor occurs at an intermediate position, moving it to the
initial derived block creates only further `N`-factors. -/
theorem functional_pbwWord_mul_derivedRelation_mul_pbwWord
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (left right : List (PBWIndex c hc R))
    (n : derivedRelations c hc R)
    (hordered : (left ++ right).Pairwise (· ≤ ·)) :
    functional c hc R Z hZ ell
      (pbwWord c hc R left *
        UniversalEnvelopingAlgebra.ι ℤ (n : FreeRing (X := X) c) *
          pbwWord c hc R right) = 0 := by
  revert n right
  induction left using List.reverseRecOn with
  | nil =>
      intro right n hordered
      simpa using functional_derivedRelation_mul_pbwWord
        c hc R Z hZ ell n right hordered
  | append_singleton left i ih =>
      intro right n hordered
      let n' : derivedRelations c hc R :=
        derivedRelationLeftBracket c hc R (pbwBasis c hc R i) n
      have hprincipal : (left ++ i :: right).Pairwise (· ≤ ·) := by
        simpa [List.append_assoc] using hordered
      have hsub : (left ++ right).Sublist ((left ++ [i]) ++ right) := by
        rw [List.append_assoc]
        exact (List.Sublist.cons i (List.Sublist.refl right)).append_left left
      have hcorrection : (left ++ right).Pairwise (· ≤ ·) :=
        List.Pairwise.sublist hsub hordered
      have hidentity :
          pbwWord c hc R (left ++ [i]) *
              UniversalEnvelopingAlgebra.ι ℤ
                (n : FreeRing (X := X) c) * pbwWord c hc R right =
            pbwWord c hc R left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (n : FreeRing (X := X) c) *
                  pbwWord c hc R (i :: right) +
              pbwWord c hc R left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (n' : FreeRing (X := X) c) * pbwWord c hc R right := by
        simp only [pbwWord_append, pbwWord_cons, pbwWord_nil, mul_one]
        have hswap :
            UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
                UniversalEnvelopingAlgebra.ι ℤ
                  (n : FreeRing (X := X) c) =
              UniversalEnvelopingAlgebra.ι ℤ
                  (n : FreeRing (X := X) c) *
                  UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) +
                UniversalEnvelopingAlgebra.ι ℤ
                  (n' : FreeRing (X := X) c) := by
          exact UEA.iota_mul_iota_swap ℤ (FreeRing (X := X) c)
            (pbwBasis c hc R i) (n : FreeRing (X := X) c)
        calc
          _ = pbwWord c hc R left *
              (UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
                UniversalEnvelopingAlgebra.ι ℤ
                  (n : FreeRing (X := X) c)) * pbwWord c hc R right := by
                noncomm_ring
          _ = pbwWord c hc R left *
              (UniversalEnvelopingAlgebra.ι ℤ
                    (n : FreeRing (X := X) c) *
                    UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) +
                UniversalEnvelopingAlgebra.ι ℤ
                    (n' : FreeRing (X := X) c)) * pbwWord c hc R right := by
                rw [hswap]
          _ = _ := by noncomm_ring
      rw [hidentity, map_add, ih (i :: right) n hprincipal,
        ih right n' hcorrection, add_zero]

/-- A derived factor whose image in `W` is zero is invisible on the left as
soon as at least one ordinary factor remains. -/
theorem functional_degreeZero_mul_pbwWord_of_ne_nil
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (p : FreeRing (X := X) c)
    (hp : FreeMetabelian.Free.degreeOneLinear hc p = 0)
    (hpW : centralImage c R Z p = 0)
    (is : List (PBWIndex c hc R)) (his : is.Pairwise (· ≤ ·))
    (hne : is ≠ []) :
    functional c hc R Z hZ ell
      (UniversalEnvelopingAlgebra.ι ℤ p * pbwWord c hc R is) = 0 := by
  cases is with
  | nil => exact (hne rfl).elim
  | cons i is =>
      cases is with
      | nil =>
          rw [pbwWord_cons, pbwWord_nil, mul_one,
            functional_iota_mul_iota, hpW]
          simp
      | cons j js =>
          apply functional_degreeZero_mul_pbwWord_of_two_le
            c hc R Z hZ ell p hp (i :: j :: js) his
          simp

/-- Moving a derived factor which is central modulo the relation ideal to
the initial block creates only `N`-branches.  If the whole word has at least
two factors, all branches are invisible. -/
theorem functional_pbwWord_mul_centralFactor_mul_pbwWord
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (p : FreeRing (X := X) c)
    (hp : FreeMetabelian.Free.degreeOneLinear hc p = 0)
    (hpW : centralImage c R Z p = 0)
    (hpR : ∀ x : FreeRing (X := X) c, ⁅x, p⁆ ∈ R)
    (left right : List (PBWIndex c hc R))
    (hordered : (left ++ right).Pairwise (· ≤ ·))
    (hfactors : 2 ≤ left.length + right.length + 1) :
    functional c hc R Z hZ ell
      (pbwWord c hc R left * UniversalEnvelopingAlgebra.ι ℤ p *
        pbwWord c hc R right) = 0 := by
  revert right
  induction left using List.reverseRecOn with
  | nil =>
      intro right hordered hfactors
      have hne : right ≠ [] := by
        intro h
        subst right
        simp at hfactors
      simpa using functional_degreeZero_mul_pbwWord_of_ne_nil
        c hc R Z hZ ell p hp hpW right hordered hne
  | append_singleton left i ih =>
      intro right hordered hfactors
      let n' : derivedRelations c hc R :=
        ⟨⁅pbwBasis c hc R i, p⁆, hpR (pbwBasis c hc R i),
          by
            change 0 = 0
            rfl⟩
      have hprincipal : (left ++ i :: right).Pairwise (· ≤ ·) := by
        simpa [List.append_assoc] using hordered
      have hsub : (left ++ right).Sublist ((left ++ [i]) ++ right) := by
        rw [List.append_assoc]
        exact (List.Sublist.cons i (List.Sublist.refl right)).append_left left
      have hcorrection : (left ++ right).Pairwise (· ≤ ·) :=
        List.Pairwise.sublist hsub hordered
      have hprincipalFactors :
          2 ≤ left.length + (i :: right).length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hfactors
        simp only [List.length_cons]
        omega
      have hidentity :
          pbwWord c hc R (left ++ [i]) *
              UniversalEnvelopingAlgebra.ι ℤ p * pbwWord c hc R right =
            pbwWord c hc R left * UniversalEnvelopingAlgebra.ι ℤ p *
                pbwWord c hc R (i :: right) +
              pbwWord c hc R left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (n' : FreeRing (X := X) c) * pbwWord c hc R right := by
        simp only [pbwWord_append, pbwWord_cons, pbwWord_nil, mul_one]
        have hswap :
            UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
                UniversalEnvelopingAlgebra.ι ℤ p =
              UniversalEnvelopingAlgebra.ι ℤ p *
                  UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) +
                UniversalEnvelopingAlgebra.ι ℤ
                  (n' : FreeRing (X := X) c) := by
          exact UEA.iota_mul_iota_swap ℤ (FreeRing (X := X) c)
            (pbwBasis c hc R i) p
        calc
          _ = pbwWord c hc R left *
              (UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) *
                UniversalEnvelopingAlgebra.ι ℤ p) *
                  pbwWord c hc R right := by noncomm_ring
          _ = pbwWord c hc R left *
              (UniversalEnvelopingAlgebra.ι ℤ p *
                    UniversalEnvelopingAlgebra.ι ℤ (pbwBasis c hc R i) +
                UniversalEnvelopingAlgebra.ι ℤ
                    (n' : FreeRing (X := X) c)) *
                  pbwWord c hc R right := by rw [hswap]
          _ = _ := by noncomm_ring
      rw [hidentity, map_add,
        ih (i :: right) hprincipal hprincipalFactors,
        functional_pbwWord_mul_derivedRelation_mul_pbwWord
          c hc R Z hZ ell left right n' hcorrection,
        add_zero]

theorem centralImage_eq_zero_of_mem
    (Z : LieIdeal ℤ (Quotient c R))
    {p : FreeRing (X := X) c} (hp : quotientMap c R p ∈ Z) :
    centralImage c R Z p = 0 := by
  apply (LieSubmodule.Quotient.mk_eq_zero' (N := Z)).mpr
  exact hp

/-- Centrality of a Smith correction in the quotient says exactly that its
bracket with any free element is a zero-head relation. -/
theorem bracket_correction_mem_R
    (j i : Fin (relationRank c hc R)) (hji : j < i)
    (x : FreeRing (X := X) c) :
    ⁅x, correction c hc R i j⁆ ∈ R := by
  apply (LieSubmodule.Quotient.mk_eq_zero' (N := R)).mp
  change quotientMap c R ⁅x, correction c hc R i j⁆ = 0
  rw [LieHom.map_lie]
  have hcenter := correction_mem_center c hc R j i hji
  rw [LieModule.mem_maxTrivSubmodule] at hcenter
  exact hcenter (quotientMap c R x)

/-- A terminal branch carrying a Smith correction `qᵢⱼ` is invisible once
the branch has at least two factors. -/
theorem functional_pbwWord_mul_correction_mul_pbwWord
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (hcorrection : ∀ (j i : Fin (relationRank c hc R)), j < i →
      quotientMap c R (correction c hc R i j) ∈ Z)
    (j i : Fin (relationRank c hc R)) (hji : j < i)
    (left right : List (PBWIndex c hc R))
    (hordered : (left ++ right).Pairwise (· ≤ ·))
    (hfactors : 2 ≤ left.length + right.length + 1) :
    functional c hc R Z hZ ell
      (pbwWord c hc R left *
        UniversalEnvelopingAlgebra.ι ℤ (correction c hc R i j) *
          pbwWord c hc R right) = 0 := by
  apply functional_pbwWord_mul_centralFactor_mul_pbwWord
    c hc R Z hZ ell (correction c hc R i j)
      (degreeOne_correction c hc R i j)
      (centralImage_eq_zero_of_mem c R Z (hcorrection j i hji))
      (fun x ↦ bracket_correction_mem_R c hc R j i hji x)
      left right hordered hfactors

/-! #### Inserting a Smith head -/

/-- The PBW index of the `i`th Smith generator. -/
def smithHeadIndex (i : Fin (relationRank c hc R)) : PBWIndex c hc R :=
  Sum.inr (Fin.castLE (smith c hc R).relationRank_le i)

@[simp] theorem pbwBasis_smithHeadIndex
    (i : Fin (relationRank c hc R)) :
    pbwBasis c hc R (smithHeadIndex c hc R i) =
      generator c hc R (Fin.castLE (smith c hc R).relationRank_le i) := by
  simpa only [smithHeadIndex] using pbwBasis_generator c hc R
    (Fin.castLE (smith c hc R).relationRank_le i)

/-- The correction produced when the `i`th Smith head crosses a derived
basis factor belongs to `N`; equation (7) is built into its proof. -/
def smithDerivedCorrection
    (i : Fin (relationRank c hc R)) (j : DerivedIndex c hc R) :
    derivedRelations c hc R := by
  let x := generator c hc R
    (Fin.castLE (smith c hc R).relationRank_le i)
  let m := pbwBasis c hc R (Sum.inl j)
  let q : FreeRing (X := X) c :=
    ((smith c hc R).diagonal i : ℤ) • ⁅x, m⁆
  have htailzero : ⁅rowTail c hc R i, m⁆ = 0 :=
    bracket_eq_zero_of_degreeOne_eq_zero c hc
      (degreeOne_rowTail c hc R i) (degreeOne_pbwBasis_derived c hc R j)
  have hq : q = ⁅(row c hc R i : FreeRing (X := X) c), m⁆ := by
    rw [row_eq_head_add_tail, add_lie, zsmul_lie, htailzero, add_zero]
  refine ⟨q, ?_, ?_⟩
  · rw [hq]
    exact lie_mem_left ℤ (FreeRing (X := X) c) R
      (row c hc R i : FreeRing (X := X) c) m (row c hc R i).property
  · change FreeMetabelian.Free.degreeOneLinear hc
        (((smith c hc R).diagonal i : ℤ) • ⁅x, m⁆) = 0
    rw [map_zsmul]
    change ((smith c hc R).diagonal i : ℤ) • 0 = 0
    simp

@[simp] theorem smithDerivedCorrection_coe
    (i : Fin (relationRank c hc R)) (j : DerivedIndex c hc R) :
    (smithDerivedCorrection c hc R i j : FreeRing (X := X) c) =
      ((smith c hc R).diagonal i : ℤ) •
        ⁅generator c hc R (Fin.castLE (smith c hc R).relationRank_le i),
          pbwBasis c hc R (Sum.inl j)⁆ := by
  rfl

/-- A generator strictly below the `i`th Smith head is itself one of the
earlier Smith directions. -/
def earlierRelationIndex (i : Fin (relationRank c hc R))
    (j : Fin (generatorRank c hc R))
    (hji : (Sum.inr j : PBWIndex c hc R) < smithHeadIndex c hc R i) :
    Fin (relationRank c hc R) :=
  ⟨j.val, by
    have hval : j.val < i.val := by
      change (Sum.inr j : PBWIndex c hc R) <
        Sum.inr (Fin.castLE (smith c hc R).relationRank_le i) at hji
      rw [generatorIndex_lt_generatorIndex c hc R] at hji
      exact hji
    exact hval.trans i.isLt⟩

theorem earlierRelationIndex_lt
    (i : Fin (relationRank c hc R))
    (j : Fin (generatorRank c hc R))
    (hji : (Sum.inr j : PBWIndex c hc R) < smithHeadIndex c hc R i) :
    earlierRelationIndex c hc R i j hji < i := by
  have hval : j.val < i.val := by
    change (Sum.inr j : PBWIndex c hc R) <
      Sum.inr (Fin.castLE (smith c hc R).relationRank_le i) at hji
    rw [generatorIndex_lt_generatorIndex c hc R] at hji
    exact hji
  exact hval

theorem cast_earlierRelationIndex
    (i : Fin (relationRank c hc R))
    (j : Fin (generatorRank c hc R))
    (hji : (Sum.inr j : PBWIndex c hc R) < smithHeadIndex c hc R i) :
    Fin.castLE (smith c hc R).relationRank_le
        (earlierRelationIndex c hc R i j hji) = j := by
  apply Fin.ext
  rfl

/-- The scalar commutator created at a lower generator is literally the
central Smith correction `qᵢⱼ`. -/
theorem smithHead_cross_generator
    (i : Fin (relationRank c hc R))
    (j : Fin (generatorRank c hc R))
    (hji : (Sum.inr j : PBWIndex c hc R) < smithHeadIndex c hc R i) :
    ((smith c hc R).diagonal i : ℤ) •
        ⁅generator c hc R (Fin.castLE (smith c hc R).relationRank_le i),
          pbwBasis c hc R (Sum.inr j)⁆ =
      correction c hc R i (earlierRelationIndex c hc R i j hji) := by
  rw [pbwBasis_generator, correction, cast_earlierRelationIndex]

private theorem pairwise_insert_middle
    (a : PBWIndex c hc R)
    (left right : List (PBWIndex c hc R))
    (hleft : left.Pairwise (· ≤ ·))
    (hright : right.Pairwise (· ≤ ·))
    (hla : ∀ x ∈ left, x ≤ a)
    (har : ∀ y ∈ right, a ≤ y) :
    (left ++ a :: right).Pairwise (· ≤ ·) := by
  rw [List.pairwise_append]
  refine ⟨hleft, ?_, ?_⟩
  · rw [List.pairwise_cons]
    exact ⟨har, hright⟩
  · intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hla x hx
    · exact (hla x hx).trans (har y hy)

/-- If a Smith head has reached its ordered position, its branch has one
more factor than the multiplier and hence is invisible for multipliers of
length at least two. -/
theorem functional_ordered_smithHead_branch
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (i : Fin (relationRank c hc R))
    (left right : List (PBWIndex c hc R))
    (hordered : (left ++ smithHeadIndex c hc R i :: right).Pairwise (· ≤ ·))
    (hfactors : 2 ≤ left.length + right.length) :
    functional c hc R Z hZ ell
      (pbwWord c hc R left *
        (((smith c hc R).diagonal i : ℤ) •
          UniversalEnvelopingAlgebra.ι ℤ
            (generator c hc R
              (Fin.castLE (smith c hc R).relationRank_le i))) *
        pbwWord c hc R right) = 0 := by
  have hlength : (left ++ smithHeadIndex c hc R i :: right).length ≠ 1 := by
    simp only [List.length_append, List.length_cons]
    omega
  have hlength2 : (left ++ smithHeadIndex c hc R i :: right).length ≠ 2 := by
    simp only [List.length_append, List.length_cons]
    omega
  have hzero := functional_basisWord_eq_zero c hc R Z hZ ell
    (left ++ smithHeadIndex c hc R i :: right) hordered hlength hlength2
  have heq :
      pbwWord c hc R left *
          (((smith c hc R).diagonal i : ℤ) •
            UniversalEnvelopingAlgebra.ι ℤ
              (generator c hc R
                (Fin.castLE (smith c hc R).relationRank_le i))) *
          pbwWord c hc R right =
        ((smith c hc R).diagonal i : ℤ) •
          pbwWord c hc R
            (left ++ smithHeadIndex c hc R i :: right) := by
    rw [pbwWord_append, pbwWord_cons, pbwBasis_smithHeadIndex]
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    noncomm_ring
  rw [heq, map_zsmul]
  change ((smith c hc R).diagonal i : ℤ) •
    functional c hc R Z hZ ell
      (basisWord ℤ (FreeRing (X := X) c) (PBWIndex c hc R)
        (pbwBasis c hc R)
        (left ++ smithHeadIndex c hc R i :: right)) = 0
  rw [hzero, smul_zero]

/-- Exact adjacent insertion of `dᵢxᵢ`.  At a derived crossing the
correction is (7); at a lower generator crossing it is `qᵢⱼ`. -/
theorem functional_smithHead_branch
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (hcorrection : ∀ (j i : Fin (relationRank c hc R)), j < i →
      quotientMap c R (correction c hc R i j) ∈ Z)
    (i : Fin (relationRank c hc R))
    (left right : List (PBWIndex c hc R))
    (hordered : (left ++ right).Pairwise (· ≤ ·))
    (hleft : ∀ x ∈ left, x ≤ smithHeadIndex c hc R i)
    (hfactors : 2 ≤ left.length + right.length) :
    functional c hc R Z hZ ell
      (pbwWord c hc R left *
        (((smith c hc R).diagonal i : ℤ) •
          UniversalEnvelopingAlgebra.ι ℤ
            (generator c hc R
              (Fin.castLE (smith c hc R).relationRank_le i))) *
        pbwWord c hc R right) = 0 := by
  induction right generalizing left with
  | nil =>
      have hparts := List.pairwise_append.mp hordered
      have hinsert :
          (left ++ smithHeadIndex c hc R i :: []).Pairwise (· ≤ ·) :=
        pairwise_insert_middle c hc R (smithHeadIndex c hc R i)
          left [] hparts.1 (by simp) hleft (by simp)
      exact functional_ordered_smithHead_branch
        c hc R Z hZ ell i left [] hinsert (by simpa using hfactors)
  | cons j js ih =>
      by_cases hstop : smithHeadIndex c hc R i ≤ j
      · have hparts := List.pairwise_append.mp hordered
        have hright := hparts.2.1
        have hjtail : ∀ y ∈ js, j ≤ y :=
          (List.pairwise_cons.mp hright).1
        have hheadRight : ∀ y ∈ j :: js,
            smithHeadIndex c hc R i ≤ y := by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hstop
          · exact hstop.trans (hjtail y hy)
        have hinsert :
            (left ++ smithHeadIndex c hc R i :: j :: js).Pairwise (· ≤ ·) :=
          pairwise_insert_middle c hc R (smithHeadIndex c hc R i)
            left (j :: js) hparts.1 hright hleft hheadRight
        exact functional_ordered_smithHead_branch
          c hc R Z hZ ell i left (j :: js) hinsert hfactors
      · have hjlt : j < smithHeadIndex c hc R i := lt_of_not_ge hstop
        have hprincipalOrdered : ((left ++ [j]) ++ js).Pairwise (· ≤ ·) := by
          simpa [List.append_assoc] using hordered
        have hsub : (left ++ js).Sublist (left ++ j :: js) :=
          (List.Sublist.cons j (List.Sublist.refl js)).append_left left
        have hcorrectionOrdered : (left ++ js).Pairwise (· ≤ ·) :=
          List.Pairwise.sublist hsub hordered
        have hleft' : ∀ x ∈ left ++ [j],
            x ≤ smithHeadIndex c hc R i := by
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · exact hleft x hx
          · simp only [List.mem_singleton] at hx
            subst x
            exact hjlt.le
        have hfactors' : 2 ≤ (left ++ [j]).length + js.length := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hfactors
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        let x := generator c hc R
          (Fin.castLE (smith c hc R).relationRank_le i)
        let y := pbwBasis c hc R j
        let d : ℤ := (smith c hc R).diagonal i
        let cross : FreeRing (X := X) c := d • ⁅x, y⁆
        have hswap :
            (d • UniversalEnvelopingAlgebra.ι ℤ x) *
                UniversalEnvelopingAlgebra.ι ℤ y =
              UniversalEnvelopingAlgebra.ι ℤ y *
                  (d • UniversalEnvelopingAlgebra.ι ℤ x) +
                UniversalEnvelopingAlgebra.ι ℤ cross := by
          have hbase := UEA.iota_mul_iota_swap ℤ (FreeRing (X := X) c) x y
          calc
            (d • UniversalEnvelopingAlgebra.ι ℤ x) *
                UniversalEnvelopingAlgebra.ι ℤ y =
              d • (UniversalEnvelopingAlgebra.ι ℤ x *
                UniversalEnvelopingAlgebra.ι ℤ y) := by
                  rw [smul_mul_assoc]
            _ = d • (UniversalEnvelopingAlgebra.ι ℤ y *
                  UniversalEnvelopingAlgebra.ι ℤ x +
                UniversalEnvelopingAlgebra.ι ℤ ⁅x, y⁆) :=
              congrArg (d • ·) hbase
            _ = _ := by
              rw [smul_add, mul_smul_comm, ← map_zsmul]
        have hidentity :
            pbwWord c hc R left *
                (d • UniversalEnvelopingAlgebra.ι ℤ x) *
                  pbwWord c hc R (j :: js) =
              pbwWord c hc R (left ++ [j]) *
                  (d • UniversalEnvelopingAlgebra.ι ℤ x) *
                    pbwWord c hc R js +
                pbwWord c hc R left *
                  UniversalEnvelopingAlgebra.ι ℤ cross *
                    pbwWord c hc R js := by
          simp only [pbwWord_append, pbwWord_cons, pbwWord_nil, mul_one]
          calc
            _ = pbwWord c hc R left *
                ((d • UniversalEnvelopingAlgebra.ι ℤ x) *
                  UniversalEnvelopingAlgebra.ι ℤ y) *
                    pbwWord c hc R js := by noncomm_ring
            _ = pbwWord c hc R left *
                (UniversalEnvelopingAlgebra.ι ℤ y *
                    (d • UniversalEnvelopingAlgebra.ι ℤ x) +
                  UniversalEnvelopingAlgebra.ι ℤ cross) *
                    pbwWord c hc R js := by rw [hswap]
            _ = _ := by noncomm_ring
        rw [hidentity, map_add]
        have hprincipal := ih (left ++ [j]) hprincipalOrdered hleft' hfactors'
        change functional c hc R Z hZ ell
            (pbwWord c hc R (left ++ [j]) *
              (d • UniversalEnvelopingAlgebra.ι ℤ x) *
                pbwWord c hc R js) +
          functional c hc R Z hZ ell
            (pbwWord c hc R left *
              UniversalEnvelopingAlgebra.ι ℤ cross *
                pbwWord c hc R js) = 0
        rw [show functional c hc R Z hZ ell
            (pbwWord c hc R (left ++ [j]) *
              (d • UniversalEnvelopingAlgebra.ι ℤ x) *
                pbwWord c hc R js) = 0 by exact hprincipal]
        cases j with
        | inl j =>
            have hN := functional_pbwWord_mul_derivedRelation_mul_pbwWord
              c hc R Z hZ ell left js
                (smithDerivedCorrection c hc R i j) hcorrectionOrdered
            have hcross : cross =
                (smithDerivedCorrection c hc R i j : FreeRing (X := X) c) := by
              exact (smithDerivedCorrection_coe c hc R i j).symm
            rw [hcross, hN, add_zero]
        | inr j =>
            let a := earlierRelationIndex c hc R i j hjlt
            have haj : a < i := earlierRelationIndex_lt c hc R i j hjlt
            have hq := functional_pbwWord_mul_correction_mul_pbwWord
              c hc R Z hZ ell hcorrection a i haj left js
                hcorrectionOrdered (by
                  simp only [List.length_cons] at hfactors
                  omega)
            have hcross : cross = correction c hc R i a := by
              exact smithHead_cross_generator c hc R i j hjlt
            rw [hcross, hq, add_zero]

/-- The `dᵢxᵢ` part of a Smith row is invisible on every ordered
multiplier having at least two factors. -/
theorem functional_smithHead_mul_pbwWord
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (hcorrection : ∀ (j i : Fin (relationRank c hc R)), j < i →
      quotientMap c R (correction c hc R i j) ∈ Z)
    (i : Fin (relationRank c hc R))
    (is : List (PBWIndex c hc R)) (his : is.Pairwise (· ≤ ·))
    (hfactors : 2 ≤ is.length) :
    functional c hc R Z hZ ell
      ((((smith c hc R).diagonal i : ℤ) •
        UniversalEnvelopingAlgebra.ι ℤ
          (generator c hc R
            (Fin.castLE (smith c hc R).relationRank_le i))) *
        pbwWord c hc R is) = 0 := by
  simpa using functional_smithHead_branch
    c hc R Z hZ ell hcorrection i [] is his (by simp) (by simpa using hfactors)

/-- Each full Smith row is invisible on the left of an ordered PBW word.
For multipliers of length zero or one this uses the full relation; only from
length two onward is the row split into its head and derived tail. -/
theorem functional_row_mul_pbwWord
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (hcorrection : ∀ (j i : Fin (relationRank c hc R)), j < i →
      quotientMap c R (correction c hc R i j) ∈ Z)
    (i : Fin (relationRank c hc R))
    (is : List (PBWIndex c hc R)) (his : is.Pairwise (· ≤ ·)) :
    functional c hc R Z hZ ell
      (UniversalEnvelopingAlgebra.ι ℤ
          (row c hc R i : FreeRing (X := X) c) * pbwWord c hc R is) = 0 := by
  cases is with
  | nil =>
      rw [pbwWord_nil, mul_one, functional_iota, quotientMap_row, map_zero]
  | cons j is =>
      cases is with
      | nil =>
          rw [pbwWord_cons, pbwWord_nil, mul_one,
            functional_iota_mul_iota]
          simp [centralImage, quotientMap_row]
      | cons k ks =>
          have hhead := functional_smithHead_mul_pbwWord
            c hc R Z hZ ell hcorrection i (j :: k :: ks) his (by simp)
          have htail := functional_degreeZero_mul_pbwWord_of_two_le
            c hc R Z hZ ell (rowTail c hc R i)
              (degreeOne_rowTail c hc R i) (j :: k :: ks) his (by simp)
          rw [row_eq_head_add_tail, map_add, map_zsmul, add_mul, map_add]
          rw [hhead, htail, add_zero]

/-- Every defining relation, not merely a chosen Smith row, is invisible on
the left of an ordered PBW word. -/
theorem functional_relation_mul_pbwWord
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (hcorrection : ∀ (j i : Fin (relationRank c hc R)), j < i →
      quotientMap c R (correction c hc R i j) ∈ Z)
    (rho : R)
    (is : List (PBWIndex c hc R)) (his : is.Pairwise (· ≤ ·)) :
    functional c hc R Z hZ ell
      (UniversalEnvelopingAlgebra.ι ℤ
          (rho : FreeRing (X := X) c) * pbwWord c hc R is) = 0 := by
  obtain ⟨n, a, hrho⟩ := relation_decomposition c hc R rho
  rw [hrho, map_add, map_sum, add_mul, Finset.sum_mul,
    map_add, map_sum]
  rw [functional_derivedRelation_mul_pbwWord c hc R Z hZ ell n is his,
    zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_zsmul, smul_mul_assoc, map_zsmul,
    functional_row_mul_pbwWord c hc R Z hZ ell hcorrection i is his,
    smul_zero]

/-- The row lemma for an arbitrary enveloping-algebra multiplier. -/
theorem functional_relation_mul
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (hcorrection : ∀ (j i : Fin (relationRank c hc R)), j < i →
      quotientMap c R (correction c hc R i j) ∈ Z)
    (rho : R) (u : UEA ℤ (FreeRing (X := X) c)) :
    functional c hc R Z hZ ell
      (UniversalEnvelopingAlgebra.ι ℤ
        (rho : FreeRing (X := X) c) * u) = 0 := by
  let B := weightedPBWBasis c hc R
  let f : MvPolynomial (PBWIndex c hc R) ℤ := B.pbwEquiv.symm u
  have hu : B.pbwEquiv f = u := B.pbwEquiv.apply_symm_apply u
  rw [← hu, f.as_sum, map_sum, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro e he
  let is := (Finsupp.toMultiset e).sort (· ≤ ·)
  have his : is.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hword : orderedMonomial ℤ (FreeRing (X := X) c)
      (PBWIndex c hc R) (pbwBasis c hc R) e = pbwWord c hc R is := by
    have h := orderedMonomial_multiset_toFinsupp
      ℤ (FreeRing (X := X) c) (PBWIndex c hc R)
        (pbwBasis c hc R) is his
    simpa [is, pbwWord] using h
  rw [B.pbwEquiv_monomial, mul_smul_comm, map_zsmul]
  change MvPolynomial.coeff e f •
      functional c hc R Z hZ ell
        (UniversalEnvelopingAlgebra.ι ℤ
          (rho : FreeRing (X := X) c) *
            orderedMonomial ℤ (FreeRing (X := X) c)
              (PBWIndex c hc R) (pbwBasis c hc R) e) = 0
  rw [hword,
    functional_relation_mul_pbwWord c hc R Z hZ ell hcorrection rho is his,
    smul_zero]

/-- Lemma 2 of the manuscript: `Λ(RU(F))=0`. -/
theorem functional_mem_idealOfLieIdeal
    (Z : LieIdeal ℤ (Quotient c R))
    (hZ : Z ≤ LieAlgebra.center ℤ (Quotient c R))
    (ell : CharacterModule (Quotient c R))
    (hcorrection : ∀ (j i : Fin (relationRank c hc R)), j < i →
      quotientMap c R (correction c hc R i j) ∈ Z)
    {u : UEA ℤ (FreeRing (X := X) c)}
    (hu : u ∈ UEA.idealOfLieIdeal ℤ (FreeRing (X := X) c) R) :
    functional c hc R Z hZ ell u = 0 := by
  rw [UEA.mem_idealOfLieIdeal_iff_relation_sum] at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨rho, v, rfl⟩ := hu
      exact functional_relation_mul c hc R Z hZ ell hcorrection rho v
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx =>
      calc
        functional c hc R Z hZ ell (a • x) =
            a • functional c hc R Z hZ ell x := map_smul _ _ _
        _ = 0 := by rw [hx, smul_zero]

/-! ### The PBW weight cutoff -/

/-- The presented quotient inherits the class-`c` cutoff of the relatively
free ring.  This is the zero-based convention: its `c`th lower-central term
is zero. -/
theorem quotient_lowerCentralSeries_cutoff_eq_bot :
    lowerCentralSeries ℤ (Quotient c R) c = ⊥ := by
  change LieModule.lowerCentralSeries ℤ (Quotient c R) (Quotient c R) c = ⊥
  rw [← LieIdeal.lowerCentralSeries_map_eq c (quotientMap_surjective c R)]
  rw [FreeMetabelian.Free.lowerCentralSeries_cutoff_eq_bot]
  simp

/-- In a class-at-most-`c` Lie ring, the preceding lower-central term is
central. -/
theorem quotient_lowerCentralSeries_pred_le_center (hc2 : 2 ≤ c) :
    lowerCentralSeries ℤ (Quotient c R) (c - 1) ≤
      LieAlgebra.center ℤ (Quotient c R) := by
  intro x hx
  rw [LieModule.mem_maxTrivSubmodule]
  intro y
  have hbr : ⁅y, x⁆ ∈ lowerCentralSeries ℤ (Quotient c R) c := by
    have hbr' : ⁅y, x⁆ ∈
        LieModule.lowerCentralSeries ℤ (Quotient c R) (Quotient c R)
          ((c - 1) + 1) := by
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (by simp) hx
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ c)] using hbr'
  rw [quotient_lowerCentralSeries_cutoff_eq_bot c R] at hbr
  simpa using hbr

/-- A homogeneous PBW basis factor of maximal weight maps to the center of
the presented quotient. -/
theorem quotientMap_pbwBasis_mem_center_of_weight_eq_cutoff
    (hc2 : 2 ≤ c) (i : PBWIndex c hc R)
    (hi : pbwWeight c hc R i = c) :
    quotientMap c R (pbwBasis c hc R i) ∈
      LieAlgebra.center ℤ (Quotient c R) := by
  have hs : (pbwIndexEquiv c hc R i).1.val = c - 1 := by
    simp only [pbwWeight] at hi
    omega
  have hfree : pbwBasis c hc R i ∈
      lowerCentralSeries ℤ (FreeRing (X := X) c) (c - 1) := by
    rw [pbwBasis_apply]
    simpa only [hs] using
      (FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
        (generatorBasis c hc R)
        (pbwIndexEquiv c hc R i).1.val
        (pbwIndexEquiv c hc R i).1.isLt
        (FreeMetabelian.Free.pieceBasis (generatorBasis c hc R)
          (pbwIndexEquiv c hc R i).1.val
          (pbwIndexEquiv c hc R i).2))
  apply quotient_lowerCentralSeries_pred_le_center c R hc2
  apply (LieIdeal.map_lowerCentralSeries_le
    (R := ℤ) (f := quotientMap c R) (c - 1))
  exact LieIdeal.mem_map hfree

/-- With the center chosen as `Z`, every maximal-weight PBW factor has zero
image in `W=K/Z`. -/
theorem basisImage_center_eq_zero_of_weight_eq_cutoff
    (hc2 : 2 ≤ c) (i : PBWIndex c hc R)
    (hi : pbwWeight c hc R i = c) :
    basisImage c hc R (LieAlgebra.center ℤ (Quotient c R)) i = 0 := by
  exact centralImage_eq_zero_of_mem c R
    (LieAlgebra.center ℤ (Quotient c R))
    (quotientMap_pbwBasis_mem_center_of_weight_eq_cutoff
      c hc R hc2 i hi)

private theorem pbwWeight_toMultiset (e : PBWIndex c hc R →₀ ℕ) :
    Finsupp.weight (pbwWeight c hc R) e =
      (Finsupp.toMultiset e |>.map (pbwWeight c hc R)).sum := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | @single_add i m e hi hm ih =>
      rw [map_add, Finsupp.toMultiset_add, Multiset.map_add,
        Multiset.sum_add, ih, Finsupp.toMultiset_single,
        Finsupp.weight_single, Multiset.map_nsmul, Multiset.sum_nsmul,
        Multiset.map_singleton, Multiset.sum_singleton]

/-- Sorting a PBW exponent multiset does not change its total bracket
weight. -/
private theorem sorted_pbwWeight (e : PBWIndex c hc R →₀ ℕ) :
    ((((Finsupp.toMultiset e).sort (· ≤ ·)).map
      (pbwWeight c hc R)).sum) =
        (weightedPBWBasis c hc R).bracketWeight e := by
  rw [← Multiset.sum_coe]
  change (Multiset.map (pbwWeight c hc R)
    (Multiset.ofList ((Finsupp.toMultiset e).sort (· ≤ ·)))).sum = _
  rw [Multiset.sort_eq]
  exact (pbwWeight_toMultiset c hc R e).symm.trans
    ((weightedPBWBasis c hc R).bracketWeight_eq_finsupp_weight e).symm

private theorem pbwWeight_le_cutoff (i : PBWIndex c hc R) :
    pbwWeight c hc R i ≤ c := by
  change (pbwIndexEquiv c hc R i).1.val + 1 ≤ c
  omega

/-- The literal weight-counting argument following (11): every ordered PBW
monomial of weight at least `2c-1` is invisible to `Λ`. -/
theorem functional_orderedMonomial_eq_zero_of_weight_ge_cutoff
    (hc2 : 2 ≤ c) (ell : CharacterModule (Quotient c R))
    (e : PBWIndex c hc R →₀ ℕ)
    (he : 2 * c - 1 ≤ (weightedPBWBasis c hc R).bracketWeight e) :
    functional c hc R (LieAlgebra.center ℤ (Quotient c R)) le_rfl ell
      (orderedMonomial ℤ (FreeRing (X := X) c) (PBWIndex c hc R)
        (pbwBasis c hc R) e) = 0 := by
  let is := (Finsupp.toMultiset e).sort (· ≤ ·)
  have his : is.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hweight : (is.map (pbwWeight c hc R)).sum =
      (weightedPBWBasis c hc R).bracketWeight e := by
    exact sorted_pbwWeight c hc R e
  have hword : orderedMonomial ℤ (FreeRing (X := X) c)
      (PBWIndex c hc R) (pbwBasis c hc R) e = pbwWord c hc R is := by
    have h := orderedMonomial_multiset_toFinsupp
      ℤ (FreeRing (X := X) c) (PBWIndex c hc R)
        (pbwBasis c hc R) is his
    simpa [is, pbwWord] using h
  rw [hword]
  generalize hshape : is = xs at his hweight ⊢
  cases xs with
  | nil =>
      simpa [pbwWord] using
        (functional_basisWord_eq_zero c hc R
          (LieAlgebra.center ℤ (Quotient c R)) le_rfl ell
          [] (by simp) (by simp) (by simp))
  | cons i is =>
      cases is with
      | nil =>
          have hiBound := pbwWeight_le_cutoff c hc R i
          simp only [List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, add_zero] at hweight
          exfalso
          omega
      | cons j is =>
          cases is with
          | nil =>
              have hij : i ≤ j := by simpa using his
              have hiBound := pbwWeight_le_cutoff c hc R i
              have hjBound := pbwWeight_le_cutoff c hc R j
              simp only [List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil, add_zero] at hweight
              have htop : pbwWeight c hc R i = c ∨
                  pbwWeight c hc R j = c := by
                omega
              simp only [pbwWord_cons, pbwWord_nil, mul_one]
              rw [functional_basisWord_two c hc R
                (LieAlgebra.center ℤ (Quotient c R)) le_rfl ell i j hij]
              rcases htop with hi | hj
              · rw [basisImage_center_eq_zero_of_weight_eq_cutoff
                    c hc R hc2 i hi]
                simp
              · rw [basisImage_center_eq_zero_of_weight_eq_cutoff
                    c hc R hc2 j hj]
                simp
          | cons k ks =>
              simpa [pbwWord] using
                (functional_basisWord_eq_zero c hc R
                  (LieAlgebra.center ℤ (Quotient c R)) le_rfl ell
                  (i :: j :: k :: ks) his (by simp) (by simp))

/-- The second vanishing used after (11): `Λ` kills the
`(2c-1)`st augmentation power. -/
theorem functional_mem_augmentationIdeal_pow_cutoff
    (hc2 : 2 ≤ c) (ell : CharacterModule (Quotient c R))
    {u : UEA ℤ (FreeRing (X := X) c)}
    (hu : u ∈ UEA.augmentationIdeal ℤ (FreeRing (X := X) c) ^
      (2 * c - 1)) :
    functional c hc R (LieAlgebra.center ℤ (Quotient c R)) le_rfl ell u = 0 := by
  let B := weightedPBWBasis c hc R
  have huWeight : u ∈ B.weightGE (2 * c - 1) := by
    rw [← B.augmentationIdeal_pow_eq_weightGE]
    exact hu
  let f : MvPolynomial (PBWIndex c hc R) ℤ := B.pbwEquiv.symm u
  have huf : B.pbwEquiv f = u := B.pbwEquiv.apply_symm_apply u
  rw [← huf, f.as_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro e heSupport
  have heWeight : 2 * c - 1 ≤ B.bracketWeight e := by
    by_contra h
    have hz := (B.mem_weightGE_iff (2 * c - 1) u).mp huWeight e
      (Nat.lt_of_not_ge h)
    exact Finsupp.mem_support_iff.mp heSupport hz
  rw [B.pbwEquiv_monomial, map_zsmul]
  change MvPolynomial.coeff e f •
      functional c hc R (LieAlgebra.center ℤ (Quotient c R)) le_rfl ell
        (orderedMonomial ℤ (FreeRing (X := X) c) (PBWIndex c hc R)
          (pbwBasis c hc R) e) = 0
  change 2 * c - 1 ≤
    (weightedPBWBasis c hc R).bracketWeight e at heWeight
  rw [
    functional_orderedMonomial_eq_zero_of_weight_ge_cutoff
      c hc R hc2 ell e heWeight, smul_zero]

/-! ### The finite relatively-free theorem -/

private theorem ker_quotientMap : LieHom.ker (quotientMap c R) = R := by
  apply SetLike.ext
  intro x
  change quotientMap c R x = 0 ↔ x ∈ R
  exact LieSubmodule.Quotient.mk_eq_zero' (N := R)

/-- Theorem 2 for a finite relatively-free presentation `K=F/R`.  This is
the contradiction after (11), expressed directly by character separation. -/
theorem dimensionSubring_quotient_eq_bot (hc2 : 2 ≤ c) :
    dimensionSubring ℤ (Quotient c R) (2 * c - 1) = ⊥ := by
  have hc : 0 < c := by omega
  rw [eq_bot_iff]
  intro a ha
  apply CharacterModule.eq_zero_of_character_apply
  intro ell
  obtain ⟨atilde, rfl⟩ := quotientMap_surjective c R a
  have haAug : UniversalEnvelopingAlgebra.ι ℤ (quotientMap c R atilde) ∈
      UEA.augmentationIdeal ℤ (Quotient c R) ^ (2 * c - 1) :=
    (mem_dimensionSubring ℤ (Quotient c R)).mp ha
  have haAug' : UniversalEnvelopingAlgebra.ι ℤ (quotientMap c R atilde) ∈
      UEA.augmentationIdeal ℤ (Quotient c R) ^ ((2 * c - 2) + 1) := by
    simpa only [show 2 * c - 2 + 1 = 2 * c - 1 by omega] using haAug
  obtain ⟨v, hv, hvMap⟩ :=
    UEA.exists_mem_augmentationIdeal_pow_succ_of_surjective ℤ
      (FreeRing (X := X) c) (Quotient c R) (quotientMap c R)
      (quotientMap_surjective c R) (2 * c - 2) haAug'
  let relationPart : UEA ℤ (FreeRing (X := X) c) :=
    UniversalEnvelopingAlgebra.ι ℤ atilde - v
  have hrelationMap : UEA.map ℤ (FreeRing (X := X) c) (Quotient c R)
      (quotientMap c R) relationPart = 0 := by
    dsimp only [relationPart]
    rw [map_sub, UEA.map_ι, hvMap, sub_self]
  have hrelation : relationPart ∈
      UEA.idealOfLieIdeal ℤ (FreeRing (X := X) c) R := by
    have h := (LieRings.PBW.WeightedBasis.mem_ker_map_iff_mem_idealOfLieIdeal
      (quotientMap c R) (quotientMap_surjective c R) relationPart).mp
        hrelationMap
    rwa [ker_quotientMap c R] at h
  have hcorrection : ∀ (j i : Fin (relationRank c hc R)), j < i →
      quotientMap c R (correction c hc R i j) ∈
        LieAlgebra.center ℤ (Quotient c R) := by
    intro j i hji
    exact correction_mem_center c hc R j i hji
  have hrelationZero := functional_mem_idealOfLieIdeal c hc R
    (LieAlgebra.center ℤ (Quotient c R)) le_rfl ell hcorrection hrelation
  have hv' : v ∈ UEA.augmentationIdeal ℤ (FreeRing (X := X) c) ^
      (2 * c - 1) := by
    simpa only [show 2 * c - 2 + 1 = 2 * c - 1 by omega] using hv
  have hvZero := functional_mem_augmentationIdeal_pow_cutoff
    c hc R hc2 ell hv'
  have htotal : functional c hc R
      (LieAlgebra.center ℤ (Quotient c R)) le_rfl ell
        (UniversalEnvelopingAlgebra.ι ℤ atilde) = 0 := by
    have hdecomp : UniversalEnvelopingAlgebra.ι ℤ atilde =
        relationPart + v := by
      dsimp only [relationPart]
      abel
    rw [hdecomp, map_add, hrelationZero, hvZero, add_zero]
  rw [functional_iota] at htotal
  exact htotal

end Presentation

/-! ## Reduction to the finitely generated presentation -/

namespace FiniteReduction

variable {A : Type u} {B : Type v}

/-- Rename the generators of a free Lie ring. -/
def freeLieRename (e : A → B) :
    FreeLieAlgebra ℤ A →ₗ⁅ℤ⁆ FreeLieAlgebra ℤ B :=
  FreeLieAlgebra.lift ℤ (fun x ↦ FreeLieAlgebra.of ℤ (e x))

/-- Rename the generators of a free associative algebra. -/
def freeAssociativeRename (e : A → B) :
    FreeAlgebra ℤ A →ₐ[ℤ] FreeAlgebra ℤ B :=
  FreeAlgebra.lift ℤ (fun x ↦ FreeAlgebra.ι ℤ (e x))

@[simp] theorem freeLieRename_of (e : A → B) (x : A) :
    freeLieRename e (FreeLieAlgebra.of ℤ x) =
      FreeLieAlgebra.of ℤ (e x) := by
  exact FreeLieAlgebra.lift_of_apply _ _

@[simp] theorem freeAssociativeRename_ι (e : A → B) (x : A) :
    freeAssociativeRename e (FreeAlgebra.ι ℤ x) =
      FreeAlgebra.ι ℤ (e x) := by
  simp [freeAssociativeRename]

/-- Naturality of `U(FreeLie A) ≃ FreeAlgebra A` under a generator
renaming. -/
theorem universalEnvelopingEquivFreeAlgebra_natural
    (e : A → B) (u : UEA ℤ (FreeLieAlgebra ℤ A)) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ B
        (UEA.map ℤ (FreeLieAlgebra ℤ A) (FreeLieAlgebra ℤ B)
          (freeLieRename e) u) =
      freeAssociativeRename e
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ A u) := by
  let left : UEA ℤ (FreeLieAlgebra ℤ A) →ₐ[ℤ] FreeAlgebra ℤ B :=
    (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ B).toAlgHom.comp
      (UEA.map ℤ (FreeLieAlgebra ℤ A) (FreeLieAlgebra ℤ B)
        (freeLieRename e))
  let right : UEA ℤ (FreeLieAlgebra ℤ A) →ₐ[ℤ] FreeAlgebra ℤ B :=
    (freeAssociativeRename e).comp
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ A).toAlgHom
  change left u = right u
  suffices left = right by rw [this]
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  change left (UniversalEnvelopingAlgebra.ι ℤ x) =
    right (UniversalEnvelopingAlgebra.ι ℤ x)
  rw [show left (UniversalEnvelopingAlgebra.ι ℤ x) =
      FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ B
        (UEA.map ℤ (FreeLieAlgebra ℤ A) (FreeLieAlgebra ℤ B)
          (freeLieRename e) (UniversalEnvelopingAlgebra.ι ℤ x)) by rfl,
    UEA.map_ι]
  let lhs : FreeLieAlgebra ℤ A →ₗ⁅ℤ⁆ FreeAlgebra ℤ B :=
    (PBW.freeLieToFreeAlgebra ℤ B).comp (freeLieRename e)
  let rhs : FreeLieAlgebra ℤ A →ₗ⁅ℤ⁆ FreeAlgebra ℤ B :=
    (freeAssociativeRename e).toLieHom.comp
      (PBW.freeLieToFreeAlgebra ℤ A)
  have hnat : lhs = rhs := by
    apply FreeLieAlgebra.hom_ext
    intro z
    change PBW.freeLieToFreeAlgebra ℤ B
        (freeLieRename e (FreeLieAlgebra.of ℤ z)) =
      freeAssociativeRename e
        (PBW.freeLieToFreeAlgebra ℤ A (FreeLieAlgebra.of ℤ z))
    rw [freeLieRename_of]
    change (FreeLieAlgebra.lift ℤ (FreeAlgebra.ι ℤ))
        (FreeLieAlgebra.of ℤ (e z)) =
      freeAssociativeRename e
        ((FreeLieAlgebra.lift ℤ (FreeAlgebra.ι ℤ))
          (FreeLieAlgebra.of ℤ z))
    rw [FreeLieAlgebra.lift_of_apply, FreeLieAlgebra.lift_of_apply,
      freeAssociativeRename_ι]
  calc
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ B
        (UniversalEnvelopingAlgebra.ι ℤ (freeLieRename e x)) =
        PBW.freeLieToFreeAlgebra ℤ B (freeLieRename e x) :=
      FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
        B (freeLieRename e x)
    _ = freeAssociativeRename e (PBW.freeLieToFreeAlgebra ℤ A x) :=
      DFunLike.congr_fun hnat x
    _ = freeAssociativeRename e
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ A
          (UniversalEnvelopingAlgebra.ι ℤ x)) := by
      exact congrArg (freeAssociativeRename e)
        (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
          A x).symm

/-- Every free-associative polynomial uses finitely many generators. -/
private theorem exists_finset_fixedBy_freeAssociativeRename
    (a : FreeAlgebra ℤ A) :
    ∃ S : Finset A, ∀ e : A → A,
      (∀ x ∈ S, e x = x) → freeAssociativeRename e a = a := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 n =>
      refine ⟨∅, ?_⟩
      intro e he
      simp [freeAssociativeRename]
  | grade1 x =>
      refine ⟨{x}, ?_⟩
      intro e he
      simpa [freeAssociativeRename] using he x (by simp)
  | mul a b ha hb =>
      obtain ⟨Sa, ha⟩ := ha
      obtain ⟨Sb, hb⟩ := hb
      refine ⟨Sa ∪ Sb, ?_⟩
      intro e he
      rw [map_mul, ha e (fun x hx ↦ he x (Finset.mem_union_left _ hx)),
        hb e (fun x hx ↦ he x (Finset.mem_union_right _ hx))]
  | add a b ha hb =>
      obtain ⟨Sa, ha⟩ := ha
      obtain ⟨Sb, hb⟩ := hb
      refine ⟨Sa ∪ Sb, ?_⟩
      intro e he
      rw [map_add, ha e (fun x hx ↦ he x (Finset.mem_union_left _ hx)),
        hb e (fun x hx ↦ he x (Finset.mem_union_right _ hx))]

/-- A finite family of free-associative polynomials has a common finite
alphabet. -/
private theorem exists_finset_fixedBy_freeAssociativeRename_finset
    (T : Finset (FreeAlgebra ℤ A)) :
    ∃ S : Finset A, ∀ e : A → A,
      (∀ x ∈ S, e x = x) → ∀ a ∈ T, freeAssociativeRename e a = a := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨∅, fun _ _ _ h ↦ by simp at h⟩
  | @insert a T ha ih =>
      obtain ⟨Sa, hSa⟩ := exists_finset_fixedBy_freeAssociativeRename a
      obtain ⟨ST, hST⟩ := ih
      refine ⟨Sa ∪ ST, ?_⟩
      intro e he b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact hSa e (fun x hx ↦ he x (Finset.mem_union_left _ hx))
      · exact hST e (fun x hx ↦ he x (Finset.mem_union_right _ hx)) b hb

/-- A finite family in the enveloping algebra of a free Lie ring has a
common finite alphabet. -/
theorem exists_finset_fixedBy_ueaRename_finset
    (T : Finset (UEA ℤ (FreeLieAlgebra ℤ A))) :
    ∃ S : Finset A, ∀ e : A → A,
      (∀ x ∈ S, e x = x) → ∀ a ∈ T,
        UEA.map ℤ (FreeLieAlgebra ℤ A) (FreeLieAlgebra ℤ A)
          (freeLieRename e) a = a := by
  classical
  let E := FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ A
  obtain ⟨S, hS⟩ :=
    exists_finset_fixedBy_freeAssociativeRename_finset (T.image E)
  refine ⟨S, ?_⟩
  intro e he a ha
  apply E.injective
  rw [universalEnvelopingEquivFreeAlgebra_natural]
  exact hS e he (E a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-! ### The finite free-metabelian model attached to a finite alphabet -/

variable {S : Type u} [Finite S]

/-- Linear evaluation of the free Abelian group on a finite alphabet. -/
def finiteGeneratorMap {K : Type v} [LieRing K] (g : S → K) :
    (S →₀ ℤ) →ₗ[ℤ] K :=
  Finsupp.linearCombination ℤ g

@[simp] theorem finiteGeneratorMap_single
    {K : Type v} [LieRing K] (g : S → K) (s : S) :
    finiteGeneratorMap g (Finsupp.single s 1) = g s := by
  simp [finiteGeneratorMap]

/-- The canonical map from the free Lie ring on `S` to the truncated free
metabelian ring on the free Abelian group `ℤ[S]`. -/
def freeLieToFreeMetabelian (c : ℕ) (hc : 0 < c) :
    FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ FreeMetabelian.Free (S →₀ ℤ) c :=
  FreeLieAlgebra.lift ℤ (fun s ↦
    FreeMetabelian.Free.weightIncl 0 hc (Finsupp.single s 1))

@[simp] theorem freeLieToFreeMetabelian_of
    (c : ℕ) (hc : 0 < c) (s : S) :
    freeLieToFreeMetabelian c hc (FreeLieAlgebra.of ℤ s) =
      FreeMetabelian.Free.weightIncl 0 hc (Finsupp.single s 1) := by
  exact FreeLieAlgebra.lift_of_apply _ _

/-- Evaluation of the finite free-metabelian model agrees with ordinary
free-Lie evaluation on the same finite alphabet. -/
theorem finiteModel_evaluation_compatibility
    {K : Type v} [LieRing K]
    (c : ℕ) (hc : 0 < c)
    (hmeta : IsMetabelian K)
    (hclass : lowerCentralSeries ℤ K c = ⊥)
    (g : S → K) (z : FreeLieAlgebra ℤ S) :
    FreeMetabelian.Evaluation.lieHom hmeta hclass (finiteGeneratorMap g)
        (freeLieToFreeMetabelian c hc z) =
      FreeLieAlgebra.lift ℤ g z := by
  let lhs : FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ K :=
    (FreeMetabelian.Evaluation.lieHom hmeta hclass
      (finiteGeneratorMap g)).comp (freeLieToFreeMetabelian c hc)
  let rhs : FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ K :=
    FreeLieAlgebra.lift ℤ g
  have hmaps : lhs = rhs := by
    apply FreeLieAlgebra.hom_ext
    intro s
    change FreeMetabelian.Evaluation.lieHom hmeta hclass
        (finiteGeneratorMap g)
          (freeLieToFreeMetabelian c hc (FreeLieAlgebra.of ℤ s)) =
      FreeLieAlgebra.lift ℤ g (FreeLieAlgebra.of ℤ s)
    rw [freeLieToFreeMetabelian_of]
    change FreeMetabelian.Evaluation.lieHom hmeta hclass
        (finiteGeneratorMap g)
          (FreeMetabelian.Free.incl (⟨0, hc⟩ : Fin c)
            (Finsupp.single s 1)) = _
    rw [FreeMetabelian.Evaluation.lieHom_incl,
      FreeLieAlgebra.lift_of_apply]
    exact finiteGeneratorMap_single g s
  exact DFunLike.congr_fun hmaps z

/-- Evaluation on a subtype alphabet is canonical evaluation after including
that alphabet into the ambient generator type. -/
theorem freeLie_subtype_evaluation_compatibility
    {K : Type v} [LieRing K] (g : S → K) (z : FreeLieAlgebra ℤ S) :
    FreeLieAlgebra.lift ℤ g z =
      canonicalFreeLieEvaluation K
        (freeLieRename g z) := by
  let lhs : FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ K := FreeLieAlgebra.lift ℤ g
  let rhs : FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ K :=
    (canonicalFreeLieEvaluation K).comp (freeLieRename g)
  have hmaps : lhs = rhs := by
    apply FreeLieAlgebra.hom_ext
    intro s
    change FreeLieAlgebra.lift ℤ g (FreeLieAlgebra.of ℤ s) =
      canonicalFreeLieEvaluation K
        (freeLieRename g (FreeLieAlgebra.of ℤ s))
    rw [FreeLieAlgebra.lift_of_apply, freeLieRename_of,
      canonicalFreeLieEvaluation_of]
  exact DFunLike.congr_fun hmaps z

end FiniteReduction

/-! ## The nilpotent theorem for an arbitrary Lie ring -/

/-- **Nilpotent form of the odd-dimensional theorem.**  If a metabelian Lie
ring has class at most `c ≥ 2`, its `(2c-1)`st dimension subring is zero. -/
theorem nilpotent_dimensionSubring_eq_bot
    (c : ℕ) (K : Type u) [LieRing K]
    (hc2 : 2 ≤ c)
    (hmeta : IsMetabelian K)
    (hclass : lowerCentralSeries ℤ K c = ⊥) :
    dimensionSubring ℤ K (2 * c - 1) = ⊥ := by
  classical
  have hc : 0 < c := by omega
  rw [eq_bot_iff]
  intro a ha
  let canonicalEval := canonicalFreeLieEvaluation K
  let lift : FreeLieAlgebra ℤ K := FreeLieAlgebra.of ℤ a
  have haAug : UniversalEnvelopingAlgebra.ι ℤ a ∈
      UEA.augmentationIdeal ℤ K ^ (2 * c - 1) :=
    (mem_dimensionSubring ℤ K).mp ha
  have haAug' : UniversalEnvelopingAlgebra.ι ℤ a ∈
      UEA.augmentationIdeal ℤ K ^ ((2 * c - 2) + 1) := by
    simpa only [show 2 * c - 2 + 1 = 2 * c - 1 by omega] using haAug
  obtain ⟨highWord, hhighWord, hhighEval⟩ :=
    UEA.exists_mem_augmentationIdeal_pow_succ_of_surjective ℤ
      (FreeLieAlgebra ℤ K) K canonicalEval
      (canonicalFreeLieEvaluation_surjective K)
      (2 * c - 2) haAug'
  have hhighWord' : highWord ∈
      UEA.augmentationIdeal ℤ (FreeLieAlgebra ℤ K) ^ (2 * c - 1) := by
    simpa only [show 2 * c - 2 + 1 = 2 * c - 1 by omega] using hhighWord
  let relationPart : UEA ℤ (FreeLieAlgebra ℤ K) :=
    UniversalEnvelopingAlgebra.ι ℤ lift - highWord
  have hrelationMap :
      UEA.map ℤ (FreeLieAlgebra ℤ K) K canonicalEval relationPart = 0 := by
    dsimp only [relationPart]
    rw [map_sub, UEA.map_ι, hhighEval]
    have hliftEval : canonicalEval lift = a := by
      exact canonicalFreeLieEvaluation_of K a
    rw [hliftEval]
    rw [sub_self]
  have hrelationIdeal : relationPart ∈
      UEA.idealOfLieIdeal ℤ (FreeLieAlgebra ℤ K)
        (LieHom.ker canonicalEval) :=
    (LieRings.PBW.WeightedBasis.mem_ker_map_iff_mem_idealOfLieIdeal
      canonicalEval (canonicalFreeLieEvaluation_surjective K)
      relationPart).mp hrelationMap
  have hrelationSpan : relationPart ∈
      UEA.rightRelationSpan ℤ (FreeLieAlgebra ℤ K)
        (LieHom.ker canonicalEval) :=
    (UEA.mem_idealOfLieIdeal_iff_relation_sum ℤ
      (FreeLieAlgebra ℤ K) (LieHom.ker canonicalEval) relationPart).mp
        hrelationIdeal
  obtain ⟨coeff, hcoeff⟩ :=
    UEA.exists_relation_finsupp_of_mem_rightRelationSpan ℤ
      (FreeLieAlgebra ℤ K) (LieHom.ker canonicalEval) hrelationSpan
  let T : Finset (UEA ℤ (FreeLieAlgebra ℤ K)) :=
    insert (UniversalEnvelopingAlgebra.ι ℤ lift)
      (coeff.support.image fun p ↦
        UniversalEnvelopingAlgebra.ι ℤ
          (p.1 : FreeLieAlgebra ℤ K))
  obtain ⟨S₀, hS₀⟩ :=
    FiniteReduction.exists_finset_fixedBy_ueaRename_finset T
  let S : Finset K := insert a S₀
  let retract : K → S := fun y ↦
    if hy : y ∈ S then ⟨y, hy⟩ else ⟨a, Finset.mem_insert_self a S₀⟩
  have retract_coe {y : K} (hy : y ∈ S) : (retract y : K) = y := by
    simp [retract, hy]
  let forward : FreeLieAlgebra ℤ K →ₗ⁅ℤ⁆ FreeLieAlgebra ℤ S :=
    FiniteReduction.freeLieRename retract
  let backward : FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ FreeLieAlgebra ℤ K :=
    FiniteReduction.freeLieRename (fun y : S ↦ (y : K))
  let forwardUEA : UEA ℤ (FreeLieAlgebra ℤ K) →ₐ[ℤ]
      UEA ℤ (FreeLieAlgebra ℤ S) :=
    UEA.map ℤ (FreeLieAlgebra ℤ K) (FreeLieAlgebra ℤ S) forward
  let backwardUEA : UEA ℤ (FreeLieAlgebra ℤ S) →ₐ[ℤ]
      UEA ℤ (FreeLieAlgebra ℤ K) :=
    UEA.map ℤ (FreeLieAlgebra ℤ S) (FreeLieAlgebra ℤ K) backward
  have hcomposite : backward.comp forward =
      FiniteReduction.freeLieRename
        (fun y : K ↦ ((retract y : S) : K)) := by
    apply FreeLieAlgebra.hom_ext
    intro y
    change FiniteReduction.freeLieRename (fun z : S ↦ (z : K))
        (FiniteReduction.freeLieRename retract (FreeLieAlgebra.of ℤ y)) =
      FiniteReduction.freeLieRename (fun y : K ↦ ((retract y : S) : K))
        (FreeLieAlgebra.of ℤ y)
    rw [FiniteReduction.freeLieRename_of,
      FiniteReduction.freeLieRename_of,
      FiniteReduction.freeLieRename_of]
  have hroundUEA {u : UEA ℤ (FreeLieAlgebra ℤ K)} (hu : u ∈ T) :
      backwardUEA (forwardUEA u) = u := by
    rw [show backwardUEA (forwardUEA u) =
        UEA.map ℤ (FreeLieAlgebra ℤ S) (FreeLieAlgebra ℤ K) backward
          (UEA.map ℤ (FreeLieAlgebra ℤ K) (FreeLieAlgebra ℤ S)
            forward u) by rfl,
      UEA.map_comp, hcomposite]
    apply hS₀ (fun y : K ↦ ((retract y : S) : K))
    · intro y hy
      exact retract_coe (Finset.mem_insert_of_mem hy)
    · exact hu
  have hroundLie {z : FreeLieAlgebra ℤ K}
      (hz : UniversalEnvelopingAlgebra.ι ℤ z ∈ T) :
      backward (forward z) = z := by
    apply PBW.canonicalMap_injective_int (FreeLieAlgebra ℤ K)
    rw [← UEA.map_ι ℤ (FreeLieAlgebra ℤ S) (FreeLieAlgebra ℤ K)
        backward,
      ← UEA.map_ι ℤ (FreeLieAlgebra ℤ K) (FreeLieAlgebra ℤ S)
        forward]
    exact hroundUEA hz
  have hliftRound : backward (forward lift) = lift := by
    apply hroundLie
    exact Finset.mem_insert_self _ _
  have hrelationRound
      (p : LieHom.ker canonicalEval × UEA ℤ (FreeLieAlgebra ℤ K))
      (hp : p ∈ coeff.support) :
      backward (forward (p.1 : FreeLieAlgebra ℤ K)) = p.1 := by
    apply hroundLie
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  let F₀ : Type u := FreeMetabelian.Free (S →₀ ℤ) c
  let phi : FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ F₀ :=
    FiniteReduction.freeLieToFreeMetabelian c hc
  let eval₀ : F₀ →ₗ⁅ℤ⁆ K :=
    FreeMetabelian.Evaluation.lieHom hmeta hclass
      (FiniteReduction.finiteGeneratorMap (fun s : S ↦ (s : K)))
  let mapModel : UEA ℤ (FreeLieAlgebra ℤ K) →ₐ[ℤ] UEA ℤ F₀ :=
    (UEA.map ℤ (FreeLieAlgebra ℤ S) F₀ phi).comp forwardUEA
  let lift₀ : F₀ := phi (forward lift)
  let high₀ : UEA ℤ F₀ := mapModel highWord
  let relation₀ : coeff.support → F₀ := fun p ↦
    phi (forward (p.1.1 : FreeLieAlgebra ℤ K))
  let R₀ : LieIdeal ℤ F₀ :=
    LieSubmodule.lieSpan ℤ F₀ (Set.range relation₀)
  have hR₀_eval : R₀ ≤ LieHom.ker eval₀ := by
    rw [LieSubmodule.lieSpan_le]
    rintro z ⟨p, rfl⟩
    change eval₀ (relation₀ p) = 0
    rw [show eval₀ (relation₀ p) =
        FreeLieAlgebra.lift ℤ (fun s : S ↦ (s : K))
          (forward (p.1.1 : FreeLieAlgebra ℤ K)) by
      exact FiniteReduction.finiteModel_evaluation_compatibility
        c hc hmeta hclass (fun s : S ↦ (s : K)) _]
    rw [FiniteReduction.freeLie_subtype_evaluation_compatibility]
    rw [hrelationRound p.1 p.2]
    exact LinearMap.mem_ker.mp p.1.1.property
  have hlift₀_eval : eval₀ lift₀ = a := by
    rw [show eval₀ lift₀ =
        FreeLieAlgebra.lift ℤ (fun s : S ↦ (s : K)) (forward lift) by
      exact FiniteReduction.finiteModel_evaluation_compatibility
        c hc hmeta hclass (fun s : S ↦ (s : K)) _]
    rw [FiniteReduction.freeLie_subtype_evaluation_compatibility,
      hliftRound]
    exact canonicalFreeLieEvaluation_of K a
  have hrelation₀ : mapModel relationPart ∈
      UEA.idealOfLieIdeal ℤ F₀ R₀ := by
    rw [← hcoeff]
    rw [map_finsuppSum]
    apply (UEA.idealOfLieIdeal ℤ F₀ R₀).sum_mem
    intro p hp
    change mapModel (coeff p •
      (UniversalEnvelopingAlgebra.ι ℤ
        (p.1 : FreeLieAlgebra ℤ K) * p.2)) ∈ _
    rw [map_zsmul, map_mul]
    have hmapRelation : mapModel
        (UniversalEnvelopingAlgebra.ι ℤ
          (p.1 : FreeLieAlgebra ℤ K)) =
        UniversalEnvelopingAlgebra.ι ℤ (relation₀ ⟨p, hp⟩) := by
      dsimp only [mapModel, relation₀]
      change UEA.map ℤ (FreeLieAlgebra ℤ S) F₀ phi
          (forwardUEA (UniversalEnvelopingAlgebra.ι ℤ
            (p.1 : FreeLieAlgebra ℤ K))) = _
      rw [show forwardUEA (UniversalEnvelopingAlgebra.ι ℤ
            (p.1 : FreeLieAlgebra ℤ K)) =
          UniversalEnvelopingAlgebra.ι ℤ
            (forward (p.1 : FreeLieAlgebra ℤ K)) by
        exact UEA.map_ι ℤ (FreeLieAlgebra ℤ K)
          (FreeLieAlgebra ℤ S) forward (p.1 : FreeLieAlgebra ℤ K),
        UEA.map_ι]
    rw [hmapRelation]
    apply ((UEA.idealOfLieIdeal ℤ F₀ R₀).restrictScalars ℤ).toAddSubgroup.zsmul_mem
    apply (UEA.idealOfLieIdeal ℤ F₀ R₀).mul_mem_right
    let ps : coeff.support := ⟨p, hp⟩
    let rho₀ : R₀ := ⟨relation₀ ps,
      LieSubmodule.subset_lieSpan
        (show relation₀ ps ∈ Set.range relation₀ from Set.mem_range_self ps)⟩
    exact UEA.ι_mem_idealOfLieIdeal ℤ F₀ R₀ rho₀
  have hrelationForm : mapModel relationPart =
      UniversalEnvelopingAlgebra.ι ℤ lift₀ - high₀ := by
    have hmapLift : mapModel (UniversalEnvelopingAlgebra.ι ℤ lift) =
        UniversalEnvelopingAlgebra.ι ℤ lift₀ := by
      dsimp only [mapModel, lift₀]
      change UEA.map ℤ (FreeLieAlgebra ℤ S) F₀ phi
          (forwardUEA (UniversalEnvelopingAlgebra.ι ℤ lift)) = _
      rw [show forwardUEA (UniversalEnvelopingAlgebra.ι ℤ lift) =
          UniversalEnvelopingAlgebra.ι ℤ (forward lift) by
        exact UEA.map_ι ℤ (FreeLieAlgebra ℤ K)
          (FreeLieAlgebra ℤ S) forward lift,
        UEA.map_ι]
    dsimp only [relationPart, high₀]
    rw [map_sub, hmapLift]
  have hrelation₀' : UniversalEnvelopingAlgebra.ι ℤ lift₀ - high₀ ∈
      UEA.idealOfLieIdeal ℤ F₀ R₀ := by
    rwa [hrelationForm] at hrelation₀
  have hhigh₀ : high₀ ∈ UEA.augmentationIdeal ℤ F₀ ^ (2 * c - 1) := by
    dsimp only [high₀, mapModel]
    apply UEA.map_mem_augmentationIdeal_pow ℤ (FreeLieAlgebra ℤ S) F₀
      phi (2 * c - 1)
    apply UEA.map_mem_augmentationIdeal_pow ℤ (FreeLieAlgebra ℤ K)
      (FreeLieAlgebra ℤ S) forward (2 * c - 1)
    exact hhighWord'
  let q₀ : F₀ →ₗ⁅ℤ⁆ Presentation.Quotient c R₀ :=
    Presentation.quotientMap c R₀
  let a₀ : Presentation.Quotient c R₀ := q₀ lift₀
  have hkerq₀ : LieHom.ker q₀ = R₀ := by
    exact Presentation.ker_quotientMap c R₀
  have hrelationMap₀ : UEA.map ℤ F₀ (Presentation.Quotient c R₀) q₀
      (UniversalEnvelopingAlgebra.ι ℤ lift₀ - high₀) = 0 := by
    apply (LieRings.PBW.WeightedBasis.mem_ker_map_iff_mem_idealOfLieIdeal
      q₀ (Presentation.quotientMap_surjective c R₀)
      (UniversalEnvelopingAlgebra.ι ℤ lift₀ - high₀)).mpr
    rwa [hkerq₀]
  have hiota_a₀ : UniversalEnvelopingAlgebra.ι ℤ a₀ =
      UEA.map ℤ F₀ (Presentation.Quotient c R₀) q₀ high₀ := by
    dsimp only [a₀] at ⊢
    rw [map_sub, UEA.map_ι] at hrelationMap₀
    exact sub_eq_zero.mp hrelationMap₀
  have hhighQuotient :
      UEA.map ℤ F₀ (Presentation.Quotient c R₀) q₀ high₀ ∈
        UEA.augmentationIdeal ℤ (Presentation.Quotient c R₀) ^
          (2 * c - 1) :=
    UEA.map_mem_augmentationIdeal_pow ℤ F₀
      (Presentation.Quotient c R₀) q₀ (2 * c - 1) hhigh₀
  have ha₀Dim : a₀ ∈
      dimensionSubring ℤ (Presentation.Quotient c R₀) (2 * c - 1) := by
    rw [mem_dimensionSubring, hiota_a₀]
    exact hhighQuotient
  have hfiniteVanishing :=
    Presentation.dimensionSubring_quotient_eq_bot
      (X := S →₀ ℤ) c R₀ hc2
  have ha₀Zero : a₀ = 0 := by
    rw [hfiniteVanishing] at ha₀Dim
    simpa using ha₀Dim
  have hlift₀R : lift₀ ∈ R₀ := by
    apply (LieSubmodule.Quotient.mk_eq_zero' (N := R₀)).mp
    exact ha₀Zero
  have hlift₀Zero : eval₀ lift₀ = 0 :=
    LinearMap.mem_ker.mp (hR₀_eval hlift₀R)
  rw [hlift₀_eval] at hlift₀Zero
  exact hlift₀Zero

/-! ## The odd-dimensional inclusion -/

/-- A quotient of a metabelian Lie ring is metabelian. -/
theorem quotient_isMetabelian_of_isMetabelian
    {L : Type u} [LieRing L] (I : LieIdeal ℤ L)
    (hmeta : IsMetabelian L) : IsMetabelian (L ⧸ I) := by
  let q : L →ₗ⁅ℤ⁆ L ⧸ I := UEA.lieIdealQuotientMk ℤ L I
  have hq : Function.Surjective q := LieSubmodule.Quotient.surjective_mk' I
  have hmap := LieIdeal.derivedSeries_map_eq (f := q) 2 hq
  change LieAlgebra.derivedSeries ℤ (L ⧸ I) 2 = ⊥
  rw [← hmap, hmeta]
  simp

/-- Quotienting by the `c`th zero-based lower-central term produces a ring
of class at most `c`. -/
theorem lowerCentralSeries_quotient_eq_bot
    (L : Type u) [LieRing L] (c : ℕ) :
    lowerCentralSeries ℤ (L ⧸ lowerCentralSeries ℤ L c) c = ⊥ := by
  let I : LieIdeal ℤ L := lowerCentralSeries ℤ L c
  let q : L →ₗ⁅ℤ⁆ L ⧸ I := UEA.lieIdealQuotientMk ℤ L I
  have hq : Function.Surjective q := LieSubmodule.Quotient.surjective_mk' I
  change LieModule.lowerCentralSeries ℤ (L ⧸ I) (L ⧸ I) c = ⊥
  rw [← LieIdeal.lowerCentralSeries_map_eq c hq,
    LieIdeal.map_eq_bot_iff]
  intro x hx
  change (LieSubmodule.Quotient.mk x : L ⧸ I) = 0
  exact (LieSubmodule.Quotient.mk_eq_zero' (N := I)).mpr hx

/-- **Odd-dimensional inclusion for metabelian Lie rings.**  In Mathlib's
zero-based convention, `lowerCentralSeries ℤ L (n+1)` is the manuscript's
`γ_(n+2)(L)`. -/
theorem odd_dimensionSubring_le_lowerCentralSeries
    (n : ℕ) (L : Type u) [LieRing L]
    (hn : 1 ≤ n) (hmeta : IsMetabelian L) :
    dimensionSubring ℤ L (2 * n + 1) ≤
      lowerCentralSeries ℤ L (n + 1) := by
  let I : LieIdeal ℤ L := lowerCentralSeries ℤ L (n + 1)
  have hquotMeta : IsMetabelian (L ⧸ I) :=
    quotient_isMetabelian_of_isMetabelian I hmeta
  have hquotClass : lowerCentralSeries ℤ (L ⧸ I) (n + 1) = ⊥ := by
    exact lowerCentralSeries_quotient_eq_bot L (n + 1)
  have hquotVanish := nilpotent_dimensionSubring_eq_bot
    (n + 1) (L ⧸ I) (by omega) hquotMeta hquotClass
  have hindex : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [hindex] at hquotVanish
  exact dimensionSubring_le_of_quotient_eq_bot ℤ L I
    (2 * n + 1) hquotVanish

/-! ## The arbitrary degree-five specialization -/

/-- The first derived ideal is exactly the first zero-based lower-central term. -/
theorem derivedSeries_one_eq_lowerCentralSeries_one
    (L : Type u) [LieRing L] :
    LieAlgebra.derivedSeries ℤ L 1 = lowerCentralSeries ℤ L 1 := by
  simpa [LieAlgebra.derivedSeries_def,
    LieAlgebra.derivedSeriesOfIdeal_succ, lowerCentralSeries,
    LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]

/-- The elementary Jacobi inclusion
`[γ₂(L), γ₂(L)] ⊆ γ₄(L)`, in zero-based indexing. -/
theorem bracket_lowerCentralSeries_one_mem_three
    (L : Type u) [LieRing L] {x y : L}
    (hx : x ∈ lowerCentralSeries ℤ L 1)
    (hy : y ∈ lowerCentralSeries ℤ L 1) :
    ⁅x, y⁆ ∈ lowerCentralSeries ℤ L 3 := by
  change y ∈ LieModule.lowerCentralSeries ℤ L L (0 + 1) at hy
  rw [LieModule.lowerCentralSeries_succ] at hy
  have hy' : y ∈ Submodule.span ℤ
      {z : L | ∃ a ∈ (⊤ : LieIdeal ℤ L),
        ∃ b ∈ LieModule.lowerCentralSeries ℤ L L 0, ⁅a, b⁆ = z} := by
    rw [← LieSubmodule.lieIdeal_oper_eq_linear_span'
      (LieModule.lowerCentralSeries ℤ L L 0) (⊤ : LieIdeal ℤ L)]
    exact hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      have hxa : ⁅x, a⁆ ∈ lowerCentralSeries ℤ L 2 := by
        change ⁅x, a⁆ ∈ LieModule.lowerCentralSeries ℤ L L (1 + 1)
        rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
        exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top a)
      have hxb : ⁅x, b⁆ ∈ lowerCentralSeries ℤ L 2 := by
        change ⁅x, b⁆ ∈ LieModule.lowerCentralSeries ℤ L L (1 + 1)
        rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
        exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top b)
      rw [leibniz_lie]
      apply (lowerCentralSeries ℤ L 3).add_mem
      · change ⁅⁅x, a⁆, b⁆ ∈
          LieModule.lowerCentralSeries ℤ L L (2 + 1)
        rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
        exact LieSubmodule.lie_mem_lie hxa (LieSubmodule.mem_top b)
      · change ⁅a, ⁅x, b⁆⁆ ∈
          LieModule.lowerCentralSeries ℤ L L (2 + 1)
        rw [LieModule.lowerCentralSeries_succ]
        exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a) hxb
  | zero => simp
  | add a b _ _ iha ihb => simpa [lie_add] using
      (lowerCentralSeries ℤ L 3).add_mem iha ihb
  | smul r a _ iha => simpa [lie_smul] using
      (lowerCentralSeries ℤ L 3).smul_mem r iha

/-- Every Lie ring of nilpotency class at most three is metabelian. -/
theorem isMetabelian_of_lowerCentralSeries_three_eq_bot
    (L : Type u) [LieRing L]
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) : IsMetabelian L := by
  rw [IsMetabelian.iff_bracket_eq_zero]
  intro x y hx hy
  have hx' : x ∈ lowerCentralSeries ℤ L 1 := by
    rw [← derivedSeries_one_eq_lowerCentralSeries_one L]
    exact hx
  have hy' : y ∈ lowerCentralSeries ℤ L 1 := by
    rw [← derivedSeries_one_eq_lowerCentralSeries_one L]
    exact hy
  have hxy := bracket_lowerCentralSeries_one_mem_three L hx' hy'
  rw [hclass] at hxy
  simpa using hxy

/-- The manuscript's `n = 2` observation for an arbitrary Lie ring:
`δ₅(L) ⊆ γ₄(L)`.  The quotient by `γ₄(L)` has class at most
three, hence is metabelian, so the nilpotent theorem applies to it. -/
theorem dimensionSubring_five_le_lowerCentralSeries_three
    (L : Type u) [LieRing L] :
    dimensionSubring ℤ L 5 ≤ lowerCentralSeries ℤ L 3 := by
  let I : LieIdeal ℤ L := lowerCentralSeries ℤ L 3
  have hquotClass : lowerCentralSeries ℤ (L ⧸ I) 3 = ⊥ :=
    lowerCentralSeries_quotient_eq_bot L 3
  have hquotMeta : IsMetabelian (L ⧸ I) :=
    isMetabelian_of_lowerCentralSeries_three_eq_bot
      (L ⧸ I) hquotClass
  have hquotVanish := nilpotent_dimensionSubring_eq_bot
    3 (L ⧸ I) (by omega) hquotMeta hquotClass
  norm_num at hquotVanish
  exact dimensionSubring_le_of_quotient_eq_bot ℤ L I 5 hquotVanish

assert_no_sorry Presentation.dimensionSubring_quotient_eq_bot
assert_no_sorry nilpotent_dimensionSubring_eq_bot
assert_no_sorry odd_dimensionSubring_le_lowerCentralSeries
assert_no_sorry dimensionSubring_five_le_lowerCentralSeries_three

end

end LieRings.MetabelianTwoFactor
