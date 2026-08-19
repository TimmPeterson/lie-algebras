import LieRings.DimensionSubring.MetabelianOdd.Assumptions
import LieRings.DimensionSubring.MetabelianOdd.OrderedPBW
import LieRings.DimensionSubring.DegreeFive.AdaptedPresentation
import LieRings.DimensionSubring.DegreeFive.FiniteClassTwoBasis
import LieRings.DimensionSubring.DegreeFive.PresentationKernel
import LieRings.DimensionSubring.DegreeFive.SemanticCollector
import LieRings.DimensionSubring.DegreeFive.Witness
import LieRings.DimensionSubring.DegreeFive.PlacedLedger
import LieRings.DimensionSubring.DegreeFive.FinitePlacedInput
import LieRings.DimensionSubring.DegreeFive.LowSymbolExtraction
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Finite homogeneous coordinates for the metabelian odd argument

For a finite generator type `X` and cutoff `N`, the quotient of the free Lie ring by its
`(N+1)`st lower-central term is identified with the product of exact free-Lie components of
weights `1,...,N`.  The ordered integral PBW theorem then supplies exact weighted coordinates.
-/

namespace LieRings.DimensionSubring.MetabelianOdd

noncomputable section

open LieRings.PBW
open LieRings.DegreeFive

universe u v

variable (X : Type u) [Finite X]

local notation "F" => FreeLieAlgebra ℤ X

/-- The free Lie ring truncated after exact weight `N`. -/
abbrev TruncatedFreeLie (N : ℕ) :=
  F ⧸ lowerCentralSeries ℤ F N

/-- The canonical map to the weight-`N` truncation. -/
def truncatedFreeLieMk (N : ℕ) : F →ₗ⁅ℤ⁆ TruncatedFreeLie X N :=
  UEA.lieIdealQuotientMk ℤ F (lowerCentralSeries ℤ F N)

/-- Product of exact free-Lie components in weights `1,...,N`. -/
abbrev LowTuple (N : ℕ) :=
  ∀ s : Fin N, freeLieExact X (s.1 + 1)

/-- Sum the finitely many exact components back into the free Lie ring. -/
private def lowTupleSum (N : ℕ) : LowTuple X N →ₗ[ℤ] F where
  toFun z := ∑ s, ((z s : freeLieExact X (s.1 + 1)) : F)
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' n x := by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower]
    exact Finset.smul_sum.symm

/-- Sum the low exact components and pass to the truncated free Lie ring. -/
private def lowTupleToTruncation (N : ℕ) :
    LowTuple X N →ₗ[ℤ] TruncatedFreeLie X N :=
  (truncatedFreeLieMk X N).toLinearMap.comp (lowTupleSum X N)

private theorem lowTupleToTruncation_injective (N : ℕ) :
    Function.Injective (lowTupleToTruncation X N) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply funext
  intro s
  apply Subtype.ext
  have hzero : lowTupleToTruncation X N (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hhigh : lowTupleSum X N (x - y) ∈
      FreeLieDimension.lieHigh X (N + 1) := by
    rw [FreeLieDimension.lieHigh_eq_lowerCentralSeries X N]
    exact (LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ F N)).mp hzero
  have hslt : s.1 + 1 < N + 1 := by omega
  have hcomponent := freeLieLengthComponent_eq_zero_of_mem_lieHigh
    X hhigh hslt
  change freeLieLengthComponent X (s.1 + 1)
      (∑ t : Fin N,
        (((x - y) t : freeLieExact X (t.1 + 1)) : F)) = 0 at hcomponent
  rw [map_sum, Finset.sum_eq_single s] at hcomponent
  · rw [freeLieLengthComponent_coe_exact X (s.1 + 1)] at hcomponent
    exact hcomponent
  · intro t _ hts
    rw [freeLieLengthComponent_coe_exact_of_ne X]
    intro hweight
    apply hts
    apply Fin.ext
    omega
  · simp

private theorem lowTupleToTruncation_surjective (N : ℕ) :
    Function.Surjective (lowTupleToTruncation X N) := by
  intro z
  obtain ⟨f, rfl⟩ := LieSubmodule.Quotient.surjective_mk'
    (lowerCentralSeries ℤ F N) z
  let parts : LowTuple X N := fun s ↦
    ⟨freeLieLengthComponent X (s.1 + 1) f,
      freeLieLengthComponent_mem_exact X (s.1 + 1) f⟩
  refine ⟨parts, ?_⟩
  let rem : F := f - lowTupleSum X N parts
  have hcomponent (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
      freeLieLengthComponent X k rem = 0 := by
    let s : Fin N := ⟨k - 1, by omega⟩
    have hsweight : s.1 + 1 = k := by
      dsimp only [s]
      omega
    change freeLieLengthComponent X k
      (f - ∑ t : Fin N,
        (((parts t : freeLieExact X (t.1 + 1)) : F))) = 0
    rw [map_sub, map_sum, Finset.sum_eq_single s]
    · rw [← hsweight, freeLieLengthComponent_coe_exact X]
      change freeLieLengthComponent X (s.1 + 1) f -
          freeLieLengthComponent X (s.1 + 1) f = 0
      abel
    · intro t _ hts
      rw [freeLieLengthComponent_coe_exact_of_ne X]
      intro hweight
      apply hts
      apply Fin.ext
      omega
    · simp
  have hhigh : ∀ k : ℕ, k ≤ N + 1 → 1 ≤ k →
      rem ∈ FreeLieDimension.lieHigh X k := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
        intro hkN hkpos
        by_cases hk0 : k = 0
        · subst k
          rw [FreeLieDimension.lieHigh_one]
          trivial
        · have hkpos' : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
          exact mem_lieHigh_succ_of_component_eq_zero X
            (ih (by omega) hkpos') (hcomponent k hkpos' (by omega))
  have hrem : rem ∈ FreeLieDimension.lieHigh X (N + 1) :=
    hhigh (N + 1) le_rfl (by omega)
  apply sub_eq_zero.mp
  change truncatedFreeLieMk X N (lowTupleSum X N parts) -
      truncatedFreeLieMk X N f = 0
  rw [← map_sub]
  apply (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ F N)).mpr
  have hneg : lowTupleSum X N parts - f = -rem := by
    dsimp only [rem]
    abel
  rw [hneg]
  change -rem ∈
    (lowerCentralSeries ℤ F N).toLieSubalgebra.toSubmodule
  rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries X N]
  exact (FreeLieDimension.lieHigh X (N + 1)).neg_mem hrem

/-- Exact weights `1,...,N` are linearly equivalent to the truncated free Lie ring. -/
private def lowTupleEquivTruncation (N : ℕ) :
    LowTuple X N ≃ₗ[ℤ] TruncatedFreeLie X N :=
  LinearEquiv.ofBijective (lowTupleToTruncation X N)
    ⟨lowTupleToTruncation_injective X N,
      lowTupleToTruncation_surjective X N⟩

/-- Indices for the homogeneous basis of the weight-`N` truncation. -/
abbrev TruncatedBasisIndex (N : ℕ) :=
  Σ s : Fin N, FreeLieExactBasisIndex X (s.1 + 1)

private def truncatedBasisIndexCode {N : ℕ} :
    TruncatedBasisIndex X N → ℕ ×ₗ ℕ := fun i ↦ toLex (i.1.1, i.2.1)

private theorem truncatedBasisIndexCode_injective {N : ℕ} :
    Function.Injective (truncatedBasisIndexCode (X := X) (N := N)) := by
  rintro ⟨s, i⟩ ⟨t, j⟩ h
  simp only [truncatedBasisIndexCode, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq] at h
  obtain ⟨hst, hij⟩ := h
  have hst' : s = t := Fin.ext hst
  subst t
  have hij' : i = j := Fin.ext hij
  subst j
  rfl

/-- Weight-first, then basis-index order on the bounded homogeneous basis. -/
noncomputable instance {N : ℕ} : LinearOrder (TruncatedBasisIndex X N) :=
  LinearOrder.lift' (truncatedBasisIndexCode (X := X) (N := N))
    (truncatedBasisIndexCode_injective X)

/-- The basis obtained by adjoining the exact free-Lie bases in weights `1,...,N`. -/
def truncatedHomogeneousBasis (N : ℕ) :
    Module.Basis (TruncatedBasisIndex X N) ℤ (TruncatedFreeLie X N) :=
  (Pi.basis (fun s : Fin N ↦ freeLieExactBasis X (s.1 + 1))).map
    (lowTupleEquivTruncation X N)

/-- A bounded homogeneous basis vector is the quotient of its exact free-Lie vector. -/
@[simp] theorem truncatedHomogeneousBasis_apply (N : ℕ)
    (i : TruncatedBasisIndex X N) :
    truncatedHomogeneousBasis X N i =
      truncatedFreeLieMk X N
        ((freeLieExactBasis X (i.1.1 + 1) i.2 :
          freeLieExact X (i.1.1 + 1)) : F) := by
  rw [truncatedHomogeneousBasis, Module.Basis.map_apply, Pi.basis_apply]
  change truncatedFreeLieMk X N
      (lowTupleSum X N
        (Pi.single i.1 (freeLieExactBasis X (i.1.1 + 1) i.2))) = _
  change truncatedFreeLieMk X N
      (∑ s : Fin N,
        (((Pi.single i.1 (freeLieExactBasis X (i.1.1 + 1) i.2) :
          LowTuple X N) s : freeLieExact X (s.1 + 1)) : F)) = _
  rw [map_sum, Finset.sum_eq_single i.1]
  · simp
  · intro s _ hsi
    simp [Pi.single_eq_of_ne hsi]
  · simp

/-- Exact Lie weight of an index in the bounded homogeneous basis. -/
def truncatedBasisWeight {N : ℕ} (i : TruncatedBasisIndex X N) : ℕ :=
  i.1.1 + 1

@[simp] theorem truncatedBasisWeight_pos {N : ℕ}
    (i : TruncatedBasisIndex X N) :
    0 < truncatedBasisWeight X i := by
  simp [truncatedBasisWeight]

theorem truncatedBasisWeight_le {N : ℕ}
    (i : TruncatedBasisIndex X N) :
    truncatedBasisWeight X i ≤ N := by
  simp only [truncatedBasisWeight]
  omega

private def quotientLieMap
    (L : Type v) [LieRing L] (N : ℕ)
    (evaluation : F →ₗ⁅ℤ⁆ L)
    (hkill : ∀ x : F, x ∈ lowerCentralSeries ℤ F N → evaluation x = 0) :
    TruncatedFreeLie X N →ₗ⁅ℤ⁆ L where
  toLinearMap := (lowerCentralSeries ℤ F N).toSubmodule.liftQ
    evaluation.toLinearMap (fun x hx ↦ by
      rw [LinearMap.mem_ker]
      exact hkill x hx)
  map_lie' := by
    intro x y
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    exact LieHom.map_lie evaluation _ _

@[simp] private theorem quotientLieMap_mk
    (L : Type v) [LieRing L] (N : ℕ)
    (evaluation : F →ₗ⁅ℤ⁆ L)
    (hkill : ∀ x : F, x ∈ lowerCentralSeries ℤ F N → evaluation x = 0)
    (x : F) :
    quotientLieMap X L N evaluation hkill (truncatedFreeLieMk X N x) =
      evaluation x := by
  rfl

/-- Evaluation of a free Lie ring in a class-`n+1` target, descended to weight `2*n`.

The inequality `n+1 ≤ 2*n` is the sole reason for the hypothesis `1 ≤ n`. -/
def classBoundedTruncatedEvaluation
    (n : ℕ) (hn : 1 ≤ n)
    (L : Type v) [LieRing L]
    (evaluation : F →ₗ⁅ℤ⁆ L)
    (hclass : lowerCentralSeries ℤ L (n + 1) = ⊥) :
    TruncatedFreeLie X (2 * n) →ₗ⁅ℤ⁆ L :=
  quotientLieMap X L (2 * n) evaluation (by
    intro x hx
    have hxmap : evaluation x ∈ lowerCentralSeries ℤ L (2 * n) := by
      apply (LieIdeal.map_lowerCentralSeries_le
        (R := ℤ) (f := evaluation) (2 * n))
      exact LieIdeal.mem_map hx
    have hxclass : evaluation x ∈ lowerCentralSeries ℤ L (n + 1) :=
      LieModule.antitone_lowerCentralSeries ℤ L L (by omega) hxmap
    rw [hclass] at hxclass
    exact hxclass)

@[simp] theorem classBoundedTruncatedEvaluation_mk
    (n : ℕ) (hn : 1 ≤ n)
    (L : Type v) [LieRing L]
    (evaluation : F →ₗ⁅ℤ⁆ L)
    (hclass : lowerCentralSeries ℤ L (n + 1) = ⊥)
    (x : F) :
    classBoundedTruncatedEvaluation X n hn L evaluation hclass
        (truncatedFreeLieMk X (2 * n) x) = evaluation x := by
  apply quotientLieMap_mk

/-! ## Exact weighted PBW coordinates -/

/-- Number of factors in an ordered PBW monomial. -/
def factorNumber {N : ℕ} (e : TruncatedBasisIndex X N →₀ ℕ) : ℕ :=
  e.sum fun _ m ↦ m

/-- Sum of the homogeneous Lie weights of an ordered PBW monomial. -/
def totalWeight {N : ℕ} (e : TruncatedBasisIndex X N →₀ ℕ) : ℕ :=
  e.sum fun i m ↦ m * truncatedBasisWeight X i

/-- Integral ordered PBW coordinates for the bounded homogeneous basis. -/
def truncatedPBWLinearEquiv (N : ℕ) :
    MvPolynomial (TruncatedBasisIndex X N) ℤ ≃ₗ[ℤ]
      UEA ℤ (TruncatedFreeLie X N) :=
  LinearEquiv.ofBijective
    (orderedPBWMap ℤ (TruncatedFreeLie X N) (TruncatedBasisIndex X N)
      (truncatedHomogeneousBasis X N))
    (freeModulePBW_int (TruncatedFreeLie X N) (TruncatedBasisIndex X N)
      (truncatedHomogeneousBasis X N))

/-- The coefficient of an ordered PBW exponent vector. -/
def pbwCoeff (N : ℕ) (u : UEA ℤ (TruncatedFreeLie X N))
    (e : TruncatedBasisIndex X N →₀ ℕ) : ℤ :=
  MvPolynomial.coeff e ((truncatedPBWLinearEquiv X N).symm u)

private def truncatedBasisIndexOf {N m : ℕ}
    (hm : 0 < m) (hmN : m ≤ N)
    (i : FreeLieExactBasisIndex X m) : TruncatedBasisIndex X N := by
  cases m with
  | zero => omega
  | succ k => exact ⟨⟨k, by omega⟩, i⟩

@[simp] private theorem truncatedBasisWeight_indexOf {N m : ℕ}
    (hm : 0 < m) (hmN : m ≤ N)
    (i : FreeLieExactBasisIndex X m) :
    truncatedBasisWeight X (truncatedBasisIndexOf X hm hmN i) = m := by
  cases m with
  | zero => omega
  | succ k => simp [truncatedBasisWeight, truncatedBasisIndexOf]

private theorem truncatedHomogeneousBasis_indexOf {N m : ℕ}
    (hm : 0 < m) (hmN : m ≤ N)
    (i : FreeLieExactBasisIndex X m) :
    truncatedHomogeneousBasis X N (truncatedBasisIndexOf X hm hmN i) =
      truncatedFreeLieMk X N
        ((freeLieExactBasis X m i : freeLieExact X m) : F) := by
  cases m with
  | zero => omega
  | succ k =>
      simp [truncatedBasisIndexOf]

private def truncatedBracketCoefficients {N : ℕ}
    (x y : TruncatedBasisIndex X N)
    (hxy : truncatedBasisWeight X x + truncatedBasisWeight X y ≤ N) :
    TruncatedBasisIndex X N →₀ ℤ :=
  (homogeneousBracketCoefficients X
      (freeLieExactBasis X (x.1.1 + 1) x.2)
      (freeLieExactBasis X (y.1.1 + 1) y.2)).mapDomain
    (truncatedBasisIndexOf X
      (Nat.add_pos_left (truncatedBasisWeight_pos X x) _) hxy)

private theorem truncatedBracketCoefficients_sum {N : ℕ}
    (x y : TruncatedBasisIndex X N)
    (hxy : truncatedBasisWeight X x + truncatedBasisWeight X y ≤ N) :
    (truncatedBracketCoefficients X x y hxy).sum
        (fun i c ↦ c • truncatedHomogeneousBasis X N i) =
      ⁅truncatedHomogeneousBasis X N x,
        truncatedHomogeneousBasis X N y⁆ := by
  unfold truncatedBracketCoefficients
  rw [Finsupp.sum_mapDomain_index]
  · let x' := freeLieExactBasis X (x.1.1 + 1) x.2
    let y' := freeLieExactBasis X (y.1.1 + 1) y.2
    let c := homogeneousBracketCoefficients X x' y'
    change c.sum (fun i z ↦ z •
        truncatedHomogeneousBasis X N
          (truncatedBasisIndexOf X
            (Nat.add_pos_left (truncatedBasisWeight_pos X x) _) hxy i)) = _
    simp_rw [truncatedHomogeneousBasis_indexOf]
    calc
      c.sum (fun i z ↦ z • truncatedFreeLieMk X N
          (((freeLieExactBasis X
            (truncatedBasisWeight X x + truncatedBasisWeight X y)) i :
              freeLieExact X
                (truncatedBasisWeight X x + truncatedBasisWeight X y)) : F)) =
          truncatedFreeLieMk X N
            (c.sum (fun i z ↦ z •
              (((freeLieExactBasis X
                (truncatedBasisWeight X x + truncatedBasisWeight X y)) i :
                  freeLieExact X
                    (truncatedBasisWeight X x + truncatedBasisWeight X y)) : F))) := by
            rw [map_finsuppSum]
            apply Finsupp.sum_congr
            intro i hi
            rw [map_zsmul]
      _ = truncatedFreeLieMk X N ⁅(x' : F), (y' : F)⁆ := by
            apply congrArg (truncatedFreeLieMk X N)
            exact homogeneousBracketCoefficients_sum X x' y'
      _ = ⁅truncatedHomogeneousBasis X N x,
          truncatedHomogeneousBasis X N y⁆ := by
            rw [LieHom.map_lie]
            simp [x', y']
  · intro i
    simp
  · intro i a b
    simp [add_smul]

private def truncatedInversionCount {N : ℕ} :
    List (TruncatedBasisIndex X N) → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + truncatedInversionCount xs

private theorem truncatedInversionCount_swap {N : ℕ}
    (left right : List (TruncatedBasisIndex X N))
    (x y : TruncatedBasisIndex X N) (hxy : y < x) :
    truncatedInversionCount X (left ++ x :: y :: right) =
      truncatedInversionCount X (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnx : ¬x < y := not_lt_of_ge (le_of_lt hxy)
      simp [truncatedInversionCount, hxy, hnx, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, truncatedInversionCount]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp <;> omega
      rw [hfilter, ih]
      omega

private theorem weight_toMultiset {N : ℕ}
    (e : TruncatedBasisIndex X N →₀ ℕ) :
    Finsupp.weight (truncatedBasisWeight X) e =
      (Finsupp.toMultiset e |>.map (truncatedBasisWeight X)).sum := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | @single_add i m e hi hm ih =>
      rw [map_add, Finsupp.toMultiset_add, Multiset.map_add,
        Multiset.sum_add, ih, Finsupp.toMultiset_single,
        Finsupp.weight_single, Multiset.map_nsmul, Multiset.sum_nsmul,
        Multiset.map_singleton, Multiset.sum_singleton]

/-- Collection of a homogeneous basis word preserves its exact total Lie weight. -/
private theorem pbwPolynomial_basisWord_isWeighted (N : ℕ)
    (xs : List (TruncatedBasisIndex X N)) :
    MvPolynomial.IsWeightedHomogeneous (truncatedBasisWeight X)
      ((truncatedPBWLinearEquiv X N).symm
        (basisWord ℤ (TruncatedFreeLie X N) (TruncatedBasisIndex X N)
          (truncatedHomogeneousBasis X N) xs))
      ((xs.map (truncatedBasisWeight X)).sum) := by
  let complexity : List (TruncatedBasisIndex X N) → ℕ × ℕ := fun ys ↦
    (ys.length, truncatedInversionCount X ys)
  let descent (new old : List (TruncatedBasisIndex X N)) : Prop :=
    Prod.Lex (· < ·) (· < ·) (complexity new) (complexity old)
  have hwell : WellFounded descent :=
    InvImage.wf complexity (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  induction xs using hwell.induction with
  | h xs ih =>
      classical
      letI : DecidableEq (TruncatedBasisIndex X N) :=
        LinearOrder.toDecidableEq
      cases hchosen : chooseAdjacentInversion? xs with
      | none =>
          have hordered : xs.Pairwise (· ≤ ·) :=
            (chooseAdjacentInversion?_eq_none_iff_pairwise xs).mp hchosen
          let e : TruncatedBasisIndex X N →₀ ℕ :=
            Multiset.toFinsupp (xs : Multiset (TruncatedBasisIndex X N))
          have hcoordinate :
              (truncatedPBWLinearEquiv X N).symm
                  (basisWord ℤ (TruncatedFreeLie X N)
                    (TruncatedBasisIndex X N)
                    (truncatedHomogeneousBasis X N) xs) =
                MvPolynomial.monomial e 1 := by
            apply (truncatedPBWLinearEquiv X N).injective
            rw [LinearEquiv.apply_symm_apply]
            symm
            change orderedPBWMap ℤ (TruncatedFreeLie X N)
                (TruncatedBasisIndex X N) (truncatedHomogeneousBasis X N)
                  (MvPolynomial.monomial e 1) = _
            rw [orderedPBWMap_monomial]
            calc
              (1 : ℤ) • orderedMonomial ℤ (TruncatedFreeLie X N)
                  (TruncatedBasisIndex X N) (truncatedHomogeneousBasis X N) e =
                  orderedMonomial ℤ (TruncatedFreeLie X N)
                    (TruncatedBasisIndex X N)
                    (truncatedHomogeneousBasis X N) e := by module
              _ = _ := by
                simpa only [e] using
                  (orderedMonomial_multiset_toFinsupp ℤ
                    (TruncatedFreeLie X N) (TruncatedBasisIndex X N)
                    (truncatedHomogeneousBasis X N) xs hordered)
          rw [hcoordinate]
          apply MvPolynomial.isWeightedHomogeneous_monomial
          dsimp only [e]
          simpa [e] using weight_toMultiset X e
      | some d =>
          have hd := chooseAdjacentInversion?_eq_some_realizes hchosen
          rcases hd with ⟨hxs, hxy⟩
          let swapped := d.left ++ d.y :: d.x :: d.right
          have hswapDescent : descent swapped xs := by
            unfold descent complexity swapped
            rw [hxs]
            simp only [List.length_append, List.length_cons]
            apply Prod.Lex.right
            have hinv := truncatedInversionCount_swap X d.left d.right
              d.x d.y hxy
            omega
          have hswap := ih swapped hswapDescent
          by_cases hweight : truncatedBasisWeight X d.x +
              truncatedBasisWeight X d.y ≤ N
          · let c := truncatedBracketCoefficients X d.x d.y hweight
            let correction := fun i : TruncatedBasisIndex X N ↦
              d.left ++ i :: d.right
            have hcorrectionDescent (i : TruncatedBasisIndex X N) :
                descent (correction i) xs := by
              unfold descent complexity correction
              rw [hxs]
              apply Prod.Lex.left
              simp
            have hcorrection (i : TruncatedBasisIndex X N) :=
              ih (correction i) (hcorrectionDescent i)
            have hword :
                basisWord ℤ (TruncatedFreeLie X N)
                    (TruncatedBasisIndex X N)
                    (truncatedHomogeneousBasis X N) xs =
                  basisWord ℤ (TruncatedFreeLie X N)
                    (TruncatedBasisIndex X N)
                    (truncatedHomogeneousBasis X N) swapped +
                  c.sum (fun i z ↦ z •
                    basisWord ℤ (TruncatedFreeLie X N)
                      (TruncatedBasisIndex X N)
                      (truncatedHomogeneousBasis X N) (correction i)) := by
              have hcoeff := truncatedBracketCoefficients_sum X d.x d.y hweight
              let context : TruncatedFreeLie X N →+ UEA ℤ (TruncatedFreeLie X N) :=
                { toFun := fun z ↦
                    word ℤ (TruncatedFreeLie X N)
                        (d.left.map (truncatedHomogeneousBasis X N)) *
                      UniversalEnvelopingAlgebra.ι ℤ z *
                      word ℤ (TruncatedFreeLie X N)
                        (d.right.map (truncatedHomogeneousBasis X N))
                  map_zero' := by simp
                  map_add' := by intro a b; simp [map_add, mul_add, add_mul] }
              have hcontext := congrArg context hcoeff
              rw [map_finsuppSum] at hcontext
              have hcontext' :
                  c.sum (fun i z ↦ z •
                    basisWord ℤ (TruncatedFreeLie X N)
                      (TruncatedBasisIndex X N)
                      (truncatedHomogeneousBasis X N) (correction i)) =
                    context ⁅truncatedHomogeneousBasis X N d.x,
                      truncatedHomogeneousBasis X N d.y⁆ := by
                rw [← hcontext]
                apply Finsupp.sum_congr
                intro i hi
                rw [map_zsmul]
                simp [context, correction, basisWord, word, List.map_append]
                noncomm_ring
              have hswapWord := envelopingWord_adjacent_swap ℤ
                (TruncatedFreeLie X N)
                (d.left.map (truncatedHomogeneousBasis X N))
                (d.right.map (truncatedHomogeneousBasis X N))
                (truncatedHomogeneousBasis X N d.x)
                (truncatedHomogeneousBasis X N d.y)
              rw [hxs]
              rw [hcontext']
              simpa only [swapped, context, basisWord, word, envelopingWord,
                List.map_append, List.map_cons, List.map_nil, List.map_map,
                Function.comp_apply] using hswapWord
            have hpoly :
                (truncatedPBWLinearEquiv X N).symm
                    (basisWord ℤ (TruncatedFreeLie X N)
                      (TruncatedBasisIndex X N)
                      (truncatedHomogeneousBasis X N) xs) =
                  (truncatedPBWLinearEquiv X N).symm
                    (basisWord ℤ (TruncatedFreeLie X N)
                      (TruncatedBasisIndex X N)
                      (truncatedHomogeneousBasis X N) swapped) +
                  c.sum (fun i z ↦ z •
                    (truncatedPBWLinearEquiv X N).symm
                      (basisWord ℤ (TruncatedFreeLie X N)
                        (TruncatedBasisIndex X N)
                        (truncatedHomogeneousBasis X N) (correction i))) := by
              rw [hword, map_add, map_finsuppSum]
              apply congrArg₂ (fun a b ↦ a + b) rfl
              apply Finsupp.sum_congr
              intro i hi
              rw [map_zsmul]
            rw [hpoly]
            apply MvPolynomial.IsWeightedHomogeneous.add
            · simpa [swapped, hxs, add_comm, add_left_comm, add_assoc] using hswap
            · apply (MvPolynomial.weightedHomogeneousSubmodule ℤ
                (truncatedBasisWeight X)
                ((xs.map (truncatedBasisWeight X)).sum)).sum_mem
              intro i hi
              apply (MvPolynomial.weightedHomogeneousSubmodule ℤ
                (truncatedBasisWeight X)
                ((xs.map (truncatedBasisWeight X)).sum)).smul_mem
              have hi' : i ∈ (truncatedBracketCoefficients X d.x d.y hweight).support := by
                simpa [c] using hi
              have hiImage := Finsupp.mapDomain_support hi'
              simp only [truncatedBracketCoefficients] at hiImage
              obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hiImage
              subst i
              simpa [correction, hxs, truncatedBasisWeight_indexOf,
                add_comm, add_left_comm, add_assoc] using
                  hcorrection (truncatedBasisIndexOf X
                    (Nat.add_pos_left (truncatedBasisWeight_pos X d.x) _) hweight j)
          · have hbracket :
                ⁅truncatedHomogeneousBasis X N d.x,
                  truncatedHomogeneousBasis X N d.y⁆ = 0 := by
              rw [truncatedHomogeneousBasis_apply,
                truncatedHomogeneousBasis_apply, ← LieHom.map_lie]
              apply (LieSubmodule.Quotient.mk_eq_zero'
                (N := lowerCentralSeries ℤ F N)).mpr
              let bracketExact : freeLieExact X
                  (truncatedBasisWeight X d.x + truncatedBasisWeight X d.y) :=
                ⟨⁅((freeLieExactBasis X (d.x.1.1 + 1) d.x.2 :
                    freeLieExact X (d.x.1.1 + 1)) : F),
                  ((freeLieExactBasis X (d.y.1.1 + 1) d.y.2 :
                    freeLieExact X (d.y.1.1 + 1)) : F)⁆,
                  freeLieExact_bracket_mem X
                    (freeLieExactBasis X (d.x.1.1 + 1) d.x.2)
                    (freeLieExactBasis X (d.y.1.1 + 1) d.y.2)⟩
              have hb := freeLieExact_mem_lieHigh X bracketExact
              have hb' : (bracketExact : F) ∈
                  lowerCentralSeries ℤ F
                    (truncatedBasisWeight X d.x +
                      truncatedBasisWeight X d.y - 1) := by
                change (bracketExact : F) ∈
                  (lowerCentralSeries ℤ F
                    (truncatedBasisWeight X d.x +
                      truncatedBasisWeight X d.y - 1)).toLieSubalgebra.toSubmodule
                rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries]
                convert hb using 1 <;> omega
              exact LieModule.antitone_lowerCentralSeries ℤ F F (by omega) hb'
            have hword :
                basisWord ℤ (TruncatedFreeLie X N)
                    (TruncatedBasisIndex X N)
                    (truncatedHomogeneousBasis X N) xs =
                  basisWord ℤ (TruncatedFreeLie X N)
                    (TruncatedBasisIndex X N)
                    (truncatedHomogeneousBasis X N) swapped := by
              have hswapWord := envelopingWord_adjacent_swap ℤ
                (TruncatedFreeLie X N)
                (d.left.map (truncatedHomogeneousBasis X N))
                (d.right.map (truncatedHomogeneousBasis X N))
                (truncatedHomogeneousBasis X N d.x)
                (truncatedHomogeneousBasis X N d.y)
              rw [hxs]
              rw [hbracket] at hswapWord
              simpa only [swapped, basisWord, word, envelopingWord,
                List.map_append, List.map_cons, List.map_nil, List.map_map,
                Function.comp_apply, map_zero, mul_zero, zero_mul,
                add_zero] using hswapWord
            rw [hword]
            simpa [swapped, hxs, add_comm, add_left_comm, add_assoc] using hswap

private theorem pbwPolynomial_iota_basis_mul_isWeighted {N W : ℕ}
    (i : TruncatedBasisIndex X N)
    (u : UEA ℤ (TruncatedFreeLie X N))
    (hu : MvPolynomial.IsWeightedHomogeneous (truncatedBasisWeight X)
      ((truncatedPBWLinearEquiv X N).symm u) W) :
    MvPolynomial.IsWeightedHomogeneous (truncatedBasisWeight X)
      ((truncatedPBWLinearEquiv X N).symm
        (UniversalEnvelopingAlgebra.ι ℤ
          (truncatedHomogeneousBasis X N i) * u))
      (truncatedBasisWeight X i + W) := by
  classical
  let E := truncatedPBWLinearEquiv X N
  let b := truncatedHomogeneousBasis X N
  let p : MvPolynomial (TruncatedBasisIndex X N) ℤ := E.symm u
  let sorted : (TruncatedBasisIndex X N →₀ ℕ) →
      List (TruncatedBasisIndex X N) := fun e ↦
    (Finsupp.toMultiset e).sort (· ≤ ·)
  have horderedMonomial (e : TruncatedBasisIndex X N →₀ ℕ) :
      orderedMonomial ℤ (TruncatedFreeLie X N)
          (TruncatedBasisIndex X N) b e =
        basisWord ℤ (TruncatedFreeLie X N)
          (TruncatedBasisIndex X N) b (sorted e) := by
    unfold orderedMonomial basisWord word sorted
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro j hj
    rfl
  have hEp : E p = p.sum (fun e c ↦ c •
      basisWord ℤ (TruncatedFreeLie X N)
        (TruncatedBasisIndex X N) b (sorted e)) := by
    change orderedPBWMap ℤ (TruncatedFreeLie X N)
        (TruncatedBasisIndex X N) b p = _
    unfold orderedPBWMap
    change p.sum (fun e c ↦ c •
      orderedMonomial ℤ (TruncatedFreeLie X N)
        (TruncatedBasisIndex X N) b e) = _
    apply Finsupp.sum_congr
    intro e he
    rw [horderedMonomial]
  have hproduct :
      UniversalEnvelopingAlgebra.ι ℤ (b i) * u =
        p.sum (fun e c ↦ c •
          basisWord ℤ (TruncatedFreeLie X N)
            (TruncatedBasisIndex X N) b (i :: sorted e)) := by
    have hEp' : E p = u := by
      simpa [E, p] using E.apply_symm_apply u
    calc
      UniversalEnvelopingAlgebra.ι ℤ (b i) * u =
          UniversalEnvelopingAlgebra.ι ℤ (b i) * E p := by
            exact congrArg
              (fun z ↦ UniversalEnvelopingAlgebra.ι ℤ (b i) * z) hEp'.symm
      _ = UniversalEnvelopingAlgebra.ι ℤ (b i) *
          p.sum (fun e c ↦ c •
            basisWord ℤ (TruncatedFreeLie X N)
              (TruncatedBasisIndex X N) b (sorted e)) := by rw [hEp]
      _ = _ := by
        rw [Finsupp.mul_sum]
        apply Finsupp.sum_congr
        intro e he
        rw [mul_smul_comm]
        simp only [basisWord_cons]
  rw [hproduct]
  rw [map_finsuppSum]
  apply (MvPolynomial.weightedHomogeneousSubmodule ℤ
    (truncatedBasisWeight X) (truncatedBasisWeight X i + W)).sum_mem
  intro e he
  change (truncatedPBWLinearEquiv X N).symm
      ((p e) • basisWord ℤ (TruncatedFreeLie X N)
        (TruncatedBasisIndex X N) b (i :: sorted e)) ∈ _
  rw [map_zsmul]
  apply (MvPolynomial.weightedHomogeneousSubmodule ℤ
    (truncatedBasisWeight X) (truncatedBasisWeight X i + W)).smul_mem
  have hword := pbwPolynomial_basisWord_isWeighted X N (i :: sorted e)
  have heweight : Finsupp.weight (truncatedBasisWeight X) e = W := by
    apply hu
    simpa [p, E] using (Finsupp.mem_support_iff.mp he)
  have hsortedWeight :
      ((sorted e).map (truncatedBasisWeight X)).sum = W := by
    have hw := weight_toMultiset X e
    rw [heweight] at hw
    rw [← Multiset.sum_coe]
    change (Multiset.map (truncatedBasisWeight X)
      (Multiset.ofList (sorted e))).sum = W
    rw [show Multiset.ofList (sorted e) = Finsupp.toMultiset e by
      simp [sorted]]
    exact hw.symm
  simpa only [b, E, List.map_cons, List.sum_cons, hsortedWeight] using hword

private theorem pbwPolynomial_generatorWord_isWeighted {N : ℕ}
    (hN : 1 ≤ N) (xs : List X) :
    MvPolynomial.IsWeightedHomogeneous (truncatedBasisWeight X)
      ((truncatedPBWLinearEquiv X N).symm
        (word ℤ (TruncatedFreeLie X N)
          (xs.map fun x ↦
            truncatedFreeLieMk X N (FreeLieAlgebra.of ℤ x))))
      xs.length := by
  classical
  induction xs with
  | nil =>
      simpa using pbwPolynomial_basisWord_isWeighted X N []
  | cons x xs ih =>
      let c : TruncatedBasisIndex X N →₀ ℤ :=
        ((freeLieExactBasis X 1).repr (freeGeneratorExactOne X x)).mapDomain
          (truncatedBasisIndexOf X (by omega) hN)
      have hc :
          c.sum (fun i a ↦ a • truncatedHomogeneousBasis X N i) =
            truncatedFreeLieMk X N (FreeLieAlgebra.of ℤ x) := by
        unfold c
        rw [Finsupp.sum_mapDomain_index]
        · simp_rw [truncatedHomogeneousBasis_indexOf]
          have hrepr := (freeLieExactBasis X 1).linearCombination_repr
            (freeGeneratorExactOne X x)
          calc
            ((freeLieExactBasis X 1).repr
                (freeGeneratorExactOne X x)).sum (fun i a ↦
                  a • truncatedFreeLieMk X N
                    (((freeLieExactBasis X 1 i : freeLieExact X 1) : F))) =
                truncatedFreeLieMk X N
                  (((freeLieExactBasis X 1).repr
                    (freeGeneratorExactOne X x)).sum (fun i a ↦
                      a • ((freeLieExactBasis X 1 i : freeLieExact X 1) : F))) := by
                    rw [map_finsuppSum]
                    apply Finsupp.sum_congr
                    intro i hi
                    rw [map_zsmul]
            _ = truncatedFreeLieMk X N (FreeLieAlgebra.of ℤ x) := by
                  apply congrArg (truncatedFreeLieMk X N)
                  calc
                    ((freeLieExactBasis X 1).repr
                        (freeGeneratorExactOne X x)).sum (fun i a ↦
                          a • ((freeLieExactBasis X 1 i : freeLieExact X 1) : F)) =
                        ((freeLieExact X 1).subtype
                          (((freeLieExactBasis X 1).repr
                            (freeGeneratorExactOne X x)).sum (fun i a ↦
                              a • freeLieExactBasis X 1 i))) := by
                                rw [map_finsuppSum]
                                apply Finsupp.sum_congr
                                intro i hi
                                rw [map_zsmul]
                                rfl
                    _ = FreeLieAlgebra.of ℤ x := congrArg Subtype.val hrepr
        · intro i
          simp
        · intro i a b
          simp [add_smul]
      let u := word ℤ (TruncatedFreeLie X N)
        (xs.map fun y ↦ truncatedFreeLieMk X N (FreeLieAlgebra.of ℤ y))
      have hproduct :
          UniversalEnvelopingAlgebra.ι ℤ
                (truncatedFreeLieMk X N (FreeLieAlgebra.of ℤ x)) * u =
            c.sum (fun i a ↦ a •
              (UniversalEnvelopingAlgebra.ι ℤ
                (truncatedHomogeneousBasis X N i) * u)) := by
        rw [← hc, map_finsuppSum, Finsupp.sum_mul]
        apply Finsupp.sum_congr
        intro i hi
        rw [map_zsmul, smul_mul_assoc]
      simp only [List.map_cons, word_cons, List.length_cons]
      change MvPolynomial.IsWeightedHomogeneous (truncatedBasisWeight X)
        ((truncatedPBWLinearEquiv X N).symm
          (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedFreeLieMk X N (FreeLieAlgebra.of ℤ x)) * u))
        (xs.length + 1)
      rw [hproduct, map_finsuppSum]
      apply (MvPolynomial.weightedHomogeneousSubmodule ℤ
        (truncatedBasisWeight X) (xs.length + 1)).sum_mem
      intro i hi
      change (truncatedPBWLinearEquiv X N).symm
          ((c i) • (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedHomogeneousBasis X N i) * u)) ∈ _
      rw [map_zsmul]
      apply (MvPolynomial.weightedHomogeneousSubmodule ℤ
        (truncatedBasisWeight X) (xs.length + 1)).smul_mem
      have hiImage := Finsupp.mapDomain_support hi
      simp only [c] at hiImage
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hiImage
      subst i
      simpa [u, truncatedBasisWeight_indexOf, Nat.add_comm] using
        (pbwPolynomial_iota_basis_mul_isWeighted X
          (truncatedBasisIndexOf X (by omega) hN j) u ih)

/-! ## The governing free-presentation equation -/

/-- The data retained from the free dimension witness after its arbitrary UEA multipliers have
been expanded into genuine generator words. -/
structure GoverningWitness (n : ℕ) (L : Type v) [LieRing L] (a : L) where
  zTilde : freeLieExact L (n + 1)
  evaluates : canonicalFreeLieEvaluation L (zTilde : CanonicalFreeLie L) = a
  relationWords :
    (CanonicalLieRelationsIdeal L × List L) →₀ ℤ

namespace GoverningWitness

variable {L : Type v} [LieRing L]

/-- The finite relation-on-the-left sum after passage to the weight-`2*n` truncation. -/
def relationSide [Finite L] {n : ℕ} {a : L}
    (w : GoverningWitness n L a) :
    UEA ℤ (TruncatedFreeLie L (2 * n)) :=
  w.relationWords.sum fun p c ↦ c •
    (UniversalEnvelopingAlgebra.ι ℤ
        (truncatedFreeLieMk L (2 * n) (p.1 : CanonicalFreeLie L)) *
      word ℤ (TruncatedFreeLie L (2 * n))
        (p.2.map fun x ↦
          truncatedFreeLieMk L (2 * n) (FreeLieAlgebra.of ℤ x)))

end GoverningWitness

/-- The finite governing PBW equation attached to a reduced top-layer dimension witness. -/
theorem governingPBWCoefficients (n : ℕ) (hn : 1 ≤ n)
    (L : Type u) [LieRing L] [Finite L]
    (R : ReducedData n L) (a : L)
    (haDim : a ∈ dimensionSubring ℤ L (2 * n + 1))
    (haTop : a ∈ lowerCentralSeries ℤ L n) :
    ∃ w : GoverningWitness n L a,
      ∀ e : TruncatedBasisIndex L (2 * n) →₀ ℕ,
        totalWeight L e ≤ 2 * n →
          pbwCoeff L (2 * n) w.relationSide e =
            pbwCoeff L (2 * n)
              (UniversalEnvelopingAlgebra.ι ℤ
                (truncatedFreeLieMk L (2 * n)
                  (w.zTilde : CanonicalFreeLie L))) e := by
  let ev := canonicalFreeLieEvaluation L
  have haMap : a ∈
      (lowerCentralSeries ℤ (CanonicalFreeLie L) n).map ev := by
    rw [LieIdeal.lowerCentralSeries_map_eq n
      (canonicalFreeLieEvaluation_surjective L)]
    exact haTop
  obtain ⟨f, hfEval⟩ := LieIdeal.mem_map_of_surjective
    (I := lowerCentralSeries ℤ (CanonicalFreeLie L) n)
    (canonicalFreeLieEvaluation_surjective L) haMap
  let zTilde : freeLieExact L (n + 1) :=
    ⟨freeLieLengthComponent L (n + 1) (f : CanonicalFreeLie L),
      freeLieLengthComponent_mem_exact L (n + 1) f⟩
  let remainder : CanonicalFreeLie L := (f : CanonicalFreeLie L) - zTilde
  have hfHigh : (f : CanonicalFreeLie L) ∈
      FreeLieDimension.lieHigh L (n + 1) := by
    rw [FreeLieDimension.lieHigh_eq_lowerCentralSeries L n]
    exact f.property
  have hremHigh : remainder ∈ FreeLieDimension.lieHigh L (n + 2) := by
    apply mem_lieHigh_succ_of_component_eq_zero L
    · apply (FreeLieDimension.lieHigh L (n + 1)).sub_mem hfHigh
        (freeLieExact_mem_lieHigh L zTilde)
    · dsimp only [remainder]
      rw [map_sub, freeLieLengthComponent_coe_exact L (n + 1) zTilde]
      exact sub_self _
  have hremLcs : remainder ∈
      lowerCentralSeries ℤ (CanonicalFreeLie L) (n + 1) := by
    change remainder ∈
      (lowerCentralSeries ℤ (CanonicalFreeLie L) (n + 1)).toLieSubalgebra.toSubmodule
    rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries L (n + 1)]
    simpa [Nat.add_assoc] using hremHigh
  have hremEvalMem : ev remainder ∈ lowerCentralSeries ℤ L (n + 1) := by
    apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) (n + 1))
    exact LieIdeal.mem_map hremLcs
  have hremEval : ev remainder = 0 := by
    rw [R.classBound] at hremEvalMem
    exact hremEvalMem
  have hzEval : ev (zTilde : CanonicalFreeLie L) = a := by
    have h := hremEval
    change ev ((f : CanonicalFreeLie L) - (zTilde : CanonicalFreeLie L)) = 0 at h
    rw [map_sub, hfEval] at h
    exact (sub_eq_zero.mp h).symm
  have haAug : UniversalEnvelopingAlgebra.ι ℤ a ∈
      UEA.augmentationIdeal ℤ L ^ (2 * n + 1) :=
    (mem_dimensionSubring ℤ L).mp haDim
  obtain ⟨highWord, hhighPow, hhighEval⟩ :=
    UEA.exists_mem_augmentationIdeal_pow_succ_of_surjective ℤ
      (CanonicalFreeLie L) L ev
      (canonicalFreeLieEvaluation_surjective L) (2 * n) haAug
  have hdiffZero :
      UEA.map ℤ (CanonicalFreeLie L) L ev
          (UniversalEnvelopingAlgebra.ι ℤ
            (zTilde : CanonicalFreeLie L) - highWord) = 0 := by
    rw [map_sub, UEA.map_ι, hzEval, hhighEval, sub_self]
  have hdiff :=
    (mem_kernel_canonical_uea_evaluation_iff_relation_sum L
      (UniversalEnvelopingAlgebra.ι ℤ
        (zTilde : CanonicalFreeLie L) - highWord)).mp hdiffZero
  obtain ⟨relationCoefficients, hrelationCoefficients⟩ :=
    exists_relation_finsupp_of_mem_rightRelationSpan ℤ
      (CanonicalFreeLie L) (CanonicalLieRelationsIdeal L) hdiff
  let relationWords :
      (CanonicalLieRelationsIdeal L × List L) →₀ ℤ :=
    relationCoefficients.sum fun p k ↦
      (placedWordCoefficients p).sum fun word m ↦
        Finsupp.single (p.1, FreeMonoid.toList word) (k * m)
  let freeEquiv :=
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
  have hwordUnderEquiv (ys : List L) :
      freeEquiv
          (word ℤ (CanonicalFreeLie L)
            (ys.map (FreeLieAlgebra.of ℤ))) =
        freeAlgebraWord L ys := by
    simpa [freeEquiv, word, envelopingWord] using
      (universalEnvelopingEquiv_envelopingWord_of (L := L) ys)
  have hplacedProduct
      (p : CanonicalLieRelationsIdeal L ×
        UEA ℤ (CanonicalFreeLie L)) :
      (placedWordCoefficients p).sum (fun wd m ↦ m •
          (UniversalEnvelopingAlgebra.ι ℤ
              (p.1 : CanonicalFreeLie L) *
            word ℤ (CanonicalFreeLie L)
              ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ)))) =
        UniversalEnvelopingAlgebra.ι ℤ
            (p.1 : CanonicalFreeLie L) * p.2 := by
    apply freeEquiv.injective
    calc
      freeEquiv ((placedWordCoefficients p).sum (fun wd m ↦ m •
          (UniversalEnvelopingAlgebra.ι ℤ
              (p.1 : CanonicalFreeLie L) *
            word ℤ (CanonicalFreeLie L)
              ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))))) =
          (placedWordCoefficients p).sum (fun wd m ↦ m •
            (PBW.freeLieToFreeAlgebra ℤ L (p.1 : CanonicalFreeLie L) *
              freeAlgebraWord L (FreeMonoid.toList wd))) := by
            rw [map_finsuppSum]
            apply Finsupp.sum_congr
            intro wd hwd
            change (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                ((placedWordCoefficients p) wd •
                  (UniversalEnvelopingAlgebra.ι ℤ
                      (p.1 : CanonicalFreeLie L) *
                    word ℤ (CanonicalFreeLie L)
                      ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ)))) = _
            calc
              _ = (placedWordCoefficients p) wd •
                  (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                    (UniversalEnvelopingAlgebra.ι ℤ
                        (p.1 : CanonicalFreeLie L) *
                      word ℤ (CanonicalFreeLie L)
                        ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))) :=
                    map_zsmul
                      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                      ((placedWordCoefficients p) wd) _
              _ = _ := by
                congr 1
                calc
                  (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                      (UniversalEnvelopingAlgebra.ι ℤ
                          (p.1 : CanonicalFreeLie L) *
                        word ℤ (CanonicalFreeLie L)
                          ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))) =
                      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                          (UniversalEnvelopingAlgebra.ι ℤ
                            (p.1 : CanonicalFreeLie L)) *
                        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                          (word ℤ (CanonicalFreeLie L)
                            ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))) :=
                        map_mul
                          (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L) _ _
                  _ = _ := by
                    exact congrArg₂ (fun s t ↦ s * t)
                      (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
                        L (p.1 : CanonicalFreeLie L))
                      (hwordUnderEquiv (FreeMonoid.toList wd))
      _ = PBW.freeLieToFreeAlgebra ℤ L (p.1 : CanonicalFreeLie L) *
          freeEquiv p.2 := placedWordCoefficients_evaluate p
      _ = freeEquiv
          (UniversalEnvelopingAlgebra.ι ℤ
            (p.1 : CanonicalFreeLie L) * p.2) := by
            rw [← FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra]
            exact (map_mul freeEquiv _ _).symm
  have hflatten
      (p : CanonicalLieRelationsIdeal L × UEA ℤ (CanonicalFreeLie L))
      (k : ℤ) (c : FreeMonoid L →₀ ℤ) :
      (c.sum fun wd m ↦
          Finsupp.single (p.1, FreeMonoid.toList wd) (k * m)).sum
        (fun q d ↦ d •
          (UniversalEnvelopingAlgebra.ι ℤ
              (q.1 : CanonicalFreeLie L) *
            word ℤ (CanonicalFreeLie L)
              (q.2.map (FreeLieAlgebra.of ℤ)))) =
        k • c.sum (fun wd m ↦ m •
          (UniversalEnvelopingAlgebra.ι ℤ
              (p.1 : CanonicalFreeLie L) *
            word ℤ (CanonicalFreeLie L)
              ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ)))) := by
    classical
    induction c using Finsupp.induction with
    | zero => simp
    | single_add wd m c hwd hm ih =>
        rw [Finsupp.sum_add_index
          (fun _ _ ↦ by simp)
          (fun _ _ b₁ b₂ ↦ by rw [mul_add, Finsupp.single_add])]
        rw [Finsupp.sum_add_index
          (fun _ _ ↦ by simp)
          (fun _ _ b₁ b₂ ↦ add_zsmul _ b₁ b₂)]
        rw [ih, Finsupp.sum_add_index
          (fun _ _ ↦ by simp)
          (fun _ _ b₁ b₂ ↦ add_zsmul _ b₁ b₂)]
        simp [smul_smul]
        noncomm_ring
  have hrelationWordsEvaluate :
      relationWords.sum (fun p k ↦ k •
        (UniversalEnvelopingAlgebra.ι ℤ
            (p.1 : CanonicalFreeLie L) *
          word ℤ (CanonicalFreeLie L)
            (p.2.map (FreeLieAlgebra.of ℤ)))) =
        UniversalEnvelopingAlgebra.ι ℤ
            (zTilde : CanonicalFreeLie L) - highWord := by
    unfold relationWords
    rw [Finsupp.sum_sum_index (fun _ ↦ by simp)
      (fun _ a b ↦ add_zsmul _ a b)]
    calc
      relationCoefficients.sum (fun p k ↦
          ((placedWordCoefficients p).sum fun wd m ↦
              Finsupp.single (p.1, FreeMonoid.toList wd) (k * m)).sum
            (fun q d ↦ d •
              (UniversalEnvelopingAlgebra.ι ℤ
                  (q.1 : CanonicalFreeLie L) *
                word ℤ (CanonicalFreeLie L)
                  (q.2.map (FreeLieAlgebra.of ℤ))))) =
          relationCoefficients.sum (fun p k ↦ k •
            (placedWordCoefficients p).sum (fun wd m ↦ m •
              (UniversalEnvelopingAlgebra.ι ℤ
                  (p.1 : CanonicalFreeLie L) *
                word ℤ (CanonicalFreeLie L)
                  ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))))) := by
                    apply Finsupp.sum_congr
                    intro p hp
                    exact hflatten p (relationCoefficients p)
                      (placedWordCoefficients p)
      _ = relationCoefficients.sum (fun p k ↦ k •
            (UniversalEnvelopingAlgebra.ι ℤ
              (p.1 : CanonicalFreeLie L) * p.2)) := by
              apply Finsupp.sum_congr
              intro p hp
              exact congrArg ((relationCoefficients p) • ·)
                (hplacedProduct p)
      _ = _ := hrelationCoefficients
  let quotientMap := truncatedFreeLieMk L (2 * n)
  let quotientUEAMap := UEA.map ℤ (CanonicalFreeLie L)
    (TruncatedFreeLie L (2 * n)) quotientMap
  have hquotientWord (ys : List L) :
      quotientUEAMap
          (word ℤ (CanonicalFreeLie L)
            (ys.map (FreeLieAlgebra.of ℤ))) =
        word ℤ (TruncatedFreeLie L (2 * n))
          (ys.map fun x ↦ quotientMap (FreeLieAlgebra.of ℤ x)) := by
    induction ys with
    | nil =>
        simpa [word] using map_one quotientUEAMap
    | cons x ys ih =>
        simp only [List.map_cons, word_cons]
        change quotientUEAMap
            (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x) *
              word ℤ (CanonicalFreeLie L)
                (ys.map (FreeLieAlgebra.of ℤ))) = _
        rw [map_mul, UEA.map_ι, ih]
  let highAssociative := freeEquiv highWord
  let highCoefficients :=
    FreeAlgebra.equivMonoidAlgebraFreeMonoid highAssociative
  have hhighAssociative : highAssociative ∈
      FreeLieDimension.associativeHigh L (2 * n + 1) := by
    exact FreeLieDimension.universalEnvelopingEquiv_mem_associativeHigh
      L (2 * n + 1) hhighPow
  have hhighExpansion :
      highCoefficients.sum (fun wd k ↦ k •
        word ℤ (CanonicalFreeLie L)
          ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))) =
        highWord := by
    apply freeEquiv.injective
    calc
      freeEquiv (highCoefficients.sum (fun wd k ↦ k •
          word ℤ (CanonicalFreeLie L)
            ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ)))) =
          highCoefficients.sum (fun wd k ↦ k •
            freeAlgebraWord L (FreeMonoid.toList wd)) := by
              rw [map_finsuppSum]
              apply Finsupp.sum_congr
              intro wd hwd
              change (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                  ((highCoefficients wd) •
                    word ℤ (CanonicalFreeLie L)
                      ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))) = _
              calc
                _ = (highCoefficients wd) •
                    (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                      (word ℤ (CanonicalFreeLie L)
                        ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))) :=
                      map_zsmul
                        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
                        (highCoefficients wd) _
                _ = _ := congrArg ((highCoefficients wd) • ·)
                  (hwordUnderEquiv (FreeMonoid.toList wd))
      _ = highAssociative := by
        simpa only [highCoefficients] using
          (freeAlgebra_eq_word_sum L highAssociative)
      _ = freeEquiv highWord := rfl
  have hquotientHighExpansion :
      quotientUEAMap highWord =
        highCoefficients.sum (fun wd k ↦ k •
          word ℤ (TruncatedFreeLie L (2 * n))
            ((FreeMonoid.toList wd).map fun x ↦
              quotientMap (FreeLieAlgebra.of ℤ x))) := by
    rw [← hhighExpansion, map_finsuppSum]
    apply Finsupp.sum_congr
    intro wd hwd
    change quotientUEAMap
        ((highCoefficients wd) •
          word ℤ (CanonicalFreeLie L)
            ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))) = _
    calc
      _ = (highCoefficients wd) • quotientUEAMap
          (word ℤ (CanonicalFreeLie L)
            ((FreeMonoid.toList wd).map (FreeLieAlgebra.of ℤ))) :=
        map_zsmul quotientUEAMap (highCoefficients wd) _
      _ = _ := congrArg ((highCoefficients wd) • ·)
        (hquotientWord (FreeMonoid.toList wd))
  have hhighCoefficient
      (e : TruncatedBasisIndex L (2 * n) →₀ ℕ)
      (he : totalWeight L e ≤ 2 * n) :
      pbwCoeff L (2 * n) (quotientUEAMap highWord) e = 0 := by
    rw [hquotientHighExpansion]
    unfold pbwCoeff
    rw [map_finsuppSum]
    unfold Finsupp.sum
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro wd hwd
    change MvPolynomial.coeff e
        ((truncatedPBWLinearEquiv L (2 * n)).symm
          ((highCoefficients wd) •
            word ℤ (TruncatedFreeLie L (2 * n))
              ((FreeMonoid.toList wd).map fun x ↦
                quotientMap (FreeLieAlgebra.of ℤ x)))) = 0
    rw [map_zsmul]
    have hwordCoefficient :
        MvPolynomial.coeff e
          ((truncatedPBWLinearEquiv L (2 * n)).symm
            (word ℤ (TruncatedFreeLie L (2 * n))
              ((FreeMonoid.toList wd).map fun x ↦
                quotientMap (FreeLieAlgebra.of ℤ x)))) = 0 := by
      by_contra hne
      have hexact :=
        (pbwPolynomial_generatorWord_isWeighted L (N := 2 * n)
          (by omega) (FreeMonoid.toList wd)) hne
      have htotal :
          Finsupp.weight (truncatedBasisWeight L) e = totalWeight L e := by
        simp [Finsupp.weight_apply, totalWeight, nsmul_eq_mul]
      rw [htotal] at hexact
      have hlength : 2 * n + 1 ≤ (FreeMonoid.toList wd).length := by
        simpa [highAssociative, highCoefficients] using
          hhighAssociative hwd
      omega
    calc
      MvPolynomial.coeff e
          ((highCoefficients wd) •
            (truncatedPBWLinearEquiv L (2 * n)).symm
              (word ℤ (TruncatedFreeLie L (2 * n))
                ((FreeMonoid.toList wd).map fun x ↦
                  quotientMap (FreeLieAlgebra.of ℤ x)))) =
          (highCoefficients wd) •
            MvPolynomial.coeff e
              ((truncatedPBWLinearEquiv L (2 * n)).symm
                (word ℤ (TruncatedFreeLie L (2 * n))
                  ((FreeMonoid.toList wd).map fun x ↦
                    quotientMap (FreeLieAlgebra.of ℤ x)))) :=
            map_zsmul (MvPolynomial.coeffAddMonoidHom e)
              (highCoefficients wd) _
      _ = 0 := by rw [hwordCoefficient, smul_zero]
  let w : GoverningWitness n L a :=
    { zTilde := zTilde
      evaluates := hzEval
      relationWords := relationWords }
  refine ⟨w, ?_⟩
  intro e he
  have hside :
      quotientUEAMap
          (relationWords.sum (fun p k ↦ k •
            (UniversalEnvelopingAlgebra.ι ℤ
                (p.1 : CanonicalFreeLie L) *
              word ℤ (CanonicalFreeLie L)
                (p.2.map (FreeLieAlgebra.of ℤ))))) =
        w.relationSide := by
    calc
      quotientUEAMap
          (relationWords.sum (fun p k ↦ k •
            (UniversalEnvelopingAlgebra.ι ℤ
                (p.1 : CanonicalFreeLie L) *
              word ℤ (CanonicalFreeLie L)
                (p.2.map (FreeLieAlgebra.of ℤ))))) =
          relationWords.sum (fun p k ↦ k •
            (UniversalEnvelopingAlgebra.ι ℤ
                (quotientMap (p.1 : CanonicalFreeLie L)) *
              word ℤ (TruncatedFreeLie L (2 * n))
                (p.2.map fun x ↦
                  quotientMap (FreeLieAlgebra.of ℤ x)))) := by
            rw [map_finsuppSum]
            apply Finsupp.sum_congr
            intro p hp
            change quotientUEAMap
                ((relationWords p) •
                  (UniversalEnvelopingAlgebra.ι ℤ
                      (p.1 : CanonicalFreeLie L) *
                    word ℤ (CanonicalFreeLie L)
                      (p.2.map (FreeLieAlgebra.of ℤ)))) = _
            calc
              _ = (relationWords p) • quotientUEAMap
                  (UniversalEnvelopingAlgebra.ι ℤ
                      (p.1 : CanonicalFreeLie L) *
                    word ℤ (CanonicalFreeLie L)
                      (p.2.map (FreeLieAlgebra.of ℤ))) :=
                    map_zsmul quotientUEAMap (relationWords p) _
              _ = _ := by
                congr 1
                calc
                  quotientUEAMap
                      (UniversalEnvelopingAlgebra.ι ℤ
                          (p.1 : CanonicalFreeLie L) *
                        word ℤ (CanonicalFreeLie L)
                          (p.2.map (FreeLieAlgebra.of ℤ))) =
                      quotientUEAMap
                          (UniversalEnvelopingAlgebra.ι ℤ
                            (p.1 : CanonicalFreeLie L)) *
                        quotientUEAMap
                          (word ℤ (CanonicalFreeLie L)
                            (p.2.map (FreeLieAlgebra.of ℤ))) :=
                        map_mul quotientUEAMap _ _
                  _ = _ := congrArg₂ (fun s t ↦ s * t)
                    (UEA.map_ι ℤ (CanonicalFreeLie L)
                      (TruncatedFreeLie L (2 * n)) quotientMap
                      (p.1 : CanonicalFreeLie L))
                    (hquotientWord p.2)
      _ = w.relationSide := by
        rfl
  have hmapped := congrArg quotientUEAMap hrelationWordsEvaluate
  rw [hside, map_sub, UEA.map_ι] at hmapped
  have hgoverning :
      w.relationSide + quotientUEAMap highWord =
        UniversalEnvelopingAlgebra.ι ℤ
          (quotientMap (zTilde : CanonicalFreeLie L)) := by
    rw [hmapped]
    abel
  have hcoordinate := congrArg
    (fun q ↦ pbwCoeff L (2 * n) q e) hgoverning
  unfold pbwCoeff at hcoordinate ⊢
  change MvPolynomial.coeff e
      ((truncatedPBWLinearEquiv L (2 * n)).symm
        (w.relationSide + quotientUEAMap highWord)) =
    MvPolynomial.coeff e
      ((truncatedPBWLinearEquiv L (2 * n)).symm
        (UniversalEnvelopingAlgebra.ι ℤ
          (quotientMap (zTilde : CanonicalFreeLie L)))) at hcoordinate
  rw [map_add, MvPolynomial.coeff_add] at hcoordinate
  have hzero := hhighCoefficient e he
  unfold pbwCoeff at hzero
  rw [hzero, add_zero] at hcoordinate
  simpa only [w, quotientMap] using hcoordinate


end


end LieRings.DimensionSubring.MetabelianOdd
