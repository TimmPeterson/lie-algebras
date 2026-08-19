import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalComb

/-!
# The one-factor read of an ordered PBW word

The exceptional all-weight-one calculation repeatedly uses one elementary
PBW fact: once a branch is an ordered word and still has either zero or at
least two factors, it cannot contribute to the complete one-factor read.
This file records that fact for the weighted integral PBW basis and then in
the `pbwPrimitive` notation used by the terminal ledger.
-/

namespace LieRings

open FreeMetabelian
open LieRings.PBW

universe u v

noncomputable section

set_option maxHeartbeats 2000000

namespace PBW

variable {F : Type u} [LieRing F]
variable {ι : Type v} [LinearOrder ι]

/-- An ordered basis word contributes to the complete one-factor PBW
projection precisely when its displayed list has length one. -/
theorem WeightedBasis.factorProj_one_basisWord_eq_zero_of_pairwise
    (B : WeightedBasis (L := F) (ι := ι))
    (xs : List ι) (hordered : xs.Pairwise (· ≤ ·))
    (hlen : xs.length ≠ 1) :
    B.factorProj 1 (basisWord ℤ F ι B.basis xs) = 0 := by
  classical
  let e : ι →₀ ℕ := Multiset.toFinsupp (xs : Multiset ι)
  have hword : orderedMonomial ℤ F ι B.basis e =
      basisWord ℤ F ι B.basis xs := by
    simpa only [e] using
      orderedMonomial_multiset_toFinsupp ℤ F ι B.basis xs hordered
  have hmonomial : basisWord ℤ F ι B.basis xs =
      B.pbwEquiv (MvPolynomial.monomial e 1) := by
    rw [B.pbwEquiv_monomial, one_smul, hword]
  rw [hmonomial, B.factorProj_monomial]
  have hfactor : WeightedBasis.factorNumber e = xs.length := by
    change (Multiset.toFinsupp (xs : Multiset ι)).sum (fun _ ↦ id) =
      xs.length
    simpa only [Multiset.card_coe] using
      (Multiset.toFinsupp_sum_eq (xs : Multiset ι))
  rw [if_neg]
  intro hone
  exact hlen (hfactor.symm.trans hone)

end PBW

namespace MetabelianVanishing

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance orderedPBWPrimitiveFintype : Fintype L := Fintype.ofFinite L

private theorem tail_one_lie_adaptedBasis
    (d : FreeModel n L)
    (hd : d ∈ FreeMetabelian.Free.tail
      (X := Generator L) (c := n + 1) 1)
    (x : AdaptedIndex n L data hn) :
    ⁅d, adaptedBasis n L data hn x⁆ ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) 1 := by
  rw [adaptedBasis_apply]
  have hhigh := RelationContext.bracket_weightIncl_right_mem_tail
    n L d 1 x.1.val x.1.isLt hd
      (pieceAdaptedBasis n L data hn x.1 x.2)
  rw [FreeMetabelian.Free.mem_tail_iff] at hhigh ⊢
  intro i hi
  exact hhigh i (by omega)

/-- An ordered nonempty spectator word followed by a derived element has no
complete one-factor PBW component. -/
theorem pbwPrimitive_basisWord_mul_iota_of_mem_tail_one_eq_zero
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·)) (hne : xs ≠ [])
    (d : FreeModel n L)
    (hd : d ∈ FreeMetabelian.Free.tail
      (X := Generator L) (c := n + 1) 1) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ d) = 0 := by
  change (SymmetricPower.degreeOneLinearEquiv
      (adaptedBasis n L data hn))
    (fullRightSymbol n L data hn 1
      (MarkedRow.basisWord n L data hn xs *
        UniversalEnvelopingAlgebra.ι ℤ d)) = 0
  rw [fullRightSymbol_basisWord_mul_iota_of_mem_tail_one_eq_zero
    n L data hn 1 d xs hordered hd]
  · exact map_zero _
  · have hpos : 0 < xs.length := Nat.pos_of_ne_zero (by
      intro hz
      exact hne (List.eq_nil_of_length_eq_zero hz))
    omega

/-- If a derived factor has a nonempty ordered spectator prefix, then no
amount of collecting it through the ordered suffix can create a complete
one-factor term: that prefix remains as an ordinary PBW spectator. -/
theorem pbwPrimitive_basisWord_mul_iota_mul_basisWord_eq_zero_of_mem_tail_one
    (left right : List (AdaptedIndex n L data hn))
    (hordered : (left ++ right).Pairwise (· ≤ ·)) (hleft : left ≠ [])
    (d : FreeModel n L)
    (hd : d ∈ FreeMetabelian.Free.tail
      (X := Generator L) (c := n + 1) 1) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ d *
          MarkedRow.basisWord n L data hn right) = 0 := by
  induction right generalizing left d with
  | nil =>
      simpa [MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word] using
        pbwPrimitive_basisWord_mul_iota_of_mem_tail_one_eq_zero
          n L data hn left (by simpa using hordered) hleft d hd
  | cons x xs ih =>
      have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
        (FreeModel n L) d (adaptedBasis n L data hn x)
      have hword : MarkedRow.basisWord n L data hn (x :: xs) =
          UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn x) *
            MarkedRow.basisWord n L data hn xs := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      have hvalue :
          MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ d *
                MarkedRow.basisWord n L data hn (x :: xs) =
            (MarkedRow.basisWord n L data hn (left ++ [x]) *
                UniversalEnvelopingAlgebra.ι ℤ d *
                MarkedRow.basisWord n L data hn xs) +
              (MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ
                  ⁅d, adaptedBasis n L data hn x⁆ *
                MarkedRow.basisWord n L data hn xs) := by
        calc
          _ = MarkedRow.basisWord n L data hn left *
                (UniversalEnvelopingAlgebra.ι ℤ d *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn x)) *
                MarkedRow.basisWord n L data hn xs := by
              rw [hword]
              noncomm_ring
          _ = MarkedRow.basisWord n L data hn left *
                (UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn x) *
                    UniversalEnvelopingAlgebra.ι ℤ d +
                  UniversalEnvelopingAlgebra.ι ℤ
                    ⁅d, adaptedBasis n L data hn x⁆) *
                MarkedRow.basisWord n L data hn xs := by rw [hswap]
          _ = _ := by
              simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
                LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
              noncomm_ring
      rw [hvalue, map_add]
      have horderedFirst : ((left ++ [x]) ++ xs).Pairwise (· ≤ ·) := by
        simpa [List.append_assoc] using hordered
      have horderedSecond : (left ++ xs).Pairwise (· ≤ ·) := by
        apply List.Pairwise.sublist
        exact List.Sublist.append (List.Sublist.refl left)
          (List.tail_sublist (x :: xs))
        exact hordered
      rw [ih (left ++ [x]) horderedFirst (by simp) d hd,
        ih left horderedSecond hleft
          ⁅d, adaptedBasis n L data hn x⁆
          (tail_one_lie_adaptedBasis n L data hn d hd x), add_zero]

private theorem leftInsertion_ordered_basisWord_eq_zero
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·)) (hlen : xs.length ≠ 1) :
    pbwPrimitive n L data hn
        (LieRings.PBW.basisWord ℤ (FreeModel n L)
          (AdaptedIndex n L data hn) (adaptedBasis n L data hn) xs) = 0 := by
  apply LieRings.PBW.canonicalMap_injective_of_freeModulePBW
    ℤ (FreeModel n L) (AdaptedIndex n L data hn)
    (adaptedWeightedBasis n L data hn).basis
    (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis)
  rw [← factorProj_one_eq_iota_pbwPrimitive n L data hn]
  simpa only [adaptedWeightedBasis, map_zero] using
    WeightedBasis.factorProj_one_basisWord_eq_zero_of_pairwise
      (adaptedWeightedBasis n L data hn) xs hordered hlen

/-- An ordinary basis factor which has already crossed to the left of an
inserted basis factor is a permanent PBW spectator.  Continuing to collect
the inserted factor through the ordered suffix cannot create a one-factor
term: the principal term eventually becomes an ordered word of length at
least two, while every commutator correction is derived and retains the
nonempty spectator prefix.

This is the left-edge counterpart of
`pbwPrimitive_basisWord_mul_iota_eq_zero_of_ordered_insertion`.  It is the
precise PBW calculation used by the corrected manuscript when the
weight-one triangular head starts on the left of the ordinary word. -/
theorem pbwPrimitive_basisWord_mul_iota_basis_mul_basisWord_eq_zero
    (left right : List (AdaptedIndex n L data hn))
    (h : AdaptedIndex n L data hn)
    (hleft : left ≠ [])
    (hordered : (left ++ right).Pairwise (· ≤ ·))
    (hle : ∀ x ∈ left, x ≤ h) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn h) *
          MarkedRow.basisWord n L data hn right) = 0 := by
  induction right generalizing left with
  | nil =>
      have hordered' : (left ++ [h]).Pairwise (· ≤ ·) := by
        rw [List.pairwise_append]
        exact ⟨by simpa using hordered, by simp, by simpa using hle⟩
      have hword :
          MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn h) *
                MarkedRow.basisWord n L data hn [] =
            LieRings.PBW.basisWord ℤ (FreeModel n L)
              (AdaptedIndex n L data hn) (adaptedBasis n L data hn)
              (left ++ [h]) := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
      rw [hword]
      apply leftInsertion_ordered_basisWord_eq_zero
        n L data hn (left ++ [h]) hordered'
      have hpos : 0 < left.length := Nat.pos_of_ne_zero (by
        intro hz
        exact hleft (List.eq_nil_of_length_eq_zero hz))
      simp only [List.length_append, List.length_singleton]
      omega
  | cons x xs ih =>
      have hrightOrdered : (x :: xs).Pairwise (· ≤ ·) :=
        (List.pairwise_append.mp hordered).2.1
      have htailOrdered : xs.Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hrightOrdered).2
      have hleftXsOrdered : (left ++ xs).Pairwise (· ≤ ·) := by
        apply List.Pairwise.sublist
        · exact List.Sublist.append (List.Sublist.refl left)
            (List.tail_sublist (x :: xs))
        · exact hordered
      by_cases hhx : h ≤ x
      · have hinsertedOrdered : (left ++ [h] ++ x :: xs).Pairwise (· ≤ ·) := by
          rw [List.pairwise_append]
          refine ⟨?_, hrightOrdered, ?_⟩
          · rw [List.pairwise_append]
            exact ⟨(List.pairwise_append.mp hordered).1, by simp,
              by simpa using hle⟩
          · intro y hy z hz
            simp only [List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact (List.pairwise_append.mp hordered).2.2 y hy z hz
            · simp only [List.mem_cons] at hz
              rcases hz with rfl | hz
              · exact hhx
              · exact hhx.trans ((List.pairwise_cons.mp hrightOrdered).1 z hz)
        have hword :
            MarkedRow.basisWord n L data hn left *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn h) *
                  MarkedRow.basisWord n L data hn (x :: xs) =
              LieRings.PBW.basisWord ℤ (FreeModel n L)
                (AdaptedIndex n L data hn) (adaptedBasis n L data hn)
                (left ++ [h] ++ x :: xs) := by
          simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
          noncomm_ring
        rw [hword]
        apply leftInsertion_ordered_basisWord_eq_zero
          n L data hn (left ++ [h] ++ x :: xs) hinsertedOrdered
        have hpos : 0 < left.length := Nat.pos_of_ne_zero (by
          intro hz
          exact hleft (List.eq_nil_of_length_eq_zero hz))
        simp only [List.length_append, List.length_singleton,
          List.length_cons]
        omega
      · have hxh : x ≤ h := le_of_not_ge hhx
        have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
          (FreeModel n L) (adaptedBasis n L data hn h)
            (adaptedBasis n L data hn x)
        have hword : MarkedRow.basisWord n L data hn (x :: xs) =
            UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) *
              MarkedRow.basisWord n L data hn xs := by
          simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, adaptedWeightedBasis]
        have hvalue :
            MarkedRow.basisWord n L data hn left *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn h) *
                  MarkedRow.basisWord n L data hn (x :: xs) =
              (MarkedRow.basisWord n L data hn (left ++ [x]) *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn h) *
                  MarkedRow.basisWord n L data hn xs) +
                (MarkedRow.basisWord n L data hn left *
                  UniversalEnvelopingAlgebra.ι ℤ
                    ⁅adaptedBasis n L data hn h,
                      adaptedBasis n L data hn x⁆ *
                  MarkedRow.basisWord n L data hn xs) := by
          calc
            _ = MarkedRow.basisWord n L data hn left *
                  (UniversalEnvelopingAlgebra.ι ℤ
                      (adaptedBasis n L data hn h) *
                    UniversalEnvelopingAlgebra.ι ℤ
                      (adaptedBasis n L data hn x)) *
                  MarkedRow.basisWord n L data hn xs := by
                rw [hword]
                noncomm_ring
            _ = MarkedRow.basisWord n L data hn left *
                  (UniversalEnvelopingAlgebra.ι ℤ
                      (adaptedBasis n L data hn x) *
                    UniversalEnvelopingAlgebra.ι ℤ
                      (adaptedBasis n L data hn h) +
                    UniversalEnvelopingAlgebra.ι ℤ
                      ⁅adaptedBasis n L data hn h,
                        adaptedBasis n L data hn x⁆) *
                  MarkedRow.basisWord n L data hn xs := by rw [hswap]
            _ = _ := by
                simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
                  LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
                noncomm_ring
        rw [hvalue, map_add]
        have horderedFirst : ((left ++ [x]) ++ xs).Pairwise (· ≤ ·) := by
          simpa [List.append_assoc] using hordered
        have hleFirst : ∀ y ∈ left ++ [x], y ≤ h := by
          intro y hy
          simp only [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact hle y hy
          · exact hxh
        have hbracketTail :
            ⁅adaptedBasis n L data hn h,
                adaptedBasis n L data hn x⁆ ∈
              FreeMetabelian.Free.tail
                (X := Generator L) (c := n + 1) 1 := by
          rw [adaptedBasis_apply, adaptedBasis_apply,
            FreeMetabelian.Free.mem_tail_iff]
          intro i hi
          exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
            h.1.val x.1.val h.1.isLt x.1.isLt
              (pieceAdaptedBasis n L data hn h.1 h.2)
              (pieceAdaptedBasis n L data hn x.1 x.2) i (by omega)
        rw [ih (left ++ [x]) (by simp) horderedFirst hleFirst,
          pbwPrimitive_basisWord_mul_iota_mul_basisWord_eq_zero_of_mem_tail_one
            n L data hn left xs hleftXsOrdered hleft
              ⁅adaptedBasis n L data hn h,
                adaptedBasis n L data hn x⁆
              hbracketTail,
          add_zero]

/-- The right-normed comb obtained by repeatedly moving one derived factor
through an ordered list of ordinary factors. -/
def adaptedRightComb (d : FreeModel n L) :
    List (AdaptedIndex n L data hn) → FreeModel n L
  | [] => d
  | x :: xs => adaptedRightComb ⁅d, adaptedBasis n L data hn x⁆ xs

@[simp] theorem adaptedRightComb_neg
    (d : FreeModel n L)
    (xs : List (AdaptedIndex n L data hn)) :
    adaptedRightComb n L data hn (-d) xs =
      -adaptedRightComb n L data hn d xs := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih =>
      change adaptedRightComb n L data hn
          ⁅-d, adaptedBasis n L data hn x⁆ xs =
        -adaptedRightComb n L data hn
          ⁅d, adaptedBasis n L data hn x⁆ xs
      rw [neg_lie, ih]

theorem adaptedRightComb_zsmul
    (a : ℤ) (d : FreeModel n L)
    (xs : List (AdaptedIndex n L data hn)) :
    adaptedRightComb n L data hn (a • d) xs =
      a • adaptedRightComb n L data hn d xs := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih =>
      change adaptedRightComb n L data hn
          ⁅a • d, adaptedBasis n L data hn x⁆ xs =
        a • adaptedRightComb n L data hn
          ⁅d, adaptedBasis n L data hn x⁆ xs
      rw [smul_lie, ih]

/-- The two sign conventions for the unique insertion comb agree: starting
with `[x,h]` is the negative of starting with `h` and absorbing `x` first. -/
theorem adaptedRightComb_bracket_skew
    (x h : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn)) :
    adaptedRightComb n L data hn
        ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ xs =
      -adaptedRightComb n L data hn
        (adaptedBasis n L data hn h) (x :: xs) := by
  rw [adaptedRightComb]
  have hskew :
      ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ =
        -⁅adaptedBasis n L data hn h,
          adaptedBasis n L data hn x⁆ := by
    exact (lie_skew _ _).symm
  rw [hskew, adaptedRightComb_neg]

/-- A positive zero-based homogeneous adapted basis vector belongs to the
derived ideal of the free metabelian Lie ring. -/
theorem adaptedBasis_mem_derived_of_piece_pos
    (i : AdaptedIndex n L data hn) (hi : 0 < i.1.val) :
    adaptedBasis n L data hn i ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  have hweight := FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
    (generatorBasis L) i.1.val i.1.isLt
      (pieceAdaptedBasis n L data hn i.1 i.2)
  have hone : adaptedBasis n L data hn i ∈
      lowerCentralSeries ℤ (FreeModel n L) 1 := by
    rw [adaptedBasis_apply]
    exact LieModule.antitone_lowerCentralSeries ℤ
      (FreeModel n L) (FreeModel n L) (by omega) hweight
  simpa [LieAlgebra.derivedSeries_def,
    LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero,
    lowerCentralSeries, LieModule.lowerCentralSeries_succ,
    LieSubmodule.lie_comm] using hone

/-- The positive homogeneous tail of the free metabelian model lies in its
derived ideal.  This is the direct homogeneous-coordinate form of
`M = F_{≥2}` used in the manuscript. -/
theorem mem_derived_of_mem_tail_one
    (d : FreeModel n L)
    (hd : d ∈ FreeMetabelian.Free.tail
      (X := Generator L) (c := n + 1) 1) :
    d ∈ LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  have hone : d ∈ lowerCentralSeries ℤ (FreeModel n L) 1 := by
    rw [← FreeMetabelian.Free.sum_incl_project d]
    apply Submodule.sum_mem
    intro i hi
    by_cases hi0 : i.val < 1
    · rw [FreeMetabelian.Free.project_apply, hd i hi0, map_zero]
      exact Submodule.zero_mem _
    · exact LieModule.antitone_lowerCentralSeries ℤ
        (FreeModel n L) (FreeModel n L) (by omega)
          (FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
            (generatorBasis L) i.val i.isLt
            (FreeMetabelian.Free.project i d))
  simpa [LieAlgebra.derivedSeries_def,
    LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero,
    lowerCentralSeries, LieModule.lowerCentralSeries_succ,
    LieSubmodule.lie_comm] using hone

/-- Every bracket belongs to the derived ideal. -/
theorem lie_mem_derived (x y : FreeModel n L) :
    ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  have hone : ⁅x, y⁆ ∈ lowerCentralSeries ℤ (FreeModel n L) 1 := by
    rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp) (by simp)
  simpa [LieAlgebra.derivedSeries_def,
    LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero,
    lowerCentralSeries, LieModule.lowerCentralSeries_succ,
    LieSubmodule.lie_comm] using hone

/-- The derived ideal remains stable when a right-comb absorbs one adapted
basis input. -/
theorem derived_lie_adaptedBasis_mem_derived
    (d : FreeModel n L)
    (hd : d ∈ LieAlgebra.derivedSeries ℤ (FreeModel n L) 1)
    (i : AdaptedIndex n L data hn) :
    ⁅d, adaptedBasis n L data hn i⁆ ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  rw [← lie_skew]
  exact (LieAlgebra.derivedSeries ℤ (FreeModel n L) 1).neg_mem
    ((LieAlgebra.derivedSeries ℤ (FreeModel n L) 1).lie_mem hd)

@[simp] theorem adaptedRightComb_zero
    (xs : List (AdaptedIndex n L data hn)) :
    adaptedRightComb n L data hn 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [adaptedRightComb, zero_lie, ih]

/-- A right comb which already starts in the derived ideal vanishes as soon
as it absorbs another derived homogeneous input.  This is the precise
metabelian two-`M` clause used in the stopping-rule partition. -/
theorem adaptedRightComb_eq_zero_of_derived_of_exists_piece_pos
    (d : FreeModel n L)
    (hd : d ∈ LieAlgebra.derivedSeries ℤ (FreeModel n L) 1)
    (xs : List (AdaptedIndex n L data hn))
    (hpos : ∃ i ∈ xs, 0 < i.1.val) :
    adaptedRightComb n L data hn d xs = 0 := by
  induction xs generalizing d with
  | nil => simp at hpos
  | cons x xs ih =>
      by_cases hx : 0 < x.1.val
      · have hbracket : ⁅d, adaptedBasis n L data hn x⁆ = 0 :=
          IsMetabelian.bracket_eq_zero
            (FreeMetabelian.Free.isMetabelian
              (X := Generator L) (c := n + 1)) hd
            (adaptedBasis_mem_derived_of_piece_pos n L data hn x hx)
        rw [adaptedRightComb, hbracket]
        exact adaptedRightComb_zero n L data hn xs
      · have htail : ∃ i ∈ xs, 0 < i.1.val := by
          obtain ⟨i, hi, hipos⟩ := hpos
          simp only [List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact (hx hipos).elim
          · exact ⟨i, hi, hipos⟩
        rw [adaptedRightComb]
        exact ih ⁅d, adaptedBasis n L data hn x⁆
          (derived_lie_adaptedBasis_mem_derived n L data hn d hd x) htail

/-- Two positive homogeneous inputs make a metabelian right comb vanish,
regardless of whether the initial input was already derived.  Multiplicity
is literal list multiplicity. -/
theorem adaptedRightComb_eq_zero_of_countP_piece_pos
    (d : FreeModel n L)
    (xs : List (AdaptedIndex n L data hn))
    (hcount : 2 ≤ xs.countP fun i ↦ decide (0 < i.1.val)) :
    adaptedRightComb n L data hn d xs = 0 := by
  induction xs generalizing d with
  | nil => simp at hcount
  | cons x xs ih =>
      by_cases hx : 0 < x.1.val
      · have htailCount : 0 < xs.countP fun i ↦ decide (0 < i.1.val) := by
          have hxTrue : decide (0 < x.1.val) = true := by simp [hx]
          rw [List.countP_cons, hxTrue] at hcount
          simp only [ite_true] at hcount
          omega
        have htail : ∃ i ∈ xs, 0 < i.1.val := by
          by_contra hnone
          have hzero : xs.countP (fun i ↦ decide (0 < i.1.val)) = 0 :=
            List.countP_eq_zero.mpr (by
              intro i hi htrue
              exact hnone ⟨i, hi, of_decide_eq_true htrue⟩)
          omega
        rw [adaptedRightComb]
        exact adaptedRightComb_eq_zero_of_derived_of_exists_piece_pos
          n L data hn ⁅d, adaptedBasis n L data hn x⁆
            (lie_mem_derived n L d (adaptedBasis n L data hn x)) xs htail
      · have htailCount :
            2 ≤ xs.countP fun i ↦ decide (0 < i.1.val) := by
          have hxFalse : decide (0 < x.1.val) = false := by simp [hx]
          rw [List.countP_cons, hxFalse] at hcount
          simpa only [Bool.false_eq_true, ite_false, add_zero] using hcount
        rw [adaptedRightComb]
        exact ih ⁅d, adaptedBasis n L data hn x⁆ htailCount

/-- A derived factor placed before an ordered spectator word has exactly one
complete primitive: the iterated right comb. -/
theorem pbwPrimitive_iota_mul_basisWord_of_mem_tail_one
    (d : FreeModel n L)
    (hd : d ∈ FreeMetabelian.Free.tail
      (X := Generator L) (c := n + 1) 1)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·)) :
    pbwPrimitive n L data hn
        (UniversalEnvelopingAlgebra.ι ℤ d *
          MarkedRow.basisWord n L data hn xs) =
      adaptedRightComb n L data hn d xs := by
  induction xs generalizing d with
  | nil =>
      simpa [adaptedRightComb, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.word] using
        pbwPrimitive_iota n L data hn d
  | cons x xs ih =>
      have htailOrdered : xs.Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hordered).2
      have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
        (FreeModel n L) d (adaptedBasis n L data hn x)
      have hword : MarkedRow.basisWord n L data hn (x :: xs) =
          UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn x) *
            MarkedRow.basisWord n L data hn xs := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      rw [hword, ← mul_assoc, hswap, add_mul, map_add]
      have hsingle : MarkedRow.basisWord n L data hn [x] =
          UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn x) := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      rw [← hsingle]
      rw [pbwPrimitive_basisWord_mul_iota_mul_basisWord_eq_zero_of_mem_tail_one
        n L data hn [x] xs (by simpa using hordered) (by simp) d hd]
      rw [zero_add, ih ⁅d, adaptedBasis n L data hn x⁆
        (tail_one_lie_adaptedBasis n L data hn d hd x) htailOrdered]
      rfl

/-- In the adapted basis, the complete Lie primitive of an already ordered
word with a non-singleton factor list is zero. -/
theorem pbwPrimitive_basisWord_eq_zero_of_pairwise
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·)) (hlen : xs.length ≠ 1) :
    pbwPrimitive n L data hn
        (LieRings.PBW.basisWord ℤ (FreeModel n L)
          (AdaptedIndex n L data hn) (adaptedBasis n L data hn) xs) = 0 := by
  apply LieRings.PBW.canonicalMap_injective_of_freeModulePBW
    ℤ (FreeModel n L) (AdaptedIndex n L data hn)
    (adaptedWeightedBasis n L data hn).basis
    (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis)
  rw [← factorProj_one_eq_iota_pbwPrimitive n L data hn]
  simpa only [adaptedWeightedBasis, map_zero] using
    WeightedBasis.factorProj_one_basisWord_eq_zero_of_pairwise
      (adaptedWeightedBasis n L data hn) xs hordered hlen

/-! ## Moving one ordinary factor through an ordered word -/

/-- The bracket of two adapted homogeneous basis vectors has no weight-one
coordinate.  This is the only tail fact needed in the insertion calculation
below. -/
private theorem bracket_adaptedBasis_mem_tail_one
    (x h : AdaptedIndex n L data hn) :
    ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) 1 := by
  rw [adaptedBasis_apply, adaptedBasis_apply,
    FreeMetabelian.Free.mem_tail_iff]
  intro i hi
  exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
    x.1.val h.1.val x.1.isLt h.1.isLt
      (pieceAdaptedBasis n L data hn x.1 x.2)
      (pieceAdaptedBasis n L data hn h.1 h.2) i (by omega)

/-- Exact left-edge PBW insertion rule.  A basis input already weakly below
the first ordinary factor produces an ordered word and hence no primitive.
Otherwise the principal swapped word has a permanent spectator, and the
only primitive is the right-normed commutator correction. -/
theorem pbwPrimitive_iota_basis_mul_basisWord_cons
    (h x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : (x :: xs).Pairwise (· ≤ ·)) :
    pbwPrimitive n L data hn
        (UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn h) *
          MarkedRow.basisWord n L data hn (x :: xs)) =
      if h ≤ x then 0 else
        adaptedRightComb n L data hn
          ⁅adaptedBasis n L data hn h,
            adaptedBasis n L data hn x⁆ xs := by
  classical
  by_cases hhx : h ≤ x
  · rw [if_pos hhx]
    have hwhole : (h :: x :: xs).Pairwise (· ≤ ·) := by
      rw [List.pairwise_cons]
      refine ⟨?_, hordered⟩
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hhx
      · exact hhx.trans ((List.pairwise_cons.mp hordered).1 y hy)
    have hword :
        UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn h) *
            MarkedRow.basisWord n L data hn (x :: xs) =
          LieRings.PBW.basisWord ℤ (FreeModel n L)
            (AdaptedIndex n L data hn) (adaptedBasis n L data hn)
            (h :: x :: xs) := by
      simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word, adaptedWeightedBasis]
    rw [hword]
    exact pbwPrimitive_basisWord_eq_zero_of_pairwise
      n L data hn (h :: x :: xs) hwhole (by simp)
  · rw [if_neg hhx]
    have hxh : x ≤ h := le_of_not_ge hhx
    have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
      (FreeModel n L) (adaptedBasis n L data hn h)
        (adaptedBasis n L data hn x)
    have hword : MarkedRow.basisWord n L data hn (x :: xs) =
        UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn x) *
          MarkedRow.basisWord n L data hn xs := by
      simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word, adaptedWeightedBasis]
    rw [hword, ← mul_assoc, hswap, add_mul, map_add]
    have hprincipal :
        pbwPrimitive n L data hn
            (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) *
              UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn h) *
              MarkedRow.basisWord n L data hn xs) = 0 := by
      have hsingle : MarkedRow.basisWord n L data hn [x] =
          UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn x) := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      rw [← hsingle]
      exact pbwPrimitive_basisWord_mul_iota_basis_mul_basisWord_eq_zero
        n L data hn [x] xs h (by simp) (by simpa using hordered)
          (by simpa using hxh)
    rw [hprincipal, zero_add]
    exact pbwPrimitive_iota_mul_basisWord_of_mem_tail_one
      n L data hn
        ⁅adaptedBasis n L data hn h, adaptedBasis n L data hn x⁆
        (bracket_adaptedBasis_mem_tail_one n L data hn h x)
        xs (List.pairwise_cons.mp hordered).2

private theorem adaptedIndex_piece_mono
    {i j : AdaptedIndex n L data hn} (hij : i ≤ j) :
    i.1.val ≤ j.1.val := by
  change toLex (i.1.val, i.2.val) ≤ toLex (j.1.val, j.2.val) at hij
  simpa using Prod.Lex.monotone_fst _ _ hij

/-- If a weight-one adapted basis input is placed at the left of an ordered
word containing two ordinary `M`-inputs, its complete PBW primitive is zero.
The proof is the literal left-to-right insertion calculation: only
weight-one factors can be crossed; the first correction is derived and is
killed on meeting an `M`-input, while every later correction retains a
spectator. -/
theorem pbwPrimitive_iota_weightOneBasis_mul_basisWord_eq_zero_of_twoM
    (h : AdaptedIndex n L data hn) (hh : h.1.val = 0)
    (right : List (AdaptedIndex n L data hn))
    (hordered : right.Pairwise (· ≤ ·))
    (hcount : 2 ≤ right.countP fun i ↦ decide (0 < i.1.val)) :
    pbwPrimitive n L data hn
        (UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn h) *
          MarkedRow.basisWord n L data hn right) = 0 := by
  classical
  suffices hgeneral : ∀
      (left right : List (AdaptedIndex n L data hn)),
      (left ++ right).Pairwise (· ≤ ·) →
      (∀ x ∈ left, x ≤ h) →
      2 ≤ right.countP (fun i ↦ decide (0 < i.1.val)) →
      pbwPrimitive n L data hn
          (MarkedRow.basisWord n L data hn left *
            UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn h) *
            MarkedRow.basisWord n L data hn right) = 0 by
    simpa [MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word] using
      hgeneral [] right (by simpa using hordered) (by simp) hcount
  intro left right
  induction right generalizing left with
  | nil =>
      intro hpair hleft hcount
      simp at hcount
  | cons x xs ih =>
      intro hpair hleft hcount
      have htailOrdered : xs.Pairwise (· ≤ ·) :=
        (List.pairwise_append.mp hpair).2.1 |> List.pairwise_cons.mp |>.2
      have hxTail : ∀ y ∈ xs, x ≤ y :=
        (List.pairwise_cons.mp (List.pairwise_append.mp hpair).2.1).1
      by_cases hhx : h ≤ x
      · have hwhole : (left ++ h :: x :: xs).Pairwise (· ≤ ·) := by
          apply List.pairwise_append.mpr
          refine ⟨(List.pairwise_append.mp hpair).1,
            List.pairwise_cons.mpr ⟨?_,
              (List.pairwise_append.mp hpair).2.1⟩, ?_⟩
          · intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact hhx
            · exact hhx.trans (hxTail y hy)
          · intro y hy z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact hleft y hy
            · exact (List.pairwise_append.mp hpair).2.2 y hy z
                (by simp [hz])
        have hword :
            MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn h) *
                MarkedRow.basisWord n L data hn (x :: xs) =
              MarkedRow.basisWord n L data hn (left ++ h :: x :: xs) := by
          simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
          noncomm_ring
        rw [hword]
        exact pbwPrimitive_basisWord_eq_zero_of_pairwise
          n L data hn _ hwhole (by
            simp only [List.length_append, List.length_cons]
            omega)
      · have hxh : x ≤ h := le_of_not_ge hhx
        have hx0 : x.1.val = 0 := by
          have hxle := adaptedIndex_piece_mono n L data hn hxh
          omega
        have hxFalse : decide (0 < x.1.val) = false := by simp [hx0]
        have htailCount :
            2 ≤ xs.countP fun i ↦ decide (0 < i.1.val) := by
          rw [List.countP_cons, hxFalse] at hcount
          simpa using hcount
        have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
          (FreeModel n L) (adaptedBasis n L data hn h)
            (adaptedBasis n L data hn x)
        have hrightWord : MarkedRow.basisWord n L data hn (x :: xs) =
            UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) *
              MarkedRow.basisWord n L data hn xs := by
          simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, adaptedWeightedBasis]
        have hprincipalWord :
            MarkedRow.basisWord n L data hn (left ++ [x]) =
              MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn x) := by
          simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
        rw [hrightWord]
        have hsplit :
            MarkedRow.basisWord n L data hn left *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn h) *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn x) *
                  MarkedRow.basisWord n L data hn xs =
              (MarkedRow.basisWord n L data hn left *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn x) *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn h) *
                  MarkedRow.basisWord n L data hn xs) +
                (MarkedRow.basisWord n L data hn left *
                  UniversalEnvelopingAlgebra.ι ℤ
                    ⁅adaptedBasis n L data hn h,
                      adaptedBasis n L data hn x⁆ *
                  MarkedRow.basisWord n L data hn xs) := by
          calc
            _ = MarkedRow.basisWord n L data hn left *
                  (UniversalEnvelopingAlgebra.ι ℤ
                      (adaptedBasis n L data hn h) *
                    UniversalEnvelopingAlgebra.ι ℤ
                      (adaptedBasis n L data hn x)) *
                  MarkedRow.basisWord n L data hn xs := by noncomm_ring
            _ = MarkedRow.basisWord n L data hn left *
                  (UniversalEnvelopingAlgebra.ι ℤ
                      (adaptedBasis n L data hn x) *
                    UniversalEnvelopingAlgebra.ι ℤ
                      (adaptedBasis n L data hn h) +
                    UniversalEnvelopingAlgebra.ι ℤ
                      ⁅adaptedBasis n L data hn h,
                        adaptedBasis n L data hn x⁆) *
                  MarkedRow.basisWord n L data hn xs := by rw [hswap]
            _ = _ := by noncomm_ring
        rw [show MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn h) *
                (UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn x) *
                  MarkedRow.basisWord n L data hn xs) =
              MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn h) *
                UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn x) *
                MarkedRow.basisWord n L data hn xs by noncomm_ring,
          hsplit, map_add]
        have hprincipal := ih (left ++ [x])
          (by simpa [List.append_assoc] using hpair)
          (by
            intro y hy
            simp only [List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact hleft y hy
            · exact hxh)
          htailCount
        rw [← hprincipalWord, hprincipal, zero_add]
        by_cases hleftNil : left = []
        · subst left
          have htailPos : ∃ i ∈ xs, 0 < i.1.val := by
            by_contra hnone
            have hzero : xs.countP
                (fun i ↦ decide (0 < i.1.val)) = 0 :=
              List.countP_eq_zero.mpr (by
                intro i hi htrue
                exact hnone ⟨i, hi, of_decide_eq_true htrue⟩)
            omega
          have hempty : MarkedRow.basisWord n L data hn [] = 1 := by
            simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word]
          rw [hempty, one_mul]
          rw [pbwPrimitive_iota_mul_basisWord_of_mem_tail_one
            n L data hn
              ⁅adaptedBasis n L data hn h, adaptedBasis n L data hn x⁆
              (bracket_adaptedBasis_mem_tail_one n L data hn h x)
              xs htailOrdered]
          exact adaptedRightComb_eq_zero_of_derived_of_exists_piece_pos
            n L data hn _
              (lie_mem_derived n L
                (adaptedBasis n L data hn h)
                (adaptedBasis n L data hn x)) xs htailPos
        · have hwithout : (left ++ xs).Pairwise (· ≤ ·) := by
            apply List.Pairwise.sublist
            exact List.Sublist.append (List.Sublist.refl left)
              (List.tail_sublist (x :: xs))
            exact hpair
          exact pbwPrimitive_basisWord_mul_iota_mul_basisWord_eq_zero_of_mem_tail_one
            n L data hn left xs hwithout hleftNil
              ⁅adaptedBasis n L data hn h, adaptedBasis n L data hn x⁆
              (bracket_adaptedBasis_mem_tail_one n L data hn h x)

/-- Grouped version of the preceding insertion calculation for an arbitrary
homogeneous weight-one input.  The basis expansion is summed before the
result is used by the occurrence ledger. -/
theorem pbwPrimitive_iota_weightIncl_zero_mul_basisWord_eq_zero_of_twoM
    (v : FreeMetabelian.Piece (Generator L) 0)
    (right : List (AdaptedIndex n L data hn))
    (hordered : right.Pairwise (· ≤ ·))
    (hcount : 2 ≤ right.countP fun i ↦ decide (0 < i.1.val)) :
    pbwPrimitive n L data hn
        (UniversalEnvelopingAlgebra.ι ℤ
            (FreeMetabelian.Free.weightIncl 0 (by omega) v) *
          MarkedRow.basisWord n L data hn right) = 0 := by
  classical
  let b := pieceAdaptedBasis n L data hn
    (⟨0, by omega⟩ : Fin (n + 1))
  rw [← b.sum_repr v, map_sum, map_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [map_zsmul, smul_mul_assoc, map_zsmul]
  have hbasis :
      FreeMetabelian.Free.weightIncl 0 (by omega) (b i) =
        adaptedBasis n L data hn
          (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
            AdaptedIndex n L data hn) := by
    rw [adaptedBasis_apply]
    rfl
  rw [hbasis,
    pbwPrimitive_iota_weightOneBasis_mul_basisWord_eq_zero_of_twoM
      n L data hn _ rfl right hordered hcount,
    smul_zero]

/-- The literal correction produced while moving one appended ordinary
factor left through a displayed word.  Its first summand is the transfer
bracket at the current position and its second summand retains the current
ordinary spectator, exactly as in the manuscript's subset collection. -/
def rightInsertionCorrection
    (h : AdaptedIndex n L data hn) :
    List (AdaptedIndex n L data hn) → UEA ℤ (FreeModel n L)
  | [] => 0
  | x :: xs =>
      UniversalEnvelopingAlgebra.ι ℤ
          ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ *
        MarkedRow.basisWord n L data hn xs +
      UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn x) *
        rightInsertionCorrection h xs

/-- Exact integral insertion identity.  No ordering assumption is involved:
it is just repeated use of `iota(x) iota(h) = iota(h) iota(x) +
iota([x,h])`. -/
theorem basisWord_mul_iota_eq_iota_mul_basisWord_add_rightInsertionCorrection
    (h : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn)) :
    MarkedRow.basisWord n L data hn xs *
        UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn h) =
      UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn h) *
          MarkedRow.basisWord n L data hn xs +
        rightInsertionCorrection n L data hn h xs := by
  induction xs with
  | nil =>
      simp [rightInsertionCorrection, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.word]
  | cons x xs ih =>
      have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
        (FreeModel n L) (adaptedBasis n L data hn x)
          (adaptedBasis n L data hn h)
      have hword : MarkedRow.basisWord n L data hn (x :: xs) =
          UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn x) *
            MarkedRow.basisWord n L data hn xs := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      rw [hword, mul_assoc, ih, mul_add, ← mul_assoc, hswap]
      simp only [rightInsertionCorrection]
      noncomm_ring

/-- Every insertion correction with a nonempty ordered prefix is invisible
to the complete one-factor projection.  This is the formal spectator clause
in the manuscript's primitive classification. -/
theorem pbwPrimitive_basisWord_mul_rightInsertionCorrection_eq_zero
    (left right : List (AdaptedIndex n L data hn))
    (hordered : (left ++ right).Pairwise (· ≤ ·))
    (hleft : left ≠ [])
    (h : AdaptedIndex n L data hn) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn left *
          rightInsertionCorrection n L data hn h right) = 0 := by
  induction right generalizing left with
  | nil =>
      simp [rightInsertionCorrection]
  | cons x xs ih =>
      have horderedFirst : (left ++ xs).Pairwise (· ≤ ·) := by
        apply List.Pairwise.sublist
        exact List.Sublist.append (List.Sublist.refl left)
          (List.tail_sublist (x :: xs))
        exact hordered
      have horderedSecond : ((left ++ [x]) ++ xs).Pairwise (· ≤ ·) := by
        simpa [List.append_assoc] using hordered
      rw [rightInsertionCorrection, mul_add, map_add]
      have hfirst :=
        pbwPrimitive_basisWord_mul_iota_mul_basisWord_eq_zero_of_mem_tail_one
          n L data hn left xs horderedFirst hleft
            ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆
            (bracket_adaptedBasis_mem_tail_one n L data hn x h)
      have hword : MarkedRow.basisWord n L data hn (left ++ [x]) =
          MarkedRow.basisWord n L data hn left *
            UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn x) := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
      have hfirst' : pbwPrimitive n L data hn
          (MarkedRow.basisWord n L data hn left *
            (UniversalEnvelopingAlgebra.ι ℤ
                ⁅adaptedBasis n L data hn x,
                  adaptedBasis n L data hn h⁆ *
              MarkedRow.basisWord n L data hn xs)) = 0 := by
        simpa only [mul_assoc] using hfirst
      rw [hfirst', zero_add]
      have hsecond :
          MarkedRow.basisWord n L data hn left *
              (UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn x) *
                rightInsertionCorrection n L data hn h xs) =
            MarkedRow.basisWord n L data hn (left ++ [x]) *
              rightInsertionCorrection n L data hn h xs := by
        rw [← mul_assoc, ← hword]
      rw [hsecond]
      exact ih (left ++ [x]) horderedSecond (by simp)

/-- With no spectator prefix, the complete primitive of the insertion
correction is the unique comb beginning with the first transfer bracket. -/
theorem pbwPrimitive_rightInsertionCorrection_cons
    (h x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : (x :: xs).Pairwise (· ≤ ·)) :
    pbwPrimitive n L data hn
        (rightInsertionCorrection n L data hn h (x :: xs)) =
      adaptedRightComb n L data hn
        ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ xs := by
  rw [rightInsertionCorrection, map_add]
  have htail : xs.Pairwise (· ≤ ·) :=
    (List.pairwise_cons.mp hordered).2
  rw [pbwPrimitive_iota_mul_basisWord_of_mem_tail_one
    n L data hn
      ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆
      (bracket_adaptedBasis_mem_tail_one n L data hn x h) xs htail]
  have hsingle : MarkedRow.basisWord n L data hn [x] =
      UniversalEnvelopingAlgebra.ι ℤ
        (adaptedBasis n L data hn x) := by
    simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, adaptedWeightedBasis]
  rw [← hsingle,
    pbwPrimitive_basisWord_mul_rightInsertionCorrection_eq_zero
      n L data hn [x] xs (by simpa using hordered) (by simp) h,
    add_zero]

/-- If the appended factor belongs at the very beginning of a nonempty
ordered word, the sole primitive is the manuscript's iterated comb. -/
theorem pbwPrimitive_basisWord_mul_iota_of_le_all
    (h x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : (x :: xs).Pairwise (· ≤ ·))
    (hh : ∀ y ∈ x :: xs, h ≤ y) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn (x :: xs) *
          UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn h)) =
      adaptedRightComb n L data hn
        ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ xs := by
  rw [basisWord_mul_iota_eq_iota_mul_basisWord_add_rightInsertionCorrection,
    map_add]
  have horderedHead : (h :: x :: xs).Pairwise (· ≤ ·) := by
    rw [List.pairwise_cons]
    exact ⟨hh, hordered⟩
  have hheadWord :
      UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn h) *
          MarkedRow.basisWord n L data hn (x :: xs) =
        LieRings.PBW.basisWord ℤ (FreeModel n L)
          (AdaptedIndex n L data hn) (adaptedBasis n L data hn)
          (h :: x :: xs) := by
    simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, adaptedWeightedBasis]
  rw [hheadWord,
    pbwPrimitive_basisWord_eq_zero_of_pairwise n L data hn
      (h :: x :: xs) horderedHead (by simp), zero_add]
  exact pbwPrimitive_rightInsertionCorrection_cons
    n L data hn h x xs hordered

/-- If the appended factor inserts after a nonempty ordered prefix, no
complete primitive survives.  The principal inserted word is ordered and
every transfer correction retains that prefix as a spectator. -/
theorem pbwPrimitive_basisWord_mul_iota_eq_zero_of_ordered_insertion
    (left right : List (AdaptedIndex n L data hn))
    (h : AdaptedIndex n L data hn)
    (hleft : left ≠ [])
    (hordered : (left ++ [h] ++ right).Pairwise (· ≤ ·)) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn (left ++ right) *
          UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn h)) = 0 := by
  have hrightOrdered : right.Pairwise (· ≤ ·) := by
    have hp : (left ++ ([h] ++ right)).Pairwise (· ≤ ·) := by
      simpa [List.append_assoc] using hordered
    exact (List.pairwise_cons.mp
      (List.pairwise_append.mp hp).2.1).2
  have hwithout : (left ++ right).Pairwise (· ≤ ·) := by
    have hp : (left ++ ([h] ++ right)).Pairwise (· ≤ ·) := by
      simpa [List.append_assoc] using hordered
    rw [List.pairwise_append] at hp ⊢
    refine ⟨hp.1, hrightOrdered, ?_⟩
    intro a ha b hb
    exact hp.2.2 a ha b (by simp [hb])
  have hwordSplit : MarkedRow.basisWord n L data hn (left ++ right) =
      MarkedRow.basisWord n L data hn left *
        MarkedRow.basisWord n L data hn right := by
    simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
  rw [hwordSplit, mul_assoc,
    basisWord_mul_iota_eq_iota_mul_basisWord_add_rightInsertionCorrection,
    mul_add, map_add]
  have hinsertedWord :
      MarkedRow.basisWord n L data hn left *
          (UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn h) *
            MarkedRow.basisWord n L data hn right) =
        LieRings.PBW.basisWord ℤ (FreeModel n L)
          (AdaptedIndex n L data hn) (adaptedBasis n L data hn)
          (left ++ [h] ++ right) := by
    simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
  rw [hinsertedWord,
    pbwPrimitive_basisWord_eq_zero_of_pairwise n L data hn
      (left ++ [h] ++ right) hordered (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        have hpos : 0 < left.length := Nat.pos_of_ne_zero (by
          intro hz
          exact hleft (List.eq_nil_of_length_eq_zero hz))
        omega),
    pbwPrimitive_basisWord_mul_rightInsertionCorrection_eq_zero
      n L data hn left right hwithout hleft h,
    add_zero]

/-! ## Grouped weight-one head expansion -/

/-- In a linearly ordered word, an extra index either belongs weakly before
the whole word or has an ordered insertion point after a nonempty prefix.
This is used only to apply the two primitive formulas above; no persistent
normal-form data are introduced. -/
private theorem ordered_head_or_nonempty_insertion
    (h : AdaptedIndex n L data hn)
    (ys : List (AdaptedIndex n L data hn))
    (hordered : ys.Pairwise (· ≤ ·)) :
    (∀ y ∈ ys, h ≤ y) ∨
      ∃ left right,
        left ≠ [] ∧ ys = left ++ right ∧
          (left ++ [h] ++ right).Pairwise (· ≤ ·) := by
  induction ys with
  | nil =>
      left
      simp
  | cons x xs ih =>
      have htail : xs.Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hordered).2
      have hxall : ∀ y ∈ xs, x ≤ y :=
        (List.pairwise_cons.mp hordered).1
      by_cases hhx : h ≤ x
      · left
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hhx
        · exact hhx.trans (hxall y hy)
      · have hxh : x ≤ h := le_of_not_ge hhx
        rcases ih htail with hbefore | ⟨left, right, hleft, hxs, hins⟩
        · right
          refine ⟨[x], xs, by simp, rfl, ?_⟩
          change (x :: h :: xs).Pairwise (· ≤ ·)
          rw [List.pairwise_cons]
          refine ⟨?_, ?_⟩
          · intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact hxh
            · exact hxall y hy
          · rw [List.pairwise_cons]
            exact ⟨hbefore, htail⟩
        · right
          refine ⟨x :: left, right, by simp, ?_, ?_⟩
          · simp only [List.cons_append, hxs]
          · simp only [List.cons_append]
            rw [List.pairwise_cons]
            refine ⟨?_, hins⟩
            intro y hy
            simp only [List.mem_append, List.mem_singleton] at hy
            rcases hy with (hy | rfl) | hy
            · exact hxall y (by
                rw [hxs]
                exact List.mem_append_left right hy)
            · exact hxh
            · exact hxall y (by
                rw [hxs]
                exact List.mem_append_right left hy)

/-- Pointwise form of the ordered insertion dichotomy.  It is deliberately
an `if`: summing it over the coordinates of a homogeneous Smith head keeps
the expansion grouped and reads each Smith coefficient exactly once. -/
theorem pbwPrimitive_basisWord_mul_iota_basis_eq_if
    (x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : (x :: xs).Pairwise (· ≤ ·))
    (h : AdaptedIndex n L data hn) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn (x :: xs) *
          UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn h)) =
      if ∀ y ∈ x :: xs, h ≤ y then
        adaptedRightComb n L data hn
          ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ xs
      else 0 := by
  classical
  by_cases hhead : ∀ y ∈ x :: xs, h ≤ y
  · rw [if_pos hhead]
    exact pbwPrimitive_basisWord_mul_iota_of_le_all
      n L data hn h x xs hordered hhead
  · rw [if_neg hhead]
    rcases ordered_head_or_nonempty_insertion
        n L data hn h (x :: xs) hordered with hbefore |
      ⟨left, right, hleft, hsplit, hinsertion⟩
    · exact (hhead hbefore).elim
    · rw [hsplit]
      exact pbwPrimitive_basisWord_mul_iota_eq_zero_of_ordered_insertion
        n L data hn left right h hleft hinsertion

/-- The coordinate contribution of one adapted weight-one basis vector to
the primitive of an ordered word followed by a homogeneous head. -/
def weightOneRightInsertionSeed
    (x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn))
    (i : Fin (PieceRank n L data hn
      (⟨0, by omega⟩ : Fin (n + 1)))) : FreeModel n L :=
  let h : AdaptedIndex n L data hn :=
    ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩
  if ∀ y ∈ x :: xs, h ≤ y then
    adaptedRightComb n L data hn
      ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ xs
  else 0

/-- The arbitrary homogeneous weight-one Smith head, expanded once in the
adapted `pSmith` basis and immediately regrouped after the complete primitive
read.  This linear map is the practical interface used by the exceptional
triangular row. -/
def weightOneRightInsertionPrimitive
    (x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn)) :
    FreeMetabelian.Piece (Generator L) 0 →ₗ[ℤ] FreeModel n L :=
  (Finsupp.linearCombination ℤ
    (weightOneRightInsertionSeed n L data hn x xs)).comp
      (pieceAdaptedBasis n L data hn
        (⟨0, by omega⟩ : Fin (n + 1))).repr.toLinearMap

/-- Grouped insertion identity for an arbitrary homogeneous weight-one
element.  The proof is linear-map extensionality on the adapted Smith basis;
there is no coordinatewise choice in the resulting theorem. -/
theorem pbwPrimitive_basisWord_mul_iota_weightOne
    (x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : (x :: xs).Pairwise (· ≤ ·))
    (v : FreeMetabelian.Piece (Generator L) 0) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn (x :: xs) *
          UniversalEnvelopingAlgebra.ι ℤ
            (FreeMetabelian.Free.weightIncl 0 (by omega) v)) =
      weightOneRightInsertionPrimitive n L data hn x xs v := by
  classical
  let b := pieceAdaptedBasis n L data hn
    (⟨0, by omega⟩ : Fin (n + 1))
  rw [← b.sum_repr v, map_sum, map_sum, Finset.mul_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_zsmul, mul_smul_comm]
  apply congrArg (fun z : FreeModel n L ↦
    ((b.repr v) i) • z)
  have hbasis : FreeMetabelian.Free.weightIncl 0 (by omega) (b i) =
      adaptedBasis n L data hn
        (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
          AdaptedIndex n L data hn) := by
    rw [adaptedBasis_apply]
    rfl
  rw [hbasis,
    pbwPrimitive_basisWord_mul_iota_basis_eq_if
      n L data hn x xs hordered]
  change _ = (Finsupp.linearCombination ℤ
      (weightOneRightInsertionSeed n L data hn x xs))
        ((pieceAdaptedBasis n L data hn
          (⟨0, by omega⟩ : Fin (n + 1))).repr (b i))
  rw [show b = pieceAdaptedBasis n L data hn
      (⟨0, by omega⟩ : Fin (n + 1)) by rfl,
    Module.Basis.repr_self, Finsupp.linearCombination_single, one_smul]
  rfl

/-- Exact specialization to the zero-based-weight-zero triangular Smith
head.  This is the grouped head term in the manuscript's exceptional row;
the Smith diagonal remains inside the single homogeneous argument. -/
theorem pbwPrimitive_basisWord_mul_iota_triangularSmithHead_zero
    (x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : (x :: xs).Pairwise (· ≤ ·))
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) 0) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn (x :: xs) *
          UniversalEnvelopingAlgebra.ι ℤ
            (FreeMetabelian.Free.weightIncl 0 (by omega)
              (((triangularSmith n L data 0 (by omega)).diagonal i : ℤ) •
                triangularPieceBasis n L data 0 (by omega) i))) =
      weightOneRightInsertionPrimitive n L data hn x xs
        (((triangularSmith n L data 0 (by omega)).diagonal i : ℤ) •
          triangularPieceBasis n L data 0 (by omega) i) := by
  exact pbwPrimitive_basisWord_mul_iota_weightOne
    n L data hn x xs hordered _

end MetabelianVanishing

end

end LieRings
