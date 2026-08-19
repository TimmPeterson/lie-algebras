import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmithPrimitive
import LieRings.PBW.FactorSymbol

/-!
# The factor-two Stokes read of the terminal Smith collector

The terminal Smith collector preserves the exact enveloping-algebra value of
each marked row.  This file records the corresponding exact degree-two PBW
read.  The sole input invariant is the one present in the manuscript: after
removing the marked relation, the ordinary Smith indices are already ordered.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalSmithStokesFintype : Fintype L := Fintype.ofFinite L

namespace TerminalSmithRow

/-- Complete Smith index word, with the distinguished relation index inserted
at its literal placement. -/
def smithWord (r : TerminalSmithRow n L data hn) :
    List (TerminalSmithIndex n L data hn) :=
  r.left ++ r.mark :: r.right

/-- A marked Smith row is its ambient basis word, multiplied by the positive
Smith diagonal attached to the marked relation basis vector. -/
theorem value_eq_diagonal_smul_basisWord
    (r : TerminalSmithRow n L data hn) :
    r.value n L data hn =
      ((terminalSmith n L data hn).diagonal r.mark : ℤ) •
        LieRings.PBW.basisWord ℤ (A L n) _
          (terminalSmith n L data hn).ambientBasis
          (r.smithWord n L data hn) := by
  unfold TerminalSmithRow.value
  rw [(terminalSmith n L data hn).relation_eq r.mark]
  rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
  congr 1
  simp [TerminalSmithRow.ambientWord,
    TerminalSmithRow.smithWord, LieRings.PBW.basisWord,
    LieRings.PBW.word, List.map_append, mul_assoc]

end TerminalSmithRow

/-! ## The ordered-neighbor invariant -/

theorem terminalMoveLeftExpansion_neighbors_pairwise
    (i : TerminalSmithIndex n L data hn)
    (front : List (TerminalSmithIndex n L data hn))
    (x : TerminalSmithIndex n L data hn)
    (right : List (TerminalSmithIndex n L data hn))
    (hordered : ((front ++ [x]) ++ right).Pairwise (· ≤ ·)) :
    ∀ q ∈ terminalMoveLeftExpansion n L data hn i front x right,
      (q.2.left ++ q.2.right).Pairwise (· ≤ ·) := by
  classical
  intro q hq
  simp only [terminalMoveLeftExpansion, List.mem_cons, List.mem_map] at hq
  rcases hq with rfl | ⟨p, hp, rfl⟩
  · simpa [List.append_assoc] using hordered
  · unfold terminalTaggedList at hp
    rw [List.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    have hsub : List.Sublist (front ++ right) ((front ++ [x]) ++ right) := by
      rw [List.append_assoc]
      exact List.Sublist.append (List.Sublist.refl front)
        (List.sublist_cons_of_sublist x (List.Sublist.refl right))
    simpa only [Prod.snd] using hordered.sublist hsub

theorem terminalMoveRightExpansion_neighbors_pairwise
    (i : TerminalSmithIndex n L data hn)
    (left : List (TerminalSmithIndex n L data hn))
    (x : TerminalSmithIndex n L data hn)
    (tail : List (TerminalSmithIndex n L data hn))
    (hordered : (left ++ x :: tail).Pairwise (· ≤ ·)) :
    ∀ q ∈ terminalMoveRightExpansion n L data hn i left x tail,
      (q.2.left ++ q.2.right).Pairwise (· ≤ ·) := by
  classical
  intro q hq
  simp only [terminalMoveRightExpansion, List.mem_cons] at hq
  rcases hq with rfl | hp
  · simpa [List.append_assoc] using hordered
  · unfold terminalTaggedList at hp
    rw [List.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    have hsub : List.Sublist (left ++ tail) (left ++ x :: tail) := by
      exact List.Sublist.append (List.Sublist.refl left)
        (List.sublist_cons_of_sublist x (List.Sublist.refl tail))
    simpa only [Prod.snd] using hordered.sublist hsub

theorem terminalSmithExpansion_neighbors_pairwise
    {r : TerminalSmithRow n L data hn}
    {rows : List (ℤ × TerminalSmithRow n L data hn)}
    (hexp : terminalSmithExpansion n L data hn r = some rows)
    (hr : (r.left ++ r.right).Pairwise (· ≤ ·)) :
    ∀ q ∈ rows, (q.2.left ++ q.2.right).Pairwise (· ≤ ·) := by
  classical
  rcases r with ⟨i, left, right⟩
  by_cases hsmall :
      TerminalSmithRow.factorCount n L data hn ⟨i, left, right⟩ ≤ 2
  · simp [terminalSmithExpansion, hsmall] at hexp
  cases hs : terminalSplitLast? left with
  | none =>
      cases right with
      | nil => simp [terminalSmithExpansion, hsmall, hs] at hexp
      | cons y tail =>
          by_cases hy : y < i
          · simp [terminalSmithExpansion, hsmall, hs, hy] at hexp
            subst rows
            exact terminalMoveRightExpansion_neighbors_pairwise
              n L data hn i left y tail hr
          · simp [terminalSmithExpansion, hsmall, hs, hy] at hexp
  | some p =>
      rcases p with ⟨front, x⟩
      have hleft : left = front ++ [x] := terminalSplitLast?_eq_some hs
      by_cases hx : i < x
      · simp [terminalSmithExpansion, hsmall, hs, hx] at hexp
        subst rows
        subst left
        exact terminalMoveLeftExpansion_neighbors_pairwise
          n L data hn i front x right hr
      · cases right with
        | nil => simp [terminalSmithExpansion, hsmall, hs, hx] at hexp
        | cons y tail =>
            by_cases hy : y < i
            · simp [terminalSmithExpansion, hsmall, hs, hx, hy] at hexp
              subst rows
              exact terminalMoveRightExpansion_neighbors_pairwise
                n L data hn i left y tail hr
            · simp [terminalSmithExpansion, hsmall, hs, hx, hy] at hexp

/-- A terminal row above factor two is completely ordered once its ordinary
neighbors are ordered.  Factor-two rows are intentionally exempt: their two
oriented placements are retained by the collector. -/
theorem terminalSmith_terminal_smithWord_pairwise_of_two_lt
    (r : TerminalSmithRow n L data hn)
    (hr : (r.left ++ r.right).Pairwise (· ≤ ·))
    (hcount : 2 < r.factorCount n L data hn)
    (hterminal : terminalSmithExpansion n L data hn r = none) :
    (r.smithWord n L data hn).Pairwise (· ≤ ·) := by
  classical
  have hparts := List.pairwise_append.mp hr
  have hleftBound : ∀ x ∈ r.left, x ≤ r.mark := by
    intro x hx
    cases hrev : r.left.reverse with
    | nil =>
        have hnil : r.left = [] := by
          have h := congrArg List.reverse hrev
          simpa using h
        simp [hnil] at hx
    | cons last frontRev =>
        have hleft : r.left = frontRev.reverse ++ [last] := by
          have h := congrArg List.reverse hrev
          simpa using h
        have hlast : last ≤ r.mark := by
          by_contra hnot
          have hbad : r.mark < last := lt_of_not_ge hnot
          have hnsmall : ¬r.factorCount n L data hn ≤ 2 := by omega
          have hsplit : terminalSplitLast? r.left =
              some (frontRev.reverse, last) := by
            simp [terminalSplitLast?, hleft]
          unfold terminalSmithExpansion at hterminal
          simp [hnsmall, hsplit, hbad] at hterminal
        by_cases hxl : x = last
        · simpa [hxl]
        · have hxfront : x ∈ frontRev.reverse := by
            simpa [hleft, hxl] using hx
          have hpLeft := hparts.1
          rw [hleft] at hpLeft
          have hcross := (List.pairwise_append.mp hpLeft).2.2
          exact (hcross x hxfront last (by simp)).trans hlast
  have hrightBound : ∀ y ∈ r.right, r.mark ≤ y := by
    intro y hy
    cases hright : r.right with
    | nil => simp [hright] at hy
    | cons first tail =>
        have hfirst : r.mark ≤ first := by
          by_contra hnot
          have hbad : first < r.mark := lt_of_not_ge hnot
          have hnsmall : ¬r.factorCount n L data hn ≤ 2 := by omega
          cases hrev : r.left.reverse with
          | nil =>
              have hleftNil : r.left = [] := by
                have h := congrArg List.reverse hrev
                simpa using h
              unfold terminalSmithExpansion at hterminal
              simp [hnsmall, hleftNil, hright, hbad,
                terminalSplitLast?] at hterminal
          | cons last frontRev =>
              have hleft : r.left = frontRev.reverse ++ [last] := by
                have h := congrArg List.reverse hrev
                simpa using h
              have hsplit : terminalSplitLast? r.left =
                  some (frontRev.reverse, last) := by
                simp [terminalSplitLast?, hleft]
              unfold terminalSmithExpansion at hterminal
              by_cases hleftBad : r.mark < last
              · simp [hnsmall, hsplit, hleftBad] at hterminal
              · simp [hnsmall, hsplit, hleftBad, hright, hbad] at hterminal
        by_cases hyf : y = first
        · simpa [hyf]
        · have hytail : y ∈ tail := by simpa [hright, hyf] using hy
          have hpRight := hparts.2.1
          rw [hright] at hpRight
          exact hfirst.trans ((List.pairwise_cons.mp hpRight).1 y hytail)
  unfold TerminalSmithRow.smithWord
  apply List.pairwise_append.mpr
  refine ⟨hparts.1, List.pairwise_cons.mpr ⟨hrightBound, hparts.2.1⟩, ?_⟩
  intro x hx y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hleftBound x hx
  · exact hparts.2.2 x hx y hy

/-- Ordered ordinary neighbors remain ordered throughout the deterministic
Smith collection. -/
theorem terminalSmith_normalForm_neighbors_pairwise
    (r : TerminalSmithRow n L data hn)
    (hr : (r.left ++ r.right).Pairwise (· ≤ ·))
    (q : TerminalSmithRow n L data hn)
    (hq : (terminalSmithCollector n L data hn).normalForm r q ≠ 0) :
    (q.left ++ q.right).Pairwise (· ≤ ·) := by
  exact (terminalSmithCollector n L data hn).invariant_of_normalForm_apply_ne_zero
    (fun s ↦ (s.left ++ s.right).Pairwise (· ≤ ·))
    (fun hexp hs ↦ terminalSmithExpansion_neighbors_pairwise
      n L data hn hexp hs) hr hq

/-- Every non-factor-two terminal Smith leaf is silent under the exact
degree-two PBW projection. -/
theorem terminalSmith_factorSymbol_eq_zero_of_terminal_of_count_ne_two
    (r : TerminalSmithRow n L data hn)
    (hr : (r.left ++ r.right).Pairwise (· ≤ ·))
    (hterminal : terminalSmithExpansion n L data hn r = none)
    (hcount : r.factorCount n L data hn ≠ 2) :
    LieRings.PBW.factorSymbol
        (terminalSmith n L data hn).ambientBasis 2
        (r.value n L data hn) = 0 := by
  rw [r.value_eq_diagonal_smul_basisWord n L data hn, map_zsmul]
  by_cases hone : r.factorCount n L data hn = 1
  · have hwordLength : (r.smithWord n L data hn).length = 1 := by
      simpa [TerminalSmithRow.factorCount, TerminalSmithRow.smithWord,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hone
    have hsingleton : ∃ i, r.smithWord n L data hn = [i] :=
      List.length_eq_one_iff.mp hwordLength
    obtain ⟨i, hi⟩ := hsingleton
    rw [hi]
    simp only [LieRings.PBW.basisWord, LieRings.PBW.word,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [LieRings.PBW.factorSymbol_iota_of_ne_one
      (terminalSmith n L data hn).ambientBasis 2 (by omega)]
    simp
  · have htwoLt : 2 < r.factorCount n L data hn := by
      have hpos : 1 ≤ r.factorCount n L data hn := by
        simp [TerminalSmithRow.factorCount]
      omega
    have hsorted := terminalSmith_terminal_smithWord_pairwise_of_two_lt
      n L data hn r hr htwoLt hterminal
    rw [LieRings.PBW.factorSymbol_basisWord_sorted_of_length_ne
      (terminalSmith n L data hn).ambientBasis 2
      (r.smithWord n L data hn) hsorted]
    · exact smul_zero _
    · simpa [TerminalSmithRow.factorCount, TerminalSmithRow.smithWord,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount

/-- The literal symbol attached to an oriented factor-two Smith row is
exactly the degree-two PBW symbol of its enveloping word. -/
theorem TerminalSmithFactorTwo.factorSymbol_value
    (r : TerminalSmithFactorTwo n L data hn) :
    LieRings.PBW.factorSymbol
        (terminalSmith n L data hn).ambientBasis 2
        (r.1.value n L data hn) = r.symbol n L data hn := by
  classical
  rcases r with ⟨⟨mark, left, right⟩, hcount⟩
  simp only [TerminalSmithRow.factorCount] at hcount
  cases left with
  | nil =>
      simp only [List.length_nil, zero_add] at hcount
      have hright : right.length = 1 := by omega
      obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hright
      have hvalue : TerminalSmithRow.value n L data hn
            ⟨mark, [], [j]⟩ =
          UniversalEnvelopingAlgebra.ι ℤ
              ((terminalSmith n L data hn).relationBasis mark : A L n) *
            UniversalEnvelopingAlgebra.ι ℤ
              ((terminalSmith n L data hn).ambientBasis j) := by
        simp [TerminalSmithRow.value, TerminalSmithRow.ambientWord,
          LieRings.PBW.basisWord, LieRings.PBW.word]
      have hfactor : TerminalSmithFactorTwo.factor n L data hn
            ⟨⟨mark, [], [j]⟩, hcount⟩ = j := by
        simp [TerminalSmithFactorTwo.factor]
      rw [hvalue, TerminalSmithFactorTwo.symbol, hfactor]
      exact LieRings.PBW.factorSymbol_two_iota_mul_iota
        (terminalSmith n L data hn).ambientBasis _ _
  | cons j js =>
      have hjs : js = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at hcount
        omega
      subst js
      have hright : right = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons, List.length_nil] at hcount
        omega
      subst right
      have hvalue : TerminalSmithRow.value n L data hn
            ⟨mark, [j], []⟩ =
          UniversalEnvelopingAlgebra.ι ℤ
              ((terminalSmith n L data hn).ambientBasis j) *
            UniversalEnvelopingAlgebra.ι ℤ
              ((terminalSmith n L data hn).relationBasis mark : A L n) := by
        simp [TerminalSmithRow.value, TerminalSmithRow.ambientWord,
          LieRings.PBW.basisWord, LieRings.PBW.word]
      have hfactor : TerminalSmithFactorTwo.factor n L data hn
            ⟨⟨mark, [j], []⟩, hcount⟩ = j := by
        simp [TerminalSmithFactorTwo.factor]
      rw [hvalue, TerminalSmithFactorTwo.symbol, hfactor,
        LieRings.PBW.factorSymbol_two_iota_mul_iota]
      have hcomm := LinearMap.congr_fun
        (SymmetricPower.insert_comm ℤ (A L n) 0
          ((terminalSmith n L data hn).ambientBasis j)
          ((terminalSmith n L data hn).relationBasis mark : A L n))
        (SymmetricPower.monomialBasis
          (terminalSmith n L data hn).ambientBasis 0 Sym.nil)
      simpa only [LinearMap.comp_apply,
        SymmetricPower.insert_monomialBasis_zero] using hcomm

/-! ## Aggregate degree-two Stokes theorem -/

/-- Degree-two symbol read of a finite Smith factor-two row family. -/
def terminalSmithFactorTwoSymbolLinear :
    (TerminalSmithFactorTwo n L data hn →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin 2) (A L n) :=
  Finsupp.linearCombination ℤ
    (fun q ↦ q.symbol n L data hn)

/-- Degree-two symbol retained from one terminal Smith row. -/
def terminalSmithFactorTwoSymbolSeed
    (r : TerminalSmithRow n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  if h : r.factorCount n L data hn = 2 then
    TerminalSmithFactorTwo.symbol n L data hn
      (⟨r, h⟩ : TerminalSmithFactorTwo n L data hn)
  else 0

theorem terminalSmithFactorTwoSymbolLinear_part
    (r : TerminalSmithRow n L data hn) :
    terminalSmithFactorTwoSymbolLinear n L data hn
        (terminalSmithFactorTwoPart n L data hn r) =
      terminalSmithFactorTwoSymbolSeed n L data hn r := by
  classical
  by_cases hcount : r.factorCount n L data hn = 2
  · rw [terminalSmithFactorTwoPart, dif_pos hcount,
      terminalSmithFactorTwoSymbolSeed, dif_pos hcount]
    change terminalSmithFactorTwoSymbolLinear n L data hn
        (Finsupp.single
          (⟨r, hcount⟩ : TerminalSmithFactorTwo n L data hn) 1) =
      TerminalSmithFactorTwo.symbol n L data hn
        (⟨r, hcount⟩ : TerminalSmithFactorTwo n L data hn)
    rw [terminalSmithFactorTwoSymbolLinear,
      Finsupp.linearCombination_single]
    exact one_smul ℤ _
  · simp [terminalSmithFactorTwoPart, terminalSmithFactorTwoSymbolLinear,
      terminalSmithFactorTwoSymbolSeed, hcount]

/-- Exact degree-two Stokes read of one completely collected terminal Smith
row.  No saturation or quotient argument occurs: the identity is obtained by
applying the exact PBW factor projection to the collector's value invariant,
and all terminal leaves of factor number other than two vanish individually. -/
theorem factorSymbol_eq_terminalSmithFactorTwoFrontier
    (r : TerminalSmithRow n L data hn)
    (hr : (r.left ++ r.right).Pairwise (· ≤ ·)) :
    LieRings.PBW.factorSymbol
        (terminalSmith n L data hn).ambientBasis 2
        (r.value n L data hn) =
      (terminalSmithFactorTwoFrontier n L data hn r).sum
        (fun q z ↦ z • q.symbol n L data hn) := by
  classical
  let C := terminalSmithCollector n L data hn
  calc
    _ = (C.normalForm r).sum (fun q z ↦ z •
          LieRings.PBW.factorSymbol
            (terminalSmith n L data hn).ambientBasis 2
            (q.value n L data hn)) := by
      have heval := congrArg
        (LieRings.PBW.factorSymbol
          (terminalSmith n L data hn).ambientBasis 2)
        (C.evaluate_normalForm r)
      change LieRings.PBW.factorSymbol
          (terminalSmith n L data hn).ambientBasis 2
          ((C.normalForm r).sum (fun q z ↦ z • q.value n L data hn)) =
        LieRings.PBW.factorSymbol
          (terminalSmith n L data hn).ambientBasis 2
          (r.value n L data hn) at heval
      rw [map_finsuppSum] at heval
      simpa only [map_zsmul] using heval.symm
    _ = (C.normalForm r).sum (fun q z ↦ z •
          terminalSmithFactorTwoSymbolSeed n L data hn q) := by
      apply Finsupp.sum_congr
      intro q hq
      congr 1
      by_cases hcount : q.factorCount n L data hn = 2
      · rw [terminalSmithFactorTwoSymbolSeed, dif_pos hcount]
        exact TerminalSmithFactorTwo.factorSymbol_value
          n L data hn ⟨q, hcount⟩
      · rw [terminalSmithFactorTwoSymbolSeed, dif_neg hcount]
        exact terminalSmith_factorSymbol_eq_zero_of_terminal_of_count_ne_two
          n L data hn q
            (terminalSmith_normalForm_neighbors_pairwise
              n L data hn r hr q (Finsupp.mem_support_iff.mp hq))
            (C.expansion_eq_none_of_mem_normalForm_support hq) hcount
    _ = terminalSmithFactorTwoSymbolLinear n L data hn
          (terminalSmithFactorTwoFrontier n L data hn r) := by
      rw [terminalSmithFactorTwoFrontier, map_finsuppSum]
      apply Finsupp.sum_congr
      intro q hq
      rw [map_zsmul,
        terminalSmithFactorTwoSymbolLinear_part n L data hn q]
    _ = _ := rfl

/-- Boundary form of the aggregate Stokes theorem. -/
theorem dOne_terminalSmithFactorTwoChain_eq_factorSymbol
    (r : TerminalSmithRow n L data hn)
    (hr : (r.left ++ r.right).Pairwise (· ≤ ·)) :
    Koszul.dOne (terminalSmithPresentation n L data hn) 1
        (terminalSmithFactorTwoChain n L data hn r) =
      LieRings.PBW.factorSymbol
        (terminalSmith n L data hn).ambientBasis 2
        (r.value n L data hn) := by
  rw [dOne_terminalSmithFactorTwoChain,
    factorSymbol_eq_terminalSmithFactorTwoFrontier n L data hn r hr]

/-! ## Safe whole-relation factor-two interface

The preceding Smith theorem concerns the PBW splitting attached to the Smith
basis itself.  The following interface is the one used to connect to the
global homogeneous/adapted PBW ledger: its input is already an explicit
finite family of genuine full-relation × primitive rows.  Thus both reads are
taken from one literal full-label word and no naturality of exact factor
projections under a nonhomogeneous basis change is asserted.
-/

/-- Literal symmetric boundary of a finite family of genuine full-relation
factor rows. -/
def terminalFullRelationFactorBoundaryRows
    (rows : (Relations n L data × FreeModel n L) →₀ ℤ) :
    Sym[ℤ] (Fin 2) (A L n) :=
  rows.sum (fun p z ↦ z •
    SymmetricPower.insert ℤ (A L n) 1
      (prLE n L n (by omega) (p.1 : FreeModel n L))
      (SymmetricPower.degreeOne
        (prLE n L n (by omega) p.2)))

/-- Boundary of the genuine full-relation factor chain, row for row. -/
theorem dOne_terminalFullRelationFactorChainRows
    (rows : (Relations n L data × FreeModel n L) →₀ ℤ) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (terminalFullRelationFactorChainRows n L data hn rows) =
      terminalFullRelationFactorBoundaryRows n L data rows := by
  classical
  rw [terminalFullRelationFactorChainRows,
    terminalFullRelationFactorBoundaryRows, map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, terminalFullRelationFactorChain, Koszul.dOne_tmul]
  rfl

/-- The adapted/global degree-two read of the literal full-label word is the
same symmetric boundary.  This comparison is safe because every summand is
explicitly a product of exactly two primitives. -/
theorem rightSymbol_terminalFullRelationFactorWordRows
    (rows : (Relations n L data × FreeModel n L) →₀ ℤ) :
    rightSymbol n L data hn 2 n (by omega)
        (terminalFullRelationFactorWordRows n L data rows) =
      terminalFullRelationFactorBoundaryRows n L data rows := by
  classical
  rw [terminalFullRelationFactorWordRows,
    terminalFullRelationFactorBoundaryRows, map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, terminalFullRelationFactorWord]
  congr 1
  rw [rightSymbol, LinearMap.comp_apply,
    fullRightSymbol_iota_mul_iota_two]
  have hmap := LinearMap.congr_fun
    (SymmetricPower.map_insert (R₀ := ℤ)
      (M₀ := FreeModel n L) (N₀ := A L n)
      (prLE n L n (by omega)) 1 (p.1 : FreeModel n L))
    (SymmetricPower.degreeOne p.2)
  simpa only [LinearMap.comp_apply, SymmetricPower.map_degreeOne] using hmap

/-- One literal full-relation row family simultaneously realizes its global
degree-two PBW symbol and its global factor-one PBW primitive. -/
theorem terminalFullRelationFactorChainRows_reads
    (rows : (Relations n L data × FreeModel n L) →₀ ℤ) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (terminalFullRelationFactorChainRows n L data hn rows) =
        rightSymbol n L data hn 2 n (by omega)
          (terminalFullRelationFactorWordRows n L data rows) ∧
      terminalSourcePrimitive n L data hn
          (terminalFullRelationFactorChainRows n L data hn rows) =
        pbwPrimitive n L data hn
          (terminalFullRelationFactorWordRows n L data rows) := by
  constructor
  · rw [dOne_terminalFullRelationFactorChainRows,
      rightSymbol_terminalFullRelationFactorWordRows]
  · exact terminalSourcePrimitive_fullRelationFactorChainRows
      n L data hn rows
end

end LieRings.MetabelianVanishing
