import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmith
import LieRings.DimensionSubring.DegreeFive.PacketCollector
import LieRings.DimensionSubring.DegreeFive.PlacedIdentities

/-!
# Smith-basis collection at the terminal presentation

This file develops the terminal factor collector directly in the ordered
Smith bases of the canonical presentation `D_n → A_n`.  In particular a
marked entry is always an actual basis element of `D_n`; bracket corrections
are expanded back in that same relation basis.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalSmithCollectorFintype : Fintype L := Fintype.ofFinite L

/-! ## Source-Smith marked rows -/

/-- The common finite index set for the ambient and relation Smith bases. -/
abbrev TerminalSmithIndex := Fin (terminalSmith n L data hn).rank

/-- A PBW word with one distinguished genuine `D_n` Smith-basis factor.
The two ordinary words are kept separately because the distinguished factor
must be moved in either direction when its Smith index changes after a
bracket correction. -/
structure TerminalSmithRow where
  mark : TerminalSmithIndex n L data hn
  left : List (TerminalSmithIndex n L data hn)
  right : List (TerminalSmithIndex n L data hn)

noncomputable instance : DecidableEq (TerminalSmithRow n L data hn) :=
  Classical.decEq _

namespace TerminalSmithRow

/-- Ordinary terminal Smith-basis word. -/
def ambientWord (xs : List (TerminalSmithIndex n L data hn)) :
    UEA ℤ (A L n) :=
  LieRings.PBW.basisWord ℤ (A L n) _
    (terminalSmith n L data hn).ambientBasis xs

/-- Exact enveloping-algebra value of a marked row. -/
def value (r : TerminalSmithRow n L data hn) : UEA ℤ (A L n) :=
  ambientWord n L data hn r.left *
    UniversalEnvelopingAlgebra.ι ℤ
      ((terminalSmith n L data hn).relationBasis r.mark : A L n) *
    ambientWord n L data hn r.right

/-- Number of Lie factors, counting the marked relation once. -/
def factorCount (r : TerminalSmithRow n L data hn) : ℕ :=
  r.left.length + r.right.length + 1

/-- Left ordinary factors that still lie strictly after the mark. -/
def badLeft (r : TerminalSmithRow n L data hn) : ℕ :=
  (r.left.filter fun i ↦ r.mark < i).length

/-- Right ordinary factors that still lie strictly before the mark. -/
def badRight (r : TerminalSmithRow n L data hn) : ℕ :=
  (r.right.filter fun i ↦ i < r.mark).length

/-- Number of unresolved crossings of the marked Smith factor. -/
def unresolved (r : TerminalSmithRow n L data hn) : ℕ :=
  r.badLeft n L data hn + r.badRight n L data hn

/-- A single natural measure: corrections lower factor count, while principal
crossings preserve factor count and lower `unresolved`. -/
def descentMeasure (r : TerminalSmithRow n L data hn) : ℕ :=
  r.factorCount n L data hn * r.factorCount n L data hn +
    r.unresolved n L data hn

/-- Lexicographic form of the same termination argument. -/
def measure (r : TerminalSmithRow n L data hn) : ℕ × ℕ :=
  (r.factorCount n L data hn, r.unresolved n L data hn)

end TerminalSmithRow

/-! ## One-step source-Smith placement -/

/-- Literal support list of a finite coefficient family. -/
def terminalTaggedList {I P : Type*} [DecidableEq I]
    (c : I →₀ ℤ) (f : I → P) : List (ℤ × P) :=
  c.support.toList.map fun i ↦ (c i, f i)

theorem terminalTaggedList_value_sum {I P B : Type*} [DecidableEq I]
    [AddCommGroup B] (c : I →₀ ℤ) (f : I → P) (v : P → B) :
    ((terminalTaggedList c f).map fun q ↦ q.1 • v q.2).sum =
      c.sum (fun i z ↦ z • v (f i)) := by
  classical
  simp [terminalTaggedList, Finsupp.sum]

theorem terminalTaggedList_neg_value_sum {I P B : Type*} [DecidableEq I]
    [AddCommGroup B] (c : I →₀ ℤ) (f : I → P) (v : P → B) :
    (((terminalTaggedList c f).map fun q ↦ (-q.1, q.2)).map
        (fun q ↦ q.1 • v q.2)).sum =
      -c.sum (fun i z ↦ z • v (f i)) := by
  classical
  have hneg : ∀ xs : List (ℤ × P),
      (((xs.map fun q ↦ (-q.1, q.2)).map
          (fun q ↦ q.1 • v q.2)).sum) =
        -((xs.map fun q ↦ q.1 • v q.2).sum) := by
    intro xs
    induction xs with
    | nil => simp
    | cons q xs ih =>
        simp only [List.map_cons, List.sum_cons, neg_smul]
        rw [ih]
        abel
  rw [hneg, terminalTaggedList_value_sum]

/-- Split a nonempty word into its initial segment and final letter. -/
def terminalSplitLast? {I : Type*} (xs : List I) : Option (List I × I) :=
  xs.getLast?.map fun last ↦ (xs.dropLast, last)

theorem terminalSplitLast?_eq_some {I : Type*} {xs front : List I} {last : I}
    (h : terminalSplitLast? xs = some (front, last)) :
    xs = front ++ [last] := by
  unfold terminalSplitLast? at h
  cases hlast : xs.getLast? with
  | none => simp [hlast] at h
  | some y =>
      simp only [hlast, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact (List.dropLast_append_getLast? y (by simp [hlast])).symm

/-- The negative correction list for `a_j d_i = d_i a_j - [d_i,a_j]`. -/
def terminalMoveLeftExpansion
    (i : TerminalSmithIndex n L data hn)
    (front : List (TerminalSmithIndex n L data hn))
    (x : TerminalSmithIndex n L data hn)
    (right : List (TerminalSmithIndex n L data hn)) :
    List (ℤ × TerminalSmithRow n L data hn) :=
  (1, ⟨i, front, x :: right⟩) ::
    (terminalTaggedList (terminalSmithBracketCoordinates n L data hn i x)
      (fun j ↦ (⟨j, front, right⟩ : TerminalSmithRow n L data hn))).map
        (fun q ↦ (-q.1, q.2))

/-- The positive correction list for `d_i a_j = a_j d_i + [d_i,a_j]`. -/
def terminalMoveRightExpansion
    (i : TerminalSmithIndex n L data hn)
    (left : List (TerminalSmithIndex n L data hn))
    (x : TerminalSmithIndex n L data hn)
    (tail : List (TerminalSmithIndex n L data hn)) :
    List (ℤ × TerminalSmithRow n L data hn) :=
  (1, ⟨i, left ++ [x], tail⟩) ::
    terminalTaggedList (terminalSmithBracketCoordinates n L data hn i x)
      (fun j ↦ (⟨j, left, tail⟩ : TerminalSmithRow n L data hn))

/-- Deterministic terminal placement.  Factor-two rows stop immediately.
Above factor two, the mark first crosses a bad final left factor, then a bad
initial right factor.  Each bracket is expanded at once in the genuine
terminal relation Smith basis. -/
def terminalSmithExpansion (r : TerminalSmithRow n L data hn) :
    Option (List (ℤ × TerminalSmithRow n L data hn)) :=
  if hsmall : r.factorCount n L data hn ≤ 2 then none
  else
    match terminalSplitLast? r.left with
    | some (front, x) =>
        if hx : r.mark < x then
          some (terminalMoveLeftExpansion n L data hn r.mark front x r.right)
        else
          match r.right with
          | [] => none
          | y :: tail =>
              if hy : y < r.mark then
                some (terminalMoveRightExpansion n L data hn r.mark r.left y tail)
              else none
    | none =>
        match r.right with
        | [] => none
        | y :: tail =>
            if hy : y < r.mark then
              some (terminalMoveRightExpansion n L data hn r.mark r.left y tail)
            else none

theorem terminalMoveLeftExpansion_decreases
    (i : TerminalSmithIndex n L data hn)
    (front : List (TerminalSmithIndex n L data hn))
    (x : TerminalSmithIndex n L data hn)
    (right : List (TerminalSmithIndex n L data hn))
    (hx : i < x) :
    ∀ q ∈ terminalMoveLeftExpansion n L data hn i front x right,
      Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
        (q.2.measure n L data hn)
        ((⟨i, front ++ [x], right⟩ :
          TerminalSmithRow n L data hn).measure n L data hn) := by
  classical
  intro q hq
  simp only [terminalMoveLeftExpansion, List.mem_cons, List.mem_map] at hq
  rcases hq with rfl | ⟨p, hp, rfl⟩
  · simp only [TerminalSmithRow.measure, TerminalSmithRow.factorCount,
      List.length_append, List.length_singleton, List.length_cons,
      List.length_nil]
    have hcount : front.length + (right.length + 1) + 1 =
        front.length + (0 + 1) + right.length + 1 := by
      simp
      omega
    rw [hcount]
    apply Prod.Lex.right
    simp [TerminalSmithRow.unresolved, TerminalSmithRow.badLeft,
      TerminalSmithRow.badRight, hx, not_lt_of_ge hx.le]
  · unfold terminalTaggedList at hp
    rw [List.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    apply Prod.Lex.left
    simp [TerminalSmithRow.measure, TerminalSmithRow.factorCount]

theorem terminalMoveRightExpansion_decreases
    (i : TerminalSmithIndex n L data hn)
    (left : List (TerminalSmithIndex n L data hn))
    (x : TerminalSmithIndex n L data hn)
    (tail : List (TerminalSmithIndex n L data hn))
    (hx : x < i) :
    ∀ q ∈ terminalMoveRightExpansion n L data hn i left x tail,
      Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
        (q.2.measure n L data hn)
        ((⟨i, left, x :: tail⟩ :
          TerminalSmithRow n L data hn).measure n L data hn) := by
  classical
  intro q hq
  simp only [terminalMoveRightExpansion, List.mem_cons] at hq
  rcases hq with rfl | hp
  · simp only [TerminalSmithRow.measure, TerminalSmithRow.factorCount,
      List.length_append, List.length_singleton, List.length_cons,
      List.length_nil]
    have hcount : left.length + (0 + 1) + tail.length + 1 =
        left.length + (tail.length + 1) + 1 := by
      simp
      omega
    rw [hcount]
    apply Prod.Lex.right
    simp [TerminalSmithRow.unresolved, TerminalSmithRow.badLeft,
      TerminalSmithRow.badRight, hx, not_lt_of_ge hx.le]
  · unfold terminalTaggedList at hp
    rw [List.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    apply Prod.Lex.left
    simp [TerminalSmithRow.measure, TerminalSmithRow.factorCount]

theorem terminalSmithExpansion_decreases
    {r : TerminalSmithRow n L data hn}
    {rows : List (ℤ × TerminalSmithRow n L data hn)}
    (h : terminalSmithExpansion n L data hn r = some rows) :
    ∀ q ∈ rows,
      Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
        (q.2.measure n L data hn) (r.measure n L data hn) := by
  classical
  rcases r with ⟨i, left, right⟩
  intro q hq
  by_cases hsmall :
      TerminalSmithRow.factorCount n L data hn ⟨i, left, right⟩ ≤ 2
  · simp [terminalSmithExpansion, hsmall] at h
  cases hs : terminalSplitLast? left with
  | none =>
      cases right with
      | nil => simp [terminalSmithExpansion, hsmall, hs] at h
      | cons y tail =>
          by_cases hy : y < i
          · simp [terminalSmithExpansion, hsmall, hs, hy] at h
            subst rows
            exact terminalMoveRightExpansion_decreases n L data hn
              i left y tail hy q hq
          · simp [terminalSmithExpansion, hsmall, hs, hy] at h
  | some p =>
      rcases p with ⟨front, x⟩
      have hleft : left = front ++ [x] := terminalSplitLast?_eq_some hs
      by_cases hx : i < x
      · simp [terminalSmithExpansion, hsmall, hs, hx] at h
        subst rows
        subst left
        exact terminalMoveLeftExpansion_decreases n L data hn
          i front x right hx q hq
      · cases right with
        | nil => simp [terminalSmithExpansion, hsmall, hs, hx] at h
        | cons y tail =>
            by_cases hy : y < i
            · simp [terminalSmithExpansion, hsmall, hs, hx, hy] at h
              subst rows
              exact terminalMoveRightExpansion_decreases n L data hn
                i left y tail hy q hq
            · simp [terminalSmithExpansion, hsmall, hs, hx, hy] at h

/-! ## Exact value preservation -/

/-- Finitely-supported version of the terminal Smith bracket expansion. -/
theorem terminalSmithBracket_finsupp_sum
    (i j : TerminalSmithIndex n L data hn) :
    (terminalSmithBracketCoordinates n L data hn i j).sum
        (fun k z ↦ z •
          ((terminalSmith n L data hn).relationBasis k : A L n)) =
      ⁅((terminalSmith n L data hn).relationBasis i : A L n),
        (terminalSmith n L data hn).ambientBasis j⁆ := by
  classical
  rw [Finsupp.sum_fintype _ _ (by intro k; simp)]
  exact terminalSmithBracket_sum n L data hn i j

/-- Fixed enveloping words on both sides form a linear context in the
distinguished Lie factor. -/
def terminalSmithContext
    (left right : List (TerminalSmithIndex n L data hn)) :
    A L n →ₗ[ℤ] UEA ℤ (A L n) where
  toFun z := TerminalSmithRow.ambientWord n L data hn left *
    UniversalEnvelopingAlgebra.ι ℤ z *
    TerminalSmithRow.ambientWord n L data hn right
  map_add' x y := by rw [map_add, mul_add, add_mul]
  map_smul' z x := by
    rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
    rfl

/-- Bracket coordinate correction evaluated in an arbitrary marked-row
context. -/
theorem terminalSmithCorrection_value
    (i x : TerminalSmithIndex n L data hn)
    (left right : List (TerminalSmithIndex n L data hn)) :
    ((terminalTaggedList (terminalSmithBracketCoordinates n L data hn i x)
        (fun j ↦ (⟨j, left, right⟩ : TerminalSmithRow n L data hn))).map
      (fun q ↦ q.1 • q.2.value n L data hn)).sum =
      TerminalSmithRow.ambientWord n L data hn left *
        UniversalEnvelopingAlgebra.ι ℤ
          ⁅((terminalSmith n L data hn).relationBasis i : A L n),
            (terminalSmith n L data hn).ambientBasis x⁆ *
        TerminalSmithRow.ambientWord n L data hn right := by
  classical
  rw [terminalTaggedList_value_sum]
  let ctx := terminalSmithContext n L data hn left right
  have h := congrArg ctx
    (terminalSmithBracket_finsupp_sum n L data hn i x)
  rw [map_finsuppSum] at h
  simpa only [map_zsmul, TerminalSmithRow.value, ctx,
    terminalSmithContext] using h

theorem terminalSmithCorrection_finsupp_value
    (i x : TerminalSmithIndex n L data hn)
    (left right : List (TerminalSmithIndex n L data hn)) :
    (terminalSmithBracketCoordinates n L data hn i x).sum
        (fun j z ↦ z •
          (⟨j, left, right⟩ :
            TerminalSmithRow n L data hn).value n L data hn) =
      TerminalSmithRow.ambientWord n L data hn left *
        UniversalEnvelopingAlgebra.ι ℤ
          ⁅((terminalSmith n L data hn).relationBasis i : A L n),
            (terminalSmith n L data hn).ambientBasis x⁆ *
        TerminalSmithRow.ambientWord n L data hn right := by
  rw [← terminalTaggedList_value_sum]
  exact terminalSmithCorrection_value n L data hn i x left right

theorem terminalMoveLeftExpansion_preserves
    (i : TerminalSmithIndex n L data hn)
    (front : List (TerminalSmithIndex n L data hn))
    (x : TerminalSmithIndex n L data hn)
    (right : List (TerminalSmithIndex n L data hn)) :
    ((terminalMoveLeftExpansion n L data hn i front x right).map
        (fun q ↦ q.1 • q.2.value n L data hn)).sum =
      (⟨i, front ++ [x], right⟩ :
        TerminalSmithRow n L data hn).value n L data hn := by
  classical
  simp only [terminalMoveLeftExpansion, List.map_cons, List.sum_cons,
    one_smul]
  rw [terminalTaggedList_neg_value_sum,
    terminalSmithCorrection_finsupp_value]
  let S := terminalSmith n L data hn
  let lw := TerminalSmithRow.ambientWord n L data hn front
  let rwrd := TerminalSmithRow.ambientWord n L data hn right
  let ix := UniversalEnvelopingAlgebra.ι ℤ (S.ambientBasis x)
  let ir := UniversalEnvelopingAlgebra.ι ℤ (S.relationBasis i : A L n)
  let ib := UniversalEnvelopingAlgebra.ι ℤ
    ⁅(S.relationBasis i : A L n), S.ambientBasis x⁆
  have happend : TerminalSmithRow.ambientWord n L data hn (front ++ [x]) =
      lw * ix := by
    simp [TerminalSmithRow.ambientWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, List.map_append, lw, ix, S]
  have hcons : TerminalSmithRow.ambientWord n L data hn (x :: right) =
      ix * rwrd := by
    simp [TerminalSmithRow.ambientWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, rwrd, ix, S]
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ (A L n)
    (S.ambientBasis x) (S.relationBasis i : A L n)
  have hskew : UniversalEnvelopingAlgebra.ι ℤ
      ⁅S.ambientBasis x, (S.relationBasis i : A L n)⁆ = -ib := by
    rw [← lie_skew, map_neg]
  rw [hskew] at hswap
  simp only [TerminalSmithRow.value]
  rw [happend, hcons]
  change lw * ir * (ix * rwrd) + -(lw * ib * rwrd) =
    lw * ix * ir * rwrd
  change ix * ir = ir * ix + -ib at hswap
  calc
    _ = lw * (ir * ix + -ib) * rwrd := by noncomm_ring
    _ = lw * (ix * ir) * rwrd := by rw [← hswap]
    _ = _ := by noncomm_ring

theorem terminalMoveRightExpansion_preserves
    (i : TerminalSmithIndex n L data hn)
    (left : List (TerminalSmithIndex n L data hn))
    (x : TerminalSmithIndex n L data hn)
    (tail : List (TerminalSmithIndex n L data hn)) :
    ((terminalMoveRightExpansion n L data hn i left x tail).map
        (fun q ↦ q.1 • q.2.value n L data hn)).sum =
      (⟨i, left, x :: tail⟩ :
        TerminalSmithRow n L data hn).value n L data hn := by
  classical
  simp only [terminalMoveRightExpansion, List.map_cons, List.sum_cons,
    one_smul]
  rw [terminalSmithCorrection_value]
  let S := terminalSmith n L data hn
  let lw := TerminalSmithRow.ambientWord n L data hn left
  let rwrd := TerminalSmithRow.ambientWord n L data hn tail
  let ix := UniversalEnvelopingAlgebra.ι ℤ (S.ambientBasis x)
  let ir := UniversalEnvelopingAlgebra.ι ℤ (S.relationBasis i : A L n)
  let ib := UniversalEnvelopingAlgebra.ι ℤ
    ⁅(S.relationBasis i : A L n), S.ambientBasis x⁆
  have happend : TerminalSmithRow.ambientWord n L data hn (left ++ [x]) =
      lw * ix := by
    simp [TerminalSmithRow.ambientWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, List.map_append, lw, ix, S]
  have hcons : TerminalSmithRow.ambientWord n L data hn (x :: tail) =
      ix * rwrd := by
    simp [TerminalSmithRow.ambientWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, rwrd, ix, S]
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ (A L n)
    (S.relationBasis i : A L n) (S.ambientBasis x)
  simp only [TerminalSmithRow.value]
  rw [happend, hcons]
  change lw * ix * ir * rwrd + lw * ib * rwrd =
    lw * ir * (ix * rwrd)
  change ir * ix = ix * ir + ib at hswap
  calc
    _ = lw * (ix * ir + ib) * rwrd := by noncomm_ring
    _ = lw * (ir * ix) * rwrd := by rw [← hswap]
    _ = _ := by noncomm_ring

theorem terminalSmithExpansion_preserves
    {r : TerminalSmithRow n L data hn}
    {rows : List (ℤ × TerminalSmithRow n L data hn)}
    (h : terminalSmithExpansion n L data hn r = some rows) :
    (rows.map fun q ↦ q.1 • q.2.value n L data hn).sum =
      r.value n L data hn := by
  classical
  rcases r with ⟨i, left, right⟩
  by_cases hsmall :
      TerminalSmithRow.factorCount n L data hn ⟨i, left, right⟩ ≤ 2
  · simp [terminalSmithExpansion, hsmall] at h
  cases hs : terminalSplitLast? left with
  | none =>
      cases right with
      | nil => simp [terminalSmithExpansion, hsmall, hs] at h
      | cons y tail =>
          by_cases hy : y < i
          · simp [terminalSmithExpansion, hsmall, hs, hy] at h
            subst rows
            exact terminalMoveRightExpansion_preserves n L data hn
              i left y tail
          · simp [terminalSmithExpansion, hsmall, hs, hy] at h
  | some p =>
      rcases p with ⟨front, x⟩
      have hleft : left = front ++ [x] := terminalSplitLast?_eq_some hs
      by_cases hx : i < x
      · simp [terminalSmithExpansion, hsmall, hs, hx] at h
        subst rows
        subst left
        exact terminalMoveLeftExpansion_preserves n L data hn
          i front x right
      · cases right with
        | nil => simp [terminalSmithExpansion, hsmall, hs, hx] at h
        | cons y tail =>
            by_cases hy : y < i
            · simp [terminalSmithExpansion, hsmall, hs, hx, hy] at h
              subst rows
              exact terminalMoveRightExpansion_preserves n L data hn
                i left y tail
            · simp [terminalSmithExpansion, hsmall, hs, hx, hy] at h

/-- The complete deterministic source-Smith collector. -/
def terminalSmithCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (TerminalSmithRow n L data hn) (UEA ℤ (A L n)) where
  relation x y := Prod.Lex (fun a b : ℕ ↦ a < b)
    (fun a b : ℕ ↦ a < b)
      (x.measure n L data hn) (y.measure n L data hn)
  wellFounded := InvImage.wf (TerminalSmithRow.measure n L data hn)
    (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  expansion := terminalSmithExpansion n L data hn
  value := TerminalSmithRow.value n L data hn
  decreases := terminalSmithExpansion_decreases n L data hn
  preserves := terminalSmithExpansion_preserves n L data hn

/-! ## The factor-two Koszul frontier -/

/-- The canonical terminal presentation, named locally to keep this file
independent of the earlier terminal-block architecture. -/
abbrev terminalSmithPresentation :=
  presentation n L data n (by omega) (by omega)

/-- A collected terminal row having exactly one ordinary factor beside its
genuine relation-basis mark. -/
abbrev TerminalSmithFactorTwo :=
  {r : TerminalSmithRow n L data hn //
    r.factorCount n L data hn = 2}

namespace TerminalSmithFactorTwo

/-- The unique ordinary factor in a factor-two row, independent of whether
it lies to the left or right of the mark. -/
def factor (r : TerminalSmithFactorTwo n L data hn) :
    TerminalSmithIndex n L data hn :=
  (r.1.left ++ r.1.right).get ⟨0, by
    have hlen : (r.1.left ++ r.1.right).length = 1 := by
      simp only [List.length_append]
      have hr := r.property
      simp only [TerminalSmithRow.factorCount] at hr
      omega
    omega⟩

/-- One factor-two row as a degree-one Koszul chain. -/
def one (r : TerminalSmithFactorTwo n L data hn) :
    Koszul.One (terminalSmithPresentation n L data hn) 1 :=
  (terminalSmith n L data hn).relationBasis r.1.mark ⊗ₜ[ℤ]
    SymmetricPower.degreeOne
      ((terminalSmith n L data hn).ambientBasis (r.factor n L data hn))

/-- Literal symmetric boundary symbol of a factor-two Smith row. -/
def symbol (r : TerminalSmithFactorTwo n L data hn) :
    Sym[ℤ] (Fin 2) (A L n) :=
  SymmetricPower.insert ℤ (A L n) 1
    ((terminalSmith n L data hn).relationBasis r.1.mark : A L n)
    (SymmetricPower.degreeOne
      ((terminalSmith n L data hn).ambientBasis (r.factor n L data hn)))

/-- Boundary of one factor-two frontier row. -/
@[simp] theorem dOne_one (r : TerminalSmithFactorTwo n L data hn) :
    Koszul.dOne (terminalSmithPresentation n L data hn) 1
        (r.one n L data hn) = r.symbol n L data hn := by
  rw [TerminalSmithFactorTwo.one, Koszul.dOne_tmul]
  rfl

end TerminalSmithFactorTwo

/-- Keep exactly the factor-two rows of an arbitrary finite row sum. -/
def terminalSmithFactorTwoPart (r : TerminalSmithRow n L data hn) :
    TerminalSmithFactorTwo n L data hn →₀ ℤ :=
  if h : r.factorCount n L data hn = 2 then
    Finsupp.single ⟨r, h⟩ 1
  else 0

/-- Factor-two portion of the fully collected normal form of one row. -/
def terminalSmithFactorTwoFrontier (r : TerminalSmithRow n L data hn) :
    TerminalSmithFactorTwo n L data hn →₀ ℤ :=
  (terminalSmithCollector n L data hn).normalForm r |>.sum
    (fun q z ↦ z • terminalSmithFactorTwoPart n L data hn q)

/-- Degree-one Koszul chain read from the factor-two frontier. -/
def terminalSmithFactorTwoChain (r : TerminalSmithRow n L data hn) :
    Koszul.One (terminalSmithPresentation n L data hn) 1 :=
  (terminalSmithFactorTwoFrontier n L data hn r).sum
    (fun q z ↦ z • q.one n L data hn)

/-- The promised compiling frontier boundary: no component has been treated
as a relation.  Every tensor entry is an actual terminal relation-basis
vector, and its boundary is the corresponding exact symmetric Smith symbol. -/
@[simp] theorem dOne_terminalSmithFactorTwoChain
    (r : TerminalSmithRow n L data hn) :
    Koszul.dOne (terminalSmithPresentation n L data hn) 1
        (terminalSmithFactorTwoChain n L data hn r) =
      (terminalSmithFactorTwoFrontier n L data hn r).sum
        (fun q z ↦ z • q.symbol n L data hn) := by
  classical
  rw [terminalSmithFactorTwoChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro q hq
  rw [map_zsmul, TerminalSmithFactorTwo.dOne_one]
  rfl

end

end LieRings.MetabelianVanishing
