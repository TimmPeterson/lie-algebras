import LieRings.DimensionSubring.MetabelianVanishing.CompleteCutoffSmith

/-!
# Koszul boundaries of the truncation-cell ledger

The ordinary edges of the marked cutoff are emitted by genuine truncation
cells.  This file records the other face of each such cell: its degree-one
Koszul row still uses the projection of the whole relation.  Both the local
and finite-sum formulas below are literal unfoldings of that construction.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffCollectedChainFintype : Fintype L :=
  Fintype.ofFinite L

/-- The Koszul boundary of one truncation cell is insertion of the projected
whole relation into the symmetric word carried by its ordinary teeth. -/
@[simp] theorem dOne_truncationCellOne
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1)
    (c : TruncationCell n L data hn) :
    Koszul.dOne (presentation n L data k hk hkn) q
        (truncationCellOne n L data hn q k hk hkn c) =
      if hlen : c.left.length = q then
        SymmetricPower.insert ℤ (A L k) q
          (relationPrefix n L data k (Nat.le_of_lt hkn) c.relation)
          (truncationCellSym n L data hn q k hkn c hlen)
      else 0 := by
  classical
  unfold truncationCellOne
  split_ifs with hlen
  · rw [Koszul.dOne_tmul]
    rfl
  · rfl

/-- When the cell lies on the selected quotient wall, the same boundary is
the complete factor-preserving symbol of the marked row immediately above
that truncation edge. -/
theorem dOne_truncationCellOne_eq_rightSymbol_of_bound
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1)
    (c : TruncationCell n L data hn) (hbound : c.bound.val = k) :
    Koszul.dOne (presentation n L data k hk hkn) q
        (truncationCellOne n L data hn q k hk hkn c) =
      if hlen : c.left.length = q then
        rightSymbol n L data hn (q + 1) k (Nat.le_of_lt hkn)
          (MarkedRow.marked c.left c.relation c.bound [] :
            MarkedRow n L data hn).value
      else 0 := by
  classical
  rw [dOne_truncationCellOne]
  split_ifs with hlen
  · subst q
    have hsymbol := rightSymbol_basisWord_mul_iota n L data hn k
      (Nat.le_of_lt hkn) c.left
      (rowTruncation n L c.bound.val (by omega)
        (c.relation : FreeModel n L))
    have hvalue :
        (MarkedRow.marked c.left c.relation c.bound [] :
            MarkedRow n L data hn).value =
          MarkedRow.basisWord n L data hn c.left *
            UniversalEnvelopingAlgebra.ι ℤ
              (rowTruncation n L c.bound.val (by omega)
                (c.relation : FreeModel n L)) := by
      simp [MarkedRow.value, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.word]
    rw [hvalue, hsymbol]
    have hprefix :
        relationPrefix n L data k (Nat.le_of_lt hkn) c.relation =
          prLE n L k (Nat.le_of_lt hkn)
            (rowTruncation n L c.bound.val (by omega)
              (c.relation : FreeModel n L)) := by
      change FreeMetabelian.Free.projectPrefix k (Nat.le_of_lt hkn)
          (c.relation : FreeModel n L) =
        FreeMetabelian.Free.projectPrefix k (Nat.le_of_lt hkn)
          (rowTruncation n L c.bound.val (by omega)
            (c.relation : FreeModel n L))
      subst k
      symm
      exact LinearMap.congr_fun
        (FreeMetabelian.Free.projectPrefix_prefixIncl
          (X := Generator L) c.bound.val (by omega))
        (FreeMetabelian.Free.projectPrefix c.bound.val (by omega)
          (c.relation : FreeModel n L))
    rw [hprefix]
    unfold truncationCellSym
    rfl
  · rfl

/-- Boundary of the complete chain on one quotient wall.  The support test,
length test, coefficient, and whole-relation label are exactly those stored
by the common truncation-cell ledger. -/
@[simp] theorem dOne_collectedSymbolChain
    {a : L} (w : GoverningWitness n L data a)
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) :
    Koszul.dOne (presentation n L data k hk hkn) q
        (collectedSymbolChain n L data hn w q k hk hkn) =
      (w.closedSquareCells n L data hn).sum (fun c z ↦
        if hbound : c.bound.val = k then
          z • if hlen : c.left.length = q then
            SymmetricPower.insert ℤ (A L k) q
              (relationPrefix n L data k (Nat.le_of_lt hkn) c.relation)
              (truncationCellSym n L data hn q k hkn c hlen)
          else 0
        else 0) := by
  classical
  rw [collectedSymbolChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hbound : c.bound.val = k
  · rw [if_pos hbound, map_zsmul, dOne_truncationCellOne,
      dif_pos hbound]
    rfl
  · rw [if_neg hbound, map_zero, dif_neg hbound]
    rfl

/-- Equivalent aggregate upper-edge formula expressed as literal marked-row
PBW symbols.  This is the form that can be compared occurrence-by-occurrence
with the contextual trace diagonal. -/
theorem dOne_collectedSymbolChain_eq_rightSymbol
    {a : L} (w : GoverningWitness n L data a)
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) :
    Koszul.dOne (presentation n L data k hk hkn) q
        (collectedSymbolChain n L data hn w q k hk hkn) =
      (w.closedSquareCells n L data hn).sum (fun c z ↦
        if hbound : c.bound.val = k then
          z • if hlen : c.left.length = q then
            rightSymbol n L data hn (q + 1) k (Nat.le_of_lt hkn)
              (MarkedRow.marked c.left c.relation c.bound [] :
                MarkedRow n L data hn).value
          else 0
        else 0) := by
  classical
  rw [collectedSymbolChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  by_cases hbound : c.bound.val = k
  · rw [if_pos hbound, map_zsmul,
      dOne_truncationCellOne_eq_rightSymbol_of_bound
        n L data hn q k hk hkn c hbound,
      dif_pos hbound]
    rfl
  · rw [if_neg hbound, map_zero, dif_neg hbound]
    rfl

end

end LieRings.MetabelianVanishing
