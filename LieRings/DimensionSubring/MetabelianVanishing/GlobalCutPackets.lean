import LieRings.DimensionSubring.MetabelianVanishing.GlobalVerticalFrontier
import LieRings.DimensionSubring.MetabelianVanishing.Assembly

/-!
# Packet chains read from the actual diagonal cuts

This file does not identify the new cut with the old contextual trace by
value.  It constructs `J_k` directly from the coefficient copies exposed by
the global vertical frontier, retaining the initial source, horizontal path,
vertical path, sign, and the full contextual relation cell.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalCutPacketsFintype : Fintype L :=
  Fintype.ofFinite L

/-- Recognition of a contextual cell determines the marked row from which
it was read. -/
theorem row_eq_markedRow_of_provenancedCell?_eq_some
    (r : ProvenancedRow n L data hn)
    (c : ProvenancedCell n L data hn)
    (h : provenancedCell? n L data hn r = some c) :
    r = c.markedRow n L data hn := by
  cases r with
  | component => simp [provenancedCell?] at h
  | marked root context mark left right =>
      simp [provenancedCell?] at h
      rcases h with ⟨rfl, hmark, hwall, rfl⟩
      rfl

/-- One coefficient copy on the actual global `(m_k,k)` cut. -/
abbrev GlobalDiagonalOccurrence (k : ℕ) :=
  {o : CellVerticalOccurrence n L data hn //
    o.IsDiagonalCut n L data hn k}

namespace GlobalDiagonalOccurrence

/-- The uniquely recognized contextual truncation cell at this cut copy. -/
def cell (k : ℕ) (o : GlobalDiagonalOccurrence n L data hn k) :
    ProvenancedCell n L data hn :=
  Classical.choose o.property.2.2.2.2

theorem cell_spec (k : ℕ)
    (o : GlobalDiagonalOccurrence n L data hn k) :
    provenancedCell? n L data hn o.1.row =
      some (o.cell n L data hn k) :=
  Classical.choose_spec o.property.2.2.2.2

theorem row_eq_markedRow (k : ℕ)
    (o : GlobalDiagonalOccurrence n L data hn k) :
    o.1.row = (o.cell n L data hn k).markedRow n L data hn :=
  row_eq_markedRow_of_provenancedCell?_eq_some n L data hn
    o.1.row (o.cell n L data hn k) (o.cell_spec n L data hn k)

theorem cell_left_length (k : ℕ)
    (o : GlobalDiagonalOccurrence n L data hn k) :
    (o.cell n L data hn k).left.length = n - k + 1 := by
  have hfactor := o.property.2.2.1
  rw [o.row_eq_markedRow n L data hn k] at hfactor
  simpa [ProvenancedCell.markedRow,
    ProvenancedRow.factorCount] using hfactor

theorem cell_activeWeight (k : ℕ)
    (o : GlobalDiagonalOccurrence n L data hn k) :
    (o.cell n L data hn k).activeWeight n L data hn = k := by
  have hactive := o.property.2.2.2.1
  rw [o.row_eq_markedRow n L data hn k] at hactive
  simpa [ProvenancedCell.markedRow, ProvenancedRow.activeWeight,
    ProvenancedCell.activeWeight] using hactive

/-- Genuine Koszul row carried by one global diagonal occurrence. -/
def realization
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (o : GlobalDiagonalOccurrence n L data hn k) :
    Koszul.One (presentation n L data k (by omega) (by omega))
      (n - k + 1) :=
  (o.cell n L data hn k).one n L data hn (n - k + 1) k
    (by omega) (by omega)

end GlobalDiagonalOccurrence

/-- The manuscript chain `chi_k`, now definitionally the signed sum over
the actual global diagonal cut. -/
def GoverningWitness.globalPacketChain
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.One (presentation n L data k (by omega) (by omega))
      (n - k + 1) :=
  (w.diagonalCutOccurrences n L data hn k).sum fun o z ↦
    z • GlobalDiagonalOccurrence.realization n L data hn k hk hkn o

/-- Exact occurrence-level boundary of the packet exposed by the global
cut.  No equal rows or equal values have been combined at the index level. -/
theorem GoverningWitness.dOne_globalPacketChain
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.dOne (presentation n L data k (by omega) (by omega))
        (n - k + 1) (w.globalPacketChain n L data hn k hk hkn) =
      (w.diagonalCutOccurrences n L data hn k).sum fun o z ↦
        z • rightSymbol n L data hn (n - k + 2) k (by omega)
          o.1.row.value := by
  classical
  rw [GoverningWitness.globalPacketChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro o ho
  rw [map_zsmul, GlobalDiagonalOccurrence.realization,
    ProvenancedCell.dOne_one,
    dif_pos (GlobalDiagonalOccurrence.cell_left_length n L data hn k o),
    dif_pos (GlobalDiagonalOccurrence.cell_activeWeight n L data hn k o)]
  rw [show n - k + 1 + 1 = n - k + 2 by omega]
  rw [GlobalDiagonalOccurrence.row_eq_markedRow n L data hn k o]
  congr 1

/-- The common vertical read on the actual global diagonal cut.  The
full-relation product and its homogeneous horizontal child are compared
cell by cell, with the same occurrence coefficient. -/
theorem GoverningWitness.T_dOne_globalPacketChain_eq_component_cut
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    T n L data k hk hkn
        (Koszul.dOne (presentation n L data k (by omega) (by omega))
          (n - k + 1) (w.globalPacketChain n L data hn k hk hkn)) =
      (w.diagonalCutOccurrences n L data hn k).sum fun o z ↦
        z • T n L data k hk hkn
          ((GlobalDiagonalOccurrence.cell n L data hn k o).factorEdge n L data hn
            (n - k + 2) k (by omega)) := by
  classical
  rw [w.dOne_globalPacketChain n L data hn k hk hkn,
    map_finsuppSum]
  apply Finsupp.sum_congr
  intro o ho
  rw [map_zsmul]
  congr 1
  rw [GlobalDiagonalOccurrence.row_eq_markedRow n L data hn k o]
  apply ProvenancedCell.T_markedRow_eq_T_componentRow
    n L data hn (GlobalDiagonalOccurrence.cell n L data hn k o)
      k hk hkn
  · exact GlobalDiagonalOccurrence.cell_left_length n L data hn k o
  · exact GlobalDiagonalOccurrence.cell_activeWeight n L data hn k o

end

end LieRings.MetabelianVanishing
