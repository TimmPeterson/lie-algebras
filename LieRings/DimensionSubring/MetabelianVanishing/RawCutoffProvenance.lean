import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffTraceLedger

/-!
# Provenance retained by the raw cutoff trace

The ordinary leaves of the continued cutoff are charged to
`TruncationCell`s.  Such a cell already contains all the data required by the
contextual collector: its relation is still a genuine full relation, and its
component is obtained with the empty bracket context.  Moreover its displayed
word has at least three factors, so it cannot lie on either contextual stopping
wall.  This file records that literal identification.

No component is retyped as a relation here.  The map below only adds the
empty `RelationContext` to the full relation which was already stored in the
raw cell.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffProvenanceFintype : Fintype L :=
  Fintype.ofFinite L

private theorem TruncationCell.provenancedWall_hole_eq_false
    (c : TruncationCell n L data hn) :
    provenancedWall n L data hn .hole c.bound c.left = false := by
  cases hleft : c.left with
  | nil =>
      have h : 2 ≤ 0 := by
        simpa [hleft] using c.factor_ge_three
      omega
  | cons x xs =>
      cases hxs : xs with
      | nil =>
          have h : 2 ≤ 1 := by
            simpa [hleft, hxs] using c.factor_ge_three
          omega
      | cons y ys =>
          simp [provenancedWall, hleft, hxs]

/-- A raw truncation cell, regarded as the identical contextual cell with
empty bracket context.  The factor-at-least-three invariant proves that this
is a genuine non-wall truncation occurrence. -/
def TruncationCell.toProvenancedCell
    (c : TruncationCell n L data hn) : ProvenancedCell n L data hn where
  root := c.relation
  context := .hole
  mark := c.bound
  left := c.left
  mark_pos := c.bound_pos
  not_wall := c.provenancedWall_hole_eq_false n L data hn

@[simp] theorem TruncationCell.toProvenancedCell_activeWeight
    (c : TruncationCell n L data hn) :
    (c.toProvenancedCell n L data hn).activeWeight n L data hn =
      c.bound.val := by
  simp [TruncationCell.toProvenancedCell,
    ProvenancedCell.activeWeight, RelationContext.weight]

/-- The marked upper edge is unchanged by adjoining the empty context. -/
@[simp] theorem TruncationCell.toProvenancedCell_markedRow_value
    (c : TruncationCell n L data hn) :
    (c.toProvenancedCell n L data hn).markedRow.value = c.row.value := by
  simp [TruncationCell.toProvenancedCell, ProvenancedCell.markedRow,
    ProvenancedRow.value, TruncationCell.row,
    MarkedRow.value, RelationContext.markedPrefix,
    MarkedRow.basisWord, LieRings.PBW.basisWord,
    LieRings.PBW.word]

/-- The exposed homogeneous component word is literally unchanged by
adjoining the empty context. -/
@[simp] theorem TruncationCell.toProvenancedCell_componentRow_value
    (c : TruncationCell n L data hn) :
    (c.toProvenancedCell n L data hn).componentRow.value =
      c.componentWord n L data hn := by
  simp [TruncationCell.toProvenancedCell, ProvenancedCell.componentRow,
    ProvenancedRow.value, TruncationCell.componentWord,
    TruncationCell.component, RelationContext.component,
    Nat.ne_of_gt c.bound_pos, MarkedRow.basisWord,
    LieRings.PBW.basisWord, LieRings.PBW.word]

/-- Consequently every exact factor read of the two cells agrees. -/
@[simp] theorem TruncationCell.toProvenancedCell_factorEdge
    (c : TruncationCell n L data hn)
    (q k : ℕ) (hk : k ≤ n + 1) :
    (c.toProvenancedCell n L data hn).factorEdge n L data hn q k hk =
      c.factorEdge n L data hn q k hk := by
  rw [ProvenancedCell.factorEdge, TruncationCell.factorEdge,
    c.toProvenancedCell_componentRow_value n L data hn]

/-- The complete one-factor PBW read is unchanged as well. -/
@[simp] theorem TruncationCell.toProvenancedCell_primitive
    (c : TruncationCell n L data hn) :
    (c.toProvenancedCell n L data hn).primitive n L data hn =
      c.primitive n L data hn := by
  rw [ProvenancedCell.primitive, TruncationCell.primitive,
    c.toProvenancedCell_componentRow_value n L data hn]

/-- The signed raw cutoff ledger, now indexed by contextual cells.  This is a
pure relabelling; coefficients and occurrences are not recollected. -/
def GoverningWitness.rawCutoffProvenancedCells {a : L}
    (w : GoverningWitness n L data a) :
    ProvenancedCell n L data hn →₀ ℤ :=
  (w.rawCutoffTraceCells n L data hn).sum fun c z ↦
    Finsupp.single (c.toProvenancedCell n L data hn) z

/-- The ordinary factor-two cutoff residue is the factor read of the same
signed contextual-cell ledger. -/
theorem GoverningWitness.rawCutoffOrdinaryFactorTwo_eq_provenancedCells
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffOrdinaryFactorTwo n L data hn =
      (w.rawCutoffProvenancedCells n L data hn).sum
        (fun c z ↦ z • c.factorEdge n L data hn 2 n (by omega)) := by
  classical
  rw [w.rawCutoffOrdinaryFactorTwo_eq_traceCells n L data hn,
    GoverningWitness.rawCutoffProvenancedCells,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro c hc
  simp

/-- The ordinary primitive cutoff residue is the primitive read of that very
same contextual-cell ledger. -/
theorem GoverningWitness.rawCutoffOrdinaryPrimitive_eq_provenancedCells
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffOrdinaryPrimitive n L data hn =
      (w.rawCutoffProvenancedCells n L data hn).sum
        (fun c z ↦ z • c.primitive n L data hn) := by
  classical
  rw [w.rawCutoffOrdinaryPrimitive_eq_traceCells n L data hn,
    GoverningWitness.rawCutoffProvenancedCells,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro c hc
  simp

end

end LieRings.MetabelianVanishing
