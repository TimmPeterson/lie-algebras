import LieRings.DimensionSubring.MetabelianVanishing.GlobalSaturatedTrace
import LieRings.DimensionSubring.MetabelianVanishing.TriangularRows

/-!
# The literal initial occurrence list of the global trace

The corrected proof starts the two-dimensional ledger before equal PBW
summands are combined.  This file turns the two finite supports in the
governing expression into that literal list and proves that forgetting its
labels gives exactly the already-audited contextual initial row.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalInitialTraceFintype : Fintype L :=
  Fintype.ofFinite L

private theorem sum_supportList
    {I M : Type*} [AddCommMonoid M]
    (f : I →₀ ℤ) (g : I → ℤ → M) :
    (f.support.toList.map fun i ↦ g i (f i)).sum = f.sum g := by
  classical
  rw [Finsupp.sum]
  induction f.support using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [hi]

private theorem sum_flatMap
    {I M : Type*} [AddCommMonoid M]
    (l : List I) (g : I → List M) :
    (l.flatMap g).sum = (l.map fun i ↦ (g i).sum).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih]

private theorem sum_map_flatMap
    {I M N : Type*} [AddCommMonoid N]
    (l : List I) (g : I → List M) (h : M → N) :
    ((l.flatMap g).map h).sum =
      (l.map fun i ↦ ((g i).map h).sum).sum := by
  rw [List.map_flatMap, sum_flatMap]

/-- A literal source copy after the manuscript's triangular expansion of the
full relation entry.  The leading-weight tag remains part of the source
label throughout the global trace. -/
structure GlobalInitialPacketLabel where
  relationTag : TriangularRelationIndex n L
  rightTerm : UEA ℤ (FreeModel n L)
  exponent : AdaptedIndex n L data hn →₀ ℕ

noncomputable instance : DecidableEq (GlobalInitialPacketLabel n L data hn) :=
  Classical.decEq _

namespace GlobalInitialPacketLabel

/-- The literal top-marked row belonging to one relation/right-PBW-monomial
source label. -/
def row (label : GlobalInitialPacketLabel n L data hn) :
    ProvenancedRow n L data hn :=
  .marked (triangularRelationOfIndex n L data label.relationTag)
    .hole ⟨n + 1, by omega⟩ []
    (exponentWord n L data hn label.exponent)

end GlobalInitialPacketLabel

/-- The manuscript's initial signed occurrence list.  The outer support
remembers the full relation/right-multiplier summand and the inner support
remembers its PBW monomial. -/
def GoverningWitness.globalInitialLabels
    {a : L} (w : GoverningWitness n L data a) :
    List (ℤ × GlobalInitialPacketLabel n L data hn) :=
  w.triangularTaggedRelationCoefficients n L data |>.support.toList.flatMap
      fun p ↦
    let coordinates := (adaptedWeightedBasis n L data hn).pbwEquiv.symm p.2
    coordinates.support.toList.map fun e ↦
      (w.triangularTaggedRelationCoefficients n L data p * coordinates e,
        { relationTag := p.1, rightTerm := p.2, exponent := e })

/-- Forget only the source label, retaining one list entry for each literal
initial coefficient copy. -/
def GoverningWitness.globalInitialRows
    {a : L} (w : GoverningWitness n L data a) :
    List (ℤ × ProvenancedRow n L data hn) :=
  (w.globalInitialLabels n L data hn).map fun q ↦
    (q.1, q.2.row n L data hn)

/-- Provenance-row form of the triangularized relative chain. -/
def GoverningWitness.globalTriangularInitial
    {a : L} (w : GoverningWitness n L data a) :
    ProvenancedRow n L data hn →₀ ℤ :=
  (w.triangularTaggedRelationCoefficients n L data).sum fun p z ↦
    z • provenancedRowsOfRightFactor n L data hn
      (triangularRelationOfIndex n L data p.1) p.2

/-- Aggregation of the literal initial list recovers the contextual initial
row exactly.  This is the formal statement that no initial occurrence was
discarded before the global trace was formed. -/
theorem GoverningWitness.sum_globalInitialRows
    {a : L} (w : GoverningWitness n L data a) :
    (w.globalInitialRows n L data hn |>.map fun q ↦
      Finsupp.single q.2 q.1).sum =
      w.globalTriangularInitial n L data hn := by
  classical
  rw [GoverningWitness.globalInitialRows,
    GoverningWitness.globalInitialLabels,
    GoverningWitness.globalTriangularInitial]
  rw [List.map_map, sum_map_flatMap]
  simp only [List.map_map]
  calc
    _ = (w.triangularTaggedRelationCoefficients n L data).sum (fun p z ↦
        let coordinates :=
          (adaptedWeightedBasis n L data hn).pbwEquiv.symm p.2
        (coordinates.support.toList.map fun e ↦
          Finsupp.single
            (GlobalInitialPacketLabel.row n L data hn
              { relationTag := p.1, rightTerm := p.2, exponent := e })
            (z * coordinates e)).sum) :=
      sum_supportList (w.triangularTaggedRelationCoefficients n L data) _
    _ = _ := by
      apply Finsupp.sum_congr
      intro p hp
      let coordinates :=
        (adaptedWeightedBasis n L data hn).pbwEquiv.symm p.2
      change
        ((coordinates.support.toList.map fun e ↦
          Finsupp.single (GlobalInitialPacketLabel.row n L data hn
            { relationTag := p.1, rightTerm := p.2, exponent := e })
            (w.triangularTaggedRelationCoefficients n L data p *
              coordinates e)).sum) =
          w.triangularTaggedRelationCoefficients n L data p •
            provenancedRowsOfRightFactor n L data hn
              (triangularRelationOfIndex n L data p.1) p.2
      rw [provenancedRowsOfRightFactor, Finsupp.smul_sum]
      rw [← sum_supportList]
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      simp only [GlobalInitialPacketLabel.row]
      rw [Finsupp.smul_single, smul_eq_mul]

/-- Triangularization changes only the relation basis, not the evaluated
governing word. -/
theorem GoverningWitness.evaluate_globalTriangularInitial
    {a : L} (w : GoverningWitness n L data a) :
    (provenancedCollector n L data hn).evaluate
        (w.globalTriangularInitial n L data hn) = w.theta := by
  classical
  rw [GoverningWitness.globalTriangularInitial, map_finsuppSum]
  calc
    _ = (w.triangularTaggedRelationCoefficients n L data).sum
        (fun p z ↦ z •
          (UniversalEnvelopingAlgebra.ι ℤ
              (triangularRelationOfIndex n L data p.1 : FreeModel n L) *
            p.2)) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [map_zsmul,
        evaluate_provenancedRowsOfRightFactor]
    _ = w.theta := w.triangularTaggedTheta_eq_theta n L data

/-- The actual governing-witness uncut comparison trace.  Root indices are
attached before recursion, hence repeated equal rows remain separate. -/
def GoverningWitness.globalUncutComparisonTrace
    {a : L} (w : GoverningWitness n L data a) :
    List (LabelledComparisonCell n L data hn) :=
  uncutComparisonTraceOfList n L data hn
    (w.globalInitialRows n L data hn)

/-- A comparison cell together with the literal relation/PBW source from
which its horizontal ancestry starts. -/
structure GoverningComparisonCell where
  source : GlobalInitialPacketLabel n L data hn
  cell : LabelledComparisonCell n L data hn

noncomputable instance :
    DecidableEq (GoverningComparisonCell n L data hn) :=
  Classical.decEq _

/-- Source-labelled form of the actual governing comparison trace.  The
root index in `cell.path` and the full source label are both retained. -/
def GoverningWitness.globalLabelledComparisonTrace
    {a : L} (w : GoverningWitness n L data a) :
    List (GoverningComparisonCell n L data hn) :=
  (List.ofFn fun i : Fin (w.globalInitialLabels n L data hn).length ↦
    let initial := (w.globalInitialLabels n L data hn).get i
    (uncutComparisonTrace n L data hn
      (initial.2.row n L data hn) [i.1] initial.1).map fun c ↦
        { source := initial.2, cell := c }).flatten

theorem GoverningWitness.globalUncutCanonicalBoundary_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    canonicalTraceBoundary n L data hn
        (w.globalUncutComparisonTrace n L data hn) = 0 :=
  canonicalTraceBoundary_uncutComparisonTraceOfList_eq_zero
    n L data hn (w.globalInitialRows n L data hn)

end

end LieRings.MetabelianVanishing
