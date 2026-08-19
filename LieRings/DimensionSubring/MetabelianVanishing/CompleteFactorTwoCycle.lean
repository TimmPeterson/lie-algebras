import LieRings.DimensionSubring.MetabelianVanishing.QuotientWeightCollector
import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmith
import LieRings.DimensionSubring.MetabelianVanishing.ClosedSquare

/-!
# The complete terminal factor-two cycle

This is the factor-number-first terminal read of the manuscript's row
calculation.  The important difference from the raw contextual wall is that a
marked row stops as soon as it reaches factor number two.  Thus every
factor-lowering correction produced above it is retained as a genuine full
relation row before the quotient-weight pass can expose a homogeneous
component.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open TensorProduct
open LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeFactorTwoCycleFintype : Fintype L := Fintype.ofFinite L

/-! ## The stopped second pass -/

/-- The quotient-weight rewrite with the terminal factor-two wall retained.
Only marked rows stop at factor two.  Ordinary rows must continue through the
literal adjacent-swap collector: their commutator children are precisely the
factor-lowering descendants which meet the next wall. -/
noncomputable def completeFactorTwoExpansion :
    QuotientWeightRow n L data →
      Option (List (ℤ × QuotientWeightRow n L data))
  | r@(.ordinary _) => quotientWeightExpansion n L data r
  | r@(.marked left rho s right) =>
      if r.factorCount n L ≤ 2 then none
      else quotientWeightExpansion n L data r

theorem completeFactorTwoExpansion_decreases
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (h : completeFactorTwoExpansion n L data r = some qs) :
    ∀ q ∈ qs, rowMeasureLt (q.2.measure n L data) (r.measure n L data) := by
  cases r with
  | ordinary xs =>
      exact quotientWeightExpansion_decreases n L data h
  | marked left rho s right =>
      simp only [completeFactorTwoExpansion] at h
      split at h
      · contradiction
      · exact quotientWeightExpansion_decreases n L data h

theorem completeFactorTwoExpansion_preserves
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (h : completeFactorTwoExpansion n L data r = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value n L data).sum = r.value n L data := by
  cases r with
  | ordinary xs =>
      exact quotientWeightExpansion_preserves n L data h
  | marked left rho s right =>
      simp only [completeFactorTwoExpansion] at h
      split at h
      · contradiction
      · exact quotientWeightExpansion_preserves n L data h

/-- The deterministic descending-factor collector used for `chi_n`. -/
def completeFactorTwoCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (QuotientWeightRow n L data) (UEA ℤ (FreeModel n L)) where
  relation x y := rowMeasureLt (x.measure n L data) (y.measure n L data)
  wellFounded := InvImage.wf (QuotientWeightRow.measure n L data)
    rowMeasureLt_wellFounded
  expansion := completeFactorTwoExpansion n L data
  value := QuotientWeightRow.value n L data
  decreases := completeFactorTwoExpansion_decreases n L data
  preserves := completeFactorTwoExpansion_preserves n L data

/-- Complete terminal frontier, starting after the triangular factor pass. -/
def GoverningWitness.completeFactorTwoFrontier {a : L}
    (w : GoverningWitness n L data a) :
    QuotientWeightRow n L data →₀ ℤ :=
  (w.quotientWeightInitial n L data).sum (fun r z ↦
    z • (completeFactorTwoCollector n L data).normalForm r)

theorem GoverningWitness.evaluate_completeFactorTwoFrontier {a : L}
    (w : GoverningWitness n L data a) :
    (completeFactorTwoCollector n L data).evaluate
        (w.completeFactorTwoFrontier n L data) = w.theta := by
  classical
  rw [GoverningWitness.completeFactorTwoFrontier, map_finsuppSum]
  calc
    _ = (quotientWeightCollector n L data).evaluate
        (w.quotientWeightInitial n L data) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul,
        (completeFactorTwoCollector n L data).evaluate_normalForm]
      rfl
    _ = w.theta := w.evaluate_quotientWeightInitial n L data

/-! ## Genuine factor-two rows -/

/-- A stopped row with one full relation and one ordinary homogeneous factor. -/
abbrev CompleteFactorTwoRow :=
  {r : QuotientWeightRow n L data //
    match r with
    | .ordinary _ => False
    | .marked _ _ _ _ => r.factorCount n L = 2}

namespace CompleteFactorTwoRow

/-- The unique ordinary factor of a complete factor-two row. -/
def factor (r : CompleteFactorTwoRow n L data) :
    TriangularPBWIndex n L :=
  match hr : r.1 with
  | .ordinary _ => by
      have hfalse : False := by simpa [hr] using r.property
      exact hfalse.elim
  | .marked left _ _ right =>
      (left ++ right).get ⟨0, by
        have hcount := r.property
        simp only [hr, QuotientWeightRow.factorCount] at hcount
        simp only [List.length_append]
        omega⟩

/-- The genuine full relation carried by the stopped row. -/
def relation (r : CompleteFactorTwoRow n L data) : Relations n L data :=
  match hr : r.1 with
  | .ordinary _ => by
      have hfalse : False := by simpa [hr] using r.property
      exact hfalse.elim
  | .marked _ rho _ _ => rho

/-- One complete factor-two row in the terminal Koszul presentation. -/
def one (r : CompleteFactorTwoRow n L data) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  fullRelationToD n L data n (by omega) (r.relation n L data) ⊗ₜ[ℤ]
    SymmetricPower.degreeOne
      (prLE n L n (by omega)
        (triangularPBWBasis n L data (r.factor n L data)))

end CompleteFactorTwoRow

/-- Keep precisely the genuine marked factor-two rows. -/
def completeFactorTwoPart (r : QuotientWeightRow n L data) :
    CompleteFactorTwoRow n L data →₀ ℤ :=
  match hr : r with
  | .ordinary _ => 0
  | .marked _ _ _ _ =>
      if htwo : r.factorCount n L = 2 then
        Finsupp.single ⟨r, by simpa [hr] using htwo⟩ 1
      else 0

/-- The full signed factor-two row list after all higher factor corrections
have been appended and collected. -/
def GoverningWitness.completeFactorTwoRows {a : L}
    (w : GoverningWitness n L data a) :
    CompleteFactorTwoRow n L data →₀ ℤ :=
  (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
    z • completeFactorTwoPart n L data r)

/-- The manuscript's complete terminal chain `chi_n`. -/
def GoverningWitness.completeFactorTwoChain {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (w.completeFactorTwoRows n L data).sum (fun r z ↦
    z • r.one n L data hn)

end

end LieRings.MetabelianVanishing
