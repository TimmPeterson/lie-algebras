import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoCycle

/-!
# The stopped-tail correction at factor two

A stopped quotient-weight row is evaluated with `rowTail s rho`, not with the
whole relation `rho`.  Consequently its Koszul row, whose relation entry must
be a genuine full relation, has one explicit extra boundary term.  This file
records that term and rules out the invalid per-row replacement
`rowTail s rho = rho`.

The global cycle proof must identify the signed sum of these prefix terms with
the factor-two descendants of the ordinary truncation branches.  That is the
trace-cell/Stokes step; it cannot be recovered from the terminal marked rows
alone after their provenance has been erased.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open TensorProduct

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeTailCorrectionFintype : Fintype L := Fintype.ofFinite L

/-! ## Exact symbols of a primitive product -/

/-- The terminal factor-two symbol of two primitive factors. -/
theorem rightSymbol_iota_mul_iota_two
    (x y : FreeModel n L) :
    rightSymbol n L data hn 2 n (by omega)
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ y) =
      SymmetricPower.insert ℤ (A L n) 1
        (prLE n L n (by omega) x)
        (SymmetricPower.degreeOne (prLE n L n (by omega) y)) := by
  rw [rightSymbol, LinearMap.comp_apply,
    fullRightSymbol_iota_mul_iota_two]
  have hmap := LinearMap.congr_fun
    (SymmetricPower.map_insert (R₀ := ℤ)
      (M₀ := FreeModel n L) (N₀ := A L n)
      (prLE n L n (by omega)) 1 x)
    (SymmetricPower.degreeOne y)
  simpa only [LinearMap.comp_apply, SymmetricPower.map_degreeOne] using hmap

/-- The same symbol with the two primitive factors interchanged. -/
theorem rightSymbol_iota_mul_iota_two_comm
    (x y : FreeModel n L) :
    rightSymbol n L data hn 2 n (by omega)
        (UniversalEnvelopingAlgebra.ι ℤ y *
          UniversalEnvelopingAlgebra.ι ℤ x) =
      SymmetricPower.insert ℤ (A L n) 1
        (prLE n L n (by omega) x)
        (SymmetricPower.degreeOne (prLE n L n (by omega) y)) := by
  rw [rightSymbol_iota_mul_iota_two n L data hn]
  have hcomm := LinearMap.congr_fun
    (SymmetricPower.insert_comm (R₀ := ℤ) (M₀ := A L n) 0
      (prLE n L n (by omega) y)
      (prLE n L n (by omega) x))
    (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i))
  have hinsertZero (z : A L n) :
      SymmetricPower.insert ℤ (A L n) 0 z
          (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i)) =
        SymmetricPower.degreeOne z := by
    rw [SymmetricPower.degreeOne_apply, SymmetricPower.insert_tprod]
    congr
    funext i
    exact Fin.elim0 i
  change SymmetricPower.insert ℤ (A L n) 1
      (prLE n L n (by omega) y)
      (SymmetricPower.insert ℤ (A L n) 0
        (prLE n L n (by omega) x)
        (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i))) =
    SymmetricPower.insert ℤ (A L n) 1
      (prLE n L n (by omega) x)
      (SymmetricPower.insert ℤ (A L n) 0
        (prLE n L n (by omega) y)
        (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i))) at hcomm
  rw [hinsertZero, hinsertZero] at hcomm
  exact hcomm

/-! ## The local stopped-tail defect -/

/-- The symmetric factor-two symbol actually carried by a stopped tail. -/
def stoppedTailSymbol
    (rho : Relations n L data) (s : Fin (n + 2))
    (v : TriangularPBWIndex n L) : Sym[ℤ] (Fin 2) (A L n) :=
  SymmetricPower.insert ℤ (A L n) 1
    (prLE n L n (by omega)
      (rowTail n L s.val (by omega) (rho : FreeModel n L)))
    (SymmetricPower.degreeOne
      (prLE n L n (by omega) (triangularPBWBasis n L data v)))

/-- The missing prefix term introduced when a stopped tail is incorrectly
replaced by its full relation. -/
def stoppedTailPrefixCorrection
    (rho : Relations n L data) (s : Fin (n + 2))
    (v : TriangularPBWIndex n L) : Sym[ℤ] (Fin 2) (A L n) :=
  SymmetricPower.insert ℤ (A L n) 1
    (prLE n L n (by omega)
      (rowTruncation n L s.val (by omega) (rho : FreeModel n L)))
    (SymmetricPower.degreeOne
      (prLE n L n (by omega) (triangularPBWBasis n L data v)))

/-- Exact local correction formula: full-relation boundary equals the actual
tail symbol plus the omitted prefix symbol. -/
theorem fullRelationFactorSymbol_eq_tail_add_prefix
    (rho : Relations n L data) (s : Fin (n + 2))
    (v : TriangularPBWIndex n L) :
    SymmetricPower.insert ℤ (A L n) 1
        (prLE n L n (by omega) (rho : FreeModel n L))
        (SymmetricPower.degreeOne
          (prLE n L n (by omega) (triangularPBWBasis n L data v))) =
      stoppedTailSymbol n L data rho s v +
        stoppedTailPrefixCorrection n L data rho s v := by
  have hsplit : (rho : FreeModel n L) =
      rowTail n L s.val (by omega) (rho : FreeModel n L) +
        rowTruncation n L s.val (by omega) (rho : FreeModel n L) := by
    rw [rowTail, LinearMap.sub_apply, LinearMap.id_apply]
    abel
  rw [hsplit, map_add, SymmetricPower.insert_add_apply]
  rfl

/-- The genuine Koszul row attached to a full relation and one triangular
factor. -/
def fullRelationFactorChain
    (rho : Relations n L data) (v : TriangularPBWIndex n L) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  fullRelationToD n L data n (by omega) rho ⊗ₜ[ℤ]
    SymmetricPower.degreeOne
      (prLE n L n (by omega) (triangularPBWBasis n L data v))

/-- This is the corrected per-cell boundary statement.  Its second summand is
indispensable unless the stored full relation still belongs to the declared
tail. -/
theorem dOne_fullRelationFactorChain_eq_tail_add_prefix
    (rho : Relations n L data) (s : Fin (n + 2))
    (v : TriangularPBWIndex n L) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (fullRelationFactorChain n L data hn rho v) =
      stoppedTailSymbol n L data rho s v +
        stoppedTailPrefixCorrection n L data rho s v := by
  rw [fullRelationFactorChain, Koszul.dOne_tmul]
  change SymmetricPower.insert ℤ (A L n) 1
      (prLE n L n (by omega) (rho : FreeModel n L))
      (SymmetricPower.degreeOne
        (prLE n L n (by omega) (triangularPBWBasis n L data v))) = _
  exact fullRelationFactorSymbol_eq_tail_add_prefix n L data rho s v

/-- The familiar uncorrected formula is valid precisely under the invariant
available at an initial triangular row: the full relation itself lies in the
stored tail.  A quotient-weight truncation does not preserve this invariant. -/
theorem stoppedTailPrefixCorrection_eq_zero_of_mem_tail
    (rho : Relations n L data) (s : Fin (n + 2))
    (v : TriangularPBWIndex n L)
    (hrho : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) s.val) :
    stoppedTailPrefixCorrection n L data rho s v = 0 := by
  have htail := rowTail_eq_of_mem_tail n L
    (rho : FreeModel n L) s.val (by omega) hrho
  have htrunc : rowTruncation n L s.val (by omega)
      (rho : FreeModel n L) = 0 := by
    rw [rowTail, LinearMap.sub_apply, LinearMap.id_apply] at htail
    exact sub_eq_self.mp htail
  rw [stoppedTailPrefixCorrection, htrunc, map_zero]
  simp

/-- For a relation-left stopped row, its actual factor-two PBW symbol is the
tail symbol, not the full-relation symbol. -/
theorem rightSymbol_stopped_relationLeft
    (rho : Relations n L data) (s : Fin (n + 2))
    (v : TriangularPBWIndex n L) :
    rightSymbol n L data hn 2 n (by omega)
        ((QuotientWeightRow.marked [] rho s [v] :
          QuotientWeightRow n L data).value n L data) =
      stoppedTailSymbol n L data rho s v := by
  simp only [QuotientWeightRow.value, QuotientWeightRow.basisWord,
    LieRings.PBW.basisWord, LieRings.PBW.word, List.map_nil,
    List.prod_nil, List.map_singleton, List.prod_singleton, one_mul]
  exact rightSymbol_iota_mul_iota_two n L data hn _ _

/-- For a relation-right stopped row, commutativity of the symmetric symbol
gives the same tail symbol. -/
theorem rightSymbol_stopped_relationRight
    (rho : Relations n L data) (s : Fin (n + 2))
    (v : TriangularPBWIndex n L) :
    rightSymbol n L data hn 2 n (by omega)
        ((QuotientWeightRow.marked [v] rho s [] :
          QuotientWeightRow n L data).value n L data) =
      stoppedTailSymbol n L data rho s v := by
  simp only [QuotientWeightRow.value, QuotientWeightRow.basisWord,
    LieRings.PBW.basisWord, LieRings.PBW.word, List.map_nil,
    List.prod_nil, List.map_singleton, List.prod_singleton, one_mul,
    mul_one]
  exact rightSymbol_iota_mul_iota_two_comm n L data hn _ _

/-! ## Ordinary rows must still be collected -/

/-- Corrected stopped expansion: only marked factor-two rows stop.  Ordinary
rows continue through the already verified PBW adjacent-swap collector, so
their factor-lowering commutator descendants are not discarded. -/
noncomputable def completeFactorTwoExpansionWithOrdinary :
    QuotientWeightRow n L data →
      Option (List (ℤ × QuotientWeightRow n L data))
  | r@(.ordinary _) => quotientWeightExpansion n L data r
  | r@(.marked _ _ _ _) =>
      if r.factorCount n L ≤ 2 then none
      else quotientWeightExpansion n L data r

theorem completeFactorTwoExpansionWithOrdinary_decreases
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (h : completeFactorTwoExpansionWithOrdinary n L data r = some qs) :
    ∀ q ∈ qs, rowMeasureLt (q.2.measure n L data) (r.measure n L data) := by
  cases r with
  | ordinary xs =>
      exact quotientWeightExpansion_decreases n L data h
  | marked left rho s right =>
      simp only [completeFactorTwoExpansionWithOrdinary] at h
      split at h
      · contradiction
      · exact quotientWeightExpansion_decreases n L data h

theorem completeFactorTwoExpansionWithOrdinary_preserves
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (h : completeFactorTwoExpansionWithOrdinary n L data r = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value n L data).sum = r.value n L data := by
  cases r with
  | ordinary xs =>
      exact quotientWeightExpansion_preserves n L data h
  | marked left rho s right =>
      simp only [completeFactorTwoExpansionWithOrdinary] at h
      split at h
      · contradiction
      · exact quotientWeightExpansion_preserves n L data h

end

end LieRings.MetabelianVanishing
