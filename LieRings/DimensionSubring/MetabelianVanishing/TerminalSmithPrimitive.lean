import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmithCollector
import LieRings.DimensionSubring.MetabelianVanishing.TerminalCertificateBridge
import LieRings.PBW.FactorSymbol

/-!
# Full-relation primitives of terminal Smith rows

The terminal Smith collector works in the truncated presentation `D_n → A_n`.
This file gives every Smith row its canonical lift back to the full free model,
without replacing a truncated relation by a pseudo-relation.  At factor two,
the canonical source chain realizes the literal lifted row up to the one
genuine commutator relation required when the ordinary factor lies to the
left of the mark.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalSmithPrimitiveFintype : Fintype L :=
  Fintype.ofFinite L

namespace TerminalSmithRow

/-- Canonical full free-model lift of one terminal ambient Smith vector. -/
def ambientFullLift (i : TerminalSmithIndex n L data hn) : FreeModel n L :=
  terminalSourceGeneratorLift n L
    ((terminalSmith n L data hn).ambientBasis i)

/-- Canonical genuine full relation lifting the marked Smith relation. -/
def relationFullLift (r : TerminalSmithRow n L data hn) :
    Relations n L data :=
  terminalRelationBasisFullLift n L data hn r.mark

/-- UEA word obtained by applying the canonical ambient lift to a list of
terminal Smith indices. -/
def ambientFullWord (xs : List (TerminalSmithIndex n L data hn)) :
    UEA ℤ (FreeModel n L) :=
  (xs.map (fun i ↦ UniversalEnvelopingAlgebra.ι ℤ
    (ambientFullLift n L data hn i))).prod

/-- Literal full-lift realization of a marked terminal Smith row, retaining
the side on which every ordinary factor occurs. -/
def fullLiftValue (r : TerminalSmithRow n L data hn) :
    UEA ℤ (FreeModel n L) :=
  ambientFullWord n L data hn r.left *
    UniversalEnvelopingAlgebra.ι ℤ (r.relationFullLift n L data hn :
      FreeModel n L) *
    ambientFullWord n L data hn r.right

@[simp] theorem prLE_ambientFullLift
    (i : TerminalSmithIndex n L data hn) :
    prLE n L n (by omega) (ambientFullLift n L data hn i) =
      (terminalSmith n L data hn).ambientBasis i := by
  exact LinearMap.congr_fun
    (FreeMetabelian.Free.projectPrefix_prefixIncl
      (X := Generator L) n (by omega))
    ((terminalSmith n L data hn).ambientBasis i)

@[simp] theorem relationPrefix_relationFullLift
    (r : TerminalSmithRow n L data hn) :
    relationPrefix n L data n (by omega)
        (r.relationFullLift n L data hn) =
      ((terminalSmith n L data hn).relationBasis r.mark : A L n) := by
  exact relationPrefix_terminalRelationBasisFullLift
    n L data hn r.mark

end TerminalSmithRow

/-- A bracket of a genuine full relation with an arbitrary full factor is
again a genuine full relation. -/
def terminalSmithFullBracketRelation
    (rho : Relations n L data) (x : FreeModel n L) : Relations n L data :=
  ⟨⁅(rho : FreeModel n L), x⁆, by
    change evaluation n L data ⁅(rho : FreeModel n L), x⁆ = 0
    rw [LieHom.map_lie]
    have hrho : evaluation n L data (rho : FreeModel n L) = 0 :=
      rho.property
    rw [hrho, zero_lie]⟩

/-! ## Identification of the two degree-two PBW symbols -/

/-- On a product of two primitive full-model factors, the manuscript's
adapted-basis symbol followed by `F → A_n` is exactly the basis-independent
degree-two PBW factor symbol computed in the terminal Smith ambient basis.

This is the only comparison with the generic PBW symbol needed by the direct
Smith collector: all of its factor-two leaves have this form. -/
theorem rightSymbol_iota_mul_iota_eq_terminalSmithFactorSymbol
    (x y : FreeModel n L) :
    rightSymbol n L data hn 2 n (by omega)
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ y) =
      LieRings.PBW.factorSymbol
        (terminalSmith n L data hn).ambientBasis 2
        (UniversalEnvelopingAlgebra.ι ℤ
            (prLE n L n (by omega) x) *
          UniversalEnvelopingAlgebra.ι ℤ
            (prLE n L n (by omega) y)) := by
  rw [rightSymbol, LinearMap.comp_apply,
    fullRightSymbol_iota_mul_iota_two,
    LieRings.PBW.factorSymbol_two_iota_mul_iota]
  have hmap := LinearMap.congr_fun
    (SymmetricPower.map_insert (R₀ := ℤ)
      (M₀ := FreeModel n L) (N₀ := A L n)
      (prLE n L n (by omega)) 1 x)
    (SymmetricPower.degreeOne y)
  simpa only [LinearMap.comp_apply, SymmetricPower.map_degreeOne] using hmap

/-- Literal full-model word represented by a finite family of ordered pairs
of primitive factors.  Keeping this domain explicit prevents an invalid
naturality claim for arbitrary higher-factor PBW words. -/
def twoPrimitiveWordRows
    (rows : (FreeModel n L × FreeModel n L) →₀ ℤ) :
    UEA ℤ (FreeModel n L) :=
  rows.sum (fun p z ↦ z •
    (UniversalEnvelopingAlgebra.ι ℤ p.1 *
      UniversalEnvelopingAlgebra.ι ℤ p.2))

/-- The projected terminal-Smith word represented by the same finite family
of two primitive factors. -/
def terminalSmithProjectedTwoPrimitiveWordRows
    (rows : (FreeModel n L × FreeModel n L) →₀ ℤ) :
    UEA ℤ (A L n) :=
  rows.sum (fun p z ↦ z •
    (UniversalEnvelopingAlgebra.ι ℤ
        (prLE n L n (by omega) p.1) *
      UniversalEnvelopingAlgebra.ι ℤ
        (prLE n L n (by omega) p.2)))

/-- Safe linear extension of the degree-two comparison.  The statement is
deliberately restricted to an explicit finite sum of two-primitive words:
exact lower PBW-factor projections are not natural on arbitrary UEA words. -/
theorem rightSymbol_twoPrimitiveWordRows_eq_terminalSmithFactorSymbol
    (rows : (FreeModel n L × FreeModel n L) →₀ ℤ) :
    rightSymbol n L data hn 2 n (by omega)
        (twoPrimitiveWordRows n L rows) =
      LieRings.PBW.factorSymbol
        (terminalSmith n L data hn).ambientBasis 2
        (terminalSmithProjectedTwoPrimitiveWordRows n L rows) := by
  classical
  rw [twoPrimitiveWordRows,
    terminalSmithProjectedTwoPrimitiveWordRows,
    map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, map_zsmul,
    rightSymbol_iota_mul_iota_eq_terminalSmithFactorSymbol]

namespace TerminalSmithFactorTwo

/-- Full relation carried by a factor-two Smith row. -/
def fullRelation (r : TerminalSmithFactorTwo n L data hn) :
    Relations n L data :=
  r.1.relationFullLift n L data hn

/-- Canonical full lift of the unique ordinary factor. -/
def fullFactor (r : TerminalSmithFactorTwo n L data hn) : FreeModel n L :=
  TerminalSmithRow.ambientFullLift n L data hn (r.factor n L data hn)

/-- The genuine relation correction needed to change the literal placement
to the relation-on-the-left source placement. -/
def sourcePlacementCorrection
    (r : TerminalSmithFactorTwo n L data hn) : Relations n L data :=
  if r.1.left = [] then 0 else
    terminalSmithFullBracketRelation n L data
      (r.fullRelation n L data hn) (r.fullFactor n L data hn)

/-- The Smith factor-two chain is literally the generic full-relation chain
for the canonical full relation and canonical full ambient lift. -/
theorem one_eq_fullRelationFactorChain
    (r : TerminalSmithFactorTwo n L data hn) :
    r.one n L data hn =
      terminalFullRelationFactorChain n L data hn
        (r.fullRelation n L data hn) (r.fullFactor n L data hn) := by
  have hrel : fullRelationToD n L data n (by omega)
        (r.fullRelation n L data hn) =
      (terminalSmith n L data hn).relationBasis r.1.mark := by
    apply Subtype.ext
    exact r.1.relationPrefix_relationFullLift n L data hn
  have hamb : prLE n L n (by omega) (r.fullFactor n L data hn) =
      (terminalSmith n L data hn).ambientBasis
        (r.factor n L data hn) := by
    exact TerminalSmithRow.prLE_ambientFullLift n L data hn _
  rw [TerminalSmithFactorTwo.one, terminalFullRelationFactorChain,
    hrel, hamb]

/-- Rowwise primitive realization, valid for both placements of the mark.
The only discrepancy is a whole relation, never a homogeneous tail relabelled
as a relation. -/
theorem terminalSourcePrimitive_one
    (r : TerminalSmithFactorTwo n L data hn) :
    terminalSourcePrimitive n L data hn (r.one n L data hn) =
      pbwPrimitive n L data hn
          (r.1.fullLiftValue n L data hn) +
        (r.sourcePlacementCorrection n L data hn : FreeModel n L) := by
  rw [r.one_eq_fullRelationFactorChain n L data hn,
    terminalSourcePrimitive_fullRelationFactorChain]
  rcases r with ⟨⟨mark, left, right⟩, hcount⟩
  simp only [TerminalSmithRow.factorCount] at hcount
  cases left with
  | nil =>
      simp only [List.length_nil, zero_add] at hcount
      have hright : right.length = 1 := by omega
      obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hright
      simp [TerminalSmithFactorTwo.fullRelation,
        TerminalSmithFactorTwo.fullFactor,
        TerminalSmithFactorTwo.factor,
        TerminalSmithFactorTwo.sourcePlacementCorrection,
        TerminalSmithRow.fullLiftValue,
        TerminalSmithRow.ambientFullWord,
        terminalFullRelationFactorWord]
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
      let rho : Relations n L data :=
        terminalRelationBasisFullLift n L data hn mark
      let x : FreeModel n L :=
        TerminalSmithRow.ambientFullLift n L data hn j
      have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
        (FreeModel n L) (rho : FreeModel n L) x
      simp [terminalFullRelationFactorWord,
        TerminalSmithFactorTwo.fullRelation,
        TerminalSmithFactorTwo.fullFactor,
        TerminalSmithFactorTwo.factor,
        TerminalSmithFactorTwo.sourcePlacementCorrection,
        TerminalSmithRow.relationFullLift,
        TerminalSmithRow.fullLiftValue,
        TerminalSmithRow.ambientFullWord, rho, x] at hswap ⊢
      rw [hswap, map_add]
      have hbracket :
          ⁅UniversalEnvelopingAlgebra.ι ℤ
              (terminalRelationBasisFullLift n L data hn mark :
                FreeModel n L),
            UniversalEnvelopingAlgebra.ι ℤ
              (TerminalSmithRow.ambientFullLift n L data hn j)⁆ =
            UniversalEnvelopingAlgebra.ι ℤ
              ⁅(terminalRelationBasisFullLift n L data hn mark :
                  FreeModel n L),
                TerminalSmithRow.ambientFullLift n L data hn j⁆ :=
        (LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℤ) _ _).symm
      have hprimitive : pbwPrimitive n L data hn
            ⁅UniversalEnvelopingAlgebra.ι ℤ
                (terminalRelationBasisFullLift n L data hn mark :
                  FreeModel n L),
              UniversalEnvelopingAlgebra.ι ℤ
                (TerminalSmithRow.ambientFullLift n L data hn j)⁆ =
          ⁅(terminalRelationBasisFullLift n L data hn mark :
              FreeModel n L),
            TerminalSmithRow.ambientFullLift n L data hn j⁆ := by
        calc
          _ = pbwPrimitive n L data hn
                (UniversalEnvelopingAlgebra.ι ℤ
                  ⁅(terminalRelationBasisFullLift n L data hn mark :
                      FreeModel n L),
                    TerminalSmithRow.ambientFullLift n L data hn j⁆) :=
              congrArg (pbwPrimitive n L data hn) hbracket
          _ = _ := pbwPrimitive_iota n L data hn _
      exact congrArg
        (fun z ↦ pbwPrimitive n L data hn
            (UniversalEnvelopingAlgebra.ι ℤ
                (TerminalSmithRow.ambientFullLift n L data hn j) *
              UniversalEnvelopingAlgebra.ι ℤ
                (terminalRelationBasisFullLift n L data hn mark :
                  FreeModel n L)) + z)
        hprimitive

end TerminalSmithFactorTwo

/-! ## Aggregate factor-two primitive ledger -/

/-- Chain obtained from an arbitrary finite sum of factor-two Smith rows. -/
def terminalSmithFactorTwoChainRows
    (rows : TerminalSmithFactorTwo n L data hn →₀ ℤ) :
    Koszul.One (terminalSmithPresentation n L data hn) 1 :=
  rows.sum (fun r z ↦ z • r.one n L data hn)

/-- Literal full-lift UEA word of the same finite Smith row sum. -/
def terminalSmithFactorTwoFullLiftWordRows
    (rows : TerminalSmithFactorTwo n L data hn →₀ ℤ) :
    UEA ℤ (FreeModel n L) :=
  rows.sum (fun r z ↦ z • r.1.fullLiftValue n L data hn)

/-- Sum of the genuine placement corrections of a finite Smith row sum. -/
def terminalSmithFactorTwoPlacementCorrectionRows
    (rows : TerminalSmithFactorTwo n L data hn →₀ ℤ) :
    Relations n L data :=
  rows.sum (fun r z ↦ z • r.sourcePlacementCorrection n L data hn)

/-- Aggregate source-primitive realization for arbitrary factor-two Smith
rows. -/
theorem terminalSourcePrimitive_terminalSmithFactorTwoChainRows
    (rows : TerminalSmithFactorTwo n L data hn →₀ ℤ) :
    terminalSourcePrimitive n L data hn
        (terminalSmithFactorTwoChainRows n L data hn rows) =
      pbwPrimitive n L data hn
          (terminalSmithFactorTwoFullLiftWordRows n L data hn rows) +
        (terminalSmithFactorTwoPlacementCorrectionRows
          n L data hn rows : FreeModel n L) := by
  classical
  rw [terminalSmithFactorTwoChainRows,
    terminalSmithFactorTwoFullLiftWordRows,
    terminalSmithFactorTwoPlacementCorrectionRows,
    map_finsuppSum, map_finsuppSum]
  change (rows.sum fun a b ↦ terminalSourcePrimitive n L data hn
      (b • a.one n L data hn)) =
    (rows.sum fun a b ↦ pbwPrimitive n L data hn
      (b • a.1.fullLiftValue n L data hn)) +
      (Relations n L data).subtype
        (rows.sum fun r z ↦ z • r.sourcePlacementCorrection n L data hn)
  rw [map_finsuppSum, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul]
  rw [r.terminalSourcePrimitive_one n L data hn, smul_add]
  rfl

/-- Primitive ledger for the actual factor-two frontier of one collected
terminal Smith row. -/
theorem terminalSourcePrimitive_terminalSmithFactorTwoChain
    (r : TerminalSmithRow n L data hn) :
    terminalSourcePrimitive n L data hn
        (terminalSmithFactorTwoChain n L data hn r) =
      pbwPrimitive n L data hn
          (terminalSmithFactorTwoFullLiftWordRows n L data hn
            (terminalSmithFactorTwoFrontier n L data hn r)) +
        (terminalSmithFactorTwoPlacementCorrectionRows n L data hn
          (terminalSmithFactorTwoFrontier n L data hn r) : FreeModel n L) := by
  change terminalSourcePrimitive n L data hn
      (terminalSmithFactorTwoChainRows n L data hn
        (terminalSmithFactorTwoFrontier n L data hn r)) = _
  exact terminalSourcePrimitive_terminalSmithFactorTwoChainRows
    n L data hn (terminalSmithFactorTwoFrontier n L data hn r)

end

end LieRings.MetabelianVanishing
