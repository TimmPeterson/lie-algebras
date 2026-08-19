import LieRings.DimensionSubring.MetabelianVanishing.TerminalPacketAssembly
import LieRings.DimensionSubring.MetabelianVanishing.TerminalTransport

/-!
# The terminal trace-to-certificate bridge

The descending factor collector produces a genuine cycle in the canonical
terminal presentation.  Its realization calculation has one precise output:
after mapping that cycle to the Smith block, the difference between the
canonical block word and the complete external word is the sum of a whole
full relation and a word whose complete one-factor PBW projection is zero.

This file is the deliberately minimal consumer of that calculation.  It does
not construct the cycle and it does not assert that the raw contextual wall is
closed.  It merely turns the aggregate realization equation into the
`TerminalRowCertificate` required by `TerminalPacketAssembly`.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalCertificateBridgeFintype : Fintype L := Fintype.ofFinite L

/-- A fixed strict comparison map from the canonical terminal presentation to
the quadratic Smith-block presentation.  It induces the identity of `W_n`;
all dependence on its projective lifts is handled by the realization-defect
part of the complete trace. -/
def terminalComparisonHom :
    Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id :=
  Koszul.Presentation.liftHom
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega)) LinearMap.id

/-- A marked realization-error word whose complete factor-one PBW projection
vanishes.  This local definition avoids imposing any stronger, weightwise
vanishing statement on the collector. -/
def terminalZeroFactorOneMarkedWord
    (noise : UEA ℤ (FreeModel n L))
    (hnoise :
      (adaptedWeightedBasis n L data hn).factorProj 1 noise = 0) :
    TerminalMarkedWord n L data hn where
  word := noise
  primitive := 0
  projection_eq := by
    rw [hnoise]
    exact (map_zero
      (UniversalEnvelopingAlgebra.ι ℤ :
        LieHom ℤ (FreeModel n L) (UEA ℤ (FreeModel n L)))).symm

/-- A whole full relation and factor-one-invisible noise are precisely the
two aggregate discrepancies that the terminal realization calculation may
discard. -/
theorem terminalCertificateOfRelationAndNoise
    (u v : TerminalMarkedWord n L data hn)
    (rho : Relations n L data)
    (noise : UEA ℤ (FreeModel n L))
    (hnoise :
      (adaptedWeightedBasis n L data hn).factorProj 1 noise = 0)
    (hword :
      (v.add n L data hn
        (terminalZeroFactorOneMarkedWord n L data hn noise hnoise)).word =
        u.word + UniversalEnvelopingAlgebra.ι ℤ
          (rho : FreeModel n L)) :
    TerminalRowCertificate n L data hn u v := by
  let zeroNoise := terminalZeroFactorOneMarkedWord
    n L data hn noise hnoise
  let vNoise := v.add n L data hn zeroNoise
  have hrel : TerminalRowCertificate n L data hn u vNoise :=
    TerminalRowCertificate.relationCorrection rho 1 (by
      simpa only [one_zsmul] using hword)
  have hdrop : TerminalRowCertificate n L data hn vNoise
      (v.add n L data hn (TerminalMarkedWord.zero n L data hn)) :=
    TerminalRowCertificate.add (TerminalRowCertificate.refl v)
      (TerminalRowCertificate.zeroFactorOne hnoise)
  have hzero : TerminalRowCertificate n L data hn
      (v.add n L data hn (TerminalMarkedWord.zero n L data hn)) v :=
    TerminalRowCertificate.basisExpansion (by simp)
  exact TerminalRowCertificate.trans hrel
    (TerminalRowCertificate.trans hdrop hzero)

/-- A two-stage version matching the proof architecture.  The collector first
compares the external word with an arbitrary literal source placement; the
presentation-realization calculation then compares that source placement with
the mapped block word.  Whole relations and factor-one-invisible errors are
combined only after both equalities have been proved. -/
theorem terminalCertificateOfTraceAndRealizationEquations
    (u v : TerminalMarkedWord n L data hn)
    (sourceWord : UEA ℤ (FreeModel n L))
    (traceRelation realizationRelation : Relations n L data)
    (traceNoise realizationNoise : UEA ℤ (FreeModel n L))
    (htraceNoise :
      (adaptedWeightedBasis n L data hn).factorProj 1 traceNoise = 0)
    (hrealizationNoise :
      (adaptedWeightedBasis n L data hn).factorProj 1 realizationNoise = 0)
    (htrace : sourceWord + traceNoise =
      u.word + UniversalEnvelopingAlgebra.ι ℤ
        (traceRelation : FreeModel n L))
    (hrealization : v.word + realizationNoise =
      sourceWord + UniversalEnvelopingAlgebra.ι ℤ
        (realizationRelation : FreeModel n L)) :
    TerminalRowCertificate n L data hn u v := by
  have hnoise : (adaptedWeightedBasis n L data hn).factorProj 1
      (realizationNoise + traceNoise) = 0 := by
    rw [map_add, hrealizationNoise, htraceNoise, add_zero]
  apply terminalCertificateOfRelationAndNoise n L data hn u v
    (traceRelation + realizationRelation)
    (realizationNoise + traceNoise) hnoise
  change v.word + (realizationNoise + traceNoise) =
    u.word + UniversalEnvelopingAlgebra.ι ℤ
      ((traceRelation + realizationRelation : Relations n L data) :
        FreeModel n L)
  rw [show v.word + (realizationNoise + traceNoise) =
      (v.word + realizationNoise) + traceNoise by abel,
    hrealization]
  rw [show sourceWord +
        UniversalEnvelopingAlgebra.ι ℤ
            (realizationRelation : FreeModel n L) + traceNoise =
      (sourceWord + traceNoise) +
        UniversalEnvelopingAlgebra.ι ℤ
          (realizationRelation : FreeModel n L) by abel,
    htrace]
  change u.word + UniversalEnvelopingAlgebra.ι ℤ
      (traceRelation : FreeModel n L) +
        UniversalEnvelopingAlgebra.ι ℤ
          (realizationRelation : FreeModel n L) =
    u.word + UniversalEnvelopingAlgebra.ι ℤ
      ((traceRelation : FreeModel n L) +
        (realizationRelation : FreeModel n L))
  rw [map_add]
  abel

/-- The form used when the realization calculation lands first in the raw
relation-on-the-left block orientation.  The already verified finite Smith
interchange then supplies the final four-family orientation. -/
theorem terminalCertificateOfRawTraceAndRealizationEquations
    (external : TerminalMarkedWord n L data hn)
    (blockCycle : Koszul.cyclesOne
      (rPresentation n L data (by omega)) 1)
    (sourceWord : UEA ℤ (FreeModel n L))
    (traceRelation realizationRelation : Relations n L data)
    (traceNoise realizationNoise : UEA ℤ (FreeModel n L))
    (htraceNoise :
      (adaptedWeightedBasis n L data hn).factorProj 1 traceNoise = 0)
    (hrealizationNoise :
      (adaptedWeightedBasis n L data hn).factorProj 1 realizationNoise = 0)
    (htrace : sourceWord + traceNoise =
      external.word + UniversalEnvelopingAlgebra.ι ℤ
        (traceRelation : FreeModel n L))
    (hrealization :
      (terminalBlockCanonicalRawMarkedWord
          n L data hn blockCycle).word + realizationNoise =
        sourceWord + UniversalEnvelopingAlgebra.ι ℤ
          (realizationRelation : FreeModel n L)) :
    TerminalRowCertificate n L data hn external
      (quadraticBlockMarkedWord n L data hn blockCycle) := by
  exact TerminalRowCertificate.trans
    (terminalCertificateOfTraceAndRealizationEquations
      n L data hn external
      (terminalBlockCanonicalRawMarkedWord n L data hn blockCycle)
      sourceWord traceRelation realizationRelation traceNoise
      realizationNoise htraceNoise hrealizationNoise htrace hrealization)
    (terminalBlockCanonicalRawCertificate n L data hn blockCycle)

/-! ## Canonical source-placement primitives -/

/-- Complete PBW primitive of the literal relation-on-the-left realization of
a chain in the canonical terminal presentation. -/
def terminalSourcePrimitive :
    Koszul.One (terminalSourcePresentation n L data hn) 1 →ₗ[ℤ]
      FreeModel n L :=
  (pbwPrimitive n L data hn).comp
    (terminalSourcePlacedWord n L data hn)

@[simp] theorem terminalSourcePrimitive_apply
    (x : Koszul.One (terminalSourcePresentation n L data hn) 1) :
    terminalSourcePrimitive n L data hn x =
      pbwPrimitive n L data hn
        (terminalSourcePlacedWord n L data hn x) := rfl

/-! ## Canonical remainders for the literal source and block placements -/

/-- A homogeneous top-weight input brackets trivially with every element of
the truncated free model: every possible bracket weight lies beyond the
class cutoff. -/
theorem bracket_weightIncl_top_eq_zero
    (top : FreeMetabelian.Piece (Generator L) n)
    (x : FreeModel n L) :
    ⁅FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
      n (by omega) top, x⁆ = 0 := by
  rw [← FreeMetabelian.Free.sum_incl_project x, lie_sum]
  apply Finset.sum_eq_zero
  intro i hi
  funext k
  exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
    n i.val (by omega) i.isLt top
      (FreeMetabelian.Free.weightProject i.val i.isLt x) k (by
        intro h
        have hk := k.isLt
        omega)

/-- A product with an arbitrary first factor and a homogeneous top-weight
second factor has no complete factor-one PBW component. -/
theorem factorProj_one_mul_iota_weightIncl_top_eq_zero
    (x : FreeModel n L)
    (top : FreeMetabelian.Piece (Generator L) n) :
    (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ x *
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
            n (by omega) top)) = 0 := by
  rw [← FreeMetabelian.Free.sum_incl_project x, map_sum,
    Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hin : i.val = n
  · have hieq : i = ⟨n, by omega⟩ := Fin.ext hin
    rw [hieq]
    simpa only [FreeMetabelian.Free.weightIncl,
      FreeMetabelian.Free.weightProject] using
      (adapted_factorProj_one_iota_derived_mul_derived
      n L data hn n n (by omega) (by omega) (by omega) (by omega)
        (FreeMetabelian.Free.weightProject n (by omega) x) top)
  · exact adapted_factorProj_one_iota_weightIncl_mul_of_lt
      n L data hn i.val n i.isLt (by omega) (by omega)
        (FreeMetabelian.Free.weightProject i.val i.isLt x) top

/-- The reversed product with a homogeneous top-weight first factor is also
factor-one invisible.  The interchange correction is zero by the cutoff
lemma above. -/
theorem factorProj_one_iota_weightIncl_top_mul_eq_zero
    (top : FreeMetabelian.Piece (Generator L) n)
    (x : FreeModel n L) :
    (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
            n (by omega) top) *
        UniversalEnvelopingAlgebra.ι ℤ x) = 0 := by
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
    (FreeModel n L)
      (FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
        n (by omega) top) x
  rw [bracket_weightIncl_top_eq_zero n L top x, map_zero, add_zero] at hswap
  rw [hswap]
  exact factorProj_one_mul_iota_weightIncl_top_eq_zero
    n L data hn x top

/-- In a free model truncated after the top coordinate, equality of the first
`n` coordinates says exactly that the difference is the included top
coordinate. -/
theorem sub_eq_weightIncl_top_of_projectPrefix_eq
    (x y : FreeModel n L)
    (hprefix : FreeMetabelian.Free.projectPrefix n (by omega) x =
      FreeMetabelian.Free.projectPrefix n (by omega) y) :
    x - y = FreeMetabelian.Free.weightIncl
      (X := Generator L) (c := n + 1) n (by omega)
        (FreeMetabelian.Free.weightProject n (by omega) (x - y)) := by
  funext i
  by_cases hin : i.val = n
  · have hieq : i = ⟨n, by omega⟩ := Fin.ext hin
    rw [hieq]
    exact (FreeMetabelian.Free.incl_apply_same
      (⟨n, by omega⟩ : Fin (n + 1)) _).symm
  · have hi : i.val < n := by omega
    have hp := congrFun hprefix ⟨i.val, hi⟩
    change x i = y i at hp
    rw [Pi.sub_apply, hp, sub_self]
    exact (FreeMetabelian.Free.incl_apply_of_ne
      (⟨n, by omega⟩ : Fin (n + 1)) i (by
        intro heq
        exact hin (congrArg Fin.val heq)) _).symm

/-- A degree-one pure symmetric tensor is read by the source-placement map as
the literal prefix inclusion of its entry. -/
@[simp] theorem terminalSourceSymOneLift_tprod
    (x : A L n) :
    terminalSourceSymOneLift n L
        (SymmetricPower.tprod ℤ (fun _ : Fin 1 ↦ x)) =
      terminalSourceGeneratorLift n L x := by
  have htprod : SymmetricPower.tprod ℤ (fun _ : Fin 1 ↦ x) =
      SymmetricPower.degreeOne (R := ℤ) x := by
    rw [SymmetricPower.degreeOne_apply]
    congr 1
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [htprod]
  change terminalSourceGeneratorLift n L
      ((SymmetricPower.degreeOneLinearEquiv (prefixBasis L n))
        (SymmetricPower.degreeOne (R := ℤ) x)) = _
  rw [SymmetricPower.degreeOneLinearEquiv_degreeOne]

/-- Canonical terminal source chain attached to a genuine full relation and
one displayed free-model factor.  This is the row shape used by every leaf of
the mark-one full-label correction. -/
def terminalFullRelationFactorChain
    (rho : Relations n L data) (x : FreeModel n L) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  fullRelationToD n L data n (by omega) rho ⊗ₜ[ℤ]
    SymmetricPower.degreeOne (prLE n L n (by omega) x)

/-- Literal relation-on-the-left word represented by a full-relation factor
chain before the canonical source lifts are chosen. -/
def terminalFullRelationFactorWord
    (rho : Relations n L data) (x : FreeModel n L) :
    UEA ℤ (FreeModel n L) :=
  UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
    UniversalEnvelopingAlgebra.ι ℤ x

/-- Choosing the canonical source lifts changes a genuine full-relation
factor row only by products containing a homogeneous top piece.  Consequently
its complete PBW primitive is exactly the primitive of the literal
relation-on-the-left word. -/
theorem terminalSourcePrimitive_fullRelationFactorChain
    (rho : Relations n L data) (x : FreeModel n L) :
    terminalSourcePrimitive n L data hn
        (terminalFullRelationFactorChain n L data hn rho x) =
      pbwPrimitive n L data hn
        (terminalFullRelationFactorWord n L data rho x) := by
  let d : D n L data n (by omega) :=
    fullRelationToD n L data n (by omega) rho
  let liftR : FreeModel n L := terminalFullLift n L data hn d
  let liftF : FreeModel n L := terminalSourceGeneratorLift n L
    (prLE n L n (by omega) x)
  have hsource : terminalSourcePlacedWord n L data hn
        (terminalFullRelationFactorChain n L data hn rho x) =
      UniversalEnvelopingAlgebra.ι ℤ liftR *
        UniversalEnvelopingAlgebra.ι ℤ liftF := by
    rw [terminalFullRelationFactorChain,
      terminalSourcePlacedWord_tmul]
    change UniversalEnvelopingAlgebra.ι ℤ liftR *
        UniversalEnvelopingAlgebra.ι ℤ
          (terminalSourceSymOneLift n L
            (SymmetricPower.degreeOne (R := ℤ)
              (prLE n L n (by omega) x))) = _
    rw [show SymmetricPower.degreeOne (R := ℤ)
        (prLE n L n (by omega) x) =
      SymmetricPower.tprod ℤ
        (fun _ : Fin 1 ↦ prLE n L n (by omega) x) by
      rw [SymmetricPower.degreeOne_apply]
      congr 1
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i,
      terminalSourceSymOneLift_tprod]
  have hliftPrefix : FreeMetabelian.Free.projectPrefix n (by omega) liftR =
      FreeMetabelian.Free.projectPrefix n (by omega) (rho : FreeModel n L) := by
    exact congrArg Subtype.val (terminalFullLift_prefix n L data hn d)
  let topR : FreeMetabelian.Piece (Generator L) n :=
    FreeMetabelian.Free.weightProject n (by omega)
      (liftR - (rho : FreeModel n L))
  have hliftR : liftR = (rho : FreeModel n L) +
      FreeMetabelian.Free.weightIncl n (by omega) topR := by
    have htop := sub_eq_weightIncl_top_of_projectPrefix_eq
      n L liftR (rho : FreeModel n L) hliftPrefix
    change liftR - (rho : FreeModel n L) =
      FreeMetabelian.Free.weightIncl n (by omega) topR at htop
    calc
      liftR = (liftR - (rho : FreeModel n L)) + (rho : FreeModel n L) := by
        abel
      _ = FreeMetabelian.Free.weightIncl n (by omega) topR +
          (rho : FreeModel n L) := by rw [htop]
      _ = _ := add_comm _ _
  have hliftFPrefix : FreeMetabelian.Free.projectPrefix n (by omega) liftF =
      FreeMetabelian.Free.projectPrefix n (by omega) x := by
    change FreeMetabelian.Free.projectPrefix n (by omega)
        (FreeMetabelian.Free.prefixIncl n (by omega)
          (FreeMetabelian.Free.projectPrefix n (by omega) x)) =
      FreeMetabelian.Free.projectPrefix n (by omega) x
    exact LinearMap.congr_fun
      (FreeMetabelian.Free.projectPrefix_prefixIncl
        (X := Generator L) n (by omega)) _
  let topF : FreeMetabelian.Piece (Generator L) n :=
    FreeMetabelian.Free.weightProject n (by omega) (x - liftF)
  have hliftF : liftF = x -
      FreeMetabelian.Free.weightIncl n (by omega) topF := by
    have htop := sub_eq_weightIncl_top_of_projectPrefix_eq
      n L x liftF hliftFPrefix.symm
    change x - liftF =
      FreeMetabelian.Free.weightIncl n (by omega) topF at htop
    calc
      liftF = x - (x - liftF) := by abel
      _ = x - FreeMetabelian.Free.weightIncl n (by omega) topF := by
        rw [htop]
  change pbwPrimitive n L data hn
      (terminalSourcePlacedWord n L data hn
        (terminalFullRelationFactorChain n L data hn rho x)) =
    pbwPrimitive n L data hn
      (terminalFullRelationFactorWord n L data rho x)
  apply LieRings.PBW.canonicalMap_injective_of_freeModulePBW
    ℤ (FreeModel n L) (AdaptedIndex n L data hn)
    (adaptedWeightedBasis n L data hn).basis
    (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis)
  rw [← factorProj_one_eq_iota_pbwPrimitive n L data hn,
    ← factorProj_one_eq_iota_pbwPrimitive n L data hn]
  change (adaptedWeightedBasis n L data hn).factorProj 1
      (terminalSourcePlacedWord n L data hn
        (terminalFullRelationFactorChain n L data hn rho x)) =
    (adaptedWeightedBasis n L data hn).factorProj 1
      (terminalFullRelationFactorWord n L data rho x)
  rw [hsource, terminalFullRelationFactorWord, hliftR, hliftF,
    map_add, map_sub, add_mul, mul_sub, map_add, map_sub]
  rw [mul_sub, map_sub]
  rw [factorProj_one_iota_weightIncl_top_mul_eq_zero
      n L data hn topR x,
    factorProj_one_mul_iota_weightIncl_top_eq_zero
      n L data hn (rho : FreeModel n L) topF,
    factorProj_one_iota_weightIncl_top_mul_eq_zero
      n L data hn topR
        (FreeMetabelian.Free.weightIncl n (by omega) topF)]
  simp

/-- Finite sum of genuine full-relation/one-factor source rows. -/
def terminalFullRelationFactorChainRows
    (rows : (Relations n L data × FreeModel n L) →₀ ℤ) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  rows.sum (fun p z ↦ z •
    terminalFullRelationFactorChain n L data hn p.1 p.2)

/-- Literal UEA realization of the same finite relation-on-the-left row
list. -/
def terminalFullRelationFactorWordRows
    (rows : (Relations n L data × FreeModel n L) →₀ ℤ) :
    UEA ℤ (FreeModel n L) :=
  rows.sum (fun p z ↦ z •
    terminalFullRelationFactorWord n L data p.1 p.2)

/-- Aggregate source-placement theorem for any finite list of genuine
full-relation/one-factor rows. -/
theorem terminalSourcePrimitive_fullRelationFactorChainRows
    (rows : (Relations n L data × FreeModel n L) →₀ ℤ) :
    terminalSourcePrimitive n L data hn
        (terminalFullRelationFactorChainRows n L data hn rows) =
      pbwPrimitive n L data hn
        (terminalFullRelationFactorWordRows n L data rows) := by
  classical
  rw [terminalFullRelationFactorChainRows,
    terminalFullRelationFactorWordRows, map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, map_zsmul,
    terminalSourcePrimitive_fullRelationFactorChain]

/-- The unique aggregate remainder which turns a literal source word into an
external marked word plus one genuine full relation.  This is only a
definition in the enveloping algebra; the theorem below proves that it has no
complete factor-one component from the corresponding primitive identity. -/
def terminalTraceRemainder
    (external : TerminalMarkedWord n L data hn)
    (sourceWord : UEA ℤ (FreeModel n L))
    (rho : Relations n L data) : UEA ℤ (FreeModel n L) :=
  external.word + UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) -
    sourceWord

@[simp] theorem terminalTraceRemainder_equation
    (external : TerminalMarkedWord n L data hn)
    (sourceWord : UEA ℤ (FreeModel n L))
    (rho : Relations n L data) :
    sourceWord + terminalTraceRemainder n L data hn external sourceWord rho =
      external.word + UniversalEnvelopingAlgebra.ι ℤ
        (rho : FreeModel n L) := by
  unfold terminalTraceRemainder
  abel

/-- A primitive identity modulo a *whole* relation proves that the canonical
trace remainder has zero complete factor-one PBW projection.  Notice that the
relation argument has type `Relations`; no homogeneous tail is accepted by
this interface. -/
theorem terminalTraceRemainder_factorProj_one_eq_zero
    (external : TerminalMarkedWord n L data hn)
    (sourceWord : UEA ℤ (FreeModel n L))
    (rho : Relations n L data)
    (hprimitive : pbwPrimitive n L data hn sourceWord =
      (external.primitive : FreeModel n L) + (rho : FreeModel n L)) :
    (adaptedWeightedBasis n L data hn).factorProj 1
        (terminalTraceRemainder n L data hn external sourceWord rho) = 0 := by
  rw [terminalTraceRemainder, map_sub, map_add,
    external.projection_eq,
    (adaptedWeightedBasis n L data hn).factorProj_one_iota,
    factorProj_one_eq_iota_pbwPrimitive, hprimitive, map_add]
  abel

/-- The analogous canonical remainder between the raw mapped Smith-block word
and the literal source-placement word. -/
def terminalRealizationRemainder
    (blockCycle : Koszul.cyclesOne
      (rPresentation n L data (by omega)) 1)
    (sourceWord : UEA ℤ (FreeModel n L))
    (rho : Relations n L data) : UEA ℤ (FreeModel n L) :=
  sourceWord + UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) -
    (terminalBlockCanonicalRawMarkedWord n L data hn blockCycle).word

@[simp] theorem terminalRealizationRemainder_equation
    (blockCycle : Koszul.cyclesOne
      (rPresentation n L data (by omega)) 1)
    (sourceWord : UEA ℤ (FreeModel n L))
    (rho : Relations n L data) :
    (terminalBlockCanonicalRawMarkedWord n L data hn blockCycle).word +
        terminalRealizationRemainder n L data hn blockCycle sourceWord rho =
      sourceWord + UniversalEnvelopingAlgebra.ι ℤ
        (rho : FreeModel n L) := by
  unfold terminalRealizationRemainder
  abel

/-- A primitive identity modulo a whole relation proves that the literal
source-to-block realization remainder is factor-one invisible. -/
theorem terminalRealizationRemainder_factorProj_one_eq_zero
    (blockCycle : Koszul.cyclesOne
      (rPresentation n L data (by omega)) 1)
    (sourceWord : UEA ℤ (FreeModel n L))
    (rho : Relations n L data)
    (hprimitive : pbwPrimitive n L data hn
        (terminalBlockCanonicalRawMarkedWord
          n L data hn blockCycle).word =
      pbwPrimitive n L data hn sourceWord + (rho : FreeModel n L)) :
    (adaptedWeightedBasis n L data hn).factorProj 1
        (terminalRealizationRemainder
          n L data hn blockCycle sourceWord rho) = 0 := by
  rw [terminalRealizationRemainder, map_sub, map_add,
    (adaptedWeightedBasis n L data hn).factorProj_one_iota,
    factorProj_one_eq_iota_pbwPrimitive,
    factorProj_one_eq_iota_pbwPrimitive, hprimitive, map_add]
  abel

/-- Concrete terminal certificate for a genuine source cycle.  Its three
literal words are fixed here:

* the governing external word;
* `terminalSourcePlacedWord cycle`, the manuscript's full-relation source
  placement; and
* the raw relation-on-the-left placement of the mapped Smith-block cycle.

Accordingly the descending trace has only two mathematical obligations left:
the displayed primitive identities modulo genuine full relations.  The two
factor-one-invisible remainders are not hypotheses; they are the canonical
differences above. -/
theorem terminalCertificateOfPlacedPrimitiveEquations
    (external : TerminalMarkedWord n L data hn)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (traceRelation realizationRelation : Relations n L data)
    (htracePrimitive : pbwPrimitive n L data hn
        (terminalSourcePlacedWord n L data hn cycle.1) =
      (external.primitive : FreeModel n L) +
        (traceRelation : FreeModel n L))
    (hrealizationPrimitive : pbwPrimitive n L data hn
        (terminalBlockCanonicalRawMarkedWord n L data hn
          (Koszul.PresentationHomology.cyclesMap
            (terminalSourcePresentation n L data hn)
            (rPresentation n L data (by omega))
            (terminalComparisonHom n L data hn) 1 cycle)).word =
      pbwPrimitive n L data hn
          (terminalSourcePlacedWord n L data hn cycle.1) +
        (realizationRelation : FreeModel n L)) :
    TerminalRowCertificate n L data hn external
      (quadraticBlockMarkedWord n L data hn
        (Koszul.PresentationHomology.cyclesMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega))
          (terminalComparisonHom n L data hn) 1 cycle)) := by
  let blockCycle := Koszul.PresentationHomology.cyclesMap
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega))
    (terminalComparisonHom n L data hn) 1 cycle
  let sourceWord := terminalSourcePlacedWord n L data hn cycle.1
  let traceNoise := terminalTraceRemainder
    n L data hn external sourceWord traceRelation
  let realizationNoise := terminalRealizationRemainder
    n L data hn blockCycle sourceWord realizationRelation
  apply terminalCertificateOfRawTraceAndRealizationEquations
    n L data hn external blockCycle sourceWord traceRelation
      realizationRelation traceNoise realizationNoise
  · exact terminalTraceRemainder_factorProj_one_eq_zero
      n L data hn external sourceWord traceRelation htracePrimitive
  · exact terminalRealizationRemainder_factorProj_one_eq_zero
      n L data hn blockCycle sourceWord realizationRelation
        hrealizationPrimitive
  · exact terminalTraceRemainder_equation
      n L data hn external sourceWord traceRelation
  · exact terminalRealizationRemainder_equation
      n L data hn blockCycle sourceWord realizationRelation

/-! ## The manuscript's corrected contextual terminal cycle -/

/-- The exact cycle shape dictated by the manuscript: the already constructed
contextual factor-two chain plus the full-label correction whose boundary is
the component defect. -/
def GoverningWitness.contextualTerminalCycleWithCorrection {a : L}
    (w : GoverningWitness n L data a)
    (correction : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hcorrection : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 correction =
      w.terminalFactorDefect n L data hn) :
    Koszul.cyclesOne (terminalSourcePresentation n L data hn) 1 :=
  ⟨w.contextualTerminalChain n L data hn + correction, by
    change Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.contextualTerminalChain n L data hn + correction) = 0
    rw [map_add, w.dOne_contextualTerminalChain_eq_neg_defect
      n L data hn, hcorrection]
    abel⟩

@[simp] theorem GoverningWitness.contextualTerminalCycleWithCorrection_val
    {a : L} (w : GoverningWitness n L data a)
    (correction : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hcorrection : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 correction =
      w.terminalFactorDefect n L data hn) :
    (w.contextualTerminalCycleWithCorrection n L data hn
        correction hcorrection :
      Koszul.One (terminalSourcePresentation n L data hn) 1) =
      w.contextualTerminalChain n L data hn + correction := rfl

/-- Assemble the trace-side primitive equation for the corrected contextual
cycle from its two genuine full-relation families.  This is the algebraic
form of the terminal external-edge classification: the original contextual
wall contributes the terminal-two primitive, the correction contributes the
component primitive, and the only discrepancies are whole relations. -/
theorem GoverningWitness.terminalSourcePrimitive_corrected_eq_external
    {a : L} (w : GoverningWitness n L data a)
    (correction : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (terminalRelation correctionRelation : Relations n L data)
    (hterminal : terminalSourcePrimitive n L data hn
        (w.contextualTerminalChain n L data hn) =
      w.terminalTwoPrimitive n L data hn +
        (terminalRelation : FreeModel n L))
    (hcorrection : terminalSourcePrimitive n L data hn correction =
      w.componentTracePrimitive n L data hn +
        (correctionRelation : FreeModel n L)) :
    terminalSourcePrimitive n L data hn
        (w.contextualTerminalChain n L data hn + correction) =
      (w.externalPrimitivePreimage n L data hn : FreeModel n L) +
        ((terminalRelation + correctionRelation : Relations n L data) :
          FreeModel n L) := by
  rw [map_add, hterminal, hcorrection,
    w.externalPrimitivePreimage_eq n L data hn]
  change w.terminalTwoPrimitive n L data hn +
        (terminalRelation : FreeModel n L) +
      (w.componentTracePrimitive n L data hn +
        (correctionRelation : FreeModel n L)) =
    (w.componentTracePrimitive n L data hn +
        w.terminalTwoPrimitive n L data hn) +
      ((terminalRelation : FreeModel n L) +
        (correctionRelation : FreeModel n L))
  abel

/-! ## Literal source placement of the contextual terminal wall -/

/-- The whole contextual commutator relation generated when the source
relation-on-the-left placement is interchanged with the displayed ordinary
factor. -/
def ProvenancedTerminalTwo.sourcePlacementRelation
    (c : ProvenancedTerminalTwo n L data hn) : Relations n L data :=
  terminalFullRelationBracket n L data
    (RelationContext.relation n L data hn c.context c.root)
    (adaptedBasis n L data hn c.factor)

/-- For one terminal contextual wall, the PBW primitive of its literal source
placement is its stored terminal-two primitive plus exactly one whole
contextual commutator relation.  All discrepancies between chosen lifts and
the displayed truncations are homogeneous top pieces, hence contribute no
factor-one term. -/
theorem ProvenancedTerminalTwo.terminalSourcePrimitive_chain
    (c : ProvenancedTerminalTwo n L data hn) :
    terminalSourcePrimitive n L data hn (c.chain n L data hn) =
      c.primitive n L data hn +
        (c.sourcePlacementRelation n L data hn : FreeModel n L) := by
  let R : FreeModel n L :=
    RelationContext.relation n L data hn c.context c.root
  let P : FreeModel n L :=
    RelationContext.markedPrefix n L data hn c.context c.root c.mark
  let f : FreeModel n L := adaptedBasis n L data hn c.factor
  let d : D n L data n (by omega) :=
    fullRelationToD n L data n (by omega)
      (RelationContext.relation n L data hn c.context c.root)
  let liftR : FreeModel n L := terminalFullLift n L data hn d
  let liftF : FreeModel n L := terminalSourceGeneratorLift n L
    (prLE n L n (by omega) f)
  have hsource : terminalSourcePlacedWord n L data hn
        (c.chain n L data hn) =
      UniversalEnvelopingAlgebra.ι ℤ liftR *
        UniversalEnvelopingAlgebra.ι ℤ liftF := by
    rw [ProvenancedTerminalTwo.chain,
      terminalSourcePlacedWord_tmul]
    change UniversalEnvelopingAlgebra.ι ℤ liftR *
        UniversalEnvelopingAlgebra.ι ℤ
          (terminalSourceSymOneLift n L
            (SymmetricPower.tprod ℤ (fun _ : Fin 1 ↦
              prLE n L n (by omega) (adaptedBasis n L data hn c.factor)))) = _
    rw [terminalSourceSymOneLift_tprod]
  have hrow : c.row.value =
      UniversalEnvelopingAlgebra.ι ℤ f *
        UniversalEnvelopingAlgebra.ι ℤ P := by
    simp [ProvenancedTerminalTwo.row, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, adaptedWeightedBasis, adaptedBasis_apply, f, P]
  have hRP : FreeMetabelian.Free.projectPrefix n (by omega) R =
      FreeMetabelian.Free.projectPrefix n (by omega) P := by
    exact RelationContext.projectPrefix_relation_eq_markedPrefix
      n L data hn c.context c.root c.mark c.active
  have hliftPrefix : FreeMetabelian.Free.projectPrefix n (by omega) liftR =
      FreeMetabelian.Free.projectPrefix n (by omega) R := by
    have h := congrArg Subtype.val
      (terminalFullLift_prefix n L data hn d)
    exact h
  have hliftP : FreeMetabelian.Free.projectPrefix n (by omega) liftR =
      FreeMetabelian.Free.projectPrefix n (by omega) P :=
    hliftPrefix.trans hRP
  let topR : FreeMetabelian.Piece (Generator L) n :=
    FreeMetabelian.Free.weightProject n (by omega) (liftR - P)
  have hliftR : liftR = P +
      FreeMetabelian.Free.weightIncl n (by omega) topR := by
    have htop := sub_eq_weightIncl_top_of_projectPrefix_eq
      n L liftR P hliftP
    change liftR - P =
      FreeMetabelian.Free.weightIncl n (by omega) topR at htop
    calc
      liftR = (liftR - P) + P := by abel
      _ = FreeMetabelian.Free.weightIncl n (by omega) topR + P := by
        rw [htop]
      _ = _ := add_comm _ _
  have hliftFPrefix : FreeMetabelian.Free.projectPrefix n (by omega) liftF =
      FreeMetabelian.Free.projectPrefix n (by omega) f := by
    change FreeMetabelian.Free.projectPrefix n (by omega)
        (FreeMetabelian.Free.prefixIncl n (by omega)
          (FreeMetabelian.Free.projectPrefix n (by omega) f)) =
      FreeMetabelian.Free.projectPrefix n (by omega) f
    exact LinearMap.congr_fun
      (FreeMetabelian.Free.projectPrefix_prefixIncl
        (X := Generator L) n (by omega)) _
  let topF : FreeMetabelian.Piece (Generator L) n :=
    FreeMetabelian.Free.weightProject n (by omega) (f - liftF)
  have hliftF : liftF = f -
      FreeMetabelian.Free.weightIncl n (by omega) topF := by
    have htop := sub_eq_weightIncl_top_of_projectPrefix_eq
      n L f liftF hliftFPrefix.symm
    change f - liftF =
      FreeMetabelian.Free.weightIncl n (by omega) topF at htop
    calc
      liftF = f - (f - liftF) := by abel
      _ = f - FreeMetabelian.Free.weightIncl n (by omega) topF := by
        rw [htop]
  have hbracket : ⁅P, f⁆ = ⁅R, f⁆ := by
    let top : FreeMetabelian.Piece (Generator L) n :=
      FreeMetabelian.Free.weightProject n (by omega) (R - P)
    have htop := sub_eq_weightIncl_top_of_projectPrefix_eq n L R P hRP
    change R - P =
      FreeMetabelian.Free.weightIncl n (by omega) top at htop
    have hR : R = P + FreeMetabelian.Free.weightIncl n (by omega) top := by
      calc
        R = (R - P) + P := by abel
        _ = FreeMetabelian.Free.weightIncl n (by omega) top + P := by
          rw [htop]
        _ = _ := add_comm _ _
    rw [hR, add_lie, bracket_weightIncl_top_eq_zero n L top f, add_zero]
  change pbwPrimitive n L data hn
      (terminalSourcePlacedWord n L data hn (c.chain n L data hn)) =
    pbwPrimitive n L data hn c.row.value +
      (c.sourcePlacementRelation n L data hn : FreeModel n L)
  apply LieRings.PBW.canonicalMap_injective_of_freeModulePBW
    ℤ (FreeModel n L) (AdaptedIndex n L data hn)
    (adaptedWeightedBasis n L data hn).basis
    (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis)
  rw [map_add]
  rw [← factorProj_one_eq_iota_pbwPrimitive n L data hn,
    ← factorProj_one_eq_iota_pbwPrimitive n L data hn]
  change (adaptedWeightedBasis n L data hn).factorProj 1
      (terminalSourcePlacedWord n L data hn (c.chain n L data hn)) =
    (adaptedWeightedBasis n L data hn).factorProj 1 c.row.value +
      UniversalEnvelopingAlgebra.ι ℤ
        ((c.sourcePlacementRelation n L data hn : Relations n L data) :
          FreeModel n L)
  rw [hsource, hrow, hliftR, hliftF, map_add, map_sub,
    add_mul, mul_sub, map_add, map_sub]
  rw [mul_sub, map_sub]
  rw [factorProj_one_iota_weightIncl_top_mul_eq_zero
      n L data hn topR f,
    factorProj_one_mul_iota_weightIncl_top_eq_zero
      n L data hn P topF,
    factorProj_one_iota_weightIncl_top_mul_eq_zero
      n L data hn topR
        (FreeMetabelian.Free.weightIncl n (by omega) topF)]
  simp only [sub_zero, add_zero]
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
    (FreeModel n L) P f
  rw [hswap, map_add,
    (adaptedWeightedBasis n L data hn).factorProj_one_iota,
    hbracket]
  rfl

/-- Sum of the whole commutator relations created by putting every contextual
terminal-two source row into the displayed relation-on-the-left placement. -/
def GoverningWitness.terminalSourcePlacementRelation {a : L}
    (w : GoverningWitness n L data a) : Relations n L data :=
  (w.provenancedTerminalTwo n L data hn).sum (fun c z ↦
    z • c.sourcePlacementRelation n L data hn)

/-- Aggregate form of `ProvenancedTerminalTwo.terminalSourcePrimitive_chain`.
This supplies the contextual-wall primitive equation with a concrete whole
relation. -/
theorem GoverningWitness.terminalSourcePrimitive_contextualTerminalChain
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (w.contextualTerminalChain n L data hn) =
      w.terminalTwoPrimitive n L data hn +
        (w.terminalSourcePlacementRelation n L data hn : FreeModel n L) := by
  classical
  rw [GoverningWitness.contextualTerminalChain,
    GoverningWitness.terminalTwoPrimitive,
    GoverningWitness.terminalSourcePlacementRelation,
    map_finsuppSum]
  simp_rw [map_zsmul]
  change (w.provenancedTerminalTwo n L data hn).sum
      (fun c z ↦ z • terminalSourcePrimitive n L data hn
        (c.chain n L data hn)) =
    (w.provenancedTerminalTwo n L data hn).sum
        (fun c z ↦ z • c.primitive n L data hn) +
      (Relations n L data).subtype
        ((w.provenancedTerminalTwo n L data hn).sum (fun c z ↦
          z • c.sourcePlacementRelation n L data hn))
  rw [map_finsuppSum]
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  rw [c.terminalSourcePrimitive_chain n L data hn, smul_add, map_zsmul]
  rfl

/-- Whole relation created when the older two-placement terminal frontier is
read in the canonical relation-on-the-left source placement. -/
def TerminalFactorTwo.sourcePlacementRelation
    (c : TerminalFactorTwo n L data hn) : Relations n L data :=
  match c.placement with
  | .relationLeft => 0
  | .relationRight =>
      relationRightBracket n L data hn c.relation c.factor

/-- The canonical source primitive of either retained placement.  For the
right placement the only discrepancy is the whole commutator relation from
the literal UEA interchange. -/
theorem TerminalFactorTwo.terminalSourcePrimitive_factorChain
    (c : TerminalFactorTwo n L data hn) :
    terminalSourcePrimitive n L data hn
        (terminalFactorChain n L data hn c) =
      pbwPrimitive n L data hn c.row.value +
        (c.sourcePlacementRelation n L data hn : FreeModel n L) := by
  have hgeneric := terminalSourcePrimitive_fullRelationFactorChain
    n L data hn c.relation
      (adaptedBasis n L data hn c.factor)
  have hchain : terminalFactorChain n L data hn c =
      terminalFullRelationFactorChain n L data hn c.relation
        (adaptedBasis n L data hn c.factor) := by
    rfl
  rw [hchain, hgeneric]
  cases c with
  | mk rho factor placement =>
      cases placement with
      | relationLeft =>
          simp [terminalFullRelationFactorWord,
            TerminalFactorTwo.row, MarkedRow.value,
            MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, rowTruncation_top,
            TerminalFactorTwo.sourcePlacementRelation,
            adaptedWeightedBasis]
      | relationRight =>
          let f : FreeModel n L := adaptedBasis n L data hn factor
          have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
            (FreeModel n L) (rho : FreeModel n L) f
          rw [terminalFullRelationFactorWord, hswap, map_add,
            pbwPrimitive_iota]
          simp only [TerminalFactorTwo.row, MarkedRow.value,
            MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, rowTruncation_top, List.map_singleton,
            List.prod_singleton, List.map_nil, List.prod_nil,
            one_mul, mul_one, TerminalFactorTwo.sourcePlacementRelation]
          rfl

/-- Primitive carried by the older two-placement terminal frontier. -/
def GoverningWitness.closedSquareTerminalPrimitive {a : L}
    (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.closedSquareTerminal n L data hn).sum (fun c z ↦
    z • pbwPrimitive n L data hn c.row.value)

/-- Aggregate whole relation needed to change that frontier to the canonical
source placement. -/
def GoverningWitness.closedSquareSourcePlacementRelation {a : L}
    (w : GoverningWitness n L data a) : Relations n L data :=
  (w.closedSquareTerminal n L data hn).sum (fun c z ↦
    z • c.sourcePlacementRelation n L data hn)

/-- Aggregate source primitive of `chiTerminalCollected`, with both retained
placements accounted for and no tail used as a relation. -/
theorem GoverningWitness.terminalSourcePrimitive_chiTerminalCollected
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (chiTerminalCollected n L data hn w) =
      w.closedSquareTerminalPrimitive n L data hn +
        (w.closedSquareSourcePlacementRelation n L data hn :
          FreeModel n L) := by
  classical
  rw [chiTerminalCollected,
    GoverningWitness.closedSquareTerminalPrimitive,
    GoverningWitness.closedSquareSourcePlacementRelation,
    map_finsuppSum]
  simp_rw [map_zsmul]
  change (w.closedSquareTerminal n L data hn).sum
      (fun c z ↦ z • terminalSourcePrimitive n L data hn
        (terminalFactorChain n L data hn c)) =
    (w.closedSquareTerminal n L data hn).sum
        (fun c z ↦ z • pbwPrimitive n L data hn c.row.value) +
      (Relations n L data).subtype
        ((w.closedSquareTerminal n L data hn).sum (fun c z ↦
          z • c.sourcePlacementRelation n L data hn))
  rw [map_finsuppSum, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  rw [c.terminalSourcePrimitive_factorChain n L data hn, smul_add, map_zsmul]
  rfl

/-- The exact certificate supplied by the aggregate terminal realization
calculation.  All relation contributions have first been summed as the whole
element `rho`; `noise` is discarded only after proving that its *complete*
factor-one PBW projection is zero. -/
def terminalCertificateOfTraceEquation
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (rho : Relations n L data)
    (noise : UEA ℤ (FreeModel n L))
    (hnoise :
      (adaptedWeightedBasis n L data hn).factorProj 1 noise = 0)
    (external : TerminalMarkedWord n L data hn)
    (hword :
      ((quadraticBlockMarkedWord n L data hn
          (Koszul.PresentationHomology.cyclesMap
            (terminalSourcePresentation n L data hn)
            (rPresentation n L data (by omega))
            (terminalComparisonHom n L data hn) 1 cycle)).add
        n L data hn
        (terminalZeroFactorOneMarkedWord
          n L data hn noise hnoise)).word =
        external.word + UniversalEnvelopingAlgebra.ι ℤ
          (rho : FreeModel n L)) :
    TerminalRowCertificate n L data hn external
      (quadraticBlockMarkedWord n L data hn
        (Koszul.PresentationHomology.cyclesMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega))
          (terminalComparisonHom n L data hn) 1 cycle)) :=
  terminalCertificateOfRelationAndNoise
    n L data hn external _ rho noise hnoise hword

/-- Step 7 after the two substantive outputs of the descending trace have
been proved: `cycle` is closed, and `hword` is its complete realization
equation.  Point 6 then kills the mapped quadratic block and the governing
top coordinate is zero. -/
theorem GoverningWitness.eq_zero_of_completeTerminalTrace {a : L}
    (w : GoverningWitness n L data a)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (rho : Relations n L data)
    (noise : UEA ℤ (FreeModel n L))
    (hnoise :
      (adaptedWeightedBasis n L data hn).factorProj 1 noise = 0)
    (hword :
      ((quadraticBlockMarkedWord n L data hn
          (Koszul.PresentationHomology.cyclesMap
            (terminalSourcePresentation n L data hn)
            (rPresentation n L data (by omega))
            (terminalComparisonHom n L data hn) 1 cycle)).add
        n L data hn
        (terminalZeroFactorOneMarkedWord
          n L data hn noise hnoise)).word =
        (w.externalMarkedWord n L data hn).word +
          UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L)) :
    a = 0 := by
  apply w.eq_zero_of_terminalCycleCertificate n L data hn
    (terminalComparisonHom n L data hn) cycle
  exact terminalCertificateOfTraceEquation n L data hn cycle rho noise
    hnoise (w.externalMarkedWord n L data hn) hword

/-- The fully concrete Step-7 endpoint in primitive form.  The cycle is
already genuine, its source word is the literal source placement, and its
target word is the literal raw placement of the mapped Smith block.  Thus the
two hypotheses are exactly the two row-calculation equalities which remain to
be supplied by the complete full-relation trace. -/
theorem GoverningWitness.eq_zero_of_placedTerminalPrimitiveEquations {a : L}
    (w : GoverningWitness n L data a)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (traceRelation realizationRelation : Relations n L data)
    (htracePrimitive : pbwPrimitive n L data hn
        (terminalSourcePlacedWord n L data hn cycle.1) =
      ((w.externalMarkedWord n L data hn).primitive : FreeModel n L) +
        (traceRelation : FreeModel n L))
    (hrealizationPrimitive : pbwPrimitive n L data hn
        (terminalBlockCanonicalRawMarkedWord n L data hn
          (Koszul.PresentationHomology.cyclesMap
            (terminalSourcePresentation n L data hn)
            (rPresentation n L data (by omega))
            (terminalComparisonHom n L data hn) 1 cycle)).word =
      pbwPrimitive n L data hn
          (terminalSourcePlacedWord n L data hn cycle.1) +
        (realizationRelation : FreeModel n L)) :
    a = 0 := by
  apply w.eq_zero_of_terminalCycleCertificate n L data hn
    (terminalComparisonHom n L data hn) cycle
  exact terminalCertificateOfPlacedPrimitiveEquations
    n L data hn (w.externalMarkedWord n L data hn) cycle
      traceRelation realizationRelation htracePrimitive
      hrealizationPrimitive

/-- Direct consumer for the manuscript's corrected contextual cycle.  The
first three hypotheses are the exact outputs of the full-label trace; the
last is the source-to-Smith realization calculation.  Together they contain
no auxiliary cycle choice and no assertion that a separated tail is a
relation. -/
theorem GoverningWitness.eq_zero_of_contextualCorrection
    {a : L} (w : GoverningWitness n L data a)
    (correction : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 correction =
      w.terminalFactorDefect n L data hn)
    (terminalRelation correctionRelation realizationRelation :
      Relations n L data)
    (hterminal : terminalSourcePrimitive n L data hn
        (w.contextualTerminalChain n L data hn) =
      w.terminalTwoPrimitive n L data hn +
        (terminalRelation : FreeModel n L))
    (hcorrection : terminalSourcePrimitive n L data hn correction =
      w.componentTracePrimitive n L data hn +
        (correctionRelation : FreeModel n L))
    (hrealization : pbwPrimitive n L data hn
        (terminalBlockCanonicalRawMarkedWord n L data hn
          (Koszul.PresentationHomology.cyclesMap
            (terminalSourcePresentation n L data hn)
            (rPresentation n L data (by omega))
            (terminalComparisonHom n L data hn) 1
            (w.contextualTerminalCycleWithCorrection
              n L data hn correction hboundary))).word =
      terminalSourcePrimitive n L data hn
          (w.contextualTerminalChain n L data hn + correction) +
        (realizationRelation : FreeModel n L)) :
    a = 0 := by
  let cycle := w.contextualTerminalCycleWithCorrection
    n L data hn correction hboundary
  apply w.eq_zero_of_placedTerminalPrimitiveEquations
    n L data hn cycle
      (terminalRelation + correctionRelation) realizationRelation
  · change terminalSourcePrimitive n L data hn
        (w.contextualTerminalChain n L data hn + correction) = _
    exact w.terminalSourcePrimitive_corrected_eq_external
      n L data hn correction terminalRelation correctionRelation
        hterminal hcorrection
  · exact hrealization

end

end LieRings.MetabelianVanishing
