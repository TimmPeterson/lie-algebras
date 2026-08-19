import LieRings.DimensionSubring.MetabelianVanishing.QuadraticPBWBlock

/-!
# The terminal source-placement transport

This file contains the narrow comparison used at the terminal wall.  It keeps
the literal placed word of the canonical source presentation separate from
the canonical four-family word in the Smith block.
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

local instance terminalTransportFintype : Fintype L := Fintype.ofFinite L

/-! ## Literal source and block placements -/

/-- Read a degree-one symmetric source generator and include it in the full
graded free model. -/
def terminalSourceSymOneLift :
    Sym[ℤ] (Fin 1) (A L n) →ₗ[ℤ] FreeModel n L :=
  (terminalSourceGeneratorLift n L).comp
    (SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)).toLinearMap

/-- The relation-on-the-left bilinear placement of the canonical terminal
presentation. -/
def terminalSourcePlacedBilinear :
    D n L data n (by omega) →ₗ[ℤ]
      Sym[ℤ] (Fin 1) (A L n) →ₗ[ℤ] UEA ℤ (FreeModel n L) where
  toFun d :=
    { toFun := fun s ↦
        UniversalEnvelopingAlgebra.ι ℤ
            (terminalFullLift n L data hn d : FreeModel n L) *
          UniversalEnvelopingAlgebra.ι ℤ
            (terminalSourceSymOneLift n L s)
      map_add' := by intro x y; rw [map_add, map_add, mul_add]
      map_smul' := by
        intro z x
        change _ * UniversalEnvelopingAlgebra.ι ℤ
            (terminalSourceSymOneLift n L (z • x)) = z • (_ * _)
        rw [show terminalSourceSymOneLift n L (z • x) =
            z • terminalSourceSymOneLift n L x by
          exact map_zsmul (terminalSourceSymOneLift n L) z x]
        rw [map_zsmul, mul_smul_comm] }
  map_add' x y := by
    ext s
    change UniversalEnvelopingAlgebra.ι ℤ
          (terminalFullLift n L data hn (x + y) : FreeModel n L) * _ =
      UniversalEnvelopingAlgebra.ι ℤ
          (terminalFullLift n L data hn x : FreeModel n L) * _ +
        UniversalEnvelopingAlgebra.ι ℤ
          (terminalFullLift n L data hn y : FreeModel n L) * _
    rw [map_add]
    change UniversalEnvelopingAlgebra.ι ℤ
        ((terminalFullLift n L data hn x : FreeModel n L) +
          (terminalFullLift n L data hn y : FreeModel n L)) * _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' z x := by
    ext s
    change UniversalEnvelopingAlgebra.ι ℤ
          (terminalFullLift n L data hn (z • x) : FreeModel n L) * _ =
      z • (UniversalEnvelopingAlgebra.ι ℤ
          (terminalFullLift n L data hn x : FreeModel n L) * _)
    rw [map_zsmul]
    change UniversalEnvelopingAlgebra.ι ℤ
        (z • (terminalFullLift n L data hn x : FreeModel n L)) * _ = _
    rw [map_zsmul, smul_mul_assoc]

/-- Literal relation-on-the-left UEA word of a source degree-one chain. -/
def terminalSourcePlacedWord :
    Koszul.One (terminalSourcePresentation n L data hn) 1 →ₗ[ℤ]
      UEA ℤ (FreeModel n L) :=
  (TensorProduct.lift (terminalSourcePlacedBilinear n L data hn)).toAddMonoidHom.toIntLinearMap

@[simp] theorem terminalSourcePlacedWord_tmul
    (d : D n L data n (by omega))
    (s : Sym[ℤ] (Fin 1) (A L n)) :
    terminalSourcePlacedWord n L data hn (d ⊗ₜ[ℤ] s) =
      UniversalEnvelopingAlgebra.ι ℤ
          (terminalFullLift n L data hn d : FreeModel n L) *
        UniversalEnvelopingAlgebra.ι ℤ
          (terminalSourceSymOneLift n L s) := by
  rfl

/-- Read a degree-one symmetric block generator and include it homogeneously
in the full graded free model. -/
def terminalBlockSymOneLift :
    Sym[ℤ] (Fin 1) (PZero L × QZero n L) →ₗ[ℤ] FreeModel n L :=
  (quadraticBlockIncl n L hn).comp
    (SymmetricPower.degreeOneLinearEquiv
      ((pSmith n L).ambientBasis.prod
        (qSmith n L data (by omega)).ambientBasis)).toLinearMap

/-- Relation-on-the-left placement before the four Smith families are put in
their prescribed orientations. -/
def terminalBlockRawPlacedBilinear :
    (POne n L × QOne n L data (by omega)) →ₗ[ℤ]
      Sym[ℤ] (Fin 1) (PZero L × QZero n L) →ₗ[ℤ]
        UEA ℤ (FreeModel n L) where
  toFun d :=
    { toFun := fun s ↦
        UniversalEnvelopingAlgebra.ι ℤ
            (quadraticBlockFullRelationLift n L data hn d : FreeModel n L) *
          UniversalEnvelopingAlgebra.ι ℤ
            (terminalBlockSymOneLift n L data hn s)
      map_add' := by intro x y; rw [map_add, map_add, mul_add]
      map_smul' := by
        intro z x
        change _ * UniversalEnvelopingAlgebra.ι ℤ
            (terminalBlockSymOneLift n L data hn (z • x)) = z • (_ * _)
        rw [show terminalBlockSymOneLift n L data hn (z • x) =
            z • terminalBlockSymOneLift n L data hn x by
          exact map_zsmul (terminalBlockSymOneLift n L data hn) z x]
        rw [map_zsmul, mul_smul_comm] }
  map_add' x y := by
    ext s
    change UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockFullRelationLift n L data hn (x + y) : FreeModel n L) * _ =
      UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockFullRelationLift n L data hn x : FreeModel n L) * _ +
        UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockFullRelationLift n L data hn y : FreeModel n L) * _
    rw [map_add]
    change UniversalEnvelopingAlgebra.ι ℤ
        ((quadraticBlockFullRelationLift n L data hn x : FreeModel n L) +
          (quadraticBlockFullRelationLift n L data hn y : FreeModel n L)) * _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' z x := by
    ext s
    change UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockFullRelationLift n L data hn (z • x) : FreeModel n L) * _ =
      z • (UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockFullRelationLift n L data hn x : FreeModel n L) * _)
    rw [map_zsmul]
    change UniversalEnvelopingAlgebra.ι ℤ
        (z • (quadraticBlockFullRelationLift n L data hn x : FreeModel n L)) * _ = _
    rw [map_zsmul, smul_mul_assoc]

/-- Raw relation-on-the-left UEA placement of a chain in the Smith block. -/
def terminalBlockRawPlacedWord :
    Koszul.One (rPresentation n L data (by omega)) 1 →ₗ[ℤ]
      UEA ℤ (FreeModel n L) :=
  (TensorProduct.lift
    (terminalBlockRawPlacedBilinear n L data hn)).toAddMonoidHom.toIntLinearMap

@[simp] theorem terminalBlockRawPlacedWord_tmul
    (d : POne n L × QOne n L data (by omega))
    (s : Sym[ℤ] (Fin 1) (PZero L × QZero n L)) :
    terminalBlockRawPlacedWord n L data hn (d ⊗ₜ[ℤ] s) =
      UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockFullRelationLift n L data hn d : FreeModel n L) *
        UniversalEnvelopingAlgebra.ι ℤ
          (terminalBlockSymOneLift n L data hn s) := by
  rfl

@[simp] theorem terminalBlockSymOneLift_basis
    (i : Sum (Fin (pSmith n L).rank)
      (Fin (qSmith n L data (by omega)).rank)) :
    terminalBlockSymOneLift n L data hn
        (quadraticBlockSymOneBasis n L data hn i) =
      quadraticBlockIncl n L hn
        (((pSmith n L).ambientBasis.prod
          (qSmith n L data (by omega)).ambientBasis) i) := by
  let B := (pSmith n L).ambientBasis.prod
    (qSmith n L data (by omega)).ambientBasis
  change quadraticBlockIncl n L hn
      ((SymmetricPower.degreeOneLinearEquiv B)
        ((SymmetricPower.degreeOneLinearEquiv B).symm (B i))) =
    quadraticBlockIncl n L hn (B i)
  rw [LinearEquiv.apply_symm_apply]

@[simp] theorem terminalBlockRawPlacedWord_oneBasis
    (i j : Sum (Fin (pSmith n L).rank)
      (Fin (qSmith n L data (by omega)).rank)) :
    terminalBlockRawPlacedWord n L data hn
        (quadraticBlockOneBasis n L data hn (i, j)) =
      UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockFullRelationLift n L data hn
            (quadraticBlockRelationBasis n L data hn i) : FreeModel n L) *
        UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockIncl n L hn
            (((pSmith n L).ambientBasis.prod
              (qSmith n L data (by omega)).ambientBasis) j)) := by
  have hbasis : quadraticBlockOneBasis n L data hn (i, j) =
      quadraticBlockRelationBasis n L data hn i ⊗ₜ[ℤ]
        quadraticBlockSymOneBasis n L data hn j := by
    change ((quadraticBlockRelationBasis n L data hn).tensorProduct
      (quadraticBlockSymOneBasis n L data hn)) (i, j) = _
    exact Module.Basis.tensorProduct_apply' _ _ (i, j)
  rw [hbasis]
  calc
    _ = UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockFullRelationLift n L data hn
            (quadraticBlockRelationBasis n L data hn i) : FreeModel n L) *
        UniversalEnvelopingAlgebra.ι ℤ
          (terminalBlockSymOneLift n L data hn
            (quadraticBlockSymOneBasis n L data hn j)) :=
      terminalBlockRawPlacedWord_tmul n L data hn _ _
    _ = _ := by rw [terminalBlockSymOneLift_basis]

@[simp] theorem terminalBlockRawPlacedWord_PP
    (i j : Fin (pSmith n L).rank) :
    terminalBlockRawPlacedWord n L data hn
        (quadraticBlockOneBasis n L data hn (Sum.inl i, Sum.inl j)) =
      UniversalEnvelopingAlgebra.ι ℤ
          (quadraticRho n L data hn i : FreeModel n L) *
        UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn j) := by
  rw [terminalBlockRawPlacedWord_oneBasis]
  simp [quadraticBlockRelationBasis, quadraticRho, quadraticX,
    quadraticBlockIncl]

@[simp] theorem terminalBlockRawPlacedWord_PQ
    (i : Fin (pSmith n L).rank)
    (a : Fin (qSmith n L data (by omega)).rank) :
    terminalBlockRawPlacedWord n L data hn
        (quadraticBlockOneBasis n L data hn (Sum.inl i, Sum.inr a)) =
      quadraticPQPlacedRow n L data hn i a := by
  rw [terminalBlockRawPlacedWord_oneBasis]
  simp [quadraticBlockRelationBasis, quadraticRho, quadraticY,
    quadraticPQPlacedRow, quadraticBlockIncl]

@[simp] theorem terminalBlockRawPlacedWord_QP
    (a : Fin (qSmith n L data (by omega)).rank)
    (i : Fin (pSmith n L).rank) :
    terminalBlockRawPlacedWord n L data hn
        (quadraticBlockOneBasis n L data hn (Sum.inr a, Sum.inl i)) =
      UniversalEnvelopingAlgebra.ι ℤ
          (quadraticSigma n L data hn a : FreeModel n L) *
        UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn i) := by
  rw [terminalBlockRawPlacedWord_oneBasis]
  simp [quadraticBlockRelationBasis, quadraticSigma, quadraticX,
    quadraticBlockIncl]

@[simp] theorem terminalBlockRawPlacedWord_QQ
    (a b : Fin (qSmith n L data (by omega)).rank) :
    terminalBlockRawPlacedWord n L data hn
        (quadraticBlockOneBasis n L data hn (Sum.inr a, Sum.inr b)) =
      quadraticQQPlacedRow n L data hn a b := by
  rw [terminalBlockRawPlacedWord_oneBasis]
  simp [quadraticBlockRelationBasis, quadraticSigma, quadraticY,
    quadraticQQPlacedRow, quadraticBlockIncl]

/-! ## Canonicalization of the raw block placement -/

/-- A bracket correction produced by moving a genuine full relation through
one block generator. -/
def terminalFullRelationBracket (rho : Relations n L data) (x : FreeModel n L) :
    Relations n L data :=
  ⟨⁅(rho : FreeModel n L), x⁆, by
    rw [← lie_skew]
    exact (Relations n L data).neg_mem
      ((Relations n L data).lie_mem rho.property)⟩

/-- The complete one-factor full-relation correction between the raw
relation-on-the-left block and the prescribed four-family placement. -/
def terminalBlockPlacementCorrection
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    Relations n L data :=
  (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
      if hij : i < j then
        quadraticHorizontalCoefficient n L data hn c i j •
          terminalFullRelationBracket n L data
            (quadraticRho n L data hn j) (quadraticX n L hn i)
      else 0) -
    (∑ a : Fin (qSmith n L data (by omega)).rank,
      ∑ i : Fin (pSmith n L).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inl i) •
          terminalFullRelationBracket n L data
            (quadraticSigma n L data hn a) (quadraticX n L hn i))

/-- The raw block word, expressed in the orientation in which every full
relation is on the left.  The equality with `terminalBlockRawPlacedWord` is
proved below; this definition fixes the correction sign independently. -/
def terminalBlockCanonicalRawWord
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    UEA ℤ (FreeModel n L) :=
  quadraticBlockPlacedWord n L data hn c -
    UniversalEnvelopingAlgebra.ι ℤ
      (terminalBlockPlacementCorrection n L data hn c : FreeModel n L)

/-- Mark the raw block word with its actual complete factor-one primitive.
The difference from the canonical block primitive is a whole full relation,
not a separated homogeneous tail. -/
def terminalBlockCanonicalRawMarkedWord
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    TerminalMarkedWord n L data hn where
  word := terminalBlockCanonicalRawWord n L data hn c
  primitive := (quadraticBlockMarkedWord n L data hn c).primitive -
    relationTopPreimage n L data
      (terminalBlockPlacementCorrection n L data hn c)
  projection_eq := by
    rw [terminalBlockCanonicalRawWord, map_sub,
      quadraticBlockPlacedWord_factorProj,
      (adaptedWeightedBasis n L data hn).factorProj_one_iota]
    change UniversalEnvelopingAlgebra.ι ℤ
          (quadraticBlockPrimitive n L data hn c) -
        UniversalEnvelopingAlgebra.ι ℤ
          (terminalBlockPlacementCorrection n L data hn c :
            FreeModel n L) =
      UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl n (by omega)
            (quadraticBlockPrimitivePiece n L data hn c) -
          (terminalBlockPlacementCorrection n L data hn c :
            FreeModel n L))
    rw [← quadraticBlockPrimitive_eq_weightIncl, map_sub]

@[simp] theorem terminalBlockCanonicalRawMarkedWord_word
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    (terminalBlockCanonicalRawMarkedWord n L data hn c).word =
      terminalBlockCanonicalRawWord n L data hn c := rfl

/-- Integral relation interchange carries the raw block orientation to the
four canonical Smith families. -/
def terminalBlockCanonicalRawCertificate
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    TerminalRowCertificate n L data hn
      (terminalBlockCanonicalRawMarkedWord n L data hn c)
      (quadraticBlockMarkedWord n L data hn c) := by
  have hword : quadraticBlockPlacedWord n L data hn c =
      terminalBlockCanonicalRawWord n L data hn c +
      UniversalEnvelopingAlgebra.ι ℤ
        (terminalBlockPlacementCorrection n L data hn c : FreeModel n L) := by
    rw [terminalBlockCanonicalRawWord]
    abel
  apply TerminalRowCertificate.relationCorrection
    (terminalBlockPlacementCorrection n L data hn c) 1
  simpa only [terminalBlockCanonicalRawMarkedWord_word, one_zsmul]
    using hword

/-! ## The exact terminal certificate combiner -/

/-- A literal UEA word with zero complete factor-one PBW projection, marked
by the zero primitive. -/
def TerminalMarkedWord.ofZeroFactorOne
    (word : UEA ℤ (FreeModel n L))
    (hproj : (adaptedWeightedBasis n L data hn).factorProj 1 word = 0) :
    TerminalMarkedWord n L data hn where
  word := word
  primitive := 0
  projection_eq := by
    rw [hproj]
    exact (map_zero
      (UniversalEnvelopingAlgebra.ι ℤ :
        LieHom ℤ (FreeModel n L) (UEA ℤ (FreeModel n L)))).symm

@[simp] theorem TerminalMarkedWord.ofZeroFactorOne_word
    (word : UEA ℤ (FreeModel n L))
    (hproj : (adaptedWeightedBasis n L data hn).factorProj 1 word = 0) :
    (TerminalMarkedWord.ofZeroFactorOne n L data hn word hproj).word = word :=
  rfl

/-- Combine the two harmless discrepancies allowed by the manuscript: a
whole one-factor full relation and a word with zero complete factor-one PBW
projection.  This is the form in which the realization-defect calculation is
consumed. -/
theorem TerminalRowCertificate.of_relation_and_zeroFactorOne
    (u v : TerminalMarkedWord n L data hn)
    (rho : Relations n L data) (z : ℤ)
    (noise : UEA ℤ (FreeModel n L))
    (hnoise : (adaptedWeightedBasis n L data hn).factorProj 1 noise = 0)
    (hword :
      (v.add n L data hn
        (TerminalMarkedWord.ofZeroFactorOne n L data hn noise hnoise)).word =
        u.word + z • UniversalEnvelopingAlgebra.ι ℤ
          (rho : FreeModel n L)) :
    TerminalRowCertificate n L data hn u v := by
  let zeroNoise := TerminalMarkedWord.ofZeroFactorOne
    n L data hn noise hnoise
  let vNoise := v.add n L data hn zeroNoise
  have hrel : TerminalRowCertificate n L data hn u vNoise :=
    TerminalRowCertificate.relationCorrection rho z hword
  have hdrop : TerminalRowCertificate n L data hn vNoise
      (v.add n L data hn (TerminalMarkedWord.zero n L data hn)) :=
    TerminalRowCertificate.add (TerminalRowCertificate.refl v)
      (TerminalRowCertificate.zeroFactorOne hnoise)
  have hzero : TerminalRowCertificate n L data hn
      (v.add n L data hn (TerminalMarkedWord.zero n L data hn)) v :=
    TerminalRowCertificate.basisExpansion (by simp)
  exact TerminalRowCertificate.trans hrel
    (TerminalRowCertificate.trans hdrop hzero)

/-- Populate a terminal packet once the complete trace has supplied its
actual finite rows and the realization-defect calculation in the exact
`relation + factor-one-zero` form above. -/
def terminalQuadraticPacketOfCertificate
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (cycle : Koszul.cyclesOne (terminalSourcePresentation n L data hn) 1)
    (actualRows :
      (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ)
    (actualMarked : TerminalMarkedWord n L data hn)
    (actualMarked_word : actualMarked.word =
      terminalPacketWord n L data actualRows)
    (rho : Relations n L data) (z : ℤ)
    (noise : UEA ℤ (FreeModel n L))
    (hnoise : (adaptedWeightedBasis n L data hn).factorProj 1 noise = 0)
    (hword :
      ((quadraticBlockMarkedWord n L data hn
        (Koszul.PresentationHomology.cyclesMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega)) g 1 cycle)).add
            n L data hn
            (TerminalMarkedWord.ofZeroFactorOne
              n L data hn noise hnoise)).word =
        actualMarked.word + z • UniversalEnvelopingAlgebra.ι ℤ
          (rho : FreeModel n L)) :
    TerminalQuadraticPacket n L data hn where
  g := g
  cycle := cycle
  actualRows := actualRows
  actualMarked := actualMarked
  actualMarked_word := actualMarked_word
  certificate := TerminalRowCertificate.of_relation_and_zeroFactorOne
    n L data hn actualMarked _ rho z noise hnoise hword

end

end LieRings.MetabelianVanishing
