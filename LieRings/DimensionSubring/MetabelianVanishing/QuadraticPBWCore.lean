import LieRings.DimensionSubring.MetabelianVanishing.Witness
import LieRings.DimensionSubring.MetabelianVanishing.QuadraticCertificate

/-!
# The canonical terminal quadratic PBW block: homogeneous realization and rows

This file realizes the terminal block presentation inside the same graded free
metabelian Lie ring used by the governing witness.  In particular, every row
label below is a full element of `Relations`; the last homogeneous coordinate
is retained separately only as a top tail.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open TensorProduct
open LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance quadraticPBWCoreFintype : Fintype L := Fintype.ofFinite L

-- These are the same canonical finite/free instances used to construct the
-- fixed Smith presentation in `QuadraticCharacter`.
local instance : Finite (V L n) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)
local instance : Module.Free ℤ (PZero L) :=
  Module.Free.of_basis (pZeroBasis L)
local instance : Module.Finite ℤ (PZero L) :=
  Module.Finite.of_basis (pZeroBasis L)
local instance : Module.Finite ℤ (POne n L) :=
  Module.Finite.of_fg (IsNoetherian.noetherian _)
local instance : Module.Free ℤ (POne n L) :=
  Module.free_of_finite_type_torsion_free'

/-! ## The homogeneous realization of the block presentation -/

/-- The two homogeneous generator pieces of `R`, embedded in the prefix
through manuscript weight `n`. -/
def quadraticBlockPrefixIncl :
    (PZero L × QZero n L) →ₗ[ℤ] A L n :=
  (FreeMetabelian.Free.weightIncl (X := Generator L) 0 (by omega)).coprod
    (FreeMetabelian.Free.weightIncl (X := Generator L) (n - 1) (by omega))

@[simp] theorem quadraticBlockPrefixIncl_apply (x : PZero L) (y : QZero n L) :
    quadraticBlockPrefixIncl n L hn (x, y) =
      FreeMetabelian.Free.weightIncl (X := Generator L) 0 (by omega) x +
        FreeMetabelian.Free.weightIncl (X := Generator L) (n - 1) (by omega) y :=
  rfl

/-- The homogeneous block generators have exactly the augmentation fixed in
Point 5. -/
theorem augmentation_quadraticBlockPrefixIncl (x : PZero L) (y : QZero n L) :
    augmentation (n := n) L data n (quadraticBlockPrefixIncl n L hn (x, y)) =
      rAugmentation n L data (by omega) (x, y) := by
  rw [quadraticBlockPrefixIncl_apply, map_add, rAugmentation_apply]
  congr 1
  · change (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ
        (FreeMetabelian.Evaluation.linear data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n
            (FreeMetabelian.Free.incl ⟨0, by omega⟩ x)) = _
    rw [FreeMetabelian.Evaluation.linear_incl]
    rfl
  · change (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ
        (FreeMetabelian.Evaluation.linear data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n
            (FreeMetabelian.Free.incl ⟨n - 1, by omega⟩ y)) = _
    rw [FreeMetabelian.Evaluation.linear_incl]
    rfl

/-- The block differential, embedded in the homogeneous prefix. -/
def quadraticBlockRelationPrefix :
    (POne n L × QOne n L data (by omega)) →ₗ[ℤ] A L n :=
  (quadraticBlockPrefixIncl n L hn).comp (rDifferential n L data (by omega))

theorem quadraticBlockRelationPrefix_mem_D
    (z : POne n L × QOne n L data (by omega)) :
    quadraticBlockRelationPrefix n L data hn z ∈ D n L data n (by omega) := by
  rw [exact_D_augmentation n L data n (by omega)]
  change augmentation (n := n) L data n
      (quadraticBlockPrefixIncl n L hn (rDifferential n L data (by omega) z)) = 0
  rw [augmentation_quadraticBlockPrefixIncl n L data hn]
  exact rAugmentation_d n L data (by omega) z

/-- The product of the two Smith relation bases, used once to choose genuine
full relation lifts. -/
def quadraticBlockRelationBasis :
    Module.Basis
      (Sum (Fin (pSmith n L).rank) (Fin (qSmith n L data (by omega)).rank))
      ℤ (POne n L × QOne n L data (by omega)) :=
  (pSmith n L).relationBasis.prod (qSmith n L data (by omega)).relationBasis

/-- The complete homogeneous inclusion of block generators in the full free
model. -/
def quadraticBlockIncl :
    (PZero L × QZero n L) →ₗ[ℤ] FreeModel n L :=
  (FreeMetabelian.Free.weightIncl (X := Generator L) 0 (by omega)).coprod
    (FreeMetabelian.Free.weightIncl (X := Generator L) (n - 1) (by omega))

/-- Evaluation of the full and prefix homogeneous block inclusions agree. -/
theorem evaluation_quadraticBlockIncl (x : PZero L) (y : QZero n L) :
    evaluation n L data (quadraticBlockIncl n L hn (x, y)) =
      prefixEvaluation (n := n) L data n
        (quadraticBlockPrefixIncl n L hn (x, y)) := by
  rw [quadraticBlockPrefixIncl_apply]
  change evaluation n L data
      (FreeMetabelian.Free.weightIncl (X := Generator L) 0 (by omega) x +
        FreeMetabelian.Free.weightIncl (X := Generator L) (n - 1) (by omega) y) =
    prefixEvaluation (n := n) L data n
      (FreeMetabelian.Free.weightIncl (X := Generator L) 0 (by omega) x +
        FreeMetabelian.Free.weightIncl (X := Generator L) (n - 1) (by omega) y)
  rw [map_add, map_add]
  change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl ⟨0, by omega⟩ x) +
      FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl ⟨n - 1, by omega⟩ y) =
    FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n
          (FreeMetabelian.Free.incl ⟨0, by omega⟩ x) +
      FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n
          (FreeMetabelian.Free.incl ⟨n - 1, by omega⟩ y)
  rw [FreeMetabelian.Evaluation.linear_incl data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
      (⟨0, by omega⟩ : Fin (n + 1)) x,
    FreeMetabelian.Evaluation.linear_incl data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
      (⟨n - 1, by omega⟩ : Fin (n + 1)) y,
    FreeMetabelian.Evaluation.linear_incl data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
      (⟨0, by omega⟩ : Fin n) x,
    FreeMetabelian.Evaluation.linear_incl data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
      (⟨n - 1, by omega⟩ : Fin n) y]

/-- The evaluation of every lower block relation lies in the last lower-central
layer, exactly because its class in `W_n` is zero. -/
theorem quadraticBlockRelationEvaluation_mem
    (z : POne n L × QOne n L data (by omega)) :
    evaluation n L data
        (quadraticBlockIncl n L hn (rDifferential n L data (by omega) z)) ∈
      lowerCentralSeries ℤ L n := by
  have hz := quadraticBlockRelationPrefix_mem_D n L data hn z
  rw [exact_D_augmentation n L data n (by omega)] at hz
  change (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ
      (prefixEvaluation (n := n) L data n
        (quadraticBlockRelationPrefix n L data hn z)) = 0 at hz
  change (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ
      (prefixEvaluation (n := n) L data n
        (quadraticBlockPrefixIncl n L hn
          (rDifferential n L data (by omega) z))) = 0 at hz
  rw [← evaluation_quadraticBlockIncl n L data hn] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mp hz

/-- A top homogeneous lift of each Smith-basis block relation evaluation. -/
private theorem quadraticBlockTopCorrectionOnBasis_mem
    (i : Sum (Fin (pSmith n L).rank)
      (Fin (qSmith n L data (by omega)).rank)) :
    evaluation n L data
        (quadraticBlockIncl n L hn
          (rDifferential n L data (by omega)
            (quadraticBlockRelationBasis n L data hn i))) ∈
      LinearMap.range (FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n) := by
  rw [FreeMetabelian.Evaluation.canonicalPiece_range_eq_lowerCentralSeries]
  exact quadraticBlockRelationEvaluation_mem n L data hn
    (quadraticBlockRelationBasis n L data hn i)

private def quadraticBlockTopCorrectionOnBasis
    (i : Sum (Fin (pSmith n L).rank)
      (Fin (qSmith n L data (by omega)).rank)) :
    FreeMetabelian.Piece (Generator L) n :=
  Classical.choose (quadraticBlockTopCorrectionOnBasis_mem n L data hn i)

private theorem quadraticBlockTopCorrectionOnBasis_spec
    (i : Sum (Fin (pSmith n L).rank)
      (Fin (qSmith n L data (by omega)).rank)) :
    FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n
          (quadraticBlockTopCorrectionOnBasis n L data hn i) =
      evaluation n L data
        (quadraticBlockIncl n L hn
          (rDifferential n L data (by omega)
            (quadraticBlockRelationBasis n L data hn i))) :=
  Classical.choose_spec (quadraticBlockTopCorrectionOnBasis_mem n L data hn i)

def quadraticBlockTopCorrection :
    (POne n L × QOne n L data (by omega)) →ₗ[ℤ]
      FreeMetabelian.Piece (Generator L) n := by
  let B := quadraticBlockRelationBasis n L data hn
  let lift :
      Sum (Fin (pSmith n L).rank) (Fin (qSmith n L data (by omega)).rank) →
        FreeMetabelian.Piece (Generator L) n :=
    quadraticBlockTopCorrectionOnBasis n L data hn
  exact B.constr ℤ lift

theorem evaluation_quadraticBlockTopCorrection
    (z : POne n L × QOne n L data (by omega)) :
    evaluation n L data
        (FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
          (quadraticBlockTopCorrection n L data hn z)) =
      evaluation n L data
        (quadraticBlockIncl n L hn (rDifferential n L data (by omega) z)) := by
  let B := quadraticBlockRelationBasis n L data hn
  have hmaps :
      (evaluation n L data).toLinearMap.comp
          ((FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)).comp
            (quadraticBlockTopCorrection n L data hn)) =
        (evaluation n L data).toLinearMap.comp
          ((quadraticBlockIncl n L hn).comp (rDifferential n L data (by omega))) := by
    apply B.ext
    intro i
    simp only [LinearMap.comp_apply]
    rw [quadraticBlockTopCorrection, Module.Basis.constr_basis]
    change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl ⟨n, by omega⟩
            (quadraticBlockTopCorrectionOnBasis n L data hn i)) = _
    rw [FreeMetabelian.Evaluation.linear_incl]
    exact quadraticBlockTopCorrectionOnBasis_spec n L data hn i
  exact LinearMap.congr_fun hmaps z

/-- A genuine full relation above every block relation, constructed exactly as
in the manuscript by subtracting a lift in homogeneous weight `n+1`. -/
def quadraticBlockFullRelationLift :
    (POne n L × QOne n L data (by omega)) →ₗ[ℤ] Relations n L data :=
  LinearMap.codRestrict (Relations n L data)
    ((quadraticBlockIncl n L hn).comp
        (rDifferential n L data (show 1 ≤ n by omega)) -
      (FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)).comp
        (quadraticBlockTopCorrection n L data hn)) (by
      intro z
      change evaluation n L data
          (quadraticBlockIncl n L hn (rDifferential n L data (by omega) z) -
            FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
              (quadraticBlockTopCorrection n L data hn z)) = 0
      rw [map_sub, evaluation_quadraticBlockTopCorrection]
      exact sub_self _)

/-- The tail convention in the displayed full-relation formula. -/
def quadraticBlockTopTail :
    (POne n L × QOne n L data (by omega)) →ₗ[ℤ]
      FreeMetabelian.Piece (Generator L) n :=
  -quadraticBlockTopCorrection n L data hn

theorem quadraticBlockFullRelationLift_prefix
    (z : POne n L × QOne n L data (by omega)) :
    relationPrefix n L data n (by omega)
        (quadraticBlockFullRelationLift n L data hn z) =
      quadraticBlockRelationPrefix n L data hn z := by
  change FreeMetabelian.Free.projectPrefix n (by omega)
      (quadraticBlockIncl n L hn (rDifferential n L data (by omega) z) -
        FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
          (quadraticBlockTopCorrection n L data hn z)) = _
  rw [map_sub,
    FreeMetabelian.Free.projectPrefix_weightIncl_eq_zero
      (X := Generator L) n n (by omega) (by omega) le_rfl,
    sub_zero]
  change FreeMetabelian.Free.projectPrefix n (by omega)
      (quadraticBlockIncl n L hn (rDifferential n L data (by omega) z)) =
    quadraticBlockPrefixIncl n L hn (rDifferential n L data (by omega) z)
  change FreeMetabelian.Free.projectPrefix (X := Generator L) (c := n + 1)
      n (by omega)
      (FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1) 0 (by omega)
          (rDifferential n L data (by omega) z).1 +
        FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
          (n - 1) (by omega)
          (rDifferential n L data (by omega) z).2) = _
  rw [map_add,
    FreeMetabelian.Free.projectPrefix_weightIncl_of_lt
      (X := Generator L) n 0 (by omega) (by omega) (by omega),
    FreeMetabelian.Free.projectPrefix_weightIncl_of_lt
      (X := Generator L) n (n - 1) (by omega) (by omega) (by omega)]
  rfl

/-- A full block relation is precisely its displayed lower homogeneous part
plus its (separately retained) top tail. -/
theorem quadraticBlockFullRelationLift_eq (z :
    POne n L × QOne n L data (by omega)) :
    (quadraticBlockFullRelationLift n L data hn z : FreeModel n L) =
      quadraticBlockIncl n L hn (rDifferential n L data (by omega) z) +
        FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
          (quadraticBlockTopTail n L data hn z) := by
  change quadraticBlockIncl n L hn (rDifferential n L data (by omega) z) -
      FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
        (quadraticBlockTopCorrection n L data hn z) = _
  rw [quadraticBlockTopTail, LinearMap.neg_apply, map_neg]
  abel

/-! ## The displayed Smith relations -/

/-- The manuscript generator `x_i` in homogeneous weight one. -/
def quadraticX (i : Fin (pSmith n L).rank) : FreeModel n L :=
  FreeMetabelian.Free.weightIncl (X := Generator L) 0 (by omega)
    ((pSmith n L).ambientBasis i)

/-- The chosen extension tail `B_i` in homogeneous weight `n`. -/
def quadraticB (i : Fin (pSmith n L).rank) : FreeModel n L :=
  FreeMetabelian.Free.weightIncl (X := Generator L) (n - 1) (by omega)
    (btilde n L data (by omega) ((pSmith n L).relationBasis i))

/-- The manuscript generator `y_α` in homogeneous weight `n`. -/
def quadraticY (a : Fin (qSmith n L data (by omega)).rank) : FreeModel n L :=
  FreeMetabelian.Free.weightIncl (X := Generator L) (n - 1) (by omega)
    ((qSmith n L data (by omega)).ambientBasis a)

/-- The full relation `ρ_i`. -/
def quadraticRho (i : Fin (pSmith n L).rank) : Relations n L data :=
  quadraticBlockFullRelationLift n L data hn
    ((pSmith n L).relationBasis i, 0)

/-- The full relation `σ_α`. -/
def quadraticSigma (a : Fin (qSmith n L data (by omega)).rank) :
    Relations n L data :=
  quadraticBlockFullRelationLift n L data hn
    (0, (qSmith n L data (by omega)).relationBasis a)

def quadraticRhoTail (i : Fin (pSmith n L).rank) :
    FreeMetabelian.Piece (Generator L) n :=
  quadraticBlockTopTail n L data hn ((pSmith n L).relationBasis i, 0)

def quadraticSigmaTail (a : Fin (qSmith n L data (by omega)).rank) :
    FreeMetabelian.Piece (Generator L) n :=
  quadraticBlockTopTail n L data hn
    (0, (qSmith n L data (by omega)).relationBasis a)

/-- The first displayed full-relation formula
`ρ_i=d_i x_i-B_i+t_i`. -/
theorem quadraticRho_eq (i : Fin (pSmith n L).rank) :
    (quadraticRho n L data hn i : FreeModel n L) =
      ((pSmith n L).diagonal i : ℤ) • quadraticX n L hn i -
        quadraticB n L data hn i +
          FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
            (quadraticRhoTail n L data hn i) := by
  rw [quadraticRho, quadraticRhoTail,
    quadraticBlockFullRelationLift_eq]
  rw [rDifferential_apply]
  change FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1) 0 (by omega)
        (((pSmith n L).relationBasis i : POne n L) : PZero L) +
      FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
        (n - 1) (by omega)
        (((0 : QOne n L data (by omega)) : QZero n L) -
          btilde n L data (by omega) ((pSmith n L).relationBasis i)) + _ = _
  rw [show ((0 : QOne n L data (by omega)) : QZero n L) = 0 from rfl,
    zero_sub, (pSmith n L).relation_eq, map_zsmul, map_neg]
  rw [quadraticX, quadraticB]
  abel

/-- The second displayed full-relation formula
`σ_α=e_α y_α+t'_α`. -/
theorem quadraticSigma_eq
    (a : Fin (qSmith n L data (by omega)).rank) :
    (quadraticSigma n L data hn a : FreeModel n L) =
      ((qSmith n L data (by omega)).diagonal a : ℤ) •
        quadraticY n L data hn a +
        FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
          (quadraticSigmaTail n L data hn a) := by
  rw [quadraticSigma, quadraticSigmaTail,
    quadraticBlockFullRelationLift_eq]
  rw [rDifferential_apply]
  change FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1) 0
        (by omega) (((0 : POne n L) : PZero L)) +
      FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
        (n - 1) (by omega)
        ((((qSmith n L data (by omega)).relationBasis a :
          QOne n L data (by omega)) : QZero n L) -
            btilde n L data (by omega) (0 : POne n L)) + _ = _
  rw [show ((0 : POne n L) : PZero L) = 0 from rfl, map_zero,
    show btilde n L data (by omega) (0 : POne n L) = 0 from map_zero _,
    sub_zero, zero_add, (qSmith n L data (by omega)).relation_eq, map_zsmul]
  rw [quadraticY]

/-- The realized quadratic block: it uses the presentation `R` of Point 5,
the fixed homogeneous inclusions, and genuine full relation labels. -/
structure RealizedQuadraticBlock where
  relationLift :
    (POne n L × QOne n L data (by omega)) →ₗ[ℤ] Relations n L data
  realizesPrefix : ∀ z,
    relationPrefix n L data n (by omega) (relationLift z) =
      quadraticBlockRelationPrefix n L data hn z

/-- The canonical realized block used below and nowhere chosen afresh. -/
def canonicalRealizedQuadraticBlock : RealizedQuadraticBlock n L data hn where
  relationLift := quadraticBlockFullRelationLift n L data hn
  realizesPrefix := quadraticBlockFullRelationLift_prefix n L data hn

/-! ## The four placed row families -/

/-- For `i<j`, the literal placed row
`rᵢⱼ ρᵢ xⱼ - xᵢ ρⱼ` of the manuscript. -/
def quadraticHorizontalPlacedRow
    (i j : Fin (pSmith n L).rank) : UEA ℤ (FreeModel n L) :=
  (Koszul.QuadraticUCT.ratio (pAugmentation n L) (pSmith n L) i j : ℤ) •
      (UniversalEnvelopingAlgebra.ι ℤ
          (quadraticRho n L data hn i : FreeModel n L) *
        UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn j)) -
    UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn i) *
      UniversalEnvelopingAlgebra.ι ℤ
        (quadraticRho n L data hn j : FreeModel n L)

/-- The primitive dictated by the horizontal placed row. -/
def quadraticHorizontalPrimitive
    (i j : Fin (pSmith n L).rank) : FreeModel n L :=
  -(Koszul.QuadraticUCT.ratio (pAugmentation n L) (pSmith n L) i j : ℤ) •
    ⁅quadraticB n L data hn i, quadraticX n L hn j⁆

/-- Exact collection of the horizontal row.  Its leading products cancel by
the ordered Smith divisibility identity, and all top-tail products have zero
one-factor component in weight `n+1`. -/
theorem quadraticHorizontalPlacedRow_proj
    {i j : Fin (pSmith n L).rank} (hij : i < j) :
    (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (quadraticHorizontalPlacedRow n L data hn i j) =
      UniversalEnvelopingAlgebra.ι ℤ
        (quadraticHorizontalPrimitive n L data hn i j) := by
  let r : ℤ := Koszul.QuadraticUCT.ratio
    (pAugmentation n L) (pSmith n L) i j
  let di : ℤ := (pSmith n L).diagonal i
  let dj : ℤ := (pSmith n L).diagonal j
  let xi := quadraticX n L hn i
  let xj := quadraticX n L hn j
  let Bi := quadraticB n L data hn i
  let Bj := quadraticB n L data hn j
  let ti : FreeModel n L :=
    FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
      (quadraticRhoTail n L data hn i)
  let tj : FreeModel n L :=
    FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
      (quadraticRhoTail n L data hn j)
  have hri : (quadraticRho n L data hn i : FreeModel n L) =
      di • xi - Bi + ti := quadraticRho_eq n L data hn i
  have hrj : (quadraticRho n L data hn j : FreeModel n L) =
      dj • xj - Bj + tj := quadraticRho_eq n L data hn j
  have hdr : r * di = dj := by
    have hnat := Koszul.QuadraticUCT.diagonal_mul_ratio
      (pAugmentation n L) (pSmith n L) hij.le
    change (Koszul.QuadraticUCT.ratio (pAugmentation n L)
        (pSmith n L) i j : ℤ) * ((pSmith n L).diagonal i : ℤ) =
      ((pSmith n L).diagonal j : ℤ)
    calc
      _ = ((Koszul.QuadraticUCT.ratio (pAugmentation n L)
            (pSmith n L) i j * (pSmith n L).diagonal i : ℕ) : ℤ) := by
              norm_num
      _ = ((pSmith n L).diagonal j : ℤ) := congrArg (fun z : ℕ ↦ (z : ℤ))
        (by simpa only [mul_comm] using hnat)
  have hBiX := adapted_proj_one_iota_weightIncl_mul_reverse n L data hn
    (n - 1) 0 (by omega) (by omega) (by omega) (by omega)
    (btilde n L data (by omega) ((pSmith n L).relationBasis i))
    ((pSmith n L).ambientBasis j)
  have hXiBj := adapted_proj_one_iota_weightIncl_mul_of_lt n L data hn
    0 (n - 1) (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i)
    (btilde n L data (by omega) ((pSmith n L).relationBasis j)) (n + 1)
  have hTiX := adapted_proj_one_iota_weightIncl_mul_of_overflow n L data hn
    n 0 (by omega) (by omega) (by omega) (by omega)
    (quadraticRhoTail n L data hn i) ((pSmith n L).ambientBasis j) (n + 1)
  have hXiT := adapted_proj_one_iota_weightIncl_mul_of_lt n L data hn
    0 n (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i) (quadraticRhoTail n L data hn j) (n + 1)
  have hBiX' : (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ Bi *
        UniversalEnvelopingAlgebra.ι ℤ xj) =
      UniversalEnvelopingAlgebra.ι ℤ ⁅Bi, xj⁆ := by
    have hw : n - 1 + 0 + 2 = n + 1 := by omega
    rw [hw] at hBiX
    simpa only [Bi, xj, quadraticB, quadraticX] using hBiX
  have hXiBj' : (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ xi *
        UniversalEnvelopingAlgebra.ι ℤ Bj) = 0 := by
    simpa only [xi, Bj, quadraticX, quadraticB] using hXiBj
  have hTiX' : (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ ti *
        UniversalEnvelopingAlgebra.ι ℤ xj) = 0 := by
    simpa only [ti, xj, quadraticX] using hTiX
  have hXiT' : (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ xi *
        UniversalEnvelopingAlgebra.ι ℤ tj) = 0 := by
    simpa only [xi, tj, quadraticX] using hXiT
  have hrow : quadraticHorizontalPlacedRow n L data hn i j =
      -r • (UniversalEnvelopingAlgebra.ι ℤ Bi *
        UniversalEnvelopingAlgebra.ι ℤ xj) +
      UniversalEnvelopingAlgebra.ι ℤ xi *
        UniversalEnvelopingAlgebra.ι ℤ Bj +
      r • (UniversalEnvelopingAlgebra.ι ℤ ti *
        UniversalEnvelopingAlgebra.ι ℤ xj) -
      UniversalEnvelopingAlgebra.ι ℤ xi *
        UniversalEnvelopingAlgebra.ι ℤ tj := by
    unfold quadraticHorizontalPlacedRow
    rw [hri, hrj]
    simp only [map_add, map_sub, map_zsmul]
    change r • ((di • UniversalEnvelopingAlgebra.ι ℤ xi -
          UniversalEnvelopingAlgebra.ι ℤ Bi +
          UniversalEnvelopingAlgebra.ι ℤ ti) *
        UniversalEnvelopingAlgebra.ι ℤ xj) -
      UniversalEnvelopingAlgebra.ι ℤ xi *
        (dj • UniversalEnvelopingAlgebra.ι ℤ xj -
          UniversalEnvelopingAlgebra.ι ℤ Bj +
          UniversalEnvelopingAlgebra.ι ℤ tj) = _
    rw [add_mul, sub_mul, mul_add, mul_sub]
    rw [smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, hdr]
    module
  rw [hrow]
  simp only [map_sub, map_add, map_zsmul]
  rw [hBiX', hXiBj', hTiX', hXiT']
  simp only [smul_zero, add_zero, sub_zero]
  rw [quadraticHorizontalPrimitive, map_zsmul]

/-- The placed `P₁⊗Q₀` row. -/
def quadraticPQPlacedRow
    (i : Fin (pSmith n L).rank)
    (a : Fin (qSmith n L data (by omega)).rank) : UEA ℤ (FreeModel n L) :=
  UniversalEnvelopingAlgebra.ι ℤ
      (quadraticRho n L data hn i : FreeModel n L) *
    UniversalEnvelopingAlgebra.ι ℤ (quadraticY n L data hn a)

/-- The placed `Q₁⊗P₀` row. -/
def quadraticQPPlacedRow
    (a : Fin (qSmith n L data (by omega)).rank)
    (i : Fin (pSmith n L).rank) : UEA ℤ (FreeModel n L) :=
  UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn i) *
    UniversalEnvelopingAlgebra.ι ℤ
      (quadraticSigma n L data hn a : FreeModel n L)

/-- The placed `Q₁⊗Q₀` row. -/
def quadraticQQPlacedRow
    (a b : Fin (qSmith n L data (by omega)).rank) : UEA ℤ (FreeModel n L) :=
  UniversalEnvelopingAlgebra.ι ℤ
      (quadraticSigma n L data hn a : FreeModel n L) *
    UniversalEnvelopingAlgebra.ι ℤ (quadraticY n L data hn b)

theorem quadraticPQPlacedRow_proj
    (i : Fin (pSmith n L).rank)
    (a : Fin (qSmith n L data (by omega)).rank) :
    (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (quadraticPQPlacedRow n L data hn i a) = 0 := by
  let xi := quadraticX n L hn i
  let Bi := quadraticB n L data hn i
  let ya := quadraticY n L data hn a
  let ti : FreeModel n L := FreeMetabelian.Free.weightIncl n (by omega)
    (quadraticRhoTail n L data hn i)
  have hri : (quadraticRho n L data hn i : FreeModel n L) =
      ((pSmith n L).diagonal i : ℤ) • xi - Bi + ti :=
    quadraticRho_eq n L data hn i
  have hxy := adapted_proj_one_iota_weightIncl_mul_of_lt n L data hn
    0 (n - 1) (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i)
    ((qSmith n L data (by omega)).ambientBasis a) (n + 1)
  have hBy := adapted_proj_one_iota_derived_mul_derived n L data hn
    (n - 1) (n - 1) (by omega) (by omega) (by omega) (by omega)
    (btilde n L data (by omega) ((pSmith n L).relationBasis i))
    ((qSmith n L data (by omega)).ambientBasis a) (n + 1)
  have hty := adapted_proj_one_iota_derived_mul_derived n L data hn
    n (n - 1) (by omega) (by omega) (by omega) (by omega)
    (quadraticRhoTail n L data hn i)
    ((qSmith n L data (by omega)).ambientBasis a) (n + 1)
  unfold quadraticPQPlacedRow
  change (adaptedWeightedBasis n L data hn).proj (n + 1) 1
    (UniversalEnvelopingAlgebra.ι ℤ
        (quadraticRho n L data hn i : FreeModel n L) *
      UniversalEnvelopingAlgebra.ι ℤ ya) = 0
  rw [hri]
  simp only [map_add, map_sub, map_zsmul, add_mul, sub_mul, smul_mul_assoc,
    map_zsmul]
  change ((pSmith n L).diagonal i : ℤ) •
      (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ xi *
          UniversalEnvelopingAlgebra.ι ℤ ya) -
      (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ Bi *
          UniversalEnvelopingAlgebra.ι ℤ ya) +
      (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ ti *
          UniversalEnvelopingAlgebra.ι ℤ ya) = 0
  simpa only [xi, Bi, ya, ti, quadraticX, quadraticB, quadraticY,
    hxy, hBy, hty, smul_zero, sub_zero, zero_add]

theorem quadraticQPPlacedRow_proj
    (a : Fin (qSmith n L data (by omega)).rank)
    (i : Fin (pSmith n L).rank) :
    (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (quadraticQPPlacedRow n L data hn a i) = 0 := by
  let xi := quadraticX n L hn i
  let ya := quadraticY n L data hn a
  let ta : FreeModel n L := FreeMetabelian.Free.weightIncl n (by omega)
    (quadraticSigmaTail n L data hn a)
  have hsa : (quadraticSigma n L data hn a : FreeModel n L) =
      ((qSmith n L data (by omega)).diagonal a : ℤ) • ya + ta :=
    quadraticSigma_eq n L data hn a
  have hxy := adapted_proj_one_iota_weightIncl_mul_of_lt n L data hn
    0 (n - 1) (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i)
    ((qSmith n L data (by omega)).ambientBasis a) (n + 1)
  have hxt := adapted_proj_one_iota_weightIncl_mul_of_lt n L data hn
    0 n (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i) (quadraticSigmaTail n L data hn a) (n + 1)
  unfold quadraticQPPlacedRow
  rw [hsa]
  simp only [map_add, map_zsmul, mul_add, mul_smul_comm,
    map_add, map_zsmul]
  change ((qSmith n L data (by omega)).diagonal a : ℤ) •
      (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ xi *
          UniversalEnvelopingAlgebra.ι ℤ ya) +
      (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ xi *
          UniversalEnvelopingAlgebra.ι ℤ ta) = 0
  simpa only [xi, ya, ta, quadraticX, quadraticY, hxy, hxt,
    smul_zero, add_zero]

theorem quadraticQQPlacedRow_proj
    (a b : Fin (qSmith n L data (by omega)).rank) :
    (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (quadraticQQPlacedRow n L data hn a b) = 0 := by
  let ya := quadraticY n L data hn a
  let yb := quadraticY n L data hn b
  let ta : FreeModel n L := FreeMetabelian.Free.weightIncl n (by omega)
    (quadraticSigmaTail n L data hn a)
  have hsa : (quadraticSigma n L data hn a : FreeModel n L) =
      ((qSmith n L data (by omega)).diagonal a : ℤ) • ya + ta :=
    quadraticSigma_eq n L data hn a
  have hyy := adapted_proj_one_iota_derived_mul_derived n L data hn
    (n - 1) (n - 1) (by omega) (by omega) (by omega) (by omega)
    ((qSmith n L data (by omega)).ambientBasis a)
    ((qSmith n L data (by omega)).ambientBasis b) (n + 1)
  have hty := adapted_proj_one_iota_derived_mul_derived n L data hn
    n (n - 1) (by omega) (by omega) (by omega) (by omega)
    (quadraticSigmaTail n L data hn a)
    ((qSmith n L data (by omega)).ambientBasis b) (n + 1)
  unfold quadraticQQPlacedRow
  rw [hsa]
  simp only [map_add, map_zsmul, add_mul, smul_mul_assoc,
    map_add, map_zsmul]
  change ((qSmith n L data (by omega)).diagonal a : ℤ) •
      (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ ya *
          UniversalEnvelopingAlgebra.ι ℤ yb) +
      (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ ta *
          UniversalEnvelopingAlgebra.ι ℤ yb) = 0
  simpa only [ya, yb, ta, quadraticY, hyy, hty, smul_zero, add_zero]

/-! ## Complete one-factor versions used by full-relation transport -/

/-- The horizontal row calculation before bracket-weight projection. -/
theorem quadraticHorizontalPlacedRow_factorProj
    {i j : Fin (pSmith n L).rank} (hij : i < j) :
    (adaptedWeightedBasis n L data hn).factorProj 1
        (quadraticHorizontalPlacedRow n L data hn i j) =
      UniversalEnvelopingAlgebra.ι ℤ
        (quadraticHorizontalPrimitive n L data hn i j) := by
  let r : ℤ := Koszul.QuadraticUCT.ratio
    (pAugmentation n L) (pSmith n L) i j
  let di : ℤ := (pSmith n L).diagonal i
  let dj : ℤ := (pSmith n L).diagonal j
  let xi := quadraticX n L hn i
  let xj := quadraticX n L hn j
  let Bi := quadraticB n L data hn i
  let Bj := quadraticB n L data hn j
  let ti : FreeModel n L :=
    FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
      (quadraticRhoTail n L data hn i)
  let tj : FreeModel n L :=
    FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)
      (quadraticRhoTail n L data hn j)
  have hri : (quadraticRho n L data hn i : FreeModel n L) =
      di • xi - Bi + ti := quadraticRho_eq n L data hn i
  have hrj : (quadraticRho n L data hn j : FreeModel n L) =
      dj • xj - Bj + tj := quadraticRho_eq n L data hn j
  have hdr : r * di = dj := by
    have hnat := Koszul.QuadraticUCT.diagonal_mul_ratio
      (pAugmentation n L) (pSmith n L) hij.le
    change (Koszul.QuadraticUCT.ratio (pAugmentation n L)
        (pSmith n L) i j : ℤ) * ((pSmith n L).diagonal i : ℤ) =
      ((pSmith n L).diagonal j : ℤ)
    calc
      _ = ((Koszul.QuadraticUCT.ratio (pAugmentation n L)
            (pSmith n L) i j * (pSmith n L).diagonal i : ℕ) : ℤ) := by
              norm_num
      _ = ((pSmith n L).diagonal j : ℤ) := congrArg (fun z : ℕ ↦ (z : ℤ))
        (by simpa only [mul_comm] using hnat)
  have hBiX := adapted_factorProj_one_iota_weightIncl_mul_reverse n L data hn
    (n - 1) 0 (by omega) (by omega) (by omega)
    (btilde n L data (by omega) ((pSmith n L).relationBasis i))
    ((pSmith n L).ambientBasis j)
  have hXiBj := adapted_factorProj_one_iota_weightIncl_mul_of_lt n L data hn
    0 (n - 1) (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i)
    (btilde n L data (by omega) ((pSmith n L).relationBasis j))
  have hTiX := adapted_factorProj_one_iota_weightIncl_mul_reverse n L data hn
    n 0 (by omega) (by omega) (by omega)
    (quadraticRhoTail n L data hn i) ((pSmith n L).ambientBasis j)
  have hXiT := adapted_factorProj_one_iota_weightIncl_mul_of_lt n L data hn
    0 n (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i) (quadraticRhoTail n L data hn j)
  have htopBracket : ⁅ti, xj⁆ = 0 := by
    funext k
    exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
      n 0 (by omega) (by omega) (quadraticRhoTail n L data hn i)
        ((pSmith n L).ambientBasis j) k (by omega)
  have hBiX' : (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ Bi *
        UniversalEnvelopingAlgebra.ι ℤ xj) =
      UniversalEnvelopingAlgebra.ι ℤ ⁅Bi, xj⁆ := by
    simpa only [Bi, xj, quadraticB, quadraticX] using hBiX
  have hXiBj' : (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ xi *
        UniversalEnvelopingAlgebra.ι ℤ Bj) = 0 := by
    simpa only [xi, Bj, quadraticX, quadraticB] using hXiBj
  have hTiX' : (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ ti *
        UniversalEnvelopingAlgebra.ι ℤ xj) = 0 := by
    rw [show (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ ti *
          UniversalEnvelopingAlgebra.ι ℤ xj) =
        UniversalEnvelopingAlgebra.ι ℤ ⁅ti, xj⁆ by
          simpa only [ti, xj, quadraticX] using hTiX,
      htopBracket, map_zero]
  have hXiT' : (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ xi *
        UniversalEnvelopingAlgebra.ι ℤ tj) = 0 := by
    simpa only [xi, tj, quadraticX] using hXiT
  have hrow : quadraticHorizontalPlacedRow n L data hn i j =
      -r • (UniversalEnvelopingAlgebra.ι ℤ Bi *
        UniversalEnvelopingAlgebra.ι ℤ xj) +
      UniversalEnvelopingAlgebra.ι ℤ xi *
        UniversalEnvelopingAlgebra.ι ℤ Bj +
      r • (UniversalEnvelopingAlgebra.ι ℤ ti *
        UniversalEnvelopingAlgebra.ι ℤ xj) -
      UniversalEnvelopingAlgebra.ι ℤ xi *
        UniversalEnvelopingAlgebra.ι ℤ tj := by
    unfold quadraticHorizontalPlacedRow
    rw [hri, hrj]
    simp only [map_add, map_sub, map_zsmul]
    change r • ((di • UniversalEnvelopingAlgebra.ι ℤ xi -
          UniversalEnvelopingAlgebra.ι ℤ Bi +
          UniversalEnvelopingAlgebra.ι ℤ ti) *
        UniversalEnvelopingAlgebra.ι ℤ xj) -
      UniversalEnvelopingAlgebra.ι ℤ xi *
        (dj • UniversalEnvelopingAlgebra.ι ℤ xj -
          UniversalEnvelopingAlgebra.ι ℤ Bj +
          UniversalEnvelopingAlgebra.ι ℤ tj) = _
    rw [add_mul, sub_mul, mul_add, mul_sub]
    rw [smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, hdr]
    module
  rw [hrow]
  simp only [map_sub, map_add, map_zsmul]
  rw [hBiX', hXiBj', hTiX', hXiT']
  simp only [smul_zero, add_zero, sub_zero]
  rw [quadraticHorizontalPrimitive, map_zsmul]

theorem quadraticPQPlacedRow_factorProj
    (i : Fin (pSmith n L).rank)
    (a : Fin (qSmith n L data (by omega)).rank) :
    (adaptedWeightedBasis n L data hn).factorProj 1
      (quadraticPQPlacedRow n L data hn i a) = 0 := by
  let xi := quadraticX n L hn i
  let Bi := quadraticB n L data hn i
  let ya := quadraticY n L data hn a
  let ti : FreeModel n L := FreeMetabelian.Free.weightIncl n (by omega)
    (quadraticRhoTail n L data hn i)
  have hri : (quadraticRho n L data hn i : FreeModel n L) =
      ((pSmith n L).diagonal i : ℤ) • xi - Bi + ti :=
    quadraticRho_eq n L data hn i
  have hxy := adapted_factorProj_one_iota_weightIncl_mul_of_lt n L data hn
    0 (n - 1) (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i)
    ((qSmith n L data (by omega)).ambientBasis a)
  have hBy := adapted_factorProj_one_iota_derived_mul_derived n L data hn
    (n - 1) (n - 1) (by omega) (by omega) (by omega) (by omega)
    (btilde n L data (by omega) ((pSmith n L).relationBasis i))
    ((qSmith n L data (by omega)).ambientBasis a)
  have hty := adapted_factorProj_one_iota_derived_mul_derived n L data hn
    n (n - 1) (by omega) (by omega) (by omega) (by omega)
    (quadraticRhoTail n L data hn i)
    ((qSmith n L data (by omega)).ambientBasis a)
  unfold quadraticPQPlacedRow
  change (adaptedWeightedBasis n L data hn).factorProj 1
    (UniversalEnvelopingAlgebra.ι ℤ
        (quadraticRho n L data hn i : FreeModel n L) *
      UniversalEnvelopingAlgebra.ι ℤ ya) = 0
  rw [hri]
  simp only [map_add, map_sub, map_zsmul, add_mul, sub_mul, smul_mul_assoc,
    map_zsmul]
  change ((pSmith n L).diagonal i : ℤ) •
      (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ xi *
          UniversalEnvelopingAlgebra.ι ℤ ya) -
      (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ Bi *
          UniversalEnvelopingAlgebra.ι ℤ ya) +
      (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ ti *
          UniversalEnvelopingAlgebra.ι ℤ ya) = 0
  simpa only [xi, Bi, ya, ti, quadraticX, quadraticB, quadraticY,
    hxy, hBy, hty, smul_zero, sub_zero, zero_add]

theorem quadraticQPPlacedRow_factorProj
    (a : Fin (qSmith n L data (by omega)).rank)
    (i : Fin (pSmith n L).rank) :
    (adaptedWeightedBasis n L data hn).factorProj 1
      (quadraticQPPlacedRow n L data hn a i) = 0 := by
  let xi := quadraticX n L hn i
  let ya := quadraticY n L data hn a
  let ta : FreeModel n L := FreeMetabelian.Free.weightIncl n (by omega)
    (quadraticSigmaTail n L data hn a)
  have hsa : (quadraticSigma n L data hn a : FreeModel n L) =
      ((qSmith n L data (by omega)).diagonal a : ℤ) • ya + ta :=
    quadraticSigma_eq n L data hn a
  have hxy := adapted_factorProj_one_iota_weightIncl_mul_of_lt n L data hn
    0 (n - 1) (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i)
    ((qSmith n L data (by omega)).ambientBasis a)
  have hxt := adapted_factorProj_one_iota_weightIncl_mul_of_lt n L data hn
    0 n (by omega) (by omega) (by omega)
    ((pSmith n L).ambientBasis i) (quadraticSigmaTail n L data hn a)
  unfold quadraticQPPlacedRow
  rw [hsa]
  simp only [map_add, map_zsmul, mul_add, mul_smul_comm,
    map_add, map_zsmul]
  change ((qSmith n L data (by omega)).diagonal a : ℤ) •
      (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ xi *
          UniversalEnvelopingAlgebra.ι ℤ ya) +
      (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ xi *
          UniversalEnvelopingAlgebra.ι ℤ ta) = 0
  simpa only [xi, ya, ta, quadraticX, quadraticY, hxy, hxt,
    smul_zero, add_zero]

theorem quadraticQQPlacedRow_factorProj
    (a b : Fin (qSmith n L data (by omega)).rank) :
    (adaptedWeightedBasis n L data hn).factorProj 1
      (quadraticQQPlacedRow n L data hn a b) = 0 := by
  let ya := quadraticY n L data hn a
  let yb := quadraticY n L data hn b
  let ta : FreeModel n L := FreeMetabelian.Free.weightIncl n (by omega)
    (quadraticSigmaTail n L data hn a)
  have hsa : (quadraticSigma n L data hn a : FreeModel n L) =
      ((qSmith n L data (by omega)).diagonal a : ℤ) • ya + ta :=
    quadraticSigma_eq n L data hn a
  have hyy := adapted_factorProj_one_iota_derived_mul_derived n L data hn
    (n - 1) (n - 1) (by omega) (by omega) (by omega) (by omega)
    ((qSmith n L data (by omega)).ambientBasis a)
    ((qSmith n L data (by omega)).ambientBasis b)
  have hty := adapted_factorProj_one_iota_derived_mul_derived n L data hn
    n (n - 1) (by omega) (by omega) (by omega) (by omega)
    (quadraticSigmaTail n L data hn a)
    ((qSmith n L data (by omega)).ambientBasis b)
  unfold quadraticQQPlacedRow
  rw [hsa]
  simp only [map_add, map_zsmul, add_mul, smul_mul_assoc,
    map_add, map_zsmul]
  change ((qSmith n L data (by omega)).diagonal a : ℤ) •
      (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ ya *
          UniversalEnvelopingAlgebra.ι ℤ yb) +
      (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ ta *
          UniversalEnvelopingAlgebra.ι ℤ yb) = 0
  simpa only [ya, yb, ta, quadraticY, hyy, hty, smul_zero, add_zero]

end

end LieRings.MetabelianVanishing
