import LieRings.DimensionSubring.MetabelianVanishing.QuadraticPBWCore

/-!
# The terminal quadratic PBW block: finite computation and transport

This file completes the realized block from `QuadraticPBWCore` by expanding a
cycle in the four Smith-basis families, computing its complete one-factor
component, proving the terminal character identity, and exposing the narrow
transport certificate used by the relative row collector.
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

local instance quadraticPBWBlockFintype : Fintype L := Fintype.ofFinite L
local instance : Finite (V L n) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)
local instance : Finite (W L n) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)
local instance : Module.Free ℤ (PZero L) := Module.Free.of_basis (pZeroBasis L)
local instance : Module.Finite ℤ (PZero L) := Module.Finite.of_basis (pZeroBasis L)
local instance : Module.Finite ℤ (POne n L) :=
  Module.Finite.of_fg (IsNoetherian.noetherian _)
local instance : Module.Free ℤ (POne n L) := Module.free_of_finite_type_torsion_free'

/-- A bracket of a weight-`n` piece with a generator is entirely in the
terminal homogeneous component. -/
theorem bracket_piece_generator_eq_weightIncl
    (b : FreeMetabelian.Piece (Generator L) (n - 1))
    (x : FreeMetabelian.Piece (Generator L) 0) :
    ⁅FreeMetabelian.Free.weightIncl (c := n + 1) (n - 1) (by omega) b,
      FreeMetabelian.Free.weightIncl (c := n + 1) 0 (by omega) x⁆ =
      FreeMetabelian.Free.weightIncl (c := n + 1) n (by omega)
        (FreeMetabelian.Free.weightProject (c := n + 1) n (by omega)
          ⁅FreeMetabelian.Free.weightIncl (c := n + 1) (n - 1) (by omega) b,
            FreeMetabelian.Free.weightIncl (c := n + 1) 0 (by omega) x⁆) := by
  funext k
  by_cases hk : k.val = n
  · have hkeq : k = ⟨n, by omega⟩ := Fin.ext hk
    rw [hkeq]
    change _ = FreeMetabelian.Free.incl ⟨n, by omega⟩
      (FreeMetabelian.Free.project ⟨n, by omega⟩ _) ⟨n, by omega⟩
    rw [FreeMetabelian.Free.incl_apply_same,
      FreeMetabelian.Free.project_apply]
  · rw [FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
      (c := n + 1) (n - 1) 0 (by omega) (by omega) b x k (by omega)]
    exact (FreeMetabelian.Free.incl_apply_of_ne
      ⟨n, by omega⟩ k (by intro h; exact hk (congrArg Fin.val h)) _).symm

/-- The terminal coordinate of a collected weight-`n`/weight-`1` bracket is
the coordinate of its evaluated Lie bracket. -/
theorem topCoord_bracket_piece_generator
    (b : FreeMetabelian.Piece (Generator L) (n - 1))
    (x : FreeMetabelian.Piece (Generator L) 0) :
    topCoord n L data
        (FreeMetabelian.Free.weightProject (c := n + 1) n (by omega)
          ⁅FreeMetabelian.Free.weightIncl (c := n + 1) (n - 1) (by omega) b,
            FreeMetabelian.Free.weightIncl (c := n + 1) 0 (by omega) x⁆) =
      data.topEquiv ⟨⁅FreeMetabelian.Evaluation.pieceEval data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n - 1) b,
        FreeMetabelian.Evaluation.canonicalGeneratorMap L x⁆, by
          have hb : FreeMetabelian.Evaluation.pieceEval data.metabelian
              (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n - 1) b ∈
                lowerCentralSeries ℤ L (n - 1) := by
            cases n with
            | zero => omega
            | succ q =>
              cases q with
              | zero => omega
              | succ r =>
                exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
                  data.metabelian
                  (FreeMetabelian.Evaluation.canonicalGeneratorMap L) r b
          have hbr : ⁅FreeMetabelian.Evaluation.pieceEval data.metabelian
                (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n - 1) b,
              FreeMetabelian.Evaluation.canonicalGeneratorMap L x⁆ ∈
              lowerCentralSeries ℤ L ((n - 1) + 1) := by
            change ⁅FreeMetabelian.Evaluation.pieceEval data.metabelian
                (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n - 1) b,
              FreeMetabelian.Evaluation.canonicalGeneratorMap L x⁆ ∈
              LieModule.lowerCentralSeries ℤ L L ((n - 1) + 1)
            rw [LieModule.lowerCentralSeries_succ ℤ L L (n - 1),
              LieSubmodule.lie_comm]
            exact LieSubmodule.lie_mem_lie hb (by simp)
          have heq : n - 1 + 1 = n := by omega
          have hseries : lowerCentralSeries ℤ L (n - 1 + 1) =
              lowerCentralSeries ℤ L n := congrArg (lowerCentralSeries ℤ L) heq
          rw [← hseries]
          exact hbr⟩ := by
  let B : FreeModel n L :=
    FreeMetabelian.Free.weightIncl (c := n + 1) (n - 1) (by omega) b
  let X : FreeModel n L :=
    FreeMetabelian.Free.weightIncl (c := n + 1) 0 (by omega) x
  let br : FreeModel n L := ⁅B, X⁆
  have hhom : br = FreeMetabelian.Free.weightIncl (c := n + 1) n (by omega)
      (FreeMetabelian.Free.weightProject (c := n + 1) n (by omega) br) := by
    funext k
    by_cases hk : k.val = n
    · have hkeq : k = ⟨n, by omega⟩ := Fin.ext hk
      rw [hkeq]
      change br ⟨n, by omega⟩ =
        FreeMetabelian.Free.incl ⟨n, by omega⟩
          (FreeMetabelian.Free.project ⟨n, by omega⟩ br) ⟨n, by omega⟩
      rw [FreeMetabelian.Free.incl_apply_same,
        FreeMetabelian.Free.project_apply]
    · dsimp only [br, B, X]
      rw [FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
        (c := n + 1) (n - 1) 0 (by omega) (by omega) b x k (by omega)]
      exact (FreeMetabelian.Free.incl_apply_of_ne
        ⟨n, by omega⟩ k (by intro h; exact hk (congrArg Fin.val h)) _).symm
  change terminalEval n L data ⟨FreeMetabelian.Free.weightIncl n (by omega)
      (FreeMetabelian.Free.weightProject n (by omega) br), _⟩ = _
  let top := FreeMetabelian.Free.weightIncl (c := n + 1) n (by omega)
    (FreeMetabelian.Free.weightProject (c := n + 1) n (by omega) br)
  have htopmem : evaluation n L data top ∈ lowerCentralSeries ℤ L n := by
    dsimp only [top]
    rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
    change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl (⟨n, by omega⟩ : Fin (n + 1))
            (FreeMetabelian.Free.weightProject n (by omega) br)) ∈ _
    rw [FreeMetabelian.Evaluation.linear_incl]
    change FreeMetabelian.Evaluation.pieceEval data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n
        (FreeMetabelian.Free.weightProject n (by omega) br) ∈
          lowerCentralSeries ℤ L n
    cases n with
    | zero => omega
    | succ q =>
      exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
        data.metabelian (FreeMetabelian.Evaluation.canonicalGeneratorMap L) q _
  have hbrmem : evaluation n L data br ∈ lowerCentralSeries ℤ L n := by
    rw [hhom]
    exact htopmem
  let ztop : TopPreimage n L data := ⟨top, htopmem⟩
  let zbr : TopPreimage n L data := ⟨br, hbrmem⟩
  have hz : ztop = zbr := by
    apply Subtype.ext
    exact hhom.symm
  change terminalEval n L data ztop = _
  rw [hz]
  change data.topEquiv ⟨evaluation n L data br, _⟩ = _
  apply congrArg data.topEquiv
  apply Subtype.ext
  change evaluation n L data br =
    ⁅FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n - 1) b,
      FreeMetabelian.Evaluation.canonicalGeneratorMap L x⁆
  rw [LieHom.map_lie]
  dsimp only [B, X]
  rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
  change ⁅FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl ⟨n - 1, by omega⟩ b),
      FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl ⟨0, by omega⟩ x)⁆ = _
  rw [FreeMetabelian.Evaluation.linear_incl,
    FreeMetabelian.Evaluation.linear_incl]
  rfl

/-- On the ordered Smith tensor basis, the terminal coordinate of the PBW
bracket is exactly the terminal Koszul cocycle. -/
theorem topCoord_quadratic_bracket_eq_terminalPhi
    (i j : Fin (pSmith n L).rank) :
    topCoord n L data
        (FreeMetabelian.Free.weightProject (c := n + 1) n (by omega)
          ⁅FreeMetabelian.Free.weightIncl (c := n + 1) (n - 1) (by omega)
              (btilde n L data (by omega) ((pSmith n L).relationBasis i)),
            FreeMetabelian.Free.weightIncl (c := n + 1) 0 (by omega)
              ((pSmith n L).ambientBasis j)⁆) =
      terminalPhi n L data hn
        (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L) (i, j)) := by
  rw [topCoord_bracket_piece_generator n L data hn]
  rw [terminalPhi_oneBasis n L data hn]
  rw [terminalPair_tmul]
  change data.topEquiv _ =
    Theta n L data n hn le_rfl
      (pTail n L (by omega) ((pSmith n L).relationBasis i) ⊗ₜ[ℤ]
        terminalTooth n L ((pSmith n L).ambientBasis j))
  rw [← qAugmentation_btilde n L data (by omega)
    ((pSmith n L).relationBasis i)]
  have htooth :
      terminalTooth n L ((pSmith n L).ambientBasis j) =
        SymmetricPower.tprod ℤ (fun _ : Fin (n + 1 - n) ↦
          (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L
              ((pSmith n L).ambientBasis j))) := by
    rw [terminalTooth, LinearMap.comp_apply, LinearMap.comp_apply]
    rw [SymmetricPower.degreeOne_apply]
    rw [SymmetricPower.reindex_tprod]
    apply congrArg (SymmetricPower.tprod ℤ)
    funext k
    haveI : Subsingleton (Fin (n + 1 - n)) :=
      ⟨fun a b ↦ Fin.ext (by omega)⟩
    have hk : k = (Fin.castOrderIso (by omega : 1 = n + 1 - n)) 0 :=
      Subsingleton.elim _ _
    rw [hk]
    rfl
  rw [htooth]
  exact (Theta_terminal_tmul n L data hn
    (FreeMetabelian.Evaluation.pieceEval data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n - 1)
      (btilde n L data (by omega) ((pSmith n L).relationBasis i)))
    (by
      cases n with
      | zero => omega
      | succ q =>
        cases q with
        | zero => omega
        | succ r =>
          exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
            data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L) r _)
    (FreeMetabelian.Evaluation.canonicalGeneratorMap L
      ((pSmith n L).ambientBasis j))).symm

def quadraticProjectedCycle
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    Koszul.cyclesOne (pPresentation n L) 1 :=
  Koszul.PresentationHomology.cyclesMap
    (rPresentation n L data (by omega)) (pPresentation n L)
    (rToP n L data (by omega)) 1 c

def quadraticHorizontalCoefficient
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1)
    (i j : Fin (pSmith n L).rank) : ℤ :=
  Koszul.QuadraticUCT.horizontalCoefficient
    (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L)
    (quadraticProjectedCycle n L data hn c) i j

def quadraticBlockSymOneBasis :
    Module.Basis
      (Sum (Fin (pSmith n L).rank)
        (Fin (qSmith n L data (by omega)).rank)) ℤ
      (Sym[ℤ] (Fin 1) (PZero L × QZero n L)) :=
  ((pSmith n L).ambientBasis.prod
    (qSmith n L data (by omega)).ambientBasis).map
      (SymmetricPower.degreeOneLinearEquiv
        ((pSmith n L).ambientBasis.prod
          (qSmith n L data (by omega)).ambientBasis)).symm

def quadraticBlockOneBasis :
    Module.Basis
      ((Sum (Fin (pSmith n L).rank)
          (Fin (qSmith n L data (by omega)).rank)) ×
        Sum (Fin (pSmith n L).rank)
          (Fin (qSmith n L data (by omega)).rank)) ℤ
      (Koszul.One (rPresentation n L data (by omega)) 1) := by
  let _tower : IsScalarTower ℤ ℤ
      (Sym[ℤ] (Fin 1) (PZero L × QZero n L)) :=
    ⟨fun r s x ↦ by change (r * s) • x = r • s • x; exact mul_smul r s x⟩
  letI := _tower
  exact Module.Basis.tensorProduct (R := ℤ) (S := ℤ)
    (quadraticBlockRelationBasis n L data hn)
    (quadraticBlockSymOneBasis n L data hn)

def quadraticBlockCoefficient
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1)
    (a b : Sum (Fin (pSmith n L).rank)
      (Fin (qSmith n L data (by omega)).rank)) : ℤ :=
  (quadraticBlockOneBasis n L data hn).repr c.1 (a, b)

def quadraticBlockPlacedWord
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    UEA ℤ (FreeModel n L) :=
  (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
      if hij : i < j then
        quadraticHorizontalCoefficient n L data hn c i j •
          quadraticHorizontalPlacedRow n L data hn i j else 0) +
  (∑ i : Fin (pSmith n L).rank,
      ∑ a : Fin (qSmith n L data (by omega)).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inl i) (Sum.inr a) •
          quadraticPQPlacedRow n L data hn i a) +
  (∑ a : Fin (qSmith n L data (by omega)).rank,
      ∑ i : Fin (pSmith n L).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inl i) •
          quadraticQPPlacedRow n L data hn a i) +
  (∑ a : Fin (qSmith n L data (by omega)).rank,
      ∑ b : Fin (qSmith n L data (by omega)).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inr b) •
          quadraticQQPlacedRow n L data hn a b)

def quadraticBlockPrimitive
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    FreeModel n L :=
  ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
      if hij : i < j then
        quadraticHorizontalCoefficient n L data hn c i j •
          quadraticHorizontalPrimitive n L data hn i j else 0

/-- The terminal homogeneous piece of the complete one-factor PBW
primitive.  This is the literal sum of the collected brackets, before
applying the cyclic terminal coordinate. -/
def quadraticBlockPrimitivePiece
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    FreeMetabelian.Piece (Generator L) n :=
  ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
      if hij : i < j then
        quadraticHorizontalCoefficient n L data hn c i j •
          (-(Koszul.QuadraticUCT.ratio (pAugmentation n L)
              (pSmith n L) i j : ℤ) •
            FreeMetabelian.Free.weightProject (c := n + 1) n (by omega)
              ⁅FreeMetabelian.Free.weightIncl (c := n + 1) (n - 1) (by omega)
                  (btilde n L data (by omega) ((pSmith n L).relationBasis i)),
                FreeMetabelian.Free.weightIncl (c := n + 1) 0 (by omega)
                  ((pSmith n L).ambientBasis j)⁆)
      else 0

/-- The complete one-factor primitive obtained from the four placed row
families is homogeneous of terminal weight, with the displayed piece. -/
theorem quadraticBlockPrimitive_eq_weightIncl
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    quadraticBlockPrimitive n L data hn c =
      FreeMetabelian.Free.weightIncl (c := n + 1) n (by omega)
        (quadraticBlockPrimitivePiece n L data hn c) := by
  simp only [quadraticBlockPrimitive, quadraticBlockPrimitivePiece, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, dite_true, map_zsmul]
    rw [quadraticHorizontalPrimitive, quadraticB, quadraticX]
    exact congrArg
      (fun z : FreeModel n L ↦
        quadraticHorizontalCoefficient n L data hn c i j •
          -(Koszul.QuadraticUCT.ratio (pAugmentation n L)
            (pSmith n L) i j : ℤ) • z)
      (bracket_piece_generator_eq_weightIncl n L hn _ _)
  · simp only [hij, dite_false, map_zero]

/-- The block value is, by definition, the terminal evaluation of the
complete one-factor PBW primitive. -/
def quadraticBlockValue
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    ZMod (2 ^ data.exponent) :=
  topCoord n L data (quadraticBlockPrimitivePiece n L data hn c)

theorem quadraticBlockPlacedWord_proj
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (quadraticBlockPlacedWord n L data hn c) =
      UniversalEnvelopingAlgebra.ι ℤ
        (quadraticBlockPrimitive n L data hn c) := by
  simp only [quadraticBlockPlacedWord, quadraticBlockPrimitive, map_sum]
  simp only [map_add]
  rw [show (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (∑ i : Fin (pSmith n L).rank,
        ∑ a : Fin (qSmith n L data (by omega)).rank,
          quadraticBlockCoefficient n L data hn c (Sum.inl i) (Sum.inr a) •
            quadraticPQPlacedRow n L data hn i a) = 0 by
      simp only [map_sum, map_zsmul, quadraticPQPlacedRow_proj,
        smul_zero, Finset.sum_const_zero]]
  rw [show (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (∑ a : Fin (qSmith n L data (by omega)).rank,
        ∑ i : Fin (pSmith n L).rank,
          quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inl i) •
            quadraticQPPlacedRow n L data hn a i) = 0 by
      simp only [map_sum, map_zsmul, quadraticQPPlacedRow_proj,
        smul_zero, Finset.sum_const_zero]]
  rw [show (adaptedWeightedBasis n L data hn).proj (n + 1) 1
      (∑ a : Fin (qSmith n L data (by omega)).rank,
        ∑ b : Fin (qSmith n L data (by omega)).rank,
          quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inr b) •
            quadraticQQPlacedRow n L data hn a b) = 0 by
      simp only [map_sum, map_zsmul, quadraticQQPlacedRow_proj,
        smul_zero, Finset.sum_const_zero]]
  simp only [add_zero]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, dite_true, map_zsmul]
    rw [quadraticHorizontalPlacedRow_proj n L data hn hij]
  · simp only [hij, dite_false, map_zero]

/-- The exact complete one-factor projection of the four-family placed block,
now displayed as a single terminal homogeneous Lie piece. -/
theorem quadraticBlockPlacedWord_proj_eq_weightIncl
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (quadraticBlockPlacedWord n L data hn c) =
      UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl (c := n + 1) n (by omega)
          (quadraticBlockPrimitivePiece n L data hn c)) := by
  rw [quadraticBlockPlacedWord_proj,
    quadraticBlockPrimitive_eq_weightIncl]

/-- The *complete* one-factor projection of the four-family block.  This is
stronger than the preceding exact-weight statement and is the form stable
under adding a full relation. -/
theorem quadraticBlockPlacedWord_factorProj
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    (adaptedWeightedBasis n L data hn).factorProj 1
        (quadraticBlockPlacedWord n L data hn c) =
      UniversalEnvelopingAlgebra.ι ℤ
        (quadraticBlockPrimitive n L data hn c) := by
  simp only [quadraticBlockPlacedWord, quadraticBlockPrimitive, map_sum]
  simp only [map_add]
  rw [show (adaptedWeightedBasis n L data hn).factorProj 1
      (∑ i : Fin (pSmith n L).rank,
        ∑ a : Fin (qSmith n L data (by omega)).rank,
          quadraticBlockCoefficient n L data hn c (Sum.inl i) (Sum.inr a) •
            quadraticPQPlacedRow n L data hn i a) = 0 by
      simp only [map_sum, map_zsmul, quadraticPQPlacedRow_factorProj,
        smul_zero, Finset.sum_const_zero]]
  rw [show (adaptedWeightedBasis n L data hn).factorProj 1
      (∑ a : Fin (qSmith n L data (by omega)).rank,
        ∑ i : Fin (pSmith n L).rank,
          quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inl i) •
            quadraticQPPlacedRow n L data hn a i) = 0 by
      simp only [map_sum, map_zsmul, quadraticQPPlacedRow_factorProj,
        smul_zero, Finset.sum_const_zero]]
  rw [show (adaptedWeightedBasis n L data hn).factorProj 1
      (∑ a : Fin (qSmith n L data (by omega)).rank,
        ∑ b : Fin (qSmith n L data (by omega)).rank,
          quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inr b) •
            quadraticQQPlacedRow n L data hn a b) = 0 by
      simp only [map_sum, map_zsmul, quadraticQQPlacedRow_factorProj,
        smul_zero, Finset.sum_const_zero]]
  simp only [add_zero]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, dite_true, map_zsmul]
    rw [quadraticHorizontalPlacedRow_factorProj n L data hn hij]
  · simp only [hij, dite_false, map_zero]

theorem quadraticBlockPlacedWord_factorProj_eq_weightIncl
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    (adaptedWeightedBasis n L data hn).factorProj 1
        (quadraticBlockPlacedWord n L data hn c) =
      UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl (c := n + 1) n (by omega)
          (quadraticBlockPrimitivePiece n L data hn c)) := by
  rw [quadraticBlockPlacedWord_factorProj,
    quadraticBlockPrimitive_eq_weightIncl]

def quadraticBlockNumerator
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) : ℤ :=
  -∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
      if hij : i < j then
        quadraticHorizontalCoefficient n L data hn c i j *
          (Koszul.QuadraticUCT.ratio (pAugmentation n L) (pSmith n L) i j : ℤ) *
          terminalLiftEntry n L data hn i j else 0

def quadraticBlockCoordinateValue
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    ZMod (2 ^ data.exponent) :=
  quadraticBlockNumerator n L data hn c

/-- Evaluation of the complete PBW primitive is the manuscript's integral
Smith-coordinate numerator modulo the terminal exponent. -/
theorem quadraticBlockValue_eq_coordinate
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    quadraticBlockValue n L data hn c =
      quadraticBlockCoordinateValue n L data hn c := by
  rw [quadraticBlockValue, quadraticBlockPrimitivePiece,
    quadraticBlockCoordinateValue, quadraticBlockNumerator]
  simp only [map_sum, Int.cast_neg, Int.cast_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, dite_true, map_zsmul]
    rw [topCoord_quadratic_bracket_eq_terminalPhi n L data hn]
    rw [← terminalLift_cast n L data hn]
    rw [terminalLift_oneBasis]
    simp only [neg_smul, zsmul_eq_mul, Int.cast_mul]
    ring
  · simp only [hij, dite_false, map_zero, Int.cast_zero, neg_zero]

def quadraticProjectedClass
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    Koszul.homologyOne (pPresentation n L) 1 :=
  (Koszul.boundariesOne (pPresentation n L) 1).mkQ
    (quadraticProjectedCycle n L data hn c)

theorem quadraticProjectedClass_eq_horizontal_sum
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    quadraticProjectedClass n L data hn c =
      ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            Koszul.QuadraticUCT.horizontalClass (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) hij
        else 0 := by
  let cp := quadraticProjectedCycle n L data hn c
  let qmap := (Koszul.boundariesOne (pPresentation n L) 1).mkQ
  change qmap cp = _
  have hcp : cp =
      ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            Koszul.QuadraticUCT.horizontalCycle (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) hij
        else 0 := by
    have hbase := Koszul.QuadraticUCT.cycle_eq_horizontalExpansion
      (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L) cp
    apply Subtype.ext
    rw [hbase]
    simp only [Koszul.QuadraticUCT.horizontalExpansion, Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij, dite_true, Submodule.coe_smul_of_tower,
        Koszul.QuadraticUCT.horizontalCycle]
      rfl
    · simp only [hij, dite_false, Submodule.coe_zero]
  rw [hcp]
  calc
    qmap (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            Koszul.QuadraticUCT.horizontalCycle (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) hij
        else 0) =
      ∑ i : Fin (pSmith n L).rank, qmap
        (∑ j : Fin (pSmith n L).rank,
          if hij : i < j then
            quadraticHorizontalCoefficient n L data hn c i j •
              Koszul.QuadraticUCT.horizontalCycle (pAugmentation n L)
                (pAugmentation_surjective n L) (pSmith n L) hij
          else 0) := by
            simpa only [Finset.sum_filter] using
              (map_sum qmap (fun i : Fin (pSmith n L).rank ↦
                ∑ j : Fin (pSmith n L).rank,
                  if hij : i < j then
                    quadraticHorizontalCoefficient n L data hn c i j •
                      Koszul.QuadraticUCT.horizontalCycle (pAugmentation n L)
                        (pAugmentation_surjective n L) (pSmith n L) hij
                  else 0) Finset.univ)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        qmap (∑ j : Fin (pSmith n L).rank,
            if hij : i < j then
              quadraticHorizontalCoefficient n L data hn c i j •
                Koszul.QuadraticUCT.horizontalCycle (pAugmentation n L)
                  (pAugmentation_surjective n L) (pSmith n L) hij
            else 0) =
          ∑ j : Fin (pSmith n L).rank, qmap
            (if hij : i < j then
              quadraticHorizontalCoefficient n L data hn c i j •
                Koszul.QuadraticUCT.horizontalCycle (pAugmentation n L)
                  (pAugmentation_surjective n L) (pSmith n L) hij
            else 0) := by
              simpa only [Finset.sum_filter] using
                (map_sum qmap (fun j : Fin (pSmith n L).rank ↦
                  if hij : i < j then
                    quadraticHorizontalCoefficient n L data hn c i j •
                      Koszul.QuadraticUCT.horizontalCycle (pAugmentation n L)
                        (pAugmentation_surjective n L) (pSmith n L) hij
                  else 0) Finset.univ)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hij : i < j
          · simp only [hij, dite_true,
              Koszul.QuadraticUCT.horizontalClass]
            exact map_zsmul qmap _ _
          · simp only [hij, dite_false, map_zero]
            rfl

theorem quadraticBlockValue_capstone_presentation
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    LieRings.zmodToRatCircle (2 ^ data.exponent)
        (quadraticBlockValue n L data hn c) =
      -etaPresentation n L data hn (quadraticProjectedClass n L data hn c) := by
  rw [quadraticProjectedClass_eq_horizontal_sum]
  let eta := etaPresentation n L data hn
  have heta : eta
      (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            Koszul.QuadraticUCT.horizontalClass (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) hij
        else 0) =
      ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            eta (Koszul.QuadraticUCT.horizontalClass (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) hij)
        else 0 := by
    rw [map_sum eta]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sum eta]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij, dite_true]
      exact map_zsmul eta _ _
    · simp only [hij, dite_false, map_zero]
  change LieRings.zmodToRatCircle (2 ^ data.exponent)
      (quadraticBlockValue n L data hn c) = -eta _
  calc
    LieRings.zmodToRatCircle (2 ^ data.exponent)
        (quadraticBlockValue n L data hn c) =
      -(∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            eta (Koszul.QuadraticUCT.horizontalClass (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) hij)
        else 0) := by
          simp_rw [eta, etaPresentation_horizontal n L data hn]
          rw [quadraticBlockValue_eq_coordinate,
            quadraticBlockCoordinateValue,
            LieRings.zmodToRatCircle_intCast]
          let circleMap : ℚ →+ LieRings.RatCircle := QuotientAddGroup.mk' _
          let ratSum : ℚ :=
            ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
              if hij : i < j then
                (quadraticHorizontalCoefficient n L data hn c i j : ℚ) *
                  (Koszul.QuadraticUCT.ratio (pAugmentation n L)
                    (pSmith n L) i j : ℚ) *
                  (terminalLiftEntry n L data hn i j : ℚ)
              else 0
          have hnum : ((quadraticBlockNumerator n L data hn c : ℤ) : ℚ) =
              -ratSum := by
            simp only [quadraticBlockNumerator, ratSum, Int.cast_neg,
              Int.cast_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hij : i < j
            · simp only [hij, dite_true, Int.cast_mul]
              norm_num
            · simp only [hij, dite_false, Int.cast_zero]
          calc
            ((((quadraticBlockNumerator n L data hn c : ℤ) : ℚ) /
                ((2 ^ data.exponent : ℕ) : ℚ)) : LieRings.RatCircle) =
                ((-ratSum / ((2 ^ data.exponent : ℕ) : ℚ)) :
                  LieRings.RatCircle) := congrArg
                    (fun z : ℚ ↦ (z : LieRings.RatCircle)) (by rw [hnum])
            _ = circleMap (-ratSum / ((2 ^ data.exponent : ℕ) : ℚ)) := rfl
            _ = circleMap (-ratSum / (2 ^ data.exponent : ℚ)) := by
              norm_num
            _ =
                circleMap (-(ratSum / (2 ^ data.exponent : ℚ))) := by
                  congr 1
                  ring
            _ = -circleMap (ratSum / (2 ^ data.exponent : ℚ)) :=
              map_neg circleMap _
            _ = -∑ i : Fin (pSmith n L).rank,
                circleMap ((∑ j : Fin (pSmith n L).rank,
                  if hij : i < j then
                    (quadraticHorizontalCoefficient n L data hn c i j : ℚ) *
                      (Koszul.QuadraticUCT.ratio (pAugmentation n L)
                        (pSmith n L) i j : ℚ) *
                      (terminalLiftEntry n L data hn i j : ℚ)
                  else 0) / (2 ^ data.exponent : ℚ)) := by
                    congr 1
                    dsimp only [ratSum]
                    rw [Finset.sum_div]
                    exact map_sum circleMap _ Finset.univ
            _ = -∑ i : Fin (pSmith n L).rank,
                ∑ j : Fin (pSmith n L).rank,
                  circleMap ((if hij : i < j then
                    (quadraticHorizontalCoefficient n L data hn c i j : ℚ) *
                      (Koszul.QuadraticUCT.ratio (pAugmentation n L)
                        (pSmith n L) i j : ℚ) *
                      (terminalLiftEntry n L data hn i j : ℚ)
                  else 0) / (2 ^ data.exponent : ℚ)) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [Finset.sum_div]
                    exact map_sum circleMap _ Finset.univ
            _ = _ := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hij : i < j
              · simp only [hij, dite_true]
                change circleMap
                    (((quadraticHorizontalCoefficient n L data hn c i j : ℚ) *
                      (Koszul.QuadraticUCT.ratio (pAugmentation n L)
                        (pSmith n L) i j : ℚ) *
                      (terminalLiftEntry n L data hn i j : ℚ)) /
                        (2 ^ data.exponent : ℚ)) =
                    quadraticHorizontalCoefficient n L data hn c i j •
                      circleMap
                        (((Koszul.QuadraticUCT.ratio (pAugmentation n L)
                          (pSmith n L) i j : ℚ) *
                          (terminalLiftEntry n L data hn i j : ℚ)) /
                            (2 ^ data.exponent : ℚ))
                rw [← map_zsmul circleMap]
                congr 1
                simp only [zsmul_eq_mul]
                ring
              · simp only [hij, dite_false, zero_div, map_zero]
    _ = -eta (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            Koszul.QuadraticUCT.horizontalClass (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) hij
        else 0) := congrArg Neg.neg heta.symm

/-- The presentation-independent class of the block cycle. -/
def quadraticCanonicalClassR
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    Koszul.FirstDerivedSymmetricPower 1 (W L n) :=
  Koszul.Presentation.homologyComparisonEquiv
    (rPresentation n L data (by omega)) 1
      ((Koszul.boundariesOne (rPresentation n L data (by omega)) 1).mkQ c)

theorem etaTerminal_map_pi_canonicalClassR
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    etaTerminal n L data hn
        (Koszul.FirstDerivedSymmetricPower.map 1 (pi L n)
          (quadraticCanonicalClassR n L data hn c)) =
      etaPresentation n L data hn (quadraticProjectedClass n L data hn c) := by
  let R := rPresentation n L data (by omega)
  let P := pPresentation n L
  let F := rToP n L data (by omega)
  let eR := Koszul.Presentation.homologyComparisonEquiv R 1
  let eP := Koszul.Presentation.homologyComparisonEquiv P 1
  let y := (Koszul.boundariesOne R 1).mkQ c
  have hnat := Koszul.Presentation.homologyComparison_natural R P F 1
  have hnatY := LinearMap.congr_fun hnat y
  have hnatY' : eP (Koszul.PresentationHomology.map R P F 1 y) =
      Koszul.FirstDerivedSymmetricPower.map 1 (pi L n) (eR y) := by
    simpa only [LinearMap.comp_apply] using hnatY
  change etaPresentation n L data hn
      (eP.symm (Koszul.FirstDerivedSymmetricPower.map 1 (pi L n) (eR y))) =
    etaPresentation n L data hn (quadraticProjectedClass n L data hn c)
  rw [← hnatY', eP.symm_apply_apply]
  congr 1

/-- Point 6 capstone, with the cycle explicitly crossing the comparison
equivalence before applying the terminal character. -/
theorem quadraticBlockValue_capstone
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    LieRings.zmodToRatCircle (2 ^ data.exponent)
        (quadraticBlockValue n L data hn c) =
      -etaTerminal n L data hn
        (Koszul.FirstDerivedSymmetricPower.map 1 (pi L n)
          (quadraticCanonicalClassR n L data hn c)) := by
  rw [etaTerminal_map_pi_canonicalClassR]
  exact quadraticBlockValue_capstone_presentation n L data hn c

/-! ## The narrow terminal transport certificate -/

/-- The canonical source presentation `Dₙ → Aₙ` of `Wₙ`. -/
abbrev terminalSourcePresentation :=
  presentation n L data n (by omega) (by omega)

/-- Projection of a full relation to the canonical terminal relation module. -/
def terminalRelationPrefixMap :
    Relations n L data →ₗ[ℤ] D n L data n (by omega) :=
  LinearMap.codRestrict (D n L data n (by omega))
    ((prLE n L n (by omega)).comp (Relations n L data).subtype) (by
      intro rho
      exact ⟨rho, rfl⟩)

theorem terminalRelationPrefixMap_surjective :
    Function.Surjective (terminalRelationPrefixMap n L data) := by
  rintro ⟨x, rho, hrho⟩
  refine ⟨rho, ?_⟩
  apply Subtype.ext
  exact hrho

private theorem terminalFullLift_exists (hn : 2 ≤ n) :
    ∃ s : D n L data n (by omega) →ₗ[ℤ] Relations n L data,
      (terminalRelationPrefixMap n L data).comp s = LinearMap.id := by
  let P := terminalSourcePresentation n L data hn
  letI : Module.Free ℤ (D n L data n (by omega)) := P.relFree
  let target := LinearMap.id (R := ℤ) (M := D n L data n (by omega))
  exact Module.projective_lifting_property
    (terminalRelationPrefixMap n L data) target
    (terminalRelationPrefixMap_surjective n L data)

/-- A linear choice of a genuine full relation above each terminal prefix. -/
def terminalFullLift (hn : 2 ≤ n) :
    D n L data n (by omega) →ₗ[ℤ] Relations n L data :=
  Classical.choose (terminalFullLift_exists n L data hn)

theorem terminalFullLift_prefix (d : D n L data n (by omega)) :
    terminalRelationPrefixMap n L data (terminalFullLift n L data hn d) = d := by
  have hs := Classical.choose_spec (terminalFullLift_exists n L data hn)
  have hd := LinearMap.congr_fun hs d
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hd

/-- Two full relations above the same terminal prefix differ only in the
homogeneous top coordinate.  The difference remains a full relation; the
displayed top coordinate is not separately coerced to `Relations`. -/
theorem relation_sub_terminalFullLift_eq_top
    (rho : Relations n L data) (d : D n L data n (by omega))
    (hprefix : terminalRelationPrefixMap n L data rho = d) :
    (rho : FreeModel n L) - (terminalFullLift n L data hn d : FreeModel n L) =
      FreeMetabelian.Free.weightIncl n (by omega)
        (FreeMetabelian.Free.weightProject n (by omega)
          ((rho : FreeModel n L) -
            (terminalFullLift n L data hn d : FreeModel n L))) := by
  have hzero : FreeMetabelian.Free.projectPrefix n (by omega)
      ((rho : FreeModel n L) -
        (terminalFullLift n L data hn d : FreeModel n L)) = 0 := by
    rw [map_sub]
    change (terminalRelationPrefixMap n L data rho).1 -
      (terminalRelationPrefixMap n L data
        (terminalFullLift n L data hn d)).1 = 0
    rw [hprefix, terminalFullLift_prefix]
    exact sub_self _
  funext k
  by_cases hk : k.val = n
  · have hkeq : k = ⟨n, by omega⟩ := Fin.ext hk
    rw [hkeq]
    change ((rho : FreeModel n L) -
        (terminalFullLift n L data hn d : FreeModel n L)) ⟨n, by omega⟩ =
      FreeMetabelian.Free.incl ⟨n, by omega⟩
        (FreeMetabelian.Free.project ⟨n, by omega⟩
          ((rho : FreeModel n L) -
            (terminalFullLift n L data hn d : FreeModel n L))) ⟨n, by omega⟩
    rw [FreeMetabelian.Free.incl_apply_same,
      FreeMetabelian.Free.project_apply]
  · have hklt : k.val < n := by omega
    have hz := congrFun hzero ⟨k.val, hklt⟩
    change ((rho : FreeModel n L) -
      (terminalFullLift n L data hn d : FreeModel n L)) k = 0 at hz
    rw [hz]
    exact (FreeMetabelian.Free.incl_apply_of_ne
      ⟨n, by omega⟩ k (by intro h; exact hk (congrArg Fin.val h)) _).symm

/-- A realization defect keeps the full relation and the homogeneous top
correction as different objects.  The displayed equality is the exact
replacement orientation used by the row certificate. -/
structure TerminalRealizationDefect (sourceLift blockLift : FreeModel n L) where
  delta : Relations n L data
  top : FreeMetabelian.Piece (Generator L) n
  source_eq : sourceLift = blockLift + (delta : FreeModel n L) -
    FreeMetabelian.Free.weightIncl n (by omega) top

/-- The source inclusion `Aₙ → F` used in generator realization defects. -/
def terminalSourceGeneratorLift : A L n →ₗ[ℤ] FreeModel n L :=
  FreeMetabelian.Free.prefixIncl n (by omega)

/-- The block inclusion after applying a strict presentation map. -/
def terminalBlockGeneratorLift
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) :
    A L n →ₗ[ℤ] FreeModel n L :=
  (quadraticBlockIncl n L hn).comp g.genMap

private theorem terminalGeneratorDifference_mem
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (w : A L n) :
    evaluation n L data
        (terminalSourceGeneratorLift n L w -
          terminalBlockGeneratorLift n L data hn g w) ∈
      lowerCentralSeries ℤ L n := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have hsource : evaluation n L data (terminalSourceGeneratorLift n L w) =
      prefixEvaluation (n := n) L data n w := by
    rw [terminalSourceGeneratorLift, evaluation,
      FreeMetabelian.Evaluation.canonicalEvaluation, prefixEvaluation]
    exact FreeMetabelian.Evaluation.linear_prefixIncl data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n (by omega) w
  have hblock : evaluation n L data
      (terminalBlockGeneratorLift n L data hn g w) =
      prefixEvaluation (n := n) L data n
        (quadraticBlockPrefixIncl n L hn (g.genMap w)) := by
    change evaluation n L data (quadraticBlockIncl n L hn (g.genMap w)) = _
    simpa only [Prod.eta] using
      evaluation_quadraticBlockIncl n L data hn
        (g.genMap w).1 (g.genMap w).2
  rw [map_sub, hsource, hblock]
  change augmentation (n := n) L data n w -
      augmentation (n := n) L data n
        (quadraticBlockPrefixIncl n L hn (g.genMap w)) = 0
  rw [show augmentation (n := n) L data n
      (quadraticBlockPrefixIncl n L hn (g.genMap w)) =
        rAugmentation n L data (by omega) (g.genMap w) by
      simpa only [Prod.eta] using
        augmentation_quadraticBlockPrefixIncl n L data hn
          (g.genMap w).1 (g.genMap w).2]
  have hg := LinearMap.congr_fun g.induces w
  change rAugmentation n L data (by omega) (g.genMap w) =
    augmentation (n := n) L data n w at hg
  rw [hg, sub_self]

/-- The evaluation of a terminal homogeneous piece, cod-restricted to the
last lower-central layer. -/
def terminalPieceEvaluation :
    FreeMetabelian.Piece (Generator L) n →ₗ[ℤ]
      lowerCentralSeries ℤ L n :=
  LinearMap.codRestrict (lowerCentralSeries ℤ L n)
    (FreeMetabelian.Evaluation.pieceEval data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n) (by
        intro x
        cases n with
        | zero =>
          change FreeMetabelian.Evaluation.pieceEval data.metabelian
              (FreeMetabelian.Evaluation.canonicalGeneratorMap L) 0 x ∈
            LieModule.lowerCentralSeries ℤ L L 0
          rw [LieModule.lowerCentralSeries_zero]
          exact LieSubmodule.mem_top _
        | succ q =>
          exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
            data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L) q x)

theorem terminalPieceEvaluation_surjective :
    Function.Surjective (terminalPieceEvaluation n L data hn) := by
  intro z
  have hz : z.1 ∈ LinearMap.range
      (FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n) := by
    rw [FreeMetabelian.Evaluation.canonicalPiece_range_eq_lowerCentralSeries]
    exact z.2
  obtain ⟨x, hx⟩ := hz
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

/-- The evaluation difference between the source and block generator lifts,
as an element of the last lower-central layer. -/
def terminalGeneratorDifference
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) :
    A L n →ₗ[ℤ] lowerCentralSeries ℤ L n :=
  LinearMap.codRestrict (lowerCentralSeries ℤ L n)
    ((evaluation n L data).toLinearMap.comp
        (terminalSourceGeneratorLift n L) -
      (evaluation n L data).toLinearMap.comp
        (terminalBlockGeneratorLift n L data hn g))
    (by
      intro w
      change evaluation n L data (terminalSourceGeneratorLift n L w) -
          evaluation n L data (terminalBlockGeneratorLift n L data hn g w) ∈
        lowerCentralSeries ℤ L n
      rw [← map_sub]
      exact terminalGeneratorDifference_mem n L data hn g w)

private theorem terminalGeneratorTopCorrection_exists
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) :
    ∃ t : A L n →ₗ[ℤ] FreeMetabelian.Piece (Generator L) n,
      (terminalPieceEvaluation n L data hn).comp t =
        -(terminalGeneratorDifference n L data hn g) := by
  let P := terminalSourcePresentation n L data hn
  letI : Module.Free ℤ (A L n) := P.genFree
  exact Module.projective_lifting_property
    (terminalPieceEvaluation n L data hn)
    (-(terminalGeneratorDifference n L data hn g))
    (terminalPieceEvaluation_surjective n L data hn)

/-- Linear top corrections for all generator-basis realization defects. -/
def terminalGeneratorTopCorrection
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) :
    A L n →ₗ[ℤ] FreeMetabelian.Piece (Generator L) n :=
  Classical.choose (terminalGeneratorTopCorrection_exists n L data hn g)

theorem terminalGeneratorTopCorrection_spec
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) (w : A L n) :
    terminalPieceEvaluation n L data hn
        (terminalGeneratorTopCorrection n L data hn g w) =
      -terminalGeneratorDifference n L data hn g w := by
  have h := Classical.choose_spec
    (terminalGeneratorTopCorrection_exists n L data hn g)
  exact LinearMap.congr_fun h w

/-- The genuine full relation in the generator realization defect. -/
def terminalGeneratorDefectRelation
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) :
    A L n →ₗ[ℤ] Relations n L data :=
  LinearMap.codRestrict (Relations n L data)
    (terminalSourceGeneratorLift n L -
      terminalBlockGeneratorLift n L data hn g +
      (FreeMetabelian.Free.weightIncl n (by omega)).comp
        (terminalGeneratorTopCorrection n L data hn g)) (by
      intro w
      change evaluation n L data
        (terminalSourceGeneratorLift n L w -
          terminalBlockGeneratorLift n L data hn g w +
          FreeMetabelian.Free.weightIncl n (by omega)
            (terminalGeneratorTopCorrection n L data hn g w)) = 0
      rw [map_add]
      have ht := terminalGeneratorTopCorrection_spec n L data hn g w
      have ht' : evaluation n L data
          (FreeMetabelian.Free.weightIncl n (by omega)
            (terminalGeneratorTopCorrection n L data hn g w)) =
          -(evaluation n L data
            (terminalSourceGeneratorLift n L w -
              terminalBlockGeneratorLift n L data hn g w)) := by
        have htval := congrArg Subtype.val ht
        calc
          _ = FreeMetabelian.Evaluation.pieceEval data.metabelian
                (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n
                  (terminalGeneratorTopCorrection n L data hn g w) := by
              rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
              exact FreeMetabelian.Evaluation.linear_incl data.metabelian
                (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
                (⟨n, by omega⟩ : Fin (n + 1))
                (terminalGeneratorTopCorrection n L data hn g w)
          _ = _ := by
            simpa only [terminalPieceEvaluation, terminalGeneratorDifference,
              LinearMap.codRestrict_apply, LinearMap.neg_apply,
              LinearMap.sub_apply, LinearMap.comp_apply, map_sub] using htval
      rw [ht', add_neg_cancel])

/-- The basiswise generator defect promised by the transport plan. -/
def terminalGeneratorRealizationDefect
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) (w : A L n) :
    TerminalRealizationDefect n L data
      (terminalSourceGeneratorLift n L w)
      (terminalBlockGeneratorLift n L data hn g w) where
  delta := terminalGeneratorDefectRelation n L data hn g w
  top := terminalGeneratorTopCorrection n L data hn g w
  source_eq := by
    change terminalSourceGeneratorLift n L w =
      terminalBlockGeneratorLift n L data hn g w +
        (terminalSourceGeneratorLift n L w -
          terminalBlockGeneratorLift n L data hn g w +
          FreeMetabelian.Free.weightIncl n (by omega)
            (terminalGeneratorTopCorrection n L data hn g w)) -
        FreeMetabelian.Free.weightIncl n (by omega)
          (terminalGeneratorTopCorrection n L data hn g w)
    abel

/-- Relation generators have an even simpler defect: both chosen labels are
already full relations. -/
def terminalRelationRealizationDefect
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (d : D n L data n (by omega)) :
    TerminalRealizationDefect n L data
      (terminalFullLift n L data hn d : FreeModel n L)
      (quadraticBlockFullRelationLift n L data hn (g.relMap d) :
        FreeModel n L) where
  delta := terminalFullLift n L data hn d -
    quadraticBlockFullRelationLift n L data hn (g.relMap d)
  top := 0
  source_eq := by
    change (terminalFullLift n L data hn d : FreeModel n L) =
      (quadraticBlockFullRelationLift n L data hn (g.relMap d) :
          FreeModel n L) +
        ((terminalFullLift n L data hn d : FreeModel n L) -
          (quadraticBlockFullRelationLift n L data hn (g.relMap d) :
            FreeModel n L)) -
        FreeMetabelian.Free.weightIncl n (by omega) 0
    rw [map_zero, sub_zero]
    abel

/-- A full relation, regarded as a terminal preimage.  Its evaluation is zero;
the point of retaining the full relation here is that its isolated top
homogeneous component need not evaluate to zero. -/
def relationTopPreimage (rho : Relations n L data) : TopPreimage n L data :=
  ⟨rho.1, by
    change evaluation n L data rho.1 ∈ lowerCentralSeries ℤ L n
    have hrho : evaluation n L data rho.1 = 0 := rho.property
    rw [hrho]
    exact Submodule.zero_mem _⟩

@[simp] theorem terminalEval_relationTopPreimage
    (rho : Relations n L data) :
    terminalEval n L data (relationTopPreimage n L data rho) = 0 := by
  change data.topEquiv ⟨evaluation n L data rho.1, _⟩ = 0
  have hrho : evaluation n L data rho.1 = 0 := rho.property
  calc
    data.topEquiv ⟨evaluation n L data rho.1, _⟩ =
        data.topEquiv (0 : lowerCentralSeries ℤ L n) := by
      apply congrArg data.topEquiv
      exact Subtype.ext hrho
    _ = 0 := data.topEquiv.map_zero

/-- A marked relative word records its literal UEA word and the *actual* full
one-factor primitive selected by the terminal PBW projection.  The primitive
is already a `TopPreimage`, so its terminal value is not an unconstrained
label. -/
structure TerminalMarkedWord where
  word : UEA ℤ (FreeModel n L)
  primitive : TopPreimage n L data
  projection_eq :
    (adaptedWeightedBasis n L data hn).factorProj 1 word =
      UniversalEnvelopingAlgebra.ι ℤ (primitive : FreeModel n L)

namespace TerminalMarkedWord

def value (w : TerminalMarkedWord n L data hn) :
    ZMod (2 ^ data.exponent) :=
  terminalEval n L data w.primitive

/-- Zero marked word.  This and the two operations below are used only to
assemble the finite signed terminal ledger from its literal local moves. -/
def zero : TerminalMarkedWord n L data hn where
  word := 0
  primitive := 0
  projection_eq := by simp

/-- Addition of marked words, retaining the complete PBW primitive. -/
def add (u v : TerminalMarkedWord n L data hn) :
    TerminalMarkedWord n L data hn where
  word := u.word + v.word
  primitive := u.primitive + v.primitive
  projection_eq := by
    rw [map_add, u.projection_eq, v.projection_eq]
    exact (map_add
      (UniversalEnvelopingAlgebra.ι ℤ :
        LieHom ℤ (FreeModel n L) (UEA ℤ (FreeModel n L))) _ _).symm

/-- Integer scaling of a marked word. -/
def zsmul (z : ℤ) (u : TerminalMarkedWord n L data hn) :
    TerminalMarkedWord n L data hn where
  word := z • u.word
  primitive := z • u.primitive
  projection_eq := by
    rw [map_zsmul, u.projection_eq]
    exact (map_zsmul
      (UniversalEnvelopingAlgebra.ι ℤ :
        LieHom ℤ (FreeModel n L) (UEA ℤ (FreeModel n L))) z _).symm

@[simp] theorem zero_word :
    (zero n L data hn).word = 0 := rfl

@[simp] theorem add_word (u v : TerminalMarkedWord n L data hn) :
    (u.add n L data hn v).word = u.word + v.word := rfl

@[simp] theorem zsmul_word (z : ℤ) (u : TerminalMarkedWord n L data hn) :
    (u.zsmul n L data hn z).word = z • u.word := rfl

@[simp] theorem zero_value : (zero n L data hn).value = 0 := by
  simp [TerminalMarkedWord.value, zero]

@[simp] theorem add_value (u v : TerminalMarkedWord n L data hn) :
    (u.add n L data hn v).value = u.value + v.value := by
  simp [TerminalMarkedWord.value, add]

@[simp] theorem zsmul_value (z : ℤ)
    (u : TerminalMarkedWord n L data hn) :
    (u.zsmul n L data hn z).value = z • u.value := by
  simp [TerminalMarkedWord.value, zsmul]

end TerminalMarkedWord

namespace TerminalMarkedWord

/-- Equality of literal UEA words forces equality of their recorded complete
one-factor primitives. -/
theorem primitive_eq_of_word_eq
    {u v : TerminalMarkedWord n L data hn} (hword : u.word = v.word) :
    u.primitive = v.primitive := by
  apply Subtype.ext
  apply canonicalMap_injective_of_freeModulePBW
    ℤ (FreeModel n L) (AdaptedIndex n L data hn)
    (adaptedWeightedBasis n L data hn).basis
    (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis)
  rw [← u.projection_eq, ← v.projection_eq, hword]

end TerminalMarkedWord

/-- The canonical marked word attached to the complete four-family block. -/
def quadraticBlockMarkedWord
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    TerminalMarkedWord n L data hn where
  word := quadraticBlockPlacedWord n L data hn c
  primitive := topInclPreimage n L data
    (quadraticBlockPrimitivePiece n L data hn c)
  projection_eq := by
    simpa only [topInclPreimage] using
      quadraticBlockPlacedWord_factorProj_eq_weightIncl n L data hn c

@[simp] theorem quadraticBlockMarkedWord_value
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    (quadraticBlockMarkedWord n L data hn c).value =
      quadraticBlockValue n L data hn c := by
  rfl

/-- The exact and deliberately small list of moves allowed in the terminal
transport.  Each endpoint carries its proved PBW primitive.  Hence a
certificate no longer assumes the equality of terminal values in its indices.
The `Relations` arguments below are full relations; in
`realizationReplacement`, `delta` is a full relation whereas `top` is only a
homogeneous top piece. -/
inductive TerminalRowCertificate :
    TerminalMarkedWord n L data hn → TerminalMarkedWord n L data hn → Prop
  | refl (w : TerminalMarkedWord n L data hn) : TerminalRowCertificate w w
  | basisExpansion {u v : TerminalMarkedWord n L data hn}
      (hword : u.word = v.word) :
      TerminalRowCertificate u v
  | zeroFactorOne {u : TerminalMarkedWord n L data hn}
      (hproj : (adaptedWeightedBasis n L data hn).factorProj 1 u.word = 0) :
      TerminalRowCertificate u (TerminalMarkedWord.zero n L data hn)
  | ordinaryAdjacentSwap {u v : TerminalMarkedWord n L data hn}
      (x y : FreeModel n L)
      (hu : u.word = UniversalEnvelopingAlgebra.ι ℤ x *
        UniversalEnvelopingAlgebra.ι ℤ y)
      (hv : v.word = UniversalEnvelopingAlgebra.ι ℤ y *
          UniversalEnvelopingAlgebra.ι ℤ x +
        UniversalEnvelopingAlgebra.ι ℤ ⁅x, y⁆) : TerminalRowCertificate u v
  | fullRelationAdjacentSwap {u v : TerminalMarkedWord n L data hn}
      (rho : Relations n L data) (x : FreeModel n L)
      (hu : u.word = UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
        UniversalEnvelopingAlgebra.ι ℤ x)
      (hv : v.word = UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) +
        UniversalEnvelopingAlgebra.ι ℤ ⁅(rho : FreeModel n L), x⁆) :
      TerminalRowCertificate u v
  | realizationReplacement {u v : TerminalMarkedWord n L data hn}
      (sourceLift blockLift : FreeModel n L) (delta : Relations n L data)
      (top : FreeMetabelian.Piece (Generator L) n)
      (h : sourceLift = blockLift + (delta : FreeModel n L) -
        FreeMetabelian.Free.weightIncl n (by omega) top)
      (right : UEA ℤ (FreeModel n L))
      (hu : u.word = UniversalEnvelopingAlgebra.ι ℤ sourceLift * right)
      (hv : v.word = UniversalEnvelopingAlgebra.ι ℤ blockLift * right +
          UniversalEnvelopingAlgebra.ι ℤ (delta : FreeModel n L) * right -
          UniversalEnvelopingAlgebra.ι ℤ
            (FreeMetabelian.Free.weightIncl n (by omega) top) * right) :
      TerminalRowCertificate u v
  | relativeBoundary {u v : TerminalMarkedWord n L data hn}
      (rho sigma : Relations n L data)
      (hu : u.word = UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
          UniversalEnvelopingAlgebra.ι ℤ (sigma : FreeModel n L) -
        UniversalEnvelopingAlgebra.ι ℤ (sigma : FreeModel n L) *
          UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) -
        UniversalEnvelopingAlgebra.ι ℤ
          ⁅(rho : FreeModel n L), (sigma : FreeModel n L)⁆)
      (hv : v.word = 0) :
      TerminalRowCertificate u v
  | relationCorrection {u v : TerminalMarkedWord n L data hn}
      (rho : Relations n L data) (z : ℤ)
      (hword : v.word = u.word + z •
        UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L)) :
      TerminalRowCertificate u v
  | add {u₁ u₂ v₁ v₂ : TerminalMarkedWord n L data hn}
      (h₁ : TerminalRowCertificate u₁ v₁)
      (h₂ : TerminalRowCertificate u₂ v₂) :
      TerminalRowCertificate
        (u₁.add n L data hn u₂) (v₁.add n L data hn v₂)
  | zsmul {u v : TerminalMarkedWord n L data hn} (z : ℤ)
      (h : TerminalRowCertificate u v) :
      TerminalRowCertificate
        (u.zsmul n L data hn z) (v.zsmul n L data hn z)
  | trans {u v w : TerminalMarkedWord n L data hn}
      (huv : TerminalRowCertificate u v)
      (hvw : TerminalRowCertificate v w) : TerminalRowCertificate u w

theorem TerminalRowCertificate.value_eq
    {u v : TerminalMarkedWord n L data hn}
    (h : TerminalRowCertificate n L data hn u v) : u.value = v.value := by
  induction h with
  | refl => rfl
  | basisExpansion hword =>
      exact congrArg (terminalEval n L data)
        (TerminalMarkedWord.primitive_eq_of_word_eq n L data hn hword)
  | @zeroFactorOne u hproj =>
      have hprimitive : u.primitive = 0 := by
        apply Subtype.ext
        apply canonicalMap_injective_of_freeModulePBW
          ℤ (FreeModel n L) (AdaptedIndex n L data hn)
          (adaptedWeightedBasis n L data hn).basis
          (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
            (adaptedWeightedBasis n L data hn).basis)
        rw [← u.projection_eq, hproj]
        exact (map_zero
          (UniversalEnvelopingAlgebra.ι ℤ :
            LieHom ℤ (FreeModel n L) (UEA ℤ (FreeModel n L)))).symm
      change terminalEval n L data u.primitive = terminalEval n L data 0
      rw [hprimitive]
  | ordinaryAdjacentSwap x y hu hv =>
      apply congrArg (terminalEval n L data)
      apply TerminalMarkedWord.primitive_eq_of_word_eq n L data hn
      exact hu.trans
        ((LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L) x y).trans
          hv.symm)
  | fullRelationAdjacentSwap rho x hu hv =>
      apply congrArg (terminalEval n L data)
      apply TerminalMarkedWord.primitive_eq_of_word_eq n L data hn
      exact hu.trans
        ((LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L)
          (rho : FreeModel n L) x).trans hv.symm)
  | realizationReplacement sourceLift blockLift delta top h right hu hv =>
      apply congrArg (terminalEval n L data)
      apply TerminalMarkedWord.primitive_eq_of_word_eq n L data hn
      calc
        _ = UniversalEnvelopingAlgebra.ι ℤ sourceLift * right := hu
        _ = UniversalEnvelopingAlgebra.ι ℤ
              (blockLift + (delta : FreeModel n L) -
                FreeMetabelian.Free.weightIncl n (by omega) top) * right := by
              rw [h]
        _ = UniversalEnvelopingAlgebra.ι ℤ blockLift * right +
              UniversalEnvelopingAlgebra.ι ℤ (delta : FreeModel n L) * right -
              UniversalEnvelopingAlgebra.ι ℤ
                (FreeMetabelian.Free.weightIncl n (by omega) top) * right := by
              simp only [map_add, map_sub, add_mul, sub_mul]
        _ = _ := hv.symm
  | relativeBoundary rho sigma hu hv =>
      apply congrArg (terminalEval n L data)
      apply TerminalMarkedWord.primitive_eq_of_word_eq n L data hn
      calc
        _ = UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
              UniversalEnvelopingAlgebra.ι ℤ (sigma : FreeModel n L) -
            UniversalEnvelopingAlgebra.ι ℤ (sigma : FreeModel n L) *
              UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) -
            UniversalEnvelopingAlgebra.ι ℤ
              ⁅(rho : FreeModel n L), (sigma : FreeModel n L)⁆ := hu
        _ = 0 := by
          rw [LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L)
            (rho : FreeModel n L) (sigma : FreeModel n L)]
          module
        _ = _ := hv.symm
  | @relationCorrection u' v' rho z hword =>
      have hp : v'.primitive = u'.primitive +
          z • relationTopPreimage n L data rho := by
        apply Subtype.ext
        apply canonicalMap_injective_of_freeModulePBW
          ℤ (FreeModel n L) (AdaptedIndex n L data hn)
          (adaptedWeightedBasis n L data hn).basis
          (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
            (adaptedWeightedBasis n L data hn).basis)
        rw [← v'.projection_eq, hword, map_add, map_zsmul,
          (adaptedWeightedBasis n L data hn).factorProj_one_iota,
          u'.projection_eq]
        change UniversalEnvelopingAlgebra.ι ℤ (u'.primitive : FreeModel n L) +
            z • UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) =
          UniversalEnvelopingAlgebra.ι ℤ
            ((u'.primitive : FreeModel n L) + z • (rho : FreeModel n L))
        rw [map_add, map_zsmul]
      change terminalEval n L data _ = terminalEval n L data _
      rw [hp, map_add, map_zsmul, terminalEval_relationTopPreimage,
        smul_zero, add_zero]
  | add h₁ h₂ ih₁ ih₂ =>
      simpa using congrArg₂ (fun x y ↦ x + y) ih₁ ih₂
  | zsmul z h ih =>
      simpa using congrArg (fun x ↦ z • x) ih
  | trans _ _ huv hvw => exact huv.trans hvw

/-- Evaluation of the actual finite relation-on-the-left row list. -/
def terminalPacketWord
    (rows : (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ) :
    UEA ℤ (FreeModel n L) :=
  rows.sum (fun p z ↦ z •
    (UniversalEnvelopingAlgebra.ι ℤ (p.1 : FreeModel n L) * p.2))

/-- Linear form of `terminalPacketWord`, used when a collected row list is
itself assembled from finitely many sublists. -/
def terminalPacketWordLinear :
    ((Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ) →ₗ[ℤ]
      UEA ℤ (FreeModel n L) :=
  Finsupp.linearCombination ℤ (fun p ↦
    UniversalEnvelopingAlgebra.ι ℤ (p.1 : FreeModel n L) * p.2)

@[simp] theorem terminalPacketWordLinear_apply
    (rows : (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ) :
    terminalPacketWordLinear n L data rows =
      terminalPacketWord n L data rows := rfl

/-- The packet supplied by the relative row calculation of Point 7.  Its map
`g` is a strict lift of the identity of `Wₙ`, and `actualRows` is genuinely
finite.  The certificate uses only the constructors above. -/
structure TerminalQuadraticPacket where
  g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega)) LinearMap.id
  cycle : Koszul.cyclesOne (terminalSourcePresentation n L data hn) 1
  actualRows : (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ
  actualMarked : TerminalMarkedWord n L data hn
  actualMarked_word : actualMarked.word =
    terminalPacketWord n L data actualRows
  certificate : TerminalRowCertificate n L data hn
    actualMarked
    (quadraticBlockMarkedWord n L data hn
      (Koszul.PresentationHomology.cyclesMap
        (terminalSourcePresentation n L data hn)
        (rPresentation n L data (by omega)) g 1 cycle))

/-- The actual terminal primitive carried by a packet. -/
def TerminalQuadraticPacket.orientedPrimitive
    (p : TerminalQuadraticPacket n L data hn) :
    ZMod (2 ^ data.exponent) :=
  p.actualMarked.value

/-- Output of the narrow transport: the transported cycle, its literal
definition as `K₂(g)(cycle)`, the row certificate, and the resulting equality
of oriented primitive and canonical block value. -/
structure TransportedTerminalPacket
    (p : TerminalQuadraticPacket n L data hn) where
  cycleR : Koszul.cyclesOne (rPresentation n L data (by omega)) 1
  cycleR_eq : cycleR = Koszul.PresentationHomology.cyclesMap
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega)) p.g 1 p.cycle
  certificate : TerminalRowCertificate n L data hn
    p.actualMarked (quadraticBlockMarkedWord n L data hn cycleR)
  primitive_eq : p.orientedPrimitive = quadraticBlockValue n L data hn cycleR

def transportTerminalPacket
    (p : TerminalQuadraticPacket n L data hn) :
    TransportedTerminalPacket n L data hn p := by
  let cR := Koszul.PresentationHomology.cyclesMap
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega)) p.g 1 p.cycle
  refine ⟨cR, rfl, p.certificate, ?_⟩
  simpa only [TerminalQuadraticPacket.orientedPrimitive,
    quadraticBlockMarkedWord_value] using p.certificate.value_eq

/-- The transported cycle represents the comparison image of the source
class.  This is naturality of the comparison equivalence, not a definitional
identification of the presentations. -/
theorem transportTerminalPacket_comparison
    (p : TerminalQuadraticPacket n L data hn) :
    Koszul.Presentation.homologyComparisonEquiv
        (rPresentation n L data (by omega)) 1
      ((Koszul.boundariesOne (rPresentation n L data (by omega)) 1).mkQ
        (transportTerminalPacket n L data hn p).cycleR) =
    Koszul.Presentation.homologyComparisonEquiv
        (terminalSourcePresentation n L data hn) 1
      ((Koszul.boundariesOne (terminalSourcePresentation n L data hn) 1).mkQ
        p.cycle) := by
  let S := terminalSourcePresentation n L data hn
  let R := rPresentation n L data (by omega)
  let eS := Koszul.Presentation.homologyComparisonEquiv S 1
  let eR := Koszul.Presentation.homologyComparisonEquiv R 1
  let y := (Koszul.boundariesOne S 1).mkQ p.cycle
  have hnat := Koszul.Presentation.homologyComparison_natural S R p.g 1
  have hy := LinearMap.congr_fun hnat y
  change eR (Koszul.PresentationHomology.map S R p.g 1 y) = eS y
  change eR (Koszul.PresentationHomology.map S R p.g 1 y) =
    Koszul.FirstDerivedSymmetricPower.map 1 LinearMap.id (eS y) at hy
  rw [Koszul.FirstDerivedSymmetricPower.map_id] at hy
  exact hy

end

end LieRings.MetabelianVanishing
