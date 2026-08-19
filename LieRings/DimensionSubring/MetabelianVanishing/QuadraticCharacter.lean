import LieRings.DimensionSubring.MetabelianVanishing.HigherCharacters
import LieRings.LinearAlgebra.InvariantFactorSmith
import LieRings.Homological.IntegralPolarization
import LieRings.Homological.QuadraticUCT

/-!
# The terminal quadratic presentation

The two presentations in this file are exactly those in the manuscript:
`P₀=F₁ -> V_n` and `Q₀=F_n -> U_n`.  Their ordered Smith bases are fixed once
and the basiswise lift `btilde : P₁ -> Q₀` is used to construct the block
presentation of `W_n`.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 1200000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)

local instance finiteVTerminal : Finite (V L n) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)

local instance finiteU : Finite (U L n) := by
  let N := (lowerCentralSeries ℤ L n : Submodule ℤ L).comap
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype
  exact Finite.of_surjective N.mkQ (Submodule.mkQ_surjective _)

local instance finiteWTerminal : Finite (W L n) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)

/-- `P₀=F₁`, the weight-one homogeneous piece. -/
abbrev PZero := FreeMetabelian.Piece (Generator L) 0

/-- The Hall basis on the weight-one ambient module. -/
def pZeroBasis : Module.Basis (Fin (Nat.card L)) ℤ (PZero L) :=
  FreeMetabelian.Free.pieceBasis
    ((Finsupp.basisSingleOne (R := ℤ) (ι := L)).reindex (Finite.equivFin L)) 0

local instance pZeroFree : Module.Free ℤ (PZero L) :=
  Module.Free.of_basis (pZeroBasis L)

local instance pZeroFinite : Module.Finite ℤ (PZero L) :=
  Module.Finite.of_basis (pZeroBasis L)

/-- The manuscript augmentation `P₀ -> V_n`. -/
def pAugmentation : PZero L →ₗ[ℤ] V L n :=
  (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ.comp
    (FreeMetabelian.Evaluation.canonicalGeneratorMap L)

theorem pAugmentation_surjective :
    Function.Surjective (pAugmentation n L) := by
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L) z
  refine ⟨Finsupp.single x 1, ?_⟩
  change (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
    (FreeMetabelian.Evaluation.canonicalGeneratorMap L
      (Finsupp.single x 1)) = _
  simp

/-- `P₁`, with its literal inclusion differential. -/
abbrev POne := LinearMap.ker (pAugmentation n L)

local instance pOneFinite : Module.Finite ℤ (POne n L) :=
  Module.Finite.of_fg (IsNoetherian.noetherian _)

local instance pOneFree : Module.Free ℤ (POne n L) :=
  Module.free_of_finite_type_torsion_free'

/-- The fixed terminal presentation of `V_n`. -/
def pPresentation : Koszul.Presentation (V L n) where
  rel := POne n L
  gen := PZero L
  relAddCommGroup := inferInstance
  genAddCommGroup := inferInstance
  relFree := inferInstance
  genFree := inferInstance
  relFinite := inferInstance
  genFinite := inferInstance
  d := (LinearMap.ker (pAugmentation n L)).subtype
  augmentation := pAugmentation n L
  d_injective := Subtype.val_injective
  augmentation_surjective := pAugmentation_surjective n L
  exact := by ext x; simp

/-- `Q₀=F_n`, the homogeneous piece of manuscript weight `n`. -/
abbrev QZero := FreeMetabelian.Piece (Generator L) (n - 1)

/-- The Hall basis on the terminal homogeneous ambient module. -/
def qZeroBasis : Module.Basis
    (FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) (n - 1))
    ℤ (QZero n L) :=
  FreeMetabelian.Free.pieceBasis
    ((Finsupp.basisSingleOne (R := ℤ) (ι := L)).reindex (Finite.equivFin L)) (n - 1)

local instance qZeroFree : Module.Free ℤ (QZero n L) :=
  Module.Free.of_basis (qZeroBasis n L)

local instance qZeroFinite : Module.Finite ℤ (QZero n L) :=
  Module.Finite.of_basis (qZeroBasis n L)

/-- The manuscript augmentation `Q₀ -> U_n`. -/
def qAugmentation (hn : 1 ≤ n) : QZero n L →ₗ[ℤ] U L n :=
  pieceToU (n := n) L data n hn

theorem qAugmentation_surjective (hn : 1 ≤ n) :
    Function.Surjective (qAugmentation n L data hn) :=
  pieceToU_surjective (n := n) L data n hn

/-- `Q₁`, again with its literal inclusion differential. -/
abbrev QOne (hn : 1 ≤ n) := LinearMap.ker (qAugmentation n L data hn)

local instance qOneFinite (hn : 1 ≤ n) :
    Module.Finite ℤ (QOne n L data hn) :=
  Module.Finite.of_fg (IsNoetherian.noetherian _)

local instance qOneFree (hn : 1 ≤ n) : Module.Free ℤ (QOne n L data hn) :=
  Module.free_of_finite_type_torsion_free'

/-- The fixed terminal presentation of `U_n`. -/
def qPresentation (hn : 1 ≤ n) : Koszul.Presentation (U L n) where
  rel := QOne n L data hn
  gen := QZero n L
  relAddCommGroup := inferInstance
  genAddCommGroup := inferInstance
  relFree := inferInstance
  genFree := inferInstance
  relFinite := inferInstance
  genFinite := inferInstance
  d := (LinearMap.ker (qAugmentation n L data hn)).subtype
  augmentation := qAugmentation n L data hn
  d_injective := Subtype.val_injective
  augmentation_surjective := qAugmentation_surjective n L data hn
  exact := by ext x; simp

/-- Ordered Smith coordinates for `P₁ ⊂ P₀`. -/
def pSmith : InvariantFactorPresentation (LinearMap.ker (pAugmentation n L)) := by
  let e := (pAugmentation n L).quotKerEquivOfSurjective
    (pAugmentation_surjective n L)
  letI : Finite (PZero L ⧸ LinearMap.ker (pAugmentation n L)) :=
    Finite.of_surjective e.symm e.symm.surjective
  exact InvariantFactorPresentation.ofFiniteQuotient
    (LinearMap.ker (pAugmentation n L)) inferInstance

/-- Ordered Smith coordinates for `Q₁ ⊂ Q₀`. -/
def qSmith (hn : 1 ≤ n) :
    InvariantFactorPresentation (LinearMap.ker (qAugmentation n L data hn)) := by
  let e := (qAugmentation n L data hn).quotKerEquivOfSurjective
    (qAugmentation_surjective n L data hn)
  letI : Finite (QZero n L ⧸ LinearMap.ker (qAugmentation n L data hn)) :=
    Finite.of_surjective e.symm e.symm.surjective
  exact InvariantFactorPresentation.ofFiniteQuotient
    (LinearMap.ker (qAugmentation n L data hn)) inferInstance

/-- A weight-one relation evaluates in `gamma_n`; this is its class in
`U_n=gamma_n/gamma_(n+1)`. -/
def pTail (hn : 1 ≤ n) : POne n L →ₗ[ℤ] U L n := by
  let f : POne n L →ₗ[ℤ]
      (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L) :=
    LinearMap.codRestrict (lowerCentralSeries ℤ L (n - 1))
      ((FreeMetabelian.Evaluation.canonicalGeneratorMap L).comp
        (LinearMap.ker (pAugmentation n L)).subtype) (by
          intro a
          have ha := a.property
          change (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L a.1) = 0 at ha
          exact (Submodule.Quotient.mk_eq_zero _).mp ha)
  exact ((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
      (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ.comp f

/-- The basiswise lift of the extension tail through `Q₀ ->> U_n`. -/
def btilde (hn : 1 ≤ n) : POne n L →ₗ[ℤ] QZero n L := by
  let S := pSmith n L
  let lift : Fin S.rank → QZero n L := fun i ↦
    Classical.choose
      (qAugmentation_surjective n L data hn (pTail n L hn (S.relationBasis i)))
  exact S.relationBasis.constr ℤ lift

theorem qAugmentation_btilde (hn : 1 ≤ n) (a : POne n L) :
    qAugmentation n L data hn (btilde n L data hn a) = pTail n L hn a := by
  let S := pSmith n L
  have hmap : (qAugmentation n L data hn).comp (btilde n L data hn) =
      pTail n L hn := by
    apply S.relationBasis.ext
    intro i
    change qAugmentation n L data hn
        (btilde n L data hn (S.relationBasis i)) = pTail n L hn (S.relationBasis i)
    rw [btilde, Module.Basis.constr_basis]
    exact Classical.choose_spec
      (qAugmentation_surjective n L data hn (pTail n L hn (S.relationBasis i)))
  exact LinearMap.congr_fun hmap a

/-- The weight-one generator, evaluated in `W_n`. -/
def pToW : PZero L →ₗ[ℤ] W L n :=
  (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ.comp
    (FreeMetabelian.Evaluation.canonicalGeneratorMap L)

/-- The inclusion of the terminal layer `U_n` in `W_n`. -/
def uToW : U L n →ₗ[ℤ] W L n :=
  (LinearMap.ker (pi L n)).subtype.comp (layerToKer L n)

theorem pi_uToW (u : U L n) : pi L n (uToW (L := L) (n := n) u) = 0 := by
  exact (layerToKer L n u).property

theorem uToW_injective : Function.Injective (uToW (L := L) (n := n)) := by
  intro x y hxy
  apply (layerEquivKer L n).injective
  apply Subtype.ext
  exact hxy

theorem pToW_relation_eq_uToW_pTail (hn : 1 ≤ n) (a : POne n L) :
    pToW n L a.1 = uToW (L := L) (n := n) (pTail n L hn a) := by
  rfl

/-- The block differential `(a,s) ↦ (d a,e s-btilde a)`. -/
def rDifferential (hn : 1 ≤ n) :
    (POne n L × QOne n L data hn) →ₗ[ℤ] (PZero L × QZero n L) :=
  LinearMap.prod
    ((LinearMap.ker (pAugmentation n L)).subtype.comp
      (LinearMap.fst ℤ (POne n L) (QOne n L data hn)))
    ((LinearMap.ker (qAugmentation n L data hn)).subtype.comp
        (LinearMap.snd ℤ (POne n L) (QOne n L data hn)) -
      (btilde n L data hn).comp
        (LinearMap.fst ℤ (POne n L) (QOne n L data hn)))

@[simp] theorem rDifferential_apply (hn : 1 ≤ n)
    (a : POne n L) (s : QOne n L data hn) :
    rDifferential n L data hn (a, s) =
      (a.1, s.1 - btilde n L data hn a) := rfl

/-- Augmentation of the block presentation of `W_n`. -/
def rAugmentation (hn : 1 ≤ n) :
    (PZero L × QZero n L) →ₗ[ℤ] W L n :=
  (pToW n L).coprod
    ((uToW (L := L) (n := n)).comp (qAugmentation n L data hn))

@[simp] theorem rAugmentation_apply (hn : 1 ≤ n)
    (x : PZero L) (y : QZero n L) :
    rAugmentation n L data hn (x, y) =
      pToW n L x + uToW (L := L) (n := n) (qAugmentation n L data hn y) := rfl

theorem rAugmentation_surjective (hn : 1 ≤ n) :
    Function.Surjective (rAugmentation n L data hn) := by
  intro z
  obtain ⟨l, rfl⟩ := Submodule.mkQ_surjective
    (lowerCentralSeries ℤ L n : Submodule ℤ L) z
  refine ⟨(Finsupp.single l 1, 0), ?_⟩
  rw [rAugmentation_apply, map_zero, map_zero, add_zero]
  change (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ
    (FreeMetabelian.Evaluation.canonicalGeneratorMap L (Finsupp.single l 1)) = _
  rw [FreeMetabelian.Evaluation.canonicalGeneratorMap_single, one_zsmul]

theorem rDifferential_injective (hn : 1 ≤ n) :
    Function.Injective (rDifferential n L data hn) := by
  rintro ⟨a, s⟩ ⟨a', s'⟩ h
  have ha : a = a' := by
    apply Subtype.ext
    exact congrArg Prod.fst h
  subst a'
  congr 1
  apply Subtype.ext
  have hs := congrArg Prod.snd h
  simpa using hs

theorem rAugmentation_d (hn : 1 ≤ n)
    (z : POne n L × QOne n L data hn) :
    rAugmentation n L data hn (rDifferential n L data hn z) = 0 := by
  rcases z with ⟨a, s⟩
  rw [rDifferential_apply, rAugmentation_apply, map_sub,
    qAugmentation_btilde]
  rw [show qAugmentation n L data hn s.1 = 0 from s.property]
  rw [zero_sub, map_neg]
  rw [← sub_eq_add_neg]
  exact sub_eq_zero.mpr (pToW_relation_eq_uToW_pTail n L hn a)

theorem rExact (hn : 1 ≤ n) :
    LinearMap.range (rDifferential n L data hn) =
      LinearMap.ker (rAugmentation n L data hn) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact rAugmentation_d n L data hn z
  · rintro ⟨x, y⟩ hxy
    change pToW n L x + uToW (L := L) (n := n)
      (qAugmentation n L data hn y) = 0 at hxy
    have hx : pAugmentation n L x = 0 := by
      change pi L n (pToW n L x) = 0
      have hp := congrArg (pi L n) hxy
      rw [map_add, pi_uToW, map_zero, add_zero] at hp
      exact hp
    let a : POne n L := ⟨x, hx⟩
    have hu : qAugmentation n L data hn
        (y + btilde n L data hn a) = 0 := by
      apply uToW_injective (L := L) (n := n)
      rw [map_zero, map_add, qAugmentation_btilde, map_add,
        ← pToW_relation_eq_uToW_pTail n L hn a]
      rw [add_comm]
      exact hxy
    let s : QOne n L data hn := ⟨y + btilde n L data hn a, hu⟩
    refine ⟨(a, s), ?_⟩
    apply Prod.ext
    · rfl
    · change y + btilde n L data hn a - btilde n L data hn a = y
      abel

/-- The exact free block presentation used in Points 5 and 6. -/
def rPresentation (hn : 1 ≤ n) : Koszul.Presentation (W L n) where
  rel := POne n L × QOne n L data hn
  gen := PZero L × QZero n L
  relAddCommGroup := inferInstance
  genAddCommGroup := inferInstance
  relFree := inferInstance
  genFree := inferInstance
  relFinite := inferInstance
  genFinite := inferInstance
  d := rDifferential n L data hn
  augmentation := rAugmentation n L data hn
  d_injective := rDifferential_injective n L data hn
  augmentation_surjective := rAugmentation_surjective n L data hn
  exact := rExact n L data hn

/-- The strict block projection `R -> P` inducing `pi : W_n -> V_n`. -/
def rToP (hn : 1 ≤ n) :
    Koszul.Presentation.Hom (rPresentation n L data hn) (pPresentation n L)
      (pi L n) where
  relMap := LinearMap.fst ℤ (POne n L) (QOne n L data hn)
  genMap := LinearMap.fst ℤ (PZero L) (QZero n L)
  commutes := by ext z; rfl
  induces := by
    ext z
    rcases z with ⟨x, y⟩
    change pAugmentation n L x = pi L n
      (pToW n L x + uToW (L := L) (n := n) (qAugmentation n L data hn y))
    rw [map_add, pi_uToW, add_zero]
    rfl

/-! ## The terminal cocycle and its exact Smith lift -/

/-- `Sym¹(P₀) ≃ P₀`, fixed using the same Smith ambient basis. -/
def pSymOneEquiv :
    SymmetricPower ℤ (Fin 1) (PZero L) ≃ₗ[ℤ] PZero L :=
  SymmetricPower.degreeOneLinearEquiv (pSmith n L).ambientBasis

/-- The single terminal tooth, reindexed from `Fin 1` to the literal
`Fin (n+1-n)` used by `Theta_n`. -/
def terminalTooth : PZero L →ₗ[ℤ]
    SymmetricPower ℤ (Fin (n + 1 - n)) (V L n) :=
  (SymmetricPower.reindex (R := ℤ)
    (Fin.castOrderIso (by omega : 1 = n + 1 - n)).toEquiv).comp
      ((SymmetricPower.degreeOne (R := ℤ)).comp (pAugmentation n L))

/-- The terminal bracket pairing `U_n ⊗ P₀ → C`, with the tooth mapped to
`V_n`. -/
def terminalPair (hn : 2 ≤ n) :
    (U L n ⊗[ℤ] PZero L) →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  (Theta n L data n hn le_rfl).comp
    (TensorProduct.map LinearMap.id (terminalTooth n L))

@[simp] theorem terminalPair_tmul (hn : 2 ≤ n) (u : U L n)
    (x : PZero L) :
    terminalPair n L data hn (u ⊗ₜ[ℤ] x) =
      Theta n L data n hn le_rfl
        (u ⊗ₜ[ℤ] terminalTooth n L x) := by
  rw [terminalPair, LinearMap.comp_apply]
  change Theta n L data n hn le_rfl
    (u ⊗ₜ[ℤ] terminalTooth n L x) = _
  rfl

/-- The manuscript cocycle `φ(a,x)=[b(a),x]`. -/
def terminalPhi (hn : 2 ≤ n) :
    Koszul.One (pPresentation n L) 1 →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  (terminalPair n L data hn).comp
    (TensorProduct.map (pTail n L (by omega))
      (pSymOneEquiv n L).toLinearMap)

@[simp] theorem terminalPhi_tmul (hn : 2 ≤ n)
    (a : POne n L) (x : PZero L) :
    terminalPhi n L data hn
        (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x) =
      terminalPair n L data hn (pTail n L (by omega) a ⊗ₜ[ℤ] x) := by
  rw [terminalPhi, LinearMap.comp_apply]
  change terminalPair n L data hn
      (pTail n L (by omega) a ⊗ₜ[ℤ]
        pSymOneEquiv n L (SymmetricPower.degreeOne (R := ℤ) x)) = _
  have hx := SymmetricPower.degreeOneLinearEquiv_degreeOne
    (pSmith n L).ambientBasis x
  change terminalPair n L data hn
      (pTail n L (by omega) a ⊗ₜ[ℤ]
        SymmetricPower.degreeOneLinearEquiv (pSmith n L).ambientBasis
          (SymmetricPower.degreeOne (R := ℤ) x)) = _
  rw [hx]

theorem terminalPhi_dOne_zero (hn : 2 ≤ n) (a a' : POne n L) :
    terminalPhi n L data hn
        (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) a'.1) = 0 := by
  rw [terminalPhi_tmul]
  have hx : pAugmentation n L a'.1 = 0 := a'.property
  rw [terminalPair_tmul]
  change Theta n L data n hn le_rfl
      (pTail n L (by omega) a ⊗ₜ[ℤ] terminalTooth n L a'.1) = 0
  rw [terminalTooth, LinearMap.comp_apply, LinearMap.comp_apply, hx,
    map_zero, map_zero, TensorProduct.tmul_zero, map_zero]

private def pGeneratorValue (i : Fin (pSmith n L).rank) : L :=
  FreeMetabelian.Evaluation.canonicalGeneratorMap L
    ((pSmith n L).ambientBasis i)

private theorem pTail_relationBasis (hn : 2 ≤ n)
    (i : Fin (pSmith n L).rank) :
    pTail n L (by omega) ((pSmith n L).relationBasis i) =
      ((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
        (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
      ⟨((pSmith n L).diagonal i : ℤ) • pGeneratorValue n L i, by
        have hi := ((pSmith n L).relationBasis i).property
        change pAugmentation n L (((pSmith n L).relationBasis i).1) = 0 at hi
        rw [(pSmith n L).relation_eq i] at hi
        apply (Submodule.Quotient.mk_eq_zero _).mp
        simpa only [pAugmentation, LinearMap.comp_apply, map_zsmul,
          pGeneratorValue] using hi⟩ := by
  change ((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
      (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
      ⟨FreeMetabelian.Evaluation.canonicalGeneratorMap L
        (((pSmith n L).relationBasis i).1), _⟩ = _
  apply congrArg (((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ)
  apply Subtype.ext
  change FreeMetabelian.Evaluation.canonicalGeneratorMap L
      (((pSmith n L).relationBasis i).1) =
    ((pSmith n L).diagonal i : ℤ) • pGeneratorValue n L i
  rw [(pSmith n L).relation_eq i]
  exact map_zsmul (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
    ((pSmith n L).diagonal i : ℤ) ((pSmith n L).ambientBasis i)

private theorem terminalTooth_basis (hn : 2 ≤ n)
    (i : Fin (pSmith n L).rank) :
    terminalTooth n L ((pSmith n L).ambientBasis i) =
      SymmetricPower.tprod ℤ (fun _ : Fin (n + 1 - n) ↦
        (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
          (pGeneratorValue n L i)) := by
  rw [terminalTooth, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [SymmetricPower.degreeOne_apply]
  rw [SymmetricPower.reindex_tprod]
  apply congrArg (SymmetricPower.tprod ℤ)
  funext j
  haveI : Subsingleton (Fin (n + 1 - n)) :=
    ⟨fun a b ↦ Fin.ext (by omega)⟩
  have hj : j = (Fin.castOrderIso (by omega : 1 = n + 1 - n)) 0 :=
    Subsingleton.elim _ _
  rw [hj]
  rfl

theorem terminalPhi_oneBasis (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    terminalPhi n L data hn
        (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L) (i, j)) =
      terminalPair n L data hn
        (pTail n L (by omega) ((pSmith n L).relationBasis i) ⊗ₜ[ℤ]
          (pSmith n L).ambientBasis j) := by
  rw [Koszul.QuadraticUCT.oneBasis_apply]
  exact terminalPhi_tmul n L data hn _ _

/-- The manuscript's divided Smith formula, proved in the Lie ring before
passing to `ZMod`; no cancellation in the finite target is used. -/
theorem terminalPhi_smith_ratio_skew (hn : 2 ≤ n)
    {i j : Fin (pSmith n L).rank} (hij : i < j) :
    terminalPhi n L data hn
        (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L) (j, i)) =
      -(Koszul.QuadraticUCT.ratio (pAugmentation n L)
          (pSmith n L) i j : ℤ) •
        terminalPhi n L data hn
          (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
            (pAugmentation_surjective n L) (pSmith n L) (i, j)) := by
  rw [terminalPhi_oneBasis n L data hn, terminalPhi_oneBasis n L data hn]
  rw [
    pTail_relationBasis n L (hn := hn), pTail_relationBasis n L (hn := hn),
    terminalPair_tmul, terminalPair_tmul,
    terminalTooth_basis n L (hn := hn), terminalTooth_basis n L (hn := hn)]
  have hd := Koszul.QuadraticUCT.diagonal_mul_ratio
    (pAugmentation n L) (pSmith n L) hij.le
  have hdZ : ((pSmith n L).diagonal j : ℤ) =
      (Koszul.QuadraticUCT.ratio (pAugmentation n L)
        (pSmith n L) i j : ℤ) * ((pSmith n L).diagonal i : ℤ) := by
    exact_mod_cast (by simpa [mul_comm] using hd.symm)
  let hjmem : ((pSmith n L).diagonal j : ℤ) • pGeneratorValue n L j ∈
      lowerCentralSeries ℤ L (n - 1) := by
    have hj0 := ((pSmith n L).relationBasis j).property
    change pAugmentation n L (((pSmith n L).relationBasis j).1) = 0 at hj0
    rw [(pSmith n L).relation_eq j] at hj0
    exact (Submodule.Quotient.mk_eq_zero _).mp (by
      simpa only [pAugmentation, LinearMap.comp_apply, map_zsmul,
        pGeneratorValue] using hj0)
  have hrmem : ((Koszul.QuadraticUCT.ratio (pAugmentation n L)
        (pSmith n L) i j : ℤ) * ((pSmith n L).diagonal i : ℤ)) •
        pGeneratorValue n L j ∈ lowerCentralSeries ℤ L (n - 1) := by
    simpa only [← hdZ] using hjmem
  let himem : ((pSmith n L).diagonal i : ℤ) • pGeneratorValue n L i ∈
      lowerCentralSeries ℤ L (n - 1) := by
    have hi0 := ((pSmith n L).relationBasis i).property
    change pAugmentation n L (((pSmith n L).relationBasis i).1) = 0 at hi0
    rw [(pSmith n L).relation_eq i] at hi0
    exact (Submodule.Quotient.mk_eq_zero _).mp (by
      simpa only [pAugmentation, LinearMap.comp_apply, map_zsmul,
        pGeneratorValue] using hi0)
  have hhead :
      ((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
        (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
          ⟨((pSmith n L).diagonal j : ℤ) • pGeneratorValue n L j, hjmem⟩ =
      ((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
        (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
          ⟨((Koszul.QuadraticUCT.ratio (pAugmentation n L)
              (pSmith n L) i j : ℤ) * ((pSmith n L).diagonal i : ℤ)) •
            pGeneratorValue n L j, hrmem⟩ := by
    congr 1
    apply Subtype.ext
    exact congrArg (fun z : ℤ ↦ z • pGeneratorValue n L j) hdZ
  rw [hhead]
  exact LieRings.MetabelianVanishing.Theta_terminal_ratio_skew n L data hn
    ((pSmith n L).diagonal i : ℤ)
    (Koszul.QuadraticUCT.ratio (pAugmentation n L) (pSmith n L) i j : ℤ)
    (pGeneratorValue n L i) (pGeneratorValue n L j) himem hrmem

private theorem terminalPhi_oneBasis_diag (hn : 2 ≤ n)
    (i : Fin (pSmith n L).rank) :
    terminalPhi n L data hn
        (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L) (i, i)) = 0 := by
  rw [terminalPhi_oneBasis n L data hn,
    pTail_relationBasis n L (hn := hn), terminalPair_tmul,
    terminalTooth_basis n L (hn := hn)]
  exact LieRings.MetabelianVanishing.Theta_terminal_same_zero n L data hn
    ((pSmith n L).diagonal i : ℤ) (pGeneratorValue n L i) _

/-- The upper-triangular integral representative of `φ(aᵢ,xⱼ)`, extended
below the diagonal by the exact Smith skew relation. -/
def terminalLiftEntry (hn : 2 ≤ n) [NeZero (2 ^ data.exponent)]
    (i j : Fin (pSmith n L).rank) : ℤ :=
  if i < j then ZMod.cast (terminalPhi n L data hn
      (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
        (pAugmentation_surjective n L) (pSmith n L) (i, j)))
  else if j < i then
    -(Koszul.QuadraticUCT.ratio (pAugmentation n L) (pSmith n L) j i : ℤ) *
      ZMod.cast (terminalPhi n L data hn
        (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L) (j, i)))
  else 0

/-- The exact integral lift `φ̂` in the ordered Smith tensor basis. -/
def terminalLift (hn : 2 ≤ n) :
    Koszul.One (pPresentation n L) 1 →ₗ[ℤ] ℤ := by
  letI : NeZero (2 ^ data.exponent) := ⟨pow_ne_zero _ (by decide)⟩
  exact (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
    (pAugmentation_surjective n L) (pSmith n L)).constr ℤ
      (fun ij ↦ terminalLiftEntry n L data hn ij.1 ij.2)

@[simp] theorem terminalLift_oneBasis (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    terminalLift n L data hn
      (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
        (pAugmentation_surjective n L) (pSmith n L) (i, j)) =
      terminalLiftEntry n L data hn i j := by
  letI : NeZero (2 ^ data.exponent) := ⟨pow_ne_zero _ (by decide)⟩
  change (((Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
    (pAugmentation_surjective n L) (pSmith n L)).constr ℤ
      (fun ij ↦ terminalLiftEntry n L data hn ij.1 ij.2))
        ((Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L)) (i, j))) = _
  exact (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
    (pAugmentation_surjective n L) (pSmith n L)).constr_basis ℤ
      (fun ij ↦ terminalLiftEntry n L data hn ij.1 ij.2) (i, j)

theorem terminalLift_cast (hn : 2 ≤ n)
    (z : Koszul.One (pPresentation n L) 1) :
    (terminalLift n L data hn z : ZMod (2 ^ data.exponent)) =
      terminalPhi n L data hn z := by
  letI : NeZero (2 ^ data.exponent) := ⟨pow_ne_zero _ (by decide)⟩
  let castMap : ℤ →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
    (Int.castAddHom (ZMod (2 ^ data.exponent))).toIntLinearMap
  change castMap (terminalLift n L data hn z) = terminalPhi n L data hn z
  have hmaps : castMap.comp (terminalLift n L data hn) =
      terminalPhi n L data hn := by
    apply (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
    (pAugmentation_surjective n L) (pSmith n L)).ext
    rintro ⟨i, j⟩
    change castMap (terminalLift n L data hn
      (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
        (pAugmentation_surjective n L) (pSmith n L) (i, j))) = _
    rw [terminalLift_oneBasis]
    rcases lt_trichotomy i j with hij | hij | hij
    · unfold terminalLiftEntry
      rw [if_pos hij]
      change ((ZMod.cast (terminalPhi n L data hn
        (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L) (i, j))) : ℤ) :
            ZMod (2 ^ data.exponent)) = _
      exact ZMod.intCast_zmod_cast _
    · subst j
      have hdiag := terminalPhi_oneBasis_diag n L data hn i
      simpa only [terminalLiftEntry, lt_self_iff_false, if_false,
        map_zero] using hdiag.symm
    · have hskew := terminalPhi_smith_ratio_skew n L data hn hij
      rw [show terminalLiftEntry n L data hn i j =
          -(Koszul.QuadraticUCT.ratio (pAugmentation n L)
              (pSmith n L) j i : ℤ) *
            ZMod.cast (terminalPhi n L data hn
              (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
                (pAugmentation_surjective n L) (pSmith n L) (j, i))) by
        simp only [terminalLiftEntry, hij, if_true,
          not_lt_of_ge hij.le, if_false]]
      change ((-(Koszul.QuadraticUCT.ratio (pAugmentation n L)
          (pSmith n L) j i : ℤ) * ZMod.cast (terminalPhi n L data hn
            (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) (j, i))) : ℤ) :
          ZMod (2 ^ data.exponent)) = _
      rw [Int.cast_mul, Int.cast_neg, ZMod.intCast_zmod_cast]
      simpa [zsmul_eq_mul, Int.cast_neg, Int.cast_natCast] using hskew.symm
  exact LinearMap.congr_fun hmaps z

theorem terminalLift_skew_on_d (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    (pSmith n L).diagonal j * terminalLiftEntry n L data hn i j +
      (pSmith n L).diagonal i * terminalLiftEntry n L data hn j i = 0 := by
  letI : NeZero (2 ^ data.exponent) := ⟨pow_ne_zero _ (by decide)⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · have hd := Koszul.QuadraticUCT.diagonal_mul_ratio
      (pAugmentation n L) (pSmith n L) hij.le
    have hdZ : ((pSmith n L).diagonal i : ℤ) *
        (Koszul.QuadraticUCT.ratio (pAugmentation n L) (pSmith n L) i j : ℤ) =
        ((pSmith n L).diagonal j : ℤ) := by exact_mod_cast hd
    simp only [terminalLiftEntry, hij, if_true, not_lt_of_ge hij.le, if_false]
    rw [← hdZ]
    ring
  · subst j
    simp [terminalLiftEntry]
  · have hd := Koszul.QuadraticUCT.diagonal_mul_ratio
      (pAugmentation n L) (pSmith n L) hij.le
    have hdZ : ((pSmith n L).diagonal j : ℤ) *
        (Koszul.QuadraticUCT.ratio (pAugmentation n L) (pSmith n L) j i : ℤ) =
        ((pSmith n L).diagonal i : ℤ) := by exact_mod_cast hd
    simp only [terminalLiftEntry, hij, if_true, not_lt_of_ge hij.le, if_false]
    rw [← hdZ]
    ring

/-- The lift satisfies the manuscript identity
`φ̂(a,da')+φ̂(a',da)=0` over the integers. -/
theorem terminalLift_exterior (hn : 2 ≤ n) (a a' : POne n L) :
    terminalLift n L data hn
        (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) a'.1) +
      terminalLift n L data hn
        (a' ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) a.1) = 0 := by
  let S := pSmith n L
  letI : TensorProduct.CompatibleSMul ℤ ℤ (POne n L) (PZero L) :=
    TensorProduct.CompatibleSMul.int
  let t : POne n L →ₗ[ℤ] PZero L →ₗ[ℤ] ℤ :=
    let tSym := (TensorProduct.lift.equiv (RingHom.id ℤ) (POne n L)
      (SymmetricPower ℤ (Fin 1) (PZero L)) ℤ).symm
        (terminalLift n L data hn)
    { toFun := fun x ↦ (tSym x).comp (SymmetricPower.degreeOne (R := ℤ))
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        change tSym (x + y) (SymmetricPower.degreeOne (R := ℤ) z) = _
        rw [map_add]
        rfl
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro y
        change tSym (c • x) (SymmetricPower.degreeOne (R := ℤ) y) = _
        rw [map_zsmul]
        rfl }
  let b : POne n L →ₗ[ℤ] POne n L →ₗ[ℤ] ℤ :=
    { toFun := fun x ↦ t x |>.comp
        (LinearMap.ker (pAugmentation n L)).subtype
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro y
        change t (c • x) y.1 = _
        rw [map_zsmul]
        rfl }
  let f : POne n L →ₗ[ℤ] POne n L →ₗ[ℤ] ℤ :=
    { toFun := fun x ↦ b x + LinearMap.flip b x
      map_add' := by
        intro x y
        ext z
        simp only [map_add, LinearMap.add_apply]
        abel
      map_smul' := by
        intro c x
        ext y
        change b (c • x) y + LinearMap.flip b (c • x) y =
          c • (b x y + LinearMap.flip b x y)
        change b (c • x) y + b y (c • x) =
          c • (b x y + b y x)
        rw [map_zsmul, map_zsmul, smul_add]
        rfl }
  have hf : f = 0 := by
    apply S.relationBasis.ext
    intro i
    apply S.relationBasis.ext
    intro j
    change b (S.relationBasis i) (S.relationBasis j) +
      b (S.relationBasis j) (S.relationBasis i) = 0
    have hjval : (S.relationBasis j : PZero L) =
        (S.diagonal j : ℤ) • S.ambientBasis j := S.relation_eq j
    have hival : (S.relationBasis i : PZero L) =
        (S.diagonal i : ℤ) • S.ambientBasis i := S.relation_eq i
    change t (S.relationBasis i) (S.relationBasis j).1 +
      t (S.relationBasis j) (S.relationBasis i).1 = 0
    rw [hjval, hival, map_zsmul, map_zsmul]
    change (S.diagonal j : ℤ) • terminalLift n L data hn
        (S.relationBasis i ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) +
      (S.diagonal i : ℤ) • terminalLift n L data hn
        (S.relationBasis j ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis i)) = 0
    change (S.diagonal j : ℤ) • terminalLift n L data hn
        (S.relationBasis i ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) +
      (S.diagonal i : ℤ) • terminalLift n L data hn
        (S.relationBasis j ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis i)) = 0
    have hliftij : terminalLift n L data hn
        (S.relationBasis i ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) =
      terminalLiftEntry n L data hn i j := by
      simpa only [Koszul.QuadraticUCT.oneBasis_apply] using
        terminalLift_oneBasis n L data hn i j
    have hliftji : terminalLift n L data hn
        (S.relationBasis j ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis i)) =
      terminalLiftEntry n L data hn j i := by
      simpa only [Koszul.QuadraticUCT.oneBasis_apply] using
        terminalLift_oneBasis n L data hn j i
    rw [hliftij, hliftji]
    simpa only [zsmul_eq_mul] using terminalLift_skew_on_d n L data hn i j
  have haa := LinearMap.congr_fun (LinearMap.congr_fun hf a) a'
  change f a a' = 0 at haa
  exact haa

/-- The lift `φ̂`, curried as an integral bilinear form on `P₁ × P₀`. -/
def terminalLiftBilinear (hn : 2 ≤ n) :
    POne n L →ₗ[ℤ] PZero L →ₗ[ℤ] ℤ := by
  let t := (TensorProduct.lift.equiv (RingHom.id ℤ) (POne n L)
    (SymmetricPower ℤ (Fin 1) (PZero L)) ℤ).symm
      (terminalLift n L data hn)
  exact
    { toFun := fun a ↦ (t a).comp (SymmetricPower.degreeOne (R := ℤ))
      map_add' := by intro a b; ext x; change t (a + b) _ = _; rw [map_add]; rfl
      map_smul' := by intro z a; ext x; change t (z • a) _ = _; rw [map_zsmul]; rfl }

@[simp] theorem terminalLiftBilinear_apply (hn : 2 ≤ n)
    (a : POne n L) (x : PZero L) :
    terminalLiftBilinear n L data hn a x =
      terminalLift n L data hn
        (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x) := rfl

/-- The coefficient of the manuscript's rational form `ϑ` in the ordered
Smith ambient basis. -/
def terminalThetaCoeff (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) : ℚ :=
  (terminalLiftEntry n L data hn i j : ℚ) /
    ((2 ^ data.exponent : ℚ) * ((pSmith n L).diagonal i : ℚ))

/-- The rational bilinear form `ϑ` on `P₀`, constructed in the fixed Smith
basis. -/
def terminalTheta (hn : 2 ≤ n) : PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
  (pSmith n L).ambientBasis.constr ℤ (fun i ↦
    (pSmith n L).ambientBasis.constr ℤ (fun j ↦
      terminalThetaCoeff n L data hn i j))

@[simp] theorem terminalTheta_basis (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    terminalTheta n L data hn ((pSmith n L).ambientBasis i)
        ((pSmith n L).ambientBasis j) =
      terminalThetaCoeff n L data hn i j := by
  rw [terminalTheta, Module.Basis.constr_basis, Module.Basis.constr_basis]

theorem terminalThetaCoeff_skew (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    terminalThetaCoeff n L data hn j i =
      -terminalThetaCoeff n L data hn i j := by
  have hq : (2 ^ data.exponent : ℚ) ≠ 0 := by positivity
  have hdi : ((pSmith n L).diagonal i : ℚ) ≠ 0 := by
    exact_mod_cast (pSmith n L).diagonal_pos i |>.ne'
  have hdj : ((pSmith n L).diagonal j : ℚ) ≠ 0 := by
    exact_mod_cast (pSmith n L).diagonal_pos j |>.ne'
  have hs := terminalLift_skew_on_d n L data hn i j
  have hsQ : ((pSmith n L).diagonal j : ℚ) *
        terminalLiftEntry n L data hn i j +
      ((pSmith n L).diagonal i : ℚ) *
        terminalLiftEntry n L data hn j i = 0 := by exact_mod_cast hs
  rw [terminalThetaCoeff, terminalThetaCoeff, ← neg_div]
  apply (div_eq_div_iff (mul_ne_zero hq hdj) (mul_ne_zero hq hdi)).2
  calc
    (terminalLiftEntry n L data hn j i : ℚ) *
        ((2 ^ data.exponent : ℚ) * ((pSmith n L).diagonal i : ℚ)) =
      (2 ^ data.exponent : ℚ) *
        (((pSmith n L).diagonal i : ℚ) *
          terminalLiftEntry n L data hn j i) := by ring
    _ = (2 ^ data.exponent : ℚ) *
        (-((pSmith n L).diagonal j : ℚ) *
          terminalLiftEntry n L data hn i j) := by
          congr 1
          linarith
    _ = (-(terminalLiftEntry n L data hn i j : ℚ)) *
        ((2 ^ data.exponent : ℚ) * ((pSmith n L).diagonal j : ℚ)) := by ring

theorem terminalTheta_skew (hn : 2 ≤ n) (x y : PZero L) :
    terminalTheta n L data hn y x = -terminalTheta n L data hn x y := by
  let S := pSmith n L
  let f : PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
    terminalTheta n L data hn + LinearMap.flip (terminalTheta n L data hn)
  have hf : f = 0 := by
    apply S.ambientBasis.ext
    intro i
    apply S.ambientBasis.ext
    intro j
    change terminalTheta n L data hn (S.ambientBasis i) (S.ambientBasis j) +
      terminalTheta n L data hn (S.ambientBasis j) (S.ambientBasis i) = 0
    rw [terminalTheta_basis, terminalTheta_basis,
      terminalThetaCoeff_skew]
    ring
  have h := LinearMap.congr_fun (LinearMap.congr_fun hf x) y
  change terminalTheta n L data hn x y +
    terminalTheta n L data hn y x = 0 at h
  linarith

theorem terminalTheta_self (hn : 2 ≤ n) (x : PZero L) :
    terminalTheta n L data hn x x = 0 := by
  have h := terminalTheta_skew n L data hn x x
  linarith

/-- The defining extension identity `ϑ(d a,x)=φ̂(a,x)/q`. -/
theorem terminalTheta_d (hn : 2 ≤ n) (a : POne n L) (x : PZero L) :
    terminalTheta n L data hn a.1 x =
      (terminalLiftBilinear n L data hn a x : ℚ) /
        (2 ^ data.exponent : ℚ) := by
  let S := pSmith n L
  let left : POne n L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
    (terminalTheta n L data hn).comp
      (LinearMap.ker (pAugmentation n L)).subtype
  let right : POne n L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
    { toFun := fun a ↦
        LinearMap.smulRight
          ((Int.castRingHom ℚ).toIntAlgHom.toLinearMap.comp
            (terminalLiftBilinear n L data hn a))
          ((2 ^ data.exponent : ℚ)⁻¹)
      map_add' := by
        intro a b
        ext x
        simp only [map_add, LinearMap.add_apply, LinearMap.smulRight_apply,
          LinearMap.comp_apply, Int.cast_add, smul_eq_mul]
        ring
      map_smul' := by
        intro z a
        ext x
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.smulRight_apply,
          LinearMap.comp_apply, Int.cast_mul, RingHom.id_apply, smul_eq_mul]
        change (((z * terminalLiftBilinear n L data hn a x : ℤ) : ℚ) *
          (2 ^ data.exponent : ℚ)⁻¹) =
          (z : ℚ) * ((terminalLiftBilinear n L data hn a x : ℚ) *
            (2 ^ data.exponent : ℚ)⁻¹)
        push_cast
        ring }
  have hlr : left = right := by
    apply S.relationBasis.ext
    intro i
    apply S.ambientBasis.ext
    intro j
    dsimp only [left, right]
    simp only [LinearMap.smulRight_apply,
      LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    change terminalTheta n L data hn (S.relationBasis i).1
        (S.ambientBasis j) =
      (terminalLiftBilinear n L data hn (S.relationBasis i)
        (S.ambientBasis j) : ℚ) * (2 ^ data.exponent : ℚ)⁻¹
    rw [S.relation_eq i, map_zsmul]
    change (S.diagonal i : ℤ) •
      terminalTheta n L data hn (S.ambientBasis i) (S.ambientBasis j) = _
    rw [terminalTheta_basis, terminalThetaCoeff]
    have hdi : (S.diagonal i : ℚ) ≠ 0 := by
      exact_mod_cast (S.diagonal_pos i).ne'
    have hq : (2 ^ data.exponent : ℚ) ≠ 0 := by positivity
    rw [terminalLiftBilinear_apply]
    have hlift := terminalLift_oneBasis n L data hn i j
    rw [Koszul.QuadraticUCT.oneBasis_apply] at hlift
    change (S.diagonal i : ℤ) •
        ((terminalLiftEntry n L data hn i j : ℚ) /
          ((2 ^ data.exponent : ℚ) * ((pSmith n L).diagonal i : ℚ))) =
      (terminalLift n L data hn
          (S.relationBasis i ⊗ₜ[ℤ]
            SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) : ℚ) *
        (2 ^ data.exponent : ℚ)⁻¹
    rw [show terminalLift n L data hn
          (S.relationBasis i ⊗ₜ[ℤ]
            SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) =
        terminalLiftEntry n L data hn i j by exact hlift]
    change (S.diagonal i : ℚ) *
        ((terminalLiftEntry n L data hn i j : ℚ) /
          ((2 ^ data.exponent : ℚ) * (S.diagonal i : ℚ))) =
      (terminalLiftEntry n L data hn i j : ℚ) *
        (2 ^ data.exponent : ℚ)⁻¹
    field_simp
  have h := LinearMap.congr_fun (LinearMap.congr_fun hlr a) x
  simpa only [left, right, LinearMap.flip_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, smul_eq_mul, div_eq_mul_inv] using h

/-! ## The divided quadratic cochain and the terminal character -/

/-- The integral bilinear form `(a,a') ↦ φ̂(a,d a')`. -/
def terminalNumeratorBilinear (hn : 2 ≤ n) :
    POne n L →ₗ[ℤ] POne n L →ₗ[ℤ] ℤ := by
  let tSym := (TensorProduct.lift.equiv (RingHom.id ℤ) (POne n L)
    (SymmetricPower ℤ (Fin 1) (PZero L)) ℤ).symm
      (terminalLift n L data hn)
  exact
    { toFun := fun a ↦ (tSym a).comp
        ((SymmetricPower.degreeOne (R := ℤ)).comp
          (LinearMap.ker (pAugmentation n L)).subtype)
      map_add' := by
        intro a b
        ext a'
        change tSym (a + b) (SymmetricPower.degreeOne (R := ℤ) a'.1) = _
        rw [map_add]
        rfl
      map_smul' := by
        intro z a
        ext a'
        change tSym (z • a) (SymmetricPower.degreeOne (R := ℤ) a'.1) = _
        rw [map_zsmul]
        rfl }

@[simp] theorem terminalNumeratorBilinear_apply (hn : 2 ≤ n)
    (a a' : POne n L) :
    terminalNumeratorBilinear n L data hn a a' =
      terminalLift n L data hn
        (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) a'.1) := rfl

private def terminalNumeratorAlternating (hn : 2 ≤ n) :
    POne n L [⋀^Fin 2]→ₗ[ℤ] ℤ :=
  AlternatingMap.mk
    (MultilinearMap.mk'
      (fun a ↦ terminalNumeratorBilinear n L data hn (a 0) (a 1))
      (by
        intro a i x y
        fin_cases i
        · change terminalNumeratorBilinear n L data hn (x + y) (a 1) = _
          rw [map_add]
          rfl
        · exact map_add (terminalNumeratorBilinear n L data hn (a 0)) x y)
      (by
        intro a i z x
        fin_cases i
        · change terminalNumeratorBilinear n L data hn (z • x) (a 1) = _
          rw [map_zsmul]
          rfl
        · exact map_zsmul (terminalNumeratorBilinear n L data hn (a 0)) z x))
    (by
      intro a i j hij hne
      fin_cases i <;> fin_cases j
      · exact (hne rfl).elim
      · have heq : a 0 = a 1 := by simpa using hij
        change terminalNumeratorBilinear n L data hn (a 0) (a 1) = 0
        rw [heq]
        have h := terminalLift_exterior n L data hn (a 1) (a 1)
        rw [terminalNumeratorBilinear_apply]
        rw [← two_mul] at h
        omega
      · have heq : a 1 = a 0 := by simpa using hij
        change terminalNumeratorBilinear n L data hn (a 0) (a 1) = 0
        rw [heq]
        have h := terminalLift_exterior n L data hn (a 0) (a 0)
        rw [terminalNumeratorBilinear_apply]
        rw [← two_mul] at h
        omega
      · exact (hne rfl).elim)

/-- The undivided exterior numerator `a∧a' ↦ φ̂(a,d a')`. -/
def terminalNumeratorExterior (hn : 2 ≤ n) :
    (⋀[ℤ]^2 (POne n L)) →ₗ[ℤ] ℤ :=
  exteriorPower.alternatingMapLinearEquiv
    (terminalNumeratorAlternating n L data hn)

@[simp] theorem terminalNumeratorExterior_ιMulti (hn : 2 ≤ n)
    (a : Fin 2 → POne n L) :
    terminalNumeratorExterior n L data hn (exteriorPower.ιMulti ℤ 2 a) =
      terminalLift n L data hn
        (a 0 ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (a 1).1) := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The undivided terminal numerator on the literal degree-two Koszul term. -/
def terminalNumerator (hn : 2 ≤ n) :
    Koszul.Two (pPresentation n L) 0 →ₗ[ℤ] ℤ :=
  (terminalNumeratorExterior n L data hn).comp
    (Koszul.QuadraticUCT.twoToExterior (pAugmentation n L)
      (pAugmentation_surjective n L) (pSmith n L)).toLinearMap

@[simp] theorem terminalNumerator_twoGenerator (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    terminalNumerator n L data hn
        (Koszul.QuadraticUCT.twoGenerator (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L) i j) =
      (pSmith n L).diagonal j * terminalLiftEntry n L data hn i j := by
  letI : TensorProduct.CompatibleSMul ℤ ℤ (POne n L)
      (SymmetricPower ℤ (Fin 1) (PZero L)) := TensorProduct.CompatibleSMul.int
  rw [terminalNumerator, Koszul.QuadraticUCT.twoGenerator,
    LinearMap.comp_apply]
  change terminalNumeratorExterior n L data hn
      (Koszul.QuadraticUCT.twoToExterior (pAugmentation n L)
        (pAugmentation_surjective n L) (pSmith n L)
          (exteriorPower.ιMulti ℤ 2 ![(pSmith n L).relationBasis i,
            (pSmith n L).relationBasis j] ⊗ₜ[ℤ]
              SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) = _
  rw [Koszul.QuadraticUCT.twoToExterior_generator,
    terminalNumeratorExterior_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [(pSmith n L).relation_eq j]
  have hdegree := map_zsmul (SymmetricPower.degreeOne (R := ℤ))
    ((pSmith n L).diagonal j : ℤ) ((pSmith n L).ambientBasis j)
  change terminalLift n L data hn
      ((pSmith n L).relationBasis i ⊗ₜ[ℤ]
        SymmetricPower.degreeOne (R := ℤ)
          (((pSmith n L).diagonal j : ℤ) • (pSmith n L).ambientBasis j)) = _
  calc
    _ = terminalLift n L data hn
        ((pSmith n L).relationBasis i ⊗ₜ[ℤ]
          (((pSmith n L).diagonal j : ℤ) •
            SymmetricPower.degreeOne (R := ℤ) ((pSmith n L).ambientBasis j))) := by
          apply congrArg (terminalLift n L data hn)
          apply congrArg (fun s ↦ (pSmith n L).relationBasis i ⊗ₜ[ℤ] s)
          exact hdegree
    _ = ((pSmith n L).diagonal j : ℤ) • terminalLift n L data hn
        ((pSmith n L).relationBasis i ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (R := ℤ) ((pSmith n L).ambientBasis j)) := by
          have ht : (pSmith n L).relationBasis i ⊗ₜ[ℤ]
              (((pSmith n L).diagonal j : ℤ) •
                SymmetricPower.degreeOne (R := ℤ) ((pSmith n L).ambientBasis j)) =
            ((pSmith n L).diagonal j : ℤ) •
              ((pSmith n L).relationBasis i ⊗ₜ[ℤ]
                SymmetricPower.degreeOne (R := ℤ) ((pSmith n L).ambientBasis j)) := by
            exact TensorProduct.tmul_smul _ _ _
          exact (congrArg (terminalLift n L data hn) ht).trans
            (map_zsmul (terminalLift n L data hn)
              ((pSmith n L).diagonal j : ℤ) _)
    _ = _ := by
      have hbasis : (pSmith n L).relationBasis i ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (R := ℤ) ((pSmith n L).ambientBasis j) =
        Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L) (i, j) := by
            exact (Koszul.QuadraticUCT.oneBasis_apply (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) i j).symm
      change ((pSmith n L).diagonal j : ℤ) •
        terminalLift n L data hn _ = _
      have hl := congrArg (terminalLift n L data hn) hbasis
      change ((pSmith n L).diagonal j : ℤ) •
        terminalLift n L data hn
          ((pSmith n L).relationBasis i ⊗ₜ[ℤ]
            SymmetricPower.degreeOne (R := ℤ) ((pSmith n L).ambientBasis j)) = _
      calc
        _ = ((pSmith n L).diagonal j : ℤ) • terminalLift n L data hn
            (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
              (pAugmentation_surjective n L) (pSmith n L) (i, j)) :=
          congrArg (fun z : ℤ ↦ ((pSmith n L).diagonal j : ℤ) • z) hl
        _ = _ := by
          rw [terminalLift_oneBasis]
          exact zsmul_eq_mul _ _

theorem terminalNumerator_divisible (hn : 2 ≤ n)
    (y : Koszul.Two (pPresentation n L) 0) :
    (2 ^ data.exponent : ℤ) ∣ terminalNumerator n L data hn y := by
  let castMap : ℤ →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
    (Int.castAddHom (ZMod (2 ^ data.exponent))).toIntLinearMap
  have hzero : castMap.comp (terminalNumeratorExterior n L data hn) = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    change (terminalNumeratorExterior n L data hn
      (exteriorPower.ιMulti ℤ 2 a) : ZMod (2 ^ data.exponent)) = 0
    rw [terminalNumeratorExterior_ιMulti, terminalLift_cast]
    exact terminalPhi_dOne_zero n L data hn (a 0) (a 1)
  change ((2 ^ data.exponent : ℕ) : ℤ) ∣ terminalNumerator n L data hn y
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change castMap (terminalNumerator n L data hn y) = 0
  change castMap (terminalNumeratorExterior n L data hn
    (Koszul.QuadraticUCT.twoToExterior (pAugmentation n L)
      (pAugmentation_surjective n L) (pSmith n L) y)) = 0
  exact LinearMap.congr_fun hzero _

/-- The manuscript cochain
`h_φ(a∧a') = φ̂(a,d a') / 2^e`, with exact division in `ℤ`. -/
def terminalDividedCochain (hn : 2 ≤ n) :
    Koszul.Two (pPresentation n L) 0 →ₗ[ℤ] ℤ :=
  Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
    (pow_pos (by decide) _) (terminalNumerator n L data hn)
    (terminalNumerator_divisible n L data hn)

theorem terminalDividedCochain_spec (hn : 2 ≤ n)
    (y : Koszul.Two (pPresentation n L) 0) :
    (2 ^ data.exponent : ℤ) * terminalDividedCochain n L data hn y =
      terminalNumerator n L data hn y :=
  Koszul.QuadraticUCT.mul_divideLinear (2 ^ data.exponent)
    (pow_pos (by decide) _) (terminalNumerator n L data hn)
    (terminalNumerator_divisible n L data hn) y

/-- The direct UCT character on the chosen terminal presentation. -/
def etaPresentation (hn : 2 ≤ n) :
    Koszul.homologyOne (pPresentation n L) 1 →ₗ[ℤ] LieRings.RatCircle :=
  Koszul.QuadraticUCT.uctCharacter (pAugmentation n L)
    (pAugmentation_surjective n L) (terminalDividedCochain n L data hn)
    (Koszul.QuadraticUCT.rationalPrimitive (pAugmentation n L)
      (pAugmentation_surjective n L) (pSmith n L)
      (terminalDividedCochain n L data hn))

/-- The terminal character `ηₙ : L₁S²(Vₙ) → ℚ/ℤ`. -/
def etaTerminal (hn : 2 ≤ n) :
    Koszul.FirstDerivedSymmetricPower 1 (V L n) →ₗ[ℤ] LieRings.RatCircle :=
  (etaPresentation n L data hn).comp
    (Koszul.Presentation.homologyComparisonEquiv (pPresentation n L) 1).symm.toLinearMap

/-- The exact ordered Smith formula used by the terminal PBW row. -/
theorem etaPresentation_horizontal (hn : 2 ≤ n)
    {i j : Fin (pSmith n L).rank} (hij : i < j) :
    etaPresentation n L data hn
        (Koszul.QuadraticUCT.horizontalClass (pAugmentation n L)
          (pAugmentation_surjective n L) (pSmith n L) hij) =
      (((Koszul.QuadraticUCT.ratio (pAugmentation n L)
          (pSmith n L) i j : ℤ) * terminalLiftEntry n L data hn i j : ℚ) /
        (2 ^ data.exponent : ℚ) : LieRings.RatCircle) := by
  let q : ℕ := 2 ^ data.exponent
  let S := pSmith n L
  let y := Koszul.QuadraticUCT.twoGenerator (pAugmentation n L)
    (pAugmentation_surjective n L) S i j
  let c := Koszul.QuadraticUCT.horizontalCycle (pAugmentation n L)
    (pAugmentation_surjective n L) S hij
  let h := terminalDividedCochain n L data hn
  let ext := Koszul.QuadraticUCT.rationalExtension (pAugmentation n L)
    (pAugmentation_surjective n L) S h
  have hdpos : 0 < S.diagonal i := S.diagonal_pos i
  have hqpos : 0 < q := pow_pos (by decide) _
  have hboundary :
      Koszul.dTwo (pPresentation n L) 0 y =
        (S.diagonal i : ℤ) • c.1 := by
    exact Koszul.QuadraticUCT.dTwo_twoGenerator (pAugmentation n L)
      (pAugmentation_surjective n L) S hij
  have hext : (S.diagonal i : ℚ) * ext c.1 = (h y : ℚ) := by
    calc
      (S.diagonal i : ℚ) * ext c.1 =
          ext ((S.diagonal i : ℤ) • c.1) := by
            rw [map_zsmul]
            norm_num [zsmul_eq_mul]
      _ = ext (Koszul.dTwo (pPresentation n L) 0 y) := by rw [hboundary]
      _ = (h y : ℚ) := Koszul.QuadraticUCT.rationalExtension_dTwo
        (pAugmentation n L) (pAugmentation_surjective n L) S h y
  have hh : (q : ℚ) * (h y : ℚ) =
      (S.diagonal j : ℚ) * terminalLiftEntry n L data hn i j := by
    exact_mod_cast terminalDividedCochain_spec n L data hn y |>.trans
      (by rw [terminalNumerator_twoGenerator])
  have hdratio := Koszul.QuadraticUCT.diagonal_mul_ratio
    (pAugmentation n L) S hij.le
  have hvalue : ext c.1 =
      ((Koszul.QuadraticUCT.ratio (pAugmentation n L) S i j : ℤ) *
        terminalLiftEntry n L data hn i j : ℚ) / (q : ℚ) := by
    have hdi : (S.diagonal i : ℚ) ≠ 0 := by positivity
    have hq : (q : ℚ) ≠ 0 := by positivity
    have hdratioQ : (S.diagonal j : ℚ) =
        (S.diagonal i : ℚ) *
          (Koszul.QuadraticUCT.ratio (pAugmentation n L) S i j : ℚ) := by
      exact_mod_cast hdratio.symm
    rw [hdratioQ] at hh
    apply (eq_div_iff hq).2
    apply (mul_left_cancel₀ hdi)
    calc
      (S.diagonal i : ℚ) * (ext c.1 * q) =
          (q : ℚ) * ((S.diagonal i : ℚ) * ext c.1) := by ring
      _ = (q : ℚ) * (h y : ℚ) := by rw [hext]
      _ = (S.diagonal i : ℚ) *
          (Koszul.QuadraticUCT.ratio (pAugmentation n L) S i j : ℚ) *
            terminalLiftEntry n L data hn i j := hh
      _ = (S.diagonal i : ℚ) *
          ((Koszul.QuadraticUCT.ratio (pAugmentation n L) S i j : ℚ) *
            terminalLiftEntry n L data hn i j) := by ring
  change Koszul.QuadraticUCT.uctCharacter (pAugmentation n L)
      (pAugmentation_surjective n L) h
      (Koszul.QuadraticUCT.rationalPrimitive (pAugmentation n L)
        (pAugmentation_surjective n L) S h)
        ((Koszul.boundariesOne (pPresentation n L) 1).mkQ c) = _
  change ((Koszul.QuadraticUCT.rationalPrimitive (pAugmentation n L)
      (pAugmentation_surjective n L) S h).value c : LieRings.RatCircle) = _
  change (ext c.1 : LieRings.RatCircle) = _
  rw [hvalue]
  congr 1
  dsimp only [S, q]
  norm_num

theorem etaTerminal_horizontal (hn : 2 ≤ n)
    {i j : Fin (pSmith n L).rank} (hij : i < j) :
    etaTerminal n L data hn
        (Koszul.Presentation.homologyComparisonEquiv
          (pPresentation n L) 1
          (Koszul.QuadraticUCT.horizontalClass (pAugmentation n L)
            (pAugmentation_surjective n L) (pSmith n L) hij)) =
      (((Koszul.QuadraticUCT.ratio (pAugmentation n L)
          (pSmith n L) i j : ℤ) * terminalLiftEntry n L data hn i j : ℚ) /
        (2 ^ data.exponent : ℚ) : LieRings.RatCircle) := by
  let x := Koszul.QuadraticUCT.horizontalClass (pAugmentation n L)
    (pAugmentation_surjective n L) (pSmith n L) hij
  let e := Koszul.Presentation.homologyComparisonEquiv (pPresentation n L) 1
  change etaPresentation n L data hn (e.symm (e x)) = _
  rw [e.symm_apply_apply]
  exact etaPresentation_horizontal n L data hn hij

end

end LieRings.MetabelianVanishing
