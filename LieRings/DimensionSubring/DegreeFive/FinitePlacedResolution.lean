import LieRings.DimensionSubring.DegreeFive.FinitePlacedWitness
import LieRings.DimensionSubring.DegreeFive.ResolutionCycle
import LieRings.DimensionSubring.DegreeFive.QuadraticCoordinates
import LieRings.DimensionSubring.DegreeFive.FiniteClassTwoBasis

/-!
# The class-two resolution of a finite free presentation

This is the presentation-independent counterpart of `RelationTruncation`.  It permits the
finite Smith collector to feed the invariant resolution argument without assuming that the
target Lie ring is finite.
-/

namespace LieRings

open scoped TensorProduct

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X
local notation "P" => GeneratorModule X
local notation "M" => FreeClassTwo P

/-- Evaluation of the finite free generator module. -/
def finiteGeneratorEvaluation
    (evaluation : LieHom ℤ F L) : P →ₗ[ℤ] L :=
  Finsupp.linearCombination ℤ (fun x ↦ evaluation (FreeLieAlgebra.of ℤ x))

@[simp]
theorem finiteGeneratorEvaluation_single
    (evaluation : LieHom ℤ F L) (x : X) :
    finiteGeneratorEvaluation X L evaluation (Finsupp.single x 1) =
      evaluation (FreeLieAlgebra.of ℤ x) := by
  simp [finiteGeneratorEvaluation]

/-- The class-two presentation map induced by the chosen finite generators. -/
def finiteClassTwoEvaluation
    (evaluation : LieHom ℤ F L) : M →ₗ⁅ℤ⁆ ModGammaThree L :=
  freeClassTwoEvaluation P L (finiteGeneratorEvaluation X L evaluation)

/-- Evaluation commutes with the free class-two truncation. -/
theorem finite_evaluation_comp_truncation
    (evaluation : LieHom ℤ F L) :
    (finiteClassTwoEvaluation X L evaluation).comp (freeClassTwoTruncation X) =
      (UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L 2)).comp evaluation := by
  apply FreeLieAlgebra.hom_ext
  intro x
  change finiteClassTwoEvaluation X L evaluation
      (freeClassTwoTruncation X (FreeLieAlgebra.of ℤ x)) =
    LieSubmodule.Quotient.mk (evaluation (FreeLieAlgebra.of ℤ x))
  rw [freeClassTwoTruncation_of]
  change (LieSubmodule.Quotient.mk
      (finiteGeneratorEvaluation X L evaluation (Finsupp.single x 1)) :
        ModGammaThree L) + degreeTwoEvaluation P L
          (finiteGeneratorEvaluation X L evaluation) 0 = _
  rw [finiteGeneratorEvaluation_single, map_zero, add_zero]

/-- Relations in the finite explicit class-two presentation. -/
abbrev FiniteClassTwoResolutionRelations
    (evaluation : LieHom ℤ F L) :=
  LinearMap.ker (finiteClassTwoEvaluation X L evaluation).toLinearMap

/-- Truncate an actual defining relation to the finite class-two resolution kernel. -/
def finiteRelationTruncation
    (evaluation : LieHom ℤ F L) :
    LinearMap.ker evaluation.toLinearMap →ₗ[ℤ]
      FiniteClassTwoResolutionRelations X L evaluation where
  toFun r := ⟨freeClassTwoTruncation X (r : F), by
    rw [LinearMap.mem_ker]
    change finiteClassTwoEvaluation X L evaluation
        (freeClassTwoTruncation X (r : F)) = 0
    have hcomp := LieHom.congr_fun
      (finite_evaluation_comp_truncation X L evaluation) (r : F)
    change finiteClassTwoEvaluation X L evaluation
        (freeClassTwoTruncation X (r : F)) =
      LieSubmodule.Quotient.mk (evaluation (r : F)) at hcomp
    rw [hcomp, show evaluation (r : F) = 0 from r.property]
    rfl⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (freeClassTwoTruncation X) (x : F) (y : F)
  map_smul' n x := by
    apply Subtype.ext
    exact map_smul (freeClassTwoTruncation X) n (x : F)

@[simp]
theorem finiteRelationTruncation_coe
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    ((finiteRelationTruncation X L evaluation r :
        FiniteClassTwoResolutionRelations X L evaluation) : M) =
      freeClassTwoTruncation X (r : F) :=
  rfl

/-- Inclusion of finite class-two presentation relations. -/
def finiteClassTwoResolutionRelationInclusion
    (evaluation : LieHom ℤ F L) :
    FiniteClassTwoResolutionRelations X L evaluation →ₗ[ℤ] M :=
  (LinearMap.ker
    (finiteClassTwoEvaluation X L evaluation).toLinearMap).subtype

/-- Boundary in the finite class-two presentation resolution. -/
def finiteClassTwoResolutionBoundary
    (evaluation : LieHom ℤ F L) :
    (FiniteClassTwoResolutionRelations X L evaluation ⊗[ℤ] M) →ₗ[ℤ]
      (M ⊗[ℤ] M) :=
  TensorProduct.map
    (finiteClassTwoResolutionRelationInclusion X L evaluation) LinearMap.id

@[simp]
theorem finiteClassTwoResolutionBoundary_tmul
    (evaluation : LieHom ℤ F L)
    (r : FiniteClassTwoResolutionRelations X L evaluation) (x : M) :
    finiteClassTwoResolutionBoundary X L evaluation (r ⊗ₜ[ℤ] x) =
      (r : M) ⊗ₜ[ℤ] x := by
  exact TensorProduct.map_tmul
    (finiteClassTwoResolutionRelationInclusion X L evaluation) LinearMap.id r x

/-- The actual kernel relation carried by a Smith-tagged packet. -/
def finitePacketRelationKernel
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) :
    LinearMap.ker evaluation.toLinearMap :=
  (p.toAlgebraPacket X L evaluation).relation

@[simp]
theorem finitePacketRelationKernel_coe
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) :
    (finitePacketRelationKernel X L evaluation p : F) =
      p.relation.value X L evaluation :=
  rfl

/-- The sole external homogeneous factor when a placed packet has exactly one.  Both possible
positions are oriented as relation-then-factor for the resolution tensor. -/
def finitePacketUniqueFactor?
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) :
    Option (LowHomogeneousBasisIndex X) :=
  match p.left, p.right with
  | [], [x] => some x
  | [x], [] => some x
  | _, _ => none

/-- Resolution tensor contributed by a terminal packet of total weight below five. -/
def finiteTerminalPacketResolutionTensor
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) :
    FiniteClassTwoResolutionRelations X L evaluation ⊗[ℤ] M :=
  if p.totalWeight X < 5 then
    match finitePacketUniqueFactor? X L evaluation p with
    | some x =>
        finiteRelationTruncation X L evaluation
            (finitePacketRelationKernel X L evaluation p) ⊗ₜ[ℤ]
          freeClassTwoTruncation X (lowHomogeneousBasisValue X x)
    | none => 0
  else 0

/-- The finite resolution tensor extracted from the fully collected Smith ledger. -/
def FinitePresentationDimensionFiveWitness.resolutionTensor
    {evaluation : LieHom ℤ F L} {a : L}
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) :
    FiniteClassTwoResolutionRelations X L evaluation ⊗[ℤ] M :=
  w.terminalPackets.sum (fun p n ↦
    n • finiteTerminalPacketResolutionTensor X L evaluation p)

/-- Applying the finite resolution boundary forgets only the kernel proof. -/
theorem finiteClassTwoResolutionBoundary_terminalPacket
    (evaluation : LieHom ℤ F L)
    (p : FiniteSmithPlacedPacket X L evaluation) :
    finiteClassTwoResolutionBoundary X L evaluation
        (finiteTerminalPacketResolutionTensor X L evaluation p) =
      if p.totalWeight X < 5 then
        match finitePacketUniqueFactor? X L evaluation p with
        | some x =>
            freeClassTwoTruncation X (p.relation.value X L evaluation) ⊗ₜ[ℤ]
              freeClassTwoTruncation X (lowHomogeneousBasisValue X x)
        | none => 0
      else 0 := by
  classical
  unfold finiteTerminalPacketResolutionTensor
  split
  · rename_i hlow
    split
    · rename_i x hx
      rw [finiteClassTwoResolutionBoundary_tmul]
      rfl
    · simp
  · simp

/-- Coefficient form of the boundary extracted from the terminal packet ledger. -/
theorem FinitePresentationDimensionFiveWitness.resolutionTensor_boundary
    {evaluation : LieHom ℤ F L} {a : L}
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) :
    finiteClassTwoResolutionBoundary X L evaluation w.resolutionTensor =
      w.terminalPackets.sum (fun p n ↦ n •
        if p.totalWeight X < 5 then
          match finitePacketUniqueFactor? X L evaluation p with
          | some x =>
              freeClassTwoTruncation X (p.relation.value X L evaluation) ⊗ₜ[ℤ]
                freeClassTwoTruncation X (lowHomogeneousBasisValue X x)
          | none => 0
        else 0) := by
  unfold FinitePresentationDimensionFiveWitness.resolutionTensor
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, finiteClassTwoResolutionBoundary_terminalPacket]

/-! ## Mapping the finite resolution into the canonical one -/

/-- Send a finite formal generator to the corresponding canonical generator of `L`. -/
def finiteGeneratorToCanonical
    (evaluation : LieHom ℤ F L) : P →ₗ[ℤ] GeneratorModule L :=
  Finsupp.lmapDomain ℤ ℤ (fun x ↦ evaluation (FreeLieAlgebra.of ℤ x))

@[simp]
theorem finiteGeneratorToCanonical_single
    (evaluation : LieHom ℤ F L) (x : X) :
    finiteGeneratorToCanonical X L evaluation (Finsupp.single x 1) =
      Finsupp.single (evaluation (FreeLieAlgebra.of ℤ x)) 1 := by
  simp [finiteGeneratorToCanonical]

/-- Evaluation after inclusion in the canonical generator module is the original finite
generator evaluation. -/
theorem canonicalGeneratorEvaluation_comp_finiteGeneratorToCanonical
    (evaluation : LieHom ℤ F L) :
    (canonicalGeneratorEvaluation L).comp
        (finiteGeneratorToCanonical X L evaluation) =
      finiteGeneratorEvaluation X L evaluation := by
  apply (Finsupp.basisSingleOne (R := ℤ) (ι := X)).ext
  intro x
  simp [finiteGeneratorToCanonical_single, finiteGeneratorEvaluation_single]

/-- The induced linear map between the explicit free class-two modules. -/
def finiteClassTwoToCanonical
    (evaluation : LieHom ℤ F L) :
    M →ₗ[ℤ] FreeClassTwo (GeneratorModule L) where
  toFun z :=
    (finiteGeneratorToCanonical X L evaluation z.1,
      exteriorPower.map 2 (finiteGeneratorToCanonical X L evaluation) z.2)
  map_add' x y := by simp
  map_smul' n x := by simp

@[simp]
theorem finiteClassTwoToCanonical_apply
    (evaluation : LieHom ℤ F L) (z : M) :
    finiteClassTwoToCanonical X L evaluation z =
      (finiteGeneratorToCanonical X L evaluation z.1,
        exteriorPower.map 2 (finiteGeneratorToCanonical X L evaluation) z.2) :=
  rfl

/-- Naturality of the degree-two evaluation under the finite-to-canonical generator map. -/
theorem degreeTwoEvaluation_finiteToCanonical
    (evaluation : LieHom ℤ F L) (w : ⋀[ℤ]^2 P) :
    degreeTwoEvaluation (GeneratorModule L) L (canonicalGeneratorEvaluation L)
        (exteriorPower.map 2 (finiteGeneratorToCanonical X L evaluation) w) =
      degreeTwoEvaluation P L (finiteGeneratorEvaluation X L evaluation) w := by
  have hmaps :
      (degreeTwoEvaluation (GeneratorModule L) L
          (canonicalGeneratorEvaluation L)).comp
          (exteriorPower.map 2 (finiteGeneratorToCanonical X L evaluation)) =
        degreeTwoEvaluation P L
          (finiteGeneratorEvaluation X L evaluation) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change degreeTwoEvaluation (GeneratorModule L) L
        (canonicalGeneratorEvaluation L)
          (exteriorPower.map 2 (finiteGeneratorToCanonical X L evaluation)
            (wedgeTwo P (v 0) (v 1))) =
      degreeTwoEvaluation P L (finiteGeneratorEvaluation X L evaluation)
        (wedgeTwo P (v 0) (v 1))
    have hmap : exteriorPower.map 2
        (finiteGeneratorToCanonical X L evaluation)
          (wedgeTwo P (v 0) (v 1)) =
        wedgeTwo (GeneratorModule L)
          (finiteGeneratorToCanonical X L evaluation (v 0))
          (finiteGeneratorToCanonical X L evaluation (v 1)) := by
      exact exteriorPower.map_apply_ιMulti
        (n := 2) (finiteGeneratorToCanonical X L evaluation) ![v 0, v 1]
    rw [hmap, degreeTwoEvaluation_wedge, degreeTwoEvaluation_wedge]
    have hcomp := canonicalGeneratorEvaluation_comp_finiteGeneratorToCanonical
      X L evaluation
    have hzero := LinearMap.congr_fun hcomp (v 0)
    have hone := LinearMap.congr_fun hcomp (v 1)
    change canonicalGeneratorEvaluation L
        (finiteGeneratorToCanonical X L evaluation (v 0)) =
      finiteGeneratorEvaluation X L evaluation (v 0) at hzero
    change canonicalGeneratorEvaluation L
        (finiteGeneratorToCanonical X L evaluation (v 1)) =
      finiteGeneratorEvaluation X L evaluation (v 1) at hone
    rw [hzero, hone]
  exact LinearMap.congr_fun hmaps w

/-- The canonical and finite class-two presentation maps commute. -/
theorem canonicalClassTwoEvaluation_comp_finiteClassTwoToCanonical
    (evaluation : LieHom ℤ F L) :
    (canonicalClassTwoEvaluation L).toLinearMap.comp
        (finiteClassTwoToCanonical X L evaluation) =
      (finiteClassTwoEvaluation X L evaluation).toLinearMap := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply]
  change
    (LieSubmodule.Quotient.mk
      (canonicalGeneratorEvaluation L
        (finiteGeneratorToCanonical X L evaluation z.1)) :
          ModGammaThree L) +
        degreeTwoEvaluation (GeneratorModule L) L
          (canonicalGeneratorEvaluation L)
          (exteriorPower.map 2
            (finiteGeneratorToCanonical X L evaluation) z.2) =
      (LieSubmodule.Quotient.mk
        (finiteGeneratorEvaluation X L evaluation z.1) :
          ModGammaThree L) +
        degreeTwoEvaluation P L
          (finiteGeneratorEvaluation X L evaluation) z.2
  have hcomp := LinearMap.congr_fun
    (canonicalGeneratorEvaluation_comp_finiteGeneratorToCanonical
      X L evaluation) z.1
  change canonicalGeneratorEvaluation L
      (finiteGeneratorToCanonical X L evaluation z.1) =
    finiteGeneratorEvaluation X L evaluation z.1 at hcomp
  rw [hcomp, degreeTwoEvaluation_finiteToCanonical]

/-- A finite class-two relation maps to a relation in the canonical resolution. -/
def finiteResolutionRelationToCanonical
    (evaluation : LieHom ℤ F L) :
    FiniteClassTwoResolutionRelations X L evaluation →ₗ[ℤ]
      ClassTwoResolutionRelations L where
  toFun r := ⟨finiteClassTwoToCanonical X L evaluation (r : M), by
    rw [LinearMap.mem_ker]
    have hcomp := LinearMap.congr_fun
      (canonicalClassTwoEvaluation_comp_finiteClassTwoToCanonical
        X L evaluation) (r : M)
    change canonicalClassTwoEvaluation L
        (finiteClassTwoToCanonical X L evaluation (r : M)) =
      finiteClassTwoEvaluation X L evaluation (r : M) at hcomp
    change canonicalClassTwoEvaluation L
        (finiteClassTwoToCanonical X L evaluation (r : M)) = 0
    rw [hcomp]
    exact r.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (finiteClassTwoToCanonical X L evaluation) (x : M) (y : M)
  map_smul' n x := by
    apply Subtype.ext
    exact map_smul (finiteClassTwoToCanonical X L evaluation) n (x : M)

/-- Map a finite resolution tensor to the canonical resolution tensor. -/
def finiteResolutionTensorToCanonical
    (evaluation : LieHom ℤ F L) :
    (FiniteClassTwoResolutionRelations X L evaluation ⊗[ℤ] M) →ₗ[ℤ]
      (ClassTwoResolutionRelations L ⊗[ℤ]
        FreeClassTwo (GeneratorModule L)) :=
  TensorProduct.map (finiteResolutionRelationToCanonical X L evaluation)
    (finiteClassTwoToCanonical X L evaluation)

/-- Naturality of the resolution boundary. -/
theorem classTwoResolutionBoundary_finiteResolutionTensorToCanonical
    (evaluation : LieHom ℤ F L)
    (chi : FiniteClassTwoResolutionRelations X L evaluation ⊗[ℤ] M) :
    classTwoResolutionBoundary L
        (finiteResolutionTensorToCanonical X L evaluation chi) =
      TensorProduct.map (finiteClassTwoToCanonical X L evaluation)
        (finiteClassTwoToCanonical X L evaluation)
          (finiteClassTwoResolutionBoundary X L evaluation chi) := by
  induction chi using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
      change classTwoResolutionBoundary L
          (finiteResolutionRelationToCanonical X L evaluation r ⊗ₜ[ℤ]
            finiteClassTwoToCanonical X L evaluation x) =
        TensorProduct.map (finiteClassTwoToCanonical X L evaluation)
          (finiteClassTwoToCanonical X L evaluation) ((r : M) ⊗ₜ[ℤ] x)
      rw [classTwoResolutionBoundary_tmul, TensorProduct.map_tmul]
      rfl
  | add x y hx hy => simp [map_add, hx, hy]

/-! ## Alternating lift and transport -/

/-- The ordered alternating lift of the boundary produced by the finite packet ledger. -/
def FinitePresentationDimensionFiveWitness.resolutionBeta
    {evaluation : LieHom ℤ F L} {a : L}
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) :
    ⋀[ℤ]^2 M :=
  orderedWedgeSection (finiteHomogeneousClassTwoBasis X)
    (finiteClassTwoResolutionBoundary X L evaluation w.resolutionTensor)

/-- The quadratic equation required to turn the ordered lift into an exact alternating
boundary. -/
def FinitePresentationDimensionFiveWitness.BoundaryNormalEquation
    {evaluation : LieHom ℤ F L} {a : L}
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) : Prop :=
  orderedTensorNormal (finiteHomogeneousClassTwoBasis X)
      (finiteClassTwoResolutionBoundary X L evaluation w.resolutionTensor) = 0

/-- The finite ordered boundary equation gives an exact source alternating boundary. -/
theorem FinitePresentationDimensionFiveWitness.exteriorToTensor_resolutionBeta
    {evaluation : LieHom ℤ F L} {a : L}
    (w : FinitePresentationDimensionFiveWitness X L evaluation a)
    (hboundary : w.BoundaryNormalEquation) :
    exteriorToTensor M w.resolutionBeta =
      finiteClassTwoResolutionBoundary X L evaluation w.resolutionTensor := by
  exact exteriorToTensor_orderedWedgeSection_of_normal_eq_zero
    (finiteHomogeneousClassTwoBasis X)
    (finiteClassTwoResolutionBoundary X L evaluation w.resolutionTensor)
    hboundary

/-- The finite alternating lift mapped into the canonical free class-two module. -/
def FinitePresentationDimensionFiveWitness.canonicalBeta
    {evaluation : LieHom ℤ F L} {a : L}
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) :
    ⋀[ℤ]^2 (FreeClassTwo (GeneratorModule L)) :=
  exteriorPower.map 2 (finiteClassTwoToCanonical X L evaluation)
    w.resolutionBeta

/-- The finite resolution tensor mapped into the canonical presentation. -/
def FinitePresentationDimensionFiveWitness.canonicalChi
    {evaluation : LieHom ℤ F L} {a : L}
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) :
    ClassTwoResolutionRelations L ⊗[ℤ]
      FreeClassTwo (GeneratorModule L) :=
  finiteResolutionTensorToCanonical X L evaluation w.resolutionTensor

/-- After transport, the source ordered equation is exactly the boundary equation expected by
the canonical resolution-cycle certificate. -/
theorem FinitePresentationDimensionFiveWitness.canonical_alternating_boundary
    {evaluation : LieHom ℤ F L} {a : L}
    (w : FinitePresentationDimensionFiveWitness X L evaluation a)
    (hboundary : w.BoundaryNormalEquation) :
    exteriorToTensor (FreeClassTwo (GeneratorModule L)) w.canonicalBeta =
      classTwoResolutionBoundary L w.canonicalChi := by
  have hnat := LinearMap.congr_fun
    (exteriorToTensor_naturality (finiteClassTwoToCanonical X L evaluation))
      w.resolutionBeta
  change TensorProduct.map (finiteClassTwoToCanonical X L evaluation)
      (finiteClassTwoToCanonical X L evaluation)
        (exteriorToTensor M w.resolutionBeta) =
    exteriorToTensor (FreeClassTwo (GeneratorModule L)) w.canonicalBeta at hnat
  rw [← hnat,
    FinitePresentationDimensionFiveWitness.exteriorToTensor_resolutionBeta
      (X := X) (L := L) w hboundary,
    ← classTwoResolutionBoundary_finiteResolutionTensorToCanonical]
  rfl

/-- The second exact output of placed PBW extraction: the represented Lie element is the sum of
the low and mixed bracket values of the transported alternating tensor. -/
def FinitePresentationDimensionFiveWitness.LedgerEvaluation
    {evaluation : LieHom ℤ F L} {a : L}
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) : Prop :=
  a =
    freeClassTwoLowBracket L
        (freeClassTwoExteriorLow (GeneratorModule L) w.canonicalBeta) +
      freeClassTwoMixedBracket L
        (freeClassTwoExteriorMixed (GeneratorModule L) w.canonicalBeta)

/-- The two checked PBW extraction equations produce the canonical resolution-cycle
certificate. -/
def FinitePresentationDimensionFiveWitness.toResolutionCycleCertificate
    {evaluation : LieHom ℤ F L} {a : L}
    (hclass : lowerCentralSeries ℤ L 3 = ⊥)
    (w : FinitePresentationDimensionFiveWitness X L evaluation a)
    (hboundary : w.BoundaryNormalEquation)
    (hledger : w.LedgerEvaluation) :
    ResolutionCycleCertificate L hclass a :=
  ResolutionCycleCertificate.ofBoundaryAndLedgerEvaluation L hclass a
    w.canonicalBeta w.canonicalChi
    (FinitePresentationDimensionFiveWitness.canonical_alternating_boundary
      (X := X) (L := L) w hboundary) hledger

/-- Sufficiency of finite placed extraction in a class-three Lie ring. -/
theorem FinitePresentationDimensionFiveWitness.value_eq_zero_of_extraction
    {evaluation : LieHom ℤ F L} {a : L}
    (hclass : lowerCentralSeries ℤ L 3 = ⊥)
    (w : FinitePresentationDimensionFiveWitness X L evaluation a)
    (hboundary : w.BoundaryNormalEquation)
    (hledger : w.LedgerEvaluation) : a = 0 :=
  (FinitePresentationDimensionFiveWitness.toResolutionCycleCertificate
    (X := X) (L := L) hclass w hboundary hledger).value_eq_zero

end

end DegreeFive

end LieRings
