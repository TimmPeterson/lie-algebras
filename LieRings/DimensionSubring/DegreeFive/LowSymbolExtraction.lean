import LieRings.DimensionSubring.DegreeFive.LowSymbols
import LieRings.DimensionSubring.DegreeFive.SemanticCollector
import LieRings.DimensionSubring.DegreeFive.WordExpansion

/-!
# Extracting integral low symbols from the semantic ledger

The quadratic tensor truncation kills every associative word of length at least three.  Thus the
augmentation-five comparison term in a degree-five witness is invisible, while the free-Lie term
is remembered exactly by its class-two truncation.  Applying this observation to the exact
semantic collector identity gives a finite, integral low-symbol equation on the terminal packet
ledger.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u)

local notation "PX" => GeneratorModule X
local notation "QX" => QuadraticTensorTruncation PX

/-- Evaluation of an associative generator word in the quadratic tensor truncation. -/
@[simp]
theorem freeAlgebraToQuadraticTensor_freeAlgebraWord (xs : List X) :
    freeAlgebraToQuadraticTensor X (freeAlgebraWord X xs) =
      (xs.map fun x ↦
        QuadraticTensorTruncation.ofLinear PX (Finsupp.single x 1)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [freeAlgebraWord_cons, ih]

/-- A product containing at least three pure positive-degree factors vanishes. -/
theorem ofLinear_list_prod_eq_zero_of_three_le
    (xs : List PX) (hxs : 3 ≤ xs.length) :
    (xs.map (QuadraticTensorTruncation.ofLinear PX)).prod = 0 := by
  cases xs with
  | nil => simp at hxs
  | cons x xs =>
      cases xs with
      | nil => simp at hxs
      | cons y xs =>
          cases xs with
          | nil => simp at hxs
          | cons z rest =>
              simp only [List.map_cons, List.prod_cons]
              rw [← mul_assoc, ← mul_assoc,
                QuadraticTensorTruncation.ofLinear_mul_ofLinear_mul_ofLinear,
                zero_mul]

/-- Consequently every associative generator word of length at least three has zero quadratic
symbol. -/
theorem freeAlgebraToQuadraticTensor_freeAlgebraWord_eq_zero
    (xs : List X) (hxs : 3 ≤ xs.length) :
    freeAlgebraToQuadraticTensor X (freeAlgebraWord X xs) = 0 := by
  rw [freeAlgebraToQuadraticTensor_freeAlgebraWord]
  simpa only [List.map_map, Function.comp_apply] using
    (ofLinear_list_prod_eq_zero_of_three_le X
      (xs.map fun x ↦ Finsupp.single x 1) (by simpa using hxs))

/-- The standard monoid basis expansion, with the coefficient family fixed to be the actual
coefficient function of the free associative polynomial. -/
theorem freeAlgebra_eq_word_sum (p : FreeAlgebra ℤ X) :
    let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid p
    c.sum (fun w n ↦ n • freeAlgebraWord X (FreeMonoid.toList w)) = p := by
  let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid p
  calc
    c.sum (fun w n ↦ n • freeAlgebraWord X (FreeMonoid.toList w)) =
        c.sum (fun w n ↦ n •
          FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
            (Finsupp.single w 1)) := by
      apply Finsupp.sum_congr
      intro w hw
      rw [monoidBasisElement_eq_freeAlgebraWord]
    _ = FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm c := by
      symm
      calc
        FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm c =
            FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
              (c.sum Finsupp.single) := by
          congr 1
          exact (Finsupp.sum_single c).symm
        _ = c.sum (fun w n ↦
              FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
                (Finsupp.single w n)) := by
          rw [map_finsuppSum]
        _ = c.sum (fun w n ↦ n •
              FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
                (Finsupp.single w 1)) := by
          apply Finsupp.sum_congr
          intro w hw
          rw [← map_smul]
          congr 1
          symm
          calc
            (c w) • (Finsupp.single w (1 : ℤ) :
                MonoidAlgebra ℤ (FreeMonoid X)) =
                Finsupp.single w ((c w) • (1 : ℤ)) :=
              Finsupp.smul_single (c w) w (1 : ℤ)
            _ = Finsupp.single w (c w) := by
              rw [smul_eq_mul, mul_one]
    _ = p := FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm_apply_apply p

/-- Every free associative polynomial of minimum word length three has zero scalar, linear, and
quadratic symbol, integrally and without a choice of basis. -/
theorem freeAlgebraToQuadraticTensor_eq_zero_of_mem_associativeHigh_three
    {p : FreeAlgebra ℤ X}
    (hp : p ∈ FreeLieDimension.associativeHigh X 3) :
    freeAlgebraToQuadraticTensor X p = 0 := by
  let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid p
  rw [← freeAlgebra_eq_word_sum X p]
  rw [map_finsuppSum]
  classical
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro w hw
  change freeAlgebraToQuadraticTensor X
      ((c w) • freeAlgebraWord X (FreeMonoid.toList w)) = 0
  rw [map_zsmul,
    freeAlgebraToQuadraticTensor_freeAlgebraWord_eq_zero, smul_zero]
  simpa using hp hw

/-- Evaluate a free enveloping-algebra element in the quadratic tensor truncation. -/
def freeEnvelopingToQuadraticTensor :
    UEA ℤ (FreeLieAlgebra ℤ X) →ₐ[ℤ] QX :=
  (freeAlgebraToQuadraticTensor X).comp
    (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X).toAlgHom

/-- On a canonical Lie element, enveloping evaluation records exactly the integral class-two
symbol. -/
@[simp]
theorem freeEnvelopingToQuadraticTensor_iota (x : FreeLieAlgebra ℤ X) :
    freeEnvelopingToQuadraticTensor X
        (UniversalEnvelopingAlgebra.ι ℤ x) =
      ⟨0,
        (freeClassTwoTruncation X x).1,
        exteriorToTensor PX (freeClassTwoTruncation X x).2⟩ := by
  change freeAlgebraToQuadraticTensor X
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
        (UniversalEnvelopingAlgebra.ι ℤ x)) = _
  calc
    freeAlgebraToQuadraticTensor X
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
          (UniversalEnvelopingAlgebra.ι ℤ x)) =
        freeAlgebraToQuadraticTensor X
          (PBW.freeLieToFreeAlgebra ℤ X x) :=
      congrArg (freeAlgebraToQuadraticTensor X)
        (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra X x)
    _ = _ := freeAlgebraToQuadraticTensor_freeLieToFreeAlgebra X x

variable (L : Type u) [LieRing L]

/-- The augmentation-five comparison word in a free witness has zero quadratic symbol. -/
theorem FreeDimensionFiveWitness.freeEnvelopingToQuadraticTensor_highWord_eq_zero
    {a : L} (w : FreeDimensionFiveWitness L a) :
    freeEnvelopingToQuadraticTensor L w.highWord = 0 := by
  apply freeAlgebraToQuadraticTensor_eq_zero_of_mem_associativeHigh_three L
  exact FreeLieDimension.associativeHigh_mono L (by omega)
    w.highWord_mem_associativeHigh

/-! ## Exact packet classification in quadratic degree -/

local notation "F" => CanonicalFreeLie L
local notation "PL" => GeneratorModule L

/-- Every canonical free-Lie element has positive quadratic-truncation degree. -/
@[simp]
theorem freeEnvelopingToQuadraticTensor_iota_scalar (x : F) :
    (freeEnvelopingToQuadraticTensor L
      (UniversalEnvelopingAlgebra.ι ℤ x)).scalar = 0 := by
  rw [freeEnvelopingToQuadraticTensor_iota]

/-- The quadratic symbol of an enveloping word is the product of the symbols of its Lie
factors. -/
theorem freeEnvelopingToQuadraticTensor_envelopingWord
    (xs : List F) :
    freeEnvelopingToQuadraticTensor L (envelopingWord ℤ F xs) =
      (xs.map fun x ↦ freeEnvelopingToQuadraticTensor L
        (UniversalEnvelopingAlgebra.ι ℤ x)).prod := by
  induction xs with
  | nil => simp [envelopingWord]
  | cons x xs ih =>
      rw [envelopingWord_cons, map_mul, ih]
      rfl

/-- A marked relation packet with no external factor contributes precisely the class-two
symbol of its relation. -/
theorem freeEnvelopingToQuadraticTensor_packet_nil
    (r : CanonicalLieRelationsIdeal L) (s : ℕ) (hs : 0 < s)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh L s) :
    freeEnvelopingToQuadraticTensor L
        (FilteredRelationPacket.withFactors L r s hs hr []).value =
      ⟨0,
        (freeClassTwoTruncation L (r : F)).1,
        exteriorToTensor PL (freeClassTwoTruncation L (r : F)).2⟩ := by
  rw [FilteredRelationPacket.value]
  change freeEnvelopingToQuadraticTensor L
      (envelopingWord ℤ F [] * UniversalEnvelopingAlgebra.ι ℤ (r : F) *
        envelopingWord ℤ F []) = _
  rw [envelopingWord_nil, one_mul, mul_one,
    freeEnvelopingToQuadraticTensor_iota]

/-- A marked relation packet with one external Lie factor contributes exactly the ordered
tensor of the two linear class-two components.  In particular, no division by two is hidden
in the extraction. -/
theorem freeEnvelopingToQuadraticTensor_packet_singleton
    (r : CanonicalLieRelationsIdeal L) (s : ℕ) (hs : 0 < s)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh L s)
    (x : FilteredLieFactor L) :
    freeEnvelopingToQuadraticTensor L
        (FilteredRelationPacket.withFactors L r s hs hr [x]).value =
      ⟨0, 0,
        (freeClassTwoTruncation L (r : F)).1 ⊗ₜ[ℤ]
          (freeClassTwoTruncation L x.value).1⟩ := by
  rw [FilteredRelationPacket.value]
  change freeEnvelopingToQuadraticTensor L
      (envelopingWord ℤ F [] * UniversalEnvelopingAlgebra.ι ℤ (r : F) *
        envelopingWord ℤ F [x.value]) = _
  rw [envelopingWord_nil, one_mul, envelopingWord_cons, envelopingWord_nil,
    mul_one, map_mul]
  rw [QuadraticTensorTruncation.mul_eq_quadratic_of_scalar_eq_zero]
  · rw [freeEnvelopingToQuadraticTensor_iota, freeEnvelopingToQuadraticTensor_iota]
  · exact freeEnvelopingToQuadraticTensor_iota_scalar L (r : F)
  · exact freeEnvelopingToQuadraticTensor_iota_scalar L x.value

/-- Packets with at least two external Lie factors have zero scalar, linear, and quadratic
symbol.  This is the exhaustive terminal-packet cutoff needed after the numerical source
table: the marked relation itself supplies the third positive-degree factor. -/
theorem freeEnvelopingToQuadraticTensor_packet_eq_zero_of_two_le_length
    (p : FilteredRelationPacket L) (hp : 2 ≤ p.factors.length) :
    freeEnvelopingToQuadraticTensor L p.value = 0 := by
  rcases p with ⟨r, s, hs, hr, factors⟩
  cases factors with
  | nil => simp at hp
  | cons x xs =>
    cases xs with
    | nil => simp at hp
    | cons y rest =>
      rw [FilteredRelationPacket.value]
      change freeEnvelopingToQuadraticTensor L
          (envelopingWord ℤ F [] * UniversalEnvelopingAlgebra.ι ℤ (r : F) *
            envelopingWord ℤ F (x.value :: y.value ::
              (rest.map FilteredLieFactor.value))) = 0
      rw [envelopingWord_nil, one_mul, envelopingWord_cons,
        envelopingWord_cons, map_mul, map_mul, map_mul]
      let ar : QuadraticTensorTruncation PL :=
        freeEnvelopingToQuadraticTensor L
          (UniversalEnvelopingAlgebra.ι ℤ (r : F))
      let ax : QuadraticTensorTruncation PL :=
        freeEnvelopingToQuadraticTensor L
          (UniversalEnvelopingAlgebra.ι ℤ x.value)
      let ay : QuadraticTensorTruncation PL :=
        freeEnvelopingToQuadraticTensor L
          (UniversalEnvelopingAlgebra.ι ℤ y.value)
      let tail : QuadraticTensorTruncation PL :=
        freeEnvelopingToQuadraticTensor L
          (envelopingWord ℤ F (rest.map FilteredLieFactor.value))
      have htriple :=
        QuadraticTensorTruncation.mul_mul_eq_zero_of_scalar_eq_zero
          PL
          (freeEnvelopingToQuadraticTensor L
            (UniversalEnvelopingAlgebra.ι ℤ (r : F)))
          (freeEnvelopingToQuadraticTensor L
            (UniversalEnvelopingAlgebra.ι ℤ x.value))
          (freeEnvelopingToQuadraticTensor L
            (UniversalEnvelopingAlgebra.ι ℤ y.value))
          (freeEnvelopingToQuadraticTensor_iota_scalar L (r : F))
          (freeEnvelopingToQuadraticTensor_iota_scalar L x.value)
          (freeEnvelopingToQuadraticTensor_iota_scalar L y.value)
      change ar * (ax * (ay * tail)) = 0
      calc
        ar * (ax * (ay * tail)) = (ar * ax) * (ay * tail) :=
          (mul_assoc ar ax (ay * tail)).symm
        _ = (ar * ax * ay) * tail :=
          (mul_assoc (ar * ax) ay tail).symm
        _ = 0 := by
          change
            (freeEnvelopingToQuadraticTensor L
                (UniversalEnvelopingAlgebra.ι ℤ (r : F)) *
              freeEnvelopingToQuadraticTensor L
                (UniversalEnvelopingAlgebra.ι ℤ x.value) *
              freeEnvelopingToQuadraticTensor L
                (UniversalEnvelopingAlgebra.ι ℤ y.value)) * tail = 0
          rw [htriple, zero_mul]

/-- The completely explicit low symbol of a terminal relation packet.  Only the empty and
singleton external-factor cases survive. -/
def terminalPacketLowSymbol (p : FilteredRelationPacket L) :
    QuadraticTensorTruncation PL :=
  match p.factors with
  | [] =>
      ⟨0,
        (freeClassTwoTruncation L (p.relation : F)).1,
        exteriorToTensor PL
          (freeClassTwoTruncation L (p.relation : F)).2⟩
  | [x] =>
      ⟨0, 0,
        (freeClassTwoTruncation L (p.relation : F)).1 ⊗ₜ[ℤ]
          (freeClassTwoTruncation L x.value).1⟩
  | _ => 0

/-- Packetwise correctness of the explicit terminal low symbol. -/
theorem freeEnvelopingToQuadraticTensor_packet_value
    (p : FilteredRelationPacket L) :
    freeEnvelopingToQuadraticTensor L p.value =
      terminalPacketLowSymbol L p := by
  rcases p with ⟨r, s, hs, hr, factors⟩
  cases factors with
  | nil =>
      exact freeEnvelopingToQuadraticTensor_packet_nil L r s hs hr
  | cons x xs =>
      cases xs with
      | nil =>
          exact freeEnvelopingToQuadraticTensor_packet_singleton L r s hs hr x
      | cons y rest =>
          exact freeEnvelopingToQuadraticTensor_packet_eq_zero_of_two_le_length L
            ⟨r, s, hs, hr, x :: y :: rest⟩ (by simp)

/-- Linear component of the explicit packet symbol. -/
def terminalPacketLinear (p : FilteredRelationPacket L) : PL :=
  match p.factors with
  | [] => (freeClassTwoTruncation L (p.relation : F)).1
  | _ => 0

/-- Ordered quadratic component of the explicit packet symbol. -/
def terminalPacketQuadratic (p : FilteredRelationPacket L) : PL ⊗[ℤ] PL :=
  match p.factors with
  | [] => exteriorToTensor PL
      (freeClassTwoTruncation L (p.relation : F)).2
  | [x] =>
      (freeClassTwoTruncation L (p.relation : F)).1 ⊗ₜ[ℤ]
        (freeClassTwoTruncation L x.value).1
  | _ => 0

@[simp]
theorem terminalPacketLowSymbol_scalar (p : FilteredRelationPacket L) :
    (terminalPacketLowSymbol L p).scalar = 0 := by
  rcases p with ⟨r, s, hs, hr, factors⟩
  cases factors with
  | nil => rfl
  | cons x xs =>
      cases xs <;> rfl

@[simp]
theorem terminalPacketLowSymbol_linear (p : FilteredRelationPacket L) :
    (terminalPacketLowSymbol L p).linear = terminalPacketLinear L p := by
  rcases p with ⟨r, s, hs, hr, factors⟩
  cases factors with
  | nil => rfl
  | cons x xs =>
      cases xs <;> rfl

@[simp]
theorem terminalPacketLowSymbol_quadratic (p : FilteredRelationPacket L) :
    (terminalPacketLowSymbol L p).quadratic = terminalPacketQuadratic L p := by
  rcases p with ⟨r, s, hs, hr, factors⟩
  cases factors with
  | nil => rfl
  | cons x xs =>
      cases xs <;> rfl

/-- Applying low-symbol evaluation to the exact semantic collector identity leaves precisely the
class-two symbol of the witness's free-Lie lift. -/
theorem FinitePlacedRelationLedger.lowSymbol_semanticNormalForm
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    freeEnvelopingToQuadraticTensor L
        ((semanticPacketCollector L).evaluate ledger.semanticNormalForm) =
      ⟨0,
        (freeClassTwoTruncation L w.lieLift).1,
        exteriorToTensor (GeneratorModule L)
          (freeClassTwoTruncation L w.lieLift).2⟩ := by
  rw [ledger.evaluate_semanticNormalForm_eq_relationDifference,
    map_sub, freeEnvelopingToQuadraticTensor_iota,
    w.freeEnvelopingToQuadraticTensor_highWord_eq_zero, sub_zero]

/-- Expanded coefficient form of `lowSymbol_semanticNormalForm`.  This is the finite integral
equation consumed by the remaining packet-to-certificate classification. -/
theorem FinitePlacedRelationLedger.semanticNormalForm_lowSymbol_sum
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    ledger.semanticNormalForm.sum (fun p n ↦ n •
        freeEnvelopingToQuadraticTensor L p.value) =
      ⟨0,
        (freeClassTwoTruncation L w.lieLift).1,
        exteriorToTensor (GeneratorModule L)
          (freeClassTwoTruncation L w.lieLift).2⟩ := by
  calc
    ledger.semanticNormalForm.sum (fun p n ↦ n •
        freeEnvelopingToQuadraticTensor L p.value) =
        freeEnvelopingToQuadraticTensor L
          ((semanticPacketCollector L).evaluate ledger.semanticNormalForm) := by
      change ledger.semanticNormalForm.sum (fun p n ↦ n •
          freeEnvelopingToQuadraticTensor L p.value) =
        freeEnvelopingToQuadraticTensor L
          (ledger.semanticNormalForm.sum (fun p n ↦ n • p.value))
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro p hp
      rw [map_zsmul]
    _ = _ := ledger.lowSymbol_semanticNormalForm

/-- **Classified terminal low-symbol equation.**  This is the same exact ledger equality with
every packet replaced by its proved empty/singleton normal form. -/
theorem FinitePlacedRelationLedger.semanticNormalForm_terminalLowSymbol_sum
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    ledger.semanticNormalForm.sum (fun p n ↦ n • terminalPacketLowSymbol L p) =
      ⟨0,
        (freeClassTwoTruncation L w.lieLift).1,
        exteriorToTensor (GeneratorModule L)
          (freeClassTwoTruncation L w.lieLift).2⟩ := by
  rw [← ledger.semanticNormalForm_lowSymbol_sum]
  apply Finsupp.sum_congr
  intro p hp
  rw [freeEnvelopingToQuadraticTensor_packet_value]

/-- Linear equation extracted from the classified terminal ledger. -/
theorem FinitePlacedRelationLedger.semanticNormalForm_linear_sum
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    ledger.semanticNormalForm.sum (fun p n ↦ n • terminalPacketLinear L p) =
      (freeClassTwoTruncation L w.lieLift).1 := by
  calc
    ledger.semanticNormalForm.sum (fun p n ↦ n • terminalPacketLinear L p) =
        QuadraticTensorTruncation.linearProjection (GeneratorModule L)
          (ledger.semanticNormalForm.sum
            (fun p n ↦ n • terminalPacketLowSymbol L p)) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro p hp
      simp only [map_zsmul, QuadraticTensorTruncation.linearProjection_apply,
        terminalPacketLowSymbol_linear]
    _ = _ := by
      rw [ledger.semanticNormalForm_terminalLowSymbol_sum]
      rfl

/-- Ordered integral quadratic equation extracted from the classified terminal ledger. -/
theorem FinitePlacedRelationLedger.semanticNormalForm_quadratic_sum
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    ledger.semanticNormalForm.sum (fun p n ↦ n • terminalPacketQuadratic L p) =
      exteriorToTensor (GeneratorModule L)
        (freeClassTwoTruncation L w.lieLift).2 := by
  calc
    ledger.semanticNormalForm.sum (fun p n ↦ n • terminalPacketQuadratic L p) =
        QuadraticTensorTruncation.quadraticProjection (GeneratorModule L)
          (ledger.semanticNormalForm.sum
            (fun p n ↦ n • terminalPacketLowSymbol L p)) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro p hp
      simp only [map_zsmul, QuadraticTensorTruncation.quadraticProjection_apply,
        terminalPacketLowSymbol_quadratic]
    _ = _ := by
      rw [ledger.semanticNormalForm_terminalLowSymbol_sum]
      rfl

/-- For the adapted `γ₃`-witness, the complete scalar/linear/quadratic terminal-symbol ledger
vanishes.  This is the integral cycle equation used in the invariant extraction. -/
theorem FinitePlacedRelationLedger.semanticNormalForm_terminalLowSymbol_sum_eq_zero
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w)
    (hw : w.lieLift ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 2) :
    ledger.semanticNormalForm.sum (fun p n ↦ n • terminalPacketLowSymbol L p) = 0 := by
  rw [ledger.semanticNormalForm_terminalLowSymbol_sum,
    FreeDimensionFiveWitness.freeClassTwoTruncation_lieLift_eq_zero L w hw]
  apply QuadraticTensorTruncation.ext <;> simp

/-- Linear part of the adapted terminal ledger. -/
theorem FinitePlacedRelationLedger.semanticNormalForm_linear_sum_eq_zero
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w)
    (hw : w.lieLift ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 2) :
    ledger.semanticNormalForm.sum (fun p n ↦ n • terminalPacketLinear L p) = 0 := by
  rw [ledger.semanticNormalForm_linear_sum,
    FreeDimensionFiveWitness.freeClassTwoTruncation_lieLift_eq_zero L w hw]
  rfl

/-- Ordered quadratic part of the adapted terminal ledger. -/
theorem FinitePlacedRelationLedger.semanticNormalForm_quadratic_sum_eq_zero
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w)
    (hw : w.lieLift ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 2) :
    ledger.semanticNormalForm.sum (fun p n ↦ n • terminalPacketQuadratic L p) = 0 := by
  rw [ledger.semanticNormalForm_quadratic_sum,
    FreeDimensionFiveWitness.freeClassTwoTruncation_lieLift_eq_zero L w hw]
  simp

end

end DegreeFive

end LieRings
