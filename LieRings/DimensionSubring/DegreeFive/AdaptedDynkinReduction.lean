import LieRings.DimensionSubring.DegreeFive.AdaptedGammaThree
import LieRings.DimensionSubring.DegreeFive.AdaptedPreThetaBridge
import LieRings.DimensionSubring.DegreeFive.AdaptedWitnessBridge

/-!
# The Dynkin reduction in degree five

This file defines the coordinate-valued degree-three Dynkin functional, proves its three
elementary identities, and uses them to identify the terminal adapted ledger's formal `z`
coefficient with the actual coordinate of the represented element in `γ₃`.  Consequently the
fifth dimension subring vanishes under the standing reduction alone.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

variable {L : Type u} [LieRing L]

namespace StandingReductionData

local notation "F" => CanonicalFreeLie L
local notation "ev" => canonicalFreeLieEvaluation L

open Coordinate Coordinate.Data Coordinate.Data.CollectedExpression

/-- The right-normed triple bracket, bundled in `γ₃(L)`. -/
def dynkinTripleGammaThree (R : StandingReductionData L) (x y z : L) :
    lowerCentralSeries ℤ L 2 :=
  ⟨⁅x, ⁅y, z⁆⁆, by
    have hyz : ⁅y, z⁆ ∈ lowerCentralSeries ℤ L 1 := by
      change ⁅y, z⁆ ∈ LieModule.lowerCentralSeries ℤ L L (0 + 1)
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
    change ⁅x, ⁅y, z⁆⁆ ∈ LieModule.lowerCentralSeries ℤ L L (1 + 1)
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hyz⟩

/-- The degree-three Dynkin coordinate of one free associative word. -/
def dynkinWordCoordinate (R : StandingReductionData L) (w : FreeMonoid L) : ZMod R.q :=
  match FreeMonoid.toList w with
  | [x, y, z] => R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z)
  | _ => 0

/-- The coordinate-valued degree-three Dynkin functional on the enveloping algebra of the
canonical free Lie presentation. -/
def dynkinThreeCoordinate (R : StandingReductionData L) :
    UEA ℤ F →ₗ[ℤ] ZMod R.q :=
  (Finsupp.linearCombination ℤ R.dynkinWordCoordinate).comp
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap.comp
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L).toLinearMap)

/-- The Dynkin functional sees no element of associative minimum length at least four. -/
theorem dynkinThreeCoordinate_eq_zero_of_mem_associativeHigh_four
    (R : StandingReductionData L) (u : UEA ℤ F)
    (hu : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L u ∈
      FreeLieDimension.associativeHigh L 4) :
    R.dynkinThreeCoordinate u = 0 := by
  classical
  let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L u)
  change c.sum (fun w n ↦ n • R.dynkinWordCoordinate w) = 0
  calc
    _ = c.sum (fun _ _ ↦ (0 : ZMod R.q)) := by
      apply Finsupp.sum_congr
      intro w hw
      have hw' : w ∈ c.support := hw
      have hlen : 4 ≤ w.length := hu hw'
      have hnot : ∀ x y z : L, FreeMonoid.toList w ≠ [x, y, z] := by
        intro x y z hxyz
        have : w.length = 3 := by simp [FreeMonoid.length, hxyz]
        omega
      rw [show R.dynkinWordCoordinate w = 0 by
        simp [dynkinWordCoordinate]]
      exact smul_zero _
    _ = 0 := by
      unfold Finsupp.sum
      simp

private theorem dynkinThreeCoordinate_generator_triple
    (R : StandingReductionData L) (x y z : L) :
    R.dynkinThreeCoordinate
      (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x : F) *
        UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ y : F) *
        UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ z : F)) =
      R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) := by
  have hword :
      UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x : F) *
          UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ y : F) *
          UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ z : F) =
        envelopingWord ℤ F ([x, y, z].map (FreeLieAlgebra.of ℤ)) := by
    simp [envelopingWord, mul_assoc]
  rw [hword]
  unfold dynkinThreeCoordinate
  simp only [LinearMap.comp_apply]
  change (Finsupp.linearCombination ℤ R.dynkinWordCoordinate)
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
          (envelopingWord ℤ F ([x, y, z].map (FreeLieAlgebra.of ℤ))))) = _
  rw [universalEnvelopingEquiv_envelopingWord_of]
  have hbasis : FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (freeAlgebraWord L [x, y, z]) =
      Finsupp.single (FreeMonoid.ofList [x, y, z]) (1 : ℤ) := by
    apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.injective
    rw [FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm_apply_apply]
    simpa using
      (monoidBasisElement_eq_freeAlgebraWord (X := L)
        (FreeMonoid.ofList [x, y, z])).symm
  rw [hbasis]
  change (Finsupp.single (FreeMonoid.ofList [x, y, z]) (1 : ℤ)).sum
      (fun w n => n • R.dynkinWordCoordinate w) = _
  rw [Finsupp.sum_single_index (by module)]
  change (1 : ℤ) • R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) = _
  exact one_smul ℤ _

private theorem dynkinThreeCoordinate_generator_bracket
    (R : StandingReductionData L) (x y z : L) :
    R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x : F) *
          UniversalEnvelopingAlgebra.ι ℤ
            ⁅(FreeLieAlgebra.of ℤ y : F), FreeLieAlgebra.of ℤ z⁆) =
      (2 : ℤ) • R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) ∧
    R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ
            ⁅(FreeLieAlgebra.of ℤ y : F), FreeLieAlgebra.of ℤ z⁆ *
          UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x : F)) =
      -R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) := by
  have hswap : R.dynkinTripleGammaThree x z y =
      -R.dynkinTripleGammaThree x y z := by
    apply Subtype.ext
    change ⁅x, ⁅z, y⁆⁆ = -⁅x, ⁅y, z⁆⁆
    calc
      ⁅x, ⁅z, y⁆⁆ = ⁅x, -⁅y, z⁆⁆ :=
        congrArg (fun t => ⁅x, t⁆) (lie_skew z y).symm
      _ = -⁅x, ⁅y, z⁆⁆ := lie_neg x ⁅y, z⁆
  have hjacobi : R.dynkinTripleGammaThree y z x -
      R.dynkinTripleGammaThree z y x = -R.dynkinTripleGammaThree x y z := by
    apply Subtype.ext
    change ⁅y, ⁅z, x⁆⁆ - ⁅z, ⁅y, x⁆⁆ = -⁅x, ⁅y, z⁆⁆
    rw [← lie_lie, lie_skew]
  constructor
  · rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, mul_sub, map_sub,
      ← mul_assoc, ← mul_assoc,
      dynkinThreeCoordinate_generator_triple,
      dynkinThreeCoordinate_generator_triple, hswap]
    have hneg : R.gammaThreeEquiv (-R.dynkinTripleGammaThree x y z) =
        -R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) :=
      R.gammaThreeEquiv.toAddMonoidHom.map_neg _
    rw [hneg]
    rw [two_zsmul]
    abel
  · rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, sub_mul, map_sub,
      dynkinThreeCoordinate_generator_triple,
      dynkinThreeCoordinate_generator_triple]
    calc
      R.gammaThreeEquiv (R.dynkinTripleGammaThree y z x) -
          R.gammaThreeEquiv (R.dynkinTripleGammaThree z y x) =
          R.gammaThreeEquiv (R.dynkinTripleGammaThree y z x -
            R.dynkinTripleGammaThree z y x) :=
        (R.gammaThreeEquiv.toAddMonoidHom.map_sub _ _).symm
      _ = R.gammaThreeEquiv (-R.dynkinTripleGammaThree x y z) :=
        congrArg R.gammaThreeEquiv hjacobi
      _ = -R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) :=
        R.gammaThreeEquiv.toAddMonoidHom.map_neg _

private theorem freeMagma_eq_of_of_length_one (w : FreeMagma L)
    (hw : w.length = 1) : ∃ x : L, w = FreeMagma.of x := by
  cases w with
  | of x => exact ⟨x, rfl⟩
  | mul a b =>
      have ha := FreeMagma.length_pos a
      have hb := FreeMagma.length_pos b
      change a.length + b.length = 1 at hw
      omega

private theorem freeMagma_eq_mul_of_length_two (w : FreeMagma L)
    (hw : w.length = 2) : ∃ x y : L, w = FreeMagma.of x * FreeMagma.of y := by
  cases w with
  | of x => simp at hw
  | mul a b =>
      have ha := FreeMagma.length_pos a
      have hb := FreeMagma.length_pos b
      change a.length + b.length = 2 at hw
      have hal : a.length = 1 := by omega
      have hbl : b.length = 1 := by omega
      obtain ⟨x, rfl⟩ := freeMagma_eq_of_of_length_one a hal
      obtain ⟨y, rfl⟩ := freeMagma_eq_of_of_length_one b hbl
      exact ⟨x, y, rfl⟩

private theorem freeMagma_length_three_cases (w : FreeMagma L)
    (hw : w.length = 3) :
    (∃ x y z : L, w = FreeMagma.of x * (FreeMagma.of y * FreeMagma.of z)) ∨
    (∃ x y z : L, w = (FreeMagma.of x * FreeMagma.of y) * FreeMagma.of z) := by
  cases w with
  | of x => simp at hw
  | mul a b =>
      have ha := FreeMagma.length_pos a
      have hb := FreeMagma.length_pos b
      change a.length + b.length = 3 at hw
      rcases (show (a.length = 1 ∧ b.length = 2) ∨
          (a.length = 2 ∧ b.length = 1) by omega) with hab | hab
      · obtain ⟨x, rfl⟩ := freeMagma_eq_of_of_length_one a hab.1
        obtain ⟨y, z, rfl⟩ := freeMagma_eq_mul_of_length_two b hab.2
        exact Or.inl ⟨x, y, z, rfl⟩
      · obtain ⟨x, y, rfl⟩ := freeMagma_eq_mul_of_length_two a hab.1
        obtain ⟨z, rfl⟩ := freeMagma_eq_of_of_length_one b hab.2
        exact Or.inr ⟨x, y, z, rfl⟩

/-- A literal magma word, regarded as an element of its exact homogeneous component. -/
private def magmaExactSingle (n : ℕ)
    (w : {w : FreeMagma L // w.length = n}) : magmaExact L n :=
  ⟨Finsupp.single w.1 1, by
    intro v hv
    have hvw : v = w.1 := by
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hv) (by simp [hne])
    simpa [hvw] using w.2⟩

/-- Literal words span an exact homogeneous magma component. -/
private theorem span_magmaExactSingle (n : ℕ) :
    Submodule.span ℤ (Set.range (magmaExactSingle (L := L) n)) = ⊤ := by
  apply top_unique
  rintro ⟨p, hp⟩ -
  let G := Submodule.span ℤ (Set.range (magmaExactSingle (L := L) n))
  have hpmap : p ∈ G.map (magmaExact L n).subtype := by
    rw [magmaExact, Finsupp.supported_eq_span_single] at hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
        obtain ⟨w, hw, rfl⟩ := hp
        refine ⟨magmaExactSingle n ⟨w, hw⟩, ?_, rfl⟩
        exact Submodule.subset_span ⟨_, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add a b ha hb hpa hpb => exact Submodule.add_mem _ hpa hpb
    | smul c p hp hrec => exact Submodule.smul_mem _ c hrec
  obtain ⟨q, hq, hqp⟩ := hpmap
  have heq : q = (⟨p, hp⟩ : magmaExact L n) := by
    apply Subtype.ext
    exact hqp
  simpa only [G, heq] using hq

private theorem freeLieMkLinear_single_mul (a b : FreeMagma L) :
    FreeLieDimension.freeLieMkLinear L (Finsupp.single (a * b) 1) =
      ⁅FreeLieDimension.freeLieMkLinear L (Finsupp.single a 1),
        FreeLieDimension.freeLieMkLinear L (Finsupp.single b 1)⁆ := by
  let sa : FreeNonUnitalNonAssocAlgebra ℤ L := Finsupp.single a 1
  let sb : FreeNonUnitalNonAssocAlgebra ℤ L := Finsupp.single b 1
  have hs : (Finsupp.single (a * b) (1 : ℤ) :
      FreeNonUnitalNonAssocAlgebra ℤ L) = sa * sb := by
    simpa only [sa, sb, one_mul] using
      (MonoidAlgebra.single_mul_single a b (1 : ℤ) (1 : ℤ)).symm
  rw [hs, FreeLieDimension.freeLieMkLinear_mul]

private theorem freeLieMkLinear_single_of (x : L) :
    FreeLieDimension.freeLieMkLinear L (Finsupp.single (FreeMagma.of x) 1) =
      FreeLieAlgebra.of ℤ x :=
  rfl

private theorem dynkinThreeCoordinate_magma_three
    (R : StandingReductionData L) (w : FreeMagma L) (hw : w.length = 3) :
    R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ
          (FreeLieDimension.freeLieMkLinear L (Finsupp.single w 1))) =
      (3 : ℤ) • R.gammaThreeEquiv
        ⟨ev (FreeLieDimension.freeLieMkLinear L (Finsupp.single w 1)), by
          letI : Finite L := R.finite_inst
          apply R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh (n := 3)
          exact ⟨Finsupp.single w 1, by
            intro v hv
            have hvw : v = w := by
              by_contra hne
              exact (Finsupp.mem_support_iff.mp hv) (by simp [hne])
            subst v
            exact hw.ge,
            rfl⟩⟩ := by
  rcases freeMagma_length_three_cases w hw with hright | hleft
  · obtain ⟨x, y, z, rfl⟩ := hright
    let coord : lowerCentralSeries ℤ L 2 :=
      ⟨ev (FreeLieDimension.freeLieMkLinear L
          (Finsupp.single (FreeMagma.of x *
            (FreeMagma.of y * FreeMagma.of z)) 1)), by
        letI : Finite L := R.finite_inst
        apply R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh (n := 3)
        exact ⟨Finsupp.single (FreeMagma.of x *
          (FreeMagma.of y * FreeMagma.of z)) 1, by
            intro v hv
            have hvw : v = FreeMagma.of x *
                (FreeMagma.of y * FreeMagma.of z) := by
              by_contra hne
              exact (Finsupp.mem_support_iff.mp hv) (by simp [hne])
            subst v
            simp, rfl⟩⟩
    change R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ
          (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single (FreeMagma.of x *
              (FreeMagma.of y * FreeMagma.of z)) 1))) =
      (3 : ℤ) • R.gammaThreeEquiv coord
    have hcoord : coord = R.dynkinTripleGammaThree x y z := by
      apply Subtype.ext
      simp only [coord, freeLieMkLinear_single_mul, freeLieMkLinear_single_of,
        LieHom.map_lie, canonicalFreeLieEvaluation_of]
      rfl
    rw [hcoord, freeLieMkLinear_single_mul, freeLieMkLinear_single_mul]
    have hmixed := dynkinThreeCoordinate_generator_bracket R x y z
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, map_sub]
    simp only [freeLieMkLinear_single_of]
    rw [hmixed.1, hmixed.2]
    change (2 : ℤ) • R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) -
        -R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) =
      (3 : ℤ) • R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z)
    rw [two_zsmul, show (3 : ℤ) •
        R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) =
        R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) +
          R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) +
          R.gammaThreeEquiv (R.dynkinTripleGammaThree x y z) by module]
    abel
  · obtain ⟨x, y, z, rfl⟩ := hleft
    let coord : lowerCentralSeries ℤ L 2 :=
      ⟨ev (FreeLieDimension.freeLieMkLinear L
          (Finsupp.single ((FreeMagma.of x * FreeMagma.of y) *
            FreeMagma.of z) 1)), by
        letI : Finite L := R.finite_inst
        apply R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh (n := 3)
        exact ⟨Finsupp.single ((FreeMagma.of x * FreeMagma.of y) *
          FreeMagma.of z) 1, by
            intro v hv
            have hvw : v = (FreeMagma.of x * FreeMagma.of y) *
                FreeMagma.of z := by
              by_contra hne
              exact (Finsupp.mem_support_iff.mp hv) (by simp [hne])
            subst v
            simp, rfl⟩⟩
    change R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ
          (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single ((FreeMagma.of x * FreeMagma.of y) *
              FreeMagma.of z) 1))) =
      (3 : ℤ) • R.gammaThreeEquiv coord
    have hmixed := dynkinThreeCoordinate_generator_bracket R z x y
    have hcoord : coord = -R.dynkinTripleGammaThree z x y := by
      apply Subtype.ext
      simp only [coord, freeLieMkLinear_single_mul, freeLieMkLinear_single_of,
        LieHom.map_lie, canonicalFreeLieEvaluation_of]
      exact (lie_skew ⁅x, y⁆ z).symm
    rw [hcoord, freeLieMkLinear_single_mul, freeLieMkLinear_single_mul,
      LieHom.map_lie, LieRing.of_associative_ring_bracket, map_sub]
    simp only [freeLieMkLinear_single_of]
    rw [hmixed.2, hmixed.1]
    have hneg (t : lowerCentralSeries ℤ L 2) :
        R.gammaThreeEquiv (-t) = -R.gammaThreeEquiv t :=
      R.gammaThreeEquiv.toAddMonoidHom.map_neg t
    rw [hneg]
    rw [two_zsmul, show (3 : ℤ) •
        (-R.gammaThreeEquiv (R.dynkinTripleGammaThree z x y)) =
        -R.gammaThreeEquiv (R.dynkinTripleGammaThree z x y) +
          -R.gammaThreeEquiv (R.dynkinTripleGammaThree z x y) +
          -R.gammaThreeEquiv (R.dynkinTripleGammaThree z x y) by module]
    abel

/-- Exactly the three elementary Dynkin identities used by the terminal-ledger argument. -/
structure DynkinProperties (R : StandingReductionData L) : Prop where
  exactThree : letI : Finite L := R.finite_inst
    ∀ f : freeLieExact L 3,
    R.dynkinThreeCoordinate (UniversalEnvelopingAlgebra.ι ℤ (f : F)) =
      (3 : ℤ) • R.gammaThreeEquiv (exactThreeEvaluation L L ev f)
  oneTwo : letI : Finite L := R.finite_inst
    ∀ (i : CoordinateI L) (k : CoordinateK L),
      R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
            UniversalEnvelopingAlgebra.ι ℤ (R.coordinateY k)) =
        (2 : ℤ) • R.coordinateGMod i k ∧
      R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateY k) *
            UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i)) =
        -R.coordinateGMod i k
  oneOneOne : letI : Finite L := R.finite_inst
    ∀ (i j l : CoordinateI L),
    R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
          UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j) *
          UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l)) =
      R.gammaThreeEquiv
        (R.dynkinTripleGammaThree
          (ev (R.coordinateX i)) (ev (R.coordinateX j)) (ev (R.coordinateX l)))

/-- Degree-three normalization for the explicitly defined Dynkin functional. -/
theorem dynkinThreeCoordinate_exactThree (R : StandingReductionData L) :
    letI : Finite L := R.finite_inst
    ∀ f : freeLieExact L 3,
    R.dynkinThreeCoordinate (UniversalEnvelopingAlgebra.ι ℤ (f : F)) =
      (3 : ℤ) • R.gammaThreeEquiv (exactThreeEvaluation L L ev f) := by
  letI : Finite L := R.finite_inst
  classical
  intro f
  let mkExact : magmaExact L 3 →ₗ[ℤ] F :=
    (FreeLieDimension.freeLieMkLinear L).domRestrict (magmaExact L 3)
  let evalExact : magmaExact L 3 →ₗ[ℤ] lowerCentralSeries ℤ L 2 :=
    ((canonicalFreeLieEvaluation L).toLinearMap.comp mkExact).codRestrict
      (lowerCentralSeries ℤ L 2) (fun p => by
      change ev (FreeLieDimension.freeLieMkLinear L p.1) ∈ lowerCentralSeries ℤ L 2
      apply R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh (n := 3)
      exact ⟨p.1, fun w hw => (p.2 hw).ge, rfl⟩)
  let lhs : magmaExact L 3 →ₗ[ℤ] ZMod R.q :=
    R.dynkinThreeCoordinate.comp
      ((UniversalEnvelopingAlgebra.ι ℤ).toLinearMap.comp mkExact)
  let rhs : magmaExact L 3 →ₗ[ℤ] ZMod R.q :=
    (3 : ℤ) •
      (R.gammaThreeEquiv.toAddMonoidHom.toIntLinearMap.comp evalExact)
  have heq : lhs = rhs := by
    apply LinearMap.ext_on (span_magmaExactSingle (L := L) 3)
    rintro p ⟨w, rfl⟩
    change R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ
          (FreeLieDimension.freeLieMkLinear L (Finsupp.single w.1 1))) = _
    simpa only [lhs, rhs, mkExact, evalExact, LinearMap.smul_apply,
      LinearMap.comp_apply] using dynkinThreeCoordinate_magma_three R w.1 w.2
  obtain ⟨p, hp, hpf⟩ := f.property
  let pExact : magmaExact L 3 := ⟨p, hp⟩
  have hvalue := LinearMap.congr_fun heq pExact
  have hpGamma : ev (FreeLieDimension.freeLieMkLinear L p) ∈
      lowerCentralSeries ℤ L 2 := by
    apply R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh (n := 3)
    exact ⟨p, fun w hw => (hp hw).ge, rfl⟩
  change R.dynkinThreeCoordinate
      (UniversalEnvelopingAlgebra.ι ℤ (FreeLieDimension.freeLieMkLinear L p)) =
    (3 : ℤ) • R.gammaThreeEquiv
      ⟨ev (FreeLieDimension.freeLieMkLinear L p), hpGamma⟩ at hvalue
  have heval :
      (⟨ev (FreeLieDimension.freeLieMkLinear L p), hpGamma⟩ :
        lowerCentralSeries ℤ L 2) = exactThreeEvaluation L L ev f := by
    apply Subtype.ext
    change ev (FreeLieDimension.freeLieMkLinear L p) = ev (f : F)
    rw [hpf]
  calc
    R.dynkinThreeCoordinate (UniversalEnvelopingAlgebra.ι ℤ (f : F)) =
        R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ
            (FreeLieDimension.freeLieMkLinear L p)) := by rw [hpf]
    _ = (3 : ℤ) • R.gammaThreeEquiv
        ⟨ev (FreeLieDimension.freeLieMkLinear L p), hpGamma⟩ := hvalue
    _ = (3 : ℤ) • R.gammaThreeEquiv (exactThreeEvaluation L L ev f) := by
      rw [heval]

/-- The two mixed degree-`(1,2)` formulas for the explicit Dynkin functional. -/
theorem dynkinThreeCoordinate_oneTwo (R : StandingReductionData L) :
    letI : Finite L := R.finite_inst
    ∀ (i : CoordinateI L) (k : CoordinateK L),
      R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
            UniversalEnvelopingAlgebra.ι ℤ (R.coordinateY k)) =
        (2 : ℤ) • R.coordinateGMod i k ∧
      R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateY k) *
            UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i)) =
        -R.coordinateGMod i k := by
  letI : Finite L := R.finite_inst
  classical
  intro i k
  let x : freeLieExact L 1 := collectedHomogeneousBasis L L ev 1 i
  let y : freeLieExact L 2 := collectedHomogeneousBasis L L ev 2 k
  let mk1 : magmaExact L 1 →ₗ[ℤ] F :=
    (FreeLieDimension.freeLieMkLinear L).domRestrict (magmaExact L 1)
  let mk2 : magmaExact L 2 →ₗ[ℤ] F :=
    (FreeLieDimension.freeLieMkLinear L).domRestrict (magmaExact L 2)
  let u1 := (UniversalEnvelopingAlgebra.ι ℤ).toLinearMap.comp mk1
  let u2 := (UniversalEnvelopingAlgebra.ι ℤ).toLinearMap.comp mk2
  let product : magmaExact L 1 →ₗ[ℤ] magmaExact L 2 →ₗ[ℤ] ZMod R.q :=
    (((LinearMap.mul ℤ (UEA ℤ F)).compl₂ u2).comp u1).compr₂
      R.dynkinThreeCoordinate
  let reverseProduct : magmaExact L 1 →ₗ[ℤ]
      magmaExact L 2 →ₗ[ℤ] ZMod R.q :=
    (((LinearMap.flip (LinearMap.mul ℤ (UEA ℤ F))).compl₂ u2).comp u1).compr₂
      R.dynkinThreeCoordinate
  let e1 := (canonicalFreeLieEvaluation L).toLinearMap.comp mk1
  let e2 := (canonicalFreeLieEvaluation L).toLinearMap.comp mk2
  let bracket : magmaExact L 1 →ₗ[ℤ]
      magmaExact L 2 →ₗ[ℤ] lowerCentralSeries ℤ L 2 := {
    toFun := fun p => ({
      toFun := fun q => ⟨⁅e1 p, e2 q⁆, by
        have hq : e2 q ∈ lowerCentralSeries ℤ L 1 := by
          change ev (FreeLieDimension.freeLieMkLinear L q.1) ∈ _
          apply R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh (n := 2)
          exact ⟨q.1, fun w hw => (q.2 hw).ge, rfl⟩
        change ⁅e1 p, e2 q⁆ ∈ LieModule.lowerCentralSeries ℤ L L (1 + 1)
        rw [LieModule.lowerCentralSeries_succ]
        exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hq⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        change ⁅e1 p, e2 (a + b)⁆ = ⁅e1 p, e2 a⁆ + ⁅e1 p, e2 b⁆
        rw [map_add, lie_add]
      map_smul' := by
        intro n a
        apply Subtype.ext
        change ⁅e1 p, e2 (n • a)⁆ = n • ⁅e1 p, e2 a⁆
        rw [map_smul, lie_zsmul] } :
        magmaExact L 2 →ₗ[ℤ] lowerCentralSeries ℤ L 2)
    map_add' p q := by
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      change ⁅e1 (p + q), e2 a⁆ = ⁅e1 p, e2 a⁆ + ⁅e1 q, e2 a⁆
      rw [map_add, add_lie]
    map_smul' n p := by
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      change ⁅e1 (n • p), e2 a⁆ = n • ⁅e1 p, e2 a⁆
      rw [map_smul, smul_lie] }
  let gamma : magmaExact L 1 →ₗ[ℤ] magmaExact L 2 →ₗ[ℤ] ZMod R.q :=
    bracket.compr₂ R.gammaThreeEquiv.toAddMonoidHom.toIntLinearMap
  have hproduct : product = (2 : ℤ) • gamma := by
    apply LinearMap.ext_on (span_magmaExactSingle (L := L) 1)
    rintro p ⟨wp, rfl⟩
    apply LinearMap.ext_on (span_magmaExactSingle (L := L) 2)
    rintro q ⟨wq, rfl⟩
    rcases wp with ⟨wp, hwp⟩
    rcases wq with ⟨wq, hwq⟩
    obtain ⟨x₀, hx₀⟩ := freeMagma_eq_of_of_length_one wp hwp
    obtain ⟨y₀, z₀, hyz₀⟩ := freeMagma_eq_mul_of_length_two wq hwq
    subst wp
    subst wq
    let pp : magmaExact L 1 :=
      magmaExactSingle 1 ⟨FreeMagma.of x₀, hwp⟩
    let qq : magmaExact L 2 :=
      magmaExactSingle 2 ⟨FreeMagma.of y₀ * FreeMagma.of z₀, hwq⟩
    change R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ
            (FreeLieDimension.freeLieMkLinear L
              (Finsupp.single (FreeMagma.of x₀) 1)) *
          UniversalEnvelopingAlgebra.ι ℤ
            (FreeLieDimension.freeLieMkLinear L
              (Finsupp.single (FreeMagma.of y₀ * FreeMagma.of z₀) 1))) =
      (2 : ℤ) • R.gammaThreeEquiv (bracket pp qq)
    have hc : bracket pp qq = R.dynkinTripleGammaThree x₀ y₀ z₀ := by
      apply Subtype.ext
      change ⁅ev (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single (FreeMagma.of x₀) 1)),
          ev (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single (FreeMagma.of y₀ * FreeMagma.of z₀) 1))⁆ =
        ⁅x₀, ⁅y₀, z₀⁆⁆
      rw [freeLieMkLinear_single_mul]
      simp only [freeLieMkLinear_single_of, LieHom.map_lie,
        canonicalFreeLieEvaluation_of]
    rw [freeLieMkLinear_single_mul]
    rw [hc]
    simpa only [freeLieMkLinear_single_of, LieHom.map_lie,
      canonicalFreeLieEvaluation_of] using
        (dynkinThreeCoordinate_generator_bracket R x₀ y₀ z₀).1
  have hreverse : reverseProduct = -gamma := by
    apply LinearMap.ext_on (span_magmaExactSingle (L := L) 1)
    rintro p ⟨wp, rfl⟩
    apply LinearMap.ext_on (span_magmaExactSingle (L := L) 2)
    rintro q ⟨wq, rfl⟩
    rcases wp with ⟨wp, hwp⟩
    rcases wq with ⟨wq, hwq⟩
    obtain ⟨x₀, hx₀⟩ := freeMagma_eq_of_of_length_one wp hwp
    obtain ⟨y₀, z₀, hyz₀⟩ := freeMagma_eq_mul_of_length_two wq hwq
    subst wp
    subst wq
    let pp : magmaExact L 1 :=
      magmaExactSingle 1 ⟨FreeMagma.of x₀, hwp⟩
    let qq : magmaExact L 2 :=
      magmaExactSingle 2 ⟨FreeMagma.of y₀ * FreeMagma.of z₀, hwq⟩
    change R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ
            (FreeLieDimension.freeLieMkLinear L
              (Finsupp.single (FreeMagma.of y₀ * FreeMagma.of z₀) 1)) *
          UniversalEnvelopingAlgebra.ι ℤ
            (FreeLieDimension.freeLieMkLinear L
              (Finsupp.single (FreeMagma.of x₀) 1))) =
      -R.gammaThreeEquiv (bracket pp qq)
    have hc : bracket pp qq = R.dynkinTripleGammaThree x₀ y₀ z₀ := by
      apply Subtype.ext
      change ⁅ev (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single (FreeMagma.of x₀) 1)),
          ev (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single (FreeMagma.of y₀ * FreeMagma.of z₀) 1))⁆ =
        ⁅x₀, ⁅y₀, z₀⁆⁆
      rw [freeLieMkLinear_single_mul]
      simp only [freeLieMkLinear_single_of, LieHom.map_lie,
        canonicalFreeLieEvaluation_of]
    rw [freeLieMkLinear_single_mul]
    rw [hc]
    simpa only [freeLieMkLinear_single_of, LieHom.map_lie,
      canonicalFreeLieEvaluation_of] using
        (dynkinThreeCoordinate_generator_bracket R x₀ y₀ z₀).2
  obtain ⟨p, hp, hpx⟩ := x.property
  obtain ⟨q, hq, hqy⟩ := y.property
  let px : magmaExact L 1 := ⟨p, hp⟩
  let qy : magmaExact L 2 := ⟨q, hq⟩
  have hl := LinearMap.congr_fun (LinearMap.congr_fun hproduct px) qy
  have hr := LinearMap.congr_fun (LinearMap.congr_fun hreverse px) qy
  change R.dynkinThreeCoordinate
      (UniversalEnvelopingAlgebra.ι ℤ (FreeLieDimension.freeLieMkLinear L p) *
        UniversalEnvelopingAlgebra.ι ℤ (FreeLieDimension.freeLieMkLinear L q)) =
      (2 : ℤ) • R.gammaThreeEquiv (bracket px qy) at hl
  change R.dynkinThreeCoordinate
      (UniversalEnvelopingAlgebra.ι ℤ (FreeLieDimension.freeLieMkLinear L q) *
        UniversalEnvelopingAlgebra.ι ℤ (FreeLieDimension.freeLieMkLinear L p)) =
      -R.gammaThreeEquiv (bracket px qy) at hr
  have hbracket : bracket px qy = R.coordinateBracketGammaThree i k := by
    apply Subtype.ext
    change ⁅ev (FreeLieDimension.freeLieMkLinear L p),
        ev (FreeLieDimension.freeLieMkLinear L q)⁆ =
      ⁅ev (x : F), ev (y : F)⁆
    rw [hpx, hqy]
  rw [hbracket] at hl hr
  change R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (x : F) *
            UniversalEnvelopingAlgebra.ι ℤ (y : F)) = _ ∧
        R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (y : F) *
            UniversalEnvelopingAlgebra.ι ℤ (x : F)) = _
  rw [← hpx, ← hqy]
  simpa only [coordinateGMod] using And.intro hl hr

/-- The triple degree-one product formula for the explicit Dynkin functional. -/
theorem dynkinThreeCoordinate_oneOneOne (R : StandingReductionData L) :
    letI : Finite L := R.finite_inst
    ∀ (i j l : CoordinateI L),
    R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
          UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j) *
          UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l)) =
      R.gammaThreeEquiv
        (R.dynkinTripleGammaThree
          (ev (R.coordinateX i)) (ev (R.coordinateX j))
            (ev (R.coordinateX l))) := by
  letI : Finite L := R.finite_inst
  classical
  intro i j l
  let xi : freeLieExact L 1 := collectedHomogeneousBasis L L ev 1 i
  let xj : freeLieExact L 1 := collectedHomogeneousBasis L L ev 1 j
  let xl : freeLieExact L 1 := collectedHomogeneousBasis L L ev 1 l
  let mk1 : magmaExact L 1 →ₗ[ℤ] F :=
    (FreeLieDimension.freeLieMkLinear L).domRestrict (magmaExact L 1)
  let u := (UniversalEnvelopingAlgebra.ι ℤ).toLinearMap.comp mk1
  let e := (canonicalFreeLieEvaluation L).toLinearMap.comp mk1
  let product : magmaExact L 1 →ₗ[ℤ]
      magmaExact L 1 →ₗ[ℤ] magmaExact L 1 →ₗ[ℤ] ZMod R.q := {
    toFun := fun p => ({
      toFun := fun q => ({
        toFun := fun r => R.dynkinThreeCoordinate ((u p * u q) * u r)
        map_add' := by
          intro a b
          change R.dynkinThreeCoordinate ((u p * u q) * u (a + b)) =
            R.dynkinThreeCoordinate ((u p * u q) * u a) +
              R.dynkinThreeCoordinate ((u p * u q) * u b)
          rw [map_add, mul_add, map_add]
        map_smul' := by
          intro n a
          change R.dynkinThreeCoordinate ((u p * u q) * u (n • a)) =
            n • R.dynkinThreeCoordinate ((u p * u q) * u a)
          rw [map_smul, mul_smul_comm, map_smul] } :
          magmaExact L 1 →ₗ[ℤ] ZMod R.q)
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro r
        change R.dynkinThreeCoordinate ((u p * u (a + b)) * u r) =
          R.dynkinThreeCoordinate ((u p * u a) * u r) +
            R.dynkinThreeCoordinate ((u p * u b) * u r)
        rw [map_add, mul_add, add_mul, map_add]
      map_smul' := by
        intro n a
        apply LinearMap.ext
        intro r
        change R.dynkinThreeCoordinate ((u p * u (n • a)) * u r) =
          n • R.dynkinThreeCoordinate ((u p * u a) * u r)
        rw [map_smul, mul_smul_comm, smul_mul_assoc, map_smul] } :
        magmaExact L 1 →ₗ[ℤ] magmaExact L 1 →ₗ[ℤ] ZMod R.q)
    map_add' p q := by
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro r
      change R.dynkinThreeCoordinate ((u (p + q) * u a) * u r) =
        R.dynkinThreeCoordinate ((u p * u a) * u r) +
          R.dynkinThreeCoordinate ((u q * u a) * u r)
      rw [map_add, add_mul, add_mul, map_add]
    map_smul' n p := by
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro r
      change R.dynkinThreeCoordinate ((u (n • p) * u a) * u r) =
        n • R.dynkinThreeCoordinate ((u p * u a) * u r)
      rw [map_smul, smul_mul_assoc, smul_mul_assoc, map_smul] }
  let gammaMap := R.gammaThreeEquiv.toAddMonoidHom.toIntLinearMap
  let triple : magmaExact L 1 →ₗ[ℤ]
      magmaExact L 1 →ₗ[ℤ] magmaExact L 1 →ₗ[ℤ] ZMod R.q := {
    toFun := fun p => ({
      toFun := fun q => ({
        toFun := fun r => gammaMap (R.dynkinTripleGammaThree (e p) (e q) (e r))
        map_add' := by
          intro a b
          have ht : R.dynkinTripleGammaThree (e p) (e q) (e (a + b)) =
              R.dynkinTripleGammaThree (e p) (e q) (e a) +
                R.dynkinTripleGammaThree (e p) (e q) (e b) := by
            apply Subtype.ext
            simp only [dynkinTripleGammaThree, map_add, lie_add]
            rfl
          rw [ht, map_add]
          rfl
        map_smul' := by
          intro n a
          have ht : R.dynkinTripleGammaThree (e p) (e q) (e (n • a)) =
              n • R.dynkinTripleGammaThree (e p) (e q) (e a) := by
            apply Subtype.ext
            simp only [dynkinTripleGammaThree, map_smul, lie_zsmul]
            rfl
          rw [ht, map_smul]
          rfl } :
          magmaExact L 1 →ₗ[ℤ] ZMod R.q)
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro r
        change gammaMap (R.dynkinTripleGammaThree (e p) (e (a + b)) (e r)) =
          gammaMap (R.dynkinTripleGammaThree (e p) (e a) (e r)) +
            gammaMap (R.dynkinTripleGammaThree (e p) (e b) (e r))
        have ht : R.dynkinTripleGammaThree (e p) (e (a + b)) (e r) =
            R.dynkinTripleGammaThree (e p) (e a) (e r) +
              R.dynkinTripleGammaThree (e p) (e b) (e r) := by
          apply Subtype.ext
          simp only [dynkinTripleGammaThree, map_add, add_lie, lie_add]
          rfl
        rw [ht, map_add]
      map_smul' := by
        intro n a
        apply LinearMap.ext
        intro r
        change gammaMap (R.dynkinTripleGammaThree (e p) (e (n • a)) (e r)) =
          n • gammaMap (R.dynkinTripleGammaThree (e p) (e a) (e r))
        have ht : R.dynkinTripleGammaThree (e p) (e (n • a)) (e r) =
            n • R.dynkinTripleGammaThree (e p) (e a) (e r) := by
          apply Subtype.ext
          simp only [dynkinTripleGammaThree, map_smul, smul_lie, lie_zsmul]
          rfl
        rw [ht, map_smul] } :
        magmaExact L 1 →ₗ[ℤ] magmaExact L 1 →ₗ[ℤ] ZMod R.q)
    map_add' p q := by
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro r
      change gammaMap (R.dynkinTripleGammaThree (e (p + q)) (e a) (e r)) =
        gammaMap (R.dynkinTripleGammaThree (e p) (e a) (e r)) +
          gammaMap (R.dynkinTripleGammaThree (e q) (e a) (e r))
      have ht : R.dynkinTripleGammaThree (e (p + q)) (e a) (e r) =
          R.dynkinTripleGammaThree (e p) (e a) (e r) +
            R.dynkinTripleGammaThree (e q) (e a) (e r) := by
        apply Subtype.ext
        simp only [dynkinTripleGammaThree, map_add, add_lie]
        rfl
      rw [ht, map_add]
    map_smul' n p := by
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro r
      change gammaMap (R.dynkinTripleGammaThree (e (n • p)) (e a) (e r)) =
        n • gammaMap (R.dynkinTripleGammaThree (e p) (e a) (e r))
      have ht : R.dynkinTripleGammaThree (e (n • p)) (e a) (e r) =
          n • R.dynkinTripleGammaThree (e p) (e a) (e r) := by
        apply Subtype.ext
        simp only [dynkinTripleGammaThree, map_smul, smul_lie]
        rfl
      rw [ht, map_smul] }
  have hproduct : product = triple := by
    apply LinearMap.ext_on (span_magmaExactSingle (L := L) 1)
    rintro p ⟨wp, rfl⟩
    apply LinearMap.ext_on (span_magmaExactSingle (L := L) 1)
    rintro q ⟨wq, rfl⟩
    apply LinearMap.ext_on (span_magmaExactSingle (L := L) 1)
    rintro r ⟨wr, rfl⟩
    rcases wp with ⟨wp, hwp⟩
    rcases wq with ⟨wq, hwq⟩
    rcases wr with ⟨wr, hwr⟩
    obtain ⟨x, hx⟩ := freeMagma_eq_of_of_length_one wp hwp
    obtain ⟨y, hy⟩ := freeMagma_eq_of_of_length_one wq hwq
    obtain ⟨z, hz⟩ := freeMagma_eq_of_of_length_one wr hwr
    subst wp
    subst wq
    subst wr
    change R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ
              (FreeLieDimension.freeLieMkLinear L
                (Finsupp.single (FreeMagma.of x) 1)) *
            UniversalEnvelopingAlgebra.ι ℤ
              (FreeLieDimension.freeLieMkLinear L
                (Finsupp.single (FreeMagma.of y) 1)) *
          UniversalEnvelopingAlgebra.ι ℤ
            (FreeLieDimension.freeLieMkLinear L
              (Finsupp.single (FreeMagma.of z) 1))) =
      R.gammaThreeEquiv
        (R.dynkinTripleGammaThree
          (ev (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single (FreeMagma.of x) 1)))
          (ev (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single (FreeMagma.of y) 1)))
          (ev (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single (FreeMagma.of z) 1))))
    simpa only [freeLieMkLinear_single_of, canonicalFreeLieEvaluation_of] using
      dynkinThreeCoordinate_generator_triple R x y z
  obtain ⟨p, hp, hpi⟩ := xi.property
  obtain ⟨q, hq, hpj⟩ := xj.property
  obtain ⟨r, hr, hpl⟩ := xl.property
  let pp : magmaExact L 1 := ⟨p, hp⟩
  let qq : magmaExact L 1 := ⟨q, hq⟩
  let rr : magmaExact L 1 := ⟨r, hr⟩
  have hvalue := LinearMap.congr_fun
    (LinearMap.congr_fun (LinearMap.congr_fun hproduct pp) qq) rr
  change R.dynkinThreeCoordinate
      (UniversalEnvelopingAlgebra.ι ℤ (FreeLieDimension.freeLieMkLinear L p) *
        UniversalEnvelopingAlgebra.ι ℤ (FreeLieDimension.freeLieMkLinear L q) *
        UniversalEnvelopingAlgebra.ι ℤ (FreeLieDimension.freeLieMkLinear L r)) =
    R.gammaThreeEquiv
      (R.dynkinTripleGammaThree
        (ev (FreeLieDimension.freeLieMkLinear L p))
        (ev (FreeLieDimension.freeLieMkLinear L q))
        (ev (FreeLieDimension.freeLieMkLinear L r))) at hvalue
  change R.dynkinThreeCoordinate
      (UniversalEnvelopingAlgebra.ι ℤ (xi : F) *
        UniversalEnvelopingAlgebra.ι ℤ (xj : F) *
        UniversalEnvelopingAlgebra.ι ℤ (xl : F)) =
    R.gammaThreeEquiv
      (R.dynkinTripleGammaThree (ev (xi : F)) (ev (xj : F)) (ev (xl : F)))
  rw [← hpi, ← hpj, ← hpl]
  exact hvalue

/-- The explicitly defined Dynkin functional satisfies all three required identities. -/
def dynkinProperties (R : StandingReductionData L) : DynkinProperties R where
  exactThree := R.dynkinThreeCoordinate_exactThree
  oneTwo := R.dynkinThreeCoordinate_oneTwo
  oneOneOne := R.dynkinThreeCoordinate_oneOneOne

/-- The terminal formal `z` coefficient is the actual cyclic coordinate of the represented
Lie element. -/
theorem terminalZeta_eq_targetCoordinate
    (R : StandingReductionData L) (hPhi : DynkinProperties R) :
    letI : Finite L := R.finite_inst
    ∀ {a : L} (w : AdaptedPresentationDimensionFiveWitness L L ev a),
      R.terminalZeta w 0 = R.gammaThreeEquiv
        ⟨a, by
          rw [← w.evaluates]
          apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) 2)
          exact LieIdeal.mem_map w.lieLift_mem_gammaThree⟩ := by
  letI : Finite L := R.finite_inst
  classical
  intro a w
  have hPhiExactNe (u : UEA ℤ F) (n : ℕ) (hn : n ≠ 3)
      (hu : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L u ∈
        FreeLieDimension.associativeExact L n) :
      R.dynkinThreeCoordinate u = 0 := by
    let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L u)
    change c.sum (fun word z ↦ z • R.dynkinWordCoordinate word) = 0
    calc
      _ = c.sum (fun _ _ ↦ (0 : ZMod R.q)) := by
        apply Finsupp.sum_congr
        intro word hword
        have hwlen : word.length = n := hu hword
        have hnot : ∀ x y z : L, FreeMonoid.toList word ≠ [x, y, z] := by
          intro x y z hxyz
          have : word.length = 3 := by simp [FreeMonoid.length, hxyz]
          omega
        rw [show R.dynkinWordCoordinate word = 0 by
          simp [dynkinWordCoordinate]]
        exact smul_zero _
      _ = 0 := by
        unfold Finsupp.sum
        simp
  have hPhiGamma (f : F) (hf : f ∈ lowerCentralSeries ℤ F 2) :
      R.dynkinThreeCoordinate (UniversalEnvelopingAlgebra.ι ℤ f) =
        (3 : ℤ) • R.gammaThreeEquiv
          ⟨ev f, by
            apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) 2)
            exact LieIdeal.mem_map hf⟩ := by
    let f3 : freeLieExact L 3 :=
      ⟨freeLieLengthComponent L 3 f, freeLieLengthComponent_mem_exact L 3 f⟩
    have hfHigh : f ∈ FreeLieDimension.lieHigh L 3 := by
      simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 2] using hf
    have hf3High : (f3 : F) ∈ FreeLieDimension.lieHigh L 3 :=
      freeLieExact_mem_lieHigh L f3
    have hcomponent : freeLieLengthComponent L 3 (f - (f3 : F)) = 0 := by
      rw [map_sub, freeLieLengthComponent_coe_exact]
      exact sub_self _
    have hremHigh : f - (f3 : F) ∈ FreeLieDimension.lieHigh L 4 := by
      simpa using mem_lieHigh_succ_of_component_eq_zero L
        ((FreeLieDimension.lieHigh L 3).sub_mem hfHigh hf3High) hcomponent
    have hremAssoc :
        FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
            (UniversalEnvelopingAlgebra.ι ℤ (f - (f3 : F))) ∈
          FreeLieDimension.associativeHigh L 4 := by
      have hiota :=
        FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra L
          (f - (f3 : F))
      exact hiota.symm ▸
        freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh L hremHigh
    have hPhiRem :=
      R.dynkinThreeCoordinate_eq_zero_of_mem_associativeHigh_four _ hremAssoc
    have hEvalRem :=
      evaluation_eq_zero_of_mem_lieHigh_four L L ev R.classThree _ hremHigh
    have hfDecomp : f = (f3 : F) + (f - (f3 : F)) := by abel
    have hEval : ev (f3 : F) = ev f := by
      rw [map_sub, sub_eq_zero] at hEvalRem
      exact hEvalRem.symm
    calc
      R.dynkinThreeCoordinate (UniversalEnvelopingAlgebra.ι ℤ f) =
          R.dynkinThreeCoordinate (UniversalEnvelopingAlgebra.ι ℤ
            ((f3 : F) + (f - (f3 : F)))) := congrArg
              (fun x : F ↦ R.dynkinThreeCoordinate
                (UniversalEnvelopingAlgebra.ι ℤ x)) hfDecomp
      _ = R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (f3 : F)) := by
        rw [map_add, map_add]
        exact add_eq_left.mpr hPhiRem
      _ = (3 : ℤ) • R.gammaThreeEquiv (exactThreeEvaluation L L ev f3) :=
        hPhi.exactThree f3
      _ = _ := by
        apply congrArg ((3 : ℤ) • ·)
        apply congrArg R.gammaThreeEquiv
        exact Subtype.ext hEval
  have hLieZ : R.terminalLieZ w 0 =
      -(∑ i : CoordinateI L,
          AdaptedTerminalCoordinates.r L L ev w.terminalPackets i * R.coordinateC i) -
      (∑ k : CoordinateK L,
          AdaptedTerminalCoordinates.s L L ev w.terminalPackets k * R.coordinateM k) +
      (∑ i : CoordinateI L,
          AdaptedTerminalCoordinates.rxx L L ev w.terminalPackets i *
            (∑ k : CoordinateK L, R.coordinateB i k * R.coordinateG i k)) +
      (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets ij.1 ij.2 *
            (∑ k : CoordinateK L,
              R.coordinateB ij.1 k * R.coordinateG ij.2 k)) := by
    simp [terminalLieZ, terminalPreTheta,
      Coordinate.Data.CollectedExpression.PreTheta.polynomial,
      Coordinate.Data.rRelation, Coordinate.Data.sRelation,
      Coordinate.Data.rawScale,
      Coordinate.Data.CollectedExpression.rawPBWProjection_coreWordExpression_z,
      Coordinate.Data.rawPBWProjection_rawTerm,
      Coordinate.Data.coreWordContribution,
      StandingReductionData.coordinateData,
      StandingReductionData.coordinateRelationTails,
      AdaptedTerminalCoordinates.visiblePreTheta,
      Coordinate.Data.CollectedExpression.TableRemainder.expression,
      sub_mul, mul_sub, Finset.sum_mul,
      Coordinate.Data.rawTerm_mul_rawWord,
      Coordinate.Data.rawWord_mul_rawTerm,
      Coordinate.Data.rawWordCoordinate, Finset.mul_sum]
    ring
  have hledger : R.dynkinThreeCoordinate
      ((adaptedPlacedPacketCollector L L ev).evaluate w.terminalPackets) =
        (3 : ℤ) • R.terminalZeta w 0 := by
    have hX (i : CoordinateI L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i)) = 0 := by
      apply hPhiExactNe _ 1 (by omega)
      rw [FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra]
      exact freeLieToFreeAlgebra_mem_exact L
        (collectedHomogeneousBasis L L ev 1 i)
    have hY (k : CoordinateK L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateY k)) = 0 := by
      apply hPhiExactNe _ 2 (by omega)
      rw [FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra]
      exact freeLieToFreeAlgebra_mem_exact L
        (collectedHomogeneousBasis L L ev 2 k)
    have hB (i : CoordinateI L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateBValue i)) = 0 := by
      rw [coordinateBValue, map_sum, map_sum]
      simp_rw [map_zsmul]
      change (∑ k, R.coordinateB i k • R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateY k))) = 0
      simp_rw [hY, smul_zero]
      exact Finset.sum_const_zero
    have hFirstScalar (i : CoordinateI L) :
        R.dynkinThreeCoordinate (UniversalEnvelopingAlgebra.ι ℤ
            (collectedRelationRow L L ev 1 i : F)) =
          (-3 : ℤ) • (R.coordinateC i : ZMod R.q) := by
      have htail := hPhiGamma (R.firstRelationTail i) (by
        simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 2] using
          R.firstRelationTail_mem_lieHigh_three i)
      have htail' : R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.firstRelationTail i)) =
            (3 : ℤ) • R.gammaThreeEquiv
              (R.firstRelationTailGammaThree i) := by
        simpa [firstRelationTailGammaThree] using htail
      have hdecomp : (collectedRelationRow L L ev 1 i : F) =
          (R.coordinateD i : ℤ) • R.coordinateX i - R.coordinateBValue i +
            R.firstRelationTail i := by simp [firstRelationTail]
      rw [hdecomp, map_add, map_sub, map_zsmul, map_add, map_sub, map_zsmul,
        hX, hB, htail', R.coordinateC_cast]
      simp only [smul_zero, sub_zero, zero_add]
      change (3 : ℤ) • R.gammaThreeEquiv (R.firstRelationTailGammaThree i) =
        (-3 : ℤ) • (-R.gammaThreeEquiv (R.firstRelationTailGammaThree i))
      rw [neg_smul, smul_neg, neg_neg]
    have hSecondScalar (k : CoordinateK L) :
        R.dynkinThreeCoordinate (UniversalEnvelopingAlgebra.ι ℤ
            (collectedRelationRow L L ev 2 k : F)) =
          (-3 : ℤ) • (R.coordinateM k : ZMod R.q) := by
      have htail := hPhiGamma (R.secondRelationTail k) (by
        simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 2] using
          R.secondRelationTail_mem_lieHigh_three k)
      have htail' : R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.secondRelationTail k)) =
            (3 : ℤ) • R.gammaThreeEquiv
              (R.secondRelationTailGammaThree k) := by
        simpa [secondRelationTailGammaThree] using htail
      have hdecomp : (collectedRelationRow L L ev 2 k : F) =
          (R.coordinateE k : ℤ) • R.coordinateY k +
            R.secondRelationTail k := by simp [secondRelationTail]
      rw [hdecomp, map_add, map_zsmul, map_add, map_zsmul,
        hY, htail', R.coordinateM_cast]
      simp only [smul_zero, zero_add]
      change (3 : ℤ) • R.gammaThreeEquiv (R.secondRelationTailGammaThree k) =
        (-3 : ℤ) • (-R.gammaThreeEquiv (R.secondRelationTailGammaThree k))
      rw [neg_smul, smul_neg, neg_neg]
    have hIotaHigh (f : F) (n : ℕ)
        (hf : f ∈ FreeLieDimension.lieHigh L n) :
        FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
            (UniversalEnvelopingAlgebra.ι ℤ f) ∈
          FreeLieDimension.associativeHigh L n := by
      have hiota :=
        FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra L f
      exact hiota.symm ▸
        freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh L hf
    have hKillMul (u v : UEA ℤ F) (m n : ℕ) (hmn : 4 ≤ m + n)
        (hu : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L u ∈
          FreeLieDimension.associativeHigh L m)
        (hv : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L v ∈
          FreeLieDimension.associativeHigh L n) :
        R.dynkinThreeCoordinate (u * v) = 0 := by
      apply R.dynkinThreeCoordinate_eq_zero_of_mem_associativeHigh_four
      have hmul := FreeLieDimension.associativeHigh_mul L hu hv
      have heq := map_mul
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L) u v
      exact heq.symm ▸ FreeLieDimension.associativeHigh_mono L hmn hmul
    have hXX (i j : CoordinateI L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
          UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j)) = 0 := by
      apply hPhiExactNe _ 2 (by omega)
      have hmul := FreeLieDimension.associativeExact_mul L
        (freeLieToFreeAlgebra_mem_exact L
          (collectedHomogeneousBasis L L ev 1 i))
        (freeLieToFreeAlgebra_mem_exact L
          (collectedHomogeneousBasis L L ev 1 j))
      have hi := FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
        L (R.coordinateX i)
      have hj := FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
        L (R.coordinateX j)
      have hmul' := congrArg₂ (· * ·) hi hj
      have heq := map_mul
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j))
      rw [show FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
            (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
              UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j)) =
          PBW.freeLieToFreeAlgebra ℤ L (R.coordinateX i) *
            PBW.freeLieToFreeAlgebra ℤ L (R.coordinateX j) by
        exact heq.trans hmul']
      exact hmul
    let gamma : CoordinateI L → CoordinateI L → ZMod R.q := fun i j ↦
      ∑ k : CoordinateK L,
        (R.coordinateB i k : ZMod R.q) * R.coordinateGMod j k
    have hBRightX (i j : CoordinateI L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateBValue i) *
          UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j)) = -gamma i j := by
      rw [coordinateBValue, map_sum, Finset.sum_mul, map_sum]
      simp_rw [map_zsmul, smul_mul_assoc, map_zsmul,
        (hPhi.oneTwo j _).2]
      simp only [gamma, zsmul_eq_mul, mul_neg, Finset.sum_neg_distrib]
    have hXLeftB (j i : CoordinateI L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j) *
          UniversalEnvelopingAlgebra.ι ℤ (R.coordinateBValue i)) =
        (2 : ℤ) • gamma i j := by
      rw [coordinateBValue, map_sum, Finset.mul_sum, map_sum]
      simp_rw [map_zsmul, mul_smul_comm, map_zsmul,
        (hPhi.oneTwo j _).1]
      simp only [gamma, zsmul_eq_mul, smul_eq_mul, smul_smul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hTailRightX (i j : CoordinateI L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.firstRelationTail i) *
          UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j)) = 0 := by
      apply hKillMul _ _ 3 1 (by omega)
      · exact hIotaHigh _ 3 (R.firstRelationTail_mem_lieHigh_three i)
      · exact hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 j))
    have hXLeftTail (j i : CoordinateI L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j) *
          UniversalEnvelopingAlgebra.ι ℤ (R.firstRelationTail i)) = 0 := by
      apply hKillMul _ _ 1 3 (by omega)
      · exact hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 j))
      · exact hIotaHigh _ 3 (R.firstRelationTail_mem_lieHigh_three i)
    have hFirstRightX (i j : CoordinateI L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ
            (collectedRelationRow L L ev 1 i : F) *
          UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j)) = gamma i j := by
      have hdecomp : (collectedRelationRow L L ev 1 i : F) =
          (R.coordinateD i : ℤ) • R.coordinateX i - R.coordinateBValue i +
            R.firstRelationTail i := by simp [firstRelationTail]
      rw [hdecomp, map_add, map_sub, map_zsmul, add_mul, sub_mul,
        smul_mul_assoc, map_add, map_sub, map_zsmul, hXX, hBRightX,
        hTailRightX]
      module
    have hLeftXFirst (j i : CoordinateI L) : R.dynkinThreeCoordinate
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j) *
          UniversalEnvelopingAlgebra.ι ℤ
            (collectedRelationRow L L ev 1 i : F)) =
          (-2 : ℤ) • gamma i j := by
      have hdecomp : (collectedRelationRow L L ev 1 i : F) =
          (R.coordinateD i : ℤ) • R.coordinateX i - R.coordinateBValue i +
            R.firstRelationTail i := by simp [firstRelationTail]
      rw [hdecomp, map_add, map_sub, map_zsmul, mul_add, mul_sub,
        mul_smul_comm, map_add, map_sub, map_zsmul, hXX, hXLeftB,
        hXLeftTail]
      module
    have hFirstRightY (i : CoordinateI L) (k : CoordinateK L) :
        R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ
              (collectedRelationRow L L ev 1 i : F) *
            UniversalEnvelopingAlgebra.ι ℤ (R.coordinateY k)) =
          (2 * R.coordinateD i : ℤ) • R.coordinateGMod i k := by
      have hBY : R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateBValue i) *
            UniversalEnvelopingAlgebra.ι ℤ (R.coordinateY k)) = 0 := by
        apply hKillMul _ _ 2 2 (by omega)
        · exact hIotaHigh _ 2 (R.coordinateBValue_mem_lieHigh_two i)
        · exact hIotaHigh _ 2 (freeLieExact_mem_lieHigh L
            (collectedHomogeneousBasis L L ev 2 k))
      have hTY : R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.firstRelationTail i) *
            UniversalEnvelopingAlgebra.ι ℤ (R.coordinateY k)) = 0 := by
        apply hKillMul _ _ 3 2 (by omega)
        · exact hIotaHigh _ 3 (R.firstRelationTail_mem_lieHigh_three i)
        · exact hIotaHigh _ 2 (freeLieExact_mem_lieHigh L
            (collectedHomogeneousBasis L L ev 2 k))
      have hdecomp : (collectedRelationRow L L ev 1 i : F) =
          (R.coordinateD i : ℤ) • R.coordinateX i - R.coordinateBValue i +
            R.firstRelationTail i := by simp [firstRelationTail]
      rw [hdecomp, map_add, map_sub, map_zsmul, add_mul, sub_mul,
        smul_mul_assoc, map_add, map_sub, map_zsmul, (hPhi.oneTwo i k).1,
        hBY, hTY]
      module
    have hLeftXSecond (i : CoordinateI L) (k : CoordinateK L) :
        R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
            UniversalEnvelopingAlgebra.ι ℤ
              (collectedRelationRow L L ev 2 k : F)) =
          (2 * R.coordinateE k : ℤ) • R.coordinateGMod i k := by
      have hXT : R.dynkinThreeCoordinate
          (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX i) *
            UniversalEnvelopingAlgebra.ι ℤ (R.secondRelationTail k)) = 0 := by
        apply hKillMul _ _ 1 3 (by omega)
        · exact hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
            (collectedHomogeneousBasis L L ev 1 i))
        · exact hIotaHigh _ 3 (R.secondRelationTail_mem_lieHigh_three k)
      have hdecomp : (collectedRelationRow L L ev 2 k : F) =
          (R.coordinateE k : ℤ) • R.coordinateY k +
            R.secondRelationTail k := by simp [secondRelationTail]
      rw [hdecomp, map_add, map_zsmul, mul_add, mul_smul_comm,
        map_add, map_zsmul, (hPhi.oneTwo i k).1, hXT]
      module
    have hDX (i : CoordinateI L) :
        (R.coordinateD i : ℤ) • ev (R.coordinateX i) =
          ev (R.coordinateBValue i) - ev (R.firstRelationTail i) := by
      have hr := collectedRelationRow_mem_ker L L ev 1 i
      have hdecomp : (collectedRelationRow L L ev 1 i : F) =
          (R.coordinateD i : ℤ) • R.coordinateX i - R.coordinateBValue i +
            R.firstRelationTail i := by simp [firstRelationTail]
      rw [hdecomp, map_add, map_sub, map_zsmul] at hr
      rw [← sub_eq_zero]
      convert hr using 1 <;> abel
    have hBGamma (i : CoordinateI L) :
        ev (R.coordinateBValue i) ∈ lowerCentralSeries ℤ L 1 := by
      simpa using R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh
        (R.coordinateBValue_mem_lieHigh_two i)
    have hTailGamma (i : CoordinateI L) :
        ev (R.firstRelationTail i) ∈ lowerCentralSeries ℤ L 2 := by
      simpa using R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh
        (R.firstRelationTail_mem_lieHigh_three i)
    have hBracketMem {x y : L} {m n : ℕ}
        (hx : x ∈ lowerCentralSeries ℤ L m)
        (hy : y ∈ lowerCentralSeries ℤ L n) :
        ⁅x, y⁆ ∈ lowerCentralSeries ℤ L (m + n + 1) := by
      apply (show ⁅lowerCentralSeries ℤ L m, lowerCentralSeries ℤ L n⁆ ≤
          lowerCentralSeries ℤ L (m + n + 1) from ?_)
      · exact LieSubmodule.lie_mem_lie hx hy
      · calc
          ⁅lowerCentralSeries ℤ L m, lowerCentralSeries ℤ L n⁆ ≤
              ⁅dimensionSubring ℤ L (m + 1), dimensionSubring ℤ L (n + 1)⁆ :=
            LieSubmodule.mono_lie
              (lowerCentralSeries_le_dimensionSubring ℤ L m)
              (lowerCentralSeries_le_dimensionSubring ℤ L n)
          _ ≤ lowerCentralSeries ℤ L (m + n + 1) :=
            bracket_dimensionSubring_le_lowerCentralSeries ℤ L m n
    have hTripleFirst (i j l : CoordinateI L) :
        (R.coordinateD i : ℤ) • R.gammaThreeEquiv
            (R.dynkinTripleGammaThree
              (ev (R.coordinateX i)) (ev (R.coordinateX j))
                (ev (R.coordinateX l))) = 0 := by
      have hzero : (R.coordinateD i : ℤ) •
          R.dynkinTripleGammaThree
            (ev (R.coordinateX i)) (ev (R.coordinateX j))
              (ev (R.coordinateX l)) = 0 := by
        apply Subtype.ext
        change (R.coordinateD i : ℤ) •
            ⁅ev (R.coordinateX i),
              ⁅ev (R.coordinateX j), ev (R.coordinateX l)⁆⁆ = 0
        rw [← smul_lie, hDX, sub_lie]
        have hinner : ⁅ev (R.coordinateX j), ev (R.coordinateX l)⁆ ∈
            lowerCentralSeries ℤ L 1 := by
          simpa using hBracketMem (m := 0) (n := 0)
            (LieSubmodule.mem_top (ev (R.coordinateX j)))
            (LieSubmodule.mem_top (ev (R.coordinateX l)))
        rw [R.bracket_eq_zero_of_mem_gamma_weights (hBGamma i) hinner (by omega),
          R.bracket_eq_zero_of_mem_gamma_weights (hTailGamma i) hinner (by omega),
          sub_zero]
      calc
        _ = R.gammaThreeEquiv ((R.coordinateD i : ℤ) •
              R.dynkinTripleGammaThree
                (ev (R.coordinateX i)) (ev (R.coordinateX j))
                  (ev (R.coordinateX l))) :=
          (R.gammaThreeEquiv.toAddMonoidHom.map_zsmul _ _).symm
        _ = 0 := by
          rw [hzero]
          exact R.gammaThreeEquiv.toAddMonoidHom.map_zero
    have hTripleMiddle (j i l : CoordinateI L) :
        (R.coordinateD i : ℤ) • R.gammaThreeEquiv
            (R.dynkinTripleGammaThree
              (ev (R.coordinateX j)) (ev (R.coordinateX i))
                (ev (R.coordinateX l))) = 0 := by
      have hzero : (R.coordinateD i : ℤ) •
          R.dynkinTripleGammaThree
            (ev (R.coordinateX j)) (ev (R.coordinateX i))
              (ev (R.coordinateX l)) = 0 := by
        apply Subtype.ext
        change (R.coordinateD i : ℤ) •
            ⁅ev (R.coordinateX j),
              ⁅ev (R.coordinateX i), ev (R.coordinateX l)⁆⁆ = 0
        rw [← lie_smul, ← smul_lie, hDX, sub_lie, lie_sub]
        have hBX : ⁅ev (R.coordinateBValue i), ev (R.coordinateX l)⁆ ∈
            lowerCentralSeries ℤ L 2 := by
          simpa using hBracketMem (m := 1) (n := 0) (hBGamma i)
            (LieSubmodule.mem_top (ev (R.coordinateX l)))
        have hTX : ⁅ev (R.firstRelationTail i), ev (R.coordinateX l)⁆ ∈
            lowerCentralSeries ℤ L 3 := by
          simpa using hBracketMem (m := 2) (n := 0) (hTailGamma i)
            (LieSubmodule.mem_top (ev (R.coordinateX l)))
        rw [R.bracket_eq_zero_of_mem_gamma_weights (m := 0) (n := 2)
            (LieSubmodule.mem_top (ev (R.coordinateX j))) hBX (by omega),
          R.bracket_eq_zero_of_mem_gamma_weights (m := 0) (n := 3)
            (LieSubmodule.mem_top (ev (R.coordinateX j))) hTX (by omega),
          sub_zero]
      calc
        _ = R.gammaThreeEquiv ((R.coordinateD i : ℤ) •
              R.dynkinTripleGammaThree
                (ev (R.coordinateX j)) (ev (R.coordinateX i))
                  (ev (R.coordinateX l))) :=
          (R.gammaThreeEquiv.toAddMonoidHom.map_zsmul _ _).symm
        _ = 0 := by
          rw [hzero]
          exact R.gammaThreeEquiv.toAddMonoidHom.map_zero
    have hTripleLast (j l i : CoordinateI L) :
        (R.coordinateD i : ℤ) • R.gammaThreeEquiv
            (R.dynkinTripleGammaThree
              (ev (R.coordinateX j)) (ev (R.coordinateX l))
                (ev (R.coordinateX i))) = 0 := by
      have hzero : (R.coordinateD i : ℤ) •
          R.dynkinTripleGammaThree
            (ev (R.coordinateX j)) (ev (R.coordinateX l))
              (ev (R.coordinateX i)) = 0 := by
        apply Subtype.ext
        change (R.coordinateD i : ℤ) •
            ⁅ev (R.coordinateX j),
              ⁅ev (R.coordinateX l), ev (R.coordinateX i)⁆⁆ = 0
        rw [← lie_smul, ← lie_smul, hDX, lie_sub, lie_sub]
        have hXB : ⁅ev (R.coordinateX l), ev (R.coordinateBValue i)⁆ ∈
            lowerCentralSeries ℤ L 2 := by
          simpa using hBracketMem (m := 0) (n := 1)
            (LieSubmodule.mem_top (ev (R.coordinateX l))) (hBGamma i)
        have hXT : ⁅ev (R.coordinateX l), ev (R.firstRelationTail i)⁆ ∈
            lowerCentralSeries ℤ L 3 := by
          simpa using hBracketMem (m := 0) (n := 2)
            (LieSubmodule.mem_top (ev (R.coordinateX l))) (hTailGamma i)
        rw [R.bracket_eq_zero_of_mem_gamma_weights (m := 0) (n := 2)
            (LieSubmodule.mem_top (ev (R.coordinateX j))) hXB (by omega),
          R.bracket_eq_zero_of_mem_gamma_weights (m := 0) (n := 3)
            (LieSubmodule.mem_top (ev (R.coordinateX j))) hXT (by omega),
          sub_zero]
      calc
        _ = R.gammaThreeEquiv ((R.coordinateD i : ℤ) •
              R.dynkinTripleGammaThree
                (ev (R.coordinateX j)) (ev (R.coordinateX l))
                  (ev (R.coordinateX i))) :=
          (R.gammaThreeEquiv.toAddMonoidHom.map_zsmul _ _).symm
        _ = 0 := by
          rw [hzero]
          exact R.gammaThreeEquiv.toAddMonoidHom.map_zero
    have hFactorX (i : CoordinateI L) :
        adaptedLowBasisValue L L ev (adaptedCoordinateXFactor L i) =
          R.coordinateX i := by
      simpa [adaptedCoordinateXFactor, coordinateX] using
        adaptedLowBasisValue_indexOf L L ev (n := 1) (by omega) (by omega) i
    have hFactorY (k : CoordinateK L) :
        adaptedLowBasisValue L L ev (adaptedCoordinateYFactor L k) =
          R.coordinateY k := by
      simpa [adaptedCoordinateYFactor, coordinateY] using
        adaptedLowBasisValue_indexOf L L ev (n := 2) (by omega) (by omega) k
    have hRowX (i : CoordinateI L) :
        adaptedLowRelationRow L L ev (adaptedCoordinateXFactor L i) =
          (collectedRelationRow L L ev 1 i : F) := rfl
    have hRowY (k : CoordinateK L) :
        adaptedLowRelationRow L L ev (adaptedCoordinateYFactor L k) =
          (collectedRelationRow L L ev 2 k : F) := rfl
    have hKillThree (u v z : UEA ℤ F) (m n r : ℕ)
        (hmnr : 4 ≤ m + n + r)
        (hu : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L u ∈
          FreeLieDimension.associativeHigh L m)
        (hv : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L v ∈
          FreeLieDimension.associativeHigh L n)
        (hz : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L z ∈
          FreeLieDimension.associativeHigh L r) :
        R.dynkinThreeCoordinate (u * v * z) = 0 := by
      apply R.dynkinThreeCoordinate_eq_zero_of_mem_associativeHigh_four
      have huv := FreeLieDimension.associativeHigh_mul L hu hv
      have hall := FreeLieDimension.associativeHigh_mul L huv hz
      have heq : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
          (u * v * z) =
          FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L u *
            FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L v *
              FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L z := by
        exact (map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
          (u * v) z).trans (congrArg
            (· * FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L z)
            (map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L) u v))
      rw [heq]
      exact FreeLieDimension.associativeHigh_mono L (by omega) hall
    have hTwoXLeft (j l i : CoordinateI L) :
        R.dynkinThreeCoordinate
            (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j) *
              UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l) *
              UniversalEnvelopingAlgebra.ι ℤ
                (collectedRelationRow L L ev 1 i : F)) = 0 := by
      have hdecomp : (collectedRelationRow L L ev 1 i : F) =
          (R.coordinateD i : ℤ) • R.coordinateX i - R.coordinateBValue i +
            R.firstRelationTail i := by simp [firstRelationTail]
      rw [hdecomp, map_add, map_sub, map_zsmul, mul_add, mul_sub,
        mul_smul_comm, map_add, map_sub, map_zsmul, hPhi.oneOneOne]
      have hBzero := hKillThree
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateBValue i)) 1 1 2
        (by omega)
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 j)))
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 l)))
        (hIotaHigh _ 2 (R.coordinateBValue_mem_lieHigh_two i))
      have hTzero := hKillThree
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l))
        (UniversalEnvelopingAlgebra.ι ℤ (R.firstRelationTail i)) 1 1 3
        (by omega)
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 j)))
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 l)))
        (hIotaHigh _ 3 (R.firstRelationTail_mem_lieHigh_three i))
      rw [hBzero, hTzero]
      simpa only [sub_zero, add_zero] using hTripleLast j l i
    have hTwoXSplit (j i l : CoordinateI L) :
        R.dynkinThreeCoordinate
            (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j) *
              UniversalEnvelopingAlgebra.ι ℤ
                (collectedRelationRow L L ev 1 i : F) *
              UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l)) = 0 := by
      have hdecomp : (collectedRelationRow L L ev 1 i : F) =
          (R.coordinateD i : ℤ) • R.coordinateX i - R.coordinateBValue i +
            R.firstRelationTail i := by simp [firstRelationTail]
      rw [hdecomp, map_add, map_sub, map_zsmul, mul_add, mul_sub,
        mul_smul_comm, add_mul, sub_mul, smul_mul_assoc,
        map_add, map_sub, map_zsmul, hPhi.oneOneOne]
      have hBzero := hKillThree
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateBValue i))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l)) 1 2 1
        (by omega)
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 j)))
        (hIotaHigh _ 2 (R.coordinateBValue_mem_lieHigh_two i))
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 l)))
      have hTzero := hKillThree
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j))
        (UniversalEnvelopingAlgebra.ι ℤ (R.firstRelationTail i))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l)) 1 3 1
        (by omega)
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 j)))
        (hIotaHigh _ 3 (R.firstRelationTail_mem_lieHigh_three i))
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 l)))
      rw [hBzero, hTzero]
      simpa only [sub_zero, add_zero] using hTripleMiddle j i l
    have hTwoXRight (i j l : CoordinateI L) :
        R.dynkinThreeCoordinate
            (UniversalEnvelopingAlgebra.ι ℤ
                (collectedRelationRow L L ev 1 i : F) *
              UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j) *
              UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l)) = 0 := by
      have hdecomp : (collectedRelationRow L L ev 1 i : F) =
          (R.coordinateD i : ℤ) • R.coordinateX i - R.coordinateBValue i +
            R.firstRelationTail i := by simp [firstRelationTail]
      rw [hdecomp, map_add, map_sub, map_zsmul, add_mul, sub_mul,
        smul_mul_assoc, add_mul, sub_mul, smul_mul_assoc,
        map_add, map_sub, map_zsmul, hPhi.oneOneOne]
      have hBzero := hKillThree
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateBValue i))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l)) 2 1 1
        (by omega) (hIotaHigh _ 2 (R.coordinateBValue_mem_lieHigh_two i))
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 j)))
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 l)))
      have hTzero := hKillThree
        (UniversalEnvelopingAlgebra.ι ℤ (R.firstRelationTail i))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX j))
        (UniversalEnvelopingAlgebra.ι ℤ (R.coordinateX l)) 3 1 1
        (by omega) (hIotaHigh _ 3 (R.firstRelationTail_mem_lieHigh_three i))
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 j)))
        (hIotaHigh _ 1 (freeLieExact_mem_lieHigh L
          (collectedHomogeneousBasis L L ev 1 l)))
      rw [hBzero, hTzero]
      simpa only [sub_zero, add_zero] using hTripleFirst i j l
    have hsumSingle {A : Type} [Fintype A] [DecidableEq A]
        (x : A) (f : A → ZMod R.q) :
        (∑ y : A, if x = y then f y else 0) = f x := by
      exact Fintype.sum_ite_eq x f
    have hsumPair {A B : Type} [Fintype A] [Fintype B]
        [DecidableEq A] [DecidableEq B] (x : A) (y : B)
        (f : A → B → ZMod R.q) :
        (∑ a : A, ∑ b : B, if x = a ∧ y = b then f a b else 0) = f x y := by
      calc
        _ = ∑ a : A, if x = a then
              (∑ b : B, if y = b then f a b else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hxa : x = a <;> simp [hxa]
        _ = _ := by rw [hsumSingle x]; exact hsumSingle y (f x)
    have hPacket (p : AdaptedSmithPlacedPacket L L ev)
        (hp : p ∈ w.terminalPackets.support) :
        R.dynkinThreeCoordinate (p.value L L ev) =
          ( (∑ i : CoordinateI L,
              if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i) [] [] p
              then (-3 : ℤ) • (R.coordinateC i : ZMod R.q) else 0) +
            (∑ k : CoordinateK L,
              if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k) [] [] p
              then (-3 : ℤ) • (R.coordinateM k : ZMod R.q) else 0)) +
          ( (∑ i : CoordinateI L, ∑ j : CoordinateI L,
              if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
                  [] [adaptedCoordinateXFactor L j] p
              then gamma i j else 0) +
            (∑ i : CoordinateI L, ∑ j : CoordinateI L,
              if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
                  [adaptedCoordinateXFactor L j] [] p
              then (-2 : ℤ) • gamma i j else 0)) +
          ( (∑ i : CoordinateI L, ∑ k : CoordinateK L,
              if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
                  [] [adaptedCoordinateYFactor L k] p
              then (2 * R.coordinateD i : ℤ) • R.coordinateGMod i k else 0) +
            (∑ i : CoordinateI L, ∑ k : CoordinateK L,
              if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k)
                  [adaptedCoordinateXFactor L i] [] p
              then (2 * R.coordinateE k : ℤ) • R.coordinateGMod i k else 0)) := by
      by_cases hhigh : 3 < p.totalWeight L
      · have hzero : R.dynkinThreeCoordinate (p.value L L ev) = 0 := by
          apply R.dynkinThreeCoordinate_eq_zero_of_mem_associativeHigh_four
          exact FreeLieDimension.associativeHigh_mono L (by omega)
            (adaptedPlacedPacket_value_mem_associativeHigh L L ev p)
        rw [hzero]
        have hscalarX (i : CoordinateI L) : ¬IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L i) [] [] p := by
          rintro ⟨hl, hr, hh⟩
          rw [AdaptedSmithPlacedPacket.totalWeight, hr,
            AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
          simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
        have hscalarY (k : CoordinateK L) : ¬IsAdaptedRowPacket L L ev
            (adaptedCoordinateYFactor L k) [] [] p := by
          rintro ⟨hl, hr, hh⟩
          rw [AdaptedSmithPlacedPacket.totalWeight, hr,
            AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
          simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
        have hRX (i j : CoordinateI L) : ¬IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L i) [] [adaptedCoordinateXFactor L j] p := by
          rintro ⟨hl, hr, hh⟩
          rw [AdaptedSmithPlacedPacket.totalWeight, hr,
            AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
          simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
        have hLX (i j : CoordinateI L) : ¬IsAdaptedRowPacket L L ev
            (adaptedCoordinateXFactor L i) [adaptedCoordinateXFactor L j] [] p := by
          rintro ⟨hl, hr, hh⟩
          rw [AdaptedSmithPlacedPacket.totalWeight, hr,
            AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
          simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
        have hRY (i : CoordinateI L) (k : CoordinateK L) :
            ¬IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
              [] [adaptedCoordinateYFactor L k] p := by
          rintro ⟨hl, hr, hh⟩
          rw [AdaptedSmithPlacedPacket.totalWeight, hr,
            AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
          simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
        have hLY (i : CoordinateI L) (k : CoordinateK L) :
            ¬IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k)
              [adaptedCoordinateXFactor L i] [] p := by
          rintro ⟨hl, hr, hh⟩
          rw [AdaptedSmithPlacedPacket.totalWeight, hr,
            AdaptedSmithPlacedPacket.externalWeight, hl, hh] at hhigh
          simp [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight] at hhigh
        simp [hscalarX, hscalarY, hRX, hLX, hRY, hLY]
        abel
      · have hle : p.totalWeight L ≤ 3 := Nat.le_of_not_gt hhigh
        have hterminal := w.terminalPackets_terminal p hp
        cases hrel : p.relation with
        | high r hr =>
            exfalso
            rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
            simp [AdaptedCollectedRelation.weight] at hle
            omega
        | row row =>
          have hrowle : adaptedLowBasisWeight L row ≤ 3 := by
            rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
            simp only [AdaptedCollectedRelation.weight,
              adaptedLowRelationRowWeight] at hle
            omega
          have hrowpos := adaptedLowBasisWeight_pos L row
          rcases (show adaptedLowBasisWeight L row = 1 ∨
              adaptedLowBasisWeight L row = 2 ∨
              adaptedLowBasisWeight L row = 3 by omega) with
            hrowone | hrowtwo | hrowthree
          · obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L row hrowone
            have hextle : p.externalWeight L ≤ 2 := by
              rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
              simp only [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight,
                adaptedCoordinateXFactor_weight] at hle
              omega
            rcases (show p.externalWeight L = 0 ∨ p.externalWeight L = 1 ∨
                p.externalWeight L = 2 by omega) with hextzero | hextone | hexttwo
            · obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hextzero
              rcases p with ⟨left, relation, right⟩
              simp only at hl hr hrel
              subst left; subst relation; subst right
              simp only [AdaptedSmithPlacedPacket.value,
                AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
                one_mul, mul_one, hRowX]
              rw [hFirstScalar i]
              simp [IsAdaptedRowPacket, adaptedCoordinateXFactor_inj_iff,
                adaptedCoordinateYFactor_inj_iff, eq_comm, hsumSingle, hsumPair]
              convert
                (hsumSingle i (fun x => (-3 : ℤ) • (R.coordinateC x : ZMod R.q))).symm
                using 1 <;> abel
            · rcases p.externalWeight_eq_one_iff.mp hextone with hleft | hright
              · obtain ⟨x, hl, hr, hx⟩ := hleft
                obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
                rcases p with ⟨left, relation, right⟩
                simp only at hl hr hrel
                subst left; subst relation; subst right
                simp only [AdaptedSmithPlacedPacket.value,
                  AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                  AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
                  envelopingWord_cons, envelopingWord_nil, mul_one, hRowX, hFactorX]
                rw [hLeftXFirst j i]
                simp [IsAdaptedRowPacket, adaptedCoordinateXFactor_inj_iff,
                  adaptedCoordinateYFactor_inj_iff, eq_comm, hsumSingle, hsumPair]
                have hpairs := hsumPair i j (fun x y => (-2 : ℤ) • gamma x y)
                convert hpairs using 1 <;>
                  simp only [smul_zero, zero_add, and_comm] <;> abel
              · obtain ⟨x, hl, hr, hx⟩ := hright
                obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
                rcases p with ⟨left, relation, right⟩
                simp only at hl hr hrel
                subst left; subst relation; subst right
                simp only [AdaptedSmithPlacedPacket.value,
                  AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                  AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
                  envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hRowX, hFactorX]
                rw [hFirstRightX i j]
                simp [IsAdaptedRowPacket, adaptedCoordinateXFactor_inj_iff,
                  adaptedCoordinateYFactor_inj_iff, eq_comm, hsumSingle, hsumPair]
                convert hsumPair i j gamma using 1 <;> abel
            · rcases p.externalWeight_eq_two_iff.mp hexttwo with
                hYleft | hYright | hXXleft | hXXsplit | hXXright
              · obtain ⟨x, hl, hr, hx⟩ := hYleft
                obtain ⟨k, rfl⟩ := exists_eq_adaptedCoordinateYFactor L x hx
                have hbad := adaptedPlacedPacket_terminal_last_le_head
                  L L ev p (adaptedCoordinateXFactor L i) hrel (by omega)
                  hterminal [] (adaptedCoordinateYFactor L k) (by rw [hl]; rfl)
                exact (adaptedCoordinateYFactor_not_le_x k i hbad).elim
              · obtain ⟨x, hl, hr, hx⟩ := hYright
                obtain ⟨k, rfl⟩ := exists_eq_adaptedCoordinateYFactor L x hx
                rcases p with ⟨left, relation, right⟩
                simp only at hl hr hrel
                subst left; subst relation; subst right
                simp only [AdaptedSmithPlacedPacket.value,
                  AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                  AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
                  envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hRowX, hFactorY]
                rw [hFirstRightY i k]
                simp [IsAdaptedRowPacket, adaptedCoordinateXFactor_inj_iff,
                  adaptedCoordinateYFactor_inj_iff, eq_comm, hsumSingle, hsumPair]
                convert (hsumPair i k (fun x y =>
                    (2 * R.coordinateD x : ℤ) • R.coordinateGMod x y)).symm
                  using 1 <;> abel
              · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXleft
                obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
                obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
                rcases p with ⟨left, relation, right⟩
                simp only at hl hr hrel
                subst left; subst relation; subst right
                simp only [AdaptedSmithPlacedPacket.value,
                  AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                  AdaptedCollectedRelation.value, List.map_cons, List.map_nil,
                  envelopingWord_cons, envelopingWord_nil, mul_one, hRowX, hFactorX]
                rw [hTwoXLeft j l i]
                simp only [IsAdaptedRowPacket, List.cons_ne_nil, List.nil_eq,
                  List.cons.injEq, false_and, and_false, if_false,
                  Finset.sum_const_zero, smul_zero, zero_add, add_zero]
              · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXsplit
                obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
                obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
                rcases p with ⟨left, relation, right⟩
                simp only at hl hr hrel
                subst left; subst relation; subst right
                simp only [AdaptedSmithPlacedPacket.value,
                  AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                  AdaptedCollectedRelation.value, List.map_singleton,
                  envelopingWord_cons, envelopingWord_nil, mul_one, hRowX, hFactorX]
                rw [hTwoXSplit j i l]
                simp only [IsAdaptedRowPacket, List.cons_ne_nil, List.nil_eq,
                  List.cons.injEq, false_and, and_false, if_false,
                  Finset.sum_const_zero, smul_zero, zero_add, add_zero]
              · obtain ⟨x, y, hl, hr, hx, hy⟩ := hXXright
                obtain ⟨j, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
                obtain ⟨l, rfl⟩ := exists_eq_adaptedCoordinateXFactor L y hy
                rcases p with ⟨left, relation, right⟩
                simp only at hl hr hrel
                subst left; subst relation; subst right
                simp only [AdaptedSmithPlacedPacket.value,
                  AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                  AdaptedCollectedRelation.value, List.map_cons, List.map_nil,
                  envelopingWord_cons, envelopingWord_nil, one_mul, mul_one, hRowX, hFactorX]
                rw [← mul_assoc, hTwoXRight i j l]
                simp only [IsAdaptedRowPacket, List.cons_ne_nil, List.nil_eq,
                  List.cons.injEq, false_and, and_false, if_false,
                  Finset.sum_const_zero, smul_zero, zero_add, add_zero]
          · obtain ⟨k, rfl⟩ := exists_eq_adaptedCoordinateYFactor L row hrowtwo
            have hextle : p.externalWeight L ≤ 1 := by
              rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
              simp only [AdaptedCollectedRelation.weight, adaptedLowRelationRowWeight,
                adaptedCoordinateYFactor_weight] at hle
              omega
            rcases (show p.externalWeight L = 0 ∨ p.externalWeight L = 1 by omega) with
              hextzero | hextone
            · obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hextzero
              rcases p with ⟨left, relation, right⟩
              simp only at hl hr hrel
              subst left; subst relation; subst right
              simp only [AdaptedSmithPlacedPacket.value,
                AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                AdaptedCollectedRelation.value, List.map_nil, envelopingWord_nil,
                one_mul, mul_one, hRowY]
              rw [hSecondScalar k]
              simp [IsAdaptedRowPacket, adaptedCoordinateXFactor_inj_iff,
                adaptedCoordinateYFactor_inj_iff, eq_comm, hsumSingle, hsumPair]
              convert
                (hsumSingle k (fun x => (-3 : ℤ) • (R.coordinateM x : ZMod R.q))).symm
                using 1 <;> abel
            · rcases p.externalWeight_eq_one_iff.mp hextone with hleft | hright
              · obtain ⟨x, hl, hr, hx⟩ := hleft
                obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
                rcases p with ⟨left, relation, right⟩
                simp only at hl hr hrel
                subst left; subst relation; subst right
                simp only [AdaptedSmithPlacedPacket.value,
                  AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                  AdaptedCollectedRelation.value, List.map_singleton, List.map_nil,
                  envelopingWord_cons, envelopingWord_nil, mul_one, hRowY, hFactorX]
                rw [hLeftXSecond i k]
                simp [IsAdaptedRowPacket, adaptedCoordinateXFactor_inj_iff,
                  adaptedCoordinateYFactor_inj_iff, eq_comm, hsumSingle, hsumPair]
                convert (hsumPair i k (fun x y =>
                    (2 * R.coordinateE y : ℤ) • R.coordinateGMod x y)).symm
                  using 1 <;> abel
              · obtain ⟨x, hl, hr, hx⟩ := hright
                obtain ⟨i, rfl⟩ := exists_eq_adaptedCoordinateXFactor L x hx
                have hbad := adaptedPlacedPacket_terminal_head_le_first
                  L L ev p (adaptedCoordinateYFactor L k) hrel (by omega)
                  hterminal (adaptedCoordinateXFactor L i) [] (by rw [hr])
                exact (adaptedCoordinateYFactor_not_le_x k i hbad).elim
          · have hext : p.externalWeight L = 0 := by
              rw [AdaptedSmithPlacedPacket.totalWeight, hrel] at hle
              simp only [AdaptedCollectedRelation.weight,
                adaptedLowRelationRowWeight, hrowthree] at hle
              omega
            obtain ⟨hl, hr⟩ := p.externalWeight_eq_zero_iff.mp hext
            rcases p with ⟨left, relation, right⟩
            simp only at hl hr hrel
            subst left; subst relation; subst right
            have hrowGamma := hPhiGamma (adaptedLowRelationRow L L ev row) (by
              have hm := adaptedLowRelationRow_mem_lieHigh L L ev row
              simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 2,
                adaptedLowRelationRowWeight, hrowthree] using hm)
            have heval : ev (adaptedLowRelationRow L L ev row) = 0 :=
              adaptedLowRelationRow_mem_ker L L ev row
            have hnotX (i : CoordinateI L) :
                row ≠ adaptedCoordinateXFactor L i := by
              intro hi
              rw [hi, adaptedCoordinateXFactor_weight] at hrowthree
              omega
            have hnotY (k : CoordinateK L) :
                row ≠ adaptedCoordinateYFactor L k := by
              intro hk
              rw [hk, adaptedCoordinateYFactor_weight] at hrowthree
              omega
            have hrowCoordZero : R.gammaThreeEquiv
                (⟨ev (adaptedLowRelationRow L L ev row), by
                  apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) 2)
                  exact LieIdeal.mem_map (by
                    have hm := adaptedLowRelationRow_mem_lieHigh L L ev row
                    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 2,
                      adaptedLowRelationRowWeight, hrowthree] using hm)⟩ :
                  lowerCentralSeries ℤ L 2) = 0 := by
              rw [show (⟨ev (adaptedLowRelationRow L L ev row), _⟩ :
                  lowerCentralSeries ℤ L 2) = 0 by
                apply Subtype.ext
                exact heval]
              exact R.gammaThreeEquiv.toAddMonoidHom.map_zero
            rw [show R.dynkinThreeCoordinate
                ((⟨[], .row row, []⟩ : AdaptedSmithPlacedPacket L L ev).value L L ev) = 0 by
              simpa [AdaptedSmithPlacedPacket.value,
                AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
                AdaptedCollectedRelation.value] using (hrowGamma.trans (by
                  rw [hrowCoordZero, smul_zero]
                  rfl))]
            simp [IsAdaptedRowPacket, hnotX, hnotY]
            abel
    have hshapeSum
        (row : AdaptedLowRelationRowIndex L)
        (left right : List (AdaptedLowBasisIndex L)) (c : ZMod R.q) :
        w.terminalPackets.sum (fun p n => n •
          (if IsAdaptedRowPacket L L ev row left right p then c else 0)) =
        (adaptedLedgerRowCoefficient L L ev w.terminalPackets row left right : ℤ) • c := by
      classical
      unfold adaptedLedgerRowCoefficient Finsupp.sum
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hs : IsAdaptedRowPacket L L ev row left right p <;>
        simp only [hs, if_true, if_false, smul_zero, zero_smul]
    have hfamilySingle {A : Type} [Fintype A]
        (row : A → AdaptedLowRelationRowIndex L)
        (left right : A → List (AdaptedLowBasisIndex L)) (c : A → ZMod R.q) :
        w.terminalPackets.sum (fun p n => n •
          (∑ x : A, if IsAdaptedRowPacket L L ev (row x) (left x) (right x) p
            then c x else 0)) =
        ∑ x : A, (adaptedLedgerRowCoefficient L L ev w.terminalPackets
          (row x) (left x) (right x) : ℤ) • c x := by
      classical
      unfold Finsupp.sum
      simp only [Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      exact hshapeSum (row x) (left x) (right x) (c x)
    have hfamilyPair {A B : Type} [Fintype A] [Fintype B]
        (row : A → B → AdaptedLowRelationRowIndex L)
        (left right : A → B → List (AdaptedLowBasisIndex L))
        (c : A → B → ZMod R.q) :
        w.terminalPackets.sum (fun p n => n •
          (∑ x : A, ∑ y : B,
            if IsAdaptedRowPacket L L ev (row x y) (left x y) (right x y) p
            then c x y else 0)) =
        ∑ x : A, ∑ y : B,
          (adaptedLedgerRowCoefficient L L ev w.terminalPackets
            (row x y) (left x y) (right x y) : ℤ) • c x y := by
      classical
      calc
        _ = w.terminalPackets.sum (fun p n => n •
            (∑ xy : A × B,
              if IsAdaptedRowPacket L L ev (row xy.1 xy.2)
                (left xy.1 xy.2) (right xy.1 xy.2) p
              then c xy.1 xy.2 else 0)) := by
                apply Finsupp.sum_congr
                intro p hp
                apply congrArg (fun z : ZMod R.q =>
                  (w.terminalPackets p : ℤ) • z)
                exact (Fintype.sum_prod_type (fun xy : A × B =>
                  if IsAdaptedRowPacket L L ev (row xy.1 xy.2)
                    (left xy.1 xy.2) (right xy.1 xy.2) p
                  then c xy.1 xy.2 else 0)).symm
        _ = ∑ xy : A × B,
            (adaptedLedgerRowCoefficient L L ev w.terminalPackets
              (row xy.1 xy.2) (left xy.1 xy.2) (right xy.1 xy.2) : ℤ) •
                c xy.1 xy.2 := hfamilySingle
                  (fun xy : A × B => row xy.1 xy.2)
                  (fun xy : A × B => left xy.1 xy.2)
                  (fun xy : A × B => right xy.1 xy.2)
                  (fun xy : A × B => c xy.1 xy.2)
        _ = _ := Fintype.sum_prod_type (fun xy : A × B =>
          (adaptedLedgerRowCoefficient L L ev w.terminalPackets
            (row xy.1 xy.2) (left xy.1 xy.2) (right xy.1 xy.2) : ℤ) •
              c xy.1 xy.2)
    have hledgerAdd (f g : AdaptedSmithPlacedPacket L L ev → ZMod R.q) :
        w.terminalPackets.sum (fun p n => n • (f p + g p)) =
          w.terminalPackets.sum (fun p n => n • f p) +
            w.terminalPackets.sum (fun p n => n • g p) := by
      classical
      unfold Finsupp.sum
      simp only [smul_add, Finset.sum_add_distrib]
    have hraw : R.dynkinThreeCoordinate
        ((adaptedPlacedPacketCollector L L ev).evaluate w.terminalPackets) =
          ((∑ i : CoordinateI L,
              (AdaptedTerminalCoordinates.r L L ev w.terminalPackets i : ℤ) •
                ((-3 : ℤ) • (R.coordinateC i : ZMod R.q))) +
            (∑ k : CoordinateK L,
              (AdaptedTerminalCoordinates.s L L ev w.terminalPackets k : ℤ) •
                ((-3 : ℤ) • (R.coordinateM k : ZMod R.q)))) +
          ((∑ i : CoordinateI L, ∑ j : CoordinateI L,
              (AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i j : ℤ) •
                gamma i j) +
            (∑ i : CoordinateI L, ∑ j : CoordinateI L,
              (adaptedLedgerRowCoefficient L L ev w.terminalPackets
                  (adaptedCoordinateXFactor L i) [adaptedCoordinateXFactor L j] [] : ℤ) •
                ((-2 : ℤ) • gamma i j))) +
          ((∑ i : CoordinateI L, ∑ k : CoordinateK L,
              (AdaptedTerminalCoordinates.v L L ev w.terminalPackets i k : ℤ) •
                ((2 * R.coordinateD i : ℤ) • R.coordinateGMod i k)) +
            (∑ i : CoordinateI L, ∑ k : CoordinateK L,
              (AdaptedTerminalCoordinates.v' L L ev w.terminalPackets i k : ℤ) •
                ((2 * R.coordinateE k : ℤ) • R.coordinateGMod i k))) := by
      change R.dynkinThreeCoordinate
          (w.terminalPackets.sum (fun p n => n • p.value L L ev)) = _
      rw [map_finsuppSum]
      calc
        _ = w.terminalPackets.sum (fun p n => n •
            ((∑ i : CoordinateI L,
                if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i) [] [] p
                then (-3 : ℤ) • (R.coordinateC i : ZMod R.q) else 0) +
              (∑ k : CoordinateK L,
                if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k) [] [] p
                then (-3 : ℤ) • (R.coordinateM k : ZMod R.q) else 0) +
              (((∑ i : CoordinateI L, ∑ j : CoordinateI L,
                  if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
                      [] [adaptedCoordinateXFactor L j] p then gamma i j else 0) +
                (∑ i : CoordinateI L, ∑ j : CoordinateI L,
                  if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
                      [adaptedCoordinateXFactor L j] [] p
                  then (-2 : ℤ) • gamma i j else 0)) +
                ((∑ i : CoordinateI L, ∑ k : CoordinateK L,
                    if IsAdaptedRowPacket L L ev (adaptedCoordinateXFactor L i)
                        [] [adaptedCoordinateYFactor L k] p
                    then (2 * R.coordinateD i : ℤ) • R.coordinateGMod i k else 0) +
                  (∑ i : CoordinateI L, ∑ k : CoordinateK L,
                    if IsAdaptedRowPacket L L ev (adaptedCoordinateYFactor L k)
                        [adaptedCoordinateXFactor L i] [] p
                    then (2 * R.coordinateE k : ℤ) • R.coordinateGMod i k else 0))))) := by
              apply Finsupp.sum_congr
              intro p hp
              rw [map_smul, hPacket p hp]
              simp only [add_assoc]
        _ = _ := by
          rw [hledgerAdd, hledgerAdd, hledgerAdd, hledgerAdd, hledgerAdd]
          rw [hfamilySingle, hfamilySingle, hfamilyPair, hfamilyPair,
            hfamilyPair, hfamilyPair]
          simp only [AdaptedTerminalCoordinates.r, AdaptedTerminalCoordinates.s,
            AdaptedTerminalCoordinates.rx, AdaptedTerminalCoordinates.v,
            AdaptedTerminalCoordinates.v']
          abel
    let cs := R.terminalCoefficientSystem w 0
    have hgamma (i j : CoordinateI L) :
        gamma i j = (R.coordinateData).gamma i j := by
      simp only [gamma, Coordinate.Data.gamma, coordinateData, coordinateG_cast]
    have hr (i : CoordinateI L) :
        AdaptedTerminalCoordinates.r L L ev w.terminalPackets i = 0 := by
      have hi := R.terminalPreTheta_xEquation w 0 i
      rw [show preThetaProjection R.coordinateData (.x i) =
          rawCoefficient [.x i] by rfl, rawCoefficient_preTheta_x] at hi
      exact int_mul_eq_zero_cancel (by exact_mod_cast (R.coordinateD_pos i).ne') hi
    have hs (k : CoordinateK L) :
        AdaptedTerminalCoordinates.s L L ev w.terminalPackets k = 0 := by
      have hk := R.terminalPreTheta_yEquation w 0 k
      rw [show preThetaProjection R.coordinateData (.y k) =
          rawCoefficient [.y k] by rfl, rawCoefficient_preTheta_y] at hk
      simp only [terminalPreTheta_r, terminalPreTheta_s, hr, zero_mul,
        Finset.sum_const_zero, neg_zero, zero_add] at hk
      exact int_mul_eq_zero_cancel (by exact_mod_cast (R.coordinateE_pos k).ne') hk
    have hpair {i j : CoordinateI L} (hij : i < j) :
        AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i j =
          ((R.coordinateData).dRatio i j : ℤ) *
            (-AdaptedTerminalCoordinates.xr L L ev w.terminalPackets i j) := by
      have heq := R.terminalPreTheta_xxOffdiagEquation w 0 hij
      rw [show preThetaProjection R.coordinateData (.xx i j) =
          rawCoefficient [.x i, .x j] by rfl,
        rawCoefficient_preTheta_xx _ _ _ hij] at heq
      have hsyz := Coordinate.Data.CollectedExpression.adjacent_smith_syzygy
        (R.coordinateD_pos i) (R.coordinateData_d_dvd hij.le) heq
      simpa [Coordinate.Data.CollectedExpression.PreTheta.typeIICoefficient,
        Coordinate.Data.dRatio, StandingReductionData.coordinateData] using hsyz
    have hZ :
        (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
          (AdaptedTerminalCoordinates.rx L L ev w.terminalPackets ij.1 ij.2 :
              ZMod R.q) * gamma ij.1 ij.2) = R.terminalZeta w 0 := by
      have hz := cs.Z_eq
      change (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
          ((-AdaptedTerminalCoordinates.xr L L ev w.terminalPackets ij.1 ij.2 : ℤ) :
              ZMod R.q) *
            ((R.coordinateData).dRatio ij.1 ij.2 : ZMod R.q) *
              (R.coordinateData).gamma ij.1 ij.2) = R.terminalZeta w 0 at hz
      rw [← hz]
      apply Finset.sum_congr rfl
      intro ij hijmem
      have hij := Coordinate.mem_upperPairs.mp hijmem
      rw [hgamma]
      have hp := congrArg (fun z : ℤ => (z : ZMod R.q)) (hpair hij)
      push_cast at hp
      rw [hp]
      push_cast
      ring
    have hDterm (i : CoordinateI L) (k : CoordinateK L) :
        (AdaptedTerminalCoordinates.v L L ev w.terminalPackets i k : ℤ) •
            ((2 * R.coordinateD i : ℤ) • R.coordinateGMod i k) = 0 := by
      have hd := R.coordinate_DG i k
      rw [R.coordinateG_cast] at hd
      simp only [zsmul_eq_mul]
      push_cast
      linear_combination
        (2 * (AdaptedTerminalCoordinates.v L L ev w.terminalPackets i k :
          ZMod R.q)) * hd
    have hEterm (i : CoordinateI L) (k : CoordinateK L) :
        (AdaptedTerminalCoordinates.v' L L ev w.terminalPackets i k : ℤ) •
            ((2 * R.coordinateE k : ℤ) • R.coordinateGMod i k) = 0 := by
      have he := R.coordinate_GE i k
      rw [R.coordinateG_cast] at he
      simp only [zsmul_eq_mul]
      push_cast
      linear_combination
        (2 * (AdaptedTerminalCoordinates.v' L L ev w.terminalPackets i k :
          ZMod R.q)) * he
    have hsumUpper {f : CoordinateI L → CoordinateI L → ZMod R.q}
        (hf : ∀ i j, ¬ i < j → f i j = 0) :
        (∑ i, ∑ j, f i j) =
          ∑ ij ∈ Coordinate.upperPairs (CoordinateI L), f ij.1 ij.2 := by
      rw [Coordinate.sum_upperPairs]
      apply Finset.sum_congr rfl
      intro i hi
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hjnot
      rw [hf i j]
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hjnot
    have hrightSum :
        (∑ i : CoordinateI L, ∑ j : CoordinateI L,
          (AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i j : ℤ) •
            gamma i j) =
        ∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
          (AdaptedTerminalCoordinates.rx L L ev w.terminalPackets ij.1 ij.2 : ℤ) •
            gamma ij.1 ij.2 := by
      apply hsumUpper
      intro i j hnot
      rcases lt_or_eq_of_le (le_of_not_gt hnot) with hji | rfl
      · change (adaptedLedgerRowCoefficient L L ev w.terminalPackets
            (adaptedCoordinateXFactor L i) [] [adaptedCoordinateXFactor L j] : ℤ) •
            gamma i j = 0
        rw [terminalPackets_rightXCoefficient_eq_zero_of_lt w hji, zero_smul]
      · rw [hgamma, R.coordinate_gamma_diag, smul_zero]
    have hleftSum :
        (∑ i : CoordinateI L, ∑ j : CoordinateI L,
          (adaptedLedgerRowCoefficient L L ev w.terminalPackets
              (adaptedCoordinateXFactor L i) [adaptedCoordinateXFactor L j] [] : ℤ) •
            ((-2 : ℤ) • gamma i j)) =
        ∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
          (AdaptedTerminalCoordinates.xr L L ev w.terminalPackets ij.1 ij.2 : ℤ) •
            ((-2 : ℤ) • gamma ij.2 ij.1) := by
      rw [Finset.sum_comm]
      apply hsumUpper
      intro i j hnot
      rcases lt_or_eq_of_le (le_of_not_gt hnot) with hji | rfl
      · change (adaptedLedgerRowCoefficient L L ev w.terminalPackets
            (adaptedCoordinateXFactor L j) [adaptedCoordinateXFactor L i] [] : ℤ) •
              ((-2 : ℤ) • gamma j i) = 0
        rw [terminalPackets_leftXCoefficient_eq_zero_of_lt w hji, zero_smul]
      · rw [hgamma, R.coordinate_gamma_diag, smul_zero, smul_zero]
    have hrawSimple : R.dynkinThreeCoordinate
        ((adaptedPlacedPacketCollector L L ev).evaluate w.terminalPackets) =
          (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
            (AdaptedTerminalCoordinates.rx L L ev w.terminalPackets ij.1 ij.2 : ℤ) •
              gamma ij.1 ij.2) +
          (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
            (AdaptedTerminalCoordinates.xr L L ev w.terminalPackets ij.1 ij.2 : ℤ) •
              ((-2 : ℤ) • gamma ij.2 ij.1)) := by
      rw [hraw, hrightSum, hleftSum]
      simp_rw [hr, hs, zero_smul, hDterm, hEterm]
      simp only [Finset.sum_const_zero, smul_zero, zero_add, add_zero]
    let alpha : CoordinateI L → CoordinateK L → ZMod R.q :=
      fun i k => R.coordinateGMod i k
    have hcertificateX (i j : CoordinateI L) :
        (R.coordinateData).certificateX alpha i j = gamma i j := by
      simp only [Coordinate.Data.certificateX, alpha, gamma,
        StandingReductionData.coordinateData]
    have hUpperEntry (i : CoordinateI L) (k : CoordinateK L) :
        (R.coordinateData).upperSkewMulMod cs.u i k * alpha i k = 0 := by
      have hb := congrArg (fun z : ℤ => (z : ZMod R.q)) (cs.B_eq i k)
      push_cast at hb
      rw [(R.coordinateData).intCast_upperSkewMul] at hb
      have hd := R.coordinate_DG i k
      have he := R.coordinate_GE i k
      rw [R.coordinateG_cast] at hd he
      change ((R.coordinateData).d i : ZMod R.q) * R.coordinateGMod i k = 0 at hd
      change R.coordinateGMod i k * ((R.coordinateData).e k : ZMod R.q) = 0 at he
      dsimp only [alpha]
      linear_combination
        R.coordinateGMod i k * hb -
          (cs.v i k : ZMod R.q) * hd -
          (cs.v' i k : ZMod R.q) * he
    have hUpperZero :
        (∑ i : CoordinateI L, ∑ k : CoordinateK L,
          (R.coordinateData).upperSkewMulMod cs.u i k * alpha i k) = 0 := by
      simp only [hUpperEntry, Finset.sum_const_zero, smul_zero]
    have hPairing :
        (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
          (cs.u ij.1 ij.2 : ZMod R.q) *
            (gamma ij.2 ij.1 -
              ((R.coordinateData).dRatio ij.1 ij.2 : ZMod R.q) *
                gamma ij.1 ij.2)) = 0 := by
      have hp := (R.coordinateData).upperPair_certificateX cs.u alpha
      rw [hUpperZero] at hp
      simpa only [hcertificateX] using hp
    have hTwoZeta : (2 : ℤ) • R.terminalZeta w 0 = 0 := by
      rw [← cs.Z_eq]
      simp only [zsmul_eq_mul]
      simp_rw [← hgamma]
      calc
        ((2 : ℤ) : ZMod R.q) *
              (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
                (cs.u ij.1 ij.2 : ZMod R.q) *
                  ((R.coordinateData).dRatio ij.1 ij.2 : ZMod R.q) *
                    gamma ij.1 ij.2) =
            ∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
              -((cs.u ij.1 ij.2 : ZMod R.q) *
                (gamma ij.2 ij.1 -
                  ((R.coordinateData).dRatio ij.1 ij.2 : ZMod R.q) *
                    gamma ij.1 ij.2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ij hijmem
          have hskew := R.coordinate_gamma_skew
            (Coordinate.mem_upperPairs.mp hijmem)
          rw [← hgamma ij.2 ij.1, ← hgamma ij.1 ij.2] at hskew
          linear_combination
            (cs.u ij.1 ij.2 : ZMod R.q) * hskew
        _ = -(∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
              (cs.u ij.1 ij.2 : ZMod R.q) *
                (gamma ij.2 ij.1 -
                  ((R.coordinateData).dRatio ij.1 ij.2 : ZMod R.q) *
                    gamma ij.1 ij.2)) := by rw [Finset.sum_neg_distrib]
        _ = 0 := by rw [hPairing, neg_zero]
    have hleftPoint {i j : CoordinateI L} (hij : i < j) :
        (AdaptedTerminalCoordinates.xr L L ev w.terminalPackets i j : ℤ) •
            ((-2 : ℤ) • gamma j i) =
          (-2 : ℤ) •
            ((AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i j : ℤ) •
              gamma i j) := by
      have hp := congrArg (fun z : ℤ => (z : ZMod R.q)) (hpair hij)
      push_cast at hp
      have hskew := R.coordinate_gamma_skew hij
      rw [← hgamma j i, ← hgamma i j] at hskew
      simp only [zsmul_eq_mul]
      linear_combination
        -2 * (AdaptedTerminalCoordinates.xr L L ev w.terminalPackets i j :
          ZMod R.q) * hskew + 2 * gamma i j * hp
    have hleftAggregate :
        (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
          (AdaptedTerminalCoordinates.xr L L ev w.terminalPackets ij.1 ij.2 : ℤ) •
            ((-2 : ℤ) • gamma ij.2 ij.1)) =
          (-2 : ℤ) •
            (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
              (AdaptedTerminalCoordinates.rx L L ev w.terminalPackets ij.1 ij.2 : ℤ) •
                gamma ij.1 ij.2) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ij hijmem
      exact hleftPoint (Coordinate.mem_upperPairs.mp hijmem)
    rw [hrawSimple, hleftAggregate]
    have hzsmul :
        (∑ ij ∈ Coordinate.upperPairs (CoordinateI L),
          (AdaptedTerminalCoordinates.rx L L ev w.terminalPackets ij.1 ij.2 : ℤ) •
            gamma ij.1 ij.2) = R.terminalZeta w 0 := by
      simpa only [zsmul_eq_mul] using hZ
    rw [hzsmul]
    have hFourZeta : (4 : ℤ) • R.terminalZeta w 0 = 0 := by
      calc
        (4 : ℤ) • R.terminalZeta w 0 =
            (2 : ℤ) • ((2 : ℤ) • R.terminalZeta w 0) := by module
        _ = 0 := by rw [hTwoZeta, smul_zero]
    calc
      R.terminalZeta w 0 + (-2 : ℤ) • R.terminalZeta w 0 =
          (3 : ℤ) • R.terminalZeta w 0 -
            (4 : ℤ) • R.terminalZeta w 0 := by module
      _ = (3 : ℤ) • R.terminalZeta w 0 := by rw [hFourZeta, sub_zero]
  have hvalue := congrArg R.dynkinThreeCoordinate w.terminalPackets_value
  rw [map_sub] at hvalue
  have hhigh5 := FreeLieDimension.universalEnvelopingEquiv_mem_associativeHigh
    L 5 w.highWord_mem
  have hhigh4 : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L w.highWord ∈
      FreeLieDimension.associativeHigh L 4 :=
    FreeLieDimension.associativeHigh_mono L (by omega) hhigh5
  have hhighZero :=
    R.dynkinThreeCoordinate_eq_zero_of_mem_associativeHigh_four w.highWord hhigh4
  have hlift := hPhiGamma w.lieLift w.lieLift_mem_gammaThree
  rw [hledger, hhighZero, sub_zero, hlift] at hvalue
  have hcoord : R.gammaThreeEquiv
      ⟨ev w.lieLift, by
        apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) 2)
        exact LieIdeal.mem_map w.lieLift_mem_gammaThree⟩ =
      R.gammaThreeEquiv
        ⟨a, by
          rw [← w.evaluates]
          apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) 2)
          exact LieIdeal.mem_map w.lieLift_mem_gammaThree⟩ := by
    apply congrArg R.gammaThreeEquiv
    exact Subtype.ext w.evaluates
  rw [hcoord] at hvalue
  have hunit : IsUnit (3 : ZMod R.q) := by
    apply (ZMod.isUnit_iff_coprime 3 R.q).2
    rw [R.q_eq]
    apply Nat.Coprime.pow_right
    decide
  let target : ZMod R.q := R.gammaThreeEquiv
      ⟨a, by
        rw [← w.evaluates]
        apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) 2)
        exact LieIdeal.mem_map w.lieLift_mem_gammaThree⟩
  have htarget : R.gammaThreeEquiv
      ⟨a, by
        rw [← w.evaluates]
        apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) 2)
        exact LieIdeal.mem_map w.lieLift_mem_gammaThree⟩ = target := rfl
  rw [htarget] at hvalue
  simp only [zsmul_eq_mul] at hvalue
  have hunitInt : IsUnit ((3 : ℤ) : ZMod R.q) := by
    rw [show ((3 : ℤ) : ZMod R.q) = (3 : ZMod R.q) by norm_num]
    exact hunit
  have hcanc : R.terminalZeta w 0 = target := hunitInt.mul_left_cancel hvalue
  simpa [target] using hcanc

/-- Under the standing reduction, the three Dynkin identities force the fifth dimension
subring to vanish. -/
theorem dimensionSubring_five_eq_bot_of_dynkinProperties
    (R : StandingReductionData L) (hPhi : DynkinProperties R) :
    dimensionSubring ℤ L 5 = ⊥ := by
  letI : Finite L := R.finite_inst
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨w⟩ := exists_adaptedPresentationDimensionFiveWitness a ha
  have hz := R.terminalZeta_eq_zero w 0
  have hc := R.terminalZeta_eq_targetCoordinate hPhi w
  rw [hz] at hc
  let a3 : lowerCentralSeries ℤ L 2 := ⟨a, by
      rw [← w.evaluates]
      apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) 2)
      exact LieIdeal.mem_map w.lieLift_mem_gammaThree⟩
  have hsub : a3 = 0 := by
    apply R.gammaThreeEquiv.injective
    exact hc.symm.trans R.gammaThreeEquiv.map_zero.symm
  exact congrArg Subtype.val hsub

/-- Under the standing reduction alone, the fifth dimension subring vanishes. -/
theorem dimensionSubring_five_eq_bot (R : StandingReductionData L) :
    dimensionSubring ℤ L 5 = ⊥ :=
  R.dimensionSubring_five_eq_bot_of_dynkinProperties R.dynkinProperties

end StandingReductionData

end

end DegreeFive

end LieRings
