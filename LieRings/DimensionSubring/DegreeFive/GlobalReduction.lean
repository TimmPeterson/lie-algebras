import LieRings.DimensionSubring.DegreeFive.AdaptedDynkinReduction
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Global reduction for the fifth dimension-subring theorem

This file formalizes every quotient step from a finite class-three witness to the standing
reduction.  The external input `2δ₄ ⊆ γ₄` is kept as an explicit proposition.  The
finite-support argument which supplies `FiniteWitnessProperty` is isolated as a separate
interface, so it cannot be confused with quotient functoriality.
-/

open scoped DirectSum

noncomputable section

namespace LieRings.DegreeFive

theorem exists_cyclic_detector
    {G : Type*} [AddCommGroup G] [Finite G]
    (hG : IsPGroup 2 (Multiplicative G)) {c : G} (hc : c ≠ 0) :
    ∃ (k : ℕ) (f : G →+ ZMod (2 ^ k)),
      Function.Surjective f ∧ f c ≠ 0 := by
  classical
  obtain ⟨ι, fintypeι, n, hn, ⟨e⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite' G
  letI : Fintype ι := fintypeι
  have hec : e c ≠ 0 := fun h ↦ hc (e.injective (h.trans (map_zero e).symm))
  have hcoord : ∃ i : ι, e c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hec (DFinsupp.ext fun i ↦ by simpa using h i)
  obtain ⟨i, hi⟩ := hcoord
  let f₀ : G →+ ZMod (n i) :=
    (DFinsupp.evalAddMonoidHom i).comp e.toAddMonoidHom
  have hf₀ : Function.Surjective f₀ := by
    intro z
    refine ⟨e.symm (DFinsupp.single i z), ?_⟩
    change (e (e.symm (DFinsupp.single i z))) i = z
    simp
  letI : NeZero (n i) := ⟨Nat.ne_zero_of_lt (hn i)⟩
  have hp₀ : IsPGroup 2 (Multiplicative (ZMod (n i))) :=
    hG.of_surjective f₀.toMultiplicative hf₀
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hp₀.exists_card_eq
  have hni : n i = 2 ^ k := by
    rw [← Nat.card_zmod (n i)]
    exact (Nat.card_congr Multiplicative.toAdd).trans hk
  let E : ZMod (n i) ≃+ ZMod (2 ^ k) :=
    (ZMod.ringEquivCongr hni).toAddEquiv
  refine ⟨k, E.toAddMonoidHom.comp f₀, E.surjective.comp hf₀, ?_⟩
  exact fun h ↦ hi (E.injective (h.trans (map_zero E).symm))

theorem exists_two_pow_not_mem
    {G : Type*} [AddCommGroup G] [Module.Finite ℤ G]
    {c : G} (hc : c ≠ 0) (h2c : 2 • c = 0) :
    ∃ k : ℕ, ¬ ∃ x : G, (2 ^ k : ℤ) • x = c := by
  classical
  letI : AddGroup.FG G := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨m, ι, fintypeι, p, hp, e, ⟨E⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  letI : Fintype ι := fintypeι
  have hEc : E c ≠ 0 := fun h ↦ hc (E.injective (h.trans (map_zero E).symm))
  have hfree : (E c).1 = 0 := by
    have h := congrArg Prod.fst (congrArg E h2c)
    simp only [map_nsmul, map_zero, Prod.smul_fst] at h
    have hz : (2 : ℤ) • (E c).1 = 0 := by simpa using h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have htor : (E c).2 ≠ 0 := by
    intro h
    exact hEc (Prod.ext hfree h)
  have hcoord : ∃ i : ι, (E c).2 i ≠ 0 := by
    by_contra h
    push Not at h
    exact htor (DFinsupp.ext fun i ↦ by simpa using h i)
  obtain ⟨i, hi⟩ := hcoord
  let f₀ : G →+ ZMod (p i ^ e i) :=
    (DFinsupp.evalAddMonoidHom i).comp
      ((AddMonoidHom.snd _ _).comp E.toAddMonoidHom)
  have hf2 : 2 • f₀ c = 0 := by rw [← map_nsmul, h2c, map_zero]
  have hord : addOrderOf (f₀ c) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp
        ((addOrderOf_dvd_iff_nsmul_eq_zero).mpr hf2) with h | h
    · exact False.elim (hi (AddMonoid.addOrderOf_eq_one_iff.mp h))
    · exact h
  have hpEq : p i = 2 := by
    letI : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
    have hdvd : 2 ∣ p i ^ e i := by
      rw [← hord]
      simpa only [ZMod.card] using
        (addOrderOf_dvd_card (G := ZMod (p i ^ e i)) (x := f₀ c))
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hp i)).mp
      (Nat.prime_two.dvd_of_dvd_pow hdvd)).symm
  refine ⟨e i, ?_⟩
  rintro ⟨x, hx⟩
  have hmap := congrArg f₀ hx
  have hzero : f₀ ((2 ^ e i : ℤ) • x) = 0 := by
    rw [map_zsmul]
    have hmod : p i ^ e i = 2 ^ e i := congrArg (fun a ↦ a ^ e i) hpEq
    have hn : (p i ^ e i) • f₀ x = 0 := by simp [nsmul_eq_mul]
    have hn2 : (2 ^ e i) • f₀ x = 0 := by rw [← hmod]; exact hn
    simpa using hn2
  exact hi (hmap.symm.trans hzero)

universe u

variable (B : Type u) [LieRing B]

/-- The ideal of scalar multiples `nB`. -/
def multipleIdeal (n : ℤ) : LieIdeal ℤ B where
  toSubmodule := LinearMap.range (n • (LinearMap.id : B →ₗ[ℤ] B))
  lie_mem := by
    rintro x y ⟨z, rfl⟩
    refine ⟨⁅x, z⁆, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [lie_smul]

theorem mem_multipleIdeal_iff (n : ℤ) (x : B) :
    x ∈ multipleIdeal B n ↔ ∃ y : B, n • y = x := by
  rfl

abbrev MultipleQuotient (n : ℕ) :=
  B ⧸ multipleIdeal B (n : ℤ)

theorem multipleQuotient_nsmul_eq_zero (n : ℕ)
    (x : MultipleQuotient B n) : n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change (LieSubmodule.Quotient.mk (n • x) : MultipleQuotient B n) = 0
      apply (LieSubmodule.Quotient.mk_eq_zero'
        (N := multipleIdeal B (n : ℤ))).mpr
      exact ⟨x, by simp⟩

theorem multipleQuotient_finite (n : ℕ) (hn : n ≠ 0)
    [Module.Finite ℤ B] : Finite (MultipleQuotient B n) := by
  letI : Module.Finite ℤ (MultipleQuotient B n) :=
    Module.Finite.quotient ℤ (multipleIdeal B (n : ℤ)).toSubmodule
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(n : ℤ), ?_⟩, ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (Int.ofNat_ne_zero.mpr hn)
  · simpa using multipleQuotient_nsmul_eq_zero B n x

theorem multipleQuotient_isPGroup_two (k : ℕ) :
    IsPGroup 2 (Multiplicative (MultipleQuotient B (2 ^ k))) := by
  intro x
  refine ⟨k, ?_⟩
  change Multiplicative.ofAdd ((2 ^ k) • Multiplicative.toAdd x) =
    Multiplicative.ofAdd 0
  rw [multipleQuotient_nsmul_eq_zero]

variable {B}

/-- A subgroup of the central third lower-central term is an ideal. -/
def gammaThreeKernelIdeal
    (hclass : lowerCentralSeries ℤ B 3 = ⊥)
    {A : Type*} [AddCommGroup A]
    (f : lowerCentralSeries ℤ B 2 →+ A) : LieIdeal ℤ B where
  toSubmodule := (LinearMap.ker f.toIntLinearMap).map
    (lowerCentralSeries ℤ B 2).subtype
  lie_mem := by
    rintro x y ⟨z, hz, rfl⟩
    refine ⟨0, LinearMap.mem_ker.mpr ?_, ?_⟩
    · exact map_zero f
    have hxy : ⁅x, (z : B)⁆ ∈ lowerCentralSeries ℤ B 3 := by
      rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) z.property
    rw [hclass] at hxy
    change (0 : B) = ⁅x, (z : B)⁆
    exact hxy.symm

theorem mem_gammaThreeKernelIdeal_iff
    (hclass : lowerCentralSeries ℤ B 3 = ⊥)
    {A : Type*} [AddCommGroup A]
    (f : lowerCentralSeries ℤ B 2 →+ A) (x : B) :
    x ∈ gammaThreeKernelIdeal hclass f ↔
      ∃ z : lowerCentralSeries ℤ B 2, f z = 0 ∧ (z : B) = x := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, LinearMap.mem_ker.mp hz, hzx⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, LinearMap.mem_ker.mpr hz, rfl⟩

theorem gammaThreeKernelIdeal_le
    (hclass : lowerCentralSeries ℤ B 3 = ⊥)
    {A : Type*} [AddCommGroup A]
    (f : lowerCentralSeries ℤ B 2 →+ A) :
    gammaThreeKernelIdeal hclass f ≤ lowerCentralSeries ℤ B 2 := by
  rintro x ⟨z, -, rfl⟩
  exact z.property

end LieRings.DegreeFive

namespace LieRings.DegreeFive

universe u

/-- The external fact `2δ₄ ⊆ γ₄`, in the elementwise form used by the reduction. -/
def TwoDeltaFourProperty : Prop :=
  ∀ (M : Type u) [LieRing M] (x : M),
    x ∈ dimensionSubring ℤ M 4 → 2 • x ∈ lowerCentralSeries ℤ M 3

/-- A bundled existential assertion of exactly the reduced counterexample requested by the
standing reduction. -/
def ReducedCounterexampleExists : Prop :=
  ∃ (D : Type u) (instD : LieRing D),
    letI : LieRing D := instD
    ∃ (_R : StandingReductionData D) (d : D),
      d ∈ dimensionSubring ℤ D 5 ∧ d ≠ 0

theorem reduced_of_finite_classThree_counterexample
    (hTwo : TwoDeltaFourProperty.{u})
    (B : Type u) [LieRing B] [Module.Finite ℤ B]
    (hclass : lowerCentralSeries ℤ B 3 = ⊥)
    (b : B) (hb : b ∈ dimensionSubring ℤ B 5) (hb0 : b ≠ 0) :
    ReducedCounterexampleExists.{u} := by
  have hbThree : b ∈ lowerCentralSeries ℤ B 2 := by
    rw [← dimensionSubring_three_eq_lowerCentralSeries_two B]
    exact dimensionSubring_antitone ℤ B (by omega) hb
  have h2b : 2 • b = 0 := by
    have hmem := hTwo B b (dimensionSubring_antitone ℤ B (by omega) hb)
    rw [hclass] at hmem
    simpa using hmem
  obtain ⟨k, hbk⟩ := exists_two_pow_not_mem hb0 h2b
  let J : LieIdeal ℤ B := multipleIdeal B (2 ^ k : ℕ)
  let C : Type u := B ⧸ J
  let q : B →ₗ⁅ℤ⁆ C := UEA.lieIdealQuotientMk ℤ B J
  let c : C := q b
  have hq : Function.Surjective q := by
    intro x
    exact Submodule.Quotient.mk_surjective J.toSubmodule x
  have hc0 : c ≠ 0 := by
    intro hc
    have hbJ : b ∈ J :=
      (LieSubmodule.Quotient.mk_eq_zero' (N := J)).mp hc
    obtain ⟨y, hy⟩ := (mem_multipleIdeal_iff B (2 ^ k : ℕ) b).mp hbJ
    exact hbk ⟨y, hy⟩
  have hcDelta : c ∈ dimensionSubring ℤ C 5 :=
    map_mem_dimensionSubring ℤ B C q 5 hb
  have hcThree : c ∈ lowerCentralSeries ℤ C 2 := by
    change c ∈ LieModule.lowerCentralSeries ℤ C C 2
    rw [← LieIdeal.lowerCentralSeries_map_eq 2 hq]
    exact LieIdeal.mem_map hbThree
  have hCclass : lowerCentralSeries ℤ C 3 = ⊥ := by
    change LieModule.lowerCentralSeries ℤ C C 3 = ⊥
    have hclass' : LieModule.lowerCentralSeries ℤ B B 3 = ⊥ := hclass
    rw [← LieIdeal.lowerCentralSeries_map_eq 3 hq, hclass']
    simp
  letI : Module.Finite ℤ C :=
    Module.Finite.quotient ℤ J.toSubmodule
  letI : Finite C := by
    dsimp only [C, J]
    exact multipleQuotient_finite B (2 ^ k) (by positivity)
  have hCp : IsPGroup 2 (Multiplicative C) := by
    dsimp only [C, J]
    exact multipleQuotient_isPGroup_two B k
  let G : Type u := lowerCentralSeries ℤ C 2
  let cG : G := ⟨c, hcThree⟩
  have hGp : IsPGroup 2 (Multiplicative G) := by
    exact hCp.of_injective
      (lowerCentralSeries ℤ C 2).subtype.toAddMonoidHom.toMultiplicative
      Subtype.coe_injective
  obtain ⟨e, f, hf, hfc⟩ := exists_cyclic_detector (G := G) hGp (c := cG) (by
    intro h
    exact hc0 (congrArg Subtype.val h))
  let K : LieIdeal ℤ C := gammaThreeKernelIdeal hCclass f
  let D : Type u := C ⧸ K
  let r : C →ₗ⁅ℤ⁆ D := UEA.lieIdealQuotientMk ℤ C K
  let d : D := r c
  have hr : Function.Surjective r := by
    intro x
    exact Submodule.Quotient.mk_surjective K.toSubmodule x
  have hd0 : d ≠ 0 := by
    intro hd
    have hcK : c ∈ K :=
      (LieSubmodule.Quotient.mk_eq_zero' (N := K)).mp hd
    obtain ⟨z, hz, hzc⟩ :=
      (mem_gammaThreeKernelIdeal_iff hCclass f c).mp hcK
    have hzcG : z = cG := Subtype.ext hzc
    exact hfc (hzcG ▸ hz)
  have hdDelta : d ∈ dimensionSubring ℤ D 5 :=
    map_mem_dimensionSubring ℤ C D r 5 hcDelta
  have hDclass : lowerCentralSeries ℤ D 3 = ⊥ := by
    change LieModule.lowerCentralSeries ℤ D D 3 = ⊥
    have hCclass' : LieModule.lowerCentralSeries ℤ C C 3 = ⊥ := hCclass
    rw [← LieIdeal.lowerCentralSeries_map_eq 3 hr, hCclass']
    rw [LieIdeal.map_eq_bot_iff]
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    exact LinearMap.mem_ker.mpr (map_zero r)
  letI : Finite D := Finite.of_surjective r hr
  have hDp : IsPGroup 2 (Multiplicative D) :=
    hCp.of_surjective r.toAddMonoidHom.toMultiplicative hr
  have hdThree : d ∈ lowerCentralSeries ℤ D 2 := by
    change d ∈ LieModule.lowerCentralSeries ℤ D D 2
    rw [← LieIdeal.lowerCentralSeries_map_eq 2 hr]
    exact LieIdeal.mem_map hcThree
  let H : Type u := lowerCentralSeries ℤ D 2
  obtain ⟨g₀, hg₀⟩ := hf 1
  have hgen : r (g₀ : C) ∈ lowerCentralSeries ℤ D 2 := by
    apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := r) 2)
    exact LieIdeal.mem_map g₀.property
  let gen : H := ⟨r (g₀ : C), hgen⟩
  have hHcyclic : IsAddCyclic H := by
    refine ⟨gen, ?_⟩
    intro z
    have hzMap : (z : D) ∈
        (lowerCentralSeries ℤ C 2).map r := by
      rw [LieIdeal.lowerCentralSeries_map_eq 2 hr]
      exact z.property
    obtain ⟨g, hgr⟩ := LieIdeal.mem_map_of_surjective hr hzMap
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective (f g)
    have hker : f (g - n • g₀) = 0 := by
      calc
        f (g - n • g₀) = f g - f (n • g₀) := f.map_sub g (n • g₀)
        _ = f g - n • f g₀ := by rw [map_zsmul]
        _ = f g - n := by rw [hg₀, zsmul_one]
        _ = 0 := sub_eq_zero.mpr hn.symm
    have hmemK : ((g - n • g₀ : G) : C) ∈ K := by
      apply (mem_gammaThreeKernelIdeal_iff hCclass f _).mpr
      exact ⟨g - n • g₀, hker, rfl⟩
    have hrzero : r ((g - n • g₀ : G) : C) = 0 :=
      (LieSubmodule.Quotient.mk_eq_zero' (N := K)).mpr hmemK
    refine ⟨n, Subtype.ext ?_⟩
    change n • r (g₀ : C) = (z : D)
    rw [← hgr]
    have hcoe : ((g - n • g₀ : G) : C) =
        (g : C) - n • (g₀ : C) := rfl
    rw [hcoe, map_sub, map_zsmul] at hrzero
    exact sub_eq_zero.mp hrzero |>.symm
  have hHp : IsPGroup 2 (Multiplicative H) := by
    exact hDp.of_injective
      (lowerCentralSeries ℤ D 2).subtype.toAddMonoidHom.toMultiplicative
      Subtype.coe_injective
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, hcard⟩ := hHp.exists_card_eq
  let gammaEquiv : lowerCentralSeries ℤ D 2 ≃+ ZMod (2 ^ a) :=
    (zmodAddCyclicAddEquiv hHcyclic).symm.trans
      (ZMod.ringEquivCongr hcard).toAddEquiv
  let R : StandingReductionData D :=
    { finite_inst := inferInstance
      two_group := hDp
      classThree := hDclass
      gammaThreeExponent := a
      gammaThreeEquiv := gammaEquiv }
  exact ⟨D, inferInstance, R, d, hdDelta, hd0⟩

/-- There is no finite-module class-three counterexample once the already proved standing
reduction theorem is invoked. -/
theorem not_finite_classThree_counterexample
    (hTwo : TwoDeltaFourProperty.{u})
    (B : Type u) [LieRing B] [Module.Finite ℤ B]
    (hclass : lowerCentralSeries ℤ B 3 = ⊥)
    (b : B) (hb : b ∈ dimensionSubring ℤ B 5) : b = 0 := by
  by_contra hb0
  obtain ⟨D, instD, R, d, hd, hd0⟩ :=
    reduced_of_finite_classThree_counterexample hTwo B hclass b hb hb0
  letI : LieRing D := instD
  have hvanish := R.dimensionSubring_five_eq_bot
  rw [hvanish] at hd
  exact hd0 (by simpa using hd)

/-- The finitary part of the reduction, isolated from the subsequent quotient argument.

The intended proof takes `A` to be a finitely generated Lie subring containing a finite
enveloping-algebra witness for `x ∈ δ₅(L)`.  Only finiteness of `A/γ₄(A)` as a
`Z`-module is needed below. -/
def FiniteWitnessProperty (L : Type u) [LieRing L] : Prop :=
  ∀ (x : L), x ∈ dimensionSubring ℤ L 5 →
    ∃ (A : Type u) (instA : LieRing A),
      letI : LieRing A := instA
      ∃ (f : A →ₗ⁅ℤ⁆ L) (a : A),
        Function.Injective f ∧ f a = x ∧
        a ∈ dimensionSubring ℤ A 5 ∧
        Nonempty (Module.Finite ℤ (ClassThreeQuotient A))

/-- Contrapositive form of the reduction: a counterexample, together with its finite witness,
produces a finite `2`-primary class-three counterexample with cyclic third lower-central term. -/
theorem reducedCounterexample_of_counterexample
    (L : Type u) [LieRing L]
    (hTwo : TwoDeltaFourProperty.{u})
    (hFinite : FiniteWitnessProperty L)
    (x : L) (hx : x ∈ dimensionSubring ℤ L 5)
    (hxGamma : x ∉ lowerCentralSeries ℤ L 3) :
    ReducedCounterexampleExists.{u} := by
  obtain ⟨A, instA, f, a, hf, hfa, ha, hAfin⟩ := hFinite x hx
  letI : LieRing A := instA
  have haGamma : a ∉ lowerCentralSeries ℤ A 3 := by
    intro haGamma
    have hmap : f a ∈ lowerCentralSeries ℤ L 3 :=
      (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := f) 3)
        (LieIdeal.mem_map haGamma)
    exact hxGamma (hfa ▸ hmap)
  let B : Type u := ClassThreeQuotient A
  let q : A →ₗ⁅ℤ⁆ B :=
    UEA.lieIdealQuotientMk ℤ A (lowerCentralSeries ℤ A 3)
  let b : B := q a
  letI : Module.Finite ℤ B := hAfin.some
  have hb : b ∈ dimensionSubring ℤ B 5 :=
    map_mem_dimensionSubring ℤ A B q 5 ha
  have hb0 : b ≠ 0 := by
    intro hb0
    exact haGamma ((LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ A 3)).mp hb0)
  exact reduced_of_finite_classThree_counterexample hTwo B
    (classThreeQuotient_lowerCentralSeries_three_eq_bot A) b hb hb0

/-- Once finite witnesses are available, the standing-reduction theorem implies the global
degree-five inclusion.  The only external dimension-series input is `2δ₄ ⊆ γ₄`. -/
theorem dimensionSubring_five_le_lowerCentralSeries_three_of_finiteWitness
    (L : Type u) [LieRing L]
    (hTwo : TwoDeltaFourProperty.{u})
    (hFinite : FiniteWitnessProperty L) :
    dimensionSubring ℤ L 5 ≤ lowerCentralSeries ℤ L 3 := by
  intro x hx
  by_contra hxGamma
  obtain ⟨A, instA, f, a, hf, hfa, ha, hAfin⟩ := hFinite x hx
  letI : LieRing A := instA
  have haGamma : a ∉ lowerCentralSeries ℤ A 3 := by
    intro haGamma
    have hmap : f a ∈ lowerCentralSeries ℤ L 3 :=
      (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := f) 3)
        (LieIdeal.mem_map haGamma)
    exact hxGamma (hfa ▸ hmap)
  let B : Type u := ClassThreeQuotient A
  let q : A →ₗ⁅ℤ⁆ B :=
    UEA.lieIdealQuotientMk ℤ A (lowerCentralSeries ℤ A 3)
  let b : B := q a
  letI : Module.Finite ℤ B := hAfin.some
  have hb : b ∈ dimensionSubring ℤ B 5 :=
    map_mem_dimensionSubring ℤ A B q 5 ha
  have hb0 : b ≠ 0 := by
    intro hb0
    exact haGamma ((LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ A 3)).mp hb0)
  exact hb0 (not_finite_classThree_counterexample hTwo B
    (classThreeQuotient_lowerCentralSeries_three_eq_bot A) b hb)

end LieRings.DegreeFive
