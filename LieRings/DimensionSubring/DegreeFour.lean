import LieRings.DimensionSubring.DegreeFive.FiniteWitnessReduction
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Int.GCD

/-!
# The fourth Lie dimension quotient

This file isolates the final, elementary step in the Bartholdi--Passi degree-four
argument.  The preceding normal-form argument produces coefficients `a i j`, elements
`x i`, and decompositions

`W i = e i • y i + z i`,

where `e i • x i` and `y i` belong to `γ₂`, and `z i` belongs to `γ₃`.  The skew
coefficient identity says that twice the represented element is the sum of the brackets
`[x i, W i]`.  Every summand then belongs to `γ₄`.
-/

namespace LieRings

universe u v

namespace DegreeFour

noncomputable section

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

variable {L : Type u} [LieRing L]
variable {ι : Type v} [Fintype ι] [LinearOrder ι]

local notation "CanonicalFreeLie" => DegreeFive.CanonicalFreeLie
local notation "canonicalFreeLieEvaluation" =>
  DegreeFive.canonicalFreeLieEvaluation

/-- Free-presentation data attached to an element of the fourth dimension subring. -/
structure FreeDimensionFourWitness (a : L) where
  lieLift : CanonicalFreeLie L
  highWord : UEA ℤ (CanonicalFreeLie L)
  evaluates : canonicalFreeLieEvaluation L lieLift = a
  highWord_mem : highWord ∈ UEA.augmentationIdeal ℤ (CanonicalFreeLie L) ^ 4
  relationDifference :
    UniversalEnvelopingAlgebra.ι ℤ lieLift - highWord ∈
      DegreeFive.rightRelationSpan ℤ (CanonicalFreeLie L)
        (DegreeFive.CanonicalLieRelationsIdeal L)

/-- A degree-four witness may be chosen with its Lie lift in `γ₂` of the free Lie ring. -/
theorem exists_freeDimensionFourWitness_gammaTwo
    (a : L) (ha : a ∈ dimensionSubring ℤ L 4) :
    ∃ w : FreeDimensionFourWitness a,
      w.lieLift ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 1 := by
  have haTwo : a ∈ dimensionSubring ℤ L 2 :=
    dimensionSubring_antitone ℤ L (by omega) ha
  have haGamma : a ∈ lowerCentralSeries ℤ L 1 := by
    rw [← dimensionSubring_two_eq_lowerCentralSeries_one ℤ L]
    exact haTwo
  have haMap : a ∈
      (lowerCentralSeries ℤ (CanonicalFreeLie L) 1).map
        (canonicalFreeLieEvaluation L) := by
    rw [LieIdeal.lowerCentralSeries_map_eq 1
      (DegreeFive.canonicalFreeLieEvaluation_surjective L)]
    exact haGamma
  obtain ⟨f, hfEval⟩ := LieIdeal.mem_map_of_surjective
    (I := lowerCentralSeries ℤ (CanonicalFreeLie L) 1)
    (DegreeFive.canonicalFreeLieEvaluation_surjective L) haMap
  have ha' : UniversalEnvelopingAlgebra.ι ℤ a ∈
      UEA.augmentationIdeal ℤ L ^ 4 :=
    (mem_dimensionSubring ℤ L).mp ha
  obtain ⟨t, htHigh, htEval⟩ :=
    UEA.exists_mem_augmentationIdeal_pow_succ_of_surjective ℤ
      (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L)
      (DegreeFive.canonicalFreeLieEvaluation_surjective L) 3 ha'
  have hdiffZero :
      UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L)
          (UniversalEnvelopingAlgebra.ι ℤ (f : CanonicalFreeLie L) - t) = 0 := by
    rw [map_sub, UEA.map_ι, hfEval, htEval, sub_self]
  have hdiff :=
    (DegreeFive.mem_kernel_canonical_uea_evaluation_iff_relation_sum L
      (UniversalEnvelopingAlgebra.ι ℤ (f : CanonicalFreeLie L) - t)).mp hdiffZero
  exact ⟨⟨(f : CanonicalFreeLie L), t, hfEval, htHigh, hdiff⟩, f.property⟩

/-- Using the integral theorem `delta_3 = gamma_3`, the lift in a degree-four
witness can in fact be chosen in free `gamma_3`.  This stronger choice is the
one needed by the degree-three Dynkin projection. -/
theorem FreeDimensionFourWitness.exists_relation_finsupp
    {a : L} (w : FreeDimensionFourWitness a) :
    ∃ c : (DegreeFive.CanonicalLieRelationsIdeal L ×
        UEA ℤ (CanonicalFreeLie L)) →₀ ℤ,
      c.sum (fun p n ↦ n •
        (UniversalEnvelopingAlgebra.ι ℤ
          (p.1 : CanonicalFreeLie L) * p.2)) =
        UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord := by
  exact DegreeFive.exists_relation_finsupp_of_mem_rightRelationSpan ℤ
    (CanonicalFreeLie L) (DegreeFive.CanonicalLieRelationsIdeal L)
      w.relationDifference

/-- Passi's relation collection with the multiplier on the left. -/
private theorem exists_relation_on_right_finsupp
    {F : Type*} [LieRing F] (R : LieIdeal ℤ F) {z : UEA ℤ F}
    (hz : z ∈ UEA.idealOfLieIdeal ℤ F R) :
    ∃ c : (UEA ℤ F × R) →₀ ℤ,
      c.sum (fun p n ↦ n •
        (p.1 * UniversalEnvelopingAlgebra.ι ℤ (p.2 : F))) = z := by
  let term : UEA ℤ F × R → UEA ℤ F := fun p ↦
    p.1 * UniversalEnvelopingAlgebra.ι ℤ (p.2 : F)
  let S : Submodule ℤ (UEA ℤ F) := Submodule.span ℤ (Set.range term)
  have hterm (u : UEA ℤ F) (r : R) : term (u, r) ∈ S :=
    Submodule.subset_span ⟨(u, r), rfl⟩
  have hleft (a : UEA ℤ F) : ∀ {x : UEA ℤ F}, x ∈ S → a * x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨⟨u, r⟩, rfl⟩ := hx
        change a * (u * UniversalEnvelopingAlgebra.ι ℤ (r : F)) ∈ S
        rw [← mul_assoc]
        exact hterm (a * u) r
    | zero => simp
    | add x y _ _ hx hy =>
        rw [mul_add]
        exact S.add_mem hx hy
    | smul n x _ hx =>
        rw [mul_smul_comm]
        exact S.smul_mem n hx
  have hright (a : UEA ℤ F) : ∀ {x : UEA ℤ F}, x ∈ S → x * a ∈ S := by
    induction a using UEA.induction ℤ F with
    | algebraMap n =>
        intro x hx
        rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
        exact S.smul_mem n hx
    | ι y =>
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
            obtain ⟨⟨u, r⟩, rfl⟩ := hx
            let ry : R := ⟨⁅(r : F), y⁆, by
              have hyr : ⁅y, (r : F)⁆ ∈ R := R.lie_mem r.property
              simpa only [lie_skew] using R.neg_mem hyr⟩
            have hcomm :
                UniversalEnvelopingAlgebra.ι ℤ ⁅(r : F), y⁆ =
                  UniversalEnvelopingAlgebra.ι ℤ (r : F) *
                      UniversalEnvelopingAlgebra.ι ℤ y -
                    UniversalEnvelopingAlgebra.ι ℤ y *
                      UniversalEnvelopingAlgebra.ι ℤ (r : F) :=
              LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℤ) (r : F) y
            have hid :
                (u * UniversalEnvelopingAlgebra.ι ℤ (r : F)) *
                    UniversalEnvelopingAlgebra.ι ℤ y =
                  (u * UniversalEnvelopingAlgebra.ι ℤ y) *
                      UniversalEnvelopingAlgebra.ι ℤ (r : F) +
                    u * UniversalEnvelopingAlgebra.ι ℤ (ry : F) := by
              change _ = _ + u * UniversalEnvelopingAlgebra.ι ℤ ⁅(r : F), y⁆
              rw [hcomm]
              noncomm_ring
            rw [hid]
            exact S.add_mem (hterm (u * UniversalEnvelopingAlgebra.ι ℤ y) r)
              (hterm u ry)
        | zero => simp
        | add x y _ _ hx hy =>
            rw [add_mul]
            exact S.add_mem hx hy
        | smul n x _ hx =>
            rw [smul_mul_assoc]
            exact S.smul_mem n hx
    | mul a b ha hb =>
        intro x hx
        rw [← mul_assoc]
        exact hb (ha hx)
    | add a b ha hb =>
        intro x hx
        rw [mul_add]
        exact S.add_mem (ha hx) (hb hx)
  have hzS : z ∈ S := by
    change z ∈ TwoSidedIdeal.span
      (Set.range fun r : R ↦ UniversalEnvelopingAlgebra.ι ℤ (r : F)) at hz
    induction hz using TwoSidedIdeal.span_induction with
    | mem x hx =>
        obtain ⟨r, rfl⟩ := hx
        simpa [term] using hterm 1 r
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | neg x _ hx => exact S.neg_mem hx
    | left_absorb a x _ hx => exact hleft a hx
    | right_absorb a x _ hx => exact hright a hx
  change z ∈ Submodule.span ℤ (Set.range term) at hzS
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hzS
  exact ⟨c, by simpa [term] using hc⟩

/-- Passi's normalized degree-four lift: all relation multipliers have zero
augmentation and occur on the left. -/
private structure NormalizedDimensionFourWitness (b : L) where
  lieLift : CanonicalFreeLie L
  highWord : UEA ℤ (CanonicalFreeLie L)
  relationTerms :
    (UEA ℤ (CanonicalFreeLie L) ×
      DegreeFive.CanonicalLieRelationsIdeal L) →₀ ℤ
  evaluates : canonicalFreeLieEvaluation L lieLift = b
  highWord_mem :
    highWord ∈ UEA.augmentationIdeal ℤ (CanonicalFreeLie L) ^ 4
  multiplier_mem : ∀ p ∈ relationTerms.support,
    p.1 - algebraMap ℤ (UEA ℤ (CanonicalFreeLie L))
        (UEA.augmentation ℤ (CanonicalFreeLie L) p.1) ∈
      UEA.augmentationIdeal ℤ (CanonicalFreeLie L)
  relationEquation :
    relationTerms.sum (fun p n ↦ n •
      ((p.1 - algebraMap ℤ (UEA ℤ (CanonicalFreeLie L))
          (UEA.augmentation ℤ (CanonicalFreeLie L) p.1)) *
        UniversalEnvelopingAlgebra.ι ℤ
          (p.2 : CanonicalFreeLie L))) =
      UniversalEnvelopingAlgebra.ι ℤ lieLift - highWord
  lieLift_mem_gammaTwo :
    lieLift ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 1

private theorem exists_normalizedDimensionFourWitness
    (b : L) (hb : b ∈ dimensionSubring ℤ L 4) :
    Nonempty (NormalizedDimensionFourWitness b) := by
  classical
  let R := DegreeFive.CanonicalLieRelationsIdeal L
  obtain ⟨w, hwGamma⟩ := exists_freeDimensionFourWitness_gammaTwo b hb
  have hrelIdeal :
      UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord ∈
        UEA.idealOfLieIdeal ℤ (CanonicalFreeLie L) R := by
    rw [DegreeFive.idealOfLieIdeal_eq_rightRelationIdeal]
    exact w.relationDifference
  obtain ⟨c, hc⟩ := exists_relation_on_right_finsupp R hrelIdeal
  let multiplier : UEA ℤ (CanonicalFreeLie L) × R →
      UEA ℤ (CanonicalFreeLie L) := fun p ↦
    p.1 - algebraMap ℤ (UEA ℤ (CanonicalFreeLie L))
      (UEA.augmentation ℤ (CanonicalFreeLie L) p.1)
  let correction : CanonicalFreeLie L := c.sum fun p n ↦
    (n * UEA.augmentation ℤ (CanonicalFreeLie L) p.1) •
      (p.2 : CanonicalFreeLie L)
  let v : CanonicalFreeLie L := w.lieLift - correction
  have hmultiplier
      (p : UEA ℤ (CanonicalFreeLie L) × R) :
      multiplier p ∈ UEA.augmentationIdeal ℤ (CanonicalFreeLie L) := by
    rw [UEA.mem_augmentationIdeal]
    change UEA.augmentation ℤ (CanonicalFreeLie L)
      (p.1 - algebraMap ℤ (UEA ℤ (CanonicalFreeLie L))
        (UEA.augmentation ℤ (CanonicalFreeLie L) p.1)) = 0
    rw [map_sub, UEA.augmentation_algebraMap, sub_self]
  have hcorrection_iota :
      UniversalEnvelopingAlgebra.ι ℤ correction =
        c.sum (fun p n ↦ n •
          (algebraMap ℤ (UEA ℤ (CanonicalFreeLie L))
              (UEA.augmentation ℤ (CanonicalFreeLie L) p.1) *
            UniversalEnvelopingAlgebra.ι ℤ
              (p.2 : CanonicalFreeLie L))) := by
    unfold correction
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro p hp
    rw [map_zsmul]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    module
  have hequation :
      c.sum (fun p n ↦ n •
        (multiplier p * UniversalEnvelopingAlgebra.ι ℤ
          (p.2 : CanonicalFreeLie L))) =
        UniversalEnvelopingAlgebra.ι ℤ v - w.highWord := by
    calc
      c.sum (fun p n ↦ n •
          (multiplier p * UniversalEnvelopingAlgebra.ι ℤ
            (p.2 : CanonicalFreeLie L))) =
          c.sum (fun p n ↦ n •
            (p.1 * UniversalEnvelopingAlgebra.ι ℤ
              (p.2 : CanonicalFreeLie L))) -
          c.sum (fun p n ↦ n •
            (algebraMap ℤ (UEA ℤ (CanonicalFreeLie L))
                (UEA.augmentation ℤ (CanonicalFreeLie L) p.1) *
              UniversalEnvelopingAlgebra.ι ℤ
                (p.2 : CanonicalFreeLie L))) := by
        unfold Finsupp.sum
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        simp only [multiplier]
        rw [sub_mul, smul_sub]
      _ = (UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord) -
          UniversalEnvelopingAlgebra.ι ℤ correction := by
        rw [hc, hcorrection_iota]
      _ = UniversalEnvelopingAlgebra.ι ℤ v - w.highWord := by
        simp only [v, map_sub]
        abel
  have hcorrection_eval : canonicalFreeLieEvaluation L correction = 0 := by
    unfold correction
    rw [map_finsuppSum]
    apply Finset.sum_eq_zero
    intro p hp
    dsimp
    rw [map_zsmul, show canonicalFreeLieEvaluation L
        (p.2 : CanonicalFreeLie L) = 0
      from p.2.property, smul_zero]
  have hveval : canonicalFreeLieEvaluation L v = b := by
    change canonicalFreeLieEvaluation L (w.lieLift - correction) = b
    rw [map_sub, w.evaluates, hcorrection_eval, sub_zero]
  let I := UEA.augmentationIdeal ℤ (CanonicalFreeLie L)
  have hrelationHigh : c.sum (fun p n ↦ n •
      (multiplier p * UniversalEnvelopingAlgebra.ι ℤ
        (p.2 : CanonicalFreeLie L))) ∈ I ^ 2 := by
    apply Submodule.sum_mem
    intro p hp
    apply zsmul_mem
    have hmul := Ideal.mul_mem_mul (hmultiplier p)
      (UEA.ι_mem_augmentationIdeal ℤ (CanonicalFreeLie L)
        (p.2 : CanonicalFreeLie L))
    simpa only [show (2 : ℕ) = 1 + 1 by rfl, Submodule.pow_succ,
      Submodule.pow_one, Submodule.pow_zero, Submodule.one_mul] using hmul
  have hhighTwo : w.highWord ∈ I ^ 2 :=
    Ideal.pow_le_pow_right (I := I) (by omega) w.highWord_mem
  have hiota : UniversalEnvelopingAlgebra.ι ℤ v ∈ I ^ 2 := by
    have hvEq : UniversalEnvelopingAlgebra.ι ℤ v =
        c.sum (fun p n ↦ n •
          (multiplier p * UniversalEnvelopingAlgebra.ι ℤ
            (p.2 : CanonicalFreeLie L))) +
          w.highWord := by
      rw [hequation]
      abel
    rw [hvEq]
    exact (I ^ 2).add_mem hrelationHigh hhighTwo
  have hvGamma : v ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 1 := by
    have hvDelta : v ∈ dimensionSubring ℤ (CanonicalFreeLie L) 2 :=
      (mem_dimensionSubring ℤ (CanonicalFreeLie L)).mpr hiota
    rw [← FreeLieDimension.dimensionSubring_succ_eq_lowerCentralSeries L 1]
    simpa using hvDelta
  exact ⟨{
    lieLift := v
    highWord := w.highWord
    relationTerms := c
    evaluates := hveval
    highWord_mem := w.highWord_mem
    multiplier_mem := fun p hp ↦ hmultiplier p
    relationEquation := hequation
    lieLift_mem_gammaTwo := hvGamma }⟩

/-- The weight-two element in the Bartholdi--Passi normal form. -/
def normalFormValue (x : ι → L) (a : ι → ι → ℤ) : L :=
  ∑ i, ∑ j, if j < i then a i j • ⁅x i, x j⁆ else 0

/-- The coefficient of `x j` obtained by collecting the normal form on the left at `x i`. -/
def normalFormRow (x : ι → L) (a : ι → ι → ℤ) (i : ι) : L :=
  (∑ j, if j < i then a i j • x j else 0) -
    ∑ j, if i < j then a j i • x j else 0

/-- The elementary skew-collection identity used in the Bartholdi--Passi corollary. -/
theorem sum_lie_normalFormRow_eq_two_smul
    (x : ι → L) (a : ι → ι → ℤ) :
    (∑ i, ⁅x i, normalFormRow x a i⁆) =
      (2 : ℤ) • normalFormValue x a := by
  classical
  simp only [normalFormRow, normalFormValue, lie_sub, lie_sum, apply_ite,
    lie_zero, lie_zsmul, Finset.sum_sub_distrib, Finset.smul_sum,
    smul_zero]
  rw [show (∑ j, ∑ i, if j < i then a i j • ⁅x j, x i⁆ else 0) =
      ∑ i, ∑ j, if j < i then a i j • ⁅x j, x i⁆ else 0 by
    rw [Finset.sum_comm]]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j < i
  · simp only [hji, if_true]
    rw [show ⁅x j, x i⁆ = -⁅x i, x j⁆ from (lie_skew (x j) (x i)).symm]
    module
  · simp only [hji, if_false, sub_zero]

/-- Membership form of the elementary final step of Corollary 4.3 of
Bartholdi--Passi.  All difficult information is concentrated in the normal-form hypotheses. -/
theorem two_smul_normalFormValue_mem_lowerCentralSeries_three
    (x : ι → L) (a : ι → ι → ℤ) (e : ι → ℤ)
    (y z : ι → L)
    (hrow : ∀ i, normalFormRow x a i = e i • y i + z i)
    (hx : ∀ i, e i • x i ∈ lowerCentralSeries ℤ L 1)
    (hy : ∀ i, y i ∈ lowerCentralSeries ℤ L 1)
    (hz : ∀ i, z i ∈ lowerCentralSeries ℤ L 2) :
    (2 : ℤ) • normalFormValue x a ∈ lowerCentralSeries ℤ L 3 := by
  rw [← sum_lie_normalFormRow_eq_two_smul]
  apply Submodule.sum_mem
  intro i hi
  rw [hrow i, lie_add, lie_zsmul, ← zsmul_lie]
  apply (lowerCentralSeries ℤ L 3).add_mem
  · apply bracket_dimensionSubring_le_lowerCentralSeries ℤ L 1 1
    exact LieSubmodule.lie_mem_lie
      (lowerCentralSeries_le_dimensionSubring ℤ L 1 (hx i))
      (lowerCentralSeries_le_dimensionSubring ℤ L 1 (hy i))
  · change ⁅x i, z i⁆ ∈ LieModule.lowerCentralSeries ℤ L L (2 + 1)
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (hz i)

/-- A packaged Bartholdi--Passi normal form for an element, modulo `γ₄`. -/
structure NormalFormCertificate (b : L) where
  ι : Type v
  fintype_ι : Fintype ι
  linearOrder_ι : LinearOrder ι
  x : ι → L
  a : ι → ι → ℤ
  e : ι → ℤ
  y : ι → L
  z : ι → L
  represents : b - normalFormValue x a ∈ lowerCentralSeries ℤ L 3
  row_decomposition : ∀ i, normalFormRow x a i = e i • y i + z i
  head_mem_gammaTwo : ∀ i, e i • x i ∈ lowerCentralSeries ℤ L 1
  y_mem_gammaTwo : ∀ i, y i ∈ lowerCentralSeries ℤ L 1
  z_mem_gammaThree : ∀ i, z i ∈ lowerCentralSeries ℤ L 2

@[simp]
theorem normalFormValue_map
    {A : Type*} [LieRing A] (f : L →ₗ⁅ℤ⁆ A)
    (x : ι → L) (a : ι → ι → ℤ) :
    normalFormValue (fun i ↦ f (x i)) a = f (normalFormValue x a) := by
  classical
  simp only [normalFormValue, map_sum, apply_ite, map_zero, map_zsmul,
    LieHom.map_lie]

@[simp]
theorem normalFormRow_map
    {A : Type*} [LieRing A] (f : L →ₗ⁅ℤ⁆ A)
    (x : ι → L) (a : ι → ι → ℤ) (i : ι) :
    normalFormRow (fun j ↦ f (x j)) a i = f (normalFormRow x a i) := by
  classical
  simp only [normalFormRow, map_sub, map_sum, apply_ite, map_zsmul, map_zero]

/-- Normal-form certificates are functorial under Lie homomorphisms. -/
def NormalFormCertificate.map
    {A : Type*} [LieRing A] {b : L}
    (c : NormalFormCertificate b) (f : L →ₗ⁅ℤ⁆ A) :
    NormalFormCertificate (f b) := by
  letI : Fintype c.ι := c.fintype_ι
  letI : LinearOrder c.ι := c.linearOrder_ι
  refine
    { ι := c.ι
      fintype_ι := c.fintype_ι
      linearOrder_ι := c.linearOrder_ι
      x := fun i ↦ f (c.x i)
      a := c.a
      e := c.e
      y := fun i ↦ f (c.y i)
      z := fun i ↦ f (c.z i)
      represents := ?_
      row_decomposition := ?_
      head_mem_gammaTwo := ?_
      y_mem_gammaTwo := ?_
      z_mem_gammaThree := ?_ }
  · rw [normalFormValue_map, ← map_sub]
    apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := f) 3)
    exact LieIdeal.mem_map c.represents
  · intro i
    rw [normalFormRow_map, c.row_decomposition i, map_add, map_zsmul]
  · intro i
    rw [← map_zsmul]
    apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := f) 1)
    exact LieIdeal.mem_map (c.head_mem_gammaTwo i)
  · intro i
    apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := f) 1)
    exact LieIdeal.mem_map (c.y_mem_gammaTwo i)
  · intro i
    apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := f) 2)
    exact LieIdeal.mem_map (c.z_mem_gammaThree i)

/-- Every certified normal-form element has twice its value in `γ₄`. -/
theorem NormalFormCertificate.two_smul_mem_lowerCentralSeries_three
    {b : L} (c : NormalFormCertificate b) :
    (2 : ℤ) • b ∈ lowerCentralSeries ℤ L 3 := by
  letI : Fintype c.ι := c.fintype_ι
  letI : LinearOrder c.ι := c.linearOrder_ι
  have hnormal : (2 : ℤ) • normalFormValue c.x c.a ∈
      lowerCentralSeries ℤ L 3 :=
    two_smul_normalFormValue_mem_lowerCentralSeries_three
      c.x c.a c.e c.y c.z c.row_decomposition c.head_mem_gammaTwo
        c.y_mem_gammaTwo c.z_mem_gammaThree
  have herror : (2 : ℤ) • (b - normalFormValue c.x c.a) ∈
      lowerCentralSeries ℤ L 3 :=
    (lowerCentralSeries ℤ L 3).smul_mem (2 : ℤ) c.represents
  convert (lowerCentralSeries ℤ L 3).add_mem herror hnormal using 1
  module

/-! ## Finite Bartholdi--Passi extraction target -/

section FiniteTarget

local notation "F" => CanonicalFreeLie L
local notation "ev" => canonicalFreeLieEvaluation L
local notation "Rel" => DegreeFive.CanonicalLieRelationsIdeal L

/-- Indices of the weight-one Smith basis of the canonical finite presentation. -/
abbrev FirstSmithIndex (A : Type u) [Finite A] :=
  DegreeFive.FreeLieExactBasisIndex A 1

/-- A weight-one generator in the collected Smith basis. -/
def firstSmithGenerator [Finite L] (i : FirstSmithIndex L) : CanonicalFreeLie L :=
  (DegreeFive.collectedHomogeneousBasis L L
    (canonicalFreeLieEvaluation L) 1 i : DegreeFive.freeLieExact L 1)

/-- Evaluation of a weight-one Smith generator. -/
def firstSmithValue [Finite L] (i : FirstSmithIndex L) : L :=
  canonicalFreeLieEvaluation L (firstSmithGenerator i)

/-- The positive diagonal of a weight-one Smith row. -/
def firstSmithDiagonal [Finite L] (i : FirstSmithIndex L) : ℤ :=
  DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 i

theorem collectedLeadingRelationBasis_one_eq [Finite L]
    (i : FirstSmithIndex L) :
    ((DegreeFive.collectedLeadingRelationBasis L L
      (canonicalFreeLieEvaluation L) 1 i :
        DegreeFive.homogeneousRelationLeading L L
          (canonicalFreeLieEvaluation L) 1) : DegreeFive.freeLieExact L 1) =
      firstSmithDiagonal i •
        DegreeFive.collectedHomogeneousBasis L L
          (canonicalFreeLieEvaluation L) 1 i := by
  unfold DegreeFive.collectedLeadingRelationBasis
    DegreeFive.collectedHomogeneousBasis firstSmithDiagonal
    DegreeFive.collectedDiagonal
  simp only [Module.Basis.reindex_apply]
  unfold DegreeFive.adaptedLeadingRelationBasis
    DegreeFive.adaptedHomogeneousBasis DegreeFive.adaptedDiagonal
  simp only [Equiv.symm_symm]
  rw [(DegreeFive.homogeneousPositiveSmithPresentation L L
    (canonicalFreeLieEvaluation L) 1).relation_eq]

theorem kernelRelation_firstSmithCoordinate_dvd [Finite L]
    (r : LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap)
    (i : FirstSmithIndex L) :
    firstSmithDiagonal i ∣
      (DegreeFive.collectedHomogeneousBasis L L
        (canonicalFreeLieEvaluation L) 1).repr
          (DegreeFive.freeLieExactProjection L 1 (r : CanonicalFreeLie L)) i := by
  let rf : DegreeFive.filteredPresentationRelations L L
      (canonicalFreeLieEvaluation L) 1 := ⟨r, r.property, by
    rw [FreeLieDimension.lieHigh_one]
    trivial⟩
  let lead : DegreeFive.homogeneousRelationLeading L L
      (canonicalFreeLieEvaluation L) 1 :=
    DegreeFive.filteredRelationLeading L L
      (canonicalFreeLieEvaluation L) 1 rf
  let c := (DegreeFive.collectedLeadingRelationBasis L L
    (canonicalFreeLieEvaluation L) 1).repr lead
  refine ⟨c i, ?_⟩
  have hexpand := (DegreeFive.collectedLeadingRelationBasis L L
    (canonicalFreeLieEvaluation L) 1).sum_repr lead
  have hexact := congrArg (fun x :
      DegreeFive.homogeneousRelationLeading L L
        (canonicalFreeLieEvaluation L) 1 ↦
      (x : DegreeFive.freeLieExact L 1)) hexpand
  change (DegreeFive.homogeneousRelationLeading L L
      (canonicalFreeLieEvaluation L) 1).subtype
        (∑ i, ((DegreeFive.collectedLeadingRelationBasis L L
          (canonicalFreeLieEvaluation L) 1).repr lead) i •
            DegreeFive.collectedLeadingRelationBasis L L
              (canonicalFreeLieEvaluation L) 1 i) =
      (lead : DegreeFive.freeLieExact L 1) at hexact
  rw [map_sum] at hexact
  change (∑ j, c j •
      (((DegreeFive.collectedLeadingRelationBasis L L
        (canonicalFreeLieEvaluation L) 1 j :
          DegreeFive.homogeneousRelationLeading L L
            (canonicalFreeLieEvaluation L) 1) :
              DegreeFive.freeLieExact L 1))) =
    (lead : DegreeFive.freeLieExact L 1) at hexact
  simp_rw [collectedLeadingRelationBasis_one_eq] at hexact
  have hrepr := congrArg
    (DegreeFive.collectedHomogeneousBasis L L
      (canonicalFreeLieEvaluation L) 1).repr hexact
  rw [map_sum] at hrepr
  simp only [map_zsmul,
    (DegreeFive.collectedHomogeneousBasis L L
      (canonicalFreeLieEvaluation L) 1).repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one] at hrepr
  have hi := congrArg (fun f : FirstSmithIndex L →₀ ℤ ↦ f i) hrepr
  simp [Finsupp.single_apply] at hi
  simpa [c, lead, rf, firstSmithDiagonal, mul_comm] using hi.symm

/-- Coefficient of the `i`th first Smith relation row in the linear head of a kernel
relation. -/
def firstSmithRelationCoefficient [Finite L]
    (r : LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap)
    (i : FirstSmithIndex L) : ℤ :=
  Classical.choose (kernelRelation_firstSmithCoordinate_dvd r i)

theorem firstSmithCoordinate_eq_diagonal_mul_relationCoefficient [Finite L]
    (r : LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap)
    (i : FirstSmithIndex L) :
    (DegreeFive.collectedHomogeneousBasis L L
        (canonicalFreeLieEvaluation L) 1).repr
          (DegreeFive.freeLieExactProjection L 1 (r : CanonicalFreeLie L)) i =
      firstSmithDiagonal i * firstSmithRelationCoefficient r i :=
  Classical.choose_spec (kernelRelation_firstSmithCoordinate_dvd r i)

/-- The part of a kernel relation above its linear Smith-row expansion. -/
def firstSmithRelationRemainder [Finite L]
    (r : LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap) :
    CanonicalFreeLie L :=
  (r : CanonicalFreeLie L) -
    ∑ i, firstSmithRelationCoefficient r i •
      (DegreeFive.collectedRelationRow L L
        (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L)

/-- After its first Smith rows are removed, a defining relation has free weight at least
two. -/
theorem firstSmithRelationRemainder_mem_lieHigh_two [Finite L]
    (r : LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap) :
    firstSmithRelationRemainder r ∈ FreeLieDimension.lieHigh L 2 := by
  classical
  apply DegreeFive.mem_lieHigh_succ_of_component_eq_zero L
  · unfold firstSmithRelationRemainder
    apply (FreeLieDimension.lieHigh L 1).sub_mem
    · rw [FreeLieDimension.lieHigh_one]
      trivial
    · apply Submodule.sum_mem
      intro i hi
      apply (FreeLieDimension.lieHigh L 1).smul_mem
      exact DegreeFive.collectedRelationRow_mem_lieHigh L L
        (canonicalFreeLieEvaluation L) 1 i
  · rw [firstSmithRelationRemainder, map_sub, map_sum]
    simp_rw [map_zsmul]
    have hrow (i : FirstSmithIndex L) :
        DegreeFive.freeLieLengthComponent L 1
            (DegreeFive.collectedRelationRow L L
              (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L) =
          firstSmithDiagonal i •
            (DegreeFive.collectedHomogeneousBasis L L
              (canonicalFreeLieEvaluation L) 1 i : DegreeFive.freeLieExact L 1) := by
      have h := DegreeFive.collectedRelationRow_head L L
        (canonicalFreeLieEvaluation L) 1 i
      exact congrArg Subtype.val h
    simp_rw [hrow]
    rw [sub_eq_zero]
    let B := DegreeFive.collectedHomogeneousBasis L L
      (canonicalFreeLieEvaluation L) 1
    have heq : DegreeFive.freeLieExactProjection L 1
        (r : CanonicalFreeLie L) =
        ∑ i, firstSmithRelationCoefficient r i •
          (firstSmithDiagonal i • B i) := by
      apply B.repr.injective
      ext i
      rw [map_sum]
      simp only [map_zsmul, B,
        (DegreeFive.collectedHomogeneousBasis L L
          (canonicalFreeLieEvaluation L) 1).repr_self,
        Finsupp.smul_single, Finsupp.sum_apply, smul_eq_mul]
      rw [firstSmithCoordinate_eq_diagonal_mul_relationCoefficient]
      simp [Finsupp.single_apply, mul_comm]
    change (DegreeFive.freeLieExactProjection L 1
      (r : CanonicalFreeLie L) : CanonicalFreeLie L) = _
    calc
      (DegreeFive.freeLieExactProjection L 1
          (r : CanonicalFreeLie L) : CanonicalFreeLie L) =
          ((∑ i, firstSmithRelationCoefficient r i •
            (firstSmithDiagonal i • B i)) : DegreeFive.freeLieExact L 1) :=
        congrArg Subtype.val heq
      _ = _ := by
        change (DegreeFive.freeLieExact L 1).subtype
          (∑ i, firstSmithRelationCoefficient r i •
            (firstSmithDiagonal i • B i)) = _
        rw [map_sum]
        simp only [map_zsmul]
        rfl

theorem firstSmithRelationRemainder_mem_ker [Finite L]
    (r : LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap) :
    firstSmithRelationRemainder r ∈
      LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap := by
  rw [LinearMap.mem_ker]
  change canonicalFreeLieEvaluation L (firstSmithRelationRemainder r) = 0
  unfold firstSmithRelationRemainder
  rw [map_sub, map_sum]
  have hr : canonicalFreeLieEvaluation L (r : CanonicalFreeLie L) = 0 :=
    r.property
  rw [hr]
  apply sub_eq_zero.mpr
  symm
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_zsmul, DegreeFive.collectedRelationRow_mem_ker, smul_zero]

/-- The preabelian decomposition of an arbitrary defining relation. -/
theorem kernelRelation_eq_firstRows_add_gammaTwo [Finite L]
    (r : LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap) :
    (r : CanonicalFreeLie L) =
      (∑ i, firstSmithRelationCoefficient r i •
        (DegreeFive.collectedRelationRow L L
          (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L)) +
        firstSmithRelationRemainder r := by
  unfold firstSmithRelationRemainder
  abel

private theorem freeMagma_eq_mul_of_length_two (w : FreeMagma L)
    (hw : w.length = 2) :
    ∃ x y : L, w = FreeMagma.of x * FreeMagma.of y := by
  cases w with
  | of x => simp at hw
  | mul p q =>
      have hp := FreeMagma.length_pos p
      have hq := FreeMagma.length_pos q
      change p.length + q.length = 2 at hw
      have hpone : p.length = 1 := by omega
      have hqone : q.length = 1 := by omega
      cases p with
      | mul a b =>
          have ha := FreeMagma.length_pos a
          have hb := FreeMagma.length_pos b
          change a.length + b.length = 1 at hpone
          omega
      | of x =>
          cases q with
          | mul a b =>
              have ha := FreeMagma.length_pos a
              have hb := FreeMagma.length_pos b
              change a.length + b.length = 1 at hqone
              omega
          | of y => exact ⟨x, y, rfl⟩

private theorem freeMagma_eq_of_of_length_one (w : FreeMagma L)
    (hw : w.length = 1) : ∃ z : L, w = FreeMagma.of z := by
  cases w with
  | of z => exact ⟨z, rfl⟩
  | mul p q =>
      have hp := FreeMagma.length_pos p
      have hq := FreeMagma.length_pos q
      change p.length + q.length = 1 at hw
      omega

private theorem freeLieMkLinear_single_mul (p q : FreeMagma L) :
    FreeLieDimension.freeLieMkLinear L (Finsupp.single (p * q) 1) =
      ⁅FreeLieDimension.freeLieMkLinear L (Finsupp.single p 1),
        FreeLieDimension.freeLieMkLinear L (Finsupp.single q 1)⁆ := by
  let sp : FreeNonUnitalNonAssocAlgebra ℤ L := Finsupp.single p 1
  let sq : FreeNonUnitalNonAssocAlgebra ℤ L := Finsupp.single q 1
  have hsingle : (Finsupp.single (p * q) (1 : ℤ) :
      FreeNonUnitalNonAssocAlgebra ℤ L) = sp * sq := by
    simpa only [sp, sq, one_mul] using
      (MonoidAlgebra.single_mul_single p q (1 : ℤ) (1 : ℤ)).symm
  rw [hsingle, FreeLieDimension.freeLieMkLinear_mul]

private def magmaExactSingle (n : ℕ)
    (w : {w : FreeMagma L // w.length = n}) : DegreeFive.magmaExact L n :=
  ⟨Finsupp.single w.1 1, by
    intro v hv
    have hvw : v = w.1 := by
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hv) (by simp [hne])
    simpa [hvw] using w.2⟩

private theorem span_magmaExactSingle (n : ℕ) :
    Submodule.span ℤ (Set.range (magmaExactSingle (L := L) n)) = ⊤ := by
  apply top_unique
  rintro ⟨p, hp⟩ -
  let G := Submodule.span ℤ (Set.range (magmaExactSingle (L := L) n))
  have hpmap : p ∈ G.map (DegreeFive.magmaExact L n).subtype := by
    rw [DegreeFive.magmaExact, Finsupp.supported_eq_span_single] at hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
        obtain ⟨w, hw, rfl⟩ := hp
        refine ⟨magmaExactSingle n ⟨w, hw⟩, ?_, rfl⟩
        exact Submodule.subset_span ⟨_, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add a b ha hb hpa hpb => exact Submodule.add_mem _ hpa hpb
    | smul c p hp hrec => exact Submodule.smul_mem _ c hrec
  obtain ⟨q, hq, hqp⟩ := hpmap
  have heq : q = (⟨p, hp⟩ : DegreeFive.magmaExact L n) := by
    apply Subtype.ext
    exact hqp
  simpa only [G, heq] using hq

private def magmaExactToFreeLieExact (n : ℕ) :
    DegreeFive.magmaExact L n →ₗ[ℤ] DegreeFive.freeLieExact L n :=
  (FreeLieDimension.freeLieMkLinear L).domRestrict (DegreeFive.magmaExact L n) |>.codRestrict
    (DegreeFive.freeLieExact L n) (fun p ↦ ⟨p, p.property, rfl⟩)

/-- Every exact quadratic free-Lie element has unique-needed (not uniquely chosen) integral
coordinates on strict brackets of the first Smith generators. -/
theorem exists_strictBracketCoordinates [Finite L]
    (x : DegreeFive.freeLieExact L 2) :
    ∃ a : FirstSmithIndex L → FirstSmithIndex L → ℤ,
      (x : CanonicalFreeLie L) =
        ∑ i, ∑ j, if j < i then
          a i j • ⁅firstSmithGenerator i, firstSmithGenerator j⁆ else 0 := by
  classical
  let I := FirstSmithIndex L
  let StrictPair := {ij : I × I // ij.2 < ij.1}
  let bracketFamily : StrictPair → CanonicalFreeLie L := fun ij ↦
    ⁅firstSmithGenerator (ij : I × I).1,
      firstSmithGenerator (ij : I × I).2⁆
  let N : Submodule ℤ (CanonicalFreeLie L) :=
    Submodule.span ℤ (Set.range bracketFamily)
  have hgenerator (z : L) : FreeLieAlgebra.of ℤ z =
      ∑ i : I,
        ((DegreeFive.collectedHomogeneousBasis L L
          (canonicalFreeLieEvaluation L) 1).repr
            (DegreeFive.adaptedFreeGeneratorExactOne L z)) i •
          firstSmithGenerator i := by
    have h := (DegreeFive.collectedHomogeneousBasis L L
      (canonicalFreeLieEvaluation L) 1).sum_repr
        (DegreeFive.adaptedFreeGeneratorExactOne L z)
    have h' := congrArg Subtype.val h
    calc
      FreeLieAlgebra.of ℤ z =
          (DegreeFive.adaptedFreeGeneratorExactOne L z : CanonicalFreeLie L) := rfl
      _ = ((∑ i : I,
          ((DegreeFive.collectedHomogeneousBasis L L
            (canonicalFreeLieEvaluation L) 1).repr
              (DegreeFive.adaptedFreeGeneratorExactOne L z)) i •
            DegreeFive.collectedHomogeneousBasis L L
              (canonicalFreeLieEvaluation L) 1 i) :
            DegreeFive.freeLieExact L 1) := h'.symm
      _ = ∑ i : I,
          ((DegreeFive.collectedHomogeneousBasis L L
            (canonicalFreeLieEvaluation L) 1).repr
              (DegreeFive.adaptedFreeGeneratorExactOne L z)) i •
            firstSmithGenerator i := by
        change (DegreeFive.freeLieExact L 1).subtype (∑ i : I,
          ((DegreeFive.collectedHomogeneousBasis L L
            (canonicalFreeLieEvaluation L) 1).repr
              (DegreeFive.adaptedFreeGeneratorExactOne L z)) i •
            DegreeFive.collectedHomogeneousBasis L L
              (canonicalFreeLieEvaluation L) 1 i) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_zsmul]
        rfl
  have hbracket (z t : L) :
      ⁅FreeLieAlgebra.of ℤ z, FreeLieAlgebra.of ℤ t⁆ ∈ N := by
    rw [hgenerator z, hgenerator t, sum_lie]
    apply Submodule.sum_mem
    intro i hi
    rw [lie_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [lie_zsmul, zsmul_lie, smul_smul]
    rcases lt_trichotomy j i with hji | rfl | hij
    · exact N.smul_mem _ (Submodule.subset_span ⟨⟨(i, j), hji⟩, rfl⟩)
    · simp
    · rw [show ⁅firstSmithGenerator i, firstSmithGenerator j⁆ =
          -⁅firstSmithGenerator j, firstSmithGenerator i⁆ by
        exact (lie_skew (firstSmithGenerator i) (firstSmithGenerator j)).symm]
      exact N.smul_mem _ (N.neg_mem
        (Submodule.subset_span ⟨⟨(j, i), hij⟩, rfl⟩))
  obtain ⟨p, hp, hpx⟩ := x.property
  have hall (q : FreeNonUnitalNonAssocAlgebra ℤ L)
      (hq : q ∈ DegreeFive.magmaExact L 2) :
      FreeLieDimension.freeLieMkLinear L q ∈ N := by
    rw [DegreeFive.magmaExact, Finsupp.supported_eq_span_single] at hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
        obtain ⟨w, hw, rfl⟩ := hq
        obtain ⟨z, t, rfl⟩ := freeMagma_eq_mul_of_length_two w hw
        rw [freeLieMkLinear_single_mul]
        simpa using hbracket z t
    | zero => simp
    | add p q hp hq ihp ihq => simpa using N.add_mem ihp ihq
    | smul n p hp ih => simpa using N.smul_mem n ih
  have hpN : FreeLieDimension.freeLieMkLinear L p ∈ N := hall p hp
  have hxN : (x : CanonicalFreeLie L) ∈ N := hpx ▸ hpN
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hxN
  let d : (I × I) →₀ ℤ := Finsupp.mapDomain Subtype.val c
  have hd : d.sum (fun ij n ↦ n •
      ⁅firstSmithGenerator ij.1, firstSmithGenerator ij.2⁆) = x := by
    unfold d
    rw [Finsupp.sum_mapDomain_index]
    · simpa [bracketFamily] using hc
    · intro q
      simp
    · intro q a b
      rw [add_smul]
  have hdzero (i j : I) (hji : ¬ j < i) : d (i, j) = 0 := by
    unfold d
    apply Finsupp.mapDomain_notin_range
    rintro ⟨q, hq⟩
    have hfst := congrArg Prod.fst hq
    have hsnd := congrArg Prod.snd hq
    apply hji
    change (q : I × I).1 = i at hfst
    change (q : I × I).2 = j at hsnd
    rw [← hfst, ← hsnd]
    exact q.property
  refine ⟨fun i j ↦ d (i, j), ?_⟩
  rw [← hd]
  calc
    d.sum (fun ij n ↦ n •
        ⁅firstSmithGenerator ij.1, firstSmithGenerator ij.2⁆) =
        ∑ ij, d ij •
          ⁅firstSmithGenerator ij.1, firstSmithGenerator ij.2⁆ := by
      exact Finsupp.sum_fintype d (fun ij n ↦ n •
        ⁅firstSmithGenerator ij.1, firstSmithGenerator ij.2⁆) (by simp)
    _ = ∑ i, ∑ j, if j < i then
          d (i, j) • ⁅firstSmithGenerator i, firstSmithGenerator j⁆ else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j < i
      · simp [hji]
      · simp [hji, hdzero i j hji]

private theorem tripleBracket_jacobi {A : Type*} [LieRing A]
    (x y z : A) :
    ⁅⁅x, y⁆, z⁆ = ⁅⁅z, y⁆, x⁆ - ⁅⁅z, x⁆, y⁆ := by
  have h := lie_jacobi x y z
  rw [show ⁅z, x⁆ = -⁅x, z⁆ by exact (lie_skew z x).symm,
    lie_neg] at h
  have hj : ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
    rw [sub_eq_add_neg]
    exact h
  have hab : ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆ = -⁅z, ⁅x, y⁆⁆ :=
    eq_neg_of_add_eq_zero_left hj
  calc
    ⁅⁅x, y⁆, z⁆ = -⁅z, ⁅x, y⁆⁆ := (lie_skew ⁅x, y⁆ z).symm
    _ = ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆ := hab.symm
    _ = ⁅⁅z, y⁆, x⁆ - ⁅⁅z, x⁆, y⁆ := by
      rw [show ⁅⁅z, y⁆, x⁆ = -⁅x, ⁅z, y⁆⁆ by
          exact (lie_skew ⁅z, y⁆ x).symm,
        show ⁅⁅z, x⁆, y⁆ = -⁅y, ⁅z, x⁆⁆ by
          exact (lie_skew ⁅z, x⁆ y).symm,
        show ⁅z, y⁆ = -⁅y, z⁆ by exact (lie_skew z y).symm,
        show ⁅z, x⁆ = -⁅x, z⁆ by exact (lie_skew z x).symm,
        lie_neg, lie_neg]
      abel

private theorem lie_nested_eq_triple_sub {A : Type*} [LieRing A]
    (x y z : A) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ - ⁅⁅x, z⁆, y⁆ := by
  have h := lie_jacobi x y z
  rw [show ⁅z, x⁆ = -⁅x, z⁆ by exact (lie_skew z x).symm,
    lie_neg] at h
  have hj : ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
    rw [sub_eq_add_neg]
    exact h
  have hab : ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆ = -⁅z, ⁅x, y⁆⁆ :=
    eq_neg_of_add_eq_zero_left hj
  calc
    ⁅x, ⁅y, z⁆⁆ =
        (⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆) + ⁅y, ⁅x, z⁆⁆ := by abel
    _ = -⁅z, ⁅x, y⁆⁆ + ⁅y, ⁅x, z⁆⁆ := by rw [hab]
    _ = ⁅⁅x, y⁆, z⁆ - ⁅⁅x, z⁆, y⁆ := by
      rw [show ⁅⁅x, y⁆, z⁆ = -⁅z, ⁅x, y⁆⁆ by
          exact (lie_skew ⁅x, y⁆ z).symm,
        show ⁅⁅x, z⁆, y⁆ = -⁅y, ⁅x, z⁆⁆ by
          exact (lie_skew ⁅x, z⁆ y).symm]
      abel

private theorem freeMagma_eq_cubic (w : FreeMagma L)
    (hw : w.length = 3) :
    (∃ x y z : L,
      w = (FreeMagma.of x * FreeMagma.of y) * FreeMagma.of z) ∨
    (∃ x y z : L,
      w = FreeMagma.of x * (FreeMagma.of y * FreeMagma.of z)) := by
  cases w with
  | of x => simp at hw
  | mul p q =>
      have hp := FreeMagma.length_pos p
      have hq := FreeMagma.length_pos q
      change p.length + q.length = 3 at hw
      by_cases hpone : p.length = 1
      · have hqtwo : q.length = 2 := by omega
        obtain ⟨x, rfl⟩ := freeMagma_eq_of_of_length_one p hpone
        obtain ⟨y, z, rfl⟩ := freeMagma_eq_mul_of_length_two q hqtwo
        exact Or.inr ⟨x, y, z, rfl⟩
      · have hptwo : p.length = 2 := by omega
        have hqone : q.length = 1 := by omega
        obtain ⟨x, y, rfl⟩ := freeMagma_eq_mul_of_length_two p hptwo
        obtain ⟨z, rfl⟩ := freeMagma_eq_of_of_length_one q hqone
        exact Or.inl ⟨x, y, z, rfl⟩

/-- Every exact cubic free-Lie element is a sum of Passi-normalized triples
`[[X_i,X_j],X_k]` with `i<j` and `i≤k`.  No independence is asserted. -/
private theorem exists_normalizedTripleCoordinates [Finite L]
    (x : DegreeFive.freeLieExact L 3) :
    ∃ b : FirstSmithIndex L → FirstSmithIndex L → FirstSmithIndex L → ℤ,
      (x : CanonicalFreeLie L) =
        ∑ i, ∑ j, ∑ k, if i < j ∧ i ≤ k then
          b i j k • ⁅⁅firstSmithGenerator i, firstSmithGenerator j⁆,
            firstSmithGenerator k⁆ else 0 := by
  classical
  let I := FirstSmithIndex L
  let GoodTriple := {t : I × I × I // t.1 < t.2.1 ∧ t.1 ≤ t.2.2}
  let tripleFamily : GoodTriple → CanonicalFreeLie L := fun t ↦
    ⁅⁅firstSmithGenerator t.1.1, firstSmithGenerator t.1.2.1⁆,
      firstSmithGenerator t.1.2.2⁆
  let N : Submodule ℤ (CanonicalFreeLie L) :=
    Submodule.span ℤ (Set.range tripleFamily)
  have hgenerator (z : L) : FreeLieAlgebra.of ℤ z =
      ∑ i : I,
        ((DegreeFive.collectedHomogeneousBasis L L
          (canonicalFreeLieEvaluation L) 1).repr
            (DegreeFive.adaptedFreeGeneratorExactOne L z)) i •
          firstSmithGenerator i := by
    have h := (DegreeFive.collectedHomogeneousBasis L L
      (canonicalFreeLieEvaluation L) 1).sum_repr
        (DegreeFive.adaptedFreeGeneratorExactOne L z)
    have h' := congrArg Subtype.val h
    calc
      FreeLieAlgebra.of ℤ z =
          (DegreeFive.adaptedFreeGeneratorExactOne L z :
            CanonicalFreeLie L) := rfl
      _ = ((∑ i : I,
          ((DegreeFive.collectedHomogeneousBasis L L
            (canonicalFreeLieEvaluation L) 1).repr
              (DegreeFive.adaptedFreeGeneratorExactOne L z)) i •
            DegreeFive.collectedHomogeneousBasis L L
              (canonicalFreeLieEvaluation L) 1 i) :
            DegreeFive.freeLieExact L 1) := h'.symm
      _ = ∑ i : I,
          ((DegreeFive.collectedHomogeneousBasis L L
            (canonicalFreeLieEvaluation L) 1).repr
              (DegreeFive.adaptedFreeGeneratorExactOne L z)) i •
            firstSmithGenerator i := by
        change (DegreeFive.freeLieExact L 1).subtype (∑ i : I,
          ((DegreeFive.collectedHomogeneousBasis L L
            (canonicalFreeLieEvaluation L) 1).repr
              (DegreeFive.adaptedFreeGeneratorExactOne L z)) i •
            DegreeFive.collectedHomogeneousBasis L L
              (canonicalFreeLieEvaluation L) 1 i) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_zsmul]
        rfl
  have hordered (i j k : I) (hij : i < j) :
      ⁅⁅firstSmithGenerator i, firstSmithGenerator j⁆,
        firstSmithGenerator k⁆ ∈ N := by
    by_cases hik : i ≤ k
    · exact Submodule.subset_span ⟨⟨(i, j, k), hij, hik⟩, rfl⟩
    · have hki : k < i := lt_of_not_ge hik
      rw [tripleBracket_jacobi]
      exact N.sub_mem
        (Submodule.subset_span ⟨⟨(k, j, i), hki.trans hij, hki.le⟩, rfl⟩)
        (Submodule.subset_span ⟨⟨(k, i, j), hki, hki.le.trans hij.le⟩,
          rfl⟩)
  have hnormalized (i j k : I) :
      ⁅⁅firstSmithGenerator i, firstSmithGenerator j⁆,
        firstSmithGenerator k⁆ ∈ N := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hordered i j k hij
    · simp
    · rw [show ⁅firstSmithGenerator i, firstSmithGenerator j⁆ =
          -⁅firstSmithGenerator j, firstSmithGenerator i⁆ by
        exact (lie_skew (firstSmithGenerator i)
          (firstSmithGenerator j)).symm,
        neg_lie]
      exact N.neg_mem (hordered j i k hji)
  have htriple (a b c : L) :
      ⁅⁅FreeLieAlgebra.of ℤ a, FreeLieAlgebra.of ℤ b⁆,
        FreeLieAlgebra.of ℤ c⁆ ∈ N := by
    rw [hgenerator a, hgenerator b, hgenerator c]
    simp only [sum_lie, lie_sum, zsmul_lie, lie_zsmul,
      Finset.smul_sum, smul_smul]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.sum_mem
    intro k hk
    exact N.smul_mem _ (hnormalized k j i)
  have hall (p : FreeNonUnitalNonAssocAlgebra ℤ L)
      (hp : p ∈ DegreeFive.magmaExact L 3) :
      FreeLieDimension.freeLieMkLinear L p ∈ N := by
    rw [DegreeFive.magmaExact, Finsupp.supported_eq_span_single] at hp
    induction hp using Submodule.span_induction with
    | mem q hq =>
        obtain ⟨w, hw, rfl⟩ := hq
        rcases freeMagma_eq_cubic w hw with hleft | hright
        · obtain ⟨a, b, c, rfl⟩ := hleft
          rw [freeLieMkLinear_single_mul, freeLieMkLinear_single_mul]
          simpa using htriple a b c
        · obtain ⟨a, b, c, rfl⟩ := hright
          rw [freeLieMkLinear_single_mul, freeLieMkLinear_single_mul,
            lie_nested_eq_triple_sub]
          exact N.sub_mem (htriple a b c) (htriple a c b)
    | zero => simp
    | add p q hp hq ihp ihq => exact N.add_mem ihp ihq
    | smul n p hp ih => exact N.smul_mem n ih
  obtain ⟨p, hp, hpx⟩ := x.property
  have hpN : FreeLieDimension.freeLieMkLinear L p ∈ N := hall p hp
  have hxN : (x : CanonicalFreeLie L) ∈ N := hpx ▸ hpN
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hxN
  let d : (I × I × I) →₀ ℤ := Finsupp.mapDomain Subtype.val c
  have hd : d.sum (fun t n ↦ n •
      ⁅⁅firstSmithGenerator t.1, firstSmithGenerator t.2.1⁆,
        firstSmithGenerator t.2.2⁆) = x := by
    unfold d
    rw [Finsupp.sum_mapDomain_index]
    · simpa [tripleFamily] using hc
    · intro q
      simp
    · intro q a b
      rw [add_smul]
  have hdzero (i j k : I) (hgood : ¬(i < j ∧ i ≤ k)) :
      d (i, j, k) = 0 := by
    unfold d
    apply Finsupp.mapDomain_notin_range
    rintro ⟨q, hq⟩
    have h1 := congrArg Prod.fst hq
    have h2 := congrArg (fun t ↦ t.2.1) hq
    have h3 := congrArg (fun t ↦ t.2.2) hq
    apply hgood
    change (q : I × I × I).1 = i at h1
    change (q : I × I × I).2.1 = j at h2
    change (q : I × I × I).2.2 = k at h3
    rw [← h1, ← h2, ← h3]
    exact q.property
  refine ⟨fun i j k ↦ d (i, j, k), ?_⟩
  rw [← hd]
  calc
    d.sum (fun t n ↦ n •
        ⁅⁅firstSmithGenerator t.1, firstSmithGenerator t.2.1⁆,
          firstSmithGenerator t.2.2⁆) =
        ∑ t, d t • ⁅⁅firstSmithGenerator t.1,
          firstSmithGenerator t.2.1⁆, firstSmithGenerator t.2.2⁆ := by
      exact Finsupp.sum_fintype d (fun t n ↦ n •
        ⁅⁅firstSmithGenerator t.1, firstSmithGenerator t.2.1⁆,
          firstSmithGenerator t.2.2⁆) (by simp)
    _ = ∑ i : I, ∑ jk : I × I,
          d (i, jk) • ⁅⁅firstSmithGenerator i,
            firstSmithGenerator jk.1⁆, firstSmithGenerator jk.2⁆ := by
      exact Fintype.sum_prod_type _
    _ = ∑ i, ∑ j, ∑ k,
          d (i, j, k) • ⁅⁅firstSmithGenerator i,
            firstSmithGenerator j⁆, firstSmithGenerator k⁆ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Fintype.sum_prod_type _
    _ = ∑ i, ∑ j, ∑ k, if i < j ∧ i ≤ k then
          d (i, j, k) • ⁅⁅firstSmithGenerator i, firstSmithGenerator j⁆,
            firstSmithGenerator k⁆ else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hgood : i < j ∧ i ≤ k
      · simp [hgood]
      · simp [hgood, hdzero i j k hgood]

/-! The following change of free associative generators is the concrete coordinate system used
for the length-two/three comparison.  It is induced by the first Smith basis, so its inverse
is again given by a finite linear substitution. -/

def originalGeneratorInFirstSmithCoordinates [Finite L]
    (z : L) : FirstSmithIndex L →₀ ℤ :=
  (DegreeFive.collectedHomogeneousBasis L L
    (canonicalFreeLieEvaluation L) 1).repr
      (DegreeFive.adaptedFreeGeneratorExactOne L z)

def freeAlgebraToFirstSmith [Finite L] :
    FreeAlgebra ℤ L →ₐ[ℤ] FreeAlgebra ℤ (FirstSmithIndex L) :=
  FreeAlgebra.lift ℤ fun z ↦
    ∑ i, originalGeneratorInFirstSmithCoordinates z i • FreeAlgebra.ι ℤ i

def freeAlgebraFromFirstSmith [Finite L] :
    FreeAlgebra ℤ (FirstSmithIndex L) →ₐ[ℤ] FreeAlgebra ℤ L :=
  FreeAlgebra.lift ℤ fun i ↦
    PBW.freeLieToFreeAlgebra ℤ L (firstSmithGenerator i)

theorem freeAlgebraToFirstSmith_exactOne [Finite L]
    (v : DegreeFive.freeLieExact L 1) :
    freeAlgebraToFirstSmith (L := L)
        (PBW.freeLieToFreeAlgebra ℤ L (v : CanonicalFreeLie L)) =
      ∑ i, ((DegreeFive.collectedHomogeneousBasis L L
          (canonicalFreeLieEvaluation L) 1).repr v) i • FreeAlgebra.ι ℤ i := by
  let lhs : DegreeFive.freeLieExact L 1 →ₗ[ℤ]
      FreeAlgebra ℤ (FirstSmithIndex L) :=
    (freeAlgebraToFirstSmith (L := L)).toLinearMap.comp
      ((PBW.freeLieToFreeAlgebra ℤ L).toLinearMap.comp
        (DegreeFive.freeLieExact L 1).subtype)
  let rhs : DegreeFive.freeLieExact L 1 →ₗ[ℤ]
      FreeAlgebra ℤ (FirstSmithIndex L) :=
    (Finsupp.linearCombination ℤ
      (FreeAlgebra.ι ℤ : FirstSmithIndex L →
        FreeAlgebra ℤ (FirstSmithIndex L))).comp
      (DegreeFive.collectedHomogeneousBasis L L
        (canonicalFreeLieEvaluation L) 1).repr.toLinearMap
  have hmaps : lhs.comp (magmaExactToFreeLieExact (L := L) 1) =
      rhs.comp (magmaExactToFreeLieExact (L := L) 1) := by
    refine LinearMap.ext_on
      (span_magmaExactSingle (L := L) 1) ?_
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    obtain ⟨z, rfl⟩ := freeMagma_eq_of_of_length_one w hw
    change freeAlgebraToFirstSmith (L := L)
        (PBW.freeLieToFreeAlgebra ℤ L
          (FreeLieDimension.freeLieMkLinear L
            (Finsupp.single (FreeMagma.of z) 1))) = _
    change freeAlgebraToFirstSmith (L := L)
        (PBW.freeLieToFreeAlgebra ℤ L (FreeLieAlgebra.of ℤ z)) = _
    have hof : PBW.freeLieToFreeAlgebra ℤ L (FreeLieAlgebra.of ℤ z) =
        FreeAlgebra.ι ℤ z := by
      unfold PBW.freeLieToFreeAlgebra
      rw [FreeLieAlgebra.lift_of_apply]
    rw [hof]
    have heq : magmaExactToFreeLieExact (L := L) 1
        (magmaExactSingle (L := L) 1 ⟨FreeMagma.of z, hw⟩) =
        DegreeFive.adaptedFreeGeneratorExactOne L z := by
      apply Subtype.ext
      rfl
    change freeAlgebraToFirstSmith (L := L) (FreeAlgebra.ι ℤ z) =
      rhs (magmaExactToFreeLieExact (L := L) 1
        (magmaExactSingle (L := L) 1 ⟨FreeMagma.of z, hw⟩))
    rw [heq]
    change (FreeAlgebra.lift ℤ (fun t ↦
        ∑ i, originalGeneratorInFirstSmithCoordinates t i •
          FreeAlgebra.ι ℤ i)) (FreeAlgebra.ι ℤ z) =
      (Finsupp.linearCombination ℤ
        (FreeAlgebra.ι ℤ : FirstSmithIndex L →
          FreeAlgebra ℤ (FirstSmithIndex L)))
        ((DegreeFive.collectedHomogeneousBasis L L
          (canonicalFreeLieEvaluation L) 1).repr
            (DegreeFive.adaptedFreeGeneratorExactOne L z))
    rw [FreeAlgebra.lift_ι_apply]
    change (∑ i, originalGeneratorInFirstSmithCoordinates z i •
        FreeAlgebra.ι ℤ i) =
      ((DegreeFive.collectedHomogeneousBasis L L
        (canonicalFreeLieEvaluation L) 1).repr
          (DegreeFive.adaptedFreeGeneratorExactOne L z)).sum
            (fun i n ↦ n • FreeAlgebra.ι ℤ i)
    rw [Finsupp.sum_fintype _ _ (by simp)]
    rfl
  obtain ⟨p, hp, hpv⟩ := v.property
  let p' : DegreeFive.magmaExact L 1 := ⟨p, hp⟩
  have hv : magmaExactToFreeLieExact (L := L) 1 p' = v := by
    apply Subtype.ext
    exact hpv
  have h := LinearMap.congr_fun hmaps p'
  change lhs (magmaExactToFreeLieExact (L := L) 1 p') =
    rhs (magmaExactToFreeLieExact (L := L) 1 p') at h
  rw [hv] at h
  change freeAlgebraToFirstSmith (L := L)
      (PBW.freeLieToFreeAlgebra ℤ L (v : CanonicalFreeLie L)) =
    ((DegreeFive.collectedHomogeneousBasis L L
      (canonicalFreeLieEvaluation L) 1).repr v).sum
        (fun i n ↦ n • FreeAlgebra.ι ℤ i) at h
  rw [Finsupp.sum_fintype _ _ (by simp)] at h
  simpa using h

@[simp]
theorem freeAlgebraToFirstSmith_firstSmithGenerator [Finite L]
    (i : FirstSmithIndex L) :
    freeAlgebraToFirstSmith (L := L)
        (PBW.freeLieToFreeAlgebra ℤ L (firstSmithGenerator i)) =
      FreeAlgebra.ι ℤ i := by
  have h := freeAlgebraToFirstSmith_exactOne
    (DegreeFive.collectedHomogeneousBasis L L
      (canonicalFreeLieEvaluation L) 1 i)
  change freeAlgebraToFirstSmith (L := L)
      (PBW.freeLieToFreeAlgebra ℤ L (firstSmithGenerator i)) = _ at h
  rw [(DegreeFive.collectedHomogeneousBasis L L
    (canonicalFreeLieEvaluation L) 1).repr_self] at h
  simpa [Finsupp.single_apply] using h

theorem freeAlgebraToFirstSmith_comp_fromFirstSmith [Finite L] :
    (freeAlgebraToFirstSmith (L := L)).comp
        (freeAlgebraFromFirstSmith (L := L)) =
      AlgHom.id ℤ (FreeAlgebra ℤ (FirstSmithIndex L)) := by
  apply FreeAlgebra.hom_ext
  funext i
  simp [freeAlgebraFromFirstSmith]

@[simp]
theorem freeAlgebraFromFirstSmith_ι [Finite L] (i : FirstSmithIndex L) :
    freeAlgebraFromFirstSmith (L := L) (FreeAlgebra.ι ℤ i) =
      PBW.freeLieToFreeAlgebra ℤ L (firstSmithGenerator i) := by
  simp [freeAlgebraFromFirstSmith]

theorem freeAlgebraFromFirstSmith_toFirstSmith_generator [Finite L] (z : L) :
    freeAlgebraFromFirstSmith (L := L)
        (freeAlgebraToFirstSmith (L := L) (FreeAlgebra.ι ℤ z)) =
      FreeAlgebra.ι ℤ z := by
  rw [show freeAlgebraToFirstSmith (L := L) (FreeAlgebra.ι ℤ z) =
      ∑ i, originalGeneratorInFirstSmithCoordinates z i • FreeAlgebra.ι ℤ i by
    simp [freeAlgebraToFirstSmith]]
  rw [map_sum]
  simp_rw [map_zsmul, freeAlgebraFromFirstSmith_ι]
  have hgen := (DegreeFive.collectedHomogeneousBasis L L
    (canonicalFreeLieEvaluation L) 1).sum_repr
      (DegreeFive.adaptedFreeGeneratorExactOne L z)
  have hgen' := congrArg Subtype.val hgen
  have hcoe : (∑ i, originalGeneratorInFirstSmithCoordinates z i •
      firstSmithGenerator i) = FreeLieAlgebra.of ℤ z := by
    calc
      _ = (DegreeFive.freeLieExact L 1).subtype
          (∑ i, originalGeneratorInFirstSmithCoordinates z i •
            DegreeFive.collectedHomogeneousBasis L L
              (canonicalFreeLieEvaluation L) 1 i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_zsmul]
        rfl
      _ = _ := by
        simpa [originalGeneratorInFirstSmithCoordinates,
          DegreeFive.adaptedFreeGeneratorExactOne] using hgen'
  have hfree := congrArg (PBW.freeLieToFreeAlgebra ℤ L) hcoe
  rw [map_sum] at hfree
  simp_rw [map_zsmul] at hfree
  have hof : PBW.freeLieToFreeAlgebra ℤ L (FreeLieAlgebra.of ℤ z) =
      FreeAlgebra.ι ℤ z := by
    unfold PBW.freeLieToFreeAlgebra
    rw [FreeLieAlgebra.lift_of_apply]
  simpa [originalGeneratorInFirstSmithCoordinates, firstSmithGenerator,
    hof] using hfree

theorem freeAlgebraFromFirstSmith_comp_toFirstSmith [Finite L] :
    (freeAlgebraFromFirstSmith (L := L)).comp
        (freeAlgebraToFirstSmith (L := L)) = AlgHom.id ℤ (FreeAlgebra ℤ L) := by
  apply FreeAlgebra.hom_ext
  funext z
  exact freeAlgebraFromFirstSmith_toFirstSmith_generator z

/-- The change to the first Smith generators is an algebra equivalence. -/
def freeAlgebraFirstSmithEquiv [Finite L] :
    FreeAlgebra ℤ L ≃ₐ[ℤ] FreeAlgebra ℤ (FirstSmithIndex L) :=
  AlgEquiv.ofAlgHom (freeAlgebraToFirstSmith (L := L))
    (freeAlgebraFromFirstSmith (L := L))
    freeAlgebraToFirstSmith_comp_fromFirstSmith
    freeAlgebraFromFirstSmith_comp_toFirstSmith

private def wordPrefix {I : Type*} (i : I) (w : FreeMonoid I) :
    FreeMonoid I :=
  FreeMonoid.of i * w

private theorem wordPrefix_inj {I : Type*} (i : I) :
    Function.Injective (wordPrefix i) := by
  intro w v h
  exact mul_left_cancel h

/-- The coefficient after removing a prescribed first letter.  These are
Passi's right-module coordinates on the augmentation ideal of a free
associative algebra. -/
private def rightCoeff {I : Type*} (i : I) :
    FreeAlgebra ℤ I →ₗ[ℤ] FreeAlgebra ℤ I :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toLinearMap.comp
    ((MonoidAlgebra.comapDomainAddMonoidHom (R := ℤ) (wordPrefix i)
      (wordPrefix_inj i)).toIntLinearMap.comp
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap)

private theorem freeAlgebraWord_equiv {I : Type*} (xs : List I) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (DegreeFive.freeAlgebraWord I xs) =
      Finsupp.single (FreeMonoid.ofList xs) 1 := by
  have h := DegreeFive.monoidBasisElement_eq_freeAlgebraWord
    (X := I) (FreeMonoid.ofList xs)
  rw [FreeMonoid.toList_ofList] at h
  rw [← h, FreeAlgebra.equivMonoidAlgebraFreeMonoid.apply_symm_apply]

private theorem rightCoeff_word {I : Type*} [DecidableEq I]
    (i j : I) (xs : List I) :
    rightCoeff i (DegreeFive.freeAlgebraWord I (j :: xs)) =
      if i = j then DegreeFive.freeAlgebraWord I xs else 0 := by
  classical
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  dsimp [rightCoeff]
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
        ((MonoidAlgebra.comapDomainAddMonoidHom (R := ℤ) (wordPrefix i)
          (wordPrefix_inj i))
            (FreeAlgebra.equivMonoidAlgebraFreeMonoid
              (DegreeFive.freeAlgebraWord I (j :: xs))))) = _
  rw [FreeAlgebra.equivMonoidAlgebraFreeMonoid.apply_symm_apply]
  change (MonoidAlgebra.comapDomainAddMonoidHom (R := ℤ) (wordPrefix i)
      (wordPrefix_inj i))
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (DegreeFive.freeAlgebraWord I (j :: xs))) =
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (if i = j then DegreeFive.freeAlgebraWord I xs else 0)
  rw [freeAlgebraWord_equiv]
  ext w
  rw [MonoidAlgebra.comapDomainAddMonoidHom_apply]
  change (Finsupp.single (FreeMonoid.ofList (j :: xs)) 1)
      (wordPrefix i w) =
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (if i = j then DegreeFive.freeAlgebraWord I xs else 0)) w
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, freeAlgebraWord_equiv]
    by_cases hw : w = FreeMonoid.ofList xs
    · subst w
      simp [wordPrefix]
    · have hp : FreeMonoid.of i * w ≠
          FreeMonoid.of i * FreeMonoid.ofList xs := by
        intro h
        exact hw (mul_left_cancel h)
      simp [wordPrefix, hw, hp]
  · rw [if_neg hij, map_zero]
    have hne : wordPrefix i w ≠
        FreeMonoid.of j * FreeMonoid.ofList xs := by
      intro h
      have ht := congrArg FreeMonoid.toList h
      simp [wordPrefix] at ht
      exact hij ht.1
    have hne' : FreeMonoid.ofList (j :: xs) ≠ wordPrefix i w :=
      fun h ↦ hne h.symm
    change (Finsupp.single (FreeMonoid.of j * FreeMonoid.ofList xs) 1)
      (FreeMonoid.of i * w) = (0 : ℤ)
    have hne'' : FreeMonoid.of j * FreeMonoid.ofList xs ≠
        FreeMonoid.of i * w := fun h ↦ hne h.symm
    simp [hne'']

private theorem rightCoeff_iota_mul {I : Type*} [DecidableEq I]
    (i j : I) (q : FreeAlgebra ℤ I) :
    rightCoeff i (FreeAlgebra.ι ℤ j * q) =
      if i = j then q else 0 := by
  classical
  obtain ⟨c, hc⟩ := DegreeFive.exists_freeAlgebra_word_finsupp I q
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, ← hc, Finsupp.mul_sum, map_finsuppSum]
    apply Finsupp.sum_congr
    intro w hw
    rw [mul_smul_comm, LinearMap.map_smul]
    rw [show FreeAlgebra.ι ℤ i *
        DegreeFive.freeAlgebraWord I (FreeMonoid.toList w) =
        DegreeFive.freeAlgebraWord I (i :: FreeMonoid.toList w) by rfl]
    rw [rightCoeff_word]
    simp
  · rw [if_neg hij, ← hc, Finsupp.mul_sum, map_finsuppSum]
    apply Finset.sum_eq_zero
    intro w hw
    dsimp
    rw [mul_smul_comm, LinearMap.map_smul]
    rw [show FreeAlgebra.ι ℤ j *
        DegreeFive.freeAlgebraWord I (FreeMonoid.toList w) =
        DegreeFive.freeAlgebraWord I (j :: FreeMonoid.toList w) by rfl]
    rw [rightCoeff_word]
    simp [hij]

private theorem sum_iota_mul_rightCoeff {I : Type*} [Fintype I]
    [DecidableEq I] (p : FreeAlgebra ℤ I)
    (hp : p ∈ FreeLieDimension.associativeHigh I 1) :
    p = ∑ i : I, FreeAlgebra.ι ℤ i * rightCoeff i p := by
  classical
  let T : FreeAlgebra ℤ I →ₗ[ℤ] FreeAlgebra ℤ I :=
    ∑ i : I,
      (LinearMap.mulLeft ℤ (FreeAlgebra.ι ℤ i)).comp (rightCoeff i)
  obtain ⟨c, hc⟩ := DegreeFive.exists_freeAlgebra_word_finsupp I p
  have hcE : c = FreeAlgebra.equivMonoidAlgebraFreeMonoid p := by
    ext w
    have h' := congrArg FreeAlgebra.equivMonoidAlgebraFreeMonoid hc
    rw [map_finsuppSum] at h'
    have h := congrArg
      (fun a : MonoidAlgebra ℤ (FreeMonoid I) ↦ a w) h'
    simp only [map_smul, freeAlgebraWord_equiv,
      FreeMonoid.ofList_toList] at h
    have hsum : c.sum (fun a b ↦ b • Finsupp.single a 1) = c := by
      calc
        _ = c.sum Finsupp.single := by
          apply Finsupp.sum_congr
          intro a ha
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        _ = c := Finsupp.sum_single c
    calc
      c w = (c.sum (fun a b ↦ b • Finsupp.single a 1)) w :=
        congrArg (fun d : FreeMonoid I →₀ ℤ ↦ d w) hsum.symm
      _ = _ := h
  have hTp : T p = p := by
    rw [← hc, map_finsuppSum]
    apply Finsupp.sum_congr
    intro w hw
    rw [LinearMap.map_smul]
    congr 1
    have hwE : w ∈
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).support := by
      rw [← hcE]
      exact hw
    have hwlen : 1 ≤ w.length := hp hwE
    have hlist : FreeMonoid.toList w ≠ [] := by
      intro h
      have : w.length = 0 := by
        simpa [FreeMonoid.length] using congrArg List.length h
      omega
    obtain ⟨j, xs, hjxs⟩ := List.exists_cons_of_ne_nil hlist
    rw [hjxs]
    simp only [T, LinearMap.sum_apply, LinearMap.comp_apply]
    simp_rw [rightCoeff_word]
    simp
  simpa only [T, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply] using hTp.symm

private theorem rightCoeff_mem_associativeHigh {I : Type*}
    [DecidableEq I] (i : I) (n : ℕ) (p : FreeAlgebra ℤ I)
    (hp : p ∈ FreeLieDimension.associativeHigh I (n + 1)) :
    rightCoeff i p ∈ FreeLieDimension.associativeHigh I n := by
  classical
  intro w hw
  have hcoeff :
      FreeAlgebra.equivMonoidAlgebraFreeMonoid (rightCoeff i p) w =
        FreeAlgebra.equivMonoidAlgebraFreeMonoid p (wordPrefix i w) := by
    dsimp [rightCoeff]
    change FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
          ((MonoidAlgebra.comapDomainAddMonoidHom (R := ℤ) (wordPrefix i)
            (wordPrefix_inj i))
              (FreeAlgebra.equivMonoidAlgebraFreeMonoid p))) w = _
    rw [FreeAlgebra.equivMonoidAlgebraFreeMonoid.apply_symm_apply]
    rfl
  have hpref : wordPrefix i w ∈
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).support := by
    rw [Finsupp.mem_support_iff]
    intro hz
    have hwne := Finsupp.mem_support_iff.mp hw
    exact hwne (hcoeff.trans hz)
  have hlen := hp hpref
  simp [wordPrefix, FreeMonoid.length_mul] at hlen
  exact Nat.lt_succ_iff.mp (by simpa [Nat.add_comm] using hlen)

private theorem rightCoeff_mem_associativeExact {I : Type*}
    [DecidableEq I] (i : I) (n : ℕ) (p : FreeAlgebra ℤ I)
    (hp : p ∈ FreeLieDimension.associativeExact I (n + 1)) :
    rightCoeff i p ∈ FreeLieDimension.associativeExact I n := by
  classical
  intro w hw
  have hcoeff :
      FreeAlgebra.equivMonoidAlgebraFreeMonoid (rightCoeff i p) w =
        FreeAlgebra.equivMonoidAlgebraFreeMonoid p (wordPrefix i w) := by
    dsimp [rightCoeff]
    change FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
          ((MonoidAlgebra.comapDomainAddMonoidHom (R := ℤ) (wordPrefix i)
            (wordPrefix_inj i))
              (FreeAlgebra.equivMonoidAlgebraFreeMonoid p))) w = _
    rw [FreeAlgebra.equivMonoidAlgebraFreeMonoid.apply_symm_apply]
    rfl
  have hpref : wordPrefix i w ∈
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).support := by
    rw [Finsupp.mem_support_iff]
    intro hz
    have hwne := Finsupp.mem_support_iff.mp hw
    exact hwne (hcoeff.trans hz)
  have hlen := hp hpref
  simpa [wordPrefix, FreeMonoid.length_mul, Nat.add_comm] using hlen

private theorem rightCoeff_mul {I : Type*} [Fintype I]
    [DecidableEq I] (i : I) (p q : FreeAlgebra ℤ I)
    (hp : p ∈ FreeLieDimension.associativeHigh I 1) :
    rightCoeff i (p * q) = rightCoeff i p * q := by
  classical
  calc
    rightCoeff i (p * q) =
        rightCoeff i
          ((∑ j : I, FreeAlgebra.ι ℤ j * rightCoeff j p) * q) := by
      rw [← sum_iota_mul_rightCoeff p hp]
    _ = rightCoeff i
        (∑ j : I, FreeAlgebra.ι ℤ j * (rightCoeff j p * q)) := by
      congr 1
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    _ = ∑ j : I, rightCoeff i
        (FreeAlgebra.ι ℤ j * (rightCoeff j p * q)) := by rw [map_sum]
    _ = rightCoeff i p * q := by
      simp_rw [rightCoeff_iota_mul]
      simp

private theorem exactZero_eq_augmentation_smul_one {I : Type*}
    (p : FreeAlgebra ℤ I)
    (hp : p ∈ FreeLieDimension.associativeExact I 0) :
    p = FreeLieDimension.freeAlgebraAugmentation I p • 1 := by
  have hhigh :=
    FreeLieDimension.sub_algebraMap_freeAlgebraAugmentation_mem_associativeHigh_one
      I p
  have hz := DegreeFive.associativeLengthComponent_eq_zero_of_mem_high I
    hhigh (by omega : 0 < 1)
  rw [map_sub,
    DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I hp] at hz
  have hscalar : (algebraMap ℤ (FreeAlgebra ℤ I))
        (FreeLieDimension.freeAlgebraAugmentation I p) ∈
      FreeLieDimension.associativeExact I 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    apply (FreeLieDimension.associativeExact I 0).smul_mem
    intro w hw
    change w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (1 : FreeAlgebra ℤ I)).support at hw
    rw [map_one FreeAlgebra.equivMonoidAlgebraFreeMonoid] at hw
    have hw1 : w = 1 := by
      by_contra hne
      have hnz := Finsupp.mem_support_iff.mp hw
      apply hnz
      change (Finsupp.single 1 (1 : ℤ)) w = 0
      exact Finsupp.single_eq_of_ne hne
    subst w
    simp
  rw [DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I hscalar]
    at hz
  rw [Algebra.algebraMap_eq_smul_one] at hz
  exact sub_eq_zero.mp hz

/-- The degree-two part of a product of two positive-length elements. -/
private theorem associativeComponent_two_mul {I : Type*}
    (u r : FreeAlgebra ℤ I)
    (hu : u ∈ FreeLieDimension.associativeHigh I 1)
    (hr : r ∈ FreeLieDimension.associativeHigh I 1) :
    DegreeFive.associativeLengthComponent I 2 (u * r) =
      DegreeFive.associativeLengthComponent I 1 u *
        DegreeFive.associativeLengthComponent I 1 r := by
  let u1 := DegreeFive.associativeLengthComponent I 1 u
  let r1 := DegreeFive.associativeLengthComponent I 1 r
  have hu1Exact : u1 ∈ FreeLieDimension.associativeExact I 1 :=
    DegreeFive.associativeLengthComponent_mem_exact I 1 u
  have hr1Exact : r1 ∈ FreeLieDimension.associativeExact I 1 :=
    DegreeFive.associativeLengthComponent_mem_exact I 1 r
  have hu2 : u - u1 ∈ FreeLieDimension.associativeHigh I 2 := by
    apply DegreeFive.mem_associativeHigh_succ_of_component_eq_zero I
    · exact (FreeLieDimension.associativeHigh I 1).sub_mem hu
        (FreeLieDimension.associativeExact_le_high I (by omega) hu1Exact)
    · simp only [u1, map_sub]
      rw [DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I
        hu1Exact, sub_self]
  have hr2 : r - r1 ∈ FreeLieDimension.associativeHigh I 2 := by
    apply DegreeFive.mem_associativeHigh_succ_of_component_eq_zero I
    · exact (FreeLieDimension.associativeHigh I 1).sub_mem hr
        (FreeLieDimension.associativeExact_le_high I (by omega) hr1Exact)
    · simp only [r1, map_sub]
      rw [DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I
        hr1Exact, sub_self]
  have hdiff : u * r - u1 * r1 ∈
      FreeLieDimension.associativeHigh I 3 := by
    rw [show u * r - u1 * r1 = (u - u1) * r + u1 * (r - r1) by
      noncomm_ring]
    apply (FreeLieDimension.associativeHigh I 3).add_mem
    · simpa using FreeLieDimension.associativeHigh_mul I hu2 hr
    · simpa using FreeLieDimension.associativeHigh_mul I
        (FreeLieDimension.associativeExact_le_high I (by omega) hu1Exact) hr2
  have hz := DegreeFive.associativeLengthComponent_eq_zero_of_mem_high I
    hdiff (by omega : 2 < 3)
  have hprodExact : u1 * r1 ∈
      FreeLieDimension.associativeExact I 2 := by
    simpa using FreeLieDimension.associativeExact_mul I hu1Exact hr1Exact
  have hcomp : DegreeFive.associativeLengthComponent I 2 (u1 * r1) =
      u1 * r1 :=
    DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I hprodExact
  rw [map_sub, hcomp] at hz
  simpa only [u1, r1] using sub_eq_zero.mp hz

/-- The degree-three part of a product of two positive-length elements. -/
private theorem associativeComponent_three_mul {I : Type*}
    (u r : FreeAlgebra ℤ I)
    (hu : u ∈ FreeLieDimension.associativeHigh I 1)
    (hr : r ∈ FreeLieDimension.associativeHigh I 1) :
    DegreeFive.associativeLengthComponent I 3 (u * r) =
      DegreeFive.associativeLengthComponent I 2 u *
          DegreeFive.associativeLengthComponent I 1 r +
        DegreeFive.associativeLengthComponent I 1 u *
          DegreeFive.associativeLengthComponent I 2 r := by
  let u1 := DegreeFive.associativeLengthComponent I 1 u
  let u2 := DegreeFive.associativeLengthComponent I 2 u
  let r1 := DegreeFive.associativeLengthComponent I 1 r
  let r2 := DegreeFive.associativeLengthComponent I 2 r
  have hu1Exact : u1 ∈ FreeLieDimension.associativeExact I 1 :=
    DegreeFive.associativeLengthComponent_mem_exact I 1 u
  have hu2Exact : u2 ∈ FreeLieDimension.associativeExact I 2 :=
    DegreeFive.associativeLengthComponent_mem_exact I 2 u
  have hr1Exact : r1 ∈ FreeLieDimension.associativeExact I 1 :=
    DegreeFive.associativeLengthComponent_mem_exact I 1 r
  have hr2Exact : r2 ∈ FreeLieDimension.associativeExact I 2 :=
    DegreeFive.associativeLengthComponent_mem_exact I 2 r
  have hu2High : u - u1 ∈ FreeLieDimension.associativeHigh I 2 := by
    apply DegreeFive.mem_associativeHigh_succ_of_component_eq_zero I
    · exact (FreeLieDimension.associativeHigh I 1).sub_mem hu
        (FreeLieDimension.associativeExact_le_high I (by omega) hu1Exact)
    · simp only [u1, map_sub]
      rw [DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I
        hu1Exact, sub_self]
  have hu3 : u - u1 - u2 ∈ FreeLieDimension.associativeHigh I 3 := by
    apply DegreeFive.mem_associativeHigh_succ_of_component_eq_zero I
    · exact (FreeLieDimension.associativeHigh I 2).sub_mem hu2High
        (FreeLieDimension.associativeExact_le_high I (by omega) hu2Exact)
    · simp only [u1, u2, map_sub]
      rw [DegreeFive.associativeLengthComponent_eq_zero_of_mem_exact_of_ne I
          hu1Exact (by omega),
        DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I hu2Exact]
      abel
  have hr2High : r - r1 ∈ FreeLieDimension.associativeHigh I 2 := by
    apply DegreeFive.mem_associativeHigh_succ_of_component_eq_zero I
    · exact (FreeLieDimension.associativeHigh I 1).sub_mem hr
        (FreeLieDimension.associativeExact_le_high I (by omega) hr1Exact)
    · simp only [r1, map_sub]
      rw [DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I
        hr1Exact, sub_self]
  have hr3 : r - r1 - r2 ∈ FreeLieDimension.associativeHigh I 3 := by
    apply DegreeFive.mem_associativeHigh_succ_of_component_eq_zero I
    · exact (FreeLieDimension.associativeHigh I 2).sub_mem hr2High
        (FreeLieDimension.associativeExact_le_high I (by omega) hr2Exact)
    · simp only [r1, r2, map_sub]
      rw [DegreeFive.associativeLengthComponent_eq_zero_of_mem_exact_of_ne I
          hr1Exact (by omega),
        DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I hr2Exact]
      abel
  have hdiff : u * r - u1 * r1 - (u2 * r1 + u1 * r2) ∈
      FreeLieDimension.associativeHigh I 4 := by
    rw [show u * r - u1 * r1 - (u2 * r1 + u1 * r2) =
        (u - u1 - u2) * r + u2 * (r - r1) +
          u1 * (r - r1 - r2) by noncomm_ring]
    apply (FreeLieDimension.associativeHigh I 4).add_mem
    · apply (FreeLieDimension.associativeHigh I 4).add_mem
      · simpa using FreeLieDimension.associativeHigh_mul I hu3 hr
      · simpa using FreeLieDimension.associativeHigh_mul I
          (FreeLieDimension.associativeExact_le_high I (by omega) hu2Exact)
          hr2High
    · simpa using FreeLieDimension.associativeHigh_mul I
        (FreeLieDimension.associativeExact_le_high I (by omega) hu1Exact) hr3
  have hz := DegreeFive.associativeLengthComponent_eq_zero_of_mem_high I
    hdiff (by omega : 3 < 4)
  rw [map_sub, map_sub,
    DegreeFive.associativeLengthComponent_eq_zero_of_mem_exact_of_ne I
      (FreeLieDimension.associativeExact_mul I hu1Exact hr1Exact) (by omega),
    DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I
      ((FreeLieDimension.associativeExact I 3).add_mem
        (by simpa using FreeLieDimension.associativeExact_mul I hu2Exact hr1Exact)
        (by simpa using FreeLieDimension.associativeExact_mul I hu1Exact hr2Exact))]
    at hz
  rw [sub_zero] at hz
  have heq := sub_eq_zero.mp hz
  simpa only [u1, u2, r1, r2] using heq

private theorem freeAlgebra_lift_word_mem_exact {I J : Type*}
    (g : I → FreeAlgebra ℤ J)
    (hg : ∀ i, g i ∈ FreeLieDimension.associativeExact J 1)
    (xs : List I) :
    (FreeAlgebra.lift ℤ g) (DegreeFive.freeAlgebraWord I xs) ∈
      FreeLieDimension.associativeExact J xs.length := by
  induction xs with
  | nil =>
      simp only [DegreeFive.freeAlgebraWord_nil, map_one, List.length_nil]
      intro w hw
      change w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (1 : FreeAlgebra ℤ J)).support at hw
      rw [map_one FreeAlgebra.equivMonoidAlgebraFreeMonoid] at hw
      have hw1 : w = 1 := by
        by_contra hne
        have hnz := Finsupp.mem_support_iff.mp hw
        apply hnz
        change (Finsupp.single 1 (1 : ℤ)) w = 0
        exact Finsupp.single_eq_of_ne hne
      subst w
      simp
  | cons i xs ih =>
      change (FreeAlgebra.lift ℤ g)
          (FreeAlgebra.ι ℤ i * DegreeFive.freeAlgebraWord I xs) ∈ _
      rw [map_mul, FreeAlgebra.lift_ι_apply]
      simpa [Nat.add_comm] using
        FreeLieDimension.associativeExact_mul J (hg i) ih

private theorem freeAlgebraWord_mem_exact {I : Type*} (xs : List I) :
    DegreeFive.freeAlgebraWord I xs ∈
      FreeLieDimension.associativeExact I xs.length := by
  have h := freeAlgebra_lift_word_mem_exact
    (fun i : I ↦ FreeAlgebra.ι ℤ i)
    (fun i ↦ FreeLieDimension.freeAlgebra_i_mem_associativeExact_one I i) xs
  have hlift : FreeAlgebra.lift ℤ (fun i : I ↦ FreeAlgebra.ι ℤ i) =
      AlgHom.id ℤ (FreeAlgebra ℤ I) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp
  rw [hlift] at h
  exact h

private theorem freeAlgebra_word_sum_eq {I : Type*}
    (p : FreeAlgebra ℤ I) :
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).sum
      (fun w n ↦ n • DegreeFive.freeAlgebraWord I
        (FreeMonoid.toList w)) = p := by
  classical
  obtain ⟨c, hc⟩ := DegreeFive.exists_freeAlgebra_word_finsupp I p
  have hcE : c = FreeAlgebra.equivMonoidAlgebraFreeMonoid p := by
    ext w
    have h' := congrArg FreeAlgebra.equivMonoidAlgebraFreeMonoid hc
    rw [map_finsuppSum] at h'
    have h := congrArg
      (fun a : MonoidAlgebra ℤ (FreeMonoid I) ↦ a w) h'
    simp only [map_smul, freeAlgebraWord_equiv,
      FreeMonoid.ofList_toList] at h
    have hsum : c.sum (fun a b ↦ b • Finsupp.single a 1) = c := by
      calc
        _ = c.sum Finsupp.single := by
          apply Finsupp.sum_congr
          intro a ha
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        _ = c := Finsupp.sum_single c
    calc
      c w = (c.sum (fun a b ↦ b • Finsupp.single a 1)) w :=
        congrArg (fun d : FreeMonoid I →₀ ℤ ↦ d w) hsum.symm
      _ = _ := h
  rw [← hcE]
  exact hc

private theorem freeAlgebra_lift_preserves_exact {I J : Type*}
    (g : I → FreeAlgebra ℤ J)
    (hg : ∀ i, g i ∈ FreeLieDimension.associativeExact J 1)
    {n : ℕ} {p : FreeAlgebra ℤ I}
    (hp : p ∈ FreeLieDimension.associativeExact I n) :
    (FreeAlgebra.lift ℤ g) p ∈
      FreeLieDimension.associativeExact J n := by
  classical
  rw [← freeAlgebra_word_sum_eq p, map_finsuppSum]
  apply Submodule.sum_mem
  intro w hw
  dsimp
  rw [map_smul]
  apply (FreeLieDimension.associativeExact J n).smul_mem
  have hwlen : w.length = n := hp hw
  have hword := freeAlgebra_lift_word_mem_exact g hg
    (FreeMonoid.toList w)
  simpa [FreeMonoid.length] using hwlen ▸ hword

private theorem freeAlgebra_lift_preserves_high {I J : Type*}
    (g : I → FreeAlgebra ℤ J)
    (hg : ∀ i, g i ∈ FreeLieDimension.associativeExact J 1)
    {n : ℕ} {p : FreeAlgebra ℤ I}
    (hp : p ∈ FreeLieDimension.associativeHigh I n) :
    (FreeAlgebra.lift ℤ g) p ∈
      FreeLieDimension.associativeHigh J n := by
  classical
  rw [← freeAlgebra_word_sum_eq p, map_finsuppSum]
  apply Submodule.sum_mem
  intro w hw
  dsimp
  rw [map_smul]
  apply (FreeLieDimension.associativeHigh J n).smul_mem
  have hword : (FreeAlgebra.lift ℤ g)
        (DegreeFive.freeAlgebraWord I (FreeMonoid.toList w)) ∈
      FreeLieDimension.associativeExact J w.length := by
    simpa [FreeMonoid.length] using
      freeAlgebra_lift_word_mem_exact g hg (FreeMonoid.toList w)
  exact FreeLieDimension.associativeExact_le_high J (hp hw) hword

private theorem freeAlgebra_lift_component {I J : Type*}
    (g : I → FreeAlgebra ℤ J)
    (hg : ∀ i, g i ∈ FreeLieDimension.associativeExact J 1)
    (n : ℕ) (p : FreeAlgebra ℤ I) :
    DegreeFive.associativeLengthComponent J n ((FreeAlgebra.lift ℤ g) p) =
      (FreeAlgebra.lift ℤ g)
        (DegreeFive.associativeLengthComponent I n p) := by
  classical
  rw [← freeAlgebra_word_sum_eq p, map_finsuppSum, map_finsuppSum,
    map_finsuppSum]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro w hw
  dsimp
  simp only [map_smul]
  by_cases hlen : w.length = n
  · have hsource : DegreeFive.freeAlgebraWord I (FreeMonoid.toList w) ∈
        FreeLieDimension.associativeExact I n := by
      simpa [FreeMonoid.length] using hlen ▸
        freeAlgebraWord_mem_exact (FreeMonoid.toList w)
    have htarget : (FreeAlgebra.lift ℤ g)
          (DegreeFive.freeAlgebraWord I (FreeMonoid.toList w)) ∈
        FreeLieDimension.associativeExact J n := by
      simpa [FreeMonoid.length] using hlen ▸
        freeAlgebra_lift_word_mem_exact g hg (FreeMonoid.toList w)
    rw [DegreeFive.associativeLengthComponent_eq_self_of_mem_exact J htarget,
      DegreeFive.associativeLengthComponent_eq_self_of_mem_exact I hsource]
  · have hsource : DegreeFive.freeAlgebraWord I (FreeMonoid.toList w) ∈
        FreeLieDimension.associativeExact I w.length := by
      simpa [FreeMonoid.length] using
        freeAlgebraWord_mem_exact (FreeMonoid.toList w)
    have htarget : (FreeAlgebra.lift ℤ g)
          (DegreeFive.freeAlgebraWord I (FreeMonoid.toList w)) ∈
        FreeLieDimension.associativeExact J w.length := by
      simpa [FreeMonoid.length] using
        freeAlgebra_lift_word_mem_exact g hg (FreeMonoid.toList w)
    rw [DegreeFive.associativeLengthComponent_eq_zero_of_mem_exact_of_ne J
        htarget hlen,
      DegreeFive.associativeLengthComponent_eq_zero_of_mem_exact_of_ne I
        hsource hlen,
      map_zero]


/-- The part of a weight-one Smith relation above its diagonal head. -/
def firstSmithTail [Finite L] (i : FirstSmithIndex L) : CanonicalFreeLie L :=
  (DegreeFive.collectedRelationRow L L
      (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L) -
    firstSmithDiagonal i • firstSmithGenerator i

/-- A weight-one Smith tail has free Lie weight at least two. -/
theorem firstSmithTail_mem_lieHigh_two [Finite L] (i : FirstSmithIndex L) :
    firstSmithTail i ∈ FreeLieDimension.lieHigh L 2 := by
  apply DegreeFive.mem_lieHigh_succ_of_component_eq_zero L
  · unfold firstSmithTail
    apply (FreeLieDimension.lieHigh L 1).sub_mem
    · exact DegreeFive.collectedRelationRow_mem_lieHigh L L
        (canonicalFreeLieEvaluation L) 1 i
    · apply (FreeLieDimension.lieHigh L 1).smul_mem
      exact DegreeFive.freeLieExact_mem_lieHigh L
        (DegreeFive.collectedHomogeneousBasis L L
          (canonicalFreeLieEvaluation L) 1 i)
  · rw [firstSmithTail, map_sub, map_zsmul]
    have hhead := DegreeFive.collectedRelationRow_head L L
      (canonicalFreeLieEvaluation L) 1 i
    have hheadval := congrArg Subtype.val hhead
    change DegreeFive.freeLieLengthComponent L 1
        (DegreeFive.collectedRelationRow L L
          (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L) =
      firstSmithDiagonal i •
        (DegreeFive.collectedHomogeneousBasis L L
          (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L) at hheadval
    rw [hheadval]
    change firstSmithDiagonal i •
        (DegreeFive.collectedHomogeneousBasis L L
          (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L) -
      firstSmithDiagonal i • DegreeFive.freeLieLengthComponent L 1
        (firstSmithGenerator i) = 0
    unfold firstSmithGenerator
    rw [DegreeFive.freeLieLengthComponent_coe_exact L 1]
    exact sub_self _

/-- The diagonal multiple of every weight-one Smith generator evaluates into `γ₂`. -/
theorem firstSmithDiagonal_smul_value_mem_gammaTwo [Finite L]
    (i : FirstSmithIndex L) :
    firstSmithDiagonal i • firstSmithValue i ∈ lowerCentralSeries ℤ L 1 := by
  have htailFree : firstSmithTail i ∈
      lowerCentralSeries ℤ (CanonicalFreeLie L) 1 := by
    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 1] using
      firstSmithTail_mem_lieHigh_two i
  have htail := (LieIdeal.map_lowerCentralSeries_le
    (R := ℤ) (f := canonicalFreeLieEvaluation L) 1)
      (LieIdeal.mem_map htailFree)
  have hrow := DegreeFive.collectedRelationRow_mem_ker L L
    (canonicalFreeLieEvaluation L) 1 i
  have heq : canonicalFreeLieEvaluation L (firstSmithTail i) =
      -(firstSmithDiagonal i • firstSmithValue i) := by
    rw [firstSmithTail, map_sub, map_zsmul, hrow, zero_sub]
    rfl
  rw [heq] at htail
  simpa using (lowerCentralSeries ℤ L 1).neg_mem htail

private theorem freeAlgebraToFirstSmith_preserves_high [Finite L]
    {n : ℕ} {p : FreeAlgebra ℤ L}
    (hp : p ∈ FreeLieDimension.associativeHigh L n) :
    freeAlgebraToFirstSmith (L := L) p ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) n := by
  change (FreeAlgebra.lift ℤ (fun z : L ↦
    ∑ i, originalGeneratorInFirstSmithCoordinates z i •
      FreeAlgebra.ι ℤ i)) p ∈ _
  apply freeAlgebra_lift_preserves_high _ _ hp
  intro z
  apply Submodule.sum_mem
  intro i hi
  exact (FreeLieDimension.associativeExact (FirstSmithIndex L) 1).smul_mem _
    (FreeLieDimension.freeAlgebra_i_mem_associativeExact_one
      (FirstSmithIndex L) i)

private theorem freeAlgebraToFirstSmith_preserves_exact [Finite L]
    {n : ℕ} {p : FreeAlgebra ℤ L}
    (hp : p ∈ FreeLieDimension.associativeExact L n) :
    freeAlgebraToFirstSmith (L := L) p ∈
      FreeLieDimension.associativeExact (FirstSmithIndex L) n := by
  change (FreeAlgebra.lift ℤ (fun z : L ↦
    ∑ i, originalGeneratorInFirstSmithCoordinates z i •
      FreeAlgebra.ι ℤ i)) p ∈ _
  apply freeAlgebra_lift_preserves_exact _ _ hp
  intro z
  apply Submodule.sum_mem
  intro i hi
  exact (FreeLieDimension.associativeExact (FirstSmithIndex L) 1).smul_mem _
    (FreeLieDimension.freeAlgebra_i_mem_associativeExact_one
      (FirstSmithIndex L) i)

private theorem freeAlgebraToFirstSmith_component [Finite L]
    (n : ℕ) (p : FreeAlgebra ℤ L) :
    DegreeFive.associativeLengthComponent (FirstSmithIndex L) n
        (freeAlgebraToFirstSmith (L := L) p) =
      freeAlgebraToFirstSmith (L := L)
        (DegreeFive.associativeLengthComponent L n p) := by
  apply freeAlgebra_lift_component
  intro z
  apply Submodule.sum_mem
  intro i hi
  exact (FreeLieDimension.associativeExact (FirstSmithIndex L) 1).smul_mem _
    (FreeLieDimension.freeAlgebra_i_mem_associativeExact_one
      (FirstSmithIndex L) i)

private theorem freeAlgebraFromFirstSmith_preserves_high [Finite L]
    {n : ℕ} {p : FreeAlgebra ℤ (FirstSmithIndex L)}
    (hp : p ∈ FreeLieDimension.associativeHigh (FirstSmithIndex L) n) :
    freeAlgebraFromFirstSmith (L := L) p ∈
      FreeLieDimension.associativeHigh L n := by
  change (FreeAlgebra.lift ℤ (fun i : FirstSmithIndex L ↦
    PBW.freeLieToFreeAlgebra ℤ L (firstSmithGenerator i))) p ∈ _
  apply freeAlgebra_lift_preserves_high _ _ hp
  intro i
  exact DegreeFive.freeLieToFreeAlgebra_mem_exact L
    (DegreeFive.collectedHomogeneousBasis L L
      (canonicalFreeLieEvaluation L) 1 i)

private theorem freeAlgebraFromFirstSmith_component [Finite L]
    (n : ℕ) (p : FreeAlgebra ℤ (FirstSmithIndex L)) :
    DegreeFive.associativeLengthComponent L n
        (freeAlgebraFromFirstSmith (L := L) p) =
      freeAlgebraFromFirstSmith (L := L)
        (DegreeFive.associativeLengthComponent (FirstSmithIndex L) n p) := by
  apply freeAlgebra_lift_component
  intro i
  exact DegreeFive.freeLieToFreeAlgebra_mem_exact L
    (DegreeFive.collectedHomogeneousBasis L L
      (canonicalFreeLieEvaluation L) 1 i)

/-- The enveloping algebra of the canonical free Lie ring, written in the
first Smith letters. -/
private def smithUEAEquiv [Finite L] :
    UEA ℤ (CanonicalFreeLie L) ≃ₐ[ℤ]
      FreeAlgebra ℤ (FirstSmithIndex L) :=
  (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L).trans
    (freeAlgebraFirstSmithEquiv (L := L))

@[simp]
private theorem smithUEAEquiv_iota_firstSmithGenerator [Finite L]
    (i : FirstSmithIndex L) :
    smithUEAEquiv (L := L) (UniversalEnvelopingAlgebra.ι ℤ
      (firstSmithGenerator i)) = FreeAlgebra.ι ℤ i := by
  change freeAlgebraToFirstSmith (L := L)
      ((FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
        (UniversalEnvelopingAlgebra.ι ℤ (firstSmithGenerator i))) = _
  have h := FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
    L (firstSmithGenerator i)
  calc
    _ = freeAlgebraToFirstSmith (L := L)
        (PBW.freeLieToFreeAlgebra ℤ L (firstSmithGenerator i)) :=
      congrArg (freeAlgebraToFirstSmith (L := L)) h
    _ = _ := freeAlgebraToFirstSmith_firstSmithGenerator i

private theorem smithUEAEquiv_mem_associativeHigh [Finite L]
    (n : ℕ) {u : UEA ℤ (CanonicalFreeLie L)}
    (hu : u ∈ UEA.augmentationIdeal ℤ (CanonicalFreeLie L) ^ n) :
    smithUEAEquiv (L := L) u ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) n := by
  change freeAlgebraToFirstSmith (L := L)
      ((FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L) u) ∈ _
  exact freeAlgebraToFirstSmith_preserves_high
    (FreeLieDimension.universalEnvelopingEquiv_mem_associativeHigh L n hu)

private theorem smithUEAEquiv_mem_associativeHigh_one [Finite L]
    {u : UEA ℤ (CanonicalFreeLie L)}
    (hu : u ∈ UEA.augmentationIdeal ℤ (CanonicalFreeLie L)) :
    smithUEAEquiv (L := L) u ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 1 := by
  change freeAlgebraToFirstSmith (L := L)
      ((FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L) u) ∈ _
  exact freeAlgebraToFirstSmith_preserves_high
    (FreeLieDimension.universalEnvelopingEquiv_mem_associativeHigh_one L hu)

/-- Passi's associative commutator ideal `a`. -/
private def associativeCommutatorIdeal (I : Type*) :
    Ideal (FreeAlgebra ℤ I) :=
  (TwoSidedIdeal.span (Set.range fun pq :
    FreeAlgebra ℤ I × FreeAlgebra ℤ I ↦
      pq.1 * pq.2 - pq.2 * pq.1)).asIdeal

/-- Passi's ideal `s`, generated by associative commutators and the diagonal
heads `e_i X_i`. -/
private def passiSIdeal [Finite L] :
    Ideal (FreeAlgebra ℤ (FirstSmithIndex L)) :=
  (TwoSidedIdeal.span (Set.range fun g :
    (FreeAlgebra ℤ (FirstSmithIndex L) ×
      FreeAlgebra ℤ (FirstSmithIndex L)) ⊕ FirstSmithIndex L ↦
      match g with
      | Sum.inl pq => pq.1 * pq.2 - pq.2 * pq.1
      | Sum.inr i => firstSmithDiagonal i • FreeAlgebra.ι ℤ i)).asIdeal

private theorem associativeCommutatorIdeal_le_passiSIdeal [Finite L] :
    associativeCommutatorIdeal (FirstSmithIndex L) ≤ passiSIdeal (L := L) := by
  intro z hz
  change z ∈ TwoSidedIdeal.span _ at hz ⊢
  apply TwoSidedIdeal.span_mono (s := Set.range fun pq :
    FreeAlgebra ℤ (FirstSmithIndex L) ×
      FreeAlgebra ℤ (FirstSmithIndex L) ↦
        pq.1 * pq.2 - pq.2 * pq.1) ?_ hz
  rintro z ⟨pq, rfl⟩
  exact ⟨Sum.inl pq, rfl⟩

private def smithLieImage [Finite L] (x : CanonicalFreeLie L) :
    FreeAlgebra ℤ (FirstSmithIndex L) :=
  freeAlgebraToFirstSmith (L := L) (PBW.freeLieToFreeAlgebra ℤ L x)

private theorem smithLieImage_mem_associativeCommutatorIdeal_of_mem_gammaTwo
    [Finite L] (x : CanonicalFreeLie L)
    (hx : x ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 1) :
    smithLieImage x ∈ associativeCommutatorIdeal (FirstSmithIndex L) := by
  have hx' : x ∈ Submodule.span ℤ
      {z : CanonicalFreeLie L |
        ∃ a ∈ (⊤ : LieIdeal ℤ (CanonicalFreeLie L)),
        ∃ b ∈ (⊤ : LieSubmodule ℤ (CanonicalFreeLie L)
          (CanonicalFreeLie L)), ⁅a, b⁆ = z} := by
    rw [← LieSubmodule.lieIdeal_oper_eq_linear_span'
      (⊤ : LieSubmodule ℤ (CanonicalFreeLie L) (CanonicalFreeLie L))
      (⊤ : LieIdeal ℤ (CanonicalFreeLie L))]
    change x ∈ LieModule.lowerCentralSeries ℤ
      (CanonicalFreeLie L) (CanonicalFreeLie L) 1 at hx
    simpa [LieModule.lowerCentralSeries_succ] using hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      simp only [smithLieImage, LieHom.map_lie]
      rw [LieRing.of_associative_ring_bracket, map_sub, map_mul, map_mul]
      change _ ∈ TwoSidedIdeal.span _
      exact TwoSidedIdeal.subset_span ⟨
        (freeAlgebraToFirstSmith (PBW.freeLieToFreeAlgebra ℤ L a),
          freeAlgebraToFirstSmith (PBW.freeLieToFreeAlgebra ℤ L b)), rfl⟩
  | zero => simp [smithLieImage]
  | add a b ha hb iha ihb =>
      simpa [smithLieImage] using
        (associativeCommutatorIdeal _).add_mem iha ihb
  | smul n a ha ih =>
      simpa [smithLieImage] using
        (associativeCommutatorIdeal _).smul_mem n ih

/-- Every defining relation belongs to Passi's `s` after changing to the
first Smith letters. -/
private theorem smithLieImage_relation_mem_passiSIdeal [Finite L]
    (r : DegreeFive.CanonicalLieRelationsIdeal L) :
    smithLieImage (r : CanonicalFreeLie L) ∈ passiSIdeal (L := L) := by
  rw [kernelRelation_eq_firstRows_add_gammaTwo r]
  simp only [smithLieImage, map_add, map_sum, map_zsmul]
  apply (passiSIdeal (L := L)).add_mem
  · apply Submodule.sum_mem
    intro i hi
    apply zsmul_mem
    have hrho :
        (DegreeFive.collectedRelationRow L L
          (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L) =
        firstSmithDiagonal i • firstSmithGenerator i + firstSmithTail i := by
      unfold firstSmithTail
      abel
    rw [hrho, map_add, map_zsmul, map_add, map_zsmul,
      freeAlgebraToFirstSmith_firstSmithGenerator]
    apply (passiSIdeal (L := L)).add_mem
    · change _ ∈ TwoSidedIdeal.span _
      exact TwoSidedIdeal.subset_span ⟨Sum.inr i, rfl⟩
    · apply associativeCommutatorIdeal_le_passiSIdeal
      apply smithLieImage_mem_associativeCommutatorIdeal_of_mem_gammaTwo
      simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 1] using
        firstSmithTail_mem_lieHigh_two i
  · apply associativeCommutatorIdeal_le_passiSIdeal
    apply smithLieImage_mem_associativeCommutatorIdeal_of_mem_gammaTwo
    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 1] using
      firstSmithRelationRemainder_mem_lieHigh_two r

private theorem smithUEAEquiv_iota [Finite L]
    (x : CanonicalFreeLie L) :
    smithUEAEquiv (L := L) (UniversalEnvelopingAlgebra.ι ℤ x) =
      smithLieImage x := by
  change freeAlgebraToFirstSmith (L := L)
      ((FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
        (UniversalEnvelopingAlgebra.ι ℤ x)) = _
  exact congrArg (freeAlgebraToFirstSmith (L := L))
    (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra L x)

/-- The exact ideal membership `Phi(iota(v)) ∈ A₄ + A₁s` obtained from
Passi's normalized relation equation. -/
private theorem NormalizedDimensionFourWitness.smithLieImage_mem_high_add
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    smithLieImage w.lieLift ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4 +
        FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1 *
          passiSIdeal (L := L) := by
  let A4 := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4
  let A1 := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1
  let S := passiSIdeal (L := L)
  have hsum : w.relationTerms.sum (fun p n ↦ n •
      ((smithUEAEquiv (L := L) p.1 -
          smithUEAEquiv (L := L)
            (algebraMap ℤ (UEA ℤ (CanonicalFreeLie L))
              (UEA.augmentation ℤ (CanonicalFreeLie L) p.1))) *
        smithLieImage (p.2 : CanonicalFreeLie L))) ∈ A1 * S := by
    apply Submodule.sum_mem
    intro p hp
    apply zsmul_mem
    apply Ideal.mul_mem_mul
    · have h := smithUEAEquiv_mem_associativeHigh_one
          (L := L) (w.multiplier_mem p hp)
      simpa only [map_sub] using h
    · exact smithLieImage_relation_mem_passiSIdeal p.2
  have hhigh : smithUEAEquiv (L := L) w.highWord ∈ A4 :=
    smithUEAEquiv_mem_associativeHigh 4 w.highWord_mem
  have heq := congrArg (smithUEAEquiv (L := L)) w.relationEquation
  rw [map_finsuppSum] at heq
  simp only [map_zsmul, map_mul, map_sub, smithUEAEquiv_iota] at heq
  have hvEq : smithLieImage w.lieLift =
      w.relationTerms.sum (fun p n ↦ n •
        ((smithUEAEquiv (L := L) p.1 -
            smithUEAEquiv (L := L)
              (algebraMap ℤ (UEA ℤ (CanonicalFreeLie L))
                (UEA.augmentation ℤ (CanonicalFreeLie L) p.1))) *
          smithLieImage (p.2 : CanonicalFreeLie L))) +
        smithUEAEquiv (L := L) w.highWord := by
    rw [heq]
    abel
  rw [hvEq]
  apply (A4 + A1 * S).add_mem
  · exact (show A1 * S ≤ A4 + A1 * S from le_sup_right) hsum
  · exact (show A4 ≤ A4 + A1 * S from le_sup_left) hhigh

private def NormalizedDimensionFourWitness.component
    {b : L} (w : NormalizedDimensionFourWitness b) (n : ℕ) :
    DegreeFive.freeLieExact L n :=
  ⟨DegreeFive.freeLieLengthComponent L n w.lieLift,
    DegreeFive.freeLieLengthComponent_mem_exact L n w.lieLift⟩

private theorem NormalizedDimensionFourWitness.lieLift_sub_components_mem_high_four
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    w.lieLift - (w.component 2 : CanonicalFreeLie L) -
        (w.component 3 : CanonicalFreeLie L) ∈
      FreeLieDimension.lieHigh L 4 := by
  have htwo : w.lieLift ∈ FreeLieDimension.lieHigh L 2 := by
    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 1] using
      w.lieLift_mem_gammaTwo
  have hcomponentTwo : DegreeFive.freeLieLengthComponent L 2
      (w.lieLift - (w.component 2 : CanonicalFreeLie L)) = 0 := by
    rw [map_sub]
    change DegreeFive.freeLieLengthComponent L 2 w.lieLift -
      DegreeFive.freeLieLengthComponent L 2
        (w.component 2 : CanonicalFreeLie L) = 0
    rw [DegreeFive.freeLieLengthComponent_coe_exact L 2]
    exact sub_self _
  have hthree : w.lieLift - (w.component 2 : CanonicalFreeLie L) ∈
      FreeLieDimension.lieHigh L 3 := by
    apply DegreeFive.mem_lieHigh_succ_of_component_eq_zero L
    · exact (FreeLieDimension.lieHigh L 2).sub_mem htwo
        (DegreeFive.freeLieExact_mem_lieHigh L (w.component 2))
    · exact hcomponentTwo
  apply DegreeFive.mem_lieHigh_succ_of_component_eq_zero L
  · exact (FreeLieDimension.lieHigh L 3).sub_mem hthree
      (DegreeFive.freeLieExact_mem_lieHigh L (w.component 3))
  · calc
      DegreeFive.freeLieLengthComponent L 3
          (w.lieLift - (w.component 2 : CanonicalFreeLie L) -
            (w.component 3 : CanonicalFreeLie L)) =
          DegreeFive.freeLieLengthComponent L 3 w.lieLift -
            DegreeFive.freeLieLengthComponent L 3
              (w.component 2 : CanonicalFreeLie L) -
            DegreeFive.freeLieLengthComponent L 3
              (w.component 3 : CanonicalFreeLie L) := by
        rw [map_sub, map_sub]
      _ = DegreeFive.freeLieLengthComponent L 3 w.lieLift - 0 -
            (w.component 3 : CanonicalFreeLie L) := by
        rw [DegreeFive.freeLieLengthComponent_coe_exact_of_ne L
            (w.component 2) (by omega),
          DegreeFive.freeLieLengthComponent_coe_exact L 3]
      _ = 0 := by
        change DegreeFive.freeLieLengthComponent L 3 w.lieLift - 0 -
          DegreeFive.freeLieLengthComponent L 3 w.lieLift = 0
        abel

private theorem NormalizedDimensionFourWitness.components_mem_high_add
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    smithLieImage ((w.component 2 : CanonicalFreeLie L) +
        (w.component 3 : CanonicalFreeLie L)) ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4 +
        FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1 *
          passiSIdeal (L := L) := by
  let H := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4 +
    FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1 *
      passiSIdeal (L := L)
  let r : CanonicalFreeLie L :=
    w.lieLift - (w.component 2 : CanonicalFreeLie L) -
      (w.component 3 : CanonicalFreeLie L)
  have hrHigh : smithLieImage r ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 4 := by
    apply freeAlgebraToFirstSmith_preserves_high
    exact DegreeFive.freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh L
      w.lieLift_sub_components_mem_high_four
  have hrH : smithLieImage r ∈ H :=
    (show FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4 ≤ H
      from le_sup_left) hrHigh
  have hvH : smithLieImage w.lieLift ∈ H :=
    w.smithLieImage_mem_high_add
  have hdecomp : w.lieLift =
      ((w.component 2 : CanonicalFreeLie L) +
        (w.component 3 : CanonicalFreeLie L)) + r := by
    simp only [r]
    abel
  rw [hdecomp] at hvH
  simp only [smithLieImage, map_add] at hvH
  simpa only [smithLieImage, map_add, add_sub_cancel_right] using
    H.sub_mem hvH hrH

private theorem exists_forwardBracketCoordinates [Finite L]
    (x : DegreeFive.freeLieExact L 2) :
    ∃ a : FirstSmithIndex L → FirstSmithIndex L → ℤ,
      (x : CanonicalFreeLie L) =
        ∑ i, ∑ j, if i < j then
          a i j • ⁅firstSmithGenerator i, firstSmithGenerator j⁆ else 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_strictBracketCoordinates x
  refine ⟨fun i j ↦ -a j i, ?_⟩
  rw [ha]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, if_true]
    rw [show ⁅firstSmithGenerator j, firstSmithGenerator i⁆ =
        -⁅firstSmithGenerator i, firstSmithGenerator j⁆ by
      exact (lie_skew (firstSmithGenerator j)
        (firstSmithGenerator i)).symm]
    module
  · simp only [hij, if_false]

private def NormalizedDimensionFourWitness.cutoffQuadraticCoefficients
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    FirstSmithIndex L → FirstSmithIndex L → ℤ :=
  Classical.choose (exists_forwardBracketCoordinates (w.component 2))

private theorem NormalizedDimensionFourWitness.component_two_eq_cutoff
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    (w.component 2 : CanonicalFreeLie L) =
      ∑ i, ∑ j, if i < j then
        w.cutoffQuadraticCoefficients i j •
          ⁅firstSmithGenerator i, firstSmithGenerator j⁆ else 0 :=
  Classical.choose_spec (exists_forwardBracketCoordinates (w.component 2))

private def NormalizedDimensionFourWitness.cubicCoefficients
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    FirstSmithIndex L → FirstSmithIndex L → FirstSmithIndex L → ℤ :=
  Classical.choose (exists_normalizedTripleCoordinates (w.component 3))

private theorem NormalizedDimensionFourWitness.component_three_eq_cutoff
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    (w.component 3 : CanonicalFreeLie L) =
      ∑ i, ∑ j, ∑ k, if i < j ∧ i ≤ k then
        w.cubicCoefficients i j k •
          ⁅⁅firstSmithGenerator i, firstSmithGenerator j⁆,
            firstSmithGenerator k⁆ else 0 :=
  Classical.choose_spec (exists_normalizedTripleCoordinates (w.component 3))

private def NormalizedDimensionFourWitness.cutoffTerm [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b) (i : FirstSmithIndex L) :
    CanonicalFreeLie L :=
  (∑ j, if i < j then w.cutoffQuadraticCoefficients i j •
      ⁅firstSmithGenerator i, firstSmithGenerator j⁆ else 0) +
    ∑ j, ∑ k, if i < j ∧ i ≤ k then w.cubicCoefficients i j k •
      ⁅⁅firstSmithGenerator i, firstSmithGenerator j⁆,
        firstSmithGenerator k⁆ else 0

private theorem NormalizedDimensionFourWitness.sum_cutoffTerm [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b) :
    (w.component 2 : CanonicalFreeLie L) +
        (w.component 3 : CanonicalFreeLie L) =
      ∑ i, w.cutoffTerm i := by
  rw [w.component_two_eq_cutoff, w.component_three_eq_cutoff]
  simp only [NormalizedDimensionFourWitness.cutoffTerm,
    Finset.sum_add_distrib]

/-- A cutoff of the Smith letters.  Passi's two maps `theta_ge_i` and
`theta_gt_i` are the instances with predicates `i ≤ ·` and `i < ·`. -/
private def letterCutoff {I : Type*} (P : I → Prop) [DecidablePred P] :
    FreeAlgebra ℤ I →ₐ[ℤ] FreeAlgebra ℤ I :=
  FreeAlgebra.lift ℤ fun j ↦ if P j then FreeAlgebra.ι ℤ j else 0

@[simp]
private theorem letterCutoff_iota {I : Type*} (P : I → Prop)
    [DecidablePred P] (j : I) :
    letterCutoff P (FreeAlgebra.ι ℤ j) =
      if P j then FreeAlgebra.ι ℤ j else 0 := by
  rw [letterCutoff, FreeAlgebra.lift_ι_apply]

private theorem letterCutoff_preserves_high {I : Type*}
    (P : I → Prop) [DecidablePred P] {n : ℕ} {p : FreeAlgebra ℤ I}
    (hp : p ∈ FreeLieDimension.associativeHigh I n) :
    letterCutoff P p ∈ FreeLieDimension.associativeHigh I n := by
  apply freeAlgebra_lift_preserves_high _ _ hp
  intro j
  by_cases hj : P j
  · rw [if_pos hj]
    exact FreeLieDimension.freeAlgebra_i_mem_associativeExact_one I j
  · rw [if_neg hj]
    exact (FreeLieDimension.associativeExact I 1).zero_mem

private theorem letterCutoff_mem_passiSIdeal [Finite L]
    (P : FirstSmithIndex L → Prop) [DecidablePred P]
    {p : FreeAlgebra ℤ (FirstSmithIndex L)}
    (hp : p ∈ passiSIdeal (L := L)) :
    letterCutoff P p ∈ passiSIdeal (L := L) := by
  change p ∈ TwoSidedIdeal.span _ at hp
  induction hp using TwoSidedIdeal.span_induction with
  | mem z hz =>
      obtain ⟨g, rfl⟩ := hz
      cases g with
      | inl pq =>
          rw [map_sub, map_mul, map_mul]
          change _ ∈ TwoSidedIdeal.span _
          exact TwoSidedIdeal.subset_span ⟨Sum.inl
            (letterCutoff P pq.1, letterCutoff P pq.2), rfl⟩
      | inr i =>
          rw [map_zsmul, letterCutoff_iota]
          by_cases hi : P i
          · rw [if_pos hi]
            change _ ∈ TwoSidedIdeal.span _
            exact TwoSidedIdeal.subset_span ⟨Sum.inr i, rfl⟩
          · rw [if_neg hi, smul_zero]
            exact (passiSIdeal (L := L)).zero_mem
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (passiSIdeal (L := L)).add_mem ihx ihy
  | neg x hx ih =>
      rw [map_neg]
      exact (passiSIdeal (L := L)).neg_mem ih
  | left_absorb a x hx ih =>
      rw [map_mul]
      exact (passiSIdeal (L := L)).mul_mem_left _ ih
  | right_absorb a x hx ih =>
    rw [map_mul]
    change _ ∈ TwoSidedIdeal.span _
    exact (TwoSidedIdeal.span _).mul_mem_right _ _ ih

private theorem letterCutoff_mem_high_add [Finite L]
    (P : FirstSmithIndex L → Prop) [DecidablePred P]
    {p : FreeAlgebra ℤ (FirstSmithIndex L)}
    (hp : p ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4 +
        FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1 *
          passiSIdeal (L := L)) :
    letterCutoff P p ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4 +
        FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1 *
          passiSIdeal (L := L) := by
  let A4 := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4
  let A1 := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1
  let S := passiSIdeal (L := L)
  change p ∈ A4 ⊔ A1 * S at hp
  rw [Submodule.mem_sup] at hp
  obtain ⟨p4, hp4, p1s, hp1s, rfl⟩ := hp
  rw [map_add]
  apply (A4 + A1 * S).add_mem
  · exact (show A4 ≤ A4 + A1 * S from le_sup_left)
      (letterCutoff_preserves_high P hp4)
  · apply (show A1 * S ≤ A4 + A1 * S from le_sup_right)
    refine Submodule.mul_induction_on hp1s ?_ ?_
    · intro a ha s hs
      rw [map_mul]
      exact Ideal.mul_mem_mul (letterCutoff_preserves_high P ha)
        (letterCutoff_mem_passiSIdeal P hs)
    · intro x y hx hy
      rw [map_add]
      exact (A1 * S).add_mem hx hy

@[simp]
private theorem freeAlgebraToFirstSmith_lie [Finite L]
    (x y : FreeAlgebra ℤ L) :
    freeAlgebraToFirstSmith (L := L) ⁅x, y⁆ =
      ⁅freeAlgebraToFirstSmith (L := L) x,
        freeAlgebraToFirstSmith (L := L) y⁆ := by
  rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket,
    map_sub, map_mul, map_mul]

private theorem smithLieImage_cutoffTerm [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    smithLieImage (w.cutoffTerm i) =
      (∑ j, if i < j then w.cutoffQuadraticCoefficients i j •
        ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ j⁆ else 0) +
      ∑ j, ∑ k, if i < j ∧ i ≤ k then w.cubicCoefficients i j k •
        ⁅⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ j⁆,
          FreeAlgebra.ι ℤ k⁆ else 0 := by
  simp only [NormalizedDimensionFourWitness.cutoffTerm, smithLieImage,
    map_add, map_sum, apply_ite, map_zsmul, map_zero, LieHom.map_lie,
    freeAlgebraToFirstSmith_lie,
    freeAlgebraToFirstSmith_firstSmithGenerator]

@[simp]
private theorem letterCutoff_lie {I : Type*} (P : I → Prop)
    [DecidablePred P] (x y : FreeAlgebra ℤ I) :
    letterCutoff P ⁅x, y⁆ = ⁅letterCutoff P x, letterCutoff P y⁆ := by
  rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket,
    map_sub, map_mul, map_mul]

private theorem letterCutoff_ge_cutoffTerm [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i l : FirstSmithIndex L) :
    letterCutoff (fun j ↦ i ≤ j) (smithLieImage (w.cutoffTerm l)) =
      if i ≤ l then smithLieImage (w.cutoffTerm l) else 0 := by
  classical
  rw [smithLieImage_cutoffTerm]
  simp only [map_add, map_sum, apply_ite, map_zsmul, map_zero,
    letterCutoff_lie, letterCutoff_iota]
  by_cases hil : i ≤ l
  · rw [if_pos hil]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hlj : l < j
      · simp [hlj, hil, hil.trans hlj.le]
      · simp [hlj]
    · apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hgood : l < j ∧ l ≤ k
      · simp [hgood, hil, hil.trans hgood.1.le, hil.trans hgood.2]
      · simp [hgood]
  · rw [if_neg hil]
    simp [hil, letterCutoff_lie]

private theorem letterCutoff_gt_cutoffTerm [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i l : FirstSmithIndex L) :
    letterCutoff (fun j ↦ i < j) (smithLieImage (w.cutoffTerm l)) =
      if i < l then smithLieImage (w.cutoffTerm l) else 0 := by
  classical
  rw [smithLieImage_cutoffTerm]
  simp only [map_add, map_sum, apply_ite, map_zsmul, map_zero,
    letterCutoff_lie, letterCutoff_iota]
  by_cases hil : i < l
  · rw [if_pos hil]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hlj : l < j
      · simp [hlj, hil, hil.trans hlj]
      · simp [hlj]
    · apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hgood : l < j ∧ l ≤ k
      · have hik : i < k := hil.trans_le hgood.2
        simp [hgood, hil, hil.trans hgood.1, hik]
      · simp [hgood]
  · rw [if_neg hil]
    simp [hil, letterCutoff_lie]

private theorem NormalizedDimensionFourWitness.cutoffTerm_mem_high_add
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    smithLieImage (w.cutoffTerm i) ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4 +
        FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1 *
          passiSIdeal (L := L) := by
  let H := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4 +
    FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1 *
      passiSIdeal (L := L)
  have htotal : (∑ l, smithLieImage (w.cutoffTerm l)) ∈ H := by
    have h := w.components_mem_high_add
    rw [w.sum_cutoffTerm] at h
    simpa only [smithLieImage, map_sum] using h
  have hge := letterCutoff_mem_high_add (fun j ↦ i ≤ j) htotal
  have hgt := letterCutoff_mem_high_add (fun j ↦ i < j) htotal
  rw [map_sum] at hge hgt
  simp_rw [letterCutoff_ge_cutoffTerm] at hge
  simp_rw [letterCutoff_gt_cutoffTerm] at hgt
  have hdiff :
      (∑ l, if i ≤ l then smithLieImage (w.cutoffTerm l) else 0) -
        (∑ l, if i < l then smithLieImage (w.cutoffTerm l) else 0) =
      smithLieImage (w.cutoffTerm i) := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · simp
    · intro l hl hli
      by_cases hil : i < l
      · simp [hil, hil.le]
      · have hnle : ¬ i ≤ l := fun hle ↦ hil (lt_of_le_of_ne hle hli.symm)
        simp [hil, hnle]
    · intro hi
      simp at hi
  rw [← hdiff]
  exact H.sub_mem hge hgt

/-- The positive-degree part of Passi's coefficient `u_ij`. -/
private def NormalizedDimensionFourWitness.passiUPositive [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i j : FirstSmithIndex L) :
    FreeAlgebra ℤ (FirstSmithIndex L) :=
  ∑ k, if i ≤ k then
    w.cubicCoefficients i j k • FreeAlgebra.ι ℤ k else 0

/-- Passi's coefficient
`u_ij = aCut_ij + sum_(k ≥ i) b_ijk X_k`. -/
private def NormalizedDimensionFourWitness.passiU [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i j : FirstSmithIndex L) :
    FreeAlgebra ℤ (FirstSmithIndex L) :=
  w.cutoffQuadraticCoefficients i j • 1 + w.passiUPositive i j

private theorem NormalizedDimensionFourWitness.smithLieImage_cutoffTerm_eq
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    smithLieImage (w.cutoffTerm i) =
      ∑ j, if i < j then
        ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ j⁆ * w.passiU i j -
          w.passiUPositive i j *
            ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ j⁆
        else 0 := by
  classical
  rw [smithLieImage_cutoffTerm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij, if_true, NormalizedDimensionFourWitness.passiU,
      NormalizedDimensionFourWitness.passiUPositive]
    simp only [true_and]
    let C : FreeAlgebra ℤ (FirstSmithIndex L) :=
      ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ j⁆
    change w.cutoffQuadraticCoefficients i j • C +
        (∑ k, if i ≤ k then w.cubicCoefficients i j k •
          ⁅C, FreeAlgebra.ι ℤ k⁆ else 0) =
      C * (w.cutoffQuadraticCoefficients i j • 1 +
        ∑ k, if i ≤ k then w.cubicCoefficients i j k •
          FreeAlgebra.ι ℤ k else 0) -
      (∑ k, if i ≤ k then w.cubicCoefficients i j k •
        FreeAlgebra.ι ℤ k else 0) * C
    rw [mul_add, Finset.mul_sum, Finset.sum_mul]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul]
    have hscalar : C * (w.cutoffQuadraticCoefficients i j • 1) =
        w.cutoffQuadraticCoefficients i j • C := by
      rw [mul_smul_comm, mul_one]
    rw [hscalar]
    rw [show w.cutoffQuadraticCoefficients i j • C +
          (∑ k, if i ≤ k then C *
            (w.cubicCoefficients i j k • FreeAlgebra.ι ℤ k) else 0) -
          (∑ k, if i ≤ k then
            (w.cubicCoefficients i j k • FreeAlgebra.ι ℤ k) * C else 0) =
        w.cutoffQuadraticCoefficients i j • C +
          ((∑ k, if i ≤ k then C *
              (w.cubicCoefficients i j k • FreeAlgebra.ι ℤ k) else 0) -
            (∑ k, if i ≤ k then
              (w.cubicCoefficients i j k • FreeAlgebra.ι ℤ k) * C else 0)) by
      abel]
    rw [← Finset.sum_sub_distrib]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hik : i ≤ k
    · simp only [hik, if_true]
      rw [LieRing.of_associative_ring_bracket, smul_sub,
        smul_mul_assoc, mul_smul_comm]
    · simp [hik]
  · simp [hij]

private theorem NormalizedDimensionFourWitness.passiUPositive_mem_high_one
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i j : FirstSmithIndex L) :
    w.passiUPositive i j ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 1 := by
  classical
  apply Submodule.sum_mem
  intro k hk
  by_cases hik : i ≤ k
  · simp only [NormalizedDimensionFourWitness.passiUPositive, hik, if_true]
    apply zsmul_mem
    exact fun v hv ↦
      (FreeLieDimension.freeAlgebra_i_mem_associativeExact_one
        (FirstSmithIndex L) k hv).ge
  · simp [NormalizedDimensionFourWitness.passiUPositive, hik]

/-- Passi's equation (3), obtained by discarding exactly the positive-degree
right commutator term and then taking the `j`-th free right-module
coordinate. -/
private theorem NormalizedDimensionFourWitness.passiThree
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    {i j : FirstSmithIndex L} (hij : i < j) :
    FreeAlgebra.ι ℤ i * w.passiU i j ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
        passiSIdeal (L := L) := by
  classical
  let A4 := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 4
  let A3 := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3
  let A1 := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 1
  let S := passiSIdeal (L := L)
  let main : FreeAlgebra ℤ (FirstSmithIndex L) :=
    ∑ l, if i < l then
      ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ l⁆ * w.passiU i l else 0
  let omitted : FreeAlgebra ℤ (FirstSmithIndex L) :=
    ∑ l, if i < l then
      w.passiUPositive i l *
        ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ l⁆ else 0
  have homitted : omitted ∈ A1 * S := by
    apply Submodule.sum_mem
    intro l hl
    by_cases hil : i < l
    · simp only [omitted, hil, if_true]
      apply Ideal.mul_mem_mul
      · exact w.passiUPositive_mem_high_one i l
      · apply associativeCommutatorIdeal_le_passiSIdeal
        change _ ∈ TwoSidedIdeal.span _
        rw [LieRing.of_associative_ring_bracket]
        exact TwoSidedIdeal.subset_span ⟨
          (FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ l), rfl⟩
    · simp [omitted, hil]
  have hmain : main ∈ A4 + A1 * S := by
    have hcut := w.cutoffTerm_mem_high_add i
    rw [w.smithLieImage_cutoffTerm_eq i] at hcut
    have hsplit :
        (∑ l, if i < l then
          ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ l⁆ * w.passiU i l -
            w.passiUPositive i l *
              ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ l⁆ else 0) =
          main - omitted := by
      change (∑ l, if i < l then
          ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ l⁆ * w.passiU i l -
            w.passiUPositive i l *
              ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ l⁆ else 0) =
        (∑ l, if i < l then
          ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ l⁆ * w.passiU i l else 0) -
        ∑ l, if i < l then w.passiUPositive i l *
          ⁅FreeAlgebra.ι ℤ i, FreeAlgebra.ι ℤ l⁆ else 0
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hil : i < l <;> simp [hil]
    rw [hsplit] at hcut
    have homitted' : omitted ∈ A4 + A1 * S :=
      (show A1 * S ≤ A4 + A1 * S from le_sup_right) homitted
    simpa only [sub_add_cancel] using (A4 + A1 * S).add_mem hcut homitted'
  have hcoeff : rightCoeff j main ∈ A3 + S := by
    change main ∈ A4 ⊔ A1 * S at hmain
    rw [Submodule.mem_sup] at hmain
    obtain ⟨p4, hp4, p1s, hp1s, heq⟩ := hmain
    rw [← heq, map_add]
    apply (A3 + S).add_mem
    · exact (show A3 ≤ A3 + S from le_sup_left)
        (rightCoeff_mem_associativeHigh j 3 p4 hp4)
    · apply (show S ≤ A3 + S from le_sup_right)
      refine Submodule.mul_induction_on hp1s ?_ ?_
      · intro a ha s hs
        rw [rightCoeff_mul j a s ha]
        exact S.mul_mem_left _ hs
      · intro x y hx hy
        rw [map_add]
        exact S.add_mem hx hy
  have hright : rightCoeff j main =
      -(FreeAlgebra.ι ℤ i * w.passiU i j) := by
    simp only [main, map_sum, apply_ite, map_zero]
    rw [Finset.sum_eq_single j]
    · simp only [hij, if_true]
      rw [LieRing.of_associative_ring_bracket, sub_mul, map_sub]
      simp only [mul_assoc, rightCoeff_iota_mul]
      simp [hij.ne', hij]
    · intro l hl hlj
      by_cases hil : i < l
      · simp only [hil, if_true]
        rw [LieRing.of_associative_ring_bracket, sub_mul, map_sub]
        simp only [mul_assoc, rightCoeff_iota_mul]
        simp [hij.ne', hlj.symm]
      · simp [hil]
    · intro hj
      simp at hj
  rw [hright] at hcoeff
  simpa only [neg_neg] using (A3 + S).neg_mem hcoeff

/-- The exact modulus of the two diagonal heads occurring in Passi's
coefficient comparison. -/
private def passiGCD [Finite L] (i k : FirstSmithIndex L) : ℕ :=
  Nat.gcd
    (DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 i)
    (DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 k)

/-- Passi's commutative polynomial probe, retaining only `X_i` and `X_k`
and reducing coefficients modulo their diagonal gcd. -/
private def passiPolynomialProbe [Finite L]
    (i k : FirstSmithIndex L) :
    FreeAlgebra ℤ (FirstSmithIndex L) →ₐ[ℤ]
      MvPolynomial (FirstSmithIndex L) (ZMod (passiGCD i k)) :=
  FreeAlgebra.lift ℤ fun l ↦
    if l = i ∨ l = k then MvPolynomial.X l else 0

private theorem firstSmithDiagonal_cast_mod_passiGCD_left [Finite L]
    (i k : FirstSmithIndex L) :
    (firstSmithDiagonal i : ZMod (passiGCD i k)) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold passiGCD firstSmithDiagonal
  exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)

private theorem firstSmithDiagonal_cast_mod_passiGCD_right [Finite L]
    (i k : FirstSmithIndex L) :
    (firstSmithDiagonal k : ZMod (passiGCD i k)) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold passiGCD firstSmithDiagonal
  exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)

private theorem passiPolynomialProbe_mem_s_eq_zero [Finite L]
    (i k : FirstSmithIndex L)
    {p : FreeAlgebra ℤ (FirstSmithIndex L)}
    (hp : p ∈ passiSIdeal (L := L)) :
    passiPolynomialProbe i k p = 0 := by
  classical
  change p ∈ TwoSidedIdeal.span _ at hp
  induction hp using TwoSidedIdeal.span_induction with
  | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      cases g with
      | inl pq =>
          simp only [map_sub, map_mul]
          rw [mul_comm, sub_self]
      | inr l =>
          simp only [map_zsmul, passiPolynomialProbe,
            FreeAlgebra.lift_ι_apply]
          by_cases hl : l = i ∨ l = k
          · rcases hl with hli | hlk
            · subst l
              rw [if_pos (Or.inl rfl),
                ← Int.cast_smul_eq_zsmul (ZMod (passiGCD i k)),
                firstSmithDiagonal_cast_mod_passiGCD_left, zero_smul]
            · subst l
              rw [if_pos (Or.inr rfl),
                ← Int.cast_smul_eq_zsmul (ZMod (passiGCD i k)),
                firstSmithDiagonal_cast_mod_passiGCD_right, zero_smul]
          · simp [hl]
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | neg x hx ih => simp [ih]
  | left_absorb a x hx ih => simp [ih]
  | right_absorb a x hx ih => simp [ih]

private def passiProbeExponent [Finite L]
    (i k : FirstSmithIndex L) : FirstSmithIndex L →₀ ℕ :=
  Finsupp.single i 1 + Finsupp.single k 1

/-- A word of length at least three has zero quadratic coefficient after
the two-letter polynomial probe.  This is the only word-length fact about
the polynomial target used in the proof. -/
private theorem passiPolynomialProbe_word_coeff_eq_zero [Finite L]
    (i k : FirstSmithIndex L) (xs : List (FirstSmithIndex L))
    (hxs : 3 ≤ xs.length) :
    MvPolynomial.coeff (passiProbeExponent i k)
      (passiPolynomialProbe i k
        (DegreeFive.freeAlgebraWord (FirstSmithIndex L) xs)) = 0 := by
  classical
  by_cases hall : ∀ l ∈ xs, l = i ∨ l = k
  · have hmap : passiPolynomialProbe i k
        (DegreeFive.freeAlgebraWord (FirstSmithIndex L) xs) =
        (xs.map (MvPolynomial.X : FirstSmithIndex L →
          MvPolynomial (FirstSmithIndex L) (ZMod (passiGCD i k)))).prod := by
      clear hxs
      induction xs with
      | nil => simp
      | cons l ls ih =>
          have hl : l = i ∨ l = k := hall l (by simp)
          have hls : ∀ x ∈ ls, x = i ∨ x = k := by
            intro x hx
            exact hall x (by simp [hx])
          simp only [DegreeFive.freeAlgebraWord_cons, map_mul,
            List.map_cons, List.prod_cons, passiPolynomialProbe,
            FreeAlgebra.lift_ι_apply]
          rw [if_pos hl]
          congr 1
          exact ih hls
    have hprod (ys : List (FirstSmithIndex L)) :
        (ys.map (MvPolynomial.X : FirstSmithIndex L →
          MvPolynomial (FirstSmithIndex L) (ZMod (passiGCD i k)))).prod =
        MvPolynomial.monomial
          (Multiset.toFinsupp (ys : Multiset (FirstSmithIndex L))) 1 := by
      induction ys with
      | nil => simp
      | cons l ls ih =>
          rw [List.map_cons, List.prod_cons, ih]
          rw [show Multiset.toFinsupp
                ((l :: ls : List (FirstSmithIndex L)) :
                  Multiset (FirstSmithIndex L)) =
              Multiset.toFinsupp
                  (ls : Multiset (FirstSmithIndex L)) +
                Finsupp.single l 1 by
            ext m
            by_cases hml : m = l
            · subst m
              simp
            · simp [hml, Ne.symm hml]]
          rw [MvPolynomial.monomial_add_single]
          simp [mul_comm]
    rw [hmap, hprod, MvPolynomial.coeff_monomial, if_neg]
    intro heq
    have hsum := congrArg
      (fun e : FirstSmithIndex L →₀ ℕ ↦ e.sum fun _ n ↦ n) heq
    have hcard : (Multiset.toFinsupp
        (xs : Multiset (FirstSmithIndex L))).sum (fun _ n ↦ n) =
        xs.length := by
      simpa only [id_eq] using Multiset.toFinsupp_sum_eq
        (xs : Multiset (FirstSmithIndex L))
    change (Multiset.toFinsupp
        (xs : Multiset (FirstSmithIndex L))).sum (fun _ n ↦ n) =
      (passiProbeExponent i k).sum (fun _ n ↦ n) at hsum
    rw [hcard] at hsum
    simp [passiProbeExponent, Finsupp.sum_add_index] at hsum
    omega
  · push_neg at hall
    obtain ⟨l, hlxs, hl⟩ := hall
    obtain ⟨as, bs, hdecomp, has⟩ := List.eq_append_cons_of_mem hlxs
    rw [hdecomp, DegreeFive.freeAlgebraWord_append,
      DegreeFive.freeAlgebraWord_cons, map_mul, map_mul,
      passiPolynomialProbe, FreeAlgebra.lift_ι_apply]
    rw [if_neg (not_or.mpr hl)]
    simp

private theorem passiPolynomialProbe_high_coeff_eq_zero [Finite L]
    (i k : FirstSmithIndex L)
    {p : FreeAlgebra ℤ (FirstSmithIndex L)}
    (hp : p ∈ FreeLieDimension.associativeHigh (FirstSmithIndex L) 3) :
    MvPolynomial.coeff (passiProbeExponent i k)
      (passiPolynomialProbe i k p) = 0 := by
  classical
  rw [← freeAlgebra_word_sum_eq p, map_finsuppSum]
  simp only [map_zsmul]
  change (MvPolynomial.lcoeff (ZMod (passiGCD i k))
      (passiProbeExponent i k))
    ((FreeAlgebra.equivMonoidAlgebraFreeMonoid p).sum
      (fun w n ↦ n • passiPolynomialProbe i k
        (DegreeFive.freeAlgebraWord (FirstSmithIndex L)
          (FreeMonoid.toList w)))) = 0
  rw [map_finsuppSum]
  apply Finset.sum_eq_zero
  intro w hw
  dsimp
  change (MvPolynomial.lcoeff (ZMod (passiGCD i k))
      (passiProbeExponent i k))
    ((FreeAlgebra.equivMonoidAlgebraFreeMonoid p) w •
      passiPolynomialProbe i k
        (DegreeFive.freeAlgebraWord (FirstSmithIndex L)
          (FreeMonoid.toList w))) = 0
  rw [map_zsmul]
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) w •
      MvPolynomial.coeff (passiProbeExponent i k)
        (passiPolynomialProbe i k
          (DegreeFive.freeAlgebraWord (FirstSmithIndex L)
            (FreeMonoid.toList w))) = 0
  rw [passiPolynomialProbe_word_coeff_eq_zero, smul_zero]
  simpa [FreeMonoid.length] using hp hw

private theorem NormalizedDimensionFourWitness.passiU_probe_coefficient
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    {i j k : FirstSmithIndex L} (hik : i ≤ k) :
    MvPolynomial.coeff (passiProbeExponent i k)
      (passiPolynomialProbe i k
        (FreeAlgebra.ι ℤ i * w.passiU i j)) =
      (w.cubicCoefficients i j k : ZMod (passiGCD i k)) := by
  classical
  rw [map_mul]
  rw [show passiPolynomialProbe i k (FreeAlgebra.ι ℤ i) =
      MvPolynomial.X i by
    simp [passiPolynomialProbe]]
  rw [show passiProbeExponent i k =
      Finsupp.single i 1 + Finsupp.single k 1 by rfl]
  change MvPolynomial.coeff
      (Finsupp.single i 1 + Finsupp.single k 1)
      (MvPolynomial.X i * passiPolynomialProbe i k (w.passiU i j)) = _
  rw [MvPolynomial.coeff_X_mul]
  rw [NormalizedDimensionFourWitness.passiU, map_add,
    MvPolynomial.coeff_add]
  have hscalar : MvPolynomial.coeff (Finsupp.single k 1)
      (passiPolynomialProbe i k
        (w.cutoffQuadraticCoefficients i j • 1)) = 0 := by
    rw [map_zsmul, map_one]
    change (MvPolynomial.lcoeff (ZMod (passiGCD i k))
      (Finsupp.single k 1))
        (w.cutoffQuadraticCoefficients i j • 1) = 0
    rw [map_zsmul, MvPolynomial.lcoeff_apply]
    rw [MvPolynomial.coeff_one, if_neg, smul_zero]
    intro h
    have hk := congrArg (fun e : FirstSmithIndex L →₀ ℕ ↦ e k) h
    simp at hk
  rw [hscalar, zero_add]
  rw [NormalizedDimensionFourWitness.passiUPositive, map_sum]
  change MvPolynomial.coeff (Finsupp.single k 1)
      (∑ l, passiPolynomialProbe i k
        (if i ≤ l then w.cubicCoefficients i j l •
          FreeAlgebra.ι ℤ l else 0)) = _
  change (MvPolynomial.lcoeff (ZMod (passiGCD i k))
      (Finsupp.single k 1))
    (∑ l, passiPolynomialProbe i k
      (if i ≤ l then w.cubicCoefficients i j l •
        FreeAlgebra.ι ℤ l else 0)) = _
  rw [map_sum]
  rw [Finset.sum_eq_single k]
  · simp only [hik, if_true, map_zsmul, passiPolynomialProbe,
      FreeAlgebra.lift_ι_apply, if_pos (Or.inr rfl)]
    simp only [or_true, if_true]
    rw [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X]
    simp
  · intro l hl hne
    by_cases hil : i ≤ l
    · simp only [hil, if_true, map_zsmul, passiPolynomialProbe,
        FreeAlgebra.lift_ι_apply, MvPolynomial.coeff_smul]
      by_cases hsel : l = i ∨ l = k
      · rw [if_pos hsel]
        have hsingle : Finsupp.single l 1 ≠ Finsupp.single k 1 := by
          intro h
          exact hne (Finsupp.single_left_injective one_ne_zero h)
        rw [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X',
          if_neg hsingle, smul_zero]
      · rw [if_neg hsel]
        simp
    · simp [hil]
  · intro hk
    simp at hk

/-- The coefficient comparison in Passi's equation (3): the cubic
coefficient is divisible by the gcd of the first and third Smith heads. -/
private theorem NormalizedDimensionFourWitness.cubicCoefficient_gcd_dvd
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    {i j k : FirstSmithIndex L} (hij : i < j) (hik : i ≤ k) :
    (passiGCD i k : ℤ) ∣ w.cubicCoefficients i j k := by
  have hp := w.passiThree hij
  change _ ∈
    FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 ⊔
      passiSIdeal (L := L) at hp
  rw [Submodule.mem_sup] at hp
  obtain ⟨p3, hp3, ps, hps, heq⟩ := hp
  have hcoeff : MvPolynomial.coeff (passiProbeExponent i k)
      (passiPolynomialProbe i k
        (FreeAlgebra.ι ℤ i * w.passiU i j)) = 0 := by
    rw [← heq, map_add, MvPolynomial.coeff_add,
      passiPolynomialProbe_high_coeff_eq_zero i k hp3,
      passiPolynomialProbe_mem_s_eq_zero i k hps]
    simp
  rw [w.passiU_probe_coefficient hik] at hcoeff
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcoeff

/-- Bézout elimination of one normalized cubic summand after evaluation in
`L`.  This is the last sentence of Passi's degree-three cancellation. -/
private theorem NormalizedDimensionFourWitness.evaluated_cubicSummand_mem_gammaFour
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    {i j k : FirstSmithIndex L} (hij : i < j) (hik : i ≤ k) :
    w.cubicCoefficients i j k •
        ⁅⁅firstSmithValue i, firstSmithValue j⁆, firstSmithValue k⁆ ∈
      lowerCentralSeries ℤ L 3 := by
  let di := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 i
  let dk := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 k
  obtain ⟨t, ht⟩ := w.cubicCoefficient_gcd_dvd hij hik
  let α : ℤ := di.gcdA dk
  let β : ℤ := di.gcdB dk
  have hgcd : (passiGCD i k : ℤ) =
      firstSmithDiagonal i * α + firstSmithDiagonal k * β := by
    simpa only [passiGCD, firstSmithDiagonal, di, dk, α, β] using
      Nat.gcd_eq_gcd_ab di dk
  have heq : w.cubicCoefficients i j k •
        ⁅⁅firstSmithValue i, firstSmithValue j⁆, firstSmithValue k⁆ =
      (t * α) •
          ⁅⁅firstSmithDiagonal i • firstSmithValue i,
              firstSmithValue j⁆, firstSmithValue k⁆ +
        (t * β) •
          ⁅⁅firstSmithValue i, firstSmithValue j⁆,
              firstSmithDiagonal k • firstSmithValue k⁆ := by
    rw [ht, hgcd]
    simp only [zsmul_lie, lie_zsmul, smul_smul]
    module
  rw [heq]
  apply (lowerCentralSeries ℤ L 3).add_mem
  · apply (lowerCentralSeries ℤ L 3).smul_mem
    have hhead := firstSmithDiagonal_smul_value_mem_gammaTwo i
    have hinnerRev : ⁅firstSmithValue j,
        firstSmithDiagonal i • firstSmithValue i⁆ ∈
        lowerCentralSeries ℤ L 2 := by
      change _ ∈ LieModule.lowerCentralSeries ℤ L L (1 + 1)
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hhead
    have hinner : ⁅firstSmithDiagonal i • firstSmithValue i,
        firstSmithValue j⁆ ∈ lowerCentralSeries ℤ L 2 := by
      rw [show ⁅firstSmithDiagonal i • firstSmithValue i,
          firstSmithValue j⁆ =
        -⁅firstSmithValue j,
          firstSmithDiagonal i • firstSmithValue i⁆ by
        exact (lie_skew _ _).symm]
      exact (lowerCentralSeries ℤ L 2).neg_mem hinnerRev
    have houtRev : ⁅firstSmithValue k,
        ⁅firstSmithDiagonal i • firstSmithValue i,
          firstSmithValue j⁆⁆ ∈ lowerCentralSeries ℤ L 3 := by
      change _ ∈ LieModule.lowerCentralSeries ℤ L L (2 + 1)
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hinner
    rw [show ⁅⁅firstSmithDiagonal i • firstSmithValue i,
          firstSmithValue j⁆, firstSmithValue k⁆ =
        -⁅firstSmithValue k,
          ⁅firstSmithDiagonal i • firstSmithValue i,
            firstSmithValue j⁆⁆ by
      exact (lie_skew _ _).symm]
    exact (lowerCentralSeries ℤ L 3).neg_mem houtRev
  · apply (lowerCentralSeries ℤ L 3).smul_mem
    have hleft : ⁅firstSmithValue i, firstSmithValue j⁆ ∈
        lowerCentralSeries ℤ L 1 := by
      change _ ∈ LieModule.lowerCentralSeries ℤ L L (0 + 1)
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie
        (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
    apply bracket_dimensionSubring_le_lowerCentralSeries ℤ L 1 1
    exact LieSubmodule.lie_mem_lie
      (lowerCentralSeries_le_dimensionSubring ℤ L 1 hleft)
      (lowerCentralSeries_le_dimensionSubring ℤ L 1
        (firstSmithDiagonal_smul_value_mem_gammaTwo k))

private theorem NormalizedDimensionFourWitness.evaluated_component_three_mem_gammaFour
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    canonicalFreeLieEvaluation L (w.component 3 : CanonicalFreeLie L) ∈
      lowerCentralSeries ℤ L 3 := by
  classical
  rw [w.component_three_eq_cutoff]
  simp only [map_sum, apply_ite, map_zsmul, map_zero, LieHom.map_lie,
    firstSmithValue]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.sum_mem
  intro k hk
  by_cases hgood : i < j ∧ i ≤ k
  · simp only [hgood, if_true]
    exact w.evaluated_cubicSummand_mem_gammaFour hgood.1 hgood.2
  · simp [hgood]

private def NormalizedDimensionFourWitness.multiplierImage [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (p : UEA ℤ (CanonicalFreeLie L) ×
      DegreeFive.CanonicalLieRelationsIdeal L) :
    FreeAlgebra ℤ (FirstSmithIndex L) :=
  smithUEAEquiv (L := L)
    (p.1 - algebraMap ℤ (UEA ℤ (CanonicalFreeLie L))
      (UEA.augmentation ℤ (CanonicalFreeLie L) p.1))

private def NormalizedDimensionFourWitness.multiplierComponent [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (n : ℕ)
    (p : UEA ℤ (CanonicalFreeLie L) ×
      DegreeFive.CanonicalLieRelationsIdeal L) :
    FreeAlgebra ℤ (FirstSmithIndex L) :=
  DegreeFive.associativeLengthComponent (FirstSmithIndex L) n
    (w.multiplierImage p)

private def relationLieComponent [Finite L] (n : ℕ)
    (r : DegreeFive.CanonicalLieRelationsIdeal L) : CanonicalFreeLie L :=
  DegreeFive.freeLieLengthComponent L n (r : CanonicalFreeLie L)

private def relationComponent [Finite L] (n : ℕ)
    (r : DegreeFive.CanonicalLieRelationsIdeal L) :
    FreeAlgebra ℤ (FirstSmithIndex L) :=
  DegreeFive.associativeLengthComponent (FirstSmithIndex L) n
    (smithLieImage (r : CanonicalFreeLie L))

private theorem smithLieImage_component [Finite L]
    (n : ℕ) (x : CanonicalFreeLie L) :
    DegreeFive.associativeLengthComponent (FirstSmithIndex L) n
        (smithLieImage x) =
      smithLieImage (DegreeFive.freeLieLengthComponent L n x) := by
  unfold smithLieImage
  rw [freeAlgebraToFirstSmith_component,
    ← DegreeFive.freeLieToFreeAlgebra_freeLieLengthComponent]

private theorem relationComponent_eq_smithLieImage [Finite L]
    (n : ℕ) (r : DegreeFive.CanonicalLieRelationsIdeal L) :
    relationComponent n r = smithLieImage (relationLieComponent n r) := by
  exact smithLieImage_component n (r : CanonicalFreeLie L)

private theorem smithLieImage_mem_high_one [Finite L]
    (x : CanonicalFreeLie L) :
    smithLieImage x ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 1 := by
  apply freeAlgebraToFirstSmith_preserves_high
  apply DegreeFive.freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh L
  rw [FreeLieDimension.lieHigh_one]
  trivial

private theorem NormalizedDimensionFourWitness.multiplierImage_mem_high_one
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (p : UEA ℤ (CanonicalFreeLie L) ×
      DegreeFive.CanonicalLieRelationsIdeal L)
    (hp : p ∈ w.relationTerms.support) :
    w.multiplierImage p ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 1 := by
  exact smithUEAEquiv_mem_associativeHigh_one (w.multiplier_mem p hp)

private def NormalizedDimensionFourWitness.multiplierLinearCoefficient
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L)
    (p : UEA ℤ (CanonicalFreeLie L) ×
      DegreeFive.CanonicalLieRelationsIdeal L) : ℤ :=
  FreeLieDimension.freeAlgebraAugmentation (FirstSmithIndex L)
    (rightCoeff i (w.multiplierComponent 1 p))

private theorem NormalizedDimensionFourWitness.rightCoeff_multiplierComponent_one
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L)
    (p : UEA ℤ (CanonicalFreeLie L) ×
      DegreeFive.CanonicalLieRelationsIdeal L) :
    rightCoeff i (w.multiplierComponent 1 p) =
      w.multiplierLinearCoefficient i p • 1 := by
  apply exactZero_eq_augmentation_smul_one
  apply rightCoeff_mem_associativeExact i 0
  exact DegreeFive.associativeLengthComponent_mem_exact
    (FirstSmithIndex L) 1 (w.multiplierImage p)

/-- Passi's `D_i`: the degree-two multiplier followed by the linear head
of a relation. -/
private def NormalizedDimensionFourWitness.passiD [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) : FreeAlgebra ℤ (FirstSmithIndex L) :=
  w.relationTerms.sum fun p n ↦ n •
    (rightCoeff i (w.multiplierComponent 2 p) *
      relationComponent 1 p.2)

/-- Passi's `C_i`, kept as an actual quadratic free-Lie element. -/
private def NormalizedDimensionFourWitness.passiC [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) : CanonicalFreeLie L :=
  w.relationTerms.sum fun p n ↦
    (n * w.multiplierLinearCoefficient i p) • relationLieComponent 2 p.2

private theorem NormalizedDimensionFourWitness.smithLieImage_passiC
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    smithLieImage (w.passiC i) =
      w.relationTerms.sum fun p n ↦ n •
        (rightCoeff i (w.multiplierComponent 1 p) *
          relationComponent 2 p.2) := by
  classical
  simp only [NormalizedDimensionFourWitness.passiC, smithLieImage,
    map_finsuppSum, map_zsmul, mul_smul, relationComponent_eq_smithLieImage]
  apply Finsupp.sum_congr
  intro p hp
  rw [w.rightCoeff_multiplierComponent_one i p]
  simp only [smul_mul_assoc, one_mul, smul_smul]

private theorem NormalizedDimensionFourWitness.passiC_mem_gammaTwo
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    w.passiC i ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 1 := by
  classical
  have hhigh : w.passiC i ∈ FreeLieDimension.lieHigh L 2 := by
    apply Submodule.sum_mem
    intro p hp
    apply (FreeLieDimension.lieHigh L 2).smul_mem
    exact DegreeFive.freeLieExact_mem_lieHigh L
      ⟨relationLieComponent 2 p.2,
        DegreeFive.freeLieLengthComponent_mem_exact L 2
          (p.2 : CanonicalFreeLie L)⟩
  simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 1] using hhigh

private theorem NormalizedDimensionFourWitness.smithRelationEquation
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    w.relationTerms.sum (fun p n ↦ n •
      (w.multiplierImage p * smithLieImage (p.2 : CanonicalFreeLie L))) =
      smithLieImage w.lieLift - smithUEAEquiv (L := L) w.highWord := by
  have heq := congrArg (smithUEAEquiv (L := L)) w.relationEquation
  rw [map_finsuppSum] at heq
  simpa only [NormalizedDimensionFourWitness.multiplierImage, map_zsmul,
    map_mul, map_sub, smithUEAEquiv_iota] using heq

/-- The degree-two part of Passi's normalized relation equation. -/
private theorem NormalizedDimensionFourWitness.smithComponentTwoEquation
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    smithLieImage (w.component 2 : CanonicalFreeLie L) =
      w.relationTerms.sum fun p n ↦ n •
        (w.multiplierComponent 1 p * relationComponent 1 p.2) := by
  classical
  let C := DegreeFive.associativeLengthComponent (FirstSmithIndex L) 2
  have hleft : C (w.relationTerms.sum (fun p n ↦ n •
      (w.multiplierImage p * smithLieImage (p.2 : CanonicalFreeLie L)))) =
      w.relationTerms.sum fun p n ↦ n •
        (w.multiplierComponent 1 p * relationComponent 1 p.2) := by
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro p hp
    rw [map_zsmul, associativeComponent_two_mul]
    · rfl
    · exact w.multiplierImage_mem_high_one p hp
    · exact smithLieImage_mem_high_one (p.2 : CanonicalFreeLie L)
  have hhigh : C (smithUEAEquiv (L := L) w.highWord) = 0 :=
    DegreeFive.associativeLengthComponent_eq_zero_of_mem_high
      (FirstSmithIndex L)
      (smithUEAEquiv_mem_associativeHigh 4 w.highWord_mem) (by omega)
  have heq := congrArg C w.smithRelationEquation
  rw [hleft, map_sub, hhigh, sub_zero, smithLieImage_component] at heq
  exact heq.symm

/-- The degree-three part of Passi's normalized relation equation. -/
private theorem NormalizedDimensionFourWitness.smithComponentThreeEquation
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    smithLieImage (w.component 3 : CanonicalFreeLie L) =
      w.relationTerms.sum fun p n ↦ n •
        (w.multiplierComponent 2 p * relationComponent 1 p.2 +
          w.multiplierComponent 1 p * relationComponent 2 p.2) := by
  classical
  let C := DegreeFive.associativeLengthComponent (FirstSmithIndex L) 3
  have hleft : C (w.relationTerms.sum (fun p n ↦ n •
      (w.multiplierImage p * smithLieImage (p.2 : CanonicalFreeLie L)))) =
      w.relationTerms.sum fun p n ↦ n •
        (w.multiplierComponent 2 p * relationComponent 1 p.2 +
          w.multiplierComponent 1 p * relationComponent 2 p.2) := by
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro p hp
    rw [map_zsmul, associativeComponent_three_mul]
    · rfl
    · exact w.multiplierImage_mem_high_one p hp
    · exact smithLieImage_mem_high_one (p.2 : CanonicalFreeLie L)
  have hhigh : C (smithUEAEquiv (L := L) w.highWord) = 0 :=
    DegreeFive.associativeLengthComponent_eq_zero_of_mem_high
      (FirstSmithIndex L)
      (smithUEAEquiv_mem_associativeHigh 4 w.highWord_mem) (by omega)
  have heq := congrArg C w.smithRelationEquation
  rw [hleft, map_sub, hhigh, sub_zero, smithLieImage_component] at heq
  exact heq.symm

@[simp]
private theorem smithLieImage_firstSmithGenerator [Finite L]
    (i : FirstSmithIndex L) :
    smithLieImage (firstSmithGenerator i) = FreeAlgebra.ι ℤ i := by
  rw [← smithUEAEquiv_iota,
    smithUEAEquiv_iota_firstSmithGenerator]

/-- Passi's final (lower-triangular) coefficients of the quadratic part. -/
private def NormalizedDimensionFourWitness.finalCoefficients [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b) :
    FirstSmithIndex L → FirstSmithIndex L → ℤ :=
  Classical.choose (exists_strictBracketCoordinates (w.component 2))

private theorem NormalizedDimensionFourWitness.component_two_eq_final
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    (w.component 2 : CanonicalFreeLie L) =
      ∑ i, ∑ j, if j < i then w.finalCoefficients i j •
        ⁅firstSmithGenerator i, firstSmithGenerator j⁆ else 0 :=
  Classical.choose_spec (exists_strictBracketCoordinates (w.component 2))

/-- Passi's identity `PBW(v₂) = sum_i X_i W_i`. -/
private theorem NormalizedDimensionFourWitness.smithComponentTwo_eq_rows
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    smithLieImage (w.component 2 : CanonicalFreeLie L) =
      ∑ i, FreeAlgebra.ι ℤ i *
        normalFormRow (fun j : FirstSmithIndex L ↦ FreeAlgebra.ι ℤ j)
          w.finalCoefficients i := by
  classical
  have hmap : smithLieImage (w.component 2 : CanonicalFreeLie L) =
      ∑ i, ∑ j, if j < i then w.finalCoefficients i j •
        (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j -
          FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) else 0 := by
    rw [w.component_two_eq_final]
    simp only [smithLieImage, map_sum, apply_ite, map_zsmul, map_zero,
      LieHom.map_lie, LieRing.of_associative_ring_bracket, map_sub, map_mul,
      freeAlgebraToFirstSmith_firstSmithGenerator]
  rw [hmap]
  simp only [normalFormRow, mul_sub, Finset.mul_sum, mul_ite, mul_zero,
    mul_smul_comm, Finset.sum_sub_distrib]
  have hswap :
      (∑ i, ∑ j, if i < j then w.finalCoefficients j i •
          (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j) else 0) =
        ∑ i, ∑ j, if j < i then w.finalCoefficients i j •
          (FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) else 0 := by
    rw [Finset.sum_comm]
  rw [hswap, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j < i
  · simp only [hji, if_true]
    rw [smul_sub]
  · simp [hji]

/-- The two-sided ideal generated by the actual presentation relations. -/
private def smithRelationIdeal [Finite L] :
    Ideal (FreeAlgebra ℤ (FirstSmithIndex L)) :=
  (TwoSidedIdeal.span (Set.range fun r :
    DegreeFive.CanonicalLieRelationsIdeal L ↦
      smithLieImage (r : CanonicalFreeLie L))).asIdeal

private theorem smithLieImage_relation_mem_relationIdeal [Finite L]
    (r : DegreeFive.CanonicalLieRelationsIdeal L) :
    smithLieImage (r : CanonicalFreeLie L) ∈ smithRelationIdeal (L := L) := by
  change _ ∈ TwoSidedIdeal.span _
  exact TwoSidedIdeal.subset_span ⟨r, rfl⟩

private theorem NormalizedDimensionFourWitness.rightCoeff_relationSum_mem
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    rightCoeff i (w.relationTerms.sum (fun p n ↦ n •
      (w.multiplierImage p * smithLieImage (p.2 : CanonicalFreeLie L)))) ∈
      smithRelationIdeal (L := L) := by
  classical
  rw [map_finsuppSum]
  apply Submodule.sum_mem
  intro p hp
  change rightCoeff i ((w.relationTerms p) •
    (w.multiplierImage p * smithLieImage (p.2 : CanonicalFreeLie L))) ∈ _
  rw [LinearMap.map_smul, rightCoeff_mul i _ _
    (w.multiplierImage_mem_high_one p hp)]
  apply zsmul_mem
  exact (smithRelationIdeal (L := L)).mul_mem_left _
    (smithLieImage_relation_mem_relationIdeal p.2)

/-- Applying the first-letter coordinate to the normalized equation gives
Passi's first row congruence. -/
private theorem NormalizedDimensionFourWitness.rightCoeff_components_mem
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    rightCoeff i (smithLieImage ((w.component 2 : CanonicalFreeLie L) +
      (w.component 3 : CanonicalFreeLie L))) ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
        smithRelationIdeal (L := L) := by
  classical
  let H := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3
  let R := smithRelationIdeal (L := L)
  let rel := w.relationTerms.sum (fun p n ↦ n •
    (w.multiplierImage p * smithLieImage (p.2 : CanonicalFreeLie L)))
  let high := smithUEAEquiv (L := L) w.highWord
  let rem := smithLieImage (w.lieLift -
    ((w.component 2 : CanonicalFreeLie L) +
      (w.component 3 : CanonicalFreeLie L)))
  have hhigh4 : high ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 4 :=
    smithUEAEquiv_mem_associativeHigh 4 w.highWord_mem
  have hrem4 : rem ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 4 := by
    apply freeAlgebraToFirstSmith_preserves_high
    apply DegreeFive.freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh L
    simpa only [sub_add_eq_sub_sub] using
      w.lieLift_sub_components_mem_high_four
  have hrelR : rightCoeff i rel ∈ R :=
    w.rightCoeff_relationSum_mem i
  have hhighH : rightCoeff i high ∈ H :=
    rightCoeff_mem_associativeHigh i 3 high hhigh4
  have hremH : rightCoeff i rem ∈ H :=
    rightCoeff_mem_associativeHigh i 3 rem hrem4
  have heq : smithLieImage ((w.component 2 : CanonicalFreeLie L) +
        (w.component 3 : CanonicalFreeLie L)) = rel + high - rem := by
    have hrel := w.smithRelationEquation
    change rel = smithLieImage w.lieLift - high at hrel
    have hadd : smithLieImage ((w.component 2 : CanonicalFreeLie L) +
        (w.component 3 : CanonicalFreeLie L)) =
        smithLieImage (w.component 2 : CanonicalFreeLie L) +
          smithLieImage (w.component 3 : CanonicalFreeLie L) := by
      simp only [smithLieImage, map_add]
    have hrem : rem = smithLieImage w.lieLift -
        (smithLieImage (w.component 2 : CanonicalFreeLie L) +
          smithLieImage (w.component 3 : CanonicalFreeLie L)) := by
      simp only [rem, smithLieImage, map_sub, map_add]
    rw [hadd, hrem, hrel]
    module
  rw [heq, map_sub, map_add]
  apply (H + R).sub_mem
  · apply (H + R).add_mem
    · exact (show R ≤ H + R from le_sup_right) hrelR
    · exact (show H ≤ H + R from le_sup_left) hhighH
  · exact (show H ≤ H + R from le_sup_left) hremH

private theorem NormalizedDimensionFourWitness.rightCoeff_component_two
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    rightCoeff i (smithLieImage (w.component 2 : CanonicalFreeLie L)) =
      normalFormRow (fun j : FirstSmithIndex L ↦ FreeAlgebra.ι ℤ j)
        w.finalCoefficients i := by
  classical
  have h := congrArg (rightCoeff i) w.smithComponentTwo_eq_rows
  rw [map_sum] at h
  simp_rw [rightCoeff_iota_mul] at h
  simpa using h

private theorem NormalizedDimensionFourWitness.rightCoeff_component_three
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    rightCoeff i (smithLieImage (w.component 3 : CanonicalFreeLie L)) =
      w.passiD i + smithLieImage (w.passiC i) := by
  classical
  have h := congrArg (rightCoeff i) w.smithComponentThreeEquation
  rw [map_finsuppSum] at h
  simp only [LinearMap.map_smul, map_add] at h
  have hrhs : w.relationTerms.sum (fun p n ↦ n •
      (rightCoeff i (w.multiplierComponent 2 p * relationComponent 1 p.2) +
        rightCoeff i (w.multiplierComponent 1 p * relationComponent 2 p.2))) =
      w.passiD i + smithLieImage (w.passiC i) := by
    unfold NormalizedDimensionFourWitness.passiD
    rw [w.smithLieImage_passiC i]
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro p hp
    rw [rightCoeff_mul, rightCoeff_mul]
    · module
    · exact FreeLieDimension.associativeExact_le_high (FirstSmithIndex L)
        (by omega)
        (DegreeFive.associativeLengthComponent_mem_exact
          (FirstSmithIndex L) 1 (w.multiplierImage p))
    · exact FreeLieDimension.associativeExact_le_high (FirstSmithIndex L)
        (by omega)
        (DegreeFive.associativeLengthComponent_mem_exact
          (FirstSmithIndex L) 2 (w.multiplierImage p))
  exact h.trans hrhs

private theorem NormalizedDimensionFourWitness.passiRowOne
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    normalFormRow (fun j : FirstSmithIndex L ↦ FreeAlgebra.ι ℤ j)
        w.finalCoefficients i + w.passiD i + smithLieImage (w.passiC i) ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
        smithRelationIdeal (L := L) := by
  have h := w.rightCoeff_components_mem i
  rw [show smithLieImage ((w.component 2 : CanonicalFreeLie L) +
      (w.component 3 : CanonicalFreeLie L)) =
      smithLieImage (w.component 2 : CanonicalFreeLie L) +
        smithLieImage (w.component 3 : CanonicalFreeLie L) by
    simp only [smithLieImage, map_add]] at h
  rw [map_add] at h
  rw [w.rightCoeff_component_two i, w.rightCoeff_component_three i] at h
  simpa only [add_assoc] using h

private theorem relation_sub_component_one_mem_high_two [Finite L]
    (r : DegreeFive.CanonicalLieRelationsIdeal L) :
    smithLieImage (r : CanonicalFreeLie L) - relationComponent 1 r ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 2 := by
  apply DegreeFive.mem_associativeHigh_succ_of_component_eq_zero
    (FirstSmithIndex L)
  · apply (FreeLieDimension.associativeHigh (FirstSmithIndex L) 1).sub_mem
    · exact smithLieImage_mem_high_one (r : CanonicalFreeLie L)
    · exact FreeLieDimension.associativeExact_le_high (FirstSmithIndex L)
        (by omega)
        (DegreeFive.associativeLengthComponent_mem_exact
          (FirstSmithIndex L) 1 (smithLieImage (r : CanonicalFreeLie L)))
  · rw [map_sub]
    unfold relationComponent
    rw [DegreeFive.associativeLengthComponent_eq_self_of_mem_exact
      (FirstSmithIndex L)
      (DegreeFive.associativeLengthComponent_mem_exact
        (FirstSmithIndex L) 1 (smithLieImage (r : CanonicalFreeLie L))),
      sub_self]

/-- In Passi's `D_i`, replacing the linear relation head by the full
relation leaves only terms of word length at least three. -/
private theorem NormalizedDimensionFourWitness.passiD_mem
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    w.passiD i ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
        smithRelationIdeal (L := L) := by
  classical
  unfold NormalizedDimensionFourWitness.passiD
  apply Submodule.sum_mem
  intro p hp
  change (w.relationTerms p) •
    (rightCoeff i (w.multiplierComponent 2 p) * relationComponent 1 p.2) ∈ _
  apply zsmul_mem
  let a := rightCoeff i (w.multiplierComponent 2 p)
  let r := smithLieImage (p.2 : CanonicalFreeLie L)
  have ha1 : a ∈ FreeLieDimension.associativeHigh (FirstSmithIndex L) 1 := by
    exact FreeLieDimension.associativeExact_le_high (FirstSmithIndex L)
      (by omega)
      (rightCoeff_mem_associativeExact i 1 (w.multiplierComponent 2 p)
        (DegreeFive.associativeLengthComponent_mem_exact
          (FirstSmithIndex L) 2 (w.multiplierImage p)))
  have hrelation : a * r ∈ smithRelationIdeal (L := L) :=
    (smithRelationIdeal (L := L)).mul_mem_left _
      (smithLieImage_relation_mem_relationIdeal p.2)
  have hhigh : a * (r - relationComponent 1 p.2) ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 3 := by
    simpa using FreeLieDimension.associativeHigh_mul
      (FirstSmithIndex L) ha1 (relation_sub_component_one_mem_high_two p.2)
  change a * relationComponent 1 p.2 ∈ _
  rw [show a * relationComponent 1 p.2 =
      a * r - a * (r - relationComponent 1 p.2) by noncomm_ring]
  apply (FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
    smithRelationIdeal (L := L)).sub_mem
  · exact (show smithRelationIdeal (L := L) ≤ _ from le_sup_right) hrelation
  · exact (show FreeLieDimension.associativeHighIdeal
      (FirstSmithIndex L) 3 ≤ _ from le_sup_left) hhigh

private theorem NormalizedDimensionFourWitness.passiC_mem_exact_two
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    w.passiC i ∈ DegreeFive.freeLieExact L 2 := by
  classical
  unfold NormalizedDimensionFourWitness.passiC
  apply Submodule.sum_mem
  intro p hp
  apply (DegreeFive.freeLieExact L 2).smul_mem
  exact DegreeFive.freeLieLengthComponent_mem_exact L 2
    (p.2 : CanonicalFreeLie L)

private def NormalizedDimensionFourWitness.passiFCoefficients [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    FirstSmithIndex L → FirstSmithIndex L → ℤ :=
  Classical.choose (exists_strictBracketCoordinates
    (⟨w.passiC i, w.passiC_mem_exact_two i⟩ : DegreeFive.freeLieExact L 2))

private theorem NormalizedDimensionFourWitness.passiC_eq_brackets
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    w.passiC i = ∑ j, ∑ k, if k < j then
      w.passiFCoefficients i j k •
        ⁅firstSmithGenerator j, firstSmithGenerator k⁆ else 0 :=
  Classical.choose_spec (exists_strictBracketCoordinates
    (⟨w.passiC i, w.passiC_mem_exact_two i⟩ : DegreeFive.freeLieExact L 2))

/-- The one free-monoid coefficient used in Passi's comparison. -/
private def wordCoefficient {I : Type*} (xs : List I) :
    FreeAlgebra ℤ I →ₗ[ℤ] ℤ where
  toFun p := FreeAlgebra.equivMonoidAlgebraFreeMonoid p
    (FreeMonoid.ofList xs)
  map_add' p q := by simp
  map_smul' n p := by
    rw [map_zsmul]
    rfl

@[simp]
private theorem wordCoefficient_word {I : Type*} [DecidableEq I]
    (xs ys : List I) :
    wordCoefficient xs (DegreeFive.freeAlgebraWord I ys) =
      if ys = xs then 1 else 0 := by
  classical
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (DegreeFive.freeAlgebraWord I ys) (FreeMonoid.ofList xs) = _
  rw [freeAlgebraWord_equiv]
  change (Finsupp.single (FreeMonoid.ofList ys) 1)
      (FreeMonoid.ofList xs) = _
  by_cases hlist : ys = xs
  · subst ys
    simp
  · have hmon : FreeMonoid.ofList ys ≠ FreeMonoid.ofList xs := by
      intro h
      exact hlist (by simpa using congrArg FreeMonoid.toList h)
    simp [hlist, hmon]

@[simp]
private theorem wordCoefficient_two_letters {I : Type*} [DecidableEq I]
    (i j a c : I) :
    wordCoefficient [i, j] (FreeAlgebra.ι ℤ a * FreeAlgebra.ι ℤ c) =
      if a = i ∧ c = j then 1 else 0 := by
  rw [show FreeAlgebra.ι ℤ a * FreeAlgebra.ι ℤ c =
      DegreeFive.freeAlgebraWord I [a, c] by
    simp [DegreeFive.freeAlgebraWord_cons]]
  rw [wordCoefficient_word]
  simp

@[simp]
private theorem wordCoefficient_three_letters {I : Type*} [DecidableEq I]
    (i j k a c d : I) :
    wordCoefficient [i, j, k]
        (FreeAlgebra.ι ℤ a * FreeAlgebra.ι ℤ c * FreeAlgebra.ι ℤ d) =
      if a = i ∧ c = j ∧ d = k then 1 else 0 := by
  rw [show FreeAlgebra.ι ℤ a * FreeAlgebra.ι ℤ c * FreeAlgebra.ι ℤ d =
      DegreeFive.freeAlgebraWord I [a, c, d] by
    simp [DegreeFive.freeAlgebraWord_cons, mul_assoc]]
  rw [wordCoefficient_word]
  simp

@[simp]
private theorem wordCoefficient_three_letters_right {I : Type*} [DecidableEq I]
    (i j k a c d : I) :
    wordCoefficient [i, j, k]
        (FreeAlgebra.ι ℤ a * (FreeAlgebra.ι ℤ c * FreeAlgebra.ι ℤ d)) =
      if a = i ∧ c = j ∧ d = k then 1 else 0 := by
  rw [← mul_assoc]
  exact wordCoefficient_three_letters i j k a c d

@[simp]
private theorem wordCoefficient_one_letter {I : Type*} [DecidableEq I]
    (i a : I) :
    wordCoefficient [i] (FreeAlgebra.ι ℤ a) = if a = i then 1 else 0 := by
  rw [show FreeAlgebra.ι ℤ a = DegreeFive.freeAlgebraWord I [a] by
    simp [DegreeFive.freeAlgebraWord_cons]]
  rw [wordCoefficient_word]
  simp

private theorem wordCoefficient_rightCoeff {I : Type*} [DecidableEq I]
    (i : I) (xs : List I) (p : FreeAlgebra ℤ I) :
    wordCoefficient xs (rightCoeff i p) =
      wordCoefficient (i :: xs) p := by
  classical
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid (rightCoeff i p)
      (FreeMonoid.ofList xs) =
    FreeAlgebra.equivMonoidAlgebraFreeMonoid p
      (FreeMonoid.ofList (i :: xs))
  dsimp only [rightCoeff, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
        ((MonoidAlgebra.comapDomainAddMonoidHom (R := ℤ) (wordPrefix i)
          (wordPrefix_inj i))
            (FreeAlgebra.equivMonoidAlgebraFreeMonoid p)))
        (FreeMonoid.ofList xs) = _
  rw [FreeAlgebra.equivMonoidAlgebraFreeMonoid.apply_symm_apply]
  rfl

private theorem NormalizedDimensionFourWitness.wordCoefficient_passiC
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) (hkj : k < j) :
    wordCoefficient [j, k] (smithLieImage (w.passiC i)) =
      w.passiFCoefficients i j k := by
  classical
  rw [w.passiC_eq_brackets i]
  simp only [smithLieImage, map_sum, apply_ite, map_zsmul, map_zero,
    LieHom.map_lie, LieRing.of_associative_ring_bracket, map_sub, map_mul,
    freeAlgebraToFirstSmith_firstSmithGenerator]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single k]
    · simp [hkj, hkj.ne]
    · intro l hl hlk
      by_cases hlj : l < j
      · simp only [hlj, if_true, LinearMap.map_smul, LinearMap.map_sub,
          wordCoefficient_two_letters, smul_eq_mul]
        by_cases hzero : l = j ∧ j = k
        · exact (hkj.ne hzero.2.symm).elim
        · simp [hlk, hzero]
      · simp [hlj]
    · simp
  · intro l hl hlj
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hml : m < l
    · simp only [hml, if_true, LinearMap.map_smul, LinearMap.map_sub,
          wordCoefficient_two_letters, smul_eq_mul]
      by_cases hzero : m = j ∧ l = k
      · have hnot : ¬m < l := by
          rw [hzero.1, hzero.2]
          exact not_lt_of_ge (le_of_lt hkj)
        exact (hnot hml).elim
      · simp [hlj, hzero]
    · simp [hml]
  · simp

private def passiTripleGCD [Finite L]
    (i j k : FirstSmithIndex L) : ℕ :=
  Nat.gcd
    (DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 i)
    (Nat.gcd
      (DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 j)
      (DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 k))

private theorem passiTripleGCD_dvd_diagonal [Finite L]
    (i j k l : FirstSmithIndex L) (hl : l = i ∨ l = j ∨ l = k) :
    passiTripleGCD i j k ∣
      DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 l := by
  rcases hl with rfl | rfl | rfl
  · exact Nat.gcd_dvd_left _ _
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

private theorem NormalizedDimensionFourWitness.tripleGCD_dvd_cubicCoefficient
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k a m c : FirstSmithIndex L)
    (ham : a < m) (hac : a ≤ c)
    (ha : a = i ∨ a = j ∨ a = k)
    (hc : c = i ∨ c = j ∨ c = k) :
    (passiTripleGCD i j k : ℤ) ∣ w.cubicCoefficients a m c := by
  have hnat : passiTripleGCD i j k ∣ Nat.gcd
      (DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 a)
      (DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 c) :=
    Nat.dvd_gcd (passiTripleGCD_dvd_diagonal i j k a ha)
      (passiTripleGCD_dvd_diagonal i j k c hc)
  have hcast : (passiTripleGCD i j k : ℤ) ∣
      (Nat.gcd
        (DegreeFive.collectedDiagonal L L (canonicalFreeLieEvaluation L) 1 a)
        (DegreeFive.collectedDiagonal L L
          (canonicalFreeLieEvaluation L) 1 c) : ℤ) := by
    exact_mod_cast hnat
  exact hcast.trans (w.cubicCoefficient_gcd_dvd ham hac)

private theorem NormalizedDimensionFourWitness.wordCoefficient_component_three_dvd
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) :
    (passiTripleGCD i j k : ℤ) ∣
      wordCoefficient [i, j, k]
        (smithLieImage (w.component 3 : CanonicalFreeLie L)) := by
  classical
  rw [w.component_three_eq_cutoff]
  simp only [smithLieImage, map_sum, apply_ite, map_zsmul, map_zero,
    LieHom.map_lie, LieRing.of_associative_ring_bracket, map_sub, map_mul,
    freeAlgebraToFirstSmith_firstSmithGenerator, sub_mul, mul_sub]
  apply Finset.dvd_sum
  intro a ha
  apply Finset.dvd_sum
  intro m hm
  apply Finset.dvd_sum
  intro c hc
  by_cases hgood : a < m ∧ a ≤ c
  · simp only [hgood, if_true]
    by_cases heq : [a, m, c] = [i, j, k] ∨
        [m, a, c] = [i, j, k] ∨ [c, a, m] = [i, j, k] ∨
          [c, m, a] = [i, j, k]
    · have habc :
          (a = i ∧ m = j ∧ c = k) ∨
          (m = i ∧ a = j ∧ c = k) ∨
          (c = i ∧ a = j ∧ m = k) ∨
          (c = i ∧ m = j ∧ a = k) := by
          simpa using heq
      have hdiv : (passiTripleGCD i j k : ℤ) ∣
          w.cubicCoefficients a m c := by
        rcases habc with h | h | h | h
        · rcases h with ⟨hai, hmj, hck⟩
          subst a; subst m; subst c
          exact w.tripleGCD_dvd_cubicCoefficient i j k i j k
            hgood.1 hgood.2 (Or.inl rfl) (Or.inr (Or.inr rfl))
        · rcases h with ⟨hmi, haj, hck⟩
          subst m; subst a; subst c
          exact w.tripleGCD_dvd_cubicCoefficient i j k j i k
            hgood.1 hgood.2 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
        · rcases h with ⟨hci, haj, hmk⟩
          subst c; subst a; subst m
          exact w.tripleGCD_dvd_cubicCoefficient i j k j k i
            hgood.1 hgood.2 (Or.inr (Or.inl rfl)) (Or.inl rfl)
        · rcases h with ⟨hci, hmj, hak⟩
          subst c; subst m; subst a
          exact w.tripleGCD_dvd_cubicCoefficient i j k k j i
            hgood.1 hgood.2 (Or.inr (Or.inr rfl)) (Or.inl rfl)
      exact dvd_mul_of_dvd_left hdiv _
    · push Not at heq
      rcases heq with ⟨h1, h2, h3, h4⟩
      have hn1 : ¬(a = i ∧ m = j ∧ c = k) := by
        rintro ⟨rfl, rfl, rfl⟩
        exact h1 rfl
      have hn2 : ¬(m = i ∧ a = j ∧ c = k) := by
        rintro ⟨rfl, rfl, rfl⟩
        exact h2 rfl
      have hn3 : ¬(c = i ∧ a = j ∧ m = k) := by
        rintro ⟨rfl, rfl, rfl⟩
        exact h3 rfl
      have hn4 : ¬(c = i ∧ m = j ∧ a = k) := by
        rintro ⟨rfl, rfl, rfl⟩
        exact h4 rfl
      simp [hn1, hn2, hn3, hn4]
  · simp [hgood]

private theorem wordCoefficient_mul_exact_one {I : Type*} [Fintype I]
    [DecidableEq I] (i j : I) (p q : FreeAlgebra ℤ I)
    (hp : p ∈ FreeLieDimension.associativeExact I 1) :
    wordCoefficient [i, j] (p * q) =
      wordCoefficient [i] p * wordCoefficient [j] q := by
  have hpHigh : p ∈ FreeLieDimension.associativeHigh I 1 :=
    FreeLieDimension.associativeExact_le_high I (by omega) hp
  have hrcExact : rightCoeff i p ∈
      FreeLieDimension.associativeExact I 0 :=
    rightCoeff_mem_associativeExact i 0 p hp
  have hrc := exactZero_eq_augmentation_smul_one (rightCoeff i p) hrcExact
  have hscalar : wordCoefficient [i] p =
      FreeLieDimension.freeAlgebraAugmentation I (rightCoeff i p) := by
    rw [← wordCoefficient_rightCoeff i [] p]
    calc
      wordCoefficient [] (rightCoeff i p) =
          wordCoefficient []
            (FreeLieDimension.freeAlgebraAugmentation I (rightCoeff i p) • 1) :=
        congrArg (wordCoefficient []) hrc
      _ = _ := by
        rw [LinearMap.map_smul]
        change _ * wordCoefficient []
          (DegreeFive.freeAlgebraWord I []) = _
        rw [wordCoefficient_word]
        simp
  calc
    wordCoefficient [i, j] (p * q) =
        wordCoefficient [j] (rightCoeff i (p * q)) := by
      rw [wordCoefficient_rightCoeff]
    _ = wordCoefficient [j] (rightCoeff i p * q) := by
      rw [rightCoeff_mul i p q hpHigh]
    _ = wordCoefficient [j]
        (FreeLieDimension.freeAlgebraAugmentation I (rightCoeff i p) • q) := by
      congr 1
      calc
        rightCoeff i p * q =
            (FreeLieDimension.freeAlgebraAugmentation I (rightCoeff i p) • 1) * q :=
          congrArg (fun z ↦ z * q) hrc
        _ = _ := by rw [smul_mul_assoc, one_mul]
    _ = FreeLieDimension.freeAlgebraAugmentation I (rightCoeff i p) *
        wordCoefficient [j] q := by
      rw [LinearMap.map_smul, smul_eq_mul]
    _ = wordCoefficient [i] p * wordCoefficient [j] q := by
      rw [hscalar]

private theorem relationComponent_one_eq_firstRows [Finite L]
    (r : DegreeFive.CanonicalLieRelationsIdeal L) :
    relationComponent 1 r =
      ∑ i, (firstSmithDiagonal i * firstSmithRelationCoefficient r i) •
        FreeAlgebra.ι ℤ i := by
  classical
  rw [relationComponent_eq_smithLieImage]
  have hdecomp := kernelRelation_eq_firstRows_add_gammaTwo r
  have hcomp := congrArg (DegreeFive.freeLieLengthComponent L 1) hdecomp
  rw [map_add, map_sum] at hcomp
  simp_rw [map_zsmul] at hcomp
  have hremZero : DegreeFive.freeLieLengthComponent L 1
      (firstSmithRelationRemainder r) = 0 :=
    DegreeFive.freeLieLengthComponent_eq_zero_of_mem_lieHigh L
      (firstSmithRelationRemainder_mem_lieHigh_two r) (by omega)
  rw [hremZero, add_zero] at hcomp
  have hrow (i : FirstSmithIndex L) :
      DegreeFive.freeLieLengthComponent L 1
          (DegreeFive.collectedRelationRow L L
            (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L) =
        firstSmithDiagonal i • firstSmithGenerator i := by
    have h := DegreeFive.collectedRelationRow_head L L
      (canonicalFreeLieEvaluation L) 1 i
    exact congrArg Subtype.val h
  simp_rw [hrow] at hcomp
  change smithLieImage (DegreeFive.freeLieLengthComponent L 1
    (r : CanonicalFreeLie L)) = _
  rw [hcomp]
  simp only [smithLieImage, map_sum, map_zsmul, smul_smul,
    freeAlgebraToFirstSmith_firstSmithGenerator]
  apply Finset.sum_congr rfl
  intro i hi
  module

private theorem wordCoefficient_relationComponent_one [Finite L]
    (r : DegreeFive.CanonicalLieRelationsIdeal L)
    (k : FirstSmithIndex L) :
    wordCoefficient [k] (relationComponent 1 r) =
      firstSmithDiagonal k * firstSmithRelationCoefficient r k := by
  classical
  rw [relationComponent_one_eq_firstRows]
  simp only [map_sum, map_zsmul, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l hl hlk
    simp [hlk]
  · simp

private theorem NormalizedDimensionFourWitness.wordCoefficient_passiD_dvd
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) :
    (passiTripleGCD i j k : ℤ) ∣ wordCoefficient [j, k] (w.passiD i) := by
  classical
  unfold NormalizedDimensionFourWitness.passiD
  rw [map_finsuppSum]
  apply Finset.dvd_sum
  intro p hp
  change (passiTripleGCD i j k : ℤ) ∣
    wordCoefficient [j, k] ((w.relationTerms p) •
      (rightCoeff i (w.multiplierComponent 2 p) *
        relationComponent 1 p.2))
  rw [LinearMap.map_smul, wordCoefficient_mul_exact_one,
    wordCoefficient_relationComponent_one, smul_eq_mul]
  · have hdiagNat := passiTripleGCD_dvd_diagonal i j k k
      (Or.inr (Or.inr rfl))
    have hdiag : (passiTripleGCD i j k : ℤ) ∣ firstSmithDiagonal k := by
      unfold firstSmithDiagonal
      exact_mod_cast hdiagNat
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_left hdiag
          (firstSmithRelationCoefficient p.2 k))
        (wordCoefficient [j] (rightCoeff i (w.multiplierComponent 2 p))))
      (w.relationTerms p)
  · exact rightCoeff_mem_associativeExact i 1 (w.multiplierComponent 2 p)
      (DegreeFive.associativeLengthComponent_mem_exact
        (FirstSmithIndex L) 2 (w.multiplierImage p))

/-- Passi's three-diagonal divisibility of the bracket coefficient
`f_{ijk}`. -/
private theorem NormalizedDimensionFourWitness.passiF_tripleGCD_dvd
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) (hkj : k < j) :
    (passiTripleGCD i j k : ℤ) ∣ w.passiFCoefficients i j k := by
  have heq := congrArg (wordCoefficient [j, k])
    (w.rightCoeff_component_three i)
  rw [wordCoefficient_rightCoeff, map_add,
    w.wordCoefficient_passiC i j k hkj] at heq
  have hthree := w.wordCoefficient_component_three_dvd i j k
  have hD := w.wordCoefficient_passiD_dvd i j k
  have hsub := hthree.sub hD
  convert hsub using 1
  rw [heq]
  module

private def NormalizedDimensionFourWitness.passiFQuotient [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) : ℤ :=
  if h : k < j then Classical.choose (w.passiF_tripleGCD_dvd i j k h) else 0

private theorem NormalizedDimensionFourWitness.passiF_eq_gcd_mul_quotient
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) (hkj : k < j) :
    w.passiFCoefficients i j k =
      (passiTripleGCD i j k : ℤ) * w.passiFQuotient i j k := by
  simp only [NormalizedDimensionFourWitness.passiFQuotient, hkj, dif_pos]
  exact Classical.choose_spec (w.passiF_tripleGCD_dvd i j k hkj)

private def NormalizedDimensionFourWitness.passiFAlpha [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) : ℤ :=
  let di := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 i
  let dj := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 j
  let dk := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 k
  w.passiFQuotient i j k * di.gcdA (Nat.gcd dj dk)

private def NormalizedDimensionFourWitness.passiFBeta [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) : ℤ :=
  let di := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 i
  let dj := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 j
  let dk := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 k
  w.passiFQuotient i j k * di.gcdB (Nat.gcd dj dk) * dj.gcdA dk

private def NormalizedDimensionFourWitness.passiFGamma [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) : ℤ :=
  let di := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 i
  let dj := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 j
  let dk := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 k
  w.passiFQuotient i j k * di.gcdB (Nat.gcd dj dk) * dj.gcdB dk

private theorem NormalizedDimensionFourWitness.passiF_diagonal_decomposition
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i j k : FirstSmithIndex L) (hkj : k < j) :
    w.passiFCoefficients i j k =
      firstSmithDiagonal i * w.passiFAlpha i j k +
      firstSmithDiagonal j * w.passiFBeta i j k +
      firstSmithDiagonal k * w.passiFGamma i j k := by
  let di := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 i
  let dj := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 j
  let dk := DegreeFive.collectedDiagonal L L
    (canonicalFreeLieEvaluation L) 1 k
  have hg₁ : (passiTripleGCD i j k : ℤ) =
      firstSmithDiagonal i * di.gcdA (Nat.gcd dj dk) +
        (Nat.gcd dj dk : ℤ) * di.gcdB (Nat.gcd dj dk) := by
    simpa only [passiTripleGCD, firstSmithDiagonal, di, dj, dk] using
      Nat.gcd_eq_gcd_ab di (Nat.gcd dj dk)
  have hg₂ : (Nat.gcd dj dk : ℤ) =
      firstSmithDiagonal j * dj.gcdA dk +
        firstSmithDiagonal k * dj.gcdB dk := by
    simpa only [firstSmithDiagonal, dj, dk] using Nat.gcd_eq_gcd_ab dj dk
  rw [w.passiF_eq_gcd_mul_quotient i j k hkj, hg₁, hg₂]
  simp only [NormalizedDimensionFourWitness.passiFAlpha,
    NormalizedDimensionFourWitness.passiFBeta,
    NormalizedDimensionFourWitness.passiFGamma, di, dj, dk]
  ring

private theorem smithDiagonalGenerator_mem_highTwo_add_relation [Finite L]
    (i : FirstSmithIndex L) :
    firstSmithDiagonal i • FreeAlgebra.ι ℤ i ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 2 +
        smithRelationIdeal (L := L) := by
  let rho : DegreeFive.CanonicalLieRelationsIdeal L :=
    ⟨(DegreeFive.collectedRelationRow L L
      (canonicalFreeLieEvaluation L) 1 i : CanonicalFreeLie L),
      DegreeFive.collectedRelationRow_mem_ker L L
        (canonicalFreeLieEvaluation L) 1 i⟩
  have hrho : smithLieImage (rho : CanonicalFreeLie L) ∈
      smithRelationIdeal (L := L) :=
    smithLieImage_relation_mem_relationIdeal rho
  have htail : smithLieImage (firstSmithTail i) ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 2 := by
    apply freeAlgebraToFirstSmith_preserves_high
    exact DegreeFive.freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh L
      (firstSmithTail_mem_lieHigh_two i)
  have heq : firstSmithDiagonal i • FreeAlgebra.ι ℤ i =
      smithLieImage (rho : CanonicalFreeLie L) - smithLieImage (firstSmithTail i) := by
    have hrhoEq : (rho : CanonicalFreeLie L) =
        firstSmithDiagonal i • firstSmithGenerator i + firstSmithTail i := by
      unfold rho firstSmithTail
      abel
    rw [hrhoEq]
    simp only [smithLieImage, map_add, map_zsmul,
      freeAlgebraToFirstSmith_firstSmithGenerator]
    abel
  rw [heq]
  apply (FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 2 +
    smithRelationIdeal (L := L)).sub_mem
  · exact (show smithRelationIdeal (L := L) ≤ _ from le_sup_right) hrho
  · exact (show FreeLieDimension.associativeHighIdeal
      (FirstSmithIndex L) 2 ≤ _ from le_sup_left) htail

private theorem smithDiagonalBracket_mem_highThree_add_relation [Finite L]
    (i j : FirstSmithIndex L) :
    firstSmithDiagonal i •
        smithLieImage ⁅firstSmithGenerator i, firstSmithGenerator j⁆ ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
        smithRelationIdeal (L := L) := by
  let H2 := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 2
  let H3 := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3
  let R := smithRelationIdeal (L := L)
  obtain ⟨h, hh, r, hr, hdecomp⟩ := Submodule.mem_sup.mp
    (smithDiagonalGenerator_mem_highTwo_add_relation (L := L) i)
  have hXi : FreeAlgebra.ι ℤ j ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 1 :=
    FreeLieDimension.freeAlgebra_i_mem_associativeHigh_one
      (FirstSmithIndex L) j
  have hhRight : h * FreeAlgebra.ι ℤ j ∈ H3 := by
    change h * FreeAlgebra.ι ℤ j ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 3
    change h ∈ FreeLieDimension.associativeHigh (FirstSmithIndex L) 2 at hh
    exact FreeLieDimension.associativeHigh_mul (FirstSmithIndex L) hh hXi
  have hhLeft : FreeAlgebra.ι ℤ j * h ∈ H3 := by
    change FreeAlgebra.ι ℤ j * h ∈
      FreeLieDimension.associativeHigh (FirstSmithIndex L) 3
    exact FreeLieDimension.associativeHigh_mul (FirstSmithIndex L) hXi hh
  have hrRight : r * FreeAlgebra.ι ℤ j ∈ R := by
    change r * FreeAlgebra.ι ℤ j ∈ TwoSidedIdeal.span _
    exact (TwoSidedIdeal.span _).mul_mem_right _ _ hr
  have hrLeft : FreeAlgebra.ι ℤ j * r ∈ R := R.mul_mem_left _ hr
  have heq : firstSmithDiagonal i •
      smithLieImage ⁅firstSmithGenerator i, firstSmithGenerator j⁆ =
      (h * FreeAlgebra.ι ℤ j - FreeAlgebra.ι ℤ j * h) +
        (r * FreeAlgebra.ι ℤ j - FreeAlgebra.ι ℤ j * r) := by
    have hbracket : smithLieImage
        ⁅firstSmithGenerator i, firstSmithGenerator j⁆ =
        FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j -
          FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i := by
      simp only [smithLieImage, LieHom.map_lie,
        LieRing.of_associative_ring_bracket, map_sub, map_mul,
        freeAlgebraToFirstSmith_firstSmithGenerator]
    rw [hbracket, smul_sub, ← smul_mul_assoc, ← mul_smul_comm]
    calc
      (firstSmithDiagonal i • FreeAlgebra.ι ℤ i) * FreeAlgebra.ι ℤ j -
          FreeAlgebra.ι ℤ j *
            (firstSmithDiagonal i • FreeAlgebra.ι ℤ i) =
          (h + r) * FreeAlgebra.ι ℤ j -
            FreeAlgebra.ι ℤ j * (h + r) := by rw [hdecomp]
      _ = _ := by noncomm_ring
  rw [heq]
  apply (H3 + R).add_mem
  · exact (show H3 ≤ H3 + R from le_sup_left) (H3.sub_mem hhRight hhLeft)
  · exact (show R ≤ H3 + R from le_sup_right) (R.sub_mem hrRight hrLeft)

private def NormalizedDimensionFourWitness.passiQ [Finite L]
    {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) : CanonicalFreeLie L :=
  ∑ j, ∑ k, if k < j then w.passiFAlpha i j k •
    ⁅firstSmithGenerator j, firstSmithGenerator k⁆ else 0

private theorem NormalizedDimensionFourWitness.passiQ_mem_gammaTwo
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    w.passiQ i ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 1 := by
  classical
  unfold NormalizedDimensionFourWitness.passiQ
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.sum_mem
  intro k hk
  by_cases hkj : k < j
  · simp only [hkj, if_true]
    apply (lowerCentralSeries ℤ (CanonicalFreeLie L) 1).smul_mem
    change _ ∈ LieModule.lowerCentralSeries ℤ
      (CanonicalFreeLie L) (CanonicalFreeLie L) (0 + 1)
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _)
      (LieSubmodule.mem_top _)
  · simp [hkj]

/-- Passi's term-by-term substitution of the three diagonal heads in
`C_i`; only the `e_i` part remains. -/
private theorem NormalizedDimensionFourWitness.passiC_sub_diagonalQ_mem
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    smithLieImage (w.passiC i) -
        firstSmithDiagonal i • smithLieImage (w.passiQ i) ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
        smithRelationIdeal (L := L) := by
  classical
  rw [w.passiC_eq_brackets i]
  unfold NormalizedDimensionFourWitness.passiQ
  simp only [smithLieImage, map_sum, apply_ite, map_zsmul, map_zero,
    Finset.smul_sum, smul_ite, smul_zero, smul_smul]
  rw [← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro j hj
  rw [← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro k hk
  by_cases hkj : k < j
  · simp only [hkj, if_true]
    let B := smithLieImage ⁅firstSmithGenerator j, firstSmithGenerator k⁆
    have hdecomp := w.passiF_diagonal_decomposition i j k hkj
    have heq : w.passiFCoefficients i j k • B -
        (firstSmithDiagonal i * w.passiFAlpha i j k) • B =
        w.passiFBeta i j k •
            (firstSmithDiagonal j • B) +
          w.passiFGamma i j k •
            (firstSmithDiagonal k • B) := by
      rw [hdecomp]
      module
    change w.passiFCoefficients i j k • B -
      (firstSmithDiagonal i * w.passiFAlpha i j k) • B ∈
        FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
          smithRelationIdeal (L := L)
    rw [heq]
    apply (FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
      smithRelationIdeal (L := L)).add_mem
    · apply zsmul_mem
      exact smithDiagonalBracket_mem_highThree_add_relation j k
    · apply zsmul_mem
      have hskew : firstSmithDiagonal k • B =
          -(firstSmithDiagonal k •
            smithLieImage ⁅firstSmithGenerator k, firstSmithGenerator j⁆) := by
        dsimp only [B]
        rw [show ⁅firstSmithGenerator j, firstSmithGenerator k⁆ =
            -⁅firstSmithGenerator k, firstSmithGenerator j⁆ by
          exact (lie_skew _ _).symm]
        simp only [smithLieImage, map_neg, smul_neg]
      rw [hskew]
      exact (FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
        smithRelationIdeal (L := L)).neg_mem
          (smithDiagonalBracket_mem_highThree_add_relation k j)
  · simp [hkj]

private theorem NormalizedDimensionFourWitness.passiRowTwo
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    normalFormRow (fun j : FirstSmithIndex L ↦ FreeAlgebra.ι ℤ j)
        w.finalCoefficients i +
      firstSmithDiagonal i • smithLieImage (w.passiQ i) ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
        smithRelationIdeal (L := L) := by
  let H := FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
    smithRelationIdeal (L := L)
  have hrow := w.passiRowOne i
  have hD := w.passiD_mem i
  have hC := w.passiC_sub_diagonalQ_mem i
  have h := H.sub_mem (H.sub_mem hrow hD) hC
  convert h using 1 <;> module

/-- Evaluation of the Smith free associative algebra in `U(L)`. -/
private def smithEvaluation [Finite L] :
    FreeAlgebra ℤ (FirstSmithIndex L) →ₐ[ℤ] UEA ℤ L :=
  (UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L)).comp
    ((FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L).symm.toAlgHom.comp
      (freeAlgebraFromFirstSmith (L := L)))

private theorem smithEvaluation_smithLieImage [Finite L]
    (x : CanonicalFreeLie L) :
    smithEvaluation (L := L) (smithLieImage x) =
      UniversalEnvelopingAlgebra.ι ℤ (canonicalFreeLieEvaluation L x) := by
  have hback := congrArg
    (fun f : FreeAlgebra ℤ L →ₐ[ℤ] FreeAlgebra ℤ L ↦
      f (PBW.freeLieToFreeAlgebra ℤ L x))
    (freeAlgebraFromFirstSmith_comp_toFirstSmith (L := L))
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at hback
  unfold smithEvaluation smithLieImage
  change UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L)
      ((FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L).symm
        (freeAlgebraFromFirstSmith (L := L)
          (freeAlgebraToFirstSmith (L := L)
            (PBW.freeLieToFreeAlgebra ℤ L x)))) = _
  rw [hback]
  rw [← FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra]
  simp only [AlgEquiv.symm_apply_apply, UEA.map_ι]

@[simp]
private theorem smithEvaluation_iota [Finite L] (i : FirstSmithIndex L) :
    smithEvaluation (L := L) (FreeAlgebra.ι ℤ i) =
      UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue i) := by
  rw [← smithLieImage_firstSmithGenerator (L := L) i,
    smithEvaluation_smithLieImage]
  rfl

private theorem smithEvaluation_word_mem_augmentation_three [Finite L]
    (xs : List (FirstSmithIndex L)) (hxs : 3 ≤ xs.length) :
    smithEvaluation (L := L)
        (DegreeFive.freeAlgebraWord (FirstSmithIndex L) xs) ∈
      UEA.augmentationIdeal ℤ L ^ 3 := by
  rcases xs with _ | ⟨i, xs⟩
  · simp at hxs
  rcases xs with _ | ⟨j, xs⟩
  · simp at hxs
  rcases xs with _ | ⟨k, xs⟩
  · simp at hxs
  let A := UEA.augmentationIdeal ℤ L
  have hi : UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue i) ∈ A :=
    UEA.ι_mem_augmentationIdeal ℤ L _
  have hj : UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue j) ∈ A :=
    UEA.ι_mem_augmentationIdeal ℤ L _
  have hk : UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue k) ∈ A :=
    UEA.ι_mem_augmentationIdeal ℤ L _
  have hij : UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue i) *
      UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue j) ∈ A ^ 2 := by
    have h := Ideal.mul_mem_mul hi hj
    simpa only [show (2 : ℕ) = 1 + 1 by rfl, Ideal.IsTwoSided.pow_add,
      Submodule.pow_one] using h
  have hijk : (UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue i) *
        UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue j)) *
      UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue k) ∈ A ^ 3 := by
    have h := Ideal.mul_mem_mul hij hk
    simpa only [show (3 : ℕ) = 2 + 1 by rfl, Ideal.IsTwoSided.pow_add,
      Submodule.pow_one] using h
  have hfull : UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue i) *
        (UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue j) *
          (UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue k) *
            smithEvaluation (L := L)
              (DegreeFive.freeAlgebraWord (FirstSmithIndex L) xs))) ∈ A ^ 3 := by
    rw [show UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue i) *
          (UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue j) *
            (UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue k) *
              smithEvaluation (L := L)
                (DegreeFive.freeAlgebraWord (FirstSmithIndex L) xs))) =
        ((UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue i) *
            UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue j)) *
          UniversalEnvelopingAlgebra.ι ℤ (firstSmithValue k)) *
            smithEvaluation (L := L)
              (DegreeFive.freeAlgebraWord (FirstSmithIndex L) xs) by
      noncomm_ring]
    exact (A ^ 3).mul_mem_right _ hijk
  simpa only [DegreeFive.freeAlgebraWord_cons, map_mul,
    smithEvaluation_iota] using hfull

private theorem smithEvaluation_mem_associativeHigh_three [Finite L]
    {p : FreeAlgebra ℤ (FirstSmithIndex L)}
    (hp : p ∈ FreeLieDimension.associativeHigh (FirstSmithIndex L) 3) :
    smithEvaluation (L := L) p ∈ UEA.augmentationIdeal ℤ L ^ 3 := by
  classical
  rw [← freeAlgebra_word_sum_eq p, map_finsuppSum]
  apply Submodule.sum_mem
  intro w hw
  change smithEvaluation (L := L)
    ((FreeAlgebra.equivMonoidAlgebraFreeMonoid p w) •
      DegreeFive.freeAlgebraWord (FirstSmithIndex L)
        (FreeMonoid.toList w)) ∈ _
  rw [map_zsmul]
  apply zsmul_mem
  apply smithEvaluation_word_mem_augmentation_three
  simpa [FreeMonoid.length] using hp hw

private theorem smithEvaluation_mem_relationIdeal_eq_zero [Finite L]
    {p : FreeAlgebra ℤ (FirstSmithIndex L)}
    (hp : p ∈ smithRelationIdeal (L := L)) :
    smithEvaluation (L := L) p = 0 := by
  change p ∈ TwoSidedIdeal.span _ at hp
  induction hp using TwoSidedIdeal.span_induction with
  | mem p hp =>
      obtain ⟨r, rfl⟩ := hp
      rw [smithEvaluation_smithLieImage]
      calc
        UniversalEnvelopingAlgebra.ι ℤ
            (canonicalFreeLieEvaluation L (r : CanonicalFreeLie L)) =
            UniversalEnvelopingAlgebra.ι ℤ 0 :=
          congrArg (UniversalEnvelopingAlgebra.ι ℤ) r.property
        _ = 0 := map_zero _
  | zero => exact map_zero _
  | add p q hp hq ihp ihq => simp [ihp, ihq]
  | neg p hp ih => simp [ih]
  | left_absorb a p hp ih => simp [ih]
  | right_absorb a p hp ih => simp [ih]

private theorem smithEvaluation_mem_highThree_add_relation [Finite L]
    {p : FreeAlgebra ℤ (FirstSmithIndex L)}
    (hp : p ∈
      FreeLieDimension.associativeHighIdeal (FirstSmithIndex L) 3 +
        smithRelationIdeal (L := L)) :
    smithEvaluation (L := L) p ∈ UEA.augmentationIdeal ℤ L ^ 3 := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hp
  obtain ⟨h, hh, r, hr, rfl⟩ := hp
  rw [map_add, smithEvaluation_mem_relationIdeal_eq_zero hr, add_zero]
  exact smithEvaluation_mem_associativeHigh_three hh

private theorem smithEvaluation_normalFormRow [Finite L]
    (a : FirstSmithIndex L → FirstSmithIndex L → ℤ)
    (i : FirstSmithIndex L) :
    smithEvaluation (L := L)
        (normalFormRow (fun j : FirstSmithIndex L ↦ FreeAlgebra.ι ℤ j) a i) =
      UniversalEnvelopingAlgebra.ι ℤ
        (normalFormRow firstSmithValue a i) := by
  classical
  simp only [normalFormRow, map_sub, map_sum, apply_ite, map_zsmul,
    map_zero, smithEvaluation_iota]

private theorem NormalizedDimensionFourWitness.passiRowValue_mem_gammaThree
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b)
    (i : FirstSmithIndex L) :
    normalFormRow firstSmithValue w.finalCoefficients i +
        firstSmithDiagonal i •
          canonicalFreeLieEvaluation L (w.passiQ i) ∈
      lowerCentralSeries ℤ L 2 := by
  have hmap := smithEvaluation_mem_highThree_add_relation (w.passiRowTwo i)
  have heval : smithEvaluation (L := L)
      (normalFormRow (fun j : FirstSmithIndex L ↦ FreeAlgebra.ι ℤ j)
          w.finalCoefficients i +
        firstSmithDiagonal i • smithLieImage (w.passiQ i)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (normalFormRow firstSmithValue w.finalCoefficients i +
          firstSmithDiagonal i •
            canonicalFreeLieEvaluation L (w.passiQ i)) := by
    rw [map_add, map_zsmul, smithEvaluation_normalFormRow,
      smithEvaluation_smithLieImage, map_add, map_zsmul]
  rw [heval] at hmap
  have hdelta : normalFormRow firstSmithValue w.finalCoefficients i +
        firstSmithDiagonal i • canonicalFreeLieEvaluation L (w.passiQ i) ∈
      dimensionSubring ℤ L 3 :=
    (mem_dimensionSubring ℤ L).mpr hmap
  rw [dimensionSubring_three_eq_lowerCentralSeries_two L] at hdelta
  exact hdelta

private theorem NormalizedDimensionFourWitness.evaluates_component_two
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    canonicalFreeLieEvaluation L (w.component 2 : CanonicalFreeLie L) =
      normalFormValue firstSmithValue w.finalCoefficients := by
  classical
  rw [w.component_two_eq_final]
  simp only [normalFormValue, map_sum, apply_ite, map_zsmul, map_zero,
    LieHom.map_lie, firstSmithValue]

private theorem NormalizedDimensionFourWitness.represents_by_component_two
    [Finite L] {b : L} (w : NormalizedDimensionFourWitness b) :
    b - normalFormValue firstSmithValue w.finalCoefficients ∈
      lowerCentralSeries ℤ L 3 := by
  have hremFree : w.lieLift - (w.component 2 : CanonicalFreeLie L) -
        (w.component 3 : CanonicalFreeLie L) ∈
      lowerCentralSeries ℤ (CanonicalFreeLie L) 3 := by
    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 3] using
      w.lieLift_sub_components_mem_high_four
  have hrem := (LieIdeal.map_lowerCentralSeries_le
    (R := ℤ) (f := canonicalFreeLieEvaluation L) 3)
      (LieIdeal.mem_map hremFree)
  have hthree := w.evaluated_component_three_mem_gammaFour
  have hsum := (lowerCentralSeries ℤ L 3).add_mem hrem hthree
  rw [map_sub, map_sub, w.evaluates, w.evaluates_component_two] at hsum
  convert hsum using 1 <;> module

/-- The finite Bartholdi--Passi certificate, constructed directly from
the normalized relation equation. -/
private theorem finite_normalFormCertificate [Finite L]
    (b : L) (hb : b ∈ dimensionSubring ℤ L 4) :
    Nonempty (NormalFormCertificate.{u, 0} b) := by
  classical
  obtain ⟨w⟩ := exists_normalizedDimensionFourWitness b hb
  let y : FirstSmithIndex L → L := fun i ↦
    -canonicalFreeLieEvaluation L (w.passiQ i)
  let z : FirstSmithIndex L → L := fun i ↦
    normalFormRow firstSmithValue w.finalCoefficients i +
      firstSmithDiagonal i • canonicalFreeLieEvaluation L (w.passiQ i)
  refine ⟨{
    ι := FirstSmithIndex L
    fintype_ι := inferInstance
    linearOrder_ι := inferInstance
    x := firstSmithValue
    a := w.finalCoefficients
    e := firstSmithDiagonal
    y := y
    z := z
    represents := w.represents_by_component_two
    row_decomposition := ?_
    head_mem_gammaTwo := firstSmithDiagonal_smul_value_mem_gammaTwo
    y_mem_gammaTwo := ?_
    z_mem_gammaThree := ?_ }⟩
  · intro i
    dsimp only [y, z]
    module
  · intro i
    dsimp only [y]
    apply (lowerCentralSeries ℤ L 1).neg_mem
    apply (LieIdeal.map_lowerCentralSeries_le
      (R := ℤ) (f := canonicalFreeLieEvaluation L) 1)
    exact LieIdeal.mem_map (w.passiQ_mem_gammaTwo i)
  · intro i
    exact w.passiRowValue_mem_gammaThree i

def FiniteBartholdiPassiExtractionProperty : Prop :=
  ∀ (M : Type u) [LieRing M] [Finite M]
    (b : M), b ∈ dimensionSubring ℤ M 4 →
    Nonempty (NormalFormCertificate.{u, 0} b)

/-- The direct Bartholdi--Passi coefficient calculation supplies the finite
normal-form certificate. -/
theorem finiteBartholdiPassiExtraction :
    FiniteBartholdiPassiExtractionProperty.{u} := by
  intro M _ _ b hb
  exact finite_normalFormCertificate b hb

/-- Exact finite target needed by the residual-finiteness promotion. -/
def FiniteTwoDeltaFourProperty : Prop :=
  ∀ (M : Type u) [LieRing M] [Finite M]
    (b : M), b ∈ dimensionSubring ℤ M 4 →
    2 • b ∈ lowerCentralSeries ℤ M 3

/-- The finite coefficient theorem implies the normal form for every finite Lie ring. -/
theorem finiteNormalForm_of_extraction
    (h : FiniteBartholdiPassiExtractionProperty.{u})
    (M : Type u) [LieRing M] [Finite M]
    (b : M) (hb : b ∈ dimensionSubring ℤ M 4) :
    Nonempty (NormalFormCertificate.{u, 0} b) :=
  h M b hb

/-- The finite coefficient theorem already gives the exponent-two conclusion on every finite
Lie ring. -/
theorem finite_twoDeltaFour_of_extraction
    (h : FiniteBartholdiPassiExtractionProperty.{u})
    (M : Type u) [LieRing M] [Finite M]
    (b : M) (hb : b ∈ dimensionSubring ℤ M 4) :
    2 • b ∈ lowerCentralSeries ℤ M 3 := by
  obtain ⟨c⟩ := finiteNormalForm_of_extraction h M b hb
  simpa only [ofNat_zsmul] using
    c.two_smul_mem_lowerCentralSeries_three

theorem finiteTwoDeltaFour_of_extraction
    (h : FiniteBartholdiPassiExtractionProperty.{u}) :
    FiniteTwoDeltaFourProperty.{u} :=
  fun M _ _ b hb ↦ finite_twoDeltaFour_of_extraction h M b hb

end FiniteTarget

/-! ## Residually finite passage

A finitely generated Abelian group is separated by quotients by `nG`.  We use the explicit
structure theorem already used by the degree-five reduction, because quotients by scalar
multiples are automatically Lie ideals.
-/

theorem exists_multiple_quotient_detecting
    {G : Type*} [AddCommGroup G] [Module.Finite ℤ G]
    {c : G} (hc : c ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ¬ ∃ x : G, (n : ℤ) • x = c := by
  classical
  letI : AddGroup.FG G := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨m, ι, fintypeι, p, hp, e, ⟨E⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  letI : Fintype ι := fintypeι
  have hEc : E c ≠ 0 := fun h ↦ hc (E.injective (h.trans (map_zero E).symm))
  by_cases hfree : (E c).1 = 0
  · have htor : (E c).2 ≠ 0 := by
      intro h
      exact hEc (Prod.ext hfree h)
    obtain ⟨i, hi⟩ : ∃ i : ι, (E c).2 i ≠ 0 := by
      by_contra h
      push Not at h
      exact htor (DFinsupp.ext fun i ↦ by simpa using h i)
    let n := p i ^ e i
    have hn : n ≠ 0 := pow_ne_zero _ (hp i).ne_zero
    refine ⟨n, hn, ?_⟩
    rintro ⟨x, hx⟩
    have hmap := congrArg (fun z ↦ (E z).2 i) hx
    have hzero : (E ((n : ℤ) • x)).2 i = 0 := by
      rw [map_zsmul]
      change (n : ℤ) • (E x).2 i = 0
      rw [zsmul_eq_mul]
      have hcast : ((n : ℤ) : ZMod n) = 0 :=
        (CharP.intCast_eq_zero_iff (ZMod n) n (n : ℤ)).2 dvd_rfl
      rw [hcast, zero_mul]
    exact hi (hmap.symm.trans hzero)
  · obtain ⟨j, hj⟩ : ∃ j : Fin m, (E c).1 j ≠ 0 := by
      by_contra h
      push Not at h
      exact hfree (Finsupp.ext fun j ↦ by simpa using h j)
    let n : ℕ := ((E c).1 j).natAbs + 1
    have hn : n ≠ 0 := by simp [n]
    refine ⟨n, hn, ?_⟩
    rintro ⟨x, hx⟩
    have hmap := congrArg (fun z ↦ (E z).1 j) hx
    have hdvd : (n : ℤ) ∣ (E c).1 j := by
      refine ⟨(E x).1 j, ?_⟩
      simpa [map_zsmul, smul_eq_mul] using hmap.symm
    have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hj
    rw [Int.natAbs_natCast] at hle
    dsimp [n] at hle
    omega

/-- Finitary witness needed to pass the finite Bartholdi--Passi calculation to an arbitrary
Lie ring.  Only the class-three quotient of the witness has to be module-finite. -/
def FiniteWitnessProperty (M : Type u) [LieRing M] : Prop :=
  ∀ (b : M), b ∈ dimensionSubring ℤ M 4 →
    ∃ (A : Type u) (instA : LieRing A),
      letI : LieRing A := instA
      ∃ (f : A →ₗ⁅ℤ⁆ M) (a : A),
        Function.Injective f ∧ f a = b ∧
        a ∈ dimensionSubring ℤ A 4 ∧
        Nonempty (Module.Finite ℤ (DegreeFive.ClassThreeQuotient A))

/-- A fourth-dimension witness involves only finitely many generators and relations. -/
theorem finiteWitnessProperty (M : Type u) [LieRing M] :
    FiniteWitnessProperty M := by
  classical
  intro b hb
  obtain ⟨w, hw⟩ := exists_freeDimensionFourWitness_gammaTwo b hb
  obtain ⟨c, hc⟩ := w.exists_relation_finsupp
  let T : Finset (UEA ℤ (CanonicalFreeLie M)) :=
    insert (UniversalEnvelopingAlgebra.ι ℤ w.lieLift)
      (c.support.image fun p ↦
        UniversalEnvelopingAlgebra.ι ℤ (p.1 : CanonicalFreeLie M))
  obtain ⟨S₀, hS₀⟩ :=
    DegreeFive.exists_finset_fixedBy_ueaRename_finset T
  let S : Finset M := insert b S₀
  let retract : M → S := fun y ↦
    if hy : y ∈ S then ⟨y, hy⟩ else ⟨b, Finset.mem_insert_self b S₀⟩
  have retract_coe {y : M} (hy : y ∈ S) : (retract y : M) = y := by
    simp [retract, hy]
  let forward : CanonicalFreeLie M →ₗ⁅ℤ⁆ FreeLieAlgebra ℤ S :=
    DegreeFive.freeLieRename retract
  let backward : FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ CanonicalFreeLie M :=
    DegreeFive.freeLieRename (fun y : S ↦ (y : M))
  let forwardUEA : UEA ℤ (CanonicalFreeLie M) →ₐ[ℤ]
      UEA ℤ (FreeLieAlgebra ℤ S) :=
    UEA.map ℤ (CanonicalFreeLie M) (FreeLieAlgebra ℤ S) forward
  let backwardUEA : UEA ℤ (FreeLieAlgebra ℤ S) →ₐ[ℤ]
      UEA ℤ (CanonicalFreeLie M) :=
    UEA.map ℤ (FreeLieAlgebra ℤ S) (CanonicalFreeLie M) backward
  have hcomposite : backward.comp forward =
      DegreeFive.freeLieRename (fun y : M ↦ ((retract y : S) : M)) := by
    apply FreeLieAlgebra.hom_ext
    intro y
    change DegreeFive.freeLieRename (fun z : S ↦ (z : M))
        (DegreeFive.freeLieRename retract (FreeLieAlgebra.of ℤ y)) =
      DegreeFive.freeLieRename (fun y : M ↦ ((retract y : S) : M))
        (FreeLieAlgebra.of ℤ y)
    rw [DegreeFive.freeLieRename_of, DegreeFive.freeLieRename_of,
      DegreeFive.freeLieRename_of]
  have hroundUEA {q : UEA ℤ (CanonicalFreeLie M)} (hq : q ∈ T) :
      backwardUEA (forwardUEA q) = q := by
    rw [show backwardUEA (forwardUEA q) =
        UEA.map ℤ (FreeLieAlgebra ℤ S) (CanonicalFreeLie M) backward
          (UEA.map ℤ (CanonicalFreeLie M) (FreeLieAlgebra ℤ S) forward q) by rfl,
      UEA.map_comp, hcomposite]
    apply hS₀ (fun y : M ↦ ((retract y : S) : M))
    · intro y hy
      exact retract_coe (Finset.mem_insert_of_mem hy)
    · exact hq
  have hroundLie {z : CanonicalFreeLie M}
      (hz : UniversalEnvelopingAlgebra.ι ℤ z ∈ T) :
      backward (forward z) = z := by
    apply PBW.canonicalMap_injective_int (CanonicalFreeLie M)
    rw [← UEA.map_ι ℤ (FreeLieAlgebra ℤ S) (CanonicalFreeLie M) backward,
      ← UEA.map_ι ℤ (CanonicalFreeLie M) (FreeLieAlgebra ℤ S) forward]
    exact hroundUEA hz
  have hliftRound : backward (forward w.lieLift) = w.lieLift := by
    apply hroundLie
    exact Finset.mem_insert_self _ _
  have hrelationRound
      (p : DegreeFive.CanonicalLieRelationsIdeal M ×
        UEA ℤ (CanonicalFreeLie M)) (hp : p ∈ c.support) :
      backward (forward (p.1 : CanonicalFreeLie M)) = p.1 := by
    apply hroundLie
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  let evaluation : FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ M :=
    (canonicalFreeLieEvaluation M).comp backward
  let A : Type u := evaluation.range
  let evaluationA : FreeLieAlgebra ℤ S →ₗ⁅ℤ⁆ A :=
    evaluation.rangeRestrict
  let inclusion : A →ₗ⁅ℤ⁆ M := evaluation.range.incl
  let a : A := evaluationA (forward w.lieLift)
  refine ⟨A, inferInstance, inclusion, a, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact hxy
  · change canonicalFreeLieEvaluation M
      (backward (forward w.lieLift)) = b
    rw [hliftRound, w.evaluates]
  · rw [mem_dimensionSubring]
    let mapForward := UEA.map ℤ (CanonicalFreeLie M)
      (FreeLieAlgebra ℤ S) forward
    let mapEvaluation := UEA.map ℤ (FreeLieAlgebra ℤ S) A evaluationA
    have hrelationZero
        (p : DegreeFive.CanonicalLieRelationsIdeal M ×
          UEA ℤ (CanonicalFreeLie M)) (hp : p ∈ c.support) :
        evaluationA (forward (p.1 : CanonicalFreeLie M)) = 0 := by
      apply Subtype.ext
      change evaluation (forward (p.1 : CanonicalFreeLie M)) = 0
      change canonicalFreeLieEvaluation M
          (backward (forward (p.1 : CanonicalFreeLie M))) = 0
      rw [hrelationRound p hp]
      exact LinearMap.mem_ker.mp p.1.property
    have hleft :
        mapEvaluation (mapForward
          (c.sum (fun p n ↦ n •
            (UniversalEnvelopingAlgebra.ι ℤ
              (p.1 : CanonicalFreeLie M) * p.2)))) = 0 := by
      rw [map_finsuppSum, map_finsuppSum]
      unfold Finsupp.sum
      apply Finset.sum_eq_zero
      intro p hp
      change mapEvaluation (mapForward
        ((c p) • (UniversalEnvelopingAlgebra.ι ℤ
          (p.1 : CanonicalFreeLie M) * p.2))) = 0
      rw [map_zsmul, map_zsmul, map_mul, map_mul, UEA.map_ι, UEA.map_ι,
        hrelationZero p hp, map_zero, zero_mul, smul_zero]
    have heq := congrArg (fun q ↦ mapEvaluation (mapForward q)) hc
    have hdiff :
        UniversalEnvelopingAlgebra.ι ℤ a -
            mapEvaluation (mapForward w.highWord) = 0 := by
      change mapEvaluation (mapForward
          (c.sum (fun p n ↦ n •
            (UniversalEnvelopingAlgebra.ι ℤ
              (p.1 : CanonicalFreeLie M) * p.2)))) =
        mapEvaluation (mapForward
          (UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord)) at heq
      rw [map_sub, map_sub, UEA.map_ι, UEA.map_ι] at heq
      exact (hleft ▸ heq).symm
    rw [sub_eq_zero.mp hdiff]
    apply UEA.map_mem_augmentationIdeal_pow ℤ (FreeLieAlgebra ℤ S) A
      evaluationA 4
    apply UEA.map_mem_augmentationIdeal_pow ℤ (CanonicalFreeLie M)
      (FreeLieAlgebra ℤ S) forward 4
    exact w.highWord_mem
  · exact ⟨DegreeFive.moduleFinite_classThreeQuotient_of_surjective_free
      S A evaluationA evaluation.surjective_rangeRestrict⟩

/-- Residual finiteness promotes the finite Bartholdi--Passi coefficient calculation to the
standard theorem `2 δ₄ ⊆ γ₄` for arbitrary Lie rings. -/
theorem twoDeltaFourProperty_of_finite
    (h : FiniteTwoDeltaFourProperty.{u}) :
    DegreeFive.TwoDeltaFourProperty.{u} := by
  intro M _ b hb
  by_contra hbGamma
  obtain ⟨A, instA, f, a, hf, hfa, ha, hAfin⟩ :=
    finiteWitnessProperty M b hb
  letI : LieRing A := instA
  have htwoAGamma : 2 • a ∉ lowerCentralSeries ℤ A 3 := by
    intro haGamma
    have hmap : f (2 • a) ∈ lowerCentralSeries ℤ M 3 :=
      (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := f) 3)
        (LieIdeal.mem_map haGamma)
    rw [map_nsmul, hfa] at hmap
    exact hbGamma hmap
  let B : Type u := DegreeFive.ClassThreeQuotient A
  letI instB : LieRing B :=
    LieSubmodule.Quotient.lieQuotientLieRing (lowerCentralSeries ℤ A 3)
  let q : A →ₗ⁅ℤ⁆ B :=
    UEA.lieIdealQuotientMk ℤ A (lowerCentralSeries ℤ A 3)
  let ba : B := q a
  let c : B := 2 • ba
  letI : Module.Finite ℤ B := hAfin.some
  have hc0 : c ≠ 0 := by
    intro hc
    apply htwoAGamma
    apply (LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ A 3)).mp
    change q (2 • a) = 0
    rw [map_nsmul]
    exact hc
  obtain ⟨n, hn, hnDiv⟩ := exists_multiple_quotient_detecting hc0
  let J : LieIdeal ℤ B := DegreeFive.multipleIdeal B n
  let C : Type u := B ⧸ J
  let r : B →ₗ⁅ℤ⁆ C := UEA.lieIdealQuotientMk ℤ B J
  let d : C := r ba
  have hr : Function.Surjective r := by
    intro x
    exact Submodule.Quotient.mk_surjective J.toSubmodule x
  letI : Finite C := by
    dsimp only [C, J]
    exact DegreeFive.multipleQuotient_finite B n hn
  have hdDelta : d ∈ dimensionSubring ℤ C 4 := by
    apply map_mem_dimensionSubring ℤ B C r 4
    exact map_mem_dimensionSubring ℤ A B q 4 ha
  have hCclass : lowerCentralSeries ℤ C 3 = ⊥ := by
    change LieModule.lowerCentralSeries ℤ C C 3 = ⊥
    have hBclass :=
      DegreeFive.classThreeQuotient_lowerCentralSeries_three_eq_bot A
    change LieModule.lowerCentralSeries ℤ B B 3 = ⊥ at hBclass
    rw [← LieIdeal.lowerCentralSeries_map_eq 3 hr, hBclass]
    simp
  have htwoD := h C d hdDelta
  rw [hCclass] at htwoD
  have hrdzero : 2 • d = 0 := by simpa using htwoD
  have hrczero : r c = 0 := by
    change r (2 • ba) = 0
    rw [map_nsmul]
    exact hrdzero
  have hcJ : c ∈ J :=
    (LieSubmodule.Quotient.mk_eq_zero' (N := J)).mp hrczero
  obtain ⟨x, hx⟩ := (DegreeFive.mem_multipleIdeal_iff B n c).mp hcJ
  apply hnDiv
  refine ⟨x, ?_⟩
  simpa only [Nat.cast_smul_eq_nsmul ℤ] using hx

/-- A finite normal-form extraction is one way to supply the exact finite factor-two input. -/
theorem twoDeltaFourProperty_of_finite_extraction
    (h : FiniteBartholdiPassiExtractionProperty.{u}) :
    DegreeFive.TwoDeltaFourProperty.{u} :=
  twoDeltaFourProperty_of_finite (finiteTwoDeltaFour_of_extraction h)

/-- Once the finite coefficient extraction is supplied, the already completed standing
reduction gives the integral fifth-dimension theorem with no remaining hypotheses. -/
theorem dimensionSubring_five_le_lowerCentralSeries_three_of_finite_extraction
    (h : FiniteBartholdiPassiExtractionProperty.{u})
    (M : Type u) [LieRing M] :
    dimensionSubring ℤ M 5 ≤ lowerCentralSeries ℤ M 3 :=
  DegreeFive.dimensionSubring_five_le_lowerCentralSeries_three M
    (twoDeltaFourProperty_of_finite_extraction h)

/-- Bartholdi--Passi's factor-two theorem for every Lie ring over `ℤ`. -/
theorem twoDeltaFourProperty : DegreeFive.TwoDeltaFourProperty.{u} :=
  twoDeltaFourProperty_of_finite_extraction
    finiteBartholdiPassiExtraction

/-- For every Lie ring over `ℤ`, the fifth dimension subring is contained in
the fourth lower-central-series term. -/
theorem dimensionSubring_five_le_lowerCentralSeries_three
    (M : Type u) [LieRing M] :
    dimensionSubring ℤ M 5 ≤ lowerCentralSeries ℤ M 3 :=
  DegreeFive.dimensionSubring_five_le_lowerCentralSeries_three M
    twoDeltaFourProperty

end

end DegreeFour

end LieRings
