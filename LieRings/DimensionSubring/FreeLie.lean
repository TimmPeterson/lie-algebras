import LieRings.DimensionSubring.Centrality
import LieRings.PBW.HigginsEmbedding
import LieRings.PBW.Reduction
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Dimension subrings of free Lie rings

This file formalizes the length-grading proof of Bartholdi--Passi, Theorem 4.1.  A free Lie
ring is represented by bracketed words (`FreeMagma X`), while its enveloping algebra is the free
associative algebra, represented by ordinary words (`FreeMonoid X`).  Both carry the filtration by
minimum word length.  Associativization preserves length, and integral PBW makes its restriction
to the free Lie ring injective.  It follows that intersection with the `n`th augmentation power is
exactly the `n`th lower-central term.
-/

namespace LieRings

universe u

namespace FreeLieDimension

noncomputable section

variable (X : Type u)

local notation "N" => FreeNonUnitalNonAssocAlgebra ℤ X
local notation "F" => FreeLieAlgebra ℤ X
local notation "A" => FreeAlgebra ℤ X

/-- Non-associative polynomials supported on bracketed words of length at least `n`. -/
def magmaHigh (n : ℕ) : Submodule ℤ N :=
  Finsupp.supported ℤ ℤ {w : FreeMagma X | n ≤ w.length}

/-- Monoid polynomials supported on associative words of length at least `n`. -/
def monoidHigh (n : ℕ) : Submodule ℤ (MonoidAlgebra ℤ (FreeMonoid X)) :=
  Finsupp.supported ℤ ℤ {w : FreeMonoid X | n ≤ w.length}

/-- The minimum-word-length filtration on the free associative algebra. -/
def associativeHigh (n : ℕ) : Submodule ℤ A :=
  (monoidHigh X n).comap
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap)

/-- Non-associative polynomials supported on bracketed words shorter than `n`. -/
def magmaLow (n : ℕ) : Submodule ℤ N :=
  Finsupp.supported ℤ ℤ {w : FreeMagma X | w.length < n}

/-- Associative polynomials supported on words shorter than `n`. -/
def monoidLow (n : ℕ) : Submodule ℤ (MonoidAlgebra ℤ (FreeMonoid X)) :=
  Finsupp.supported ℤ ℤ {w : FreeMonoid X | w.length < n}

/-- The short-word submodule of the free associative algebra. -/
def associativeLow (n : ℕ) : Submodule ℤ A :=
  (monoidLow X n).comap
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap)

/-- Associative polynomials concentrated in one word length. -/
def monoidExact (n : ℕ) : Submodule ℤ (MonoidAlgebra ℤ (FreeMonoid X)) :=
  Finsupp.supported ℤ ℤ {w : FreeMonoid X | w.length = n}

/-- The homogeneous word-length-`n` submodule of the free associative algebra. -/
def associativeExact (n : ℕ) : Submodule ℤ A :=
  (monoidExact X n).comap
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap)

/-- The quotient map from non-associative words to the free Lie ring, as a linear map. -/
def freeLieMkLinear : N →ₗ[ℤ] F where
  toFun := FreeLieAlgebra.mk ℤ
  map_add' := map_add (FreeLieAlgebra.mk ℤ)
  map_smul' := map_smul (FreeLieAlgebra.mk ℤ)

/-- Evaluation of bracketed words in the commutator algebra of the free associative algebra. -/
def magmaToFreeAlgebraNonUnital : N →ₙₐ[ℤ] CommutatorRing A :=
  FreeNonUnitalNonAssocAlgebra.lift ℤ
    (fun x : X ↦ (FreeAlgebra.ι ℤ x : CommutatorRing A))

/-- Associativization of bracketed words, as a linear map. -/
def magmaToFreeAlgebra : N →ₗ[ℤ] A where
  toFun := magmaToFreeAlgebraNonUnital X
  map_add' := map_add (magmaToFreeAlgebraNonUnital X)
  map_smul' := map_smul (magmaToFreeAlgebraNonUnital X)

@[simp]
theorem magmaToFreeAlgebra_of (x : X) :
    magmaToFreeAlgebra X (FreeNonUnitalNonAssocAlgebra.of ℤ x) =
      FreeAlgebra.ι ℤ x :=
  by
    simp [magmaToFreeAlgebra, magmaToFreeAlgebraNonUnital]

@[simp]
theorem magmaToFreeAlgebra_mul (a b : N) :
    magmaToFreeAlgebra X (a * b) =
      ⁅magmaToFreeAlgebra X a, magmaToFreeAlgebra X b⁆ :=
  by
    change (magmaToFreeAlgebraNonUnital X) (a * b) = _
    exact (magmaToFreeAlgebraNonUnital X).map_mul a b

@[simp]
theorem magmaToFreeAlgebra_single_of (x : X) :
    magmaToFreeAlgebra X (Finsupp.single (FreeMagma.of x) 1) =
      FreeAlgebra.ι ℤ x := by
  change magmaToFreeAlgebra X (FreeNonUnitalNonAssocAlgebra.of ℤ x) = _
  exact magmaToFreeAlgebra_of X x

theorem magmaToFreeAlgebra_single_mul (a b : FreeMagma X) :
    magmaToFreeAlgebra X (Finsupp.single (a * b) 1) =
      ⁅magmaToFreeAlgebra X (Finsupp.single a 1),
        magmaToFreeAlgebra X (Finsupp.single b 1)⁆ := by
  let sa : N := Finsupp.single a 1
  let sb : N := Finsupp.single b 1
  have hs : (Finsupp.single (a * b) (1 : ℤ) : N) =
      sa * sb := by
    simpa only [sa, sb, one_mul] using
      (MonoidAlgebra.single_mul_single a b (1 : ℤ) (1 : ℤ)).symm
  rw [hs]
  exact magmaToFreeAlgebra_mul X sa sb

/-- The image in the free Lie ring of bracketed words of length at least `n`. -/
def lieHigh (n : ℕ) : Submodule ℤ F :=
  (magmaHigh X n).map (freeLieMkLinear X)

@[simp]
theorem mem_magmaHigh (n : ℕ) (p : N) :
    p ∈ magmaHigh X n ↔ ↑p.support ⊆ {w : FreeMagma X | n ≤ w.length} :=
  Iff.rfl

@[simp]
theorem mem_monoidHigh (n : ℕ) (p : MonoidAlgebra ℤ (FreeMonoid X)) :
    p ∈ monoidHigh X n ↔ ↑p.support ⊆ {w : FreeMonoid X | n ≤ w.length} :=
  Iff.rfl

@[simp]
theorem mem_associativeHigh (n : ℕ) (p : A) :
    p ∈ associativeHigh X n ↔
      FreeAlgebra.equivMonoidAlgebraFreeMonoid p ∈ monoidHigh X n :=
  Iff.rfl

@[simp]
theorem mem_associativeLow (n : ℕ) (p : A) :
    p ∈ associativeLow X n ↔
      FreeAlgebra.equivMonoidAlgebraFreeMonoid p ∈ monoidLow X n :=
  Iff.rfl

@[simp]
theorem mem_associativeExact (n : ℕ) (p : A) :
    p ∈ associativeExact X n ↔
      FreeAlgebra.equivMonoidAlgebraFreeMonoid p ∈ monoidExact X n :=
  Iff.rfl

theorem magmaHigh_mono : Antitone (magmaHigh X) := by
  intro m n hmn p hp
  exact fun w hw ↦ hmn.trans (hp hw)

theorem monoidHigh_mono : Antitone (monoidHigh X) := by
  intro m n hmn p hp
  exact fun w hw ↦ hmn.trans (hp hw)

theorem associativeHigh_mono : Antitone (associativeHigh X) := by
  intro m n hmn p hp
  exact monoidHigh_mono X hmn hp

theorem magmaHigh_mul {m n : ℕ} {a b : N}
    (ha : a ∈ magmaHigh X m) (hb : b ∈ magmaHigh X n) :
    a * b ∈ magmaHigh X (m + n) := by
  classical
  intro w hw
  rcases Finset.mem_mul.mp (MonoidAlgebra.support_mul a b hw) with
    ⟨wa, hwa, wb, hwb, rfl⟩
  simpa using Nat.add_le_add (ha hwa) (hb hwb)

theorem monoidHigh_mul {m n : ℕ}
    {a b : MonoidAlgebra ℤ (FreeMonoid X)}
    (ha : a ∈ monoidHigh X m) (hb : b ∈ monoidHigh X n) :
    a * b ∈ monoidHigh X (m + n) := by
  classical
  intro w hw
  rcases Finset.mem_mul.mp (MonoidAlgebra.support_mul a b hw) with
    ⟨wa, hwa, wb, hwb, rfl⟩
  simpa [FreeMonoid.length_mul] using Nat.add_le_add (ha hwa) (hb hwb)

theorem monoidExact_mul {m n : ℕ}
    {a b : MonoidAlgebra ℤ (FreeMonoid X)}
    (ha : a ∈ monoidExact X m) (hb : b ∈ monoidExact X n) :
    a * b ∈ monoidExact X (m + n) := by
  classical
  intro w hw
  rcases Finset.mem_mul.mp (MonoidAlgebra.support_mul a b hw) with
    ⟨wa, hwa, wb, hwb, rfl⟩
  simpa [FreeMonoid.length_mul] using
    congrArg₂ Nat.add (ha hwa) (hb hwb)

theorem associativeHigh_mul {m n : ℕ} {a b : A}
    (ha : a ∈ associativeHigh X m) (hb : b ∈ associativeHigh X n) :
    a * b ∈ associativeHigh X (m + n) := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid (a * b) ∈ monoidHigh X (m + n)
  rw [map_mul]
  exact monoidHigh_mul X ha hb

/-- The minimum-word-length filtration, regarded as a (two-sided) ideal of the free algebra. -/
def associativeHighIdeal (n : ℕ) : Ideal A where
  carrier := associativeHigh X n
  zero_mem' := (associativeHigh X n).zero_mem
  add_mem' := (associativeHigh X n).add_mem
  smul_mem' a b hb := by
    change a * b ∈ associativeHigh X n
    have ha : a ∈ associativeHigh X 0 := fun _ _ ↦ Nat.zero_le _
    simpa using associativeHigh_mul X ha hb

instance associativeHighIdeal_isTwoSided (n : ℕ) :
    (associativeHighIdeal X n).IsTwoSided where
  mul_mem_of_left b ha := by
    change _ * b ∈ associativeHigh X n
    have hb : b ∈ associativeHigh X 0 := fun _ _ ↦ Nat.zero_le _
    simpa using associativeHigh_mul X ha hb

@[simp]
theorem mem_associativeHighIdeal {n : ℕ} {a : A} :
    a ∈ associativeHighIdeal X n ↔ a ∈ associativeHigh X n :=
  Iff.rfl

theorem associativeExact_mul {m n : ℕ} {a b : A}
    (ha : a ∈ associativeExact X m) (hb : b ∈ associativeExact X n) :
    a * b ∈ associativeExact X (m + n) := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid (a * b) ∈ monoidExact X (m + n)
  rw [map_mul]
  exact monoidExact_mul X ha hb

theorem associativeExact_lie {m n : ℕ} {a b : A}
    (ha : a ∈ associativeExact X m) (hb : b ∈ associativeExact X n) :
    ⁅a, b⁆ ∈ associativeExact X (m + n) := by
  rw [LieRing.of_associative_ring_bracket]
  exact (associativeExact X (m + n)).sub_mem
    (associativeExact_mul X ha hb)
    (by simpa [Nat.add_comm] using associativeExact_mul X hb ha)

@[simp]
theorem associativeHigh_zero : associativeHigh X 0 = ⊤ := by
  apply top_unique
  intro p hp
  exact fun w hw ↦ Nat.zero_le _

theorem freeAlgebra_i_mem_associativeHigh_one (x : X) :
    FreeAlgebra.ι ℤ x ∈ associativeHigh X 1 := by
  rw [mem_associativeHigh, monoidHigh]
  simpa [FreeAlgebra.equivMonoidAlgebraFreeMonoid] using
    Finsupp.single_mem_supported (a := FreeMonoid.of x) ℤ (1 : ℤ)
    (show 1 ≤ (FreeMonoid.of x).length by simp)

theorem freeAlgebra_i_mem_associativeExact_one (x : X) :
    FreeAlgebra.ι ℤ x ∈ associativeExact X 1 := by
  rw [mem_associativeExact, monoidExact]
  simpa [FreeAlgebra.equivMonoidAlgebraFreeMonoid] using
    Finsupp.single_mem_supported (a := FreeMonoid.of x) ℤ (1 : ℤ)
      (show (FreeMonoid.of x).length = 1 by simp)

theorem magmaToFreeAlgebra_single_mem_exact (w : FreeMagma X) :
    magmaToFreeAlgebra X (Finsupp.single w 1) ∈
      associativeExact X w.length := by
  induction w using FreeMagma.recOnMul with
  | ih1 x =>
      rw [magmaToFreeAlgebra_single_of]
      exact freeAlgebra_i_mem_associativeExact_one X x
  | ih2 a b ha hb =>
      rw [magmaToFreeAlgebra_single_mul]
      exact associativeExact_lie X ha hb

theorem associativeExact_le_high {m n : ℕ} (hmn : n ≤ m) :
    associativeExact X m ≤ associativeHigh X n := by
  intro p hp w hw
  exact hmn.trans (hp hw).ge

theorem associativeExact_le_low {m n : ℕ} (hmn : m < n) :
    associativeExact X m ≤ associativeLow X n := by
  intro p hp w hw
  change w.length < n
  rw [hp hw]
  exact hmn

theorem magmaToFreeAlgebra_mem_high {n : ℕ} {p : N}
    (hp : p ∈ magmaHigh X n) :
    magmaToFreeAlgebra X p ∈ associativeHigh X n := by
  rw [magmaHigh, Finsupp.supported_eq_span_single] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨w, hw, rfl⟩ := hp
      exact associativeExact_le_high X hw
        (magmaToFreeAlgebra_single_mem_exact X w)
  | zero => simp
  | add a b _ _ ha hb =>
      rw [map_add]
      exact (associativeHigh X n).add_mem ha hb
  | smul c a _ ha =>
      rw [map_smul]
      exact (associativeHigh X n).smul_mem c ha

theorem magmaToFreeAlgebra_mem_low {n : ℕ} {p : N}
    (hp : p ∈ magmaLow X n) :
    magmaToFreeAlgebra X p ∈ associativeLow X n := by
  rw [magmaLow, Finsupp.supported_eq_span_single] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨w, hw, rfl⟩ := hp
      exact associativeExact_le_low X hw
        (magmaToFreeAlgebra_single_mem_exact X w)
  | zero => simp
  | add a b _ _ ha hb =>
      rw [map_add]
      exact (associativeLow X n).add_mem ha hb
  | smul c a _ ha =>
      rw [map_smul]
      exact (associativeLow X n).smul_mem c ha

theorem eq_zero_of_mem_associativeHigh_of_mem_associativeLow
    {n : ℕ} {p : A} (phigh : p ∈ associativeHigh X n)
    (plow : p ∈ associativeLow X n) : p = 0 := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  apply Finsupp.ext
  intro w
  by_contra hw
  have hw' : (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) w ≠ 0 := by
    simpa using hw
  have hws : w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).support :=
    Finsupp.mem_support_iff.mpr hw'
  exact (Nat.not_lt_of_ge (phigh hws)) (plow hws)

/-- The part of a non-associative polynomial supported in lengths below `n`. -/
def magmaLowPart (n : ℕ) (p : N) : N :=
  Finsupp.filter (fun w ↦ w.length < n) p

/-- The complementary part, supported in lengths at least `n`. -/
def magmaHighPart (n : ℕ) (p : N) : N :=
  p - magmaLowPart X n p

theorem magmaLowPart_mem (n : ℕ) (p : N) :
    magmaLowPart X n p ∈ magmaLow X n := by
  intro w hw
  have hne := Finsupp.mem_support_iff.mp hw
  by_contra hn
  apply hne
  exact Finsupp.filter_apply_neg (fun w ↦ w.length < n) p hn

theorem magmaHighPart_mem (n : ℕ) (p : N) :
    magmaHighPart X n p ∈ magmaHigh X n := by
  intro w hw
  by_contra hn
  have hlow : w.length < n := Nat.lt_of_not_ge hn
  have hne := Finsupp.mem_support_iff.mp hw
  apply hne
  change p w - Finsupp.filter (fun w ↦ w.length < n) p w = 0
  rw [Finsupp.filter_apply_pos (fun w ↦ w.length < n) p hlow, sub_self]

theorem magmaLowPart_add_magmaHighPart (n : ℕ) (p : N) :
    magmaLowPart X n p + magmaHighPart X n p = p := by
  simp [magmaHighPart]

@[simp]
theorem freeLieToFreeAlgebra_mk (p : N) :
    PBW.freeLieToFreeAlgebra ℤ X (freeLieMkLinear X p) =
      magmaToFreeAlgebra X p := by
  unfold PBW.freeLieToFreeAlgebra freeLieMkLinear magmaToFreeAlgebra
  unfold magmaToFreeAlgebraNonUnital FreeLieAlgebra.lift FreeLieAlgebra.liftAux
    FreeLieAlgebra.mk
  rfl

/-- Integral PBW gives the Magnus--Witt embedding of the free Lie ring in the free associative
algebra. -/
theorem freeLieToFreeAlgebra_injective_int :
    Function.Injective (PBW.freeLieToFreeAlgebra ℤ X) :=
  (PBW.freeLie_canonicalMap_injective_iff_magnusWitt ℤ X).mp
    (PBW.canonicalMap_injective_int (FreeLieAlgebra ℤ X))

/-- Length separation: if the associativization of a representative has minimum degree `n`, its
class in the free Lie ring is represented entirely by bracketed words of length at least `n`. -/
theorem freeLieMkLinear_mem_lieHigh_of_magmaToFreeAlgebra_mem
    {n : ℕ} {p : N} (hp : magmaToFreeAlgebra X p ∈ associativeHigh X n) :
    freeLieMkLinear X p ∈ lieHigh X n := by
  let lo : N := magmaLowPart X n p
  let hi : N := magmaHighPart X n p
  have hlo : lo ∈ magmaLow X n := magmaLowPart_mem X n p
  have hhi : hi ∈ magmaHigh X n := magmaHighPart_mem X n p
  have heq : lo + hi = p := magmaLowPart_add_magmaHighPart X n p
  have hevalHi : magmaToFreeAlgebra X hi ∈ associativeHigh X n :=
    magmaToFreeAlgebra_mem_high X hhi
  have hevalLoLow : magmaToFreeAlgebra X lo ∈ associativeLow X n :=
    magmaToFreeAlgebra_mem_low X hlo
  have hevalLoHigh : magmaToFreeAlgebra X lo ∈ associativeHigh X n := by
    have hp' : magmaToFreeAlgebra X (lo + hi) ∈ associativeHigh X n := by
      rw [heq]
      exact hp
    rw [map_add] at hp'
    simpa using (associativeHigh X n).sub_mem hp' hevalHi
  have hevalLoZero : magmaToFreeAlgebra X lo = 0 :=
    eq_zero_of_mem_associativeHigh_of_mem_associativeLow X hevalLoHigh hevalLoLow
  have hlieLoZero : freeLieMkLinear X lo = 0 := by
    apply freeLieToFreeAlgebra_injective_int X
    rw [freeLieToFreeAlgebra_mk, map_zero, hevalLoZero]
  refine ⟨hi, hhi, ?_⟩
  have hmap := congrArg (freeLieMkLinear X) heq
  rw [map_add, hlieLoZero, zero_add] at hmap
  exact hmap

@[simp]
theorem lieHigh_one : lieHigh X 1 = ⊤ := by
  apply top_unique
  rintro ⟨p⟩ hp
  refine ⟨p, ?_, rfl⟩
  exact fun w hw ↦ FreeMagma.length_pos w

/-- The augmentation of the free associative algebra, sending every free generator to zero. -/
def freeAlgebraAugmentation : A →ₐ[ℤ] ℤ :=
  FreeAlgebra.lift ℤ (fun _ : X ↦ 0)

@[simp]
theorem freeAlgebraAugmentation_i (x : X) :
    freeAlgebraAugmentation X (FreeAlgebra.ι ℤ x) = 0 := by
  simp [freeAlgebraAugmentation]

/-- Removing the constant term of a free polynomial leaves an element of positive word length. -/
theorem sub_algebraMap_freeAlgebraAugmentation_mem_associativeHigh_one (a : A) :
    a - algebraMap ℤ A (freeAlgebraAugmentation X a) ∈ associativeHigh X 1 := by
  induction a using FreeAlgebra.induction with
  | grade0 r => simp [freeAlgebraAugmentation]
  | grade1 x => simpa [freeAlgebraAugmentation] using
      freeAlgebra_i_mem_associativeHigh_one X x
  | add a b ha hb =>
      rw [map_add, map_add]
      convert (associativeHigh X 1).add_mem ha hb using 1
      abel
  | mul a b ha hb =>
      let a₀ : A := algebraMap ℤ A (freeAlgebraAugmentation X a)
      let b₀ : A := algebraMap ℤ A (freeAlgebraAugmentation X b)
      have hbAll : b ∈ associativeHigh X 0 := fun _ _ ↦ Nat.zero_le _
      have ha₀All : a₀ ∈ associativeHigh X 0 := fun _ _ ↦ Nat.zero_le _
      have h₁ : (a - a₀) * b ∈ associativeHigh X 1 :=
        associativeHigh_mul X (m := 1) (n := 0) ha hbAll
      have h₂ : a₀ * (b - b₀) ∈ associativeHigh X 1 :=
        associativeHigh_mul X (m := 0) (n := 1) ha₀All hb
      have h := (associativeHigh X 1).add_mem h₁ h₂
      rw [map_mul, map_mul]
      change a * b - a₀ * b₀ ∈ associativeHigh X 1
      have hid : a * b - a₀ * b₀ = (a - a₀) * b + a₀ * (b - b₀) := by
        noncomm_ring
      rw [hid]
      exact h

/-- Under `U(FreeLie(X)) ≃ FreeAlgebra(X)`, the two natural augmentations agree. -/
theorem freeAlgebraAugmentation_comp_universalEnvelopingEquiv :
    (freeAlgebraAugmentation X).comp
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X).toAlgHom =
      UEA.augmentation ℤ F := by
  apply UniversalEnvelopingAlgebra.hom_ext ℤ
  apply FreeLieAlgebra.hom_ext
  intro x
  change ((freeAlgebraAugmentation X).comp
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X).toAlgHom)
        (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x)) =
      UEA.augmentation ℤ F
        (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x))
  rw [UEA.augmentation_ι, AlgHom.comp_apply]
  have he : (↑(FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X) :
      UEA ℤ F → A) (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x)) =
      FreeAlgebra.ι ℤ x := by
    calc
      _ = ((UniversalEnvelopingAlgebra.lift ℤ)
          ((FreeLieAlgebra.lift ℤ) (FreeAlgebra.ι ℤ)))
            (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x)) :=
        FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra_apply ℤ X _
      _ = (FreeLieAlgebra.lift ℤ (FreeAlgebra.ι ℤ))
            (FreeLieAlgebra.of ℤ x) :=
        UniversalEnvelopingAlgebra.lift_ι_apply ℤ
          (FreeLieAlgebra.lift ℤ (FreeAlgebra.ι ℤ)) (FreeLieAlgebra.of ℤ x)
      _ = FreeAlgebra.ι ℤ x := FreeLieAlgebra.lift_of_apply _ _
  calc
    _ = freeAlgebraAugmentation X (FreeAlgebra.ι ℤ x) := congrArg _ he
    _ = 0 := freeAlgebraAugmentation_i X x

/-- The enveloping-algebra equivalence sends the augmentation ideal into positive word length. -/
theorem universalEnvelopingEquiv_mem_associativeHigh_one
    {u : UEA ℤ F} (hu : u ∈ UEA.augmentationIdeal ℤ F) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X u ∈
      associativeHigh X 1 := by
  have hzero : freeAlgebraAugmentation X
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X u) = 0 := by
    calc
      _ = UEA.augmentation ℤ F u := DFunLike.congr_fun
        (freeAlgebraAugmentation_comp_universalEnvelopingEquiv X) u
      _ = 0 := (UEA.mem_augmentationIdeal ℤ F).mp hu
  simpa only [hzero, map_zero, sub_zero] using
    sub_algebraMap_freeAlgebraAugmentation_mem_associativeHigh_one X
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X u)

/-- Every element of the `n`th augmentation power has minimum associative word length `n`. -/
theorem universalEnvelopingEquiv_mem_associativeHigh
    (n : ℕ) {u : UEA ℤ F} (hu : u ∈ UEA.augmentationIdeal ℤ F ^ n) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X u ∈
      associativeHigh X n := by
  induction n generalizing u with
  | zero => rw [associativeHigh_zero]; trivial
  | succ n ih =>
      have hpow : UEA.augmentationIdeal ℤ F ^ (n + 1) =
          UEA.augmentationIdeal ℤ F ^ n * UEA.augmentationIdeal ℤ F := by
        rw [Ideal.IsTwoSided.pow_add, Submodule.pow_one]
      rw [hpow] at hu
      have hle : UEA.augmentationIdeal ℤ F ^ n * UEA.augmentationIdeal ℤ F ≤
          Ideal.comap
            (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X).toRingEquiv.toRingHom
            (associativeHighIdeal X (n + 1)) := by
        rw [Ideal.mul_le]
        intro a ha b hb
        change FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X (a * b) ∈
          associativeHigh X (n + 1)
        have hm := associativeHigh_mul X (ih ha)
          (universalEnvelopingEquiv_mem_associativeHigh_one X hb)
        exact (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X).map_mul a b |>.symm ▸ hm
      exact hle hu

/-- The enveloping-algebra equivalence takes the canonical Lie map to evaluation in the free
associative algebra. -/
theorem universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra (x : F) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
        (UniversalEnvelopingAlgebra.ι ℤ x) =
      PBW.freeLieToFreeAlgebra ℤ X x := by
  calc
    _ = ((UniversalEnvelopingAlgebra.lift ℤ)
        ((FreeLieAlgebra.lift ℤ) (FreeAlgebra.ι ℤ)))
          (UniversalEnvelopingAlgebra.ι ℤ x) :=
      FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra_apply ℤ X _
    _ = (FreeLieAlgebra.lift ℤ (FreeAlgebra.ι ℤ)) x :=
      UniversalEnvelopingAlgebra.lift_ι_apply ℤ
        (FreeLieAlgebra.lift ℤ (FreeAlgebra.ι ℤ)) x
    _ = PBW.freeLieToFreeAlgebra ℤ X x := rfl

@[simp]
theorem freeLieMkLinear_mul (a b : N) :
    freeLieMkLinear X (a * b) =
      ⁅freeLieMkLinear X a, freeLieMkLinear X b⁆ :=
  rfl

/-- The bracket of the `m`th and `n`th lower-central terms has the expected weight.

Here Mathlib's term `n` is the conventional `γₙ₊₁`.  This useful general lemma is obtained
from dimension centrality, whose proof is independent of PBW. -/
theorem lowerCentralSeries_lie_lowerCentralSeries_le (m n : ℕ) :
    ⁅lowerCentralSeries ℤ F m, lowerCentralSeries ℤ F n⁆ ≤
      lowerCentralSeries ℤ F (m + n + 1) := by
  calc
    ⁅lowerCentralSeries ℤ F m, lowerCentralSeries ℤ F n⁆ ≤
        ⁅dimensionSubring ℤ F (m + 1), dimensionSubring ℤ F (n + 1)⁆ :=
      LieSubmodule.mono_lie
        (lowerCentralSeries_le_dimensionSubring ℤ F m)
        (lowerCentralSeries_le_dimensionSubring ℤ F n)
    _ ≤ lowerCentralSeries ℤ F (m + n + 1) :=
      bracket_dimensionSubring_le_lowerCentralSeries ℤ F m n

/-- A bracketed word of length `r` belongs to `γᵣ`, i.e. to Mathlib's lower-central term
`r - 1`. -/
theorem freeLieMkLinear_single_mem_lowerCentralSeries (w : FreeMagma X) :
    freeLieMkLinear X (Finsupp.single w 1) ∈
      lowerCentralSeries ℤ F (w.length - 1) := by
  induction w using FreeMagma.recOnMul with
  | ih1 x =>
      simp
  | ih2 a b ha hb =>
      have hbracket :
          ⁅freeLieMkLinear X (Finsupp.single a 1),
              freeLieMkLinear X (Finsupp.single b 1)⁆ ∈
            ⁅lowerCentralSeries ℤ F (a.length - 1),
              lowerCentralSeries ℤ F (b.length - 1)⁆ :=
        LieSubmodule.lie_coe_mem_lie
          ⟨freeLieMkLinear X (Finsupp.single a 1), ha⟩
          ⟨freeLieMkLinear X (Finsupp.single b 1), hb⟩
      have htarget :=
        lowerCentralSeries_lie_lowerCentralSeries_le X (a.length - 1) (b.length - 1)
          hbracket
      let sa : N := Finsupp.single a 1
      let sb : N := Finsupp.single b 1
      have hsingle : (Finsupp.single (a * b) (1 : ℤ) : N) = sa * sb := by
        simpa only [sa, sb, one_mul] using
          (MonoidAlgebra.single_mul_single a b (1 : ℤ) (1 : ℤ)).symm
      rw [hsingle, freeLieMkLinear_mul]
      have ha_pos := FreeMagma.length_pos a
      have hb_pos := FreeMagma.length_pos b
      change
        ⁅freeLieMkLinear X (Finsupp.single a 1),
            freeLieMkLinear X (Finsupp.single b 1)⁆ ∈
          lowerCentralSeries ℤ F ((a * b).length - 1)
      have hindex : (a * b).length - 1 =
          (a.length - 1) + (b.length - 1) + 1 := by
        change a.length + b.length - 1 =
          (a.length - 1) + (b.length - 1) + 1
        omega
      rw [hindex]
      exact htarget

/-- The minimum bracket-length filtration is contained in the lower central series. -/
theorem lieHigh_le_lowerCentralSeries (n : ℕ) :
    lieHigh X (n + 1) ≤ lowerCentralSeries ℤ F n := by
  rintro y ⟨p, hp, rfl⟩
  rw [magmaHigh, Finsupp.supported_eq_span_single] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨w, hw, rfl⟩ := hp
      have hw' : n + 1 ≤ w.length := hw
      have hn : n ≤ w.length - 1 := by omega
      apply LieModule.antitone_lowerCentralSeries ℤ F F hn
      exact freeLieMkLinear_single_mem_lowerCentralSeries X w
  | zero => simp
  | add a b _ _ ha hb =>
      rw [map_add]
      exact (lowerCentralSeries ℤ F n).add_mem ha hb
  | smul c a _ ha =>
      rw [map_smul]
      exact (lowerCentralSeries ℤ F n).smul_mem c ha

/-- Bracketing elements of filtration degrees `m` and `n` adds the degrees. -/
theorem lieHigh_lie_mem {m n : ℕ} {x y : F}
    (hx : x ∈ lieHigh X m) (hy : y ∈ lieHigh X n) :
    ⁅x, y⁆ ∈ lieHigh X (m + n) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨a * b, magmaHigh_mul X ha hb, ?_⟩
  exact (freeLieMkLinear_mul X a b).symm

/-- The lower central series is contained in the minimum bracket-length filtration. -/
theorem lowerCentralSeries_le_lieHigh (n : ℕ) :
    lowerCentralSeries ℤ F n ≤ lieHigh X (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      change LieModule.lowerCentralSeries ℤ F F (n + 1) ≤ lieHigh X (n + 2)
      rw [LieModule.lowerCentralSeries_succ]
      intro z hz
      let N' : LieSubmodule ℤ F F := lowerCentralSeries ℤ F n
      have hz' : z ∈ ⁅(⊤ : LieIdeal ℤ F), N'⁆ := hz
      have hzspan : z ∈ Submodule.span ℤ
          {w : F | ∃ x, x ∈ (⊤ : LieIdeal ℤ F) ∧ ∃ y, y ∈ N' ∧ ⁅x, y⁆ = w} := by
        have heq : (↑⁅(⊤ : LieIdeal ℤ F), N'⁆ : Submodule ℤ F) =
            Submodule.span ℤ
              {w : F | ∃ x, x ∈ (⊤ : LieIdeal ℤ F) ∧ ∃ y, y ∈ N' ∧ ⁅x, y⁆ = w} :=
          LieSubmodule.lieIdeal_oper_eq_linear_span' N' (⊤ : LieIdeal ℤ F)
        rw [← heq]
        exact hz'
      refine Submodule.span_induction (p := fun z _ ↦ z ∈ lieHigh X (n + 2))
        ?_ (lieHigh X (n + 2)).zero_mem
        (fun _ _ _ _ ha hb ↦ (lieHigh X (n + 2)).add_mem ha hb)
        (fun c _ _ ha ↦ (lieHigh X (n + 2)).smul_mem c ha) hzspan
      rintro z ⟨x, _, y, hy, rfl⟩
      have hx : x ∈ lieHigh X 1 := by rw [lieHigh_one]; trivial
      simpa [N', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        lieHigh_lie_mem X hx (ih hy)

/-- The bracket-length filtration on a free Lie ring is its lower central series. -/
theorem lieHigh_eq_lowerCentralSeries (n : ℕ) :
    lieHigh X (n + 1) = lowerCentralSeries ℤ F n :=
  le_antisymm (lieHigh_le_lowerCentralSeries X n)
    (lowerCentralSeries_le_lieHigh X n)

/-- **Dimension subgroup theorem for free Lie rings.**  In Mathlib's zero-based indexing,
`dimensionSubring (n + 1) = lowerCentralSeries n`; in conventional notation this is
`δₙ₊₁(F) = γₙ₊₁(F)` for every free Lie ring `F` over `ℤ`. -/
theorem dimensionSubring_succ_eq_lowerCentralSeries (n : ℕ) :
    dimensionSubring ℤ F (n + 1) = lowerCentralSeries ℤ F n := by
  apply le_antisymm
  · rintro ⟨p⟩ hp
    have hpU : UniversalEnvelopingAlgebra.ι ℤ (freeLieMkLinear X p) ∈
        UEA.augmentationIdeal ℤ F ^ (n + 1) :=
      (mem_dimensionSubring ℤ F).mp hp
    have hpHigh := universalEnvelopingEquiv_mem_associativeHigh X (n + 1) hpU
    have heval : magmaToFreeAlgebra X p ∈ associativeHigh X (n + 1) := by
      rw [← freeLieToFreeAlgebra_mk]
      rw [← universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra]
      exact hpHigh
    have hlie := freeLieMkLinear_mem_lieHigh_of_magmaToFreeAlgebra_mem X heval
    rw [lieHigh_eq_lowerCentralSeries] at hlie
    exact hlie
  · exact lowerCentralSeries_le_dimensionSubring ℤ F n

/-- Conventional one-based formulation: `δₙ(F) = γₙ(F)` for all `n`.  The expression
`lowerCentralSeries (n - 1)` denotes `γₙ`, including the harmless convention `δ₀ = γ₁ = F`. -/
theorem dimensionSubring_eq_lowerCentralSeries_pred (n : ℕ) :
    dimensionSubring ℤ F n = lowerCentralSeries ℤ F (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa using dimensionSubring_succ_eq_lowerCentralSeries X n

end

end FreeLieDimension

end LieRings
