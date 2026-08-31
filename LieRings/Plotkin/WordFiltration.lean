import LieRings.Plotkin.FilteredNoetherian
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.FiniteType

/-!
# Finite almost-commutative word filtrations

This file packages the elementary filtered-ring argument used for the Rees ring in the
Plotkin proof.  A ring generated additively by bounded words in a finite family carries its
word-length filtration.  If commutators of generators have word length at most one, its
associated graded ring is a finitely generated commutative `Z`-algebra, and the original ring
is Noetherian.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

namespace WordFiltration

variable {A : Type u} [Ring A]
variable {ι : Type v}

/-- The product represented by a word in a chosen family of ring elements. -/
def word (g : ι → A) (xs : List ι) : A :=
  (xs.map g).prod

@[simp] theorem word_nil (g : ι → A) : word g [] = 1 := rfl

@[simp] theorem word_cons (g : ι → A) (i : ι) (xs : List ι) :
    word g (i :: xs) = g i * word g xs := by
  simp [word]

@[simp] theorem word_append (g : ι → A) (xs ys : List ι) :
    word g (xs ++ ys) = word g xs * word g ys := by
  simp [word]

/-- The `n`th word-length term: the integral span of products of at most `n` generators. -/
def term (g : ι → A) (n : ℕ) : Submodule ℤ A :=
  Submodule.span ℤ {a | ∃ xs : List ι, xs.length ≤ n ∧ word g xs = a}

theorem word_mem_term (g : ι → A) (xs : List ι) {n : ℕ} (hxs : xs.length ≤ n) :
    word g xs ∈ term g n :=
  Submodule.subset_span ⟨xs, hxs, rfl⟩

theorem term_mono (g : ι → A) {m n : ℕ} (hmn : m ≤ n) : term g m ≤ term g n := by
  apply Submodule.span_mono
  rintro a ⟨xs, hxs, rfl⟩
  exact ⟨xs, hxs.trans hmn, rfl⟩

theorem one_mem_term_zero (g : ι → A) : (1 : A) ∈ term g 0 := by
  simpa using word_mem_term g ([] : List ι) (le_refl 0)

private theorem mul_zsmul_ring (a x : A) (z : ℤ) :
    a * (z • x) = z • (a * x) := by
  simp only [zsmul_eq_mul]
  calc
    a * ((z : A) * x) = (a * (z : A)) * x := (mul_assoc _ _ _).symm
    _ = ((z : A) * a) * x := congrArg (fun q : A ↦ q * x) (Int.cast_comm z a).symm
    _ = (z : A) * (a * x) := mul_assoc _ _ _

private theorem zsmul_mul_ring (x a : A) (z : ℤ) :
    (z • x) * a = z • (x * a) := by
  simp only [zsmul_eq_mul, mul_assoc]

private theorem zsmul_sub_ring (a b : A) (z : ℤ) :
    z • (a - b) = z • a - z • b := by
  simp only [zsmul_eq_mul]
  noncomm_ring

theorem mul_mem_term (g : ι → A) {m n : ℕ} {a b : A}
    (ha : a ∈ term g m) (hb : b ∈ term g n) : a * b ∈ term g (m + n) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨xs, hxs, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨ys, hys, rfl⟩ := hb
          rw [← word_append]
          exact word_mem_term g (xs ++ ys) (by simp; omega)
      | zero => simp
      | add x y _ _ hx hy => simpa [mul_add] using (term g (m + n)).add_mem hx hy
      | smul z x _ hx =>
          have hz := (term g (m + n)).smul_mem z hx
          simpa only [mul_zsmul_ring] using hz
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using (term g (m + n)).add_mem hx hy
  | smul z x _ hx =>
      have hz := (term g (m + n)).smul_mem z hx
      simpa only [zsmul_mul_ring] using hz

/-- The word-length filtration, provided the chosen words exhaust the ring. -/
def filtration (g : ι → A) (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n) :
    NatRingFiltration A where
  term := term g
  monotone' := fun _ _ ↦ term_mono g
  one_mem := one_mem_term_zero g
  mul_mem' := mul_mem_term g
  exhaustive := hexhaustive

private theorem commutator_mul_right (a b c : A) :
    a * (b * c) - (b * c) * a =
      (a * b - b * a) * c + b * (a * c - c * a) := by
  noncomm_ring

private theorem commutator_mul_left (a b c : A) :
    (a * b) * c - c * (a * b) =
      a * (b * c - c * b) + (a * c - c * a) * b := by
  noncomm_ring

/-- A generator commuted past a word of length `n` produces terms of word length at most `n`,
provided pairwise generator commutators have word length at most one. -/
theorem generator_commutator_word_mem (g : ι → A)
    (hcomm : ∀ i j, g i * g j - g j * g i ∈ term g 1)
    (i : ι) (ys : List ι) :
    g i * word g ys - word g ys * g i ∈ term g ys.length := by
  induction ys with
  | nil => simp
  | cons j ys ih =>
      rw [word_cons, commutator_mul_right]
      apply (term g (j :: ys).length).add_mem
      · simpa [Nat.add_comm] using
          mul_mem_term g (m := 1) (n := ys.length) (hcomm i j)
          (word_mem_term g ys (le_refl ys.length))
      · simpa [Nat.add_comm] using mul_mem_term g (m := 1) (n := ys.length)
          (word_mem_term g [j] (le_refl 1)) ih

/-- Commuting two words lowers their total word length by one. -/
theorem word_commutator_word_mem (g : ι → A)
    (hcomm : ∀ i j, g i * g j - g j * g i ∈ term g 1)
    (xs ys : List ι) :
    word g xs * word g ys - word g ys * word g xs ∈
      term g (xs.length + ys.length - 1) := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      by_cases hzero : xs.length + ys.length = 0
      · have hxs : xs = [] :=
          List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_right hzero)
        have hys : ys = [] :=
          List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_left hzero)
        subst xs
        subst ys
        simp
      rw [word_cons, commutator_mul_left]
      apply (term g ((i :: xs).length + ys.length - 1)).add_mem
      · have hmul := mul_mem_term g (m := 1)
          (n := xs.length + ys.length - 1)
          (word_mem_term g [i] (le_refl 1)) ih
        have hmul' : g i * (word g xs * word g ys - word g ys * word g xs) ∈
            term g (1 + (xs.length + ys.length - 1)) := by simpa using hmul
        exact term_mono g (m := 1 + (xs.length + ys.length - 1))
          (n := (i :: xs).length + ys.length - 1) (by simp; omega) hmul'
      · have hmul := mul_mem_term g (m := ys.length) (n := xs.length)
          (generator_commutator_word_mem g hcomm i ys)
          (word_mem_term g xs (le_refl xs.length))
        exact term_mono g (by simp; omega) hmul

private theorem commutator_mem_term_pred (g : ι → A)
    (hcomm : ∀ i j, g i * g j - g j * g i ∈ term g 1)
    {m n : ℕ} {a b : A} (ha : a ∈ term g m) (hb : b ∈ term g n) :
    a * b - b * a ∈ term g (m + n - 1) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨xs, hxs, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨ys, hys, rfl⟩ := hb
          exact term_mono g (by omega) (word_commutator_word_mem g hcomm xs ys)
      | zero => simp
      | add x y _ _ hx hy =>
          have hadd := (term g (m + n - 1)).add_mem hx hy
          convert hadd using 1 <;> noncomm_ring
      | smul z x _ hx =>
          have hz := (term g (m + n - 1)).smul_mem z hx
          simpa only [mul_zsmul_ring, zsmul_mul_ring, zsmul_sub_ring] using hz
  | zero => simp
  | add x y _ _ hx hy =>
      have hadd := (term g (m + n - 1)).add_mem hx hy
      convert hadd using 1 <;> noncomm_ring
  | smul z x _ hx =>
      have hz := (term g (m + n - 1)).smul_mem z hx
      simpa only [zsmul_mul_ring, mul_zsmul_ring, zsmul_sub_ring] using hz

private theorem commutator_eq_zero_of_mem_term_zero (g : ι → A)
    {a : A} (ha : a ∈ term g 0) (b : A) : a * b - b * a = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨xs, hxs, rfl⟩ := ha
      have : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hxs)
      subst xs
      simp
  | zero => simp
  | add x y _ _ hx hy =>
      calc
        (x + y) * b - b * (x + y) =
            (x * b - b * x) + (y * b - b * y) := by noncomm_ring
        _ = 0 := by rw [hx, hy, add_zero]
  | smul z x _ hx =>
      rw [zsmul_mul_ring, mul_zsmul_ring, ← zsmul_sub_ring, hx]
      simp

/-- The word filtration is almost commutative. -/
theorem filtration_isAlmostCommutative (g : ι → A)
    (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n)
    (hcomm : ∀ i j, g i * g j - g j * g i ∈ term g 1) :
    (filtration g hexhaustive).IsAlmostCommutative := by
  intro m n x y
  cases hmn : m + n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_add_eq_zero_right hmn
      have hn : n = 0 := Nat.eq_zero_of_add_eq_zero_left hmn
      subst m
      subst n
      change (x : A) * (y : A) - (y : A) * (x : A) ∈ (⊥ : Submodule ℤ A)
      rw [commutator_eq_zero_of_mem_term_zero g x.property (y : A)]
      simp
  | succ k =>
      change (x : A) * (y : A) - (y : A) * (x : A) ∈ term g k
      have hxy := commutator_mem_term_pred g hcomm x.property y.property
      simpa [hmn] using hxy

section FiniteGeneration

variable [Finite ι]

/-- The homogeneous class of a filtered element in the full associated graded ring. -/
def homogeneous (g : ι → A) (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n)
    (n : ℕ) :
    (filtration g hexhaustive) n →ₗ[ℤ]
      (filtration g hexhaustive).AssociatedGraded :=
  (DirectSum.lof ℤ ℕ (filtration g hexhaustive).GradedPiece n).comp
    ((filtration g hexhaustive).toGradedPiece n)

/-- The degree-one symbol of a chosen generator. -/
def symbol (g : ι → A) (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n)
    (i : ι) : (filtration g hexhaustive).AssociatedGraded :=
  homogeneous g hexhaustive 1
    ⟨g i, by simpa using word_mem_term g [i] (le_refl 1)⟩

theorem product_symbol_eq_homogeneous_word
    (g : ι → A) (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n)
    (xs : List ι) :
    (xs.map (symbol g hexhaustive)).prod =
      homogeneous g hexhaustive xs.length
        ⟨word g xs, word_mem_term g xs (le_refl xs.length)⟩ := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      rw [List.map_cons, List.prod_cons, ih]
      change
        DirectSum.of (filtration g hexhaustive).GradedPiece 1
            ((filtration g hexhaustive).toGradedPiece 1
              ⟨g i, by simpa using word_mem_term g [i] (le_refl 1)⟩) *
          DirectSum.of (filtration g hexhaustive).GradedPiece xs.length
            ((filtration g hexhaustive).toGradedPiece xs.length
              ⟨word g xs, word_mem_term g xs (le_refl xs.length)⟩) =
        DirectSum.of (filtration g hexhaustive).GradedPiece (i :: xs).length
          ((filtration g hexhaustive).toGradedPiece (i :: xs).length
            ⟨word g (i :: xs),
              word_mem_term g (i :: xs) (le_refl (i :: xs).length)⟩)
      rw [DirectSum.of_mul_of,
        show GradedMonoid.GMul.mul
            ((filtration g hexhaustive).toGradedPiece 1
              ⟨g i, by simpa using word_mem_term g [i] (le_refl 1)⟩)
            ((filtration g hexhaustive).toGradedPiece xs.length
              ⟨word g xs, word_mem_term g xs (le_refl xs.length)⟩) =
          (filtration g hexhaustive).gradedMul
            ((filtration g hexhaustive).toGradedPiece 1
              ⟨g i, by simpa using word_mem_term g [i] (le_refl 1)⟩)
            ((filtration g hexhaustive).toGradedPiece xs.length
              ⟨word g xs, word_mem_term g xs (le_refl xs.length)⟩) from rfl,
        NatRingFiltration.gradedMul_toGradedPiece]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      exact (filtration g hexhaustive).gradedMk_toGradedPiece_eq
        (Nat.add_comm 1 xs.length) _ _ (by simp [word_cons])

theorem homogeneous_word_eq_zero_of_length_lt
    (g : ι → A) (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n)
    (xs : List ι) (n : ℕ) (hxs : xs.length < n) :
    homogeneous g hexhaustive n
        ⟨word g xs, word_mem_term g xs hxs.le⟩ = 0 := by
  change DirectSum.of (filtration g hexhaustive).GradedPiece n
      ((filtration g hexhaustive).toGradedPiece n
        ⟨word g xs, word_mem_term g xs hxs.le⟩) = 0
  have hgrade :
      (filtration g hexhaustive).toGradedPiece n
          ⟨word g xs, word_mem_term g xs hxs.le⟩ = 0 := by
    apply (Submodule.Quotient.mk_eq_zero
      ((filtration g hexhaustive).previousIn n)).2
    change word g xs ∈ (filtration g hexhaustive).previous n
    cases n with
    | zero => omega
    | succ n =>
        change word g xs ∈ term g n
        exact word_mem_term g xs (by omega)
  rw [hgrade, map_zero]

private theorem product_symbol_mem_adjoin
    (g : ι → A) (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n)
    (xs : List ι) :
    (xs.map (symbol g hexhaustive)).prod ∈
      Algebra.adjoin ℤ (Set.range (symbol g hexhaustive)) := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      rw [List.map_cons, List.prod_cons]
      exact (Algebra.adjoin ℤ (Set.range (symbol g hexhaustive))).mul_mem
        (Algebra.subset_adjoin ⟨i, rfl⟩) ih

/-- Every homogeneous class belongs to the algebra generated by the degree-one symbols. -/
theorem homogeneous_mem_adjoin_symbols
    (g : ι → A) (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n)
    (n : ℕ) (x : (filtration g hexhaustive) n) :
    homogeneous g hexhaustive n x ∈
      Algebra.adjoin ℤ (Set.range (symbol g hexhaustive)) := by
  let S := Algebra.adjoin ℤ (Set.range (symbol g hexhaustive))
  let P : (a : A) → a ∈ term g n → Prop := fun a _ ↦
    ∀ ha : a ∈ term g n,
      homogeneous g hexhaustive n ⟨a, ha⟩ ∈ S
  have hp : P (x : A) x.property := by
    apply Submodule.span_induction (p := P)
    · intro a ha
      obtain ⟨xs, hlen, rfl⟩ := ha
      intro hword
      by_cases heq : xs.length = n
      · subst n
        rw [← product_symbol_eq_homogeneous_word g hexhaustive xs]
        exact product_symbol_mem_adjoin g hexhaustive xs
      · have hlt : xs.length < n := lt_of_le_of_ne hlen heq
        have hz := homogeneous_word_eq_zero_of_length_lt
          g hexhaustive xs n hlt
        have hproof :
            (⟨word g xs, hword⟩ : (filtration g hexhaustive) n) =
              ⟨word g xs, word_mem_term g xs hlt.le⟩ := rfl
        rw [hproof, hz]
        exact S.zero_mem
    · intro hzero
      have hz : (⟨(0 : A), hzero⟩ : (filtration g hexhaustive) n) = 0 := by
        rfl
      rw [hz, map_zero]
      exact S.zero_mem
    · intro a b ha hb hpa hpb
      intro hab
      have ha' : a ∈ term g n := ha
      have hb' : b ∈ term g n := hb
      have hadd :
          (⟨a + b, hab⟩ : (filtration g hexhaustive) n) =
            ⟨a, ha'⟩ + ⟨b, hb'⟩ := rfl
      rw [hadd, map_add]
      exact S.add_mem (hpa ha') (hpb hb')
    · intro z a ha hpa
      intro hza
      have ha' : a ∈ term g n := ha
      have hsmul :
          (⟨z • a, hza⟩ : (filtration g hexhaustive) n) =
            z • (⟨a, ha'⟩ : (filtration g hexhaustive) n) := rfl
      rw [hsmul, map_zsmul]
      exact S.smul_mem (hpa ha') z
    · exact x.property
  exact hp x.property

/-- The degree-one symbols generate the entire associated graded algebra. -/
theorem adjoin_symbols_eq_top
    (g : ι → A) (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n) :
    Algebra.adjoin ℤ (Set.range (symbol g hexhaustive)) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using DirectSum.induction_on with
  | zero => exact (Algebra.adjoin ℤ (Set.range (symbol g hexhaustive))).zero_mem
  | add x y hx hy =>
      exact (Algebra.adjoin ℤ (Set.range (symbol g hexhaustive))).add_mem hx hy
  | of n q =>
      induction q using Quotient.inductionOn' with
      | _ x =>
          change homogeneous g hexhaustive n x ∈
            Algebra.adjoin ℤ (Set.range (symbol g hexhaustive))
          exact homogeneous_mem_adjoin_symbols g hexhaustive n x

/-- A ring exhausted by words in finitely many generators is Noetherian as soon as the
commutator of every two generators has word length at most one. -/
theorem isNoetherianRing_of_finite_generators
    (g : ι → A) (hexhaustive : ∀ a : A, ∃ n, a ∈ term g n)
    (hcomm : ∀ i j, g i * g j - g j * g i ∈ term g 1) :
    IsNoetherianRing A := by
  let F := filtration g hexhaustive
  have hFcomm : F.IsAlmostCommutative :=
    filtration_isAlmostCommutative g hexhaustive hcomm
  letI : CommRing F.AssociatedGraded :=
    F.associatedGradedCommRing hFcomm
  letI : Algebra ℤ F.AssociatedGraded := Ring.toIntAlgebra F.AssociatedGraded
  have htop : Algebra.adjoin ℤ (Set.range (symbol g hexhaustive)) = ⊤ :=
    adjoin_symbols_eq_top g hexhaustive
  letI : Algebra.FiniteType ℤ F.AssociatedGraded := by
    refine ⟨?_⟩
    rw [Subalgebra.fg_def]
    exact ⟨Set.range (symbol g hexhaustive), Set.finite_range _, htop⟩
  letI : IsNoetherianRing F.AssociatedGraded :=
    Algebra.FiniteType.isNoetherianRing ℤ F.AssociatedGraded
  exact F.isNoetherianRing_of_associatedGraded

end FiniteGeneration

end WordFiltration

end

end LieRings.Plotkin
