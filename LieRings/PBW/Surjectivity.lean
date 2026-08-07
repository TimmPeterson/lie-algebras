import LieRings.PBW.FreeModuleStatement
import Mathlib.Tactic.NoncommRing

/-!
# Spanning half of PBW

This file proves the elementary half of the ordered-basis PBW theorem: every element of the
universal enveloping algebra is a linear combination of ordered monomials.  The proof is the
rearrangement argument of Cartan--Eilenberg, Chapter XIII, Lemma 3.4.
-/

namespace LieRings.PBW

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The product in `U(L)` represented by a list of elements of `L`. -/
def word (xs : List L) : UEA R L :=
  (xs.map (UniversalEnvelopingAlgebra.ι R)).prod

@[simp]
theorem word_nil : word R L [] = 1 := rfl

@[simp]
theorem word_cons (x : L) (xs : List L) :
    word R L (x :: xs) = UniversalEnvelopingAlgebra.ι R x * word R L xs := by
  simp [word]

@[simp]
theorem word_append (xs ys : List L) :
    word R L (xs ++ ys) = word R L xs * word R L ys := by
  simp [word]

/-- The standard length filtration on `U(L)`, presented as the span of words of length at most
`n`. -/
def wordFiltration (n : ℕ) : Submodule R (UEA R L) :=
  Submodule.span R {u | ∃ xs : List L, xs.length ≤ n ∧ word R L xs = u}

theorem word_mem_wordFiltration (xs : List L) {n : ℕ} (h : xs.length ≤ n) :
    word R L xs ∈ wordFiltration R L n :=
  Submodule.subset_span ⟨xs, h, rfl⟩

theorem wordFiltration_mono {m n : ℕ} (h : m ≤ n) :
    wordFiltration R L m ≤ wordFiltration R L n := by
  apply Submodule.span_mono
  rintro u ⟨xs, hxs, rfl⟩
  exact ⟨xs, hxs.trans h, rfl⟩

/-- Left multiplication by one canonical generator raises the word filtration by at most one. -/
theorem iota_mul_mem_wordFiltration (x : L) {u : UEA R L} {n : ℕ}
    (hu : u ∈ wordFiltration R L n) :
    UniversalEnvelopingAlgebra.ι R x * u ∈ wordFiltration R L (n + 1) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨xs, hxs, rfl⟩ := hu
      rw [← word_cons]
      exact word_mem_wordFiltration R L (x :: xs) (by simp; omega)
  | zero => simp
  | add a b _ _ ha hb => simpa [mul_add] using add_mem ha hb
  | smul r a _ ha =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r ha

private theorem iota_mul_word_sub_word_of_perm_mem (x : L) {xs ys : List L}
    (h : xs.Perm ys)
    (hu : word R L xs - word R L ys ∈ wordFiltration R L (xs.length - 1)) :
    UniversalEnvelopingAlgebra.ι R x * (word R L xs - word R L ys) ∈
      wordFiltration R L xs.length := by
  cases xs with
  | nil =>
      have : ys = [] := List.length_eq_zero_iff.mp (by simpa using h.length_eq.symm)
      subst ys
      simp
  | cons y xs =>
      have hmem := iota_mul_mem_wordFiltration R L x hu
      exact wordFiltration_mono R L (by simp) hmem

/-- Permuting a word changes it only by terms of strictly smaller length. -/
theorem word_sub_word_of_perm {xs ys : List L} (h : xs.Perm ys) :
    word R L xs - word R L ys ∈ wordFiltration R L (xs.length - 1) := by
  induction h with
  | nil => simp
  | cons x h ih =>
      rw [word_cons, word_cons, ← mul_sub]
      simpa using iota_mul_word_sub_word_of_perm_mem R L x h ih
  | swap x y xs =>
      rw [word_cons, word_cons, word_cons, word_cons]
      have hlie := LieHom.map_lie (UniversalEnvelopingAlgebra.ι R) y x
      simp only [LieRing.of_associative_ring_bracket] at hlie
      rw [show UniversalEnvelopingAlgebra.ι R y *
            (UniversalEnvelopingAlgebra.ι R x * word R L xs) -
            UniversalEnvelopingAlgebra.ι R x *
              (UniversalEnvelopingAlgebra.ι R y * word R L xs) =
            (UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x -
              UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y) *
                word R L xs by noncomm_ring]
      rw [← hlie, ← word_cons]
      apply word_mem_wordFiltration
      simp
  | trans h₁ h₂ ih₁ ih₂ =>
      have hadd := add_mem ih₁ (by simpa [h₁.length_eq] using ih₂)
      simpa only [sub_add_sub_cancel] using hadd

variable (ι : Type w)

/-- A word made from the chosen basis. -/
noncomputable def basisWord (b : Module.Basis ι R L) (is : List ι) : UEA R L :=
  word R L (is.map b)

@[simp]
theorem basisWord_nil (b : Module.Basis ι R L) : basisWord R L ι b [] = 1 := rfl

@[simp]
theorem basisWord_cons (b : Module.Basis ι R L) (i : ι) (is : List ι) :
    basisWord R L ι b (i :: is) =
      UniversalEnvelopingAlgebra.ι R (b i) * basisWord R L ι b is := by
  simp [basisWord]

/-- The span of basis words having exactly length `n`. -/
def basisWordSpan (b : Module.Basis ι R L) (n : ℕ) : Submodule R (UEA R L) :=
  Submodule.span R {u | ∃ is : List ι, is.length = n ∧ basisWord R L ι b is = u}

theorem basisWord_mem_basisWordSpan (b : Module.Basis ι R L) (is : List ι) :
    basisWord R L ι b is ∈ basisWordSpan R L ι b is.length :=
  Submodule.subset_span ⟨is, rfl, rfl⟩

theorem basis_iota_mul_mem_basisWordSpan (b : Module.Basis ι R L) (i : ι)
    {u : UEA R L} {n : ℕ} (hu : u ∈ basisWordSpan R L ι b n) :
    UniversalEnvelopingAlgebra.ι R (b i) * u ∈ basisWordSpan R L ι b (n + 1) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨is, his, rfl⟩ := hu
      rw [← basisWord_cons]
      exact Submodule.subset_span ⟨i :: is, by simp [his], rfl⟩
  | zero => simp
  | add a c _ _ ha hc => simpa [mul_add] using add_mem ha hc
  | smul r a _ ha =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r ha

/-- The product of an arbitrary canonical generator and an exact-length basis word is still in
the span of basis words of the next length. -/
theorem iota_mul_mem_basisWordSpan (b : Module.Basis ι R L) (x : L)
    {u : UEA R L} {n : ℕ} (hu : u ∈ basisWordSpan R L ι b n) :
    UniversalEnvelopingAlgebra.ι R x * u ∈ basisWordSpan R L ι b (n + 1) := by
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (basis_iota_mul_mem_basisWordSpan R L ι b i hu)

/-- Every word in arbitrary elements of `L` expands into basis words of the same length. -/
theorem word_mem_basisWordSpan (b : Module.Basis ι R L) (xs : List L) :
    word R L xs ∈ basisWordSpan R L ι b xs.length := by
  induction xs with
  | nil => exact basisWord_mem_basisWordSpan R L ι b []
  | cons x xs ih =>
      rw [word_cons]
      simpa using iota_mul_mem_basisWordSpan R L ι b x ih

/-- For a sorted list, the PBW exponent-vector monomial is exactly the corresponding basis word. -/
theorem orderedMonomial_multiset_toFinsupp [LinearOrder ι]
    (b : Module.Basis ι R L) (is : List ι)
    (his : is.Pairwise (· ≤ ·)) :
    orderedMonomial R L ι b (Multiset.toFinsupp (is : Multiset ι)) =
      basisWord R L ι b is := by
  simp only [orderedMonomial, Multiset.toFinsupp_toMultiset, Multiset.coe_sort]
  rw [List.mergeSort_eq_self _ his]
  change (is.map fun i => UniversalEnvelopingAlgebra.ι R (b i)).prod =
    word R L (is.map b)
  unfold word
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  rfl

/-- The span of all words in basis elements, without a length restriction. -/
noncomputable def basisWordTotalSpan (b : Module.Basis ι R L) : Submodule R (UEA R L) :=
  Submodule.span R {u | ∃ is : List ι, basisWord R L ι b is = u}

theorem basisWordSpan_le_totalSpan (b : Module.Basis ι R L) (n : ℕ) :
    basisWordSpan R L ι b n ≤ basisWordTotalSpan R L ι b := by
  apply Submodule.span_le.2
  rintro u ⟨is, _, rfl⟩
  exact Submodule.subset_span ⟨is, rfl⟩

theorem basisWordTotalSpan_mul_mem (b : Module.Basis ι R L) {a c : UEA R L}
    (ha : a ∈ basisWordTotalSpan R L ι b) (hc : c ∈ basisWordTotalSpan R L ι b) :
    a * c ∈ basisWordTotalSpan R L ι b := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨as, rfl⟩ := ha
      induction hc using Submodule.span_induction with
      | mem c hc =>
          obtain ⟨cs, rfl⟩ := hc
          apply Submodule.subset_span
          refine ⟨as ++ cs, ?_⟩
          simp [basisWord, word]
      | zero => simp
      | add c d _ _ hc hd => simpa [mul_add] using Submodule.add_mem _ hc hd
      | smul r c _ hc =>
          rw [mul_smul_comm]
          exact Submodule.smul_mem _ r hc
  | zero => simp
  | add a d _ _ ha hd => simpa [add_mul] using Submodule.add_mem _ ha hd
  | smul r a _ ha =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r ha

/-- Basis words span the whole enveloping algebra. -/
theorem basisWordTotalSpan_eq_top (b : Module.Basis ι R L) :
    basisWordTotalSpan R L ι b = ⊤ := by
  apply top_unique
  intro u hu
  clear hu
  induction u using UEA.induction R L with
  | algebraMap r =>
      rw [← mul_one (algebraMap R (UEA R L) r), ← Algebra.smul_def,
        ← basisWord_nil R L ι b]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], rfl⟩)
  | ι x =>
      have hx := word_mem_basisWordSpan R L ι b [x]
      exact basisWordSpan_le_totalSpan R L ι b 1 (by simpa using hx)
  | mul a c ha hc => exact basisWordTotalSpan_mul_mem R L ι b ha hc
  | add a c ha hc => exact Submodule.add_mem _ ha hc

/-- **Spanning PBW.** Ordered basis monomials span the universal enveloping algebra. -/
theorem orderedPBWMap_surjective [LinearOrder ι] (b : Module.Basis ι R L) :
    Function.Surjective (orderedPBWMap R L ι b) := by
  let P : ℕ → Prop := fun n => ∀ is : List ι, is.length = n →
    basisWord R L ι b is ∈ LinearMap.range (orderedPBWMap R L ι b)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro is his
        subst n
        cases is with
        | nil =>
            refine ⟨MvPolynomial.monomial 0 1, ?_⟩
            simpa [basisWord] using orderedPBWMap_monomial R L ι b 0 1
        | cons i is =>
            let sorted : List ι := ((i :: is : List ι) : Multiset ι).sort (· ≤ ·)
            let e : ι →₀ ℕ := Multiset.toFinsupp ((i :: is : List ι) : Multiset ι)
            have hsorted_pairwise : sorted.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
            have hsorted_mem : basisWord R L ι b sorted ∈
                LinearMap.range (orderedPBWMap R L ι b) := by
              refine ⟨MvPolynomial.monomial e 1, ?_⟩
              rw [orderedPBWMap_monomial, one_smul]
              have hmult : (sorted : Multiset ι) = (i :: is : List ι) :=
                Multiset.sort_eq _ _
              have he : Multiset.toFinsupp (sorted : Multiset ι) = e := by
                simpa [e] using congrArg Multiset.toFinsupp hmult
              rw [← he]
              exact orderedMonomial_multiset_toFinsupp R L ι b sorted hsorted_pairwise
            have hperm : (i :: is).Perm sorted := by
              exact Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _).symm
            have hdiff : basisWord R L ι b (i :: is) - basisWord R L ι b sorted ∈
                wordFiltration R L is.length := by
              have hp := word_sub_word_of_perm R L (hperm.map b)
              simpa [basisWord] using hp
            have hfiltration : wordFiltration R L is.length ≤
                LinearMap.range (orderedPBWMap R L ι b) := by
              apply Submodule.span_le.2
              rintro u ⟨xs, hxs, rfl⟩
              have hxspan := word_mem_basisWordSpan R L ι b xs
              refine Submodule.span_induction (p := fun u _ =>
                  u ∈ LinearMap.range (orderedPBWMap R L ι b)) ?_ ?_ ?_ ?_ hxspan
              · rintro u ⟨js, hjs, rfl⟩
                have hjle : js.length ≤ is.length := hjs.trans_le hxs
                have hjlt : js.length < (i :: is).length := by simpa using hjle
                exact ih js.length hjlt js rfl
              · exact Submodule.zero_mem _
              · exact fun _ _ _ _ hu hv => Submodule.add_mem _ hu hv
              · exact fun r _ _ hu => Submodule.smul_mem _ r hu
            have hdiff_mem := hfiltration hdiff
            rw [show basisWord R L ι b (i :: is) =
                (basisWord R L ι b (i :: is) - basisWord R L ι b sorted) +
                  basisWord R L ι b sorted by abel]
            exact Submodule.add_mem _ hdiff_mem hsorted_mem
  have htotal : basisWordTotalSpan R L ι b ≤
      LinearMap.range (orderedPBWMap R L ι b) := by
    apply Submodule.span_le.2
    rintro u ⟨is, rfl⟩
    exact hP is.length is rfl
  have htop : (⊤ : Submodule R (UEA R L)) ≤
      LinearMap.range (orderedPBWMap R L ι b) := by
    rw [← basisWordTotalSpan_eq_top R L ι b]
    exact htotal
  exact LinearMap.range_eq_top.mp (top_unique htop)

/-- After the spanning theorem, free-module PBW is exactly the remaining linear-independence
claim. -/
theorem freeModulePBW_iff_orderedPBWMap_injective [LinearOrder ι]
    (b : Module.Basis ι R L) :
    FreeModulePBW R L ι b ↔ Function.Injective (orderedPBWMap R L ι b) := by
  constructor
  · exact fun h => h.1
  · intro hinj
    exact ⟨hinj, orderedPBWMap_surjective R L ι b⟩

end LieRings.PBW
