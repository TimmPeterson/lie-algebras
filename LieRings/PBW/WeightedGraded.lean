import LieRings.DimensionSubring.Functoriality
import LieRings.PBW.Collection
import LieRings.PBW.IntegralFreeModule
import LieRings.UniversalEnveloping.Quotient
import Mathlib.Data.Multiset.Fintype
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted integral PBW coordinates

This file contains the basis-level statement used in the metabelian
dimension-subring argument.  A `WeightedBasis` is an ordered integral basis
whose brackets are homogeneous and whose basis vectors have the asserted
augmentation order.  The resulting PBW coordinates carry two *independent*
statistics: bracket weight and number of Lie factors.
-/

namespace LieRings.PBW

noncomputable section

open scoped BigOperators

universe u v

variable {L : Type u} [LieRing L]
variable {ι : Type v} [LinearOrder ι]

/-- An ordered homogeneous basis, including the one fact about its elements
needed for the reverse inclusion in the augmentation theorem. -/
structure WeightedBasis where
  basis : Module.Basis ι ℤ L
  weight : ι → ℕ
  weight_pos : ∀ i, 0 < weight i
  bracket_homogeneous : ∀ i j k,
    basis.repr ⁅basis i, basis j⁆ k ≠ 0 → weight k = weight i + weight j
  iota_mem_augmentation_pow : ∀ i,
    UniversalEnvelopingAlgebra.ι ℤ (basis i) ∈
      UEA.augmentationIdeal ℤ L ^ weight i

namespace WeightedBasis

variable (B : WeightedBasis (L := L) (ι := ι))

/-- Number of Lie factors in an ordered PBW monomial. -/
def factorNumber (e : ι →₀ ℕ) : ℕ := e.sum fun _ m ↦ m

/-- Total bracket weight of an ordered PBW monomial. -/
def bracketWeight (e : ι →₀ ℕ) : ℕ :=
  e.sum fun i m ↦ m * B.weight i

@[simp] theorem factorNumber_zero : factorNumber (ι := ι) 0 = 0 := by
  simp [factorNumber]

@[simp] theorem bracketWeight_zero : B.bracketWeight 0 = 0 := by
  simp [bracketWeight]

@[simp] theorem factorNumber_single (i : ι) (m : ℕ) :
    factorNumber (Finsupp.single i m) = m := by
  simp [factorNumber]

@[simp] theorem bracketWeight_single (i : ι) (m : ℕ) :
    B.bracketWeight (Finsupp.single i m) = m * B.weight i := by
  simp [bracketWeight]

theorem factorNumber_eq_finsupp_weight_one (e : ι →₀ ℕ) :
    factorNumber e = Finsupp.weight (fun _ : ι ↦ 1) e := by
  simp [factorNumber, Finsupp.weight_apply]

theorem bracketWeight_eq_finsupp_weight (e : ι →₀ ℕ) :
    B.bracketWeight e = Finsupp.weight B.weight e := by
  simp [bracketWeight, Finsupp.weight_apply, nsmul_eq_mul, mul_comm]

/-- The integral PBW linear equivalence attached to this basis. -/
def pbwEquiv : MvPolynomial ι ℤ ≃ₗ[ℤ] UEA ℤ L :=
  LinearEquiv.ofBijective (orderedPBWMap ℤ L ι B.basis)
    (freeModulePBW_int L ι B.basis)

@[simp] theorem pbwEquiv_monomial (e : ι →₀ ℕ) (z : ℤ) :
    B.pbwEquiv (MvPolynomial.monomial e z) =
      z • orderedMonomial ℤ L ι B.basis e := by
  exact orderedPBWMap_monomial ℤ L ι B.basis e z

@[simp] theorem pbwEquiv_X (i : ι) :
    B.pbwEquiv (MvPolynomial.X i) =
      UniversalEnvelopingAlgebra.ι ℤ (B.basis i) := by
  exact orderedPBWMap_X ℤ L ι B.basis i

/-- The coefficient of one exact PBW exponent vector. -/
def coeff (e : ι →₀ ℕ) : UEA ℤ L →ₗ[ℤ] ℤ :=
  (MvPolynomial.lcoeff ℤ e).comp B.pbwEquiv.symm.toLinearMap

/-- Polynomial projection to one exact `(bracket weight, factor number)`
pair.  It is literally finite-support filtering. -/
def polynomialProj (w p : ℕ) : Module.End ℤ (MvPolynomial ι ℤ) :=
  (MvPolynomial.weightedHomogeneousComponent B.weight w).comp
    (MvPolynomial.weightedHomogeneousComponent (fun _ : ι ↦ 1) p)

/-- PBW projection to one exact `(bracket weight, factor number)` pair. -/
def proj (w p : ℕ) : Module.End ℤ (UEA ℤ L) :=
  B.pbwEquiv.toLinearMap.comp
    ((B.polynomialProj w p).comp B.pbwEquiv.symm.toLinearMap)

/-- PBW projection to one exact factor number, without discarding any bracket
weight.  This is the projection needed when a comparison changes a primitive
by a *full* relation: evaluation must take place before any homogeneous
weight component is discarded. -/
def factorProj (p : ℕ) : Module.End ℤ (UEA ℤ L) :=
  B.pbwEquiv.toLinearMap.comp
    ((MvPolynomial.weightedHomogeneousComponent (fun _ : ι ↦ 1) p).comp
      B.pbwEquiv.symm.toLinearMap)

theorem factorProj_monomial (p : ℕ) (e : ι →₀ ℕ) (z : ℤ) :
    B.factorProj p (B.pbwEquiv (MvPolynomial.monomial e z)) =
      if factorNumber e = p
      then B.pbwEquiv (MvPolynomial.monomial e z) else 0 := by
  apply B.pbwEquiv.symm.injective
  change B.pbwEquiv.symm (B.pbwEquiv
      (MvPolynomial.weightedHomogeneousComponent (fun _ : ι ↦ 1) p
        (B.pbwEquiv.symm (B.pbwEquiv (MvPolynomial.monomial e z))))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  by_cases hp : factorNumber e = p
  · rw [if_pos hp, LinearEquiv.symm_apply_apply]
    ext d
    rw [MvPolynomial.coeff_weightedHomogeneousComponent,
      ← factorNumber_eq_finsupp_weight_one]
    by_cases hde : d = e
    · subst d
      simp [hp]
    · rw [MvPolynomial.coeff_monomial]
      have hne : e ≠ d := fun hed ↦ hde hed.symm
      simp [hne]
  · rw [if_neg hp, map_zero]
    ext d
    rw [MvPolynomial.coeff_weightedHomogeneousComponent,
      ← factorNumber_eq_finsupp_weight_one]
    by_cases hde : d = e
    · subst d
      simp [hp]
    · rw [MvPolynomial.coeff_monomial]
      have hne : e ≠ d := fun hed ↦ hde hed.symm
      simp [hne]

/-- The complete one-factor PBW projection fixes every Lie primitive. -/
theorem factorProj_one_iota (x : L) :
    B.factorProj 1 (UniversalEnvelopingAlgebra.ι ℤ x) =
      UniversalEnvelopingAlgebra.ι ℤ x := by
  let f : L →ₗ[ℤ] UEA ℤ L :=
    (B.factorProj 1).comp
      (UniversalEnvelopingAlgebra.ι ℤ : LieHom ℤ L (UEA ℤ L)).toLinearMap
  have hf : f =
      (UniversalEnvelopingAlgebra.ι ℤ : LieHom ℤ L (UEA ℤ L)).toLinearMap := by
    apply B.basis.ext
    intro i
    change B.factorProj 1 (UniversalEnvelopingAlgebra.ι ℤ (B.basis i)) = _
    calc
      B.factorProj 1 (UniversalEnvelopingAlgebra.ι ℤ (B.basis i)) =
          B.factorProj 1 (B.pbwEquiv (MvPolynomial.X i)) := by
            rw [B.pbwEquiv_X]
      _ = B.pbwEquiv (MvPolynomial.X i) := by
        change B.factorProj 1
            (B.pbwEquiv (MvPolynomial.monomial (Finsupp.single i 1) 1)) = _
        rw [B.factorProj_monomial]
        simp
      _ = UniversalEnvelopingAlgebra.ι ℤ (B.basis i) := B.pbwEquiv_X i
  exact LinearMap.congr_fun hf x

/-- An ordered product of two basis primitives has zero complete one-factor
projection. -/
theorem factorProj_one_iota_basis_mul_iota_basis_of_le
    (i j : ι) (hij : i ≤ j) :
    B.factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ (B.basis i) *
          UniversalEnvelopingAlgebra.ι ℤ (B.basis j)) = 0 := by
  let e : ι →₀ ℕ := Multiset.toFinsupp ([i, j] : Multiset ι)
  have hordered : ([i, j] : List ι).Pairwise (· ≤ ·) := by simp [hij]
  have hmon : orderedMonomial ℤ L ι B.basis e =
      UniversalEnvelopingAlgebra.ι ℤ (B.basis i) *
        UniversalEnvelopingAlgebra.ι ℤ (B.basis j) := by
    rw [orderedMonomial_multiset_toFinsupp ℤ L ι B.basis [i, j] hordered]
    simp [basisWord, word]
  have heq : UniversalEnvelopingAlgebra.ι ℤ (B.basis i) *
        UniversalEnvelopingAlgebra.ι ℤ (B.basis j) =
      B.pbwEquiv (MvPolynomial.monomial e 1) := by
    rw [B.pbwEquiv_monomial, one_smul, hmon]
  rw [heq, B.factorProj_monomial]
  have hf : factorNumber e = 2 := by
    change (Multiset.toFinsupp ([i, j] : Multiset ι)).sum
      (fun _ ↦ id) = 2
    rw [Multiset.toFinsupp_sum_eq]
    rfl
  simp [hf]

theorem coeff_polynomialProj (w p : ℕ) (f : MvPolynomial ι ℤ)
    (e : ι →₀ ℕ) :
    MvPolynomial.coeff e (B.polynomialProj w p f) =
      if B.bracketWeight e = w ∧ factorNumber e = p
      then MvPolynomial.coeff e f else 0 := by
  classical
  change MvPolynomial.coeff e
    (MvPolynomial.weightedHomogeneousComponent B.weight w
      (MvPolynomial.weightedHomogeneousComponent (fun _ : ι ↦ 1) p f)) = _
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  rw [← B.bracketWeight_eq_finsupp_weight e,
    ← factorNumber_eq_finsupp_weight_one e]
  by_cases hw : B.bracketWeight e = w <;>
    by_cases hp : factorNumber e = p <;> simp [hw, hp]

theorem coeff_proj (w p : ℕ) (u : UEA ℤ L) (e : ι →₀ ℕ) :
    B.coeff e (B.proj w p u) =
      if B.bracketWeight e = w ∧ factorNumber e = p
      then B.coeff e u else 0 := by
  change MvPolynomial.coeff e
      (B.pbwEquiv.symm (B.pbwEquiv
        (B.polynomialProj w p (B.pbwEquiv.symm u)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact B.coeff_polynomialProj w p (B.pbwEquiv.symm u) e

theorem coeff_factorProj (p : ℕ) (u : UEA ℤ L) (e : ι →₀ ℕ) :
    B.coeff e (B.factorProj p u) =
      if factorNumber e = p then B.coeff e u else 0 := by
  change MvPolynomial.coeff e
      (B.pbwEquiv.symm (B.pbwEquiv
        (MvPolynomial.weightedHomogeneousComponent (fun _ : ι ↦ 1) p
          (B.pbwEquiv.symm u)))) = _
  rw [LinearEquiv.symm_apply_apply,
    MvPolynomial.coeff_weightedHomogeneousComponent,
    ← factorNumber_eq_finsupp_weight_one (e := e)]
  rfl

theorem proj_monomial (w p : ℕ) (e : ι →₀ ℕ) (z : ℤ) :
    B.proj w p (B.pbwEquiv (MvPolynomial.monomial e z)) =
      if B.bracketWeight e = w ∧ factorNumber e = p
      then B.pbwEquiv (MvPolynomial.monomial e z) else 0 := by
  apply B.pbwEquiv.symm.injective
  change B.pbwEquiv.symm (B.pbwEquiv
      (B.polynomialProj w p (B.pbwEquiv.symm
        (B.pbwEquiv (MvPolynomial.monomial e z))))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  by_cases h : B.bracketWeight e = w ∧ factorNumber e = p
  · rw [if_pos h, LinearEquiv.symm_apply_apply]
    ext d
    rw [B.coeff_polynomialProj]
    by_cases hde : d = e
    · subst d
      simp [h]
    · rw [MvPolynomial.coeff_monomial]
      have hne : e ≠ d := fun hed ↦ hde hed.symm
      simp [hne]
  · rw [if_neg h, map_zero]
    ext d
    rw [B.coeff_polynomialProj]
    by_cases hde : d = e
    · subst d
      simp [h]
    · rw [MvPolynomial.coeff_monomial]
      have hne : e ≠ d := fun hed ↦ hde hed.symm
      simp [hne]

/-- The PBW inverse of the enveloping inclusion is the degree-one basis
polynomial. -/
theorem pbwEquiv_symm_iota (x : L) :
    B.pbwEquiv.symm (UniversalEnvelopingAlgebra.ι ℤ x) =
      basisPolynomial ℤ L ι B.basis x := by
  apply B.pbwEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact (orderedPBWMap_basisPolynomial ℤ L ι B.basis x).symm

/-- Exact PBW projection of the enveloping inclusion of a homogeneous basis
vector. -/
theorem proj_iota_basis (i : ι) (w p : ℕ) :
    B.proj w p (UniversalEnvelopingAlgebra.ι ℤ (B.basis i)) =
      if B.weight i = w ∧ p = 1
      then UniversalEnvelopingAlgebra.ι ℤ (B.basis i) else 0 := by
  rw [← B.pbwEquiv_X]
  change B.proj w p
      (B.pbwEquiv (MvPolynomial.monomial (Finsupp.single i 1) 1)) = _
  rw [B.proj_monomial]
  by_cases hw : B.weight i = w <;> by_cases hp : p = 1
  · simp [hw, hp]
  · have hp' : (1 : ℕ) ≠ p := Ne.symm hp
    simp [hw, hp, hp']
  · simp [hw]
  · simp [hw]

/-- An already ordered product of two Lie basis factors has no one-factor PBW
component.  This is the exact two-letter fact used by the terminal block; it
does not invoke a general collector. -/
theorem proj_one_iota_basis_mul_iota_basis_of_le
    (i j : ι) (hij : i ≤ j) (w : ℕ) :
    B.proj w 1
        (UniversalEnvelopingAlgebra.ι ℤ (B.basis i) *
          UniversalEnvelopingAlgebra.ι ℤ (B.basis j)) = 0 := by
  let e : ι →₀ ℕ := Multiset.toFinsupp ([i, j] : Multiset ι)
  have hordered : ([i, j] : List ι).Pairwise (· ≤ ·) := by
    simp [hij]
  have hmon : orderedMonomial ℤ L ι B.basis e =
      UniversalEnvelopingAlgebra.ι ℤ (B.basis i) *
        UniversalEnvelopingAlgebra.ι ℤ (B.basis j) := by
    rw [orderedMonomial_multiset_toFinsupp ℤ L ι B.basis [i, j] hordered]
    simp [basisWord, word]
  have heq : UniversalEnvelopingAlgebra.ι ℤ (B.basis i) *
        UniversalEnvelopingAlgebra.ι ℤ (B.basis j) =
      B.pbwEquiv (MvPolynomial.monomial e 1) := by
    rw [B.pbwEquiv_monomial, one_smul, hmon]
  rw [heq, B.proj_monomial]
  have hf : factorNumber e = 2 := by
    change (Multiset.toFinsupp ([i, j] : Multiset ι)).sum
      (fun _ ↦ id) = 2
    rw [Multiset.toFinsupp_sum_eq]
    rfl
  simp [hf]

/-- Distinct exact bidegrees have disjoint images. -/
theorem proj_proj (w p w' p' : ℕ) (u : UEA ℤ L) :
    B.proj w p (B.proj w' p' u) =
      if w = w' ∧ p = p' then B.proj w p u else 0 := by
  apply B.pbwEquiv.symm.injective
  ext e
  change B.coeff e (B.proj w p (B.proj w' p' u)) = _
  rw [B.coeff_proj]
  by_cases h : B.bracketWeight e = w ∧ factorNumber e = p
  · rw [if_pos h, B.coeff_proj]
    by_cases h' : B.bracketWeight e = w' ∧ factorNumber e = p'
    · rw [if_pos h']
      have hpair : w = w' ∧ p = p' :=
        ⟨h.1.symm.trans h'.1, h.2.symm.trans h'.2⟩
      rw [if_pos hpair]
      change B.coeff e u = B.coeff e (B.proj w p u)
      rw [B.coeff_proj, if_pos h]
    · rw [if_neg h']
      have hpair : ¬(w = w' ∧ p = p') := by
        rintro ⟨rfl, rfl⟩
        exact h' h
      rw [if_neg hpair, map_zero]
      rfl
  · rw [if_neg h]
    by_cases hpair : w = w' ∧ p = p'
    · rw [if_pos hpair]
      change 0 = B.coeff e (B.proj w p u)
      rw [B.coeff_proj, if_neg h]
    · rw [if_neg hpair, map_zero]
      rfl

/-- Filtering first by factor number and then by the matching exact
bidegree is the same as taking the exact bidegree directly. -/
theorem proj_factorProj (w p : ℕ) (u : UEA ℤ L) :
    B.proj w p (B.factorProj p u) = B.proj w p u := by
  apply B.pbwEquiv.symm.injective
  ext e
  change B.coeff e (B.proj w p (B.factorProj p u)) =
    B.coeff e (B.proj w p u)
  rw [B.coeff_proj, B.coeff_proj]
  split_ifs with h
  · rw [B.coeff_factorProj, if_pos h.2]
  · rfl

set_option maxHeartbeats 2000000 in
/-- The exact bidegree projections reconstruct an element.  The `image` is
essential: several PBW monomials can have the same bidegree and that component
must occur only once. -/
theorem sum_proj_support (u : UEA ℤ L) :
    ((B.pbwEquiv.symm u).support.image
        (fun e ↦ (B.bracketWeight e, factorNumber e))).sum
      (fun d ↦ B.proj d.1 d.2 u) = u := by
  classical
  apply B.pbwEquiv.symm.injective
  rw [map_sum]
  ext d
  change (MvPolynomial.lcoeff ℤ d)
      (∑ x ∈ (B.pbwEquiv.symm u).support.image
        (fun e ↦ (B.bracketWeight e, factorNumber e)),
        B.pbwEquiv.symm (B.proj x.1 x.2 u)) = _
  rw [map_sum]
  change (∑ x ∈ (B.pbwEquiv.symm u).support.image
      (fun e ↦ (B.bracketWeight e, factorNumber e)),
      B.coeff d (B.proj x.1 x.2 u)) = B.coeff d u
  by_cases hd : d ∈ (B.pbwEquiv.symm u).support
  · let s : ℕ × ℕ := (B.bracketWeight d, factorNumber d)
    have hs : s ∈ (B.pbwEquiv.symm u).support.image
        (fun e ↦ (B.bracketWeight e, factorNumber e)) :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    rw [Finset.sum_eq_single s]
    · rw [B.coeff_proj]
      rw [if_pos ⟨rfl, rfl⟩]
    · intro t ht hts
      rw [B.coeff_proj]
      rw [if_neg]
      intro hstats
      apply hts
      exact Prod.ext hstats.1.symm hstats.2.symm
    · intro hnot
      exact (hnot hs).elim
  · have hz : MvPolynomial.coeff d (B.pbwEquiv.symm u) = 0 :=
      by simpa [Finsupp.mem_support_iff] using hd
    rw [Finset.sum_eq_zero]
    · exact hz.symm
    · intro e he
      rw [B.coeff_proj]
      split_ifs with h
      · exact hz
      · rfl

/-- The PBW subgroup supported in bracket weights at least `r`. -/
def weightGE (r : ℕ) : Submodule ℤ (UEA ℤ L) :=
  Submodule.comap B.pbwEquiv.symm.toLinearMap
    (Finsupp.supported ℤ ℤ {e : ι →₀ ℕ | r ≤ B.bracketWeight e})

theorem mem_weightGE_iff (r : ℕ) (u : UEA ℤ L) :
    u ∈ B.weightGE r ↔ ∀ e, B.bracketWeight e < r → B.coeff e u = 0 := by
  constructor
  · intro h e he
    have h' := (Finsupp.mem_supported' ℤ (B.pbwEquiv.symm u)).mp h
    change MvPolynomial.coeff e (B.pbwEquiv.symm u) = 0
    exact h' e (by simpa using Nat.not_le.mpr he)
  · intro h
    apply (Finsupp.mem_supported' ℤ (B.pbwEquiv.symm u)).mpr
    intro e he
    change MvPolynomial.coeff e (B.pbwEquiv.symm u) = 0
    exact h e (Nat.lt_of_not_ge (by simpa using he))

theorem proj_eq_zero_of_mem_weightGE {r w p : ℕ} {u : UEA ℤ L}
    (hu : u ∈ B.weightGE r) (hw : w < r) : B.proj w p u = 0 := by
  apply B.pbwEquiv.symm.injective
  change B.pbwEquiv.symm
      (B.pbwEquiv (B.polynomialProj w p (B.pbwEquiv.symm u))) =
    B.pbwEquiv.symm 0
  rw [LinearEquiv.symm_apply_apply, map_zero]
  ext e
  rw [B.coeff_polynomialProj]
  split_ifs with h
  · exact (B.mem_weightGE_iff r u).mp hu e (h.1.trans_lt hw)
  · rfl

/-! ## Collection preserves bracket weight -/

private def inversionCount : List ι → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + inversionCount xs

private theorem inversionCount_swap (left right : List ι) (x y : ι)
    (hxy : y < x) :
    inversionCount (left ++ x :: y :: right) =
      inversionCount (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnx : ¬x < y := not_lt_of_ge (le_of_lt hxy)
      simp [inversionCount, hxy, hnx, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, inversionCount]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp <;> omega
      rw [hfilter, ih]
      omega

private theorem weight_toMultiset (e : ι →₀ ℕ) :
    Finsupp.weight B.weight e =
      (Finsupp.toMultiset e |>.map B.weight).sum := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | @single_add i m e hi hm ih =>
      rw [map_add, Finsupp.toMultiset_add, Multiset.map_add,
        Multiset.sum_add, ih, Finsupp.toMultiset_single,
        Finsupp.weight_single, Multiset.map_nsmul, Multiset.sum_nsmul,
        Multiset.map_singleton, Multiset.sum_singleton]

/-- An already ordered basis word is fixed by the projection to its literal
bracket weight and factor number. -/
theorem proj_basisWord_sorted
    (xs : List ι) (hxs : xs.Pairwise (· ≤ ·)) :
    B.proj (xs.map B.weight).sum xs.length
        (basisWord ℤ L ι B.basis xs) =
      basisWord ℤ L ι B.basis xs := by
  let e : ι →₀ ℕ := Multiset.toFinsupp (xs : Multiset ι)
  have hfactor : factorNumber e = xs.length := by
    change (Multiset.toFinsupp (xs : Multiset ι)).sum
      (fun _ ↦ id) = xs.length
    simpa only [Multiset.card_coe] using
      Multiset.toFinsupp_sum_eq (xs : Multiset ι)
  have hweight : B.bracketWeight e = (xs.map B.weight).sum := by
    rw [B.bracketWeight_eq_finsupp_weight, B.weight_toMultiset]
    simp only [e, Multiset.toFinsupp_toMultiset, Multiset.map_coe,
      Multiset.sum_coe]
  have hword := orderedMonomial_multiset_toFinsupp
    ℤ L ι B.basis xs hxs
  have hmon : B.pbwEquiv (MvPolynomial.monomial e 1) =
      basisWord ℤ L ι B.basis xs := by
    rw [B.pbwEquiv_monomial, one_smul]
    exact hword
  rw [← hmon, B.proj_monomial, if_pos ⟨hweight, hfactor⟩]

/-- Collecting an arbitrary basis word preserves its exact bracket weight.
At an adjacent interchange the ordered branch has the same factors, while the
bracket correction has one fewer factor and the same weight. -/
private theorem pbwPolynomial_basisWord_isWeighted (xs : List ι) :
    MvPolynomial.IsWeightedHomogeneous B.weight
      (B.pbwEquiv.symm (basisWord ℤ L ι B.basis xs))
      ((xs.map B.weight).sum) := by
  let complexity : List ι → ℕ × ℕ := fun ys ↦ (ys.length, inversionCount ys)
  let descent (new old : List ι) : Prop :=
    Prod.Lex (· < ·) (· < ·) (complexity new) (complexity old)
  have hwell : WellFounded descent :=
    InvImage.wf complexity (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  induction xs using hwell.induction with
  | h xs ih =>
      classical
      cases hchosen : chooseAdjacentInversion? xs with
      | none =>
          have hordered : xs.Pairwise (· ≤ ·) :=
            (chooseAdjacentInversion?_eq_none_iff_pairwise xs).mp hchosen
          let e : ι →₀ ℕ := Multiset.toFinsupp (xs : Multiset ι)
          have hcoordinate :
              B.pbwEquiv.symm (basisWord ℤ L ι B.basis xs) =
                MvPolynomial.monomial e 1 := by
            apply B.pbwEquiv.injective
            rw [LinearEquiv.apply_symm_apply]
            symm
            change orderedPBWMap ℤ L ι B.basis
                (MvPolynomial.monomial e 1) = _
            rw [orderedPBWMap_monomial]
            calc
              (1 : ℤ) • orderedMonomial ℤ L ι B.basis e =
                  orderedMonomial ℤ L ι B.basis e := by module
              _ = _ := by
                simpa only [e] using
                  (orderedMonomial_multiset_toFinsupp ℤ L ι B.basis xs hordered)
          rw [hcoordinate]
          apply MvPolynomial.isWeightedHomogeneous_monomial
          rw [weight_toMultiset]
          simpa [e]
      | some d =>
          obtain ⟨hxs, hxy⟩ :=
            chooseAdjacentInversion?_eq_some_realizes hchosen
          let swapped := d.left ++ d.y :: d.x :: d.right
          have hswapDescent : descent swapped xs := by
            unfold descent complexity swapped
            rw [hxs]
            simp only [List.length_append, List.length_cons]
            apply Prod.Lex.right
            have hinv := inversionCount_swap d.left d.right d.x d.y hxy
            omega
          have hswap := ih swapped hswapDescent
          let c : ι →₀ ℤ := B.basis.repr ⁅B.basis d.x, B.basis d.y⁆
          let correction := fun i : ι ↦ d.left ++ i :: d.right
          have hcorrectionDescent (i : ι) : descent (correction i) xs := by
            unfold descent complexity correction
            rw [hxs]
            apply Prod.Lex.left
            simp
          have hcorrection (i : ι) := ih (correction i) (hcorrectionDescent i)
          have hc : c.sum (fun i z ↦ z • B.basis i) =
              ⁅B.basis d.x, B.basis d.y⁆ := by
            exact B.basis.linearCombination_repr _
          have hword :
              basisWord ℤ L ι B.basis xs =
                basisWord ℤ L ι B.basis swapped +
                  c.sum (fun i z ↦ z •
                    basisWord ℤ L ι B.basis (correction i)) := by
            let context : L →+ UEA ℤ L :=
              { toFun := fun z ↦
                  word ℤ L (d.left.map B.basis) *
                    UniversalEnvelopingAlgebra.ι ℤ z *
                      word ℤ L (d.right.map B.basis)
                map_zero' := by simp
                map_add' := by intro a b; simp [map_add, mul_add, add_mul] }
            have hcontext := congrArg context hc
            rw [map_finsuppSum] at hcontext
            have hcontext' :
                c.sum (fun i z ↦ z •
                  basisWord ℤ L ι B.basis (correction i)) =
                    context ⁅B.basis d.x, B.basis d.y⁆ := by
              rw [← hcontext]
              apply Finsupp.sum_congr
              intro i hi
              rw [map_zsmul]
              simp [context, correction, basisWord, word, List.map_append]
              noncomm_ring
            have hswapWord := envelopingWord_adjacent_swap ℤ L
              (d.left.map B.basis) (d.right.map B.basis)
              (B.basis d.x) (B.basis d.y)
            rw [hxs, hcontext']
            simpa only [swapped, context, basisWord, word, envelopingWord,
              List.map_append, List.map_cons, List.map_nil, List.map_map,
              Function.comp_apply] using hswapWord
          have hpoly :
              B.pbwEquiv.symm (basisWord ℤ L ι B.basis xs) =
                B.pbwEquiv.symm (basisWord ℤ L ι B.basis swapped) +
                c.sum (fun i z ↦ z • B.pbwEquiv.symm
                  (basisWord ℤ L ι B.basis (correction i))) := by
            rw [hword, map_add, map_finsuppSum]
            apply congrArg₂ (fun a b ↦ a + b) rfl
            apply Finsupp.sum_congr
            intro i hi
            rw [map_zsmul]
          rw [hpoly]
          apply MvPolynomial.IsWeightedHomogeneous.add
          · simpa [swapped, hxs, add_comm, add_left_comm, add_assoc] using hswap
          · apply (MvPolynomial.weightedHomogeneousSubmodule ℤ B.weight
              ((xs.map B.weight).sum)).sum_mem
            intro i hi
            apply (MvPolynomial.weightedHomogeneousSubmodule ℤ B.weight
              ((xs.map B.weight).sum)).smul_mem
            have hic : c i ≠ 0 := Finsupp.mem_support_iff.mp hi
            have hiweight : B.weight i = B.weight d.x + B.weight d.y :=
              B.bracket_homogeneous d.x d.y i hic
            simpa [correction, hxs, hiweight, add_comm, add_left_comm,
              add_assoc] using hcorrection i

/-- An arbitrary (not necessarily ordered) word in homogeneous basis
elements has no PBW component in a different bracket weight.  This is the
public projection form of the collection theorem above; clients do not need
to inspect the chosen sequence of adjacent interchanges. -/
theorem proj_basisWord_eq_zero_of_weight_ne
    (xs : List ι) (w p : ℕ)
    (hne : (xs.map B.weight).sum ≠ w) :
    B.proj w p (basisWord ℤ L ι B.basis xs) = 0 := by
  apply B.pbwEquiv.symm.injective
  change B.pbwEquiv.symm (B.pbwEquiv (B.polynomialProj w p
      (B.pbwEquiv.symm (basisWord ℤ L ι B.basis xs)))) =
    B.pbwEquiv.symm 0
  rw [LinearEquiv.symm_apply_apply, map_zero]
  ext e
  rw [B.coeff_polynomialProj]
  split_ifs with he
  · apply (B.pbwPolynomial_basisWord_isWeighted xs).coeff_eq_zero
    rw [← B.bracketWeight_eq_finsupp_weight]
    intro heq
    apply hne
    exact heq.symm.trans he.1
  · rfl

private theorem sorted_weight (e : ι →₀ ℕ) :
    (((Finsupp.toMultiset e).sort (· ≤ ·)).map B.weight).sum =
      B.bracketWeight e := by
  rw [← Multiset.sum_coe]
  change (Multiset.map B.weight
    (Multiset.ofList ((Finsupp.toMultiset e).sort (· ≤ ·)))).sum = _
  rw [Multiset.sort_eq]
  exact (B.weight_toMultiset e).symm.trans
    (B.bracketWeight_eq_finsupp_weight e).symm

/-- A product of two ordered PBW monomials collects in their summed exact
bracket weight. -/
private theorem pbwPolynomial_orderedMonomial_mul_isWeighted
    (e d : ι →₀ ℕ) :
    MvPolynomial.IsWeightedHomogeneous B.weight
      (B.pbwEquiv.symm
        (orderedMonomial ℤ L ι B.basis e *
          orderedMonomial ℤ L ι B.basis d))
      (B.bracketWeight e + B.bracketWeight d) := by
  let es := (Finsupp.toMultiset e).sort (· ≤ ·)
  let ds := (Finsupp.toMultiset d).sort (· ≤ ·)
  have hword : orderedMonomial ℤ L ι B.basis e *
      orderedMonomial ℤ L ι B.basis d =
        basisWord ℤ L ι B.basis (es ++ ds) := by
    unfold orderedMonomial basisWord word
    simp only [es, ds, List.map_append, List.prod_append, List.map_map]
    rfl
  rw [hword]
  simpa [es, ds, B.sorted_weight, List.sum_append] using
    B.pbwPolynomial_basisWord_isWeighted (es ++ ds)

/-- The PBW weight filtration is multiplicative. -/
theorem weightGE_mul {r s : ℕ} {u v : UEA ℤ L}
    (hu : u ∈ B.weightGE r) (hv : v ∈ B.weightGE s) :
    u * v ∈ B.weightGE (r + s) := by
  rw [B.mem_weightGE_iff] at hu hv ⊢
  let f := B.pbwEquiv.symm u
  let g := B.pbwEquiv.symm v
  have hEf : B.pbwEquiv f = u := B.pbwEquiv.apply_symm_apply u
  have hEg : B.pbwEquiv g = v := B.pbwEquiv.apply_symm_apply v
  rw [← hEf, ← hEg]
  change ∀ a, B.bracketWeight a < r + s →
    MvPolynomial.coeff a
      (B.pbwEquiv.symm (B.pbwEquiv f * B.pbwEquiv g)) = 0
  intro a ha
  have hprod : B.pbwEquiv f * B.pbwEquiv g =
      ∑ e ∈ f.support, ∑ d ∈ g.support,
        (MvPolynomial.coeff e f * MvPolynomial.coeff d g) •
          (orderedMonomial ℤ L ι B.basis e *
            orderedMonomial ℤ L ι B.basis d) := by
    have hfSum : B.pbwEquiv f = ∑ e ∈ f.support,
        B.pbwEquiv (MvPolynomial.monomial e (MvPolynomial.coeff e f)) := by
      calc
        B.pbwEquiv f = B.pbwEquiv (∑ e ∈ f.support,
            MvPolynomial.monomial e (MvPolynomial.coeff e f)) :=
          congrArg B.pbwEquiv f.as_sum
        _ = _ := by
          rw [map_sum]
    have hgSum : B.pbwEquiv g = ∑ d ∈ g.support,
        B.pbwEquiv (MvPolynomial.monomial d (MvPolynomial.coeff d g)) := by
      calc
        B.pbwEquiv g = B.pbwEquiv (∑ d ∈ g.support,
            MvPolynomial.monomial d (MvPolynomial.coeff d g)) :=
          congrArg B.pbwEquiv g.as_sum
        _ = _ := by
          rw [map_sum]
    rw [hfSum, hgSum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [B.pbwEquiv_monomial, B.pbwEquiv_monomial, smul_mul_smul]
  rw [hprod, map_sum]
  change (MvPolynomial.lcoeff ℤ a)
      (∑ e ∈ f.support, B.pbwEquiv.symm
        (∑ d ∈ g.support,
          (MvPolynomial.coeff e f * MvPolynomial.coeff d g) •
            (orderedMonomial ℤ L ι B.basis e *
              orderedMonomial ℤ L ι B.basis d))) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro e he
  rw [map_sum]
  change (MvPolynomial.lcoeff ℤ a)
      (∑ d ∈ g.support, B.pbwEquiv.symm
        ((MvPolynomial.coeff e f * MvPolynomial.coeff d g) •
          (orderedMonomial ℤ L ι B.basis e *
            orderedMonomial ℤ L ι B.basis d))) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  simp only [map_smul]
  by_cases hfe : MvPolynomial.coeff e f = 0
  · simp [hfe]
  by_cases hgd : MvPolynomial.coeff d g = 0
  · simp [hgd]
  have her : r ≤ B.bracketWeight e := by
    by_contra h
    exact hfe (hu e (Nat.lt_of_not_ge h))
  have hds : s ≤ B.bracketWeight d := by
    by_contra h
    exact hgd (hv d (Nat.lt_of_not_ge h))
  have hhom := B.pbwPolynomial_orderedMonomial_mul_isWeighted e d
  have hane : B.bracketWeight a ≠ B.bracketWeight e + B.bracketWeight d := by
    omega
  have hcoeff := hhom.coeff_eq_zero a (by
    rw [← B.bracketWeight_eq_finsupp_weight]
    exact hane)
  change MvPolynomial.coeff a
      ((MvPolynomial.coeff e f * MvPolynomial.coeff d g) •
        B.pbwEquiv.symm
          (orderedMonomial ℤ L ι B.basis e *
            orderedMonomial ℤ L ι B.basis d)) = 0
  change (MvPolynomial.lcoeff ℤ a)
      ((MvPolynomial.coeff e f * MvPolynomial.coeff d g) •
        B.pbwEquiv.symm
          (orderedMonomial ℤ L ι B.basis e *
            orderedMonomial ℤ L ι B.basis d)) = 0
  rw [map_smul]
  have hcoeff' : (MvPolynomial.lcoeff ℤ a)
      (B.pbwEquiv.symm
        (orderedMonomial ℤ L ι B.basis e *
          orderedMonomial ℤ L ι B.basis d)) = 0 := hcoeff
  rw [hcoeff', smul_zero]

/-! ## The augmentation filtration -/

private theorem augmentation_orderedMonomial (e : ι →₀ ℕ) :
    UEA.augmentation ℤ L (orderedMonomial ℤ L ι B.basis e) =
      if e = 0 then 1 else 0 := by
  classical
  by_cases he : e = 0
  · subst e
    simp
  · have hnonempty : (Finsupp.toMultiset e).sort (· ≤ ·) ≠ [] := by
      intro h
      have : Finsupp.toMultiset e = 0 := by
        simpa using congrArg Multiset.ofList h
      apply he
      ext i
      have hi := congrArg (Multiset.count i) this
      simpa using hi
    obtain ⟨i, is, his⟩ := List.exists_cons_of_ne_nil hnonempty
    rw [orderedMonomial]
    change UEA.augmentation ℤ L
      (((((Finsupp.toMultiset e).sort (· ≤ ·)).map
        (fun i ↦ UniversalEnvelopingAlgebra.ι ℤ (B.basis i))).prod)) = _
    rw [his]
    rw [List.map_cons, List.prod_cons, map_mul,
      UEA.augmentation_ι, zero_mul]
    simp [he]

private theorem augmentation_pbwEquiv (f : MvPolynomial ι ℤ) :
    UEA.augmentation ℤ L (B.pbwEquiv f) = MvPolynomial.coeff 0 f := by
  let s := f.support
  let term : (ι →₀ ℕ) → MvPolynomial ι ℤ := fun e ↦
    MvPolynomial.monomial e (MvPolynomial.coeff e f)
  have hf : f = ∑ e ∈ s, term e := by
    simpa [s, term] using f.as_sum
  calc
    UEA.augmentation ℤ L (B.pbwEquiv f) =
        ∑ e ∈ s, UEA.augmentation ℤ L (B.pbwEquiv (term e)) := by
      rw [hf, map_sum, map_sum]
    _ = ∑ e ∈ s, MvPolynomial.coeff 0 (term e) := by
      apply Finset.sum_congr rfl
      intro e he
      dsimp only [term]
      rw [B.pbwEquiv_monomial, map_smul, B.augmentation_orderedMonomial]
      by_cases hz : e = 0
      · subst e
        simp only [if_pos rfl, smul_eq_mul, mul_one,
          MvPolynomial.coeff_monomial, ↓reduceIte]
      · simp [hz, MvPolynomial.coeff_monomial]
    _ = MvPolynomial.coeff 0 (∑ e ∈ s, term e) := by
      symm
      change (MvPolynomial.lcoeff ℤ 0) (∑ e ∈ s, term e) = _
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro e he
      rfl
    _ = MvPolynomial.coeff 0 f := by rw [← hf]

theorem augmentationIdeal_le_weightGE_one :
    (UEA.augmentationIdeal ℤ L).restrictScalars ℤ ≤ B.weightGE 1 := by
  intro u hu
  rw [B.mem_weightGE_iff]
  intro e he
  have he0 : e = 0 := by
    have hw0 : B.bracketWeight e = 0 := by omega
    apply Finsupp.ext
    intro i
    by_contra hi
    have hwi : e i * B.weight i ≤ B.bracketWeight e := by
      have hsingle := Finsupp.single_le_sum e
        (g := fun j m ↦ m * B.weight j)
        (fun j m ↦ Nat.zero_le (m * B.weight j)) i
      simpa [bracketWeight] using hsingle
    have : 0 < e i * B.weight i := Nat.mul_pos (Nat.pos_of_ne_zero hi) (B.weight_pos i)
    omega
  subst e
  change MvPolynomial.coeff 0 (B.pbwEquiv.symm u) = 0
  rw [← B.augmentation_pbwEquiv (B.pbwEquiv.symm u),
    B.pbwEquiv.apply_symm_apply]
  exact (UEA.mem_augmentationIdeal ℤ L).mp hu

private theorem augmentation_pow_le_weightGE (r : ℕ) :
    (UEA.augmentationIdeal ℤ L ^ r).restrictScalars ℤ ≤ B.weightGE r := by
  induction r with
  | zero =>
      intro u hu
      rw [B.mem_weightGE_iff]
      intro e he
      omega
  | succ r ih =>
      intro u hu
      have hu' : u ∈ (UEA.augmentationIdeal ℤ L ^ r) *
          UEA.augmentationIdeal ℤ L := by simpa [pow_succ] using hu
      exact Submodule.mul_induction_on hu'
        (fun x hx y hy ↦ by
          simpa [Nat.add_comm] using B.weightGE_mul (ih hx)
            (B.augmentationIdeal_le_weightGE_one hy))
        (fun x y hx hy ↦ (B.weightGE (r + 1)).add_mem hx hy)

private theorem orderedMonomial_mem_augmentation_pow (e : ι →₀ ℕ) :
    orderedMonomial ℤ L ι B.basis e ∈
      UEA.augmentationIdeal ℤ L ^ B.bracketWeight e := by
  let xs := (Finsupp.toMultiset e).sort (· ≤ ·)
  have hweight : (xs.map B.weight).sum = B.bracketWeight e := B.sorted_weight e
  have hword : ∀ ys : List ι,
      (ys.map (fun i ↦ UniversalEnvelopingAlgebra.ι ℤ (B.basis i))).prod ∈
        UEA.augmentationIdeal ℤ L ^ (ys.map B.weight).sum := by
    intro ys
    induction ys with
    | nil =>
      change (1 : UEA ℤ L) ∈ UEA.augmentationIdeal ℤ L ^ 0
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      simp
    | cons i is ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        rw [Ideal.IsTwoSided.pow_add]
        exact Submodule.mul_mem_mul (B.iota_mem_augmentation_pow i) ih
  change (xs.map (fun i ↦ UniversalEnvelopingAlgebra.ι ℤ (B.basis i))).prod ∈ _
  rw [← hweight]
  exact hword xs

private theorem weightGE_le_augmentation_pow (r : ℕ) :
    B.weightGE r ≤ (UEA.augmentationIdeal ℤ L ^ r).restrictScalars ℤ := by
  intro u hu
  let f := B.pbwEquiv.symm u
  have huf : B.pbwEquiv f = u := B.pbwEquiv.apply_symm_apply u
  rw [← huf, f.as_sum, map_sum]
  apply (UEA.augmentationIdeal ℤ L ^ r).sum_mem
  intro e he
  rw [B.pbwEquiv_monomial]
  apply ((UEA.augmentationIdeal ℤ L ^ r).restrictScalars ℤ).smul_mem
  have her : r ≤ B.bracketWeight e := by
    by_contra h
    have hz := (B.mem_weightGE_iff r u).mp hu e (Nat.lt_of_not_ge h)
    exact Finsupp.mem_support_iff.mp he hz
  exact Ideal.pow_le_pow_right her (B.orderedMonomial_mem_augmentation_pow e)

/-- **Weighted augmentation theorem.**  The `r`th augmentation power is
exactly the PBW subgroup supported in bracket weights at least `r`. -/
theorem augmentationIdeal_pow_eq_weightGE (r : ℕ) :
    (UEA.augmentationIdeal ℤ L ^ r).restrictScalars ℤ = B.weightGE r := by
  apply le_antisymm
  · exact B.augmentation_pow_le_weightGE r
  · exact B.weightGE_le_augmentation_pow r

/-! ## Kernel of a surjective enveloping-algebra map -/

/-- The first-isomorphism Lie equivalence attached to a surjection. -/
def quotientKerEquivOfSurjective {F : Type*} {K : Type*}
    [LieRing F] [LieRing K] (f : F →ₗ⁅ℤ⁆ K)
    (hf : Function.Surjective f) : (F ⧸ LieHom.ker f) ≃ₗ⁅ℤ⁆ K where
  toLieHom :=
    { f.toLinearMap.quotKerEquivOfSurjective hf with
      map_lie' := by
        intro x y
        induction x using Submodule.Quotient.induction_on
        induction y using Submodule.Quotient.induction_on
        exact LieHom.map_lie f _ _ }
  invFun := (f.toLinearMap.quotKerEquivOfSurjective hf).symm
  left_inv := (f.toLinearMap.quotKerEquivOfSurjective hf).symm_apply_apply
  right_inv := (f.toLinearMap.quotKerEquivOfSurjective hf).apply_symm_apply

/-- A surjective Lie map has exactly the two-sided ideal generated by its Lie
kernel as the kernel of the induced enveloping-algebra map. -/
theorem mem_ker_map_iff_mem_idealOfLieIdeal {F : Type*} {K : Type*}
    [LieRing F] [LieRing K] (f : F →ₗ⁅ℤ⁆ K)
    (hf : Function.Surjective f) (u : UEA ℤ F) :
    UEA.map ℤ F K f u = 0 ↔
      u ∈ UEA.idealOfLieIdeal ℤ F (LieHom.ker f) := by
  let q := UEA.lieIdealQuotientMk ℤ F (LieHom.ker f)
  let e := quotientKerEquivOfSurjective f hf
  have hfac : UEA.map ℤ F K f u =
      UEA.map ℤ (F ⧸ LieHom.ker f) K e.toLieHom
        (UEA.map ℤ F (F ⧸ LieHom.ker f) q u) := by
    let g := (UEA.map ℤ (F ⧸ LieHom.ker f) K e.toLieHom).comp
      (UEA.map ℤ F (F ⧸ LieHom.ker f) q)
    have hg : UEA.map ℤ F K f = g := by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      change UEA.map ℤ F K f (UniversalEnvelopingAlgebra.ι ℤ x) =
        UEA.map ℤ (F ⧸ LieHom.ker f) K e.toLieHom
          (UEA.map ℤ F (F ⧸ LieHom.ker f) q
            (UniversalEnvelopingAlgebra.ι ℤ x))
      rw [UEA.map_ι]
      rw [show UEA.map ℤ F (F ⧸ LieHom.ker f) q
          (UniversalEnvelopingAlgebra.ι ℤ x) =
          UniversalEnvelopingAlgebra.ι ℤ (q x) by
        exact UEA.map_ι ℤ F (F ⧸ LieHom.ker f) q x]
      rw [show UEA.map ℤ (F ⧸ LieHom.ker f) K e.toLieHom
          (UniversalEnvelopingAlgebra.ι ℤ (q x)) =
          UniversalEnvelopingAlgebra.ι ℤ (e (q x)) by
        exact UEA.map_ι ℤ (F ⧸ LieHom.ker f) K e.toLieHom (q x)]
      change (UniversalEnvelopingAlgebra.ι ℤ) (f x) =
        (UniversalEnvelopingAlgebra.ι ℤ) (e (q x))
      congr 1
    exact DFunLike.congr_fun hg u
  rw [hfac]
  change (UEA.mapEquiv ℤ (F ⧸ LieHom.ker f) K e)
      (UEA.map ℤ F (F ⧸ LieHom.ker f) q u) = 0 ↔ _
  rw [map_eq_zero_iff (UEA.mapEquiv ℤ (F ⧸ LieHom.ker f) K e)
    (UEA.mapEquiv ℤ (F ⧸ LieHom.ker f) K e).injective]
  let E := UEA.quotientEquivLieIdeal ℤ F (LieHom.ker f)
  calc
    UEA.map ℤ F (F ⧸ LieHom.ker f) q u = 0 ↔
        E (UEA.map ℤ F (F ⧸ LieHom.ker f) q u) = 0 :=
      (map_eq_zero_iff E E.injective).symm
    _ ↔ u ∈ UEA.idealOfLieIdeal ℤ F (LieHom.ker f) := by
      rw [show E (UEA.map ℤ F (F ⧸ LieHom.ker f) q u) =
          Ideal.Quotient.mk (UEA.idealOfLieIdeal ℤ F (LieHom.ker f)) u by
        let g := E.toAlgHom.comp (UEA.map ℤ F (F ⧸ LieHom.ker f) q)
        let h := Ideal.Quotient.mkₐ ℤ
          (UEA.idealOfLieIdeal ℤ F (LieHom.ker f))
        have hgh : g = h := by
          apply UniversalEnvelopingAlgebra.hom_ext
          apply LieHom.ext
          intro x
          change E (UEA.map ℤ F (F ⧸ LieHom.ker f) q
              (UniversalEnvelopingAlgebra.ι ℤ x)) =
            Ideal.Quotient.mk (UEA.idealOfLieIdeal ℤ F (LieHom.ker f))
              (UniversalEnvelopingAlgebra.ι ℤ x)
          rw [UEA.map_ι]
          change (UEA.quotientEquivLieIdeal ℤ F (LieHom.ker f))
            (UniversalEnvelopingAlgebra.ι ℤ
              (LieSubmodule.Quotient.mk x : F ⧸ LieHom.ker f)) = _
          exact UEA.quotientEquivLieIdeal_ι_mk ℤ F (LieHom.ker f) x
        exact DFunLike.congr_fun hgh u]
      exact Ideal.Quotient.eq_zero_iff_mem

end WeightedBasis

end

end LieRings.PBW
