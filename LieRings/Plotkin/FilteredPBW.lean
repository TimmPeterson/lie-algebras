import LieRings.Plotkin.GenericPBW
import LieRings.DimensionSubring.Functoriality
import LieRings.PBW.Collection
import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.Finsupp.Weight

/-!
# Filtered PBW coordinates

This is the filtered, rather than graded, form of the PBW calculation needed in the finite-tail
argument.  A basis vector has a positive filtration weight, and a nonzero coordinate in a bracket
may have any *larger* weight.  Collection therefore cannot preserve an exact weight, but it does
preserve the lower bound on weight.  This is precisely the form used by a basis adapted to the
lower central series of a Lie algebra over a field.
-/

namespace LieRings.Plotkin

noncomputable section

open scoped BigOperators

universe u v w

variable {R : Type u} [CommRing R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]
variable {ι : Type w} [LinearOrder ι]

/-- An ordered basis compatible with an increasing lower bound on bracket weight. -/
structure FilteredBasis where
  basis : Module.Basis ι R L
  weight : ι → ℕ
  weight_pos : ∀ i, 0 < weight i
  bracket_filtered : ∀ i j k,
    basis.repr ⁅basis i, basis j⁆ k ≠ 0 → weight i + weight j ≤ weight k
  iota_mem_augmentation_pow : ∀ i,
    UniversalEnvelopingAlgebra.ι R (basis i) ∈
      UEA.augmentationIdeal R L ^ weight i

namespace FilteredBasis

variable (B : FilteredBasis (R := R) (L := L) (ι := ι))

/-- Total filtration weight of a PBW exponent vector. -/
def bracketWeight (e : ι →₀ ℕ) : ℕ :=
  e.sum fun i m ↦ m * B.weight i

@[simp] theorem bracketWeight_zero : B.bracketWeight 0 = 0 := by
  simp [bracketWeight]

theorem bracketWeight_eq_finsupp_weight (e : ι →₀ ℕ) :
    B.bracketWeight e = Finsupp.weight B.weight e := by
  simp [bracketWeight, Finsupp.weight_apply, nsmul_eq_mul, mul_comm]

/-- The PBW equivalence supplied by the generic Cartan--Eilenberg theorem. -/
def pbwEquiv : MvPolynomial ι R ≃ₗ[R] UEA R L :=
  LinearEquiv.ofBijective (LieRings.PBW.orderedPBWMap R L ι B.basis)
    (LieRings.PBW.freeModulePBW_commRing L ι B.basis)

@[simp] theorem pbwEquiv_monomial (e : ι →₀ ℕ) (r : R) :
    B.pbwEquiv (MvPolynomial.monomial e r) =
      r • LieRings.PBW.orderedMonomial R L ι B.basis e := by
  exact LieRings.PBW.orderedPBWMap_monomial R L ι B.basis e r

@[simp] theorem pbwEquiv_X (i : ι) :
    B.pbwEquiv (MvPolynomial.X i) =
      UniversalEnvelopingAlgebra.ι R (B.basis i) := by
  exact LieRings.PBW.orderedPBWMap_X R L ι B.basis i

/-- The coefficient of one ordered PBW monomial. -/
def coeff (e : ι →₀ ℕ) : UEA R L →ₗ[R] R :=
  (MvPolynomial.lcoeff R e).comp B.pbwEquiv.symm.toLinearMap

/-- Polynomials all of whose monomials have weight at least `r`. -/
def polynomialWeightGE (r : ℕ) : Submodule R (MvPolynomial ι R) :=
  Finsupp.supported R R {e : ι →₀ ℕ | r ≤ B.bracketWeight e}

/-- The PBW submodule supported in filtration weights at least `r`. -/
def weightGE (r : ℕ) : Submodule R (UEA R L) :=
  Submodule.comap B.pbwEquiv.symm.toLinearMap (B.polynomialWeightGE r)

theorem mem_polynomialWeightGE_iff (r : ℕ) (f : MvPolynomial ι R) :
    f ∈ B.polynomialWeightGE r ↔
      ∀ e, B.bracketWeight e < r → MvPolynomial.coeff e f = 0 := by
  constructor
  · intro h e he
    exact (Finsupp.mem_supported' R f).mp h e (by simpa using Nat.not_le.mpr he)
  · intro h
    exact (Finsupp.mem_supported' R f).mpr fun e he ↦
      h e (Nat.lt_of_not_ge (by simpa using he))

theorem mem_weightGE_iff (r : ℕ) (u : UEA R L) :
    u ∈ B.weightGE r ↔ ∀ e, B.bracketWeight e < r → B.coeff e u = 0 := by
  exact B.mem_polynomialWeightGE_iff r (B.pbwEquiv.symm u)

theorem polynomialWeightGE_mono {r s : ℕ} (hrs : r ≤ s) :
    B.polynomialWeightGE s ≤ B.polynomialWeightGE r := by
  intro f hf
  rw [B.mem_polynomialWeightGE_iff] at hf ⊢
  intro e he
  exact hf e (he.trans_le hrs)

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

private theorem sorted_weight (e : ι →₀ ℕ) :
    (((Finsupp.toMultiset e).sort (· ≤ ·)).map B.weight).sum =
      B.bracketWeight e := by
  rw [← Multiset.sum_coe]
  change (Multiset.map B.weight
    (Multiset.ofList ((Finsupp.toMultiset e).sort (· ≤ ·)))).sum = _
  rw [Multiset.sort_eq]
  exact (B.weight_toMultiset e).symm.trans
    (B.bracketWeight_eq_finsupp_weight e).symm

/-- Collection can only increase filtration weight. -/
private theorem pbwPolynomial_basisWord_mem
    (xs : List ι) :
    B.pbwEquiv.symm
        (LieRings.PBW.basisWord R L ι B.basis xs) ∈
      B.polynomialWeightGE ((xs.map B.weight).sum) := by
  let complexity : List ι → ℕ × ℕ := fun ys ↦
    (ys.length, inversionCount ys)
  let descent (new old : List ι) : Prop :=
    Prod.Lex (· < ·) (· < ·) (complexity new) (complexity old)
  have hwell : WellFounded descent :=
    InvImage.wf complexity (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  induction xs using hwell.induction with
  | h xs ih =>
      classical
      cases hchosen : LieRings.PBW.chooseAdjacentInversion? xs with
      | none =>
          have hordered : xs.Pairwise (· ≤ ·) :=
            (LieRings.PBW.chooseAdjacentInversion?_eq_none_iff_pairwise xs).mp hchosen
          let e : ι →₀ ℕ := Multiset.toFinsupp (xs : Multiset ι)
          have hcoordinate :
              B.pbwEquiv.symm (LieRings.PBW.basisWord R L ι B.basis xs) =
                MvPolynomial.monomial e 1 := by
            apply B.pbwEquiv.injective
            rw [LinearEquiv.apply_symm_apply]
            symm
            change LieRings.PBW.orderedPBWMap R L ι B.basis
                (MvPolynomial.monomial e 1) = _
            rw [LieRings.PBW.orderedPBWMap_monomial]
            calc
              (1 : R) • LieRings.PBW.orderedMonomial R L ι B.basis e =
                  LieRings.PBW.orderedMonomial R L ι B.basis e := by simp
              _ = _ := by
                simpa only [e] using
                  (LieRings.PBW.orderedMonomial_multiset_toFinsupp
                    R L ι B.basis xs hordered)
          rw [hcoordinate, B.mem_polynomialWeightGE_iff]
          intro d hd
          rw [MvPolynomial.coeff_monomial]
          by_cases hde : d = e
          · subst d
            have hw : B.bracketWeight e = (xs.map B.weight).sum := by
              rw [B.bracketWeight_eq_finsupp_weight, B.weight_toMultiset]
              simp [e]
            exact (hd.ne hw).elim
          · simp [Ne.symm hde]
      | some d =>
          obtain ⟨hxs, hxy⟩ :=
            LieRings.PBW.chooseAdjacentInversion?_eq_some_realizes hchosen
          let swapped := d.left ++ d.y :: d.x :: d.right
          have hswapDescent : descent swapped xs := by
            unfold descent complexity swapped
            rw [hxs]
            simp only [List.length_append, List.length_cons]
            apply Prod.Lex.right
            have hinv := inversionCount_swap d.left d.right d.x d.y hxy
            omega
          have hswap := ih swapped hswapDescent
          let c : ι →₀ R := B.basis.repr ⁅B.basis d.x, B.basis d.y⁆
          let correction := fun i : ι ↦ d.left ++ i :: d.right
          have hcorrectionDescent (i : ι) : descent (correction i) xs := by
            unfold descent complexity correction
            rw [hxs]
            apply Prod.Lex.left
            simp
          have hcorrection (i : ι) := ih (correction i) (hcorrectionDescent i)
          have hc : c.sum (fun i z ↦ z • B.basis i) =
              ⁅B.basis d.x, B.basis d.y⁆ :=
            B.basis.linearCombination_repr _
          have hword :
              LieRings.PBW.basisWord R L ι B.basis xs =
                LieRings.PBW.basisWord R L ι B.basis swapped +
                  c.sum (fun i z ↦ z •
                    LieRings.PBW.basisWord R L ι B.basis (correction i)) := by
            let context : L →ₗ[R] UEA R L :=
              { toFun := fun z ↦
                  LieRings.PBW.word R L (d.left.map B.basis) *
                    UniversalEnvelopingAlgebra.ι R z *
                      LieRings.PBW.word R L (d.right.map B.basis)
                map_add' := by intro a b; simp [map_add, mul_add, add_mul]
                map_smul' := by
                  intro r z
                  simp only [map_smul]
                  simp only [Algebra.smul_def, ← mul_assoc]
                  rw [Algebra.commutes]
                  simp }
            have hcontext := congrArg context hc
            rw [map_finsuppSum] at hcontext
            have hcontext' :
                c.sum (fun i z ↦ z •
                  LieRings.PBW.basisWord R L ι B.basis (correction i)) =
                    context ⁅B.basis d.x, B.basis d.y⁆ := by
              rw [← hcontext]
              apply Finsupp.sum_congr
              intro i hi
              rw [map_smul]
              simp [context, correction, LieRings.PBW.basisWord,
                LieRings.PBW.word, List.map_append]
              noncomm_ring
            have hswapWord := LieRings.PBW.envelopingWord_adjacent_swap R L
              (d.left.map B.basis) (d.right.map B.basis)
              (B.basis d.x) (B.basis d.y)
            rw [hxs, hcontext']
            simpa only [swapped, context, LieRings.PBW.basisWord,
              LieRings.PBW.word, LieRings.PBW.envelopingWord,
              List.map_append, List.map_cons, List.map_nil, List.map_map,
              Function.comp_apply] using hswapWord
          rw [hword, map_add, map_finsuppSum]
          simp_rw [map_smul]
          apply (B.polynomialWeightGE ((xs.map B.weight).sum)).add_mem
          · simpa [swapped, hxs, add_comm, add_left_comm, add_assoc] using hswap
          · apply (B.polynomialWeightGE ((xs.map B.weight).sum)).sum_mem
            intro i hi
            apply (B.polynomialWeightGE ((xs.map B.weight).sum)).smul_mem
            have hic : c i ≠ 0 := Finsupp.mem_support_iff.mp hi
            have hiweight : B.weight d.x + B.weight d.y ≤ B.weight i :=
              B.bracket_filtered d.x d.y i hic
            apply B.polynomialWeightGE_mono
                (s := ((correction i).map B.weight).sum)
            · simp [correction, hxs]
              omega
            · exact hcorrection i

private theorem orderedMonomial_mul_mem
    (e d : ι →₀ ℕ) :
    B.pbwEquiv.symm
        (LieRings.PBW.orderedMonomial R L ι B.basis e *
          LieRings.PBW.orderedMonomial R L ι B.basis d) ∈
      B.polynomialWeightGE (B.bracketWeight e + B.bracketWeight d) := by
  let es := (Finsupp.toMultiset e).sort (· ≤ ·)
  let ds := (Finsupp.toMultiset d).sort (· ≤ ·)
  have hword : LieRings.PBW.orderedMonomial R L ι B.basis e *
      LieRings.PBW.orderedMonomial R L ι B.basis d =
        LieRings.PBW.basisWord R L ι B.basis (es ++ ds) := by
    unfold LieRings.PBW.orderedMonomial LieRings.PBW.basisWord LieRings.PBW.word
    simp only [es, ds, List.map_append, List.prod_append, List.map_map]
    rfl
  rw [hword]
  simpa [es, ds, B.sorted_weight, List.sum_append] using
    B.pbwPolynomial_basisWord_mem (es ++ ds)

/-- The PBW weight filtration is multiplicative. -/
theorem weightGE_mul {r s : ℕ} {u v : UEA R L}
    (hu : u ∈ B.weightGE r) (hv : v ∈ B.weightGE s) :
    u * v ∈ B.weightGE (r + s) := by
  rw [B.mem_weightGE_iff] at hu hv ⊢
  let f := B.pbwEquiv.symm u
  let g := B.pbwEquiv.symm v
  have hEf : B.pbwEquiv f = u := B.pbwEquiv.apply_symm_apply u
  have hEg : B.pbwEquiv g = v := B.pbwEquiv.apply_symm_apply v
  rw [← hEf, ← hEg]
  intro a ha
  have hprod : B.pbwEquiv f * B.pbwEquiv g =
      ∑ e ∈ f.support, ∑ d ∈ g.support,
        (MvPolynomial.coeff e f * MvPolynomial.coeff d g) •
          (LieRings.PBW.orderedMonomial R L ι B.basis e *
            LieRings.PBW.orderedMonomial R L ι B.basis d) := by
    have hfSum : B.pbwEquiv f = ∑ e ∈ f.support,
        B.pbwEquiv (MvPolynomial.monomial e (MvPolynomial.coeff e f)) := by
      calc
        B.pbwEquiv f = B.pbwEquiv (∑ e ∈ f.support,
            MvPolynomial.monomial e (MvPolynomial.coeff e f)) :=
          congrArg B.pbwEquiv f.as_sum
        _ = _ := by rw [map_sum]
    have hgSum : B.pbwEquiv g = ∑ d ∈ g.support,
        B.pbwEquiv (MvPolynomial.monomial d (MvPolynomial.coeff d g)) := by
      calc
        B.pbwEquiv g = B.pbwEquiv (∑ d ∈ g.support,
            MvPolynomial.monomial d (MvPolynomial.coeff d g)) :=
          congrArg B.pbwEquiv g.as_sum
        _ = _ := by rw [map_sum]
    rw [hfSum, hgSum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [B.pbwEquiv_monomial, B.pbwEquiv_monomial, smul_mul_smul]
  rw [hprod, map_sum]
  apply Finset.sum_eq_zero
  intro e he
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
  have hmem := B.orderedMonomial_mul_mem e d
  have hzero := (B.mem_polynomialWeightGE_iff
    (B.bracketWeight e + B.bracketWeight d) _).mp hmem a (by omega)
  change MvPolynomial.coeff a
      ((MvPolynomial.coeff e f * MvPolynomial.coeff d g) •
        B.pbwEquiv.symm
          (LieRings.PBW.orderedMonomial R L ι B.basis e *
            LieRings.PBW.orderedMonomial R L ι B.basis d)) = 0
  simp [hzero]

private theorem augmentation_orderedMonomial (e : ι →₀ ℕ) :
    UEA.augmentation R L (LieRings.PBW.orderedMonomial R L ι B.basis e) =
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
    rw [LieRings.PBW.orderedMonomial]
    change UEA.augmentation R L
      (((((Finsupp.toMultiset e).sort (· ≤ ·)).map
        (fun i ↦ UniversalEnvelopingAlgebra.ι R (B.basis i))).prod)) = _
    rw [his, List.map_cons, List.prod_cons, map_mul,
      UEA.augmentation_ι, zero_mul]
    simp [he]

private theorem augmentation_pbwEquiv (f : MvPolynomial ι R) :
    UEA.augmentation R L (B.pbwEquiv f) = MvPolynomial.coeff 0 f := by
  let s := f.support
  let term : (ι →₀ ℕ) → MvPolynomial ι R := fun e ↦
    MvPolynomial.monomial e (MvPolynomial.coeff e f)
  have hf : f = ∑ e ∈ s, term e := by
    simpa [s, term] using f.as_sum
  calc
    UEA.augmentation R L (B.pbwEquiv f) =
        ∑ e ∈ s, UEA.augmentation R L (B.pbwEquiv (term e)) := by
      rw [hf, map_sum, map_sum]
    _ = ∑ e ∈ s, MvPolynomial.coeff 0 (term e) := by
      apply Finset.sum_congr rfl
      intro e he
      dsimp only [term]
      rw [B.pbwEquiv_monomial, map_smul, B.augmentation_orderedMonomial]
      by_cases hz : e = 0
      · subst e
        simp
      · simp [hz, MvPolynomial.coeff_monomial]
    _ = MvPolynomial.coeff 0 (∑ e ∈ s, term e) := by
      symm
      change (MvPolynomial.lcoeff R 0) (∑ e ∈ s, term e) = _
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro e he
      rfl
    _ = MvPolynomial.coeff 0 f := by rw [← hf]

theorem augmentationIdeal_le_weightGE_one :
    (UEA.augmentationIdeal R L).restrictScalars R ≤ B.weightGE 1 := by
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
    have : 0 < e i * B.weight i :=
      Nat.mul_pos (Nat.pos_of_ne_zero hi) (B.weight_pos i)
    omega
  subst e
  change MvPolynomial.coeff 0 (B.pbwEquiv.symm u) = 0
  rw [← B.augmentation_pbwEquiv (B.pbwEquiv.symm u),
    B.pbwEquiv.apply_symm_apply]
  exact (UEA.mem_augmentationIdeal R L).mp hu

/-- Every augmentation power has PBW weight at least its exponent. -/
theorem augmentationIdeal_pow_le_weightGE (r : ℕ) :
    (UEA.augmentationIdeal R L ^ r).restrictScalars R ≤ B.weightGE r := by
  induction r with
  | zero =>
      intro u hu
      rw [B.mem_weightGE_iff]
      intro e he
      omega
  | succ r ih =>
      intro u hu
      have hu' : u ∈ (UEA.augmentationIdeal R L ^ r) *
          UEA.augmentationIdeal R L := by simpa [pow_succ] using hu
      exact Submodule.mul_induction_on hu'
        (fun x hx y hy ↦ by
          simpa [Nat.add_comm] using B.weightGE_mul (ih hx)
            (B.augmentationIdeal_le_weightGE_one hy))
        (fun x y hx hy ↦ (B.weightGE (r + 1)).add_mem hx hy)

/-- A primitive in augmentation order above every basis weight is zero. -/
theorem primitive_eq_zero_of_mem_augmentation_pow
    (c : ℕ) (hweight : ∀ i, B.weight i ≤ c) (x : L)
    (hx : UniversalEnvelopingAlgebra.ι R x ∈
      UEA.augmentationIdeal R L ^ (c + 1)) : x = 0 := by
  have hxw : UniversalEnvelopingAlgebra.ι R x ∈ B.weightGE (c + 1) :=
    B.augmentationIdeal_pow_le_weightGE (c + 1) hx
  apply B.basis.repr.injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  have hcoeff := (B.mem_weightGE_iff (c + 1)
    (UniversalEnvelopingAlgebra.ι R x)).mp hxw (Finsupp.single i 1)
  have hlt : B.bracketWeight (Finsupp.single i 1) < c + 1 := by
    simp [bracketWeight, hweight i]
  have hz := hcoeff hlt
  change MvPolynomial.coeff (Finsupp.single i 1)
      (B.pbwEquiv.symm (UniversalEnvelopingAlgebra.ι R x)) = 0 at hz
  have hiota : B.pbwEquiv.symm (UniversalEnvelopingAlgebra.ι R x) =
      LieRings.PBW.basisPolynomial R L ι B.basis x := by
    apply B.pbwEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (LieRings.PBW.orderedPBWMap_basisPolynomial R L ι B.basis x).symm
  rw [hiota] at hz
  let A : L →ₗ[R] R :=
    (MvPolynomial.lcoeff R (Finsupp.single i 1)).comp
      (LieRings.PBW.basisPolynomial R L ι B.basis)
  have hA : A = B.basis.coord i := by
    apply B.basis.ext
    intro j
    by_cases hji : j = i
    · subst j
      simp [A, LieRings.PBW.basisPolynomial_basis]
    · simp [A, LieRings.PBW.basisPolynomial_basis, hji, Ne.symm hji]
  have hAx := LinearMap.congr_fun hA x
  change A x = 0 at hz
  rw [hAx] at hz
  simpa using hz

end FilteredBasis

end

end LieRings.Plotkin
