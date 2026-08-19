import LieRings.DimensionSubring.MetabelianVanishing.MarkedCollector

/-!
# The two-filtered closed square

This file contains the PBW factor symbol and the actual degree-one Koszul
chains read from a full-relation row.  The definitions are coordinate-free
after the one unavoidable PBW coordinate projection: a monomial of factor
number `q` is sent to the corresponding genuine symmetric tensor and then
projected down the tower `A_k`.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open TensorProduct
open LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance closedSquareFintype : Fintype L := Fintype.ofFinite L

/-! ## Exact-factor PBW symbols -/

/-- The unordered monomial represented by an exponent vector of the stated
factor number. -/
def exponentSym (q : ℕ) (e : AdaptedIndex n L data hn →₀ ℕ)
    (he : e.sum (fun _ z ↦ z) = q) :
    Sym (AdaptedIndex n L data hn) q :=
  Sym.mk (Finsupp.toMultiset e) ((Finsupp.card_toMultiset e).trans he)

/-- The unordered monomial underlying a literal list. -/
def listSym (xs : List (AdaptedIndex n L data hn)) :
    Sym (AdaptedIndex n L data hn) xs.length :=
  Sym.mk (xs : Multiset (AdaptedIndex n L data hn)) rfl

private local instance squareVectorPermSetoid {κ : Type*} (q : ℕ) :
    Setoid (List.Vector κ q) := List.Vector.Perm.isSetoid κ q

/-- A public local representative for a `Sym` index.  The symmetric-power
API intentionally hides its internal representative; the closed-square
support calculation only needs one representative together with this
choice-independent equation. -/
private noncomputable def squareSymRepresentative {κ : Type*} (q : ℕ)
    (s : Sym κ q) : Fin q → κ :=
  (Quotient.out (Sym.symEquivSym' s)).get

private theorem symIndexOfFun_squareSymRepresentative {κ : Type*} [Finite κ]
    (q : ℕ) (s : Sym κ q) :
    SymmetricPower.symIndexOfFun q (squareSymRepresentative q s) = s := by
  apply Sym.symEquivSym'.injective
  change Quotient.mk' (List.Vector.ofFn
      (Quotient.out (Sym.symEquivSym' s)).get) = Sym.symEquivSym' s
  rw [show List.Vector.ofFn (Quotient.out (Sym.symEquivSym' s)).get =
      Quotient.out (Sym.symEquivSym' s) by
    exact List.Vector.ofFn_get _]
  exact Quotient.out_eq _

theorem coe_symIndexOfFun {κ : Type*} [Finite κ]
    (q : ℕ) (p : Fin q → κ) :
    (SymmetricPower.symIndexOfFun q p : Multiset κ) =
      (List.ofFn p : Multiset κ) := by
  induction p using Fin.consInduction with
  | elim0 =>
      have hnil :
          SymmetricPower.symIndexOfFun 0 (Fin.elim0 : Fin 0 → κ) =
            (Sym.nil : Sym κ 0) := Subsingleton.elim _ _
      rw [hnil]
      rfl
  | cons x p ih =>
      rw [SymmetricPower.symIndexOfFun_cons, Sym.coe_cons, ih]
      simp

private theorem monomialBasis_eq_tprod_squareSymRepresentative
    {M κ : Type*} [AddCommGroup M] [Module ℤ M]
    [Finite κ] (b : Module.Basis κ ℤ M) (q : ℕ) (s : Sym κ q) :
    SymmetricPower.monomialBasis b q s =
      SymmetricPower.tprod ℤ
        (b ∘ squareSymRepresentative q s) := by
  apply (SymmetricPower.monomialBasis b q).repr.injective
  rw [(SymmetricPower.monomialBasis b q).repr_self]
  change Finsupp.single s 1 = SymmetricPower.monomialRepr b q
    (SymmetricPower.tprod ℤ (b ∘ squareSymRepresentative q s))
  rw [SymmetricPower.monomialRepr_tprod_basis,
    symIndexOfFun_squareSymRepresentative]

theorem monomialBasis_eq_tprod_of_symIndex
    {M κ : Type*} [AddCommGroup M] [Module ℤ M] [Finite κ]
    (b : Module.Basis κ ℤ M) (q : ℕ) (s : Sym κ q)
    (p : Fin q → κ) (hp : SymmetricPower.symIndexOfFun q p = s) :
    SymmetricPower.monomialBasis b q s =
      SymmetricPower.tprod ℤ (b ∘ p) := by
  apply (SymmetricPower.monomialBasis b q).repr.injective
  rw [(SymmetricPower.monomialBasis b q).repr_self]
  change Finsupp.single s 1 = SymmetricPower.monomialRepr b q
    (SymmetricPower.tprod ℤ (b ∘ p))
  rw [SymmetricPower.monomialRepr_tprod_basis, hp]

private theorem bracketWeight_eq_toMultiset_sum
    (e : AdaptedIndex n L data hn →₀ ℕ) :
    (adaptedWeightedBasis n L data hn).bracketWeight e =
      ((Finsupp.toMultiset e).map
        (adaptedWeightedBasis n L data hn).weight).sum := by
  classical
  induction e using Finsupp.induction with
  | zero => simp [LieRings.PBW.WeightedBasis.bracketWeight]
  | @single_add i m e hi hm ih =>
      rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.sum_add, ← ih]
      unfold LieRings.PBW.WeightedBasis.bracketWeight
      rw [Finsupp.sum_add_index']
      · rw [Finsupp.toMultiset_single, Multiset.map_nsmul,
          Multiset.map_singleton, Multiset.sum_nsmul,
          Multiset.sum_singleton]
        simp [Finsupp.sum_single_index, nsmul_eq_mul]
      · intro i
        simp
      · intro i a b
        exact Nat.add_mul a b _

private theorem exponent_eq_single_of_factorNumber_eq_one
    (e : AdaptedIndex n L data hn →₀ ℕ)
    (he : LieRings.PBW.WeightedBasis.factorNumber e = 1) :
    ∃ i, e = Finsupp.single i 1 := by
  classical
  have hcard : (Finsupp.toMultiset e).card = 1 := by
    rw [Finsupp.card_toMultiset]
    simpa [LieRings.PBW.WeightedBasis.factorNumber] using he
  obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp hcard
  refine ⟨i, ?_⟩
  apply Finsupp.ext
  intro j
  have hc := congrArg (Multiset.count j) hi
  rw [Finsupp.count_toMultiset] at hc
  by_cases hji : j = i
  · subst j
    simpa using hc
  · simpa [hji] using hc

private theorem exponentSum_toFinsupp
    (xs : List (AdaptedIndex n L data hn)) :
    (Multiset.toFinsupp (xs : Multiset (AdaptedIndex n L data hn))).sum
        (fun _ z ↦ z) = xs.length := by
  simpa only [id_eq, Multiset.coe_sort, Multiset.card_coe] using
    (Multiset.toFinsupp_sum_eq
      (xs : Multiset (AdaptedIndex n L data hn)))

private theorem exponentSym_toFinsupp
    (xs : List (AdaptedIndex n L data hn)) :
    exponentSym n L data hn xs.length
        (Multiset.toFinsupp (xs : Multiset (AdaptedIndex n L data hn)))
        (exponentSum_toFinsupp n L data hn xs) =
      listSym n L data hn xs := by
  apply Subtype.ext
  simp [exponentSym, listSym]

/-- One exponent coordinate, retained only in exact factor number `q`. -/
def exponentFactorCoordinate (q : ℕ)
    (e : AdaptedIndex n L data hn →₀ ℕ) :
    ℤ →ₗ[ℤ] (Sym (AdaptedIndex n L data hn) q →₀ ℤ) :=
  if he : e.sum (fun _ z ↦ z) = q then
    Finsupp.lsingle (exponentSym n L data hn q e he)
  else 0

/-- Projection of a PBW polynomial to the free coordinates on unordered
monomials with exactly `q` factors. -/
def polynomialFactorCoordinates (q : ℕ) :
    MvPolynomial (AdaptedIndex n L data hn) ℤ →ₗ[ℤ]
      (Sym (AdaptedIndex n L data hn) q →₀ ℤ) :=
  Finsupp.lsum ℤ (fun e ↦ exponentFactorCoordinate n L data hn q e)

theorem polynomialFactorCoordinates_monomial (q : ℕ)
    (e : AdaptedIndex n L data hn →₀ ℕ) (z : ℤ) :
    polynomialFactorCoordinates n L data hn q (MvPolynomial.monomial e z) =
      if he : e.sum (fun _ r ↦ r) = q then
        Finsupp.single (exponentSym n L data hn q e he) z
      else 0 := by
  classical
  change ((Finsupp.lsum ℤ) (fun e ↦
      exponentFactorCoordinate n L data hn q e)) (Finsupp.single e z) = _
  rw [Finsupp.lsum_single]
  unfold exponentFactorCoordinate
  split <;> simp_all

/-- The exact-factor PBW symbol in the symmetric power of the full free
model. -/
def fullRightSymbol (q : ℕ) :
    UEA ℤ (FreeModel n L) →ₗ[ℤ]
      Sym[ℤ] (Fin q) (FreeModel n L) :=
  (SymmetricPower.monomialLinearEquiv
      (adaptedBasis n L data hn) q).symm.toLinearMap.comp
    ((polynomialFactorCoordinates n L data hn q).comp
      (adaptedWeightedBasis n L data hn).pbwEquiv.symm.toLinearMap)

/-- The complete one-factor PBW primitive, transported back from the first
symmetric power to the free metabelian Lie ring. -/
def pbwPrimitive : UEA ℤ (FreeModel n L) →ₗ[ℤ] FreeModel n L :=
  (SymmetricPower.degreeOneLinearEquiv
      (adaptedBasis n L data hn)).toLinearMap.comp
    (fullRightSymbol n L data hn 1)

theorem fullRightSymbol_pbwMonomial (q : ℕ)
    (e : AdaptedIndex n L data hn →₀ ℕ) (z : ℤ) :
    fullRightSymbol n L data hn q
        ((adaptedWeightedBasis n L data hn).pbwEquiv
          (MvPolynomial.monomial e z)) =
      if he : e.sum (fun _ r ↦ r) = q then
        z • SymmetricPower.monomialBasis (adaptedBasis n L data hn) q
          (exponentSym n L data hn q e he)
      else 0 := by
  classical
  change (SymmetricPower.monomialLinearEquiv
      (adaptedBasis n L data hn) q).symm
    (polynomialFactorCoordinates n L data hn q
      ((adaptedWeightedBasis n L data hn).pbwEquiv.symm
        ((adaptedWeightedBasis n L data hn).pbwEquiv
          (MvPolynomial.monomial e z)))) = _
  rw [LinearEquiv.symm_apply_apply,
    polynomialFactorCoordinates_monomial]
  split <;> rename_i he
  · change (SymmetricPower.monomialLinearEquiv
        (adaptedBasis n L data hn) q).symm
          (Finsupp.single (exponentSym n L data hn q e he) z) =
      z • (SymmetricPower.monomialLinearEquiv
        (adaptedBasis n L data hn) q).symm
          (Finsupp.single (exponentSym n L data hn q e he) 1)
    rw [← map_zsmul]
    congr 1
    simp
  · exact map_zero _

/-- Coordinate expansion of the exact-factor symbol.  This form is used by
the two support arguments below; it keeps the original PBW coefficient
visible instead of hiding it behind the linear equivalence. -/
theorem fullRightSymbol_apply (q : ℕ) (u : UEA ℤ (FreeModel n L)) :
    fullRightSymbol n L data hn q u =
      ((adaptedWeightedBasis n L data hn).pbwEquiv.symm u).sum
        (fun e z ↦ if he : e.sum (fun _ r ↦ r) = q then
          z • SymmetricPower.monomialBasis (adaptedBasis n L data hn) q
            (exponentSym n L data hn q e he)
        else 0) := by
  classical
  let B := adaptedWeightedBasis n L data hn
  let f := B.pbwEquiv.symm u
  have hf : f.sum (fun e z ↦ MvPolynomial.monomial e z) = f := by
    simpa only [MvPolynomial.monomial] using Finsupp.sum_single f
  exact calc
    fullRightSymbol n L data hn q u =
        fullRightSymbol n L data hn q
          (B.pbwEquiv (f.sum (fun e z ↦ MvPolynomial.monomial e z))) := by
            rw [hf, B.pbwEquiv.apply_symm_apply]
    _ = fullRightSymbol n L data hn q
          (f.sum (fun e z ↦ B.pbwEquiv (MvPolynomial.monomial e z))) := by
            congr 1
            rw [map_finsuppSum]
    _ = f.sum (fun e z ↦ fullRightSymbol n L data hn q
          (B.pbwEquiv (MvPolynomial.monomial e z))) := by
            rw [map_finsuppSum]
    _ = _ := by
      apply Finsupp.sum_congr
      intro e he
      rw [fullRightSymbol_pbwMonomial]

/-- Every non-primitive PBW coefficient of a governing expression vanishes
in the weight range controlled by the dimension witness.  Keeping this as a
coefficient statement is what lets the subsequent support arguments use the
actual PBW monomials, without choosing representatives for a symmetric
tensor. -/
theorem GoverningWitness.coeff_theta_eq_zero_of_factor_ne_one {a : L}
    (w : GoverningWitness n L data a)
    (e : AdaptedIndex n L data hn →₀ ℕ)
    (hweight : (adaptedWeightedBasis n L data hn).bracketWeight e ≤ 2 * n)
    (hfactor : LieRings.PBW.WeightedBasis.factorNumber e ≠ 1) :
    (adaptedWeightedBasis n L data hn).coeff e w.theta = 0 := by
  have hproj := congrArg
    ((adaptedWeightedBasis n L data hn).coeff e)
    (GoverningWitness.theta_proj (hn := hn) w
      ((adaptedWeightedBasis n L data hn).bracketWeight e)
      (LieRings.PBW.WeightedBasis.factorNumber e) hweight)
  rw [(adaptedWeightedBasis n L data hn).coeff_proj,
    if_pos ⟨rfl, rfl⟩] at hproj
  rw [if_neg] at hproj
  · simpa only [map_zero] using hproj
  · rintro ⟨_, hf⟩
    exact hfactor hf

/-- A two-factor monomial of bracket weight above `2n` is killed by the
terminal prefix map: at least one of its two factors has weight `n+1`. -/
theorem terminal_map_monomial_eq_zero_of_weight_gt
    (e : AdaptedIndex n L data hn →₀ ℕ)
    (he : LieRings.PBW.WeightedBasis.factorNumber e = 2)
    (hweight : 2 * n <
      (adaptedWeightedBasis n L data hn).bracketWeight e) :
    SymmetricPower.map (R := ℤ) (ι := Fin 2) (prLE n L n (by omega))
        (SymmetricPower.monomialBasis (adaptedBasis n L data hn) 2
          (exponentSym n L data hn 2 e he)) = 0 := by
  classical
  let B := adaptedWeightedBasis n L data hn
  have hhigh : ∃ i ∈ e.support, n < B.weight i := by
    by_contra h
    push_neg at h
    have hle : B.bracketWeight e ≤
        LieRings.PBW.WeightedBasis.factorNumber e * n := by
      unfold LieRings.PBW.WeightedBasis.bracketWeight
        LieRings.PBW.WeightedBasis.factorNumber
      calc
        e.sum (fun i m ↦ m * B.weight i) ≤
            e.sum (fun _ m ↦ m * n) := by
              apply Finsupp.sum_le_sum
              intro i hi
              exact Nat.mul_le_mul_left _ (h i hi)
        _ = e.sum (fun _ m ↦ m) * n := by
              simp only [Finsupp.sum, Finset.sum_mul]
    have hle' : B.bracketWeight e ≤ 2 * n := by
      rw [he] at hle
      exact hle
    have hsame : B.bracketWeight e =
        (adaptedWeightedBasis n L data hn).bracketWeight e := rfl
    rw [hsame] at hle'
    omega
  obtain ⟨i, hi, hiweight⟩ := hhigh
  apply SymmetricPower.map_monomialBasis_eq_zero_of_mem
    (adaptedBasis n L data hn) 2 (prLE n L n (by omega))
    (exponentSym n L data hn 2 e he) i
  · change i ∈ Finsupp.toMultiset e
    exact (Finsupp.mem_toMultiset e i).2 hi
  · rw [adaptedBasis_apply]
    apply FreeMetabelian.Free.projectPrefix_weightIncl_eq_zero
    change n ≤ i.1.val
    change n < i.1.val + 1 at hiweight
    omega

theorem fullRightSymbol_basisWord_sorted
    (xs : List (AdaptedIndex n L data hn))
    (hxs : xs.Pairwise (· ≤ ·)) :
    fullRightSymbol n L data hn xs.length
        (MarkedRow.basisWord n L data hn xs) =
      SymmetricPower.monomialBasis (adaptedBasis n L data hn) xs.length
        (listSym n L data hn xs) := by
  classical
  letI : DecidableEq (AdaptedIndex n L data hn) :=
    LinearOrder.toDecidableEq
  let e : AdaptedIndex n L data hn →₀ ℕ :=
    Multiset.toFinsupp (xs : Multiset (AdaptedIndex n L data hn))
  have hordered : LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
      (AdaptedIndex n L data hn) (adaptedBasis n L data hn) e =
        MarkedRow.basisWord n L data hn xs := by
    change LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
        (AdaptedIndex n L data hn) (adaptedBasis n L data hn) e =
      LieRings.PBW.basisWord ℤ (FreeModel n L)
        (AdaptedIndex n L data hn) (adaptedBasis n L data hn) xs
    exact LieRings.PBW.orderedMonomial_multiset_toFinsupp ℤ
      (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedBasis n L data hn) xs hxs
  have hpbw : (adaptedWeightedBasis n L data hn).pbwEquiv
      (MvPolynomial.monomial e 1) =
        MarkedRow.basisWord n L data hn xs := by
    rw [(adaptedWeightedBasis n L data hn).pbwEquiv_monomial, one_smul]
    change LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
      (AdaptedIndex n L data hn) (adaptedBasis n L data hn) e = _
    exact hordered
  have he : e.sum (fun _ z ↦ z) = xs.length := by
    change (Multiset.toFinsupp
      (xs : Multiset (AdaptedIndex n L data hn))).sum (fun _ z ↦ z) = _
    simpa only [id_eq, Multiset.card_coe] using
      (Multiset.toFinsupp_sum_eq
        (xs : Multiset (AdaptedIndex n L data hn)))
  rw [← hpbw, fullRightSymbol_pbwMonomial]
  rw [dif_pos he]
  simp only [one_smul]
  congr 1
  apply Subtype.ext
  change Finsupp.toMultiset e = (xs : Multiset (AdaptedIndex n L data hn))
  simp [e]

theorem fullRightSymbol_basisWord_sorted_of_lt
    (q : ℕ) (xs : List (AdaptedIndex n L data hn))
    (hxs : xs.Pairwise (· ≤ ·)) (hlen : xs.length < q) :
    fullRightSymbol n L data hn q
        (MarkedRow.basisWord n L data hn xs) = 0 := by
  classical
  letI : DecidableEq (AdaptedIndex n L data hn) :=
    LinearOrder.toDecidableEq
  let e : AdaptedIndex n L data hn →₀ ℕ :=
    Multiset.toFinsupp (xs : Multiset (AdaptedIndex n L data hn))
  have hordered : LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
      (AdaptedIndex n L data hn) (adaptedBasis n L data hn) e =
        MarkedRow.basisWord n L data hn xs := by
    change LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
        (AdaptedIndex n L data hn) (adaptedBasis n L data hn) e =
      LieRings.PBW.basisWord ℤ (FreeModel n L)
        (AdaptedIndex n L data hn) (adaptedBasis n L data hn) xs
    exact LieRings.PBW.orderedMonomial_multiset_toFinsupp ℤ
      (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedBasis n L data hn) xs hxs
  have hpbw : (adaptedWeightedBasis n L data hn).pbwEquiv
      (MvPolynomial.monomial e 1) =
        MarkedRow.basisWord n L data hn xs := by
    rw [(adaptedWeightedBasis n L data hn).pbwEquiv_monomial, one_smul]
    change LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
      (AdaptedIndex n L data hn) (adaptedBasis n L data hn) e = _
    exact hordered
  have he : e.sum (fun _ z ↦ z) = xs.length := by
    change (Multiset.toFinsupp
      (xs : Multiset (AdaptedIndex n L data hn))).sum (fun _ z ↦ z) = _
    simpa only [id_eq, Multiset.card_coe] using
      (Multiset.toFinsupp_sum_eq
        (xs : Multiset (AdaptedIndex n L data hn)))
  rw [← hpbw, fullRightSymbol_pbwMonomial]
  rw [dif_neg (by omega)]

/-- An ordered PBW word has support in exactly its displayed factor number.
This is the equality-strengthened form needed when the terminal component
frontier is split into its one-, two-, and higher-factor parts. -/
theorem fullRightSymbol_basisWord_sorted_of_length_ne
    (q : ℕ) (xs : List (AdaptedIndex n L data hn))
    (hxs : xs.Pairwise (· ≤ ·)) (hlen : xs.length ≠ q) :
    fullRightSymbol n L data hn q
        (MarkedRow.basisWord n L data hn xs) = 0 := by
  classical
  letI : DecidableEq (AdaptedIndex n L data hn) :=
    LinearOrder.toDecidableEq
  let e : AdaptedIndex n L data hn →₀ ℕ :=
    Multiset.toFinsupp (xs : Multiset (AdaptedIndex n L data hn))
  have hordered : LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
      (AdaptedIndex n L data hn) (adaptedBasis n L data hn) e =
        MarkedRow.basisWord n L data hn xs := by
    change LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
        (AdaptedIndex n L data hn) (adaptedBasis n L data hn) e =
      LieRings.PBW.basisWord ℤ (FreeModel n L)
        (AdaptedIndex n L data hn) (adaptedBasis n L data hn) xs
    exact LieRings.PBW.orderedMonomial_multiset_toFinsupp ℤ
      (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedBasis n L data hn) xs hxs
  have hpbw : (adaptedWeightedBasis n L data hn).pbwEquiv
      (MvPolynomial.monomial e 1) =
        MarkedRow.basisWord n L data hn xs := by
    rw [(adaptedWeightedBasis n L data hn).pbwEquiv_monomial, one_smul]
    exact hordered
  have he : e.sum (fun _ z ↦ z) = xs.length := by
    change (Multiset.toFinsupp
      (xs : Multiset (AdaptedIndex n L data hn))).sum (fun _ z ↦ z) = _
    simpa only [id_eq, Multiset.card_coe] using
      (Multiset.toFinsupp_sum_eq
        (xs : Multiset (AdaptedIndex n L data hn)))
  rw [← hpbw, fullRightSymbol_pbwMonomial]
  rw [dif_neg (fun h ↦ hlen (he.symm.trans h))]

/-- A product of fewer than `q` basis primitives has no factor-`q` PBW
symbol, without any ordering hypothesis.  The proof is the literal ordinary
PBW collection: the ordered branch preserves length and every commutator
branch shortens it. -/
theorem fullRightSymbol_basisWord_eq_zero_of_length_lt
    (q : ℕ) (xs : List (AdaptedIndex n L data hn))
    (hlen : xs.length < q) :
    fullRightSymbol n L data hn q
        (MarkedRow.basisWord n L data hn xs) = 0 := by
  classical
  let C := closedSquareCollector n L data hn
  have hall : ∀ r : MarkedRow n L data hn,
      (∀ ys, r = .ordinary ys → ys.length < q →
        fullRightSymbol n L data hn q r.value = 0) := by
    intro r
    induction r using C.wellFounded.induction with
    | h r ih =>
        intro ys hry hys
        subst r
        cases hexpand : closedSquareExpansion n L data hn (.ordinary ys) with
        | none =>
            have hordered : ys.Pairwise (· ≤ ·) := by
              simp only [closedSquareExpansion] at hexpand
              split at hexpand
              · rename_i hnone
                exact
                  (LieRings.DegreeFive.chooseAdjacentInversion?_eq_none_iff_pairwise
                    ys).mp hnone
              · contradiction
            exact fullRightSymbol_basisWord_sorted_of_lt
              n L data hn q ys hordered hys
        | some rows =>
            have hvalue := closedSquareExpansion_preserves
              n L data hn hexpand
            have hexpandC : C.expansion (.ordinary ys) = some rows := by
              change closedSquareExpansion n L data hn (.ordinary ys) = some rows
              exact hexpand
            have hmap := congrArg (fullRightSymbol n L data hn q) hvalue
            rw [map_list_sum] at hmap
            rw [← hmap]
            simp only [List.map_map, Function.comp_apply, map_zsmul]
            apply List.sum_eq_zero
            intro z hz
            simp only [List.mem_map] at hz
            obtain ⟨row, hrow, rfl⟩ := hz
            change fullRightSymbol n L data hn q (row.1 • row.2.value) = 0
            rw [map_zsmul]
            have hshape : ∃ zs, row.2 = .ordinary zs ∧ zs.length < q := by
              simp only [closedSquareExpansion] at hexpand
              split at hexpand
              · contradiction
              · rename_i d hd
                rw [Option.some.injEq] at hexpand
                subst rows
                simp only [List.mem_cons] at hrow
                rcases hrow with rfl | hrow
                · refine ⟨d.left ++ d.y :: d.x :: d.right, rfl, ?_⟩
                  obtain ⟨hys', _⟩ :=
                    LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
                  rw [hys'] at hys
                  simp at hys ⊢
                  omega
                · rw [ordinaryCorrection, List.mem_map] at hrow
                  obtain ⟨t, ht, rfl⟩ := hrow
                  refine ⟨d.left ++ t.2 :: d.right, rfl, ?_⟩
                  obtain ⟨hys', _⟩ :=
                    LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
                  rw [hys'] at hys
                  simp at hys ⊢
                  omega
            obtain ⟨zs, hzs, hzlen⟩ := hshape
            rw [ih row.2 (C.decreases hexpandC row hrow) zs hzs hzlen]
            exact smul_zero _
  change fullRightSymbol n L data hn q
      (MarkedRow.ordinary xs : MarkedRow n L data hn).value = 0
  exact hall (.ordinary xs) xs rfl hlen

/-- The top factor symbol of an arbitrary basis word is its unordered
symmetric monomial.  Adjacent PBW swaps do not change that monomial, and the
commutator corrections vanish by the preceding factor bound. -/
theorem fullRightSymbol_basisWord
    (xs : List (AdaptedIndex n L data hn)) :
    fullRightSymbol n L data hn xs.length
        (MarkedRow.basisWord n L data hn xs) =
      SymmetricPower.monomialBasis (adaptedBasis n L data hn) xs.length
        (listSym n L data hn xs) := by
  classical
  let C := closedSquareCollector n L data hn
  have hall : ∀ r : MarkedRow n L data hn,
      (∀ (q : ℕ) (ys : List (AdaptedIndex n L data hn)),
        r = .ordinary ys → ∀ hlen : ys.length = q,
        fullRightSymbol n L data hn q r.value =
          SymmetricPower.monomialBasis (adaptedBasis n L data hn) q
            (Sym.mk (↑ys : Multiset (AdaptedIndex n L data hn)) hlen)) := by
    intro r
    induction r using C.wellFounded.induction with
    | h r ih =>
        intro q ys hry hlen
        subst r
        cases hexpand : closedSquareExpansion n L data hn (.ordinary ys) with
        | none =>
            have hordered : ys.Pairwise (· ≤ ·) := by
              simp only [closedSquareExpansion] at hexpand
              split at hexpand
              · rename_i hnone
                exact
                  (LieRings.DegreeFive.chooseAdjacentInversion?_eq_none_iff_pairwise
                    ys).mp hnone
              · contradiction
            subst q
            simpa only [MarkedRow.value, listSym] using
              fullRightSymbol_basisWord_sorted n L data hn ys hordered
        | some rows =>
            simp only [closedSquareExpansion] at hexpand
            split at hexpand
            · contradiction
            · rename_i d hd
              rw [Option.some.injEq] at hexpand
              subst rows
              obtain ⟨hys, hyx⟩ :=
                LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
              have hexpand' : C.expansion (.ordinary ys) =
                  some ((1, .ordinary (d.left ++ d.y :: d.x :: d.right)) ::
                    ordinaryCorrection n L data hn d.left d.right d.x d.y) := by
                change closedSquareExpansion n L data hn (.ordinary ys) = _
                simp only [closedSquareExpansion, hd]
              have hmain := ih
                (.ordinary (d.left ++ d.y :: d.x :: d.right))
                (C.decreases hexpand'
                  (1, .ordinary (d.left ++ d.y :: d.x :: d.right))
                  (by simp only [List.mem_cons, true_or]))
                q (d.left ++ d.y :: d.x :: d.right) rfl (by
                  rw [← hlen, hys]
                  simp)
              have hcorr : fullRightSymbol n L data hn q
                  ((ordinaryCorrection n L data hn d.left d.right d.x d.y).map
                    (fun t ↦ t.1 • t.2.value)).sum = 0 := by
                rw [map_list_sum]
                rw [List.map_map]
                apply List.sum_eq_zero
                intro z hz
                simp only [List.mem_map] at hz
                obtain ⟨t, ht, rfl⟩ := hz
                rw [ordinaryCorrection, List.mem_map] at ht
                obtain ⟨s, hs, rfl⟩ := ht
                change fullRightSymbol n L data hn q
                      (s.1 •
                        (MarkedRow.ordinary (d.left ++ s.2 :: d.right) :
                          MarkedRow n L data hn).value) = 0
                rw [map_zsmul]
                change s.1 • fullRightSymbol n L data hn q
                    (MarkedRow.basisWord n L data hn
                      (d.left ++ s.2 :: d.right)) = 0
                rw [fullRightSymbol_basisWord_eq_zero_of_length_lt]
                · exact smul_zero _
                · rw [← hlen, hys]
                  simp
              have hvalue := closedSquareExpansion_preserves
                n L data hn (show
                  closedSquareExpansion n L data hn (.ordinary ys) =
                    some ((1, .ordinary
                      (d.left ++ d.y :: d.x :: d.right)) ::
                        ordinaryCorrection n L data hn
                          d.left d.right d.x d.y) by
                    simp only [closedSquareExpansion, hd])
              subst ys
              change fullRightSymbol n L data hn q
                  (MarkedRow.ordinary
                    (d.left ++ d.x :: d.y :: d.right) :
                      MarkedRow n L data hn).value = _
              rw [← hvalue]
              simp only [List.map_cons, List.sum_cons, one_smul, map_add,
                hmain, hcorr,
                add_zero]
              congr 1
              apply Subtype.ext
              simp only [Multiset.coe_eq_coe]
              exact List.Perm.append_left d.left
                (List.Perm.swap d.x d.y d.right)
  simpa only [MarkedRow.value, listSym] using
    hall (.ordinary xs) xs.length xs rfl rfl

/-- Length-indexed form of `fullRightSymbol_basisWord`, avoiding a
dependent cast when the length is known by a non-definitional equality. -/
theorem fullRightSymbol_basisWord_of_length
    (q : ℕ) (xs : List (AdaptedIndex n L data hn))
    (hlen : xs.length = q) :
    fullRightSymbol n L data hn q
        (MarkedRow.basisWord n L data hn xs) =
      SymmetricPower.monomialBasis (adaptedBasis n L data hn) q
        (Sym.mk (xs : Multiset (AdaptedIndex n L data hn)) hlen) := by
  subst q
  simpa only [listSym] using fullRightSymbol_basisWord n L data hn xs

@[simp] theorem pbwPrimitive_iota (x : FreeModel n L) :
    pbwPrimitive n L data hn (UniversalEnvelopingAlgebra.ι ℤ x) = x := by
  classical
  rw [← (adaptedBasis n L data hn).sum_repr x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  change (SymmetricPower.degreeOneLinearEquiv
      (adaptedBasis n L data hn))
      (fullRightSymbol n L data hn 1
        (UniversalEnvelopingAlgebra.ι ℤ
          ((adaptedWeightedBasis n L data hn).basis i))) =
    (adaptedWeightedBasis n L data hn).basis i
  rw [← (adaptedWeightedBasis n L data hn).pbwEquiv_X i,
    MvPolynomial.X,
    fullRightSymbol_pbwMonomial]
  have he : (Finsupp.single i 1).sum (fun _ r ↦ r) = 1 := by simp
  rw [dif_pos he, one_smul]
  have hs : exponentSym n L data hn 1 (Finsupp.single i 1) he =
      Sym.oneEquiv i := by
    apply Subtype.ext
    simp [exponentSym]
  rw [hs, SymmetricPower.degreeOneLinearEquiv_monomialBasis]
  rfl

/-- The top two-factor symbol of a product of two primitives is their
commutative product.  This is the factor-two local equation used at the
terminal wall. -/
theorem fullRightSymbol_iota_mul_iota_two (x y : FreeModel n L) :
    fullRightSymbol n L data hn 2
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ y) =
      SymmetricPower.insert ℤ (FreeModel n L) 1 x
        (SymmetricPower.degreeOne y) := by
  classical
  let b := adaptedBasis n L data hn
  let lhsX : FreeModel n L →ₗ[ℤ] Sym[ℤ] (Fin 2) (FreeModel n L) := by
    refine
      { toFun := fun x ↦ fullRightSymbol n L data hn 2
          (UniversalEnvelopingAlgebra.ι ℤ x *
            UniversalEnvelopingAlgebra.ι ℤ y)
        map_add' := ?_
        map_smul' := ?_ }
    · intro x z
      rw [map_add, add_mul, map_add]
    · intro r x
      rw [map_zsmul, smul_mul_assoc, map_zsmul]
      rfl
  let rhsX : FreeModel n L →ₗ[ℤ] Sym[ℤ] (Fin 2) (FreeModel n L) :=
    SymmetricPower.insertRight ℤ (FreeModel n L) 1
      (SymmetricPower.degreeOne y)
  suffices lhsX = rhsX by exact DFunLike.congr_fun this x
  apply b.ext
  intro i
  let lhsY : FreeModel n L →ₗ[ℤ] Sym[ℤ] (Fin 2) (FreeModel n L) := by
    refine
      { toFun := fun y ↦ fullRightSymbol n L data hn 2
          (UniversalEnvelopingAlgebra.ι ℤ (b i) *
            UniversalEnvelopingAlgebra.ι ℤ y)
        map_add' := ?_
        map_smul' := ?_ }
    · intro y z
      rw [map_add, mul_add, map_add]
    · intro r y
      rw [map_zsmul, mul_smul_comm, map_zsmul]
      rfl
  let rhsY : FreeModel n L →ₗ[ℤ] Sym[ℤ] (Fin 2) (FreeModel n L) :=
    (SymmetricPower.insert ℤ (FreeModel n L) 1 (b i)).comp
      (SymmetricPower.degreeOne (R := ℤ))
  change lhsY y = rhsY y
  suffices lhsY = rhsY by exact DFunLike.congr_fun this y
  apply b.ext
  intro j
  change fullRightSymbol n L data hn 2
      (UniversalEnvelopingAlgebra.ι ℤ (b i) *
        UniversalEnvelopingAlgebra.ι ℤ (b j)) =
    SymmetricPower.insert ℤ (FreeModel n L) 1 (b i)
      (SymmetricPower.degreeOne (b j))
  have hword := fullRightSymbol_basisWord n L data hn [i, j]
  have hword' : fullRightSymbol n L data hn 2
      (UniversalEnvelopingAlgebra.ι ℤ (b i) *
        UniversalEnvelopingAlgebra.ι ℤ (b j)) =
      SymmetricPower.monomialBasis (adaptedBasis n L data hn) 2
        (listSym n L data hn [i, j]) := by
    simpa only [List.length_cons, List.length_nil, MarkedRow.basisWord,
      b, adaptedWeightedBasis, LieRings.PBW.basisWord,
      LieRings.PBW.word, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one] using hword
  rw [hword', SymmetricPower.degreeOne_apply,
    SymmetricPower.insert_tprod]
  let p : Fin 2 → AdaptedIndex n L data hn := Fin.cons i (fun _ ↦ j)
  have hp : SymmetricPower.symIndexOfFun 2 p = listSym n L data hn [i, j] := by
    apply Subtype.ext
    have hcoe : (SymmetricPower.symIndexOfFun 2 p).val =
        (List.ofFn p : Multiset (AdaptedIndex n L data hn)) :=
      coe_symIndexOfFun 2 p
    rw [hcoe]
    change (List.ofFn p : Multiset (AdaptedIndex n L data hn)) =
      ([i, j] : List (AdaptedIndex n L data hn))
    simp [p]
  rw [monomialBasis_eq_tprod_of_symIndex
    (adaptedBasis n L data hn) 2 (listSym n L data hn [i, j]) p hp]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem pbwPrimitive_eq_zero_of_mem_weightGE
    (u : UEA ℤ (FreeModel n L))
    (hu : u ∈ (adaptedWeightedBasis n L data hn).weightGE (2 * n + 1)) :
    pbwPrimitive n L data hn u = 0 := by
  classical
  rw [pbwPrimitive, LinearMap.comp_apply, fullRightSymbol_apply,
    map_finsuppSum]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro e heSupport
  split_ifs with he
  · obtain ⟨i, rfl⟩ := exponent_eq_single_of_factorNumber_eq_one
      n L data hn e (by
        simpa [LieRings.PBW.WeightedBasis.factorNumber] using he)
    have hcoeff :=
      ((adaptedWeightedBasis n L data hn).mem_weightGE_iff
        (2 * n + 1) u).mp hu (Finsupp.single i 1) (by
          rw [(adaptedWeightedBasis n L data hn).bracketWeight_single]
          simp only [one_mul]
          change (adaptedWeightedBasis n L data hn).weight i < 2 * n + 1
          change i.1.val + 1 < 2 * n + 1
          omega)
    change ((adaptedWeightedBasis n L data hn).pbwEquiv.symm u)
      (Finsupp.single i 1) = 0 at hcoeff
    rw [hcoeff, zero_smul, map_zero]
  · simp

/-- The one-factor PBW primitive of the governing expression is the chosen
homogeneous lift.  This is the literal one-factor part of the governing
equation; the high augmentation word has no possible one-factor monomial in
the truncated free model. -/
theorem GoverningWitness.pbwPrimitive_theta {a : L}
    (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn w.theta =
      FreeMetabelian.Free.weightIncl n (by omega) w.atilde := by
  have hmem : w.highWord ∈
      (adaptedWeightedBasis n L data hn).weightGE (2 * n + 1) := by
    rw [← (adaptedWeightedBasis n L data hn).augmentationIdeal_pow_eq_weightGE]
    exact w.highWord_mem
  have hhigh := pbwPrimitive_eq_zero_of_mem_weightGE
    n L data hn w.highWord hmem
  have heq := congrArg (pbwPrimitive n L data hn) w.theta_sub_iota
  rw [map_sub, pbwPrimitive_iota, map_neg, hhigh] at heq
  apply sub_eq_zero.mp
  simpa using heq

theorem fullRightSymbol_iota_eq_zero_of_one_lt
    (q : ℕ) (hq : 1 < q) (x : FreeModel n L) :
    fullRightSymbol n L data hn q
        (UniversalEnvelopingAlgebra.ι ℤ x) = 0 := by
  classical
  rw [← (adaptedBasis n L data hn).sum_repr x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_eq_zero
  intro i hi
  change ((adaptedBasis n L data hn).repr x) i •
      fullRightSymbol n L data hn q
        (UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i)) = 0
  suffices fullRightSymbol n L data hn q
      (UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i)) = 0 by
    rw [this]
    exact smul_zero _
  change fullRightSymbol n L data hn q
      (UniversalEnvelopingAlgebra.ι ℤ
        ((adaptedWeightedBasis n L data hn).basis i)) = 0
  rw [← (adaptedWeightedBasis n L data hn).pbwEquiv_X i]
  change fullRightSymbol n L data hn q
      ((adaptedWeightedBasis n L data hn).pbwEquiv
        (MvPolynomial.monomial (Finsupp.single i 1) 1)) = 0
  rw [fullRightSymbol_pbwMonomial]
  rw [dif_neg]
  simp
  omega

theorem fullRightSymbol_iota_mul_iota_eq_zero_of_two_lt
    (q : ℕ) (hq : 2 < q) (x y : FreeModel n L) :
    fullRightSymbol n L data hn q
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ y) = 0 := by
  classical
  let b := adaptedBasis n L data hn
  rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_zsmul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul, map_zsmul]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  change ((b.repr x) j * (b.repr y) i) •
      fullRightSymbol n L data hn q
        (UniversalEnvelopingAlgebra.ι ℤ (b j) *
          UniversalEnvelopingAlgebra.ι ℤ (b i)) = 0
  suffices fullRightSymbol n L data hn q
      (UniversalEnvelopingAlgebra.ι ℤ (b j) *
        UniversalEnvelopingAlgebra.ι ℤ (b i)) = 0 by
    rw [this]
    exact smul_zero _
  change fullRightSymbol n L data hn q
      (UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn j) *
        UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i)) = 0
  by_cases hji : j ≤ i
  · simpa [MarkedRow.basisWord, adaptedWeightedBasis,
      LieRings.PBW.basisWord, LieRings.PBW.word] using
      (fullRightSymbol_basisWord_sorted_of_lt n L data hn q [j, i]
        (by simpa using hji) (by simp; omega))
  · have hij : i ≤ j := le_of_not_ge hji
    rw [LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L)
      (b j) (b i), map_add]
    have hsorted := fullRightSymbol_basisWord_sorted_of_lt
      n L data hn q [i, j] (by simpa using hij) (by simp; omega)
    have hsorted' : fullRightSymbol n L data hn q
        (UniversalEnvelopingAlgebra.ι ℤ (b i) *
          UniversalEnvelopingAlgebra.ι ℤ (b j)) = 0 := by
      simpa [MarkedRow.basisWord, b, adaptedWeightedBasis,
        LieRings.PBW.basisWord, LieRings.PBW.word] using hsorted
    rw [hsorted', zero_add]
    exact fullRightSymbol_iota_eq_zero_of_one_lt n L data hn q (by omega)
      ⁅b j, b i⁆

/-- The manuscript's `rightSymbol(q)`, followed by the literal prefix map
`F → A_k`. -/
def rightSymbol (q k : ℕ) (hk : k ≤ n + 1) :
    UEA ℤ (FreeModel n L) →ₗ[ℤ] Sym[ℤ] (Fin q) (A L k) :=
  (SymmetricPower.map (R := ℤ) (ι := Fin q) (prLE n L k hk)).comp
    (fullRightSymbol n L data hn q)

/-- If the nonterminal transgression sees a projected PBW monomial of the
diagonal factor number, then that monomial has exactly manuscript weight
`n+1`.  This is the precise monomial form of the support paragraph in the
manuscript. -/
theorem T_map_exponentMonomial_ne_zero_weight
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (e : AdaptedIndex n L data hn →₀ ℕ)
    (he : LieRings.PBW.WeightedBasis.factorNumber e = n - k + 2)
    (hT : T n L data k hk hkn
      (SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 2))
        (prLE n L k (by omega))
        (SymmetricPower.monomialBasis (adaptedBasis n L data hn)
          (n - k + 2)
          (exponentSym n L data hn (n - k + 2) e he))) ≠ 0) :
    (adaptedWeightedBasis n L data hn).bracketWeight e = n + 1 := by
  classical
  let q := n - k + 2
  let s := exponentSym n L data hn q e he
  let p : Fin q → AdaptedIndex n L data hn :=
    squareSymRepresentative q s
  have hp : SymmetricPower.symIndexOfFun q p = s :=
    symIndexOfFun_squareSymRepresentative q s
  have hp_mem (j : Fin q) : p j ∈ s := by
    rw [← hp]
    exact (SymmetricPower.mem_symIndexOfFun q p (p j)).2 ⟨j, rfl⟩
  have hlt (j : Fin q) : (p j).1.val < k := by
    by_contra hj
    have hkill := SymmetricPower.map_monomialBasis_eq_zero_of_mem
      (adaptedBasis n L data hn) q (prLE n L k (by omega)) s (p j)
      (hp_mem j) (by
        rw [adaptedBasis_apply]
        apply FreeMetabelian.Free.projectPrefix_weightIncl_eq_zero
        exact Nat.le_of_not_gt hj)
    exact hT (by simpa [q, s] using congrArg (T n L data k hk hkn) hkill)
  let degrees : Fin q → Fin k := fun j ↦ ⟨(p j).1.val, hlt j⟩
  let pieces : ∀ j, FreeMetabelian.Piece (Generator L) (degrees j).val :=
    fun j ↦ pieceAdaptedBasis n L data hn (p j).1 (p j).2
  have hprefix (j : Fin q) :
      prLE n L k (by omega) (adaptedBasis n L data hn (p j)) =
        FreeMetabelian.Free.weightIncl (degrees j).val (degrees j).isLt
          (pieces j) := by
    rw [adaptedBasis_apply]
    exact FreeMetabelian.Free.projectPrefix_weightIncl_of_lt
      k (p j).1.val (by omega) (p j).1.isLt (hlt j) _
  have hT' : T n L data k hk hkn
      (SymmetricPower.tprod ℤ (fun j ↦
        FreeMetabelian.Free.weightIncl (degrees j).val (degrees j).isLt
          (pieces j))) ≠ 0 := by
    rw [monomialBasis_eq_tprod_squareSymRepresentative,
      SymmetricPower.map_tprod] at hT
    simpa only [q, s, p, Function.comp_apply, hprefix] using hT
  have hshape := T_homogeneous_ne_zero_shape n L data k hk hkn
    degrees pieces hT'
  obtain ⟨i, hi, _hiunique⟩ := hshape
  have hsum : ∑ j : Fin q,
      (adaptedWeightedBasis n L data hn).weight (p j) = n + 1 := by
    rw [Finset.sum_eq_add_sum_diff_singleton i _ (by simp)]
    have hhead : (adaptedWeightedBasis n L data hn).weight (p i) = k := by
      change (p i).1.val + 1 = k
      have hi' : (p i).1.val = k - 1 := by
        simpa only [degrees] using hi.1
      omega
    rw [hhead]
    have htail : ∑ j ∈ (Finset.univ : Finset (Fin q)) \ {i},
        (adaptedWeightedBasis n L data hn).weight (p j) = q - 1 := by
      calc
        _ = ∑ _j ∈ (Finset.univ : Finset (Fin q)) \ {i}, 1 := by
          apply Finset.sum_congr rfl
          intro j hj
          change (p j).1.val + 1 = 1
          have hjne : j ≠ i := by simpa using hj
          have hjzero : (p j).1.val = 0 := by
            simpa only [degrees] using hi.2 j hjne
          rw [hjzero]
        _ = q - 1 := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [Finset.sdiff_singleton_eq_erase,
            Finset.card_erase_of_mem (by simp)]
          simp
    rw [htail]
    dsimp only [q]
    omega
  rw [bracketWeight_eq_toMultiset_sum]
  have hmult : Finsupp.toMultiset e = (List.ofFn p : Multiset _) := by
    calc
      Finsupp.toMultiset e = (s : Multiset _) := rfl
      _ = (SymmetricPower.symIndexOfFun q p : Multiset _) := by rw [hp]
      _ = (List.ofFn p : Multiset _) := coe_symIndexOfFun q p
  rw [hmult]
  simpa only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn,
    List.sum_ofFn] using hsum

/-- The terminal projected two-factor PBW symbol of a governing expression
is zero.  Low weights vanish coefficientwise by `theta_proj`; high weights
are killed by the terminal prefix map. -/
theorem rightSymbol_theta_terminal_eq_zero {a : L}
    (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega) w.theta = 0 := by
  classical
  rw [rightSymbol, LinearMap.comp_apply, fullRightSymbol_apply,
    map_finsuppSum]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro e heSupport
  split_ifs with he
  · rw [map_zsmul]
    by_cases hweight :
        (adaptedWeightedBasis n L data hn).bracketWeight e ≤ 2 * n
    · have hz := w.coeff_theta_eq_zero_of_factor_ne_one n L data hn e hweight
        (by
          unfold LieRings.PBW.WeightedBasis.factorNumber
          omega)
      change ((adaptedWeightedBasis n L data hn).pbwEquiv.symm w.theta) e = 0
        at hz
      rw [hz]
      exact zero_smul _ _
    · rw [terminal_map_monomial_eq_zero_of_weight_gt n L data hn e
        (by simpa [LieRings.PBW.WeightedBasis.factorNumber] using he)
        (by omega)]
      exact smul_zero _
  · simp

/-- Every nonterminal diagonal transgression reads zero from the governing
PBW expression.  The preceding support theorem forces any visible monomial
to have weight `n+1`, where `theta_proj` kills its (multi-factor)
coefficient. -/
theorem T_rightSymbol_theta_eq_zero {a : L}
    (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    T n L data k hk hkn
      (rightSymbol n L data hn (n - k + 2) k (by omega) w.theta) = 0 := by
  classical
  rw [rightSymbol, LinearMap.comp_apply, fullRightSymbol_apply,
    map_finsuppSum, map_finsuppSum]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro e heSupport
  split_ifs with he
  · rw [map_zsmul, map_zsmul]
    let monomial := SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 2))
      (prLE n L k (by omega))
      (SymmetricPower.monomialBasis (adaptedBasis n L data hn)
        (n - k + 2)
        (exponentSym n L data hn (n - k + 2) e he))
    by_cases hmonomial : T n L data k hk hkn monomial = 0
    · rw [hmonomial, smul_zero]
    · have hweight := T_map_exponentMonomial_ne_zero_weight
        n L data hn k hk hkn e
          (by simpa [LieRings.PBW.WeightedBasis.factorNumber] using he)
          hmonomial
      have hz := w.coeff_theta_eq_zero_of_factor_ne_one n L data hn e
        (by rw [hweight]; omega) (by
          rw [show LieRings.PBW.WeightedBasis.factorNumber e = n - k + 2 by
            simpa [LieRings.PBW.WeightedBasis.factorNumber] using he]
          omega)
      change ((adaptedWeightedBasis n L data hn).pbwEquiv.symm w.theta) e = 0
        at hz
      rw [hz, zero_smul]
  · simp

/-- The transgression read of a factor-`m_k` PBW symbol only depends on its
exact manuscript-weight-`n+1` component.  This is the linear form of the
support calculation above and is useful for the row-by-row closed-square
classification: a homogeneous row of any other total weight is silent. -/
theorem T_rightSymbol_eq_zero_of_proj_eq_zero
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (u : UEA ℤ (FreeModel n L))
    (hu : (adaptedWeightedBasis n L data hn).proj
      (n + 1) (n - k + 2) u = 0) :
    T n L data k hk hkn
      (rightSymbol n L data hn (n - k + 2) k (by omega) u) = 0 := by
  classical
  let B := adaptedWeightedBasis n L data hn
  rw [rightSymbol, LinearMap.comp_apply, fullRightSymbol_apply,
    map_finsuppSum, map_finsuppSum]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro e heSupport
  split_ifs with he
  · rw [map_zsmul, map_zsmul]
    let monomial := SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 2))
      (prLE n L k (by omega))
      (SymmetricPower.monomialBasis (adaptedBasis n L data hn)
        (n - k + 2)
        (exponentSym n L data hn (n - k + 2) e he))
    by_cases hmonomial : T n L data k hk hkn monomial = 0
    · rw [hmonomial, smul_zero]
    · have hweight := T_map_exponentMonomial_ne_zero_weight
        n L data hn k hk hkn e
          (by simpa [LieRings.PBW.WeightedBasis.factorNumber] using he)
          hmonomial
      have hcoeff := congrArg (B.coeff e) hu
      rw [B.coeff_proj, if_pos ⟨hweight, by
        simpa [LieRings.PBW.WeightedBasis.factorNumber] using he⟩,
        map_zero] at hcoeff
      change (B.pbwEquiv.symm u) e = 0 at hcoeff
      rw [hcoeff, zero_smul]
  · simp

/-- A full relation, projected to the actual relation module `D_k`. -/
def fullRelationToD (k : ℕ) (hk : k ≤ n + 1) :
    Relations n L data →ₗ[ℤ] D n L data k hk :=
  LinearMap.codRestrict (D n L data k hk)
    (relationPrefix n L data k hk) (fun rho ↦ ⟨rho, rfl⟩)

/-- Factor-`q+1` degree-one Koszul symbol of the chosen complete relative
chain.  No relation component is split in this definition. -/
def symbolChain {a : L} (w : GoverningWitness n L data a)
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) :
    Koszul.One (presentation n L data k hk hkn) q :=
  w.relationCoefficients.sum (fun p z ↦ z •
    (fullRelationToD n L data k (Nat.le_of_lt hkn) p.1 ⊗ₜ[ℤ]
      rightSymbol n L data hn q k (Nat.le_of_lt hkn) p.2))

@[simp] theorem dOne_symbolChain {a : L}
    (w : GoverningWitness n L data a)
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) :
    Koszul.dOne (presentation n L data k hk hkn) q
        (symbolChain n L data hn w q k hk hkn) =
      w.relationCoefficients.sum (fun p z ↦ z •
        SymmetricPower.insert ℤ (A L k) q
          (relationPrefix n L data k (Nat.le_of_lt hkn) p.1)
          (rightSymbol n L data hn q k (Nat.le_of_lt hkn) p.2)) := by
  classical
  rw [symbolChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  change Koszul.dOne (presentation n L data k hk hkn) q
      (w.relationCoefficients p •
        (fullRelationToD n L data k (Nat.le_of_lt hkn) p.1 ⊗ₜ[ℤ]
          rightSymbol n L data hn q k (Nat.le_of_lt hkn) p.2)) = _
  let r := fullRelationToD n L data k (Nat.le_of_lt hkn) p.1
  let s := rightSymbol n L data hn q k (Nat.le_of_lt hkn) p.2
  let z := w.relationCoefficients p
  change Koszul.dOne (presentation n L data k hk hkn) q
      ((z • r) ⊗ₜ[ℤ] s) =
    z • SymmetricPower.insert ℤ (A L k) q
      (relationPrefix n L data k (Nat.le_of_lt hkn) p.1) s
  have hnatTensor (m : ℕ) : (m • r) ⊗ₜ[ℤ] s =
      m • (r ⊗ₜ[ℤ] s) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [succ_nsmul, succ_nsmul, TensorProduct.add_tmul, ih]
  have hztensor : (z • r) ⊗ₜ[ℤ] s = z • (r ⊗ₜ[ℤ] s) := by
    rcases z with (m | m)
    · simpa only [Int.ofNat_eq_coe, Nat.cast_smul_eq_nsmul ℤ]
        using hnatTensor m
    · rw [show Int.negSucc m = -((m + 1 : ℕ) : ℤ) by omega,
        neg_smul, neg_smul, Nat.cast_smul_eq_nsmul ℤ,
        TensorProduct.neg_tmul]
      congr 1
      simpa only [Nat.cast_smul_eq_nsmul ℤ] using hnatTensor (m + 1)
  calc
    _ = Koszul.dOne (presentation n L data k hk hkn) q
        (z • (r ⊗ₜ[ℤ] s)) := by
          exact congrArg (Koszul.dOne (presentation n L data k hk hkn) q)
            hztensor
    _ = z • Koszul.dOne (presentation n L data k hk hkn) q
        (r ⊗ₜ[ℤ] s) := map_smul _ _ _
    _ = _ := by
      rw [Koszul.dOne_tmul]
      rfl

/-- The symmetric word carried by a truncation cell, after projection to
`A_k`.  The equality argument is only an index transport: the cell itself
stores the literal ordered PBW word. -/
def truncationCellSym (q k : ℕ) (hkn : k < n + 1)
    (c : TruncationCell n L data hn) (hlen : c.left.length = q) :
    Sym[ℤ] (Fin q) (A L k) :=
  SymmetricPower.tprod ℤ (fun i ↦
    prLE n L k (Nat.le_of_lt hkn)
      (adaptedBasis n L data hn
        (c.left.get ⟨i.val, by omega⟩)))

/-- One collected cell as a degree-one Koszul chain.  Cells at other factor
numbers contribute zero. -/
def truncationCellOne (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1)
    (c : TruncationCell n L data hn) :
    Koszul.One (presentation n L data k hk hkn) q :=
  if hlen : c.left.length = q then
    fullRelationToD n L data k (Nat.le_of_lt hkn) c.relation ⊗ₜ[ℤ]
      truncationCellSym n L data hn q k hkn c hlen
  else 0

/-- The complete factor-`q+1` chain at quotient wall `k`, including every
full-relation correction propagated from a higher factor level. -/
def collectedSymbolChain {a : L} (w : GoverningWitness n L data a)
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) :
    Koszul.One (presentation n L data k hk hkn) q :=
  (GoverningWitness.closedSquareCells n L data hn w).sum (fun c z ↦
    if c.bound.val = k then
      z • truncationCellOne n L data hn q k hk hkn c
    else 0)

/-- The diagonal chain used at the `k`th quotient wall.  This is read from
the complete descending-factor trace, rather than from the uncollected
relation-on-the-left expression. -/
def chi {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.One (presentation n L data k (by omega) (by omega))
      (n - k + 1) :=
  collectedSymbolChain n L data (hn := hn) w
    (n - k + 1) k (by omega) (by omega)

/-- The terminal factor-two chain before its cycle proof is attached. -/
def chiTerminalRaw {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  symbolChain n L data hn w 1 n (by omega) (by omega)

/-- One retained factor-two occurrence, with placement forgotten only after
the full relation and the ordinary factor have both been recorded. -/
def terminalFactorChain (c : TerminalFactorTwo n L data hn) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  fullRelationToD n L data n (by omega) c.relation ⊗ₜ[ℤ]
    SymmetricPower.degreeOne
      (prLE n L n (by omega) (adaptedBasis n L data hn c.factor))

/-- The boundary of a retained factor-two row is its literal terminal PBW
symbol.  The right placement gives the same symmetric tensor as the left
placement; no relation component is split here. -/
theorem dOne_terminalFactorChain
    (c : TerminalFactorTwo n L data hn) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (terminalFactorChain n L data hn c) =
      rightSymbol n L data hn 2 n (by omega) c.row.value := by
  classical
  rcases c with ⟨rho, factor, placement⟩
  rw [terminalFactorChain, Koszul.dOne_tmul]
  change SymmetricPower.insert ℤ (A L n) 1
      (relationPrefix n L data n (by omega) rho)
      (SymmetricPower.degreeOne
        (prLE n L n (by omega) (adaptedBasis n L data hn factor))) = _
  cases placement with
  | relationLeft =>
      rw [show (TerminalFactorTwo.row n L data hn
          ⟨rho, factor, .relationLeft⟩).value =
          UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
            UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn factor) by
        simp [TerminalFactorTwo.row, MarkedRow.value,
          MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, rowTruncation_top, adaptedWeightedBasis]]
      rw [rightSymbol, LinearMap.comp_apply,
        fullRightSymbol_iota_mul_iota_two]
      have hmap := LinearMap.congr_fun
        (SymmetricPower.map_insert (R₀ := ℤ)
          (M₀ := FreeModel n L) (N₀ := A L n)
          (prLE n L n (by omega)) 1 (rho : FreeModel n L))
        (SymmetricPower.degreeOne
          (adaptedBasis n L data hn factor))
      calc
        _ = SymmetricPower.insert ℤ (A L n) 1
              (relationPrefix n L data n (by omega) rho)
              (SymmetricPower.map (R := ℤ) (ι := Fin 1)
                (prLE n L n (by omega))
                (SymmetricPower.degreeOne
                  (adaptedBasis n L data hn factor))) := by
            rw [SymmetricPower.map_degreeOne]
        _ = _ := hmap.symm
  | relationRight =>
      rw [show (TerminalFactorTwo.row n L data hn
          ⟨rho, factor, .relationRight⟩).value =
          UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn factor) *
            UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) by
        simp [TerminalFactorTwo.row, MarkedRow.value,
          MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, rowTruncation_top, adaptedWeightedBasis]]
      rw [rightSymbol, LinearMap.comp_apply,
        fullRightSymbol_iota_mul_iota_two]
      have hmap := LinearMap.congr_fun
        (SymmetricPower.map_insert (R₀ := ℤ)
          (M₀ := FreeModel n L) (N₀ := A L n)
          (prLE n L n (by omega)) 1
          (adaptedBasis n L data hn factor))
        (SymmetricPower.degreeOne (rho : FreeModel n L))
      have hcomm := LinearMap.congr_fun
        (SymmetricPower.insert_comm (R₀ := ℤ) (M₀ := A L n) 0
          (prLE n L n (by omega) (adaptedBasis n L data hn factor))
          (relationPrefix n L data n (by omega) rho))
        (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i))
      have hinsertZero (x : A L n) :
          SymmetricPower.insert ℤ (A L n) 0 x
              (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i)) =
            SymmetricPower.degreeOne x := by
        rw [SymmetricPower.degreeOne_apply, SymmetricPower.insert_tprod]
        congr
        funext i
        exact Fin.elim0 i
      change SymmetricPower.insert ℤ (A L n) 1
          (prLE n L n (by omega) (adaptedBasis n L data hn factor))
          (SymmetricPower.insert ℤ (A L n) 0
            (relationPrefix n L data n (by omega) rho)
            (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i))) =
        SymmetricPower.insert ℤ (A L n) 1
          (relationPrefix n L data n (by omega) rho)
          (SymmetricPower.insert ℤ (A L n) 0
            (prLE n L n (by omega) (adaptedBasis n L data hn factor))
            (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i))) at hcomm
      rw [hinsertZero, hinsertZero] at hcomm
      calc
        _ = SymmetricPower.insert ℤ (A L n) 1
              (prLE n L n (by omega) (adaptedBasis n L data hn factor))
              (SymmetricPower.degreeOne
                (relationPrefix n L data n (by omega) rho)) := by
            simpa [LinearMap.comp_apply, SymmetricPower.degreeOne_apply,
              SymmetricPower.insert_tprod] using hcomm.symm
        _ = _ := by
          calc
            _ = SymmetricPower.insert ℤ (A L n) 1
                  (prLE n L n (by omega)
                    (adaptedBasis n L data hn factor))
                  (SymmetricPower.map (R := ℤ) (ι := Fin 1)
                    (prLE n L n (by omega))
                    (SymmetricPower.degreeOne (rho : FreeModel n L))) := by
                rw [SymmetricPower.map_degreeOne]
                rfl
            _ = _ := hmap.symm

theorem fullRightSymbol_terminalFactorTwo_eq_zero_of_two_lt
    (q : ℕ) (hq : 2 < q) (c : TerminalFactorTwo n L data hn) :
    fullRightSymbol n L data hn q c.row.value = 0 := by
  cases c with
  | mk rho v placement =>
      cases placement <;>
        simp only [TerminalFactorTwo.row, MarkedRow.value,
          MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, rowTruncation_top, List.map_singleton,
          List.prod_singleton, List.map_nil, List.prod_nil, one_mul, mul_one]
      · exact fullRightSymbol_iota_mul_iota_eq_zero_of_two_lt
          n L data hn q hq (rho : FreeModel n L)
            ((adaptedWeightedBasis n L data hn).basis v)
      · exact fullRightSymbol_iota_mul_iota_eq_zero_of_two_lt
          n L data hn q hq
            ((adaptedWeightedBasis n L data hn).basis v) (rho : FreeModel n L)

/-- The actual terminal factor-two chain produced after every larger factor
has been collected. -/
def chiTerminalCollected {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (GoverningWitness.closedSquareTerminal n L data hn w).sum
    (fun c z ↦ z • terminalFactorChain n L data hn c)

@[simp] theorem dOne_chiTerminalCollected {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (chiTerminalCollected n L data hn w) =
      (GoverningWitness.closedSquareTerminal n L data hn w).sum
        (fun c z ↦ z • rightSymbol n L data hn 2 n (by omega)
          c.row.value) := by
  classical
  rw [chiTerminalCollected, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, dOne_terminalFactorChain]
  rfl

/-- Rewrite one of the two retained placements as a genuine
relation-on-the-left row list.  In the right placement the correction is the
full relation `[rho,v]`; no homogeneous component is relabelled as a
relation. -/
def terminalFactorRows (c : TerminalFactorTwo n L data hn) :
    (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ :=
  let v := (adaptedWeightedBasis n L data hn).basis c.factor
  match c.placement with
  | .relationLeft =>
      Finsupp.single (c.relation, UniversalEnvelopingAlgebra.ι ℤ v) 1
  | .relationRight =>
      Finsupp.single (c.relation, UniversalEnvelopingAlgebra.ι ℤ v) 1 -
        Finsupp.single
          (relationRightBracket n L data hn c.relation c.factor, 1) 1

theorem terminalPacketWord_terminalFactorRows
    (c : TerminalFactorTwo n L data hn) :
    terminalPacketWord n L data (terminalFactorRows n L data hn c) =
      c.row.value := by
  classical
  cases c with
  | mk rho v placement =>
      cases placement with
      | relationLeft =>
          simp [terminalFactorRows, terminalPacketWord,
            TerminalFactorTwo.row, MarkedRow.value, MarkedRow.basisWord,
            LieRings.PBW.basisWord, LieRings.PBW.word,
            rowTruncation_top, adaptedWeightedBasis]
      | relationRight =>
          unfold terminalFactorRows terminalPacketWord
          rw [Finsupp.sum_sub_index (by
            intro a z₁ z₂
            exact sub_smul z₁ z₂ _)]
          rw [Finsupp.sum_single_index (by simp),
            Finsupp.sum_single_index (by simp)]
          simp only [one_smul, mul_one]
          have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
            (FreeModel n L) (rho : FreeModel n L)
              ((adaptedWeightedBasis n L data hn).basis v)
          simp only [TerminalFactorTwo.row, MarkedRow.value,
            MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, rowTruncation_top, List.map_singleton,
            List.prod_singleton, List.map_nil, List.prod_nil, one_mul, mul_one]
          rw [hswap]
          simp [relationRightBracket]

/-- The relation-on-the-left realization of the whole terminal frontier. -/
def terminalCollectedRows {a : L} (w : GoverningWitness n L data a) :
    (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ :=
  (GoverningWitness.closedSquareTerminal n L data hn w).sum
    (fun c z ↦ z • terminalFactorRows n L data hn c)

theorem terminalPacketWord_terminalCollectedRows {a : L}
    (w : GoverningWitness n L data a) :
    terminalPacketWord n L data (terminalCollectedRows n L data hn w) =
      (GoverningWitness.closedSquareTerminal n L data hn w).sum
        (fun c z ↦ z • c.row.value) := by
  classical
  rw [← terminalPacketWordLinear_apply,
    terminalCollectedRows, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, terminalPacketWordLinear_apply,
    terminalPacketWord_terminalFactorRows]

/-! ## The primitive Stokes account

The normal form forgets which truncation wall produced an ordinary branch.
The following account restores exactly that one piece of provenance.  It is
the algebraic content of the manuscript's vertical edge: an ordinary
terminal primitive is charged to the unique marked truncation at which its
homogeneous relation component was exposed. -/

/-- Primitive read of an ordinary row; marked rows contribute nothing to
this particular account. -/
def ordinaryPrimitiveSeed (r : MarkedRow n L data hn) : FreeModel n L :=
  match r with
  | .ordinary word =>
      pbwPrimitive n L data hn (MarkedRow.basisWord n L data hn word)
  | .marked _ _ _ _ => 0

/-- The genuine homogeneous component exposed by a truncation cell. -/
def TruncationCell.component (c : TruncationCell n L data hn) :
    FreeModel n L :=
  FreeMetabelian.Free.weightIncl (c.bound.val - 1) (by omega)
    (FreeMetabelian.Free.weightProject (c.bound.val - 1) (by omega)
      (c.relation : FreeModel n L))

/-- Literal ordinary word emitted by a truncation cell before its subsequent
PBW ordering. -/
def TruncationCell.componentWord (c : TruncationCell n L data hn) :
    UEA ℤ (FreeModel n L) :=
  MarkedRow.basisWord n L data hn c.left *
    UniversalEnvelopingAlgebra.ι ℤ c.component

/-- One-factor PBW primitive emitted by a truncation cell. -/
def TruncationCell.primitive (c : TruncationCell n L data hn) :
    FreeModel n L :=
  pbwPrimitive n L data hn c.componentWord

/-- Ordinary primitive carried by all terminal leaves below one row. -/
def normalFormOrdinaryPrimitive (r : MarkedRow n L data hn) :
    FreeModel n L :=
  ((closedSquareCollector n L data hn).normalForm r).sum
    (fun s z ↦ z • ordinaryPrimitiveSeed n L data hn s)

/-- Sum of all primitive vertical edges below one row. -/
def tracePrimitive (r : MarkedRow n L data hn) : FreeModel n L :=
  (closedSquareTraceCells n L data hn r).sum
    (fun c z ↦ z • c.primitive)

/-- Linear ordinary-primitive read of a finite row frontier. -/
def ordinaryPrimitiveLinear :
    (MarkedRow n L data hn →₀ ℤ) →ₗ[ℤ] FreeModel n L :=
  Finsupp.linearCombination ℤ (ordinaryPrimitiveSeed n L data hn)

/-- Linear primitive read of the signed truncation-cell trace. -/
def truncationPrimitiveLinear :
    (TruncationCell n L data hn →₀ ℤ) →ₗ[ℤ] FreeModel n L :=
  Finsupp.linearCombination ℤ (fun c ↦ c.primitive)

@[simp] theorem ordinaryPrimitiveLinear_apply
    (x : MarkedRow n L data hn →₀ ℤ) :
    ordinaryPrimitiveLinear n L data hn x =
      x.sum (fun r z ↦ z • ordinaryPrimitiveSeed n L data hn r) := rfl

@[simp] theorem truncationPrimitiveLinear_apply
    (x : TruncationCell n L data hn →₀ ℤ) :
    truncationPrimitiveLinear n L data hn x =
      x.sum (fun c z ↦ z • c.primitive) := rfl

/-- Primitive charged at the present row, if it is a genuine truncation
wall. -/
def truncationPrimitiveSeed (r : MarkedRow n L data hn) : FreeModel n L :=
  match truncationCell? n L data hn r with
  | none => 0
  | some c => c.primitive

/-- Local primitive balance for one deterministic rewrite.  Ordinary swaps
preserve the primitive read, marked swaps have no ordinary primitive edge,
and a truncation step exposes exactly its recorded homogeneous component. -/
theorem closedSquareExpansion_ordinaryPrimitive
    {r : MarkedRow n L data hn}
    {qs : List (ℤ × MarkedRow n L data hn)}
    (h : closedSquareExpansion n L data hn r = some qs) :
    (qs.map (fun q ↦ q.1 • ordinaryPrimitiveSeed n L data hn q.2)).sum =
      ordinaryPrimitiveSeed n L data hn r +
        truncationPrimitiveSeed n L data hn r := by
  classical
  cases r with
  | ordinary word =>
      simp only [closedSquareExpansion] at h
      split at h
      · contradiction
      · rename_i d hd
        rw [Option.some.injEq] at h
        subst qs
        let rows : List (ℤ × MarkedRow n L data hn) :=
          (1, .ordinary (d.left ++ d.y :: d.x :: d.right)) ::
            ordinaryCorrection n L data hn d.left d.right d.x d.y
        have hpres :
            (rows.map (fun q ↦ q.1 • q.2.value)).sum =
              (MarkedRow.ordinary word : MarkedRow n L data hn).value :=
          closedSquareExpansion_preserves n L data hn
            (show closedSquareExpansion n L data hn (.ordinary word) =
                some rows by
              simp only [rows, closedSquareExpansion, hd])
        calc
          (rows.map (fun q ↦ q.1 •
              ordinaryPrimitiveSeed n L data hn q.2)).sum =
              pbwPrimitive n L data hn
                ((rows.map (fun q ↦ q.1 • q.2.value)).sum) := by
            rw [map_list_sum, List.map_map]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            have hordinary : ∃ xs, q.2 = MarkedRow.ordinary xs := by
              simp only [rows, List.mem_cons] at hq
              rcases hq with rfl | hq
              · exact ⟨_, rfl⟩
              · rw [ordinaryCorrection, List.mem_map] at hq
                obtain ⟨s, hs, rfl⟩ := hq
                exact ⟨_, rfl⟩
            rcases q with ⟨z, r⟩
            change ∃ xs, r = MarkedRow.ordinary xs at hordinary
            obtain ⟨xs, rfl⟩ := hordinary
            simp only [Function.comp_apply, ordinaryPrimitiveSeed,
              MarkedRow.value, map_zsmul]
          _ = pbwPrimitive n L data hn
              (MarkedRow.ordinary word : MarkedRow n L data hn).value := by
            rw [hpres]
          _ = ordinaryPrimitiveSeed n L data hn (.ordinary word) +
              truncationPrimitiveSeed n L data hn (.ordinary word) := by
            simp [ordinaryPrimitiveSeed, truncationPrimitiveSeed,
              truncationCell?, MarkedRow.value]
  | marked left rho k right =>
      by_cases hfactorOne : left = [] ∧ right = []
      · simp [closedSquareExpansion, hfactorOne] at h
      by_cases hfactorTwo : left.length + right.length + 1 = 2
      · simp [closedSquareExpansion, hfactorOne, hfactorTwo] at h
      cases right with
      | cons v rest =>
          by_cases htop : k.val = n + 1
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, htop] at h
            rcases h with ⟨_, rfl⟩
            simp [ordinaryPrimitiveSeed, truncationPrimitiveSeed,
              truncationCell?]
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, htop] at h
      | nil =>
          by_cases hk : k.val = 0
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hk] at h
            rcases h with ⟨_, _, rfl⟩
            simp [ordinaryPrimitiveSeed, truncationPrimitiveSeed,
              truncationCell?, hk]
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hk] at h
            rcases h with ⟨_, _, hqs⟩
            rw [← hqs]
            have hthree : 3 ≤ left.length + 1 := by
              have hleft : left ≠ [] := by
                intro hleft
                exact hfactorOne ⟨hleft, rfl⟩
              have hpos : 0 < left.length := Nat.pos_of_ne_zero (by
                intro hzero
                exact hleft (List.eq_nil_of_length_eq_zero hzero))
              omega
            have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
            have hcell : truncationCell? n L data hn
                (.marked left rho k []) =
                some ⟨left, rho, k, hthree, hkpos⟩ := by
              simp [truncationCell?, hthree, hkpos]
            let component : FreeModel n L :=
              FreeMetabelian.Free.weightIncl (k.val - 1) (by omega)
                (FreeMetabelian.Free.weightProject (k.val - 1) (by omega)
                  (rho : FreeModel n L))
            let context : FreeModel n L →ₗ[ℤ] FreeModel n L :=
              (pbwPrimitive n L data hn).comp
                (show FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) from
                  { toFun := fun x ↦ MarkedRow.basisWord n L data hn left *
                      UniversalEnvelopingAlgebra.ι ℤ x
                    map_add' := by intro x y; rw [map_add, mul_add]
                    map_smul' := by
                      intro z x
                      rw [map_zsmul, mul_smul_comm]
                      rfl })
            have hc := congrArg context
              (adaptedCoordinates_sum n L data hn component)
            rw [map_list_sum] at hc
            have hc' :
                ((adaptedCoordinates n L data hn component).map
                    (fun q ↦ q.1 • pbwPrimitive n L data hn
                      (MarkedRow.basisWord n L data hn left *
                        UniversalEnvelopingAlgebra.ι ℤ
                          (adaptedBasis n L data hn q.2)))).sum =
                  pbwPrimitive n L data hn
                    (MarkedRow.basisWord n L data hn left *
                      UniversalEnvelopingAlgebra.ι ℤ component) := by
              calc
                _ = ((adaptedCoordinates n L data hn component).map
                    (fun q ↦ context
                      (q.1 • adaptedBasis n L data hn q.2))).sum := by
                      apply congrArg List.sum
                      apply List.map_congr_left
                      intro q hq
                      rw [map_zsmul]
                      rfl
                _ = context component := by
                      simpa only [List.map_map, Function.comp_apply] using hc
                _ = _ := rfl
            rw [List.map_cons, List.sum_cons, List.map_map]
            simp only [ordinaryPrimitiveSeed, one_smul, zero_add,
              Function.comp_apply, truncationPrimitiveSeed, hcell]
            change
              ((adaptedCoordinates n L data hn component).map
                  (fun q ↦ q.1 • pbwPrimitive n L data hn
                    (MarkedRow.basisWord n L data hn (left ++ [q.2])))).sum =
                pbwPrimitive n L data hn
                  (MarkedRow.basisWord n L data hn left *
                    UniversalEnvelopingAlgebra.ι ℤ component)
            simpa [ordinaryPrimitiveSeed, TruncationCell.primitive,
              TruncationCell.componentWord, TruncationCell.component,
              component, MarkedRow.value, MarkedRow.basisWord,
              LieRings.PBW.basisWord, LieRings.PBW.word,
              List.map_append, adaptedWeightedBasis] using hc'

private theorem truncationCell?_eq_none_of_expansion_eq_none
    (r : MarkedRow n L data hn)
    (h : closedSquareExpansion n L data hn r = none) :
    truncationCell? n L data hn r = none := by
  classical
  cases r with
  | ordinary word => rfl
  | marked left rho k right =>
      cases right with
      | cons v rest => simp [truncationCell?]
      | nil =>
          by_cases hf : 3 ≤ left.length + 1
          · by_cases hk : 0 < k.val
            · have hfactorOne : ¬(left = [] ∧ ([] :
                  List (AdaptedIndex n L data hn)) = []) := by
                intro hzero
                rw [hzero.1] at hf
                simp at hf
              have hfactorTwo : ¬(left.length +
                  ([] : List (AdaptedIndex n L data hn)).length + 1 = 2) := by
                omega
              have hk0 : k.val ≠ 0 := by omega
              simp [closedSquareExpansion, hfactorOne, hfactorTwo, hk0] at h
              have hleft : left ≠ [] := by
                intro hleft
                rw [hleft] at hf
                simp at hf
              have hlen := h hleft
              omega
            · simp [truncationCell?, hf, hk]
          · simp [truncationCell?, hf]

private theorem sum_smul_add_primitive
    (qs : List (ℤ × MarkedRow n L data hn)) :
    (qs.map (fun q ↦ q.1 •
      (ordinaryPrimitiveSeed n L data hn q.2 +
        tracePrimitive n L data hn q.2))).sum =
      (qs.map (fun q ↦ q.1 •
        ordinaryPrimitiveSeed n L data hn q.2)).sum +
      (qs.map (fun q ↦ q.1 •
        tracePrimitive n L data hn q.2)).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons, smul_add]
      simp only [smul_add] at ih
      rw [ih]
      abel

/-- Global primitive Stokes formula for one collected row.  The proof is a
literal induction over the deterministic rewrite tree: the local balance is
applied at its root and all coefficients are propagated to its children. -/
theorem normalFormOrdinaryPrimitive_eq_tracePrimitive
    (r : MarkedRow n L data hn) :
    normalFormOrdinaryPrimitive n L data hn r =
      ordinaryPrimitiveSeed n L data hn r +
        tracePrimitive n L data hn r := by
  classical
  let C := closedSquareCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : closedSquareExpansion n L data hn r with
      | none =>
          have hcell := truncationCell?_eq_none_of_expansion_eq_none
            n L data hn r hexp
          rw [normalFormOrdinaryPrimitive,
            C.normalForm_eq_single_of_terminal hexp,
            tracePrimitive,
            closedSquareTraceCells_eq_of_expansion_none
              n L data hn r hexp]
          simp [ordinaryPrimitiveSeed, hcell]
      | some qs =>
          have hnf :
              normalFormOrdinaryPrimitive n L data hn r =
                (qs.map (fun q ↦ q.1 •
                  normalFormOrdinaryPrimitive n L data hn q.2)).sum := by
            change ordinaryPrimitiveLinear n L data hn (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r qs hexp, map_list_sum]
            simp only [List.map_map, Function.comp_apply]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            change ordinaryPrimitiveLinear n L data hn
              (q.1 • C.normalForm q.2) =
                q.1 • normalFormOrdinaryPrimitive n L data hn q.2
            rw [map_zsmul]
            rfl
          have hhere :
              truncationPrimitiveLinear n L data hn
                  (match truncationCell? n L data hn r with
                    | none => 0
                    | some c => Finsupp.single c 1) =
                truncationPrimitiveSeed n L data hn r := by
            cases hc : truncationCell? n L data hn r <;>
              simp [truncationPrimitiveSeed, hc]
          have htrace :
              tracePrimitive n L data hn r =
                truncationPrimitiveSeed n L data hn r +
                  (qs.map (fun q ↦ q.1 •
                    tracePrimitive n L data hn q.2)).sum := by
            change truncationPrimitiveLinear n L data hn
              (closedSquareTraceCells n L data hn r) = _
            rw [closedSquareTraceCells_eq_of_expansion_some
              n L data hn r qs hexp, map_add, map_list_sum]
            have hchildren :
                ((qs.attach.map fun q ↦ q.1.1 •
                    closedSquareTraceCells n L data hn q.1.2).map
                  (truncationPrimitiveLinear n L data hn)).sum =
                  (qs.attach.map fun q ↦ q.1.1 •
                    tracePrimitive n L data hn q.1.2).sum := by
              apply congrArg List.sum
              rw [List.map_map]
              apply List.map_congr_left
              intro q hq
              change truncationPrimitiveLinear n L data hn
                (q.1.1 • closedSquareTraceCells n L data hn q.1.2) =
                  q.1.1 • tracePrimitive n L data hn q.1.2
              rw [map_zsmul]
              rfl
            calc
              _ = truncationPrimitiveSeed n L data hn r +
                  (qs.attach.map fun q ↦ q.1.1 •
                    tracePrimitive n L data hn q.1.2).sum :=
                congrArg₂ (· + ·) hhere hchildren
              _ = truncationPrimitiveSeed n L data hn r +
                  (qs.map (fun q ↦ q.1 •
                    tracePrimitive n L data hn q.2)).sum := by
                congr 1
                exact congrArg List.sum
                  (List.attach_map_val
                    (l := qs) (f := fun q ↦ q.1 •
                      tracePrimitive n L data hn q.2))
          have hih :
              (qs.map (fun q ↦ q.1 •
                normalFormOrdinaryPrimitive n L data hn q.2)).sum =
                (qs.map (fun q ↦ q.1 •
                  (ordinaryPrimitiveSeed n L data hn q.2 +
                    tracePrimitive n L data hn q.2))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            rw [ih q.2 (C.decreases hexp q hq)]
          have hsplit :
              (qs.map (fun q ↦ q.1 •
                (ordinaryPrimitiveSeed n L data hn q.2 +
                  tracePrimitive n L data hn q.2))).sum =
                (qs.map (fun q ↦ q.1 •
                  ordinaryPrimitiveSeed n L data hn q.2)).sum +
                (qs.map (fun q ↦ q.1 •
                  tracePrimitive n L data hn q.2)).sum := by
            exact sum_smul_add_primitive n L data hn qs
          have hlocal := closedSquareExpansion_ordinaryPrimitive
            n L data hn hexp
          rw [hnf, hih, hsplit, hlocal, htrace]
          abel

/-! ## The same Stokes account in every PBW factor number

The preceding proof used the one-factor projection only through linearity.
For the factor diagonal we need the identical ledger with the exact
factor-`q` PBW symbol as coefficient group.  Keeping this statement separate
avoids rebuilding a second collector or silently discarding the ordinary
commutator branches created below a truncation cell. -/

/-- Exact factor-`q` read of an ordinary row after projection to `A_k`.
Marked rows carry no ordinary read. -/
def ordinaryFactorSeed (q k : ℕ) (hk : k ≤ n + 1)
    (r : MarkedRow n L data hn) : Sym[ℤ] (Fin q) (A L k) :=
  match r with
  | .ordinary word =>
      rightSymbol n L data hn q k hk
        (MarkedRow.basisWord n L data hn word)
  | .marked _ _ _ _ => 0

/-- Exact factor-`q` PBW contribution exposed at one truncation cell. -/
def TruncationCell.factorEdge (q k : ℕ) (hk : k ≤ n + 1)
    (c : TruncationCell n L data hn) : Sym[ℤ] (Fin q) (A L k) :=
  rightSymbol n L data hn q k hk c.componentWord

/-- Factor-`q` ordinary contribution of all terminal leaves below a row. -/
def normalFormOrdinaryFactor (q k : ℕ) (hk : k ≤ n + 1)
    (r : MarkedRow n L data hn) : Sym[ℤ] (Fin q) (A L k) :=
  ((closedSquareCollector n L data hn).normalForm r).sum
    (fun s z ↦ z • ordinaryFactorSeed n L data hn q k hk s)

/-- Factor-`q` contribution of all truncation edges below a row. -/
def traceFactor (q k : ℕ) (hk : k ≤ n + 1)
    (r : MarkedRow n L data hn) : Sym[ℤ] (Fin q) (A L k) :=
  (closedSquareTraceCells n L data hn r).sum
    (fun c z ↦ z • TruncationCell.factorEdge n L data hn q k hk c)

/-- Local factor-symbol balance for one deterministic rewrite. -/
private theorem closedSquareExpansion_ordinaryFactor
    (q k : ℕ) (hk : k ≤ n + 1)
    {r : MarkedRow n L data hn}
    {qs : List (ℤ × MarkedRow n L data hn)}
    (h : closedSquareExpansion n L data hn r = some qs) :
    (qs.map (fun t ↦ t.1 •
      ordinaryFactorSeed n L data hn q k hk t.2)).sum =
      ordinaryFactorSeed n L data hn q k hk r +
        match truncationCell? n L data hn r with
        | none => 0
        | some c => TruncationCell.factorEdge n L data hn q k hk c := by
  classical
  cases r with
  | ordinary word =>
      simp only [closedSquareExpansion] at h
      split at h
      · contradiction
      · rename_i d hd
        rw [Option.some.injEq] at h
        subst qs
        let rows : List (ℤ × MarkedRow n L data hn) :=
          (1, .ordinary (d.left ++ d.y :: d.x :: d.right)) ::
            ordinaryCorrection n L data hn d.left d.right d.x d.y
        have hpres :
            (rows.map (fun t ↦ t.1 • t.2.value)).sum =
              (MarkedRow.ordinary word : MarkedRow n L data hn).value :=
          closedSquareExpansion_preserves n L data hn
            (show closedSquareExpansion n L data hn (.ordinary word) =
                some rows by
              simp only [rows, closedSquareExpansion, hd])
        calc
          (rows.map (fun t ↦ t.1 •
              ordinaryFactorSeed n L data hn q k hk t.2)).sum =
              rightSymbol n L data hn q k hk
                ((rows.map (fun t ↦ t.1 • t.2.value)).sum) := by
            rw [map_list_sum, List.map_map]
            apply congrArg List.sum
            apply List.map_congr_left
            intro t ht
            have hord : ∃ xs, t.2 = MarkedRow.ordinary xs := by
              simp only [rows, List.mem_cons] at ht
              rcases ht with rfl | ht
              · exact ⟨_, rfl⟩
              · rw [ordinaryCorrection, List.mem_map] at ht
                obtain ⟨s, hs, rfl⟩ := ht
                exact ⟨_, rfl⟩
            rcases t with ⟨z, t⟩
            obtain ⟨xs, rfl⟩ := hord
            simp only [Function.comp_apply, ordinaryFactorSeed,
              MarkedRow.value, map_zsmul]
          _ = rightSymbol n L data hn q k hk
              (MarkedRow.ordinary word : MarkedRow n L data hn).value := by
            rw [hpres]
          _ = ordinaryFactorSeed n L data hn q k hk (.ordinary word) +
              match truncationCell? n L data hn (.ordinary word) with
              | none => 0
              | some c => TruncationCell.factorEdge n L data hn q k hk c := by
            simp [ordinaryFactorSeed, truncationCell?, MarkedRow.value]
  | marked left rho b right =>
      by_cases hfactorOne : left = [] ∧ right = []
      · simp [closedSquareExpansion, hfactorOne] at h
      by_cases hfactorTwo : left.length + right.length + 1 = 2
      · simp [closedSquareExpansion, hfactorOne, hfactorTwo] at h
      cases right with
      | cons v rest =>
          by_cases htop : b.val = n + 1
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, htop] at h
            rcases h with ⟨_, rfl⟩
            simp [ordinaryFactorSeed, truncationCell?]
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, htop] at h
      | nil =>
          by_cases hb : b.val = 0
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hb] at h
            rcases h with ⟨_, _, rfl⟩
            simp [ordinaryFactorSeed, truncationCell?, hb]
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hb] at h
            rcases h with ⟨_, _, hqs⟩
            rw [← hqs]
            have hthree : 3 ≤ left.length + 1 := by
              have hleft : left ≠ [] := by
                intro hleft
                exact hfactorOne ⟨hleft, rfl⟩
              have hpos : 0 < left.length := Nat.pos_of_ne_zero (by
                intro hzero
                exact hleft (List.eq_nil_of_length_eq_zero hzero))
              omega
            have hbpos : 0 < b.val := Nat.pos_of_ne_zero hb
            have hcell : truncationCell? n L data hn
                (.marked left rho b []) =
                some ⟨left, rho, b, hthree, hbpos⟩ := by
              simp [truncationCell?, hthree, hbpos]
            let component : FreeModel n L :=
              FreeMetabelian.Free.weightIncl (b.val - 1) (by omega)
                (FreeMetabelian.Free.weightProject (b.val - 1) (by omega)
                  (rho : FreeModel n L))
            let context : FreeModel n L →ₗ[ℤ]
                Sym[ℤ] (Fin q) (A L k) :=
              (rightSymbol n L data hn q k hk).comp
                (show FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) from
                  { toFun := fun x ↦ MarkedRow.basisWord n L data hn left *
                      UniversalEnvelopingAlgebra.ι ℤ x
                    map_add' := by intro x y; rw [map_add, mul_add]
                    map_smul' := by
                      intro z x
                      rw [map_zsmul, mul_smul_comm]
                      rfl })
            have hc := congrArg context
              (adaptedCoordinates_sum n L data hn component)
            rw [map_list_sum] at hc
            have hc' :
                ((adaptedCoordinates n L data hn component).map
                    (fun t ↦ t.1 • rightSymbol n L data hn q k hk
                      (MarkedRow.basisWord n L data hn left *
                        UniversalEnvelopingAlgebra.ι ℤ
                          (adaptedBasis n L data hn t.2)))).sum =
                  rightSymbol n L data hn q k hk
                    (MarkedRow.basisWord n L data hn left *
                      UniversalEnvelopingAlgebra.ι ℤ component) := by
              calc
                _ = ((adaptedCoordinates n L data hn component).map
                    (fun t ↦ context
                      (t.1 • adaptedBasis n L data hn t.2))).sum := by
                      apply congrArg List.sum
                      apply List.map_congr_left
                      intro t ht
                      rw [map_zsmul]
                      rfl
                _ = context component := by
                      simpa only [List.map_map, Function.comp_apply] using hc
                _ = _ := rfl
            rw [List.map_cons, List.sum_cons, List.map_map]
            simp only [ordinaryFactorSeed, one_smul, zero_add,
              Function.comp_apply, hcell]
            change
              ((adaptedCoordinates n L data hn component).map
                  (fun t ↦ t.1 • rightSymbol n L data hn q k hk
                    (MarkedRow.basisWord n L data hn (left ++ [t.2])))).sum =
                TruncationCell.factorEdge n L data hn
                  q k hk ⟨left, rho, b, hthree, hbpos⟩
            simpa [TruncationCell.factorEdge, TruncationCell.componentWord,
              TruncationCell.component, component, MarkedRow.value,
              MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
              using hc'

private theorem sum_smul_add_factor
    (q k : ℕ) (hk : k ≤ n + 1)
    (rows : List (ℤ × MarkedRow n L data hn)) :
    (rows.map (fun t ↦ t.1 •
      (ordinaryFactorSeed n L data hn q k hk t.2 +
        traceFactor n L data hn q k hk t.2))).sum =
      (rows.map (fun t ↦ t.1 •
        ordinaryFactorSeed n L data hn q k hk t.2)).sum +
      (rows.map (fun t ↦ t.1 •
        traceFactor n L data hn q k hk t.2)).sum := by
  induction rows with
  | nil => simp
  | cons t rows ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      module

/-- Global Stokes formula in every exact PBW factor number. -/
theorem normalFormOrdinaryFactor_eq_traceFactor
    (q k : ℕ) (hk : k ≤ n + 1)
    (r : MarkedRow n L data hn) :
    normalFormOrdinaryFactor n L data hn q k hk r =
      ordinaryFactorSeed n L data hn q k hk r +
        traceFactor n L data hn q k hk r := by
  classical
  let C := closedSquareCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : closedSquareExpansion n L data hn r with
      | none =>
          have hcell := truncationCell?_eq_none_of_expansion_eq_none
            n L data hn r hexp
          rw [normalFormOrdinaryFactor,
            C.normalForm_eq_single_of_terminal hexp,
            traceFactor,
            closedSquareTraceCells_eq_of_expansion_none
              n L data hn r hexp]
          simp [ordinaryFactorSeed, hcell]
      | some rows =>
          have hnf :
              normalFormOrdinaryFactor n L data hn q k hk r =
                (rows.map (fun t ↦ t.1 •
                  normalFormOrdinaryFactor n L data hn q k hk t.2)).sum := by
            change Finsupp.linearCombination ℤ
              (ordinaryFactorSeed n L data hn q k hk) (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r rows hexp, map_list_sum]
            simp only [List.map_map, Function.comp_apply]
            apply congrArg List.sum
            apply List.map_congr_left
            intro t ht
            change Finsupp.linearCombination ℤ
                (ordinaryFactorSeed n L data hn q k hk)
                (t.1 • C.normalForm t.2) =
              t.1 • normalFormOrdinaryFactor n L data hn q k hk t.2
            rw [map_zsmul]
            rfl
          have htrace :
              traceFactor n L data hn q k hk r =
                (match truncationCell? n L data hn r with
                  | none => 0
                  | some c =>
                      TruncationCell.factorEdge n L data hn q k hk c) +
                  (rows.map (fun t ↦ t.1 •
                    traceFactor n L data hn q k hk t.2)).sum := by
            change Finsupp.linearCombination ℤ
              (fun c : TruncationCell n L data hn ↦
                TruncationCell.factorEdge n L data hn q k hk c)
                (closedSquareTraceCells n L data hn r) = _
            rw [closedSquareTraceCells_eq_of_expansion_some
              n L data hn r rows hexp, map_add, map_list_sum]
            have hhere : Finsupp.linearCombination ℤ
                (fun c : TruncationCell n L data hn ↦
                  TruncationCell.factorEdge n L data hn q k hk c)
                (match truncationCell? n L data hn r with
                  | none => 0
                  | some c => Finsupp.single c 1) =
                match truncationCell? n L data hn r with
                | none => 0
                | some c =>
                    TruncationCell.factorEdge n L data hn q k hk c := by
              cases hc : truncationCell? n L data hn r with
              | none => simp [hc]
              | some c =>
                  simp only [hc, Finsupp.linearCombination_single]
                  exact one_smul ℤ _
            have hchildren :
                ((rows.attach.map fun t ↦ t.1.1 •
                    closedSquareTraceCells n L data hn t.1.2).map
                  (Finsupp.linearCombination ℤ
                    (fun c : TruncationCell n L data hn ↦
                      TruncationCell.factorEdge n L data hn q k hk c))).sum =
                  (rows.attach.map fun t ↦ t.1.1 •
                    traceFactor n L data hn q k hk t.1.2).sum := by
              apply congrArg List.sum
              rw [List.map_map]
              apply List.map_congr_left
              intro t ht
              change Finsupp.linearCombination ℤ
                  (fun c : TruncationCell n L data hn ↦
                    TruncationCell.factorEdge n L data hn q k hk c)
                  (t.1.1 • closedSquareTraceCells n L data hn t.1.2) =
                t.1.1 • traceFactor n L data hn q k hk t.1.2
              rw [map_zsmul]
              rfl
            calc
              _ = (match truncationCell? n L data hn r with
                    | none => 0
                    | some c =>
                        TruncationCell.factorEdge n L data hn q k hk c) +
                  (rows.attach.map fun t ↦ t.1.1 •
                    traceFactor n L data hn q k hk t.1.2).sum :=
                congrArg₂ (· + ·) hhere hchildren
              _ = (match truncationCell? n L data hn r with
                    | none => 0
                    | some c =>
                        TruncationCell.factorEdge n L data hn q k hk c) +
                  (rows.map (fun t ↦ t.1 •
                    traceFactor n L data hn q k hk t.2)).sum := by
                congr 1
                exact congrArg List.sum
                  (List.attach_map_val
                    (l := rows) (f := fun t ↦ t.1 •
                      traceFactor n L data hn q k hk t.2))
          have hih :
              (rows.map (fun t ↦ t.1 •
                normalFormOrdinaryFactor n L data hn q k hk t.2)).sum =
                (rows.map (fun t ↦ t.1 •
                  (ordinaryFactorSeed n L data hn q k hk t.2 +
                    traceFactor n L data hn q k hk t.2))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro t ht
            rw [ih t.2 (C.decreases hexp t ht)]
          have hsplit := sum_smul_add_factor
            n L data hn q k hk rows
          have hlocal := closedSquareExpansion_ordinaryFactor
            n L data hn q k hk hexp
          rw [hnf, hih, hsplit, hlocal, htrace]
          abel

/-! ### The exact factor-two terminal frontier -/

private def terminalFactorSymbolSeed
    (r : MarkedRow n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  match terminalFactorTwo? n L data hn r with
  | none => 0
  | some c => rightSymbol n L data hn 2 n (by omega) c.row.value

private def terminalFactorSymbolLinear :
    (MarkedRow n L data hn →₀ ℤ) →ₗ[ℤ] Sym[ℤ] (Fin 2) (A L n) :=
  Finsupp.linearCombination ℤ (terminalFactorSymbolSeed n L data hn)

/-- On the actual terminal frontier, the factor-two symbol splits into the
ordinary collected part and the two retained full-relation placements. -/
private theorem GoverningWitness.rightSymbol_closedSquareFrontier {a : L}
    (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega) w.theta =
      Finsupp.linearCombination ℤ
          (ordinaryFactorSeed n L data hn 2 n (by omega))
          (GoverningWitness.closedSquareFrontier n L data hn w) +
        terminalFactorSymbolLinear n L data hn
          (GoverningWitness.closedSquareFrontier n L data hn w) := by
  classical
  have heval := w.evaluate_closedSquareFrontier n L data hn
  have hsymbol := congrArg (rightSymbol n L data hn 2 n (by omega)) heval
  change rightSymbol n L data hn 2 n (by omega)
      ((GoverningWitness.closedSquareFrontier n L data hn w).sum
        (fun r z ↦ z • r.value)) =
      rightSymbol n L data hn 2 n (by omega) w.theta at hsymbol
  rw [map_finsuppSum] at hsymbol
  rw [← hsymbol]
  simp only [map_zsmul, Finsupp.linearCombination_apply,
    terminalFactorSymbolLinear]
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hrSupport
  have hrne := Finsupp.mem_support_iff.mp hrSupport
  have hreach := w.closedSquareFrontier_reachable_of_ne
    n L data hn r hrne
  have hterminal := w.closedSquareFrontier_terminal_of_ne
    n L data hn r hrne
  have hrow : rightSymbol n L data hn 2 n (by omega) r.value =
      ordinaryFactorSeed n L data hn 2 n (by omega) r +
        terminalFactorSymbolSeed n L data hn r := by
    cases r with
    | ordinary word =>
        simp [ordinaryFactorSeed, terminalFactorSymbolSeed,
          terminalFactorTwo?]
        rfl
    | marked left rho k right =>
        rcases reachable_terminal_marked n L data hn left rho k right
            hreach hterminal with hone | htwo
        · rcases hone with ⟨rfl, rfl, hk⟩
          have hmarked : (MarkedRow.marked [] rho k [] :
              MarkedRow n L data hn) =
                .marked [] rho ⟨n + 1, by omega⟩ [] := by
            congr 1
            exact Fin.ext hk
          have hzero : rightSymbol n L data hn 2 n (by omega)
              (MarkedRow.marked [] rho ⟨n + 1, by omega⟩ [] :
                MarkedRow n L data hn).value = 0 := by
            rw [show (MarkedRow.marked [] rho ⟨n + 1, by omega⟩ [] :
                MarkedRow n L data hn).value =
                  UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) by
              simp [MarkedRow.value, MarkedRow.basisWord,
                LieRings.PBW.basisWord, LieRings.PBW.word,
                rowTruncation_top]]
            change SymmetricPower.map (R := ℤ) (ι := Fin 2)
                (prLE n L n (by omega))
                (fullRightSymbol n L data hn 2
                  (UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L))) = 0
            rw [fullRightSymbol_iota_eq_zero_of_one_lt n L data hn 2
              (by omega), map_zero]
          rw [hmarked, hzero]
          simp [ordinaryFactorSeed, terminalFactorSymbolSeed,
            terminalFactorTwo?]
        · obtain ⟨c, hc⟩ := htwo
          have hr : (MarkedRow.marked left rho k right :
              MarkedRow n L data hn) = c.row := hc.symm
          rw [hr]
          rcases c with ⟨rho', factor, placement⟩
          cases placement <;>
            simp [TerminalFactorTwo.row, ordinaryFactorSeed,
              terminalFactorSymbolSeed, terminalFactorTwo?]
  exact calc
    _ = (GoverningWitness.closedSquareFrontier n L data hn w) r •
        rightSymbol n L data hn 2 n (by omega) r.value := rfl
    _ = (GoverningWitness.closedSquareFrontier n L data hn w) r •
        (ordinaryFactorSeed n L data hn 2 n (by omega) r +
          terminalFactorSymbolSeed n L data hn r) := congrArg
            (fun z ↦
              (GoverningWitness.closedSquareFrontier n L data hn w) r • z)
            hrow
    _ = _ := smul_add _ _ _

/-- The terminal-placement read of the frontier is exactly the boundary read
of `chiTerminalCollected`. -/
private theorem GoverningWitness.terminalFactorSymbolFrontier_eq {a : L}
    (w : GoverningWitness n L data a) :
    terminalFactorSymbolLinear n L data hn
        (GoverningWitness.closedSquareFrontier n L data hn w) =
      (GoverningWitness.closedSquareTerminal n L data hn w).sum
        (fun c z ↦ z • rightSymbol n L data hn 2 n (by omega)
          c.row.value) := by
  classical
  rw [GoverningWitness.closedSquareTerminal]
  change terminalFactorSymbolLinear n L data hn
      (GoverningWitness.closedSquareFrontier n L data hn w) =
    Finsupp.linearCombination ℤ
      (fun c ↦ rightSymbol n L data hn 2 n (by omega) c.row.value)
      ((GoverningWitness.closedSquareFrontier n L data hn w).sum
        (fun r z ↦ z • terminalFactorTwoPart n L data hn r))
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul]
  cases hc : terminalFactorTwo? n L data hn r with
  | none =>
      simp [terminalFactorTwoPart, terminalFactorSymbolLinear,
        terminalFactorSymbolSeed, hc]
      module
  | some c =>
      simp [terminalFactorTwoPart, terminalFactorSymbolLinear,
        terminalFactorSymbolSeed, hc]
      module

/-- The complete ordinary factor-two edge emitted by marked truncations. -/
def GoverningWitness.closedSquareFactorDefect {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (GoverningWitness.closedSquareCells n L data hn w).sum
    (fun c z ↦ z • TruncationCell.factorEdge n L data hn 2 n
      (by omega) c)

private theorem GoverningWitness.ordinaryFactorFrontier_eq_defect {a : L}
    (w : GoverningWitness n L data a) :
    Finsupp.linearCombination ℤ
        (ordinaryFactorSeed n L data hn 2 n (by omega))
        (GoverningWitness.closedSquareFrontier n L data hn w) =
      w.closedSquareFactorDefect n L data hn := by
  classical
  change Finsupp.linearCombination ℤ
      (ordinaryFactorSeed n L data hn 2 n (by omega))
      ((GoverningWitness.closedSquareInitial n L data hn w).sum
        (fun r z ↦ z • (closedSquareCollector n L data hn).normalForm r)) =
    Finsupp.linearCombination ℤ
      (TruncationCell.factorEdge n L data hn 2 n (by omega))
      ((GoverningWitness.closedSquareInitial n L data hn w).sum
        (fun r z ↦ z • closedSquareTraceCells n L data hn r))
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul, map_zsmul]
  change (GoverningWitness.closedSquareInitial n L data hn w) r •
      normalFormOrdinaryFactor n L data hn 2 n (by omega) r =
    (GoverningWitness.closedSquareInitial n L data hn w) r •
      traceFactor n L data hn 2 n (by omega) r
  rw [normalFormOrdinaryFactor_eq_traceFactor]
  have hseed : ordinaryFactorSeed n L data hn 2 n (by omega) r = 0 := by
    have hrne := Finsupp.mem_support_iff.mp hr
    rw [GoverningWitness.closedSquareInitial, Finsupp.sum_apply] at hrne
    cases r with
    | ordinary word =>
        exfalso
        apply hrne
        apply Finset.sum_eq_zero
        intro p hp
        change w.relationCoefficients p *
          markedRowsOfRightFactor n L data hn p.1 p.2 (.ordinary word) = 0
        apply mul_eq_zero_of_right
        rw [markedRowsOfRightFactor, Finsupp.sum_apply]
        unfold Finsupp.sum
        apply Finset.sum_eq_zero
        intro e he
        simp
    | marked => rfl
  rw [hseed, zero_add]

/-- The retained factor-two chain has precisely the negative of the complete
ordinary truncation defect as its boundary. -/
theorem GoverningWitness.dOne_chiTerminalCollected_eq_neg_defect {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (chiTerminalCollected n L data hn w) =
      -w.closedSquareFactorDefect n L data hn := by
  have hfront := w.rightSymbol_closedSquareFrontier n L data hn
  rw [rightSymbol_theta_terminal_eq_zero n L data hn w,
    w.ordinaryFactorFrontier_eq_defect n L data hn,
    w.terminalFactorSymbolFrontier_eq n L data hn] at hfront
  rw [dOne_chiTerminalCollected]
  exact eq_neg_of_add_eq_zero_right hfront.symm

/-- Every realized quadratic block has zero terminal coordinate.  This is
the direct combination of the Point 6 PBW computation with the Point 5
pullback certificate; it is kept here because the closed-square output is
exactly such a block. -/
theorem quadraticBlockValue_eq_zero
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    quadraticBlockValue n L data hn c = 0 := by
  letI : Finite (V L n) := Finite.of_surjective
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
      (Submodule.mkQ_surjective _)
  letI : Finite (W L n) := Finite.of_surjective
    (lowerCentralSeries ℤ L n).mkQ (Submodule.mkQ_surjective _)
  apply LieRings.zmodToRatCircle_injective (pow_pos (by decide) _)
  rw [quadraticBlockValue_capstone n L data hn c]
  have hvanish := LinearMap.congr_fun
    (etaTerminal_comp_map_pi_eq_zero n L data hn)
    (quadraticCanonicalClassR n L data hn c)
  have hvanish' : etaTerminal n L data hn
      (Koszul.FirstDerivedSymmetricPower.map 1 (pi L n)
        (quadraticCanonicalClassR n L data hn c)) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hvanish
  rw [hvanish', neg_zero, map_zero]

/-! ## The provenance-preserving primitive Stokes formula

The first marked collector above is useful for the factor-diagonal formulas,
but a factor-lowering correction must retain the full relation which produced
it.  The contextual collector in `MarkedCollector` does exactly that.  The
next theorem is its one-factor Stokes formula.  It is proved directly from the
literal rewrite tree; no confluence or cancellation assertion is used. -/

/-- The primitive carried by the component edge of one contextual cell. -/
def ProvenancedCell.primitive (c : ProvenancedCell n L data hn) :
    FreeModel n L :=
  pbwPrimitive n L data hn c.componentRow.value

/-- Primitive read of a contextual component row.  Marked rows contribute to
the two external walls and therefore do not enter this read. -/
def provenancedComponentPrimitiveSeed
    (r : ProvenancedRow n L data hn) : FreeModel n L :=
  match r with
  | .marked _ _ _ _ _ => 0
  | .component _ _ _ _ _ => pbwPrimitive n L data hn r.value

/-- Component primitive carried by all terminal leaves below one row. -/
def normalFormProvenancedComponentPrimitive
    (r : ProvenancedRow n L data hn) : FreeModel n L :=
  ((provenancedCollector n L data hn).normalForm r).sum
    (fun s z ↦ z • provenancedComponentPrimitiveSeed n L data hn s)

/-- Sum of the primitive component edges at every contextual truncation below
one row. -/
def provenancedTracePrimitive (r : ProvenancedRow n L data hn) :
    FreeModel n L :=
  (provenancedTrace n L data hn r).sum (fun c z ↦ z • c.primitive)

private def provenancedComponentPrimitiveLinear :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ] FreeModel n L :=
  Finsupp.linearCombination ℤ
    (provenancedComponentPrimitiveSeed n L data hn)

private def provenancedCellPrimitiveLinear :
    (ProvenancedCell n L data hn →₀ ℤ) →ₗ[ℤ] FreeModel n L :=
  Finsupp.linearCombination ℤ (fun c ↦ c.primitive)

private def provenancedCellPrimitiveSeed
    (r : ProvenancedRow n L data hn) : FreeModel n L :=
  match provenancedCell? n L data hn r with
  | none => 0
  | some c => c.primitive

private theorem provenancedExpansion_componentPrimitive
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs) :
    (qs.map (fun q ↦ q.1 •
      provenancedComponentPrimitiveSeed n L data hn q.2)).sum =
      provenancedComponentPrimitiveSeed n L data hn r +
        provenancedCellPrimitiveSeed n L data hn r := by
  classical
  cases r with
  | component rho c k left right =>
      simp only [provenancedExpansion] at h
      split at h
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at h
        subst qs
        have hpres := provenancedExpansion_preserves n L data hn
          (show provenancedExpansion n L data hn
              (.component rho c k left right) =
                some [(1, .component rho c k leftRev.reverse (x :: right)),
                  (-1, .component rho (RelationContext.lieRight c x) k
                    leftRev.reverse right)] by
            simp only [provenancedExpansion]
            rw [hleft])
        calc
          _ = pbwPrimitive n L data hn
              (([(1, .component rho c k leftRev.reverse (x :: right)),
                  (-1, .component rho (RelationContext.lieRight c x) k
                    leftRev.reverse right)] :
                List (ℤ × ProvenancedRow n L data hn)).map
                  (fun q ↦ q.1 • q.2.value)).sum := by
              rw [map_list_sum]
              simp [provenancedComponentPrimitiveSeed, map_zsmul]
          _ = pbwPrimitive n L data hn
              (ProvenancedRow.value n L data hn
                (.component rho c k left right)) :=
            congrArg (pbwPrimitive n L data hn) hpres
          _ = _ := by
            simp [provenancedComponentPrimitiveSeed,
              provenancedCellPrimitiveSeed, provenancedCell?]
  | marked rho c k left right =>
      cases right with
      | cons x right =>
          simp only [provenancedExpansion] at h
          rw [Option.some.injEq] at h
          subst qs
          simp [provenancedComponentPrimitiveSeed,
            provenancedCellPrimitiveSeed, provenancedCell?]
      | nil =>
          simp only [provenancedExpansion] at h
          split at h
          · rw [Option.some.injEq] at h
            subst qs
            simp [provenancedComponentPrimitiveSeed,
              provenancedCellPrimitiveSeed, provenancedCell?, *]
          · rename_i hk
            split at h
            · contradiction
            · rename_i hw
              rw [Option.some.injEq] at h
              subst qs
              have hkpos : 0 < k.val := by omega
              have hcell : provenancedCell? n L data hn
                  (.marked rho c k left []) =
                    some ⟨rho, c, k, left, hkpos, by simpa using hw⟩ := by
                simp [provenancedCell?, hkpos, hw]
              simp only [List.map_cons, List.map_singleton, List.sum_cons,
                List.sum_singleton, one_smul,
                provenancedComponentPrimitiveSeed, zero_add,
                provenancedCellPrimitiveSeed, hcell]
              simp [ProvenancedCell.primitive,
                ProvenancedCell.componentRow]

private theorem provenancedCell?_eq_none_of_expansion_eq_none
    (r : ProvenancedRow n L data hn)
    (h : provenancedExpansion n L data hn r = none) :
    provenancedCell? n L data hn r = none := by
  classical
  cases r with
  | component rho c k left right => rfl
  | marked rho c k left right =>
      cases right with
      | cons x right => simp [provenancedCell?]
      | nil =>
          by_cases hk : 0 < k.val
          · by_cases hw : provenancedWall n L data hn c k left = false
            · exfalso
              have hne : provenancedExpansion n L data hn
                  (.marked rho c k left []) ≠ none := by
                simp [provenancedExpansion, Nat.ne_of_gt hk, hw]
              exact hne h
            · simp [provenancedCell?, hk, hw]
          · simp [provenancedCell?, hk]

private theorem sum_smul_add_provenancedPrimitive
    (qs : List (ℤ × ProvenancedRow n L data hn)) :
    (qs.map (fun q ↦ q.1 •
      (provenancedComponentPrimitiveSeed n L data hn q.2 +
        provenancedTracePrimitive n L data hn q.2))).sum =
      (qs.map (fun q ↦ q.1 •
        provenancedComponentPrimitiveSeed n L data hn q.2)).sum +
      (qs.map (fun q ↦ q.1 •
        provenancedTracePrimitive n L data hn q.2)).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons, smul_add]
      simp only [smul_add] at ih
      rw [ih]
      abel

/-- Contextual primitive Stokes formula.  Every component correction is
charged to the unique truncation of the same full relation and context. -/
theorem normalFormProvenancedComponentPrimitive_eq_trace
    (r : ProvenancedRow n L data hn) :
    normalFormProvenancedComponentPrimitive n L data hn r =
      provenancedComponentPrimitiveSeed n L data hn r +
        provenancedTracePrimitive n L data hn r := by
  classical
  let C := provenancedCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : provenancedExpansion n L data hn r with
      | none =>
          have hcell := provenancedCell?_eq_none_of_expansion_eq_none
            n L data hn r hexp
          rw [normalFormProvenancedComponentPrimitive,
            C.normalForm_eq_single_of_terminal hexp,
            provenancedTracePrimitive,
            provenancedTrace_eq_of_expansion_none n L data hn r hexp]
          simp [provenancedComponentPrimitiveSeed, hcell]
      | some qs =>
          have hnf :
              normalFormProvenancedComponentPrimitive n L data hn r =
                (qs.map (fun q ↦ q.1 •
                  normalFormProvenancedComponentPrimitive
                    n L data hn q.2)).sum := by
            change provenancedComponentPrimitiveLinear n L data hn
              (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r qs hexp, map_list_sum]
            simp only [List.map_map, Function.comp_apply]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            change provenancedComponentPrimitiveLinear n L data hn
                (q.1 • C.normalForm q.2) =
              q.1 • normalFormProvenancedComponentPrimitive
                n L data hn q.2
            rw [map_zsmul]
            rfl
          have hhere : provenancedCellPrimitiveLinear n L data hn
                (match provenancedCell? n L data hn r with
                | none => 0
                | some c => Finsupp.single c 1) =
              provenancedCellPrimitiveSeed n L data hn r := by
            cases hc : provenancedCell? n L data hn r <;>
              simp [provenancedCellPrimitiveSeed, hc,
                provenancedCellPrimitiveLinear]
          have htrace :
              provenancedTracePrimitive n L data hn r =
                provenancedCellPrimitiveSeed n L data hn r +
                  (qs.map (fun q ↦ q.1 •
                    provenancedTracePrimitive n L data hn q.2)).sum := by
            change provenancedCellPrimitiveLinear n L data hn
              (provenancedTrace n L data hn r) = _
            rw [provenancedTrace_eq_of_expansion_some
              n L data hn r qs hexp, map_add, map_list_sum]
            have hchildren :
                ((qs.attach.map fun q ↦ q.1.1 •
                    provenancedTrace n L data hn q.1.2).map
                  (provenancedCellPrimitiveLinear n L data hn)).sum =
                  (qs.attach.map fun q ↦ q.1.1 •
                    provenancedTracePrimitive n L data hn q.1.2).sum := by
              apply congrArg List.sum
              rw [List.map_map]
              apply List.map_congr_left
              intro q hq
              change provenancedCellPrimitiveLinear n L data hn
                    (q.1.1 • provenancedTrace n L data hn q.1.2) =
                  q.1.1 • provenancedTracePrimitive n L data hn q.1.2
              rw [map_zsmul]
              rfl
            calc
              _ = provenancedCellPrimitiveSeed n L data hn r +
                  (qs.attach.map fun q ↦ q.1.1 •
                    provenancedTracePrimitive n L data hn q.1.2).sum :=
                congrArg₂ (· + ·) hhere hchildren
              _ = provenancedCellPrimitiveSeed n L data hn r +
                  (qs.map (fun q ↦ q.1 •
                    provenancedTracePrimitive n L data hn q.2)).sum := by
                congr 1
                exact congrArg List.sum
                  (List.attach_map_val (l := qs)
                    (f := fun q ↦ q.1 •
                      provenancedTracePrimitive n L data hn q.2))
          have hih :
              (qs.map (fun q ↦ q.1 •
                normalFormProvenancedComponentPrimitive
                  n L data hn q.2)).sum =
                (qs.map (fun q ↦ q.1 •
                  (provenancedComponentPrimitiveSeed n L data hn q.2 +
                    provenancedTracePrimitive n L data hn q.2))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            rw [ih q.2 (C.decreases hexp q hq)]
          have hsplit := sum_smul_add_provenancedPrimitive
            n L data hn qs
          have hlocal := provenancedExpansion_componentPrimitive
            n L data hn hexp
          rw [hnf, hih, hsplit, hlocal, htrace]
          abel

/-! The same contextual Stokes formula in an exact PBW factor number. -/

def ProvenancedCell.factorEdge (q k : ℕ) (hk : k ≤ n + 1)
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin q) (A L k) :=
  rightSymbol n L data hn q k hk c.componentRow.value

def provenancedComponentFactorSeed (q k : ℕ) (hk : k ≤ n + 1)
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin q) (A L k) :=
  match r with
  | .marked _ _ _ _ _ => 0
  | .component _ _ _ _ _ => rightSymbol n L data hn q k hk r.value

def normalFormProvenancedComponentFactor (q k : ℕ) (hk : k ≤ n + 1)
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin q) (A L k) :=
  ((provenancedCollector n L data hn).normalForm r).sum
    (fun s z ↦ z • provenancedComponentFactorSeed n L data hn q k hk s)

def provenancedTraceFactor (q k : ℕ) (hk : k ≤ n + 1)
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin q) (A L k) :=
  (provenancedTrace n L data hn r).sum
    (fun c z ↦ z • ProvenancedCell.factorEdge n L data hn q k hk c)

private def provenancedComponentFactorLinear (q k : ℕ)
    (hk : k ≤ n + 1) :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin q) (A L k) :=
  Finsupp.linearCombination ℤ
    (provenancedComponentFactorSeed n L data hn q k hk)

private def provenancedCellFactorLinear (q k : ℕ) (hk : k ≤ n + 1) :
    (ProvenancedCell n L data hn →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin q) (A L k) :=
  Finsupp.linearCombination ℤ
    (fun c ↦ ProvenancedCell.factorEdge n L data hn q k hk c)

private def provenancedCellFactorSeed (q k : ℕ) (hk : k ≤ n + 1)
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin q) (A L k) :=
  match provenancedCell? n L data hn r with
  | none => 0
  | some c => ProvenancedCell.factorEdge n L data hn q k hk c

private theorem provenancedExpansion_componentFactor
    (q k₀ : ℕ) (hk₀ : k₀ ≤ n + 1)
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs) :
    (qs.map (fun s ↦ s.1 •
      provenancedComponentFactorSeed n L data hn q k₀ hk₀ s.2)).sum =
      provenancedComponentFactorSeed n L data hn q k₀ hk₀ r +
        provenancedCellFactorSeed n L data hn q k₀ hk₀ r := by
  classical
  cases r with
  | component rho c b left right =>
      simp only [provenancedExpansion] at h
      split at h
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at h
        subst qs
        have hpres := provenancedExpansion_preserves n L data hn
          (show provenancedExpansion n L data hn
              (.component rho c b left right) =
                some [(1, .component rho c b leftRev.reverse (x :: right)),
                  (-1, .component rho (RelationContext.lieRight c x) b
                    leftRev.reverse right)] by
            simp only [provenancedExpansion]
            rw [hleft])
        calc
          _ = rightSymbol n L data hn q k₀ hk₀
              (([(1, .component rho c b leftRev.reverse (x :: right)),
                  (-1, .component rho (RelationContext.lieRight c x) b
                    leftRev.reverse right)] :
                List (ℤ × ProvenancedRow n L data hn)).map
                  (fun s ↦ s.1 • s.2.value)).sum := by
              rw [map_list_sum]
              simp [provenancedComponentFactorSeed, map_zsmul]
          _ = rightSymbol n L data hn q k₀ hk₀
              (ProvenancedRow.value n L data hn
                (.component rho c b left right)) :=
            congrArg (rightSymbol n L data hn q k₀ hk₀) hpres
          _ = _ := by
            simp [provenancedComponentFactorSeed,
              provenancedCellFactorSeed, provenancedCell?]
  | marked rho c b left right =>
      cases right with
      | cons x right =>
          simp only [provenancedExpansion] at h
          rw [Option.some.injEq] at h
          subst qs
          simp [provenancedComponentFactorSeed,
            provenancedCellFactorSeed, provenancedCell?]
      | nil =>
          simp only [provenancedExpansion] at h
          split at h
          · rw [Option.some.injEq] at h
            subst qs
            simp [provenancedComponentFactorSeed,
              provenancedCellFactorSeed, provenancedCell?, *]
          · rename_i hb
            split at h
            · contradiction
            · rename_i hw
              rw [Option.some.injEq] at h
              subst qs
              have hbpos : 0 < b.val := by omega
              have hcell : provenancedCell? n L data hn
                  (.marked rho c b left []) =
                    some ⟨rho, c, b, left, hbpos, by simpa using hw⟩ := by
                simp [provenancedCell?, hbpos, hw]
              simp only [List.map_cons, List.map_singleton, List.sum_cons,
                List.sum_singleton, one_smul,
                provenancedComponentFactorSeed, zero_add,
                provenancedCellFactorSeed, hcell]
              simp [ProvenancedCell.factorEdge,
                ProvenancedCell.componentRow]

private theorem sum_smul_add_provenancedFactor
    (q k : ℕ) (hk : k ≤ n + 1)
    (qs : List (ℤ × ProvenancedRow n L data hn)) :
    (qs.map (fun s ↦ s.1 •
      (provenancedComponentFactorSeed n L data hn q k hk s.2 +
        provenancedTraceFactor n L data hn q k hk s.2))).sum =
      (qs.map (fun s ↦ s.1 •
        provenancedComponentFactorSeed n L data hn q k hk s.2)).sum +
      (qs.map (fun s ↦ s.1 •
        provenancedTraceFactor n L data hn q k hk s.2)).sum := by
  induction qs with
  | nil => simp
  | cons s qs ih =>
      simp only [List.map_cons, List.sum_cons, smul_add]
      simp only [smul_add] at ih
      rw [ih]
      module

/-- Contextual Stokes formula in every exact PBW factor number. -/
theorem normalFormProvenancedComponentFactor_eq_trace
    (q k : ℕ) (hk : k ≤ n + 1)
    (r : ProvenancedRow n L data hn) :
    normalFormProvenancedComponentFactor n L data hn q k hk r =
      provenancedComponentFactorSeed n L data hn q k hk r +
        provenancedTraceFactor n L data hn q k hk r := by
  classical
  let C := provenancedCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : provenancedExpansion n L data hn r with
      | none =>
          have hcell := provenancedCell?_eq_none_of_expansion_eq_none
            n L data hn r hexp
          rw [normalFormProvenancedComponentFactor,
            C.normalForm_eq_single_of_terminal hexp,
            provenancedTraceFactor,
            provenancedTrace_eq_of_expansion_none n L data hn r hexp]
          simp [provenancedComponentFactorSeed, hcell]
      | some qs =>
          have hnf :
              normalFormProvenancedComponentFactor n L data hn q k hk r =
                (qs.map (fun s ↦ s.1 •
                  normalFormProvenancedComponentFactor
                    n L data hn q k hk s.2)).sum := by
            change provenancedComponentFactorLinear n L data hn q k hk
              (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r qs hexp, map_list_sum]
            simp only [List.map_map, Function.comp_apply]
            apply congrArg List.sum
            apply List.map_congr_left
            intro s hs
            change provenancedComponentFactorLinear n L data hn q k hk
                (s.1 • C.normalForm s.2) =
              s.1 • normalFormProvenancedComponentFactor
                n L data hn q k hk s.2
            rw [map_zsmul]
            rfl
          have hhere : provenancedCellFactorLinear n L data hn q k hk
                (match provenancedCell? n L data hn r with
                | none => 0
                | some c => Finsupp.single c 1) =
              provenancedCellFactorSeed n L data hn q k hk r := by
            cases hc : provenancedCell? n L data hn r with
            | none =>
                simp [provenancedCellFactorSeed, hc,
                  provenancedCellFactorLinear]
            | some c =>
                simp only [provenancedCellFactorSeed, hc,
                  provenancedCellFactorLinear,
                  Finsupp.linearCombination_single]
                module
          have htrace :
              provenancedTraceFactor n L data hn q k hk r =
                provenancedCellFactorSeed n L data hn q k hk r +
                  (qs.map (fun s ↦ s.1 •
                    provenancedTraceFactor n L data hn q k hk s.2)).sum := by
            change provenancedCellFactorLinear n L data hn q k hk
              (provenancedTrace n L data hn r) = _
            rw [provenancedTrace_eq_of_expansion_some
              n L data hn r qs hexp, map_add, map_list_sum]
            have hchildren :
                ((qs.attach.map fun s ↦ s.1.1 •
                    provenancedTrace n L data hn s.1.2).map
                  (provenancedCellFactorLinear n L data hn q k hk)).sum =
                  (qs.attach.map fun s ↦ s.1.1 •
                    provenancedTraceFactor n L data hn q k hk s.1.2).sum := by
              apply congrArg List.sum
              rw [List.map_map]
              apply List.map_congr_left
              intro s hs
              change provenancedCellFactorLinear n L data hn q k hk
                    (s.1.1 • provenancedTrace n L data hn s.1.2) =
                  s.1.1 • provenancedTraceFactor
                    n L data hn q k hk s.1.2
              rw [map_zsmul]
              rfl
            calc
              _ = provenancedCellFactorSeed n L data hn q k hk r +
                  (qs.attach.map fun s ↦ s.1.1 •
                    provenancedTraceFactor n L data hn q k hk s.1.2).sum :=
                congrArg₂ (· + ·) hhere hchildren
              _ = provenancedCellFactorSeed n L data hn q k hk r +
                  (qs.map (fun s ↦ s.1 •
                    provenancedTraceFactor n L data hn q k hk s.2)).sum := by
                congr 1
                exact congrArg List.sum
                  (List.attach_map_val (l := qs)
                    (f := fun s ↦ s.1 •
                      provenancedTraceFactor n L data hn q k hk s.2))
          have hih :
              (qs.map (fun s ↦ s.1 •
                normalFormProvenancedComponentFactor
                  n L data hn q k hk s.2)).sum =
                (qs.map (fun s ↦ s.1 •
                  (provenancedComponentFactorSeed
                      n L data hn q k hk s.2 +
                    provenancedTraceFactor n L data hn q k hk s.2))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro s hs
            rw [ih s.2 (C.decreases hexp s hs)]
          have hsplit := sum_smul_add_provenancedFactor
            n L data hn q k hk qs
          have hlocal := provenancedExpansion_componentFactor
            n L data hn q k hk hexp
          rw [hnf, hih, hsplit, hlocal, htrace]
          module

/-! ## Contextual diagonal Koszul rows -/

/-- The top-factor PBW symbol of a literal basis word followed by one
arbitrary primitive is its symmetric product.  No ordering hypothesis is
needed: commutator corrections have one fewer factor. -/
theorem rightSymbol_basisWord_mul_iota
    (k : ℕ) (hk : k ≤ n + 1)
    (left : List (AdaptedIndex n L data hn)) (x : FreeModel n L) :
    rightSymbol n L data hn (left.length + 1) k hk
        (MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ x) =
      SymmetricPower.insert ℤ (A L k) left.length
        (prLE n L k hk x)
        (SymmetricPower.tprod ℤ (fun j : Fin left.length ↦
          prLE n L k hk
            (adaptedBasis n L data hn (left.get j)))) := by
  classical
  let word := MarkedRow.basisWord n L data hn left
  let symLeft := SymmetricPower.tprod ℤ (fun j : Fin left.length ↦
    prLE n L k hk (adaptedBasis n L data hn (left.get j)))
  let lhs : FreeModel n L →ₗ[ℤ] Sym[ℤ] (Fin (left.length + 1)) (A L k) :=
    (rightSymbol n L data hn (left.length + 1) k hk).comp
      (show FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) from
      { toFun := fun z ↦ word * UniversalEnvelopingAlgebra.ι ℤ z
        map_add' := by intro z w; rw [map_add, mul_add]
        map_smul' := by
          intro z w
          rw [map_zsmul, mul_smul_comm]
          rfl })
  let rhs : FreeModel n L →ₗ[ℤ] Sym[ℤ] (Fin (left.length + 1)) (A L k) :=
    (SymmetricPower.insertRight ℤ (A L k) left.length symLeft).comp
      (prLE n L k hk)
  change lhs x = rhs x
  rw [← (adaptedBasis n L data hn).sum_repr x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul, map_zsmul]
  congr 1
  change rightSymbol n L data hn (left.length + 1) k hk
      (MarkedRow.basisWord n L data hn left *
        UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn i)) =
    SymmetricPower.insert ℤ (A L k) left.length
      (prLE n L k hk (adaptedBasis n L data hn i)) symLeft
  have hword : MarkedRow.basisWord n L data hn left *
      UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) =
        MarkedRow.basisWord n L data hn (left ++ [i]) := by
    simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
  rw [hword, rightSymbol, LinearMap.comp_apply]
  let xs := left ++ [i]
  let s : Sym (AdaptedIndex n L data hn) (left.length + 1) :=
    Sym.mk (xs : Multiset (AdaptedIndex n L data hn)) (by simp [xs])
  have hfull : fullRightSymbol n L data hn (left.length + 1)
      (MarkedRow.basisWord n L data hn xs) =
        SymmetricPower.monomialBasis (adaptedBasis n L data hn)
          (left.length + 1) s := by
    exact fullRightSymbol_basisWord_of_length n L data hn
      (left.length + 1) xs (by simp [xs])
  rw [hfull]
  let p : Fin (left.length + 1) → AdaptedIndex n L data hn := fun j ↦
    xs.get ⟨j.val, by simpa [xs] using j.isLt⟩
  have hp : SymmetricPower.symIndexOfFun (left.length + 1) p = s := by
    apply Sym.ext
    rw [coe_symIndexOfFun]
    change (List.ofFn p : Multiset (AdaptedIndex n L data hn)) =
      (xs : List (AdaptedIndex n L data hn))
    rw [show List.ofFn p = xs by
      apply List.ext_get
      · simp [xs]
      · intro j hj₁ hj₂
        simp only [List.get_ofFn]
        rfl]
  rw [monomialBasis_eq_tprod_of_symIndex
    (adaptedBasis n L data hn) (left.length + 1) s p hp,
    SymmetricPower.map_tprod, SymmetricPower.insert_tprod]
  change SymmetricPower.tprod ℤ
      (fun j : Fin (left.length + 1) ↦
        prLE n L k hk
          (adaptedBasis n L data hn (p j))) =
    SymmetricPower.tprod ℤ (Fin.cons
      (prLE n L k hk (adaptedBasis n L data hn i))
      (fun j : Fin left.length ↦
        prLE n L k hk (adaptedBasis n L data hn (left.get j))))
  let y : Fin left.length → A L k := fun j ↦
    prLE n L k hk (adaptedBasis n L data hn (left.get j))
  let z : A L k := prLE n L k hk (adaptedBasis n L data hn i)
  have hsnoc : (fun j : Fin (left.length + 1) ↦
      prLE n L k hk
        (adaptedBasis n L data hn (p j))) =
      Fin.snoc y z := by
    funext j
    by_cases hj : j.val < left.length
    · simp [Fin.snoc, y, p, xs, hj]
      rfl
    · have hjlast : j = Fin.last left.length := by
        apply Fin.ext
        exact Nat.eq_of_lt_succ_of_not_lt j.isLt hj
      subst j
      simp [Fin.snoc, z, p, xs]
  rw [hsnoc, Fin.snoc_eq_cons_rotate]
  exact SymmetricPower.tprod_equiv (finRotate (left.length + 1))
    (Fin.cons z y)

/-! ### The diagonal read of a contextual trace -/

/-- The active manuscript weight of a contextual truncation cell. -/
def ProvenancedCell.activeWeight (c : ProvenancedCell n L data hn) : ℕ :=
  c.mark.val + RelationContext.weight n L data hn c.context

/-- The symmetric word to the left of a contextual mark. -/
def ProvenancedCell.sym (q k : ℕ) (hk : k ≤ n + 1)
    (c : ProvenancedCell n L data hn) (hlen : c.left.length = q) :
    Sym[ℤ] (Fin q) (A L k) :=
  SymmetricPower.tprod ℤ (fun j : Fin q ↦
    prLE n L k hk (adaptedBasis n L data hn
      (c.left.get ⟨j.val, by omega⟩)))

/-- A cell on the `(q+1,k)` diagonal, regarded as a genuine degree-one
Koszul row.  Its relation entry is the projection of the *full contextual
relation*; the exposed component is never coerced to `D_k`. -/
def ProvenancedCell.one (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1)
    (c : ProvenancedCell n L data hn) :
    Koszul.One (presentation n L data k hk hkn) q :=
  if hlen : c.left.length = q then
    if hactive : c.activeWeight n L data hn = k then
      fullRelationToD n L data k (Nat.le_of_lt hkn)
          (RelationContext.relation n L data hn c.context c.root) ⊗ₜ[ℤ]
        c.sym n L data hn q k (Nat.le_of_lt hkn) hlen
    else 0
  else 0

/-- The complete chain on one diagonal of the contextual trace. -/
def contextualSymbolChain {a : L} (w : GoverningWitness n L data a)
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) :
    Koszul.One (presentation n L data k hk hkn) q :=
  (GoverningWitness.provenancedCells n L data hn w).sum (fun c z ↦
    z • c.one n L data hn q k hk hkn)

/-- On a diagonal cell the Koszul boundary is literally the projected
top-factor symbol of its marked prefix. -/
theorem ProvenancedCell.dOne_one
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1)
    (c : ProvenancedCell n L data hn) :
    Koszul.dOne (presentation n L data k hk hkn) q
        (c.one n L data hn q k hk hkn) =
      if hlen : c.left.length = q then
        if hactive : c.activeWeight n L data hn = k then
          rightSymbol n L data hn (q + 1) k (Nat.le_of_lt hkn)
            c.markedRow.value
        else 0
      else 0 := by
  classical
  unfold ProvenancedCell.one
  split_ifs with hlen hactive
  · subst q
    rw [Koszul.dOne_tmul]
    have hprefix := RelationContext.projectPrefix_relation_eq_markedPrefix_of_active
      n L data hn k (Nat.le_of_lt hkn) c.context c.root c.mark
      (by simpa [ProvenancedCell.activeWeight] using hactive)
    change SymmetricPower.insert ℤ (A L k) c.left.length
        (relationPrefix n L data k (Nat.le_of_lt hkn)
          (RelationContext.relation n L data hn c.context c.root))
        (c.sym n L data hn c.left.length k (Nat.le_of_lt hkn) rfl) = _
    have hsymbol := rightSymbol_basisWord_mul_iota n L data hn k
      (Nat.le_of_lt hkn) c.left
      (RelationContext.markedPrefix n L data hn c.context c.root c.mark)
    have hvalue : c.markedRow.value =
        (MarkedRow.basisWord n L data hn c.left *
          UniversalEnvelopingAlgebra.ι ℤ
            (RelationContext.markedPrefix n L data hn c.context c.root c.mark)) := by
      simp [ProvenancedCell.markedRow, ProvenancedRow.value,
        MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word]
    rw [hvalue, hsymbol]
    have hprefix' : relationPrefix n L data k (Nat.le_of_lt hkn)
          (RelationContext.relation n L data hn c.context c.root) =
        prLE n L k (Nat.le_of_lt hkn)
          (RelationContext.markedPrefix n L data hn c.context c.root c.mark) :=
      hprefix
    rw [hprefix']
    unfold ProvenancedCell.sym
    rfl
  all_goals rfl

@[simp] theorem dOne_contextualSymbolChain {a : L}
    (w : GoverningWitness n L data a)
    (q k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) :
    Koszul.dOne (presentation n L data k hk hkn) q
        (contextualSymbolChain n L data hn w q k hk hkn) =
      (GoverningWitness.provenancedCells n L data hn w).sum (fun c z ↦
        z • if hlen : c.left.length = q then
          if hactive : c.activeWeight n L data hn = k then
            rightSymbol n L data hn (q + 1) k (Nat.le_of_lt hkn)
              c.markedRow.value
          else 0
        else 0) := by
  classical
  rw [contextualSymbolChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, ProvenancedCell.dOne_one]
  rfl

/-- A contextual homogeneous component starts in its active manuscript
weight.  Hence every smaller prefix projection kills it. -/
theorem RelationContext.prLE_component_eq_zero_of_lt
    (k : ℕ) (hk : k ≤ n + 1)
    (c : RelationContext n L data hn) (rho : Relations n L data)
    (b : Fin (n + 2))
    (hkb : k < b.val + RelationContext.weight n L data hn c) :
    prLE n L k hk (RelationContext.component n L data hn c rho b) = 0 := by
  classical
  by_cases hb : b.val = 0
  · rw [RelationContext.component_zero n L data hn c rho b hb, map_zero]
  · have hb_pos : 0 < b.val := Nat.pos_of_ne_zero hb
    have hb_lt : b.val < n + 2 := b.isLt
    have hb_bound : b.val - 1 < n + 1 := by omega
    have hbase : FreeMetabelian.Free.weightIncl (b.val - 1) hb_bound
        (FreeMetabelian.Free.weightProject (b.val - 1) hb_bound rho.1) ∈
        FreeMetabelian.Free.tail (b.val - 1) := by
      rw [FreeMetabelian.Free.mem_tail_iff]
      intro i hi
      change FreeMetabelian.Free.incl
        (⟨b.val - 1, hb_bound⟩ : Fin (n + 1)) _ i = 0
      apply FreeMetabelian.Free.incl_apply_of_ne
      intro hieq
      have hval := congrArg Fin.val hieq
      have hval' : i.val = b.val - 1 := by simpa using hval
      omega
    have htail := RelationContext.apply_mem_tail n L data hn c _
      (b.val - 1) hbase
    have htail' : RelationContext.component n L data hn c rho b ∈
        FreeMetabelian.Free.tail
          (b.val - 1 + RelationContext.weight n L data hn c) := by
      simpa [RelationContext.component, hb] using htail
    funext i
    have hi_lt : i.val < k := i.isLt
    change RelationContext.component n L data hn c rho b
      ⟨i.val, i.isLt.trans_le hk⟩ = 0
    apply htail' ⟨i.val, i.isLt.trans_le hk⟩
    change i.val < b.val - 1 + RelationContext.weight n L data hn c
    omega

/-- A word containing `r` displayed primitive factors has no PBW symbol in a
strictly larger factor number. -/
theorem fullRightSymbol_basisWord_mul_iota_mul_basisWord_eq_zero_of_lt
    (p : ℕ) (left right : List (AdaptedIndex n L data hn))
    (x : FreeModel n L)
    (hlt : left.length + right.length + 1 < p) :
    fullRightSymbol n L data hn p
      (MarkedRow.basisWord n L data hn left *
        UniversalEnvelopingAlgebra.ι ℤ x *
        MarkedRow.basisWord n L data hn right) = 0 := by
  classical
  let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    { toFun := fun y ↦ MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ y *
          MarkedRow.basisWord n L data hn right
      map_add' := by intro y z; rw [map_add, mul_add, add_mul]
      map_smul' := by
        intro z y
        rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
        rfl }
  change fullRightSymbol n L data hn p (context x) = 0
  rw [← (adaptedBasis n L data hn).sum_repr x, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_zsmul, map_zsmul]
  have hword : MarkedRow.basisWord n L data hn left *
        UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) *
        MarkedRow.basisWord n L data hn right =
      MarkedRow.basisWord n L data hn (left ++ [i] ++ right) := by
    simp [MarkedRow.basisWord,
      LieRings.PBW.basisWord, LieRings.PBW.word, List.map_append,
      adaptedWeightedBasis]
    noncomm_ring
  change ((adaptedBasis n L data hn).repr x) i •
      fullRightSymbol n L data hn p
        (MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) *
          MarkedRow.basisWord n L data hn right) = 0
  rw [hword]
  rw [fullRightSymbol_basisWord_eq_zero_of_length_lt n L data hn
    p (left ++ [i] ++ right) (by simpa using hlt)]
  exact smul_zero _

/-- Literal number of displayed primitive factors in a contextual row. -/
def ProvenancedRow.factorCount : ProvenancedRow n L data hn → ℕ
  | .marked _ _ _ left right | .component _ _ _ left right =>
      left.length + right.length + 1

theorem rightSymbol_provenancedRow_eq_zero_of_factorCount_lt
    (p k : ℕ) (hk : k ≤ n + 1) (r : ProvenancedRow n L data hn)
    (hr : r.factorCount n L data hn < p) :
    rightSymbol n L data hn p k hk r.value = 0 := by
  cases r with
  | marked root context mark left right =>
      change SymmetricPower.map (R := ℤ) (ι := Fin p) (prLE n L k hk)
        (fullRightSymbol n L data hn p
          (MarkedRow.basisWord n L data hn left *
            UniversalEnvelopingAlgebra.ι ℤ
              (RelationContext.markedPrefix n L data hn context root mark) *
            MarkedRow.basisWord n L data hn right)) = 0
      rw [fullRightSymbol_basisWord_mul_iota_mul_basisWord_eq_zero_of_lt
        n L data hn p left right _ hr, map_zero]
  | component root context mark left right =>
      change SymmetricPower.map (R := ℤ) (ι := Fin p) (prLE n L k hk)
        (fullRightSymbol n L data hn p
          (MarkedRow.basisWord n L data hn left *
            UniversalEnvelopingAlgebra.ι ℤ
              (RelationContext.component n L data hn context root mark) *
            MarkedRow.basisWord n L data hn right)) = 0
      rw [fullRightSymbol_basisWord_mul_iota_mul_basisWord_eq_zero_of_lt
        n L data hn p left right _ hr, map_zero]

/-- Every contextual rewrite weakly decreases the displayed factor count. -/
theorem provenancedExpansion_factorCount_le
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs) :
    ∀ s ∈ qs, s.2.factorCount n L data hn ≤ r.factorCount n L data hn := by
  classical
  intro s hs
  cases r with
  | component rho c b left right =>
      simp only [provenancedExpansion] at h
      split at h
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at h
        subst qs
        have hleftEq : left = leftRev.reverse ++ [x] := by
          have hr := congrArg List.reverse hleft
          simpa using hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl <;>
          simp [ProvenancedRow.factorCount, hleftEq] <;> omega
  | marked rho c b left right =>
      cases right with
      | cons x right =>
          simp only [provenancedExpansion] at h
          rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl <;>
            simp [ProvenancedRow.factorCount] <;> omega
      | nil =>
          simp only [provenancedExpansion] at h
          split at h
          · rw [Option.some.injEq] at h
            subst qs
            simp at hs
          · split at h
            · contradiction
            · rw [Option.some.injEq] at h
              subst qs
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
              rcases hs with rfl | rfl <;>
                simp [ProvenancedRow.factorCount] <;> omega

/-- A whole trace below a row with too few displayed factors is invisible in
factor number `p`. -/
theorem provenancedTraceFactor_eq_zero_of_factorCount_lt
    (p k : ℕ) (hk : k ≤ n + 1) (r : ProvenancedRow n L data hn)
    (hr : r.factorCount n L data hn < p) :
    provenancedTraceFactor n L data hn p k hk r = 0 := by
  classical
  let C := provenancedCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : provenancedExpansion n L data hn r with
      | none =>
          change provenancedCellFactorLinear n L data hn p k hk
            (provenancedTrace n L data hn r) = 0
          rw [provenancedTrace_eq_of_expansion_none n L data hn r hexp]
          have hc := provenancedCell?_eq_none_of_expansion_eq_none
            n L data hn r hexp
          simp [hc]
      | some qs =>
          change provenancedCellFactorLinear n L data hn p k hk
            (provenancedTrace n L data hn r) = 0
          rw [provenancedTrace_eq_of_expansion_some n L data hn r qs hexp,
            map_add, map_list_sum]
          have hhere : provenancedCellFactorLinear n L data hn p k hk
              (match provenancedCell? n L data hn r with
              | none => 0
              | some c => Finsupp.single c 1) = 0 := by
            cases hc : provenancedCell? n L data hn r with
            | none => simp [hc]
            | some c =>
                have hrow : c.componentRow.factorCount n L data hn < p := by
                  cases r with
                  | component => simp [provenancedCell?] at hc
                  | marked rho context mark left right =>
                      simp [provenancedCell?] at hc
                      rcases hc with ⟨rfl, hmark, hwall, rfl⟩
                      simpa [ProvenancedCell.componentRow,
                        ProvenancedRow.factorCount] using hr
                simp only [hc, provenancedCellFactorLinear,
                  Finsupp.linearCombination_single]
                simpa [ProvenancedCell.factorEdge] using
                  rightSymbol_provenancedRow_eq_zero_of_factorCount_lt
                    n L data hn p k hk c.componentRow hrow
          have hchildren :
              ((qs.attach.map fun s ↦ s.1.1 •
                  provenancedTrace n L data hn s.1.2).map
                (provenancedCellFactorLinear n L data hn p k hk)).sum = 0 := by
            simp only [List.map_map, Function.comp_apply]
            apply List.sum_eq_zero
            intro y hy
            rw [List.mem_map] at hy
            obtain ⟨s, hs, rfl⟩ := hy
            change provenancedCellFactorLinear n L data hn p k hk
                (s.1.1 • provenancedTrace n L data hn s.1.2) = 0
            rw [map_zsmul]
            change s.1.1 • provenancedTraceFactor n L data hn p k hk s.1.2 = 0
            have hsle := provenancedExpansion_factorCount_le n L data hn hexp
              s.1 s.2
            rw [ih s.1.2 (C.decreases hexp s.1 s.2)
                (lt_of_le_of_lt hsle hr)]
            module
          exact (congrArg₂ (fun x y ↦ x + y) hhere hchildren).trans (add_zero 0)

/-- The boundary symbol stored at the unique crossing of weight `k` and
factor number `q+1`. -/
def ProvenancedCell.diagonalBoundary (q k : ℕ) (hk : k ≤ n + 1)
    (c : ProvenancedCell n L data hn) :
    Sym[ℤ] (Fin (q + 1)) (A L k) :=
  if hlen : c.left.length = q then
    if hactive : c.activeWeight n L data hn = k then
      rightSymbol n L data hn (q + 1) k hk c.markedRow.value
    else 0
  else 0

private def provenancedCellDiagonalLinear (q k : ℕ) (hk : k ≤ n + 1) :
    (ProvenancedCell n L data hn →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin (q + 1)) (A L k) :=
  Finsupp.linearCombination ℤ
    (fun c ↦ c.diagonalBoundary n L data hn q k hk)

/-- The complete signed diagonal boundary below one contextual row. -/
def provenancedTraceDiagonal (q k : ℕ) (hk : k ≤ n + 1)
    (r : ProvenancedRow n L data hn) :
    Sym[ℤ] (Fin (q + 1)) (A L k) :=
  (provenancedTrace n L data hn r).sum (fun c z ↦
    z • c.diagonalBoundary n L data hn q k hk)

private def provenancedDiagonalSeed (q k : ℕ) (hk : k ≤ n + 1)
    (r : ProvenancedRow n L data hn) :
    Sym[ℤ] (Fin (q + 1)) (A L k) :=
  match provenancedCell? n L data hn r with
  | none => 0
  | some c => c.diagonalBoundary n L data hn q k hk

private theorem provenancedTraceDiagonal_eq_of_expansion_some
    (q k : ℕ) (hk : k ≤ n + 1)
    (r : ProvenancedRow n L data hn)
    (rows : List (ℤ × ProvenancedRow n L data hn))
    (h : provenancedExpansion n L data hn r = some rows) :
    provenancedTraceDiagonal n L data hn q k hk r =
      provenancedDiagonalSeed n L data hn q k hk r +
        (rows.map fun s ↦ s.1 •
          provenancedTraceDiagonal n L data hn q k hk s.2).sum := by
  change provenancedCellDiagonalLinear n L data hn q k hk
    (provenancedTrace n L data hn r) = _
  rw [provenancedTrace_eq_of_expansion_some n L data hn r rows h,
    map_add, map_list_sum]
  have hhere : provenancedCellDiagonalLinear n L data hn q k hk
        (match provenancedCell? n L data hn r with
        | none => 0
        | some c => Finsupp.single c 1) =
      provenancedDiagonalSeed n L data hn q k hk r := by
    cases hc : provenancedCell? n L data hn r with
    | none => simp [provenancedDiagonalSeed, hc,
        provenancedCellDiagonalLinear]
    | some c =>
        simp only [provenancedDiagonalSeed, hc,
          provenancedCellDiagonalLinear, Finsupp.linearCombination_single]
        module
  have hchildren :
      ((rows.attach.map fun s ↦ s.1.1 •
          provenancedTrace n L data hn s.1.2).map
        (provenancedCellDiagonalLinear n L data hn q k hk)).sum =
        (rows.attach.map fun s ↦ s.1.1 •
          provenancedTraceDiagonal n L data hn q k hk s.1.2).sum := by
    apply congrArg List.sum
    rw [List.map_map]
    apply List.map_congr_left
    intro s hs
    change provenancedCellDiagonalLinear n L data hn q k hk
        (s.1.1 • provenancedTrace n L data hn s.1.2) =
      s.1.1 • provenancedTraceDiagonal n L data hn q k hk s.1.2
    rw [map_zsmul]
    rfl
  have hattached :
      (rows.attach.map fun s ↦ s.1.1 •
          provenancedTraceDiagonal n L data hn q k hk s.1.2).sum =
        (rows.map fun s ↦ s.1 •
          provenancedTraceDiagonal n L data hn q k hk s.2).sum := by
    have hmap : rows.attach.map (fun s ↦ s.1.1 •
          provenancedTraceDiagonal n L data hn q k hk s.1.2) =
        rows.map (fun s ↦ s.1 •
          provenancedTraceDiagonal n L data hn q k hk s.2) :=
      List.attach_map_val (l := rows)
        (f := fun s : ℤ × ProvenancedRow n L data hn ↦
          s.1 • provenancedTraceDiagonal n L data hn q k hk s.2)
    rw [hmap]
  calc
    _ = provenancedDiagonalSeed n L data hn q k hk r +
        (rows.attach.map fun s ↦ s.1.1 •
          provenancedTraceDiagonal n L data hn q k hk s.1.2).sum :=
      congrArg₂ (fun x y ↦ x + y) hhere hchildren
    _ = _ := congrArg (fun z ↦
      provenancedDiagonalSeed n L data hn q k hk r + z) hattached

/-- Component rows never contain another truncation event. -/
theorem provenancedTrace_component_eq_zero
    (rho : Relations n L data) (c : RelationContext n L data hn)
    (b : Fin (n + 2))
    (left right : List (AdaptedIndex n L data hn)) :
    provenancedTrace n L data hn (.component rho c b left right) = 0 := by
  classical
  let C := provenancedCollector n L data hn
  let P : ProvenancedRow n L data hn → Prop
    | .marked _ _ _ _ _ => True
    | .component rho c b left right =>
        provenancedTrace n L data hn (.component rho c b left right) = 0
  have hall : ∀ r, P r := by
    intro r
    induction r using C.wellFounded.induction with
    | h r ih =>
        cases r with
        | marked => trivial
        | component rho c b left right =>
            change provenancedTrace n L data hn
              (.component rho c b left right) = 0
            cases hleft : left.reverse with
            | nil =>
                have hexp : provenancedExpansion n L data hn
                    (.component rho c b left right) = none := by
                  simp only [provenancedExpansion]
                  split
                  · rfl
                  · simp_all
                rw [provenancedTrace_eq_of_expansion_none n L data hn _ hexp]
                rfl
            | cons x leftRev =>
                let r₁ : ProvenancedRow n L data hn :=
                  .component rho c b leftRev.reverse (x :: right)
                let r₂ : ProvenancedRow n L data hn :=
                  .component rho (RelationContext.lieRight c x) b
                    leftRev.reverse right
                have hexp : provenancedExpansion n L data hn
                    (.component rho c b left right) =
                      some [(1, r₁), (-1, r₂)] := by
                  simp only [provenancedExpansion]
                  split
                  · simp_all
                  · simp_all [r₁, r₂]
                rw [provenancedTrace_eq_of_expansion_some
                  n L data hn _ _ hexp]
                simp only [provenancedCell?, zero_add]
                have hexpC : C.expansion (.component rho c b left right) =
                    some [(1, r₁), (-1, r₂)] := hexp
                have h₁ := ih r₁ (C.decreases hexpC (1, r₁) (by simp))
                have h₂ := ih r₂ (C.decreases hexpC (-1, r₂) (by simp))
                change provenancedTrace n L data hn r₁ = 0 at h₁
                change provenancedTrace n L data hn r₂ = 0 at h₂
                simp [h₁, h₂]
  exact hall (.component rho c b left right)

@[simp] theorem provenancedTraceDiagonal_component
    (q k : ℕ) (hk : k ≤ n + 1)
    (rho : Relations n L data) (c : RelationContext n L data hn)
    (b : Fin (n + 2))
    (left right : List (AdaptedIndex n L data hn)) :
    provenancedTraceDiagonal n L data hn q k hk
      (.component rho c b left right) = 0 := by
  rw [provenancedTraceDiagonal,
    provenancedTrace_component_eq_zero n L data hn]
  simp

/-- A trace with too few displayed factors cannot meet the `q+1` diagonal. -/
theorem provenancedTraceDiagonal_eq_zero_of_factorCount_lt
    (q k : ℕ) (hk : k ≤ n + 1) (r : ProvenancedRow n L data hn)
    (hr : r.factorCount n L data hn < q + 1) :
    provenancedTraceDiagonal n L data hn q k hk r = 0 := by
  classical
  let C := provenancedCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : provenancedExpansion n L data hn r with
      | none =>
          change provenancedCellDiagonalLinear n L data hn q k hk
            (provenancedTrace n L data hn r) = 0
          rw [provenancedTrace_eq_of_expansion_none n L data hn r hexp]
          have hc := provenancedCell?_eq_none_of_expansion_eq_none
            n L data hn r hexp
          simp [hc]
      | some qs =>
          change provenancedCellDiagonalLinear n L data hn q k hk
            (provenancedTrace n L data hn r) = 0
          rw [provenancedTrace_eq_of_expansion_some n L data hn r qs hexp,
            map_add, map_list_sum]
          have hhere : provenancedCellDiagonalLinear n L data hn q k hk
              (match provenancedCell? n L data hn r with
              | none => 0
              | some c => Finsupp.single c 1) = 0 := by
            cases hc : provenancedCell? n L data hn r with
            | none => simp [hc]
            | some c =>
                have hlen : c.left.length ≠ q := by
                  intro hlen
                  have hrow : c.componentRow.factorCount n L data hn = q + 1 := by
                    simp [ProvenancedCell.componentRow,
                      ProvenancedRow.factorCount, hlen]
                  cases r <;> simp [provenancedCell?] at hc
                  next rho context mark left right =>
                    rcases hc with ⟨rfl, hmark, hwall, rfl⟩
                    have hlt : left.length + 1 < q + 1 := by
                      simpa [ProvenancedRow.factorCount] using hr
                    have hlen' : left.length = q := by simpa using hlen
                    omega
                simp [hc, provenancedCellDiagonalLinear,
                  ProvenancedCell.diagonalBoundary, hlen]
          have hchildren :
              ((qs.attach.map fun s ↦ s.1.1 •
                  provenancedTrace n L data hn s.1.2).map
                (provenancedCellDiagonalLinear n L data hn q k hk)).sum = 0 := by
            simp only [List.map_map, Function.comp_apply]
            apply List.sum_eq_zero
            intro y hy
            rw [List.mem_map] at hy
            obtain ⟨s, hs, rfl⟩ := hy
            change provenancedCellDiagonalLinear n L data hn q k hk
                (s.1.1 • provenancedTrace n L data hn s.1.2) = 0
            rw [map_zsmul]
            change s.1.1 • provenancedTraceDiagonal n L data hn q k hk s.1.2 = 0
            have hsle := provenancedExpansion_factorCount_le n L data hn hexp
              s.1 s.2
            rw [ih s.1.2 (C.decreases hexp s.1 s.2)
                (lt_of_le_of_lt hsle hr)]
            module
          exact (congrArg₂ (fun x y ↦ x + y) hhere hchildren).trans (add_zero 0)

/-- The manuscript's intermediate packet on the diagonal
`(m_k,k)=(n-k+2,k)`. -/
def contextualChi {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.One (presentation n L data k (by omega) (by omega))
      (n - k + 1) :=
  contextualSymbolChain n L data hn w (n - k + 1) k (by omega) (by omega)

/-- The horizontal and vertical reads of every intermediate packet agree,
with the sign already fixed in `transgression`. -/
theorem Phi_contextualChi_eq_T_dOne {a : L}
    (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Phi n L data k hk hkn
        (Koszul.PresentationHomology.oneMap
          (presentation n L data k (by omega) (by omega))
          (presentation (n := n) L data (k - 1) (by omega) (by omega))
          (presentationProjection n L data k hk (by omega))
          (n - k + 1) (contextualChi n L data hn w k hk hkn)) =
      T n L data k hk hkn
        (Koszul.dOne (presentation n L data k (by omega) (by omega))
          (n - k + 1) (contextualChi n L data hn w k hk hkn)) := by
  exact LinearMap.congr_fun (transgression n L data k hk hkn)
    (contextualChi n L data hn w k hk hkn)

/-! ### The complete nonterminal vertical read

The diagonal packet above is useful only after all factor-lowering
corrections have been included.  The following two statements perform that
global bookkeeping once.  They deliberately use the complete contextual
trace: terminal marked walls have at most two displayed factors, so they are
invisible in every nonterminal factor number `n-k+2 ≥ 3`. -/

/-- The exact factor-`q` component edge of the complete contextual trace. -/
def GoverningWitness.componentTraceFactor {a : L}
    (w : GoverningWitness n L data a) (q k : ℕ) (hk : k ≤ n + 1) :
    Sym[ℤ] (Fin q) (A L k) :=
  (GoverningWitness.provenancedCells n L data hn w).sum
    (fun c z ↦ z • c.factorEdge n L data hn q k hk)

private theorem GoverningWitness.componentFactorFrontier_eq_trace {a : L}
    (w : GoverningWitness n L data a) (q k : ℕ) (hk : k ≤ n + 1) :
    provenancedComponentFactorLinear n L data hn q k hk
        (GoverningWitness.provenancedFrontier n L data hn w) =
      w.componentTraceFactor n L data hn q k hk := by
  classical
  rw [GoverningWitness.provenancedFrontier,
    GoverningWitness.componentTraceFactor,
    GoverningWitness.provenancedCells]
  change provenancedComponentFactorLinear n L data hn q k hk
      ((GoverningWitness.provenancedInitial n L data hn w).sum
        (fun r z ↦ z • (provenancedCollector n L data hn).normalForm r)) =
    provenancedCellFactorLinear n L data hn q k hk
      ((GoverningWitness.provenancedInitial n L data hn w).sum
        (fun r z ↦ z • provenancedTrace n L data hn r))
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul]
  change w.provenancedInitial n L data hn r •
      normalFormProvenancedComponentFactor n L data hn q k hk r =
    w.provenancedInitial n L data hn r •
      provenancedTraceFactor n L data hn q k hk r
  rw [normalFormProvenancedComponentFactor_eq_trace]
  have hseed : provenancedComponentFactorSeed n L data hn q k hk r = 0 := by
    have hrne := Finsupp.mem_support_iff.mp hr
    rw [GoverningWitness.provenancedInitial, Finsupp.sum_apply] at hrne
    cases r with
    | component root context mark left right =>
        exfalso
        apply hrne
        apply Finset.sum_eq_zero
        intro p hp
        change w.relationCoefficients p *
          (provenancedRowsOfRightFactor n L data hn p.1 p.2)
            (.component root context mark left right) = 0
        rw [show (provenancedRowsOfRightFactor n L data hn p.1 p.2)
            (.component root context mark left right) = 0 by
          rw [provenancedRowsOfRightFactor, Finsupp.sum_apply]
          apply Finset.sum_eq_zero
          intro e he
          simp, mul_zero]
    | marked => rfl
  rw [hseed, zero_add]

/-- In factor number at least three, the complete component trace is the
whole projected PBW symbol.  The two marked external walls are too short to
contribute. -/
theorem GoverningWitness.componentTraceFactor_eq_rightSymbol
    {a : L} (w : GoverningWitness n L data a)
    (q k : ℕ) (hk : k ≤ n + 1) (hq : 3 ≤ q) :
    w.componentTraceFactor n L data hn q k hk =
      rightSymbol n L data hn q k hk w.theta := by
  classical
  have heval := GoverningWitness.evaluate_provenancedFrontier
    n L data hn w
  have hsymbol := congrArg (rightSymbol n L data hn q k hk) heval
  change rightSymbol n L data hn q k hk
      ((GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z • r.value)) =
    rightSymbol n L data hn q k hk w.theta at hsymbol
  rw [map_finsuppSum] at hsymbol
  have hmarked :
      (GoverningWitness.provenancedFrontier n L data hn w).sum
          (fun r z ↦ z • rightSymbol n L data hn q k hk r.value) =
        provenancedComponentFactorLinear n L data hn q k hk
          (GoverningWitness.provenancedFrontier n L data hn w) := by
    classical
    change (GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z • rightSymbol n L data hn q k hk r.value) =
      (GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z •
          provenancedComponentFactorSeed n L data hn q k hk r)
    apply Finsupp.sum_congr
    intro r hrSupport
    have hterminal : provenancedExpansion n L data hn r = none := by
      by_contra hnonterminal
      apply Finsupp.mem_support_iff.mp hrSupport
      rw [GoverningWitness.provenancedFrontier, Finsupp.sum_apply]
      apply Finset.sum_eq_zero
      intro s hs
      change (GoverningWitness.provenancedInitial n L data hn w) s *
          (provenancedCollector n L data hn).normalForm s r = 0
      have hz :=
        (provenancedCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
          s r hnonterminal
      rw [hz, mul_zero]
    cases r with
    | component => rfl
    | marked root context mark left right =>
        have hright : right = [] := by
          cases right with
          | nil => rfl
          | cons x right => simp [provenancedExpansion] at hterminal
        subst right
        have hmark : mark.val ≠ 0 := by
          intro hzero
          simp [provenancedExpansion, hzero] at hterminal
        have hwall :
            provenancedWall n L data hn context mark left = true := by
          by_contra hfalse
          have hfalse' :
              provenancedWall n L data hn context mark left = false :=
            Bool.eq_false_of_not_eq_true hfalse
          simp [provenancedExpansion, hmark, hfalse'] at hterminal
        have hcount :
            (ProvenancedRow.marked root context mark left [] :
                ProvenancedRow n L data hn).factorCount n L data hn < q := by
          cases left with
          | nil => simp [ProvenancedRow.factorCount]; omega
          | cons x tail =>
              cases tail with
              | nil => simp [ProvenancedRow.factorCount]; omega
              | cons y tail => simp [provenancedWall] at hwall
        rw [rightSymbol_provenancedRow_eq_zero_of_factorCount_lt
          n L data hn q k hk _ hcount]
        rfl
  calc
    w.componentTraceFactor n L data hn q k hk =
        provenancedComponentFactorLinear n L data hn q k hk
          (GoverningWitness.provenancedFrontier n L data hn w) :=
      (w.componentFactorFrontier_eq_trace n L data hn q k hk).symm
    _ = (GoverningWitness.provenancedFrontier n L data hn w).sum
          (fun r z ↦ z • rightSymbol n L data hn q k hk r.value) :=
      hmarked.symm
    _ = rightSymbol n L data hn q k hk w.theta := by
      simpa only [map_zsmul] using hsymbol

/-- The complete nonterminal vertical edge is zero.  This is the governing
coefficient vanishing after every factor-lowering correction has been fed
into the contextual trace. -/
theorem GoverningWitness.T_componentTraceFactor_eq_zero {a : L}
    (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    T n L data k hk hkn
        (w.componentTraceFactor n L data hn (n - k + 2) k (by omega)) = 0 := by
  rw [w.componentTraceFactor_eq_rightSymbol n L data hn
    (n - k + 2) k (by omega) (by omega)]
  exact T_rightSymbol_theta_eq_zero n L data hn w k hk hkn

/-- A contextual component row is homogeneous in the sum of the weights of
its displayed ordinary factors and its active relation component. -/
theorem ProvenancedCell.proj_componentRow_eq_zero_of_weight_ne
    (c : ProvenancedCell n L data hn) (p : ℕ)
    (hne : (c.left.map (adaptedWeightedBasis n L data hn).weight).sum +
        c.activeWeight n L data hn ≠ n + 1) :
    (adaptedWeightedBasis n L data hn).proj (n + 1) p
        c.componentRow.value = 0 := by
  classical
  let B := adaptedWeightedBasis n L data hn
  let x := RelationContext.component n L data hn c.context c.root c.mark
  rw [show c.componentRow.value =
      (MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ x) by
    simp [ProvenancedCell.componentRow, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, x]]
  rw [← (adaptedBasis n L data hn).sum_repr x, map_sum,
    Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_zsmul, mul_smul_comm, map_zsmul]
  by_cases hiw : B.weight i = c.activeWeight n L data hn
  · have hword : MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) =
        MarkedRow.basisWord n L data hn (c.left ++ [i]) := by
      simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
    rw [hword]
    apply smul_eq_zero_of_right
    change B.proj (n + 1) p
      (LieRings.PBW.basisWord ℤ (FreeModel n L)
        (AdaptedIndex n L data hn) B.basis (c.left ++ [i])) = 0
    apply B.proj_basisWord_eq_zero_of_weight_ne
    simpa [List.map_append, hiw, B] using hne
  · have hcoeff : ((adaptedBasis n L data hn).repr x) i = 0 := by
      change ((pieceAdaptedBasis n L data hn i.1).repr (x i.1)) i.2 = 0
      have hx : x i.1 = 0 := by
        apply RelationContext.component_apply_eq_zero_of_ne
          n L data hn c.context c.root c.mark c.mark_pos i.1
        simpa [B, adaptedWeightedBasis,
          ProvenancedCell.activeWeight] using hiw
      rw [hx, map_zero]
      rfl
    rw [hcoeff, zero_smul]

/-- Consequently a nonterminal transgression can only see contextual cells
of total manuscript weight `n+1`. -/
theorem ProvenancedCell.T_factorEdge_eq_zero_of_weight_ne
    (c : ProvenancedCell n L data hn)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (hne : (c.left.map (adaptedWeightedBasis n L data hn).weight).sum +
        c.activeWeight n L data hn ≠ n + 1) :
    T n L data k hk hkn
        (c.factorEdge n L data hn (n - k + 2) k (by omega)) = 0 := by
  apply T_rightSymbol_eq_zero_of_proj_eq_zero n L data hn k hk hkn
  exact c.proj_componentRow_eq_zero_of_weight_ne n L data hn
    (n - k + 2) hne

/-! ### Terminal primitive read -/

/-- One-factor PBW projection, followed by the homogeneous terminal
coordinate. -/
def terminalPrimitiveRead : UEA ℤ (FreeModel n L) →ₗ[ℤ]
    ZMod (2 ^ data.exponent) :=
  (topCoord n L data).comp
    ((FreeMetabelian.Free.weightProject n (by omega)).comp
      (pbwPrimitive n L data hn))

/-- The governing relation side has terminal primitive coordinate equal to
the cyclic coordinate of the original top-layer element. -/
theorem GoverningWitness.terminalPrimitiveRead_theta {a : L}
    (w : GoverningWitness n L data a) :
    terminalPrimitiveRead n L data hn w.theta =
      data.topEquiv ⟨a, by
        rw [← w.evaluates]
        change evaluation n L data
          (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
            lowerCentralSeries ℤ L n
        rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
        change FreeMetabelian.Evaluation.linear data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
            (FreeMetabelian.Free.incl
              (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
        rw [FreeMetabelian.Evaluation.linear_incl]
        cases n with
        | zero => simp
        | succ t =>
            exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
              data.metabelian
              (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ := by
  rw [terminalPrimitiveRead, LinearMap.comp_apply, LinearMap.comp_apply,
    w.pbwPrimitive_theta n L data hn]
  rw [FreeMetabelian.Free.weightProject_weightIncl]
  change data.topEquiv _ = data.topEquiv _
  apply congrArg data.topEquiv
  apply Subtype.ext
  exact w.evaluates

/-- Primitive attached to a whole one-factor contextual relation wall. -/
def ProvenancedTerminalOne.fullPrimitive
    (c : ProvenancedTerminalOne n L data hn) : FreeModel n L :=
  RelationContext.relation n L data hn c.context c.root

/-- Primitive attached to a placed terminal factor-two wall. -/
def ProvenancedTerminalTwo.primitive
    (c : ProvenancedTerminalTwo n L data hn) : FreeModel n L :=
  pbwPrimitive n L data hn c.row.value

private def provenancedTerminalOnePrimitiveSeed
    (r : ProvenancedRow n L data hn) : FreeModel n L :=
  match provenancedTerminal? n L data hn r with
  | some (.inl c) => c.fullPrimitive n L data hn
  | _ => 0

private def provenancedTerminalTwoPrimitiveSeed
    (r : ProvenancedRow n L data hn) : FreeModel n L :=
  match provenancedTerminal? n L data hn r with
  | some (.inr c) => c.primitive n L data hn
  | _ => 0

/-- Every terminal contextual row is exactly one of the three external
families: a component leaf, a whole one-factor relation, or a placed
factor-two relation wall. -/
theorem provenanced_terminal_cases
    (r : ProvenancedRow n L data hn)
    (hr : provenancedExpansion n L data hn r = none) :
    (∃ rho c b right, r = .component rho c b [] right) ∨
      (∃ t : ProvenancedTerminalOne n L data hn, r = t.row) ∨
      (∃ t : ProvenancedTerminalTwo n L data hn, r = t.row) := by
  classical
  cases r with
  | component rho c b left right =>
      simp only [provenancedExpansion] at hr
      split at hr
      · rename_i hleft
        left
        have : left = [] := by
          have hrev : left.reverse = [] := hleft
          simpa using congrArg List.reverse hrev
        subst left
        exact ⟨rho, c, b, right, rfl⟩
      · contradiction
  | marked rho c b left right =>
      cases right with
      | cons x right => simp [provenancedExpansion] at hr
      | nil =>
          simp only [provenancedExpansion] at hr
          split at hr
          · contradiction
          · rename_i hb0
            split at hr
            · rename_i hwall
              right
              unfold provenancedWall at hwall
              cases left with
              | nil =>
                  simp only at hwall
                  have hactive : b.val +
                      RelationContext.weight n L data hn c = n + 1 := by
                    simpa using of_decide_eq_true hwall
                  left
                  exact ⟨⟨rho, c, b, hactive⟩, rfl⟩
              | cons x tail =>
                  cases tail with
                  | nil =>
                      simp only at hwall
                      have hactive : b.val +
                          RelationContext.weight n L data hn c = n := by
                        simpa using of_decide_eq_true hwall
                      right
                      exact ⟨⟨rho, c, b, x, hactive⟩, rfl⟩
                  | cons y tail => simp at hwall
            · contradiction

/-- At a terminal row, PBW primitive evaluation splits into precisely the
three external primitive reads.  The one-factor marked case is kept as the
whole contextual relation. -/
private theorem pbwPrimitive_terminal_decomposition
    (r : ProvenancedRow n L data hn)
    (hr : provenancedExpansion n L data hn r = none) :
    pbwPrimitive n L data hn r.value =
      provenancedComponentPrimitiveSeed n L data hn r +
        provenancedTerminalOnePrimitiveSeed n L data hn r +
        provenancedTerminalTwoPrimitiveSeed n L data hn r := by
  rcases provenanced_terminal_cases n L data hn r hr with
    ⟨rho, c, b, right, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · simp [provenancedComponentPrimitiveSeed,
      provenancedTerminalOnePrimitiveSeed,
      provenancedTerminalTwoPrimitiveSeed, provenancedTerminal?]
  · have hfull := RelationContext.relation_eq_markedPrefix_of_active_top
      n L data hn t.context t.root t.mark t.active
    simp only [ProvenancedTerminalOne.row, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word,
      List.map_nil, List.prod_nil, one_mul, mul_one]
    rw [← hfull, pbwPrimitive_iota]
    simp [provenancedComponentPrimitiveSeed,
      provenancedTerminalOnePrimitiveSeed,
      provenancedTerminalTwoPrimitiveSeed, provenancedTerminal?,
      ProvenancedTerminalOne.fullPrimitive, t.active]
  · simp [ProvenancedTerminalTwo.primitive,
      provenancedComponentPrimitiveSeed,
      provenancedTerminalOnePrimitiveSeed,
      provenancedTerminalTwoPrimitiveSeed, provenancedTerminal?,
      ProvenancedTerminalTwo.row, t.active]

private def provenancedTerminalOnePrimitiveLinear :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ] FreeModel n L :=
  Finsupp.linearCombination ℤ
    (provenancedTerminalOnePrimitiveSeed n L data hn)

private def provenancedTerminalTwoPrimitiveLinear :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ] FreeModel n L :=
  Finsupp.linearCombination ℤ
    (provenancedTerminalTwoPrimitiveSeed n L data hn)

/-- The complete primitive frontier, with whole relations grouped before
any terminal projection. -/
theorem GoverningWitness.pbwPrimitive_theta_frontier {a : L}
    (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn w.theta =
      provenancedComponentPrimitiveLinear n L data hn
          (GoverningWitness.provenancedFrontier n L data hn w) +
        provenancedTerminalOnePrimitiveLinear n L data hn
          (GoverningWitness.provenancedFrontier n L data hn w) +
        provenancedTerminalTwoPrimitiveLinear n L data hn
          (GoverningWitness.provenancedFrontier n L data hn w) := by
  classical
  have heval := GoverningWitness.evaluate_provenancedFrontier
    n L data hn w
  have hpbw := congrArg (pbwPrimitive n L data hn) heval
  change pbwPrimitive n L data hn
      ((GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z • r.value)) = pbwPrimitive n L data hn w.theta at hpbw
  rw [map_finsuppSum] at hpbw
  rw [← hpbw]
  simp only [map_zsmul]
  simp only [provenancedComponentPrimitiveLinear,
    provenancedTerminalOnePrimitiveLinear,
    provenancedTerminalTwoPrimitiveLinear,
    Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hrSupport
  have hterminal : provenancedExpansion n L data hn r = none := by
    by_contra hnonterminal
    apply Finsupp.mem_support_iff.mp hrSupport
    rw [GoverningWitness.provenancedFrontier, Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    change (GoverningWitness.provenancedInitial n L data hn w) s *
        (provenancedCollector n L data hn).normalForm s r = 0
    have hz := (provenancedCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
      s r hnonterminal
    rw [hz, mul_zero]
  have hdec := pbwPrimitive_terminal_decomposition n L data hn r hterminal
  simpa only [smul_add] using congrArg
    (fun x ↦ (GoverningWitness.provenancedFrontier n L data hn w) r • x) hdec

/-- Sum of all contextual component edges in the complete signed trace. -/
def GoverningWitness.componentTracePrimitive {a : L}
    (w : GoverningWitness n L data a) : FreeModel n L :=
  (GoverningWitness.provenancedCells n L data hn w).sum
    (fun c z ↦ z • c.primitive n L data hn)

/-- Sum of the whole contextual relations at the one-factor wall. -/
def GoverningWitness.terminalOnePrimitive {a : L}
    (w : GoverningWitness n L data a) : FreeModel n L :=
  (GoverningWitness.provenancedTerminalOne n L data hn w).sum
    (fun c z ↦ z • c.fullPrimitive n L data hn)

/-- Sum of the placed PBW primitives at the factor-two wall. -/
def GoverningWitness.terminalTwoPrimitive {a : L}
    (w : GoverningWitness n L data a) : FreeModel n L :=
  (GoverningWitness.provenancedTerminalTwo n L data hn w).sum
    (fun c z ↦ z • c.primitive n L data hn)

private theorem GoverningWitness.componentFrontier_eq_trace {a : L}
    (w : GoverningWitness n L data a) :
    provenancedComponentPrimitiveLinear n L data hn
        (GoverningWitness.provenancedFrontier n L data hn w) =
      w.componentTracePrimitive n L data hn := by
  classical
  rw [GoverningWitness.provenancedFrontier,
    GoverningWitness.componentTracePrimitive,
    GoverningWitness.provenancedCells]
  change provenancedComponentPrimitiveLinear n L data hn
      ((GoverningWitness.provenancedInitial n L data hn w).sum
        (fun r z ↦ z • (provenancedCollector n L data hn).normalForm r)) =
    provenancedCellPrimitiveLinear n L data hn
      ((GoverningWitness.provenancedInitial n L data hn w).sum
        (fun r z ↦ z • provenancedTrace n L data hn r))
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul]
  change w.provenancedInitial n L data hn r •
      normalFormProvenancedComponentPrimitive n L data hn r =
    w.provenancedInitial n L data hn r •
      provenancedTracePrimitive n L data hn r
  rw [normalFormProvenancedComponentPrimitive_eq_trace]
  have hseed : provenancedComponentPrimitiveSeed n L data hn r = 0 := by
    have hrne := Finsupp.mem_support_iff.mp hr
    rw [GoverningWitness.provenancedInitial, Finsupp.sum_apply] at hrne
    by_contra hne
    cases r with
    | component root context mark left right =>
        apply hrne
        apply Finset.sum_eq_zero
        intro p hp
        change w.relationCoefficients p *
          (provenancedRowsOfRightFactor n L data hn p.1 p.2)
            (.component root context mark left right) = 0
        rw [show (provenancedRowsOfRightFactor n L data hn p.1 p.2)
            (.component root context mark left right) = 0 by
          rw [provenancedRowsOfRightFactor, Finsupp.sum_apply]
          apply Finset.sum_eq_zero
          intro e he
          simp, mul_zero]
    | marked => exact hne rfl
  rw [hseed, zero_add]

private theorem GoverningWitness.terminalOneFrontier_eq {a : L}
    (w : GoverningWitness n L data a) :
    provenancedTerminalOnePrimitiveLinear n L data hn
        (GoverningWitness.provenancedFrontier n L data hn w) =
      w.terminalOnePrimitive n L data hn := by
  classical
  rw [GoverningWitness.terminalOnePrimitive,
    GoverningWitness.provenancedTerminalOne]
  change provenancedTerminalOnePrimitiveLinear n L data hn
      (GoverningWitness.provenancedFrontier n L data hn w) =
    Finsupp.linearCombination ℤ
      (fun c ↦ c.fullPrimitive n L data hn)
      ((GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z • provenancedTerminalOnePart n L data hn r))
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul]
  cases hc : provenancedTerminal? n L data hn r with
  | none => simp [provenancedTerminalOnePart,
      provenancedTerminalOnePrimitiveSeed, hc]
  | some t =>
      cases t with
      | inl c => simp [provenancedTerminalOnePart,
          provenancedTerminalOnePrimitiveSeed, hc]
      | inr c => simp [provenancedTerminalOnePart,
          provenancedTerminalOnePrimitiveSeed, hc]

private theorem GoverningWitness.terminalTwoFrontier_eq {a : L}
    (w : GoverningWitness n L data a) :
    provenancedTerminalTwoPrimitiveLinear n L data hn
        (GoverningWitness.provenancedFrontier n L data hn w) =
      w.terminalTwoPrimitive n L data hn := by
  classical
  rw [GoverningWitness.terminalTwoPrimitive,
    GoverningWitness.provenancedTerminalTwo]
  change provenancedTerminalTwoPrimitiveLinear n L data hn
      (GoverningWitness.provenancedFrontier n L data hn w) =
    Finsupp.linearCombination ℤ
      (fun c ↦ c.primitive n L data hn)
      ((GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z • provenancedTerminalTwoPart n L data hn r))
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul]
  cases hc : provenancedTerminal? n L data hn r with
  | none => simp [provenancedTerminalTwoPart,
      provenancedTerminalTwoPrimitiveSeed, hc]
  | some t =>
      cases t with
      | inl c => simp [provenancedTerminalTwoPart,
          provenancedTerminalTwoPrimitiveSeed, hc]
      | inr c => simp [provenancedTerminalTwoPart,
          provenancedTerminalTwoPrimitiveSeed, hc]

/-- Exact grouped primitive frontier of the governing relation side. -/
theorem GoverningWitness.pbwPrimitive_theta_external {a : L}
    (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn w.theta =
      w.componentTracePrimitive n L data hn +
        w.terminalOnePrimitive n L data hn +
        w.terminalTwoPrimitive n L data hn := by
  rw [w.pbwPrimitive_theta_frontier n L data hn,
    w.componentFrontier_eq_trace n L data hn,
    w.terminalOneFrontier_eq n L data hn,
    w.terminalTwoFrontier_eq n L data hn]

/-- The grouped one-factor wall is still an honest full relation. -/
def GoverningWitness.terminalOneRelation {a : L}
    (w : GoverningWitness n L data a) : Relations n L data :=
  (GoverningWitness.provenancedTerminalOne n L data hn w).sum
    (fun c z ↦ z • RelationContext.relation n L data hn c.context c.root)

@[simp] theorem GoverningWitness.terminalOneRelation_coe {a : L}
    (w : GoverningWitness n L data a) :
    (w.terminalOneRelation n L data hn : FreeModel n L) =
      w.terminalOnePrimitive n L data hn := by
  classical
  rw [GoverningWitness.terminalOneRelation,
    GoverningWitness.terminalOnePrimitive]
  change (Relations n L data).subtype
      ((GoverningWitness.provenancedTerminalOne n L data hn w).sum
        (fun c z ↦ z • RelationContext.relation n L data hn c.context c.root)) = _
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul]
  rfl

/-- The non-relation part of the primitive frontier, grouped before terminal
evaluation as required by the manuscript. -/
def GoverningWitness.externalPrimitivePreimage {a : L}
    (w : GoverningWitness n L data a) : TopPreimage n L data :=
  ⟨FreeMetabelian.Free.weightIncl n (by omega) w.atilde -
      (w.terminalOneRelation n L data hn : FreeModel n L), by
    change evaluation n L data
      (FreeMetabelian.Free.weightIncl n (by omega) w.atilde -
        (w.terminalOneRelation n L data hn : FreeModel n L)) ∈
          lowerCentralSeries ℤ L n
    rw [map_sub]
    have hrel : evaluation n L data
        (w.terminalOneRelation n L data hn : FreeModel n L) = 0 :=
      (w.terminalOneRelation n L data hn).property
    rw [hrel, sub_zero]
    rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
    change FreeMetabelian.Evaluation.linear data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
        (FreeMetabelian.Free.incl
          (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
    rw [FreeMetabelian.Evaluation.linear_incl]
    cases n with
    | zero => simp
    | succ t =>
        exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
          data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩

theorem GoverningWitness.externalPrimitivePreimage_eq {a : L}
    (w : GoverningWitness n L data a) :
    (w.externalPrimitivePreimage n L data hn : FreeModel n L) =
      w.componentTracePrimitive n L data hn +
        w.terminalTwoPrimitive n L data hn := by
  have h := w.pbwPrimitive_theta_external n L data hn
  rw [w.pbwPrimitive_theta n L data hn] at h
  change FreeMetabelian.Free.weightIncl n (by omega) w.atilde -
      (w.terminalOneRelation n L data hn : FreeModel n L) = _
  rw [w.terminalOneRelation_coe n L data hn]
  rw [h]
  abel

/-- Grouping whole relations first makes the external terminal value exactly
the cyclic coordinate of `a`. -/
theorem GoverningWitness.terminalEval_externalPrimitivePreimage {a : L}
    (w : GoverningWitness n L data a) :
    terminalEval n L data (w.externalPrimitivePreimage n L data hn) =
      data.topEquiv ⟨a, by
        rw [← w.evaluates]
        change evaluation n L data
          (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
            lowerCentralSeries ℤ L n
        rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
        change FreeMetabelian.Evaluation.linear data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
            (FreeMetabelian.Free.incl
              (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
        rw [FreeMetabelian.Evaluation.linear_incl]
        cases n with
        | zero => simp
        | succ t =>
            exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
              data.metabelian
              (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ := by
  change data.topEquiv _ = data.topEquiv _
  apply congrArg data.topEquiv
  apply Subtype.ext
  change evaluation n L data
      (FreeMetabelian.Free.weightIncl n (by omega) w.atilde -
        (w.terminalOneRelation n L data hn : FreeModel n L)) = a
  have hrel : evaluation n L data
      (w.terminalOneRelation n L data hn : FreeModel n L) = 0 :=
    (w.terminalOneRelation n L data hn).property
  rw [map_sub, w.evaluates, hrel, sub_zero]

/-- The complete factor-one projection is the enveloping inclusion of the
PBW primitive. -/
theorem factorProj_one_eq_iota_pbwPrimitive
    (u : UEA ℤ (FreeModel n L)) :
    (adaptedWeightedBasis n L data hn).factorProj 1 u =
      UniversalEnvelopingAlgebra.ι ℤ (pbwPrimitive n L data hn u) := by
  classical
  let B := adaptedWeightedBasis n L data hn
  let f := B.pbwEquiv.symm u
  have hf : f.sum (fun e z ↦ MvPolynomial.monomial e z) = f := by
    simpa only [MvPolynomial.monomial] using Finsupp.sum_single f
  have hu : f.sum (fun e z ↦ B.pbwEquiv (MvPolynomial.monomial e z)) = u := by
    rw [← map_finsuppSum, hf]
    exact B.pbwEquiv.apply_symm_apply u
  rw [← hu, map_finsuppSum, map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro e heSupport
  rw [B.factorProj_monomial]
  change (if LieRings.PBW.WeightedBasis.factorNumber e = 1 then
      B.pbwEquiv (MvPolynomial.monomial e (f e)) else 0) =
    UniversalEnvelopingAlgebra.ι ℤ
      (pbwPrimitive n L data hn
        (B.pbwEquiv (MvPolynomial.monomial e (f e))))
  simp only [pbwPrimitive, LinearMap.comp_apply]
  by_cases he : LieRings.PBW.WeightedBasis.factorNumber e = 1
  · rw [if_pos he]
    obtain ⟨i, rfl⟩ := exponent_eq_single_of_factorNumber_eq_one
      n L data hn e he
    rw [fullRightSymbol_pbwMonomial]
    have hsum : (Finsupp.single i 1).sum (fun _ r ↦ r) = 1 := by simp
    rw [dif_pos hsum]
    change B.pbwEquiv (MvPolynomial.monomial (Finsupp.single i 1) (f _)) =
      UniversalEnvelopingAlgebra.ι ℤ
        ((SymmetricPower.degreeOneLinearEquiv (adaptedBasis n L data hn))
          (f (Finsupp.single i 1) •
            SymmetricPower.monomialBasis (adaptedBasis n L data hn) 1
              (exponentSym n L data hn 1 (Finsupp.single i 1) hsum)))
    have hs : exponentSym n L data hn 1 (Finsupp.single i 1) hsum =
        Sym.oneEquiv i := by
      apply Subtype.ext
      simp [exponentSym]
    rw [hs, map_zsmul,
      SymmetricPower.degreeOneLinearEquiv_monomialBasis, map_zsmul]
    rw [B.pbwEquiv_monomial, LieRings.PBW.orderedMonomial_single]
    rfl
  · rw [if_neg he, fullRightSymbol_pbwMonomial, dif_neg]
    · simp [pbwPrimitive]
    · simpa [LieRings.PBW.WeightedBasis.factorNumber] using he

/-- Relation rows obtained from the grouped one-factor wall. -/
def GoverningWitness.terminalOneRows {a : L}
    (w : GoverningWitness n L data a) :
    (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ :=
  (GoverningWitness.provenancedTerminalOne n L data hn w).sum
    (fun c z ↦ z • Finsupp.single
      (RelationContext.relation n L data hn c.context c.root, 1) 1)

theorem GoverningWitness.terminalPacketWord_terminalOneRows {a : L}
    (w : GoverningWitness n L data a) :
    terminalPacketWord n L data (w.terminalOneRows n L data hn) =
      UniversalEnvelopingAlgebra.ι ℤ
        (w.terminalOneRelation n L data hn : FreeModel n L) := by
  classical
  rw [← terminalPacketWordLinear_apply,
    GoverningWitness.terminalOneRows, map_finsuppSum,
    w.terminalOneRelation_coe n L data hn,
    GoverningWitness.terminalOnePrimitive, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, map_zsmul]
  congr 1
  simp [terminalPacketWordLinear, terminalPacketWord,
    ProvenancedTerminalOne.fullPrimitive]

/-- The original relation-on-the-left rows after the whole one-factor wall
has been removed. -/
def GoverningWitness.externalRows {a : L}
    (w : GoverningWitness n L data a) :
    (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ :=
  w.relationCoefficients - w.terminalOneRows n L data hn

theorem GoverningWitness.terminalPacketWord_externalRows {a : L}
    (w : GoverningWitness n L data a) :
    terminalPacketWord n L data (w.externalRows n L data hn) =
      w.theta - UniversalEnvelopingAlgebra.ι ℤ
        (w.terminalOneRelation n L data hn : FreeModel n L) := by
  rw [← terminalPacketWordLinear_apply,
    GoverningWitness.externalRows, map_sub,
    terminalPacketWordLinear_apply]
  change terminalPacketWord n L data w.relationCoefficients -
      terminalPacketWord n L data (w.terminalOneRows n L data hn) = _
  rw [w.terminalPacketWord_terminalOneRows n L data hn]
  rfl

/-- The grouped external word, equipped with its actual complete PBW
primitive. -/
def GoverningWitness.externalMarkedWord {a : L}
    (w : GoverningWitness n L data a) : TerminalMarkedWord n L data hn where
  word := terminalPacketWord n L data (w.externalRows n L data hn)
  primitive := w.externalPrimitivePreimage n L data hn
  projection_eq := by
    rw [factorProj_one_eq_iota_pbwPrimitive,
      w.terminalPacketWord_externalRows n L data hn, map_sub,
      w.pbwPrimitive_theta n L data hn, pbwPrimitive_iota]
    change UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl n (by omega) w.atilde -
          (w.terminalOneRelation n L data hn : FreeModel n L)) = _
    rfl

@[simp] theorem GoverningWitness.externalMarkedWord_value {a : L}
    (w : GoverningWitness n L data a) :
    (w.externalMarkedWord n L data hn).value =
      data.topEquiv ⟨a, by
        rw [← w.evaluates]
        change evaluation n L data
          (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
            lowerCentralSeries ℤ L n
        rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
        change FreeMetabelian.Evaluation.linear data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
            (FreeMetabelian.Free.incl
              (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
        rw [FreeMetabelian.Evaluation.linear_incl]
        cases n with
        | zero => simp
        | succ t =>
            exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
              data.metabelian
              (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ :=
  w.terminalEval_externalPrimitivePreimage n L data hn

/-! ### The contextual terminal factor-two packet -/

/-- A placed terminal wall, with its genuine full contextual relation, as a
degree-one row of the canonical terminal presentation. -/
def ProvenancedTerminalTwo.chain
    (c : ProvenancedTerminalTwo n L data hn) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  fullRelationToD n L data n (by omega)
      (RelationContext.relation n L data hn c.context c.root) ⊗ₜ[ℤ]
    SymmetricPower.tprod ℤ (fun _ : Fin 1 ↦
      prLE n L n (by omega) (adaptedBasis n L data hn c.factor))

/-- Complete signed factor-two chain on the terminal wall. -/
def GoverningWitness.contextualTerminalChain {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (GoverningWitness.provenancedTerminalTwo n L data hn w).sum
    (fun c z ↦ z • c.chain n L data hn)

/-- The boundary of one terminal wall is its literal projected symmetric PBW
symbol. -/
theorem ProvenancedTerminalTwo.dOne_chain
    (c : ProvenancedTerminalTwo n L data hn) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (c.chain n L data hn) =
      rightSymbol n L data hn 2 n (by omega) c.row.value := by
  rw [ProvenancedTerminalTwo.chain, Koszul.dOne_tmul]
  have hprefix := RelationContext.projectPrefix_relation_eq_markedPrefix
    n L data hn c.context c.root c.mark c.active
  have hsymbol := rightSymbol_basisWord_mul_iota n L data hn n (by omega)
    [c.factor]
    (RelationContext.markedPrefix n L data hn c.context c.root c.mark)
  rw [show (terminalSourcePresentation n L data hn).d
      (fullRelationToD n L data n (by omega)
        (RelationContext.relation n L data hn c.context c.root)) =
      relationPrefix n L data n (by omega)
        (RelationContext.relation n L data hn c.context c.root) by rfl]
  rw [show c.row.value =
      (MarkedRow.basisWord n L data hn [c.factor] *
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.markedPrefix n L data hn
            c.context c.root c.mark)) by
      simp [ProvenancedTerminalTwo.row, ProvenancedRow.value,
        MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word]]
  change SymmetricPower.insert ℤ (A L n) 1
      (relationPrefix n L data n (by omega)
        (RelationContext.relation n L data hn c.context c.root))
      (SymmetricPower.tprod ℤ (fun _ : Fin 1 ↦
        prLE n L n (by omega) (adaptedBasis n L data hn c.factor))) = _
  have htprod : SymmetricPower.tprod ℤ (fun _ : Fin 1 ↦
      prLE n L n (by omega) (adaptedBasis n L data hn c.factor)) =
    SymmetricPower.tprod ℤ (fun j : Fin [c.factor].length ↦
      prLE n L n (by omega)
        (adaptedBasis n L data hn ([c.factor].get j))) := by
    apply congrArg (SymmetricPower.tprod ℤ)
    funext j
    fin_cases j
    rfl
  have hprefix' : relationPrefix n L data n (by omega)
      (RelationContext.relation n L data hn c.context c.root) =
    prLE n L n (by omega)
      (RelationContext.markedPrefix n L data hn
        c.context c.root c.mark) := by
    change prLE n L n (by omega)
        (RelationContext.relation n L data hn c.context c.root : FreeModel n L) = _
    exact hprefix
  calc
    _ = SymmetricPower.insert ℤ (A L n) 1
        (prLE n L n (by omega)
          (RelationContext.markedPrefix n L data hn
            c.context c.root c.mark))
        (SymmetricPower.tprod ℤ (fun _ : Fin 1 ↦
          prLE n L n (by omega) (adaptedBasis n L data hn c.factor))) := by
          rw [hprefix']
    _ = SymmetricPower.insert ℤ (A L n) [c.factor].length
        (prLE n L n (by omega)
          (RelationContext.markedPrefix n L data hn
            c.context c.root c.mark))
        (SymmetricPower.tprod ℤ (fun j : Fin [c.factor].length ↦
          prLE n L n (by omega)
            (adaptedBasis n L data hn ([c.factor].get j)))) := by
          rw [htprod]
          congr
    _ = _ := hsymbol.symm

@[simp] theorem GoverningWitness.dOne_contextualTerminalChain {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.contextualTerminalChain n L data hn) =
      (GoverningWitness.provenancedTerminalTwo n L data hn w).sum
        (fun c z ↦ z • rightSymbol n L data hn 2 n (by omega) c.row.value) := by
  classical
  rw [GoverningWitness.contextualTerminalChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, ProvenancedTerminalTwo.dOne_chain]
  rfl

private def provenancedTerminalTwoFactorSeed
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  match provenancedTerminal? n L data hn r with
  | some (.inr c) => rightSymbol n L data hn 2 n (by omega) c.row.value
  | _ => 0

private def provenancedTerminalTwoFactorLinear :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin 2) (A L n) :=
  Finsupp.linearCombination ℤ
    (provenancedTerminalTwoFactorSeed n L data hn)

private theorem rightSymbol_terminal_decomposition
    (r : ProvenancedRow n L data hn)
    (hr : provenancedExpansion n L data hn r = none) :
    rightSymbol n L data hn 2 n (by omega) r.value =
      provenancedComponentFactorSeed n L data hn 2 n (by omega) r +
        provenancedTerminalTwoFactorSeed n L data hn r := by
  rcases provenanced_terminal_cases n L data hn r hr with
    ⟨rho, c, b, right, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · simp [provenancedComponentFactorSeed,
      provenancedTerminalTwoFactorSeed, provenancedTerminal?]
  · change rightSymbol n L data hn 2 n (by omega)
        (ProvenancedTerminalOne.row n L data hn t).value =
      provenancedComponentFactorSeed n L data hn 2 n (by omega)
          (ProvenancedTerminalOne.row n L data hn t) +
        provenancedTerminalTwoFactorSeed n L data hn
          (ProvenancedTerminalOne.row n L data hn t)
    have hcomp : provenancedComponentFactorSeed n L data hn 2 n (by omega)
        (ProvenancedTerminalOne.row n L data hn t) = 0 := rfl
    have hterm : provenancedTerminalTwoFactorSeed n L data hn
        (ProvenancedTerminalOne.row n L data hn t) = 0 := by
      simp [provenancedTerminalTwoFactorSeed, ProvenancedTerminalOne.row,
        provenancedTerminal?, t.active]
    rw [hcomp, hterm, add_zero]
    rw [show (ProvenancedTerminalOne.row n L data hn t).value =
        (UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.markedPrefix n L data hn
            t.context t.root t.mark)) by
      simp [ProvenancedTerminalOne.row, ProvenancedRow.value,
        MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word]]
    unfold rightSymbol
    rw [LinearMap.comp_apply,
      fullRightSymbol_iota_eq_zero_of_one_lt n L data hn 2 (by omega),
      map_zero]
  · simp [ProvenancedTerminalTwo.row,
      provenancedComponentFactorSeed,
      provenancedTerminalTwoFactorSeed, provenancedTerminal?, t.active]

private theorem GoverningWitness.rightSymbol_theta_terminal_frontier {a : L}
    (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega) w.theta =
      provenancedComponentFactorLinear n L data hn 2 n (by omega)
          (GoverningWitness.provenancedFrontier n L data hn w) +
        provenancedTerminalTwoFactorLinear n L data hn
          (GoverningWitness.provenancedFrontier n L data hn w) := by
  classical
  have heval := GoverningWitness.evaluate_provenancedFrontier
    n L data hn w
  have hsymbol := congrArg (rightSymbol n L data hn 2 n (by omega)) heval
  change rightSymbol n L data hn 2 n (by omega)
      ((GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z • r.value)) =
    rightSymbol n L data hn 2 n (by omega) w.theta at hsymbol
  rw [map_finsuppSum] at hsymbol
  rw [← hsymbol]
  simp only [map_zsmul, provenancedComponentFactorLinear,
    provenancedTerminalTwoFactorLinear,
    Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hrSupport
  have hterminal : provenancedExpansion n L data hn r = none := by
    by_contra hnonterminal
    apply Finsupp.mem_support_iff.mp hrSupport
    rw [GoverningWitness.provenancedFrontier, Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    change (GoverningWitness.provenancedInitial n L data hn w) s *
        (provenancedCollector n L data hn).normalForm s r = 0
    have hz := (provenancedCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
      s r hnonterminal
    rw [hz, mul_zero]
  have hdec := rightSymbol_terminal_decomposition n L data hn r hterminal
  change (GoverningWitness.provenancedFrontier n L data hn w) r •
      rightSymbol n L data hn 2 n (by omega) r.value =
    (GoverningWitness.provenancedFrontier n L data hn w) r •
        provenancedComponentFactorSeed n L data hn 2 n (by omega) r +
      (GoverningWitness.provenancedFrontier n L data hn w) r •
        provenancedTerminalTwoFactorSeed n L data hn r
  rw [hdec, zsmul_add]

/-- Complete factor-two vertical defect of the contextual trace. -/
def GoverningWitness.terminalFactorDefect {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (GoverningWitness.provenancedCells n L data hn w).sum
    (fun c z ↦ z • c.factorEdge n L data hn 2 n (by omega))

private theorem GoverningWitness.componentTerminalFactor_eq_defect {a : L}
    (w : GoverningWitness n L data a) :
    provenancedComponentFactorLinear n L data hn 2 n (by omega)
        (GoverningWitness.provenancedFrontier n L data hn w) =
      w.terminalFactorDefect n L data hn := by
  classical
  rw [GoverningWitness.provenancedFrontier,
    GoverningWitness.terminalFactorDefect,
    GoverningWitness.provenancedCells]
  change provenancedComponentFactorLinear n L data hn 2 n (by omega)
      ((GoverningWitness.provenancedInitial n L data hn w).sum
        (fun r z ↦ z • (provenancedCollector n L data hn).normalForm r)) =
    provenancedCellFactorLinear n L data hn 2 n (by omega)
      ((GoverningWitness.provenancedInitial n L data hn w).sum
        (fun r z ↦ z • provenancedTrace n L data hn r))
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul]
  change w.provenancedInitial n L data hn r •
      normalFormProvenancedComponentFactor n L data hn 2 n (by omega) r =
    w.provenancedInitial n L data hn r •
      provenancedTraceFactor n L data hn 2 n (by omega) r
  rw [normalFormProvenancedComponentFactor_eq_trace]
  have hseed : provenancedComponentFactorSeed n L data hn
      2 n (by omega) r = 0 := by
    have hrne := Finsupp.mem_support_iff.mp hr
    rw [GoverningWitness.provenancedInitial, Finsupp.sum_apply] at hrne
    cases r with
    | component root context mark left right =>
        exfalso
        apply hrne
        apply Finset.sum_eq_zero
        intro p hp
        change w.relationCoefficients p *
          (provenancedRowsOfRightFactor n L data hn p.1 p.2)
            (.component root context mark left right) = 0
        rw [show (provenancedRowsOfRightFactor n L data hn p.1 p.2)
            (.component root context mark left right) = 0 by
          rw [provenancedRowsOfRightFactor, Finsupp.sum_apply]
          apply Finset.sum_eq_zero
          intro e he
          simp, mul_zero]
    | marked => rfl
  rw [hseed, zero_add]

private theorem GoverningWitness.terminalTwoFactorFrontier_eq {a : L}
    (w : GoverningWitness n L data a) :
    provenancedTerminalTwoFactorLinear n L data hn
        (GoverningWitness.provenancedFrontier n L data hn w) =
      (GoverningWitness.provenancedTerminalTwo n L data hn w).sum
        (fun c z ↦ z • rightSymbol n L data hn 2 n (by omega) c.row.value) := by
  classical
  rw [GoverningWitness.provenancedTerminalTwo]
  change provenancedTerminalTwoFactorLinear n L data hn
      (GoverningWitness.provenancedFrontier n L data hn w) =
    Finsupp.linearCombination ℤ
      (fun c ↦ rightSymbol n L data hn 2 n (by omega) c.row.value)
      ((GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z • provenancedTerminalTwoPart n L data hn r))
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul]
  cases hc : provenancedTerminal? n L data hn r with
  | none =>
      simp [provenancedTerminalTwoPart,
        provenancedTerminalTwoFactorSeed, hc]
      module
  | some t =>
      cases t with
      | inl c =>
          simp [provenancedTerminalTwoPart,
            provenancedTerminalTwoFactorSeed, hc]
          module
      | inr c =>
          simp [provenancedTerminalTwoPart,
            provenancedTerminalTwoFactorSeed, hc]
          module

/-- Exact terminal boundary equation.  The sole remaining obstruction to
being a cycle is the displayed vertical factor-two defect. -/
theorem GoverningWitness.dOne_contextualTerminalChain_eq_neg_defect {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.contextualTerminalChain n L data hn) =
      -w.terminalFactorDefect n L data hn := by
  have hfront := w.rightSymbol_theta_terminal_frontier n L data hn
  rw [rightSymbol_theta_terminal_eq_zero n L data hn w,
    w.componentTerminalFactor_eq_defect n L data hn,
    w.terminalTwoFactorFrontier_eq n L data hn] at hfront
  rw [w.dOne_contextualTerminalChain n L data hn]
  exact eq_neg_of_add_eq_zero_right hfront.symm

/-! ### Exact terminal support of contextual component edges -/

/-- A contextual component edge is homogeneous in the sum of the weight of
its displayed left word and its active relation weight.  Consequently its
PBW primitive has no terminal coordinate off that one diagonal. -/
theorem ProvenancedCell.weightProject_primitive_eq_zero_of_ne
    (c : ProvenancedCell n L data hn)
    (hne : (c.left.map (adaptedWeightedBasis n L data hn).weight).sum +
        c.activeWeight n L data hn ≠ n + 1) :
    FreeMetabelian.Free.weightProject n (by omega)
        (c.primitive n L data hn) = 0 := by
  classical
  let B := adaptedWeightedBasis n L data hn
  let x := RelationContext.component n L data hn c.context c.root c.mark
  have hrow : B.proj (n + 1) 1 c.componentRow.value = 0 := by
    rw [show c.componentRow.value =
      (MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ x) by
      simp [ProvenancedCell.componentRow, ProvenancedRow.value,
        MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word, x]]
    rw [← (adaptedBasis n L data hn).sum_repr x, map_sum,
      Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_zsmul, mul_smul_comm, map_zsmul]
    by_cases hiw : B.weight i = c.activeWeight n L data hn
    · have hword : MarkedRow.basisWord n L data hn c.left *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) =
          MarkedRow.basisWord n L data hn (c.left ++ [i]) := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
      rw [hword]
      have hweight :
          (((c.left ++ [i]).map B.weight).sum) ≠ n + 1 := by
        simpa [List.map_append, hiw, B] using hne
      have hzero : B.proj (n + 1) 1
          (MarkedRow.basisWord n L data hn (c.left ++ [i])) = 0 := by
        change B.proj (n + 1) 1
          (LieRings.PBW.basisWord ℤ (FreeModel n L)
            (AdaptedIndex n L data hn) B.basis (c.left ++ [i])) = 0
        exact B.proj_basisWord_eq_zero_of_weight_ne
          (c.left ++ [i]) (n + 1) 1 hweight
      rw [hzero, smul_zero]
    · have hcoeff : ((adaptedBasis n L data hn).repr x) i = 0 := by
        change ((pieceAdaptedBasis n L data hn i.1).repr (x i.1)) i.2 = 0
        have hx : x i.1 = 0 := by
          apply RelationContext.component_apply_eq_zero_of_ne
            n L data hn c.context c.root c.mark c.mark_pos i.1
          simpa [B, adaptedWeightedBasis,
            ProvenancedCell.activeWeight] using hiw
        rw [hx, map_zero]
        rfl
      rw [hcoeff, zero_smul]
  have hprimitive : B.proj (n + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ (c.primitive n L data hn)) = 0 := by
    change B.proj (n + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ
        (pbwPrimitive n L data hn c.componentRow.value)) = 0
    rw [← factorProj_one_eq_iota_pbwPrimitive n L data hn]
    rw [B.proj_factorProj]
    exact hrow
  rw [adapted_proj_top_iota n L data hn] at hprimitive
  have hnlt : n < n + 1 := Nat.lt_succ_self n
  have hfree : FreeMetabelian.Free.weightIncl n hnlt
      (FreeMetabelian.Free.weightProject n hnlt
        (c.primitive n L data hn)) = 0 := by
    apply canonicalMap_injective_of_freeModulePBW
      ℤ (FreeModel n L) (AdaptedIndex n L data hn)
      B.basis
      (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
        B.basis)
    simpa using hprimitive
  have hp := congrArg (FreeMetabelian.Free.weightProject n hnlt) hfree
  simpa using hp

/-! ### Complete PBW normalization of contextual component rows

The contextual collector deliberately moves an exposed homogeneous component
without forgetting the full relation which produced it.  Its terminal
component rows are therefore not yet PBW normal forms.  For the last row
calculation we now expand that one homogeneous component in the fixed adapted
basis and collect it through its two (already ordered) neighbour lists.  The
root relation, bracket context, and mark remain attached to every correction.
-/

/-- One basis summand of a contextual component, with all of its relation
provenance retained. -/

def ProvenancedRow.ordinaryNeighbors :
    ProvenancedRow n L data hn → List (AdaptedIndex n L data hn)
  | .marked _ _ _ left right | .component _ _ _ left right => left ++ right

theorem provenancedExpansion_ordinaryNeighbors_pairwise
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs)
    (hr : (r.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·)) :
    ∀ q ∈ qs, (q.2.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·) := by
  classical
  intro q hq
  cases r with
  | component root context mark left right =>
      simp only [provenancedExpansion] at h
      split at h
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at h
        subst qs
        have hleftEq : left = leftRev.reverse ++ [x] := by
          have hrev := congrArg List.reverse hleft
          simpa using hrev
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · simpa [ProvenancedRow.ordinaryNeighbors, hleftEq,
            List.append_assoc] using hr
        · have hsub : List.Sublist (leftRev.reverse ++ right)
              (left ++ right) := by
            rw [hleftEq, List.append_assoc]
            exact List.Sublist.append (List.Sublist.refl leftRev.reverse)
              (List.sublist_cons_of_sublist x (List.Sublist.refl right))
          exact hr.sublist hsub
  | marked root context mark left right =>
      cases right with
      | cons x right =>
          simp only [provenancedExpansion] at h
          rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · simpa [ProvenancedRow.ordinaryNeighbors,
              List.append_assoc] using hr
          · have hsub : List.Sublist (left ++ right) (left ++ x :: right) :=
              List.Sublist.append (List.Sublist.refl left)
                (List.sublist_cons_of_sublist x (List.Sublist.refl right))
            exact hr.sublist hsub
      | nil =>
          simp only [provenancedExpansion] at h
          split at h
          · rw [Option.some.injEq] at h
            subst qs
            simp at hq
          · split at h
            · contradiction
            · rw [Option.some.injEq] at h
              subst qs
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
              rcases hq with rfl | rfl <;>
                simpa [ProvenancedRow.ordinaryNeighbors] using hr

private theorem provenancedCell_left_pairwise_of_row
    (r : ProvenancedRow n L data hn)
    (hr : (r.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·))
    (c : ProvenancedCell n L data hn)
    (hc : provenancedCell? n L data hn r = some c) :
    c.left.Pairwise (· ≤ ·) := by
  cases r with
  | component => simp [provenancedCell?] at hc
  | marked root context mark left right =>
      simp only [provenancedCell?] at hc
      split at hc <;> try contradiction
      split at hc <;> try contradiction
      split at hc <;> try contradiction
      have hdata := Option.some.inj hc
      subst c
      simpa [ProvenancedRow.ordinaryNeighbors, *] using hr

private theorem provenancedTrace_cell_left_pairwise
    (r : ProvenancedRow n L data hn)
    (hr : (r.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·))
    (c : ProvenancedCell n L data hn)
    (hc : provenancedTrace n L data hn r c ≠ 0) :
    c.left.Pairwise (· ≤ ·) := by
  classical
  let C := provenancedCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : provenancedExpansion n L data hn r with
      | none =>
          rw [provenancedTrace_eq_of_expansion_none n L data hn r hexp] at hc
          have hcell := provenancedCell?_eq_none_of_expansion_eq_none
            n L data hn r hexp
          simp [hcell] at hc
      | some rows =>
          rw [provenancedTrace_eq_of_expansion_some
            n L data hn r rows hexp, Finsupp.add_apply] at hc
          by_cases hhere : (match provenancedCell? n L data hn r with
              | none => (0 : ProvenancedCell n L data hn →₀ ℤ)
              | some d => Finsupp.single d 1) c ≠ 0
          · cases hcell : provenancedCell? n L data hn r with
            | none => simp [hcell] at hhere
            | some d =>
                have hdc : d = c := by
                  by_contra hne
                  have hz : (Finsupp.single d 1 :
                      ProvenancedCell n L data hn →₀ ℤ) c = 0 := by
                    simp [hne]
                  exact hhere (by simpa [hcell] using hz)
                subst d
                exact provenancedCell_left_pairwise_of_row
                  n L data hn r hr c hcell
          · have hchildren :
                ((rows.attach.map fun q ↦ q.1.1 •
                    provenancedTrace n L data hn q.1.2).sum) c ≠ 0 := by
              cases hcell : provenancedCell? n L data hn r with
              | none => simpa [hcell] using hc
              | some d =>
                  have hdc : d ≠ c := by
                    intro heq
                    subst d
                    simp [hcell] at hhere
                  simpa [hcell, hdc] using hc
            have hexists : ∃ z ∈
                (rows.attach.map fun q ↦ q.1.1 •
                  provenancedTrace n L data hn q.1.2), z c ≠ 0 := by
              by_contra hall
              push Not at hall
              apply hchildren
              have sum_apply (xs : List
                  (ProvenancedCell n L data hn →₀ ℤ)) :
                  xs.sum c = (xs.map fun f ↦ f c).sum := by
                induction xs with
                | nil => simp
                | cons x xs ihxs => simp [ihxs]
              rw [sum_apply]
              apply List.sum_eq_zero
              intro z hz
              rw [List.mem_map] at hz
              obtain ⟨f, hf, rfl⟩ := hz
              exact hall f hf
            obtain ⟨z, hz, hzc⟩ := hexists
            rw [List.mem_map] at hz
            obtain ⟨q, hq, rfl⟩ := hz
            have hchild : provenancedTrace n L data hn q.1.2 c ≠ 0 := by
              intro hzero
              simp [hzero] at hzc
            have hordered := provenancedExpansion_ordinaryNeighbors_pairwise
              n L data hn hexp hr q.1 q.2
            exact ih q.1.2 (C.decreases hexp q.1 q.2)
              hordered hchild

/-- Public aggregate form of the ordered-neighbour invariant.  A provenance
trace started from an ordered ordinary word can expose only truncation cells
whose displayed left word is still ordered. -/
theorem provenancedTrace_cell_left_pairwise_of_append
    (r : ProvenancedRow n L data hn)
    (hr : match r with
      | .marked _ _ _ left right =>
          (left ++ right).Pairwise (· ≤ ·)
      | .component _ _ _ left right =>
          (left ++ right).Pairwise (· ≤ ·))
    (c : ProvenancedCell n L data hn)
    (hc : provenancedTrace n L data hn r c ≠ 0) :
    c.left.Pairwise (· ≤ ·) := by
  cases r with
  | marked root context mark left right =>
      apply provenancedTrace_cell_left_pairwise n L data hn
        (.marked root context mark left right)
          (by simpa [ProvenancedRow.ordinaryNeighbors] using hr) c hc
  | component root context mark left right =>
      apply provenancedTrace_cell_left_pairwise n L data hn
        (.component root context mark left right)
          (by simpa [ProvenancedRow.ordinaryNeighbors] using hr) c hc

theorem exponentWord_pairwise
    (e : AdaptedIndex n L data hn →₀ ℕ) :
    (exponentWord n L data hn e).Pairwise (· ≤ ·) := by
  exact Multiset.pairwise_sort _ _

private theorem provenancedRowsOfRightFactor_ordinaryNeighbors_pairwise
    (rho : Relations n L data) (u : UEA ℤ (FreeModel n L))
    (r : ProvenancedRow n L data hn)
    (hr : provenancedRowsOfRightFactor n L data hn rho u r ≠ 0) :
    (r.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·) := by
  classical
  rw [provenancedRowsOfRightFactor, Finsupp.sum_apply] at hr
  have hexists : ∃ e ∈
      ((adaptedWeightedBasis n L data hn).pbwEquiv.symm u).support,
      (Finsupp.single
        (.marked rho .hole ⟨n + 1, by omega⟩ []
          (exponentWord n L data hn e))
        (((adaptedWeightedBasis n L data hn).pbwEquiv.symm u) e)) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun e he ↦ hall e he))
  obtain ⟨e, he, her⟩ := hexists
  have hre : r = .marked rho .hole ⟨n + 1, by omega⟩ []
      (exponentWord n L data hn e) := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at her
  subst r
  simpa [ProvenancedRow.ordinaryNeighbors] using
    (exponentWord_pairwise n L data hn e)

private theorem GoverningWitness.provenancedInitial_ordinaryNeighbors_pairwise
    {a : L} (w : GoverningWitness n L data a)
    (r : ProvenancedRow n L data hn)
    (hr : w.provenancedInitial n L data hn r ≠ 0) :
    (r.ordinaryNeighbors n L data hn).Pairwise (· ≤ ·) := by
  classical
  rw [GoverningWitness.provenancedInitial, Finsupp.sum_apply] at hr
  have hexists : ∃ p ∈ w.relationCoefficients.support,
      (w.relationCoefficients p •
        provenancedRowsOfRightFactor n L data hn p.1 p.2) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun p hp ↦ hall p hp))
  obtain ⟨p, hp, hpr⟩ := hexists
  have hrow : provenancedRowsOfRightFactor n L data hn p.1 p.2 r ≠ 0 := by
    intro hzero
    simp [hzero] at hpr
  exact provenancedRowsOfRightFactor_ordinaryNeighbors_pairwise
    n L data hn p.1 p.2 r hrow

theorem GoverningWitness.provenancedCell_left_pairwise
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.provenancedCells n L data hn c ≠ 0) :
    c.left.Pairwise (· ≤ ·) := by
  classical
  rw [GoverningWitness.provenancedCells, Finsupp.sum_apply] at hc
  have hexists : ∃ r ∈ (w.provenancedInitial n L data hn).support,
      (w.provenancedInitial n L data hn r •
        provenancedTrace n L data hn r) c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc (Finset.sum_eq_zero (fun r hr ↦ hall r hr))
  obtain ⟨r, hr, hrc⟩ := hexists
  have htrace : provenancedTrace n L data hn r c ≠ 0 := by
    intro hzero
    simp [hzero] at hrc
  exact provenancedTrace_cell_left_pairwise n L data hn r
    (w.provenancedInitial_ordinaryNeighbors_pairwise n L data hn r
      (Finsupp.mem_support_iff.mp hr)) c htrace

structure ComponentPBWState where
  root : Relations n L data
  context : RelationContext n L data hn
  mark : Fin (n + 2)
  distinguished : AdaptedIndex n L data hn
  left : List (AdaptedIndex n L data hn)
  right : List (AdaptedIndex n L data hn)

noncomputable instance : DecidableEq (ComponentPBWState n L data hn) :=
  Classical.decEq _

namespace ComponentPBWState

/-- The literal enveloping word represented by a component state. -/
def value (s : ComponentPBWState n L data hn) :
    UEA ℤ (FreeModel n L) :=
  MarkedRow.basisWord n L data hn s.left *
    UniversalEnvelopingAlgebra.ι ℤ
      (adaptedBasis n L data hn s.distinguished) *
    MarkedRow.basisWord n L data hn s.right

/-- Number of PBW factors in the represented word. -/
def factorCount (s : ComponentPBWState n L data hn) : ℕ :=
  s.left.length + 1 + s.right.length

/-- The complete basis word, including the distinguished component. -/
def word (s : ComponentPBWState n L data hn) :
    List (AdaptedIndex n L data hn) :=
  s.left ++ s.distinguished :: s.right

/-- The two-component termination measure: corrections lower factor number,
and the factor-preserving branch lowers the literal PBW inversion count. -/
def measure (s : ComponentPBWState n L data hn) : ℕ × ℕ :=
  (s.factorCount n L data hn,
    rowInversionCount n L data hn (s.word n L data hn))

end ComponentPBWState

def componentPBWBracketChildren
    (s : ComponentPBWState n L data hn)
    (newContext : RelationContext n L data hn)
    (x y : AdaptedIndex n L data hn)
    (left right : List (AdaptedIndex n L data hn)) :
    List (ℤ × ComponentPBWState n L data hn) :=
  (adaptedCoordinates n L data hn
      ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn y⁆).map
    (fun q ↦ (q.1, ⟨s.root, newContext, s.mark, q.2, left, right⟩))

/-- Deterministic adjacent collection of the distinguished component. -/
noncomputable def componentPBWExpansion
    (s : ComponentPBWState n L data hn) :
    Option (List (ℤ × ComponentPBWState n L data hn)) :=
  match hleft : s.left.reverse with
  | x :: leftRev =>
      if hxi : s.distinguished < x then
        some ((1, ⟨s.root, s.context, s.mark, s.distinguished,
            leftRev.reverse, x :: s.right⟩) ::
          componentPBWBracketChildren n L data hn s
            (RelationContext.lieRight s.context x) x s.distinguished
              leftRev.reverse s.right)
      else
        match s.right with
        | [] => none
        | y :: right =>
            if hyi : y < s.distinguished then
              some ((1, ⟨s.root, s.context, s.mark, s.distinguished,
                  s.left ++ [y], right⟩) ::
                componentPBWBracketChildren n L data hn s
                  (RelationContext.lieRight s.context y)
                    s.distinguished y s.left right)
            else none
  | [] =>
      match s.right with
      | [] => none
      | y :: right =>
          if hyi : y < s.distinguished then
            some ((1, ⟨s.root, s.context, s.mark, s.distinguished,
                s.left ++ [y], right⟩) ::
              componentPBWBracketChildren n L data hn s
                (RelationContext.lieRight s.context y)
                  s.distinguished y s.left right)
          else none

private theorem componentPBWBracketChildren_factorCount
    (s : ComponentPBWState n L data hn)
    (newContext : RelationContext n L data hn)
    (x y : AdaptedIndex n L data hn)
    (left right : List (AdaptedIndex n L data hn))
    (q : ℤ × ComponentPBWState n L data hn)
    (hq : q ∈ componentPBWBracketChildren n L data hn s newContext
      x y left right) :
    q.2.factorCount n L data hn = left.length + 1 + right.length := by
  simp only [componentPBWBracketChildren, List.mem_map] at hq
  obtain ⟨z, hz, rfl⟩ := hq
  simp [ComponentPBWState.factorCount]

private theorem componentPBWExpansion_decreases
    {s : ComponentPBWState n L data hn}
    {qs : List (ℤ × ComponentPBWState n L data hn)}
    (h : componentPBWExpansion n L data hn s = some qs) :
    ∀ q ∈ qs, Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
      (q.2.measure n L data hn) (s.measure n L data hn) := by
  classical
  intro q hq
  unfold componentPBWExpansion at h
  split at h
  · rename_i x leftRev hleft
    split at h
    · rename_i hxi
      rw [Option.some.injEq] at h
      subst qs
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp only [Prod.snd, ComponentPBWState.measure,
          ComponentPBWState.factorCount, ComponentPBWState.word]
        have hleftEq : s.left = leftRev.reverse ++ [x] := by
          have hr := congrArg List.reverse hleft
          simpa using hr
        rw [hleftEq]
        have hcount : leftRev.reverse.length + 1 + (x :: s.right).length =
            (leftRev.reverse ++ [x]).length + 1 + s.right.length := by
          simp
          omega
        rw [hcount]
        apply Prod.Lex.right
        have hinv := rowInversionCount_swap n L data hn
          leftRev.reverse s.right x s.distinguished hxi
        have hlt : rowInversionCount n L data hn
              (leftRev.reverse ++ s.distinguished :: x :: s.right) <
            rowInversionCount n L data hn
              (leftRev.reverse ++ x :: s.distinguished :: s.right) := by
          omega
        simpa [List.append_assoc] using hlt
      · apply Prod.Lex.left
        rw [componentPBWBracketChildren_factorCount n L data hn
          s (RelationContext.lieRight s.context x) x s.distinguished
            leftRev.reverse s.right q hq]
        change leftRev.reverse.length + 1 + s.right.length <
          s.left.length + 1 + s.right.length
        have hleftEq : s.left = leftRev.reverse ++ [x] := by
          have hr := congrArg List.reverse hleft
          simpa using hr
        rw [hleftEq]
        simp
    · rename_i hnxi
      split at h
      · contradiction
      · rename_i y right hright
        split at h
        · rename_i hyi
          rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · simp only [Prod.snd, ComponentPBWState.measure,
              ComponentPBWState.factorCount, ComponentPBWState.word]
            rw [hright]
            have hcount : (s.left ++ [y]).length + 1 + right.length =
                s.left.length + 1 + (y :: right).length := by
              simp
              omega
            rw [hcount]
            apply Prod.Lex.right
            have hinv := rowInversionCount_swap n L data hn s.left right
              s.distinguished y hyi
            have hlt : rowInversionCount n L data hn
                  (s.left ++ y :: s.distinguished :: right) <
                rowInversionCount n L data hn
                  (s.left ++ s.distinguished :: y :: right) := by
              omega
            simpa [List.append_assoc] using hlt
          · apply Prod.Lex.left
            rw [componentPBWBracketChildren_factorCount n L data hn
              s (RelationContext.lieRight s.context y)
                s.distinguished y s.left right q hq]
            change s.left.length + 1 + right.length <
              s.left.length + 1 + s.right.length
            rw [hright]
            simp
        · contradiction
  · rename_i hleft
    split at h
    · contradiction
    · rename_i y right hright
      split at h
      · rename_i hyi
        rw [Option.some.injEq] at h
        subst qs
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · simp only [Prod.snd, ComponentPBWState.measure,
            ComponentPBWState.factorCount, ComponentPBWState.word]
          have hleftNil : s.left = [] := by
            have hr := congrArg List.reverse hleft
            simpa using hr
          rw [hleftNil, hright]
          have hcount :
              ((([] : List (AdaptedIndex n L data hn)) ++ [y]).length +
                  1 + right.length) =
                ([] : List (AdaptedIndex n L data hn)).length + 1 +
                  (y :: right).length := by
            simp
            omega
          rw [hcount]
          apply Prod.Lex.right
          have hinv := rowInversionCount_swap n L data hn [] right
            s.distinguished y hyi
          simp only [List.nil_append] at hinv
          have hlt : rowInversionCount n L data hn
                (y :: s.distinguished :: right) <
              rowInversionCount n L data hn
                (s.distinguished :: y :: right) := by omega
          simpa [List.append_assoc] using hlt
        · apply Prod.Lex.left
          rw [componentPBWBracketChildren_factorCount n L data hn
            s (RelationContext.lieRight s.context y)
              s.distinguished y s.left right q hq]
          change s.left.length + 1 + right.length <
            s.left.length + 1 + s.right.length
          rw [hright]
          simp
      · contradiction

private theorem componentPBWBracketChildren_value
    (s : ComponentPBWState n L data hn)
    (newContext : RelationContext n L data hn)
    (x y : AdaptedIndex n L data hn)
    (left right : List (AdaptedIndex n L data hn)) :
    ((componentPBWBracketChildren n L data hn s newContext x y left right).map
      (fun q ↦ q.1 • q.2.value n L data hn)).sum =
      MarkedRow.basisWord n L data hn left *
        UniversalEnvelopingAlgebra.ι ℤ
          ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn y⁆ *
        MarkedRow.basisWord n L data hn right := by
  classical
  let bracket : FreeModel n L :=
    ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn y⁆
  let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    { toFun := fun z ↦
        MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ z *
          MarkedRow.basisWord n L data hn right
      map_add' := by intro z w; rw [map_add, mul_add, add_mul]
      map_smul' := by
        intro z w
        rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
        rfl }
  have hcoordinates := congrArg
    context
    (adaptedCoordinates_sum n L data hn bracket)
  rw [map_list_sum] at hcoordinates
  calc
    _ = ((adaptedCoordinates n L data hn bracket).map (fun q ↦
          q.1 • context (adaptedBasis n L data hn q.2))).sum := by
      unfold componentPBWBracketChildren
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      rfl
    _ = ((adaptedCoordinates n L data hn bracket).map (fun q ↦
          context (q.1 • adaptedBasis n L data hn q.2))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      rw [map_zsmul]
    _ = context bracket := by
      simpa only [List.map_map, Function.comp_apply] using hcoordinates
    _ = _ := rfl

private theorem componentPBWExpansion_preserves
    {s : ComponentPBWState n L data hn}
    {qs : List (ℤ × ComponentPBWState n L data hn)}
    (h : componentPBWExpansion n L data hn s = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value n L data hn).sum =
      s.value n L data hn := by
  classical
  unfold componentPBWExpansion at h
  split at h
  · rename_i x leftRev hleft
    split at h
    · rename_i hxi
      rw [Option.some.injEq] at h
      subst qs
      have hleftEq : s.left = leftRev.reverse ++ [x] := by
        have hr := congrArg List.reverse hleft
        simpa using hr
      simp only [List.map_cons, List.sum_cons, one_smul]
      rw [componentPBWBracketChildren_value]
      unfold ComponentPBWState.value
      rw [hleftEq]
      have hleftWord : MarkedRow.basisWord n L data hn
          (leftRev.reverse ++ [x]) =
          MarkedRow.basisWord n L data hn leftRev.reverse *
            UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn x) := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
      have hrightWord : MarkedRow.basisWord n L data hn (x :: s.right) =
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn x) *
            MarkedRow.basisWord n L data hn s.right := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      rw [hleftWord, hrightWord]
      have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
        (FreeModel n L) (adaptedBasis n L data hn x)
          (adaptedBasis n L data hn s.distinguished)
      calc
        _ = MarkedRow.basisWord n L data hn leftRev.reverse *
            (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn s.distinguished) *
              UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) +
              UniversalEnvelopingAlgebra.ι ℤ
                ⁅adaptedBasis n L data hn x,
                  adaptedBasis n L data hn s.distinguished⁆) *
            MarkedRow.basisWord n L data hn s.right := by noncomm_ring
        _ = _ := by rw [← hswap]; noncomm_ring
    · split at h
      · contradiction
      · rename_i y right hright
        split at h
        · rw [Option.some.injEq] at h
          subst qs
          simp only [List.map_cons, List.sum_cons, one_smul]
          rw [componentPBWBracketChildren_value]
          unfold ComponentPBWState.value
          rw [hright]
          have hleftWord : MarkedRow.basisWord n L data hn (s.left ++ [y]) =
              MarkedRow.basisWord n L data hn s.left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn y) := by
            simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word, List.map_append, adaptedWeightedBasis]
          have hrightWord : MarkedRow.basisWord n L data hn (y :: right) =
              UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn y) *
                MarkedRow.basisWord n L data hn right := by
            simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word, adaptedWeightedBasis]
          rw [hleftWord, hrightWord]
          have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
            (FreeModel n L) (adaptedBasis n L data hn s.distinguished)
              (adaptedBasis n L data hn y)
          calc
            _ = MarkedRow.basisWord n L data hn s.left *
                (UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn y) *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn s.distinguished) +
                  UniversalEnvelopingAlgebra.ι ℤ
                    ⁅adaptedBasis n L data hn s.distinguished,
                      adaptedBasis n L data hn y⁆) *
                MarkedRow.basisWord n L data hn right := by noncomm_ring
            _ = _ := by rw [← hswap]; noncomm_ring
        · contradiction
  · rename_i hleft
    split at h
    · contradiction
    · rename_i y right hright
      split at h
      · rw [Option.some.injEq] at h
        subst qs
        simp only [List.map_cons, List.sum_cons, one_smul]
        rw [componentPBWBracketChildren_value]
        unfold ComponentPBWState.value
        have hleftNil : s.left = [] := by
          have hr := congrArg List.reverse hleft
          simpa using hr
        rw [hleftNil, hright]
        have hrightWord : MarkedRow.basisWord n L data hn (y :: right) =
            UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn y) *
              MarkedRow.basisWord n L data hn right := by
          simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, adaptedWeightedBasis]
        rw [hrightWord]
        have hyWord : MarkedRow.basisWord n L data hn ([] ++ [y]) =
            UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn y) := by
          simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, adaptedWeightedBasis]
        rw [hyWord]
        simp only [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_nil, List.prod_nil, one_mul]
        have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
          (FreeModel n L) (adaptedBasis n L data hn s.distinguished)
            (adaptedBasis n L data hn y)
        calc
          _ = (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn y) *
              UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn s.distinguished) +
              UniversalEnvelopingAlgebra.ι ℤ
                ⁅adaptedBasis n L data hn s.distinguished,
                  adaptedBasis n L data hn y⁆) *
              MarkedRow.basisWord n L data hn right := by noncomm_ring
          _ = _ := by rw [← hswap]; noncomm_ring
      · contradiction

/-- The finite component PBW collector. -/
def componentPBWCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (ComponentPBWState n L data hn) (UEA ℤ (FreeModel n L)) where
  relation x y := Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
    (x.measure n L data hn) (y.measure n L data hn)
  wellFounded := InvImage.wf (ComponentPBWState.measure n L data hn)
    (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  expansion := componentPBWExpansion n L data hn
  value := ComponentPBWState.value n L data hn
  decreases := componentPBWExpansion_decreases n L data hn
  preserves := componentPBWExpansion_preserves n L data hn

/-! The distinguished coordinate in a component state always has the active
weight recorded by its mark and relation context.  This provenance invariant
is needed below independently of the particular signed ledger from which the
component cell arose. -/

private def ComponentPBWState.distinguishedWeightInvariant
    (s : ComponentPBWState n L data hn) : Prop :=
  (adaptedWeightedBasis n L data hn).weight s.distinguished =
    s.mark.val + RelationContext.weight n L data hn s.context

/-! Besides the active weight of the distinguished coordinate, collection
preserves the literal provenance of a component cell.  An ordinary factor
moved into a bracket correction disappears from the PBW word and is recorded
with exactly the same weight in the relation context. -/

private def ComponentPBWState.cellProvenanceInvariant
    (c : ProvenancedCell n L data hn)
    (s : ComponentPBWState n L data hn) : Prop :=
  s.root = c.root ∧ s.mark = c.mark ∧
    RelationContext.weight n L data hn s.context +
          (s.left.map (adaptedWeightedBasis n L data hn).weight).sum +
          (s.right.map (adaptedWeightedBasis n L data hn).weight).sum =
      RelationContext.weight n L data hn c.context +
        (c.left.map (adaptedWeightedBasis n L data hn).weight).sum ∧
    (s.left ++ s.right).Sublist c.left

private theorem componentPBWBracketChildren_cellProvenanceInvariant
    (c : ProvenancedCell n L data hn)
    (s : ComponentPBWState n L data hn)
    (newContext : RelationContext n L data hn)
    (x y : AdaptedIndex n L data hn)
    (left right : List (AdaptedIndex n L data hn))
    (hs : s.cellProvenanceInvariant n L data hn c)
    (hweight :
      RelationContext.weight n L data hn newContext +
            (left.map (adaptedWeightedBasis n L data hn).weight).sum +
            (right.map (adaptedWeightedBasis n L data hn).weight).sum =
        RelationContext.weight n L data hn s.context +
          (s.left.map (adaptedWeightedBasis n L data hn).weight).sum +
          (s.right.map (adaptedWeightedBasis n L data hn).weight).sum)
    (hsub : (left ++ right).Sublist (s.left ++ s.right))
    (q : ℤ × ComponentPBWState n L data hn)
    (hq : q ∈ componentPBWBracketChildren n L data hn s newContext
      x y left right) :
    q.2.cellProvenanceInvariant n L data hn c := by
  simp only [componentPBWBracketChildren, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact ⟨hs.1, hs.2.1, hweight.trans hs.2.2.1,
    hsub.trans hs.2.2.2⟩

private theorem componentPBWExpansion_preserves_cellProvenanceInvariant
    (c : ProvenancedCell n L data hn)
    {s : ComponentPBWState n L data hn}
    {qs : List (ℤ × ComponentPBWState n L data hn)}
    (h : componentPBWExpansion n L data hn s = some qs)
    (hs : s.cellProvenanceInvariant n L data hn c) :
    ∀ q ∈ qs, q.2.cellProvenanceInvariant n L data hn c := by
  classical
  intro q hq
  unfold componentPBWExpansion at h
  split at h
  · rename_i x leftRev hleft
    have hleftEq : s.left = leftRev.reverse ++ [x] := by
      have hrev := congrArg List.reverse hleft
      simpa using hrev
    split at h
    · rw [Option.some.injEq] at h
      subst qs
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · simpa [ComponentPBWState.cellProvenanceInvariant, hleftEq,
          List.map_append, Nat.add_assoc] using hs
      · apply componentPBWBracketChildren_cellProvenanceInvariant
          n L data hn c s (RelationContext.lieRight s.context x)
            x s.distinguished leftRev.reverse s.right hs _ _ q hq
        · simp [RelationContext.weight, hleftEq, List.map_append,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · rw [hleftEq, List.append_assoc]
          exact List.Sublist.append (List.Sublist.refl leftRev.reverse)
            (List.sublist_cons_of_sublist x (List.Sublist.refl s.right))
    · split at h
      · contradiction
      · rename_i y right hright
        split at h
        · rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · simpa [ComponentPBWState.cellProvenanceInvariant, hright,
              List.map_append, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hs
          · apply componentPBWBracketChildren_cellProvenanceInvariant
              n L data hn c s (RelationContext.lieRight s.context y)
                s.distinguished y s.left right hs _ _ q hq
            · simp [RelationContext.weight, hright, List.map_append,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            · rw [hright]
              exact List.Sublist.append (List.Sublist.refl s.left)
                (List.sublist_cons_of_sublist y (List.Sublist.refl right))
        · contradiction
  · rename_i hleft
    have hleftNil : s.left = [] := by
      have hrev := congrArg List.reverse hleft
      simpa using hrev
    split at h
    · contradiction
    · rename_i y right hright
      split at h
      · rw [Option.some.injEq] at h
        subst qs
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · simpa [ComponentPBWState.cellProvenanceInvariant, hleftNil,
            hright, List.map_append, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hs
        · apply componentPBWBracketChildren_cellProvenanceInvariant
            n L data hn c s (RelationContext.lieRight s.context y)
              s.distinguished y s.left right hs _ _ q hq
          · simp [RelationContext.weight, hleftNil, hright,
              List.map_append, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm]
          · rw [hright]
            exact List.Sublist.append (List.Sublist.refl s.left)
              (List.sublist_cons_of_sublist y (List.Sublist.refl right))
      · contradiction

private theorem componentPBWBracketChildren_distinguishedWeightInvariant
    (s : ComponentPBWState n L data hn)
    (newContext : RelationContext n L data hn)
    (x y : AdaptedIndex n L data hn)
    (left right : List (AdaptedIndex n L data hn))
    (hweight :
      (adaptedWeightedBasis n L data hn).weight x +
          (adaptedWeightedBasis n L data hn).weight y =
        s.mark.val + RelationContext.weight n L data hn newContext)
    (q : ℤ × ComponentPBWState n L data hn)
    (hq : q ∈ componentPBWBracketChildren n L data hn s newContext
      x y left right) :
    q.2.distinguishedWeightInvariant n L data hn := by
  classical
  simp only [componentPBWBracketChildren, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  change (adaptedWeightedBasis n L data hn).weight p.2 =
    s.mark.val + RelationContext.weight n L data hn newContext
  apply ((adaptedWeightedBasis n L data hn).bracket_homogeneous
    x y p.2 ?_).trans hweight
  rw [adaptedCoordinates, List.mem_map] at hp
  obtain ⟨i, hi, hip⟩ := hp
  have hiIndex : i = p.2 := congrArg Prod.snd hip
  subst i
  exact Finsupp.mem_support_iff.mp (by
    simpa only [Finset.mem_toList] using hi)

private theorem componentPBWExpansion_preserves_distinguishedWeightInvariant
    {s : ComponentPBWState n L data hn}
    {qs : List (ℤ × ComponentPBWState n L data hn)}
    (h : componentPBWExpansion n L data hn s = some qs)
    (hs : s.distinguishedWeightInvariant n L data hn) :
    ∀ q ∈ qs, q.2.distinguishedWeightInvariant n L data hn := by
  classical
  intro q hq
  unfold componentPBWExpansion at h
  split at h
  · rename_i x leftRev hleft
    split at h
    · rw [Option.some.injEq] at h
      subst qs
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hs
      · apply componentPBWBracketChildren_distinguishedWeightInvariant
          n L data hn s (RelationContext.lieRight s.context x)
            x s.distinguished leftRev.reverse s.right _ q hq
        simp only [RelationContext.weight]
        rw [hs]
        omega
    · split at h
      · contradiction

      · rename_i y right hright
        split at h
        · rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact hs
          · apply componentPBWBracketChildren_distinguishedWeightInvariant
              n L data hn s (RelationContext.lieRight s.context y)
                s.distinguished y s.left right _ q hq
            simp only [RelationContext.weight]
            rw [hs]
            omega
        · contradiction
  · rename_i hleft
    split at h
    · contradiction
    · rename_i y right hright
      split at h
      · rw [Option.some.injEq] at h
        subst qs
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hs
        · apply componentPBWBracketChildren_distinguishedWeightInvariant
            n L data hn s (RelationContext.lieRight s.context y)
              s.distinguished y s.left right _ q hq
          simp only [RelationContext.weight]
          rw [hs]
          omega
      · contradiction

/-! A factor-lowering PBW correction always records the crossed ordinary
factor in the relation context. Consequently an empty context can survive
only along the factor-preserving branch of the collector. -/

private def ComponentPBWState.holeFactorAtLeast
    (m : ℕ) (s : ComponentPBWState n L data hn) : Prop :=
  s.context = .hole → m ≤ s.factorCount n L data hn

private theorem componentPBWBracketChildren_holeFactorAtLeast
    (m : ℕ) (s : ComponentPBWState n L data hn)
    (baseContext : RelationContext n L data hn)
    (contextFactor : AdaptedIndex n L data hn)
    (x y : AdaptedIndex n L data hn)
    (left right : List (AdaptedIndex n L data hn))
    (q : ℤ × ComponentPBWState n L data hn)
    (hq : q ∈ componentPBWBracketChildren n L data hn s
      (.lieRight baseContext contextFactor) x y left right) :
    q.2.holeFactorAtLeast n L data hn m := by
  simp only [componentPBWBracketChildren, List.mem_map] at hq
  obtain ⟨z, hz, rfl⟩ := hq
  simp [ComponentPBWState.holeFactorAtLeast]

private theorem componentPBWExpansion_preserves_holeFactorAtLeast
    (m : ℕ)
    {s : ComponentPBWState n L data hn}
    {qs : List (ℤ × ComponentPBWState n L data hn)}
    (h : componentPBWExpansion n L data hn s = some qs)
    (hs : s.holeFactorAtLeast n L data hn m) :
    ∀ q ∈ qs, q.2.holeFactorAtLeast n L data hn m := by
  classical
  intro q hq
  unfold componentPBWExpansion at h
  split at h
  · rename_i x leftRev hleft
    split at h
    · rw [Option.some.injEq] at h
      subst qs
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · have hleftEq : s.left = leftRev.reverse ++ [x] := by
          have hrev := congrArg List.reverse hleft
          simpa using hrev
        rw [ComponentPBWState.holeFactorAtLeast]
        intro hhole
        have hbound := hs hhole
        simp only [ComponentPBWState.factorCount] at hbound ⊢
        rw [hleftEq] at hbound
        simp only [List.length_append, List.length_singleton,
          List.length_cons, List.length_nil] at hbound ⊢
        omega
      · exact componentPBWBracketChildren_holeFactorAtLeast
          n L data hn m s s.context x x s.distinguished
            leftRev.reverse s.right q hq
    · split at h
      · contradiction
      · rename_i y right hright
        split at h
        · rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · rw [ComponentPBWState.holeFactorAtLeast]
            intro hhole
            have hbound := hs hhole
            simp only [ComponentPBWState.factorCount] at hbound ⊢
            rw [hright] at hbound
            simp only [List.length_append, List.length_singleton,
              List.length_cons, List.length_nil] at hbound ⊢
            omega
          · exact componentPBWBracketChildren_holeFactorAtLeast
              n L data hn m s s.context y s.distinguished y
                s.left right q hq
        · contradiction
  · rename_i hleft
    split at h
    · contradiction
    · rename_i y right hright
      split at h
      · rw [Option.some.injEq] at h
        subst qs
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · have hleftNil : s.left = [] := by
            have hrev := congrArg List.reverse hleft
            simpa using hrev
          rw [ComponentPBWState.holeFactorAtLeast]
          intro hhole
          have hbound := hs hhole
          simp only [ComponentPBWState.factorCount] at hbound ⊢
          rw [hleftNil, hright] at hbound
          simp only [List.length_nil, List.length_append,
            List.length_singleton, List.length_cons] at hbound ⊢
          omega
        · exact componentPBWBracketChildren_holeFactorAtLeast
            n L data hn m s s.context y s.distinguished y
              s.left right q hq
      · contradiction

private theorem componentPBWBracketChildren_neighbors_pairwise
    (s : ComponentPBWState n L data hn)
    (newContext : RelationContext n L data hn)
    (x y : AdaptedIndex n L data hn)
    (left right : List (AdaptedIndex n L data hn))
    (hordered : (left ++ right).Pairwise (· ≤ ·))
    (q : ℤ × ComponentPBWState n L data hn)
    (hq : q ∈ componentPBWBracketChildren n L data hn s newContext
      x y left right) :
    (q.2.left ++ q.2.right).Pairwise (· ≤ ·) := by
  simp only [componentPBWBracketChildren, List.mem_map] at hq
  obtain ⟨z, hz, rfl⟩ := hq
  simpa using hordered

theorem componentPBWExpansion_neighbors_pairwise
    {s : ComponentPBWState n L data hn}
    {qs : List (ℤ × ComponentPBWState n L data hn)}
    (h : componentPBWExpansion n L data hn s = some qs)
    (hs : (s.left ++ s.right).Pairwise (· ≤ ·)) :
    ∀ q ∈ qs, (q.2.left ++ q.2.right).Pairwise (· ≤ ·) := by
  classical
  intro q hq
  unfold componentPBWExpansion at h
  split at h
  · rename_i x leftRev hleft
    have hleftEq : s.left = leftRev.reverse ++ [x] := by
      have hrev := congrArg List.reverse hleft
      simpa using hrev
    split at h
    · rw [Option.some.injEq] at h
      subst qs
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · simpa [hleftEq, List.append_assoc] using hs
      · have hsub : List.Sublist (leftRev.reverse ++ s.right)
            (s.left ++ s.right) := by
          rw [hleftEq, List.append_assoc]
          exact List.Sublist.append (List.Sublist.refl leftRev.reverse)
            (List.sublist_cons_of_sublist x (List.Sublist.refl s.right))
        exact componentPBWBracketChildren_neighbors_pairwise
          n L data hn s (RelationContext.lieRight s.context x)
          x s.distinguished leftRev.reverse s.right
          (hs.sublist hsub) q hq
    · split at h
      · contradiction
      · rename_i y right hright
        split at h
        · rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · simpa [hright, List.append_assoc] using hs
          · have hsub : List.Sublist (s.left ++ right)
                (s.left ++ s.right) := by
              rw [hright]
              exact List.Sublist.append (List.Sublist.refl s.left)
                (List.sublist_cons_of_sublist y (List.Sublist.refl right))
            exact componentPBWBracketChildren_neighbors_pairwise
              n L data hn s (RelationContext.lieRight s.context y)
              s.distinguished y s.left right
              (hs.sublist hsub) q hq
        · contradiction
  · rename_i hleft
    split at h
    · contradiction
    · rename_i y right hright
      split at h
      · rw [Option.some.injEq] at h
        subst qs
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · simpa [hright, List.append_assoc] using hs
        · have hsub : List.Sublist (s.left ++ right)
              (s.left ++ s.right) := by
            rw [hright]
            exact List.Sublist.append (List.Sublist.refl s.left)
              (List.sublist_cons_of_sublist y (List.Sublist.refl right))
          exact componentPBWBracketChildren_neighbors_pairwise
            n L data hn s (RelationContext.lieRight s.context y)
            s.distinguished y s.left right
            (hs.sublist hsub) q hq
      · contradiction

theorem componentPBW_terminal_word_pairwise
    (s : ComponentPBWState n L data hn)
    (hs : (s.left ++ s.right).Pairwise (· ≤ ·))
    (hterminal : componentPBWExpansion n L data hn s = none) :
    (s.word n L data hn).Pairwise (· ≤ ·) := by
  classical
  have hparts := List.pairwise_append.mp hs
  have hleftBound : ∀ x ∈ s.left, x ≤ s.distinguished := by
    intro x hx
    cases hrev : s.left.reverse with
    | nil =>
        have hnil : s.left = [] := by
          have h := congrArg List.reverse hrev
          simpa using h
        simp [hnil] at hx
    | cons last leftRev =>
        have hleftEq : s.left = leftRev.reverse ++ [last] := by
          have h := congrArg List.reverse hrev
          simpa using h
        have hlast : last ≤ s.distinguished := by
          by_contra hnot
          have hxi : s.distinguished < last := lt_of_not_ge hnot
          unfold componentPBWExpansion at hterminal
          rw [hrev] at hterminal
          simp [hxi] at hterminal
        by_cases hxl : x = last
        · simpa [hxl]
        · have hxpre : x ∈ leftRev.reverse := by
            simpa [hleftEq, hxl] using hx
          have hpairLeft := hparts.1
          rw [hleftEq] at hpairLeft
          have hcross := (List.pairwise_append.mp hpairLeft).2.2
          exact (hcross x hxpre last (by simp)).trans hlast
  have hrightBound : ∀ y ∈ s.right, s.distinguished ≤ y := by
    intro y hy
    cases hright : s.right with
    | nil => simp [hright] at hy
    | cons first right =>
        have hfirst : s.distinguished ≤ first := by
          by_contra hnot
          have hfi : first < s.distinguished := lt_of_not_ge hnot
          unfold componentPBWExpansion at hterminal
          cases hrev : s.left.reverse with
          | nil =>
              rw [hrev, hright] at hterminal
              simp [hfi] at hterminal
          | cons last leftRev =>
              rw [hrev] at hterminal
              by_cases hil : s.distinguished < last
              · simp [hil] at hterminal
              · simp [hil, hright, hfi] at hterminal
        by_cases hyf : y = first
        · simpa [hyf]
        · have hytail : y ∈ right := by simpa [hright, hyf] using hy
          have hpairRight := hparts.2.1
          rw [hright] at hpairRight
          exact hfirst.trans ((List.pairwise_cons.mp hpairRight).1 y hytail)
  unfold ComponentPBWState.word
  apply List.pairwise_append.mpr
  refine ⟨hparts.1, List.pairwise_cons.mpr ⟨hrightBound, hparts.2.1⟩, ?_⟩
  intro x hx y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hleftBound x hx
  · exact hparts.2.2 x hx y hy

private theorem componentPBW_normalForm_word_pairwise
    (s : ComponentPBWState n L data hn)
    (hs : (s.left ++ s.right).Pairwise (· ≤ ·))
    (q : ComponentPBWState n L data hn)
    (hq : (componentPBWCollector n L data hn).normalForm s q ≠ 0) :
    (q.word n L data hn).Pairwise (· ≤ ·) := by
  classical
  let C := componentPBWCollector n L data hn
  induction s using C.wellFounded.induction with
  | h s ih =>
      cases hexp : componentPBWExpansion n L data hn s with
      | none =>
          rw [C.normalForm_eq_single_of_terminal hexp] at hq
          have hqs : q = s := by
            by_contra hne
            simp [Finsupp.single_apply, hne] at hq
          subst q
          exact componentPBW_terminal_word_pairwise n L data hn s hs hexp
      | some rows =>
          rw [C.normalForm_eq_sum_of_expansion s rows hexp] at hq
          have sum_apply (xs : List
              (ComponentPBWState n L data hn →₀ ℤ)) :
              xs.sum q = (xs.map fun f ↦ f q).sum := by
            induction xs with
            | nil => simp
            | cons x xs ihxs => simp [ihxs]
          rw [sum_apply] at hq
          have hexists : ∃ z ∈
              (rows.map fun r ↦ r.1 • C.normalForm r.2),
              z q ≠ 0 := by
            by_contra hall
            push Not at hall
            apply hq
            apply List.sum_eq_zero
            intro z hz
            rw [List.mem_map] at hz
            obtain ⟨f, hf, rfl⟩ := hz
            exact hall f hf
          obtain ⟨z, hz, hzq⟩ := hexists
          rw [List.mem_map] at hz
          obtain ⟨r, hr, rfl⟩ := hz
          have hchild : C.normalForm r.2 q ≠ 0 := by
            intro hzero
            simp [hzero] at hzq
          exact ih r.2 (C.decreases hexp r hr)
            (componentPBWExpansion_neighbors_pairwise
              n L data hn hexp hs r hr) hchild

/-- Basis expansion of the exact contextual component before collection. -/
def ProvenancedCell.componentPBWInitial
    (c : ProvenancedCell n L data hn) :
    ComponentPBWState n L data hn →₀ ℤ :=
  ((adaptedBasis n L data hn).repr
      (RelationContext.component n L data hn c.context c.root c.mark)).sum
    (fun i z ↦ Finsupp.single
      ⟨c.root, c.context, c.mark, i, c.left, []⟩ z)

/-- Complete PBW-normalized frontier below one contextual component cell. -/
def ProvenancedCell.componentPBWFrontier
    (c : ProvenancedCell n L data hn) :
    ComponentPBWState n L data hn →₀ ℤ :=
  (c.componentPBWInitial n L data hn).sum (fun s z ↦
    z • (componentPBWCollector n L data hn).normalForm s)

theorem ProvenancedCell.evaluate_componentPBWInitial
    (c : ProvenancedCell n L data hn) :
    (componentPBWCollector n L data hn).evaluate
        (c.componentPBWInitial n L data hn) = c.componentRow.value := by
  classical
  rw [ProvenancedCell.componentPBWInitial, map_finsuppSum]
  simp only [LieRings.DegreeFive.FiniteTaggedCollector.evaluate_single]
  change ((adaptedBasis n L data hn).repr
      (RelationContext.component n L data hn c.context c.root c.mark)).sum
        (fun i z ↦ z • ComponentPBWState.value n L data hn
          ⟨c.root, c.context, c.mark, i, c.left, []⟩) = _
  let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    { toFun := fun z ↦ MarkedRow.basisWord n L data hn c.left *
          UniversalEnvelopingAlgebra.ι ℤ z
      map_add' := by intro z w; rw [map_add, mul_add]
      map_smul' := by intro z w; rw [map_zsmul, mul_smul_comm]; rfl }
  have hcoordinates := congrArg context
    ((adaptedBasis n L data hn).linearCombination_repr
      (RelationContext.component n L data hn c.context c.root c.mark))
  change context (((adaptedBasis n L data hn).repr
      (RelationContext.component n L data hn c.context c.root c.mark)).sum
        (fun i z ↦ z • adaptedBasis n L data hn i)) =
    context (RelationContext.component n L data hn c.context c.root c.mark)
      at hcoordinates
  rw [map_finsuppSum] at hcoordinates
  simpa [ComponentPBWState.value, ProvenancedCell.componentRow,
    ProvenancedRow.value, MarkedRow.basisWord,
    LieRings.PBW.basisWord, LieRings.PBW.word, adaptedWeightedBasis,
    map_zsmul, mul_smul_comm, context] using hcoordinates

theorem ProvenancedCell.evaluate_componentPBWFrontier
    (c : ProvenancedCell n L data hn) :
    (componentPBWCollector n L data hn).evaluate
        (c.componentPBWFrontier n L data hn) = c.componentRow.value := by
  classical
  rw [ProvenancedCell.componentPBWFrontier, map_finsuppSum]
  calc
    _ = (c.componentPBWInitial n L data hn).sum (fun s z ↦
        z • (componentPBWCollector n L data hn).value s) := by
      apply Finsupp.sum_congr
      intro s hs
      rw [map_zsmul,
        (componentPBWCollector n L data hn).evaluate_normalForm]
    _ = (componentPBWCollector n L data hn).evaluate
        (c.componentPBWInitial n L data hn) := rfl
    _ = c.componentRow.value := c.evaluate_componentPBWInitial n L data hn

private theorem ProvenancedCell.componentPBWInitial_neighbors_pairwise
    (c : ProvenancedCell n L data hn)
    (hc : c.left.Pairwise (· ≤ ·))
    (s : ComponentPBWState n L data hn)
    (hs : c.componentPBWInitial n L data hn s ≠ 0) :
    (s.left ++ s.right).Pairwise (· ≤ ·) := by
  classical
  rw [ProvenancedCell.componentPBWInitial, Finsupp.sum_apply] at hs
  have hexists : ∃ i ∈ ((adaptedBasis n L data hn).repr
      (RelationContext.component n L data hn c.context c.root c.mark)).support,
      (Finsupp.single
        ⟨c.root, c.context, c.mark, i, c.left, []⟩
        (((adaptedBasis n L data hn).repr
          (RelationContext.component n L data hn
            c.context c.root c.mark)) i)) s ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hs (Finset.sum_eq_zero (fun i hi ↦ hall i hi))
  obtain ⟨i, hi, his⟩ := hexists
  have hstate : s = ⟨c.root, c.context, c.mark, i, c.left, []⟩ := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at his
  subst s
  simpa using hc

private theorem ProvenancedCell.componentPBWInitial_distinguishedWeightInvariant
    (c : ProvenancedCell n L data hn)
    (s : ComponentPBWState n L data hn)
    (hs : c.componentPBWInitial n L data hn s ≠ 0) :
    s.distinguishedWeightInvariant n L data hn := by
  classical
  rw [ProvenancedCell.componentPBWInitial, Finsupp.sum_apply] at hs
  have hexists : ∃ i ∈ ((adaptedBasis n L data hn).repr
      (RelationContext.component n L data hn c.context c.root c.mark)).support,
      (Finsupp.single
        ⟨c.root, c.context, c.mark, i, c.left, []⟩
        (((adaptedBasis n L data hn).repr
          (RelationContext.component n L data hn
            c.context c.root c.mark)) i)) s ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hs (Finset.sum_eq_zero (fun i hi ↦ hall i hi))
  obtain ⟨i, hi, his⟩ := hexists
  have hstate : s = ⟨c.root, c.context, c.mark, i, c.left, []⟩ := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at his
  subst s
  change (adaptedWeightedBasis n L data hn).weight i =
    c.mark.val + RelationContext.weight n L data hn c.context
  by_contra hweight
  apply Finsupp.mem_support_iff.mp hi
  change ((pieceAdaptedBasis n L data hn i.1).repr
    (RelationContext.component n L data hn
      c.context c.root c.mark i.1)) i.2 = 0
  have hcomponent : RelationContext.component n L data hn
      c.context c.root c.mark i.1 = 0 := by
    apply RelationContext.component_apply_eq_zero_of_ne
      n L data hn c.context c.root c.mark c.mark_pos i.1
    simpa [adaptedWeightedBasis] using hweight
  rw [hcomponent, map_zero]
  rfl

private theorem ProvenancedCell.componentPBWInitial_cellProvenanceInvariant
    (c : ProvenancedCell n L data hn)
    (s : ComponentPBWState n L data hn)
    (hs : c.componentPBWInitial n L data hn s ≠ 0) :
    s.cellProvenanceInvariant n L data hn c := by
  classical
  rw [ProvenancedCell.componentPBWInitial, Finsupp.sum_apply] at hs
  have hexists : ∃ i ∈ ((adaptedBasis n L data hn).repr
      (RelationContext.component n L data hn c.context c.root c.mark)).support,
      (Finsupp.single
        ⟨c.root, c.context, c.mark, i, c.left, []⟩
        (((adaptedBasis n L data hn).repr
          (RelationContext.component n L data hn
            c.context c.root c.mark)) i)) s ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hs (Finset.sum_eq_zero (fun i hi ↦ hall i hi))
  obtain ⟨i, hi, his⟩ := hexists
  have hstate : s = ⟨c.root, c.context, c.mark, i, c.left, []⟩ := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at his
  subst s
  simp [ComponentPBWState.cellProvenanceInvariant]

private theorem ProvenancedCell.componentPBWInitial_holeFactorAtLeast_three
    (c : ProvenancedCell n L data hn)
    (hleft : 2 ≤ c.left.length)
    (s : ComponentPBWState n L data hn)
    (hs : c.componentPBWInitial n L data hn s ≠ 0) :
    s.holeFactorAtLeast n L data hn 3 := by
  classical
  rw [ProvenancedCell.componentPBWInitial, Finsupp.sum_apply] at hs
  have hexists : ∃ i ∈ ((adaptedBasis n L data hn).repr
      (RelationContext.component n L data hn c.context c.root c.mark)).support,
      (Finsupp.single
        ⟨c.root, c.context, c.mark, i, c.left, []⟩
        (((adaptedBasis n L data hn).repr
          (RelationContext.component n L data hn
            c.context c.root c.mark)) i)) s ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hs (Finset.sum_eq_zero (fun i hi ↦ hall i hi))
  obtain ⟨i, hi, his⟩ := hexists
  have hstate : s = ⟨c.root, c.context, c.mark, i, c.left, []⟩ := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at his
  subst s
  intro hcontext
  simp only [ComponentPBWState.factorCount, List.length_nil, add_zero]
  omega

/-- Every normalized descendant of a contextual component retains the exact
active weight of the distinguished basis coordinate.  Bracket corrections
increase the stored context weight and the distinguished basis weight by the
same positive amount. -/
theorem ProvenancedCell.componentPBWFrontier_distinguished_weight
    (c : ProvenancedCell n L data hn)
    (q : ComponentPBWState n L data hn)
    (hq : c.componentPBWFrontier n L data hn q ≠ 0) :
    (adaptedWeightedBasis n L data hn).weight q.distinguished =
      q.mark.val + RelationContext.weight n L data hn q.context := by
  classical
  rw [ProvenancedCell.componentPBWFrontier, Finsupp.sum_apply] at hq
  have hexists : ∃ s ∈ (c.componentPBWInitial n L data hn).support,
      (c.componentPBWInitial n L data hn s •
        (componentPBWCollector n L data hn).normalForm s) q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq (Finset.sum_eq_zero (fun s hs ↦ hall s hs))
  obtain ⟨s, hs, hsq⟩ := hexists
  have hnormal :
      (componentPBWCollector n L data hn).normalForm s q ≠ 0 := by
    intro hzero
    simp [hzero] at hsq
  exact (componentPBWCollector n L data hn).invariant_of_normalForm_apply_ne_zero
    (ComponentPBWState.distinguishedWeightInvariant n L data hn)
    (fun hexp hinv ↦
      componentPBWExpansion_preserves_distinguishedWeightInvariant
        n L data hn hexp hinv)
    (c.componentPBWInitial_distinguishedWeightInvariant n L data hn s
      (Finsupp.mem_support_iff.mp hs)) hnormal

/-- Every normalized descendant of a contextual component retains its root
and active mark.  Context weight plus the weights of the ordinary factors
still present in the PBW word is exactly the corresponding source quantity.
Thus a factor lowered by a bracket correction is neither lost nor counted
twice: its weight has moved into the stored relation context. -/
theorem ProvenancedCell.componentPBWFrontier_provenance_weight
    (c : ProvenancedCell n L data hn)
    (q : ComponentPBWState n L data hn)
    (hq : c.componentPBWFrontier n L data hn q ≠ 0) :
    q.root = c.root ∧ q.mark = c.mark ∧
      RelationContext.weight n L data hn q.context +
            (q.left.map (adaptedWeightedBasis n L data hn).weight).sum +
            (q.right.map (adaptedWeightedBasis n L data hn).weight).sum =
        RelationContext.weight n L data hn c.context +
          (c.left.map (adaptedWeightedBasis n L data hn).weight).sum ∧
      (q.left ++ q.right).Sublist c.left := by
  classical
  rw [ProvenancedCell.componentPBWFrontier, Finsupp.sum_apply] at hq
  have hexists : ∃ s ∈ (c.componentPBWInitial n L data hn).support,
      (c.componentPBWInitial n L data hn s •
        (componentPBWCollector n L data hn).normalForm s) q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq (Finset.sum_eq_zero (fun s hs ↦ hall s hs))
  obtain ⟨s, hs, hsq⟩ := hexists
  have hnormal :
      (componentPBWCollector n L data hn).normalForm s q ≠ 0 := by
    intro hzero
    simp [hzero] at hsq
  exact (componentPBWCollector n L data hn).invariant_of_normalForm_apply_ne_zero
    (ComponentPBWState.cellProvenanceInvariant n L data hn c)
    (fun hexp hinv ↦
      componentPBWExpansion_preserves_cellProvenanceInvariant
        n L data hn c hexp hinv)
    (c.componentPBWInitial_cellProvenanceInvariant n L data hn s
      (Finsupp.mem_support_iff.mp hs)) hnormal

/-- A component cell with at least two ordinary factors can reach factor two
only through a bracket correction.  Such a correction records a nonempty
relation context, so every supported factor-two descendant has a genuine
contextual full relation. -/
theorem ProvenancedCell.componentPBWFrontier_factorTwo_context_ne_hole
    (c : ProvenancedCell n L data hn)
    (hleft : 2 ≤ c.left.length)
    (q : ComponentPBWState n L data hn)
    (hq : c.componentPBWFrontier n L data hn q ≠ 0)
    (htwo : q.factorCount n L data hn = 2) :
    q.context ≠ .hole := by
  classical
  rw [ProvenancedCell.componentPBWFrontier, Finsupp.sum_apply] at hq
  have hexists : ∃ s ∈ (c.componentPBWInitial n L data hn).support,
      (c.componentPBWInitial n L data hn s •
        (componentPBWCollector n L data hn).normalForm s) q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq (Finset.sum_eq_zero (fun s hs ↦ hall s hs))
  obtain ⟨s, hs, hsq⟩ := hexists
  have hnormal :
      (componentPBWCollector n L data hn).normalForm s q ≠ 0 := by
    intro hzero
    simp [hzero] at hsq
  have hinvariant : q.holeFactorAtLeast n L data hn 3 :=
    (componentPBWCollector n L data hn).invariant_of_normalForm_apply_ne_zero
      (ComponentPBWState.holeFactorAtLeast n L data hn 3)
      (fun hexp hinv ↦
        componentPBWExpansion_preserves_holeFactorAtLeast
          n L data hn 3 hexp hinv)
      (c.componentPBWInitial_holeFactorAtLeast_three
        n L data hn hleft s (Finsupp.mem_support_iff.mp hs)) hnormal
  intro hhole
  have := hinvariant hhole
  omega

theorem ProvenancedCell.componentPBWFrontier_word_pairwise
    (c : ProvenancedCell n L data hn)
    (hc : c.left.Pairwise (· ≤ ·))
    (q : ComponentPBWState n L data hn)
    (hq : c.componentPBWFrontier n L data hn q ≠ 0) :
    (q.word n L data hn).Pairwise (· ≤ ·) := by
  classical
  rw [ProvenancedCell.componentPBWFrontier, Finsupp.sum_apply] at hq
  have hexists : ∃ s ∈ (c.componentPBWInitial n L data hn).support,
      (c.componentPBWInitial n L data hn s •
        (componentPBWCollector n L data hn).normalForm s) q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq (Finset.sum_eq_zero (fun s hs ↦ hall s hs))
  obtain ⟨s, hs, hsq⟩ := hexists
  have hnormal : (componentPBWCollector n L data hn).normalForm s q ≠ 0 := by
    intro hzero
    simp [hzero] at hsq
  exact componentPBW_normalForm_word_pairwise n L data hn s
    (c.componentPBWInitial_neighbors_pairwise n L data hn hc s
      (Finsupp.mem_support_iff.mp hs)) q hnormal

/-- The completely normalized component part of the contextual closed
square.  Coefficients are still indexed by their originating full relation,
context, and mark. -/
def GoverningWitness.completeComponentPBWFrontier {a : L}
    (w : GoverningWitness n L data a) :
    ComponentPBWState n L data hn →₀ ℤ :=
  (w.provenancedCells n L data hn).sum (fun c z ↦
    z • c.componentPBWFrontier n L data hn)

theorem GoverningWitness.completeComponentPBWFrontier_word_pairwise
    {a : L} (w : GoverningWitness n L data a)
    (q : ComponentPBWState n L data hn)
    (hq : w.completeComponentPBWFrontier n L data hn q ≠ 0) :
    (q.word n L data hn).Pairwise (· ≤ ·) := by
  classical
  rw [GoverningWitness.completeComponentPBWFrontier,
    Finsupp.sum_apply] at hq
  have hexists : ∃ c ∈ (w.provenancedCells n L data hn).support,
      (w.provenancedCells n L data hn c •
        c.componentPBWFrontier n L data hn) q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq (Finset.sum_eq_zero (fun c hc ↦ hall c hc))
  obtain ⟨c, hc, hcq⟩ := hexists
  have hfront : c.componentPBWFrontier n L data hn q ≠ 0 := by
    intro hzero
    simp [hzero] at hcq
  exact c.componentPBWFrontier_word_pairwise n L data hn
    (w.provenancedCell_left_pairwise n L data hn c
      (Finsupp.mem_support_iff.mp hc)) q hfront

theorem GoverningWitness.evaluate_completeComponentPBWFrontier
    {a : L} (w : GoverningWitness n L data a) :
    (componentPBWCollector n L data hn).evaluate
        (w.completeComponentPBWFrontier n L data hn) =
      (w.provenancedCells n L data hn).sum
        (fun c z ↦ z • c.componentRow.value) := by
  classical
  rw [GoverningWitness.completeComponentPBWFrontier, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, c.evaluate_componentPBWFrontier]

/-- Once a component state is PBW ordered, its displayed factor count is
literal: its value is the basis word obtained by inserting the distinguished
coordinate between the two ordinary lists. -/
theorem ComponentPBWState.value_eq_basisWord
    (s : ComponentPBWState n L data hn) :
    s.value n L data hn =
      MarkedRow.basisWord n L data hn (s.word n L data hn) := by
  simp [ComponentPBWState.value, ComponentPBWState.word,
    MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word,
    List.map_append, adaptedWeightedBasis]
  noncomm_ring

/-- A terminal ordered component state contributes to the complete PBW
primitive exactly when it has one displayed factor.  In particular, the
factor-two component wall carries no hidden primitive term after collection. -/
theorem ComponentPBWState.pbwPrimitive_value_eq_zero_of_factorCount_ne_one
    (s : ComponentPBWState n L data hn)
    (hs : (s.word n L data hn).Pairwise (· ≤ ·))
    (hne : s.factorCount n L data hn ≠ 1) :
    pbwPrimitive n L data hn (s.value n L data hn) = 0 := by
  rw [s.value_eq_basisWord n L data hn]
  change (SymmetricPower.degreeOneLinearEquiv
      (adaptedBasis n L data hn))
    (fullRightSymbol n L data hn 1
      (MarkedRow.basisWord n L data hn (s.word n L data hn))) = 0
  rw [fullRightSymbol_basisWord_sorted_of_length_ne
    n L data hn 1 (s.word n L data hn) hs]
  · exact map_zero _
  · simpa [ComponentPBWState.factorCount, ComponentPBWState.word,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hne

/-- Primitive read of the completely ordered component frontier. -/
def GoverningWitness.completeComponentPBWPrimitive {a : L}
    (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.completeComponentPBWFrontier n L data hn).sum (fun s z ↦
    z • pbwPrimitive n L data hn (s.value n L data hn))

/-- Complete PBW ordering does not change the aggregate primitive carried by
the contextual component cells. -/
theorem GoverningWitness.completeComponentPBWPrimitive_eq_componentTrace
    {a : L} (w : GoverningWitness n L data a) :
    w.completeComponentPBWPrimitive n L data hn =
      w.componentTracePrimitive n L data hn := by
  classical
  have h := congrArg (pbwPrimitive n L data hn)
    (w.evaluate_completeComponentPBWFrontier n L data hn)
  change pbwPrimitive n L data hn
      ((w.completeComponentPBWFrontier n L data hn).sum
        (fun s z ↦ z • s.value n L data hn)) =
    pbwPrimitive n L data hn
      ((w.provenancedCells n L data hn).sum
        (fun c z ↦ z • c.componentRow.value)) at h
  rw [map_finsuppSum, map_finsuppSum] at h
  simpa only [map_zsmul, GoverningWitness.completeComponentPBWPrimitive,
    GoverningWitness.componentTracePrimitive, ProvenancedCell.primitive]
    using h

/-- After complete PBW ordering, only literal one-factor leaves survive the
primitive projection.  This is the precise factor-filtration statement used
in the terminal external-edge classification. -/
theorem GoverningWitness.completeComponentPBWPrimitive_eq_factorOne
    {a : L} (w : GoverningWitness n L data a) :
    w.completeComponentPBWPrimitive n L data hn =
      (w.completeComponentPBWFrontier n L data hn).sum (fun s z ↦
        if s.factorCount n L data hn = 1 then
          z • pbwPrimitive n L data hn (s.value n L data hn)
        else 0) := by
  classical
  rw [GoverningWitness.completeComponentPBWPrimitive]
  apply Finsupp.sum_congr
  intro s hs
  by_cases hone : s.factorCount n L data hn = 1
  · simp [hone]
  · rw [if_neg hone,
      s.pbwPrimitive_value_eq_zero_of_factorCount_ne_one n L data hn
        (w.completeComponentPBWFrontier_word_pairwise n L data hn s
          (Finsupp.mem_support_iff.mp hs)) hone]
    simp

/-! ### Terminal packet consequence

The construction of the packet is the remaining row calculation.  Once it
has been constructed, no further PBW argument is needed: Point 6 kills the
transported Smith block.  Keeping this consequence here prevents the reduced
theorem from depending on any of the placement bookkeeping. -/

/-- Every completely certified terminal packet has zero oriented primitive. -/
theorem TerminalQuadraticPacket.orientedPrimitive_eq_zero
    (p : TerminalQuadraticPacket n L data hn) :
    p.orientedPrimitive = 0 := by
  let transported := transportTerminalPacket n L data hn p
  calc
    p.orientedPrimitive =
        quadraticBlockValue n L data hn transported.cycleR :=
      transported.primitive_eq
    _ = 0 := quadraticBlockValue_eq_zero n L data hn transported.cycleR

end

end LieRings.MetabelianVanishing
