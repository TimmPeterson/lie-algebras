import LieRings.PBW.IntegralFreeModule
import LieRings.Homological.SymmetricPower

/-!
# Exact-factor symbols for integral PBW coordinates

Let `b : Basis ι ℤ L` be an ordered basis of a Lie ring.  Integral PBW
identifies `U(L)` linearly with the polynomial module on `ι`.  This file
retains exactly the monomials with `q` polynomial factors and transports
them to the genuine symmetric power `S^q(L)`.

There is no bracket-weight grading in this construction.  In particular it
can be used before a nonhomogeneous relation is split into weight pieces.
-/

namespace LieRings.PBW

open scoped BigOperators
open TensorProduct

universe u v

noncomputable section

variable {L : Type u} [LieRing L]
variable {ι : Type v} [LinearOrder ι] [Finite ι]

/-- The number of factors in a PBW exponent vector. -/
def factorNumber (e : ι →₀ ℕ) : ℕ := e.sum fun _ m ↦ m

@[simp] theorem factorNumber_zero : factorNumber (ι := ι) 0 = 0 := by
  simp [factorNumber]

@[simp] theorem factorNumber_single (i : ι) (m : ℕ) :
    factorNumber (Finsupp.single i m) = m := by
  simp [factorNumber]

/-- The unordered monomial represented by an exponent vector of factor
number `q`. -/
def exponentSym (q : ℕ) (e : ι →₀ ℕ) (he : factorNumber e = q) : Sym ι q :=
  Sym.mk (Finsupp.toMultiset e) <| by
    rw [Finsupp.card_toMultiset]
    simpa [factorNumber] using he

/-- The unordered monomial represented by a literal list. -/
def listSym (xs : List ι) : Sym ι xs.length :=
  Sym.mk (xs : Multiset ι) rfl

/-- The multiset underlying the symmetric index of a tuple is the multiset
of its entries. -/
theorem coe_symIndexOfFun {κ : Type*} [Finite κ]
    (q : ℕ) (p : Fin q → κ) :
    (SymmetricPower.symIndexOfFun q p : Multiset κ) =
      (List.ofFn p : Multiset κ) := by
  induction p using Fin.consInduction with
  | elim0 =>
      have hnil : SymmetricPower.symIndexOfFun 0
          (Fin.elim0 : Fin 0 → κ) = (Sym.nil : Sym κ 0) :=
        Subsingleton.elim _ _
      rw [hnil]
      rfl
  | cons x p ih =>
      rw [SymmetricPower.symIndexOfFun_cons, Sym.coe_cons, ih]
      simp

/-- A monomial basis vector is the pure symmetric tensor attached to any
tuple representing its symmetric index. -/
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

/-- The integral PBW equivalence attached to an arbitrary ordered basis. -/
def orderedPBWEquiv (b : Module.Basis ι ℤ L) :
    MvPolynomial ι ℤ ≃ₗ[ℤ] UEA ℤ L :=
  LinearEquiv.ofBijective (orderedPBWMap ℤ L ι b)
    (freeModulePBW_int L ι b)

@[simp] theorem orderedPBWEquiv_monomial (b : Module.Basis ι ℤ L)
    (e : ι →₀ ℕ) (z : ℤ) :
    orderedPBWEquiv b (MvPolynomial.monomial e z) =
      z • orderedMonomial ℤ L ι b e :=
  orderedPBWMap_monomial ℤ L ι b e z

@[simp] theorem orderedPBWEquiv_X (b : Module.Basis ι ℤ L) (i : ι) :
    orderedPBWEquiv b (MvPolynomial.X i) =
      UniversalEnvelopingAlgebra.ι ℤ (b i) :=
  orderedPBWMap_X ℤ L ι b i

/-- One exponent coordinate, retained only in exact factor number `q`. -/
def exponentFactorCoordinate (q : ℕ) (e : ι →₀ ℕ) :
    ℤ →ₗ[ℤ] (Sym ι q →₀ ℤ) :=
  if he : factorNumber e = q then Finsupp.lsingle (exponentSym q e he) else 0

/-- Projection of a polynomial to the free coordinates on unordered
monomials having exactly `q` factors. -/
def polynomialFactorCoordinates (q : ℕ) :
    MvPolynomial ι ℤ →ₗ[ℤ] (Sym ι q →₀ ℤ) :=
  Finsupp.lsum ℤ (fun e ↦ exponentFactorCoordinate q e)

theorem polynomialFactorCoordinates_monomial (q : ℕ)
    (e : ι →₀ ℕ) (z : ℤ) :
    polynomialFactorCoordinates q (MvPolynomial.monomial e z) =
      if he : factorNumber e = q then Finsupp.single (exponentSym q e he) z
      else 0 := by
  classical
  change ((Finsupp.lsum ℤ) (fun e ↦ exponentFactorCoordinate q e))
      (Finsupp.single e z) = _
  rw [Finsupp.lsum_single]
  unfold exponentFactorCoordinate
  split <;> simp_all

/-- The exact factor-`q` PBW symbol in the genuine symmetric power. -/
def factorSymbol (b : Module.Basis ι ℤ L) (q : ℕ) :
    UEA ℤ L →ₗ[ℤ] Sym[ℤ] (Fin q) L :=
  (SymmetricPower.monomialLinearEquiv b q).symm.toLinearMap.comp
    ((polynomialFactorCoordinates q).comp
      (orderedPBWEquiv b).symm.toLinearMap)

/-- Exact-factor symbol of one PBW monomial. -/
theorem factorSymbol_pbwMonomial (b : Module.Basis ι ℤ L) (q : ℕ)
    (e : ι →₀ ℕ) (z : ℤ) :
    factorSymbol b q (orderedPBWEquiv b (MvPolynomial.monomial e z)) =
      if he : factorNumber e = q then
        z • SymmetricPower.monomialBasis b q (exponentSym q e he)
      else 0 := by
  classical
  change (SymmetricPower.monomialLinearEquiv b q).symm
    (polynomialFactorCoordinates q
      ((orderedPBWEquiv b).symm
        (orderedPBWEquiv b (MvPolynomial.monomial e z)))) = _
  rw [LinearEquiv.symm_apply_apply, polynomialFactorCoordinates_monomial]
  split <;> rename_i he
  · change (SymmetricPower.monomialLinearEquiv b q).symm
        (Finsupp.single (exponentSym q e he) z) =
      z • (SymmetricPower.monomialLinearEquiv b q).symm
        (Finsupp.single (exponentSym q e he) 1)
    rw [← map_zsmul]
    congr 1
    simp
  · exact map_zero _

/-- Exact-factor symbol of a sorted basis word in its displayed length. -/
theorem factorSymbol_basisWord_sorted (b : Module.Basis ι ℤ L)
    (xs : List ι) (hxs : xs.Pairwise (· ≤ ·)) :
    factorSymbol b xs.length (basisWord ℤ L ι b xs) =
      SymmetricPower.monomialBasis b xs.length (listSym xs) := by
  classical
  let e : ι →₀ ℕ := Multiset.toFinsupp (xs : Multiset ι)
  have hordered : orderedMonomial ℤ L ι b e = basisWord ℤ L ι b xs :=
    orderedMonomial_multiset_toFinsupp ℤ L ι b xs hxs
  have hpbw : orderedPBWEquiv b (MvPolynomial.monomial e 1) =
      basisWord ℤ L ι b xs := by
    rw [orderedPBWEquiv_monomial, one_smul, hordered]
  have he : factorNumber e = xs.length := by
    change (Multiset.toFinsupp (xs : Multiset ι)).sum (fun _ z ↦ z) = _
    simpa only [id_eq, Multiset.card_coe] using
      (Multiset.toFinsupp_sum_eq (xs : Multiset ι))
  rw [← hpbw, factorSymbol_pbwMonomial, dif_pos he, one_smul]
  congr 1
  apply Subtype.ext
  simp [exponentSym, listSym, e]

/-- A sorted basis word has no symbol in a different factor number. -/
theorem factorSymbol_basisWord_sorted_of_length_ne
    (b : Module.Basis ι ℤ L) (q : ℕ) (xs : List ι)
    (hxs : xs.Pairwise (· ≤ ·)) (hlen : xs.length ≠ q) :
    factorSymbol b q (basisWord ℤ L ι b xs) = 0 := by
  classical
  let e : ι →₀ ℕ := Multiset.toFinsupp (xs : Multiset ι)
  have hordered : orderedMonomial ℤ L ι b e = basisWord ℤ L ι b xs :=
    orderedMonomial_multiset_toFinsupp ℤ L ι b xs hxs
  have hpbw : orderedPBWEquiv b (MvPolynomial.monomial e 1) =
      basisWord ℤ L ι b xs := by
    rw [orderedPBWEquiv_monomial, one_smul, hordered]
  have he : factorNumber e = xs.length := by
    change (Multiset.toFinsupp (xs : Multiset ι)).sum (fun _ z ↦ z) = _
    simpa only [id_eq, Multiset.card_coe] using
      (Multiset.toFinsupp_sum_eq (xs : Multiset ι))
  rw [← hpbw, factorSymbol_pbwMonomial]
  rw [dif_neg (fun h ↦ hlen (he.symm.trans h))]

/-- The factor-one symbol fixes the canonical copy of the Lie ring. -/
@[simp] theorem factorSymbol_one_iota (b : Module.Basis ι ℤ L) (x : L) :
    factorSymbol b 1 (UniversalEnvelopingAlgebra.ι ℤ x) =
      SymmetricPower.degreeOne x := by
  classical
  rw [← b.sum_repr x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [← orderedPBWEquiv_X b i, MvPolynomial.X,
    factorSymbol_pbwMonomial]
  have he : factorNumber (Finsupp.single i 1) = 1 := by simp
  rw [dif_pos he, one_smul, SymmetricPower.degreeOne_apply]
  let p : Fin 1 → ι := fun _ ↦ i
  have hp : SymmetricPower.symIndexOfFun 1 p =
      exponentSym 1 (Finsupp.single i 1) he := by
    apply Subtype.ext
    have hcoe : (SymmetricPower.symIndexOfFun 1 p).val =
        (List.ofFn p : Multiset ι) := coe_symIndexOfFun 1 p
    rw [hcoe]
    simp [p, exponentSym]
  rw [monomialBasis_eq_tprod_of_symIndex b 1 _ p hp]
  congr 1
  funext k
  fin_cases k
  rfl

/-- A primitive has no exact-factor symbol except in factor number one. -/
theorem factorSymbol_iota_of_ne_one (b : Module.Basis ι ℤ L)
    (q : ℕ) (hq : q ≠ 1) (x : L) :
    factorSymbol b q (UniversalEnvelopingAlgebra.ι ℤ x) = 0 := by
  classical
  rw [← b.sum_repr x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← orderedPBWEquiv_X b i, MvPolynomial.X,
    factorSymbol_pbwMonomial]
  rw [dif_neg]
  · exact smul_zero ((b.repr x) i)
  · simpa using hq.symm

/-- The exact factor-two symbol of a product of two *ordered basis*
primitives is their symmetric product. -/
theorem factorSymbol_two_iota_basis_mul_iota_basis_of_le
    (b : Module.Basis ι ℤ L) (i j : ι) (hij : i ≤ j) :
    factorSymbol b 2
        (UniversalEnvelopingAlgebra.ι ℤ (b i) *
          UniversalEnvelopingAlgebra.ι ℤ (b j)) =
      SymmetricPower.insert ℤ L 1 (b i)
        (SymmetricPower.degreeOne (b j)) := by
  classical
  let e : ι →₀ ℕ := Multiset.toFinsupp ([i, j] : Multiset ι)
  have hsorted : ([i, j] : List ι).Pairwise (· ≤ ·) := by simp [hij]
  have hword := factorSymbol_basisWord_sorted b [i, j] hsorted
  have hword' : factorSymbol b 2
      (UniversalEnvelopingAlgebra.ι ℤ (b i) *
        UniversalEnvelopingAlgebra.ι ℤ (b j)) =
      SymmetricPower.monomialBasis b 2 (listSym [i, j]) := by
    simpa only [List.length_cons, List.length_nil, basisWord, word,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] using hword
  rw [hword', SymmetricPower.degreeOne_apply,
    SymmetricPower.insert_tprod]
  let p : Fin 2 → ι := Fin.cons i (fun _ ↦ j)
  have hp : SymmetricPower.symIndexOfFun 2 p = listSym [i, j] := by
    apply Subtype.ext
    have hcoe : (SymmetricPower.symIndexOfFun 2 p).val =
        (List.ofFn p : Multiset ι) := coe_symIndexOfFun 2 p
    rw [hcoe]
    change (List.ofFn p : Multiset ι) =
      ([i, j] : List ι)
    simp [p]
  rw [monomialBasis_eq_tprod_of_symIndex b 2 _ p hp]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The factor-two symbol of a product of two basis primitives, with no
ordering hypothesis.  An out-of-order product differs from the sorted one
by one primitive bracket, whose factor-two symbol is zero. -/
theorem factorSymbol_two_iota_basis_mul_iota_basis
    (b : Module.Basis ι ℤ L) (i j : ι) :
    factorSymbol b 2
        (UniversalEnvelopingAlgebra.ι ℤ (b i) *
          UniversalEnvelopingAlgebra.ι ℤ (b j)) =
      SymmetricPower.insert ℤ L 1 (b i)
        (SymmetricPower.degreeOne (b j)) := by
  classical
  by_cases hij : i ≤ j
  · exact factorSymbol_two_iota_basis_mul_iota_basis_of_le b i j hij
  · have hji : j ≤ i := le_of_not_ge hij
    have hswap :
        UniversalEnvelopingAlgebra.ι ℤ (b i) *
            UniversalEnvelopingAlgebra.ι ℤ (b j) =
          UniversalEnvelopingAlgebra.ι ℤ (b j) *
              UniversalEnvelopingAlgebra.ι ℤ (b i) +
            UniversalEnvelopingAlgebra.ι ℤ ⁅b i, b j⁆ := by
      have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℤ)
        (b i) (b j)
      change UniversalEnvelopingAlgebra.ι ℤ ⁅b i, b j⁆ =
        UniversalEnvelopingAlgebra.ι ℤ (b i) *
            UniversalEnvelopingAlgebra.ι ℤ (b j) -
          UniversalEnvelopingAlgebra.ι ℤ (b j) *
            UniversalEnvelopingAlgebra.ι ℤ (b i) at h
      rw [h]
      noncomm_ring
    rw [hswap, map_add,
      factorSymbol_two_iota_basis_mul_iota_basis_of_le b j i hji,
      factorSymbol_iota_of_ne_one b 2 (by omega), add_zero]
    have hcomm := LinearMap.congr_fun
      (SymmetricPower.insert_comm ℤ L 0 (b i) (b j))
      (SymmetricPower.monomialBasis b 0 Sym.nil)
    simpa only [LinearMap.comp_apply,
      SymmetricPower.insert_monomialBasis_zero] using hcomm.symm

/-- The factor-two symbol of the product of two arbitrary primitives is
their commutative symmetric product. -/
theorem factorSymbol_two_iota_mul_iota (b : Module.Basis ι ℤ L)
    (x y : L) :
    factorSymbol b 2
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ y) =
      SymmetricPower.insert ℤ L 1 x (SymmetricPower.degreeOne y) := by
  classical
  let lhsX : L →ₗ[ℤ] Sym[ℤ] (Fin 2) L := by
    refine
      { toFun := fun x ↦ factorSymbol b 2
          (UniversalEnvelopingAlgebra.ι ℤ x *
            UniversalEnvelopingAlgebra.ι ℤ y)
        map_add' := ?_
        map_smul' := ?_ }
    · intro x z
      rw [map_add, add_mul, map_add]
    · intro r x
      rw [map_zsmul, smul_mul_assoc, map_zsmul]
      rfl
  let rhsX : L →ₗ[ℤ] Sym[ℤ] (Fin 2) L :=
    SymmetricPower.insertRight ℤ L 1 (SymmetricPower.degreeOne y)
  suffices lhsX = rhsX by exact DFunLike.congr_fun this x
  apply b.ext
  intro i
  let lhsY : L →ₗ[ℤ] Sym[ℤ] (Fin 2) L := by
    refine
      { toFun := fun y ↦ factorSymbol b 2
          (UniversalEnvelopingAlgebra.ι ℤ (b i) *
            UniversalEnvelopingAlgebra.ι ℤ y)
        map_add' := ?_
        map_smul' := ?_ }
    · intro y z
      rw [map_add, mul_add, map_add]
    · intro r y
      rw [map_zsmul, mul_smul_comm, map_zsmul]
      rfl
  let rhsY : L →ₗ[ℤ] Sym[ℤ] (Fin 2) L :=
    (SymmetricPower.insert ℤ L 1 (b i)).comp
      (SymmetricPower.degreeOne (R := ℤ))
  change lhsY y = rhsY y
  suffices lhsY = rhsY by exact DFunLike.congr_fun this y
  apply b.ext
  intro j
  exact factorSymbol_two_iota_basis_mul_iota_basis b i j

end

end LieRings.PBW
