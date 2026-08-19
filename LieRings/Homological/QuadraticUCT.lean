import LieRings.Homological.PresentationComparison
import LieRings.Homological.RatCircleTorsion
import LieRings.LinearAlgebra.InvariantFactorSmith
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.RingTheory.Flat.Basic

/-!
# The integral quadratic UCT in ordered Smith coordinates

This is the degree-two calculation used in the manuscript.  It deliberately
works with the actual Koszul cycle quotient.  Ordered Smith coordinates give
the horizontal cycles, their boundary multiples, and the unique rational
functional whose reduction modulo `ℤ` is the UCT character.
-/

namespace Koszul.QuadraticUCT

open TensorProduct
open LieRings

noncomputable section

set_option maxHeartbeats 1200000

universe u

variable {M A : Type u} [AddCommGroup M] [AddCommGroup A] [Finite A]
variable [Module.Free ℤ M] [Module.Finite ℤ M]
variable (ε : M →ₗ[ℤ] A) (hε : Function.Surjective ε)

abbrev N := LinearMap.ker ε

local instance nFinite : Module.Finite ℤ (N ε) :=
  Module.Finite.of_fg (IsNoetherian.noetherian _)

local instance nFree : Module.Free ℤ (N ε) :=
  Module.free_of_finite_type_torsion_free'

/-- The literal kernel presentation attached to a finite quotient. -/
def kernelPresentation : Presentation A where
  rel := N ε
  gen := M
  relAddCommGroup := inferInstance
  genAddCommGroup := inferInstance
  relFree := inferInstance
  genFree := inferInstance
  relFinite := inferInstance
  genFinite := inferInstance
  d := (LinearMap.ker ε).subtype
  augmentation := ε
  d_injective := Subtype.val_injective
  augmentation_surjective := hε
  exact := by ext x; simp

/-- Ordered Smith data for the literal kernel presentation. -/
def smith : InvariantFactorPresentation (N ε) := by
  let e := ε.quotKerEquivOfSurjective hε
  letI : Finite (M ⧸ N ε) := Finite.of_surjective e.symm e.symm.surjective
  exact InvariantFactorPresentation.ofFiniteQuotient (N ε) inferInstance

variable (S : InvariantFactorPresentation (N ε))

/-- The manuscript quotient `rᵢⱼ=dⱼ/dᵢ`. -/
def ratio (i j : Fin S.rank) : ℕ := S.diagonal j / S.diagonal i

theorem diagonal_mul_ratio {i j : Fin S.rank} (hij : i ≤ j) :
    S.diagonal i * ratio (ε := ε) S i j = S.diagonal j :=
  Nat.mul_div_cancel' (S.diagonal_dvd i j hij)

private def symOneBasis :
    Module.Basis (Fin S.rank) ℤ (Sym[ℤ] (Fin 1) M) :=
  S.ambientBasis.map (SymmetricPower.degreeOneLinearEquiv S.ambientBasis).symm

@[simp] theorem symOneBasis_apply (i : Fin S.rank) :
    symOneBasis (ε := ε) S i =
      SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis i) := by
  apply (SymmetricPower.degreeOneLinearEquiv S.ambientBasis).injective
  rw [show symOneBasis (ε := ε) S i =
      (SymmetricPower.degreeOneLinearEquiv S.ambientBasis).symm
        (S.ambientBasis i) by rfl,
    LinearEquiv.apply_symm_apply]
  exact (SymmetricPower.degreeOneLinearEquiv_degreeOne
    S.ambientBasis (S.ambientBasis i)).symm

/-- The tensor basis `aᵢ ⊗ xⱼ` of quadratic degree one. -/
def oneBasis : Module.Basis (Fin S.rank × Fin S.rank) ℤ
    (One (kernelPresentation ε hε) 1) :=
  by
    let _tower : IsScalarTower ℤ ℤ (N ε) := ⟨fun r s x => by
      change (r * s) • x = r • s • x
      exact mul_smul r s x⟩
    letI := _tower
    exact Module.Basis.tensorProduct (R := ℤ) (S := ℤ) S.relationBasis
      (symOneBasis (ε := ε) S)

@[simp] theorem oneBasis_apply (i j : Fin S.rank) :
    oneBasis (ε := ε) hε S (i, j) = S.relationBasis i ⊗ₜ[ℤ]
      SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j) := by
  change (S.relationBasis.tensorProduct (symOneBasis (ε := ε) S)) (i, j) = _
  rw [Module.Basis.tensorProduct_apply]
  rw [symOneBasis_apply]

@[simp] theorem dOne_oneBasis (i j : Fin S.rank) :
    dOne (kernelPresentation ε hε) 1 (oneBasis (ε := ε) hε S (i, j)) =
      SymmetricPower.insert ℤ M 1 ((S.relationBasis i : N ε) : M)
        (SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) := by
  rw [oneBasis_apply]
  rfl

theorem dOne_oneBasis_smith (i j : Fin S.rank) :
    dOne (kernelPresentation ε hε) 1 (oneBasis (ε := ε) hε S (i, j)) =
      (S.diagonal i : ℤ) •
        SymmetricPower.monomialBasis S.ambientBasis 2
          (i ::ₛ j ::ₛ Sym.nil) := by
  rw [dOne_oneBasis, S.relation_eq,
    SymmetricPower.insert_smul_apply]
  congr 1
  have hj : SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j) =
      SymmetricPower.monomialBasis S.ambientBasis 1 (j ::ₛ Sym.nil) := by
    rw [← SymmetricPower.insert_monomialBasis_zero S.ambientBasis,
      SymmetricPower.insert_monomialBasis]
  rw [hj]
  simpa using SymmetricPower.insert_monomialBasis S.ambientBasis 1 i
    (j ::ₛ Sym.nil)

/-- `cᵢⱼ=(dⱼ/dᵢ)aᵢ⊗xⱼ-aⱼ⊗xᵢ`, with exactly the manuscript normalization. -/
def horizontal (i j : Fin S.rank) : One (kernelPresentation ε hε) 1 :=
  (ratio (ε := ε) S i j : ℤ) • oneBasis (ε := ε) hε S (i, j) -
    oneBasis (ε := ε) hε S (j, i)

theorem horizontal_cycle {i j : Fin S.rank} (hij : i < j) :
    dOne (kernelPresentation ε hε) 1 (horizontal (ε := ε) hε S i j) = 0 := by
  rw [horizontal, map_sub, map_zsmul, dOne_oneBasis, dOne_oneBasis]
  change (ratio (ε := ε) S i j : ℤ) •
      SymmetricPower.insert ℤ M 1 ((S.relationBasis i : N ε) : M)
        (SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) -
    SymmetricPower.insert ℤ M 1 ((S.relationBasis j : N ε) : M)
        (SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis i)) = 0
  rw [S.relation_eq i, S.relation_eq j,
    SymmetricPower.insert_smul_apply, SymmetricPower.insert_smul_apply]
  have hd := diagonal_mul_ratio (ε := ε) S hij.le
  have hdZ : (ratio (ε := ε) S i j : ℤ) * (S.diagonal i : ℤ) =
      (S.diagonal j : ℤ) := by
    exact_mod_cast (by simpa [mul_comm] using hd)
  apply sub_eq_zero.mpr
  calc
    (ratio (ε := ε) S i j : ℤ) •
        ((S.diagonal i : ℤ) •
          SymmetricPower.insert ℤ M 1 (S.ambientBasis i)
            (SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j))) =
      ((ratio (ε := ε) S i j : ℤ) * (S.diagonal i : ℤ)) •
        SymmetricPower.insert ℤ M 1 (S.ambientBasis i)
          (SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) := by
            exact smul_smul _ _ _
    _ = (S.diagonal j : ℤ) •
        SymmetricPower.insert ℤ M 1 (S.ambientBasis i)
          (SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) := by rw [hdZ]
    _ = (S.diagonal j : ℤ) •
        SymmetricPower.insert ℤ M 1 (S.ambientBasis j)
          (SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis i)) := by
      congr 1
      simpa only [LinearMap.comp_apply,
        SymmetricPower.insert_monomialBasis_zero] using LinearMap.congr_fun
        (SymmetricPower.insert_comm ℤ M 0 (S.ambientBasis i) (S.ambientBasis j))
        (SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil)

/-- The horizontal cycle as an element of `Z₁K₂(P)`. -/
def horizontalCycle {i j : Fin S.rank} (hij : i < j) :
    cyclesOne (kernelPresentation ε hε) 1 :=
  ⟨horizontal (ε := ε) hε S i j,
    horizontal_cycle (ε := ε) hε S hij⟩

/-- The oriented Smith exterior generator `aᵢ∧aⱼ`, placed in degree two. -/
def twoGenerator (i j : Fin S.rank) : Two (kernelPresentation ε hε) 0 :=
  exteriorPower.ιMulti ℤ 2 ![S.relationBasis i, S.relationBasis j] ⊗ₜ[ℤ]
    SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil

/-- The unsimplified Smith-coordinate boundary formula, valid without an
ordering hypothesis on the two indices. -/
theorem dTwo_twoGenerator_raw (i j : Fin S.rank) :
    dTwo (kernelPresentation ε hε) 0 (twoGenerator (ε := ε) hε S i j) =
      (S.diagonal j : ℤ) • oneBasis (ε := ε) hε S (i, j) -
        (S.diagonal i : ℤ) • oneBasis (ε := ε) hε S (j, i) := by
  letI : TensorProduct.CompatibleSMul ℤ ℤ (N ε) (Sym[ℤ] (Fin 1) M) :=
    TensorProduct.CompatibleSMul.int
  rw [twoGenerator, dTwo_wedge_tmul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  change S.relationBasis i ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ M 0 ((S.relationBasis j : N ε) : M)
          (SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil) -
      S.relationBasis j ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ M 0 ((S.relationBasis i : N ε) : M)
          (SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil) = _
  rw [S.relation_eq i, S.relation_eq j,
    SymmetricPower.insert_smul_apply, SymmetricPower.insert_smul_apply,
    SymmetricPower.insert_monomialBasis_zero]
  rw [oneBasis_apply, oneBasis_apply,
    TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  rw [SymmetricPower.insert_monomialBasis_zero]
  rfl

/-- The exact boundary normalization from the manuscript:
`∂(aᵢ∧aⱼ)=dᵢ cᵢⱼ`. -/
theorem dTwo_twoGenerator {i j : Fin S.rank} (hij : i < j) :
    dTwo (kernelPresentation ε hε) 0 (twoGenerator (ε := ε) hε S i j) =
      (S.diagonal i : ℤ) • horizontal (ε := ε) hε S i j := by
  letI : TensorProduct.CompatibleSMul ℤ ℤ (N ε) (Sym[ℤ] (Fin 1) M) :=
    TensorProduct.CompatibleSMul.int
  rw [twoGenerator, dTwo_wedge_tmul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  change S.relationBasis i ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ M 0 ((S.relationBasis j : N ε) : M)
          (SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil) -
      S.relationBasis j ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ M 0 ((S.relationBasis i : N ε) : M)
          (SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil) = _
  rw [S.relation_eq i, S.relation_eq j,
    SymmetricPower.insert_smul_apply, SymmetricPower.insert_smul_apply,
    SymmetricPower.insert_monomialBasis_zero]
  rw [horizontal, oneBasis_apply, oneBasis_apply]
  rw [SymmetricPower.insert_monomialBasis_zero]
  have hd := diagonal_mul_ratio (ε := ε) S hij.le
  have hdZ : (S.diagonal j : ℤ) =
      (S.diagonal i : ℤ) * (ratio (ε := ε) S i j : ℤ) := by
    exact_mod_cast hd.symm
  rw [hdZ]
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  calc
    ((S.diagonal i : ℤ) * (ratio (ε := ε) S i j : ℤ)) •
          S.relationBasis i ⊗ₜ[ℤ]
            SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j) -
        (S.diagonal i : ℤ) • S.relationBasis j ⊗ₜ[ℤ]
            SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis i) = _ := by
      change _ = (S.diagonal i : ℤ) •
        ((ratio (ε := ε) S i j : ℤ) •
            (S.relationBasis i ⊗ₜ[ℤ]
              SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis j)) -
          (S.relationBasis j ⊗ₜ[ℤ]
            SymmetricPower.degreeOne (R := ℤ) (S.ambientBasis i)))
      module

/-- The homology class of the horizontal Smith cycle. -/
def horizontalClass {i j : Fin S.rank} (hij : i < j) :
    homologyOne (kernelPresentation ε hε) 1 :=
  (boundariesOne (kernelPresentation ε hε) 1).mkQ
    (horizontalCycle (ε := ε) hε S hij)

def cycleCoefficient
    (c : cyclesOne (kernelPresentation ε hε) 1)
    (i j : Fin S.rank) : ℤ :=
  (oneBasis (ε := ε) hε S).repr c.1 (i, j)

theorem cycle_pair_equation
    (c : cyclesOne (kernelPresentation ε hε) 1)
    (i j : Fin S.rank) (hij : i ≠ j) :
    (S.diagonal i : ℤ) * cycleCoefficient ε hε S c i j +
      (S.diagonal j : ℤ) * cycleCoefficient ε hε S c j i = 0 := by
  let B := oneBasis (ε := ε) hε S
  let coeff := B.repr c.1
  have hsum : dOne (kernelPresentation ε hε) 1 c.1 =
      ∑ x : Fin S.rank × Fin S.rank,
        coeff x • (S.diagonal x.1 : ℤ) •
          SymmetricPower.monomialBasis S.ambientBasis 2
            (Sym.cons x.1 (Sym.cons x.2 Sym.nil)) := by
    rw [← B.sum_repr c.1, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [map_smul, dOne_oneBasis_smith]
    rfl
  have hcoord :
      (∑ x : Fin S.rank × Fin S.rank,
        coeff x * (S.diagonal x.1 : ℤ) *
          if Sym.cons x.1 (Sym.cons x.2 Sym.nil) =
              Sym.cons i (Sym.cons j Sym.nil) then 1 else 0) = 0 := by
    have hrepr : (SymmetricPower.monomialBasis S.ambientBasis 2).repr
        (∑ x : Fin S.rank × Fin S.rank,
          coeff x • (S.diagonal x.1 : ℤ) •
            SymmetricPower.monomialBasis S.ambientBasis 2
              (Sym.cons x.1 (Sym.cons x.2 Sym.nil))) = 0 := by
      calc
        _ = (SymmetricPower.monomialBasis S.ambientBasis 2).repr
            (dOne (kernelPresentation ε hε) 1 c.1) := congrArg _ hsum.symm
        _ = (SymmetricPower.monomialBasis S.ambientBasis 2).repr 0 :=
          congrArg _ c.property
        _ = 0 := (SymmetricPower.monomialBasis S.ambientBasis 2).repr.map_zero
    let ev : (Sym (Fin S.rank) 2 →₀ ℤ) →+ ℤ :=
      Finsupp.applyAddHom (Sym.cons i (Sym.cons j Sym.nil))
    have h := congrArg ev hrepr
    change ev ((SymmetricPower.monomialBasis S.ambientBasis 2).repr
        (∑ x : Fin S.rank × Fin S.rank,
          coeff x • (S.diagonal x.1 : ℤ) •
            SymmetricPower.monomialBasis S.ambientBasis 2
              (Sym.cons x.1 (Sym.cons x.2 Sym.nil)))) = 0 at h
    simp only [map_sum, map_smul,
      (SymmetricPower.monomialBasis S.ambientBasis 2).repr_self,
      ev, Finsupp.applyAddHom_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
    simpa [mul_ite] using h
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (i, j)),
    ← Finset.add_sum_erase (Finset.univ.erase (i, j)) _
      (show (j, i) ∈ Finset.univ.erase (i, j) by simp [hij])] at hcoord
  have hswap : Sym.cons j (Sym.cons i Sym.nil) =
      Sym.cons i (Sym.cons j Sym.nil) := Sym.cons_swap j i Sym.nil
  have hrest : (∑ x ∈ (Finset.univ.erase (i, j)).erase (j, i),
      coeff x * (S.diagonal x.1 : ℤ) *
        if Sym.cons x.1 (Sym.cons x.2 Sym.nil) =
            Sym.cons i (Sym.cons j Sym.nil) then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_erase] at hx
    have hne : Sym.cons x.1 (Sym.cons x.2 Sym.nil) ≠
        Sym.cons i (Sym.cons j Sym.nil) := by
      intro h
      rw [SymmetricPower.pairSym_eq_pairSym_iff] at h
      rcases h with h | h
      · exact hx.2.1 (Prod.ext h.1 h.2)
      · exact hx.1 (Prod.ext h.1 h.2)
    simp [hne]
  rw [hrest, add_zero] at hcoord
  simp only [hswap] at hcoord
  simp at hcoord
  change (S.diagonal i : ℤ) * coeff (i, j) +
      (S.diagonal j : ℤ) * coeff (j, i) = 0
  ring_nf at hcoord ⊢
  exact hcoord

theorem cycle_diagonal_coefficient_eq_zero
    (c : cyclesOne (kernelPresentation ε hε) 1)
    (i : Fin S.rank) : cycleCoefficient ε hε S c i i = 0 := by
  let B := oneBasis (ε := ε) hε S
  let coeff := B.repr c.1
  have hsum : dOne (kernelPresentation ε hε) 1 c.1 =
      ∑ x : Fin S.rank × Fin S.rank,
        coeff x • (S.diagonal x.1 : ℤ) •
          SymmetricPower.monomialBasis S.ambientBasis 2
            (Sym.cons x.1 (Sym.cons x.2 Sym.nil)) := by
    rw [← B.sum_repr c.1, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [map_smul, dOne_oneBasis_smith]
    rfl
  have hrepr : (SymmetricPower.monomialBasis S.ambientBasis 2).repr
      (∑ x : Fin S.rank × Fin S.rank,
        coeff x • (S.diagonal x.1 : ℤ) •
          SymmetricPower.monomialBasis S.ambientBasis 2
            (Sym.cons x.1 (Sym.cons x.2 Sym.nil))) = 0 := by
    calc
      _ = (SymmetricPower.monomialBasis S.ambientBasis 2).repr
          (dOne (kernelPresentation ε hε) 1 c.1) := congrArg _ hsum.symm
      _ = (SymmetricPower.monomialBasis S.ambientBasis 2).repr 0 :=
        congrArg _ c.property
      _ = 0 := (SymmetricPower.monomialBasis S.ambientBasis 2).repr.map_zero
  let ev : (Sym (Fin S.rank) 2 →₀ ℤ) →+ ℤ :=
    Finsupp.applyAddHom (Sym.cons i (Sym.cons i Sym.nil))
  have h := congrArg ev hrepr
  change ev ((SymmetricPower.monomialBasis S.ambientBasis 2).repr
      (∑ x : Fin S.rank × Fin S.rank,
        coeff x • (S.diagonal x.1 : ℤ) •
          SymmetricPower.monomialBasis S.ambientBasis 2
            (Sym.cons x.1 (Sym.cons x.2 Sym.nil)))) = 0 at h
  simp only [map_sum, map_smul,
    (SymmetricPower.monomialBasis S.ambientBasis 2).repr_self,
    ev, Finsupp.applyAddHom_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul] at h
  rw [Finset.sum_eq_single (i, i)] at h
  · simp at h
    rcases h with hcoeff | hdiag
    · exact hcoeff
    · exact (S.diagonal_pos i).ne' hdiag |>.elim
  · intro x _ hx
    have hne : Sym.cons x.1 (Sym.cons x.2 Sym.nil) ≠
        Sym.cons i (Sym.cons i Sym.nil) := by
      intro heq
      rw [SymmetricPower.pairSym_eq_pairSym_iff] at heq
      rcases heq with heq | heq <;> exact hx (Prod.ext heq.1 heq.2)
    simp [hne]
  · intro hnot
    exact (hnot (Finset.mem_univ (i, i))).elim

def horizontalCoefficient
    (c : cyclesOne (kernelPresentation ε hε) 1)
    (i j : Fin S.rank) : ℤ :=
  -cycleCoefficient ε hε S c j i

def horizontalExpansion
    (c : cyclesOne (kernelPresentation ε hε) 1) :
    One (kernelPresentation ε hε) 1 :=
  ∑ i : Fin S.rank, ∑ j : Fin S.rank,
    if hij : i < j then
      horizontalCoefficient ε hε S c i j • horizontal (ε := ε) hε S i j
    else 0

private theorem oneBasis_repr_horizontal
    (a b i j : Fin S.rank) :
    (oneBasis (ε := ε) hε S).repr (horizontal (ε := ε) hε S a b) (i, j) =
      (ratio (ε := ε) S a b : ℤ) * (if (a, b) = (i, j) then 1 else 0) -
        (if (b, a) = (i, j) then 1 else 0) := by
  change (oneBasis (ε := ε) hε S).repr
      ((ratio (ε := ε) S a b : ℤ) •
        oneBasis (ε := ε) hε S (a, b) -
          oneBasis (ε := ε) hε S (b, a)) (i, j) = _
  rw [map_sub, map_zsmul]
  simp only [Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.sub_apply, Finsupp.single_apply, smul_eq_mul]

theorem cycle_eq_horizontalExpansion
    (c : cyclesOne (kernelPresentation ε hε) 1) :
    c.1 = horizontalExpansion ε hε S c := by
  let B := oneBasis (ε := ε) hε S
  let coeff := B.repr c.1
  apply B.repr.injective
  apply Finsupp.ext
  rintro ⟨i, j⟩
  change coeff (i, j) = B.repr (horizontalExpansion ε hε S c) (i, j)
  simp only [horizontalExpansion, map_sum]
  let term : Fin S.rank → Fin S.rank → ℤ := fun a b ↦
    if hab : a < b then
      horizontalCoefficient ε hε S c a b *
        ((ratio (ε := ε) S a b : ℤ) *
            (if (a, b) = (i, j) then 1 else 0) -
          (if (b, a) = (i, j) then 1 else 0))
    else 0
  have hterm (a b : Fin S.rank) :
      B.repr (if hab : a < b then
          horizontalCoefficient ε hε S c a b •
            horizontal (ε := ε) hε S a b else 0) (i, j) = term a b := by
    by_cases hab : a < b
    · simp only [hab, dite_true, map_zsmul]
      change (horizontalCoefficient ε hε S c a b •
          (oneBasis (ε := ε) hε S).repr
            (horizontal (ε := ε) hε S a b)) (i, j) = term a b
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [oneBasis_repr_horizontal]
      simp [term, hab]
    · simp [term, hab]
  let ev : (Fin S.rank × Fin S.rank →₀ ℤ) →+ ℤ :=
    Finsupp.applyAddHom (i, j)
  change coeff (i, j) = ev (∑ a : Fin S.rank, ∑ b : Fin S.rank,
    B.repr (if hab : a < b then
      horizontalCoefficient ε hε S c a b •
        horizontal (ε := ε) hε S a b else 0))
  rw [map_sum]
  simp_rw [map_sum]
  change coeff (i, j) = ∑ a : Fin S.rank, ∑ b : Fin S.rank,
    B.repr (if hab : a < b then
      horizontalCoefficient ε hε S c a b •
        horizontal (ε := ε) hε S a b else 0) (i, j)
  simp_rw [hterm]
  have term_eq_zero_of_ne (a b : Fin S.rank)
      (h₁ : (a, b) ≠ (i, j)) (h₂ : (b, a) ≠ (i, j)) : term a b = 0 := by
    by_cases hab : a < b
    · have h₁' : ¬(a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact h₁ rfl
      have h₂' : ¬(b = i ∧ a = j) := by
        rintro ⟨rfl, rfl⟩
        exact h₂ rfl
      simp [term, hab, h₁', h₂']
    · simp [term, hab]
  rcases lt_trichotomy i j with hij | hij | hji
  · have term_eq_zero_lt (a b : Fin S.rank)
        (hne : (a, b) ≠ (i, j)) : term a b = 0 := by
      by_cases hab : a < b
      · apply term_eq_zero_of_ne a b hne
        intro hrev
        have hbi : b = i := (Prod.mk.inj hrev).1
        have haj : a = j := (Prod.mk.inj hrev).2
        subst b
        subst a
        exact (not_lt_of_ge hij.le) hab
      · simp [term, hab]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · change coeff (i, j) = term i j
        have hp := cycle_pair_equation ε hε S c i j hij.ne
        have hd := diagonal_mul_ratio (ε := ε) S hij.le
        have hdZ : (S.diagonal j : ℤ) =
            (S.diagonal i : ℤ) * (ratio (ε := ε) S i j : ℤ) := by
          exact_mod_cast hd.symm
        have hdi : (S.diagonal i : ℤ) ≠ 0 := by
          exact_mod_cast (S.diagonal_pos i).ne'
        have hcoeff : coeff (i, j) =
            -(ratio (ε := ε) S i j : ℤ) * coeff (j, i) := by
          change (S.diagonal i : ℤ) * coeff (i, j) +
              (S.diagonal j : ℤ) * coeff (j, i) = 0 at hp
          rw [hdZ] at hp
          apply mul_left_cancel₀ hdi
          linear_combination hp
        simp [term, hij, horizontalCoefficient, cycleCoefficient, coeff, B,
          hij.ne, hij.ne', hcoeff, mul_comm]
      · intro b _ hb
        exact term_eq_zero_lt i b (fun h ↦ hb (Prod.mk.inj h).2)
      · intro hnot
        exact (hnot (Finset.mem_univ j)).elim
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro b _
      exact term_eq_zero_lt a b (fun h ↦ ha (Prod.mk.inj h).1)
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  · subst j
    change cycleCoefficient ε hε S c i i = ∑ a, ∑ b, term a b
    rw [cycle_diagonal_coefficient_eq_zero ε hε S c i]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    by_cases hab : a < b
    · have h₁ : (a, b) ≠ (i, i) := by
        intro h
        exact hab.ne ((Prod.mk.inj h).1.trans (Prod.mk.inj h).2.symm)
      have h₂ : (b, a) ≠ (i, i) := by
        intro h
        exact hab.ne ((Prod.mk.inj h).2.trans (Prod.mk.inj h).1.symm)
      exact term_eq_zero_of_ne a b h₁ h₂
    · simp [term, hab]
  · have term_eq_zero_gt (a b : Fin S.rank)
        (hne : (b, a) ≠ (i, j)) : term a b = 0 := by
      by_cases hab : a < b
      · apply term_eq_zero_of_ne a b
        · intro hdir
          have hai : a = i := (Prod.mk.inj hdir).1
          have hbj : b = j := (Prod.mk.inj hdir).2
          subst a
          subst b
          exact (not_lt_of_ge hji.le) hab
        · exact hne
      · simp [term, hab]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · change coeff (i, j) = term j i
        simp [term, hji, horizontalCoefficient, cycleCoefficient, coeff, B,
          hji.ne, hji.ne']
      · intro b _ hbi
        exact term_eq_zero_gt j b (fun h ↦ hbi (Prod.mk.inj h).1)
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    · intro a _ haj
      apply Finset.sum_eq_zero
      intro b _
      exact term_eq_zero_gt a b (fun h ↦ haj (Prod.mk.inj h).2)
    · intro hnot
      exact (hnot (Finset.mem_univ j)).elim

/-! ## Exactness in rational degree one

For the quadratic complex the second differential is already injective over
the integers.  The proof below is the literal factorization

`Λ²N ⊗ Sym⁰M ≃ Λ²N ↪ N ⊗ N ↪ N ⊗ M ≃ N ⊗ Sym¹M`.

The first injection is integral alternation in the chosen Smith basis and the
second is tensoring the presentation inclusion with the free module `N`.
-/

private def symZeroBasis :
    Module.Basis (Sym (Fin S.rank) 0) ℤ (Sym[ℤ] (Fin 0) M) :=
  SymmetricPower.monomialBasis S.ambientBasis 0

/-- Remove the tautological `Sym⁰` factor from quadratic degree two. -/
def twoToExterior : Two (kernelPresentation ε hε) 0 ≃ₗ[ℤ] ⋀[ℤ]^2 (N ε) :=
  (TensorProduct.congr (LinearEquiv.refl ℤ (⋀[ℤ]^2 (N ε)))
      (SymmetricPower.degreeZeroLinearEquiv S.ambientBasis)).trans
    (TensorProduct.rid ℤ (⋀[ℤ]^2 (N ε)))

@[simp] theorem twoToExterior_tmul (w : ⋀[ℤ]^2 (N ε))
    (s : Sym[ℤ] (Fin 0) M) :
    twoToExterior ε hε S (w ⊗ₜ[ℤ] s) =
      (SymmetricPower.degreeZeroLinearEquiv S.ambientBasis s) • w := by
  change (TensorProduct.rid ℤ (⋀[ℤ]^2 (N ε)))
      ((TensorProduct.congr (LinearEquiv.refl ℤ (⋀[ℤ]^2 (N ε)))
        (SymmetricPower.degreeZeroLinearEquiv S.ambientBasis))
        (w ⊗ₜ[ℤ] s)) = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.rid_tmul]

/-- The exterior component of a pure quadratic degree-two generator. -/
@[simp] theorem twoToExterior_generator (a : Fin 2 → N ε) :
    twoToExterior ε hε S
        (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil) =
      exteriorPower.ιMulti ℤ 2 a := by
  rw [twoToExterior_tmul,
    SymmetricPower.degreeZeroLinearEquiv_monomialBasis, one_smul]
  rfl

/-- Replace the tautological `Sym¹` factor in quadratic degree one by `M`. -/
def oneToTensor : One (kernelPresentation ε hε) 1 ≃ₗ[ℤ] (N ε ⊗[ℤ] M) :=
  TensorProduct.congr (LinearEquiv.refl ℤ (N ε))
    (SymmetricPower.degreeOneLinearEquiv S.ambientBasis)

@[simp] theorem oneToTensor_tmul (a : N ε) (s : Sym[ℤ] (Fin 1) M) :
    oneToTensor ε hε S (a ⊗ₜ[ℤ] s) =
      a ⊗ₜ[ℤ] SymmetricPower.degreeOneLinearEquiv S.ambientBasis s := by
  exact TensorProduct.congr_tmul _ _ _ _

private theorem dTwo_factorization :
    (oneToTensor (ε := ε) hε S).toLinearMap.comp
        (dTwo (kernelPresentation ε hε) 0) =
      (TensorProduct.map (LinearMap.id : N ε →ₗ[ℤ] N ε)
          (LinearMap.ker ε).subtype).comp
        ((SymmetricPower.exteriorTwoToTensor
          (R := ℤ) (M := N ε)).comp
          (twoToExterior (ε := ε) hε S).toLinearMap) := by
  letI : IsScalarTower ℤ ℤ (⋀[ℤ]^2 (N ε)) :=
    ⟨fun r s x => (smul_smul r s x).symm⟩
  let Btwo : Module.Basis
      (Set.powersetCard (Fin S.rank) 2 × Sym (Fin S.rank) 0) ℤ
      (Two (kernelPresentation ε hε) 0) :=
    Module.Basis.tensorProduct (R := ℤ) (S := ℤ)
      (S.relationBasis.exteriorPower 2) (symZeroBasis (ε := ε) S)
  apply Btwo.ext
  rintro ⟨s, t⟩
  have ht : t = Sym.nil := Subsingleton.elim _ _
  subst t
  change _ = _
  rw [show Btwo (s, Sym.nil) =
      S.relationBasis.exteriorPower 2 s ⊗ₜ[ℤ]
        symZeroBasis (ε := ε) S Sym.nil by
    exact Module.Basis.tensorProduct_apply _ _ _ _,
    exteriorPower.basis_apply]
  let p : Fin 2 → Fin S.rank := s.val.orderEmbOfFin s.property
  rw [show exteriorPower.ιMulti_family ℤ 2 (⇑S.relationBasis) s =
      exteriorPower.ιMulti ℤ 2 (S.relationBasis ∘ p) by rfl]
  change (oneToTensor (ε := ε) hε S)
      (dTwo (kernelPresentation ε hε) 0
        ((exteriorPower.ιMulti ℤ 2 (S.relationBasis ∘ p)) ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil)) = _
  rw [dTwo_wedge_tmul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_apply]
  change (oneToTensor (ε := ε) hε S)
      (S.relationBasis (p 0) ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ M 0 (S.relationBasis (p 1)).1
            (SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil) -
        S.relationBasis (p 1) ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ M 0 (S.relationBasis (p 0)).1
            (SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil)) = _
  let u := S.relationBasis (p 0) ⊗ₜ[ℤ]
    SymmetricPower.insert ℤ M 0 (S.relationBasis (p 1)).1
      (SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil)
  let v := S.relationBasis (p 1) ⊗ₜ[ℤ]
    SymmetricPower.insert ℤ M 0 (S.relationBasis (p 0)).1
      (SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil)
  have hleft : (oneToTensor (ε := ε) hε S) (u - v) =
      S.relationBasis (p 0) ⊗ₜ[ℤ] (S.relationBasis (p 1)).1 -
        S.relationBasis (p 1) ⊗ₜ[ℤ] (S.relationBasis (p 0)).1 := by
    have hm := (oneToTensor (ε := ε) hε S).map_sub u v
    change (oneToTensor (ε := ε) hε S) (u - v) = _
    calc
      (oneToTensor (ε := ε) hε S) (u - v) =
          (oneToTensor (ε := ε) hε S) u -
            (oneToTensor (ε := ε) hε S) v := hm
      _ = _ := by
        dsimp only [u, v]
        rw [SymmetricPower.insert_monomialBasis_zero,
          SymmetricPower.insert_monomialBasis_zero]
        change
          (oneToTensor (ε := ε) hε S).toLinearMap
              (S.relationBasis (p 0) ⊗ₜ[ℤ]
                SymmetricPower.degreeOne (R := ℤ) (S.relationBasis (p 1)).1) -
            (oneToTensor (ε := ε) hε S).toLinearMap
              (S.relationBasis (p 1) ⊗ₜ[ℤ]
                SymmetricPower.degreeOne (R := ℤ) (S.relationBasis (p 0)).1) = _
        congr 1
        · have ht := oneToTensor_tmul (ε := ε) hε S
              (S.relationBasis (p 0))
              (SymmetricPower.degreeOne (R := ℤ) (S.relationBasis (p 1)).1)
          change (oneToTensor (ε := ε) hε S)
              (S.relationBasis (p 0) ⊗ₜ[ℤ]
                SymmetricPower.degreeOne (R := ℤ) (S.relationBasis (p 1)).1) = _
          exact ht.trans (by
            congr 1
            exact SymmetricPower.degreeOneLinearEquiv_degreeOne _ _)
        · have ht := oneToTensor_tmul (ε := ε) hε S
              (S.relationBasis (p 1))
              (SymmetricPower.degreeOne (R := ℤ) (S.relationBasis (p 0)).1)
          change (oneToTensor (ε := ε) hε S)
              (S.relationBasis (p 1) ⊗ₜ[ℤ]
                SymmetricPower.degreeOne (R := ℤ) (S.relationBasis (p 0)).1) = _
          exact ht.trans (by
            congr 1
            exact SymmetricPower.degreeOneLinearEquiv_degreeOne _ _)
  change (oneToTensor (ε := ε) hε S) (u - v) = _
  rw [hleft]
  change _ = (TensorProduct.map (LinearMap.id : N ε →ₗ[ℤ] N ε)
      (LinearMap.ker ε).subtype)
    (SymmetricPower.exteriorTwoToTensor
      ((twoToExterior (ε := ε) hε S)
        ((exteriorPower.ιMulti ℤ 2 (S.relationBasis ∘ p)) ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil)))
  change
    S.relationBasis (p 0) ⊗ₜ[ℤ] (S.relationBasis (p 1)).1 -
        S.relationBasis (p 1) ⊗ₜ[ℤ] (S.relationBasis (p 0)).1 =
      (TensorProduct.map (LinearMap.id : N ε →ₗ[ℤ] N ε)
        (LinearMap.ker ε).subtype)
        (SymmetricPower.exteriorTwoToTensor
          ((twoToExterior (ε := ε) hε S)
            ((exteriorPower.ιMulti ℤ 2 (S.relationBasis ∘ p)) ⊗ₜ[ℤ]
              SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil)))
  rw [show (twoToExterior (ε := ε) hε S)
      ((exteriorPower.ιMulti ℤ 2 (S.relationBasis ∘ p)) ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis S.ambientBasis 0 Sym.nil) =
      exteriorPower.ιMulti ℤ 2 (S.relationBasis ∘ p) by
    rw [twoToExterior_tmul,
      SymmetricPower.degreeZeroLinearEquiv_monomialBasis, one_smul]
    rfl]
  rw [SymmetricPower.exteriorTwoToTensor_ιMulti, map_sub,
    TensorProduct.map_tmul, TensorProduct.map_tmul]
  rfl

/-- The quadratic second differential of a finite kernel presentation is
injective.  This is the integral fact used to define the rational primitive;
it is not assumed as a general Koszul exactness theorem. -/
theorem dTwo_injective (S : InvariantFactorPresentation (N ε)) :
    Function.Injective (dTwo (kernelPresentation ε hε) 0) := by
  have hAlt : Function.Injective
      (SymmetricPower.exteriorTwoToTensor
        (R := ℤ) (M := N ε)) :=
    SymmetricPower.exteriorTwoToTensor_injective
      (S.relationBasis)
  have hTensor : Function.Injective
      (TensorProduct.map (LinearMap.id : N ε →ₗ[ℤ] N ε)
        (LinearMap.ker ε).subtype) :=
    TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id
      Subtype.val_injective
  intro x y hxy
  apply (twoToExterior (ε := ε) hε S).injective
  apply hAlt
  apply hTensor
  have h := congrArg (oneToTensor (ε := ε) hε S) hxy
  have hfac := dTwo_factorization (ε := ε) hε S
  have hx := LinearMap.congr_fun hfac x
  have hy := LinearMap.congr_fun hfac y
  rw [LinearMap.comp_apply] at hx hy
  change (TensorProduct.map (LinearMap.id : N ε →ₗ[ℤ] N ε)
      (LinearMap.ker ε).subtype)
        (SymmetricPower.exteriorTwoToTensor ((twoToExterior (ε := ε) hε S) x)) =
    (TensorProduct.map (LinearMap.id : N ε →ₗ[ℤ] N ε)
      (LinearMap.ker ε).subtype)
        (SymmetricPower.exteriorTwoToTensor ((twoToExterior (ε := ε) hε S) y))
  exact hx.symm.trans (h.trans hy)

/-- Extend an integral degree-two cochain across the injective quadratic
boundary map.  Divisibility of `ℚ` is the only universal-coefficient input. -/
noncomputable def rationalExtension
    (S : InvariantFactorPresentation (N ε))
    (h : Two (kernelPresentation ε hε) 0 →ₗ[ℤ] ℤ) :
    One (kernelPresentation ε hε) 1 →ₗ[ℤ] ℚ :=
  Classical.choose ((Module.Baer.of_divisible ℚ).extension_property
    (dTwo (kernelPresentation ε hε) 0) (dTwo_injective ε hε S)
    ((Int.castRingHom ℚ).toIntAlgHom.toLinearMap.comp h))

theorem rationalExtension_dTwo
    (S : InvariantFactorPresentation (N ε))
    (h : Two (kernelPresentation ε hε) 0 →ₗ[ℤ] ℤ)
    (y : Two (kernelPresentation ε hε) 0) :
    rationalExtension ε hε S h (dTwo (kernelPresentation ε hε) 0 y) =
      (h y : ℚ) := by
  have hext := Classical.choose_spec
    ((Module.Baer.of_divisible ℚ).extension_property
      (dTwo (kernelPresentation ε hε) 0) (dTwo_injective ε hε S)
      ((Int.castRingHom ℚ).toIntAlgHom.toLinearMap.comp h))
  exact LinearMap.congr_fun hext y

/-! ## The direct universal-coefficient character

The following is the small universal-coefficient construction actually used
below.  A rational primitive is precisely the unique rational evaluation on
degree-one cycles: its value on an integral boundary is the integral value of
the degree-two cochain.  Reducing this primitive modulo `ℤ` therefore kills
boundaries and gives a character of the literal Koszul homology quotient.
-/

/-- The quotient map `ℚ → ℚ/ℤ`, as an integral linear map. -/
def ratToCircle : ℚ →ₗ[ℤ] LieRings.RatCircle where
  toFun x := (x : LieRings.RatCircle)
  map_add' := by intro x y; exact AddCircle.coe_add (1 : ℚ) x y
  map_smul' := by intro z x; simpa using AddCircle.coe_zsmul (1 : ℚ)

@[simp] theorem ratToCircle_apply (x : ℚ) :
    ratToCircle x = (x : LieRings.RatCircle) := rfl

@[simp] theorem ratToCircle_intCast (z : ℤ) :
    ratToCircle (z : ℚ) = 0 := by
  rw [ratToCircle_apply, AddCircle.coe_eq_zero_iff]
  exact ⟨z, by simp⟩

/-- The exact data needed to evaluate an integral degree-two cochain on the
unique rational preimage of an integral quadratic cycle.  Point 5 constructs
this data in ordered Smith coordinates; no general derived-category UCT is
introduced. -/
structure RationalPrimitive (h : Two (kernelPresentation ε hε) 0 →ₗ[ℤ] ℤ) where
  value : cyclesOne (kernelPresentation ε hε) 1 →ₗ[ℤ] ℚ
  boundary : ∀ y : Two (kernelPresentation ε hε) 0,
    value (boundaryMapOne (kernelPresentation ε hε) 1 y) = (h y : ℚ)

/-- The rational primitive attached to an integral quadratic cochain. -/
noncomputable def rationalPrimitive
    (S : InvariantFactorPresentation (N ε))
    (h : Two (kernelPresentation ε hε) 0 →ₗ[ℤ] ℤ) :
    RationalPrimitive ε hε h where
  value := (rationalExtension ε hε S h).domRestrict
    (cyclesOne (kernelPresentation ε hε) 1)
  boundary y := rationalExtension_dTwo ε hε S h y

/-- Direct quadratic UCT: evaluate the unique rational primitive and reduce
modulo the integers. -/
def uctCharacter (h : Two (kernelPresentation ε hε) 0 →ₗ[ℤ] ℤ)
    (primitive : RationalPrimitive ε hε h) :
    homologyOne (kernelPresentation ε hε) 1 →ₗ[ℤ] LieRings.RatCircle :=
  (boundariesOne (kernelPresentation ε hε) 1).liftQ
    (ratToCircle.comp primitive.value) (by
      rintro x ⟨y, rfl⟩
      change ratToCircle (primitive.value
        (boundaryMapOne (kernelPresentation ε hε) 1 y)) = 0
      rw [primitive.boundary]
      exact ratToCircle_intCast (h y))

@[simp] theorem uctCharacter_mk
    (h : Two (kernelPresentation ε hε) 0 →ₗ[ℤ] ℤ)
    (primitive : RationalPrimitive ε hε h)
    (c : cyclesOne (kernelPresentation ε hε) 1) :
    uctCharacter ε hε h primitive
        ((boundariesOne (kernelPresentation ε hε) 1).mkQ c) =
      (primitive.value c : LieRings.RatCircle) := by
  change ratToCircle (primitive.value c) = _
  rw [ratToCircle_apply]

/-- The rational primitive is unique whenever the rationalized second
differential is onto the rationalized cycle module.  This packages the sole
uniqueness statement needed for independence of all coordinate choices. -/
theorem uctCharacter_eq_of_value_sub_integer
    (h h' : Two (kernelPresentation ε hε) 0 →ₗ[ℤ] ℤ)
    (p : RationalPrimitive ε hε h) (p' : RationalPrimitive ε hε h')
    (hint : ∀ c, ∃ z : ℤ, p.value c - p'.value c = z) :
    uctCharacter ε hε h p = uctCharacter ε hε h' p' := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective
    (boundariesOne (kernelPresentation ε hε) 1) x
  rw [uctCharacter_mk, uctCharacter_mk]
  obtain ⟨z, hz⟩ := hint c
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub, hz]
  change ratToCircle (z : ℚ) = 0
  exact ratToCircle_intCast z

/-- Any two rational primitives of the same integral quadratic cochain differ
by an integer on integral cycles.  In ordered Smith coordinates this is the
literal denominator-clearing assertion behind independence of the Baer
extension. -/
theorem rationalCycleExtensions_sub_integer
    (S : InvariantFactorPresentation (N ε))
    (h : Two (kernelPresentation ε hε) 0 →ₗ[ℤ] ℤ)
    (p : RationalPrimitive ε hε h)
    (c : cyclesOne (kernelPresentation ε hε) 1) :
    ratToCircle (p.value c -
      (rationalPrimitive ε hε S h).value c) = 0 := by
  let f : cyclesOne (kernelPresentation ε hε) 1 →ₗ[ℤ] ℚ :=
    p.value - (rationalPrimitive ε hε S h).value
  have f_boundary (y : Two (kernelPresentation ε hε) 0) :
      f (boundaryMapOne (kernelPresentation ε hε) 1 y) = 0 := by
    change p.value (boundaryMapOne (kernelPresentation ε hε) 1 y) -
      (rationalPrimitive ε hε S h).value
        (boundaryMapOne (kernelPresentation ε hε) 1 y) = 0
    rw [p.boundary, (rationalPrimitive ε hε S h).boundary, sub_self]
  -- A finite-index Smith lattice becomes all of `M` over `ℚ`; consequently
  -- the quadratic boundary lattice has finite index in the cycle lattice.
  -- We only need the elementwise denominator for `c`.
  have hden : ∃ d : ℕ, 0 < d ∧ ∃ y : Two (kernelPresentation ε hε) 0,
      (d : ℤ) • c.1 = dTwo (kernelPresentation ε hε) 0 y := by
    let B := oneBasis (ε := ε) hε S
    let coeff := B.repr c.1
    -- The cycle equations give the exact horizontal decomposition.  Taking
    -- the product of the positive diagonal entries clears all horizontal
    -- boundary denominators at once.
    let d : ℕ := ∏ i : Fin S.rank, S.diagonal i
    have hd : 0 < d := Finset.prod_pos fun i _ ↦ S.diagonal_pos i
    let y : Two (kernelPresentation ε hε) 0 :=
      ∑ i : Fin S.rank, ∑ j : Fin S.rank,
        if hij : i < j then
          (-(((d / S.diagonal i : ℕ) : ℤ) * coeff (j, i)) : ℤ) •
            twoGenerator (ε := ε) hε S i j
        else 0
    refine ⟨d, hd, y, ?_⟩
    -- Equality in the tensor basis; diagonal coefficients vanish and each
    -- off-diagonal pair is the horizontal Smith cycle.
    apply B.repr.injective
    apply Finsupp.ext
    rintro ⟨i, j⟩
    have hcycle := c.property
    have hcoord : ((SymmetricPower.monomialBasis S.ambientBasis 2).repr
        (dOne (kernelPresentation ε hε) 1 c.1))
          (i ::ₛ j ::ₛ Sym.nil) = 0 := by
      rw [hcycle]
      exact congrArg (fun z ↦ z (i ::ₛ j ::ₛ Sym.nil))
        ((SymmetricPower.monomialBasis S.ambientBasis 2).repr.map_zero)
    -- The coefficient of `xᵢxⱼ` is the Smith cycle equation.
    have hpair (hij : i ≠ j) : (S.diagonal i : ℤ) * coeff (i, j) +
        (S.diagonal j : ℤ) * coeff (j, i) = 0 := by
      rw [← B.sum_repr c.1] at hcoord
      dsimp only [B] at hcoord
      rw [map_sum] at hcoord
      simp only [map_smul, map_zero, Finsupp.zero_apply] at hcoord
      change ((SymmetricPower.monomialBasis S.ambientBasis 2).repr
          (∑ x : Fin S.rank × Fin S.rank,
            coeff x • dOne (kernelPresentation ε hε) 1
              (oneBasis (ε := ε) hε S x)))
          (i ::ₛ j ::ₛ Sym.nil) = 0 at hcoord
      have hsum : (∑ x : Fin S.rank × Fin S.rank,
            coeff x • dOne (kernelPresentation ε hε) 1
              (oneBasis (ε := ε) hε S x)) =
          ∑ x : Fin S.rank × Fin S.rank,
            coeff x • (S.diagonal x.1 : ℤ) •
              SymmetricPower.monomialBasis S.ambientBasis 2
                (x.1 ::ₛ x.2 ::ₛ Sym.nil) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [dOne_oneBasis_smith]
        rfl
      have hcoord' := congrArg
        (fun z ↦ (SymmetricPower.monomialBasis S.ambientBasis 2).repr z
          (i ::ₛ j ::ₛ Sym.nil)) hsum
      change ((SymmetricPower.monomialBasis S.ambientBasis 2).repr
          (∑ x, coeff x • dOne (kernelPresentation ε hε) 1
            (oneBasis (ε := ε) hε S x)))
          (i ::ₛ j ::ₛ Sym.nil) = _ at hcoord'
      rw [hcoord] at hcoord'
      simp only [map_sum, map_smul,
        (SymmetricPower.monomialBasis S.ambientBasis 2).repr_self,
        Finsupp.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, map_zero,
        Finsupp.zero_apply] at hcoord'
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (i, j)),
        ← Finset.add_sum_erase (Finset.univ.erase (i, j)) _
          (show (j, i) ∈ (Finset.univ.erase (i, j)) by simp [hij])] at hcoord'
      have hrest : ((∑ x ∈ (Finset.univ.erase (i, j)).erase (j, i),
          coeff x • (S.diagonal x.1 : ℤ) •
            Finsupp.single (x.1 ::ₛ x.2 ::ₛ Sym.nil) (1 : ℤ)) :
              Sym (Fin S.rank) 2 →₀ ℤ) (i ::ₛ j ::ₛ Sym.nil) = 0 := by
        let ev : (Sym (Fin S.rank) 2 →₀ ℤ) →+ ℤ :=
          Finsupp.applyAddHom (i ::ₛ j ::ₛ Sym.nil)
        change ev (∑ x ∈ (Finset.univ.erase (i, j)).erase (j, i),
          coeff x • (S.diagonal x.1 : ℤ) •
            Finsupp.single (x.1 ::ₛ x.2 ::ₛ Sym.nil) (1 : ℤ)) = 0
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Finset.mem_erase] at hx
        have hne : x.1 ::ₛ x.2 ::ₛ Sym.nil ≠ i ::ₛ j ::ₛ Sym.nil := by
          intro heq
          have hm : x.1 ::ₘ {x.2} = i ::ₘ {j} :=
            congrArg Sym.toMultiset heq
          rw [Multiset.cons_eq_cons] at hm
          rcases hm with (⟨h1, h2⟩ | ⟨h1, t, h2, h3⟩)
          · apply hx.2.1
            apply Prod.ext h1
            exact Multiset.singleton_inj.mp h2
          · apply hx.1
            have ht : t = 0 := by
              simpa using congrArg Multiset.card h2
            subst t
            apply Prod.ext
            · simpa using h3.symm
            · simpa using h2
        simp [ev, hne]
      simp only [Finsupp.add_apply, Finsupp.sum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at hcoord'
      rw [hrest, add_zero] at hcoord'
      have hswap : j ::ₛ i ::ₛ Sym.nil = i ::ₛ j ::ₛ Sym.nil :=
        Sym.cons_swap j i Sym.nil
      simp only [if_pos rfl, hswap, Finsupp.add_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at hcoord'
      simp only [if_pos] at hcoord'
      ring_nf at hcoord' ⊢
      exact hcoord'.symm
    change B.repr ((d : ℤ) • c.1) (i, j) =
      B.repr (dTwo (kernelPresentation ε hε) 0 y) (i, j)
    rw [map_zsmul]
    change (d : ℤ) * coeff (i, j) = _
    simp only [y, map_sum]
    simp_rw [apply_dite (dTwo (kernelPresentation ε hε) 0)]
    simp only [map_zsmul, map_zero]
    simp_rw [dTwo_twoGenerator_raw (ε := ε) hε S]
    dsimp only [B]
    simp_rw [apply_dite (oneBasis (ε := ε) hε S).repr]
    simp only [map_smul, map_sub, map_zero,
      (oneBasis (ε := ε) hε S).repr_self]
    let ev : (Fin S.rank × Fin S.rank →₀ ℤ) →+ ℤ :=
      Finsupp.applyAddHom (i, j)
    change (d : ℤ) * coeff (i, j) = ev _
    simp only [map_sum, map_zsmul, ev, Finsupp.applyAddHom_apply]
    try simp_rw [ite_apply]
    try simp only [Pi.zero_apply, Finsupp.smul_apply, Finsupp.sub_apply,
      Finsupp.single_apply, smul_eq_mul]
    have happ (x z : Fin S.rank) :
        ((if hxz : x < z then
            -(↑(d / S.diagonal x) * coeff (z, x)) •
              ((S.diagonal z : ℤ) • Finsupp.single (x, z) 1 -
                (S.diagonal x : ℤ) • Finsupp.single (z, x) 1)
          else 0) : Fin S.rank × Fin S.rank →₀ ℤ) (i, j) =
        if hxz : x < z then
          (-(↑(d / S.diagonal x) * coeff (z, x)) •
            ((S.diagonal z : ℤ) •
                Finsupp.single (x, z) (1 : ℤ) -
              (S.diagonal x : ℤ) •
                Finsupp.single (z, x) (1 : ℤ))) (i, j)
        else 0 := by
      by_cases hxz : x < z <;> simp [hxz]
    simp_rw [happ]
    simp only [Finsupp.smul_apply, Finsupp.sub_apply,
      Finsupp.single_apply, smul_eq_mul]
    let term : Fin S.rank → Fin S.rank → ℤ := fun x z ↦
      if x < z then
        -(((d / S.diagonal x : ℕ) : ℤ) * coeff (z, x)) *
          ((S.diagonal z : ℤ) * if (x, z) = (i, j) then 1 else 0) -
        -(((d / S.diagonal x : ℕ) : ℤ) * coeff (z, x)) *
          ((S.diagonal x : ℤ) * if (z, x) = (i, j) then 1 else 0)
      else 0
    have hterm (x z : Fin S.rank) :
        (if x < z then
          -(((d / S.diagonal x : ℕ) : ℤ) * coeff (z, x)) *
            (((S.diagonal z : ℤ) * if (x, z) = (i, j) then 1 else 0) -
              ((S.diagonal x : ℤ) * if (z, x) = (i, j) then 1 else 0))
        else 0) = term x z := by
      by_cases hxz : x < z
      · simp only [hxz, if_true, term]
        by_cases h₁ : (x, z) = (i, j) <;>
          by_cases h₂ : (z, x) = (i, j) <;> simp [h₁, h₂] <;> ring
      · simp [term, hxz]
    have hsum : (∑ x, ∑ z,
        (if hxz : x < z then
          -(((d / S.diagonal x : ℕ) : ℤ) * coeff (z, x)) *
            (((S.diagonal z : ℤ) * if (x, z) = (i, j) then 1 else 0) -
              ((S.diagonal x : ℤ) * if (z, x) = (i, j) then 1 else 0))
        else 0)) = ∑ x, ∑ z, term x z := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      simpa only using hterm x z
    rw [hsum]
    have term_eq_zero_of_ne (x z : Fin S.rank)
        (h₁ : x ≠ i ∨ z ≠ j) (h₂ : z ≠ i ∨ x ≠ j) :
        term x z = 0 := by
      have hp₁ : (x, z) ≠ (i, j) := by
        intro h
        rcases Prod.mk.inj h with ⟨rfl, rfl⟩
        exact h₁.elim (fun h ↦ h rfl) (fun h ↦ h rfl)
      have hp₂ : (z, x) ≠ (i, j) := by
        intro h
        rcases Prod.mk.inj h with ⟨rfl, rfl⟩
        exact h₂.elim (fun h ↦ h rfl) (fun h ↦ h rfl)
      by_cases hxz : x < z
      · simp only [term, hxz, if_true]
        rw [if_neg hp₁, if_neg hp₂]
        ring
      · simp [term, hxz]
    by_cases hij : i < j
    · have hdi : S.diagonal i ∣ d :=
        Finset.dvd_prod_of_mem S.diagonal (Finset.mem_univ i)
      have hclear : (d / S.diagonal i) * S.diagonal i = d :=
        Nat.div_mul_cancel hdi
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · rw [show term i j =
              -(((d / S.diagonal i : ℕ) : ℤ) * coeff (j, i)) *
                (S.diagonal j : ℤ) by simp [term, hij, hij.ne]]
          have hp := hpair hij.ne
          have hcast : (((d / S.diagonal i : ℕ) : ℤ) *
              (S.diagonal i : ℤ)) = (d : ℤ) := by exact_mod_cast hclear
          calc
            (d : ℤ) * coeff (i, j) =
                (((d / S.diagonal i : ℕ) : ℤ) * (S.diagonal i : ℤ)) *
                  coeff (i, j) := by rw [hcast]
            _ = ((d / S.diagonal i : ℕ) : ℤ) *
                ((S.diagonal i : ℤ) * coeff (i, j)) := by ring
            _ = ((d / S.diagonal i : ℕ) : ℤ) *
                (-((S.diagonal j : ℤ) * coeff (j, i))) := by
                  rw [eq_neg_of_add_eq_zero_left hp]
            _ = -(((d / S.diagonal i : ℕ) : ℤ) * coeff (j, i)) *
                (S.diagonal j : ℤ) := by ring
        · intro z _ hzj
          apply term_eq_zero_of_ne
          · exact Or.inr hzj
          · exact Or.inr hij.ne
        · intro hcontra
          exact (hcontra (Finset.mem_univ j)).elim
      · intro x _ hxi
        apply Finset.sum_eq_zero
        intro z _
        have h₁ : x ≠ i ∨ z ≠ j := Or.inl hxi
        by_cases h₂ : (z, x) = (i, j)
        · have hzi : z = i := (Prod.mk.inj h₂).1
          have hxj : x = j := (Prod.mk.inj h₂).2
          rw [hzi, hxj]
          simp [term, not_lt_of_ge hij.le]
        · have h₂' : z ≠ i ∨ x ≠ j := by
            by_cases hzi : z = i
            · right
              intro hxj
              exact h₂ (Prod.ext hzi hxj)
            · exact Or.inl hzi
          exact term_eq_zero_of_ne x z h₁ h₂'
      · intro hcontra
        exact (hcontra (Finset.mem_univ i)).elim
    · by_cases hji : j < i
      · have hdj : S.diagonal j ∣ d :=
          Finset.dvd_prod_of_mem S.diagonal (Finset.mem_univ j)
        have hclear : (d / S.diagonal j) * S.diagonal j = d :=
          Nat.div_mul_cancel hdj
        rw [Finset.sum_eq_single j]
        · rw [Finset.sum_eq_single i]
          · rw [show term j i =
                (((d / S.diagonal j : ℕ) : ℤ) * coeff (i, j)) *
                  (S.diagonal j : ℤ) by simp [term, hij, hji, hji.ne]]
            have hcast : (((d / S.diagonal j : ℕ) : ℤ) *
                (S.diagonal j : ℤ)) = (d : ℤ) := by exact_mod_cast hclear
            rw [← hcast]
            ring
          · intro z _ hzi
            apply term_eq_zero_of_ne
            · exact Or.inl hji.ne
            · exact Or.inl hzi
          · intro hcontra
            exact (hcontra (Finset.mem_univ i)).elim
        · intro x _ hxj
          apply Finset.sum_eq_zero
          intro z _
          have h₂ : z ≠ i ∨ x ≠ j := Or.inr hxj
          by_cases h₁ : (x, z) = (i, j)
          · have hxi : x = i := (Prod.mk.inj h₁).1
            have hzj : z = j := (Prod.mk.inj h₁).2
            rw [hxi, hzj]
            simp [term, hij]
          · have h₁' : x ≠ i ∨ z ≠ j := by
              by_cases hxi : x = i
              · right
                intro hzj
                exact h₁ (Prod.ext hxi hzj)
              · exact Or.inl hxi
            exact term_eq_zero_of_ne x z h₁' h₂
        · intro hcontra
          exact (hcontra (Finset.mem_univ j)).elim
      · have hii : i = j := le_antisymm (not_lt.mp hji) (not_lt.mp hij)
        subst j
        have hd0 : coeff (i, i) = 0 := by
          have hsumDiag : dOne (kernelPresentation ε hε) 1 c.1 =
              ∑ x : Fin S.rank × Fin S.rank,
                coeff x • (S.diagonal x.1 : ℤ) •
                  SymmetricPower.monomialBasis S.ambientBasis 2
                    (x.1 ::ₛ x.2 ::ₛ Sym.nil) := by
            rw [← B.sum_repr c.1, map_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [map_smul, dOne_oneBasis_smith]
            rfl
          rw [hsumDiag] at hcoord
          simp only [map_sum, map_smul,
            (SymmetricPower.monomialBasis S.ambientBasis 2).repr_self,
            Finsupp.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
            smul_eq_mul, mul_ite, mul_one, mul_zero] at hcoord
          have hindex (x : Fin S.rank × Fin S.rank)
              (hx : x.1 ::ₛ x.2 ::ₛ Sym.nil = i ::ₛ i ::ₛ Sym.nil) :
              x = (i, i) := by
            have hm : x.1 ::ₘ {x.2} = i ::ₘ {i} :=
              congrArg Sym.toMultiset hx
            rw [Multiset.cons_eq_cons] at hm
            rcases hm with (⟨h1, h2⟩ | ⟨h1, t, h2, h3⟩)
            · apply Prod.ext h1
              exact Multiset.singleton_inj.mp h2
            · have ht : t = 0 := by
                simpa using congrArg Multiset.card h2
              subst t
              apply Prod.ext
              · simpa using h3.symm
              · simpa using h2
          change (Finsupp.applyAddHom (i ::ₛ i ::ₛ Sym.nil))
              (∑ x, coeff x • (S.diagonal x.1 : ℤ) •
                Finsupp.single (x.1 ::ₛ x.2 ::ₛ Sym.nil) 1) = _ at hcoord
          rw [map_sum] at hcoord
          rw [Finset.sum_eq_single (i, i)] at hcoord
          · simp only [Finsupp.smul_apply, Finsupp.single_apply, if_pos,
                smul_eq_mul, mul_one] at hcoord
            change ((coeff (i, i) • (S.diagonal i : ℤ) •
              Finsupp.single (i ::ₛ i ::ₛ Sym.nil) 1) :
                Sym (Fin S.rank) 2 →₀ ℤ) (i ::ₛ i ::ₛ Sym.nil) = 0 at hcoord
            simp only [Finsupp.smul_apply, Finsupp.single_eq_same,
              smul_eq_mul, mul_one] at hcoord
            have hpos : (S.diagonal i : ℤ) ≠ 0 := by
              exact_mod_cast (S.diagonal_pos i).ne'
            have : (S.diagonal i : ℤ) * coeff (i, i) = 0 := by
              calc
                (S.diagonal i : ℤ) * coeff (i, i) =
                    coeff (i, i) * (S.diagonal i : ℤ) := mul_comm _ _
                _ = 0 := hcoord
            exact (mul_eq_zero.mp this).resolve_left hpos
          · intro x _ hx
            have hne : x.1 ::ₛ x.2 ::ₛ Sym.nil ≠
                i ::ₛ i ::ₛ Sym.nil := fun h ↦ hx (hindex x h)
            simp [hne]
          · intro hcontra
            exact (hcontra (Finset.mem_univ (i, i))).elim
        rw [hd0, mul_zero]
        apply Eq.symm
        apply Finset.sum_eq_zero
        intro x _
        apply Finset.sum_eq_zero
        intro z _
        by_cases hxz : x < z
        · have hxi_or_hzi : x ≠ i ∨ z ≠ i := by
            by_cases hxi : x = i
            · right
              intro hzi
              exact hxz.ne (hxi.trans hzi.symm)
            · exact Or.inl hxi
          exact term_eq_zero_of_ne x z hxi_or_hzi
            (hxi_or_hzi.elim (fun h ↦ Or.inr h) (fun h ↦ Or.inl h))
        · simp [term, hxz]
  obtain ⟨d, hd, y, hy⟩ := hden
  have hdc : (d : ℤ) • c.1 ∈
      cyclesOne (kernelPresentation ε hε) 1 := by
    change dOne (kernelPresentation ε hε) 1 ((d : ℤ) • c.1) = 0
    rw [map_zsmul, c.property]
    exact smul_zero _
  have hf : (d : ℤ) • f c = 0 := by
    rw [← map_zsmul]
    change f ⟨(d : ℤ) • c.1, hdc⟩ = 0
    rw [show (⟨(d : ℤ) • c.1, hdc⟩ :
        cyclesOne (kernelPresentation ε hε) 1) =
      boundaryMapOne (kernelPresentation ε hε) 1 y by
        apply Subtype.ext
        exact hy]
    exact f_boundary y
  have hdQ : (d : ℚ) ≠ 0 := by positivity
  have hf0 : f c = 0 := by
    change (d : ℚ) * f c = 0 at hf
    exact (mul_eq_zero.mp hf).resolve_left hdQ
  change ratToCircle (f c) = 0
  rw [hf0, map_zero]

/-! ## Exact division of integral linear maps -/

/-- Divide an integral linear map by a fixed positive integer when every
value is divisible by it.  The quotient is characterized by multiplication,
so additivity uses only torsion-freeness of `ℤ`. -/
noncomputable def divideLinear {X : Type*} [AddCommGroup X]
    (q : ℕ) (hq : 0 < q) (f : X →ₗ[ℤ] ℤ)
    (hdiv : ∀ x, (q : ℤ) ∣ f x) : X →ₗ[ℤ] ℤ :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x ↦ Classical.choose (hdiv x)
      map_zero' := by
        apply mul_left_cancel₀ (show (q : ℤ) ≠ 0 by exact_mod_cast hq.ne')
        rw [← Classical.choose_spec (hdiv 0), map_zero]
        simp
      map_add' := by
        intro x y
        have hx := Classical.choose_spec (hdiv x)
        have hy := Classical.choose_spec (hdiv y)
        have hxy := Classical.choose_spec (hdiv (x + y))
        have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
        apply mul_left_cancel₀ hq0
        rw [← hxy, mul_add, ← hx, ← hy, map_add] }

theorem mul_divideLinear {X : Type*} [AddCommGroup X]
    (q : ℕ) (hq : 0 < q) (f : X →ₗ[ℤ] ℤ)
    (hdiv : ∀ x, (q : ℤ) ∣ f x) (x : X) :
    (q : ℤ) * divideLinear q hq f hdiv x = f x :=
  (Classical.choose_spec (hdiv x)).symm


end

end Koszul.QuadraticUCT
