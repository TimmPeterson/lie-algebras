import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The coordinate certificate in degree five

This file formalizes Sections 2, 4, and the purely algebraic part of Section 3 of
`complete_proof_delta5_subset_gamma4.tex`.  Indices in `I` correspond to the generators
`x_i`, and indices in `K` to the named degree-two generators `y_k`.

The definitions below deliberately use the four displayed systems `(B)`, `(Z)`, `(C1)`,
`(C2)` and `(P1)`--`(P4)` from the paper.  Thus the certificate criterion proved here has no
PBW or Lie-theoretic hypothesis hidden in its statement.
-/

namespace LieRings

namespace DegreeFive

namespace Coordinate

open scoped BigOperators

noncomputable section

variable {I K : Type*} [Fintype I] [Fintype K]

/-- Coordinate data from the adapted presentation. -/
structure Data (I K : Type*) [Fintype I] [Fintype K] (q : ℕ) where
  d : I → ℕ
  e : K → ℕ
  B : I → K → ℤ
  G : I → K → ℤ

namespace Data

variable {q : ℕ} (D : Data I K q)

/-- The matrix `Γ = B Gᵀ`, reduced modulo `q`. -/
def gamma (i j : I) : ZMod q :=
  ∑ k, (D.B i k : ZMod q) * (D.G j k : ZMod q)

/-- The quotient `d_j / d_i` occurring above the diagonal. -/
def dRatio [LinearOrder I] (i j : I) : ℕ := D.d j / D.d i

/-- The four identities in `(2.8)` of the coordinate proof. -/
structure Identities [LinearOrder I] : Prop where
  d_dvd : ∀ {i j}, i ≤ j → D.d i ∣ D.d j
  DG : ∀ i k, (D.d i : ZMod q) * (D.G i k : ZMod q) = 0
  GE : ∀ i k, (D.G i k : ZMod q) * (D.e k : ZMod q) = 0
  gamma_diag : ∀ i, D.gamma i i = 0
  gamma_skew : ∀ {i j}, i < j →
    D.gamma j i + (D.dRatio i j : ZMod q) * D.gamma i j = 0

end Data

variable [LinearOrder I]

/-- The strictly upper-triangular index set used throughout the paper. -/
def upperPairs (I : Type*) [Fintype I] [LinearOrder I] : Finset (I × I) :=
  Finset.univ.filter fun ij ↦ ij.1 < ij.2

@[simp]
theorem mem_upperPairs {i j : I} : (i, j) ∈ upperPairs I ↔ i < j := by
  simp [upperPairs]

theorem sum_upperPairs {R : Type*} [AddCommMonoid R] (f : I → I → R) :
    (∑ ij ∈ upperPairs I, f ij.1 ij.2) =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), f i j := by
  rw [upperPairs, ← Finset.univ_product_univ]
  simp only [Finset.filter_product, Finset.sum_product, Finset.sum_filter]

theorem sum_upperPairs_right {R : Type*} [AddCommMonoid R] (f : I → I → R) :
    (∑ ij ∈ upperPairs I, f ij.1 ij.2) =
      ∑ j, ∑ i ∈ Finset.univ.filter (· < j), f i j := by
  rw [upperPairs, ← Finset.univ_product_univ]
  simp only [Finset.sum_product_right, Finset.sum_filter]

namespace Data

variable {q : ℕ} (D : Data I K q)

/-- The `i,k` entry of `\bar u B`, written without introducing a diagonal matrix. -/
def upperSkewMul (u : I → I → ℤ) (i : I) (k : K) : ℤ :=
  (∑ j ∈ Finset.univ.filter (i < ·), u i j * D.B j k) -
    ∑ j ∈ Finset.univ.filter (· < i),
      (D.dRatio j i : ℤ) * u j i * D.B j k

/-- The same entry after reduction modulo `q`. -/
def upperSkewMulMod (u : I → I → ℤ) (i : I) (k : K) : ZMod q :=
  (∑ j ∈ Finset.univ.filter (i < ·),
      (u i j : ZMod q) * (D.B j k : ZMod q)) -
    ∑ j ∈ Finset.univ.filter (· < i),
      (D.dRatio j i : ZMod q) * (u j i : ZMod q) * (D.B j k : ZMod q)

theorem intCast_upperSkewMul (u : I → I → ℤ) (i : I) (k : K) :
    (D.upperSkewMul u i k : ZMod q) = D.upperSkewMulMod u i k := by
  simp [upperSkewMul, upperSkewMulMod]

/-- The four equations extracted by PBW collection. -/
structure CoefficientSystem (ζ : ZMod q) where
  u : I → I → ℤ
  v : I → K → ℤ
  v' : I → K → ℤ
  B_eq : ∀ i k,
    D.upperSkewMul u i k + (D.d i : ℤ) * v i k + v' i k * (D.e k : ℤ) = 0
  Z_eq : (∑ ij ∈ upperPairs I,
      (u ij.1 ij.2 : ZMod q) * (D.dRatio ij.1 ij.2 : ZMod q) *
        D.gamma ij.1 ij.2) = ζ
  C1 : ∀ k l, k ≠ l →
    (Nat.gcd (D.e k) (D.e l) : ℤ) ∣
      ∑ i, (v i k * D.B i l + D.B i k * v i l)
  C2 : ∀ k, (D.e k : ℤ) ∣ ∑ i, v i k * D.B i k

/-- The matrix entry `(B αᵀ)_{ij}`. -/
def certificateX (α : I → K → ZMod q) (i j : I) : ZMod q :=
  ∑ k, (D.B i k : ZMod q) * α j k

/-- A certificate satisfying `(P1)`--`(P4)` in the coordinate proof. -/
structure Certificate where
  α : I → K → ZMod q
  Λ : K → K → ZMod q
  symmetric : ∀ k l, Λ k l = Λ l k
  P1 : ∀ {i j}, i < j →
    D.certificateX α j i - (D.dRatio i j : ZMod q) * D.certificateX α i j =
      D.gamma j i
  P2 : ∀ i k, (D.d i : ZMod q) * α i k =
    ∑ l, (D.B i l : ZMod q) * Λ l k
  P3 : ∀ i k, α i k * (D.e k : ZMod q) = 0
  P4 : ∀ k l, (D.e k : ZMod q) * Λ k l = 0

/-- The upper-triangular/Frobenius-pairing rearrangement used in the certificate criterion. -/
theorem upperPair_certificateX
    (u : I → I → ℤ) (α : I → K → ZMod q) :
    (∑ ij ∈ upperPairs I, (u ij.1 ij.2 : ZMod q) *
      (D.certificateX α ij.2 ij.1 -
        (D.dRatio ij.1 ij.2 : ZMod q) * D.certificateX α ij.1 ij.2)) =
      ∑ i, ∑ k, D.upperSkewMulMod u i k * α i k := by
  have hleft :
      (∑ ij ∈ upperPairs I,
          (u ij.1 ij.2 : ZMod q) * D.certificateX α ij.2 ij.1) =
        ∑ i, ∑ k,
          (∑ j ∈ Finset.univ.filter (i < ·),
            (u i j : ZMod q) * (D.B j k : ZMod q)) * α i k := by
    rw [sum_upperPairs (fun i j ↦
      (u i j : ZMod q) * D.certificateX α j i)]
    simp only [certificateX]
    simp_rw [Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hright :
      (∑ ij ∈ upperPairs I,
          (u ij.1 ij.2 : ZMod q) *
            ((D.dRatio ij.1 ij.2 : ZMod q) * D.certificateX α ij.1 ij.2)) =
        ∑ i, ∑ k,
          (∑ j ∈ Finset.univ.filter (· < i),
            (D.dRatio j i : ZMod q) * (u j i : ZMod q) *
              (D.B j k : ZMod q)) * α i k := by
    rw [sum_upperPairs_right (fun i j ↦
      (u i j : ZMod q) *
        ((D.dRatio i j : ZMod q) * D.certificateX α i j))]
    simp only [certificateX]
    simp_rw [Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hleft, hright]
  simp only [upperSkewMulMod, sub_mul, Finset.sum_sub_distrib]

private theorem mul_intCast_eq_zero_of_dvd
    {n : ℕ} {a : ZMod q} {z : ℤ}
    (ha : (n : ZMod q) * a = 0) (hz : (n : ℤ) ∣ z) :
    a * (z : ZMod q) = 0 := by
  obtain ⟨t, rfl⟩ := hz
  push_cast
  calc
    a * ((n : ZMod q) * (t : ZMod q)) =
        ((n : ZMod q) * a) * (t : ZMod q) := by ring
    _ = 0 := by rw [ha, zero_mul]

private theorem gcd_mul_eq_zero
    {a : ZMod q} {m n : ℕ}
    (hm : (m : ZMod q) * a = 0) (hn : (n : ZMod q) * a = 0) :
    (Nat.gcd m n : ZMod q) * a = 0 := by
  have hbez := Nat.gcd_eq_gcd_ab m n
  have hcast := congrArg (fun z : ℤ ↦ (z : ZMod q)) hbez
  push_cast at hcast
  rw [hcast]
  calc
    ((m : ZMod q) * (Nat.gcdA m n : ZMod q) +
        (n : ZMod q) * (Nat.gcdB m n : ZMod q)) * a =
      (Nat.gcdA m n : ZMod q) * ((m : ZMod q) * a) +
        (Nat.gcdB m n : ZMod q) * ((n : ZMod q) * a) := by ring
    _ = 0 := by rw [hm, hn, mul_zero, mul_zero, add_zero]

/-- **Coordinate certificate criterion.**  The four PBW equations `(B)`, `(Z)`, `(C1)`,
`(C2)`, the data identities, and a certificate `(P1)`--`(P4)` force the central coefficient
`ζ` to vanish.  This is Theorem 4.2 of the coordinate proof, separated from its Lie-theoretic
input. -/
theorem certificateCriterion
    (hD : D.Identities)
    {ζ : ZMod q} (s : D.CoefficientSystem ζ) (c : D.Certificate) : ζ = 0 := by
  let N : ZMod q :=
    ∑ ij ∈ upperPairs I, (s.u ij.1 ij.2 : ZMod q) * D.gamma ij.2 ij.1
  have hzetaN : ζ + N = 0 := by
    rw [← s.Z_eq]
    change
      (∑ ij ∈ upperPairs I,
          (s.u ij.1 ij.2 : ZMod q) *
            (D.dRatio ij.1 ij.2 : ZMod q) * D.gamma ij.1 ij.2) +
        (∑ ij ∈ upperPairs I,
          (s.u ij.1 ij.2 : ZMod q) * D.gamma ij.2 ij.1) = 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro ij hij
    have hlt : ij.1 < ij.2 := mem_upperPairs.mp hij
    have hskew := hD.gamma_skew hlt
    calc
      (s.u ij.1 ij.2 : ZMod q) * (D.dRatio ij.1 ij.2 : ZMod q) *
            D.gamma ij.1 ij.2 +
          (s.u ij.1 ij.2 : ZMod q) * D.gamma ij.2 ij.1 =
        (s.u ij.1 ij.2 : ZMod q) *
          (D.gamma ij.2 ij.1 +
            (D.dRatio ij.1 ij.2 : ZMod q) * D.gamma ij.1 ij.2) := by ring
      _ = 0 := by rw [hskew, mul_zero]
  have hNpair : N =
      ∑ i, ∑ k, D.upperSkewMulMod s.u i k * c.α i k := by
    calc
      N = ∑ ij ∈ upperPairs I, (s.u ij.1 ij.2 : ZMod q) *
          (D.certificateX c.α ij.2 ij.1 -
            (D.dRatio ij.1 ij.2 : ZMod q) *
              D.certificateX c.α ij.1 ij.2) := by
        apply Finset.sum_congr rfl
        intro ij hij
        rw [c.P1 (mem_upperPairs.mp hij)]
      _ = _ := D.upperPair_certificateX s.u c.α
  have hBmod : ∀ i k,
      D.upperSkewMulMod s.u i k +
          (D.d i : ZMod q) * (s.v i k : ZMod q) +
          (s.v' i k : ZMod q) * (D.e k : ZMod q) = 0 := by
    intro i k
    have h := congrArg (fun z : ℤ ↦ (z : ZMod q)) (s.B_eq i k)
    push_cast at h
    rwa [D.intCast_upperSkewMul] at h
  have hNrelations : N =
      -∑ i, ∑ k,
        ((D.d i : ZMod q) * (s.v i k : ZMod q) +
          (s.v' i k : ZMod q) * (D.e k : ZMod q)) * c.α i k := by
    rw [hNpair]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have h := hBmod i k
    have hu : D.upperSkewMulMod s.u i k =
        -((D.d i : ZMod q) * (s.v i k : ZMod q) +
          (s.v' i k : ZMod q) * (D.e k : ZMod q)) := by
      apply (eq_neg_iff_add_eq_zero).2
      simpa only [add_assoc] using h
    rw [hu]
    ring
  have hNlambda : N =
      -∑ i, ∑ k, (s.v i k : ZMod q) *
        (∑ l, (D.B i l : ZMod q) * c.Λ l k) := by
    rw [hNrelations]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    have hp2 := c.P2 i k
    have hp3 := c.P3 i k
    calc
      ((D.d i : ZMod q) * (s.v i k : ZMod q) +
          (s.v' i k : ZMod q) * (D.e k : ZMod q)) * c.α i k =
        (s.v i k : ZMod q) * ((D.d i : ZMod q) * c.α i k) +
          (s.v' i k : ZMod q) * (c.α i k * (D.e k : ZMod q)) := by ring
      _ = (s.v i k : ZMod q) *
          (∑ l, (D.B i l : ZMod q) * c.Λ l k) := by
        rw [hp2, hp3, mul_zero, add_zero]
  let S : K → K → ℤ := fun k l ↦ ∑ i, s.v i k * D.B i l
  have hNmatrix : N = -∑ kl : K × K, c.Λ kl.2 kl.1 * (S kl.1 kl.2 : ZMod q) := by
    rw [hNlambda]
    congr 1
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [S, Int.cast_sum, Int.cast_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpair : ∀ kl : K × K,
      c.Λ kl.2 kl.1 * (S kl.1 kl.2 : ZMod q) +
        c.Λ kl.1 kl.2 * (S kl.2 kl.1 : ZMod q) = 0 := by
    rintro ⟨k, l⟩
    rcases eq_or_ne k l with hEq | hNe
    · subst l
      have hz : c.Λ k k * (S k k : ZMod q) = 0 :=
        mul_intCast_eq_zero_of_dvd (c.P4 k k) (s.C2 k)
      rw [hz, add_zero]
    · have hel : (D.e l : ZMod q) * c.Λ k l = 0 := by
        simpa only [c.symmetric l k] using c.P4 l k
      have hgcd : (Nat.gcd (D.e k) (D.e l) : ZMod q) * c.Λ k l = 0 :=
        gcd_mul_eq_zero (c.P4 k l) hel
      have hdiv : (Nat.gcd (D.e k) (D.e l) : ℤ) ∣ S k l + S l k := by
        simpa only [S, ← Finset.sum_add_distrib, mul_comm] using s.C1 k l hNe
      have hz : c.Λ k l *
          ((S k l + S l k : ℤ) : ZMod q) = 0 :=
        mul_intCast_eq_zero_of_dvd hgcd hdiv
      rw [c.symmetric l k]
      push_cast at hz
      calc
        c.Λ k l * (S k l : ZMod q) +
            c.Λ k l * (S l k : ZMod q) =
          c.Λ k l * ((S k l : ZMod q) + (S l k : ZMod q)) := by ring
        _ = 0 := hz
  have hsum : (∑ kl : K × K,
      c.Λ kl.2 kl.1 * (S kl.1 kl.2 : ZMod q)) = 0 := by
    classical
    apply Finset.sum_involution (s := Finset.univ)
      (fun kl _ ↦ (kl.2, kl.1))
    · intro kl _
      exact hpair kl
    · intro kl _ hne hfix
      have hdiag : kl.1 = kl.2 := (congrArg Prod.fst hfix).symm
      rcases kl with ⟨k, l⟩
      simp only at hdiag
      subst l
      have hz : c.Λ k k * (S k k : ZMod q) = 0 :=
        mul_intCast_eq_zero_of_dvd (c.P4 k k) (s.C2 k)
      exact (hne hz).elim
    · intro kl _
      simp
    · intro kl _
      rfl
  have hNzero : N = 0 := by rw [hNmatrix, hsum, neg_zero]
  rw [hNzero, add_zero] at hzetaN
  exact hzetaN

end Data

end


end Coordinate

end DegreeFive

end LieRings
