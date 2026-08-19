import LieRings.PBW.CartanEilenberg
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Weight

/-!
# Integral ordered PBW for a based Lie ring

This file closes the single compatibility hypothesis left by the Cartan--Eilenberg
construction.  All degree bookkeeping is private; the only exported result is the ordered PBW
theorem needed by the metabelian odd-dimension argument.
-/

namespace LieRings.DimensionSubring.MetabelianOdd

noncomputable section

open LieRings.PBW

universe u v

variable (L : Type u) [LieRing L]
variable (ι : Type v) [LinearOrder ι]
variable (b : Module.Basis ι ℤ L)

/-- Polynomial filtration used in the Cartan--Eilenberg induction. -/
private def DegreeLE (d : ℕ) (p : MvPolynomial ι ℤ) : Prop :=
  ∀ e ∈ p.support, exponentDegree ι e ≤ d

private theorem degreeLE_iff_totalDegree_le (d : ℕ) (p : MvPolynomial ι ℤ) :
    DegreeLE ι d p ↔ p.totalDegree ≤ d := by
  constructor
  · intro h
    rw [MvPolynomial.totalDegree_eq, Finset.sup_le_iff]
    intro e he
    simpa [exponentDegree] using h e he
  · intro h e he
    exact (MvPolynomial.le_totalDegree he).trans h

private theorem degreeLE_zero (d : ℕ) :
    DegreeLE ι d (0 : MvPolynomial ι ℤ) := by
  simp [DegreeLE]

private theorem degreeLE_add {d : ℕ} {p q : MvPolynomial ι ℤ}
    (hp : DegreeLE ι d p) (hq : DegreeLE ι d q) : DegreeLE ι d (p + q) := by
  rw [degreeLE_iff_totalDegree_le] at hp hq ⊢
  exact (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)

private theorem degreeLE_sub {d : ℕ} {p q : MvPolynomial ι ℤ}
    (hp : DegreeLE ι d p) (hq : DegreeLE ι d q) : DegreeLE ι d (p - q) := by
  rw [degreeLE_iff_totalDegree_le] at hp hq ⊢
  exact (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq)

private theorem degreeLE_smul {d : ℕ} (r : ℤ) {p : MvPolynomial ι ℤ}
    (hp : DegreeLE ι d p) : DegreeLE ι d (r • p) := by
  rw [degreeLE_iff_totalDegree_le] at hp ⊢
  exact (MvPolynomial.totalDegree_smul_le r p).trans hp

private theorem degreeLE_neg {d : ℕ} {p : MvPolynomial ι ℤ}
    (hp : DegreeLE ι d p) : DegreeLE ι d (-p) := by
  rw [degreeLE_iff_totalDegree_le] at hp ⊢
  simpa using hp

private theorem degreeLE_mono {d e : ℕ} {p : MvPolynomial ι ℤ}
    (hde : d ≤ e) (hp : DegreeLE ι d p) : DegreeLE ι e p := by
  exact fun a ha ↦ (hp a ha).trans hde

private theorem degreeLE_mul {d e : ℕ} {p q : MvPolynomial ι ℤ}
    (hp : DegreeLE ι d p) (hq : DegreeLE ι e q) : DegreeLE ι (d + e) (p * q) := by
  rw [degreeLE_iff_totalDegree_le] at hp hq ⊢
  exact (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq)

private theorem degreeLE_monomial (e : ι →₀ ℕ) (r : ℤ) :
    DegreeLE ι (exponentDegree ι e) (MvPolynomial.monomial e r) := by
  rw [degreeLE_iff_totalDegree_le]
  exact MvPolynomial.totalDegree_monomial_le e r

private theorem degreeLE_X (i : ι) :
    DegreeLE ι 1 (MvPolynomial.X i : MvPolynomial ι ℤ) := by
  simpa [MvPolynomial.X, exponentDegree] using
    (degreeLE_monomial ι (Finsupp.single i 1) (1 : ℤ))

/-- A linear map preserves a polynomial filtration once this is known on unit monomials. -/
private theorem degreeLE_map_of_monomial
    (T : Module.End ℤ (MvPolynomial ι ℤ)) (q d : ℕ)
    (hT : ∀ e : ι →₀ ℕ, exponentDegree ι e ≤ q →
      DegreeLE ι d (T (MvPolynomial.monomial e 1)))
    (f : MvPolynomial ι ℤ) (hf : DegreeLE ι q f) : DegreeLE ι d (T f) := by
  rw [f.as_sum, map_sum]
  rw [degreeLE_iff_totalDegree_le]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  rw [show MvPolynomial.monomial e (MvPolynomial.coeff e f) =
      (MvPolynomial.coeff e f) • MvPolynomial.monomial e 1 by
    symm
    calc
      (MvPolynomial.coeff e f) • MvPolynomial.monomial e 1 =
          MvPolynomial.monomial e ((MvPolynomial.coeff e f) • (1 : ℤ)) :=
        MvPolynomial.smul_monomial _
      _ = MvPolynomial.monomial e (MvPolynomial.coeff e f) := by simp]
  rw [map_smul]
  rw [← degreeLE_iff_totalDegree_le]
  exact degreeLE_smul ι _ (hT e (hf e he))

private theorem linearMap_eq_on_degreeLE_of_monomial
    (A B : Module.End ℤ (MvPolynomial ι ℤ)) (q : ℕ)
    (hAB : ∀ e : ι →₀ ℕ, exponentDegree ι e ≤ q →
      A (MvPolynomial.monomial e 1) = B (MvPolynomial.monomial e 1))
    (f : MvPolynomial ι ℤ) (hf : DegreeLE ι q f) : A f = B f := by
  rw [f.as_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [show MvPolynomial.monomial e (MvPolynomial.coeff e f) =
      (MvPolynomial.coeff e f) • MvPolynomial.monomial e 1 by
    symm
    calc
      (MvPolynomial.coeff e f) • MvPolynomial.monomial e 1 =
          MvPolynomial.monomial e ((MvPolynomial.coeff e f) • (1 : ℤ)) :=
        MvPolynomial.smul_monomial _
      _ = MvPolynomial.monomial e (MvPolynomial.coeff e f) := by simp]
  rw [map_smul, map_smul, hAB e (hf e he)]

private theorem basisPolynomial_degreeLE (x : L) :
    DegreeLE ι 1 (basisPolynomial ℤ L ι b x) := by
  unfold basisPolynomial
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [degreeLE_iff_totalDegree_le]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  rw [← degreeLE_iff_totalDegree_le]
  exact degreeLE_smul ι ((b.repr x) i) (degreeLE_X ι i)

private theorem degreeLE_linearMap_of_basis
    (A : L →ₗ[ℤ] MvPolynomial ι ℤ) (d : ℕ)
    (hA : ∀ i : ι, DegreeLE ι d (A (b i))) (x : L) :
    DegreeLE ι d (A x) := by
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  rw [degreeLE_iff_totalDegree_le]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  rw [map_smul]
  rw [← degreeLE_iff_totalDegree_le]
  exact degreeLE_smul ι ((b.repr x) i) (hA i)

private theorem exponentDegree_toFinsupp (is : List ι) :
    exponentDegree ι (Multiset.toFinsupp (is : Multiset ι)) = is.length := by
  change (Multiset.toFinsupp (is : Multiset ι)).sum (fun _ ↦ id) =
    Multiset.card (is : Multiset ι)
  exact Multiset.toFinsupp_sum_eq (is : Multiset ι)

private theorem exponentDegree_single_add (i : ι) (e : ι →₀ ℕ) :
    exponentDegree ι (Finsupp.single i 1 + e) = exponentDegree ι e + 1 := by
  change Finsupp.degree (Finsupp.single i 1 + e) = Finsupp.degree e + 1
  rw [map_add, Finsupp.degree_single]
  omega

/-!
The remainder of the proof is deliberately phrased as one finite-stage invariant.  Keeping the
three mutually dependent assertions together prevents Lean from forcing an artificial chain of
public helper lemmas.
-/

private structure StageInvariant (p : ℕ) : Prop where
  stable : ∀ (q : ℕ), q ≤ p → 1 ≤ p → q < p →
    ∀ (x : L) (f : MvPolynomial ι ℤ), DegreeLE ι q f →
      cartanStage ℤ L ι b p x f = cartanStage ℤ L ι b (p - 1) x f
  bounded : ∀ (q : ℕ), q ≤ p →
    ∀ (x : L) (f : MvPolynomial ι ℤ), DegreeLE ι q f →
      DegreeLE ι (q + 1) (cartanStage ℤ L ι b p x f)
  leading : ∀ (q : ℕ), q ≤ p →
    ∀ (x : L) (e : ι →₀ ℕ), exponentDegree ι e = q →
      DegreeLE ι q
        (cartanStage ℤ L ι b p x (MvPolynomial.monomial e 1) -
          basisPolynomial ℤ L ι b x * MvPolynomial.monomial e 1)
  compatible : ∀ (q : ℕ), q + 1 ≤ p →
    ∀ (x y : L) (f : MvPolynomial ι ℤ), DegreeLE ι q f →
      cartanStage ℤ L ι b p ⁅x, y⁆ f =
        cartanStage ℤ L ι b p x (cartanStage ℤ L ι b p y f) -
          cartanStage ℤ L ι b p y (cartanStage ℤ L ι b p x f)

/- The simultaneous Cartan--Eilenberg induction is filled below. -/
private theorem stageInvariant (p : ℕ) : StageInvariant L ι b p := by
  induction p with
  | zero =>
      refine
        { stable := ?_
          bounded := ?_
          leading := ?_
          compatible := ?_ }
      · intro q hq hp hlt
        omega
      · intro q hq x f hf
        have hq0 : q = 0 := by omega
        subst q
        apply degreeLE_map_of_monomial ι
          (cartanStage ℤ L ι b 0 x) 0 1
        · intro e he
          have he0 : exponentDegree ι e = 0 := Nat.eq_zero_of_le_zero he
          have hzero : e = 0 := by
            change Finsupp.degree e = 0 at he0
            exact (Finsupp.degree_eq_zero_iff e).mp he0
          subst e
          rw [show MvPolynomial.monomial (0 : ι →₀ ℕ) (1 : ℤ) = 1 by simp]
          have hstage := cartanStage_apply_one ℤ L ι b 0 x
          rw [degreeLE_iff_totalDegree_le]
          calc
            (((cartanStage ℤ L ι b 0) x) 1).totalDegree =
                (basisPolynomial ℤ L ι b x).totalDegree :=
              congrArg MvPolynomial.totalDegree hstage
            _ ≤ 1 := (degreeLE_iff_totalDegree_le ι 1 _).mp
              (basisPolynomial_degreeLE L ι b x)
        · exact hf
      · intro q hq x e he
        have hq0 : q = 0 := by omega
        have he0 : exponentDegree ι e = 0 := he.trans hq0
        subst q
        have hzero : e = 0 := by
          change Finsupp.degree e = 0 at he0
          exact (Finsupp.degree_eq_zero_iff e).mp he0
        subst e
        rw [show MvPolynomial.monomial (0 : ι →₀ ℕ) (1 : ℤ) = 1 by simp,
          cartanStage_apply_one, mul_one, sub_self]
        exact degreeLE_zero ι 0
      · intro q hq
        omega
  | succ p ih =>
      have hstableBasis : ∀ (i : ι) (e : ι →₀ ℕ),
          exponentDegree ι e ≤ p →
          cartanStage ℤ L ι b (p + 1) (b i) (MvPolynomial.monomial e 1) =
            cartanStage ℤ L ι b p (b i) (MvPolynomial.monomial e 1) := by
        intro i e he
        by_cases he0 : exponentDegree ι e = 0
        · have hzero : e = 0 := by
            change Finsupp.degree e = 0 at he0
            exact (Finsupp.degree_eq_zero_iff e).mp he0
          subst e
          simp only [show MvPolynomial.monomial (0 : ι →₀ ℕ) (1 : ℤ) = 1 by simp]
          rw [cartanStage_apply_one, cartanStage_apply_one]
        · have hp0 : p ≠ 0 := by omega
          let is := (Finsupp.toMultiset e).sort (· ≤ ·)
          have his : is.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
          have his_ne : is ≠ [] := by
            intro hz
            have hzcard : Multiset.card (Finsupp.toMultiset e) = 0 := by
              simpa [is] using congrArg List.length hz
            exact he0 (by simpa [exponentDegree] using hzcard)
          obtain ⟨j, js, hcons⟩ := List.exists_cons_of_ne_nil his_ne
          subst is
          let tail : ι →₀ ℕ := Multiset.toFinsupp (js : Multiset ι)
          have hmulti : (j :: js : List ι) = (Finsupp.toMultiset e).sort (· ≤ ·) :=
            hcons.symm
          have he_split : e = Finsupp.single j 1 + tail := by
            calc
              e = Multiset.toFinsupp (Finsupp.toMultiset e) := by simp
              _ = Multiset.toFinsupp ((j :: js : List ι) : Multiset ι) := by
                congr 1
                rw [hmulti, Multiset.sort_eq]
              _ = Finsupp.single j 1 + tail := by
                simp [tail, toFinsupp_cons]
          have htail_le : exponentDegree ι tail + 1 ≤ p := by
            rw [he_split, exponentDegree_single_add] at he
            exact he
          have htail_lt : exponentDegree ι tail < p := by omega
          have htail_bound : DegreeLE ι (exponentDegree ι tail)
              (MvPolynomial.monomial tail 1) := degreeLE_monomial ι tail 1
          have hinner (x : L) :
              cartanStage ℤ L ι b p x (MvPolynomial.monomial tail 1) =
                cartanStage ℤ L ι b (p - 1) x (MvPolynomial.monomial tail 1) :=
            ih.stable (exponentDegree ι tail) (by omega) (by omega) htail_lt
              x _ htail_bound
          have hrem : DegreeLE ι (exponentDegree ι tail)
              (cartanStage ℤ L ι b p (b i) (MvPolynomial.monomial tail 1) -
                MvPolynomial.monomial (Finsupp.single i 1 + tail) 1) := by
            simpa [basisPolynomial_basis, MvPolynomial.X,
              MvPolynomial.monomial_mul] using
              ih.leading (exponentDegree ι tail) (by omega) (b i) tail rfl
          have hrem' : DegreeLE ι (exponentDegree ι tail)
              (cartanStage ℤ L ι b (p - 1) (b i) (MvPolynomial.monomial tail 1) -
                MvPolynomial.monomial (Finsupp.single i 1 + tail) 1) := by
            simpa [hinner (b i)] using hrem
          have houter :
              cartanStage ℤ L ι b p (b j)
                  (cartanStage ℤ L ι b (p - 1) (b i)
                      (MvPolynomial.monomial tail 1) -
                    MvPolynomial.monomial (Finsupp.single i 1 + tail) 1) =
                cartanStage ℤ L ι b (p - 1) (b j)
                  (cartanStage ℤ L ι b (p - 1) (b i)
                      (MvPolynomial.monomial tail 1) -
                    MvPolynomial.monomial (Finsupp.single i 1 + tail) 1) :=
            ih.stable (exponentDegree ι tail) (by omega) (by omega) htail_lt
              (b j) _ hrem'
          have hbracket := hinner ⁅b i, b j⁆
          have hpstage : cartanStage ℤ L ι b p =
              cartanStep ℤ L ι b (cartanStage ℤ L ι b (p - 1)) := by
            simpa [hp0] using cartanStage_eq_step ℤ L ι b p
          calc
            cartanStage ℤ L ι b (p + 1) (b i) (MvPolynomial.monomial e 1) =
                (1 : ℤ) • cartanMonomialStep ℤ L ι b
                  (cartanStage ℤ L ι b p) i e := by
              change cartanStep ℤ L ι b (cartanStage ℤ L ι b p) (b i)
                  (MvPolynomial.monomial e 1) = _
              exact cartanStep_basis_monomial ℤ L ι b
                (cartanStage ℤ L ι b p) i e 1
            _ = (1 : ℤ) • cartanMonomialStep ℤ L ι b
                (cartanStage ℤ L ι b (p - 1)) i e := by
              apply congrArg ((1 : ℤ) • ·)
              simp only [cartanMonomialStep, hcons]
              split
              · rfl
              · rw [hinner (b i), houter, hbracket]
            _ = cartanStage ℤ L ι b p (b i) (MvPolynomial.monomial e 1) := by
              rw [hpstage]
              exact (cartanStep_basis_monomial ℤ L ι b
                (cartanStage ℤ L ι b (p - 1)) i e 1).symm
      have hstable : ∀ (q : ℕ), q ≤ p →
          ∀ (x : L) (f : MvPolynomial ι ℤ), DegreeLE ι q f →
            cartanStage ℤ L ι b (p + 1) x f =
              cartanStage ℤ L ι b p x f := by
        intro q hq x f hf
        let A : L →ₗ[ℤ] MvPolynomial ι ℤ :=
          (LinearMap.applyₗ f).comp (cartanStage ℤ L ι b (p + 1))
        let B : L →ₗ[ℤ] MvPolynomial ι ℤ :=
          (LinearMap.applyₗ f).comp (cartanStage ℤ L ι b p)
        change A x = B x
        have hAB : A = B := by
          apply b.ext
          intro i
          exact linearMap_eq_on_degreeLE_of_monomial ι
            (cartanStage ℤ L ι b (p + 1) (b i))
            (cartanStage ℤ L ι b p (b i)) q
            (fun e he ↦ hstableBasis i e (he.trans hq)) f hf
        exact LinearMap.congr_fun hAB x
      have hleadingBasis : ∀ (i : ι) (e : ι →₀ ℕ),
          exponentDegree ι e ≤ p + 1 →
          DegreeLE ι (exponentDegree ι e)
            (cartanStage ℤ L ι b (p + 1) (b i) (MvPolynomial.monomial e 1) -
              MvPolynomial.X i * MvPolynomial.monomial e 1) := by
        intro i e he
        by_cases he0 : exponentDegree ι e = 0
        · have hzero : e = 0 := by
            change Finsupp.degree e = 0 at he0
            exact (Finsupp.degree_eq_zero_iff e).mp he0
          subst e
          simp only [show MvPolynomial.monomial (0 : ι →₀ ℕ) (1 : ℤ) = 1 by simp,
            mul_one]
          have hstage := cartanStage_apply_one ℤ L ι b (p + 1) (b i)
          have hbasis := basisPolynomial_basis ℤ L ι b i
          rw [degreeLE_iff_totalDegree_le]
          calc
            (((cartanStage ℤ L ι b (p + 1)) (b i)) 1 - MvPolynomial.X i).totalDegree =
                (0 : MvPolynomial ι ℤ).totalDegree := by
              congr 1
              rw [hstage, hbasis, sub_self]
            _ ≤ 0 := by simp
        · let is := (Finsupp.toMultiset e).sort (· ≤ ·)
          have his_ne : is ≠ [] := by
            intro hz
            have hzcard : Multiset.card (Finsupp.toMultiset e) = 0 := by
              simpa [is] using congrArg List.length hz
            exact he0 (by simpa [exponentDegree] using hzcard)
          obtain ⟨j, js, hcons⟩ := List.exists_cons_of_ne_nil his_ne
          subst is
          let tail : ι →₀ ℕ := Multiset.toFinsupp (js : Multiset ι)
          have hmulti : (j :: js : List ι) = (Finsupp.toMultiset e).sort (· ≤ ·) :=
            hcons.symm
          have he_split : e = Finsupp.single j 1 + tail := by
            calc
              e = Multiset.toFinsupp (Finsupp.toMultiset e) := by simp
              _ = Multiset.toFinsupp ((j :: js : List ι) : Multiset ι) := by
                congr 1
                rw [hmulti, Multiset.sort_eq]
              _ = Finsupp.single j 1 + tail := by
                simp [tail, toFinsupp_cons]
          have htail_le : exponentDegree ι tail ≤ p := by
            rw [he_split, exponentDegree_single_add] at he
            omega
          have htail_bound : DegreeLE ι (exponentDegree ι tail)
              (MvPolynomial.monomial tail 1) := degreeLE_monomial ι tail 1
          have hrem : DegreeLE ι (exponentDegree ι tail)
              (cartanStage ℤ L ι b p (b i) (MvPolynomial.monomial tail 1) -
                MvPolynomial.monomial (Finsupp.single i 1 + tail) 1) := by
            simpa [basisPolynomial_basis, MvPolynomial.X,
              MvPolynomial.monomial_mul] using
              ih.leading (exponentDegree ι tail) htail_le (b i) tail rfl
          have houter : DegreeLE ι (exponentDegree ι tail + 1)
              (cartanStage ℤ L ι b p (b j)
                (cartanStage ℤ L ι b p (b i) (MvPolynomial.monomial tail 1) -
                  MvPolynomial.monomial (Finsupp.single i 1 + tail) 1)) :=
            ih.bounded (exponentDegree ι tail) htail_le (b j) _ hrem
          have hbracket : DegreeLE ι (exponentDegree ι tail + 1)
              (cartanStage ℤ L ι b p ⁅b i, b j⁆
                (MvPolynomial.monomial tail 1)) :=
            ih.bounded (exponentDegree ι tail) htail_le ⁅b i, b j⁆ _ htail_bound
          have hdegree : exponentDegree ι e = exponentDegree ι tail + 1 := by
            rw [he_split, exponentDegree_single_add]
          have hlead :
              MvPolynomial.monomial (Finsupp.single i 1 + e) (1 : ℤ) =
                MvPolynomial.X i * MvPolynomial.monomial e 1 := by
            simp [MvPolynomial.X, MvPolynomial.monomial_mul]
          have hstep :
              cartanStage ℤ L ι b (p + 1) (b i) (MvPolynomial.monomial e 1) =
                cartanMonomialStep ℤ L ι b (cartanStage ℤ L ι b p) i e := by
            calc
              _ = (1 : ℤ) • cartanMonomialStep ℤ L ι b
                    (cartanStage ℤ L ι b p) i e := by
                change cartanStep ℤ L ι b (cartanStage ℤ L ι b p) (b i)
                    (MvPolynomial.monomial e 1) = _
                exact cartanStep_basis_monomial ℤ L ι b
                  (cartanStage ℤ L ι b p) i e 1
              _ = _ := by module
          rw [hdegree, hstep]
          simp only [cartanMonomialStep, hcons]
          split
          · rw [hlead, sub_self]
            exact degreeLE_zero ι (exponentDegree ι tail + 1)
          · rw [hlead]
            have halg :
                MvPolynomial.X i * MvPolynomial.monomial e 1 +
                      cartanStage ℤ L ι b p (b j)
                        (cartanStage ℤ L ι b p (b i)
                            (MvPolynomial.monomial tail 1) -
                          MvPolynomial.monomial (Finsupp.single i 1 + tail) 1) +
                      cartanStage ℤ L ι b p ⁅b i, b j⁆
                        (MvPolynomial.monomial tail 1) -
                    MvPolynomial.X i * MvPolynomial.monomial e 1 =
                  cartanStage ℤ L ι b p (b j)
                        (cartanStage ℤ L ι b p (b i)
                            (MvPolynomial.monomial tail 1) -
                          MvPolynomial.monomial (Finsupp.single i 1 + tail) 1) +
                    cartanStage ℤ L ι b p ⁅b i, b j⁆
                      (MvPolynomial.monomial tail 1) := by abel
            rw [halg]
            exact degreeLE_add ι houter hbracket
      have hleading : ∀ (q : ℕ), q ≤ p + 1 →
          ∀ (x : L) (e : ι →₀ ℕ), exponentDegree ι e = q →
            DegreeLE ι q
              (cartanStage ℤ L ι b (p + 1) x (MvPolynomial.monomial e 1) -
                basisPolynomial ℤ L ι b x * MvPolynomial.monomial e 1) := by
        intro q hq x e he
        let A : L →ₗ[ℤ] MvPolynomial ι ℤ :=
          { toFun := fun y ↦
              cartanStage ℤ L ι b (p + 1) y (MvPolynomial.monomial e 1) -
                basisPolynomial ℤ L ι b y * MvPolynomial.monomial e 1
            map_add' := by intro y z; simp [add_mul]; abel
            map_smul' := by intro r y; simp; ring }
        change DegreeLE ι q (A x)
        apply degreeLE_linearMap_of_basis L ι b A q
        intro i
        change DegreeLE ι q
          (cartanStage ℤ L ι b (p + 1) (b i) (MvPolynomial.monomial e 1) -
            basisPolynomial ℤ L ι b (b i) * MvPolynomial.monomial e 1)
        rw [basisPolynomial_basis]
        rw [← he]
        exact hleadingBasis i e (he.trans_le hq)
      have hbounded : ∀ (q : ℕ), q ≤ p + 1 →
          ∀ (x : L) (f : MvPolynomial ι ℤ), DegreeLE ι q f →
            DegreeLE ι (q + 1) (cartanStage ℤ L ι b (p + 1) x f) := by
        intro q hq x f hf
        apply degreeLE_map_of_monomial ι
          (cartanStage ℤ L ι b (p + 1) x) q (q + 1)
        · intro e he
          have hrem := hleading (exponentDegree ι e) (he.trans hq) x e rfl
          have hlead : DegreeLE ι (exponentDegree ι e + 1)
              (basisPolynomial ℤ L ι b x * MvPolynomial.monomial e 1) := by
            simpa [Nat.add_comm] using degreeLE_mul ι
              (basisPolynomial_degreeLE L ι b x) (degreeLE_monomial ι e 1)
          have hsum : DegreeLE ι (exponentDegree ι e + 1)
              ((cartanStage ℤ L ι b (p + 1) x (MvPolynomial.monomial e 1) -
                  basisPolynomial ℤ L ι b x * MvPolynomial.monomial e 1) +
                basisPolynomial ℤ L ι b x * MvPolynomial.monomial e 1) :=
            degreeLE_add ι (degreeLE_mono ι (by omega) hrem) hlead
          have heq :
              (cartanStage ℤ L ι b (p + 1) x (MvPolynomial.monomial e 1) -
                    basisPolynomial ℤ L ι b x * MvPolynomial.monomial e 1) +
                  basisPolynomial ℤ L ι b x * MvPolynomial.monomial e 1 =
                cartanStage ℤ L ι b (p + 1) x (MvPolynomial.monomial e 1) := by abel
          rw [heq] at hsum
          exact degreeLE_mono ι (by omega) hsum
        · exact hf
      have hcompatibleLower : ∀ (q : ℕ), q + 1 ≤ p →
          ∀ (x y : L) (f : MvPolynomial ι ℤ), DegreeLE ι q f →
            cartanStage ℤ L ι b (p + 1) ⁅x, y⁆ f =
              cartanStage ℤ L ι b (p + 1) x
                  (cartanStage ℤ L ι b (p + 1) y f) -
                cartanStage ℤ L ι b (p + 1) y
                  (cartanStage ℤ L ι b (p + 1) x f) := by
        intro q hq x y f hf
        have hxy := hstable q (by omega) ⁅x, y⁆ f hf
        have hx := hstable q (by omega) x f hf
        have hy := hstable q (by omega) y f hf
        have hbx := ih.bounded q (by omega) x f hf
        have hby := ih.bounded q (by omega) y f hf
        have hox := hstable (q + 1) hq x
          (cartanStage ℤ L ι b p y f) hby
        have hoy := hstable (q + 1) hq y
          (cartanStage ℤ L ι b p x f) hbx
        rw [hxy, hx, hy, hox, hoy]
        exact ih.compatible q hq x y f hf
      have hordered : ∀ (stage : ℕ) (i : ι) (e : ι →₀ ℕ),
          (∀ j ∈ e.support, i ≤ j) →
          cartanStage ℤ L ι b stage (b i) (MvPolynomial.monomial e 1) =
            MvPolynomial.monomial (Finsupp.single i 1 + e) 1 := by
        intro stage i e hi
        let is := (Finsupp.toMultiset e).sort (· ≤ ·)
        have his : is.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
        have hto : Multiset.toFinsupp (is : Multiset ι) = e := by
          calc
            Multiset.toFinsupp (is : Multiset ι) =
                Multiset.toFinsupp (Finsupp.toMultiset e) := by
              congr 1
              simp [is]
            _ = e := by simp
        have hilist : ∀ j ∈ is, i ≤ j := by
          intro j hj
          apply hi j
          rw [← Finsupp.mem_toMultiset]
          simpa [is] using hj
        have hval := cartanStage_basis_orderedList ℤ L ι b stage i is his hilist
        simpa [hto, toFinsupp_cons] using hval
      have hrec : ∀ (a gamma : ι) (ls : List ι),
          (gamma :: ls).Pairwise (· ≤ ·) → gamma < a →
          ls.length ≤ p →
          cartanStage ℤ L ι b (p + 1) (b a)
              (MvPolynomial.monomial
                (Multiset.toFinsupp ((gamma :: ls : List ι) : Multiset ι)) 1) =
            cartanStage ℤ L ι b (p + 1) (b gamma)
                (cartanStage ℤ L ι b (p + 1) (b a)
                  (MvPolynomial.monomial
                    (Multiset.toFinsupp (ls : Multiset ι)) 1)) +
              cartanStage ℤ L ι b (p + 1) ⁅b a, b gamma⁆
                (MvPolynomial.monomial
                  (Multiset.toFinsupp (ls : Multiset ι)) 1) := by
        intro a gamma ls hpair hga hlen
        let tail : ι →₀ ℕ := Multiset.toFinsupp (ls : Multiset ι)
        let full : ι →₀ ℕ :=
          Multiset.toFinsupp ((gamma :: ls : List ι) : Multiset ι)
        have htailDegree : exponentDegree ι tail = ls.length :=
          exponentDegree_toFinsupp ι ls
        have htail_le : exponentDegree ι tail ≤ p := by
          rw [htailDegree]
          exact hlen
        have htailBound : DegreeLE ι (exponentDegree ι tail)
            (MvPolynomial.monomial tail 1) := degreeLE_monomial ι tail 1
        have htailStable (x : L) :
            cartanStage ℤ L ι b (p + 1) x (MvPolynomial.monomial tail 1) =
              cartanStage ℤ L ι b p x (MvPolynomial.monomial tail 1) :=
          hstable (exponentDegree ι tail) htail_le x _ htailBound
        let leadA : MvPolynomial ι ℤ :=
          MvPolynomial.monomial (Finsupp.single a 1 + tail) 1
        let rem : MvPolynomial ι ℤ :=
          cartanStage ℤ L ι b p (b a) (MvPolynomial.monomial tail 1) - leadA
        have hrem : DegreeLE ι (exponentDegree ι tail) rem := by
          dsimp only [rem, leadA]
          simpa [basisPolynomial_basis, MvPolynomial.X,
            MvPolynomial.monomial_mul] using
            ih.leading (exponentDegree ι tail) htail_le
              (b a) tail rfl
        have hremStable :
            cartanStage ℤ L ι b (p + 1) (b gamma) rem =
              cartanStage ℤ L ι b p (b gamma) rem :=
          hstable (exponentDegree ι tail) htail_le
            (b gamma) rem hrem
        have hbracketStable := htailStable ⁅b a, b gamma⁆
        have hgammaTail : ∀ j ∈ tail.support, gamma ≤ j := by
          intro j hj
          have hjm : j ∈ (ls : Multiset ι) := by
            rw [← Finsupp.mem_toMultiset] at hj
            simpa [tail] using hj
          exact (List.pairwise_cons.mp hpair).1 j (by simpa using hjm)
        have hgammaLeadSupport :
            ∀ j ∈ (Finsupp.single a 1 + tail).support, gamma ≤ j := by
          intro j hj
          have hj' := Finsupp.support_add hj
          simp only [Finsupp.support_single_ne_zero _ one_ne_zero,
            Finset.mem_union, Finset.mem_singleton] at hj'
          rcases hj' with rfl | hjtail
          · exact hga.le
          · exact hgammaTail j hjtail
        have hleadOrdered :
            cartanStage ℤ L ι b (p + 1) (b gamma) leadA =
              MvPolynomial.monomial
                (Finsupp.single gamma 1 + (Finsupp.single a 1 + tail)) 1 := by
          exact hordered (p + 1) gamma (Finsupp.single a 1 + tail)
            hgammaLeadSupport
        have hsort : (Finsupp.toMultiset full).sort (· ≤ ·) = gamma :: ls := by
          dsimp only [full]
          simp only [Multiset.toFinsupp_toMultiset, Multiset.coe_sort]
          exact List.mergeSort_eq_self _ hpair
        have hnot : ¬a ≤ gamma := not_le_of_gt hga
        have hstep :
            cartanStage ℤ L ι b (p + 1) (b a) (MvPolynomial.monomial full 1) =
              cartanMonomialStep ℤ L ι b (cartanStage ℤ L ι b p) a full := by
          calc
            _ = (1 : ℤ) • cartanMonomialStep ℤ L ι b
                  (cartanStage ℤ L ι b p) a full := by
              change cartanStep ℤ L ι b (cartanStage ℤ L ι b p) (b a)
                  (MvPolynomial.monomial full 1) = _
              exact cartanStep_basis_monomial ℤ L ι b
                (cartanStage ℤ L ι b p) a full 1
            _ = _ := by module
        have hfullSplit : full = Finsupp.single gamma 1 + tail := by
          simp [full, tail, toFinsupp_cons]
        have hformula :
            cartanStage ℤ L ι b (p + 1) (b a) (MvPolynomial.monomial full 1) =
              MvPolynomial.monomial (Finsupp.single a 1 + full) 1 +
                cartanStage ℤ L ι b p (b gamma) rem +
                cartanStage ℤ L ι b p ⁅b a, b gamma⁆
                  (MvPolynomial.monomial tail 1) := by
          rw [hstep]
          simp only [cartanMonomialStep, hsort, hnot, if_false]
          rfl
        have hsplit :
            cartanStage ℤ L ι b p (b a) (MvPolynomial.monomial tail 1) =
              leadA + rem := by
          dsimp only [rem]
          abel
        have hleadExp :
            Finsupp.single a 1 + full =
              Finsupp.single gamma 1 + (Finsupp.single a 1 + tail) := by
          rw [hfullSplit]
          abel
        change cartanStage ℤ L ι b (p + 1) (b a)
              (MvPolynomial.monomial full 1) = _
        rw [hformula, htailStable (b a), hsplit, map_add,
          hleadOrdered, hremStable, hbracketStable, hleadExp]
      have hstageX : ∀ (stage : ℕ), 1 ≤ stage → ∀ i j : ι,
          cartanStage ℤ L ι b stage (b i) (MvPolynomial.X j) =
            MvPolynomial.X i * MvPolynomial.X j +
              if i ≤ j then 0 else basisPolynomial ℤ L ι b ⁅b i, b j⁆ := by
        intro stage hstage i j
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : stage ≠ 0)
        rw [MvPolynomial.X]
        change cartanStep ℤ L ι b (cartanStage ℤ L ι b k) (b i)
            (MvPolynomial.monomial (Finsupp.single j 1) 1) = _
        rw [cartanStep_basis_monomial]
        have hone (x : L) :
            cartanStage ℤ L ι b k x (1 : MvPolynomial ι ℤ) =
              basisPolynomial ℤ L ι b x :=
          cartanStage_apply_one ℤ L ι b k x
        by_cases hij : i ≤ j
        · simp [cartanMonomialStep, hij, MvPolynomial.X,
            MvPolynomial.monomial_mul]
          module
        · simp [cartanMonomialStep, hij, MvPolynomial.X,
            MvPolynomial.monomial_mul]
          rw [hone (b i), basisPolynomial_basis, hone ⁅b i, b j⁆]
          simp [MvPolynomial.X]
          module
      have hcompatBasis : ∀ (i j : ι) (e : ι →₀ ℕ),
          exponentDegree ι e ≤ p →
          cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆
              (MvPolynomial.monomial e 1) =
            cartanStage ℤ L ι b (p + 1) (b i)
                (cartanStage ℤ L ι b (p + 1) (b j)
                  (MvPolynomial.monomial e 1)) -
              cartanStage ℤ L ι b (p + 1) (b j)
                (cartanStage ℤ L ι b (p + 1) (b i)
                  (MvPolynomial.monomial e 1)) := by
        intro i j e he
        by_cases he0 : exponentDegree ι e = 0
        · have hzero : e = 0 := by
            change Finsupp.degree e = 0 at he0
            exact (Finsupp.degree_eq_zero_iff e).mp he0
          subst e
          simp only [show MvPolynomial.monomial (0 : ι →₀ ℕ) (1 : ℤ) = 1 by simp]
          rw [cartanStage_apply_one, cartanStage_apply_one, cartanStage_apply_one,
            basisPolynomial_basis, basisPolynomial_basis,
            hstageX (p + 1) (by omega) i j,
            hstageX (p + 1) (by omega) j i]
          by_cases hij : i ≤ j
          · by_cases hji : j ≤ i
            · have hijEq : i = j := le_antisymm hij hji
              subst j
              simp
            · simp [hij, hji, mul_comm, ← map_neg, lie_skew]
          · have hji : j ≤ i := le_of_not_ge hij
            simp [hij, hji, mul_comm]
        · let is := (Finsupp.toMultiset e).sort (· ≤ ·)
          have his : is.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
          have his_ne : is ≠ [] := by
            intro hz
            have hzcard : Multiset.card (Finsupp.toMultiset e) = 0 := by
              simpa [is] using congrArg List.length hz
            exact he0 (by simpa [exponentDegree] using hzcard)
          obtain ⟨gamma, ls, hcons⟩ := List.exists_cons_of_ne_nil his_ne
          subst is
          have hpair : (gamma :: ls).Pairwise (· ≤ ·) := by
            rw [← hcons]
            exact his
          have hgammaAll : ∀ k ∈ gamma :: ls, gamma ≤ k := by
            intro k hk
            simp only [List.mem_cons] at hk
            rcases hk with rfl | hk
            · rfl
            · exact (List.pairwise_cons.mp hpair).1 k hk
          have heq : e =
              Multiset.toFinsupp ((gamma :: ls : List ι) : Multiset ι) := by
            calc
              e = Multiset.toFinsupp (Finsupp.toMultiset e) := by simp
              _ = Multiset.toFinsupp ((gamma :: ls : List ι) : Multiset ι) := by
                congr 1
                rw [← hcons, Multiset.sort_eq]
          have hlen : (gamma :: ls).length ≤ p := by
            rw [← exponentDegree_toFinsupp ι (gamma :: ls), ← heq]
            exact he
          rw [heq]
          by_cases hig : i ≤ gamma
          · by_cases hij : i = j
            · subst j
              simp
            · by_cases hijlt : i < j
              · have hpairI : (i :: gamma :: ls).Pairwise (· ≤ ·) := by
                  apply List.pairwise_cons.mpr
                  exact ⟨fun k hk ↦ hig.trans (hgammaAll k hk), hpair⟩
                have hiord := cartanStage_basis_orderedList ℤ L ι b (p + 1)
                  i (gamma :: ls) hpair
                  (fun k hk ↦ hig.trans (hgammaAll k hk))
                have hr := hrec j i (gamma :: ls) hpairI hijlt hlen
                rw [hiord, hr]
                rw [show ⁅b j, b i⁆ = -⁅b i, b j⁆ by
                  exact (lie_skew (b j) (b i)).symm]
                simp only [map_neg]
                simp
              · have hjilt : j < i := lt_of_le_of_ne (le_of_not_gt hijlt) (Ne.symm hij)
                have hjg : j ≤ gamma := hjilt.le.trans hig
                have hpairJ : (j :: gamma :: ls).Pairwise (· ≤ ·) := by
                  apply List.pairwise_cons.mpr
                  exact ⟨fun k hk ↦ hjg.trans (hgammaAll k hk), hpair⟩
                have hjord := cartanStage_basis_orderedList ℤ L ι b (p + 1)
                  j (gamma :: ls) hpair
                  (fun k hk ↦ hjg.trans (hgammaAll k hk))
                have hr := hrec i j (gamma :: ls) hpairJ hjilt hlen
                rw [hjord, hr]
                abel
          · by_cases hjg : j ≤ gamma
            · have hjilt : j < i := lt_of_not_ge
                (fun hijle ↦ hig (hijle.trans hjg))
              have hpairJ : (j :: gamma :: ls).Pairwise (· ≤ ·) := by
                apply List.pairwise_cons.mpr
                exact ⟨fun k hk ↦ hjg.trans (hgammaAll k hk), hpair⟩
              have hjord := cartanStage_basis_orderedList ℤ L ι b (p + 1)
                j (gamma :: ls) hpair
                (fun k hk ↦ hjg.trans (hgammaAll k hk))
              have hr := hrec i j (gamma :: ls) hpairJ hjilt hlen
              rw [hjord, hr]
              abel
            · have hgi : gamma < i := lt_of_not_ge hig
              have hgj : gamma < j := lt_of_not_ge hjg
              let tail : ι →₀ ℕ := Multiset.toFinsupp (ls : Multiset ι)
              let mL : MvPolynomial ι ℤ := MvPolynomial.monomial tail 1
              let mJ : MvPolynomial ι ℤ :=
                MvPolynomial.monomial
                  (Multiset.toFinsupp ((gamma :: ls : List ι) : Multiset ι)) 1
              have htailDegree : exponentDegree ι tail = ls.length :=
                exponentDegree_toFinsupp ι ls
              have hlow : exponentDegree ι tail + 1 ≤ p := by
                rw [htailDegree]
                simpa using hlen
              have htailBound : DegreeLE ι (exponentDegree ι tail) mL := by
                exact degreeLE_monomial ι tail 1
              have hgammaTail : ∀ k ∈ tail.support, gamma ≤ k := by
                intro k hk
                have hkm : k ∈ (ls : Multiset ι) := by
                  rw [← Finsupp.mem_toMultiset] at hk
                  simpa [tail] using hk
                exact (List.pairwise_cons.mp hpair).1 k (by simpa using hkm)
              have hcommGamma : ∀ (a beta : ι), gamma < a → gamma < beta →
                  cartanStage ℤ L ι b (p + 1) (b a)
                      (cartanStage ℤ L ι b (p + 1) (b gamma)
                        (cartanStage ℤ L ι b (p + 1) (b beta) mL)) =
                    cartanStage ℤ L ι b (p + 1) (b gamma)
                        (cartanStage ℤ L ι b (p + 1) (b a)
                          (cartanStage ℤ L ι b (p + 1) (b beta) mL)) +
                      cartanStage ℤ L ι b (p + 1) ⁅b a, b gamma⁆
                        (cartanStage ℤ L ι b (p + 1) (b beta) mL) := by
                intro a beta hga hgb
                let lead : MvPolynomial ι ℤ :=
                  MvPolynomial.monomial (Finsupp.single beta 1 + tail) 1
                let w : MvPolynomial ι ℤ :=
                  cartanStage ℤ L ι b (p + 1) (b beta) mL - lead
                have hw : DegreeLE ι (exponentDegree ι tail) w := by
                  dsimp only [w, lead, mL]
                  simpa [basisPolynomial_basis, MvPolynomial.X,
                    MvPolynomial.monomial_mul] using
                    hleading (exponentDegree ι tail) (by omega) (b beta) tail rfl
                have hcw0 := hcompatibleLower (exponentDegree ι tail) hlow
                  (b a) (b gamma) w hw
                have hcw :
                    cartanStage ℤ L ι b (p + 1) (b a)
                        (cartanStage ℤ L ι b (p + 1) (b gamma) w) =
                      cartanStage ℤ L ι b (p + 1) (b gamma)
                          (cartanStage ℤ L ι b (p + 1) (b a) w) +
                        cartanStage ℤ L ι b (p + 1) ⁅b a, b gamma⁆ w := by
                  rw [hcw0]
                  abel
                have hleadSupport :
                    ∀ k ∈ (Finsupp.single beta 1 + tail).support, gamma ≤ k := by
                  intro k hk
                  have hk' := Finsupp.support_add hk
                  simp only [Finsupp.support_single_ne_zero _ one_ne_zero,
                    Finset.mem_union, Finset.mem_singleton] at hk'
                  rcases hk' with rfl | hkt
                  · exact hgb.le
                  · exact hgammaTail k hkt
                have hgammaLead :
                    cartanStage ℤ L ι b (p + 1) (b gamma) lead =
                      MvPolynomial.monomial
                        (Finsupp.single gamma 1 +
                          (Finsupp.single beta 1 + tail)) 1 := by
                  exact hordered (p + 1) gamma
                    (Finsupp.single beta 1 + tail) hleadSupport
                let rest :=
                  (Finsupp.toMultiset (Finsupp.single beta 1 + tail)).sort (· ≤ ·)
                have hrestPair : rest.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
                have hrestTo : Multiset.toFinsupp (rest : Multiset ι) =
                    Finsupp.single beta 1 + tail := by
                  calc
                    Multiset.toFinsupp (rest : Multiset ι) =
                        Multiset.toFinsupp
                          (Finsupp.toMultiset (Finsupp.single beta 1 + tail)) := by
                      congr 1
                      simp [rest]
                    _ = _ := Finsupp.toMultiset_toFinsupp _
                have hgammaRest : ∀ k ∈ rest, gamma ≤ k := by
                  intro k hk
                  apply hleadSupport k
                  rw [← Finsupp.mem_toMultiset]
                  simpa [rest] using hk
                have hpairRest : (gamma :: rest).Pairwise (· ≤ ·) :=
                  List.pairwise_cons.mpr ⟨hgammaRest, hrestPair⟩
                have hrestLength : rest.length ≤ p := by
                  have hcard : rest.length = exponentDegree ι
                      (Finsupp.single beta 1 + tail) := by
                    calc
                      rest.length = Multiset.card
                          (Finsupp.toMultiset (Finsupp.single beta 1 + tail)) := by
                        simp [rest]
                      _ = exponentDegree ι (Finsupp.single beta 1 + tail) := by
                        change Multiset.card
                            (Finsupp.toMultiset (Finsupp.single beta 1 + tail)) =
                          (Finsupp.single beta 1 + tail).sum (fun _ ↦ id)
                        exact Finsupp.card_toMultiset (Finsupp.single beta 1 + tail)
                  calc
                    rest.length = exponentDegree ι
                        (Finsupp.single beta 1 + tail) := hcard
                    _ = exponentDegree ι tail + 1 :=
                      exponentDegree_single_add ι beta tail
                    _ ≤ p := hlow
                have hrecLead0 := hrec a gamma rest hpairRest hga hrestLength
                have hrecLead :
                    cartanStage ℤ L ι b (p + 1) (b a)
                        (cartanStage ℤ L ι b (p + 1) (b gamma) lead) =
                      cartanStage ℤ L ι b (p + 1) (b gamma)
                          (cartanStage ℤ L ι b (p + 1) (b a) lead) +
                        cartanStage ℤ L ι b (p + 1) ⁅b a, b gamma⁆ lead := by
                  rw [hgammaLead]
                  simpa [lead, hrestTo, toFinsupp_cons, add_assoc] using hrecLead0
                have hsplit :
                    cartanStage ℤ L ι b (p + 1) (b beta) mL = lead + w := by
                  dsimp only [w]
                  abel
                rw [hsplit, map_add, map_add, map_add, map_add, hrecLead, hcw]
                simp only [map_add]
                abel
              have hformula5 : ∀ (a beta : ι), gamma < a → gamma < beta →
                  cartanStage ℤ L ι b (p + 1) (b a)
                      (cartanStage ℤ L ι b (p + 1) (b beta) mJ) =
                    cartanStage ℤ L ι b (p + 1) (b gamma)
                        (cartanStage ℤ L ι b (p + 1) (b a)
                          (cartanStage ℤ L ι b (p + 1) (b beta) mL)) +
                      cartanStage ℤ L ι b (p + 1) ⁅b a, b gamma⁆
                          (cartanStage ℤ L ι b (p + 1) (b beta) mL) +
                        cartanStage ℤ L ι b (p + 1) ⁅b beta, b gamma⁆
                            (cartanStage ℤ L ι b (p + 1) (b a) mL) +
                          cartanStage ℤ L ι b (p + 1)
                            ⁅b a, ⁅b beta, b gamma⁆⁆ mL := by
                intro a beta hga hgb
                have hr := hrec beta gamma ls hpair hgb (by omega)
                have hc := hcommGamma a beta hga hgb
                have hcb0 := hcompatibleLower (exponentDegree ι tail) hlow
                  (b a) ⁅b beta, b gamma⁆ mL htailBound
                have hcb :
                    cartanStage ℤ L ι b (p + 1) (b a)
                        (cartanStage ℤ L ι b (p + 1) ⁅b beta, b gamma⁆ mL) =
                      cartanStage ℤ L ι b (p + 1) ⁅b beta, b gamma⁆
                          (cartanStage ℤ L ι b (p + 1) (b a) mL) +
                        cartanStage ℤ L ι b (p + 1)
                          ⁅b a, ⁅b beta, b gamma⁆⁆ mL := by
                  rw [hcb0]
                  abel
                change cartanStage ℤ L ι b (p + 1) (b a)
                    (cartanStage ℤ L ι b (p + 1) (b beta)
                      (MvPolynomial.monomial
                        (Multiset.toFinsupp ((gamma :: ls : List ι) : Multiset ι)) 1)) = _
                rw [hr, map_add, hc, hcb]
                abel
              have hi5 := hformula5 i j hgi hgj
              have hj5 := hformula5 j i hgj hgi
              have htailCompat := hcompatibleLower (exponentDegree ι tail) hlow
                (b i) (b j) mL htailBound
              have htailDiff :
                  cartanStage ℤ L ι b (p + 1) (b i)
                      (cartanStage ℤ L ι b (p + 1) (b j) mL) -
                    cartanStage ℤ L ι b (p + 1) (b j)
                      (cartanStage ℤ L ι b (p + 1) (b i) mL) =
                    cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆ mL :=
                htailCompat.symm
              have hgammaBracket0 := hcompatibleLower (exponentDegree ι tail) hlow
                (b gamma) ⁅b i, b j⁆ mL htailBound
              have hgammaBracket :
                  cartanStage ℤ L ι b (p + 1) (b gamma)
                      (cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆ mL) =
                    cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆
                        (cartanStage ℤ L ι b (p + 1) (b gamma) mL) +
                      cartanStage ℤ L ι b (p + 1) ⁅b gamma, ⁅b i, b j⁆⁆ mL := by
                rw [hgammaBracket0]
                abel
              have hgammaML :
                  cartanStage ℤ L ι b (p + 1) (b gamma) mL = mJ := by
                dsimp only [mL, mJ]
                have hg := hordered (p + 1) gamma tail hgammaTail
                simpa [tail, toFinsupp_cons] using hg
              have hjacobi :
                  ⁅b gamma, ⁅b i, b j⁆⁆ + ⁅b i, ⁅b j, b gamma⁆⁆ -
                    ⁅b j, ⁅b i, b gamma⁆⁆ = 0 := by
                have h := lie_jacobi (b gamma) (b i) (b j)
                have hskew : ⁅b gamma, b i⁆ = -⁅b i, b gamma⁆ :=
                  (lie_skew (b gamma) (b i)).symm
                have hthird : ⁅b j, ⁅b gamma, b i⁆⁆ =
                    -⁅b j, ⁅b i, b gamma⁆⁆ := by
                  calc
                    ⁅b j, ⁅b gamma, b i⁆⁆ = ⁅b j, -⁅b i, b gamma⁆⁆ := by
                      rw [hskew]
                    _ = -⁅b j, ⁅b i, b gamma⁆⁆ := by
                      rw [lie_neg]
                rw [hthird] at h
                rw [sub_eq_add_neg]
                exact h
              have hjacobiAction := congrArg
                (fun x : L ↦ cartanStage ℤ L ι b (p + 1) x mL) hjacobi
              simp only [map_add, map_sub, map_zero] at hjacobiAction
              change
                cartanStage ℤ L ι b (p + 1) ⁅b gamma, ⁅b i, b j⁆⁆ mL +
                    cartanStage ℤ L ι b (p + 1) ⁅b i, ⁅b j, b gamma⁆⁆ mL -
                    cartanStage ℤ L ι b (p + 1) ⁅b j, ⁅b i, b gamma⁆⁆ mL = 0
                at hjacobiAction
              have hdiffFormula :
                  cartanStage ℤ L ι b (p + 1) (b i)
                        (cartanStage ℤ L ι b (p + 1) (b j) mJ) -
                      cartanStage ℤ L ι b (p + 1) (b j)
                        (cartanStage ℤ L ι b (p + 1) (b i) mJ) =
                    cartanStage ℤ L ι b (p + 1) (b gamma)
                        (cartanStage ℤ L ι b (p + 1) (b i)
                            (cartanStage ℤ L ι b (p + 1) (b j) mL) -
                          cartanStage ℤ L ι b (p + 1) (b j)
                            (cartanStage ℤ L ι b (p + 1) (b i) mL)) +
                      cartanStage ℤ L ι b (p + 1) ⁅b i, ⁅b j, b gamma⁆⁆ mL -
                        cartanStage ℤ L ι b (p + 1) ⁅b j, ⁅b i, b gamma⁆⁆ mL := by
                rw [hi5, hj5, map_sub]
                abel
              change cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆ mJ = _
              rw [hdiffFormula, htailDiff, hgammaBracket, hgammaML]
              rw [show
                cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆ mJ +
                      cartanStage ℤ L ι b (p + 1) ⁅b gamma, ⁅b i, b j⁆⁆ mL +
                      cartanStage ℤ L ι b (p + 1) ⁅b i, ⁅b j, b gamma⁆⁆ mL -
                      cartanStage ℤ L ι b (p + 1) ⁅b j, ⁅b i, b gamma⁆⁆ mL =
                    cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆ mJ +
                      (cartanStage ℤ L ι b (p + 1) ⁅b gamma, ⁅b i, b j⁆⁆ mL +
                       cartanStage ℤ L ι b (p + 1) ⁅b i, ⁅b j, b gamma⁆⁆ mL -
                       cartanStage ℤ L ι b (p + 1) ⁅b j, ⁅b i, b gamma⁆⁆ mL) by
                  abel,
                hjacobiAction, add_zero]
      refine
        { stable := ?_
          bounded := ?_
          leading := ?_
          compatible := ?_ }
      · intro q hq hp hlt x f hf
        exact hstable q (by omega) x f hf
      · exact hbounded
      · exact hleading
      · intro q hq x y f hf
        have hqp : q ≤ p := by omega
        have hb (i j : ι) :
            cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆ f =
              cartanStage ℤ L ι b (p + 1) (b i)
                  (cartanStage ℤ L ι b (p + 1) (b j) f) -
                cartanStage ℤ L ι b (p + 1) (b j)
                  (cartanStage ℤ L ι b (p + 1) (b i) f) := by
          let A : Module.End ℤ (MvPolynomial ι ℤ) :=
            cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆
          let B : Module.End ℤ (MvPolynomial ι ℤ) :=
            cartanStage ℤ L ι b (p + 1) (b i) *
                cartanStage ℤ L ι b (p + 1) (b j) -
              cartanStage ℤ L ι b (p + 1) (b j) *
                cartanStage ℤ L ι b (p + 1) (b i)
          have hAB : A f = B f :=
            linearMap_eq_on_degreeLE_of_monomial ι A B q (by
              intro e he
              dsimp only [A, B]
              change
                cartanStage ℤ L ι b (p + 1) ⁅b i, b j⁆
                    (MvPolynomial.monomial e 1) =
                  cartanStage ℤ L ι b (p + 1) (b i)
                      (cartanStage ℤ L ι b (p + 1) (b j)
                        (MvPolynomial.monomial e 1)) -
                    cartanStage ℤ L ι b (p + 1) (b j)
                      (cartanStage ℤ L ι b (p + 1) (b i)
                        (MvPolynomial.monomial e 1))
              exact hcompatBasis i j e (he.trans hqp)) f hf
          simpa [A, B, LinearMap.sub_apply, Module.End.mul_apply] using hAB
        let left : L →ₗ[ℤ] L →ₗ[ℤ] MvPolynomial ι ℤ :=
          LinearMap.mk₂ ℤ
            (fun x y ↦ cartanStage ℤ L ι b (p + 1) ⁅x, y⁆ f)
            (by intros; simp [add_lie])
            (by intros; simp)
            (by intros; simp [lie_add])
            (by intros; simp)
        let right : L →ₗ[ℤ] L →ₗ[ℤ] MvPolynomial ι ℤ :=
          LinearMap.mk₂ ℤ
            (fun x y ↦
              cartanStage ℤ L ι b (p + 1) x
                  (cartanStage ℤ L ι b (p + 1) y f) -
                cartanStage ℤ L ι b (p + 1) y
                  (cartanStage ℤ L ι b (p + 1) x f))
            (by intros; simp; module)
            (by
              intro c m n
              simp only [map_smul]
              change c • cartanStage ℤ L ι b (p + 1) m
                      (cartanStage ℤ L ι b (p + 1) n f) -
                    cartanStage ℤ L ι b (p + 1) n
                      (c • cartanStage ℤ L ι b (p + 1) m f) = _
              rw [map_smul]
              module)
            (by intros; simp; module)
            (by
              intro c m n
              simp only [map_smul]
              change cartanStage ℤ L ι b (p + 1) m
                      (c • cartanStage ℤ L ι b (p + 1) n f) -
                    c • cartanStage ℤ L ι b (p + 1) n
                      (cartanStage ℤ L ι b (p + 1) m f) = _
              rw [map_smul]
              module)
        have hlr : left = right := by
          apply b.ext
          intro i
          apply b.ext
          intro j
          exact hb i j
        exact LinearMap.congr_fun (LinearMap.congr_fun hlr x) y

/- A finite stage at least as large as the input degree is the assembled action. -/
private theorem cartanStage_eq_action_of_degreeLE (N : ℕ)
    (x : L) (f : MvPolynomial ι ℤ) (hf : DegreeLE ι N f) :
    cartanStage ℤ L ι b N x f = cartanAction ℤ L ι b x f := by
  induction N generalizing x f with
  | zero =>
      have hmono (e : ι →₀ ℕ) (he : exponentDegree ι e ≤ 0) :
          cartanStage ℤ L ι b 0 x (MvPolynomial.monomial e 1) =
            cartanAction ℤ L ι b x (MvPolynomial.monomial e 1) := by
        have hb (i : ι) :
            cartanStage ℤ L ι b 0 (b i) (MvPolynomial.monomial e 1) =
              cartanAction ℤ L ι b (b i) (MvPolynomial.monomial e 1) := by
          have ha := cartanAction_basis_monomial ℤ L ι b i e 1
          rw [Nat.eq_zero_of_le_zero he] at ha
          calc
            cartanStage ℤ L ι b 0 (b i) (MvPolynomial.monomial e 1) =
                (1 : ℤ) • cartanStage ℤ L ι b 0 (b i)
                  (MvPolynomial.monomial e 1) := by module
            _ = cartanAction ℤ L ι b (b i) (MvPolynomial.monomial e 1) :=
              ha.symm
        let A : L →ₗ[ℤ] MvPolynomial ι ℤ :=
          (LinearMap.applyₗ (MvPolynomial.monomial e 1)).comp
            (cartanStage ℤ L ι b 0)
        let B : L →ₗ[ℤ] MvPolynomial ι ℤ :=
          (LinearMap.applyₗ (MvPolynomial.monomial e 1)).comp
            (cartanAction ℤ L ι b)
        have hAB : A = B := by
          apply b.ext
          intro i
          exact hb i
        exact LinearMap.congr_fun hAB x
      exact linearMap_eq_on_degreeLE_of_monomial ι
        (cartanStage ℤ L ι b 0 x) (cartanAction ℤ L ι b x) 0 hmono f hf
  | succ N ih =>
      have hmono (e : ι →₀ ℕ) (he : exponentDegree ι e ≤ N + 1) :
          cartanStage ℤ L ι b (N + 1) x (MvPolynomial.monomial e 1) =
            cartanAction ℤ L ι b x (MvPolynomial.monomial e 1) := by
        have hb (i : ι) :
            cartanStage ℤ L ι b (N + 1) (b i) (MvPolynomial.monomial e 1) =
              cartanAction ℤ L ι b (b i) (MvPolynomial.monomial e 1) := by
          by_cases htop : exponentDegree ι e = N + 1
          · have ha := cartanAction_basis_monomial ℤ L ι b i e 1
            rw [htop] at ha
            calc
              cartanStage ℤ L ι b (N + 1) (b i)
                    (MvPolynomial.monomial e 1) =
                  (1 : ℤ) • cartanStage ℤ L ι b (N + 1) (b i)
                    (MvPolynomial.monomial e 1) := by module
              _ = cartanAction ℤ L ι b (b i) (MvPolynomial.monomial e 1) :=
                ha.symm
          · have hlow : exponentDegree ι e ≤ N := by omega
            have hs := (stageInvariant L ι b (N + 1)).stable
              (exponentDegree ι e) (by omega) (by omega) (by omega)
              (b i) (MvPolynomial.monomial e 1)
              (degreeLE_monomial ι e 1)
            rw [hs]
            exact ih (b i) (MvPolynomial.monomial e 1)
              (degreeLE_mono ι hlow (degreeLE_monomial ι e 1))
        let A : L →ₗ[ℤ] MvPolynomial ι ℤ :=
          (LinearMap.applyₗ (MvPolynomial.monomial e 1)).comp
            (cartanStage ℤ L ι b (N + 1))
        let B : L →ₗ[ℤ] MvPolynomial ι ℤ :=
          (LinearMap.applyₗ (MvPolynomial.monomial e 1)).comp
            (cartanAction ℤ L ι b)
        have hAB : A = B := by
          apply b.ext
          intro i
          exact hb i
        exact LinearMap.congr_fun hAB x
      exact linearMap_eq_on_degreeLE_of_monomial ι
        (cartanStage ℤ L ι b (N + 1) x) (cartanAction ℤ L ι b x)
        (N + 1) hmono f hf

private theorem cartanActionLieCompatible_int :
    CartanActionLieCompatible ℤ L ι b := by
  intro x y
  apply LinearMap.ext
  intro f
  induction f using MvPolynomial.induction_on' with
  | monomial e r =>
      let d := exponentDegree ι e
      let m : MvPolynomial ι ℤ := MvPolynomial.monomial e 1
      have hm : DegreeLE ι d m := degreeLE_monomial ι e 1
      have hmN : DegreeLE ι (d + 1) m := degreeLE_mono ι (by omega) hm
      have hstage := stageInvariant L ι b (d + 1)
      have hxBound : DegreeLE ι (d + 1)
          (cartanStage ℤ L ι b (d + 1) x m) :=
        hstage.bounded d (by omega) x m hm
      have hyBound : DegreeLE ι (d + 1)
          (cartanStage ℤ L ι b (d + 1) y m) :=
        hstage.bounded d (by omega) y m hm
      have hunit :
          cartanAction ℤ L ι b ⁅x, y⁆ m =
            cartanAction ℤ L ι b x (cartanAction ℤ L ι b y m) -
              cartanAction ℤ L ι b y (cartanAction ℤ L ι b x m) := by
        calc
          cartanAction ℤ L ι b ⁅x, y⁆ m =
              cartanStage ℤ L ι b (d + 1) ⁅x, y⁆ m :=
            (cartanStage_eq_action_of_degreeLE L ι b (d + 1) ⁅x, y⁆ m hmN).symm
          _ = cartanStage ℤ L ι b (d + 1) x
                  (cartanStage ℤ L ι b (d + 1) y m) -
                cartanStage ℤ L ι b (d + 1) y
                  (cartanStage ℤ L ι b (d + 1) x m) :=
            hstage.compatible d (by omega) x y m hm
          _ = cartanAction ℤ L ι b x (cartanAction ℤ L ι b y m) -
                cartanAction ℤ L ι b y (cartanAction ℤ L ι b x m) := by
            rw [cartanStage_eq_action_of_degreeLE L ι b (d + 1) x _ hyBound,
              cartanStage_eq_action_of_degreeLE L ι b (d + 1) y _ hxBound,
              cartanStage_eq_action_of_degreeLE L ι b (d + 1) y m hmN,
              cartanStage_eq_action_of_degreeLE L ι b (d + 1) x m hmN]
      rw [show MvPolynomial.monomial e r = r • m by
        dsimp only [m]
        calc
          MvPolynomial.monomial e r =
              MvPolynomial.monomial e (r • (1 : ℤ)) := by
            congr
            simp
          _ = r • MvPolynomial.monomial e 1 := by rw [map_zsmul]]
      simp only [map_smul]
      change r • cartanAction ℤ L ι b ⁅x, y⁆ m =
        r • (cartanAction ℤ L ι b x (cartanAction ℤ L ι b y m) -
          cartanAction ℤ L ι b y (cartanAction ℤ L ι b x m))
      rw [hunit]
  | add p q hp hq =>
      simp only [map_add, hp, hq]

/-- Ordered PBW over `ℤ` for a Lie ring with a chosen ordered additive basis. -/
theorem freeModulePBW_int : PBW.FreeModulePBW ℤ L ι b :=
  freeModulePBW_of_cartanAction_lie ℤ L ι b
    (cartanActionLieCompatible_int L ι b)

end

end LieRings.DimensionSubring.MetabelianOdd
