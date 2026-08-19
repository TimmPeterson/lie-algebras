import LieRings.DimensionSubring.MetabelianOdd.WeightedPresentation

noncomputable section

#check Finsupp.sum_mul
#check Finsupp.mul_sum
#check MvPolynomial.coeff_C_mul
#check MvPolynomial.coeff_monomial
#check smul_mul_smul
#check smul_mul_assoc
#check mul_smul_comm
#check Multiset.cons_eq_cons

private def linPoly {I M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis I ℤ M) (x : M) : MvPolynomial I ℤ :=
  (b.repr x).sum fun i c ↦ c • MvPolynomial.X i

private theorem pairExponent_eq_diag_iff {I : Type*} [DecidableEq I]
    (a c i : I) :
    Finsupp.single a 1 + Finsupp.single c 1 =
        Finsupp.single i 1 + Finsupp.single i 1 ↔
      a = i ∧ c = i := by
  constructor
  · intro h
    have hm : ({a} + {c} : Multiset I) = {i} + {i} := by
      apply Multiset.toFinsupp.injective
      simpa only [Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton] using h
    change a ::ₘ ({c} : Multiset I) = i ::ₘ ({i} : Multiset I) at hm
    rw [Multiset.cons_eq_cons] at hm
    rcases hm with h | h
    · exact ⟨h.1, Multiset.singleton_injective h.2⟩
    · obtain ⟨cs, hc, hi⟩ := h.2
      have hcs : cs = 0 := by
        apply Multiset.card_eq_zero.mp
        have hcard := congrArg Multiset.card hc
        simpa using hcard
      subst cs
      simp only [Multiset.cons_zero, Multiset.singleton_inj] at hc hi
      exact (h.1 hi.symm).elim
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem pairExponent_eq_offdiag_iff {I : Type*} [DecidableEq I]
    (a c i j : I) (hij : i ≠ j) :
    Finsupp.single a 1 + Finsupp.single c 1 =
        Finsupp.single i 1 + Finsupp.single j 1 ↔
      (a = i ∧ c = j) ∨ (a = j ∧ c = i) := by
  constructor
  · intro h
    have hm : ({a} + {c} : Multiset I) = {i} + {j} := by
      apply Multiset.toFinsupp.injective
      simpa only [Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton] using h
    change a ::ₘ ({c} : Multiset I) = i ::ₘ ({j} : Multiset I) at hm
    rw [Multiset.cons_eq_cons] at hm
    rcases hm with h | h
    · left
      exact ⟨h.1, by simpa using h.2⟩
    · obtain ⟨cs, hc, hj⟩ := h.2
      have hcs : cs = 0 := by
        apply Multiset.card_eq_zero.mp
        have hcard := congrArg Multiset.card hc
        simpa using hcard
      subst cs
      simp only [Multiset.cons_zero, Multiset.singleton_inj] at hc hj
      exact Or.inr ⟨hj.symm, hc⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

example {I M : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis I ℤ M) (x y : M) (i j : I) :
    MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
        (linPoly b x * linPoly b y) =
      if i = j then b.repr x i * b.repr y i
      else b.repr x i * b.repr y j + b.repr x j * b.repr y i := by
  classical
  unfold linPoly
  change MvPolynomial.coeff _
      ((b.repr x).sum (fun a z ↦ z • MvPolynomial.X a) *
        (b.repr y).sum (fun c z ↦ z • MvPolynomial.X c)) = _
  rw [Finsupp.sum_mul]
  change (MvPolynomial.coeffAddMonoidHom _)
      ((b.repr x).sum fun a z ↦ (z • MvPolynomial.X a) *
        (b.repr y).sum fun c z ↦ z • MvPolynomial.X c) = _
  rw [map_finsuppSum]
  simp_rw [Finsupp.mul_sum]
  simp_rw [map_finsuppSum]
  simp only [smul_mul_smul, map_zsmul]
  by_cases hij : i = j
  · subst j
    simp [MvPolynomial.X, MvPolynomial.monomial_mul, Finsupp.sum,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
      pairExponent_eq_diag_iff]
  · simp [MvPolynomial.X, MvPolynomial.monomial_mul, Finsupp.sum,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
      pairExponent_eq_offdiag_iff, hij]
