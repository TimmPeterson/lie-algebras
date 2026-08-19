import LieRings.DimensionSubring.MetabelianOdd.WeightedPresentation
import LieRings.DimensionSubring.DegreeFive.CoordinatePBW

noncomputable section

example {I : Type*} [Fintype I] [DecidableEq I]
    (f g : I →₀ ℤ) (i : I) :
    f.sum (fun a za ↦ g.sum fun c zc ↦
      if a = i ∧ c = i then za * zc else 0) = f i * g i := by
  classical
  have hmulSum (r : ℤ) (g : I →₀ ℤ) (j : I) :
      g.sum (fun c zc ↦ if c = j then r * zc else 0) = r * g j := by
    calc
      _ = r * g.sum (fun c zc ↦ if c = j then zc else 0) := by
        rw [Finsupp.mul_sum]
        apply Finsupp.sum_congr
        intro c hc
        by_cases hcj : c = j <;> simp [hcj]
      _ = _ := by rw [Finsupp.sum_ite_self_eq']
  calc
    _ = f.sum (fun a za ↦
        if a = i then za * g i else 0) := by
      apply Finsupp.sum_congr
      intro a ha
      by_cases hai : a = i
      · subst a
        simp only [true_and, if_pos]
        exact hmulSum (f i) g i
      · simp [hai]
    _ = _ := by
      simpa [mul_comm] using hmulSum (g i) f i

example {I : Type*} [Fintype I] [DecidableEq I]
    (f g : I →₀ ℤ) (i j : I) (hij : i ≠ j) :
    f.sum (fun a za ↦ g.sum fun c zc ↦
      if (a = i ∧ c = j) ∨ (a = j ∧ c = i)
      then za * zc else 0) = f i * g j + f j * g i := by
  classical
  have hmulSum (r : ℤ) (g : I →₀ ℤ) (k : I) :
      g.sum (fun c zc ↦ if c = k then r * zc else 0) = r * g k := by
    calc
      _ = r * g.sum (fun c zc ↦ if c = k then zc else 0) := by
        rw [Finsupp.mul_sum]
        apply Finsupp.sum_congr
        intro c hc
        by_cases hck : c = k <;> simp [hck]
      _ = _ := by rw [Finsupp.sum_ite_self_eq']
  calc
    _ = f.sum (fun a za ↦
        (if a = i then za * g j else 0) +
        (if a = j then za * g i else 0)) := by
      apply Finsupp.sum_congr
      intro a ha
      by_cases hai : a = i
      · subst a
        simp only [true_and, eq_self, hij, false_and, or_false,
          if_true, if_false, false_or]
        simpa using hmulSum (f i) g j
      · by_cases haj : a = j
        · subst a
          simp only [hai, false_and, eq_self, true_and, false_or,
            if_false, if_true, zero_add]
          exact hmulSum (f j) g i
        · simp [hai, haj]
    _ = _ := by
      rw [Finsupp.sum_add]
      congr 1
      · simpa [mul_comm] using hmulSum (g j) f i
      · simpa [mul_comm] using hmulSum (g i) f j

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
    have ha : a ∈ ({i} + {i} : Multiset I) := by rw [← hm]; simp
    have hc : c ∈ ({i} + {i} : Multiset I) := by rw [← hm]; simp
    simpa using And.intro ha hc
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
    · exact Or.inl ⟨h.1, Multiset.singleton_inj.mp h.2⟩
    · obtain ⟨hai, cs, hc, hj⟩ := h
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
  change (b.repr x).sum (fun a za ↦
      (MvPolynomial.coeffAddMonoidHom _)
        ((b.repr y).sum fun c zc ↦
          (za • MvPolynomial.X a) * (zc • MvPolynomial.X c))) = _
  simp_rw [map_finsuppSum]
  simp only [smul_mul_smul, map_zsmul]
  have hmulSum (r : ℤ) (f : I →₀ ℤ) (k : I) :
      f.sum (fun c zc ↦ if c = k then r * zc else 0) = r * f k := by
    calc
      _ = r * f.sum (fun c zc ↦ if c = k then zc else 0) := by
        rw [Finsupp.mul_sum]
        apply Finsupp.sum_congr
        intro c hc
        by_cases hck : c = k <;> simp [hck]
      _ = _ := by rw [Finsupp.sum_ite_self_eq']
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    change (b.repr x).sum (fun a za ↦ (b.repr y).sum fun c zc ↦
      (za * zc) * MvPolynomial.coeff
        (Finsupp.single i 1 + Finsupp.single i 1)
          (MvPolynomial.X a * MvPolynomial.X c)) = _
    simp_rw [MvPolynomial.X, MvPolynomial.monomial_mul,
      MvPolynomial.coeff_monomial, pairExponent_eq_diag_iff]
    simp only [mul_ite, mul_one, mul_zero]
    calc
      _ = (b.repr x).sum (fun a za ↦
          if a = i then za * b.repr y i else 0) := by
        apply Finsupp.sum_congr
        intro a ha
        by_cases hai : a = i
        · subst a
          simp only [true_and, if_true]
          exact hmulSum (b.repr x i) (b.repr y) i
        · simp [hai]
      _ = _ := by
        simpa [mul_comm] using hmulSum (b.repr y i) (b.repr x) i
  · simp only [if_neg hij]
    change (b.repr x).sum (fun a za ↦ (b.repr y).sum fun c zc ↦
      (za * zc) * MvPolynomial.coeff
        (Finsupp.single i 1 + Finsupp.single j 1)
          (MvPolynomial.X a * MvPolynomial.X c)) = _
    simp_rw [MvPolynomial.X, MvPolynomial.monomial_mul,
      MvPolynomial.coeff_monomial,
      pairExponent_eq_offdiag_iff _ _ _ _ hij]
    simp only [mul_ite, mul_one, mul_zero]
    calc
      _ = (b.repr x).sum (fun a za ↦
          (if a = i then za * b.repr y j else 0) +
          (if a = j then za * b.repr y i else 0)) := by
        apply Finsupp.sum_congr
        intro a ha
        by_cases hai : a = i
        · subst a
          simp only [true_and, eq_self, hij, false_and, or_false,
            if_true, if_false]
          simpa using hmulSum (b.repr x i) (b.repr y) j
        · by_cases haj : a = j
          · subst a
            simp only [hai, false_and, eq_self, true_and, false_or,
              if_false, if_true, zero_add]
            exact hmulSum (b.repr x j) (b.repr y) i
          · simp [hai, haj]
      _ = _ := by
        rw [Finsupp.sum_add]
        congr 1
        · simpa [mul_comm] using
            hmulSum (b.repr y j) (b.repr x) i
        · simpa [mul_comm] using
            hmulSum (b.repr y i) (b.repr x) j

end
#check sub_left_inj
#check sub_right_inj
#check sub_left_injective
#check sub_right_injective
#check lie_skew
#check lie_jacobi
#check LieModule.antitone_lowerCentralSeries
