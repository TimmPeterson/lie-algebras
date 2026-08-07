import LieRings.DimensionSubring.DegreeFive.FreeClassTwoPBW
import LieRings.DimensionSubring.DegreeFive.RelationTruncation
import LieRings.DimensionSubring.DegreeFive.PlacedIdentities
import LieRings.DimensionSubring.DegreeFive.WordExpansion

/-!
# Weighted PBW symbols for the free class-two quotient

The generators of `P ⊕ ⋀²P` have weights one and two respectively.  This file equips
the explicit polynomial PBW model with the corresponding homogeneous projections and defines
the symbol obtained by mapping `U(𝕃(X))` to the enveloping algebra of its class-two
quotient and evaluating on the PBW vacuum.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u) [LinearOrder X]

local notation "P" => GeneratorModule X
local notation "M" => FreeClassTwo P
local notation "I" => ClassTwoBasisIndex X
local notation "Poly" => MvPolynomial I ℤ

/-- PBW weight of a class-two basis variable. -/
def classTwoVariableWeight : I → ℕ
  | .generator _ => 1
  | .central _ => 2

@[simp]
theorem classTwoVariableWeight_generator (x : X) :
    classTwoVariableWeight X (.generator x) = 1 := rfl

@[simp]
theorem classTwoVariableWeight_central (a : ClassTwoWedgeIndex X) :
    classTwoVariableWeight X (.central a) = 2 := rfl

/-- Weighted degree of a polynomial exponent vector. -/
def classTwoExponentWeight (e : I →₀ ℕ) : ℕ :=
  e.sum fun i n ↦ n * classTwoVariableWeight X i

@[simp]
theorem classTwoExponentWeight_zero :
    classTwoExponentWeight X 0 = 0 := by
  simp [classTwoExponentWeight]

@[simp]
theorem classTwoExponentWeight_single (i : I) (n : ℕ) :
    classTwoExponentWeight X (Finsupp.single i n) =
      n * classTwoVariableWeight X i := by
  simp [classTwoExponentWeight]

theorem classTwoExponentWeight_add (e f : I →₀ ℕ) :
    classTwoExponentWeight X (e + f) =
      classTwoExponentWeight X e + classTwoExponentWeight X f := by
  classical
  simp [classTwoExponentWeight, Finsupp.sum_add_index, add_mul, add_comm,
    add_left_comm, add_assoc]

/-- Projection to one exact weighted PBW degree. -/
def classTwoWeightedComponent (n : ℕ) : Poly →ₗ[ℤ] Poly where
  toFun p := Finsupp.filter (fun e : I →₀ ℕ ↦ classTwoExponentWeight X e = n) p
  map_add' p q := by
    exact Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

@[simp]
theorem classTwoWeightedComponent_coeff (n : ℕ) (e : I →₀ ℕ) (p : Poly) :
    MvPolynomial.coeff e (classTwoWeightedComponent X n p) =
      if classTwoExponentWeight X e = n then MvPolynomial.coeff e p else 0 := by
  classical
  change Finsupp.filter (fun f : I →₀ ℕ ↦ classTwoExponentWeight X f = n) p e = _
  by_cases h : classTwoExponentWeight X e = n
  · rw [Finsupp.filter_apply_pos
      (fun f : I →₀ ℕ ↦ classTwoExponentWeight X f = n) p h]
    rw [if_pos h]
    rfl
  · rw [Finsupp.filter_apply_neg
      (fun f : I →₀ ℕ ↦ classTwoExponentWeight X f = n) p h]
    simp [h]

@[simp]
theorem classTwoWeightedComponent_monomial_same
    (e : I →₀ ℕ) (a : ℤ) :
    classTwoWeightedComponent X (classTwoExponentWeight X e)
        (MvPolynomial.monomial e a) =
      MvPolynomial.monomial e a := by
  classical
  ext f
  by_cases h : f = e
  · subst f
    simp [classTwoWeightedComponent_coeff, MvPolynomial.coeff_monomial]
  · have h' : e ≠ f := Ne.symm h
    simp [classTwoWeightedComponent_coeff, MvPolynomial.coeff_monomial, h, h']

theorem classTwoWeightedComponent_monomial_of_ne
    (n : ℕ) (e : I →₀ ℕ) (a : ℤ)
    (h : classTwoExponentWeight X e ≠ n) :
    classTwoWeightedComponent X n (MvPolynomial.monomial e a) = 0 := by
  classical
  ext f
  by_cases hfe : f = e
  · subst f
    simp [classTwoWeightedComponent_coeff, MvPolynomial.coeff_monomial, h]
  · have hef : e ≠ f := Ne.symm hfe
    simp [classTwoWeightedComponent_coeff, MvPolynomial.coeff_monomial, hfe, hef]

/-- Projection to one exact ordinary polynomial degree. -/
def classTwoPolynomialDegreeComponent (n : ℕ) : Poly →ₗ[ℤ] Poly where
  toFun p := Finsupp.filter (fun e : I →₀ ℕ ↦ e.sum (fun _ k ↦ k) = n) p
  map_add' p q := by
    exact Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

@[simp]
theorem classTwoPolynomialDegreeComponent_coeff
    (n : ℕ) (e : I →₀ ℕ) (p : Poly) :
    MvPolynomial.coeff e (classTwoPolynomialDegreeComponent X n p) =
      if e.sum (fun _ k ↦ k) = n then MvPolynomial.coeff e p else 0 := by
  classical
  change Finsupp.filter (fun f : I →₀ ℕ ↦ f.sum (fun _ k ↦ k) = n) p e = _
  by_cases h : e.sum (fun _ k ↦ k) = n
  · rw [Finsupp.filter_apply_pos
      (fun f : I →₀ ℕ ↦ f.sum (fun _ k ↦ k) = n) p h]
    rw [if_pos h]
    rfl
  · rw [Finsupp.filter_apply_neg
      (fun f : I →₀ ℕ ↦ f.sum (fun _ k ↦ k) = n) p h]
    simp [h]

/-! ## Weighted support calculus -/

/-- A polynomial all of whose nonzero monomials have one fixed PBW weight. -/
def ClassTwoIsWeighted (n : ℕ) (p : Poly) : Prop :=
  ∀ e ∈ p.support, classTwoExponentWeight X e = n

theorem classTwoIsWeighted_zero (n : ℕ) :
    ClassTwoIsWeighted X n 0 := by
  intro e he
  simp at he

theorem classTwoIsWeighted_add {n : ℕ} {p q : Poly}
    (hp : ClassTwoIsWeighted X n p) (hq : ClassTwoIsWeighted X n q) :
    ClassTwoIsWeighted X n (p + q) := by
  classical
  intro e he
  have he' := MvPolynomial.support_add he
  simp only [Finset.mem_union] at he'
  exact he'.elim (hp e) (hq e)

theorem classTwoIsWeighted_neg {n : ℕ} {p : Poly}
    (hp : ClassTwoIsWeighted X n p) :
    ClassTwoIsWeighted X n (-p) := by
  classical
  intro e he
  have : e ∈ p.support := by simpa using he
  exact hp e this

theorem classTwoIsWeighted_zsmul {n : ℕ} {p : Poly}
    (a : ℤ) (hp : ClassTwoIsWeighted X n p) :
    ClassTwoIsWeighted X n (a • p) := by
  classical
  intro e he
  exact hp e (MvPolynomial.support_smul he)

theorem classTwoIsWeighted_monomial (e : I →₀ ℕ) (a : ℤ) :
    ClassTwoIsWeighted X (classTwoExponentWeight X e)
      (MvPolynomial.monomial e a) := by
  classical
  intro f hf
  have hf' := MvPolynomial.support_monomial_subset hf
  exact congrArg (classTwoExponentWeight X) (by simpa using hf')

theorem classTwoIsWeighted_X (i : I) :
    ClassTwoIsWeighted X (classTwoVariableWeight X i) (MvPolynomial.X i) := by
  simpa [MvPolynomial.X] using
    (classTwoIsWeighted_monomial X (Finsupp.single i 1) (1 : ℤ))

theorem classTwoIsWeighted_mul {m n : ℕ} {p q : Poly}
    (hp : ClassTwoIsWeighted X m p) (hq : ClassTwoIsWeighted X n q) :
    ClassTwoIsWeighted X (m + n) (p * q) := by
  classical
  intro e he
  have he' := MvPolynomial.support_mul p q he
  rw [Finset.mem_add] at he'
  obtain ⟨f, hf, g, hg, hfg⟩ := he'
  rw [← hfg, classTwoExponentWeight_add, hp f hf, hq g hg]

/-- Exact-weight polynomials form an integral submodule. -/
def classTwoWeightedSubmodule (n : ℕ) : Submodule ℤ Poly where
  carrier := ClassTwoIsWeighted X n
  zero_mem' := classTwoIsWeighted_zero X n
  add_mem' := classTwoIsWeighted_add X
  smul_mem' a p hp := classTwoIsWeighted_zsmul X a hp

/-- The coordinate polynomial of a central class-two element has exact weight two. -/
theorem freeClassTwoPolynomial_central_isWeighted (w : ⋀[ℤ]^2 P) :
    ClassTwoIsWeighted X 2 (freeClassTwoPolynomial X (0, w)) := by
  let bW := (freeGeneratorBasis X).exteriorPower 2
  let f : (⋀[ℤ]^2 P) →ₗ[ℤ] Poly :=
    (freeClassTwoPolynomial X).comp (freeClassTwoCentralInclusion X)
  let N := classTwoWeightedSubmodule X 2
  have hb (a : ClassTwoWedgeIndex X) : f (bW a) ∈ N := by
    change ClassTwoIsWeighted X 2
      (freeClassTwoPolynomial X (0, bW a))
    rw [show (0, bW a) =
        freeClassTwoBasis X (ClassTwoBasisIndex.central a) by
      exact (freeClassTwoBasis_inr X a).symm]
    rw [freeClassTwoPolynomial_basis]
    exact classTwoIsWeighted_X X (ClassTwoBasisIndex.central a)
  let g : (⋀[ℤ]^2 P) →ₗ[ℤ] N :=
    bW.constr ℤ fun a ↦ ⟨f (bW a), hb a⟩
  have hgf : N.subtype.comp g = f := by
    apply bW.ext
    intro a
    change ((g (bW a) : N) : Poly) = f (bW a)
    change (((bW.constr ℤ) (fun a ↦ (⟨f (bW a), hb a⟩ : N)))
      (bW a) : Poly) = _
    rw [Module.Basis.constr_basis]
  change ClassTwoIsWeighted X 2
    (freeClassTwoPolynomial X (freeClassTwoCentralInclusion X w))
  change f w ∈ N
  have hw := LinearMap.congr_fun hgf w
  rw [← hw]
  exact (g w).property

/-- Every value assigned to a generator by a correction derivation is either zero or a
central coordinate polynomial of exact weight two. -/
theorem correctionValue_isWeighted (i : X) (k : I) :
    ClassTwoIsWeighted X 2 (correctionValue X i k) := by
  cases k with
  | generator j =>
      change ClassTwoIsWeighted X 2
        (if (ClassTwoBasisIndex.generator j : I) <
            ClassTwoBasisIndex.generator i then
          freeClassTwoPolynomial X
            ⁅freeClassTwoBasis X (ClassTwoBasisIndex.generator i),
              freeClassTwoBasis X (ClassTwoBasisIndex.generator j)⁆
        else 0)
      by_cases h : (ClassTwoBasisIndex.generator j : I) <
          ClassTwoBasisIndex.generator i
      · rw [if_pos h, FreeClassTwo.bracket_apply]
        exact freeClassTwoPolynomial_central_isWeighted X
          (wedgeTwo P
            (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)).1
            (freeClassTwoBasis X (ClassTwoBasisIndex.generator j)).1)
      · rw [if_neg h]
        exact classTwoIsWeighted_zero X 2
  | central a =>
      exact classTwoIsWeighted_zero X 2

theorem classTwoExponentWeight_sub_single_add
    (e : I →₀ ℕ) (i : I) (hi : 0 < e i) :
    classTwoExponentWeight X (e - Finsupp.single i 1) +
        classTwoVariableWeight X i =
      classTwoExponentWeight X e := by
  have hle : Finsupp.single i 1 ≤ e := by
    rw [Finsupp.single_le_iff]
    exact hi
  have heq : e - Finsupp.single i 1 + Finsupp.single i 1 = e :=
    tsub_add_cancel_of_le hle
  have h := classTwoExponentWeight_add X
    (e - Finsupp.single i 1) (Finsupp.single i 1)
  rw [heq, classTwoExponentWeight_single, one_mul] at h
  exact h.symm

/-- A correction derivation raises PBW weight by one. -/
theorem correctionDerivation_monomial_isWeighted
    (i : X) (e : I →₀ ℕ) (a : ℤ) :
    ClassTwoIsWeighted X (classTwoExponentWeight X e + 1)
      (correctionDerivation X i (MvPolynomial.monomial e a)) := by
  classical
  rw [correctionDerivation, MvPolynomial.mkDerivation_monomial]
  apply classTwoIsWeighted_zsmul X a
  let N := classTwoWeightedSubmodule X (classTwoExponentWeight X e + 1)
  change e.sum (fun k n ↦
      MvPolynomial.monomial (e - Finsupp.single k 1) (n : ℤ) •
        correctionValue X i k) ∈ N
  rw [Finsupp.sum]
  apply N.sum_mem
  intro k hk
  rw [Algebra.smul_def]
  cases k with
  | central c =>
      change MvPolynomial.monomial
          (e - Finsupp.single (ClassTwoBasisIndex.central c) 1)
            ((e (ClassTwoBasisIndex.central c) : ℕ) : ℤ) * 0 ∈ N
      rw [mul_zero]
      exact N.zero_mem
  | generator j =>
      have hj : 0 < e (ClassTwoBasisIndex.generator j) := by
        exact Finsupp.mem_support_iff.mp hk |>.bot_lt
      have hsub := classTwoExponentWeight_sub_single_add X e
        (ClassTwoBasisIndex.generator j) hj
      rw [classTwoVariableWeight_generator] at hsub
      have hmono := classTwoIsWeighted_monomial X
        (e - Finsupp.single (ClassTwoBasisIndex.generator j) 1)
        ((e (ClassTwoBasisIndex.generator j) : ℕ) : ℤ)
      have hcorr := correctionValue_isWeighted X i
        (ClassTwoBasisIndex.generator j)
      have hmul := classTwoIsWeighted_mul X hmono hcorr
      change ClassTwoIsWeighted X (classTwoExponentWeight X e + 1) _
      convert hmul using 1
      omega

theorem correctionDerivation_isWeighted
    (i : X) {n : ℕ} {p : Poly} (hp : ClassTwoIsWeighted X n p) :
    ClassTwoIsWeighted X (n + 1) (correctionDerivation X i p) := by
  classical
  let N := classTwoWeightedSubmodule X (n + 1)
  rw [MvPolynomial.as_sum p]
  rw [map_sum]
  apply N.sum_mem
  intro e he
  have hew := hp e he
  change ClassTwoIsWeighted X (n + 1)
    (correctionDerivation X i
      (MvPolynomial.monomial e (MvPolynomial.coeff e p)))
  rw [← hew]
  exact correctionDerivation_monomial_isWeighted X i e _

/-- A noncentral basis operator raises PBW weight by one. -/
theorem freeClassTwoAction_generator_isWeighted
    (i : X) {n : ℕ} {p : Poly} (hp : ClassTwoIsWeighted X n p) :
    ClassTwoIsWeighted X (n + 1)
      (freeClassTwoAction X
        (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)) p) := by
  rw [freeClassTwoAction_basis_inl_apply]
  apply classTwoIsWeighted_add X
  · have hx := classTwoIsWeighted_X X
      (ClassTwoBasisIndex.generator i)
    have hmul := classTwoIsWeighted_mul X hx hp
    simpa [add_comm] using hmul
  · exact correctionDerivation_isWeighted X i hp

@[simp]
theorem freeClassTwoTruncation_of_eq_basis_generator (x : X) :
    freeClassTwoTruncation X (FreeLieAlgebra.of ℤ x) =
      freeClassTwoBasis X (ClassTwoBasisIndex.generator x) := by
  apply Prod.ext
  · rw [freeClassTwoTruncation_of, freeClassTwoBasis_inl_fst]
  · rw [freeClassTwoTruncation_of, freeClassTwoBasis_inl_snd]

theorem classTwoIsWeighted_one :
    ClassTwoIsWeighted X 0 (1 : Poly) := by
  intro e he
  have he' : e = 0 := by
    simpa using he
  subst e
  exact classTwoExponentWeight_zero X

/-- The enveloping map induced by free class-two truncation. -/
def freeEnvelopingToClassTwoEnveloping :
    UEA ℤ (CanonicalFreeLie X) →ₐ[ℤ] UEA ℤ M :=
  UniversalEnvelopingAlgebra.lift ℤ
    ((UniversalEnvelopingAlgebra.ι ℤ : LieHom ℤ M (UEA ℤ M)).comp
      (freeClassTwoTruncation X))

@[simp]
theorem freeEnvelopingToClassTwoEnveloping_iota (x : CanonicalFreeLie X) :
    freeEnvelopingToClassTwoEnveloping X
        (UniversalEnvelopingAlgebra.ι ℤ x) =
      UniversalEnvelopingAlgebra.ι ℤ (freeClassTwoTruncation X x) := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ _ x

/-- The full ordered PBW polynomial symbol of an element of `U(𝕃(X))`, after passing
to the free class-two quotient. -/
def freeEnvelopingToClassTwoPBWSymbol :
    UEA ℤ (CanonicalFreeLie X) →ₗ[ℤ] Poly :=
  (freeClassTwoTriangularRepresentation X).vacuumEvaluation.comp
    (freeEnvelopingToClassTwoEnveloping X).toLinearMap

@[simp]
theorem freeEnvelopingToClassTwoPBWSymbol_iota (x : CanonicalFreeLie X) :
    freeEnvelopingToClassTwoPBWSymbol X
        (UniversalEnvelopingAlgebra.ι ℤ x) =
      freeClassTwoPolynomial X (freeClassTwoTruncation X x) := by
  change (freeClassTwoTriangularRepresentation X).vacuumEvaluation
      (freeEnvelopingToClassTwoEnveloping X
        (UniversalEnvelopingAlgebra.ι ℤ x)) = _
  rw [freeEnvelopingToClassTwoEnveloping_iota]
  rw [LieRings.PBW.TriangularRepresentation.vacuumEvaluation_apply,
    LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
  exact (freeClassTwoTriangularRepresentation X).toLieHom_apply_one
    (freeClassTwoTruncation X x)

/-- The symbol of a product is computed by applying the left factor's class-two operator to
the symbol of the right factor. -/
theorem freeEnvelopingToClassTwoPBWSymbol_mul (u v : UEA ℤ (CanonicalFreeLie X)) :
    freeEnvelopingToClassTwoPBWSymbol X (u * v) =
      (freeClassTwoTriangularRepresentation X).envelopingAction
          (freeEnvelopingToClassTwoEnveloping X u)
        (freeEnvelopingToClassTwoPBWSymbol X v) := by
  change
    (freeClassTwoTriangularRepresentation X).envelopingAction
        (freeEnvelopingToClassTwoEnveloping X (u * v)) 1 = _
  rw [map_mul, map_mul]
  rfl

theorem universalEnvelopingEquiv_generatorWord (xs : List X) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
        (envelopingWord ℤ (CanonicalFreeLie X)
          (xs.map (FreeLieAlgebra.of ℤ))) =
      freeAlgebraWord X xs := by
  induction xs with
  | nil =>
      exact map_one
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X)
  | cons x xs ih =>
      simp only [List.map_cons, envelopingWord_cons, freeAlgebraWord_cons]
      calc
        _ = FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
              (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x)) *
            FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
              (envelopingWord ℤ (CanonicalFreeLie X)
                (xs.map (FreeLieAlgebra.of ℤ))) :=
          map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X) _ _
        _ = PBW.freeLieToFreeAlgebra ℤ X (FreeLieAlgebra.of ℤ x) *
            freeAlgebraWord X xs := congrArg₂ (fun a b ↦ a * b)
          (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
            X (FreeLieAlgebra.of ℤ x)) ih
        _ = _ := by simp [PBW.freeLieToFreeAlgebra]

/-- A word of `r` original free generators has exact weighted PBW degree `r` after class-two
collection.  Every commutator correction replaces two weight-one variables by one weight-two
central variable, so the weight is preserved integrally. -/
theorem freeEnvelopingToClassTwoPBWSymbol_generatorWord_isWeighted
    (xs : List X) :
    ClassTwoIsWeighted X xs.length
      (freeEnvelopingToClassTwoPBWSymbol X
        (envelopingWord ℤ (CanonicalFreeLie X)
          (xs.map (FreeLieAlgebra.of ℤ)))) := by
  induction xs with
  | nil =>
      simp only [List.map_nil, envelopingWord_nil]
      change ClassTwoIsWeighted X 0
        ((freeClassTwoTriangularRepresentation X).vacuumEvaluation
          (freeEnvelopingToClassTwoEnveloping X 1))
      rw [map_one]
      rw [LieRings.PBW.TriangularRepresentation.vacuumEvaluation_apply]
      rw [map_one (freeClassTwoTriangularRepresentation X).envelopingAction]
      change ClassTwoIsWeighted X 0 (1 : Poly)
      exact classTwoIsWeighted_one X
  | cons x xs ih =>
      simp only [List.map_cons, envelopingWord_cons, List.length_cons]
      rw [freeEnvelopingToClassTwoPBWSymbol_mul,
        freeEnvelopingToClassTwoEnveloping_iota,
        freeClassTwoTruncation_of_eq_basis_generator,
        LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
      change ClassTwoIsWeighted X (xs.length + 1)
        (freeClassTwoAction X
          (freeClassTwoBasis X (ClassTwoBasisIndex.generator x))
          (freeEnvelopingToClassTwoPBWSymbol X
            (envelopingWord ℤ (CanonicalFreeLie X)
              (xs.map (FreeLieAlgebra.of ℤ)))))
      exact freeClassTwoAction_generator_isWeighted X x ih

/-- An exact-weight polynomial has zero projection to every different weight. -/
theorem classTwoWeightedComponent_eq_zero_of_isWeighted_of_ne
    {m n : ℕ} {p : Poly} (hp : ClassTwoIsWeighted X m p) (h : m ≠ n) :
    classTwoWeightedComponent X n p = 0 := by
  classical
  ext e
  rw [classTwoWeightedComponent_coeff]
  by_cases he : classTwoExponentWeight X e = n
  · rw [if_pos he]
    by_contra hcoeff
    have hem : classTwoExponentWeight X e = m :=
      hp e (MvPolynomial.mem_support_iff.mpr hcoeff)
    exact h (hem.symm.trans he)
  · rw [if_neg he]
    rfl

end

end DegreeFive

end LieRings
