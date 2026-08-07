import LieRings.PBW.TriangularRepresentation

/-!
# The Cartan--Eilenberg triangular action

This file implements the recursive operator used in Cartan--Eilenberg, Chapter XIII, Lemma 3.5.
For a basis element `b i` and a commutative monomial, the easy case prepends `i` when it is already
in order.  If the least variable is `j < i`, the defining identity is

`D_i (X_j m) = D_j (D_i m) + D_[i,j] m`.

The two occurrences on the right that are not the leading monomial have lower polynomial degree,
so the operators can be constructed degree by degree.  `cartanStage n` is the finite stage used on
monomials of degree `n`; `cartanAction` assembles those stages into an `R`-linear map
`L → End_R(R[X])`.

The remaining main theorem in this file is that `cartanAction` respects the Lie bracket.  Its proof
is the Jacobi calculation in the last paragraph of Cartan--Eilenberg Lemma 3.5.  Once proved, the
linear action upgrades to `TriangularRepresentation`, and
`PBW.TriangularRepresentation.freeModulePBW`
immediately supplies the complete theorem.
-/

namespace LieRings.PBW

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
variable (ι : Type w) [LinearOrder ι]
variable (b : Module.Basis ι R L)

/-- Total degree of an exponent vector. -/
def exponentDegree (e : ι →₀ ℕ) : ℕ :=
  e.sum fun _ n ↦ n

theorem toFinsupp_cons (i : ι) (is : List ι) :
    Multiset.toFinsupp ((i :: is : List ι) : Multiset ι) =
      Finsupp.single i 1 + Multiset.toFinsupp (is : Multiset ι) := by
  rw [show ((i :: is : List ι) : Multiset ι) = {i} + (is : Multiset ι) by rfl,
    Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

/--
One Cartan--Eilenberg recursion step on a monomial, relative to operators already constructed in
lower degree.
-/
noncomputable def cartanMonomialStep
    (previous : L →ₗ[R] Module.End R (MvPolynomial ι R))
    (i : ι) (e : ι →₀ ℕ) : MvPolynomial ι R :=
  match (Finsupp.toMultiset e).sort (· ≤ ·) with
  | [] => MvPolynomial.X i
  | j :: js =>
      if i ≤ j then
        MvPolynomial.monomial (Finsupp.single i 1 + e) 1
      else
        let tail : ι →₀ ℕ := Multiset.toFinsupp (js : Multiset ι)
        MvPolynomial.monomial (Finsupp.single i 1 + e) 1 +
          previous (b j)
            (previous (b i) (MvPolynomial.monomial tail 1) -
              MvPolynomial.monomial (Finsupp.single i 1 + tail) 1) +
          previous ⁅b i, b j⁆ (MvPolynomial.monomial tail 1)

/-- Extend `cartanMonomialStep` linearly in the polynomial argument. -/
noncomputable def cartanStepBasis
    (previous : L →ₗ[R] Module.End R (MvPolynomial ι R))
    (i : ι) : Module.End R (MvPolynomial ι R) :=
  Finsupp.linearCombination R (cartanMonomialStep R L ι b previous i)

/-- Extend one recursion step linearly from basis elements to arbitrary elements of `L`. -/
noncomputable def cartanStep
    (previous : L →ₗ[R] Module.End R (MvPolynomial ι R)) :
    L →ₗ[R] Module.End R (MvPolynomial ι R) :=
  (Finsupp.linearCombination R (cartanStepBasis R L ι b previous)).comp b.repr.toLinearMap

/-- The finite Cartan--Eilenberg actions, constructed by recursion on polynomial degree. -/
noncomputable def cartanStage : ℕ → L →ₗ[R] Module.End R (MvPolynomial ι R)
  | 0 => cartanStep R L ι b 0
  | n + 1 => cartanStep R L ι b (cartanStage n)

/-- The action of a basis element, using the stage matching each input monomial's degree. -/
noncomputable def cartanActionBasis (i : ι) : Module.End R (MvPolynomial ι R) :=
  Finsupp.linearCombination R fun e ↦
    cartanStage R L ι b (exponentDegree ι e) (b i) (MvPolynomial.monomial e 1)

/-- The candidate Cartan--Eilenberg action, linear in both `L` and the polynomial argument. -/
noncomputable def cartanAction : L →ₗ[R] Module.End R (MvPolynomial ι R) :=
  (Finsupp.linearCombination R (cartanActionBasis R L ι b)).comp b.repr.toLinearMap

@[simp]
theorem cartanStep_basis_monomial
    (previous : L →ₗ[R] Module.End R (MvPolynomial ι R))
    (i : ι) (e : ι →₀ ℕ) (r : R) :
    cartanStep R L ι b previous (b i) (MvPolynomial.monomial e r) =
      r • cartanMonomialStep R L ι b previous i e := by
  simp only [cartanStep, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Module.Basis.repr_self, Finsupp.linearCombination_single, one_smul, cartanStepBasis]
  rw [← MvPolynomial.single_eq_monomial]
  exact Finsupp.linearCombination_single R r e

theorem cartanStage_eq_step (n : ℕ) :
    cartanStage R L ι b n =
      cartanStep R L ι b (if n = 0 then 0 else cartanStage R L ι b (n - 1)) := by
  cases n with
  | zero => rfl
  | succ n => simp [cartanStage]

@[simp]
theorem cartanAction_basis_monomial (i : ι) (e : ι →₀ ℕ) (r : R) :
    cartanAction R L ι b (b i) (MvPolynomial.monomial e r) =
      r • cartanStage R L ι b (exponentDegree ι e) (b i)
        (MvPolynomial.monomial e 1) := by
  simp only [cartanAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Module.Basis.repr_self, Finsupp.linearCombination_single, one_smul, cartanActionBasis]
  rw [← MvPolynomial.single_eq_monomial]
  exact Finsupp.linearCombination_single R r e

/--
Every finite stage has the required leading action when prepending a variable preserves order.
-/
theorem cartanStage_basis_orderedList (n : ℕ) (i : ι) (is : List ι)
    (his : is.Pairwise (· ≤ ·)) (hi : ∀ j ∈ is, i ≤ j) :
    cartanStage R L ι b n (b i)
        (MvPolynomial.monomial (Multiset.toFinsupp (is : Multiset ι)) 1) =
      MvPolynomial.monomial (Multiset.toFinsupp ((i :: is : List ι) : Multiset ι)) 1 := by
  rw [cartanStage_eq_step, cartanStep_basis_monomial, one_smul]
  unfold cartanMonomialStep
  have hsort :
      (Finsupp.toMultiset (Multiset.toFinsupp (is : Multiset ι))).sort (· ≤ ·) = is := by
    simp only [Multiset.toFinsupp_toMultiset, Multiset.coe_sort]
    exact List.mergeSort_eq_self _ his
  rw [hsort]
  cases is with
  | nil => simp [MvPolynomial.X]
  | cons j js =>
      simp only
      rw [if_pos (hi j (by simp))]
      rw [toFinsupp_cons (i := i) (is := j :: js),
        toFinsupp_cons (i := j) (is := js)]

/-- The assembled action has the same ordered-leading-term rule. -/
theorem cartanAction_basis_orderedList (i : ι) (is : List ι)
    (his : is.Pairwise (· ≤ ·)) (hi : ∀ j ∈ is, i ≤ j) :
    cartanAction R L ι b (b i)
        (MvPolynomial.monomial (Multiset.toFinsupp (is : Multiset ι)) 1) =
      MvPolynomial.monomial (Multiset.toFinsupp ((i :: is : List ι) : Multiset ι)) 1 := by
  rw [cartanAction_basis_monomial, one_smul]
  exact cartanStage_basis_orderedList R L ι b _ i is his hi

/-- Every finite stage sends the vacuum to the degree-one polynomial carrying the coordinates. -/
theorem cartanStage_apply_one (n : ℕ) (x : L) :
    cartanStage R L ι b n x 1 = basisPolynomial R L ι b x := by
  let lhs : L →ₗ[R] MvPolynomial ι R :=
    (LinearMap.applyₗ (1 : MvPolynomial ι R)).comp (cartanStage R L ι b n)
  change lhs x = basisPolynomial R L ι b x
  have h : lhs = basisPolynomial R L ι b := by
    apply b.ext
    intro i
    simpa [lhs] using
      cartanStage_basis_orderedList R L ι b n i [] (by simp) (by simp)
  exact LinearMap.congr_fun h x

/-- The assembled candidate action also sends `1` to the coordinate polynomial. -/
theorem cartanAction_apply_one (x : L) :
    cartanAction R L ι b x 1 = basisPolynomial R L ι b x := by
  let lhs : L →ₗ[R] MvPolynomial ι R :=
    (LinearMap.applyₗ (1 : MvPolynomial ι R)).comp (cartanAction R L ι b)
  change lhs x = basisPolynomial R L ι b x
  have h : lhs = basisPolynomial R L ι b := by
    apply b.ext
    intro i
    simpa [lhs] using cartanAction_basis_orderedList R L ι b i [] (by simp) (by simp)
  exact LinearMap.congr_fun h x

/-- The explicit first-degree action; this is the first nontrivial recursion step. -/
theorem cartanAction_basis_X (i j : ι) :
    cartanAction R L ι b (b i) (MvPolynomial.X j) =
      MvPolynomial.X i * MvPolynomial.X j +
        if i ≤ j then 0 else basisPolynomial R L ι b ⁅b i, b j⁆ := by
  rw [MvPolynomial.X, cartanAction_basis_monomial, one_smul]
  by_cases hij : i ≤ j
  · simp [exponentDegree, cartanStage, cartanStep_basis_monomial,
      cartanMonomialStep, hij, MvPolynomial.X, MvPolynomial.monomial_mul]
  · have hzero (x : L) :
        cartanStep R L ι b 0 x 1 = basisPolynomial R L ι b x :=
      cartanStage_apply_one R L ι b 0 x
    simp [exponentDegree, cartanStage, cartanStep_basis_monomial,
      cartanMonomialStep, hij, hzero, MvPolynomial.X,
      MvPolynomial.monomial_mul]

/-- The candidate action satisfies the representation identity on `1` for basis elements. -/
theorem cartanAction_lie_basis_apply_one (i j : ι) :
    cartanAction R L ι b ⁅b i, b j⁆ 1 =
      ⁅cartanAction R L ι b (b i), cartanAction R L ι b (b j)⁆ 1 := by
  rw [cartanAction_apply_one]
  change basisPolynomial R L ι b ⁅b i, b j⁆ =
    (cartanAction R L ι b (b i) * cartanAction R L ι b (b j) -
      cartanAction R L ι b (b j) * cartanAction R L ι b (b i)) 1
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    cartanAction_apply_one, cartanAction_apply_one, basisPolynomial_basis,
    basisPolynomial_basis, cartanAction_basis_X, cartanAction_basis_X]
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have : i = j := le_antisymm hij hji
      subst j
      simp
    · simp [hij, hji, mul_comm, ← map_neg, lie_skew]
  · have hji : j ≤ i := le_of_not_ge hij
    simp [hij, hji, mul_comm]

/-- The two sides of the representation identity on the vacuum, bundled as a bilinear map. -/
noncomputable def cartanLieVacuumLeft :
    L →ₗ[R] L →ₗ[R] MvPolynomial ι R :=
  LinearMap.mk₂ R (fun x y ↦ cartanAction R L ι b ⁅x, y⁆ 1)
    (by intros; simp [add_lie])
    (by intros; simp)
    (by intros; simp [lie_add])
    (by intros; simp)

/-- The commutator side of the representation identity on the vacuum. -/
noncomputable def cartanLieVacuumRight :
    L →ₗ[R] L →ₗ[R] MvPolynomial ι R :=
  LinearMap.mk₂ R
    (fun x y ↦ ⁅cartanAction R L ι b x, cartanAction R L ι b y⁆ 1)
    (by intros; simp [add_lie])
    (by intros; simp; module)
    (by intros; simp [lie_add])
    (by intros; simp; module)

/-- The candidate action satisfies the Lie-representation identity on the vacuum `1`. -/
theorem cartanAction_lie_apply_one (x y : L) :
    cartanAction R L ι b ⁅x, y⁆ 1 =
      ⁅cartanAction R L ι b x, cartanAction R L ι b y⁆ 1 := by
  have h : cartanLieVacuumLeft R L ι b = cartanLieVacuumRight R L ι b := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    exact cartanAction_lie_basis_apply_one R L ι b i j
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- The product of Cartan operators belonging to a basis word. -/
noncomputable def cartanBasisWordAction (is : List ι) :
    Module.End R (MvPolynomial ι R) :=
  (is.map fun i ↦ cartanAction R L ι b (b i)).prod

@[simp]
theorem cartanBasisWordAction_nil :
    cartanBasisWordAction R L ι b [] = 1 :=
  rfl

@[simp]
theorem cartanBasisWordAction_cons (i : ι) (is : List ι) :
    cartanBasisWordAction R L ι b (i :: is) =
      cartanAction R L ι b (b i) * cartanBasisWordAction R L ι b is := by
  simp [cartanBasisWordAction]

/-- An ordered product of the candidate operators sends `1` to its commutative monomial. -/
theorem cartanBasisWordAction_apply_one (is : List ι) (his : is.Pairwise (· ≤ ·)) :
    cartanBasisWordAction R L ι b is 1 =
      MvPolynomial.monomial (Multiset.toFinsupp (is : Multiset ι)) 1 := by
  induction is with
  | nil => simp [cartanBasisWordAction]
  | cons i is ih =>
      have hcons := List.pairwise_cons.mp his
      rw [cartanBasisWordAction_cons, Module.End.mul_apply, ih hcons.2]
      exact cartanAction_basis_orderedList R L ι b i is hcons.2 hcons.1

/-- The ordered exponent-vector version of `cartanBasisWordAction_apply_one`. -/
theorem cartanBasisWordAction_sortedExponent_apply_one (e : ι →₀ ℕ) :
    cartanBasisWordAction R L ι b ((Finsupp.toMultiset e).sort (· ≤ ·)) 1 =
      MvPolynomial.monomial e 1 := by
  rw [cartanBasisWordAction_apply_one R L ι b _ (Multiset.pairwise_sort _ _)]
  congr 2
  rw [Multiset.sort_eq, Finsupp.toMultiset_toFinsupp]

/-- The one remaining compatibility assertion for the candidate action. -/
def CartanActionLieCompatible : Prop :=
  ∀ x y : L,
    cartanAction R L ι b ⁅x, y⁆ =
      ⁅cartanAction R L ι b x, cartanAction R L ι b y⁆

/-- Upgrade the candidate action to a Lie representation once the Jacobi calculation is supplied. -/
noncomputable def cartanLieHom (h : CartanActionLieCompatible R L ι b) :
    LieHom R L (Module.End R (MvPolynomial ι R)) :=
  { cartanAction R L ι b with
    map_lie' := fun {x y} ↦ h x y }

@[simp]
theorem cartanLieHom_apply (h : CartanActionLieCompatible R L ι b) (x : L) :
    cartanLieHom R L ι b h x = cartanAction R L ι b x :=
  rfl

/-- Package the Cartan construction as the exact representation needed for PBW. -/
noncomputable def cartanTriangularRepresentation
    (h : CartanActionLieCompatible R L ι b) : TriangularRepresentation R L ι b where
  toLieHom := cartanLieHom R L ι b h
  orderedMonomial_apply_one e := by
    have hgen (i : ι) :
        UniversalEnvelopingAlgebra.lift R (cartanLieHom R L ι b h)
            (UniversalEnvelopingAlgebra.ι R (b i)) =
          cartanAction R L ι b (b i) := by
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      rfl
    unfold orderedMonomial
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def]
    simp_rw [hgen]
    change cartanBasisWordAction R L ι b ((Finsupp.toMultiset e).sort (· ≤ ·)) 1 =
      MvPolynomial.monomial e 1
    exact cartanBasisWordAction_sortedExponent_apply_one R L ι b e

/-- The Jacobi compatibility of the constructed action is the final input needed for PBW. -/
theorem freeModulePBW_of_cartanAction_lie
    (h : CartanActionLieCompatible R L ι b) : FreeModulePBW R L ι b :=
  (cartanTriangularRepresentation R L ι b h).freeModulePBW

/-- The same compatibility also gives the canonical embedding `L → U(L)`. -/
theorem canonicalMap_injective_of_cartanAction_lie
    (h : CartanActionLieCompatible R L ι b) :
    Function.Injective (UniversalEnvelopingAlgebra.ι R : L → UEA R L) :=
  (cartanTriangularRepresentation R L ι b h).canonicalMap_injective

end LieRings.PBW
