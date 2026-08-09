import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Data.PNat.Basic

/-!
# Associated graded Lie algebras

This file constructs the external associated graded Lie algebra of a descending
Lie filtration indexed by the positive natural numbers.
-/

namespace LieRings

universe u v

/-- A descending filtration of a Lie algebra whose bracket adds filtration degrees. -/
structure LieFiltration (R : Type u) (L : Type v)
    [CommRing R] [LieRing L] [LieAlgebra R L] where
  term : ℕ+ → LieIdeal R L
  antitone' : Antitone term
  lie_le' (i j : ℕ+) : ⁅term i, term j⁆ ≤ term (i + j)

namespace LieFiltration

variable {R : Type u} {L : Type v}
variable [CommRing R] [LieRing L] [LieAlgebra R L]

instance : CoeFun (LieFiltration R L) (fun _ ↦ ℕ+ → LieIdeal R L) :=
  ⟨LieFiltration.term⟩

theorem antitone (F : LieFiltration R L) : Antitone F :=
  F.antitone'

theorem bracket_mem (F : LieFiltration R L) {i j : ℕ+} {x y : L}
    (hx : x ∈ F i) (hy : y ∈ F j) : ⁅x, y⁆ ∈ F (i + j) := by
  have h := F.lie_le' i j
  rw [LieSubmodule.lie_le_iff] at h
  exact h x hx y hy

/-- The next filtration term, regarded as a submodule of the current term. -/
def nextSubmodule (F : LieFiltration R L) (n : ℕ+) : Submodule R (F n) :=
  (F (n + 1)).toSubmodule.comap (F n).subtype

/-- The degree-`n` component `Fₙ/Fₙ₊₁` of the associated graded Lie algebra. -/
def GradedPiece (F : LieFiltration R L) (n : ℕ+) :=
  (F n) ⧸ F.nextSubmodule n

instance (F : LieFiltration R L) (n : ℕ+) : AddCommGroup (F.GradedPiece n) :=
  inferInstanceAs (AddCommGroup ((F n) ⧸ F.nextSubmodule n))

instance (F : LieFiltration R L) (n : ℕ+) : Module R (F.GradedPiece n) :=
  inferInstanceAs (Module R ((F n) ⧸ F.nextSubmodule n))

/-- The class of an element of a filtration term in the corresponding graded piece. -/
def toGradedPiece (F : LieFiltration R L) (n : ℕ+) : F n →ₗ[R] F.GradedPiece n :=
  (F.nextSubmodule n).mkQ

/-- The bracket induced between two successive filtration quotients. -/
def gradedBracket (F : LieFiltration R L) {i j : ℕ+} :
    F.GradedPiece i → F.GradedPiece j → F.GradedPiece (i + j) := by
  intro x y
  apply Quotient.liftOn₂' x y
    (fun x y ↦ F.toGradedPiece (i + j) ⟨⁅(x : L), (y : L)⁆,
      F.bracket_mem x.property y.property⟩)
  intro x₁ y₁ x₂ y₂ hx hy
  apply (Submodule.Quotient.eq (F.nextSubmodule (i + j))).2
  rw [Submodule.quotientRel_def] at hx hy
  change ⁅(x₁ : L), (y₁ : L)⁆ - ⁅(x₂ : L), (y₂ : L)⁆ ∈ F ((i + j) + 1)
  rw [show ⁅(x₁ : L), (y₁ : L)⁆ - ⁅(x₂ : L), (y₂ : L)⁆ =
      ⁅(x₁ : L), (y₁ : L) - y₂⁆ + ⁅(x₁ : L) - x₂, (y₂ : L)⁆ by
    simp [-lie_skew, sub_eq_add_neg, add_assoc]]
  apply (F ((i + j) + 1)).add_mem
  · have hy' : (y₁ : L) - y₂ ∈ F (j + 1) := hy
    simpa [add_assoc] using F.bracket_mem x₁.property hy'
  · have hx' : (x₁ : L) - x₂ ∈ F (i + 1) := hx
    simpa [add_assoc, add_left_comm, add_comm] using F.bracket_mem hx' y₂.property

@[simp]
theorem gradedBracket_toGradedPiece (F : LieFiltration R L) {i j : ℕ+}
    (x : F i) (y : F j) :
    F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j y) =
      F.toGradedPiece (i + j)
        ⟨⁅(x : L), (y : L)⁆, F.bracket_mem x.property y.property⟩ :=
  by
    change Quotient.liftOn₂' (Quotient.mk'' x) (Quotient.mk'' y) _ _ = _
    rw [Quotient.liftOn₂'_mk'']

private theorem toGradedPiece_heq (F : LieFiltration R L) {i j : ℕ+}
    (h : i = j) (x : F i) (y : F j) (hxy : (x : L) = y) :
    HEq (F.toGradedPiece i x) (F.toGradedPiece j y) := by
  subst j
  have : x = y := Subtype.ext hxy
  subst y
  rfl

private theorem of_toGradedPiece_eq (F : LieFiltration R L) {i j : ℕ+}
    (h : i = j) (x : F i) (y : F j) (hxy : (x : L) = y) :
    DirectSum.of F.GradedPiece i (F.toGradedPiece i x) =
      DirectSum.of F.GradedPiece j (F.toGradedPiece j y) := by
  apply DirectSum.of_eq_of_gradedMonoid_eq
  exact Sigma.ext h (F.toGradedPiece_heq h x y hxy)

private theorem gradedBracket_zero_right (F : LieFiltration R L) {i j : ℕ+}
    (x : F.GradedPiece i) : F.gradedBracket x (0 : F.GradedPiece j) = 0 := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    change F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j 0) = 0
    rw [F.gradedBracket_toGradedPiece]
    rw [show (⟨⁅(x : L), (0 : F j)⁆, F.bracket_mem x.property (F j).zero_mem⟩ :
        F (i + j)) = 0 by ext; simp, map_zero]

private theorem gradedBracket_zero_left (F : LieFiltration R L) {i j : ℕ+}
    (y : F.GradedPiece j) : F.gradedBracket (0 : F.GradedPiece i) y = 0 := by
  induction y using Quotient.inductionOn' with
  | _ y =>
    change F.gradedBracket (F.toGradedPiece i 0) (F.toGradedPiece j y) = 0
    rw [F.gradedBracket_toGradedPiece]
    rw [← map_zero (F.toGradedPiece (i + j))]
    congr 1
    ext
    exact zero_lie _

private theorem gradedBracket_add_right (F : LieFiltration R L) {i j : ℕ+}
    (x : F.GradedPiece i) (y z : F.GradedPiece j) :
    F.gradedBracket x (y + z) = F.gradedBracket x y + F.gradedBracket x z := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      induction z using Quotient.inductionOn' with
      | _ z =>
        change F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j (y + z)) =
          F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j y) +
            F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j z)
        rw [F.gradedBracket_toGradedPiece, F.gradedBracket_toGradedPiece,
          F.gradedBracket_toGradedPiece, ← map_add]
        congr 1
        ext
        exact lie_add _ _ _

private theorem gradedBracket_add_left (F : LieFiltration R L) {i j : ℕ+}
    (x y : F.GradedPiece i) (z : F.GradedPiece j) :
    F.gradedBracket (x + y) z = F.gradedBracket x z + F.gradedBracket y z := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      induction z using Quotient.inductionOn' with
      | _ z =>
        change F.gradedBracket (F.toGradedPiece i (x + y)) (F.toGradedPiece j z) =
          F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j z) +
            F.gradedBracket (F.toGradedPiece i y) (F.toGradedPiece j z)
        rw [F.gradedBracket_toGradedPiece, F.gradedBracket_toGradedPiece,
          F.gradedBracket_toGradedPiece, ← map_add]
        congr 1
        ext
        exact add_lie _ _ _

instance (F : LieFiltration R L) :
    DirectSum.GNonUnitalNonAssocSemiring F.GradedPiece where
  mul := F.gradedBracket
  mul_zero := F.gradedBracket_zero_right
  zero_mul := F.gradedBracket_zero_left
  mul_add := F.gradedBracket_add_right
  add_mul := F.gradedBracket_add_left

/-- The associated graded module `⨁ n > 0, Fₙ/Fₙ₊₁`. -/
abbrev AssociatedGraded (F : LieFiltration R L) : Type v :=
  DirectSum ℕ+ (fun n ↦ F.GradedPiece n)

private theorem associatedGraded_of_mul_skew (F : LieFiltration R L) {i j : ℕ+}
    (x : F.GradedPiece i) (y : F.GradedPiece j) :
    DirectSum.of F.GradedPiece i x * DirectSum.of F.GradedPiece j y =
      -(DirectSum.of F.GradedPiece j y * DirectSum.of F.GradedPiece i x) := by
  rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
  change DirectSum.of F.GradedPiece (i + j) (F.gradedBracket x y) =
    -(DirectSum.of F.GradedPiece (j + i) (F.gradedBracket y x))
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      change DirectSum.of F.GradedPiece (i + j)
          (F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j y)) =
        -(DirectSum.of F.GradedPiece (j + i)
          (F.gradedBracket (F.toGradedPiece j y) (F.toGradedPiece i x)))
      rw [F.gradedBracket_toGradedPiece, F.gradedBracket_toGradedPiece,
        ← map_neg, ← map_neg]
      apply DirectSum.of_eq_of_gradedMonoid_eq
      apply Sigma.ext (add_comm i j)
      refine F.toGradedPiece_heq (add_comm i j)
        ⟨⁅(x : L), (y : L)⁆, F.bracket_mem x.property y.property⟩
        (-⟨⁅(y : L), (x : L)⁆, F.bracket_mem y.property x.property⟩) ?_
      exact (lie_skew _ _).symm

private theorem associatedGraded_mul_skew (F : LieFiltration R L)
    (x y : F.AssociatedGraded) : x * y = -(y * x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j y => exact F.associatedGraded_of_mul_skew x y
    | add y z hy hz => simp only [mul_add, add_mul, hy, hz, neg_add_rev, add_comm]
  | add x y hx hy => simp only [add_mul, mul_add, hx, hy, neg_add_rev, add_comm]

private theorem associatedGraded_piece_mul_self (F : LieFiltration R L) {i : ℕ+}
    (x : F.GradedPiece i) : F.gradedBracket x x = 0 := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    change F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece i x) = 0
    rw [F.gradedBracket_toGradedPiece,
      ← (F.toGradedPiece (i + i)).map_zero]
    congr 1
    ext
    exact lie_self _

private theorem associatedGraded_mul_self (F : LieFiltration R L)
    (x : F.AssociatedGraded) : x * x = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [DirectSum.of_mul_of]
    change DirectSum.of F.GradedPiece (i + i) (F.gradedBracket x x) = 0
    rw [F.associatedGraded_piece_mul_self, map_zero]
  | add x y hx hy =>
    rw [add_mul, mul_add, mul_add, hx, hy, zero_add, add_zero,
      F.associatedGraded_mul_skew y x]
    simp

private theorem associatedGraded_of_mul_leibniz (F : LieFiltration R L)
    {i j k : ℕ+} (x : F.GradedPiece i) (y : F.GradedPiece j)
    (z : F.GradedPiece k) :
    DirectSum.of F.GradedPiece i x *
        (DirectSum.of F.GradedPiece j y * DirectSum.of F.GradedPiece k z) =
      (DirectSum.of F.GradedPiece i x * DirectSum.of F.GradedPiece j y) *
          DirectSum.of F.GradedPiece k z +
        DirectSum.of F.GradedPiece j y *
          (DirectSum.of F.GradedPiece i x * DirectSum.of F.GradedPiece k z) := by
  simp only [DirectSum.of_mul_of]
  change DirectSum.of F.GradedPiece (i + (j + k))
      (F.gradedBracket x (F.gradedBracket y z)) =
    DirectSum.of F.GradedPiece ((i + j) + k)
        (F.gradedBracket (F.gradedBracket x y) z) +
      DirectSum.of F.GradedPiece (j + (i + k))
        (F.gradedBracket y (F.gradedBracket x z))
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      induction z using Quotient.inductionOn' with
      | _ z =>
        change DirectSum.of F.GradedPiece (i + (j + k))
            (F.gradedBracket (F.toGradedPiece i x)
              (F.gradedBracket (F.toGradedPiece j y) (F.toGradedPiece k z))) =
          DirectSum.of F.GradedPiece ((i + j) + k)
              (F.gradedBracket
                (F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j y))
                (F.toGradedPiece k z)) +
            DirectSum.of F.GradedPiece (j + (i + k))
              (F.gradedBracket (F.toGradedPiece j y)
                (F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece k z)))
        rw [F.gradedBracket_toGradedPiece, F.gradedBracket_toGradedPiece,
          F.gradedBracket_toGradedPiece, F.gradedBracket_toGradedPiece,
          F.gradedBracket_toGradedPiece, F.gradedBracket_toGradedPiece]
        let lhs : F (i + (j + k)) :=
          ⟨⁅(x : L), ⁅(y : L), (z : L)⁆⁆, F.bracket_mem x.property
            (F.bracket_mem y.property z.property)⟩
        let src₁ : F ((i + j) + k) :=
          ⟨⁅⁅(x : L), (y : L)⁆, (z : L)⁆,
            F.bracket_mem (F.bracket_mem x.property y.property) z.property⟩
        let src₂ : F (j + (i + k)) :=
          ⟨⁅(y : L), ⁅(x : L), (z : L)⁆⁆,
            F.bracket_mem y.property (F.bracket_mem x.property z.property)⟩
        let rhs₁ : F (i + (j + k)) :=
          ⟨⁅⁅(x : L), (y : L)⁆, (z : L)⁆, by
            simpa [add_assoc] using
              F.bracket_mem (F.bracket_mem x.property y.property) z.property⟩
        let rhs₂ : F (i + (j + k)) :=
          ⟨⁅(y : L), ⁅(x : L), (z : L)⁆⁆, by
            simpa [add_assoc, add_left_comm, add_comm] using
              F.bracket_mem y.property (F.bracket_mem x.property z.property)⟩
        change DirectSum.of F.GradedPiece (i + (j + k))
            (F.toGradedPiece _ lhs) =
          DirectSum.of F.GradedPiece ((i + j) + k) (F.toGradedPiece _ src₁) +
            DirectSum.of F.GradedPiece (j + (i + k)) (F.toGradedPiece _ src₂)
        rw [F.of_toGradedPiece_eq (add_assoc i j k) src₁ rhs₁ rfl,
          F.of_toGradedPiece_eq (by
            simp only [add_left_comm]) src₂ rhs₂ rfl,
          ← map_add, ← map_add]
        apply congrArg (DirectSum.of F.GradedPiece (i + (j + k)))
        apply congrArg (F.toGradedPiece (i + (j + k)))
        apply Subtype.ext
        exact leibniz_lie _ _ _

private theorem associatedGraded_mul_leibniz (F : LieFiltration R L)
    (x y z : F.AssociatedGraded) :
    x * (y * z) = (x * y) * z + y * (x * z) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      induction z using DirectSum.induction_on with
      | zero => simp
      | of k z => exact F.associatedGraded_of_mul_leibniz x y z
      | add z w hz hw => simp only [mul_add, hz, hw]; abel
    | add y z hy hz => simp only [add_mul, mul_add, hy, hz]; abel
  | add x y hx hy => simp only [add_mul, mul_add, hx, hy]; abel

instance (F : LieFiltration R L) : LieRing F.AssociatedGraded where
  bracket := (· * ·)
  add_lie := add_mul
  lie_add := mul_add
  lie_self := F.associatedGraded_mul_self
  leibniz_lie := F.associatedGraded_mul_leibniz

private theorem gradedBracket_smul_right (F : LieFiltration R L) {i j : ℕ+}
    (r : R) (x : F.GradedPiece i) (y : F.GradedPiece j) :
    F.gradedBracket x (r • y) = r • F.gradedBracket x y := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      change F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j (r • y)) =
        r • F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j y)
      rw [F.gradedBracket_toGradedPiece, F.gradedBracket_toGradedPiece, ← map_smul]
      congr 1
      ext
      exact lie_smul _ _ _

private theorem associatedGraded_mul_smul_right (F : LieFiltration R L)
    (r : R) (x y : F.AssociatedGraded) : x * (r • y) = r • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [← DirectSum.of_smul, DirectSum.of_mul_of, DirectSum.of_mul_of]
      change DirectSum.of F.GradedPiece (i + j) (F.gradedBracket x (r • y)) =
        r • DirectSum.of F.GradedPiece (i + j) (F.gradedBracket x y)
      rw [F.gradedBracket_smul_right, DirectSum.of_smul]
    | add y z hy hz => simp only [smul_add, mul_add, hy, hz]
  | add x y hx hy => simp only [add_mul, smul_add, hx, hy]

instance (F : LieFiltration R L) : LieAlgebra R F.AssociatedGraded where
  lie_smul := F.associatedGraded_mul_smul_right

/-- An ideal in an external direct sum is graded if it contains every homogeneous component of
each of its elements. Mathlib has no corresponding predicate for externally graded Lie algebras. -/
def IsGradedIdeal (F : LieFiltration R L) (I : LieIdeal R F.AssociatedGraded) : Prop :=
  ∀ ⦃x : F.AssociatedGraded⦄, x ∈ I → ∀ n,
    DirectSum.of F.GradedPiece n (x n) ∈ I

/-- The map on one graded piece induced by an inclusion of filtrations. -/
def inclusionPiece (F G : LieFiltration R L) (h : ∀ n, F n ≤ G n) (n : ℕ+) :
    F.GradedPiece n →ₗ[R] G.GradedPiece n :=
  (F.nextSubmodule n).liftQ
    ((G.toGradedPiece n).comp
      ({
        toFun := fun x ↦ ⟨x, h n x.property⟩
        map_add' := by intro x y; ext; rfl
        map_smul' := by intro r x; ext; rfl
      } : F n →ₗ[R] G n)) <| by
      intro x hx
      rw [LinearMap.mem_ker]
      change G.toGradedPiece n ⟨x, h n x.property⟩ = 0
      exact (Submodule.Quotient.mk_eq_zero (G.nextSubmodule n)).2 (h (n + 1) hx)

@[simp]
theorem inclusionPiece_toGradedPiece (F G : LieFiltration R L)
    (h : ∀ n, F n ≤ G n) (n : ℕ+) (x : F n) :
    inclusionPiece F G h n (F.toGradedPiece n x) =
      G.toGradedPiece n ⟨x, h n x.property⟩ := by
  rfl

private theorem inclusionPiece_bracket (F G : LieFiltration R L)
    (h : ∀ n, F n ≤ G n) {i j : ℕ+}
    (x : F.GradedPiece i) (y : F.GradedPiece j) :
    inclusionPiece F G h (i + j) (F.gradedBracket x y) =
      G.gradedBracket (inclusionPiece F G h i x) (inclusionPiece F G h j y) := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      change inclusionPiece F G h (i + j)
          (F.gradedBracket (F.toGradedPiece i x) (F.toGradedPiece j y)) =
        G.gradedBracket
          (inclusionPiece F G h i (F.toGradedPiece i x))
          (inclusionPiece F G h j (F.toGradedPiece j y))
      rw [F.gradedBracket_toGradedPiece, inclusionPiece_toGradedPiece,
        inclusionPiece_toGradedPiece, inclusionPiece_toGradedPiece,
        G.gradedBracket_toGradedPiece]

/-- The degree-preserving linear map of associated gradeds induced by `Fₙ ≤ Gₙ`. -/
def inclusionLinear (F G : LieFiltration R L) (h : ∀ n, F n ≤ G n) :
    F.AssociatedGraded →ₗ[R] G.AssociatedGraded :=
  DirectSum.toModule R ℕ+ G.AssociatedGraded fun n ↦
    (DirectSum.lof R ℕ+ G.GradedPiece n).comp (inclusionPiece F G h n)

@[simp]
theorem inclusionLinear_of (F G : LieFiltration R L) (h : ∀ n, F n ≤ G n)
    (n : ℕ+) (x : F.GradedPiece n) :
    inclusionLinear F G h (DirectSum.of F.GradedPiece n x) =
      DirectSum.of G.GradedPiece n (inclusionPiece F G h n x) := by
  change (DirectSum.toModule R ℕ+ G.AssociatedGraded fun n ↦
      (DirectSum.lof R ℕ+ G.GradedPiece n).comp (inclusionPiece F G h n))
      (DirectSum.lof R ℕ+ F.GradedPiece n x) = _
  rw [DirectSum.toModule_lof]
  rfl

@[simp]
theorem inclusionLinear_apply (F G : LieFiltration R L) (h : ∀ n, F n ≤ G n)
    (x : F.AssociatedGraded) (n : ℕ+) :
    inclusionLinear F G h x n = inclusionPiece F G h n (x n) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [inclusionLinear_of]
    by_cases hin : i = n
    · subst n
      simp
    · simp [DirectSum.of_apply, hin]
  | add x y hx hy => simp [map_add, hx, hy]

/-- The canonical Lie homomorphism between associated gradeds of nested filtrations. -/
def inclusionHom (F G : LieFiltration R L) (h : ∀ n, F n ≤ G n) :
    F.AssociatedGraded →ₗ⁅R⁆ G.AssociatedGraded where
  __ := inclusionLinear F G h
  map_lie' := by
    intro x y
    change inclusionLinear F G h (x * y) =
      inclusionLinear F G h x * inclusionLinear F G h y
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | of j y =>
        rw [DirectSum.of_mul_of, inclusionLinear_of, inclusionLinear_of,
          inclusionLinear_of, DirectSum.of_mul_of]
        change DirectSum.of G.GradedPiece (i + j)
            (inclusionPiece F G h (i + j) (F.gradedBracket x y)) =
          DirectSum.of G.GradedPiece (i + j)
            (G.gradedBracket (inclusionPiece F G h i x) (inclusionPiece F G h j y))
        rw [F.inclusionPiece_bracket G h]
      | add y z hy hz => simp only [mul_add, map_add, hy, hz]
    | add x y hx hy => simp only [add_mul, map_add, hx, hy]

end LieFiltration

end LieRings
