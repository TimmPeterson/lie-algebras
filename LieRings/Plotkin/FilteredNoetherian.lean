import Mathlib.Algebra.DirectSum.Ring
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Associated rings of exhaustive natural filtrations

This file contains the filtered-ring infrastructure used by the Plotkin argument.  Mathlib has
the predicate `IsRingFiltration`, but currently has no external associated-graded ring or the
Noetherian transfer needed here.  We keep the construction over `ℤ`, which is exactly the case
needed for integral enveloping algebras.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

/-- An exhaustive increasing filtration of a ring by additive subgroups, compatible with
multiplication. -/
structure NatRingFiltration (A : Type u) [Ring A] where
  term : ℕ → Submodule ℤ A
  monotone' : Monotone term
  one_mem : (1 : A) ∈ term 0
  mul_mem' : ∀ {m n : ℕ} {x y : A}, x ∈ term m → y ∈ term n → x * y ∈ term (m + n)
  exhaustive : ∀ x : A, ∃ n, x ∈ term n

namespace NatRingFiltration

variable {A : Type u} [Ring A]

instance : CoeFun (NatRingFiltration A) (fun _ ↦ ℕ → Submodule ℤ A) :=
  ⟨NatRingFiltration.term⟩

theorem monotone (F : NatRingFiltration A) : Monotone F := F.monotone'

theorem mul_mem (F : NatRingFiltration A) {m n : ℕ} {x y : A}
    (hx : x ∈ F m) (hy : y ∈ F n) : x * y ∈ F (m + n) :=
  F.mul_mem' hx hy

/-- The union of all preceding terms; for a natural filtration this is simply the predecessor
term, with zero in degree zero. -/
def previous (F : NatRingFiltration A) : ℕ → Submodule ℤ A
  | 0 => ⊥
  | n + 1 => F n

theorem previous_le (F : NatRingFiltration A) (n : ℕ) : F.previous n ≤ F n := by
  cases n with
  | zero => exact bot_le
  | succ n => exact F.monotone (Nat.le_succ n)

/-- The preceding filtration term, regarded inside the current term. -/
def previousIn (F : NatRingFiltration A) (n : ℕ) : Submodule ℤ (F n) :=
  (F.previous n).comap (F n).subtype

/-- Degree `n` of the associated graded ring. -/
abbrev GradedPiece (F : NatRingFiltration A) (n : ℕ) :=
  (F n) ⧸ F.previousIn n

/-- The class of a filtered element in its corresponding graded piece. -/
def toGradedPiece (F : NatRingFiltration A) (n : ℕ) :
    F n →ₗ[ℤ] F.GradedPiece n :=
  (F.previousIn n).mkQ

private theorem previous_mul_right (F : NatRingFiltration A) {m n : ℕ}
    {x y : A} (hx : x ∈ F.previous m) (hy : y ∈ F n) :
    x * y ∈ F.previous (m + n) := by
  cases m with
  | zero =>
      have hx0 : x = 0 := by simpa [previous] using hx
      subst x
      simp [previous]
  | succ m =>
      have hxy : x * y ∈ F (m + n) := F.mul_mem hx hy
      simpa [previous, Nat.succ_add] using hxy

private theorem previous_mul_left (F : NatRingFiltration A) {m n : ℕ}
    {x y : A} (hx : x ∈ F m) (hy : y ∈ F.previous n) :
    x * y ∈ F.previous (m + n) := by
  cases n with
  | zero =>
      have hy0 : y = 0 := by simpa [previous] using hy
      subst y
      simp [previous]
  | succ n =>
      have hxy : x * y ∈ F (m + n) := F.mul_mem hx hy
      simpa [previous, Nat.add_succ] using hxy

/-- Multiplication on homogeneous associated-graded pieces. -/
def gradedMul (F : NatRingFiltration A) {m n : ℕ} :
    F.GradedPiece m → F.GradedPiece n → F.GradedPiece (m + n) := by
  intro x y
  refine Quotient.liftOn₂' x y
    (fun x y ↦ F.toGradedPiece (m + n)
      ⟨(x : A) * (y : A), F.mul_mem x.property y.property⟩) ?_
  intro x₁ y₁ x₂ y₂ hx hy
  apply (Submodule.Quotient.eq (F.previousIn (m + n))).2
  rw [Submodule.quotientRel_def] at hx hy
  change (x₁ : A) - x₂ ∈ F.previous m at hx
  change (y₁ : A) - y₂ ∈ F.previous n at hy
  change (x₁ : A) * (y₁ : A) - (x₂ : A) * (y₂ : A) ∈ F.previous (m + n)
  rw [show (x₁ : A) * (y₁ : A) - (x₂ : A) * (y₂ : A) =
      (x₁ : A) * ((y₁ : A) - y₂) + ((x₁ : A) - x₂) * (y₂ : A) by
    noncomm_ring]
  exact (F.previous (m + n)).add_mem
    (F.previous_mul_left x₁.property hy)
    (F.previous_mul_right hx y₂.property)

@[simp]
theorem gradedMul_toGradedPiece (F : NatRingFiltration A) {m n : ℕ}
    (x : F m) (y : F n) :
    F.gradedMul (F.toGradedPiece m x) (F.toGradedPiece n y) =
      F.toGradedPiece (m + n) ⟨(x : A) * (y : A), F.mul_mem x.property y.property⟩ := by
  change Quotient.liftOn₂' (Quotient.mk'' x) (Quotient.mk'' y) _ _ = _
  rw [Quotient.liftOn₂'_mk'']

private theorem gradedMul_zero_right (F : NatRingFiltration A) {m n : ℕ}
    (x : F.GradedPiece m) : F.gradedMul x (0 : F.GradedPiece n) = 0 := by
  induction x using Quotient.inductionOn' with
  | _ x =>
      change F.gradedMul (F.toGradedPiece m x) (F.toGradedPiece n 0) = 0
      rw [F.gradedMul_toGradedPiece]
      rw [← map_zero (F.toGradedPiece (m + n))]
      congr 1
      ext
      exact mul_zero _

private theorem gradedMul_zero_left (F : NatRingFiltration A) {m n : ℕ}
    (y : F.GradedPiece n) : F.gradedMul (0 : F.GradedPiece m) y = 0 := by
  induction y using Quotient.inductionOn' with
  | _ y =>
      change F.gradedMul (F.toGradedPiece m 0) (F.toGradedPiece n y) = 0
      rw [F.gradedMul_toGradedPiece]
      rw [← map_zero (F.toGradedPiece (m + n))]
      congr 1
      ext
      exact zero_mul _

private theorem gradedMul_add_right (F : NatRingFiltration A) {m n : ℕ}
    (x : F.GradedPiece m) (y z : F.GradedPiece n) :
    F.gradedMul x (y + z) = F.gradedMul x y + F.gradedMul x z := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      induction z using Quotient.inductionOn' with
      | _ z =>
        change F.toGradedPiece (m + n) ⟨(x : A) * (y + z : F n), _⟩ =
          F.toGradedPiece (m + n) ⟨(x : A) * (y : A), _⟩ +
            F.toGradedPiece (m + n) ⟨(x : A) * (z : A), _⟩
        rw [← map_add]
        apply congrArg (F.toGradedPiece (m + n))
        apply Subtype.ext
        exact mul_add _ _ _

private theorem gradedMul_add_left (F : NatRingFiltration A) {m n : ℕ}
    (x y : F.GradedPiece m) (z : F.GradedPiece n) :
    F.gradedMul (x + y) z = F.gradedMul x z + F.gradedMul y z := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      induction z using Quotient.inductionOn' with
      | _ z =>
        change F.toGradedPiece (m + n) ⟨((x + y : F m) : A) * (z : A), _⟩ =
          F.toGradedPiece (m + n) ⟨(x : A) * (z : A), _⟩ +
            F.toGradedPiece (m + n) ⟨(y : A) * (z : A), _⟩
        rw [← map_add]
        apply congrArg (F.toGradedPiece (m + n))
        apply Subtype.ext
        exact add_mul _ _ _

instance (F : NatRingFiltration A) :
    DirectSum.GNonUnitalNonAssocSemiring F.GradedPiece where
  mul := F.gradedMul
  mul_zero := F.gradedMul_zero_right
  zero_mul := F.gradedMul_zero_left
  mul_add := F.gradedMul_add_right
  add_mul := F.gradedMul_add_left

theorem toGradedPiece_heq (F : NatRingFiltration A) {m n : ℕ}
    (h : m = n) (x : F m) (y : F n) (hxy : (x : A) = y) :
    HEq (F.toGradedPiece m x) (F.toGradedPiece n y) := by
  subst n
  have : x = y := Subtype.ext hxy
  subst y
  rfl

theorem gradedMk_toGradedPiece_eq (F : NatRingFiltration A) {m n : ℕ}
    (h : m = n) (x : F m) (y : F n) (hxy : (x : A) = y) :
    GradedMonoid.mk m (F.toGradedPiece m x) =
      GradedMonoid.mk n (F.toGradedPiece n y) := by
  exact Sigma.ext h (F.toGradedPiece_heq h x y hxy)

instance (F : NatRingFiltration A) : GradedMonoid.GOne F.GradedPiece where
  one := F.toGradedPiece 0 ⟨1, F.one_mem⟩

instance (F : NatRingFiltration A) : GradedMonoid.GMonoid F.GradedPiece where
  one_mul := by
    rintro ⟨n, x⟩
    induction x using Quotient.inductionOn' with
    | _ x =>
      change GradedMonoid.mk (0 + n)
          (F.gradedMul (F.toGradedPiece 0 ⟨1, F.one_mem⟩)
            (F.toGradedPiece n x)) =
        GradedMonoid.mk n (F.toGradedPiece n x)
      rw [F.gradedMul_toGradedPiece]
      exact F.gradedMk_toGradedPiece_eq (Nat.zero_add n)
        ⟨(1 : A) * x, F.mul_mem F.one_mem x.property⟩ x (one_mul (x : A))
  mul_one := by
    rintro ⟨n, x⟩
    induction x using Quotient.inductionOn' with
    | _ x =>
      change GradedMonoid.mk (n + 0)
          (F.gradedMul (F.toGradedPiece n x)
            (F.toGradedPiece 0 ⟨1, F.one_mem⟩)) =
        GradedMonoid.mk n (F.toGradedPiece n x)
      rw [F.gradedMul_toGradedPiece]
      exact F.gradedMk_toGradedPiece_eq (Nat.add_zero n)
        ⟨(x : A) * 1, F.mul_mem x.property F.one_mem⟩ x (mul_one (x : A))
  mul_assoc := by
    rintro ⟨m, x⟩ ⟨n, y⟩ ⟨p, z⟩
    induction x using Quotient.inductionOn' with
    | _ x =>
      induction y using Quotient.inductionOn' with
      | _ y =>
        induction z using Quotient.inductionOn' with
        | _ z =>
          change GradedMonoid.mk ((m + n) + p)
              (F.gradedMul
                (F.gradedMul (F.toGradedPiece m x) (F.toGradedPiece n y))
                (F.toGradedPiece p z)) =
            GradedMonoid.mk (m + (n + p))
              (F.gradedMul (F.toGradedPiece m x)
                (F.gradedMul (F.toGradedPiece n y) (F.toGradedPiece p z)))
          rw [F.gradedMul_toGradedPiece, F.gradedMul_toGradedPiece,
            F.gradedMul_toGradedPiece, F.gradedMul_toGradedPiece]
          exact F.gradedMk_toGradedPiece_eq (Nat.add_assoc m n p)
            ⟨((x : A) * (y : A)) * (z : A),
              F.mul_mem (F.mul_mem x.property y.property) z.property⟩
            ⟨(x : A) * ((y : A) * (z : A)),
              F.mul_mem x.property (F.mul_mem y.property z.property)⟩
            (mul_assoc (x : A) (y : A) (z : A))

private theorem natCast_mem_zero (F : NatRingFiltration A) (n : ℕ) :
    (n : A) ∈ F 0 := by
  simpa only [nsmul_eq_mul, mul_one] using (F 0).nsmul_mem F.one_mem n

instance (F : NatRingFiltration A) : DirectSum.GSemiring F.GradedPiece where
  toGNonUnitalNonAssocSemiring := inferInstance
  one_mul := GradedMonoid.GMonoid.one_mul
  mul_one := GradedMonoid.GMonoid.mul_one
  mul_assoc := GradedMonoid.GMonoid.mul_assoc
  natCast n := n • F.toGradedPiece 0 ⟨1, F.one_mem⟩
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n

private theorem intCast_mem_zero (F : NatRingFiltration A) (z : ℤ) :
    (z : A) ∈ F 0 := by
  simpa only [zsmul_eq_mul, mul_one] using (F 0).smul_mem z F.one_mem

instance (F : NatRingFiltration A) : DirectSum.GRing F.GradedPiece where
  toGSemiring := inferInstance
  intCast z := z • F.toGradedPiece 0 ⟨1, F.one_mem⟩
  intCast_ofNat n := by
    exact ofNat_zsmul _ n
  intCast_negSucc_ofNat n := by
    exact negSucc_zsmul _ n

/-- The external associated graded of a natural ring filtration. -/
abbrev AssociatedGraded (F : NatRingFiltration A) :=
  DirectSum ℕ F.GradedPiece

/-! ## Associated ideals and Noetherian transfer -/

/-- The elements of a filtered term which also belong to a left ideal. -/
def idealFilteredPart (F : NatRingFiltration A) (J : Ideal A) (n : ℕ) :
    Submodule ℤ (F n) :=
  (J.restrictScalars ℤ).comap (F n).subtype

/-- The degree-`n` leading terms of a left ideal. -/
def idealGradedPiece (F : NatRingFiltration A) (J : Ideal A) (n : ℕ) :
    Submodule ℤ (F.GradedPiece n) :=
  (F.idealFilteredPart J n).map (F.toGradedPiece n)

theorem mem_idealGradedPiece_iff (F : NatRingFiltration A) (J : Ideal A)
    (n : ℕ) (x : F.GradedPiece n) :
    x ∈ F.idealGradedPiece J n ↔
      ∃ y : F n, (y : A) ∈ J ∧ F.toGradedPiece n y = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

private theorem homogeneous_mul_mem_idealGradedPiece
    (F : NatRingFiltration A) (J : Ideal A) {m n : ℕ}
    (a : F.GradedPiece m) (b : F.GradedPiece n)
    (hb : b ∈ F.idealGradedPiece J n) :
    F.gradedMul a b ∈ F.idealGradedPiece J (m + n) := by
  obtain ⟨y, hyJ, rfl⟩ := (F.mem_idealGradedPiece_iff J n b).mp hb
  induction a using Quotient.inductionOn' with
  | _ x =>
      apply (F.mem_idealGradedPiece_iff J (m + n) _).mpr
      refine ⟨⟨(x : A) * (y : A), F.mul_mem x.property y.property⟩, ?_, ?_⟩
      · exact J.smul_mem (x : A) hyJ
      · exact F.gradedMul_toGradedPiece x y

/-- The associated graded left ideal, defined coordinate by coordinate. -/
def associatedIdeal (F : NatRingFiltration A) (J : Ideal A) :
    Ideal F.AssociatedGraded where
  carrier := {x | ∀ n, x n ∈ F.idealGradedPiece J n}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro x y hx hy n
    exact (F.idealGradedPiece J n).add_mem (hx n) (hy n)
  smul_mem' := by
    classical
    intro a x hx
    change ∀ n, (a * x) n ∈ F.idealGradedPiece J n
    rw [DirectSum.mul_eq_sum_support_ghas_mul]
    intro k
    let ev : F.AssociatedGraded →+ F.GradedPiece k :=
      { toFun := fun z ↦ z k
        map_zero' := rfl
        map_add' := fun _ _ ↦ DFinsupp.add_apply _ _ k }
    change ev (∑ mn ∈ DFinsupp.support a ×ˢ DFinsupp.support x,
      DirectSum.of F.GradedPiece (mn.1 + mn.2)
        (GradedMonoid.GMul.mul (a mn.1) (x mn.2))) ∈ F.idealGradedPiece J k
    rw [map_sum]
    apply Submodule.sum_mem
    intro mn hmn
    let m := mn.1
    let n := mn.2
    have hxn : x n ∈ F.idealGradedPiece J n := hx n
    have hprod := F.homogeneous_mul_mem_idealGradedPiece J (a m) (x n) hxn
    by_cases hk : m + n = k
    · subst k
      change (DirectSum.of F.GradedPiece (m + n)
        (F.gradedMul (a m) (x n))) (m + n) ∈ F.idealGradedPiece J (m + n)
      rw [DirectSum.of_apply, dif_pos rfl]
      exact hprod
    · change (DirectSum.of F.GradedPiece (m + n)
        (F.gradedMul (a m) (x n))) k ∈ F.idealGradedPiece J k
      rw [DirectSum.of_apply, dif_neg hk]
      exact (F.idealGradedPiece J k).zero_mem

theorem mem_associatedIdeal_iff (F : NatRingFiltration A) (J : Ideal A)
    (x : F.AssociatedGraded) :
    x ∈ F.associatedIdeal J ↔ ∀ n, x n ∈ F.idealGradedPiece J n :=
  Iff.rfl

theorem of_mem_associatedIdeal_iff (F : NatRingFiltration A) (J : Ideal A)
    (n : ℕ) (x : F.GradedPiece n) :
    DirectSum.of F.GradedPiece n x ∈ F.associatedIdeal J ↔
      x ∈ F.idealGradedPiece J n := by
  constructor
  · intro hx
    have := hx n
    simpa using this
  · intro hx m
    by_cases hmn : n = m
    · subst m
      simpa only [DirectSum.of_apply, dif_pos rfl] using hx
    · simp only [DirectSum.of_apply, dif_neg hmn]
      exact (F.idealGradedPiece J m).zero_mem

theorem associatedIdeal_mono (F : NatRingFiltration A) :
    Monotone F.associatedIdeal := by
  intro J K hJK x hx n
  obtain ⟨y, hyJ, hy⟩ :=
    (F.mem_idealGradedPiece_iff J n (x n)).mp (hx n)
  exact (F.mem_idealGradedPiece_iff K n (x n)).mpr ⟨y, hJK hyJ, hy⟩

/-- For comparable ideals, inclusion of associated ideals reflects inclusion.  This is the
filtered descent used in the leading-term proof. -/
theorem le_of_le_of_associatedIdeal_le (F : NatRingFiltration A)
    {J K : Ideal A} (hJK : J ≤ K)
    (hgr : F.associatedIdeal K ≤ F.associatedIdeal J) : K ≤ J := by
  have hdegree : ∀ n (x : A), x ∈ F n → x ∈ K → x ∈ J := by
    intro n
    induction n with
    | zero =>
      intro x hxF hxK
      let xf : F 0 := ⟨x, hxF⟩
      have hleadK : DirectSum.of F.GradedPiece 0 (F.toGradedPiece 0 xf) ∈
          F.associatedIdeal K :=
        (F.of_mem_associatedIdeal_iff K 0 _).mpr
          ((F.mem_idealGradedPiece_iff K 0 _).mpr ⟨xf, hxK, rfl⟩)
      have hleadJ := hgr hleadK
      have hpieceJ := (F.of_mem_associatedIdeal_iff J 0 _).mp hleadJ
      obtain ⟨y, hyJ, heq⟩ := (F.mem_idealGradedPiece_iff J 0 _).mp hpieceJ
      have hdiff : x - (y : A) ∈ F.previous 0 := by
        have := (Submodule.Quotient.eq (F.previousIn 0)).mp heq.symm
        exact this
      have hxy : x = y := by
        have : x - (y : A) = 0 := by simpa [previous] using hdiff
        exact sub_eq_zero.mp this
      simpa [hxy] using hyJ
    | succ n ih =>
      intro x hxF hxK
      let xf : F (n + 1) := ⟨x, hxF⟩
      have hleadK : DirectSum.of F.GradedPiece (n + 1)
          (F.toGradedPiece (n + 1) xf) ∈ F.associatedIdeal K :=
        (F.of_mem_associatedIdeal_iff K (n + 1) _).mpr
          ((F.mem_idealGradedPiece_iff K (n + 1) _).mpr ⟨xf, hxK, rfl⟩)
      have hleadJ := hgr hleadK
      have hpieceJ := (F.of_mem_associatedIdeal_iff J (n + 1) _).mp hleadJ
      obtain ⟨y, hyJ, heq⟩ :=
        (F.mem_idealGradedPiece_iff J (n + 1) _).mp hpieceJ
      have hdiffF : x - (y : A) ∈ F n := by
        have hdiff := (Submodule.Quotient.eq (F.previousIn (n + 1))).mp heq.symm
        simpa [previous] using hdiff
      have hdiffK : x - (y : A) ∈ K := K.sub_mem hxK (hJK hyJ)
      have hdiffJ := ih (x - (y : A)) hdiffF hdiffK
      have hsum := J.add_mem hdiffJ hyJ
      simpa only [sub_add_cancel] using hsum
  intro x hxK
  obtain ⟨n, hxn⟩ := F.exhaustive x
  exact hdegree n x hxn hxK

theorem associatedIdeal_strictMono (F : NatRingFiltration A) :
    StrictMono F.associatedIdeal := by
  intro J K hJK
  refine lt_of_le_of_ne (F.associatedIdeal_mono hJK.le) ?_
  intro heq
  have hKJ := F.le_of_le_of_associatedIdeal_le hJK.le heq.ge
  exact hJK.2 hKJ

/-- **Filtered Noetherian transfer.**  An exhaustive natural filtration with Noetherian
associated graded ring is itself Noetherian. -/
theorem isNoetherianRing_of_associatedGraded (F : NatRingFiltration A)
    [IsNoetherianRing F.AssociatedGraded] : IsNoetherianRing A := by
  rw [isNoetherianRing_iff, isNoetherian_iff']
  exact F.associatedIdeal_strictMono.wellFoundedGT

/-! ## Almost-commutative filtrations -/

/-- Multiplication is commutative in the associated graded precisely when every filtered
commutator drops by one filtration step. -/
def IsAlmostCommutative (F : NatRingFiltration A) : Prop :=
  ∀ {m n : ℕ} (x : F m) (y : F n),
    (x : A) * (y : A) - (y : A) * (x : A) ∈ F.previous (m + n)

private theorem associatedGraded_of_mul_comm (F : NatRingFiltration A)
    (hcomm : F.IsAlmostCommutative) {m n : ℕ}
    (x : F.GradedPiece m) (y : F.GradedPiece n) :
    DirectSum.of F.GradedPiece m x * DirectSum.of F.GradedPiece n y =
      DirectSum.of F.GradedPiece n y * DirectSum.of F.GradedPiece m x := by
  rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      change DirectSum.of F.GradedPiece (m + n)
          (F.gradedMul (F.toGradedPiece m x) (F.toGradedPiece n y)) =
        DirectSum.of F.GradedPiece (n + m)
          (F.gradedMul (F.toGradedPiece n y) (F.toGradedPiece m x))
      rw [F.gradedMul_toGradedPiece, F.gradedMul_toGradedPiece]
      let xy : F (m + n) :=
        ⟨(x : A) * (y : A), F.mul_mem x.property y.property⟩
      let yx : F (n + m) :=
        ⟨(y : A) * (x : A), F.mul_mem y.property x.property⟩
      let yx' : F (m + n) := ⟨(y : A) * (x : A), by
        rw [Nat.add_comm]
        exact F.mul_mem y.property x.property⟩
      have hq : F.toGradedPiece (m + n) xy =
          F.toGradedPiece (m + n) yx' := by
        apply (Submodule.Quotient.eq (F.previousIn (m + n))).2
        exact hcomm x y
      have htransport : HEq (F.toGradedPiece (m + n) yx')
          (F.toGradedPiece (n + m) yx) :=
        F.toGradedPiece_heq (Nat.add_comm m n) yx' yx rfl
      apply DirectSum.of_eq_of_gradedMonoid_eq
      apply Sigma.ext (Nat.add_comm m n)
      exact (heq_of_eq hq).trans htransport

private theorem associatedGraded_mul_comm (F : NatRingFiltration A)
    (hcomm : F.IsAlmostCommutative) (x y : F.AssociatedGraded) : x * y = y * x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of m x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of n y => exact F.associatedGraded_of_mul_comm hcomm x y
    | add y z hy hz => simp only [mul_add, add_mul, hy, hz, add_comm]
  | add x y hx hy => simp only [add_mul, mul_add, hx, hy, add_comm]

/-- The commutative-ring structure on the associated graded of an almost-commutative
filtration. -/
@[reducible] def associatedGradedCommRing (F : NatRingFiltration A)
    (hcomm : F.IsAlmostCommutative) : CommRing F.AssociatedGraded :=
  { (inferInstance : Ring F.AssociatedGraded) with
    mul_comm := F.associatedGraded_mul_comm hcomm }

end NatRingFiltration

end


end LieRings.Plotkin
