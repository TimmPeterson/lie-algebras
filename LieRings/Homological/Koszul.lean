import LieRings.Homological.SymmetricPower
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic

/-!
# Integral Koszul presentations

This file fixes the presentation and sign conventions used for
`L₁Sᵐ`.  Presentations are genuinely two-term finite free resolutions; no
basis is part of the abstract data.
-/

open TensorProduct

namespace Koszul

universe u v w z

noncomputable section

/-- A two-term finite free integral presentation of an additive group. -/
structure Presentation (A : Type u) [AddCommGroup A] where
  rel : Type v
  gen : Type w
  relAddCommGroup : AddCommGroup rel
  genAddCommGroup : AddCommGroup gen
  relFree : Module.Free ℤ rel
  genFree : Module.Free ℤ gen
  relFinite : Module.Finite ℤ rel
  genFinite : Module.Finite ℤ gen
  d : rel →ₗ[ℤ] gen
  augmentation : gen →ₗ[ℤ] A
  d_injective : Function.Injective d
  augmentation_surjective : Function.Surjective augmentation
  exact : LinearMap.range d = LinearMap.ker augmentation

attribute [instance] Presentation.relAddCommGroup Presentation.genAddCommGroup
  Presentation.relFree Presentation.genFree Presentation.relFinite Presentation.genFinite

namespace Presentation

variable {A : Type u} [AddCommGroup A]

@[simp]
theorem augmentation_d (P : Presentation A) (r : P.rel) :
    P.augmentation (P.d r) = 0 := by
  have : P.d r ∈ LinearMap.ker P.augmentation := by
    rw [← P.exact]
    exact ⟨r, rfl⟩
  exact this

/-- A morphism of presentations inducing the specified map on cokernels. -/
structure Hom {B : Type*} [AddCommGroup B]
    (P : Presentation A) (Q : Presentation B) (f : A →ₗ[ℤ] B) where
  relMap : P.rel →ₗ[ℤ] Q.rel
  genMap : P.gen →ₗ[ℤ] Q.gen
  commutes : Q.d.comp relMap = genMap.comp P.d
  induces : Q.augmentation.comp genMap = f.comp P.augmentation

namespace Hom

variable {B : Type*} [AddCommGroup B] {C : Type*} [AddCommGroup C]
variable {P : Presentation A} {Q : Presentation B} {S : Presentation C}

/-- Identity presentation morphism. -/
def id (P : Presentation A) : Hom P P LinearMap.id where
  relMap := LinearMap.id
  genMap := LinearMap.id
  commutes := by ext; rfl
  induces := by ext; rfl

/-- Composition of strict presentation morphisms. -/
def comp {f : A →ₗ[ℤ] B} {g : B →ₗ[ℤ] C}
    (G : Hom Q S g) (F : Hom P Q f) : Hom P S (g.comp f) where
  relMap := G.relMap.comp F.relMap
  genMap := G.genMap.comp F.genMap
  commutes := by
    ext x
    change S.d (G.relMap (F.relMap x)) = G.genMap (F.genMap (P.d x))
    rw [show S.d (G.relMap (F.relMap x)) = G.genMap (Q.d (F.relMap x)) by
      exact LinearMap.congr_fun G.commutes (F.relMap x)]
    rw [show Q.d (F.relMap x) = F.genMap (P.d x) by
      exact LinearMap.congr_fun F.commutes x]
  induces := by
    ext x
    change S.augmentation (G.genMap (F.genMap x)) = g (f (P.augmentation x))
    rw [show S.augmentation (G.genMap (F.genMap x)) =
        g (Q.augmentation (F.genMap x)) by
      exact LinearMap.congr_fun G.induces (F.genMap x)]
    rw [show Q.augmentation (F.genMap x) = f (P.augmentation x) by
      exact LinearMap.congr_fun F.induces x]

@[simp] theorem id_relMap (P : Presentation A) : (id P).relMap = LinearMap.id := rfl
@[simp] theorem id_genMap (P : Presentation A) : (id P).genMap = LinearMap.id := rfl
@[simp] theorem comp_relMap {f : A →ₗ[ℤ] B} {g : B →ₗ[ℤ] C}
    (G : Hom Q S g) (F : Hom P Q f) :
    (comp G F).relMap = G.relMap.comp F.relMap := rfl
@[simp] theorem comp_genMap {f : A →ₗ[ℤ] B} {g : B →ₗ[ℤ] C}
    (G : Hom Q S g) (F : Hom P Q f) :
    (comp G F).genMap = G.genMap.comp F.genMap := rfl

end Hom

/-- The augmentation of the canonical free presentation. -/
def freeAugmentation (A : Type u) [AddCommGroup A] :
    (A →₀ ℤ) →ₗ[ℤ] A :=
  Finsupp.linearCombination ℤ id

@[simp]
theorem freeAugmentation_single (A : Type u) [AddCommGroup A] (a : A) (z : ℤ) :
    freeAugmentation A (Finsupp.single a z) = z • a := by
  simp [freeAugmentation]

theorem freeAugmentation_surjective (A : Type u) [AddCommGroup A] :
    Function.Surjective (freeAugmentation A) := by
  intro a
  refine ⟨Finsupp.single a 1, ?_⟩
  simp

/-- The canonical finite free presentation used in the definition of
`L₁Sᵐ(A)`. -/
def canonical (A : Type u) [AddCommGroup A] [Finite A] : Presentation A where
  rel := LinearMap.ker (freeAugmentation A)
  gen := A →₀ ℤ
  relAddCommGroup := inferInstance
  genAddCommGroup := inferInstance
  relFree := inferInstance
  genFree := inferInstance
  relFinite := inferInstance
  genFinite := inferInstance
  d := (LinearMap.ker (freeAugmentation A)).subtype
  augmentation := freeAugmentation A
  d_injective := Subtype.val_injective
  augmentation_surjective := freeAugmentation_surjective A
  exact := by
    ext x
    simp

/-- The strict lift of a homomorphism between canonical presentations. -/
def canonicalHom {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    [Finite A] [Finite B] (f : A →ₗ[ℤ] B) :
    Hom (canonical A) (canonical B) f := by
  let g : (A →₀ ℤ) →ₗ[ℤ] (B →₀ ℤ) :=
    Finsupp.lmapDomain ℤ ℤ f
  have hgMap : (freeAugmentation B).comp g = f.comp (freeAugmentation A) := by
    apply Finsupp.lhom_ext
    intro a z
    simp [g, freeAugmentation]
  have hg (x : A →₀ ℤ) : freeAugmentation B (g x) = f (freeAugmentation A x) :=
    LinearMap.congr_fun hgMap x
  exact
    { genMap := g
      relMap := LinearMap.codRestrict (LinearMap.ker (freeAugmentation B))
        (g.domRestrict (LinearMap.ker (freeAugmentation A))) (fun x ↦ by
          change freeAugmentation B (g x.1) = 0
          rw [hg, x.property, map_zero])
      commutes := by ext x; rfl
      induces := by ext x; exact hg x }

@[ext]
theorem Hom.ext {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    {P : Presentation A} {Q : Presentation B} {f : A →ₗ[ℤ] B}
    {F G : Hom P Q f} (hrel : F.relMap = G.relMap)
    (hgen : F.genMap = G.genMap) : F = G := by
  cases F
  cases G
  simp only [mk.injEq] at hrel hgen ⊢
  exact ⟨hrel, hgen⟩

@[simp]
theorem canonicalHom_id {A : Type u} [AddCommGroup A] [Finite A] :
    canonicalHom (LinearMap.id (R := ℤ) (M := A)) = Hom.id (canonical A) := by
  apply Hom.ext
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change Finsupp.lmapDomain ℤ ℤ (LinearMap.id (R := ℤ) (M := A)) x.1 = x.1
    rw [show (LinearMap.id (R := ℤ) (M := A) : A → A) = id by rfl,
      Finsupp.lmapDomain_id]
    rfl
  · change Finsupp.lmapDomain ℤ ℤ (LinearMap.id (R := ℤ) (M := A)) =
      LinearMap.id
    rw [show (LinearMap.id (R := ℤ) (M := A) : A → A) = id by rfl,
      Finsupp.lmapDomain_id]

theorem canonicalHom_comp {A : Type u} {B : Type v} {C : Type w}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Finite A] [Finite B] [Finite C] (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C) :
    canonicalHom (g.comp f) = (canonicalHom g).comp (canonicalHom f) := by
  apply Hom.ext
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change Finsupp.lmapDomain ℤ ℤ (g.comp f) x.1 =
      Finsupp.lmapDomain ℤ ℤ g (Finsupp.lmapDomain ℤ ℤ f x.1)
    exact LinearMap.congr_fun (Finsupp.lmapDomain_comp ℤ ℤ f g) x.1
  · change Finsupp.lmapDomain ℤ ℤ (g.comp f) =
      (Finsupp.lmapDomain ℤ ℤ g).comp (Finsupp.lmapDomain ℤ ℤ f)
    exact Finsupp.lmapDomain_comp ℤ ℤ f g

/-! ### Strict comparison maps between free presentations -/

private theorem genLift_exists {B : Type v} [AddCommGroup B]
    (P : Presentation A) (Q : Presentation B) (f : A →ₗ[ℤ] B) :
    ∃ g : P.gen →ₗ[ℤ] Q.gen,
      Q.augmentation.comp g = f.comp P.augmentation := by
  exact Module.projective_lifting_property Q.augmentation
    (f.comp P.augmentation) Q.augmentation_surjective

/-- A chosen lift on generators of a map between the presented groups. -/
noncomputable def genLift {B : Type v} [AddCommGroup B]
    (P : Presentation A) (Q : Presentation B) (f : A →ₗ[ℤ] B) :
    P.gen →ₗ[ℤ] Q.gen :=
  Classical.choose (genLift_exists P Q f)

theorem genLift_spec {B : Type v} [AddCommGroup B]
    (P : Presentation A) (Q : Presentation B) (f : A →ₗ[ℤ] B) :
    Q.augmentation.comp (genLift P Q f) = f.comp P.augmentation :=
  Classical.choose_spec (genLift_exists P Q f)

private def differentialToKernel {B : Type v} [AddCommGroup B]
    (Q : Presentation B) : Q.rel →ₗ[ℤ] LinearMap.ker Q.augmentation :=
  LinearMap.codRestrict (LinearMap.ker Q.augmentation) Q.d (fun r ↦ by
    exact Q.augmentation_d r)

private theorem differentialToKernel_surjective
    {B : Type v} [AddCommGroup B] (Q : Presentation B) :
    Function.Surjective (differentialToKernel Q) := by
  rintro ⟨x, hx⟩
  have hrange : x ∈ LinearMap.range Q.d := by
    rw [Q.exact]
    exact hx
  obtain ⟨r, hr⟩ := hrange
  refine ⟨r, ?_⟩
  apply Subtype.ext
  exact hr

private def relationLiftTarget {B : Type v} [AddCommGroup B]
    (P : Presentation A) (Q : Presentation B) (f : A →ₗ[ℤ] B) :
    P.rel →ₗ[ℤ] LinearMap.ker Q.augmentation :=
  LinearMap.codRestrict (LinearMap.ker Q.augmentation)
    ((genLift P Q f).comp P.d) (fun r ↦ by
      have hgen := LinearMap.congr_fun (genLift_spec P Q f) (P.d r)
      simpa only [LinearMap.comp_apply, P.augmentation_d, map_zero] using hgen)

private theorem relLift_exists {B : Type v} [AddCommGroup B]
    (P : Presentation A) (Q : Presentation B) (f : A →ₗ[ℤ] B) :
    ∃ h : P.rel →ₗ[ℤ] Q.rel,
      (differentialToKernel Q).comp h = relationLiftTarget P Q f := by
  exact Module.projective_lifting_property (differentialToKernel Q)
    (relationLiftTarget P Q f) (differentialToKernel_surjective Q)

/-- Every homomorphism of the presented groups admits a strict comparison
map between finite free presentations.  No compatibility is postulated: the
two squares are proved from the chosen projective lifts. -/
noncomputable def liftHom {B : Type v} [AddCommGroup B]
    (P : Presentation A) (Q : Presentation B) (f : A →ₗ[ℤ] B) :
    Hom P Q f where
  genMap := genLift P Q f
  relMap := Classical.choose (relLift_exists P Q f)
  commutes := by
    apply LinearMap.ext
    intro r
    have h := LinearMap.congr_fun
      (Classical.choose_spec (relLift_exists P Q f)) r
    exact congrArg Subtype.val h
  induces := genLift_spec P Q f

end Presentation

namespace AllDegrees

variable {Rel : Type u} {Gen : Type v} [AddCommGroup Rel] [AddCommGroup Gen]

/-- One summand in the all-degree Koszul differential, before alternating
uncurrying. -/
private def wedgeTensorInsert (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) (a : Rel) :
    (⋀[ℤ]^n Rel) →ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) where
  toFun w := (TensorProduct.mk ℤ _ _ w).comp (SymmetricPower.insert ℤ Gen q (d a))
  map_add' x y := by
    ext s
    change (x + y) ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s =
      x ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s +
        y ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s
    exact add_tmul x y _
  map_smul' r x := by
    ext s
    change (r • x) ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s =
      r • (x ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s)
    exact smul_tmul' r x _

private def tail (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    Rel →ₗ[ℤ] Rel [⋀^Fin n]→ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) where
  toFun a := (wedgeTensorInsert d n q a).compAlternatingMap (exteriorPower.ιMulti ℤ n)
  map_add' a b := by
    ext v s
    change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen q (d (a + b)) s =
      exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen q (d a) s +
        exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen q (d b) s
    rw [map_add, SymmetricPower.insert_add_apply, tmul_add]
  map_smul' r a := by
    letI : TensorProduct.CompatibleSMul ℤ ℤ (⋀[ℤ]^n Rel)
        (Sym[ℤ] (Fin (q + 1)) Gen) := TensorProduct.CompatibleSMul.int
    ext v s
    change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen q (d (r • a)) s =
      r • (exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen q (d a) s)
    rw [map_smul, SymmetricPower.insert_smul_apply]
    calc
      exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          (r • SymmetricPower.insert ℤ Gen q (d a) s) =
          (r • exteriorPower.ιMulti ℤ n v) ⊗ₜ[ℤ]
            SymmetricPower.insert ℤ Gen q (d a) s :=
        (TensorProduct.smul_tmul (R := ℤ) (R' := ℤ) r _ _).symm
      _ = r • (exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen q (d a) s) :=
        (TensorProduct.smul_tmul' (R := ℤ) (R' := ℤ) r _ _).symm

private def differentialAlternating (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    Rel [⋀^Fin (n + 1)]→ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) :=
  ((-1 : ℤ) ^ n) • AlternatingMap.alternatizeUncurryFin (tail d n q)

private def differentialCore (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    (⋀[ℤ]^(n + 1) Rel) →ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) :=
  exteriorPower.alternatingMapLinearEquiv (differentialAlternating d n q)

/-- The integral Koszul differential
`Lambda^(n+1) Rel tensor Sym^q Gen -> Lambda^n Rel tensor Sym^(q+1) Gen`.
Its sign agrees literally with the manuscript. -/
def differential (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    ((⋀[ℤ]^(n + 1) Rel) ⊗[ℤ] Sym[ℤ] (Fin q) Gen) →ₗ[ℤ]
      ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) :=
  (TensorProduct.lift (differentialCore d n q)).toAddMonoidHom.toIntLinearMap

private theorem neg_one_pow_mul_neg_one_pow (n : ℕ) (j : Fin (n + 1)) :
    ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ j.val) = (-1 : ℤ) ^ (n - j.val) := by
  have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  rw [← pow_add]
  rw [show n + j.val = (n - j.val) + 2 * j.val by omega, pow_add]
  have heven : (-1 : ℤ) ^ (2 * j.val) = 1 :=
    Even.neg_one_pow ⟨j.val, by omega⟩
  rw [heven, mul_one]

@[simp]
theorem differential_wedge_tmul (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 1) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    differential d n q (exteriorPower.ιMulti ℤ (n + 1) a ⊗ₜ[ℤ] s) =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (n - j.val)) •
        (exteriorPower.ιMulti ℤ n (j.removeNth a) ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen q (d (a j)) s) := by
  change differentialCore d n q (exteriorPower.ιMulti ℤ (n + 1) a) s = _
  have h := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (differentialAlternating d n q) a
  calc
    differentialCore d n q (exteriorPower.ιMulti ℤ (n + 1) a) s =
        differentialAlternating d n q a s := by
      exact DFunLike.congr_fun h s
    _ = _ := by
      simp only [differentialAlternating, AlternatingMap.smul_apply,
        AlternatingMap.alternatizeUncurryFin_apply, Finset.smul_sum, smul_smul,
        tail, wedgeTensorInsert, neg_one_pow_mul_neg_one_pow]
      let ev :
          (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
            ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen)) →ₗ[ℤ]
              ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) := {
        toFun f := f s
        map_add' f g := rfl
        map_smul' r f := rfl }
      change ev (∑ x : Fin (n + 1),
          ((-1 : ℤ) ^ (n - x.val)) • (tail d n q (a x)) (x.removeNth a)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rfl

private def wedgeTensorDouble (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) (a b : Rel) :
    (⋀[ℤ]^n Rel) →ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) where
  toFun w := (TensorProduct.mk ℤ _ _ w).comp
    ((SymmetricPower.insert ℤ Gen (q + 1) (d b)).comp
      (SymmetricPower.insert ℤ Gen q (d a)))
  map_add' x y := by
    ext s
    change (x + y) ⊗ₜ[ℤ] _ = x ⊗ₜ[ℤ] _ + y ⊗ₜ[ℤ] _
    exact add_tmul x y _
  map_smul' r x := by
    ext s
    change (r • x) ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d b)
          (SymmetricPower.insert ℤ Gen q (d a) s) =
      r • (x ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d b)
          (SymmetricPower.insert ℤ Gen q (d a) s))
    exact smul_tmul' r x _

set_option maxHeartbeats 800000 in
private def doubleTail (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    Rel →ₗ[ℤ] Rel →ₗ[ℤ] Rel [⋀^Fin n]→ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) where
  toFun a := {
    toFun := fun b ↦ (wedgeTensorDouble d n q a b).compAlternatingMap
      (exteriorPower.ιMulti ℤ n)
    map_add' := by
      intro b c
      ext v s
      change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen (q + 1) (d (b + c))
            (SymmetricPower.insert ℤ Gen q (d a) s) =
        exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
            SymmetricPower.insert ℤ Gen (q + 1) (d b)
              (SymmetricPower.insert ℤ Gen q (d a) s) +
          exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
            SymmetricPower.insert ℤ Gen (q + 1) (d c)
              (SymmetricPower.insert ℤ Gen q (d a) s)
      rw [map_add, SymmetricPower.insert_add_apply, tmul_add]
    map_smul' := by
      intro r b
      letI : TensorProduct.CompatibleSMul ℤ ℤ (⋀[ℤ]^n Rel)
          (Sym[ℤ] (Fin (q + 2)) Gen) := TensorProduct.CompatibleSMul.int
      ext v s
      change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen (q + 1) (d (r • b))
            (SymmetricPower.insert ℤ Gen q (d a) s) = _
      rw [map_smul, SymmetricPower.insert_smul_apply]
      calc
        exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
            (r • SymmetricPower.insert ℤ Gen (q + 1) (d b)
              (SymmetricPower.insert ℤ Gen q (d a) s)) =
            (r • exteriorPower.ιMulti ℤ n v) ⊗ₜ[ℤ] _ :=
          (TensorProduct.smul_tmul (R := ℤ) (R' := ℤ) r _ _).symm
        _ = r • (exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ] _) :=
          (TensorProduct.smul_tmul' (R := ℤ) (R' := ℤ) r _ _).symm }
  map_add' := by
    intro a b
    ext c v s
    change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d c)
          (SymmetricPower.insert ℤ Gen q (d (a + b)) s) =
      exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen (q + 1) (d c)
            (SymmetricPower.insert ℤ Gen q (d a) s) +
        exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen (q + 1) (d c)
            (SymmetricPower.insert ℤ Gen q (d b) s)
    rw [map_add, SymmetricPower.insert_add_apply, map_add, tmul_add]
  map_smul' := by
    intro r a
    letI : TensorProduct.CompatibleSMul ℤ ℤ (⋀[ℤ]^n Rel)
        (Sym[ℤ] (Fin (q + 2)) Gen) := TensorProduct.CompatibleSMul.int
    ext b v s
    change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d b)
          (SymmetricPower.insert ℤ Gen q (d (r • a)) s) = _
    rw [map_smul, SymmetricPower.insert_smul_apply, map_smul]
    calc
      exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          (r • SymmetricPower.insert ℤ Gen (q + 1) (d b)
            (SymmetricPower.insert ℤ Gen q (d a) s)) =
          (r • exteriorPower.ιMulti ℤ n v) ⊗ₜ[ℤ] _ :=
        (TensorProduct.smul_tmul (R := ℤ) (R' := ℤ) r _ _).symm
      _ = r • (exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ] _) :=
        (TensorProduct.smul_tmul' (R := ℤ) (R' := ℤ) r _ _).symm

private theorem doubleTail_symmetric (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) (a b : Rel) :
    doubleTail d n q a b = doubleTail d n q b a := by
  ext v s
  change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
      SymmetricPower.insert ℤ Gen (q + 1) (d b)
        (SymmetricPower.insert ℤ Gen q (d a) s) =
    exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
      SymmetricPower.insert ℤ Gen (q + 1) (d a)
        (SymmetricPower.insert ℤ Gen q (d b) s)
  apply congrArg (fun z ↦ exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ] z)
  exact LinearMap.congr_fun (SymmetricPower.insert_comm ℤ Gen q (d b) (d a)) s

private theorem doubleAlternating_zero (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    AlternatingMap.alternatizeUncurryFin
      (AlternatingMap.alternatizeUncurryFinLM ∘ₗ doubleTail d n q) = 0 :=
  AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
    (doubleTail_symmetric d n q)

private def doubleSum (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
    ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) •
      (exteriorPower.ιMulti ℤ n (j.removeNth (i.removeNth a)) ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d ((i.removeNth a) j))
          (SymmetricPower.insert ℤ Gen q (d (a i)) s))

private theorem doubleSum_zero (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    doubleSum d n q a s = 0 := by
  have h := DFunLike.congr_fun (doubleAlternating_zero d n q) a
  have hs := DFunLike.congr_fun h s
  simp only [AlternatingMap.alternatizeUncurryFin_apply,
    LinearMap.coe_comp, Function.comp_apply,
    AlternatingMap.alternatizeUncurryFinLM_apply] at hs
  let ev :
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen)) →ₗ[ℤ]
          ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) := {
    toFun f := f s
    map_add' f g := rfl
    map_smul' r f := rfl }
  change ev (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) •
        (doubleTail d n q (a i) ((i.removeNth a) j))
          (j.removeNth (i.removeNth a))) = ev 0 at hs
  simp only [map_sum, map_smul, map_zero, doubleTail, wedgeTensorDouble] at hs
  exact hs

private def reverseDoubleSum (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (n + 1 - i.val)) •
    ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (n - j.val)) •
      (exteriorPower.ιMulti ℤ n (j.removeNth (i.removeNth a)) ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d ((i.removeNth a) j))
          (SymmetricPower.insert ℤ Gen q (d (a i)) s))

private def intScalarEnd {T : Type*} [AddCommGroup T] (c : ℤ) : T →ₗ[ℤ] T :=
  c • LinearMap.id

private theorem int_smul_fintype_sum {T I : Type*} [AddCommGroup T] [Fintype I]
    (c : ℤ) (f : I → T) :
    c • (∑ i, f i) = ∑ i, c • f i := by
  change intScalarEnd c (∑ i, f i) = _
  rw [map_sum]
  rfl

private theorem reverseSignedSum_eq {T : Type*} [AddCommGroup T] (n : ℕ)
    (f : Fin (n + 1) → T) :
    (∑ i, ((-1 : ℤ) ^ (n - i.val)) • f i) =
      ((-1 : ℤ) ^ n) • ∑ i, ((-1 : ℤ) ^ i.val) • f i := by
  rw [int_smul_fintype_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul, neg_one_pow_mul_neg_one_pow]

private theorem reverseDoubleSum_eq (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    reverseDoubleSum d n q a s =
      (((-1 : ℤ) ^ (n + 1)) * ((-1 : ℤ) ^ n)) • doubleSum d n q a s := by
  unfold reverseDoubleSum doubleSum
  rw [reverseSignedSum_eq (n + 1)]
  simp_rw [reverseSignedSum_eq n]
  let g : Fin (n + 2) → Fin (n + 1) →
      ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) := fun i j ↦
    exteriorPower.ιMulti ℤ n (j.removeNth (i.removeNth a)) ⊗ₜ[ℤ]
      SymmetricPower.insert ℤ Gen (q + 1) (d ((i.removeNth a) j))
        (SymmetricPower.insert ℤ Gen q (d (a i)) s)
  change ((-1 : ℤ) ^ (n + 1)) •
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (((-1 : ℤ) ^ n) •
          ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j) =
    (((-1 : ℤ) ^ (n + 1)) * ((-1 : ℤ) ^ n)) •
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j
  have hinside :
      (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (((-1 : ℤ) ^ n) •
          ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j)) =
      ((-1 : ℤ) ^ n) •
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
          ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j := by
    calc
      _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ n) •
          (((-1 : ℤ) ^ i.val) •
            ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [smul_smul]
        congr 1
        ring
      _ = _ := (int_smul_fintype_sum ((-1 : ℤ) ^ n)
        (fun i : Fin (n + 2) ↦ ((-1 : ℤ) ^ i.val) •
          ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j)).symm
  rw [hinside, smul_smul]

private theorem reverseDoubleSum_zero (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    reverseDoubleSum d n q a s = 0 := by
  rw [reverseDoubleSum_eq, doubleSum_zero]
  exact smul_zero _

/-- Consecutive all-degree Koszul differentials compose to zero. -/
theorem differential_comp_differential (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    (differential d n (q + 1)).comp (differential d (n + 1) q) = 0 := by
  apply TensorProduct.ext'
  intro w s
  let F : (⋀[ℤ]^(n + 2) Rel) →ₗ[ℤ]
      ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) :=
    ((differential d n (q + 1)).comp (differential d (n + 1) q)).comp
      ((TensorProduct.mk ℤ (⋀[ℤ]^(n + 2) Rel) _).flip s)
  have hF : F = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    change differential d n (q + 1)
      (differential d (n + 1) q
        (exteriorPower.ιMulti ℤ (n + 2) a ⊗ₜ[ℤ] s)) = 0
    rw [differential_wedge_tmul, map_sum]
    simp only [map_smul, differential_wedge_tmul]
    exact reverseDoubleSum_zero d n q a s
  have hw := LinearMap.congr_fun hF w
  simpa [F, LinearMap.comp_apply] using hw

/-- Naturality of the all-degree Koszul differential under a commuting square
of presentation differentials. -/
theorem differential_natural {Rel' : Type*} {Gen' : Type*}
    [AddCommGroup Rel'] [AddCommGroup Gen']
    (d : Rel →ₗ[ℤ] Gen) (d' : Rel' →ₗ[ℤ] Gen')
    (fr : Rel →ₗ[ℤ] Rel') (fg : Gen →ₗ[ℤ] Gen')
    (hcomm : d'.comp fr = fg.comp d) (n q : ℕ) :
    (differential d' n q).comp
        (TensorProduct.map (exteriorPower.map (n + 1) fr)
          (SymmetricPower.map (R := ℤ) (ι := Fin q) fg)) =
      (TensorProduct.map (exteriorPower.map n fr)
          (SymmetricPower.map (R := ℤ) (ι := Fin (q + 1)) fg)).comp
        (differential d n q) := by
  apply TensorProduct.ext'
  intro w s
  let Fw : (⋀[ℤ]^(n + 1) Rel) →ₗ[ℤ]
      ((⋀[ℤ]^n Rel') ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen') :=
    ((differential d' n q).comp
        (TensorProduct.map (exteriorPower.map (n + 1) fr)
          (SymmetricPower.map (R := ℤ) (ι := Fin q) fg))).comp
      ((TensorProduct.mk ℤ _ _).flip s)
  have hFw : Fw =
      ((TensorProduct.map (exteriorPower.map n fr)
          (SymmetricPower.map (R := ℤ) (ι := Fin (q + 1)) fg)).comp
        (differential d n q)).comp ((TensorProduct.mk ℤ _ _).flip s) := by
    apply exteriorPower.linearMap_ext
    ext a
    let Fs : Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        ((⋀[ℤ]^n Rel') ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen') :=
      ((differential d' n q).comp
          (TensorProduct.map (exteriorPower.map (n + 1) fr)
            (SymmetricPower.map (R := ℤ) (ι := Fin q) fg))).comp
        (TensorProduct.mk ℤ _ _ (exteriorPower.ιMulti ℤ (n + 1) a))
    have hFs : Fs =
        ((TensorProduct.map (exteriorPower.map n fr)
            (SymmetricPower.map (R := ℤ) (ι := Fin (q + 1)) fg)).comp
          (differential d n q)).comp
            (TensorProduct.mk ℤ _ _ (exteriorPower.ιMulti ℤ (n + 1) a)) := by
      apply SymmetricPower.linearMap_ext
      intro x
      change differential d' n q
          (exteriorPower.map (n + 1) fr
              (exteriorPower.ιMulti ℤ (n + 1) a) ⊗ₜ[ℤ]
            SymmetricPower.map (R := ℤ) (ι := Fin q) fg
              (SymmetricPower.tprod ℤ x)) =
        (TensorProduct.map (exteriorPower.map n fr)
          (SymmetricPower.map (R := ℤ) (ι := Fin (q + 1)) fg))
            (differential d n q
              (exteriorPower.ιMulti ℤ (n + 1) a ⊗ₜ[ℤ]
                SymmetricPower.tprod ℤ x))
      rw [exteriorPower.map_apply_ιMulti, SymmetricPower.map_tprod,
        differential_wedge_tmul, differential_wedge_tmul]
      symm
      calc
        _ = ∑ j : Fin (n + 1),
            (TensorProduct.map (exteriorPower.map n fr)
              (SymmetricPower.map (R := ℤ) (ι := Fin (q + 1)) fg))
              (((-1 : ℤ) ^ (n - j.val)) •
                (exteriorPower.ιMulti ℤ n (j.removeNth a) ⊗ₜ[ℤ]
                  SymmetricPower.insert ℤ Gen q (d (a j))
                    (SymmetricPower.tprod ℤ x))) := map_sum _ _ Finset.univ
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          change (TensorProduct.map (exteriorPower.map n fr)
              (SymmetricPower.map (R := ℤ) (ι := Fin (q + 1)) fg))
              ((((-1 : ℤ) ^ (n - j.val)) •
                  exteriorPower.ιMulti ℤ n (j.removeNth a)) ⊗ₜ[ℤ]
                SymmetricPower.insert ℤ Gen q (d (a j))
                  (SymmetricPower.tprod ℤ x)) =
            (((-1 : ℤ) ^ (n - j.val)) •
                exteriorPower.ιMulti ℤ n (j.removeNth (fr ∘ a))) ⊗ₜ[ℤ]
              SymmetricPower.insert ℤ Gen' q (d' (fr (a j)))
                (SymmetricPower.tprod ℤ (fg ∘ x))
          rw [TensorProduct.map_tmul, map_zsmul,
            exteriorPower.map_apply_ιMulti]
          have hdj : d' (fr (a j)) = fg (d (a j)) := by
            exact LinearMap.congr_fun hcomm (a j)
          congr 1
          rw [hdj]
          have hm := LinearMap.congr_fun
            (SymmetricPower.map_insert (R₀ := ℤ) (M₀ := Gen) (N₀ := Gen')
              fg q (d (a j)))
            (SymmetricPower.tprod ℤ x)
          simpa only [LinearMap.comp_apply, SymmetricPower.map_tprod] using hm
    exact LinearMap.congr_fun hFs s
  exact LinearMap.congr_fun hFw w

end AllDegrees

section BoundedComplex

open CategoryTheory
open CategoryTheory.Limits

variable {A : Type u} [AddCommGroup A] (P : Presentation.{u, v, w} A)

/-- The displayed degree-`i` term of the weight-`m` Koszul complex.  This is
used only in the range `i ≤ m`; the actual complex is stupidly truncated and
is a zero object above `m`. -/
abbrev Term (m i : ℕ) :=
  (⋀[ℤ]^i P.rel) ⊗[ℤ] Sym[ℤ] (Fin (m - i)) P.gen

/-- The differential between two displayed terms in the nonzero range. -/
def boundedDifferential (m i : ℕ) (h : i + 1 ≤ m) :
    Term P m (i + 1) →ₗ[ℤ] Term P m i := by
  have hq : m - (i + 1) + 1 = m - i := by omega
  exact (TensorProduct.map LinearMap.id
    (SymmetricPower.reindex (R := ℤ) (finCongr hq))).comp
      (AllDegrees.differential P.d i (m - (i + 1)))

@[simp]
theorem boundedDifferential_wedge_tmul (m i : ℕ) (h : i + 1 ≤ m)
    (a : Fin (i + 1) → P.rel)
    (s : Sym[ℤ] (Fin (m - (i + 1))) P.gen) :
    boundedDifferential P m i h
      (exteriorPower.ιMulti ℤ (i + 1) a ⊗ₜ[ℤ] s) =
      ∑ j : Fin (i + 1), ((-1 : ℤ) ^ (i - j.val)) •
        (exteriorPower.ιMulti ℤ i (j.removeNth a) ⊗ₜ[ℤ]
          SymmetricPower.reindex (R := ℤ)
            (finCongr (show m - (i + 1) + 1 = m - i by omega))
              (SymmetricPower.insert ℤ P.gen (m - (i + 1)) (P.d (a j)) s)) := by
  simp only [boundedDifferential]
  change (TensorProduct.map LinearMap.id
    (SymmetricPower.reindex (R := ℤ)
      (finCongr (show m - (i + 1) + 1 = m - i by omega))))
      (AllDegrees.differential P.d i (m - (i + 1))
        (exteriorPower.ιMulti ℤ (i + 1) a ⊗ₜ[ℤ] s)) = _
  rw [AllDegrees.differential_wedge_tmul, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  rfl

private theorem finCons_finCongr_two {M : Type u} {q r t : ℕ}
    (h₁ : q + 1 = r) (h₂ : r + 1 = t) (hout : q + 2 = t)
    (y z : M) (x : Fin q → M) :
    (Fin.cons y (Fin.cons z x ∘ (finCongr h₁).symm) ∘
        (finCongr h₂).symm) =
      (Fin.cons y (Fin.cons z x) ∘ (finCongr hout).symm) := by
  subst r
  subst t
  funext k
  simp only [Function.comp_apply, finCongr_symm, finCongr_apply]
  rcases k with ⟨k, hk⟩
  simp only [Fin.cast_mk]
  rcases k with _ | k
  · simp
  rcases k with _ | k
  · simp
  simp

/-- Consecutive displayed differentials compose to zero. -/
theorem boundedDifferential_comp (m i : ℕ) (h : i + 2 ≤ m) :
    (boundedDifferential P m i (by omega)).comp
      (boundedDifferential P m (i + 1) (by omega)) = 0 := by
  apply TensorProduct.ext'
  intro w s
  let Fw : (⋀[ℤ]^(i + 2) P.rel) →ₗ[ℤ] Term P m i :=
    ((boundedDifferential P m i (by omega)).comp
      (boundedDifferential P m (i + 1) (by omega))).comp
        ((TensorProduct.mk ℤ (⋀[ℤ]^(i + 2) P.rel) _).flip s)
  have hFw : Fw = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    let Fs : Sym[ℤ] (Fin (m - (i + 2))) P.gen →ₗ[ℤ] Term P m i :=
      ((boundedDifferential P m i (by omega)).comp
        (boundedDifferential P m (i + 1) (by omega))).comp
          (TensorProduct.mk ℤ _ _ (exteriorPower.ιMulti ℤ (i + 2) a))
    have hFs : Fs = 0 := by
      apply SymmetricPower.linearMap_ext
      intro x
      change boundedDifferential P m i (by omega)
        (boundedDifferential P m (i + 1) (by omega)
          (exteriorPower.ιMulti ℤ (i + 2) a ⊗ₜ[ℤ]
            SymmetricPower.tprod ℤ x)) = 0
      rw [boundedDifferential_wedge_tmul, map_sum]
      simp only [map_smul, boundedDifferential_wedge_tmul,
        SymmetricPower.insert_tprod, SymmetricPower.reindex_tprod]
      have hout : (m - (i + 2)) + 2 = m - i := by omega
      let castOut :
          ((⋀[ℤ]^i P.rel) ⊗[ℤ] Sym[ℤ] (Fin ((m - (i + 2)) + 2)) P.gen) →ₗ[ℤ]
            Term P m i :=
        TensorProduct.map LinearMap.id
          (SymmetricPower.reindex (R := ℤ) (finCongr hout))
      have hd := congrArg castOut
        (LinearMap.congr_fun
          (AllDegrees.differential_comp_differential P.d i (m - (i + 2)))
          (exteriorPower.ιMulti ℤ (i + 2) a ⊗ₜ[ℤ]
            SymmetricPower.tprod ℤ x))
      simp only [LinearMap.comp_apply, AllDegrees.differential_wedge_tmul,
        map_sum, map_smul] at hd
      simp only [castOut, SymmetricPower.insert_tprod] at hd
      have h₁ : m - (i + 2) + 1 = m - (i + 1) := by omega
      have h₂ : m - (i + 1) + 1 = m - i := by omega
      simp_rw [finCons_finCongr_two h₁ h₂ hout]
      simpa [castOut, Function.comp_def] using hd
    exact LinearMap.congr_fun hFs s
  exact LinearMap.congr_fun hFw w

/-- The displayed differential, extended by zero outside the weight range. -/
def rawDifferential (m i : ℕ) :
    ModuleCat.of.{max v w} ℤ (Term P m (i + 1)) ⟶
      ModuleCat.of.{max v w} ℤ (Term P m i) := by
  by_cases h : i + 1 ≤ m
  · exact ModuleCat.ofHom (boundedDifferential P m i h)
  · exact 0

theorem rawDifferential_sq (m i : ℕ) :
    rawDifferential P m (i + 1) ≫ rawDifferential P m i = 0 := by
  by_cases h : i + 2 ≤ m
  · simp only [rawDifferential, dif_pos (by omega : i + 1 + 1 ≤ m),
      dif_pos (by omega : i + 1 ≤ m)]
    apply ModuleCat.hom_ext
    change (boundedDifferential P m i (by omega)).comp
      (boundedDifferential P m (i + 1) (by omega)) = 0
    exact boundedDifferential_comp P m i h
  · simp only [rawDifferential, dif_neg (by omega : ¬i + 1 + 1 ≤ m)]
    simp

/-- An auxiliary complex with the correct differential.  The public Koszul
complex below is its standard stupid truncation. -/
def rawComplex (m : ℕ) : ChainComplex (ModuleCat.{max v w} ℤ) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of.{max v w} ℤ (Term P m i))
    (rawDifferential P m) (rawDifferential_sq P m)

abbrev BoundedIndex (m : ℕ) := {i : ℕ // i ≤ m}

private def boundedShape (m : ℕ) : ComplexShape (BoundedIndex m) where
  Rel i j := j.val + 1 = i.val
  next_eq hi hj := Subtype.ext (Nat.add_right_cancel (hi.trans hj.symm))
  prev_eq hi hj := Subtype.ext (hi.symm.trans hj)

private def weightEmbedding (m : ℕ) :
    (boundedShape m).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.Embedding.mk' (boundedShape m) (ComplexShape.down ℕ)
    Subtype.val Subtype.val_injective (fun _ _ => Iff.rfl)

private instance weightEmbedding_isRelIff (m : ℕ) :
    (weightEmbedding m).IsRelIff := by
  dsimp only [weightEmbedding]
  infer_instance

/-- The weight-`m` Koszul chain complex.  Its term at `i ≤ m` is canonically
isomorphic to `Λ^i P.rel ⊗ Sym^(m-i) P.gen`, and it is a zero object above
`m`. -/
def complex (m : ℕ) : ChainComplex (ModuleCat.{max v w} ℤ) ℕ :=
  (rawComplex P m).stupidTrunc (weightEmbedding m)

theorem complex_isZero_above (m i : ℕ) (h : m < i) :
    IsZero ((complex P m).X i) := by
  apply HomologicalComplex.isZero_stupidTrunc_X
  intro j hj
  change j.val = i at hj
  omega

/-- The canonical identification of an in-range term of the truncated complex
with the displayed Koszul module. -/
def complexTermIso (m i : ℕ) (h : i ≤ m) :
    (complex P m).X i ≅ ModuleCat.of ℤ (Term P m i) :=
  (rawComplex P m).stupidTruncXIso (weightEmbedding m)
    (i := ⟨i, h⟩) rfl

section Functoriality

variable {B : Type z} [AddCommGroup B] (Q : Presentation.{z, v, w} B)
variable {f : A →ₗ[ℤ] B} (F : Presentation.Hom P Q f)

/-- The map on a displayed Koszul term induced by a strict presentation map. -/
def termMap (m i : ℕ) : Term P m i →ₗ[ℤ] Term Q m i :=
  TensorProduct.map (exteriorPower.map i F.relMap)
    (SymmetricPower.map (R := ℤ) (ι := Fin (m - i)) F.genMap)

@[simp]
theorem termMap_wedge_tmul (m i : ℕ) (a : Fin i → P.rel)
    (s : Sym[ℤ] (Fin (m - i)) P.gen) :
    termMap P Q F m i (exteriorPower.ιMulti ℤ i a ⊗ₜ[ℤ] s) =
      exteriorPower.ιMulti ℤ i (F.relMap ∘ a) ⊗ₜ[ℤ]
        SymmetricPower.map (R := ℤ) (ι := Fin (m - i)) F.genMap s := by
  change (TensorProduct.map (exteriorPower.map i F.relMap)
      (SymmetricPower.map (R := ℤ) (ι := Fin (m - i)) F.genMap))
        (exteriorPower.ιMulti ℤ i a ⊗ₜ[ℤ] s) = _
  rw [TensorProduct.map_tmul, exteriorPower.map_apply_ιMulti]
  rfl

private theorem castTermMap_comm (m i : ℕ) (h : i + 1 ≤ m) :
    (TensorProduct.map LinearMap.id
      (SymmetricPower.reindex (R := ℤ)
        (finCongr (show m - (i + 1) + 1 = m - i by omega)))).comp
      (TensorProduct.map (exteriorPower.map i F.relMap)
        (SymmetricPower.map (R := ℤ) (ι := Fin (m - (i + 1) + 1)) F.genMap)) =
    (termMap P Q F m i).comp
      (TensorProduct.map LinearMap.id
        (SymmetricPower.reindex (R := ℤ)
          (finCongr (show m - (i + 1) + 1 = m - i by omega)))) := by
  apply TensorProduct.ext'
  intro x s
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  congr 1
  exact LinearMap.congr_fun
    (SymmetricPower.reindex_map (R := ℤ)
      (finCongr (show m - (i + 1) + 1 = m - i by omega)) F.genMap) s

theorem boundedDifferential_natural (m i : ℕ) (h : i + 1 ≤ m) :
    (boundedDifferential Q m i h).comp (termMap P Q F m (i + 1)) =
      (termMap P Q F m i).comp (boundedDifferential P m i h) := by
  have hq : m - (i + 1) + 1 = m - i := by omega
  change
    ((TensorProduct.map LinearMap.id
        (SymmetricPower.reindex (R := ℤ) (finCongr hq))).comp
      (AllDegrees.differential Q.d i (m - (i + 1)))).comp
        (termMap P Q F m (i + 1)) =
      (termMap P Q F m i).comp
        ((TensorProduct.map LinearMap.id
          (SymmetricPower.reindex (R := ℤ) (finCongr hq))).comp
        (AllDegrees.differential P.d i (m - (i + 1))))
  have hn :
      (AllDegrees.differential Q.d i (m - (i + 1))).comp
          (termMap P Q F m (i + 1)) =
        (TensorProduct.map (exteriorPower.map i F.relMap)
            (SymmetricPower.map (R := ℤ) (ι := Fin (m - (i + 1) + 1)) F.genMap)).comp
          (AllDegrees.differential P.d i (m - (i + 1))) := by
    simpa only [termMap] using
      (AllDegrees.differential_natural P.d Q.d F.relMap F.genMap F.commutes
        i (m - (i + 1)))
  let castMapQ :
      ((⋀[ℤ]^i Q.rel) ⊗[ℤ] Sym[ℤ] (Fin (m - (i + 1) + 1)) Q.gen) →ₗ[ℤ]
        Term Q m i :=
    TensorProduct.map LinearMap.id
      (SymmetricPower.reindex (R := ℤ) (finCongr hq))
  let castMapP :
      ((⋀[ℤ]^i P.rel) ⊗[ℤ] Sym[ℤ] (Fin (m - (i + 1) + 1)) P.gen) →ₗ[ℤ]
        Term P m i :=
    TensorProduct.map LinearMap.id
      (SymmetricPower.reindex (R := ℤ) (finCongr hq))
  let middleMap :
      ((⋀[ℤ]^i P.rel) ⊗[ℤ] Sym[ℤ] (Fin (m - (i + 1) + 1)) P.gen) →ₗ[ℤ]
        ((⋀[ℤ]^i Q.rel) ⊗[ℤ] Sym[ℤ] (Fin (m - (i + 1) + 1)) Q.gen) :=
    TensorProduct.map (exteriorPower.map i F.relMap)
      (SymmetricPower.map (R := ℤ) (ι := Fin (m - (i + 1) + 1)) F.genMap)
  have hc : castMapQ.comp middleMap =
      (termMap P Q F m i).comp castMapP := by
    exact castTermMap_comm P Q F m i h
  calc
    (castMapQ.comp (AllDegrees.differential Q.d i (m - (i + 1)))).comp
        (termMap P Q F m (i + 1)) =
      castMapQ.comp ((AllDegrees.differential Q.d i (m - (i + 1))).comp
        (termMap P Q F m (i + 1))) := LinearMap.comp_assoc _ _ _
    _ = castMapQ.comp (middleMap.comp
        (AllDegrees.differential P.d i (m - (i + 1)))) := by
      exact congrArg (fun k ↦ castMapQ.comp k) hn
    _ = (castMapQ.comp middleMap).comp
        (AllDegrees.differential P.d i (m - (i + 1))) :=
      (LinearMap.comp_assoc _ _ _).symm
    _ = ((termMap P Q F m i).comp castMapP).comp
        (AllDegrees.differential P.d i (m - (i + 1))) := by rw [hc]
    _ = (termMap P Q F m i).comp
        (castMapP.comp (AllDegrees.differential P.d i (m - (i + 1)))) :=
      LinearMap.comp_assoc _ _ _

/-- The map of auxiliary untruncated complexes induced by a strict
presentation map. -/
def rawComplexMap (m : ℕ) : rawComplex P m ⟶ rawComplex Q m :=
  ChainComplex.ofHom
    (fun i => ModuleCat.of.{max v w} ℤ (Term P m i))
    (rawDifferential P m) (rawDifferential_sq P m)
    (fun i => ModuleCat.of.{max v w} ℤ (Term Q m i))
    (rawDifferential Q m) (rawDifferential_sq Q m)
    (fun i => (ModuleCat.ofHom.{max v w} (termMap P Q F m i) :
      ModuleCat.of.{max v w} ℤ (Term P m i) ⟶
        ModuleCat.of.{max v w} ℤ (Term Q m i)))
    (fun i => by
      by_cases h : i + 1 ≤ m
      · simp only [rawDifferential, dif_pos h]
        apply ModuleCat.hom_ext
        exact boundedDifferential_natural P Q F m i h
      · simp only [rawDifferential, dif_neg h]
        simp)

/-- The chain map of the genuinely truncated Koszul complexes. -/
def complexMap (m : ℕ) : complex P m ⟶ complex Q m :=
  HomologicalComplex.stupidTruncMap (rawComplexMap P Q F m) (weightEmbedding m)

@[simp]
theorem termMap_id (m i : ℕ) :
    termMap P P (Presentation.Hom.id P) m i = LinearMap.id := by
  rw [termMap]
  simp only [Presentation.Hom.id, exteriorPower.map_id, SymmetricPower.map_id]
  exact TensorProduct.map_id

theorem termMap_comp {C : Type*} [AddCommGroup C] (S : Presentation C)
    {g : B →ₗ[ℤ] C} (G : Presentation.Hom Q S g) (m i : ℕ) :
    termMap P S (G.comp F) m i =
      (termMap Q S G m i).comp (termMap P Q F m i) := by
  rw [termMap, termMap, termMap, Presentation.Hom.comp]
  simp only [exteriorPower.map_comp, SymmetricPower.map_comp]
  exact TensorProduct.map_comp _ _ _ _

@[simp]
theorem rawComplexMap_id (m : ℕ) :
    rawComplexMap P P (Presentation.Hom.id P) m = 𝟙 (rawComplex P m) := by
  ext i
  change termMap P P (Presentation.Hom.id P) m i _ = _
  rw [termMap_id]
  rfl

theorem rawComplexMap_comp {C : Type u} [AddCommGroup C]
    (S : Presentation.{u, v, w} C) {g : B →ₗ[ℤ] C}
    (G : Presentation.Hom Q S g) (m : ℕ) :
    rawComplexMap P S (G.comp F) m =
      rawComplexMap P Q F m ≫ rawComplexMap Q S G m := by
  ext i
  change termMap P S (G.comp F) m i _ = _
  rw [termMap_comp]
  rfl

@[simp]
theorem complexMap_id (m : ℕ) :
    complexMap P P (Presentation.Hom.id P) m = 𝟙 (complex P m) := by
  rw [complexMap, rawComplexMap_id]
  exact HomologicalComplex.stupidTruncMap_id (rawComplex P m) (weightEmbedding m)

theorem complexMap_comp {C : Type u} [AddCommGroup C]
    (S : Presentation.{u, v, w} C) {g : B →ₗ[ℤ] C}
    (G : Presentation.Hom Q S g) (m : ℕ) :
    complexMap P S (G.comp F) m =
      complexMap P Q F m ≫ complexMap Q S G m := by
  rw [complexMap, complexMap, complexMap, rawComplexMap_comp P Q F S G]
  exact HomologicalComplex.stupidTruncMap_comp
    (rawComplexMap P Q F m) (rawComplexMap Q S G m) (weightEmbedding m)

end Functoriality

end BoundedComplex

namespace GenericDifferential

variable {R : Type} [CommRing R]
variable {Rel Gen : Type*} [AddCommGroup Rel] [AddCommGroup Gen]
  [Module R Rel] [Module R Gen]

private def term (d : Rel →ₗ[R] Gen) (q : ℕ) :
    Rel →ₗ[R] Rel →ₗ[R]
      (Sym[R] (Fin q) Gen →ₗ[R]
        Rel ⊗[R] Sym[R] (Fin (q + 1)) Gen) where
  toFun a :=
    { toFun := fun b ↦
        (TensorProduct.mk R Rel _ a).comp
          (SymmetricPower.insert R Gen q (d b))
      map_add' := by
        intro x y
        ext s
        simp [SymmetricPower.insert_add_apply, map_add, tmul_add]
      map_smul' := by
        intro r x
        ext s
        simp [SymmetricPower.insert_smul_apply, map_smul, tmul_smul] }
  map_add' := by
    intro x y
    ext b s
    simp [add_tmul]
  map_smul' := by
    intro r x
    ext b s
    simp [smul_tmul']

def alternating (d : Rel →ₗ[R] Gen) (q : ℕ) :
    Rel [⋀^Fin 2]→ₗ[R]
      (Sym[R] (Fin q) Gen →ₗ[R]
        Rel ⊗[R] Sym[R] (Fin (q + 1)) Gen) where
  toMultilinearMap :=
    MultilinearMap.mk' (fun v ↦ term d q (v 0) (v 1) - term d q (v 1) (v 0))
      (by
        intro v i x y
        fin_cases i <;> simp [Function.update] <;> abel)
      (by
        intro v i r x
        fin_cases i <;> simp [Function.update] <;> module)
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change v 0 = v 1 at hv
      change term d q (v 0) (v 1) - term d q (v 1) (v 0) = 0
      rw [hv]
      exact sub_self _
    · change v 1 = v 0 at hv
      change term d q (v 0) (v 1) - term d q (v 1) (v 0) = 0
      rw [hv]
      exact sub_self _
    · exact (hij rfl).elim

end GenericDifferential

section LowDegrees

variable {A : Type u} [AddCommGroup A] (P : Presentation A)

/-- Degree one of the weight-`q+1` Koszul complex. -/
abbrev One (q : ℕ) :=
  P.rel ⊗[ℤ] Sym[ℤ] (Fin q) P.gen

/-- Degree two of the weight-`q+2` Koszul complex. -/
abbrev Two (q : ℕ) :=
  (⋀[ℤ]^2 P.rel) ⊗[ℤ] Sym[ℤ] (Fin q) P.gen

/-- The first Koszul differential, parametrized by the remaining symmetric
degree. -/
def dOne (q : ℕ) : One P q →ₗ[ℤ] Sym[ℤ] (Fin (q + 1)) P.gen :=
  (TensorProduct.lift ((SymmetricPower.insertLinear ℤ P.gen q).comp P.d)).toAddMonoidHom.toIntLinearMap

@[simp]
theorem dOne_tmul (q : ℕ) (a : P.rel) (s : Sym[ℤ] (Fin q) P.gen) :
    dOne P q (a ⊗ₜ[ℤ] s) = SymmetricPower.insert ℤ P.gen q (P.d a) s := by
  change ((SymmetricPower.insertLinear ℤ P.gen q).comp P.d a) s = _
  rfl

/-- The degree-two formula before evaluating the symmetric tensor. -/
private def dTwoCore (q : ℕ) :
    (⋀[ℤ]^2 P.rel) →ₗ[ℤ]
      (Sym[ℤ] (Fin q) P.gen →ₗ[ℤ]
        P.rel ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) P.gen) :=
  exteriorPower.alternatingMapLinearEquiv (GenericDifferential.alternating P.d q)

/-- The second Koszul differential, with manuscript sign
`a₁ ⊗ d(a₂)u - a₂ ⊗ d(a₁)u`. -/
def dTwo (q : ℕ) : Two P q →ₗ[ℤ] One P (q + 1) :=
  (TensorProduct.lift (dTwoCore P q)).toAddMonoidHom.toIntLinearMap

@[simp]
theorem dTwo_wedge_tmul (q : ℕ) (a : Fin 2 → P.rel)
    (s : Sym[ℤ] (Fin q) P.gen) :
    dTwo P q (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s) =
      a 0 ⊗ₜ[ℤ] SymmetricPower.insert ℤ P.gen q (P.d (a 1)) s -
      a 1 ⊗ₜ[ℤ] SymmetricPower.insert ℤ P.gen q (P.d (a 0)) s := by
  change dTwoCore P q (exteriorPower.ιMulti ℤ 2 a) s = _
  change dTwoCore P q (exteriorPower.ιMulti ℤ 2 a) s = _
  have h := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (GenericDifferential.alternating P.d q) a
  calc
    dTwoCore P q (exteriorPower.ιMulti ℤ 2 a) s =
        GenericDifferential.alternating P.d q a s := by
          exact DFunLike.congr_fun h s
    _ = _ := rfl

/-- Consecutive low-degree Koszul differentials compose to zero. -/
theorem dOne_comp_dTwo (q : ℕ) :
    (dOne P (q + 1)).comp (dTwo P q) = 0 := by
  apply TensorProduct.ext'
  intro w s
  let F : (⋀[ℤ]^2 P.rel) →ₗ[ℤ] Sym[ℤ] (Fin (q + 1 + 1)) P.gen :=
    ((dOne P (q + 1)).comp (dTwo P q)).comp
      ((TensorProduct.mk ℤ (⋀[ℤ]^2 P.rel) _).flip s)
  have hF : F = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    change dOne P (q + 1)
        (dTwo P q (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s)) = 0
    rw [dTwo_wedge_tmul, map_sub, dOne_tmul, dOne_tmul]
    rw [show SymmetricPower.insert ℤ P.gen (q + 1) (P.d (a 0))
          (SymmetricPower.insert ℤ P.gen q (P.d (a 1)) s) =
        SymmetricPower.insert ℤ P.gen (q + 1) (P.d (a 1))
          (SymmetricPower.insert ℤ P.gen q (P.d (a 0)) s) by
      exact LinearMap.congr_fun
        (SymmetricPower.insert_comm ℤ P.gen q (P.d (a 0)) (P.d (a 1))) s]
    exact sub_self _
  have hs := LinearMap.congr_fun hF w
  simpa [F, LinearMap.comp_apply] using hs

/-- Degree-one cycles. -/
def cyclesOne (q : ℕ) : Submodule ℤ (One P q) := LinearMap.ker (dOne P q)

/-- The second differential with codomain restricted to cycles. -/
def boundaryMapOne (q : ℕ) : Two P (q - 1) →ₗ[ℤ] cyclesOne P q := by
  cases q with
  | zero =>
    exact 0
  | succ r =>
    exact LinearMap.codRestrict (cyclesOne P (r + 1)) (dTwo P r) (fun x ↦ by
      change dOne P (r + 1) (dTwo P r x) = 0
      exact LinearMap.congr_fun (dOne_comp_dTwo P r) x)

@[simp]
theorem boundaryMapOne_succ_val (q : ℕ) (x : Two P q) :
    (boundaryMapOne P (q + 1) x).1 = dTwo P q x := by
  rfl

/-- Degree-one boundaries, as a submodule of cycles. -/
def boundariesOne (q : ℕ) : Submodule ℤ (cyclesOne P q) :=
  LinearMap.range (boundaryMapOne P q)

/-- Elementwise degree-one Koszul homology. -/
abbrev homologyOne (q : ℕ) :=
  (cyclesOne P q) ⧸ boundariesOne P q

/-- The low-degree displayed short complex.  Its two arrows are exactly the
elementwise `d₂` (restricted to cycles) and `d₁`, with the displayed
degree-zero tensor term retained as codomain. -/
def lowDegreeBoundary (P : Presentation.{u, v, w} A) (q : ℕ) :
    Two P (q - 1) →ₗ[ℤ] One P q :=
  (cyclesOne P q).subtype.comp (boundaryMapOne P q)

noncomputable def lowDegreeTargetEquiv (P : Presentation.{u, v, w} A) (q : ℕ) :
    Term P (q + 1) 0 ≃ₗ[ℤ] Sym[ℤ] (Fin (q + 1)) P.gen :=
  (TensorProduct.congr (exteriorPower.zeroEquiv ℤ P.rel)
    (LinearEquiv.refl ℤ _)).trans (TensorProduct.lid ℤ _)

noncomputable def lowDegreeDifferential (P : Presentation.{u, v, w} A) (q : ℕ) :
    One P q →ₗ[ℤ] Term P (q + 1) 0 :=
  (lowDegreeTargetEquiv P q).symm.toLinearMap.comp (dOne P q)

def lowDegreeShortComplex (P : Presentation.{u, v, w} A) (q : ℕ) :
    CategoryTheory.ShortComplex (ModuleCat.{max v w} ℤ) :=
  CategoryTheory.ShortComplex.moduleCatMk
    (X₁ := ModuleCat.of.{max v w} ℤ (Two P (q - 1)))
    (X₂ := ModuleCat.of.{max v w} ℤ (One P q))
    (X₃ := ModuleCat.of.{max v w} ℤ (Term P (q + 1) 0))
    (lowDegreeBoundary P q) (lowDegreeDifferential P q) <| by
      apply LinearMap.ext
      intro x
      change (lowDegreeTargetEquiv P q).symm
          (dOne P q (boundaryMapOne P q x)) = 0
      rw [(boundaryMapOne P q x).property]
      exact map_zero _

/-- Elementwise cycles and the kernel chosen by the categorical short-complex
API are canonically the same module. -/
noncomputable def categoricalCyclesEquiv (q : ℕ) :
    cyclesOne P q ≃ₗ[ℤ]
      LinearMap.ker (lowDegreeShortComplex (P := P) q).g.hom where
  toFun x := ⟨(x : One P q), by
    change (lowDegreeTargetEquiv P q).symm (dOne P q (x : One P q)) = 0
    rw [x.property]
    exact map_zero _⟩
  invFun x := ⟨(x.1 : One P q), by
    change dOne P q (x.1 : One P q) = 0
    apply (lowDegreeTargetEquiv P q).symm.injective
    change (lowDegreeTargetEquiv P q).symm (dOne P q x.1) =
      (lowDegreeTargetEquiv P q).symm 0
    rw [map_zero]
    exact x.property⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' r x := by rfl

private theorem categoricalCyclesEquiv_map_boundaries (q : ℕ) :
    Submodule.map (categoricalCyclesEquiv P q).toLinearMap (boundariesOne P q) =
      LinearMap.range
        (lowDegreeShortComplex (P := P) q).moduleCatToCycles := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨z, ?_⟩
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨boundaryMapOne P q z, ⟨z, rfl⟩, ?_⟩
    rfl

/-- The explicit quotient `ker(d₁)/range(d₂)` is the categorical homology of
the displayed low-degree Koszul complex. -/
noncomputable def homologyOneIsoCategorical (q : ℕ) :
    ModuleCat.of ℤ (homologyOne P q) ≅
      (lowDegreeShortComplex (P := P) q).homology :=
  (Submodule.Quotient.equiv (boundariesOne P q)
      (LinearMap.range
        (lowDegreeShortComplex (P := P) q).moduleCatToCycles)
      (categoricalCyclesEquiv P q)
      (categoricalCyclesEquiv_map_boundaries P q)).toModuleIso ≪≫
    (CategoryTheory.ShortComplex.moduleCatHomologyIso
      (lowDegreeShortComplex (P := P) q)).symm

noncomputable def homologyOneLinearEquivCategorical (q : ℕ) :
    homologyOne P q ≃ₗ[ℤ]
      (lowDegreeShortComplex (P := P) q).homology :=
  (homologyOneIsoCategorical P q).toLinearEquiv

end LowDegrees

end

end Koszul
