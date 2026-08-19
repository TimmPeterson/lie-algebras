import LieRings.Homological.FirstDerivedSymmetricPower
import Mathlib.Algebra.Module.Projective

/-!
# Contractible summands and cylinders of two-term presentations

This file contains the strict presentation-level objects used in the integral
stabilization argument.  No assertion about Koszul homology is made until the
chain contraction has been constructed.
-/

namespace Koszul

universe u v w t

noncomputable section

namespace Presentation

variable {A : Type u} [AddCommGroup A]
variable (P : Presentation.{u, v, w} A)
variable (T : Type t) [AddCommGroup T] [Module.Free ℤ T] [Module.Finite ℤ T]

private def sumDifferential : (P.rel × T) →ₗ[ℤ] (P.gen × T) where
  toFun x := (P.d x.1, x.2)
  map_add' x y := by ext <;> simp
  map_smul' z x := by ext <;> simp

private def sumAugmentation : (P.gen × T) →ₗ[ℤ] A where
  toFun x := P.augmentation x.1
  map_add' x y := by simp
  map_smul' z x := by simp

/-- Adjoin the contractible presentation `T --id--> T`. -/
def stabilize : Presentation A where
  rel := P.rel × T
  gen := P.gen × T
  relAddCommGroup := inferInstance
  genAddCommGroup := inferInstance
  relFree := inferInstance
  genFree := inferInstance
  relFinite := inferInstance
  genFinite := inferInstance
  d := sumDifferential P T
  augmentation := sumAugmentation P T
  d_injective := by
    intro x y h
    rcases x with ⟨xr, xt⟩
    rcases y with ⟨yr, yt⟩
    change (P.d xr, xt) = (P.d yr, yt) at h
    exact Prod.ext (P.d_injective (Prod.mk.inj h).1) (Prod.mk.inj h).2
  augmentation_surjective := by
    intro a
    obtain ⟨x, rfl⟩ := P.augmentation_surjective a
    exact ⟨(x, 0), rfl⟩
  exact := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change P.augmentation (P.d y.1) = 0
      exact P.augmentation_d y.1
    · intro hx
      change P.augmentation x.1 = 0 at hx
      have hx' : x.1 ∈ LinearMap.ker P.augmentation := hx
      rw [← P.exact] at hx'
      obtain ⟨r, hr⟩ := hx'
      exact ⟨(r, x.2), Prod.ext hr rfl⟩

@[simp]
theorem stabilize_d_apply (x : P.rel × T) :
    (stabilize P T).d x = (P.d x.1, x.2) := rfl

@[simp]
theorem stabilize_augmentation_apply (x : P.gen × T) :
    (stabilize P T).augmentation x = P.augmentation x.1 := rfl

/-- Projection away from a contractible summand. -/
def stabilizeProj : Hom (stabilize P T) P LinearMap.id where
  relMap := LinearMap.fst ℤ P.rel T
  genMap := LinearMap.fst ℤ P.gen T
  commutes := by ext x; rfl
  induces := by ext x; rfl

/-- The zero-section of a stabilized presentation. -/
def stabilizeIncl : Hom P (stabilize P T) LinearMap.id where
  relMap := {
    toFun := fun r ↦ (r, 0)
    map_add' := by intro x y; change (x + y, 0) = (x + y, 0 + 0); simp
    map_smul' := by intro z x; change (z • x, 0) = (z • x, z • (0 : T)); simp }
  genMap := {
    toFun := fun x ↦ (x, 0)
    map_add' := by intro x y; change (x + y, 0) = (x + y, 0 + 0); simp
    map_smul' := by intro z x; change (z • x, 0) = (z • x, z • (0 : T)); simp }
  commutes := by ext x <;> rfl
  induces := by ext x; rfl

@[simp]
theorem stabilizeProj_comp_stabilizeIncl :
    (stabilizeProj P T).comp (stabilizeIncl P T) = Hom.id P := by
  apply Hom.ext <;> ext x <;> rfl

/-- The cylinder presentation `P ⊕ (P.gen --id--> P.gen)`. -/
abbrev cylinder : Presentation A := stabilize P P.gen

/-- The second endpoint of the presentation cylinder. -/
def cylinderInclOne : Hom P (cylinder P) LinearMap.id where
  relMap := {
    toFun := fun r ↦ (r, P.d r)
    map_add' := by intro x y; change (x + y, P.d (x + y)) = (x + y, P.d x + P.d y); rw [map_add]
    map_smul' := by intro z x; change (z • x, P.d (z • x)) = (z • x, z • P.d x); rw [map_zsmul] }
  genMap := {
    toFun := fun x ↦ (x, x)
    map_add' := by intro x y; rfl
    map_smul' := by intro z x; rfl }
  commutes := by ext x <;> rfl
  induces := by ext x; rfl

/-- The zero endpoint of the presentation cylinder. -/
abbrev cylinderInclZero : Hom P (cylinder P) LinearMap.id :=
  stabilizeIncl P P.gen

/-- Cylinder retraction. -/
abbrev cylinderRetract : Hom (cylinder P) P LinearMap.id :=
  stabilizeProj P P.gen

@[simp]
theorem cylinderRetract_comp_zero :
    (cylinderRetract P).comp (cylinderInclZero P) = Hom.id P :=
  stabilizeProj_comp_stabilizeIncl P P.gen

@[simp]
theorem cylinderRetract_comp_one :
    (cylinderRetract P).comp (cylinderInclOne P) = Hom.id P := by
  apply Hom.ext <;> ext x <;> rfl

/-- A presentation homotopy between strict maps. -/
structure Homotopy {B : Type*} [AddCommGroup B]
    (Q : Presentation B) {f : A →ₗ[ℤ] B}
    (F G : Hom P Q f) where
  h : P.gen →ₗ[ℤ] Q.rel
  gen_sub : F.genMap - G.genMap = Q.d.comp h
  rel_sub : F.relMap - G.relMap = h.comp P.d

/-- Any two strict lifts of the same cokernel map are presentation-homotopic.
The lift through `Q.d` uses projectivity of the finite free module `P.gen`. -/
theorem homotopy_exists {B : Type*} [AddCommGroup B]
    (Q : Presentation B) {f : A →ₗ[ℤ] B} (F G : Hom P Q f) :
    Nonempty (Homotopy P Q F G) := by
  let u : P.gen →ₗ[ℤ] Q.gen := F.genMap - G.genMap
  have hu (x : P.gen) : u x ∈ LinearMap.range Q.d := by
    rw [Q.exact]
    change Q.augmentation (F.genMap x - G.genMap x) = 0
    rw [map_sub, show Q.augmentation (F.genMap x) = f (P.augmentation x) by
      exact LinearMap.congr_fun F.induces x,
      show Q.augmentation (G.genMap x) = f (P.augmentation x) by
      exact LinearMap.congr_fun G.induces x, sub_self]
  let uRange : P.gen →ₗ[ℤ] LinearMap.range Q.d :=
    LinearMap.codRestrict (LinearMap.range Q.d) u hu
  let dRange : Q.rel →ₗ[ℤ] LinearMap.range Q.d :=
    LinearMap.codRestrict (LinearMap.range Q.d) Q.d (fun x ↦ ⟨x, rfl⟩)
  have hdRange : Function.Surjective dRange := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨h, hh⟩ := Module.projective_lifting_property dRange uRange hdRange
  refine ⟨⟨h, ?_, ?_⟩⟩
  · apply LinearMap.ext
    intro x
    have hx := congrArg Subtype.val (LinearMap.congr_fun hh x)
    change u x = Q.d (h x)
    exact hx.symm
  · apply LinearMap.ext
    intro r
    apply Q.d_injective
    change Q.d (F.relMap r - G.relMap r) = Q.d (h (P.d r))
    rw [map_sub]
    rw [show Q.d (F.relMap r) = F.genMap (P.d r) by
      exact LinearMap.congr_fun F.commutes r,
      show Q.d (G.relMap r) = G.genMap (P.d r) by
      exact LinearMap.congr_fun G.commutes r]
    have hx := congrArg Subtype.val (LinearMap.congr_fun hh (P.d r))
    exact hx.symm

/-- A homomorphism of the presented additive groups admits a strict lift to
any pair of finite free two-term presentations.  The degree-zero lift uses
projectivity; exactness and injectivity then force its degree-one part. -/
theorem hom_nonempty {B : Type*} [AddCommGroup B]
    (Q : Presentation B) (f : A →ₗ[ℤ] B) :
    Nonempty (Hom P Q f) := by
  let target : P.gen →ₗ[ℤ] B := f.comp P.augmentation
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    Q.augmentation target Q.augmentation_surjective
  let dRange : Q.rel →ₗ[ℤ] LinearMap.range Q.d :=
    LinearMap.codRestrict (LinearMap.range Q.d) Q.d (fun x ↦ ⟨x, rfl⟩)
  have hdRange : Function.Bijective dRange := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply Q.d_injective
      exact congrArg Subtype.val hxy
    · rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
  let dEquiv : Q.rel ≃ₗ[ℤ] LinearMap.range Q.d :=
    LinearEquiv.ofBijective dRange hdRange
  have hgd (r : P.rel) : g (P.d r) ∈ LinearMap.range Q.d := by
    rw [Q.exact]
    change Q.augmentation (g (P.d r)) = 0
    have h := LinearMap.congr_fun hg (P.d r)
    change Q.augmentation (g (P.d r)) = target (P.d r) at h
    rw [h]
    change f (P.augmentation (P.d r)) = 0
    rw [P.augmentation_d, map_zero]
  let gdRange : P.rel →ₗ[ℤ] LinearMap.range Q.d :=
    LinearMap.codRestrict (LinearMap.range Q.d) (g.comp P.d) hgd
  let r : P.rel →ₗ[ℤ] Q.rel := dEquiv.symm.toLinearMap.comp gdRange
  refine ⟨{
    relMap := r
    genMap := g
    commutes := ?_
    induces := ?_ }⟩
  · apply LinearMap.ext
    intro x
    have hx := congrArg Subtype.val (dEquiv.apply_symm_apply (gdRange x))
    exact hx
  · exact hg

/-- Composition with a presentation map inducing the identity, retaining the
original cokernel map in the dependent index. -/
def compRightId {B : Type*} [AddCommGroup B]
    {Q : Presentation A} {S : Presentation B}
    {f : A →ₗ[ℤ] B} (G : Hom Q S f) (F : Hom P Q LinearMap.id) :
    Hom P S f where
  relMap := G.relMap.comp F.relMap
  genMap := G.genMap.comp F.genMap
  commutes := by
    ext x
    change S.d (G.relMap (F.relMap x)) = G.genMap (F.genMap (P.d x))
    rw [show S.d (G.relMap (F.relMap x)) =
        G.genMap (Q.d (F.relMap x)) by
      exact LinearMap.congr_fun G.commutes (F.relMap x)]
    exact congrArg G.genMap (LinearMap.congr_fun F.commutes x)
  induces := by
    ext x
    change S.augmentation (G.genMap (F.genMap x)) = f (P.augmentation x)
    rw [show S.augmentation (G.genMap (F.genMap x)) =
        f (Q.augmentation (F.genMap x)) by
      exact LinearMap.congr_fun G.induces (F.genMap x)]
    exact congrArg f (LinearMap.congr_fun F.induces x)

/-- A presentation homotopy gives the strict map out of the cylinder whose
two endpoint restrictions are the original maps. -/
def Homotopy.cylinderMap {B : Type*} [AddCommGroup B]
    (Q : Presentation B) {f : A →ₗ[ℤ] B}
    {F G : Hom P Q f} (H : Homotopy P Q F G) : Hom (cylinder P) Q f where
  relMap := {
    toFun := fun x ↦ G.relMap x.1 + H.h x.2
    map_add' := by
      intro x y
      change G.relMap (x.1 + y.1) + H.h (x.2 + y.2) =
        (G.relMap x.1 + H.h x.2) + (G.relMap y.1 + H.h y.2)
      rw [map_add, map_add]
      abel
    map_smul' := by
      intro z x
      change G.relMap (z • x.1) + H.h (z • x.2) =
        z • (G.relMap x.1 + H.h x.2)
      rw [map_zsmul, map_zsmul]
      exact (smul_add z _ _).symm }
  genMap := {
    toFun := fun x ↦ G.genMap x.1 + Q.d (H.h x.2)
    map_add' := by
      intro x y
      change G.genMap (x.1 + y.1) + Q.d (H.h (x.2 + y.2)) =
        (G.genMap x.1 + Q.d (H.h x.2)) +
          (G.genMap y.1 + Q.d (H.h y.2))
      rw [map_add, map_add, map_add]
      abel
    map_smul' := by
      intro z x
      change G.genMap (z • x.1) + Q.d (H.h (z • x.2)) =
        z • (G.genMap x.1 + Q.d (H.h x.2))
      rw [map_zsmul, map_zsmul, map_zsmul]
      exact (smul_add z _ _).symm }
  commutes := by
    ext x
    change Q.d (G.relMap x.1 + H.h x.2) =
      G.genMap (P.d x.1) + Q.d (H.h x.2)
    rw [map_add, show Q.d (G.relMap x.1) = G.genMap (P.d x.1) by
      exact LinearMap.congr_fun G.commutes x.1]
  induces := by
    ext x
    change Q.augmentation (G.genMap x.1 + Q.d (H.h x.2)) =
      f (P.augmentation x.1)
    rw [map_add, Q.augmentation_d, add_zero]
    exact LinearMap.congr_fun G.induces x.1

theorem Homotopy.cylinderMap_comp_zero {B : Type*} [AddCommGroup B]
    (Q : Presentation B) {f : A →ₗ[ℤ] B}
    {F G : Hom P Q f} (H : Homotopy P Q F G) :
    compRightId P (Homotopy.cylinderMap P Q H) (cylinderInclZero P) = G := by
  apply Hom.ext <;> ext x <;>
    simp [compRightId, Homotopy.cylinderMap, cylinderInclZero, stabilizeIncl]

theorem Homotopy.cylinderMap_comp_one {B : Type*} [AddCommGroup B]
    (Q : Presentation B) {f : A →ₗ[ℤ] B}
    {F G : Hom P Q f} (H : Homotopy P Q F G) :
    compRightId P (Homotopy.cylinderMap P Q H) (cylinderInclOne P) = F := by
  apply Hom.ext
  · ext r
    change G.relMap r + H.h (P.d r) = F.relMap r
    have h := LinearMap.congr_fun H.rel_sub r
    change F.relMap r - G.relMap r = H.h (P.d r) at h
    rw [← h]
    abel
  · ext x
    change G.genMap x + Q.d (H.h x) = F.genMap x
    have h := LinearMap.congr_fun H.gen_sub x
    change F.genMap x - G.genMap x = Q.d (H.h x) at h
    rw [← h]
    abel

end Presentation

end

end Koszul
