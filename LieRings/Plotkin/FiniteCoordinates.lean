import LieRings.Plotkin.SeparationIntegration
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite coordinate modules in a semidirect product

This file implements the finite-coordinate choice in the proof of central separation.  If the
underlying additive group of `K` is finite over `ℤ`, then the first coordinates of a finite
additive generating family generate a finite `U(H)`-submodule.  Restricting a map
`K → J ⋊ H` to this submodule loses no element of `K`.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

variable (H : Type u) [LieRing H]
variable (J : Type u) [AddCommGroup J]
variable [LieRingModule H J] [LieModule ℤ H J]

local instance : Module (UEA ℤ H) J := representationModule H J

/-- The first coordinates of a finite additive generating family, closed under the enveloping
action. -/
def finiteCoordinateSpan {K : Type u} [LieRing K]
    (rho : K →ₗ⁅ℤ⁆
      (AbelianLie J ⋊⁅abelianDerivationAction H J⁆ H))
    {n : ℕ} (generators : Fin n → K) : Submodule (UEA ℤ H) J :=
  Submodule.span (UEA ℤ H)
    (Set.range fun i ↦ (show J from (rho (generators i)).left))

/-- The same coordinate span, regarded as a Lie submodule. -/
def finiteCoordinateLieSubmodule {K : Type u} [LieRing K]
    (rho : K →ₗ⁅ℤ⁆
      (AbelianLie J ⋊⁅abelianDerivationAction H J⁆ H))
    {n : ℕ} (generators : Fin n → K) : LieSubmodule ℤ H J :=
  ueaSubmoduleToLieSubmodule H J (finiteCoordinateSpan H J rho generators)

/-- Every first coordinate belongs to the enveloping span of the first coordinates of any
additive spanning family. -/
theorem left_mem_finiteCoordinateSpan {K : Type u} [LieRing K]
    (rho : K →ₗ⁅ℤ⁆
      (AbelianLie J ⋊⁅abelianDerivationAction H J⁆ H))
    {n : ℕ} (generators : Fin n → K)
    (hgenerators : Submodule.span ℤ (Set.range generators) = ⊤)
    (k : K) :
    (show J from (rho k).left) ∈ finiteCoordinateSpan H J rho generators := by
  let Q := finiteCoordinateSpan H J rho generators
  have hk : k ∈ Submodule.span ℤ (Set.range generators) := by
    rw [hgenerators]
    trivial
  induction hk using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
      change (show J from (rho 0).left) ∈ Q
      rw [map_zero]
      change (0 : J) ∈ Q
      exact Q.zero_mem
  | add x y _ _ hx hy =>
      change (show J from (rho (x + y)).left) ∈ Q
      simpa using Q.add_mem hx hy
  | smul z x _ hx =>
      change (show J from (rho (z • x)).left) ∈ Q
      have hz := Q.smul_mem (algebraMap ℤ (UEA ℤ H) z) hx
      simpa [representationModule_smul,
        UEA.representation_algebraMap_apply] using hz

/-- The finite coordinate Lie submodule is finite over `U(H)`, for the canonical enveloping
module structure induced by its Lie action. -/
theorem finite_coordinate_module {K : Type u} [LieRing K]
    (rho : K →ₗ⁅ℤ⁆
      (AbelianLie J ⋊⁅abelianDerivationAction H J⁆ H))
    {n : ℕ} (generators : Fin n → K) :
    let V := finiteCoordinateLieSubmodule H J rho generators
    letI : Module (UEA ℤ H) V := representationModule H V
    Module.Finite (UEA ℤ H) V := by
  let Q := finiteCoordinateSpan H J rho generators
  let V := finiteCoordinateLieSubmodule H J rho generators
  letI : Module (UEA ℤ H) V := representationModule H V
  let g : Fin n → V := fun i ↦
    ⟨(show J from (rho (generators i)).left),
      Submodule.subset_span ⟨i, rfl⟩⟩
  have hspan : Submodule.span (UEA ℤ H) (Set.range g) = ⊤ := by
    apply top_unique
    intro v hv
    change v ∈ Submodule.span (UEA ℤ H) (Set.range g)
    have hvQ : (v : J) ∈ Q := v.property
    refine Submodule.span_induction
      (p := fun x hx ↦ (⟨x, hx⟩ : V) ∈
        Submodule.span (UEA ℤ H) (Set.range g)) ?_ ?_ ?_ ?_ hvQ
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    · change (0 : V) ∈ Submodule.span (UEA ℤ H) (Set.range g)
      exact (Submodule.span (UEA ℤ H) (Set.range g)).zero_mem
    · intro x y hx hy ihx ihy
      simpa using
        (Submodule.span (UEA ℤ H) (Set.range g)).add_mem ihx ihy
    · intro a x hx ih
      have hsmul :=
        (Submodule.span (UEA ℤ H) (Set.range g)).smul_mem a ih
      have hcomm := LieModuleHom.map_representation V V.incl a
        (⟨x, hx⟩ : V)
      have heq : (⟨a • x, Q.smul_mem a hx⟩ : V) =
          a • (⟨x, hx⟩ : V) := by
        apply Subtype.ext
        simpa [representationModule_smul] using hcomm.symm
      rw [heq]
      exact hsmul
  change Module.Finite (UEA ℤ H) V
  refine Module.Finite.of_fg_top ?_
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range g)

/-- Restrict a semidirect-product map to its finite coordinate module. -/
def restrictToFiniteCoordinates {K : Type u} [LieRing K]
    (rho : K →ₗ⁅ℤ⁆
      (AbelianLie J ⋊⁅abelianDerivationAction H J⁆ H))
    {n : ℕ} (generators : Fin n → K)
    (hgenerators : Submodule.span ℤ (Set.range generators) = ⊤) :
    K →ₗ⁅ℤ⁆
      (AbelianLie (finiteCoordinateLieSubmodule H J rho generators) ⋊⁅
        abelianDerivationAction H
          (finiteCoordinateLieSubmodule H J rho generators)⁆ H) where
  toFun k :=
    ⟨⟨(show J from (rho k).left),
        left_mem_finiteCoordinateSpan H J rho generators hgenerators k⟩,
      (rho k).right⟩
  map_add' x y := by
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact congrArg LieAlgebra.SemiDirectSum.left (map_add rho x y)
    · change (rho (x + y)).right = (rho x).right + (rho y).right
      exact congrArg LieAlgebra.SemiDirectSum.right (map_add rho x y)
  map_smul' z x := by
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact congrArg LieAlgebra.SemiDirectSum.left (map_smul rho z x)
    · change (rho (z • x)).right = z • (rho x).right
      exact congrArg LieAlgebra.SemiDirectSum.right (map_smul rho z x)
  map_lie' {x y} := by
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact congrArg LieAlgebra.SemiDirectSum.left (LieHom.map_lie rho x y)
    · change (rho ⁅x, y⁆).right = ⁅(rho x).right, (rho y).right⁆
      exact congrArg LieAlgebra.SemiDirectSum.right (LieHom.map_lie rho x y)

@[simp]
theorem restrictToFiniteCoordinates_left {K : Type u} [LieRing K]
    (rho : K →ₗ⁅ℤ⁆
      (AbelianLie J ⋊⁅abelianDerivationAction H J⁆ H))
    {n : ℕ} (generators : Fin n → K)
    (hgenerators : Submodule.span ℤ (Set.range generators) = ⊤)
    (k : K) :
    ((show finiteCoordinateLieSubmodule H J rho generators from
      (restrictToFiniteCoordinates H J rho generators hgenerators k).left) : J) =
      (rho k).left :=
  rfl

@[simp]
theorem restrictToFiniteCoordinates_right {K : Type u} [LieRing K]
    (rho : K →ₗ⁅ℤ⁆
      (AbelianLie J ⋊⁅abelianDerivationAction H J⁆ H))
    {n : ℕ} (generators : Fin n → K)
    (hgenerators : Submodule.span ℤ (Set.range generators) = ⊤)
    (k : K) :
    (restrictToFiniteCoordinates H J rho generators hgenerators k).right =
      (rho k).right :=
  rfl

/-! ## Augmentation-trivial coordinates -/

/-- The largest submodule annihilated by the augmentation ideal. -/
def augmentationAnnihilatedSubmodule
    (V : Type u) [AddCommGroup V] [LieRingModule H V] [LieModule ℤ H V] :
    letI : Module (UEA ℤ H) V := representationModule H V
    Submodule (UEA ℤ H) V := by
  letI : Module (UEA ℤ H) V := representationModule H V
  exact
    { carrier := {v | ∀ u, u ∈ UEA.augmentationIdeal ℤ H → u • v = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy u hu
        rw [smul_add, hx u hu, hy u hu, add_zero]
      smul_mem' := by
        intro a v hv u hu
        rw [smul_smul]
        exact hv (u * a)
          ((UEA.augmentationIdeal ℤ H).mul_mem_right a hu) }

/-- By definition, multiplying the augmentation-annihilated submodule by the augmentation ideal
gives zero. -/
theorem augmentationIdeal_smul_augmentationAnnihilatedSubmodule_eq_bot
    (V : Type u) [AddCommGroup V] [LieRingModule H V] [LieModule ℤ H V] :
    letI : Module (UEA ℤ H) V := representationModule H V
    UEA.augmentationIdeal ℤ H • augmentationAnnihilatedSubmodule H V = ⊥ := by
  letI : Module (UEA ℤ H) V := representationModule H V
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro u hu v hv
    exact hv u hu
  · intro x y hx hy
    rw [hx, hy, add_zero]

/-- The complete finite-coordinate package used by central separation.  It is obtained directly
from an additively finite semidirect representation whose selected coordinates are killed by the
augmentation ideal. -/
theorem exists_finiteSemidirectCentralCoordinates_of_additiveFinite
    {K : Type u} [LieRing K] [Module.Finite ℤ K]
    (hHfg : IsFinitelyGenerated H) (c : ℕ)
    (hHclass : lowerCentralSeries ℤ H c = ⊥)
    (rho : K →ₗ⁅ℤ⁆
      (AbelianLie J ⋊⁅abelianDerivationAction H J⁆ H))
    (A : LieIdeal ℤ K) (f : A →ₗ[ℤ] J)
    (hrho : ∀ a : A, rho (a : K) =
      LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H J) (f a))
    (hf : Function.Injective f)
    (hann : ∀ (u : UEA ℤ H), u ∈ UEA.augmentationIdeal ℤ H →
      ∀ a : A, UEA.representation ℤ H J u (f a) = 0) :
    Nonempty (FiniteSemidirectCentralCoordinates K A) := by
  obtain ⟨n, generators, hgenerators⟩ := Module.Finite.exists_fin (R := ℤ) (M := K)
  let V : LieSubmodule ℤ H J :=
    finiteCoordinateLieSubmodule H J rho generators
  letI : Module (UEA ℤ H) V := representationModule H V
  letI : Module.Finite (UEA ℤ H) V :=
    finite_coordinate_module H J rho generators
  let rhoV : K →ₗ⁅ℤ⁆
      (AbelianLie V ⋊⁅abelianDerivationAction H V⁆ H) :=
    restrictToFiniteCoordinates H J rho generators hgenerators
  have hfmem (a : A) : f a ∈ finiteCoordinateSpan H J rho generators := by
    have hmem := left_mem_finiteCoordinateSpan H J rho generators
      hgenerators (a : K)
    rw [hrho a] at hmem
    exact hmem
  let fV : A →ₗ[ℤ] V :=
    { toFun := fun a ↦ ⟨f a, hfmem a⟩
      map_add' := by intro a b; apply Subtype.ext; exact map_add f a b
      map_smul' := by intro z a; apply Subtype.ext; exact map_smul f z a }
  have hrhoV (a : A) : rhoV (a : K) =
      LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H V) (fV a) := by
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      have h := congrArg LieAlgebra.SemiDirectSum.left (hrho a)
      exact h
    · change (rho (a : K)).right = 0
      exact congrArg LieAlgebra.SemiDirectSum.right (hrho a)
  have hfV : Function.Injective fV := by
    intro a b hab
    apply hf
    exact congrArg Subtype.val hab
  have hannV (u : UEA ℤ H) (hu : u ∈ UEA.augmentationIdeal ℤ H)
      (a : A) : UEA.representation ℤ H V u (fV a) = 0 := by
    apply V.injective_incl
    rw [LieModuleHom.map_representation]
    exact hann u hu a
  let B : Submodule (UEA ℤ H) V := augmentationAnnihilatedSubmodule H V
  have hfVB (a : A) : fV a ∈ B := by
    intro u hu
    change UEA.representation ℤ H V u (fV a) = 0
    exact hannV u hu a
  refine ⟨
    { H := H
      V := V
      finiteV := inferInstance
      hHfg := hHfg
      nilpotencyClass := c
      hHclass := hHclass
      rho := rhoV
      coordinate := fV
      selected := B
      rho_on_A := hrhoV
      coordinate_injective := hfV
      coordinate_mem_selected := hfVB
      augmentation_smul_selected := ?_ }⟩
  exact augmentationIdeal_smul_augmentationAnnihilatedSubmodule_eq_bot H V

end

end LieRings.Plotkin
