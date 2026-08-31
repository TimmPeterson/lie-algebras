import LieRings.Plotkin.ReesSeparation
import LieRings.Plotkin.ReesNoetherian
import LieRings.Plotkin.Triangular
import LieRings.Plotkin.Coinduced

/-!
# Integration of Rees separation and triangular realization

This file formalizes the final, purely module-theoretic part of the central
separation argument.  Starting with a Lie map into `V ⋊ H`, it applies Rees
separation to the selected central coordinates, quotients by a power of the
augmentation ideal, and then applies the triangular realization.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

attribute [local instance 2000] LieAlgebra.ofAssociativeAlgebra

variable (H : Type u) [LieRing H]
variable (V : Type u) [AddCommGroup V]
variable [LieRingModule H V] [LieModule ℤ H V]

/-- The canonical `UEA ℤ H`-module structure associated to a Lie-module
structure. -/
@[reducible] def representationModule : Module (UEA ℤ H) V :=
  Module.compHom V (UEA.representation ℤ H V).toRingHom

local instance : Module (UEA ℤ H) V := representationModule H V

@[simp] theorem representationModule_smul (u : UEA ℤ H) (v : V) :
    u • v = UEA.representation ℤ H V u v := rfl

/-- A submodule for the enveloping action is, in particular, a Lie
submodule. -/
def ueaSubmoduleToLieSubmodule (Q : Submodule (UEA ℤ H) V) :
    LieSubmodule ℤ H V where
  toSubmodule := Q.restrictScalars ℤ
  lie_mem := by
    intro x v hv
    change ⁅x, v⁆ ∈ Q
    rw [← UEA.representation_ι_apply ℤ H V]
    change UniversalEnvelopingAlgebra.ι ℤ x • v ∈ Q
    exact Q.smul_mem _ hv

/-- The Lie submodule `I^r V`, where `I` is the augmentation ideal. -/
def augmentationPowerLieSubmodule (r : ℕ) : LieSubmodule ℤ H V :=
  ueaSubmoduleToLieSubmodule H V
    (UEA.augmentationIdeal ℤ H ^ r • (⊤ : Submodule (UEA ℤ H) V))

/-- The quotient map, with the canonical integer-module structures forced on
both sides.  This avoids the harmless but non-definitional diamond between
the quotient module structure and `AddCommGroup.toIntModule`. -/
def canonicalQuotientMk (N : LieSubmodule ℤ H V) : V →ₗ⁅ℤ,H⁆ V ⧸ N where
  toFun := LieSubmodule.Quotient.mk' N
  map_add' := map_add (LieSubmodule.Quotient.mk' N)
  map_smul' := by
    intro z v
    exact map_zsmul (LieSubmodule.Quotient.mk' N) z v
  map_lie' := by
    intro x v
    exact (LieSubmodule.Quotient.mk' N).map_lie x v

/-- The `r`th augmentation power acts trivially on `V / I^r V`. -/
theorem quotient_actionSubmodule_augmentation_pow_eq_bot (r : ℕ) :
    UEA.actionSubmodule ℤ H (V ⧸ augmentationPowerLieSubmodule H V r)
        (UEA.augmentationIdeal ℤ H ^ r)
        (⊤ : LieSubmodule ℤ H (V ⧸ augmentationPowerLieSubmodule H V r)) = ⊥ := by
  rw [UEA.actionSubmodule, eq_bot_iff, Submodule.span_le]
  rintro z ⟨u, hu, w, hw, rfl⟩
  obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk'
    (augmentationPowerLieSubmodule H V r) w
  have hcomm := LieModuleHom.map_representation
    V (canonicalQuotientMk H V (augmentationPowerLieSubmodule H V r)) u v
  change UEA.representation ℤ H (V ⧸ augmentationPowerLieSubmodule H V r) u
    ((canonicalQuotientMk H V (augmentationPowerLieSubmodule H V r)) v) = 0
  rw [← hcomm]
  change (LieSubmodule.Quotient.mk' (augmentationPowerLieSubmodule H V r))
    (UEA.representation ℤ H V u v) = 0
  rw [LieSubmodule.Quotient.mk_eq_zero]
  change u • v ∈ UEA.augmentationIdeal ℤ H ^ r •
    (⊤ : Submodule (UEA ℤ H) V)
  exact Submodule.smul_mem_smul hu (by trivial)

/-- Quotient the abelian coordinate of a semidirect product, leaving the
acting Lie ring unchanged. -/
def semidirectQuotientMap (N : LieSubmodule ℤ H V) :
    (AbelianLie V ⋊⁅abelianDerivationAction H V⁆ H) →ₗ⁅ℤ⁆
      (AbelianLie (V ⧸ N) ⋊⁅abelianDerivationAction H (V ⧸ N)⁆ H) where
  toFun e := ⟨canonicalQuotientMk H V N e.left, e.right⟩
  map_add' x y := by
    apply LieAlgebra.SemiDirectSum.ext
    · exact map_add (canonicalQuotientMk H V N) x.left y.left
    · rfl
  map_smul' z x := by
    apply LieAlgebra.SemiDirectSum.ext
    · exact map_smul (canonicalQuotientMk H V N) z x.left
    · rfl
  map_lie' {x y} := by
    apply LieAlgebra.SemiDirectSum.ext
    · simp only [LieAlgebra.SemiDirectSum.lie_eq_mk]
      change canonicalQuotientMk H V N
          (0 + ⁅x.right, (show V from y.left)⁆ -
            ⁅y.right, (show V from x.left)⁆) =
        0 + ⁅x.right, canonicalQuotientMk H V N (show V from y.left)⁆ -
          ⁅y.right, canonicalQuotientMk H V N (show V from x.left)⁆
      rw [map_sub, map_add, map_zero,
        (canonicalQuotientMk H V N).map_lie,
        (canonicalQuotientMk H V N).map_lie]
    · rfl

@[simp] theorem semidirectQuotientMap_inl (N : LieSubmodule ℤ H V)
    (v : AbelianLie V) :
    semidirectQuotientMap H V N
        (LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H V) v) =
      LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H (V ⧸ N))
        (canonicalQuotientMk H V N v) := rfl

/-- Pull a nilpotent-ideal representation back along a Lie homomorphism. -/
def NilpotentIdealRepresentation.comp
    {K K' : Type u} [LieRing K] [LieRing K']
    (P : NilpotentIdealRepresentation K') (f : K →ₗ⁅ℤ⁆ K') :
    NilpotentIdealRepresentation K where
  Target := P.Target
  targetRing := P.targetRing
  targetAlgebra := P.targetAlgebra
  ideal := P.ideal
  idealTwoSided := P.idealTwoSided
  exponent := P.exponent
  ideal_pow_eq_bot := P.ideal_pow_eq_bot
  map := P.map.comp f
  map_mem x := P.map_mem (f x)

/-- The exact last integration step in central separation.  A finite
enveloping-module coordinate representation whose chosen central subgroup
lies in an augmentation-trivial submodule can be separated in a nilpotent
associative target. -/
theorem exists_nilpotentIdealRepresentation_of_finite_semidirect_embedding
    {K : Type u} [LieRing K] (A : LieIdeal ℤ K)
    [Module.Finite (UEA ℤ H) V]
    [IsNoetherianRing (ReesRing (UEA.augmentationIdeal ℤ H))]
    (rho : K →ₗ⁅ℤ⁆ (AbelianLie V ⋊⁅abelianDerivationAction H V⁆ H))
    (f : A →ₗ[ℤ] V) (B : Submodule (UEA ℤ H) V)
    (hrho : ∀ a : A, rho (a : K) =
      LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H V) (f a))
    (hf : Function.Injective f)
    (hfB : ∀ a : A, f a ∈ B)
    (hIB : UEA.augmentationIdeal ℤ H • B = ⊥) :
    ∃ P : NilpotentIdealRepresentation K,
      Function.Injective (fun a : A ↦ P.map (a : K)) := by
  obtain ⟨r, hr⟩ := exists_pow_smul_inf_eq_bot_of_rees_noetherian
    (V := V) (UEA.augmentationIdeal ℤ H) B hIB
  let N : LieSubmodule ℤ H V := augmentationPowerLieSubmodule H V r
  let qrho : K →ₗ⁅ℤ⁆
      (AbelianLie (V ⧸ N) ⋊⁅abelianDerivationAction H (V ⧸ N)⁆ H) :=
    (semidirectQuotientMap H V N).comp rho
  obtain ⟨P, hPinj⟩ := exists_triangular_nilpotentIdealRepresentation
    H (V ⧸ N) r (by
      simpa only [N] using quotient_actionSubmodule_augmentation_pow_eq_bot H V r)
  let PK : NilpotentIdealRepresentation K := P.comp qrho
  refine ⟨PK, ?_⟩
  intro a b hab
  have hP : P.map
        (LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H (V ⧸ N))
          (canonicalQuotientMk H V N (f a))) =
      P.map
        (LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H (V ⧸ N))
          (canonicalQuotientMk H V N (f b))) := by
    change P.map ((semidirectQuotientMap H V N) (rho (a : K))) =
      P.map ((semidirectQuotientMap H V N) (rho (b : K))) at hab
    rw [hrho a, hrho b, semidirectQuotientMap_inl,
      semidirectQuotientMap_inl] at hab
    exact hab
  have hq : canonicalQuotientMk H V N (f a) =
      canonicalQuotientMk H V N (f b) := hPinj hP
  have hdiffN : f a - f b ∈ N := by
    rw [← LieSubmodule.Quotient.mk_eq_zero]
    change canonicalQuotientMk H V N (f a - f b) = 0
    rw [map_sub, hq, sub_self]
  have hdiff : f a - f b ∈
      B ⊓ (UEA.augmentationIdeal ℤ H ^ r •
        (⊤ : Submodule (UEA ℤ H) V)) := by
    constructor
    · exact B.sub_mem (hfB a) (hfB b)
    · exact hdiffN
  rw [hr] at hdiff
  have hfab : f a = f b := sub_eq_zero.mp hdiff
  exact hf hfab

/-! ## Packaged central-separation interface -/

/-- All data needed after choosing the finite coordinate module in the
central-separation proof.  The Noetherian hypothesis is recorded in its
manuscript form: the acting Lie ring is finitely generated and nilpotent. -/
structure FiniteSemidirectCentralCoordinates
    (K : Type u) [LieRing K] (A : LieIdeal ℤ K) where
  H : Type u
  [lieRingH : LieRing H]
  V : Type u
  [addCommGroupV : AddCommGroup V]
  [lieRingModuleV : LieRingModule H V]
  [lieModuleV : LieModule ℤ H V]
  [finiteV : Module.Finite (UEA ℤ H) V]
  hHfg : IsFinitelyGenerated H
  nilpotencyClass : ℕ
  hHclass : lowerCentralSeries ℤ H nilpotencyClass = ⊥
  rho : K →ₗ⁅ℤ⁆ (AbelianLie V ⋊⁅abelianDerivationAction H V⁆ H)
  coordinate : A →ₗ[ℤ] V
  selected : Submodule (UEA ℤ H) V
  rho_on_A : ∀ a : A, rho (a : K) =
    LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H V) (coordinate a)
  coordinate_injective : Function.Injective coordinate
  coordinate_mem_selected : ∀ a : A, coordinate a ∈ selected
  augmentation_smul_selected : UEA.augmentationIdeal ℤ H • selected = ⊥

namespace FiniteSemidirectCentralCoordinates

instance {K : Type u} [LieRing K] {A : LieIdeal ℤ K}
    (D : FiniteSemidirectCentralCoordinates K A) : LieRing D.H := D.lieRingH

instance {K : Type u} [LieRing K] {A : LieIdeal ℤ K}
    (D : FiniteSemidirectCentralCoordinates K A) : AddCommGroup D.V :=
  D.addCommGroupV

instance {K : Type u} [LieRing K] {A : LieIdeal ℤ K}
    (D : FiniteSemidirectCentralCoordinates K A) : LieRingModule D.H D.V :=
  D.lieRingModuleV

instance {K : Type u} [LieRing K] {A : LieIdeal ℤ K}
    (D : FiniteSemidirectCentralCoordinates K A) : LieModule ℤ D.H D.V :=
  D.lieModuleV

local instance {K : Type u} [LieRing K] {A : LieIdeal ℤ K}
    (D : FiniteSemidirectCentralCoordinates K A) : Module (UEA ℤ D.H) D.V :=
  representationModule D.H D.V

instance {K : Type u} [LieRing K] {A : LieIdeal ℤ K}
    (D : FiniteSemidirectCentralCoordinates K A) :
    Module.Finite (UEA ℤ D.H) D.V := D.finiteV

/-- The packaged coordinate data separates its specified central ideal. -/
theorem separate {K : Type u} [LieRing K] {A : LieIdeal ℤ K}
    (D : FiniteSemidirectCentralCoordinates K A) :
    ∃ P : NilpotentIdealRepresentation K,
      Function.Injective (fun a : A ↦ P.map (a : K)) := by
  letI : IsNoetherianRing (ReesRing (UEA.augmentationIdeal ℤ D.H)) :=
    isNoetherianRing_augmentationRees_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
      D.hHfg D.nilpotencyClass D.hHclass
  exact exists_nilpotentIdealRepresentation_of_finite_semidirect_embedding
    D.H D.V A D.rho D.coordinate D.selected D.rho_on_A
    D.coordinate_injective D.coordinate_mem_selected D.augmentation_smul_selected

end FiniteSemidirectCentralCoordinates

/-- Central-prime separation follows once the finite coordinate data is
available for each central subgroup of prime order. -/
theorem hasCentralPrimeSeparation_of_finiteSemidirectCentralCoordinates
    {K : Type u} [LieRing K]
    (h : ∀ (p : ℕ) (A : LieIdeal ℤ K), p.Prime → Nat.card A = p →
      A ≤ LieAlgebra.center ℤ K →
      Nonempty (FiniteSemidirectCentralCoordinates K A)) :
    HasCentralPrimeSeparation K := by
  intro p A hp hcard hcentral
  obtain ⟨D⟩ := h p A hp hcard hcentral
  exact D.separate

end

end LieRings.Plotkin
