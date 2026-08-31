import LieRings.Plotkin.CentralEmbedding
import LieRings.Plotkin.FiniteCoordinates

/-!
# Finite coordinates for the coinduced central embedding

This file connects the concrete coinduced embedding of a central extension to
the finite-coordinate package used by the Plotkin separation argument.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

namespace Coinduced

variable (H : Type u) [LieRing H]
variable (D : Type u) [AddCommGroup D]

/-- The explicitly defined action on the coinduced module is the canonical
action used for an abelian semidirect product. -/
theorem derivationAction_eq_abelianDerivationAction :
    derivationAction H D = abelianDerivationAction H (Coinduced H D) := by
  ext x alpha a
  rfl

/-- The identity on both coordinates, as a map between the two presentations
of the coinduced semidirect product. -/
def semidirectMap :
    ((Coinduced H D) ⋊⁅derivationAction H D⁆ H) →ₗ⁅ℤ⁆
      (AbelianLie (Coinduced H D) ⋊⁅
        abelianDerivationAction H (Coinduced H D)⁆ H) where
  toFun x := ⟨x.left, x.right⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {x y} := by
    apply LieAlgebra.SemiDirectSum.ext
    · change
        (0 : Coinduced H D) + derivationAction H D x.right y.left -
            derivationAction H D y.right x.left =
          (0 : Coinduced H D) +
              (show Coinduced H D from
                abelianDerivationAction H (Coinduced H D) x.right y.left) -
              (show Coinduced H D from
                abelianDerivationAction H (Coinduced H D) y.right x.left)
      have hxy : derivationAction H D x.right y.left =
          (show Coinduced H D from
            abelianDerivationAction H (Coinduced H D) x.right y.left) := by
        ext a
        rfl
      have hyx : derivationAction H D y.right x.left =
          (show Coinduced H D from
            abelianDerivationAction H (Coinduced H D) y.right x.left) := by
        ext a
        rfl
      rw [hxy, hyx]
    · rfl

/-- The identity on both coordinates identifies the two presentations of the
coinduced semidirect product. -/
def semidirectEquiv :
    ((Coinduced H D) ⋊⁅derivationAction H D⁆ H) ≃ₗ⁅ℤ⁆
      (AbelianLie (Coinduced H D) ⋊⁅
        abelianDerivationAction H (Coinduced H D)⁆ H) :=
  LieEquiv.ofBijective (semidirectMap H D) ⟨by
    intro x y hxy
    apply LieAlgebra.SemiDirectSum.ext
    · exact congrArg LieAlgebra.SemiDirectSum.left hxy
    · exact congrArg LieAlgebra.SemiDirectSum.right hxy,
    by
      intro y
      exact ⟨⟨y.left, y.right⟩, rfl⟩⟩

@[simp]
theorem semidirectEquiv_apply
    (x : (Coinduced H D) ⋊⁅derivationAction H D⁆ H) :
    semidirectEquiv H D x = ⟨x.left, x.right⟩ := by
  change semidirectMap H D x = _
  rfl

end Coinduced

namespace CentralEmbedding

variable (E : Type u) [LieRing E]
variable (D : LieIdeal ℤ E)

/-- Every element of the augmentation ideal annihilates the augmentation
copy of the central ideal in the coinduced module. -/
theorem augmentationIdeal_annihilates_augmentationEmbedding
    (a : UEA ℤ (H E D)) (ha : a ∈ UEA.augmentationIdeal ℤ (H E D))
    (d : D) :
    UEA.representation ℤ (H E D) (J E D) a
      (augmentationEmbedding E D d) = 0 := by
  ext u
  rw [Coinduced.representation_apply, augmentationEmbedding_apply]
  rw [map_mul, (UEA.mem_augmentationIdeal ℤ (H E D)).mp ha]
  simp

/-- The coinduced central embedding, expressed in the standard abelian
semidirect-product interface. -/
def abelianMap
    (hcentral : D ≤ LieAlgebra.center ℤ E)
    (coefficient : M E D →ₗ[ℤ] D) :
    E →ₗ⁅ℤ⁆
      (AbelianLie (J E D) ⋊⁅abelianDerivationAction (H E D) (J E D)⁆
        (H E D)) :=
  (Coinduced.semidirectEquiv (H E D) D).toLieHom.comp
    (map E D hcentral coefficient)

@[simp]
theorem abelianMap_apply
    (hcentral : D ≤ LieAlgebra.center ℤ E)
    (coefficient : M E D →ₗ[ℤ] D) (e : E) :
    abelianMap E D hcentral coefficient e =
      ⟨extension E D hcentral coefficient (CentralDerivative.bar E D e),
        LieSubmodule.Quotient.mk e⟩ := by
  change Coinduced.semidirectEquiv (H E D) D
      (map E D hcentral coefficient e) = _
  rw [Coinduced.semidirectEquiv_apply]
  rfl

variable (hcentral : D ≤ LieAlgebra.center ℤ E)
variable (coefficient : M E D →ₗ[ℤ] D)
variable (hcoefficient : ∀ d : D,
  coefficient (centralInclusion E D hcentral d) = d)

include hcoefficient in
theorem abelianMap_central (d : D) :
    abelianMap E D hcentral coefficient d =
      LieAlgebra.SemiDirectSum.inl
        (abelianDerivationAction (H E D) (J E D))
        (augmentationEmbedding E D d) := by
  change Coinduced.semidirectEquiv (H E D) D
      (map E D hcentral coefficient d) = _
  rw [map_central E D hcentral coefficient hcoefficient d]
  exact Coinduced.semidirectEquiv_apply (H E D) D _

include hcentral coefficient hcoefficient in
/-- A central subgroup whose image is identified with a subgroup of `D`
acquires the finite coinduced coordinates required by central separation. -/
theorem exists_finiteSemidirectCentralCoordinates
    {K : Type u} [LieRing K] [Module.Finite ℤ K]
    (kappa : K →ₗ⁅ℤ⁆ E)
    (A : LieIdeal ℤ K) (d : A →ₗ[ℤ] D)
    (hd : Function.Injective d)
    (hkappa : ∀ a : A, kappa (a : K) = (d a : E))
    (hHfg : IsFinitelyGenerated (H E D)) (c : ℕ)
    (hHclass : lowerCentralSeries ℤ (H E D) c = ⊥) :
    Nonempty (FiniteSemidirectCentralCoordinates K A) := by
  let rho : K →ₗ⁅ℤ⁆
      (AbelianLie (J E D) ⋊⁅abelianDerivationAction (H E D) (J E D)⁆
        (H E D)) :=
    (abelianMap E D hcentral coefficient).comp kappa
  let f : A →ₗ[ℤ] J E D :=
    (augmentationEmbedding E D).toLinearMap.comp d
  have hrho (a : A) : rho (a : K) =
      LieAlgebra.SemiDirectSum.inl
        (abelianDerivationAction (H E D) (J E D)) (f a) := by
    change abelianMap E D hcentral coefficient (kappa (a : K)) = _
    rw [hkappa a]
    exact abelianMap_central E D hcentral coefficient hcoefficient (d a)
  have hf : Function.Injective f := by
    intro a b hab
    apply hd
    have h := congrArg (fun alpha : J E D ↦ alpha 1) hab
    simpa [f] using h
  have hann (u : UEA ℤ (H E D))
      (hu : u ∈ UEA.augmentationIdeal ℤ (H E D)) (a : A) :
      UEA.representation ℤ (H E D) (J E D) u (f a) = 0 := by
    exact augmentationIdeal_annihilates_augmentationEmbedding E D u hu (d a)
  exact exists_finiteSemidirectCentralCoordinates_of_additiveFinite
    (H E D) (J E D) hHfg c hHclass rho A f hrho hf hann

end CentralEmbedding

end

end LieRings.Plotkin
