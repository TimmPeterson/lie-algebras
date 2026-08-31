import LieRings.Plotkin.Rees
import LieRings.DimensionSubring.Functoriality
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Functoriality of noncommutative Rees rings

A ring map carrying each power of one two-sided ideal into the corresponding power of another
induces a graded map of Rees rings.  If it is surjective on every filtered piece, the Rees map is
surjective.  We then specialize this to enveloping algebras of a surjective Lie map.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v w

variable {U : Type u} {W : Type v} [Ring U] [Ring W]

/-- The map on one homogeneous Rees piece. -/
def reesMapPiece (I : Ideal U) (J : Ideal W) (f : U →+* W)
    (hpow : ∀ (n : ℕ) (x : U), x ∈ I ^ n → f x ∈ J ^ n) (n : ℕ) :
    reesPiece I n →+ reesPiece J n where
  toFun x := ⟨f x, hpow n x x.property⟩
  map_zero' := Subtype.ext f.map_zero
  map_add' x y := Subtype.ext (f.map_add x y)

@[simp]
theorem reesMapPiece_coe (I : Ideal U) (J : Ideal W) (f : U →+* W)
    (hpow : ∀ (n : ℕ) (x : U), x ∈ I ^ n → f x ∈ J ^ n) (n : ℕ)
    (x : reesPiece I n) :
    ((reesMapPiece I J f hpow n x : reesPiece J n) : W) = f (x : U) :=
  rfl

/-- The graded Rees-ring map induced by a filtered ring map. -/
def reesMap (I : Ideal U) [I.IsTwoSided] (J : Ideal W) [J.IsTwoSided]
    (f : U →+* W) (hpow : ∀ (n : ℕ) (x : U), x ∈ I ^ n → f x ∈ J ^ n) :
    ReesRing I →+* ReesRing J := by
  let piece : ∀ n, reesPiece I n →+ ReesRing J := fun n ↦
    (DirectSum.of (fun k ↦ ↑(reesPiece J k)) n).comp
      (reesMapPiece I J f hpow n)
  refine DirectSum.toSemiring piece ?_ ?_
  · change DirectSum.of (fun k ↦ ↑(reesPiece J k)) 0
        (reesMapPiece I J f hpow 0
          (show reesPiece I 0 from ⟨1, by
            change (1 : U) ∈ I ^ 0
            rw [Submodule.pow_zero, Ideal.one_eq_top]
            trivial⟩)) =
      DirectSum.of (fun k ↦ ↑(reesPiece J k)) 0
        (show reesPiece J 0 from ⟨1, by
          change (1 : W) ∈ J ^ 0
          rw [Submodule.pow_zero, Ideal.one_eq_top]
          trivial⟩)
    congr 1
    apply Subtype.ext
    exact f.map_one
  · intro m n x y
    dsimp only [piece, AddMonoidHom.comp_apply]
    rw [DirectSum.of_mul_of]
    congr 1
    apply Subtype.ext
    exact f.map_mul (x : U) (y : U)

@[simp]
theorem reesMap_of (I : Ideal U) [I.IsTwoSided] (J : Ideal W) [J.IsTwoSided]
    (f : U →+* W) (hpow : ∀ (n : ℕ) (x : U), x ∈ I ^ n → f x ∈ J ^ n)
    (n : ℕ) (x : reesPiece I n) :
    reesMap I J f hpow (DirectSum.of (fun k ↦ ↑(reesPiece I k)) n x) =
      DirectSum.of (fun k ↦ ↑(reesPiece J k)) n
        (reesMapPiece I J f hpow n x) := by
  unfold reesMap
  rw [DirectSum.toSemiring_of]
  rfl

/-- Piecewise surjectivity implies surjectivity of the full Rees map. -/
theorem reesMap_surjective
    (I : Ideal U) [I.IsTwoSided] (J : Ideal W) [J.IsTwoSided]
    (f : U →+* W) (hpow : ∀ (n : ℕ) (x : U), x ∈ I ^ n → f x ∈ J ^ n)
    (hsurj : ∀ (n : ℕ) (y : W), y ∈ J ^ n →
      ∃ x : U, x ∈ I ^ n ∧ f x = y) :
    Function.Surjective (reesMap I J f hpow) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add y z hy hz =>
      obtain ⟨x, rfl⟩ := hy
      obtain ⟨w, rfl⟩ := hz
      exact ⟨x + w, map_add _ _ _⟩
  | of n y =>
      obtain ⟨x, hx, hxy⟩ := hsurj n (y : W) y.property
      let xr : reesPiece I n := ⟨x, hx⟩
      refine ⟨DirectSum.of (fun k ↦ ↑(reesPiece I k)) n xr, ?_⟩
      rw [reesMap_of]
      congr 1
      exact Subtype.ext hxy

section Enveloping

variable {L : Type u} {K : Type v} [LieRing L] [LieRing K]

/-- The Rees-ring map on augmentation filtrations induced by a Lie map. -/
def augmentationReesMap (f : L →ₗ⁅ℤ⁆ K) :
    ReesRing (UEA.augmentationIdeal ℤ L) →+*
      ReesRing (UEA.augmentationIdeal ℤ K) :=
  reesMap (UEA.augmentationIdeal ℤ L) (UEA.augmentationIdeal ℤ K)
    (UEA.map ℤ L K f).toRingHom
    (fun n x hx ↦ UEA.map_mem_augmentationIdeal_pow ℤ L K f n hx)

@[simp]
theorem augmentationReesMap_of (f : L →ₗ⁅ℤ⁆ K) (n : ℕ)
    (x : reesPiece (UEA.augmentationIdeal ℤ L) n) :
    augmentationReesMap f
        (DirectSum.of (fun k ↦ ↑(reesPiece (UEA.augmentationIdeal ℤ L) k)) n x) =
      DirectSum.of (fun k ↦ ↑(reesPiece (UEA.augmentationIdeal ℤ K) k)) n
        ⟨UEA.map ℤ L K f x,
          UEA.map_mem_augmentationIdeal_pow ℤ L K f n x.property⟩ := by
  exact reesMap_of _ _ _ _ n x

/-- A surjective Lie map induces a surjective map of augmentation Rees rings. -/
theorem augmentationReesMap_surjective (f : L →ₗ⁅ℤ⁆ K)
    (hf : Function.Surjective f) :
    Function.Surjective (augmentationReesMap f) := by
  apply reesMap_surjective
  intro n y hy
  cases n with
  | zero =>
      obtain ⟨x, hxy⟩ := UEA.map_surjective_of_surjective ℤ L K f hf y
      refine ⟨x, ?_, hxy⟩
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | succ n =>
      exact UEA.exists_mem_augmentationIdeal_pow_succ_of_surjective ℤ L K f hf n hy

set_option synthInstance.maxHeartbeats 100000 in
/-- Noetherianity of augmentation Rees rings descends along a surjective Lie map. -/
theorem isNoetherianRing_augmentationRees_of_surjective
    (f : L →ₗ⁅ℤ⁆ K) (hf : Function.Surjective f)
    [IsNoetherianRing (ReesRing (UEA.augmentationIdeal ℤ L))] :
    IsNoetherianRing (ReesRing (UEA.augmentationIdeal ℤ K)) :=
  isNoetherianRing_of_surjective _ _ (augmentationReesMap f)
    (augmentationReesMap_surjective f hf)

end Enveloping

end

end LieRings.Plotkin
