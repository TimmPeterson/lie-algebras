import LieRings.Plotkin.FiniteGeneration
import LieRings.Plotkin.LowerCentralBasis
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Localization.Module

/-!
# The finite dimension-subring tail of a finitely generated nilpotent Lie ring

The manuscript rationalizes the Lie ring and applies filtered PBW over `ℚ`.  We implement that
argument literally.  The induced cross-base map on enveloping algebras is constructed from the
universal property, and localization then identifies its kernel with additive torsion.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

variable {K : Type u} [LieRing K]

local notation "Krat" => TensorProduct ℤ ℚ K

/-- The canonical Lie homomorphism from a Lie ring to its rationalization. -/
def rationalizationLieHom : K →ₗ⁅ℤ⁆ Krat where
  toLinearMap := (TensorProduct.mk ℤ ℚ K) 1
  map_lie' := by
    intro x y
    change (1 : ℚ) ⊗ₜ[ℤ] ⁅x, y⁆ =
      ⁅(1 : ℚ) ⊗ₜ[ℤ] x, (1 : ℚ) ⊗ₜ[ℤ] y⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul]
    simp

@[simp] theorem rationalizationLieHom_apply (x : K) :
    rationalizationLieHom x = (1 : ℚ) ⊗ₜ[ℤ] x :=
  rfl

/-- The rationalized primitive, regarded as a `ℤ`-linear Lie map into the rational enveloping
algebra. -/
def rationalPrimitiveLieHom : K →ₗ⁅ℤ⁆ UEA ℚ Krat where
  toLinearMap :=
    ((UniversalEnvelopingAlgebra.ι ℚ : Krat →ₗ⁅ℚ⁆ UEA ℚ Krat).toLinearMap.restrictScalars ℤ).comp
      rationalizationLieHom.toLinearMap
  map_lie' := by
    intro x y
    change UniversalEnvelopingAlgebra.ι ℚ (rationalizationLieHom ⁅x, y⁆) =
      ⁅UniversalEnvelopingAlgebra.ι ℚ (rationalizationLieHom x),
        UniversalEnvelopingAlgebra.ι ℚ (rationalizationLieHom y)⁆
    rw [LieHom.map_lie, LieHom.map_lie]

@[simp] theorem rationalPrimitiveLieHom_apply (x : K) :
    rationalPrimitiveLieHom x =
      UniversalEnvelopingAlgebra.ι ℚ ((1 : ℚ) ⊗ₜ[ℤ] x) :=
  rfl

/-- The enveloping-algebra map induced by rationalization.  Its codomain is the enveloping
algebra over `ℚ`, with scalars restricted to `ℤ`. -/
def rationalUEAMap : UEA ℤ K →ₐ[ℤ] UEA ℚ Krat :=
  UniversalEnvelopingAlgebra.lift ℤ rationalPrimitiveLieHom

@[simp] theorem rationalUEAMap_iota (x : K) :
    rationalUEAMap (UniversalEnvelopingAlgebra.ι ℤ x) =
      UniversalEnvelopingAlgebra.ι ℚ ((1 : ℚ) ⊗ₜ[ℤ] x) := by
  rw [rationalUEAMap, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- Rationalization commutes with augmentation, after applying `ℤ → ℚ` to the source value. -/
@[simp] theorem augmentation_rationalUEAMap (u : UEA ℤ K) :
    UEA.augmentation ℚ Krat (rationalUEAMap u) =
      algebraMap ℤ ℚ (UEA.augmentation ℤ K u) := by
  induction u using UEA.induction ℤ K with
  | algebraMap z => simp [rationalUEAMap]
  | ι x =>
      rw [rationalUEAMap_iota, UEA.augmentation_ι, UEA.augmentation_ι, map_zero]
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

theorem rationalUEAMap_mem_augmentationIdeal {u : UEA ℤ K}
    (hu : u ∈ UEA.augmentationIdeal ℤ K) :
    rationalUEAMap u ∈ UEA.augmentationIdeal ℚ Krat := by
  rw [UEA.mem_augmentationIdeal] at hu ⊢
  rw [augmentation_rationalUEAMap, hu]
  simp

/-- Rationalization preserves every augmentation power. -/
theorem rationalUEAMap_mem_augmentationIdeal_pow (n : ℕ) {u : UEA ℤ K}
    (hu : u ∈ UEA.augmentationIdeal ℤ K ^ n) :
    rationalUEAMap u ∈ UEA.augmentationIdeal ℚ Krat ^ n := by
  induction n generalizing u with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | succ n ih =>
      rw [Submodule.pow_succ] at hu ⊢
      refine Submodule.mul_induction_on hu ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Submodule.mul_mem_mul (ih ha)
          (rationalUEAMap_mem_augmentationIdeal hb)
      · intro a b ha hb
        rw [map_add]
        exact (UEA.augmentationIdeal ℚ Krat ^ n *
          UEA.augmentationIdeal ℚ Krat).add_mem ha hb

/-- Nilpotence survives rational extension of scalars. -/
theorem rationalization_lowerCentralSeries_eq_bot
    (c : ℕ) (hclass : lowerCentralSeries ℤ K c = ⊥) :
    lowerCentralSeries ℚ Krat c = ⊥ := by
  change LieModule.lowerCentralSeries ℤ K K c = ⊥ at hclass
  change LieModule.lowerCentralSeries ℚ Krat Krat c = ⊥
  rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange ℤ ℚ K K c,
    hclass, LieSubmodule.baseChange_bot]

/-- An element of the first augmentation power beyond the nilpotency class dies after
rationalization. -/
theorem rationalization_eq_zero_of_mem_dimensionSubring_succ
    (c : ℕ) (hclass : lowerCentralSeries ℤ K c = ⊥) {x : K}
    (hx : x ∈ dimensionSubring ℤ K (c + 1)) :
    rationalizationLieHom x = 0 := by
  have hxpow := (mem_dimensionSubring ℤ K).mp hx
  have hmap : UniversalEnvelopingAlgebra.ι ℚ (rationalizationLieHom x) ∈
      UEA.augmentationIdeal ℚ Krat ^ (c + 1) := by
    simpa only [rationalUEAMap_iota, rationalizationLieHom_apply] using
      (rationalUEAMap_mem_augmentationIdeal_pow (c + 1) hxpow)
  have hxRat : rationalizationLieHom x ∈ dimensionSubring ℚ Krat (c + 1) :=
    (mem_dimensionSubring ℚ Krat).mpr hmap
  rw [dimensionSubring_succ_eq_bot_of_lowerCentralSeries_eq_bot_field c
    (rationalization_lowerCentralSeries_eq_bot c hclass)] at hxRat
  simpa using hxRat

/-- The finite-tail dimension subring is an additive torsion module. -/
theorem dimensionSubring_succ_isTorsion
    (c : ℕ) (hclass : lowerCentralSeries ℤ K c = ⊥) :
    Module.IsTorsion ℤ (dimensionSubring ℤ K (c + 1)) := by
  intro x
  let q : K →ₗ[ℤ] Krat := (TensorProduct.mk ℤ ℚ K) 1
  letI : IsLocalizedModule (nonZeroDivisors ℤ) q :=
    IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ
  have hqx : q x.1 = 0 :=
    rationalization_eq_zero_of_mem_dimensionSubring_succ c hclass x.2
  have hxker : x.1 ∈ LinearMap.ker q := by simpa [LinearMap.mem_ker] using hqx
  obtain ⟨r, hrS, hr⟩ :=
    (IsLocalizedModule.mem_ker_iff (nonZeroDivisors ℤ)).mp hxker
  refine ⟨⟨r, hrS⟩, ?_⟩
  apply Subtype.ext
  exact hr

/-- **Finite tail.**  If `K` is finitely generated as a Lie ring and its zero-based `c`th
lower-central term vanishes, then `δ_(c+1)(K)` is a finite additive group. -/
theorem finite_dimensionSubring_succ_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
    (hK : IsFinitelyGenerated K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥) :
    Finite (dimensionSubring ℤ K (c + 1)) := by
  letI : Module.Finite ℤ K :=
    moduleFinite_of_finitelyGenerated_of_lowerCentralSeries_eq_bot K hK c hclass
  letI : Module.Finite ℤ (dimensionSubring ℤ K (c + 1)) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  exact Module.finite_of_fg_torsion _ (dimensionSubring_succ_isTorsion c hclass)

end

end LieRings.Plotkin
