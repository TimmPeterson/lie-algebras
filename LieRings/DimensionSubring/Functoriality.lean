import LieRings.DimensionSubring.Basic
import LieRings.UniversalEnveloping.Quotient

/-!
# Functoriality of Lie dimension subrings

Every Lie homomorphism `f : L → L'` induces an algebra homomorphism
`U(f) : U(L) → U(L')`.  It preserves augmentations and their powers, hence sends
`δₙ(L)` into `δₙ(L')`.
-/

namespace LieRings

universe u v w

namespace UEA

variable (R : Type u) (L : Type v) (L' : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LieRing L'] [LieAlgebra R L']

/-- The algebra homomorphism on universal enveloping algebras induced by a Lie homomorphism. -/
noncomputable def map (f : L →ₗ⁅R⁆ L') : UEA R L →ₐ[R] UEA R L' :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp f)

@[simp]
theorem map_ι (f : L →ₗ⁅R⁆ L') (x : L) :
    map R L L' f (UniversalEnvelopingAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R (f x) := by
  simp [map]

@[simp]
theorem map_id (u : UEA R L) :
    map R L L (LieHom.id : L →ₗ⁅R⁆ L) u = u := by
  induction u using UEA.induction R L with
  | algebraMap r => simp [map]
  | ι x => rw [map_ι]; rfl
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

@[simp]
theorem map_comp (L'' : Type*) [LieRing L''] [LieAlgebra R L'']
    (g : L' →ₗ⁅R⁆ L'') (f : L →ₗ⁅R⁆ L') (u : UEA R L) :
    map R L' L'' g (map R L L' f u) = map R L L'' (g.comp f) u := by
  induction u using UEA.induction R L with
  | algebraMap r => simp [map]
  | ι x => rw [map_ι, map_ι, map_ι]; rfl
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- A Lie equivalence induces an equivalence of universal enveloping algebras. -/
noncomputable def mapEquiv (e : L ≃ₗ⁅R⁆ L') : UEA R L ≃ₐ[R] UEA R L' :=
  AlgEquiv.ofAlgHom (map R L L' e.toLieHom) (map R L' L e.symm.toLieHom)
    (by
      apply UniversalEnvelopingAlgebra.hom_ext
      ext x
      change map R L L' e.toLieHom
          (map R L' L e.symm.toLieHom (UniversalEnvelopingAlgebra.ι R x)) =
        UniversalEnvelopingAlgebra.ι R x
      rw [map_ι, map_ι]
      exact congrArg (UniversalEnvelopingAlgebra.ι R) (e.apply_symm_apply x))
    (by
      apply UniversalEnvelopingAlgebra.hom_ext
      ext x
      change map R L' L e.symm.toLieHom
          (map R L L' e.toLieHom (UniversalEnvelopingAlgebra.ι R x)) =
        UniversalEnvelopingAlgebra.ι R x
      rw [map_ι, map_ι]
      exact congrArg (UniversalEnvelopingAlgebra.ι R) (e.symm_apply_apply x))

@[simp]
theorem mapEquiv_apply (e : L ≃ₗ⁅R⁆ L') (u : UEA R L) :
    mapEquiv R L L' e u = map R L L' e.toLieHom u :=
  rfl

@[simp]
theorem mapEquiv_ι (e : L ≃ₗ⁅R⁆ L') (x : L) :
    mapEquiv R L L' e (UniversalEnvelopingAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R (e x) := by
  exact map_ι R L L' e.toLieHom x

/-- A surjective Lie map induces a surjective map of enveloping algebras. -/
theorem map_surjective_of_surjective (f : L →ₗ⁅R⁆ L')
    (hf : Function.Surjective f) :
    Function.Surjective (map R L L' f) := by
  intro u
  induction u using UEA.induction R L' with
  | algebraMap r => exact ⟨algebraMap R (UEA R L) r, by simp [map]⟩
  | ι x =>
      obtain ⟨y, rfl⟩ := hf x
      exact ⟨UniversalEnvelopingAlgebra.ι R y, map_ι R L L' f y⟩
  | mul a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x * y, map_mul (map R L L' f) x y⟩
  | add a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x + y, map_add (map R L L' f) x y⟩

/-- The map induced on enveloping algebras commutes with augmentation. -/
@[simp]
theorem augmentation_map (f : L →ₗ⁅R⁆ L') (a : UEA R L) :
    augmentation R L' (map R L L' f a) = augmentation R L a := by
  induction a using UEA.induction R L with
  | algebraMap r => simp
  | ι x =>
      change augmentation R L' (map R L L' f
        (UniversalEnvelopingAlgebra.ι R x)) =
          augmentation R L (UniversalEnvelopingAlgebra.ι R x)
      rw [map_ι, augmentation_ι, augmentation_ι]
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- The enveloping-algebra map sends the augmentation ideal into the augmentation ideal. -/
theorem map_mem_augmentationIdeal (f : L →ₗ⁅R⁆ L') {a : UEA R L}
    (ha : a ∈ augmentationIdeal R L) :
    map R L L' f a ∈ augmentationIdeal R L' := by
  rw [mem_augmentationIdeal] at ha ⊢
  rw [augmentation_map]
  exact ha

/-- The enveloping-algebra map sends every augmentation power into the corresponding power. -/
theorem map_mem_augmentationIdeal_pow (f : L →ₗ⁅R⁆ L') (n : ℕ)
    {a : UEA R L} (ha : a ∈ augmentationIdeal R L ^ n) :
    map R L L' f a ∈ augmentationIdeal R L' ^ n := by
  induction n generalizing a with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | succ n ih =>
      rw [Submodule.pow_succ] at ha ⊢
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Submodule.mul_mem_mul (ih ha)
          (map_mem_augmentationIdeal R L L' f hb)
      · intro a b ha hb
        rw [map_add]
        exact (augmentationIdeal R L' ^ n * augmentationIdeal R L').add_mem ha hb

/-- Under a surjective Lie map, every element of an augmentation power has a preimage in the
same augmentation power. -/
theorem exists_mem_augmentationIdeal_pow_succ_of_surjective
    (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f) (n : ℕ)
    {u : UEA R L'} (hu : u ∈ augmentationIdeal R L' ^ (n + 1)) :
    ∃ v : UEA R L, v ∈ augmentationIdeal R L ^ (n + 1) ∧
      map R L L' f v = u := by
  induction n generalizing u with
  | zero =>
      rw [zero_add, Submodule.pow_one] at hu ⊢
      obtain ⟨v, hv⟩ := map_surjective_of_surjective R L L' f hf u
      refine ⟨v, ?_, hv⟩
      rw [mem_augmentationIdeal]
      rw [← augmentation_map R L L' f, hv]
      exact (mem_augmentationIdeal R L').mp hu
  | succ n ih =>
      rw [Nat.succ_add] at hu ⊢
      rw [Submodule.pow_succ] at hu
      refine Submodule.mul_induction_on hu ?_ ?_
      · intro a ha b hb
        obtain ⟨x, hx, hxa⟩ := ih ha
        obtain ⟨y, rfl⟩ := map_surjective_of_surjective R L L' f hf b
        have hy : y ∈ augmentationIdeal R L := by
          rw [mem_augmentationIdeal]
          rw [← augmentation_map R L L' f]
          exact (mem_augmentationIdeal R L').mp hb
        refine ⟨x * y, ?_, ?_⟩
        · rw [Submodule.pow_succ]
          exact Submodule.mul_mem_mul hx hy
        · rw [map_mul, hxa]
      · intro a b ha hb
        obtain ⟨x, hx, hxa⟩ := ha
        obtain ⟨y, hy, hyb⟩ := hb
        refine ⟨x + y, (augmentationIdeal R L ^ (n + 1 + 1)).add_mem hx hy, ?_⟩
        rw [map_add, hxa, hyb]

end UEA

variable (R : Type u) (L : Type v) (L' : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [LieRing L'] [LieAlgebra R L']

/-- Lie dimension subrings are functorial: `f(δₙ(L)) ⊆ δₙ(L')`. -/
theorem map_dimensionSubring_le (f : L →ₗ⁅R⁆ L') (n : ℕ) :
    LieIdeal.map f (dimensionSubring R L n) ≤ dimensionSubring R L' n := by
  rw [LieIdeal.map_le_iff_le_comap]
  intro x hx
  rw [LieIdeal.mem_comap, mem_dimensionSubring]
  rw [mem_dimensionSubring] at hx
  rw [← UEA.map_ι R L L' f]
  exact UEA.map_mem_augmentationIdeal_pow R L L' f n hx

/-- Elementwise form of functoriality of Lie dimension subrings. -/
theorem map_mem_dimensionSubring (f : L →ₗ⁅R⁆ L') (n : ℕ)
    {x : L} (hx : x ∈ dimensionSubring R L n) :
    f x ∈ dimensionSubring R L' n :=
  map_dimensionSubring_le R L L' f n (LieIdeal.mem_map hx)

/-- If the `n`th dimension subring of `L/I` vanishes, then `δₙ(L) ⊆ I`. -/
theorem dimensionSubring_le_of_quotient_eq_bot (I : LieIdeal R L) (n : ℕ)
    (hquot : dimensionSubring R (L ⧸ I) n = ⊥) :
    dimensionSubring R L n ≤ I := by
  intro x hx
  have hmap := map_mem_dimensionSubring R L (L ⧸ I)
    (UEA.lieIdealQuotientMk R L I) n hx
  rw [hquot] at hmap
  have hzero : (LieSubmodule.Quotient.mk x : L ⧸ I) = 0 := by
    simpa using hmap
  exact (LieSubmodule.Quotient.mk_eq_zero' (N := I)).mp hzero

end LieRings
