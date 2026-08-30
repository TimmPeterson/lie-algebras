import LieRings.Homological.LieHomology.Complex
import Mathlib.Algebra.Lie.IdealOperations

/-!
# Low-degree Chevalley--Eilenberg differentials

This file records the degree-two and degree-three formulas in a form convenient for computing
`H₁` and `H₂`.  With the convention used in the accompanying manuscript,

* `d₂(x ∧ y) = -⁅x,y⁆`;
* `d₃(x ∧ y ∧ z) = -⁅x,y⁆ ∧ z + ⁅x,z⁆ ∧ y - ⁅y,z⁆ ∧ x`.

The signs are immaterial for kernels and images, but fixing them here prevents later comparison
arguments from silently changing conventions.
-/

universe u v

namespace LieRings.Homological.LieHomology

noncomputable section

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The degree-two CE boundary, with `⋀¹L` identified with `L`. -/
def degreeTwoBoundary : (⋀[R]^2 L) →ₗ[R] L :=
  (exteriorPower.oneEquiv R L).toLinearMap.comp (differential R L 1)

@[simp]
theorem degreeTwoBoundary_ιMulti (x y : L) :
    degreeTwoBoundary R L (exteriorPower.ιMulti R 2 ![x, y]) = -⁅x, y⁆ := by
  change exteriorPower.oneEquiv R L
      (differential R L 1 (exteriorPower.ιMulti R 2 ![x, y])) = -⁅x, y⁆
  rw [← (exteriorPower.oneEquiv R L).apply_symm_apply (-⁅x, y⁆)]
  congr 1
  apply Subtype.ext
  rw [differential_coe]
  simp [ExteriorAlgebra.ιMulti_succ_apply, exteriorPower.oneEquiv_symm_apply]
  rw [← map_neg]
  exact congrArg (ExteriorAlgebra.ι R) (lie_skew y x)

/-- The bracket map `⋀²L → L`.  It is the negative of the chosen CE differential. -/
def bracketMap : (⋀[R]^2 L) →ₗ[R] L := -degreeTwoBoundary R L

@[simp]
theorem bracketMap_ιMulti (x y : L) :
    bracketMap R L (exteriorPower.ιMulti R 2 ![x, y]) = ⁅x, y⁆ := by
  simp [bracketMap]

variable {L}
variable {K : Type*} [LieRing K] [LieAlgebra R K]

/-- Naturality of the bracket map on exterior squares. -/
theorem bracketMap_natural (f : LieHom R L K) :
    f.toLinearMap.comp (bracketMap R L) =
      (bracketMap R K).comp (exteriorPower.map 2 f.toLinearMap) := by
  apply exteriorPower.linearMap_ext
  ext a
  have ha : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
  rw [ha]
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    bracketMap_ιMulti, exteriorPower.map_apply_ιMulti]
  have h0 : f.toLinearMap (a 0) = f (a 0) := congrFun (LieHom.coe_toLinearMap f) (a 0)
  have h1 : f.toLinearMap (a 1) = f (a 1) := congrFun (LieHom.coe_toLinearMap f) (a 1)
  rw [show f.toLinearMap ⁅a 0, a 1⁆ = ⁅f (a 0), f (a 1)⁆ by
      simpa only [LieHom.coe_toLinearMap] using f.map_lie (a 0) (a 1)]
  have hv : f.toLinearMap ∘ ![a 0, a 1] = ![f (a 0), f (a 1)] := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
  rw [hv, bracketMap_ιMulti]

variable (L)

/-- The degree-three boundary on a pure wedge, stated inside the exterior algebra. -/
theorem differential_two_ιMulti_coe (x y z : L) :
    ((differential R L 2 (exteriorPower.ιMulti R 3 ![x, y, z]) : ⋀[R]^2 L) :
        ExteriorAlgebra R L) =
      -(ExteriorAlgebra.ι R ⁅x, y⁆ * ExteriorAlgebra.ι R z) +
        ExteriorAlgebra.ι R ⁅x, z⁆ * ExteriorAlgebra.ι R y -
          ExteriorAlgebra.ι R ⁅y, z⁆ * ExteriorAlgebra.ι R x := by
  rw [differential_coe]
  simp [ExteriorAlgebra.ιMulti_succ_apply]
  have hxz := ExteriorAlgebra.ι_add_mul_swap (R := R) ⁅x, z⁆ y
  have hyz := ExteriorAlgebra.ι_add_mul_swap (R := R) ⁅y, z⁆ x
  rw [eq_neg_of_add_eq_zero_right hxz, eq_neg_of_add_eq_zero_right hyz]
  abel

/-- The image of the degree-two boundary is the derived ideal, viewed as a submodule. -/
theorem range_degreeTwoBoundary :
    LinearMap.range (degreeTwoBoundary R L) =
      ((⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆ : LieIdeal R L) : Submodule R L) := by
  let S : Submodule R L :=
    Submodule.span R { ⁅(x : L), (y : L)⁆ |
      (x : (⊤ : LieIdeal R L)) (y : (⊤ : LieIdeal R L)) }
  have hderived :
      ((⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆ : LieIdeal R L) : Submodule R L) = S :=
    LieSubmodule.lieIdeal_oper_eq_linear_span
      (I := (⊤ : LieIdeal R L)) (N := (⊤ : LieIdeal R L))
  rw [hderived]
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    have hu : u ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    refine Submodule.span_induction (p := fun u _ => degreeTwoBoundary R L u ∈ S)
      ?_ (by simpa using S.zero_mem) ?_ ?_ hu
    · rintro _ ⟨a, rfl⟩
      have ha : a = ![a 0, a 1] := by
        funext i
        fin_cases i <;> rfl
      rw [ha, degreeTwoBoundary_ιMulti]
      exact S.neg_mem (Submodule.subset_span
        ⟨⟨a 0, by simp⟩, ⟨a 1, by simp⟩, rfl⟩)
    · intro x y _ _ hx hy
      simpa only [map_add] using S.add_mem hx hy
    · intro r x _ hx
      simpa only [map_smul] using S.smul_mem r hx
  · rw [Submodule.span_le]
    rintro _ ⟨x, y, rfl⟩
    refine ⟨-exteriorPower.ιMulti R 2 ![(x : L), (y : L)], ?_⟩
    simp

end

end LieRings.Homological.LieHomology
