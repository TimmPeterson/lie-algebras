import LieRings.Homological.LieHomology.Differential
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The Chevalley--Eilenberg chain complex

This file packages the homogeneous differential constructed in
`LieRings.Homological.LieHomology.Differential` as a chain complex of modules.  It also
constructs the chain map, and hence the map on homology, induced by a morphism of Lie
algebras.

The coefficients are trivial: the degree-`n` chain module is `⋀[R]^n L`. A future complex with
coefficients in a general right Lie module should be kept separate, since its differential has an
additional action term.
-/

open CategoryTheory

universe u v

namespace LieRings.Homological.LieHomology

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The degree-`n` Chevalley--Eilenberg chain module with trivial coefficients. -/
abbrev chains (n : ℕ) : ModuleCat.{max u v} R := ModuleCat.of R (⋀[R]^n L)

private theorem differential_sq (n : ℕ) :
    ModuleCat.ofHom (differential R L (n + 1)) ≫
      ModuleCat.ofHom (differential R L n) = 0 := by
  apply ModuleCat.hom_ext
  exact differential_comp_differential R L n

/-- The Chevalley--Eilenberg chain complex of `L` with trivial coefficients in `R`. -/
def complex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (chains R L)
    (fun n => ModuleCat.ofHom (differential R L n))
    (differential_sq R L)

@[simp]
theorem complex_X (n : ℕ) : (complex R L).X n = chains R L n := rfl

@[simp]
theorem complex_d (n : ℕ) :
    (complex R L).d (n + 1) n = ModuleCat.ofHom (differential R L n) := by
  apply ChainComplex.of_d

variable {R L}
variable {K : Type v} [LieRing K] [LieAlgebra R K]
variable {M : Type v} [LieRing M] [LieAlgebra R M]

/-- The chain map induced by a morphism of Lie algebras. -/
noncomputable def complexMap (f : LieHom R L K) : complex R L ⟶ complex R K :=
  ChainComplex.ofHom (chains R L)
    (fun n => ModuleCat.ofHom (differential R L n))
    (differential_sq R L)
    (chains R K)
    (fun n => ModuleCat.ofHom (differential R K n))
    (differential_sq R K)
    (fun n => ModuleCat.ofHom (exteriorPower.map n f.toLinearMap))
    (fun n => by
      apply ModuleCat.hom_ext
      exact (differential_natural R L f n).symm)

@[simp]
theorem complexMap_f (f : LieHom R L K) (n : ℕ) :
    (complexMap f).f n = ModuleCat.ofHom (exteriorPower.map n f.toLinearMap) := rfl

@[simp]
theorem complexMap_id : complexMap (LieHom.id : LieHom R L L) = 𝟙 (complex R L) := by
  ext n x
  change exteriorPower.map n (LieHom.id : LieHom R L L).toLinearMap x = x
  rw [show (LieHom.id : LieHom R L L).toLinearMap = LinearMap.id by ext; rfl,
    exteriorPower.map_id]
  rfl

@[simp]
theorem complexMap_comp (f : LieHom R L K) (g : LieHom R K M) :
    complexMap (g.comp f) = complexMap f ≫ complexMap g := by
  ext n x
  change exteriorPower.map n (g.comp f).toLinearMap x =
    exteriorPower.map n g.toLinearMap (exteriorPower.map n f.toLinearMap x)
  rw [show (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap by ext; rfl,
    exteriorPower.map_comp]
  rfl

/-- Chevalley--Eilenberg homology with trivial coefficients, as an object of `ModuleCat`. -/
noncomputable abbrev homology (n : ℕ) : ModuleCat.{max u v} R := (complex R L).homology n

/-- The underlying type of Chevalley--Eilenberg homology with trivial coefficients. -/
noncomputable abbrev Homology (n : ℕ) :=
  (homology (R := R) (L := L) n : Type (max u v))

/-- The homomorphism on Chevalley--Eilenberg homology induced by a Lie homomorphism. -/
noncomputable def homologyMap (f : LieHom R L K) (n : ℕ) :
    homology (R := R) (L := L) n ⟶ homology (R := R) (L := K) n :=
  HomologicalComplex.homologyMap (complexMap f) n

@[simp]
theorem homologyMap_id (n : ℕ) :
    homologyMap (LieHom.id : LieHom R L L) n = 𝟙 _ := by
  rw [homologyMap, complexMap_id]
  exact HomologicalComplex.homologyMap_id (complex R L) n

theorem homologyMap_comp (f : LieHom R L K) (g : LieHom R K M) (n : ℕ) :
    homologyMap (g.comp f) n = homologyMap f n ≫ homologyMap g n := by
  rw [homologyMap, complexMap_comp]
  exact HomologicalComplex.homologyMap_comp (complexMap f) (complexMap g) n

/-- The standard concrete presentation of homology as cycles modulo boundaries. -/
noncomputable def homologyConcreteIso (n : ℕ) :
    homology (R := R) (L := L) n ≅ (complex R L).sc n |>.moduleCatLeftHomologyData.H :=
  (complex R L).sc n |>.moduleCatHomologyIso

end LieRings.Homological.LieHomology
