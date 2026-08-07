import LieRings.PBW.CartanEilenberg
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Module-theoretic PBW conditions

The extension of free-module PBW to flat modules uses the Govorov--Lazard theorem: a flat module is
a filtered direct limit of finite free modules.  Mathlib does not yet contain that theorem, so this
file records the condition implications that are already available and keeps them separate from
the still-missing PBW transport argument.

In particular, mathlib already knows that a torsion-free module over a Dedekind domain is flat.
For `R = ℤ`, this is the familiar fact that a torsion-free Abelian group is a flat `ℤ`-module.
-/

namespace LieRings.PBW

universe u v

variable (R : Type u) (M : Type v)
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Free modules satisfy the flatness hypothesis used in the Lazard extension of PBW. -/
theorem flat_of_free [Module.Free R M] : Module.Flat R M := by
  infer_instance

/-- Over a Dedekind domain, torsion-free modules are flat. -/
theorem flat_of_torsionFree_of_dedekind [IsDedekindDomain R]
    [Module.IsTorsionFree R M] :
    Module.Flat R M := by
  infer_instance

/-- A torsion-free Abelian group is flat as a `ℤ`-module. -/
theorem flat_int_of_torsionFree [Module.IsTorsionFree ℤ M] : Module.Flat ℤ M := by
  infer_instance

end LieRings.PBW
