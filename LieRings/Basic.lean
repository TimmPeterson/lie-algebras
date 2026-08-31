import Mathlib.Algebra.Lie.Subalgebra

/-!
# Basic definitions for Lie rings

This file contains foundational definitions intended for use throughout the
project, independently of any particular dimension-subring argument.
-/

namespace LieRings

universe u

/-- A Lie ring is finitely generated if a finite set generates it as a Lie
subalgebra over `ℤ`.  This is finite generation as a Lie ring, not finite
generation of its underlying additive group. -/
def IsFinitelyGenerated (L : Type u) [LieRing L] : Prop :=
  ∃ generators : Finset L,
    LieSubalgebra.lieSpan ℤ L (generators : Set L) = ⊤

end LieRings
