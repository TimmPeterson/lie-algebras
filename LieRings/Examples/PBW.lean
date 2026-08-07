import LieRings.PBW.Abelian
import LieRings.PBW.Conditions
import LieRings.PBW.HigginsEmbedding

/-!
# Small PBW examples

These declarations are intentionally short, copyable examples of the public PBW interface.
-/

namespace LieRings.Examples

open LieRings.PBW

universe u v w

/-- Every Lie algebra over `ℤ` embeds canonically in its universal enveloping algebra.
No basis or auxiliary parameter is needed. -/
example (L : Type v) [LieRing L] :
    Function.Injective
      (UniversalEnvelopingAlgebra.ι ℤ : L → UEA ℤ L) :=
  canonicalMap_injective_int L

/-- Ordered monomials span the enveloping algebra whenever the underlying module has an ordered
basis. -/
noncomputable example (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
    (ι : Type w) [LinearOrder ι] (b : Module.Basis ι R L) (u : UEA R L) :
    ∃ p : MvPolynomial ι R, orderedPBWMap R L ι b p = u :=
  orderedPBWMap_surjective R L ι b u

/-- For an Abelian Lie algebra, PBW is already a complete algebra equivalence. -/
noncomputable example (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
    [IsLieAbelian L] :
    UEA R L ≃ₐ[R] SymmetricAlgebra R L :=
  abelianEquivSymmetric R L

/-- The exact final input expected from the Cartan--Eilenberg construction. -/
noncomputable example (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
    (ι : Type w) [LinearOrder ι] (b : Module.Basis ι R L)
    (P : TriangularRepresentation R L ι b) :
    FreeModulePBW R L ι b :=
  P.freeModulePBW

/-- A completed ordered PBW theorem implies the canonical embedding `L → U(L)`. -/
example (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
    (ι : Type w) [LinearOrder ι] (b : Module.Basis ι R L)
    (h : FreeModulePBW R L ι b) :
    Function.Injective (UniversalEnvelopingAlgebra.ι R : L → UEA R L) :=
  canonicalMap_injective_of_freeModulePBW R L ι b h

end LieRings.Examples
