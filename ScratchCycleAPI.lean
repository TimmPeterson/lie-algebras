import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmithContinuation

#check UniversalEnvelopingAlgebra.lift
#check UniversalEnvelopingAlgebra.ι
#check LieHom.mk
#check LieHom.comp
#check LieRings.MetabelianVanishing.prLE
#check FreeMetabelian.Free.projectPrefix
#check FreeMetabelian.Free.prefixMap
#check LieRings.PBW.factorSymbol
#check LieRings.MetabelianVanishing.rightSymbol
#check LieRings.MetabelianVanishing.fullRightSymbol

namespace LieRings.MetabelianVanishing
open FreeMetabelian
universe u
noncomputable section
variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L) (hn : 2 ≤ n)

def testPrefixLieHom : FreeModel n L →ₗ⁅ℤ⁆ A L n :=
  LieHom.mk (prLE n L n (by omega)) (by
    intro x y
    funext i
    rcases i with ⟨(_ | _ | q), hi⟩ <;> rfl)

#check testPrefixLieHom

def testUEAMap : UEA ℤ (FreeModel n L) →ₐ[ℤ] UEA ℤ (A L n) :=
  UniversalEnvelopingAlgebra.lift ℤ
    ((UniversalEnvelopingAlgebra.ι ℤ).comp (testPrefixLieHom n L))

end
end LieRings.MetabelianVanishing
