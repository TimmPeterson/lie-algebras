import LieRings.DimensionSubring.MetabelianVanishing.CompleteCutoffCycle

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance scratchFinalIntegrationFintype : Fintype L :=
  Fintype.ofFinite L

theorem test_eq_zero_of_completeCutoffCorrection_eval
    {a : L} (w : GoverningWitness n L data a)
    (correction : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 correction =
      w.rawCutoffOrdinaryFactorTwo n L data hn)
    (heval : evaluation n L data
        (terminalSourcePrimitive n L data hn correction -
          w.rawCutoffOrdinaryPrimitive n L data hn) = 0) :
    a = 0 := by
  let error : TopPreimage n L data :=
    ⟨terminalSourcePrimitive n L data hn correction -
        w.rawCutoffOrdinaryPrimitive n L data hn, by
      change evaluation n L data
          (terminalSourcePrimitive n L data hn correction -
            w.rawCutoffOrdinaryPrimitive n L data hn) ∈
        lowerCentralSeries ℤ L n
      rw [heval]
      exact LieSubmodule.zero_mem _⟩
  apply w.eq_zero_of_completeCutoffCorrection n L data hn
    correction error hboundary
  · change terminalSourcePrimitive n L data hn correction =
      w.rawCutoffOrdinaryPrimitive n L data hn +
        (terminalSourcePrimitive n L data hn correction -
          w.rawCutoffOrdinaryPrimitive n L data hn)
    abel
  · change data.topEquiv.toIntLinearEquiv.toLinearMap
      ⟨evaluation n L data
          (terminalSourcePrimitive n L data hn correction -
            w.rawCutoffOrdinaryPrimitive n L data hn), _⟩ = 0
    have hevalSubtype :
        (⟨evaluation n L data
            (terminalSourcePrimitive n L data hn correction -
              w.rawCutoffOrdinaryPrimitive n L data hn), by
            rw [heval]
            exact LieSubmodule.zero_mem _⟩ :
          lowerCentralSeries ℤ L n) = 0 := by
      apply Subtype.ext
      exact heval
    rw [hevalSubtype, map_zero]

end

end LieRings.MetabelianVanishing
