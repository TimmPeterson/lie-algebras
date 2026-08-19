import LieRings.DimensionSubring.MetabelianVanishing.StepSeven

/-!
Audit of the abstract ``choose any preimage of the factor-two defect'' route.

The first result shows that existence of such a preimage is already formal,
without any exactness theorem for `Sym²`: the negative contextual wall is a
preimage.  The second result is the strongest choice-independence statement
that follows from Point 6.  It says that two corrections whose source
primitives lie in the top preimage have the same terminal coordinate.

This deliberately does not identify that common coordinate with the
component-trace primitive.  That identification is precisely the missing
placed PBW/full-label calculation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

theorem scratch_terminalFactorDefect_mem_range {a : L}
    (w : GoverningWitness n L data a) :
    w.terminalFactorDefect n L data hn ∈
      LinearMap.range
        (Koszul.dOne (terminalSourcePresentation n L data hn) 1) := by
  refine ⟨-w.contextualTerminalChain n L data hn, ?_⟩
  rw [map_neg, w.dOne_contextualTerminalChain_eq_neg_defect n L data hn]
  exact neg_neg _

def scratchCorrectionDifferenceCycle
    (c₁ c₂ : Koszul.One (terminalSourcePresentation n L data hn) 1)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 c₁ =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1 c₂) :
    Koszul.cyclesOne (terminalSourcePresentation n L data hn) 1 :=
  ⟨c₁ - c₂, by
    change Koszul.dOne (terminalSourcePresentation n L data hn) 1
      (c₁ - c₂) = 0
    rw [map_sub, hboundary, sub_self]⟩

@[simp] theorem scratchCorrectionDifferenceCycle_val
    (c₁ c₂ : Koszul.One (terminalSourcePresentation n L data hn) 1)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 c₁ =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1 c₂) :
    (scratchCorrectionDifferenceCycle n L data hn c₁ c₂ hboundary :
      Koszul.One (terminalSourcePresentation n L data hn) 1) = c₁ - c₂ :=
  rfl

theorem scratch_terminalSourceCoordinate_independent
    (c₁ c₂ : Koszul.One (terminalSourcePresentation n L data hn) 1)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 c₁ =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1 c₂)
    (p₁ p₂ : TopPreimage n L data)
    (hp₁ : (p₁ : FreeModel n L) =
      terminalSourcePrimitive n L data hn c₁)
    (hp₂ : (p₂ : FreeModel n L) =
      terminalSourcePrimitive n L data hn c₂) :
    terminalEval n L data p₁ = terminalEval n L data p₂ := by
  let z := scratchCorrectionDifferenceCycle n L data hn c₁ c₂ hboundary
  have hzero := terminalEval_terminalSourceCyclePreimage_eq_zero
    n L data hn z
  have hpreimage : terminalSourceCyclePreimage n L data hn z = p₁ - p₂ := by
    apply Subtype.ext
    rw [terminalSourceCyclePreimage_coe]
    change terminalSourcePrimitive n L data hn (c₁ - c₂) =
      (p₁ : FreeModel n L) - (p₂ : FreeModel n L)
    rw [map_sub, hp₁, hp₂]
  rw [hpreimage, map_sub] at hzero
  exact sub_eq_zero.mp hzero

end

end LieRings.MetabelianVanishing
