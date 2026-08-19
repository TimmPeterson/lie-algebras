import LieRings.DimensionSubring.MetabelianVanishing.GlobalTerminalCorrection
import LieRings.DimensionSubring.MetabelianVanishing.Main

/-!
# Aristotle target: the terminal cycle supplied by the global closed square

This file has exactly one proof hole.  It starts after the construction of
the complete occurrence-labelled comparison trace and after the independent
PBW/Koszul infrastructure, but before the final closed-square/PBW assembly.

The target is deliberately smaller than the odd dimension-subring theorem.
It asks for the concrete certificate constructed in the manuscript: the
global factor-two packet `B^(n)` is a genuine cycle in the terminal
presentation, and its realized source primitive has the same terminal
coordinate as the governing external marked word.

The three theorems after the target are proof-complete.  They verify inside
Lean that filling this one hole proves unconditional Step 7, the reduced
top-layer theorem, and finally the public implication with exactly the
Reduction and Passi--Sicking properties as assumptions.
-/

namespace LieRings.Aristotle

open MetabelianVanishing

universe u

noncomputable section

set_option maxHeartbeats 4000000

/-!
## The single Aristotle obligation

Mathematically, the cycle below is the terminal packet `chi_n` obtained from
the factor-two cut `B^(n)` of the global marked-row/closed-square trace.  The
coordinate equality is the PBW assembly identity after the intermediate
horizontal/vertical diagonals cancel by `Phi_k = T_k \circ d` and the
governing multifactor coefficients vanish.

No relation component may be promoted to a full relation.  The proof must
retain the complete occurrence ledger and all lower-context corrections.
-/

/-- The corrected closed-square calculation makes the manuscript's concrete
factor-two packet `B^(n) = chi_n` a genuine terminal source cycle and
identifies its canonical primitive read with the external governing
coordinate.  This is the smallest remaining certificate that closes Step 7.
-/
theorem globalFactorTwoChain_cycle_and_external_coordinate
    (n : ℕ) (L : Type u) [LieRing L] [Finite L]
    (data : CyclicTopData n L) (hn3 : 3 ≤ n) {a : L}
    (w : GoverningWitness n L data a) :
    ∃ hcycle : Koszul.dOne
        (terminalSourcePresentation n L data (by omega)) 1
          (w.globalFactorTwoChain n L data (by omega)) = 0,
      terminalEval n L data
          (terminalSourceCyclePreimage n L data (by omega)
            ⟨w.globalFactorTwoChain n L data (by omega), hcycle⟩) =
        (w.externalMarkedWord n L data (by omega)).value := by
  sorry

/-!
## Checked consequences of the target

Do not replace these wrappers by additional assumptions.  Their purpose is
to make the sufficiency of the single obligation mechanically explicit.
-/

/-- Filling the Aristotle obligation gives the unconditional Step-7
governing-witness theorem in every degree needed by the reduction. -/
theorem governingWitness_eq_zero
    (n : ℕ) (L : Type u) [LieRing L] [Finite L]
    (data : CyclicTopData n L) (hn3 : 3 ≤ n) {a : L}
    (w : GoverningWitness n L data a) : a = 0 := by
  obtain ⟨hboundary, hcoordinate⟩ :=
    globalFactorTwoChain_cycle_and_external_coordinate
      n L data hn3 w
  exact w.eq_zero_of_terminalCycleSourceValue
    n L data (by omega)
      ⟨w.globalFactorTwoChain n L data (by omega), hboundary⟩
      hcoordinate

/-- The low-degree library results plus the Aristotle obligation give the
entire reduced top-layer theorem. -/
theorem reducedTopLayerVanishes : ReducedTopLayerVanishes.{u} := by
  apply MetabelianVanishing.reducedTopLayerVanishes_of_stepSeven
  intro n L _ _ data hn3 a w
  exact governingWitness_eq_zero n L data hn3 w

/-- Final implication requested in the project.  Its only assumptions are
exactly the two explicitly deferred inputs. -/
theorem finite_metabelian_odd_dimensionSubring_eq_bot
    (hReduction : ReductionProperty.{u})
    (hPS : PassiSickingProperty.{u})
    (n : ℕ) (L : Type u) [LieRing L] [Finite L]
    (hn : 1 ≤ n)
    (hmeta : IsMetabelian L)
    (hclass : lowerCentralSeries ℤ L (n + 1) = ⊥) :
    dimensionSubring ℤ L (2 * n + 1) = ⊥ := by
  exact finite_metabelian_odd_dimensionSubring_eq_bot_of_stepSeven
    (fun n L _ _ data hn3 _ w ↦
      governingWitness_eq_zero n L data hn3 w)
    hReduction hPS n L hn hmeta hclass

end

end LieRings.Aristotle
