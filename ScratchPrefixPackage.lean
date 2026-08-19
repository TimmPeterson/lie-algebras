import LieRings.DimensionSubring.MetabelianVanishing.TerminalCertificateBridge
import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmith

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

/-- The canonical genuine relation having the prescribed terminal prefix. -/
def terminalPrefixRelation (x : FreeModel n L)
    (hx : prLE n L n (by omega) x ∈ D n L data n (by omega)) :
    Relations n L data :=
  terminalRelationFullSection n L data hn
    ⟨prLE n L n (by omega) x, hx⟩

/-- Replace the lower-weight prefix by a genuine relation and retain the
remaining homogeneous top coordinate. -/
def terminalPrefixError (x : FreeModel n L)
    (hx : prLE n L n (by omega) x ∈ D n L data n (by omega)) :
    TopPreimage n L data :=
  relationTopPreimage n L data (terminalPrefixRelation n L data hn x hx) +
    topInclPreimage n L data
      (FreeMetabelian.Free.weightProject n (by omega)
        (x - (terminalPrefixRelation n L data hn x hx : FreeModel n L)))

@[simp] theorem terminalPrefixError_coe (x : FreeModel n L)
    (hx : prLE n L n (by omega) x ∈ D n L data n (by omega)) :
    (terminalPrefixError n L data hn x hx : FreeModel n L) = x := by
  let rho := terminalPrefixRelation n L data hn x hx
  have hprefix : FreeMetabelian.Free.projectPrefix n (by omega) x =
      FreeMetabelian.Free.projectPrefix n (by omega) (rho : FreeModel n L) := by
    have hsection := relationPrefix_terminalRelationFullSection n L data hn
      (⟨prLE n L n (by omega) x, hx⟩ : D n L data n (by omega))
    change relationPrefix n L data n (by omega) rho =
      prLE n L n (by omega) x at hsection
    exact hsection.symm
  have htop := sub_eq_weightIncl_top_of_projectPrefix_eq
    n L x (rho : FreeModel n L) hprefix
  change (rho : FreeModel n L) +
      FreeMetabelian.Free.weightIncl n (by omega)
        (FreeMetabelian.Free.weightProject n (by omega)
          (x - (rho : FreeModel n L))) = x
  rw [← htop]
  abel

@[simp] theorem terminalEval_terminalPrefixError (x : FreeModel n L)
    (hx : prLE n L n (by omega) x ∈ D n L data n (by omega)) :
    terminalEval n L data (terminalPrefixError n L data hn x hx) =
      topCoord n L data
        (FreeMetabelian.Free.weightProject n (by omega)
          (x - (terminalPrefixRelation n L data hn x hx :
            FreeModel n L))) := by
  rw [terminalPrefixError, map_add, terminalEval_relationTopPreimage,
    zero_add]
  rfl

end

end LieRings.MetabelianVanishing
