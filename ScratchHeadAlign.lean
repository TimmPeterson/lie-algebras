import LieRings.DimensionSubring.MetabelianVanishing.TriangularRows

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

example
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) 0) :
    FreeMetabelian.Free.weightIncl 0 (by omega)
        (((triangularSmith n L data 0 (by omega)).diagonal i : ℤ) •
          triangularPieceBasis n L data 0 (by omega) i) =
      ((triangularSmith n L data 0 (by omega)).diagonal i : ℤ) •
        adaptedBasis n L data hn
          (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
            AdaptedIndex n L data hn) := by
  rw [adaptedBasis_apply, map_zsmul]
  simp only
  have hb : triangularPieceBasis n L data 0 (by omega) i =
      pieceAdaptedBasis n L data hn (⟨0, by omega⟩ : Fin (n + 1)) i := by
    unfold pieceAdaptedBasis
    simp only [Fin.zero_eta, ↓reduceDIte]
    apply eq_of_heq
    apply congrArg_heq
    · exact cast_heq _ _
    · rfl
  rw [hb]
  rfl

end

end LieRings.MetabelianVanishing
