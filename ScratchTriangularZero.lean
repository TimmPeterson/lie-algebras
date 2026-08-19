import LieRings.DimensionSubring.MetabelianVanishing.TriangularRows

namespace LieRings.MetabelianVanishing
open FreeMetabelian
universe u
noncomputable section
variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
#check pSmith
#check triangularSmith
#check FreeMetabelian.Free.PieceIndex
#check relationLeading_finrank_eq
#check pZeroBasis
#check InvariantFactorPresentation.rank
#check LieRings.DegreeFive.PositiveSmithPresentation
set_option pp.universes false in
#check (pSmith n L).ambientBasis
set_option pp.universes false in
#check (triangularSmith n L data 0 (by omega)).ambientBasis
end
end LieRings.MetabelianVanishing
