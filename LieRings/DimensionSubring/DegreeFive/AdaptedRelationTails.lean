import LieRings.DimensionSubring.DegreeFive.AdaptedIdentities

/-!
# The degree-three tails of the adapted relations

The coordinate proof only remembers the image in the cyclic group `γ₃(L)`.  The definitions
below extract that image from the actual relation rows; no tail coefficient is supplied as
presentation data.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable {L : Type u} [LieRing L] [Finite L]

namespace StandingReductionData

local notation "F" => CanonicalFreeLie L
local notation "ev" => canonicalFreeLieEvaluation L

/-- The weight-three remainder of `r_i=d_i x_i-B_i-(weight three)`. -/
def firstRelationTail (R : StandingReductionData L) (i : CoordinateI L) : F :=
  (collectedRelationRow L L ev 1 i : F) -
    (R.coordinateD i : ℤ) • R.coordinateX i + R.coordinateBValue i

theorem firstRelationTail_mem_lieHigh_three (R : StandingReductionData L)
    (i : CoordinateI L) :
    R.firstRelationTail i ∈ FreeLieDimension.lieHigh L 3 :=
  R.firstRow_sub_coordinate_terms_mem_lieHigh_three i

/-- Its image, bundled in `γ₃(L)`. -/
def firstRelationTailGammaThree (R : StandingReductionData L)
    (i : CoordinateI L) : lowerCentralSeries ℤ L 2 :=
  ⟨ev (R.firstRelationTail i), by
    simpa using R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh
      (R.firstRelationTail_mem_lieHigh_three i)⟩

/-- The coefficient `c_i`; the sign agrees with `r_i=d_i x_i-B_i-c_i z`. -/
def coordinateC (R : StandingReductionData L) (i : CoordinateI L) : ℤ :=
  (-R.gammaThreeEquiv (R.firstRelationTailGammaThree i)).cast

@[simp]
theorem coordinateC_cast (R : StandingReductionData L) (i : CoordinateI L) :
    (R.coordinateC i : ZMod R.q) =
      -R.gammaThreeEquiv (R.firstRelationTailGammaThree i) := by
  exact ZMod.intCast_zmod_cast _

/-- The weight-three remainder of `s_k=e_k y_k-(weight three)`. -/
def secondRelationTail (R : StandingReductionData L) (k : CoordinateK L) : F :=
  (collectedRelationRow L L ev 2 k : F) -
    (R.coordinateE k : ℤ) • R.coordinateY k

theorem secondRelationTail_mem_lieHigh_three (R : StandingReductionData L)
    (k : CoordinateK L) :
    R.secondRelationTail k ∈ FreeLieDimension.lieHigh L 3 := by
  simpa [secondRelationTail, coordinateE, coordinateY] using
    R.collectedRelationRow_sub_head_mem_lieHigh_succ 2 k

/-- Its image, bundled in `γ₃(L)`. -/
def secondRelationTailGammaThree (R : StandingReductionData L)
    (k : CoordinateK L) : lowerCentralSeries ℤ L 2 :=
  ⟨ev (R.secondRelationTail k), by
    simpa using R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh
      (R.secondRelationTail_mem_lieHigh_three k)⟩

/-- The coefficient `m_k`; the sign agrees with `s_k=e_k y_k-m_k z`. -/
def coordinateM (R : StandingReductionData L) (k : CoordinateK L) : ℤ :=
  (-R.gammaThreeEquiv (R.secondRelationTailGammaThree k)).cast

@[simp]
theorem coordinateM_cast (R : StandingReductionData L) (k : CoordinateK L) :
    (R.coordinateM k : ZMod R.q) =
      -R.gammaThreeEquiv (R.secondRelationTailGammaThree k) := by
  exact ZMod.intCast_zmod_cast _

/-- The tails consumed by the already proved formal word collection. -/
def coordinateRelationTails (R : StandingReductionData L) :
    Coordinate.Data.RelationTails
      (I := CoordinateI L) (K := CoordinateK L) where
  c := R.coordinateC
  m := R.coordinateM

end StandingReductionData

end

end DegreeFive

end LieRings
