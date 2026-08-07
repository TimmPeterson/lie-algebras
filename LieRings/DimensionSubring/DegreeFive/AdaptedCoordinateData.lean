import LieRings.DimensionSubring.DegreeFive.AdaptedCollectorBasis

/-!
# Coordinate data read from the shared adapted collector basis

The definitions in this file do not make any new basis choices.  The index sets `I` and `K`,
the diagonals `d,e`, the relation-tail matrix `B`, and the bracket matrix `G` are all read from
`collectedHomogeneousBasis` and `collectedRelationRow`.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable {L : Type u} [LieRing L] [Finite L]

namespace StandingReductionData

variable (R : StandingReductionData L)

local notation "F" => CanonicalFreeLie L
local notation "ev" => canonicalFreeLieEvaluation L

/-- Generator indices and named weight-two indices used by the coordinate proof.  Unit Smith
entries automatically represent supplementary directions, so no second basis is introduced. -/
abbrev CoordinateI (L : Type u) [Finite L] := FreeLieExactBasisIndex L 1
abbrev CoordinateK (L : Type u) [Finite L] := FreeLieExactBasisIndex L 2

/-- The actual adapted generator `x_i`. -/
def coordinateX (R : StandingReductionData L) (i : CoordinateI L) : F :=
  (collectedHomogeneousBasis L L ev 1 i : freeLieExact L 1)

/-- The actual adapted weight-two basis element `y_k`. -/
def coordinateY (R : StandingReductionData L) (k : CoordinateK L) : F :=
  (collectedHomogeneousBasis L L ev 2 k : freeLieExact L 2)

/-- Positive first and second Smith diagonals. -/
def coordinateD (R : StandingReductionData L) (i : CoordinateI L) : ℕ :=
  collectedDiagonal L L ev 1 i
def coordinateE (R : StandingReductionData L) (k : CoordinateK L) : ℕ :=
  collectedDiagonal L L ev 2 k

theorem coordinateD_pos (i : CoordinateI L) : 0 < R.coordinateD i :=
  collectedDiagonal_pos L L ev 1 i

theorem coordinateE_pos (k : CoordinateK L) : 0 < R.coordinateE k :=
  collectedDiagonal_pos L L ev 2 k

theorem coordinateD_dvd_of_le {i j : CoordinateI L} (hij : i ≤ j) :
    R.coordinateD i ∣ R.coordinateD j :=
  R.collectedDiagonal_dvd_of_le ev 1 hij

/-! ## The actual `B` matrix -/

/-- Coordinates of the degree-two component of the first adapted relation row. -/
def firstRowDegreeTwoCoordinates (R : StandingReductionData L)
    (i : CoordinateI L) : CoordinateK L →₀ ℤ :=
  (collectedHomogeneousBasis L L ev 2).repr
    ⟨freeLieLengthComponent L 2 (collectedRelationRow L L ev 1 i : F),
      freeLieLengthComponent_mem_exact L 2 _⟩

/-- `B` is defined with the sign in `r_i=d_i x_i-B_i-(higher terms)`. -/
def coordinateB (R : StandingReductionData L)
    (i : CoordinateI L) (k : CoordinateK L) : ℤ :=
  -R.firstRowDegreeTwoCoordinates i k

/-- The degree-two component of `r_i` is exactly `-∑_k B_ik y_k`. -/
theorem firstRow_degreeTwo_eq_neg_B_sum (i : CoordinateI L) :
    freeLieLengthComponent L 2 (collectedRelationRow L L ev 1 i : F) =
      -∑ k, R.coordinateB i k • R.coordinateY k := by
  classical
  let v : freeLieExact L 2 :=
    ⟨freeLieLengthComponent L 2 (collectedRelationRow L L ev 1 i : F),
      freeLieLengthComponent_mem_exact L 2 _⟩
  let c := (collectedHomogeneousBasis L L ev 2).repr v
  have h := (collectedHomogeneousBasis L L ev 2).linearCombination_repr v
  have hsum : (∑ k, c k • R.coordinateY k) = (v : F) := by
    calc
      (∑ k, c k • R.coordinateY k) =
          (freeLieExact L 2).subtype
            (c.sum (fun k z ↦ z • collectedHomogeneousBasis L L ev 2 k)) := by
        rw [← Finsupp.sum_fintype c
          (fun k z ↦ z • R.coordinateY k) (by intro k; simp)]
        rw [map_finsuppSum]
        apply Finsupp.sum_congr
        intro k hk
        rw [map_zsmul]
        rfl
      _ = (v : F) := congrArg Subtype.val h
  change (v : F) = -∑ k, (-c k) • R.coordinateY k
  rw [← hsum]
  simp only [neg_smul, Finset.sum_neg_distrib, neg_neg]

/-! ## The actual `G` matrix -/

/-- The bracket of an adapted weight-one and weight-two basis vector, in `γ₃(L)`. -/
def coordinateBracketGammaThree (R : StandingReductionData L)
    (i : CoordinateI L) (k : CoordinateK L) :
    lowerCentralSeries ℤ L 2 :=
  ⟨⁅ev (R.coordinateX i), ev (R.coordinateY k)⁆, by
    rw [← LieHom.map_lie]
    apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) 2)
    apply LieIdeal.mem_map
    have hx : R.coordinateX i ∈ FreeLieDimension.lieHigh L 1 :=
      freeLieExact_mem_lieHigh L
        (collectedHomogeneousBasis L L ev 1 i)
    have hy : R.coordinateY k ∈ FreeLieDimension.lieHigh L 2 :=
      freeLieExact_mem_lieHigh L
        (collectedHomogeneousBasis L L ev 2 k)
    have hxy := FreeLieDimension.lieHigh_lie_mem L hx hy
    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L 2] using hxy⟩

/-- The intrinsic bracket coordinate in `ZMod q`. -/
def coordinateGMod (R : StandingReductionData L)
    (i : CoordinateI L) (k : CoordinateK L) : ZMod R.q :=
  R.gammaThreeEquiv (R.coordinateBracketGammaThree i k)

/-- A fixed integral representative of the bracket coordinate. -/
def coordinateG (R : StandingReductionData L)
    (i : CoordinateI L) (k : CoordinateK L) : ℤ :=
  (R.coordinateGMod i k).cast

@[simp]
theorem coordinateG_cast (i : CoordinateI L) (k : CoordinateK L) :
    (R.coordinateG i k : ZMod R.q) = R.coordinateGMod i k := by
  exact ZMod.intCast_zmod_cast _

/-- The complete matrix datum consumed by the existing coordinate PBW proof. -/
def coordinateData (R : StandingReductionData L) :
    Coordinate.Data (CoordinateI L) (CoordinateK L) R.q where
  d := R.coordinateD
  e := R.coordinateE
  B := R.coordinateB
  G := R.coordinateG

theorem coordinateData_d_dvd {i j : CoordinateI L} (hij : i ≤ j) :
    (R.coordinateData).d i ∣ (R.coordinateData).d j :=
  R.coordinateD_dvd_of_le hij

end StandingReductionData

end


end DegreeFive

end LieRings
