import LieRings.DimensionSubring.DegreeFive.AdaptedCoordinateData

/-!
# Identities forced by the adapted presentation

The identities in `Coordinate.Data.Identities` are consequences of the actual relation rows.
They are not fields of the adapted presentation.  This file isolates the filtration argument
which removes the higher tails in a class-three target.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable {L : Type u} [LieRing L] [Finite L]

namespace StandingReductionData

local notation "F" => CanonicalFreeLie L
local notation "ev" => canonicalFreeLieEvaluation L

/-- Removing the certified homogeneous head of a collected relation row raises its minimum
weight by one. -/
theorem collectedRelationRow_sub_head_mem_lieHigh_succ
    (R : StandingReductionData L) (n : ℕ)
    (i : FreeLieExactBasisIndex L n) :
    (collectedRelationRow L L ev n i : F) -
        (collectedDiagonal L L ev n i : ℤ) •
          ((collectedHomogeneousBasis L L ev n i : freeLieExact L n) : F) ∈
      FreeLieDimension.lieHigh L (n + 1) := by
  apply mem_lieHigh_succ_of_component_eq_zero L
  · exact (FreeLieDimension.lieHigh L n).sub_mem
      (collectedRelationRow_mem_lieHigh L L ev n i)
      ((FreeLieDimension.lieHigh L n).smul_mem
        (collectedDiagonal L L ev n i : ℤ)
        (freeLieExact_mem_lieHigh L (collectedHomogeneousBasis L L ev n i)))
  · rw [map_sub, map_zsmul]
    have hhead := collectedRelationRow_head L L ev n i
    have hheadval := congrArg Subtype.val hhead
    change freeLieLengthComponent L n (collectedRelationRow L L ev n i : F) =
      (collectedDiagonal L L ev n i : ℤ) •
        ((collectedHomogeneousBasis L L ev n i : freeLieExact L n) : F) at hheadval
    rw [hheadval, freeLieLengthComponent_coe_exact]
    exact sub_self _

/-- Evaluation sends a free-Lie filtration term to the corresponding lower-central term. -/
theorem evaluation_mem_lowerCentralSeries_of_mem_lieHigh
    (R : StandingReductionData L) {n : ℕ} {x : F}
    (hx : x ∈ FreeLieDimension.lieHigh L n) :
    ev x ∈ lowerCentralSeries ℤ L (n - 1) := by
  cases n with
  | zero =>
      simpa using (LieSubmodule.mem_top (ev x) : ev x ∈ lowerCentralSeries ℤ L 0)
  | succ n =>
      have hx' : x ∈ lowerCentralSeries ℤ F n := by
        simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L n] using hx
      apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := ev) n)
      exact LieIdeal.mem_map hx'

/-- In a class-three target, the bracket of elements of lower-central weights adding to four
vanishes. -/
theorem bracket_eq_zero_of_mem_gamma_weights
    (R : StandingReductionData L) {a b : L} {m n : ℕ}
    (ha : a ∈ lowerCentralSeries ℤ L m)
    (hb : b ∈ lowerCentralSeries ℤ L n)
    (hmn : 3 ≤ m + n + 1) : ⁅a, b⁆ = 0 := by
  have habBracket : ⁅a, b⁆ ∈
      ⁅lowerCentralSeries ℤ L m, lowerCentralSeries ℤ L n⁆ :=
    LieSubmodule.lie_mem_lie ha hb
  have hab : ⁅a, b⁆ ∈ lowerCentralSeries ℤ L (m + n + 1) := by
    apply (show ⁅lowerCentralSeries ℤ L m, lowerCentralSeries ℤ L n⁆ ≤
        lowerCentralSeries ℤ L (m + n + 1) from ?_)
    · exact habBracket
    · calc
        ⁅lowerCentralSeries ℤ L m, lowerCentralSeries ℤ L n⁆ ≤
            ⁅dimensionSubring ℤ L (m + 1), dimensionSubring ℤ L (n + 1)⁆ :=
          LieSubmodule.mono_lie
            (lowerCentralSeries_le_dimensionSubring ℤ L m)
            (lowerCentralSeries_le_dimensionSubring ℤ L n)
        _ ≤ lowerCentralSeries ℤ L (m + n + 1) :=
          bracket_dimensionSubring_le_lowerCentralSeries ℤ L m n
  have hle : lowerCentralSeries ℤ L (m + n + 1) ≤ lowerCentralSeries ℤ L 3 :=
    LieModule.antitone_lowerCentralSeries ℤ L L hmn
  have : ⁅a, b⁆ ∈ lowerCentralSeries ℤ L 3 := hle hab
  rw [R.classThree] at this
  exact this

/-- An adapted homogeneous vector evaluates into the lower-central term prescribed by its
weight. -/
theorem evaluation_collectedHomogeneousBasis_mem_lowerCentralSeries
    (R : StandingReductionData L) (n : ℕ)
    (i : FreeLieExactBasisIndex L n) :
    ev ((collectedHomogeneousBasis L L ev n i : freeLieExact L n) : F) ∈
      lowerCentralSeries ℤ L (n - 1) :=
  R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh
    (freeLieExact_mem_lieHigh L (collectedHomogeneousBasis L L ev n i))

/-- The first Smith diagonal kills every `G` entry. -/
theorem coordinate_DG (R : StandingReductionData L)
    (i : CoordinateI L) (k : CoordinateK L) :
    (R.coordinateD i : ZMod R.q) * (R.coordinateG i k : ZMod R.q) = 0 := by
  let r : F := collectedRelationRow L L ev 1 i
  let x : F := R.coordinateX i
  let y : F := R.coordinateY k
  let rem : F := r - (R.coordinateD i : ℤ) • x
  have hremHigh : rem ∈ FreeLieDimension.lieHigh L 2 := by
    simpa [rem, r, x, coordinateD, coordinateX] using
      R.collectedRelationRow_sub_head_mem_lieHigh_succ 1 i
  have hremGamma : ev rem ∈ lowerCentralSeries ℤ L 1 := by
    simpa using R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh hremHigh
  have hyGamma : ev y ∈ lowerCentralSeries ℤ L 1 := by
    simpa [y, coordinateY] using
      R.evaluation_collectedHomogeneousBasis_mem_lowerCentralSeries 2 k
  have hremBracket : ⁅ev rem, ev y⁆ = 0 :=
    R.bracket_eq_zero_of_mem_gamma_weights hremGamma hyGamma (by omega)
  have hremEval : ev rem = -(R.coordinateD i : ℤ) • ev x := by
    simp only [rem, map_sub, map_zsmul]
    rw [show ev r = 0 by
      exact collectedRelationRow_mem_ker L L ev 1 i]
    simp
  have hbracket : R.coordinateD i • ⁅ev x, ev y⁆ = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← smul_lie]
    have hdx : (R.coordinateD i : ℤ) • ev x = -ev rem := by
      rw [hremEval]
      module
    rw [hdx, neg_lie, hremBracket, neg_zero]
  have hsubtype : R.coordinateD i • R.coordinateBracketGammaThree i k = 0 := by
    apply Subtype.ext
    simpa [coordinateBracketGammaThree, x, y] using hbracket
  rw [R.coordinateG_cast]
  change (R.coordinateD i : ZMod (2 ^ R.gammaThreeExponent)) *
      R.gammaThreeEquiv (R.coordinateBracketGammaThree i k) = 0
  rw [← nsmul_eq_mul]
  calc
    R.coordinateD i • R.gammaThreeEquiv (R.coordinateBracketGammaThree i k) =
        R.gammaThreeEquiv
          (R.coordinateD i • R.coordinateBracketGammaThree i k) :=
      (R.gammaThreeEquiv.toAddMonoidHom.map_nsmul _ _).symm
    _ = R.gammaThreeEquiv 0 := congrArg
      (fun z : lowerCentralSeries ℤ L 2 ↦ R.gammaThreeEquiv z) hsubtype
    _ = 0 := R.gammaThreeEquiv.toAddMonoidHom.map_zero

/-- The second Smith diagonal kills every `G` entry. -/
theorem coordinate_GE (R : StandingReductionData L)
    (i : CoordinateI L) (k : CoordinateK L) :
    (R.coordinateG i k : ZMod R.q) * (R.coordinateE k : ZMod R.q) = 0 := by
  let s : F := collectedRelationRow L L ev 2 k
  let x : F := R.coordinateX i
  let y : F := R.coordinateY k
  let rem : F := s - (R.coordinateE k : ℤ) • y
  have hremHigh : rem ∈ FreeLieDimension.lieHigh L 3 := by
    simpa [rem, s, y, coordinateE, coordinateY] using
      R.collectedRelationRow_sub_head_mem_lieHigh_succ 2 k
  have hremGamma : ev rem ∈ lowerCentralSeries ℤ L 2 := by
    simpa using R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh hremHigh
  have hxGamma : ev x ∈ lowerCentralSeries ℤ L 0 := by
    exact LieSubmodule.mem_top (ev x)
  have hremBracket : ⁅ev x, ev rem⁆ = 0 :=
    R.bracket_eq_zero_of_mem_gamma_weights hxGamma hremGamma (by omega)
  have hremEval : ev rem = -(R.coordinateE k : ℤ) • ev y := by
    simp only [rem, map_sub, map_zsmul]
    rw [show ev s = 0 by
      exact collectedRelationRow_mem_ker L L ev 2 k]
    simp
  have hbracket : R.coordinateE k • ⁅ev x, ev y⁆ = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← lie_smul]
    have hey : (R.coordinateE k : ℤ) • ev y = -ev rem := by
      rw [hremEval]
      module
    rw [hey, lie_neg, hremBracket, neg_zero]
  have hsubtype : R.coordinateE k • R.coordinateBracketGammaThree i k = 0 := by
    apply Subtype.ext
    simpa [coordinateBracketGammaThree, x, y] using hbracket
  rw [R.coordinateG_cast]
  rw [mul_comm]
  change (R.coordinateE k : ZMod (2 ^ R.gammaThreeExponent)) *
      R.gammaThreeEquiv (R.coordinateBracketGammaThree i k) = 0
  rw [← nsmul_eq_mul]
  calc
    R.coordinateE k • R.gammaThreeEquiv (R.coordinateBracketGammaThree i k) =
        R.gammaThreeEquiv
          (R.coordinateE k • R.coordinateBracketGammaThree i k) :=
      (R.gammaThreeEquiv.toAddMonoidHom.map_nsmul _ _).symm
    _ = R.gammaThreeEquiv 0 := congrArg
      (fun z : lowerCentralSeries ℤ L 2 ↦ R.gammaThreeEquiv z) hsubtype
    _ = 0 := R.gammaThreeEquiv.toAddMonoidHom.map_zero

/-! ## The `B Gᵀ` identities -/

/-- The actual degree-two element denoted `B_i`. -/
def coordinateBValue (R : StandingReductionData L) (i : CoordinateI L) : F :=
  ∑ k, R.coordinateB i k • R.coordinateY k

theorem coordinateBValue_mem_lieHigh_two (R : StandingReductionData L)
    (i : CoordinateI L) :
    R.coordinateBValue i ∈ FreeLieDimension.lieHigh L 2 := by
  classical
  apply Submodule.sum_mem
  intro k hk
  exact (FreeLieDimension.lieHigh L 2).smul_mem _
    (freeLieExact_mem_lieHigh L (collectedHomogeneousBasis L L ev 2 k))

/-- After removing `d_i x_i-B_i`, the first relation row begins in weight three. -/
theorem firstRow_sub_coordinate_terms_mem_lieHigh_three
    (R : StandingReductionData L) (i : CoordinateI L) :
    (collectedRelationRow L L ev 1 i : F) -
        (R.coordinateD i : ℤ) • R.coordinateX i + R.coordinateBValue i ∈
      FreeLieDimension.lieHigh L 3 := by
  let u : F := (collectedRelationRow L L ev 1 i : F) -
    (R.coordinateD i : ℤ) • R.coordinateX i
  apply mem_lieHigh_succ_of_component_eq_zero L
  · exact (FreeLieDimension.lieHigh L 2).add_mem
      (by simpa [u, coordinateD, coordinateX] using
        R.collectedRelationRow_sub_head_mem_lieHigh_succ 1 i)
      (R.coordinateBValue_mem_lieHigh_two i)
  · rw [map_add, map_sub, map_zsmul]
    have hr := R.firstRow_degreeTwo_eq_neg_B_sum i
    change freeLieLengthComponent L 2 (collectedRelationRow L L ev 1 i : F) =
      -R.coordinateBValue i at hr
    rw [hr]
    have hxzero : freeLieLengthComponent L 2 (R.coordinateX i) = 0 := by
      exact freeLieLengthComponent_coe_exact_of_ne L
        (collectedHomogeneousBasis L L ev 1 i) (by omega)
    rw [hxzero, smul_zero, sub_zero]
    have hB : freeLieLengthComponent L 2 (R.coordinateBValue i) =
        R.coordinateBValue i := by
      classical
      unfold coordinateBValue
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [map_zsmul]
      unfold coordinateY
      rw [freeLieLengthComponent_coe_exact]
    rw [hB, neg_add_cancel]

/-- The bracket `[x_j,B_i]`, naturally an element of `γ₃(L)`. -/
def coordinateBGammaThree (R : StandingReductionData L)
    (i j : CoordinateI L) : lowerCentralSeries ℤ L 2 :=
  ⟨⁅ev (R.coordinateX j), ev (R.coordinateBValue i)⁆, by
    have hx : ev (R.coordinateX j) ∈ lowerCentralSeries ℤ L 0 :=
      LieSubmodule.mem_top _
    have hB : ev (R.coordinateBValue i) ∈ lowerCentralSeries ℤ L 1 := by
      simpa using R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh
        (R.coordinateBValue_mem_lieHigh_two i)
    change ⁅ev (R.coordinateX j), ev (R.coordinateBValue i)⁆ ∈
      LieModule.lowerCentralSeries ℤ L L (1 + 1)
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie hx hB⟩

/-- Coordinate form of `d_i [x_j,x_i]=[x_j,B_i]`. -/
theorem coordinate_bracket_data (R : StandingReductionData L)
    (i j : CoordinateI L) :
    R.gammaThreeEquiv (R.coordinateBGammaThree i j) =
      (R.coordinateData).gamma i j := by
  have hsubtype : R.coordinateBGammaThree i j =
      ∑ k, R.coordinateB i k • R.coordinateBracketGammaThree j k := by
    apply Subtype.ext
    have hcoe :
        (((∑ k, R.coordinateB i k • R.coordinateBracketGammaThree j k) :
          lowerCentralSeries ℤ L 2) : L) =
          ∑ k, ((R.coordinateB i k • R.coordinateBracketGammaThree j k :
            lowerCentralSeries ℤ L 2) : L) := by
      exact map_sum (lowerCentralSeries ℤ L 2).subtype _ Finset.univ
    rw [hcoe]
    simp only [coordinateBGammaThree]
    change ⁅ev (R.coordinateX j), ev (R.coordinateBValue i)⁆ =
      ∑ k, ((R.coordinateB i k • R.coordinateBracketGammaThree j k :
        lowerCentralSeries ℤ L 2) : L)
    unfold coordinateBValue
    rw [map_sum, lie_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_zsmul, lie_smul]
    rfl
  calc
    R.gammaThreeEquiv (R.coordinateBGammaThree i j) = R.gammaThreeEquiv
        (∑ k, R.coordinateB i k • R.coordinateBracketGammaThree j k) :=
      congrArg (fun z : lowerCentralSeries ℤ L 2 ↦ R.gammaThreeEquiv z) hsubtype
    _ = ∑ k, (R.coordinateB i k : ZMod (2 ^ R.gammaThreeExponent)) *
          R.gammaThreeEquiv (R.coordinateBracketGammaThree j k) := by
      change R.gammaThreeEquiv.toAddMonoidHom
          (∑ k, R.coordinateB i k • R.coordinateBracketGammaThree j k) = _
      rw [map_sum R.gammaThreeEquiv.toAddMonoidHom]
      apply Finset.sum_congr rfl
      intro k hk
      rw [map_zsmul R.gammaThreeEquiv.toAddMonoidHom]
      rw [zsmul_eq_mul]
      rfl
    _ = (R.coordinateData).gamma i j := by
      simp only [Coordinate.Data.gamma, coordinateData, coordinateG_cast,
        coordinateGMod]
      rfl

/-- The semantic equality behind the bracket-data coordinate. -/
theorem coordinateBGammaThree_eq_scaled_bracket
    (R : StandingReductionData L) (i j : CoordinateI L) :
    (R.coordinateBGammaThree i j : L) =
      (R.coordinateD i : ℤ) •
        ⁅ev (R.coordinateX j), ev (R.coordinateX i)⁆ := by
  let h : F := (collectedRelationRow L L ev 1 i : F) -
    (R.coordinateD i : ℤ) • R.coordinateX i + R.coordinateBValue i
  have hh : h ∈ FreeLieDimension.lieHigh L 3 :=
    R.firstRow_sub_coordinate_terms_mem_lieHigh_three i
  have hhGamma : ev h ∈ lowerCentralSeries ℤ L 2 := by
    simpa using R.evaluation_mem_lowerCentralSeries_of_mem_lieHigh hh
  have hxTop : ev (R.coordinateX j) ∈ lowerCentralSeries ℤ L 0 :=
    LieSubmodule.mem_top _
  have hcentral : ⁅ev (R.coordinateX j), ev h⁆ = 0 :=
    R.bracket_eq_zero_of_mem_gamma_weights hxTop hhGamma (by omega)
  have hevalh : ev h =
      -(R.coordinateD i : ℤ) • ev (R.coordinateX i) +
        ev (R.coordinateBValue i) := by
    simp only [h, map_add, map_sub, map_zsmul]
    rw [show ev (collectedRelationRow L L ev 1 i : F) = 0 by
      exact collectedRelationRow_mem_ker L L ev 1 i]
    module
  rw [hevalh, lie_add, lie_smul] at hcentral
  change ⁅ev (R.coordinateX j), ev (R.coordinateBValue i)⁆ = _
  calc
    ⁅ev (R.coordinateX j), ev (R.coordinateBValue i)⁆ =
        (R.coordinateD i : ℤ) •
          ⁅ev (R.coordinateX j), ev (R.coordinateX i)⁆ := by
      apply eq_of_sub_eq_zero
      calc
        ⁅ev (R.coordinateX j), ev (R.coordinateBValue i)⁆ -
            (R.coordinateD i : ℤ) •
              ⁅ev (R.coordinateX j), ev (R.coordinateX i)⁆ =
            (-(R.coordinateD i : ℤ)) •
                ⁅ev (R.coordinateX j), ev (R.coordinateX i)⁆ +
              ⁅ev (R.coordinateX j), ev (R.coordinateBValue i)⁆ := by module
        _ = 0 := hcentral
    _ = _ := rfl

theorem coordinate_gamma_diag (R : StandingReductionData L)
    (i : CoordinateI L) : (R.coordinateData).gamma i i = 0 := by
  rw [← R.coordinate_bracket_data i i]
  have hzero : R.coordinateBGammaThree i i = 0 := by
    apply Subtype.ext
    rw [R.coordinateBGammaThree_eq_scaled_bracket i i]
    simp
  rw [hzero]
  exact R.gammaThreeEquiv.toAddMonoidHom.map_zero

theorem coordinate_gamma_skew (R : StandingReductionData L)
    {i j : CoordinateI L} (hij : i < j) :
    (R.coordinateData).gamma j i +
        ((R.coordinateData).dRatio i j : ZMod R.q) *
          (R.coordinateData).gamma i j = 0 := by
  have hdvd : R.coordinateD i ∣ R.coordinateD j :=
    R.coordinateD_dvd_of_le (le_of_lt hij)
  have hratioNat : R.coordinateD i *
      (R.coordinateData).dRatio i j = R.coordinateD j := by
    exact Nat.mul_div_cancel' hdvd
  have hratioInt : (R.coordinateD j : ℤ) =
      ((R.coordinateData).dRatio i j : ℤ) * (R.coordinateD i : ℤ) := by
    exact_mod_cast hratioNat.symm.trans (Nat.mul_comm _ _)
  have hbg : R.coordinateBGammaThree j i +
      (R.coordinateData).dRatio i j • R.coordinateBGammaThree i j = 0 := by
    apply Subtype.ext
    change (lowerCentralSeries ℤ L 2).subtype
        (R.coordinateBGammaThree j i +
          (R.coordinateData).dRatio i j • R.coordinateBGammaThree i j) =
      (lowerCentralSeries ℤ L 2).subtype 0
    rw [(lowerCentralSeries ℤ L 2).subtype.map_add]
    have hnsmul : (lowerCentralSeries ℤ L 2).subtype
        ((R.coordinateData).dRatio i j • R.coordinateBGammaThree i j) =
      (R.coordinateData).dRatio i j •
        (lowerCentralSeries ℤ L 2).subtype (R.coordinateBGammaThree i j) :=
      (lowerCentralSeries ℤ L 2).subtype.toAddMonoidHom.map_nsmul _ _
    have hji := R.coordinateBGammaThree_eq_scaled_bracket j i
    have hij' := R.coordinateBGammaThree_eq_scaled_bracket i j
    change (lowerCentralSeries ℤ L 2).subtype (R.coordinateBGammaThree j i) = _ at hji
    change (lowerCentralSeries ℤ L 2).subtype (R.coordinateBGammaThree i j) = _ at hij'
    rw [hnsmul, (lowerCentralSeries ℤ L 2).subtype.map_zero, hji, hij']
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
    rw [← lie_skew (ev (R.coordinateX i)) (ev (R.coordinateX j))]
    rw [hratioInt]
    module
  rw [← R.coordinate_bracket_data j i, ← R.coordinate_bracket_data i j]
  change R.gammaThreeEquiv (R.coordinateBGammaThree j i) +
      ((R.coordinateData).dRatio i j :
        ZMod (2 ^ R.gammaThreeExponent)) *
        R.gammaThreeEquiv (R.coordinateBGammaThree i j) = 0
  rw [← nsmul_eq_mul]
  calc
    R.gammaThreeEquiv (R.coordinateBGammaThree j i) +
        (R.coordinateData).dRatio i j •
          R.gammaThreeEquiv (R.coordinateBGammaThree i j) =
      R.gammaThreeEquiv (R.coordinateBGammaThree j i) +
        R.gammaThreeEquiv
          ((R.coordinateData).dRatio i j • R.coordinateBGammaThree i j) := by
            congr 1
            exact (R.gammaThreeEquiv.toAddMonoidHom.map_nsmul _ _).symm
    _ = R.gammaThreeEquiv
        (R.coordinateBGammaThree j i +
          (R.coordinateData).dRatio i j • R.coordinateBGammaThree i j) :=
      (R.gammaThreeEquiv.toAddMonoidHom.map_add _ _).symm
    _ = R.gammaThreeEquiv 0 := congrArg
      (fun z : lowerCentralSeries ℤ L 2 ↦ R.gammaThreeEquiv z) hbg
    _ = 0 := R.gammaThreeEquiv.toAddMonoidHom.map_zero

/-- All five identities required by the coordinate certificate, derived from the standing
reduction and the constructed Smith rows. -/
def coordinateIdentities (R : StandingReductionData L) :
    (R.coordinateData).Identities where
  d_dvd := fun {_ _} hij ↦ R.coordinateData_d_dvd hij
  DG := R.coordinate_DG
  GE := R.coordinate_GE
  gamma_diag := R.coordinate_gamma_diag
  gamma_skew := R.coordinate_gamma_skew


end StandingReductionData

end

end DegreeFive

end LieRings
