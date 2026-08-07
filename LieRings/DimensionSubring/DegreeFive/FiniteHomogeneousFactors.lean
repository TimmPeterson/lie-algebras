import LieRings.DimensionSubring.DegreeFive.FiniteRelationRowExpansion
import LieRings.DimensionSubring.DegreeFive.FilteredPackets

/-!
# Finite homogeneous factors below weight five

For a finite free generating type, this file packages the chosen bases in weights one through
four into one finite ordered type.  It also expands the bracket of two homogeneous basis factors
in the basis of the summed weight.  These are the coefficient-level ordinary PBW corrections
used by the placed collector.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]

local notation "F" => FreeLieAlgebra ℤ X

/-- A homogeneous nonassociative polynomial maps to the matching homogeneous associative
component. -/
theorem magmaToFreeAlgebra_mem_exact {n : ℕ}
    {p : FreeNonUnitalNonAssocAlgebra ℤ X} (hp : p ∈ magmaExact X n) :
    FreeLieDimension.magmaToFreeAlgebra X p ∈
      FreeLieDimension.associativeExact X n := by
  rw [magmaExact, Finsupp.supported_eq_span_single] at hp
  induction hp using Submodule.span_induction with
  | mem q hq =>
      obtain ⟨w, hw, rfl⟩ := hq
      rw [← hw]
      exact FreeLieDimension.magmaToFreeAlgebra_single_mem_exact X w
  | zero => simp
  | add a b ha hb ihA ihB =>
      rw [map_add]
      exact (FreeLieDimension.associativeExact X n).add_mem ihA ihB
  | smul c a ha ih =>
      rw [map_smul]
      exact (FreeLieDimension.associativeExact X n).smul_mem c ih

/-- The Magnus image of an element of `freeLieExact X n` is homogeneous of weight `n`. -/
theorem freeLieToFreeAlgebra_mem_exact {n : ℕ} (x : freeLieExact X n) :
    PBW.freeLieToFreeAlgebra ℤ X (x : F) ∈
      FreeLieDimension.associativeExact X n := by
  obtain ⟨p, hp, hpx⟩ := x.property
  rw [← hpx]
  rw [FreeLieDimension.freeLieToFreeAlgebra_mk]
  exact magmaToFreeAlgebra_mem_exact X hp

/-- Bracketing exact free-Lie components adds their homogeneous weights. -/
theorem freeLieExact_bracket_mem {m n : ℕ}
    (x : freeLieExact X m) (y : freeLieExact X n) :
    ⁅(x : F), (y : F)⁆ ∈ freeLieExact X (m + n) := by
  let z : F := freeLieLengthComponent X (m + n) ⁅(x : F), (y : F)⁆
  have hz : z ∈ freeLieExact X (m + n) :=
    freeLieLengthComponent_mem_exact X (m + n) _
  have himageExact : PBW.freeLieToFreeAlgebra ℤ X ⁅(x : F), (y : F)⁆ ∈
      FreeLieDimension.associativeExact X (m + n) := by
    rw [LieHom.map_lie]
    exact FreeLieDimension.associativeExact_lie X
      (freeLieToFreeAlgebra_mem_exact X x)
      (freeLieToFreeAlgebra_mem_exact X y)
  have hzEq : z = ⁅(x : F), (y : F)⁆ := by
    apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
    rw [freeLieToFreeAlgebra_freeLieLengthComponent]
    exact associativeLengthComponent_eq_self_of_mem_exact X himageExact
  exact hzEq ▸ hz

/-- The disjoint union of homogeneous basis factors in weights one through four. -/
abbrev LowHomogeneousBasisIndex :=
  Σ k : Fin 4, FreeLieExactBasisIndex X (k.1 + 1)

/-- Homogeneous weight of a low basis factor. -/
def lowHomogeneousBasisWeight (i : LowHomogeneousBasisIndex X) : ℕ :=
  i.1.1 + 1

/-- Actual free-Lie value of a low homogeneous basis factor. -/
def lowHomogeneousBasisValue (i : LowHomogeneousBasisIndex X) : F :=
  (freeLieExactBasis X (i.1.1 + 1) i.2 : freeLieExact X (i.1.1 + 1))

theorem lowHomogeneousBasisWeight_pos (i : LowHomogeneousBasisIndex X) :
    0 < lowHomogeneousBasisWeight X i := by
  simp [lowHomogeneousBasisWeight]

theorem lowHomogeneousBasisWeight_le_four (i : LowHomogeneousBasisIndex X) :
    lowHomogeneousBasisWeight X i ≤ 4 := by
  have hi := i.1.2
  simp [lowHomogeneousBasisWeight] at hi ⊢

theorem lowHomogeneousBasisValue_mem_exact (i : LowHomogeneousBasisIndex X) :
    lowHomogeneousBasisValue X i ∈
      freeLieExact X (lowHomogeneousBasisWeight X i) := by
  exact (freeLieExactBasis X (i.1.1 + 1) i.2).property

/-- Embed an exact basis index of any positive weight at most four into the common low-factor
index type. -/
def lowHomogeneousBasisIndexOf {n : ℕ} (hn : 0 < n) (hn4 : n ≤ 4)
    (i : FreeLieExactBasisIndex X n) : LowHomogeneousBasisIndex X := by
  cases n with
  | zero => omega
  | succ k => exact ⟨⟨k, by omega⟩, i⟩

@[simp]
theorem lowHomogeneousBasisWeight_indexOf {n : ℕ} (hn : 0 < n) (hn4 : n ≤ 4)
    (i : FreeLieExactBasisIndex X n) :
    lowHomogeneousBasisWeight X (lowHomogeneousBasisIndexOf X hn hn4 i) = n := by
  cases n with
  | zero => omega
  | succ k => simp [lowHomogeneousBasisWeight, lowHomogeneousBasisIndexOf]

theorem lowHomogeneousBasisValue_indexOf {n : ℕ} (hn : 0 < n) (hn4 : n ≤ 4)
    (i : FreeLieExactBasisIndex X n) :
    lowHomogeneousBasisValue X (lowHomogeneousBasisIndexOf X hn hn4 i) =
      ((freeLieExactBasis X n i : freeLieExact X n) : F) := by
  cases n with
  | zero => omega
  | succ k =>
      simp [lowHomogeneousBasisValue, lowHomogeneousBasisIndexOf]
      rfl

/-- A low homogeneous basis factor as a semantic filtered factor. -/
def lowHomogeneousFilteredFactor (i : LowHomogeneousBasisIndex X) :
    FilteredLieFactor X where
  value := lowHomogeneousBasisValue X i
  weight := lowHomogeneousBasisWeight X i
  weight_pos := lowHomogeneousBasisWeight_pos X i
  filtered := by
    obtain ⟨p, hp, hvalue⟩ := lowHomogeneousBasisValue_mem_exact X i
    refine ⟨p, ?_, hvalue⟩
    intro w hw
    exact (hp hw).ge

/-- Coefficients of the homogeneous bracket correction in its exact basis. -/
def homogeneousBracketCoefficients
    {m n : ℕ} (x : freeLieExact X m) (y : freeLieExact X n) :
    FreeLieExactBasisIndex X (m + n) →₀ ℤ :=
  (freeLieExactBasis X (m + n)).repr
    ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩

/-- Bracket coefficients embedded in the common low-factor index type. -/
def lowHomogeneousBracketCoefficients
    (x y : LowHomogeneousBasisIndex X)
    (hxy : lowHomogeneousBasisWeight X x + lowHomogeneousBasisWeight X y ≤ 4) :
    LowHomogeneousBasisIndex X →₀ ℤ :=
  let m := lowHomogeneousBasisWeight X x
  let n := lowHomogeneousBasisWeight X y
  (homogeneousBracketCoefficients X
      ⟨lowHomogeneousBasisValue X x, lowHomogeneousBasisValue_mem_exact X x⟩
      ⟨lowHomogeneousBasisValue X y, lowHomogeneousBasisValue_mem_exact X y⟩).mapDomain
    (lowHomogeneousBasisIndexOf X
      (Nat.add_pos_left (lowHomogeneousBasisWeight_pos X x) _) hxy)

/-- Evaluating the finite bracket coefficient family recovers the actual bracket. -/
theorem homogeneousBracketCoefficients_sum
    {m n : ℕ} (x : freeLieExact X m) (y : freeLieExact X n) :
    (homogeneousBracketCoefficients X x y).sum
        (fun i c ↦ c •
          (((freeLieExactBasis X (m + n) i : freeLieExact X (m + n))) : F)) =
      ⁅(x : F), (y : F)⁆ := by
  change ((freeLieExactBasis X (m + n)).repr
      ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩).sum
        (fun i c ↦ c •
          ((freeLieExactBasis X (m + n) i : freeLieExact X (m + n)) : F)) = _
  have h := (freeLieExactBasis X (m + n)).linearCombination_repr
    ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩
  change ((freeLieExactBasis X (m + n)).repr
      ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩).sum
        (fun i c ↦ c • (freeLieExactBasis X (m + n) i)) =
      ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩ at h
  let c := (freeLieExactBasis X (m + n)).repr
    ⟨⁅(x : F), (y : F)⁆, freeLieExact_bracket_mem X x y⟩
  calc
    c.sum (fun i z ↦ z •
        (((freeLieExactBasis X (m + n) i : freeLieExact X (m + n))) : F)) =
        (freeLieExact X (m + n)).subtype
          (c.sum (fun i z ↦ z • freeLieExactBasis X (m + n) i)) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro i hi
      rw [map_zsmul]
      rfl
    _ = ⁅(x : F), (y : F)⁆ := congrArg Subtype.val h

/-- Evaluating the common-index bracket family recovers the actual bracket. -/
theorem lowHomogeneousBracketCoefficients_sum
    (x y : LowHomogeneousBasisIndex X)
    (hxy : lowHomogeneousBasisWeight X x + lowHomogeneousBasisWeight X y ≤ 4) :
    (lowHomogeneousBracketCoefficients X x y hxy).sum
        (fun i c ↦ c • lowHomogeneousBasisValue X i) =
      ⁅lowHomogeneousBasisValue X x, lowHomogeneousBasisValue X y⁆ := by
  unfold lowHomogeneousBracketCoefficients
  rw [Finsupp.sum_mapDomain_index]
  · simpa only [lowHomogeneousBasisValue_indexOf] using
      homogeneousBracketCoefficients_sum X
        (⟨lowHomogeneousBasisValue X x,
          lowHomogeneousBasisValue_mem_exact X x⟩ :
            freeLieExact X (lowHomogeneousBasisWeight X x))
        (⟨lowHomogeneousBasisValue X y,
          lowHomogeneousBasisValue_mem_exact X y⟩ :
            freeLieExact X (lowHomogeneousBasisWeight X y))
  · intro i
    simp
  · intro i a b
    simp [add_smul]

end

end DegreeFive

end LieRings
