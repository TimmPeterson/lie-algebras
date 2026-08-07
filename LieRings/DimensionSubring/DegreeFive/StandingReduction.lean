import LieRings.DimensionSubring.DegreeFive.AdaptedPresentation
import Mathlib.GroupTheory.PGroup

/-!
# The standing class-three reduction

This is a literal Lean package for condition `(R)` in the coordinate proof: `L` is finite,
its additive group is a `2`-group, `γ₄(L)=0`, and `γ₃(L)` is cyclic of order a power of two.
The generator of `γ₃` is obtained as the inverse image of `1` under `gammaThreeEquiv`; it is
therefore not an additional choice or assumption.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

/-- Exactly the hypotheses denoted `(R)` by the standing reduction. -/
structure StandingReductionData (L : Type u) [LieRing L] where
  finite_inst : Finite L
  two_group : IsPGroup 2 (Multiplicative L)
  classThree : lowerCentralSeries ℤ L 3 = ⊥
  gammaThreeExponent : ℕ
  gammaThreeEquiv :
    lowerCentralSeries ℤ L 2 ≃+ ZMod (2 ^ gammaThreeExponent)

namespace StandingReductionData

variable {L : Type u} [LieRing L] (R : StandingReductionData L)

/-- The modulus `q=2^κ` of the cyclic third lower-central term. -/
def q : ℕ := 2 ^ R.gammaThreeExponent

@[simp]
theorem q_eq : R.q = 2 ^ R.gammaThreeExponent := rfl

theorem q_pos : 0 < R.q := by simp [q]

/-- The distinguished generator `z̄` of `γ₃(L)`. -/
def gammaThreeGenerator : lowerCentralSeries ℤ L 2 :=
  R.gammaThreeEquiv.symm 1

@[simp]
theorem gammaThreeEquiv_generator :
    R.gammaThreeEquiv R.gammaThreeGenerator = 1 := by
  simp [gammaThreeGenerator]

/-- The additive cardinality of `L` is a power of two. -/
theorem exists_card_eq_two_pow (R : StandingReductionData L) :
    ∃ ν : ℕ, Nat.card L = 2 ^ ν := by
  letI : Finite L := R.finite_inst
  obtain ⟨ν, hν⟩ := R.two_group.exists_card_eq
  exact ⟨ν, hν⟩

universe v

variable {X : Type v} [Finite X]

/-- Every diagonal entry in every adapted homogeneous layer is a power of two. -/
theorem adaptedDiagonal_eq_two_pow
    (R : StandingReductionData L) :
    letI : Finite L := R.finite_inst
    ∀ (evaluation : LieHom ℤ (FreeLieAlgebra ℤ X) L) (n : ℕ)
      (i : FreeLieExactBasisIndex X n),
      ∃ a : ℕ, adaptedDiagonal X L evaluation n i = 2 ^ a := by
  letI : Finite L := R.finite_inst
  intro evaluation n i
  obtain ⟨ν, hν⟩ := R.exists_card_eq_two_pow
  have hdiv := adaptedDiagonal_dvd_card X L evaluation n i
  rw [hν] at hdiv
  exact (Nat.dvd_prime_pow Nat.prime_two).mp hdiv |>.imp fun a ha ↦ ha.2

/-- Diagonal entries are pairwise comparable by divisibility. -/
theorem adaptedDiagonal_dvd_or_dvd
    (R : StandingReductionData L) :
    letI : Finite L := R.finite_inst
    ∀ (evaluation : LieHom ℤ (FreeLieAlgebra ℤ X) L) (n : ℕ)
      (i j : FreeLieExactBasisIndex X n),
      adaptedDiagonal X L evaluation n i ∣ adaptedDiagonal X L evaluation n j ∨
        adaptedDiagonal X L evaluation n j ∣ adaptedDiagonal X L evaluation n i := by
  letI : Finite L := R.finite_inst
  intro evaluation n i j
  obtain ⟨a, ha⟩ := R.adaptedDiagonal_eq_two_pow evaluation n i
  obtain ⟨b, hb⟩ := R.adaptedDiagonal_eq_two_pow evaluation n j
  rw [ha, hb]
  rcases le_total a b with hab | hba
  · exact Or.inl (pow_dvd_pow 2 hab)
  · exact Or.inr (pow_dvd_pow 2 hba)

/-- In the shared collected order, earlier Smith entries divide later Smith entries.  This is
the exact divisibility convention used in the definition of `Data.Identities`; it is derived
from `(R)`, not stored in an adapted-presentation record. -/
theorem collectedDiagonal_dvd_of_le
    (R : StandingReductionData L) :
    letI : Finite L := R.finite_inst
    ∀ (evaluation : LieHom ℤ (FreeLieAlgebra ℤ X) L) (n : ℕ)
      {i j : FreeLieExactBasisIndex X n}, i ≤ j →
      collectedDiagonal X L evaluation n i ∣
        collectedDiagonal X L evaluation n j := by
  letI : Finite L := R.finite_inst
  intro evaluation n i j hij
  let σ := adaptedDiagonalSort X L evaluation n
  rcases R.adaptedDiagonal_dvd_or_dvd evaluation n (σ i) (σ j) with h | h
  · exact h
  · have hji : collectedDiagonal X L evaluation n j ≤
        collectedDiagonal X L evaluation n i :=
      Nat.le_of_dvd (collectedDiagonal_pos X L evaluation n i) h
    have hij' := collectedDiagonal_mono X L evaluation n hij
    have heq : collectedDiagonal X L evaluation n i =
        collectedDiagonal X L evaluation n j := Nat.le_antisymm hij' hji
    exact heq ▸ dvd_refl _

/-- The relations-through-weight-four statement for the canonical free presentation.  All
bases and all row representatives in this equality are constructed, not supplied as fields. -/
theorem canonical_relation_eq_four_adapted_rowParts
    (R : StandingReductionData L) :
    letI : Finite L := R.finite_inst
    ∀ r : LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap,
      (r : CanonicalFreeLie L) =
        iteratedCollectedRelationRowPart L L (canonicalFreeLieEvaluation L) 0 r +
        iteratedCollectedRelationRowPart L L (canonicalFreeLieEvaluation L) 1 r +
        iteratedCollectedRelationRowPart L L (canonicalFreeLieEvaluation L) 2 r +
        iteratedCollectedRelationRowPart L L (canonicalFreeLieEvaluation L) 3 r +
        (iteratedCollectedRelationRemainder L L
          (canonicalFreeLieEvaluation L) 4 r : CanonicalFreeLie L) := by
  letI : Finite L := R.finite_inst
  intro r
  exact relation_eq_four_collected_rowParts_add_weightFiveRemainder
    L L (canonicalFreeLieEvaluation L) r

end StandingReductionData

end

end DegreeFive

end LieRings
