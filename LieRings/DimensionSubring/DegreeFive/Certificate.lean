import LieRings.DimensionSubring.DegreeFive.Exterior

/-!
# Invariant certificates for a fifth dimension witness

The PBW collection in the class-three proof produces an alternating tensor with two parts.
The low part evaluates the original Lie element.  The remaining (mixed and high) part has zero
bracket evaluation, and the total tensor vanishes in `⋀²(L/γ₃)`.  These four pieces of finite
data form the certificate below.  Its sufficiency is completely invariant and does not use
derived functors.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

/-- The finite algebraic output required from the PBW collection of a degree-five witness.

`low` is the weight-`(1,1)` alternating tensor. `other` combines the mixed weight-`(1,2)` and
high weight-`(2,2)` parts.  The PBW ledger proves directly that the latter has zero bracket
evaluation; it need not come from `⋀² γ₂(L)`. -/
structure InvariantCertificate
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) (a : L) where
  low : ⋀[ℤ]^2 (ModGammaThree L)
  other : ⋀[ℤ]^2 (ModGammaThree L)
  total_zero : low + other = 0
  other_evaluates_zero : exteriorBracket L hclass other = 0
  evaluates : a = -(exteriorBracket L hclass low)

/-- **Certificate criterion.** Every invariant certificate in nilpotency class three evaluates
to zero. -/
theorem InvariantCertificate.value_eq_zero
    {hclass : lowerCentralSeries ℤ L 3 = ⊥} {a : L}
    (c : InvariantCertificate L hclass a) : a = 0 := by
  have hlow : exteriorBracket L hclass c.low = 0 := by
    have htotal := congrArg (exteriorBracket L hclass) c.total_zero
    rw [map_add, map_zero, c.other_evaluates_zero, add_zero] at htotal
    exact htotal
  rw [c.evaluates, hlow, neg_zero]

/-- If every element of `δ₅(L)` admits the PBW certificate, then `δ₅(L)=0` in class three. -/
theorem dimensionSubring_five_eq_bot_of_certificates
    (hclass : lowerCentralSeries ℤ L 3 = ⊥)
    (hexists : ∀ a : L, a ∈ dimensionSubring ℤ L 5 →
      Nonempty (InvariantCertificate L hclass a)) :
    dimensionSubring ℤ L 5 = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  exact (hexists a ha).some.value_eq_zero

/-- The global degree-five inclusion follows as soon as the canonical class-three quotient
admits the invariant certificate for each of its fifth-dimension elements.  This packages the
quotient reduction and the certificate criterion into the exact final interface needed by the
PBW extraction. -/
theorem dimensionSubring_five_le_lowerCentralSeries_three_of_quotient_certificates
    (hexists : ∀ a : ClassThreeQuotient L,
      a ∈ dimensionSubring ℤ (ClassThreeQuotient L) 5 →
        Nonempty (InvariantCertificate (ClassThreeQuotient L)
          (classThreeQuotient_lowerCentralSeries_three_eq_bot L) a)) :
    dimensionSubring ℤ L 5 ≤ lowerCentralSeries ℤ L 3 := by
  apply dimensionSubring_five_le_lowerCentralSeries_three_of_quotient L
  exact dimensionSubring_five_eq_bot_of_certificates (ClassThreeQuotient L)
    (classThreeQuotient_lowerCentralSeries_three_eq_bot L) hexists

end

end DegreeFive

end LieRings
