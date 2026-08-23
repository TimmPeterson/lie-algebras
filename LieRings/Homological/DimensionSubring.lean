import LieRings.Homological.SecondHomology
import LieRings.DimensionSubring.Centrality
import LieRings.DimensionSubring.DegreeTwo
import Mathlib.Tactic

/-!
# Dimension factors as cokernels on second integral homology

For `n ≥ 2`, the extension

`0 → δₙ(L)/γₙ(L) → L/γₙ(L) → L/δₙ(L) → 0`

is central and stem.  Applying the Hopf-formula central-stem theorem identifies its kernel with
the cokernel of the induced map on the concrete second integral homology objects.

Mathlib numbers the lower central series from zero, so conventional `γₙ(L)` is represented by
`lowerCentralSeries ℤ L n.pred`.
-/

namespace LieRings

namespace Homological

universe u

noncomputable section

open FreePresentation

variable (L : Type u) [LieRing L]

/-- Conventional `γₙ(L)`, using Mathlib's zero-based lower-central-series indexing. -/
abbrev conventionalLowerCentralSeries (n : ℕ) : LieIdeal ℤ L :=
  lowerCentralSeries ℤ L n.pred

/-- The standard inclusion `γₙ(L) ≤ δₙ(L)` at a positive conventional index. -/
theorem conventionalLowerCentralSeries_le_dimensionSubring
    {n : ℕ} (hn : 1 ≤ n) :
    conventionalLowerCentralSeries L n ≤ dimensionSubring ℤ L n := by
  have hindex : n.pred + 1 = n := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred (by omega : n ≠ 0)
  change lowerCentralSeries ℤ L n.pred ≤ dimensionSubring ℤ L n
  rw [← hindex]
  exact lowerCentralSeries_le_dimensionSubring ℤ L n.pred

/-- The canonical quotient homomorphism `L/γₙ(L) → L/δₙ(L)`. -/
def dimensionExtensionMap (n : ℕ) (hn : 1 ≤ n) :
    LieHom ℤ (L ⧸ conventionalLowerCentralSeries L n)
      (L ⧸ dimensionSubring ℤ L n) :=
  quotientMap (dimensionSubring ℤ L n) (conventionalLowerCentralSeries L n)
    (conventionalLowerCentralSeries_le_dimensionSubring L hn)

/-- The dimension factor `δₙ(L)/γₙ(L)` as a quotient of the ideal `δₙ(L)`. -/
abbrev DimensionFactor (n : ℕ) :=
  IdealQuotient (dimensionSubring ℤ L n) (conventionalLowerCentralSeries L n)

/--
For every Lie ring and every `n ≥ 2`, the dimension factor `δₙ(L)/γₙ(L)` is naturally
isomorphic, as an Abelian group (equivalently a `ℤ`-module), to

`Coker (H₂(L/γₙ(L); ℤ) → H₂(L/δₙ(L); ℤ))`.
-/
def dimensionFactorEquivSecondHomologyCokernel
    {n : ℕ} (hn : 2 ≤ n) :
    LinearCokernel (secondHomologyMap
      (dimensionExtensionMap L n (by omega))) ≃ₗ[ℤ]
      DimensionFactor L n := by
  let I := dimensionSubring ℤ L n
  let J := conventionalLowerCentralSeries L n
  have hnpos : 1 ≤ n := by omega
  have hJI : J ≤ I := conventionalLowerCentralSeries_le_dimensionSubring L hnpos
  have hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J := by
    calc
      ⁅(⊤ : LieIdeal ℤ L), I⁆ = ⁅I, (⊤ : LieIdeal ℤ L)⁆ :=
        LieSubmodule.lie_comm _ _
      _ = lowerCentralSeries ℤ L n := by
        exact dimensionSubring_bracket_eq_lowerCentralSeries_of_pos ℤ L hnpos
      _ ≤ lowerCentralSeries ℤ L n.pred :=
        LieModule.antitone_lowerCentralSeries ℤ L L (Nat.pred_le n)
      _ = J := rfl
  have hstem : I ≤
      ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆ ⊔ J := by
    have hderived : I ≤
        ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆ := by
      calc
        I ≤ dimensionSubring ℤ L 2 := dimensionSubring_antitone ℤ L hn
        _ = lowerCentralSeries ℤ L 1 :=
          dimensionSubring_two_eq_lowerCentralSeries_one ℤ L
        _ = ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆ := by
          change LieModule.lowerCentralSeries ℤ L L (0 + 1) = _
          rw [LieModule.lowerCentralSeries_succ]
          simp
    exact hderived.trans le_sup_left
  change LinearCokernel (secondHomologyMap (quotientMap I J hJI)) ≃ₗ[ℤ]
    IdealQuotient I J
  exact centralStemCokernelEquiv hJI hcentral hstem

end

end Homological

end LieRings
