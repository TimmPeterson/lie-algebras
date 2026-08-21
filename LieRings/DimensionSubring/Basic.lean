import LieRings.UniversalEnveloping.Adjoint
import Mathlib.Algebra.Lie.Nilpotent

/-!
# Lie dimension subrings

For a Lie algebra `L` over a commutative ring `R`, we define

`dimensionSubring R L n = ι⁻¹(augmentationIdeal R L ^ n)`.

This is the usual dimension subring `δₙ(L)`.  No injectivity of `ι` is built into the definition.
-/

namespace LieRings

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/--
The `n`th Lie dimension subring `δₙ(L) = ι⁻¹(𝜔(L)^n)`, as a Lie ideal of `L`.
-/
def dimensionSubring (n : ℕ) : LieIdeal R L :=
  LieIdeal.comap (UniversalEnvelopingAlgebra.ι R)
    (twoSidedIdealLieIdeal R (UEA R L) (UEA.augmentationIdeal R L ^ n))

/-- The usual lower central series, with term `0` equal to `L` (thus term `n` is `γₙ₊₁`). -/
abbrev lowerCentralSeries (n : ℕ) : LieIdeal R L :=
  LieModule.lowerCentralSeries R L L n

/-- The intersection `δ_ω(L)` of all finite dimension subrings. -/
def dimensionSubringOmega : LieIdeal R L :=
  ⨅ n : ℕ, dimensionSubring R L n

/-- The intersection `γ_ω(L)` of all finite lower-central terms. -/
def lowerCentralSeriesOmega : LieIdeal R L :=
  ⨅ n : ℕ, lowerCentralSeries R L n

@[simp]
theorem mem_dimensionSubring {n : ℕ} {x : L} :
    x ∈ dimensionSubring R L n ↔
      UniversalEnvelopingAlgebra.ι R x ∈ UEA.augmentationIdeal R L ^ n :=
  Iff.rfl

@[simp]
theorem mem_dimensionSubringOmega {x : L} :
    x ∈ dimensionSubringOmega R L ↔ ∀ n : ℕ, x ∈ dimensionSubring R L n := by
  simp [dimensionSubringOmega]

@[simp]
theorem mem_lowerCentralSeriesOmega {x : L} :
    x ∈ lowerCentralSeriesOmega R L ↔ ∀ n : ℕ, x ∈ lowerCentralSeries R L n := by
  simp [lowerCentralSeriesOmega]

@[simp]
theorem dimensionSubring_zero : dimensionSubring R L 0 = ⊤ := by
  apply top_unique
  intro x _
  rw [mem_dimensionSubring, Submodule.pow_zero]
  rw [Ideal.one_eq_top]
  trivial

@[simp]
theorem dimensionSubring_one : dimensionSubring R L 1 = ⊤ := by
  apply top_unique
  intro x _
  rw [mem_dimensionSubring, Submodule.pow_one]
  exact UEA.ι_mem_augmentationIdeal R L x

/-- The dimension filtration is decreasing. -/
theorem dimensionSubring_antitone : Antitone (dimensionSubring R L) := by
  intro m n hmn x hx
  rw [mem_dimensionSubring] at hx ⊢
  exact UEA.augmentationIdeal R L |>.pow_le_pow_right hmn hx

/-- `δₙ₊₁(L) ⊆ δₙ(L)`. -/
theorem dimensionSubring_succ_le (n : ℕ) :
    dimensionSubring R L (n + 1) ≤ dimensionSubring R L n :=
  dimensionSubring_antitone R L (Nat.le_add_right n 1)

end LieRings
