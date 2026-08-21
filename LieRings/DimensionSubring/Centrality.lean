import LieRings.DimensionSubring.Basic

/-!
# Centrality of Lie dimension subrings

Mathlib numbers the lower central series from zero:

* `LieModule.lowerCentralSeries R L L 0 = L = γ₁(L)`;
* `LieModule.lowerCentralSeries R L L n = γₙ₊₁(L)`.

Accordingly, the main theorem below says
`[δₙ₊₁(L), L] = lowerCentralSeries (n + 1) = γₙ₊₂(L)`.

All results hold over an arbitrary commutative base ring.  They do not use PBW and do not assume
that the canonical map into the universal enveloping algebra is injective.
-/

namespace LieRings

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/--
Relative dimension centrality: `[A, δₙ(L)]` lies in the `n`-fold relative commutator
`[A, L, ..., L]`.
-/
theorem bracket_dimensionSubring_le_lcs (A : LieIdeal R L) (n : ℕ) :
    ⁅A, dimensionSubring R L n⁆ ≤ LieSubmodule.lcs n A := by
  rw [LieSubmodule.lie_le_iff]
  intro a ha x hx
  have h := UEA.augmentationIdeal_pow_action_mem R L L A n
    ((mem_dimensionSubring R L).mp hx) ha
  rw [UEA.representation_ι_apply] at h
  rw [← lie_skew]
  exact (LieSubmodule.lcs n A).neg_mem h

/-- The standard inclusion `γₙ₊₁(L) ⊆ δₙ₊₁(L)`. -/
theorem lowerCentralSeries_le_dimensionSubring (n : ℕ) :
    lowerCentralSeries R L n ≤ dimensionSubring R L (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      change LieModule.lowerCentralSeries R L L (n + 1) ≤
        dimensionSubring R L (n + 1 + 1)
      rw [LieModule.lowerCentralSeries_succ]
      rw [LieSubmodule.lie_le_iff]
      intro x _ y hy
      rw [mem_dimensionSubring]
      have hx : UniversalEnvelopingAlgebra.ι R x ∈ UEA.augmentationIdeal R L :=
        UEA.ι_mem_augmentationIdeal R L x
      have hy' : UniversalEnvelopingAlgebra.ι R y ∈
          UEA.augmentationIdeal R L ^ (n + 1) :=
        (mem_dimensionSubring R L).mp (ih hy)
      have hxy : UniversalEnvelopingAlgebra.ι R x *
          UniversalEnvelopingAlgebra.ι R y ∈
          UEA.augmentationIdeal R L ^ (n + 1 + 1) := by
        rw [add_comm (n + 1) 1, Ideal.IsTwoSided.pow_add, Submodule.pow_one]
        exact Ideal.mul_mem_mul hx hy'
      have hyx : UniversalEnvelopingAlgebra.ι R y *
          UniversalEnvelopingAlgebra.ι R x ∈
          UEA.augmentationIdeal R L ^ (n + 1 + 1) := by
        rw [Ideal.IsTwoSided.pow_add, Submodule.pow_one]
        exact Ideal.mul_mem_mul hy' hx
      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      exact (UEA.augmentationIdeal R L ^ (n + 1 + 1)).sub_mem hxy hyx

/-- The lower-central intersection is always contained in the dimension-subring intersection. -/
theorem lowerCentralSeriesOmega_le_dimensionSubringOmega :
    lowerCentralSeriesOmega R L ≤ dimensionSubringOmega R L := by
  intro x hx
  rw [mem_dimensionSubringOmega]
  intro n
  cases n with
  | zero => simp
  | succ n =>
      exact lowerCentralSeries_le_dimensionSubring R L n
        ((mem_lowerCentralSeriesOmega R L).mp hx n)

/--
Dimension centrality, in a hypothesis-free positive-index form:
`[δₙ₊₁(L), L] = γₙ₊₂(L)`.
-/
theorem dimensionSubring_bracket_eq_lowerCentralSeries (n : ℕ) :
    ⁅dimensionSubring R L (n + 1), (⊤ : LieIdeal R L)⁆ =
      lowerCentralSeries R L (n + 1) := by
  rw [LieSubmodule.lie_comm]
  apply le_antisymm
  · simpa [lowerCentralSeries, LieModule.lowerCentralSeries] using
      bracket_dimensionSubring_le_lcs R L (⊤ : LieIdeal R L) (n + 1)
  · change LieModule.lowerCentralSeries R L L (n + 1) ≤
      ⁅(⊤ : LieIdeal R L), dimensionSubring R L (n + 1)⁆
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.mono_lie_right (⊤ : LieIdeal R L)
      (lowerCentralSeries_le_dimensionSubring R L n)

/-- The same theorem with the conventional hypothesis `1 ≤ n`: `[δₙ(L),L] = γₙ₊₁(L)`. -/
theorem dimensionSubring_bracket_eq_lowerCentralSeries_of_pos
    {n : ℕ} (hn : 1 ≤ n) :
    ⁅dimensionSubring R L n, (⊤ : LieIdeal R L)⁆ = lowerCentralSeries R L n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [add_comm] using dimensionSubring_bracket_eq_lowerCentralSeries R L k

/-- A dimension element is central modulo the preceding lower-central term. -/
theorem dimensionSubring_bracket_le_previousLowerCentralSeries (n : ℕ) :
    ⁅dimensionSubring R L (n + 1), (⊤ : LieIdeal R L)⁆ ≤
      lowerCentralSeries R L n := by
  rw [dimensionSubring_bracket_eq_lowerCentralSeries]
  exact LieModule.antitone_lowerCentralSeries R L L (Nat.le_succ n)

/--
The entire relative lower-central tail after `δₙ₊₁` agrees with the classical tail.
-/
theorem dimensionSubring_lcs_eq_lowerCentralSeries (n r : ℕ) :
    LieSubmodule.lcs (r + 1) (dimensionSubring R L (n + 1)) =
      lowerCentralSeries R L (n + r + 1) := by
  induction r with
  | zero =>
      simpa [lowerCentralSeries, LieModule.lowerCentralSeries, LieSubmodule.lie_comm] using
        dimensionSubring_bracket_eq_lowerCentralSeries R L n
  | succ r ih =>
      rw [LieSubmodule.lcs_succ, ih]
      change ⁅(⊤ : LieIdeal R L), LieModule.lowerCentralSeries R L L (n + r + 1)⁆ =
        LieModule.lowerCentralSeries R L L (n + (r + 1) + 1)
      rw [← LieModule.lowerCentralSeries_succ]
      congr 2

/-- Strong centrality: `[δₘ₊₁(L), δₙ₊₁(L)] ⊆ γₘ₊ₙ₊₂(L)`. -/
theorem bracket_dimensionSubring_le_lowerCentralSeries (m n : ℕ) :
    ⁅dimensionSubring R L (m + 1), dimensionSubring R L (n + 1)⁆ ≤
      lowerCentralSeries R L (m + n + 1) := by
  rw [← dimensionSubring_lcs_eq_lowerCentralSeries R L m n]
  exact bracket_dimensionSubring_le_lcs R L (dimensionSubring R L (m + 1)) (n + 1)

/-- The conventional positive-index form of strong centrality:
`[δₘ(L), δₙ(L)] ⊆ γₘ₊ₙ(L)`. -/
theorem bracket_dimensionSubring_le_lowerCentralSeries_of_pos
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ⁅dimensionSubring R L m, dimensionSubring R L n⁆ ≤
      lowerCentralSeries R L (m + n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [add_assoc, add_left_comm, add_comm] using
    bracket_dimensionSubring_le_lowerCentralSeries R L m n

end LieRings
