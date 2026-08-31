import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneous
import LieRings.Basic
import LieRings.UniversalEnveloping.Quotient
import Mathlib.GroupTheory.Finiteness

/-!
# Finite generation for the Plotkin theorem

The public finite-generation predicate is `LieRings.IsFinitelyGenerated`, defined by a finite set
whose Lie span is the whole ring.  For the Plotkin proof it is convenient to use the equivalent
free-presentation formulation recorded here.

The main result is the additive-finiteness lemma from the manuscript: a finitely generated
nilpotent Lie ring is finitely generated as an abelian group.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

/-- The free-presentation formulation of finite generation used internally by the Plotkin proof. -/
def HasFiniteFreePresentation (L : Type u) [LieRing L] : Prop :=
  ∃ r : ℕ, ∃ generators : Fin r → L,
    Function.Surjective (FreeLieAlgebra.lift ℤ generators)

namespace HasFiniteFreePresentation

variable {L : Type u} [LieRing L]
variable {K : Type v} [LieRing K]

/-- A surjective image of a Lie ring with a finite free presentation again has one. -/
theorem map (hL : HasFiniteFreePresentation L) (f : L →ₗ⁅ℤ⁆ K)
    (hf : Function.Surjective f) : HasFiniteFreePresentation K := by
  obtain ⟨r, generators, hevaluation⟩ := hL
  refine ⟨r, fun i ↦ f (generators i), ?_⟩
  have hcomp : FreeLieAlgebra.lift ℤ (fun i ↦ f (generators i)) =
      f.comp (FreeLieAlgebra.lift ℤ generators) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp only [LieHom.comp_apply, FreeLieAlgebra.lift_of_apply]
  rw [hcomp]
  exact hf.comp hevaluation

/-- A quotient of a Lie ring with a finite free presentation again has one. -/
theorem quotient (hL : HasFiniteFreePresentation L) (I : LieIdeal ℤ L) :
    HasFiniteFreePresentation (L ⧸ I) :=
  hL.map (UEA.lieIdealQuotientMk ℤ L I)
    (LieSubmodule.Quotient.surjective_mk' I)

end HasFiniteFreePresentation

/-- Finite generation by `lieSpan` is equivalent to being a quotient of a free Lie ring on a
finite set. -/
theorem isFinitelyGenerated_iff_hasFiniteFreePresentation
    (L : Type u) [LieRing L] :
    LieRings.IsFinitelyGenerated L ↔ HasFiniteFreePresentation L := by
  classical
  constructor
  · rintro ⟨generators, hspan⟩
    let e : Fin (Fintype.card generators) ≃ generators :=
      (Fintype.equivFin generators).symm
    let g : Fin (Fintype.card generators) → L := fun i ↦ e i
    let evaluation : FreeLieAlgebra ℤ (Fin (Fintype.card generators)) →ₗ⁅ℤ⁆ L :=
      FreeLieAlgebra.lift ℤ g
    refine ⟨Fintype.card generators, g, ?_⟩
    rw [← LieHom.range_eq_top]
    apply top_unique
    rw [← hspan]
    apply LieSubalgebra.lieSpan_le.mpr
    intro x hx
    have hx' : x ∈ generators := hx
    let i : Fin (Fintype.card generators) := e.symm ⟨x, hx'⟩
    have hi : g i = x := by
      change ((e (e.symm ⟨x, hx'⟩) : generators) : L) = x
      simp
    rw [← hi]
    exact (LieHom.mem_range (FreeLieAlgebra.lift ℤ g) (g i)).mpr
      ⟨FreeLieAlgebra.of ℤ i, by simp⟩
  · rintro ⟨r, generators, hevaluation⟩
    let s : Finset L := Finset.univ.image generators
    refine ⟨s, ?_⟩
    apply top_unique
    intro x _hx
    obtain ⟨y, rfl⟩ := hevaluation x
    let N : LieSubalgebra ℤ L :=
      LieSubalgebra.lieSpan ℤ L (s : Set L)
    have hgenerator (i : Fin r) : generators i ∈ N := by
      exact LieSubalgebra.subset_lieSpan
        (Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨i, Finset.mem_univ i, rfl⟩))
    let generatorsN : Fin r → N := fun i ↦ ⟨generators i, hgenerator i⟩
    let evaluationN : FreeLieAlgebra ℤ (Fin r) →ₗ⁅ℤ⁆ N :=
      FreeLieAlgebra.lift ℤ generatorsN
    have hcomp : LieHom.comp N.incl evaluationN =
        FreeLieAlgebra.lift ℤ generators := by
      apply FreeLieAlgebra.hom_ext
      intro i
      change
        (((FreeLieAlgebra.lift ℤ generatorsN) (FreeLieAlgebra.of ℤ i) : N) : L) =
          (FreeLieAlgebra.lift ℤ generators) (FreeLieAlgebra.of ℤ i)
      simp [generatorsN]
    change FreeLieAlgebra.lift ℤ generators y ∈ N
    rw [← hcomp]
    exact (evaluationN y).property

variable {L : Type u} [LieRing L]
variable {K : Type v} [LieRing K]

/-- A surjective image of a finitely generated Lie ring is finitely generated. -/
theorem _root_.LieRings.IsFinitelyGenerated.map
    (hL : LieRings.IsFinitelyGenerated L) (f : L →ₗ⁅ℤ⁆ K)
    (hf : Function.Surjective f) : LieRings.IsFinitelyGenerated K := by
  rw [isFinitelyGenerated_iff_hasFiniteFreePresentation] at hL ⊢
  exact hL.map f hf

/-- A quotient of a finitely generated Lie ring by a Lie ideal is finitely generated. -/
theorem _root_.LieRings.IsFinitelyGenerated.quotient
    (hL : LieRings.IsFinitelyGenerated L) (I : LieIdeal ℤ L) :
    LieRings.IsFinitelyGenerated (L ⧸ I) := by
  rw [isFinitelyGenerated_iff_hasFiniteFreePresentation] at hL ⊢
  exact hL.quotient I

namespace AdditiveFinite

open LieRings.DegreeFive

variable (X : Type u) [Finite X]

local notation "N" => FreeNonUnitalNonAssocAlgebra ℤ X
local notation "F" => FreeLieAlgebra ℤ X

/-- Bracketed words of length strictly below `n` form a finite integral module when the alphabet
is finite. -/
theorem magmaLow_fg (n : ℕ) : (FreeLieDimension.magmaLow X n).FG := by
  rw [FreeLieDimension.magmaLow, Finsupp.supported_eq_span_single]
  apply Submodule.fg_span
  exact (finite_freeMagma_length_lt X n).image _

instance magmaLow_moduleFinite (n : ℕ) :
    Module.Finite ℤ (FreeLieDimension.magmaLow X n) := by
  rw [Module.Finite.iff_fg]
  exact magmaLow_fg X n

/-- Evaluate the bounded-length bracketed words in a target Lie ring. -/
def lowEvaluation (K : Type v) [LieRing K]
    (evaluation : F →ₗ⁅ℤ⁆ K) (c : ℕ) :
    FreeLieDimension.magmaLow X (c + 1) →ₗ[ℤ] K :=
  evaluation.toLinearMap.comp
    ((FreeLieDimension.freeLieMkLinear X).comp
      (FreeLieDimension.magmaLow X (c + 1)).subtype)

/-- If the target has lower-central term `c` equal to zero, bounded-length bracketed words already
surject onto it. -/
theorem lowEvaluation_surjective (K : Type v) [LieRing K]
    (evaluation : F →ₗ⁅ℤ⁆ K) (hevaluation : Function.Surjective evaluation)
    (c : ℕ) (hclass : lowerCentralSeries ℤ K c = ⊥) :
    Function.Surjective (lowEvaluation X K evaluation c) := by
  intro y
  obtain ⟨f, rfl⟩ := hevaluation y
  let p : N := freeLieRepresentative X f
  let lo : N := FreeLieDimension.magmaLowPart X (c + 1) p
  let hi : N := FreeLieDimension.magmaHighPart X (c + 1) p
  have hlo : lo ∈ FreeLieDimension.magmaLow X (c + 1) :=
    FreeLieDimension.magmaLowPart_mem X (c + 1) p
  have hhi : hi ∈ FreeLieDimension.magmaHigh X (c + 1) :=
    FreeLieDimension.magmaHighPart_mem X (c + 1) p
  have hp : FreeLieDimension.freeLieMkLinear X p = f :=
    freeLieMkLinear_freeLieRepresentative X f
  have hsum : lo + hi = p :=
    FreeLieDimension.magmaLowPart_add_magmaHighPart X (c + 1) p
  have hhiLcs : FreeLieDimension.freeLieMkLinear X hi ∈
      lowerCentralSeries ℤ F c := by
    change FreeLieDimension.freeLieMkLinear X hi ∈
      (lowerCentralSeries ℤ F c : Submodule ℤ F)
    rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries X c]
    exact ⟨hi, hhi, rfl⟩
  have hevalHi : evaluation (FreeLieDimension.freeLieMkLinear X hi) = 0 := by
    have hmem : evaluation (FreeLieDimension.freeLieMkLinear X hi) ∈
        lowerCentralSeries ℤ K c :=
      (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := evaluation) c)
        (LieIdeal.mem_map hhiLcs)
    rw [hclass] at hmem
    simpa using hmem
  refine ⟨⟨lo, hlo⟩, ?_⟩
  change evaluation (FreeLieDimension.freeLieMkLinear X lo) = evaluation f
  rw [← hp, ← hsum, map_add, map_add, hevalHi, add_zero]

end AdditiveFinite

/-- **Additive finite generation.** A finitely generated nilpotent Lie ring is finitely generated
as an abelian group. -/
theorem moduleFinite_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
    (K : Type u) [LieRing K] (hK : IsFinitelyGenerated K)
    (c : ℕ) (hclass : lowerCentralSeries ℤ K c = ⊥) :
    Module.Finite ℤ K := by
  obtain ⟨r, generators, hevaluation⟩ :=
    (isFinitelyGenerated_iff_hasFiniteFreePresentation K).mp hK
  exact Module.Finite.of_surjective
    (AdditiveFinite.lowEvaluation (Fin r) K
      (FreeLieAlgebra.lift ℤ generators) c)
    (AdditiveFinite.lowEvaluation_surjective (Fin r) K
      (FreeLieAlgebra.lift ℤ generators) hevaluation c hclass)

/-- Additive-group form of the preceding theorem. -/
theorem addGroupFG_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
    (K : Type u) [LieRing K] (hK : IsFinitelyGenerated K)
    (c : ℕ) (hclass : lowerCentralSeries ℤ K c = ⊥) :
    AddGroup.FG K := by
  exact Module.Finite.iff_addGroup_fg.mp
    (moduleFinite_of_finitelyGenerated_of_lowerCentralSeries_eq_bot K hK c hclass)

end

end LieRings.Plotkin
