import LieRings.Plotkin.FiniteTail
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Util.AssertNoSorry

/-!
# A central prime-order ideal in a nonzero dimension intersection

This file implements the first paragraph of the manuscript's zero-intersection argument.  The
last nonzero term of the lower-central series of `δ_ω(K)`, regarded as a `K`-module, is central.
The finite-tail theorem makes it finite, and Cauchy's theorem supplies a cyclic subgroup of prime
order.  Since its generator is central, that cyclic subgroup is itself a Lie ideal.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

variable {K : Type u} [LieRing K]

/-- The cyclic Lie ideal generated additively by a central element. -/
def centralCyclicIdeal (a : K) (ha : a ∈ LieAlgebra.center ℤ K) : LieIdeal ℤ K :=
  { Submodule.span ℤ ({a} : Set K) with
    lie_mem := by
      intro x y hy
      change y ∈ ℤ ∙ a at hy
      change ⁅x, y⁆ ∈ ℤ ∙ a
      rw [Submodule.mem_span_singleton] at hy ⊢
      obtain ⟨z, rfl⟩ := hy
      refine ⟨0, ?_⟩
      simp [ha x] }

@[simp]
theorem mem_centralCyclicIdeal {a : K} {ha : a ∈ LieAlgebra.center ℤ K} {x : K} :
    x ∈ centralCyclicIdeal a ha ↔ ∃ z : ℤ, z • a = x := by
  exact Submodule.mem_span_singleton

theorem centralCyclicIdeal_le_center (a : K) (ha : a ∈ LieAlgebra.center ℤ K) :
    centralCyclicIdeal a ha ≤ LieAlgebra.center ℤ K := by
  intro x hx y
  obtain ⟨z, rfl⟩ := (mem_centralCyclicIdeal.mp hx)
  simp [ha y]

theorem centralCyclicIdeal_le {a : K} (ha : a ∈ LieAlgebra.center ℤ K)
    {I : LieIdeal ℤ K} (hmem : a ∈ I) :
    centralCyclicIdeal a ha ≤ I := by
  intro x hx
  obtain ⟨z, rfl⟩ := (mem_centralCyclicIdeal.mp hx)
  exact I.smul_mem z hmem

/-- The cardinality of the central cyclic ideal is the additive order of its generator. -/
theorem natCard_centralCyclicIdeal (a : K) (ha : a ∈ LieAlgebra.center ℤ K) :
    Nat.card (centralCyclicIdeal a ha) = addOrderOf a := by
  change Nat.card (Submodule.span ℤ ({a} : Set K)) = addOrderOf a
  have hspan : (Submodule.span ℤ ({a} : Set K)).toAddSubgroup =
      AddSubgroup.zmultiples a := by
    ext x
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton]
    exact AddSubgroup.mem_zmultiples_iff.symm
  change Nat.card (Submodule.span ℤ ({a} : Set K)).toAddSubgroup = addOrderOf a
  rw [hspan, Nat.card_zmultiples]

private theorem lcs_mono {M : Type u} [AddCommGroup M] [Module ℤ M]
    [LieRingModule K M] {P Q : LieSubmodule ℤ K M} (hPQ : P ≤ Q) (n : ℕ) :
    P.lcs n ≤ Q.lcs n := by
  induction n with
  | zero => exact hPQ
  | succ n ih =>
      rw [LieSubmodule.lcs_succ, LieSubmodule.lcs_succ]
      exact LieSubmodule.mono_lie_right (⊤ : LieIdeal ℤ K) ih

/-- If the ambient Lie ring is nilpotent, every one of its Lie submodules is nilpotent as a
module for the ambient action. -/
theorem lcs_eq_bot_of_lowerCentralSeries_eq_bot
    (N : LieSubmodule ℤ K K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥) :
    N.lcs c = ⊥ := by
  apply le_bot_iff.mp
  exact (lcs_mono (show N ≤ (⊤ : LieSubmodule ℤ K K) from le_top) c).trans_eq hclass

/-- **Central prime-order ideal.**  A nonzero `δ_ω(K)` in a finitely generated nilpotent Lie
ring contains a central Lie ideal of prime cardinality.

The nilpotence convention is zero-based: `lowerCentralSeries ℤ K c = ⊥` says that the
conventional term `γ_(c+1)` vanishes. -/
theorem exists_central_prime_ideal_le_dimensionSubringOmega
    (hK : IsFinitelyGenerated K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥)
    (homega : dimensionSubringOmega ℤ K ≠ ⊥) :
    ∃ (p : ℕ) (A : LieIdeal ℤ K),
      p.Prime ∧ (Nat.card A = p) ∧
      A ≤ LieAlgebra.center ℤ K ∧ A ≤ dimensionSubringOmega ℤ K := by
  let Ω : LieIdeal ℤ K := dimensionSubringOmega ℤ K
  letI : Nontrivial Ω :=
    (LieSubmodule.nontrivial_iff_ne_bot ℤ K K).mpr homega
  letI : LieRingModule K Ω := Ω.instLieRingModuleSubtypeMem
  letI : LieModule.IsNilpotent K Ω := by
    apply (LieModule.isNilpotent_iff ℤ K Ω).mpr
    refine ⟨c, ?_⟩
    exact (Ω.lowerCentralSeries_eq_bot_iff_lcs_eq_bot c).mpr
      (lcs_eq_bot_of_lowerCentralSeries_eq_bot Ω c hclass)

  letI : Finite (dimensionSubring ℤ K (c + 1)) :=
    finite_dimensionSubring_succ_of_finitelyGenerated_of_lowerCentralSeries_eq_bot hK c hclass
  let omegaToTail : Ω → dimensionSubring ℤ K (c + 1) := fun x ↦
    ⟨x.1, (mem_dimensionSubringOmega ℤ K).mp x.2 (c + 1)⟩
  have homegaToTail : Function.Injective omegaToTail := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : dimensionSubring ℤ K (c + 1) ↦ (z : K)) hxy
  letI : Finite Ω := Finite.of_injective omegaToTail homegaToTail

  let C : LieSubmodule ℤ K Ω := LieModule.lowerCentralSeriesLast ℤ K Ω
  letI : Nontrivial C := LieModule.nontrivial_lowerCentralSeriesLast ℤ K Ω
  letI : Finite C := Finite.of_injective C.subtype C.injective_subtype

  have hcard_ne_one : Nat.card C ≠ 1 := by
    intro hcard
    exact not_subsingleton C (Nat.card_eq_one_iff_unique.mp hcard).1
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, haorder⟩ := exists_prime_addOrderOf_dvd_card' p hpdiv

  let a₀ : K := ((a : C) : Ω)
  have ha₀order : addOrderOf a₀ = p := by
    let incl : C →+ K :=
      Ω.subtype.toAddMonoidHom.comp C.subtype.toAddMonoidHom
    have hincl : Function.Injective incl := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext hxy)
    exact (addOrderOf_injective incl hincl a).trans haorder
  have ha₀central : a₀ ∈ LieAlgebra.center ℤ K := by
    intro x
    have haMax : (a : C).1 ∈ LieModule.maxTrivSubmodule ℤ K Ω :=
      LieModule.lowerCentralSeriesLast_le_max_triv ℤ K Ω a.2
    exact congrArg Subtype.val ((LieModule.mem_maxTrivSubmodule ℤ K Ω (a : C).1).mp haMax x)
  have ha₀omega : a₀ ∈ dimensionSubringOmega ℤ K := (a : C).1.2

  let A : LieIdeal ℤ K := centralCyclicIdeal a₀ ha₀central
  refine ⟨p, A, hp, ?_, centralCyclicIdeal_le_center a₀ ha₀central, ?_⟩
  · exact (natCard_centralCyclicIdeal a₀ ha₀central).trans ha₀order
  · exact centralCyclicIdeal_le ha₀central ha₀omega

end

end LieRings.Plotkin

assert_no_sorry LieRings.Plotkin.exists_central_prime_ideal_le_dimensionSubringOmega
