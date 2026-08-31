import LieRings.Plotkin.Rees
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Separation by powers of an ideal

This file formalizes the Rees-module proof of the following elementary
noncommutative separation statement.  If the Rees ring of a two-sided ideal
`I` is left Noetherian, `V` is a finite left module, and `I` kills a submodule
`B`, then `B ∩ I^r V = 0` for some `r`.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

variable {U : Type u} [Ring U]
variable {V : Type v} [AddCommGroup V] [Module U V]

/-- The graded Rees submodule whose degree-`n` component is `B ∩ I^n V`. -/
def reesIntersectionSubmodule (I : Ideal U) [I.IsTwoSided]
    (B : Submodule U V) : Submodule (ReesRing I) (ReesModule (V := V) I) where
  carrier := {x | ∀ n, ((x n : reesModulePiece (V := V) I n) : V) ∈ B}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro x y hx hy n
    simpa using B.add_mem (hx n) (hy n)
  smul_mem' := by
    classical
    intro a x hx
    induction a using DirectSum.induction_on with
    | zero => intro n; simp
    | add a b ha hb =>
        intro n
        simpa [add_smul] using B.add_mem (ha n) (hb n)
    | of i a =>
        rw [← DirectSum.sum_support_of x, Finset.smul_sum]
        intro n
        let ev : ReesModule (V := V) I →+ V :=
          (reesModulePiece (V := V) I n).subtype.toAddMonoidHom.comp
            (DFinsupp.evalAddMonoidHom n)
        change ev (∑ j ∈ x.support,
          DirectSum.of (fun k ↦ ↑(reesPiece I k)) i a •
            DirectSum.of (fun k ↦ ↑(reesModulePiece (V := V) I k)) j (x j)) ∈ B
        rw [map_sum]
        apply B.sum_mem
        intro j hj
        rw [DirectSum.Gmodule.of_smul_of]
        change (((DirectSum.of (fun k ↦
            ↑(reesModulePiece (V := V) I k)) (i + j)
              (GradedMonoid.GSMul.smul
                (A := fun k ↦ ↑(reesPiece I k))
                (M := fun k ↦ ↑(reesModulePiece (V := V) I k))
                a (x j))) n : reesModulePiece (V := V) I n) : V) ∈ B
        by_cases h : i + j = n
        · subst n
          have hwB : ((x j : reesModulePiece (V := V) I j) : V) ∈ B := hx j
          simpa [DirectSum.of_apply] using B.smul_mem (a : U) hwB
        · simp [DirectSum.of_apply, h]

private theorem positiveHomogeneous_smul_eq_zero
    (I : Ideal U) [I.IsTwoSided] (B : Submodule U V)
    (hIB : I • B = ⊥) {i : ℕ} (hi : 0 < i) (a : reesPiece I i)
    {x : ReesModule (V := V) I} (hx : x ∈ reesIntersectionSubmodule I B) :
    DirectSum.of (fun k ↦ ↑(reesPiece I k)) i a • x = 0 := by
  classical
  rw [← DirectSum.sum_support_of x, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hwB : ((x j : reesModulePiece (V := V) I j) : V) ∈ B := hx j
  have haI : (a : U) ∈ I :=
    (Ideal.pow_le_self (Nat.ne_of_gt hi)) a.property
  have haw : (a : U) • ((x j : reesModulePiece (V := V) I j) : V) ∈ I • B :=
    Submodule.smul_mem_smul haI hwB
  rw [hIB] at haw
  have haw0 : (a : U) • ((x j : reesModulePiece (V := V) I j) : V) = 0 := haw
  rw [DirectSum.Gmodule.of_smul_of]
  have hz : GradedMonoid.GSMul.smul
      (A := fun k ↦ ↑(reesPiece I k))
      (M := fun k ↦ ↑(reesModulePiece (V := V) I k)) a (x j) = 0 := by
    ext
    exact haw0
  rw [hz]
  simp

private theorem degreeZeroHomogeneous_smul_apply_eq_zero
    (I : Ideal U) [I.IsTwoSided] (a : reesPiece I 0)
    {x : ReesModule (V := V) I} {n : ℕ} (hx : x n = 0) :
    (DirectSum.of (fun k ↦ ↑(reesPiece I k)) 0 a • x) n = 0 := by
  classical
  rw [← DirectSum.sum_support_of x, Finset.smul_sum]
  let ev : ReesModule (V := V) I →+ reesModulePiece (V := V) I n :=
    DFinsupp.evalAddMonoidHom n
  change ev (∑ j ∈ x.support,
    DirectSum.of (fun k ↦ ↑(reesPiece I k)) 0 a •
      DirectSum.of (fun k ↦ ↑(reesModulePiece (V := V) I k)) j (x j)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [DirectSum.Gmodule.of_smul_of]
  change (DirectSum.of (fun k ↦ ↑(reesModulePiece (V := V) I k))
    (0 +ᵥ j) (GradedMonoid.GSMul.smul
      (A := fun k ↦ ↑(reesPiece I k))
      (M := fun k ↦ ↑(reesModulePiece (V := V) I k)) a (x j))) n = 0
  by_cases h : j = n
  · subst j
    rw [hx]
    rw [DirectSum.GdistribMulAction.smul_zero]
    simp
  · simp [DirectSum.of_apply, h]

private theorem rees_smul_apply_eq_zero
    (I : Ideal U) [I.IsTwoSided] (B : Submodule U V)
    (hIB : I • B = ⊥) (a : ReesRing I)
    {x : ReesModule (V := V) I} (hxB : x ∈ reesIntersectionSubmodule I B)
    {n : ℕ} (hx : x n = 0) : (a • x) n = 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb =>
      rw [add_smul]
      change (a • x) n + (b • x) n = 0
      rw [ha, hb, add_zero]
  | of i a =>
      cases i with
      | zero => exact degreeZeroHomogeneous_smul_apply_eq_zero I a hx
      | succ i =>
          have hzero := positiveHomogeneous_smul_eq_zero I B hIB
            (Nat.succ_pos i) a hxB
          rw [hzero]
          rfl

/-- **Rees separation.**  If `I B = 0`, the Rees ring of `I` is left
Noetherian, and `V` is finite over `U`, then `B ∩ I^r V = 0` for some `r`.

The proof is the finite-support version of the manuscript's homogeneous
generator argument.  A finite generating set of the graded intersection
submodule has a common degree bound.  Positive-degree Rees coefficients kill
that submodule, while degree-zero coefficients do not change support. -/
theorem exists_pow_smul_inf_eq_bot_of_rees_noetherian
    (I : Ideal U) [I.IsTwoSided] [IsNoetherianRing (ReesRing I)]
    [Module.Finite U V] (B : Submodule U V) (hIB : I • B = ⊥) :
    ∃ r : ℕ, B ⊓ (I ^ r • (⊤ : Submodule U V)) = ⊥ := by
  classical
  letI : Module.Finite (ReesRing I) (ReesModule (V := V) I) :=
    reesModule_finite I
  letI : IsNoetherian (ReesRing I) (ReesModule (V := V) I) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  let N := reesIntersectionSubmodule (V := V) I B
  have hNfg : N.FG := IsNoetherian.noetherian N
  rw [Submodule.fg_def] at hNfg
  obtain ⟨s, hsfin, hs⟩ := hNfg
  let sf : Finset (ReesModule (V := V) I) := hsfin.toFinset
  let supportUnion : Finset ℕ := sf.biUnion fun g ↦ g.support
  let D : ℕ := supportUnion.sup id
  let r : ℕ := D + 1
  have hgenerator (g : ReesModule (V := V) I) (hg : g ∈ s) : g r = 0 := by
    by_contra hgr
    have hgrsupp : r ∈ g.support := DFinsupp.mem_support_iff.mpr hgr
    have hgsf : g ∈ sf := by
      exact (Set.Finite.mem_toFinset hsfin).mpr hg
    have hrsupport : r ∈ supportUnion := by
      exact Finset.mem_biUnion.mpr ⟨g, hgsf, hgrsupp⟩
    have hrle : r ≤ D := by
      exact Finset.le_sup (f := id) hrsupport
    omega
  have hcoordinate (x : ReesModule (V := V) I)
      (hxspan : x ∈ Submodule.span (ReesRing I) s) : x r = 0 := by
    induction hxspan using Submodule.span_induction with
    | mem x hx => exact hgenerator x hx
    | zero => rfl
    | add x y hx hy ihx ihy =>
        change x r + y r = 0
        rw [ihx, ihy, add_zero]
    | smul a x hx ih =>
        apply rees_smul_apply_eq_zero I B hIB a
        · change x ∈ N
          rw [← hs]
          exact hx
        · exact ih
  refine ⟨r, le_antisymm ?_ bot_le⟩
  intro z hz
  change z = 0
  rcases hz with ⟨hzB, hzI⟩
  let zr : reesModulePiece (V := V) I r := ⟨z, hzI⟩
  let x : ReesModule (V := V) I :=
    DirectSum.of (fun k ↦ ↑(reesModulePiece (V := V) I k)) r zr
  have hxN : x ∈ N := by
    intro n
    by_cases h : r = n
    · subst n
      simpa [x, zr, DirectSum.of_apply] using hzB
    · simp [x, DirectSum.of_apply, h]
  have hxspan : x ∈ Submodule.span (ReesRing I) s := by
    rw [hs]
    exact hxN
  have hxr := hcoordinate x hxspan
  have hzr : zr = 0 := by
    simpa [x, DirectSum.of_apply] using hxr
  exact congrArg Subtype.val hzr

end

end LieRings.Plotkin
