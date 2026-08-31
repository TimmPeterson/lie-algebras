import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Noncommutative Rees rings and modules

This file defines the Rees ring of a two-sided ideal `I` of a possibly
noncommutative ring `U`, and the Rees module of a left `U`-module `V`:

* `ReesRing I = ⊕ n, I^n`;
* `ReesModule I = ⊕ n, I^n V`.

The indeterminate customarily denoted by `t` is represented by the direct-sum
degree.  We also prove the elementary fact used in the Rees separation
argument: if `V` is finite over `U`, then its Rees module is finite over the
Rees ring.  No commutativity hypothesis is imposed on `U`.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

variable {U : Type u} [Ring U]

/-- The degree-`n` piece `I^n` of a noncommutative Rees ring, regarded as a
`Z`-submodule of the underlying additive group. -/
def reesPiece (I : Ideal U) (n : ℕ) : Submodule ℤ U :=
  (I ^ n).restrictScalars ℤ

instance reesPieceGradedMonoid (I : Ideal U) [I.IsTwoSided] :
    SetLike.GradedMonoid (reesPiece I) where
  one_mem := by
    change (1 : U) ∈ I ^ 0
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    trivial
  mul_mem := by
    intro i j x y hx hy
    change (x : U) * y ∈ I ^ (i + j)
    rw [Ideal.IsTwoSided.pow_add]
    exact Submodule.mul_mem_mul hx hy

/-- The noncommutative Rees ring `⊕ n, I^n t^n`. -/
abbrev ReesRing (I : Ideal U) [I.IsTwoSided] : Type u :=
  DirectSum ℕ (fun n ↦ ↑(reesPiece I n))

variable {V : Type v} [AddCommGroup V] [Module U V]

/-- The degree-`n` piece `I^n V` of the Rees module of `V`. -/
def reesModulePiece (I : Ideal U) (n : ℕ) : Submodule ℤ V :=
  (I ^ n • (⊤ : Submodule U V)).restrictScalars ℤ

theorem smul_mem_reesModulePiece (I : Ideal U) {n : ℕ}
    {a : U} (ha : a ∈ I ^ n) (v : V) :
    a • v ∈ reesModulePiece (V := V) I n := by
  change a • v ∈ I ^ n • (⊤ : Submodule U V)
  exact Submodule.smul_mem_smul (R := U) ha (by trivial)

instance reesPieceGradedSMul (I : Ideal U) [I.IsTwoSided] :
    SetLike.GradedSMul (reesPiece I) (reesModulePiece (V := V) I) where
  smul_mem := by
    intro i j a v ha hv
    change (a : U) • (v : V) ∈ I ^ (i + j) • (⊤ : Submodule U V)
    rw [Ideal.IsTwoSided.pow_add, Submodule.mul_smul]
    exact Submodule.smul_mem_smul ha hv

/-- The Rees module `⊕ n, I^n V t^n`. -/
abbrev ReesModule (I : Ideal U) [I.IsTwoSided] : Type v :=
  DirectSum ℕ (fun n ↦ ↑(reesModulePiece (V := V) I n))

/-- Place a vector in degree zero of its Rees module. -/
def reesDegreeZero (I : Ideal U) [I.IsTwoSided] (v : V) :
    ReesModule (V := V) I :=
  DirectSum.of (fun n ↦ ↑(reesModulePiece (V := V) I n)) 0
    ⟨v, by
      change v ∈ I ^ 0 • (⊤ : Submodule U V)
      rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      trivial⟩

private theorem rees_of_smul_mem_span_degreeZero
    (I : Ideal U) [I.IsTwoSided] (s : Set V) {n : ℕ} {w : V}
    (hw : w ∈ Submodule.span U s) (a : U) (ha : a ∈ I ^ n) :
    DirectSum.of (fun k ↦ ↑(reesModulePiece (V := V) I k)) n
        ⟨a • w, smul_mem_reesModulePiece I ha w⟩ ∈
      Submodule.span (ReesRing I) (reesDegreeZero I '' s) := by
  induction hw using Submodule.span_induction generalizing a with
  | mem w hw =>
      let ar : reesPiece I n := ⟨a, ha⟩
      have hw0 : reesDegreeZero I w ∈
          Submodule.span (ReesRing I) (reesDegreeZero I '' s) :=
        Submodule.subset_span ⟨w, hw, rfl⟩
      have hsmul :=
        (Submodule.span (ReesRing I) (reesDegreeZero I '' s)).smul_mem
          (DirectSum.of (fun k ↦ ↑(reesPiece I k)) n ar) hw0
      rw [reesDegreeZero, DirectSum.Gmodule.of_smul_of] at hsmul
      exact hsmul
  | zero =>
      have hz :
          (⟨a • (0 : V), smul_mem_reesModulePiece I ha (0 : V)⟩ :
              reesModulePiece (V := V) I n) = 0 := by
        ext
        simp
      rw [hz]
      simpa using
        (Submodule.span (ReesRing I) (reesDegreeZero I '' s)).zero_mem
  | add x y hx hy ihx ihy =>
      have hadd :
          (⟨a • (x + y), smul_mem_reesModulePiece I ha (x + y)⟩ :
              reesModulePiece (V := V) I n) =
            ⟨a • x, smul_mem_reesModulePiece I ha x⟩ +
              ⟨a • y, smul_mem_reesModulePiece I ha y⟩ := by
        ext
        exact smul_add a x y
      rw [hadd, map_add]
      exact (Submodule.span (ReesRing I) (reesDegreeZero I '' s)).add_mem
        (ihx a ha) (ihy a ha)
  | smul u w hw ih =>
      have hau : a * u ∈ I ^ n := Ideal.mul_mem_right u (I ^ n) ha
      simpa [mul_smul] using ih (a * u) hau

/-- If `V` is finitely generated over `U`, then its Rees module is finitely
generated over the Rees ring, by the same generators placed in degree zero. -/
theorem reesModule_finite (I : Ideal U) [I.IsTwoSided]
    [Module.Finite U V] : Module.Finite (ReesRing I) (ReesModule (V := V) I) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := U) (M := V)
  refine Module.Finite.of_fg_top ?_
  rw [Submodule.fg_def]
  refine ⟨↑(s.image (reesDegreeZero I)),
    (s.image (reesDegreeZero I)).finite_toSet, ?_⟩
  apply le_antisymm le_top
  intro x hx
  clear hx
  induction x using DirectSum.induction_on with
  | zero => exact (Submodule.span _ _).zero_mem
  | add x y hx hy => exact (Submodule.span _ _).add_mem hx hy
  | of n v =>
      let S : Submodule (ReesRing I) (ReesModule (V := V) I) :=
        Submodule.span (ReesRing I) (reesDegreeZero I '' (s : Set V))
      let Q : Submodule U V := {
        carrier := {z | ∃ hz : z ∈ I ^ n • (⊤ : Submodule U V),
          DirectSum.of (fun k ↦ ↑(reesModulePiece (V := V) I k)) n
            ⟨z, hz⟩ ∈ S}
        zero_mem' := by
          let hz : (0 : V) ∈ I ^ n • (⊤ : Submodule U V) :=
            (I ^ n • (⊤ : Submodule U V)).zero_mem
          refine ⟨hz, ?_⟩
          have hz0 : (⟨0, hz⟩ : reesModulePiece (V := V) I n) = 0 := by
            ext
            rfl
          rw [hz0]
          simpa only [map_zero] using S.zero_mem
        add_mem' := by
          rintro x y ⟨hx, hxS⟩ ⟨hy, hyS⟩
          refine ⟨Submodule.add_mem _ hx hy, ?_⟩
          have hsum := S.add_mem hxS hyS
          have hadd :
              (⟨x + y, Submodule.add_mem _ hx hy⟩ :
                  reesModulePiece (V := V) I n) = ⟨x, hx⟩ + ⟨y, hy⟩ := by
            ext
            rfl
          rw [hadd, map_add]
          exact hsum
        smul_mem' := by
          rintro u z ⟨hz, hzS⟩
          have huz : u • z ∈ I ^ n • (⊤ : Submodule U V) :=
            (I ^ n • (⊤ : Submodule U V)).smul_mem u hz
          refine ⟨huz, ?_⟩
          let ur : reesPiece I 0 := ⟨u, by
            change u ∈ I ^ 0
            rw [Submodule.pow_zero, Ideal.one_eq_top]
            trivial⟩
          have hsmul := S.smul_mem
            (DirectSum.of (fun k ↦ ↑(reesPiece I k)) 0 ur) hzS
          rw [DirectSum.Gmodule.of_smul_of] at hsmul
          have hsigma :
              GradedMonoid.mk (A := fun k ↦
                  ↑(reesModulePiece (V := V) I k)) (0 +ᵥ n)
                  (GradedMonoid.GSMul.smul
                    (A := fun k ↦ ↑(reesPiece I k))
                    (M := fun k ↦ ↑(reesModulePiece (V := V) I k))
                    ur (⟨z, hz⟩ : reesModulePiece (V := V) I n)) =
                GradedMonoid.mk (A := fun k ↦
                  ↑(reesModulePiece (V := V) I k)) n
                  (⟨u • z, huz⟩ : reesModulePiece (V := V) I n) := by
            apply Sigma.subtype_ext (zero_vadd ℕ n)
            rfl
          have hof := DirectSum.of_eq_of_gradedMonoid_eq hsigma
          rw [hof] at hsmul
          exact hsmul }
      have hle : I ^ n • (⊤ : Submodule U V) ≤ Q := by
        rw [Submodule.smul_le]
        intro a ha w hw
        refine ⟨Submodule.smul_mem_smul ha hw, ?_⟩
        have hwspan : w ∈ Submodule.span U (s : Set V) := by
          rw [hs]
          trivial
        simpa only [S, Finset.coe_image] using
          rees_of_smul_mem_span_degreeZero I (s : Set V) hwspan a ha
      simpa only [S, Finset.coe_image] using (hle v.property).choose_spec

end

end LieRings.Plotkin
