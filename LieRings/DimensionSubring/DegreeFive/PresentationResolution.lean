import LieRings.DimensionSubring.DegreeFive.FreePresentation
import LieRings.DimensionSubring.DegreeFive.Exterior

/-!
# The explicit class-two presentation resolution

Given a linear map from a free generator module to a Lie ring `L`, this file constructs the
induced map `P ⊕ ⋀²P → L/γ₃(L)`.  Its kernel is the two-term resolution used by the invariant
degree-five proof.
-/

namespace LieRings

open scoped TensorProduct

universe u v

namespace DegreeFive

noncomputable section

variable (P : Type u) [AddCommGroup P]
variable (L : Type v) [LieRing L]

/-- The quotient by `γ₃` is nilpotent of class at most two. -/
theorem modGammaThree_lowerCentralSeries_two_eq_bot :
    lowerCentralSeries ℤ (ModGammaThree L) 2 = ⊥ := by
  let q : L →ₗ⁅ℤ⁆ ModGammaThree L :=
    UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L 2)
  have hq : Function.Surjective q := by
    intro y
    exact Submodule.Quotient.mk_surjective
      (lowerCentralSeries ℤ L 2).toSubmodule y
  change LieModule.lowerCentralSeries ℤ (ModGammaThree L)
      (ModGammaThree L) 2 = ⊥
  rw [← LieIdeal.lowerCentralSeries_map_eq 2 hq]
  rw [LieIdeal.map_eq_bot_iff]
  intro x hx
  change (LieSubmodule.Quotient.mk x : ModGammaThree L) = 0
  exact (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ L 2)).mpr hx

/-- Bracket evaluation on two generators, valued in `L/γ₃(L)`. -/
def generatorBracketAlternating (f : P →ₗ[ℤ] L) :
    P [⋀^Fin 2]→ₗ[ℤ] ModGammaThree L where
  toFun v := LieSubmodule.Quotient.mk ⁅f (v 0), f (v 1)⁆
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i n x := by
    fin_cases i <;> simp <;> rfl
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change (LieSubmodule.Quotient.mk ⁅f (v 0), f (v 1)⁆ :
          ModGammaThree L) = 0
      change v 0 = v 1 at hv
      rw [hv, lie_self]
      change (0 : ModGammaThree L) = 0
      rfl
    · change (LieSubmodule.Quotient.mk ⁅f (v 0), f (v 1)⁆ :
          ModGammaThree L) = 0
      change v 1 = v 0 at hv
      rw [hv, lie_self]
      change (0 : ModGammaThree L) = 0
      rfl
    · exact (hij rfl).elim

/-- Evaluation of the degree-two component. -/
def degreeTwoEvaluation (f : P →ₗ[ℤ] L) :
    ⋀[ℤ]^2 P →ₗ[ℤ] ModGammaThree L :=
  exteriorPower.alternatingMapLinearEquiv (generatorBracketAlternating P L f)

@[simp]
theorem degreeTwoEvaluation_wedge (f : P →ₗ[ℤ] L) (x y : P) :
    degreeTwoEvaluation P L f (wedgeTwo P x y) =
      (LieSubmodule.Quotient.mk ⁅f x, f y⁆ : ModGammaThree L) := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (generatorBracketAlternating P L f) ![x, y]

/-- Every degree-two value lies in the commutator ideal of `L/γ₃(L)`. -/
theorem degreeTwoEvaluation_mem_lowerCentralSeries_one
    (f : P →ₗ[ℤ] L) (a : ⋀[ℤ]^2 P) :
    degreeTwoEvaluation P L f a ∈
      lowerCentralSeries ℤ (ModGammaThree L) 1 := by
  let Q := ModGammaThree L
  let N : Submodule ℤ (⋀[ℤ]^2 P) :=
    (lowerCentralSeries ℤ Q 1).toSubmodule.comap (degreeTwoEvaluation P L f)
  have hwedge : ∀ v : Fin 2 → P, exteriorPower.ιMulti ℤ 2 v ∈ N := by
    intro v
    change degreeTwoEvaluation P L f (exteriorPower.ιMulti ℤ 2 v) ∈
      lowerCentralSeries ℤ Q 1
    rw [show exteriorPower.ιMulti ℤ 2 v = wedgeTwo P (v 0) (v 1) by rfl,
      degreeTwoEvaluation_wedge]
    change ⁅(LieSubmodule.Quotient.mk (f (v 0)) : Q),
      LieSubmodule.Quotient.mk (f (v 1))⁆ ∈ lowerCentralSeries ℤ Q 1
    change _ ∈ LieModule.lowerCentralSeries ℤ Q Q 1
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _)
      (LieSubmodule.mem_top _)
  have hspan : Submodule.span ℤ
      (Set.range (exteriorPower.ιMulti ℤ 2 : (Fin 2 → P) → ⋀[ℤ]^2 P)) ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hwedge v
  have htop : Submodule.span ℤ
      (Set.range (exteriorPower.ιMulti ℤ 2 : (Fin 2 → P) → ⋀[ℤ]^2 P)) = ⊤ :=
    exteriorPower.ιMulti_span ℤ 2 P
  apply hspan
  rw [htop]
  exact Submodule.mem_top

/-- Degree-two values are central in `L/γ₃(L)`. -/
theorem lie_degreeTwoEvaluation_eq_zero
    (f : P →ₗ[ℤ] L) (x : ModGammaThree L) (a : ⋀[ℤ]^2 P) :
    ⁅x, degreeTwoEvaluation P L f a⁆ = 0 := by
  have hmem : ⁅x, degreeTwoEvaluation P L f a⁆ ∈
      lowerCentralSeries ℤ (ModGammaThree L) 2 := by
    change _ ∈ LieModule.lowerCentralSeries ℤ (ModGammaThree L)
      (ModGammaThree L) 2
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x)
      (degreeTwoEvaluation_mem_lowerCentralSeries_one P L f a)
  rw [modGammaThree_lowerCentralSeries_two_eq_bot L] at hmem
  simpa using hmem

/-- The map `P ⊕ ⋀²P → L/γ₃(L)` induced by a linear generator map. -/
def freeClassTwoEvaluation (f : P →ₗ[ℤ] L) :
    FreeClassTwo P →ₗ⁅ℤ⁆ ModGammaThree L where
  toLinearMap :=
    { toFun := fun x ↦
        (LieSubmodule.Quotient.mk (f x.1) : ModGammaThree L) +
          degreeTwoEvaluation P L f x.2
      map_add' := by
        intro x y
        let q : L →ₗ[ℤ] ModGammaThree L :=
          (lowerCentralSeries ℤ L 2).toSubmodule.mkQ
        change q (f (x.1 + y.1)) + degreeTwoEvaluation P L f (x.2 + y.2) =
          (q (f x.1) + degreeTwoEvaluation P L f x.2) +
            (q (f y.1) + degreeTwoEvaluation P L f y.2)
        rw [map_add, map_add, map_add]
        abel
      map_smul' := by
        intro n x
        let q : L →ₗ[ℤ] ModGammaThree L :=
          (lowerCentralSeries ℤ L 2).toSubmodule.mkQ
        change q (f (n • x.1)) + degreeTwoEvaluation P L f (n • x.2) =
          n • (q (f x.1) + degreeTwoEvaluation P L f x.2)
        rw [map_smul, map_smul, map_smul, smul_add] }
  map_lie' := by
    intro x y
    change (LieSubmodule.Quotient.mk (f 0) : ModGammaThree L) +
        degreeTwoEvaluation P L f (wedgeTwo P x.1 y.1) =
      ⁅(LieSubmodule.Quotient.mk (f x.1) : ModGammaThree L) +
          degreeTwoEvaluation P L f x.2,
        (LieSubmodule.Quotient.mk (f y.1) : ModGammaThree L) +
          degreeTwoEvaluation P L f y.2⁆
    rw [show f 0 = 0 by exact map_zero f]
    change (0 : ModGammaThree L) +
        degreeTwoEvaluation P L f (wedgeTwo P x.1 y.1) = _
    rw [zero_add, degreeTwoEvaluation_wedge]
    rw [add_lie, lie_add, lie_add]
    rw [lie_degreeTwoEvaluation_eq_zero P L f,
      lie_degreeTwoEvaluation_eq_zero P L f]
    have hleft : ⁅degreeTwoEvaluation P L f x.2,
        (LieSubmodule.Quotient.mk (f y.1) : ModGammaThree L)⁆ = 0 := by
      calc
        _ = -⁅(LieSubmodule.Quotient.mk (f y.1) : ModGammaThree L),
            degreeTwoEvaluation P L f x.2⁆ := (lie_skew _ _).symm
        _ = 0 := by rw [lie_degreeTwoEvaluation_eq_zero P L f, neg_zero]
    rw [hleft, zero_add, add_zero, add_zero]
    rfl

@[simp]
theorem freeClassTwoEvaluation_apply (f : P →ₗ[ℤ] L) (x : FreeClassTwo P) :
    freeClassTwoEvaluation P L f x =
      (LieSubmodule.Quotient.mk (f x.1) : ModGammaThree L) +
        degreeTwoEvaluation P L f x.2 :=
  rfl

end

end DegreeFive

end LieRings
