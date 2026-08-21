import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Positive full-rank Smith presentations
-/

namespace LieRings

namespace DegreeFive

noncomputable section

variable {M ι : Type*} [AddCommGroup M] [Module ℤ M]
variable [Fintype ι]

/-- The unit `1` or `-1` which changes an integer into its absolute value. -/
def smithSignUnit (a : ℤ) : ℤˣ := if 0 ≤ a then 1 else -1

@[simp]
theorem coe_smithSignUnit_mul (a : ℤ) : (↑(smithSignUnit a) : ℤ) * a = a.natAbs := by
  by_cases hz : a = 0
  · simp [hz, smithSignUnit]
  · rw [← Int.sign_mul_self_eq_natAbs]
    by_cases ha : 0 ≤ a
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
      simp [smithSignUnit, ha, Int.sign_eq_one_of_pos ha']
    · have ha' : a < 0 := lt_of_not_ge ha
      simp [smithSignUnit, ha, Int.sign_eq_neg_one_of_neg ha']

/-- A square Smith presentation whose diagonal has been normalized to positive naturals. -/
structure PositiveSmithPresentation (N : Submodule ℤ M) where
  ambientBasis : Module.Basis ι ℤ M
  relationBasis : Module.Basis ι ℤ N
  diagonal : ι → ℕ
  diagonal_pos : ∀ i, 0 < diagonal i
  relation_eq : ∀ i, (relationBasis i : M) =
    (diagonal i : ℤ) • ambientBasis i

namespace PositiveSmithPresentation

/-- A finite quotient produces a positive square Smith presentation. -/
def ofFiniteQuotient (b : Module.Basis ι ℤ M) (N : Submodule ℤ M)
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (hfinite : Finite (M ⧸ N)) : PositiveSmithPresentation (ι := ι) N := by
  have hmodule : (inferInstance : Module ℤ M) = AddCommGroup.toIntModule M :=
    Subsingleton.elim _ _
  cases hmodule
  letI : Finite (M ⧸ N) := hfinite
  let hrank : Module.finrank ℤ N = Module.finrank ℤ M :=
    (Submodule.finiteQuotient_iff N).mp inferInstance
  let bM := Submodule.smithNormalFormTopBasis b hrank
  let bN := Submodule.smithNormalFormBotBasis b hrank
  let a := Submodule.smithNormalFormCoeffs b hrank
  have ha : ∀ i, a i ≠ 0 :=
    Submodule.smithNormalFormCoeffs_ne_zero b hrank
  let units : ι → ℤˣ := fun i ↦ smithSignUnit (a i)
  let bNpos : Module.Basis ι ℤ N := bN.unitsSMul units
  refine
    { ambientBasis := bM
      relationBasis := bNpos
      diagonal := fun i ↦ (a i).natAbs
      diagonal_pos := fun i ↦ Int.natAbs_pos.mpr (ha i)
      relation_eq := ?_ }
  intro i
  change ((bN.unitsSMul units i : N) : M) =
    ((a i).natAbs : ℤ) • bM i
  rw [Module.Basis.unitsSMul_apply]
  change (units i : ℤ) • (bN i : M) = ((a i).natAbs : ℤ) • bM i
  rw [Submodule.smithNormalFormBotBasis_def b hrank]
  rw [smul_smul]
  change ((units i : ℤ) * a i) • bM i = ((a i).natAbs : ℤ) • bM i
  rw [show (units i : ℤ) = (smithSignUnit (a i) : ℤ) by rfl,
    coe_smithSignUnit_mul]

end PositiveSmithPresentation

end


end DegreeFive

end LieRings
