import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Positive full-rank Smith presentations

This file isolates the linear-algebra step used by an adapted presentation.  A finite quotient
of a finite free integral module has full-rank kernel.  Smith normal form therefore gives bases
of the ambient module and of the kernel indexed by the same finite type.  We normalize each
kernel basis vector by a sign, so every diagonal coefficient is a strictly positive natural
number.
-/

namespace LieRings

namespace DegreeFive

noncomputable section

variable {M ι : Type*} [AddCommGroup M] [Module ℤ M]
variable [Fintype ι]

/-- The unit `1` or `-1` which changes an integer into its absolute value. -/
def smithSignUnit (a : ℤ) : ℤˣ := if 0 ≤ a then 1 else -1

@[simp]
theorem coe_smithSignUnit_mul (a : ℤ) : (smithSignUnit a : ℤ) * a = a.natAbs := by
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

/-- Any scalar multiple of one adapted ambient basis vector which lies in the relation
submodule is divisible by that row's diagonal coefficient. -/
theorem diagonal_dvd_of_smul_mem {N : Submodule ℤ M}
    (P : PositiveSmithPresentation (ι := ι) N)
    (i : ι) (c : ℤ) (hmem : c • P.ambientBasis i ∈ N) :
    (P.diagonal i : ℤ) ∣ c := by
  classical
  have hmodule : (inferInstance : Module ℤ M) = AddCommGroup.toIntModule M :=
    Subsingleton.elim _ _
  cases hmodule
  let x : N := ⟨c • P.ambientBasis i, hmem⟩
  refine ⟨P.relationBasis.repr x i, ?_⟩
  have hexpand := P.relationBasis.sum_repr x
  have hexpandM :
      ∑ j, (P.relationBasis.repr x) j • (P.relationBasis j : M) = (x : M) := by
    have hcoe := congrArg (N.subtype : N →ₗ[ℤ] M) hexpand
    simpa only [map_sum, map_smul, LinearMap.coe_coe,
      LinearMap.coe_mk, AddHom.coe_mk] using hcoe
  have hre := congrArg P.ambientBasis.repr hexpandM
  rw [map_sum] at hre
  simp only [P.relation_eq, smul_smul, map_smul,
    Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one] at hre
  have hi := congrArg (Finsupp.lapply i : (ι →₀ ℤ) →ₗ[ℤ] ℤ) hre
  rw [map_sum] at hi
  simpa [Finsupp.single_apply, x, mul_comm] using hi.symm

/-- A finite quotient produces the positive, square Smith presentation used in the coordinate
proof.  In particular, positivity of the diagonal entries is proved, not assumed. -/
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

/-- The quotient coordinates associated with the same positive Smith presentation. -/
def quotientEquivPiZMod (b : Module.Basis ι ℤ M) (N : Submodule ℤ M)
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (hfinite : Finite (M ⧸ N)) :
    (M ⧸ N) ≃+ ∀ i : ι,
      ZMod ((ofFiniteQuotient b N hfinite).diagonal i) := by
  have hmodule : (inferInstance : Module ℤ M) = AddCommGroup.toIntModule M :=
    Subsingleton.elim _ _
  cases hmodule
  letI : Finite (M ⧸ N) := hfinite
  let hrank : Module.finrank ℤ N = Module.finrank ℤ M :=
    (Submodule.finiteQuotient_iff N).mp inferInstance
  change (M ⧸ N) ≃+ ∀ i : ι,
    ZMod (Submodule.smithNormalFormCoeffs b hrank i).natAbs
  exact Submodule.quotientEquivPiZMod N b hrank

end PositiveSmithPresentation

end

end DegreeFive

end LieRings
