import LieRings.FinitePlateau.MagnusProbe

/-!
# Masked Magnus probes for the finite plateau presentation

The three shifted rows have leading coefficients `4`, `16`, and `64`.
For the corresponding modular probes we successively erase the earlier
small generators:

* modulo `4`, no generator is erased;
* modulo `16`, `x₁` is erased;
* modulo `64`, `x₁` and `x₂` are erased.

At truncation degree at most `N + 2`, every high tail `cᵢ` and every top
relation is zero.  Consequently these masks kill the *whole* shifted rows,
not merely their leading terms, and the probes descend through the exact
manuscript presentation.
-/

namespace LieRings.FinitePlateau

noncomputable section

namespace MagnusMasks

open MagnusProbe
open LieRings.Plotkin

/-- The coefficient modulus belonging to a shifted row. -/
def modulus : Fin 3 → ℕ
  | 0 => 4
  | 1 => 16
  | 2 => 64

@[simp] theorem modulus_zero : modulus 0 = 4 := rfl
@[simp] theorem modulus_one : modulus 1 = 16 := rfl
@[simp] theorem modulus_two : modulus 2 = 64 := rfl

/-- The occurrence mask for row `i`.  The generator `x₅` (index zero)
always survives; among `x₁,x₂,x₃,x₄`, precisely those whose
manuscript index is strictly later than `i` survive. -/
def Active (i : Fin 3) (j : Generator) : Prop :=
  j = 0 ∨ i.val < j.val

instance (i : Fin 3) (j : Generator) : Decidable (Active i j) :=
  Classical.propDecidable _

@[simp] theorem active_zero (j : Generator) : Active 0 j := by
  fin_cases j <;> simp [Active]

@[simp] theorem active_one (j : Generator) :
    Active 1 j ↔ j ≠ smallGeneratorIndex 0 := by
  fin_cases j <;> simp [Active, smallGeneratorIndex]

@[simp] theorem active_two (j : Generator) :
    Active 2 j ↔
      j ≠ smallGeneratorIndex 0 ∧ j ≠ smallGeneratorIndex 1 := by
  fin_cases j <;> simp [Active, smallGeneratorIndex]

@[simp] theorem not_active_one_x1 :
    ¬ Active 1 (smallGeneratorIndex 0) := by simp

@[simp] theorem not_active_two_x1 :
    ¬ Active 2 (smallGeneratorIndex 0) := by simp

@[simp] theorem not_active_two_x2 :
    ¬ Active 2 (smallGeneratorIndex 1) := by simp

/-- The masked value of a free generator. -/
def maskedGenerator (i : Fin 3) (r : ℕ) (j : Generator) :
    Target (modulus i) r :=
  if Active i j then Ring.generator (modulus i) r j else 0

@[simp] theorem maskedGenerator_of_active (i : Fin 3) (r : ℕ)
    (j : Generator) (hj : Active i j) :
    maskedGenerator i r j = Ring.generator (modulus i) r j := by
  simp [maskedGenerator, hj]

@[simp] theorem maskedGenerator_of_not_active (i : Fin 3) (r : ℕ)
    (j : Generator) (hj : ¬ Active i j) :
    maskedGenerator i r j = 0 := by
  simp [maskedGenerator, hj]

/-- Linear generator assignment for the masked probe. -/
def generatorLinearMap (i : Fin 3) (r : ℕ) :
    GeneratorModule →ₗ[ℤ] Target (modulus i) r :=
  generatorBasis.constr ℤ (maskedGenerator i r)

@[simp] theorem generatorLinearMap_basis (i : Fin 3) (r : ℕ)
    (j : Generator) :
    generatorLinearMap i r (generatorBasis j) = maskedGenerator i r j := by
  exact generatorBasis.constr_basis ℤ (maskedGenerator i r) j

/-- Universal evaluation with the row mask `i`. -/
def sourceProbe (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 4) :
    Source N →ₗ⁅ℤ⁆ Target (modulus i) r :=
  FreeMetabelian.Evaluation.lieHom
    (MagnusProbe.Target.isMetabelian (modulus i) r)
    (MagnusProbe.Target.lowerCentralSeries_eq_bot_of_le
      (modulus i) r (n := N + 3) (by omega))
    (generatorLinearMap i r)

@[simp] theorem sourceProbe_sourceGenerator
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 4)
    (j : Generator) :
    sourceProbe N i r hr (sourceGenerator N j) = maskedGenerator i r j := by
  rw [sourceProbe, sourceGenerator, FreeMetabelian.Free.weightIncl,
    FreeMetabelian.Evaluation.lieHom_apply,
    FreeMetabelian.Evaluation.linear_incl]
  exact generatorLinearMap_basis i r j

/-! ## Vanishing of the complete presentation -/

private theorem rightBracketPow_mem_lowerCentralSeries
    (N k : ℕ) :
    rightBracketPow (x4Source N) (x5Source N) k ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [rightBracketPow_succ]
      have hrev : ⁅x5Source N,
          rightBracketPow (x4Source N) (x5Source N) k⁆ ∈
          LieModule.lowerCentralSeries ℤ (Source N) (Source N) (k + 1) := by
        rw [LieModule.lowerCentralSeries_succ]
        exact LieSubmodule.lie_mem_lie (by simp) ih
      rw [← lie_skew]
      exact (LieModule.lowerCentralSeries ℤ (Source N) (Source N) (k + 1)).neg_mem hrev

private theorem cSource_mem_lowerCentralSeries (N : ℕ) (j : Fin 3) :
    cSource N j ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1) := by
  rw [cSource]
  have hrev : ⁅smallSourceGenerator N j, tSource N⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp)
      (by simpa [tSource] using rightBracketPow_mem_lowerCentralSeries N N)
  rw [← lie_skew]
  exact (LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).neg_mem hrev

private theorem map_mem_target_lowerCentralSeries
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 4)
    (k : ℕ) {x : Source N}
    (hx : x ∈ LieModule.lowerCentralSeries ℤ (Source N) (Source N) k) :
    sourceProbe N i r hr x ∈
      LieModule.lowerCentralSeries ℤ
        (Target (modulus i) r) (Target (modulus i) r) k := by
  apply (LieIdeal.map_lowerCentralSeries_le
    (R := ℤ) (f := sourceProbe N i r hr) k)
  exact LieIdeal.mem_map hx

@[simp] theorem sourceProbe_cSource_eq_zero
    (N : ℕ) (i j : Fin 3) (r : ℕ) (hr : r ≤ N + 2) :
    sourceProbe N i r (by omega) (cSource N j) = 0 := by
  have hm := map_mem_target_lowerCentralSeries N i r (by omega) (N + 1)
    (cSource_mem_lowerCentralSeries N j)
  have hbot := MagnusProbe.Target.lowerCentralSeries_eq_bot_of_le
    (modulus i) r (n := N + 1) hr
  rw [hbot] at hm
  exact hm

@[simp] theorem sourceProbe_uSource_eq_zero
    (N : ℕ) (i j : Fin 3) (r : ℕ) (hr : r ≤ N + 2) :
    sourceProbe N i r (by omega) (uSource N j) = 0 := by
  rw [uSource, LieHom.map_lie, sourceProbe_cSource_eq_zero N i j r hr,
    zero_lie]

private theorem topHallSource_mem_lowerCentralSeries
    (N : ℕ) (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    topHallSource N h ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 2) := by
  rw [topHallSource, FreeMetabelian.hallBasis_apply]
  change FreeMetabelian.Free.incl
    (⟨N + 1 + 1, by omega⟩ : Fin (N + 3))
    (FreeMetabelian.hallVector generatorBasis (N + 1) h) ∈ _
  rw [← FreeMetabelian.Evaluation.hallBracket_eq_incl]
  exact FreeMetabelian.Evaluation.hallBracket_mem_lowerCentralSeries
    generatorBasis (N + 1) h (by omega)

@[simp] theorem sourceProbe_topHallSource_eq_zero
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    sourceProbe N i r (by omega) (topHallSource N h) = 0 := by
  have hm := map_mem_target_lowerCentralSeries N i r (by omega) (N + 2)
    (topHallSource_mem_lowerCentralSeries N h)
  have hbot := MagnusProbe.Target.lowerCentralSeries_eq_bot_of_le
    (modulus i) r (n := N + 2) (by omega)
  rw [hbot] at hm
  exact hm

private theorem modulus_zsmul_eq_zero (i : Fin 3) (r : ℕ)
    (x : Target (modulus i) r) :
    (modulus i : ℤ) • x = 0 := by
  apply MagnusProbe.Ring.ext
  · change (modulus i : ℤ) • x.scalar = 0
    have hInt := Int.cast_smul_eq_zsmul ℤ (modulus i : ℤ) x.scalar
    have hMod := Int.cast_smul_eq_zsmul (ZMod (modulus i))
      (modulus i : ℤ) x.scalar
    have hbridge : (modulus i : ℤ) • x.scalar =
        ((modulus i : ℤ) : ZMod (modulus i)) • x.scalar := by
      simpa only [Int.cast_id] using hInt.trans hMod.symm
    rw [hbridge]
    simp
  · funext j
    change (modulus i : ℤ) • x.vector j = 0
    have hInt := Int.cast_smul_eq_zsmul ℤ (modulus i : ℤ) (x.vector j)
    have hMod := Int.cast_smul_eq_zsmul (ZMod (modulus i))
      (modulus i : ℤ) (x.vector j)
    have hbridge : (modulus i : ℤ) • x.vector j =
        ((modulus i : ℤ) : ZMod (modulus i)) • x.vector j := by
      simpa only [Int.cast_id] using hInt.trans hMod.symm
    rw [hbridge]
    simp

private theorem zsmul_eq_zero_of_modulus_dvd (i : Fin 3) (r : ℕ)
    (a : ℤ) (ha : (modulus i : ℤ) ∣ a)
    (x : Target (modulus i) r) : a • x = 0 := by
  obtain ⟨b, rfl⟩ := ha
  rw [mul_smul]
  exact modulus_zsmul_eq_zero i r (b • x)

private theorem sourceProbe_zsmul_sourceGenerator_eq_zero
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2)
    (a : ℤ) (j : Generator)
    (ha : (modulus i : ℤ) ∣ a ∨ ¬ Active i j) :
    sourceProbe N i r (by omega) (a • sourceGenerator N j) = 0 := by
  rw [map_zsmul, sourceProbe_sourceGenerator]
  rcases ha with ha | hj
  · exact zsmul_eq_zero_of_modulus_dvd i r a ha _
  · rw [maskedGenerator_of_not_active i r j hj, smul_zero]

@[simp] theorem sourceProbe_r1_eq_zero
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2) :
    sourceProbe N i r (by omega) (r1Source N) = 0 := by
  have hlead : sourceProbe N i r (by omega) ((4 : ℤ) • x1Source N) = 0 := by
    change sourceProbe N i r (by omega) ((4 : ℤ) • sourceGenerator N 1) = 0
    apply sourceProbe_zsmul_sourceGenerator_eq_zero N i r hr
    fin_cases i <;> simp [modulus, Active]
  have hc3 := sourceProbe_cSource_eq_zero N i 2 r hr
  have hc2 := sourceProbe_cSource_eq_zero N i 1 r hr
  simp only [r1Source, map_add, map_zsmul]
  rw [hc3, hc2, smul_zero, add_zero]
  simpa only [map_zsmul, add_zero] using hlead

@[simp] theorem sourceProbe_r2_eq_zero
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2) :
    sourceProbe N i r (by omega) (r2Source N) = 0 := by
  have hlead : sourceProbe N i r (by omega) ((16 : ℤ) • x2Source N) = 0 := by
    change sourceProbe N i r (by omega) ((16 : ℤ) • sourceGenerator N 2) = 0
    apply sourceProbe_zsmul_sourceGenerator_eq_zero N i r hr
    fin_cases i <;> simp [modulus, Active]
  have hc3 := sourceProbe_cSource_eq_zero N i 2 r hr
  have hc1 := sourceProbe_cSource_eq_zero N i 0 r hr
  simp only [r2Source, map_sub, map_add, map_zsmul]
  rw [hc3, hc1, smul_zero, sub_zero, add_zero]
  simpa only [map_zsmul, sub_zero, smul_zero] using hlead

@[simp] theorem sourceProbe_r3_eq_zero
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2) :
    sourceProbe N i r (by omega) (r3Source N) = 0 := by
  have hlead : sourceProbe N i r (by omega) ((64 : ℤ) • x3Source N) = 0 := by
    change sourceProbe N i r (by omega) ((64 : ℤ) • sourceGenerator N 3) = 0
    apply sourceProbe_zsmul_sourceGenerator_eq_zero N i r hr
    fin_cases i <;> simp [modulus, Active]
  have hc2 := sourceProbe_cSource_eq_zero N i 1 r hr
  have hc1 := sourceProbe_cSource_eq_zero N i 0 r hr
  simp only [r3Source, map_sub, map_zsmul]
  rw [hc2, hc1, smul_zero, sub_zero]
  simpa only [map_zsmul, sub_zero, smul_zero] using hlead

theorem sourceProbe_eq_zero_of_mem_definingRelators
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2)
    {z : Source N} (hz : z ∈ definingRelators N) :
    sourceProbe N i r (by omega) z = 0 := by
  simp only [definingRelators, Set.mem_union] at hz
  rcases hz with ((hshift | htop) | hex)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hshift
    rcases hshift with (rfl | rfl | rfl)
    · exact sourceProbe_r1_eq_zero N i r hr
    · exact sourceProbe_r2_eq_zero N i r hr
    · exact sourceProbe_r3_eq_zero N i r hr
  · rcases htop with ⟨h, -, rfl⟩
    exact sourceProbe_topHallSource_eq_zero N i r hr h
  · simp only [exceptionalRelators, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hex
    rcases hex with (rfl | rfl | rfl)
    · simp [sourceProbe_uSource_eq_zero N i 0 r hr,
        sourceProbe_uSource_eq_zero N i 2 r hr]
    · simp [sourceProbe_uSource_eq_zero N i 1 r hr,
        sourceProbe_uSource_eq_zero N i 2 r hr]
    · simp [sourceProbe_uSource_eq_zero N i 2 r hr]

/-- The complete defining ideal, including every Lie consequence of every
displayed row, lies in the kernel of the masked probe. -/
theorem relationIdeal_le_ker_sourceProbe
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2) :
    relationIdeal N ≤ LieHom.ker (sourceProbe N i r (by omega)) := by
  rw [relationIdeal, LieSubmodule.lieSpan_le]
  intro z hz
  exact sourceProbe_eq_zero_of_mem_definingRelators N i r hr hz

/-- Descend a masked source probe through the exact presentation. -/
def quotientProbe (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2) :
    L N →ₗ⁅ℤ⁆ Target (modulus i) r where
  toLinearMap := (relationIdeal N).toSubmodule.liftQ
    (sourceProbe N i r (by omega)).toLinearMap (by
      intro x hx
      exact relationIdeal_le_ker_sourceProbe N i r hr hx)
  map_lie' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        rw [← LieSubmodule.Quotient.mk_bracket]
        exact LieHom.map_lie (sourceProbe N i r (by omega)) x y

@[simp] theorem quotientProbe_quotientMap
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2)
    (z : Source N) :
    quotientProbe N i r hr (quotientMap N z) =
      sourceProbe N i r (by omega) z := by
  change (relationIdeal N).toSubmodule.liftQ
    (sourceProbe N i r (by omega)).toLinearMap _
      (LieSubmodule.Quotient.mk z) = _
  exact Submodule.liftQ_apply _ _ z

/-- A critical dimension element is zero in every descended masked probe. -/
theorem quotientProbe_eq_zero_of_mem_dimensionSubring
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2)
    {z : L N} (hz : z ∈ dimensionSubring ℤ (L N) (N + 4)) :
    quotientProbe N i r hr z = 0 := by
  let rho : L N →ₗ⁅ℤ⁆ Unitization ℤ (Ring (modulus i) r) :=
    nonUnitalCommutatorToUnitization.comp (quotientProbe N i r hr)
  have hzero : rho z = 0 :=
    lieHom_eq_zero_of_mem_dimensionSubring_of_ideal_pow_eq_bot rho
      unitizationIdeal
      (fun y ↦ nonUnitalCommutatorToUnitization_mem
        (quotientProbe N i r hr y))
      (N + 4)
      (MagnusProbe.unitizationIdeal_pow_eq_bot (modulus i) r (N + 4)
        (by omega) (by omega)) hz
  change (show Ring (modulus i) r from quotientProbe N i r hr z) = 0
  apply Unitization.inr_injective (R := ℤ)
    (A := Ring (modulus i) r)
  simpa [rho] using hzero

theorem sourceProbe_eq_zero_of_quotient_dimensionSubring
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 2)
    {x : Source N}
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4)) :
    sourceProbe N i r (by omega) x = 0 := by
  rw [← quotientProbe_quotientMap N i r hr]
  exact quotientProbe_eq_zero_of_mem_dimensionSubring N i r hr hx

/-! ## Exact surviving Hall words -/

/-- Recursive occurrence predicate: every generator occurrence of the Hall
comb survives the mask.  This form mirrors the recursive Hall bracket and is
therefore directly usable without multiset collection. -/
def HallSurvives (i : Fin 3) :
    (s : ℕ) → FreeMetabelian.HallIndex Generator s → Prop
  | 0, h => Active i h.head ∧ Active i h.pivot
  | s + 1, h => Active i h.nextTooth ∧ HallSurvives i s h.predecessor

@[simp] theorem hallSurvives_zero (i : Fin 3)
    (h : FreeMetabelian.HallIndex Generator 0) :
    HallSurvives i 0 h ↔ Active i h.head ∧ Active i h.pivot := Iff.rfl

@[simp] theorem hallSurvives_succ (i : Fin 3) (s : ℕ)
    (h : FreeMetabelian.HallIndex Generator (s + 1)) :
    HallSurvives i (s + 1) h ↔
      Active i h.nextTooth ∧ HallSurvives i s h.predecessor := Iff.rfl

set_option maxHeartbeats 1000000 in
/-- On a Hall comb all of whose occurrences survive, the masked and
unmasked Magnus evaluations agree exactly. -/
theorem sourceProbe_hallBracket_eq_unmasked
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 4) :
    ∀ (s : ℕ) (h : FreeMetabelian.HallIndex Generator s)
      (hs : s + 1 < N + 3), HallSurvives i s h →
      sourceProbe N i r (by omega)
          (FreeMetabelian.Evaluation.hallBracket generatorBasis s h hs) =
        MagnusProbe.sourceProbe N (modulus i) r (by omega)
          (FreeMetabelian.Evaluation.hallBracket generatorBasis s h hs) := by
  intro s
  induction s with
  | zero =>
      intro h hs ha
      rcases ha with ⟨hhead, hpivot⟩
      have hmHead : sourceProbe N i r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.head)) = maskedGenerator i r h.head := by
        change sourceProbe N i r (by omega) (sourceGenerator N h.head) = _
        exact sourceProbe_sourceGenerator N i r (by omega) h.head
      have hmPivot : sourceProbe N i r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.pivot)) = maskedGenerator i r h.pivot := by
        change sourceProbe N i r (by omega) (sourceGenerator N h.pivot) = _
        exact sourceProbe_sourceGenerator N i r (by omega) h.pivot
      have huHead : MagnusProbe.sourceProbe N (modulus i) r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.head)) =
          Ring.generator (modulus i) r h.head := by
        change MagnusProbe.sourceProbe N (modulus i) r (by omega)
          (sourceGenerator N h.head) = _
        exact MagnusProbe.sourceProbe_sourceGenerator N (modulus i) r
          (by omega) h.head
      have huPivot : MagnusProbe.sourceProbe N (modulus i) r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.pivot)) =
          Ring.generator (modulus i) r h.pivot := by
        change MagnusProbe.sourceProbe N (modulus i) r (by omega)
          (sourceGenerator N h.pivot) = _
        exact MagnusProbe.sourceProbe_sourceGenerator N (modulus i) r
          (by omega) h.pivot
      rw [FreeMetabelian.Evaluation.hallBracket,
        LieHom.map_lie, LieHom.map_lie,
        hmHead, hmPivot, huHead, huPivot,
        maskedGenerator_of_active _ _ _ hhead,
        maskedGenerator_of_active _ _ _ hpivot]
  | succ s ih =>
      intro h hs ha
      rcases ha with ⟨hnext, hpred⟩
      have hmNext : sourceProbe N i r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.nextTooth)) = maskedGenerator i r h.nextTooth := by
        change sourceProbe N i r (by omega) (sourceGenerator N h.nextTooth) = _
        exact sourceProbe_sourceGenerator N i r (by omega) h.nextTooth
      have huNext : MagnusProbe.sourceProbe N (modulus i) r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.nextTooth)) =
          Ring.generator (modulus i) r h.nextTooth := by
        change MagnusProbe.sourceProbe N (modulus i) r (by omega)
          (sourceGenerator N h.nextTooth) = _
        exact MagnusProbe.sourceProbe_sourceGenerator N (modulus i) r
          (by omega) h.nextTooth
      rw [FreeMetabelian.Evaluation.hallBracket,
        LieHom.map_lie, LieHom.map_lie,
        ih h.predecessor (by omega) hpred,
        hmNext, huNext,
        maskedGenerator_of_active _ _ _ hnext]

/-- Exact vector-coordinate formula for a surviving Hall comb. -/
theorem sourceProbe_hallBracket_vector
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 4)
    (s : ℕ) (h : FreeMetabelian.HallIndex Generator s)
    (hs : s + 1 < N + 3) (ha : HallSurvives i s h)
    (j : Generator) :
    (sourceProbe N i r (by omega)
      (FreeMetabelian.Evaluation.hallBracket generatorBasis s h hs)).vector j =
      MagnusProbe.hallSign s •
        ((if h.pivot = j then MagnusProbe.hallProduct (modulus i) r s h else 0) -
          (if h.head = j then MagnusProbe.hallProduct (modulus i) r s h else 0)) := by
  rw [sourceProbe_hallBracket_eq_unmasked N i r hr s h hs ha]
  exact MagnusProbe.sourceProbe_hallBracket_vector
    N (modulus i) r (by omega) s h hs j

/-! ## The integral outer-generator mask -/

/-- The integral mask retains only the two outer generators `x₅,x₄` and
erases `x₁,x₂,x₃`. -/
def OuterActive (j : Generator) : Prop := j = 0 ∨ j = 4

instance (j : Generator) : Decidable (OuterActive j) :=
  Classical.propDecidable _

@[simp] theorem outerActive_zero : OuterActive (0 : Generator) := Or.inl rfl
@[simp] theorem outerActive_four : OuterActive (4 : Generator) := Or.inr rfl

@[simp] theorem not_outerActive_smallGeneratorIndex (j : Fin 3) :
    ¬ OuterActive (smallGeneratorIndex j) := by
  fin_cases j <;> simp [OuterActive, smallGeneratorIndex]

def outerGenerator (r : ℕ) (j : Generator) : Target 0 r :=
  if OuterActive j then Ring.generator 0 r j else 0

@[simp] theorem outerGenerator_of_active (r : ℕ) (j : Generator)
    (hj : OuterActive j) :
    outerGenerator r j = Ring.generator 0 r j := by
  simp [outerGenerator, hj]

@[simp] theorem outerGenerator_of_not_active (r : ℕ) (j : Generator)
    (hj : ¬ OuterActive j) : outerGenerator r j = 0 := by
  simp [outerGenerator, hj]

def outerGeneratorLinearMap (r : ℕ) :
    GeneratorModule →ₗ[ℤ] Target 0 r :=
  generatorBasis.constr ℤ (outerGenerator r)

@[simp] theorem outerGeneratorLinearMap_basis (r : ℕ) (j : Generator) :
    outerGeneratorLinearMap r (generatorBasis j) = outerGenerator r j := by
  exact generatorBasis.constr_basis ℤ (outerGenerator r) j

/-- Integral universal evaluation retaining only `x₅,x₄`. -/
def outerSourceProbe (N r : ℕ) (hr : r ≤ N + 4) :
    Source N →ₗ⁅ℤ⁆ Target 0 r :=
  FreeMetabelian.Evaluation.lieHom
    (MagnusProbe.Target.isMetabelian 0 r)
    (MagnusProbe.Target.lowerCentralSeries_eq_bot_of_le
      0 r (n := N + 3) (by omega))
    (outerGeneratorLinearMap r)

@[simp] theorem outerSourceProbe_sourceGenerator
    (N r : ℕ) (hr : r ≤ N + 4) (j : Generator) :
    outerSourceProbe N r hr (sourceGenerator N j) = outerGenerator r j := by
  rw [outerSourceProbe, sourceGenerator, FreeMetabelian.Free.weightIncl,
    FreeMetabelian.Evaluation.lieHom_apply,
    FreeMetabelian.Evaluation.linear_incl]
  exact outerGeneratorLinearMap_basis r j

@[simp] theorem outerSourceProbe_smallSourceGenerator_eq_zero
    (N r : ℕ) (hr : r ≤ N + 4) (j : Fin 3) :
    outerSourceProbe N r hr (smallSourceGenerator N j) = 0 := by
  change outerSourceProbe N r hr
    (sourceGenerator N (smallGeneratorIndex j)) = 0
  rw [outerSourceProbe_sourceGenerator,
    outerGenerator_of_not_active r _
      (not_outerActive_smallGeneratorIndex j)]

@[simp] theorem outerSourceProbe_cSource_eq_zero
    (N r : ℕ) (hr : r ≤ N + 4) (j : Fin 3) :
    outerSourceProbe N r hr (cSource N j) = 0 := by
  rw [cSource, LieHom.map_lie,
    outerSourceProbe_smallSourceGenerator_eq_zero, lie_zero]

@[simp] theorem outerSourceProbe_uSource_eq_zero
    (N r : ℕ) (hr : r ≤ N + 4) (j : Fin 3) :
    outerSourceProbe N r hr (uSource N j) = 0 := by
  rw [uSource, LieHom.map_lie, outerSourceProbe_cSource_eq_zero, zero_lie]

private theorem outer_map_mem_target_lowerCentralSeries
    (N r k : ℕ) (hr : r ≤ N + 4) {x : Source N}
    (hx : x ∈ LieModule.lowerCentralSeries ℤ (Source N) (Source N) k) :
    outerSourceProbe N r hr x ∈
      LieModule.lowerCentralSeries ℤ (Target 0 r) (Target 0 r) k := by
  apply (LieIdeal.map_lowerCentralSeries_le
    (R := ℤ) (f := outerSourceProbe N r hr) k)
  exact LieIdeal.mem_map hx

@[simp] theorem outerSourceProbe_topHallSource_eq_zero
    (N r : ℕ) (hr : r ≤ N + 3)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    outerSourceProbe N r (by omega) (topHallSource N h) = 0 := by
  have hm := outer_map_mem_target_lowerCentralSeries N r (N + 2)
    (by omega) (topHallSource_mem_lowerCentralSeries N h)
  have hbot := MagnusProbe.Target.lowerCentralSeries_eq_bot_of_le
    0 r (n := N + 2) hr
  rw [hbot] at hm
  exact hm

@[simp] theorem outerSourceProbe_r1_eq_zero
    (N r : ℕ) (hr : r ≤ N + 3) :
    outerSourceProbe N r (by omega) (r1Source N) = 0 := by
  simp [r1Source, x1Source, outerGenerator, OuterActive]

@[simp] theorem outerSourceProbe_r2_eq_zero
    (N r : ℕ) (hr : r ≤ N + 3) :
    outerSourceProbe N r (by omega) (r2Source N) = 0 := by
  simp [r2Source, x2Source, outerGenerator, OuterActive]

@[simp] theorem outerSourceProbe_r3_eq_zero
    (N r : ℕ) (hr : r ≤ N + 3) :
    outerSourceProbe N r (by omega) (r3Source N) = 0 := by
  simp [r3Source, x3Source, outerGenerator, OuterActive]

theorem outerSourceProbe_eq_zero_of_mem_definingRelators
    (N r : ℕ) (hr : r ≤ N + 3) {z : Source N}
    (hz : z ∈ definingRelators N) :
    outerSourceProbe N r (by omega) z = 0 := by
  simp only [definingRelators, Set.mem_union] at hz
  rcases hz with ((hshift | htop) | hex)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hshift
    rcases hshift with (rfl | rfl | rfl)
    · exact outerSourceProbe_r1_eq_zero N r hr
    · exact outerSourceProbe_r2_eq_zero N r hr
    · exact outerSourceProbe_r3_eq_zero N r hr
  · rcases htop with ⟨h, -, rfl⟩
    exact outerSourceProbe_topHallSource_eq_zero N r hr h
  · simp only [exceptionalRelators, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hex
    rcases hex with (rfl | rfl | rfl)
    · simp
    · simp
    · simp

theorem relationIdeal_le_ker_outerSourceProbe
    (N r : ℕ) (hr : r ≤ N + 3) :
    relationIdeal N ≤ LieHom.ker (outerSourceProbe N r (by omega)) := by
  rw [relationIdeal, LieSubmodule.lieSpan_le]
  intro z hz
  exact outerSourceProbe_eq_zero_of_mem_definingRelators N r hr hz

def outerQuotientProbe (N r : ℕ) (hr : r ≤ N + 3) :
    L N →ₗ⁅ℤ⁆ Target 0 r where
  toLinearMap := (relationIdeal N).toSubmodule.liftQ
    (outerSourceProbe N r (by omega)).toLinearMap (by
      intro x hx
      exact relationIdeal_le_ker_outerSourceProbe N r hr hx)
  map_lie' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        rw [← LieSubmodule.Quotient.mk_bracket]
        exact LieHom.map_lie (outerSourceProbe N r (by omega)) x y

@[simp] theorem outerQuotientProbe_quotientMap
    (N r : ℕ) (hr : r ≤ N + 3) (z : Source N) :
    outerQuotientProbe N r hr (quotientMap N z) =
      outerSourceProbe N r (by omega) z := by
  exact Submodule.liftQ_apply _ _ z

theorem outerQuotientProbe_eq_zero_of_mem_dimensionSubring
    (N r : ℕ) (hr : r ≤ N + 3) {z : L N}
    (hz : z ∈ dimensionSubring ℤ (L N) (N + 4)) :
    outerQuotientProbe N r hr z = 0 := by
  let rho : L N →ₗ⁅ℤ⁆ Unitization ℤ (Ring 0 r) :=
    nonUnitalCommutatorToUnitization.comp (outerQuotientProbe N r hr)
  have hzero : rho z = 0 :=
    lieHom_eq_zero_of_mem_dimensionSubring_of_ideal_pow_eq_bot rho
      unitizationIdeal
      (fun y ↦ nonUnitalCommutatorToUnitization_mem
        (outerQuotientProbe N r hr y))
      (N + 4)
      (MagnusProbe.unitizationIdeal_pow_eq_bot 0 r (N + 4)
        (by omega) (by omega)) hz
  change (show Ring 0 r from outerQuotientProbe N r hr z) = 0
  apply Unitization.inr_injective (R := ℤ) (A := Ring 0 r)
  simpa [rho] using hzero

theorem outerSourceProbe_eq_zero_of_quotient_dimensionSubring
    (N r : ℕ) (hr : r ≤ N + 3) {x : Source N}
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4)) :
    outerSourceProbe N r (by omega) x = 0 := by
  rw [← outerQuotientProbe_quotientMap N r hr]
  exact outerQuotientProbe_eq_zero_of_mem_dimensionSubring N r hr hx

/-- Every occurrence in the Hall comb is one of the two outer generators. -/
def OuterHallSurvives :
    (s : ℕ) → FreeMetabelian.HallIndex Generator s → Prop
  | 0, h => OuterActive h.head ∧ OuterActive h.pivot
  | s + 1, h => OuterActive h.nextTooth ∧
      OuterHallSurvives s h.predecessor

@[simp] theorem outerHallSurvives_zero
    (h : FreeMetabelian.HallIndex Generator 0) :
    OuterHallSurvives 0 h ↔ OuterActive h.head ∧ OuterActive h.pivot := Iff.rfl

@[simp] theorem outerHallSurvives_succ (s : ℕ)
    (h : FreeMetabelian.HallIndex Generator (s + 1)) :
    OuterHallSurvives (s + 1) h ↔
      OuterActive h.nextTooth ∧ OuterHallSurvives s h.predecessor := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem outerSourceProbe_hallBracket_eq_unmasked
    (N r : ℕ) (hr : r ≤ N + 3) :
    ∀ (s : ℕ) (h : FreeMetabelian.HallIndex Generator s)
      (hs : s + 1 < N + 3), OuterHallSurvives s h →
      outerSourceProbe N r (by omega)
          (FreeMetabelian.Evaluation.hallBracket generatorBasis s h hs) =
        MagnusProbe.sourceProbe N 0 r (by omega)
          (FreeMetabelian.Evaluation.hallBracket generatorBasis s h hs) := by
  intro s
  induction s with
  | zero =>
      intro h hs ha
      rcases ha with ⟨hhead, hpivot⟩
      have hmHead : outerSourceProbe N r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.head)) = outerGenerator r h.head := by
        change outerSourceProbe N r (by omega) (sourceGenerator N h.head) = _
        exact outerSourceProbe_sourceGenerator N r (by omega) h.head
      have hmPivot : outerSourceProbe N r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.pivot)) = outerGenerator r h.pivot := by
        change outerSourceProbe N r (by omega) (sourceGenerator N h.pivot) = _
        exact outerSourceProbe_sourceGenerator N r (by omega) h.pivot
      have huHead : MagnusProbe.sourceProbe N 0 r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.head)) = Ring.generator 0 r h.head := by
        change MagnusProbe.sourceProbe N 0 r (by omega)
          (sourceGenerator N h.head) = _
        exact MagnusProbe.sourceProbe_sourceGenerator N 0 r (by omega) h.head
      have huPivot : MagnusProbe.sourceProbe N 0 r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.pivot)) = Ring.generator 0 r h.pivot := by
        change MagnusProbe.sourceProbe N 0 r (by omega)
          (sourceGenerator N h.pivot) = _
        exact MagnusProbe.sourceProbe_sourceGenerator N 0 r (by omega) h.pivot
      rw [FreeMetabelian.Evaluation.hallBracket,
        LieHom.map_lie, LieHom.map_lie, hmHead, hmPivot, huHead, huPivot,
        outerGenerator_of_active _ _ hhead,
        outerGenerator_of_active _ _ hpivot]
  | succ s ih =>
      intro h hs ha
      rcases ha with ⟨hnext, hpred⟩
      have hmNext : outerSourceProbe N r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.nextTooth)) = outerGenerator r h.nextTooth := by
        change outerSourceProbe N r (by omega)
          (sourceGenerator N h.nextTooth) = _
        exact outerSourceProbe_sourceGenerator N r (by omega) h.nextTooth
      have huNext : MagnusProbe.sourceProbe N 0 r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.nextTooth)) = Ring.generator 0 r h.nextTooth := by
        change MagnusProbe.sourceProbe N 0 r (by omega)
          (sourceGenerator N h.nextTooth) = _
        exact MagnusProbe.sourceProbe_sourceGenerator N 0 r
          (by omega) h.nextTooth
      rw [FreeMetabelian.Evaluation.hallBracket,
        LieHom.map_lie, LieHom.map_lie,
        ih h.predecessor (by omega) hpred, hmNext, huNext,
        outerGenerator_of_active _ _ hnext]

theorem outerSourceProbe_hallBracket_vector
    (N r : ℕ) (hr : r ≤ N + 3)
    (s : ℕ) (h : FreeMetabelian.HallIndex Generator s)
    (hs : s + 1 < N + 3) (ha : OuterHallSurvives s h)
    (j : Generator) :
    (outerSourceProbe N r (by omega)
      (FreeMetabelian.Evaluation.hallBracket generatorBasis s h hs)).vector j =
      MagnusProbe.hallSign s •
        ((if h.pivot = j then MagnusProbe.hallProduct 0 r s h else 0) -
          (if h.head = j then MagnusProbe.hallProduct 0 r s h else 0)) := by
  rw [outerSourceProbe_hallBracket_eq_unmasked N r hr s h hs ha]
  exact MagnusProbe.sourceProbe_hallBracket_vector N 0 r (by omega) s h hs j

end MagnusMasks

end

end LieRings.FinitePlateau
