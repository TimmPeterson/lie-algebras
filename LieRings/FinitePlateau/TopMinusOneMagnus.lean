import LieRings.FinitePlateau.MagnusCoordinateReads
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# The top-minus-one masked Magnus quotient

At truncation `N + 3`, the three elements `c_i` no longer vanish in the
masked Magnus probes.  Their images nevertheless have degree `N + 2` and
zero scalar coordinate.  Consequently they annihilate the whole positive
Magnus ring on both sides.  This file packages their additive span as a
two-sided ideal.  Quotienting by this ideal is the extra probe needed for
the weight-`N+2` Hall-coordinate step in the finite-plateau normal form.
-/

namespace LieRings.FinitePlateau

noncomputable section

namespace TopMinusOneMagnus

open LieRings.Plotkin
open MagnusProbe
open MagnusMasks

abbrev ProbeRing (N : ℕ) (i : Fin 3) :=
  MagnusProbe.Ring (MagnusMasks.modulus i) (N + 3)

/-- The image of `c_j` in masked probe `i`, at the first truncation at
which it can survive. -/
def cImage (N : ℕ) (i j : Fin 3) : ProbeRing N i :=
  MagnusMasks.sourceProbe N i (N + 3) (by omega) (cSource N j)

/-! ## The literal Hall indices of the three `c`-terms -/

/-- The symmetric teeth of `c_j=[x₄,x₅,...,x₅,x_j]`: after the initial
pair there are `N-1` further copies of `x₅` and one copy of `x_j`. -/
def cHallTeeth (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) : Sym Generator N :=
  Sym.mk
    (Multiset.replicate (N - 1) (0 : Generator) +
      ({smallGeneratorIndex j} : Multiset Generator))
    (by simp; omega)

/-- The literal Hall index representing `c_j`. -/
def cHallIndex (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) :
    FreeMetabelian.HallIndex Generator N where
  head := 4
  pivot := 0
  teeth := cHallTeeth N hN j
  pivot_lt_head := by decide
  pivot_le_teeth := fun k _ ↦ Fin.zero_le k

private theorem hallIndex_ext {q : ℕ}
    {a b : FreeMetabelian.HallIndex Generator q}
    (hh : a.head = b.head) (hp : a.pivot = b.pivot)
    (ht : a.teeth = b.teeth) : a = b := by
  cases a
  cases b
  simp only at hh hp ht
  subst_vars
  rfl

private theorem cHallIndex_nextTooth (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) :
    (cHallIndex (N + 1) (by omega) j).nextTooth = 0 := by
  simp only [FreeMetabelian.HallIndex.nextTooth, cHallIndex, cHallTeeth]
  change ((Multiset.replicate N (0 : Generator) +
    ({smallGeneratorIndex j} : Multiset Generator)).toFinset.min' _) = 0
  rw [Finset.min'_eq_iff]
  constructor
  · have hN0 : N ≠ 0 := by omega
    simp [hN0]
  · intro b _
    exact Fin.zero_le b

private theorem cHallIndex_predecessor (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) :
    (cHallIndex (N + 1) (by omega) j).predecessor =
      cHallIndex N hN j := by
  refine hallIndex_ext rfl rfl ?_
  apply Sym.ext
  simp only [FreeMetabelian.HallIndex.predecessor, cHallIndex, cHallTeeth]
  change Multiset.erase
        (Multiset.replicate N (0 : Generator) +
          ({smallGeneratorIndex j} : Multiset Generator))
        ((Multiset.replicate N (0 : Generator) +
          ({smallGeneratorIndex j} : Multiset Generator)).toFinset.min' _) =
      Multiset.replicate (N - 1) (0 : Generator) +
        ({smallGeneratorIndex j} : Multiset Generator)
  rw [show ((Multiset.replicate N (0 : Generator) +
        ({smallGeneratorIndex j} : Multiset Generator)).toFinset.min' _) = 0 by
    rw [Finset.min'_eq_iff]
    constructor
    · have hN0 : N ≠ 0 := by omega
      simp [hN0]
    · intro b _
      exact Fin.zero_le b]
  cases N with
  | zero => omega
  | succ n =>
      have hj : smallGeneratorIndex j ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp [smallGeneratorIndex] at this
      simp [Multiset.replicate_succ, hj]

private theorem cHallIndex_one_nextTooth (j : Fin 3) :
    (cHallIndex 1 (by omega) j).nextTooth = smallGeneratorIndex j := by
  fin_cases j <;> decide

private theorem bracket_mem_derived {N : ℕ} (x y : Source N) :
    ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ (Source N) 1 := by
  change ⁅x, y⁆ ∈ ⁅(⊤ : LieIdeal ℤ (Source N)),
    (⊤ : LieIdeal ℤ (Source N))⁆
  exact LieSubmodule.lie_mem_lie (by simp) (by simp)

private theorem source_right_actions_commute {N : ℕ} {d x y : Source N}
    (hd : d ∈ LieAlgebra.derivedSeries ℤ (Source N) 1) :
    ⁅⁅d, x⁆, y⁆ = ⁅⁅d, y⁆, x⁆ := by
  have hxy := bracket_mem_derived (N := N) x y
  have hz : ⁅d, ⁅x, y⁆⁆ = 0 :=
    FreeMetabelian.Free.isMetabelian.bracket_eq_zero hd hxy
  have hj := leibniz_lie d x y
  have hs : ⁅x, ⁅d, y⁆⁆ = -⁅⁅d, y⁆, x⁆ :=
    (lie_skew x ⁅d, y⁆).symm
  rw [hz, hs] at hj
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg]
  exact hj.symm

private theorem rightBracketPow_mem_derived (N r : ℕ) (hr : 1 ≤ r) :
    rightBracketPow (x4Source N) (x5Source N) r ∈
      LieAlgebra.derivedSeries ℤ (Source N) 1 := by
  cases r with
  | zero => omega
  | succ k => exact bracket_mem_derived _ _

private theorem embedded_c_hall_base (N : ℕ) (j : Fin 3) :
    FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis 1
        (cHallIndex 1 (by omega) j) (by omega) =
      ⁅⁅x4Source N, x5Source N⁆, smallSourceGenerator N j⁆ := by
  rw [FreeMetabelian.Evaluation.hallBracket,
    FreeMetabelian.Evaluation.hallBracket,
    cHallIndex_one_nextTooth]
  rfl

private theorem literal_c_succ (N r : ℕ) (hr : 1 ≤ r) (j : Fin 3) :
    ⁅rightBracketPow (x4Source N) (x5Source N) (r + 1),
        smallSourceGenerator N j⁆ =
      ⁅⁅rightBracketPow (x4Source N) (x5Source N) r,
          smallSourceGenerator N j⁆, x5Source N⁆ := by
  rw [rightBracketPow_succ]
  exact source_right_actions_commute (rightBracketPow_mem_derived N r hr)

private theorem embedded_c_hall_succ
    (N r : ℕ) (hr : 1 ≤ r) (hrN : r < N) (j : Fin 3) :
    FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis (r + 1)
        (cHallIndex (r + 1) (by omega) j) (by omega) =
      ⁅FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis r
          (cHallIndex r hr j) (by omega), x5Source N⁆ := by
  rw [FreeMetabelian.Evaluation.hallBracket,
    cHallIndex_predecessor r hr,
    cHallIndex_nextTooth r hr]
  rfl

private theorem embedded_c_hall_eq
    (N r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) (j : Fin 3) :
    FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis r
        (cHallIndex r hr j) (by omega) =
      ⁅rightBracketPow (x4Source N) (x5Source N) r,
        smallSourceGenerator N j⁆ := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        exact embedded_c_hall_base N j
      · have hr1 : 1 ≤ r := by omega
        rw [embedded_c_hall_succ N r hr1 (by omega) j,
          ih hr1 (by omega)]
        exact (literal_c_succ N r hr1 j).symm

/-- The exposed Hall index is exactly the manuscript element `c_j`. -/
theorem hallBracket_cHallIndex_eq_cSource
    (N : ℕ) (hN : 1 ≤ N) (j : Fin 3) :
    FreeMetabelian.Evaluation.hallBracket generatorBasis N
        (cHallIndex N hN j) (by omega) = cSource N j := by
  rw [cSource]
  exact embedded_c_hall_eq N N hN le_rfl j

@[simp] theorem cImage_scalar (N : ℕ) (i j : Fin 3) :
    (cImage N i j).scalar = 0 := by
  rw [cImage, cSource, LieHom.map_lie]
  exact MagnusProbe.Target.scalar_lie _ _ _ _

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

theorem cImage_mem_degree (N : ℕ) (i j : Fin 3) :
    (show MagnusProbe.Target (MagnusMasks.modulus i) (N + 3) from cImage N i j) ∈
      MagnusProbe.Target.degreeLieSubmodule
        (MagnusMasks.modulus i) (N + 3) (N + 2) := by
  have hm : MagnusMasks.sourceProbe N i (N + 3) (by omega) (cSource N j) ∈
      LieModule.lowerCentralSeries ℤ
        (MagnusProbe.Target (MagnusMasks.modulus i) (N + 3))
        (MagnusProbe.Target (MagnusMasks.modulus i) (N + 3)) (N + 1) := by
    apply (LieIdeal.map_lowerCentralSeries_le
      (R := ℤ) (f := MagnusMasks.sourceProbe N i (N + 3) (by omega)) (N + 1))
    exact LieIdeal.mem_map (cSource_mem_lowerCentralSeries N j)
  exact MagnusProbe.Target.lowerCentralSeries_le_degree
    (MagnusMasks.modulus i) (N + 3) (N + 1) hm

@[simp] theorem cImage_mul (N : ℕ) (i j : Fin 3) (x : ProbeRing N i) :
    cImage N i j * x = 0 := by
  apply MagnusProbe.Ring.ext
  · simp
  · funext k
    simp

@[simp] theorem mul_cImage (N : ℕ) (i j : Fin 3) (x : ProbeRing N i) :
    x * cImage N i j = 0 := by
  have hc := cImage_mem_degree N i j
  rw [MagnusProbe.Target.mem_degreeLieSubmodule_iff] at hc
  apply MagnusProbe.Ring.ext
  · simp
  · funext k
    apply Subtype.ext
    change ((x.scalar * (cImage N i j).vector k :
      MagnusProbe.positiveIdeal (MagnusMasks.modulus i) (N + 3)) :
        MagnusProbe.TruncatedPoly (MagnusMasks.modulus i) (N + 3)) = 0
    have hx : (x.scalar : MagnusProbe.TruncatedPoly
        (MagnusMasks.modulus i) (N + 3)) ∈
        MagnusProbe.positivePower (MagnusMasks.modulus i) (N + 3) 1 := by
      rw [MagnusProbe.positivePower_one]
      exact x.scalar.property
    have hmul : ((x.scalar * (cImage N i j).vector k :
        MagnusProbe.positiveIdeal (MagnusMasks.modulus i) (N + 3)) :
          MagnusProbe.TruncatedPoly (MagnusMasks.modulus i) (N + 3)) ∈
        MagnusProbe.positivePower (MagnusMasks.modulus i) (N + 3) (1 + (N + 2)) := by
      rw [MagnusProbe.positivePower_pow_add]
      exact Ideal.mul_mem_mul hx (hc.2 k)
    have hbot := MagnusProbe.positivePower_eq_bot_of_le
      (MagnusMasks.modulus i) (N + 3) (1 + (N + 2)) (by omega)
    rw [hbot] at hmul
    simpa using hmul

/-- The additive span of the three surviving `c`-images. -/
def cImageAddSubgroup (N : ℕ) (i : Fin 3) : AddSubgroup (ProbeRing N i) :=
  AddSubgroup.closure (Set.range (cImage N i))

theorem cImageAddSubgroup_mul (N : ℕ) (i : Fin 3)
    {y : ProbeRing N i} (hy : y ∈ cImageAddSubgroup N i)
    (x : ProbeRing N i) : y * x = 0 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact cImage_mul N i j x
  | zero => simp
  | add y z hy hz iy iz => rw [add_mul, iy, iz, add_zero]
  | neg y hy iy => rw [neg_mul, iy, neg_zero]

theorem mul_cImageAddSubgroup (N : ℕ) (i : Fin 3)
    (x : ProbeRing N i) {y : ProbeRing N i}
    (hy : y ∈ cImageAddSubgroup N i) : x * y = 0 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact mul_cImage N i j x
  | zero => simp
  | add y z hy hz iy iz => rw [mul_add, iy, iz, add_zero]
  | neg y hy iy => rw [mul_neg, iy, neg_zero]

/-- The `c`-span is already a two-sided ideal: every one of its elements
annihilates and is annihilated by the whole positive Magnus ring. -/
def cImageIdeal (N : ℕ) (i : Fin 3) : TwoSidedIdeal (ProbeRing N i) :=
  TwoSidedIdeal.mk' (cImageAddSubgroup N i : Set (ProbeRing N i))
    (cImageAddSubgroup N i).zero_mem
    (fun hx hy ↦ (cImageAddSubgroup N i).add_mem hx hy)
    (fun hx ↦ (cImageAddSubgroup N i).neg_mem hx)
    (fun {x y} hy ↦ by
      rw [mul_cImageAddSubgroup N i x hy]
      exact (cImageAddSubgroup N i).zero_mem)
    (fun {x y} hx ↦ by
      rw [cImageAddSubgroup_mul N i hx y]
      exact (cImageAddSubgroup N i).zero_mem)

@[simp] theorem mem_cImageIdeal_iff (N : ℕ) (i : Fin 3) (x : ProbeRing N i) :
    x ∈ cImageIdeal N i ↔ x ∈ cImageAddSubgroup N i := by
  apply TwoSidedIdeal.mem_mk'

theorem cImage_mem_ideal (N : ℕ) (i j : Fin 3) :
    cImage N i j ∈ cImageIdeal N i := by
  rw [mem_cImageIdeal_iff]
  exact AddSubgroup.subset_closure (Set.mem_range_self j)

/-! ## The quotient probe and the defining relations -/

/-- The nonunital quotient ring in which all three surviving `c`-images
are set equal to zero. -/
abbrev QuotientRing (N : ℕ) (i : Fin 3) :=
  (cImageIdeal N i).ringCon.Quotient

abbrev QuotientTarget (N : ℕ) (i : Fin 3) :=
  NonUnitalCommutator (QuotientRing N i)

/-- The canonical quotient map of positive Magnus rings. -/
def ringQuotientMap (N : ℕ) (i : Fin 3) :
    ProbeRing N i →ₙ+* QuotientRing N i where
  toFun := RingCon.toQuotient
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem ringQuotientMap_eq_zero_iff
    (N : ℕ) (i : Fin 3) (x : ProbeRing N i) :
    ringQuotientMap N i x = 0 ↔ x ∈ cImageIdeal N i := by
  change (↑x : (cImageIdeal N i).ringCon.Quotient) = ↑(0 : ProbeRing N i) ↔ _
  rw [RingCon.eq]
  exact (TwoSidedIdeal.mem_iff (cImageIdeal N i) x).symm

@[simp] theorem ringQuotientMap_cImage
    (N : ℕ) (i j : Fin 3) :
    ringQuotientMap N i (cImage N i j) = 0 :=
  (ringQuotientMap_eq_zero_iff N i _).2 (cImage_mem_ideal N i j)

/-- Compose the masked source probe with the ring quotient, regarded as a
homomorphism of commutator Lie rings. -/
def sourceQuotientProbe (N : ℕ) (i : Fin 3) :
    Source N →ₗ⁅ℤ⁆ QuotientTarget N i where
  toLinearMap :=
    (ringQuotientMap N i).toAddMonoidHom.toIntLinearMap.comp
      (MagnusMasks.sourceProbe N i (N + 3) (by omega)).toLinearMap
  map_lie' := by
    intro x y
    change ringQuotientMap N i
        (MagnusMasks.sourceProbe N i (N + 3) (by omega) ⁅x, y⁆) =
      ⁅ringQuotientMap N i
          (MagnusMasks.sourceProbe N i (N + 3) (by omega) x),
        ringQuotientMap N i
          (MagnusMasks.sourceProbe N i (N + 3) (by omega) y)⁆
    rw [LieHom.map_lie]
    rfl

@[simp] theorem sourceQuotientProbe_apply
    (N : ℕ) (i : Fin 3) (x : Source N) :
    sourceQuotientProbe N i x =
      ringQuotientMap N i
        (MagnusMasks.sourceProbe N i (N + 3) (by omega) x) := rfl

private theorem modulus_zsmul_eq_zero (i : Fin 3) (r : ℕ)
    (x : MagnusProbe.Target (MagnusMasks.modulus i) r) :
    (MagnusMasks.modulus i : ℤ) • x = 0 := by
  apply MagnusProbe.Ring.ext
  · change (MagnusMasks.modulus i : ℤ) • x.scalar = 0
    have hInt := Int.cast_smul_eq_zsmul ℤ
      (MagnusMasks.modulus i : ℤ) x.scalar
    have hMod := Int.cast_smul_eq_zsmul (ZMod (MagnusMasks.modulus i))
      (MagnusMasks.modulus i : ℤ) x.scalar
    have hbridge : (MagnusMasks.modulus i : ℤ) • x.scalar =
        ((MagnusMasks.modulus i : ℤ) : ZMod (MagnusMasks.modulus i)) •
          x.scalar := by
      simpa only [Int.cast_id] using hInt.trans hMod.symm
    rw [hbridge]
    simp
  · funext j
    change (MagnusMasks.modulus i : ℤ) • x.vector j = 0
    have hInt := Int.cast_smul_eq_zsmul ℤ
      (MagnusMasks.modulus i : ℤ) (x.vector j)
    have hMod := Int.cast_smul_eq_zsmul (ZMod (MagnusMasks.modulus i))
      (MagnusMasks.modulus i : ℤ) (x.vector j)
    have hbridge : (MagnusMasks.modulus i : ℤ) • x.vector j =
        ((MagnusMasks.modulus i : ℤ) : ZMod (MagnusMasks.modulus i)) •
          x.vector j := by
      simpa only [Int.cast_id] using hInt.trans hMod.symm
    rw [hbridge]
    simp

private theorem zsmul_eq_zero_of_modulus_dvd (i : Fin 3) (r : ℕ)
    (a : ℤ) (ha : (MagnusMasks.modulus i : ℤ) ∣ a)
    (x : MagnusProbe.Target (MagnusMasks.modulus i) r) : a • x = 0 := by
  obtain ⟨b, rfl⟩ := ha
  rw [mul_smul]
  exact modulus_zsmul_eq_zero i r (b • x)

private theorem sourceProbe_zsmul_sourceGenerator_eq_zero
    (N : ℕ) (i : Fin 3) (a : ℤ) (j : Generator)
    (ha : (MagnusMasks.modulus i : ℤ) ∣ a ∨ ¬ MagnusMasks.Active i j) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega)
      (a • sourceGenerator N j) = 0 := by
  rw [map_zsmul, MagnusMasks.sourceProbe_sourceGenerator]
  rcases ha with ha | hj
  · exact zsmul_eq_zero_of_modulus_dvd i (N + 3) a ha _
  · rw [MagnusMasks.maskedGenerator_of_not_active i (N + 3) j hj,
      smul_zero]

private theorem sourceProbe_rowLead_eq_zero
    (N : ℕ) (i j : Fin 3) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega)
      ((match j with | 0 => (4 : ℤ) | 1 => 16 | 2 => 64) •
        smallSourceGenerator N j) = 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    apply sourceProbe_zsmul_sourceGenerator_eq_zero
    simp [smallSourceGenerator, MagnusMasks.modulus,
      MagnusMasks.Active, smallGeneratorIndex]

private theorem probe_r1_mem_cImageIdeal (N : ℕ) (i : Fin 3) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega) (r1Source N) ∈
      cImageIdeal N i := by
  have hlead := sourceProbe_rowLead_eq_zero N i 0
  change MagnusMasks.sourceProbe N i (N + 3) (by omega)
      ((4 : ℤ) • x1Source N) = 0 at hlead
  have hlead' : (4 : ℤ) •
      MagnusMasks.sourceProbe N i (N + 3) (by omega) (x1Source N) = 0 := by
    simpa only [map_zsmul] using hlead
  simp only [r1Source, map_add, map_zsmul]
  rw [hlead', zero_add]
  exact (cImageIdeal N i).add_mem
    ((cImageIdeal N i).zsmul_mem 2 (cImage_mem_ideal N i 2))
    (cImage_mem_ideal N i 1)

private theorem probe_r2_mem_cImageIdeal (N : ℕ) (i : Fin 3) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega) (r2Source N) ∈
      cImageIdeal N i := by
  have hlead := sourceProbe_rowLead_eq_zero N i 1
  change MagnusMasks.sourceProbe N i (N + 3) (by omega)
      ((16 : ℤ) • x2Source N) = 0 at hlead
  have hlead' : (16 : ℤ) •
      MagnusMasks.sourceProbe N i (N + 3) (by omega) (x2Source N) = 0 := by
    simpa only [map_zsmul] using hlead
  simp only [r2Source, map_sub, map_add, map_zsmul]
  rw [hlead', zero_add]
  exact (cImageIdeal N i).sub_mem
    ((cImageIdeal N i).zsmul_mem 4 (cImage_mem_ideal N i 2))
    (cImage_mem_ideal N i 0)

private theorem probe_r3_mem_cImageIdeal (N : ℕ) (i : Fin 3) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega) (r3Source N) ∈
      cImageIdeal N i := by
  have hlead := sourceProbe_rowLead_eq_zero N i 2
  change MagnusMasks.sourceProbe N i (N + 3) (by omega)
      ((64 : ℤ) • x3Source N) = 0 at hlead
  have hlead' : (64 : ℤ) •
      MagnusMasks.sourceProbe N i (N + 3) (by omega) (x3Source N) = 0 := by
    simpa only [map_zsmul] using hlead
  simp only [r3Source, map_sub, map_zsmul]
  rw [hlead', zero_sub]
  exact (cImageIdeal N i).sub_mem
    ((cImageIdeal N i).neg_mem
      ((cImageIdeal N i).zsmul_mem 4 (cImage_mem_ideal N i 1)))
    ((cImageIdeal N i).zsmul_mem 2 (cImage_mem_ideal N i 0))

private theorem uSource_mem_lowerCentralSeries (N : ℕ) (j : Fin 3) :
    uSource N j ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 2) := by
  rw [uSource]
  have hrev : ⁅smallSourceGenerator N j, cSource N j⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 2) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp)
      (cSource_mem_lowerCentralSeries N j)
  rw [← lie_skew]
  exact (LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 2)).neg_mem hrev

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

private theorem sourceProbe_eq_zero_of_mem_top_lowerCentralSeries
    (N : ℕ) (i : Fin 3) {x : Source N}
    (hx : x ∈ LieModule.lowerCentralSeries ℤ
      (Source N) (Source N) (N + 2)) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega) x = 0 := by
  have hm : MagnusMasks.sourceProbe N i (N + 3) (by omega) x ∈
      LieModule.lowerCentralSeries ℤ
        (MagnusProbe.Target (MagnusMasks.modulus i) (N + 3))
        (MagnusProbe.Target (MagnusMasks.modulus i) (N + 3)) (N + 2) := by
    apply (LieIdeal.map_lowerCentralSeries_le
      (R := ℤ) (f := MagnusMasks.sourceProbe N i (N + 3) (by omega)) (N + 2))
    exact LieIdeal.mem_map hx
  have hbot := MagnusProbe.Target.lowerCentralSeries_eq_bot_of_le
    (MagnusMasks.modulus i) (N + 3) (n := N + 2) (by omega)
  rw [hbot] at hm
  simpa using hm

@[simp] theorem sourceProbe_uSource_eq_zero
    (N : ℕ) (i j : Fin 3) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega) (uSource N j) = 0 :=
  sourceProbe_eq_zero_of_mem_top_lowerCentralSeries N i
    (uSource_mem_lowerCentralSeries N j)

@[simp] theorem sourceProbe_topHallSource_eq_zero
    (N : ℕ) (i : Fin 3)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega) (topHallSource N h) = 0 :=
  sourceProbe_eq_zero_of_mem_top_lowerCentralSeries N i
    (topHallSource_mem_lowerCentralSeries N h)

/-- At truncation `N+3`, every defining relator has probe image in the
additive span of the three `c`-images.  This is the exact replacement for
the lower-truncation statement that every relator maps to zero. -/
theorem sourceProbe_mem_cImageIdeal_of_mem_definingRelators
    (N : ℕ) (i : Fin 3) {x : Source N} (hx : x ∈ definingRelators N) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega) x ∈ cImageIdeal N i := by
  simp only [definingRelators, Set.mem_union] at hx
  rcases hx with ((hshift | htop) | hex)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hshift
    rcases hshift with (rfl | rfl | rfl)
    · exact probe_r1_mem_cImageIdeal N i
    · exact probe_r2_mem_cImageIdeal N i
    · exact probe_r3_mem_cImageIdeal N i
  · rcases htop with ⟨h, -, rfl⟩
    rw [sourceProbe_topHallSource_eq_zero]
    exact (cImageIdeal N i).zero_mem
  · simp only [exceptionalRelators, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hex
    rcases hex with (rfl | rfl | rfl)
    · simp only [map_sub, map_zsmul, sourceProbe_uSource_eq_zero,
        smul_zero, sub_zero]
      exact (cImageIdeal N i).zero_mem
    · simp only [map_sub, map_zsmul, sourceProbe_uSource_eq_zero,
        smul_zero, sub_zero]
      exact (cImageIdeal N i).zero_mem
    · simp only [map_zsmul, sourceProbe_uSource_eq_zero, smul_zero]
      exact (cImageIdeal N i).zero_mem

theorem relationIdeal_le_ker_sourceQuotientProbe
    (N : ℕ) (i : Fin 3) :
    relationIdeal N ≤ LieHom.ker (sourceQuotientProbe N i) := by
  rw [relationIdeal, LieSubmodule.lieSpan_le]
  intro x hx
  change sourceQuotientProbe N i x = 0
  rw [sourceQuotientProbe_apply]
  change ringQuotientMap N i
      (MagnusMasks.sourceProbe N i (N + 3) (by omega) x) =
    (0 : QuotientRing N i)
  rw [ringQuotientMap_eq_zero_iff]
  exact sourceProbe_mem_cImageIdeal_of_mem_definingRelators N i hx

/-- The top-minus-one probe descended through the exact presentation of
`L N`. -/
def quotientProbe (N : ℕ) (i : Fin 3) :
    L N →ₗ⁅ℤ⁆ QuotientTarget N i where
  toLinearMap := (relationIdeal N).toSubmodule.liftQ
    (sourceQuotientProbe N i).toLinearMap (by
      intro x hx
      exact relationIdeal_le_ker_sourceQuotientProbe N i hx)
  map_lie' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        rw [← LieSubmodule.Quotient.mk_bracket]
        exact LieHom.map_lie (sourceQuotientProbe N i) x y

@[simp] theorem quotientProbe_quotientMap
    (N : ℕ) (i : Fin 3) (x : Source N) :
    quotientProbe N i (quotientMap N x) = sourceQuotientProbe N i x := by
  change (relationIdeal N).toSubmodule.liftQ
    (sourceQuotientProbe N i).toLinearMap _
      (LieSubmodule.Quotient.mk x) = _
  exact Submodule.liftQ_apply _ _ x

/-! ## Nilpotence of the quotient probe -/

section QuotientNilpotence

-- The nested ring-congruence quotient and unitization instances are
-- definitionally large; this budget affects deterministic synthesis only.
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

/-- Unitization of the quotient map.  It is written explicitly because the
source and target rings are nonunital. -/
def unitizationQuotientMap (N : ℕ) (i : Fin 3) :
    Unitization ℤ (ProbeRing N i) →+*
      Unitization ℤ (QuotientRing N i) where
  toFun x := ⟨x.fst, ringQuotientMap N i x.snd⟩
  map_zero' := by
    apply Unitization.ext <;> rfl
  map_one' := by
    apply Unitization.ext <;> rfl
  map_add' x y := by
    apply Unitization.ext
    · rfl
    · exact map_add (ringQuotientMap N i) x.snd y.snd
  map_mul' x y := by
    apply Unitization.ext
    · rfl
    · change ringQuotientMap N i
          (x.fst • y.snd + y.fst • x.snd + x.snd * y.snd) =
        x.fst • ringQuotientMap N i y.snd +
          y.fst • ringQuotientMap N i x.snd +
          ringQuotientMap N i x.snd * ringQuotientMap N i y.snd
      simp

theorem ringQuotientMap_surjective (N : ℕ) (i : Fin 3) :
    Function.Surjective (ringQuotientMap N i) := by
  intro x
  obtain ⟨y, hy⟩ := Quotient.mk''_surjective x
  exact ⟨y, hy⟩

theorem unitizationQuotientMap_surjective (N : ℕ) (i : Fin 3) :
    Function.Surjective (unitizationQuotientMap N i) := by
  intro x
  obtain ⟨y, hy⟩ := ringQuotientMap_surjective N i x.snd
  refine ⟨⟨x.fst, y⟩, ?_⟩
  apply Unitization.ext
  · rfl
  · exact hy

private theorem map_unitizationIdeal
    (N : ℕ) (i : Fin 3) :
    Ideal.map (unitizationQuotientMap N i)
        (unitizationIdeal (R := ProbeRing N i)) =
      unitizationIdeal (R := QuotientRing N i) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_unitizationIdeal_iff]
    change x.fst = 0
    exact (mem_unitizationIdeal_iff x).mp hx
  · intro x hx
    rw [Ideal.mem_map_iff_of_surjective _
      (unitizationQuotientMap_surjective N i)]
    obtain ⟨y, hy⟩ := ringQuotientMap_surjective N i x.snd
    let y' : Unitization ℤ (ProbeRing N i) := ⟨0, y⟩
    refine ⟨y', ?_, ?_⟩
    · rw [mem_unitizationIdeal_iff]
    · apply Unitization.ext
      · change 0 = x.fst
        exact ((mem_unitizationIdeal_iff x).mp hx).symm
      · exact hy

private theorem ideal_pow_le_map_pow_of_surjective
    {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) [I.IsTwoSided] [(Ideal.map f I).IsTwoSided] (n : ℕ) :
    (Ideal.map f I) ^ n ≤ Ideal.map f (I ^ n) := by
  induction n with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top,
        Submodule.pow_zero, Ideal.one_eq_top, Ideal.map_top]
  | succ n ih =>
      rw [Ideal.IsTwoSided.pow_succ, Ideal.IsTwoSided.pow_succ]
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        rw [Ideal.mem_map_iff_of_surjective f hf] at ha
        have hb' := ih hb
        rw [Ideal.mem_map_iff_of_surjective f hf] at hb'
        obtain ⟨a', ha'I, ha'eq⟩ := ha
        obtain ⟨b', hb'I, hb'eq⟩ := hb'
        rw [← ha'eq, ← hb'eq, ← map_mul]
        apply Ideal.mem_map_of_mem f
        exact Ideal.mul_mem_mul ha'I hb'I
      · intro x y hx hy
        exact (Ideal.map f (I * I ^ n)).add_mem hx hy

/-- Quotienting by the annihilator `c`-span preserves the critical
nilpotence bound for the nonunital Magnus ring. -/
theorem quotient_unitizationIdeal_pow_eq_bot
    (N : ℕ) (i : Fin 3) :
    unitizationIdeal (R := QuotientRing N i) ^ (N + 4) = ⊥ := by
  letI : (Ideal.map (unitizationQuotientMap N i)
      (unitizationIdeal (R := ProbeRing N i))).IsTwoSided := by
    rw [map_unitizationIdeal N i]
    infer_instance
  rw [eq_bot_iff, ← map_unitizationIdeal N i]
  refine (ideal_pow_le_map_pow_of_surjective
    (unitizationQuotientMap N i) (unitizationQuotientMap_surjective N i)
    (unitizationIdeal (R := ProbeRing N i)) (N + 4)).trans ?_
  rw [MagnusProbe.unitizationIdeal_pow_eq_bot
      (MagnusMasks.modulus i) (N + 3) (N + 4) (by omega) (by omega),
    Ideal.map_bot]

/-- Every critical dimension element vanishes in the descended
top-minus-one quotient probe. -/
theorem quotientProbe_eq_zero_of_mem_dimensionSubring
    (N : ℕ) (i : Fin 3) {z : L N}
    (hz : z ∈ dimensionSubring ℤ (L N) (N + 4)) :
    quotientProbe N i z = 0 := by
  let rho : L N →ₗ⁅ℤ⁆ Unitization ℤ (QuotientRing N i) :=
    nonUnitalCommutatorToUnitization.comp (quotientProbe N i)
  have hzero : rho z = 0 :=
    lieHom_eq_zero_of_mem_dimensionSubring_of_ideal_pow_eq_bot rho
      unitizationIdeal
      (fun y ↦ nonUnitalCommutatorToUnitization_mem (quotientProbe N i y))
      (N + 4) (quotient_unitizationIdeal_pow_eq_bot N i) hz
  change (show QuotientRing N i from quotientProbe N i z) = 0
  apply Unitization.inr_injective (R := ℤ) (A := QuotientRing N i)
  simpa [rho] using hzero

/-- In source coordinates, a lift of a critical dimension element has
masked Magnus image in the additive span of the three `c`-images. -/
theorem sourceProbe_mem_cImageIdeal_of_quotient_dimensionSubring
    (N : ℕ) (i : Fin 3) {x : Source N}
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4)) :
    MagnusMasks.sourceProbe N i (N + 3) (by omega) x ∈
      cImageIdeal N i := by
  have hzero := quotientProbe_eq_zero_of_mem_dimensionSubring N i hx
  rw [quotientProbe_quotientMap, sourceQuotientProbe_apply] at hzero
  change ringQuotientMap N i
      (MagnusMasks.sourceProbe N i (N + 3) (by omega) x) =
    (0 : QuotientRing N i) at hzero
  exact (ringQuotientMap_eq_zero_iff N i _).mp hzero

/-- An additive read which kills the three distinguished `c`-images kills
their entire additive span. -/
theorem addHom_eq_zero_of_mem_cImageIdeal
    (N : ℕ) (i : Fin 3) {A : Type*} [AddCommGroup A]
    (f : ProbeRing N i →+ A) (hf : ∀ j : Fin 3, f (cImage N i j) = 0)
    {x : ProbeRing N i} (hx : x ∈ cImageIdeal N i) : f x = 0 := by
  rw [mem_cImageIdeal_iff] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hf j
  | zero => exact f.map_zero
  | add x y hx hy ihx ihy => rw [f.map_add, ihx, ihy, add_zero]
  | neg x hx ih => rw [f.map_neg, ih, neg_zero]

/-- Read-only form of the top-minus-one obstruction: every additive
functional vanishing on the three `c`-images vanishes on a lift of a
critical dimension element. -/
theorem sourceProbe_read_eq_zero_of_quotient_dimensionSubring
    (N : ℕ) (i : Fin 3) {A : Type*} [AddCommGroup A]
    (f : ProbeRing N i →+ A) (hf : ∀ j : Fin 3, f (cImage N i j) = 0)
    {x : Source N}
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4)) :
    f (MagnusMasks.sourceProbe N i (N + 3) (by omega) x) = 0 :=
  addHom_eq_zero_of_mem_cImageIdeal N i f hf
    (sourceProbe_mem_cImageIdeal_of_quotient_dimensionSubring N i hx)

private theorem hallRead_cImage_eq_zero_of_not_cSource
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3)
    (h : FreeMetabelian.HallIndex Generator N)
    (hc : ∀ j : Fin 3,
      FreeMetabelian.Evaluation.hallBracket generatorBasis N h (by omega) ≠
        cSource N j) (j : Fin 3) :
    MagnusCoordinates.hallRead (MagnusMasks.modulus i) (N + 3) N h (by omega)
        (cImage N i j) = 0 := by
  rw [cImage, ← hallBracket_cHallIndex_eq_cSource N hN j]
  by_cases hj : MagnusMasks.HallSurvives i N (cHallIndex N hN j)
  · rw [MagnusMasks.sourceProbe_hallBracket_eq_unmasked
        N i (N + 3) (by omega) N (cHallIndex N hN j) (by omega) hj,
      MagnusCoordinates.hallRead_sourceProbe_hallBracket]
    rw [if_neg]
    intro heq
    apply hc j
    rw [heq, hallBracket_cHallIndex_eq_cSource N hN j]
  · rw [MagnusCoordinateReads.maskedSourceProbe_hallBracket_eq_zero_of_not_survives
        N i (N + 3) (by omega) N (cHallIndex N hN j) (by omega) hj,
      map_zero]

private theorem hallSign_eq_one_or_neg_one (s : ℕ) :
    MagnusProbe.hallSign s = 1 ∨ MagnusProbe.hallSign s = -1 := by
  induction s with
  | zero => exact Or.inl rfl
  | succ s ih =>
      rw [MagnusProbe.hallSign_succ]
      rcases ih with h | h
      · exact Or.inr (by simp [h])
      · exact Or.inl (by simp [h])

/-- **Exact top-minus-one Hall congruence.**  A surviving Hall word of
weight `N+2` which is not one of the three retained `c_j` has its literal
source coordinate divisible by the modulus of the chosen mask. -/
theorem modulus_dvd_hallCoordinate_topMinusOne
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3)
    (h : FreeMetabelian.HallIndex Generator N)
    (ha : MagnusMasks.HallSurvives i N h)
    (hc : ∀ j : Fin 3,
      FreeMetabelian.Evaluation.hallBracket generatorBasis N h (by omega) ≠
        cSource N j)
    {x : Source N}
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4)) :
    (MagnusMasks.modulus i : ℤ) ∣
      gradedCoordinate N
        (MagnusCoordinateReads.hallIndex N N h (by omega)) x := by
  let read := MagnusCoordinates.hallRead
    (MagnusMasks.modulus i) (N + 3) N h (by omega)
  have hread : read (MagnusMasks.sourceProbe N i (N + 3) (by omega) x) = 0 :=
    sourceProbe_read_eq_zero_of_quotient_dimensionSubring N i read
      (hallRead_cImage_eq_zero_of_not_cSource N hN i h hc) hx
  rw [MagnusCoordinateReads.hallRead_maskedSourceProbe
    N i (N + 3) N (by omega) h (by omega) (by omega) ha x] at hread
  have hcoord :
      ((gradedCoordinate N
        (MagnusCoordinateReads.hallIndex N N h (by omega)) x : ℤ) :
          ZMod (MagnusMasks.modulus i)) = 0 := by
    rcases hallSign_eq_one_or_neg_one N with hs | hs
    · simpa [hs] using hread
    · simpa [hs] using hread
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcoord

end QuotientNilpotence

end TopMinusOneMagnus

end

end LieRings.FinitePlateau
