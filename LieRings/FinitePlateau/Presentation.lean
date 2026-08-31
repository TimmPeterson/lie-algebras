import LieRings.Metabelian.FreeEvaluation
import LieRings.UniversalEnveloping.Quotient

/-!
# The finite-plateau presentation

This file defines the Lie ring `L_N` used in the finite-plateau construction.
The relatively free source is the explicit truncated free metabelian Lie ring
on five ordered generators

`x₅ < x₁ < x₂ < x₃ < x₄`.

The truncation already imposes `γ_(N+4) = 0`.  The remaining relation ideal
contains exactly the three shifted relations, all nonexceptional Hall
generators in weight `N+3`, and the three displayed relations between the
exceptional generators.  We prove below that the off-diagonal brackets
`[c_i,x_j]`, `i ≠ j`, are among those nonexceptional Hall generators.
-/

namespace LieRings.FinitePlateau

noncomputable section

open FreeMetabelian

/-! ## The ordered generators and the relatively free source -/

/-- Indices for the five generators.  Their numerical order is the manuscript
order `x₅ < x₁ < x₂ < x₃ < x₄`. -/
abbrev Generator := Fin 5

/-- The free integral module on the five ordered generators. -/
abbrev GeneratorModule := Generator →₀ ℤ

/-- The standard basis, indexed in the manuscript order. -/
def generatorBasis : Module.Basis Generator ℤ GeneratorModule :=
  Finsupp.basisSingleOne

/-- The class-`N+3` free metabelian source of the presentation. -/
abbrev Source (N : ℕ) := FreeMetabelian.Free GeneratorModule (N + 3)

/-- A weight-one generator in the free metabelian source. -/
def sourceGenerator (N : ℕ) (i : Generator) : Source N :=
  FreeMetabelian.Free.weightIncl 0 (by omega) (generatorBasis i)

/-- The first three generators `x₁,x₂,x₃`. -/
def smallSourceGenerator (N : ℕ) (i : Fin 3) : Source N :=
  sourceGenerator N ⟨i.val + 1, by omega⟩

def x5Source (N : ℕ) : Source N := sourceGenerator N 0
def x1Source (N : ℕ) : Source N := sourceGenerator N 1
def x2Source (N : ℕ) : Source N := sourceGenerator N 2
def x3Source (N : ℕ) : Source N := sourceGenerator N 3
def x4Source (N : ℕ) : Source N := sourceGenerator N 4

@[simp] theorem smallSourceGenerator_zero (N : ℕ) :
    smallSourceGenerator N 0 = x1Source N := rfl

@[simp] theorem smallSourceGenerator_one (N : ℕ) :
    smallSourceGenerator N 1 = x2Source N := rfl

@[simp] theorem smallSourceGenerator_two (N : ℕ) :
    smallSourceGenerator N 2 = x3Source N := rfl

/-! ## The distinguished commutators and shifted relations -/

/-- `rightBracketPow x y n = [x,y,...,y]`, with `n` copies of `y`. -/
def rightBracketPow {A : Type*} [LieRing A] (x y : A) : ℕ → A
  | 0 => x
  | n + 1 => ⁅rightBracketPow x y n, y⁆

@[simp] theorem rightBracketPow_zero {A : Type*} [LieRing A] (x y : A) :
    rightBracketPow x y 0 = x := rfl

@[simp] theorem rightBracketPow_succ {A : Type*} [LieRing A]
    (x y : A) (n : ℕ) :
    rightBracketPow x y (n + 1) = ⁅rightBracketPow x y n, y⁆ := rfl

/-- The manuscript element `t=[x₄,x₅,...,x₅]`. -/
def tSource (N : ℕ) : Source N :=
  rightBracketPow (x4Source N) (x5Source N) N

/-- `c_i=[t,x_i]`, for `i=1,2,3` (represented by `Fin 3`). -/
def cSource (N : ℕ) (i : Fin 3) : Source N :=
  ⁅tSource N, smallSourceGenerator N i⁆

/-- `u_i=[c_i,x_i]`, for `i=1,2,3` (represented by `Fin 3`). -/
def uSource (N : ℕ) (i : Fin 3) : Source N :=
  ⁅cSource N i, smallSourceGenerator N i⁆

abbrev c1Source (N : ℕ) := cSource N 0
abbrev c2Source (N : ℕ) := cSource N 1
abbrev c3Source (N : ℕ) := cSource N 2
abbrev u1Source (N : ℕ) := uSource N 0
abbrev u2Source (N : ℕ) := uSource N 1
abbrev u3Source (N : ℕ) := uSource N 2

/-- The first shifted relation `4x₁+2c₃+c₂`. -/
def r1Source (N : ℕ) : Source N :=
  (4 : ℤ) • x1Source N + (2 : ℤ) • c3Source N + c2Source N

/-- The second shifted relation `16x₂+4c₃-c₁`. -/
def r2Source (N : ℕ) : Source N :=
  (16 : ℤ) • x2Source N + (4 : ℤ) • c3Source N - c1Source N

/-- The third shifted relation `64x₃-4c₂-2c₁`. -/
def r3Source (N : ℕ) : Source N :=
  (64 : ℤ) • x3Source N - (4 : ℤ) • c2Source N -
    (2 : ℤ) • c1Source N

def b12Source (N : ℕ) : Source N := ⁅x1Source N, x2Source N⁆
def b13Source (N : ℕ) : Source N := ⁅x1Source N, x3Source N⁆
def b23Source (N : ℕ) : Source N := ⁅x2Source N, x3Source N⁆

/-- The exceptional element used throughout the construction. -/
def aSource (N : ℕ) : Source N :=
  (32 : ℤ) • b12Source N + (64 : ℤ) • b13Source N +
    (128 : ℤ) • b23Source N

/-! ## The defining ideal -/

/-- The generator index `1,2,3` corresponding to `i : Fin 3`. -/
def smallGeneratorIndex (i : Fin 3) : Generator := ⟨i.val + 1, by omega⟩

/-- The symmetric teeth of `[c_i,x_j]`: after the initial pair
`[x₄,x₅]`, there are `N-1` further copies of `x₅`, followed by `x_i`
and `x_j`. -/
def topBracketTeeth (N : ℕ) (hN : 1 ≤ N) (i j : Fin 3) :
    Sym Generator (N + 1) :=
  Sym.mk
    (Multiset.replicate (N - 1) (0 : Generator) +
      ({smallGeneratorIndex i, smallGeneratorIndex j} : Multiset Generator))
    (by simp; omega)

/-- The Hall index of the top bracket `[c_i,x_j]`. -/
def topBracketHallIndex (N : ℕ) (hN : 1 ≤ N) (i j : Fin 3) :
    FreeMetabelian.HallIndex Generator (N + 1) where
  head := 4
  pivot := 0
  teeth := topBracketTeeth N hN i j
  pivot_lt_head := by decide
  pivot_le_teeth := fun k _ ↦ Fin.zero_le k

/-- The retained diagonal Hall index `u_i`. -/
def uHallIndex (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) :
    FreeMetabelian.HallIndex Generator (N + 1) :=
  topBracketHallIndex N hN i i

/-- A Hall generator in the top manuscript weight `N+3`. -/
def topHallSource (N : ℕ) (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    Source N :=
  FreeMetabelian.Free.inclComponent (N + 1) (by omega)
    (FreeMetabelian.hallBasis generatorBasis (N + 1) h)

/-- The three top Hall generators retained by the presentation. -/
def IsExceptionalTop (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) : Prop :=
  topHallSource N h = u1Source N ∨
    topHallSource N h = u2Source N ∨
    topHallSource N h = u3Source N

/-- Relation (iii): every nonexceptional Hall generator in weight `N+3`. -/
def topHallRelators (N : ℕ) : Set (Source N) :=
  {z | ∃ h : FreeMetabelian.HallIndex Generator (N + 1),
    ¬ IsExceptionalTop N h ∧ z = topHallSource N h}

/-- The off-diagonal top brackets used in the six elementary relation
computations.  These are the corresponding particular members of relation
(iii), listed explicitly in the presentation interface. -/
def offDiagonalTopRelators (N : ℕ) : Set (Source N) :=
  {z | ∃ i j : Fin 3, i ≠ j ∧
    z = ⁅cSource N i, smallSourceGenerator N j⁆}

/-! ### Identification of the off-diagonal Hall generators -/

private theorem hallIndex_ext {q : ℕ}
    {a b : FreeMetabelian.HallIndex Generator q}
    (hh : a.head = b.head) (hp : a.pivot = b.pivot)
    (ht : a.teeth = b.teeth) : a = b := by
  cases a
  cases b
  simp only at hh hp ht
  subst_vars
  rfl

private theorem topBracketHallIndex_nextTooth (N : ℕ) (hN : 1 ≤ N)
    (i j : Fin 3) :
    (topBracketHallIndex (N + 1) (by omega) i j).nextTooth = 0 := by
  simp only [FreeMetabelian.HallIndex.nextTooth, topBracketHallIndex,
    topBracketTeeth]
  change ((Multiset.replicate N (0 : Generator) +
    ({smallGeneratorIndex i, smallGeneratorIndex j} :
      Multiset Generator)).toFinset.min' _) = 0
  rw [Finset.min'_eq_iff]
  constructor
  · have hN0 : N ≠ 0 := by omega
    simp [hN0]
  · intro b _
    exact Fin.zero_le b

private theorem topBracketHallIndex_predecessor (N : ℕ) (hN : 1 ≤ N)
    (i j : Fin 3) :
    (topBracketHallIndex (N + 1) (by omega) i j).predecessor =
      topBracketHallIndex N hN i j := by
  refine hallIndex_ext
    (a := (topBracketHallIndex (N + 1) (by omega) i j).predecessor)
    (b := topBracketHallIndex N hN i j) rfl rfl ?_
  apply Sym.ext
  simp only [FreeMetabelian.HallIndex.predecessor, topBracketHallIndex,
    topBracketTeeth]
  change Multiset.erase
        (Multiset.replicate N (0 : Generator) +
          ({smallGeneratorIndex i, smallGeneratorIndex j} : Multiset Generator))
        ((Multiset.replicate N (0 : Generator) +
          ({smallGeneratorIndex i, smallGeneratorIndex j} :
            Multiset Generator)).toFinset.min' _) =
      Multiset.replicate (N - 1) (0 : Generator) +
        ({smallGeneratorIndex i, smallGeneratorIndex j} : Multiset Generator)
  rw [show ((Multiset.replicate N (0 : Generator) +
        ({smallGeneratorIndex i, smallGeneratorIndex j} :
          Multiset Generator)).toFinset.min' _) = 0 by
    rw [Finset.min'_eq_iff]
    constructor
    · have hN0 : N ≠ 0 := by omega
      simp [hN0]
    · intro b _
      exact Fin.zero_le b]
  cases N with
  | zero => omega
  | succ n =>
      have hi : smallGeneratorIndex i ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp [smallGeneratorIndex] at this
      simp [Multiset.replicate_succ, hi]

private theorem bracket_mem_derived {N : ℕ} (x y : Source N) :
    ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ (Source N) 1 := by
  change ⁅x, y⁆ ∈ ⁅(⊤ : LieIdeal ℤ (Source N)),
    (⊤ : LieIdeal ℤ (Source N))⁆
  exact LieSubmodule.lie_mem_lie (by simp) (by simp)

/-- Right adjoint actions commute on a derived element of the metabelian
source. -/
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

private theorem base_nextTooth (i j : Fin 3) :
    (topBracketHallIndex 1 (by omega) i j).nextTooth =
      min (smallGeneratorIndex i) (smallGeneratorIndex j) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem base_predecessor_nextTooth (i j : Fin 3) :
    (topBracketHallIndex 1 (by omega) i j).predecessor.nextTooth =
      max (smallGeneratorIndex i) (smallGeneratorIndex j) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem embedded_top_hall_base
    (N : ℕ) (hN : 1 ≤ N) (i j : Fin 3) :
    FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis 2
        (topBracketHallIndex 1 (by omega) i j) (by omega) =
      ⁅⁅⁅x4Source N, x5Source N⁆, smallSourceGenerator N i⁆,
        smallSourceGenerator N j⁆ := by
  rw [FreeMetabelian.Evaluation.hallBracket,
    FreeMetabelian.Evaluation.hallBracket,
    FreeMetabelian.Evaluation.hallBracket]
  rw [base_nextTooth, base_predecessor_nextTooth]
  change ⁅⁅⁅x4Source N, x5Source N⁆,
      sourceGenerator N (max (smallGeneratorIndex i) (smallGeneratorIndex j))⁆,
      sourceGenerator N (min (smallGeneratorIndex i) (smallGeneratorIndex j))⁆ = _
  fin_cases i <;> fin_cases j
  case «0».«0» => rfl
  case «0».«1» =>
    change ⁅⁅⁅x4Source N, x5Source N⁆, sourceGenerator N 2⁆,
      sourceGenerator N 1⁆ =
      ⁅⁅⁅x4Source N, x5Source N⁆, sourceGenerator N 1⁆,
        sourceGenerator N 2⁆
    exact source_right_actions_commute
      (bracket_mem_derived (x4Source N) (x5Source N))
  case «0».«2» =>
    change ⁅⁅⁅x4Source N, x5Source N⁆, sourceGenerator N 3⁆,
      sourceGenerator N 1⁆ =
      ⁅⁅⁅x4Source N, x5Source N⁆, sourceGenerator N 1⁆,
        sourceGenerator N 3⁆
    exact source_right_actions_commute
      (bracket_mem_derived (x4Source N) (x5Source N))
  case «1».«0» => rfl
  case «1».«1» => rfl
  case «1».«2» =>
    change ⁅⁅⁅x4Source N, x5Source N⁆, sourceGenerator N 3⁆,
      sourceGenerator N 2⁆ =
      ⁅⁅⁅x4Source N, x5Source N⁆, sourceGenerator N 2⁆,
        sourceGenerator N 3⁆
    exact source_right_actions_commute
      (bracket_mem_derived (x4Source N) (x5Source N))
  case «2».«0» => rfl
  case «2».«1» => rfl
  case «2».«2» => rfl

private theorem embedded_top_hall_succ
    (N r : ℕ) (hr : 1 ≤ r) (hrN : r < N) (i j : Fin 3) :
    FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis (r + 2)
        (topBracketHallIndex (r + 1) (by omega) i j) (by omega) =
      ⁅FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis
          (r + 1) (topBracketHallIndex r hr i j) (by omega), x5Source N⁆ := by
  rw [FreeMetabelian.Evaluation.hallBracket,
    topBracketHallIndex_predecessor r hr,
    topBracketHallIndex_nextTooth r hr]
  rfl

private theorem literal_top_bracket_succ
    (N r : ℕ) (hr : 1 ≤ r) (i j : Fin 3) :
    ⁅⁅rightBracketPow (x4Source N) (x5Source N) (r + 1),
          smallSourceGenerator N i⁆, smallSourceGenerator N j⁆ =
      ⁅⁅⁅rightBracketPow (x4Source N) (x5Source N) r,
          smallSourceGenerator N i⁆, smallSourceGenerator N j⁆,
        x5Source N⁆ := by
  rw [rightBracketPow_succ]
  rw [source_right_actions_commute (rightBracketPow_mem_derived N r hr)]
  rw [source_right_actions_commute
    (bracket_mem_derived
      (rightBracketPow (x4Source N) (x5Source N) r)
      (smallSourceGenerator N i))]

private theorem embedded_top_hall_eq_bracket
    (N r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) (i j : Fin 3) :
    FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis (r + 1)
        (topBracketHallIndex r hr i j) (by omega) =
      ⁅⁅rightBracketPow (x4Source N) (x5Source N) r,
          smallSourceGenerator N i⁆, smallSourceGenerator N j⁆ := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        exact embedded_top_hall_base N (by omega) i j
      · have hr1 : 1 ≤ r := by omega
        rw [embedded_top_hall_succ N r hr1 (by omega) i j,
          ih hr1 (by omega)]
        exact (literal_top_bracket_succ N r hr1 i j).symm

/-- The Hall generator with teeth prescribed by `i,j` is the literal
manuscript bracket `[c_i,x_j]`. -/
theorem topHallSource_topBracketHallIndex_eq (N : ℕ) (hN : 1 ≤ N)
    (i j : Fin 3) :
    topHallSource N (topBracketHallIndex N hN i j) =
      ⁅cSource N i, smallSourceGenerator N j⁆ := by
  rw [topHallSource, FreeMetabelian.hallBasis_apply]
  change FreeMetabelian.Free.incl (⟨N + 2, by omega⟩ : Fin (N + 3))
      (FreeMetabelian.hallVector generatorBasis (N + 1)
        (topBracketHallIndex N hN i j)) = _
  rw [← FreeMetabelian.Evaluation.hallBracket_eq_incl]
  exact embedded_top_hall_eq_bracket N N hN (by omega) i j

/-- Each retained `u_i` is represented by the explicitly exposed diagonal
top Hall index. -/
@[simp] theorem topHallSource_uHallIndex_eq (N : ℕ) (hN : 1 ≤ N)
    (i : Fin 3) :
    topHallSource N (uHallIndex N hN i) = uSource N i := by
  exact topHallSource_topBracketHallIndex_eq N hN i i

private theorem topHallSource_injective (N : ℕ) :
    Function.Injective (topHallSource N) := by
  intro h k heq
  have hc := congrArg
    (fun z : Source N => z (⟨N + 1 + 1, by omega⟩ : Fin (N + 3))) heq
  have hb : FreeMetabelian.hallBasis generatorBasis (N + 1) h =
      FreeMetabelian.hallBasis generatorBasis (N + 1) k := by
    simp only [topHallSource, FreeMetabelian.Free.inclComponent,
      FreeMetabelian.hallBasis_apply, LinearMap.comp_apply] at hc
    change (FreeMetabelian.Free.incl (⟨N + 1 + 1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallVector generatorBasis (N + 1) h))
          ⟨N + 1 + 1, by omega⟩ =
      (FreeMetabelian.Free.incl (⟨N + 1 + 1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallVector generatorBasis (N + 1) k))
          ⟨N + 1 + 1, by omega⟩ at hc
    have hv : FreeMetabelian.hallVector generatorBasis (N + 1) h =
        FreeMetabelian.hallVector generatorBasis (N + 1) k := by
      simpa [FreeMetabelian.Free.incl] using hc
    simpa only [FreeMetabelian.hallBasis_apply] using hv
  exact (FreeMetabelian.hallBasis generatorBasis (N + 1)).injective hb

private theorem topBracketHallIndex_ne_uHallIndex
    (N : ℕ) (hN : 1 ≤ N) {i j : Fin 3} (hij : i ≠ j) (k : Fin 3) :
    topBracketHallIndex N hN i j ≠ uHallIndex N hN k := by
  intro heq
  have ht := congrArg
    (fun h : FreeMetabelian.HallIndex Generator (N + 1) =>
      (h.teeth : Multiset Generator)) heq
  simp only [topBracketHallIndex, uHallIndex, topBracketTeeth] at ht
  have hc := congrArg (Multiset.count (smallGeneratorIndex i)) ht
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [smallGeneratorIndex] at hij hc

theorem topBracketHallIndex_not_exceptional
    (N : ℕ) (hN : 1 ≤ N) {i j : Fin 3} (hij : i ≠ j) :
    ¬ IsExceptionalTop N (topBracketHallIndex N hN i j) := by
  intro hex
  rcases hex with h0 | h1 | h2
  · exact topBracketHallIndex_ne_uHallIndex N hN hij 0
      (topHallSource_injective N
        (h0.trans (topHallSource_uHallIndex_eq N hN 0).symm))
  · exact topBracketHallIndex_ne_uHallIndex N hN hij 1
      (topHallSource_injective N
        (h1.trans (topHallSource_uHallIndex_eq N hN 1).symm))
  · exact topBracketHallIndex_ne_uHallIndex N hN hij 2
      (topHallSource_injective N
        (h2.trans (topHallSource_uHallIndex_eq N hN 2).symm))

/-- The explicitly named off-diagonal brackets are not extra relations:
they are a subset of relation (iii). -/
theorem offDiagonalTopRelators_subset_topHallRelators
    (N : ℕ) (hN : 1 ≤ N) :
    offDiagonalTopRelators N ⊆ topHallRelators N := by
  rintro z ⟨i, j, hij, rfl⟩
  exact ⟨topBracketHallIndex N hN i j,
    topBracketHallIndex_not_exceptional N hN hij,
    (topHallSource_topBracketHallIndex_eq N hN i j).symm⟩

/-- Relations (iv) in the top weight. -/
def exceptionalRelators (N : ℕ) : Set (Source N) :=
  {u1Source N - (16 : ℤ) • u3Source N,
    u2Source N - (4 : ℤ) • u3Source N,
    (64 : ℤ) • u3Source N}

/-- All defining relations, except for the nilpotency cutoff already built
into `Source N`. -/
def definingRelators (N : ℕ) : Set (Source N) :=
  {r1Source N, r2Source N, r3Source N} ∪
    topHallRelators N ∪ exceptionalRelators N

/-- The Lie ideal generated by the defining relations. -/
def relationIdeal (N : ℕ) : LieIdeal ℤ (Source N) :=
  LieSubmodule.lieSpan ℤ (Source N) (definingRelators N)

/-- The finite-plateau Lie ring `L_N`. -/
abbrev L (N : ℕ) := Source N ⧸ relationIdeal N

/-- The presentation map from the relatively free source to `L_N`. -/
def quotientMap (N : ℕ) : LieHom ℤ (Source N) (L N) :=
  UEA.lieIdealQuotientMk ℤ (Source N) (relationIdeal N)

theorem quotientMap_surjective (N : ℕ) : Function.Surjective (quotientMap N) :=
  LieSubmodule.Quotient.surjective_mk' (relationIdeal N)

theorem mem_relationIdeal_of_mem_definingRelators {N : ℕ} {z : Source N}
    (hz : z ∈ definingRelators N) : z ∈ relationIdeal N :=
  LieSubmodule.subset_lieSpan hz

@[simp] theorem quotientMap_eq_zero_of_mem_definingRelators
    {N : ℕ} {z : Source N} (hz : z ∈ definingRelators N) :
    quotientMap N z = 0 := by
  apply (LieSubmodule.Quotient.mk_eq_zero' (N := relationIdeal N)).mpr
  exact mem_relationIdeal_of_mem_definingRelators hz

/-! ## Named elements in the quotient -/

def x5 (N : ℕ) : L N := quotientMap N (x5Source N)
def x1 (N : ℕ) : L N := quotientMap N (x1Source N)
def x2 (N : ℕ) : L N := quotientMap N (x2Source N)
def x3 (N : ℕ) : L N := quotientMap N (x3Source N)
def x4 (N : ℕ) : L N := quotientMap N (x4Source N)
def smallGenerator (N : ℕ) (i : Fin 3) : L N :=
  quotientMap N (smallSourceGenerator N i)
def t (N : ℕ) : L N := quotientMap N (tSource N)
def c (N : ℕ) (i : Fin 3) : L N := quotientMap N (cSource N i)
def u (N : ℕ) (i : Fin 3) : L N := quotientMap N (uSource N i)
abbrev c1 (N : ℕ) := c N 0
abbrev c2 (N : ℕ) := c N 1
abbrev c3 (N : ℕ) := c N 2
abbrev u1 (N : ℕ) := u N 0
abbrev u2 (N : ℕ) := u N 1
abbrev u3 (N : ℕ) := u N 2
def b12 (N : ℕ) : L N := quotientMap N (b12Source N)
def b13 (N : ℕ) : L N := quotientMap N (b13Source N)
def b23 (N : ℕ) : L N := quotientMap N (b23Source N)
def a (N : ℕ) : L N := quotientMap N (aSource N)

/-- The cyclic exceptional ideal generated by the manuscript element `a`.
The critical calculation identifies this ideal with `δ_(N+4)(L_N)`. -/
def exceptionalIdeal (N : ℕ) : LieIdeal ℤ (L N) :=
  LieSubmodule.lieSpan ℤ (L N) {a N}

@[simp] theorem smallGenerator_zero (N : ℕ) : smallGenerator N 0 = x1 N := rfl
@[simp] theorem smallGenerator_one (N : ℕ) : smallGenerator N 1 = x2 N := rfl
@[simp] theorem smallGenerator_two (N : ℕ) : smallGenerator N 2 = x3 N := rfl

@[simp] theorem map_tSource (N : ℕ) : quotientMap N (tSource N) = t N := rfl
@[simp] theorem map_x1Source (N : ℕ) : quotientMap N (x1Source N) = x1 N := rfl
@[simp] theorem map_x2Source (N : ℕ) : quotientMap N (x2Source N) = x2 N := rfl
@[simp] theorem map_x3Source (N : ℕ) : quotientMap N (x3Source N) = x3 N := rfl
@[simp] theorem map_x4Source (N : ℕ) : quotientMap N (x4Source N) = x4 N := rfl
@[simp] theorem map_x5Source (N : ℕ) : quotientMap N (x5Source N) = x5 N := rfl
@[simp] theorem map_smallSourceGenerator (N : ℕ) (i : Fin 3) :
    quotientMap N (smallSourceGenerator N i) = smallGenerator N i := rfl
@[simp] theorem map_cSource (N : ℕ) (i : Fin 3) :
    quotientMap N (cSource N i) = c N i := rfl
@[simp] theorem map_uSource (N : ℕ) (i : Fin 3) :
    quotientMap N (uSource N i) = u N i := rfl
@[simp] theorem map_b12Source (N : ℕ) : quotientMap N (b12Source N) = b12 N := rfl
@[simp] theorem map_b13Source (N : ℕ) : quotientMap N (b13Source N) = b13 N := rfl
@[simp] theorem map_b23Source (N : ℕ) : quotientMap N (b23Source N) = b23 N := rfl
@[simp] theorem map_aSource (N : ℕ) : quotientMap N (aSource N) = a N := rfl

/-! ## Direct structural properties -/

/-- Metabelianity descends from the relatively free source. -/
theorem isMetabelian (N : ℕ) : IsMetabelian (L N) := by
  have hmap := LieIdeal.derivedSeries_map_eq
    (f := quotientMap N) 2 (quotientMap_surjective N)
  change LieAlgebra.derivedSeries ℤ (L N) 2 = ⊥
  rw [← hmap]
  rw [FreeMetabelian.Free.isMetabelian]
  simp

/-- In zero-based convention, the `(N+3)`rd lower-central term is
the manuscript term `γ_(N+4)`, hence is zero. -/
theorem lowerCentralSeries_cutoff_eq_bot (N : ℕ) :
    LieModule.lowerCentralSeries ℤ (L N) (L N) (N + 3) = ⊥ := by
  have hmap := LieIdeal.lowerCentralSeries_map_eq
    (f := quotientMap N) (N + 3) (quotientMap_surjective N)
  rw [← hmap, FreeMetabelian.Free.lowerCentralSeries_cutoff_eq_bot]
  simp

private theorem r1_mem (N : ℕ) : r1Source N ∈ definingRelators N := by
  exact Or.inl (Or.inl (by simp))

private theorem r2_mem (N : ℕ) : r2Source N ∈ definingRelators N := by
  exact Or.inl (Or.inl (by simp))

private theorem r3_mem (N : ℕ) : r3Source N ∈ definingRelators N := by
  exact Or.inl (Or.inl (by simp))

@[simp] theorem r1_eq_zero (N : ℕ) : quotientMap N (r1Source N) = 0 :=
  quotientMap_eq_zero_of_mem_definingRelators (r1_mem N)

@[simp] theorem r2_eq_zero (N : ℕ) : quotientMap N (r2Source N) = 0 :=
  quotientMap_eq_zero_of_mem_definingRelators (r2_mem N)

@[simp] theorem r3_eq_zero (N : ℕ) : quotientMap N (r3Source N) = 0 :=
  quotientMap_eq_zero_of_mem_definingRelators (r3_mem N)

theorem offDiagonalTop_eq_zero (N : ℕ) (hN : 1 ≤ N)
    {i j : Fin 3} (hij : i ≠ j) :
    ⁅c N i, smallGenerator N j⁆ = 0 := by
  rw [c, smallGenerator, ← LieHom.map_lie]
  apply quotientMap_eq_zero_of_mem_definingRelators
  exact Or.inl (Or.inr
    (offDiagonalTopRelators_subset_topHallRelators N hN ⟨i, j, hij, rfl⟩))

@[simp] theorem c_lie_smallGenerator (N : ℕ) (i : Fin 3) :
    ⁅c N i, smallGenerator N i⁆ = u N i := by
  change ⁅quotientMap N (cSource N i),
      quotientMap N (smallSourceGenerator N i)⁆ =
    quotientMap N ⁅cSource N i, smallSourceGenerator N i⁆
  exact (LieHom.map_lie (quotientMap N) _ _).symm

@[simp] theorem lie_x1_x2 (N : ℕ) : ⁅x1 N, x2 N⁆ = b12 N := by
  exact (LieHom.map_lie (quotientMap N) (x1Source N) (x2Source N)).symm

@[simp] theorem lie_x1_x3 (N : ℕ) : ⁅x1 N, x3 N⁆ = b13 N := by
  exact (LieHom.map_lie (quotientMap N) (x1Source N) (x3Source N)).symm

@[simp] theorem lie_x2_x3 (N : ℕ) : ⁅x2 N, x3 N⁆ = b23 N := by
  exact (LieHom.map_lie (quotientMap N) (x2Source N) (x3Source N)).symm

@[simp] theorem u1_eq_sixteen_u3 (N : ℕ) : u1 N = (16 : ℤ) • u3 N := by
  have hz : quotientMap N (u1Source N - (16 : ℤ) • u3Source N) = 0 := by
    apply quotientMap_eq_zero_of_mem_definingRelators
    exact Or.inr (by simp [exceptionalRelators])
  simpa [map_sub, map_zsmul] using sub_eq_zero.mp hz

@[simp] theorem u2_eq_four_u3 (N : ℕ) : u2 N = (4 : ℤ) • u3 N := by
  have hz : quotientMap N (u2Source N - (4 : ℤ) • u3Source N) = 0 := by
    apply quotientMap_eq_zero_of_mem_definingRelators
    exact Or.inr (by simp [exceptionalRelators])
  simpa [map_sub, map_zsmul] using sub_eq_zero.mp hz

@[simp] theorem sixtyFour_u3_eq_zero (N : ℕ) : (64 : ℤ) • u3 N = 0 := by
  have hz : quotientMap N ((64 : ℤ) • u3Source N) = 0 := by
    apply quotientMap_eq_zero_of_mem_definingRelators
    exact Or.inr (by simp [exceptionalRelators])
  simpa [map_zsmul] using hz

/-! ## The six displayed bracket relations -/

theorem four_b12_add_u2_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    (4 : ℤ) • b12 N + u2 N = 0 := by
  have hrel : (4 : ℤ) • x1 N + (2 : ℤ) • c3 N + c2 N = 0 := by
    simpa only [r1Source, map_add, map_zsmul, map_x1Source, map_cSource]
      using r1_eq_zero N
  have hr := congrArg (fun z : L N => ⁅z, x2 N⁆) hrel
  change ⁅(4 : ℤ) • x1 N + (2 : ℤ) • c3 N + c2 N, x2 N⁆ =
    ⁅0, x2 N⁆ at hr
  rw [add_lie, add_lie, zsmul_lie, zsmul_lie, zero_lie, lie_x1_x2] at hr
  change (4 : ℤ) • b12 N + (2 : ℤ) •
      ⁅c N 2, smallGenerator N 1⁆ + ⁅c N 1, smallGenerator N 1⁆ = 0 at hr
  rw [offDiagonalTop_eq_zero N hN (i := 2) (j := 1) (by decide),
    c_lie_smallGenerator, smul_zero, add_zero] at hr
  exact hr

theorem four_b13_add_two_u3_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    (4 : ℤ) • b13 N + (2 : ℤ) • u3 N = 0 := by
  have hrel : (4 : ℤ) • x1 N + (2 : ℤ) • c3 N + c2 N = 0 := by
    simpa only [r1Source, map_add, map_zsmul, map_x1Source, map_cSource]
      using r1_eq_zero N
  have hr := congrArg (fun z : L N => ⁅z, x3 N⁆) hrel
  change ⁅(4 : ℤ) • x1 N + (2 : ℤ) • c3 N + c2 N, x3 N⁆ =
    ⁅0, x3 N⁆ at hr
  rw [add_lie, add_lie, zsmul_lie, zsmul_lie, zero_lie, lie_x1_x3] at hr
  change (4 : ℤ) • b13 N + (2 : ℤ) •
      ⁅c N 2, smallGenerator N 2⁆ + ⁅c N 1, smallGenerator N 2⁆ = 0 at hr
  rw [c_lie_smallGenerator,
    offDiagonalTop_eq_zero N hN (i := 1) (j := 2) (by decide), add_zero] at hr
  exact hr

theorem neg_sixteen_b12_sub_u1_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    -(16 : ℤ) • b12 N - u1 N = 0 := by
  have hrel : (16 : ℤ) • x2 N + (4 : ℤ) • c3 N - c1 N = 0 := by
    simpa only [r2Source, map_add, map_sub, map_zsmul, map_x2Source, map_cSource]
      using r2_eq_zero N
  have hr := congrArg (fun z : L N => ⁅z, x1 N⁆) hrel
  change ⁅(16 : ℤ) • x2 N + (4 : ℤ) • c3 N - c1 N, x1 N⁆ =
    ⁅0, x1 N⁆ at hr
  rw [sub_lie, add_lie, zsmul_lie, zsmul_lie, zero_lie] at hr
  change (16 : ℤ) • ⁅x2 N, x1 N⁆ + (4 : ℤ) •
      ⁅c N 2, smallGenerator N 0⁆ - ⁅c N 0, smallGenerator N 0⁆ = 0 at hr
  rw [offDiagonalTop_eq_zero N hN (i := 2) (j := 0) (by decide),
    c_lie_smallGenerator, smul_zero, add_zero] at hr
  have hs : ⁅x2 N, x1 N⁆ = -b12 N := by
    calc
      _ = -⁅x1 N, x2 N⁆ := (lie_skew (x2 N) (x1 N)).symm
      _ = -b12 N := congrArg Neg.neg (lie_x1_x2 N)
  rw [hs] at hr
  simpa using hr

theorem sixteen_b23_add_four_u3_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    (16 : ℤ) • b23 N + (4 : ℤ) • u3 N = 0 := by
  have hrel : (16 : ℤ) • x2 N + (4 : ℤ) • c3 N - c1 N = 0 := by
    simpa only [r2Source, map_add, map_sub, map_zsmul, map_x2Source, map_cSource]
      using r2_eq_zero N
  have hr := congrArg (fun z : L N => ⁅z, x3 N⁆) hrel
  change ⁅(16 : ℤ) • x2 N + (4 : ℤ) • c3 N - c1 N, x3 N⁆ =
    ⁅0, x3 N⁆ at hr
  rw [sub_lie, add_lie, zsmul_lie, zsmul_lie, zero_lie, lie_x2_x3] at hr
  change (16 : ℤ) • b23 N + (4 : ℤ) •
      ⁅c N 2, smallGenerator N 2⁆ - ⁅c N 0, smallGenerator N 2⁆ = 0 at hr
  rw [c_lie_smallGenerator,
    offDiagonalTop_eq_zero N hN (i := 0) (j := 2) (by decide), sub_zero] at hr
  exact hr

theorem neg_sixtyFour_b13_sub_two_u1_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    -(64 : ℤ) • b13 N - (2 : ℤ) • u1 N = 0 := by
  have hrel : (64 : ℤ) • x3 N - (4 : ℤ) • c2 N -
      (2 : ℤ) • c1 N = 0 := by
    simpa only [r3Source, map_sub, map_zsmul, map_x3Source, map_cSource]
      using r3_eq_zero N
  have hr := congrArg (fun z : L N => ⁅z, x1 N⁆) hrel
  change ⁅(64 : ℤ) • x3 N - (4 : ℤ) • c2 N -
      (2 : ℤ) • c1 N, x1 N⁆ = ⁅0, x1 N⁆ at hr
  rw [sub_lie, sub_lie, zsmul_lie, zsmul_lie, zsmul_lie, zero_lie] at hr
  change (64 : ℤ) • ⁅x3 N, x1 N⁆ - (4 : ℤ) •
      ⁅c N 1, smallGenerator N 0⁆ - (2 : ℤ) •
      ⁅c N 0, smallGenerator N 0⁆ = 0 at hr
  rw [offDiagonalTop_eq_zero N hN (i := 1) (j := 0) (by decide),
    c_lie_smallGenerator, smul_zero, sub_zero] at hr
  have hs : ⁅x3 N, x1 N⁆ = -b13 N := by
    calc
      _ = -⁅x1 N, x3 N⁆ := (lie_skew (x3 N) (x1 N)).symm
      _ = -b13 N := congrArg Neg.neg (lie_x1_x3 N)
  rw [hs] at hr
  simpa using hr

theorem neg_sixtyFour_b23_sub_four_u2_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    -(64 : ℤ) • b23 N - (4 : ℤ) • u2 N = 0 := by
  have hrel : (64 : ℤ) • x3 N - (4 : ℤ) • c2 N -
      (2 : ℤ) • c1 N = 0 := by
    simpa only [r3Source, map_sub, map_zsmul, map_x3Source, map_cSource]
      using r3_eq_zero N
  have hr := congrArg (fun z : L N => ⁅z, x2 N⁆) hrel
  change ⁅(64 : ℤ) • x3 N - (4 : ℤ) • c2 N -
      (2 : ℤ) • c1 N, x2 N⁆ = ⁅0, x2 N⁆ at hr
  rw [sub_lie, sub_lie, zsmul_lie, zsmul_lie, zsmul_lie, zero_lie] at hr
  change (64 : ℤ) • ⁅x3 N, x2 N⁆ - (4 : ℤ) •
      ⁅c N 1, smallGenerator N 1⁆ - (2 : ℤ) •
      ⁅c N 0, smallGenerator N 1⁆ = 0 at hr
  rw [c_lie_smallGenerator,
    offDiagonalTop_eq_zero N hN (i := 0) (j := 1) (by decide), smul_zero,
    sub_zero] at hr
  have hs : ⁅x3 N, x2 N⁆ = -b23 N := by
    calc
      _ = -⁅x2 N, x3 N⁆ := (lie_skew (x3 N) (x2 N)).symm
      _ = -b23 N := congrArg Neg.neg (lie_x2_x3 N)
  rw [hs] at hr
  simpa using hr

end

end LieRings.FinitePlateau
