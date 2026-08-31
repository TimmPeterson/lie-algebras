import LieRings.FinitePlateau.Height
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The exceptional top layer of the finite-plateau presentation

This file proves the additive assertions about the three exceptional
top-weight generators.  The lower-bound argument will be supplied by a
character of the *whole* presented Lie ring; checking that the character
descends therefore includes every iterated bracket of every defining
relation, not merely the displayed four-coordinate relation matrix.
-/

namespace LieRings.FinitePlateau

noncomputable section

open FreeMetabelian

/-! ## Integral Hall-coordinate reads -/

/-- The three standard weight-two Hall indices.  The Hall orientation is
`[x_j,x_i]` for `i<j`; consequently the manuscript elements `b_ij=[x_i,x_j]`
are the negatives of these basis vectors. -/
def pairHallIndex (i j : Fin 3) (hij : i < j) :
    FreeMetabelian.HallIndex Generator 0 where
  head := smallGeneratorIndex j
  pivot := smallGeneratorIndex i
  teeth := Sym.mk 0 rfl
  pivot_lt_head := by simp [smallGeneratorIndex]; omega
  pivot_le_teeth := by simp

/-- Read one integral Hall coefficient in weight two. -/
def pairCoordinate (N : ℕ) (i j : Fin 3) (hij : i < j) :
    Source N →ₗ[ℤ] ℤ :=
  ((FreeMetabelian.hallBasis generatorBasis 0).coord
      (pairHallIndex i j hij)).comp
    (FreeMetabelian.Free.weightProject 1 (by omega))

/-- The source element represented by a standard weight-two Hall index. -/
def pairHallSource (N : ℕ) (i j : Fin 3) (hij : i < j) : Source N :=
  FreeMetabelian.Free.inclComponent 0 (by omega)
    (FreeMetabelian.hallBasis generatorBasis 0 (pairHallIndex i j hij))

@[simp] theorem pairCoordinate_pairHallSource (N : ℕ)
    (i j : Fin 3) (hij : i < j)
    (k l : Fin 3) (hkl : k < l) :
    pairCoordinate N i j hij (pairHallSource N k l hkl) =
      if pairHallIndex i j hij = pairHallIndex k l hkl then 1 else 0 := by
  rw [pairCoordinate, LinearMap.comp_apply, Module.Basis.coord_apply]
  have hp : FreeMetabelian.Free.weightProject 1 (by omega)
      (pairHallSource N k l hkl) =
      FreeMetabelian.hallBasis generatorBasis 0 (pairHallIndex k l hkl) := by
    simp only [pairHallSource, FreeMetabelian.Free.weightProject,
      FreeMetabelian.Free.project_apply, FreeMetabelian.Free.inclComponent,
      FreeMetabelian.hallBasis_apply]
    change (FreeMetabelian.Free.incl
        (⟨1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallVector generatorBasis 0 (pairHallIndex k l hkl)))
        ⟨1, by omega⟩ = _
    exact FreeMetabelian.Free.incl_apply_same _ _
  calc
    _ = ((FreeMetabelian.hallBasis generatorBasis 0).repr
        (FreeMetabelian.hallBasis generatorBasis 0
          (pairHallIndex k l hkl))) (pairHallIndex i j hij) :=
      congrArg (fun z ↦ ((FreeMetabelian.hallBasis generatorBasis 0).repr z)
        (pairHallIndex i j hij)) hp
    _ = _ := by
      classical
      rw [Module.Basis.repr_self]
      simp [Finsupp.single_apply, eq_comm]

theorem pairHallSource_eq_bracket (N : ℕ) (i j : Fin 3) (hij : i < j) :
    pairHallSource N i j hij =
      ⁅smallSourceGenerator N j, smallSourceGenerator N i⁆ := by
  have he := FreeMetabelian.Evaluation.hallBracket_eq_incl
    (c := N + 3) generatorBasis 0 (pairHallIndex i j hij) (by omega)
  have hlhs : pairHallSource N i j hij =
      FreeMetabelian.Free.incl
        (⟨1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallVector generatorBasis 0
          (pairHallIndex i j hij)) := by
    unfold pairHallSource FreeMetabelian.Free.inclComponent
    apply congrArg (FreeMetabelian.Free.incl
      (⟨1, by omega⟩ : Fin (N + 3)))
    rw [FreeMetabelian.hallBasis_apply]
    rfl
  rw [hlhs, ← he]
  rfl

theorem b12Source_eq_neg_pairHallSource (N : ℕ) :
    b12Source N = -pairHallSource N 0 1 (by decide) := by
  rw [pairHallSource_eq_bracket]
  change ⁅smallSourceGenerator N 0, smallSourceGenerator N 1⁆ =
    -⁅smallSourceGenerator N 1, smallSourceGenerator N 0⁆
  exact (lie_skew (smallSourceGenerator N 0)
    (smallSourceGenerator N 1)).symm

theorem b13Source_eq_neg_pairHallSource (N : ℕ) :
    b13Source N = -pairHallSource N 0 2 (by decide) := by
  rw [pairHallSource_eq_bracket]
  change ⁅smallSourceGenerator N 0, smallSourceGenerator N 2⁆ =
    -⁅smallSourceGenerator N 2, smallSourceGenerator N 0⁆
  exact (lie_skew (smallSourceGenerator N 0)
    (smallSourceGenerator N 2)).symm

theorem b23Source_eq_neg_pairHallSource (N : ℕ) :
    b23Source N = -pairHallSource N 1 2 (by decide) := by
  rw [pairHallSource_eq_bracket]
  change ⁅smallSourceGenerator N 1, smallSourceGenerator N 2⁆ =
    -⁅smallSourceGenerator N 2, smallSourceGenerator N 1⁆
  exact (lie_skew (smallSourceGenerator N 1)
    (smallSourceGenerator N 2)).symm

/-- Read one integral Hall coefficient in the top manuscript weight `N+3`. -/
def topCoordinate (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    Source N →ₗ[ℤ] ℤ :=
  ((FreeMetabelian.hallBasis generatorBasis (N + 1)).coord h).comp
    (FreeMetabelian.Free.weightProject (N + 2) (by omega))

@[simp] theorem topCoordinate_topHallSource (N : ℕ)
    (h k : FreeMetabelian.HallIndex Generator (N + 1)) :
    topCoordinate N h (topHallSource N k) = if h = k then 1 else 0 := by
  rw [topCoordinate, LinearMap.comp_apply, Module.Basis.coord_apply]
  have hp : FreeMetabelian.Free.weightProject (N + 2) (by omega)
      (topHallSource N k) =
      FreeMetabelian.hallBasis generatorBasis (N + 1) k := by
    simp only [topHallSource, FreeMetabelian.Free.weightProject,
      FreeMetabelian.Free.project_apply, FreeMetabelian.hallBasis_apply]
    simp only [FreeMetabelian.Free.inclComponent]
    change (FreeMetabelian.Free.incl
        (⟨N + 1 + 1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallVector generatorBasis (N + 1) k))
        ⟨N + 2, by omega⟩ = _
    have hn : N + 1 + 1 = N + 2 := by omega
    simpa only [hn] using
      (FreeMetabelian.Free.incl_apply_same
        (⟨N + 2, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallVector generatorBasis (N + 1) k))
  calc
    _ = ((FreeMetabelian.hallBasis generatorBasis (N + 1)).repr
        (FreeMetabelian.hallBasis generatorBasis (N + 1) k)) h :=
      congrArg (fun z ↦
        ((FreeMetabelian.hallBasis generatorBasis (N + 1)).repr z) h) hp
    _ = _ := by
      classical
      rw [Module.Basis.repr_self]
      simp [Finsupp.single_apply, eq_comm]

/-! ## Generator erasure and multidegree separation -/

/-- Delete one coordinate from the free generator module. -/
def eraseGeneratorLinear (i : Generator) :
    GeneratorModule →ₗ[ℤ] GeneratorModule :=
  (Finsupp.eraseAddHom i).toIntLinearMap

/-- The induced endomorphism of the truncated free metabelian Lie ring.
It sends the chosen free generator to zero and fixes every other generator. -/
def eraseGenerator (N : ℕ) (i : Generator) : Source N →ₗ⁅ℤ⁆ Source N :=
  FreeMetabelian.Evaluation.lieHom
    (FreeMetabelian.Free.isMetabelian (X := GeneratorModule) (c := N + 3))
    (FreeMetabelian.Free.lowerCentralSeries_cutoff_eq_bot
      (X := GeneratorModule) (c := N + 3))
    ((FreeMetabelian.Free.weightIncl 0 (by omega)).comp
      (eraseGeneratorLinear i))

@[simp] theorem eraseGenerator_sourceGenerator (N : ℕ) (i j : Generator) :
    eraseGenerator N i (sourceGenerator N j) =
      if j = i then 0 else sourceGenerator N j := by
  rw [eraseGenerator, sourceGenerator]
  change FreeMetabelian.Evaluation.lieHom _ _ _
      (FreeMetabelian.Free.incl
        (⟨0, by omega⟩ : Fin (N + 3)) (generatorBasis j)) = _
  rw [FreeMetabelian.Evaluation.lieHom_incl]
  change FreeMetabelian.Free.weightIncl 0 (by omega)
      (Finsupp.erase i (generatorBasis j)) = _
  by_cases hji : j = i
  · subst j
    simp [generatorBasis]
    exact map_zero _
  · simp [generatorBasis, hji]

/-- Erasing a generator acts diagonally on every literal Hall bracket: a word
is either fixed or killed. -/
theorem eraseGenerator_hallBracket_eq_self_or_zero (N : ℕ) (i : Generator) :
    ∀ (q : ℕ) (k : FreeMetabelian.HallIndex Generator q)
      (hq : q + 1 < N + 3),
      eraseGenerator N i
          (FreeMetabelian.Evaluation.hallBracket generatorBasis q k hq) =
          FreeMetabelian.Evaluation.hallBracket generatorBasis q k hq ∨
        eraseGenerator N i
          (FreeMetabelian.Evaluation.hallBracket generatorBasis q k hq) = 0 := by
  intro q
  induction q with
  | zero =>
      intro k hq
      rw [FreeMetabelian.Evaluation.hallBracket, LieHom.map_lie]
      change ⁅eraseGenerator N i (sourceGenerator N k.head),
          eraseGenerator N i (sourceGenerator N k.pivot)⁆ =
            ⁅sourceGenerator N k.head, sourceGenerator N k.pivot⁆ ∨
          ⁅eraseGenerator N i (sourceGenerator N k.head),
            eraseGenerator N i (sourceGenerator N k.pivot)⁆ = 0
      rw [eraseGenerator_sourceGenerator, eraseGenerator_sourceGenerator]
      by_cases hh : k.head = i <;> by_cases hp : k.pivot = i
      all_goals simp [hh, hp]
  | succ q ih =>
      intro k hq
      rw [FreeMetabelian.Evaluation.hallBracket, LieHom.map_lie]
      rcases ih k.predecessor (by omega) with hprev | hprev
      · rw [hprev]
        change ⁅FreeMetabelian.Evaluation.hallBracket generatorBasis q
              k.predecessor (by omega),
            eraseGenerator N i (sourceGenerator N k.nextTooth)⁆ =
              ⁅FreeMetabelian.Evaluation.hallBracket generatorBasis q
                  k.predecessor (by omega),
                sourceGenerator N k.nextTooth⁆ ∨
            ⁅FreeMetabelian.Evaluation.hallBracket generatorBasis q
                k.predecessor (by omega),
              eraseGenerator N i (sourceGenerator N k.nextTooth)⁆ = 0
        rw [eraseGenerator_sourceGenerator]
        by_cases ht : k.nextTooth = i
        · right
          simp [ht]
        · left
          simp [ht]
      · right
        rw [hprev]
        exact zero_lie _

/-- The same diagonal statement for a top Hall basis source. -/
theorem eraseGenerator_topHallSource_eq_self_or_zero (N : ℕ)
    (i : Generator) (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    eraseGenerator N i (topHallSource N h) = topHallSource N h ∨
      eraseGenerator N i (topHallSource N h) = 0 := by
  have he := eraseGenerator_hallBracket_eq_self_or_zero N i
    (N + 1) h (by omega)
  rw [FreeMetabelian.Evaluation.hallBracket_eq_incl] at he
  simpa [topHallSource, FreeMetabelian.Free.inclComponent,
    FreeMetabelian.hallBasis_apply] using he

@[simp] theorem hallGradedBasis_apply (N : ℕ)
    (p : (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis p =
      FreeMetabelian.Free.incl p.1
        (FreeMetabelian.Free.pieceBasis generatorBasis p.1.val p.2) := by
  classical
  rw [FreeMetabelian.Free.hallGradedBasis]
  let bPi := Pi.basis (fun i : Fin (N + 3) ↦
    FreeMetabelian.Free.pieceBasis generatorBasis i.val)
  have he : bPi.equivFun.toAddEquiv.toIntLinearEquiv = bPi.equivFun :=
    LinearEquiv.toAddEquiv_toIntLinearEquiv bPi.equivFun
  rw [he, Module.Basis.ofEquivFun_equivFun, Pi.basis_apply]
  ext s
  by_cases hs : s = p.1
  · subst s
    simp [FreeMetabelian.Free.incl]
  · simp [FreeMetabelian.Free.incl, Pi.single_eq_of_ne hs]

/-- The generator erasure is diagonal on the full graded Hall basis. -/
theorem eraseGenerator_hallGradedBasis_eq_self_or_zero (N : ℕ)
    (i : Generator)
    (p : (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val) :
    eraseGenerator N i (FreeMetabelian.Free.hallGradedBasis generatorBasis p) =
        FreeMetabelian.Free.hallGradedBasis generatorBasis p ∨
      eraseGenerator N i (FreeMetabelian.Free.hallGradedBasis generatorBasis p) = 0 := by
  rw [hallGradedBasis_apply]
  rcases p with ⟨⟨s, hs⟩, p⟩
  cases s with
  | zero =>
      change Generator at p
      change eraseGenerator N i (sourceGenerator N p) = sourceGenerator N p ∨
        eraseGenerator N i (sourceGenerator N p) = 0
      rw [eraseGenerator_sourceGenerator]
      by_cases hp : p = i
      · right
        simp [hp]
      · left
        simp [hp]
  | succ q =>
      change FreeMetabelian.HallIndex Generator q at p
      dsimp only [Prod.fst, Prod.snd]
      rw [FreeMetabelian.Free.pieceBasis]
      have he :
          (FreeMetabelian.hallBasis generatorBasis q).equivFun.toAddEquiv.toIntLinearEquiv =
            (FreeMetabelian.hallBasis generatorBasis q).equivFun :=
        LinearEquiv.toAddEquiv_toIntLinearEquiv
          (FreeMetabelian.hallBasis generatorBasis q).equivFun
      have hbEq : Module.Basis.ofEquivFun
            (FreeMetabelian.hallBasis generatorBasis q).equivFun.toAddEquiv.toIntLinearEquiv =
          FreeMetabelian.hallBasis generatorBasis q := by
        rw [he, Module.Basis.ofEquivFun_equivFun]
      have hpEq : (Module.Basis.ofEquivFun
            (FreeMetabelian.hallBasis generatorBasis q).equivFun.toAddEquiv.toIntLinearEquiv) p =
          FreeMetabelian.hallBasis generatorBasis q p :=
        congrArg (fun b ↦ b p) hbEq
      have hincl : FreeMetabelian.Free.incl
            (⟨q + 1, hs⟩ : Fin (N + 3))
            ((Module.Basis.ofEquivFun
              (FreeMetabelian.hallBasis generatorBasis q).equivFun.toAddEquiv.toIntLinearEquiv) p) =
          FreeMetabelian.Free.incl (⟨q + 1, hs⟩ : Fin (N + 3))
            (FreeMetabelian.hallBasis generatorBasis q p) :=
        congrArg (FreeMetabelian.Free.incl
          (⟨q + 1, hs⟩ : Fin (N + 3))) hpEq
      have heHall := eraseGenerator_hallBracket_eq_self_or_zero N i q p (by omega)
      rw [FreeMetabelian.Evaluation.hallBracket_eq_incl] at heHall
      have heBasis : eraseGenerator N i
            (FreeMetabelian.Free.incl (⟨q + 1, hs⟩ : Fin (N + 3))
              (FreeMetabelian.hallBasis generatorBasis q p)) =
              FreeMetabelian.Free.incl (⟨q + 1, hs⟩ : Fin (N + 3))
                (FreeMetabelian.hallBasis generatorBasis q p) ∨
          eraseGenerator N i
            (FreeMetabelian.Free.incl (⟨q + 1, hs⟩ : Fin (N + 3))
              (FreeMetabelian.hallBasis generatorBasis q p)) = 0 := by
        simpa [FreeMetabelian.hallBasis_apply] using heHall
      rcases heBasis with hfix | hzero
      · left
        exact (congrArg (eraseGenerator N i) hincl).trans
          (hfix.trans hincl.symm)
      · right
        exact (congrArg (eraseGenerator N i) hincl).trans hzero

/-- The full graded-basis index of a top Hall word. -/
def topGradedIndex (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val :=
  ⟨⟨N + 1 + 1, by omega⟩, h⟩

theorem hallGradedBasis_topGradedIndex (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis (topGradedIndex N h) =
      topHallSource N h := by
  rw [hallGradedBasis_apply]
  change FreeMetabelian.Free.incl
      (⟨N + 1 + 1, by omega⟩ : Fin (N + 3))
      (FreeMetabelian.Free.pieceBasis generatorBasis (N + 1 + 1) h) = _
  rw [FreeMetabelian.Free.pieceBasis]
  have he :
      (FreeMetabelian.hallBasis generatorBasis (N + 1)).equivFun.toAddEquiv.toIntLinearEquiv =
        (FreeMetabelian.hallBasis generatorBasis (N + 1)).equivFun :=
    LinearEquiv.toAddEquiv_toIntLinearEquiv
      (FreeMetabelian.hallBasis generatorBasis (N + 1)).equivFun
  have hbEq : Module.Basis.ofEquivFun
        (FreeMetabelian.hallBasis generatorBasis
          (N + 1)).equivFun.toAddEquiv.toIntLinearEquiv =
      FreeMetabelian.hallBasis generatorBasis (N + 1) := by
    rw [he, Module.Basis.ofEquivFun_equivFun]
  have hpEq := congrArg (fun b ↦ b h) hbEq
  calc
    _ = FreeMetabelian.Free.incl
        (⟨N + 1 + 1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallBasis generatorBasis (N + 1) h) :=
      congrArg (FreeMetabelian.Free.incl
        (⟨N + 1 + 1, by omega⟩ : Fin (N + 3))) hpEq
    _ = topHallSource N h := by
      unfold topHallSource FreeMetabelian.Free.inclComponent
      apply congrArg (FreeMetabelian.Free.incl
        (⟨N + 1 + 1, by omega⟩ : Fin (N + 3)))
      rfl

private theorem basis_coordinate_invariant_of_diagonal
    {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup A] (B : Module.Basis ι ℤ A)
    (E : A →ₗ[ℤ] A)
    (hdiag : ∀ p, E (B p) = B p ∨ E (B p) = 0)
    (p₀ : ι) (hfix : E (B p₀) = B p₀) (z : A) :
    B.coord p₀ (E z) = B.coord p₀ z := by
  have hmaps : (B.coord p₀).comp E = B.coord p₀ := by
    apply B.ext
    intro p
    rcases hdiag p with hp | hp
    · simp [LinearMap.comp_apply, hp]
    · by_cases hpp : p = p₀
      · subst p
        rw [hfix] at hp
        exact (B.ne_zero p₀ hp).elim
      · rw [LinearMap.comp_apply, hp, map_zero, Module.Basis.coord_apply,
          Module.Basis.repr_self]
        simp [Finsupp.single_apply, hpp]
  exact LinearMap.congr_fun hmaps z

/-- Lie homomorphisms commute with the iterated right bracket. -/
@[simp] theorem map_rightBracketPow {A B : Type*} [LieRing A] [LieRing B]
    (f : A →ₗ⁅ℤ⁆ B) (x y : A) : ∀ n,
    f (rightBracketPow x y n) = rightBracketPow (f x) (f y) n
  | 0 => rfl
  | n + 1 => by
      rw [rightBracketPow_succ, LieHom.map_lie, map_rightBracketPow,
        rightBracketPow_succ]

theorem eraseGenerator_tSource (N : ℕ) (i : Fin 3) :
    eraseGenerator N (smallGeneratorIndex i) (tSource N) = tSource N := by
  rw [tSource, map_rightBracketPow]
  change rightBracketPow
      (eraseGenerator N (smallGeneratorIndex i) (sourceGenerator N 4))
      (eraseGenerator N (smallGeneratorIndex i) (sourceGenerator N 0)) N =
    rightBracketPow (sourceGenerator N 4) (sourceGenerator N 0) N
  rw [eraseGenerator_sourceGenerator, eraseGenerator_sourceGenerator]
  have h4 : (4 : Generator) ≠ smallGeneratorIndex i := by
    intro h
    have := congrArg Fin.val h
    simp [smallGeneratorIndex] at this
    omega
  have h0 : (0 : Generator) ≠ smallGeneratorIndex i := by
    intro h
    have := congrArg Fin.val h
    simp [smallGeneratorIndex] at this
  simp [h4, h0]

theorem eraseGenerator_uSource_of_ne (N : ℕ) (i j : Fin 3) (hij : i ≠ j) :
    eraseGenerator N (smallGeneratorIndex i) (uSource N j) = uSource N j := by
  have hindex : smallGeneratorIndex j ≠ smallGeneratorIndex i := by
    intro h
    apply hij
    apply Fin.ext
    have := congrArg Fin.val h
    simpa [smallGeneratorIndex] using this.symm
  rw [uSource, cSource, LieHom.map_lie, LieHom.map_lie,
    eraseGenerator_tSource]
  change ⁅⁅tSource N,
      eraseGenerator N (smallGeneratorIndex i)
        (sourceGenerator N (smallGeneratorIndex j))⁆,
    eraseGenerator N (smallGeneratorIndex i)
      (sourceGenerator N (smallGeneratorIndex j))⁆ = _
  rw [eraseGenerator_sourceGenerator]
  simp only [hindex, if_false]
  rfl

theorem eraseGenerator_uSource_same (N : ℕ) (i : Fin 3) :
    eraseGenerator N (smallGeneratorIndex i) (uSource N i) = 0 := by
  rw [uSource, cSource, LieHom.map_lie, LieHom.map_lie,
    eraseGenerator_tSource]
  change ⁅⁅tSource N,
      eraseGenerator N (smallGeneratorIndex i)
        (sourceGenerator N (smallGeneratorIndex i))⁆,
    eraseGenerator N (smallGeneratorIndex i)
      (sourceGenerator N (smallGeneratorIndex i))⁆ = 0
  rw [eraseGenerator_sourceGenerator]
  simp

/-- A Hall coordinate of the full graded source basis. -/
def gradedCoordinate (N : ℕ)
    (p : (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val) :
    Source N →ₗ[ℤ] ℤ :=
  (FreeMetabelian.Free.hallGradedBasis generatorBasis).coord p

@[simp] theorem gradedCoordinate_hallGradedBasis_self (N : ℕ)
    (p : (s : Fin (N + 3)) ×
      FreeMetabelian.Free.PieceIndex Generator s.val) :
    gradedCoordinate N p
        (FreeMetabelian.Free.hallGradedBasis generatorBasis p) = 1 := by
  classical
  rw [gradedCoordinate, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp

theorem gradedCoordinate_hallGradedBasis_of_ne (N : ℕ)
    (p q : (s : Fin (N + 3)) ×
      FreeMetabelian.Free.PieceIndex Generator s.val) (hpq : p ≠ q) :
    gradedCoordinate N p
        (FreeMetabelian.Free.hallGradedBasis generatorBasis q) = 0 := by
  classical
  rw [gradedCoordinate, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply, hpq, Ne.symm hpq]

theorem exceptionalCoordinate_erase_of_ne (N : ℕ) (hN : 1 ≤ N)
    (i j : Fin 3) (hij : i ≠ j) (z : Source N) :
    gradedCoordinate N (topGradedIndex N (uHallIndex N hN j))
        (eraseGenerator N (smallGeneratorIndex i) z) =
      gradedCoordinate N (topGradedIndex N (uHallIndex N hN j)) z := by
  letI : Fintype
      ((s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val) :=
    Fintype.ofFinite _
  letI : DecidableEq
      ((s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val) :=
    Classical.decEq _
  apply basis_coordinate_invariant_of_diagonal
    (FreeMetabelian.Free.hallGradedBasis generatorBasis)
    (eraseGenerator N (smallGeneratorIndex i)).toLinearMap
    (eraseGenerator_hallGradedBasis_eq_self_or_zero N
      (smallGeneratorIndex i))
  rw [hallGradedBasis_topGradedIndex,
    topHallSource_uHallIndex_eq N hN j]
  change eraseGenerator N (smallGeneratorIndex i) (uSource N j) = uSource N j
  exact eraseGenerator_uSource_of_ne N i j hij

theorem exceptionalCoordinate_eq_zero_of_erase_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (i j : Fin 3) (hij : i ≠ j)
    {z : Source N} (hz : eraseGenerator N (smallGeneratorIndex i) z = 0) :
    gradedCoordinate N (topGradedIndex N (uHallIndex N hN j)) z = 0 := by
  rw [← exceptionalCoordinate_erase_of_ne N hN i j hij z, hz, map_zero]

@[simp] theorem exceptionalCoordinate_uSource_self
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) :
    gradedCoordinate N (topGradedIndex N (uHallIndex N hN i))
        (uSource N i) = 1 := by
  rw [← topHallSource_uHallIndex_eq N hN i,
    ← hallGradedBasis_topGradedIndex,
    gradedCoordinate_hallGradedBasis_self]

@[simp] theorem exceptionalCoordinate_uSource_of_ne
    (N : ℕ) (hN : 1 ≤ N) (i j : Fin 3) (hij : i ≠ j) :
    gradedCoordinate N (topGradedIndex N (uHallIndex N hN j))
        (uSource N i) = 0 := by
  exact exceptionalCoordinate_eq_zero_of_erase_eq_zero N hN i j hij
    (eraseGenerator_uSource_same N i)

/-- The full graded-basis index of a standard weight-two pair. -/
def pairGradedIndex (N : ℕ) (i j : Fin 3) (hij : i < j) :
    (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val :=
  ⟨⟨1, by omega⟩, pairHallIndex i j hij⟩

theorem hallGradedBasis_pairGradedIndex (N : ℕ)
    (i j : Fin 3) (hij : i < j) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis
        (pairGradedIndex N i j hij) = pairHallSource N i j hij := by
  rw [hallGradedBasis_apply]
  change FreeMetabelian.Free.incl (⟨1, by omega⟩ : Fin (N + 3))
      (FreeMetabelian.Free.pieceBasis generatorBasis 1
        (pairHallIndex i j hij)) = _
  rw [FreeMetabelian.Free.pieceBasis]
  have he :
      (FreeMetabelian.hallBasis generatorBasis 0).equivFun.toAddEquiv.toIntLinearEquiv =
        (FreeMetabelian.hallBasis generatorBasis 0).equivFun :=
    LinearEquiv.toAddEquiv_toIntLinearEquiv
      (FreeMetabelian.hallBasis generatorBasis 0).equivFun
  have hbEq : Module.Basis.ofEquivFun
        (FreeMetabelian.hallBasis generatorBasis 0).equivFun.toAddEquiv.toIntLinearEquiv =
      FreeMetabelian.hallBasis generatorBasis 0 := by
    rw [he, Module.Basis.ofEquivFun_equivFun]
  have hpEq := congrArg (fun b ↦ b (pairHallIndex i j hij)) hbEq
  calc
    _ = FreeMetabelian.Free.incl (⟨1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallBasis generatorBasis 0
          (pairHallIndex i j hij)) :=
      congrArg (FreeMetabelian.Free.incl
        (⟨1, by omega⟩ : Fin (N + 3))) hpEq
    _ = pairHallSource N i j hij := by
      unfold pairHallSource FreeMetabelian.Free.inclComponent
      apply congrArg (FreeMetabelian.Free.incl
        (⟨1, by omega⟩ : Fin (N + 3)))
      rfl

/-- Cast one integral graded coordinate to `ZMod 256`. -/
def castCoordinate (N : ℕ) (f : Source N →ₗ[ℤ] ℤ) :
    Source N →ₗ[ℤ] ZMod 256 :=
  (Int.castAddHom (ZMod 256)).toIntLinearMap.comp f

/-- Cast one integral graded coordinate to `ZMod 256`. -/
def gradedZModCoordinate (N : ℕ)
    (p : (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val) :
    Source N →ₗ[ℤ] ZMod 256 :=
  castCoordinate N (gradedCoordinate N p)

/-- The manuscript detector.  On
`(b12,b13,b23,u1,u2,u3)` it takes the values
`(-4,-2,-1,64,16,4)` in `ZMod 256`. -/
def sourceDetector (N : ℕ) (hN : 1 ≤ N) : Source N →ₗ[ℤ] ZMod 256 :=
  (4 : ℤ) • castCoordinate N (pairCoordinate N 0 1 (by decide)) +
    (2 : ℤ) • castCoordinate N (pairCoordinate N 0 2 (by decide)) +
    castCoordinate N (pairCoordinate N 1 2 (by decide)) +
    (64 : ℤ) • gradedZModCoordinate N
      (topGradedIndex N (uHallIndex N hN 0)) +
    (16 : ℤ) • gradedZModCoordinate N
      (topGradedIndex N (uHallIndex N hN 1)) +
    (4 : ℤ) • gradedZModCoordinate N
      (topGradedIndex N (uHallIndex N hN 2))

@[simp] theorem pairCoordinate_topHallSource (N : ℕ) (hN : 1 ≤ N)
    (i j : Fin 3) (hij : i < j)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    pairCoordinate N i j hij (topHallSource N h) = 0 := by
  rw [pairCoordinate, LinearMap.comp_apply]
  have hp : FreeMetabelian.Free.weightProject 1 (by omega)
      (topHallSource N h) = 0 := by
    change (topHallSource N h) ⟨1, by omega⟩ = 0
    unfold topHallSource FreeMetabelian.Free.inclComponent
    rw [LinearMap.comp_apply]
    apply FreeMetabelian.Free.incl_apply_of_ne
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_mk] at hv
    omega
  exact (congrArg
    ((FreeMetabelian.hallBasis generatorBasis 0).coord
      (pairHallIndex i j hij)) hp).trans (map_zero _)

@[simp] theorem pairCoordinate_uSource (N : ℕ) (hN : 1 ≤ N)
    (i j : Fin 3) (hij : i < j) (k : Fin 3) :
    pairCoordinate N i j hij (uSource N k) = 0 := by
  rw [← topHallSource_uHallIndex_eq N hN k]
  exact pairCoordinate_topHallSource N hN i j hij _

@[simp] theorem exceptionalCoordinate_pairHallSource (N : ℕ) (hN : 1 ≤ N)
    (k : Fin 3) (i j : Fin 3) (hij : i < j) :
    gradedCoordinate N (topGradedIndex N (uHallIndex N hN k))
        (pairHallSource N i j hij) = 0 := by
  rw [← hallGradedBasis_pairGradedIndex]
  apply gradedCoordinate_hallGradedBasis_of_ne
  intro heq
  have hv := congrArg (fun p ↦ p.1.val) heq
  simp [topGradedIndex, pairGradedIndex] at hv

@[simp] theorem exceptionalCoordinate_b12Source (N : ℕ) (hN : 1 ≤ N)
    (k : Fin 3) :
    gradedCoordinate N (topGradedIndex N (uHallIndex N hN k))
        (b12Source N) = 0 := by
  rw [b12Source_eq_neg_pairHallSource, map_neg,
    exceptionalCoordinate_pairHallSource, neg_zero]

@[simp] theorem exceptionalCoordinate_b13Source (N : ℕ) (hN : 1 ≤ N)
    (k : Fin 3) :
    gradedCoordinate N (topGradedIndex N (uHallIndex N hN k))
        (b13Source N) = 0 := by
  rw [b13Source_eq_neg_pairHallSource, map_neg,
    exceptionalCoordinate_pairHallSource, neg_zero]

@[simp] theorem exceptionalCoordinate_b23Source (N : ℕ) (hN : 1 ≤ N)
    (k : Fin 3) :
    gradedCoordinate N (topGradedIndex N (uHallIndex N hN k))
        (b23Source N) = 0 := by
  rw [b23Source_eq_neg_pairHallSource, map_neg,
    exceptionalCoordinate_pairHallSource, neg_zero]

@[simp] theorem sourceDetector_uSource (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) :
    sourceDetector N hN (uSource N i) =
      match i with
      | 0 => 64
      | 1 => 16
      | 2 => 4 := by
  fin_cases i <;>
    simp [sourceDetector, castCoordinate, gradedZModCoordinate,
      LinearMap.add_apply, LinearMap.smul_apply,
      pairCoordinate_uSource N hN,
      exceptionalCoordinate_uSource_of_ne]

@[simp] theorem sourceDetector_b12Source (N : ℕ) (hN : 1 ≤ N) :
    sourceDetector N hN (b12Source N) = -4 := by
  rw [b12Source_eq_neg_pairHallSource, map_neg]
  simp [sourceDetector, castCoordinate, gradedZModCoordinate,
    LinearMap.add_apply, LinearMap.smul_apply,
    pairCoordinate_pairHallSource,
    exceptionalCoordinate_pairHallSource N hN,
    pairHallIndex, smallGeneratorIndex]

@[simp] theorem sourceDetector_b13Source (N : ℕ) (hN : 1 ≤ N) :
    sourceDetector N hN (b13Source N) = -2 := by
  rw [b13Source_eq_neg_pairHallSource, map_neg]
  simp [sourceDetector, castCoordinate, gradedZModCoordinate,
    LinearMap.add_apply, LinearMap.smul_apply,
    pairCoordinate_pairHallSource,
    exceptionalCoordinate_pairHallSource N hN,
    pairHallIndex, smallGeneratorIndex]

@[simp] theorem sourceDetector_b23Source (N : ℕ) (hN : 1 ≤ N) :
    sourceDetector N hN (b23Source N) = -1 := by
  rw [b23Source_eq_neg_pairHallSource, map_neg]
  simp [sourceDetector, castCoordinate, gradedZModCoordinate,
    LinearMap.add_apply, LinearMap.smul_apply,
    pairCoordinate_pairHallSource,
    exceptionalCoordinate_pairHallSource N hN,
    pairHallIndex, smallGeneratorIndex]

/-! ## The whole relation ideal -/

/-- Successive right bracketing by a list of arbitrary source elements. -/
def rightOrbit {A : Type*} [LieRing A] (z : A) : List A → A
  | [] => z
  | x :: xs => rightOrbit ⁅z, x⁆ xs

@[simp] theorem rightOrbit_nil {A : Type*} [LieRing A] (z : A) :
    rightOrbit z [] = z := rfl

@[simp] theorem rightOrbit_cons {A : Type*} [LieRing A]
    (z x : A) (xs : List A) :
    rightOrbit z (x :: xs) = rightOrbit ⁅z, x⁆ xs := rfl

theorem rightOrbit_zero {A : Type*} [LieRing A] : ∀ xs : List A,
    rightOrbit 0 xs = 0
  | [] => rfl
  | x :: xs => by rw [rightOrbit_cons, zero_lie, rightOrbit_zero]

theorem rightOrbit_add {A : Type*} [LieRing A] (z w : A) : ∀ xs : List A,
    rightOrbit (z + w) xs = rightOrbit z xs + rightOrbit w xs
  | [] => rfl
  | x :: xs => by
      rw [rightOrbit_cons, add_lie, rightOrbit_add, rightOrbit_cons,
        rightOrbit_cons]

theorem rightOrbit_zsmul {A : Type*} [LieRing A] (n : ℤ) (z : A) :
    ∀ xs : List A, rightOrbit (n • z) xs = n • rightOrbit z xs
  | [] => rfl
  | x :: xs => by
      rw [rightOrbit_cons, zsmul_lie, rightOrbit_zsmul, rightOrbit_cons]

theorem rightOrbit_neg {A : Type*} [LieRing A] (z : A) (xs : List A) :
    rightOrbit (-z) xs = -rightOrbit z xs := by
  simpa using rightOrbit_zsmul (-1) z xs

theorem topHallSource_lie_eq_zero (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) (z : Source N) :
    ⁅topHallSource N h, z⁆ = 0 := by
  have hm : topHallSource N h ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 2) := by
    rw [topHallSource, FreeMetabelian.hallBasis_apply]
    change FreeMetabelian.Free.incl
      (⟨N + 1 + 1, by omega⟩ : Fin (N + 3))
      (FreeMetabelian.hallVector generatorBasis (N + 1) h) ∈ _
    rw [← FreeMetabelian.Evaluation.hallBracket_eq_incl]
    exact FreeMetabelian.Evaluation.hallBracket_mem_lowerCentralSeries
      generatorBasis (N + 1) h (by omega)
  have hz : ⁅z, topHallSource N h⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 3) := by
    have hz' : ⁅z, topHallSource N h⁆ ∈
        LieModule.lowerCentralSeries ℤ (Source N) (Source N) ((N + 2) + 1) := by
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (by simp) hm
    simpa only [show (N + 2) + 1 = N + 3 by omega] using hz'
  have hz0 : ⁅z, topHallSource N h⁆ = 0 := by
    have hcut := FreeMetabelian.Free.lowerCentralSeries_cutoff_eq_bot
      (X := GeneratorModule) (c := N + 3)
    rw [hcut] at hz
    exact hz
  rw [← lie_skew, hz0, neg_zero]

theorem rightOrbit_topHallSource (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator (N + 1)) : ∀ xs : List (Source N),
    rightOrbit (topHallSource N h) xs =
      if xs = [] then topHallSource N h else 0
  | [] => by simp
  | x :: xs => by
      rw [rightOrbit_cons, topHallSource_lie_eq_zero, rightOrbit_zero]
      simp

theorem sourceDetector_topHallSource_of_not_exceptional
    (N : ℕ) (hN : 1 ≤ N)
    (h : FreeMetabelian.HallIndex Generator (N + 1))
    (hne : ¬ IsExceptionalTop N h) :
    sourceDetector N hN (topHallSource N h) = 0 := by
  have hcoord : ∀ k : Fin 3,
      gradedCoordinate N (topGradedIndex N (uHallIndex N hN k))
        (topHallSource N h) = 0 := by
    intro k
    rw [← hallGradedBasis_topGradedIndex]
    apply gradedCoordinate_hallGradedBasis_of_ne
    intro heq
    have hs := congrArg
      (FreeMetabelian.Free.hallGradedBasis generatorBasis) heq
    rw [hallGradedBasis_topGradedIndex,
      hallGradedBasis_topGradedIndex,
      topHallSource_uHallIndex_eq N hN k] at hs
    fin_cases k
    · exact hne (Or.inl hs.symm)
    · exact hne (Or.inr (Or.inl hs.symm))
    · exact hne (Or.inr (Or.inr hs.symm))
  simp [sourceDetector, castCoordinate, gradedZModCoordinate,
    LinearMap.add_apply, LinearMap.smul_apply,
    pairCoordinate_topHallSource N hN, hcoord]

/-! The two outer generators `x₅,x₄` do not occur among the three
exceptional diagonals.  The following Hall calculation identifies
`[cᵢ,x₅]` and `[cᵢ,x₄]` as literal nonexceptional top Hall words.  We use an
index allowing an arbitrary final generator because the presentation's public
`topBracketHallIndex` is intentionally restricted to `x₁,x₂,x₃`. -/

private def allTopBracketTeeth (N : ℕ) (hN : 1 ≤ N) (i : Fin 3)
    (j : Generator) : Sym Generator (N + 1) :=
  Sym.mk
    (Multiset.replicate (N - 1) (0 : Generator) +
      ({smallGeneratorIndex i, j} : Multiset Generator))
    (by simp; omega)

private def allTopBracketHallIndex (N : ℕ) (hN : 1 ≤ N) (i : Fin 3)
    (j : Generator) : FreeMetabelian.HallIndex Generator (N + 1) where
  head := 4
  pivot := 0
  teeth := allTopBracketTeeth N hN i j
  pivot_lt_head := by decide
  pivot_le_teeth := fun k _ ↦ Fin.zero_le k

private theorem hallIndex_ext' {q : ℕ}
    {a b : FreeMetabelian.HallIndex Generator q}
    (hh : a.head = b.head) (hp : a.pivot = b.pivot)
    (ht : a.teeth = b.teeth) : a = b := by
  cases a
  cases b
  simp only at hh hp ht
  subst_vars
  rfl

private theorem allTopBracketHallIndex_nextTooth (N : ℕ) (hN : 1 ≤ N)
    (i : Fin 3) (j : Generator) :
    (allTopBracketHallIndex (N + 1) (by omega) i j).nextTooth = 0 := by
  simp only [FreeMetabelian.HallIndex.nextTooth, allTopBracketHallIndex,
    allTopBracketTeeth]
  change ((Multiset.replicate N (0 : Generator) +
    ({smallGeneratorIndex i, j} : Multiset Generator)).toFinset.min' _) = 0
  rw [Finset.min'_eq_iff]
  constructor
  · have hN0 : N ≠ 0 := by omega
    simp [hN0]
  · intro b _
    exact Fin.zero_le b

private theorem allTopBracketHallIndex_predecessor (N : ℕ) (hN : 1 ≤ N)
    (i : Fin 3) (j : Generator) :
    (allTopBracketHallIndex (N + 1) (by omega) i j).predecessor =
      allTopBracketHallIndex N hN i j := by
  refine hallIndex_ext'
    (a := (allTopBracketHallIndex (N + 1) (by omega) i j).predecessor)
    (b := allTopBracketHallIndex N hN i j) rfl rfl ?_
  apply Sym.ext
  simp only [FreeMetabelian.HallIndex.predecessor, allTopBracketHallIndex,
    allTopBracketTeeth]
  change Multiset.erase
        (Multiset.replicate N (0 : Generator) +
          ({smallGeneratorIndex i, j} : Multiset Generator))
        ((Multiset.replicate N (0 : Generator) +
          ({smallGeneratorIndex i, j} : Multiset Generator)).toFinset.min' _) =
      Multiset.replicate (N - 1) (0 : Generator) +
        ({smallGeneratorIndex i, j} : Multiset Generator)
  rw [show ((Multiset.replicate N (0 : Generator) +
        ({smallGeneratorIndex i, j} : Multiset Generator)).toFinset.min' _) = 0 by
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

private theorem allBase_nextTooth (i : Fin 3) (j : Generator) :
    (allTopBracketHallIndex 1 (by omega) i j).nextTooth =
      min (smallGeneratorIndex i) j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem allBase_predecessor_nextTooth (i : Fin 3) (j : Generator) :
    (allTopBracketHallIndex 1 (by omega) i j).predecessor.nextTooth =
      max (smallGeneratorIndex i) j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem bracket_mem_derived' {N : ℕ} (x y : Source N) :
    ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ (Source N) 1 := by
  change ⁅x, y⁆ ∈ ⁅(⊤ : LieIdeal ℤ (Source N)),
    (⊤ : LieIdeal ℤ (Source N))⁆
  exact LieSubmodule.lie_mem_lie (by simp) (by simp)

private theorem source_right_actions_commute' {N : ℕ} {d x y : Source N}
    (hd : d ∈ LieAlgebra.derivedSeries ℤ (Source N) 1) :
    ⁅⁅d, x⁆, y⁆ = ⁅⁅d, y⁆, x⁆ := by
  have hxy := bracket_mem_derived' (N := N) x y
  have hz : ⁅d, ⁅x, y⁆⁆ = 0 :=
    FreeMetabelian.Free.isMetabelian.bracket_eq_zero hd hxy
  have hj := leibniz_lie d x y
  have hs : ⁅x, ⁅d, y⁆⁆ = -⁅⁅d, y⁆, x⁆ :=
    (lie_skew x ⁅d, y⁆).symm
  rw [hz, hs] at hj
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg]
  exact hj.symm

private theorem rightBracketPow_mem_derived' (N r : ℕ) (hr : 1 ≤ r) :
    rightBracketPow (x4Source N) (x5Source N) r ∈
      LieAlgebra.derivedSeries ℤ (Source N) 1 := by
  cases r with
  | zero => omega
  | succ k => exact bracket_mem_derived' _ _

private theorem allEmbedded_top_hall_base
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator) :
    FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis 2
        (allTopBracketHallIndex 1 (by omega) i j) (by omega) =
      ⁅⁅⁅x4Source N, x5Source N⁆, smallSourceGenerator N i⁆,
        sourceGenerator N j⁆ := by
  rw [FreeMetabelian.Evaluation.hallBracket,
    FreeMetabelian.Evaluation.hallBracket,
    FreeMetabelian.Evaluation.hallBracket]
  rw [allBase_nextTooth, allBase_predecessor_nextTooth]
  change ⁅⁅⁅x4Source N, x5Source N⁆,
      sourceGenerator N (max (smallGeneratorIndex i) j)⁆,
      sourceGenerator N (min (smallGeneratorIndex i) j)⁆ = _
  by_cases hij : smallGeneratorIndex i ≤ j
  · rw [max_eq_right hij, min_eq_left hij]
    exact source_right_actions_commute'
      (bracket_mem_derived' (x4Source N) (x5Source N))
  · have hji : j ≤ smallGeneratorIndex i := le_of_not_ge hij
    rw [max_eq_left hji, min_eq_right hji]
    rfl

private theorem allEmbedded_top_hall_succ
    (N r : ℕ) (hr : 1 ≤ r) (hrN : r < N) (i : Fin 3) (j : Generator) :
    FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis (r + 2)
        (allTopBracketHallIndex (r + 1) (by omega) i j) (by omega) =
      ⁅FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis
          (r + 1) (allTopBracketHallIndex r hr i j) (by omega), x5Source N⁆ := by
  rw [FreeMetabelian.Evaluation.hallBracket,
    allTopBracketHallIndex_predecessor r hr,
    allTopBracketHallIndex_nextTooth r hr]
  rfl

private theorem allLiteral_top_bracket_succ
    (N r : ℕ) (hr : 1 ≤ r) (i : Fin 3) (j : Generator) :
    ⁅⁅rightBracketPow (x4Source N) (x5Source N) (r + 1),
          smallSourceGenerator N i⁆, sourceGenerator N j⁆ =
      ⁅⁅⁅rightBracketPow (x4Source N) (x5Source N) r,
          smallSourceGenerator N i⁆, sourceGenerator N j⁆,
        x5Source N⁆ := by
  rw [rightBracketPow_succ]
  rw [source_right_actions_commute' (rightBracketPow_mem_derived' N r hr)]
  rw [source_right_actions_commute'
    (bracket_mem_derived'
      (rightBracketPow (x4Source N) (x5Source N) r)
      (smallSourceGenerator N i))]

private theorem allEmbedded_top_hall_eq_bracket
    (N r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) (i : Fin 3) (j : Generator) :
    FreeMetabelian.Evaluation.hallBracket (c := N + 3) generatorBasis (r + 1)
        (allTopBracketHallIndex r hr i j) (by omega) =
      ⁅⁅rightBracketPow (x4Source N) (x5Source N) r,
          smallSourceGenerator N i⁆, sourceGenerator N j⁆ := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        exact allEmbedded_top_hall_base N (by omega) i j
      · have hr1 : 1 ≤ r := by omega
        rw [allEmbedded_top_hall_succ N r hr1 (by omega) i j,
          ih hr1 (by omega)]
        exact (allLiteral_top_bracket_succ N r hr1 i j).symm

private theorem topHallSource_allTopBracketHallIndex_eq
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator) :
    topHallSource N (allTopBracketHallIndex N hN i j) =
      ⁅cSource N i, sourceGenerator N j⁆ := by
  rw [topHallSource, FreeMetabelian.hallBasis_apply]
  change FreeMetabelian.Free.incl (⟨N + 2, by omega⟩ : Fin (N + 3))
      (FreeMetabelian.hallVector generatorBasis (N + 1)
        (allTopBracketHallIndex N hN i j)) = _
  rw [← FreeMetabelian.Evaluation.hallBracket_eq_incl]
  exact allEmbedded_top_hall_eq_bracket N N hN (by omega) i j

private theorem allTopBracketHallIndex_ne_uHallIndex_of_extreme
    (N : ℕ) (hN : 1 ≤ N) (i k : Fin 3) (j : Generator)
    (hj : j = 0 ∨ j = 4) :
    allTopBracketHallIndex N hN i j ≠ uHallIndex N hN k := by
  intro heq
  have ht := congrArg
    (fun h : FreeMetabelian.HallIndex Generator (N + 1) =>
      (h.teeth : Multiset Generator)) heq
  simp only [allTopBracketHallIndex, allTopBracketTeeth, uHallIndex,
    topBracketHallIndex, topBracketTeeth] at ht
  rcases hj with rfl | rfl
  · have hc := congrArg (Multiset.count (0 : Generator)) ht
    simp [smallGeneratorIndex] at hc
  · have hc := congrArg (Multiset.count (4 : Generator)) ht
    fin_cases i <;> fin_cases k <;> simp [smallGeneratorIndex] at hc

private theorem topHallSource_injective' (N : ℕ) :
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

private theorem allTopBracketHallIndex_not_exceptional_of_extreme
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator)
    (hj : j = 0 ∨ j = 4) :
    ¬ IsExceptionalTop N (allTopBracketHallIndex N hN i j) := by
  intro hex
  rcases hex with h0 | h1 | h2
  · exact allTopBracketHallIndex_ne_uHallIndex_of_extreme N hN i 0 j hj
      (topHallSource_injective' N
        (h0.trans (topHallSource_uHallIndex_eq N hN 0).symm))
  · exact allTopBracketHallIndex_ne_uHallIndex_of_extreme N hN i 1 j hj
      (topHallSource_injective' N
        (h1.trans (topHallSource_uHallIndex_eq N hN 1).symm))
  · exact allTopBracketHallIndex_ne_uHallIndex_of_extreme N hN i 2 j hj
      (topHallSource_injective' N
        (h2.trans (topHallSource_uHallIndex_eq N hN 2).symm))

private theorem cSource_lie_outerGenerator_mem_relationIdeal
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator)
    (hj : j = 0 ∨ j = 4) :
    ⁅cSource N i, sourceGenerator N j⁆ ∈ relationIdeal N := by
  apply mem_relationIdeal_of_mem_definingRelators
  refine Or.inl (Or.inr ?_)
  exact ⟨allTopBracketHallIndex N hN i j,
    allTopBracketHallIndex_not_exceptional_of_extreme N hN i j hj,
    (topHallSource_allTopBracketHallIndex_eq N hN i j).symm⟩

private theorem cSource_lie_smallSourceGenerator_mem_relationIdeal_of_ne
    (N : ℕ) (hN : 1 ≤ N) {i j : Fin 3} (hij : i ≠ j) :
    ⁅cSource N i, smallSourceGenerator N j⁆ ∈ relationIdeal N := by
  apply mem_relationIdeal_of_mem_definingRelators
  exact Or.inl (Or.inr
    (offDiagonalTopRelators_subset_topHallRelators N hN
      ⟨i, j, hij, rfl⟩))

/-- Every last-generator bracket of a manuscript element `cᵢ` is, modulo the
exact defining ideal, its retained diagonal bracket `uᵢ` and nothing else.
This is the compact source-level top-row interface used in subsequent Hall
normal-form arguments. -/
theorem cSource_lie_sourceGenerator_sub_diagonal_mem_relationIdeal
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator) :
    ⁅cSource N i, sourceGenerator N j⁆ -
        (if j = smallGeneratorIndex i then uSource N i else 0) ∈
      relationIdeal N := by
  by_cases hji : j = smallGeneratorIndex i
  · rw [if_pos hji, hji]
    simp only [uSource, smallSourceGenerator, smallGeneratorIndex, sub_self,
      LieSubmodule.zero_mem]
  · rw [if_neg hji, sub_zero]
    fin_cases j
    · exact cSource_lie_outerGenerator_mem_relationIdeal N hN i 0 (Or.inl rfl)
    · have hi : i ≠ (0 : Fin 3) := by
        intro hi
        subst i
        exact hji rfl
      simpa only [smallSourceGenerator] using
        cSource_lie_smallSourceGenerator_mem_relationIdeal_of_ne N hN hi
    · have hi : i ≠ (1 : Fin 3) := by
        intro hi
        subst i
        exact hji rfl
      simpa only [smallSourceGenerator] using
        cSource_lie_smallSourceGenerator_mem_relationIdeal_of_ne N hN hi
    · have hi : i ≠ (2 : Fin 3) := by
        intro hi
        subst i
        exact hji rfl
      simpa only [smallSourceGenerator] using
        cSource_lie_smallSourceGenerator_mem_relationIdeal_of_ne N hN hi
    · exact cSource_lie_outerGenerator_mem_relationIdeal N hN i 4 (Or.inr rfl)

theorem sourceDetector_topHallRelator (N : ℕ) (hN : 1 ≤ N)
    {z : Source N} (hz : z ∈ topHallRelators N) :
    ∀ xs : List (Source N), sourceDetector N hN (rightOrbit z xs) = 0 := by
  rcases hz with ⟨h, hne, rfl⟩
  intro xs
  cases xs with
  | nil => exact sourceDetector_topHallSource_of_not_exceptional N hN h hne
  | cons x xs =>
      rw [rightOrbit_cons, topHallSource_lie_eq_zero, rightOrbit_zero, map_zero]

theorem uSource_lie_eq_zero (N : ℕ) (hN : 1 ≤ N)
    (i : Fin 3) (z : Source N) : ⁅uSource N i, z⁆ = 0 := by
  rw [← topHallSource_uHallIndex_eq N hN i]
  exact topHallSource_lie_eq_zero N _ z

theorem sourceDetector_exceptionalRelator (N : ℕ) (hN : 1 ≤ N)
    {z : Source N} (hz : z ∈ exceptionalRelators N) :
    ∀ xs : List (Source N), sourceDetector N hN (rightOrbit z xs) = 0 := by
  simp only [exceptionalRelators, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  all_goals intro xs
  all_goals cases xs with
  | nil =>
      simp [sourceDetector_uSource, map_sub, map_zsmul]
      change (0 : ZMod 256) = 0
      rfl
  | cons x xs =>
      rw [rightOrbit_cons]
      simp only [sub_lie, zsmul_lie, uSource_lie_eq_zero N hN,
        smul_zero, sub_zero, rightOrbit_zero, map_zero]

/-! ### The three shifted rows, including all of their Lie consequences -/

/-- The coefficient of `xᵢ` in the corresponding shifted row. -/
private def rowScale : Fin 3 → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 64

private theorem pairCoordinate_eq_zero_of_mem_lowerCentralSeries_two
    (N : ℕ) (i j : Fin 3) (hij : i < j) {z : Source N}
    (hz : z ∈ LieModule.lowerCentralSeries ℤ (Source N) (Source N) 2) :
    pairCoordinate N i j hij z = 0 := by
  rw [pairCoordinate, LinearMap.comp_apply]
  have ht : z ∈ FreeMetabelian.Free.tail 2 :=
    FreeMetabelian.Free.lowerCentralSeries_le_tail 2 hz
  have hp : FreeMetabelian.Free.weightProject 1 (by omega) z = 0 := by
    change z (⟨1, by omega⟩ : Fin (N + 3)) = 0
    exact ht ⟨1, by omega⟩ (by norm_num)
  have hc := congrArg
    ((FreeMetabelian.hallBasis generatorBasis 0).coord
      (pairHallIndex i j hij)) hp
  exact hc.trans
    ((FreeMetabelian.hallBasis generatorBasis 0).coord
      (pairHallIndex i j hij)).map_zero

/-- Once a bracket word is at least three letters deep and contains `xᵢ`,
the corresponding row coefficient kills every coordinate read by the
detector.  The three products are `4·64=16·16=64·4=256`. -/
private theorem sourceDetector_rowScale_smul_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) {z : Source N}
    (hz : z ∈ LieModule.lowerCentralSeries ℤ (Source N) (Source N) 2)
    (herase : eraseGenerator N (smallGeneratorIndex i) z = 0) :
    sourceDetector N hN (rowScale i • z) = 0 := by
  have hp12 := pairCoordinate_eq_zero_of_mem_lowerCentralSeries_two
    N 0 1 (by decide) hz
  have hp13 := pairCoordinate_eq_zero_of_mem_lowerCentralSeries_two
    N 0 2 (by decide) hz
  have hp23 := pairCoordinate_eq_zero_of_mem_lowerCentralSeries_two
    N 1 2 (by decide) hz
  fin_cases i
  · have he1 := exceptionalCoordinate_eq_zero_of_erase_eq_zero
      N hN 0 1 (by decide) herase
    have he2 := exceptionalCoordinate_eq_zero_of_erase_eq_zero
      N hN 0 2 (by decide) herase
    simp [sourceDetector, rowScale, castCoordinate, gradedZModCoordinate,
      LinearMap.add_apply, LinearMap.smul_apply, hp12, hp13, hp23, he1, he2]
    rw [← mul_assoc]
    rw [show (4 : ZMod 256) * 64 = 0 by decide, zero_mul]
  · have he0 := exceptionalCoordinate_eq_zero_of_erase_eq_zero
      N hN 1 0 (by decide) herase
    have he2 := exceptionalCoordinate_eq_zero_of_erase_eq_zero
      N hN 1 2 (by decide) herase
    simp [sourceDetector, rowScale, castCoordinate, gradedZModCoordinate,
      LinearMap.add_apply, LinearMap.smul_apply, hp12, hp13, hp23, he0, he2]
    rw [← mul_assoc]
    rw [show (16 : ZMod 256) * 16 = 0 by decide, zero_mul]
  · have he0 := exceptionalCoordinate_eq_zero_of_erase_eq_zero
      N hN 2 0 (by decide) herase
    have he1 := exceptionalCoordinate_eq_zero_of_erase_eq_zero
      N hN 2 1 (by decide) herase
    simp [sourceDetector, rowScale, castCoordinate, gradedZModCoordinate,
      LinearMap.add_apply, LinearMap.smul_apply, hp12, hp13, hp23, he0, he1]
    rw [← mul_assoc]
    rw [show (64 : ZMod 256) * 4 = 0 by decide, zero_mul]

private theorem map_rightOrbit {A B : Type*} [LieRing A] [LieRing B]
    (f : A →ₗ⁅ℤ⁆ B) (z : A) : ∀ xs : List A,
    f (rightOrbit z xs) = rightOrbit (f z) (xs.map f)
  | [] => rfl
  | x :: xs => by
      rw [rightOrbit_cons, map_rightOrbit f ⁅z, x⁆ xs,
        List.map_cons, rightOrbit_cons, LieHom.map_lie]

private theorem bracket_mem_lowerCentralSeries_one
    {A : Type*} [LieRing A] (x y : A) :
    ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℤ A A 1 := by
  rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
  exact LieSubmodule.lie_mem_lie (by simp) (by simp)

private theorem doubleBracket_mem_lowerCentralSeries_two
    {A : Type*} [LieRing A] (x y z : A) :
    ⁅⁅x, y⁆, z⁆ ∈ LieModule.lowerCentralSeries ℤ A A 2 := by
  rw [show 2 = Nat.succ 1 by omega, LieModule.lowerCentralSeries_succ,
    LieSubmodule.lie_comm]
  exact LieSubmodule.lie_mem_lie
    (bracket_mem_lowerCentralSeries_one x y) (by simp)

private theorem rightOrbit_preserves_lowerCentralSeries_two
    {A : Type*} [LieRing A] {z : A}
    (hz : z ∈ LieModule.lowerCentralSeries ℤ A A 2) :
    ∀ xs : List A,
      rightOrbit z xs ∈ LieModule.lowerCentralSeries ℤ A A 2 := by
  intro xs
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
      rw [rightOrbit_cons]
      apply ih
      have hnext : ⁅z, x⁆ ∈ LieModule.lowerCentralSeries ℤ A A 3 := by
        rw [show 3 = Nat.succ 2 by omega,
          LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
        exact LieSubmodule.lie_mem_lie hz (by simp)
      exact LieModule.antitone_lowerCentralSeries ℤ A A (show 2 ≤ 3 by omega) hnext

private theorem eraseGenerator_deepOrbit_eq_zero
    (N : ℕ) (i : Fin 3) (x y : Source N) (xs : List (Source N)) :
    eraseGenerator N (smallGeneratorIndex i)
        (rightOrbit ⁅⁅smallSourceGenerator N i, x⁆, y⁆ xs) = 0 := by
  rw [map_rightOrbit]
  rw [LieHom.map_lie, LieHom.map_lie]
  change rightOrbit
      ⁅⁅eraseGenerator N (smallGeneratorIndex i)
            (smallSourceGenerator N i),
          eraseGenerator N (smallGeneratorIndex i) x⁆,
        eraseGenerator N (smallGeneratorIndex i) y⁆
      (xs.map (eraseGenerator N (smallGeneratorIndex i))) = 0
  change rightOrbit ⁅⁅eraseGenerator N (smallGeneratorIndex i)
      (sourceGenerator N (smallGeneratorIndex i)), _⁆, _⁆ _ = 0
  rw [eraseGenerator_sourceGenerator]
  simp [rightOrbit_zero]

private theorem sourceDetector_rowScale_deepOrbit_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3)
    (x y : Source N) (xs : List (Source N)) :
    sourceDetector N hN
      (rowScale i • rightOrbit ⁅⁅smallSourceGenerator N i, x⁆, y⁆ xs) = 0 := by
  apply sourceDetector_rowScale_smul_eq_zero N hN i
  · apply rightOrbit_preserves_lowerCentralSeries_two
    exact doubleBracket_mem_lowerCentralSeries_two _ _ _
  · exact eraseGenerator_deepOrbit_eq_zero N i x y xs

/-! The weight-two brackets with the two outer generators are Hall words not
read by the three selected pair coordinates. -/

private def lowOuterPairHallIndex (i : Fin 3) :
    FreeMetabelian.HallIndex Generator 0 where
  head := smallGeneratorIndex i
  pivot := 0
  teeth := Sym.mk 0 rfl
  pivot_lt_head := by fin_cases i <;> decide
  pivot_le_teeth := by simp

private def highOuterPairHallIndex (i : Fin 3) :
    FreeMetabelian.HallIndex Generator 0 where
  head := 4
  pivot := smallGeneratorIndex i
  teeth := Sym.mk 0 rfl
  pivot_lt_head := by fin_cases i <;> decide
  pivot_le_teeth := by simp

private def outerPairHallSource (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator 0) : Source N :=
  FreeMetabelian.Free.inclComponent 0 (by omega)
    (FreeMetabelian.hallBasis generatorBasis 0 h)

private theorem pairCoordinate_outerPairHallSource (N : ℕ)
    (i j : Fin 3) (hij : i < j)
    (h : FreeMetabelian.HallIndex Generator 0) :
    pairCoordinate N i j hij (outerPairHallSource N h) =
      if pairHallIndex i j hij = h then 1 else 0 := by
  rw [pairCoordinate, LinearMap.comp_apply, Module.Basis.coord_apply]
  have hp : FreeMetabelian.Free.weightProject 1 (by omega)
      (outerPairHallSource N h) =
      FreeMetabelian.hallBasis generatorBasis 0 h := by
    simp only [outerPairHallSource, FreeMetabelian.Free.weightProject,
      FreeMetabelian.Free.inclComponent, FreeMetabelian.hallBasis_apply]
    change (FreeMetabelian.Free.incl
        (⟨1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallVector generatorBasis 0 h))
        ⟨1, by omega⟩ = _
    exact FreeMetabelian.Free.incl_apply_same _ _
  calc
    _ = ((FreeMetabelian.hallBasis generatorBasis 0).repr
        (FreeMetabelian.hallBasis generatorBasis 0 h))
          (pairHallIndex i j hij) :=
      congrArg (fun z ↦ ((FreeMetabelian.hallBasis generatorBasis 0).repr z)
        (pairHallIndex i j hij)) hp
    _ = _ := by
      classical
      rw [Module.Basis.repr_self]
      simp [Finsupp.single_apply, eq_comm]

private theorem outerPairHallSource_eq_bracket (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator 0) :
    outerPairHallSource N h =
      ⁅sourceGenerator N h.head, sourceGenerator N h.pivot⁆ := by
  have he := FreeMetabelian.Evaluation.hallBracket_eq_incl
    (c := N + 3) generatorBasis 0 h (by omega)
  have hlhs : outerPairHallSource N h =
      FreeMetabelian.Free.incl
        (⟨1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallVector generatorBasis 0 h) := by
    unfold outerPairHallSource FreeMetabelian.Free.inclComponent
    apply congrArg (FreeMetabelian.Free.incl
      (⟨1, by omega⟩ : Fin (N + 3)))
    rw [FreeMetabelian.hallBasis_apply]
    rfl
  rw [hlhs, ← he]
  rfl

private def outerPairGradedIndex (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator 0) :
    (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val :=
  ⟨⟨1, by omega⟩, h⟩

private theorem hallGradedBasis_outerPairGradedIndex (N : ℕ)
    (h : FreeMetabelian.HallIndex Generator 0) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis
        (outerPairGradedIndex N h) = outerPairHallSource N h := by
  rw [hallGradedBasis_apply]
  change FreeMetabelian.Free.incl (⟨1, by omega⟩ : Fin (N + 3))
      (FreeMetabelian.Free.pieceBasis generatorBasis 1 h) = _
  rw [FreeMetabelian.Free.pieceBasis]
  have he :
      (FreeMetabelian.hallBasis generatorBasis 0).equivFun.toAddEquiv.toIntLinearEquiv =
        (FreeMetabelian.hallBasis generatorBasis 0).equivFun :=
    LinearEquiv.toAddEquiv_toIntLinearEquiv
      (FreeMetabelian.hallBasis generatorBasis 0).equivFun
  have hbEq : Module.Basis.ofEquivFun
        (FreeMetabelian.hallBasis generatorBasis 0).equivFun.toAddEquiv.toIntLinearEquiv =
      FreeMetabelian.hallBasis generatorBasis 0 := by
    rw [he, Module.Basis.ofEquivFun_equivFun]
  have hpEq := congrArg (fun b ↦ b h) hbEq
  calc
    _ = FreeMetabelian.Free.incl (⟨1, by omega⟩ : Fin (N + 3))
        (FreeMetabelian.hallBasis generatorBasis 0 h) :=
      congrArg (FreeMetabelian.Free.incl
        (⟨1, by omega⟩ : Fin (N + 3))) hpEq
    _ = outerPairHallSource N h := by
      unfold outerPairHallSource FreeMetabelian.Free.inclComponent
      apply congrArg (FreeMetabelian.Free.incl
        (⟨1, by omega⟩ : Fin (N + 3)))
      rfl

private theorem exceptionalCoordinate_outerPairHallSource
    (N : ℕ) (hN : 1 ≤ N) (k : Fin 3)
    (h : FreeMetabelian.HallIndex Generator 0) :
    gradedCoordinate N (topGradedIndex N (uHallIndex N hN k))
        (outerPairHallSource N h) = 0 := by
  rw [← hallGradedBasis_outerPairGradedIndex]
  apply gradedCoordinate_hallGradedBasis_of_ne
  intro heq
  have hv := congrArg (fun p ↦ p.1.val) heq
  simp [topGradedIndex, outerPairGradedIndex] at hv

private theorem sourceDetector_lie_small_outer_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator)
    (hj : j = 0 ∨ j = 4) :
    sourceDetector N hN
      ⁅smallSourceGenerator N i, sourceGenerator N j⁆ = 0 := by
  rcases hj with rfl | rfl
  · have hs : ⁅smallSourceGenerator N i, sourceGenerator N 0⁆ =
        outerPairHallSource N (lowOuterPairHallIndex i) := by
      change ⁅sourceGenerator N (smallGeneratorIndex i), sourceGenerator N 0⁆ = _
      exact (outerPairHallSource_eq_bracket N (lowOuterPairHallIndex i)).symm
    rw [hs]
    fin_cases i <;>
      simp [sourceDetector, castCoordinate, gradedZModCoordinate,
        LinearMap.add_apply, LinearMap.smul_apply,
        pairCoordinate_outerPairHallSource,
        exceptionalCoordinate_outerPairHallSource,
        pairHallIndex, lowOuterPairHallIndex, smallGeneratorIndex]
  · have hs : ⁅smallSourceGenerator N i, sourceGenerator N 4⁆ =
        -outerPairHallSource N (highOuterPairHallIndex i) := by
      rw [outerPairHallSource_eq_bracket]
      change ⁅sourceGenerator N (smallGeneratorIndex i), sourceGenerator N 4⁆ =
        -⁅sourceGenerator N 4, sourceGenerator N (smallGeneratorIndex i)⁆
      exact (lie_skew _ _).symm
    rw [hs, map_neg]
    fin_cases i <;>
      simp [sourceDetector, castCoordinate, gradedZModCoordinate,
        LinearMap.add_apply, LinearMap.smul_apply,
        pairCoordinate_outerPairHallSource,
        exceptionalCoordinate_outerPairHallSource,
        pairHallIndex, highOuterPairHallIndex, smallGeneratorIndex]

private def smallPairDetectorValue : Fin 3 → Fin 3 → ZMod 256
  | 0, 0 => 0
  | 0, 1 => -4
  | 0, 2 => -2
  | 1, 0 => 4
  | 1, 1 => 0
  | 1, 2 => -1
  | 2, 0 => 2
  | 2, 1 => 1
  | 2, 2 => 0

private theorem sourceDetector_lie_smallSourceGenerator
    (N : ℕ) (hN : 1 ≤ N) (i j : Fin 3) :
    sourceDetector N hN
      ⁅smallSourceGenerator N i, smallSourceGenerator N j⁆ =
        smallPairDetectorValue i j := by
  fin_cases i <;> fin_cases j
  all_goals simp only [smallPairDetectorValue]
  · simp
  · exact sourceDetector_b12Source N hN
  · exact sourceDetector_b13Source N hN
  · rw [← lie_skew, map_neg]
    change -sourceDetector N hN (b12Source N) = 4
    rw [sourceDetector_b12Source]
    decide
  · simp
  · exact sourceDetector_b23Source N hN
  · rw [← lie_skew, map_neg]
    change -sourceDetector N hN (b13Source N) = 2
    rw [sourceDetector_b13Source]
    decide
  · rw [← lie_skew, map_neg]
    change -sourceDetector N hN (b23Source N) = 1
    rw [sourceDetector_b23Source]
    decide
  · simp

private def diagonalDetectorValue : Fin 3 → ZMod 256
  | 0 => 64
  | 1 => 16
  | 2 => 4

private theorem sourceDetector_cSource_lie_smallSourceGenerator
    (N : ℕ) (hN : 1 ≤ N) (i j : Fin 3) :
    sourceDetector N hN ⁅cSource N i, smallSourceGenerator N j⁆ =
      if i = j then diagonalDetectorValue i else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    change sourceDetector N hN (uSource N i) = diagonalDetectorValue i
    rw [sourceDetector_uSource]
    fin_cases i <;> rfl
  · rw [← topHallSource_topBracketHallIndex_eq N hN i j]
    rw [sourceDetector_topHallSource_of_not_exceptional N hN _
      (topBracketHallIndex_not_exceptional N hN hij)]
    simp [hij]

private theorem sourceDetector_cSource_lie_outer_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator)
    (hj : j = 0 ∨ j = 4) :
    sourceDetector N hN ⁅cSource N i, sourceGenerator N j⁆ = 0 := by
  rw [← topHallSource_allTopBracketHallIndex_eq N hN i j]
  exact sourceDetector_topHallSource_of_not_exceptional N hN _
    (allTopBracketHallIndex_not_exceptional_of_extreme N hN i j hj)

private theorem sourceDetector_r1Source_lie_sourceGenerator
    (N : ℕ) (hN : 1 ≤ N) (j : Generator) :
    sourceDetector N hN ⁅r1Source N, sourceGenerator N j⁆ = 0 := by
  fin_cases j
  all_goals
    simp only [r1Source, add_lie, zsmul_lie, map_add, map_zsmul,
      x1Source, c1Source, c2Source, c3Source]
  · change (4 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 0, sourceGenerator N 0⁆ +
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, sourceGenerator N 0⁆ +
      sourceDetector N hN ⁅cSource N 1, sourceGenerator N 0⁆ = 0
    rw [sourceDetector_lie_small_outer_eq_zero N hN 0 0 (Or.inl rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 2 0 (Or.inl rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 1 0 (Or.inl rfl)]
    simp
  · change (4 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 0, smallSourceGenerator N 0⁆ +
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, smallSourceGenerator N 0⁆ +
      sourceDetector N hN ⁅cSource N 1, smallSourceGenerator N 0⁆ = 0
    rw [sourceDetector_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator]
    decide
  · change (4 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 0, smallSourceGenerator N 1⁆ +
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, smallSourceGenerator N 1⁆ +
      sourceDetector N hN ⁅cSource N 1, smallSourceGenerator N 1⁆ = 0
    rw [sourceDetector_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator]
    decide
  · change (4 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 0, smallSourceGenerator N 2⁆ +
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, smallSourceGenerator N 2⁆ +
      sourceDetector N hN ⁅cSource N 1, smallSourceGenerator N 2⁆ = 0
    rw [sourceDetector_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator]
    decide
  · change (4 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 0, sourceGenerator N 4⁆ +
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, sourceGenerator N 4⁆ +
      sourceDetector N hN ⁅cSource N 1, sourceGenerator N 4⁆ = 0
    rw [sourceDetector_lie_small_outer_eq_zero N hN 0 4 (Or.inr rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 2 4 (Or.inr rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 1 4 (Or.inr rfl)]
    simp

private theorem sourceDetector_r2Source_lie_sourceGenerator
    (N : ℕ) (hN : 1 ≤ N) (j : Generator) :
    sourceDetector N hN ⁅r2Source N, sourceGenerator N j⁆ = 0 := by
  fin_cases j
  all_goals
    simp only [r2Source, sub_lie, add_lie, zsmul_lie, map_sub, map_add,
      map_zsmul, x2Source, c1Source, c2Source, c3Source]
  · change (16 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 1, sourceGenerator N 0⁆ +
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, sourceGenerator N 0⁆ -
      sourceDetector N hN ⁅cSource N 0, sourceGenerator N 0⁆ = 0
    rw [sourceDetector_lie_small_outer_eq_zero N hN 1 0 (Or.inl rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 2 0 (Or.inl rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 0 0 (Or.inl rfl)]
    simp
  · change (16 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 1, smallSourceGenerator N 0⁆ +
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, smallSourceGenerator N 0⁆ -
      sourceDetector N hN ⁅cSource N 0, smallSourceGenerator N 0⁆ = 0
    rw [sourceDetector_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator]
    decide
  · change (16 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 1, smallSourceGenerator N 1⁆ +
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, smallSourceGenerator N 1⁆ -
      sourceDetector N hN ⁅cSource N 0, smallSourceGenerator N 1⁆ = 0
    rw [sourceDetector_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator]
    decide
  · change (16 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 1, smallSourceGenerator N 2⁆ +
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, smallSourceGenerator N 2⁆ -
      sourceDetector N hN ⁅cSource N 0, smallSourceGenerator N 2⁆ = 0
    rw [sourceDetector_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator]
    decide
  · change (16 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 1, sourceGenerator N 4⁆ +
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 2, sourceGenerator N 4⁆ -
      sourceDetector N hN ⁅cSource N 0, sourceGenerator N 4⁆ = 0
    rw [sourceDetector_lie_small_outer_eq_zero N hN 1 4 (Or.inr rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 2 4 (Or.inr rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 0 4 (Or.inr rfl)]
    simp

private theorem sourceDetector_r3Source_lie_sourceGenerator
    (N : ℕ) (hN : 1 ≤ N) (j : Generator) :
    sourceDetector N hN ⁅r3Source N, sourceGenerator N j⁆ = 0 := by
  fin_cases j
  all_goals
    simp only [r3Source, sub_lie, zsmul_lie, map_sub, map_zsmul,
      x3Source, c1Source, c2Source, c3Source]
  · change (64 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 2, sourceGenerator N 0⁆ -
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 1, sourceGenerator N 0⁆ -
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 0, sourceGenerator N 0⁆ = 0
    rw [sourceDetector_lie_small_outer_eq_zero N hN 2 0 (Or.inl rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 1 0 (Or.inl rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 0 0 (Or.inl rfl)]
    simp
  · change (64 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 2, smallSourceGenerator N 0⁆ -
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 1, smallSourceGenerator N 0⁆ -
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 0, smallSourceGenerator N 0⁆ = 0
    rw [sourceDetector_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator]
    decide
  · change (64 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 2, smallSourceGenerator N 1⁆ -
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 1, smallSourceGenerator N 1⁆ -
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 0, smallSourceGenerator N 1⁆ = 0
    rw [sourceDetector_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator]
    decide
  · change (64 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 2, smallSourceGenerator N 2⁆ -
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 1, smallSourceGenerator N 2⁆ -
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 0, smallSourceGenerator N 2⁆ = 0
    rw [sourceDetector_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator,
      sourceDetector_cSource_lie_smallSourceGenerator]
    decide
  · change (64 : ℤ) • sourceDetector N hN
        ⁅smallSourceGenerator N 2, sourceGenerator N 4⁆ -
      (4 : ℤ) • sourceDetector N hN
        ⁅cSource N 1, sourceGenerator N 4⁆ -
      (2 : ℤ) • sourceDetector N hN
        ⁅cSource N 0, sourceGenerator N 4⁆ = 0
    rw [sourceDetector_lie_small_outer_eq_zero N hN 2 4 (Or.inr rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 1 4 (Or.inr rfl),
      sourceDetector_cSource_lie_outer_eq_zero N hN 0 4 (Or.inr rfl)]
    simp

private theorem sourceDetector_rowScale_lie_derived_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (y : Source N)
    (hy : y ∈ LieModule.lowerCentralSeries ℤ (Source N) (Source N) 1) :
    sourceDetector N hN
      (rowScale i • ⁅smallSourceGenerator N i, y⁆) = 0 := by
  apply sourceDetector_rowScale_smul_eq_zero N hN i
  · rw [show 2 = Nat.succ 1 by omega,
      LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp) hy
  · rw [LieHom.map_lie]
    change ⁅eraseGenerator N (smallGeneratorIndex i)
        (sourceGenerator N (smallGeneratorIndex i)),
      eraseGenerator N (smallGeneratorIndex i) y⁆ = 0
    rw [eraseGenerator_sourceGenerator]
    simp

private theorem cSource_lie_eq_zero_of_mem_derived
    (N : ℕ) (i : Fin 3) (y : Source N)
    (hy : y ∈ LieAlgebra.derivedSeries ℤ (Source N) 1) :
    ⁅cSource N i, y⁆ = 0 := by
  exact FreeMetabelian.Free.isMetabelian.bracket_eq_zero
    (bracket_mem_derived' _ _) hy

private theorem sourceDetector_r1Source_lie_of_mem_derived
    (N : ℕ) (hN : 1 ≤ N) (y : Source N)
    (hy : y ∈ LieAlgebra.derivedSeries ℤ (Source N) 1) :
    sourceDetector N hN ⁅r1Source N, y⁆ = 0 := by
  have hc3 : ⁅c3Source N, y⁆ = 0 :=
    cSource_lie_eq_zero_of_mem_derived N 2 y hy
  have hc2 : ⁅c2Source N, y⁆ = 0 :=
    cSource_lie_eq_zero_of_mem_derived N 1 y hy
  rw [r1Source, add_lie, add_lie, zsmul_lie, zsmul_lie,
    hc3, hc2]
  simp only [smul_zero, add_zero]
  rw [map_zsmul]
  change (4 : ℤ) • sourceDetector N hN
    ⁅smallSourceGenerator N 0, y⁆ = 0
  simpa [rowScale] using
    sourceDetector_rowScale_lie_derived_eq_zero N hN 0 y hy

private theorem sourceDetector_r2Source_lie_of_mem_derived
    (N : ℕ) (hN : 1 ≤ N) (y : Source N)
    (hy : y ∈ LieAlgebra.derivedSeries ℤ (Source N) 1) :
    sourceDetector N hN ⁅r2Source N, y⁆ = 0 := by
  have hc3 : ⁅c3Source N, y⁆ = 0 :=
    cSource_lie_eq_zero_of_mem_derived N 2 y hy
  have hc1 : ⁅c1Source N, y⁆ = 0 :=
    cSource_lie_eq_zero_of_mem_derived N 0 y hy
  rw [r2Source, sub_lie, add_lie, zsmul_lie, zsmul_lie,
    hc3, hc1]
  simp only [smul_zero, add_zero, sub_zero]
  rw [map_zsmul]
  change (16 : ℤ) • sourceDetector N hN
    ⁅smallSourceGenerator N 1, y⁆ = 0
  simpa [rowScale] using
    sourceDetector_rowScale_lie_derived_eq_zero N hN 1 y hy

private theorem sourceDetector_r3Source_lie_of_mem_derived
    (N : ℕ) (hN : 1 ≤ N) (y : Source N)
    (hy : y ∈ LieAlgebra.derivedSeries ℤ (Source N) 1) :
    sourceDetector N hN ⁅r3Source N, y⁆ = 0 := by
  have hc2 : ⁅c2Source N, y⁆ = 0 :=
    cSource_lie_eq_zero_of_mem_derived N 1 y hy
  have hc1 : ⁅c1Source N, y⁆ = 0 :=
    cSource_lie_eq_zero_of_mem_derived N 0 y hy
  rw [r3Source, sub_lie, sub_lie, zsmul_lie, zsmul_lie, zsmul_lie,
    hc2, hc1]
  simp only [smul_zero, sub_zero]
  rw [map_zsmul]
  change (64 : ℤ) • sourceDetector N hN
    ⁅smallSourceGenerator N 2, y⁆ = 0
  simpa [rowScale] using
    sourceDetector_rowScale_lie_derived_eq_zero N hN 2 y hy

private theorem hallGradedBasis_zero_eq_sourceGenerator (N : ℕ)
    (i : Generator) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis
        (⟨⟨0, by omega⟩, i⟩ :
          (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val) =
      sourceGenerator N i := by
  rw [hallGradedBasis_apply]
  rfl

private theorem hallGradedBasis_mem_derived_of_succ
    (N q : ℕ) (hs : q + 1 < N + 3)
    (p : FreeMetabelian.Free.PieceIndex Generator (q + 1)) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis
        (⟨⟨q + 1, hs⟩, p⟩ :
          (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val) ∈
      LieAlgebra.derivedSeries ℤ (Source N) 1 := by
  have hp := FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
    (c := N + 3) generatorBasis (q + 1) hs
      (FreeMetabelian.Free.pieceBasis generatorBasis (q + 1) p)
  have hp1 : FreeMetabelian.Free.weightIncl (q + 1) hs
        (FreeMetabelian.Free.pieceBasis generatorBasis (q + 1) p) ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) 1 :=
    LieModule.antitone_lowerCentralSeries ℤ (Source N) (Source N)
      (by omega) hp
  rw [hallGradedBasis_apply]
  exact hp1

private def bracketDetector (N : ℕ) (hN : 1 ≤ N) (r : Source N) :
    Source N →ₗ[ℤ] ZMod 256 where
  toFun y := sourceDetector N hN ⁅r, y⁆
  map_add' x y := by rw [lie_add, map_add]
  map_smul' n y := by simp only [lie_zsmul, map_zsmul, RingHom.id_apply]

private theorem sourceDetector_r1Source_lie (N : ℕ) (hN : 1 ≤ N)
    (y : Source N) : sourceDetector N hN ⁅r1Source N, y⁆ = 0 := by
  have hf : bracketDetector N hN (r1Source N) = 0 := by
    apply (FreeMetabelian.Free.hallGradedBasis generatorBasis).ext
    rintro ⟨⟨s, hs⟩, p⟩
    cases s with
    | zero =>
        change sourceDetector N hN
          ⁅r1Source N,
            FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨0, hs⟩, p⟩ :
                (s : Fin (N + 3)) ×
                  FreeMetabelian.Free.PieceIndex Generator s.val)⁆ = 0
        rw [hallGradedBasis_zero_eq_sourceGenerator]
        exact sourceDetector_r1Source_lie_sourceGenerator N hN p
    | succ q =>
        change sourceDetector N hN
          ⁅r1Source N,
            FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨q + 1, hs⟩, p⟩ :
                (s : Fin (N + 3)) ×
                  FreeMetabelian.Free.PieceIndex Generator s.val)⁆ = 0
        exact sourceDetector_r1Source_lie_of_mem_derived N hN _
          (hallGradedBasis_mem_derived_of_succ N q hs p)
  exact LinearMap.congr_fun hf y

private theorem sourceDetector_r2Source_lie (N : ℕ) (hN : 1 ≤ N)
    (y : Source N) : sourceDetector N hN ⁅r2Source N, y⁆ = 0 := by
  have hf : bracketDetector N hN (r2Source N) = 0 := by
    apply (FreeMetabelian.Free.hallGradedBasis generatorBasis).ext
    rintro ⟨⟨s, hs⟩, p⟩
    cases s with
    | zero =>
        change sourceDetector N hN
          ⁅r2Source N,
            FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨0, hs⟩, p⟩ :
                (s : Fin (N + 3)) ×
                  FreeMetabelian.Free.PieceIndex Generator s.val)⁆ = 0
        rw [hallGradedBasis_zero_eq_sourceGenerator]
        exact sourceDetector_r2Source_lie_sourceGenerator N hN p
    | succ q =>
        change sourceDetector N hN
          ⁅r2Source N,
            FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨q + 1, hs⟩, p⟩ :
                (s : Fin (N + 3)) ×
                  FreeMetabelian.Free.PieceIndex Generator s.val)⁆ = 0
        exact sourceDetector_r2Source_lie_of_mem_derived N hN _
          (hallGradedBasis_mem_derived_of_succ N q hs p)
  exact LinearMap.congr_fun hf y

private theorem sourceDetector_r3Source_lie (N : ℕ) (hN : 1 ≤ N)
    (y : Source N) : sourceDetector N hN ⁅r3Source N, y⁆ = 0 := by
  have hf : bracketDetector N hN (r3Source N) = 0 := by
    apply (FreeMetabelian.Free.hallGradedBasis generatorBasis).ext
    rintro ⟨⟨s, hs⟩, p⟩
    cases s with
    | zero =>
        change sourceDetector N hN
          ⁅r3Source N,
            FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨0, hs⟩, p⟩ :
                (s : Fin (N + 3)) ×
                  FreeMetabelian.Free.PieceIndex Generator s.val)⁆ = 0
        rw [hallGradedBasis_zero_eq_sourceGenerator]
        exact sourceDetector_r3Source_lie_sourceGenerator N hN p
    | succ q =>
        change sourceDetector N hN
          ⁅r3Source N,
            FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨q + 1, hs⟩, p⟩ :
                (s : Fin (N + 3)) ×
                  FreeMetabelian.Free.PieceIndex Generator s.val)⁆ = 0
        exact sourceDetector_r3Source_lie_of_mem_derived N hN _
          (hallGradedBasis_mem_derived_of_succ N q hs p)
  exact LinearMap.congr_fun hf y

/-! ### The value on the shifted rows themselves -/

private theorem gradedCoordinate_repr_apply (N : ℕ) (z : Source N)
    (p : (s : Fin (N + 3)) ×
      FreeMetabelian.Free.PieceIndex Generator s.val) :
    gradedCoordinate N p z =
      (FreeMetabelian.Free.pieceBasis generatorBasis p.1.val).repr
        (z p.1) p.2 := by
  classical
  rw [gradedCoordinate, FreeMetabelian.Free.hallGradedBasis]
  let bPi := Pi.basis (fun i : Fin (N + 3) ↦
    FreeMetabelian.Free.pieceBasis generatorBasis i.val)
  have he : bPi.equivFun.toAddEquiv.toIntLinearEquiv = bPi.equivFun :=
    LinearEquiv.toAddEquiv_toIntLinearEquiv bPi.equivFun
  rw [he, Module.Basis.ofEquivFun_equivFun]
  rfl

private theorem sourceDetector_weightIncl_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hs : s < N + 3)
    (x : FreeMetabelian.Piece GeneratorModule s)
    (hsPair : s ≠ 1) (hsTop : s ≠ N + 2) :
    sourceDetector N hN (FreeMetabelian.Free.weightIncl s hs x) = 0 := by
  have hpair : ∀ (i j : Fin 3) (hij : i < j),
      pairCoordinate N i j hij
          (FreeMetabelian.Free.weightIncl s hs x) = 0 := by
    intro i j hij
    rw [pairCoordinate, LinearMap.comp_apply]
    have hp : FreeMetabelian.Free.weightProject 1 (by omega)
        (FreeMetabelian.Free.weightIncl s hs x) = 0 := by
      change FreeMetabelian.Free.incl (⟨s, hs⟩ : Fin (N + 3)) x
        (⟨1, by omega⟩ : Fin (N + 3)) = 0
      apply FreeMetabelian.Free.incl_apply_of_ne
      intro heq
      apply hsPair
      exact (congrArg Fin.val heq).symm
    have hc := congrArg
      ((FreeMetabelian.hallBasis generatorBasis 0).coord
        (pairHallIndex i j hij)) hp
    exact hc.trans
      ((FreeMetabelian.hallBasis generatorBasis 0).coord
        (pairHallIndex i j hij)).map_zero
  have htop : ∀ k : Fin 3,
      gradedCoordinate N (topGradedIndex N (uHallIndex N hN k))
          (FreeMetabelian.Free.weightIncl s hs x) = 0 := by
    intro k
    rw [gradedCoordinate_repr_apply]
    have hp : FreeMetabelian.Free.weightIncl s hs x
        (topGradedIndex N (uHallIndex N hN k)).1 = 0 := by
      change FreeMetabelian.Free.incl (⟨s, hs⟩ : Fin (N + 3)) x
        (⟨N + 2, by omega⟩ : Fin (N + 3)) = 0
      apply FreeMetabelian.Free.incl_apply_of_ne
      intro heq
      apply hsTop
      exact (congrArg Fin.val heq).symm
    rw [hp]
    have hz := congrArg (fun f ↦ f
        (topGradedIndex N (uHallIndex N hN k)).2)
      (FreeMetabelian.Free.pieceBasis generatorBasis
        (topGradedIndex N (uHallIndex N hN k)).1.val).repr.map_zero
    exact hz
  simp [sourceDetector, castCoordinate, gradedZModCoordinate,
    LinearMap.add_apply, LinearMap.smul_apply, hpair, htop]

private theorem bracket_weightIncl_zero_eq_weightIncl_succ
    (N s : ℕ) (hs : s < N + 3) (hsucc : s + 1 < N + 3)
    (x : FreeMetabelian.Piece GeneratorModule s)
    (y : GeneratorModule) :
    ⁅FreeMetabelian.Free.weightIncl s hs x,
      FreeMetabelian.Free.weightIncl 0 (by omega) y⁆ =
        FreeMetabelian.Free.weightIncl (s + 1) hsucc
          (⁅FreeMetabelian.Free.weightIncl s hs x,
            FreeMetabelian.Free.weightIncl 0 (by omega) y⁆
              (⟨s + 1, hsucc⟩ : Fin (N + 3))) := by
  funext k
  by_cases hk : k.val = s + 1
  · have hkeq : k = (⟨s + 1, hsucc⟩ : Fin (N + 3)) := Fin.ext hk
    subst k
    exact (FreeMetabelian.Free.incl_apply_same _ _).symm
  · calc
      _ = 0 := FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
        s 0 hs (by omega) x y k (by simpa using hk)
      _ = FreeMetabelian.Free.weightIncl (s + 1) hsucc
          (⁅FreeMetabelian.Free.weightIncl s hs x,
            FreeMetabelian.Free.weightIncl 0 (by omega) y⁆
              (⟨s + 1, hsucc⟩ : Fin (N + 3))) k := by
        symm
        apply FreeMetabelian.Free.incl_apply_of_ne
        intro heq
        exact hk (congrArg Fin.val heq)

private theorem rightBracketPow_source_homogeneous
    (N n : ℕ) (hn : n ≤ N) :
    ∃ x : FreeMetabelian.Piece GeneratorModule n,
      rightBracketPow (x4Source N) (x5Source N) n =
        FreeMetabelian.Free.weightIncl n (by omega) x := by
  induction n with
  | zero =>
      exact ⟨generatorBasis 4, rfl⟩
  | succ n ih =>
      rcases ih (by omega) with ⟨x, hx⟩
      have hnlt : n < N + 3 := by omega
      have hn1lt : n + 1 < N + 3 := by omega
      have hzero : 0 < N + 3 := by omega
      rw [rightBracketPow_succ, hx]
      let w : FreeMetabelian.Piece GeneratorModule (n + 1) :=
        ⁅FreeMetabelian.Free.weightIncl n hnlt x,
          FreeMetabelian.Free.weightIncl 0 hzero (generatorBasis 0)⁆
            (⟨n + 1, hn1lt⟩ : Fin (N + 3))
      refine ⟨w, ?_⟩
      change ⁅FreeMetabelian.Free.weightIncl n hnlt x,
        FreeMetabelian.Free.weightIncl 0 hzero (generatorBasis 0)⁆ =
          FreeMetabelian.Free.weightIncl (n + 1) hn1lt w
      exact bracket_weightIncl_zero_eq_weightIncl_succ N n hnlt
        hn1lt x (generatorBasis 0)

private theorem cSource_homogeneous (N : ℕ) (i : Fin 3) :
    ∃ x : FreeMetabelian.Piece GeneratorModule (N + 1),
      cSource N i = FreeMetabelian.Free.weightIncl (N + 1) (by omega) x := by
  rcases rightBracketPow_source_homogeneous N N (by omega) with ⟨x, hx⟩
  have hNlt : N < N + 3 := by omega
  have hN1lt : N + 1 < N + 3 := by omega
  have hzero : 0 < N + 3 := by omega
  rw [cSource, tSource, hx]
  let w : FreeMetabelian.Piece GeneratorModule (N + 1) :=
    ⁅FreeMetabelian.Free.weightIncl N hNlt x,
      FreeMetabelian.Free.weightIncl 0 hzero
        (generatorBasis (smallGeneratorIndex i))⁆
      (⟨N + 1, hN1lt⟩ : Fin (N + 3))
  refine ⟨w, ?_⟩
  change ⁅FreeMetabelian.Free.weightIncl N hNlt x,
    FreeMetabelian.Free.weightIncl 0 hzero
      (generatorBasis (smallGeneratorIndex i))⁆ =
        FreeMetabelian.Free.weightIncl (N + 1) hN1lt w
  exact bracket_weightIncl_zero_eq_weightIncl_succ N N hNlt hN1lt
    x (generatorBasis (smallGeneratorIndex i))

private theorem sourceDetector_sourceGenerator_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (i : Generator) :
    sourceDetector N hN (sourceGenerator N i) = 0 := by
  change sourceDetector N hN
    (FreeMetabelian.Free.weightIncl 0 (by omega) (generatorBasis i)) = 0
  exact sourceDetector_weightIncl_eq_zero N hN 0 (by omega)
    (generatorBasis i) (by omega) (by omega)

private theorem sourceDetector_cSource_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) :
    sourceDetector N hN (cSource N i) = 0 := by
  rcases cSource_homogeneous N i with ⟨x, hx⟩
  rw [hx]
  exact sourceDetector_weightIncl_eq_zero N hN (N + 1) (by omega) x
    (by omega) (by omega)

private theorem sourceDetector_r1Source_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    sourceDetector N hN (r1Source N) = 0 := by
  have hx1 : sourceDetector N hN (x1Source N) = 0 :=
    sourceDetector_sourceGenerator_eq_zero N hN 1
  have hc3 : sourceDetector N hN (c3Source N) = 0 :=
    sourceDetector_cSource_eq_zero N hN 2
  have hc2 : sourceDetector N hN (c2Source N) = 0 :=
    sourceDetector_cSource_eq_zero N hN 1
  simp [r1Source, hx1, hc3, hc2]

private theorem sourceDetector_r2Source_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    sourceDetector N hN (r2Source N) = 0 := by
  have hx2 : sourceDetector N hN (x2Source N) = 0 :=
    sourceDetector_sourceGenerator_eq_zero N hN 2
  have hc3 : sourceDetector N hN (c3Source N) = 0 :=
    sourceDetector_cSource_eq_zero N hN 2
  have hc1 : sourceDetector N hN (c1Source N) = 0 :=
    sourceDetector_cSource_eq_zero N hN 0
  simp [r2Source, hx2, hc3, hc1]

private theorem sourceDetector_r3Source_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    sourceDetector N hN (r3Source N) = 0 := by
  have hx3 : sourceDetector N hN (x3Source N) = 0 :=
    sourceDetector_sourceGenerator_eq_zero N hN 3
  have hc2 : sourceDetector N hN (c2Source N) = 0 :=
    sourceDetector_cSource_eq_zero N hN 1
  have hc1 : sourceDetector N hN (c1Source N) = 0 :=
    sourceDetector_cSource_eq_zero N hN 0
  simp [r3Source, hx3, hc2, hc1]

private theorem cSource_doubleBracket_eq_zero (N : ℕ) (i : Fin 3)
    (x y : Source N) : ⁅⁅cSource N i, x⁆, y⁆ = 0 := by
  rcases cSource_homogeneous N i with ⟨c, hc⟩
  have hcLCS : cSource N i ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1) := by
    rw [hc]
    exact FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
      generatorBasis (N + 1) (by omega) c
  have hcx : ⁅cSource N i, x⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 2) := by
    rw [show N + 2 = (N + 1) + 1 by omega,
      LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
    exact LieSubmodule.lie_mem_lie hcLCS (by simp)
  have hcxy : ⁅⁅cSource N i, x⁆, y⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 3) := by
    change ⁅⁅cSource N i, x⁆, y⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) ((N + 2) + 1)
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
    exact LieSubmodule.lie_mem_lie hcx (by simp)
  have hcut := FreeMetabelian.Free.lowerCentralSeries_cutoff_eq_bot
    (X := GeneratorModule) (c := N + 3)
  rw [hcut] at hcxy
  exact hcxy

private theorem rightOrbit_r1Source_cons_cons (N : ℕ)
    (x y : Source N) (xs : List (Source N)) :
    rightOrbit (r1Source N) (x :: y :: xs) =
      rowScale 0 •
        rightOrbit ⁅⁅smallSourceGenerator N 0, x⁆, y⁆ xs := by
  have hc3 : ⁅⁅c3Source N, x⁆, y⁆ = 0 :=
    cSource_doubleBracket_eq_zero N 2 x y
  have hc2 : ⁅⁅c2Source N, x⁆, y⁆ = 0 :=
    cSource_doubleBracket_eq_zero N 1 x y
  simp only [rightOrbit_cons, r1Source, add_lie, zsmul_lie,
    hc3, hc2, smul_zero, add_zero, rightOrbit_zsmul, rowScale]
  rfl

private theorem rightOrbit_r2Source_cons_cons (N : ℕ)
    (x y : Source N) (xs : List (Source N)) :
    rightOrbit (r2Source N) (x :: y :: xs) =
      rowScale 1 •
        rightOrbit ⁅⁅smallSourceGenerator N 1, x⁆, y⁆ xs := by
  have hc3 : ⁅⁅c3Source N, x⁆, y⁆ = 0 :=
    cSource_doubleBracket_eq_zero N 2 x y
  have hc1 : ⁅⁅c1Source N, x⁆, y⁆ = 0 :=
    cSource_doubleBracket_eq_zero N 0 x y
  simp only [rightOrbit_cons, r2Source, sub_lie, add_lie, zsmul_lie,
    hc3, hc1, smul_zero, add_zero, sub_zero, rightOrbit_zsmul, rowScale]
  rfl

private theorem rightOrbit_r3Source_cons_cons (N : ℕ)
    (x y : Source N) (xs : List (Source N)) :
    rightOrbit (r3Source N) (x :: y :: xs) =
      rowScale 2 •
        rightOrbit ⁅⁅smallSourceGenerator N 2, x⁆, y⁆ xs := by
  have hc2 : ⁅⁅c2Source N, x⁆, y⁆ = 0 :=
    cSource_doubleBracket_eq_zero N 1 x y
  have hc1 : ⁅⁅c1Source N, x⁆, y⁆ = 0 :=
    cSource_doubleBracket_eq_zero N 0 x y
  simp only [rightOrbit_cons, r3Source, sub_lie, zsmul_lie,
    hc2, hc1, smul_zero, sub_zero, rightOrbit_zsmul, rowScale]
  rfl

private theorem sourceDetector_r1Source_rightOrbit
    (N : ℕ) (hN : 1 ≤ N) : ∀ xs : List (Source N),
    sourceDetector N hN (rightOrbit (r1Source N) xs) = 0
  | [] => sourceDetector_r1Source_eq_zero N hN
  | [x] => sourceDetector_r1Source_lie N hN x
  | x :: y :: xs => by
      rw [rightOrbit_r1Source_cons_cons]
      exact sourceDetector_rowScale_deepOrbit_eq_zero N hN 0 x y xs

private theorem sourceDetector_r2Source_rightOrbit
    (N : ℕ) (hN : 1 ≤ N) : ∀ xs : List (Source N),
    sourceDetector N hN (rightOrbit (r2Source N) xs) = 0
  | [] => sourceDetector_r2Source_eq_zero N hN
  | [x] => sourceDetector_r2Source_lie N hN x
  | x :: y :: xs => by
      rw [rightOrbit_r2Source_cons_cons]
      exact sourceDetector_rowScale_deepOrbit_eq_zero N hN 1 x y xs

private theorem sourceDetector_r3Source_rightOrbit
    (N : ℕ) (hN : 1 ≤ N) : ∀ xs : List (Source N),
    sourceDetector N hN (rightOrbit (r3Source N) xs) = 0
  | [] => sourceDetector_r3Source_eq_zero N hN
  | [x] => sourceDetector_r3Source_lie N hN x
  | x :: y :: xs => by
      rw [rightOrbit_r3Source_cons_cons]
      exact sourceDetector_rowScale_deepOrbit_eq_zero N hN 2 x y xs

private theorem sourceDetector_definingRelator_rightOrbit
    (N : ℕ) (hN : 1 ≤ N) {z : Source N}
    (hz : z ∈ definingRelators N) : ∀ xs : List (Source N),
    sourceDetector N hN (rightOrbit z xs) = 0 := by
  change z ∈ ({r1Source N, r2Source N, r3Source N} ∪
    topHallRelators N) ∪ exceptionalRelators N at hz
  rcases hz with (hrow | htop) | hexceptional
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hrow
    rcases hrow with rfl | rfl | rfl
    · exact sourceDetector_r1Source_rightOrbit N hN
    · exact sourceDetector_r2Source_rightOrbit N hN
    · exact sourceDetector_r3Source_rightOrbit N hN
  · exact sourceDetector_topHallRelator N hN htop
  · exact sourceDetector_exceptionalRelator N hN hexceptional

private theorem sourceDetector_rightOrbit_eq_zero_of_mem_relationIdeal
    (N : ℕ) (hN : 1 ≤ N) {z : Source N}
    (hz : z ∈ relationIdeal N) : ∀ xs : List (Source N),
    sourceDetector N hN (rightOrbit z xs) = 0 := by
  change z ∈ LieSubmodule.lieSpan ℤ (Source N) (definingRelators N) at hz
  induction hz using LieSubmodule.lieSpan_induction with
  | mem z hz => exact sourceDetector_definingRelator_rightOrbit N hN hz
  | zero =>
      intro xs
      rw [rightOrbit_zero, map_zero]
  | add x y hx hy ihx ihy =>
      intro xs
      rw [rightOrbit_add, map_add, ihx xs, ihy xs, add_zero]
  | smul n x hx ih =>
      intro xs
      rw [rightOrbit_zsmul, map_zsmul, ih xs, smul_zero]
  | lie x y hy ih =>
      intro xs
      have hzero := ih (x :: xs)
      rw [rightOrbit_cons] at hzero
      rw [← lie_skew x y, rightOrbit_neg, map_neg, hzero, neg_zero]

theorem sourceDetector_eq_zero_of_mem_relationIdeal
    (N : ℕ) (hN : 1 ≤ N) {z : Source N} (hz : z ∈ relationIdeal N) :
    sourceDetector N hN z = 0 :=
  sourceDetector_rightOrbit_eq_zero_of_mem_relationIdeal N hN hz []

theorem relationIdeal_le_sourceDetector_ker (N : ℕ) (hN : 1 ≤ N) :
    (relationIdeal N).toSubmodule ≤ (sourceDetector N hN).ker := by
  intro z hz
  exact sourceDetector_eq_zero_of_mem_relationIdeal N hN hz

/-! ## The descended top character and exact additive orders -/

/-- A `ZMod 256` value equal to `4` detects exact additive order `64`.
This small arithmetic lemma is kept private; the substantive work is the
construction of the descended character below. -/
private theorem addOrderOf_eq_sixtyFour_of_detector
    {A : Type*} [AddCommGroup A] (v : A) (h64 : (64 : ℤ) • v = 0)
    (χ : A →+ ZMod 256) (hχ : χ v = 4) :
    addOrderOf v = 64 := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
      simpa only [ofNat_zsmul] using h64)
  · have hmap : addOrderOf (χ v) ∣ addOrderOf v :=
      addOrderOf_map_dvd χ v
    rw [hχ] at hmap
    have hfour : addOrderOf (4 : ZMod 256) = 64 := by
      change addOrderOf ((4 : ℕ) : ZMod 256) = 64
      rw [ZMod.addOrderOf_coe 4 (by norm_num)]
      norm_num
    simpa [hfour] using hmap

/-- The top-coordinate character of the exact manuscript quotient.  Its
construction uses the preceding calculation for the whole Lie ideal, so all
iterated brackets of all defining rows—not only the displayed relations—are
accounted for. -/
def topDetector (N : ℕ) (hN : 1 ≤ N) : L N →+ ZMod 256 :=
  (Submodule.liftQ (relationIdeal N).toSubmodule (sourceDetector N hN)
    (relationIdeal_le_sourceDetector_ker N hN)).toAddMonoidHom

@[simp] theorem topDetector_quotientMap (N : ℕ) (hN : 1 ≤ N)
    (z : Source N) :
    topDetector N hN (quotientMap N z) = sourceDetector N hN z := by
  change (Submodule.liftQ (relationIdeal N).toSubmodule
    (sourceDetector N hN) (relationIdeal_le_sourceDetector_ker N hN)
      (LieSubmodule.Quotient.mk z)) = _
  rw [Submodule.liftQ_apply]

@[simp] theorem topDetector_b12 (N : ℕ) (hN : 1 ≤ N) :
    topDetector N hN (b12 N) = -4 := by
  change topDetector N hN (quotientMap N (b12Source N)) = -4
  rw [topDetector_quotientMap, sourceDetector_b12Source]

@[simp] theorem topDetector_b13 (N : ℕ) (hN : 1 ≤ N) :
    topDetector N hN (b13 N) = -2 := by
  change topDetector N hN (quotientMap N (b13Source N)) = -2
  rw [topDetector_quotientMap, sourceDetector_b13Source]

@[simp] theorem topDetector_b23 (N : ℕ) (hN : 1 ≤ N) :
    topDetector N hN (b23 N) = -1 := by
  change topDetector N hN (quotientMap N (b23Source N)) = -1
  rw [topDetector_quotientMap, sourceDetector_b23Source]

@[simp] theorem topDetector_u1 (N : ℕ) (hN : 1 ≤ N) :
    topDetector N hN (u1 N) = 64 := by
  change topDetector N hN (quotientMap N (uSource N 0)) = 64
  rw [topDetector_quotientMap, sourceDetector_uSource]

@[simp] theorem topDetector_u2 (N : ℕ) (hN : 1 ≤ N) :
    topDetector N hN (u2 N) = 16 := by
  change topDetector N hN (quotientMap N (uSource N 1)) = 16
  rw [topDetector_quotientMap, sourceDetector_uSource]

@[simp] theorem topDetector_u3 (N : ℕ) (hN : 1 ≤ N) :
    topDetector N hN (u3 N) = 4 := by
  change topDetector N hN (quotientMap N (uSource N 2)) = 4
  rw [topDetector_quotientMap, sourceDetector_uSource]

/-- The retained top generator has exactly the manuscript additive order. -/
theorem addOrderOf_u3_eq_sixtyFour (N : ℕ) (hN : 1 ≤ N) :
    addOrderOf (u3 N) = 64 := by
  exact addOrderOf_eq_sixtyFour_of_detector (u3 N)
    (sixtyFour_u3_eq_zero N) (topDetector N hN) (topDetector_u3 N hN)

theorem u3_ne_zero (N : ℕ) (hN : 1 ≤ N) : u3 N ≠ 0 := by
  intro hz
  have horder := addOrderOf_u3_eq_sixtyFour N hN
  rw [hz, addOrderOf_zero] at horder
  omega

/-- Each retained top diagonal lies in the last potentially nonzero
lower-central term. -/
theorem u_mem_lowerCentralSeries (N : ℕ) (i : Fin 3) :
    u N i ∈ lowerCentralSeries ℤ (L N) (N + 2) := by
  have hu : ⁅c N i, smallGenerator N i⁆ ∈
      LieModule.lowerCentralSeries ℤ (L N) (L N) ((N + 1) + 1) := by
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
    exact LieSubmodule.lie_mem_lie (c_mem_lowerCentralSeries N i) (by simp)
  simpa only [show (N + 1) + 1 = N + 2 by omega,
    c_lie_smallGenerator] using hu

/-- The last possible lower-central term is genuinely nonzero. -/
theorem lowerCentralSeries_top_ne_bot (N : ℕ) (hN : 1 ≤ N) :
    lowerCentralSeries ℤ (L N) (N + 2) ≠ ⊥ := by
  intro hbot
  have hu := u_mem_lowerCentralSeries N (2 : Fin 3)
  rw [hbot] at hu
  exact u3_ne_zero N hN (by simpa using hu)

/-- In zero-based lower-central indexing, `L_N` has exact class `N+3`:
its `(N+2)`nd term is nonzero and its `(N+3)`rd term is zero. -/
theorem exact_lowerCentral_height (N : ℕ) (hN : 1 ≤ N) :
    lowerCentralSeries ℤ (L N) (N + 2) ≠ ⊥ ∧
      lowerCentralSeries ℤ (L N) (N + 3) = ⊥ :=
  ⟨lowerCentralSeries_top_ne_bot N hN, lowerCentralSeries_cutoff_eq_bot N⟩

/-- Since `a=32u₃`, its additive order is exactly two. -/
theorem addOrderOf_a_eq_two (N : ℕ) (hN : 1 ≤ N) :
    addOrderOf (a N) = 2 := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
      simpa only [ofNat_zsmul] using two_a_eq_zero N hN)
  · have hmap : addOrderOf (topDetector N hN (a N)) ∣ addOrderOf (a N) :=
      addOrderOf_map_dvd (topDetector N hN) (a N)
    have hvalue : topDetector N hN (a N) = 128 := by
      rw [a_eq_thirtyTwo_u3 N hN, map_zsmul, topDetector_u3]
      norm_num
    rw [hvalue] at hmap
    have h128 : addOrderOf (128 : ZMod 256) = 2 := by
      change addOrderOf ((128 : ℕ) : ZMod 256) = 2
      rw [ZMod.addOrderOf_coe 128 (by norm_num)]
      norm_num
    simpa [h128] using hmap

theorem a_ne_zero (N : ℕ) (hN : 1 ≤ N) : a N ≠ 0 := by
  intro hz
  have horder := addOrderOf_a_eq_two N hN
  rw [hz, addOrderOf_zero] at horder
  omega

end

end LieRings.FinitePlateau
