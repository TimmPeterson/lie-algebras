import LieRings.FinitePlateau.MagnusMasks
import LieRings.FinitePlateau.MagnusCoordinates

/-!
# Literal Hall-coordinate consequences of the masked Magnus probes

The probe files construct maps out of the manuscript presentation and compute
them on individual generators and Hall brackets.  This file packages those
computations as reads of the literal graded Hall coordinates of an arbitrary
source element.  The resulting congruence and exact-zero statements are the
interface consumed by the Hall normal-form argument.
-/

namespace LieRings.FinitePlateau

noncomputable section

namespace MagnusCoordinateReads

open MagnusProbe MagnusCoordinates MagnusMasks

/-- A local name for the literal graded Hall index of the free source. -/
abbrev GradedHallIndex (N : ℕ) :=
  (u : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator u.val

/-- The literal graded index of a free generator. -/
def generatorIndex (N : ℕ) (j : Generator) : GradedHallIndex N :=
  ⟨⟨0, by omega⟩, j⟩

/-- The literal graded index of a Hall comb of bracket weight `s + 2`. -/
def hallIndex (N s : ℕ) (h : FreeMetabelian.HallIndex Generator s)
    (hcut : s + 1 < N + 3) : GradedHallIndex N :=
  ⟨⟨s + 1, hcut⟩, h⟩

@[simp] theorem hallGradedBasis_generatorIndex
    (N : ℕ) (j : Generator) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis (generatorIndex N j) =
      sourceGenerator N j := by
  rw [generatorIndex, hallGradedBasis_apply]
  rfl

/-- A positive-weight vector of the literal graded basis is the manuscript's
recursive Hall bracket with the same index. -/
theorem hallGradedBasis_hallIndex
    (N s : ℕ) (h : FreeMetabelian.HallIndex Generator s)
    (hcut : s + 1 < N + 3) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis
        (hallIndex N s h hcut) =
      FreeMetabelian.Evaluation.hallBracket generatorBasis s h hcut := by
  rw [hallIndex, hallGradedBasis_apply,
    FreeMetabelian.Evaluation.hallBracket_eq_incl]
  change FreeMetabelian.Free.incl
      (⟨s + 1, hcut⟩ : Fin (N + 3))
        (FreeMetabelian.Free.pieceBasis generatorBasis (s + 1) h) =
    FreeMetabelian.Free.incl (⟨s + 1, hcut⟩ : Fin (N + 3))
      (FreeMetabelian.hallVector generatorBasis s h)
  rw [FreeMetabelian.Free.pieceBasis]
  have he :
      (FreeMetabelian.hallBasis generatorBasis s).equivFun.toAddEquiv.toIntLinearEquiv =
        (FreeMetabelian.hallBasis generatorBasis s).equivFun :=
    LinearEquiv.toAddEquiv_toIntLinearEquiv
      (FreeMetabelian.hallBasis generatorBasis s).equivFun
  have hbEq : Module.Basis.ofEquivFun
        (FreeMetabelian.hallBasis generatorBasis s).equivFun.toAddEquiv.toIntLinearEquiv =
      FreeMetabelian.hallBasis generatorBasis s := by
    rw [he, Module.Basis.ofEquivFun_equivFun]
  have hpEq := congrArg (fun b ↦ b h) hbEq
  calc
    _ = FreeMetabelian.Free.incl (⟨s + 1, hcut⟩ : Fin (N + 3))
        (FreeMetabelian.hallBasis generatorBasis s h) :=
      congrArg (FreeMetabelian.Free.incl
        (⟨s + 1, hcut⟩ : Fin (N + 3))) hpEq
    _ = _ := by rw [FreeMetabelian.hallBasis_apply]

/-- Reduction of a literal integral Hall coordinate modulo `q`. -/
def coordinateMod (N q : ℕ) (p : GradedHallIndex N) :
    Source N →ₗ[ℤ] ZMod q :=
  (Int.castAddHom (ZMod q)).toIntLinearMap.comp (gradedCoordinate N p)

/-! ## Reads for the unmasked universal probe -/

/-- The scalar Magnus monomial `X_j` reads exactly the literal weight-one
Hall coordinate of an arbitrary source element. -/
theorem generatorRead_sourceProbe
    (N q r : ℕ) (hr : r ≤ N + 4) (hr1 : 1 < r)
    (j : Generator) (x : Source N) :
    generatorRead q r j hr1 (MagnusProbe.sourceProbe N q r hr x) =
      (gradedCoordinate N (generatorIndex N j) x : ZMod q) := by
  let lhs : Source N →ₗ[ℤ] ZMod q :=
    (generatorRead q r j hr1).toIntLinearMap.comp
      (MagnusProbe.sourceProbe N q r hr).toLinearMap
  let rhs : Source N →ₗ[ℤ] ZMod q := coordinateMod N q (generatorIndex N j)
  have hmaps : lhs = rhs := by
    apply (FreeMetabelian.Free.hallGradedBasis generatorBasis).ext
    rintro ⟨⟨w, hw⟩, p⟩
    cases w with
    | zero =>
        change Generator at p
        rw [hallGradedBasis_apply]
        change generatorRead q r j hr1
            (MagnusProbe.sourceProbe N q r hr (sourceGenerator N p)) =
          ((gradedCoordinate N (generatorIndex N j)
            (sourceGenerator N p) : ℤ) : ZMod q)
        rw [generatorRead_sourceProbe_sourceGenerator,
          ← hallGradedBasis_generatorIndex N p]
        by_cases hjp : j = p
        · subst p
          rw [if_pos rfl, gradedCoordinate_hallGradedBasis_self]
          simp
        · rw [if_neg hjp,
            gradedCoordinate_hallGradedBasis_of_ne N
              (generatorIndex N j) (generatorIndex N p)]
          · simp
          · intro he
            apply hjp
            cases he
            rfl
    | succ t =>
        change FreeMetabelian.HallIndex Generator t at p
        let k : GradedHallIndex N := hallIndex N t p hw
        change generatorRead q r j hr1
            (MagnusProbe.sourceProbe N q r hr
              (FreeMetabelian.Free.hallGradedBasis generatorBasis k)) =
          ((gradedCoordinate N (generatorIndex N j)
            (FreeMetabelian.Free.hallGradedBasis generatorBasis k) : ℤ) : ZMod q)
        rw [show FreeMetabelian.Free.hallGradedBasis generatorBasis k =
              FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw by
            exact hallGradedBasis_hallIndex N t p hw,
          generatorRead_sourceProbe_hallBracket,
          ← hallGradedBasis_hallIndex N t p hw,
          gradedCoordinate_hallGradedBasis_of_ne]
        · simp
        · intro he
          have hwgt := congrArg (fun z : GradedHallIndex N ↦ z.1.val) he
          simp [generatorIndex, k, hallIndex] at hwgt
  exact LinearMap.congr_fun hmaps x

/-- A Hall monomial/vector read vanishes on a source generator. -/
theorem hallRead_sourceProbe_sourceGenerator
    (N q r s : ℕ) (hr : r ≤ N + 4)
    (h : FreeMetabelian.HallIndex Generator s) (hs : s + 2 < r)
    (j : Generator) :
    hallRead q r s h hs
        (MagnusProbe.sourceProbe N q r hr (sourceGenerator N j)) = 0 := by
  rw [MagnusProbe.sourceProbe_sourceGenerator, hallRead,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  by_cases hj : j = h.head
  · subst j
    rw [Ring.generator_vector]
    rw [if_pos (rfl : h.head = h.head)]
    change truncatedCoeff q r (hallExponent s h) _
      (((varImage q r h.head : positiveIdeal q r) : TruncatedPoly q r)) = 0
    rw [varImage_coe, truncatedCoeff_mk]
    have hne : hallExponent s h ≠ Finsupp.single h.head 1 := by
      intro he
      have hd := congrArg Finsupp.degree he
      rw [hallExponent_degree] at hd
      simp [Finsupp.degree_single] at hd
    rw [MvPolynomial.X, MvPolynomial.coeff_monomial]
    simp [hne, Ne.symm hne]
  · rw [Ring.generator_vector, if_neg hj]
    exact map_zero _

/-- The Hall monomial at its head reads the signed literal Hall coordinate
of an arbitrary source element. -/
theorem hallRead_sourceProbe
    (N q r s : ℕ) (hr : r ≤ N + 4)
    (h : FreeMetabelian.HallIndex Generator s)
    (hs : s + 2 < r) (hcut : s + 1 < N + 3)
    (x : Source N) :
    hallRead q r s h hs (MagnusProbe.sourceProbe N q r hr x) =
      (-(hallSign s : ℤ)) •
        (gradedCoordinate N (hallIndex N s h hcut) x : ZMod q) := by
  let lhs : Source N →ₗ[ℤ] ZMod q :=
    (hallRead q r s h hs).toIntLinearMap.comp
      (MagnusProbe.sourceProbe N q r hr).toLinearMap
  let rhs : Source N →ₗ[ℤ] ZMod q :=
    (-(hallSign s : ℤ)) • coordinateMod N q (hallIndex N s h hcut)
  have hmaps : lhs = rhs := by
    apply (FreeMetabelian.Free.hallGradedBasis generatorBasis).ext
    rintro ⟨⟨w, hw⟩, p⟩
    cases w with
    | zero =>
        change Generator at p
        rw [hallGradedBasis_apply]
        change hallRead q r s h hs
            (MagnusProbe.sourceProbe N q r hr (sourceGenerator N p)) =
          (-(hallSign s : ℤ)) •
            ((gradedCoordinate N (hallIndex N s h hcut)
              (sourceGenerator N p) : ℤ) : ZMod q)
        rw [hallRead_sourceProbe_sourceGenerator,
          ← hallGradedBasis_generatorIndex N p,
          gradedCoordinate_hallGradedBasis_of_ne]
        · simp
        · intro he
          have hwgt := congrArg (fun z : GradedHallIndex N ↦ z.1.val) he
          simp [hallIndex, generatorIndex] at hwgt
    | succ t =>
        change FreeMetabelian.HallIndex Generator t at p
        let k : GradedHallIndex N := hallIndex N t p hw
        change hallRead q r s h hs
            (MagnusProbe.sourceProbe N q r hr
              (FreeMetabelian.Free.hallGradedBasis generatorBasis k)) =
          (-(hallSign s : ℤ)) •
            ((gradedCoordinate N (hallIndex N s h hcut)
              (FreeMetabelian.Free.hallGradedBasis generatorBasis k) : ℤ) : ZMod q)
        rw [show FreeMetabelian.Free.hallGradedBasis generatorBasis k =
              FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw by
            exact hallGradedBasis_hallIndex N t p hw]
        by_cases hst : s = t
        · subst t
          rw [hallRead_sourceProbe_hallBracket]
          rw [← hallGradedBasis_hallIndex N s p hw]
          by_cases hhp : h = p
          · subst p
            rw [if_pos rfl, gradedCoordinate_hallGradedBasis_self]
            simp
          · rw [if_neg hhp, gradedCoordinate_hallGradedBasis_of_ne]
            · simp
            · intro he
              apply hhp
              cases he
              rfl
        · rw [hallRead_sourceProbe_hallBracket_of_weight_ne N q r s t hr
              h p hs hw hst,
            ← hallGradedBasis_hallIndex N t p hw,
            gradedCoordinate_hallGradedBasis_of_ne]
          · simp
          · intro he
            apply hst
            have hwgt := congrArg (fun z : GradedHallIndex N ↦ z.1.val) he
            simp [hallIndex, k] at hwgt
            omega
  exact LinearMap.congr_fun hmaps x

/-! ## Modular masked reads -/

@[simp] private theorem generatorRead_lie
    (q r : ℕ) (j : Generator) (hr1 : 1 < r)
    (x y : Target q r) :
    generatorRead q r j hr1 ⁅x, y⁆ = 0 := by
  rw [generatorRead, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Target.scalar_lie]
  exact map_zero _

/-- If a Hall comb has an erased occurrence, its masked Magnus evaluation is
zero.  This is the complementary half of
`MagnusMasks.sourceProbe_hallBracket_eq_unmasked`. -/
theorem maskedSourceProbe_hallBracket_eq_zero_of_not_survives
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 4) :
    ∀ (s : ℕ) (h : FreeMetabelian.HallIndex Generator s)
      (hcut : s + 1 < N + 3), ¬ HallSurvives i s h →
      MagnusMasks.sourceProbe N i r (by omega)
          (FreeMetabelian.Evaluation.hallBracket generatorBasis s h hcut) = 0 := by
  intro s
  induction s with
  | zero =>
      intro h hcut hn
      have hmHead : MagnusMasks.sourceProbe N i r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.head)) = maskedGenerator i r h.head := by
        change MagnusMasks.sourceProbe N i r (by omega)
          (sourceGenerator N h.head) = _
        exact MagnusMasks.sourceProbe_sourceGenerator N i r (by omega) h.head
      have hmPivot : MagnusMasks.sourceProbe N i r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.pivot)) = maskedGenerator i r h.pivot := by
        change MagnusMasks.sourceProbe N i r (by omega)
          (sourceGenerator N h.pivot) = _
        exact MagnusMasks.sourceProbe_sourceGenerator N i r (by omega) h.pivot
      rw [FreeMetabelian.Evaluation.hallBracket, LieHom.map_lie,
        hmHead, hmPivot]
      by_cases hh : Active i h.head
      · have hp : ¬ Active i h.pivot := fun hp ↦ hn ⟨hh, hp⟩
        rw [maskedGenerator_of_active _ _ _ hh,
          maskedGenerator_of_not_active _ _ _ hp, lie_zero]
      · rw [maskedGenerator_of_not_active _ _ _ hh, zero_lie]
  | succ s ih =>
      intro h hcut hn
      have hmNext : MagnusMasks.sourceProbe N i r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.nextTooth)) = maskedGenerator i r h.nextTooth := by
        change MagnusMasks.sourceProbe N i r (by omega)
          (sourceGenerator N h.nextTooth) = _
        exact MagnusMasks.sourceProbe_sourceGenerator N i r
          (by omega) h.nextTooth
      rw [FreeMetabelian.Evaluation.hallBracket, LieHom.map_lie, hmNext]
      by_cases ht : Active i h.nextTooth
      · have hp : ¬ HallSurvives i s h.predecessor := fun hp ↦ hn ⟨ht, hp⟩
        rw [ih h.predecessor (by omega) hp,
          maskedGenerator_of_active _ _ _ ht, zero_lie]
      · rw [maskedGenerator_of_not_active _ _ _ ht, lie_zero]

/-- On an active generator coordinate, the modular masked probe and the
unmasked universal probe have the same arbitrary-source read. -/
theorem generatorRead_maskedSourceProbe_eq_unmasked
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 4)
    (j : Generator) (hr1 : 1 < r) (hj : Active i j) (x : Source N) :
    generatorRead (modulus i) r j hr1
        (MagnusMasks.sourceProbe N i r (by omega) x) =
      generatorRead (modulus i) r j hr1
        (MagnusProbe.sourceProbe N (modulus i) r (by omega) x) := by
  let lhs : Source N →ₗ[ℤ] ZMod (modulus i) :=
    (generatorRead (modulus i) r j hr1).toIntLinearMap.comp
      (MagnusMasks.sourceProbe N i r (by omega)).toLinearMap
  let rhs : Source N →ₗ[ℤ] ZMod (modulus i) :=
    (generatorRead (modulus i) r j hr1).toIntLinearMap.comp
      (MagnusProbe.sourceProbe N (modulus i) r (by omega)).toLinearMap
  have hmaps : lhs = rhs := by
    apply (FreeMetabelian.Free.hallGradedBasis generatorBasis).ext
    rintro ⟨⟨w, hw⟩, p⟩
    cases w with
    | zero =>
        change Generator at p
        rw [hallGradedBasis_apply]
        change generatorRead (modulus i) r j hr1
            (MagnusMasks.sourceProbe N i r (by omega) (sourceGenerator N p)) =
          generatorRead (modulus i) r j hr1
            (MagnusProbe.sourceProbe N (modulus i) r (by omega)
              (sourceGenerator N p))
        rw [MagnusMasks.sourceProbe_sourceGenerator,
          MagnusProbe.sourceProbe_sourceGenerator]
        by_cases hp : Active i p
        · rw [maskedGenerator_of_active _ _ _ hp]
        · rw [maskedGenerator_of_not_active _ _ _ hp, map_zero]
          rw [← MagnusProbe.sourceProbe_sourceGenerator N (modulus i) r
              (by omega) p,
            generatorRead_sourceProbe_sourceGenerator, if_neg]
          intro hjp
          apply hp
          simpa [hjp] using hj
    | succ t =>
        change FreeMetabelian.HallIndex Generator t at p
        have hb := hallGradedBasis_hallIndex N t p hw
        have hb' : FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨t + 1, hw⟩, p⟩ : GradedHallIndex N) =
            FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw := by
          simpa only [hallIndex] using hb
        rw [hb']
        change generatorRead (modulus i) r j hr1
            (MagnusMasks.sourceProbe N i r (by omega)
              (FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw)) =
          generatorRead (modulus i) r j hr1
            (MagnusProbe.sourceProbe N (modulus i) r (by omega)
              (FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw))
        cases t <;>
          rw [FreeMetabelian.Evaluation.hallBracket, LieHom.map_lie,
            LieHom.map_lie, generatorRead_lie, generatorRead_lie]
  exact LinearMap.congr_fun hmaps x

/-- Exact arbitrary-source generator-coordinate formula for a modular mask. -/
theorem generatorRead_maskedSourceProbe
    (N : ℕ) (i : Fin 3) (r : ℕ) (hr : r ≤ N + 4)
    (j : Generator) (hr1 : 1 < r) (hj : Active i j) (x : Source N) :
    generatorRead (modulus i) r j hr1
        (MagnusMasks.sourceProbe N i r (by omega) x) =
      (gradedCoordinate N (generatorIndex N j) x : ZMod (modulus i)) := by
  rw [generatorRead_maskedSourceProbe_eq_unmasked N i r hr j hr1 hj x]
  exact generatorRead_sourceProbe N (modulus i) r (by omega) hr1 j x

/-- On a surviving Hall coordinate, the modular masked probe and unmasked
probe have the same arbitrary-source Hall read. -/
theorem hallRead_maskedSourceProbe_eq_unmasked
    (N : ℕ) (i : Fin 3) (r s : ℕ) (hr : r ≤ N + 4)
    (h : FreeMetabelian.HallIndex Generator s)
    (hs : s + 2 < r) (hcut : s + 1 < N + 3)
    (ha : HallSurvives i s h) (x : Source N) :
    hallRead (modulus i) r s h hs
        (MagnusMasks.sourceProbe N i r (by omega) x) =
      hallRead (modulus i) r s h hs
        (MagnusProbe.sourceProbe N (modulus i) r (by omega) x) := by
  let lhs : Source N →ₗ[ℤ] ZMod (modulus i) :=
    (hallRead (modulus i) r s h hs).toIntLinearMap.comp
      (MagnusMasks.sourceProbe N i r (by omega)).toLinearMap
  let rhs : Source N →ₗ[ℤ] ZMod (modulus i) :=
    (hallRead (modulus i) r s h hs).toIntLinearMap.comp
      (MagnusProbe.sourceProbe N (modulus i) r (by omega)).toLinearMap
  have hmaps : lhs = rhs := by
    apply (FreeMetabelian.Free.hallGradedBasis generatorBasis).ext
    rintro ⟨⟨w, hw⟩, p⟩
    cases w with
    | zero =>
        change Generator at p
        rw [hallGradedBasis_apply]
        change hallRead (modulus i) r s h hs
            (MagnusMasks.sourceProbe N i r (by omega) (sourceGenerator N p)) =
          hallRead (modulus i) r s h hs
            (MagnusProbe.sourceProbe N (modulus i) r (by omega)
              (sourceGenerator N p))
        rw [MagnusMasks.sourceProbe_sourceGenerator,
          MagnusProbe.sourceProbe_sourceGenerator]
        by_cases hp : Active i p
        · rw [maskedGenerator_of_active _ _ _ hp]
        · rw [maskedGenerator_of_not_active _ _ _ hp, map_zero]
          rw [← MagnusProbe.sourceProbe_sourceGenerator N (modulus i) r
              (by omega) p,
            hallRead_sourceProbe_sourceGenerator]
    | succ t =>
        change FreeMetabelian.HallIndex Generator t at p
        have hb : FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨t + 1, hw⟩, p⟩ : GradedHallIndex N) =
            FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw := by
          simpa only [hallIndex] using hallGradedBasis_hallIndex N t p hw
        rw [hb]
        change hallRead (modulus i) r s h hs
            (MagnusMasks.sourceProbe N i r (by omega)
              (FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw)) =
          hallRead (modulus i) r s h hs
            (MagnusProbe.sourceProbe N (modulus i) r (by omega)
              (FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw))
        by_cases hp : HallSurvives i t p
        · rw [MagnusMasks.sourceProbe_hallBracket_eq_unmasked
              N i r hr t p hw hp]
        · rw [maskedSourceProbe_hallBracket_eq_zero_of_not_survives
              N i r hr t p hw hp, map_zero]
          by_cases hst : s = t
          · subst t
            rw [hallRead_sourceProbe_hallBracket]
            have hne : h ≠ p := by
              intro he
              subst p
              exact hp ha
            rw [if_neg hne]
          · exact (hallRead_sourceProbe_hallBracket_of_weight_ne
              N (modulus i) r s t (by omega) h p hs hw hst).symm
  exact LinearMap.congr_fun hmaps x

/-- Exact arbitrary-source Hall-coordinate formula for a modular mask. -/
theorem hallRead_maskedSourceProbe
    (N : ℕ) (i : Fin 3) (r s : ℕ) (hr : r ≤ N + 4)
    (h : FreeMetabelian.HallIndex Generator s)
    (hs : s + 2 < r) (hcut : s + 1 < N + 3)
    (ha : HallSurvives i s h) (x : Source N) :
    hallRead (modulus i) r s h hs
        (MagnusMasks.sourceProbe N i r (by omega) x) =
      (-(hallSign s : ℤ)) •
        (gradedCoordinate N (hallIndex N s h hcut) x : ZMod (modulus i)) := by
  rw [hallRead_maskedSourceProbe_eq_unmasked N i r s hr h hs hcut ha x]
  exact hallRead_sourceProbe N (modulus i) r s (by omega) h hs hcut x

/-! ## Integral outer-mask reads -/

/-- If a Hall comb contains a small generator, its outer-only Magnus
evaluation is zero. -/
theorem outerSourceProbe_hallBracket_eq_zero_of_not_survives
    (N r : ℕ) (hr : r ≤ N + 3) :
    ∀ (s : ℕ) (h : FreeMetabelian.HallIndex Generator s)
      (hcut : s + 1 < N + 3), ¬ OuterHallSurvives s h →
      outerSourceProbe N r (by omega)
          (FreeMetabelian.Evaluation.hallBracket generatorBasis s h hcut) = 0 := by
  intro s
  induction s with
  | zero =>
      intro h hcut hn
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
      rw [FreeMetabelian.Evaluation.hallBracket, LieHom.map_lie,
        hmHead, hmPivot]
      by_cases hh : OuterActive h.head
      · have hp : ¬ OuterActive h.pivot := fun hp ↦ hn ⟨hh, hp⟩
        rw [outerGenerator_of_active _ _ hh,
          outerGenerator_of_not_active _ _ hp, lie_zero]
      · rw [outerGenerator_of_not_active _ _ hh, zero_lie]
  | succ s ih =>
      intro h hcut hn
      have hmNext : outerSourceProbe N r (by omega)
          (FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (N + 3))
            (generatorBasis h.nextTooth)) = outerGenerator r h.nextTooth := by
        change outerSourceProbe N r (by omega)
          (sourceGenerator N h.nextTooth) = _
        exact outerSourceProbe_sourceGenerator N r (by omega) h.nextTooth
      rw [FreeMetabelian.Evaluation.hallBracket, LieHom.map_lie, hmNext]
      by_cases ht : OuterActive h.nextTooth
      · have hp : ¬ OuterHallSurvives s h.predecessor := fun hp ↦ hn ⟨ht, hp⟩
        rw [ih h.predecessor (by omega) hp,
          outerGenerator_of_active _ _ ht, zero_lie]
      · rw [outerGenerator_of_not_active _ _ ht, lie_zero]

/-- On a retained outer generator, the integral outer mask and the unmasked
integral probe have the same arbitrary-source scalar read. -/
theorem generatorRead_outerSourceProbe_eq_unmasked
    (N r : ℕ) (hr : r ≤ N + 3)
    (j : Generator) (hr1 : 1 < r) (hj : OuterActive j) (x : Source N) :
    generatorRead 0 r j hr1 (outerSourceProbe N r (by omega) x) =
      generatorRead 0 r j hr1
        (MagnusProbe.sourceProbe N 0 r (by omega) x) := by
  let lhs : Source N →ₗ[ℤ] ZMod 0 :=
    (generatorRead 0 r j hr1).toIntLinearMap.comp
      (outerSourceProbe N r (by omega)).toLinearMap
  let rhs : Source N →ₗ[ℤ] ZMod 0 :=
    (generatorRead 0 r j hr1).toIntLinearMap.comp
      (MagnusProbe.sourceProbe N 0 r (by omega)).toLinearMap
  have hmaps : lhs = rhs := by
    apply (FreeMetabelian.Free.hallGradedBasis generatorBasis).ext
    rintro ⟨⟨w, hw⟩, p⟩
    cases w with
    | zero =>
        change Generator at p
        rw [hallGradedBasis_apply]
        change generatorRead 0 r j hr1
            (outerSourceProbe N r (by omega) (sourceGenerator N p)) =
          generatorRead 0 r j hr1
            (MagnusProbe.sourceProbe N 0 r (by omega) (sourceGenerator N p))
        rw [outerSourceProbe_sourceGenerator,
          MagnusProbe.sourceProbe_sourceGenerator]
        by_cases hp : OuterActive p
        · rw [outerGenerator_of_active _ _ hp]
        · rw [outerGenerator_of_not_active _ _ hp, map_zero]
          rw [← MagnusProbe.sourceProbe_sourceGenerator N 0 r (by omega) p,
            generatorRead_sourceProbe_sourceGenerator, if_neg]
          intro hjp
          apply hp
          simpa [hjp] using hj
    | succ t =>
        change FreeMetabelian.HallIndex Generator t at p
        have hb : FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨t + 1, hw⟩, p⟩ : GradedHallIndex N) =
            FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw := by
          simpa only [hallIndex] using hallGradedBasis_hallIndex N t p hw
        rw [hb]
        change generatorRead 0 r j hr1
            (outerSourceProbe N r (by omega)
              (FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw)) =
          generatorRead 0 r j hr1
            (MagnusProbe.sourceProbe N 0 r (by omega)
              (FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw))
        cases t <;>
          rw [FreeMetabelian.Evaluation.hallBracket, LieHom.map_lie,
            LieHom.map_lie, generatorRead_lie, generatorRead_lie]
  exact LinearMap.congr_fun hmaps x

/-- Exact arbitrary-source generator-coordinate formula for the integral
outer mask. -/
theorem generatorRead_outerSourceProbe
    (N r : ℕ) (hr : r ≤ N + 3)
    (j : Generator) (hr1 : 1 < r) (hj : OuterActive j) (x : Source N) :
    generatorRead 0 r j hr1 (outerSourceProbe N r (by omega) x) =
      (gradedCoordinate N (generatorIndex N j) x : ZMod 0) := by
  rw [generatorRead_outerSourceProbe_eq_unmasked N r hr j hr1 hj x]
  exact generatorRead_sourceProbe N 0 r (by omega) hr1 j x

/-- On a Hall word made only of `x₅,x₄`, the integral outer mask and
unmasked probe have the same arbitrary-source Hall read. -/
theorem hallRead_outerSourceProbe_eq_unmasked
    (N r s : ℕ) (hr : r ≤ N + 3)
    (h : FreeMetabelian.HallIndex Generator s)
    (hs : s + 2 < r) (hcut : s + 1 < N + 3)
    (ha : OuterHallSurvives s h) (x : Source N) :
    hallRead 0 r s h hs (outerSourceProbe N r (by omega) x) =
      hallRead 0 r s h hs
        (MagnusProbe.sourceProbe N 0 r (by omega) x) := by
  let lhs : Source N →ₗ[ℤ] ZMod 0 :=
    (hallRead 0 r s h hs).toIntLinearMap.comp
      (outerSourceProbe N r (by omega)).toLinearMap
  let rhs : Source N →ₗ[ℤ] ZMod 0 :=
    (hallRead 0 r s h hs).toIntLinearMap.comp
      (MagnusProbe.sourceProbe N 0 r (by omega)).toLinearMap
  have hmaps : lhs = rhs := by
    apply (FreeMetabelian.Free.hallGradedBasis generatorBasis).ext
    rintro ⟨⟨w, hw⟩, p⟩
    cases w with
    | zero =>
        change Generator at p
        rw [hallGradedBasis_apply]
        change hallRead 0 r s h hs
            (outerSourceProbe N r (by omega) (sourceGenerator N p)) =
          hallRead 0 r s h hs
            (MagnusProbe.sourceProbe N 0 r (by omega) (sourceGenerator N p))
        rw [outerSourceProbe_sourceGenerator,
          MagnusProbe.sourceProbe_sourceGenerator]
        by_cases hp : OuterActive p
        · rw [outerGenerator_of_active _ _ hp]
        · rw [outerGenerator_of_not_active _ _ hp, map_zero]
          rw [← MagnusProbe.sourceProbe_sourceGenerator N 0 r (by omega) p,
            hallRead_sourceProbe_sourceGenerator]
    | succ t =>
        change FreeMetabelian.HallIndex Generator t at p
        have hb : FreeMetabelian.Free.hallGradedBasis generatorBasis
              (⟨⟨t + 1, hw⟩, p⟩ : GradedHallIndex N) =
            FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw := by
          simpa only [hallIndex] using hallGradedBasis_hallIndex N t p hw
        rw [hb]
        change hallRead 0 r s h hs
            (outerSourceProbe N r (by omega)
              (FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw)) =
          hallRead 0 r s h hs
            (MagnusProbe.sourceProbe N 0 r (by omega)
              (FreeMetabelian.Evaluation.hallBracket generatorBasis t p hw))
        by_cases hp : OuterHallSurvives t p
        · rw [outerSourceProbe_hallBracket_eq_unmasked
              N r hr t p hw hp]
        · rw [outerSourceProbe_hallBracket_eq_zero_of_not_survives
              N r hr t p hw hp, map_zero]
          by_cases hst : s = t
          · subst t
            rw [hallRead_sourceProbe_hallBracket]
            have hne : h ≠ p := by
              intro he
              subst p
              exact hp ha
            rw [if_neg hne]
          · exact (hallRead_sourceProbe_hallBracket_of_weight_ne
              N 0 r s t (by omega) h p hs hw hst).symm
  exact LinearMap.congr_fun hmaps x

/-- Exact arbitrary-source Hall-coordinate formula for the integral outer
mask. -/
theorem hallRead_outerSourceProbe
    (N r s : ℕ) (hr : r ≤ N + 3)
    (h : FreeMetabelian.HallIndex Generator s)
    (hs : s + 2 < r) (hcut : s + 1 < N + 3)
    (ha : OuterHallSurvives s h) (x : Source N) :
    hallRead 0 r s h hs (outerSourceProbe N r (by omega) x) =
      (-(hallSign s : ℤ)) •
        (gradedCoordinate N (hallIndex N s h hcut) x : ZMod 0) := by
  rw [hallRead_outerSourceProbe_eq_unmasked N r s hr h hs hcut ha x]
  exact hallRead_sourceProbe N 0 r s (by omega) h hs hcut x

/-! ## Coordinate consequences of the descended probes -/

private theorem hallSign_eq_one_or_neg_one (s : ℕ) :
    hallSign s = 1 ∨ hallSign s = -1 := by
  induction s with
  | zero => exact Or.inl rfl
  | succ s ih =>
      rw [hallSign_succ]
      rcases ih with h | h
      · right
        rw [h]
      · left
        rw [h]
        norm_num

/-- An active generator coordinate of a dimension-high lift is divisible by
the modulus of the chosen shifted row. -/
theorem modulus_dvd_generatorCoordinate_of_quotient_dimensionSubring
    (N : ℕ) (i : Fin 3) (j : Generator) (hj : Active i j)
    (x : Source N)
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4)) :
    (modulus i : ℤ) ∣ gradedCoordinate N (generatorIndex N j) x := by
  have hzero := sourceProbe_eq_zero_of_quotient_dimensionSubring
    N i 2 (by omega) hx
  have hread := generatorRead_maskedSourceProbe
    N i 2 (by omega) j (by omega) hj x
  rw [hzero, map_zero] at hread
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (gradedCoordinate N (generatorIndex N j) x) (modulus i)).mp hread.symm

/-- A surviving Hall coordinate strictly below the terminal layer is
divisible by the modulus of the chosen shifted row. -/
theorem modulus_dvd_hallCoordinate_of_quotient_dimensionSubring
    (N : ℕ) (i : Fin 3) (s : ℕ) (hsN : s < N)
    (h : FreeMetabelian.HallIndex Generator s) (ha : HallSurvives i s h)
    (x : Source N)
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4)) :
    (modulus i : ℤ) ∣
      gradedCoordinate N (hallIndex N s h (by omega)) x := by
  have hzero := sourceProbe_eq_zero_of_quotient_dimensionSubring
    N i (s + 3) (by omega) hx
  have hread := hallRead_maskedSourceProbe
    N i (s + 3) s (by omega) h (by omega) (by omega) ha x
  rw [hzero, map_zero] at hread
  have hcast :
      (gradedCoordinate N (hallIndex N s h (by omega)) x :
        ZMod (modulus i)) = 0 := by
    rcases hallSign_eq_one_or_neg_one s with hsign | hsign
    · simpa [hsign] using hread.symm
    · simpa [hsign] using hread.symm
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (gradedCoordinate N (hallIndex N s h (by omega)) x) (modulus i)).mp hcast

/-- A retained outer-generator coordinate of a dimension-high lift is
literally zero.  The coefficient ring `ZMod 0` is integral, so no congruence
information is lost. -/
theorem generatorCoordinate_eq_zero_of_outerActive_of_quotient_dimensionSubring
    (N : ℕ) (j : Generator) (hj : OuterActive j) (x : Source N)
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4)) :
    gradedCoordinate N (generatorIndex N j) x = 0 := by
  have hzero := outerSourceProbe_eq_zero_of_quotient_dimensionSubring
    N 2 (by omega) hx
  have hread := generatorRead_outerSourceProbe
    N 2 (by omega) j (by omega) hj x
  rw [hzero, map_zero] at hread
  exact hread.symm

/-- A Hall coordinate containing no small generator is literally zero through
the last layer visible to the outer descended probe. -/
theorem hallCoordinate_eq_zero_of_outerSurvives_of_quotient_dimensionSubring
    (N s : ℕ) (hsN : s ≤ N)
    (h : FreeMetabelian.HallIndex Generator s)
    (ha : OuterHallSurvives s h) (x : Source N)
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4)) :
    gradedCoordinate N (hallIndex N s h (by omega)) x = 0 := by
  have hzero := outerSourceProbe_eq_zero_of_quotient_dimensionSubring
    N (s + 3) (by omega) hx
  have hread := hallRead_outerSourceProbe
    N (s + 3) s (by omega) h (by omega) (by omega) ha x
  rw [hzero, map_zero] at hread
  have hcast :
      (gradedCoordinate N (hallIndex N s h (by omega)) x : ZMod 0) = 0 := by
    rcases hallSign_eq_one_or_neg_one s with hsign | hsign
    · rw [hsign] at hread
      rw [neg_smul, one_smul] at hread
      change (0 : ℤ) =
        -gradedCoordinate N (hallIndex N s h (by omega)) x at hread
      exact neg_eq_zero.mp hread.symm
    · rw [hsign] at hread
      rw [neg_neg, one_smul] at hread
      change (0 : ℤ) =
        gradedCoordinate N (hallIndex N s h (by omega)) x at hread
      exact hread.symm
  exact hcast

end MagnusCoordinateReads

end

end LieRings.FinitePlateau
