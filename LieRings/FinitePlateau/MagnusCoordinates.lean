import LieRings.FinitePlateau.MagnusProbe
import LieRings.FinitePlateau.TopLayer

/-!
# Hall-coordinate reads in the Magnus probes

This file proves the occurrence uniqueness needed to turn the explicit
Magnus evaluation into literal Hall-coordinate congruences.  It is kept
separate from the presentation descent: `MagnusMasks` constructs the probes,
while this file reads their individual monomial/vector coordinates.
-/

namespace LieRings.FinitePlateau

noncomputable section

namespace MagnusCoordinates

open MagnusProbe

/-- The unordered multiset of all generator occurrences of a Hall comb. -/
def hallOccurrences :
    (s : ℕ) → FreeMetabelian.HallIndex Generator s → Multiset Generator
  | 0, h => h.head ::ₘ {h.pivot}
  | s + 1, h => h.nextTooth ::ₘ hallOccurrences s h.predecessor

/-- The Magnus exponent vector is precisely the multiplicity function of
the occurrence multiset. -/
theorem hallExponent_eq_toFinsupp :
    ∀ (s : ℕ) (h : FreeMetabelian.HallIndex Generator s),
      hallExponent s h = Multiset.toFinsupp (hallOccurrences s h) := by
  intro s
  induction s with
  | zero =>
      intro h
      rw [hallExponent, hallOccurrences, ← Multiset.singleton_add,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
        Multiset.toFinsupp_singleton]
  | succ s ih =>
      intro h
      rw [hallExponent, hallOccurrences, ← Multiset.singleton_add,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, ih]

/-- The recursive occurrence ledger is the literal head, pivot, and teeth
multiset of the Hall index. -/
theorem hallOccurrences_eq_head_cons_pivot_cons_teeth
    (s : ℕ) (h : FreeMetabelian.HallIndex Generator s) :
    hallOccurrences s h =
      h.head ::ₘ h.pivot ::ₘ (h.teeth : Multiset Generator) := by
  induction s with
  | zero =>
      have ht : (h.teeth : Multiset Generator) = 0 :=
        Multiset.card_eq_zero.mp h.teeth.property
      simp [hallOccurrences, ht]
  | succ s ih =>
      rw [hallOccurrences, ih h.predecessor]
      have hteeth :
          h.nextTooth ::ₘ (h.predecessor.teeth : Multiset Generator) =
            (h.teeth : Multiset Generator) := by
        simpa only [Sym.coe_cons] using congrArg Sym.toMultiset
          (FreeMetabelian.HallIndex.nextTooth_cons_predecessor_teeth h)
      change h.nextTooth ::ₘ
          (h.head ::ₘ h.pivot ::ₘ (h.predecessor.teeth : Multiset Generator)) = _
      rw [← hteeth]
      simp only [← Multiset.singleton_add]
      simpa only [add_comm, add_left_comm, add_assoc]

private theorem hallIndex_ext {s : ℕ}
    {h k : FreeMetabelian.HallIndex Generator s}
    (hhead : h.head = k.head) (hpivot : h.pivot = k.pivot)
    (hteeth : h.teeth = k.teeth) : h = k := by
  rcases h with ⟨hh, hp, ht, hph, hpt⟩
  rcases k with ⟨kh, kp, kt, kph, kpt⟩
  simp only at hhead hpivot hteeth
  subst kh
  subst kp
  subst kt
  rfl

/-- For a standard Hall comb, its head together with its commutative
occurrence monomial determines the complete Hall index. -/
theorem hallIndex_eq_of_head_eq_of_hallExponent_eq
    {s : ℕ} (h k : FreeMetabelian.HallIndex Generator s)
    (hhead : h.head = k.head)
    (hexp : hallExponent s h = hallExponent s k) : h = k := by
  have hocc : hallOccurrences s h = hallOccurrences s k := by
    apply Multiset.toFinsupp.injective
    rw [← hallExponent_eq_toFinsupp, ← hallExponent_eq_toFinsupp]
    exact hexp
  rw [hallOccurrences_eq_head_cons_pivot_cons_teeth,
    hallOccurrences_eq_head_cons_pivot_cons_teeth] at hocc
  have hrest :
      h.pivot ::ₘ (h.teeth : Multiset Generator) =
        k.pivot ::ₘ (k.teeth : Multiset Generator) := by
    have he := congrArg (fun t : Multiset Generator ↦ t.erase h.head) hocc
    simpa only [hhead, Multiset.erase_cons_head] using he
  have hkh : k.pivot ≤ h.pivot := by
    have hm : h.pivot ∈
        k.pivot ::ₘ (k.teeth : Multiset Generator) := by
      rw [← hrest]
      simp
    rw [Multiset.mem_cons] at hm
    exact hm.elim (fun he ↦ he.symm.le)
      (fun he ↦ k.pivot_le_teeth h.pivot he)
  have hhk : h.pivot ≤ k.pivot := by
    have hm : k.pivot ∈
        h.pivot ::ₘ (h.teeth : Multiset Generator) := by
      rw [hrest]
      simp
    rw [Multiset.mem_cons] at hm
    exact hm.elim (fun he ↦ he.symm.le)
      (fun he ↦ h.pivot_le_teeth k.pivot he)
  have hpivot : h.pivot = k.pivot := le_antisymm hhk hkh
  have hteethCoe :
      (h.teeth : Multiset Generator) = (k.teeth : Multiset Generator) := by
    rw [hpivot] at hrest
    exact (Multiset.cons_inj_right k.pivot).mp hrest
  exact hallIndex_ext hhead hpivot (Sym.ext hteethCoe)

/-- With the same occurrence monomial, another Hall comb cannot have the
first comb's head as its pivot.  The smaller original pivot would violate
standardness in the second comb. -/
theorem hallExponent_eq_not_pivot_eq_head
    {s : ℕ} (h k : FreeMetabelian.HallIndex Generator s)
    (hexp : hallExponent s h = hallExponent s k) :
    k.pivot ≠ h.head := by
  intro hpivot
  have hocc : hallOccurrences s h = hallOccurrences s k := by
    apply Multiset.toFinsupp.injective
    rw [← hallExponent_eq_toFinsupp, ← hallExponent_eq_toFinsupp]
    exact hexp
  rw [hallOccurrences_eq_head_cons_pivot_cons_teeth,
    hallOccurrences_eq_head_cons_pivot_cons_teeth] at hocc
  have hmH : h.pivot ∈
      h.head ::ₘ h.pivot ::ₘ (h.teeth : Multiset Generator) := by simp
  have hmK : h.pivot ∈
      k.head ::ₘ k.pivot ::ₘ (k.teeth : Multiset Generator) := by
    rw [← hocc]
    exact hmH
  simp only [Multiset.mem_cons] at hmK
  rcases hmK with hkh | hkp | hkt
  · have hbad : h.head < h.pivot := by
      calc
        h.head = k.pivot := hpivot.symm
        _ < k.head := k.pivot_lt_head
        _ = h.pivot := hkh.symm
    exact (not_lt_of_ge h.pivot_lt_head.le) hbad
  · rw [hpivot] at hkp
    exact h.pivot_lt_head.ne hkp
  · have hle := k.pivot_le_teeth h.pivot hkt
    rw [hpivot] at hle
    exact (not_le_of_gt h.pivot_lt_head) hle

/-- Read the coefficient of the Hall monomial `h` in the vector coordinate
indexed by its head. -/
def hallRead (q r s : ℕ)
    (h : FreeMetabelian.HallIndex Generator s) (hs : s + 2 < r) :
    Target q r →+ ZMod q where
  toFun x := truncatedCoeff q r (hallExponent s h) (by simpa using hs)
    (((show Ring q r from x).vector h.head : positiveIdeal q r) :
      TruncatedPoly q r)
  map_zero' := by simp
  map_add' x y := by
    change truncatedCoeff q r (hallExponent s h) _
        ((((show Ring q r from x).vector h.head : positiveIdeal q r) :
            TruncatedPoly q r) +
          (((show Ring q r from y).vector h.head : positiveIdeal q r) :
            TruncatedPoly q r)) = _
    exact map_add _ _ _

private theorem truncatedCoeff_positive_zsmul
    (q r : ℕ) (e : Generator →₀ ℕ) (he : Finsupp.degree e < r)
    (z : ℤ) (p : positiveIdeal q r) :
    truncatedCoeff q r e he
        (((z • p : positiveIdeal q r) : TruncatedPoly q r)) =
      z • truncatedCoeff q r e he
        ((p : positiveIdeal q r) : TruncatedPoly q r) := by
  change truncatedCoeff q r e he
      (z • ((p : positiveIdeal q r) : TruncatedPoly q r)) = _
  exact (truncatedCoeff q r e he).map_zsmul
    ((p : positiveIdeal q r) : TruncatedPoly q r) z

private theorem truncatedCoeff_positive_neg
    (q r : ℕ) (e : Generator →₀ ℕ) (he : Finsupp.degree e < r)
    (p : positiveIdeal q r) :
    truncatedCoeff q r e he
        (((-p : positiveIdeal q r) : TruncatedPoly q r)) =
      -truncatedCoeff q r e he
        ((p : positiveIdeal q r) : TruncatedPoly q r) := by
  change truncatedCoeff q r e he
      (-((p : positiveIdeal q r) : TruncatedPoly q r)) = _
  exact (truncatedCoeff q r e he).map_neg
    ((p : positiveIdeal q r) : TruncatedPoly q r)

private theorem truncatedCoeff_hallProduct_eq
    (q r s : ℕ) (h k : FreeMetabelian.HallIndex Generator s)
    (hs : s + 2 < r) :
    truncatedCoeff q r (hallExponent s h) (by simpa using hs)
        (((hallProduct q r s k : positiveIdeal q r) : TruncatedPoly q r)) =
      if hallExponent s h = hallExponent s k then 1 else 0 := by
  rw [hallProduct_coe, truncatedCoeff_mk]
  by_cases he : hallExponent s h = hallExponent s k
  · rw [if_pos he, he]
    simp
  · rw [if_neg he]
    simp [MvPolynomial.coeff_monomial, he, Ne.symm he]

/-- Exact Kronecker formula on Hall brackets of the same weight.  The unit
is signed because the Magnus vector at the head is `e_pivot-e_head`. -/
theorem hallRead_sourceProbe_hallBracket
    (N q r s : ℕ) (hr : r ≤ N + 4)
    (h k : FreeMetabelian.HallIndex Generator s)
    (hs : s + 2 < r) (hcut : s + 1 < N + 3) :
    hallRead q r s h hs
        (MagnusProbe.sourceProbe N q r hr
          (FreeMetabelian.Evaluation.hallBracket generatorBasis s k hcut)) =
      if h = k then -(hallSign s : ZMod q) else 0 := by
  rw [hallRead, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    MagnusProbe.sourceProbe_hallBracket_vector]
  by_cases heq : h = k
  · subst k
    rw [if_pos rfl]
    simp only [h.pivot_lt_head.ne, if_false, if_true, zero_sub]
    rw [truncatedCoeff_positive_zsmul,
      truncatedCoeff_positive_neg,
      MagnusProbe.truncatedCoeff_hallProduct q r s h hs]
    simp
  · rw [if_neg heq]
    by_cases hexp : hallExponent s h = hallExponent s k
    · have hhead : k.head ≠ h.head := by
        intro hk
        exact heq (hallIndex_eq_of_head_eq_of_hallExponent_eq h k hk.symm hexp)
      have hpivot := hallExponent_eq_not_pivot_eq_head h k hexp
      rw [if_neg hpivot, if_neg hhead]
      rw [truncatedCoeff_positive_zsmul]
      simp
    · by_cases hpivot : k.pivot = h.head <;>
        by_cases hhead : k.head = h.head
      all_goals simp only [hpivot, hhead, if_true, if_false]
      all_goals rw [truncatedCoeff_positive_zsmul]
      · rw [sub_self]
        simp
      · rw [sub_zero, truncatedCoeff_hallProduct_eq q r s h k hs]
        simp [hexp]
      · rw [zero_sub, truncatedCoeff_positive_neg,
          truncatedCoeff_hallProduct_eq q r s h k hs]
        simp [hexp]
      · rw [sub_self]
        simp

/-- A Hall read of one manuscript weight vanishes on every Hall bracket of
a different weight.  Polynomial degree separates the two monomials. -/
theorem hallRead_sourceProbe_hallBracket_of_weight_ne
    (N q r s t : ℕ) (hr : r ≤ N + 4)
    (h : FreeMetabelian.HallIndex Generator s)
    (k : FreeMetabelian.HallIndex Generator t)
    (hs : s + 2 < r) (hcut : t + 1 < N + 3) (hst : s ≠ t) :
    hallRead q r s h hs
        (MagnusProbe.sourceProbe N q r hr
          (FreeMetabelian.Evaluation.hallBracket generatorBasis t k hcut)) =
      0 := by
  have hexp : hallExponent s h ≠ hallExponent t k := by
    intro he
    have hd := congrArg Finsupp.degree he
    rw [hallExponent_degree, hallExponent_degree] at hd
    omega
  have hcoeff : truncatedCoeff q r (hallExponent s h) (by simpa using hs)
      (((hallProduct q r t k : positiveIdeal q r) : TruncatedPoly q r)) = 0 := by
    rw [hallProduct_coe, truncatedCoeff_mk]
    simp [MvPolynomial.coeff_monomial, hexp, Ne.symm hexp]
  rw [hallRead, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    MagnusProbe.sourceProbe_hallBracket_vector]
  by_cases hpivot : k.pivot = h.head <;>
      by_cases hhead : k.head = h.head
  · simp only [hpivot, hhead, if_true, sub_self, smul_zero]
    rw [truncatedCoeff_positive_zsmul]
    have hz : (((0 : positiveIdeal q r) : TruncatedPoly q r)) = 0 := rfl
    rw [hz]
    change (hallSign t : ℤ) •
      truncatedCoeff q r (hallExponent s h) _
        (0 : TruncatedPoly q r) = 0
    rw [map_zero, smul_zero]
  · simp only [hpivot, hhead, if_true, if_false, sub_zero]
    rw [truncatedCoeff_positive_zsmul, hcoeff, smul_zero]
  · simp only [hpivot, hhead, if_false, if_true, zero_sub]
    rw [truncatedCoeff_positive_zsmul, truncatedCoeff_positive_neg,
      hcoeff, neg_zero, smul_zero]
  · simp only [hpivot, hhead, if_false, sub_self, smul_zero]
    rw [truncatedCoeff_positive_zsmul]
    have hz : (((0 : positiveIdeal q r) : TruncatedPoly q r)) = 0 := rfl
    rw [hz]
    change (hallSign t : ℤ) •
      truncatedCoeff q r (hallExponent s h) _
        (0 : TruncatedPoly q r) = 0
    rw [map_zero, smul_zero]

/-! ## Weight-one scalar reads -/

/-- Read the coefficient of `X_j` in the scalar Magnus coordinate. -/
def generatorRead (q r : ℕ) (j : Generator) (hr : 1 < r) :
    Target q r →+ ZMod q where
  toFun x := truncatedCoeff q r (Finsupp.single j 1) (by
    simpa [Finsupp.degree_single])
      (((show Ring q r from x).scalar : positiveIdeal q r) :
        TruncatedPoly q r)
  map_zero' := by simp
  map_add' x y := by
    change truncatedCoeff q r (Finsupp.single j 1) _
      ((((show Ring q r from x).scalar : positiveIdeal q r) :
          TruncatedPoly q r) +
        (((show Ring q r from y).scalar : positiveIdeal q r) :
          TruncatedPoly q r)) = _
    exact map_add _ _ _

@[simp] theorem generatorRead_sourceProbe_sourceGenerator
    (N q r : ℕ) (hr : r ≤ N + 4) (hr1 : 1 < r)
    (j k : Generator) :
    generatorRead q r j hr1
        (MagnusProbe.sourceProbe N q r hr (sourceGenerator N k)) =
      if j = k then 1 else 0 := by
  rw [MagnusProbe.sourceProbe_sourceGenerator, generatorRead,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Ring.generator_scalar,
    varImage_coe, truncatedCoeff_mk]
  by_cases hjk : j = k
  · subst k
    simp [MvPolynomial.X]
  · rw [if_neg hjk]
    have hsingle : Finsupp.single k 1 ≠ Finsupp.single j 1 := by
      intro he
      have hev := congrArg (fun e : Generator →₀ ℕ ↦ e k) he
      simp [Finsupp.single_apply, hjk] at hev
    change MvPolynomial.coeff (Finsupp.single j 1)
      (MvPolynomial.X k : Poly q) = 0
    rw [MvPolynomial.X, MvPolynomial.coeff_monomial]
    simp [hsingle]

@[simp] theorem generatorRead_sourceProbe_hallBracket
    (N q r t : ℕ) (hr : r ≤ N + 4) (hr1 : 1 < r)
    (k : FreeMetabelian.HallIndex Generator t)
    (hcut : t + 1 < N + 3) (j : Generator) :
    generatorRead q r j hr1
        (MagnusProbe.sourceProbe N q r hr
          (FreeMetabelian.Evaluation.hallBracket generatorBasis t k hcut)) =
      0 := by
  rw [generatorRead, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    MagnusProbe.sourceProbe_hallBracket_scalar]
  exact map_zero _

end MagnusCoordinates

end

end LieRings.FinitePlateau
