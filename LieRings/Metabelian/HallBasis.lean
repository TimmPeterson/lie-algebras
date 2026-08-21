import LieRings.Metabelian.FreeComponent
import Mathlib.Order.Hom.PowersetCard

/-!
# Integral Hall coordinates for the free metabelian components

For manuscript weight `q+2`, a Hall index is
`[x_head,x_pivot,teeth]` with `pivot < head` and every tooth at least
`pivot`.  The orientation is deliberately `head ∧ pivot`; Mathlib's exterior
basis uses the opposite, increasing orientation.
-/

open TensorProduct

namespace FreeMetabelian

universe u v

noncomputable section

/-- Indices of standard metabelian combs with `q` symmetric teeth. -/
structure HallIndex (ι : Type u) [LinearOrder ι] (q : ℕ) where
  head : ι
  pivot : ι
  teeth : Sym ι q
  pivot_lt_head : pivot < head
  pivot_le_teeth : ∀ i, i ∈ (teeth : Multiset ι) → pivot ≤ i

namespace HallIndex

variable {ι : Type u} [LinearOrder ι]

instance (q : ℕ) : DecidableEq (HallIndex ι q) := Classical.decEq _
instance [Finite ι] (q : ℕ) : Finite (HallIndex ι q) := by
  let f : HallIndex ι q → ι × ι × Sym ι q :=
    fun h ↦ (h.head, h.pivot, h.teeth)
  exact Finite.of_injective f (by
    rintro ⟨ah, ap, ateeth, ahp, ahs⟩ ⟨bh, bp, bt, bhp, bhs⟩ h
    change (ah, ap, ateeth) = (bh, bp, bt) at h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    rfl)

/-- The free coordinate module on standard combs. -/
abbrev Module (q : ℕ) := HallIndex ι q →₀ ℤ

end HallIndex

section Based

variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable {X : Type v} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (b : Module.Basis ι ℤ X)

private def wedge (head pivot : ι) : ⋀[ℤ]^2 X :=
  exteriorPower.ιMulti ℤ 2 (Fin.cons (b head) (Fin.cons (b pivot) Fin.elim0))

/-- The standard comb represented in its homogeneous quotient. -/
def hallVector (q : ℕ) (h : HallIndex ι q) : Component X q := by
  cases q with
  | zero =>
      exact wedge b h.head h.pivot
  | succ q =>
      exact (commutatorClass X q)
        (wedge b h.head h.pivot ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis b (q + 1) h.teeth)

/-- The tautological map from formal Hall coordinates to the Jacobi quotient. -/
def hallMap (q : ℕ) : HallIndex.Module (ι := ι) q →ₗ[ℤ] Component X q :=
  Finsupp.linearCombination ℤ (hallVector b q)

@[simp]
theorem hallMap_single (q : ℕ) (h : HallIndex ι q) :
    hallMap b q (Finsupp.single h 1) = hallVector b q h := by
  rw [hallMap, Finsupp.linearCombination_single]
  module

private def isStandard {q : ℕ} (pivot : ι) (s : Sym ι q) : Prop :=
  ∀ i, i ∈ (s : Multiset ι) → pivot ≤ i

private instance {q : ℕ} (pivot : ι) (s : Sym ι q) :
    Decidable (isStandard pivot s) := Classical.propDecidable _

private def standardIndex {q : ℕ} (head pivot : ι) (s : Sym ι q)
    (hp : pivot < head) (hs : isStandard pivot s) : HallIndex ι q where
  head := head
  pivot := pivot
  teeth := s
  pivot_lt_head := hp
  pivot_le_teeth := hs

private theorem teeth_nonempty {q : ℕ} (s : Sym ι (q + 1)) :
    (s : Multiset ι).toFinset.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hs : (s : Multiset ι) = 0 := Multiset.toFinset_eq_empty.mp h
  have hc := congrArg Multiset.card hs
  simp only [Multiset.card_zero] at hc
  have hz : q + 1 = 0 := s.property.symm.trans hc
  exact Nat.succ_ne_zero q hz

private def leastTooth {q : ℕ} (s : Sym ι (q + 1)) : ι :=
  (s : Multiset ι).toFinset.min' (teeth_nonempty s)

private theorem leastTooth_mem {q : ℕ} (s : Sym ι (q + 1)) :
    leastTooth s ∈ (s : Multiset ι) := by
  exact Multiset.mem_toFinset.mp
    (Finset.min'_mem _ (teeth_nonempty s))

private theorem leastTooth_le {q : ℕ} (s : Sym ι (q + 1))
    {i : ι} (hi : i ∈ (s : Multiset ι)) : leastTooth s ≤ i := by
  exact Finset.min'_le _ i (Multiset.mem_toFinset.mpr hi)

private def eraseLeast {q : ℕ} (s : Sym ι (q + 1)) : Sym ι q :=
  s.erase (leastTooth s) (leastTooth_mem s)

private theorem mem_eraseLeast {q : ℕ} (s : Sym ι (q + 1))
    {i : ι} (hi : i ∈ (eraseLeast s : Multiset ι)) :
    i ∈ (s : Multiset ι) := by
  exact Multiset.mem_of_mem_erase hi

private theorem cons_eraseLeast {q : ℕ} (s : Sym ι (q + 1)) :
    leastTooth s ::ₛ eraseLeast s = s := by
  apply Sym.ext
  exact Multiset.cons_erase (leastTooth_mem s)

/-- The manuscript's one-step Hall collector on an already oriented comb.
If the pivot is not the least entry, it applies
`[a,b]c = [a,c]b - [b,c]a` exactly once. -/
private def normalizeOriented :
    (q : ℕ) → (head pivot : ι) → pivot < head → Sym ι q →
      HallIndex.Module (ι := ι) q
  | 0, head, pivot, hp, s =>
      Finsupp.single (standardIndex head pivot s hp (by
        intro i hi
        have hz : s = Sym.nil := Subsingleton.elim _ _
        subst s
        simpa using hi)) 1
  | q + 1, head, pivot, hp, s =>
      if hs : isStandard pivot s then
        Finsupp.single (standardIndex head pivot s hp hs) 1
      else
        let c := leastTooth s
        let r := eraseLeast s
        have hc_lt : c < pivot := by
          simp only [isStandard] at hs
          push_neg at hs
          obtain ⟨i, hit, hnot⟩ := hs
          exact (leastTooth_le s hit).trans_lt hnot
        have hc_head : c < head := hc_lt.trans hp
        have hc_pivot : c < pivot := hc_lt
        have hcr : ∀ i, i ∈ (r : Multiset ι) → c ≤ i :=
          fun i hi ↦ leastTooth_le s (mem_eraseLeast s hi)
        have hfirst : isStandard c (pivot ::ₛ r) := by
          intro i hi
          rw [Sym.coe_cons, Multiset.mem_cons] at hi
          exact hi.elim (fun h ↦ h ▸ hc_lt.le) (hcr i)
        have hsecond : isStandard c (head ::ₛ r) := by
          intro i hi
          rw [Sym.coe_cons, Multiset.mem_cons] at hi
          exact hi.elim (fun h ↦ h ▸ hc_head.le) (hcr i)
        Finsupp.single
            (standardIndex head c (pivot ::ₛ r) hc_head hfirst) 1 -
          Finsupp.single
            (standardIndex pivot c (head ::ₛ r) hc_pivot hsecond) 1

private theorem normalizeOriented_standard (q : ℕ) (h : HallIndex ι q) :
    normalizeOriented q h.head h.pivot h.pivot_lt_head h.teeth =
      Finsupp.single h 1 := by
  rcases h with ⟨head, pivot, teeth, hp, hs⟩
  cases q with
  | zero =>
      simp only [normalizeOriented]
      congr 1
  | succ q =>
      change normalizeOriented (q + 1) head pivot hp teeth =
        Finsupp.single
          { head := head, pivot := pivot, teeth := teeth,
            pivot_lt_head := hp, pivot_le_teeth := hs } 1
      rw [normalizeOriented]
      split
      · congr 1
      · rename_i hnot
        exact (hnot hs).elim

private def pairLow (s : Set.powersetCard ι 2) : ι :=
  Set.powersetCard.ofFinEmbEquiv.symm s 0

private def pairHigh (s : Set.powersetCard ι 2) : ι :=
  Set.powersetCard.ofFinEmbEquiv.symm s 1

private theorem pairLow_lt_pairHigh (s : Set.powersetCard ι 2) :
    pairLow s < pairHigh s := by
  exact (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono (by decide)

private def pairEmbedding (pivot head : ι) (h : pivot < head) : Fin 2 ↪o ι :=
  OrderEmbedding.ofStrictMono
    (Fin.cons pivot (Fin.cons head Fin.elim0)) (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · simp at hij
      · exact h
      · simp at hij
      · simp at hij)

private def pairIndex (pivot head : ι) (h : pivot < head) :
    Set.powersetCard ι 2 :=
  Set.powersetCard.ofFinEmbEquiv (pairEmbedding pivot head h)

@[simp]
private theorem pairLow_pairIndex (pivot head : ι) (h : pivot < head) :
    pairLow (pairIndex pivot head h) = pivot := by
  rw [pairLow, pairIndex, Equiv.symm_apply_apply]
  rfl

@[simp]
private theorem pairHigh_pairIndex (pivot head : ι) (h : pivot < head) :
    pairHigh (pairIndex pivot head h) = head := by
  rw [pairHigh, pairIndex, Equiv.symm_apply_apply]
  rfl

private theorem pairIndex_pairLow_pairHigh (s : Set.powersetCard ι 2) :
    pairIndex (pairLow s) (pairHigh s) (pairLow_lt_pairHigh s) = s := by
  change Set.powersetCard.ofFinEmbEquiv
      (pairEmbedding (pairLow s) (pairHigh s) (pairLow_lt_pairHigh s)) = s
  rw [show pairEmbedding (pairLow s) (pairHigh s)
      (pairLow_lt_pairHigh s) =
        Set.powersetCard.ofFinEmbEquiv.symm s by
    ext i
    fin_cases i <;> rfl]
  exact Equiv.apply_symm_apply Set.powersetCard.ofFinEmbEquiv s

private theorem exteriorBasis_pairIndex (pivot head : ι) (h : pivot < head) :
    b.exteriorPower 2 (pairIndex pivot head h) =
      exteriorPower.ιMulti ℤ 2
        (Fin.cons (b pivot) (Fin.cons (b head) Fin.elim0)) := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family pairIndex pairEmbedding
  rw [Equiv.symm_apply_apply]
  rfl

private theorem exteriorBasis_eq_wedge_low_high
    (s : Set.powersetCard ι 2) :
    b.exteriorPower 2 s = wedge b (pairLow s) (pairHigh s) := by
  calc
    b.exteriorPower 2 s = b.exteriorPower 2
        (pairIndex (pairLow s) (pairHigh s) (pairLow_lt_pairHigh s)) := by
          rw [pairIndex_pairLow_pairHigh]
    _ = exteriorPower.ιMulti ℤ 2
        (Fin.cons (b (pairLow s))
          (Fin.cons (b (pairHigh s)) Fin.elim0)) :=
      exteriorBasis_pairIndex b _ _ _
    _ = wedge b (pairLow s) (pairHigh s) := rfl

private theorem wedge_skew (head pivot : ι) :
    wedge b head pivot = -wedge b pivot head := by
  have h := (exteriorPower.ιMulti ℤ 2).map_swap
    (v := Fin.cons (b pivot) (Fin.cons (b head) Fin.elim0))
    (i := 0) (j := 1) (by decide)
  change wedge b head pivot = -wedge b pivot head at h
  exact h

private theorem removeNth_pair_zero {Y : Type*} (x y : Y) :
    (0 : Fin 2).removeNth
        (show Fin 2 → Y from Fin.cons x (Fin.cons y Fin.elim0)) =
      (fun _ : Fin 1 => y) := by
  funext i
  fin_cases i
  rfl

private theorem removeNth_pair_one {Y : Type*} (x y : Y) :
    (1 : Fin 2).removeNth
        (show Fin 2 → Y from Fin.cons x (Fin.cons y Fin.elim0)) =
      (fun _ : Fin 1 => x) := by
  funext i
  fin_cases i
  rfl

private theorem removeNth_triple_zero {Y : Type*} (x y z : Y) :
    (0 : Fin 3).removeNth
        (show Fin 3 → Y from
          Fin.cons x (Fin.cons y (Fin.cons z Fin.elim0))) =
      Fin.cons y (Fin.cons z Fin.elim0) := by
  funext i
  fin_cases i <;> rfl

private theorem removeNth_triple_one {Y : Type*} (x y z : Y) :
    (1 : Fin 3).removeNth
        (show Fin 3 → Y from
          Fin.cons x (Fin.cons y (Fin.cons z Fin.elim0))) =
      Fin.cons x (Fin.cons z Fin.elim0) := by
  funext i
  fin_cases i <;> rfl

private theorem removeNth_triple_two {Y : Type*} (x y z : Y) :
    (2 : Fin 3).removeNth
        (show Fin 3 → Y from
          Fin.cons x (Fin.cons y (Fin.cons z Fin.elim0))) =
      Fin.cons x (Fin.cons y Fin.elim0) := by
  funext i
  fin_cases i <;> rfl

@[simp]
private theorem pair_apply_zero {Y : Type*} (x y : Y) :
    (Fin.cons x (Fin.cons y Fin.elim0) : Fin 2 → Y) 0 = x := rfl

@[simp]
private theorem pair_apply_one {Y : Type*} (x y : Y) :
    (Fin.cons x (Fin.cons y Fin.elim0) : Fin 2 → Y) 1 = y := rfl

/-- The explicit Hall normalizer on the tensor-monomial basis.  The initial
minus sign is the conversion from Mathlib's increasing wedge
`pivot ∧ head` to the manuscript's `head ∧ pivot`. -/
private def preNormalizer (q : ℕ) :
    PreComponent X q →ₗ[ℤ] HallIndex.Module (ι := ι) q :=
  TensorProduct.lift <|
    (b.exteriorPower 2).constr ℤ (fun w ↦
      (SymmetricPower.monomialBasis b q).constr ℤ (fun s ↦
        -normalizeOriented q (pairHigh w) (pairLow w)
          (pairLow_lt_pairHigh w) s))

/-- Evaluation of the normalizer on an oriented basis comb. -/
private theorem preNormalizer_oriented (q : ℕ) (head pivot : ι)
    (hp : pivot < head) (s : Sym ι q) :
    preNormalizer (b := b) q
        (wedge b head pivot ⊗ₜ[ℤ] SymmetricPower.monomialBasis b q s) =
      normalizeOriented q head pivot hp s := by
  have hwedge : wedge b head pivot =
      -(b.exteriorPower 2 (pairIndex pivot head hp)) := by
    rw [exteriorBasis_pairIndex]
    exact wedge_skew b head pivot
  rw [hwedge, TensorProduct.neg_tmul, map_neg, preNormalizer]
  change -(((b.exteriorPower 2).constr ℤ (fun w ↦
      (SymmetricPower.monomialBasis b q).constr ℤ (fun t ↦
        -normalizeOriented q (pairHigh w) (pairLow w)
          (pairLow_lt_pairHigh w) t)))
      (b.exteriorPower 2 (pairIndex pivot head hp))
      (SymmetricPower.monomialBasis b q s)) = _
  rw [Module.Basis.constr_basis, Module.Basis.constr_basis]
  simp

private theorem hallMap_normalizeOriented_succ (q : ℕ)
    (head pivot : ι) (hp : pivot < head) (s : Sym ι (q + 1)) :
    hallMap b (q + 1) (normalizeOriented (q + 1) head pivot hp s) =
      (commutatorClass X q)
        (wedge b head pivot ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis b (q + 1) s) := by
  rw [normalizeOriented]
  split
  · rw [hallMap_single]
    rfl
  · rename_i hs
    let c := leastTooth s
    let r := eraseLeast s
    have hc_lt : c < pivot := by
      simp only [isStandard] at hs
      push Not at hs
      obtain ⟨i, hit, hnot⟩ := hs
      exact (leastTooth_le s hit).trans_lt hnot
    have hc_head : c < head := hc_lt.trans hp
    have hcr : ∀ i, i ∈ (r : Multiset ι) → c ≤ i :=
      fun i hi ↦ leastTooth_le s (mem_eraseLeast s hi)
    have hfirst : isStandard c (pivot ::ₛ r) := by
      intro i hi
      rw [Sym.coe_cons, Multiset.mem_cons] at hi
      exact hi.elim (fun h ↦ h ▸ hc_lt.le) (hcr i)
    have hsecond : isStandard c (head ::ₛ r) := by
      intro i hi
      rw [Sym.coe_cons, Multiset.mem_cons] at hi
      exact hi.elim (fun h ↦ h ▸ hc_head.le) (hcr i)
    change hallMap b (q + 1)
        (Finsupp.single
            (standardIndex head c (pivot ::ₛ r) hc_head hfirst) 1 -
          Finsupp.single
            (standardIndex pivot c (head ::ₛ r) hc_lt hsecond) 1) = _
    rw [map_sub, hallMap_single, hallMap_single]
    change (commutatorClass X q)
          (wedge b head c ⊗ₜ[ℤ]
            SymmetricPower.monomialBasis b (q + 1) (pivot ::ₛ r)) -
        (commutatorClass X q)
          (wedge b pivot c ⊗ₜ[ℤ]
            SymmetricPower.monomialBasis b (q + 1) (head ::ₛ r)) = _
    let a : Fin 3 → X :=
      Fin.cons (b head) (Fin.cons (b pivot) (Fin.cons (b c) Fin.elim0))
    let u : Sym[ℤ] (Fin q) X := SymmetricPower.monomialBasis b q r
    let A : Component X (q + 1) := (commutatorClass X q)
      (wedge b head c ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis b (q + 1) (pivot ::ₛ r))
    let B : Component X (q + 1) := (commutatorClass X q)
      (wedge b pivot c ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis b (q + 1) (head ::ₛ r))
    let C : Component X (q + 1) := (commutatorClass X q)
      (wedge b head pivot ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis b (q + 1) s)
    change A - B = C
    have hj : (commutatorClass X q) (jacobi X (q + 1)
        (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] u)) = 0 := by
      change (LinearMap.range (jacobi X (q + 1))).mkQ
        (jacobi X (q + 1)
          (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] u)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] u, rfl⟩
    rw [jacobi_wedge_tmul, map_add, map_sub,
      removeNth_triple_zero, removeNth_triple_one,
      removeNth_triple_two] at hj
    change (commutatorClass X q)
          (wedge b pivot c ⊗ₜ[ℤ]
            SymmetricPower.insert ℤ X q (b head) u) -
        (commutatorClass X q)
          (wedge b head c ⊗ₜ[ℤ]
            SymmetricPower.insert ℤ X q (b pivot) u) +
        (commutatorClass X q)
          (wedge b head pivot ⊗ₜ[ℤ]
            SymmetricPower.insert ℤ X q (b c) u) = 0 at hj
    rw [SymmetricPower.insert_monomialBasis,
      SymmetricPower.insert_monomialBasis,
      SymmetricPower.insert_monomialBasis] at hj
    have hsr : c ::ₛ r = s := cons_eraseLeast s
    rw [hsr] at hj
    change B - A + C = 0 at hj
    have hBA : B - A = -C := eq_neg_of_add_eq_zero_left hj
    calc
      A - B = -(B - A) := by abel
      _ = -(-C) := congrArg Neg.neg hBA
      _ = C := neg_neg C

private theorem hallMap_comp_preNormalizer_succ (q : ℕ) :
    (hallMap b (q + 1)).comp (preNormalizer (b := b) (q + 1)) =
      commutatorClass X q := by
  apply TensorProduct.ext
  apply (b.exteriorPower 2).ext
  intro w
  apply (SymmetricPower.monomialBasis b (q + 1)).ext
  intro s
  change ((hallMap b (q + 1)).comp (preNormalizer (b := b) (q + 1)))
      (b.exteriorPower 2 w ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis b (q + 1) s) =
      (commutatorClass X q)
        (b.exteriorPower 2 w ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis b (q + 1) s)
  rw [LinearMap.comp_apply, preNormalizer]
  change hallMap b (q + 1)
      (((b.exteriorPower 2).constr ℤ (fun w ↦
        (SymmetricPower.monomialBasis b (q + 1)).constr ℤ (fun s ↦
          -normalizeOriented (q + 1) (pairHigh w) (pairLow w)
            (pairLow_lt_pairHigh w) s)))
        (b.exteriorPower 2 w)
        (SymmetricPower.monomialBasis b (q + 1) s)) = _
  rw [Module.Basis.constr_basis, Module.Basis.constr_basis]
  rw [map_neg, hallMap_normalizeOriented_succ,
    exteriorBasis_eq_wedge_low_high]
  rw [wedge_skew b (pairHigh w) (pairLow w), neg_tmul, map_neg]
  simp

private def componentTwoNormalizer :
    Component X 0 →ₗ[ℤ] HallIndex.Module (ι := ι) 0 :=
  (b.exteriorPower 2).constr ℤ (fun w ↦
    -normalizeOriented 0 (pairHigh w) (pairLow w)
      (pairLow_lt_pairHigh w) Sym.nil)

private theorem hallMap_comp_componentTwoNormalizer :
    (hallMap b 0).comp (componentTwoNormalizer b) = LinearMap.id := by
  apply (b.exteriorPower 2).ext
  intro w
  change hallMap b 0 (componentTwoNormalizer b (b.exteriorPower 2 w)) =
    b.exteriorPower 2 w
  rw [componentTwoNormalizer]
  change hallMap b 0 (((b.exteriorPower 2).constr ℤ (fun w ↦
      -normalizeOriented 0 (pairHigh w) (pairLow w)
        (pairLow_lt_pairHigh w) Sym.nil)) (b.exteriorPower 2 w)) = _
  rw [Module.Basis.constr_basis]
  rw [map_neg]
  change -hallMap b 0 (Finsupp.single
      (standardIndex (pairHigh w) (pairLow w) Sym.nil
        (pairLow_lt_pairHigh w) (by
          intro i hi
          simpa using hi)) 1) = _
  rw [hallMap_single]
  change -wedge b (pairHigh w) (pairLow w) = b.exteriorPower 2 w
  rw [exteriorBasis_eq_wedge_low_high,
    wedge_skew b (pairHigh w) (pairLow w)]
  simp

/-- The alternating-boundary representation of a metabelian component.  In
positive symmetric degree it descends because consecutive boundaries compose
to zero. -/
private def representation :
    (q : ℕ) → Component X q →ₗ[ℤ]
      (⋀[ℤ]^1 X) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) X
  | 0 =>
      (JacobiBoundary.differential
        (LinearMap.id : X →ₗ[ℤ] X) 1 0).comp
          ((TensorProduct.mk ℤ (⋀[ℤ]^2 X)
            (Sym[ℤ] (Fin 0) X)).flip
              (SymmetricPower.monomialBasis b 0 Sym.nil))
  | q + 1 =>
      (LinearMap.range (jacobi X (q + 1))).liftQ
        (JacobiBoundary.differential
          (LinearMap.id : X →ₗ[ℤ] X) 1 (q + 1)) (by
            rintro _ ⟨z, rfl⟩
            change JacobiBoundary.differential LinearMap.id 1 (q + 1)
              (JacobiBoundary.differential LinearMap.id 2 q z) = 0
            exact LinearMap.congr_fun
              (JacobiBoundary.differential_comp_differential
                (LinearMap.id : X →ₗ[ℤ] X) 1 q) z)

private theorem representation_hallVector (q : ℕ) (h : HallIndex ι q) :
    representation b q (hallVector b q h) =
      exteriorPower.ιMulti ℤ 1 (Fin.cons (b h.head) Fin.elim0) ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis b (q + 1) (h.pivot ::ₛ h.teeth) -
        exteriorPower.ιMulti ℤ 1 (Fin.cons (b h.pivot) Fin.elim0) ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis b (q + 1) (h.head ::ₛ h.teeth) := by
  cases q with
  | zero =>
      change JacobiBoundary.differential LinearMap.id 1 0
          (wedge b h.head h.pivot ⊗ₜ[ℤ]
            SymmetricPower.monomialBasis b 0 Sym.nil) = _
      rw [show h.teeth = Sym.nil from Subsingleton.elim _ _, wedge,
        JacobiBoundary.differential_wedge_tmul, Fin.sum_univ_two]
      simp only [Fin.val_zero, Nat.reduceSubDiff, one_smul,
        LinearMap.id_apply, Fin.val_one, pow_one, neg_smul, Fin.isValue]
      rw [removeNth_pair_zero, removeNth_pair_one]
      rw [pair_apply_zero, pair_apply_one]
      simp only [pow_zero, one_smul]
      rw [SymmetricPower.insert_monomialBasis,
        SymmetricPower.insert_monomialBasis]
      have hhead : (fun _ : Fin 1 => b h.head) =
          Fin.cons (b h.head) Fin.elim0 := by funext i; fin_cases i; rfl
      have hpivot : (fun _ : Fin 1 => b h.pivot) =
          Fin.cons (b h.pivot) Fin.elim0 := by funext i; fin_cases i; rfl
      rw [hhead, hpivot]
      abel
  | succ q =>
      change JacobiBoundary.differential LinearMap.id 1 (q + 1)
          (wedge b h.head h.pivot ⊗ₜ[ℤ]
            SymmetricPower.monomialBasis b (q + 1) h.teeth) = _
      rw [wedge, JacobiBoundary.differential_wedge_tmul,
        Fin.sum_univ_two]
      simp only [Fin.val_zero, Nat.reduceSubDiff, one_smul,
        LinearMap.id_apply, Fin.val_one, pow_one, neg_smul, Fin.isValue]
      rw [removeNth_pair_zero, removeNth_pair_one]
      rw [pair_apply_zero, pair_apply_one]
      simp only [pow_zero, one_smul]
      rw [SymmetricPower.insert_monomialBasis,
        SymmetricPower.insert_monomialBasis]
      have hhead : (fun _ : Fin 1 => b h.head) =
          Fin.cons (b h.head) Fin.elim0 := by funext i; fin_cases i; rfl
      have hpivot : (fun _ : Fin 1 => b h.pivot) =
          Fin.cons (b h.pivot) Fin.elim0 := by funext i; fin_cases i; rfl
      rw [hhead, hpivot]
      abel

private theorem hall_eq_of_head_cons_eq {q : ℕ} (h k : HallIndex ι q)
    (hhead : h.head = k.head)
    (hcons : h.pivot ::ₛ h.teeth = k.pivot ::ₛ k.teeth) : h = k := by
  have hm : h.pivot ::ₘ (h.teeth : Multiset ι) =
      k.pivot ::ₘ (k.teeth : Multiset ι) :=
    congrArg Sym.toMultiset hcons
  have hmemH : h.pivot ∈ k.pivot ::ₘ (k.teeth : Multiset ι) := by
    rw [← hm]
    exact Multiset.mem_cons_self _ _
  have hmemK : k.pivot ∈ h.pivot ::ₘ (h.teeth : Multiset ι) := by
    rw [hm]
    exact Multiset.mem_cons_self _ _
  have hkh : k.pivot ≤ h.pivot := by
    rw [Multiset.mem_cons] at hmemH
    exact hmemH.elim (fun e ↦ e ▸ le_rfl) (k.pivot_le_teeth _)
  have hhk : h.pivot ≤ k.pivot := by
    rw [Multiset.mem_cons] at hmemK
    exact hmemK.elim (fun e ↦ e ▸ le_rfl) (h.pivot_le_teeth _)
  have hpivot : h.pivot = k.pivot := le_antisymm hhk hkh
  have hteeth : h.teeth = k.teeth := by
    apply Sym.ext
    rw [hpivot] at hm
    exact (Multiset.cons_inj_right k.pivot).mp hm
  cases h
  cases k
  simp_all

private theorem hall_negative_coordinate_impossible {q : ℕ}
    (h k : HallIndex ι q) (hfirst : h.head = k.pivot)
    (hcons : h.pivot ::ₛ h.teeth = k.head ::ₛ k.teeth) : False := by
  have hm : h.pivot ::ₘ (h.teeth : Multiset ι) =
      k.head ::ₘ (k.teeth : Multiset ι) :=
    congrArg Sym.toMultiset hcons
  have hpivot_mem : h.pivot ∈ k.head ::ₘ (k.teeth : Multiset ι) := by
    rw [← hm]
    exact Multiset.mem_cons_self _ _
  have hk_le : k.pivot ≤ h.pivot := by
    rw [Multiset.mem_cons] at hpivot_mem
    exact hpivot_mem.elim (fun e ↦ e ▸ k.pivot_lt_head.le)
      (k.pivot_le_teeth _)
  have hh_lt : h.pivot < k.pivot := h.pivot_lt_head.trans_le hfirst.le
  exact (not_lt_of_ge hk_le) hh_lt

private def singletonEmbedding (i : ι) : Fin 1 ↪o ι :=
  OrderEmbedding.ofStrictMono (fun _ ↦ i) (by
    intro a c hac
    fin_cases a
    fin_cases c
    simp at hac)

private def singletonIndex (i : ι) : Set.powersetCard ι 1 :=
  Set.powersetCard.ofFinEmbEquiv (singletonEmbedding i)

private theorem exteriorBasis_singletonIndex (i : ι) :
    b.exteriorPower 1 (singletonIndex i) =
      exteriorPower.ιMulti ℤ 1 (Fin.cons (b i) Fin.elim0) := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family singletonIndex singletonEmbedding
  rw [Equiv.symm_apply_apply]
  apply congrArg (exteriorPower.ιMulti ℤ 1)
  funext x
  fin_cases x
  rfl

private def tensorCoordinate (q : ℕ) (i : ι) (s : Sym ι (q + 1)) :
    ((⋀[ℤ]^1 X) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) X) →ₗ[ℤ] ℤ :=
  TensorProduct.lift {
    toFun := fun w ↦ (b.exteriorPower 1).coord (singletonIndex i) w •
      (SymmetricPower.monomialBasis b (q + 1)).coord s
    map_add' := by
      intro x y
      ext t
      simp [add_smul]
    map_smul' := by
      intro z x
      ext t
      simp [mul_smul] }

private theorem tensorCoordinate_basis (q : ℕ) (i j : ι)
    (s t : Sym ι (q + 1)) :
    tensorCoordinate b q i s
        (exteriorPower.ιMulti ℤ 1 (Fin.cons (b j) Fin.elim0) ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis b (q + 1) t) =
      if i = j ∧ s = t then 1 else 0 := by
  rw [← exteriorBasis_singletonIndex]
  change ((b.exteriorPower 1).coord (singletonIndex i)
      (b.exteriorPower 1 (singletonIndex j))) *
    ((SymmetricPower.monomialBasis b (q + 1)).coord s
      (SymmetricPower.monomialBasis b (q + 1) t)) = _
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  by_cases hij : i = j
  · subst j
    by_cases hst : s = t
    · simp [hst]
    · simp [hst, Ne.symm hst]
  · have hsij : singletonIndex i ≠ singletonIndex j := by
      intro heq
      have he := congrArg
        (fun e : Set.powersetCard ι 1 ↦
          Set.powersetCard.ofFinEmbEquiv.symm e 0) heq
      exact hij (by simpa [singletonIndex, singletonEmbedding] using he)
    simp [hij, hsij, Ne.symm hsij]

private theorem separatingCoordinate (q : ℕ) (h k : HallIndex ι q) :
    tensorCoordinate b q h.head (h.pivot ::ₛ h.teeth)
        (representation b q (hallVector b q k)) =
      if h = k then 1 else 0 := by
  rw [representation_hallVector, map_sub,
    tensorCoordinate_basis, tensorCoordinate_basis]
  by_cases hhk : h = k
  · subst k
    simp [h.pivot_lt_head.ne, h.pivot_lt_head.ne']
  · have hpos : ¬(h.head = k.head ∧
        h.pivot ::ₛ h.teeth = k.pivot ::ₛ k.teeth) := by
      intro hp
      exact hhk (hall_eq_of_head_cons_eq h k hp.1 hp.2)
    have hneg : ¬(h.head = k.pivot ∧
        h.pivot ::ₛ h.teeth = k.head ::ₛ k.teeth) := by
      intro hn
      exact hall_negative_coordinate_impossible h k hn.1 hn.2
    simp [hhk, hpos, hneg]

private theorem coordinate_hallMap (q : ℕ) (h : HallIndex ι q)
    (x : HallIndex.Module (ι := ι) q) :
    tensorCoordinate b q h.head (h.pivot ::ₛ h.teeth)
        (representation b q (hallMap b q x)) = x h := by
  let lhs : HallIndex.Module (ι := ι) q →ₗ[ℤ] ℤ :=
    (tensorCoordinate b q h.head (h.pivot ::ₛ h.teeth)).comp
      ((representation b q).comp (hallMap b q))
  have hlhs : lhs = Finsupp.lapply h := by
    apply Finsupp.lhom_ext
    intro k z
    by_cases hhk : h = k
    · subst k
      simp [lhs, hallMap, separatingCoordinate]
    · simp [lhs, hallMap, separatingCoordinate, hhk, Ne.symm hhk]
  exact LinearMap.congr_fun hlhs x

/-- The standard Hall combs are linearly independent.  The proof is integral:
the alternating-boundary representation supplies an honest coefficient
functional for each Hall comb, so no passage to a field is involved. -/
theorem hallMap_injective (q : ℕ) : Function.Injective (hallMap b q) := by
  intro x y hxy
  ext h
  have hc := congrArg
    (fun z ↦ tensorCoordinate b q h.head (h.pivot ::ₛ h.teeth)
      (representation b q z)) hxy
  simpa only [coordinate_hallMap] using hc

/-- The explicit collector annihilates every Jacobi relation.  This is the
formal statement that the Hall collection is well-defined on the quotient. -/
theorem preNormalizer_jacobi (q : ℕ) (z : JacobiSource X (q + 1)) :
    preNormalizer (b := b) (q + 1) (jacobi X (q + 1) z) = 0 := by
  apply hallMap_injective b (q + 1)
  calc
    hallMap b (q + 1)
        (preNormalizer (b := b) (q + 1) (jacobi X (q + 1) z)) =
        (commutatorClass X q) (jacobi X (q + 1) z) :=
      LinearMap.congr_fun (hallMap_comp_preNormalizer_succ b q)
        (jacobi X (q + 1) z)
    _ = 0 := by
      change (LinearMap.range (jacobi X (q + 1))).mkQ
        (jacobi X (q + 1) z) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨z, rfl⟩
    _ = hallMap b (q + 1) 0 := (map_zero _).symm

/-- Every homogeneous metabelian component has a unique Hall expansion. -/
theorem hallMap_surjective (q : ℕ) : Function.Surjective (hallMap b q) := by
  cases q with
  | zero =>
      intro z
      refine ⟨componentTwoNormalizer b z, ?_⟩
      simpa using LinearMap.congr_fun
        (hallMap_comp_componentTwoNormalizer b) z
  | succ q =>
      intro z
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (jacobi X (q + 1))) z
      refine ⟨preNormalizer (b := b) (q + 1) w, ?_⟩
      exact LinearMap.congr_fun (hallMap_comp_preNormalizer_succ b q) w

/-- Coordinate equivalence realizing the manuscript's Hall normal form. -/
def hallEquiv (q : ℕ) :
    HallIndex.Module (ι := ι) q ≃ₗ[ℤ] Component X q :=
  LinearEquiv.ofBijective (hallMap b q)
    ⟨hallMap_injective b q, hallMap_surjective b q⟩

@[simp]
theorem hallEquiv_apply (q : ℕ) (x : HallIndex.Module (ι := ι) q) :
    hallEquiv b q x = hallMap b q x :=
  LinearEquiv.ofBijective_apply _ _

/-- The integral Hall basis in manuscript weight `q+2`. -/
def hallBasis (q : ℕ) : Module.Basis (HallIndex ι q) ℤ (Component X q) :=
  Finsupp.basisSingleOne.map (hallEquiv b q)

@[simp]
theorem hallBasis_apply (q : ℕ) (h : HallIndex ι q) :
    hallBasis b q h = hallVector b q h := by
  rw [hallBasis, Module.Basis.map_apply, hallEquiv_apply]
  exact hallMap_single b q h

/-- The least symmetric tooth in a positive-length Hall comb. -/
def HallIndex.nextTooth {q : ℕ} (h : HallIndex ι (q + 1)) : ι :=
  leastTooth h.teeth

/-- Delete the least symmetric tooth of a positive-length Hall comb. -/
def HallIndex.predecessor {q : ℕ} (h : HallIndex ι (q + 1)) :
    HallIndex ι q where
  head := h.head
  pivot := h.pivot
  teeth := eraseLeast h.teeth
  pivot_lt_head := h.pivot_lt_head
  pivot_le_teeth := fun i hi ↦ h.pivot_le_teeth i
    (mem_eraseLeast h.teeth hi)

/-- Removing the least symmetric tooth turns a Hall comb of weight `q+3`
into one of weight `q+2`; reattaching that tooth is exactly the homogeneous
right action.  This is the recursive bracket formula used in the universal
property. -/
theorem hallVector_succ_eq_action (q : ℕ) (h : HallIndex ι (q + 1)) :
    hallVector b (q + 1) h =
      Action.apply X q (b h.nextTooth) (hallVector b q h.predecessor) := by
  change hallVector b (q + 1) h =
      Action.apply X q (b (leastTooth h.teeth))
        (hallVector b q
          { head := h.head
            pivot := h.pivot
            teeth := eraseLeast h.teeth
            pivot_lt_head := h.pivot_lt_head
            pivot_le_teeth := fun i hi ↦ h.pivot_le_teeth i
              (mem_eraseLeast h.teeth hi) })
  cases q with
  | zero =>
      change (commutatorClass X 0)
          (wedge b h.head h.pivot ⊗ₜ[ℤ]
            SymmetricPower.monomialBasis b 1 h.teeth) =
        (commutatorClass X 0)
          (wedge b h.head h.pivot ⊗ₜ[ℤ]
            SymmetricPower.degreeOne (R := ℤ) (b (leastTooth h.teeth)))
      apply congrArg (commutatorClass X 0)
      apply congrArg (fun s ↦ wedge b h.head h.pivot ⊗ₜ[ℤ] s)
      let r : Sym ι 0 := eraseLeast h.teeth
      have hr : r = Sym.nil := Subsingleton.elim _ _
      have hc : leastTooth h.teeth ::ₛ r = h.teeth := cons_eraseLeast h.teeth
      have htooth : leastTooth (leastTooth h.teeth ::ₛ Sym.nil) =
          leastTooth h.teeth := by
        have hm := leastTooth_mem (leastTooth h.teeth ::ₛ Sym.nil)
        simpa using hm
      rw [← hc, hr, htooth]
      calc
        SymmetricPower.monomialBasis b 1
            (leastTooth h.teeth ::ₛ Sym.nil) =
            SymmetricPower.insert ℤ X 0 (b (leastTooth h.teeth))
              (SymmetricPower.monomialBasis b 0 Sym.nil) :=
          (SymmetricPower.insert_monomialBasis b 0
            (leastTooth h.teeth) Sym.nil).symm
        _ = SymmetricPower.degreeOne (R := ℤ) (b (leastTooth h.teeth)) := by
          have hempty : SymmetricPower.monomialBasis b 0 Sym.nil =
              SymmetricPower.tprod ℤ (fun i : Fin 0 => Fin.elim0 i) := by
            exact SymmetricPower.monomialBasis_zero_nil b
          rw [hempty, SymmetricPower.degreeOne_apply]
          rw [SymmetricPower.insert_tprod]
          apply congrArg (SymmetricPower.tprod ℤ)
          funext i
          fin_cases i
          rfl
  | succ q =>
      change (LinearMap.range (jacobi X (q + 2))).mkQ
          (wedge b h.head h.pivot ⊗ₜ[ℤ]
            SymmetricPower.monomialBasis b (q + 2) h.teeth) =
        (LinearMap.range (jacobi X (q + 2))).mkQ
          (Action.pre X (q + 1) (b (leastTooth h.teeth))
            (wedge b h.head h.pivot ⊗ₜ[ℤ]
              SymmetricPower.monomialBasis b (q + 1)
                (eraseLeast h.teeth)))
      rw [Action.pre_tmul, SymmetricPower.insert_monomialBasis,
        cons_eraseLeast]

/-- The unique coefficients of a homogeneous metabelian element. -/
def normalForm (q : ℕ) :
    Component X q →ₗ[ℤ] HallIndex.Module (ι := ι) q :=
  (hallEquiv b q).symm

@[simp]
theorem hallMap_normalForm (q : ℕ) (x : Component X q) :
    hallMap b q (normalForm b q x) = x := by
  change hallEquiv b q ((hallEquiv b q).symm x) = x
  exact (hallEquiv b q).apply_symm_apply x

@[simp]
theorem normalForm_hallMap (q : ℕ) (x : HallIndex.Module (ι := ι) q) :
    normalForm b q (hallMap b q x) = x := by
  change (hallEquiv b q).symm (hallEquiv b q x) = x
  exact (hallEquiv b q).symm_apply_apply x

end Based

end

end FreeMetabelian
