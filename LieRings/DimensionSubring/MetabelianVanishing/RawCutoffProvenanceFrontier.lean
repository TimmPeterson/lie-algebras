import LieRings.DimensionSubring.MetabelianVanishing.ProvenanceLedger
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffFullLabelCollector

/-!
# Contextual provenance frontier of the raw complete cutoff

This file feeds the actual top-marked cutoff occurrences into the
provenance-preserving collector.  It is deliberately an aggregate
construction: no terminal row above factor two is declared silent.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffProvenanceFrontierFintype : Fintype L :=
  Fintype.ofFinite L

/-- Add the empty contextual provenance to one adapted marked row.  Ordinary
rows do not occur in the raw cutoff input and are sent to zero. -/
def rawProvenancedPart :
    MarkedRow n L data hn → ProvenancedRow n L data hn →₀ ℤ
  | .ordinary _ => 0
  | .marked left rho mark right =>
      Finsupp.single (.marked rho .hole mark left right) 1

/-- The raw complete-cutoff occurrences, with their full relation and empty
initial bracket context retained. -/
def GoverningWitness.rawCutoffProvenancedInitial {a : L}
    (w : GoverningWitness n L data a) :
    ProvenancedRow n L data hn →₀ ℤ :=
  (w.rawCutoffFullLabelFrontier n L data hn).sum fun r z ↦
    z • rawProvenancedPart n L data hn r

/-- The raw provenance input consists only of marked whole-relation roots. -/
@[simp] theorem GoverningWitness.rawCutoffProvenancedInitial_component
    {a : L} (w : GoverningWitness n L data a)
    (root : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2))
    (left right : List (AdaptedIndex n L data hn)) :
    w.rawCutoffProvenancedInitial n L data hn
        (.component root context mark left right) = 0 := by
  classical
  rw [GoverningWitness.rawCutoffProvenancedInitial, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro r hr
  cases r <;> simp [rawProvenancedPart]

private theorem rawProvenancedPart_value_marked
    (left : List (AdaptedIndex n L data hn))
    (rho : Relations n L data) (mark : Fin (n + 2))
    (right : List (AdaptedIndex n L data hn)) :
    (provenancedCollector n L data hn).evaluate
        (rawProvenancedPart n L data hn
          (.marked left rho mark right)) =
      MarkedRow.value n L data hn (.marked left rho mark right) := by
  rw [rawProvenancedPart,
    LieRings.DegreeFive.FiniteTaggedCollector.evaluate_single, one_smul]
  change ProvenancedRow.value n L data hn
      (.marked rho .hole mark left right) = _
  rfl

/-- The full-label collector never discards the distinguished genuine
relation or changes its top mark. -/
private def FullLabelTopMarked : MarkedRow n L data hn → Prop
  | .ordinary _ => False
  | .marked _ _ mark _ => mark.val = n + 1

private theorem fullLabelExpansion_topMarked
    {r : MarkedRow n L data hn}
    {qs : List (ℤ × MarkedRow n L data hn)}
    (hexp : fullLabelExpansion n L data hn r = some qs)
    (hr : FullLabelTopMarked n L data hn r) :
    ∀ q ∈ qs, FullLabelTopMarked n L data hn q.2 := by
  classical
  intro q hq
  cases r with
  | ordinary word => simp [FullLabelTopMarked] at hr
  | marked left rho mark right =>
      simp only [fullLabelExpansion] at hexp
      split at hexp <;> try contradiction
      rename_i htop
      split at hexp
      · rename_i _ v rest
        rw [Option.some.injEq] at hexp
        subst qs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> exact htop
      · rename_i hright
        split at hexp <;> try contradiction
        rename_i hlarge
        split at hexp <;> try contradiction
        rename_i d hd
        rw [Option.some.injEq] at hexp
        subst qs
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact htop
        · rw [fullLabelOrdinaryCorrection, List.mem_map] at hq
          obtain ⟨p, hp, rfl⟩ := hq
          rfl

/-- Every supported marked row before full-label collection carries the top
mark.  This is a direct consequence of the literal PBW expansion in
`markedRowsAround`; no collector invariant is used here. -/
private theorem GoverningWitness.rawCompleteCutoffMarkedRows_mark_eq_top
    {a : L} (w : GoverningWitness n L data a)
    (left : List (AdaptedIndex n L data hn))
    (rho : Relations n L data) (mark : Fin (n + 2))
    (right : List (AdaptedIndex n L data hn))
    (hrow : w.rawCompleteCutoffMarkedRows n L data hn
      (.marked left rho mark right) ≠ 0) :
    mark.val = n + 1 := by
  classical
  by_contra hmark
  have hfin : (⟨n + 1, by omega⟩ : Fin (n + 2)) ≠ mark := by
    intro h
    apply hmark
    rw [← h]
  apply hrow
  rw [GoverningWitness.rawCompleteCutoffMarkedRows, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  cases q with
  | ordinary xs => simp [adaptedMarkedRowsOfQuotientWeightRow]
  | marked rootLeft rootRho rootMark rootRight =>
      change w.rawCompleteCutoffRows n L data
          (.marked rootLeft rootRho rootMark rootRight) *
        adaptedMarkedRowsOfQuotientWeightRow n L data hn
          (.marked rootLeft rootRho rootMark rootRight)
          (.marked left rho mark right) = 0
      apply mul_eq_zero_of_right
      simp [adaptedMarkedRowsOfQuotientWeightRow, markedRowsAround,
        Finsupp.sum_apply, Finsupp.single_apply, hfin]

private theorem GoverningWitness.rawCompleteCutoffMarkedRows_ordinary_eq_zero'
    {a : L} (w : GoverningWitness n L data a)
    (word : List (AdaptedIndex n L data hn)) :
    w.rawCompleteCutoffMarkedRows n L data hn (.ordinary word) = 0 := by
  classical
  rw [GoverningWitness.rawCompleteCutoffMarkedRows, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  cases q with
  | ordinary xs => simp [adaptedMarkedRowsOfQuotientWeightRow]
  | marked left rho mark right =>
      change w.rawCompleteCutoffRows n L data
          (.marked left rho mark right) *
        adaptedMarkedRowsOfQuotientWeightRow n L data hn
          (.marked left rho mark right) (.ordinary word) = 0
      apply mul_eq_zero_of_right
      simp [adaptedMarkedRowsOfQuotientWeightRow, markedRowsAround]

/-- There is no ordinary row in the adapted raw cutoff input.  This is an
aggregate statement about its coefficient, not a rowwise evaluation claim. -/
private theorem GoverningWitness.rawCutoffFullLabelFrontier_ordinary_eq_zero
    {a : L} (w : GoverningWitness n L data a)
    (word : List (AdaptedIndex n L data hn)) :
    w.rawCutoffFullLabelFrontier n L data hn (.ordinary word) = 0 := by
  classical
  rw [GoverningWitness.rawCutoffFullLabelFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro r hr
  change w.rawCompleteCutoffMarkedRows n L data hn r *
      (fullLabelCollector n L data hn).normalForm r (.ordinary word) = 0
  cases r with
  | ordinary rootWord =>
      rw [w.rawCompleteCutoffMarkedRows_ordinary_eq_zero'
        n L data hn rootWord]
      exact zero_mul _
  | marked left rho mark right =>
      by_cases hroot : w.rawCompleteCutoffMarkedRows n L data hn
          (.marked left rho mark right) = 0
      · rw [hroot, zero_mul]
      · apply mul_eq_zero_of_right
        by_contra hnormal
        have hmarked :=
          (fullLabelCollector n L data hn).invariant_of_normalForm_apply_ne_zero
            (FullLabelTopMarked n L data hn)
            (fullLabelExpansion_topMarked n L data hn)
            (p := .marked left rho mark right)
            (q := .ordinary word)
            (w.rawCompleteCutoffMarkedRows_mark_eq_top
              n L data hn left rho mark right hroot) hnormal
        exact hmarked

/-- Exact support shape of the full-label frontier.  The genuine relation is
at the right edge, still carries the top mark, and all ordinary factors to
its left are PBW ordered. -/
theorem GoverningWitness.rawCutoffFullLabelFrontier_shape_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (r : MarkedRow n L data hn)
    (hr : w.rawCutoffFullLabelFrontier n L data hn r ≠ 0) :
    match r with
    | .ordinary _ => False
    | .marked left _ mark right =>
        mark.val = n + 1 ∧ right = [] ∧ left.Pairwise (· ≤ ·) := by
  classical
  rw [GoverningWitness.rawCutoffFullLabelFrontier, Finsupp.sum_apply] at hr
  have hroot : ∃ root ∈
      (w.rawCompleteCutoffMarkedRows n L data hn).support,
      (w.rawCompleteCutoffMarkedRows n L data hn root •
        (fullLabelCollector n L data hn).normalForm root) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun root hroot ↦ hall root hroot))
  obtain ⟨root, hroot, hrootr⟩ := hroot
  have hrootCoeff : w.rawCompleteCutoffMarkedRows n L data hn root ≠ 0 :=
    Finsupp.mem_support_iff.mp hroot
  have hnormal :
      (fullLabelCollector n L data hn).normalForm root r ≠ 0 := by
    intro hzero
    simp [hzero] at hrootr
  have hrootTop : FullLabelTopMarked n L data hn root := by
    cases root with
    | ordinary word =>
        exact (hrootCoeff
          (w.rawCompleteCutoffMarkedRows_ordinary_eq_zero'
            n L data hn word)).elim
    | marked left rho mark right =>
        exact w.rawCompleteCutoffMarkedRows_mark_eq_top
          n L data hn left rho mark right hrootCoeff
  have htop :=
    (fullLabelCollector n L data hn).invariant_of_normalForm_apply_ne_zero
      (FullLabelTopMarked n L data hn)
      (fullLabelExpansion_topMarked n L data hn)
      hrootTop hnormal
  have hterminal : fullLabelExpansion n L data hn r = none :=
    (fullLabelCollector n L data hn).expansion_eq_none_of_mem_normalForm_support
      (Finsupp.mem_support_iff.mpr hnormal)
  cases r with
  | ordinary word => exact htop
  | marked left rho mark right =>
      have hmark : mark.val = n + 1 := htop
      have hright : right = [] := by
        cases right with
        | nil => rfl
        | cons v rest =>
            simp [fullLabelExpansion, hmark] at hterminal
      subst right
      refine ⟨hmark, rfl, ?_⟩
      by_cases hsmall : left.length + 1 ≤ 2
      · cases left with
        | nil => simp
        | cons x xs =>
            have hxs : xs = [] := by
              apply List.eq_nil_of_length_eq_zero
              simp only [List.length_cons] at hsmall
              omega
            subst xs
            simp
      · cases hchoose :
          LieRings.DegreeFive.chooseAdjacentInversion? left with
        | none =>
            exact
              (LieRings.DegreeFive.chooseAdjacentInversion?_eq_none_iff_pairwise
                left).mp hchoose
        | some d =>
            simp [fullLabelExpansion, hmark, hsmall, hchoose] at hterminal

/-- The primary contextual evaluation is the literal raw cutoff word. -/
theorem GoverningWitness.evaluate_rawCutoffProvenancedInitial {a : L}
    (w : GoverningWitness n L data a) :
    (provenancedCollector n L data hn).evaluate
        (w.rawCutoffProvenancedInitial n L data hn) =
      w.rawCompleteCutoffWord n L data := by
  classical
  rw [GoverningWitness.rawCutoffProvenancedInitial, map_finsuppSum]
  calc
    _ = markedRowEvaluation n L data hn
        (w.rawCutoffFullLabelFrontier n L data hn) := by
      apply Finsupp.sum_congr
      intro r hr
      cases r with
      | ordinary word =>
          exact (Finsupp.mem_support_iff.mp hr
            (w.rawCutoffFullLabelFrontier_ordinary_eq_zero
              n L data hn word)).elim
      | marked left rho mark right =>
          rw [map_zsmul, rawProvenancedPart_value_marked]
          rfl
    _ = _ := w.rawCutoffFullLabelFrontier_evaluation n L data hn

/-- Complete contextual normal form below the raw cutoff input. -/
def GoverningWitness.rawCutoffProvenancedFrontier {a : L}
    (w : GoverningWitness n L data a) :
    ProvenancedRow n L data hn →₀ ℤ :=
  (w.rawCutoffProvenancedInitial n L data hn).sum fun r z ↦
    z • (provenancedCollector n L data hn).normalForm r

/-- The contextual collector preserves the raw cutoff word exactly. -/
theorem GoverningWitness.evaluate_rawCutoffProvenancedFrontier {a : L}
    (w : GoverningWitness n L data a) :
    (provenancedCollector n L data hn).evaluate
        (w.rawCutoffProvenancedFrontier n L data hn) =
      w.rawCompleteCutoffWord n L data := by
  classical
  rw [GoverningWitness.rawCutoffProvenancedFrontier, map_finsuppSum]
  calc
    _ = (provenancedCollector n L data hn).evaluate
        (w.rawCutoffProvenancedInitial n L data hn) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul, provenancedCollector_evaluate]
      rfl
    _ = _ := w.evaluate_rawCutoffProvenancedInitial n L data hn

/-- Complete signed truncation-cell ledger below the raw cutoff input. -/
def GoverningWitness.rawCutoffFullProvenancedCells {a : L}
    (w : GoverningWitness n L data a) :
    ProvenancedCell n L data hn →₀ ℤ :=
  (w.rawCutoffProvenancedInitial n L data hn).sum fun r z ↦
    z • provenancedTrace n L data hn r

private theorem trace_top_hole_nil
    (rho : Relations n L data) :
    provenancedTrace n L data hn
      (.marked rho .hole ⟨n + 1, by omega⟩ [] []) = 0 := by
  have hwall : provenancedWall n L data hn (.hole)
      ⟨n + 1, by omega⟩ [] = true := by
    simp [provenancedWall, RelationContext.weight]
  rw [provenancedTrace_eq_of_expansion_none]
  · simp [provenancedCell?, hwall]
  · simp [provenancedExpansion, provenancedWall,
      RelationContext.weight]

private theorem trace_top_hole_singleton_apply_mark_one
    (rho : Relations n L data) (x : AdaptedIndex n L data hn)
    (c : ProvenancedCell n L data hn) (hcmark : c.mark.val = 1) :
    provenancedTrace n L data hn
      (.marked rho .hole ⟨n + 1, by omega⟩ [x] []) c = 0 := by
  let top : Fin (n + 2) := ⟨n + 1, by omega⟩
  let next : Fin (n + 2) := ⟨n, by omega⟩
  have htopNotWall :
      provenancedWall n L data hn (.hole) top [x] = false := by
    simp [provenancedWall, top, RelationContext.weight]
  have htopExpansion : provenancedExpansion n L data hn
      (.marked rho .hole top [x] []) =
        some [(1, .marked rho .hole next [x] []),
          (1, .component rho .hole top [x] [])] := by
    simp [provenancedExpansion, htopNotWall, top, next]
  have hnextExpansion : provenancedExpansion n L data hn
      (.marked rho .hole next [x] []) = none := by
    have hn0 : n ≠ 0 := by omega
    simp [provenancedExpansion, provenancedWall, next,
      RelationContext.weight, hn0]
  let cell : ProvenancedCell n L data hn :=
    ⟨rho, .hole, top, [x], by simp [top], htopNotWall⟩
  have hcell : provenancedCell? n L data hn
      (.marked rho .hole top [x] []) = some cell := by
    simp [provenancedCell?, cell, htopNotWall, top]
  rw [show (⟨n + 1, by omega⟩ : Fin (n + 2)) = top by rfl,
    provenancedTrace_eq_of_expansion_some _ _ _ _ _ _ htopExpansion]
  have hnext : provenancedTrace n L data hn
      (.marked rho .hole next [x] []) = 0 := by
    rw [provenancedTrace_eq_of_expansion_none _ _ _ _ _ hnextExpansion]
    simp [provenancedCell?, provenancedWall, next,
      RelationContext.weight]
  simp only [hnext, provenancedTrace_component_eq_zero, hcell,
    List.attach_cons, List.map_cons, List.sum_cons, List.attach_nil,
    List.map_nil, List.sum_nil, one_smul, add_zero,
    Finsupp.single_apply]
  by_cases hctop : cell = c
  · have hmarks := congrArg
        (fun d : ProvenancedCell n L data hn ↦ d.mark.val) hctop
    have hbad : n + 1 = 1 := by
      calc
        n + 1 = cell.mark.val := by rfl
        _ = c.mark.val := hmarks
        _ = 1 := hcmark
    omega
  · simp [hctop]

theorem provenancedTrace_marked_nil_cell_data
    (rho : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2))
    (left : List (AdaptedIndex n L data hn))
    (c : ProvenancedCell n L data hn)
    (hc : provenancedTrace n L data hn
      (.marked rho context mark left []) c ≠ 0) :
    c.root = rho ∧ c.context = context ∧ c.left = left := by
  classical
  let C := provenancedCollector n L data hn
  let P : ProvenancedRow n L data hn → Prop
    | .marked rho context mark left [] =>
        ∀ c, provenancedTrace n L data hn
          (.marked rho context mark left []) c ≠ 0 →
          c.root = rho ∧ c.context = context ∧ c.left = left
    | _ => True
  have hall : ∀ r, P r := by
    intro r
    induction r using C.wellFounded.induction with
    | h r ih =>
        cases r with
        | component => trivial
        | marked rho context mark left right =>
            cases right with
            | cons x right => trivial
            | nil =>
                change ∀ c, provenancedTrace n L data hn
                  (.marked rho context mark left []) c ≠ 0 →
                  c.root = rho ∧ c.context = context ∧ c.left = left
                intro c hc
                by_cases hk : mark.val = 0
                · have hexp : provenancedExpansion n L data hn
                      (.marked rho context mark left []) = some [] := by
                    simp [provenancedExpansion, hk]
                  rw [provenancedTrace_eq_of_expansion_some
                    n L data hn _ _ hexp] at hc
                  simp [provenancedCell?, hk] at hc
                · by_cases hw :
                      provenancedWall n L data hn context mark left = true
                  · have hexp : provenancedExpansion n L data hn
                        (.marked rho context mark left []) = none := by
                      simp [provenancedExpansion, hk, hw]
                    rw [provenancedTrace_eq_of_expansion_none
                      n L data hn _ hexp] at hc
                    simp [provenancedCell?, hk, hw] at hc
                  · have hwfalse :
                        provenancedWall n L data hn context mark left = false :=
                      Bool.eq_false_of_not_eq_true hw
                    have hmarkpos : 0 < mark.val := by omega
                    let next : Fin (n + 2) :=
                      ⟨mark.val - 1, by omega⟩
                    let r₁ : ProvenancedRow n L data hn :=
                      .marked rho context next left []
                    let r₂ : ProvenancedRow n L data hn :=
                      .component rho context mark left []
                    let d : ProvenancedCell n L data hn :=
                      ⟨rho, context, mark, left, hmarkpos, hwfalse⟩
                    have hexp : provenancedExpansion n L data hn
                        (.marked rho context mark left []) =
                          some [(1, r₁), (1, r₂)] := by
                      simp [provenancedExpansion, hk, hwfalse, r₁, r₂,
                        next]
                    have hcell : provenancedCell? n L data hn
                        (.marked rho context mark left []) = some d := by
                      simp only [provenancedCell?]
                      rw [dif_pos trivial, dif_pos hmarkpos, dif_pos hwfalse]
                    have hr₂zero : provenancedTrace n L data hn r₂ = 0 := by
                      simp [r₂, provenancedTrace_component_eq_zero]
                    rw [provenancedTrace_eq_of_expansion_some
                      n L data hn _ _ hexp] at hc
                    simp only [hcell, List.attach_cons, List.map_cons,
                      List.sum_cons, List.attach_nil, List.map_nil,
                      List.sum_nil, one_smul, add_zero, hr₂zero,
                      Finsupp.add_apply, Finsupp.single_apply] at hc
                    by_cases hdc : d = c
                    · subst c
                      exact ⟨rfl, rfl, rfl⟩
                    · have hchild : provenancedTrace n L data hn r₁ c ≠ 0 := by
                        simpa [hdc] using hc
                      have hexpC : C.expansion
                          (.marked rho context mark left []) =
                            some [(1, r₁), (1, r₂)] := hexp
                      have hir₁ := ih r₁
                        (C.decreases hexpC (1, r₁) (by simp))
                      change ∀ c, provenancedTrace n L data hn r₁ c ≠ 0 →
                        c.root = rho ∧ c.context = context ∧ c.left = left
                        at hir₁
                      exact hir₁ c hchild
  exact hall (.marked rho context mark left []) c hc

theorem GoverningWitness.rawCutoffProvenancedInitial_shape
    {a : L} (w : GoverningWitness n L data a)
    (r : ProvenancedRow n L data hn)
    (hr : w.rawCutoffProvenancedInitial n L data hn r ≠ 0) :
    ∃ (rho : Relations n L data)
      (left : List (AdaptedIndex n L data hn)),
      r = .marked rho .hole ⟨n + 1, by omega⟩ left [] := by
  classical
  rw [GoverningWitness.rawCutoffProvenancedInitial,
    Finsupp.sum_apply] at hr
  have hexists : ∃ s ∈
      (w.rawCutoffFullLabelFrontier n L data hn).support,
      (w.rawCutoffFullLabelFrontier n L data hn s •
        rawProvenancedPart n L data hn s) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun s hs ↦ hall s hs))
  obtain ⟨s, hs, hsr⟩ := hexists
  have hsne : w.rawCutoffFullLabelFrontier n L data hn s ≠ 0 :=
    Finsupp.mem_support_iff.mp hs
  cases s with
  | ordinary word => simp [rawProvenancedPart] at hsr
  | marked left rho mark right =>
      have hshape := w.rawCutoffFullLabelFrontier_shape_of_ne
        n L data hn (.marked left rho mark right) hsne
      rcases hshape with ⟨hmark, hright, hordered⟩
      have hre : r = .marked rho .hole mark left right := by
        by_contra hne
        simp [rawProvenancedPart, Finsupp.smul_apply,
          Finsupp.single_apply, hne] at hsr
      subst r
      subst right
      have hmarkTop : mark = ⟨n + 1, by omega⟩ := by
        apply Fin.ext
        exact hmark
      exact ⟨rho, left, by rw [hmarkTop]⟩

/-- Every truncation cell in the full-label raw trace retains the empty
initial relation context.  Component branches contain no later truncation
events, while the marked branch only lowers the mark. -/
theorem GoverningWitness.rawCutoffFullProvenancedCells_context_eq_hole
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0) :
    c.context = .hole := by
  classical
  rw [GoverningWitness.rawCutoffFullProvenancedCells,
    Finsupp.sum_apply] at hc
  have hexists : ∃ r ∈
      (w.rawCutoffProvenancedInitial n L data hn).support,
      (w.rawCutoffProvenancedInitial n L data hn r •
        provenancedTrace n L data hn r) c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc (Finset.sum_eq_zero (fun r hr ↦ hall r hr))
  obtain ⟨r, hr, hrc⟩ := hexists
  have hrne : w.rawCutoffProvenancedInitial n L data hn r ≠ 0 :=
    Finsupp.mem_support_iff.mp hr
  obtain ⟨rho, left, rfl⟩ :=
    w.rawCutoffProvenancedInitial_shape n L data hn r hrne
  have htrace : provenancedTrace n L data hn
      (.marked rho .hole ⟨n + 1, by omega⟩ left []) c ≠ 0 := by
    intro hzero
    simp [hzero] at hrc
  exact (provenancedTrace_marked_nil_cell_data
    n L data hn rho .hole ⟨n + 1, by omega⟩ left c htrace).2.1

/-- A mark-one cell in the complete full-label trace has at least two
ordinary factors on its left.  The two smaller cases stop at the two
contextual walls before mark one is reached. -/
theorem GoverningWitness.rawCutoffFullProvenancedCells_markOne_left_length
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0)
    (hmark : c.mark.val = 1) :
    2 ≤ c.left.length := by
  classical
  rw [GoverningWitness.rawCutoffFullProvenancedCells,
    Finsupp.sum_apply] at hc
  have hexists : ∃ r ∈
      (w.rawCutoffProvenancedInitial n L data hn).support,
      (w.rawCutoffProvenancedInitial n L data hn r •
        provenancedTrace n L data hn r) c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc (Finset.sum_eq_zero (fun r hr ↦ hall r hr))
  obtain ⟨r, hr, hrc⟩ := hexists
  have hrne : w.rawCutoffProvenancedInitial n L data hn r ≠ 0 :=
    Finsupp.mem_support_iff.mp hr
  obtain ⟨rho, left, rfl⟩ :=
    w.rawCutoffProvenancedInitial_shape n L data hn r hrne
  have htrace : provenancedTrace n L data hn
      (.marked rho .hole ⟨n + 1, by omega⟩ left []) c ≠ 0 := by
    intro hzero
    simp [hzero] at hrc
  have hdata := provenancedTrace_marked_nil_cell_data
    n L data hn rho .hole ⟨n + 1, by omega⟩ left c htrace
  have hleft : c.left = left := hdata.2.2
  rw [hleft]
  cases left with
  | nil =>
      have hz := congrArg
        (fun f : ProvenancedCell n L data hn →₀ ℤ ↦ f c)
        (trace_top_hole_nil n L data hn rho)
      exact (htrace hz).elim
  | cons x xs =>
      cases xs with
      | nil =>
          exact (htrace (trace_top_hole_singleton_apply_mark_one
            n L data hn rho x c hmark)).elim
      | cons y ys => simp

/-- Every supported raw provenance root has an ordered ordinary word.  This
is the precise support property needed to normalize all of its component
cells; it follows from the full-label frontier theorem and does not inspect
the subsequent trace. -/
theorem GoverningWitness.rawCutoffProvenancedInitial_neighbors_pairwise
    {a : L} (w : GoverningWitness n L data a)
    (r : ProvenancedRow n L data hn)
    (hr : w.rawCutoffProvenancedInitial n L data hn r ≠ 0) :
    match r with
    | .marked _ _ _ left right =>
        (left ++ right).Pairwise (· ≤ ·)
    | .component _ _ _ left right =>
        (left ++ right).Pairwise (· ≤ ·) := by
  classical
  rw [GoverningWitness.rawCutoffProvenancedInitial, Finsupp.sum_apply] at hr
  have hexists : ∃ s ∈
      (w.rawCutoffFullLabelFrontier n L data hn).support,
      (w.rawCutoffFullLabelFrontier n L data hn s •
        rawProvenancedPart n L data hn s) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun s hs ↦ hall s hs))
  obtain ⟨s, hs, hsr⟩ := hexists
  have hsne : w.rawCutoffFullLabelFrontier n L data hn s ≠ 0 :=
    Finsupp.mem_support_iff.mp hs
  cases s with
  | ordinary word => simp [rawProvenancedPart] at hsr
  | marked left rho mark right =>
      have hshape := w.rawCutoffFullLabelFrontier_shape_of_ne
        n L data hn (.marked left rho mark right) hsne
      rcases hshape with ⟨hmark, hright, hleft⟩
      have hre : r = .marked rho .hole mark left right := by
        by_contra hne
        simp [rawProvenancedPart, Finsupp.smul_apply,
          Finsupp.single_apply, hne] at hsr
      subst r
      subst right
      simpa using hleft

/-- Every supported cell of the complete raw cutoff ledger has an ordered
ordinary left word.  This aggregate theorem is what the component PBW
normalizer consumes. -/
theorem GoverningWitness.rawCutoffFullProvenancedCells_left_pairwise
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0) :
    c.left.Pairwise (· ≤ ·) := by
  classical
  rw [GoverningWitness.rawCutoffFullProvenancedCells,
    Finsupp.sum_apply] at hc
  have hexists : ∃ r ∈
      (w.rawCutoffProvenancedInitial n L data hn).support,
      (w.rawCutoffProvenancedInitial n L data hn r •
        provenancedTrace n L data hn r) c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc (Finset.sum_eq_zero (fun r hr ↦ hall r hr))
  obtain ⟨r, hr, hrc⟩ := hexists
  have hrne : w.rawCutoffProvenancedInitial n L data hn r ≠ 0 :=
    Finsupp.mem_support_iff.mp hr
  have htrace : provenancedTrace n L data hn r c ≠ 0 := by
    intro hzero
    simp [hzero] at hrc
  cases r with
  | marked root context mark left right =>
      exact provenancedTrace_cell_left_pairwise_of_append n L data hn
        (.marked root context mark left right)
        (w.rawCutoffProvenancedInitial_neighbors_pairwise n L data hn
          (.marked root context mark left right) hrne) c htrace
  | component root context mark left right =>
      exact provenancedTrace_cell_left_pairwise_of_append n L data hn
        (.component root context mark left right)
        (w.rawCutoffProvenancedInitial_neighbors_pairwise n L data hn
          (.component root context mark left right) hrne) c htrace

/-- Whole one-factor contextual walls in the raw provenance frontier. -/
def GoverningWitness.rawCutoffProvenancedTerminalOne {a : L}
    (w : GoverningWitness n L data a) :
    ProvenancedTerminalOne n L data hn →₀ ℤ :=
  (w.rawCutoffProvenancedFrontier n L data hn).sum fun r z ↦
    z • provenancedTerminalOnePart n L data hn r

/-- Placed factor-two contextual walls in the raw provenance frontier. -/
def GoverningWitness.rawCutoffProvenancedTerminalTwo {a : L}
    (w : GoverningWitness n L data a) :
    ProvenancedTerminalTwo n L data hn →₀ ℤ :=
  (w.rawCutoffProvenancedFrontier n L data hn).sum fun r z ↦
    z • provenancedTerminalTwoPart n L data hn r

/-- Genuine terminal-source chain read from the placed factor-two walls. -/
def GoverningWitness.rawCutoffContextualTerminalChain {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (w.rawCutoffProvenancedTerminalTwo n L data hn).sum fun c z ↦
    z • c.chain n L data hn

/-- Boundary read of the raw contextual terminal chain. -/
@[simp] theorem GoverningWitness.dOne_rawCutoffContextualTerminalChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffContextualTerminalChain n L data hn) =
      (w.rawCutoffProvenancedTerminalTwo n L data hn).sum
        (fun c z ↦ z • rightSymbol n L data hn 2 n (by omega)
          c.row.value) := by
  classical
  rw [GoverningWitness.rawCutoffContextualTerminalChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, ProvenancedTerminalTwo.dOne_chain]
  rfl

end

end LieRings.MetabelianVanishing
