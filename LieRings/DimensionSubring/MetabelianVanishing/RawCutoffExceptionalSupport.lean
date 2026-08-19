import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffHoleTailCorrection
import LieRings.DimensionSubring.MetabelianVanishing.RelationSubsetTailCorrection

/-!
# Exact support of the exceptional raw hole cells

The full-label continuation can create new relation labels only by bracketing
a genuine full relation.  Such a bracket is already in the derived tail.
Consequently a raw truncation cell whose root is not in that tail must retain
one of the original zero-based-weight-zero triangular relations.

This file also records the only word-shape dichotomy used by the exceptional
primitive calculation.  It deliberately makes no homogeneity or
relation-membership claim about an exposed component.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalSupportFintype : Fintype L :=
  Fintype.ofFinite L

/-! ## Relation-label provenance -/

private theorem fullLabelExpansion_preserves_rawCutoffMarkedRelationShape
    {r : MarkedRow n L data hn}
    {rows : List (ℤ × MarkedRow n L data hn)}
    (hexp : fullLabelExpansion n L data hn r = some rows)
    (hr : RawCutoffMarkedRelationShape n L data hn r) :
    ∀ q ∈ rows, RawCutoffMarkedRelationShape n L data hn q.2 := by
  classical
  intro q hq
  cases r with
  | ordinary word => simp [fullLabelExpansion] at hexp
  | marked left rho mark right =>
      simp only [RawCutoffMarkedRelationShape] at hr
      simp only [fullLabelExpansion] at hexp
      split at hexp <;> try contradiction
      rename_i htop
      split at hexp
      · rename_i _ v rest
        rw [Option.some.injEq] at hexp
        subst rows
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hr
        · exact Or.inl
            (relationRightBracket_mem_tail_one_unconditionally
              n L data hn rho v)
      · rename_i hright
        split at hexp <;> try contradiction
        rename_i hlarge
        split at hexp <;> try contradiction
        rename_i d hd
        rw [Option.some.injEq] at hexp
        subst rows
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hr
        · rw [fullLabelOrdinaryCorrection, List.mem_map] at hq
          obtain ⟨p, hp, rfl⟩ := hq
          exact hr

/-- Relation provenance survives the full-label PBW continuation. -/
theorem GoverningWitness.rawCutoffFullLabelFrontier_relationShape_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (r : MarkedRow n L data hn)
    (hr : w.rawCutoffFullLabelFrontier n L data hn r ≠ 0) :
    RawCutoffMarkedRelationShape n L data hn r := by
  classical
  rw [GoverningWitness.rawCutoffFullLabelFrontier,
    Finsupp.sum_apply] at hr
  have hexists : ∃ root ∈
      (w.rawCompleteCutoffMarkedRows n L data hn).support,
      (w.rawCompleteCutoffMarkedRows n L data hn root •
        (fullLabelCollector n L data hn).normalForm root) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun root hroot ↦ hall root hroot))
  obtain ⟨root, hroot, hrootr⟩ := hexists
  have hrootCoeff : w.rawCompleteCutoffMarkedRows n L data hn root ≠ 0 :=
    Finsupp.mem_support_iff.mp hroot
  have hnormal :
      (fullLabelCollector n L data hn).normalForm root r ≠ 0 := by
    intro hzero
    simp [hzero] at hrootr
  exact
    (fullLabelCollector n L data hn).invariant_of_normalForm_apply_ne_zero
      (RawCutoffMarkedRelationShape n L data hn)
      (fullLabelExpansion_preserves_rawCutoffMarkedRelationShape
        n L data hn)
      (w.rawCompleteCutoffMarkedRows_relationShape_of_ne
        n L data hn root hrootCoeff)
      hnormal

/-- Every supported provenance input retains the raw-cutoff relation-shape
alternative for its genuine full root. -/
theorem GoverningWitness.rawCutoffProvenancedInitial_relationShape_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (r : ProvenancedRow n L data hn)
    (hr : w.rawCutoffProvenancedInitial n L data hn r ≠ 0) :
    match r with
    | .marked root _ _ _ _ => RawCutoffRelationShape n L data root
    | .component root _ _ _ _ => RawCutoffRelationShape n L data root := by
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
  have hshape := w.rawCutoffFullLabelFrontier_relationShape_of_ne
    n L data hn s hsne
  cases s with
  | ordinary word => simp [rawProvenancedPart] at hsr
  | marked left rho mark right =>
      have hre : r = .marked rho .hole mark left right := by
        by_contra hne
        simp [rawProvenancedPart, Finsupp.smul_apply,
          Finsupp.single_apply, hne] at hsr
      subst r
      simpa [RawCutoffMarkedRelationShape] using hshape

/-- Every supported truncation cell has exactly the inherited raw-cutoff
relation-shape alternative. -/
theorem GoverningWitness.rawCutoffFullProvenancedCells_relationShape_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0) :
    RawCutoffRelationShape n L data c.root := by
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
  have hroot := (provenancedTrace_marked_nil_cell_data
    n L data hn rho .hole ⟨n + 1, by omega⟩ left c htrace).1
  have hshape := w.rawCutoffProvenancedInitial_relationShape_of_ne
    n L data hn
      (.marked rho .hole ⟨n + 1, by omega⟩ left []) hrne
  simpa [hroot] using hshape

/-! ## The exceptional root and its ordinary word -/

/-- A supported mark-one hole cell outside the derived tail is necessarily
one of the original triangular relations with zero-based weight zero. -/
theorem GoverningWitness.rawCutoffHoleExceptional_root
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0)
    (hexceptional : c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) :
    ∃ tag : TriangularRelationIndex n L,
      tag.1.val = 0 ∧
        c.root = triangularRelationOfIndex n L data tag := by
  rcases w.rawCutoffFullProvenancedCells_relationShape_of_ne
      n L data hn c hc with htail | htriangular
  · exact (hexceptional.2.2 htail).elim
  · exact htriangular

private theorem adaptedWeightSum_eq_length_of_val_eq_zero
    (xs : List (AdaptedIndex n L data hn))
    (hzero : ∀ i ∈ xs, i.1.val = 0) :
    (xs.map (adaptedWeightedBasis n L data hn).weight).sum = xs.length := by
  revert hzero
  induction xs with
  | nil => simp
  | cons i xs ih =>
      intro hzero
      have hi : i.1.val = 0 := hzero i (by simp)
      have hxs : ∀ j ∈ xs, j.1.val = 0 := by
        intro j hj
        exact hzero j (List.mem_cons_of_mem i hj)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih hxs]
      simp [adaptedWeightedBasis, hi]
      omega

private theorem adaptedWeightSum_length_lt_of_exists_val_pos
    (xs : List (AdaptedIndex n L data hn))
    (hpos : ∃ i ∈ xs, 0 < i.1.val) :
    xs.length <
      (xs.map (adaptedWeightedBasis n L data hn).weight).sum := by
  let B := adaptedWeightedBasis n L data hn
  have length_le_weight_sum (ys : List (AdaptedIndex n L data hn)) :
      ys.length ≤ (ys.map B.weight).sum := by
    simpa only [List.length_map] using
      (List.length_le_sum_of_one_le (ys.map B.weight) (by
        intro k hk
        rw [List.mem_map] at hk
        obtain ⟨j, hj, rfl⟩ := hk
        exact B.weight_pos j))
  induction xs with
  | nil => simp at hpos
  | cons j xs ih =>
      obtain ⟨i, hi, hiPos⟩ := hpos
      simp only [List.mem_cons] at hi
      rcases hi with hij | hi
      · subst i
        have htail := length_le_weight_sum xs
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        change xs.length + 1 <
          (j.1.val + 1) + (xs.map B.weight).sum
        omega
      · have htail := ih ⟨i, hi, hiPos⟩
        have hj : 1 ≤
            (adaptedWeightedBasis n L data hn).weight j :=
          (adaptedWeightedBasis n L data hn).weight_pos j
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega

/-- The ordered spectator word of an exceptional cell is either entirely
weight one (zero-based index weight zero), or its manuscript total weight is
strictly larger than its factor length.  These are the two primitive cases;
no stronger total-weight equality follows from support alone. -/
theorem GoverningWitness.rawCutoffHoleExceptional_left_cases
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0)
    (hexceptional : c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) :
    c.left.Pairwise (· ≤ ·) ∧ 2 ≤ c.left.length ∧
      (((∀ i ∈ c.left, i.1.val = 0) ∧
          (c.left.map (adaptedWeightedBasis n L data hn).weight).sum =
            c.left.length) ∨
        ((∃ i ∈ c.left, 0 < i.1.val) ∧
          c.left.length <
            (c.left.map
              (adaptedWeightedBasis n L data hn).weight).sum)) := by
  refine ⟨w.rawCutoffFullProvenancedCells_left_pairwise
      n L data hn c hc,
    w.rawCutoffFullProvenancedCells_markOne_left_length
      n L data hn c hc hexceptional.1, ?_⟩
  by_cases hall : ∀ i ∈ c.left, i.1.val = 0
  · left
    exact ⟨hall, adaptedWeightSum_eq_length_of_val_eq_zero
      n L data hn c.left hall⟩
  · right
    push Not at hall
    obtain ⟨i, hi, hi0⟩ := hall
    have hiPos : 0 < i.1.val := by omega
    exact ⟨⟨i, hi, hiPos⟩,
      adaptedWeightSum_length_lt_of_exists_val_pos
        n L data hn c.left ⟨i, hi, hiPos⟩⟩

/-! ## Exact provenance at the one-factor PBW wall -/

/-- If an all-weight-one source word of length `n` reaches a one-factor PBW
leaf, every ordinary factor has necessarily been absorbed into its bracket
context.  The context therefore has manuscript weight exactly `n`; root and
active mark are unchanged. -/
theorem ProvenancedCell.componentPBWFrontier_factorOne_all_weight_one
    (c : ProvenancedCell n L data hn)
    (hcontext : c.context = .hole)
    (hall : ∀ i ∈ c.left, i.1.val = 0)
    (hlen : c.left.length = n)
    (q : ComponentPBWState n L data hn)
    (hq : c.componentPBWFrontier n L data hn q ≠ 0)
    (hone : q.factorCount n L data hn = 1) :
    q.root = c.root ∧ q.mark = c.mark ∧ q.left = [] ∧ q.right = [] ∧
      RelationContext.weight n L data hn q.context = n := by
  have hprov := c.componentPBWFrontier_provenance_weight
    n L data hn q hq
  have hleftLength : q.left.length = 0 := by
    simp only [ComponentPBWState.factorCount] at hone
    omega
  have hrightLength : q.right.length = 0 := by
    simp only [ComponentPBWState.factorCount] at hone
    omega
  have hleft : q.left = [] := List.length_eq_zero_iff.mp hleftLength
  have hright : q.right = [] := List.length_eq_zero_iff.mp hrightLength
  have hsourceWeight := adaptedWeightSum_eq_length_of_val_eq_zero
    n L data hn c.left hall
  have hcontextWeight :
      RelationContext.weight n L data hn q.context = n := by
    have hmass := hprov.2.2.1
    simp [hleft, hright, hcontext, RelationContext.weight,
      hsourceWeight, hlen] at hmass
    exact hmass
  exact ⟨hprov.1, hprov.2.1, hleft, hright, hcontextWeight⟩

/-- Specialization of the preceding collector invariant to an exceptional
raw cutoff cell.  This is the exact support statement consumed by the
terminal triangular-comb calculation. -/
theorem GoverningWitness.rawCutoffHoleExceptional_factorOne_shape
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0)
    (hexceptional : c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1)
    (hall : ∀ i ∈ c.left, i.1.val = 0)
    (hlen : c.left.length = n)
    (q : ComponentPBWState n L data hn)
    (hq : c.componentPBWFrontier n L data hn q ≠ 0)
    (hone : q.factorCount n L data hn = 1) :
    ∃ tag : TriangularRelationIndex n L,
      tag.1.val = 0 ∧
        q.root = triangularRelationOfIndex n L data tag ∧
        q.mark.val = 1 ∧ q.left = [] ∧ q.right = [] ∧
        RelationContext.weight n L data hn q.context = n := by
  obtain ⟨tag, htag, hroot⟩ :=
    w.rawCutoffHoleExceptional_root n L data hn c hc hexceptional
  have hshape := c.componentPBWFrontier_factorOne_all_weight_one
    n L data hn hexceptional.2.1 hall hlen q hq hone
  refine ⟨tag, htag, ?_, ?_, hshape.2.2.1, hshape.2.2.2.1,
    hshape.2.2.2.2⟩
  · exact hshape.1.trans hroot
  · rw [hshape.2.1, hexceptional.1]

end

end LieRings.MetabelianVanishing
