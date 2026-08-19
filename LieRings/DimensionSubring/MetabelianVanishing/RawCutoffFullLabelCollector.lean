import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffMarkedRows

/-!
# Full-label PBW continuation of the raw cutoff

This collector never replaces a homogeneous component by a relation.  It
starts with the top-marked, genuine full-relation rows of the raw cutoff,
moves the full relation to the right, and then orders the ordinary factors.
Every factor-lowering child still contains the same genuine full relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffFullLabelFintype : Fintype L := Fintype.ofFinite L

/-- Bracket children of an ordinary adjacent interchange, with the genuine
full relation retained on the right. -/
def fullLabelOrdinaryCorrection
    (left right : List (AdaptedIndex n L data hn))
    (x y : AdaptedIndex n L data hn) (rho : Relations n L data) :
    List (ℤ × MarkedRow n L data hn) :=
  (adaptedCoordinates n L data hn
      ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn y⁆).map
    (fun q ↦ (q.1, .marked (left ++ q.2 :: right) rho
      ⟨n + 1, by omega⟩ []))

/-- The full-label continuation.  Transfer across the marked relation is
performed first.  Once the relation is at the right edge, ordinary adjacent
inversions are collected. -/
noncomputable def fullLabelExpansion : MarkedRow n L data hn →
    Option (List (ℤ × MarkedRow n L data hn))
  | .ordinary _ => none
  | .marked left rho k right =>
      if htop : k.val = n + 1 then
        match right with
        | v :: rest => some
            [(1, .marked (left ++ [v]) rho k rest),
             (1, .marked left
               (relationRightBracket n L data hn rho v) k rest)]
        | [] =>
            if hsmall : left.length + 1 ≤ 2 then none
            else
              match LieRings.DegreeFive.chooseAdjacentInversion? left with
              | none => none
              | some d => some
                  ((1, .marked (d.left ++ d.y :: d.x :: d.right) rho k []) ::
                    fullLabelOrdinaryCorrection n L data hn
                      d.left d.right d.x d.y rho)
      else none

/-- Termination measure: displayed factor number, unresolved factors to the
right of the relation, and ordinary PBW inversions. -/
def fullLabelMeasure : MarkedRow n L data hn → RowMeasure
  | .ordinary xs => (xs.length, 0, rowInversionCount n L data hn xs)
  | .marked left _ _ right =>
      (left.length + right.length + 1, right.length,
        rowInversionCount n L data hn left)

theorem fullLabelExpansion_decreases
    {r : MarkedRow n L data hn}
    {qs : List (ℤ × MarkedRow n L data hn)}
    (h : fullLabelExpansion n L data hn r = some qs) :
    ∀ q ∈ qs, rowMeasureLt (fullLabelMeasure n L data hn q.2)
      (fullLabelMeasure n L data hn r) := by
  classical
  intro q hq
  cases r with
  | ordinary xs => simp [fullLabelExpansion] at h
  | marked left rho k right =>
      simp only [fullLabelExpansion] at h
      split at h <;> try contradiction
      rename_i htop
      split at h
      · rename_i _ v rest
        rw [Option.some.injEq] at h
        subst qs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · unfold rowMeasureLt
          simp only [fullLabelMeasure, List.length_append,
            List.length_singleton, List.length_cons, List.length_nil]
          have hfactor :
              left.length + (0 + 1) + rest.length + 1 =
                left.length + (rest.length + 1) + 1 := by
            omega
          rw [hfactor]
          apply Prod.Lex.right
          apply Prod.Lex.left
          omega
        · unfold rowMeasureLt
          apply Prod.Lex.left
          simp [fullLabelMeasure]
      · rename_i hright
        split at h <;> try contradiction
        rename_i hlarge
        split at h <;> try contradiction
        rename_i d hd
        rw [Option.some.injEq] at h
        subst qs
        obtain ⟨hleft, hyx⟩ :=
          LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · rw [hleft]
          unfold rowMeasureLt
          simp only [fullLabelMeasure, List.length_append, List.length_cons,
            List.length_nil]
          apply Prod.Lex.right
          apply Prod.Lex.right
          have hinv := rowInversionCount_swap n L data hn
            d.left d.right d.x d.y hyx
          omega
        · rw [fullLabelOrdinaryCorrection, List.mem_map] at hq
          obtain ⟨p, hp, rfl⟩ := hq
          rw [hleft]
          unfold rowMeasureLt
          apply Prod.Lex.left
          simp [fullLabelMeasure]

private theorem fullLabelOrdinaryCorrection_value
    (left right : List (AdaptedIndex n L data hn))
    (x y : AdaptedIndex n L data hn) (rho : Relations n L data) :
    ((fullLabelOrdinaryCorrection n L data hn left right x y rho).map
      (fun q ↦ q.1 • q.2.value)).sum =
      (MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn y⁆ *
          MarkedRow.basisWord n L data hn right) *
        UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) := by
  classical
  let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    { toFun := fun z ↦
        (MarkedRow.basisWord n L data hn left *
            UniversalEnvelopingAlgebra.ι ℤ z *
            MarkedRow.basisWord n L data hn right) *
          UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L)
      map_add' := by
        intro z w
        rw [map_add, mul_add, add_mul]
        noncomm_ring
      map_smul' := by
        intro z w
        rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
        noncomm_ring }
  have hc := congrArg context (adaptedCoordinates_sum n L data hn
    ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn y⁆)
  rw [map_list_sum] at hc
  calc
    _ = ((adaptedCoordinates n L data hn
          ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn y⁆).map
        (fun q ↦ context (q.1 • adaptedBasis n L data hn q.2))).sum := by
      unfold fullLabelOrdinaryCorrection
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      rcases q with ⟨z, i⟩
      rw [map_zsmul]
      simp [context, MarkedRow.value, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.word, List.map_append,
        adaptedWeightedBasis]
      noncomm_ring
    _ = context ⁅adaptedBasis n L data hn x,
          adaptedBasis n L data hn y⁆ := by
      simpa only [List.map_map, Function.comp_apply] using hc
    _ = _ := rfl

theorem fullLabelExpansion_preserves
    {r : MarkedRow n L data hn}
    {qs : List (ℤ × MarkedRow n L data hn)}
    (h : fullLabelExpansion n L data hn r = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value).sum = r.value := by
  classical
  cases r with
  | ordinary xs => simp [fullLabelExpansion] at h
  | marked left rho k right =>
      simp only [fullLabelExpansion] at h
      split at h <;> try contradiction
      rename_i htop
      have hk : k = ⟨n + 1, by omega⟩ := Fin.ext htop
      split at h
      · rename_i _ v rest
        rw [Option.some.injEq] at h
        subst qs
        simp only [List.map_cons, List.map_singleton, List.sum_cons,
          List.sum_singleton, List.map_nil, List.sum_nil, add_zero, one_smul]
        rw [hk]
        exact (markedTransferRightTop n L data hn left rest rho v).symm
      · rename_i hright
        split at h <;> try contradiction
        rename_i hlarge
        split at h <;> try contradiction
        rename_i d hd
        rw [Option.some.injEq] at h
        subst qs
        obtain ⟨hleft, hyx⟩ :=
          LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
        rw [hk]
        rw [List.map_cons, List.sum_cons, one_smul,
          fullLabelOrdinaryCorrection_value]
        rw [show (MarkedRow.marked left rho ⟨n + 1, by omega⟩ [] :
            MarkedRow n L data hn).value =
            MarkedRow.basisWord n L data hn left *
              UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) by
          simp [MarkedRow.value, rowTruncation_top,
            MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word]]
        rw [hleft]
        have hord := ordinaryTransfer n L data hn
          d.left d.right d.x d.y
        have hord' :
            MarkedRow.basisWord n L data hn
                (d.left ++ d.x :: d.y :: d.right) =
              MarkedRow.basisWord n L data hn
                  (d.left ++ d.y :: d.x :: d.right) +
                MarkedRow.basisWord n L data hn d.left *
                    UniversalEnvelopingAlgebra.ι ℤ
                      ⁅adaptedBasis n L data hn d.x,
                        adaptedBasis n L data hn d.y⁆ *
                    MarkedRow.basisWord n L data hn d.right := by
          simpa only [adaptedWeightedBasis] using hord
        have hnil : MarkedRow.basisWord n L data hn [] = 1 := by
          simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word]
        simp only [MarkedRow.value, rowTruncation_top, hnil, mul_one]
        calc
          MarkedRow.basisWord n L data hn
                  (d.left ++ d.y :: d.x :: d.right) *
                UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) +
              (MarkedRow.basisWord n L data hn d.left *
                    UniversalEnvelopingAlgebra.ι ℤ
                      ⁅adaptedBasis n L data hn d.x,
                        adaptedBasis n L data hn d.y⁆ *
                    MarkedRow.basisWord n L data hn d.right) *
                UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) =
              (MarkedRow.basisWord n L data hn
                    (d.left ++ d.y :: d.x :: d.right) +
                MarkedRow.basisWord n L data hn d.left *
                    UniversalEnvelopingAlgebra.ι ℤ
                      ⁅adaptedBasis n L data hn d.x,
                        adaptedBasis n L data hn d.y⁆ *
                    MarkedRow.basisWord n L data hn d.right) *
                UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) := by
                  rw [add_mul]
          _ = MarkedRow.basisWord n L data hn
                  (d.left ++ d.x :: d.y :: d.right) *
                UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) := by
                  rw [← hord']

/-- The deterministic full-label collector. -/
def fullLabelCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (MarkedRow n L data hn) (UEA ℤ (FreeModel n L)) :=
  deterministicCollector n L data hn
    (fullLabelMeasure n L data hn)
    (fullLabelExpansion n L data hn)
    (fullLabelExpansion_decreases n L data hn)
    (fullLabelExpansion_preserves n L data hn)

/-- Complete full-label continuation of the raw cutoff occurrence family. -/
def GoverningWitness.rawCutoffFullLabelFrontier {a : L}
    (w : GoverningWitness n L data a) : MarkedRow n L data hn →₀ ℤ :=
  (w.rawCompleteCutoffMarkedRows n L data hn).sum fun r z ↦
    z • (fullLabelCollector n L data hn).normalForm r

/-- The full-label continuation evaluates to the exact raw cutoff word. -/
theorem GoverningWitness.rawCutoffFullLabelFrontier_evaluation {a : L}
    (w : GoverningWitness n L data a) :
    markedRowEvaluation n L data hn
        (w.rawCutoffFullLabelFrontier n L data hn) =
      w.rawCompleteCutoffWord n L data := by
  classical
  rw [GoverningWitness.rawCutoffFullLabelFrontier, map_finsuppSum]
  calc
    _ = markedRowEvaluation n L data hn
        (w.rawCompleteCutoffMarkedRows n L data hn) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul]
      change (w.rawCompleteCutoffMarkedRows n L data hn r) •
          (fullLabelCollector n L data hn).evaluate
            ((fullLabelCollector n L data hn).normalForm r) =
        (w.rawCompleteCutoffMarkedRows n L data hn r) • r.value
      rw [(fullLabelCollector n L data hn).evaluate_normalForm]
      rfl
    _ = _ := w.rawCompleteCutoffMarkedRows_evaluation n L data hn

end

end LieRings.MetabelianVanishing
