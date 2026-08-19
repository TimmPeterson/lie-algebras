import LieRings.DimensionSubring.MetabelianVanishing.RelativeRows
import LieRings.DimensionSubring.DegreeFive.PacketCollector

/-!
# Full-relation marked rows and their exact ledger

A mark always stores a genuine member of Relations. Its natural-number index
affects only evaluation through the grading truncation. The finite ledger is
independent of confluence: a fixed list of replacements telescopes exactly.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance markedCollectorFintype : Fintype L := Fintype.ofFinite L

/-- Evaluation of the first k manuscript weights, extended by zero back into
the same free model. -/
def rowTruncation (k : ℕ) (hk : k ≤ n + 1) :
    FreeModel n L →ₗ[ℤ] FreeModel n L :=
  (FreeMetabelian.Free.prefixIncl k hk).comp
    (FreeMetabelian.Free.projectPrefix k hk)

@[simp] theorem rowTruncation_zero (x : FreeModel n L) :
    rowTruncation n L 0 (by omega) x = 0 := by
  funext i
  simp [rowTruncation, FreeMetabelian.Free.prefixIncl_apply_of_le]

@[simp] theorem rowTruncation_top (x : FreeModel n L) :
    rowTruncation n L (n + 1) le_rfl x = x := by
  funext i
  simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
    FreeMetabelian.Free.projectPrefix] <;> omega

/-- The active-weight edge. The last summand is a homogeneous coordinate,
not an element of Relations. -/
theorem rowTruncation_succ (k : ℕ) (hk : k < n + 1)
    (x : FreeModel n L) :
    rowTruncation n L (k + 1) (by omega) x =
      rowTruncation n L k (by omega) x +
        FreeMetabelian.Free.weightIncl k hk
          (FreeMetabelian.Free.weightProject k hk x) := by
  funext i
  by_cases hik : i.val < k
  · simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
      FreeMetabelian.Free.projectPrefix, FreeMetabelian.Free.weightIncl,
      FreeMetabelian.Free.weightProject, FreeMetabelian.Free.incl, hik,
      show i.val < k + 1 by omega,
      show i ≠ (⟨k, hk⟩ : Fin (n + 1)) by
        intro h; have := congrArg Fin.val h; simp only at this; omega] <;>
      omega
  · by_cases hieq : i.val = k
    · have hi : i = ⟨k, hk⟩ := Fin.ext hieq
      subst i
      simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
        FreeMetabelian.Free.projectPrefix, FreeMetabelian.Free.weightIncl,
        FreeMetabelian.Free.weightProject, FreeMetabelian.Free.incl,
        FreeMetabelian.Free.project] <;> rfl
    · have hki : k < i.val := by omega
      simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
        FreeMetabelian.Free.projectPrefix, FreeMetabelian.Free.weightIncl,
        FreeMetabelian.Free.weightProject, FreeMetabelian.Free.incl,
        Nat.not_lt.mpr (by omega : k + 1 ≤ i.val),
        Nat.not_lt.mpr (by omega : k ≤ i.val),
        show i ≠ (⟨k, hk⟩ : Fin (n + 1)) by
          intro h; have := congrArg Fin.val h; simp only at this; omega] <;>
        omega

/-- A placed row has either no mark, or exactly one mark with ordinary entries
on its two sides. Coefficients live in the surrounding Finsupp. -/
inductive MarkedRow
  | ordinary (word : List (AdaptedIndex n L data hn))
  | marked (left : List (AdaptedIndex n L data hn))
      (relation : Relations n L data) (bound : Fin (n + 2))
      (right : List (AdaptedIndex n L data hn))

noncomputable instance : DecidableEq (MarkedRow n L data hn) :=
  Classical.decEq _

namespace MarkedRow

def basisWord (word : List (AdaptedIndex n L data hn)) :
    UEA ℤ (FreeModel n L) :=
  LieRings.PBW.basisWord ℤ (FreeModel n L)
    (AdaptedIndex n L data hn) (adaptedWeightedBasis n L data hn).basis word

/-- Literal evaluation. At the top bound the stored relation is evaluated
whole. -/
def value : MarkedRow n L data hn → UEA ℤ (FreeModel n L)
  | ordinary word => basisWord n L data hn word
  | marked left rho k right =>
      basisWord n L data hn left *
        UniversalEnvelopingAlgebra.ι ℤ
          (rowTruncation n L k.val (by omega) (rho : FreeModel n L)) *
        basisWord n L data hn right

end MarkedRow

def markedRowEvaluation :
    (MarkedRow n L data hn →₀ ℤ) →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
  Finsupp.linearCombination ℤ (MarkedRow.value n L data hn)

@[simp] theorem markedRowEvaluation_single (r : MarkedRow n L data hn)
    (z : ℤ) :
    markedRowEvaluation n L data hn (Finsupp.single r z) =
      z • r.value := by
  simp [markedRowEvaluation]

/-- Ordinary adjacent transfer with its fixed sign. -/
theorem ordinaryTransfer (left right : List (AdaptedIndex n L data hn))
    (v u : AdaptedIndex n L data hn) :
    MarkedRow.basisWord n L data hn (left ++ v :: u :: right) =
      MarkedRow.basisWord n L data hn (left ++ u :: v :: right) +
        MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            ⁅(adaptedWeightedBasis n L data hn).basis v,
              (adaptedWeightedBasis n L data hn).basis u⁆ *
          MarkedRow.basisWord n L data hn right := by
  simpa [MarkedRow.basisWord, LieRings.PBW.basisWord,
    LieRings.PBW.word, LieRings.DegreeFive.envelopingWord] using
    LieRings.DegreeFive.envelopingWord_adjacent_swap ℤ (FreeModel n L)
      (left.map (adaptedWeightedBasis n L data hn).basis)
      (right.map (adaptedWeightedBasis n L data hn).basis)
      ((adaptedWeightedBasis n L data hn).basis v)
      ((adaptedWeightedBasis n L data hn).basis u)

/-- Marked adjacent transfer. The correction is explicitly labelled by a
full relation; hcomm is the local grading/truncation square. -/
theorem markedTransfer
    (left right : List (AdaptedIndex n L data hn))
    (v : AdaptedIndex n L data hn) (rho : Relations n L data)
    (k : Fin (n + 2)) (rho' : Relations n L data)
    (hcomm : rowTruncation n L (min (n + 1)
        (k.val + (adaptedWeightedBasis n L data hn).weight v)) (by omega)
          (rho' : FreeModel n L) =
      ⁅(adaptedWeightedBasis n L data hn).basis v,
        rowTruncation n L k.val (by omega) (rho : FreeModel n L)⁆) :
    MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            ((adaptedWeightedBasis n L data hn).basis v) *
          UniversalEnvelopingAlgebra.ι ℤ
            (rowTruncation n L k.val (by omega) (rho : FreeModel n L)) *
          MarkedRow.basisWord n L data hn right =
      MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            (rowTruncation n L k.val (by omega) (rho : FreeModel n L)) *
          UniversalEnvelopingAlgebra.ι ℤ
            ((adaptedWeightedBasis n L data hn).basis v) *
          MarkedRow.basisWord n L data hn right +
        MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            (rowTruncation n L (min (n + 1)
              (k.val + (adaptedWeightedBasis n L data hn).weight v))
              (by omega) (rho' : FreeModel n L)) *
          MarkedRow.basisWord n L data hn right := by
  rw [hcomm]
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L)
    ((adaptedWeightedBasis n L data hn).basis v)
    (rowTruncation n L k.val (by omega) (rho : FreeModel n L))
  calc
    _ = MarkedRow.basisWord n L data hn left *
          (UniversalEnvelopingAlgebra.ι ℤ
              ((adaptedWeightedBasis n L data hn).basis v) *
            UniversalEnvelopingAlgebra.ι ℤ
              (rowTruncation n L k.val (by omega) (rho : FreeModel n L))) *
          MarkedRow.basisWord n L data hn right := by noncomm_ring
    _ = MarkedRow.basisWord n L data hn left *
          (UniversalEnvelopingAlgebra.ι ℤ
              (rowTruncation n L k.val (by omega) (rho : FreeModel n L)) *
            UniversalEnvelopingAlgebra.ι ℤ
              ((adaptedWeightedBasis n L data hn).basis v) +
            UniversalEnvelopingAlgebra.ι ℤ
              ⁅(adaptedWeightedBasis n L data hn).basis v,
                rowTruncation n L k.val (by omega) (rho : FreeModel n L)⁆) *
          MarkedRow.basisWord n L data hn right := by rw [hswap]
    _ = _ := by noncomm_ring

/-- Marked truncation. Its exposed homogeneous edge is an ordinary Lie
element and is never coerced to Relations. -/
theorem markedTruncation (left right : List (AdaptedIndex n L data hn))
    (rho : Relations n L data) (k : ℕ) (hk : k < n + 1) :
    MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            (rowTruncation n L (k + 1) (by omega) (rho : FreeModel n L)) *
          MarkedRow.basisWord n L data hn right =
      MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            (rowTruncation n L k (by omega) (rho : FreeModel n L)) *
          MarkedRow.basisWord n L data hn right +
        MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            (FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
              k hk
              (FreeMetabelian.Free.weightProject
                (X := Generator L) (c := n + 1) k hk
                (rho : FreeModel n L))) *
          MarkedRow.basisWord n L data hn right := by
  rw [rowTruncation_succ n L k hk (rho : FreeModel n L), map_add]
  noncomm_ring

/-! ## Exact finite occurrence ledger -/

/-- Labels make equal-valued occurrences distinct ledger generators. -/
structure RowOccurrence where
  label : ℕ
  row : MarkedRow n L data hn

noncomputable instance : DecidableEq (RowOccurrence n L data hn) :=
  Classical.decEq _

def occurrenceValue (o : RowOccurrence n L data hn) :
    UEA ℤ (FreeModel n L) :=
  o.row.value

/-- One signed replacement. Soundness is the literal row identity used to
construct the step, rather than a statement about the desired boundary. -/
structure LedgerStep where
  input : RowOccurrence n L data hn
  coefficient : ℤ
  outputs : RowOccurrence n L data hn →₀ ℤ
  sound :
    coefficient • occurrenceValue n L data hn input =
      Finsupp.linearCombination ℤ (occurrenceValue n L data hn) outputs

def LedgerStep.boundary (s : LedgerStep n L data hn) :
    RowOccurrence n L data hn →₀ ℤ :=
  Finsupp.single s.input s.coefficient - s.outputs

def runLedger (initial : RowOccurrence n L data hn →₀ ℤ) :
    List (LedgerStep n L data hn) → RowOccurrence n L data hn →₀ ℤ
  | [] => initial
  | s :: ss => runLedger (initial - s.boundary) ss

/-- Prefix ledger / finite integral Stokes formula. -/
theorem runLedger_eq (initial : RowOccurrence n L data hn →₀ ℤ)
    (steps : List (LedgerStep n L data hn)) :
    initial - runLedger n L data hn initial steps =
      (steps.map (fun s ↦ s.boundary)).sum := by
  induction steps generalizing initial with
  | nil => simp [runLedger]
  | cons s ss ih =>
      rw [runLedger]
      calc
        initial - runLedger n L data hn (initial - s.boundary) ss =
            s.boundary +
              ((initial - s.boundary) -
                runLedger n L data hn (initial - s.boundary) ss) := by abel
        _ = s.boundary +
            (ss.map (fun t ↦ t.boundary)).sum := by rw [ih]
        _ = ((s :: ss).map (fun t ↦ t.boundary)).sum := by simp

theorem ledgerBoundary_evaluation_zero (s : LedgerStep n L data hn) :
    Finsupp.linearCombination ℤ (occurrenceValue n L data hn) s.boundary = 0 := by
  rw [LedgerStep.boundary, map_sub]
  simp only [Finsupp.linearCombination_single]
  exact sub_eq_zero.mpr s.sound

/-- Evaluating a complete ledger recovers the initial frontier exactly. -/
theorem runLedger_evaluation (initial : RowOccurrence n L data hn →₀ ℤ)
    (steps : List (LedgerStep n L data hn)) :
    Finsupp.linearCombination ℤ (occurrenceValue n L data hn)
        (runLedger n L data hn initial steps) =
      Finsupp.linearCombination ℤ (occurrenceValue n L data hn) initial := by
  have h := congrArg
    (Finsupp.linearCombination ℤ (occurrenceValue n L data hn))
    (runLedger_eq n L data hn initial steps)
  rw [map_sub, map_list_sum] at h
  have hz : ((steps.map (fun s ↦ s.boundary)).map
      (Finsupp.linearCombination ℤ (occurrenceValue n L data hn))).sum = 0 := by
    rw [List.map_map]
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact ledgerBoundary_evaluation_zero n L data hn s
  rw [hz, sub_eq_zero] at h
  exact h.symm

/-- Factor number, mark, and unresolved-pair count, in that order. -/
abbrev RowMeasure := ℕ × (ℕ × ℕ)

def rowMeasureLt : RowMeasure → RowMeasure → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem rowMeasureLt_wellFounded : WellFounded rowMeasureLt :=
  Nat.lt_wfRel.wf.prod_lex (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

/-- Reusable deterministic normalizer. A caller supplies exactly one finite
expansion at each redex and verifies strict descent of every output. -/
def deterministicCollector
    (measure : MarkedRow n L data hn → RowMeasure)
    (expand : MarkedRow n L data hn →
      Option (List (ℤ × MarkedRow n L data hn)))
    (hdecrease : ∀ {r qs}, expand r = some qs →
      ∀ q ∈ qs, rowMeasureLt (measure q.2) (measure r))
    (hpreserve : ∀ {r qs}, expand r = some qs →
      (qs.map fun q ↦ q.1 • q.2.value).sum = r.value) :
    LieRings.DegreeFive.FiniteTaggedCollector
      (MarkedRow n L data hn) (UEA ℤ (FreeModel n L)) where
  relation x y := rowMeasureLt (measure x) (measure y)
  wellFounded := InvImage.wf measure rowMeasureLt_wellFounded
  expansion := expand
  value := MarkedRow.value n L data hn
  decreases := hdecrease
  preserves := hpreserve

theorem deterministicCollector_evaluate
    (measure : MarkedRow n L data hn → RowMeasure)
    (expand : MarkedRow n L data hn →
      Option (List (ℤ × MarkedRow n L data hn)))
    (hdecrease : ∀ {r qs}, expand r = some qs →
      ∀ q ∈ qs, rowMeasureLt (measure q.2) (measure r))
    (hpreserve : ∀ {r qs}, expand r = some qs →
      (qs.map fun q ↦ q.1 • q.2.value).sum = r.value)
    (r : MarkedRow n L data hn) :
    (deterministicCollector n L data hn measure expand hdecrease hpreserve).evaluate
        ((deterministicCollector n L data hn measure expand hdecrease hpreserve).normalForm r) =
      r.value :=
  LieRings.DegreeFive.FiniteTaggedCollector.evaluate_normalForm _ r

/-! ## The collector used by the closed square

The initial relative rows have their full relation at the far left.  That
property is preserved by a truncation step.  Consequently the concrete
collector below needs ordinary adjacent interchanges and the successive
truncation edge; the more general marked interchange proved above is retained
for the local square and for the terminal transport certificate.
-/

/-- Finite coordinates of a Lie element in the fixed homogeneous PBW basis. -/
def adaptedCoordinates (x : FreeModel n L) :
    List (ℤ × AdaptedIndex n L data hn) :=
  ((adaptedBasis n L data hn).repr x).support.toList.map
    (fun i ↦ (((adaptedBasis n L data hn).repr x) i, i))

theorem adaptedCoordinates_sum (x : FreeModel n L) :
    ((adaptedCoordinates n L data hn x).map
      (fun q ↦ q.1 • adaptedBasis n L data hn q.2)).sum = x := by
  classical
  rw [adaptedCoordinates, List.map_map]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
  rw [Finset.toList_toFinset]
  change ((adaptedBasis n L data hn).repr x).sum
    (fun i z ↦ z • adaptedBasis n L data hn i) = x
  exact (adaptedBasis n L data hn).linearCombination_repr x

/-- The ordinary inversion number used in the terminating measure. -/
def rowInversionCount : List (AdaptedIndex n L data hn) → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + rowInversionCount xs

theorem rowInversionCount_swap
    (left right : List (AdaptedIndex n L data hn))
    (x y : AdaptedIndex n L data hn) (hyx : y < x) :
    rowInversionCount n L data hn (left ++ x :: y :: right) =
      rowInversionCount n L data hn (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnxy : ¬ x < y := not_lt_of_ge (le_of_lt hyx)
      simp [rowInversionCount, hyx, hnxy, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, rowInversionCount]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp <;> omega
      rw [hfilter, ih]
      omega

/-- The exact lexicographic measure from the implementation plan. -/
def markedRowMeasure : MarkedRow n L data hn → RowMeasure
  | .ordinary word => (word.length, 0, rowInversionCount n L data hn word)
  | .marked left _ k right =>
      (left.length + right.length + 1, k.val,
        right.length + rowInversionCount n L data hn (left ++ right))

/-- The correction produced while moving a full relation to the right.  Its
label remains a genuine member of the original relation ideal. -/
def relationRightBracket (rho : Relations n L data)
    (v : AdaptedIndex n L data hn) : Relations n L data :=
  ⟨⁅(rho : FreeModel n L), (adaptedWeightedBasis n L data hn).basis v⁆,
    by
      rw [← lie_skew]
      exact (Relations n L data).neg_mem
        ((Relations n L data).lie_mem rho.property)⟩

/-- The right-moving form of the full-relation transfer.  The collector uses
this rule only at the top mark, so the grading square reduces literally to
`prLE(n+1)=id`; truncated marks are never interchanged. -/
theorem markedTransferRightTop
    (left right : List (AdaptedIndex n L data hn))
    (rho : Relations n L data) (v : AdaptedIndex n L data hn) :
    (MarkedRow.marked left rho ⟨n + 1, by omega⟩ (v :: right) :
        MarkedRow n L data hn).value =
      (MarkedRow.marked (left ++ [v]) rho ⟨n + 1, by omega⟩ right :
        MarkedRow n L data hn).value +
      (MarkedRow.marked left (relationRightBracket n L data hn rho v)
          ⟨n + 1, by omega⟩ right : MarkedRow n L data hn).value := by
  simp only [MarkedRow.value]
  rw [rowTruncation_top n L]
  rw [rowTruncation_top n L]
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L)
    (rho : FreeModel n L) ((adaptedWeightedBasis n L data hn).basis v)
  calc
    _ = MarkedRow.basisWord n L data hn left *
          (UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
            UniversalEnvelopingAlgebra.ι ℤ
              ((adaptedWeightedBasis n L data hn).basis v)) *
          MarkedRow.basisWord n L data hn right := by
            simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word, List.map_append]
            noncomm_ring
    _ = MarkedRow.basisWord n L data hn left *
          (UniversalEnvelopingAlgebra.ι ℤ
              ((adaptedWeightedBasis n L data hn).basis v) *
            UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) +
            UniversalEnvelopingAlgebra.ι ℤ
              ⁅(rho : FreeModel n L),
                (adaptedWeightedBasis n L data hn).basis v⁆) *
          MarkedRow.basisWord n L data hn right := by rw [hswap]
    _ = _ := by
      simp [relationRightBracket, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.word, List.map_append]
      noncomm_ring

/-- Expand the bracket correction of one ordinary adjacent interchange in
the adapted basis. -/
def ordinaryCorrection
    (left right : List (AdaptedIndex n L data hn))
    (x y : AdaptedIndex n L data hn) :
    List (ℤ × MarkedRow n L data hn) :=
  (adaptedCoordinates n L data hn
      ⁅(adaptedWeightedBasis n L data hn).basis x,
        (adaptedWeightedBasis n L data hn).basis y⁆).map
    (fun q ↦ (q.1, .ordinary (left ++ q.2 :: right)))

/-- The deterministic full-relation expansion.  A one-factor marked row is
kept whole, exactly as in the manuscript. -/
def closedSquareExpansion : MarkedRow n L data hn →
    Option (List (ℤ × MarkedRow n L data hn))
  | .ordinary word =>
      match LieRings.DegreeFive.chooseAdjacentInversion? word with
      | none => none
      | some d => some
          ((1, .ordinary (d.left ++ d.y :: d.x :: d.right)) ::
            ordinaryCorrection n L data hn d.left d.right d.x d.y)
  | .marked left rho k right =>
      if hfactorOne : left = [] ∧ right = [] then none
      else if hfactorTwo : left.length + right.length + 1 = 2 then none
      else match right with
        | v :: rest =>
            if htop : k.val = n + 1 then
              some [(1, .marked (left ++ [v]) rho k rest),
                (1, .marked left
                  (relationRightBracket n L data hn rho v) k rest)]
            else none
        | [] =>
            if hk : k.val = 0 then some []
            else
              let k' : Fin (n + 2) := ⟨k.val - 1, by omega⟩
              let component := FreeMetabelian.Free.weightIncl
                (X := Generator L) (c := n + 1) (k.val - 1) (by omega)
                (FreeMetabelian.Free.weightProject
                  (X := Generator L) (c := n + 1) (k.val - 1) (by omega)
                  (rho : FreeModel n L))
              some ((1, .marked left rho k' []) ::
                (adaptedCoordinates n L data hn component).map
                  (fun q ↦ (q.1, .ordinary (left ++ [q.2]))))

theorem closedSquareExpansion_decreases {r : MarkedRow n L data hn}
    {qs : List (ℤ × MarkedRow n L data hn)}
    (h : closedSquareExpansion n L data hn r = some qs) :
    ∀ q ∈ qs,
      rowMeasureLt (markedRowMeasure n L data hn q.2)
        (markedRowMeasure n L data hn r) := by
  classical
  cases r with
  | ordinary word =>
      simp only [closedSquareExpansion] at h
      split at h
      · contradiction
      · rename_i d hd
        rw [Option.some.injEq] at h
        subst qs
        obtain ⟨hword, hyx⟩ :=
          LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        ·
          rw [hword]
          simp only [Prod.snd, markedRowMeasure, List.length_append,
            List.length_cons]
          apply Prod.Lex.right
          apply Prod.Lex.right
          have hinv := rowInversionCount_swap n L data hn
            d.left d.right d.x d.y hyx
          omega
        · rw [ordinaryCorrection, List.mem_map] at hq
          obtain ⟨⟨z, i⟩, hi, rfl⟩ := hq
          rw [hword]
          apply Prod.Lex.left
          simp
  | marked left rho k right =>
      by_cases hfactorOne : left = [] ∧ right = []
      · simp [closedSquareExpansion, hfactorOne] at h
      by_cases hfactorTwo : left.length + right.length + 1 = 2
      · simp [closedSquareExpansion, hfactorOne, hfactorTwo] at h
      cases right with
      | cons v rest =>
          by_cases htop : k.val = n + 1
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, htop] at h
            rcases h with ⟨_, rfl⟩
            intro q hq
            simp at hq
            rcases hq with rfl | rfl
            · simp only [markedRowMeasure, List.length_append,
                List.length_singleton, List.length_cons, List.length_nil]
              rw [show left.length + (0 + 1) + rest.length + 1 =
                left.length + (rest.length + 1) + 1 by omega]
              have hword : (left ++ [v]) ++ rest = left ++ v :: rest := by simp
              rw [hword]
              apply Prod.Lex.right
              apply Prod.Lex.right
              omega
            · simp only [markedRowMeasure, List.length_cons]
              apply Prod.Lex.left
              omega
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, htop] at h
      | nil =>
          by_cases hk : k.val = 0
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hk] at h
            rcases h with ⟨_, _, rfl⟩
            simp
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hk] at h
            rcases h with ⟨_, _, hqs⟩
            rw [← hqs]
            intro q hq
            simp only [List.mem_cons] at hq
            rcases hq with rfl | hq
            · simp only [markedRowMeasure, List.length_nil,
                List.length_append, List.length_singleton, zero_add]
              apply Prod.Lex.right
              apply Prod.Lex.left
              omega
            · rw [List.mem_map] at hq
              obtain ⟨⟨z, i⟩, hi, rfl⟩ := hq
              simp only [markedRowMeasure, List.length_nil,
                List.length_append, List.length_singleton, zero_add]
              apply Prod.Lex.right
              apply Prod.Lex.left
              omega

theorem closedSquareExpansion_preserves {r : MarkedRow n L data hn}
    {qs : List (ℤ × MarkedRow n L data hn)}
    (h : closedSquareExpansion n L data hn r = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value).sum = r.value := by
  classical
  cases r with
  | ordinary word =>
      simp only [closedSquareExpansion] at h
      split at h
      · contradiction
      · rename_i d hd
        rw [Option.some.injEq] at h
        subst qs
        obtain ⟨hword, hyx⟩ :=
          LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
        rw [hword]
        simp only [List.map_cons, List.sum_cons, one_smul]
        simp only [MarkedRow.value]
        rw [ordinaryTransfer n L data hn d.left d.right d.x d.y]
        congr 1
        rw [ordinaryCorrection, List.map_map]
        let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
          { toFun := fun z ↦ MarkedRow.basisWord n L data hn d.left *
                UniversalEnvelopingAlgebra.ι ℤ z *
                MarkedRow.basisWord n L data hn d.right
            map_add' := by intro x y; rw [map_add, mul_add, add_mul]
            map_smul' := by
              intro z x
              rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
              simp only [RingHom.id_apply] }
        have hc := congrArg context
          (adaptedCoordinates_sum n L data hn
            ⁅(adaptedWeightedBasis n L data hn).basis d.x,
              (adaptedWeightedBasis n L data hn).basis d.y⁆)
        rw [map_list_sum] at hc
        calc
          ((adaptedCoordinates n L data hn
                ⁅(adaptedWeightedBasis n L data hn).basis d.x,
                  (adaptedWeightedBasis n L data hn).basis d.y⁆).map
              (fun q ↦ q.1 •
                (MarkedRow.ordinary (d.left ++ q.2 :: d.right) :
                  MarkedRow n L data hn).value)).sum =
              ((adaptedCoordinates n L data hn
                ⁅(adaptedWeightedBasis n L data hn).basis d.x,
                  (adaptedWeightedBasis n L data hn).basis d.y⁆).map
                (fun q ↦ context
                  (q.1 • adaptedBasis n L data hn q.2))).sum := by
                    congr 1
                    apply List.map_congr_left
                    intro q hq
                    rcases q with ⟨z, i⟩
                    simp [context, MarkedRow.value, MarkedRow.basisWord,
                      LieRings.PBW.basisWord, LieRings.PBW.word,
                      List.map_append, adaptedWeightedBasis]
                    noncomm_ring
          _ = context ⁅(adaptedWeightedBasis n L data hn).basis d.x,
                (adaptedWeightedBasis n L data hn).basis d.y⁆ := by
                  simpa only [List.map_map, Function.comp_apply] using hc
          _ = _ := rfl
  | marked left rho k right =>
      by_cases hfactorOne : left = [] ∧ right = []
      · simp [closedSquareExpansion, hfactorOne] at h
      by_cases hfactorTwo : left.length + right.length + 1 = 2
      · simp [closedSquareExpansion, hfactorOne, hfactorTwo] at h
      cases right with
      | cons v rest =>
          by_cases htop : k.val = n + 1
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, htop] at h
            rcases h with ⟨_, rfl⟩
            have hk : k = ⟨n + 1, by omega⟩ := Fin.ext htop
            simp only [List.map_cons, List.map_singleton, List.sum_cons,
              List.sum_singleton, one_smul]
            simpa [hk] using
              (markedTransferRightTop n L data hn left rest rho v).symm
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, htop] at h
      | nil =>
          by_cases hk : k.val = 0
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hk] at h
            rcases h with ⟨_, _, rfl⟩
            have hzero : rowTruncation n L k.val (by omega)
                (rho : FreeModel n L) = 0 := by
              simpa [hk] using rowTruncation_zero n L hn (rho : FreeModel n L)
            simp [MarkedRow.value, MarkedRow.basisWord,
              LieRings.PBW.basisWord, LieRings.PBW.word, hzero]
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hk] at h
            rcases h with ⟨_, _, hqs⟩
            rw [← hqs]
            simp only [List.map_cons, List.sum_cons, one_smul, List.map_map]
            let component := FreeMetabelian.Free.weightIncl
              (X := Generator L) (c := n + 1) (k.val - 1) (by omega)
              (FreeMetabelian.Free.weightProject
                (X := Generator L) (c := n + 1) (k.val - 1) (by omega)
                (rho : FreeModel n L))
            let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
              { toFun := fun x ↦ MarkedRow.basisWord n L data hn left *
                    UniversalEnvelopingAlgebra.ι ℤ x
                map_add' := by intro x y; rw [map_add, mul_add]
                map_smul' := by
                  intro z x
                  rw [map_zsmul, mul_smul_comm]
                  simp only [RingHom.id_apply] }
            have hc := congrArg context
              (adaptedCoordinates_sum n L data hn component)
            rw [map_list_sum] at hc
            have htr := markedTruncation n L data hn left [] rho
              (k.val - 1) (by omega)
            have hsucc : k.val - 1 + 1 = k.val := by omega
            have hcomponent :
                ((adaptedCoordinates n L data hn component).map
                  (fun q ↦ q.1 •
                    (MarkedRow.ordinary (left ++ [q.2]) :
                      MarkedRow n L data hn).value)).sum =
                  MarkedRow.basisWord n L data hn left *
                    UniversalEnvelopingAlgebra.ι ℤ component := by
              calc
                _ = ((adaptedCoordinates n L data hn component).map
                    (fun q ↦ context
                      (q.1 • adaptedBasis n L data hn q.2))).sum := by
                    congr 1
                    apply List.map_congr_left
                    intro q hq
                    rcases q with ⟨z, i⟩
                    simp [context, MarkedRow.value, MarkedRow.basisWord,
                      LieRings.PBW.basisWord, LieRings.PBW.word,
                      List.map_append, adaptedWeightedBasis]
                _ = context component := by
                  simpa only [List.map_map, Function.comp_apply] using hc
                _ = _ := rfl
            change
              (MarkedRow.marked left rho ⟨k.val - 1, by omega⟩ [] :
                  MarkedRow n L data hn).value +
                ((adaptedCoordinates n L data hn component).map
                  (fun q ↦ q.1 •
                    (MarkedRow.ordinary (left ++ [q.2]) :
                      MarkedRow n L data hn).value)).sum =
                (MarkedRow.marked left rho k [] :
                  MarkedRow n L data hn).value
            rw [hcomponent]
            simpa [MarkedRow.value, component, hsucc,
              MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word] using htr.symm

/-- The fully specified collector used in the PBW assembly. -/
def closedSquareCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (MarkedRow n L data hn) (UEA ℤ (FreeModel n L)) :=
  deterministicCollector n L data hn
    (markedRowMeasure n L data hn)
    (closedSquareExpansion n L data hn)
    (closedSquareExpansion_decreases n L data hn)
    (closedSquareExpansion_preserves n L data hn)

theorem closedSquareCollector_evaluate (r : MarkedRow n L data hn) :
    (closedSquareCollector n L data hn).evaluate
        ((closedSquareCollector n L data hn).normalForm r) = r.value :=
  LieRings.DegreeFive.FiniteTaggedCollector.evaluate_normalForm _ r

/-! ## The complete initial frontier

The governing witness has arbitrary enveloping-algebra right factors.  The
collector, on the other hand, works on PBW basis words.  The following finite
expansion is the exact bridge; in particular it does not assume that the
chosen right factors were already monomials. -/

/-- The sorted PBW word belonging to an exponent vector. -/
def exponentWord (e : AdaptedIndex n L data hn →₀ ℕ) :
    List (AdaptedIndex n L data hn) :=
  (Finsupp.toMultiset e).sort (· ≤ ·)

/-- Expand one arbitrary right factor into top-marked PBW rows. -/
def markedRowsOfRightFactor (rho : Relations n L data)
    (u : UEA ℤ (FreeModel n L)) : MarkedRow n L data hn →₀ ℤ :=
  ((adaptedWeightedBasis n L data hn).pbwEquiv.symm u).sum
    (fun e z ↦ Finsupp.single
      (.marked [] rho ⟨n + 1, by omega⟩ (exponentWord n L data hn e)) z)

theorem evaluate_markedRowsOfRightFactor (rho : Relations n L data)
    (u : UEA ℤ (FreeModel n L)) :
    (closedSquareCollector n L data hn).evaluate
        (markedRowsOfRightFactor n L data hn rho u) =
      UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) * u := by
  classical
  let B := adaptedWeightedBasis n L data hn
  change Finsupp.linearCombination ℤ (MarkedRow.value n L data hn)
      (((B.pbwEquiv.symm u).sum fun e z ↦
        Finsupp.single
          (.marked [] rho ⟨n + 1, by omega⟩ (exponentWord n L data hn e)) z)) = _
  rw [map_finsuppSum]
  simp only [Finsupp.linearCombination_single]
  have hu : (B.pbwEquiv.symm u).sum
      (fun e z ↦ z • LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
        (AdaptedIndex n L data hn) B.basis e) = u := by
    have hsum : (B.pbwEquiv.symm u).sum
        (fun e z ↦ MvPolynomial.monomial e z) = B.pbwEquiv.symm u := by
      simpa only [MvPolynomial.monomial] using
        (Finsupp.sum_single (B.pbwEquiv.symm u))
    calc
      _ = (B.pbwEquiv.symm u).sum
          (fun e z ↦ B.pbwEquiv (MvPolynomial.monomial e z)) := by
        apply Finsupp.sum_congr
        intro e he
        rw [B.pbwEquiv_monomial]
      _ = B.pbwEquiv ((B.pbwEquiv.symm u).sum
          (fun e z ↦ MvPolynomial.monomial e z)) := by
        rw [map_finsuppSum]
      _ = B.pbwEquiv (B.pbwEquiv.symm u) := by rw [hsum]
      _ = u := B.pbwEquiv.apply_symm_apply u
  calc
    _ = (B.pbwEquiv.symm u).sum (fun e z ↦ z •
        (UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
          LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
            (AdaptedIndex n L data hn) B.basis e)) := by
      apply Finsupp.sum_congr
      intro e he
      congr 1
      simp [MarkedRow.value, exponentWord, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.orderedMonomial,
        LieRings.PBW.word, List.map_map, Function.comp_def, B]
    _ = UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
        (B.pbwEquiv.symm u).sum (fun e z ↦ z •
          LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
            (AdaptedIndex n L data hn) B.basis e) := by
      rw [Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro e he
      rw [mul_smul_comm]
    _ = _ := by rw [hu]

/-- The complete finite initial row expression attached to a governing
witness.  Every mark stores the original full relation. -/
def GoverningWitness.closedSquareInitial {a : L}
    (w : GoverningWitness n L data a) : MarkedRow n L data hn →₀ ℤ :=
  w.relationCoefficients.sum (fun p z ↦
    z • markedRowsOfRightFactor n L data hn p.1 p.2)

theorem GoverningWitness.evaluate_closedSquareInitial {a : L}
    (w : GoverningWitness n L data a) :
    (closedSquareCollector n L data hn).evaluate
        (GoverningWitness.closedSquareInitial n L data hn w) =
      w.theta := by
  classical
  rw [GoverningWitness.closedSquareInitial, map_finsuppSum,
    GoverningWitness.theta]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, evaluate_markedRowsOfRightFactor]

/-- The post-collection frontier of the complete governing expression. -/
def GoverningWitness.closedSquareFrontier {a : L}
    (w : GoverningWitness n L data a) : MarkedRow n L data hn →₀ ℤ :=
  (GoverningWitness.closedSquareInitial n L data hn w).sum (fun r z ↦
    z • (closedSquareCollector n L data hn).normalForm r)

theorem GoverningWitness.evaluate_closedSquareFrontier {a : L}
    (w : GoverningWitness n L data a) :
    (closedSquareCollector n L data hn).evaluate
        (GoverningWitness.closedSquareFrontier n L data hn w) =
      w.theta := by
  classical
  rw [GoverningWitness.closedSquareFrontier, map_finsuppSum]
  calc
    _ = (closedSquareCollector n L data hn).evaluate
        (GoverningWitness.closedSquareInitial n L data hn w) := by
      change (GoverningWitness.closedSquareInitial n L data hn w).sum
          (fun r z ↦ (closedSquareCollector n L data hn).evaluate
            (z • (closedSquareCollector n L data hn).normalForm r)) =
        (GoverningWitness.closedSquareInitial n L data hn w).sum
          (fun r z ↦ z • MarkedRow.value n L data hn r)
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul, closedSquareCollector_evaluate]
    _ = w.theta := GoverningWitness.evaluate_closedSquareInitial n L data hn w

/-! ## The descending-factor trace

The normal form alone deliberately forgets internal rows.  The manuscript's
Koszul packets are read at truncation walls, so we retain exactly those
internal occurrences.  Coefficients are propagated down the rewrite tree;
consequently a correction created at a larger factor number is present when a
smaller factor number is read. -/

/-- A genuine truncation-wall occurrence.  Its relation is still a member of
the full relation ideal; the exposed homogeneous component is not stored as a
relation. -/
structure TruncationCell where
  left : List (AdaptedIndex n L data hn)
  relation : Relations n L data
  bound : Fin (n + 2)
  factor_ge_three : 3 ≤ left.length + 1
  bound_pos : 0 < bound.val

noncomputable instance : DecidableEq (TruncationCell n L data hn) :=
  Classical.decEq _

def TruncationCell.row (c : TruncationCell n L data hn) :
    MarkedRow n L data hn :=
  .marked c.left c.relation c.bound []

/-- Recognize precisely the marked truncation events of the deterministic
collector. -/
def truncationCell? : MarkedRow n L data hn →
    Option (TruncationCell n L data hn)
  | .ordinary _ => none
  | .marked left rho k right =>
      if hr : right = [] then
        if hf : 3 ≤ left.length + 1 then
          if hk : 0 < k.val then
            some ⟨left, rho, k, hf, hk⟩
          else none
        else none
      else none

private def closedSquareTraceCellsStep
    (r : MarkedRow n L data hn)
    (rec : ∀ q, (closedSquareCollector n L data hn).relation q r →
      TruncationCell n L data hn →₀ ℤ) :
    TruncationCell n L data hn →₀ ℤ :=
  let here := match truncationCell? n L data hn r with
    | none => 0
    | some c => Finsupp.single c 1
  match h : (closedSquareCollector n L data hn).expansion r with
  | none => here
  | some qs => here + (qs.attach.map fun q ↦
      q.1.1 • rec q.1.2
        ((closedSquareCollector n L data hn).decreases h q.1 q.2)).sum

/-- The complete signed multiset of truncation cells below one root row. -/
def closedSquareTraceCells (r : MarkedRow n L data hn) :
    TruncationCell n L data hn →₀ ℤ :=
  (closedSquareCollector n L data hn).wellFounded.fix
    (closedSquareTraceCellsStep n L data hn) r

theorem closedSquareTraceCells_eq (r : MarkedRow n L data hn) :
    closedSquareTraceCells n L data hn r =
      closedSquareTraceCellsStep n L data hn r
        (fun q _ ↦ closedSquareTraceCells n L data hn q) := by
  rw [closedSquareTraceCells,
    (closedSquareCollector n L data hn).wellFounded.fix_eq]
  congr 1

/-- Recursive trace equation at a terminal row. -/
theorem closedSquareTraceCells_eq_of_expansion_none
    (r : MarkedRow n L data hn)
    (h : closedSquareExpansion n L data hn r = none) :
    closedSquareTraceCells n L data hn r =
      match truncationCell? n L data hn r with
      | none => 0
      | some c => Finsupp.single c 1 := by
  rw [closedSquareTraceCells_eq]
  unfold closedSquareTraceCellsStep
  have h' : (closedSquareCollector n L data hn).expansion r = none := h
  cases hc : truncationCell? n L data hn r with
  | none =>
      simp only [hc]
      split
      · rfl
      · rename_i qs he
        rw [h'] at he
        contradiction
  | some c =>
      simp only [hc]
      split
      · rfl
      · rename_i qs he
        rw [h'] at he
        contradiction

/-- Recursive trace equation at one nonterminal rewrite. -/
theorem closedSquareTraceCells_eq_of_expansion_some
    (r : MarkedRow n L data hn)
    (qs : List (ℤ × MarkedRow n L data hn))
    (h : closedSquareExpansion n L data hn r = some qs) :
    closedSquareTraceCells n L data hn r =
      (match truncationCell? n L data hn r with
        | none => 0
        | some c => Finsupp.single c 1) +
      (qs.attach.map fun q ↦
        q.1.1 • closedSquareTraceCells n L data hn q.1.2).sum := by
  rw [closedSquareTraceCells_eq]
  unfold closedSquareTraceCellsStep
  have h' : (closedSquareCollector n L data hn).expansion r = some qs := h
  cases hc : truncationCell? n L data hn r with
  | none =>
      simp only [hc]
      split
      · rename_i he
        rw [h'] at he
        contradiction
      · rename_i qs' he
        have hqs : qs' = qs := by
          rw [h'] at he
          exact Option.some.inj he.symm
        subst qs'
        rfl
  | some c =>
      simp only [hc]
      split
      · rename_i he
        rw [h'] at he
        contradiction
      · rename_i qs' he
        have hqs : qs' = qs := by
          rw [h'] at he
          exact Option.some.inj he.symm
        subst qs'
        rfl

/-- All truncation cells of the complete governing expression, with the
coefficient of every occurrence propagated from its initial PBW row. -/
def GoverningWitness.closedSquareCells {a : L}
    (w : GoverningWitness n L data a) :
    TruncationCell n L data hn →₀ ℤ :=
  (GoverningWitness.closedSquareInitial n L data hn w).sum
    (fun r z ↦ z • closedSquareTraceCells n L data hn r)

/-! ## The retained factor-two frontier -/

/-- The two placements which remain distinct at the quadratic edge. -/
inductive TerminalPlacement
  | relationLeft
  | relationRight
  deriving DecidableEq

/-- A terminal marked factor-two occurrence, with its genuine full relation
and its single homogeneous ordinary factor retained. -/
structure TerminalFactorTwo where
  relation : Relations n L data
  factor : AdaptedIndex n L data hn
  placement : TerminalPlacement

noncomputable instance : DecidableEq (TerminalFactorTwo n L data hn) :=
  Classical.decEq _

def TerminalFactorTwo.row (c : TerminalFactorTwo n L data hn) :
    MarkedRow n L data hn :=
  match c.placement with
  | .relationLeft => .marked [] c.relation ⟨n + 1, by omega⟩ [c.factor]
  | .relationRight => .marked [c.factor] c.relation ⟨n + 1, by omega⟩ []

/-- Recognize the two literal terminal placements. -/
def terminalFactorTwo? : MarkedRow n L data hn →
    Option (TerminalFactorTwo n L data hn)
  | .marked [] rho k [v] =>
      if hk : k.val = n + 1 then
        some ⟨rho, v, .relationLeft⟩
      else none
  | .marked [v] rho k [] =>
      if hk : k.val = n + 1 then
        some ⟨rho, v, .relationRight⟩
      else none
  | _ => none

@[simp]
theorem terminalFactorTwo?_row (c : TerminalFactorTwo n L data hn) :
    terminalFactorTwo? n L data hn c.row = some c := by
  rcases c with ⟨rho, factor, placement⟩
  cases placement <;>
    simp [TerminalFactorTwo.row, terminalFactorTwo?]

def terminalFactorTwoPart (r : MarkedRow n L data hn) :
    TerminalFactorTwo n L data hn →₀ ℤ :=
  match terminalFactorTwo? n L data hn r with
  | none => 0
  | some c => Finsupp.single c 1

/-- The signed terminal factor-two list of the complete governing
expression. -/
def GoverningWitness.closedSquareTerminal {a : L}
    (w : GoverningWitness n L data a) :
    TerminalFactorTwo n L data hn →₀ ℤ :=
  (GoverningWitness.closedSquareFrontier n L data hn w).sum
    (fun r z ↦ z • terminalFactorTwoPart n L data hn r)

/-! ## Reachability and exhaustion of marked leaves -/

/-- Exact shape invariant of every row below an initial top-marked PBW row.
Once a mark has been truncated it is already at the right edge and still has
at least three total factors. -/
def ClosedSquareReachable : MarkedRow n L data hn → Prop
  | .ordinary _ => True
  | .marked left _ k right =>
      k.val = n + 1 ∨
        (right = [] ∧ 3 ≤ left.length + right.length + 1)

/-- Every nonzero initial row has the top mark and hence satisfies the
collector's reachability invariant. -/
theorem GoverningWitness.closedSquareInitial_reachable_of_ne {a : L}
    (w : GoverningWitness n L data a) (r : MarkedRow n L data hn)
    (hr : GoverningWitness.closedSquareInitial n L data hn w r ≠ 0) :
    ClosedSquareReachable n L data hn r := by
  classical
  by_contra hreachable
  apply hr
  rw [GoverningWitness.closedSquareInitial, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro p hp
  change w.relationCoefficients p *
      markedRowsOfRightFactor n L data hn p.1 p.2 r = 0
  apply mul_eq_zero_of_right
  rw [markedRowsOfRightFactor, Finsupp.sum_apply]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro e he
  change Finsupp.single
      (.marked [] p.1 ⟨n + 1, by omega⟩
        (exponentWord n L data hn e))
      (((adaptedWeightedBasis n L data hn).pbwEquiv.symm p.2) e) r = 0
  by_cases hrow : r = .marked [] p.1 ⟨n + 1, by omega⟩
      (exponentWord n L data hn e)
  · subst r
    exact (hreachable (Or.inl rfl)).elim
  · rw [Finsupp.single_apply]
    split
    · rename_i heq
      exact (hrow heq.symm).elim
    · rfl

theorem closedSquareExpansion_preserves_reachable
    {r : MarkedRow n L data hn}
    {qs : List (ℤ × MarkedRow n L data hn)}
    (hr : ClosedSquareReachable n L data hn r)
    (h : closedSquareExpansion n L data hn r = some qs) :
    ∀ q ∈ qs, ClosedSquareReachable n L data hn q.2 := by
  classical
  cases r with
  | ordinary word =>
      simp only [closedSquareExpansion] at h
      split at h
      · contradiction
      · rw [Option.some.injEq] at h
        subst qs
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · trivial
        · rw [ordinaryCorrection, List.mem_map] at hq
          obtain ⟨q, hq, rfl⟩ := hq
          trivial
  | marked left rho k right =>
      by_cases hfactorOne : left = [] ∧ right = []
      · simp [closedSquareExpansion, hfactorOne] at h
      by_cases hfactorTwo : left.length + right.length + 1 = 2
      · simp [closedSquareExpansion, hfactorOne, hfactorTwo] at h
      cases right with
      | cons v rest =>
          have htop : k.val = n + 1 := by
            rcases hr with htop | hr
            · exact htop
            · simp at hr
          simp [closedSquareExpansion, hfactorOne, hfactorTwo, htop] at h
          rcases h with ⟨_, rfl⟩
          intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact Or.inl htop
          · exact Or.inl htop
      | nil =>
          by_cases hk : k.val = 0
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hk] at h
            rcases h with ⟨_, _, rfl⟩
            simp
          · simp [closedSquareExpansion, hfactorOne, hfactorTwo, hk] at h
            rcases h with ⟨_, _, hqs⟩
            rw [← hqs]
            intro q hq
            simp only [List.mem_cons] at hq
            rcases hq with rfl | hq
            · right
              refine ⟨rfl, ?_⟩
              simp only [List.length_nil, add_zero]
              have hleft : 0 < left.length := by
                apply Nat.pos_of_ne_zero
                intro hzero
                apply hfactorOne
                exact ⟨List.eq_nil_of_length_eq_zero hzero, rfl⟩
              omega
            · rw [List.mem_map] at hq
              obtain ⟨q, hq, rfl⟩ := hq
              trivial

/-- Reachability is inherited by every nonzero terminal coefficient of the
deterministic collector.  This is the precise provenance statement needed
when the PBW symbol is read from the final frontier. -/
theorem closedSquare_reachable_of_normalForm_apply_ne_zero
    (r : MarkedRow n L data hn)
    (hr : ClosedSquareReachable n L data hn r)
    {q : MarkedRow n L data hn}
    (hq : (closedSquareCollector n L data hn).normalForm r q ≠ 0) :
    ClosedSquareReachable n L data hn q :=
  LieRings.DegreeFive.FiniteTaggedCollector.invariant_of_normalForm_apply_ne_zero
    (closedSquareCollector n L data hn)
    (ClosedSquareReachable n L data hn)
    (fun hexpand hreachable ↦
      closedSquareExpansion_preserves_reachable n L data hn
        hreachable hexpand)
    hr hq

/-- Reachability survives the finite linear combination defining the complete
frontier, even though equal terminal rows may cancel. -/
theorem GoverningWitness.closedSquareFrontier_reachable_of_ne {a : L}
    (w : GoverningWitness n L data a) (r : MarkedRow n L data hn)
    (hr : GoverningWitness.closedSquareFrontier n L data hn w r ≠ 0) :
    ClosedSquareReachable n L data hn r := by
  classical
  by_contra hreachable
  apply hr
  rw [GoverningWitness.closedSquareFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro root hroot
  change (GoverningWitness.closedSquareInitial n L data hn w) root *
      (closedSquareCollector n L data hn).normalForm root r = 0
  by_cases hrootCoeff :
      (GoverningWitness.closedSquareInitial n L data hn w) root = 0
  · rw [hrootCoeff, zero_mul]
  · have hrootReach := w.closedSquareInitial_reachable_of_ne
      n L data hn root hrootCoeff
    have hnormal : (closedSquareCollector n L data hn).normalForm root r = 0 := by
      by_contra hnormal
      exact hreachable
        (closedSquare_reachable_of_normalForm_apply_ne_zero
          n L data hn root hrootReach hnormal)
    rw [hnormal, mul_zero]

/-- Every nonzero coefficient of the complete frontier is terminal for the
deterministic collector. -/
theorem GoverningWitness.closedSquareFrontier_terminal_of_ne {a : L}
    (w : GoverningWitness n L data a) (r : MarkedRow n L data hn)
    (hr : GoverningWitness.closedSquareFrontier n L data hn w r ≠ 0) :
    closedSquareExpansion n L data hn r = none := by
  by_contra hnonterminal
  apply hr
  rw [GoverningWitness.closedSquareFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro root hroot
  change (GoverningWitness.closedSquareInitial n L data hn w) root *
      (closedSquareCollector n L data hn).normalForm root r = 0
  rw [(closedSquareCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
    root r hnonterminal, mul_zero]

/-- A reachable marked terminal row is either a whole one-factor relation or
one of the two retained factor-two placements. -/
theorem reachable_terminal_marked
    (left : List (AdaptedIndex n L data hn))
    (rho : Relations n L data) (k : Fin (n + 2))
    (right : List (AdaptedIndex n L data hn))
    (hr : ClosedSquareReachable n L data hn (.marked left rho k right))
    (ht : closedSquareExpansion n L data hn (.marked left rho k right) = none) :
    (left = [] ∧ right = [] ∧ k.val = n + 1) ∨
      ∃ c : TerminalFactorTwo n L data hn,
        c.row = .marked left rho k right := by
  classical
  by_cases hfactorOne : left = [] ∧ right = []
  · left
    refine ⟨hfactorOne.1, hfactorOne.2, ?_⟩
    rcases hr with htop | hr
    · exact htop
    · simp [hfactorOne.1, hfactorOne.2] at hr
  by_cases hfactorTwo : left.length + right.length + 1 = 2
  · right
    have htop : k.val = n + 1 := by
      rcases hr with htop | hr
      · exact htop
      · rcases hr with ⟨_, hthree⟩
        omega
    have hlr : (left = [] ∧ ∃ v, right = [v]) ∨
        (∃ v, left = [v]) ∧ right = [] := by
      have hlen : left.length + right.length = 1 := by omega
      rcases left with _ | ⟨v, vs⟩
      · left
        refine ⟨rfl, ?_⟩
        rcases right with _ | ⟨w, ws⟩
        · simp at hlen
        · refine ⟨w, ?_⟩
          simp only [List.length_cons, List.length_nil, zero_add] at hlen
          have : ws = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst ws
          rfl
      · right
        have hvs : vs = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp only [List.length_cons] at hlen
          omega
        subst vs
        refine ⟨⟨v, rfl⟩, ?_⟩
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons, List.length_nil] at hlen
        omega
    rcases hlr with ⟨rfl, v, rfl⟩ | ⟨⟨v, rfl⟩, rfl⟩
    · refine ⟨⟨rho, v, .relationLeft⟩, ?_⟩
      simp [TerminalFactorTwo.row, Fin.ext_iff, htop]
    · refine ⟨⟨rho, v, .relationRight⟩, ?_⟩
      simp [TerminalFactorTwo.row, Fin.ext_iff, htop]
  · exfalso
    rcases hr with htop | hr
    · cases right with
      | cons v rest =>
          unfold closedSquareExpansion at ht
          simp [hfactorOne, hfactorTwo, htop] at ht
          apply hfactorTwo
          simp only [List.length_cons]
          omega
      | nil =>
          have hk : k.val ≠ 0 := by omega
          unfold closedSquareExpansion at ht
          simp [hfactorOne, hfactorTwo, hk] at ht
          have hleft : left ≠ [] := by
            intro hleft
            exact hfactorOne ⟨hleft, rfl⟩
          have hlen := ht hleft
          apply hfactorTwo
          simp only [List.length_nil]
          omega
    · rcases hr with ⟨hright, hthree⟩
      subst right
      by_cases hk : k.val = 0
      · unfold closedSquareExpansion at ht
        simp [hfactorOne, hfactorTwo, hk] at ht
        have hleft : left ≠ [] := by
          intro hleft
          exact hfactorOne ⟨hleft, rfl⟩
        have hlen := ht hleft
        simp only [List.length_nil] at hthree
        omega
      · unfold closedSquareExpansion at ht
        simp [hfactorOne, hfactorTwo, hk] at ht
        have hleft : left ≠ [] := by
          intro hleft
          exact hfactorOne ⟨hleft, rfl⟩
        have hlen := ht hleft
        simp only [List.length_nil] at hthree
        omega

/-! ## The provenance-preserving transfer--truncation square

The collector above is useful for PBW calculations, but its ordinary branch
forgets which full relation produced a homogeneous component.  The closed
square must retain that information until the transfer correction has met the
matching truncation correction.  The following second, deliberately smaller,
collector is the literal marked/component square from the manuscript.  It has
no ordinary constructor: components are moved back across the factors on
their left while their root relation and nested commutator context remain
visible in the type.
-/

/-- A nested right-bracket context.  Applying it to a full relation again
gives a full relation; applying it to one homogeneous component gives the
ordinary component carried by the corresponding internal edge. -/
inductive RelationContext (n : ℕ) (L : Type u) [LieRing L] [Finite L]
    (data : CyclicTopData n L) (hn : 2 ≤ n)
  | hole
  | lieRight (context : RelationContext n L data hn)
      (factor : AdaptedIndex n L data hn)

noncomputable instance : DecidableEq (RelationContext n L data hn) :=
  Classical.decEq _

namespace RelationContext

/-- Manuscript weight added by the factors in a context. -/
def weight : RelationContext n L data hn → ℕ
  | .hole => 0
  | .lieRight c x =>
      weight c + (adaptedWeightedBasis n L data hn).weight x

/-- The integral linear operation represented by a context. -/
def apply : RelationContext n L data hn →
    FreeModel n L →ₗ[ℤ] FreeModel n L
  | .hole => LinearMap.id
  | .lieRight c x =>
      { toFun := fun z ↦ ⁅apply c z,
          (adaptedWeightedBasis n L data hn).basis x⁆
        map_add' := by intro z w; rw [map_add, add_lie]
        map_smul' := by intro a z; rw [map_smul, smul_lie]; rfl }

@[simp] theorem apply_hole (z : FreeModel n L) :
    RelationContext.apply n L data hn
      (hole : RelationContext n L data hn) z = z := rfl

@[simp] theorem apply_lieRight
    (c : RelationContext n L data hn)
    (x : AdaptedIndex n L data hn) (z : FreeModel n L) :
    RelationContext.apply n L data hn
        (RelationContext.lieRight c x) z =
      ⁅RelationContext.apply n L data hn c z,
        (adaptedWeightedBasis n L data hn).basis x⁆ := rfl

/-- Applying a bracket context to one homogeneous piece remains homogeneous
in the sum of the manuscript weights.  The assertion is phrased directly on
coordinates, so it also covers the case where the requested weight lies past
the nilpotence cutoff (when the result is zero). -/
theorem apply_weightIncl_apply_eq_zero_of_ne
    (c : RelationContext n L data hn)
    (s : ℕ) (hs : s < n + 1)
    (z : FreeMetabelian.Piece (Generator L) s)
    (i : Fin (n + 1))
    (hne : i.val ≠ s + RelationContext.weight n L data hn c) :
    RelationContext.apply n L data hn c
        (FreeMetabelian.Free.weightIncl s hs z) i = 0 := by
  induction c generalizing i with
  | hole =>
      exact FreeMetabelian.Free.incl_apply_of_ne
        ⟨s, hs⟩ i (by
          intro h
          apply hne
          simpa [RelationContext.weight] using congrArg Fin.val h) z
  | lieRight c x ih =>
      let r := s + RelationContext.weight n L data hn c
      by_cases hr : r < n + 1
      · have hhom : RelationContext.apply n L data hn c
            (FreeMetabelian.Free.weightIncl s hs z) =
          FreeMetabelian.Free.weightIncl r hr
            (FreeMetabelian.Free.weightProject r hr
              (RelationContext.apply n L data hn c
                (FreeMetabelian.Free.weightIncl s hs z))) := by
          funext j
          by_cases hj : j.val = r
          · have hjeq : j = ⟨r, hr⟩ := Fin.ext hj
            subst j
            exact (FreeMetabelian.Free.incl_apply_same
              (⟨r, hr⟩ : Fin (n + 1)) _).symm
          · rw [ih j hj]
            exact (FreeMetabelian.Free.incl_apply_of_ne
              ⟨r, hr⟩ j (by
                intro h
                exact hj (congrArg Fin.val h)) _).symm
        have hbasis : (adaptedWeightedBasis n L data hn).basis x =
            FreeMetabelian.Free.weightIncl x.1.val x.1.isLt
              (pieceAdaptedBasis n L data hn x.1 x.2) := by
          exact adaptedBasis_apply n L data hn x
        rw [RelationContext.apply_lieRight, hhom, hbasis]
        exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
          r x.1.val hr x.1.isLt
          (FreeMetabelian.Free.weightProject r hr
            (RelationContext.apply n L data hn c
              (FreeMetabelian.Free.weightIncl s hs z)))
          (pieceAdaptedBasis n L data hn x.1 x.2) i (by
            simpa [r, RelationContext.weight, adaptedWeightedBasis,
              add_assoc] using hne)
      · have hzero : RelationContext.apply n L data hn c
            (FreeMetabelian.Free.weightIncl s hs z) = 0 := by
          funext j
          exact ih j (by omega)
        rw [RelationContext.apply_lieRight, hzero, zero_lie]
        rfl

/-- The genuine full relation obtained by filling the context hole. -/
def relation (c : RelationContext n L data hn)
    (rho : Relations n L data) : Relations n L data :=
  ⟨RelationContext.apply n L data hn c rho.1, by
    induction c with
    | hole => exact rho.property
    | lieRight c x ih =>
        rw [RelationContext.apply_lieRight]
        rw [← lie_skew]
        exact (Relations n L data).neg_mem
          ((Relations n L data).lie_mem ih)⟩

@[simp] theorem relation_coe (c : RelationContext n L data hn)
    (rho : Relations n L data) :
    (RelationContext.relation n L data hn c rho : FreeModel n L) =
      RelationContext.apply n L data hn c rho.1 := rfl

/-- The marked prefix, before the context is filled. -/
def markedPrefix (c : RelationContext n L data hn)
    (rho : Relations n L data) (k : Fin (n + 2)) : FreeModel n L :=
  RelationContext.apply n L data hn c
    (rowTruncation n L k.val (by omega) rho.1)

/-- The exact contextual homogeneous component exposed when the root mark is
lowered from `k` to `k-1`.  At mark zero it is defined to be zero. -/
def component (c : RelationContext n L data hn)
    (rho : Relations n L data) (k : Fin (n + 2)) : FreeModel n L :=
  if hk : k.val = 0 then 0 else
    RelationContext.apply n L data hn c
      (FreeMetabelian.Free.weightIncl (k.val - 1) (by omega)
      (FreeMetabelian.Free.weightProject (k.val - 1) (by omega) rho.1))

/-- The contextual component exposed at a positive mark is supported in its
single active manuscript weight. -/
theorem component_apply_eq_zero_of_ne
    (c : RelationContext n L data hn)
    (rho : Relations n L data) (k : Fin (n + 2))
    (hk : 0 < k.val) (i : Fin (n + 1))
    (hne : i.val + 1 ≠
      k.val + RelationContext.weight n L data hn c) :
    RelationContext.component n L data hn c rho k i = 0 := by
  rw [RelationContext.component, dif_neg (by omega)]
  apply RelationContext.apply_weightIncl_apply_eq_zero_of_ne
  omega

@[simp] theorem component_zero (c : RelationContext n L data hn)
    (rho : Relations n L data) (k : Fin (n + 2)) (hk : k.val = 0) :
    RelationContext.component n L data hn c rho k = 0 := by
  simp [component, hk]

theorem prefix_step (c : RelationContext n L data hn)
    (rho : Relations n L data) (k : Fin (n + 2)) (hk : 0 < k.val) :
    RelationContext.markedPrefix n L data hn c rho k =
      RelationContext.markedPrefix n L data hn c rho
          ⟨k.val - 1, by omega⟩ +
        RelationContext.component n L data hn c rho k := by
  have hrow := rowTruncation_succ n L (k.val - 1) (by omega) rho.1
  have hsucc : k.val - 1 + 1 = k.val := by omega
  have hrow' :
      rowTruncation n L k.val (by omega) rho.1 =
        rowTruncation n L (k.val - 1) (by omega) rho.1 +
          FreeMetabelian.Free.weightIncl (k.val - 1) (by omega)
            (FreeMetabelian.Free.weightProject (k.val - 1) (by omega)
              rho.1) := by
    simpa only [hsucc] using hrow
  rw [markedPrefix, markedPrefix, component, dif_neg (by omega), hrow', map_add]

@[simp] theorem component_lieRight
    (c : RelationContext n L data hn)
    (x : AdaptedIndex n L data hn) (rho : Relations n L data)
    (k : Fin (n + 2)) :
    RelationContext.component n L data hn
        (RelationContext.lieRight c x) rho k =
      ⁅RelationContext.component n L data hn c rho k,
        (adaptedWeightedBasis n L data hn).basis x⁆ := by
  by_cases hk : k.val = 0
  · simp [component, hk]
  · simp only [component, dif_neg hk, RelationContext.apply_lieRight]

/-- Bracketing on the right by a homogeneous factor of zero-based weight
`t` raises the coordinate-tail bound by `t+1`. -/
theorem bracket_weightIncl_right_mem_tail
    (z : FreeModel n L) (k t : ℕ) (ht : t < n + 1)
    (hz : z ∈ FreeMetabelian.Free.tail k)
    (x : FreeMetabelian.Piece (Generator L) t) :
    ⁅z, FreeMetabelian.Free.weightIncl t ht x⁆ ∈
      FreeMetabelian.Free.tail (k + t + 1) := by
  rw [FreeMetabelian.Free.mem_tail_iff]
  intro i hi
  have hsum := FreeMetabelian.Free.sum_incl_project z
  have hbr := congrArg
    (fun w : FreeModel n L ↦
      ⁅w, FreeMetabelian.Free.weightIncl t ht x⁆) hsum
  simp only [sum_lie] at hbr
  have happly := congrFun hbr i
  rw [Finset.sum_apply] at happly
  rw [← happly]
  apply Finset.sum_eq_zero
  intro s hs
  by_cases hsk : s.val < k
  · have hzcoord := hz s hsk
    rw [FreeMetabelian.Free.project_apply, hzcoord, map_zero]
    simp
  · exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
      s.val t s.isLt ht (FreeMetabelian.Free.weightProject s.val s.isLt z)
      x i (by omega)

/-- A context raises the tail bound by its full manuscript weight. -/
theorem apply_mem_tail (c : RelationContext n L data hn)
    (z : FreeModel n L) (k : ℕ)
    (hz : z ∈ FreeMetabelian.Free.tail k) :
    RelationContext.apply n L data hn c z ∈
      FreeMetabelian.Free.tail
        (k + RelationContext.weight n L data hn c) := by
  induction c generalizing k with
  | hole => simpa [RelationContext.apply, RelationContext.weight] using hz
  | lieRight c x ih =>
      have hc := ih k hz
      have hb := bracket_weightIncl_right_mem_tail n L
        (RelationContext.apply n L data hn c z)
        (k + RelationContext.weight n L data hn c) x.1.val x.1.isLt hc
        (pieceAdaptedBasis n L data hn x.1 x.2)
      simpa [RelationContext.apply, RelationContext.weight,
        adaptedWeightedBasis, adaptedBasis_apply, Nat.add_assoc] using hb

/-- Removing the first `k` manuscript weights leaves the coordinate tail
starting at `k`. -/
theorem sub_rowTruncation_mem_tail (z : FreeModel n L)
    (k : ℕ) (hk : k ≤ n + 1) :
    z - rowTruncation n L k hk z ∈ FreeMetabelian.Free.tail k := by
  rw [FreeMetabelian.Free.mem_tail_iff]
  intro i hi
  simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
    FreeMetabelian.Free.projectPrefix, hi]

/-- At its active weight, the contextual marked prefix and the contextual
full relation have the same projection. -/
theorem projectPrefix_relation_eq_markedPrefix_of_active
    (s : ℕ) (hs : s ≤ n + 1)
    (c : RelationContext n L data hn) (rho : Relations n L data)
    (k : Fin (n + 2))
    (hactive : k.val + RelationContext.weight n L data hn c = s) :
    FreeMetabelian.Free.projectPrefix s hs
        (RelationContext.relation n L data hn c rho : FreeModel n L) =
      FreeMetabelian.Free.projectPrefix s hs
        (RelationContext.markedPrefix n L data hn c rho k) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  have htail0 := sub_rowTruncation_mem_tail n L rho.1 k.val (by omega)
  have htail := apply_mem_tail n L data hn c
    (rho.1 - rowTruncation n L k.val (by omega) rho.1) k.val htail0
  have htail' : RelationContext.apply n L data hn c
      (rho.1 - rowTruncation n L k.val (by omega) rho.1) ∈
        FreeMetabelian.Free.tail s := by simpa [hactive] using htail
  apply funext
  intro i
  change (FreeMetabelian.Free.projectPrefix s hs
      (RelationContext.apply n L data hn c rho.1 -
        RelationContext.apply n L data hn c
          (rowTruncation n L k.val (by omega) rho.1))) i = 0
  rw [← map_sub]
  change RelationContext.apply n L data hn c
      (rho.1 - rowTruncation n L k.val (by omega) rho.1)
        ⟨i.val, i.isLt.trans_le hs⟩ = 0
  exact htail' ⟨i.val, i.isLt.trans_le hs⟩ i.isLt

/-- The terminal factor-two specialization used by the quadratic wall. -/
theorem projectPrefix_relation_eq_markedPrefix
    (c : RelationContext n L data hn) (rho : Relations n L data)
    (k : Fin (n + 2))
    (hactive : k.val + RelationContext.weight n L data hn c = n) :
    FreeMetabelian.Free.projectPrefix n (by omega)
        (RelationContext.relation n L data hn c rho : FreeModel n L) =
      FreeMetabelian.Free.projectPrefix n (by omega)
        (RelationContext.markedPrefix n L data hn c rho k) :=
  projectPrefix_relation_eq_markedPrefix_of_active n L data hn n (by omega)
    c rho k hactive

/-- At active weight `n+1` no contextual tail survives in the truncated free
model, so the marked prefix is literally the full contextual relation. -/
theorem relation_eq_markedPrefix_of_active_top
    (c : RelationContext n L data hn) (rho : Relations n L data)
    (k : Fin (n + 2))
    (hactive : k.val + RelationContext.weight n L data hn c = n + 1) :
    (RelationContext.relation n L data hn c rho : FreeModel n L) =
      RelationContext.markedPrefix n L data hn c rho k := by
  apply sub_eq_zero.mp
  change RelationContext.apply n L data hn c rho.1 -
      RelationContext.apply n L data hn c
        (rowTruncation n L k.val (by omega) rho.1) = 0
  rw [← map_sub]
  have htail0 := sub_rowTruncation_mem_tail n L rho.1 k.val (by omega)
  have htail := apply_mem_tail n L data hn c
    (rho.1 - rowTruncation n L k.val (by omega) rho.1) k.val htail0
  have htail' : RelationContext.apply n L data hn c
      (rho.1 - rowTruncation n L k.val (by omega) rho.1) ∈
        FreeMetabelian.Free.tail (n + 1) := by simpa [hactive] using htail
  have hz : RelationContext.apply n L data hn c
      (rho.1 - rowTruncation n L k.val (by omega) rho.1) = 0 := by
    have hbot := FreeMetabelian.Free.tail_cutoff_eq_bot
      (X := Generator L) (c := n + 1)
    rw [hbot] at htail'
    simpa using htail'
  simpa [RelationContext.relation, RelationContext.markedPrefix,
    map_sub] using hz

end RelationContext

/-- Rows of the provenance-preserving square.  A marked row contains the
contextual truncation of a full relation.  A component row contains its exact
homogeneous edge, but still remembers the same root and context. -/
inductive ProvenancedRow
  | marked (root : Relations n L data)
      (context : RelationContext n L data hn) (mark : Fin (n + 2))
      (left right : List (AdaptedIndex n L data hn))
  | component (root : Relations n L data)
      (context : RelationContext n L data hn) (mark : Fin (n + 2))
      (left right : List (AdaptedIndex n L data hn))

noncomputable instance : DecidableEq (ProvenancedRow n L data hn) :=
  Classical.decEq _

namespace ProvenancedRow

def value : ProvenancedRow n L data hn → UEA ℤ (FreeModel n L)
  | .marked rho c k left right =>
      MarkedRow.basisWord n L data hn left *
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.markedPrefix n L data hn c rho k) *
        MarkedRow.basisWord n L data hn right
  | .component rho c k left right =>
      MarkedRow.basisWord n L data hn left *
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.component n L data hn c rho k) *
        MarkedRow.basisWord n L data hn right

def activeWeight : ProvenancedRow n L data hn → ℕ
  | .marked _ c k _ _ | .component _ c k _ _ =>
      k.val + RelationContext.weight n L data hn c

end ProvenancedRow

/-- The two external stopping walls.  The first is the complete primitive
edge; the second is the weight-`n` relation edge with one remaining factor. -/
def provenancedWall (c : RelationContext n L data hn) (k : Fin (n + 2))
    (left : List (AdaptedIndex n L data hn)) : Bool :=
  match left with
  | [] => decide (k.val + RelationContext.weight n L data hn c = n + 1)
  | [_] => decide (k.val + RelationContext.weight n L data hn c = n)
  | _ => false

/-- Literal marked/component rewrite.  Transfer is completed before
truncation.  A component moves back across the last factor on its left; its
negative contextual bracket is syntactically the same row as the positive
component later emitted by the corresponding marked correction. -/
noncomputable def provenancedExpansion : ProvenancedRow n L data hn →
    Option (List (ℤ × ProvenancedRow n L data hn))
  | .component rho c k left right =>
      match hleft : left.reverse with
      | [] => none
      | x :: leftRev =>
          some [(1, .component rho c k leftRev.reverse (x :: right)),
            (-1, .component rho
              (RelationContext.lieRight c x) k
                leftRev.reverse right)]
  | .marked rho c k left (x :: right) =>
      some [(1, .marked rho c k (left ++ [x]) right),
        (1, .marked rho (RelationContext.lieRight c x)
          k left right)]
  | .marked rho c k left [] =>
      if hk : k.val = 0 then some []
      else if provenancedWall n L data hn c k left then none
      else
        let k' : Fin (n + 2) := ⟨k.val - 1, by omega⟩
        some [(1, .marked rho c k' left []),
          (1, .component rho c k left [])]

/-- The exact terminating measure of the contextual square. -/
def provenancedMeasure : ProvenancedRow n L data hn → RowMeasure
  | .marked _ _ k _ right => (1, right.length, k.val)
  | .component _ _ _ left _ => (0, left.length, 0)

theorem provenancedExpansion_decreases
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs) :
    ∀ q ∈ qs, rowMeasureLt (provenancedMeasure n L data hn q.2)
      (provenancedMeasure n L data hn r) := by
  classical
  intro q hq
  cases r with
  | component rho c k left right =>
      simp only [provenancedExpansion] at h
      split at h
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at h
        subst qs
        have hleftEq : left = leftRev.reverse ++ [x] := by
          have hr := congrArg List.reverse hleft
          simpa using hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;>
          unfold rowMeasureLt provenancedMeasure <;>
          apply Prod.Lex.right <;> apply Prod.Lex.left <;>
          simp [hleftEq]
  | marked rho c k left right =>
      cases right with
      | cons x right =>
          simp only [provenancedExpansion] at h
          rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl <;>
            unfold rowMeasureLt provenancedMeasure <;>
            apply Prod.Lex.right <;> apply Prod.Lex.left <;> simp
      | nil =>
          simp only [provenancedExpansion] at h
          split at h
          · rw [Option.some.injEq] at h
            subst qs
            simp at hq
          · split at h
            · contradiction
            · rw [Option.some.injEq] at h
              subst qs
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
              rcases hq with rfl | rfl
              · unfold rowMeasureLt provenancedMeasure
                apply Prod.Lex.right
                apply Prod.Lex.right
                change k.val - 1 < k.val
                omega
              · unfold rowMeasureLt provenancedMeasure
                apply Prod.Lex.left
                omega

theorem provenancedExpansion_preserves
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value).sum = r.value := by
  classical
  cases r with
  | component rho c k left right =>
      simp only [provenancedExpansion] at h
      split at h
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at h
        subst qs
        have hleftEq : left = leftRev.reverse ++ [x] := by
          have hr := congrArg List.reverse hleft
          simpa using hr
        simp only [List.map_cons, List.map_singleton, List.map_nil,
          List.sum_cons, List.sum_singleton, List.sum_nil, one_smul,
          neg_one_smul, add_zero]
        simp only [ProvenancedRow.value, RelationContext.component_lieRight]
        rw [hleftEq]
        simp only [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_append, List.map_singleton,
          List.prod_append, List.prod_singleton]
        have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
          (FreeModel n L) (RelationContext.component n L data hn c rho k)
            ((adaptedWeightedBasis n L data hn).basis x)
        rw [← sub_eq_add_neg]
        calc
          _ = MarkedRow.basisWord n L data hn leftRev.reverse *
              (UniversalEnvelopingAlgebra.ι ℤ
                    (RelationContext.component n L data hn c rho k) *
                  UniversalEnvelopingAlgebra.ι ℤ
                    ((adaptedWeightedBasis n L data hn).basis x) -
                UniversalEnvelopingAlgebra.ι ℤ
                  ⁅RelationContext.component n L data hn c rho k,
                    (adaptedWeightedBasis n L data hn).basis x⁆) *
              MarkedRow.basisWord n L data hn right := by noncomm_ring
          _ = MarkedRow.basisWord n L data hn leftRev.reverse *
              (UniversalEnvelopingAlgebra.ι ℤ
                    ((adaptedWeightedBasis n L data hn).basis x) *
                UniversalEnvelopingAlgebra.ι ℤ
                  (RelationContext.component n L data hn c rho k)) *
              MarkedRow.basisWord n L data hn right := by
                rw [hswap]
                noncomm_ring
          _ = _ := by noncomm_ring
  | marked rho c k left right =>
      cases right with
      | cons x right =>
          simp only [provenancedExpansion] at h
          rw [Option.some.injEq] at h
          subst qs
          simp only [List.map_cons, List.map_singleton, List.map_nil,
            List.sum_cons, List.sum_singleton, List.sum_nil, one_smul,
            add_zero]
          simp only [ProvenancedRow.value, RelationContext.markedPrefix,
            RelationContext.apply_lieRight]
          let a := RelationContext.apply n L data hn c
            (rowTruncation n L k.val (by omega) rho.1)
          let xv := (adaptedWeightedBasis n L data hn).basis x
          have hleftWord : MarkedRow.basisWord n L data hn (left ++ [x]) =
              MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ xv := by
            simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word, List.map_append, xv]
          have hrightWord : MarkedRow.basisWord n L data hn (x :: right) =
              UniversalEnvelopingAlgebra.ι ℤ xv *
                MarkedRow.basisWord n L data hn right := by
            simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word, xv]
          rw [hleftWord, hrightWord]
          change
            (MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ xv) *
                UniversalEnvelopingAlgebra.ι ℤ a *
                MarkedRow.basisWord n L data hn right +
              MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ ⁅a, xv⁆ *
                MarkedRow.basisWord n L data hn right =
              MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ a *
                (UniversalEnvelopingAlgebra.ι ℤ xv *
                  MarkedRow.basisWord n L data hn right)
          have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
            (FreeModel n L) a xv
          calc
            _ = MarkedRow.basisWord n L data hn left *
                (UniversalEnvelopingAlgebra.ι ℤ xv *
                    UniversalEnvelopingAlgebra.ι ℤ a +
                  UniversalEnvelopingAlgebra.ι ℤ ⁅a, xv⁆) *
                MarkedRow.basisWord n L data hn right := by
                  noncomm_ring
            _ = MarkedRow.basisWord n L data hn left *
                (UniversalEnvelopingAlgebra.ι ℤ a *
                  UniversalEnvelopingAlgebra.ι ℤ xv) *
                MarkedRow.basisWord n L data hn right := by rw [← hswap]
            _ = _ := by noncomm_ring
      | nil =>
          simp only [provenancedExpansion] at h
          split at h
          · rename_i hk
            rw [Option.some.injEq] at h
            subst qs
            let k0 : Fin (n + 2) := ⟨0, by omega⟩
            have hk' : k = k0 := Fin.ext hk
            rw [hk']
            have hz : RelationContext.markedPrefix n L data hn c rho
                k0 = 0 := by
              rw [RelationContext.markedPrefix,
                rowTruncation_zero n L hn rho.1, map_zero]
            change 0 = MarkedRow.basisWord n L data hn left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (RelationContext.markedPrefix n L data hn c rho k0) *
                MarkedRow.basisWord n L data hn []
            rw [hz, map_zero]
            simp
          · split at h
            · contradiction
            · rename_i hk hwall
              rw [Option.some.injEq] at h
              subst qs
              simp only [List.map_cons, List.map_singleton, List.map_nil,
                List.sum_cons, List.sum_singleton, List.sum_nil, one_smul,
                add_zero]
              simp only [ProvenancedRow.value]
              rw [RelationContext.prefix_step n L data hn c rho k
                (Nat.pos_of_ne_zero hk), map_add]
              simp only [MarkedRow.basisWord, LieRings.PBW.basisWord,
                LieRings.PBW.word, List.map_nil, List.prod_nil, mul_one]
              noncomm_ring

/-- The finite contextual collector. -/
def provenancedCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (ProvenancedRow n L data hn) (UEA ℤ (FreeModel n L)) where
  relation x y := rowMeasureLt (provenancedMeasure n L data hn x)
    (provenancedMeasure n L data hn y)
  wellFounded := InvImage.wf (provenancedMeasure n L data hn)
    rowMeasureLt_wellFounded
  expansion := provenancedExpansion n L data hn
  value := ProvenancedRow.value n L data hn
  decreases := provenancedExpansion_decreases n L data hn
  preserves := provenancedExpansion_preserves n L data hn

theorem provenancedCollector_evaluate (r : ProvenancedRow n L data hn) :
    (provenancedCollector n L data hn).evaluate
        ((provenancedCollector n L data hn).normalForm r) = r.value :=
  LieRings.DegreeFive.FiniteTaggedCollector.evaluate_normalForm _ r

/-- Expand an arbitrary right multiplier into contextual top-marked roots. -/
def provenancedRowsOfRightFactor (rho : Relations n L data)
    (u : UEA ℤ (FreeModel n L)) : ProvenancedRow n L data hn →₀ ℤ :=
  ((adaptedWeightedBasis n L data hn).pbwEquiv.symm u).sum
    (fun e z ↦ Finsupp.single
      (.marked rho .hole ⟨n + 1, by omega⟩ []
        (exponentWord n L data hn e)) z)

theorem evaluate_provenancedRowsOfRightFactor
    (rho : Relations n L data) (u : UEA ℤ (FreeModel n L)) :
    (provenancedCollector n L data hn).evaluate
        (provenancedRowsOfRightFactor n L data hn rho u) =
      UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) * u := by
  classical
  let B := adaptedWeightedBasis n L data hn
  change Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
      (((B.pbwEquiv.symm u).sum fun e z ↦
        Finsupp.single
          (.marked rho .hole ⟨n + 1, by omega⟩ []
            (exponentWord n L data hn e)) z)) = _
  rw [map_finsuppSum]
  simp only [Finsupp.linearCombination_single]
  have hu : (B.pbwEquiv.symm u).sum
      (fun e z ↦ z • LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
        (AdaptedIndex n L data hn) B.basis e) = u := by
    have hsum : (B.pbwEquiv.symm u).sum
        (fun e z ↦ MvPolynomial.monomial e z) = B.pbwEquiv.symm u := by
      simpa only [MvPolynomial.monomial] using
        (Finsupp.sum_single (B.pbwEquiv.symm u))
    calc
      _ = (B.pbwEquiv.symm u).sum
          (fun e z ↦ B.pbwEquiv (MvPolynomial.monomial e z)) := by
        apply Finsupp.sum_congr
        intro e he
        rw [B.pbwEquiv_monomial]
      _ = B.pbwEquiv ((B.pbwEquiv.symm u).sum
          (fun e z ↦ MvPolynomial.monomial e z)) := by rw [map_finsuppSum]
      _ = B.pbwEquiv (B.pbwEquiv.symm u) := by rw [hsum]
      _ = u := B.pbwEquiv.apply_symm_apply u
  calc
    _ = (B.pbwEquiv.symm u).sum (fun e z ↦ z •
        (UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
          LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
            (AdaptedIndex n L data hn) B.basis e)) := by
      apply Finsupp.sum_congr
      intro e he
      congr 1
      simp [ProvenancedRow.value, RelationContext.markedPrefix,
        exponentWord, MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.orderedMonomial, LieRings.PBW.word,
        List.map_map, Function.comp_def, B]
    _ = UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
        (B.pbwEquiv.symm u).sum (fun e z ↦ z •
          LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
            (AdaptedIndex n L data hn) B.basis e) := by
      rw [Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro e he
      rw [mul_smul_comm]
    _ = _ := by rw [hu]

def GoverningWitness.provenancedInitial {a : L}
    (w : GoverningWitness n L data a) : ProvenancedRow n L data hn →₀ ℤ :=
  w.relationCoefficients.sum (fun p z ↦
    z • provenancedRowsOfRightFactor n L data hn p.1 p.2)

theorem GoverningWitness.evaluate_provenancedInitial {a : L}
    (w : GoverningWitness n L data a) :
    (provenancedCollector n L data hn).evaluate
        (GoverningWitness.provenancedInitial n L data hn w) = w.theta := by
  classical
  rw [GoverningWitness.provenancedInitial, map_finsuppSum,
    GoverningWitness.theta]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, evaluate_provenancedRowsOfRightFactor]

def GoverningWitness.provenancedFrontier {a : L}
    (w : GoverningWitness n L data a) : ProvenancedRow n L data hn →₀ ℤ :=
  (GoverningWitness.provenancedInitial n L data hn w).sum (fun r z ↦
    z • (provenancedCollector n L data hn).normalForm r)

theorem GoverningWitness.evaluate_provenancedFrontier {a : L}
    (w : GoverningWitness n L data a) :
    (provenancedCollector n L data hn).evaluate
        (GoverningWitness.provenancedFrontier n L data hn w) = w.theta := by
  classical
  rw [GoverningWitness.provenancedFrontier, map_finsuppSum]
  calc
    _ = (provenancedCollector n L data hn).evaluate
        (GoverningWitness.provenancedInitial n L data hn w) := by
      change (GoverningWitness.provenancedInitial n L data hn w).sum
          (fun r z ↦ (provenancedCollector n L data hn).evaluate
            (z • (provenancedCollector n L data hn).normalForm r)) =
        (GoverningWitness.provenancedInitial n L data hn w).sum
          (fun r z ↦ z • ProvenancedRow.value n L data hn r)
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul, provenancedCollector_evaluate]
    _ = w.theta := GoverningWitness.evaluate_provenancedInitial n L data hn w

/-! ### Signed truncation cells of the contextual square -/

/-- A genuine non-wall truncation occurrence.  The full root relation and
its complete commutator context are retained together with the exact mark. -/
structure ProvenancedCell where
  root : Relations n L data
  context : RelationContext n L data hn
  mark : Fin (n + 2)
  left : List (AdaptedIndex n L data hn)
  mark_pos : 0 < mark.val
  not_wall : provenancedWall n L data hn context mark left = false

noncomputable instance : DecidableEq (ProvenancedCell n L data hn) :=
  Classical.decEq _

def ProvenancedCell.markedRow (c : ProvenancedCell n L data hn) :
    ProvenancedRow n L data hn :=
  .marked c.root c.context c.mark c.left []

def ProvenancedCell.componentRow (c : ProvenancedCell n L data hn) :
    ProvenancedRow n L data hn :=
  .component c.root c.context c.mark c.left []

/-- Recognize exactly the contextual marked-truncation rule. -/
def provenancedCell? : ProvenancedRow n L data hn →
    Option (ProvenancedCell n L data hn)
  | .component _ _ _ _ _ => none
  | .marked rho c k left right =>
      if hr : right = [] then
        if hk : 0 < k.val then
          if hw : provenancedWall n L data hn c k left = false then
            some ⟨rho, c, k, left, hk, hw⟩
          else none
        else none
      else none

private def provenancedTraceStep
    (r : ProvenancedRow n L data hn)
    (rec : ∀ q, (provenancedCollector n L data hn).relation q r →
      ProvenancedCell n L data hn →₀ ℤ) :
    ProvenancedCell n L data hn →₀ ℤ :=
  let here := match provenancedCell? n L data hn r with
    | none => 0
    | some c => Finsupp.single c 1
  match h : (provenancedCollector n L data hn).expansion r with
  | none => here
  | some qs => here + (qs.attach.map fun q ↦
      q.1.1 • rec q.1.2
        ((provenancedCollector n L data hn).decreases h q.1 q.2)).sum

/-- Complete signed truncation trace below one contextual row. -/
def provenancedTrace (r : ProvenancedRow n L data hn) :
    ProvenancedCell n L data hn →₀ ℤ :=
  (provenancedCollector n L data hn).wellFounded.fix
    (provenancedTraceStep n L data hn) r

theorem provenancedTrace_eq (r : ProvenancedRow n L data hn) :
    provenancedTrace n L data hn r =
      provenancedTraceStep n L data hn r
        (fun q _ ↦ provenancedTrace n L data hn q) := by
  rw [provenancedTrace,
    (provenancedCollector n L data hn).wellFounded.fix_eq]
  congr 1

theorem provenancedTrace_eq_of_expansion_none
    (r : ProvenancedRow n L data hn)
    (h : provenancedExpansion n L data hn r = none) :
    provenancedTrace n L data hn r =
      match provenancedCell? n L data hn r with
      | none => 0
      | some c => Finsupp.single c 1 := by
  rw [provenancedTrace_eq]
  unfold provenancedTraceStep
  have h' : (provenancedCollector n L data hn).expansion r = none := h
  cases hc : provenancedCell? n L data hn r <;> simp only [hc]
  all_goals
    split
    · rfl
    · rename_i qs he
      rw [h'] at he
      contradiction

theorem provenancedTrace_eq_of_expansion_some
    (r : ProvenancedRow n L data hn)
    (qs : List (ℤ × ProvenancedRow n L data hn))
    (h : provenancedExpansion n L data hn r = some qs) :
    provenancedTrace n L data hn r =
      (match provenancedCell? n L data hn r with
        | none => 0
        | some c => Finsupp.single c 1) +
      (qs.attach.map fun q ↦ q.1.1 •
        provenancedTrace n L data hn q.1.2).sum := by
  rw [provenancedTrace_eq]
  unfold provenancedTraceStep
  have h' : (provenancedCollector n L data hn).expansion r = some qs := h
  cases hc : provenancedCell? n L data hn r <;> simp only [hc]
  all_goals
    split
    · rename_i he
      rw [h'] at he
      contradiction
    · rename_i qs' he
      have hqs : qs' = qs := by
        rw [h'] at he
        exact Option.some.inj he.symm
      subst qs'
      rfl

def GoverningWitness.provenancedCells {a : L}
    (w : GoverningWitness n L data a) : ProvenancedCell n L data hn →₀ ℤ :=
  (GoverningWitness.provenancedInitial n L data hn w).sum
    (fun r z ↦ z • provenancedTrace n L data hn r)

/-! ### External marked walls -/

/-- A marked one-factor wall at active manuscript weight `n+1`. -/
structure ProvenancedTerminalOne where
  root : Relations n L data
  context : RelationContext n L data hn
  mark : Fin (n + 2)
  active : mark.val + RelationContext.weight n L data hn context = n + 1

noncomputable instance : DecidableEq (ProvenancedTerminalOne n L data hn) :=
  Classical.decEq _

def ProvenancedTerminalOne.row (c : ProvenancedTerminalOne n L data hn) :
    ProvenancedRow n L data hn :=
  .marked c.root c.context c.mark [] []

/-- A marked factor-two wall.  The ordinary factor is literally to the left
of the contextual mark, as prescribed by the transfer direction. -/
structure ProvenancedTerminalTwo where
  root : Relations n L data
  context : RelationContext n L data hn
  mark : Fin (n + 2)
  factor : AdaptedIndex n L data hn
  active : mark.val + RelationContext.weight n L data hn context = n

noncomputable instance : DecidableEq (ProvenancedTerminalTwo n L data hn) :=
  Classical.decEq _

def ProvenancedTerminalTwo.row (c : ProvenancedTerminalTwo n L data hn) :
    ProvenancedRow n L data hn :=
  .marked c.root c.context c.mark [c.factor] []

/-- Read the two external marked wall shapes. -/
def provenancedTerminal? (r : ProvenancedRow n L data hn) :
    Option (ProvenancedTerminalOne n L data hn ⊕
      ProvenancedTerminalTwo n L data hn) :=
  match r with
  | .marked rho c k [] [] =>
      if h : k.val + RelationContext.weight n L data hn c = n + 1 then
        some (.inl ⟨rho, c, k, h⟩)
      else none
  | .marked rho c k [x] [] =>
      if h : k.val + RelationContext.weight n L data hn c = n then
        some (.inr ⟨rho, c, k, x, h⟩)
      else none
  | _ => none

def provenancedTerminalOnePart (r : ProvenancedRow n L data hn) :
    ProvenancedTerminalOne n L data hn →₀ ℤ :=
  match provenancedTerminal? n L data hn r with
  | some (.inl c) => Finsupp.single c 1
  | _ => 0

def provenancedTerminalTwoPart (r : ProvenancedRow n L data hn) :
    ProvenancedTerminalTwo n L data hn →₀ ℤ :=
  match provenancedTerminal? n L data hn r with
  | some (.inr c) => Finsupp.single c 1
  | _ => 0

def GoverningWitness.provenancedTerminalOne {a : L}
    (w : GoverningWitness n L data a) :
    ProvenancedTerminalOne n L data hn →₀ ℤ :=
  (GoverningWitness.provenancedFrontier n L data hn w).sum
    (fun r z ↦ z • provenancedTerminalOnePart n L data hn r)

def GoverningWitness.provenancedTerminalTwo {a : L}
    (w : GoverningWitness n L data a) :
    ProvenancedTerminalTwo n L data hn →₀ ℤ :=
  (GoverningWitness.provenancedFrontier n L data hn w).sum
    (fun r z ↦ z • provenancedTerminalTwoPart n L data hn r)

end

end LieRings.MetabelianVanishing
