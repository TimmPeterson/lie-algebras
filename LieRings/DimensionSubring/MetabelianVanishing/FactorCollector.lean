import LieRings.DimensionSubring.MetabelianVanishing.TriangularRows

/-!
# Factor-first collection with triangular full relations

This is the first (vertical) pass in the manuscript's exact two-filtered
calculation.  It never exposes a homogeneous component of a relation.  A
commutator correction is immediately expanded back into the chosen finite
triangular family of genuine full relations.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance factorCollectorFintype : Fintype L := Fintype.ofFinite L

/-- The support list of the finite triangular expansion. -/
def triangularExpansionList (rho : Relations n L data) :
    List (ℤ × Relations n L data) :=
  (triangularExpansion n L data rho).support.toList.map
    (fun sigma ↦ (triangularExpansion n L data rho sigma, sigma))

theorem triangularExpansionList_value (rho : Relations n L data) :
    ((triangularExpansionList n L data rho).map
        (fun p ↦ p.1 • (p.2 : FreeModel n L))).sum =
      (rho : FreeModel n L) := by
  classical
  rw [triangularExpansionList, List.map_map,
    ← List.sum_toFinset _ (Finset.nodup_toList _),
    Finset.toList_toFinset]
  change (triangularExpansion n L data rho).sum
      (fun sigma z ↦ z • (sigma : FreeModel n L)) = _
  exact triangularExpansion_value n L data rho

/-- Factor-first expansion.  Rows of factor number at most two are retained.
At larger factor number the top-marked relation is moved one place right;
the full commutator correction is re-expanded in triangular full rows. -/
def factorFirstExpansion : MarkedRow n L data hn →
    Option (List (ℤ × MarkedRow n L data hn))
  | .ordinary _ => none
  | .marked left rho k right =>
      if hsmall : left.length + right.length + 1 ≤ 2 then none
      else if htop : k.val = n + 1 then
        match right with
        | [] => none
        | v :: rest =>
            some ((1, .marked (left ++ [v]) rho k rest) ::
              (triangularExpansionList n L data
                (relationRightBracket n L data hn rho v)).map
                  (fun p ↦ (p.1, .marked left p.2 k rest)))
      else none

theorem factorFirstExpansion_decreases
    {r : MarkedRow n L data hn}
    {rows : List (ℤ × MarkedRow n L data hn)}
    (h : factorFirstExpansion n L data hn r = some rows) :
    ∀ q ∈ rows,
      rowMeasureLt (markedRowMeasure n L data hn q.2)
        (markedRowMeasure n L data hn r) := by
  classical
  intro q hq
  cases r with
  | ordinary word => simp [factorFirstExpansion] at h
  | marked left rho k right =>
      simp only [factorFirstExpansion] at h
      split at h
      · contradiction
      · rename_i hlarge
        split at h
        · rename_i htop
          cases right with
          | nil => contradiction
          | cons v rest =>
              rw [Option.some.injEq] at h
              subst rows
              simp only [List.mem_cons] at hq
              rcases hq with rfl | hq
              · simp only [markedRowMeasure, List.length_append,
                  List.length_cons]
                unfold rowMeasureLt
                simp only [List.length_nil]
                have hfactor :
                    left.length + (0 + 1) + rest.length + 1 =
                      left.length + (rest.length + 1) + 1 := by
                  omega
                rw [hfactor]
                apply Prod.Lex.right
                apply Prod.Lex.right
                have hword : (left ++ [v]) ++ rest = left ++ v :: rest := by
                  simp
                rw [hword]
                omega
              · rw [List.mem_map] at hq
                obtain ⟨p, hp, rfl⟩ := hq
                simp only [markedRowMeasure, List.length_cons]
                apply Prod.Lex.left
                omega
        · contradiction

private theorem factorFirstCorrection_value
    (left rest : List (AdaptedIndex n L data hn))
    (rho : Relations n L data) (v : AdaptedIndex n L data hn)
    (k : Fin (n + 2)) :
    (((triangularExpansionList n L data
        (relationRightBracket n L data hn rho v)).map
      (fun p ↦ p.1 •
        (MarkedRow.marked left p.2 k rest :
          MarkedRow n L data hn).value)).sum) =
      (MarkedRow.marked left
        (relationRightBracket n L data hn rho v) k rest :
          MarkedRow n L data hn).value := by
  classical
  let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    { toFun := fun x ↦ MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ
            (rowTruncation n L k.val (by omega) x) *
          MarkedRow.basisWord n L data hn rest
      map_add' := by intro x y; rw [map_add, map_add, mul_add, add_mul]
      map_smul' := by
        intro z x
        rw [map_zsmul, map_zsmul, mul_smul_comm, smul_mul_assoc]
        rfl }
  have hv := congrArg context
    (triangularExpansionList_value n L data
      (relationRightBracket n L data hn rho v))
  rw [map_list_sum] at hv
  calc
    _ = ((triangularExpansionList n L data
          (relationRightBracket n L data hn rho v)).map
        (fun p ↦ context (p.1 • (p.2 : FreeModel n L)))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [map_zsmul]
      rfl
    _ = context ((relationRightBracket n L data hn rho v :
          Relations n L data) : FreeModel n L) := by
      simpa only [List.map_map, Function.comp_apply] using hv
    _ = _ := rfl

theorem factorFirstExpansion_preserves
    {r : MarkedRow n L data hn}
    {rows : List (ℤ × MarkedRow n L data hn)}
    (h : factorFirstExpansion n L data hn r = some rows) :
    (rows.map fun q ↦ q.1 • q.2.value).sum = r.value := by
  classical
  cases r with
  | ordinary word => simp [factorFirstExpansion] at h
  | marked left rho k right =>
      simp only [factorFirstExpansion] at h
      split at h
      · contradiction
      · rename_i hlarge
        split at h
        · rename_i htop
          cases right with
          | nil => contradiction
          | cons v rest =>
              rw [Option.some.injEq] at h
              subst rows
              simp only [List.map_cons, List.sum_cons, one_smul,
                List.map_map]
              change
                (MarkedRow.marked (left ++ [v]) rho k rest :
                    MarkedRow n L data hn).value +
                  (((triangularExpansionList n L data
                      (relationRightBracket n L data hn rho v)).map
                    (fun p ↦ p.1 •
                      (MarkedRow.marked left p.2 k rest :
                        MarkedRow n L data hn).value)).sum) = _
              rw [factorFirstCorrection_value]
              have hk : k = ⟨n + 1, by omega⟩ := Fin.ext htop
              rw [hk]
              exact (markedTransferRightTop n L data hn left rest rho v).symm
        · contradiction

/-- The deterministic first pass of the manuscript collection. -/
def factorFirstCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (MarkedRow n L data hn) (UEA ℤ (FreeModel n L)) :=
  deterministicCollector n L data hn
    (markedRowMeasure n L data hn)
    (factorFirstExpansion n L data hn)
    (factorFirstExpansion_decreases n L data hn)
    (factorFirstExpansion_preserves n L data hn)

/-- Initial PBW rows after the required triangular expansion of every
relation coefficient. -/
def GoverningWitness.factorFirstInitial {a : L}
    (w : GoverningWitness n L data a) :
    MarkedRow n L data hn →₀ ℤ :=
  (w.triangularRelationCoefficients n L data).sum (fun p z ↦
    z • markedRowsOfRightFactor n L data hn p.1 p.2)

theorem GoverningWitness.evaluate_factorFirstInitial {a : L}
    (w : GoverningWitness n L data a) :
    (factorFirstCollector n L data hn).evaluate
        (w.factorFirstInitial n L data hn) = w.theta := by
  classical
  rw [GoverningWitness.factorFirstInitial, map_finsuppSum]
  calc
    _ = terminalPacketWord n L data
        (w.triangularRelationCoefficients n L data) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [map_zsmul]
      change w.triangularRelationCoefficients n L data p •
          (closedSquareCollector n L data hn).evaluate
            (markedRowsOfRightFactor n L data hn p.1 p.2) = _
      rw [evaluate_markedRowsOfRightFactor]
    _ = w.theta := w.triangularTheta_eq_theta n L data

/-- Terminal factor-first frontier. -/
def GoverningWitness.factorFirstFrontier {a : L}
    (w : GoverningWitness n L data a) :
    MarkedRow n L data hn →₀ ℤ :=
  (w.factorFirstInitial n L data hn).sum (fun r z ↦
    z • (factorFirstCollector n L data hn).normalForm r)

theorem GoverningWitness.evaluate_factorFirstFrontier {a : L}
    (w : GoverningWitness n L data a) :
    (factorFirstCollector n L data hn).evaluate
        (w.factorFirstFrontier n L data hn) = w.theta := by
  classical
  rw [GoverningWitness.factorFirstFrontier, map_finsuppSum]
  calc
    _ = (factorFirstCollector n L data hn).evaluate
        (w.factorFirstInitial n L data hn) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul,
        (factorFirstCollector n L data hn).evaluate_normalForm]
      rfl
    _ = w.theta := w.evaluate_factorFirstInitial n L data hn

/-! ## Exact support of the first pass -/

/-- Rows reachable in the factor-first pass always retain one genuine full
relation at the top mark.  In particular, this pass never creates an
ordinary pseudo-relation row. -/
def FactorFirstReachable : MarkedRow n L data hn → Prop
  | .ordinary _ => False
  | .marked _ _ k _ => k.val = n + 1

theorem factorFirstExpansion_preserves_reachable
    {r : MarkedRow n L data hn}
    {rows : List (ℤ × MarkedRow n L data hn)}
    (hr : FactorFirstReachable n L data hn r)
    (h : factorFirstExpansion n L data hn r = some rows) :
    ∀ q ∈ rows, FactorFirstReachable n L data hn q.2 := by
  classical
  intro q hq
  cases r with
  | ordinary word => exact hr.elim
  | marked left rho k right =>
      simp only [FactorFirstReachable] at hr
      by_cases hsmall : left.length + right.length + 1 ≤ 2
      · simp [factorFirstExpansion, hsmall] at h
      · by_cases htop : k.val = n + 1
        · cases right with
          | nil => simp [factorFirstExpansion, hsmall, htop] at h
          | cons v rest =>
              simp only [factorFirstExpansion, hsmall, ↓reduceDIte,
                htop] at h
              rw [Option.some.injEq] at h
              subst rows
              simp only [List.mem_cons] at hq
              rcases hq with rfl | hq
              · exact hr
              · rw [List.mem_map] at hq
                obtain ⟨p, hp, rfl⟩ := hq
                exact hr
        · simp [factorFirstExpansion, hsmall, htop] at h

theorem GoverningWitness.factorFirstInitial_reachable_of_ne {a : L}
    (w : GoverningWitness n L data a) (r : MarkedRow n L data hn)
    (hr : w.factorFirstInitial n L data hn r ≠ 0) :
    FactorFirstReachable n L data hn r := by
  classical
  by_contra hreach
  apply hr
  rw [GoverningWitness.factorFirstInitial, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro p hp
  change w.triangularRelationCoefficients n L data p *
      markedRowsOfRightFactor n L data hn p.1 p.2 r = 0
  apply mul_eq_zero_of_right
  rw [markedRowsOfRightFactor, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro e he
  by_cases hre : r = .marked [] p.1 ⟨n + 1, by omega⟩
      (exponentWord n L data hn e)
  · subst r
    exact (hreach rfl).elim
  · simp [Finsupp.single_apply, hre]

theorem GoverningWitness.factorFirstFrontier_reachable_of_ne {a : L}
    (w : GoverningWitness n L data a) (r : MarkedRow n L data hn)
    (hr : w.factorFirstFrontier n L data hn r ≠ 0) :
    FactorFirstReachable n L data hn r := by
  classical
  by_contra hreach
  apply hr
  rw [GoverningWitness.factorFirstFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro root hroot
  change w.factorFirstInitial n L data hn root *
      (factorFirstCollector n L data hn).normalForm root r = 0
  by_cases hrootZero : w.factorFirstInitial n L data hn root = 0
  · rw [hrootZero, zero_mul]
  · have hnormal :
        (factorFirstCollector n L data hn).normalForm root r = 0 := by
      by_contra hnormal
      exact hreach
        ((factorFirstCollector n L data hn).invariant_of_normalForm_apply_ne_zero
          (FactorFirstReachable n L data hn)
          (fun hexp hreachable ↦
            factorFirstExpansion_preserves_reachable n L data hn
              hreachable hexp)
          (w.factorFirstInitial_reachable_of_ne n L data hn root hrootZero)
          hnormal)
    rw [hnormal, mul_zero]

theorem GoverningWitness.factorFirstFrontier_terminal_of_ne {a : L}
    (w : GoverningWitness n L data a) (r : MarkedRow n L data hn)
    (hr : w.factorFirstFrontier n L data hn r ≠ 0) :
    factorFirstExpansion n L data hn r = none := by
  by_contra hnonterminal
  apply hr
  rw [GoverningWitness.factorFirstFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro root hroot
  change w.factorFirstInitial n L data hn root *
      (factorFirstCollector n L data hn).normalForm root r = 0
  rw [(factorFirstCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
    root r hnonterminal, mul_zero]

/-- A terminal reachable row is either already in factor number at most two,
or has put its full relation at the far right. -/
theorem factorFirst_terminal_shape
    (r : MarkedRow n L data hn)
    (hr : FactorFirstReachable n L data hn r)
    (ht : factorFirstExpansion n L data hn r = none) :
    match r with
    | .ordinary _ => False
    | .marked left _ _ right =>
        left.length + right.length + 1 ≤ 2 ∨ right = [] := by
  classical
  cases r with
  | ordinary word => exact hr
  | marked left rho k right =>
      simp only [FactorFirstReachable] at hr
      by_cases hsmall : left.length + right.length + 1 ≤ 2
      · exact Or.inl hsmall
      · right
        cases right with
        | nil => rfl
        | cons v rest =>
            have hsmall' : ¬left.length + (rest.length + 1) + 1 ≤ 2 := by
              simpa only [List.length_cons] using hsmall
            have hexp : factorFirstExpansion n L data hn
                (.marked left rho k (v :: rest)) =
                some ((1, .marked (left ++ [v]) rho k rest) ::
                  (triangularExpansionList n L data
                    (relationRightBracket n L data hn rho v)).map
                      (fun p ↦ (p.1, .marked left p.2 k rest))) := by
              simp [factorFirstExpansion, hsmall', hr]
            rw [hexp] at ht
            contradiction

/-! ## The manuscript collector with its leading Smith tags retained

The untagged collector above is useful for the literal transfer identity,
but cannot state when the leading homogeneous relation factor has reached
its PBW position.  The following is the collector used in the assembly. -/

/-- A finite support list for the tagged triangular expansion of a full
relation. -/
def triangularTaggedExpansionList (rho : Relations n L data) :
    List (ℤ × TriangularRelationIndex n L) :=
  (triangularTaggedExpansion n L data rho).support.toList.map
    (fun i ↦ (triangularTaggedExpansion n L data rho i, i))

theorem triangularTaggedExpansionList_value (rho : Relations n L data) :
    ((triangularTaggedExpansionList n L data rho).map
        (fun p ↦ p.1 •
          (triangularRelationOfIndex n L data p.2 : FreeModel n L))).sum =
      (rho : FreeModel n L) := by
  classical
  rw [triangularTaggedExpansionList, List.map_map,
    ← List.sum_toFinset _ (Finset.nodup_toList _),
    Finset.toList_toFinset]
  change (triangularTaggedExpansion n L data rho).sum
      (fun i z ↦ z •
        (triangularRelationOfIndex n L data i : FreeModel n L)) = _
  exact triangularTaggedExpansion_value n L data rho

/-- Expand a relation known to start at zero-based weight `s`.  Unlike the
global expansion, this version exposes in its type that no smaller Smith tag
can occur. -/
def triangularTaggedExpansionAt
    (s : ℕ) (hs : s ≤ n + 1) (rho : Relations n L data)
    (hrho : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) s) :
    TriangularRelationIndex n L →₀ ℤ :=
  if hlt : s < n + 1 then
    triangularTaggedExpansionFrom n L data (n + 1 - s) s (by omega)
      ⟨rho.1, rho.property, hrho⟩
  else 0

theorem triangularTaggedExpansionAt_value
    (s : ℕ) (hs : s ≤ n + 1) (rho : Relations n L data)
    (hrho : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) s) :
    (triangularTaggedExpansionAt n L data s hs rho hrho).sum
        (fun i z ↦ z •
          (triangularRelationOfIndex n L data i : FreeModel n L)) =
      (rho : FreeModel n L) := by
  classical
  unfold triangularTaggedExpansionAt
  split
  · exact triangularTaggedExpansionFrom_value n L data (n + 1 - s) s
      (by omega) ⟨rho.1, rho.property, hrho⟩
  · rename_i hnot
    have hsn : s = n + 1 := by omega
    have hzero : (rho : FreeModel n L) = 0 := by
      have hz : (rho : FreeModel n L) ∈
          FreeMetabelian.Free.tail
            (X := Generator L) (c := n + 1) (n + 1) := by
        simpa only [hsn] using hrho
      rw [FreeMetabelian.Free.tail_cutoff_eq_bot] at hz
      simpa using hz
    simp [hzero]

theorem triangularTaggedExpansionAt_weight_ge
    (s : ℕ) (hs : s ≤ n + 1) (rho : Relations n L data)
    (hrho : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) s)
    (i : TriangularRelationIndex n L)
    (hi : triangularTaggedExpansionAt n L data s hs rho hrho i ≠ 0) :
    s ≤ i.1.val := by
  classical
  unfold triangularTaggedExpansionAt at hi
  split at hi
  · exact triangularTaggedExpansionFrom_weight_ge n L data
      (n + 1 - s) s (by omega) ⟨rho.1, rho.property, hrho⟩ i hi
  · simp at hi

/-- The relation bracket correction, still represented by a genuine full
kernel element. -/
def triangularRelationRightBracket (rho : Relations n L data)
    (v : TriangularPBWIndex n L) : Relations n L data :=
  ⟨⁅(rho : FreeModel n L), triangularPBWBasis n L data v⁆, by
    rw [← lie_skew]
    exact (Relations n L data).neg_mem
      ((Relations n L data).lie_mem rho.property)⟩

/-- First possible zero-based weight of the full commutator correction. -/
def triangularCorrectionBound
    (tag : TriangularRelationIndex n L)
    (v : TriangularPBWIndex n L) : ℕ :=
  tag.1.val + v.1.val + 1

theorem triangularRelationRightBracket_mem_tail
    (tag : TriangularRelationIndex n L)
    (v : TriangularPBWIndex n L) :
    (triangularRelationRightBracket n L data
        (triangularRelationOfIndex n L data tag) v : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1)
        (triangularCorrectionBound n L tag v) := by
  have h := RelationContext.bracket_weightIncl_right_mem_tail n L
    (triangularRelationOfIndex n L data tag : FreeModel n L)
    tag.1.val v.1.val v.1.isLt
    (triangularRelationOfIndex_mem_tail n L data tag)
    (triangularPieceBasis n L data v.1.val v.1.isLt v.2)
  simpa only [triangularCorrectionBound, triangularPBWBasis_apply,
    triangularRelationRightBracket] using h

/-- Triangular expansion of a correction, starting at its proved bracket
weight.  If that weight lies past the nilpotence cutoff, the correction is
literally zero. -/
def triangularCorrectionTaggedExpansion
    (tag : TriangularRelationIndex n L)
    (v : TriangularPBWIndex n L) :
    TriangularRelationIndex n L →₀ ℤ :=
  if h : triangularCorrectionBound n L tag v ≤ n + 1 then
    triangularTaggedExpansionAt n L data
      (triangularCorrectionBound n L tag v) h
      (triangularRelationRightBracket n L data
        (triangularRelationOfIndex n L data tag) v)
      (triangularRelationRightBracket_mem_tail n L data tag v)
  else 0

theorem triangularCorrectionTaggedExpansion_value
    (tag : TriangularRelationIndex n L)
    (v : TriangularPBWIndex n L) :
    (triangularCorrectionTaggedExpansion n L data tag v).sum
        (fun i z ↦ z •
          (triangularRelationOfIndex n L data i : FreeModel n L)) =
      (triangularRelationRightBracket n L data
        (triangularRelationOfIndex n L data tag) v : FreeModel n L) := by
  classical
  unfold triangularCorrectionTaggedExpansion
  split
  · exact triangularTaggedExpansionAt_value n L data
      (triangularCorrectionBound n L tag v) (by assumption)
      (triangularRelationRightBracket n L data
        (triangularRelationOfIndex n L data tag) v)
      (triangularRelationRightBracket_mem_tail n L data tag v)
  · rename_i hlarge
    have htail := triangularRelationRightBracket_mem_tail n L data tag v
    have hzero : (triangularRelationRightBracket n L data
        (triangularRelationOfIndex n L data tag) v : FreeModel n L) = 0 := by
      funext i
      exact htail i (by omega)
    simp [hzero]

theorem triangularCorrectionTaggedExpansion_weight_ge
    (tag : TriangularRelationIndex n L)
    (v : TriangularPBWIndex n L)
    (i : TriangularRelationIndex n L)
    (hi : triangularCorrectionTaggedExpansion n L data tag v i ≠ 0) :
    triangularCorrectionBound n L tag v ≤ i.1.val := by
  classical
  unfold triangularCorrectionTaggedExpansion at hi
  split at hi
  · exact triangularTaggedExpansionAt_weight_ge n L data
      (triangularCorrectionBound n L tag v) (by assumption)
      (triangularRelationRightBracket n L data
        (triangularRelationOfIndex n L data tag) v)
      (triangularRelationRightBracket_mem_tail n L data tag v) i hi
  · simp at hi

def triangularCorrectionExpansionList
    (tag : TriangularRelationIndex n L)
    (v : TriangularPBWIndex n L) :
    List (ℤ × TriangularRelationIndex n L) :=
  (triangularCorrectionTaggedExpansion n L data tag v).support.toList.map
    (fun i ↦ (triangularCorrectionTaggedExpansion n L data tag v i, i))

theorem triangularCorrectionExpansionList_value
    (tag : TriangularRelationIndex n L)
    (v : TriangularPBWIndex n L) :
    ((triangularCorrectionExpansionList n L data tag v).map
        (fun p ↦ p.1 •
          (triangularRelationOfIndex n L data p.2 : FreeModel n L))).sum =
      (triangularRelationRightBracket n L data
        (triangularRelationOfIndex n L data tag) v : FreeModel n L) := by
  classical
  rw [triangularCorrectionExpansionList, List.map_map,
    ← List.sum_toFinset _ (Finset.nodup_toList _),
    Finset.toList_toFinset]
  change (triangularCorrectionTaggedExpansion n L data tag v).sum
      (fun i z ↦ z •
        (triangularRelationOfIndex n L data i : FreeModel n L)) = _
  exact triangularCorrectionTaggedExpansion_value n L data tag v

/-- A placed full triangular relation.  Its tag determines the PBW position
of its Smith head; its evaluation always uses the whole relation. -/
structure TriangularPlacedRow where
  tag : TriangularRelationIndex n L
  left : List (TriangularPBWIndex n L)
  right : List (TriangularPBWIndex n L)

noncomputable instance : DecidableEq (TriangularPlacedRow n L) :=
  Classical.decEq _

namespace TriangularPlacedRow

def relation (r : TriangularPlacedRow n L) : Relations n L data :=
  triangularRelationOfIndex n L data r.tag

def basisWord (xs : List (TriangularPBWIndex n L)) :
    UEA ℤ (FreeModel n L) :=
  LieRings.PBW.basisWord ℤ (FreeModel n L)
    (TriangularPBWIndex n L) (triangularPBWBasis n L data) xs

def value (r : TriangularPlacedRow n L) :
    UEA ℤ (FreeModel n L) :=
  TriangularPlacedRow.basisWord n L data r.left *
    UniversalEnvelopingAlgebra.ι ℤ
      (TriangularPlacedRow.relation n L data r : FreeModel n L) *
    TriangularPlacedRow.basisWord n L data r.right

def factorCount (r : TriangularPlacedRow n L) : ℕ :=
  r.left.length + r.right.length + 1

def measure (r : TriangularPlacedRow n L) : ℕ × ℕ :=
  (TriangularPlacedRow.factorCount n L r, r.right.length)

end TriangularPlacedRow

/-- Move the full relation across precisely the next ordinary factor lying
strictly before its Smith head.  At factor two both orientations are retained
unchanged for the terminal quadratic block. -/
def triangularPlacedExpansion (r : TriangularPlacedRow n L) :
    Option (List (ℤ × TriangularPlacedRow n L)) :=
  if hsmall : TriangularPlacedRow.factorCount n L r ≤ 2 then none
  else
    match r.right with
    | [] => none
    | v :: rest =>
        if hv : v < triangularHeadIndex n L r.tag then
          some ((1, ⟨r.tag, r.left ++ [v], rest⟩) ::
            (triangularCorrectionExpansionList n L data r.tag v).map
                (fun p ↦ (p.1, ⟨p.2, r.left, rest⟩)))
        else none

theorem triangularPlacedExpansion_decreases
    {r : TriangularPlacedRow n L}
    {rows : List (ℤ × TriangularPlacedRow n L)}
    (h : triangularPlacedExpansion n L data r = some rows) :
    ∀ q ∈ rows,
      Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
        (TriangularPlacedRow.measure n L q.2)
        (TriangularPlacedRow.measure n L r) := by
  classical
  intro q hq
  unfold triangularPlacedExpansion at h
  split at h
  · contradiction
  · rename_i hlarge
    split at h
    · contradiction
    · rename_i v rest hright
      split at h
      · rename_i hv
        rw [Option.some.injEq] at h
        subst rows
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · simp only [Prod.snd, TriangularPlacedRow.measure,
            TriangularPlacedRow.factorCount]
          have hcount : (r.left ++ [v]).length + rest.length + 1 =
              r.left.length + r.right.length + 1 := by
            rw [hright]
            simp
            omega
          rw [hcount]
          apply Prod.Lex.right
          simp [hright]
        · rw [List.mem_map] at hq
          obtain ⟨p, hp, rfl⟩ := hq
          simp only [Prod.snd, TriangularPlacedRow.measure,
            TriangularPlacedRow.factorCount]
          apply Prod.Lex.left
          simp [hright]
      · contradiction

private theorem triangularPlacedCorrection_value
    (tag : TriangularRelationIndex n L)
    (left rest : List (TriangularPBWIndex n L))
    (v : TriangularPBWIndex n L) :
    (((triangularCorrectionExpansionList n L data tag v).map
      (fun p ↦ p.1 •
        (TriangularPlacedRow.value n L data
          ⟨p.2, left, rest⟩))).sum) =
      TriangularPlacedRow.basisWord n L data left *
        UniversalEnvelopingAlgebra.ι ℤ
          (triangularRelationRightBracket n L data
            (triangularRelationOfIndex n L data tag) v : FreeModel n L) *
        TriangularPlacedRow.basisWord n L data rest := by
  classical
  let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    { toFun := fun x ↦ TriangularPlacedRow.basisWord n L data left *
          UniversalEnvelopingAlgebra.ι ℤ x *
          TriangularPlacedRow.basisWord n L data rest
      map_add' := by intro x y; rw [map_add, mul_add, add_mul]
      map_smul' := by
        intro z x
        rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
        rfl }
  have hv := congrArg context
    (triangularCorrectionExpansionList_value n L data tag v)
  rw [map_list_sum] at hv
  calc
    _ = ((triangularCorrectionExpansionList n L data tag v).map
        (fun p ↦ context
          (p.1 • (triangularRelationOfIndex n L data p.2 : FreeModel n L)))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [map_zsmul]
      rfl
    _ = context (triangularRelationRightBracket n L data
          (triangularRelationOfIndex n L data tag) v : FreeModel n L) := by
      simpa only [List.map_map, Function.comp_apply] using hv
    _ = _ := rfl

theorem triangularPlacedExpansion_preserves
    {r : TriangularPlacedRow n L}
    {rows : List (ℤ × TriangularPlacedRow n L)}
    (h : triangularPlacedExpansion n L data r = some rows) :
    (rows.map fun q ↦ q.1 •
      TriangularPlacedRow.value n L data q.2).sum =
      TriangularPlacedRow.value n L data r := by
  classical
  unfold triangularPlacedExpansion at h
  split at h
  · contradiction
  · rename_i hlarge
    split at h
    · contradiction
    · rename_i v rest hright
      split at h
      · rename_i hv
        rw [Option.some.injEq] at h
        subst rows
        simp only [List.map_cons, List.sum_cons, one_smul, List.map_map]
        change TriangularPlacedRow.value n L data
            ⟨r.tag, r.left ++ [v], rest⟩ +
          (((triangularCorrectionExpansionList n L data r.tag v).map
            (fun p ↦ p.1 • TriangularPlacedRow.value n L data
              ⟨p.2, r.left, rest⟩)).sum) =
            TriangularPlacedRow.value n L data r
        rw [triangularPlacedCorrection_value]
        have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
          (FreeModel n L)
            (TriangularPlacedRow.relation n L data r : FreeModel n L)
            (triangularPBWBasis n L data v)
        let lw := TriangularPlacedRow.basisWord n L data r.left
        let rwrd := TriangularPlacedRow.basisWord n L data rest
        let iv := UniversalEnvelopingAlgebra.ι ℤ
          (triangularPBWBasis n L data v)
        let ir := UniversalEnvelopingAlgebra.ι ℤ
          (TriangularPlacedRow.relation n L data r : FreeModel n L)
        have hleftWord : TriangularPlacedRow.basisWord n L data
            (r.left ++ [v]) = lw * iv := by
          simp [TriangularPlacedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, List.map_append, lw, iv]
        have hrightWord : TriangularPlacedRow.basisWord n L data
            (v :: rest) = iv * rwrd := by
          simp [TriangularPlacedRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, rwrd, iv]
        simp only [TriangularPlacedRow.value,
          TriangularPlacedRow.relation]
        rw [hleftWord, hright, hrightWord]
        have hleft : TriangularPlacedRow.basisWord n L data r.left = lw := rfl
        have hrest : TriangularPlacedRow.basisWord n L data rest = rwrd := rfl
        have hrelation : UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationOfIndex n L data r.tag : FreeModel n L) = ir := rfl
        rw [hleft, hrest, hrelation]
        change lw * iv * ir * rwrd +
            lw * UniversalEnvelopingAlgebra.ι ℤ
              (triangularRelationRightBracket n L data
                (triangularRelationOfIndex n L data r.tag) v :
                  FreeModel n L) * rwrd =
          lw * ir * (iv * rwrd)
        change ir * iv = iv * ir +
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationRightBracket n L data
              (triangularRelationOfIndex n L data r.tag) v :
                FreeModel n L) at hswap
        calc
          _ = lw * (iv * ir +
                UniversalEnvelopingAlgebra.ι ℤ
                  (triangularRelationRightBracket n L data
                    (triangularRelationOfIndex n L data r.tag) v :
                      FreeModel n L)) * rwrd := by noncomm_ring
          _ = lw * (ir * iv) * rwrd := by rw [← hswap]
          _ = _ := by noncomm_ring
      · contradiction

/-- The deterministic, strictly decreasing triangular placement pass. -/
def triangularPlacedCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (TriangularPlacedRow n L) (UEA ℤ (FreeModel n L)) where
  relation x y := Prod.Lex (fun a b : ℕ ↦ a < b)
    (fun a b : ℕ ↦ a < b)
      (TriangularPlacedRow.measure n L x)
      (TriangularPlacedRow.measure n L y)
  wellFounded := InvImage.wf (TriangularPlacedRow.measure n L)
    (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  expansion := triangularPlacedExpansion n L data
  value := TriangularPlacedRow.value n L data
  decreases := triangularPlacedExpansion_decreases n L data
  preserves := triangularPlacedExpansion_preserves n L data

/-- Sorted PBW word for the triangular homogeneous basis. -/
def triangularExponentWord (e : TriangularPBWIndex n L →₀ ℕ) :
    List (TriangularPBWIndex n L) :=
  (Finsupp.toMultiset e).sort (· ≤ ·)

/-- Expand a tagged relation with an arbitrary right multiplier into the
literal top frontier of the placement collector. -/
def triangularPlacedRowsOfRightFactor
    (tag : TriangularRelationIndex n L)
    (u : UEA ℤ (FreeModel n L)) :
    TriangularPlacedRow n L →₀ ℤ :=
  ((triangularWeightedBasis n L data).pbwEquiv.symm u).sum
    (fun e z ↦ Finsupp.single
      ⟨tag, [], triangularExponentWord n L e⟩ z)

theorem evaluate_triangularPlacedRowsOfRightFactor
    (tag : TriangularRelationIndex n L)
    (u : UEA ℤ (FreeModel n L)) :
    (triangularPlacedCollector n L data).evaluate
        (triangularPlacedRowsOfRightFactor n L data tag u) =
      UniversalEnvelopingAlgebra.ι ℤ
        (triangularRelationOfIndex n L data tag : FreeModel n L) * u := by
  classical
  let B := triangularWeightedBasis n L data
  rw [triangularPlacedRowsOfRightFactor, map_finsuppSum]
  simp only [LieRings.DegreeFive.FiniteTaggedCollector.evaluate_single]
  have hu : (B.pbwEquiv.symm u).sum
      (fun e z ↦ z • LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
        (TriangularPBWIndex n L) B.basis e) = u := by
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
      _ = u := by rw [hsum, B.pbwEquiv.apply_symm_apply]
  calc
    _ = (B.pbwEquiv.symm u).sum (fun e z ↦ z •
        (UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationOfIndex n L data tag : FreeModel n L) *
          LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
            (TriangularPBWIndex n L) B.basis e)) := by
      apply Finsupp.sum_congr
      intro e he
      congr 1
      change TriangularPlacedRow.value n L data
          ⟨tag, [], triangularExponentWord n L e⟩ = _
      simp [TriangularPlacedRow.value, TriangularPlacedRow.relation,
        TriangularPlacedRow.basisWord, triangularExponentWord, B,
        LieRings.PBW.orderedMonomial,
        LieRings.PBW.basisWord, LieRings.PBW.word]
      congr 1
    _ = UniversalEnvelopingAlgebra.ι ℤ
          (triangularRelationOfIndex n L data tag : FreeModel n L) *
        (B.pbwEquiv.symm u).sum (fun e z ↦ z •
          LieRings.PBW.orderedMonomial ℤ (FreeModel n L)
            (TriangularPBWIndex n L) B.basis e) := by
      rw [Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro e he
      rw [mul_smul_comm]
    _ = _ := by rw [hu]

/-- The complete tagged initial expression of the governing relative chain. -/
def GoverningWitness.triangularPlacedInitial {a : L}
    (w : GoverningWitness n L data a) :
    TriangularPlacedRow n L →₀ ℤ :=
  (w.triangularTaggedRelationCoefficients n L data).sum
    (fun p z ↦ z • triangularPlacedRowsOfRightFactor n L data p.1 p.2)

theorem GoverningWitness.evaluate_triangularPlacedInitial {a : L}
    (w : GoverningWitness n L data a) :
    (triangularPlacedCollector n L data).evaluate
        (w.triangularPlacedInitial n L data) = w.theta := by
  classical
  rw [GoverningWitness.triangularPlacedInitial, map_finsuppSum]
  calc
    _ = (w.triangularTaggedRelationCoefficients n L data).sum
        (fun p z ↦ z •
          (UniversalEnvelopingAlgebra.ι ℤ
              (triangularRelationOfIndex n L data p.1 : FreeModel n L) *
            p.2)) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [map_zsmul, evaluate_triangularPlacedRowsOfRightFactor]
    _ = w.theta := w.triangularTaggedTheta_eq_theta n L data

/-- The terminal tagged placement frontier. -/
def GoverningWitness.triangularPlacedFrontier {a : L}
    (w : GoverningWitness n L data a) :
    TriangularPlacedRow n L →₀ ℤ :=
  (w.triangularPlacedInitial n L data).sum (fun r z ↦
    z • (triangularPlacedCollector n L data).normalForm r)

theorem GoverningWitness.evaluate_triangularPlacedFrontier {a : L}
    (w : GoverningWitness n L data a) :
    (triangularPlacedCollector n L data).evaluate
        (w.triangularPlacedFrontier n L data) = w.theta := by
  classical
  rw [GoverningWitness.triangularPlacedFrontier, map_finsuppSum]
  calc
    _ = (triangularPlacedCollector n L data).evaluate
        (w.triangularPlacedInitial n L data) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul,
        (triangularPlacedCollector n L data).evaluate_normalForm]
      rfl
    _ = w.theta := w.evaluate_triangularPlacedInitial n L data

/-! ## The exact Smith-head placement invariant -/

/-- The ordinary factors stay ordered, and every factor already crossed by
the relation lies strictly before its tagged Smith head. -/
def TriangularPlacedInvariant (r : TriangularPlacedRow n L) : Prop :=
  (r.left ++ r.right).Pairwise (· ≤ ·) ∧
    ∀ x ∈ r.left, x < triangularHeadIndex n L r.tag

private theorem triangularPBW_lt_of_weight_lt
    {i j : TriangularPBWIndex n L} (h : i.1.val < j.1.val) : i < j := by
  change toLex (i.1.val, (Finite.equivFin _ i.2).val) <
    toLex (j.1.val, (Finite.equivFin _ j.2).val)
  exact Prod.Lex.left _ _ h

theorem triangularPlacedExpansion_preserves_invariant
    {r : TriangularPlacedRow n L}
    {rows : List (ℤ × TriangularPlacedRow n L)}
    (hr : TriangularPlacedInvariant n L r)
    (h : triangularPlacedExpansion n L data r = some rows) :
    ∀ q ∈ rows, TriangularPlacedInvariant n L q.2 := by
  classical
  intro q hq
  unfold triangularPlacedExpansion at h
  split at h
  · contradiction
  · rename_i hlarge
    split at h
    · contradiction
    · rename_i v rest hright
      split at h
      · rename_i hv
        rw [Option.some.injEq] at h
        subst rows
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · constructor
          · simpa [hright, List.append_assoc] using hr.1
          · intro x hx
            rw [List.mem_append] at hx
            rcases hx with hx | hx
            · exact hr.2 x hx
            · simp only [List.mem_singleton] at hx
              simpa [hx] using hv
        · rw [List.mem_map] at hq
          obtain ⟨p, hp, rfl⟩ := hq
          have htagSupport : p.2 ∈
              (triangularCorrectionTaggedExpansion n L data r.tag v).support := by
            rw [triangularCorrectionExpansionList] at hp
            simp only [List.mem_map] at hp
            obtain ⟨i, hi, rfl⟩ := hp
            simpa only [Finset.mem_toList] using hi
          have htagCoeff : triangularCorrectionTaggedExpansion n L data
              r.tag v p.2 ≠ 0 := Finsupp.mem_support_iff.mp htagSupport
          have hbound := triangularCorrectionTaggedExpansion_weight_ge
            n L data r.tag v p.2 htagCoeff
          have hheadlt : triangularHeadIndex n L r.tag <
              triangularHeadIndex n L p.2 := by
            apply triangularPBW_lt_of_weight_lt n L
            change r.tag.1.val < p.2.1.val
            unfold triangularCorrectionBound at hbound
            omega
          constructor
          · have hsub : List.Sublist (r.left ++ rest)
                (r.left ++ r.right) := by
              rw [hright]
              exact List.Sublist.append (List.Sublist.refl r.left)
                (List.tail_sublist (v :: rest))
            exact hr.1.sublist hsub
          · intro x hx
            exact (hr.2 x hx).trans hheadlt
      · contradiction

private theorem triangularExponentWord_pairwise
    (e : TriangularPBWIndex n L →₀ ℕ) :
    (triangularExponentWord n L e).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

theorem GoverningWitness.triangularPlacedInitial_invariant_of_ne {a : L}
    (w : GoverningWitness n L data a)
    (r : TriangularPlacedRow n L)
    (hr : w.triangularPlacedInitial n L data r ≠ 0) :
    TriangularPlacedInvariant n L r := by
  classical
  rw [GoverningWitness.triangularPlacedInitial, Finsupp.sum_apply] at hr
  have hexists : ∃ p ∈
      (w.triangularTaggedRelationCoefficients n L data).support,
      (w.triangularTaggedRelationCoefficients n L data p •
        triangularPlacedRowsOfRightFactor n L data p.1 p.2) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun p hp ↦ hall p hp))
  obtain ⟨p, hp, hpr⟩ := hexists
  have hrows : triangularPlacedRowsOfRightFactor n L data p.1 p.2 r ≠ 0 := by
    intro hz
    apply hpr
    simp [Finsupp.smul_apply, hz]
  rw [triangularPlacedRowsOfRightFactor, Finsupp.sum_apply] at hrows
  have he : ∃ e ∈ ((triangularWeightedBasis n L data).pbwEquiv.symm p.2).support,
      (Finsupp.single ⟨p.1, [], triangularExponentWord n L e⟩
        (((triangularWeightedBasis n L data).pbwEquiv.symm p.2) e)) r ≠ 0 := by
    by_contra hall
    push Not at hall
    have hz := Finset.sum_eq_zero (fun e he ↦ hall e he)
    exact hrows hz
  obtain ⟨e, he, her⟩ := he
  have hre : r = ⟨p.1, [], triangularExponentWord n L e⟩ := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at her
  subst r
  exact ⟨by simpa using triangularExponentWord_pairwise n L e, by simp⟩

theorem GoverningWitness.triangularPlacedFrontier_invariant_of_ne {a : L}
    (w : GoverningWitness n L data a)
    (r : TriangularPlacedRow n L)
    (hr : w.triangularPlacedFrontier n L data r ≠ 0) :
    TriangularPlacedInvariant n L r := by
  classical
  by_contra hreach
  apply hr
  rw [GoverningWitness.triangularPlacedFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro root hroot
  change w.triangularPlacedInitial n L data root *
      (triangularPlacedCollector n L data).normalForm root r = 0
  by_cases hrootZero : w.triangularPlacedInitial n L data root = 0
  · rw [hrootZero, zero_mul]
  · have hnormal : (triangularPlacedCollector n L data).normalForm root r = 0 := by
      by_contra hnormal
      exact hreach
        ((triangularPlacedCollector n L data).invariant_of_normalForm_apply_ne_zero
          (TriangularPlacedInvariant n L)
          (fun hexp hinv ↦
            triangularPlacedExpansion_preserves_invariant n L data hinv hexp)
          (w.triangularPlacedInitial_invariant_of_ne n L data root hrootZero)
          hnormal)
    rw [hnormal, mul_zero]

theorem GoverningWitness.triangularPlacedFrontier_terminal_of_ne {a : L}
    (w : GoverningWitness n L data a)
    (r : TriangularPlacedRow n L)
    (hr : w.triangularPlacedFrontier n L data r ≠ 0) :
    triangularPlacedExpansion n L data r = none := by
  by_contra hnonterminal
  apply hr
  rw [GoverningWitness.triangularPlacedFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro root hroot
  change w.triangularPlacedInitial n L data root *
      (triangularPlacedCollector n L data).normalForm root r = 0
  rw [(triangularPlacedCollector n L data).normalForm_apply_eq_zero_of_nonterminal
    root r hnonterminal, mul_zero]

/-- At a terminal row above the quadratic wall, the tagged Smith head has
reached its unique ordered position. -/
theorem triangularPlaced_terminal_head_position
    (r : TriangularPlacedRow n L)
    (hr : TriangularPlacedInvariant n L r)
    (ht : triangularPlacedExpansion n L data r = none)
    (hlarge : 2 < r.factorCount n L) :
    (r.left ++ triangularHeadIndex n L r.tag :: r.right).Pairwise (· ≤ ·) := by
  classical
  have hrightBound : ∀ y ∈ r.right,
      triangularHeadIndex n L r.tag ≤ y := by
    intro y hy
    cases hright : r.right with
    | nil => simp [hright] at hy
    | cons first rest =>
        have hfirst : triangularHeadIndex n L r.tag ≤ first := by
          by_contra hnot
          have hlt : first < triangularHeadIndex n L r.tag := lt_of_not_ge hnot
          unfold triangularPlacedExpansion at ht
          have hnsmall : ¬r.factorCount n L ≤ 2 := by omega
          rw [hright] at ht
          simp [hlt] at ht
          omega
        rcases List.pairwise_append.mp hr.1 with ⟨_, hpairRight, _⟩
        rw [hright] at hpairRight
        rcases List.pairwise_cons.mp hpairRight with ⟨hrest, _⟩
        by_cases hyf : y = first
        · simpa [hyf] using hfirst
        · have hyrest : y ∈ rest := by
            rw [hright] at hy
            simpa [hyf] using hy
          exact hfirst.trans (hrest y hyrest)
  apply List.pairwise_append.mpr
  rcases List.pairwise_append.mp hr.1 with ⟨hleft, hright, hcross⟩
  refine ⟨hleft, List.pairwise_cons.mpr ⟨hrightBound, hright⟩, ?_⟩
  intro x hx y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact (hr.2 x hx).le
  · exact hcross x hx y hy

/-! ## The leading PBW coefficient of a placed triangular row -/

/-- The ordered word obtained by replacing the full relation by its single
Smith head. -/
def TriangularPlacedRow.headWord (r : TriangularPlacedRow n L) :
    List (TriangularPBWIndex n L) :=
  r.left ++ triangularHeadIndex n L r.tag :: r.right

/-- The total PBW weight of the Smith-head word. -/
def TriangularPlacedRow.headWeight (r : TriangularPlacedRow n L) : ℕ :=
  ((r.headWord n L).map (triangularWeightedBasis n L data).weight).sum

private theorem triangularRelationTail_repr_ne_zero_weight_gt
    (tag : TriangularRelationIndex n L) (i : TriangularPBWIndex n L)
    (hi : (triangularPBWBasis n L data).repr
        (triangularRelationTail n L data tag) i ≠ 0) :
    tag.1.val < i.1.val := by
  by_contra hnot
  have hlt : i.1.val < tag.1.val + 1 := by omega
  have hcoord := triangularRelationTail_mem_tail_succ n L data tag i.1 hlt
  apply hi
  change ((triangularPieceBasis n L data i.1.val i.1.isLt).repr
      ((triangularRelationTail n L data tag) i.1)) i.2 = 0
  rw [hcoord, map_zero]
  rfl

private theorem triangularPlaced_tail_proj_eq_zero
    (r : TriangularPlacedRow n L) :
    (triangularWeightedBasis n L data).proj
        (r.headWeight n L data) (r.factorCount n L)
        (TriangularPlacedRow.basisWord n L data r.left *
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationTail n L data r.tag) *
          TriangularPlacedRow.basisWord n L data r.right) = 0 := by
  classical
  let B := triangularWeightedBasis n L data
  let tail := triangularRelationTail n L data r.tag
  rw [← (triangularPBWBasis n L data).sum_repr
      (triangularRelationTail n L data r.tag),
    map_sum, Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_zsmul, mul_smul_comm, smul_mul_assoc, map_zsmul]
  by_cases hcoeff : (triangularPBWBasis n L data).repr tail i = 0
  · rw [hcoeff, zero_smul]
  · have hiWeight := triangularRelationTail_repr_ne_zero_weight_gt
      n L data r.tag i hcoeff
    have hword : TriangularPlacedRow.basisWord n L data r.left *
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularPBWBasis n L data i) *
          TriangularPlacedRow.basisWord n L data r.right =
        TriangularPlacedRow.basisWord n L data
          (r.left ++ i :: r.right) := by
      simp [TriangularPlacedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word, List.map_append]
      noncomm_ring
    rw [hword]
    have hweight :
        (((r.left ++ i :: r.right).map B.weight).sum) ≠
          r.headWeight n L data := by
      simp only [TriangularPlacedRow.headWeight,
        TriangularPlacedRow.headWord, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      change (r.left.map B.weight).sum +
          (i.1.val + 1 + (r.right.map B.weight).sum) ≠
        (r.left.map B.weight).sum +
          (r.tag.1.val + 1 + (r.right.map B.weight).sum)
      omega
    have hzero : (triangularWeightedBasis n L data).proj
        (r.headWeight n L data) (r.factorCount n L)
        (TriangularPlacedRow.basisWord n L data
          (r.left ++ i :: r.right)) = 0 := by
      simpa [B, TriangularPlacedRow.basisWord] using
        B.proj_basisWord_eq_zero_of_weight_ne
          (r.left ++ i :: r.right) (r.headWeight n L data)
            (r.factorCount n L) hweight
    rw [hzero, smul_zero]

/-- Once the Smith head has reached its prescribed ordered position, the
projection to its exact weight and factor number is precisely its positive
Smith coefficient times that ordered PBW word.  The higher homogeneous tail
is invisible in this projection. -/
theorem triangularPlaced_proj_head
    (r : TriangularPlacedRow n L)
    (hordered : (r.headWord n L).Pairwise (· ≤ ·)) :
    (triangularWeightedBasis n L data).proj
        (r.headWeight n L data) (r.factorCount n L)
          (TriangularPlacedRow.value n L data r) =
      ((triangularSmith n L data r.tag.1.val r.tag.1.isLt).diagonal
          r.tag.2 : ℤ) • TriangularPlacedRow.basisWord n L data
            (r.headWord n L) := by
  classical
  let B := triangularWeightedBasis n L data
  let d : ℤ :=
    (triangularSmith n L data r.tag.1.val r.tag.1.isLt).diagonal r.tag.2
  have hrelation := triangularRelation_eq_head_add_tail n L data r.tag
  have hheadWord : TriangularPlacedRow.basisWord n L data
        (r.headWord n L) =
      TriangularPlacedRow.basisWord n L data r.left *
        UniversalEnvelopingAlgebra.ι ℤ
          (triangularPBWBasis n L data (triangularHeadIndex n L r.tag)) *
        TriangularPlacedRow.basisWord n L data r.right := by
    simp [TriangularPlacedRow.basisWord, TriangularPlacedRow.headWord,
      LieRings.PBW.basisWord, LieRings.PBW.word, List.map_append]
    noncomm_ring
  have hvalue : TriangularPlacedRow.value n L data r =
      d • TriangularPlacedRow.basisWord n L data (r.headWord n L) +
        TriangularPlacedRow.basisWord n L data r.left *
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationTail n L data r.tag) *
          TriangularPlacedRow.basisWord n L data r.right := by
    simp only [TriangularPlacedRow.value, TriangularPlacedRow.relation]
    rw [hrelation, map_add, mul_add, add_mul]
    change _ = d • TriangularPlacedRow.basisWord n L data
      (r.headWord n L) + _
    congr 1
    rw [hheadWord]
    simp only [map_zsmul, triangularPBWBasis_apply, d]
    rw [mul_smul_comm, smul_mul_assoc]
    simp [triangularHeadIndex]
    rfl
  have hhead : (triangularWeightedBasis n L data).proj
        (r.headWeight n L data) (r.factorCount n L)
        (TriangularPlacedRow.basisWord n L data (r.headWord n L)) =
      TriangularPlacedRow.basisWord n L data (r.headWord n L) := by
    have h := B.proj_basisWord_sorted (r.headWord n L) hordered
    simpa [B, TriangularPlacedRow.headWeight,
      TriangularPlacedRow.factorCount, TriangularPlacedRow.headWord,
      TriangularPlacedRow.basisWord] using h
  rw [hvalue, map_add, map_zsmul, hhead,
    triangularPlaced_tail_proj_eq_zero n L data r, add_zero]

/-! ## Literal subset collection with a full relation -/

/-- One summand of the subset-collection identity, with the ordinary
spectators on the left and the iterated full relation on the right. -/
structure RelationRightRow where
  relation : Relations n L data
  ordinary : List (AdaptedIndex n L data hn)

noncomputable instance : DecidableEq (RelationRightRow n L data hn) :=
  Classical.decEq _

namespace RelationRightRow

/-- Literal enveloping value of a right-collected row. -/
def value (r : RelationRightRow n L data hn) :
    UEA ℤ (FreeModel n L) :=
  MarkedRow.basisWord n L data hn r.ordinary *
    UniversalEnvelopingAlgebra.ι ℤ (r.relation : FreeModel n L)

end RelationRightRow

/-- All subset terms in
`rho * x₁ * ... * xᵣ = ∑ x_(Iᶜ) * [rho;x_I]`, in their literal
recursive order.  The factors and bracket teeth retain their input order. -/
def relationSubsetCollection
    (rho : Relations n L data) :
    List (AdaptedIndex n L data hn) →
      List (RelationRightRow n L data hn)
  | [] => [⟨rho, []⟩]
  | x :: xs =>
      (relationSubsetCollection rho xs).map
          (fun r ↦ ⟨r.relation, x :: r.ordinary⟩) ++
        relationSubsetCollection
          (relationRightBracket n L data hn rho x) xs

private theorem relationSubsetCollection_prepend_value
    (x : AdaptedIndex n L data hn)
    (rows : List (RelationRightRow n L data hn)) :
    ((rows.map (fun r ↦
        RelationRightRow.value n L data hn
          ⟨r.relation, x :: r.ordinary⟩)).sum) =
      UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn x) *
        (rows.map (RelationRightRow.value n L data hn)).sum := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, mul_add]
      congr 1
      simp [RelationRightRow.value, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.word, adaptedWeightedBasis]
      noncomm_ring

/-- The integral subset-collection identity from the manuscript.  It is an
equality in the enveloping algebra, not merely in an associated graded
object. -/
theorem relationSubsetCollection_value
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn)) :
    ((relationSubsetCollection n L data hn rho xs).map
        (RelationRightRow.value n L data hn)).sum =
      UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
        MarkedRow.basisWord n L data hn xs := by
  induction xs generalizing rho with
  | nil =>
      simp [relationSubsetCollection, RelationRightRow.value,
        MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word]
  | cons x xs ih =>
      rw [relationSubsetCollection, List.map_append, List.sum_append,
        List.map_map]
      change ((relationSubsetCollection n L data hn rho xs).map
            (fun r ↦ RelationRightRow.value n L data hn
              ⟨r.relation, x :: r.ordinary⟩)).sum +
          ((relationSubsetCollection n L data hn
              (relationRightBracket n L data hn rho x) xs).map
            (RelationRightRow.value n L data hn)).sum = _
      rw [relationSubsetCollection_prepend_value,
        ih rho, ih (relationRightBracket n L data hn rho x)]
      have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
        (FreeModel n L) (rho : FreeModel n L)
          (adaptedBasis n L data hn x)
      have hword : MarkedRow.basisWord n L data hn (x :: xs) =
          UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn x) *
            MarkedRow.basisWord n L data hn xs := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      rw [hword]
      change UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn x) *
            (UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) * _) +
          UniversalEnvelopingAlgebra.ι ℤ
              ⁅(rho : FreeModel n L), adaptedBasis n L data hn x⁆ * _ = _
      calc
        _ = (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) *
              UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) +
            UniversalEnvelopingAlgebra.ι ℤ
              ⁅(rho : FreeModel n L), adaptedBasis n L data hn x⁆) *
              MarkedRow.basisWord n L data hn xs := by noncomm_ring
        _ = (UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
              UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x)) *
              MarkedRow.basisWord n L data hn xs := by rw [hswap]
        _ = _ := by noncomm_ring

end

end LieRings.MetabelianVanishing
