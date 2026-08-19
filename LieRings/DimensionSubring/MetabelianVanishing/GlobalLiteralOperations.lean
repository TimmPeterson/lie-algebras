import LieRings.DimensionSubring.MetabelianVanishing.GlobalPacketOccurrences

/-!
# The literal horizontal and vertical operations

This file separates the two operations which were interleaved in the old
normalizer.  `horizontalRow` is one quotient-tower truncation.  The vertical
collector performs the complete deterministic placed-word pass while
retaining every full contextual relation correction.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.DegreeFive

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalLiteralOperationsFintype : Fintype L :=
  Fintype.ofFinite L

/-- One literal marked truncation, fixing rows on which truncation is
unavailable.  The homogeneous output is a component row, never a relation. -/
def horizontalRow : ProvenancedRow n L data hn →
    ProvenancedRow n L data hn →₀ ℤ
  | r@(.component _ _ _ _ _) => Finsupp.single r 1
  | r@(.marked root context mark left right) =>
      if hmark : mark.val = 0 then Finsupp.single r 1
      else
        Finsupp.single
            (.marked root context ⟨mark.val - 1, by omega⟩ left right) 1 +
          Finsupp.single (.component root context mark left right) 1

/-- Linear extension of one horizontal truncation to signed occurrence
lists. -/
def horizontalOperation :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      (ProvenancedRow n L data hn →₀ ℤ) :=
  Finsupp.linearCombination ℤ (horizontalRow n L data hn)

/-- One vertical placed-word rewrite.  Marked rows move their full
contextual relation to the prescribed side and retain the full relation
correction.  Component rows move the exposed component in the opposite
direction and retain the Jacobi correction. -/
def verticalExpansion : ProvenancedRow n L data hn →
    Option (List (ℤ × ProvenancedRow n L data hn))
  | .component root context mark left right =>
      match left.reverse with
      | [] => none
      | x :: leftRev =>
          some [(1, .component root context mark leftRev.reverse (x :: right)),
            (-1, .component root (RelationContext.lieRight context x) mark
              leftRev.reverse right)]
  | .marked root context mark left right =>
      match right with
      | [] => none
      | x :: rest =>
          some [(1, .marked root context mark (left ++ [x]) rest),
            (1, .marked root (RelationContext.lieRight context x) mark
              left rest)]

/-! ## The two literal summands of a marked truncation -/

/-- The value of the lower-mark child of a row.  It is zero when a marked
row has already reached mark zero, and on a component row because that row
has no marked child.  Keeping this as a value-valued function is useful for
the closed-square calculation: it does not identify any route labels. -/
def lowerMarkedValue : ProvenancedRow n L data hn →
    UEA ℤ (FreeModel n L)
  | .component _ _ _ _ _ => 0
  | .marked root context mark left right =>
      if hmark : mark.val = 0 then 0
      else
        (ProvenancedRow.marked root context
          ⟨mark.val - 1, by omega⟩ left right :
            ProvenancedRow n L data hn).value

/-- The complementary homogeneous-child value in one marked truncation.
It is defined as the literal difference, so the decomposition is valid also
at mark zero and on component rows without separate exceptional cases. -/
def horizontalComponentValue (r : ProvenancedRow n L data hn) :
    UEA ℤ (FreeModel n L) :=
  r.value - lowerMarkedValue n L data hn r

theorem value_eq_lowerMarkedValue_add_horizontalComponentValue
    (r : ProvenancedRow n L data hn) :
    r.value = lowerMarkedValue n L data hn r +
      horizontalComponentValue n L data hn r := by
  simp [horizontalComponentValue]

/-- For a genuine marked truncation, the complementary value is exactly
the displayed homogeneous component child. -/
theorem horizontalComponentValue_marked_of_pos
    (root : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2)) (left right : List (AdaptedIndex n L data hn))
    (hmark : mark.val ≠ 0) :
    horizontalComponentValue n L data hn
        (.marked root context mark left right) =
      (ProvenancedRow.component root context mark left right :
        ProvenancedRow n L data hn).value := by
  have hstep := RelationContext.prefix_step n L data hn
    context root mark (Nat.pos_of_ne_zero hmark)
  simp only [horizontalComponentValue, lowerMarkedValue, hmark, dite_false,
    ProvenancedRow.value]
  rw [hstep, map_add, mul_add]
  noncomm_ring

/-- The separated vertical rewrite is literally the corresponding branch
of the audited provenance-preserving expansion. -/
theorem verticalExpansion_eq_provenancedExpansion_of_some
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows) :
    provenancedExpansion n L data hn r = some rows := by
  cases r with
  | component root context mark left right =>
      cases hleft : left.reverse with
      | nil => simp [verticalExpansion, hleft] at h
      | cons x leftRev =>
          simp only [verticalExpansion, hleft, Option.some.injEq] at h
          subst rows
          rw [provenancedExpansion, hleft]
  | marked root context mark left right =>
      cases right with
      | nil => simp [verticalExpansion] at h
      | cons x rest => simpa only [verticalExpansion, provenancedExpansion] using h

/-- Every vertical output strictly lowers the existing row measure. -/
theorem verticalExpansion_decreases
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows) :
    ∀ q ∈ rows,
      rowMeasureLt (provenancedMeasure n L data hn q.2)
        (provenancedMeasure n L data hn r) := by
  exact provenancedExpansion_decreases n L data hn
    (verticalExpansion_eq_provenancedExpansion_of_some n L data hn h)

/-- A vertical rewrite preserves literal evaluation, including every
full-relation and Jacobi correction. -/
theorem verticalExpansion_preserves
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows) :
    (rows.map fun q ↦ q.1 • q.2.value).sum = r.value := by
  exact provenancedExpansion_preserves n L data hn
    (verticalExpansion_eq_provenancedExpansion_of_some n L data hn h)

/-- Lowering the quotient mark commutes with the complete vertical rewrite
at the level of literal evaluated sums.  This is the value-valued form of
the marked transfer--truncation square. -/
theorem verticalExpansion_preserves_lowerMarkedValue
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows) :
    (rows.map fun q ↦ q.1 • lowerMarkedValue n L data hn q.2).sum =
      lowerMarkedValue n L data hn r := by
  cases r with
  | component root context mark left right =>
      cases hleft : left.reverse with
      | nil => simp [verticalExpansion, hleft] at h
      | cons x leftRev =>
          simp only [verticalExpansion, hleft, Option.some.injEq] at h
          subst rows
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            lowerMarkedValue, smul_zero, add_zero]
  | marked root context mark left right =>
      cases right with
      | nil => simp [verticalExpansion] at h
      | cons x rest =>
          simp only [verticalExpansion, Option.some.injEq] at h
          subst rows
          by_cases hmark : mark.val = 0
          · simp only [List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil, lowerMarkedValue, hmark, dite_true, smul_zero,
              add_zero]
          · have hlower := verticalExpansion_preserves n L data hn
                (r := (ProvenancedRow.marked root context
                  ⟨mark.val - 1, by omega⟩ left (x :: rest) :
                    ProvenancedRow n L data hn))
                (rows :=
                  [(1, .marked root context ⟨mark.val - 1, by omega⟩
                      (left ++ [x]) rest),
                    (1, .marked root (RelationContext.lieRight context x)
                      ⟨mark.val - 1, by omega⟩ left rest)])
                (by rfl)
            have hmark' : mark ≠ 0 := by
              intro hz
              apply hmark
              exact congrArg Fin.val hz
            simpa [lowerMarkedValue, hmark, hmark'] using hlower

/-- The complementary homogeneous-child value is preserved by the vertical
rewrite as well.  This follows from preservation of the whole row and of the
lower-mark summand, so no local component is ever retyped as a relation. -/
theorem verticalExpansion_preserves_horizontalComponentValue
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : verticalExpansion n L data hn r = some rows) :
    (rows.map fun q ↦ q.1 • horizontalComponentValue n L data hn q.2).sum =
      horizontalComponentValue n L data hn r := by
  rw [horizontalComponentValue]
  simp_rw [horizontalComponentValue, smul_sub]
  have hsum (xs : List (ℤ × ProvenancedRow n L data hn)) :
      (xs.map fun q ↦
          q.1 • q.2.value - q.1 • lowerMarkedValue n L data hn q.2).sum =
        (xs.map fun q ↦ q.1 • q.2.value).sum -
          (xs.map fun q ↦
            q.1 • lowerMarkedValue n L data hn q.2).sum := by
    induction xs with
    | nil => simp
    | cons q xs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        abel
  rw [hsum rows]
  rw [verticalExpansion_preserves n L data hn h,
    verticalExpansion_preserves_lowerMarkedValue n L data hn h]

/-- The complete deterministic vertical pass. -/
def verticalCollector :
    FiniteTaggedCollector (ProvenancedRow n L data hn)
      (UEA ℤ (FreeModel n L)) where
  relation x y := rowMeasureLt (provenancedMeasure n L data hn x)
    (provenancedMeasure n L data hn y)
  wellFounded := InvImage.wf (provenancedMeasure n L data hn)
    rowMeasureLt_wellFounded
  expansion := verticalExpansion n L data hn
  value := ProvenancedRow.value n L data hn
  decreases := verticalExpansion_decreases n L data hn
  preserves := verticalExpansion_preserves n L data hn

/-- Linear read of the lower-mark summand on a row ledger. -/
def lowerMarkedLinear :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      UEA ℤ (FreeModel n L) :=
  Finsupp.linearCombination ℤ (lowerMarkedValue n L data hn)

/-- The complete vertical pass preserves the lower-mark summand.  The proof
uses the same well-founded recursion as the collector, with the local
transfer--truncation square proved above as its only rewrite input. -/
theorem lowerMarkedLinear_normalForm
    (r : ProvenancedRow n L data hn) :
    lowerMarkedLinear n L data hn
        ((verticalCollector n L data hn).normalForm r) =
      lowerMarkedValue n L data hn r := by
  classical
  let C := verticalCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : verticalExpansion n L data hn r with
      | none =>
          rw [C.normalForm_eq_single_of_terminal hexp]
          simp [lowerMarkedLinear]
      | some rows =>
          rw [C.normalForm_eq_sum_of_expansion r rows hexp, map_list_sum]
          calc
            ((rows.map fun q ↦
                q.1 • C.normalForm q.2).map
                (lowerMarkedLinear n L data hn)).sum =
                (rows.map fun q ↦
                  q.1 • lowerMarkedValue n L data hn q.2).sum := by
                    apply congrArg List.sum
                    rw [List.map_map]
                    apply List.map_congr_left
                    intro q hq
                    simp only [Function.comp_apply, map_zsmul]
                    rw [ih q.2 (C.decreases hexp q hq)]
            _ = _ := verticalExpansion_preserves_lowerMarkedValue
              n L data hn hexp

/-- Linear read of the complementary homogeneous summand. -/
def horizontalComponentLinear :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      UEA ℤ (FreeModel n L) :=
  Finsupp.linearCombination ℤ
    (horizontalComponentValue n L data hn)

/-- The complete vertical pass preserves the complementary homogeneous
summand as a whole. -/
theorem horizontalComponentLinear_normalForm
    (r : ProvenancedRow n L data hn) :
    horizontalComponentLinear n L data hn
        ((verticalCollector n L data hn).normalForm r) =
      horizontalComponentValue n L data hn r := by
  classical
  let C := verticalCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : verticalExpansion n L data hn r with
      | none =>
          rw [C.normalForm_eq_single_of_terminal hexp]
          simp [horizontalComponentLinear]
      | some rows =>
          rw [C.normalForm_eq_sum_of_expansion r rows hexp, map_list_sum]
          calc
            ((rows.map fun q ↦
                q.1 • C.normalForm q.2).map
                (horizontalComponentLinear n L data hn)).sum =
                (rows.map fun q ↦
                  q.1 • horizontalComponentValue
                    n L data hn q.2).sum := by
                    apply congrArg List.sum
                    rw [List.map_map]
                    apply List.map_congr_left
                    intro q hq
                    simp only [Function.comp_apply, map_zsmul]
                    rw [ih q.2 (C.decreases hexp q hq)]
            _ = _ := verticalExpansion_preserves_horizontalComponentValue
              n L data hn hexp

/-- Linear extension of the complete vertical pass. -/
def verticalOperation :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      (ProvenancedRow n L data hn →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun r ↦ (verticalCollector n L data hn).normalForm r)

/-- One horizontal truncation preserves the literal enveloping-algebra
value. -/
theorem evaluate_horizontalRow (r : ProvenancedRow n L data hn) :
    Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
        (horizontalRow n L data hn r) = r.value := by
  classical
  cases r with
  | component root context mark left right =>
      simp [horizontalRow]
  | marked root context mark left right =>
      by_cases hmark : mark.val = 0
      · simp [horizontalRow, hmark]
      · have hstep := RelationContext.prefix_step n L data hn
          context root mark (Nat.pos_of_ne_zero hmark)
        rw [horizontalRow, dif_neg hmark, map_add]
        simp only [Finsupp.linearCombination_single, one_smul,
          ProvenancedRow.value]
        rw [hstep, map_add]
        noncomm_ring

/-- Horizontal truncation preserves evaluation on every signed list. -/
theorem evaluate_horizontalOperation
    (rows : ProvenancedRow n L data hn →₀ ℤ) :
    Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
        (horizontalOperation n L data hn rows) =
      Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
        rows := by
  classical
  rw [horizontalOperation]
  change Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
      (rows.sum fun r z ↦ z • horizontalRow n L data hn r) = _
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul, evaluate_horizontalRow n L data hn r]
  rfl

/-- The complete vertical pass preserves evaluation on every signed list. -/
theorem evaluate_verticalOperation
    (rows : ProvenancedRow n L data hn →₀ ℤ) :
    Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
        (verticalOperation n L data hn rows) =
      Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
        rows := by
  classical
  rw [verticalOperation]
  change Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
      (rows.sum fun r z ↦ z •
        (verticalCollector n L data hn).normalForm r) = _
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul]
  exact congrArg (fun x ↦ rows r • x)
    ((verticalCollector n L data hn).evaluate_normalForm r)

/-- Canonical placed-basis expansion of a signed row list.  Its coefficients
are the integral PBW coordinates for the fixed adapted weighted basis.  In
particular, this deliberately forgets route labels only *after* literal
evaluation; raw occurrence lists are not identified. -/
def canonicalPlacedExpansion :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      MvPolynomial (AdaptedIndex n L data hn) ℤ :=
  (adaptedWeightedBasis n L data hn).pbwEquiv.symm.toLinearMap.comp
    (Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn))

/-- The horizontal and vertical operations commute coefficientwise after
canonical placed-basis expansion.  The proof uses the exact literal
transfer/truncation identities above and PBW uniqueness; it makes no claim
that the two raw provenance-labelled lists are equal. -/
theorem canonicalPlacedExpansion_horizontal_vertical
    (rows : ProvenancedRow n L data hn →₀ ℤ) :
    canonicalPlacedExpansion n L data hn
        (horizontalOperation n L data hn
          (verticalOperation n L data hn rows)) =
      canonicalPlacedExpansion n L data hn
        (verticalOperation n L data hn
          (horizontalOperation n L data hn rows)) := by
  apply (adaptedWeightedBasis n L data hn).pbwEquiv.injective
  simp only [canonicalPlacedExpansion, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]
  rw [evaluate_horizontalOperation, evaluate_verticalOperation,
    evaluate_verticalOperation, evaluate_horizontalOperation]

/-- Coefficient form of `canonicalPlacedExpansion_horizontal_vertical`.
This is the incidence-group equality used for gluing comparison cells. -/
theorem canonicalPlacedCoefficient_horizontal_vertical
    (rows : ProvenancedRow n L data hn →₀ ℤ)
    (e : AdaptedIndex n L data hn →₀ ℕ) :
    canonicalPlacedExpansion n L data hn
        (horizontalOperation n L data hn
          (verticalOperation n L data hn rows)) e =
      canonicalPlacedExpansion n L data hn
        (verticalOperation n L data hn
          (horizontalOperation n L data hn rows)) e :=
  congrArg (fun f ↦ f e)
    (canonicalPlacedExpansion_horizontal_vertical n L data hn rows)

/-- Every nontrivial horizontal output strictly lowers the existing measure. -/
theorem horizontalRow_decreases
    (root : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2)) (left right : List (AdaptedIndex n L data hn))
    (hmark : mark.val ≠ 0)
    (q : ProvenancedRow n L data hn)
    (hq : horizontalRow n L data hn
        (.marked root context mark left right) q ≠ 0) :
    rowMeasureLt (provenancedMeasure n L data hn q)
      (provenancedMeasure n L data hn
        (.marked root context mark left right)) := by
  classical
  rw [horizontalRow, dif_neg hmark, Finsupp.add_apply] at hq
  by_cases hlower : q = .marked root context
      ⟨mark.val - 1, by omega⟩ left right
  · subst q
    simp only [provenancedMeasure]
    unfold rowMeasureLt
    apply Prod.Lex.right
    apply Prod.Lex.right
    change mark.val - 1 < mark.val
    omega
  · have hcomponent : q = .component root context mark left right := by
      by_contra hne
      simp [hlower, hne] at hq
    subst q
    simp only [provenancedMeasure]
    unfold rowMeasureLt
    apply Prod.Lex.left
    omega

/-- The genuinely available horizontal replacement.  Unlike
`horizontalRow`, which fixes unavailable rows so that it extends linearly,
this partial operation exposes the two literal children and is therefore
suited to the occurrence ledger. -/
def horizontalExpansion : ProvenancedRow n L data hn →
    Option (List (ℤ × ProvenancedRow n L data hn))
  | .component _ _ _ _ _ => none
  | .marked root context mark left right =>
      if hmark : mark.val = 0 then none
      else some
        [(1, .marked root context ⟨mark.val - 1, by omega⟩ left right),
          (1, .component root context mark left right)]

/-- The occurrence replacement underlying `horizontalRow` is exactly its
two-child marked truncation. -/
theorem horizontalRow_eq_sum_of_expansion
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : horizontalExpansion n L data hn r = some rows) :
    horizontalRow n L data hn r =
      (rows.map fun q ↦ Finsupp.single q.2 q.1).sum := by
  classical
  cases r with
  | component => simp [horizontalExpansion] at h
  | marked root context mark left right =>
      simp only [horizontalExpansion] at h
      split at h
      · contradiction
      · rename_i hmark
        rw [Option.some.injEq] at h
        subst rows
        simp [horizontalRow, hmark]

/-- Every child of an available horizontal replacement strictly decreases
the same lexicographic row measure used by the vertical pass. -/
theorem horizontalExpansion_decreases
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : horizontalExpansion n L data hn r = some rows) :
    ∀ q ∈ rows,
      rowMeasureLt (provenancedMeasure n L data hn q.2)
        (provenancedMeasure n L data hn r) := by
  classical
  cases r with
  | component => simp [horizontalExpansion] at h
  | marked root context mark left right =>
      simp only [horizontalExpansion] at h
      split at h
      · contradiction
      · rename_i hmark
        rw [Option.some.injEq] at h
        subst rows
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact horizontalRow_decreases n L data hn root context mark left right
            hmark _ (by simp [horizontalRow, hmark])
        · exact horizontalRow_decreases n L data hn root context mark left right
            hmark _ (by simp [horizontalRow, hmark])

/-- The literal two-child horizontal replacement preserves evaluation. -/
theorem horizontalExpansion_preserves
    {r : ProvenancedRow n L data hn}
    {rows : List (ℤ × ProvenancedRow n L data hn)}
    (h : horizontalExpansion n L data hn r = some rows) :
    (rows.map fun q ↦ q.1 • q.2.value).sum = r.value := by
  classical
  have hrows := horizontalRow_eq_sum_of_expansion n L data hn h
  have heval := evaluate_horizontalRow n L data hn r
  rw [hrows] at heval
  rw [map_list_sum] at heval
  have hmap :
      ((rows.map fun q ↦ Finsupp.single q.2 q.1).map
          (Finsupp.linearCombination ℤ
            (ProvenancedRow.value n L data hn))) =
        rows.map fun q ↦ q.1 • q.2.value := by
    rw [List.map_map]
    apply List.map_congr_left
    intro q hq
    simpa only [Function.comp_apply] using
      (Finsupp.linearCombination_single (R := ℤ)
        (v := ProvenancedRow.value n L data hn) q.1 q.2)
  rw [hmap] at heval
  exact heval

/-- Well-founded occurrence collector for repeated marked truncation.  Its
trace is the horizontal spine of the uncut comparison complex. -/
def horizontalCollector :
    FiniteTaggedCollector (ProvenancedRow n L data hn)
      (UEA ℤ (FreeModel n L)) where
  relation x y := rowMeasureLt (provenancedMeasure n L data hn x)
    (provenancedMeasure n L data hn y)
  wellFounded := InvImage.wf (provenancedMeasure n L data hn)
    rowMeasureLt_wellFounded
  expansion := horizontalExpansion n L data hn
  value := ProvenancedRow.value n L data hn
  decreases := horizontalExpansion_decreases n L data hn
  preserves := horizontalExpansion_preserves n L data hn

end

end LieRings.MetabelianVanishing
