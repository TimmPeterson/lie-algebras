import LieRings.DimensionSubring.MetabelianVanishing.GlobalSaturatedTrace

/-!
# Internal gluing of the uncut trace

The horizontal children are kept as a literal coefficient list.  Only after
that list has been formed do we sum their bases.  The resulting successor
right incidence is exactly the negative of the parent's left incidence.
Thus each numbered horizontal output is present before canonical expansion,
while the gluing equality is valid coefficientwise in the fixed PBW basis.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalInternalGluingFintype : Fintype L :=
  Fintype.ofFinite L

namespace LabelledComparisonCell

/-- The numbered horizontal children, with ancestry coefficients already
multiplied but without combining equal underlying rows. -/
def horizontalSuccessorBases (c : LabelledComparisonCell n L data hn) :
    List (ProvenancedRow n L data hn →₀ ℤ) :=
  c.horizontalOutputs.map fun q ↦
    Finsupp.single q.2 (c.coefficient * q.1)

/-- Sum of the literal numbered horizontal child bases. -/
def horizontalSuccessorAggregate
    (c : LabelledComparisonCell n L data hn) :
    ProvenancedRow n L data hn →₀ ℤ :=
  (c.horizontalSuccessorBases n L data hn).sum

/-- The occurrence-level horizontal output list is exactly `H` applied to
the parent coefficient copy. -/
theorem horizontalSuccessorAggregate_eq
    (c : LabelledComparisonCell n L data hn) :
    c.horizontalSuccessorAggregate n L data hn =
      horizontalOperation n L data hn (c.cell n L data hn).base := by
  classical
  have hrow := horizontalRow_eq_sum_of_expansion n L data hn c.horizontal_eq
  calc
    c.horizontalSuccessorAggregate n L data hn =
        (c.horizontalOutputs.map fun q ↦
          c.coefficient • Finsupp.single q.2 q.1).sum := by
      rw [horizontalSuccessorAggregate, horizontalSuccessorBases]
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      simp [Finsupp.smul_single]
    _ = c.coefficient •
        (c.horizontalOutputs.map fun q ↦ Finsupp.single q.2 q.1).sum := by
      rw [List.smul_sum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      rfl
    _ = c.coefficient • horizontalRow n L data hn c.input := by
      rw [hrow]
    _ = horizontalOperation n L data hn (c.cell n L data hn).base := by
      simp [cell, horizontalOperation]

/-- Sum of the right incidences based at every horizontal child.  It is
written via the aggregate only after the numbered list has been retained. -/
def horizontalSuccessorRightIncidence
    (c : LabelledComparisonCell n L data hn) :
    ProvenancedRow n L data hn →₀ ℤ :=
  -c.horizontalSuccessorAggregate n L data hn +
    verticalOperation n L data hn
      (c.horizontalSuccessorAggregate n L data hn)

/-- The right incidence belonging to each literal numbered horizontal
successor before any equal rows are combined. -/
def numberedHorizontalSuccessorRightIncidences
    (c : LabelledComparisonCell n L data hn) :
    List (ProvenancedRow n L data hn →₀ ℤ) :=
  (c.horizontalSuccessorBases n L data hn).map fun b ↦
    -b + verticalOperation n L data hn b

/-- Summing the numbered successor incidences gives the aggregate successor
right incidence.  This equality is proved only after retaining the literal
list of coefficient copies. -/
theorem sum_numberedHorizontalSuccessorRightIncidences
    (c : LabelledComparisonCell n L data hn) :
    (c.numberedHorizontalSuccessorRightIncidences n L data hn).sum =
      c.horizontalSuccessorRightIncidence n L data hn := by
  rw [numberedHorizontalSuccessorRightIncidences,
    horizontalSuccessorRightIncidence, horizontalSuccessorAggregate]
  generalize c.horizontalSuccessorBases n L data hn = bases
  induction bases with
  | nil => simp
  | cons b bases ih =>
      simp only [List.map_cons, List.sum_cons, List.sum_nil]
      rw [map_add, ih]
      abel

/-- For an internal successor, its retained numbered incidence is exactly
the right edge of the unique adjacent comparison cell. -/
theorem horizontalSuccessorCell_right_eq
    (c : LabelledComparisonCell n L data hn)
    (i : Fin c.horizontalOutputs.length)
    (horizontalOutputs : List (ℤ × ProvenancedRow n L data hn))
    (hhorizontal : horizontalExpansion n L data hn
      (c.horizontalOutputs.get i).2 = some horizontalOutputs)
    (verticalOutputs : List (ℤ × ProvenancedRow n L data hn))
    (hvertical : verticalExpansion n L data hn
      (c.horizontalOutputs.get i).2 = some verticalOutputs) :
    ((c.horizontalSuccessorCell n L data hn i horizontalOutputs hhorizontal
      verticalOutputs hvertical).cell n L data hn).right n L data hn =
      -Finsupp.single (c.horizontalOutputs.get i).2
          (c.coefficient * (c.horizontalOutputs.get i).1) +
        verticalOperation n L data hn
          (Finsupp.single (c.horizontalOutputs.get i).2
            (c.coefficient * (c.horizontalOutputs.get i).1)) := by
  rfl

/-- Exact internal gluing: the parent's left incidence and all numbered
horizontal-successor right incidences occur with opposite orientations. -/
theorem left_add_horizontalSuccessorRightIncidence_eq_zero
    (c : LabelledComparisonCell n L data hn) :
    (c.cell n L data hn).left n L data hn +
        c.horizontalSuccessorRightIncidence n L data hn = 0 := by
  rw [horizontalSuccessorRightIncidence,
    horizontalSuccessorAggregate_eq]
  simp only [ComparisonCell.left]
  abel

/-- Coefficientwise canonical form of the internal gluing identity.  Since
the parent path is stored in `c` and the children were numbered before the
sum, this is the precise incidence pairing used by the cut trace. -/
theorem canonical_horizontal_internal_gluing
    (c : LabelledComparisonCell n L data hn) :
    canonicalPlacedExpansion n L data hn
      ((c.cell n L data hn).left n L data hn +
        c.horizontalSuccessorRightIncidence n L data hn) = 0 := by
  rw [left_add_horizontalSuccessorRightIncidence_eq_zero, map_zero]

/-- Coefficient-copy form of internal gluing.  For every placed PBW basis
index, the coefficient on the parent's left incidence is the negative of
the aggregate coefficient on its numbered horizontal successors' right
incidences.  The numbered successor list is retained by
`horizontalSuccessorBases`; only its canonical basis coefficients are
compared here. -/
theorem canonical_left_coefficient_eq_neg_successor_right
    (c : LabelledComparisonCell n L data hn)
    (e : AdaptedIndex n L data hn →₀ ℕ) :
    canonicalPlacedExpansion n L data hn
        (c.cell n L data hn).left e =
      -canonicalPlacedExpansion n L data hn
        (c.horizontalSuccessorRightIncidence n L data hn) e := by
  have h := congrArg (fun f ↦ f e)
    (c.canonical_horizontal_internal_gluing n L data hn)
  rw [map_add] at h
  have h' : canonicalPlacedExpansion n L data hn
          (c.cell n L data hn).left e +
        canonicalPlacedExpansion n L data hn
          (c.horizontalSuccessorRightIncidence n L data hn) e = 0 := by
    simpa using h
  exact eq_neg_of_add_eq_zero_left h'

end LabelledComparisonCell

end


end LieRings.MetabelianVanishing
