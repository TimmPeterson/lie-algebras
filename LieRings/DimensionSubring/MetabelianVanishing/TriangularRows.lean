import LieRings.DimensionSubring.MetabelianVanishing.ClosedSquare
import LieRings.DimensionSubring.MetabelianVanishing.TriangularBasis

/-!
# Triangular full-relation rows in the free metabelian model

This is the filtration used in the proof of the closed-square row lemma.  A
row chosen in weight `s+1` is an actual element of the kernel of evaluation,
has no component below `s`, and has a single Smith head in weight `s`.
Homogeneous tails are never regarded as relations.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance triangularRowsFintype : Fintype L := Fintype.ofFinite L

local instance triangularRowsPieceFree (s : ℕ) :
    Module.Free ℤ (FreeMetabelian.Piece (Generator L) s) :=
  Module.Free.of_basis (FreeMetabelian.Free.pieceBasis (generatorBasis L) s)

local instance triangularRowsPieceFinite (s : ℕ) :
    Module.Finite ℤ (FreeMetabelian.Piece (Generator L) s) :=
  Module.Finite.of_basis (FreeMetabelian.Free.pieceBasis (generatorBasis L) s)

/-- A genuine filtered relation lifting one Smith leading row. -/
def triangularRelationRow (s : ℕ) (hs : s < n + 1)
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s) :
    FilteredRelations n L data s := by
  let d : RelationLeading n L data s hs :=
    (triangularSmith n L data s hs).relationBasis i
  exact ⟨Classical.choose d.property, (Classical.choose_spec d.property).1⟩

theorem triangularRelationRow_head
    (s : ℕ) (hs : s < n + 1)
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s) :
    FreeMetabelian.Free.weightProject s hs
        (triangularRelationRow n L data s hs i : FreeModel n L) =
      ((triangularSmith n L data s hs).diagonal i : ℤ) •
        triangularPieceBasis n L data s hs i := by
  unfold triangularRelationRow
  dsimp only
  rw [(Classical.choose_spec
    ((triangularSmith n L data s hs).relationBasis i).property).2]
  exact (triangularSmith n L data s hs).relation_eq i

theorem triangularRelationRow_head_relationBasis
    (s : ℕ) (hs : s < n + 1)
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s) :
    FreeMetabelian.Free.weightProject s hs
        (triangularRelationRow n L data s hs i : FreeModel n L) =
      ((triangularSmith n L data s hs).relationBasis i :
        RelationLeading n L data s hs) := by
  unfold triangularRelationRow
  dsimp only
  exact (Classical.choose_spec
    ((triangularSmith n L data s hs).relationBasis i).property).2

theorem triangularRelationRow_mem_relations
    (s : ℕ) (hs : s < n + 1)
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s) :
    evaluation n L data
      (triangularRelationRow n L data s hs i : FreeModel n L) = 0 :=
  (triangularRelationRow n L data s hs i).property.1

theorem triangularRelationRow_mem_tail
    (s : ℕ) (hs : s < n + 1)
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s) :
    (triangularRelationRow n L data s hs i : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) s :=
  (triangularRelationRow n L data s hs i).property.2

/-- The chosen full-relation rows, extended linearly from the Smith basis of
the leading-relation module. -/
def triangularRelationRowLift (s : ℕ) (hs : s < n + 1) :
    RelationLeading n L data s hs →ₗ[ℤ] FilteredRelations n L data s :=
  (triangularSmith n L data s hs).relationBasis.constr ℤ
    (triangularRelationRow n L data s hs)

@[simp]
theorem triangularRelationRowLift_basis
    (s : ℕ) (hs : s < n + 1)
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s) :
    triangularRelationRowLift n L data s hs
        ((triangularSmith n L data s hs).relationBasis i) =
      triangularRelationRow n L data s hs i := by
  rw [triangularRelationRowLift, Module.Basis.constr_basis]

/-- The leading coordinate of a filtered full relation, retaining the proof
that it is the image of that same full relation. -/
def filteredRelationLeading (s : ℕ) (hs : s < n + 1)
    (r : FilteredRelations n L data s) :
    RelationLeading n L data s hs :=
  ⟨FreeMetabelian.Free.weightProject s hs (r : FreeModel n L),
    ⟨r, r.property, rfl⟩⟩

/-- Taking the leading coordinate after recombining the chosen full rows is
the inclusion of the leading-relation module. -/
theorem weightProject_triangularRelationRowLift
    (s : ℕ) (hs : s < n + 1)
    (d : RelationLeading n L data s hs) :
    FreeMetabelian.Free.weightProject s hs
      (triangularRelationRowLift n L data s hs d : FreeModel n L) = d := by
  let P := triangularSmith n L data s hs
  let f : RelationLeading n L data s hs →ₗ[ℤ]
      FreeMetabelian.Piece (Generator L) s :=
    (FreeMetabelian.Free.weightProject s hs).comp
      ((FilteredRelations n L data s).subtype.comp
        (triangularRelationRowLift n L data s hs))
  have hf : f = (RelationLeading n L data s hs).subtype := by
    apply LinearMap.ext_on_range P.relationBasis.span_eq
    intro i
    dsimp only [f, LinearMap.comp_apply]
    rw [triangularRelationRowLift_basis]
    change FreeMetabelian.Free.weightProject s hs
        (triangularRelationRow n L data s hs i : FreeModel n L) =
      ((P.relationBasis i : RelationLeading n L data s hs) :
        FreeMetabelian.Piece (Generator L) s)
    simpa only [P] using
      triangularRelationRow_head_relationBasis n L data s hs i
  exact LinearMap.congr_fun hf d

/-- Subtract the integral combination of triangular rows having the same
weight-`s+1` head.  This is still represented as a full relation. -/
def triangularRelationRemainder
    (s : ℕ) (hs : s < n + 1)
    (r : FilteredRelations n L data s) : FreeModel n L :=
  (r : FreeModel n L) -
    (triangularRelationRowLift n L data s hs
      (filteredRelationLeading n L data s hs r) : FreeModel n L)

theorem triangularRelationRemainder_mem_relations
    (s : ℕ) (hs : s < n + 1)
    (r : FilteredRelations n L data s) :
    evaluation n L data (triangularRelationRemainder n L data s hs r) = 0 := by
  rw [triangularRelationRemainder, map_sub]
  have hr : evaluation n L data (r : FreeModel n L) = 0 := r.property.1
  rw [hr]
  have hl : evaluation n L data
      ((triangularRelationRowLift n L data s hs
        (filteredRelationLeading n L data s hs r) :
          FilteredRelations n L data s) : FreeModel n L) = 0 :=
    (triangularRelationRowLift n L data s hs
      (filteredRelationLeading n L data s hs r)).property.1
  rw [hl, sub_zero]

theorem triangularRelationRemainder_mem_tail_succ
    (s : ℕ) (hs : s < n + 1)
    (r : FilteredRelations n L data s) :
    triangularRelationRemainder n L data s hs r ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) (s + 1) := by
  rw [FreeMetabelian.Free.mem_tail_iff]
  intro i hi
  by_cases his : i.val < s
  · change (r : FreeModel n L) i -
        (triangularRelationRowLift n L data s hs
          (filteredRelationLeading n L data s hs r) : FreeModel n L) i = 0
    rw [r.property.2 i his]
    have hl := (triangularRelationRowLift n L data s hs
      (filteredRelationLeading n L data s hs r)).property.2
    rw [hl i his, sub_zero]
  · have hieq : i = ⟨s, hs⟩ := by
      apply Fin.ext
      simp only
      omega
    subst i
    change FreeMetabelian.Free.weightProject s hs (r : FreeModel n L) -
        FreeMetabelian.Free.weightProject s hs
          (triangularRelationRowLift n L data s hs
            (filteredRelationLeading n L data s hs r) : FreeModel n L) = 0
    rw [weightProject_triangularRelationRowLift]
    exact sub_self _

/-- The remainder is a genuine relation whose first possible component is
the next weight. -/
def triangularRelationRemainderFilteredSucc
    (s : ℕ) (hs : s < n + 1)
    (r : FilteredRelations n L data s) :
    FilteredRelations n L data (s + 1) :=
  ⟨triangularRelationRemainder n L data s hs r,
    triangularRelationRemainder_mem_relations n L data s hs r,
    triangularRelationRemainder_mem_tail_succ n L data s hs r⟩

/-- Exact one-stage triangular decomposition.  No homogeneous tail is ever
asserted to be a relation: both summands on the right come from full kernel
elements. -/
theorem filteredRelation_eq_rowLift_add_remainder
    (s : ℕ) (hs : s < n + 1)
    (r : FilteredRelations n L data s) :
    (r : FreeModel n L) =
      (triangularRelationRowLift n L data s hs
        (filteredRelationLeading n L data s hs r) : FreeModel n L) +
      (triangularRelationRemainderFilteredSucc n L data s hs r :
        FreeModel n L) := by
  unfold triangularRelationRemainderFilteredSucc triangularRelationRemainder
  module

/-- Forget the filtration proof on one chosen triangular row, while retaining
the proof that it is a full defining relation. -/
def triangularRelation
    (s : ℕ) (hs : s < n + 1)
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s) :
    Relations n L data :=
  ⟨(triangularRelationRow n L data s hs i : FreeModel n L),
    triangularRelationRow_mem_relations n L data s hs i⟩

/-- An index of the triangular relation basis, including its declared
leading weight.  Keeping this tag is essential during PBW placement: the
full relation itself is carried by the row, while this index tells the
collector where its Smith head belongs. -/
abbrev TriangularRelationIndex :=
  (s : Fin (n + 1)) ×
    FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s.val

/-- The genuine full relation indexed by a triangular basis tag. -/
def triangularRelationOfIndex
    (i : TriangularRelationIndex n L) : Relations n L data :=
  triangularRelation n L data i.1.val i.1.isLt i.2

/-! ## The homogeneous PBW basis belonging to the triangular Smith rows -/

/-- Weight-first indices for the PBW basis in which a triangular relation
has a single leading basis vector. -/
abbrev TriangularPBWIndex :=
  (s : Fin (n + 1)) ×
    FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s.val

private def triangularPBWIndexCode :
    TriangularPBWIndex n L → ℕ ×ₗ ℕ :=
  fun i ↦ toLex (i.1.val, (Finite.equivFin _ i.2).val)

private theorem triangularPBWIndexCode_injective :
    Function.Injective (triangularPBWIndexCode n L) := by
  rintro ⟨s, i⟩ ⟨t, j⟩ h
  simp only [triangularPBWIndexCode, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq] at h
  rcases h with ⟨hst, hij⟩
  have hs : s = t := Fin.ext hst
  subst t
  have hi : i = j := (Finite.equivFin _).injective (Fin.ext hij)
  subst j
  rfl

noncomputable instance : LinearOrder (TriangularPBWIndex n L) :=
  LinearOrder.lift' (triangularPBWIndexCode n L)
    (triangularPBWIndexCode_injective n L)

/-- The direct-sum basis assembled from the ambient Smith bases chosen in
every homogeneous relation-leading quotient. -/
def triangularPBWBasis :
    Module.Basis (TriangularPBWIndex n L) ℤ (FreeModel n L) :=
  Pi.basis (fun s ↦ triangularPieceBasis n L data s.val s.isLt)

@[simp] theorem triangularPBWBasis_apply (i : TriangularPBWIndex n L) :
    triangularPBWBasis n L data i =
      FreeMetabelian.Free.weightIncl i.1.val i.1.isLt
        (triangularPieceBasis n L data i.1.val i.1.isLt i.2) := by
  rw [triangularPBWBasis, Pi.basis_apply]
  rfl

private theorem triangularPBW_bracket_homogeneous
    (i j k : TriangularPBWIndex n L)
    (h : (triangularPBWBasis n L data).repr
      ⁅triangularPBWBasis n L data i,
        triangularPBWBasis n L data j⁆ k ≠ 0) :
    k.1.val + 1 = (i.1.val + 1) + (j.1.val + 1) := by
  by_contra hweight
  apply h
  have hv : ⁅triangularPBWBasis n L data i,
      triangularPBWBasis n L data j⁆ k.1 = 0 := by
    rw [triangularPBWBasis_apply, triangularPBWBasis_apply]
    exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
      i.1.val j.1.val i.1.isLt j.1.isLt
      (triangularPieceBasis n L data i.1.val i.1.isLt i.2)
      (triangularPieceBasis n L data j.1.val j.1.isLt j.2) k.1 (by omega)
  change ((triangularPieceBasis n L data k.1.val k.1.isLt).repr
    (⁅triangularPBWBasis n L data i,
      triangularPBWBasis n L data j⁆ k.1)) k.2 = 0
  rw [hv, map_zero]
  rfl

private theorem triangularPBW_iota_mem_augmentation_pow
    (s : ℕ) {x : FreeModel n L}
    (hx : x ∈ lowerCentralSeries ℤ (FreeModel n L) s) :
    UniversalEnvelopingAlgebra.ι ℤ x ∈
      UEA.augmentationIdeal ℤ (FreeModel n L) ^ (s + 1) := by
  exact (mem_dimensionSubring ℤ (FreeModel n L)).mp
    (lowerCentralSeries_le_dimensionSubring ℤ (FreeModel n L) s hx)

/-- The weight-compatible PBW basis used by the literal triangular
collector.  This is deliberately distinct from the terminal `p/q`-adapted
basis; the later presentation comparison performs that change of basis. -/
def triangularWeightedBasis :
    LieRings.PBW.WeightedBasis
      (L := FreeModel n L) (ι := TriangularPBWIndex n L) where
  basis := triangularPBWBasis n L data
  weight i := i.1.val + 1
  weight_pos i := by omega
  bracket_homogeneous := triangularPBW_bracket_homogeneous n L data
  iota_mem_augmentation_pow i := by
    apply triangularPBW_iota_mem_augmentation_pow
      (n := n) (L := L) i.1.val
    rw [triangularPBWBasis_apply]
    exact FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
      (generatorBasis L) i.1.val i.1.isLt _

/-- A homogeneous piece is recovered by the exact one-factor projection for
the triangular PBW basis.  This is the triangular-coordinate counterpart of
`adapted_proj_iota_weightIncl`; it is needed to read the governing equation
after the relation module has been put in its invariant-factor basis. -/
theorem triangular_proj_iota_weightIncl (s : ℕ) (hs : s < n + 1)
    (x : FreeMetabelian.Piece (Generator L) s) :
    (triangularWeightedBasis n L data).proj (s + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl s hs x) := by
  let b := triangularPieceBasis n L data s hs
  rw [← b.sum_repr x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  have hb : FreeMetabelian.Free.weightIncl s hs (b i) =
      triangularPBWBasis n L data ⟨⟨s, hs⟩, i⟩ := by
    dsimp only [b]
    exact (triangularPBWBasis_apply n L data ⟨⟨s, hs⟩, i⟩).symm
  rw [hb]
  have hp := (triangularWeightedBasis n L data).proj_iota_basis
    ⟨⟨s, hs⟩, i⟩ (s + 1) 1
  change (triangularWeightedBasis n L data).proj (s + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ
        (triangularPBWBasis n L data ⟨⟨s, hs⟩, i⟩)) = _ at hp
  rw [hp]
  simp [triangularWeightedBasis]

/-- Every other exact bidegree of a homogeneous enveloping inclusion is zero
also in the triangular PBW coordinates. -/
theorem triangular_proj_iota_weightIncl_eq_zero
    (s : ℕ) (hs : s < n + 1)
    (x : FreeMetabelian.Piece (Generator L) s) (w p : ℕ)
    (hne : w ≠ s + 1 ∨ p ≠ 1) :
    (triangularWeightedBasis n L data).proj w p
        (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x)) = 0 := by
  let b := triangularPieceBasis n L data s hs
  rw [← b.sum_repr x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_eq_zero
  intro i hi
  have hb : FreeMetabelian.Free.weightIncl s hs (b i) =
      triangularPBWBasis n L data ⟨⟨s, hs⟩, i⟩ := by
    dsimp only [b]
    exact (triangularPBWBasis_apply n L data ⟨⟨s, hs⟩, i⟩).symm
  rw [hb]
  have hp := (triangularWeightedBasis n L data).proj_iota_basis
    ⟨⟨s, hs⟩, i⟩ w p
  change (triangularWeightedBasis n L data).proj w p
      (UniversalEnvelopingAlgebra.ι ℤ
        (triangularPBWBasis n L data ⟨⟨s, hs⟩, i⟩)) = _ at hp
  rw [hp]
  split_ifs with hwp
  · have hsw : s + 1 = w := by
      simpa only [triangularWeightedBasis] using hwp.1
    exact (hne.elim (fun h ↦ h hsw.symm) (fun h ↦ h hwp.2)).elim
  · simp

/-- The PBW basis index which is the head of a tagged triangular relation. -/
def triangularHeadIndex (i : TriangularRelationIndex n L) :
    TriangularPBWIndex n L := i

theorem triangularRelationOfIndex_head (i : TriangularRelationIndex n L) :
    FreeMetabelian.Free.weightProject i.1.val i.1.isLt
        (triangularRelationOfIndex n L data i : FreeModel n L) =
      ((triangularSmith n L data i.1.val i.1.isLt).diagonal i.2 : ℤ) •
        triangularPieceBasis n L data i.1.val i.1.isLt i.2 := by
  exact triangularRelationRow_head n L data i.1.val i.1.isLt i.2

theorem triangularRelationOfIndex_mem_tail
    (i : TriangularRelationIndex n L) :
    (triangularRelationOfIndex n L data i : FreeModel n L) ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) i.1.val :=
  triangularRelationRow_mem_tail n L data i.1.val i.1.isLt i.2

/-- The homogeneous tail of one triangular relation after removing its
single Smith head.  It is an element of the free Lie ring, not a relation. -/
def triangularRelationTail (i : TriangularRelationIndex n L) :
    FreeModel n L :=
  (triangularRelationOfIndex n L data i : FreeModel n L) -
    FreeMetabelian.Free.weightIncl i.1.val i.1.isLt
      (((triangularSmith n L data i.1.val i.1.isLt).diagonal i.2 : ℤ) •
        triangularPieceBasis n L data i.1.val i.1.isLt i.2)

theorem triangularRelation_eq_head_add_tail
    (i : TriangularRelationIndex n L) :
    (triangularRelationOfIndex n L data i : FreeModel n L) =
      FreeMetabelian.Free.weightIncl i.1.val i.1.isLt
        (((triangularSmith n L data i.1.val i.1.isLt).diagonal i.2 : ℤ) •
          triangularPieceBasis n L data i.1.val i.1.isLt i.2) +
        triangularRelationTail n L data i := by
  unfold triangularRelationTail
  module

theorem triangularRelationTail_mem_tail_succ
    (i : TriangularRelationIndex n L) :
    triangularRelationTail n L data i ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) (i.1.val + 1) := by
  rw [FreeMetabelian.Free.mem_tail_iff]
  intro j hj
  change (triangularRelationOfIndex n L data i : FreeModel n L) j -
      FreeMetabelian.Free.weightIncl i.1.val i.1.isLt
        (((triangularSmith n L data i.1.val i.1.isLt).diagonal i.2 : ℤ) •
          triangularPieceBasis n L data i.1.val i.1.isLt i.2) j = 0
  by_cases hjs : j.val < i.1.val
  · rw [(triangularRelationOfIndex_mem_tail n L data i) j hjs]
    change 0 - FreeMetabelian.Free.incl i.1
      (((triangularSmith n L data i.1.val i.1.isLt).diagonal i.2 : ℤ) •
        triangularPieceBasis n L data i.1.val i.1.isLt i.2) j = 0
    rw [FreeMetabelian.Free.incl_apply_of_ne]
    · exact sub_zero 0
    · intro heq
      have := congrArg Fin.val heq
      omega
  · have hjeq : j = i.1 := by
      apply Fin.ext
      omega
    subst j
    change (triangularRelationOfIndex n L data i : FreeModel n L) i.1 -
      FreeMetabelian.Free.incl i.1
        (((triangularSmith n L data i.1.val i.1.isLt).diagonal i.2 : ℤ) •
          triangularPieceBasis n L data i.1.val i.1.isLt i.2) i.1 = 0
    rw [FreeMetabelian.Free.incl_apply_same]
    change FreeMetabelian.Free.weightProject i.1.val i.1.isLt
          (triangularRelationOfIndex n L data i : FreeModel n L) -
        (((triangularSmith n L data i.1.val i.1.isLt).diagonal i.2 : ℤ) •
          triangularPieceBasis n L data i.1.val i.1.isLt i.2) = 0
    rw [triangularRelationOfIndex_head]
    exact sub_self _

/-- Tagged coefficients of the triangular rows realizing one leading
component.  Unlike `triangularLeadingExpansion`, this version cannot forget
the leading weight of a row. -/
def triangularLeadingTaggedExpansion
    (s : ℕ) (hs : s < n + 1)
    (d : RelationLeading n L data s hs) :
    TriangularRelationIndex n L →₀ ℤ :=
  ((triangularSmith n L data s hs).relationBasis.repr d).sum
    (fun i z ↦
      let sf : Fin (n + 1) := ⟨s, hs⟩
      let ii : FreeMetabelian.Free.PieceIndex
          (Fin (Nat.card L)) sf.val := by simpa only [sf] using i
      z • Finsupp.single
        (show TriangularRelationIndex n L from ⟨sf, ii⟩) 1)

theorem triangularLeadingTaggedExpansion_value
    (s : ℕ) (hs : s < n + 1)
    (d : RelationLeading n L data s hs) :
    (triangularLeadingTaggedExpansion n L data s hs d).sum
        (fun i z ↦ z •
          (triangularRelationOfIndex n L data i : FreeModel n L)) =
      (triangularRelationRowLift n L data s hs d : FreeModel n L) := by
  classical
  let V : (TriangularRelationIndex n L →₀ ℤ) →ₗ[ℤ] FreeModel n L :=
    Finsupp.linearCombination ℤ (fun i ↦
      (triangularRelationOfIndex n L data i : FreeModel n L))
  change V (triangularLeadingTaggedExpansion n L data s hs d) = _
  rw [triangularLeadingTaggedExpansion, map_finsuppSum]
  simp only [map_zsmul, Finsupp.linearCombination_single, one_smul, V]
  rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
  have hrepr := (triangularSmith n L data s hs).relationBasis.sum_repr d
  have hlift := congrArg (triangularRelationRowLift n L data s hs) hrepr
  have hcoe := congrArg (FilteredRelations n L data s).subtype hlift
  simpa only [map_sum, map_zsmul, triangularRelationOfIndex,
    triangularRelationRowLift_basis] using hcoe

/-- Every nonzero coefficient in a one-stage tagged expansion has exactly
the active leading weight.  This is the support fact which makes the Smith
head of a full row usable as a PBW placement marker. -/
theorem triangularLeadingTaggedExpansion_weight
    (s : ℕ) (hs : s < n + 1)
    (d : RelationLeading n L data s hs)
    (i : TriangularRelationIndex n L)
    (hi : triangularLeadingTaggedExpansion n L data s hs d i ≠ 0) :
    i.1.val = s := by
  classical
  by_contra his
  apply hi
  rw [triangularLeadingTaggedExpansion, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finsupp.smul_apply, smul_eq_mul]
  rw [Finsupp.single_apply]
  split
  · rename_i heq
    have hval := congrArg (fun x : TriangularRelationIndex n L ↦ x.1.val) heq
    simp only at hval
    exact (his hval.symm).elim
  · simp

/-- Finite coefficients of the chosen triangular rows which recombine a
given leading-relation element. -/
def triangularLeadingExpansion
    (s : ℕ) (hs : s < n + 1)
    (d : RelationLeading n L data s hs) :
    Relations n L data →₀ ℤ :=
  ((triangularSmith n L data s hs).relationBasis.repr d).sum
    (fun i z ↦ z • Finsupp.single (triangularRelation n L data s hs i) 1)

theorem triangularLeadingExpansion_value
    (s : ℕ) (hs : s < n + 1)
    (d : RelationLeading n L data s hs) :
    (triangularLeadingExpansion n L data s hs d).sum
        (fun rho z ↦ z • (rho : FreeModel n L)) =
      (triangularRelationRowLift n L data s hs d : FreeModel n L) := by
  classical
  let V : (Relations n L data →₀ ℤ) →ₗ[ℤ] FreeModel n L :=
    Finsupp.linearCombination ℤ (fun rho ↦ (rho : FreeModel n L))
  change V (triangularLeadingExpansion n L data s hs d) = _
  rw [triangularLeadingExpansion, map_finsuppSum]
  simp only [map_zsmul, Finsupp.linearCombination_single, one_smul, V]
  simp only [triangularRelation]
  rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
  have hrepr := (triangularSmith n L data s hs).relationBasis.sum_repr d
  have hlift := congrArg (triangularRelationRowLift n L data s hs) hrepr
  have hcoe := congrArg (FilteredRelations n L data s).subtype hlift
  simpa only [map_sum, map_zsmul,
    triangularRelationRowLift_basis] using hcoe

/-- Every full relation is filtered from weight one onward (zero-based
coordinate `0`). -/
def relationAsFilteredZero (rho : Relations n L data) :
    FilteredRelations n L data 0 :=
  ⟨(rho : FreeModel n L), rho.property, by
    change ∀ i : Fin (n + 1), i.val < 0 → (rho : FreeModel n L) i = 0
    intro i hi
    omega⟩

/-- Iterate the triangular elimination until the nilpotence cutoff.  The
equation `s + fuel = n+1` makes termination and the final zero remainder
literal. -/
def triangularExpansionFrom :
    (fuel s : ℕ) → s + fuel = n + 1 →
      FilteredRelations n L data s → Relations n L data →₀ ℤ
  | 0, _s, _hcut, _r => 0
  | fuel + 1, s, hcut, r =>
      triangularLeadingExpansion n L data s (by omega)
          (filteredRelationLeading n L data s (by omega) r) +
        triangularExpansionFrom fuel (s + 1) (by omega)
          (triangularRelationRemainderFilteredSucc n L data s (by omega) r)

theorem triangularExpansionFrom_value
    (fuel s : ℕ) (hcut : s + fuel = n + 1)
    (r : FilteredRelations n L data s) :
    (triangularExpansionFrom n L data fuel s hcut r).sum
        (fun rho z ↦ z • (rho : FreeModel n L)) =
      (r : FreeModel n L) := by
  classical
  induction fuel generalizing s with
  | zero =>
      have hs : s = n + 1 := by omega
      have hr : (r : FreeModel n L) ∈
          FreeMetabelian.Free.tail
            (X := Generator L) (c := n + 1) (n + 1) := by
        simpa only [hs] using r.property.2
      rw [FreeMetabelian.Free.tail_cutoff_eq_bot] at hr
      simp only [triangularExpansionFrom, Finsupp.sum_zero]
      simpa using hr.symm
  | succ fuel ih =>
      rw [triangularExpansionFrom, Finsupp.sum_add_index]
      · rw [triangularLeadingExpansion_value,
          ih (s := s + 1) (hcut := by omega)]
        exact (filteredRelation_eq_rowLift_add_remainder
          n L data s (by omega) r).symm
      · intro rho
        simp
      · intro rho a b
        simp [add_smul]

/-- Tagged triangular elimination through the finite weight cutoff. -/
def triangularTaggedExpansionFrom :
    (fuel s : ℕ) → s + fuel = n + 1 →
      FilteredRelations n L data s →
        TriangularRelationIndex n L →₀ ℤ
  | 0, _s, _hcut, _r => 0
  | fuel + 1, s, hcut, r =>
      triangularLeadingTaggedExpansion n L data s (by omega)
          (filteredRelationLeading n L data s (by omega) r) +
        triangularTaggedExpansionFrom fuel (s + 1) (by omega)
          (triangularRelationRemainderFilteredSucc n L data s (by omega) r)

theorem triangularTaggedExpansionFrom_value
    (fuel s : ℕ) (hcut : s + fuel = n + 1)
    (r : FilteredRelations n L data s) :
    (triangularTaggedExpansionFrom n L data fuel s hcut r).sum
        (fun i z ↦ z •
          (triangularRelationOfIndex n L data i : FreeModel n L)) =
      (r : FreeModel n L) := by
  classical
  induction fuel generalizing s with
  | zero =>
      have hs : s = n + 1 := by omega
      have hr : (r : FreeModel n L) ∈
          FreeMetabelian.Free.tail
            (X := Generator L) (c := n + 1) (n + 1) := by
        simpa only [hs] using r.property.2
      rw [FreeMetabelian.Free.tail_cutoff_eq_bot] at hr
      simp only [triangularTaggedExpansionFrom, Finsupp.sum_zero]
      simpa using hr.symm
  | succ fuel ih =>
      rw [triangularTaggedExpansionFrom, Finsupp.sum_add_index]
      · rw [triangularLeadingTaggedExpansion_value,
          ih (s := s + 1) (hcut := by omega)]
        exact (filteredRelation_eq_rowLift_add_remainder
          n L data s (by omega) r).symm
      · intro i
        simp
      · intro i a b
        simp [add_smul]

/-- Tagged elimination never introduces a Smith head below the filtration
level at which it starts. -/
theorem triangularTaggedExpansionFrom_weight_ge
    (fuel s : ℕ) (hcut : s + fuel = n + 1)
    (r : FilteredRelations n L data s)
    (i : TriangularRelationIndex n L)
    (hi : triangularTaggedExpansionFrom n L data fuel s hcut r i ≠ 0) :
    s ≤ i.1.val := by
  classical
  induction fuel generalizing s with
  | zero =>
      simp [triangularTaggedExpansionFrom] at hi
  | succ fuel ih =>
      rw [triangularTaggedExpansionFrom, Finsupp.add_apply] at hi
      by_cases hlead : triangularLeadingTaggedExpansion n L data s
          (by omega) (filteredRelationLeading n L data s (by omega) r) i ≠ 0
      · have hw := triangularLeadingTaggedExpansion_weight n L data s
          (by omega) (filteredRelationLeading n L data s (by omega) r) i hlead
        omega
      · have htail : triangularTaggedExpansionFrom n L data fuel (s + 1)
            (by omega)
            (triangularRelationRemainderFilteredSucc n L data s (by omega) r) i ≠ 0 := by
          intro hz
          have hlead0 : triangularLeadingTaggedExpansion n L data s
              (by omega) (filteredRelationLeading n L data s (by omega) r) i = 0 :=
            not_ne_iff.mp hlead
          rw [hlead0, hz, add_zero] at hi
          exact hi rfl
        have hw := ih (s := s + 1) (hcut := by omega)
          (triangularRelationRemainderFilteredSucc n L data s (by omega) r)
          htail
        omega

/-- The finite tagged triangular expansion of a full relation. -/
def triangularTaggedExpansion (rho : Relations n L data) :
    TriangularRelationIndex n L →₀ ℤ :=
  triangularTaggedExpansionFrom n L data (n + 1) 0 (by omega)
    (relationAsFilteredZero n L data rho)

theorem triangularTaggedExpansion_value (rho : Relations n L data) :
    (triangularTaggedExpansion n L data rho).sum
        (fun i z ↦ z •
          (triangularRelationOfIndex n L data i : FreeModel n L)) =
      (rho : FreeModel n L) := by
  exact triangularTaggedExpansionFrom_value n L data (n + 1) 0 (by omega)
    (relationAsFilteredZero n L data rho)

/-- The finite triangular expansion of an arbitrary defining relation. -/
def triangularExpansion (rho : Relations n L data) :
    Relations n L data →₀ ℤ :=
  triangularExpansionFrom n L data (n + 1) 0 (by omega)
    (relationAsFilteredZero n L data rho)

/-- The triangular expansion is an integral equality of full relations. -/
theorem triangularExpansion_value (rho : Relations n L data) :
    (triangularExpansion n L data rho).sum
        (fun sigma z ↦ z • (sigma : FreeModel n L)) =
      (rho : FreeModel n L) := by
  exact triangularExpansionFrom_value n L data (n + 1) 0 (by omega)
    (relationAsFilteredZero n L data rho)

/-- Replace one relation-on-the-left row by its finite triangular full-row
expansion, leaving the right enveloping factor untouched. -/
def triangularizeRelationRow
    (p : Relations n L data × UEA ℤ (FreeModel n L)) :
    (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ :=
  (triangularExpansion n L data p.1).sum (fun sigma c ↦
    c • Finsupp.single (sigma, p.2) 1)

theorem terminalPacketWord_triangularizeRelationRow
    (p : Relations n L data × UEA ℤ (FreeModel n L)) :
    terminalPacketWord n L data (triangularizeRelationRow n L data p) =
      UniversalEnvelopingAlgebra.ι ℤ (p.1 : FreeModel n L) * p.2 := by
  classical
  rw [← terminalPacketWordLinear_apply,
    triangularizeRelationRow, map_finsuppSum]
  simp only [map_zsmul, Finsupp.linearCombination_single, one_smul,
    terminalPacketWordLinear]
  let rightMul : UEA ℤ (FreeModel n L) →+ UEA ℤ (FreeModel n L) :=
    AddMonoidHom.mulRight p.2
  simp_rw [← smul_mul_assoc, ← map_zsmul]
  change (triangularExpansion n L data p.1).sum
      (fun sigma c ↦ rightMul
        (UniversalEnvelopingAlgebra.ι ℤ
          (c • (sigma : FreeModel n L)))) =
    rightMul (UniversalEnvelopingAlgebra.ι ℤ (p.1 : FreeModel n L))
  rw [← map_finsuppSum]
  congr 1
  rw [← map_finsuppSum, triangularExpansion_value]

/-- Simultaneously triangularize every relation occurrence in a finite
relative row chain. -/
def triangularizeRelationRows
    (rows : (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ) :
    (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ :=
  rows.sum (fun p z ↦ z • triangularizeRelationRow n L data p)

/-- Triangularization is a literal equality in the enveloping algebra; it
does not change the chosen relative-chain boundary. -/
theorem terminalPacketWord_triangularizeRelationRows
    (rows : (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ) :
    terminalPacketWord n L data (triangularizeRelationRows n L data rows) =
      terminalPacketWord n L data rows := by
  classical
  rw [← terminalPacketWordLinear_apply,
    triangularizeRelationRows, map_finsuppSum]
  simp only [map_zsmul, terminalPacketWordLinear_apply]
  simp_rw [terminalPacketWord_triangularizeRelationRow]
  rfl

/-- The governing relative chain after the manuscript's triangular-basis
expansion. -/
def GoverningWitness.triangularRelationCoefficients {a : L}
    (w : GoverningWitness n L data a) :
    (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ :=
  triangularizeRelationRows n L data w.relationCoefficients

theorem GoverningWitness.triangularTheta_eq_theta {a : L}
    (w : GoverningWitness n L data a) :
    terminalPacketWord n L data
        (w.triangularRelationCoefficients n L data) = w.theta := by
  rw [GoverningWitness.triangularRelationCoefficients,
    terminalPacketWord_triangularizeRelationRows]
  rfl

/-- The same governing expansion with the leading-weight tags retained. -/
def GoverningWitness.triangularTaggedRelationCoefficients {a : L}
    (w : GoverningWitness n L data a) :
    (TriangularRelationIndex n L × UEA ℤ (FreeModel n L)) →₀ ℤ :=
  w.relationCoefficients.sum (fun p z ↦ z •
    (triangularTaggedExpansion n L data p.1).sum (fun i c ↦
      c • Finsupp.single (i, p.2) 1))

theorem GoverningWitness.triangularTaggedTheta_eq_theta {a : L}
    (w : GoverningWitness n L data a) :
    (w.triangularTaggedRelationCoefficients n L data).sum
        (fun p z ↦ z •
          (UniversalEnvelopingAlgebra.ι ℤ
              (triangularRelationOfIndex n L data p.1 : FreeModel n L) *
            p.2)) = w.theta := by
  classical
  rw [GoverningWitness.triangularTaggedRelationCoefficients,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  rw [GoverningWitness.theta]
  apply Finsupp.sum_congr
  intro p hp
  rw [Finsupp.sum_smul_index (fun _ ↦ by simp)]
  rw [Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  let rightMul : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    { toFun := fun r ↦ UniversalEnvelopingAlgebra.ι ℤ r * p.2
      map_add' := by intro x y; rw [map_add, add_mul]
      map_smul' := by
        intro z x
        rw [map_zsmul, smul_mul_assoc]
        rfl }
  have hcollect :
      ((triangularTaggedExpansion n L data p.1).sum fun i c ↦
          (c • Finsupp.single (i, p.2) 1).sum fun j d ↦
            (w.relationCoefficients p * d) •
              (UniversalEnvelopingAlgebra.ι ℤ
                  (triangularRelationOfIndex n L data j.1 : FreeModel n L) *
                j.2)) =
        w.relationCoefficients p •
          (triangularTaggedExpansion n L data p.1).sum fun i c ↦
            c • rightMul
              (triangularRelationOfIndex n L data i : FreeModel n L) := by
    rw [Finsupp.smul_sum]
    apply Finsupp.sum_congr
    intro i hi
    rw [Finsupp.sum_smul_index (fun _ ↦ by simp)]
    rw [Finsupp.sum_single_index (by simp)]
    dsimp only [rightMul]
    module
  rw [hcollect]
  have hvalue := congrArg rightMul
    (triangularTaggedExpansion_value n L data p.1)
  rw [map_finsuppSum] at hvalue
  simpa only [map_zsmul, rightMul, mul_smul_comm] using
    congrArg (fun x ↦ w.relationCoefficients p • x) hvalue

/-- The governing PBW coefficient statement in the triangular homogeneous
basis.  This is the coefficient equation used by the Smith-head row ledger;
it follows from the same governing equality as the adapted-basis statement
and therefore makes no basis-change assumption. -/
theorem GoverningWitness.triangularTheta_proj {a : L}
    (w : GoverningWitness n L data a)
    (weight factors : ℕ) (hsmall : weight ≤ 2 * n) :
    (triangularWeightedBasis n L data).proj weight factors w.theta =
      if weight = n + 1 ∧ factors = 1 then
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl n (by omega) w.atilde)
      else 0 := by
  have hhigh : (triangularWeightedBasis n L data).proj weight factors
      w.highWord = 0 := by
    have hmem : w.highWord ∈
        (triangularWeightedBasis n L data).weightGE (2 * n + 1) := by
      rw [← (triangularWeightedBasis n L data).augmentationIdeal_pow_eq_weightGE]
      exact w.highWord_mem
    apply LieRings.PBW.WeightedBasis.proj_eq_zero_of_mem_weightGE
      (B := triangularWeightedBasis n L data)
      (r := 2 * n + 1) (w := weight) (p := factors) hmem
    omega
  have heq := congrArg
    (fun z ↦ (triangularWeightedBasis n L data).proj weight factors z)
    w.theta_sub_iota
  simp only [map_sub, map_neg, hhigh, map_zero, neg_zero,
    sub_eq_zero] at heq
  rw [heq]
  by_cases h : weight = n + 1 ∧ factors = 1
  · rcases h with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩]
    exact triangular_proj_iota_weightIncl n L data n (by omega) w.atilde
  · rw [if_neg h]
    exact triangular_proj_iota_weightIncl_eq_zero n L data n (by omega)
      w.atilde weight factors (by tauto)

end

end LieRings.MetabelianVanishing
