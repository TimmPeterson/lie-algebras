import LieRings.DimensionSubring.MetabelianVanishing.FactorCollector

/-!
# The quotient-weight pass of the closed-square collector

The factor-first pass leaves a genuine full relation in every row.  This
file performs the second pass from the manuscript.  At active zero-based
weight `s` the mark denotes the *tail* `rho_{>=s}` of that same full
relation.  A transfer replaces its correction by the corresponding tail of
the full relation `[rho,x]`; a weight step exposes only the homogeneous head
and retains `rho` as the mark.  Thus no homogeneous component is ever
relabelled as a relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance quotientWeightCollectorFintype : Fintype L := Fintype.ofFinite L

/-! ## Literal tail identities -/

/-- The part of a free-model element in zero-based weights at least `s`. -/
def rowTail (s : ℕ) (hs : s ≤ n + 1) :
    FreeModel n L →ₗ[ℤ] FreeModel n L :=
  LinearMap.id - rowTruncation n L s hs

@[simp] theorem rowTail_zero (x : FreeModel n L) :
    rowTail n L 0 (by omega) x = x := by
  rw [rowTail, LinearMap.sub_apply, LinearMap.id_apply,
    rowTruncation_zero n L hn, sub_zero]

@[simp] theorem rowTail_cutoff (x : FreeModel n L) :
    rowTail n L (n + 1) le_rfl x = 0 := by
  rw [rowTail, LinearMap.sub_apply, LinearMap.id_apply,
    rowTruncation_top n L, sub_self]

/-- Successive tails differ by precisely one homogeneous coordinate. -/
theorem rowTail_eq_head_add_succ (s : ℕ) (hs : s < n + 1)
    (x : FreeModel n L) :
    rowTail n L s (by omega) x =
      FreeMetabelian.Free.weightIncl s hs
          (FreeMetabelian.Free.weightProject s hs x) +
        rowTail n L (s + 1) (by omega) x := by
  rw [rowTail, rowTail, LinearMap.sub_apply, LinearMap.sub_apply,
    rowTruncation_succ n L s hs x]
  abel

/-- A tail has no coordinate below its declared bound. -/
theorem rowTail_mem_tail (s : ℕ) (hs : s ≤ n + 1)
    (x : FreeModel n L) :
    rowTail n L s hs x ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) s := by
  exact RelationContext.sub_rowTruncation_mem_tail n L x s hs

/-- Bracketing a tail by one homogeneous basis element is the corresponding
tail of the full bracket.  This is the transfer--truncation square in the
orientation used by the second pass. -/
theorem rowTail_lie_basis
    (rho : Relations n L data) (s : ℕ) (hs : s ≤ n + 1)
    (v : TriangularPBWIndex n L) :
    ⁅rowTail n L s hs (rho : FreeModel n L),
        triangularPBWBasis n L data v⁆ =
      rowTail n L (min (n + 1) (s + v.1.val + 1)) (by omega)
        (triangularRelationRightBracket n L data rho v : FreeModel n L) := by
  funext i
  by_cases hcut : n + 1 ≤ s + v.1.val + 1
  · have hright : rowTail n L (min (n + 1) (s + v.1.val + 1))
        (by omega)
        (triangularRelationRightBracket n L data rho v : FreeModel n L) = 0 := by
      simpa only [min_eq_left hcut] using
        rowTail_cutoff n L
          (triangularRelationRightBracket n L data rho v : FreeModel n L)
    rw [hright, Pi.zero_apply, triangularPBWBasis_apply]
    have hmem := RelationContext.bracket_weightIncl_right_mem_tail n L
      (rowTail n L s hs (rho : FreeModel n L)) s v.1.val v.1.isLt
      (rowTail_mem_tail n L s hs (rho : FreeModel n L))
      (triangularPieceBasis n L data v.1.val v.1.isLt v.2)
    apply hmem
    omega
  · have hlt : s + v.1.val + 1 < n + 1 := by omega
    have hright : rowTail n L (min (n + 1) (s + v.1.val + 1))
          (by omega)
          (triangularRelationRightBracket n L data rho v : FreeModel n L) =
        rowTail n L (s + v.1.val + 1) (by omega)
          (triangularRelationRightBracket n L data rho v : FreeModel n L) := by
      have heq :
          (⟨min (n + 1) (s + v.1.val + 1), by omega⟩ :
              {j : ℕ // j ≤ n + 1}) =
            ⟨s + v.1.val + 1, by omega⟩ := by
        apply Subtype.ext
        exact min_eq_right (by omega)
      exact congrArg
        (fun t : {j : ℕ // j ≤ n + 1} ↦
          rowTail n L t.1 t.2
            (triangularRelationRightBracket n L data rho v : FreeModel n L))
        heq
    rw [hright]
    rw [triangularPBWBasis_apply]
    simp only [triangularRelationRightBracket]
    rw [triangularPBWBasis_apply]
    change ⁅rowTail n L s hs (rho : FreeModel n L),
        FreeMetabelian.Free.weightIncl v.1.val v.1.isLt
          (triangularPieceBasis n L data v.1.val v.1.isLt v.2)⁆ i =
      rowTail n L (s + v.1.val + 1) (by omega)
        (⁅(rho : FreeModel n L),
          FreeMetabelian.Free.weightIncl v.1.val v.1.isLt
            (triangularPieceBasis n L data v.1.val v.1.isLt v.2)⁆) i
    by_cases hi : i.val < s + v.1.val + 1
    · have hleft := RelationContext.bracket_weightIncl_right_mem_tail n L
        (rowTail n L s hs (rho : FreeModel n L)) s v.1.val v.1.isLt
        (rowTail_mem_tail n L s hs (rho : FreeModel n L))
        (triangularPieceBasis n L data v.1.val v.1.isLt v.2)
      rw [hleft i hi]
      change 0 = ((⁅(rho : FreeModel n L),
          FreeMetabelian.Free.weightIncl v.1.val v.1.isLt
            (triangularPieceBasis n L data v.1.val v.1.isLt v.2)⁆) -
          rowTruncation n L (s + v.1.val + 1) (by omega)
            (⁅(rho : FreeModel n L),
              FreeMetabelian.Free.weightIncl v.1.val v.1.isLt
                (triangularPieceBasis n L data v.1.val v.1.isLt v.2)⁆)) i
      simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
        FreeMetabelian.Free.projectPrefix,
        show i.val ≤ s + v.1.val from by omega]
    · have hdrop : ∀ j : Fin (n + 1), j.val < s →
          ⁅FreeMetabelian.Free.incl j
              (FreeMetabelian.Free.project j (rho : FreeModel n L)),
            FreeMetabelian.Free.weightIncl v.1.val v.1.isLt
              (triangularPieceBasis n L data v.1.val v.1.isLt v.2)⁆ i = 0 := by
        intro j hj
        simpa only [FreeMetabelian.Free.weightIncl,
          FreeMetabelian.Free.weightProject] using
            FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
              j.val v.1.val j.isLt v.1.isLt
              (FreeMetabelian.Free.weightProject j.val j.isLt
                (rho : FreeModel n L))
              (triangularPieceBasis n L data v.1.val v.1.isLt v.2) i
              (by omega)
      change ⁅(rho : FreeModel n L) -
          rowTruncation n L s hs (rho : FreeModel n L),
        FreeMetabelian.Free.weightIncl v.1.val v.1.isLt
          (triangularPieceBasis n L data v.1.val v.1.isLt v.2)⁆ i = _
      rw [sub_lie]
      have hprefix : ⁅rowTruncation n L s hs (rho : FreeModel n L),
          FreeMetabelian.Free.weightIncl v.1.val v.1.isLt
            (triangularPieceBasis n L data v.1.val v.1.isLt v.2)⁆ i = 0 := by
        have hp := FreeMetabelian.Free.sum_incl_project
          (rowTruncation n L s hs (rho : FreeModel n L))
        have hpbr := congrArg (fun z : FreeModel n L ↦
          ⁅z, FreeMetabelian.Free.weightIncl v.1.val v.1.isLt
            (triangularPieceBasis n L data v.1.val v.1.isLt v.2)⁆) hp
        simp only [sum_lie] at hpbr
        have hpcoord := congrFun hpbr i
        rw [Finset.sum_apply] at hpcoord
        rw [← hpcoord]
        apply Finset.sum_eq_zero
        intro j hj
        by_cases hjs : j.val < s
        · have hcoord : FreeMetabelian.Free.project j
              (rowTruncation n L s hs (rho : FreeModel n L)) =
                FreeMetabelian.Free.project j (rho : FreeModel n L) := by
            change rowTruncation n L s hs (rho : FreeModel n L) j =
              (rho : FreeModel n L) j
            simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
              FreeMetabelian.Free.projectPrefix, hjs]
          rw [hcoord]
          exact hdrop j hjs
        · have hz : FreeMetabelian.Free.project j
              (rowTruncation n L s hs (rho : FreeModel n L)) = 0 := by
            change rowTruncation n L s hs (rho : FreeModel n L) j = 0
            simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
              FreeMetabelian.Free.projectPrefix, hjs]
          rw [hz, map_zero, zero_lie]
          rfl
      rw [Pi.sub_apply, hprefix, sub_zero]
      change ⁅(rho : FreeModel n L),
          FreeMetabelian.Free.weightIncl v.1.val v.1.isLt
            (triangularPieceBasis n L data v.1.val v.1.isLt v.2)⁆ i = _
      change _ = ((⁅(rho : FreeModel n L), _⁆) -
        rowTruncation n L (s + v.1.val + 1) (by omega)
          (⁅(rho : FreeModel n L), _⁆)) i
      simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
        FreeMetabelian.Free.projectPrefix,
        show ¬i.val ≤ s + v.1.val from by omega]

/-! ## Rows for the second pass -/

/-- A second-pass row is either an ordinary triangular PBW word or a tail of
one genuine full relation placed between two ordinary words. -/
inductive QuotientWeightRow
  | ordinary (word : List (TriangularPBWIndex n L))
  | marked (left : List (TriangularPBWIndex n L))
      (relation : Relations n L data) (bound : Fin (n + 2))
      (right : List (TriangularPBWIndex n L))

noncomputable instance : DecidableEq (QuotientWeightRow n L data) :=
  Classical.decEq _

namespace QuotientWeightRow

def basisWord (xs : List (TriangularPBWIndex n L)) :
    UEA ℤ (FreeModel n L) :=
  LieRings.PBW.basisWord ℤ (FreeModel n L) (TriangularPBWIndex n L)
    (triangularPBWBasis n L data) xs

def value : QuotientWeightRow n L data → UEA ℤ (FreeModel n L)
  | .ordinary xs => basisWord n L data xs
  | .marked left rho s right =>
      basisWord n L data left *
        UniversalEnvelopingAlgebra.ι ℤ
          (rowTail n L s.val (by omega) (rho : FreeModel n L)) *
        basisWord n L data right

def factorCount : QuotientWeightRow n L data → ℕ
  | .ordinary xs => xs.length
  | .marked left _ _ right => left.length + 1 + right.length

/-- Number of active tail levels still to be exposed.  Ordinary rows have
no marked filtration coordinate. -/
def remaining : QuotientWeightRow n L data → ℕ
  | .ordinary _ => 0
  | .marked _ _ s _ => n + 1 - s.val

def inversions : List (TriangularPBWIndex n L) → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + inversions xs

/-- At a marked row, only factors on the right whose weight precedes the
active tail are unresolved. -/
def unresolved : QuotientWeightRow n L data → ℕ
  | .ordinary xs => inversions n L xs
  | .marked _ _ s right =>
      (right.filter (fun x ↦ x.1.val < s.val)).length

def measure (r : QuotientWeightRow n L data) : ℕ × ℕ × ℕ :=
  (r.factorCount n L, r.remaining n, r.unresolved n L)

end QuotientWeightRow

theorem QuotientWeightRow.inversions_swap
    (left right : List (TriangularPBWIndex n L))
    (x y : TriangularPBWIndex n L) (hyx : y < x) :
    QuotientWeightRow.inversions n L (left ++ x :: y :: right) =
      QuotientWeightRow.inversions n L (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnxy : ¬x < y := not_lt_of_ge (le_of_lt hyx)
      simp [QuotientWeightRow.inversions, hyx, hnxy, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, QuotientWeightRow.inversions]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp <;> omega
      rw [hfilter, ih]
      omega

/-! ## The finite rewrite -/

def triangularCoordinates (x : FreeModel n L) :
    List (ℤ × TriangularPBWIndex n L) :=
  ((triangularPBWBasis n L data).repr x).support.toList.map
    (fun i ↦ (((triangularPBWBasis n L data).repr x) i, i))

theorem triangularCoordinates_sum (x : FreeModel n L) :
    ((triangularCoordinates n L data x).map
      (fun q ↦ q.1 • triangularPBWBasis n L data q.2)).sum = x := by
  classical
  rw [triangularCoordinates, List.map_map,
    ← List.sum_toFinset _ (Finset.nodup_toList _),
    Finset.toList_toFinset]
  exact (triangularPBWBasis n L data).linearCombination_repr x

def quotientOrdinaryCorrection
    (left right : List (TriangularPBWIndex n L))
    (x y : TriangularPBWIndex n L) :
    List (ℤ × QuotientWeightRow n L data) :=
  (triangularCoordinates n L data
    ⁅triangularPBWBasis n L data x,
      triangularPBWBasis n L data y⁆).map
    (fun q ↦ (q.1, .ordinary (left ++ q.2 :: right)))

def quotientTruncationRows
    (left right : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (s : ℕ) (hs : s < n + 1) :
    List (ℤ × QuotientWeightRow n L data) :=
  (triangularCoordinates n L data
    (FreeMetabelian.Free.weightIncl s hs
      (FreeMetabelian.Free.weightProject s hs
        (rho : FreeModel n L)))).map
    (fun q ↦ (q.1, .ordinary (left ++ q.2 :: right)))

/-- Factor-first, then quotient-weight collection.  A factor-one marked row
is retained whole.  At larger factor number, a low right neighbour is
crossed before the active homogeneous head is exposed. -/
noncomputable def quotientWeightExpansion : QuotientWeightRow n L data →
    Option (List (ℤ × QuotientWeightRow n L data))
  | .ordinary xs =>
      match LieRings.DegreeFive.chooseAdjacentInversion? xs with
      | none => none
      | some d => some
          ((1, .ordinary (d.left ++ d.y :: d.x :: d.right)) ::
            quotientOrdinaryCorrection n L data d.left d.right d.x d.y)
  | .marked left rho s right =>
      if hone : left.length + 1 + right.length ≤ 1 then none
      else if hcut : s.val = n + 1 then some []
      else
        match right with
        | v :: rest =>
            if hv : v.1.val < s.val then
              let b : Fin (n + 2) :=
                ⟨min (n + 1) (s.val + v.1.val + 1), by omega⟩
              some [(1, .marked (left ++ [v]) rho s rest),
                (1, .marked left
                  (triangularRelationRightBracket n L data rho v) b rest)]
            else
              let s' : Fin (n + 2) := ⟨s.val + 1, by omega⟩
              some ((1, .marked left rho s' right) ::
                quotientTruncationRows n L data left right rho s.val (by omega))
        | [] =>
            let s' : Fin (n + 2) := ⟨s.val + 1, by omega⟩
            some ((1, .marked left rho s' []) ::
              quotientTruncationRows n L data left [] rho s.val (by omega))

private theorem quotientWeightExpansion_factorCount_le
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (h : quotientWeightExpansion n L data r = some qs) :
    ∀ q ∈ qs, q.2.factorCount n L ≤ r.factorCount n L := by
  classical
  intro q hq
  cases r with
  | ordinary xs =>
      simp only [quotientWeightExpansion] at h
      split at h <;> try contradiction
      rename_i d hd
      rw [Option.some.injEq] at h
      subst qs
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · obtain ⟨rfl, _⟩ :=
          LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
        simp [QuotientWeightRow.factorCount]
      · rw [quotientOrdinaryCorrection, List.mem_map] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        obtain ⟨rfl, _⟩ :=
          LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
        simp [QuotientWeightRow.factorCount]
  | marked left rho s right =>
      simp only [quotientWeightExpansion] at h
      split at h <;> try contradiction
      split at h
      · rw [Option.some.injEq] at h
        subst qs
        simp at hq
      · split at h
        · rename_i v rest hright
          split at h
          · rw [Option.some.injEq] at h
            subst qs
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl <;>
              simp only [QuotientWeightRow.factorCount,
                List.length_append, List.length_singleton,
                List.length_cons, List.length_nil] <;> omega
          · rw [Option.some.injEq] at h
            subst qs
            simp only [List.mem_cons] at hq
            rcases hq with rfl | hq
            · simp only [QuotientWeightRow.factorCount, List.length_cons]
              omega
            · rw [quotientTruncationRows, List.mem_map] at hq
              obtain ⟨p, hp, rfl⟩ := hq
              simp only [QuotientWeightRow.factorCount,
                List.length_append, List.length_cons]
              omega
        · rename_i hright
          rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · simp only [QuotientWeightRow.factorCount]
            omega
          · rw [quotientTruncationRows, List.mem_map] at hq
            obtain ⟨p, hp, rfl⟩ := hq
            simp only [QuotientWeightRow.factorCount,
              List.length_append, List.length_cons]
            omega

theorem quotientWeightExpansion_decreases
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (h : quotientWeightExpansion n L data r = some qs) :
    ∀ q ∈ qs,
      rowMeasureLt (q.2.measure n L data) (r.measure n L data) := by
  classical
  intro q hq
  cases r with
  | ordinary xs =>
      simp only [quotientWeightExpansion] at h
      split at h <;> try contradiction
      rename_i d hd
      rw [Option.some.injEq] at h
      subst qs
      obtain ⟨hxs, hyx⟩ :=
        LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · rw [hxs]
        unfold rowMeasureLt
        simp only [QuotientWeightRow.measure,
          QuotientWeightRow.factorCount, QuotientWeightRow.remaining,
          QuotientWeightRow.unresolved, List.length_append,
          List.length_cons]
        apply Prod.Lex.right
        apply Prod.Lex.right
        have hswap := QuotientWeightRow.inversions_swap n L
          d.left d.right d.x d.y hyx
        omega
      · rw [quotientOrdinaryCorrection, List.mem_map] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        rw [hxs]
        unfold rowMeasureLt
        simp only [QuotientWeightRow.measure]
        apply Prod.Lex.left
        simp [QuotientWeightRow.measure,
          QuotientWeightRow.factorCount]
  | marked left rho s right =>
      simp only [quotientWeightExpansion] at h
      split at h <;> try contradiction
      rename_i hone
      split at h
      · rw [Option.some.injEq] at h
        subst qs
        simp at hq
      · rename_i hcut
        have hslt : s.val < n + 1 := by omega
        split at h
        · rename_i v rest hright
          split at h
          · rename_i hv
            rw [Option.some.injEq] at h
            subst qs
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · unfold rowMeasureLt
              simp only [QuotientWeightRow.measure]
              rw [show
                QuotientWeightRow.factorCount n L data
                    (.marked (left ++ [v]) rho s rest) =
                  QuotientWeightRow.factorCount n L data
                    (.marked left rho s (v :: rest)) by
                simp [QuotientWeightRow.factorCount]
                omega]
              apply Prod.Lex.right
              apply Prod.Lex.right
              simp [QuotientWeightRow.unresolved, hv]
            · unfold rowMeasureLt
              simp only [QuotientWeightRow.measure]
              apply Prod.Lex.left
              simp only [QuotientWeightRow.measure,
                QuotientWeightRow.factorCount, List.length_cons]
              omega
          · rename_i hv
            rw [Option.some.injEq] at h
            subst qs
            simp only [List.mem_cons] at hq
            rcases hq with rfl | hq
            · unfold rowMeasureLt
              simp only [QuotientWeightRow.measure,
                QuotientWeightRow.factorCount,
                QuotientWeightRow.remaining,
                List.length_cons]
              apply Prod.Lex.right
              apply Prod.Lex.left
              omega
            · rw [quotientTruncationRows, List.mem_map] at hq
              obtain ⟨p, hp, rfl⟩ := hq
              unfold rowMeasureLt
              simp only [QuotientWeightRow.measure]
              rw [show
                QuotientWeightRow.factorCount n L data
                    (.ordinary (left ++ p.2 :: v :: rest)) =
                  QuotientWeightRow.factorCount n L data
                    (.marked left rho s (v :: rest)) by
                simp [QuotientWeightRow.factorCount]
                omega]
              apply Prod.Lex.right
              apply Prod.Lex.left
              simp only [QuotientWeightRow.remaining]
              omega
        · rename_i hright
          rw [Option.some.injEq] at h
          subst qs
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · unfold rowMeasureLt
            simp only [QuotientWeightRow.measure,
              QuotientWeightRow.factorCount,
              QuotientWeightRow.remaining]
            apply Prod.Lex.right
            apply Prod.Lex.left
            omega
          · rw [quotientTruncationRows, List.mem_map] at hq
            obtain ⟨p, hp, rfl⟩ := hq
            unfold rowMeasureLt
            simp only [QuotientWeightRow.measure,
              QuotientWeightRow.factorCount,
              QuotientWeightRow.remaining, List.length_append,
              List.length_cons]
            apply Prod.Lex.right
            apply Prod.Lex.left
            omega

/-! ## Literal preservation of the three rewrite rules -/

/-- Ordinary adjacent interchange in the triangular PBW alphabet. -/
theorem quotientOrdinaryTransfer
    (left right : List (TriangularPBWIndex n L))
    (x y : TriangularPBWIndex n L) :
    QuotientWeightRow.basisWord n L data (left ++ x :: y :: right) =
      QuotientWeightRow.basisWord n L data (left ++ y :: x :: right) +
        QuotientWeightRow.basisWord n L data left *
          UniversalEnvelopingAlgebra.ι ℤ
            ⁅triangularPBWBasis n L data x,
              triangularPBWBasis n L data y⁆ *
          QuotientWeightRow.basisWord n L data right := by
  simpa [QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
    LieRings.PBW.word, LieRings.DegreeFive.envelopingWord] using
    LieRings.DegreeFive.envelopingWord_adjacent_swap ℤ (FreeModel n L)
      (left.map (triangularPBWBasis n L data))
      (right.map (triangularPBWBasis n L data))
      (triangularPBWBasis n L data x)
      (triangularPBWBasis n L data y)

/-- Marked transfer.  The correction mark is the full relation
`[rho,v]`; only its evaluation is restricted to the resulting tail. -/
theorem quotientMarkedTransfer
    (left rest : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (s : Fin (n + 2))
    (v : TriangularPBWIndex n L) :
    (QuotientWeightRow.marked left rho s (v :: rest) :
        QuotientWeightRow n L data).value n L data =
      (QuotientWeightRow.marked (left ++ [v]) rho s rest :
          QuotientWeightRow n L data).value n L data +
        (QuotientWeightRow.marked left
            (triangularRelationRightBracket n L data rho v)
            ⟨min (n + 1) (s.val + v.1.val + 1), by omega⟩ rest :
          QuotientWeightRow n L data).value n L data := by
  let lw := QuotientWeightRow.basisWord n L data left
  let rwrd := QuotientWeightRow.basisWord n L data rest
  let ir := UniversalEnvelopingAlgebra.ι ℤ
    (rowTail n L s.val (by omega) (rho : FreeModel n L))
  let iv := UniversalEnvelopingAlgebra.ι ℤ
    (triangularPBWBasis n L data v)
  let ib := UniversalEnvelopingAlgebra.ι ℤ
    (rowTail n L (min (n + 1) (s.val + v.1.val + 1)) (by omega)
      (triangularRelationRightBracket n L data rho v : FreeModel n L))
  have htail := rowTail_lie_basis n L data rho s.val (by omega) v
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
    (FreeModel n L)
    (rowTail n L s.val (by omega) (rho : FreeModel n L))
    (triangularPBWBasis n L data v)
  have hleftWord : QuotientWeightRow.basisWord n L data
      (left ++ [v]) = lw * iv := by
    simp [QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, List.map_append, lw, iv]
  have hrightWord : QuotientWeightRow.basisWord n L data
      (v :: rest) = iv * rwrd := by
    simp [QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, rwrd, iv]
  simp only [QuotientWeightRow.value]
  rw [hleftWord, hrightWord]
  change lw * ir * (iv * rwrd) = (lw * iv) * ir * rwrd + lw * ib * rwrd
  rw [show ib = UniversalEnvelopingAlgebra.ι ℤ
      ⁅rowTail n L s.val (by omega) (rho : FreeModel n L),
        triangularPBWBasis n L data v⁆ by
      simpa [ib] using (congrArg (UniversalEnvelopingAlgebra.ι ℤ) htail).symm]
  calc
    _ = lw * (ir * iv) * rwrd := by noncomm_ring
    _ = lw * (iv * ir + UniversalEnvelopingAlgebra.ι ℤ
          ⁅rowTail n L s.val (by omega) (rho : FreeModel n L),
            triangularPBWBasis n L data v⁆) * rwrd := by rw [hswap]
    _ = _ := by noncomm_ring

/-- One quotient-weight step exposes exactly the homogeneous head and
retains the same full relation at the successor bound. -/
theorem quotientMarkedTruncation
    (left right : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (s : ℕ) (hs : s < n + 1) :
    (QuotientWeightRow.marked left rho ⟨s, by omega⟩ right :
        QuotientWeightRow n L data).value n L data =
      (QuotientWeightRow.marked left rho ⟨s + 1, by omega⟩ right :
          QuotientWeightRow n L data).value n L data +
        ((quotientTruncationRows n L data left right rho s hs).map
          (fun q ↦ q.1 • q.2.value n L data)).sum := by
  classical
  let component := FreeMetabelian.Free.weightIncl s hs
    (FreeMetabelian.Free.weightProject s hs (rho : FreeModel n L))
  let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    { toFun := fun x ↦ QuotientWeightRow.basisWord n L data left *
          UniversalEnvelopingAlgebra.ι ℤ x *
          QuotientWeightRow.basisWord n L data right
      map_add' := by intro x y; rw [map_add, mul_add, add_mul]
      map_smul' := by
        intro z x
        rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
        simp only [RingHom.id_apply] }
  have hc := congrArg context (triangularCoordinates_sum n L data component)
  rw [map_list_sum] at hc
  have hcomponent :
      ((quotientTruncationRows n L data left right rho s hs).map
        (fun q ↦ q.1 • q.2.value n L data)).sum = context component := by
    rw [quotientTruncationRows, List.map_map]
    calc
      _ = ((triangularCoordinates n L data component).map
          (fun q ↦ context (q.1 • triangularPBWBasis n L data q.2))).sum := by
        congr 1
        apply List.map_congr_left
        intro q hq
        rcases q with ⟨z, i⟩
        simp [context, QuotientWeightRow.value,
          QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_append]
        noncomm_ring
      _ = context component := by
        simpa only [List.map_map, Function.comp_apply] using hc
  rw [hcomponent]
  have htail := rowTail_eq_head_add_succ n L s hs (rho : FreeModel n L)
  simp only [QuotientWeightRow.value]
  rw [htail, map_add]
  change _ = _ +
    QuotientWeightRow.basisWord n L data left *
      UniversalEnvelopingAlgebra.ι ℤ component *
      QuotientWeightRow.basisWord n L data right
  noncomm_ring

theorem quotientWeightExpansion_preserves
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (h : quotientWeightExpansion n L data r = some qs) :
    (qs.map fun q ↦ q.1 • q.2.value n L data).sum =
      r.value n L data := by
  classical
  cases r with
  | ordinary xs =>
      simp only [quotientWeightExpansion] at h
      split at h <;> try contradiction
      rename_i d hd
      rw [Option.some.injEq] at h
      subst qs
      obtain ⟨hxs, hyx⟩ :=
        LieRings.DegreeFive.chooseAdjacentInversion?_eq_some_realizes hd
      rw [hxs]
      simp only [List.map_cons, List.sum_cons, one_smul]
      simp only [QuotientWeightRow.value]
      rw [quotientOrdinaryTransfer n L data d.left d.right d.x d.y]
      congr 1
      rw [quotientOrdinaryCorrection, List.map_map]
      let context : FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
        { toFun := fun z ↦ QuotientWeightRow.basisWord n L data d.left *
              UniversalEnvelopingAlgebra.ι ℤ z *
              QuotientWeightRow.basisWord n L data d.right
          map_add' := by intro x y; rw [map_add, mul_add, add_mul]
          map_smul' := by
            intro z x
            rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
            simp only [RingHom.id_apply] }
      have hc := congrArg context
        (triangularCoordinates_sum n L data
          ⁅triangularPBWBasis n L data d.x,
            triangularPBWBasis n L data d.y⁆)
      rw [map_list_sum] at hc
      calc
        ((triangularCoordinates n L data
              ⁅triangularPBWBasis n L data d.x,
                triangularPBWBasis n L data d.y⁆).map
            (fun q ↦ q.1 •
              (QuotientWeightRow.ordinary (d.left ++ q.2 :: d.right) :
                QuotientWeightRow n L data).value n L data)).sum =
            ((triangularCoordinates n L data
              ⁅triangularPBWBasis n L data d.x,
                triangularPBWBasis n L data d.y⁆).map
              (fun q ↦ context
                (q.1 • triangularPBWBasis n L data q.2))).sum := by
          congr 1
          apply List.map_congr_left
          intro q hq
          rcases q with ⟨z, i⟩
          simp [context, QuotientWeightRow.value,
            QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, List.map_append]
          noncomm_ring
        _ = context ⁅triangularPBWBasis n L data d.x,
              triangularPBWBasis n L data d.y⁆ := by
          simpa only [List.map_map, Function.comp_apply] using hc
        _ = _ := rfl
  | marked left rho s right =>
      simp only [quotientWeightExpansion] at h
      split at h <;> try contradiction
      rename_i hone
      split at h
      · rw [Option.some.injEq] at h
        subst qs
        have hs : s = ⟨n + 1, by omega⟩ := Fin.ext (by assumption)
        simp [QuotientWeightRow.value, hs]
      · rename_i hcut
        have hslt : s.val < n + 1 := by omega
        split at h
        · rename_i v rest hright
          split at h
          · rename_i hv
            rw [Option.some.injEq] at h
            subst qs
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              one_smul, add_zero]
            exact (quotientMarkedTransfer n L data left rest rho s v).symm
          · rename_i hv
            rw [Option.some.injEq] at h
            subst qs
            simp only [List.map_cons, List.sum_cons, one_smul]
            exact (quotientMarkedTruncation n L data left (v :: rest)
              rho s.val hslt).symm
        · rename_i hright
          rw [Option.some.injEq] at h
          subst qs
          simp only [List.map_cons, List.sum_cons, one_smul]
          exact (quotientMarkedTruncation n L data left []
            rho s.val hslt).symm

/-- The complete factor-first/quotient-weight deterministic collector. -/
def quotientWeightCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (QuotientWeightRow n L data) (UEA ℤ (FreeModel n L)) where
  relation x y := rowMeasureLt (x.measure n L data) (y.measure n L data)
  wellFounded := InvImage.wf (QuotientWeightRow.measure n L data)
    rowMeasureLt_wellFounded
  expansion := quotientWeightExpansion n L data
  value := QuotientWeightRow.value n L data
  decreases := quotientWeightExpansion_decreases n L data
  preserves := quotientWeightExpansion_preserves n L data

theorem quotientWeightCollector_evaluate (r : QuotientWeightRow n L data) :
    (quotientWeightCollector n L data).evaluate
        ((quotientWeightCollector n L data).normalForm r) =
      r.value n L data :=
  LieRings.DegreeFive.FiniteTaggedCollector.evaluate_normalForm _ r

/-! ## The exact bridge from the factor pass -/

/-- If an element already lies in the declared tail, taking that tail does
nothing. -/
theorem rowTail_eq_of_mem_tail (x : FreeModel n L) (s : ℕ)
    (hs : s ≤ n + 1)
    (hx : x ∈ FreeMetabelian.Free.tail
      (X := Generator L) (c := n + 1) s) :
    rowTail n L s hs x = x := by
  funext i
  rw [rowTail, LinearMap.sub_apply, LinearMap.id_apply]
  by_cases hi : i.val < s
  · have hxi : x i = 0 := hx i hi
    simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
      FreeMetabelian.Free.projectPrefix, hi, hxi]
  · simp [rowTruncation, FreeMetabelian.Free.prefixIncl,
      FreeMetabelian.Free.projectPrefix, hi]

/-- Interpret a placed full relation at the quotient bound determined by
its Smith leading weight. -/
def quotientWeightRowOfPlaced (r : TriangularPlacedRow n L) :
    QuotientWeightRow n L data :=
  .marked r.left (triangularRelationOfIndex n L data r.tag)
    ⟨r.tag.1.val, by omega⟩ r.right

theorem quotientWeightRowOfPlaced_value (r : TriangularPlacedRow n L) :
    (quotientWeightRowOfPlaced n L data r).value n L data =
      TriangularPlacedRow.value n L data r := by
  simp only [quotientWeightRowOfPlaced, QuotientWeightRow.value,
    TriangularPlacedRow.value, TriangularPlacedRow.relation]
  rw [rowTail_eq_of_mem_tail n L
    (triangularRelationOfIndex n L data r.tag : FreeModel n L)
    r.tag.1.val (by omega)
    (triangularRelationOfIndex_mem_tail n L data r.tag)]
  rfl

/-- The complete first-pass frontier, with every relation still labelled by
its genuine full defining relation, is the initial expression of the
quotient-weight pass. -/
def GoverningWitness.quotientWeightInitial {a : L}
    (w : GoverningWitness n L data a) :
    QuotientWeightRow n L data →₀ ℤ :=
  (w.triangularPlacedFrontier n L data).sum (fun r z ↦
    Finsupp.single (quotientWeightRowOfPlaced n L data r) z)

theorem GoverningWitness.evaluate_quotientWeightInitial {a : L}
    (w : GoverningWitness n L data a) :
    (quotientWeightCollector n L data).evaluate
        (w.quotientWeightInitial n L data) = w.theta := by
  classical
  rw [GoverningWitness.quotientWeightInitial, map_finsuppSum]
  calc
    _ = (triangularPlacedCollector n L data).evaluate
        (w.triangularPlacedFrontier n L data) := by
      apply Finsupp.sum_congr
      intro r hr
      simp only [LieRings.DegreeFive.FiniteTaggedCollector.evaluate_single]
      change (w.triangularPlacedFrontier n L data r) •
          (quotientWeightRowOfPlaced n L data r).value n L data =
        (w.triangularPlacedFrontier n L data r) •
          TriangularPlacedRow.value n L data r
      rw [quotientWeightRowOfPlaced_value]
    _ = w.theta := w.evaluate_triangularPlacedFrontier n L data

/-- The terminal quotient-weight frontier. -/
def GoverningWitness.quotientWeightFrontier {a : L}
    (w : GoverningWitness n L data a) :
    QuotientWeightRow n L data →₀ ℤ :=
  (w.quotientWeightInitial n L data).sum (fun r z ↦
    z • (quotientWeightCollector n L data).normalForm r)

theorem GoverningWitness.evaluate_quotientWeightFrontier {a : L}
    (w : GoverningWitness n L data a) :
    (quotientWeightCollector n L data).evaluate
        (w.quotientWeightFrontier n L data) = w.theta := by
  classical
  rw [GoverningWitness.quotientWeightFrontier, map_finsuppSum]
  calc
    _ = (quotientWeightCollector n L data).evaluate
        (w.quotientWeightInitial n L data) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul,
        (quotientWeightCollector n L data).evaluate_normalForm]
      rfl
    _ = w.theta := w.evaluate_quotientWeightInitial n L data

end

end LieRings.MetabelianVanishing
