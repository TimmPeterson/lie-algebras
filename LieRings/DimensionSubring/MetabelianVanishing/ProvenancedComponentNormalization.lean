import LieRings.DimensionSubring.MetabelianVanishing.ClosedSquare

/-!
# PBW normalization of an arbitrary contextual component ledger

The closed-square collector is used for more than the governing initial
relation family.  This file packages its component PBW normalization for an
arbitrary finite signed ledger.  The only support hypothesis needed for the
ordered-word conclusion is the literal one: the ordinary factors to the left
of every source component cell are already ordered.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance provenancedComponentNormalizationFintype : Fintype L :=
  Fintype.ofFinite L

/-- Complete PBW normalization of an arbitrary signed contextual-component
ledger.  Root relation, context, and mark remain attached to every summand. -/
def normalizedComponentFrontier
    (cells : ProvenancedCell n L data hn →₀ ℤ) :
    ComponentPBWState n L data hn →₀ ℤ :=
  cells.sum fun c z ↦ z • c.componentPBWFrontier n L data hn

/-- Evaluation of the normalized ledger is the sum of the literal component
rows from which it was built. -/
theorem evaluate_normalizedComponentFrontier
    (cells : ProvenancedCell n L data hn →₀ ℤ) :
    (componentPBWCollector n L data hn).evaluate
        (normalizedComponentFrontier n L data hn cells) =
      cells.sum (fun c z ↦ z • c.componentRow.value) := by
  classical
  rw [normalizedComponentFrontier, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, c.evaluate_componentPBWFrontier]

/-- The exact factor-`q` read of an arbitrary normalized component ledger. -/
def normalizedComponentFactor
    (q k : ℕ) (hk : k ≤ n + 1)
    (cells : ProvenancedCell n L data hn →₀ ℤ) :
    Sym[ℤ] (Fin q) (A L k) :=
  (normalizedComponentFrontier n L data hn cells).sum fun s z ↦
    z • rightSymbol n L data hn q k hk (s.value n L data hn)

/-- PBW normalization does not change any exact factor-number read.  In
particular, the factor-two boundary and the factor-one primitive used at the
terminal wall are two projections of the same signed ledger. -/
theorem normalizedComponentFactor_eq_trace
    (q k : ℕ) (hk : k ≤ n + 1)
    (cells : ProvenancedCell n L data hn →₀ ℤ) :
    normalizedComponentFactor n L data hn q k hk cells =
      cells.sum (fun c z ↦
        z • c.factorEdge n L data hn q k hk) := by
  classical
  have h := congrArg (rightSymbol n L data hn q k hk)
    (evaluate_normalizedComponentFrontier n L data hn cells)
  change rightSymbol n L data hn q k hk
      ((normalizedComponentFrontier n L data hn cells).sum
        (fun s z ↦ z • s.value n L data hn)) =
    rightSymbol n L data hn q k hk
      (cells.sum (fun c z ↦ z • c.componentRow.value)) at h
  rw [map_finsuppSum, map_finsuppSum] at h
  simpa only [map_zsmul, normalizedComponentFactor,
    ProvenancedCell.factorEdge] using h

/-- Every supported normalized state retains the exact active weight carried
by its provenance. -/
theorem normalizedComponentFrontier_distinguished_weight
    (cells : ProvenancedCell n L data hn →₀ ℤ)
    (q : ComponentPBWState n L data hn)
    (hq : normalizedComponentFrontier n L data hn cells q ≠ 0) :
    (adaptedWeightedBasis n L data hn).weight q.distinguished =
      q.mark.val + RelationContext.weight n L data hn q.context := by
  classical
  rw [normalizedComponentFrontier, Finsupp.sum_apply] at hq
  have hexists : ∃ c ∈ cells.support,
      (cells c • c.componentPBWFrontier n L data hn) q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq (Finset.sum_eq_zero (fun c hc ↦ hall c hc))
  obtain ⟨c, hc, hcq⟩ := hexists
  have hfront : c.componentPBWFrontier n L data hn q ≠ 0 := by
    intro hzero
    simp [hzero] at hcq
  exact c.componentPBWFrontier_distinguished_weight
    n L data hn q hfront

/-- If every source cell has its ordinary left word ordered, every supported
normal form is an ordered complete PBW word. -/
theorem normalizedComponentFrontier_word_pairwise
    (cells : ProvenancedCell n L data hn →₀ ℤ)
    (hleft : ∀ c, cells c ≠ 0 → c.left.Pairwise (· ≤ ·))
    (q : ComponentPBWState n L data hn)
    (hq : normalizedComponentFrontier n L data hn cells q ≠ 0) :
    (q.word n L data hn).Pairwise (· ≤ ·) := by
  classical
  rw [normalizedComponentFrontier, Finsupp.sum_apply] at hq
  have hexists : ∃ c ∈ cells.support,
      (cells c • c.componentPBWFrontier n L data hn) q ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq (Finset.sum_eq_zero (fun c hc ↦ hall c hc))
  obtain ⟨c, hc, hcq⟩ := hexists
  have hfront : c.componentPBWFrontier n L data hn q ≠ 0 := by
    intro hzero
    simp [hzero] at hcq
  exact c.componentPBWFrontier_word_pairwise n L data hn
    (hleft c (Finsupp.mem_support_iff.mp hc)) q hfront

/-- Complete one-factor primitive of an arbitrary normalized component
ledger. -/
def normalizedComponentPrimitive
    (cells : ProvenancedCell n L data hn →₀ ℤ) : FreeModel n L :=
  (normalizedComponentFrontier n L data hn cells).sum fun s z ↦
    z • pbwPrimitive n L data hn (s.value n L data hn)

/-- PBW normalization does not change the aggregate primitive of the
component rows. -/
theorem normalizedComponentPrimitive_eq_trace
    (cells : ProvenancedCell n L data hn →₀ ℤ) :
    normalizedComponentPrimitive n L data hn cells =
      cells.sum (fun c z ↦ z • c.primitive n L data hn) := by
  classical
  have h := congrArg (pbwPrimitive n L data hn)
    (evaluate_normalizedComponentFrontier n L data hn cells)
  change pbwPrimitive n L data hn
      ((normalizedComponentFrontier n L data hn cells).sum
        (fun s z ↦ z • s.value n L data hn)) =
    pbwPrimitive n L data hn
      (cells.sum (fun c z ↦ z • c.componentRow.value)) at h
  rw [map_finsuppSum, map_finsuppSum] at h
  simpa only [map_zsmul, normalizedComponentPrimitive,
    ProvenancedCell.primitive] using h

/-- Once the source left words are ordered, only literal one-factor leaves
contribute to the primitive of the normalized component ledger. -/
theorem normalizedComponentPrimitive_eq_factorOne
    (cells : ProvenancedCell n L data hn →₀ ℤ)
    (hleft : ∀ c, cells c ≠ 0 → c.left.Pairwise (· ≤ ·)) :
    normalizedComponentPrimitive n L data hn cells =
      (normalizedComponentFrontier n L data hn cells).sum (fun s z ↦
        if s.factorCount n L data hn = 1 then
          z • pbwPrimitive n L data hn (s.value n L data hn)
        else 0) := by
  classical
  rw [normalizedComponentPrimitive]
  apply Finsupp.sum_congr
  intro s hs
  by_cases hone : s.factorCount n L data hn = 1
  · simp [hone]
  · rw [if_neg hone,
      s.pbwPrimitive_value_eq_zero_of_factorCount_ne_one n L data hn
        (normalizedComponentFrontier_word_pairwise n L data hn cells hleft s
          (Finsupp.mem_support_iff.mp hs)) hone]
    simp

end

end LieRings.MetabelianVanishing
