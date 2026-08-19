import LieRings.DimensionSubring.MetabelianVanishing.FactorCollector

/-!
# Assembly of the two-filtered row calculation

The statements in this file are the global consequences of the literal
factor and quotient-weight collectors.  In particular, an exposed
homogeneous component is never used as a relation: all Koszul relation
entries below are projections of the contextual full relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance assemblyFintype : Fintype L := Fintype.ofFinite L

/-! ## The two local filtration identities -/

/-- A bracket context has manuscript weight zero only when it is the empty
context.  Every adapted basis factor has strictly positive weight. -/
theorem RelationContext.eq_hole_of_weight_eq_zero
    (c : RelationContext n L data hn)
    (h : RelationContext.weight n L data hn c = 0) :
    c = .hole := by
  cases c with
  | hole => rfl
  | lieRight c x =>
      simp [RelationContext.weight, adaptedWeightedBasis] at h

/-- An active-weight-one truncation cell is exactly a mark-one occurrence
with no surrounding commutator context. -/
theorem ProvenancedCell.context_eq_hole_and_mark_eq_one_of_activeWeight_eq_one
    (c : ProvenancedCell n L data hn)
    (h : c.activeWeight n L data hn = 1) :
    c.context = .hole ∧ c.mark.val = 1 := by
  have hmark : c.mark.val = 1 := by
    simp only [ProvenancedCell.activeWeight] at h
    have hpos := c.mark_pos
    omega
  have hcontext : RelationContext.weight n L data hn c.context = 0 := by
    simp only [ProvenancedCell.activeWeight] at h
    omega
  exact ⟨RelationContext.eq_hole_of_weight_eq_zero
    n L data hn c.context hcontext, hmark⟩

/-- A contextual prefix marked at `b` has no coordinate at or above its
active manuscript weight `b + context.weight`.  This is the upper-support
counterpart of `RelationContext.apply_mem_tail`. -/
theorem RelationContext.markedPrefix_apply_eq_zero_of_le
    (c : RelationContext n L data hn) (rho : Relations n L data)
    (b : Fin (n + 2)) (i : Fin (n + 1))
    (hi : b.val + RelationContext.weight n L data hn c ≤ i.val) :
    RelationContext.markedPrefix n L data hn c rho b i = 0 := by
  classical
  let z := rowTruncation n L b.val (by omega) (rho : FreeModel n L)
  have hsum := FreeMetabelian.Free.sum_incl_project z
  have happly := congrArg (RelationContext.apply n L data hn c) hsum
  rw [map_sum] at happly
  have hcoord := congrFun happly i
  rw [Finset.sum_apply] at hcoord
  rw [RelationContext.markedPrefix, ← hcoord]
  apply Finset.sum_eq_zero
  intro s hs
  by_cases hsb : s.val < b.val
  · exact RelationContext.apply_weightIncl_apply_eq_zero_of_ne
      n L data hn c s.val s.isLt
      (FreeMetabelian.Free.weightProject s.val s.isLt z) i (by omega)
  · have hz : FreeMetabelian.Free.weightProject s.val s.isLt z = 0 := by
      change z s = 0
      change (if h : s.val < b.val then (rho : FreeModel n L) s else 0) = 0
      simp [hsb]
    change RelationContext.apply n L data hn c
        (FreeMetabelian.Free.weightIncl s.val s.isLt
          (FreeMetabelian.Free.weightProject s.val s.isLt z)) i = 0
    rw [hz, map_zero, map_zero]
    rfl

/-- At a contextual cell of active weight `k`, its exposed component has
zero old-prefix image in the transgression. -/
theorem ProvenancedCell.transgressionTooth_component_eq_zero
    (c : ProvenancedCell n L data hn)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (hactive : c.activeWeight n L data hn = k) :
    transgressionTooth n L data k hk hkn
        (prLE n L k (by omega)
          (RelationContext.component n L data hn
            c.context c.root c.mark)) = 0 := by
  have hprefix : FreeMetabelian.Free.prefixMap (X := Generator L)
      (k - 1) k (by omega)
      (prLE n L k (by omega)
        (RelationContext.component n L data hn
          c.context c.root c.mark)) = 0 := by
    funext i
    change RelationContext.component n L data hn
        c.context c.root c.mark ⟨i.val, by omega⟩ = 0
    apply RelationContext.component_apply_eq_zero_of_ne
      n L data hn c.context c.root c.mark c.mark_pos
    change c.mark.val + RelationContext.weight n L data hn c.context = k at hactive
    have hi : i.val < k - 1 := i.isLt
    intro heq
    have heq' : i.val + 1 =
        c.mark.val + RelationContext.weight n L data hn c.context := by
      simpa only using heq
    omega
  rw [transgressionTooth, LinearMap.comp_apply, hprefix, map_zero]

/-- The new-weight head of a full contextual relation is exactly the head of
the component exposed on its active edge. -/
theorem ProvenancedCell.transgressionHead_component_eq_relation
    (c : ProvenancedCell n L data hn)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (hactive : c.activeWeight n L data hn = k) :
    transgressionHead n L data k hk hkn
        (prLE n L k (by omega)
          (RelationContext.component n L data hn
            c.context c.root c.mark)) =
      transgressionHead n L data k hk hkn
        (relationPrefix n L data k (by omega)
          (RelationContext.relation n L data hn c.context c.root)) := by
  unfold transgressionHead
  apply congrArg (pieceToU (n := n) L data k (by omega))
  change RelationContext.component n L data hn c.context c.root c.mark
      ⟨k - 1, by omega⟩ =
    (RelationContext.relation n L data hn c.context c.root : FreeModel n L)
      ⟨k - 1, by omega⟩
  have hprefix :=
    RelationContext.projectPrefix_relation_eq_markedPrefix_of_active
      n L data hn k (by omega) c.context c.root c.mark (by
        simpa [ProvenancedCell.activeWeight] using hactive)
  have hstep := RelationContext.prefix_step n L data hn
    c.context c.root c.mark c.mark_pos
  have hprevious : RelationContext.markedPrefix n L data hn c.context c.root
      ⟨c.mark.val - 1, by omega⟩
        ⟨k - 1, by omega⟩ = 0 := by
    apply RelationContext.markedPrefix_apply_eq_zero_of_le
      n L data hn c.context c.root ⟨c.mark.val - 1, by omega⟩
        ⟨k - 1, by omega⟩
    simp only [ProvenancedCell.activeWeight] at hactive
    change c.mark.val - 1 +
      RelationContext.weight n L data hn c.context ≤ k - 1
    have hm := c.mark_pos
    omega
  have hstepCoord := congrFun hstep ⟨k - 1, by omega⟩
  simp only [Pi.add_apply] at hstepCoord
  rw [hprevious, zero_add] at hstepCoord
  have hprefixCoord := congrFun hprefix ⟨k - 1, by omega⟩
  exact hstepCoord.symm.trans hprefixCoord.symm

/-- The basis-word symbol formula with its factor degree supplied externally.
This is the transport-free form used on a fixed diagonal of the rectangle. -/
theorem rightSymbol_basisWord_mul_iota_of_length
    (q k : ℕ) (hk : k ≤ n + 1)
    (left : List (AdaptedIndex n L data hn))
    (x : FreeModel n L) (hlen : left.length = q) :
    rightSymbol n L data hn (q + 1) k hk
        (MarkedRow.basisWord n L data hn left *
          UniversalEnvelopingAlgebra.ι ℤ x) =
      SymmetricPower.insert ℤ (A L k) q (prLE n L k hk x)
        (SymmetricPower.tprod ℤ (fun j : Fin q ↦
          prLE n L k hk
            (adaptedBasis n L data hn
              (left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩)))) := by
  subst q
  simpa only using rightSymbol_basisWord_mul_iota
    n L data hn k hk left x

/-- On a diagonal cell, the horizontal (full-relation) and vertical
(component) transgression reads are literally equal. -/
theorem ProvenancedCell.T_markedRow_eq_T_componentRow
    (c : ProvenancedCell n L data hn)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (hlen : c.left.length = n - k + 1)
    (hactive : c.activeWeight n L data hn = k) :
    T n L data k hk hkn
        (rightSymbol n L data hn (n - k + 2) k (by omega)
          c.markedRow.value) =
      T n L data k hk hkn
        (c.factorEdge n L data hn (n - k + 2) k (by omega)) := by
  let s : SymmetricPower ℤ (Fin (n - k + 1)) (A L k) :=
    c.sym n L data hn (n - k + 1) k (by omega) hlen
  let r : D n L data k (by omega) :=
    fullRelationToD n L data k (by omega)
      (RelationContext.relation n L data hn c.context c.root)
  have hmarked := rightSymbol_basisWord_mul_iota_of_length
    n L data hn (n - k + 1) k (by omega) c.left
      (RelationContext.markedPrefix n L data hn
        c.context c.root c.mark) hlen
  have hcomponent := rightSymbol_basisWord_mul_iota_of_length
    n L data hn (n - k + 1) k (by omega) c.left
      (RelationContext.component n L data hn
        c.context c.root c.mark) hlen
  have hprefix :=
    RelationContext.projectPrefix_relation_eq_markedPrefix_of_active
      n L data hn k (by omega) c.context c.root c.mark (by
        simpa [ProvenancedCell.activeWeight] using hactive)
  have htooth := c.transgressionTooth_component_eq_zero
    n L data hn k hk hkn hactive
  have hhead := c.transgressionHead_component_eq_relation
    n L data hn k hk hkn hactive
  have hmarkedValue : c.markedRow.value =
      MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.markedPrefix n L data hn
            c.context c.root c.mark) := by
    simp [ProvenancedCell.markedRow, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word]
  have hcomponentValue : c.componentRow.value =
      MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.component n L data hn
            c.context c.root c.mark) := by
    simp [ProvenancedCell.componentRow, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word]
  have hmarked' : rightSymbol n L data hn (n - k + 2) k (by omega)
        c.markedRow.value =
      SymmetricPower.insert ℤ (A L k) (n - k + 1)
        (prLE n L k (by omega)
          (RelationContext.markedPrefix n L data hn
            c.context c.root c.mark)) s := by
    simpa only [hmarkedValue, s, ProvenancedCell.sym] using hmarked
  have hcomponent' : c.factorEdge n L data hn
        (n - k + 2) k (by omega) =
      SymmetricPower.insert ℤ (A L k) (n - k + 1)
        (prLE n L k (by omega)
          (RelationContext.component n L data hn
            c.context c.root c.mark)) s := by
    simpa only [ProvenancedCell.factorEdge, hcomponentValue, s,
      ProvenancedCell.sym] using hcomponent
  rw [hmarked', hcomponent']
  have hprefix' : prLE n L k (by omega)
        (RelationContext.markedPrefix n L data hn
          c.context c.root c.mark) =
      relationPrefix n L data k (by omega)
        (RelationContext.relation n L data hn c.context c.root) :=
    hprefix.symm
  rw [hprefix']
  change T n L data k hk hkn
      (SymmetricPower.insert ℤ (A L k) (n - k + 1) r.1 s) = _
  rw [T_insert_of_tooth_eq_zero n L data k hk hkn r.1
      (by exact transgressionTooth_relation_zero n L data k hk hkn r) s]
  rw [T_insert_of_tooth_eq_zero n L data k hk hkn _ htooth s]
  congr 1
  apply congrArg (fun x ↦ x ⊗ₜ[ℤ]
    SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
      (transgressionTooth n L data k hk hkn) s)
  simpa only [r, fullRelationToD] using hhead.symm

/-! ## The exact intermediate diagonal -/

/-- The component side of the `(n-k+2,k)` diagonal.  The two tests are kept
in the definition so this is literally the same signed set of trace cells as
`contextualChi`, rather than a post-hoc support restriction. -/
def GoverningWitness.diagonalComponentFactor {a : L}
    (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    SymmetricPower ℤ (Fin (n - k + 2)) (A L k) :=
  (w.provenancedCells n L data hn).sum (fun c z ↦ z •
    if hlen : c.left.length = n - k + 1 then
      if hactive : c.activeWeight n L data hn = k then
        c.factorEdge n L data hn (n - k + 2) k (by omega)
      else 0
    else 0)

/-- Cell-by-cell polarization identifies the boundary of the genuine
relative packet with the component edge on exactly the same diagonal. -/
theorem GoverningWitness.T_dOne_contextualChi_eq_diagonalComponentFactor
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    T n L data k hk hkn
        (Koszul.dOne (presentation n L data k (by omega) (by omega))
          (n - k + 1) (contextualChi n L data hn w k hk hkn)) =
      T n L data k hk hkn
        (w.diagonalComponentFactor n L data hn k hk hkn) := by
  classical
  rw [contextualChi, dOne_contextualSymbolChain,
    GoverningWitness.diagonalComponentFactor, map_finsuppSum,
    map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  simp only [map_zsmul]
  congr 1
  by_cases hlen : c.left.length = n - k + 1
  · rw [dif_pos hlen, dif_pos hlen]
    by_cases hactive : c.activeWeight n L data hn = k
    · rw [dif_pos hactive, dif_pos hactive]
      exact c.T_markedRow_eq_T_componentRow n L data hn
        k hk hkn hlen hactive
    · rw [dif_neg hactive, dif_neg hactive, map_zero]
  · rw [dif_neg hlen, dif_neg hlen, map_zero]

/-- The manuscript's horizontal character is therefore the read of its
literal component diagonal, with no homogeneous component treated as a
relation. -/
theorem GoverningWitness.Phi_contextualChi_eq_T_diagonalComponentFactor
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Phi n L data k hk hkn
        (Koszul.PresentationHomology.oneMap
          (presentation n L data k (by omega) (by omega))
          (presentation (n := n) L data (k - 1) (by omega) (by omega))
          (presentationProjection n L data k hk (by omega))
          (n - k + 1) (contextualChi n L data hn w k hk hkn)) =
      T n L data k hk hkn
        (w.diagonalComponentFactor n L data hn k hk hkn) := by
  rw [Phi_contextualChi_eq_T_dOne n L data hn w k hk hkn,
    w.T_dOne_contextualChi_eq_diagonalComponentFactor n L data hn k hk hkn]

/-! ## The terminal target -/

/-- Once the literal terminal collection has produced its certified packet,
Point 6 kills its oriented primitive and hence the original cyclic top
coordinate.  This lemma contains no row calculation; it is the exact final
use of the packet constructed below. -/
theorem GoverningWitness.eq_zero_of_terminalPacket
    {a : L} (w : GoverningWitness n L data a)
    (p : TerminalQuadraticPacket n L data hn)
    (hp : (w.externalMarkedWord n L data hn).value =
      p.orientedPrimitive) : a = 0 := by
  have hpacket := p.orientedPrimitive_eq_zero n L data hn
  have hcoord : data.topEquiv ⟨a, by
      rw [← w.evaluates]
      change evaluation n L data
        (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
          lowerCentralSeries ℤ L n
      rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
      change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl
            (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
      rw [FreeMetabelian.Evaluation.linear_incl]
      cases n with
      | zero => simp
      | succ t =>
          exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
            data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ = 0 := by
    rw [← w.externalMarkedWord_value n L data hn]
    exact hp.trans hpacket
  have hsub : (⟨a, by
      rw [← w.evaluates]
      change evaluation n L data
        (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
          lowerCentralSeries ℤ L n
      rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
      change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl
            (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
      rw [FreeMetabelian.Evaluation.linear_incl]
      cases n with
      | zero => simp
      | succ t =>
          exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
            data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ :
        lowerCentralSeries ℤ L n) = 0 := by
    exact data.topEquiv.injective
      (hcoord.trans data.topEquiv.toAddMonoidHom.map_zero.symm)
  exact congrArg Subtype.val hsub

end

end LieRings.MetabelianVanishing
