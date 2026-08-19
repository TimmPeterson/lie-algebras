import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffMarkOneAggregate
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffTerminalComponentPrimitiveBridge

/-!
# Primitive Stokes identity for the raw mark-one ledger

The factor-two full-label Stokes theorem is not by itself enough to compare
primitive reads.  This file records the stronger identity in the enveloping
algebra, before either projection is applied.  It is the same deterministic
occurrence trace: at the last truncation step the whole contextual relation
moves from the marked branch to the mark-one component branch.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffPrimitiveStokesFintype : Fintype L :=
  Fintype.ofFinite L

/-! ## The UEA-valued occurrence identity -/

/-- The whole-relation word charged to a mark-one truncation cell. -/
def ProvenancedCell.markOneFullLabelWord
    (c : ProvenancedCell n L data hn) : UEA ℤ (FreeModel n L) :=
  if c.mark.val = 1 then
    contextualFullRelationWord n L data hn
      c.root c.context c.left []
  else 0

/-- The same word at a terminal mark-one component occurrence. -/
def provenancedComponentFullLabelWordSeed
    (r : ProvenancedRow n L data hn) : UEA ℤ (FreeModel n L) :=
  match r with
  | .marked _ _ _ _ _ => 0
  | .component rho c k left right =>
      if k.val = 1 then
        contextualFullRelationWord n L data hn rho c left right
      else 0

/-- Sum of terminal mark-one component words below one row. -/
def normalFormProvenancedComponentFullLabelWord
    (r : ProvenancedRow n L data hn) : UEA ℤ (FreeModel n L) :=
  ((provenancedCollector n L data hn).normalForm r).sum
    (fun s z ↦ z • provenancedComponentFullLabelWordSeed n L data hn s)

/-- Sum of mark-one cell words in the complete trace below one row. -/
def provenancedTraceMarkOneFullLabelWord
    (r : ProvenancedRow n L data hn) : UEA ℤ (FreeModel n L) :=
  (provenancedTrace n L data hn r).sum
    (fun c z ↦ z • c.markOneFullLabelWord n L data hn)

private def provenancedComponentFullLabelWordLinear :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      UEA ℤ (FreeModel n L) :=
  Finsupp.linearCombination ℤ
    (provenancedComponentFullLabelWordSeed n L data hn)

private def provenancedCellFullLabelWordLinear :
    (ProvenancedCell n L data hn →₀ ℤ) →ₗ[ℤ]
      UEA ℤ (FreeModel n L) :=
  Finsupp.linearCombination ℤ
    (fun c ↦ c.markOneFullLabelWord n L data hn)

private def provenancedCellFullLabelWordSeed
    (r : ProvenancedRow n L data hn) : UEA ℤ (FreeModel n L) :=
  match provenancedCell? n L data hn r with
  | none => 0
  | some c => c.markOneFullLabelWord n L data hn

/-- One rewrite step transfers exactly one whole-relation label at the last
truncation and otherwise creates no mark-one label. -/
private theorem provenancedExpansion_componentFullLabelWord
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs) :
    (qs.map (fun q ↦ q.1 •
      provenancedComponentFullLabelWordSeed n L data hn q.2)).sum =
      provenancedComponentFullLabelWordSeed n L data hn r +
        provenancedCellFullLabelWordSeed n L data hn r := by
  classical
  have hfull := provenancedExpansion_preserves_fullLabelWord
    n L data hn h
  cases r with
  | component rho c k left right =>
      simp only [provenancedExpansion] at h
      split at h
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at h
        subst qs
        by_cases hk : k.val = 1
        · simpa [provenancedComponentFullLabelWordSeed,
            provenancedCellFullLabelWordSeed, provenancedCell?,
            provenancedFullLabelWord, hk] using hfull
        · simp [provenancedComponentFullLabelWordSeed,
            provenancedCellFullLabelWordSeed, provenancedCell?, hk]
  | marked rho c k left right =>
      cases right with
      | cons x right =>
          simp only [provenancedExpansion] at h
          rw [Option.some.injEq] at h
          subst qs
          simp [provenancedComponentFullLabelWordSeed,
            provenancedCellFullLabelWordSeed, provenancedCell?]
      | nil =>
          simp only [provenancedExpansion] at h
          split at h
          · rename_i hk
            rw [Option.some.injEq] at h
            subst qs
            simp [provenancedComponentFullLabelWordSeed,
              provenancedCellFullLabelWordSeed, provenancedCell?, hk]
          · rename_i hk
            split at h
            · contradiction
            · rename_i hw
              rw [Option.some.injEq] at h
              subst qs
              have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
              have hcell : provenancedCell? n L data hn
                  (.marked rho c k left []) =
                    some ⟨rho, c, k, left, hkpos, by simpa using hw⟩ := by
                simp [provenancedCell?, hkpos, hw]
              by_cases hkone : k.val = 1
              · simp [provenancedComponentFullLabelWordSeed,
                  provenancedCellFullLabelWordSeed, hcell,
                  ProvenancedCell.markOneFullLabelWord, hkone]
              · simp [provenancedComponentFullLabelWordSeed,
                  provenancedCellFullLabelWordSeed, hcell,
                  ProvenancedCell.markOneFullLabelWord, hkone]

private theorem provenancedCell?_eq_none_of_expansion_eq_none_word
    (r : ProvenancedRow n L data hn)
    (h : provenancedExpansion n L data hn r = none) :
    provenancedCell? n L data hn r = none := by
  classical
  cases r with
  | component rho c k left right => rfl
  | marked rho c k left right =>
      cases right with
      | cons x right => simp [provenancedCell?]
      | nil =>
          by_cases hk : 0 < k.val
          · by_cases hw : provenancedWall n L data hn c k left = false
            · exfalso
              have hne : provenancedExpansion n L data hn
                  (.marked rho c k left []) ≠ none := by
                simp [provenancedExpansion, Nat.ne_of_gt hk, hw]
              exact hne h
            · simp [provenancedCell?, hk, hw]
          · simp [provenancedCell?, hk]

private theorem sum_smul_add_provenancedFullLabelWord
    (qs : List (ℤ × ProvenancedRow n L data hn)) :
    (qs.map (fun q ↦ q.1 •
      (provenancedComponentFullLabelWordSeed n L data hn q.2 +
        provenancedTraceMarkOneFullLabelWord n L data hn q.2))).sum =
      (qs.map (fun q ↦ q.1 •
        provenancedComponentFullLabelWordSeed n L data hn q.2)).sum +
      (qs.map (fun q ↦ q.1 •
        provenancedTraceMarkOneFullLabelWord n L data hn q.2)).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons, smul_add]
      simp only [smul_add] at ih
      rw [ih]
      module

/-- UEA-valued full-label Stokes formula.  It is stronger than either the
factor-two or primitive projection used later. -/
theorem normalFormProvenancedComponentFullLabelWord_eq_trace
    (r : ProvenancedRow n L data hn) :
    normalFormProvenancedComponentFullLabelWord n L data hn r =
      provenancedComponentFullLabelWordSeed n L data hn r +
        provenancedTraceMarkOneFullLabelWord n L data hn r := by
  classical
  let C := provenancedCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : provenancedExpansion n L data hn r with
      | none =>
          have hcell := provenancedCell?_eq_none_of_expansion_eq_none_word
            n L data hn r hexp
          rw [normalFormProvenancedComponentFullLabelWord,
            C.normalForm_eq_single_of_terminal hexp,
            provenancedTraceMarkOneFullLabelWord,
            provenancedTrace_eq_of_expansion_none n L data hn r hexp]
          simp [provenancedComponentFullLabelWordSeed, hcell]
      | some qs =>
          have hnf :
              normalFormProvenancedComponentFullLabelWord n L data hn r =
                (qs.map (fun q ↦ q.1 •
                  normalFormProvenancedComponentFullLabelWord
                    n L data hn q.2)).sum := by
            change provenancedComponentFullLabelWordLinear n L data hn
              (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r qs hexp, map_list_sum]
            simp only [List.map_map]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            change provenancedComponentFullLabelWordLinear n L data hn
                (q.1 • C.normalForm q.2) =
              q.1 • normalFormProvenancedComponentFullLabelWord
                n L data hn q.2
            rw [map_zsmul]
            rfl
          have hhere : provenancedCellFullLabelWordLinear n L data hn
                (match provenancedCell? n L data hn r with
                | none => 0
                | some c => Finsupp.single c 1) =
              provenancedCellFullLabelWordSeed n L data hn r := by
            cases hc : provenancedCell? n L data hn r <;>
              simp [provenancedCellFullLabelWordSeed, hc,
                provenancedCellFullLabelWordLinear]
          have htrace :
              provenancedTraceMarkOneFullLabelWord n L data hn r =
                provenancedCellFullLabelWordSeed n L data hn r +
                  (qs.map (fun q ↦ q.1 •
                    provenancedTraceMarkOneFullLabelWord
                      n L data hn q.2)).sum := by
            change provenancedCellFullLabelWordLinear n L data hn
              (provenancedTrace n L data hn r) = _
            rw [provenancedTrace_eq_of_expansion_some
              n L data hn r qs hexp, map_add, map_list_sum]
            have hchildren :
                ((qs.attach.map fun q ↦ q.1.1 •
                    provenancedTrace n L data hn q.1.2).map
                  (provenancedCellFullLabelWordLinear n L data hn)).sum =
                  (qs.attach.map fun q ↦ q.1.1 •
                    provenancedTraceMarkOneFullLabelWord
                      n L data hn q.1.2).sum := by
              apply congrArg List.sum
              rw [List.map_map]
              apply List.map_congr_left
              intro q hq
              change provenancedCellFullLabelWordLinear n L data hn
                    (q.1.1 • provenancedTrace n L data hn q.1.2) =
                  q.1.1 • provenancedTraceMarkOneFullLabelWord
                    n L data hn q.1.2
              rw [map_zsmul]
              rfl
            calc
              _ = provenancedCellFullLabelWordSeed n L data hn r +
                  (qs.attach.map fun q ↦ q.1.1 •
                    provenancedTraceMarkOneFullLabelWord
                      n L data hn q.1.2).sum :=
                congrArg₂ (fun x y ↦ x + y) hhere hchildren
              _ = provenancedCellFullLabelWordSeed n L data hn r +
                  (qs.map (fun q ↦ q.1 •
                    provenancedTraceMarkOneFullLabelWord
                      n L data hn q.2)).sum := by
                congr 1
                exact congrArg List.sum
                  (List.attach_map_val (l := qs)
                    (f := fun q ↦ q.1 •
                      provenancedTraceMarkOneFullLabelWord
                        n L data hn q.2))
          have hih :
              (qs.map (fun q ↦ q.1 •
                normalFormProvenancedComponentFullLabelWord
                  n L data hn q.2)).sum =
                (qs.map (fun q ↦ q.1 •
                  (provenancedComponentFullLabelWordSeed n L data hn q.2 +
                    provenancedTraceMarkOneFullLabelWord
                      n L data hn q.2))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            rw [ih q.2 (C.decreases hexp q hq)]
          have hsplit := sum_smul_add_provenancedFullLabelWord
            n L data hn qs
          have hlocal := provenancedExpansion_componentFullLabelWord
            n L data hn hexp
          rw [hnf, hih, hsplit, hlocal, htrace]
          abel

/-! ## Aggregate raw-cutoff consequence -/

/-- Terminal mark-one whole-label word in the raw contextual frontier. -/
def GoverningWitness.rawCutoffTerminalComponentFullLabelWord
    {a : L} (w : GoverningWitness n L data a) : UEA ℤ (FreeModel n L) :=
  (w.rawCutoffProvenancedFrontier n L data hn).sum (fun r z ↦
    z • provenancedComponentFullLabelWordSeed n L data hn r)

/-- The terminal mark-one word is the exact sum of the whole labels charged
to the truncation cells. -/
theorem GoverningWitness.rawCutoffTerminalComponentFullLabelWord_eq_trace
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffTerminalComponentFullLabelWord n L data hn =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
        z • c.markOneFullLabelWord n L data hn) := by
  classical
  rw [GoverningWitness.rawCutoffTerminalComponentFullLabelWord,
    GoverningWitness.rawCutoffProvenancedFrontier,
    GoverningWitness.rawCutoffFullProvenancedCells]
  change Finsupp.linearCombination ℤ
      (provenancedComponentFullLabelWordSeed n L data hn)
        ((w.rawCutoffProvenancedInitial n L data hn).sum
          (fun r z ↦ z • (provenancedCollector n L data hn).normalForm r)) =
    Finsupp.linearCombination ℤ
      (fun c ↦ c.markOneFullLabelWord n L data hn)
        ((w.rawCutoffProvenancedInitial n L data hn).sum
          (fun r z ↦ z • provenancedTrace n L data hn r))
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul]
  change w.rawCutoffProvenancedInitial n L data hn r •
      normalFormProvenancedComponentFullLabelWord n L data hn r =
    w.rawCutoffProvenancedInitial n L data hn r •
      provenancedTraceMarkOneFullLabelWord n L data hn r
  rw [normalFormProvenancedComponentFullLabelWord_eq_trace]
  have hseed : provenancedComponentFullLabelWordSeed n L data hn r = 0 := by
    cases r with
    | marked => rfl
    | component root context mark left right =>
        exact (Finsupp.mem_support_iff.mp hr
          (w.rawCutoffProvenancedInitial_component
            n L data hn root context mark left right)).elim
  rw [hseed, zero_add]

/-- Our cell-Stokes terminal word is definitionally the literal raw terminal
component word used by the sound PBW terminal decomposition. -/
private theorem GoverningWitness.rawCutoffTerminalComponentFullLabelWord_eq_aggregate
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffTerminalComponentFullLabelWord n L data hn =
      w.rawCutoffAggregateTerminalComponentFullLabelWord n L data hn := by
  rfl

/-- The literal mark-one primitive is exactly the ordinary component-trace
primitive.  The first equality is the UEA-valued Stokes identity above; the
second is the PBW terminal decomposition, where the factor-two comparison is
made only after primitive projection. -/
theorem GoverningWitness.rawCutoffTraceMarkOneFullLabelPrimitive_eq_trace
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffTraceMarkOneFullLabelPrimitive n L data hn =
      w.rawCutoffTracePrimitive n L data hn := by
  classical
  have hcells : pbwPrimitive n L data hn
        ((w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
          z • c.markOneFullLabelWord n L data hn)) =
      w.rawCutoffTraceMarkOneFullLabelPrimitive n L data hn := by
    rw [map_finsuppSum,
      GoverningWitness.rawCutoffTraceMarkOneFullLabelPrimitive]
    apply Finsupp.sum_congr
    intro c hc
    rw [map_zsmul]
    by_cases hmark : c.mark.val = 1 <;>
      simp [ProvenancedCell.markOneFullLabelWord, hmark]
  calc
    w.rawCutoffTraceMarkOneFullLabelPrimitive n L data hn =
        pbwPrimitive n L data hn
          ((w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
            z • c.markOneFullLabelWord n L data hn)) := hcells.symm
    _ = pbwPrimitive n L data hn
          (w.rawCutoffTerminalComponentFullLabelWord n L data hn) :=
      congrArg (pbwPrimitive n L data hn)
        (w.rawCutoffTerminalComponentFullLabelWord_eq_trace
          n L data hn).symm
    _ = pbwPrimitive n L data hn
          (w.rawCutoffAggregateTerminalComponentFullLabelWord
            n L data hn) := congrArg (pbwPrimitive n L data hn)
        (w.rawCutoffTerminalComponentFullLabelWord_eq_aggregate
          n L data hn)
    _ = w.rawCutoffTracePrimitive n L data hn :=
      w.pbwPrimitive_rawCutoffAggregateTerminalComponentFullLabelWord
        n L data hn

end

end LieRings.MetabelianVanishing
