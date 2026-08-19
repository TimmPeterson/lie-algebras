import LieRings.DimensionSubring.MetabelianVanishing.GlobalOccurrenceLedger
import LieRings.DimensionSubring.MetabelianVanishing.ClosedSquare

/-!
# Contextual occurrence presentations of the intermediate packets

This is the manuscript's `J_k` on the complete provenance-preserving trace.
Every occurrence retains its initial relation/PBW-monomial label, child path,
full root relation, and complete lower commutator context.  In particular,
equal algebraic rows with different ancestry are never identified.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.DegreeFive

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalPacketOccurrencesFintype : Fintype L :=
  Fintype.ofFinite L

/-- A distinct source copy in the governing relation/PBW expansion. -/
structure InitialPacketLabel where
  relationTerm : Relations n L data × UEA ℤ (FreeModel n L)
  exponent : AdaptedIndex n L data hn →₀ ℕ

noncomputable instance : DecidableEq (InitialPacketLabel n L data hn) :=
  Classical.decEq _

/-- A contextual truncation cell together with its complete ancestry. -/
structure TruncationOccurrence where
  root : InitialPacketLabel n L data hn
  path : List ℕ
  cell : ProvenancedCell n L data hn

noncomputable instance : DecidableEq (TruncationOccurrence n L data hn) :=
  Classical.decEq _

/-- One recursion layer of the occurrence-preserving contextual trace. -/
private def labelledTruncationTraceStep
    (root : InitialPacketLabel n L data hn)
    (r : ProvenancedRow n L data hn)
    (rec : ∀ q, (provenancedCollector n L data hn).relation q r →
      List ℕ → TruncationOccurrence n L data hn →₀ ℤ)
    (path : List ℕ) : TruncationOccurrence n L data hn →₀ ℤ := by
  classical
  exact match h : (provenancedCollector n L data hn).expansion r with
  | none =>
      match provenancedCell? n L data hn r with
      | none => 0
      | some c => Finsupp.single
          ({ root := root, path := path, cell := c } :
            TruncationOccurrence n L data hn) 1
  | some qs =>
      (match provenancedCell? n L data hn r with
        | none => 0
        | some c => Finsupp.single
            ({ root := root, path := path, cell := c } :
              TruncationOccurrence n L data hn) 1) +
      (List.ofFn fun i : Fin qs.length ↦
        (qs.get i).1 • rec (qs.get i).2
          ((provenancedCollector n L data hn).decreases h
            (qs.get i) (List.get_mem qs i))
          (i.1 :: path)).sum

/-- Complete finite contextual truncation trace below one source copy. -/
def labelledTruncationTrace
    (root : InitialPacketLabel n L data hn)
    (r : ProvenancedRow n L data hn) (path : List ℕ) :
    TruncationOccurrence n L data hn →₀ ℤ :=
  (provenancedCollector n L data hn).wellFounded.fix
    (fun r rec ↦ labelledTruncationTraceStep n L data hn root r rec)
    r path

theorem labelledTruncationTrace_eq_of_expansion_none
    (root : InitialPacketLabel n L data hn)
    (r : ProvenancedRow n L data hn) (path : List ℕ)
    (h : provenancedExpansion n L data hn r = none) :
    labelledTruncationTrace n L data hn root r path =
      match provenancedCell? n L data hn r with
      | none => 0
      | some c => Finsupp.single
          ({ root := root, path := path, cell := c } :
            TruncationOccurrence n L data hn) 1 := by
  rw [labelledTruncationTrace,
    (provenancedCollector n L data hn).wellFounded.fix_eq]
  unfold labelledTruncationTraceStep
  have h' : (provenancedCollector n L data hn).expansion r = none := h
  split
  · rfl
  · rename_i qs he
    rw [h'] at he
    contradiction

theorem labelledTruncationTrace_eq_of_expansion_some
    (root : InitialPacketLabel n L data hn)
    (r : ProvenancedRow n L data hn) (path : List ℕ)
    (qs : List (ℤ × ProvenancedRow n L data hn))
    (h : provenancedExpansion n L data hn r = some qs) :
    labelledTruncationTrace n L data hn root r path =
      (match provenancedCell? n L data hn r with
        | none => 0
        | some c => Finsupp.single
            ({ root := root, path := path, cell := c } :
              TruncationOccurrence n L data hn) 1) +
      (List.ofFn fun i : Fin qs.length ↦
        (qs.get i).1 • labelledTruncationTrace n L data hn root
          (qs.get i).2 (i.1 :: path)).sum := by
  rw [labelledTruncationTrace,
    (provenancedCollector n L data hn).wellFounded.fix_eq]
  unfold labelledTruncationTraceStep
  have h' : (provenancedCollector n L data hn).expansion r = some qs := h
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

/-- Forget ancestry while retaining the full contextual truncation cell. -/
def forgetTruncationAncestry :
    (TruncationOccurrence n L data hn →₀ ℤ) →ₗ[ℤ]
      (ProvenancedCell n L data hn →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ TruncationOccurrence.cell

theorem sum_forgetTruncationAncestry
    {M : Type*} [AddCommGroup M]
    (x : TruncationOccurrence n L data hn →₀ ℤ)
    (f : ProvenancedCell n L data hn → M) :
    (forgetTruncationAncestry n L data hn x).sum
        (fun c z ↦ z • f c) =
      x.sum (fun o z ↦ z • f o.cell) := by
  change (Finsupp.linearCombination ℤ f)
      (forgetTruncationAncestry n L data hn x) =
    (Finsupp.linearCombination ℤ (f ∘ TruncationOccurrence.cell)) x
  exact LinearMap.congr_fun
    (Finsupp.linearCombination_comp_lmapDomain
      (R := ℤ) (v' := f) TruncationOccurrence.cell) x

/-- Forgetting ancestry recovers the complete contextual cell trace. -/
theorem forgetTruncationAncestry_labelledTrace
    (root : InitialPacketLabel n L data hn)
    (r : ProvenancedRow n L data hn) (path : List ℕ) :
    forgetTruncationAncestry n L data hn
        (labelledTruncationTrace n L data hn root r path) =
      provenancedTrace n L data hn r := by
  classical
  let C := provenancedCollector n L data hn
  induction r using C.wellFounded.induction generalizing path with
  | h r ih =>
      cases hexp : provenancedExpansion n L data hn r with
      | none =>
          rw [labelledTruncationTrace_eq_of_expansion_none
            n L data hn root r path hexp]
          rw [provenancedTrace_eq_of_expansion_none n L data hn r hexp]
          cases hc : provenancedCell? n L data hn r with
          | none => simp [forgetTruncationAncestry, hc]
          | some c =>
              simp [forgetTruncationAncestry, hc,
                Finsupp.lmapDomain_apply]
      | some qs =>
          rw [labelledTruncationTrace_eq_of_expansion_some
            n L data hn root r path qs hexp]
          rw [provenancedTrace_eq_of_expansion_some
            n L data hn r qs hexp]
          rw [map_add]
          congr 1
          · cases hc : provenancedCell? n L data hn r with
            | none => simp [forgetTruncationAncestry, hc]
            | some c =>
                simp [forgetTruncationAncestry, hc,
                  Finsupp.lmapDomain_apply]
          · rw [map_list_sum, List.map_ofFn]
            change
              (List.ofFn fun i : Fin qs.length ↦
                forgetTruncationAncestry n L data hn
                  ((qs.get i).1 • labelledTruncationTrace n L data hn root
                    (qs.get i).2 (i.1 :: path))).sum = _
            calc
              _ = (List.ofFn fun i : Fin qs.length ↦
                  (qs.get i).1 • provenancedTrace n L data hn
                    (qs.get i).2).sum := by
                apply congrArg List.sum
                apply congrArg List.ofFn
                funext i
                rw [map_zsmul,
                  ih (qs.get i).2
                    (C.decreases hexp (qs.get i) (List.get_mem qs i))]
              _ = ((List.ofFn qs.get).map fun q ↦
                  q.1 • provenancedTrace n L data hn q.2).sum := by
                rw [List.map_ofFn]
                apply congrArg List.sum
                apply congrArg List.ofFn
                funext i
                rfl
              _ = (qs.map fun q ↦
                  q.1 • provenancedTrace n L data hn q.2).sum := by
                rw [List.ofFn_get]
              _ = (qs.attach.map fun q ↦ q.1.1 •
                  provenancedTrace n L data hn q.1.2).sum := by
                exact congrArg List.sum
                  (List.attach_map_val
                    (l := qs) (f := fun q ↦ q.1 •
                      provenancedTrace n L data hn q.2)).symm

/-- All contextual truncation occurrences of the governing expression,
before equal source copies or descendant rows are combined. -/
def GoverningWitness.globalTruncationOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    TruncationOccurrence n L data hn →₀ ℤ :=
  w.relationCoefficients.sum fun p z ↦ z •
    ((adaptedWeightedBasis n L data hn).pbwEquiv.symm p.2).sum fun e t ↦
      t • labelledTruncationTrace n L data hn
        ⟨p, e⟩
        (.marked p.1 .hole ⟨n + 1, by omega⟩ []
          (exponentWord n L data hn e)) []

/-- The occurrence trace is a genuine refinement of the already-audited
complete contextual cell ledger. -/
theorem GoverningWitness.forget_globalTruncationOccurrences
    {a : L} (w : GoverningWitness n L data a) :
    forgetTruncationAncestry n L data hn
        (w.globalTruncationOccurrences n L data hn) =
      w.provenancedCells n L data hn := by
  classical
  let traceLinear :
      (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
        (ProvenancedCell n L data hn →₀ ℤ) :=
    Finsupp.linearCombination ℤ (provenancedTrace n L data hn)
  change forgetTruncationAncestry n L data hn
      (w.globalTruncationOccurrences n L data hn) =
    traceLinear (w.provenancedInitial n L data hn)
  rw [GoverningWitness.globalTruncationOccurrences,
    GoverningWitness.provenancedInitial, map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, map_zsmul]
  congr 1
  rw [provenancedRowsOfRightFactor, map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro e he
  rw [map_zsmul, forgetTruncationAncestry_labelledTrace]
  simp [traceLinear]

/-- One occurrence in the manuscript packet `J_k`. -/
structure PacketOccurrence (k : ℕ) where
  occurrence : TruncationOccurrence n L data hn
  active_wall : occurrence.cell.activeWeight n L data hn = k
  factor_count : occurrence.cell.left.length = n - k + 1

noncomputable instance (k : ℕ) :
    DecidableEq (PacketOccurrence n L data hn k) :=
  Classical.decEq _

/-- The complete signed occurrence presentation `J_k`. -/
def GoverningWitness.packetOccurrences
    {a : L} (w : GoverningWitness n L data a) (k : ℕ) :
    PacketOccurrence n L data hn k →₀ ℤ :=
  (w.globalTruncationOccurrences n L data hn).sum fun o z ↦
    if hactive : o.cell.activeWeight n L data hn = k then
      if hfactor : o.cell.left.length = n - k + 1 then
        Finsupp.single ⟨o, hactive, hfactor⟩ z
      else 0
    else 0

/-- Genuine contextual Koszul row represented by one packet occurrence. -/
def PacketOccurrence.realization
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (o : PacketOccurrence n L data hn k) :
    Koszul.One (presentation n L data k (by omega) (by omega))
      (n - k + 1) :=
  o.occurrence.cell.one n L data hn (n - k + 1) k
    (by omega) (by omega)

/-- The manuscript packet `chi_k`, definitionally read from `J_k`. -/
def GoverningWitness.packetChain
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.One (presentation n L data k (by omega) (by omega))
      (n - k + 1) :=
  (w.packetOccurrences n L data hn k).sum fun o z ↦
    z • o.realization n L data hn k hk hkn

theorem GoverningWitness.packetChain_eq_globalOccurrenceSum
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    w.packetChain n L data hn k hk hkn =
      (w.globalTruncationOccurrences n L data hn).sum (fun o z ↦
        z • if hactive : o.cell.activeWeight n L data hn = k then
          if hfactor : o.cell.left.length = n - k + 1 then
            o.cell.one n L data hn (n - k + 1) k
              (by omega) (by omega)
          else 0
        else 0) := by
  classical
  rw [GoverningWitness.packetChain, GoverningWitness.packetOccurrences,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro o ho
  by_cases hactive : o.cell.activeWeight n L data hn = k
  · simp only [hactive, dif_pos]
    by_cases hfactor : o.cell.left.length = n - k + 1
    · simp only [hfactor, dif_pos]
      rw [Finsupp.sum_single_index (by simp)]
      rfl
    · simp [hfactor]
      exact (smul_zero _).symm
  · simp [hactive]
    exact (smul_zero _).symm

/-- The labelled packet is exactly the complete contextual diagonal chain
after ancestry is forgotten. -/
theorem GoverningWitness.packetChain_eq_contextualChi
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    w.packetChain n L data hn k hk hkn =
      contextualChi n L data hn w k hk hkn := by
  classical
  rw [w.packetChain_eq_globalOccurrenceSum n L data hn k hk hkn]
  let f : ProvenancedCell n L data hn →
      Koszul.One (presentation n L data k (by omega) (by omega))
        (n - k + 1) := fun c ↦
    if hactive : c.activeWeight n L data hn = k then
      if hfactor : c.left.length = n - k + 1 then
        c.one n L data hn (n - k + 1) k (by omega) (by omega)
      else 0
    else 0
  have hforget := sum_forgetTruncationAncestry n L data hn
    (w.globalTruncationOccurrences n L data hn) f
  rw [w.forget_globalTruncationOccurrences n L data hn] at hforget
  rw [← hforget]
  unfold contextualChi contextualSymbolChain f
  apply Finsupp.sum_congr
  intro o ho
  by_cases hactive : o.activeWeight n L data hn = k <;>
    by_cases hfactor : o.left.length = n - k + 1 <;>
    simp [hactive, hfactor, ProvenancedCell.one]

/-- Exact occurrence-level Koszul boundary of `chi_k`. -/
theorem GoverningWitness.dOne_packetChain
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.dOne (presentation n L data k (by omega) (by omega))
        (n - k + 1) (w.packetChain n L data hn k hk hkn) =
      (w.packetOccurrences n L data hn k).sum fun o z ↦
        z • rightSymbol n L data hn (n - k + 2) k (by omega)
          o.occurrence.cell.markedRow.value := by
  classical
  rw [GoverningWitness.packetChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro o ho
  rw [map_zsmul, PacketOccurrence.realization,
    ProvenancedCell.dOne_one]
  rw [dif_pos o.factor_count, dif_pos o.active_wall]
  rw [show n - k + 1 + 1 = n - k + 2 by omega]
  rfl

/-- All ordinary inputs of a packet occurrence have manuscript weight one. -/
def PacketOccurrence.IsSupported
    (k : ℕ) (o : PacketOccurrence n L data hn k) : Prop :=
  ∀ x ∈ o.occurrence.cell.left,
    (adaptedWeightedBasis n L data hn).weight x = 1

noncomputable instance (k : ℕ) (o : PacketOccurrence n L data hn k) :
    Decidable (o.IsSupported n L data hn k) :=
  Classical.propDecidable _

/-- The manuscript subset `Delta_k`, retaining its original `J_k` index. -/
def GoverningWitness.supportedPacketOccurrences
    {a : L} (w : GoverningWitness n L data a) (k : ℕ) :
    {o : PacketOccurrence n L data hn k //
      o.IsSupported n L data hn k} →₀ ℤ :=
  (w.packetOccurrences n L data hn k).sum fun o z ↦
    if hs : o.IsSupported n L data hn k then
      Finsupp.single ⟨o, hs⟩ z
    else 0

end


end LieRings.MetabelianVanishing
