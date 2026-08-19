import LieRings.DimensionSubring.MetabelianVanishing.MarkedCollector

/-!
# Provenance-preserving finite collector traces

The corrected closed-square proof works with occurrences, not with an
already-combined normal form.  This file supplies the small generic ledger
needed for that purpose.  A path records the chosen child at every rewrite,
so equal rows reached by different routes remain different generators.
-/

namespace LieRings.MetabelianVanishing

open LieRings.DegreeFive

noncomputable section

universe u v

variable {P : Type u} {A : Type v} [AddCommGroup A]

/-- A nonzero coefficient in a finite sum of occurrence ledgers comes from
at least one literal list entry. -/
theorem exists_finsupp_in_list_of_sum_apply_ne_zero
    {I : Type*} (rows : List (I →₀ ℤ)) (i : I)
    (h : rows.sum i ≠ 0) :
    ∃ row ∈ rows, row i ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h
  let ev : (I →₀ ℤ) →+ ℤ := Finsupp.applyAddHom i
  change ev rows.sum = 0
  rw [map_list_sum]
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨row, hrow, rfl⟩ := hz
  exact hall row hrow

/-- A row together with its route through a deterministic rewrite tree. -/
abbrev CollectorOccurrence (P : Type u) := List ℕ × P

/-- One occurrence-level use of a collector rewrite. -/
structure CollectorRewriteCell (C : FiniteTaggedCollector P A) where
  path : List ℕ
  coefficient : ℤ
  input : P
  outputs : List (ℤ × P)
  expansion_eq : C.expansion input = some outputs

/-- Oriented incidence boundary of one rewrite cell. -/
def CollectorRewriteCell.boundary (C : FiniteTaggedCollector P A)
    (cell : CollectorRewriteCell C) : CollectorOccurrence P →₀ ℤ := by
  classical
  exact
    Finsupp.single (cell.path, cell.input) cell.coefficient -
      (List.ofFn fun i : Fin cell.outputs.length ↦
        Finsupp.single
          (i.1 :: cell.path, (cell.outputs.get i).2)
          (cell.coefficient * (cell.outputs.get i).1)).sum

/-- One recursive layer of the flattened rewrite trace. -/
private def collectorTraceStep (C : FiniteTaggedCollector P A) (p : P)
    (rec : ∀ q, C.relation q p → List ℕ → ℤ →
      List (CollectorRewriteCell C))
    (path : List ℕ) (coefficient : ℤ) :
    List (CollectorRewriteCell C) :=
  match h : C.expansion p with
  | none => []
  | some qs =>
      { path := path
        coefficient := coefficient
        input := p
        outputs := qs
        expansion_eq := h } ::
        (List.ofFn fun i : Fin qs.length ↦
          rec (qs.get i).2 (C.decreases h (qs.get i) (List.get_mem qs i))
            (i.1 :: path) (coefficient * (qs.get i).1)).flatten

/-- The finite list of all rewrite cells below one labelled root. -/
def collectorTrace (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ) :
    List (CollectorRewriteCell C) :=
  C.wellFounded.fix (fun p rec ↦ collectorTraceStep C p rec) p path coefficient

/-- Recursive equation for a terminal occurrence trace. -/
theorem collectorTrace_eq_of_expansion_none
    (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ)
    (h : C.expansion p = none) :
    collectorTrace C p path coefficient = [] := by
  rw [collectorTrace, C.wellFounded.fix_eq]
  unfold collectorTraceStep
  split
  · rfl
  · rename_i qs he
    rw [h] at he
    contradiction

/-- Recursive equation for a nonterminal occurrence trace.  In particular,
the root cell and each numbered child trace remain literal list entries. -/
theorem collectorTrace_eq_of_expansion_some
    (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ)
    (qs : List (ℤ × P)) (h : C.expansion p = some qs) :
    collectorTrace C p path coefficient =
      { path := path
        coefficient := coefficient
        input := p
        outputs := qs
        expansion_eq := h } ::
        (List.ofFn fun i : Fin qs.length ↦
          collectorTrace C (qs.get i).2 (i.1 :: path)
            (coefficient * (qs.get i).1)).flatten := by
  rw [collectorTrace, C.wellFounded.fix_eq]
  unfold collectorTraceStep
  split
  · rename_i he
    rw [h] at he
    contradiction
  · rename_i qs' he
    have hqs : qs' = qs := by
      rw [h] at he
      exact Option.some.inj he.symm
    subst qs'
    rfl

/-- One recursive layer of the path-labelled terminal frontier. -/
private def collectorFrontierStep (C : FiniteTaggedCollector P A) (p : P)
    (rec : ∀ q, C.relation q p → List ℕ → ℤ →
      CollectorOccurrence P →₀ ℤ)
    (path : List ℕ) (coefficient : ℤ) :
    CollectorOccurrence P →₀ ℤ := by
  classical
  exact match h : C.expansion p with
  | none => Finsupp.single (path, p) coefficient
  | some qs =>
      (List.ofFn fun i : Fin qs.length ↦
        rec (qs.get i).2 (C.decreases h (qs.get i) (List.get_mem qs i))
          (i.1 :: path) (coefficient * (qs.get i).1)).sum

/-- The path-labelled terminal frontier below one root. -/
def collectorFrontier (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ) :
    CollectorOccurrence P →₀ ℤ :=
  C.wellFounded.fix (fun p rec ↦ collectorFrontierStep C p rec)
    p path coefficient

theorem collectorFrontier_eq_of_expansion_none
    (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ)
    (h : C.expansion p = none) :
    collectorFrontier C p path coefficient =
      Finsupp.single (path, p) coefficient := by
  rw [collectorFrontier, C.wellFounded.fix_eq]
  unfold collectorFrontierStep
  split
  · rfl
  · rename_i qs he
    rw [h] at he
    contradiction

theorem collectorFrontier_eq_of_expansion_some
    (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ)
    (qs : List (ℤ × P)) (h : C.expansion p = some qs) :
    collectorFrontier C p path coefficient =
      (List.ofFn fun i : Fin qs.length ↦
        collectorFrontier C (qs.get i).2 (i.1 :: path)
          (coefficient * (qs.get i).1)).sum := by
  rw [collectorFrontier, C.wellFounded.fix_eq]
  unfold collectorFrontierStep
  split
  · rename_i he
    rw [h] at he
    contradiction
  · rename_i qs' he
    have hqs : qs' = qs := by
      rw [h] at he
      exact Option.some.inj he.symm
    subst qs'
    rfl

/-- Every nonzero path-labelled frontier coefficient is genuinely terminal
for the collector.  This occurrence statement is stronger than the usual
normal-form support statement because it is proved before different paths
are forgotten. -/
theorem collectorFrontier_terminal_of_ne
    (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ) (o : CollectorOccurrence P)
    (ho : collectorFrontier C p path coefficient o ≠ 0) :
    C.expansion o.2 = none := by
  induction p using C.wellFounded.induction generalizing path coefficient with
  | h p ih =>
      cases hexp : C.expansion p with
      | none =>
        rw [collectorFrontier_eq_of_expansion_none
          C p path coefficient hexp] at ho
        have hop : o = (path, p) := by
          by_contra hne
          simp [hne] at ho
        subst o
        exact hexp
      | some qs =>
        rw [collectorFrontier_eq_of_expansion_some
          C p path coefficient qs hexp] at ho
        have hchild : ∃ i : Fin qs.length,
            collectorFrontier C (qs.get i).2 (i.1 :: path)
                (coefficient * (qs.get i).1) o ≠ 0 := by
          by_contra hall
          push Not at hall
          apply ho
          let ev : (CollectorOccurrence P →₀ ℤ) →+ ℤ :=
            Finsupp.applyAddHom o
          change ev (List.ofFn fun i : Fin qs.length ↦
            collectorFrontier C (qs.get i).2 (i.1 :: path)
              (coefficient * (qs.get i).1)).sum = 0
          rw [map_list_sum]
          apply List.sum_eq_zero
          intro z hz
          rw [List.mem_map] at hz
          obtain ⟨x, hx, rfl⟩ := hz
          rw [List.mem_ofFn] at hx
          obtain ⟨i, rfl⟩ := hx
          exact hall i
        obtain ⟨i, hi⟩ := hchild
        exact ih (qs.get i).2
          (C.decreases hexp (qs.get i) (List.get_mem qs i))
          (i.1 :: path) (coefficient * (qs.get i).1) hi

/-- A property preserved by every numbered rewrite child is retained by
every nonzero occurrence of the path-labelled terminal frontier.  This is
the occurrence-level invariant principle: it does not first combine equal
terminal rows. -/
theorem collectorFrontier_invariant_of_ne
    (C : FiniteTaggedCollector P A) (I : P → Prop)
    (hpreserves : ∀ {p qs}, C.expansion p = some qs → I p →
      ∀ q ∈ qs, I q.2)
    (p : P) (hp : I p) (path : List ℕ) (coefficient : ℤ)
    (o : CollectorOccurrence P)
    (ho : collectorFrontier C p path coefficient o ≠ 0) :
    I o.2 := by
  induction p using C.wellFounded.induction generalizing path coefficient with
  | h p ih =>
      cases hexp : C.expansion p with
      | none =>
          rw [collectorFrontier_eq_of_expansion_none
            C p path coefficient hexp] at ho
          have hop : o = (path, p) := by
            by_contra hne
            simp [hne] at ho
          subst o
          exact hp
      | some qs =>
          rw [collectorFrontier_eq_of_expansion_some
            C p path coefficient qs hexp] at ho
          have hchild : ∃ i : Fin qs.length,
              collectorFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1) o ≠ 0 := by
            by_contra hall
            push Not at hall
            apply ho
            let ev : (CollectorOccurrence P →₀ ℤ) →+ ℤ :=
              Finsupp.applyAddHom o
            change ev (List.ofFn fun i : Fin qs.length ↦
              collectorFrontier C (qs.get i).2 (i.1 :: path)
                (coefficient * (qs.get i).1)).sum = 0
            rw [map_list_sum]
            apply List.sum_eq_zero
            intro z hz
            rw [List.mem_map] at hz
            obtain ⟨x, hx, rfl⟩ := hz
            rw [List.mem_ofFn] at hx
            obtain ⟨i, rfl⟩ := hx
            exact hall i
          obtain ⟨i, hi⟩ := hchild
          exact ih (qs.get i).2
            (C.decreases hexp (qs.get i) (List.get_mem qs i))
            (hpreserves hexp hp (qs.get i) (List.get_mem qs i))
            (i.1 :: path) (coefficient * (qs.get i).1) hi

/-- Every input cell in the flattened rewrite trace inherits any property
which is stable under all rewrite children. -/
theorem collectorTrace_input_invariant
    (C : FiniteTaggedCollector P A) (I : P → Prop)
    (hpreserves : ∀ {p qs}, C.expansion p = some qs → I p →
      ∀ q ∈ qs, I q.2)
    (p : P) (hp : I p) (path : List ℕ) (coefficient : ℤ)
    (cell : CollectorRewriteCell C)
    (hcell : cell ∈ collectorTrace C p path coefficient) :
    I cell.input := by
  induction p using C.wellFounded.induction generalizing path coefficient with
  | h p ih =>
      cases hexp : C.expansion p with
      | none =>
          rw [collectorTrace_eq_of_expansion_none
            C p path coefficient hexp] at hcell
          contradiction
      | some qs =>
          rw [collectorTrace_eq_of_expansion_some
            C p path coefficient qs hexp] at hcell
          simp only [List.mem_cons] at hcell
          rcases hcell with hroot | hdesc
          · subst cell
            exact hp
          · rw [List.mem_flatten] at hdesc
            obtain ⟨childTrace, hchildTrace, hcell⟩ := hdesc
            rw [List.mem_ofFn] at hchildTrace
            obtain ⟨i, rfl⟩ := hchildTrace
            exact ih (qs.get i).2
              (C.decreases hexp (qs.get i) (List.get_mem qs i))
              (hpreserves hexp hp (qs.get i) (List.get_mem qs i))
              (i.1 :: path) (coefficient * (qs.get i).1) hcell

/-- Sum of the incidence boundaries of a finite trace. -/
def collectorTraceBoundary (C : FiniteTaggedCollector P A)
    (cells : List (CollectorRewriteCell C)) :
    CollectorOccurrence P →₀ ℤ :=
  (cells.map fun cell ↦ cell.boundary C).sum

/-- Forget route labels and combine equal underlying rows. -/
def forgetCollectorPaths :
    (CollectorOccurrence P →₀ ℤ) →ₗ[ℤ] (P →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Prod.snd

/-- Forgetting paths recovers the ordinary collector normal form. -/
theorem forgetCollectorPaths_frontier (C : FiniteTaggedCollector P A)
    (p : P) (path : List ℕ) (coefficient : ℤ) :
    forgetCollectorPaths (collectorFrontier C p path coefficient) =
      coefficient • C.normalForm p := by
  induction p using C.wellFounded.induction generalizing path coefficient with
  | h p ih =>
      rw [collectorFrontier, C.wellFounded.fix_eq,
        FiniteTaggedCollector.normalForm, C.wellFounded.fix_eq]
      change
        forgetCollectorPaths
          (match hx : C.expansion p with
          | none => Finsupp.single (path, p) coefficient
          | some qs =>
              (List.ofFn fun i : Fin qs.length ↦
                collectorFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1)).sum) =
          coefficient •
            (match hx : C.expansion p with
            | none => Finsupp.single p 1
            | some qs =>
                (qs.attach.map fun q : {x // x ∈ qs} ↦
                  q.1.1 • C.normalForm q.1.2).sum)
      split
      · simp [forgetCollectorPaths, Finsupp.lmapDomain_apply]
      · rename_i qs hexpand
        rw [map_list_sum]
        have hchildren :
            (List.ofFn fun i : Fin qs.length ↦
              forgetCollectorPaths
                (collectorFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1))) =
              List.ofFn fun i : Fin qs.length ↦
                (coefficient * (qs.get i).1) • C.normalForm (qs.get i).2 := by
          apply congrArg List.ofFn
          funext i
          exact ih (qs.get i).2
            (C.decreases hexpand (qs.get i) (List.get_mem qs i))
            (i.1 :: path) (coefficient * (qs.get i).1)
        rw [List.map_ofFn]
        change
          (List.ofFn fun i : Fin qs.length ↦
            forgetCollectorPaths
              (collectorFrontier C (qs.get i).2 (i.1 :: path)
                (coefficient * (qs.get i).1))).sum = _
        rw [hchildren]
        have hattach :
            (qs.attach.map fun q : {x // x ∈ qs} ↦
                q.1.1 • C.normalForm q.1.2).sum =
              (qs.map fun q ↦ q.1 • C.normalForm q.2).sum :=
          congrArg List.sum
            (List.attach_map_val
              (l := qs) (f := fun q ↦ q.1 • C.normalForm q.2))
        rw [hattach, List.smul_sum]
        apply congrArg List.sum
        rw [List.map_map]
        calc
          List.ofFn (fun i : Fin qs.length ↦
              (coefficient * (qs.get i).1) • C.normalForm (qs.get i).2) =
              List.ofFn (fun i : Fin qs.length ↦
                coefficient • ((qs.get i).1 • C.normalForm (qs.get i).2)) := by
            apply congrArg List.ofFn
            funext i
            rw [mul_smul]
          _ = qs.map (fun q ↦
              coefficient • (q.1 • C.normalForm q.2)) := by
            calc
              _ = (List.ofFn qs.get).map (fun q ↦
                    coefficient • (q.1 • C.normalForm q.2)) := by
                  rw [List.map_ofFn]
                  rfl
              _ = _ := congrArg
                (List.map (fun q ↦ coefficient •
                  (q.1 • C.normalForm q.2))) (List.ofFn_get qs)

/-- Evaluating a path-labelled terminal frontier gives the coefficient times
the value of its root.  This is the occurrence-level evaluation identity;
paths are forgotten only inside this final linear read. -/
theorem evaluate_collectorFrontier
    (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ) :
    (collectorFrontier C p path coefficient).sum
        (fun o z ↦ z • C.value o.2) = coefficient • C.value p := by
  have hforget := forgetCollectorPaths_frontier C p path coefficient
  have hlinear := LinearMap.congr_fun
    (Finsupp.linearCombination_comp_lmapDomain
      (R := ℤ) (v' := C.value) Prod.snd)
    (collectorFrontier C p path coefficient)
  change
    (forgetCollectorPaths (collectorFrontier C p path coefficient)).sum
        (fun q z ↦ z • C.value q) =
      (collectorFrontier C p path coefficient).sum
        (fun o z ↦ z • C.value o.2) at hlinear
  rw [← hlinear, hforget]
  change C.evaluate (coefficient • C.normalForm p) = _
  rw [map_zsmul, C.evaluate_normalForm]

/-- Prefix ledger / finite integral Stokes formula with route labels. -/
theorem collector_prefix_ledger (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ) :
    Finsupp.single (path, p) coefficient -
        collectorFrontier C p path coefficient =
      collectorTraceBoundary C (collectorTrace C p path coefficient) := by
  induction p using C.wellFounded.induction generalizing path coefficient with
  | h p ih =>
      rw [collectorTrace, C.wellFounded.fix_eq,
        collectorFrontier, C.wellFounded.fix_eq]
      unfold collectorTraceStep collectorFrontierStep
      split
      · simp [collectorTraceBoundary]
      · rename_i qs hexpand
        let roots : List (CollectorOccurrence P →₀ ℤ) :=
          List.ofFn fun i : Fin qs.length ↦
            Finsupp.single (i.1 :: path, (qs.get i).2)
              (coefficient * (qs.get i).1)
        let fronts : List (CollectorOccurrence P →₀ ℤ) :=
          List.ofFn fun i : Fin qs.length ↦
            collectorFrontier C (qs.get i).2 (i.1 :: path)
              (coefficient * (qs.get i).1)
        let traces : List (List (CollectorRewriteCell C)) :=
          List.ofFn fun i : Fin qs.length ↦
            collectorTrace C (qs.get i).2 (i.1 :: path)
              (coefficient * (qs.get i).1)
        have hchildren :
            (List.ofFn fun i : Fin qs.length ↦
              Finsupp.single (i.1 :: path, (qs.get i).2)
                    (coefficient * (qs.get i).1) -
                collectorFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1)).sum =
              (traces.map fun cells ↦ collectorTraceBoundary C cells).sum := by
          dsimp only [traces]
          rw [List.map_ofFn]
          apply congrArg List.sum
          apply congrArg List.ofFn
          funext i
          simpa [Function.comp_def] using
            ih (qs.get i).2
              (C.decreases hexpand (qs.get i) (List.get_mem qs i))
              (i.1 :: path) (coefficient * (qs.get i).1)
        have sum_ofFn_sub : ∀ (m : ℕ)
            (r f : Fin m → CollectorOccurrence P →₀ ℤ),
            (List.ofFn fun i ↦ r i - f i).sum =
              (List.ofFn r).sum - (List.ofFn f).sum := by
          intro m
          induction m with
          | zero => intro r f; simp
          | succ m ihm =>
              intro r f
              rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
              simp only [List.sum_cons]
              rw [ihm]
              abel
        have hsumDiff :
            (List.ofFn fun i : Fin qs.length ↦
              Finsupp.single (i.1 :: path, (qs.get i).2)
                    (coefficient * (qs.get i).1) -
                collectorFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1)).sum =
              roots.sum - fronts.sum := by
          exact sum_ofFn_sub qs.length _ _
        change
          Finsupp.single (path, p) coefficient - fronts.sum =
            (Finsupp.single (path, p) coefficient - roots.sum) +
              collectorTraceBoundary C traces.flatten
        rw [collectorTraceBoundary, List.map_flatten, List.sum_flatten]
        rw [List.map_map]
        change
          Finsupp.single (path, p) coefficient - fronts.sum =
            (Finsupp.single (path, p) coefficient - roots.sum) +
              (traces.map fun cells ↦ collectorTraceBoundary C cells).sum
        rw [← hchildren, hsumDiff]
        abel

end

end LieRings.MetabelianVanishing
