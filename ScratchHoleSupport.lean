import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffNonHoleCorrection

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

private theorem trace_top_hole_nil
    (rho : Relations n L data) :
    provenancedTrace n L data hn
      (.marked rho .hole ⟨n + 1, by omega⟩ [] []) = 0 := by
  have hwall : provenancedWall n L data hn (.hole)
      ⟨n + 1, by omega⟩ [] = true := by
    simp [provenancedWall, RelationContext.weight]
  rw [provenancedTrace_eq_of_expansion_none]
  · simp [provenancedCell?, hwall]
  · simp [provenancedExpansion, provenancedWall,
      RelationContext.weight]

private theorem trace_top_hole_singleton_apply_mark_one
    (rho : Relations n L data) (x : AdaptedIndex n L data hn)
    (c : ProvenancedCell n L data hn) (hcmark : c.mark.val = 1) :
    provenancedTrace n L data hn
      (.marked rho .hole ⟨n + 1, by omega⟩ [x] []) c = 0 := by
  let top : Fin (n + 2) := ⟨n + 1, by omega⟩
  let next : Fin (n + 2) := ⟨n, by omega⟩
  have htopNotWall :
      provenancedWall n L data hn (.hole) top [x] = false := by
    simp [provenancedWall, top, RelationContext.weight]
  have htopExpansion : provenancedExpansion n L data hn
      (.marked rho .hole top [x] []) =
        some [(1, .marked rho .hole next [x] []),
          (1, .component rho .hole top [x] [])] := by
    simp [provenancedExpansion, htopNotWall, top, next]
  have hnextExpansion : provenancedExpansion n L data hn
      (.marked rho .hole next [x] []) = none := by
    have hn0 : n ≠ 0 := by omega
    simp [provenancedExpansion, provenancedWall, next,
      RelationContext.weight, hn0]
  let cell : ProvenancedCell n L data hn :=
    ⟨rho, .hole, top, [x], by simp [top], htopNotWall⟩
  have hcell : provenancedCell? n L data hn
      (.marked rho .hole top [x] []) = some cell := by
    simp [provenancedCell?, cell, htopNotWall, top]
  rw [show (⟨n + 1, by omega⟩ : Fin (n + 2)) = top by rfl,
    provenancedTrace_eq_of_expansion_some _ _ _ _ _ _ htopExpansion]
  have hnext : provenancedTrace n L data hn
      (.marked rho .hole next [x] []) = 0 := by
    rw [provenancedTrace_eq_of_expansion_none _ _ _ _ _ hnextExpansion]
    simp [provenancedCell?, provenancedWall, next,
      RelationContext.weight]
  simp only [hnext, provenancedTrace_component_eq_zero, hcell,
    List.attach_cons, List.map_cons, List.sum_cons, List.attach_nil,
    List.map_nil, List.sum_nil, one_smul, zero_smul, add_zero,
    Finsupp.add_apply, Finsupp.single_apply]
  by_cases hctop : cell = c
  · have hmarks := congrArg
        (fun d : ProvenancedCell n L data hn ↦ d.mark.val) hctop
    have hbad : n + 1 = 1 := by
      calc
        n + 1 = cell.mark.val := by rfl
        _ = c.mark.val := hmarks
        _ = 1 := hcmark
    omega
  · simp [hctop]

private theorem provenancedTrace_marked_nil_cell_data
    (rho : Relations n L data)
    (context : RelationContext n L data hn)
    (mark : Fin (n + 2))
    (left : List (AdaptedIndex n L data hn))
    (c : ProvenancedCell n L data hn)
    (hc : provenancedTrace n L data hn
      (.marked rho context mark left []) c ≠ 0) :
    c.root = rho ∧ c.context = context ∧ c.left = left := by
  classical
  let C := provenancedCollector n L data hn
  let P : ProvenancedRow n L data hn → Prop
    | .marked rho context mark left [] =>
        ∀ c, provenancedTrace n L data hn
          (.marked rho context mark left []) c ≠ 0 →
          c.root = rho ∧ c.context = context ∧ c.left = left
    | _ => True
  have hall : ∀ r, P r := by
    intro r
    induction r using C.wellFounded.induction with
    | h r ih =>
        cases r with
        | component => trivial
        | marked rho context mark left right =>
            cases right with
            | cons x right => trivial
            | nil =>
                change ∀ c, provenancedTrace n L data hn
                  (.marked rho context mark left []) c ≠ 0 →
                  c.root = rho ∧ c.context = context ∧ c.left = left
                intro c hc
                by_cases hk : mark.val = 0
                · have hexp : provenancedExpansion n L data hn
                      (.marked rho context mark left []) = some [] := by
                    simp [provenancedExpansion, hk]
                  rw [provenancedTrace_eq_of_expansion_some
                    n L data hn _ _ hexp] at hc
                  simp [provenancedCell?, hk] at hc
                · by_cases hw :
                      provenancedWall n L data hn context mark left = true
                  · have hexp : provenancedExpansion n L data hn
                        (.marked rho context mark left []) = none := by
                      simp [provenancedExpansion, hk, hw]
                    rw [provenancedTrace_eq_of_expansion_none
                      n L data hn _ hexp] at hc
                    simp [provenancedCell?, hk, hw] at hc
                  · have hwfalse :
                        provenancedWall n L data hn context mark left = false :=
                      Bool.eq_false_of_not_eq_true hw
                    have hmarkpos : 0 < mark.val := by omega
                    let next : Fin (n + 2) :=
                      ⟨mark.val - 1, by omega⟩
                    let r₁ : ProvenancedRow n L data hn :=
                      .marked rho context next left []
                    let r₂ : ProvenancedRow n L data hn :=
                      .component rho context mark left []
                    let d : ProvenancedCell n L data hn :=
                      ⟨rho, context, mark, left, hmarkpos, hwfalse⟩
                    have hexp : provenancedExpansion n L data hn
                        (.marked rho context mark left []) =
                          some [(1, r₁), (1, r₂)] := by
                      simp [provenancedExpansion, hk, hwfalse, r₁, r₂,
                        next]
                    have hcell : provenancedCell? n L data hn
                        (.marked rho context mark left []) = some d := by
                      simp only [provenancedCell?]
                      rw [dif_pos trivial, dif_pos hmarkpos, dif_pos hwfalse]
                    have hr₂zero : provenancedTrace n L data hn r₂ = 0 := by
                      simp [r₂, provenancedTrace_component_eq_zero]
                    rw [provenancedTrace_eq_of_expansion_some
                      n L data hn _ _ hexp] at hc
                    simp only [hcell, List.attach_cons, List.map_cons,
                      List.sum_cons, List.attach_nil, List.map_nil,
                      List.sum_nil, one_smul, add_zero,
                      hr₂zero,
                      Finsupp.add_apply, Finsupp.single_apply] at hc
                    by_cases hdc : d = c
                    · subst c
                      exact ⟨rfl, rfl, rfl⟩
                    · have hchild : provenancedTrace n L data hn r₁ c ≠ 0 := by
                        simpa [hdc] using hc
                      have hexpC : C.expansion
                          (.marked rho context mark left []) =
                            some [(1, r₁), (1, r₂)] := hexp
                      have hir₁ := ih r₁
                        (C.decreases hexpC (1, r₁) (by simp))
                      change ∀ c, provenancedTrace n L data hn r₁ c ≠ 0 →
                        c.root = rho ∧ c.context = context ∧ c.left = left
                        at hir₁
                      exact hir₁ c hchild
  exact hall (.marked rho context mark left []) c hc

private theorem GoverningWitness.rawCutoffProvenancedInitial_shape
    {a : L} (w : GoverningWitness n L data a)
    (r : ProvenancedRow n L data hn)
    (hr : w.rawCutoffProvenancedInitial n L data hn r ≠ 0) :
    ∃ (rho : Relations n L data)
      (left : List (AdaptedIndex n L data hn)),
      r = .marked rho .hole ⟨n + 1, by omega⟩ left [] := by
  classical
  rw [GoverningWitness.rawCutoffProvenancedInitial,
    Finsupp.sum_apply] at hr
  have hexists : ∃ s ∈
      (w.rawCutoffFullLabelFrontier n L data hn).support,
      (w.rawCutoffFullLabelFrontier n L data hn s •
        rawProvenancedPart n L data hn s) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun s hs ↦ hall s hs))
  obtain ⟨s, hs, hsr⟩ := hexists
  have hsne : w.rawCutoffFullLabelFrontier n L data hn s ≠ 0 :=
    Finsupp.mem_support_iff.mp hs
  cases s with
  | ordinary word => simp [rawProvenancedPart] at hsr
  | marked left rho mark right =>
      have hshape := w.rawCutoffFullLabelFrontier_shape_of_ne
        n L data hn (.marked left rho mark right) hsne
      rcases hshape with ⟨hmark, hright, hordered⟩
      have hre : r = .marked rho .hole mark left right := by
        by_contra hne
        simp [rawProvenancedPart, Finsupp.smul_apply,
          Finsupp.single_apply, hne] at hsr
      subst r
      subst right
      have hmarkTop : mark = ⟨n + 1, by omega⟩ := by
        apply Fin.ext
        exact hmark
      exact ⟨rho, left, by rw [hmarkTop]⟩

/-- A mark-one cell in the complete full-label trace has at least two
ordinary factors on its left.  The two smaller cases stop at the two
contextual walls before mark one is reached. -/
theorem GoverningWitness.rawCutoffFullProvenancedCells_markOne_left_length
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0)
    (hmark : c.mark.val = 1) :
    2 ≤ c.left.length := by
  classical
  rw [GoverningWitness.rawCutoffFullProvenancedCells,
    Finsupp.sum_apply] at hc
  have hexists : ∃ r ∈
      (w.rawCutoffProvenancedInitial n L data hn).support,
      (w.rawCutoffProvenancedInitial n L data hn r •
        provenancedTrace n L data hn r) c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc (Finset.sum_eq_zero (fun r hr ↦ hall r hr))
  obtain ⟨r, hr, hrc⟩ := hexists
  have hrne : w.rawCutoffProvenancedInitial n L data hn r ≠ 0 :=
    Finsupp.mem_support_iff.mp hr
  obtain ⟨rho, left, rfl⟩ :=
    w.rawCutoffProvenancedInitial_shape n L data hn r hrne
  have htrace : provenancedTrace n L data hn
      (.marked rho .hole ⟨n + 1, by omega⟩ left []) c ≠ 0 := by
    intro hzero
    simp [hzero] at hrc
  have hdata := provenancedTrace_marked_nil_cell_data
    n L data hn rho .hole ⟨n + 1, by omega⟩ left c htrace
  have hleft : c.left = left := hdata.2.2
  rw [hleft]
  cases left with
  | nil =>
      have hz := congrArg
        (fun f : ProvenancedCell n L data hn →₀ ℤ ↦ f c)
        (trace_top_hole_nil n L data hn rho)
      exact (htrace hz).elim
  | cons x xs =>
      cases xs with
      | nil =>
          exact (htrace (trace_top_hole_singleton_apply_mark_one
            n L data hn rho x c hmark)).elim
      | cons y ys => simp

end

end LieRings.MetabelianVanishing
