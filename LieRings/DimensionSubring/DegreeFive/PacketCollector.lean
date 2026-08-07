import LieRings.DimensionSubring.DegreeFive.PacketWeights

/-!
# A finite tagged collector driven by a well-founded rewrite

This file turns the termination proof for placed packets into a reusable algebraic collector.
Each nonterminal tag expands into a finite integral linear combination of smaller tags.  The
normal form retains tags and coefficients, and its evaluation is proved equal to the original
value.  No confluence hypothesis is needed: the expansion function fixes the rewrite choice.
-/

namespace LieRings

namespace DegreeFive

noncomputable section

universe u v

/-- Data for a deterministic, coefficient-retaining finite rewrite system. -/
structure FiniteTaggedCollector (P : Type u) (A : Type v) [AddCommGroup A] where
  relation : P → P → Prop
  wellFounded : WellFounded relation
  expansion : P → Option (List (ℤ × P))
  value : P → A
  decreases : ∀ {p : P} {qs : List (ℤ × P)}, expansion p = some qs →
    ∀ q ∈ qs, relation q.2 p
  preserves : ∀ {p : P} {qs : List (ℤ × P)}, expansion p = some qs →
    (qs.map fun q ↦ q.1 • value q.2).sum = value p

namespace FiniteTaggedCollector

variable {P : Type u} {A : Type v} [AddCommGroup A]

/-- Linear evaluation of a finite tagged sum. -/
def evaluate (C : FiniteTaggedCollector P A) : (P →₀ ℤ) →ₗ[ℤ] A :=
  Finsupp.linearCombination ℤ C.value

@[simp]
theorem evaluate_single (C : FiniteTaggedCollector P A) (p : P) (n : ℤ) :
    C.evaluate (Finsupp.single p n) = n • C.value p := by
  simp [evaluate]

/-- One recursive normalization layer. -/
private def normalFormStep (C : FiniteTaggedCollector P A) (p : P)
    (rec : ∀ q, C.relation q p → P →₀ ℤ) : P →₀ ℤ :=
  match h : C.expansion p with
  | none => Finsupp.single p 1
  | some qs => (qs.attach.map fun q ↦
      q.1.1 • rec q.1.2 (C.decreases h q.1 q.2)).sum

/-- Fully collected finite normal form. -/
def normalForm (C : FiniteTaggedCollector P A) (p : P) : P →₀ ℤ :=
  C.wellFounded.fix (fun p rec ↦ C.normalFormStep p rec) p

/-- Evaluating a fully collected normal form recovers the value of the original tag. -/
theorem evaluate_normalForm (C : FiniteTaggedCollector P A) (p : P) :
    C.evaluate (C.normalForm p) = C.value p := by
  induction p using C.wellFounded.induction with
  | h p ih =>
      rw [normalForm, C.wellFounded.fix_eq]
      unfold normalFormStep
      split
      · simp
      · rename_i qs hexpand
        rw [map_list_sum]
        simp only [List.map_map]
        calc
          (qs.attach.map fun q ↦
              C.evaluate (q.1.1 • C.normalForm q.1.2)).sum =
              (qs.attach.map fun q ↦ q.1.1 • C.value q.1.2).sum := by
                congr 1
                apply List.map_congr_left
                intro q hq
                rw [map_smul, ih q.1.2 (C.decreases hexpand q.1 q.2)]
          _ = (qs.map fun q ↦ q.1 • C.value q.2).sum := by
                exact congrArg List.sum
                  (List.attach_map_val
                    (l := qs) (f := fun q ↦ q.1 • C.value q.2))
          _ = C.value p := C.preserves hexpand

/-- A terminal tag is already in normal form. -/
theorem normalForm_eq_single_of_terminal (C : FiniteTaggedCollector P A)
    {p : P} (hp : C.expansion p = none) :
    C.normalForm p = Finsupp.single p 1 := by
  rw [normalForm, C.wellFounded.fix_eq]
  unfold normalFormStep
  split
  · rfl
  · rename_i qs hsome
    rw [hp] at hsome
    contradiction

/-- A nonterminal tag has coefficient zero in every fully collected normal form. -/
theorem normalForm_apply_eq_zero_of_nonterminal
    (C : FiniteTaggedCollector P A) (p q : P)
    (hq : C.expansion q ≠ none) : C.normalForm p q = 0 := by
  induction p using C.wellFounded.induction with
  | h p ih =>
      rw [normalForm, C.wellFounded.fix_eq]
      unfold normalFormStep
      split
      · rename_i hp
        have hpq : p ≠ q := by
          intro hpq
          subst p
          exact hq hp
        simp [hpq]
      · rename_i qs hexpand
        have hsum (xs : List (P →₀ ℤ)) :
            xs.sum q = (xs.map fun f ↦ f q).sum := by
          induction xs with
          | nil => simp
          | cons x xs ihxs => simp [ihxs]
        rw [hsum]
        simp only [List.map_map]
        apply List.sum_eq_zero
        intro z hz
        simp only [List.mem_map] at hz
        obtain ⟨r, hr, rfl⟩ := hz
        change r.1.1 • C.normalForm r.1.2 q = 0
        rw [ih r.1.2 (C.decreases hexpand r.1 r.2), smul_zero]

/-- Consequently, every tag occurring in the support of a normal form is terminal. -/
theorem expansion_eq_none_of_mem_normalForm_support
    (C : FiniteTaggedCollector P A) {p q : P}
    (hq : q ∈ (C.normalForm p).support) : C.expansion q = none := by
  by_contra hnonterminal
  exact Finsupp.mem_support_iff.mp hq
    (C.normalForm_apply_eq_zero_of_nonterminal p q hnonterminal)

end FiniteTaggedCollector

end

end DegreeFive

end LieRings
