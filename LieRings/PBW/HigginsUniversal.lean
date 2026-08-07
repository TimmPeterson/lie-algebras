import LieRings.PBW.Higgins
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.Logic.Relation

/-!
# The universal property of Higgins's canonical Lie structure

This file formalizes Higgins, Theorem 3 and Theorem 4.  The core construction sorts words in the
free associative algebra.  Swapping an inverted adjacent pair records the corresponding bracket
in the target Lie structure.  The two possible critical overlaps are precisely axioms (L2) and
(L3).
-/

namespace LieRings.PBW.Higgins

universe u v

noncomputable section

variable (M : Type u) [AddCommGroup M]

section Target

variable {A : Type v} [AddCommGroup A]
variable [Module (TensorAlgebra ℤ M) A] [Module (TensorAlgebra ℤ M)ᵐᵒᵖ A]
variable [SMulCommClass (TensorAlgebra ℤ M) (TensorAlgebra ℤ M)ᵐᵒᵖ A]
variable (target : LieStructure M A)

/-- The tensor word associated with a list of elements of the underlying module. -/
def lieWord (w : List M) : TensorAlgebra ℤ M :=
  (w.map (TensorAlgebra.ι ℤ)).prod

@[simp]
theorem lieWord_nil : lieWord M [] = 1 :=
  rfl

@[simp]
theorem lieWord_cons (x : M) (w : List M) :
    lieWord M (x :: w) = TensorAlgebra.ι ℤ x * lieWord M w :=
  rfl

@[simp]
theorem lieWord_append (u w : List M) :
    lieWord M (u ++ w) = lieWord M u * lieWord M w := by
  simp [lieWord, List.map_append]

/-- The correction contributed by swapping `x > y` inside the word `left ++ x :: y :: right`. -/
def swapCorrection (left : List M) (x y : M) (right : List M) : A :=
  MulOpposite.op (lieWord M right) • (lieWord M left • target.bracket x y)

/-- A word together with the accumulated correction in the target Lie structure. -/
abbrev ReductionState := List M × A

/-- One oriented adjacent sorting step, carrying its bracket correction. -/
inductive LieWordStep [LinearOrder M] : (List M × A) → (List M × A) → Prop
  | swap (left right : List M) (x y : M) (a : A) (hxy : y < x) :
      LieWordStep (left ++ x :: y :: right, a)
        (left ++ y :: x :: right, a + swapCorrection M target left x y right)

/-- The reflexive-transitive closure of the correction-carrying word reduction. -/
abbrev LieWordRed [LinearOrder M] := Relation.ReflTransGen (LieWordStep M target)

theorem LieWordStep.to_red [LinearOrder M] {s t : List M × A}
    (h : LieWordStep M target s t) : LieWordRed M target s t :=
  Relation.ReflTransGen.single h

/-- The number of inversions in a word. -/
def inversionCount [LinearOrder M] : List M → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + inversionCount xs

/-- Swapping an inverted adjacent pair removes exactly one inversion, also inside an arbitrary
prefix. -/
theorem inversionCount_swap [LinearOrder M]
    (left right : List M) (x y : M) (hxy : y < x) :
    inversionCount M (left ++ x :: y :: right) =
      inversionCount M (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnx : ¬x < y := not_lt_of_ge (le_of_lt hxy)
      simp [inversionCount, hxy, hnx, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, inversionCount]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp <;> omega
      rw [hfilter, ih]
      omega

/-- Alternation (L1) implies skew-symmetry of the distinguished bracket. -/
theorem LieStructure.bracket_skew (x y : M) :
    target.bracket y x = -target.bracket x y := by
  have h := target.lie_self (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  rw [target.lie_self x, target.lie_self y] at h
  simp only [zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The three-letter critical pair is exactly the Jacobi axiom (L3). -/
theorem overlapCorrection_core (a b c : M) :
    MulOpposite.op (TensorAlgebra.ι ℤ c) • target.bracket a b +
          TensorAlgebra.ι ℤ b • target.bracket a c +
        MulOpposite.op (TensorAlgebra.ι ℤ a) • target.bracket b c =
      TensorAlgebra.ι ℤ a • target.bracket b c +
          MulOpposite.op (TensorAlgebra.ι ℤ b) • target.bracket a c +
        TensorAlgebra.ι ℤ c • target.bracket a b := by
  have h := target.jacobi a b c
  rw [LieStructure.bracket_skew M target a c, smul_neg, smul_neg] at h
  rw [← sub_eq_zero]
  convert h using 1 <;> abel

/-- Two separated adjacent swaps commute; the required correction identity is precisely (L2). -/
theorem disjointCorrection_core (a b c d : M) (t : TensorAlgebra ℤ M) :
    MulOpposite.op (t * TensorAlgebra.ι ℤ c * TensorAlgebra.ι ℤ d) •
          target.bracket a b +
        (TensorAlgebra.ι ℤ b * TensorAlgebra.ι ℤ a * t) • target.bracket c d =
      (TensorAlgebra.ι ℤ a * TensorAlgebra.ι ℤ b * t) • target.bracket c d +
        MulOpposite.op (t * TensorAlgebra.ι ℤ d * TensorAlgebra.ι ℤ c) •
          target.bracket a b := by
  have h := target.balance a b c d t
  simp only [LieRing.of_associative_ring_bracket, MulOpposite.op_sub,
    sub_mul, sub_smul] at h
  have h' :
      MulOpposite.op (t * TensorAlgebra.ι ℤ c * TensorAlgebra.ι ℤ d) •
            target.bracket a b -
          MulOpposite.op (t * TensorAlgebra.ι ℤ d * TensorAlgebra.ι ℤ c) •
            target.bracket a b =
        (TensorAlgebra.ι ℤ a * TensorAlgebra.ι ℤ b * t) • target.bracket c d -
          (TensorAlgebra.ι ℤ b * TensorAlgebra.ι ℤ a * t) • target.bracket c d := by
    simpa only [← mul_smul, MulOpposite.op_mul, MulOpposite.unop_op, mul_assoc]
      using h
  exact sub_eq_sub_iff_add_eq_add.mp h'

/-- The overlapping critical-pair identity inside arbitrary surrounding words. -/
theorem overlapCorrection (left right : List M) (a b c : M) :
    swapCorrection M target left a b (c :: right) +
          swapCorrection M target (left ++ [b]) a c right +
        swapCorrection M target left b c (a :: right) =
      swapCorrection M target (left ++ [a]) b c right +
          swapCorrection M target left a c (b :: right) +
        swapCorrection M target (left ++ [c]) a b right := by
  have h := overlapCorrection_core M target a b c
  have ho := congrArg
    (fun z : A ↦ MulOpposite.op (lieWord M right) • (lieWord M left • z)) h
  simpa only [swapCorrection, lieWord_cons, lieWord_append, lieWord_nil, mul_one,
    smul_add, ← mul_smul, MulOpposite.op_mul, MulOpposite.unop_op, mul_assoc,
    smul_comm] using ho

/-- The separated critical-pair identity inside arbitrary surrounding words. -/
theorem disjointCorrection (left middle right : List M) (a b c d : M) :
    swapCorrection M target left a b (middle ++ c :: d :: right) +
        swapCorrection M target (left ++ b :: a :: middle) c d right =
      swapCorrection M target (left ++ a :: b :: middle) c d right +
        swapCorrection M target left a b (middle ++ d :: c :: right) := by
  have h := disjointCorrection_core M target a b c d (lieWord M middle)
  have ho := congrArg
    (fun z : A ↦ MulOpposite.op (lieWord M right) • (lieWord M left • z)) h
  simpa only [swapCorrection, lieWord_cons, lieWord_append, lieWord_nil, mul_one,
    smul_add, ← mul_smul, MulOpposite.op_mul, MulOpposite.unop_op, mul_assoc,
    smul_comm] using ho

/-- Local confluence when the first selected inversion is at the beginning of the remaining word.
The singleton-prefix case is the Jacobi overlap; a prefix of length at least two is the separated
(L2) case. -/
theorem LieWordStep.localConfluent_nil_left [LinearOrder M]
    (pre right₁ left₂ right₂ : List M) (x₁ y₁ x₂ y₂ : M) (a : A)
    (h₁ : y₁ < x₁) (h₂ : y₂ < x₂)
    (heq : pre ++ x₁ :: y₁ :: right₁ =
      pre ++ left₂ ++ x₂ :: y₂ :: right₂) :
    Relation.Join (LieWordRed M target)
      (pre ++ y₁ :: x₁ :: right₁,
        a + swapCorrection M target pre x₁ y₁ right₁)
      (pre ++ left₂ ++ y₂ :: x₂ :: right₂,
        a + swapCorrection M target (pre ++ left₂) x₂ y₂ right₂) := by
  have heq' : x₁ :: y₁ :: right₁ = left₂ ++ x₂ :: y₂ :: right₂ :=
    List.append_cancel_left (by simpa only [List.append_assoc] using heq)
  cases left₂ with
  | nil =>
      simp only [List.nil_append] at heq' ⊢
      simp only [List.cons.injEq] at heq'
      rcases heq' with ⟨rfl, rfl, rfl⟩
      refine ⟨_, Relation.ReflTransGen.refl, ?_⟩
      simpa only [List.append_nil] using
        (Relation.ReflTransGen.refl : LieWordRed M target
          (pre ++ y₁ :: x₁ :: right₁,
            a + swapCorrection M target pre x₁ y₁ right₁)
          (pre ++ y₁ :: x₁ :: right₁,
            a + swapCorrection M target pre x₁ y₁ right₁))
  | cons z zs =>
      cases zs with
      | nil =>
          simp only [List.cons_append, List.nil_append] at heq'
          simp only [List.cons.injEq] at heq'
          rcases heq' with ⟨rfl, rfl, rfl⟩
          let finalCorrection :=
            (a + swapCorrection M target pre x₁ y₁ (y₂ :: right₂) +
                swapCorrection M target (pre ++ [y₁]) x₁ y₂ right₂) +
              swapCorrection M target pre y₁ y₂ (x₁ :: right₂)
          let finalState : List M × A :=
            (pre ++ y₂ :: y₁ :: x₁ :: right₂, finalCorrection)
          refine ⟨finalState, ?_, ?_⟩
          · have hs₁ := LieWordStep.swap (M := M) (target := target)
                  (pre ++ [y₁]) right₂ x₁ y₂
                  (a + swapCorrection M target pre x₁ y₁ (y₂ :: right₂))
                  (lt_trans h₂ h₁)
            have hs₁' : LieWordStep M target
                (pre ++ y₁ :: x₁ :: y₂ :: right₂,
                  a + swapCorrection M target pre x₁ y₁ (y₂ :: right₂))
                (pre ++ y₁ :: y₂ :: x₁ :: right₂,
                  a + swapCorrection M target pre x₁ y₁ (y₂ :: right₂) +
                    swapCorrection M target (pre ++ [y₁]) x₁ y₂ right₂) := by
              simpa only [List.append_assoc, List.singleton_append] using hs₁
            refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single hs₁') ?_
            convert LieWordStep.swap (M := M) (target := target)
              pre (x₁ :: right₂) y₁ y₂
              (a + swapCorrection M target pre x₁ y₁ (y₂ :: right₂) +
                swapCorrection M target (pre ++ [y₁]) x₁ y₂ right₂) h₂ using 1
          · have hcorr := overlapCorrection M target pre right₂ x₁ y₁ y₂
            have hcorr' := congrArg (fun q : A ↦ a + q) hcorr
            have hs₂ := LieWordStep.swap (M := M) (target := target)
                    pre (y₁ :: right₂) x₁ y₂
                    (a + swapCorrection M target (pre ++ [x₁]) y₁ y₂ right₂)
                    (lt_trans h₂ h₁)
            have hs₂' : LieWordStep M target
                (pre ++ x₁ :: y₂ :: y₁ :: right₂,
                  a + swapCorrection M target (pre ++ [x₁]) y₁ y₂ right₂)
                (pre ++ y₂ :: x₁ :: y₁ :: right₂,
                  a + swapCorrection M target (pre ++ [x₁]) y₁ y₂ right₂ +
                    swapCorrection M target pre x₁ y₂ (y₁ :: right₂)) := by
              simpa only using hs₂
            have hs₃ := LieWordStep.swap (M := M) (target := target)
              (pre ++ [y₂]) right₂ x₁ y₁
              (a + swapCorrection M target (pre ++ [x₁]) y₁ y₂ right₂ +
                swapCorrection M target pre x₁ y₂ (y₁ :: right₂)) h₁
            have hs₃' : LieWordStep M target
                (pre ++ y₂ :: x₁ :: y₁ :: right₂,
                  a + swapCorrection M target (pre ++ [x₁]) y₁ y₂ right₂ +
                    swapCorrection M target pre x₁ y₂ (y₁ :: right₂))
                (pre ++ y₂ :: y₁ :: x₁ :: right₂,
                  a + swapCorrection M target (pre ++ [x₁]) y₁ y₂ right₂ +
                    swapCorrection M target pre x₁ y₂ (y₁ :: right₂) +
                      swapCorrection M target (pre ++ [y₂]) x₁ y₁ right₂) := by
              simpa only [List.append_assoc, List.singleton_append] using hs₃
            have path := Relation.ReflTransGen.tail
              (Relation.ReflTransGen.single hs₂') hs₃'
            convert path using 1
            · simp only [List.append_assoc, List.singleton_append]
            · simp only [finalState, finalCorrection, List.append_assoc,
                List.singleton_append]
              abel_nf at hcorr' ⊢
              exact congrArg (fun q : A ↦ (pre ++ y₂ :: y₁ :: x₁ :: right₂, q)) hcorr'
      | cons z₂ tail =>
          simp only [List.cons_append] at heq'
          simp only [List.cons.injEq] at heq'
          rcases heq' with ⟨rfl, rfl, rfl⟩
          let finalCorrection :=
            a + swapCorrection M target pre x₁ y₁
                (tail ++ x₂ :: y₂ :: right₂) +
              swapCorrection M target (pre ++ y₁ :: x₁ :: tail) x₂ y₂ right₂
          let finalState : List M × A :=
            (pre ++ y₁ :: x₁ :: tail ++ y₂ :: x₂ :: right₂, finalCorrection)
          refine ⟨finalState, ?_, ?_⟩
          · convert Relation.ReflTransGen.single
              (LieWordStep.swap (M := M) (target := target)
                (pre ++ y₁ :: x₁ :: tail) right₂ x₂ y₂
                (a + swapCorrection M target pre x₁ y₁
                  (tail ++ x₂ :: y₂ :: right₂)) h₂) using 1 <;>
              simp only [finalState, finalCorrection, List.cons_append, List.append_assoc]
          · have hcorr := disjointCorrection M target pre tail right₂ x₁ y₁ x₂ y₂
            have hfinal : finalCorrection =
                a + swapCorrection M target (pre ++ x₁ :: y₁ :: tail) x₂ y₂ right₂ +
                  swapCorrection M target pre x₁ y₁ (tail ++ y₂ :: x₂ :: right₂) := by
              dsimp only [finalCorrection]
              rw [add_assoc, hcorr, ← add_assoc]
            convert Relation.ReflTransGen.single
              (LieWordStep.swap (M := M) (target := target)
                pre (tail ++ y₂ :: x₂ :: right₂) x₁ y₁
                (a + swapCorrection M target (pre ++ x₁ :: y₁ :: tail)
                  x₂ y₂ right₂) h₁) using 1
            · simp only [finalState, List.cons_append, List.append_assoc]
            ·
              simpa only [finalState, finalCorrection, List.cons_append, List.append_assoc] using
                congrArg
                  (fun q : A ↦ (pre ++ y₁ :: x₁ :: tail ++ y₂ :: x₂ :: right₂, q))
                  hfinal

/-- Constructor data for a one-step reduction, exposed without dependent pattern matching. -/
theorem LieWordStep.exists_swap [LinearOrder M] {s t : List M × A}
    (h : LieWordStep M target s t) :
    ∃ (left right : List M) (x y : M) (a : A) (hxy : y < x),
      s = (left ++ x :: y :: right, a) ∧
      t = (left ++ y :: x :: right,
        a + swapCorrection M target left x y right) := by
  cases h with
  | swap left right x y a hxy => exact ⟨left, right, x, y, a, hxy, rfl, rfl⟩

/-- Local confluence for two arbitrary positions after a common prefix. -/
theorem LieWordStep.localConfluent_prefix [LinearOrder M]
    (pre left₁ right₁ left₂ right₂ : List M)
    (x₁ y₁ x₂ y₂ : M) (a : A) (h₁ : y₁ < x₁) (h₂ : y₂ < x₂)
    (heq : pre ++ left₁ ++ x₁ :: y₁ :: right₁ =
      pre ++ left₂ ++ x₂ :: y₂ :: right₂) :
    Relation.Join (LieWordRed M target)
      (pre ++ left₁ ++ y₁ :: x₁ :: right₁,
        a + swapCorrection M target (pre ++ left₁) x₁ y₁ right₁)
      (pre ++ left₂ ++ y₂ :: x₂ :: right₂,
        a + swapCorrection M target (pre ++ left₂) x₂ y₂ right₂) := by
  induction left₁ generalizing pre left₂ with
  | nil =>
      simpa only [List.nil_append, List.append_nil] using
        LieWordStep.localConfluent_nil_left M target pre right₁ left₂ right₂
          x₁ y₁ x₂ y₂ a h₁ h₂ (by
            simpa only [List.nil_append, List.append_nil] using heq)
  | cons z₁ tail₁ ih =>
      cases left₂ with
      | nil =>
          obtain ⟨d, hd₂, hd₁⟩ := (by
              simpa only [List.nil_append, List.append_nil] using
                LieWordStep.localConfluent_nil_left M target pre right₂ (z₁ :: tail₁) right₁
                  x₂ y₂ x₁ y₁ a h₂ h₁ (by
                    simpa only [List.nil_append, List.append_nil] using heq.symm))
          refine ⟨d, ?_, ?_⟩
          · simpa only [List.append_nil] using hd₁
          · simpa only [List.append_nil] using hd₂
      | cons z₂ tail₂ =>
          have heq' : z₁ :: tail₁ ++ x₁ :: y₁ :: right₁ =
              z₂ :: tail₂ ++ x₂ :: y₂ :: right₂ :=
            List.append_cancel_left (by simpa only [List.append_assoc] using heq)
          have hz : z₁ = z₂ := (List.cons.inj heq').1
          subst z₂
          have htail : tail₁ ++ x₁ :: y₁ :: right₁ =
              tail₂ ++ x₂ :: y₂ :: right₂ := by
            exact (List.cons.inj heq').2
          have hrec := congrArg (fun w : List M ↦ (pre ++ [z₁]) ++ w) htail
          simpa only [List.cons_append, List.append_assoc, List.singleton_append] using
            ih (pre := pre ++ [z₁]) (left₂ := tail₂) (by
              simpa only [List.append_assoc] using hrec)

/-- Any two one-step word reductions admit a common reduct. -/
theorem LieWordStep.localConfluent [LinearOrder M] {s t u : List M × A}
    (h₁ : LieWordStep M target s t) (h₂ : LieWordStep M target s u) :
    Relation.Join (LieWordRed M target) t u := by
  obtain ⟨left₁, right₁, x₁, y₁, a₁, hxy₁, hs₁, ht⟩ :=
    LieWordStep.exists_swap M target h₁
  obtain ⟨left₂, right₂, x₂, y₂, a₂, hxy₂, hs₂, hu⟩ :=
    LieWordStep.exists_swap M target h₂
  have hsource := hs₁.symm.trans hs₂
  have hword : left₁ ++ x₁ :: y₁ :: right₁ =
      left₂ ++ x₂ :: y₂ :: right₂ := congrArg Prod.fst hsource
  have ha : a₁ = a₂ := congrArg Prod.snd hsource
  subst a₂
  subst t
  subst u
  simpa only [List.nil_append] using
    (LieWordStep.localConfluent_prefix M target [] left₁ right₁ left₂ right₂
      x₁ y₁ x₂ y₂ a₁ hxy₁ hxy₂ hword)

/-- A reduction step strictly decreases the inversion count of its word component. -/
theorem LieWordStep.inversionCount_lt [LinearOrder M] {s t : List M × A}
    (h : LieWordStep M target s t) :
    inversionCount M t.1 < inversionCount M s.1 := by
  cases h with
  | swap left right x y a hxy =>
      change inversionCount M (left ++ y :: x :: right) <
        inversionCount M (left ++ x :: y :: right)
      rw [inversionCount_swap M left right x y hxy]
      omega

/-- A finite reduction cannot increase inversion count. -/
theorem LieWordRed.inversionCount_le [LinearOrder M] {s t : List M × A}
    (h : LieWordRed M target s t) :
    inversionCount M t.1 ≤ inversionCount M s.1 := by
  induction h with
  | refl => exact le_rfl
  | tail hst htu ih =>
      exact le_trans (Nat.le_of_lt (LieWordStep.inversionCount_lt M target htu)) ih

/-- Newman's lemma for the correction-carrying word reduction: termination and the two critical
pair identities imply global confluence. -/
theorem LieWordRed.confluent [LinearOrder M] {s t u : List M × A}
    (hst : LieWordRed M target s t) (hsu : LieWordRed M target s u) :
    Relation.Join (LieWordRed M target) t u := by
  let measureState : (List M × A) → ℕ := fun q ↦ inversionCount M q.1
  suffices h : ∀ s : List M × A, ∀ t u,
      LieWordRed M target s t → LieWordRed M target s u →
        Relation.Join (LieWordRed M target) t u by
    exact h s t u hst hsu
  intro s
  induction s using (measure measureState).wf.induction with
  | h s ih =>
      intro t u hst hsu
      rcases hst.cases_head with hst0 | ⟨s₁, hs₁, h₁t⟩
      · subst t
        exact ⟨u, hsu, Relation.ReflTransGen.refl⟩
      rcases hsu.cases_head with hsu0 | ⟨s₂, hs₂, h₂u⟩
      · subst u
        exact ⟨t, Relation.ReflTransGen.refl, hst⟩
      obtain ⟨d, h₁d, h₂d⟩ := LieWordStep.localConfluent M target hs₁ hs₂
      have hs₁lt : measureState s₁ < measureState s :=
        LieWordStep.inversionCount_lt M target hs₁
      have hs₂lt : measureState s₂ < measureState s :=
        LieWordStep.inversionCount_lt M target hs₂
      obtain ⟨e, hte, hde⟩ := ih s₁ hs₁lt t d h₁t h₁d
      obtain ⟨f, huf, hdf⟩ := ih s₂ hs₂lt u d h₂u h₂d
      have hdlt : measureState d < measureState s :=
        lt_of_le_of_lt (LieWordRed.inversionCount_le M target h₁d) hs₁lt
      obtain ⟨g, heg, hfg⟩ := ih d hdlt e f hde hdf
      exact ⟨g, hte.trans heg, huf.trans hfg⟩

/-- Every state reaches a state on which no further adjacent swap is possible. -/
theorem LieWordRed.exists_normal [LinearOrder M] (s : List M × A) :
    ∃ t, LieWordRed M target s t ∧ ∀ u, ¬LieWordStep M target t u := by
  suffices h : ∀ n, ∀ s : List M × A, inversionCount M s.1 = n →
      ∃ t, LieWordRed M target s t ∧ ∀ u, ¬LieWordStep M target t u by
    exact h (inversionCount M s.1) s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro s hs
      by_cases hstep : ∃ u, LieWordStep M target s u
      · obtain ⟨u, hsu⟩ := hstep
        have hlt : inversionCount M u.1 < n := by
          rw [← hs]
          exact LieWordStep.inversionCount_lt M target hsu
        obtain ⟨t, hut, ht⟩ := ih (inversionCount M u.1) hlt u rfl
        exact ⟨t, Relation.ReflTransGen.head hsu hut, ht⟩
      · exact ⟨s, Relation.ReflTransGen.refl, fun u hsu ↦ hstep ⟨u, hsu⟩⟩

/-- A chosen normal endpoint of the terminating reduction. -/
noncomputable def normalState [LinearOrder M] (s : List M × A) : List M × A :=
  Classical.choose (LieWordRed.exists_normal M target s)

theorem LieWordRed.to_normalState [LinearOrder M] (s : List M × A) :
    LieWordRed M target s (normalState M target s) :=
  (Classical.choose_spec (LieWordRed.exists_normal M target s)).1

theorem normalState_is_normal [LinearOrder M] (s : List M × A) (u : List M × A) :
    ¬LieWordStep M target (normalState M target s) u :=
  (Classical.choose_spec (LieWordRed.exists_normal M target s)).2 u

theorem LieWordRed.eq_of_normal [LinearOrder M] {s t : List M × A}
    (hs : ∀ u, ¬LieWordStep M target s u) (hst : LieWordRed M target s t) : t = s := by
  rcases hst.cases_head with h | ⟨u, hsu, _⟩
  · exact h.symm
  · exact (hs u hsu).elim

/-- Confluence makes the chosen normal endpoint equal to every normal endpoint. -/
theorem normalState_eq_of_red_normal [LinearOrder M] {s t : List M × A}
    (hst : LieWordRed M target s t) (ht : ∀ u, ¬LieWordStep M target t u) :
    normalState M target s = t := by
  obtain ⟨d, hnd, htd⟩ := LieWordRed.confluent M target
    (LieWordRed.to_normalState M target s) hst
  have hd₁ := LieWordRed.eq_of_normal M target
    (normalState_is_normal M target s) hnd
  have hd₂ := LieWordRed.eq_of_normal M target ht htd
  exact hd₁.symm.trans hd₂

/-- Add a fixed amount to the accumulated correction without changing the word. -/
def translateState (c : A) (s : List M × A) : List M × A :=
  (s.1, c + s.2)

theorem LieWordStep.translate [LinearOrder M] (c : A) {s t : List M × A}
    (h : LieWordStep M target s t) :
    LieWordStep M target (translateState M c s) (translateState M c t) := by
  cases h with
  | swap left right x y a hxy =>
      convert LieWordStep.swap (M := M) (target := target) left right x y (c + a) hxy using 1
      simp only [translateState, add_assoc]

theorem LieWordRed.translate [LinearOrder M] (c : A) {s t : List M × A}
    (h : LieWordRed M target s t) :
    LieWordRed M target (translateState M c s) (translateState M c t) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ htu ih => exact Relation.ReflTransGen.tail ih (htu.translate M target c)

theorem normal_translateState [LinearOrder M] (c : A) {s : List M × A}
    (hs : ∀ u, ¬LieWordStep M target s u) :
    ∀ u, ¬LieWordStep M target (translateState M c s) u := by
  intro u htu
  obtain ⟨left, right, x, y, a, hxy, hsource, _⟩ :=
    LieWordStep.exists_swap M target htu
  have hw : s.1 = left ++ x :: y :: right := congrArg Prod.fst hsource
  have hs_eq : s = (left ++ x :: y :: right, s.2) := by
    apply Prod.ext
    · exact hw
    · rfl
  apply hs (left ++ y :: x :: right,
    s.2 + swapCorrection M target left x y right)
  rw [hs_eq]
  exact LieWordStep.swap left right x y s.2 hxy

theorem normalState_translate [LinearOrder M] (c : A) (s : List M × A) :
    normalState M target (translateState M c s) =
      translateState M c (normalState M target s) := by
  apply normalState_eq_of_red_normal M target
  · exact (LieWordRed.to_normalState M target s).translate M target c
  · exact normal_translateState M target c (normalState_is_normal M target s)

/-- The correction attached to a word by its unique normal form. -/
noncomputable def wordCorrection [LinearOrder M] (w : List M) : A :=
  (normalState M target (w, 0)).2

theorem normalState_second (w : List M) [LinearOrder M] (a : A) :
    (normalState M target (w, a)).2 = a + wordCorrection M target w := by
  have h := congrArg Prod.snd (normalState_translate M target a (w, 0))
  simpa only [translateState, wordCorrection, add_zero] using h

/-- The correction formula for one adjacent inversion. -/
theorem wordCorrection_swap [LinearOrder M]
    (left right : List M) (x y : M) (hxy : y < x) :
    wordCorrection M target (left ++ x :: y :: right) =
      swapCorrection M target left x y right +
        wordCorrection M target (left ++ y :: x :: right) := by
  have hstep := LieWordStep.swap (M := M) (target := target)
    left right x y (0 : A) hxy
  have hstep' : LieWordStep M target
      (left ++ x :: y :: right, 0)
      (left ++ y :: x :: right, swapCorrection M target left x y right) := by
    simpa only [zero_add] using hstep
  have hnormal : normalState M target
      (left ++ x :: y :: right, 0) =
      normalState M target
        (left ++ y :: x :: right, swapCorrection M target left x y right) := by
    apply normalState_eq_of_red_normal M target
    · exact Relation.ReflTransGen.head hstep'
        (LieWordRed.to_normalState M target
          (left ++ y :: x :: right, swapCorrection M target left x y right))
    · exact normalState_is_normal M target _
  have hsecond := congrArg Prod.snd hnormal
  rw [normalState_second M target (left ++ y :: x :: right)
    (swapCorrection M target left x y right)] at hsecond
  simpa only [wordCorrection, zero_add] using hsecond

/-- The canonical word basis of the tensor algebra on the free presentation. -/
noncomputable def presentationTensorWordBasis :
    Module.Basis (FreeMonoid M) ℤ (PresentationTensor M) :=
  (Finsupp.basisSingleOne (R := ℤ) (ι := M)).tensorAlgebra

/-- The normal-form correction, extended linearly from tensor words. -/
noncomputable def correctionLinearMap [LinearOrder M] :
    PresentationTensor M →ₗ[ℤ] A :=
  (Finsupp.linearCombination ℤ
      (fun w : FreeMonoid M ↦ wordCorrection M target (FreeMonoid.toList w))).comp
    (presentationTensorWordBasis M).repr.toLinearMap

@[simp]
theorem correctionLinearMap_basis [LinearOrder M] (w : FreeMonoid M) :
    correctionLinearMap M target (presentationTensorWordBasis M w) =
      wordCorrection M target (FreeMonoid.toList w) := by
  rw [correctionLinearMap, LinearMap.comp_apply]
  have hr : (↑(presentationTensorWordBasis M).repr :
      PresentationTensor M → (FreeMonoid M →₀ ℤ))
        (presentationTensorWordBasis M w) = Finsupp.single w 1 :=
    Module.Basis.repr_self (presentationTensorWordBasis M) w
  calc
    _ = (Finsupp.linearCombination ℤ
        (fun w : FreeMonoid M ↦ wordCorrection M target (FreeMonoid.toList w)))
          (Finsupp.single w 1) := congrArg _ hr
    _ = wordCorrection M target (FreeMonoid.toList w) := by
      rw [Finsupp.linearCombination_single]
      exact one_smul ℤ _

/-- A word-basis vector is the corresponding product of canonical presentation generators. -/
theorem presentationTensorWordBasis_apply (w : FreeMonoid M) :
    presentationTensorWordBasis M w =
      lieWord (FreePresentation M)
        ((FreeMonoid.toList w).map (canonicalPresentationLift M)) := by
  let b := Finsupp.basisSingleOne (R := ℤ) (ι := M)
  change (TensorAlgebra.equivFreeAlgebra b).symm
      (FreeAlgebra.basisFreeMonoid ℤ M w) = _
  apply (TensorAlgebra.equivFreeAlgebra b).injective
  rw [AlgEquiv.apply_symm_apply]
  simp only [lieWord, map_list_prod, List.map_map, Function.comp_apply]
  have hgen : ∀ x : M,
      TensorAlgebra.equivFreeAlgebra b
          (TensorAlgebra.ι ℤ (canonicalPresentationLift M x)) =
        FreeAlgebra.ι ℤ x := by
    intro x
    exact TensorAlgebra.equivFreeAlgebra_ι_apply b x
  have hfun : (↑(TensorAlgebra.equivFreeAlgebra b) ∘
      ↑(TensorAlgebra.ι ℤ) ∘ canonicalPresentationLift M) = FreeAlgebra.ι ℤ :=
    funext hgen
  rw [hfun]
  rw [FreeAlgebra.basisFreeMonoid, Module.Basis.map_apply]
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (Finsupp.single w 1)) = _
  rw [AlgEquiv.apply_symm_apply]
  induction w using FreeMonoid.recOn with
  | h0 => simp [MonoidAlgebra.one_def]
  | ih x w ih =>
      simp only [FreeMonoid.toList_of_mul, List.map_cons, List.prod_cons, map_mul]
      rw [← ih]
      have hι : FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (FreeAlgebra.ι ℤ x) = Finsupp.single (FreeMonoid.of x) 1 := by
        simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
      rw [hι]
      simp

theorem presentationTensorWordBasis_mul (u w : FreeMonoid M) :
    presentationTensorWordBasis M u * presentationTensorWordBasis M w =
      presentationTensorWordBasis M (u * w) := by
  rw [presentationTensorWordBasis_apply, presentationTensorWordBasis_apply,
    presentationTensorWordBasis_apply]
  simp only [FreeMonoid.toList_mul, List.map_append, lieWord_append]

theorem presentationTensorWordBasis_of (x : M) :
    presentationTensorWordBasis M (FreeMonoid.of x) =
      TensorAlgebra.ι ℤ (canonicalPresentationLift M x) := by
  rw [presentationTensorWordBasis_apply]
  simp [lieWord]

@[simp]
theorem tensorPresentationMap_basis (w : FreeMonoid M) :
    tensorPresentationMap M (presentationTensorWordBasis M w) =
      lieWord M (FreeMonoid.toList w) := by
  rw [presentationTensorWordBasis_apply]
  induction FreeMonoid.toList w with
  | nil => simp
  | cons x xs ih =>
      change tensorPresentationMap M
          (TensorAlgebra.ι ℤ (canonicalPresentationLift M x) *
            lieWord (FreePresentation M) (xs.map (canonicalPresentationLift M))) = _
      rw [map_mul, tensorPresentationMap_ι,
        presentationMap_canonicalPresentationLift, ih]
      rfl

/-- The linear correction sends a basis-word commutator to the prescribed bracket correction. -/
theorem correctionLinearMap_basis_commutator [LinearOrder M]
    (left right : FreeMonoid M) (x y : M) :
    correctionLinearMap M target
        (presentationTensorWordBasis M left *
          ⁅TensorAlgebra.ι ℤ (canonicalPresentationLift M x),
            TensorAlgebra.ι ℤ (canonicalPresentationLift M y)⁆ *
          presentationTensorWordBasis M right) =
      swapCorrection M target (FreeMonoid.toList left) x y (FreeMonoid.toList right) := by
  simp only [LieRing.of_associative_ring_bracket, mul_sub, sub_mul, map_sub]
  rw [← presentationTensorWordBasis_of M x, ← presentationTensorWordBasis_of M y]
  repeat' rw [presentationTensorWordBasis_mul]
  simp only [correctionLinearMap_basis, FreeMonoid.toList_mul, FreeMonoid.toList_of,
    List.singleton_append, List.append_assoc]
  change wordCorrection M target
        (FreeMonoid.toList left ++ x :: y :: FreeMonoid.toList right) -
      wordCorrection M target
        (FreeMonoid.toList left ++ y :: x :: FreeMonoid.toList right) = _
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hskew : swapCorrection M target (FreeMonoid.toList left) y x
        (FreeMonoid.toList right) =
        -swapCorrection M target (FreeMonoid.toList left) x y
          (FreeMonoid.toList right) := by
      rw [swapCorrection, swapCorrection, LieStructure.bracket_skew M target,
        smul_neg, smul_neg]
    rw [wordCorrection_swap M target _ _ y x hxy, hskew]
    abel
  · simp [swapCorrection, target.lie_self]
  · rw [wordCorrection_swap M target _ _ x y hyx]
    abel

/-- Commutators of inserted presentation generators are additive in the first variable. -/
theorem commutator_ι_add_left (p₁ p₂ q : FreePresentation M) :
    ⁅TensorAlgebra.ι ℤ (p₁ + p₂), TensorAlgebra.ι ℤ q⁆ =
      ⁅TensorAlgebra.ι ℤ p₁, TensorAlgebra.ι ℤ q⁆ +
        ⁅TensorAlgebra.ι ℤ p₂, TensorAlgebra.ι ℤ q⁆ := by
  simp only [map_add, LieRing.of_associative_ring_bracket]
  noncomm_ring

theorem commutator_ι_add_right (p q₁ q₂ : FreePresentation M) :
    ⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ (q₁ + q₂)⁆ =
      ⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ q₁⁆ +
        ⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ q₂⁆ := by
  simp only [map_add, LieRing.of_associative_ring_bracket]
  noncomm_ring

theorem commutator_ι_smul_left (c : ℤ) (p q : FreePresentation M) :
    ⁅TensorAlgebra.ι ℤ (c • p), TensorAlgebra.ι ℤ q⁆ =
      c • ⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ q⁆ := by
  rw [map_smul]
  simp only [LieRing.of_associative_ring_bracket]
  rw [smul_mul_assoc, mul_smul_comm, smul_sub]

theorem commutator_ι_smul_right (c : ℤ) (p q : FreePresentation M) :
    ⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ (c • q)⁆ =
      c • ⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ q⁆ := by
  rw [map_smul]
  simp only [LieRing.of_associative_ring_bracket]
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

/-- The correction form `a [p,q] b`, linear in all four variables. -/
noncomputable def correctionCommutatorForm [LinearOrder M] :
    PresentationTensor M →ₗ[ℤ] PresentationTensor M →ₗ[ℤ]
      FreePresentation M →ₗ[ℤ] FreePresentation M →ₗ[ℤ] A :=
  LinearMap.mk₂ ℤ (fun (a b : PresentationTensor M) ↦
    LinearMap.mk₂ ℤ (fun (p q : FreePresentation M) ↦
      correctionLinearMap M target
        (a * ⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ q⁆ * b))
      (by
        intros
        dsimp only
        rw [commutator_ι_add_left, mul_add, add_mul, map_add])
      (by
        intros
        dsimp only
        rw [commutator_ι_smul_left]
        rw [mul_smul_comm, smul_mul_assoc, map_smul])
      (by
        intros
        dsimp only
        rw [commutator_ι_add_right, mul_add, add_mul, map_add])
      (by
        intros
        dsimp only
        rw [commutator_ι_smul_right]
        rw [mul_smul_comm, smul_mul_assoc, map_smul]))
    (by
      intros
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro q
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply]
      change correctionLinearMap M target ((_ + _) * _ * _) = _
      rw [add_mul, add_mul, map_add])
    (by
      intros
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro q
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply]
      change correctionLinearMap M target ((_ • _) * _ * _) = _
      rw [smul_mul_assoc, smul_mul_assoc, map_smul])
    (by
      intros
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro q
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply]
      change correctionLinearMap M target (_ * _ * (_ + _)) = _
      rw [mul_add, map_add])
    (by
      intros
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro q
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply]
      change correctionLinearMap M target (_ * _ * (_ • _)) = _
      rw [mul_smul_comm, map_smul])

theorem tensor_biaction_int_smul (l r : TensorAlgebra ℤ M) (c : ℤ) (z : A) :
    MulOpposite.op r • (l • (c • z)) = c • MulOpposite.op r • (l • z) := by
  calc
    _ = MulOpposite.op r • (c • (l • z)) := congrArg
      (fun w : A ↦ MulOpposite.op r • w)
      (map_zsmul (DistribSMul.toAddMonoidHom A l) c z)
    _ = _ := map_zsmul (DistribSMul.toAddMonoidHom A (MulOpposite.op r)) c (l • z)

/-- The target-action form prescribed by a Higgins Lie structure, linear in the same variables. -/
noncomputable def targetCommutatorForm :
    PresentationTensor M →ₗ[ℤ] PresentationTensor M →ₗ[ℤ]
      FreePresentation M →ₗ[ℤ] FreePresentation M →ₗ[ℤ] A :=
  LinearMap.mk₂ ℤ (fun (a b : PresentationTensor M) ↦
    LinearMap.mk₂ ℤ (fun (p q : FreePresentation M) ↦
      MulOpposite.op (tensorPresentationMap M b) •
        (tensorPresentationMap M a •
          target.bracket (presentationMap M p) (presentationMap M q)))
      (by intros; simp [map_add, add_smul])
      (by
        intro c p q
        simp only [map_smul, LinearMap.smul_apply]
        exact tensor_biaction_int_smul M _ _ c _)
      (by intros; simp [map_add, add_smul])
      (by
        intro c p q
        simp only [map_smul, LinearMap.smul_apply]
        exact tensor_biaction_int_smul M _ _ c _))
    (by
      intros
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro q
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply]
      change MulOpposite.op _ • (tensorPresentationMap M (_ + _) • _) = _
      rw [map_add, add_smul, smul_add])
    (by
      intro c a b
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro q
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply]
      change MulOpposite.op _ • (tensorPresentationMap M (c • a) • _) = _
      rw [map_smul]
      change MulOpposite.op _ • (((c : TensorAlgebra ℤ M) *
        tensorPresentationMap M a) • _) = _
      rw [mul_smul, Int.cast_smul_eq_zsmul]
      change (DistribSMul.toAddMonoidHom A
          (MulOpposite.op (tensorPresentationMap M b))) (c • _) = c • _
      exact map_zsmul (DistribSMul.toAddMonoidHom A
        (MulOpposite.op (tensorPresentationMap M b))) c _)
    (by
      intros
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro q
      simp only [LinearMap.mk₂_apply, LinearMap.add_apply]
      change MulOpposite.op (tensorPresentationMap M (_ + _)) • _ = _
      rw [map_add, MulOpposite.op_add, add_smul])
    (by
      intro c a b
      apply LinearMap.ext
      intro p
      apply LinearMap.ext
      intro q
      simp only [LinearMap.mk₂_apply, LinearMap.smul_apply]
      change MulOpposite.op (tensorPresentationMap M (c • b)) • _ = _
      rw [map_smul]
      change (MulOpposite.op (tensorPresentationMap M b) *
        (c : (TensorAlgebra ℤ M)ᵐᵒᵖ)) • _ = _
      rw [mul_smul, Int.cast_smul_eq_zsmul]
      change (DistribSMul.toAddMonoidHom A
          (MulOpposite.op (tensorPresentationMap M b))) (c • _) = c • _
      exact map_zsmul (DistribSMul.toAddMonoidHom A
        (MulOpposite.op (tensorPresentationMap M b))) c _)

/-- The normal-form correction realizes the prescribed bracket with arbitrary surrounding
tensors and arbitrary presentation lifts. -/
theorem correctionCommutatorForm_eq_target [LinearOrder M] :
    correctionCommutatorForm M target = targetCommutatorForm M target := by
  apply (presentationTensorWordBasis M).ext
  intro left
  apply (presentationTensorWordBasis M).ext
  intro right
  apply (Finsupp.basisSingleOne (R := ℤ) (ι := M)).ext
  intro x
  apply (Finsupp.basisSingleOne (R := ℤ) (ι := M)).ext
  intro y
  change correctionLinearMap M target
      (presentationTensorWordBasis M left *
        ⁅TensorAlgebra.ι ℤ (canonicalPresentationLift M x),
          TensorAlgebra.ι ℤ (canonicalPresentationLift M y)⁆ *
        presentationTensorWordBasis M right) = _
  simp only [targetCommutatorForm, LinearMap.mk₂_apply]
  rw [correctionLinearMap_basis_commutator, tensorPresentationMap_basis,
    tensorPresentationMap_basis]
  change _ = MulOpposite.op _ • (_ • target.bracket
    (presentationMap M (Finsupp.single x 1))
    (presentationMap M (Finsupp.single y 1)))
  rw [presentationMap_single, presentationMap_single]
  change swapCorrection M target (FreeMonoid.toList left) x y
      (FreeMonoid.toList right) =
    MulOpposite.op (lieWord M (FreeMonoid.toList right)) •
      (lieWord M (FreeMonoid.toList left) • target.bracket x y)
  rfl

/-- Pointwise form of `correctionCommutatorForm_eq_target`: the normal-form correction of an
elementary commutator, with arbitrary tensors on either side, is the corresponding bracket with
the evaluated tensors acting on it. -/
theorem correctionLinearMap_mul_commutator_mul [LinearOrder M]
    (a b : PresentationTensor M) (p q : FreePresentation M) :
    correctionLinearMap M target
        (a * ⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ q⁆ * b) =
      MulOpposite.op (tensorPresentationMap M b) •
        (tensorPresentationMap M a •
          target.bracket (presentationMap M p) (presentationMap M q)) := by
  have h := congrArg
    (fun f ↦ f a b p q) (correctionCommutatorForm_eq_target M target)
  simpa only [correctionCommutatorForm, targetCommutatorForm,
    LinearMap.mk₂_apply] using h

/-- On the commutator ideal, the correction map intertwines multiplication in the presentation
tensor algebra with the prescribed left and right actions after evaluation. -/
theorem correctionLinearMap_bimodule [LinearOrder M]
    (k : commutatorIdeal M) (a b : PresentationTensor M) :
    correctionLinearMap M target (a * (k : PresentationTensor M) * b) =
      MulOpposite.op (tensorPresentationMap M b) •
        (tensorPresentationMap M a •
          correctionLinearMap M target (k : PresentationTensor M)) := by
  let generatorIdeal := TwoSidedIdeal.span
    (Set.range fun pq : FreePresentation M × FreePresentation M ↦
      ⁅TensorAlgebra.ι ℤ pq.1, TensorAlgebra.ι ℤ pq.2⁆)
  have hk : (k : PresentationTensor M) ∈ generatorIdeal := by
    change (k : PresentationTensor M) ∈
      elementaryCommutatorIdeal (FreePresentation M)
    rw [elementaryCommutatorIdeal_eq_tensorCommutatorIdeal]
    exact k.property
  have hspan : ∀ (u : PresentationTensor M) (hu : u ∈ generatorIdeal),
      ∀ a b : PresentationTensor M,
        correctionLinearMap M target (a * u * b) =
          MulOpposite.op (tensorPresentationMap M b) •
            (tensorPresentationMap M a • correctionLinearMap M target u) := by
    intro u hu
    induction hu using TwoSidedIdeal.span_induction with
    | mem u hu =>
        obtain ⟨⟨p, q⟩, rfl⟩ := hu
        intro a b
        change correctionLinearMap M target
            (a * ⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ q⁆ * b) = _
        rw [correctionLinearMap_mul_commutator_mul]
        have hbase := correctionLinearMap_mul_commutator_mul M target
          (1 : PresentationTensor M) (1 : PresentationTensor M) p q
        simp only [one_mul, mul_one, map_one, MulOpposite.op_one, one_smul] at hbase
        rw [hbase]
    | zero =>
        intro a b
        simp
    | add x y _ _ hx hy =>
        intro a b
        rw [mul_add, add_mul, map_add, hx a b, hy a b, map_add, smul_add, smul_add]
    | neg x _ hx =>
        intro a b
        rw [mul_neg, neg_mul, map_neg, hx a b, map_neg, smul_neg, smul_neg]
    | left_absorb c x _ hx =>
        intro a b
        rw [← mul_assoc, hx (a * c) b]
        have hcx := hx c 1
        simp only [mul_one, map_one, MulOpposite.op_one, one_smul] at hcx
        rw [hcx]
        simp only [map_mul, mul_smul]
    | right_absorb c x _ hx =>
        intro a b
        rw [show a * (x * c) * b = a * x * (c * b) by simp [mul_assoc], hx a (c * b)]
        have hxc := hx 1 c
        simp only [one_mul, map_one, one_smul] at hxc
        rw [hxc]
        simp only [map_mul, MulOpposite.op_mul, mul_smul]
        rw [smul_comm (tensorPresentationMap M a)
          (MulOpposite.op (tensorPresentationMap M c))]
  exact hspan (k : PresentationTensor M) hk a b

/-- Any associative commutator in the presentation tensor algebra lies in its commutator ideal. -/
def commutatorElement (s t : PresentationTensor M) : commutatorIdeal M :=
  ⟨⁅s, t⁆, by
    rw [commutatorIdeal, RingHom.mem_ker]
    simp [LieRing.of_associative_ring_bracket, mul_comm]⟩

@[simp]
theorem commutatorElement_coe (s t : PresentationTensor M) :
    (commutatorElement M s t : PresentationTensor M) = ⁅s, t⁆ :=
  rfl

/-- The correction vanishes on the commutator of a presentation word with a degree-one defining
relation.  This is the basic relation calculation needed for descent. -/
theorem correctionLinearMap_lieWord_commutator_relation [LinearOrder M]
    (r : PresentationRelations M) (xs : List M) :
    correctionLinearMap M target
        ⁅lieWord (FreePresentation M) (xs.map (canonicalPresentationLift M)),
          TensorAlgebra.ι ℤ (r : FreePresentation M)⁆ = 0 := by
  induction xs with
  | nil => simp [lieWord, LieRing.of_associative_ring_bracket]
  | cons x xs ih =>
      let tail : PresentationTensor M :=
        lieWord (FreePresentation M) (xs.map (canonicalPresentationLift M))
      let ix : PresentationTensor M :=
        TensorAlgebra.ι ℤ (canonicalPresentationLift M x)
      let ir : PresentationTensor M := TensorAlgebra.ι ℤ (r : FreePresentation M)
      have hword : lieWord (FreePresentation M)
          ((x :: xs).map (canonicalPresentationLift M)) = ix * tail := by
        rfl
      rw [hword]
      have hcomm : ⁅ix * tail, ir⁆ = ix * ⁅tail, ir⁆ + ⁅ix, ir⁆ * tail := by
        simp only [LieRing.of_associative_ring_bracket]
        noncomm_ring
      rw [hcomm, map_add]
      have hleft := correctionLinearMap_bimodule M target
        (commutatorElement M tail ir) ix 1
      simp only [commutatorElement_coe, mul_one, map_one, MulOpposite.op_one,
        one_smul] at hleft
      rw [hleft, ih, smul_zero, zero_add]
      rw [← one_mul ⁅ix, ir⁆]
      rw [correctionLinearMap_mul_commutator_mul]
      change MulOpposite.op (tensorPresentationMap M tail) •
          (tensorPresentationMap M 1 •
            target.bracket
              (presentationMap M (canonicalPresentationLift M x))
              (presentationMap M (r : FreePresentation M))) = 0
      rw [presentationMap_canonicalPresentationLift, r.property]
      simp

/-- The correction vanishes on the commutator of an arbitrary presentation tensor with a
degree-one defining relation. -/
theorem correctionLinearMap_commutator_ι_relation [LinearOrder M]
    (r : PresentationRelations M) (t : PresentationTensor M) :
    correctionLinearMap M target
        ⁅t, TensorAlgebra.ι ℤ (r : FreePresentation M)⁆ = 0 := by
  let f : PresentationTensor M →ₗ[ℤ] A :=
    { toFun := fun s ↦ correctionLinearMap M target
          ⁅s, TensorAlgebra.ι ℤ (r : FreePresentation M)⁆
      map_add' := by
        intro s t
        have h : ⁅s + t, TensorAlgebra.ι ℤ (r : FreePresentation M)⁆ =
            ⁅s, TensorAlgebra.ι ℤ (r : FreePresentation M)⁆ +
              ⁅t, TensorAlgebra.ι ℤ (r : FreePresentation M)⁆ := by
          simp only [LieRing.of_associative_ring_bracket, add_mul, mul_add]
          abel
        rw [h, map_add]
      map_smul' := by
        intro c s
        have h : ⁅c • s, TensorAlgebra.ι ℤ (r : FreePresentation M)⁆ =
            c • ⁅s, TensorAlgebra.ι ℤ (r : FreePresentation M)⁆ := by
          simp only [LieRing.of_associative_ring_bracket, smul_mul_assoc,
            mul_smul_comm, smul_sub]
        rw [h, map_smul]
        rfl }
  have hf : f = 0 := by
    apply (presentationTensorWordBasis M).ext
    intro w
    change correctionLinearMap M target
        ⁅presentationTensorWordBasis M w,
          TensorAlgebra.ι ℤ (r : FreePresentation M)⁆ = 0
    rw [presentationTensorWordBasis_apply]
    exact correctionLinearMap_lieWord_commutator_relation M target r _
  exact LinearMap.congr_fun hf t

/-- The correction restricted to the presentation commutator ideal. -/
noncomputable def correctionOnCommutator [LinearOrder M] :
    commutatorIdeal M →ₗ[ℤ] A where
  toFun k := correctionLinearMap M target (k : PresentationTensor M)
  map_add' x y := by
    change correctionLinearMap M target
      ((x : PresentationTensor M) + (y : PresentationTensor M)) = _
    rw [map_add]
  map_smul' c x := by
    change correctionLinearMap M target (c • (x : PresentationTensor M)) = _
    rw [map_smul]
    rfl

@[simp]
theorem correctionOnCommutator_apply [LinearOrder M] (k : commutatorIdeal M) :
    correctionOnCommutator M target k =
      correctionLinearMap M target (k : PresentationTensor M) :=
  rfl

/-- Multiplying a commutator-ideal element by a presentation relation on the right is killed by
the correction. -/
theorem correctionLinearMap_commutator_mul_relation [LinearOrder M]
    (k : commutatorIdeal M) (q : relationIdeal M) :
    correctionLinearMap M target
        ((k : PresentationTensor M) * (q : PresentationTensor M)) = 0 := by
  have h := correctionLinearMap_bimodule M target k 1 (q : PresentationTensor M)
  simp only [one_mul, map_one, one_smul] at h
  have hqzero : tensorPresentationMap M (q : PresentationTensor M) = 0 :=
    RingHom.mem_ker.mp (relationIdeal_le_ker_tensorPresentationMap M q.property)
  rw [h, hqzero, MulOpposite.op_zero, zero_smul]

/-- Multiplying a commutator-ideal element by a presentation relation on the left is killed by
the correction. -/
theorem correctionLinearMap_relation_mul_commutator [LinearOrder M]
    (q : relationIdeal M) (k : commutatorIdeal M) :
    correctionLinearMap M target
        ((q : PresentationTensor M) * (k : PresentationTensor M)) = 0 := by
  have h := correctionLinearMap_bimodule M target k (q : PresentationTensor M) 1
  simp only [mul_one, map_one, MulOpposite.op_one, one_smul] at h
  have hqzero : tensorPresentationMap M (q : PresentationTensor M) = 0 :=
    RingHom.mem_ker.mp (relationIdeal_le_ker_tensorPresentationMap M q.property)
  rw [h, hqzero, zero_smul]

/-- The correction vanishes on every generator `[t,q]` of Higgins's relation ideal `Z`, with
`q` allowed to range over the full two-sided presentation relation ideal. -/
theorem correctionLinearMap_relation_commutator [LinearOrder M]
    (t : PresentationTensor M) (q : relationIdeal M) :
    correctionLinearMap M target ⁅t, (q : PresentationTensor M)⁆ = 0 := by
  let u : PresentationTensor M := q
  have hu : u ∈ TwoSidedIdeal.span
    (Set.range fun r : PresentationRelations M ↦
      TensorAlgebra.ι ℤ (r : FreePresentation M)) := q.property
  have hspan : ∀ (u : PresentationTensor M)
      (hu : u ∈ TwoSidedIdeal.span
        (Set.range fun r : PresentationRelations M ↦
          TensorAlgebra.ι ℤ (r : FreePresentation M))),
      correctionLinearMap M target ⁅t, u⁆ = 0 := by
    intro u hu
    induction hu using TwoSidedIdeal.span_induction with
    | mem u hu =>
        obtain ⟨r, rfl⟩ := hu
        exact correctionLinearMap_commutator_ι_relation M target r t
    | zero => simp [LieRing.of_associative_ring_bracket]
    | add x y _ _ hx hy =>
        have hcomm : ⁅t, x + y⁆ = ⁅t, x⁆ + ⁅t, y⁆ := by
          simp only [LieRing.of_associative_ring_bracket, mul_add, add_mul]
          abel
        rw [hcomm, map_add, hx, hy, add_zero]
    | neg x _ hx =>
        have hcomm : ⁅t, -x⁆ = -⁅t, x⁆ := by
          simp only [LieRing.of_associative_ring_bracket, mul_neg, neg_mul]
          abel
        rw [hcomm, map_neg, hx, neg_zero]
    | left_absorb a x hxmem hx =>
        let qx : relationIdeal M := ⟨x, hxmem⟩
        let ktx : commutatorIdeal M := commutatorElement M t x
        have hcomm : ⁅t, a * x⁆ = ⁅t, a⁆ * x + a * ⁅t, x⁆ := by
          simp only [LieRing.of_associative_ring_bracket]
          noncomm_ring
        rw [hcomm, map_add]
        have hright := correctionLinearMap_commutator_mul_relation M target
          (commutatorElement M t a) qx
        have hleft := correctionLinearMap_bimodule M target ktx a 1
        change correctionLinearMap M target (⁅t, a⁆ * x) = 0 at hright
        simp only [mul_one, map_one, MulOpposite.op_one,
          one_smul] at hleft
        change correctionLinearMap M target (a * ⁅t, x⁆) =
          tensorPresentationMap M a • correctionLinearMap M target ⁅t, x⁆ at hleft
        rw [hright, hleft, hx, smul_zero, add_zero]
    | right_absorb a x hxmem hx =>
        let qx : relationIdeal M := ⟨x, hxmem⟩
        let ktx : commutatorIdeal M := commutatorElement M t x
        have hcomm : ⁅t, x * a⁆ = ⁅t, x⁆ * a + x * ⁅t, a⁆ := by
          simp only [LieRing.of_associative_ring_bracket]
          noncomm_ring
        rw [hcomm, map_add]
        have hright := correctionLinearMap_bimodule M target ktx 1 a
        simp only [one_mul, map_one, one_smul] at hright
        change correctionLinearMap M target (⁅t, x⁆ * a) =
          MulOpposite.op (tensorPresentationMap M a) •
            correctionLinearMap M target ⁅t, x⁆ at hright
        have hleft := correctionLinearMap_relation_mul_commutator M target qx
          (commutatorElement M t a)
        change correctionLinearMap M target (x * ⁅t, a⁆) = 0 at hleft
        rw [hright, hx, smul_zero, hleft, add_zero]
  exact hspan u hu

/-- Public form of the elementary containment `Z ⊆ K(P)`. -/
theorem relationCommutatorIdeal_le_commutatorIdeal_public :
    relationCommutatorIdeal M ≤ commutatorIdeal M := by
  intro u hu
  change u ∈ TwoSidedIdeal.span
    (Set.range fun tq : PresentationTensor M × relationIdeal M ↦
      ⁅tq.1, (tq.2 : PresentationTensor M)⁆) at hu
  induction hu using TwoSidedIdeal.span_induction with
  | mem u hu =>
      obtain ⟨⟨t, q⟩, rfl⟩ := hu
      exact (commutatorElement M t q).property
  | zero => exact (commutatorIdeal M).zero_mem
  | add x y _ _ hx hy => exact (commutatorIdeal M).add_mem hx hy
  | neg x _ hx => exact (commutatorIdeal M).neg_mem hx
  | left_absorb a x _ hx => exact (commutatorIdeal M).mul_mem_left a hx
  | right_absorb a x _ hx => exact (commutatorIdeal M).mul_mem_right a hx

/-- The correction map kills all of Higgins's defining relation ideal `Z`. -/
theorem correctionLinearMap_eq_zero_of_mem_relationCommutatorIdeal [LinearOrder M]
    {u : PresentationTensor M} (hu : u ∈ relationCommutatorIdeal M) :
    correctionLinearMap M target u = 0 := by
  change u ∈ TwoSidedIdeal.span
    (Set.range fun tq : PresentationTensor M × relationIdeal M ↦
      ⁅tq.1, (tq.2 : PresentationTensor M)⁆) at hu
  induction hu using TwoSidedIdeal.span_induction with
  | mem u hu =>
      obtain ⟨⟨t, q⟩, rfl⟩ := hu
      exact correctionLinearMap_relation_commutator M target t q
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x hxmem hx =>
      let kx : commutatorIdeal M :=
        ⟨x, relationCommutatorIdeal_le_commutatorIdeal_public M hxmem⟩
      have h := correctionLinearMap_bimodule M target kx a 1
      simp only [kx, mul_one, map_one, MulOpposite.op_one, one_smul] at h
      rw [h, hx, smul_zero]
  | right_absorb a x hxmem hx =>
      let kx : commutatorIdeal M :=
        ⟨x, relationCommutatorIdeal_le_commutatorIdeal_public M hxmem⟩
      have h := correctionLinearMap_bimodule M target kx 1 a
      simp only [kx, one_mul, map_one, one_smul] at h
      rw [h, hx, smul_zero]

/-- The restricted correction kills the submodule used to define `C(M)=K(P)/Z`. -/
theorem commutatorRelations_le_ker_correctionOnCommutator [LinearOrder M] :
    commutatorRelations M ≤ LinearMap.ker (correctionOnCommutator M target) := by
  intro k hk
  rw [LinearMap.mem_ker]
  exact correctionLinearMap_eq_zero_of_mem_relationCommutatorIdeal M target hk

/-- The correction descended to Higgins's quotient `C(M)=K(P)/Z`. -/
noncomputable def correctionQuotient [LinearOrder M] :
    UniversalLieCarrier M →ₗ[ℤ] A :=
  (commutatorRelations M).liftQ (correctionOnCommutator M target)
    (commutatorRelations_le_ker_correctionOnCommutator M target)

@[simp]
theorem correctionQuotient_mk [LinearOrder M] (k : commutatorIdeal M) :
    correctionQuotient M target (Submodule.Quotient.mk k) =
      correctionLinearMap M target (k : PresentationTensor M) := by
  change correctionQuotient M target (Submodule.Quotient.mk k) =
    correctionOnCommutator M target k
  exact Submodule.liftQ_apply (commutatorRelations M)
    (correctionOnCommutator M target) k

/-- The descended correction respects the left `T(M)`-action. -/
theorem correctionQuotient_smul_left [LinearOrder M] :
    letI := universalLieCarrierModuleOverTensor M
    ∀ (a : TensorAlgebra ℤ M) (c : UniversalLieCarrier M),
      correctionQuotient M target (a • c) = a • correctionQuotient M target c := by
  letI := universalLieCarrierModuleOverTensor M
  intro a c
  obtain ⟨p, rfl⟩ := tensorPresentationMap_surjective M a
  obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective (commutatorRelations M) c
  rw [tensorPresentationMap_smul_universalLieCarrier_mk, correctionQuotient_mk,
    correctionQuotient_mk]
  have h := correctionLinearMap_bimodule M target k p 1
  simp only [mul_one, map_one, MulOpposite.op_one, one_smul] at h
  exact h

/-- The descended correction respects the right `T(M)`-action. -/
theorem correctionQuotient_smul_right [LinearOrder M] :
    letI := universalLieCarrierModuleOverTensorOpposite M
    ∀ (b : (TensorAlgebra ℤ M)ᵐᵒᵖ) (c : UniversalLieCarrier M),
      correctionQuotient M target (b • c) = b • correctionQuotient M target c := by
  letI := universalLieCarrierModuleOverTensorOpposite M
  intro b c
  induction b using MulOpposite.rec' with
  | _ b =>
      obtain ⟨p, rfl⟩ := tensorPresentationMap_surjective M b
      obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective (commutatorRelations M) c
      rw [op_tensorPresentationMap_smul_universalLieCarrier_mk, correctionQuotient_mk,
        correctionQuotient_mk]
      have h := correctionLinearMap_bimodule M target k 1 p
      simp only [one_mul, map_one, one_smul] at h
      exact h

/-- The descended correction sends the canonical bracket on `C(M)` to the bracket of the target
Lie structure. -/
theorem correctionQuotient_map_bracket [LinearOrder M] (x y : M) :
    correctionQuotient M target (universalLieBracket M x y) = target.bracket x y := by
  rw [universalLieBracket_apply, universalLieBracketValue, correctionQuotient_mk]
  change correctionLinearMap M target
      ⁅TensorAlgebra.ι ℤ (canonicalPresentationLift M x),
        TensorAlgebra.ι ℤ (canonicalPresentationLift M y)⁆ = target.bracket x y
  have h := correctionLinearMap_mul_commutator_mul M target
    (1 : PresentationTensor M) (1 : PresentationTensor M)
    (canonicalPresentationLift M x) (canonicalPresentationLift M y)
  simp only [one_mul, mul_one, map_one, MulOpposite.op_one, one_smul,
    presentationMap_canonicalPresentationLift] at h
  exact h

/-- The canonical morphism from Higgins's `C(M)` to an arbitrary Lie structure, constructed from
normal-form corrections.  This is the existence half of Higgins's universal property (for a
chosen linear order on the underlying type). -/
noncomputable def universalLieStructureLift [LinearOrder M] :
    letI := universalLieCarrierModuleOverTensor M
    letI := universalLieCarrierModuleOverTensorOpposite M
    letI := universalLieCarrierSMulCommClass M
    LieStructure.Hom M (universalLieStructure M) target := by
  letI := universalLieCarrierModuleOverTensor M
  letI := universalLieCarrierModuleOverTensorOpposite M
  letI := universalLieCarrierSMulCommClass M
  let toMap : UniversalLieCarrier M →ₗ[TensorAlgebra ℤ M] A :=
    { toFun := correctionQuotient M target
      map_add' := map_add (correctionQuotient M target)
      map_smul' := correctionQuotient_smul_left M target }
  exact
    { toLinearMap := toMap
      map_smul_right := correctionQuotient_smul_right M target
      map_bracket := correctionQuotient_map_bracket M target }

@[simp]
theorem universalLieStructureLift_mk [LinearOrder M] (k : commutatorIdeal M) :
    letI := universalLieCarrierModuleOverTensor M
    letI := universalLieCarrierModuleOverTensorOpposite M
    letI := universalLieCarrierSMulCommClass M
    universalLieStructureLift M target (Submodule.Quotient.mk k) =
      correctionLinearMap M target (k : PresentationTensor M) := by
  letI := universalLieCarrierModuleOverTensor M
  letI := universalLieCarrierModuleOverTensorOpposite M
  letI := universalLieCarrierSMulCommClass M
  exact correctionQuotient_mk M target k

end Target

end

end LieRings.PBW.Higgins
