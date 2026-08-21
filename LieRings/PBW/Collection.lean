import LieRings.UniversalEnveloping.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic.NoncommRing

/-!
# Elementary PBW collection

This file contains the two generic ingredients used when collecting PBW words:
an exact adjacent-swap identity in a universal enveloping algebra, and a deterministic
choice of an adjacent inversion in a finite list.  Neither construction is specific to
dimension subrings or to degree five.
-/

namespace LieRings.PBW

noncomputable section

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The enveloping word associated with a list of Lie factors. -/
def envelopingWord (xs : List L) : UEA R L :=
  (xs.map (UniversalEnvelopingAlgebra.ι R)).prod

@[simp]
theorem envelopingWord_nil : envelopingWord R L [] = 1 :=
  rfl

@[simp]
theorem envelopingWord_cons (x : L) (xs : List L) :
    envelopingWord R L (x :: xs) =
      UniversalEnvelopingAlgebra.ι R x * envelopingWord R L xs :=
  rfl

@[simp]
theorem envelopingWord_append (xs ys : List L) :
    envelopingWord R L (xs ++ ys) =
      envelopingWord R L xs * envelopingWord R L ys := by
  simp [envelopingWord, List.map_append]

/-- Moving one Lie factor past another creates their Lie bracket. -/
theorem iota_mul_iota_swap (x y : L) :
    UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y =
      UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x +
        UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ := by
  have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι R) x y
  change UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ =
    UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
      UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x at h
  rw [h]
  noncomm_ring

/-- Exact PBW swap inside arbitrary surrounding words. -/
theorem envelopingWord_adjacent_swap
    (left right : List L) (x y : L) :
    envelopingWord R L (left ++ x :: y :: right) =
      envelopingWord R L (left ++ y :: x :: right) +
        envelopingWord R L left *
          UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ *
            envelopingWord R L right := by
  simp only [envelopingWord_append, envelopingWord_cons]
  rw [← mul_assoc (UniversalEnvelopingAlgebra.ι R x)
    (UniversalEnvelopingAlgebra.ι R y) (envelopingWord R L right)]
  rw [iota_mul_iota_swap R L x y]
  noncomm_ring

variable {alpha : Type u}

/-- Data locating one inverted adjacent pair in a list. -/
structure AdjacentInversionData (alpha : Type u) where
  left : List alpha
  x : alpha
  y : alpha
  right : List alpha

/-- The data really locate an inverted adjacent pair in `xs`. -/
def AdjacentInversionData.Realizes [LT alpha]
    (d : AdjacentInversionData alpha) (xs : List alpha) : Prop :=
  xs = d.left ++ d.x :: d.y :: d.right ∧ d.y < d.x

/-- Choose one adjacent inversion when one exists. -/
noncomputable def chooseAdjacentInversion? [LinearOrder alpha]
    (xs : List alpha) : Option (AdjacentInversionData alpha) := by
  classical
  exact if h : ∃ d : AdjacentInversionData alpha,
      AdjacentInversionData.Realizes d xs then
    some (Classical.choose h) else none

theorem chooseAdjacentInversion?_eq_some_realizes [LinearOrder alpha]
    {xs : List alpha} {d : AdjacentInversionData alpha}
    (h : chooseAdjacentInversion? xs = some d) : d.Realizes xs := by
  unfold chooseAdjacentInversion? at h
  split at h
  · rename_i hexists
    have hd := Classical.choose_spec hexists
    have heq : Classical.choose hexists = d := Option.some.inj h
    simpa [← heq] using hd
  · contradiction

theorem chooseAdjacentInversion?_eq_none_iff [LinearOrder alpha]
    (xs : List alpha) :
    chooseAdjacentInversion? xs = none ↔
      ¬∃ d : AdjacentInversionData alpha, d.Realizes xs := by
  classical
  unfold chooseAdjacentInversion?
  split
  · rename_i hexists
    constructor
    · intro hbad
      contradiction
    · intro hnot
      exact (hnot hexists).elim
  · simp_all

/-- A list with no inverted adjacent pair is globally nondecreasing. -/
theorem pairwise_le_of_no_adjacent_inversion [LinearOrder alpha]
    (xs : List alpha)
    (h : ¬∃ d : AdjacentInversionData alpha, d.Realizes xs) :
    xs.Pairwise (· ≤ ·) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ¬∃ d : AdjacentInversionData alpha, d.Realizes xs := by
        rintro ⟨d, hd, hlt⟩
        apply h
        exact ⟨⟨x :: d.left, d.x, d.y, d.right⟩, by
          simp only [AdjacentInversionData.Realizes, List.cons_append]
          exact ⟨congrArg (x :: ·) hd, hlt⟩⟩
      have ih' := ih htail
      rw [List.pairwise_cons]
      refine ⟨?_, ih'⟩
      intro y hy
      cases xs with
      | nil => simp at hy
      | cons z zs =>
          have hxz : x ≤ z := by
            apply not_lt.mp
            intro hzx
            apply h
            exact ⟨⟨[], x, z, zs⟩, by simp [AdjacentInversionData.Realizes, hzx]⟩
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hxz
          · exact hxz.trans ((List.pairwise_cons.mp ih').1 y hy)

/-- Conversely, a nondecreasing list contains no inverted adjacent pair. -/
theorem no_adjacent_inversion_of_pairwise_le [LinearOrder alpha]
    {xs : List alpha} (h : xs.Pairwise (· ≤ ·)) :
    ¬∃ d : AdjacentInversionData alpha, d.Realizes xs := by
  rintro ⟨d, hd, hlt⟩
  rw [hd] at h
  have hxy : d.x ≤ d.y := by
    simp only [List.pairwise_append, List.pairwise_cons] at h
    exact h.2.1.1 d.y (by simp)
  exact (not_lt_of_ge hxy) hlt

theorem chooseAdjacentInversion?_eq_none_iff_pairwise [LinearOrder alpha]
    (xs : List alpha) :
    chooseAdjacentInversion? xs = none ↔ xs.Pairwise (· ≤ ·) := by
  rw [chooseAdjacentInversion?_eq_none_iff]
  exact ⟨pairwise_le_of_no_adjacent_inversion xs,
    no_adjacent_inversion_of_pairwise_le⟩

end

end LieRings.PBW
