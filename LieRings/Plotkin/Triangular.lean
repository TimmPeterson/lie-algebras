import LieRings.Plotkin.NilpotentTarget
import LieRings.UniversalEnveloping.Adjoint
import Mathlib.Algebra.Lie.SemiDirect

/-!
# Triangular realization

This file formalizes the triangular-matrix lemma in the Plotkin argument.
For a Lie ring `H` acting on an abelian group `V`, an element `(v,x)` of the
semidirect product is sent to the block matrix `[[0,0],[v,θ(x)]]`.  We use
the equivalent pair model `(v,θ(x))` for these matrices.

Rather than take an opaque generated subring, `TriangularRing H V` consists
of all pairs whose endomorphism raises the module lower-central filtration.
This makes the nilpotence calculation completely explicit.  If the `r`th
augmentation-ideal action on `V` vanishes, its unitization ideal has
`(r+1)`st power zero.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

/-- An additive group regarded as an abelian Lie ring. -/
def AbelianLie (V : Type u) := V

namespace AbelianLie

variable (V : Type u) [AddCommGroup V]

instance : AddCommGroup (AbelianLie V) := inferInstanceAs (AddCommGroup V)
instance : Module ℤ (AbelianLie V) := inferInstanceAs (Module ℤ V)
instance : LieRing (AbelianLie V) where
  bracket _ _ := 0
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp
instance : LieAlgebra ℤ (AbelianLie V) where
  lie_smul := by simp

variable (H : Type u) [LieRing H]
variable [LieRingModule H V] [LieModule ℤ H V]

instance : LieRingModule H (AbelianLie V) :=
  inferInstanceAs (LieRingModule H V)

instance : LieModule ℤ H (AbelianLie V) :=
  inferInstanceAs (LieModule ℤ H V)

end AbelianLie

variable (H : Type u) [LieRing H]
variable (V : Type u) [AddCommGroup V]
variable [LieRingModule H V] [LieModule ℤ H V]

/-- The action on `V`, viewed as derivations of its zero Lie bracket. -/
def abelianDerivationAction :
    H →ₗ⁅ℤ⁆ LieDerivation ℤ (AbelianLie V) (AbelianLie V) where
  toFun x :=
    { toLinearMap := LieModule.toEnd ℤ H V x
      leibniz' := by
        intro a b
        change ⁅x, (0 : V)⁆ = 0 - 0
        simp }
  map_add' x y := by ext v; exact add_lie x y v
  map_smul' z x := by ext v; exact smul_lie z x v
  map_lie' {x y} := by
    ext v
    change ⁅⁅x, y⁆, v⁆ = ⁅x, ⁅y, v⁆⁆ - ⁅y, ⁅x, v⁆⁆
    rw [leibniz_lie]
    abel

@[simp] theorem abelianDerivationAction_apply (x : H) (v : AbelianLie V) :
    abelianDerivationAction H V x v = ⁅x, (show V from v)⁆ := rfl

/-- The lower-central filtration of the `H`-module `V`. -/
def actionFiltration (n : ℕ) : Submodule ℤ V :=
  ((⊤ : LieSubmodule ℤ H V).lcs n : Submodule ℤ V)

@[simp] theorem actionFiltration_zero : actionFiltration H V 0 = ⊤ := by
  rw [actionFiltration, LieSubmodule.lcs_zero]
  rfl

theorem actionFiltration_succ_le (n : ℕ) :
    actionFiltration H V (n + 1) ≤ actionFiltration H V n := by
  rw [actionFiltration, actionFiltration, LieSubmodule.lcs_succ]
  exact LieSubmodule.lie_le_right _ _

theorem lie_mem_actionFiltration_succ (x : H) {n : ℕ} {v : V}
    (hv : v ∈ actionFiltration H V n) :
    ⁅x, v⁆ ∈ actionFiltration H V (n + 1) := by
  rw [actionFiltration, LieSubmodule.lcs_succ]
  exact LieSubmodule.lie_mem_lie (by trivial) hv

/-- Endomorphisms which raise the lower-central filtration by at least one. -/
def filtrationRaisingEnd : NonUnitalSubring (Module.End ℤ V) where
  carrier := {f | ∀ n v, v ∈ actionFiltration H V n →
    f v ∈ actionFiltration H V (n + 1)}
  zero_mem' := by intro n v hv; simp
  add_mem' := by
    intro f g hf hg n v hv
    exact (actionFiltration H V (n + 1)).add_mem (hf n v hv) (hg n v hv)
  neg_mem' := by
    intro f hf n v hv
    exact (actionFiltration H V (n + 1)).neg_mem (hf n v hv)
  mul_mem' := by
    intro f g hf hg n v hv
    change f (g v) ∈ actionFiltration H V (n + 1)
    exact actionFiltration_succ_le H V (n + 1)
      (hf (n + 1) (g v) (hg n v hv))

/-- The filtration-raising triangular nonunital matrix ring.  A pair `(v,f)`
represents the block matrix `[[0,0],[v,f]]`. -/
def TriangularRing := V × filtrationRaisingEnd H V

namespace TriangularRing

instance : AddCommGroup (TriangularRing H V) :=
  inferInstanceAs (AddCommGroup (V × filtrationRaisingEnd H V))

instance : Mul (TriangularRing H V) where
  mul p q := ⟨(p.2 : Module.End ℤ V) q.1, p.2 * q.2⟩

@[simp] theorem fst_mul (p q : TriangularRing H V) :
    (p * q).1 = (p.2 : Module.End ℤ V) q.1 := rfl

@[simp] theorem snd_mul (p q : TriangularRing H V) :
    (p * q).2 = p.2 * q.2 := rfl

instance : NonUnitalNonAssocRing (TriangularRing H V) :=
  NonUnitalNonAssocRing.mk
    (by
      rintro ⟨v, f⟩ ⟨w, g⟩ ⟨z, h⟩
      apply Prod.ext
      · exact (f : Module.End ℤ V).map_add w z
      · exact mul_add f g h)
    (by
      rintro ⟨v, f⟩ ⟨w, g⟩ ⟨z, h⟩
      apply Prod.ext
      · rfl
      · exact add_mul f g h)
    (by
      rintro ⟨v, f⟩
      apply Prod.ext
      · rfl
      · exact zero_mul f)
    (by
      rintro ⟨v, f⟩
      apply Prod.ext
      · exact (f : Module.End ℤ V).map_zero
      · exact mul_zero f)

instance : NonUnitalRing (TriangularRing H V) :=
  NonUnitalRing.mk (by
    rintro ⟨v, f⟩ ⟨w, g⟩ ⟨z, h⟩
    apply Prod.ext
    · rfl
    · exact mul_assoc f g h)

end TriangularRing

@[simp] theorem triangularCommutator_fst
    (p q : NonUnitalCommutator (TriangularRing H V)) :
    (⁅p, q⁆ : NonUnitalCommutator (TriangularRing H V)).1 =
      (p.2 : Module.End ℤ V) q.1 - (q.2 : Module.End ℤ V) p.1 := rfl

@[simp] theorem triangularCommutator_snd
    (p q : NonUnitalCommutator (TriangularRing H V)) :
    (⁅p, q⁆ : NonUnitalCommutator (TriangularRing H V)).2 =
      p.2 * q.2 - q.2 * p.2 := rfl

/-- The action of an element of `H` raises the module lower-central
filtration by one. -/
def actionRaisingEnd (x : H) : filtrationRaisingEnd H V :=
  ⟨LieModule.toEnd ℤ H V x, fun n v hv ↦
    lie_mem_actionFiltration_succ H V x hv⟩

@[simp] theorem actionRaisingEnd_apply (x : H) (v : V) :
    (actionRaisingEnd H V x : Module.End ℤ V) v = ⁅x, v⁆ := rfl

/-- The block-triangular map `(v,x) ↦ [[0,0],[v,θ(x)]]`. -/
def triangularLieMap :
    (AbelianLie V ⋊⁅abelianDerivationAction H V⁆ H) →ₗ⁅ℤ⁆
      NonUnitalCommutator (TriangularRing H V) where
  toFun e := ⟨(show V from e.left), actionRaisingEnd H V e.right⟩
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact map_add (LieModule.toEnd ℤ H V) x.right y.right
  map_smul' z x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact map_smul (LieModule.toEnd ℤ H V) z x.right
  map_lie' {x y} := by
    apply Prod.ext
    · simp only [LieAlgebra.SemiDirectSum.lie_eq_mk]
      change (0 : V) + ⁅x.right, (show V from y.left)⁆ -
        ⁅y.right, (show V from x.left)⁆ = _
      simp
    · apply Subtype.ext
      ext v
      change ⁅⁅x.right, y.right⁆, v⁆ =
        ⁅x.right, ⁅y.right, v⁆⁆ - ⁅y.right, ⁅x.right, v⁆⁆
      rw [leibniz_lie]
      abel

@[simp] theorem triangularLieMap_inl (v : AbelianLie V) :
    triangularLieMap H V
        (LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H V) v) =
      ((show V from v), 0) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact map_zero (LieModule.toEnd ℤ H V)

theorem triangularLieMap_injective_on_inl :
    Function.Injective (fun v : AbelianLie V ↦
      triangularLieMap H V
        (LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H V) v)) := by
  intro v w h
  simpa only [triangularLieMap_inl] using congrArg Prod.fst h

/-- A triangular matrix has degree `k` if its lower-left entry lies in the
`k`th filtration term and its endomorphism raises filtration by `k+1`. -/
def HasTriangularDegree (k : ℕ) (p : TriangularRing H V) : Prop :=
  p.1 ∈ actionFiltration H V k ∧
    ∀ n v, v ∈ actionFiltration H V n →
      (p.2 : Module.End ℤ V) v ∈ actionFiltration H V (n + k + 1)

theorem hasTriangularDegree_zero (p : TriangularRing H V) :
    HasTriangularDegree H V 0 p := by
  refine ⟨?_, ?_⟩
  · rw [actionFiltration_zero]
    trivial
  · intro n v hv
    simpa only [Nat.add_zero] using p.2.property n v hv

theorem HasTriangularDegree.add {k : ℕ} {p q : TriangularRing H V}
    (hp : HasTriangularDegree H V k p)
    (hq : HasTriangularDegree H V k q) :
    HasTriangularDegree H V k (p + q) := by
  refine ⟨(actionFiltration H V k).add_mem hp.1 hq.1, ?_⟩
  intro n v hv
  exact (actionFiltration H V (n + k + 1)).add_mem
    (hp.2 n v hv) (hq.2 n v hv)

theorem HasTriangularDegree.left_mul {k : ℕ} {p q : TriangularRing H V}
    (_hp : HasTriangularDegree H V 0 p)
    (hq : HasTriangularDegree H V k q) :
    HasTriangularDegree H V (k + 1) (p * q) := by
  refine ⟨?_, ?_⟩
  · exact p.2.property k q.1 hq.1
  · intro n v hv
    change (p.2 : Module.End ℤ V) ((q.2 : Module.End ℤ V) v) ∈
      actionFiltration H V (n + (k + 1) + 1)
    have hqv := hq.2 n v hv
    have hpv := p.2.property (n + k + 1)
      ((q.2 : Module.End ℤ V) v) hqv
    convert hpv using 1

private theorem unitization_pow_hasTriangularDegree
    (k : ℕ) {x : Unitization ℤ (TriangularRing H V)}
    (hx : x ∈ unitizationIdeal (R := TriangularRing H V) ^ (k + 1)) :
    x.fst = 0 ∧ HasTriangularDegree H V k x.snd := by
  induction k generalizing x with
  | zero =>
      have hxJ : x ∈ unitizationIdeal (R := TriangularRing H V) := by
        simpa only [zero_add, Submodule.pow_one] using hx
      exact ⟨(mem_unitizationIdeal_iff x).mp hxJ,
        hasTriangularDegree_zero H V x.snd⟩
  | succ k ih =>
      have hxmul : x ∈ unitizationIdeal (R := TriangularRing H V) *
          unitizationIdeal (R := TriangularRing H V) ^ (k + 1) := by
        simpa only [Nat.succ_eq_add_one, Ideal.IsTwoSided.pow_succ] using hx
      refine Submodule.mul_induction_on hxmul ?_ ?_
      · intro a ha b hb
        have ha0 : a.fst = 0 := (mem_unitizationIdeal_iff a).mp ha
        have hadeg : HasTriangularDegree H V 0 a.snd :=
          hasTriangularDegree_zero H V a.snd
        obtain ⟨hb0, hbdeg⟩ := ih hb
        refine ⟨?_, ?_⟩
        · simpa [Unitization.fst_mul, ha0, hb0]
        · have hsnd : (a * b).snd = a.snd * b.snd := by
            rw [Unitization.snd_mul, ha0, hb0]
            simp
          rw [hsnd]
          exact HasTriangularDegree.left_mul H V hadeg hbdeg
      · intro a b ha hb
        refine ⟨?_, ?_⟩
        · simpa [ha.1, hb.1]
        · exact HasTriangularDegree.add H V ha.2 hb.2

/-- The triangular ring is nilpotent at exponent `r+1` once the `r`th
action-filtration term vanishes. -/
theorem triangular_unitizationIdeal_pow_eq_bot (r : ℕ)
    (hr : actionFiltration H V r = ⊥) :
    unitizationIdeal (R := TriangularRing H V) ^ (r + 1) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  obtain ⟨hfst, hdeg⟩ := unitization_pow_hasTriangularDegree H V r hx
  apply Unitization.ext
  · exact hfst
  · apply Prod.ext
    · have hv := hdeg.1
      rw [hr] at hv
      exact hv
    · apply Subtype.ext
      ext v
      have hv0 : v ∈ actionFiltration H V 0 := by
        rw [actionFiltration_zero]
        trivial
      have hv := hdeg.2 0 v hv0
      have hv' : (x.snd.2 : Module.End ℤ V) v ∈ actionFiltration H V r := by
        apply actionFiltration_succ_le H V r
        simpa only [Nat.zero_add] using hv
      rw [hr] at hv'
      exact hv'

theorem actionFiltration_eq_actionSubmodule (n : ℕ) :
    actionFiltration H V n =
      UEA.actionSubmodule ℤ H V (UEA.augmentationIdeal ℤ H ^ n)
        (⊤ : LieSubmodule ℤ H V) := by
  exact (UEA.actionSubmodule_augmentationIdeal_pow_eq_lcs ℤ H V
    (⊤ : LieSubmodule ℤ H V) n).symm

/-- **Triangular realization.**  If the `r`th augmentation-ideal action on
`V` is zero, the semidirect product maps into a nilpotent associative ideal,
and the map is injective on the abelian factor. -/
theorem exists_triangular_nilpotentIdealRepresentation (r : ℕ)
    (hr : UEA.actionSubmodule ℤ H V (UEA.augmentationIdeal ℤ H ^ r)
        (⊤ : LieSubmodule ℤ H V) = ⊥) :
    ∃ P : NilpotentIdealRepresentation
        (AbelianLie V ⋊⁅abelianDerivationAction H V⁆ H),
      Function.Injective (fun v : AbelianLie V ↦
        P.map (LieAlgebra.SemiDirectSum.inl (abelianDerivationAction H V) v)) := by
  have hfiltration : actionFiltration H V r = ⊥ := by
    rw [actionFiltration_eq_actionSubmodule]
    exact hr
  have hpow := triangular_unitizationIdeal_pow_eq_bot H V r hfiltration
  let P : NilpotentIdealRepresentation
      (AbelianLie V ⋊⁅abelianDerivationAction H V⁆ H) :=
    NilpotentIdealRepresentation.ofNonUnital
      (triangularLieMap H V) (r + 1) hpow
  refine ⟨P, ?_⟩
  intro v w hvw
  apply triangularLieMap_injective_on_inl H V
  apply (Unitization.inr_injective (R := ℤ) (A := TriangularRing H V))
  exact hvw

end

end LieRings.Plotkin
