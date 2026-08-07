import LieRings.PBW.HigginsFiltration
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# Integral PBW and the canonical embedding

This file completes Higgins's filtered argument.  The top tensor-degree component gives a
comparison from the associated graded of the enveloping relation ideal to the commutator ideal.
Universality makes that comparison injective; descending the filtration then proves that the
degree-one copy of a Lie ring does not meet the defining ideal.
-/

namespace LieRings.PBW.Higgins

universe u

noncomputable section

open scoped DirectSum TensorProduct

variable (L : Type u) [LieRing L]

local notation "T" => TensorAlgebra ℤ L

/-- Projection to tensor degree `n`, included back into the tensor algebra. -/
def tensorHomogeneousComponent (n : ℕ) : T →ₗ[ℤ] T :=
  TensorPower.toTensorAlgebra.comp
    ((DirectSum.component ℤ ℕ (fun k => TensorPower ℤ k L) n).comp
      (TensorAlgebra.toDirectSum (R := ℤ) (M := L)).toLinearMap)

theorem tensorWord_eq_tprod (xs : List L) :
    tensorWord L xs =
      TensorAlgebra.tprod ℤ L xs.length (fun i => xs.get i) := by
  simp [tensorWord, TensorAlgebra.tprod_apply]

@[simp]
theorem tensorHomogeneousComponent_tensorWord_same (xs : List L) :
    tensorHomogeneousComponent L xs.length (tensorWord L xs) = tensorWord L xs := by
  rw [tensorWord_eq_tprod]
  change TensorPower.toTensorAlgebra
      (DirectSum.component ℤ ℕ (fun k => TensorPower ℤ k L) xs.length
        (TensorAlgebra.toDirectSum
          (TensorAlgebra.tprod ℤ L xs.length (fun i => xs.get i)))) = _
  rw [TensorAlgebra.toDirectSum_tensorPower_tprod]
  rw [← DirectSum.lof_eq_of (R := ℤ), DirectSum.component.lof_self,
    TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]

theorem tensorHomogeneousComponent_tensorWord_of_ne (n : ℕ) (xs : List L)
    (h : xs.length ≠ n) :
    tensorHomogeneousComponent L n (tensorWord L xs) = 0 := by
  rw [tensorWord_eq_tprod]
  change TensorPower.toTensorAlgebra
      (DirectSum.component ℤ ℕ (fun k => TensorPower ℤ k L) n
        (TensorAlgebra.toDirectSum
          (TensorAlgebra.tprod ℤ L xs.length (fun i => xs.get i)))) = 0
  rw [TensorAlgebra.toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of (R := ℤ),
    DirectSum.component.of]
  simp [h]

theorem tensorHomogeneousComponent_eq_zero_of_mem_filtration
    {m n : ℕ} {t : T} (ht : t ∈ tensorDegreeFiltration L m) (hmn : m < n) :
    tensorHomogeneousComponent L n t = 0 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨xs, hxs, rfl⟩ := ht
      exact tensorHomogeneousComponent_tensorWord_of_ne L n xs (by omega)
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

theorem tensorHomogeneousComponent_ι_mul {n : ℕ} (z : L) {t : T}
    (ht : t ∈ tensorDegreeFiltration L n) :
    tensorHomogeneousComponent L (n + 1) (TensorAlgebra.ι ℤ z * t) =
      TensorAlgebra.ι ℤ z * tensorHomogeneousComponent L n t := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨xs, hxs, rfl⟩ := ht
      have hword : TensorAlgebra.ι ℤ z * tensorWord L xs = tensorWord L (z :: xs) := by
        simp [tensorWord]
      rw [hword]
      by_cases hlen : xs.length = n
      · subst n
        calc
          tensorHomogeneousComponent L (xs.length + 1) (tensorWord L (z :: xs)) =
              tensorWord L (z :: xs) := by
                simpa using tensorHomogeneousComponent_tensorWord_same L (z :: xs)
          _ = TensorAlgebra.ι ℤ z * tensorWord L xs := hword.symm
          _ = TensorAlgebra.ι ℤ z *
              tensorHomogeneousComponent L xs.length (tensorWord L xs) := by
                rw [tensorHomogeneousComponent_tensorWord_same]
      · have hlt : xs.length < n := by omega
        rw [tensorHomogeneousComponent_tensorWord_of_ne L n xs hlen,
          mul_zero, tensorHomogeneousComponent_tensorWord_of_ne]
        simp
        omega
  | zero => simp
  | add x y _ _ hx hy => simp only [mul_add, map_add, hx, hy]
  | smul c x _ hx =>
      rw [mul_smul_comm, map_smul, hx, map_smul]
      rw [mul_smul_comm]

theorem tensorHomogeneousComponent_mul_ι {n : ℕ} (z : L) {t : T}
    (ht : t ∈ tensorDegreeFiltration L n) :
    tensorHomogeneousComponent L (n + 1) (t * TensorAlgebra.ι ℤ z) =
      tensorHomogeneousComponent L n t * TensorAlgebra.ι ℤ z := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨xs, hxs, rfl⟩ := ht
      have hword : tensorWord L xs * TensorAlgebra.ι ℤ z = tensorWord L (xs ++ [z]) := by
        simp [tensorWord_append]
      rw [hword]
      by_cases hlen : xs.length = n
      · subst n
        calc
          tensorHomogeneousComponent L (xs.length + 1) (tensorWord L (xs ++ [z])) =
              tensorWord L (xs ++ [z]) := by
                simpa using tensorHomogeneousComponent_tensorWord_same L (xs ++ [z])
          _ = tensorWord L xs * TensorAlgebra.ι ℤ z := hword.symm
          _ = tensorHomogeneousComponent L xs.length (tensorWord L xs) *
              TensorAlgebra.ι ℤ z := by
                rw [tensorHomogeneousComponent_tensorWord_same]
      · have hlt : xs.length < n := by omega
        rw [tensorHomogeneousComponent_tensorWord_of_ne L n xs hlen,
          zero_mul, tensorHomogeneousComponent_tensorWord_of_ne]
        simp
        omega
  | zero => simp
  | add x y _ _ hx hy => simp only [add_mul, map_add, hx, hy]
  | smul c x _ hx =>
      rw [smul_mul_assoc, map_smul, hx, map_smul]
      rw [smul_mul_assoc]

theorem tensorHomogeneousComponent_word_relation_word_mem_commutator
    (n : ℕ) (as bs : List L) (x y : L)
    (hlen : as.length + bs.length + 2 ≤ n) :
    tensorHomogeneousComponent L n
        (tensorWord L as * envelopingRelation L x y * tensorWord L bs) ∈
      tensorCommutatorIdeal L := by
  have hexpand :
      tensorWord L as * envelopingRelation L x y * tensorWord L bs =
        tensorWord L (as ++ [x, y] ++ bs) -
          tensorWord L (as ++ [y, x] ++ bs) -
            tensorWord L (as ++ [⁅x, y⁆] ++ bs) := by
    unfold envelopingRelation
    simp [tensorWord]
    noncomm_ring
  rw [hexpand, map_sub, map_sub]
  have hlower : (as ++ [⁅x, y⁆] ++ bs).length ≠ n := by
    simp
    omega
  rw [tensorHomogeneousComponent_tensorWord_of_ne L n _ hlower, sub_zero]
  by_cases htop : as.length + bs.length + 2 = n
  · have h₁ : (as ++ [x, y] ++ bs).length = n := by simp; omega
    have h₂ : (as ++ [y, x] ++ bs).length = n := by simp; omega
    have hc := (tensorCommutatorBracketValue L x y).property
    have hmem := (tensorCommutatorIdeal L).mul_mem_right (tensorWord L bs)
      ((tensorCommutatorIdeal L).mul_mem_left (tensorWord L as) hc)
    have hc₁ : tensorHomogeneousComponent L n (tensorWord L (as ++ [x, y] ++ bs)) =
        tensorWord L (as ++ [x, y] ++ bs) := by
      rw [← h₁]
      exact tensorHomogeneousComponent_tensorWord_same L (as ++ [x, y] ++ bs)
    have hc₂ : tensorHomogeneousComponent L n (tensorWord L (as ++ [y, x] ++ bs)) =
        tensorWord L (as ++ [y, x] ++ bs) := by
      rw [← h₂]
      exact tensorHomogeneousComponent_tensorWord_same L (as ++ [y, x] ++ bs)
    rw [hc₁, hc₂]
    convert hmem using 1
    simp [tensorCommutatorBracketValue, tensorWord,
      LieRing.of_associative_ring_bracket]
    noncomm_ring
  · have h₁ : (as ++ [x, y] ++ bs).length ≠ n := by simp; omega
    have h₂ : (as ++ [y, x] ++ bs).length ≠ n := by simp; omega
    rw [tensorHomogeneousComponent_tensorWord_of_ne L n _ h₁,
      tensorHomogeneousComponent_tensorWord_of_ne L n _ h₂, sub_zero]
    exact (tensorCommutatorIdeal L).zero_mem

theorem tensorHomogeneousComponent_mul_relation_mul_mem_commutator
    {n p q : ℕ} {a b : T} (x y : L)
    (hpq : p + q + 2 ≤ n)
    (ha : a ∈ tensorDegreeFiltration L p)
    (hb : b ∈ tensorDegreeFiltration L q) :
    tensorHomogeneousComponent L n (a * envelopingRelation L x y * b) ∈
      tensorCommutatorIdeal L := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨as, has, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨bs, hbs, rfl⟩ := hb
          exact tensorHomogeneousComponent_word_relation_word_mem_commutator
            L n as bs x y (by omega)
      | zero => simp
      | add b c _ _ hb hc =>
          simpa only [mul_add, map_add] using (tensorCommutatorIdeal L).add_mem hb hc
      | smul c b _ hb =>
          rw [mul_smul_comm, map_smul]
          exact (tensorCommutatorIdeal L).smul_mem c hb
  | zero => simp
  | add a c _ _ ha hc =>
      simpa only [add_mul, map_add] using (tensorCommutatorIdeal L).add_mem ha hc
  | smul c a _ ha =>
      rw [smul_mul_assoc, smul_mul_assoc, map_smul]
      exact (tensorCommutatorIdeal L).smul_mem c ha

theorem tensorHomogeneousComponent_mem_commutator_of_mem_higginsFiltration
    {n : ℕ} {t : T} (ht : t ∈ higginsFiltration L n) :
    tensorHomogeneousComponent L n t ∈ tensorCommutatorIdeal L := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨p, q, x, y, a, b, hpq, ha, hb, rfl⟩ := ht
      exact tensorHomogeneousComponent_mul_relation_mul_mem_commutator
        L x y hpq ha hb
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (tensorCommutatorIdeal L).add_mem hx hy
  | smul c x _ hx =>
      rw [map_smul]
      exact (tensorCommutatorIdeal L).smul_mem c hx

/-! ## The leading-component comparison -/

/-- The degree-`n` leading component on `J(n)`, valued in the commutator ideal. -/
def higginsLeadingFiltrationMap (n : ℕ) :
    higginsFiltration L n →ₗ[ℤ] tensorCommutatorIdeal L where
  toFun t := ⟨tensorHomogeneousComponent L n (t : T),
    tensorHomogeneousComponent_mem_commutator_of_mem_higginsFiltration L t.property⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simpa using map_smul (tensorHomogeneousComponent L n) c (x : T)

theorem previousHigginsFiltration_le_ker_leading (n : ℕ) :
    previousHigginsFiltration L n ≤ LinearMap.ker (higginsLeadingFiltrationMap L n) := by
  intro t ht
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change tensorHomogeneousComponent L n (t : T) = 0
  cases n with
  | zero =>
      have ht0 : (t : T) = 0 := by
        have h := t.property
        simpa using h
      rw [ht0, map_zero]
  | succ n =>
      apply tensorHomogeneousComponent_eq_zero_of_mem_filtration L
        (higginsFiltration_le_tensorDegreeFiltration L n ht)
      omega

/-- The leading component descends to `J(n)/J(n-1)`. -/
def higginsLeadingGradedPiece (n : ℕ) :
    HigginsGradedPiece L n →ₗ[ℤ] tensorCommutatorIdeal L :=
  (previousHigginsFiltration L n).liftQ (higginsLeadingFiltrationMap L n)
    (previousHigginsFiltration_le_ker_leading L n)

@[simp]
theorem higginsLeadingGradedPiece_mk (n : ℕ) (t : higginsFiltration L n) :
    higginsLeadingGradedPiece L n (Submodule.Quotient.mk t) =
      higginsLeadingFiltrationMap L n t :=
  rfl

/-- Sum the leading components of all associated-graded pieces. -/
def higginsLeadingComparison :
    HigginsAssociatedGraded L →ₗ[ℤ] tensorCommutatorIdeal L :=
  DirectSum.toModule ℤ ℕ (tensorCommutatorIdeal L) (higginsLeadingGradedPiece L)

@[simp]
theorem higginsLeadingComparison_lof (n : ℕ) (q : HigginsGradedPiece L n) :
    higginsLeadingComparison L
        (DirectSum.lof ℤ ℕ (HigginsGradedPiece L) n q) =
      higginsLeadingGradedPiece L n q :=
  DirectSum.toModule_lof ℤ n q

theorem higginsLeadingFiltrationMap_leftGenerator (n : ℕ) (z : L)
    (t : higginsFiltration L n) :
    higginsLeadingFiltrationMap L (n + 1) (leftGeneratorFiltrationMap L n z t) =
      TensorAlgebra.ι ℤ z • higginsLeadingFiltrationMap L n t := by
  apply Subtype.ext
  exact tensorHomogeneousComponent_ι_mul L z
    (higginsFiltration_le_tensorDegreeFiltration L n t.property)

theorem higginsLeadingFiltrationMap_rightGenerator (n : ℕ) (z : L)
    (t : higginsFiltration L n) :
    higginsLeadingFiltrationMap L (n + 1) (rightGeneratorFiltrationMap L n z t) =
      MulOpposite.op (TensorAlgebra.ι ℤ z) • higginsLeadingFiltrationMap L n t := by
  apply Subtype.ext
  exact tensorHomogeneousComponent_mul_ι L z
    (higginsFiltration_le_tensorDegreeFiltration L n t.property)

theorem higginsLeadingComparison_smul_left_generator (z : L)
    (a : HigginsAssociatedGraded L) :
    letI := higginsAssociatedModule L
    higginsLeadingComparison L (TensorAlgebra.ι ℤ z • a) =
      TensorAlgebra.ι ℤ z • higginsLeadingComparison L a := by
  letI := higginsAssociatedModule L
  change higginsLeadingComparison L (leftTensorAction L (TensorAlgebra.ι ℤ z) a) = _
  rw [leftTensorAction_ι]
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb
  | of n q =>
      induction q using Submodule.Quotient.induction_on with
      | _ t =>
          rw [← DirectSum.lof_eq_of (R := ℤ)]
          rw [leftGeneratorAssociatedEnd_lof, leftGeneratorGradedPiece_mk,
            higginsLeadingComparison_lof, higginsLeadingGradedPiece_mk,
            higginsLeadingComparison_lof, higginsLeadingGradedPiece_mk]
          exact higginsLeadingFiltrationMap_leftGenerator L n z t

theorem higginsLeadingComparison_smul_right_generator (z : L)
    (a : HigginsAssociatedGraded L) :
    letI := higginsAssociatedModuleOpposite L
    higginsLeadingComparison L (MulOpposite.op (TensorAlgebra.ι ℤ z) • a) =
      MulOpposite.op (TensorAlgebra.ι ℤ z) • higginsLeadingComparison L a := by
  letI := higginsAssociatedModuleOpposite L
  change higginsLeadingComparison L
    (rightTensorAction L (MulOpposite.op (TensorAlgebra.ι ℤ z)) a) = _
  rw [rightTensorAction_op_ι]
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb
  | of n q =>
      induction q using Submodule.Quotient.induction_on with
      | _ t =>
          rw [← DirectSum.lof_eq_of (R := ℤ)]
          rw [rightGeneratorAssociatedEnd_lof, rightGeneratorGradedPiece_mk,
            higginsLeadingComparison_lof, higginsLeadingGradedPiece_mk,
            higginsLeadingComparison_lof, higginsLeadingGradedPiece_mk]
          exact higginsLeadingFiltrationMap_rightGenerator L n z t

theorem higginsLeadingComparison_smul_left (s : T)
    (a : HigginsAssociatedGraded L) :
    letI := higginsAssociatedModule L
    higginsLeadingComparison L (s • a) = s • higginsLeadingComparison L a := by
  letI := higginsAssociatedModule L
  induction s using TensorAlgebra.induction generalizing a with
  | algebraMap c =>
      have hsource : (algebraMap ℤ T c) • a = c • a := by
        change leftTensorAction L (algebraMap ℤ T c) a = c • a
        simp [leftTensorAction]
      have htarget : (algebraMap ℤ T c) • higginsLeadingComparison L a =
          c • higginsLeadingComparison L a := by
        apply Subtype.ext
        simp
      rw [hsource, htarget]
      exact map_smul (higginsLeadingComparison L) c a
  | ι z => exact higginsLeadingComparison_smul_left_generator L z a
  | mul s t hs ht => rw [mul_smul, hs, ht, mul_smul]
  | add s t hs ht => rw [add_smul, map_add, hs, ht, add_smul]

theorem higginsLeadingComparison_smul_right (s : Tᵐᵒᵖ)
    (a : HigginsAssociatedGraded L) :
    letI := higginsAssociatedModuleOpposite L
    higginsLeadingComparison L (s • a) = s • higginsLeadingComparison L a := by
  letI := higginsAssociatedModuleOpposite L
  induction s using MulOpposite.rec' with
  | _ s =>
      induction s using TensorAlgebra.induction generalizing a with
      | algebraMap c =>
          have hsource : MulOpposite.op (algebraMap ℤ T c) • a = c • a := by
            change rightTensorAction L (MulOpposite.op (algebraMap ℤ T c)) a = c • a
            simp [rightTensorAction, rightTensorActionOp]
          have htarget : MulOpposite.op (algebraMap ℤ T c) •
                higginsLeadingComparison L a = c • higginsLeadingComparison L a := by
            apply Subtype.ext
            change (higginsLeadingComparison L a : T) * algebraMap ℤ T c =
              algebraMap ℤ T c * (higginsLeadingComparison L a : T)
            exact (Algebra.commutes c (higginsLeadingComparison L a : T)).symm
          rw [hsource, htarget]
          exact map_smul (higginsLeadingComparison L) c a
      | ι z => exact higginsLeadingComparison_smul_right_generator L z a
      | mul s t hs ht =>
          rw [MulOpposite.op_mul, mul_smul, ht, hs, mul_smul]
      | add s t hs ht =>
          rw [MulOpposite.op_add, add_smul, map_add, hs, ht, add_smul]

theorem higginsLeadingComparison_bracket (x y : L) :
    higginsLeadingComparison L (higginsRelationClass L x y) =
      tensorCommutatorBracket L x y := by
  rw [higginsRelationClass_apply]
  simp only [higginsRelationClassValue, higginsLeadingComparison_lof,
    higginsLeadingGradedPiece_mk]
  apply Subtype.ext
  change tensorHomogeneousComponent L 2 (envelopingRelation L x y) =
    ⁅TensorAlgebra.ι ℤ x, TensorAlgebra.ι ℤ y⁆
  have hxy : TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y = tensorWord L [x, y] := by
    simp [tensorWord]
  have hyx : TensorAlgebra.ι ℤ y * TensorAlgebra.ι ℤ x = tensorWord L [y, x] := by
    simp [tensorWord]
  have hlie : TensorAlgebra.ι ℤ ⁅x, y⁆ = tensorWord L [⁅x, y⁆] := by
    simp [tensorWord]
  unfold envelopingRelation
  rw [map_sub, map_sub, hxy, hyx, hlie]
  have hcxy : tensorHomogeneousComponent L 2 (tensorWord L [x, y]) =
      tensorWord L [x, y] := by
    simpa using tensorHomogeneousComponent_tensorWord_same L [x, y]
  have hcyx : tensorHomogeneousComponent L 2 (tensorWord L [y, x]) =
      tensorWord L [y, x] := by
    simpa using tensorHomogeneousComponent_tensorWord_same L [y, x]
  rw [hcxy, hcyx, tensorHomogeneousComponent_tensorWord_of_ne]
  · simp [tensorWord, LieRing.of_associative_ring_bracket]
  · simp

/-- The leading-component comparison as a morphism of Higgins Lie structures. -/
noncomputable def higginsLeadingLieStructureHom :
    letI := higginsAssociatedModule L
    letI := higginsAssociatedModuleOpposite L
    letI := higginsAssociatedSMulCommClass L
    letI := tensorCommutatorIdealSMulCommClass L
    LieStructure.Hom L (higginsFiltrationLieStructure L)
      (tensorCommutatorLieStructure L) := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  letI := tensorCommutatorIdealSMulCommClass L
  exact
    { toLinearMap :=
        { toFun := higginsLeadingComparison L
          map_add' := map_add (higginsLeadingComparison L)
          map_smul' := higginsLeadingComparison_smul_left L }
      map_smul_right := higginsLeadingComparison_smul_right L
      map_bracket := higginsLeadingComparison_bracket L }

namespace LieStructure.Hom

/-- Composition of Higgins Lie-structure morphisms. -/
def comp {A B C : Type*}
    [AddCommGroup A] [Module ℤ A]
    [Module (TensorAlgebra ℤ L) A] [Module (TensorAlgebra ℤ L)ᵐᵒᵖ A]
    [SMulCommClass (TensorAlgebra ℤ L) (TensorAlgebra ℤ L)ᵐᵒᵖ A]
    [AddCommGroup B] [Module ℤ B]
    [Module (TensorAlgebra ℤ L) B] [Module (TensorAlgebra ℤ L)ᵐᵒᵖ B]
    [SMulCommClass (TensorAlgebra ℤ L) (TensorAlgebra ℤ L)ᵐᵒᵖ B]
    [AddCommGroup C] [Module ℤ C]
    [Module (TensorAlgebra ℤ L) C] [Module (TensorAlgebra ℤ L)ᵐᵒᵖ C]
    [SMulCommClass (TensorAlgebra ℤ L) (TensorAlgebra ℤ L)ᵐᵒᵖ C]
    {source : LieStructure L A} {middle : LieStructure L B} {target : LieStructure L C}
    (g : LieStructure.Hom L middle target) (f : LieStructure.Hom L source middle) :
    LieStructure.Hom L source target where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_smul_right a x := by
    change g.toLinearMap (f.toLinearMap (a • x)) = a • g.toLinearMap (f.toLinearMap x)
    rw [f.map_smul_right, g.map_smul_right]
  map_bracket x y := by
    change g.toLinearMap (f.toLinearMap (source.bracket x y)) = target.bracket x y
    rw [f.map_bracket, g.map_bracket]

/-- Identity Higgins Lie-structure morphism. -/
def id {A : Type*}
    [AddCommGroup A] [Module ℤ A]
    [Module (TensorAlgebra ℤ L) A] [Module (TensorAlgebra ℤ L)ᵐᵒᵖ A]
    [SMulCommClass (TensorAlgebra ℤ L) (TensorAlgebra ℤ L)ᵐᵒᵖ A]
    (source : LieStructure L A) : LieStructure.Hom L source source where
  toLinearMap := LinearMap.id
  map_smul_right _ _ := rfl
  map_bracket _ _ := rfl

end LieStructure.Hom

/-- A universal morphism from the tensor commutator structure to the filtered structure. -/
noncomputable def higginsUniversalToFiltrationHom :
    letI := higginsAssociatedModule L
    letI := higginsAssociatedModuleOpposite L
    letI := higginsAssociatedSMulCommClass L
    letI := tensorCommutatorIdealSMulCommClass L
    LieStructure.Hom L (tensorCommutatorLieStructure L)
      (higginsFiltrationLieStructure L) := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  letI := tensorCommutatorIdealSMulCommClass L
  exact Classical.choose
    (tensorCommutatorLieStructure_isUniversal L
      (HigginsAssociatedGraded L) (higginsFiltrationLieStructure L))

theorem higginsLeading_after_universal (k : tensorCommutatorIdeal L) :
    letI := higginsAssociatedModule L
    letI := higginsAssociatedModuleOpposite L
    letI := higginsAssociatedSMulCommClass L
    letI := tensorCommutatorIdealSMulCommClass L
    higginsLeadingComparison L (higginsUniversalToFiltrationHom L k) = k := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  letI := tensorCommutatorIdealSMulCommClass L
  obtain ⟨base, hbase⟩ := tensorCommutatorLieStructure_isUniversal L
    (tensorCommutatorIdeal L) (tensorCommutatorLieStructure L)
  have hcomp := hbase
    (LieStructure.Hom.comp L (higginsLeadingLieStructureHom L)
      (higginsUniversalToFiltrationHom L))
  have hid := hbase (LieStructure.Hom.id L (tensorCommutatorLieStructure L))
  have heq : LieStructure.Hom.comp L (higginsLeadingLieStructureHom L)
        (higginsUniversalToFiltrationHom L) =
      LieStructure.Hom.id L (tensorCommutatorLieStructure L) := hcomp.trans hid.symm
  exact congrArg (fun f ↦ f k) heq

/-! ## Generation of the filtered structure -/

def higginsWordRelationWordElement (n : ℕ) (as bs : List L) (x y : L)
    (hdegree : as.length + bs.length + 2 ≤ n) : higginsFiltration L n :=
  ⟨tensorWord L as * envelopingRelation L x y * tensorWord L bs, by
    apply Submodule.subset_span
    exact ⟨as.length, bs.length, x, y, tensorWord L as, tensorWord L bs,
      hdegree, tensorWord_mem_tensorDegreeFiltration L le_rfl,
      tensorWord_mem_tensorDegreeFiltration L le_rfl, rfl⟩⟩

theorem tensorWords_smul_relationClass (as bs : List L) (x y : L) :
    letI := higginsAssociatedModule L
    letI := higginsAssociatedModuleOpposite L
    letI := higginsAssociatedSMulCommClass L
    tensorWord L as •
        (MulOpposite.op (tensorWord L bs) • higginsRelationClass L x y) =
      DirectSum.lof ℤ ℕ (HigginsGradedPiece L) (as.length + bs.length + 2)
        (Submodule.Quotient.mk
          (higginsWordRelationWordElement L (as.length + bs.length + 2)
            as bs x y (by omega))) := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  change tensorWord L as •
      (MulOpposite.op (tensorWord L bs) •
        DirectSum.lof ℤ ℕ (HigginsGradedPiece L) 2
          (Submodule.Quotient.mk (envelopingRelationFiltrationElement L x y))) = _
  rw [right_tensorWord_smul_lof_mk, left_tensorWord_smul_lof_mk]
  apply lof_quotient_mk_eq_of_coe_eq L
  · omega
  · simp [leftTensorWordFiltrationElement, rightTensorWordFiltrationElement,
      higginsWordRelationWordElement, envelopingRelationFiltrationElement, mul_assoc]

theorem higginsWordRelationWordClass_mem_universal_range
    (n : ℕ) (as bs : List L) (x y : L)
    (hdegree : as.length + bs.length + 2 ≤ n) :
    letI := higginsAssociatedModule L
    letI := higginsAssociatedModuleOpposite L
    letI := higginsAssociatedSMulCommClass L
    letI := tensorCommutatorIdealSMulCommClass L
    DirectSum.lof ℤ ℕ (HigginsGradedPiece L) n
        (Submodule.Quotient.mk
          (higginsWordRelationWordElement L n as bs x y hdegree)) ∈
      LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  letI := tensorCommutatorIdealSMulCommClass L
  by_cases htop : as.length + bs.length + 2 = n
  · subst n
    let k : tensorCommutatorIdeal L :=
      tensorWord L as •
        (MulOpposite.op (tensorWord L bs) • tensorCommutatorBracket L x y)
    refine ⟨k, ?_⟩
    change higginsUniversalToFiltrationHom L k = _
    have hb := (higginsUniversalToFiltrationHom L).map_bracket x y
    change higginsUniversalToFiltrationHom L (tensorCommutatorBracket L x y) =
      higginsRelationClass L x y at hb
    rw [map_smul, (higginsUniversalToFiltrationHom L).map_smul_right, hb]
    exact tensorWords_smul_relationClass L as bs x y
  · have hlt : as.length + bs.length + 2 ≤ n - 1 := by omega
    have hprev : higginsWordRelationWordElement L n as bs x y hdegree ∈
        previousHigginsFiltration L n := by
      change tensorWord L as * envelopingRelation L x y * tensorWord L bs ∈
        higginsFiltration L (n - 1)
      exact (higginsWordRelationWordElement L (n - 1) as bs x y hlt).property
    have hq : Submodule.Quotient.mk
        (higginsWordRelationWordElement L n as bs x y hdegree) = 0 :=
      (Submodule.Quotient.mk_eq_zero (previousHigginsFiltration L n)).mpr hprev
    rw [hq, map_zero]
    exact (LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap).zero_mem

def higginsGeneratorElement (n p q : ℕ) (x y : L) (a b : T)
    (hpq : p + q + 2 ≤ n)
    (ha : a ∈ tensorDegreeFiltration L p)
    (hb : b ∈ tensorDegreeFiltration L q) : higginsFiltration L n :=
  ⟨a * envelopingRelation L x y * b,
    Submodule.subset_span ⟨p, q, x, y, a, b, hpq, ha, hb, rfl⟩⟩

theorem higginsGeneratorClass_mem_universal_range
    (n p q : ℕ) (x y : L) (a b : T)
    (hpq : p + q + 2 ≤ n)
    (ha : a ∈ tensorDegreeFiltration L p)
    (hb : b ∈ tensorDegreeFiltration L q) :
    letI := higginsAssociatedModule L
    letI := higginsAssociatedModuleOpposite L
    letI := higginsAssociatedSMulCommClass L
    letI := tensorCommutatorIdealSMulCommClass L
    DirectSum.lof ℤ ℕ (HigginsGradedPiece L) n
        (Submodule.Quotient.mk
          (higginsGeneratorElement L n p q x y a b hpq ha hb)) ∈
      LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  letI := tensorCommutatorIdealSMulCommClass L
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨as, has, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨bs, hbs, rfl⟩ := hb
          have hrange := higginsWordRelationWordClass_mem_universal_range
            L n as bs x y (by omega)
          convert hrange using 1
      | zero =>
          have hz : higginsGeneratorElement L n p q x y (tensorWord L as) 0
              hpq (tensorWord_mem_tensorDegreeFiltration L has)
              (tensorDegreeFiltration L q).zero_mem = 0 := by
            apply Subtype.ext
            simp [higginsGeneratorElement]
          rw [hz, Submodule.Quotient.mk_zero, map_zero]
          exact (LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap).zero_mem
      | add b c hbmem hcmem hb hc =>
          have hadd := (LinearMap.range
            (higginsUniversalToFiltrationHom L).toLinearMap).add_mem hb hc
          rw [← map_add, ← Submodule.Quotient.mk_add] at hadd
          convert hadd using 1
          apply lof_quotient_mk_eq_of_coe_eq L
          · rfl
          · simp [higginsGeneratorElement, mul_add]
      | smul c b hbmem hb =>
          have hsmul := zsmul_mem hb c
          rw [← map_smul] at hsmul
          have hmk : c • Submodule.Quotient.mk
                (higginsGeneratorElement L n p q x y (tensorWord L as) b hpq
                  (tensorWord_mem_tensorDegreeFiltration L has) hbmem) =
              Submodule.Quotient.mk
                (c • higginsGeneratorElement L n p q x y (tensorWord L as) b hpq
                  (tensorWord_mem_tensorDegreeFiltration L has) hbmem) :=
            (Submodule.Quotient.mk_smul (previousHigginsFiltration L n) c _).symm
          have hsmul' : DirectSum.lof ℤ ℕ (HigginsGradedPiece L) n
                (Submodule.Quotient.mk
                  (c • higginsGeneratorElement L n p q x y (tensorWord L as) b hpq
                    (tensorWord_mem_tensorDegreeFiltration L has) hbmem)) ∈
              LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap := by
            rw [← hmk]
            exact hsmul
          convert hsmul' using 1
          apply lof_quotient_mk_eq_of_coe_eq L
          · rfl
          · change (tensorWord L as * envelopingRelation L x y) *
                (algebraMap ℤ T c * b) =
              algebraMap ℤ T c *
                ((tensorWord L as * envelopingRelation L x y) * b)
            rw [← mul_assoc, ← Algebra.commutes c, mul_assoc]
  | zero =>
      have hz : higginsGeneratorElement L n p q x y 0 b hpq
          (tensorDegreeFiltration L p).zero_mem hb = 0 := by
        apply Subtype.ext
        simp [higginsGeneratorElement]
      rw [hz, Submodule.Quotient.mk_zero, map_zero]
      exact (LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap).zero_mem
  | add a c hamem hcmem ha hc =>
      have hadd := (LinearMap.range
        (higginsUniversalToFiltrationHom L).toLinearMap).add_mem ha hc
      rw [← map_add, ← Submodule.Quotient.mk_add] at hadd
      convert hadd using 1
      apply lof_quotient_mk_eq_of_coe_eq L
      · rfl
      · simp [higginsGeneratorElement, add_mul]
  | smul c a hamem ha =>
      have hsmul := zsmul_mem ha c
      rw [← map_smul] at hsmul
      have hmk : c • Submodule.Quotient.mk
            (higginsGeneratorElement L n p q x y a b hpq hamem hb) =
          Submodule.Quotient.mk
            (c • higginsGeneratorElement L n p q x y a b hpq hamem hb) :=
        (Submodule.Quotient.mk_smul (previousHigginsFiltration L n) c _).symm
      have hsmul' : DirectSum.lof ℤ ℕ (HigginsGradedPiece L) n
            (Submodule.Quotient.mk
              (c • higginsGeneratorElement L n p q x y a b hpq hamem hb)) ∈
          LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap := by
        rw [← hmk]
        exact hsmul
      convert hsmul' using 1
      apply lof_quotient_mk_eq_of_coe_eq L
      · rfl
      · simp [higginsGeneratorElement, mul_assoc]

theorem higginsGradedClass_mem_universal_range (n : ℕ)
    (t : higginsFiltration L n) :
    letI := higginsAssociatedModule L
    letI := higginsAssociatedModuleOpposite L
    letI := higginsAssociatedSMulCommClass L
    letI := tensorCommutatorIdealSMulCommClass L
    DirectSum.lof ℤ ℕ (HigginsGradedPiece L) n (Submodule.Quotient.mk t) ∈
      LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  letI := tensorCommutatorIdealSMulCommClass L
  rcases t with ⟨t, ht⟩
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨p, q, x, y, a, b, hpq, ha, hb, rfl⟩ := ht
      exact higginsGeneratorClass_mem_universal_range L n p q x y a b hpq ha hb
  | zero =>
      have hzero : (⟨0, (higginsFiltration L n).zero_mem⟩ :
          higginsFiltration L n) = 0 := Subtype.ext (by rfl)
      rw [hzero]
      rw [Submodule.Quotient.mk_zero, map_zero]
      exact (LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap).zero_mem
  | add a b hamem hbmem ha hb =>
      have hadd := (LinearMap.range
        (higginsUniversalToFiltrationHom L).toLinearMap).add_mem ha hb
      rw [← map_add, ← Submodule.Quotient.mk_add] at hadd
      exact hadd
  | smul c a hamem ha =>
      have hsmul := zsmul_mem ha c
      rw [← map_smul] at hsmul
      have hmk : c • Submodule.Quotient.mk (⟨a, hamem⟩ : higginsFiltration L n) =
          Submodule.Quotient.mk (c • (⟨a, hamem⟩ : higginsFiltration L n)) :=
        (Submodule.Quotient.mk_smul (previousHigginsFiltration L n) c _).symm
      have hsmul' : DirectSum.lof ℤ ℕ (HigginsGradedPiece L) n
            (Submodule.Quotient.mk (c • (⟨a, hamem⟩ : higginsFiltration L n))) ∈
          LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap := by
        rw [← hmk]
        exact hsmul
      convert hsmul' using 1

theorem higginsUniversalToFiltrationHom_surjective :
    letI := higginsAssociatedModule L
    letI := higginsAssociatedModuleOpposite L
    letI := higginsAssociatedSMulCommClass L
    letI := tensorCommutatorIdealSMulCommClass L
    Function.Surjective (higginsUniversalToFiltrationHom L) := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  letI := tensorCommutatorIdealSMulCommClass L
  intro a
  have ha : a ∈ LinearMap.range (higginsUniversalToFiltrationHom L).toLinearMap := by
    induction a using DirectSum.induction_on with
    | zero => exact (LinearMap.range
        (higginsUniversalToFiltrationHom L).toLinearMap).zero_mem
    | add a b ha hb => exact (LinearMap.range
        (higginsUniversalToFiltrationHom L).toLinearMap).add_mem ha hb
    | of n q =>
        induction q using Submodule.Quotient.induction_on with
        | _ t => exact higginsGradedClass_mem_universal_range L n t
  exact ha

/-- The leading-term comparison is injective.  Together with
`higginsUniversalToFiltrationHom_surjective`, this says that the associated
graded Higgins module is exactly the commutative tensor quotient. -/
theorem higginsLeadingComparison_injective :
    letI := higginsAssociatedModule L
    letI := higginsAssociatedModuleOpposite L
    letI := higginsAssociatedSMulCommClass L
    letI := tensorCommutatorIdealSMulCommClass L
    Function.Injective (higginsLeadingComparison L) := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  letI := tensorCommutatorIdealSMulCommClass L
  intro a b hab
  obtain ⟨a', rfl⟩ := higginsUniversalToFiltrationHom_surjective L a
  obtain ⟨b', rfl⟩ := higginsUniversalToFiltrationHom_surjective L b
  have hab' : a' = b' := by
    simpa only [higginsLeading_after_universal] using hab
  exact congrArg (higginsUniversalToFiltrationHom L) hab'

/-- If the degree-`n` leading tensor component of an element of `J(n)`
vanishes, then that element already belongs to `J(n-1)`. -/
theorem mem_previousHigginsFiltration_of_component_eq_zero (n : ℕ)
    (t : higginsFiltration L n)
    (ht : tensorHomogeneousComponent L n (t : T) = 0) :
    t ∈ previousHigginsFiltration L n := by
  letI := higginsAssociatedModule L
  letI := higginsAssociatedModuleOpposite L
  letI := higginsAssociatedSMulCommClass L
  letI := tensorCommutatorIdealSMulCommClass L
  have hlead : higginsLeadingComparison L
        (DirectSum.lof ℤ ℕ (HigginsGradedPiece L) n
          (Submodule.Quotient.mk t)) = 0 := by
    rw [higginsLeadingComparison_lof]
    apply Subtype.ext
    exact ht
  have hclass : DirectSum.lof ℤ ℕ (HigginsGradedPiece L) n
        (Submodule.Quotient.mk t) = 0 :=
    higginsLeadingComparison_injective L hlead
  have hcomponent := congrArg
    (DirectSum.component ℤ ℕ (HigginsGradedPiece L) n) hclass
  rw [DirectSum.component.lof_self, map_zero] at hcomponent
  exact (Submodule.Quotient.mk_eq_zero _).mp hcomponent

/-- A tensor of degree at most one which belongs to some `J(n)` already
belongs to `J(1)`.  This is the filtered descent at the heart of the
embedding theorem. -/
theorem mem_higginsFiltration_one_of_mem_degree_one {t : T}
    (htdegree : t ∈ tensorDegreeFiltration L 1) (n : ℕ)
    (ht : t ∈ higginsFiltration L n) :
    t ∈ higginsFiltration L 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · exact higginsFiltration_mono L hn ht
      · have hcomponent : tensorHomogeneousComponent L n t = 0 :=
          tensorHomogeneousComponent_eq_zero_of_mem_filtration L htdegree (by omega)
        have hprevious := mem_previousHigginsFiltration_of_component_eq_zero L n
          (⟨t, ht⟩ : higginsFiltration L n) hcomponent
        have ht' : t ∈ higginsFiltration L (n - 1) := hprevious
        exact ih (n - 1) (by omega) ht'

/-- The degree-one copy of `L` has zero intersection with the defining
relation ideal in the tensor algebra. -/
theorem tensorGenerator_eq_zero_of_mem_envelopingRelationIdeal (x : L)
    (hx : TensorAlgebra.ι ℤ x ∈ envelopingRelationIdeal L) :
    TensorAlgebra.ι ℤ x = 0 := by
  obtain ⟨n, hn⟩ := exists_higginsFiltration_of_mem_envelopingRelationIdeal L hx
  have hone := mem_higginsFiltration_one_of_mem_degree_one L
    (ι_mem_tensorDegreeFiltration L x) n hn
  rw [higginsFiltration_one] at hone
  exact hone

/-! ## Comparison with mathlib's universal enveloping algebra -/

/-- The quotient of the tensor algebra by the explicitly generated
enveloping relation ideal. -/
abbrev EnvelopingRelationQuotient := T ⧸ envelopingRelationIdeal L

-- For the quotient, use the Lie algebra structure coming from its `ℤ`-algebra
-- structure.  Over `ℤ` there is also the canonical Lie-ring module structure;
-- selecting this instance removes that harmless instance diamond.
local instance (priority := 1000) envelopingRelationQuotientModule :
    Module ℤ (EnvelopingRelationQuotient L) :=
  Algebra.toModule

local instance (priority := 1000) envelopingRelationQuotientLieAlgebra :
    LieAlgebra ℤ (EnvelopingRelationQuotient L) :=
  LieAlgebra.ofAssociativeAlgebra

/-- The generators in the explicit ideal quotient form a Lie homomorphism. -/
def toEnvelopingRelationQuotient :
    L →ₗ⁅ℤ⁆ EnvelopingRelationQuotient L where
  toLinearMap :=
    { toFun := fun x ↦
        Ideal.Quotient.mk (envelopingRelationIdeal L) (TensorAlgebra.ι ℤ x)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp [Algebra.smul_def] }
  map_lie' := by
    intro x y
    have hr : Ideal.Quotient.mk (envelopingRelationIdeal L)
          (envelopingRelation L x y) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (envelopingRelation_mem_ideal L x y)
    change Ideal.Quotient.mk (envelopingRelationIdeal L)
        (TensorAlgebra.ι ℤ ⁅x, y⁆) =
      ⁅Ideal.Quotient.mk (envelopingRelationIdeal L) (TensorAlgebra.ι ℤ x),
        Ideal.Quotient.mk (envelopingRelationIdeal L) (TensorAlgebra.ι ℤ y)⁆
    simp only [envelopingRelation, map_sub, map_mul] at hr
    simp only [LieRing.of_associative_ring_bracket]
    rw [sub_eq_zero] at hr
    exact hr.symm

/-- The universal enveloping algebra maps to the explicit ideal quotient. -/
def universalToEnvelopingRelationQuotient :
    UniversalEnvelopingAlgebra ℤ L →ₐ[ℤ] EnvelopingRelationQuotient L :=
  UniversalEnvelopingAlgebra.lift ℤ (toEnvelopingRelationQuotient L)

@[simp]
theorem universalToEnvelopingRelationQuotient_i (x : L) :
    universalToEnvelopingRelationQuotient L
        (UniversalEnvelopingAlgebra.ι ℤ x) =
      Ideal.Quotient.mk (envelopingRelationIdeal L) (TensorAlgebra.ι ℤ x) := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ
    (toEnvelopingRelationQuotient L) x

/-- Equality to zero in mathlib's universal enveloping algebra implies
membership in the explicit tensor relation ideal. -/
theorem tensorGenerator_mem_envelopingRelationIdeal_of_canonical_eq_zero
    (x : L) (hx : UniversalEnvelopingAlgebra.ι ℤ x = 0) :
    TensorAlgebra.ι ℤ x ∈ envelopingRelationIdeal L := by
  have hq := congrArg (universalToEnvelopingRelationQuotient L) hx
  rw [universalToEnvelopingRelationQuotient_i, map_zero] at hq
  exact Ideal.Quotient.eq_zero_iff_mem.mp hq

/-- **Integral embedding theorem.**  For every Lie ring, the canonical Lie
homomorphism into its universal enveloping algebra over `ℤ` is injective.

No basis, freeness, flatness, presentation, or auxiliary representation is
required in the statement. -/
theorem canonicalMap_injective_int :
    Function.Injective
      (UniversalEnvelopingAlgebra.ι ℤ : L → UniversalEnvelopingAlgebra ℤ L) := by
  intro x y hxy
  have hu : UniversalEnvelopingAlgebra.ι ℤ (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hmem : TensorAlgebra.ι ℤ (x - y) ∈ envelopingRelationIdeal L :=
    tensorGenerator_mem_envelopingRelationIdeal_of_canonical_eq_zero L (x - y) hu
  have hzero : TensorAlgebra.ι ℤ (x - y) = 0 :=
    tensorGenerator_eq_zero_of_mem_envelopingRelationIdeal L (x - y) hmem
  have heq : TensorAlgebra.ι ℤ (x - y) = TensorAlgebra.ι ℤ (0 : L) := by
    simpa using hzero
  exact sub_eq_zero.mp ((TensorAlgebra.ι_inj ℤ (x - y) 0).mp heq)

end

end LieRings.PBW.Higgins

namespace LieRings.PBW

universe u

/-- Public, parameter-free form of the integral embedding theorem. -/
theorem canonicalMap_injective_int (L : Type u) [LieRing L] :
    Function.Injective
      (UniversalEnvelopingAlgebra.ι ℤ : L → UniversalEnvelopingAlgebra ℤ L) :=
  Higgins.canonicalMap_injective_int L

end LieRings.PBW
