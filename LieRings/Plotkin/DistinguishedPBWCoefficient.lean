import LieRings.Plotkin.CentralDerivative
import LieRings.PBW.HigginsEmbedding
import LieRings.PBW.HigginsCyclic
import LieRings.PBW.Surjectivity
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Util.AssertNoSorry

/-!
# A distinguished PBW coefficient for split central cyclic ideals

This file proves the ordered-cyclic PBW coefficient calculation in the
central-derivative lemma.  The construction uses a diagonal presentation of
the finitely generated Abelian group underlying the ambient Lie ring.  Its
only filtered input is Higgins's integral leading-component comparison.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

open LieRings.PBW.Higgins

namespace DistinguishedPBW

variable {E : Type u} [LieRing E]
variable {D : Type v} [AddCommGroup D]
variable {ι : Type u} [DecidableEq ι] [LinearOrder ι]

abbrev P := ι →₀ ℤ
abbrev T := TensorAlgebra ℤ (P (ι := ι))

-- Evaluation of a free cyclic presentation in the ambient Lie ring.
variable (ε : P (ι := ι) →ₗ[ℤ] E)

/-- The tensor-algebra map induced by the presentation. -/
abbrev tensorMap : T (ι := ι) →ₐ[ℤ] TensorAlgebra ℤ E :=
  AuxiliaryPresentation.tensorMap ε

/-- Evaluation of presentation tensors in the universal enveloping algebra. -/
def tensorToUEA : T (ι := ι) →ₐ[ℤ] UEA ℤ E :=
  TensorAlgebra.lift ℤ
    ((UniversalEnvelopingAlgebra.ι ℤ).toLinearMap.comp ε)

@[simp]
theorem tensorToUEA_ι (p : P (ι := ι)) :
    tensorToUEA ε (TensorAlgebra.ι ℤ p) =
      UniversalEnvelopingAlgebra.ι ℤ (ε p) := by
  simp [tensorToUEA, LinearMap.comp_apply]

theorem tensorToUEA_eq_mk_comp_tensorMap :
    tensorToUEA ε =
      (UniversalEnvelopingAlgebra.mkAlgHom ℤ E).comp (tensorMap ε) := by
  apply TensorAlgebra.hom_ext
  apply LinearMap.ext
  intro p
  simp [tensorToUEA, tensorMap, AuxiliaryPresentation.tensorMap_ι]

/-- Vanishing after evaluation in `U(E)` puts the evaluated tensor in the
explicit enveloping-relation ideal. -/
theorem tensorMap_mem_envelopingRelationIdeal_of_tensorToUEA_eq_zero
    {t : T (ι := ι)} (ht : tensorToUEA ε t = 0) :
    tensorMap ε t ∈ envelopingRelationIdeal E := by
  have hmaps :
      (universalToEnvelopingRelationQuotient E).comp (tensorToUEA ε) =
        (Ideal.Quotient.mkₐ ℤ (envelopingRelationIdeal E)).comp
          (tensorMap ε) := by
    apply TensorAlgebra.hom_ext
    apply LinearMap.ext
    intro p
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, tensorToUEA_ι, AuxiliaryPresentation.tensorMap_ι,
      universalToEnvelopingRelationQuotient_i]
    rfl
  have hz := congrArg (universalToEnvelopingRelationQuotient E) ht
  rw [map_zero] at hz
  have hz' := DFunLike.congr_fun hmaps t
  change universalToEnvelopingRelationQuotient E (tensorToUEA ε t) =
    Ideal.Quotient.mk (envelopingRelationIdeal E) (tensorMap ε t) at hz'
  rw [hz] at hz'
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz'.symm

/-- Ordered collection followed by evaluation in `U(E)`. -/
def collectedMap : T (ι := ι) →ₗ[ℤ] UEA ℤ E :=
  (tensorToUEA ε).toLinearMap.comp
    (OrderedCyclic.normalizer (ι := ι))

/-- The degree-one coefficient attached to a linear map out of `E`.
The square-zero target kills every tensor word except those of length one. -/
def rawCoefficient (π : E →ₗ[ℤ] D) : T (ι := ι) →ₗ[ℤ] D :=
  by
    letI : Module ℤᵐᵒᵖ D :=
      Module.compHom D ((RingHom.id ℤ).fromOpposite mul_comm)
    let F : T (ι := ι) →ₐ[ℤ] TrivSqZeroExt ℤ D :=
      TensorAlgebra.lift ℤ
        ((TrivSqZeroExt.inrHom ℤ D).comp (π.comp ε))
    refine
      { toFun := fun t ↦ (F t).snd
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      simp [F]
    · intro n x
      simp [F]

@[simp]
theorem rawCoefficient_ι (π : E →ₗ[ℤ] D) (p : P (ι := ι)) :
    rawCoefficient ε π (TensorAlgebra.ι ℤ p) = π (ε p) := by
  simp [rawCoefficient, LinearMap.comp_apply]

@[simp]
theorem rawCoefficient_one (π : E →ₗ[ℤ] D) :
    rawCoefficient ε π 1 = 0 := by
  letI : Module ℤᵐᵒᵖ D :=
    Module.compHom D ((RingHom.id ℤ).fromOpposite mul_comm)
  change ((TensorAlgebra.lift ℤ
    ((TrivSqZeroExt.inrHom ℤ D).comp (π.comp ε))) (1 : T (ι := ι))).snd = 0
  rw [map_one]
  rfl

theorem rawCoefficient_word (π : E →ₗ[ℤ] D) (xs : List ι) :
    rawCoefficient ε π (OrderedCyclic.word (ι := ι) xs) =
      match xs with
      | [i] => π (ε (Finsupp.single i 1))
      | _ => 0 := by
  letI : Module ℤᵐᵒᵖ D :=
    Module.compHom D ((RingHom.id ℤ).fromOpposite mul_comm)
  cases xs with
  | nil => simp
  | cons i xs =>
      cases xs with
      | nil => simp
      | cons j xs =>
          rw [OrderedCyclic.word_cons, OrderedCyclic.word_cons]
          change ((TensorAlgebra.lift ℤ
            ((TrivSqZeroExt.inrHom ℤ D).comp (π.comp ε)))
              (TensorAlgebra.ι ℤ (Finsupp.single i 1) *
                (TensorAlgebra.ι ℤ (Finsupp.single j 1) *
                  OrderedCyclic.word (ι := ι) xs))).snd = 0
          simp only [map_mul, TensorAlgebra.lift_ι_apply, LinearMap.comp_apply]
          simp only [TrivSqZeroExt.inrHom_apply]
          rw [← mul_assoc, TrivSqZeroExt.inr_mul_inr, zero_mul]
          rfl

/-- The ordered normalizer does not change the degree-one coefficient. -/
theorem rawCoefficient_normalizer (π : E →ₗ[ℤ] D) (t : T (ι := ι)) :
    rawCoefficient ε π (OrderedCyclic.normalizer (ι := ι) t) =
      rawCoefficient ε π t := by
  have hmaps :
      (rawCoefficient ε π).comp (OrderedCyclic.normalizer (ι := ι)) =
        rawCoefficient ε π := by
    apply (OrderedCyclic.wordBasis (ι := ι)).ext
    intro w
    rw [LinearMap.comp_apply]
    change rawCoefficient ε π
        (OrderedCyclic.normalizer (ι := ι)
          (OrderedCyclic.word (ι := ι) (FreeMonoid.toList w))) =
      rawCoefficient ε π
        (OrderedCyclic.word (ι := ι) (FreeMonoid.toList w))
    rw [OrderedCyclic.normalizer_word, rawCoefficient_word,
      rawCoefficient_word]
    cases hxs : FreeMonoid.toList w with
    | nil => simp
    | cons i xs =>
        cases xs with
        | nil => simp [hxs]
        | cons j xs =>
            have hlen :
                (((FreeMonoid.toList w : Multiset ι).sort (· ≤ ·))).length ≥ 2 := by
              simp [hxs]
            generalize hs : ((FreeMonoid.toList w : Multiset ι).sort (· ≤ ·)) = ys at hlen ⊢
            rcases ys with _ | ⟨y, _ | ⟨z, ys⟩⟩ <;> simp_all
  exact LinearMap.congr_fun hmaps t

/-- The raw degree-one coefficient only depends on the evaluated tensor in
`T(E)`.  This elementary factorization is useful at the bottom of the
filtered kernel induction. -/
theorem rawCoefficient_eq_zero_of_tensorMap_eq_zero
    (π : E →ₗ[ℤ] D) {t : T (ι := ι)}
    (ht : tensorMap ε t = 0) :
    rawCoefficient ε π t = 0 := by
  letI : Module ℤᵐᵒᵖ D :=
    Module.compHom D ((RingHom.id ℤ).fromOpposite mul_comm)
  let G : TensorAlgebra ℤ E →ₐ[ℤ] TrivSqZeroExt ℤ D :=
    TensorAlgebra.lift ℤ ((TrivSqZeroExt.inrHom ℤ D).comp π)
  have hcomp :
      G.comp (tensorMap ε) =
        TensorAlgebra.lift ℤ
          ((TrivSqZeroExt.inrHom ℤ D).comp (π.comp ε)) := by
    apply TensorAlgebra.hom_ext
    apply LinearMap.ext
    intro p
    simp [G, AuxiliaryPresentation.tensorMap_ι, LinearMap.comp_apply]
  change ((TensorAlgebra.lift ℤ
    ((TrivSqZeroExt.inrHom ℤ D).comp (π.comp ε))) t).snd = 0
  rw [← hcomp]
  change (G (tensorMap ε t)).snd = 0
  rw [ht, map_zero]
  rfl

/-- Ordered collection is a projection. -/
theorem normalizer_idempotent (t : T (ι := ι)) :
    OrderedCyclic.normalizer (ι := ι)
        (OrderedCyclic.normalizer (ι := ι) t) =
      OrderedCyclic.normalizer (ι := ι) t := by
  have hmaps :
      (OrderedCyclic.normalizer (ι := ι)).comp
          (OrderedCyclic.normalizer (ι := ι)) =
        OrderedCyclic.normalizer (ι := ι) := by
    apply (OrderedCyclic.wordBasis (ι := ι)).ext
    intro w
    simp only [LinearMap.comp_apply]
    change OrderedCyclic.normalizer (ι := ι)
        (OrderedCyclic.normalizer (ι := ι)
          (OrderedCyclic.word (ι := ι) (FreeMonoid.toList w))) =
      OrderedCyclic.normalizer (ι := ι)
        (OrderedCyclic.word (ι := ι) (FreeMonoid.toList w))
    rw [OrderedCyclic.normalizer_word, OrderedCyclic.normalizer_word]
    congr 1
    simpa using List.mergeSort_eq_self (· ≤ ·)
      (Multiset.pairwise_sort (FreeMonoid.toList w : Multiset ι) (· ≤ ·))
  exact LinearMap.congr_fun hmaps t

/-- Projection to tensor degree, stated without an irrelevant Lie bracket on the source. -/
def tensorComponent {M : Type*} [AddCommGroup M] (n : ℕ) :
    TensorAlgebra ℤ M →ₗ[ℤ] TensorAlgebra ℤ M :=
  TensorPower.toTensorAlgebra.comp
    ((DirectSum.component ℤ ℕ (fun k => TensorPower ℤ k M) n).comp
      (TensorAlgebra.toDirectSum (R := ℤ) (M := M)).toLinearMap)

@[simp]
theorem tensorComponent_tensorWord_same {M : Type*} [AddCommGroup M]
    (xs : List M) :
    tensorComponent xs.length (lieWord M xs) = lieWord M xs := by
  rw [show lieWord M xs =
      TensorAlgebra.tprod ℤ M xs.length (fun i => xs.get i) by
        simp [lieWord, TensorAlgebra.tprod_apply]]
  change TensorPower.toTensorAlgebra
      (DirectSum.component ℤ ℕ (fun k => TensorPower ℤ k M) xs.length
        (TensorAlgebra.toDirectSum
          (TensorAlgebra.tprod ℤ M xs.length (fun i => xs.get i)))) = _
  rw [TensorAlgebra.toDirectSum_tensorPower_tprod,
    ← DirectSum.lof_eq_of (R := ℤ), DirectSum.component.lof_self,
    TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]

theorem tensorComponent_tensorWord_of_ne {M : Type*} [AddCommGroup M]
    (n : ℕ) (xs : List M) (h : xs.length ≠ n) :
    tensorComponent n (lieWord M xs) = 0 := by
  -- This is the defining direct-sum projection; no Lie bracket is involved.
  rw [show lieWord M xs =
      TensorAlgebra.tprod ℤ M xs.length (fun i => xs.get i) by
        simp [lieWord, TensorAlgebra.tprod_apply]]
  change TensorPower.toTensorAlgebra
      (DirectSum.component ℤ ℕ (fun k => TensorPower ℤ k M) n
        (TensorAlgebra.toDirectSum
          (TensorAlgebra.tprod ℤ M xs.length (fun i => xs.get i)))) = 0
  rw [TensorAlgebra.toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of (R := ℤ),
    DirectSum.component.of]
  simp [h]

theorem tensorMap_lieWord (xs : List (P (ι := ι))) :
    tensorMap ε (lieWord (P (ι := ι)) xs) =
      lieWord E (xs.map ε) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, lieWord_cons, map_mul,
        AuxiliaryPresentation.tensorMap_ι, ih]

theorem ordered_word_eq_lieWord (xs : List ι) :
    OrderedCyclic.word (ι := ι) xs =
      lieWord (P (ι := ι)) (xs.map fun i ↦ Finsupp.single i 1) := by
  rw [OrderedCyclic.word, OrderedCyclic.wordBasis_apply,
    FreeMonoid.toList_ofList]

@[simp]
theorem tensorComponent_orderedWord_same (xs : List ι) :
    tensorComponent xs.length (OrderedCyclic.word (ι := ι) xs) =
      OrderedCyclic.word (ι := ι) xs := by
  rw [ordered_word_eq_lieWord]
  simpa using tensorComponent_tensorWord_same
    (xs.map fun i ↦ Finsupp.single i (1 : ℤ))

theorem tensorComponent_orderedWord_of_ne (n : ℕ) (xs : List ι)
    (h : xs.length ≠ n) :
    tensorComponent n (OrderedCyclic.word (ι := ι) xs) = 0 := by
  rw [ordered_word_eq_lieWord]
  apply tensorComponent_tensorWord_of_ne
  simpa using h

/-- Tensor evaluation commutes with projection to a fixed tensor degree. -/
theorem tensorMap_homogeneousComponent (n : ℕ) (t : T (ι := ι)) :
    tensorMap ε (tensorComponent n t) =
      tensorComponent n (tensorMap ε t) := by
  have hmaps :
      (tensorMap ε).toLinearMap.comp
          (tensorComponent n) =
        (tensorComponent n).comp (tensorMap ε).toLinearMap := by
    apply (OrderedCyclic.wordBasis (ι := ι)).ext
    intro w
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [OrderedCyclic.wordBasis_apply]
    change tensorMap ε
        (tensorComponent n
          (lieWord (P (ι := ι))
            ((FreeMonoid.toList w).map fun i ↦ Finsupp.single i 1))) =
      tensorComponent n
        (tensorMap ε
          (lieWord (P (ι := ι))
            ((FreeMonoid.toList w).map fun i ↦ Finsupp.single i 1)))
    by_cases hlen : (FreeMonoid.toList w).length = n
    · rw [← List.length_map (f := fun i ↦ Finsupp.single i (1 : ℤ))] at hlen
      rw [← hlen, tensorComponent_tensorWord_same]
      rw [tensorMap_lieWord]
      symm
      have hmaplen :
          (((FreeMonoid.toList w).map fun i ↦ Finsupp.single i (1 : ℤ)).map ε).length =
            ((FreeMonoid.toList w).map fun i ↦ Finsupp.single i (1 : ℤ)).length := by
        simp
      rw [← hmaplen]
      exact tensorComponent_tensorWord_same _
    · have hlen' :
          (((FreeMonoid.toList w).map fun i ↦ Finsupp.single i (1 : ℤ))).length ≠ n := by
        simpa using hlen
      rw [tensorComponent_tensorWord_of_ne n _ hlen', map_zero]
      rw [tensorMap_lieWord]
      rw [tensorComponent_tensorWord_of_ne]
      simpa using hlen
  exact LinearMap.congr_fun hmaps t

set_option maxHeartbeats 800000 in
/-- Ordered collection commutes with projection to a fixed tensor degree. -/
theorem normalizer_homogeneousComponent (n : ℕ) (t : T (ι := ι)) :
    OrderedCyclic.normalizer (ι := ι)
        (tensorComponent n t) =
      tensorComponent n
        (OrderedCyclic.normalizer (ι := ι) t) := by
  have hmaps :
      (OrderedCyclic.normalizer (ι := ι)).comp
          (tensorComponent n) =
        (tensorComponent n).comp
          (OrderedCyclic.normalizer (ι := ι)) := by
    apply (OrderedCyclic.wordBasis (ι := ι)).ext
    intro w
    simp only [LinearMap.comp_apply]
    change OrderedCyclic.normalizer (ι := ι)
        (tensorComponent n
          (OrderedCyclic.word (ι := ι) (FreeMonoid.toList w))) =
      tensorComponent n
        (OrderedCyclic.normalizer (ι := ι)
          (OrderedCyclic.word (ι := ι) (FreeMonoid.toList w)))
    rw [OrderedCyclic.normalizer_word]
    by_cases hlen : (FreeMonoid.toList w).length = n
    · let xs := FreeMonoid.toList w
      let ys := ((xs : Multiset ι).sort (· ≤ ·))
      have hxs : xs.length = n := hlen
      have hys : ys.length = n := by simp [ys, xs, hlen]
      have hcLeft : tensorComponent n
            (OrderedCyclic.word (ι := ι) xs) =
          OrderedCyclic.word (ι := ι) xs := by
        rw [← hxs]
        exact tensorComponent_orderedWord_same _
      have hcRight : tensorComponent n
            (OrderedCyclic.word (ι := ι) ys) =
          OrderedCyclic.word (ι := ι) ys := by
        rw [← hys]
        exact tensorComponent_orderedWord_same _
      change OrderedCyclic.normalizer (ι := ι)
          (tensorComponent n (OrderedCyclic.word (ι := ι) xs)) =
        tensorComponent n (OrderedCyclic.word (ι := ι) ys)
      rw [hcLeft, hcRight]
      exact OrderedCyclic.normalizer_word xs
    · let xs := FreeMonoid.toList w
      let ys := ((xs : Multiset ι).sort (· ≤ ·))
      have hxs : xs.length ≠ n := hlen
      have hys : ys.length ≠ n := by simpa [ys, xs] using hlen
      have hcLeft := tensorComponent_orderedWord_of_ne n xs hxs
      have hcRight := tensorComponent_orderedWord_of_ne n ys hys
      change OrderedCyclic.normalizer (ι := ι)
          (tensorComponent n (OrderedCyclic.word (ι := ι) xs)) =
        tensorComponent n (OrderedCyclic.word (ι := ι) ys)
      rw [hcLeft, map_zero, hcRight]
  exact LinearMap.congr_fun hmaps t

/-- The relation--commutator ideal is contained in the presentation ideal. -/
theorem relationCommutatorIdeal_le_relationIdeal :
    AuxiliaryPresentation.relationCommutatorIdeal ε ≤
      AuxiliaryPresentation.relationIdeal ε := by
  intro t ht
  change t ∈ TwoSidedIdeal.span
    (Set.range fun tq : T (ι := ι) × AuxiliaryPresentation.relationIdeal ε ↦
      ⁅tq.1, (tq.2 : T (ι := ι))⁆) at ht
  induction ht using TwoSidedIdeal.span_induction with
  | mem t ht =>
      obtain ⟨⟨a, q⟩, rfl⟩ := ht
      change a * (q : T (ι := ι)) - (q : T (ι := ι)) * a ∈
        AuxiliaryPresentation.relationIdeal ε
      exact (AuxiliaryPresentation.relationIdeal ε).sub_mem
        ((AuxiliaryPresentation.relationIdeal ε).mul_mem_left a q.property)
        ((AuxiliaryPresentation.relationIdeal ε).mul_mem_right a q.property)
  | zero => simp
  | add x y _ _ hx hy => exact (AuxiliaryPresentation.relationIdeal ε).add_mem hx hy
  | neg x _ hx => exact (AuxiliaryPresentation.relationIdeal ε).neg_mem hx
  | left_absorb a x _ hx =>
      exact (AuxiliaryPresentation.relationIdeal ε).mul_mem_left a hx
  | right_absorb b x _ hx =>
      exact (AuxiliaryPresentation.relationIdeal ε).mul_mem_right b hx

/-- For a diagonal cyclic presentation, collection carries every relation
back into the relation ideal. -/
theorem normalizer_mem_relationIdeal_of_diagonal
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    {q : T (ι := ι)} (hq : q ∈ AuxiliaryPresentation.relationIdeal ε) :
    OrderedCyclic.normalizer (ι := ι) q ∈
      AuxiliaryPresentation.relationIdeal ε := by
  change q ∈ TwoSidedIdeal.span
    (Set.range fun r : LinearMap.ker ε ↦
      TensorAlgebra.ι ℤ (r : P (ι := ι))) at hq
  have hspan {u : T (ι := ι)}
      (hu : u ∈ TwoSidedIdeal.span
        (Set.range fun r : LinearMap.ker ε ↦
          TensorAlgebra.ι ℤ (r : P (ι := ι)))) :
      ∀ a b : T (ι := ι),
        a * u * b - OrderedCyclic.normalizer (ι := ι) (a * u * b) ∈
          AuxiliaryPresentation.relationCommutatorIdeal ε := by
    induction hu using TwoSidedIdeal.span_induction with
    | mem u hu =>
        intro a b
        obtain ⟨r, rfl⟩ := hu
        exact OrderedCyclic.mul_diagonalRelation_mul_mod ε r (hdiag r) a b
    | zero => intro a b; simp
    | add x y _ _ hx hy =>
        intro a b
        have hz := (AuxiliaryPresentation.relationCommutatorIdeal ε).add_mem
          (hx a b) (hy a b)
        convert hz using 1 <;>
          simp only [mul_add, add_mul, map_add] <;> abel
    | neg x _ hx =>
        intro a b
        have hz := (AuxiliaryPresentation.relationCommutatorIdeal ε).neg_mem (hx a b)
        convert hz using 1 <;>
          simp only [mul_neg, neg_mul, map_neg] <;> abel
    | left_absorb c x _ hx =>
        intro a b
        simpa only [mul_assoc] using hx (a * c) b
    | right_absorb c x _ hx =>
        intro a b
        simpa only [mul_assoc] using hx a (c * b)
  have hdefect : q - OrderedCyclic.normalizer (ι := ι) q ∈
      AuxiliaryPresentation.relationCommutatorIdeal ε := by
    simpa using hspan hq 1 1
  have hdefectQ := relationCommutatorIdeal_le_relationIdeal ε hdefect
  have hneg := (AuxiliaryPresentation.relationIdeal ε).sub_mem hq hdefectQ
  convert hneg using 1 <;> abel

/-- A surjective map of generators induces a surjective tensor-algebra map. -/
theorem tensorMap_surjective (hε : Function.Surjective ε) :
    Function.Surjective (tensorMap ε) := by
  intro t
  induction t using TensorAlgebra.induction with
  | algebraMap z => exact ⟨algebraMap ℤ (T (ι := ι)) z, by simp⟩
  | ι x =>
      obtain ⟨p, rfl⟩ := hε x
      exact ⟨TensorAlgebra.ι ℤ p, AuxiliaryPresentation.tensorMap_ι ε p⟩
  | mul x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, by simp⟩
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp⟩

/-- Surjective tensor evaluation is also onto on the tensor commutator ideals. -/
theorem commutatorIdeal_surjective (hε : Function.Surjective ε)
    (k : tensorCommutatorIdeal E) :
    ∃ k' : tensorCommutatorIdeal (P (ι := ι)), tensorMap ε k' = k := by
  let G := TwoSidedIdeal.span
    (Set.range fun xy : E × E ↦
      ⁅TensorAlgebra.ι ℤ xy.1, TensorAlgebra.ι ℤ xy.2⁆)
  have hkG : (k : TensorAlgebra ℤ E) ∈ G := by
    change (k : TensorAlgebra ℤ E) ∈ elementaryCommutatorIdeal E
    rw [elementaryCommutatorIdeal_eq_tensorCommutatorIdeal]
    exact k.property
  have hspan {u : TensorAlgebra ℤ E} (hu : u ∈ G) :
      ∃ k' : tensorCommutatorIdeal (P (ι := ι)), tensorMap ε k' = u := by
    induction hu using TwoSidedIdeal.span_induction with
    | mem u hu =>
        obtain ⟨⟨x, y⟩, rfl⟩ := hu
        obtain ⟨p, rfl⟩ := hε x
        obtain ⟨q, rfl⟩ := hε y
        let k' : tensorCommutatorIdeal (P (ι := ι)) :=
          ⟨⁅TensorAlgebra.ι ℤ p, TensorAlgebra.ι ℤ q⁆,
            by
              rw [← elementaryCommutatorIdeal_eq_tensorCommutatorIdeal]
              exact elementary_commutator_mem (P (ι := ι)) p q⟩
        refine ⟨k', ?_⟩
        simp [k', LieRing.of_associative_ring_bracket,
          AuxiliaryPresentation.tensorMap_ι]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by simp [ha, hb]⟩
    | neg x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨-a, by simp [ha]⟩
    | left_absorb a x _ hx =>
        obtain ⟨a', ha'⟩ := tensorMap_surjective ε hε a
        obtain ⟨x', hx'⟩ := hx
        exact ⟨⟨a' * (x' : T (ι := ι)),
          (tensorCommutatorIdeal (P (ι := ι))).mul_mem_left a' x'.property⟩,
          by simp [ha', hx']⟩
    | right_absorb b x _ hx =>
        obtain ⟨b', hb'⟩ := tensorMap_surjective ε hε b
        obtain ⟨x', hx'⟩ := hx
        exact ⟨⟨(x' : T (ι := ι)) * b',
          (tensorCommutatorIdeal (P (ι := ι))).mul_mem_right b' x'.property⟩,
          by simp [hb', hx']⟩
  exact hspan hkG

/-! ### The finite tensor-degree descent -/

/-- A tensor is supported on words of length at most `n`. -/
def WordDegreeLE (n : ℕ) (t : T (ι := ι)) : Prop :=
  ∀ w : FreeMonoid ι,
    (OrderedCyclic.wordBasis (ι := ι)).repr t w ≠ 0 →
      (FreeMonoid.toList w).length ≤ n

theorem exists_wordDegreeLE (t : T (ι := ι)) : ∃ n, WordDegreeLE n t := by
  let s := ((OrderedCyclic.wordBasis (ι := ι)).repr t).support
  refine ⟨∑ w ∈ s, (FreeMonoid.toList w).length, ?_⟩
  intro w hw
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finsupp.mem_support_iff.mpr hw)

theorem tensorComponent_wordBasis (n : ℕ) (w : FreeMonoid ι) :
    tensorComponent n (OrderedCyclic.wordBasis (ι := ι) w) =
      if (FreeMonoid.toList w).length = n then
        OrderedCyclic.wordBasis (ι := ι) w else 0 := by
  change tensorComponent n
      (OrderedCyclic.word (ι := ι) (FreeMonoid.toList w)) = _
  split <;> rename_i h
  · rw [← h, tensorComponent_orderedWord_same]
    simp [OrderedCyclic.word, FreeMonoid.ofList_toList]
  · rw [tensorComponent_orderedWord_of_ne n _ h]

theorem repr_tensorComponent_apply (n : ℕ) (t : T (ι := ι))
    (w : FreeMonoid ι) :
    (OrderedCyclic.wordBasis (ι := ι)).repr (tensorComponent n t) w =
      if (FreeMonoid.toList w).length = n then
        (OrderedCyclic.wordBasis (ι := ι)).repr t w else 0 := by
  let coord : T (ι := ι) →ₗ[ℤ] ℤ :=
    (Finsupp.lapply w).comp
      (OrderedCyclic.wordBasis (ι := ι)).repr.toLinearMap
  have hmaps : coord.comp (tensorComponent n) =
      if (FreeMonoid.toList w).length = n then coord else 0 := by
    apply (OrderedCyclic.wordBasis (ι := ι)).ext
    intro v
    simp only [LinearMap.comp_apply]
    rw [tensorComponent_wordBasis]
    by_cases hv : v = w
    · subst v
      by_cases hlen : (FreeMonoid.toList w).length = n <;>
        simp [hlen, coord]
    · by_cases hlenv : (FreeMonoid.toList v).length = n <;>
        by_cases hlenw : (FreeMonoid.toList w).length = n <;>
          simp [hlenv, hlenw, coord, hv]
  have ht := LinearMap.congr_fun hmaps t
  by_cases hlen : (FreeMonoid.toList w).length = n <;>
    simpa [hlen, coord] using ht

theorem sub_component_wordDegreeLE
    {n : ℕ} (hn : 1 ≤ n) {t : T (ι := ι)}
    (ht : WordDegreeLE n t) :
    WordDegreeLE (n - 1) (t - tensorComponent n t) := by
  intro w hw
  simp only [map_sub, Finsupp.sub_apply] at hw
  rw [repr_tensorComponent_apply] at hw
  by_cases hlen : (FreeMonoid.toList w).length = n
  · simp [hlen] at hw
  · have hw' : (OrderedCyclic.wordBasis (ι := ι)).repr t w ≠ 0 := by
      simpa [hlen] using hw
    exact Nat.le_sub_one_of_lt (lt_of_le_of_ne (ht w hw') hlen)

theorem tensorMap_mem_tensorDegreeFiltration (n : ℕ) {t : T (ι := ι)}
    (ht : WordDegreeLE n t) :
    tensorMap ε t ∈ tensorDegreeFiltration E n := by
  let S : Submodule ℤ (T (ι := ι)) :=
    (tensorDegreeFiltration E n).comap (tensorMap ε).toLinearMap
  change t ∈ S
  apply Submodule.span_induction (p := fun x _ ↦ x ∈ S)
    (fun x hx ↦ ?_) S.zero_mem
    (fun _ _ _ _ hx hy ↦ S.add_mem hx hy)
    (fun z _ _ hx ↦ S.smul_mem z hx)
    ((OrderedCyclic.wordBasis (ι := ι)).mem_span_repr_support t)
  obtain ⟨w, hw, rfl⟩ := hx
  change tensorMap ε (OrderedCyclic.wordBasis (ι := ι) w) ∈
    tensorDegreeFiltration E n
  rw [OrderedCyclic.wordBasis_apply, tensorMap_lieWord]
  exact tensorWord_mem_tensorDegreeFiltration E
    (by simpa using ht w (Finsupp.mem_support_iff.mp hw))

/-- Filtered descent in Higgins's relation ideal, at an arbitrary degree bound. -/
theorem mem_higginsFiltration_of_mem_degree {u : TensorAlgebra ℤ E}
    {n : ℕ} (huDegree : u ∈ tensorDegreeFiltration E n) (m : ℕ)
    (hu : u ∈ higginsFiltration E m) :
    u ∈ higginsFiltration E n := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hmn : m ≤ n
      · exact higginsFiltration_mono E hmn hu
      · have hcomponent : tensorHomogeneousComponent E m u = 0 :=
          tensorHomogeneousComponent_eq_zero_of_mem_filtration E huDegree (by omega)
        have hprevious := mem_previousHigginsFiltration_of_component_eq_zero E m
          (⟨u, hu⟩ : higginsFiltration E m) hcomponent
        exact ih (m - 1) (by omega) hprevious

theorem rawCoefficient_component_eq_zero (π : E →ₗ[ℤ] D)
    (n : ℕ) (hn : n ≠ 1) (t : T (ι := ι)) :
    rawCoefficient ε π (tensorComponent n t) = 0 := by
  have hmaps : (rawCoefficient ε π).comp (tensorComponent n) = 0 := by
    apply (OrderedCyclic.wordBasis (ι := ι)).ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    change rawCoefficient ε π
      (tensorComponent n
        (OrderedCyclic.word (ι := ι) (FreeMonoid.toList w))) = 0
    by_cases hlen : (FreeMonoid.toList w).length = n
    · rw [← hlen, tensorComponent_orderedWord_same, rawCoefficient_word]
      cases hxs : FreeMonoid.toList w with
      | nil => simp
      | cons i xs =>
          cases xs with
          | nil => simp_all
          | cons j xs => simp
    · rw [tensorComponent_orderedWord_of_ne n _ hlen, map_zero]
  exact LinearMap.congr_fun hmaps t

/-- The filtered collection lemma: on normalized tensors, vanishing in the
universal enveloping algebra forces the distinguished degree-one coefficient
to vanish.  This is Higgins's leading-component descent, with the top
commutator lifted back to the diagonal presentation at each step. -/
theorem rawCoefficient_eq_zero_of_normalized_kernel
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) {s : T (ι := ι)} {n : ℕ}
    (hsnorm : OrderedCyclic.normalizer (ι := ι) s = s)
    (hsdeg : WordDegreeLE n s)
    (hseval : tensorToUEA ε s = 0) :
    rawCoefficient ε π s = 0 := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      have huJ : tensorMap ε s ∈ envelopingRelationIdeal E :=
        tensorMap_mem_envelopingRelationIdeal_of_tensorToUEA_eq_zero ε hseval
      obtain ⟨m, hum⟩ :=
        exists_higginsFiltration_of_mem_envelopingRelationIdeal E huJ
      have huDegree : tensorMap ε s ∈ tensorDegreeFiltration E n :=
        tensorMap_mem_tensorDegreeFiltration ε n hsdeg
      have huN : tensorMap ε s ∈ higginsFiltration E n :=
        mem_higginsFiltration_of_mem_degree huDegree m hum
      by_cases hn : n ≤ 1
      · have huOne : tensorMap ε s ∈ higginsFiltration E 1 :=
          higginsFiltration_mono E hn huN
        rw [higginsFiltration_one] at huOne
        exact rawCoefficient_eq_zero_of_tensorMap_eq_zero ε π huOne
      · have hn2 : 2 ≤ n := by omega
        have htopK :
            tensorComponent n (tensorMap ε s) ∈ tensorCommutatorIdeal E := by
          exact tensorHomogeneousComponent_mem_commutator_of_mem_higginsFiltration
            E huN
        let kE : tensorCommutatorIdeal E :=
          ⟨tensorComponent n (tensorMap ε s), htopK⟩
        obtain ⟨kP, hkP⟩ := commutatorIdeal_surjective ε hε kE
        let top : T (ι := ι) := tensorComponent n s
        have htopMap : tensorMap ε top = (kE : TensorAlgebra ℤ E) := by
          rw [tensorMap_homogeneousComponent]
        have hqMap : tensorMap ε (top - (kP : T (ι := ι))) = 0 := by
          rw [map_sub, htopMap, hkP, sub_self]
        have hqQ : top - (kP : T (ι := ι)) ∈
            AuxiliaryPresentation.relationIdeal ε := by
          rw [AuxiliaryPresentation.relationIdeal_eq_ker_tensorMap ε hε,
            RingHom.mem_ker]
          exact hqMap
        have hnormalQ :=
          normalizer_mem_relationIdeal_of_diagonal ε hdiag hqQ
        have htopNorm : OrderedCyclic.normalizer (ι := ι) top = top := by
          dsimp [top]
          rw [normalizer_homogeneousComponent, hsnorm]
        have hkNorm :
            OrderedCyclic.normalizer (ι := ι) (kP : T (ι := ι)) = 0 :=
          OrderedCyclic.normalizer_eq_zero_of_mem_commutatorIdeal kP.property
        have hnormalQeq :
            OrderedCyclic.normalizer (ι := ι)
                (top - (kP : T (ι := ι))) = top := by
          rw [map_sub, htopNorm, hkNorm, sub_zero]
        have htopQ : top ∈ AuxiliaryPresentation.relationIdeal ε := by
          rw [← hnormalQeq]
          exact hnormalQ
        have htopMapZero : tensorMap ε top = 0 := by
          rw [AuxiliaryPresentation.relationIdeal_eq_ker_tensorMap ε hε,
            RingHom.mem_ker] at htopQ
          exact htopQ
        let s' : T (ι := ι) := s - top
        have hs'deg : WordDegreeLE (n - 1) s' := by
          exact sub_component_wordDegreeLE (by omega) hsdeg
        have hs'norm : OrderedCyclic.normalizer (ι := ι) s' = s' := by
          dsimp [s']
          rw [map_sub, hsnorm, htopNorm]
        have htopEval : tensorToUEA ε top = 0 := by
          rw [tensorToUEA_eq_mk_comp_tensorMap, AlgHom.comp_apply,
            htopMapZero, map_zero]
        have hs'eval : tensorToUEA ε s' = 0 := by
          dsimp [s']
          rw [map_sub, hseval, htopEval, sub_zero]
        have hs'raw : rawCoefficient ε π s' = 0 :=
          ih (n - 1) (by omega) hs'norm hs'deg hs'eval
        have htopRaw : rawCoefficient ε π top = 0 := by
          dsimp [top]
          exact rawCoefficient_component_eq_zero ε π n (by omega) s
        dsimp [s'] at hs'raw
        rw [map_sub, htopRaw, sub_zero] at hs'raw
        exact hs'raw

/-! ### Ordered presentation words span the enveloping algebra -/

/-- A word in the chosen cyclic presentation generators, evaluated in `U(E)`. -/
def presentationWord (xs : List ι) : UEA ℤ E :=
  LieRings.PBW.word ℤ E
    (xs.map fun i ↦ ε (Finsupp.single i 1))

@[simp]
theorem presentationWord_nil : presentationWord ε ([] : List ι) = 1 := rfl

@[simp]
theorem presentationWord_cons (i : ι) (xs : List ι) :
    presentationWord ε (i :: xs) =
      UniversalEnvelopingAlgebra.ι ℤ (ε (Finsupp.single i 1)) *
        presentationWord ε xs := by
  simp [presentationWord, LieRings.PBW.word_cons]

theorem tensorToUEA_orderedWord (xs : List ι) :
    tensorToUEA ε (OrderedCyclic.word (ι := ι) xs) =
      presentationWord ε xs := by
  induction xs with
  | nil => rw [OrderedCyclic.word_nil, map_one, presentationWord_nil]
  | cons i xs ih =>
      rw [OrderedCyclic.word_cons, map_mul, tensorToUEA_ι, ih,
        presentationWord_cons]

/-- The span of presentation words of exactly a prescribed length. -/
def presentationWordSpan (n : ℕ) : Submodule ℤ (UEA ℤ E) :=
  Submodule.span ℤ
    {u | ∃ xs : List ι, xs.length = n ∧ presentationWord ε xs = u}

theorem presentationWord_mem_span (xs : List ι) :
    presentationWord ε xs ∈ presentationWordSpan ε xs.length :=
  Submodule.subset_span ⟨xs, rfl, rfl⟩

/-- Multiplication by an arbitrary presented generator raises exact word
length by one. -/
theorem iota_presentation_mul_mem_span (p : P (ι := ι))
    {u : UEA ℤ E} {n : ℕ} (hu : u ∈ presentationWordSpan ε n) :
    UniversalEnvelopingAlgebra.ι ℤ (ε p) * u ∈
      presentationWordSpan ε (n + 1) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨xs, hxs, rfl⟩ := hu
      induction p using Finsupp.induction with
      | zero => simp
      | @single_add i z p hi hz ih =>
          rw [map_add, map_add, add_mul]
          apply (presentationWordSpan ε (n + 1)).add_mem
          · have hsingle : Finsupp.single i z =
                z • Finsupp.single i (1 : ℤ) := by
              ext j
              by_cases hji : j = i <;> subst_vars <;> simp
            rw [hsingle, map_smul, map_smul, smul_mul_assoc,
              ← presentationWord_cons]
            exact (presentationWordSpan ε (n + 1)).smul_mem z
              (by
                apply Submodule.subset_span
                exact ⟨i :: xs, by simp [hxs], rfl⟩)
          · exact ih
  | zero => simp
  | add a b _ _ ha hb => simpa [mul_add] using
      (presentationWordSpan ε (n + 1)).add_mem ha hb
  | smul z a _ ha =>
      rw [mul_smul_comm]
      exact (presentationWordSpan ε (n + 1)).smul_mem z ha

/-- Every ordinary enveloping word expands into presentation words of the
same length. -/
theorem ueaWord_mem_presentationWordSpan (hε : Function.Surjective ε)
    (xs : List E) :
    LieRings.PBW.word ℤ E xs ∈ presentationWordSpan ε xs.length := by
  induction xs with
  | nil => exact presentationWord_mem_span ε []
  | cons x xs ih =>
      obtain ⟨p, rfl⟩ := hε x
      rw [LieRings.PBW.word_cons]
      simpa using iota_presentation_mul_mem_span ε p ih

/-- The unrestricted span of presentation words. -/
def presentationWordTotalSpan : Submodule ℤ (UEA ℤ E) :=
  Submodule.span ℤ {u | ∃ xs : List ι, presentationWord ε xs = u}

theorem presentationWordSpan_le_totalSpan (n : ℕ) :
    presentationWordSpan ε n ≤ presentationWordTotalSpan ε := by
  apply Submodule.span_le.2
  rintro u ⟨xs, _, rfl⟩
  exact Submodule.subset_span ⟨xs, rfl⟩

theorem presentationWordTotalSpan_mul_mem {a b : UEA ℤ E}
    (ha : a ∈ presentationWordTotalSpan ε)
    (hb : b ∈ presentationWordTotalSpan ε) :
    a * b ∈ presentationWordTotalSpan ε := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨as, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨bs, rfl⟩ := hb
          apply Submodule.subset_span
          refine ⟨as ++ bs, ?_⟩
          simp [presentationWord, LieRings.PBW.word_append]
      | zero => simp
      | add b c _ _ hb hc => simpa [mul_add] using
          (presentationWordTotalSpan ε).add_mem hb hc
      | smul z b _ hb =>
          rw [mul_smul_comm]
          exact (presentationWordTotalSpan ε).smul_mem z hb
  | zero => simp
  | add a c _ _ ha hc => simpa [add_mul] using
      (presentationWordTotalSpan ε).add_mem ha hc
  | smul z a _ ha =>
      rw [smul_mul_assoc]
      exact (presentationWordTotalSpan ε).smul_mem z ha

theorem presentationWordTotalSpan_eq_top (hε : Function.Surjective ε) :
    presentationWordTotalSpan ε = ⊤ := by
  apply top_unique
  intro u hu
  clear hu
  induction u using UEA.induction ℤ E with
  | algebraMap z =>
      rw [← mul_one (algebraMap ℤ (UEA ℤ E) z), ← Algebra.smul_def,
        ← presentationWord_nil ε]
      exact (presentationWordTotalSpan ε).smul_mem z
        (Submodule.subset_span ⟨[], rfl⟩)
  | ι x =>
      have hx := ueaWord_mem_presentationWordSpan ε hε [x]
      exact presentationWordSpan_le_totalSpan ε 1 (by simpa using hx)
  | mul a b ha hb => exact presentationWordTotalSpan_mul_mem ε ha hb
  | add a b ha hb => exact (presentationWordTotalSpan ε).add_mem ha hb

/-- Ordered collection of a surjective cyclic presentation spans `U(E)`.
This is the elementary (surjectivity) half of PBW; torsion in the presented
group is harmless. -/
theorem collectedMap_surjective (hε : Function.Surjective ε) :
    Function.Surjective (collectedMap ε) := by
  let Q : ℕ → Prop := fun n ↦ ∀ xs : List ι, xs.length = n →
    presentationWord ε xs ∈ LinearMap.range (collectedMap ε)
  have hQ : ∀ n, Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro xs hxs
        subst n
        cases xs with
        | nil =>
            refine ⟨1, ?_⟩
            change tensorToUEA ε
                (OrderedCyclic.normalizer (ι := ι) 1) = 1
            rw [show (1 : T (ι := ι)) =
                OrderedCyclic.word (ι := ι) [] by
                  rw [OrderedCyclic.word_nil],
              OrderedCyclic.normalizer_word]
            simpa using tensorToUEA_orderedWord ε ([] : List ι)
        | cons i is =>
            let sorted : List ι :=
              (((i :: is : List ι) : Multiset ι).sort (· ≤ ·))
            have hsorted_pairwise : sorted.Pairwise (· ≤ ·) :=
              Multiset.pairwise_sort _ _
            have hsorted_mem : presentationWord ε sorted ∈
                LinearMap.range (collectedMap ε) := by
              refine ⟨OrderedCyclic.word (ι := ι) sorted, ?_⟩
              change tensorToUEA ε
                  (OrderedCyclic.normalizer (ι := ι)
                    (OrderedCyclic.word (ι := ι) sorted)) =
                presentationWord ε sorted
              rw [OrderedCyclic.normalizer_word]
              have hsort : ((sorted : Multiset ι).sort (· ≤ ·)) = sorted := by
                simpa using List.mergeSort_eq_self (· ≤ ·) hsorted_pairwise
              rw [hsort, tensorToUEA_orderedWord]
            have hperm : (i :: is).Perm sorted := by
              exact Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _).symm
            have hdiff : presentationWord ε (i :: is) -
                presentationWord ε sorted ∈
                  LieRings.PBW.wordFiltration ℤ E is.length := by
              have hp := LieRings.PBW.word_sub_word_of_perm ℤ E
                (hperm.map fun j ↦ ε (Finsupp.single j 1))
              simpa [presentationWord] using hp
            have hfiltration : LieRings.PBW.wordFiltration ℤ E is.length ≤
                LinearMap.range (collectedMap ε) := by
              apply Submodule.span_le.2
              rintro u ⟨ys, hys, rfl⟩
              have hyspan := ueaWord_mem_presentationWordSpan ε hε ys
              refine Submodule.span_induction (p := fun u _ ↦
                  u ∈ LinearMap.range (collectedMap ε)) ?_ ?_ ?_ ?_ hyspan
              · rintro u ⟨js, hjs, rfl⟩
                have hjle : js.length ≤ is.length := hjs.trans_le hys
                have hjlt : js.length < (i :: is).length := by
                  simpa using hjle
                exact ih js.length hjlt js rfl
              · exact Submodule.zero_mem _
              · exact fun _ _ _ _ hu hv => Submodule.add_mem _ hu hv
              · exact fun z _ _ hu => Submodule.smul_mem _ z hu
            have hdiff_mem := hfiltration hdiff
            rw [show presentationWord ε (i :: is) =
                (presentationWord ε (i :: is) - presentationWord ε sorted) +
                  presentationWord ε sorted by abel]
            exact Submodule.add_mem _ hdiff_mem hsorted_mem
  have htotal : presentationWordTotalSpan ε ≤
      LinearMap.range (collectedMap ε) := by
    apply Submodule.span_le.2
    rintro u ⟨xs, rfl⟩
    exact hQ xs.length xs rfl
  have htop : (⊤ : Submodule ℤ (UEA ℤ E)) ≤
      LinearMap.range (collectedMap ε) := by
    rw [← presentationWordTotalSpan_eq_top ε hε]
    exact htotal
  exact LinearMap.range_eq_top.mp (top_unique htop)

/-! ### The coefficient on the universal enveloping algebra -/

theorem rawCoefficient_eq_zero_of_collectedMap_eq_zero
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) {t : T (ι := ι)}
    (ht : collectedMap ε t = 0) :
    rawCoefficient ε π t = 0 := by
  let s := OrderedCyclic.normalizer (ι := ι) t
  obtain ⟨n, hn⟩ := exists_wordDegreeLE s
  have hsnorm : OrderedCyclic.normalizer (ι := ι) s = s := by
    exact normalizer_idempotent t
  have hseval : tensorToUEA ε s = 0 := by
    exact ht
  have hsraw := rawCoefficient_eq_zero_of_normalized_kernel ε hε hdiag π
    hsnorm hn hseval
  rw [rawCoefficient_normalizer] at hsraw
  exact hsraw

theorem ker_collectedMap_le_ker_rawCoefficient
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) :
    LinearMap.ker (collectedMap ε) ≤
      LinearMap.ker (rawCoefficient ε π) := by
  intro t ht
  rw [LinearMap.mem_ker] at ht ⊢
  exact rawCoefficient_eq_zero_of_collectedMap_eq_zero ε hε hdiag π ht

/-- The PBW degree-one coefficient on the enveloping algebra. -/
def ueaCoefficient
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) : UEA ℤ E →ₗ[ℤ] D :=
  ((LinearMap.ker (collectedMap ε)).liftQ (rawCoefficient ε π)
      (ker_collectedMap_le_ker_rawCoefficient ε hε hdiag π)).comp
    (((collectedMap ε).quotKerEquivOfSurjective
      (collectedMap_surjective ε hε)).symm.toLinearMap)

@[simp]
theorem ueaCoefficient_collectedMap
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) (t : T (ι := ι)) :
    ueaCoefficient ε hε hdiag π (collectedMap ε t) =
      rawCoefficient ε π t := by
  simp [ueaCoefficient,
    LinearMap.quotKerEquivOfSurjective_symm_apply]

@[simp]
theorem ueaCoefficient_iota
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) (p : P (ι := ι)) :
    ueaCoefficient ε hε hdiag π
        (UniversalEnvelopingAlgebra.ι ℤ (ε p)) = π (ε p) := by
  have hnormal : OrderedCyclic.normalizer (ι := ι)
      (TensorAlgebra.ι ℤ p) = TensorAlgebra.ι ℤ p := by
    induction p using Finsupp.induction with
    | zero => simp
    | @single_add i z p hi hz ih =>
        rw [map_add, map_add, ih]
        congr 1
        have hsingle : Finsupp.single i z =
            z • Finsupp.single i (1 : ℤ) := by
          ext j
          by_cases hji : j = i <;> subst_vars <;> simp
        rw [hsingle, map_smul, map_smul]
        congr 1
        rw [← OrderedCyclic.word_singleton]
        rw [OrderedCyclic.normalizer_word]
        simp
  have hcollected : collectedMap ε (TensorAlgebra.ι ℤ p) =
      UniversalEnvelopingAlgebra.ι ℤ (ε p) := by
    change tensorToUEA ε
      (OrderedCyclic.normalizer (ι := ι) (TensorAlgebra.ι ℤ p)) = _
    rw [hnormal]
    exact tensorToUEA_ι ε p
  rw [← hcollected, ueaCoefficient_collectedMap, rawCoefficient_ι]

@[simp]
theorem ueaCoefficient_iota_of_surjective
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) (e : E) :
    ueaCoefficient ε hε hdiag π
        (UniversalEnvelopingAlgebra.ι ℤ e) = π e := by
  obtain ⟨p, rfl⟩ := hε e
  exact ueaCoefficient_iota ε hε hdiag π p

/-- If `i₀` is the first presentation coordinate, then the distinguished
coefficient of left multiplication by its generator is its scalar
coefficient times augmentation. -/
theorem ueaCoefficient_iota_distinguished_mul_collectedMap
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) (i₀ : ι) (hi₀ : ∀ i, i₀ ≤ i)
    (t : T (ι := ι)) :
    ueaCoefficient ε hε hdiag π
        (UniversalEnvelopingAlgebra.ι ℤ
          (ε (Finsupp.single i₀ 1)) * collectedMap ε t) =
      UEA.augmentation ℤ E (collectedMap ε t) •
        π (ε (Finsupp.single i₀ 1)) := by
  let S : Submodule ℤ (T (ι := ι)) :=
    Submodule.span ℤ (Set.range (OrderedCyclic.wordBasis (ι := ι)))
  have hspan : S = ⊤ := by
    exact (OrderedCyclic.wordBasis (ι := ι)).span_eq
  suffices ht : t ∈ S by
    induction ht using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨w, rfl⟩ := hx
        let xs := FreeMonoid.toList w
        change ueaCoefficient ε hε hdiag π
            (UniversalEnvelopingAlgebra.ι ℤ
              (ε (Finsupp.single i₀ 1)) *
                collectedMap ε (OrderedCyclic.word (ι := ι) xs)) =
          UEA.augmentation ℤ E
              (collectedMap ε (OrderedCyclic.word (ι := ι) xs)) •
            π (ε (Finsupp.single i₀ 1))
        by_cases hxs : xs = []
        · rw [hxs]
          change ueaCoefficient ε hε hdiag π
              (UniversalEnvelopingAlgebra.ι ℤ
                  (ε (Finsupp.single i₀ 1)) *
                tensorToUEA ε
                  (OrderedCyclic.normalizer (ι := ι)
                    (OrderedCyclic.word (ι := ι) []))) =
            UEA.augmentation ℤ E
                (tensorToUEA ε
                  (OrderedCyclic.normalizer (ι := ι)
                    (OrderedCyclic.word (ι := ι) []))) • _
          rw [OrderedCyclic.normalizer_word, tensorToUEA_orderedWord,
            Multiset.coe_nil, Multiset.sort_zero, presentationWord_nil, mul_one]
          rw [ueaCoefficient_iota]
          simp
        · let ys : List ι := ((xs : Multiset ι).sort (· ≤ ·))
          have hysPairwise : ys.Pairwise (· ≤ ·) :=
            Multiset.pairwise_sort _ _
          have hys : ys ≠ [] := by
            intro hy
            apply hxs
            apply List.length_eq_zero_iff.mp
            rw [← show ys.length = xs.length by simp [ys], hy]
            simp
          have hiPairwise : (i₀ :: ys).Pairwise (· ≤ ·) := by
            simp only [List.pairwise_cons]
            exact ⟨fun j _ ↦ hi₀ j, hysPairwise⟩
          have hprod :
              UniversalEnvelopingAlgebra.ι ℤ
                  (ε (Finsupp.single i₀ 1)) *
                collectedMap ε (OrderedCyclic.word (ι := ι) xs) =
              collectedMap ε
                (OrderedCyclic.word (ι := ι) (i₀ :: ys)) := by
            change UniversalEnvelopingAlgebra.ι ℤ
                  (ε (Finsupp.single i₀ 1)) *
                tensorToUEA ε
                  (OrderedCyclic.normalizer (ι := ι)
                    (OrderedCyclic.word (ι := ι) xs)) =
              tensorToUEA ε
                (OrderedCyclic.normalizer (ι := ι)
                  (OrderedCyclic.word (ι := ι) (i₀ :: ys)))
            rw [OrderedCyclic.normalizer_word,
              tensorToUEA_orderedWord]
            change UniversalEnvelopingAlgebra.ι ℤ
                  (ε (Finsupp.single i₀ 1)) * presentationWord ε ys = _
            have hsortCons :
                (((i₀ :: ys : List ι) : Multiset ι).sort (· ≤ ·)) =
                  i₀ :: ys := by
              simpa using List.mergeSort_eq_self (· ≤ ·) hiPairwise
            rw [OrderedCyclic.normalizer_word, hsortCons,
              tensorToUEA_orderedWord,
              presentationWord_cons]
          rw [hprod, ueaCoefficient_collectedMap, rawCoefficient_word]
          have hysDef : ((xs : Multiset ι).sort (· ≤ ·)) = ys := rfl
          rcases ys with _ | ⟨j, ys⟩
          · exact (hys rfl).elim
          change 0 = UEA.augmentation ℤ E
              (collectedMap ε (OrderedCyclic.word (ι := ι) xs)) •
                π (ε (Finsupp.single i₀ 1))
          change 0 = UEA.augmentation ℤ E
              (tensorToUEA ε
                (OrderedCyclic.normalizer (ι := ι)
                  (OrderedCyclic.word (ι := ι) xs))) • _
          rw [OrderedCyclic.normalizer_word,
            tensorToUEA_orderedWord]
          rw [hysDef]
          change 0 = UEA.augmentation ℤ E
              (presentationWord ε (j :: ys)) • _
          rw [presentationWord_cons, map_mul, UEA.augmentation_ι,
            zero_mul, zero_smul]
    | zero => simp
    | add x y _ _ hx hy =>
        simpa [mul_add, add_smul] using congrArg₂ (· + ·) hx hy
    | smul z x _ hx =>
        rw [map_smul, mul_smul_comm, map_smul, map_smul, hx, smul_assoc]
  rw [hspan]
  exact Submodule.mem_top

/-- A central Lie generator commutes with every element of the enveloping
algebra. -/
theorem iota_mem_center_commutes
    {D₀ : LieIdeal ℤ E} (hcentral : D₀ ≤ LieAlgebra.center ℤ E)
    (d : D₀) (u : UEA ℤ E) :
    UniversalEnvelopingAlgebra.ι ℤ (d : E) * u =
      u * UniversalEnvelopingAlgebra.ι ℤ (d : E) := by
  induction u using UEA.induction ℤ E with
  | algebraMap z => exact (Algebra.commutes z
      (UniversalEnvelopingAlgebra.ι ℤ (d : E))).symm
  | ι x =>
      have hzero : ⁅x, (d : E)⁆ = 0 :=
        (LieModule.mem_maxTrivSubmodule ℤ E E (d : E)).mp
          (hcentral d.property) x
      have hcomm : UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ (d : E) =
          UniversalEnvelopingAlgebra.ι ℤ (d : E) *
            UniversalEnvelopingAlgebra.ι ℤ x := by
        apply sub_eq_zero.mp
        rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie,
          hzero, map_zero]
      exact hcomm.symm
  | mul a b ha hb =>
      calc
        UniversalEnvelopingAlgebra.ι ℤ (d : E) * (a * b) =
            (UniversalEnvelopingAlgebra.ι ℤ (d : E) * a) * b :=
              (mul_assoc _ _ _).symm
        _ = (a * UniversalEnvelopingAlgebra.ι ℤ (d : E)) * b := by rw [ha]
        _ = a * (UniversalEnvelopingAlgebra.ι ℤ (d : E) * b) :=
              mul_assoc _ _ _
        _ = a * (b * UniversalEnvelopingAlgebra.ι ℤ (d : E)) := by rw [hb]
        _ = (a * b) * UniversalEnvelopingAlgebra.ι ℤ (d : E) :=
              (mul_assoc _ _ _).symm
  | add a b ha hb =>
      rw [mul_add, add_mul]
      exact congrArg₂ (· + ·) ha hb

/-- Left multiplication by an element of the distinguished cyclic summand
has zero distinguished coefficient on the augmentation ideal. -/
theorem ueaCoefficient_iota_distinguished_mul_eq_zero
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) (i₀ : ι) (hi₀ : ∀ i, i₀ ≤ i)
    {D₀ : LieIdeal ℤ E}
    (hgen : ∀ d : D₀, ∃ z : ℤ,
      (d : E) = z • ε (Finsupp.single i₀ 1))
    (d : D₀) (v : UEA.augmentationIdeal ℤ E) :
    ueaCoefficient ε hε hdiag π
        (UniversalEnvelopingAlgebra.ι ℤ (d : E) * (v : UEA ℤ E)) = 0 := by
  obtain ⟨z, hz⟩ := hgen d
  obtain ⟨t, ht⟩ := collectedMap_surjective ε hε (v : UEA ℤ E)
  have haug : UEA.augmentation ℤ E (collectedMap ε t) = 0 := by
    rw [ht]
    exact v.property
  rw [hz, map_smul, smul_mul_assoc, map_smul]
  rw [← ht]
  rw [ueaCoefficient_iota_distinguished_mul_collectedMap ε hε hdiag π i₀ hi₀]
  rw [haug, zero_smul, smul_zero]

/-- The distinguished coefficient annihilates the product of the ideal
generated by a central cyclic summand with the augmentation ideal. -/
theorem ueaCoefficient_productIdeal_eq_zero
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) (i₀ : ι) (hi₀ : ∀ i, i₀ ≤ i)
    (D₀ : LieIdeal ℤ E)
    (hcentral : D₀ ≤ LieAlgebra.center ℤ E)
    (hgen : ∀ d : D₀, ∃ z : ℤ,
      (d : E) = z • ε (Finsupp.single i₀ 1))
    {x : UEA ℤ E} (hx : x ∈ CentralDerivative.productIdeal E D₀) :
    ueaCoefficient ε hε hdiag π x = 0 := by
  let c := ueaCoefficient ε hε hdiag π
  have hbase (d : D₀) (v : UEA ℤ E)
      (hv : v ∈ UEA.augmentationIdeal ℤ E) :
      c (UniversalEnvelopingAlgebra.ι ℤ (d : E) * v) = 0 := by
    exact ueaCoefficient_iota_distinguished_mul_eq_zero ε hε hdiag π
      i₀ hi₀ hgen d ⟨v, hv⟩
  have hideal {a : UEA ℤ E}
      (ha : a ∈ UEA.idealOfLieIdeal ℤ E D₀) :
      ∀ l b : UEA ℤ E, b ∈ UEA.augmentationIdeal ℤ E →
        c (l * a * b) = 0 := by
    change a ∈ TwoSidedIdeal.span
      (Set.range fun d : D₀ ↦ UniversalEnvelopingAlgebra.ι ℤ (d : E)) at ha
    induction ha using TwoSidedIdeal.span_induction with
    | mem a ha =>
        obtain ⟨d, rfl⟩ := ha
        intro l b hb
        have hcomm := iota_mem_center_commutes hcentral d l
        change c (l * UniversalEnvelopingAlgebra.ι ℤ (d : E) * b) = 0
        rw [← hcomm, mul_assoc]
        exact hbase d (l * b)
          ((UEA.augmentationIdeal ℤ E).mul_mem_left l hb)
    | zero => intro l b hb; simp
    | add a a' _ _ ha ha' =>
        intro l b hb
        rw [mul_add, add_mul, map_add, ha l b hb, ha' l b hb, add_zero]
    | neg a _ ha =>
        intro l b hb
        rw [mul_neg, neg_mul, map_neg, ha l b hb, neg_zero]
    | left_absorb r a _ ha =>
        intro l b hb
        simpa only [mul_assoc] using ha (l * r) b hb
    | right_absorb r a _ ha =>
        intro l b hb
        simpa only [mul_assoc] using ha l (r * b)
          ((UEA.augmentationIdeal ℤ E).mul_mem_left r hb)
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha b hb
    change c (a * b) = 0
    simpa using hideal ha 1 b hb
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

/-- Restriction of the PBW coefficient to the augmentation ideal. -/
def augmentationCoefficient
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) :
    CentralDerivative.Augmentation E →ₗ[ℤ] D where
  toFun v := ueaCoefficient ε hε hdiag π (v : UEA ℤ E)
  map_add' v w := by simp
  map_smul' z v := by
    change ueaCoefficient ε hε hdiag π
        (z • (v : UEA ℤ E)) =
      z • ueaCoefficient ε hε hdiag π (v : UEA ℤ E)
    exact (ueaCoefficient ε hε hdiag π).map_smul z (v : UEA ℤ E)

@[simp]
theorem augmentationCoefficient_apply
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) (v : CentralDerivative.Augmentation E) :
    augmentationCoefficient ε hε hdiag π v =
      ueaCoefficient ε hε hdiag π (v : UEA ℤ E) := rfl

/-- The distinguished PBW coefficient descended to the central derivative
module. -/
def derivativeCoefficient
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) (i₀ : ι) (hi₀ : ∀ i, i₀ ≤ i)
    (D₀ : LieIdeal ℤ E)
    (hcentral : D₀ ≤ LieAlgebra.center ℤ E)
    (hgen : ∀ d : D₀, ∃ z : ℤ,
      (d : E) = z • ε (Finsupp.single i₀ 1)) :
    CentralDerivative.Derivative E D₀ →ₗ[ℤ] D :=
  (CentralDerivative.denominator E D₀).liftQ
    (augmentationCoefficient ε hε hdiag π) (by
      intro v hv
      rw [LinearMap.mem_ker]
      exact ueaCoefficient_productIdeal_eq_zero ε hε hdiag π i₀ hi₀
        D₀ hcentral hgen hv)

@[simp]
theorem derivativeCoefficient_bar
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D) (i₀ : ι) (hi₀ : ∀ i, i₀ ≤ i)
    (D₀ : LieIdeal ℤ E)
    (hcentral : D₀ ≤ LieAlgebra.center ℤ E)
    (hgen : ∀ d : D₀, ∃ z : ℤ,
      (d : E) = z • ε (Finsupp.single i₀ 1))
    (e : E) :
    derivativeCoefficient ε hε hdiag π i₀ hi₀ D₀ hcentral hgen
        (CentralDerivative.bar E D₀ e) = π e := by
  rw [CentralDerivative.bar_apply]
  rw [derivativeCoefficient]
  change augmentationCoefficient ε hε hdiag π
      (CentralDerivative.toAugmentation E e) = π e
  exact ueaCoefficient_iota_of_surjective ε hε hdiag π e

/-- Directly consumable presentation-level form of the central-module PBW
lemma. -/
theorem exists_derivative_retraction_of_diagonal_presentation
    {D₀ : LieIdeal ℤ E}
    (hε : Function.Surjective ε)
    (hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0)
    (π : E →ₗ[ℤ] D₀) (i₀ : ι) (hi₀ : ∀ i, i₀ ≤ i)
    (hcentral : D₀ ≤ LieAlgebra.center ℤ E)
    (hgen : ∀ d : D₀, ∃ z : ℤ,
      (d : E) = z • ε (Finsupp.single i₀ 1))
    (hπ : ∀ d : D₀, π (d : E) = d) :
    ∃ coefficient : CentralDerivative.Derivative E D₀ →ₗ[ℤ] D₀,
      ∀ d : D₀, coefficient (CentralDerivative.bar E D₀ (d : E)) = d := by
  let coefficient :=
    derivativeCoefficient ε hε hdiag π i₀ hi₀ D₀ hcentral hgen
  refine ⟨coefficient, fun d ↦ ?_⟩
  rw [show coefficient (CentralDerivative.bar E D₀ (d : E)) =
      π (d : E) by
        exact derivativeCoefficient_bar ε hε hdiag π i₀ hi₀
          D₀ hcentral hgen (d : E), hπ]

/-! ### Construction from an aligned additive splitting -/

set_option maxHeartbeats 1200000 in
/-- **Central-module PBW coefficient from an aligned split.**  This is the
public form used by the cyclic pushout: the first additive coordinate is the
central cyclic ideal, while the finitely generated complement is decomposed
by the structure theorem for finitely generated Abelian groups. -/
theorem exists_derivative_retraction_of_aligned_split
    {D₀ : LieIdeal ℤ E} [Finite D₀] [IsAddCyclic D₀]
    {H : Type u} [AddCommGroup H] [Module.Finite ℤ H]
    (split : E ≃ₗ[ℤ] D₀ × H)
    (hsplit : ∀ d : D₀, split (d : E) = (d, 0))
    (hcentral : D₀ ≤ LieAlgebra.center ℤ E) :
    ∃ coefficient : CentralDerivative.Derivative E D₀ →ₗ[ℤ] D₀,
      ∀ d : D₀,
        coefficient (CentralDerivative.bar E D₀ (d : E)) = d := by
  obtain ⟨n, τ, fintypeτ, p, hp, exponents, ⟨eH⟩⟩ :=
    Module.equiv_free_prod_directSum ℤ H
  letI : Fintype τ := fintypeτ
  letI : DecidableEq τ := Classical.decEq τ
  let J : Fin 2 → Type := Fin.cases (Fin n) (fun _ ↦ τ)
  let B : (j : Fin 2) → J j → Type := fun j ↦
    Fin.cases (fun _ : Fin n ↦ ℤ)
      (fun _ : Fin 1 ↦ fun i : τ ↦
        ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ)) j
  letI : ∀ j, ∀ i : J j, AddCommGroup (B j i) := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · intro i
      change AddCommGroup ℤ
      exact inferInstance
    · intro i
      change AddCommGroup
        (ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ))
      exact inferInstance
  have hcyclicB : ∀ ji : (j : Fin 2) × J j,
      IsAddCyclic (B ji.1 ji.2) := by
    intro ji
    rcases ji with ⟨j, i⟩
    fin_cases j
    · change IsAddCyclic ℤ
      exact inferInstance
    · change IsAddCyclic
        (ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ))
      exact isAddCyclic_intQuotient
        (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ)
  let κ₀ := (j : Fin 2) × J j
  let κ := ULift.{u} κ₀
  letI : DecidableEq κ := Classical.decEq κ
  letI : LinearOrder κ := WellOrderingRel.isWellOrder.linearOrder
  let BU : κ → Type u := fun ji ↦
    ULift.{u} (B ji.down.1 ji.down.2)
  letI : ∀ ji, AddCommGroup (BU ji) := fun _ ↦ inferInstance
  have hcyclicBU : ∀ ji, IsAddCyclic (BU ji) := by
    intro ji
    exact (ULift.moduleEquiv
      (R := ℤ) (M := B ji.down.1 ji.down.2)).toAddEquiv.isAddCyclic.mpr
        (hcyclicB ji.down)
  let eHSigma : (DirectSum κ₀ fun ji ↦ B ji.1 ji.2) ≃ₗ[ℤ]
      (Fin n →₀ ℤ) × DirectSum τ
        (fun i ↦ ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ)) := by
    dsimp only [κ₀, J, B]
    exact (DirectSum.sigmaLcurryEquiv ℤ).trans <|
      (DirectSum.linearEquivFunOnFintype ℤ (Fin 2)
        (fun j ↦ DirectSum (Fin.cases (Fin n) (fun _ ↦ τ) j)
          (fun i ↦ Fin.cases (fun _ : Fin n ↦ ℤ)
            (fun _ : Fin 1 ↦ fun i : τ ↦
              ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ)) j i))).trans <|
        (LinearEquiv.piFinTwo ℤ
          (fun j ↦ DirectSum (Fin.cases (Fin n) (fun _ ↦ τ) j)
            (fun i ↦ Fin.cases (fun _ : Fin n ↦ ℤ)
              (fun _ : Fin 1 ↦ fun i : τ ↦
                ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ)) j i))).trans <|
          LinearEquiv.prodCongr
            (finsuppLEquivDirectSum ℤ ℤ (Fin n)).symm
            (LinearEquiv.refl ℤ (DirectSum τ
              (fun i ↦ ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ))))
  let eReindex : (DirectSum κ BU) ≃ₗ[ℤ]
      DirectSum κ₀ (fun ji ↦ ULift.{u} (B ji.1 ji.2)) := by
    dsimp only [κ, BU]
    exact DirectSum.lequivCongrLeft ℤ Equiv.ulift
  let eHTail : (DirectSum κ BU) ≃ₗ[ℤ] H :=
    eReindex.trans <| (DirectSum.congrLinearEquiv
      (fun ji ↦ ULift.moduleEquiv (R := ℤ) (M := B ji.1 ji.2))).trans <|
        eHSigma.trans eH.symm
  let A : WithBot κ → Type u := fun i ↦
    WithBot.recBotCoe D₀ BU i
  letI : ∀ i, AddCommGroup (A i) := by
    intro i
    induction i using WithBot.recBotCoe with
    | bot =>
        change AddCommGroup D₀
        exact inferInstance
    | coe ji =>
        change AddCommGroup (BU ji)
        exact inferInstance
  let cyclicA : ∀ i, IsAddCyclic (A i) := by
    intro i
    induction i using WithBot.recBotCoe with
    | bot =>
        change IsAddCyclic D₀
        exact inferInstance
    | coe ji =>
        change IsAddCyclic (BU ji)
        exact hcyclicBU ji
  let eTotal : DirectSum (WithBot κ) A ≃ₗ[ℤ] D₀ × H :=
    (DirectSum.lequivProdDirectSum ℤ (α := A)).trans <|
      LinearEquiv.prodCongr (LinearEquiv.refl ℤ D₀) eHTail
  let eE : DirectSum (WithBot κ) A ≃ₗ[ℤ] E := eTotal.trans split.symm
  let ε : (WithBot κ →₀ ℤ) →ₗ[ℤ] E :=
    ExternalCyclic.presentation A cyclicA eE
  have hε : Function.Surjective ε :=
    ExternalCyclic.presentation_surjective A cyclicA eE
  have hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0 := by
    intro q i
    rw [show q.1 i • Finsupp.single i 1 = Finsupp.single i (q.1 i) by
      ext j
      by_cases hji : j = i <;> simp [hji]]
    change eE (ExternalCyclic.toDirectSum A cyclicA
      (Finsupp.single i (q.1 i))) = 0
    rw [← map_zero eE]
    apply congrArg eE
    apply DFinsupp.ext
    intro j
    by_cases hji : j = i
    · subst j
      simpa [ExternalCyclic.toDirectSum_apply] using
        ExternalCyclic.ker_component A cyclicA eE q i
    · simp [ExternalCyclic.toDirectSum_apply, hji]
  let π : E →ₗ[ℤ] D₀ :=
    (LinearMap.fst ℤ D₀ H).comp split.toLinearMap
  have hπ : ∀ d : D₀, π (d : E) = d := by
    intro d
    simp [π, hsplit d]
  let gA : A (⊥ : WithBot κ) :=
    ExternalCyclic.generator A cyclicA (⊥ : WithBot κ)
  let g : D₀ := gA
  have htoDirectSum :
      ExternalCyclic.toDirectSum A cyclicA
          (Finsupp.single (⊥ : WithBot κ) 1) =
        DirectSum.of A (⊥ : WithBot κ) gA := by
    apply DFinsupp.ext
    intro i
    by_cases hi : i = ⊥
    · subst i
      simp [ExternalCyclic.toDirectSum_apply, gA]
    · have hbotne : (⊥ : WithBot κ) ≠ i := Ne.symm hi
      simp [ExternalCyclic.toDirectSum_apply, DirectSum.of_apply, hi, hbotne]
  have hbot : ε (Finsupp.single (⊥ : WithBot κ) 1) =
      (g : E) := by
    apply split.injective
    rw [hsplit g]
    rw [show ε (Finsupp.single (⊥ : WithBot κ) 1) =
        eE (ExternalCyclic.toDirectSum A cyclicA
          (Finsupp.single (⊥ : WithBot κ) 1)) by rfl]
    rw [htoDirectSum]
    change split (split.symm (eTotal
      (DirectSum.of A (⊥ : WithBot κ) gA))) = (g, 0)
    rw [split.apply_symm_apply]
    change ((LinearEquiv.refl ℤ D₀).prodCongr eHTail)
        (DirectSum.lequivProdDirectSum ℤ
          (DirectSum.of A (⊥ : WithBot κ) gA)) = (g, 0)
    have hprod :
        DirectSum.lequivProdDirectSum ℤ
            (DirectSum.of A (⊥ : WithBot κ) gA) = (gA, 0) := by
      rw [DirectSum.lequivProdDirectSum_apply]
      change DirectSum.addEquivProdDirectSum
          (DirectSum.of A (⊥ : WithBot κ) gA) = (gA, 0)
      rw [DirectSum.addEquivProdDirectSum_apply]
      apply Prod.ext
      · exact DirectSum.of_eq_same _ _
      · apply DFinsupp.ext
        intro i
        exact DirectSum.of_eq_of_ne (⊥ : WithBot κ) (some i) gA (by simp)
    rw [hprod]
    simp [g]
    rfl
  have hgen : ∀ d : D₀, ∃ z : ℤ,
      (d : E) = z • ε (Finsupp.single (⊥ : WithBot κ) 1) := by
    intro d
    obtain ⟨z, hz⟩ := ExternalCyclic.generator_surjective A cyclicA
      (⊥ : WithBot κ) d
    refine ⟨z, ?_⟩
    rw [hbot]
    have hz' : z • g = d := by simpa only [g, gA, A] using hz
    simpa using congrArg Subtype.val hz'.symm
  exact exists_derivative_retraction_of_diagonal_presentation ε hε hdiag π
    (⊥ : WithBot κ) (fun _ ↦ bot_le) hcentral hgen hπ

end DistinguishedPBW

end

end LieRings.Plotkin
