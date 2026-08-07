import LieRings.PBW.HigginsCyclic
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Directed-limit vanishing of Higgins's obstruction

Every Abelian group is the directed union of its finitely generated subgroups.  This file proves
that every finite tensor/relation calculation defining Higgins's obstruction occurs in one such
subgroup.  The cyclic-sum theorem and the structure theorem for finitely generated modules over
`ℤ` then imply that the obstruction vanishes for every Abelian group.
-/

namespace LieRings.PBW.Higgins

universe u v w

noncomputable section

namespace AuxiliaryPresentation

variable {M : Type u} [AddCommGroup M]
variable {P : Type u} [AddCommGroup P]

/-- The relation ideal of a surjective presentation is exactly the kernel of tensor evaluation. -/
theorem relationIdeal_eq_ker_tensorMap (ε : P →ₗ[ℤ] M)
    (hε : Function.Surjective ε) :
    relationIdeal ε = RingHom.ker (tensorMap ε).toRingHom := by
  let Q := relationIdeal ε
  have hQker : Q ≤ RingHom.ker (tensorMap ε).toRingHom := by
    intro x hx
    change x ∈ TwoSidedIdeal.span (Set.range fun q : LinearMap.ker ε ↦
      TensorAlgebra.ι ℤ (q : P)) at hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx =>
        obtain ⟨q, rfl⟩ := hx
        rw [RingHom.mem_ker]
        change tensorMap ε (TensorAlgebra.ι ℤ (q : P)) = 0
        rw [tensorMap_ι, q.property, map_zero]
    | zero => simp
    | add x y _ _ hx hy =>
        rw [RingHom.mem_ker] at hx hy ⊢
        rw [map_add, hx, hy, add_zero]
    | neg x _ hx =>
        rw [RingHom.mem_ker] at hx ⊢
        simpa only [map_neg, neg_eq_zero] using hx
    | left_absorb a x _ hx =>
        rw [RingHom.mem_ker] at hx ⊢
        rw [map_mul, hx, mul_zero]
    | right_absorb b x _ hx =>
        rw [RingHom.mem_ker] at hx ⊢
        rw [map_mul, hx, zero_mul]
  apply le_antisymm hQker
  let toQ : P →ₗ[ℤ] (TensorAlgebra ℤ P ⧸ Q) :=
    (Ideal.Quotient.mkₐ ℤ Q).toLinearMap.comp (TensorAlgebra.ι ℤ)
  have hkill : LinearMap.ker ε ≤ LinearMap.ker toQ := by
    intro p hp
    rw [LinearMap.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (TwoSidedIdeal.subset_span ⟨⟨p, hp⟩, rfl⟩)
  let quotientGenerator : M →ₗ[ℤ] (TensorAlgebra ℤ P ⧸ Q) :=
    ((LinearMap.ker ε).liftQ toQ hkill).comp
      ((ε.quotKerEquivOfSurjective hε).symm.toLinearMap)
  have quotientGenerator_ε (p : P) :
      quotientGenerator (ε p) =
        Ideal.Quotient.mk Q (TensorAlgebra.ι ℤ p) := by
    change (LinearMap.ker ε).liftQ toQ hkill
      ((ε.quotKerEquivOfSurjective hε).symm (ε p)) = _
    rw [show (ε.quotKerEquivOfSurjective hε).symm (ε p) =
        Submodule.Quotient.mk p by simp]
    rfl
  let fromTensor : TensorAlgebra ℤ M →ₐ[ℤ] TensorAlgebra ℤ P ⧸ Q :=
    TensorAlgebra.lift ℤ quotientGenerator
  have fromTensor_tensorMap (x : TensorAlgebra ℤ P) :
      fromTensor (tensorMap ε x) = Ideal.Quotient.mk Q x := by
    induction x using TensorAlgebra.induction with
    | algebraMap r => simp [fromTensor]
    | ι p =>
        rw [tensorMap_ι]
        rw [TensorAlgebra.lift_ι_apply]
        exact quotientGenerator_ε p
    | mul x y hx hy => simpa using congrArg₂ (· * ·) hx hy
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  intro x hx
  rw [RingHom.mem_ker] at hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← fromTensor_tensorMap x]
  have hx' : tensorMap ε x = 0 := hx
  rw [hx', map_zero]

/-- Tensor-algebra maps compose as expected. -/
theorem tensorMap_comp {P' : Type*} [AddCommGroup P']
    (f : P →ₗ[ℤ] M) (g : M →ₗ[ℤ] P') (x : TensorAlgebra ℤ P) :
    tensorMap g (tensorMap f x) = tensorMap (g.comp f) x := by
  let lhs := (tensorMap g).comp (tensorMap f)
  let rhs := tensorMap (g.comp f)
  have h : lhs = rhs := by
    apply TensorAlgebra.hom_ext
    apply LinearMap.ext
    intro p
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lhs, rhs, AlgHom.comp_apply,
      tensorMap_ι]
  exact DFunLike.congr_fun h x

@[simp]
theorem tensorMap_id (x : TensorAlgebra ℤ P) :
    tensorMap (LinearMap.id : P →ₗ[ℤ] P) x = x := by
  let f := tensorMap (LinearMap.id : P →ₗ[ℤ] P)
  have h : f = AlgHom.id ℤ (TensorAlgebra ℤ P) := by
    apply TensorAlgebra.hom_ext
    apply LinearMap.ext
    intro p
    simp [f, tensorMap_ι]
  exact DFunLike.congr_fun h x

/-- The relation--commutator ideal is contained in the tensor commutator ideal. -/
theorem relationCommutatorIdeal_le_commutatorIdeal (ε : P →ₗ[ℤ] M) :
    relationCommutatorIdeal ε ≤ tensorCommutatorIdeal P := by
  intro x hx
  change x ∈ TwoSidedIdeal.span
    (Set.range fun tq : TensorAlgebra ℤ P × relationIdeal ε ↦
      ⁅tq.1, (tq.2 : TensorAlgebra ℤ P)⁆) at hx
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
      obtain ⟨⟨t, q⟩, rfl⟩ := hx
      rw [tensorCommutatorIdeal, RingHom.mem_ker]
      simp [LieRing.of_associative_ring_bracket, mul_comm]
  | zero => exact (tensorCommutatorIdeal P).zero_mem
  | add x y _ _ hx hy => exact (tensorCommutatorIdeal P).add_mem hx hy
  | neg x _ hx => exact (tensorCommutatorIdeal P).neg_mem hx
  | left_absorb a x _ hx => exact (tensorCommutatorIdeal P).mul_mem_left a hx
  | right_absorb b x _ hx => exact (tensorCommutatorIdeal P).mul_mem_right b hx

/-- The endomorphism of a tensor algebra induced by a presentation endomorphism. -/
def tensorEndomorphism (h : P →ₗ[ℤ] P) :
    TensorAlgebra ℤ P →ₐ[ℤ] TensorAlgebra ℤ P := tensorMap h

/-- Presentation-change calculation for an arbitrary surjective free presentation. -/
theorem commutator_sub_tensorEndomorphism_mem_relationCommutatorIdeal
    (ε : P →ₗ[ℤ] M) (hε : Function.Surjective ε)
    (h : P →ₗ[ℤ] P) (hh : ε.comp h = ε)
    (k : tensorCommutatorIdeal P) :
    (k : TensorAlgebra ℤ P) - tensorEndomorphism h k ∈ relationCommutatorIdeal ε := by
  let generatorIdeal := TwoSidedIdeal.span
    (Set.range fun xy : P × P ↦
      ⁅TensorAlgebra.ι ℤ xy.1, TensorAlgebra.ι ℤ xy.2⁆)
  have hk : (k : TensorAlgebra ℤ P) ∈ generatorIdeal := by
    change (k : TensorAlgebra ℤ P) ∈ elementaryCommutatorIdeal P
    rw [elementaryCommutatorIdeal_eq_tensorCommutatorIdeal]
    exact k.property
  have hrelation (p : P) :
      TensorAlgebra.ι ℤ (p - h p) ∈ relationIdeal ε := by
    let q : LinearMap.ker ε := ⟨p - h p, by
      rw [LinearMap.mem_ker, map_sub]
      have hp := LinearMap.congr_fun hh p
      change ε (h p) = ε p at hp
      rw [hp, sub_self]⟩
    exact TwoSidedIdeal.subset_span ⟨q, rfl⟩
  have hcomm : (tensorMap ε).comp (tensorEndomorphism h) = tensorMap ε := by
    apply TensorAlgebra.hom_ext
    apply LinearMap.ext
    intro p
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      tensorEndomorphism, tensorMap_ι]
    exact congrArg (TensorAlgebra.ι ℤ) (LinearMap.congr_fun hh p)
  have hspan : ∀ (x : TensorAlgebra ℤ P) (hx : x ∈ generatorIdeal),
      x - tensorEndomorphism h x ∈ relationCommutatorIdeal ε := by
    intro x hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx =>
        obtain ⟨⟨a, b⟩, rfl⟩ := hx
        let qa : relationIdeal ε :=
          ⟨TensorAlgebra.ι ℤ (a - h a), hrelation a⟩
        let qb : relationIdeal ε :=
          ⟨TensorAlgebra.ι ℤ (b - h b), hrelation b⟩
        have ha := (relationCommutatorIdeal ε).neg_mem
          (relation_commutator_mem ε (TensorAlgebra.ι ℤ b) qa)
        have hb := relation_commutator_mem ε (TensorAlgebra.ι ℤ (h a)) qb
        have hz := (relationCommutatorIdeal ε).add_mem ha hb
        convert hz using 1 <;>
          simp only [qa, qb, tensorEndomorphism, LieRing.of_associative_ring_bracket,
            map_sub, map_mul, tensorMap_ι] <;> noncomm_ring
    | zero => simp
    | add x y _ _ hx hy =>
        have hz := (relationCommutatorIdeal ε).add_mem hx hy
        convert hz using 1 <;> simp only [map_add] <;> abel
    | neg x _ hx =>
        have hz := (relationCommutatorIdeal ε).neg_mem hx
        convert hz using 1 <;> simp only [map_neg] <;> abel
    | left_absorb a x hxK hx =>
        let qa : relationIdeal ε := ⟨a - tensorEndomorphism h a, by
          rw [relationIdeal_eq_ker_tensorMap ε hε, RingHom.mem_ker, map_sub]
          change tensorMap ε a - tensorMap ε (tensorEndomorphism h a) = 0
          have ha := DFunLike.congr_fun hcomm a
          change tensorMap ε (tensorEndomorphism h a) = tensorMap ε a at ha
          rw [ha, sub_self]⟩
        let kx : tensorCommutatorIdeal P := ⟨x, by
          rw [← elementaryCommutatorIdeal_eq_tensorCommutatorIdeal]
          exact hxK⟩
        have hleft := relation_mul_commutator_mem ε qa kx
        have hright := (relationCommutatorIdeal ε).mul_mem_left
          (tensorEndomorphism h a) hx
        have hz := (relationCommutatorIdeal ε).add_mem hleft hright
        convert hz using 1 <;>
          simp only [qa, map_mul] <;> noncomm_ring
    | right_absorb b x hxK hx =>
        let qb : relationIdeal ε := ⟨b - tensorEndomorphism h b, by
          rw [relationIdeal_eq_ker_tensorMap ε hε, RingHom.mem_ker, map_sub]
          change tensorMap ε b - tensorMap ε (tensorEndomorphism h b) = 0
          have hb := DFunLike.congr_fun hcomm b
          change tensorMap ε (tensorEndomorphism h b) = tensorMap ε b at hb
          rw [hb, sub_self]⟩
        have hdiffK : x - tensorEndomorphism h x ∈ tensorCommutatorIdeal P := by
          exact relationCommutatorIdeal_le_commutatorIdeal ε hx
        let krx : tensorCommutatorIdeal P :=
          ⟨tensorEndomorphism h x, by
            have hx' : x ∈ tensorCommutatorIdeal P := by
              rw [← elementaryCommutatorIdeal_eq_tensorCommutatorIdeal]
              exact hxK
            have hz := (tensorCommutatorIdeal P).sub_mem hx' hdiffK
            convert hz using 1 <;> abel⟩
        have hleft := (relationCommutatorIdeal ε).mul_mem_right b hx
        have hright := commutator_mul_relation_mem ε krx qb
        have hz := (relationCommutatorIdeal ε).add_mem hleft hright
        convert hz using 1 <;>
          simp only [qb, map_mul] <;> noncomm_ring
  exact hspan k hk

/-- Canonical vanishing transports to any surjective projective presentation. -/
theorem obstructionVanishes_of_canonical
    (ε : P →ₗ[ℤ] M) (hε : Function.Surjective ε)
    [Module.Projective ℤ P] (hB : LieRings.PBW.Higgins.ObstructionVanishes M) :
    ObstructionVanishes ε := by
  intro u hu
  let τ : P →ₗ[ℤ] FreePresentation M :=
    Classical.choose (Module.projective_lifting_property (presentationMap M) ε
      (presentationMap_surjective M))
  have hτ : (presentationMap M).comp τ = ε :=
    Classical.choose_spec (Module.projective_lifting_property (presentationMap M) ε
      (presentationMap_surjective M))
  let σ : FreePresentation M →ₗ[ℤ] P :=
    Classical.choose (Module.projective_lifting_property ε (presentationMap M) hε)
  have hσ : ε.comp σ = presentationMap M :=
    Classical.choose_spec (Module.projective_lifting_property ε (presentationMap M) hε)
  let Φ := tensorMap τ
  let Ψ := tensorMap σ
  have hΦK : Φ u ∈ commutatorIdeal M :=
    tensorMap_mem_commutatorIdeal τ hu.1
  have hΦQ : Φ u ∈ LieRings.PBW.Higgins.relationIdeal M := by
    exact tensorMap_mem_relationIdeal ε (presentationMap M) τ hτ hu.2
  have hΦZ : Φ u ∈ LieRings.PBW.Higgins.relationCommutatorIdeal M := by
    rw [obstructionVanishes_iff] at hB
    exact hB ⟨hΦK, hΦQ⟩
  have hΨZ : Ψ (Φ u) ∈ relationCommutatorIdeal ε :=
    tensorMap_mem_relationCommutatorIdeal
      (presentationMap M) ε σ hσ hΦZ
  have hcomp : Ψ.comp Φ = tensorEndomorphism (σ.comp τ) := by
    apply TensorAlgebra.hom_ext
    apply LinearMap.ext
    intro p
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, Φ, Ψ,
      tensorEndomorphism, tensorMap_ι]
  have hlift : ε.comp (σ.comp τ) = ε := by
    apply LinearMap.ext
    intro p
    change ε (σ (τ p)) = ε p
    rw [show ε (σ (τ p)) = presentationMap M (τ p) by
        exact LinearMap.congr_fun hσ (τ p),
      show presentationMap M (τ p) = ε p by
        exact LinearMap.congr_fun hτ p]
  let k : tensorCommutatorIdeal P := ⟨u, hu.1⟩
  have hdiff := commutator_sub_tensorEndomorphism_mem_relationCommutatorIdeal
    ε hε (σ.comp τ) hlift k
  change u - tensorEndomorphism (σ.comp τ) u ∈ relationCommutatorIdeal ε at hdiff
  have hΨΦ : Ψ (Φ u) = tensorEndomorphism (σ.comp τ) u :=
    DFunLike.congr_fun hcomp u
  rw [← hΨΦ] at hdiff
  have hz := (relationCommutatorIdeal ε).add_mem hdiff hΨZ
  convert hz using 1 <;> abel

theorem relationIdeal_eq_of_ker_eq {N : Type*} [AddCommGroup N]
    (ε : P →ₗ[ℤ] M) (ε' : P →ₗ[ℤ] N) (h : LinearMap.ker ε = LinearMap.ker ε') :
    relationIdeal ε = relationIdeal ε' := by
  simp only [relationIdeal]
  rw [h]

theorem relationCommutatorIdeal_eq_of_ker_eq {N : Type*} [AddCommGroup N]
    (ε : P →ₗ[ℤ] M) (ε' : P →ₗ[ℤ] N) (h : LinearMap.ker ε = LinearMap.ker ε') :
    relationCommutatorIdeal ε = relationCommutatorIdeal ε' := by
  simp only [relationCommutatorIdeal]
  rw [relationIdeal_eq_of_ker_eq ε ε' h]

end AuxiliaryPresentation

namespace ExternalCyclic

variable {M : Type u} [AddCommGroup M]
variable {ι : Type v} [DecidableEq ι]
variable (A : ι → Type w) [∀ i, AddCommGroup (A i)]
variable (cyclic : ∀ i, IsAddCyclic (A i))

def generator (i : ι) : A i := by
  letI : IsAddCyclic (A i) := cyclic i
  exact Classical.choose IsAddCyclic.exists_zsmul_surjective

theorem generator_surjective (i : ι) :
    Function.Surjective (fun n : ℤ ↦ n • generator A cyclic i) := by
  letI : IsAddCyclic (A i) := cyclic i
  exact Classical.choose_spec IsAddCyclic.exists_zsmul_surjective

def coefficientMap (i : ι) : ℤ →ₗ[ℤ] A i where
  toFun n := n • generator A cyclic i
  map_add' a b := add_smul a b _
  map_smul' a b := by
    change (a * b) • generator A cyclic i = a • b • generator A cyclic i
    rw [mul_smul]

def toDirectSum : (ι →₀ ℤ) →ₗ[ℤ] DirectSum ι A :=
  (DirectSum.lmap (coefficientMap A cyclic)).comp
    (finsuppLEquivDirectSum ℤ ℤ ι).toLinearMap

@[simp]
theorem toDirectSum_apply (p : ι →₀ ℤ) (i : ι) :
    toDirectSum A cyclic p i = p i • generator A cyclic i := by
  change (DirectSum.lmap (coefficientMap A cyclic)
    (finsuppLEquivDirectSum ℤ ℤ ι p)) i = _
  let d := finsuppLEquivDirectSum ℤ ℤ ι p
  calc
    ((DFinsupp.mapRange.linearMap (coefficientMap A cyclic)) d) i =
        (DFinsupp.mapRange (fun i x ↦ coefficientMap A cyclic i x)
          (fun i ↦ (coefficientMap A cyclic i).map_zero) d) i :=
      congrArg (fun x : DirectSum ι A ↦ x i)
        (DFinsupp.mapRange.linearMap_apply (coefficientMap A cyclic) d)
    _ = coefficientMap A cyclic i (d i) := DFinsupp.mapRange_apply _ _ _ _
    _ = p i • generator A cyclic i := by
      rw [show d i = p i by exact finsuppLEquivDirectSum_apply ℤ ℤ ι p i]
      rfl

/-- The free presentation obtained by choosing one generator in each cyclic summand. -/
def presentation (e : DirectSum ι A ≃ₗ[ℤ] M) : (ι →₀ ℤ) →ₗ[ℤ] M :=
  e.toLinearMap.comp (toDirectSum A cyclic)

theorem presentation_surjective (e : DirectSum ι A ≃ₗ[ℤ] M) :
    Function.Surjective (presentation A cyclic e) := by
  intro x
  let d := e.symm x
  have hd : ∃ p, toDirectSum A cyclic p = d := by
    induction d using DirectSum.induction_on with
    | zero => exact ⟨0, by simp [toDirectSum]⟩
    | of i a =>
        obtain ⟨n, hn⟩ := generator_surjective A cyclic i a
        refine ⟨Finsupp.single i n, ?_⟩
        apply DFinsupp.ext
        intro j
        by_cases hji : j = i
        · subst j
          simpa [toDirectSum_apply] using hn
        · simp [toDirectSum_apply, DirectSum.of_apply, hji, Ne.symm hji]
    | add x y hx hy =>
        obtain ⟨p, hp⟩ := hx
        obtain ⟨q, hq⟩ := hy
        exact ⟨p + q, by rw [map_add, hp, hq]⟩
  obtain ⟨p, hp⟩ := hd
  refine ⟨p, ?_⟩
  rw [presentation, LinearMap.comp_apply, hp]
  exact e.apply_symm_apply x

theorem ker_component (e : DirectSum ι A ≃ₗ[ℤ] M)
    (q : LinearMap.ker (presentation A cyclic e)) (i : ι) :
    q.1 i • generator A cyclic i = 0 := by
  have hzero : toDirectSum A cyclic q = 0 := by
    apply e.injective
    change e (toDirectSum A cyclic q) = e 0
    simpa [presentation, LinearMap.comp_apply] using q.property
  have hi := congrArg (fun d : DirectSum ι A ↦ d i) hzero
  simpa [toDirectSum_apply] using hi

set_option maxHeartbeats 800000 in
-- Elaborating the dependent external direct-sum equivalence needs a larger heartbeat budget.
/-- Vanishing for a module externally presented as a direct sum of cyclic modules. -/
theorem obstructionVanishes_of_equiv_directSum
    (cyclic : ∀ i, IsAddCyclic (A i))
    (e : DirectSum ι A ≃ₗ[ℤ] M) : ObstructionVanishes M := by
  letI : LinearOrder ι := WellOrderingRel.isWellOrder.linearOrder
  let ε := presentation A cyclic e
  have hdiag : ∀ (q : LinearMap.ker ε) i,
      ε (q.1 i • Finsupp.single i 1) = 0 := by
    intro q i
    rw [show q.1 i • Finsupp.single i 1 = Finsupp.single i (q.1 i) by
      ext j
      by_cases hji : j = i <;> simp [hji]]
    change e (toDirectSum A cyclic (Finsupp.single i (q.1 i))) = 0
    rw [← map_zero e]
    apply congrArg e
    apply DFinsupp.ext
    intro j
    by_cases hji : j = i
    · subst j
      simpa [toDirectSum_apply] using ker_component A cyclic e q i
    · simp [toDirectSum_apply, hji]
  have haux : AuxiliaryPresentation.ObstructionVanishes ε :=
    OrderedCyclic.auxiliaryObstructionVanishes_of_diagonal ε hdiag
  exact obstructionVanishes_of_auxiliary_freePresentation ε
    (presentation_surjective A cyclic e) haux

end ExternalCyclic

section FiniteAbelian

variable {M : Type u} [AddCommGroup M]

/-- Every quotient of `ℤ` is cyclic as an additive group. -/
theorem isAddCyclic_intQuotient (I : Submodule ℤ ℤ) :
    IsAddCyclic (ℤ ⧸ I) := by
  refine ⟨⟨Submodule.Quotient.mk 1, ?_⟩⟩
  intro x
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective I x
  refine ⟨n, ?_⟩
  change n • Submodule.Quotient.mk 1 = Submodule.Quotient.mk n
  calc
    n • Submodule.Quotient.mk 1 =
        Submodule.Quotient.mk (n • (1 : ℤ)) :=
      (Submodule.Quotient.mk_smul I n 1).symm
    _ = Submodule.Quotient.mk n := by simp

/-- The structure theorem for finitely generated Abelian groups, in the exact external form needed
by the cyclic-sum obstruction theorem. -/
theorem obstructionVanishes_of_finite [Module.Finite ℤ M] : ObstructionVanishes M := by
  obtain ⟨n, ι, fintypeι, p, hp, exponents, ⟨e⟩⟩ :=
    Module.equiv_free_prod_directSum ℤ M
  letI : Fintype ι := fintypeι
  letI : DecidableEq ι := Classical.decEq ι
  let J : Fin 2 → Type := Fin.cases (Fin n) (fun _ ↦ ι)
  let B : (j : Fin 2) → J j → Type := fun j ↦
    Fin.cases (fun _ : Fin n ↦ ℤ)
      (fun _ : Fin 1 ↦ fun i : ι ↦
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
  let eSigma : (DirectSum ((j : Fin 2) × J j) fun ji ↦ B ji.1 ji.2) ≃ₗ[ℤ]
      (Fin n →₀ ℤ) × DirectSum ι
        (fun i ↦ ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ)) :=
    by
      dsimp only [J, B]
      exact (DirectSum.sigmaLcurryEquiv ℤ).trans <|
        (DirectSum.linearEquivFunOnFintype ℤ (Fin 2)
          (fun j ↦ DirectSum (Fin.cases (Fin n) (fun _ ↦ ι) j)
            (fun i ↦ Fin.cases (fun _ : Fin n ↦ ℤ)
              (fun _ : Fin 1 ↦ fun i : ι ↦
                ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ)) j i))).trans <|
          (LinearEquiv.piFinTwo ℤ
            (fun j ↦ DirectSum (Fin.cases (Fin n) (fun _ ↦ ι) j)
              (fun i ↦ Fin.cases (fun _ : Fin n ↦ ℤ)
                (fun _ : Fin 1 ↦ fun i : ι ↦
                  ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ)) j i))).trans <|
            LinearEquiv.prodCongr
              (finsuppLEquivDirectSum ℤ ℤ (Fin n)).symm
              (LinearEquiv.refl ℤ (DirectSum ι
                (fun i ↦ ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ))))
  have hcyclic : ∀ ji : (j : Fin 2) × J j, IsAddCyclic (B ji.1 ji.2) := by
    intro ji
    rcases ji with ⟨j, i⟩
    fin_cases j
    · change IsAddCyclic ℤ
      exact inferInstance
    · change IsAddCyclic
        (ℤ ⧸ (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ))
      exact isAddCyclic_intQuotient
        (ℤ ∙ (p i ^ exponents i) : Submodule ℤ ℤ)
  letI : DecidableEq ((j : Fin 2) × J j) := Classical.decEq _
  exact ExternalCyclic.obstructionVanishes_of_equiv_directSum
    (fun ji : (j : Fin 2) × J j ↦ B ji.1 ji.2) hcyclic (eSigma.trans e.symm)

end FiniteAbelian

namespace FiniteStage

variable {M : Type u} [AddCommGroup M]

abbrev Free (S : Finset M) := S →₀ ℤ

/-- Inclusion of the free module on a finite subset into the canonical free presentation. -/
def inclusion (S : Finset M) : Free S →ₗ[ℤ] FreePresentation M :=
  Finsupp.lmapDomain ℤ ℤ (fun x : S ↦ (x : M))

/-- Coordinate restriction, a left inverse to `inclusion`. -/
def restrict (S : Finset M) : FreePresentation M →ₗ[ℤ] Free S :=
  Finsupp.lcomapDomain (R := ℤ) (M := ℤ) (fun x : S ↦ (x : M)) Subtype.val_injective

theorem restrict_include (S : Finset M) :
    (restrict S).comp (inclusion S) =
      (LinearMap.id : Free S →ₗ[ℤ] Free S) := by
  apply LinearMap.ext
  intro p
  exact Finsupp.leftInverse_lcomapDomain_mapDomain
    (R := ℤ) (M := ℤ) _ Subtype.val_injective p

theorem include_injective (S : Finset M) : Function.Injective (inclusion S) := by
  apply Function.LeftInverse.injective (g := restrict S)
  intro p
  exact LinearMap.congr_fun (restrict_include S) p

/-- Evaluation of the finite free module in `M`. -/
def presentation (S : Finset M) : Free S →ₗ[ℤ] M :=
  (presentationMap M).comp (inclusion S)

/-- Inclusion between two finite stages. -/
def mapTo {S T : Finset M} (h : S ⊆ T) : Free S →ₗ[ℤ] Free T :=
  Finsupp.lmapDomain ℤ ℤ (fun x : S ↦ (⟨x, h x.property⟩ : T))

theorem include_mapTo {S T : Finset M} (h : S ⊆ T) :
    (inclusion T).comp (mapTo h) = inclusion S := by
  rw [inclusion, mapTo, ← Finsupp.lmapDomain_comp]
  rfl

theorem presentation_mapTo {S T : Finset M} (h : S ⊆ T) :
    (presentation T).comp (mapTo h) = presentation S := by
  rw [presentation, presentation, LinearMap.comp_assoc, include_mapTo]

theorem include_restrict_of_support_subset (S : Finset M) (p : FreePresentation M)
    (hp : p.support ⊆ S) : inclusion S (restrict S p) = p := by
  change Finsupp.mapDomain (fun x : S ↦ (x : M))
      (Finsupp.comapDomain (fun x : S ↦ (x : M)) p _) = p
  apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective p
  intro x hx
  exact ⟨⟨x, hp hx⟩, rfl⟩

theorem tensor_include_mapTo {S T : Finset M} (h : S ⊆ T)
    (x : TensorAlgebra ℤ (Free S)) :
    AuxiliaryPresentation.tensorMap (inclusion T)
        (AuxiliaryPresentation.tensorMap (mapTo h) x) =
      AuxiliaryPresentation.tensorMap (inclusion S) x := by
  rw [AuxiliaryPresentation.tensorMap_comp]
  have hm : (inclusion T).comp (mapTo h) = inclusion S := include_mapTo h
  rw [hm]

/-- Every tensor in the canonical free presentation is already defined over a finite subset. -/
theorem exists_tensor_lift (x : PresentationTensor M) :
    ∃ (S : Finset M) (y : TensorAlgebra ℤ (Free S)),
      AuxiliaryPresentation.tensorMap (inclusion S) y = x := by
  classical
  induction x using TensorAlgebra.induction with
  | algebraMap n =>
      exact ⟨∅, algebraMap ℤ (TensorAlgebra ℤ (Free ∅)) n, by simp⟩
  | ι p =>
      let S := p.support
      let q := restrict S p
      refine ⟨S, TensorAlgebra.ι ℤ q, ?_⟩
      rw [AuxiliaryPresentation.tensorMap_ι]
      exact congrArg (TensorAlgebra.ι ℤ)
        (include_restrict_of_support_subset S p (by rfl))
  | mul x y hx hy =>
      obtain ⟨S, x', hx'⟩ := hx
      obtain ⟨T, y', hy'⟩ := hy
      let U := S ∪ T
      let xU := AuxiliaryPresentation.tensorMap
        (mapTo (Finset.subset_union_left : S ⊆ U)) x'
      let yU := AuxiliaryPresentation.tensorMap
        (mapTo (Finset.subset_union_right : T ⊆ U)) y'
      refine ⟨U, xU * yU, ?_⟩
      rw [map_mul]
      change AuxiliaryPresentation.tensorMap (inclusion U) xU *
        AuxiliaryPresentation.tensorMap (inclusion U) yU = x * y
      rw [tensor_include_mapTo, tensor_include_mapTo, hx', hy']
  | add x y hx hy =>
      obtain ⟨S, x', hx'⟩ := hx
      obtain ⟨T, y', hy'⟩ := hy
      let U := S ∪ T
      let xU := AuxiliaryPresentation.tensorMap
        (mapTo (Finset.subset_union_left : S ⊆ U)) x'
      let yU := AuxiliaryPresentation.tensorMap
        (mapTo (Finset.subset_union_right : T ⊆ U)) y'
      refine ⟨U, xU + yU, ?_⟩
      rw [map_add]
      change AuxiliaryPresentation.tensorMap (inclusion U) xU +
        AuxiliaryPresentation.tensorMap (inclusion U) yU = x + y
      rw [tensor_include_mapTo, tensor_include_mapTo, hx', hy']

/-- Every membership witness in the canonical relation ideal already occurs at a finite stage. -/
theorem exists_relation_lift {x : PresentationTensor M} (hx : x ∈ relationIdeal M) :
    ∃ (S : Finset M) (y : TensorAlgebra ℤ (Free S)),
      AuxiliaryPresentation.tensorMap (inclusion S) y = x ∧
        y ∈ AuxiliaryPresentation.relationIdeal (presentation S) := by
  classical
  change x ∈ TwoSidedIdeal.span
    (Set.range fun q : PresentationRelations M ↦
      TensorAlgebra.ι ℤ (q : FreePresentation M)) at hx
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      let S := q.1.support
      let qS : LinearMap.ker (presentation S) := ⟨restrict S q, by
        rw [LinearMap.mem_ker]
        change presentationMap M (inclusion S (restrict S q)) = 0
        rw [include_restrict_of_support_subset S q (by rfl)]
        exact q.property⟩
      refine ⟨S, TensorAlgebra.ι ℤ qS, ?_, ?_⟩
      · rw [AuxiliaryPresentation.tensorMap_ι]
        exact congrArg (TensorAlgebra.ι ℤ)
          (include_restrict_of_support_subset S q (by rfl))
      · exact TwoSidedIdeal.subset_span ⟨qS, rfl⟩
  | zero =>
      exact ⟨∅, 0, by simp, (AuxiliaryPresentation.relationIdeal _).zero_mem⟩
  | add x y _ _ hx hy =>
      obtain ⟨S, x', hxmap, hxQ⟩ := hx
      obtain ⟨T, y', hymap, hyQ⟩ := hy
      let U := S ∪ T
      let fS := mapTo (Finset.subset_union_left : S ⊆ U)
      let fT := mapTo (Finset.subset_union_right : T ⊆ U)
      let xU := AuxiliaryPresentation.tensorMap fS x'
      let yU := AuxiliaryPresentation.tensorMap fT y'
      have hxU : xU ∈ AuxiliaryPresentation.relationIdeal (presentation U) :=
        AuxiliaryPresentation.tensorMap_mem_relationIdeal
          (presentation S) (presentation U) fS (presentation_mapTo _) hxQ
      have hyU : yU ∈ AuxiliaryPresentation.relationIdeal (presentation U) :=
        AuxiliaryPresentation.tensorMap_mem_relationIdeal
          (presentation T) (presentation U) fT (presentation_mapTo _) hyQ
      refine ⟨U, xU + yU, ?_,
        (AuxiliaryPresentation.relationIdeal _).add_mem hxU hyU⟩
      rw [map_add]
      change AuxiliaryPresentation.tensorMap (inclusion U) xU +
        AuxiliaryPresentation.tensorMap (inclusion U) yU = x + y
      rw [tensor_include_mapTo, tensor_include_mapTo, hxmap, hymap]
  | neg x _ hx =>
      obtain ⟨S, x', hxmap, hxQ⟩ := hx
      refine ⟨S, -x', ?_, (AuxiliaryPresentation.relationIdeal _).neg_mem hxQ⟩
      simpa using congrArg Neg.neg hxmap
  | left_absorb a x _ hx =>
      obtain ⟨T, a', hamap⟩ := exists_tensor_lift a
      obtain ⟨S, x', hxmap, hxQ⟩ := hx
      let U := S ∪ T
      let fS := mapTo (Finset.subset_union_left : S ⊆ U)
      let fT := mapTo (Finset.subset_union_right : T ⊆ U)
      let aU := AuxiliaryPresentation.tensorMap fT a'
      let xU := AuxiliaryPresentation.tensorMap fS x'
      have hxU : xU ∈ AuxiliaryPresentation.relationIdeal (presentation U) :=
        AuxiliaryPresentation.tensorMap_mem_relationIdeal
          (presentation S) (presentation U) fS (presentation_mapTo _) hxQ
      refine ⟨U, aU * xU, ?_,
        (AuxiliaryPresentation.relationIdeal _).mul_mem_left aU hxU⟩
      rw [map_mul]
      change AuxiliaryPresentation.tensorMap (inclusion U) aU *
        AuxiliaryPresentation.tensorMap (inclusion U) xU = a * x
      rw [tensor_include_mapTo, tensor_include_mapTo, hamap, hxmap]
  | right_absorb b x _ hx =>
      obtain ⟨T, b', hbmap⟩ := exists_tensor_lift b
      obtain ⟨S, x', hxmap, hxQ⟩ := hx
      let U := S ∪ T
      let fS := mapTo (Finset.subset_union_left : S ⊆ U)
      let fT := mapTo (Finset.subset_union_right : T ⊆ U)
      let bU := AuxiliaryPresentation.tensorMap fT b'
      let xU := AuxiliaryPresentation.tensorMap fS x'
      have hxU : xU ∈ AuxiliaryPresentation.relationIdeal (presentation U) :=
        AuxiliaryPresentation.tensorMap_mem_relationIdeal
          (presentation S) (presentation U) fS (presentation_mapTo _) hxQ
      refine ⟨U, xU * bU, ?_,
        (AuxiliaryPresentation.relationIdeal _).mul_mem_right bU hxU⟩
      rw [map_mul]
      change AuxiliaryPresentation.tensorMap (inclusion U) xU *
        AuxiliaryPresentation.tensorMap (inclusion U) bU = x * b
      rw [tensor_include_mapTo, tensor_include_mapTo, hxmap, hbmap]

end FiniteStage

section DirectedUnion

variable (M : Type u) [AddCommGroup M]

/-- A canonical obstruction element vanishes as soon as its finite relation stage does.  This is
the elementwise filtered-colimit compatibility statement used in the final theorem. -/
theorem baerNumerator_mem_relationCommutatorIdeal_of_finiteStage
    (x : PresentationTensor M) (hx : x ∈ baerNumerator M) :
    x ∈ relationCommutatorIdeal M := by
  obtain ⟨S, y, hymap, hyQ⟩ := FiniteStage.exists_relation_lift hx.2
  have hyKambient : AuxiliaryPresentation.tensorMap (FiniteStage.inclusion S) y ∈
      tensorCommutatorIdeal (FreePresentation M) := by
    rw [hymap]
    exact hx.1
  have hyK' := AuxiliaryPresentation.tensorMap_mem_commutatorIdeal
    (FiniteStage.restrict S) hyKambient
  have hretract : AuxiliaryPresentation.tensorMap (FiniteStage.restrict S)
      (AuxiliaryPresentation.tensorMap (FiniteStage.inclusion S) y) = y := by
    rw [AuxiliaryPresentation.tensorMap_comp]
    rw [FiniteStage.restrict_include]
    exact AuxiliaryPresentation.tensorMap_id y
  rw [hretract] at hyK'
  let A := LinearMap.range (FiniteStage.presentation S)
  let εA : FiniteStage.Free S →ₗ[ℤ] A :=
    (FiniteStage.presentation S).codRestrict A fun p ↦ ⟨p, rfl⟩
  have hεA : Function.Surjective εA := by
    intro a
    obtain ⟨p, hp⟩ := a.property
    refine ⟨p, ?_⟩
    exact Subtype.ext hp
  letI : Module.Finite ℤ A := Module.Finite.of_surjective εA hεA
  have hBA : ObstructionVanishes A := obstructionVanishes_of_finite
  have hauxA : AuxiliaryPresentation.ObstructionVanishes εA :=
    AuxiliaryPresentation.obstructionVanishes_of_canonical εA hεA hBA
  have hker : LinearMap.ker (FiniteStage.presentation S) = LinearMap.ker εA := by
    symm
    exact LinearMap.ker_codRestrict A (FiniteStage.presentation S)
      (fun p ↦ ⟨p, rfl⟩)
  have hyQA : y ∈ AuxiliaryPresentation.relationIdeal εA := by
    rw [← AuxiliaryPresentation.relationIdeal_eq_of_ker_eq
      (FiniteStage.presentation S) εA hker]
    exact hyQ
  have hyZA : y ∈ AuxiliaryPresentation.relationCommutatorIdeal εA :=
    hauxA ⟨hyK', hyQA⟩
  have hyZS : y ∈ AuxiliaryPresentation.relationCommutatorIdeal
      (FiniteStage.presentation S) := by
    rw [AuxiliaryPresentation.relationCommutatorIdeal_eq_of_ker_eq
      (FiniteStage.presentation S) εA hker]
    exact hyZA
  have hcompat : (presentationMap M).comp (FiniteStage.inclusion S) =
      FiniteStage.presentation S := rfl
  have hmapZ := AuxiliaryPresentation.tensorMap_mem_relationCommutatorIdeal
    (FiniteStage.presentation S) (presentationMap M) (FiniteStage.inclusion S)
      hcompat hyZS
  change AuxiliaryPresentation.tensorMap (FiniteStage.inclusion S) y ∈
    relationCommutatorIdeal M at hmapZ
  rwa [hymap] at hmapZ

/-- **Higgins's directed-limit theorem over `ℤ`.** The Baer obstruction vanishes for every
Abelian group.  No finite generation, torsion-freeness, freeness, or choice of presentation is
assumed. -/
theorem obstructionVanishes_all : ObstructionVanishes M := by
  rw [obstructionVanishes_iff]
  intro x hx
  exact baerNumerator_mem_relationCommutatorIdeal_of_finiteStage M x hx

end DirectedUnion

end

end LieRings.PBW.Higgins
