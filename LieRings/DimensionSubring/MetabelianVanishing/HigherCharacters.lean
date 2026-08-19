import LieRings.DimensionSubring.MetabelianVanishing.Tower
import LieRings.Homological.RatCircleTorsion

/-!
# Higher characters and their chain transgression

This file follows the manuscript's construction literally.  The long bracket
is first made multilinear on representatives.  Its two quotient-independence
proofs are then used to descend it to `U_k ⊗ Sym^(m_k-1)(V_k)`.
-/

namespace LieRings.MetabelianVanishing

open TensorProduct FreeMetabelian

universe u

noncomputable section

set_option maxHeartbeats 1200000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)

local instance finiteV (k : ℕ) : Finite (V L k) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)

local instance finiteW (k : ℕ) : Finite (W L k) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)

theorem derived_eq_lowerCentralSeries_one :
    LieAlgebra.derivedSeries ℤ L 1 = lowerCentralSeries ℤ L 1 := by
  simpa [LieAlgebra.derivedSeries_def,
    LieAlgebra.derivedSeriesOfIdeal_succ, lowerCentralSeries,
    LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]

/-- A lower-central element of manuscript weight at least two is derived. -/
private def lcsToDerived (k : ℕ) (hk : 2 ≤ k) :
    (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L) →ₗ[ℤ]
      FreeMetabelian.Evaluation.Derived L :=
  LinearMap.codRestrict (LieAlgebra.derivedSeries ℤ L 1)
    (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype (by
      intro x
      rw [derived_eq_lowerCentralSeries_one L]
      exact LieModule.antitone_lowerCentralSeries ℤ L L (by omega) x.2)

/-- The literal iterated right bracket, with its derived head still exposed. -/
private def rawBracket (q : ℕ) :
    FreeMetabelian.Evaluation.Derived L →ₗ[ℤ]
      MultilinearMap ℤ (fun _ : Fin q ↦ L) L where
  toFun d := by
    classical
    let A := FreeMetabelian.Evaluation.actionMultilinear data.metabelian
      (LinearMap.id : L →ₗ[ℤ] L) q
    exact
      { toFun := fun x ↦ (A x d).1
        map_update_add' := by
          intro _ x i a b
          exact congrArg (fun T : Module.End ℤ
              (FreeMetabelian.Evaluation.Derived L) ↦ (T d).1)
            (A.map_update_add x i a b)
        map_update_smul' := by
          intro _ x i z a
          exact congrArg (fun T : Module.End ℤ
              (FreeMetabelian.Evaluation.Derived L) ↦ (T d).1)
            (A.map_update_smul x i z a) }
  map_add' a b := by
    ext x
    change ((FreeMetabelian.Evaluation.actionMultilinear data.metabelian
      (LinearMap.id : L →ₗ[ℤ] L) q x) (a + b)).1 = _
    rw [map_add]
    rfl
  map_smul' z a := by
    ext x
    change ((FreeMetabelian.Evaluation.actionMultilinear data.metabelian
      (LinearMap.id : L →ₗ[ℤ] L) q x) (z • a)).1 = _
    rw [map_smul]
    rfl

private theorem rawBracket_symmetric (q : ℕ)
    (d : FreeMetabelian.Evaluation.Derived L) :
    SymmetricPower.IsSymmetric
      (rawBracket (n := n) (L := L) data q d) := by
  intro e x
  have hsym := FreeMetabelian.Evaluation.actionMultilinear_symmetric
    data.metabelian (LinearMap.id : L →ₗ[ℤ] L) q e x
  exact congrArg (fun T : Module.End ℤ
      (FreeMetabelian.Evaluation.Derived L) ↦ (T d).1)
    hsym

private theorem actionList_mem_lowerCentralSeries (r : ℕ)
    (d : FreeMetabelian.Evaluation.Derived L)
    (hd : d.1 ∈ lowerCentralSeries ℤ L r) (xs : List L) :
    (((xs.map (FreeMetabelian.Evaluation.rightAction
      (LinearMap.id : L →ₗ[ℤ] L))).prod d).1) ∈
      lowerCentralSeries ℤ L (r + xs.length) := by
  induction xs with
  | nil => simpa using hd
  | cons x xs ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
      change ⁅((xs.map (FreeMetabelian.Evaluation.rightAction
        (LinearMap.id : L →ₗ[ℤ] L))).prod d).1, x⁆ ∈ _
      have hbracket : ⁅((xs.map (FreeMetabelian.Evaluation.rightAction
          (LinearMap.id : L →ₗ[ℤ] L))).prod d).1, x⁆ ∈
          lowerCentralSeries ℤ L (r + xs.length + 1) := by
        change ⁅((xs.map (FreeMetabelian.Evaluation.rightAction
          (LinearMap.id : L →ₗ[ℤ] L))).prod d).1, x⁆ ∈
          LieModule.lowerCentralSeries ℤ L L ((r + xs.length) + 1)
        rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
        exact LieSubmodule.lie_mem_lie ih (LieSubmodule.mem_top x)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 xs.length,
        Nat.add_left_comm 1 r] using hbracket

private theorem actionList_eq_zero_of_derived_tooth
    (hmeta : IsMetabelian L)
    (d : FreeMetabelian.Evaluation.Derived L) (xs : List L)
    (h : ∃ x ∈ xs, x ∈ LieAlgebra.derivedSeries ℤ L 1) :
    (xs.map (FreeMetabelian.Evaluation.rightAction
      (LinearMap.id : L →ₗ[ℤ] L))).prod d = 0 := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      rcases h with ⟨y, hy, hyder⟩
      rw [List.mem_cons] at hy
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rcases hy with (hy | hy)
      · subst y
        apply Subtype.ext
        change ⁅((xs.map (FreeMetabelian.Evaluation.rightAction
          (LinearMap.id : L →ₗ[ℤ] L))).prod d).1, x⁆ = 0
        exact IsMetabelian.bracket_eq_zero hmeta
          ((xs.map (FreeMetabelian.Evaluation.rightAction
            (LinearMap.id : L →ₗ[ℤ] L))).prod d).2 hyder
      · rw [ih ⟨y, hy, hyder⟩]
        exact map_zero _

private theorem rawBracket_mem_lowerCentralSeries (k q : ℕ) (hk : 2 ≤ k)
    (d : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L))
    (x : Fin q → L) :
    rawBracket (n := n) (L := L) data q (lcsToDerived L k hk d) x ∈
      lowerCentralSeries ℤ L (k - 1 + q) := by
  change ((FreeMetabelian.Evaluation.actionMultilinear data.metabelian
      (LinearMap.id : L →ₗ[ℤ] L) q x) (lcsToDerived L k hk d)).1 ∈ _
  rw [FreeMetabelian.Evaluation.actionMultilinear,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply]
  simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using
    actionList_mem_lowerCentralSeries (L := L) (k - 1)
    (lcsToDerived L k hk d) d.2 (List.ofFn x)

private theorem rawBracket_eq_zero_of_derived_tooth (k q : ℕ) (hk : 2 ≤ k)
    (d : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L))
    (x : Fin q → L) (i : Fin q)
    (hi : x i ∈ LieAlgebra.derivedSeries ℤ L 1) :
    rawBracket (n := n) (L := L) data q (lcsToDerived L k hk d) x = 0 := by
  change ((FreeMetabelian.Evaluation.actionMultilinear data.metabelian
      (LinearMap.id : L →ₗ[ℤ] L) q x) (lcsToDerived L k hk d)).1 = 0
  rw [FreeMetabelian.Evaluation.actionMultilinear,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply]
  have hzero := actionList_eq_zero_of_derived_tooth (L := L)
    data.metabelian (lcsToDerived L k hk d) (List.ofFn x)
      ⟨x i, (List.mem_ofFn' x (x i)).2 ⟨i, rfl⟩, hi⟩
  simpa only [List.map_ofFn, Function.comp_def] using congrArg Subtype.val hzero

/-- The representative-level bracket, already cod-restricted to the last
lower-central layer. -/
private def rawTopBracket (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L) →ₗ[ℤ]
      MultilinearMap ℤ (fun _ : Fin (n + 1 - k) ↦ L)
        (lowerCentralSeries ℤ L n : Submodule ℤ L) :=
  { toFun := fun d ↦
      (rawBracket (n := n) (L := L) data (n + 1 - k)
          (lcsToDerived L k hk d)).codRestrict
        (lowerCentralSeries ℤ L n) (fun x ↦ by
          have hmem := rawBracket_mem_lowerCentralSeries (n := n) (L := L)
            data k (n + 1 - k)
            hk d x
          have hindex : k - 1 + (n + 1 - k) = n := by omega
          simpa only [hindex] using hmem),
    map_add' := by
      intro a b
      ext x
      change rawBracket (n := n) (L := L) data (n + 1 - k)
          (lcsToDerived L k hk (a + b)) x = _
      rw [map_add, map_add, MultilinearMap.add_apply]
      change _ = rawBracket (n := n) (L := L) data (n + 1 - k)
          (lcsToDerived L k hk a) x +
        rawBracket (n := n) (L := L) data (n + 1 - k)
          (lcsToDerived L k hk b) x
      rfl
    map_smul' := by
      intro z a
      ext x
      change rawBracket (n := n) (L := L) data (n + 1 - k)
          (lcsToDerived L k hk (z • a)) x = _
      rw [map_smul, map_smul, MultilinearMap.smul_apply]
      rfl }

private theorem rawTopBracket_eq_zero_of_head_next (k : ℕ)
    (hk : 2 ≤ k) (hkn : k ≤ n)
    (d : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L))
    (hd : d.1 ∈ lowerCentralSeries ℤ L k)
    (x : Fin (n + 1 - k) → L) :
    rawTopBracket (n := n) (L := L) data k hk hkn d x = 0 := by
  apply Subtype.ext
  have hmem := rawBracket_mem_lowerCentralSeries (n := n) (L := L) data (k + 1)
    (n + 1 - k) (by omega) ⟨d.1, hd⟩ x
  have hindex : k + 1 - 1 + (n + 1 - k) = n + 1 := by omega
  rw [hindex, data.classBound] at hmem
  simpa only [Submodule.mem_bot] using hmem

private theorem rawTopBracket_eq_zero_of_tooth_next (k : ℕ)
    (hk : 2 ≤ k) (hkn : k ≤ n)
    (d : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L))
    (x : Fin (n + 1 - k) → L) (i : Fin (n + 1 - k))
    (hi : x i ∈ lowerCentralSeries ℤ L (k - 1)) :
    rawTopBracket (n := n) (L := L) data k hk hkn d x = 0 := by
  apply Subtype.ext
  apply rawBracket_eq_zero_of_derived_tooth (n := n) (L := L) data k _ hk d x i
  rw [derived_eq_lowerCentralSeries_one L]
  exact LieModule.antitone_lowerCentralSeries ℤ L L (by omega) hi

private theorem multilinear_eq_of_sub_mem
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {q : ℕ}
    (S : Submodule ℤ M) (f : MultilinearMap ℤ (fun _ : Fin q ↦ M) N)
    (hzero : ∀ (x : Fin q → M) (i : Fin q), x i ∈ S → f x = 0)
    (x y : Fin q → M) (hxy : ∀ i, x i - y i ∈ S) : f x = f y := by
  classical
  apply sub_eq_zero.mp
  have hformula := f.map_sub_map_piecewise x y Finset.univ
  rw [Finset.piecewise_univ] at hformula
  rw [hformula]
  apply Finset.sum_eq_zero
  intro i _
  apply hzero _ i
  simpa only [Finset.mem_univ, true_implies, lt_self_iff_false, if_false,
    if_pos] using hxy i

/-- Descend every variable of a multilinear map through the same module
quotient.  This is the repeated quotient step used for the teeth of the long
bracket. -/
private def descendMultilinear
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {q : ℕ}
    (S : Submodule ℤ M) (f : MultilinearMap ℤ (fun _ : Fin q ↦ M) N)
    (hzero : ∀ (x : Fin q → M) (i : Fin q), x i ∈ S → f x = 0) :
    MultilinearMap ℤ (fun _ : Fin q ↦ M ⧸ S) N := by
  classical
  let rep : (Fin q → M ⧸ S) → (Fin q → M) :=
    fun x i ↦ Quotient.out (x i)
  have bridge (x : Fin q → M ⧸ S) (y : Fin q → M)
      (hy : ∀ i, S.mkQ (y i) = x i) : f (rep x) = f y := by
    apply multilinear_eq_of_sub_mem S f hzero
    intro i
    apply (Submodule.Quotient.eq S).mp
    exact (Submodule.Quotient.mk_out _).trans (hy i).symm
  exact
    { toFun := fun x ↦ f (rep x)
      map_update_add' := by
        intro _ x i a b
        let ya := Function.update (rep x) i (Quotient.out a)
        let yb := Function.update (rep x) i (Quotient.out b)
        let yab := Function.update (rep x) i (Quotient.out a + Quotient.out b)
        calc
          f (rep (Function.update x i (a + b))) = f yab := bridge _ _ (by
            intro j
            by_cases hji : j = i
            · subst j
              simp [yab]
            · simp [yab, rep, hji])
          _ = f ya + f yb := by
            exact f.map_update_add (rep x) i (Quotient.out a) (Quotient.out b)
          _ = f (rep (Function.update x i a)) +
              f (rep (Function.update x i b)) := congrArg₂ (.+.)
                (bridge _ _ (by
                  intro j
                  by_cases hji : j = i
                  · subst j; simp [ya]
                  · simp [ya, rep, hji])).symm
                (bridge _ _ (by
                  intro j
                  by_cases hji : j = i
                  · subst j; simp [yb]
                  · simp [yb, rep, hji])).symm
      map_update_smul' := by
        intro _ x i z a
        let ya := Function.update (rep x) i (Quotient.out a)
        let yza := Function.update (rep x) i
          (z • Quotient.out a)
        calc
          f (rep (Function.update x i (z • a))) = f yza := bridge _ _ (by
            intro j
            by_cases hji : j = i
            · subst j
              simp [yza, rep]
            · simp [yza, rep, hji])
          _ = z • f ya := by
            calc
              f (Function.update (rep x) i (z • Quotient.out a)) =
                  f (Function.update (rep x) i
                    ((inferInstance : Module ℤ M).smul z (Quotient.out a))) := by
                      congr 2
                      exact (int_smul_eq_zsmul
                        (inferInstance : Module ℤ M) z (Quotient.out a)).symm
              _ = (inferInstance : Module ℤ N).smul z
                    (f (Function.update (rep x) i (Quotient.out a))) :=
                f.map_update_smul (rep x) i z (Quotient.out a)
              _ = z • f (Function.update (rep x) i (Quotient.out a)) :=
                int_smul_eq_zsmul (inferInstance : Module ℤ N) _ _
          _ = z • f (rep (Function.update x i a)) := by
            have hrep : f ya = f (rep (Function.update x i a)) := (bridge _ _ (by
              intro j
              by_cases hji : j = i
              · subst j; simp [ya]
              · simp [ya, rep, hji])).symm
            rw [hrep]
        exact (int_smul_eq_zsmul (inferInstance : Module ℤ N) _ _).symm }

private theorem descendMultilinear_mk
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {q : ℕ}
    (S : Submodule ℤ M) (f : MultilinearMap ℤ (fun _ : Fin q ↦ M) N)
    (hzero : ∀ (x : Fin q → M) (i : Fin q), x i ∈ S → f x = 0)
    (x : Fin q → M) :
    descendMultilinear S f hzero (fun i ↦ S.mkQ (x i)) = f x := by
  apply multilinear_eq_of_sub_mem S f hzero
  intro i
  apply (Submodule.Quotient.eq S).mp
  exact Submodule.Quotient.mk_out _

private theorem descendMultilinear_symmetric
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {q : ℕ}
    (S : Submodule ℤ M) (f : MultilinearMap ℤ (fun _ : Fin q ↦ M) N)
    (hzero : ∀ (x : Fin q → M) (i : Fin q), x i ∈ S → f x = 0)
    (hsym : SymmetricPower.IsSymmetric f) :
    SymmetricPower.IsSymmetric (descendMultilinear S f hzero) := by
  intro e x
  exact hsym e (fun i ↦ Quotient.out (x i))

private def topBracketOnV (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L) →ₗ[ℤ]
      MultilinearMap ℤ (fun _ : Fin (n + 1 - k) ↦ V L k)
        (lowerCentralSeries ℤ L n : Submodule ℤ L) :=
  { toFun := fun d ↦ descendMultilinear
      (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L)
      (rawTopBracket (n := n) (L := L) data k hk hkn d)
      (fun x i hi ↦ rawTopBracket_eq_zero_of_tooth_next
        (n := n) (L := L) data k hk hkn d x i hi),
    map_add' := by
      intro a b
      apply MultilinearMap.ext
      intro x
      change (rawTopBracket (n := n) (L := L) data k hk hkn (a + b)
        (fun i ↦ Quotient.out (x i))) = _
      rw [map_add, MultilinearMap.add_apply]
      rfl
    map_smul' := by
      intro z a
      apply MultilinearMap.ext
      intro x
      change (rawTopBracket (n := n) (L := L) data k hk hkn (z • a)
        (fun i ↦ Quotient.out (x i))) = _
      rw [map_smul, MultilinearMap.smul_apply]
      rfl }

private theorem topBracketOnV_symmetric (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (d : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L)) :
    SymmetricPower.IsSymmetric (topBracketOnV n L data k hk hkn d) :=
  descendMultilinear_symmetric _ _
    (fun x i hi ↦ rawTopBracket_eq_zero_of_tooth_next
      (n := n) (L := L) data k hk hkn d x i hi) (by
    intro e x
    apply Subtype.ext
    exact rawBracket_symmetric (n := n) (L := L) data _
      (lcsToDerived L k hk d) e x)

private def topBracketOnU (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    U L k →ₗ[ℤ] MultilinearMap ℤ (fun _ : Fin (n + 1 - k) ↦ V L k)
      (lowerCentralSeries ℤ L n : Submodule ℤ L) :=
  ((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
      (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).liftQ
    (topBracketOnV n L data k hk hkn) (by
      intro d hd
      apply MultilinearMap.ext
      intro x
      apply Subtype.ext
      exact congrArg Subtype.val
        (rawTopBracket_eq_zero_of_head_next (n := n) (L := L)
          data k hk hkn d hd (fun i ↦ Quotient.out (x i))))

private theorem topBracketOnU_symmetric (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (d : U L k) : SymmetricPower.IsSymmetric
      (topBracketOnU n L data k hk hkn d) := by
  induction d using Submodule.Quotient.induction_on with
  | _ d => exact topBracketOnV_symmetric n L data k hk hkn d

private def topBracketSymmetric (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    U L k →ₗ[ℤ] Sym[ℤ] (Fin (n + 1 - k)) (V L k) →ₗ[ℤ]
      (lowerCentralSeries ℤ L n : Submodule ℤ L) :=
  { toFun := fun d ↦ SymmetricPower.lift (topBracketOnU n L data k hk hkn d)
      (topBracketOnU_symmetric n L data k hk hkn d)
    map_add' := by
      intro a b
      apply SymmetricPower.linearMap_ext
      intro x
      simp only [SymmetricPower.lift_tprod]
      change (topBracketOnU n L data k hk hkn (a + b)) x = _
      rw [map_add, MultilinearMap.add_apply, LinearMap.add_apply,
        SymmetricPower.lift_tprod, SymmetricPower.lift_tprod]
    map_smul' := by
      intro z a
      apply SymmetricPower.linearMap_ext
      intro x
      simp only [SymmetricPower.lift_tprod]
      change (topBracketOnU n L data k hk hkn (z • a)) x = _
      rw [map_smul, MultilinearMap.smul_apply, LinearMap.smul_apply,
        SymmetricPower.lift_tprod]
      simp only [RingHom.id_apply] }

/-- The manuscript long-bracket pairing
`U_k ⊗ Sym^(n+1-k)(V_k) → ZMod(2^e)`. -/
def Theta (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    U L k ⊗[ℤ] Sym[ℤ] (Fin (n + 1 - k)) (V L k) →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
  data.topEquiv.toIntLinearEquiv.toLinearMap.comp
    (TensorProduct.lift (topBracketSymmetric n L data k hk hkn))

@[simp]
theorem Theta_tmul_tprod (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (d : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L))
    (x : Fin (n + 1 - k) → L) :
    Theta n L data k hk hkn
        (((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
          (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).mkQ d ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun i ↦
            (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ (x i))) =
      data.topEquiv (rawTopBracket (n := n) (L := L) data k hk hkn d x) := by
  rw [Theta, LinearMap.comp_apply]
  change data.topEquiv
      ((topBracketSymmetric n L data k hk hkn
        (((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
          (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).mkQ d))
        (SymmetricPower.tprod ℤ (fun i ↦
          (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ (x i)))) = _
  change data.topEquiv
      ((SymmetricPower.lift
        (topBracketOnU n L data k hk hkn
          (((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
            (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).mkQ d))
        (topBracketOnU_symmetric n L data k hk hkn _))
        (SymmetricPower.tprod ℤ (fun i ↦
          (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ (x i)))) = _
  rw [SymmetricPower.lift_tprod]
  change data.topEquiv
      (descendMultilinear _
        (rawTopBracket (n := n) (L := L) data k hk hkn d)
        (fun x i hi ↦ rawTopBracket_eq_zero_of_tooth_next
          (n := n) (L := L) data k hk hkn d x i hi)
        (fun i ↦ (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ (x i))) = _
  apply congrArg data.topEquiv
  exact descendMultilinear_mk _ _ _ x

/-- At the terminal stage, the representative-level construction is the
literal one-tooth Lie bracket. -/
private theorem rawTopBracket_terminal_val (hn : 2 ≤ n)
    (z : L) (hz : z ∈ lowerCentralSeries ℤ L (n - 1)) (y : L) :
    (rawTopBracket (n := n) (L := L) data n hn le_rfl
      ⟨z, hz⟩ (fun _ ↦ y) : L) = ⁅z, y⁆ := by
  change rawBracket (n := n) (L := L) data (n + 1 - n)
      (lcsToDerived L n hn ⟨z, hz⟩) (fun _ ↦ y) = ⁅z, y⁆
  rw [show n + 1 - n = 1 by omega]
  simp only [rawBracket, FreeMetabelian.Evaluation.actionMultilinear,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, one_mul]
  rfl

/-- Public one-tooth evaluation of the terminal pairing. -/
theorem Theta_terminal_tmul (hn : 2 ≤ n)
    (z : L) (hz : z ∈ lowerCentralSeries ℤ L (n - 1)) (y : L) :
    Theta n L data n hn le_rfl
        (((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
          (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
            ⟨z, hz⟩ ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun _ : Fin (n + 1 - n) ↦
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ y)) =
      data.topEquiv ⟨⁅z, y⁆, by
        have hbr : ⁅z, y⁆ ∈ lowerCentralSeries ℤ L ((n - 1) + 1) := by
          change ⁅z, y⁆ ∈ LieModule.lowerCentralSeries ℤ L L ((n - 1) + 1)
          rw [LieModule.lowerCentralSeries_succ ℤ L L (n - 1),
            LieSubmodule.lie_comm]
          exact LieSubmodule.lie_mem_lie hz (by simp)
        have heq : n - 1 + 1 = n := by omega
        have hseries : lowerCentralSeries ℤ L (n - 1 + 1) =
            lowerCentralSeries ℤ L n := congrArg (lowerCentralSeries ℤ L) heq
        rw [← hseries]
        exact hbr⟩ := by
  rw [Theta_tmul_tprod]
  apply congrArg data.topEquiv
  apply Subtype.ext
  exact rawTopBracket_terminal_val n L data hn z hz y

/-- At the terminal stage `k=n`, `Theta` is the one-tooth bracket.  This is
the exact scaled skew identity used to choose the manuscript's integral
upper-triangular lift. -/
theorem Theta_terminal_scaled_skew (hn : 2 ≤ n)
    (z w : ℤ) (x y : L)
    (hz : z • x ∈ lowerCentralSeries ℤ L (n - 1))
    (hw : w • y ∈ lowerCentralSeries ℤ L (n - 1)) :
    w • Theta n L data n hn le_rfl
        (((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
          ⟨z • x, hz⟩ ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun _ : Fin (n + 1 - n) ↦
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ y)) +
      z • Theta n L data n hn le_rfl
        (((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
          ⟨w • y, hw⟩ ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun _ : Fin (n + 1 - n) ↦
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ x)) = 0 := by
  rw [Theta_tmul_tprod, Theta_tmul_tprod]
  have htop :
      w • rawTopBracket (n := n) (L := L) data n hn le_rfl
          ⟨z • x, hz⟩ (fun _ ↦ y) +
        z • rawTopBracket (n := n) (L := L) data n hn le_rfl
          ⟨w • y, hw⟩ (fun _ ↦ x) = 0 := by
    apply Subtype.ext
    change w • (rawTopBracket (n := n) (L := L) data n hn le_rfl
        ⟨z • x, hz⟩ (fun _ ↦ y) : L) +
      z • (rawTopBracket (n := n) (L := L) data n hn le_rfl
        ⟨w • y, hw⟩ (fun _ ↦ x) : L) = 0
    rw [rawTopBracket_terminal_val, rawTopBracket_terminal_val]
    rw [zsmul_lie, zsmul_lie, ← lie_skew x y]
    module
  calc
    w • data.topEquiv _ + z • data.topEquiv _ =
        data.topEquiv (w • rawTopBracket (n := n) (L := L) data n hn le_rfl
          ⟨z • x, hz⟩ (fun _ ↦ y) +
          z • rawTopBracket (n := n) (L := L) data n hn le_rfl
            ⟨w • y, hw⟩ (fun _ ↦ x)) := by
      change w • data.topEquiv.toIntLinearEquiv.toLinearMap _ +
          z • data.topEquiv.toIntLinearEquiv.toLinearMap _ =
        data.topEquiv.toIntLinearEquiv.toLinearMap (w • _ + z • _)
      rw [map_add, map_zsmul, map_zsmul]
    _ = data.topEquiv 0 := congrArg data.topEquiv htop
    _ = 0 := data.topEquiv.map_zero

/-- The divided form of terminal skew-symmetry used by ordered Smith
coordinates.  Unlike cancellation in `ZMod`, this is an integral identity in
the Lie ring before applying the top coordinate. -/
theorem Theta_terminal_ratio_skew (hn : 2 ≤ n)
    (z r : ℤ) (x y : L)
    (hz : z • x ∈ lowerCentralSeries ℤ L (n - 1))
    (hry : (r * z) • y ∈ lowerCentralSeries ℤ L (n - 1)) :
    Theta n L data n hn le_rfl
        (((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
          ⟨(r * z) • y, hry⟩ ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun _ : Fin (n + 1 - n) ↦
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ x)) =
      -r • Theta n L data n hn le_rfl
        (((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
          ⟨z • x, hz⟩ ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun _ : Fin (n + 1 - n) ↦
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ y)) := by
  rw [Theta_tmul_tprod, Theta_tmul_tprod]
  have htop : rawTopBracket (n := n) (L := L) data n hn le_rfl
        ⟨(r * z) • y, hry⟩ (fun _ ↦ x) =
      -r • rawTopBracket (n := n) (L := L) data n hn le_rfl
        ⟨z • x, hz⟩ (fun _ ↦ y) := by
    apply Subtype.ext
    change (rawTopBracket (n := n) (L := L) data n hn le_rfl
        ⟨(r * z) • y, hry⟩ (fun _ ↦ x) : L) =
      -r • (rawTopBracket (n := n) (L := L) data n hn le_rfl
        ⟨z • x, hz⟩ (fun _ ↦ y) : L)
    rw [rawTopBracket_terminal_val, rawTopBracket_terminal_val]
    rw [zsmul_lie, zsmul_lie, ← lie_skew x y]
    module
  calc
    data.topEquiv _ = data.topEquiv (-r •
        rawTopBracket (n := n) (L := L) data n hn le_rfl
          ⟨z • x, hz⟩ (fun _ ↦ y)) := congrArg data.topEquiv htop
    _ = -r • data.topEquiv _ := by
      change data.topEquiv.toIntLinearEquiv.toLinearMap (-r • _) = _
      exact map_zsmul data.topEquiv.toIntLinearEquiv.toLinearMap _ _

/-- The terminal one-tooth bracket vanishes when its head is an integral
multiple of the tooth. -/
theorem Theta_terminal_same_zero (hn : 2 ≤ n)
    (z : ℤ) (x : L)
    (hz : z • x ∈ lowerCentralSeries ℤ L (n - 1)) :
    Theta n L data n hn le_rfl
        (((lowerCentralSeries ℤ L n : Submodule ℤ L).comap
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype).mkQ
          ⟨z • x, hz⟩ ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun _ : Fin (n + 1 - n) ↦
            (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ x)) = 0 := by
  rw [Theta_tmul_tprod]
  have htop : rawTopBracket (n := n) (L := L) data n hn le_rfl
      ⟨z • x, hz⟩ (fun _ ↦ x) = 0 := by
    apply Subtype.ext
    change (rawTopBracket (n := n) (L := L) data n hn le_rfl
      ⟨z • x, hz⟩ (fun _ ↦ x) : L) = 0
    rw [rawTopBracket_terminal_val, zsmul_lie, lie_self, smul_zero]
  rw [htop]
  exact data.topEquiv.map_zero

/-! ### The nonterminal cocycle -/

private def thetaNonterminal (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    U L k ⊗[ℤ] Sym[ℤ] (Fin (n - k + 1)) (V L k) →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
  (Theta n L data k hk hkn.le).comp
    (TensorProduct.map LinearMap.id
      (SymmetricPower.reindex (R := ℤ)
        (Fin.castOrderIso (by omega : n - k + 1 = n + 1 - k)).toEquiv))

@[simp] private theorem thetaNonterminal_tmul_tprod
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (d : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L))
    (x : Fin (n - k + 1) → L) :
    thetaNonterminal n L data k hk hkn
        (((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
            (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).mkQ d
          ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun j ↦
            (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ (x j))) =
      data.topEquiv
        (rawTopBracket (n := n) (L := L) data k hk hkn.le d
          (fun j ↦ x ((Fin.castOrderIso
            (by omega : n - k + 1 = n + 1 - k)).symm j))) := by
  unfold thetaNonterminal
  rw [LinearMap.comp_apply]
  change Theta n L data k hk hkn.le
      ((TensorProduct.map LinearMap.id
        (SymmetricPower.reindex (R := ℤ)
          (Fin.castOrderIso (by omega : n - k + 1 = n + 1 - k)).toEquiv))
        (_ ⊗ₜ[ℤ] _)) = _
  rw [TensorProduct.map_tmul,
    SymmetricPower.reindex_tprod]
  change Theta n L data k hk hkn.le
      (((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
          (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).mkQ d
        ⊗ₜ[ℤ] SymmetricPower.tprod ℤ (fun j ↦
          (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ
            (x ((Fin.castOrderIso (by omega : n - k + 1 = n + 1 - k)).symm j)))) = _
  rw [Theta_tmul_tprod]

private def phiCore (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.One (presentation (n := n) L data (k - 1) (by omega) (by omega))
        (n - k + 1) →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  -(thetaNonterminal n L data k hk hkn).comp
    (TensorProduct.map (extensionTail n L data k hk (by omega))
      (SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
        (augmentation (n := n) L data (k - 1))))

/-- The manuscript cochain `Phi_k` on degree one. -/
def Phi (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.One (presentation (n := n) L data (k - 1) (by omega) (by omega))
        (n - k + 1) →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  phiCore n L data k hk hkn

@[simp]
theorem Phi_tmul_tprod (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (a : D n L data (k - 1) (by omega))
    (x : Fin (n - k + 1) → A L (k - 1)) :
    Phi n L data k hk hkn (a ⊗ₜ[ℤ] SymmetricPower.tprod ℤ x) =
      -thetaNonterminal n L data k hk hkn
        (extensionTail n L data k hk (by omega) a ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ
            (fun i ↦ augmentation (n := n) L data (k - 1) (x i))) := by
  change (-thetaNonterminal n L data k hk hkn)
      ((TensorProduct.map (extensionTail n L data k hk (by omega))
        (SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
          (augmentation (n := n) L data (k - 1))))
        (a ⊗ₜ[ℤ] SymmetricPower.tprod ℤ x)) = _
  rw [TensorProduct.map_tmul, SymmetricPower.map_tprod]
  rfl

private theorem Phi_dTwo_wedge_tmul_zero
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (a : Fin 2 → D n L data (k - 1) (by omega))
    (s : Sym[ℤ] (Fin (n - k)) (A L (k - 1))) :
    Phi n L data k hk hkn
      (a 0 ⊗ₜ[ℤ] SymmetricPower.insert ℤ (A L (k - 1)) (n - k)
            ((presentation (n := n) L data (k - 1) (by omega) (by omega)).d
              (a 1)) s -
          a 1 ⊗ₜ[ℤ] SymmetricPower.insert ℤ (A L (k - 1)) (n - k)
            ((presentation (n := n) L data (k - 1) (by omega) (by omega)).d
              (a 0)) s) = 0 := by
  change phiCore n L data k hk hkn (_ - _) = 0
  rw [map_sub]
  change -thetaNonterminal n L data k hk hkn
        (extensionTail n L data k hk (by omega) (a 0) ⊗ₜ[ℤ]
          SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
            (augmentation (n := n) L data (k - 1))
            (SymmetricPower.insert ℤ (A L (k - 1)) (n - k)
              ((presentation (n := n) L data (k - 1) (by omega) (by omega)).d
                (a 1)) s)) -
      -thetaNonterminal n L data k hk hkn
        (extensionTail n L data k hk (by omega) (a 1) ⊗ₜ[ℤ]
          SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
            (augmentation (n := n) L data (k - 1))
            (SymmetricPower.insert ℤ (A L (k - 1)) (n - k)
              ((presentation (n := n) L data (k - 1) (by omega) (by omega)).d
                (a 0)) s)) = 0
  have hzero (r : D n L data (k - 1) (by omega)) :
      augmentation (n := n) L data (k - 1)
        ((presentation (n := n) L data (k - 1) (by omega) (by omega)).d r) = 0 :=
    (presentation (n := n) L data (k - 1) (by omega) (by omega)).augmentation_d r
  have hmap (r : D n L data (k - 1) (by omega)) :
      SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
          (augmentation (n := n) L data (k - 1))
          (SymmetricPower.insert ℤ (A L (k - 1)) (n - k)
            ((presentation (n := n) L data (k - 1) (by omega) (by omega)).d r) s) =
        SymmetricPower.insert ℤ (W L (k - 1)) (n - k)
          (augmentation (n := n) L data (k - 1)
            ((presentation (n := n) L data (k - 1) (by omega) (by omega)).d r))
          (SymmetricPower.map (R := ℤ) (ι := Fin (n - k))
            (augmentation (n := n) L data (k - 1)) s) := by
    exact LinearMap.congr_fun (SymmetricPower.map_insert
      (R₀ := ℤ) (M₀ := A L (k - 1)) (N₀ := W L (k - 1))
      (augmentation (n := n) L data (k - 1)) (n - k) _) s
  rw [hmap (a 1), hmap (a 0)]
  rw [hzero (a 1), hzero (a 0)]
  simp

/-- `Phi_k` annihilates every degree-two Koszul boundary. -/
theorem Phi_comp_dTwo (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    (Phi n L data k hk hkn).comp
      (Koszul.dTwo
        (presentation (n := n) L data (k - 1) (by omega) (by omega))
        (n - k)) = 0 := by
  let P := presentation (n := n) L data (k - 1) (by omega) (by omega)
  change (Phi n L data k hk hkn).comp (Koszul.dTwo P (n - k)) = 0
  apply TensorProduct.ext'
  intro w s
  let f : (⋀[ℤ]^2 P.rel) →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
    ((Phi n L data k hk hkn).comp
      (Koszul.dTwo P (n - k))).comp
        ((TensorProduct.mk ℤ (⋀[ℤ]^2 P.rel) _).flip s)
  have hf : f = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    change Phi n L data k hk hkn
      (Koszul.dTwo P (n - k)
        (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s)) = 0
    rw [Koszul.dTwo_wedge_tmul]
    exact Phi_dTwo_wedge_tmul_zero n L data k hk hkn a s
  have hw := LinearMap.congr_fun hf w
  simpa [f, LinearMap.comp_apply] using hw

/-- Restriction of `Phi_k` to cycles. -/
def PhiCycles (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.cyclesOne
        (presentation (n := n) L data (k - 1) (by omega) (by omega))
        (n - k + 1) →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  (Phi n L data k hk hkn).domRestrict _

private theorem boundaries_le_ker_PhiCycles
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.boundariesOne
        (presentation (n := n) L data (k - 1) (by omega) (by omega))
        (n - k + 1) ≤ LinearMap.ker (PhiCycles n L data k hk hkn) := by
  intro c hc
  rcases hc with ⟨z, rfl⟩
  let P := presentation (n := n) L data (k - 1) (by omega) (by omega)
  have hq : n - k + 1 = (n - k) + 1 := rfl
  change Phi n L data k hk hkn
      (Koszul.boundaryMapOne P (n - k + 1) z).1 = 0
  rw [Koszul.boundaryMapOne_succ_val]
  exact LinearMap.congr_fun (Phi_comp_dTwo n L data k hk hkn) z

/-- The finite, exact version of the nonterminal character. -/
def etaFinite (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.FirstDerivedSymmetricPower (n - k + 1) (V L k) →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
  ((Koszul.boundariesOne
    (presentation (n := n) L data (k - 1) (by omega) (by omega))
    (n - k + 1)).liftQ (PhiCycles n L data k hk hkn)
      (boundaries_le_ker_PhiCycles n L data k hk hkn)).comp
    ((Koszul.Presentation.homologyComparisonEquiv
      (presentation (n := n) L data (k - 1) (by omega) (by omega))
      (n - k + 1)).symm.toLinearMap)

/-- The manuscript character `eta_k : L₁S^(n+2-k)(V_k) → ℚ/ℤ`. -/
def eta (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Koszul.FirstDerivedSymmetricPower (n - k + 1) (V L k) →ₗ[ℤ]
  LieRings.RatCircle :=
  (LieRings.zmodToRatCircle (2 ^ data.exponent)).toIntLinearMap.comp
    (etaFinite n L data k hk hkn)

/-! ### The literal chain transgression -/

/-- The new weight-`k` coordinate of `A_k`, interpreted in `U_k`. -/
def transgressionHead (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    A L k →ₗ[ℤ] U L k :=
  (pieceToU (n := n) L data k (by omega)).comp
    (FreeMetabelian.Free.weightProject (X := Generator L) (k - 1) (by omega))

/-- The old prefix of `A_k`, evaluated in `V_k`. -/
def transgressionTooth (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    A L k →ₗ[ℤ] V L k :=
  (augmentation (n := n) L data (k - 1)).comp
    (FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k (by omega))

/-- The manuscript cochain `T_k`: choose each factor in turn for the new
weight-`k` slot and put all remaining factors in the old prefix. -/
def T (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    Sym[ℤ] (Fin (n - k + 2)) (A L k) →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  SymmetricPower.polarize (N₀ := ZMod (2 ^ data.exponent)) (n - k + 1)
    (transgressionHead n L data k hk hkn)
    (transgressionTooth n L data k hk hkn)
    (thetaNonterminal n L data k hk hkn)

@[simp]
theorem T_tprod (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (x : Fin (n - k + 2) → A L k) :
    T n L data k hk hkn (SymmetricPower.tprod ℤ x) = ∑ i,
      thetaNonterminal n L data k hk hkn
        (transgressionHead n L data k hk hkn (x i) ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun j ↦
            transgressionTooth n L data k hk hkn (i.removeNth x j))) := by
  change SymmetricPower.polarize (n - k + 1)
      (transgressionHead n L data k hk hkn)
      (transgressionTooth n L data k hk hkn)
      (thetaNonterminal n L data k hk hkn)
      (SymmetricPower.tprod ℤ x) = _
  exact SymmetricPower.polarize_tprod _ _ _ _ x

private theorem transgressionHead_weightIncl_eq_zero_of_ne
    (k s : ℕ) (hk : 2 ≤ k) (hkn : k < n) (hs : s < k)
    (hsk : s ≠ k - 1)
    (x : FreeMetabelian.Piece (Generator L) s) :
    transgressionHead n L data k hk hkn
        (FreeMetabelian.Free.weightIncl s hs x) = 0 := by
  change pieceToU (n := n) L data k (by omega)
      (FreeMetabelian.Free.weightProject (X := Generator L)
        (k - 1) (by omega)
        (FreeMetabelian.Free.weightIncl s hs x)) = 0
  rw [FreeMetabelian.Free.weightProject,
    FreeMetabelian.Free.weightIncl]
  change pieceToU (n := n) L data k (by omega)
      (FreeMetabelian.Free.incl (⟨s, hs⟩ : Fin k) x
        (⟨k - 1, by omega⟩ : Fin k)) = 0
  rw [FreeMetabelian.Free.incl_apply_of_ne]
  · exact map_zero _
  · intro h
    apply hsk
    exact congrArg Fin.val h.symm

private theorem transgressionTooth_weightIncl_eq_zero
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (x : FreeMetabelian.Piece (Generator L) (k - 1)) :
    transgressionTooth n L data k hk hkn
        (FreeMetabelian.Free.weightIncl (k - 1) (by omega) x) = 0 := by
  change augmentation (n := n) L data (k - 1)
      (FreeMetabelian.Free.projectPrefix (X := Generator L) (k - 1)
        (by omega)
        (FreeMetabelian.Free.weightIncl (k - 1) (by omega) x)) = 0
  rw [FreeMetabelian.Free.projectPrefix_weightIncl_eq_zero
    (c := k) (k - 1) (k - 1) (by omega) (by omega) le_rfl]
  exact map_zero _

private theorem transgressionTooth_weightIncl_eq_zero_of_eq
    (k s : ℕ) (hk : 2 ≤ k) (hkn : k < n) (hs : s < k)
    (h : s = k - 1)
    (x : FreeMetabelian.Piece (Generator L) s) :
    transgressionTooth n L data k hk hkn
        (FreeMetabelian.Free.weightIncl s hs x) = 0 := by
  subst s
  exact transgressionTooth_weightIncl_eq_zero n L data k hk hkn x

private theorem transgressionTooth_weightIncl_of_lt
    (k s : ℕ) (hk : 2 ≤ k) (hkn : k < n) (hs : s < k - 1)
    (x : FreeMetabelian.Piece (Generator L) s) :
    transgressionTooth n L data k hk hkn
        (FreeMetabelian.Free.weightIncl s (by omega) x) =
      (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ
        (FreeMetabelian.Evaluation.pieceEval data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) s x) := by
  change augmentation (n := n) L data (k - 1)
      (FreeMetabelian.Free.projectPrefix (X := Generator L) (k - 1)
        (by omega) (FreeMetabelian.Free.weightIncl s (by omega) x)) = _
  change (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ
      (FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (k - 1)
        (FreeMetabelian.Free.projectPrefix (X := Generator L) (k - 1)
          (by omega) (FreeMetabelian.Free.weightIncl s (by omega) x))) = _
  have hp : FreeMetabelian.Free.projectPrefix (X := Generator L) (k - 1)
      (by omega) (FreeMetabelian.Free.weightIncl (c := k) s (by omega) x) =
      FreeMetabelian.Free.weightIncl (c := k - 1) s hs x := by
    funext i
    rw [FreeMetabelian.Free.projectPrefix_apply]
    change (FreeMetabelian.Free.incl (⟨s, by omega⟩ : Fin k) x)
        (⟨i.val, by omega⟩ : Fin k) =
      (FreeMetabelian.Free.incl (⟨s, hs⟩ : Fin (k - 1)) x) i
    by_cases hi : i.val = s
    · let il : Fin k := ⟨i.val, by omega⟩
      let sl : Fin k := ⟨s, by omega⟩
      have hil : il = sl := Fin.ext hi
      let sr : Fin (k - 1) := ⟨s, hs⟩
      have hir : i = sr := Fin.ext hi
      change (FreeMetabelian.Free.incl sl x) il =
        (FreeMetabelian.Free.incl sr x) i
      subst il
      subst i
      rw [FreeMetabelian.Free.incl_apply_same,
        FreeMetabelian.Free.incl_apply_same]
    · rw [FreeMetabelian.Free.incl_apply_of_ne,
        FreeMetabelian.Free.incl_apply_of_ne]
      · intro h
        exact hi (congrArg Fin.val h)
      · intro h
        exact hi (congrArg Fin.val h)
  rw [hp]
  apply congrArg (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ
  exact FreeMetabelian.Evaluation.linear_incl data.metabelian
    (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (⟨s, hs⟩ : Fin (k - 1)) x

private theorem pieceEval_mem_derived_of_pos
    (s : ℕ) (hs : 0 < s)
    (x : FreeMetabelian.Piece (Generator L) s) :
    FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) s x ∈
      LieAlgebra.derivedSeries ℤ L 1 := by
  rw [derived_eq_lowerCentralSeries_one L]
  cases s with
  | zero => omega
  | succ q =>
      exact LieModule.antitone_lowerCentralSeries ℤ L L (by omega)
        (FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
          data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) q x)

private theorem thetaNonterminal_tmul_tprod_eq_zero_of_derived_tooth
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (d : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L))
    (x : Fin (n - k + 1) → L) (i : Fin (n - k + 1))
    (hi : x i ∈ LieAlgebra.derivedSeries ℤ L 1) :
    thetaNonterminal n L data k hk hkn
        (((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
            (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).mkQ d
          ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun j ↦
            (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ (x j))) = 0 := by
  rw [thetaNonterminal_tmul_tprod]
  let e := (Fin.castOrderIso
    (by omega : n - k + 1 = n + 1 - k)).toEquiv
  let i' : Fin (n + 1 - k) := e i
  have hi' : x (e.symm i') ∈ LieAlgebra.derivedSeries ℤ L 1 := by
    simpa [i'] using hi
  have hz : rawTopBracket (n := n) (L := L) data k hk hkn.le d
      (fun j ↦ x (e.symm j)) = 0 := by
    apply Subtype.ext
    exact rawBracket_eq_zero_of_derived_tooth
      (n := n) (L := L) data k (n + 1 - k) hk d
      (fun j ↦ x (e.symm j)) i' hi'
  change data.topEquiv
      (rawTopBracket (n := n) (L := L) data k hk hkn.le d
        (fun j ↦ x (e.symm j))) = 0
  rw [hz]
  exact data.topEquiv.map_zero

private theorem T_homogeneous_eq_zero_of_not_shape
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (s : Fin (n - k + 2) → Fin k)
    (x : ∀ i, FreeMetabelian.Piece (Generator L) (s i).val)
    (hshape : ¬ ∃! i,
      (s i).val = k - 1 ∧ ∀ j, j ≠ i → (s j).val = 0) :
    T n L data k hk hkn
      (SymmetricPower.tprod ℤ (fun i ↦
        FreeMetabelian.Free.weightIncl (s i).val (s i).isLt (x i))) = 0 := by
  classical
  rw [T_tprod]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : (s i).val = k - 1
  · have hothers : ¬ ∀ j, j ≠ i → (s j).val = 0 := by
      intro hall
      apply hshape
      refine ⟨i, ⟨hi, hall⟩, ?_⟩
      intro j hj
      by_contra hji
      have hjzero := hall j hji
      have hjtop := hj.1
      omega
    push_neg at hothers
    obtain ⟨j, hji, hj⟩ := hothers
    have hjpos : 0 < (s j).val := Nat.pos_of_ne_zero hj
    by_cases hjtop : (s j).val = k - 1
    · have hremove : ∃ r : Fin (n - k + 1), i.succAbove r = j :=
        Fin.exists_succAbove_eq hji
      obtain ⟨r, hr⟩ := hremove
      have htooth : transgressionTooth n L data k hk hkn
          (i.removeNth (fun t ↦
            FreeMetabelian.Free.weightIncl (s t).val (s t).isLt (x t)) r) = 0 := by
        change transgressionTooth n L data k hk hkn
          (FreeMetabelian.Free.weightIncl (s (i.succAbove r)).val
            (s (i.succAbove r)).isLt (x (i.succAbove r))) = 0
        subst j
        exact transgressionTooth_weightIncl_eq_zero_of_eq n L data k
          (s (i.succAbove r)).val hk hkn (s (i.succAbove r)).isLt hjtop
          (x (i.succAbove r))
      have htprod : SymmetricPower.tprod ℤ (fun j ↦
          transgressionTooth n L data k hk hkn
            (i.removeNth (fun t ↦
              FreeMetabelian.Free.weightIncl (s t).val (s t).isLt (x t)) j)) = 0 := by
        exact (SymmetricPower.tprod ℤ).map_coord_zero r htooth
      rw [htprod, TensorProduct.tmul_zero, map_zero]
    · have hjlt : (s j).val < k - 1 := by omega
      let y : Fin (n - k + 1) → L := fun r ↦
        if (s (i.succAbove r)).val = k - 1 then 0 else
          FreeMetabelian.Evaluation.pieceEval data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
            (s (i.succAbove r)).val (x (i.succAbove r))
      have hteeth : (fun r ↦ transgressionTooth n L data k hk hkn
          (i.removeNth (fun t ↦
            FreeMetabelian.Free.weightIncl (s t).val (s t).isLt (x t)) r)) =
          fun r ↦ (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ (y r) := by
        funext r
        by_cases hs' : (s (i.succAbove r)).val = k - 1
        · simp only [y, hs', if_pos, map_zero]
          exact transgressionTooth_weightIncl_eq_zero_of_eq n L data k
            (s (i.succAbove r)).val hk hkn (s (i.succAbove r)).isLt hs'
            (x (i.succAbove r))
        · have hslt : (s (i.succAbove r)).val < k - 1 := by omega
          simp only [y, hs', if_neg]
          exact transgressionTooth_weightIncl_of_lt n L data k
            (s (i.succAbove r)).val hk hkn hslt (x (i.succAbove r))
      rw [hteeth]
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hji
      have hyr : y r ∈ LieAlgebra.derivedSeries ℤ L 1 := by
        subst j
        simp only [y, hjtop, if_false]
        exact pieceEval_mem_derived_of_pos n L data
          (s (i.succAbove r)).val hjpos (x (i.succAbove r))
      induction transgressionHead n L data k hk hkn
          (FreeMetabelian.Free.weightIncl (s i).val (s i).isLt (x i))
        using Submodule.Quotient.induction_on with
      | _ d =>
        exact thetaNonterminal_tmul_tprod_eq_zero_of_derived_tooth
          n L data k hk hkn d y r hyr
  · rw [transgressionHead_weightIncl_eq_zero_of_ne
      n L data k (s i).val hk hkn (s i).isLt hi]
    simp

/-- Exact homogeneous support of the chain transgression.  The zero-based
piece index `0` is manuscript weight one and `k-1` is manuscript weight `k`.
Thus a nonzero pure value has one and only one weight-`k` input and all its
other inputs have weight one. -/
theorem T_homogeneous_ne_zero_shape
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (s : Fin (n - k + 2) → Fin k)
    (x : ∀ i, FreeMetabelian.Piece (Generator L) (s i).val)
    (hT : T n L data k hk hkn
      (SymmetricPower.tprod ℤ (fun i ↦
        FreeMetabelian.Free.weightIncl (s i).val (s i).isLt (x i))) ≠ 0) :
    ∃! i, (s i).val = k - 1 ∧ ∀ j, j ≠ i → (s j).val = 0 := by
  by_contra hshape
  exact hT (T_homogeneous_eq_zero_of_not_shape n L data k hk hkn s x hshape)

/-- A manuscript-weight-one input whose evaluation is already derived kills
the only homogeneous shape on which `T` can be nonzero.  Indeed the unique
weight-`k` input must be a different coordinate, so the distinguished
weight-one input occurs among its teeth; metabelianity then kills the long
bracket. -/
theorem T_homogeneous_eq_zero_of_derived_weightOne
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (s : Fin (n - k + 2) → Fin k)
    (x : ∀ i, FreeMetabelian.Piece (Generator L) (s i).val)
    (i₀ : Fin (n - k + 2)) (hi₀ : (s i₀).val = 0)
    (hderived :
      FreeMetabelian.Evaluation.pieceEval data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
          (s i₀).val (x i₀) ∈ LieAlgebra.derivedSeries ℤ L 1) :
    T n L data k hk hkn
      (SymmetricPower.tprod ℤ (fun i ↦
        FreeMetabelian.Free.weightIncl (s i).val (s i).isLt (x i))) = 0 := by
  classical
  by_contra hT
  have hshape := T_homogeneous_ne_zero_shape n L data k hk hkn s x hT
  obtain ⟨i, hi, hi_unique⟩ := hshape
  have hi₀i : i₀ ≠ i := by
    intro h
    subst i₀
    omega
  apply hT
  rw [T_tprod]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j = i
  · subst j
    let y : Fin (n - k + 1) → L := fun r ↦
      FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
        (s (i.succAbove r)).val (x (i.succAbove r))
    have hteeth : (fun r ↦ transgressionTooth n L data k hk hkn
        (i.removeNth (fun t ↦
          FreeMetabelian.Free.weightIncl (s t).val (s t).isLt (x t)) r)) =
        fun r ↦ (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ
          (y r) := by
      funext r
      have hir : i.succAbove r ≠ i := Fin.succAbove_ne i r
      have hs₀ : (s (i.succAbove r)).val = 0 := hi.2 _ hir
      have hslt : (s (i.succAbove r)).val < k - 1 := by omega
      change transgressionTooth n L data k hk hkn
          (FreeMetabelian.Free.weightIncl (s (i.succAbove r)).val
            (s (i.succAbove r)).isLt (x (i.succAbove r))) = _
      exact transgressionTooth_weightIncl_of_lt n L data k
        (s (i.succAbove r)).val hk hkn hslt (x (i.succAbove r))
    rw [hteeth]
    obtain ⟨r₀, hr₀⟩ := Fin.exists_succAbove_eq hi₀i
    have hyr₀ : y r₀ ∈ LieAlgebra.derivedSeries ℤ L 1 := by
      subst i₀
      exact hderived
    induction transgressionHead n L data k hk hkn
        (FreeMetabelian.Free.weightIncl (s i).val (s i).isLt (x i))
      using Submodule.Quotient.induction_on with
    | _ d =>
      exact thetaNonterminal_tmul_tprod_eq_zero_of_derived_tooth
        n L data k hk hkn d y r₀ hyr₀
  · have hj₀ : (s j).val = 0 := hi.2 j hji
    rw [transgressionHead_weightIncl_eq_zero_of_ne
      n L data k (s j).val hk hkn (s j).isLt (by omega)]
    simp

theorem transgressionTooth_relation_zero
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (r : D n L data k (by omega)) :
    transgressionTooth n L data k hk hkn r.1 = 0 := by
  change augmentation (n := n) L data (k - 1)
      (FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k
        (by omega) r.1) = 0
  exact (presentation (n := n) L data (k - 1) (by omega) (by omega)).augmentation_d
    (relationProjection n L data k (by omega) (by omega) r)

private theorem transgressionHead_relation
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (r : D n L data k (by omega)) :
    transgressionHead n L data k hk hkn r.1 =
      -extensionTail n L data k hk (by omega)
        (relationProjection n L data k (by omega) (by omega) r) := by
  obtain ⟨rho, hrho⟩ := r.2
  have hr : r = ⟨prLE n L k (by omega) rho.1, ⟨rho, rfl⟩⟩ := by
    apply Subtype.ext
    exact hrho.symm
  subst r
  have hp : relationProjection n L data k (by omega) (by omega)
      ⟨prLE n L k (by omega) rho.1, ⟨rho, rfl⟩⟩ =
      ⟨prLE n L (k - 1) (by omega) rho.1, ⟨rho, rfl⟩⟩ := by
    apply Subtype.ext
    exact LinearMap.congr_fun
      (FreeMetabelian.Free.projectPrefix_trans
        (X := Generator L) (k - 1) k (n + 1) (by omega) (by omega)) rho.1
  rw [hp, extensionTail_relation]
  change pieceToU (n := n) L data k (by omega) _ = - -pieceToU
      (n := n) L data k (by omega) _
  rw [neg_neg]

theorem T_insert_of_tooth_eq_zero (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (head : A L k)
    (hhead : transgressionTooth n L data k hk hkn head = 0)
    (s : Sym[ℤ] (Fin (n - k + 1)) (A L k)) :
    T n L data k hk hkn
        (SymmetricPower.insert ℤ (A L k) (n - k + 1) head s) =
      thetaNonterminal n L data k hk hkn
        (transgressionHead n L data k hk hkn head ⊗ₜ[ℤ]
          SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
            (transgressionTooth n L data k hk hkn) s) := by
  let lhs : Sym[ℤ] (Fin (n - k + 1)) (A L k) →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
    (T n L data k hk hkn).comp
      (SymmetricPower.insert ℤ (A L k) (n - k + 1) head)
  let rhs : Sym[ℤ] (Fin (n - k + 1)) (A L k) →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
    (thetaNonterminal n L data k hk hkn).comp
      ((TensorProduct.mk ℤ (U L k) _
        (transgressionHead n L data k hk hkn head)).comp
          (SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
            (transgressionTooth n L data k hk hkn)))
  change lhs s = rhs s
  apply LinearMap.congr_fun _ s
  apply SymmetricPower.linearMap_ext
  intro x
  change T n L data k hk hkn
      (SymmetricPower.insert ℤ (A L k) (n - k + 1) head
        (SymmetricPower.tprod ℤ x)) = _
  rw [SymmetricPower.insert_tprod, T_tprod, Fin.sum_univ_succ]
  change _ = thetaNonterminal n L data k hk hkn
      (transgressionHead n L data k hk hkn head ⊗ₜ[ℤ]
        SymmetricPower.tprod ℤ
          (fun i ↦ transgressionTooth n L data k hk hkn (x i)))
  simp only [Fin.removeNth_zero, Fin.tail_cons, Fin.cons_zero, Fin.cons_succ]
  have hq : 1 ≤ n - k + 1 := by omega
  have hzero (i : Fin (n - k + 1)) :
      SymmetricPower.tprod ℤ (fun j ↦
        transgressionTooth n L data k hk hkn
          ((Fin.cons head x : Fin (n - k + 2) → A L k)
            ((i.succ : Fin (n - k + 2)).succAbove j))) = 0 := by
    let j0 : Fin (n - k + 1) := ⟨0, hq⟩
    exact (SymmetricPower.tprod ℤ).map_coord_zero j0 (by
      change transgressionTooth n L data k hk hkn
          ((Fin.cons head x : Fin (n - k + 2) → A L k)
            (i.succ.succAbove j0)) = 0
      have hs : i.succ.succAbove j0 = 0 := by
        apply Fin.ext
        simp [j0, Fin.succAbove]
      rw [hs, Fin.cons_zero, hhead])
  have hsum : (∑ i : Fin (n - k + 1),
      thetaNonterminal n L data k hk hkn
        (transgressionHead n L data k hk hkn (x i) ⊗ₜ[ℤ]
          SymmetricPower.tprod ℤ (fun j ↦
            transgressionTooth n L data k hk hkn
              ((Fin.cons head x : Fin (n - k + 2) → A L k)
                ((i.succ : Fin (n - k + 2)).succAbove j))))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hzero i]
    simp
  change thetaNonterminal n L data k hk hkn
      (transgressionHead n L data k hk hkn head ⊗ₜ[ℤ]
        SymmetricPower.tprod ℤ
          (fun j ↦ transgressionTooth n L data k hk hkn (x j))) +
      (∑ i : Fin (n - k + 1),
        thetaNonterminal n L data k hk hkn
          (transgressionHead n L data k hk hkn (x i) ⊗ₜ[ℤ]
            SymmetricPower.tprod ℤ (fun j ↦
              transgressionTooth n L data k hk hkn
                ((Fin.cons head x : Fin (n - k + 2) → A L k)
                  ((i.succ : Fin (n - k + 2)).succAbove j))))) = _
  rw [hsum, add_zero]

private theorem T_insert_relation (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (r : D n L data k (by omega))
    (s : Sym[ℤ] (Fin (n - k + 1)) (A L k)) :
    T n L data k hk hkn
        (SymmetricPower.insert ℤ (A L k) (n - k + 1) r.1 s) =
      thetaNonterminal n L data k hk hkn
        (transgressionHead n L data k hk hkn r.1 ⊗ₜ[ℤ]
          SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
            (transgressionTooth n L data k hk hkn) s) := by
  exact T_insert_of_tooth_eq_zero n L data k hk hkn r.1
    (transgressionTooth_relation_zero n L data k hk hkn r) s

/-- Chain-level transgression, with the manuscript's sign fixed by the
negative-tail definition of `extensionTail`. -/
theorem transgression (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    (Phi n L data k hk hkn).comp
        (Koszul.PresentationHomology.oneMap
          (presentation n L data k (by omega) (by omega))
          (presentation (n := n) L data (k - 1) (by omega) (by omega))
          (presentationProjection n L data k hk (by omega))
          (n - k + 1)) =
      (T n L data k hk hkn).comp
        (Koszul.dOne (presentation n L data k (by omega) (by omega))
          (n - k + 1)) := by
  apply TensorProduct.ext'
  intro r s
  change Phi n L data k hk hkn
      (Koszul.PresentationHomology.oneMap
        (presentation n L data k (by omega) (by omega))
        (presentation (n := n) L data (k - 1) (by omega) (by omega))
        (presentationProjection n L data k hk (by omega))
        (n - k + 1) (r ⊗ₜ[ℤ] s)) =
    T n L data k hk hkn
      (Koszul.dOne (presentation n L data k (by omega) (by omega))
        (n - k + 1) (r ⊗ₜ[ℤ] s))
  rw [Koszul.PresentationHomology.oneMap_tmul, Koszul.dOne_tmul]
  change Phi n L data k hk hkn
      (relationProjection n L data k (by omega) (by omega) r ⊗ₜ[ℤ]
        SymmetricPower.map
          (FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k
            (by omega)) s) = _
  change _ = T n L data k hk hkn
      (SymmetricPower.insert ℤ (A L k) (n - k + 1) r.1 s)
  rw [T_insert_relation, transgressionHead_relation]
  change -thetaNonterminal n L data k hk hkn
      (extensionTail n L data k hk (by omega)
          (relationProjection n L data k (by omega) (by omega) r) ⊗ₜ[ℤ]
        SymmetricPower.map
          (augmentation (n := n) L data (k - 1))
          (SymmetricPower.map
            (FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k
              (by omega)) s)) =
    thetaNonterminal n L data k hk hkn
      (-extensionTail n L data k hk (by omega)
          (relationProjection n L data k (by omega) (by omega) r) ⊗ₜ[ℤ]
        SymmetricPower.map (transgressionTooth n L data k hk hkn) s)
  have hmap := LinearMap.congr_fun
    (SymmetricPower.map_comp (R := ℤ) (ι := Fin (n - k + 1))
      (augmentation (n := n) L data (k - 1))
      (FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k
        (by omega))) s
  have hmap' :
      SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
          (augmentation (n := n) L data (k - 1))
          (SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
            (FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k
              (by omega)) s) =
        SymmetricPower.map (R := ℤ) (ι := Fin (n - k + 1))
          (transgressionTooth n L data k hk hkn) s := by
    exact hmap.symm
  rw [hmap']
  rw [← TensorProduct.neg_tmul]
  exact (map_neg (thetaNonterminal n L data k hk hkn) _).symm

/-- The higher character vanishes after pullback along `W_k -> V_k`. -/
theorem eta_comp_map_pi (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    (eta n L data k hk hkn).comp
      (Koszul.FirstDerivedSymmetricPower.map (n - k + 1) (pi L k)) = 0 := by
  let Pk := presentation n L data k (by omega) (by omega)
  let Pkm := presentation (n := n) L data (k - 1) (by omega) (by omega)
  let F := presentationProjection n L data k hk (by omega)
  rw [eta]
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective
    (Koszul.boundariesOne (Koszul.Presentation.canonical (W L k))
      (n - k + 1)) z
  have hnat := Koszul.Presentation.homologyComparison_natural Pk Pkm F
    (n - k + 1)
  have hcomp := Koszul.Presentation.homologyComparisonEquiv_toLinearMap_eq
    Pk (n - k + 1) (Koszul.Presentation.toCanonical Pk)
  change LieRings.zmodToRatCircle (2 ^ data.exponent)
      (etaFinite n L data k hk hkn
        (Koszul.FirstDerivedSymmetricPower.map (n - k + 1) (pi L k)
          ((Koszul.boundariesOne
            (Koszul.Presentation.canonical (W L k)) (n - k + 1)).mkQ c))) = 0
  change LieRings.zmodToRatCircle (2 ^ data.exponent)
      (((Koszul.boundariesOne Pkm (n - k + 1)).liftQ
          (PhiCycles n L data k hk hkn)
          (boundaries_le_ker_PhiCycles n L data k hk hkn))
        ((Koszul.Presentation.homologyComparisonEquiv Pkm
          (n - k + 1)).symm
          (Koszul.FirstDerivedSymmetricPower.map (n - k + 1) (pi L k)
            ((Koszul.boundariesOne
              (Koszul.Presentation.canonical (W L k)) (n - k + 1)).mkQ c)))) = 0
  have hpre := LinearMap.congr_fun hnat
    ((Koszul.Presentation.homologyComparisonEquiv Pk (n - k + 1)).symm
      ((Koszul.boundariesOne
        (Koszul.Presentation.canonical (W L k)) (n - k + 1)).mkQ c))
  simp only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply] at hpre
  have hpre2 :
      (Koszul.Presentation.homologyComparisonEquiv Pkm (n - k + 1))
        (Koszul.PresentationHomology.map Pk Pkm F (n - k + 1)
          ((Koszul.Presentation.homologyComparisonEquiv Pk
            (n - k + 1)).symm
            ((Koszul.boundariesOne
              (Koszul.Presentation.canonical (W L k)) (n - k + 1)).mkQ c))) =
      Koszul.FirstDerivedSymmetricPower.map (n - k + 1) (pi L k)
        ((Koszul.boundariesOne
          (Koszul.Presentation.canonical (W L k)) (n - k + 1)).mkQ c) := by
    calc
      _ = Koszul.PresentationHomology.map
          (Koszul.Presentation.canonical (W L k))
          (Koszul.Presentation.canonical (W L (k - 1)))
          (Koszul.Presentation.canonicalHom (pi L k)) (n - k + 1)
          ((Koszul.Presentation.homologyComparisonEquiv Pk (n - k + 1))
            ((Koszul.Presentation.homologyComparisonEquiv Pk
              (n - k + 1)).symm
              ((Koszul.boundariesOne
                (Koszul.Presentation.canonical (W L k))
                (n - k + 1)).mkQ c))) := hpre
      _ = Koszul.PresentationHomology.map
          (Koszul.Presentation.canonical (W L k))
          (Koszul.Presentation.canonical (W L (k - 1)))
          (Koszul.Presentation.canonicalHom (pi L k)) (n - k + 1)
          ((Koszul.boundariesOne
            (Koszul.Presentation.canonical (W L k))
            (n - k + 1)).mkQ c) := by rw [LinearEquiv.apply_symm_apply]
      _ = _ := rfl
  have hpre' :
      (Koszul.Presentation.homologyComparisonEquiv Pkm (n - k + 1)).symm
        (Koszul.FirstDerivedSymmetricPower.map (n - k + 1) (pi L k)
          ((Koszul.boundariesOne
            (Koszul.Presentation.canonical (W L k)) (n - k + 1)).mkQ c)) =
      Koszul.PresentationHomology.map Pk Pkm F (n - k + 1)
        ((Koszul.Presentation.homologyComparisonEquiv Pk
          (n - k + 1)).symm
          ((Koszul.boundariesOne
            (Koszul.Presentation.canonical (W L k)) (n - k + 1)).mkQ c)) := by
    apply (Koszul.Presentation.homologyComparisonEquiv Pkm
      (n - k + 1)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hpre2.symm
  rw [hpre']
  obtain ⟨cPk, hcPk⟩ := Submodule.mkQ_surjective
    (Koszul.boundariesOne Pk (n - k + 1))
    ((Koszul.Presentation.homologyComparisonEquiv Pk (n - k + 1)).symm
      ((Koszul.boundariesOne
        (Koszul.Presentation.canonical (W L k)) (n - k + 1)).mkQ c))
  rw [← hcPk]
  change LieRings.zmodToRatCircle (2 ^ data.exponent)
      (Phi n L data k hk hkn
        (Koszul.PresentationHomology.oneMap Pk Pkm F (n - k + 1) cPk.1)) = 0
  have ht := LinearMap.congr_fun (transgression n L data k hk hkn) cPk.1
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at ht
  have hcycle : Koszul.dOne Pk (n - k + 1) cPk.1 = 0 := cPk.2
  change Koszul.dOne (presentation n L data k (by omega) (by omega))
      (n - k + 1) cPk.1 = 0 at hcycle
  have htzero : Phi n L data k hk hkn
      (Koszul.PresentationHomology.oneMap Pk Pkm F (n - k + 1) cPk.1) = 0 := by
    calc
      _ = T n L data k hk hkn
          (Koszul.dOne (presentation n L data k (by omega) (by omega))
            (n - k + 1) cPk.1) := ht
      _ = T n L data k hk hkn 0 := congrArg (T n L data k hk hkn) hcycle
      _ = 0 := map_zero _
  rw [htzero]
  exact map_zero _

end

end LieRings.MetabelianVanishing
