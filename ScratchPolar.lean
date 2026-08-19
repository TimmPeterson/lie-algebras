import LieRings.Homological.SymmetricPower

open TensorProduct

namespace Test

noncomputable section

#check TensorProduct.lift.equiv
#check TensorProduct.lift.equiv_symm_apply
#check TensorProduct.lift.tmul
#check TensorProduct.tmul_smul
#check TensorProduct.smul_tmul
#check TensorProduct.smul_tmul'
#check TensorProduct.tmul_smul

private def omitEquiv {q : ℕ} (e : Equiv.Perm (Fin (q + 1)))
    (i : Fin (q + 1)) : Equiv.Perm (Fin q) :=
  ((finSuccAboveEquiv i).trans
    (Equiv.subtypeEquiv e (fun j ↦ by
      constructor
      · exact fun (h : j ≠ i) h' ↦ h (e.injective h')
      · exact fun (h : e j ≠ e i) h' ↦ h (congrArg e h')))).trans
      (finSuccAboveEquiv (e i)).symm

private theorem omitEquiv_spec {q : ℕ} (e : Equiv.Perm (Fin (q + 1)))
    (i : Fin (q + 1)) (j : Fin q) :
    (e i).succAbove (omitEquiv e i j) = e (i.succAbove j) := by
  change (finSuccAboveEquiv (e i)
    ((finSuccAboveEquiv (e i)).symm
      ⟨e (i.succAbove j), by
        exact fun h ↦ Fin.succAbove_ne i j (e.injective h)⟩)).1 = _
  rw [Equiv.apply_symm_apply]

universe v w
variable {R : Type} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {U V N : Type w} [AddCommMonoid U] [Module R U]
  [AddCommMonoid V] [Module R V] [AddCommMonoid N] [Module R N]

def polarMultilinear (q : ℕ) (p : M →ₗ[R] U) (v : M →ₗ[R] V)
    (theta : U ⊗[R] Sym[R] (Fin q) V →ₗ[R] N) :
    MultilinearMap R (fun _ : Fin (q + 1) ↦ M) N := by
  let tooth : MultilinearMap R (fun _ : Fin q ↦ M)
      (Sym[R] (Fin q) V) :=
    (SymmetricPower.tprod R).compLinearMap (fun _ ↦ v)
  let theta' : U →ₗ[R] Sym[R] (Fin q) V →ₗ[R] N :=
    (TensorProduct.lift.equiv (RingHom.id R) U (Sym[R] (Fin q) V) N).symm theta
  let head : M →ₗ[R] MultilinearMap R (fun _ : Fin q ↦ M) N :=
    { toFun := fun x ↦
        (theta' (p x)).compMultilinearMap tooth
      map_add' := by
        intro x y
        ext z
        simp [theta']
      map_smul' := by
        intro r x
        ext z
        simp [theta'] }
  exact ∑ i, head.uncurryMid i

theorem polarMultilinear_apply (q : ℕ) (p : M →ₗ[R] U) (v : M →ₗ[R] V)
    (theta : U ⊗[R] Sym[R] (Fin q) V →ₗ[R] N)
    (x : Fin (q + 1) → M) :
    polarMultilinear q p v theta x = ∑ i,
      theta (p (x i) ⊗ₜ[R] SymmetricPower.tprod R
        (fun j ↦ v (i.removeNth x j))) := by
  simp [polarMultilinear, TensorProduct.lift.equiv_symm_apply]

theorem polarMultilinear_symmetric (q : ℕ) (p : M →ₗ[R] U) (v : M →ₗ[R] V)
    (theta : U ⊗[R] Sym[R] (Fin q) V →ₗ[R] N) :
    SymmetricPower.IsSymmetric (polarMultilinear q p v theta) := by
  intro e x
  rw [polarMultilinear_apply, polarMultilinear_apply]
  apply Fintype.sum_equiv e
  intro i
  simp only [Function.comp_apply]
  apply congrArg theta
  apply congrArg (fun s ↦ p (x (e i)) ⊗ₜ[R] s)
  let lhs : Fin q → V := fun j ↦ v (i.removeNth (x ∘ e) j)
  let rhs : Fin q → V := fun j ↦ v ((e i).removeNth x j)
  have hfun : lhs = rhs ∘ omitEquiv e i := by
    funext j
    simp only [lhs, rhs, Function.comp_apply, Fin.removeNth_apply]
    rw [omitEquiv_spec]
  change SymmetricPower.tprod R lhs = SymmetricPower.tprod R rhs
  rw [hfun]
  exact SymmetricPower.tprod_equiv (omitEquiv e i) rhs

end
end Test

namespace Test2
open TensorProduct
noncomputable section
universe u
variable (n : Nat) (L : Type u)
variable {M U V N : Type u} [AddCommMonoid M] [Module ℤ M]
  [AddCommMonoid U] [Module ℤ U] [AddCommMonoid V] [Module ℤ V]
  [AddCommMonoid N] [Module ℤ N]

def p (q : Nat) (h : M →ₗ[ℤ] U) (v : M →ₗ[ℤ] V)
    (t : U ⊗[ℤ] Sym[ℤ] (Fin q) V →ₗ[ℤ] N) :
    Sym[ℤ] (Fin (q+1)) M →ₗ[ℤ] N :=
  SymmetricPower.polarize (N₀ := N) q h v t

theorem p_insert (q : Nat) (h : M →ₗ[ℤ] U) (v : M →ₗ[ℤ] V)
    (t : U ⊗[ℤ] Sym[ℤ] (Fin q) V →ₗ[ℤ] N)
    (r : M) (x : Fin q → M)
    (hq : 1 ≤ q) (hz : v r = 0) :
    p (M := M) (U := U) (V := V) (N := N) q h v t
      (SymmetricPower.insert ℤ M q r
      (SymmetricPower.tprod ℤ x)) =
      t (h r ⊗ₜ[ℤ] SymmetricPower.tprod ℤ (fun i => v (x i))) := by
  rw [SymmetricPower.insert_tprod]
  rw [p, SymmetricPower.polarize_tprod, Fin.sum_univ_succ]
  have hzero : ∀ i : Fin q, SymmetricPower.tprod ℤ
      (fun j : Fin q => v (((Fin.cons r x : Fin (q+1) → M))
        ((i.succ : Fin (q+1)).succAbove j))) = 0 := by
    intro i
    let j0 : Fin q := ⟨0, hq⟩
    exact (SymmetricPower.tprod ℤ).map_coord_zero j0 (by
      change v ((Fin.cons r x : Fin (q+1) → M) (i.succ.succAbove j0)) = 0
      have hs : i.succ.succAbove j0 = 0 := by
        apply Fin.ext
        simp [j0, Fin.succAbove]
      rw [hs, Fin.cons_zero, hz])
  simp only [Fin.removeNth_zero, Fin.tail_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hsum : (∑ i : Fin q,
      t (h (x i) ⊗ₜ[ℤ] SymmetricPower.tprod ℤ
        (fun j => v (((Fin.cons r x : Fin (q+1) → M))
          ((i.succ : Fin (q+1)).succAbove j))))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hzero i]
    simp
  have hsum' : (∑ i : Fin q,
      t (h (x i) ⊗ₜ[ℤ] SymmetricPower.tprod ℤ
        (fun j => v (((Fin.cons r x : Fin (q+1) → M))
          ((i.succ : Fin (q+1)).succAbove j))))) = 0 := hsum
  change t (h r ⊗ₜ[ℤ] SymmetricPower.tprod ℤ (fun j => v (x j))) +
      (∑ i : Fin q, t (h (x i) ⊗ₜ[ℤ] SymmetricPower.tprod ℤ
        (fun j => v ((Fin.cons r x : Fin (q+1) → M)
          ((i.succ : Fin (q+1)).succAbove j))))) = _
  rw [hsum']
  exact add_zero _

end
end Test2
