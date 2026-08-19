import LieRings.Homological.PresentationStabilization
open TensorProduct
example {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (c : ℤ) (m : M) (n : N) :
    m ⊗ₜ[ℤ] (c • n) = (c • m) ⊗ₜ[ℤ] n := by
  have ht := TensorProduct.smul_tmul (R := ℤ) (R' := ℤ) (M := M) (N := N) c m n
  exact ht.symm

example {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (c : ℤ) (m : M) (n : N) :
    m ⊗ₜ[ℤ] (c • n) = c • (m ⊗ₜ[ℤ] n) := by
  change m ⊗ₜ[ℤ] ((c • n : N)) = _
  rcases c with (k | k)
  · simp; rfl
  · change m ⊗ₜ[ℤ] (-((k + 1) • n)) = -((k + 1) • (m ⊗ₜ[ℤ] n))
    rw [TensorProduct.tmul_neg, TensorProduct.tmul_nsmul]
#check TensorProduct.smul_tmul'
#check TensorProduct.tmul_smul
#check TensorProduct.smul_tmul
#check TensorProduct.nsmul_tmul
#check TensorProduct.neg_tmul
