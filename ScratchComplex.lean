import LieRings.Homological.Koszul
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

open TensorProduct
open CategoryTheory
open CategoryTheory.Limits

namespace Koszul
namespace ScratchComplex

universe u v w
noncomputable section

variable {A : Type u} [AddCommGroup A] (P : Presentation A)

abbrev RawTerm (m i : ℕ) :=
  (⋀[ℤ]^i P.rel) ⊗[ℤ] Sym[ℤ] (Fin (m - i)) P.gen

def boundedDifferential (m i : ℕ) (h : i + 1 ≤ m) :
    RawTerm P m (i + 1) →ₗ[ℤ] RawTerm P m i := by
  have hq : m - (i + 1) + 1 = m - i := by omega
  exact (TensorProduct.map LinearMap.id
    (SymmetricPower.reindex (R := ℤ) (finCongr hq))).comp
      (AllDegrees.differential P.d i (m - (i + 1)))

@[simp]
theorem boundedDifferential_wedge_tmul (m i : ℕ) (h : i + 1 ≤ m)
    (a : Fin (i + 1) → P.rel)
    (s : Sym[ℤ] (Fin (m - (i + 1))) P.gen) :
    boundedDifferential P m i h
      (exteriorPower.ιMulti ℤ (i + 1) a ⊗ₜ[ℤ] s) =
      ∑ j : Fin (i + 1), ((-1 : ℤ) ^ (i - j.val)) •
        (exteriorPower.ιMulti ℤ i (j.removeNth a) ⊗ₜ[ℤ]
          SymmetricPower.reindex (R := ℤ)
            (finCongr (show m - (i + 1) + 1 = m - i by omega))
              (SymmetricPower.insert ℤ P.gen (m - (i + 1)) (P.d (a j)) s)) := by
  simp only [boundedDifferential]
  change (TensorProduct.map LinearMap.id
    (SymmetricPower.reindex (R := ℤ)
      (finCongr (show m - (i + 1) + 1 = m - i by omega))))
      (AllDegrees.differential P.d i (m - (i + 1))
        (exteriorPower.ιMulti ℤ (i + 1) a ⊗ₜ[ℤ] s)) = _
  rw [AllDegrees.differential_wedge_tmul, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul]
  rfl

private theorem finCons_finCongr_two {M : Type u} {q r t : ℕ}
    (h₁ : q + 1 = r) (h₂ : r + 1 = t) (hout : q + 2 = t)
    (y z : M) (x : Fin q → M) :
    (Fin.cons y (Fin.cons z x ∘ (finCongr h₁).symm) ∘
        (finCongr h₂).symm) =
      (Fin.cons y (Fin.cons z x) ∘ (finCongr hout).symm) := by
  subst r
  subst t
  funext k
  simp only [Function.comp_apply, finCongr_symm, finCongr_apply]
  rcases k with ⟨k, hk⟩
  simp only [Fin.cast_mk]
  rcases k with _ | k
  · simp
  rcases k with _ | k
  · simp
  simp

theorem boundedDifferential_comp (m i : ℕ) (h : i + 2 ≤ m) :
    (boundedDifferential P m i (by omega)).comp
      (boundedDifferential P m (i + 1) (by omega)) = 0 := by
  apply TensorProduct.ext'
  intro w s
  let Fw : (⋀[ℤ]^(i + 2) P.rel) →ₗ[ℤ] RawTerm P m i :=
    ((boundedDifferential P m i (by omega)).comp
      (boundedDifferential P m (i + 1) (by omega))).comp
        ((TensorProduct.mk ℤ (⋀[ℤ]^(i + 2) P.rel) _).flip s)
  have hFw : Fw = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    let Fs : Sym[ℤ] (Fin (m - (i + 2))) P.gen →ₗ[ℤ] RawTerm P m i :=
      ((boundedDifferential P m i (by omega)).comp
        (boundedDifferential P m (i + 1) (by omega))).comp
          (TensorProduct.mk ℤ _ _ (exteriorPower.ιMulti ℤ (i + 2) a))
    have hFs : Fs = 0 := by
      apply SymmetricPower.linearMap_ext
      intro x
      change boundedDifferential P m i (by omega)
        (boundedDifferential P m (i + 1) (by omega)
          (exteriorPower.ιMulti ℤ (i + 2) a ⊗ₜ[ℤ]
            SymmetricPower.tprod ℤ x)) = 0
      rw [boundedDifferential_wedge_tmul, map_sum]
      simp only [map_smul, boundedDifferential_wedge_tmul,
        SymmetricPower.insert_tprod, SymmetricPower.reindex_tprod]
      have hout : (m - (i + 2)) + 2 = m - i := by omega
      let castOut :
          ((⋀[ℤ]^i P.rel) ⊗[ℤ] Sym[ℤ] (Fin ((m - (i + 2)) + 2)) P.gen) →ₗ[ℤ]
            RawTerm P m i :=
        TensorProduct.map LinearMap.id
          (SymmetricPower.reindex (R := ℤ) (finCongr hout))
      have hd := congrArg castOut
        (LinearMap.congr_fun
          (AllDegrees.differential_comp_differential P.d i (m - (i + 2)))
          (exteriorPower.ιMulti ℤ (i + 2) a ⊗ₜ[ℤ]
            SymmetricPower.tprod ℤ x))
      simp only [LinearMap.comp_apply, AllDegrees.differential_wedge_tmul,
        map_sum, map_smul, TensorProduct.map_tmul, LinearMap.id_coe,
        id_eq, SymmetricPower.reindex_tprod, map_zero] at hd
      simp only [castOut, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
        SymmetricPower.reindex_tprod, SymmetricPower.insert_tprod, map_zero] at hd
      have h₁ : m - (i + 2) + 1 = m - (i + 1) := by omega
      have h₂ : m - (i + 1) + 1 = m - i := by omega
      simp_rw [finCons_finCongr_two h₁ h₂ hout]
      simpa [castOut, Function.comp_def] using hd
    have hs := LinearMap.congr_fun hFs s
    exact hs
  have hw := LinearMap.congr_fun hFw w
  exact hw

def rawD (m i : ℕ) :
    ModuleCat.of ℤ (RawTerm P m (i + 1)) ⟶ ModuleCat.of ℤ (RawTerm P m i) := by
  by_cases h : i + 1 ≤ m
  · exact ModuleCat.ofHom (boundedDifferential P m i h)
  · exact 0

theorem rawD_sq (m i : ℕ) : rawD P m (i + 1) ≫ rawD P m i = 0 := by
  by_cases h : i + 2 ≤ m
  · simp only [rawD, dif_pos (by omega : i + 1 + 1 ≤ m),
      dif_pos (by omega : i + 1 ≤ m)]
    apply ModuleCat.hom_ext
    change (boundedDifferential P m i (by omega)).comp
      (boundedDifferential P m (i + 1) (by omega)) = 0
    exact boundedDifferential_comp P m i h
  · simp only [rawD, dif_neg (by omega : ¬i + 1 + 1 ≤ m)]
    simp

def rawComplex (m : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of ℤ (RawTerm P m i))
    (rawD P m) (rawD_sq P m)

abbrev BoundedIndex (m : ℕ) := {i : ℕ // i ≤ m}

def boundedShape (m : ℕ) : ComplexShape (BoundedIndex m) where
  Rel i j := j.val + 1 = i.val
  next_eq hi hj := Subtype.ext (Nat.add_right_cancel (hi.trans hj.symm))
  prev_eq hi hj := Subtype.ext (hi.symm.trans hj)

def weightEmbedding (m : ℕ) :
    (boundedShape m).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.Embedding.mk' (boundedShape m) (ComplexShape.down ℕ)
    Subtype.val Subtype.val_injective (fun _ _ => Iff.rfl)

instance weightEmbedding_isRelIff (m : ℕ) :
    (weightEmbedding m).IsRelIff := by
  dsimp only [weightEmbedding]
  infer_instance

def complex (m : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  (rawComplex P m).stupidTrunc (weightEmbedding m)

theorem complex_isZero_above (m i : ℕ) (h : m < i) :
    IsZero ((complex P m).X i) := by
  apply HomologicalComplex.isZero_stupidTrunc_X
  intro j hj
  change j.val = i at hj
  omega

end
end ScratchComplex
end Koszul
