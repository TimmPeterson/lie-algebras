import LieRings.DimensionSubring.MetabelianVanishing.ClosedSquare

open FreeMetabelian
open TensorProduct
open LieRings.PBW
open LieRings.MetabelianVanishing

#check LieSubmodule.toSubmodule
#check Submodule.comap
#check LinearMap.range
#check Module.projective_lifting_property
#check Submodule.basisOfPid
#check Submodule.smithNormalForm
#check Module.Basis.prod
#check LinearEquiv.prodCongr
#check LinearEquiv.ofBijective
#check FreeMetabelian.Free.tail
#check FreeMetabelian.Free.weightProject
#check FreeMetabelian.Free.tail_cutoff_eq_bot
#check FreeMetabelian.Free.mem_tail_iff
#check Submodule.map_comap_subtype
#check LinearMap.ker_eq_bot

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L) (hn : 2 ≤ n)

theorem scratch_rightSymbol_iota_basis_mul_basisWord
    (q k : ℕ) (hk : k ≤ n + 1)
    (i : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn)) (hlen : xs.length = q) :
    rightSymbol n L data hn (q + 1) k hk
        (UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) *
          MarkedRow.basisWord n L data hn xs) =
      SymmetricPower.insert ℤ (A L k) q
        (prLE n L k hk (adaptedBasis n L data hn i))
        (SymmetricPower.tprod ℤ (fun j : Fin q ↦
          prLE n L k hk
            (adaptedBasis n L data hn
              (xs.get ⟨j.val, by omega⟩)))) := by
  classical
  have hword : UniversalEnvelopingAlgebra.ι ℤ
        (adaptedBasis n L data hn i) *
      MarkedRow.basisWord n L data hn xs =
        MarkedRow.basisWord n L data hn (i :: xs) := by
    simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, adaptedWeightedBasis]
  rw [hword, rightSymbol, LinearMap.comp_apply]
  let ys := i :: xs
  let s : Sym (AdaptedIndex n L data hn) (q + 1) :=
    Sym.mk (ys : Multiset (AdaptedIndex n L data hn)) (by simp [ys, hlen])
  have hfull : fullRightSymbol n L data hn (q + 1)
      (MarkedRow.basisWord n L data hn ys) =
        SymmetricPower.monomialBasis (adaptedBasis n L data hn) (q + 1) s := by
    exact fullRightSymbol_basisWord_of_length n L data hn (q + 1) ys
      (by simp [ys, hlen])
  rw [hfull]
  let p : Fin (q + 1) → AdaptedIndex n L data hn :=
    Fin.cons i (fun j : Fin q ↦ xs.get ⟨j.val, by omega⟩)
  have hp : SymmetricPower.symIndexOfFun (q + 1) p = s := by
    apply Sym.ext
    rw [coe_symIndexOfFun]
    change (List.ofFn p : Multiset (AdaptedIndex n L data hn)) =
      (ys : List (AdaptedIndex n L data hn))
    rw [show List.ofFn p = ys by
      rw [show List.ofFn p = i :: List.ofFn
          (fun j : Fin q ↦ xs.get ⟨j.val, by omega⟩) by
        exact List.ofFn_cons _ _]
      simp only [ys, List.cons.injEq, true_and]
      apply List.ext_get
      · simpa [hlen]
      · intro j hj₁ hj₂
        simp only [List.get_ofFn]
        rfl]
  rw [monomialBasis_eq_tprod_of_symIndex
    (adaptedBasis n L data hn) (q + 1) s p hp,
    SymmetricPower.map_tprod, SymmetricPower.insert_tprod]
  congr 1
  funext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · rfl
  · rfl

end

end LieRings.MetabelianVanishing
