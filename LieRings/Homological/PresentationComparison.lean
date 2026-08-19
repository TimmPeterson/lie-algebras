import LieRings.Homological.PresentationStabilization
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Stabilization and comparison for Koszul homology

This file proves the integral contraction used to make degree-one Koszul
homology independent of a chosen finite free presentation.  The contraction is
defined on the actual exterior/symmetric monomial bases; it uses no division
and no polynomial substitute for symmetric powers.
-/

open TensorProduct

namespace Koszul.Presentation

universe u v w t
noncomputable section
set_option maxHeartbeats 1200000

variable {A : Type u} [AddCommGroup A]
variable (P : Presentation.{u, v, w} A)
variable (T : Type t) [AddCommGroup T] [Module.Free ℤ T] [Module.Finite ℤ T]

private def relRank : ℕ :=
  (Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := P.rel)).1

private def relBasis : Module.Basis (Fin (relRank P)) ℤ P.rel :=
  (Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := P.rel)).2

private def genRank : ℕ :=
  (Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := P.gen)).1

private def genBasis : Module.Basis (Fin (genRank P)) ℤ P.gen :=
  (Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := P.gen)).2

private def summandRank : ℕ :=
  (Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := T)).1

private def summandBasis : Module.Basis (Fin (summandRank T)) ℤ T :=
  (Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := T)).2

private abbrev RI := Fin (relRank P) ⊕ Fin (summandRank T)
private abbrev GI := Fin (genRank P) ⊕ Fin (summandRank T)

private def stabilizedRelBasis :
    Module.Basis (RI P T) ℤ (P.rel × T) :=
  (relBasis P).prod (summandBasis T)

private def stabilizedGenBasis :
    Module.Basis (GI P T) ℤ (P.gen × T) :=
  (genBasis P).prod (summandBasis T)

@[simp]
private theorem stabilizedRelBasis_inl (a : Fin (relRank P)) :
    stabilizedRelBasis P T (Sum.inl a) = (relBasis P a, 0) := by
  simp [stabilizedRelBasis]

@[simp]
private theorem stabilizedRelBasis_inr (a : Fin (summandRank T)) :
    stabilizedRelBasis P T (Sum.inr a) = (0, summandBasis T a) := by
  simp [stabilizedRelBasis]

@[simp]
private theorem stabilizedGenBasis_inl (a : Fin (genRank P)) :
    stabilizedGenBasis P T (Sum.inl a) = (genBasis P a, 0) := by
  simp [stabilizedGenBasis]

@[simp]
private theorem stabilizedGenBasis_inr (a : Fin (summandRank T)) :
    stabilizedGenBasis P T (Sum.inr a) = (0, summandBasis T a) := by
  simp [stabilizedGenBasis]

private def oneBasis (q : ℕ) :
    Module.Basis (RI P T × Sym (GI P T) q) ℤ (One (stabilize P T) q) :=
  by
    let _tower : IsScalarTower ℤ ℤ (P.rel × T) := ⟨fun r s x => by
      change (r * s) • x = r • s • x
      exact mul_smul r s x⟩
    letI := _tower
    exact Module.Basis.tensorProduct (R := ℤ) (S := ℤ) (stabilizedRelBasis P T)
      (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q)

private def twoBasis (q : ℕ) :
    Module.Basis (Set.powersetCard (RI P T) 2 × Sym (GI P T) q) ℤ
      (Two (stabilize P T) q) :=
  by
    letI : LinearOrder (RI P T) :=
      LinearOrder.lift' finSumFinEquiv finSumFinEquiv.injective
    let _tower : IsScalarTower ℤ ℤ (⋀[ℤ]^2 (P.rel × T)) := ⟨fun r s x => by
      change (r * s) • x = r • s • x
      exact mul_smul r s x⟩
    letI := _tower
    exact Module.Basis.tensorProduct (R := ℤ) (S := ℤ)
      ((stabilizedRelBasis P T).exteriorPower 2)
      (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q)

private def tSupport {q : ℕ} (s : Sym (GI P T) q) :
    Finset (Fin (summandRank T)) :=
  Finset.univ.filter (fun a ↦ Sum.inr a ∈ (s : Multiset (GI P T)))

private theorem mem_tSupport {q : ℕ} (s : Sym (GI P T) q)
    (a : Fin (summandRank T)) :
    a ∈ tSupport P T s ↔ Sum.inr a ∈ (s : Multiset (GI P T)) := by
  simp [tSupport]

private theorem tSupport_cons_inl {q : ℕ} (i : Fin (genRank P))
    (s : Sym (GI P T) q) :
    tSupport P T (Sum.inl i ::ₛ s) = tSupport P T s := by
  ext a
  simp [tSupport]

private theorem tSupport_cons_inr {q : ℕ} (a : Fin (summandRank T))
    (s : Sym (GI P T) q) :
    tSupport P T (Sum.inr a ::ₛ s) = insert a (tSupport P T s) := by
  ext b
  simp [tSupport, eq_comm]

private def totalSupport {q : ℕ} (i : RI P T) (s : Sym (GI P T) q) :
    Finset (Fin (summandRank T)) :=
  match i with
  | Sum.inl _ => tSupport P T s
  | Sum.inr a => insert a (tSupport P T s)

private def leastT (S : Finset (Fin (summandRank T))) (hS : S.Nonempty) :
    Fin (summandRank T) := S.min' hS

private theorem leastT_mem (S : Finset (Fin (summandRank T))) (hS : S.Nonempty) :
    leastT T S hS ∈ S := Finset.min'_mem S hS

private def eraseT {q : ℕ} (s : Sym (GI P T) (q + 1))
    (a : Fin (summandRank T)) (ha : Sum.inr a ∈ (s : Multiset (GI P T))) :
    Sym (GI P T) q := s.erase (Sum.inr a) ha

private theorem cons_eraseT {q : ℕ} (s : Sym (GI P T) (q + 1))
    (a : Fin (summandRank T)) (ha : Sum.inr a ∈ (s : Multiset (GI P T))) :
    Sum.inr a ::ₛ eraseT P T s a ha = s := Sym.cons_erase ha

private theorem eraseT_cons_inl {q : ℕ} (s : Sym (GI P T) (q + 1))
    (a : Fin (summandRank T)) (ha : Sum.inr a ∈ (s : Multiset (GI P T)))
    (i : Fin (genRank P)) :
    eraseT P T (Sum.inl i ::ₛ s) a (by
      exact Sym.mem_cons_of_mem ha) =
      Sum.inl i ::ₛ eraseT P T s a ha := by
  apply Sym.coe_injective
  exact Multiset.erase_cons_tail_of_mem ha

private theorem eraseT_cons_inr_ne {q : ℕ} (s : Sym (GI P T) (q + 1))
    (a j : Fin (summandRank T))
    (ha : Sum.inr a ∈ (s : Multiset (GI P T))) (_hja : j ≠ a) :
    eraseT P T (Sum.inr j ::ₛ s) a (by
      exact Sym.mem_cons_of_mem ha) =
      Sum.inr j ::ₛ eraseT P T s a ha := by
  apply Sym.coe_injective
  exact Multiset.erase_cons_tail_of_mem ha

private theorem eraseT_cons_inr_head {q : ℕ} (s : Sym (GI P T) q)
    (a : Fin (summandRank T)) :
    eraseT P T (Sum.inr a ::ₛ s) a (by simp) = s := by
  exact Sym.erase_cons_head s (Sum.inr a)

private def tRel (a : Fin (summandRank T)) : P.rel × T :=
  stabilizedRelBasis P T (Sum.inr a)

private def pRel (a : Fin (relRank P)) : P.rel × T :=
  stabilizedRelBasis P T (Sum.inl a)

private def hZeroOnBasis (q : ℕ) (s : Sym (GI P T) (q + 1)) :
    One (stabilize P T) q := by
  classical
  by_cases hs : (tSupport P T s).Nonempty
  · let a := leastT T (tSupport P T s) hs
    have ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
      (mem_tSupport P T s a).mp (leastT_mem T _ hs)
    exact tRel P T a ⊗ₜ[ℤ]
      SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
        (eraseT P T s a ha)
  · exact 0

/-- Degree-zero part of the integral stabilization contraction. -/
def hZero (q : ℕ) :
    Sym[ℤ] (Fin (q + 1)) (P.gen × T) →ₗ[ℤ] One (stabilize P T) q :=
  (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1)).constr ℤ
    (hZeroOnBasis P T q)

@[simp]
private theorem hZero_basis (q : ℕ) (s : Sym (GI P T) (q + 1)) :
    hZero P T q
      (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s) =
        hZeroOnBasis P T q s := by
  exact (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1)).constr_basis
    ℤ (hZeroOnBasis P T q) s

private def eraseSummandGen : (P.gen × T) →ₗ[ℤ] (P.gen × T) where
  toFun x := (x.1, 0)
  map_add' x y := by ext <;> simp
  map_smul' z x := by ext <;> simp

private def eraseSummandRel : (P.rel × T) →ₗ[ℤ] (P.rel × T) where
  toFun x := (x.1, 0)
  map_add' x y := by ext <;> simp
  map_smul' z x := by ext <;> simp

private def pGen : P.gen →ₗ[ℤ] (P.gen × T) where
  toFun x := (x, 0)
  map_add' x y := by ext <;> simp
  map_smul' z x := by ext <;> simp

@[simp]
private theorem stabilize_d_pRel (i : Fin (relRank P)) :
    (stabilize P T).d (pRel P T i) = pGen P T (P.d (relBasis P i)) := by
  simp [pRel, pGen]

@[simp]
private theorem stabilize_d_tRel (i : Fin (summandRank T)) :
    (stabilize P T).d (tRel P T i) =
      stabilizedGenBasis P T (Sum.inr i) := by
  simp [tRel]

private theorem hZero_insert_pGen_basis (q : ℕ) (i : Fin (genRank P))
    (s : Sym (GI P T) (q + 1)) :
    hZero P T (q + 1)
        (SymmetricPower.insert ℤ (P.gen × T) (q + 1)
          (pGen P T (genBasis P i))
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s)) =
      if hs : (tSupport P T s).Nonempty then
        let a := leastT T (tSupport P T s) hs
        let ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
          (mem_tSupport P T s a).mp (leastT_mem T _ hs)
        tRel P T a ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ (P.gen × T) q
            (pGen P T (genBasis P i))
            (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
              (eraseT P T s a ha))
      else 0 := by
  classical
  have hp : pGen P T (genBasis P i) =
      stabilizedGenBasis P T (Sum.inl i) := by simp [pGen]
  rw [hp, SymmetricPower.insert_monomialBasis, hZero_basis]
  unfold hZeroOnBasis
  simp only [tSupport_cons_inl]
  by_cases hs : (tSupport P T s).Nonempty
  · simp only [dif_pos hs]
    let a := leastT T (tSupport P T s) hs
    have ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
      (mem_tSupport P T s a).mp (leastT_mem T _ hs)
    rw [eraseT_cons_inl P T s a ha i,
      SymmetricPower.insert_monomialBasis]
    rfl
  · simp [hs]
    rfl

private theorem hZero_insert_pGen (q : ℕ) (x : P.gen)
    (s : Sym (GI P T) (q + 1)) :
    hZero P T (q + 1)
        (SymmetricPower.insert ℤ (P.gen × T) (q + 1) (pGen P T x)
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s)) =
      if hs : (tSupport P T s).Nonempty then
        let a := leastT T (tSupport P T s) hs
        let ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
          (mem_tSupport P T s a).mp (leastT_mem T _ hs)
        tRel P T a ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ (P.gen × T) q (pGen P T x)
            (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
              (eraseT P T s a ha))
      else 0 := by
  let lhs : P.gen →ₗ[ℤ] One (stabilize P T) (q + 1) :=
    {
      toFun := fun y ↦ hZero P T (q + 1)
        (SymmetricPower.insert ℤ (P.gen × T) (q + 1) (pGen P T y)
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s))
      map_add' := by intro y z; simp [SymmetricPower.insert_add_apply]
      map_smul' := by intro c y; simp [SymmetricPower.insert_smul_apply] }
  let rhs : P.gen →ₗ[ℤ] One (stabilize P T) (q + 1) := by
    classical
    by_cases hs : (tSupport P T s).Nonempty
    · let a := leastT T (tSupport P T s) hs
      have ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
        (mem_tSupport P T s a).mp (leastT_mem T _ hs)
      exact (TensorProduct.mk ℤ (P.rel × T) _ (tRel P T a)).comp <|
        (SymmetricPower.insertRight ℤ (P.gen × T) q
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
            (eraseT P T s a ha))).comp (pGen P T)
    · exact 0
  have hmaps : lhs = rhs := by
    apply (genBasis P).ext
    intro i
    change hZero P T (q + 1)
        (SymmetricPower.insert ℤ (P.gen × T) (q + 1)
          (pGen P T (genBasis P i))
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s)) = _
    rw [hZero_insert_pGen_basis]
    unfold rhs
    split_ifs <;> rfl
  have hx := LinearMap.congr_fun hmaps x
  change hZero P T (q + 1)
      (SymmetricPower.insert ℤ (P.gen × T) (q + 1) (pGen P T x)
        (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s)) = _ at hx
  unfold rhs at hx
  split_ifs at hx ⊢ <;> exact hx

private theorem hZero_insert_tGen_basis (q : ℕ)
    (j : Fin (summandRank T)) (s : Sym (GI P T) (q + 1)) :
    hZero P T (q + 1)
        (SymmetricPower.insert ℤ (P.gen × T) (q + 1)
          (stabilizedGenBasis P T (Sum.inr j))
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s)) =
      let hs : (tSupport P T (Sum.inr j ::ₛ s)).Nonempty := by
        rw [tSupport_cons_inr]
        exact ⟨j, Finset.mem_insert_self j _⟩
      let a := leastT T (tSupport P T (Sum.inr j ::ₛ s)) hs
      let ha : Sum.inr a ∈ ((Sum.inr j ::ₛ s) : Multiset (GI P T)) :=
        (mem_tSupport P T _ a).mp (leastT_mem T _ hs)
      tRel P T a ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1)
          (eraseT P T (Sum.inr j ::ₛ s) a ha) := by
  classical
  rw [SymmetricPower.insert_monomialBasis, hZero_basis]
  unfold hZeroOnBasis
  simp only [dif_pos (show (tSupport P T (Sum.inr j ::ₛ s)).Nonempty by
    rw [tSupport_cons_inr]
    exact ⟨j, Finset.mem_insert_self j _⟩)]
  rfl

private theorem d_hZeroOnBasis (q : ℕ) (s : Sym (GI P T) (q + 1)) :
    dOne (stabilize P T) q (hZeroOnBasis P T q s) =
      SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s -
        SymmetricPower.map (R := ℤ) (ι := Fin (q + 1))
          (eraseSummandGen P T)
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s) := by
  classical
  rw [hZeroOnBasis]
  split_ifs with hs
  · simp only [dOne_tmul, stabilize_d_apply, tRel, stabilizedRelBasis_inr]
    let a := leastT T (tSupport P T s) hs
    have ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
      (mem_tSupport P T s a).mp (leastT_mem T _ hs)
    have hd : ((P.d 0, summandBasis T a) : P.gen × T) =
        stabilizedGenBasis P T (Sum.inr a) := by simp
    rw [hd]
    change SymmetricPower.insert ℤ (P.gen × T) q
        (stabilizedGenBasis P T (Sum.inr a))
        (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
          (eraseT P T s a ha)) = _
    rw [SymmetricPower.insert_monomialBasis, cons_eraseT P T s a ha]
    rw [SymmetricPower.map_monomialBasis_eq_zero_of_mem
      (stabilizedGenBasis P T) (q + 1) (eraseSummandGen P T) s (Sum.inr a) ha]
    · simp
    · simp [eraseSummandGen]
  · simp only [map_zero]
    have heq : SymmetricPower.map (R := ℤ) (ι := Fin (q + 1))
          (eraseSummandGen P T)
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s) =
        SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s := by
      apply SymmetricPower.map_monomialBasis_eq_self_of_mem
      intro i hi
      rcases i with i | i
      · simp [eraseSummandGen]
      · exfalso
        apply hs
        exact ⟨i, (mem_tSupport P T s i).mpr hi⟩
    rw [heq, sub_self]
    rfl

private theorem d_hZero (q : ℕ)
    (x : Sym[ℤ] (Fin (q + 1)) (P.gen × T)) :
    dOne (stabilize P T) q (hZero P T q x) =
      x - SymmetricPower.map (R := ℤ) (ι := Fin (q + 1))
        (eraseSummandGen P T) x := by
  let lhs : Sym[ℤ] (Fin (q + 1)) (P.gen × T) →ₗ[ℤ]
      Sym[ℤ] (Fin (q + 1)) (P.gen × T) :=
    (dOne (stabilize P T) q).comp (hZero P T q)
  let rhs : Sym[ℤ] (Fin (q + 1)) (P.gen × T) →ₗ[ℤ]
      Sym[ℤ] (Fin (q + 1)) (P.gen × T) :=
    {
      toFun := fun y ↦ y - SymmetricPower.map (R := ℤ) (ι := Fin (q + 1))
        (eraseSummandGen P T) y
      map_add' := by intro y z; simp; abel
      map_smul' := by intro c y; simp [smul_sub]; rfl }
  have hmaps : lhs = rhs := by
    apply (SymmetricPower.monomialBasis
      (stabilizedGenBasis P T) (q + 1)).ext
    intro s
    change dOne (stabilize P T) q
        (hZero P T q
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s)) = _
    rw [hZero_basis, d_hZeroOnBasis]
    rfl
  exact LinearMap.congr_fun hmaps x

private theorem totalSupport_nonempty_of_inl {q : ℕ}
    (a : Fin (relRank P)) (s : Sym (GI P T) q)
    (hs : (totalSupport P T (Sum.inl a) s).Nonempty) :
    (tSupport P T s).Nonempty := hs

private theorem least_total_mem_sym_of_inl {q : ℕ}
    (a : Fin (relRank P)) (s : Sym (GI P T) q)
    (hs : (totalSupport P T (Sum.inl a) s).Nonempty) :
    Sum.inr (leastT T (totalSupport P T (Sum.inl a) s) hs) ∈
      (s : Multiset (GI P T)) := by
  apply (mem_tSupport P T s _).mp
  exact leastT_mem T _ hs

private theorem least_total_mem_sym_of_inr_ne {q : ℕ}
    (a : Fin (summandRank T)) (s : Sym (GI P T) q)
    (hs : (totalSupport P T (Sum.inr a) s).Nonempty)
    (hne : leastT T (totalSupport P T (Sum.inr a) s) hs ≠ a) :
    Sum.inr (leastT T (totalSupport P T (Sum.inr a) s) hs) ∈
      (s : Multiset (GI P T)) := by
  have hm := leastT_mem T _ hs
  change leastT T (insert a (tSupport P T s)) hs ∈
    insert a (tSupport P T s) at hm
  rw [Finset.mem_insert] at hm
  exact (mem_tSupport P T s _).mp (hm.resolve_left hne)

private def wedgeRel (x y : P.rel × T) : ⋀[ℤ]^2 (P.rel × T) :=
  exteriorPower.ιMulti ℤ 2 (Fin.cons x (Fin.cons y Fin.elim0))

private theorem dTwo_wedgeRel (q : ℕ) (x y : P.rel × T)
    (s : Sym[ℤ] (Fin q) (P.gen × T)) :
    dTwo (stabilize P T) q (wedgeRel P T x y ⊗ₜ[ℤ] s) =
      x ⊗ₜ[ℤ] SymmetricPower.insert ℤ (P.gen × T) q
          ((stabilize P T).d y) s -
        y ⊗ₜ[ℤ] SymmetricPower.insert ℤ (P.gen × T) q
          ((stabilize P T).d x) s := by
  unfold wedgeRel
  have h := dTwo_wedge_tmul (stabilize P T) q
    (Fin.cons x (Fin.cons y Fin.elim0)) s
  change _ = _ at h
  exact h

private def hOneOnBasis (q : ℕ)
    (js : RI P T × Sym (GI P T) (q + 1)) :
    Two (stabilize P T) q := by
  classical
  rcases js with ⟨j, s⟩
  by_cases hs : (totalSupport P T j s).Nonempty
  · let a := leastT T (totalSupport P T j s) hs
    rcases j with j | j
    · have ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
        least_total_mem_sym_of_inl P T j s hs
      exact wedgeRel P T (pRel P T j) (tRel P T a) ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
          (eraseT P T s a ha)
    · by_cases hja : a = j
      · exact 0
      · have ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
          least_total_mem_sym_of_inr_ne P T j s hs hja
        exact wedgeRel P T (tRel P T j) (tRel P T a) ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
            (eraseT P T s a ha)
  · exact 0

/-- Degree-one part of the integral stabilization contraction. -/
def hOne (q : ℕ) :
    One (stabilize P T) (q + 1) →ₗ[ℤ] Two (stabilize P T) q :=
  (oneBasis P T (q + 1)).constr ℤ (hOneOnBasis P T q)

@[simp]
private theorem hOne_basis (q : ℕ)
    (js : RI P T × Sym (GI P T) (q + 1)) :
    hOne P T q (oneBasis P T (q + 1) js) = hOneOnBasis P T q js := by
  exact (oneBasis P T (q + 1)).constr_basis ℤ (hOneOnBasis P T q) js

private theorem oneBasis_apply (q : ℕ) (i : RI P T) (s : Sym (GI P T) q) :
    oneBasis P T q (i, s) = stabilizedRelBasis P T i ⊗ₜ[ℤ]
      SymmetricPower.monomialBasis (stabilizedGenBasis P T) q s := by
  change ((stabilizedRelBasis P T).tensorProduct
      (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q)) (i, s) = _
  exact Module.Basis.tensorProduct_apply _ _ i s

private theorem oneMap_retract_basis (q : ℕ) (i : RI P T)
    (s : Sym (GI P T) q) :
    PresentationHomology.oneMap (stabilize P T) (stabilize P T)
        ((stabilizeIncl P T).comp (stabilizeProj P T)) q
        (oneBasis P T q (i, s)) =
      eraseSummandRel P T (stabilizedRelBasis P T i) ⊗ₜ[ℤ]
        SymmetricPower.map (R := ℤ) (ι := Fin q) (eraseSummandGen P T)
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q s) := by
  rw [oneBasis_apply]
  change (TensorProduct.map _ _)
      (stabilizedRelBasis P T i ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (stabilizedGenBasis P T) q s) = _
  rw [TensorProduct.map_tmul]
  change ((stabilizeIncl P T).comp (stabilizeProj P T)).relMap
        (stabilizedRelBasis P T i) ⊗ₜ[ℤ]
      SymmetricPower.map (R := ℤ) (ι := Fin q)
        (((stabilizeIncl P T).comp (stabilizeProj P T)).genMap)
        (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q s) = _
  rfl

private theorem contraction_basis_inl (q : ℕ) (j : Fin (relRank P))
    (s : Sym (GI P T) (q + 1)) :
    dTwo (stabilize P T) q
        (hOne P T q (oneBasis P T (q + 1) (Sum.inl j, s))) +
      hZero P T (q + 1)
        (dOne (stabilize P T) (q + 1)
          (oneBasis P T (q + 1) (Sum.inl j, s))) =
      oneBasis P T (q + 1) (Sum.inl j, s) -
        PresentationHomology.oneMap (stabilize P T) (stabilize P T)
          ((stabilizeIncl P T).comp (stabilizeProj P T)) (q + 1)
          (oneBasis P T (q + 1) (Sum.inl j, s)) := by
  classical
  rw [hOne_basis]
  have hone : oneBasis P T (q + 1) (Sum.inl j, s) =
      pRel P T j ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s := by
    rw [oneBasis_apply]
    rfl
  rw [hone]
  change dTwo (stabilize P T) q (hOneOnBasis P T q (Sum.inl j, s)) +
      hZero P T (q + 1)
        (SymmetricPower.insert ℤ (P.gen × T) (q + 1)
          ((stabilize P T).d (pRel P T j))
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s)) = _
  rw [stabilize_d_pRel]
  unfold hOneOnBasis
  by_cases hs : (tSupport P T s).Nonempty
  · simp only [totalSupport, dif_pos hs]
    let a := leastT T (tSupport P T s) hs
    have ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
      (mem_tSupport P T s a).mp (leastT_mem T _ hs)
    change dTwo (stabilize P T) q
        (wedgeRel P T (pRel P T j) (tRel P T a) ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
            (eraseT P T s a ha)) + _ = _
    rw [dTwo_wedgeRel, stabilize_d_tRel, stabilize_d_pRel,
      SymmetricPower.insert_monomialBasis, cons_eraseT P T s a ha]
    rw [hZero_insert_pGen P T q (P.d (relBasis P j)) s]
    simp only [dif_pos hs]
    change pRel P T j ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s -
        tRel P T a ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ (P.gen × T) q
            (pGen P T (P.d (relBasis P j)))
            (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
              (eraseT P T s a ha)) +
        tRel P T a ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ (P.gen × T) q
            (pGen P T (P.d (relBasis P j)))
            (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
              (eraseT P T s a ha)) = _
    rw [sub_add_cancel]
    rw [← hone, oneMap_retract_basis, hone]
    rw [SymmetricPower.map_monomialBasis_eq_zero_of_mem
      (stabilizedGenBasis P T) (q + 1) (eraseSummandGen P T) s (Sum.inr a) ha]
    · simp
      rfl
    · simp [eraseSummandGen]
  · simp only [totalSupport, dif_neg hs, map_zero, zero_add]
    rw [hZero_insert_pGen P T q (P.d (relBasis P j)) s]
    simp only [dif_neg hs]
    rw [← hone, oneMap_retract_basis, hone]
    have hfix : SymmetricPower.map (R := ℤ) (ι := Fin (q + 1))
        (eraseSummandGen P T)
        (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s) =
      SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s := by
      apply SymmetricPower.map_monomialBasis_eq_self_of_mem
      intro i hi
      rcases i with i | i
      · simp [eraseSummandGen]
      · exfalso
        apply hs
        exact ⟨i, (mem_tSupport P T s i).mpr hi⟩
    rw [hfix]
    simp [eraseSummandRel, pRel]
    rfl

private theorem contraction_basis_inr (q : ℕ) (j : Fin (summandRank T))
    (s : Sym (GI P T) (q + 1)) :
    dTwo (stabilize P T) q
        (hOne P T q (oneBasis P T (q + 1) (Sum.inr j, s))) +
      hZero P T (q + 1)
        (dOne (stabilize P T) (q + 1)
          (oneBasis P T (q + 1) (Sum.inr j, s))) =
      oneBasis P T (q + 1) (Sum.inr j, s) -
        PresentationHomology.oneMap (stabilize P T) (stabilize P T)
          ((stabilizeIncl P T).comp (stabilizeProj P T)) (q + 1)
          (oneBasis P T (q + 1) (Sum.inr j, s)) := by
  classical
  rw [hOne_basis]
  have hone : oneBasis P T (q + 1) (Sum.inr j, s) =
      tRel P T j ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s := by
    rw [oneBasis_apply]
    rfl
  rw [hone]
  change dTwo (stabilize P T) q (hOneOnBasis P T q (Sum.inr j, s)) +
      hZero P T (q + 1)
        (SymmetricPower.insert ℤ (P.gen × T) (q + 1)
          ((stabilize P T).d (tRel P T j))
          (SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s)) = _
  rw [stabilize_d_tRel, hZero_insert_tGen_basis]
  unfold hOneOnBasis
  let hs : (totalSupport P T (Sum.inr j) s).Nonempty :=
    ⟨j, Finset.mem_insert_self j _⟩
  simp only [dif_pos hs]
  let a := leastT T (totalSupport P T (Sum.inr j) s) hs
  by_cases hja : a = j
  · rw [dif_pos hja]
    simp only [map_zero, zero_add]
    have hht : tSupport P T (Sum.inr j ::ₛ s) =
        totalSupport P T (Sum.inr j) s := tSupport_cons_inr P T j s
    have hleast : leastT T (tSupport P T (Sum.inr j ::ₛ s)) (by
          rw [hht]; exact hs) = a := by
      simp only [hht]
      rfl
    change tRel P T (leastT T (tSupport P T (Sum.inr j ::ₛ s)) (by
          rw [hht]; exact hs)) ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1)
          (eraseT P T (Sum.inr j ::ₛ s)
            (leastT T (tSupport P T (Sum.inr j ::ₛ s)) (by rw [hht]; exact hs))
            (by apply (mem_tSupport P T _ _).mp; exact leastT_mem T _ _)) = _
    simp only [hht] at hleast ⊢
    have hjleast : leastT T (totalSupport P T (Sum.inr j) s) (by exact hs) = j := hja
    simp only [hjleast]
    change tRel P T j ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1)
          (eraseT P T (Sum.inr j ::ₛ s) j (by exact Sym.mem_cons_self _ _)) = _
    rw [eraseT_cons_inr_head]
    change tRel P T j ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s = _
    rw [← hone, oneMap_retract_basis, hone]
    simp [eraseSummandRel, tRel]
    have hz : ((0, 0) : P.rel × T) = 0 := rfl
    rw [hz, TensorProduct.zero_tmul]
    symm
    exact sub_zero _

  · rw [dif_neg hja]
    have ha : Sum.inr a ∈ (s : Multiset (GI P T)) :=
      least_total_mem_sym_of_inr_ne P T j s hs hja
    change dTwo (stabilize P T) q
        (wedgeRel P T (tRel P T j) (tRel P T a) ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
            (eraseT P T s a ha)) + _ = _
    rw [dTwo_wedgeRel, stabilize_d_tRel, stabilize_d_tRel,
      SymmetricPower.insert_monomialBasis, cons_eraseT P T s a ha]
    have hht : tSupport P T (Sum.inr j ::ₛ s) =
        totalSupport P T (Sum.inr j) s := tSupport_cons_inr P T j s
    change tRel P T j ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s -
        tRel P T a ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ (P.gen × T) q
            (stabilizedGenBasis P T (Sum.inr j))
            (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
              (eraseT P T s a ha)) +
        tRel P T (leastT T (tSupport P T (Sum.inr j ::ₛ s)) (by
          rw [hht]; exact hs)) ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1)
            (eraseT P T (Sum.inr j ::ₛ s)
              (leastT T (tSupport P T (Sum.inr j ::ₛ s)) (by rw [hht]; exact hs))
              (by apply (mem_tSupport P T _ _).mp; exact leastT_mem T _ _)) = _
    have hleast : leastT T (tSupport P T (Sum.inr j ::ₛ s)) (by
          rw [hht]; exact hs) = a := by
      simp only [hht]
      rfl
    simp only [hht] at hleast ⊢
    change tRel P T j ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1) s -
        tRel P T a ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ (P.gen × T) q
            (stabilizedGenBasis P T (Sum.inr j))
            (SymmetricPower.monomialBasis (stabilizedGenBasis P T) q
              (eraseT P T s a ha)) +
        tRel P T a ⊗ₜ[ℤ]
          SymmetricPower.monomialBasis (stabilizedGenBasis P T) (q + 1)
            (eraseT P T (Sum.inr j ::ₛ s) a (by
              exact Sym.mem_cons_of_mem ha)) = _
    have herase : eraseT P T (Sum.inr j ::ₛ s) a (by
          exact Sym.mem_cons_of_mem ha) = Sum.inr j ::ₛ eraseT P T s a ha :=
      eraseT_cons_inr_ne P T s a j ha (Ne.symm hja)
    rw [herase, SymmetricPower.insert_monomialBasis, sub_add_cancel]
    rw [← hone, oneMap_retract_basis, hone]
    simp [eraseSummandRel, tRel]
    have hz : ((0, 0) : P.rel × T) = 0 := rfl
    rw [hz, TensorProduct.zero_tmul]
    symm
    exact sub_zero _

/-- The integral contraction identity behind stabilization.  On the part with
positive `T`-support, the final retract term vanishes, so this is the
fixed-exponent identity `d h + h d = id` used in weights two and three. -/
theorem stabilizationContractionIdentity (q : ℕ)
    (x : One (stabilize P T) (q + 1)) :
    dTwo (stabilize P T) q (hOne P T q x) +
      hZero P T (q + 1) (dOne (stabilize P T) (q + 1) x) =
      x - PresentationHomology.oneMap (stabilize P T) (stabilize P T)
        ((stabilizeIncl P T).comp (stabilizeProj P T)) (q + 1) x := by
  let lhs : One (stabilize P T) (q + 1) →ₗ[ℤ]
      One (stabilize P T) (q + 1) :=
    (dTwo (stabilize P T) q).comp (hOne P T q) +
      (hZero P T (q + 1)).comp (dOne (stabilize P T) (q + 1))
  let rhs : One (stabilize P T) (q + 1) →ₗ[ℤ]
      One (stabilize P T) (q + 1) := {
    toFun := fun y ↦ y - PresentationHomology.oneMap
      (stabilize P T) (stabilize P T)
      ((stabilizeIncl P T).comp (stabilizeProj P T)) (q + 1) y
    map_add' := by intro y z; simp; abel
    map_smul' := by
      intro c y
      rw [map_smul]
      exact (smul_sub c y _).symm }
  have hmaps : lhs = rhs := by
    apply (oneBasis P T (q + 1)).ext
    rintro ⟨i, s⟩
    rcases i with i | i
    · exact contraction_basis_inl P T q i s
    · exact contraction_basis_inr P T q i s
  exact LinearMap.congr_fun hmaps x

/-- Projection away from a contractible summand is an equivalence on the
degree-one homology of every positive-weight Koszul complex. -/
noncomputable def stabilizeHomologyEquiv (q : ℕ) :
    homologyOne (stabilize P T) q ≃ₗ[ℤ] homologyOne P q where
  toLinearMap := PresentationHomology.map (stabilize P T) P (stabilizeProj P T) q
  invFun := PresentationHomology.map P (stabilize P T) (stabilizeIncl P T) q
  left_inv := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      (boundariesOne (stabilize P T) q) y
    change (boundariesOne (stabilize P T) q).mkQ
        (PresentationHomology.cyclesMap P (stabilize P T) (stabilizeIncl P T) q
          (PresentationHomology.cyclesMap (stabilize P T) P (stabilizeProj P T) q z)) =
      (boundariesOne (stabilize P T) q).mkQ z
    have hcyc : PresentationHomology.cyclesMap P (stabilize P T)
          (stabilizeIncl P T) q
          (PresentationHomology.cyclesMap (stabilize P T) P (stabilizeProj P T) q z) =
        PresentationHomology.cyclesMap (stabilize P T) (stabilize P T)
          ((stabilizeIncl P T).comp (stabilizeProj P T)) q z := by
      apply Subtype.ext
      exact (LinearMap.congr_fun
        (PresentationHomology.oneMap_comp (stabilize P T) P (stabilizeProj P T)
          (stabilize P T) (stabilizeIncl P T) q) z.1).symm
    rw [hcyc]
    apply (Submodule.Quotient.eq _).mpr
    change (PresentationHomology.cyclesMap (stabilize P T) (stabilize P T)
        ((stabilizeIncl P T).comp (stabilizeProj P T)) q z - z) ∈
      boundariesOne (stabilize P T) q
    cases q with
    | zero =>
        have hz : z.1 = 0 := by
          have hzcycle := z.property
          change dOne (stabilize P T) 0 z.1 = 0 at hzcycle
          let eOne : One (stabilize P T) 0 ≃ₗ[ℤ] P.rel × T :=
            (TensorProduct.congr (LinearEquiv.refl ℤ (P.rel × T))
              (SymmetricPower.degreeZeroLinearEquiv (stabilizedGenBasis P T))).trans
                (TensorProduct.rid ℤ (P.rel × T))
          let eSym : Sym[ℤ] (Fin 1) (P.gen × T) ≃ₗ[ℤ] (P.gen × T) :=
            SymmetricPower.degreeOneLinearEquiv (stabilizedGenBasis P T)
          have hmaps : eSym.toLinearMap.comp (dOne (stabilize P T) 0) =
              (stabilize P T).d.comp eOne.toLinearMap := by
            apply (oneBasis P T 0).ext
            rintro ⟨i, s⟩
            have hs : s = Sym.nil := Subsingleton.elim _ _
            subst s
            rw [oneBasis_apply]
            simp only [LinearMap.comp_apply]
            change eSym
                (SymmetricPower.insert ℤ (P.gen × T) 0
                  ((stabilize P T).d (stabilizedRelBasis P T i))
                  (SymmetricPower.monomialBasis
                    (stabilizedGenBasis P T) 0 Sym.nil)) = _
            rw [SymmetricPower.insert_monomialBasis_zero,
              SymmetricPower.degreeOneLinearEquiv_degreeOne]
            have heOne : eOne
                  (stabilizedRelBasis P T i ⊗ₜ[ℤ]
                    SymmetricPower.monomialBasis
                      (stabilizedGenBasis P T) 0 Sym.nil) =
                stabilizedRelBasis P T i := by
              change (TensorProduct.rid ℤ (P.rel × T))
                  ((TensorProduct.congr (LinearEquiv.refl ℤ (P.rel × T))
                    (SymmetricPower.degreeZeroLinearEquiv
                      (stabilizedGenBasis P T)))
                    (stabilizedRelBasis P T i ⊗ₜ[ℤ]
                      SymmetricPower.monomialBasis
                        (stabilizedGenBasis P T) 0 Sym.nil)) = _
              rw [TensorProduct.congr_tmul,
                SymmetricPower.degreeZeroLinearEquiv_monomialBasis,
                TensorProduct.rid_tmul, one_smul]
              rfl
            exact congrArg (stabilize P T).d heOne.symm
          have hd : (stabilize P T).d (eOne z.1) = 0 := by
            have hh := LinearMap.congr_fun hmaps z.1
            change eSym (dOne (stabilize P T) 0 z.1) =
              (stabilize P T).d (eOne z.1) at hh
            rw [hzcycle] at hh
            calc
              (stabilize P T).d (eOne z.1) = eSym 0 := hh.symm
              _ = 0 := eSym.map_zero
          have he : eOne z.1 = 0 := by
            apply (stabilize P T).d_injective
            calc
              (stabilize P T).d (eOne z.1) = 0 := hd
              _ = (stabilize P T).d 0 := (map_zero _).symm
          exact eOne.injective (by simpa using he)
        have hfirst :
            (PresentationHomology.cyclesMap (stabilize P T) (stabilize P T)
              ((stabilizeIncl P T).comp (stabilizeProj P T)) 0 z).1 = 0 := by
          change PresentationHomology.oneMap (stabilize P T) (stabilize P T)
              ((stabilizeIncl P T).comp (stabilizeProj P T)) 0 z.1 = 0
          rw [hz, map_zero]
        have hdiff :
            PresentationHomology.cyclesMap (stabilize P T) (stabilize P T)
                ((stabilizeIncl P T).comp (stabilizeProj P T)) 0 z - z = 0 := by
          apply Subtype.ext
          change (PresentationHomology.cyclesMap (stabilize P T) (stabilize P T)
              ((stabilizeIncl P T).comp (stabilizeProj P T)) 0 z).1 - z.1 = 0
          rw [hfirst, hz, sub_zero]
        rw [hdiff]
        exact Submodule.zero_mem _
    | succ r =>
        refine ⟨-hOne P T r z.1, ?_⟩
        apply Subtype.ext
        change dTwo (stabilize P T) r (-hOne P T r z.1) = _
        rw [map_neg]
        have hc := stabilizationContractionIdentity P T r z.1
        have hzcycle := z.property
        change dOne (stabilize P T) (r + 1) z.1 = 0 at hzcycle
        rw [hzcycle] at hc
        have hzero : hZero P T (r + 1) 0 = 0 := map_zero _
        have hc' : dTwo (stabilize P T) r (hOne P T r z.1) =
            z.1 - PresentationHomology.oneMap (stabilize P T) (stabilize P T)
              ((stabilizeIncl P T).comp (stabilizeProj P T)) (r + 1) z.1 := by
          calc
            dTwo (stabilize P T) r (hOne P T r z.1) =
                dTwo (stabilize P T) r (hOne P T r z.1) + 0 := (add_zero _).symm
            _ = dTwo (stabilize P T) r (hOne P T r z.1) +
                hZero P T (r + 1) 0 := congrArg _ hzero.symm
            _ = _ := hc
        change -dTwo (stabilize P T) r (hOne P T r z.1) =
          (PresentationHomology.cyclesMap (stabilize P T) (stabilize P T)
              ((stabilizeIncl P T).comp (stabilizeProj P T)) (r + 1) z).1 - z.1
        change -dTwo (stabilize P T) r (hOne P T r z.1) =
          PresentationHomology.oneMap (stabilize P T) (stabilize P T)
              ((stabilizeIncl P T).comp (stabilizeProj P T)) (r + 1) z.1 - z.1
        rw [hc']
        abel
  right_inv := by
    intro y
    have hcomp := PresentationHomology.map_comp P (stabilize P T)
      (stabilizeIncl P T) P (stabilizeProj P T) q
    have hy := LinearMap.congr_fun hcomp y
    change PresentationHomology.map (stabilize P T) P (stabilizeProj P T) q
        (PresentationHomology.map P (stabilize P T) (stabilizeIncl P T) q y) = y
    have hy' : PresentationHomology.map (stabilize P T) P (stabilizeProj P T) q
          (PresentationHomology.map P (stabilize P T) (stabilizeIncl P T) q y) =
        PresentationHomology.map P P
          ((stabilizeProj P T).comp (stabilizeIncl P T)) q y := by
      exact hy.symm
    rw [hy', stabilizeProj_comp_stabilizeIncl]
    exact LinearMap.congr_fun (PresentationHomology.map_id P q) y

/-- The two cylinder endpoints induce the same map on degree-one Koszul
homology.  Both are inverses of the stabilization projection. -/
theorem cylinder_map_zero_eq_one (q : ℕ) :
    PresentationHomology.map P (cylinder P) (cylinderInclZero P) q =
      PresentationHomology.map P (cylinder P) (cylinderInclOne P) q := by
  apply LinearMap.ext
  intro x
  apply (stabilizeHomologyEquiv P P.gen q).injective
  have hzero := LinearMap.congr_fun
    (PresentationHomology.map_comp P (cylinder P) (cylinderInclZero P)
      P (cylinderRetract P) q) x
  have hone := LinearMap.congr_fun
    (PresentationHomology.map_comp P (cylinder P) (cylinderInclOne P)
      P (cylinderRetract P) q) x
  rw [cylinderRetract_comp_zero] at hzero
  rw [cylinderRetract_comp_one] at hone
  have hid := LinearMap.congr_fun (PresentationHomology.map_id P q) x
  exact hzero.symm.trans (hid.trans (hid.symm.trans hone))

/-- Strict lifts of the same map of presented groups induce the same map on
degree-one Koszul homology.  This is the integral presentation-homotopy
invariance theorem; its proof factors the homotopy through the cylinder. -/
theorem homologyMap_eq_of_homotopy {B : Type*} [AddCommGroup B]
    (Q : Presentation B) {f : A →ₗ[ℤ] B}
    (F G : Hom P Q f) (q : ℕ) :
    PresentationHomology.map P Q F q =
      PresentationHomology.map P Q G q := by
  obtain ⟨H⟩ := homotopy_exists P Q F G
  let C := H.cylinderMap P Q
  have hzero := PresentationHomology.map_comp P (cylinder P)
    (cylinderInclZero P) Q C q
  have hone := PresentationHomology.map_comp P (cylinder P)
    (cylinderInclOne P) Q C q
  have endpoints := cylinder_map_zero_eq_one P q
  rw [endpoints] at hzero
  have hstrictZero : C.comp (cylinderInclZero P) = G := by
    change compRightId P (H.cylinderMap P Q) (cylinderInclZero P) = G
    exact H.cylinderMap_comp_zero P Q
  have hstrictOne : C.comp (cylinderInclOne P) = F := by
    change compRightId P (H.cylinderMap P Q) (cylinderInclOne P) = F
    exact H.cylinderMap_comp_one P Q
  rw [hstrictZero] at hzero
  rw [hstrictOne] at hone
  exact hone.trans hzero.symm

/-- A chosen strict comparison from an arbitrary finite free presentation to
the canonical presentation. -/
noncomputable def toCanonical [Finite A] :
    Hom P (canonical A) LinearMap.id :=
  Classical.choice (hom_nonempty P (canonical A) LinearMap.id)

/-- A chosen strict comparison from the canonical presentation to an
arbitrary finite free presentation. -/
noncomputable def fromCanonical [Finite A] :
    Hom (canonical A) P LinearMap.id :=
  Classical.choice (hom_nonempty (canonical A) P LinearMap.id)

/-- Resolution-independence: the Koszul `H₁` of any finite free two-term
presentation is canonically equivalent to `L₁S^(q+1)` computed from the
canonical presentation. -/
noncomputable def homologyComparisonEquiv [Finite A] (q : ℕ) :
    homologyOne P q ≃ₗ[ℤ] FirstDerivedSymmetricPower q A where
  toLinearMap := PresentationHomology.map P (canonical A) (toCanonical P) q
  invFun := PresentationHomology.map (canonical A) P (fromCanonical P) q
  left_inv := by
    intro x
    have hcomp := LinearMap.congr_fun
      (PresentationHomology.map_comp P (canonical A) (toCanonical P)
        P (fromCanonical P) q) x
    have heq := LinearMap.congr_fun
      (homologyMap_eq_of_homotopy P P
        ((fromCanonical P).comp (toCanonical P)) (Hom.id P) q) x
    have hid := LinearMap.congr_fun (PresentationHomology.map_id P q) x
    exact hcomp.symm.trans (heq.trans hid)
  right_inv := by
    intro x
    have hcomp := LinearMap.congr_fun
      (PresentationHomology.map_comp (canonical A) P (fromCanonical P)
        (canonical A) (toCanonical P) q) x
    have heq := LinearMap.congr_fun
      (homologyMap_eq_of_homotopy (canonical A) (canonical A)
        ((toCanonical P).comp (fromCanonical P))
        (Hom.id (canonical A)) q) x
    have hid := LinearMap.congr_fun
      (PresentationHomology.map_id (canonical A) q) x
    exact hcomp.symm.trans (heq.trans hid)

/-- The comparison equivalence is independent of the chosen strict lift: any
lift to the canonical presentation gives its forward map. -/
theorem homologyComparisonEquiv_toLinearMap_eq [Finite A]
    (q : ℕ) (F : Hom P (canonical A) LinearMap.id) :
    (homologyComparisonEquiv P q).toLinearMap =
      PresentationHomology.map P (canonical A) F q :=
  homologyMap_eq_of_homotopy P (canonical A) (toCanonical P) F q

/-- Naturality of resolution comparison with respect to an arbitrary strict
lift of a homomorphism of presented groups. -/
theorem homologyComparison_natural {B : Type*} [AddCommGroup B] [Finite A]
    [Finite B] (Q : Presentation B) {f : A →ₗ[ℤ] B}
    (F : Hom P Q f) (q : ℕ) :
    (homologyComparisonEquiv Q q).toLinearMap.comp
        (PresentationHomology.map P Q F q) =
      PresentationHomology.map (canonical A) (canonical B)
          (canonicalHom f) q ∘ₗ
        (homologyComparisonEquiv P q).toLinearMap := by
  let leftLift : Hom P (canonical B) f := (toCanonical Q).comp F
  let rightLift : Hom P (canonical B) f :=
    (canonicalHom f).comp (toCanonical P)
  have hleft := PresentationHomology.map_comp P Q F
    (canonical B) (toCanonical Q) q
  have hright := PresentationHomology.map_comp P (canonical A) (toCanonical P)
    (canonical B) (canonicalHom f) q
  change PresentationHomology.map Q (canonical B) (toCanonical Q) q ∘ₗ
        PresentationHomology.map P Q F q =
      PresentationHomology.map (canonical A) (canonical B) (canonicalHom f) q ∘ₗ
        PresentationHomology.map P (canonical A) (toCanonical P) q
  rw [← hleft, ← hright]
  exact homologyMap_eq_of_homotopy P (canonical B) leftLift rightLift q
end
end Koszul.Presentation
