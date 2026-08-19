import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Tactic
import Mathlib.Util.AssertNoSorry

/-!
# Ordered invariant-factor presentations over the integers

This file strengthens the square diagonal basis supplied by Mathlib's Smith
normal form.  When the quotient by a full-rank submodule is finite, the
diagonal entries are made positive and then ordered by divisibility.  The
ordering operation transports both bases; it is not a permutation of a list
of coefficients.
-/

namespace LieRings

noncomputable section

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- Bases for a full-rank integral submodule whose positive diagonal entries
are in invariant-factor order. -/
structure InvariantFactorPresentation (N : Submodule ℤ M) where
  rank : ℕ
  ambientBasis : Module.Basis (Fin rank) ℤ M
  relationBasis : Module.Basis (Fin rank) ℤ N
  diagonal : Fin rank → ℕ
  diagonal_pos : ∀ i, 0 < diagonal i
  relation_eq : ∀ i, (relationBasis i : M) =
    (diagonal i : ℤ) • ambientBasis i
  diagonal_dvd : ∀ i j, i ≤ j → diagonal i ∣ diagonal j

namespace InvariantFactorPresentation

/-- The unit which changes an integer into its nonnegative absolute value. -/
private def signUnit (a : ℤ) : ℤˣ := if 0 ≤ a then 1 else -1

@[simp]
private theorem coe_signUnit_mul (a : ℤ) :
    (signUnit a : ℤ) * a = a.natAbs := by
  by_cases hz : a = 0
  · simp [hz, signUnit]
  · rw [← Int.sign_mul_self_eq_natAbs]
    by_cases ha : 0 ≤ a
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
      simp [signUnit, ha, Int.sign_eq_one_of_pos ha']
    · have ha' : a < 0 := lt_of_not_ge ha
      simp [signUnit, ha, Int.sign_eq_neg_one_of_neg ha']

/-- A positive diagonal presentation, before invariant-factor ordering. -/
private structure DiagonalPresentation (r : ℕ) (N : Submodule ℤ M) where
  ambientBasis : Module.Basis (Fin r) ℤ M
  relationBasis : Module.Basis (Fin r) ℤ N
  diagonal : Fin r → ℕ
  diagonal_pos : ∀ i, 0 < diagonal i
  relation_eq : ∀ i, (relationBasis i : M) =
    (diagonal i : ℤ) • ambientBasis i

/-- A linear coordinate change which applies a `2 × 2` matrix in the
coordinates `i,j` and is the identity elsewhere. -/
private def pairCoord {r : ℕ} (p q s t : ℤ) (i j : Fin r) :
    (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ) where
  toFun x k := if k = i then p * x i + q * x j
    else if k = j then s * x i + t * x j else x k
  map_add' x y := by
    funext k
    change
      (if k = i then p * (x + y) i + q * (x + y) j
        else if k = j then s * (x + y) i + t * (x + y) j else (x + y) k) =
      (if k = i then p * x i + q * x j
        else if k = j then s * x i + t * x j else x k) +
      (if k = i then p * y i + q * y j
        else if k = j then s * y i + t * y j else y k)
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext k
    change
      (if k = i then p * (c • x) i + q * (c • x) j
        else if k = j then s * (c • x) i + t * (c • x) j else (c • x) k) =
      c • (if k = i then p * x i + q * x j
        else if k = j then s * x i + t * x j else x k)
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring

@[simp]
private theorem pairCoord_apply_left {r : ℕ} (p q s t : ℤ)
    (i j : Fin r) (hij : i ≠ j) (x : Fin r → ℤ) :
    pairCoord p q s t i j x i = p * x i + q * x j := by
  simp [pairCoord, hij]

@[simp]
private theorem pairCoord_apply_right {r : ℕ} (p q s t : ℤ)
    (i j : Fin r) (hij : i ≠ j) (x : Fin r → ℤ) :
    pairCoord p q s t i j x j = s * x i + t * x j := by
  simp [pairCoord, hij, hij.symm]

@[simp]
private theorem pairCoord_apply_other {r : ℕ} (p q s t : ℤ)
    (i j k : Fin r) (hki : k ≠ i) (hkj : k ≠ j) (x : Fin r → ℤ) :
    pairCoord p q s t i j x k = x k := by
  simp [pairCoord, hki, hkj]

/-- The row operation `U` in the two-coordinate gcd/lcm refinement. -/
private def uEquiv {r : ℕ} (ap bp : ℕ) (u v : ℤ)
    (hbez : (ap : ℤ) * u + (bp : ℤ) * v = 1)
    (i j : Fin r) (hij : i ≠ j) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ) := by
  let f := pairCoord u v (-(bp : ℤ)) (ap : ℤ) i j
  let g := pairCoord (ap : ℤ) (-v) (bp : ℤ) u i j
  refine LinearEquiv.ofLinear f g ?_ ?_
  · apply LinearMap.ext
    intro x
    funext k
    by_cases hki : k = i
    · subst k
      simp [f, g, hij]
      linear_combination (hbez) * x i
    · by_cases hkj : k = j
      · subst k
        simp [f, g, hij]
        linear_combination (hbez) * x j
      · simp [f, g, hki, hkj]
  · apply LinearMap.ext
    intro x
    funext k
    by_cases hki : k = i
    · subst k
      simp [f, g, hij]
      linear_combination (hbez) * x i
    · by_cases hkj : k = j
      · subst k
        simp [f, g, hij]
        linear_combination (hbez) * x j
      · simp [f, g, hki, hkj]

/-- The column operation `V` in the two-coordinate gcd/lcm refinement. -/
private def vEquiv {r : ℕ} (ap bp : ℕ) (u v : ℤ)
    (hbez : (ap : ℤ) * u + (bp : ℤ) * v = 1)
    (i j : Fin r) (hij : i ≠ j) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ) := by
  let f := pairCoord 1 (-(v * (bp : ℤ))) 1 (u * (ap : ℤ)) i j
  let g := pairCoord (u * (ap : ℤ)) (v * (bp : ℤ)) (-1) 1 i j
  refine LinearEquiv.ofLinear f g ?_ ?_
  · apply LinearMap.ext
    intro x
    funext k
    by_cases hki : k = i
    · subst k
      simp [f, g, hij]
      linear_combination (hbez) * x i
    · by_cases hkj : k = j
      · subst k
        simp [f, g, hij]
        linear_combination (hbez) * x j
      · simp [f, g, hki, hkj]
  · apply LinearMap.ext
    intro x
    funext k
    by_cases hki : k = i
    · subst k
      simp [f, g, hij]
      linear_combination (hbez) * x i
    · by_cases hkj : k = j
      · subst k
        simp [f, g, hij]
        linear_combination (hbez) * x j
      · simp [f, g, hki, hkj]

/-- The two `2 × 2` matrices used by the refinement are unimodular. -/
private theorem pair_determinants (ap bp : ℕ) (u v : ℤ)
    (hbez : (ap : ℤ) * u + (bp : ℤ) * v = 1) :
    u * (ap : ℤ) - v * (-(bp : ℤ)) = 1 ∧
      1 * (u * (ap : ℤ)) - (-(v * (bp : ℤ))) * 1 = 1 := by
  constructor <;> linear_combination hbez

/-- The exact integral identity behind the `gcd,lcm` pair refinement. -/
private theorem pair_matrix_identity (g ap bp : ℕ) (u v : ℤ)
    (hbez : (ap : ℤ) * u + (bp : ℤ) * v = 1) :
    u * ((g * ap : ℕ) : ℤ) + v * ((g * bp : ℕ) : ℤ) = (g : ℤ) ∧
    (-(bp : ℤ)) * ((g * ap : ℕ) : ℤ) +
        (ap : ℤ) * ((g * bp : ℕ) : ℤ) = 0 ∧
    u * ((g * ap : ℕ) : ℤ) * (-(v * (bp : ℤ))) +
        v * ((g * bp : ℕ) : ℤ) * (u * (ap : ℤ)) = 0 ∧
    (-(bp : ℤ)) * ((g * ap : ℕ) : ℤ) * (-(v * (bp : ℤ))) +
        (ap : ℤ) * ((g * bp : ℕ) : ℤ) * (u * (ap : ℤ)) =
          ((g * ap * bp : ℕ) : ℤ) := by
  constructor
  · norm_num at hbez ⊢
    linear_combination (hbez) * g
  constructor
  · norm_num
    ring
  constructor
  · push_cast
    ring
  · push_cast
    linear_combination (hbez) * (g * ap * bp)

/-- Change a basis by applying a linear equivalence to its column
coordinates. -/
private def changeBasis {r : ℕ} {A : Type*} [AddCommGroup A] [Module ℤ A]
    (b : Module.Basis (Fin r) ℤ A) (e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) :
    Module.Basis (Fin r) ℤ A :=
  b.map (b.equivFun.trans (e.trans b.equivFun.symm))

@[simp]
private theorem equivFun_changeBasis {r : ℕ} {A : Type*}
    [AddCommGroup A] [Module ℤ A] (b : Module.Basis (Fin r) ℤ A)
    (e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (i : Fin r) :
    b.equivFun (changeBasis b e i) = e (Pi.single i 1) := by
  classical
  change b.equivFun (b.equivFun.symm (e (b.equivFun (b i)))) = _
  rw [b.equivFun.apply_symm_apply]
  congr 1
  funext k
  simp [Pi.single_apply, eq_comm]

/-- In old ambient coordinates, synthesis in a diagonal relation basis is
coordinatewise multiplication by the diagonal. -/
private theorem equivFun_relation_synthesis {r : ℕ} {N : Submodule ℤ M}
    (P : DiagonalPresentation r N) (x : Fin r → ℤ) :
    P.ambientBasis.equivFun
        ((P.relationBasis.equivFun.symm x : N) : M) =
      fun i ↦ (P.diagonal i : ℤ) * x i := by
  classical
  have hmodule : (inferInstance : Module ℤ M) = AddCommGroup.toIntModule M :=
    Subsingleton.elim _ _
  cases hmodule
  rw [Module.Basis.equivFun_symm_apply]
  change P.ambientBasis.equivFun
      ((N.subtype : N →ₗ[ℤ] M) (∑ i, x i • P.relationBasis i)) = _
  have hcoord (i : Fin r) :
      P.ambientBasis.equivFun (P.relationBasis i : M) =
        fun k ↦ if k = i then (P.diagonal i : ℤ) else 0 := by
    rw [P.relation_eq]
    funext k
    simp [Finsupp.single_apply, eq_comm]
  have hcoord_apply (i k : Fin r) :
      P.ambientBasis.repr (P.relationBasis i : M) k =
        if k = i then (P.diagonal i : ℤ) else 0 :=
    congrFun (hcoord i) k
  rw [map_sum, map_sum]
  simp only [map_smul]
  funext k
  simp [hcoord_apply, mul_comm]

/-- Replace two positive diagonal entries `a,b` by `gcd(a,b),lcm(a,b)`,
transporting both bases by the explicit unimodular changes from the proof. -/
private def refinePair {r : ℕ} {N : Submodule ℤ M}
    (P : DiagonalPresentation r N) (i j : Fin r) (hij : i ≠ j) :
    DiagonalPresentation r N := by
  let a := P.diagonal i
  let b := P.diagonal j
  let g := Nat.gcd a b
  let ap := a / g
  let bp := b / g
  let u := Nat.gcdA ap bp
  let v := Nat.gcdB ap bp
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (P.diagonal_pos i)
  have hga : g * ap = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * bp = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hgaZ : (a : ℤ) = (g : ℤ) * (ap : ℤ) := by exact_mod_cast hga.symm
  have hgbZ : (b : ℤ) = (g : ℤ) * (bp : ℤ) := by exact_mod_cast hgb.symm
  have hgaP : (P.diagonal i : ℤ) = (g : ℤ) * (ap : ℤ) := by
    simpa [a] using hgaZ
  have hgbP : (P.diagonal j : ℤ) = (g : ℤ) * (bp : ℤ) := by
    simpa [b] using hgbZ
  have hcop : Nat.gcd ap bp = 1 :=
    Nat.gcd_div_gcd_div_gcd_of_pos_left (P.diagonal_pos i)
  have hbez : (ap : ℤ) * u + (bp : ℤ) * v = 1 := by
    have he := Nat.gcd_eq_gcd_ab ap bp
    rw [hcop] at he
    simpa [u, v] using he.symm
  let U := uEquiv ap bp u v hbez i j hij
  let V := vEquiv ap bp u v hbez i j hij
  let newAmbient := changeBasis P.ambientBasis U.symm
  let newRelation := changeBasis P.relationBasis V
  let newDiagonal : Fin r → ℕ := fun k ↦
    if k = i then g else if k = j then g * ap * bp else P.diagonal k
  refine
    { ambientBasis := newAmbient
      relationBasis := newRelation
      diagonal := newDiagonal
      diagonal_pos := ?_
      relation_eq := ?_ }
  · intro k
    by_cases hki : k = i
    · simp [newDiagonal, hki, hgpos]
    · by_cases hkj : k = j
      · subst k
        have hap : 0 < ap := Nat.div_pos (Nat.gcd_le_left b (P.diagonal_pos i)) hgpos
        have hbp : 0 < bp := Nat.div_pos (Nat.gcd_le_right a (P.diagonal_pos j)) hgpos
        simp [newDiagonal, hij.symm, hgpos, hap, hbp]
      · simp [newDiagonal, hki, hkj, P.diagonal_pos k]
  · intro k
    apply P.ambientBasis.equivFun.injective
    rw [show (newRelation k : M) =
        ((newRelation k : N) : M) by rfl]
    rw [show newRelation k =
        P.relationBasis.equivFun.symm (V (Pi.single k 1)) by
      apply P.relationBasis.equivFun.injective
      rw [P.relationBasis.equivFun.apply_symm_apply]
      exact equivFun_changeBasis P.relationBasis V k]
    rw [equivFun_relation_synthesis P]
    rw [map_zsmul]
    rw [equivFun_changeBasis P.ambientBasis U.symm k]
    apply funext
    intro l
    by_cases hki : k = i
    · subst k
      by_cases hli : l = i
      · subst l
        simp [newDiagonal, U, V, uEquiv, vEquiv, hij, hij.symm, pairCoord, hgaP]
      · by_cases hlj : l = j
        · subst l
          simp [newDiagonal, U, V, uEquiv, vEquiv, hij, hij.symm, hgaP, hgbP,
            pairCoord]
        · simp [newDiagonal, U, V, uEquiv, vEquiv, hij, hli, hlj,
            pairCoord, Pi.single_apply]
    · by_cases hkj : k = j
      · subst k
        by_cases hli : l = i
        · subst l
          simp [newDiagonal, U, V, uEquiv, vEquiv, hij, hij.symm, pairCoord, hgaP]
          ring
        · by_cases hlj : l = j
          · subst l
            simp [newDiagonal, U, V, uEquiv, vEquiv, hij, hij.symm, pairCoord, hgbP]
            ring
          · simp [newDiagonal, U, V, uEquiv, vEquiv, hij, hli, hlj,
              pairCoord, Pi.single_apply]
      · by_cases hli : l = i
        · subst l
          simp [newDiagonal, U, V, uEquiv, vEquiv, hij, pairCoord, hki, hkj]
        · by_cases hlj : l = j
          · subst l
            simp [newDiagonal, U, V, uEquiv, vEquiv, hij, pairCoord, hki, hkj]
          · by_cases hlk : l = k
            · subst l
              simp [newDiagonal, U, V, uEquiv, vEquiv, hki, hkj, pairCoord]
            · simp [newDiagonal, U, V, uEquiv, vEquiv, hij, hki, hkj,
                hli, hlj, hlk, pairCoord, Pi.single_apply]

/-- Divisibility of adjacent entries implies divisibility of every earlier
entry into every later entry. -/
private theorem dvd_of_adjacent {r : ℕ} (d : Fin r → ℕ)
    (h : ∀ (i : Fin r) (hi : i.val + 1 < r),
      d i ∣ d ⟨i.val + 1, hi⟩)
    (i j : Fin r) (hij : i ≤ j) : d i ∣ d j := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hij
  have hjval : j.val = i.val + t := by omega
  have aux : ∀ t (j : Fin r), j.val = i.val + t → d i ∣ d j := by
    intro t
    induction t with
    | zero =>
        intro j hj
        have hji : j = i := by ext; omega
        subst j
        exact dvd_refl _
    | succ t ih =>
        intro j hj
        let k : Fin r := ⟨i.val + t, by omega⟩
        have hkj : k.val + 1 < r := by simp [k]; omega
        have ih' : d i ∣ d k := ih k (by simp [k])
        have hnext := h k hkj
        have heq : (⟨k.val + 1, hkj⟩ : Fin r) = j := by
          ext
          simp [k]
          omega
        simpa [heq] using dvd_trans ih' hnext
  exact aux t j hjval

/-- Every positive diagonal presentation can be normalized to invariant-factor
order.  The recursion follows the least adjacent failure and is justified by
lexicographic decrease of the entire diagonal vector. -/
private theorem exists_ordered {r : ℕ} {N : Submodule ℤ M}
    (P : DiagonalPresentation r N) :
    ∃ Q : DiagonalPresentation r N,
      ∀ i j, i ≤ j → Q.diagonal i ∣ Q.diagonal j := by
  classical
  let rel : (Fin r → ℕ) → (Fin r → ℕ) → Prop :=
    Pi.Lex (fun i j : Fin r ↦ i < j) (fun {_ : Fin r} (a b : ℕ) ↦ a < b)
  have hwf : WellFounded rel := by
    change WellFounded
      (Pi.Lex (fun i j : Fin r ↦ i < j) (fun {_ : Fin r} (a b : ℕ) ↦ a < b))
    exact Pi.Lex.wellFounded (fun i j : Fin r ↦ i < j)
      (fun _ ↦ Nat.lt_wfRel.wf)
  let motive : (Fin r → ℕ) → Prop := fun d ↦
    ∀ P : DiagonalPresentation r N, P.diagonal = d →
      ∃ Q : DiagonalPresentation r N,
        ∀ i j, i ≤ j → Q.diagonal i ∣ Q.diagonal j
  have hnormalize : ∀ d, motive d := fun d ↦ hwf.induction d (C := motive) fun d ih P hPd ↦ by
    subst d
    by_cases hadj : ∀ (i : Fin r) (hi : i.val + 1 < r),
        P.diagonal i ∣ P.diagonal ⟨i.val + 1, hi⟩
    · exact ⟨P, dvd_of_adjacent P.diagonal hadj⟩
    · push_neg at hadj
      let Bad : Fin r → Prop := fun i ↦
        ∃ hi : i.val + 1 < r,
          ¬ P.diagonal i ∣ P.diagonal ⟨i.val + 1, hi⟩
      let badSet : Finset (Fin r) := Finset.univ.filter Bad
      have hbadSet : badSet.Nonempty := by
        obtain ⟨i, hi, hbad⟩ := hadj
        refine ⟨i, ?_⟩
        simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi, hbad⟩
      let i : Fin r := badSet.min' hbadSet
      have hiBad : Bad i := by
        have himem := badSet.min'_mem hbadSet
        exact (Finset.mem_filter.mp himem).2
      obtain ⟨hi, hbad⟩ := hiBad
      let j : Fin r := ⟨i.val + 1, hi⟩
      have hij : i ≠ j := by
        intro heq
        have := congrArg Fin.val heq
        simp [j] at this
      let Q := refinePair P i j hij
      have hijlt : i < j := by
        change i.val < i.val + 1
        omega
      have hgcdlt : Nat.gcd (P.diagonal i) (P.diagonal j) < P.diagonal i := by
        apply lt_of_le_of_ne (Nat.gcd_le_left _ (P.diagonal_pos i))
        intro heq
        apply hbad
        have hdvd : P.diagonal i ∣ P.diagonal j :=
          Nat.gcd_eq_left_iff_dvd.mp heq
        simpa [j] using hdvd
      have hrel : rel Q.diagonal P.diagonal := by
        refine ⟨i, ?_, ?_⟩
        · intro k hki
          have hki' : k ≠ i := ne_of_lt hki
          have hkj' : k ≠ j := by
            intro h
            subst k
            exact (not_lt_of_ge hijlt.le) hki
          simp [Q, refinePair, hki', hkj']
        · simpa [Q, refinePair] using hgcdlt
      exact ih Q.diagonal hrel Q rfl
  exact hnormalize P.diagonal P rfl

/-- The positive square Smith presentation supplied by Mathlib, before the
invariant factors are ordered. -/
private def positiveDiagonalOfFiniteQuotient {r : ℕ}
    (b : Module.Basis (Fin r) ℤ M) (N : Submodule ℤ M)
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (hfinite : Finite (M ⧸ N)) : DiagonalPresentation r N := by
  have hmodule : (inferInstance : Module ℤ M) = AddCommGroup.toIntModule M :=
    Subsingleton.elim _ _
  cases hmodule
  letI : Finite (M ⧸ N) := hfinite
  let hrank : Module.finrank ℤ N = Module.finrank ℤ M :=
    (Submodule.finiteQuotient_iff N).mp inferInstance
  let bM := Submodule.smithNormalFormTopBasis b hrank
  let bN := Submodule.smithNormalFormBotBasis b hrank
  let a := Submodule.smithNormalFormCoeffs b hrank
  have ha : ∀ i, a i ≠ 0 :=
    Submodule.smithNormalFormCoeffs_ne_zero b hrank
  let units : Fin r → ℤˣ := fun i ↦ signUnit (a i)
  let bNpos : Module.Basis (Fin r) ℤ N := bN.unitsSMul units
  refine
    { ambientBasis := bM
      relationBasis := bNpos
      diagonal := fun i ↦ (a i).natAbs
      diagonal_pos := fun i ↦ Int.natAbs_pos.mpr (ha i)
      relation_eq := ?_ }
  intro i
  change ((bN.unitsSMul units i : N) : M) =
    ((a i).natAbs : ℤ) • bM i
  rw [Module.Basis.unitsSMul_apply]
  change (units i : ℤ) • (bN i : M) = ((a i).natAbs : ℤ) • bM i
  rw [Submodule.smithNormalFormBotBasis_def b hrank, smul_smul]
  change ((units i : ℤ) * a i) • bM i = ((a i).natAbs : ℤ) • bM i
  rw [show (units i : ℤ) = (signUnit (a i) : ℤ) by rfl,
    coe_signUnit_mul]

/-- A finite quotient of a finite free integral module admits Smith bases in
invariant-factor order. -/
def ofFiniteQuotient (N : Submodule ℤ M)
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (hfinite : Finite (M ⧸ N)) : InvariantFactorPresentation N := by
  let ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  let P := positiveDiagonalOfFiniteQuotient b N hfinite
  let Q := Classical.choose (exists_ordered P)
  have hQ := Classical.choose_spec (exists_ordered P)
  exact
    { rank := r
      ambientBasis := Q.ambientBasis
      relationBasis := Q.relationBasis
      diagonal := Q.diagonal
      diagonal_pos := Q.diagonal_pos
      relation_eq := Q.relation_eq
      diagonal_dvd := hQ }

/-- The concrete normalization gate exercises the transported bases, not just
the arithmetic identity: a diagonal pair `6, 10` is replaced by `2, 30`. -/
example {N : Submodule ℤ M} (P : DiagonalPresentation 2 N)
    (h0 : P.diagonal (0 : Fin 2) = 6)
    (h1 : P.diagonal (1 : Fin 2) = 10) :
    (refinePair P (0 : Fin 2) (1 : Fin 2) (by decide)).diagonal 0 = 2 ∧
      (refinePair P (0 : Fin 2) (1 : Fin 2) (by decide)).diagonal 1 = 30 := by
  simp [refinePair, h0, h1]

end InvariantFactorPresentation

end

end LieRings

assert_no_sorry LieRings.InvariantFactorPresentation.ofFiniteQuotient
