import LieRings.FinitePlateau.Presentation
import LieRings.DimensionSubring.Centrality

/-!
# The exceptional element in the finite-plateau presentation

This file verifies the elementary identities in the middle of the manuscript's
finite-plateau construction.  In particular, the exceptional element is both
`32 u₃` and the two-factor enveloping expression `c₁c₃-c₂²`.  The
latter expression places it in the required high augmentation power.
-/

namespace LieRings.FinitePlateau

noncomputable section

open scoped BigOperators

private theorem bracket_mem_derived (N : ℕ) (x y : L N) :
    ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ (L N) 1 := by
  change ⁅x, y⁆ ∈ ⁅(⊤ : LieIdeal ℤ (L N)), (⊤ : LieIdeal ℤ (L N))⁆
  exact LieSubmodule.lie_mem_lie (by simp) (by simp)

private theorem c_mem_derived (N : ℕ) (i : Fin 3) :
    c N i ∈ LieAlgebra.derivedSeries ℤ (L N) 1 := by
  change quotientMap N (cSource N i) ∈ _
  rw [cSource, LieHom.map_lie]
  exact bracket_mem_derived N _ _

private theorem t_mem_derived (N : ℕ) (hN : 1 ≤ N) :
    t N ∈ LieAlgebra.derivedSeries ℤ (L N) 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  change quotientMap (k + 1)
      (rightBracketPow (x4Source (k + 1)) (x5Source (k + 1)) (k + 1)) ∈ _
  rw [rightBracketPow_succ, LieHom.map_lie]
  exact bracket_mem_derived (k + 1) _ _

private theorem t_bracket_c_eq_zero (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) :
    ⁅t N, c N i⁆ = 0 :=
  (isMetabelian N).bracket_eq_zero (t_mem_derived N hN) (c_mem_derived N i)

@[simp] private theorem t_lie_smallGenerator (N : ℕ) (i : Fin 3) :
    ⁅t N, smallGenerator N i⁆ = c N i := by
  change ⁅quotientMap N (tSource N),
      quotientMap N (smallSourceGenerator N i)⁆ =
    quotientMap N ⁅tSource N, smallSourceGenerator N i⁆
  exact (LieHom.map_lie (quotientMap N) _ _).symm

/-! ## Torsion relations for the three `c`-terms -/

theorem four_c1_eq_zero (N : ℕ) (hN : 1 ≤ N) : (4 : ℤ) • c1 N = 0 := by
  have hrel : (4 : ℤ) • x1 N + (2 : ℤ) • c3 N + c2 N = 0 := by
    simpa only [r1Source, map_add, map_zsmul, map_x1Source, map_cSource]
      using r1_eq_zero N
  have hr := congrArg (fun z : L N ↦ ⁅t N, z⁆) hrel
  have hc2 := t_bracket_c_eq_zero N hN 1
  have hc3 := t_bracket_c_eq_zero N hN 2
  have htx : ⁅t N, x1 N⁆ = c1 N := by
    simpa using t_lie_smallGenerator N 0
  change ⁅t N, (4 : ℤ) • x1 N + (2 : ℤ) • c3 N + c2 N⁆ =
    ⁅t N, 0⁆ at hr
  rw [lie_add, lie_add, lie_zsmul, lie_zsmul, lie_zero,
    htx, hc2, hc3, smul_zero] at hr
  simpa using hr

theorem sixteen_c2_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    (16 : ℤ) • c2 N = 0 := by
  have hrel : (16 : ℤ) • x2 N + (4 : ℤ) • c3 N - c1 N = 0 := by
    simpa only [r2Source, map_add, map_sub, map_zsmul, map_x2Source, map_cSource]
      using r2_eq_zero N
  have hr := congrArg (fun z : L N ↦ ⁅t N, z⁆) hrel
  have hc1 := t_bracket_c_eq_zero N hN 0
  have hc3 := t_bracket_c_eq_zero N hN 2
  have htx : ⁅t N, x2 N⁆ = c2 N := by
    simpa using t_lie_smallGenerator N 1
  change ⁅t N, (16 : ℤ) • x2 N + (4 : ℤ) • c3 N - c1 N⁆ =
    ⁅t N, 0⁆ at hr
  rw [lie_sub, lie_add, lie_zsmul, lie_zsmul, lie_zero,
    htx, hc1, hc3, smul_zero, add_zero, sub_zero] at hr
  exact hr

theorem sixtyFour_c3_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    (64 : ℤ) • c3 N = 0 := by
  have hrel : (64 : ℤ) • x3 N - (4 : ℤ) • c2 N -
      (2 : ℤ) • c1 N = 0 := by
    simpa only [r3Source, map_sub, map_zsmul, map_x3Source, map_cSource]
      using r3_eq_zero N
  have hr := congrArg (fun z : L N ↦ ⁅t N, z⁆) hrel
  have hc1 := t_bracket_c_eq_zero N hN 0
  have hc2 := t_bracket_c_eq_zero N hN 1
  have htx : ⁅t N, x3 N⁆ = c3 N := by
    simpa using t_lie_smallGenerator N 2
  change ⁅t N, (64 : ℤ) • x3 N - (4 : ℤ) • c2 N -
      (2 : ℤ) • c1 N⁆ = ⁅t N, 0⁆ at hr
  rw [lie_sub, lie_sub, lie_zsmul, lie_zsmul, lie_zsmul, lie_zero,
    htx, hc1, hc2, smul_zero, sub_zero] at hr
  simpa using hr

/-! ## The additive order-two identity -/

private theorem thirtyTwo_b12_eq_neg_two_u1 (N : ℕ) (hN : 1 ≤ N) :
    (32 : ℤ) • b12 N = -((2 : ℤ) • u1 N) := by
  have h := congrArg (fun z : L N ↦ (-2 : ℤ) • z)
    (neg_sixteen_b12_sub_u1_eq_zero N hN)
  have hz : (32 : ℤ) • b12 N + (2 : ℤ) • u1 N = 0 := by
    simpa [smul_sub, smul_smul] using h
  exact eq_neg_of_add_eq_zero_left hz

private theorem sixtyFour_b13_eq_neg_two_u1 (N : ℕ) (hN : 1 ≤ N) :
    (64 : ℤ) • b13 N = -((2 : ℤ) • u1 N) := by
  have h := congrArg (fun z : L N ↦ (-1 : ℤ) • z)
    (neg_sixtyFour_b13_sub_two_u1_eq_zero N hN)
  have hz : (64 : ℤ) • b13 N + (2 : ℤ) • u1 N = 0 := by
    simpa [smul_sub, smul_smul] using h
  exact eq_neg_of_add_eq_zero_left hz

private theorem oneTwentyEight_b23_eq_neg_eight_u2 (N : ℕ) (hN : 1 ≤ N) :
    (128 : ℤ) • b23 N = -((8 : ℤ) • u2 N) := by
  have h := congrArg (fun z : L N ↦ (-2 : ℤ) • z)
    (neg_sixtyFour_b23_sub_four_u2_eq_zero N hN)
  have hz : (128 : ℤ) • b23 N + (8 : ℤ) • u2 N = 0 := by
    simpa [smul_sub, smul_smul] using h
  exact eq_neg_of_add_eq_zero_left hz

/-- The manuscript identity `a = 32u₃`. -/
theorem a_eq_thirtyTwo_u3 (N : ℕ) (hN : 1 ≤ N) :
    a N = (32 : ℤ) • u3 N := by
  rw [a, aSource, map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
    map_b12Source, map_b13Source, map_b23Source,
    thirtyTwo_b12_eq_neg_two_u1 N hN,
    sixtyFour_b13_eq_neg_two_u1 N hN,
    oneTwentyEight_b23_eq_neg_eight_u2 N hN,
    u1_eq_sixteen_u3, u2_eq_four_u3]
  have h64 := sixtyFour_u3_eq_zero N
  calc
    -((2 : ℤ) • ((16 : ℤ) • u3 N)) +
          -((2 : ℤ) • ((16 : ℤ) • u3 N)) +
          -((8 : ℤ) • ((4 : ℤ) • u3 N)) =
        (-96 : ℤ) • u3 N := by module
    _ = (32 : ℤ) • u3 N := by
      calc
        (-96 : ℤ) • u3 N =
            (32 : ℤ) • u3 N - (2 : ℤ) • ((64 : ℤ) • u3 N) := by module
        _ = (32 : ℤ) • u3 N := by rw [h64, smul_zero, sub_zero]

/-- The exceptional element is annihilated by two.  Its nonvanishing, and
hence its exact additive order, is proved by the top-coordinate detector. -/
theorem two_a_eq_zero (N : ℕ) (hN : 1 ≤ N) : (2 : ℤ) • a N = 0 := by
  rw [a_eq_thirtyTwo_u3 N hN, smul_smul]
  norm_num

/-! ## Lower-central weight of the `cᵢ` -/

private theorem map_rightBracketPow {A B : Type*} [LieRing A] [LieRing B]
    (f : LieHom ℤ A B) (x y : A) (n : ℕ) :
    f (rightBracketPow x y n) = rightBracketPow (f x) (f y) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rightBracketPow_succ, LieHom.map_lie, ih]

private theorem rightBracketPow_mem_lowerCentralSeries
    {A : Type*} [LieRing A] (x y : A) (n : ℕ) :
    rightBracketPow x y n ∈ lowerCentralSeries ℤ A n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rightBracketPow_succ]
      change ⁅rightBracketPow x y n, y⁆ ∈
        LieModule.lowerCentralSeries ℤ A A (Nat.succ n)
      rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
      exact LieSubmodule.lie_mem_lie ih (by simp)

theorem t_mem_lowerCentralSeries (N : ℕ) :
    t N ∈ lowerCentralSeries ℤ (L N) N := by
  have h := rightBracketPow_mem_lowerCentralSeries (x4 N) (x5 N) N
  simpa only [t, tSource, map_rightBracketPow, map_x4Source, map_x5Source] using h

/-- Each `cᵢ` has manuscript lower-central weight `N+2`, hence belongs to
the zero-based term `γ_(N+2) = lowerCentralSeries (N+1)`. -/
theorem c_mem_lowerCentralSeries (N : ℕ) (i : Fin 3) :
    c N i ∈ lowerCentralSeries ℤ (L N) (N + 1) := by
  rw [← t_lie_smallGenerator N i]
  change ⁅t N, smallGenerator N i⁆ ∈
    LieModule.lowerCentralSeries ℤ (L N) (L N) (Nat.succ N)
  rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
  exact LieSubmodule.lie_mem_lie (t_mem_lowerCentralSeries N) (by simp)

theorem c_mem_dimensionSubring (N : ℕ) (i : Fin 3) :
    c N i ∈ dimensionSubring ℤ (L N) (N + 2) := by
  simpa only [show N + 1 + 1 = N + 2 by omega] using
    lowerCentralSeries_le_dimensionSubring ℤ (L N) (N + 1)
      (c_mem_lowerCentralSeries N i)

/-! ## The three coefficient identities -/

private theorem shifted_r1 (N : ℕ) :
    (4 : ℤ) • x1 N = -((2 : ℤ) • c3 N + c2 N) := by
  have h : (4 : ℤ) • x1 N + (2 : ℤ) • c3 N + c2 N = 0 := by
    simpa only [r1Source, map_add, map_zsmul, map_x1Source, map_cSource]
      using r1_eq_zero N
  calc
    (4 : ℤ) • x1 N =
        ((4 : ℤ) • x1 N + (2 : ℤ) • c3 N + c2 N) -
          ((2 : ℤ) • c3 N + c2 N) := by abel
    _ = -((2 : ℤ) • c3 N + c2 N) := by rw [h, zero_sub]

private theorem shifted_r2 (N : ℕ) :
    (16 : ℤ) • x2 N = -((4 : ℤ) • c3 N - c1 N) := by
  have h : (16 : ℤ) • x2 N + (4 : ℤ) • c3 N - c1 N = 0 := by
    simpa only [r2Source, map_add, map_sub, map_zsmul, map_x2Source, map_cSource]
      using r2_eq_zero N
  calc
    (16 : ℤ) • x2 N =
        ((16 : ℤ) • x2 N + (4 : ℤ) • c3 N - c1 N) -
          ((4 : ℤ) • c3 N - c1 N) := by abel
    _ = -((4 : ℤ) • c3 N - c1 N) := by rw [h, zero_sub]

private theorem shifted_r3 (N : ℕ) :
    (64 : ℤ) • x3 N = (4 : ℤ) • c2 N + (2 : ℤ) • c1 N := by
  have h : (64 : ℤ) • x3 N - (4 : ℤ) • c2 N -
      (2 : ℤ) • c1 N = 0 := by
    simpa only [r3Source, map_sub, map_zsmul, map_x3Source, map_cSource]
      using r3_eq_zero N
  calc
    (64 : ℤ) • x3 N =
        ((64 : ℤ) • x3 N - (4 : ℤ) • c2 N - (2 : ℤ) • c1 N) +
          ((4 : ℤ) • c2 N + (2 : ℤ) • c1 N) := by abel
    _ = (4 : ℤ) • c2 N + (2 : ℤ) • c1 N := by rw [h, zero_add]

private theorem w1_eq (N : ℕ) :
    (32 : ℤ) • x2 N + (64 : ℤ) • x3 N =
      (4 : ℤ) • (c1 N + c2 N - (2 : ℤ) • c3 N) := by
  have h2 := shifted_r2 N
  have h3 := shifted_r3 N
  calc
    (32 : ℤ) • x2 N + (64 : ℤ) • x3 N =
        (2 : ℤ) • ((16 : ℤ) • x2 N) + (64 : ℤ) • x3 N := by module
    _ = (2 : ℤ) • (-((4 : ℤ) • c3 N - c1 N)) +
        ((4 : ℤ) • c2 N + (2 : ℤ) • c1 N) := by rw [h2, h3]
    _ = (4 : ℤ) • (c1 N + c2 N - (2 : ℤ) • c3 N) := by module

private theorem w2_eq (N : ℕ) (hN : 1 ≤ N) :
    -(32 : ℤ) • x1 N + (128 : ℤ) • x3 N =
      (16 : ℤ) • (c2 N + c3 N) := by
  have h1 := shifted_r1 N
  have h3 := shifted_r3 N
  have hc1 := four_c1_eq_zero N hN
  calc
    -(32 : ℤ) • x1 N + (128 : ℤ) • x3 N =
        (-8 : ℤ) • ((4 : ℤ) • x1 N) +
          (2 : ℤ) • ((64 : ℤ) • x3 N) := by module
    _ = (-8 : ℤ) • (-((2 : ℤ) • c3 N + c2 N)) +
          (2 : ℤ) • ((4 : ℤ) • c2 N + (2 : ℤ) • c1 N) := by rw [h1, h3]
    _ = (16 : ℤ) • (c2 N + c3 N) + (4 : ℤ) • c1 N := by module
    _ = (16 : ℤ) • (c2 N + c3 N) := by rw [hc1, add_zero]

private theorem w3_eq (N : ℕ) (hN : 1 ≤ N) :
    -(64 : ℤ) • x1 N - (128 : ℤ) • x2 N =
      (64 : ℤ) • c3 N := by
  have h1 := shifted_r1 N
  have h2 := shifted_r2 N
  have hc1 := four_c1_eq_zero N hN
  have hc2 := sixteen_c2_eq_zero N hN
  calc
    -(64 : ℤ) • x1 N - (128 : ℤ) • x2 N =
        (-16 : ℤ) • ((4 : ℤ) • x1 N) -
          (8 : ℤ) • ((16 : ℤ) • x2 N) := by module
    _ = (-16 : ℤ) • (-((2 : ℤ) • c3 N + c2 N)) -
          (8 : ℤ) • (-((4 : ℤ) • c3 N - c1 N)) := by rw [h1, h2]
    _ = (64 : ℤ) • c3 N + (16 : ℤ) • c2 N -
          (2 : ℤ) • ((4 : ℤ) • c1 N) := by module
    _ = (64 : ℤ) • c3 N := by rw [hc1, hc2, smul_zero, sub_zero, add_zero]

private theorem iota_c_comm (N : ℕ) (i j : Fin 3) :
    UniversalEnvelopingAlgebra.ι ℤ (c N i) *
        UniversalEnvelopingAlgebra.ι ℤ (c N j) =
      UniversalEnvelopingAlgebra.ι ℤ (c N j) *
        UniversalEnvelopingAlgebra.ι ℤ (c N i) := by
  have hzero : ⁅c N i, c N j⁆ = 0 :=
    (isMetabelian N).bracket_eq_zero
      (c_mem_derived N i) (c_mem_derived N j)
  have hmap := LieHom.map_lie
    (UniversalEnvelopingAlgebra.ι ℤ : LieHom ℤ (L N) (UEA ℤ (L N)))
    (c N i) (c N j)
  rw [hzero, map_zero, LieRing.of_associative_ring_bracket] at hmap
  exact sub_eq_zero.mp hmap.symm

/-- The exact enveloping-algebra factorization from the manuscript. -/
theorem iota_a_eq_c1_mul_c3_sub_c2_sq (N : ℕ) (hN : 1 ≤ N) :
    UniversalEnvelopingAlgebra.ι ℤ (a N) =
      UniversalEnvelopingAlgebra.ι ℤ (c1 N) *
          UniversalEnvelopingAlgebra.ι ℤ (c3 N) -
        UniversalEnvelopingAlgebra.ι ℤ (c2 N) *
          UniversalEnvelopingAlgebra.ι ℤ (c2 N) := by
  let ιL : LieHom ℤ (L N) (UEA ℤ (L N)) := UniversalEnvelopingAlgebra.ι ℤ
  have ha : a N = (32 : ℤ) • b12 N + (64 : ℤ) • b13 N +
      (128 : ℤ) • b23 N := by
    simp only [a, aSource, map_add, map_zsmul, map_b12Source,
      map_b13Source, map_b23Source]
  rw [ha, ← lie_x1_x2, ← lie_x1_x3, ← lie_x2_x3]
  simp only [map_add, map_zsmul, LieHom.map_lie,
    LieRing.of_associative_ring_bracket]
  have hw1 := congrArg ιL.toLinearMap (w1_eq N)
  have hw2 := congrArg ιL.toLinearMap (w2_eq N hN)
  have hw3 := congrArg ιL.toLinearMap (w3_eq N hN)
  simp only [map_add, map_sub, map_zsmul, LinearMap.coe_toAddHom] at hw1 hw2 hw3
  change (32 : ℤ) • ιL (x2 N) + (64 : ℤ) • ιL (x3 N) =
    (4 : ℤ) • (ιL (c1 N) + ιL (c2 N) - (2 : ℤ) • ιL (c3 N)) at hw1
  change -(32 : ℤ) • ιL (x1 N) + (128 : ℤ) • ιL (x3 N) =
    (16 : ℤ) • (ιL (c2 N) + ιL (c3 N)) at hw2
  change -(64 : ℤ) • ιL (x1 N) - (128 : ℤ) • ιL (x2 N) =
    (64 : ℤ) • ιL (c3 N) at hw3
  have hs1 := congrArg ιL.toLinearMap (shifted_r1 N)
  have hs2 := congrArg ιL.toLinearMap (shifted_r2 N)
  have hs3 := congrArg ιL.toLinearMap (shifted_r3 N)
  simp only [map_add, map_sub, map_neg, map_zsmul, LinearMap.coe_toAddHom] at hs1 hs2 hs3
  change (4 : ℤ) • ιL (x1 N) =
    -((2 : ℤ) • ιL (c3 N) + ιL (c2 N)) at hs1
  change (16 : ℤ) • ιL (x2 N) =
    -((4 : ℤ) • ιL (c3 N) - ιL (c1 N)) at hs2
  change (64 : ℤ) • ιL (x3 N) =
    (4 : ℤ) • ιL (c2 N) + (2 : ℤ) • ιL (c1 N) at hs3
  have hgroup :
      (32 : ℤ) • (ιL (x1 N) * ιL (x2 N) - ιL (x2 N) * ιL (x1 N)) +
          (64 : ℤ) • (ιL (x1 N) * ιL (x3 N) - ιL (x3 N) * ιL (x1 N)) +
          (128 : ℤ) • (ιL (x2 N) * ιL (x3 N) - ιL (x3 N) * ιL (x2 N)) =
        ιL (x1 N) * ιL ((32 : ℤ) • x2 N + (64 : ℤ) • x3 N) +
          ιL (x2 N) * ιL (-(32 : ℤ) • x1 N + (128 : ℤ) • x3 N) +
          ιL (x3 N) * ιL (-(64 : ℤ) • x1 N - (128 : ℤ) • x2 N) := by
    simp only [map_add, map_sub, map_neg, map_zsmul]
    noncomm_ring
  change
    (32 : ℤ) • (ιL (x1 N) * ιL (x2 N) - ιL (x2 N) * ιL (x1 N)) +
          (64 : ℤ) • (ιL (x1 N) * ιL (x3 N) - ιL (x3 N) * ιL (x1 N)) +
          (128 : ℤ) • (ιL (x2 N) * ιL (x3 N) - ιL (x3 N) * ιL (x2 N)) =
      ιL (c1 N) * ιL (c3 N) - ιL (c2 N) * ιL (c2 N)
  rw [hgroup]
  simp only [map_add, map_sub, map_neg, map_zsmul]
  rw [hw1, hw2, hw3]
  have hscalar :
      ιL (x1 N) * ((4 : ℤ) •
          (ιL (c1 N) + ιL (c2 N) - (2 : ℤ) • ιL (c3 N))) +
        ιL (x2 N) * ((16 : ℤ) • (ιL (c2 N) + ιL (c3 N))) +
        ιL (x3 N) * ((64 : ℤ) • ιL (c3 N)) =
      ((4 : ℤ) • ιL (x1 N)) *
          (ιL (c1 N) + ιL (c2 N) - (2 : ℤ) • ιL (c3 N)) +
        ((16 : ℤ) • ιL (x2 N)) * (ιL (c2 N) + ιL (c3 N)) +
        ((64 : ℤ) • ιL (x3 N)) * ιL (c3 N) := by
    noncomm_ring
  rw [hscalar, hs1, hs2, hs3]
  have h31 := iota_c_comm N 2 0
  have h32 := iota_c_comm N 2 1
  have h21 := iota_c_comm N 1 0
  change ιL (c3 N) * ιL (c1 N) = ιL (c1 N) * ιL (c3 N) at h31
  change ιL (c3 N) * ιL (c2 N) = ιL (c2 N) * ιL (c3 N) at h32
  change ιL (c2 N) * ιL (c1 N) = ιL (c1 N) * ιL (c2 N) at h21
  calc
    -(2 • ιL (c3 N) + ιL (c2 N)) *
          (ιL (c1 N) + ιL (c2 N) - 2 • ιL (c3 N)) +
        -(4 • ιL (c3 N) - ιL (c1 N)) *
          (ιL (c2 N) + ιL (c3 N)) +
        (4 • ιL (c2 N) + 2 • ιL (c1 N)) * ιL (c3 N) =
      (ιL (c1 N) * ιL (c3 N) - ιL (c2 N) * ιL (c2 N)) +
        2 • (ιL (c1 N) * ιL (c3 N) - ιL (c3 N) * ιL (c1 N)) +
        6 • (ιL (c2 N) * ιL (c3 N) - ιL (c3 N) * ιL (c2 N)) +
        (ιL (c1 N) * ιL (c2 N) - ιL (c2 N) * ιL (c1 N)) := by
          noncomm_ring
    _ = ιL (c1 N) * ιL (c3 N) - ιL (c2 N) * ιL (c2 N) := by
      rw [h31, h32, h21]
      simp

/-- The manuscript height calculation: `a ∈ δ_(2N+4)(L_N)`. -/
theorem a_mem_dimensionSubring_twoN_add_four (N : ℕ) (hN : 1 ≤ N) :
    a N ∈ dimensionSubring ℤ (L N) (2 * N + 4) := by
  rw [mem_dimensionSubring, iota_a_eq_c1_mul_c3_sub_c2_sq N hN]
  have hc1 := (mem_dimensionSubring ℤ (L N)).mp (c_mem_dimensionSubring N 0)
  have hc2 := (mem_dimensionSubring ℤ (L N)).mp (c_mem_dimensionSubring N 1)
  have hc3 := (mem_dimensionSubring ℤ (L N)).mp (c_mem_dimensionSubring N 2)
  have h13 : UniversalEnvelopingAlgebra.ι ℤ (c1 N) *
      UniversalEnvelopingAlgebra.ι ℤ (c3 N) ∈
      UEA.augmentationIdeal ℤ (L N) ^ (2 * N + 4) := by
    rw [show 2 * N + 4 = (N + 2) + (N + 2) by omega,
      Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul hc1 hc3
  have h22 : UniversalEnvelopingAlgebra.ι ℤ (c2 N) *
      UniversalEnvelopingAlgebra.ι ℤ (c2 N) ∈
      UEA.augmentationIdeal ℤ (L N) ^ (2 * N + 4) := by
    rw [show 2 * N + 4 = (N + 2) + (N + 2) by omega,
      Ideal.IsTwoSided.pow_add]
    exact Ideal.mul_mem_mul hc2 hc2
  exact (UEA.augmentationIdeal ℤ (L N) ^ (2 * N + 4)).sub_mem h13 h22

/-- The whole exceptional cyclic ideal lies in the last nonzero term claimed
in the manuscript. -/
theorem exceptionalIdeal_le_dimensionSubring_twoN_add_four
    (N : ℕ) (hN : 1 ≤ N) :
    exceptionalIdeal N ≤ dimensionSubring ℤ (L N) (2 * N + 4) := by
  rw [exceptionalIdeal, LieSubmodule.lieSpan_le]
  simpa only [Set.singleton_subset_iff] using
    a_mem_dimensionSubring_twoN_add_four N hN

/-- The exceptional element is central.  This follows from dimension
centrality and the nilpotency cutoff, rather than from a separate bracket
collection. -/
theorem a_mem_center (N : ℕ) (hN : 1 ≤ N) :
    a N ∈ LieAlgebra.center ℤ (L N) := by
  rw [LieModule.mem_maxTrivSubmodule]
  intro x
  have ha := a_mem_dimensionSubring_twoN_add_four N hN
  have hbracket : ⁅a N, x⁆ ∈
      ⁅dimensionSubring ℤ (L N) (2 * N + 4),
        (⊤ : LieIdeal ℤ (L N))⁆ :=
    LieSubmodule.lie_mem_lie ha (by simp)
  rw [dimensionSubring_bracket_eq_lowerCentralSeries_of_pos
      ℤ (L N) (by omega : 1 ≤ 2 * N + 4)] at hbracket
  have hcut : lowerCentralSeries ℤ (L N) (2 * N + 4) = ⊥ := by
    apply le_antisymm
    · exact (LieModule.antitone_lowerCentralSeries ℤ (L N) (L N)
          (by omega : N + 3 ≤ 2 * N + 4)).trans
        (by rw [lowerCentralSeries_cutoff_eq_bot N])
    · exact bot_le
  rw [hcut] at hbracket
  have hazero : ⁅a N, x⁆ = 0 := by simpa using hbracket
  rw [← lie_skew, hazero, neg_zero]

theorem exceptionalIdeal_le_center (N : ℕ) (hN : 1 ≤ N) :
    exceptionalIdeal N ≤ LieAlgebra.center ℤ (L N) := by
  rw [exceptionalIdeal, LieSubmodule.lieSpan_le]
  simpa only [Set.singleton_subset_iff] using a_mem_center N hN

end

end LieRings.FinitePlateau
