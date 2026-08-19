import LieRings.DimensionSubring.MetabelianVanishing.TerminalCertificateBridge

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open TensorProduct
open LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L
local instance : Module.Free ℤ (PZero L) := Module.Free.of_basis (pZeroBasis L)
local instance : Module.Finite ℤ (PZero L) := Module.Finite.of_basis (pZeroBasis L)
local instance : Finite (V L n) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)
local instance : Module.Finite ℤ (POne n L) :=
  Module.Finite.of_fg (IsNoetherian.noetherian _)
local instance : Module.Free ℤ (POne n L) :=
  Module.free_of_finite_type_torsion_free'

def testCycleTensor :
    Koszul.One (terminalSourcePresentation n L data hn) 1 →ₗ[ℤ]
      (A L n ⊗[ℤ] A L n) :=
  TensorProduct.map (terminalSourcePresentation n L data hn).d
    (SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)).toLinearMap

@[simp] theorem testCycleTensor_tmul
    (d : D n L data n (by omega))
    (s : Sym[ℤ] (Fin 1) (A L n)) :
    testCycleTensor n L data hn (d ⊗ₜ[ℤ] s) =
      (terminalSourcePresentation n L data hn).d d ⊗ₜ[ℤ]
        (SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)) s := by
  rfl

theorem testSymTensor_eq_dOne
    (x : Koszul.One (terminalSourcePresentation n L data hn) 1) :
    SymmetricPower.tensorToSymTwo (R := ℤ)
        (testCycleTensor n L data hn x) =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1 x := by
  let lhs := (SymmetricPower.tensorToSymTwo (R := ℤ) (M := A L n)).comp
    (testCycleTensor n L data hn)
  have hmaps : lhs = Koszul.dOne
      (terminalSourcePresentation n L data hn) 1 := by
    apply TensorProduct.ext'
    intro d s
    change SymmetricPower.tensorToSymTwo (R := ℤ)
        (testCycleTensor n L data hn (d ⊗ₜ[ℤ] s)) = _
    rw [testCycleTensor_tmul]
    let e := SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)
    have hs : SymmetricPower.degreeOne (R := ℤ) (e s) = s := by
      apply e.injective
      rw [SymmetricPower.degreeOneLinearEquiv_degreeOne]
    have hprod :
      SymmetricPower.tensorToSymTwo (R := ℤ)
          ((terminalSourcePresentation n L data hn).d d ⊗ₜ[ℤ]
            (SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)) s) =
        SymmetricPower.insert ℤ (A L n) 1
          ((terminalSourcePresentation n L data hn).d d) s := by
      calc
        SymmetricPower.tensorToSymTwo (R := ℤ)
            ((terminalSourcePresentation n L data hn).d d ⊗ₜ[ℤ]
              (SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)) s) =
          SymmetricPower.insert ℤ (A L n) 1
          ((terminalSourcePresentation n L data hn).d d)
          (SymmetricPower.degreeOne (R := ℤ) (e s)) := by
            rw [SymmetricPower.tensorToSymTwo_tmul,
              SymmetricPower.degreeOne_apply,
              SymmetricPower.insert_tprod]
            dsimp only [e]
            congr 1
        _ = SymmetricPower.insert ℤ (A L n) 1
            ((terminalSourcePresentation n L data hn).d d) s := by rw [hs]
    have hd := Koszul.dOne_tmul
      (terminalSourcePresentation n L data hn) 1 d s
    exact hprod.trans hd.symm
  exact LinearMap.congr_fun hmaps x

theorem testCycleExterior_exists
    (c : Koszul.cyclesOne (terminalSourcePresentation n L data hn) 1) :
    ∃ y : ⋀[ℤ]^2 (A L n),
      SymmetricPower.exteriorTwoToTensor (R := ℤ) y =
        testCycleTensor n L data hn c.1 := by
  have hker : testCycleTensor n L data hn c.1 ∈
      LinearMap.ker (SymmetricPower.tensorToSymTwo
        (R := ℤ) (M := A L n)) := by
    rw [LinearMap.mem_ker, testSymTensor_eq_dOne]
    exact c.property
  have hrange : testCycleTensor n L data hn c.1 ∈
      LinearMap.range (SymmetricPower.exteriorTwoToTensor
        (R := ℤ) (M := A L n)) := by
    let κ := (i : Fin n) × FreeMetabelian.Free.PieceIndex
      (Fin (Nat.card L)) i.val
    let b : Module.Basis (Fin (Fintype.card κ)) ℤ (A L n) :=
      (prefixBasis L n).reindex (Fintype.equivFin κ)
    rw [SymmetricPower.exteriorTwoToTensor_range_eq_ker b]
    exact hker
  exact (LinearMap.mem_range).mp hrange

noncomputable def testCycleExterior
    (c : Koszul.cyclesOne (terminalSourcePresentation n L data hn) 1) :
    ⋀[ℤ]^2 (A L n) :=
  Classical.choose (testCycleExterior_exists n L data hn c)

theorem testCycleExterior_spec
    (c : Koszul.cyclesOne (terminalSourcePresentation n L data hn) 1) :
    SymmetricPower.exteriorTwoToTensor (R := ℤ)
        (testCycleExterior n L data hn c) =
      testCycleTensor n L data hn c.1 := by
  exact Classical.choose_spec (testCycleExterior_exists n L data hn c)

private def testLiftProductBilinear
    (f : A L n →ₗ[ℤ] FreeModel n L) :
    A L n →ₗ[ℤ] A L n →ₗ[ℤ] UEA ℤ (FreeModel n L) where
  toFun x :=
    { toFun := fun y ↦ UniversalEnvelopingAlgebra.ι ℤ (f x) *
          UniversalEnvelopingAlgebra.ι ℤ (f y)
      map_add' := by intro y z; rw [map_add, map_add, mul_add]
      map_smul' := by
        intro z y
        rw [map_zsmul, map_zsmul, mul_smul_comm]
        simp only [RingHom.id_apply] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change UniversalEnvelopingAlgebra.ι ℤ (f (x + y)) *
        UniversalEnvelopingAlgebra.ι ℤ (f z) = _
    rw [map_add, map_add, add_mul]
    rfl
  map_smul' z x := by
    apply LinearMap.ext
    intro y
    change UniversalEnvelopingAlgebra.ι ℤ (f (z • x)) *
        UniversalEnvelopingAlgebra.ι ℤ (f y) = _
    rw [map_zsmul, map_zsmul, smul_mul_assoc]
    simp only [RingHom.id_apply]
    rfl

def testLiftProductWord
    (f : A L n →ₗ[ℤ] FreeModel n L) :
    (A L n ⊗[ℤ] A L n) →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
  (TensorProduct.lift (testLiftProductBilinear n L f)).toAddMonoidHom.toIntLinearMap

@[simp] theorem testLiftProductWord_tmul
    (f : A L n →ₗ[ℤ] FreeModel n L) (x y : A L n) :
    testLiftProductWord n L f (x ⊗ₜ[ℤ] y) =
      UniversalEnvelopingAlgebra.ι ℤ (f x) *
        UniversalEnvelopingAlgebra.ι ℤ (f y) := by
  rfl

def testLiftProductPrimitive
    (f : A L n →ₗ[ℤ] FreeModel n L) :
    (A L n ⊗[ℤ] A L n) →ₗ[ℤ] FreeModel n L :=
  (pbwPrimitive n L data hn).comp (testLiftProductWord n L f)

theorem testLiftProductPrimitive_antisym
    (f : A L n →ₗ[ℤ] FreeModel n L) (x y : A L n) :
    testLiftProductPrimitive n L data hn f
        (x ⊗ₜ[ℤ] y - y ⊗ₜ[ℤ] x) = ⁅f x, f y⁆ := by
  rw [testLiftProductPrimitive, map_sub, LinearMap.comp_apply]
  change pbwPrimitive n L data hn
        (testLiftProductWord n L f (x ⊗ₜ[ℤ] y)) -
      pbwPrimitive n L data hn
        (testLiftProductWord n L f (y ⊗ₜ[ℤ] x)) = _
  rw [testLiftProductWord_tmul, testLiftProductWord_tmul]
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
    (FreeModel n L) (f x) (f y)
  rw [hswap, map_add, pbwPrimitive_iota]
  abel

theorem testBracketTopLeft
    (top : FreeMetabelian.Piece (Generator L) n)
    (x : FreeModel n L) :
    ⁅FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
      n (by omega) top, x⁆ = 0 := by
  rw [← FreeMetabelian.Free.sum_incl_project x, lie_sum]
  apply Finset.sum_eq_zero
  intro i hi
  funext k
  exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
    n i.val (by omega) i.isLt top
      (FreeMetabelian.Free.weightProject i.val i.isLt x) k (by
        intro h
        have hk := k.isLt
        omega)

theorem testBracketTopRight
    (x : FreeModel n L)
    (top : FreeMetabelian.Piece (Generator L) n) :
    ⁅x, FreeMetabelian.Free.weightIncl (X := Generator L) (c := n + 1)
      n (by omega) top⁆ = 0 := by
  rw [← lie_skew, testBracketTopLeft n L top x, neg_zero]

theorem testBracketRealizationDifference_mem
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (x y : A L n) :
    ⁅terminalSourceGeneratorLift n L x,
        terminalSourceGeneratorLift n L y⁆ -
      ⁅terminalBlockGeneratorLift n L data hn g x,
        terminalBlockGeneratorLift n L data hn g y⁆ ∈ Relations n L data := by
  let S := terminalSourceGeneratorLift n L
  let B := terminalBlockGeneratorLift n L data hn g
  let deltaX := terminalGeneratorDefectRelation n L data hn g x
  let deltaY := terminalGeneratorDefectRelation n L data hn g y
  let topX := terminalGeneratorTopCorrection n L data hn g x
  let topY := terminalGeneratorTopCorrection n L data hn g y
  have hx : S x = B x + (deltaX : FreeModel n L) -
      FreeMetabelian.Free.weightIncl n (by omega) topX :=
    (terminalGeneratorRealizationDefect n L data hn g x).source_eq
  have hy : S y = B y + (deltaY : FreeModel n L) -
      FreeMetabelian.Free.weightIncl n (by omega) topY :=
    (terminalGeneratorRealizationDefect n L data hn g y).source_eq
  have hval : ⁅S x, S y⁆ - ⁅B x, B y⁆ =
      ⁅B x, (deltaY : FreeModel n L)⁆ +
        ⁅(deltaX : FreeModel n L), B y⁆ +
        ⁅(deltaX : FreeModel n L), (deltaY : FreeModel n L)⁆ := by
    rw [hx, hy]
    simp only [sub_lie, add_lie, lie_sub, lie_add]
    rw [testBracketTopLeft n L topX (B y),
      testBracketTopLeft n L topX (deltaY : FreeModel n L),
      testBracketTopLeft n L topX
        (FreeMetabelian.Free.weightIncl n (by omega) topY),
      testBracketTopRight n L (B x) topY,
      testBracketTopRight n L (deltaX : FreeModel n L) topY]
    module
  rw [hval]
  change evaluation n L data
    (⁅B x, (deltaY : FreeModel n L)⁆ +
      ⁅(deltaX : FreeModel n L), B y⁆ +
      ⁅(deltaX : FreeModel n L), (deltaY : FreeModel n L)⁆) = 0
  rw [map_add, map_add, LieHom.map_lie, LieHom.map_lie, LieHom.map_lie]
  have hdx : evaluation n L data (deltaX : FreeModel n L) = 0 :=
    deltaX.property
  have hdy : evaluation n L data (deltaY : FreeModel n L) = 0 :=
    deltaY.property
  rw [hdx, hdy]
  simp

def testBracketRealizationRelation
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (x y : A L n) : Relations n L data :=
  ⟨⁅terminalSourceGeneratorLift n L x,
      terminalSourceGeneratorLift n L y⁆ -
    ⁅terminalBlockGeneratorLift n L data hn g x,
      terminalBlockGeneratorLift n L data hn g y⁆,
    testBracketRealizationDifference_mem n L data hn g x y⟩

@[simp] theorem testBracketRealizationRelation_val
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (x y : A L n) :
    (testBracketRealizationRelation n L data hn g x y : FreeModel n L) =
      ⁅terminalSourceGeneratorLift n L x,
        terminalSourceGeneratorLift n L y⁆ -
      ⁅terminalBlockGeneratorLift n L data hn g x,
        terminalBlockGeneratorLift n L data hn g y⁆ := rfl

theorem testBracketRealizationRelation_add_left
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (x y z : A L n) :
    testBracketRealizationRelation n L data hn g (x + y) z =
      testBracketRealizationRelation n L data hn g x z +
        testBracketRealizationRelation n L data hn g y z := by
  apply Subtype.ext
  change
    (⁅terminalSourceGeneratorLift n L (x + y),
        terminalSourceGeneratorLift n L z⁆ -
      ⁅terminalBlockGeneratorLift n L data hn g (x + y),
        terminalBlockGeneratorLift n L data hn g z⁆) =
      (⁅terminalSourceGeneratorLift n L x,
          terminalSourceGeneratorLift n L z⁆ -
        ⁅terminalBlockGeneratorLift n L data hn g x,
          terminalBlockGeneratorLift n L data hn g z⁆) +
      (⁅terminalSourceGeneratorLift n L y,
          terminalSourceGeneratorLift n L z⁆ -
        ⁅terminalBlockGeneratorLift n L data hn g y,
          terminalBlockGeneratorLift n L data hn g z⁆)
  rw [map_add, map_add, add_lie, add_lie]
  abel

theorem testBracketRealizationRelation_add_right
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (x y z : A L n) :
    testBracketRealizationRelation n L data hn g x (y + z) =
      testBracketRealizationRelation n L data hn g x y +
        testBracketRealizationRelation n L data hn g x z := by
  apply Subtype.ext
  change
    (⁅terminalSourceGeneratorLift n L x,
        terminalSourceGeneratorLift n L (y + z)⁆ -
      ⁅terminalBlockGeneratorLift n L data hn g x,
        terminalBlockGeneratorLift n L data hn g (y + z)⁆) =
      (⁅terminalSourceGeneratorLift n L x,
          terminalSourceGeneratorLift n L y⁆ -
        ⁅terminalBlockGeneratorLift n L data hn g x,
          terminalBlockGeneratorLift n L data hn g y⁆) +
      (⁅terminalSourceGeneratorLift n L x,
          terminalSourceGeneratorLift n L z⁆ -
        ⁅terminalBlockGeneratorLift n L data hn g x,
          terminalBlockGeneratorLift n L data hn g z⁆)
  rw [map_add, map_add, lie_add, lie_add]
  abel

theorem testBracketRealizationRelation_zsmul_left
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (z : ℤ) (x y : A L n) :
    testBracketRealizationRelation n L data hn g (z • x) y =
      z • testBracketRealizationRelation n L data hn g x y := by
  apply Subtype.ext
  change
    (⁅terminalSourceGeneratorLift n L (z • x),
        terminalSourceGeneratorLift n L y⁆ -
      ⁅terminalBlockGeneratorLift n L data hn g (z • x),
        terminalBlockGeneratorLift n L data hn g y⁆) =
      z • (⁅terminalSourceGeneratorLift n L x,
          terminalSourceGeneratorLift n L y⁆ -
        ⁅terminalBlockGeneratorLift n L data hn g x,
          terminalBlockGeneratorLift n L data hn g y⁆)
  rw [map_zsmul, map_zsmul, zsmul_lie, zsmul_lie, smul_sub]

theorem testBracketRealizationRelation_zsmul_right
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (z : ℤ) (x y : A L n) :
    testBracketRealizationRelation n L data hn g x (z • y) =
      z • testBracketRealizationRelation n L data hn g x y := by
  apply Subtype.ext
  change
    (⁅terminalSourceGeneratorLift n L x,
        terminalSourceGeneratorLift n L (z • y)⁆ -
      ⁅terminalBlockGeneratorLift n L data hn g x,
        terminalBlockGeneratorLift n L data hn g (z • y)⁆) =
      z • (⁅terminalSourceGeneratorLift n L x,
          terminalSourceGeneratorLift n L y⁆ -
        ⁅terminalBlockGeneratorLift n L data hn g x,
          terminalBlockGeneratorLift n L data hn g y⁆)
  rw [map_zsmul, map_zsmul, lie_zsmul, lie_zsmul, smul_sub]

private def testBracketRealizationMultilinear
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) :
    MultilinearMap ℤ (fun _ : Fin 2 ↦ A L n) (Relations n L data) :=
  MultilinearMap.mk'
    (fun a ↦ testBracketRealizationRelation n L data hn g (a 0) (a 1))
    (by
      intro a i x y
      fin_cases i
      · simpa [Function.update] using
          testBracketRealizationRelation_add_left n L data hn g x y (a 1)
      · simpa [Function.update] using
          testBracketRealizationRelation_add_right n L data hn g (a 0) x y)
    (by
      intro a i z x
      fin_cases i
      · simpa [Function.update] using
          testBracketRealizationRelation_zsmul_left
            n L data hn g z x (a 1)
      · simpa [Function.update] using
          testBracketRealizationRelation_zsmul_right
            n L data hn g z (a 0) x)

private def testBracketRealizationAlternating
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) :
    A L n [⋀^Fin 2]→ₗ[ℤ] Relations n L data :=
  AlternatingMap.mk (testBracketRealizationMultilinear n L data hn g) (by
    intro a i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · apply Subtype.ext
      change ⁅terminalSourceGeneratorLift n L (a 0),
          terminalSourceGeneratorLift n L (a 1)⁆ -
        ⁅terminalBlockGeneratorLift n L data hn g (a 0),
          terminalBlockGeneratorLift n L data hn g (a 1)⁆ = 0
      have h : a 0 = a 1 := by simpa using hij
      rw [h, lie_self, lie_self, sub_self]
    · apply Subtype.ext
      change ⁅terminalSourceGeneratorLift n L (a 0),
          terminalSourceGeneratorLift n L (a 1)⁆ -
        ⁅terminalBlockGeneratorLift n L data hn g (a 0),
          terminalBlockGeneratorLift n L data hn g (a 1)⁆ = 0
      have h : a 1 = a 0 := by simpa using hij
      rw [h, lie_self, lie_self, sub_self]
    · exact (hne rfl).elim)

def testBracketRealizationExterior
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id) :
    (⋀[ℤ]^2 (A L n)) →ₗ[ℤ] Relations n L data :=
  exteriorPower.alternatingMapLinearEquiv
    (testBracketRealizationAlternating n L data hn g)

@[simp] theorem testBracketRealizationExterior_iMulti
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (a : Fin 2 → A L n) :
    testBracketRealizationExterior n L data hn g
        (exteriorPower.ιMulti ℤ 2 a) =
      testBracketRealizationRelation n L data hn g (a 0) (a 1) := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem testSourceBlockPrimitive_exterior
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (y : ⋀[ℤ]^2 (A L n)) :
    testLiftProductPrimitive n L data hn (terminalSourceGeneratorLift n L)
        (SymmetricPower.exteriorTwoToTensor (R := ℤ) y) =
      testLiftProductPrimitive n L data hn
          (terminalBlockGeneratorLift n L data hn g)
          (SymmetricPower.exteriorTwoToTensor (R := ℤ) y) +
        (testBracketRealizationExterior n L data hn g y : FreeModel n L) := by
  let source := testLiftProductPrimitive n L data hn
    (terminalSourceGeneratorLift n L)
  let block := testLiftProductPrimitive n L data hn
    (terminalBlockGeneratorLift n L data hn g)
  let relation := testBracketRealizationExterior n L data hn g
  have hmaps : (source - block).comp
        (SymmetricPower.exteriorTwoToTensor (R := ℤ) (M := A L n)) =
      (Relations n L data).subtype.comp relation := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span ℤ 2 (A L n))
    rintro _ ⟨a, rfl⟩
    change source (SymmetricPower.exteriorTwoToTensor (R := ℤ)
          (exteriorPower.ιMulti ℤ 2 a)) -
        block (SymmetricPower.exteriorTwoToTensor (R := ℤ)
          (exteriorPower.ιMulti ℤ 2 a)) =
      (relation (exteriorPower.ιMulti ℤ 2 a) : FreeModel n L)
    rw [SymmetricPower.exteriorTwoToTensor_ιMulti,
      testLiftProductPrimitive_antisym,
      testLiftProductPrimitive_antisym,
      testBracketRealizationExterior_iMulti,
      testBracketRealizationRelation_val]
  have hy := LinearMap.congr_fun hmaps y
  change source (SymmetricPower.exteriorTwoToTensor (R := ℤ) y) =
    block (SymmetricPower.exteriorTwoToTensor (R := ℤ) y) +
      (relation y : FreeModel n L)
  change source _ - block _ = (relation y : FreeModel n L) at hy
  calc
    source _ = (relation y : FreeModel n L) + block _ :=
      (sub_eq_iff_eq_add.mp hy)
    _ = block _ + (relation y : FreeModel n L) := add_comm _ _

theorem testSourcePlacedPrimitive_eq_product
    (x : Koszul.One (terminalSourcePresentation n L data hn) 1) :
    terminalSourcePrimitive n L data hn x =
      testLiftProductPrimitive n L data hn
        (terminalSourceGeneratorLift n L)
        (testCycleTensor n L data hn x) := by
  let source := terminalSourcePrimitive n L data hn
  let product := (testLiftProductPrimitive n L data hn
    (terminalSourceGeneratorLift n L)).comp
      (testCycleTensor n L data hn)
  have hmaps : source = product := by
    apply TensorProduct.ext'
    intro d s
    let relationLift : FreeModel n L :=
      terminalFullLift n L data hn d
    let displayed : FreeModel n L :=
      terminalSourceGeneratorLift n L
        ((terminalSourcePresentation n L data hn).d d)
    let factor : FreeModel n L := terminalSourceSymOneLift n L s
    have hfactor : factor = terminalSourceGeneratorLift n L
        ((SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)) s) := rfl
    have hprefixLift : FreeMetabelian.Free.projectPrefix n (by omega)
        relationLift = d.1 := by
      have h := congrArg Subtype.val
        (terminalFullLift_prefix n L data hn d)
      exact h
    have hprefixDisplayed : FreeMetabelian.Free.projectPrefix n (by omega)
        displayed = d.1 := by
      change FreeMetabelian.Free.projectPrefix n (by omega)
          (FreeMetabelian.Free.prefixIncl n (by omega) d.1) = d.1
      exact LinearMap.congr_fun
        (FreeMetabelian.Free.projectPrefix_prefixIncl
          (X := Generator L) n (by omega)) d.1
    let top : FreeMetabelian.Piece (Generator L) n :=
      FreeMetabelian.Free.weightProject n (by omega)
        (relationLift - displayed)
    have htop : relationLift - displayed =
        FreeMetabelian.Free.weightIncl n (by omega) top := by
      exact sub_eq_weightIncl_top_of_projectPrefix_eq n L
        relationLift displayed (hprefixLift.trans hprefixDisplayed.symm)
    have hlift : relationLift = displayed +
        FreeMetabelian.Free.weightIncl n (by omega) top := by
      calc
        relationLift = (relationLift - displayed) + displayed := by abel
        _ = FreeMetabelian.Free.weightIncl n (by omega) top + displayed := by
          rw [htop]
        _ = _ := add_comm _ _
    change pbwPrimitive n L data hn
        (terminalSourcePlacedWord n L data hn (d ⊗ₜ[ℤ] s)) =
      pbwPrimitive n L data hn
        (testLiftProductWord n L (terminalSourceGeneratorLift n L)
          (testCycleTensor n L data hn (d ⊗ₜ[ℤ] s)))
    rw [terminalSourcePlacedWord_tmul, testCycleTensor_tmul]
    change pbwPrimitive n L data hn
        (UniversalEnvelopingAlgebra.ι ℤ relationLift *
          UniversalEnvelopingAlgebra.ι ℤ factor) =
      pbwPrimitive n L data hn
        (UniversalEnvelopingAlgebra.ι ℤ displayed *
          UniversalEnvelopingAlgebra.ι ℤ
            (terminalSourceGeneratorLift n L
              ((SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)) s)))
    rw [← hfactor]
    apply LieRings.PBW.canonicalMap_injective_of_freeModulePBW
      ℤ (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis
      (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
        (adaptedWeightedBasis n L data hn).basis)
    rw [← factorProj_one_eq_iota_pbwPrimitive n L data hn,
      ← factorProj_one_eq_iota_pbwPrimitive n L data hn]
    rw [hlift, map_add, add_mul, map_add,
      factorProj_one_iota_weightIncl_top_mul_eq_zero
        n L data hn top factor, add_zero]
  exact LinearMap.congr_fun hmaps x

theorem testMappedBlockRawPrimitive_eq_product
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (x : Koszul.One (terminalSourcePresentation n L data hn) 1) :
    pbwPrimitive n L data hn
        (terminalBlockRawPlacedWord n L data hn
          (Koszul.PresentationHomology.oneMap
            (terminalSourcePresentation n L data hn)
            (rPresentation n L data (by omega)) g 1 x)) =
      testLiftProductPrimitive n L data hn
        (terminalBlockGeneratorLift n L data hn g)
        (testCycleTensor n L data hn x) := by
  let raw := (pbwPrimitive n L data hn).comp
    ((terminalBlockRawPlacedWord n L data hn).comp
      (Koszul.PresentationHomology.oneMap
        (terminalSourcePresentation n L data hn)
        (rPresentation n L data (by omega)) g 1))
  let product := (testLiftProductPrimitive n L data hn
    (terminalBlockGeneratorLift n L data hn g)).comp
      (testCycleTensor n L data hn)
  have hmaps : raw = product := by
    apply TensorProduct.ext'
    intro d s
    let relationLift : FreeModel n L :=
      quadraticBlockFullRelationLift n L data hn (g.relMap d)
    let displayed : FreeModel n L :=
      terminalBlockGeneratorLift n L data hn g
        ((terminalSourcePresentation n L data hn).d d)
    let factor : FreeModel n L := terminalBlockSymOneLift n L data hn
      (SymmetricPower.map (R := ℤ) (ι := Fin 1) g.genMap s)
    have hcommutes : rDifferential n L data (by omega) (g.relMap d) =
        g.genMap ((terminalSourcePresentation n L data hn).d d) := by
      exact LinearMap.congr_fun g.commutes d
    let top : FreeMetabelian.Piece (Generator L) n :=
      quadraticBlockTopTail n L data hn (g.relMap d)
    have hlift : relationLift = displayed +
        FreeMetabelian.Free.weightIncl n (by omega) top := by
      change
        (quadraticBlockFullRelationLift n L data hn (g.relMap d) :
          FreeModel n L) =
        terminalBlockGeneratorLift n L data hn g
            ((terminalSourcePresentation n L data hn).d d) +
          FreeMetabelian.Free.weightIncl n (by omega)
            (quadraticBlockTopTail n L data hn (g.relMap d))
      rw [quadraticBlockFullRelationLift_eq]
      change quadraticBlockIncl n L hn
          (rDifferential n L data (by omega) (g.relMap d)) +
          FreeMetabelian.Free.weightIncl n (by omega) top =
        quadraticBlockIncl n L hn
          (g.genMap ((terminalSourcePresentation n L data hn).d d)) +
          FreeMetabelian.Free.weightIncl n (by omega) top
      rw [hcommutes]
    have hfactor : factor = terminalBlockGeneratorLift n L data hn g
        ((SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)) s) := by
      let e := SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)
      have hs : SymmetricPower.degreeOne (R := ℤ) (e s) = s := by
        apply e.injective
        rw [SymmetricPower.degreeOneLinearEquiv_degreeOne]
      calc
        factor = terminalBlockSymOneLift n L data hn
            (SymmetricPower.map (R := ℤ) (ι := Fin 1) g.genMap
              (SymmetricPower.degreeOne (R := ℤ) (e s))) := by
          exact congrArg (terminalBlockSymOneLift n L data hn)
            (congrArg
              (SymmetricPower.map (R := ℤ) (ι := Fin 1) g.genMap)
              hs.symm)
        _ = terminalBlockSymOneLift n L data hn
            (SymmetricPower.degreeOne (R := ℤ) (g.genMap (e s))) := by
          rw [SymmetricPower.map_degreeOne]
          rfl
        _ = quadraticBlockIncl n L hn (g.genMap (e s)) := by
          change quadraticBlockIncl n L hn
            ((SymmetricPower.degreeOneLinearEquiv
              ((pSmith n L).ambientBasis.prod
                (qSmith n L data (by omega)).ambientBasis))
              (SymmetricPower.degreeOne (R := ℤ) (g.genMap (e s)))) = _
          rw [SymmetricPower.degreeOneLinearEquiv_degreeOne]
        _ = terminalBlockGeneratorLift n L data hn g (e s) := rfl
    change pbwPrimitive n L data hn
        (terminalBlockRawPlacedWord n L data hn
          (Koszul.PresentationHomology.oneMap
            (terminalSourcePresentation n L data hn)
            (rPresentation n L data (by omega)) g 1 (d ⊗ₜ[ℤ] s))) =
      pbwPrimitive n L data hn
        (testLiftProductWord n L
          (terminalBlockGeneratorLift n L data hn g)
          (testCycleTensor n L data hn (d ⊗ₜ[ℤ] s)))
    rw [Koszul.PresentationHomology.oneMap_tmul,
      terminalBlockRawPlacedWord_tmul, testCycleTensor_tmul]
    change pbwPrimitive n L data hn
        (UniversalEnvelopingAlgebra.ι ℤ relationLift *
          UniversalEnvelopingAlgebra.ι ℤ factor) =
      pbwPrimitive n L data hn
        (UniversalEnvelopingAlgebra.ι ℤ displayed *
          UniversalEnvelopingAlgebra.ι ℤ
            (terminalBlockGeneratorLift n L data hn g
              ((SymmetricPower.degreeOneLinearEquiv (prefixBasis L n)) s)))
    rw [← hfactor]
    apply LieRings.PBW.canonicalMap_injective_of_freeModulePBW
      ℤ (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis
      (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
        (adaptedWeightedBasis n L data hn).basis)
    rw [← factorProj_one_eq_iota_pbwPrimitive n L data hn,
      ← factorProj_one_eq_iota_pbwPrimitive n L data hn]
    rw [hlift, map_add, add_mul, map_add,
      factorProj_one_iota_weightIncl_top_mul_eq_zero
        n L data hn top factor, add_zero]
  exact LinearMap.congr_fun hmaps x

theorem testQuadraticBlockChain_basisExpansion
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    c.1 =
      (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inl i) (Sum.inl j) •
          quadraticBlockOneBasis n L data hn (Sum.inl i, Sum.inl j)) +
      (∑ i : Fin (pSmith n L).rank,
        ∑ a : Fin (qSmith n L data (by omega)).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inl i) (Sum.inr a) •
          quadraticBlockOneBasis n L data hn (Sum.inl i, Sum.inr a)) +
      (∑ a : Fin (qSmith n L data (by omega)).rank,
        ∑ i : Fin (pSmith n L).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inl i) •
          quadraticBlockOneBasis n L data hn (Sum.inr a, Sum.inl i)) +
      (∑ a : Fin (qSmith n L data (by omega)).rank,
        ∑ b : Fin (qSmith n L data (by omega)).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inr b) •
          quadraticBlockOneBasis n L data hn (Sum.inr a, Sum.inr b)) := by
  classical
  let B := quadraticBlockOneBasis n L data hn
  let coeff := B.repr c.1
  calc
    c.1 = ∑ ij, coeff ij • B ij := (B.sum_repr c.1).symm
    _ = ∑ i, ∑ j, coeff (i, j) • B (i, j) := by
      rw [Fintype.sum_prod_type]
    _ = _ := by
      simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
      dsimp only [coeff, B, quadraticBlockCoefficient]
      abel

theorem testTerminalBlockRawPlacedWord_decomposition
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    terminalBlockRawPlacedWord n L data hn c.1 =
      (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inl i) (Sum.inl j) •
          (UniversalEnvelopingAlgebra.ι ℤ
              (quadraticRho n L data hn i : FreeModel n L) *
            UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn j))) +
      (∑ i : Fin (pSmith n L).rank,
        ∑ a : Fin (qSmith n L data (by omega)).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inl i) (Sum.inr a) •
          quadraticPQPlacedRow n L data hn i a) +
      (∑ a : Fin (qSmith n L data (by omega)).rank,
        ∑ i : Fin (pSmith n L).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inl i) •
          (UniversalEnvelopingAlgebra.ι ℤ
              (quadraticSigma n L data hn a : FreeModel n L) *
            UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn i))) +
      (∑ a : Fin (qSmith n L data (by omega)).rank,
        ∑ b : Fin (qSmith n L data (by omega)).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inr a) (Sum.inr b) •
          quadraticQQPlacedRow n L data hn a b) := by
  rw [testQuadraticBlockChain_basisExpansion n L data hn c,
    map_add, map_add, map_add]
  simp only [map_sum, map_zsmul, terminalBlockRawPlacedWord_PP,
    terminalBlockRawPlacedWord_PQ, terminalBlockRawPlacedWord_QP,
    terminalBlockRawPlacedWord_QQ]

def testPBlockOneIncl :
    Koszul.One (pPresentation n L) 1 →ₗ[ℤ]
      Koszul.One (rPresentation n L data (by omega)) 1 :=
  TensorProduct.map
    (LinearMap.inl ℤ (POne n L) (QOne n L data (by omega)))
    (SymmetricPower.map (R := ℤ) (ι := Fin 1)
      (LinearMap.inl ℤ (PZero L) (QZero n L)))

def testPBlockRawWord :
    Koszul.One (pPresentation n L) 1 →ₗ[ℤ]
      UEA ℤ (FreeModel n L) :=
  (terminalBlockRawPlacedWord n L data hn).comp
    (testPBlockOneIncl n L data hn)

@[simp] theorem testPBlockRawWord_oneBasis
    (i j : Fin (pSmith n L).rank) :
    testPBlockRawWord n L data hn
        (Koszul.QuadraticUCT.oneBasis
          (pAugmentation n L) (pAugmentation_surjective n L)
          (pSmith n L) (i, j)) =
      UniversalEnvelopingAlgebra.ι ℤ
          (quadraticRho n L data hn i : FreeModel n L) *
        UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn j) := by
  have hincl : testPBlockOneIncl n L data hn
      (Koszul.QuadraticUCT.oneBasis
        (pAugmentation n L) (pAugmentation_surjective n L)
        (pSmith n L) (i, j)) =
      quadraticBlockOneBasis n L data hn (Sum.inl i, Sum.inl j) := by
    rw [Koszul.QuadraticUCT.oneBasis_apply]
    change
      TensorProduct.map
          (LinearMap.inl ℤ (POne n L) (QOne n L data (by omega)))
          (SymmetricPower.map (R := ℤ) (ι := Fin 1)
            (LinearMap.inl ℤ (PZero L) (QZero n L)))
          ((pSmith n L).relationBasis i ⊗ₜ[ℤ]
            SymmetricPower.degreeOne (R := ℤ)
              ((pSmith n L).ambientBasis j)) = _
    rw [TensorProduct.map_tmul, SymmetricPower.map_degreeOne]
    change
      ((pSmith n L).relationBasis i, 0) ⊗ₜ[ℤ]
          SymmetricPower.degreeOne (R := ℤ)
            ((pSmith n L).ambientBasis j, 0) = _
    let B := (pSmith n L).ambientBasis.prod
      (qSmith n L data (by omega)).ambientBasis
    have hsym : quadraticBlockSymOneBasis n L data hn (Sum.inl j) =
        SymmetricPower.degreeOne (R := ℤ)
          ((pSmith n L).ambientBasis j, 0) := by
      apply (SymmetricPower.degreeOneLinearEquiv B).injective
      change (SymmetricPower.degreeOneLinearEquiv B)
          ((SymmetricPower.degreeOneLinearEquiv B).symm (B (Sum.inl j))) =
        (SymmetricPower.degreeOneLinearEquiv B)
          (SymmetricPower.degreeOne (R := ℤ)
            ((pSmith n L).ambientBasis j, 0))
      rw [LinearEquiv.apply_symm_apply,
        SymmetricPower.degreeOneLinearEquiv_degreeOne]
      rw [Module.Basis.prod_apply]
      rfl
    change _ = (quadraticBlockRelationBasis n L data hn).tensorProduct
      (quadraticBlockSymOneBasis n L data hn) (Sum.inl i, Sum.inl j)
    rw [Module.Basis.tensorProduct_apply']
    rw [hsym]
    simp [quadraticBlockRelationBasis]
  rw [testPBlockRawWord, LinearMap.comp_apply, hincl,
    terminalBlockRawPlacedWord_PP]

theorem testQuadraticBlockSymOneBasis_eq_degreeOne
    (a : Sum (Fin (pSmith n L).rank)
      (Fin (qSmith n L data (by omega)).rank)) :
    quadraticBlockSymOneBasis n L data hn a =
      SymmetricPower.degreeOne (R := ℤ)
        (((pSmith n L).ambientBasis.prod
          (qSmith n L data (by omega)).ambientBasis) a) := by
  let B := (pSmith n L).ambientBasis.prod
    (qSmith n L data (by omega)).ambientBasis
  apply (SymmetricPower.degreeOneLinearEquiv B).injective
  change (SymmetricPower.degreeOneLinearEquiv B)
      ((SymmetricPower.degreeOneLinearEquiv B).symm (B a)) =
    (SymmetricPower.degreeOneLinearEquiv B)
      (SymmetricPower.degreeOne (R := ℤ) (B a))
  rw [LinearEquiv.apply_symm_apply,
    SymmetricPower.degreeOneLinearEquiv_degreeOne]

theorem testRToPOneMap_blockBasis
    (a b : Sum (Fin (pSmith n L).rank)
      (Fin (qSmith n L data (by omega)).rank)) :
    Koszul.PresentationHomology.oneMap
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1
        (quadraticBlockOneBasis n L data hn (a, b)) =
      (quadraticBlockRelationBasis n L data hn a).1 ⊗ₜ[ℤ]
        SymmetricPower.degreeOne (R := ℤ)
          ((((pSmith n L).ambientBasis.prod
            (qSmith n L data (by omega)).ambientBasis) b).1) := by
  have hbasis : quadraticBlockOneBasis n L data hn (a, b) =
      quadraticBlockRelationBasis n L data hn a ⊗ₜ[ℤ]
        quadraticBlockSymOneBasis n L data hn b := by
    change ((quadraticBlockRelationBasis n L data hn).tensorProduct
      (quadraticBlockSymOneBasis n L data hn)) (a, b) = _
    exact Module.Basis.tensorProduct_apply' _ _ (a, b)
  rw [hbasis]
  calc
    _ = (rToP n L data (by omega)).relMap
          (quadraticBlockRelationBasis n L data hn a) ⊗ₜ[ℤ]
        SymmetricPower.map (R := ℤ) (ι := Fin 1)
          (rToP n L data (by omega)).genMap
          (quadraticBlockSymOneBasis n L data hn b) :=
      Koszul.PresentationHomology.oneMap_tmul
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1 _ _
    _ = _ := by
      rw [testQuadraticBlockSymOneBasis_eq_degreeOne]
      apply congrArg₂ (fun x y ↦ x ⊗ₜ[ℤ] y)
      · rfl
      · exact SymmetricPower.map_degreeOne
          (rToP n L data (by omega)).genMap _

@[simp] theorem testRToPOneMap_blockBasis_PP
    (i j : Fin (pSmith n L).rank) :
    Koszul.PresentationHomology.oneMap
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1
        (quadraticBlockOneBasis n L data hn (Sum.inl i, Sum.inl j)) =
      Koszul.QuadraticUCT.oneBasis
        (pAugmentation n L) (pAugmentation_surjective n L)
        (pSmith n L) (i, j) := by
  rw [testRToPOneMap_blockBasis,
    Koszul.QuadraticUCT.oneBasis_apply]
  congr 1 <;>
    simp [quadraticBlockRelationBasis, Module.Basis.prod_apply]

@[simp] theorem testRToPOneMap_blockBasis_PQ
    (i : Fin (pSmith n L).rank)
    (a : Fin (qSmith n L data (by omega)).rank) :
    Koszul.PresentationHomology.oneMap
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1
        (quadraticBlockOneBasis n L data hn (Sum.inl i, Sum.inr a)) = 0 := by
  rw [testRToPOneMap_blockBasis]
  have hz :
      ((((pSmith n L).ambientBasis.prod
        (qSmith n L data (by omega)).ambientBasis) (Sum.inr a)).1) = 0 := by
    simp [Module.Basis.prod_apply]
  rw [hz, map_zero, TensorProduct.tmul_zero]
  rfl

@[simp] theorem testRToPOneMap_blockBasis_QP
    (a : Fin (qSmith n L data (by omega)).rank)
    (i : Fin (pSmith n L).rank) :
    Koszul.PresentationHomology.oneMap
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1
        (quadraticBlockOneBasis n L data hn (Sum.inr a, Sum.inl i)) = 0 := by
  rw [testRToPOneMap_blockBasis]
  have hz :
      ((quadraticBlockRelationBasis n L data hn (Sum.inr a)).1) = 0 := by
    simp [quadraticBlockRelationBasis, Module.Basis.prod_apply]
  rw [hz, TensorProduct.zero_tmul]
  rfl

@[simp] theorem testRToPOneMap_blockBasis_QQ
    (a b : Fin (qSmith n L data (by omega)).rank) :
    Koszul.PresentationHomology.oneMap
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1
        (quadraticBlockOneBasis n L data hn (Sum.inr a, Sum.inr b)) = 0 := by
  rw [testRToPOneMap_blockBasis]
  have hz :
      ((quadraticBlockRelationBasis n L data hn (Sum.inr a)).1) = 0 := by
    simp [quadraticBlockRelationBasis, Module.Basis.prod_apply]
  rw [hz, TensorProduct.zero_tmul]
  rfl

theorem testPBlockRawWord_projectedCycle
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    testPBlockRawWord n L data hn
        (quadraticProjectedCycle n L data hn c).1 =
      ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inl i) (Sum.inl j) •
          (UniversalEnvelopingAlgebra.ι ℤ
              (quadraticRho n L data hn i : FreeModel n L) *
            UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn j)) := by
  change testPBlockRawWord n L data hn
      (Koszul.PresentationHomology.oneMap
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1 c.1) = _
  rw [testQuadraticBlockChain_basisExpansion n L data hn c,
    map_add, map_add, map_add]
  simp only [map_add, map_sum, map_zsmul, testRToPOneMap_blockBasis_PP,
    testRToPOneMap_blockBasis_PQ, testRToPOneMap_blockBasis_QP,
    testRToPOneMap_blockBasis_QQ, testPBlockRawWord_oneBasis,
    map_zero, smul_zero, Finset.sum_const_zero, add_zero]

theorem testPBlockRawWord_horizontal
    (i j : Fin (pSmith n L).rank) :
    testPBlockRawWord n L data hn
        (Koszul.QuadraticUCT.horizontal
          (pAugmentation n L) (pAugmentation_surjective n L)
          (pSmith n L) i j) =
      quadraticHorizontalPlacedRow n L data hn i j -
        UniversalEnvelopingAlgebra.ι ℤ
          (terminalFullRelationBracket n L data
            (quadraticRho n L data hn j) (quadraticX n L hn i) :
              FreeModel n L) := by
  rw [Koszul.QuadraticUCT.horizontal]
  calc
    _ = testPBlockRawWord n L data hn
          ((Koszul.QuadraticUCT.ratio (pAugmentation n L)
            (pSmith n L) i j : ℤ) •
              Koszul.QuadraticUCT.oneBasis
                (pAugmentation n L) (pAugmentation_surjective n L)
                (pSmith n L) (i, j)) -
        testPBlockRawWord n L data hn
          (Koszul.QuadraticUCT.oneBasis
            (pAugmentation n L) (pAugmentation_surjective n L)
            (pSmith n L) (j, i)) := by
      exact map_sub (testPBlockRawWord n L data hn) _ _
    _ = (Koszul.QuadraticUCT.ratio (pAugmentation n L)
            (pSmith n L) i j : ℤ) •
          testPBlockRawWord n L data hn
            (Koszul.QuadraticUCT.oneBasis
              (pAugmentation n L) (pAugmentation_surjective n L)
              (pSmith n L) (i, j)) -
        testPBlockRawWord n L data hn
          (Koszul.QuadraticUCT.oneBasis
            (pAugmentation n L) (pAugmentation_surjective n L)
            (pSmith n L) (j, i)) := by
      apply congrArg (fun z ↦ z - testPBlockRawWord n L data hn
        (Koszul.QuadraticUCT.oneBasis
          (pAugmentation n L) (pAugmentation_surjective n L)
          (pSmith n L) (j, i)))
      exact map_smul (testPBlockRawWord n L data hn) _ _
    _ = _ := by
      rw [testPBlockRawWord_oneBasis, testPBlockRawWord_oneBasis]
      have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
        (FreeModel n L) (quadraticRho n L data hn j : FreeModel n L)
          (quadraticX n L hn i)
      rw [hswap]
      unfold quadraticHorizontalPlacedRow terminalFullRelationBracket
      module

theorem testPBlockRawWord_horizontalExpansion
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    testPBlockRawWord n L data hn
        (quadraticProjectedCycle n L data hn c).1 =
      ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            (quadraticHorizontalPlacedRow n L data hn i j -
              UniversalEnvelopingAlgebra.ι ℤ
                (terminalFullRelationBracket n L data
                  (quadraticRho n L data hn j) (quadraticX n L hn i) :
                    FreeModel n L))
        else 0 := by
  let cp := quadraticProjectedCycle n L data hn c
  have hcycle := Koszul.QuadraticUCT.cycle_eq_horizontalExpansion
    (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L) cp
  change testPBlockRawWord n L data hn cp.1 = _
  rw [hcycle]
  unfold Koszul.QuadraticUCT.horizontalExpansion
  calc
    testPBlockRawWord n L data hn (∑ i, ∑ j,
        if hij : i < j then
          Koszul.QuadraticUCT.horizontalCoefficient
            (pAugmentation n L) (pAugmentation_surjective n L)
              (pSmith n L) cp i j •
            Koszul.QuadraticUCT.horizontal
              (pAugmentation n L) (pAugmentation_surjective n L)
                (pSmith n L) i j
        else 0) =
      ∑ i, testPBlockRawWord n L data hn (∑ j,
        if hij : i < j then
          Koszul.QuadraticUCT.horizontalCoefficient
            (pAugmentation n L) (pAugmentation_surjective n L)
              (pSmith n L) cp i j •
            Koszul.QuadraticUCT.horizontal
              (pAugmentation n L) (pAugmentation_surjective n L)
                (pSmith n L) i j
        else 0) :=
      map_sum (testPBlockRawWord n L data hn) _ Finset.univ
    _ = ∑ i, ∑ j, testPBlockRawWord n L data hn
        (if hij : i < j then
          Koszul.QuadraticUCT.horizontalCoefficient
            (pAugmentation n L) (pAugmentation_surjective n L)
              (pSmith n L) cp i j •
            Koszul.QuadraticUCT.horizontal
              (pAugmentation n L) (pAugmentation_surjective n L)
                (pSmith n L) i j
        else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact map_sum (testPBlockRawWord n L data hn) _ Finset.univ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i < j
      · simp only [hij, dite_true]
        calc
          testPBlockRawWord n L data hn
              (Koszul.QuadraticUCT.horizontalCoefficient
                  (pAugmentation n L) (pAugmentation_surjective n L)
                    (pSmith n L) cp i j •
                Koszul.QuadraticUCT.horizontal
                  (pAugmentation n L) (pAugmentation_surjective n L)
                    (pSmith n L) i j) =
            Koszul.QuadraticUCT.horizontalCoefficient
                (pAugmentation n L) (pAugmentation_surjective n L)
                  (pSmith n L) cp i j •
              testPBlockRawWord n L data hn
                (Koszul.QuadraticUCT.horizontal
                  (pAugmentation n L) (pAugmentation_surjective n L)
                    (pSmith n L) i j) :=
              map_smul (testPBlockRawWord n L data hn) _ _
          _ = _ := by
            rw [testPBlockRawWord_horizontal]
            rfl
      · simp only [hij, dite_false]
        exact map_zero (testPBlockRawWord n L data hn)

theorem testRawPP_eq_horizontalRows
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        quadraticBlockCoefficient n L data hn c (Sum.inl i) (Sum.inl j) •
          (UniversalEnvelopingAlgebra.ι ℤ
              (quadraticRho n L data hn i : FreeModel n L) *
            UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn j))) =
      ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            (quadraticHorizontalPlacedRow n L data hn i j -
              UniversalEnvelopingAlgebra.ι ℤ
                (terminalFullRelationBracket n L data
                  (quadraticRho n L data hn j) (quadraticX n L hn i) :
                    FreeModel n L))
        else 0 := by
  exact (testPBlockRawWord_projectedCycle n L data hn c).symm.trans
    (testPBlockRawWord_horizontalExpansion n L data hn c)

theorem testRawQP_eq_placed_add_bracket
    (a : Fin (qSmith n L data (by omega)).rank)
    (i : Fin (pSmith n L).rank) :
    UniversalEnvelopingAlgebra.ι ℤ
        (quadraticSigma n L data hn a : FreeModel n L) *
      UniversalEnvelopingAlgebra.ι ℤ (quadraticX n L hn i) =
    quadraticQPPlacedRow n L data hn a i +
      UniversalEnvelopingAlgebra.ι ℤ
        (terminalFullRelationBracket n L data
          (quadraticSigma n L data hn a) (quadraticX n L hn i) :
            FreeModel n L) := by
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
    (FreeModel n L) (quadraticSigma n L data hn a : FreeModel n L)
      (quadraticX n L hn i)
  rw [hswap]
  unfold quadraticQPPlacedRow terminalFullRelationBracket
  rfl

theorem testTerminalBlockRawPlacedWord_eq_canonical
    (c : Koszul.cyclesOne (rPresentation n L data (by omega)) 1) :
    terminalBlockRawPlacedWord n L data hn c.1 =
      terminalBlockCanonicalRawWord n L data hn c := by
  let relIota : Relations n L data →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
    (UniversalEnvelopingAlgebra.ι ℤ).toLinearMap.comp
      (Relations n L data).subtype
  have hPPmap :
      relIota
          (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
            if hij : i < j then
              quadraticHorizontalCoefficient n L data hn c i j •
                terminalFullRelationBracket n L data
                  (quadraticRho n L data hn j) (quadraticX n L hn i)
            else 0) =
        ∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
          if hij : i < j then
            quadraticHorizontalCoefficient n L data hn c i j •
              UniversalEnvelopingAlgebra.ι ℤ
                (terminalFullRelationBracket n L data
                  (quadraticRho n L data hn j) (quadraticX n L hn i) :
                    FreeModel n L)
          else 0 := by
    calc
      _ = ∑ i : Fin (pSmith n L).rank, relIota
          (∑ j : Fin (pSmith n L).rank,
            if hij : i < j then
              quadraticHorizontalCoefficient n L data hn c i j •
                terminalFullRelationBracket n L data
                  (quadraticRho n L data hn j) (quadraticX n L hn i)
            else 0) := map_sum relIota _ Finset.univ
      _ = ∑ i : Fin (pSmith n L).rank,
          ∑ j : Fin (pSmith n L).rank, relIota
            (if hij : i < j then
              quadraticHorizontalCoefficient n L data hn c i j •
                terminalFullRelationBracket n L data
                  (quadraticRho n L data hn j) (quadraticX n L hn i)
            else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact map_sum relIota _ Finset.univ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i < j
        · simp only [hij, dite_true]
          exact map_smul relIota _ _
        · simp only [hij, dite_false]
          exact map_zero relIota
  have hQPmap :
      relIota
          (∑ a : Fin (qSmith n L data (by omega)).rank,
            ∑ i : Fin (pSmith n L).rank,
              quadraticBlockCoefficient n L data hn c
                  (Sum.inr a) (Sum.inl i) •
                terminalFullRelationBracket n L data
                  (quadraticSigma n L data hn a) (quadraticX n L hn i)) =
        ∑ a : Fin (qSmith n L data (by omega)).rank,
          ∑ i : Fin (pSmith n L).rank,
            quadraticBlockCoefficient n L data hn c
                (Sum.inr a) (Sum.inl i) •
              UniversalEnvelopingAlgebra.ι ℤ
                (terminalFullRelationBracket n L data
                  (quadraticSigma n L data hn a) (quadraticX n L hn i) :
                    FreeModel n L) := by
    calc
      _ = ∑ a : Fin (qSmith n L data (by omega)).rank, relIota
          (∑ i : Fin (pSmith n L).rank,
            quadraticBlockCoefficient n L data hn c
                (Sum.inr a) (Sum.inl i) •
              terminalFullRelationBracket n L data
                (quadraticSigma n L data hn a) (quadraticX n L hn i)) :=
        map_sum relIota _ Finset.univ
      _ = ∑ a : Fin (qSmith n L data (by omega)).rank,
          ∑ i : Fin (pSmith n L).rank, relIota
            (quadraticBlockCoefficient n L data hn c
                (Sum.inr a) (Sum.inl i) •
              terminalFullRelationBracket n L data
                (quadraticSigma n L data hn a) (quadraticX n L hn i)) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact map_sum relIota _ Finset.univ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro i hi
        exact map_smul relIota _ _
  have hPPsplit :
      (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            (quadraticHorizontalPlacedRow n L data hn i j -
              UniversalEnvelopingAlgebra.ι ℤ
                (terminalFullRelationBracket n L data
                  (quadraticRho n L data hn j) (quadraticX n L hn i) :
                    FreeModel n L))
        else 0) =
      (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            quadraticHorizontalPlacedRow n L data hn i j
        else 0) -
      (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
        if hij : i < j then
          quadraticHorizontalCoefficient n L data hn c i j •
            UniversalEnvelopingAlgebra.ι ℤ
              (terminalFullRelationBracket n L data
                (quadraticRho n L data hn j) (quadraticX n L hn i) :
                  FreeModel n L)
        else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [hij, dite_true, smul_sub]
    · simp only [hij, dite_false, sub_zero]
  have hcorrectionMap :
      UniversalEnvelopingAlgebra.ι ℤ
          (((∑ i : Fin (pSmith n L).rank,
              ∑ j : Fin (pSmith n L).rank,
                if hij : i < j then
                  quadraticHorizontalCoefficient n L data hn c i j •
                    terminalFullRelationBracket n L data
                      (quadraticRho n L data hn j) (quadraticX n L hn i)
                else 0) -
            (∑ a : Fin (qSmith n L data (by omega)).rank,
              ∑ i : Fin (pSmith n L).rank,
                quadraticBlockCoefficient n L data hn c
                    (Sum.inr a) (Sum.inl i) •
                  terminalFullRelationBracket n L data
                    (quadraticSigma n L data hn a) (quadraticX n L hn i)) :
              Relations n L data) : FreeModel n L) =
        (∑ i : Fin (pSmith n L).rank, ∑ j : Fin (pSmith n L).rank,
          if hij : i < j then
            quadraticHorizontalCoefficient n L data hn c i j •
              UniversalEnvelopingAlgebra.ι ℤ
                (terminalFullRelationBracket n L data
                  (quadraticRho n L data hn j) (quadraticX n L hn i) :
                    FreeModel n L)
          else 0) -
        (∑ a : Fin (qSmith n L data (by omega)).rank,
          ∑ i : Fin (pSmith n L).rank,
            quadraticBlockCoefficient n L data hn c
                (Sum.inr a) (Sum.inl i) •
              UniversalEnvelopingAlgebra.ι ℤ
                (terminalFullRelationBracket n L data
                  (quadraticSigma n L data hn a) (quadraticX n L hn i) :
                    FreeModel n L)) := by
    change relIota (_ - _) = _
    calc
      relIota (_ - _) = relIota _ - relIota _ := map_sub relIota _ _
      _ = _ := by rw [hPPmap, hQPmap]
  rw [testTerminalBlockRawPlacedWord_decomposition n L data hn c,
    testRawPP_eq_horizontalRows n L data hn c]
  simp_rw [testRawQP_eq_placed_add_bracket n L data hn]
  unfold terminalBlockCanonicalRawWord quadraticBlockPlacedWord
    terminalBlockPlacementCorrection
  rw [hPPsplit, hcorrectionMap]
  simp only [smul_add, Finset.sum_add_distrib]
  module

theorem terminalMappedBlockPrimitive_eq_source_add_relation
    (c : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1) :
    ∃ rho : Relations n L data,
      pbwPrimitive n L data hn
          (terminalBlockCanonicalRawMarkedWord n L data hn
            (Koszul.PresentationHomology.cyclesMap
              (terminalSourcePresentation n L data hn)
              (rPresentation n L data (by omega))
              (terminalComparisonHom n L data hn) 1 c)).word =
        terminalSourcePrimitive n L data hn c.1 +
          (rho : FreeModel n L) := by
  let g := terminalComparisonHom n L data hn
  let blockCycle := Koszul.PresentationHomology.cyclesMap
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega)) g 1 c
  let y := testCycleExterior n L data hn c
  let relation := testBracketRealizationExterior n L data hn g y
  refine ⟨-relation, ?_⟩
  have hneg : ((-relation : Relations n L data) : FreeModel n L) =
      -(relation : FreeModel n L) :=
    map_neg (Relations n L data).subtype relation
  rw [hneg]
  rw [terminalBlockCanonicalRawMarkedWord_word,
    ← testTerminalBlockRawPlacedWord_eq_canonical n L data hn blockCycle]
  change pbwPrimitive n L data hn
      (terminalBlockRawPlacedWord n L data hn
        (Koszul.PresentationHomology.oneMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega)) g 1 c.1)) = _
  rw [testMappedBlockRawPrimitive_eq_product n L data hn g c.1,
    testSourcePlacedPrimitive_eq_product n L data hn c.1]
  have hrealization := testSourceBlockPrimitive_exterior
    n L data hn g y
  rw [testCycleExterior_spec n L data hn c] at hrealization
  change _ = _ + -(relation : FreeModel n L)
  rw [hrealization]
  abel

end

end LieRings.MetabelianVanishing
