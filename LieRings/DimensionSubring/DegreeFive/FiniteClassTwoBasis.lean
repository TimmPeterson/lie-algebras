import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneousFactors
import LieRings.DimensionSubring.DegreeFive.FreeClassTwoKernel

/-!
# The homogeneous basis of the finite free class-two quotient

The placed collector chooses bases independently in free-Lie weights one and two.  The direct
sum of those two exact components is canonically the free class-two quotient.  Keeping this
basis, rather than silently replacing it by the original-generator basis, is essential: it
makes the order used by packet collection agree with the order used by PBW coordinates.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]

local notation "F" => FreeLieAlgebra ℤ X
local notation "P" => GeneratorModule X
local notation "M" => FreeClassTwo P

/-- Projection back to the same homogeneous component fixes an exact free-Lie element. -/
theorem freeLieLengthComponent_coe_exact
    (n : ℕ) (x : freeLieExact X n) :
    freeLieLengthComponent X n (x : F) = (x : F) := by
  apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
  rw [freeLieToFreeAlgebra_freeLieLengthComponent]
  exact associativeLengthComponent_eq_self_of_mem_exact X
    (freeLieToFreeAlgebra_mem_exact X x)

/-- A different homogeneous projection of an exact free-Lie element is zero. -/
theorem freeLieLengthComponent_coe_exact_of_ne
    {m n : ℕ} (x : freeLieExact X m) (hmn : m ≠ n) :
    freeLieLengthComponent X n (x : F) = 0 := by
  apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
  rw [freeLieToFreeAlgebra_freeLieLengthComponent, map_zero]
  exact associativeLengthComponent_eq_zero_of_mem_exact_of_ne X
    (freeLieToFreeAlgebra_mem_exact X x) hmn

/-- An exact component below a strictly higher filtration step has zero intersection with it. -/
theorem freeLieExact_eq_zero_of_mem_lieHigh
    {m n : ℕ} (x : freeLieExact X m)
    (hx : (x : F) ∈ FreeLieDimension.lieHigh X n) (hmn : m < n) : x = 0 := by
  apply Subtype.ext
  have hzero := freeLieLengthComponent_eq_zero_of_mem_lieHigh
    X hx hmn
  rw [freeLieLengthComponent_coe_exact X m x] at hzero
  exact hzero

/-- The direct sum of exact weights one and two, mapped to the class-two quotient. -/
def finiteLowExactToClassTwo :
    (freeLieExact X 1 × freeLieExact X 2) →ₗ[ℤ] M where
  toFun z := freeClassTwoTruncation X ((z.1 : F) + (z.2 : F))
  map_add' x y := by
    rw [Prod.fst_add, Prod.snd_add]
    change freeClassTwoTruncation X
        (((x.1 + y.1 : freeLieExact X 1) : F) +
          ((x.2 + y.2 : freeLieExact X 2) : F)) = _
    change freeClassTwoTruncation X
        ((x.1 : F) + (y.1 : F) + ((x.2 : F) + (y.2 : F))) = _
    simp only [map_add]
    abel
  map_smul' n x := by
    rw [Prod.smul_fst, Prod.smul_snd]
    change freeClassTwoTruncation X
        (((n • x.1 : freeLieExact X 1) : F) +
          ((n • x.2 : freeLieExact X 2) : F)) = _
    change freeClassTwoTruncation X
        (n • (x.1 : F) + n • (x.2 : F)) = _
    rw [← smul_add, map_smul]
    rfl

/-- The low homogeneous map is injective. -/
theorem finiteLowExactToClassTwo_injective :
    Function.Injective (finiteLowExactToClassTwo X) := by
  intro x y hxy
  have hzero : finiteLowExactToClassTwo X (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  suffices hxyzero : x - y = 0 from sub_eq_zero.mp hxyzero
  rcases zdef : x - y with ⟨z₁, z₂⟩
  rw [zdef] at hzero
  change freeClassTwoTruncation X ((z₁ : F) + (z₂ : F)) = 0 at hzero
  have hhigh : (z₁ : F) + (z₂ : F) ∈
      FreeLieDimension.lieHigh X 3 := by
    rw [FreeLieDimension.lieHigh_eq_lowerCentralSeries X 2]
    exact (freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two
      X _).mp hzero
  have hone := freeLieLengthComponent_eq_zero_of_mem_lieHigh
    X hhigh (by omega : 1 < 3)
  rw [map_add, freeLieLengthComponent_coe_exact X 1 z₁,
    freeLieLengthComponent_coe_exact_of_ne X z₂ (by omega : 2 ≠ 1),
    add_zero] at hone
  have hz₁ : z₁ = 0 := Subtype.ext hone
  have htwo := freeLieLengthComponent_eq_zero_of_mem_lieHigh
    X hhigh (by omega : 2 < 3)
  rw [map_add, freeLieLengthComponent_coe_exact_of_ne X z₁
    (by omega : 1 ≠ 2), freeLieLengthComponent_coe_exact X 2 z₂,
    zero_add] at htwo
  have hz₂ : z₂ = 0 := Subtype.ext htwo
  simp [hz₁, hz₂]

/-- The low homogeneous map is surjective. -/
theorem finiteLowExactToClassTwo_surjective :
    Function.Surjective (finiteLowExactToClassTwo X) := by
  intro z
  obtain ⟨f, hf⟩ := freeClassTwoTruncation_surjective X z
  let f₁ : freeLieExact X 1 :=
    ⟨freeLieLengthComponent X 1 f,
      freeLieLengthComponent_mem_exact X 1 f⟩
  let f₂ : freeLieExact X 2 :=
    ⟨freeLieLengthComponent X 2 f,
      freeLieLengthComponent_mem_exact X 2 f⟩
  refine ⟨(f₁, f₂), ?_⟩
  suffices hrem : f - (f₁ : F) - (f₂ : F) ∈
      FreeLieDimension.lieHigh X 3 by
    have hgamma : f - (f₁ : F) - (f₂ : F) ∈
        lowerCentralSeries ℤ F 2 := by
      rw [FreeLieDimension.lieHigh_eq_lowerCentralSeries X 2] at hrem
      exact hrem
    have htrunc : freeClassTwoTruncation X
        (f - (f₁ : F) - (f₂ : F)) = 0 :=
      (freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two
        X _).mpr hgamma
    change freeClassTwoTruncation X ((f₁ : F) + (f₂ : F)) = z
    rw [← hf]
    rw [map_sub, map_sub] at htrunc
    rw [map_add]
    rw [sub_sub] at htrunc
    exact (sub_eq_zero.mp htrunc).symm
  have hhighOne : f - (f₁ : F) - (f₂ : F) ∈
      FreeLieDimension.lieHigh X 1 := by
    rw [FreeLieDimension.lieHigh_one]
    trivial
  have hcomponentOne : freeLieLengthComponent X 1
      (f - (f₁ : F) - (f₂ : F)) = 0 := by
    rw [map_sub, map_sub]
    change freeLieLengthComponent X 1 f -
        freeLieLengthComponent X 1 (f₁ : F) -
          freeLieLengthComponent X 1 (f₂ : F) = 0
    rw [freeLieLengthComponent_coe_exact X 1 f₁,
      freeLieLengthComponent_coe_exact_of_ne X f₂ (by omega : 2 ≠ 1)]
    change freeLieLengthComponent X 1 f - freeLieLengthComponent X 1 f - 0 = 0
    abel
  have hhighTwo : f - (f₁ : F) - (f₂ : F) ∈
      FreeLieDimension.lieHigh X 2 := by
    simpa using mem_lieHigh_succ_of_component_eq_zero X hhighOne hcomponentOne
  have hcomponentTwo : freeLieLengthComponent X 2
      (f - (f₁ : F) - (f₂ : F)) = 0 := by
    rw [map_sub, map_sub]
    change freeLieLengthComponent X 2 f -
        freeLieLengthComponent X 2 (f₁ : F) -
          freeLieLengthComponent X 2 (f₂ : F) = 0
    rw [freeLieLengthComponent_coe_exact_of_ne X f₁ (by omega : 1 ≠ 2),
      freeLieLengthComponent_coe_exact X 2 f₂]
    change freeLieLengthComponent X 2 f - 0 - freeLieLengthComponent X 2 f = 0
    abel
  simpa using mem_lieHigh_succ_of_component_eq_zero X hhighTwo hcomponentTwo

/-- Exact weights one and two give a linear equivalence with the free class-two quotient. -/
def finiteLowExactEquivClassTwo :
    (freeLieExact X 1 × freeLieExact X 2) ≃ₗ[ℤ] M :=
  LinearEquiv.ofBijective (finiteLowExactToClassTwo X)
    ⟨finiteLowExactToClassTwo_injective X,
      finiteLowExactToClassTwo_surjective X⟩

/-- Indices of the homogeneous class-two basis, with all weight-one entries before weight two. -/
inductive FiniteClassTwoBasisIndex (X : Type u) [Finite X]
  | weightOne (i : FreeLieExactBasisIndex X 1)
  | weightTwo (i : FreeLieExactBasisIndex X 2)

/-- Numerical code inducing exactly the order inherited from the low homogeneous collector. -/
def finiteClassTwoBasisIndexCode : FiniteClassTwoBasisIndex X → ℕ × ℕ
  | .weightOne i => (0, i.1)
  | .weightTwo i => (1, i.1)

theorem finiteClassTwoBasisIndexCode_injective :
    Function.Injective (finiteClassTwoBasisIndexCode X) := by
  intro i j hij
  cases i with
  | weightOne i =>
      cases j with
      | weightOne j =>
          simp only [finiteClassTwoBasisIndexCode, Prod.mk.injEq] at hij
          exact congrArg FiniteClassTwoBasisIndex.weightOne (Fin.ext hij.2)
      | weightTwo j => simp [finiteClassTwoBasisIndexCode] at hij
  | weightTwo i =>
      cases j with
      | weightOne j => simp [finiteClassTwoBasisIndexCode] at hij
      | weightTwo j =>
          simp only [finiteClassTwoBasisIndexCode, Prod.mk.injEq] at hij
          exact congrArg FiniteClassTwoBasisIndex.weightTwo (Fin.ext hij.2)

noncomputable instance finiteClassTwoBasisIndexLinearOrder :
    LinearOrder (FiniteClassTwoBasisIndex X) :=
  LinearOrder.lift' (fun i ↦ toLex (finiteClassTwoBasisIndexCode X i))
    (toLex.injective.comp (finiteClassTwoBasisIndexCode_injective X))

/-- Identification with the sum index of the product of the two exact-component bases. -/
def finiteClassTwoBasisIndexEquiv :
    (FreeLieExactBasisIndex X 1 ⊕ FreeLieExactBasisIndex X 2) ≃
      FiniteClassTwoBasisIndex X where
  toFun
    | .inl i => .weightOne i
    | .inr i => .weightTwo i
  invFun
    | .weightOne i => .inl i
    | .weightTwo i => .inr i
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i <;> rfl

/-- The class-two basis transported from the exact free-Lie bases used by the collector. -/
def finiteHomogeneousClassTwoBasis :
    Module.Basis (FiniteClassTwoBasisIndex X) ℤ M :=
  (((freeLieExactBasis X 1).prod (freeLieExactBasis X 2)).map
      (finiteLowExactEquivClassTwo X)).reindex
    (finiteClassTwoBasisIndexEquiv X)

@[simp]
theorem finiteHomogeneousClassTwoBasis_weightOne
    (i : FreeLieExactBasisIndex X 1) :
    finiteHomogeneousClassTwoBasis X (.weightOne i) =
      freeClassTwoTruncation X
        ((freeLieExactBasis X 1 i : freeLieExact X 1) : F) := by
  rw [finiteHomogeneousClassTwoBasis, Module.Basis.reindex_apply,
    Module.Basis.map_apply]
  simp [finiteClassTwoBasisIndexEquiv, finiteLowExactEquivClassTwo,
    finiteLowExactToClassTwo]

@[simp]
theorem finiteHomogeneousClassTwoBasis_weightTwo
    (i : FreeLieExactBasisIndex X 2) :
    finiteHomogeneousClassTwoBasis X (.weightTwo i) =
      freeClassTwoTruncation X
        ((freeLieExactBasis X 2 i : freeLieExact X 2) : F) := by
  rw [finiteHomogeneousClassTwoBasis, Module.Basis.reindex_apply,
    Module.Basis.map_apply]
  simp [finiteClassTwoBasisIndexEquiv, finiteLowExactEquivClassTwo,
    finiteLowExactToClassTwo]


end

end DegreeFive

end LieRings
