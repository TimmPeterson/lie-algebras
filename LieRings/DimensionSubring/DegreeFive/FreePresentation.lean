import LieRings.DimensionSubring.DegreeFive.FreeClassTwo
import Mathlib.Algebra.Lie.Free

/-!
# The class-two truncation of a free Lie ring

The map constructed here is the basis-free replacement for taking the weight-one and weight-two
homogeneous components of a free Lie element.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u)

/-- The free Abelian group on the generator type. -/
abbrev GeneratorModule := X →₀ ℤ

/-- The linear degree-one inclusion into the free Lie ring. -/
def freeLieDegreeOne :
    GeneratorModule X →ₗ[ℤ] FreeLieAlgebra ℤ X :=
  Finsupp.linearCombination ℤ (FreeLieAlgebra.of ℤ)

@[simp]
theorem freeLieDegreeOne_single (x : X) :
    freeLieDegreeOne X (Finsupp.single x 1) = FreeLieAlgebra.of ℤ x := by
  simp [freeLieDegreeOne]

/-- The canonical map from the free Lie ring to its class-two truncation. -/
def freeClassTwoTruncation :
    FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ FreeClassTwo (GeneratorModule X) :=
  FreeLieAlgebra.lift ℤ (fun x ↦ FreeClassTwo.of (GeneratorModule X)
    (Finsupp.single x 1))

@[simp]
theorem freeClassTwoTruncation_of (x : X) :
    freeClassTwoTruncation X (FreeLieAlgebra.of ℤ x) =
      (Finsupp.single x 1, 0) := by
  exact FreeLieAlgebra.lift_of_apply _ _

/-- Truncating a degree-one linear combination retains that combination and no degree-two
component. -/
theorem freeClassTwoTruncation_degreeOne (p : GeneratorModule X) :
    freeClassTwoTruncation X (freeLieDegreeOne X p) = (p, 0) := by
  induction p using Finsupp.induction with
  | zero =>
      change ((0, 0) : GeneratorModule X × ⋀[ℤ]^2 (GeneratorModule X)) = (0, 0)
      rfl
  | single_add x n p hx hn ih =>
      rw [map_add, map_add, ih]
      rw [show freeLieDegreeOne X (Finsupp.single x n) =
          n • FreeLieAlgebra.of ℤ x by simp [freeLieDegreeOne]]
      rw [map_smul, freeClassTwoTruncation_of]
      change n • ((Finsupp.single x 1, 0) :
          GeneratorModule X × ⋀[ℤ]^2 (GeneratorModule X)) + (p, 0) =
        (Finsupp.single x n + p, 0)
      ext <;> simp

/-- Every pure degree-two exterior generator occurs as the truncation of a bracket. -/
theorem freeClassTwoTruncation_bracket_degreeOne (p q : GeneratorModule X) :
    freeClassTwoTruncation X
        ⁅freeLieDegreeOne X p, freeLieDegreeOne X q⁆ =
      (0, wedgeTwo (GeneratorModule X) p q) := by
  rw [LieHom.map_lie, freeClassTwoTruncation_degreeOne,
    freeClassTwoTruncation_degreeOne]
  rfl

/-- The free class-two truncation is onto. -/
theorem freeClassTwoTruncation_surjective :
    Function.Surjective (freeClassTwoTruncation X) := by
  intro z
  rcases z with ⟨p, a⟩
  let range : Submodule ℤ (FreeClassTwo (GeneratorModule X)) :=
    LinearMap.range (freeClassTwoTruncation X).toLinearMap
  have hp : (p, 0) ∈ range := by
    exact ⟨freeLieDegreeOne X p, freeClassTwoTruncation_degreeOne X p⟩
  have hwedge (v : Fin 2 → GeneratorModule X) :
      (0, exteriorPower.ιMulti ℤ 2 v) ∈ range := by
    refine ⟨⁅freeLieDegreeOne X (v 0), freeLieDegreeOne X (v 1)⁆, ?_⟩
    simpa [wedgeTwo] using
      freeClassTwoTruncation_bracket_degreeOne X (v 0) (v 1)
  have ha : (0, a) ∈ range := by
    have hspan : a ∈ Submodule.span ℤ
        (Set.range (exteriorPower.ιMulti ℤ 2 :
          (Fin 2 → GeneratorModule X) → ⋀[ℤ]^2 (GeneratorModule X))) := by
      have htop : Submodule.span ℤ
          (Set.range (exteriorPower.ιMulti ℤ 2 :
            (Fin 2 → GeneratorModule X) → ⋀[ℤ]^2 (GeneratorModule X))) = ⊤ :=
        exteriorPower.ιMulti_span ℤ 2 (GeneratorModule X)
      rw [htop]
      trivial
    refine Submodule.span_induction (p := fun a _ ↦ (0, a) ∈ range)
      ?_ range.zero_mem
      (fun x y _ _ hx hy ↦ by
        simpa using range.add_mem hx hy)
      (fun n x _ hx ↦ by
        simpa using range.smul_mem n hx) hspan
    rintro _ ⟨v, rfl⟩
    exact hwedge v
  have hz : (p, a) ∈ range := by
    convert range.add_mem hp ha using 1 <;> simp
  exact hz

end

end DegreeFive

end LieRings
