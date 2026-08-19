import LieRings.DimensionSubring.MetabelianVanishing.Tower
import LieRings.LinearAlgebra.InvariantFactorSmith

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

/-! ## The terminal Smith presentation -/

local instance terminalWFinite : Finite (W L n) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)

/-- The terminal quotient `A_n / D_n` is finite. -/
@[implicit_reducible] def terminalQuotientFinite :
    Finite (A L n ⧸ D n L data n (by omega)) := by
  rw [exact_D_augmentation n L data n (by omega)]
  let e := (augmentation (n := n) L data n).quotKerEquivOfSurjective
    (augmentation_surjective (n := n) L data n (by omega))
  exact Finite.of_surjective e.symm e.symm.surjective

/-- Smith bases for the complete terminal relation module `D_n ⊆ A_n`. -/
def terminalSmith :
    InvariantFactorPresentation (D n L data n (by omega)) := by
  let b := prefixBasis L n
  letI : Module.Free ℤ (A L n) := Module.Free.of_basis b
  letI : Module.Finite ℤ (A L n) := Module.Finite.of_basis b
  letI : Finite (A L n ⧸ D n L data n (by omega)) :=
    terminalQuotientFinite n L data hn
  exact InvariantFactorPresentation.ofFiniteQuotient
    (D n L data n (Nat.le_succ n)) inferInstance

/-! ## The truncated bracket and preservation of terminal relations -/

/-- The intrinsic truncated Lie bracket on `A_n`, in bilinear linear-map
form. -/
def terminalBracket : A L n →ₗ[ℤ] A L n →ₗ[ℤ] A L n :=
  LinearMap.mk₂ ℤ (fun x y ↦ ⁅x, y⁆)
    (by intro x y z; exact add_lie x y z)
    (by intro z x y; exact smul_lie z x y)
    (by intro x y z; exact lie_add x y z)
    (by intro z x y; exact lie_smul z x y)

@[simp] theorem terminalBracket_apply (x y : A L n) :
    terminalBracket n L x y = ⁅x, y⁆ := rfl

/-- Prefix restriction commutes with the truncated metabelian bracket. -/
theorem prLE_lie_prefixIncl (x : FreeModel n L) (y : A L n) :
    prLE n L n (by omega)
        ⁅x, FreeMetabelian.Free.prefixIncl n (by omega) y⁆ =
      ⁅prLE n L n (by omega) x, y⁆ := by
  funext i
  rcases i with ⟨(_ | _ | q), hi⟩
  · rfl
  · change FreeMetabelian.generatorBracket (Generator L)
        (x ⟨0, by omega⟩)
        ((FreeMetabelian.Free.prefixIncl n (by omega) y) ⟨0, by omega⟩) =
      FreeMetabelian.generatorBracket (Generator L)
        ((prLE n L n (by omega) x) ⟨0, by omega⟩) (y ⟨0, by omega⟩)
    rw [FreeMetabelian.Free.prefixIncl_apply_of_lt]
    rfl
  · change FreeMetabelian.Action.apply (Generator L) q
          ((FreeMetabelian.Free.prefixIncl n (by omega) y) ⟨0, by omega⟩)
          (x ⟨q + 1, by omega⟩) -
        FreeMetabelian.Action.apply (Generator L) q
          (x ⟨0, by omega⟩)
          ((FreeMetabelian.Free.prefixIncl n (by omega) y)
            ⟨q + 1, by omega⟩) =
      FreeMetabelian.Action.apply (Generator L) q
          (y ⟨0, by omega⟩)
          ((prLE n L n (by omega) x) ⟨q + 1, by omega⟩) -
        FreeMetabelian.Action.apply (Generator L) q
          ((prLE n L n (by omega) x) ⟨0, by omega⟩)
          (y ⟨q + 1, by omega⟩)
    rw [FreeMetabelian.Free.prefixIncl_apply_of_lt,
      FreeMetabelian.Free.prefixIncl_apply_of_lt]
    rfl

/-- `D_n` is closed under right bracketing by `A_n`. -/
theorem terminalBracket_mem_D
    (d : D n L data n (by omega)) (x : A L n) :
    ⁅(d : A L n), x⁆ ∈ D n L data n (by omega) := by
  rcases d.2 with ⟨rho, hrho⟩
  let xfull : FreeModel n L :=
    FreeMetabelian.Free.prefixIncl n (by omega) x
  let sigma : Relations n L data :=
    ⟨⁅(rho : FreeModel n L), xfull⁆, by
      change evaluation n L data ⁅(rho : FreeModel n L), xfull⁆ = 0
      rw [LieHom.map_lie]
      have hz : evaluation n L data (rho : FreeModel n L) = 0 := rho.property
      rw [hz, zero_lie]⟩
  refine ⟨sigma, ?_⟩
  change relationPrefix n L data n (by omega) sigma = ⁅(d : A L n), x⁆
  change prLE n L n (by omega) ⁅(rho : FreeModel n L), xfull⁆ = _
  rw [prLE_lie_prefixIncl n L]
  rw [← hrho]
  rfl

/-- The bracket action of `A_n` on its terminal relation module. -/
def terminalRelationBracket :
    D n L data n (by omega) →ₗ[ℤ]
      A L n →ₗ[ℤ] D n L data n (by omega) :=
  LinearMap.mk₂ ℤ
    (fun d x ↦ ⟨⁅(d : A L n), x⁆,
      terminalBracket_mem_D n L data d x⟩)
    (by
      intro x y z
      apply Subtype.ext
      exact add_lie (x : A L n) y z)
    (by
      intro z x y
      apply Subtype.ext
      exact smul_lie z (x : A L n) y)
    (by
      intro x y z
      apply Subtype.ext
      exact lie_add (x : A L n) y z)
    (by
      intro z x y
      apply Subtype.ext
      exact lie_smul z (x : A L n) y)

@[simp] theorem terminalRelationBracket_coe
    (d : D n L data n (by omega)) (x : A L n) :
    ((terminalRelationBracket n L data d x :
        D n L data n (by omega)) : A L n) = ⁅(d : A L n), x⁆ := rfl

/-! ## Coordinates in the terminal relation basis -/

/-- Coordinates of `[d,x]` in the terminal Smith relation basis. -/
def terminalRelationBracketCoordinates
    (d : D n L data n (by omega)) (x : A L n) :
    Fin (terminalSmith n L data hn).rank →₀ ℤ :=
  (terminalSmith n L data hn).relationBasis.repr
    (terminalRelationBracket n L data d x)

/-- The coordinate expansion reconstructs the bracket in `D_n`. -/
theorem terminalRelationBracket_sum
    (d : D n L data n (by omega)) (x : A L n) :
    ∑ i, terminalRelationBracketCoordinates n L data hn d x i •
        (terminalSmith n L data hn).relationBasis i =
      terminalRelationBracket n L data d x := by
  exact (terminalSmith n L data hn).relationBasis.sum_repr
    (terminalRelationBracket n L data d x)

/-- The same coordinate expansion after forgetting the subtype. -/
theorem terminalRelationBracket_sum_coe
    (d : D n L data n (by omega)) (x : A L n) :
    ∑ i, terminalRelationBracketCoordinates n L data hn d x i •
        ((terminalSmith n L data hn).relationBasis i : A L n) =
      ⁅(d : A L n), x⁆ := by
  have h := congrArg
    (D n L data n (by omega)).subtype
    (terminalRelationBracket_sum n L data hn d x)
  simpa only [map_sum, map_zsmul, terminalRelationBracket_coe] using h

/-! ## Genuine full-relation representatives -/

/-- A chosen genuine full relation lifting one vector of the terminal Smith
relation basis.  Only these basiswise choices are made; arbitrary elements
are lifted by the resulting linear section. -/
def terminalRelationBasisFullLift
    (i : Fin (terminalSmith n L data hn).rank) : Relations n L data :=
  Classical.choose ((terminalSmith n L data hn).relationBasis i).property

@[simp] theorem relationPrefix_terminalRelationBasisFullLift
    (i : Fin (terminalSmith n L data hn).rank) :
    relationPrefix n L data n (by omega)
        (terminalRelationBasisFullLift n L data hn i) =
      ((terminalSmith n L data hn).relationBasis i : A L n) :=
  Classical.choose_spec ((terminalSmith n L data hn).relationBasis i).property

/-- The linear section of `relationPrefix` obtained from the terminal Smith
relation basis.  Its values remain genuine elements of `Relations`. -/
def terminalRelationFullSection :
    D n L data n (by omega) →ₗ[ℤ] Relations n L data :=
  (terminalSmith n L data hn).relationBasis.constr ℤ
    (terminalRelationBasisFullLift n L data hn)

@[simp] theorem terminalRelationFullSection_basis
    (i : Fin (terminalSmith n L data hn).rank) :
    terminalRelationFullSection n L data hn
        ((terminalSmith n L data hn).relationBasis i) =
      terminalRelationBasisFullLift n L data hn i := by
  rw [terminalRelationFullSection, Module.Basis.constr_basis]

/-- The chosen full-relation lift is a strict section at the terminal
prefix. -/
theorem relationPrefix_terminalRelationFullSection
    (d : D n L data n (by omega)) :
    relationPrefix n L data n (by omega)
        (terminalRelationFullSection n L data hn d) = (d : A L n) := by
  let B := (terminalSmith n L data hn).relationBasis
  have hmaps :
      (relationPrefix n L data n (by omega)).comp
          (terminalRelationFullSection n L data hn) =
        (D n L data n (by omega)).subtype := by
    apply B.ext
    intro i
    simp [B]
  exact LinearMap.congr_fun hmaps d

/-- The full relation representing the truncated correction `[d,x]`. -/
def terminalRelationBracketFullLift
    (d : D n L data n (by omega)) (x : A L n) : Relations n L data :=
  terminalRelationFullSection n L data hn
    (terminalRelationBracket n L data d x)

@[simp] theorem relationPrefix_terminalRelationBracketFullLift
    (d : D n L data n (by omega)) (x : A L n) :
    relationPrefix n L data n (by omega)
        (terminalRelationBracketFullLift n L data hn d x) =
      ⁅(d : A L n), x⁆ := by
  rw [terminalRelationBracketFullLift,
    relationPrefix_terminalRelationFullSection]
  rfl

/-- Basis-specialized correction coordinates, the finite table needed by a
Smith-row collector. -/
def terminalSmithBracketCoordinates
    (i j : Fin (terminalSmith n L data hn).rank) :
    Fin (terminalSmith n L data hn).rank →₀ ℤ :=
  terminalRelationBracketCoordinates n L data hn
    ((terminalSmith n L data hn).relationBasis i)
    ((terminalSmith n L data hn).ambientBasis j)

/-- Each basis correction is exactly the indicated integral combination of
terminal Smith relation rows. -/
theorem terminalSmithBracket_sum
    (i j : Fin (terminalSmith n L data hn).rank) :
    ∑ k, terminalSmithBracketCoordinates n L data hn i j k •
        ((terminalSmith n L data hn).relationBasis k : A L n) =
      ⁅((terminalSmith n L data hn).relationBasis i : A L n),
        (terminalSmith n L data hn).ambientBasis j⁆ := by
  exact terminalRelationBracket_sum_coe n L data hn
    ((terminalSmith n L data hn).relationBasis i)
    ((terminalSmith n L data hn).ambientBasis j)

end

end LieRings.MetabelianVanishing
