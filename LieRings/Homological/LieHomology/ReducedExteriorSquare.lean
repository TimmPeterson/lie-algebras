import LieRings.Homological.LieHomology.DegreeTwo

/-!
# The reduced exterior square

The reduced exterior square of a Lie algebra is the cokernel of the third
Chevalley--Eilenberg differential.  Its induced bracket has kernel equal to second homology.
This elementary reformulation is the starting point of the Hopf-formula calculation.
-/

universe u v w

namespace LieRings.Homological.LieHomology

noncomputable section

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The submodule of degree-two CE boundaries. -/
abbrev thirdBoundaries : Submodule R (⋀[R]^2 L) :=
  LinearMap.range (differential R L 2)

/-- The reduced exterior square `Coker(d₃)`. -/
abbrev ReducedExteriorSquare : Type (max u v) :=
  (⋀[R]^2 L) ⧸ thirdBoundaries R L

/-- The quotient map from the exterior square to the reduced exterior square. -/
abbrev reducedClass : (⋀[R]^2 L) →ₗ[R] ReducedExteriorSquare R L :=
  (thirdBoundaries R L).mkQ

/-- The class of a pure wedge in the reduced exterior square, bundled bilinearly. -/
def reducedWedge : L →ₗ[R] L →ₗ[R] ReducedExteriorSquare R L :=
  LinearMap.mk₂ R
    (fun x y => reducedClass R L (exteriorPower.ιMulti R 2 ![x, y]))
    (by
      intro x y z
      have h : exteriorPower.ιMulti R 2 ![x + y, z] =
          exteriorPower.ιMulti R 2 ![x, z] + exteriorPower.ιMulti R 2 ![y, z] := by
        exact (exteriorPower.ιMulti R 2).map_update_add
          (v := ![0, z]) (i := 0) x y
      change reducedClass R L (exteriorPower.ιMulti R 2 ![x + y, z]) = _
      rw [h, map_add])
    (by
      intro r x y
      have h : exteriorPower.ιMulti R 2 ![r • x, y] =
          r • exteriorPower.ιMulti R 2 ![x, y] := by
        exact (exteriorPower.ιMulti R 2).map_update_smul
          (v := ![0, y]) (i := 0) r x
      change reducedClass R L (exteriorPower.ιMulti R 2 ![r • x, y]) = _
      rw [h, map_smul])
    (by
      intro x y z
      have h : exteriorPower.ιMulti R 2 ![x, y + z] =
          exteriorPower.ιMulti R 2 ![x, y] + exteriorPower.ιMulti R 2 ![x, z] := by
        exact (exteriorPower.ιMulti R 2).map_update_add
          (v := ![x, 0]) (i := 1) y z
      change reducedClass R L (exteriorPower.ιMulti R 2 ![x, y + z]) = _
      rw [h, map_add])
    (by
      intro r x y
      have h : exteriorPower.ιMulti R 2 ![x, r • y] =
          r • exteriorPower.ιMulti R 2 ![x, y] := by
        exact (exteriorPower.ιMulti R 2).map_update_smul
          (v := ![x, 0]) (i := 1) r y
      change reducedClass R L (exteriorPower.ιMulti R 2 ![x, r • y]) = _
      rw [h, map_smul])

@[simp]
theorem reducedWedge_apply (x y : L) :
    reducedWedge R L x y =
      reducedClass R L (exteriorPower.ιMulti R 2 ![x, y]) := rfl

@[simp]
theorem reducedWedge_zero_left (y : L) : reducedWedge R L 0 y = 0 := by
  rw [map_zero]
  rfl

@[simp]
theorem reducedWedge_zero_right (x : L) : reducedWedge R L x 0 = 0 :=
  map_zero (reducedWedge R L x)

@[simp]
theorem reducedWedge_self (x : L) : reducedWedge R L x x = 0 := by
  rw [reducedWedge_apply]
  have h := (exteriorPower.ιMulti R 2).map_eq_zero_of_eq ![x, x]
    (i := 0) (j := 1) rfl (by decide)
  simpa using congrArg (reducedClass R L) h

theorem reducedWedge_skew (x y : L) :
    reducedWedge R L x y = -reducedWedge R L y x := by
  change reducedClass R L (exteriorPower.ιMulti R 2 ![x, y]) =
    -reducedClass R L (exteriorPower.ιMulti R 2 ![y, x])
  rw [← map_neg]
  congr 1
  apply Subtype.ext
  simp [ExteriorAlgebra.ιMulti_succ_apply]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := R) x y)

/-- The defining `d₃` relation in the reduced exterior square, written in Leibniz form. -/
theorem reducedWedge_leibniz (x y z : L) :
    reducedWedge R L x ⁅y, z⁆ =
      reducedWedge R L ⁅x, y⁆ z + reducedWedge R L y ⁅x, z⁆ := by
  have hd : differential R L 2 (exteriorPower.ιMulti R 3 ![x, y, z]) =
      -exteriorPower.ιMulti R 2 ![⁅x, y⁆, z] +
        exteriorPower.ιMulti R 2 ![⁅x, z⁆, y] -
          exteriorPower.ιMulti R 2 ![⁅y, z⁆, x] := by
    apply Subtype.ext
    simpa [ExteriorAlgebra.ιMulti_succ_apply] using
      differential_two_ιMulti_coe R L x y z
  have hzero :
      -reducedWedge R L ⁅x, y⁆ z + reducedWedge R L ⁅x, z⁆ y -
          reducedWedge R L ⁅y, z⁆ x = 0 := by
    have hboundary :
        reducedClass R L (differential R L 2
          (exteriorPower.ιMulti R 3 ![x, y, z])) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨_, rfl⟩
    rw [hd, map_sub, map_add, map_neg] at hboundary
    exact hboundary
  rw [reducedWedge_skew R L x ⁅y, z⁆, reducedWedge_skew R L y ⁅x, z⁆]
  have hsum :
    (-reducedWedge R L ⁅x, y⁆ z + reducedWedge R L ⁅x, z⁆ y) +
      (-reducedWedge R L ⁅y, z⁆ x) = 0 := by
    rw [← sub_eq_add_neg]
    exact hzero
  have h := eq_neg_of_add_eq_zero_right hsum
  calc
    -reducedWedge R L ⁅y, z⁆ x =
        -(-reducedWedge R L ⁅x, y⁆ z + reducedWedge R L ⁅x, z⁆ y) := h
    _ = -reducedWedge R L ⁅x, z⁆ y + reducedWedge R L ⁅x, y⁆ z := by
      rw [neg_add_rev, neg_neg]
    _ = reducedWedge R L ⁅x, y⁆ z + -reducedWedge R L ⁅x, z⁆ y := add_comm _ _

private theorem thirdBoundaries_le_degreeTwoBoundary_ker :
    thirdBoundaries R L ≤ LinearMap.ker (degreeTwoBoundary R L) := by
  rintro _ ⟨x, rfl⟩
  change degreeTwoBoundary R L (differential R L 2 x) = 0
  change exteriorPower.oneEquiv R L
      (differential R L 1 (differential R L 2 x)) = 0
  rw [show differential R L 1 (differential R L 2 x) = 0 by
    exact LinearMap.congr_fun (differential_comp_differential R L 1) x]
  exact map_zero _

/-- The bracket induced on the reduced exterior square. -/
def reducedBracket : ReducedExteriorSquare R L →ₗ[R] L :=
  (thirdBoundaries R L).liftQ (bracketMap R L)
    (by
      intro x hx
      change -degreeTwoBoundary R L x = 0
      rw [(thirdBoundaries_le_degreeTwoBoundary_ker R L) hx]
      exact neg_zero)

@[simp]
theorem reducedBracket_class (x : ⋀[R]^2 L) :
    reducedBracket R L (reducedClass R L x) = bracketMap R L x :=
  Submodule.liftQ_apply _ _ x

@[simp]
theorem reducedBracket_wedge (x y : L) :
    reducedBracket R L (reducedWedge R L x y) = ⁅x, y⁆ := by
  rw [reducedWedge_apply, reducedBracket_class, bracketMap_ιMulti]

private def cyclesToReducedBracketKernel :
    secondCycles R L →ₗ[R] LinearMap.ker (reducedBracket R L) where
  toFun z := ⟨reducedClass R L z, by
    change bracketMap R L z = 0
    change -exteriorPower.oneEquiv R L (differential R L 1 z) = 0
    rw [z.property]
    simp⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

private theorem boundaries_le_cyclesToReducedBracketKernel_ker :
    LinearMap.range (thirdBoundaryToCycles R L) ≤
      LinearMap.ker (cyclesToReducedBracketKernel R L) := by
  rintro _ ⟨x, rfl⟩
  apply Subtype.ext
  change reducedClass R L (differential R L 2 x) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

/-- The canonical map from second CE homology to the kernel of the bracket on the reduced
exterior square. -/
def secondHomologyToReducedBracketKernel :
    SecondHomology R L →ₗ[R] LinearMap.ker (reducedBracket R L) :=
  (LinearMap.range (thirdBoundaryToCycles R L)).liftQ
    (cyclesToReducedBracketKernel R L)
    (boundaries_le_cyclesToReducedBracketKernel_ker R L)

@[simp]
private theorem secondHomologyToReducedBracketKernel_mk (z : secondCycles R L) :
    secondHomologyToReducedBracketKernel R L (Submodule.Quotient.mk z) =
      cyclesToReducedBracketKernel R L z :=
  Submodule.liftQ_apply _ _ z

private theorem secondHomologyToReducedBracketKernel_injective :
    Function.Injective (secondHomologyToReducedBracketKernel R L) := by
  intro a b hab
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      rw [secondHomologyToReducedBracketKernel_mk,
        secondHomologyToReducedBracketKernel_mk] at hab
      apply (Submodule.Quotient.eq _).2
      have hab' : reducedClass R L (a : ⋀[R]^2 L) = reducedClass R L b :=
        congrArg Subtype.val hab
      have hq : reducedClass R L (a - b : ⋀[R]^2 L) = 0 := by
        rw [map_sub, hab', sub_self]
      obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).1 hq
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx

private theorem secondHomologyToReducedBracketKernel_surjective :
    Function.Surjective (secondHomologyToReducedBracketKernel R L) := by
  intro y
  obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_surjective (thirdBoundaries R L)) y.1
  have hcycle : differential R L 1 x = 0 := by
    have hy := y.property
    change reducedBracket R L y.1 = 0 at hy
    rw [← hx] at hy
    change bracketMap R L x = 0 at hy
    change -exteriorPower.oneEquiv R L (differential R L 1 x) = 0 at hy
    rw [neg_eq_zero] at hy
    exact (exteriorPower.oneEquiv R L).injective (by simpa using hy)
  let z : secondCycles R L := ⟨x, hcycle⟩
  refine ⟨Submodule.Quotient.mk z, ?_⟩
  rw [secondHomologyToReducedBracketKernel_mk]
  apply Subtype.ext
  exact hx

/-- The standard identification
`H₂(L;R) ≃ ker(Λ̃²L → L)`. -/
noncomputable def secondHomologyEquivReducedBracketKernel :
    SecondHomology R L ≃ₗ[R] LinearMap.ker (reducedBracket R L) :=
  LinearEquiv.ofBijective (secondHomologyToReducedBracketKernel R L)
    ⟨secondHomologyToReducedBracketKernel_injective R L,
      secondHomologyToReducedBracketKernel_surjective R L⟩

/-! ## Functoriality -/

variable {L}
variable {K : Type w} [LieRing K] [LieAlgebra R K]

private theorem map_thirdBoundaries (f : LieHom R L K) :
    thirdBoundaries R L ≤
      (thirdBoundaries R K).comap (exteriorPower.map 2 f.toLinearMap) := by
  rintro _ ⟨(x : ⋀[R]^3 L), rfl⟩
  change exteriorPower.map 2 f.toLinearMap (differential R L 2 x) ∈
    LinearMap.range (differential R K 2)
  refine ⟨exteriorPower.map 3 f.toLinearMap x, ?_⟩
  exact (differential_natural_apply R L f 2 x).symm

/-- The map on reduced exterior squares induced by a Lie homomorphism. -/
def reducedExteriorMap (f : LieHom R L K) :
    ReducedExteriorSquare R L →ₗ[R] ReducedExteriorSquare R K :=
  (thirdBoundaries R L).mapQ (thirdBoundaries R K)
    (exteriorPower.map 2 f.toLinearMap)
    (map_thirdBoundaries (R := R) (L := L) (K := K) f)

@[simp]
theorem reducedExteriorMap_class (f : LieHom R L K) (x : ⋀[R]^2 L) :
    reducedExteriorMap (R := R) (L := L) (K := K) f (reducedClass R L x) =
      reducedClass R K (exteriorPower.map 2 f.toLinearMap x) :=
  Submodule.mapQ_apply _ _ _ x

@[simp]
theorem reducedExteriorMap_wedge (f : LieHom R L K) (x y : L) :
    reducedExteriorMap (R := R) (L := L) (K := K) f (reducedWedge R L x y) =
      reducedWedge R K (f x) (f y) := by
  rw [reducedWedge_apply, reducedExteriorMap_class, reducedWedge_apply,
    exteriorPower.map_apply_ιMulti]
  congr 2

theorem reducedBracket_natural (f : LieHom R L K) :
    f.toLinearMap.comp (reducedBracket R L) =
      (reducedBracket R K).comp (reducedExteriorMap (R := R) (L := L) (K := K) f) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    change f.toLinearMap (reducedBracket R L (reducedClass R L x)) =
      reducedBracket R K
        (reducedExteriorMap (R := R) (L := L) (K := K) f (reducedClass R L x))
    rw [reducedBracket_class, reducedExteriorMap_class, reducedBracket_class]
    exact LinearMap.congr_fun (bracketMap_natural R f) x

/-- The map between the kernels of the reduced brackets induced by a Lie homomorphism. -/
def reducedBracketKernelMap (f : LieHom R L K) :
    LinearMap.ker (reducedBracket R L) →ₗ[R]
      LinearMap.ker (reducedBracket R K) where
  toFun z := ⟨reducedExteriorMap (R := R) (L := L) (K := K) f z, by
    calc
      reducedBracket R K (reducedExteriorMap (R := R) (L := L) (K := K) f z) =
          f (reducedBracket R L z) :=
        (LinearMap.congr_fun (reducedBracket_natural R f) z).symm
      _ = 0 := by rw [z.property, map_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (reducedExteriorMap (R := R) (L := L) (K := K) f) x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul (reducedExteriorMap (R := R) (L := L) (K := K) f) r x.1

set_option maxHeartbeats 1000000 in
-- The statement compares maps between two nested cycles-and-boundaries quotients.
set_option synthInstance.maxHeartbeats 100000 in
-- Typeclass synthesis must unfold those nested quotient modules in two different universes.
/-- Naturality of the standard identification `H₂ ≃ ker(Λ̃²L → L)`. -/
theorem secondHomologyEquivReducedBracketKernel_natural (f : LieHom R L K) :
    (secondHomologyEquivReducedBracketKernel R K).toLinearMap.comp
        (secondHomologyMap f) =
      (reducedBracketKernelMap (R := R) (L := L) (K := K) f).comp
        (secondHomologyEquivReducedBracketKernel R L).toLinearMap := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      change secondHomologyEquivReducedBracketKernel R K
          (secondHomologyMap f (Submodule.Quotient.mk z)) =
        reducedBracketKernelMap (R := R) (L := L) (K := K) f
          (secondHomologyEquivReducedBracketKernel R L (Submodule.Quotient.mk z))
      rw [show secondHomologyMap f (Submodule.Quotient.mk z) =
            (Submodule.Quotient.mk (secondCyclesMap f z) : SecondHomology R K) by rfl,
        show secondHomologyEquivReducedBracketKernel R K
            (Submodule.Quotient.mk (secondCyclesMap f z)) =
              cyclesToReducedBracketKernel R K (secondCyclesMap f z) by rfl,
        show secondHomologyEquivReducedBracketKernel R L (Submodule.Quotient.mk z) =
              cyclesToReducedBracketKernel R L z by rfl]
      apply Subtype.ext
      exact (reducedExteriorMap_class (R := R) (L := L) (K := K) f z).symm

end

end LieRings.Homological.LieHomology
