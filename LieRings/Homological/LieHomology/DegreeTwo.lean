import LieRings.Homological.LieHomology.LowDegree

/-!
# The concrete second Chevalley--Eilenberg homology module

For trivial coefficients, the second homology is

`ker (d₂ : ⋀²L → ⋀¹L) / im (d₃ : ⋀³L → ⋀²L)`.

The definitions below expose exactly that quotient while
`secondHomologyConcreteIso` proves that it is the degree-two homology of the all-degree chain
complex.  This is the concrete interface used by the Hopf-formula proof.
-/

open CategoryTheory

universe u v w

namespace LieRings.Homological.LieHomology

noncomputable section

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The two-cycles in the Chevalley--Eilenberg complex. -/
abbrev secondCycles : Submodule R (⋀[R]^2 L) :=
  LinearMap.ker (differential R L 1)

/-- The third differential with codomain restricted to the module of two-cycles. -/
def thirdBoundaryToCycles : (⋀[R]^3 L) →ₗ[R] secondCycles R L :=
  (differential R L 2).codRestrict _ (fun x => by
    change differential R L 1 (differential R L 2 x) = 0
    exact LinearMap.congr_fun (differential_comp_differential R L 1) x)

@[simp]
theorem thirdBoundaryToCycles_coe (x : ⋀[R]^3 L) :
    (thirdBoundaryToCycles R L x : ⋀[R]^2 L) = differential R L 2 x := rfl

/-- The concrete cycles-modulo-boundaries model of second CE homology. -/
abbrev SecondHomology : Type (max u v) :=
  secondCycles R L ⧸ LinearMap.range (thirdBoundaryToCycles R L)

/-- The abstract degree-two homology of `complex R L` is its usual
`ker d₂ / im d₃` quotient. -/
noncomputable def secondHomologyConcreteIso :
    homology (R := R) (L := L) 2 ≅ ModuleCat.of R (SecondHomology R L) :=
  (complex R L).homologyIsoSc' 3 2 1
      (by simpa using ChainComplex.prev ℕ 2)
      (by simpa using ChainComplex.next_nat_succ 1) ≪≫
    ((complex R L).sc' 3 2 1).moduleCatHomologyIso

/-- A two-chain represents a second-homology class precisely when it is a cycle. -/
def secondHomologyClass : secondCycles R L →ₗ[R] SecondHomology R L :=
  (LinearMap.range (thirdBoundaryToCycles R L)).mkQ

@[simp]
theorem secondHomologyClass_eq_zero_iff (z : secondCycles R L) :
    secondHomologyClass R L z = 0 ↔
      z ∈ LinearMap.range (thirdBoundaryToCycles R L) :=
  by
    change (Submodule.Quotient.mk z : SecondHomology R L) = 0 ↔ _
    exact Submodule.Quotient.mk_eq_zero _

/-! ## Functoriality of the concrete model -/

variable {R L}
variable {K : Type w} [LieRing K] [LieAlgebra R K]

/-- The map on two-cycles induced by a Lie homomorphism. -/
def secondCyclesMap (f : LieHom R L K) : secondCycles R L →ₗ[R] secondCycles R K where
  toFun z := ⟨exteriorPower.map 2 f.toLinearMap z, by
    change differential R K 1 (exteriorPower.map 2 f.toLinearMap z) = 0
    rw [← differential_natural_apply R L f 1 z, z.property, map_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (exteriorPower.map 2 f.toLinearMap) x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul (exteriorPower.map 2 f.toLinearMap) r x.1

@[simp]
theorem secondCyclesMap_coe (f : LieHom R L K) (z : secondCycles R L) :
    (secondCyclesMap f z : ⋀[R]^2 K) = exteriorPower.map 2 f.toLinearMap z :=
  rfl

private theorem map_secondBoundaries (f : LieHom R L K) :
    LinearMap.range (thirdBoundaryToCycles R L) ≤
      (LinearMap.range (thirdBoundaryToCycles R K)).comap (secondCyclesMap f) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨exteriorPower.map 3 f.toLinearMap x, ?_⟩
  apply Subtype.ext
  exact (differential_natural_apply R L f 2 x).symm

/-- The map on the concrete second Chevalley--Eilenberg homology induced by a Lie
homomorphism. -/
def secondHomologyMap (f : LieHom R L K) :
    SecondHomology R L →ₗ[R] SecondHomology R K :=
  (LinearMap.range (thirdBoundaryToCycles R L)).mapQ
    (LinearMap.range (thirdBoundaryToCycles R K)) (secondCyclesMap f)
    (map_secondBoundaries f)

@[simp]
theorem secondHomologyMap_class (f : LieHom R L K) (z : secondCycles R L) :
    secondHomologyMap f (secondHomologyClass R L z) =
      secondHomologyClass R K (secondCyclesMap f z) :=
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Elaborating equality of the nested cycles-and-boundaries quotients needs extra synthesis time.
@[simp]
theorem secondHomologyMap_id :
    secondHomologyMap (LieHom.id : LieHom R L L) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
      change Submodule.Quotient.mk (secondCyclesMap
        (LieHom.id : LieHom R L L) z) = Submodule.Quotient.mk z
      apply congrArg (fun x : secondCycles R L =>
        (Submodule.Quotient.mk x : SecondHomology R L))
      apply Subtype.ext
      rw [secondCyclesMap_coe]
      change exteriorPower.map 2 (LinearMap.id : L →ₗ[R] L) z.1 = z.1
      rw [exteriorPower.map_id]
      rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Elaborating equality of the nested cycles-and-boundaries quotients needs extra synthesis time.
theorem secondHomologyMap_comp
    {M : Type*} [LieRing M] [LieAlgebra R M]
    (f : LieHom R L K) (g : LieHom R K M) :
    secondHomologyMap (g.comp f) =
      (secondHomologyMap g).comp (secondHomologyMap f) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
      change Submodule.Quotient.mk (secondCyclesMap (g.comp f) z) =
        Submodule.Quotient.mk (secondCyclesMap g (secondCyclesMap f z))
      apply congrArg (fun x : secondCycles R M =>
        (Submodule.Quotient.mk x : SecondHomology R M))
      apply Subtype.ext
      simp only [secondCyclesMap_coe]
      change exteriorPower.map 2 (g.toLinearMap.comp f.toLinearMap) z =
        exteriorPower.map 2 g.toLinearMap (exteriorPower.map 2 f.toLinearMap z)
      rw [exteriorPower.map_comp]
      rfl

end

end LieRings.Homological.LieHomology
