import LieRings.Homological.LieHomology.ReducedExteriorSquare
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Universal property of the reduced exterior square

The reduced exterior square represents alternating bilinear maps satisfying the
Chevalley--Eilenberg degree-three relation.  This file packages that universal property in the
form needed by the presentation proof of the Hopf formula.
-/

universe u v w

namespace LieRings.Homological.LieHomology

noncomputable section

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- An alternating map on two variables obtained from an alternating curried bilinear map. -/
private def alternatingMapTwo (f : L →ₗ[R] L →ₗ[R] M) (hf : f.IsAlt) :
    L [⋀^Fin 2]→ₗ[R] M where
  toFun v := f (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp
  map_update_smul' := by
    intro _ v i r x
    fin_cases i <;> simp
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have hij' : v 0 = v 1 := by simpa using hij
      rw [hij']
      exact hf (v 1)
    · have hij' : v 1 = v 0 := by simpa using hij
      rw [← hij']
      exact hf (v 1)
    · exact (hne rfl).elim

/-- The map on the ordinary exterior square represented by an alternating bilinear map. -/
private def exteriorLiftTwo (f : L →ₗ[R] L →ₗ[R] M) (hf : f.IsAlt) :
    (⋀[R]^2 L) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv (alternatingMapTwo R L f hf)

@[simp]
private theorem exteriorLiftTwo_ιMulti (f : L →ₗ[R] L →ₗ[R] M) (hf : f.IsAlt)
    (x y : L) :
    exteriorLiftTwo R L f hf (exteriorPower.ιMulti R 2 ![x, y]) = f x y := by
  rw [exteriorLiftTwo, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private theorem exteriorLiftTwo_differential (f : L →ₗ[R] L →ₗ[R] M)
    (hf : f.IsAlt)
    (hleibniz : ∀ x y z : L,
      f x ⁅y, z⁆ = f ⁅x, y⁆ z + f y ⁅x, z⁆)
    (c : ⋀[R]^3 L) :
    exteriorLiftTwo R L f hf (differential R L 2 c) = 0 := by
  have hc : c ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 3)) := by
    rw [exteriorPower.ιMulti_span R 3 L]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun c _ => exteriorLiftTwo R L f hf (differential R L 2 c) = 0)
    ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨v, rfl⟩
    have hv : v = ![v 0, v 1, v 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    have hd : differential R L 2 (exteriorPower.ιMulti R 3 ![v 0, v 1, v 2]) =
        -exteriorPower.ιMulti R 2 ![⁅v 0, v 1⁆, v 2] +
          exteriorPower.ιMulti R 2 ![⁅v 0, v 2⁆, v 1] -
            exteriorPower.ιMulti R 2 ![⁅v 1, v 2⁆, v 0] := by
      apply Subtype.ext
      simpa [ExteriorAlgebra.ιMulti_succ_apply] using
        differential_two_ιMulti_coe R L (v 0) (v 1) (v 2)
    rw [hd, map_sub, map_add, map_neg,
      exteriorLiftTwo_ιMulti, exteriorLiftTwo_ιMulti,
      exteriorLiftTwo_ιMulti]
    rw [← hf.neg (v 1) ⁅v 0, v 2⁆, ← hf.neg (v 0) ⁅v 1, v 2⁆,
      hleibniz (v 0) (v 1) (v 2)]
    abel
  · change exteriorLiftTwo R L f hf (differential R L 2 0) = 0
    rw [map_zero, map_zero]
  · intro a b _ _ ha hb
    rw [map_add, map_add, ha, hb, add_zero]
  · intro r a _ ha
    rw [map_smul, map_smul, ha, smul_zero]

private theorem exteriorLiftTwo_eq_zero_of_mem_thirdBoundaries
    (f : L →ₗ[R] L →ₗ[R] M)
    (hf : f.IsAlt)
    (hleibniz : ∀ x y z : L,
      f x ⁅y, z⁆ = f ⁅x, y⁆ z + f y ⁅x, z⁆)
    {x : ⋀[R]^2 L} (hx : x ∈ thirdBoundaries R L) :
    exteriorLiftTwo R L f hf x = 0 := by
  obtain ⟨c, rfl⟩ := hx
  exact exteriorLiftTwo_differential R L f hf hleibniz c

/-- Universal lift out of the reduced exterior square.  The two hypotheses say precisely that
`f` is alternating and that it kills the degree-three CE boundaries. -/
def reducedExteriorLift (f : L →ₗ[R] L →ₗ[R] M) (hf : f.IsAlt)
    (hleibniz : ∀ x y z : L,
      f x ⁅y, z⁆ = f ⁅x, y⁆ z + f y ⁅x, z⁆) :
    ReducedExteriorSquare R L →ₗ[R] M :=
  { QuotientAddGroup.lift (thirdBoundaries R L).toAddSubgroup
      (exteriorLiftTwo R L f hf).toAddMonoidHom
      (fun x hx => exteriorLiftTwo_eq_zero_of_mem_thirdBoundaries
        R L f hf hleibniz hx) with
    map_smul' := by
      intro r z
      induction z using Quotient.inductionOn with
      | _ x => exact map_smul (exteriorLiftTwo R L f hf) r x }

@[simp]
theorem reducedExteriorLift_wedge (f : L →ₗ[R] L →ₗ[R] M) (hf : f.IsAlt)
    (hleibniz : ∀ x y z : L,
      f x ⁅y, z⁆ = f ⁅x, y⁆ z + f y ⁅x, z⁆)
    (x y : L) :
    reducedExteriorLift R L f hf hleibniz (reducedWedge R L x y) = f x y := by
  change exteriorLiftTwo R L f hf (exteriorPower.ιMulti R 2 ![x, y]) = f x y
  exact exteriorLiftTwo_ιMulti R L f hf x y

/-- Linear maps out of the reduced exterior square are determined by pure reduced wedges. -/
theorem reducedExteriorMap_ext {N : Type w} [AddCommGroup N] [Module R N]
    {g h : ReducedExteriorSquare R L →ₗ[R] N}
    (hwedge : ∀ x y : L, g (reducedWedge R L x y) = h (reducedWedge R L x y)) :
    g = h := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ c =>
      change g (reducedClass R L c) = h (reducedClass R L c)
      have heq : g.comp (reducedClass R L) = h.comp (reducedClass R L) := by
        rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
          (exteriorPower.ιMulti_span R 2 L)]
        rintro ⟨x, hx⟩
        obtain ⟨v, rfl⟩ := hx
        have hv : v = ![v 0, v 1] := by
          funext i
          fin_cases i <;> rfl
        rw [hv, LinearMap.comp_apply, LinearMap.comp_apply]
        exact hwedge (v 0) (v 1)
      exact LinearMap.congr_fun heq c

end

end LieRings.Homological.LieHomology
