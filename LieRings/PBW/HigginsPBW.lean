import LieRings.PBW.HigginsDirectLimit

/-!
# Universality of Higgins's concrete commutator structure

This file turns the vanishing of Higgins's Baer obstruction into the universality of the
concrete commutator Lie structure.  The subsequent filtered Birkhoff--Witt comparison with the
defining ideal of the universal enveloping algebra is a separate step.
-/

namespace LieRings.PBW.Higgins

universe u

noncomputable section

variable (M : Type u) [AddCommGroup M]

/-- Higgins's canonical structure `C(M)` has its full universal property. -/
theorem universalLieStructure_isUniversal :
    letI := universalLieCarrierModuleOverTensor M
    letI := universalLieCarrierModuleOverTensorOpposite M
    letI := universalLieCarrierSMulCommClass M
    LieStructure.IsUniversal M (universalLieStructure M) := by
  letI := universalLieCarrierModuleOverTensor M
  letI := universalLieCarrierModuleOverTensorOpposite M
  letI := universalLieCarrierSMulCommClass M
  intro A _ _ _ _ _ target
  have hmodule : (inferInstance : Module ℤ A) = AddCommGroup.toIntModule A :=
    Subsingleton.elim _ _
  cases hmodule
  letI : LinearOrder M := WellOrderingRel.isWellOrder.linearOrder
  let f := universalLieStructureLift M target
  refine ⟨f, fun g ↦ ?_⟩
  exact universalLieStructure_hom_unique M target g f

/-- If `B(M)=0`, Higgins's concrete commutator ideal `K(M)` is the universal Lie structure over
`M`.  This is implication `(i) → (ii)` in Higgins's Theorem 5. -/
theorem tensorCommutatorLieStructure_isUniversal_of_obstructionVanishes
    (hB : ObstructionVanishes M) :
    letI := tensorCommutatorIdealSMulCommClass M
    LieStructure.IsUniversal M (tensorCommutatorLieStructure M) := by
  letI := tensorCommutatorIdealSMulCommClass M
  intro A _ _ _ _ _ target
  have hmodule : (inferInstance : Module ℤ A) = AddCommGroup.toIntModule A :=
    Subsingleton.elim _ _
  cases hmodule
  letI := universalLieCarrierModuleOverTensor M
  letI := universalLieCarrierModuleOverTensorOpposite M
  letI := universalLieCarrierSMulCommClass M
  let e := universalCommutatorEquivOfObstructionVanishes M hB
  obtain ⟨f, hf⟩ := universalLieStructure_isUniversal M A target
  let g : LieStructure.Hom M (tensorCommutatorLieStructure M) target :=
    { toLinearMap :=
        { toFun := fun k ↦ f (e.symm k)
          map_add' := by intro x y; simp
          map_smul' := by
            intro a k
            rw [show e.symm (a • k) = a • e.symm k by
              apply e.injective
              calc
                e (e.symm (a • k)) = a • k := e.apply_symm_apply _
                _ = a • e (e.symm k) :=
                  congrArg (a • ·) (e.apply_symm_apply k).symm
                _ = e (a • e.symm k) :=
                  (universalCommutatorEquivOfObstructionVanishes_smul_left
                    M hB a (e.symm k)).symm]
            exact map_smul f.toLinearMap a (e.symm k) }
      map_smul_right := by
        intro a k
        change f (e.symm (a • k)) = a • f (e.symm k)
        rw [show e.symm (a • k) = a • e.symm k by
          apply e.injective
          calc
            e (e.symm (a • k)) = a • k := e.apply_symm_apply _
            _ = a • e (e.symm k) :=
              congrArg (a • ·) (e.apply_symm_apply k).symm
            _ = e (a • e.symm k) :=
              (universalCommutatorEquivOfObstructionVanishes_smul_right
                M hB a (e.symm k)).symm]
        exact f.map_smul_right a (e.symm k)
      map_bracket := by
        intro x y
        change f (e.symm (tensorCommutatorBracket M x y)) = target.bracket x y
        have hinv : e.symm (tensorCommutatorBracket M x y) =
            universalLieBracket M x y := by
          apply e.injective
          calc
            e (e.symm (tensorCommutatorBracket M x y)) =
                tensorCommutatorBracket M x y := e.apply_symm_apply _
            _ = e (universalLieBracket M x y) :=
              (universalCommutatorEquivOfObstructionVanishes_bracket M hB x y).symm
        rw [hinv]
        exact f.map_bracket x y }
  refine ⟨g, fun g' ↦ ?_⟩
  apply LieStructure.Hom.ext
  apply LinearMap.ext
  intro k
  obtain ⟨c, rfl⟩ := e.surjective k
  let hcomp : LieStructure.Hom M (universalLieStructure M) target :=
    { toLinearMap :=
        { toFun := fun c ↦ g' (e c)
          map_add' := by intro x y; simp
          map_smul' := by
            intro a c
            change g' (e (a • c)) = a • g' (e c)
            rw [universalCommutatorEquivOfObstructionVanishes_smul_left]
            exact map_smul g'.toLinearMap a (e c) }
      map_smul_right := by
        intro a c
        change g' (e (a • c)) = a • g' (e c)
        rw [universalCommutatorEquivOfObstructionVanishes_smul_right]
        exact g'.map_smul_right a (e c)
      map_bracket := by
        intro x y
        change g' (e (universalLieBracket M x y)) = target.bracket x y
        rw [universalCommutatorEquivOfObstructionVanishes_bracket]
        exact g'.map_bracket x y }
  have hu := hf hcomp
  change g' (e c) = f (e.symm (e c))
  rw [e.symm_apply_apply]
  have huc := congrArg (fun q ↦ q c) hu
  have hcomp_apply : hcomp c = g' (e c) := rfl
  exact hcomp_apply.symm.trans huc

/-- Over `ℤ`, the concrete commutator Lie structure is universal for every Abelian group. -/
theorem tensorCommutatorLieStructure_isUniversal :
    letI := tensorCommutatorIdealSMulCommClass M
    LieStructure.IsUniversal M (tensorCommutatorLieStructure M) :=
  tensorCommutatorLieStructure_isUniversal_of_obstructionVanishes M
    (obstructionVanishes_all M)

end

end LieRings.PBW.Higgins
