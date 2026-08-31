import LieRings.UniversalEnveloping.Adjoint
import Mathlib.Algebra.Lie.SemiDirect

/-!
# The coinduced module used in central separation

For a Lie ring `H` and an abelian group `D`, the coinduced module is
`Hom_ℤ(U(H), D)`, with `(x • α)(u) = α(u x)`.  Evaluation at `1` identifies maps into this
module with additive maps, and therefore turns an additive retraction into the extension theorem
needed in the Plotkin argument.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v w

variable (H : Type u) [LieRing H]
variable (D : Type v) [AddCommGroup D]

/-- The coinduced `H`-module with values in `D`. -/
abbrev Coinduced := UEA ℤ H →ₗ[ℤ] D

namespace Coinduced

/-- The additive group underlying a coinduced module has the zero internal Lie bracket. -/
instance zeroLieRing : LieRing (Coinduced H D) where
  bracket _ _ := 0
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

/-- Right translation by a Lie generator. -/
def generatorAction (x : H) : Module.End ℤ (Coinduced H D) where
  toFun α :=
    { toFun := fun u ↦ α (u * UniversalEnvelopingAlgebra.ι ℤ x)
      map_add' := fun u v ↦ by rw [add_mul, map_add]
      map_smul' := fun z u ↦ by
        rw [smul_mul_assoc]
        simpa only [RingHom.id_apply] using
          (map_smul α z (u * UniversalEnvelopingAlgebra.ι ℤ x)) }
  map_add' α β := by ext u; simp
  map_smul' z α := by ext u; simp

@[simp]
theorem generatorAction_apply (x : H) (α : Coinduced H D) (u : UEA ℤ H) :
    generatorAction H D x α u =
      α (u * UniversalEnvelopingAlgebra.ι ℤ x) :=
  rfl

instance lieRingModule : LieRingModule H (Coinduced H D) where
  bracket x α := generatorAction H D x α
  add_lie x y α := by
    ext u
    change α (u * UniversalEnvelopingAlgebra.ι ℤ (x + y)) =
      α (u * UniversalEnvelopingAlgebra.ι ℤ x) +
        α (u * UniversalEnvelopingAlgebra.ι ℤ y)
    rw [map_add, mul_add, map_add]
  lie_add x α β := by ext u; rfl
  leibniz_lie x y α := by
    ext u
    change α ((u * UniversalEnvelopingAlgebra.ι ℤ x) *
          UniversalEnvelopingAlgebra.ι ℤ y) =
      α (u * UniversalEnvelopingAlgebra.ι ℤ ⁅x, y⁆) +
        α ((u * UniversalEnvelopingAlgebra.ι ℤ y) *
          UniversalEnvelopingAlgebra.ι ℤ x)
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
    simp only [mul_sub, map_sub, mul_assoc]
    abel

instance lieModule : LieModule ℤ H (Coinduced H D) where
  smul_lie z x α := by
    ext u
    change α (u * UniversalEnvelopingAlgebra.ι ℤ (z • x)) =
      z • α (u * UniversalEnvelopingAlgebra.ι ℤ x)
    rw [map_smul, mul_smul_comm, map_smul]
  lie_smul z x α := by ext u; rfl

@[simp]
theorem lie_apply (x : H) (α : Coinduced H D) (u : UEA ℤ H) :
    ⁅x, α⁆ u = α (u * UniversalEnvelopingAlgebra.ι ℤ x) :=
  rfl

/-- The coinduced action, regarded as an action by derivations of the abelian Lie ring. -/
def derivationAction : H →ₗ⁅ℤ⁆ LieDerivation ℤ (Coinduced H D) (Coinduced H D) where
  toFun x :=
    { toLinearMap := generatorAction H D x
      leibniz' := by
        intro α β
        change generatorAction H D x 0 = 0 - 0
        simp }
  map_add' x y := by
    ext α u
    change α (u * UniversalEnvelopingAlgebra.ι ℤ (x + y)) =
      α (u * UniversalEnvelopingAlgebra.ι ℤ x) +
        α (u * UniversalEnvelopingAlgebra.ι ℤ y)
    rw [map_add, mul_add, map_add]
  map_smul' z x := by
    ext α u
    change α (u * UniversalEnvelopingAlgebra.ι ℤ (z • x)) =
      z • α (u * UniversalEnvelopingAlgebra.ι ℤ x)
    rw [map_smul, mul_smul_comm, map_smul]
  map_lie' {x y} := by
    ext α u
    change α (u * UniversalEnvelopingAlgebra.ι ℤ ⁅x, y⁆) =
      α ((u * UniversalEnvelopingAlgebra.ι ℤ x) *
          UniversalEnvelopingAlgebra.ι ℤ y) -
        α ((u * UniversalEnvelopingAlgebra.ι ℤ y) *
          UniversalEnvelopingAlgebra.ι ℤ x)
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
    simp only [mul_sub, map_sub, mul_assoc]

@[simp]
theorem derivationAction_apply (x : H) (α : Coinduced H D) (u : UEA ℤ H) :
    derivationAction H D x α u =
      α (u * UniversalEnvelopingAlgebra.ι ℤ x) :=
  rfl

/-- The full enveloping-algebra action is right translation. -/
theorem representation_apply (a : UEA ℤ H) (α : Coinduced H D) (u : UEA ℤ H) :
    UEA.representation ℤ H (Coinduced H D) a α u = α (u * a) := by
  induction a using UEA.induction ℤ H generalizing α u with
  | algebraMap z =>
      rw [UEA.representation_algebraMap_apply]
      calc
        (z • α) u = z • α u := rfl
        _ = α (z • u) := (map_smul α z u).symm
        _ = α (algebraMap ℤ (UEA ℤ H) z * u) := by
          congr 1
        _ = α (u * algebraMap ℤ (UEA ℤ H) z) := by
          rw [Algebra.commutes z u]
  | ι x =>
    rw [UEA.representation_ι_apply, lie_apply]
  | mul a b ha hb =>
      rw [UEA.representation_mul_apply, ha, hb, mul_assoc]
  | add a b ha hb =>
      rw [map_add]
      change UEA.representation ℤ H (Coinduced H D) a α u +
          UEA.representation ℤ H (Coinduced H D) b α u = α (u * (a + b))
      rw [ha, hb, mul_add, map_add]

/-- Evaluation at the unit of the enveloping algebra. -/
def evaluationOne : Coinduced H D →ₗ[ℤ] D where
  toFun α := α 1
  map_add' α β := by simp
  map_smul' z α := by simp

@[simp]
theorem evaluationOne_apply (α : Coinduced H D) :
    evaluationOne H D α = α 1 :=
  rfl

end Coinduced

section Extension

variable {H D}
variable (M : Type w) [AddCommGroup M] [Module ℤ M]
variable [LieRingModule H M] [LieModule ℤ H M]

/-- A morphism of Lie modules commutes with the induced action of the enveloping algebra. -/
theorem LieModuleHom.map_representation
    {M' : Type*} [AddCommGroup M'] [Module ℤ M']
    [LieRingModule H M'] [LieModule ℤ H M']
    (f : M →ₗ⁅ℤ,H⁆ M') (u : UEA ℤ H) (m : M) :
    f (UEA.representation ℤ H M u m) =
      UEA.representation ℤ H M' u (f m) := by
  induction u using UEA.induction ℤ H generalizing m with
  | algebraMap z => simp
  | ι x =>
      rw [UEA.representation_ι_apply, UEA.representation_ι_apply]
      exact f.map_lie x m
  | mul u v hu hv =>
      rw [UEA.representation_mul_apply, UEA.representation_mul_apply,
        hu, hv]
  | add u v hu hv =>
      rw [map_add, map_add]
      change f (UEA.representation ℤ H M u m +
          UEA.representation ℤ H M v m) =
        UEA.representation ℤ H M' u (f m) +
          UEA.representation ℤ H M' v (f m)
      rw [map_add, hu, hv]

variable (N : LieSubmodule ℤ H M)

/-- The additive functional obtained from a map to the coinduced module and an additive
retraction. -/
def extensionFunctional
    (retraction : M →ₗ[ℤ] N)
    (f : N →ₗ⁅ℤ,H⁆ Coinduced H D) : M →ₗ[ℤ] D :=
  (Coinduced.evaluationOne H D).comp (f.toLinearMap.comp retraction)

/-- Extend a module map from an additively split Lie submodule to the whole module. -/
def extend
    (retraction : M →ₗ[ℤ] N)
    (f : N →ₗ⁅ℤ,H⁆ Coinduced H D) : M →ₗ⁅ℤ,H⁆ Coinduced H D where
  toFun m :=
    { toFun := fun u ↦ extensionFunctional M N retraction f
          (UEA.representation ℤ H M u m)
      map_add' := fun u v ↦ by simp
      map_smul' := fun z u ↦ by simp }
  map_add' m n := by ext u; simp
  map_smul' z m := by ext u; simp
  map_lie' {x m} := by
    ext u
    change extensionFunctional M N retraction f
        (UEA.representation ℤ H M u ⁅x, m⁆) =
      extensionFunctional M N retraction f
        (UEA.representation ℤ H M
          (u * UniversalEnvelopingAlgebra.ι ℤ x) m)
    rw [UEA.representation_mul_apply, UEA.representation_ι_apply]

@[simp]
theorem extend_apply (retraction : M →ₗ[ℤ] N)
    (f : N →ₗ⁅ℤ,H⁆ Coinduced H D) (m : M) (u : UEA ℤ H) :
    extend M N retraction f m u =
      extensionFunctional M N retraction f
        (UEA.representation ℤ H M u m) :=
  rfl

/-- The preceding construction really extends the original map when the additive map is a
retraction of the inclusion. -/
theorem extend_restricts
    (retraction : M →ₗ[ℤ] N)
    (hretraction : ∀ n : N, retraction n = n)
    (f : N →ₗ⁅ℤ,H⁆ Coinduced H D) (n : N) :
    extend M N retraction f n = f n := by
  ext u
  rw [extend_apply]
  change f (retraction (UEA.representation ℤ H M u (n : M))) 1 = f n u
  let restrict : UEA ℤ H → N → N := fun a m ↦
    ⟨UEA.representation ℤ H M a (m : M),
      UEA.representation_mem ℤ H M N a m.property⟩
  have hnatural (a : UEA ℤ H) (m : N) :
      f (restrict a m) = UEA.representation ℤ H (Coinduced H D) a (f m) := by
    induction a using UEA.induction ℤ H generalizing m with
    | algebraMap z =>
        rw [show restrict (algebraMap ℤ (UEA ℤ H) z) m = z • m by
          ext
          simp [restrict], UEA.representation_algebraMap_apply]
        exact map_smul f z m
    | ι x =>
        rw [show restrict (UniversalEnvelopingAlgebra.ι ℤ x) m = ⁅x, m⁆ by
          ext
          exact UEA.representation_ι_apply ℤ H M x (m : M),
          UEA.representation_ι_apply]
        exact f.map_lie x m
    | mul a b ha hb =>
        rw [show restrict (a * b) m = restrict a (restrict b m) by
          ext
          simp [restrict, UEA.representation_mul_apply],
          UEA.representation_mul_apply]
        rw [ha, hb]
    | add a b ha hb =>
        rw [show restrict (a + b) m = restrict a m + restrict b m by
          ext
          simp [restrict], map_add]
        rw [map_add, ha, hb]
        rfl
  change f (retraction (restrict u n : M)) 1 = f n u
  rw [hretraction, hnatural, Coinduced.representation_apply]
  simp

end Extension

end

end LieRings.Plotkin
