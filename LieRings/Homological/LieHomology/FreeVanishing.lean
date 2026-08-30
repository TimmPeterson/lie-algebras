import LieRings.Homological.LieHomology.ReducedExteriorSquare
import Mathlib.Algebra.Lie.Free

/-!
# Second homology of a free Lie algebra

This file proves directly that the bracket

`Λ̃²(FreeLieAlgebra R X) → [FreeLieAlgebra R X, FreeLieAlgebra R X]`

is an isomorphism.  The inverse is constructed on Mathlib's presentation of the free Lie algebra
as a quotient of the free non-unital non-associative algebra.  A formal product `a * b` is sent to
the reduced wedge of the classes of `a` and `b`; the defining Leibniz relation descends precisely
because it is the degree-three Chevalley--Eilenberg boundary relation.
-/

universe u v

namespace LieRings.Homological.LieHomology

noncomputable section

variable (R : Type u) (X : Type v) [CommRing R]

private abbrev F := FreeLieAlgebra R X
private abbrev Raw := FreeNonUnitalNonAssocAlgebra R X

/-- Convolution multiplication on the raw free non-associative algebra.  This is named explicitly
because importing exterior powers also exposes the unrelated pointwise multiplication on the
underlying `Finsupp`. -/
private def rawProduct (a b : Raw R X) : Raw R X :=
  @Mul.mul (Raw R X) MonoidAlgebra.instMul a b

/-- The additive constructors used by `Finsupp.induction_linear`.  Naming them lets the proof
cross the reducible-abbreviation boundary without asking unification to identify two inherited
copies of the same additive structure. -/
private def rawFinsuppZero : Raw R X :=
  @Zero.zero (FreeMagma X →₀ R) (@Finsupp.instZero (FreeMagma X) R inferInstance)

private def rawFinsuppAdd (a b : Raw R X) : Raw R X :=
  @Add.add (FreeMagma X →₀ R) (@Finsupp.instAdd (FreeMagma X) R inferInstance) a b

private theorem rawFinsuppZero_eq : rawFinsuppZero R X = (0 : Raw R X) := rfl

private theorem rawFinsuppAdd_eq (a b : Raw R X) : rawFinsuppAdd R X a b = a + b := rfl

private theorem mk_finsupp_zero :
    FreeLieAlgebra.mk R (rawFinsuppZero R X) = 0 := by
  rw [rawFinsuppZero_eq R X]
  exact map_zero (FreeLieAlgebra.mk R)

private theorem mk_finsupp_add (a b : Raw R X) :
    FreeLieAlgebra.mk R (rawFinsuppAdd R X a b) =
      FreeLieAlgebra.mk R a + FreeLieAlgebra.mk R b := by
  rw [rawFinsuppAdd_eq R X a b]
  exact map_add (FreeLieAlgebra.mk R) a b

private theorem rawProduct_zero_left (b : Raw R X) : rawProduct R X 0 b = 0 := by
  change MonoidAlgebra.mul' 0 b = 0
  exact @NonUnitalNonAssocSemiring.zero_mul (Raw R X)
    MonoidAlgebra.nonUnitalNonAssocSemiring b

private theorem rawProduct_add_left (a b c : Raw R X) :
    rawProduct R X (a + b) c = rawProduct R X a c + rawProduct R X b c := by
  change MonoidAlgebra.mul' (a + b) c =
    MonoidAlgebra.mul' a c + MonoidAlgebra.mul' b c
  exact @NonUnitalNonAssocSemiring.right_distrib (Raw R X)
    MonoidAlgebra.nonUnitalNonAssocSemiring a b c

private theorem rawProduct_zero_right (a : Raw R X) : rawProduct R X a 0 = 0 := by
  change MonoidAlgebra.mul' a 0 = 0
  exact @NonUnitalNonAssocSemiring.mul_zero (Raw R X)
    MonoidAlgebra.nonUnitalNonAssocSemiring a

private theorem rawProduct_add_right (a b c : Raw R X) :
    rawProduct R X a (b + c) = rawProduct R X a b + rawProduct R X a c := by
  change MonoidAlgebra.mul' a (b + c) =
    MonoidAlgebra.mul' a b + MonoidAlgebra.mul' a c
  exact @NonUnitalNonAssocSemiring.left_distrib (Raw R X)
    MonoidAlgebra.nonUnitalNonAssocSemiring a b c

private theorem rawProduct_finsupp_zero_left (b : Raw R X) :
    rawProduct R X (rawFinsuppZero R X) b = rawFinsuppZero R X := by
  rw [rawFinsuppZero_eq R X, rawProduct_zero_left R X b]

private theorem rawProduct_finsupp_add_left (a b c : Raw R X) :
    rawProduct R X (rawFinsuppAdd R X a b) c =
      rawFinsuppAdd R X (rawProduct R X a c) (rawProduct R X b c) := by
  rw [rawFinsuppAdd_eq R X a b, rawProduct_add_left R X a b c,
    rawFinsuppAdd_eq R X]

private theorem rawProduct_finsupp_zero_right (a : Raw R X) :
    rawProduct R X a (rawFinsuppZero R X) = rawFinsuppZero R X := by
  rw [rawFinsuppZero_eq R X, rawProduct_zero_right R X a]

private theorem rawProduct_finsupp_add_right (a b c : Raw R X) :
    rawProduct R X a (rawFinsuppAdd R X b c) =
      rawFinsuppAdd R X (rawProduct R X a b) (rawProduct R X a c) := by
  rw [rawFinsuppAdd_eq R X b c, rawProduct_add_right R X a b c,
    rawFinsuppAdd_eq R X]

private theorem rawProduct_single (a b : FreeMagma X) (r s : R) :
    rawProduct R X (MonoidAlgebra.single a r) (MonoidAlgebra.single b s) =
      MonoidAlgebra.single (a * b) (r * s) := by
  change @Mul.mul (Raw R X) MonoidAlgebra.instMul
    (MonoidAlgebra.single a r) (MonoidAlgebra.single b s) = _
  exact MonoidAlgebra.single_mul_single a b r s

/-- The class in the free Lie algebra of a single non-associative monomial. -/
private def treeToFree (t : FreeMagma X) : F R X :=
  FreeLieAlgebra.mk R (MonoidAlgebra.single t 1)

private theorem treeToFree_mul (a b : FreeMagma X) :
    treeToFree R X (a * b) = ⁅treeToFree R X a, treeToFree R X b⁆ := by
  change FreeLieAlgebra.mk R (MonoidAlgebra.single (a * b) 1) =
    FreeLieAlgebra.mk R (MonoidAlgebra.single a 1 * MonoidAlgebra.single b 1)
  rw [MonoidAlgebra.single_mul_single, one_mul]

private theorem mk_single (a : FreeMagma X) (r : R) :
    FreeLieAlgebra.mk R (MonoidAlgebra.single a r) = r • treeToFree R X a := by
  have h : MonoidAlgebra.single a r = r • MonoidAlgebra.single a (1 : R) := by
    ext t
    by_cases ht : t = a
    · subst ht
      simp
    · simp [ht]
  rw [h, map_smul]
  rfl

/-- The primitive attached to a non-associative monomial. -/
private def treePrimitive : FreeMagma X → ReducedExteriorSquare R (F R X)
  | .of _ => 0
  | .mul a b => reducedWedge R (F R X) (treeToFree R X a) (treeToFree R X b)

/-- Linear extension of `treePrimitive` to the free non-associative algebra. -/
private def rawPrimitive : Raw R X →ₗ[R] ReducedExteriorSquare R (F R X) :=
  Finsupp.linearCombination R (treePrimitive R X)

private theorem rawPrimitive_finsupp_zero :
    rawPrimitive R X (rawFinsuppZero R X) = 0 := by
  rw [rawFinsuppZero_eq R X]
  exact map_zero (rawPrimitive R X)

private theorem rawPrimitive_finsupp_add (a b : Raw R X) :
    rawPrimitive R X (rawFinsuppAdd R X a b) =
      rawPrimitive R X a + rawPrimitive R X b := by
  rw [rawFinsuppAdd_eq R X a b]
  exact map_add (rawPrimitive R X) a b

@[simp]
private theorem rawPrimitive_single (a : FreeMagma X) (r : R) :
    rawPrimitive R X (MonoidAlgebra.single a r) = r • treePrimitive R X a :=
  Finsupp.linearCombination_single R r a

/-- The raw primitive sends a product to the wedge of its two images in the free Lie algebra. -/
private theorem rawPrimitive_mul (a b : Raw R X) :
    rawPrimitive R X (rawProduct R X a b) =
      reducedWedge R (F R X) (FreeLieAlgebra.mk R a) (FreeLieAlgebra.mk R b) := by
  induction a using Finsupp.induction_linear with
  | zero =>
      change rawPrimitive R X (rawProduct R X (rawFinsuppZero R X) b) =
        reducedWedge R (F R X) (FreeLieAlgebra.mk R (rawFinsuppZero R X))
          (FreeLieAlgebra.mk R b)
      rw [rawProduct_finsupp_zero_left R X b, rawPrimitive_finsupp_zero R X,
        mk_finsupp_zero R X]
      exact (reducedWedge_zero_left R (F R X) _).symm
  | add a₁ a₂ ha₁ ha₂ =>
      change rawPrimitive R X (rawProduct R X (rawFinsuppAdd R X a₁ a₂) b) =
        reducedWedge R (F R X) (FreeLieAlgebra.mk R (rawFinsuppAdd R X a₁ a₂))
          (FreeLieAlgebra.mk R b)
      rw [rawProduct_finsupp_add_left R X a₁ a₂ b,
        rawPrimitive_finsupp_add R X, ha₁, ha₂, mk_finsupp_add R X]
      simpa only [LinearMap.add_apply] using congrArg
        (fun f : F R X →ₗ[R] ReducedExteriorSquare R (F R X) => f (FreeLieAlgebra.mk R b))
        (map_add (reducedWedge R (F R X)) (FreeLieAlgebra.mk R a₁)
          (FreeLieAlgebra.mk R a₂)).symm
  | single ta ra =>
      induction b using Finsupp.induction_linear with
      | zero =>
          change rawPrimitive R X
              (rawProduct R X (MonoidAlgebra.single ta ra) (rawFinsuppZero R X)) =
            reducedWedge R (F R X) (FreeLieAlgebra.mk R (MonoidAlgebra.single ta ra))
              (FreeLieAlgebra.mk R (rawFinsuppZero R X))
          rw [rawProduct_finsupp_zero_right R X,
            rawPrimitive_finsupp_zero R X, mk_finsupp_zero R X]
          exact (reducedWedge_zero_right R (F R X) _).symm
      | add b₁ b₂ hb₁ hb₂ =>
          change rawPrimitive R X
              (rawProduct R X (MonoidAlgebra.single ta ra) (rawFinsuppAdd R X b₁ b₂)) =
            reducedWedge R (F R X) (FreeLieAlgebra.mk R (MonoidAlgebra.single ta ra))
              (FreeLieAlgebra.mk R (rawFinsuppAdd R X b₁ b₂))
          rw [rawProduct_finsupp_add_right R X,
            rawPrimitive_finsupp_add R X, hb₁, hb₂, mk_finsupp_add R X]
          exact (map_add
            (reducedWedge R (F R X) (FreeLieAlgebra.mk R (MonoidAlgebra.single ta ra)))
            (FreeLieAlgebra.mk R b₁) (FreeLieAlgebra.mk R b₂)).symm
      | single tb rb =>
          rw [rawProduct_single R X ta tb ra rb, rawPrimitive_single]
          change (ra * rb) • reducedWedge R (F R X) (treeToFree R X ta)
              (treeToFree R X tb) =
            reducedWedge R (F R X)
              (FreeLieAlgebra.mk R (MonoidAlgebra.single ta ra))
              (FreeLieAlgebra.mk R (MonoidAlgebra.single tb rb))
          rw [mk_single, mk_single]
          rw [map_smul]
          rw [map_smul (reducedWedge R (F R X)) ra (treeToFree R X ta),
            LinearMap.smul_apply, smul_smul, mul_comm rb ra]

/-- The raw primitive respects every defining relation of the free Lie algebra. -/
private theorem rawPrimitive_rel {a b : Raw R X} (h : FreeLieAlgebra.Rel R X a b) :
    rawPrimitive R X a = rawPrimitive R X b := by
  induction h with
  | lie_self a =>
      change rawPrimitive R X (rawProduct R X a a) = rawPrimitive R X 0
      rw [rawPrimitive_mul R X a a, map_zero]
      exact reducedWedge_self R (F R X) _
  | leibniz_lie a b c =>
      rw [map_add]
      change rawPrimitive R X (rawProduct R X a (rawProduct R X b c)) =
        rawPrimitive R X (rawProduct R X (rawProduct R X a b) c) +
          rawPrimitive R X (rawProduct R X b (rawProduct R X a c))
      simp only [rawPrimitive_mul]
      let qa : F R X := Quot.mk _ a
      let qb : F R X := Quot.mk _ b
      let qc : F R X := Quot.mk _ c
      change reducedWedge R (F R X) qa ⁅qb, qc⁆ =
        reducedWedge R (F R X) ⁅qa, qb⁆ qc + reducedWedge R (F R X) qb ⁅qa, qc⁆
      exact reducedWedge_leibniz R (F R X) qa qb qc
  | smul r h ih => simpa only [map_smul] using congrArg (r • ·) ih
  | add_right c h ih => simpa only [map_add] using congrArg (· + rawPrimitive R X c) ih
  | mul_left a h ih =>
      change rawPrimitive R X (rawProduct R X a _) = rawPrimitive R X (rawProduct R X a _)
      rw [rawPrimitive_mul R X, rawPrimitive_mul R X]
      exact congrArg
        (fun q : F R X => reducedWedge R (F R X) (FreeLieAlgebra.mk R a) q)
        (Quot.sound h)
  | mul_right c h ih =>
      change rawPrimitive R X (rawProduct R X _ c) = rawPrimitive R X (rawProduct R X _ c)
      rw [rawPrimitive_mul R X, rawPrimitive_mul R X]
      exact congrArg
        (fun q : F R X => reducedWedge R (F R X) q (FreeLieAlgebra.mk R c))
        (Quot.sound h)

/-- The canonical primitive from the free Lie algebra to its reduced exterior square. -/
def freePrimitive : F R X →ₗ[R] ReducedExteriorSquare R (F R X) where
  toFun z := Quot.lift (rawPrimitive R X) (fun _ _ h => rawPrimitive_rel R X h) z
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    exact map_add (rawPrimitive R X) a b
  map_smul' := by
    intro r z
    induction z using Quot.inductionOn with
    | _ a => exact map_smul (rawPrimitive R X) r a

@[simp]
theorem freePrimitive_lie (a b : F R X) :
    freePrimitive R X ⁅a, b⁆ = reducedWedge R (F R X) a b := by
  induction a using Quot.inductionOn with
  | _ a =>
    induction b using Quot.inductionOn with
    | _ b => exact rawPrimitive_mul R X a b

@[simp]
theorem freePrimitive_of (x : X) :
    freePrimitive R X (FreeLieAlgebra.of R x) = 0 := by
  change rawPrimitive R X (FreeNonUnitalNonAssocAlgebra.of R x) = 0
  change rawPrimitive R X (MonoidAlgebra.single (FreeMagma.of x) 1) = 0
  rw [rawPrimitive_single]
  change (1 : R) • (0 : ReducedExteriorSquare R (F R X)) = 0
  exact one_smul R 0

/-- On a free Lie algebra, the primitive is a left inverse to the bracket on the reduced exterior
square.  This is the direct free-Lie calculation in the proof of the Hopf formula. -/
theorem freePrimitive_reducedBracket (z : ReducedExteriorSquare R (F R X)) :
    freePrimitive R X (reducedBracket R (F R X) z) = z := by
  have hpure :
      (freePrimitive R X).comp (bracketMap R (F R X)) = reducedClass R (F R X) := by
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (exteriorPower.ιMulti_span R 2 (F R X))]
    rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := hx
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    rw [LinearMap.comp_apply, bracketMap_ιMulti, freePrimitive_lie, reducedWedge_apply]
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
      change freePrimitive R X
          (reducedBracket R (F R X) (reducedClass R (F R X) x)) =
        reducedClass R (F R X) x
      rw [reducedBracket_class]
      exact LinearMap.congr_fun hpure x

/-- The reduced bracket of a free Lie algebra is injective. -/
theorem reducedBracket_free_injective :
    Function.Injective (reducedBracket R (F R X)) := by
  intro a b hab
  calc
    a = freePrimitive R X (reducedBracket R (F R X) a) :=
      (freePrimitive_reducedBracket R X a).symm
    _ = freePrimitive R X (reducedBracket R (F R X) b) := congrArg (freePrimitive R X) hab
    _ = b := freePrimitive_reducedBracket R X b

/-- The kernel model for second homology of a free Lie algebra is zero. -/
theorem reducedBracket_free_ker_eq_bot :
    LinearMap.ker (reducedBracket R (F R X)) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (reducedBracket_free_injective R X)

/-- The derived ideal of a free Lie algebra. -/
abbrev freeDerived : LieIdeal R (F R X) :=
  ⁅(⊤ : LieIdeal R (F R X)), (⊤ : LieIdeal R (F R X))⁆

private theorem reducedBracket_mem_freeDerived
    (z : ReducedExteriorSquare R (F R X)) :
    reducedBracket R (F R X) z ∈ freeDerived R X := by
  induction z using Submodule.Quotient.induction_on with
  | _ c =>
      change bracketMap R (F R X) c ∈ freeDerived R X
      have hc : c ∈ Submodule.span R
          (Set.range (exteriorPower.ιMulti R 2)) := by
        rw [exteriorPower.ιMulti_span R 2 (F R X)]
        exact Submodule.mem_top
      refine Submodule.span_induction
        (p := fun c _ => bracketMap R (F R X) c ∈ freeDerived R X)
        ?_ ?_ ?_ ?_ hc
      · rintro _ ⟨v, rfl⟩
        have hv : v = ![v 0, v 1] := by
          funext i
          fin_cases i <;> rfl
        rw [hv]
        rw [bracketMap_ιMulti]
        exact LieSubmodule.lie_mem_lie (by simp) (by simp)
      · change bracketMap R (F R X) 0 ∈ freeDerived R X
        rw [map_zero]
        exact LieSubmodule.zero_mem _
      · intro a b _ _ ha hb
        rw [map_add]
        exact (freeDerived R X).add_mem ha hb
      · intro r a _ ha
        rw [map_smul]
        exact (freeDerived R X).smul_mem r ha

/-- The reduced bracket, with codomain restricted to the derived ideal. -/
def reducedBracketToFreeDerived :
    ReducedExteriorSquare R (F R X) →ₗ[R] freeDerived R X :=
  (reducedBracket R (F R X)).codRestrict (freeDerived R X)
    (reducedBracket_mem_freeDerived R X)

@[simp]
theorem reducedBracketToFreeDerived_wedge (x y : F R X) :
    reducedBracketToFreeDerived R X (reducedWedge R (F R X) x y) =
      ⟨⁅x, y⁆, LieSubmodule.lie_mem_lie (by simp) (by simp)⟩ := by
  apply Subtype.ext
  exact reducedBracket_wedge R (F R X) x y

private theorem reducedBracketToFreeDerived_surjective :
    Function.Surjective (reducedBracketToFreeDerived R X) := by
  intro z
  have hz : (z : F R X) ∈ Submodule.span R
      {q : F R X | ∃ a ∈ (⊤ : LieIdeal R (F R X)),
        ∃ b ∈ (⊤ : LieIdeal R (F R X)), ⁅a, b⁆ = q} := by
    rw [← LieSubmodule.lieIdeal_oper_eq_linear_span'
      (⊤ : LieIdeal R (F R X)) (⊤ : LieIdeal R (F R X))]
    exact z.property
  have hlift : ∀ q : F R X,
      q ∈ Submodule.span R
        {q : F R X | ∃ a ∈ (⊤ : LieIdeal R (F R X)),
          ∃ b ∈ (⊤ : LieIdeal R (F R X)), ⁅a, b⁆ = q} →
      ∃ w : ReducedExteriorSquare R (F R X), reducedBracket R (F R X) w = q := by
    intro q hq
    refine Submodule.span_induction
      (p := fun q _ => ∃ w : ReducedExteriorSquare R (F R X),
        reducedBracket R (F R X) w = q)
      ?_ ?_ ?_ ?_ hq
    · rintro q ⟨a, -, b, -, rfl⟩
      exact ⟨reducedWedge R (F R X) a b,
        reducedBracket_wedge R (F R X) a b⟩
    · exact ⟨0, map_zero _⟩
    · rintro a b _ _ ⟨wa, hwa⟩ ⟨wb, hwb⟩
      refine ⟨wa + wb, ?_⟩
      rw [map_add, hwa, hwb]
    · rintro r a _ ⟨wa, hwa⟩
      refine ⟨r • wa, ?_⟩
      rw [map_smul, hwa]
  obtain ⟨w, hw⟩ := hlift z hz
  refine ⟨w, ?_⟩
  apply Subtype.ext
  exact hw

/-- For a free Lie algebra, the reduced exterior square is canonically its derived ideal. -/
def freeReducedExteriorEquivDerived :
    ReducedExteriorSquare R (F R X) ≃ₗ[R] freeDerived R X :=
  LinearEquiv.ofBijective (reducedBracketToFreeDerived R X)
    ⟨fun _ _ h => reducedBracket_free_injective R X (congrArg Subtype.val h),
      reducedBracketToFreeDerived_surjective R X⟩

set_option synthInstance.maxHeartbeats 100000 in
-- The equivalence unfolds two nested submodule quotients while constructing the subtype instance.
/-- The second Chevalley--Eilenberg homology of a free Lie algebra vanishes. -/
theorem secondHomology_free_subsingleton :
    Subsingleton (SecondHomology R (F R X)) := by
  constructor
  intro a b
  apply (secondHomologyEquivReducedBracketKernel R (F R X)).injective
  apply Subtype.ext
  have ha : ((secondHomologyEquivReducedBracketKernel R (F R X)) a).1 = 0 := by
    apply (Submodule.mem_bot R).mp
    rw [← reducedBracket_free_ker_eq_bot R X]
    exact ((secondHomologyEquivReducedBracketKernel R (F R X)) a).2
  have hb : ((secondHomologyEquivReducedBracketKernel R (F R X)) b).1 = 0 := by
    apply (Submodule.mem_bot R).mp
    rw [← reducedBracket_free_ker_eq_bot R X]
    exact ((secondHomologyEquivReducedBracketKernel R (F R X)) b).2
  exact ha.trans hb.symm

set_option synthInstance.maxHeartbeats 100000 in
-- The abstract and concrete homology quotients both unfold during instance synthesis.
/-- Degree two of the all-degree CE homology object also vanishes on a free Lie algebra. -/
theorem homologyTwo_free_subsingleton :
    Subsingleton (Homology (R := R) (L := F R X) 2) := by
  letI : Subsingleton (SecondHomology R (F R X)) :=
    secondHomology_free_subsingleton R X
  exact (secondHomologyConcreteIso R (F R X)).toLinearEquiv.toEquiv.subsingleton

end

end LieRings.Homological.LieHomology
