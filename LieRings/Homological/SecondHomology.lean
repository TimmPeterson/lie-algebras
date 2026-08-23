import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

/-!
# Second integral homology via the Hopf formula

This file deliberately implements only the degree-two, integral object needed in this project.
For a free presentation `F → L` with relation ideal `R`, its presentation-level Hopf multiplier is

`(R ∩ [F,F]) / [F,R]`.

The public object `secondHomology` uses the canonical free presentation on the underlying set of
the Lie ring.  This is not a construction of Lie homology in arbitrary degrees or with arbitrary
coefficients.  In particular, this file does not yet compare the Hopf-formula model with a
Chevalley--Eilenberg complex or with a derived-functor definition.  Such a comparison can be added
later without changing the concrete degree-two interface developed here.
-/

namespace LieRings

namespace Homological

universe u v w

noncomputable section

/-- A free presentation of a Lie ring.  The source is free on the type `Generators`. -/
structure FreePresentation (L : Type u) [LieRing L] where
  Generators : Type v
  evaluation : LieHom ℤ (FreeLieAlgebra ℤ Generators) L
  surjective : Function.Surjective evaluation

namespace FreePresentation

variable {L : Type u} [LieRing L]

/-- The free Lie ring underlying a free presentation. -/
abbrev Free (P : FreePresentation L) := FreeLieAlgebra ℤ P.Generators

/-- The relation ideal of a free presentation. -/
abbrev relations (P : FreePresentation L) : LieIdeal ℤ P.Free :=
  LieHom.ker P.evaluation

/-- The derived ideal of the free Lie ring in a presentation. -/
abbrev derived (P : FreePresentation L) : LieIdeal ℤ P.Free :=
  ⁅(⊤ : LieIdeal ℤ P.Free), (⊤ : LieIdeal ℤ P.Free)⁆

/-- The numerator `R ∩ [F,F]` in the Hopf formula. -/
abbrev hopfNumerator (P : FreePresentation L) : LieIdeal ℤ P.Free :=
  P.relations ⊓ P.derived

/-- The denominator `[F,R]` in the Hopf formula. -/
abbrev hopfDenominator (P : FreePresentation L) : LieIdeal ℤ P.Free :=
  ⁅(⊤ : LieIdeal ℤ P.Free), P.relations⁆

theorem hopfDenominator_le_hopfNumerator (P : FreePresentation L) :
    P.hopfDenominator ≤ P.hopfNumerator := by
  rw [le_inf_iff]
  exact ⟨LieSubmodule.lie_le_right P.relations (⊤ : LieIdeal ℤ P.Free),
    LieSubmodule.mono_lie_right (⊤ : LieIdeal ℤ P.Free) le_top⟩

/-- The denominator, regarded as a submodule of the Hopf numerator. -/
abbrev hopfRelations (P : FreePresentation L) :
    Submodule ℤ P.hopfNumerator :=
  P.hopfDenominator.toSubmodule.comap P.hopfNumerator.toSubmodule.subtype

/-- The Hopf-formula multiplier attached to a specified free presentation. -/
abbrev hopfSecondHomology (P : FreePresentation L) :=
  P.hopfNumerator ⧸ P.hopfRelations

/-- A morphism of free presentations, including a chosen lift between their free sources. -/
structure Hom {M : Type w} [LieRing M]
    (P : FreePresentation L) (Q : FreePresentation M) where
  base : LieHom ℤ L M
  free : LieHom ℤ P.Free Q.Free
  commutes : Q.evaluation.comp free = base.comp P.evaluation

variable {M : Type w} [LieRing M]
variable {P : FreePresentation L} {Q : FreePresentation M}

theorem Hom.map_relations (f : Hom P Q) :
    LieIdeal.map f.free P.relations ≤ Q.relations := by
  rw [LieIdeal.map_le_iff_le_comap]
  intro x hx
  change Q.evaluation (f.free x) = 0
  have hx0 : P.evaluation x = 0 := hx
  have hcomm := LieHom.congr_fun f.commutes x
  simpa [hx0] using hcomm

theorem Hom.map_derived (f : Hom P Q) :
    LieIdeal.map f.free P.derived ≤ Q.derived := by
  exact (LieIdeal.map_bracket_le f.free).trans
    (LieSubmodule.mono_lie le_top le_top)

theorem Hom.map_hopfNumerator (f : Hom P Q) :
    LieIdeal.map f.free P.hopfNumerator ≤ Q.hopfNumerator := by
  rw [LieIdeal.map_le_iff_le_comap]
  intro x hx
  exact ⟨(LieIdeal.map_le_iff_le_comap.mp f.map_relations) hx.1,
    (LieIdeal.map_le_iff_le_comap.mp f.map_derived) hx.2⟩

theorem Hom.map_hopfDenominator (f : Hom P Q) :
    LieIdeal.map f.free P.hopfDenominator ≤ Q.hopfDenominator := by
  exact (LieIdeal.map_bracket_le f.free).trans
    (LieSubmodule.mono_lie le_top f.map_relations)

/-- The map of Hopf numerators induced by a morphism of presentations. -/
def Hom.numeratorMap (f : Hom P Q) :
    P.hopfNumerator →ₗ[ℤ] Q.hopfNumerator :=
  f.free.toLinearMap.restrict (by
    intro x hx
    exact (LieIdeal.map_le_iff_le_comap.mp f.map_hopfNumerator) hx)

theorem Hom.hopfRelations_le_comap_numeratorMap (f : Hom P Q) :
    P.hopfRelations ≤ Q.hopfRelations.comap f.numeratorMap := by
  intro x hx
  rw [Submodule.mem_comap]
  change f.free (x : P.Free) ∈ Q.hopfDenominator
  change (x : P.Free) ∈ P.hopfDenominator at hx
  exact (LieIdeal.map_le_iff_le_comap.mp f.map_hopfDenominator) hx

/-- The map on presentation-level Hopf multipliers. -/
def Hom.hopfMap (f : Hom P Q) :
    P.hopfSecondHomology →ₗ[ℤ] Q.hopfSecondHomology :=
  P.hopfRelations.mapQ Q.hopfRelations f.numeratorMap
    f.hopfRelations_le_comap_numeratorMap

@[simp]
theorem Hom.hopfMap_mk (f : Hom P Q) (x : P.hopfNumerator) :
    f.hopfMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.numeratorMap x) :=
  rfl

/-- Two lifts which induce the same map on the presented Lie rings agree on the derived ideal
modulo `[F,R]`.  This is the elementary lift-independence calculation behind the Hopf formula. -/
theorem lieHom_sub_mem_hopfDenominator_of_mem_derived
    {A : Type u} [LieRing A] (Q : FreePresentation M)
    (f g : LieHom ℤ A Q.Free)
    (h : Q.evaluation.comp f = Q.evaluation.comp g)
    {x : A} (hx : x ∈ ⁅(⊤ : LieIdeal ℤ A), (⊤ : LieIdeal ℤ A)⁆) :
    f x - g x ∈ Q.hopfDenominator := by
  have hx' : x ∈ Submodule.span ℤ
      {z : A | ∃ a ∈ (⊤ : LieIdeal ℤ A), ∃ b ∈ (⊤ : LieIdeal ℤ A), ⁅a, b⁆ = z} := by
    rw [← LieSubmodule.lieIdeal_oper_eq_linear_span'
      (⊤ : LieIdeal ℤ A) (⊤ : LieIdeal ℤ A)]
    exact hx
  refine Submodule.span_induction (p := fun z _ ↦ f z - g z ∈ Q.hopfDenominator)
    ?_ ?_ ?_ ?_ hx'
  · rintro z ⟨a, -, b, -, rfl⟩
    have ha : f a - g a ∈ Q.relations := by
      change Q.evaluation (f a - g a) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (LieHom.congr_fun h a)
    have hb : f b - g b ∈ Q.relations := by
      change Q.evaluation (f b - g b) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (LieHom.congr_fun h b)
    have hleft : ⁅f a - g a, f b⁆ ∈ Q.hopfDenominator := by
      have hmem : ⁅f a - g a, f b⁆ ∈
          ⁅Q.relations, (⊤ : LieIdeal ℤ Q.Free)⁆ :=
        LieSubmodule.lie_mem_lie ha (by simp)
      rw [LieSubmodule.lie_comm] at hmem
      exact hmem
    have hright : ⁅g a, f b - g b⁆ ∈ Q.hopfDenominator :=
      LieSubmodule.lie_mem_lie (by simp) hb
    rw [LieHom.map_lie, LieHom.map_lie]
    have hid : ⁅f a, f b⁆ - ⁅g a, g b⁆ =
        ⁅f a - g a, f b⁆ + ⁅g a, f b - g b⁆ := by
      rw [sub_lie, lie_sub]
      abel
    rw [hid]
    exact Q.hopfDenominator.add_mem hleft hright
  · simp
  · intro a b _ _ ha hb
    have heq : f (a + b) - g (a + b) =
        (f a - g a) + (f b - g b) := by
      rw [map_add, map_add]
      abel
    rw [heq]
    exact Q.hopfDenominator.add_mem ha hb
  · intro n a _ ha
    simpa [smul_sub] using Q.hopfDenominator.smul_mem n ha

/-- The map on Hopf multipliers is independent of the chosen free lift of a fixed base map. -/
theorem Hom.hopfMap_eq_of_base_eq (f g : Hom P Q) (hbase : f.base = g.base) :
    f.hopfMap = g.hopfMap := by
  have hfree : Q.evaluation.comp f.free = Q.evaluation.comp g.free := by
    rw [f.commutes, g.commutes, hbase]
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
      rw [f.hopfMap_mk, g.hopfMap_mk]
      apply (Submodule.Quotient.eq Q.hopfRelations).2
      change f.free (x : P.Free) - g.free (x : P.Free) ∈ Q.hopfDenominator
      exact lieHom_sub_mem_hopfDenominator_of_mem_derived Q f.free g.free hfree x.property.2

/-- The identity morphism of a free presentation. -/
def Hom.id (P : FreePresentation L) : Hom P P where
  base := LieHom.id
  free := LieHom.id
  commutes := by rfl

/-- Composition of morphisms of free presentations. -/
def Hom.comp {N : Type*} [LieRing N] {S : FreePresentation N}
    (g : Hom Q S) (f : Hom P Q) : Hom P S where
  base := g.base.comp f.base
  free := g.free.comp f.free
  commutes := by
    apply LieHom.ext
    intro x
    have hg := LieHom.congr_fun g.commutes (f.free x)
    have hf := LieHom.congr_fun f.commutes x
    exact hg.trans (congrArg g.base hf)

@[simp]
theorem Hom.hopfMap_id (P : FreePresentation L) :
    (Hom.id P).hopfMap = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x => rfl

theorem Hom.hopfMap_comp {N : Type*} [LieRing N] {S : FreePresentation N}
    (g : Hom Q S) (f : Hom P Q) :
    (g.comp f).hopfMap = g.hopfMap.comp f.hopfMap := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- A chosen lift of a base homomorphism to the free sources of two presentations. -/
def chosenHom (P : FreePresentation L) (Q : FreePresentation M)
    (f : LieHom ℤ L M) : Hom P Q := by
  let generatorLift : P.Generators → Q.Free := fun x ↦
    Classical.choose (Q.surjective (f (P.evaluation (FreeLieAlgebra.of ℤ x))))
  let freeLift : LieHom ℤ P.Free Q.Free := FreeLieAlgebra.lift ℤ generatorLift
  refine
    { base := f
      free := freeLift
      commutes := ?_ }
  apply FreeLieAlgebra.hom_ext
  intro x
  change Q.evaluation
      ((FreeLieAlgebra.lift ℤ generatorLift) (FreeLieAlgebra.of ℤ x)) =
    f (P.evaluation (FreeLieAlgebra.of ℤ x))
  rw [FreeLieAlgebra.lift_of_apply]
  exact Classical.choose_spec
    (Q.surjective (f (P.evaluation (FreeLieAlgebra.of ℤ x))))

/-- Presentation-independence of the Hopf multiplier.  The equivalence is built from chosen
comparison lifts; lift-independence makes the two directions inverse. -/
def hopfSecondHomologyEquiv (P Q : FreePresentation L) :
    P.hopfSecondHomology ≃ₗ[ℤ] Q.hopfSecondHomology := by
  let f : Hom P Q := chosenHom P Q LieHom.id
  let g : Hom Q P := chosenHom Q P LieHom.id
  refine LinearEquiv.ofLinear f.hopfMap g.hopfMap ?_ ?_
  · rw [← f.hopfMap_comp g]
    calc
      (f.comp g).hopfMap = (Hom.id Q).hopfMap :=
        Hom.hopfMap_eq_of_base_eq (f.comp g) (Hom.id Q) (by
          apply LieHom.ext
          intro x
          rfl)
      _ = LinearMap.id := Hom.hopfMap_id Q
  · rw [← g.hopfMap_comp f]
    calc
      (g.comp f).hopfMap = (Hom.id P).hopfMap :=
        Hom.hopfMap_eq_of_base_eq (g.comp f) (Hom.id P) (by
          apply LieHom.ext
          intro x
          rfl)
      _ = LinearMap.id := Hom.hopfMap_id P

/-- The canonical free presentation on the underlying set of a Lie ring. -/
def canonicalPresentation (L : Type u) [LieRing L] : FreePresentation L where
  Generators := L
  evaluation := FreeLieAlgebra.lift ℤ id
  surjective := by
    intro x
    exact ⟨FreeLieAlgebra.of ℤ x, FreeLieAlgebra.lift_of_apply id x⟩

@[simp]
theorem canonicalPresentation_evaluation_of (L : Type u) [LieRing L] (x : L) :
    (canonicalPresentation L).evaluation (FreeLieAlgebra.of ℤ x) = x := by
  exact FreeLieAlgebra.lift_of_apply id x

/-- The canonical free lift of a Lie-ring homomorphism. -/
def canonicalHom (f : LieHom ℤ L M) :
    Hom (canonicalPresentation L) (canonicalPresentation M) where
  base := f
  free := FreeLieAlgebra.lift ℤ (fun x ↦ FreeLieAlgebra.of ℤ (f x))
  commutes := by
    apply FreeLieAlgebra.hom_ext
    intro x
    change (canonicalPresentation M).evaluation
        ((FreeLieAlgebra.lift ℤ (fun y ↦ FreeLieAlgebra.of ℤ (f y)))
          (FreeLieAlgebra.of ℤ x)) =
      f ((canonicalPresentation L).evaluation (FreeLieAlgebra.of ℤ x))
    rw [FreeLieAlgebra.lift_of_apply, canonicalPresentation_evaluation_of]
    exact canonicalPresentation_evaluation_of M (f x)

/--
The concrete Hopf-formula model for `H₂(L; ℤ)`, formed from the canonical free presentation:
`(R ∩ [F,F]) / [F,R]`.

This definition is intentionally not a general definition of Lie homology.  It provides only
degree two with trivial integral coefficients, and currently makes no assertion identifying this
model with Chevalley--Eilenberg or derived-functor homology.
-/
abbrev secondHomology (L : Type u) [LieRing L] :=
  (canonicalPresentation L).hopfSecondHomology

/-- The map on the Hopf-formula models of second homology induced by a Lie-ring homomorphism. -/
def secondHomologyMap (f : LieHom ℤ L M) :
    secondHomology L →ₗ[ℤ] secondHomology M :=
  (canonicalHom f).hopfMap

@[simp]
theorem secondHomologyMap_id :
    secondHomologyMap (LieHom.id : LieHom ℤ L L) = LinearMap.id := by
  calc
    secondHomologyMap (LieHom.id : LieHom ℤ L L) =
        (Hom.id (canonicalPresentation L)).hopfMap :=
      Hom.hopfMap_eq_of_base_eq (canonicalHom LieHom.id)
        (Hom.id (canonicalPresentation L)) rfl
    _ = LinearMap.id := Hom.hopfMap_id (canonicalPresentation L)

theorem secondHomologyMap_comp {N : Type*} [LieRing N]
    (g : LieHom ℤ M N) (f : LieHom ℤ L M) :
    secondHomologyMap (g.comp f) =
      (secondHomologyMap g).comp (secondHomologyMap f) := by
  calc
    secondHomologyMap (g.comp f) =
        ((canonicalHom g).comp (canonicalHom f)).hopfMap :=
      Hom.hopfMap_eq_of_base_eq (canonicalHom (g.comp f))
        ((canonicalHom g).comp (canonicalHom f)) rfl
    _ = (secondHomologyMap g).comp (secondHomologyMap f) :=
      Hom.hopfMap_comp (canonicalHom g) (canonicalHom f)

section Quotients

variable (I J : LieIdeal ℤ L)

/-- The quotient map by a Lie ideal, as a Lie-ring homomorphism. -/
def quotientMk : LieHom ℤ L (L ⧸ I) where
  __ := I.toSubmodule.mkQ
  map_lie' := by
    intro x y
    rfl

@[simp]
theorem quotientMk_apply (x : L) :
    quotientMk I x = (LieSubmodule.Quotient.mk x : L ⧸ I) :=
  rfl

@[simp]
theorem quotientMk_ker : LieHom.ker (quotientMk I) = I := by
  ext x
  exact LieSubmodule.Quotient.mk_eq_zero'

/-- The quotient homomorphism `L/J → L/I` induced by an inclusion `J ≤ I`. -/
def quotientMap (hJI : J ≤ I) : LieHom ℤ (L ⧸ J) (L ⧸ I) where
  __ := J.toSubmodule.mapQ I.toSubmodule LinearMap.id hJI
  map_lie' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y => rfl

@[simp]
theorem quotientMap_mk (hJI : J ≤ I) (x : L) :
    quotientMap I J hJI (LieSubmodule.Quotient.mk x) =
      (LieSubmodule.Quotient.mk x : L ⧸ I) :=
  rfl

@[simp]
theorem quotientMap_comp_quotientMk (hJI : J ≤ I) :
    (quotientMap I J hJI).comp (quotientMk J) = quotientMk I := by
  apply LieHom.ext
  intro x
  rfl

/-- A free presentation followed by a Lie-ideal quotient. -/
def quotient (P : FreePresentation L) (I : LieIdeal ℤ L) :
    FreePresentation (L ⧸ I) where
  Generators := P.Generators
  evaluation := (quotientMk I).comp P.evaluation
  surjective := (LieSubmodule.Quotient.surjective_mk' I).comp P.surjective

@[simp]
theorem quotient_relations (P : FreePresentation L) (I : LieIdeal ℤ L) :
    (P.quotient I).relations = LieIdeal.comap P.evaluation I := by
  ext x
  change quotientMk I (P.evaluation x) = 0 ↔ P.evaluation x ∈ I
  exact LieSubmodule.Quotient.mk_eq_zero'

/-- The morphism between the compatible quotient presentations arising from `J ≤ I`. -/
def quotientHom (P : FreePresentation L) (hJI : J ≤ I) :
    Hom (P.quotient J) (P.quotient I) where
  base := quotientMap I J hJI
  free := LieHom.id
  commutes := by
    apply LieHom.ext
    intro x
    change quotientMap I J hJI (quotientMk J (P.evaluation x)) =
      quotientMk I (P.evaluation x)
    rfl

/-- The morphism from a presentation of `L` to the compatible presentation of `L/I`. -/
def quotientProjectionHom (P : FreePresentation L) (I : LieIdeal ℤ L) :
    Hom P (P.quotient I) where
  base := quotientMk I
  free := LieHom.id
  commutes := by
    rfl

/-- The module `I/J`, represented as the quotient of the subtype `I`. -/
abbrev IdealQuotient :=
  I ⧸ J.toSubmodule.comap I.toSubmodule.subtype

variable {I J}

/-- Evaluation from the Hopf numerator for `L/I` to the ideal `I`. -/
def hopfTransgressionRaw (P : FreePresentation L) (I : LieIdeal ℤ L) :
    (P.quotient I).hopfNumerator →ₗ[ℤ] I where
  toFun := fun x ↦ ⟨P.evaluation (x : (P.quotient I).Free), by
    have hx := x.property.1
    rw [quotient_relations] at hx
    exact hx⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    exact map_add P.evaluation (x : (P.quotient I).Free)
      (y : (P.quotient I).Free)
  map_smul' := by
    intro n x
    apply Subtype.ext
    exact map_smul P.evaluation n (x : (P.quotient I).Free)

theorem evaluation_hopfDenominator_le
    (P : FreePresentation L) (I J : LieIdeal ℤ L)
    (hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J) :
    LieIdeal.map P.evaluation (P.quotient I).hopfDenominator ≤ J := by
  calc
    LieIdeal.map P.evaluation (P.quotient I).hopfDenominator ≤
        ⁅LieIdeal.map P.evaluation (⊤ : LieIdeal ℤ P.Free),
          LieIdeal.map P.evaluation (P.quotient I).relations⁆ :=
      LieIdeal.map_bracket_le P.evaluation
    _ ≤ ⁅(⊤ : LieIdeal ℤ L), I⁆ := by
      apply LieSubmodule.mono_lie
      · exact le_top
      · rw [quotient_relations]
        exact LieIdeal.map_comap_le
    _ ≤ J := hcentral

theorem hopfTransgressionRaw_hopfRelations_le_ker
    (P : FreePresentation L)
    (hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J) :
    (P.quotient I).hopfRelations ≤
      LinearMap.ker
        ((J.toSubmodule.comap I.toSubmodule.subtype).mkQ.comp
          (hopfTransgressionRaw P I)) := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply (Submodule.Quotient.mk_eq_zero _).2
  change P.evaluation (x : (P.quotient I).Free) ∈ J
  change (x : (P.quotient I).Free) ∈ (P.quotient I).hopfDenominator at hx
  exact evaluation_hopfDenominator_le P I J hcentral (LieIdeal.mem_map hx)

/-- The Hopf transgression for the central extension `I/J → L/J → L/I`. -/
def hopfTransgression (P : FreePresentation L)
    (hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J) :
    (P.quotient I).hopfSecondHomology →ₗ[ℤ] IdealQuotient I J :=
  (P.quotient I).hopfRelations.liftQ
    ((J.toSubmodule.comap I.toSubmodule.subtype).mkQ.comp
      (hopfTransgressionRaw P I))
    (hopfTransgressionRaw_hopfRelations_le_ker P hcentral)

/-- The five-term transgression `H₂(L/I) → I/[L,I]` attached to a presentation of `L`. -/
def hopfQuotientTransgression (P : FreePresentation L) (I : LieIdeal ℤ L) :
    (P.quotient I).hopfSecondHomology →ₗ[ℤ]
      IdealQuotient I ⁅(⊤ : LieIdeal ℤ L), I⁆ :=
  hopfTransgression P (le_refl ⁅(⊤ : LieIdeal ℤ L), I⁆)

@[simp]
theorem hopfTransgression_mk (P : FreePresentation L)
    (hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J)
    (x : (P.quotient I).hopfNumerator) :
    hopfTransgression P hcentral (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (hopfTransgressionRaw P I x) :=
  rfl

theorem hopfTransgression_comp_quotientHom_hopfMap
    (P : FreePresentation L) (hJI : J ≤ I)
    (hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J) :
    (hopfTransgression P hcentral).comp
      (quotientHom I J P hJI).hopfMap = 0 := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
      rw [LinearMap.comp_apply, Hom.hopfMap_mk, hopfTransgression_mk]
      apply (Submodule.Quotient.mk_eq_zero _).2
      change P.evaluation (x : (P.quotient J).Free) ∈ J
      have hx := x.property.1
      rw [quotient_relations] at hx
      exact hx

/-- Exactness of the Hopf transgression at `H₂(L/I)` for a central extension. -/
theorem range_quotientHom_hopfMap_eq_ker_hopfTransgression
    (P : FreePresentation L) (hJI : J ≤ I)
    (hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J) :
    LinearMap.range (quotientHom I J P hJI).hopfMap =
      LinearMap.ker (hopfTransgression P hcentral) := by
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun
      (hopfTransgression_comp_quotientHom_hopfMap P hJI hcentral) y
  · intro z hz
    induction z using Submodule.Quotient.induction_on with
    | _ x =>
        rw [LinearMap.mem_ker, hopfTransgression_mk] at hz
        have hxJ : P.evaluation (x : (P.quotient I).Free) ∈ J := by
          have hmem : hopfTransgressionRaw P I x ∈
              J.toSubmodule.comap I.toSubmodule.subtype :=
            (Submodule.Quotient.mk_eq_zero _).1 hz
          exact hmem
        let y : (P.quotient J).hopfNumerator :=
          ⟨(x : (P.quotient I).Free), ⟨by
            rw [quotient_relations]
            exact hxJ, x.property.2⟩⟩
        refine ⟨Submodule.Quotient.mk y, ?_⟩
        rfl

theorem map_top_eq_top_of_surjective (P : FreePresentation L) :
    LieIdeal.map P.evaluation (⊤ : LieIdeal ℤ P.Free) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := P.surjective y
  exact LieIdeal.mem_map (by simp)

theorem map_derived_eq_derived (P : FreePresentation L) :
    LieIdeal.map P.evaluation P.derived =
      ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆ := by
  rw [LieIdeal.map_bracket_eq P.evaluation P.surjective,
    map_top_eq_top_of_surjective P]

/-- Exactness at `H₂(L/I)` in the Hopf five-term sequence, proved directly from one free
presentation. -/
theorem range_quotientProjectionHom_hopfMap_eq_ker_hopfQuotientTransgression
    (P : FreePresentation L) (I : LieIdeal ℤ L) :
    LinearMap.range (quotientProjectionHom P I).hopfMap =
      LinearMap.ker (hopfQuotientTransgression P I) := by
  have hmapI :
      LieIdeal.map P.evaluation (LieIdeal.comap P.evaluation I) = I := by
    apply le_antisymm
    · exact LieIdeal.map_comap_le
    · intro y hy
      obtain ⟨x, rfl⟩ := P.surjective y
      exact LieIdeal.mem_map hy
  have hmapDenominator :
      LieIdeal.map P.evaluation (P.quotient I).hopfDenominator =
        ⁅(⊤ : LieIdeal ℤ L), I⁆ := by
    calc
      LieIdeal.map P.evaluation (P.quotient I).hopfDenominator =
          ⁅LieIdeal.map P.evaluation (⊤ : LieIdeal ℤ P.Free),
            LieIdeal.map P.evaluation (P.quotient I).relations⁆ :=
        LieIdeal.map_bracket_eq P.evaluation P.surjective
      _ = ⁅(⊤ : LieIdeal ℤ L), I⁆ := by
        rw [map_top_eq_top_of_surjective P, quotient_relations, hmapI]
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    induction y using Submodule.Quotient.induction_on with
    | _ x =>
        rw [Hom.hopfMap_mk]
        change hopfQuotientTransgression P I
            (Submodule.Quotient.mk
              ((quotientProjectionHom P I).numeratorMap x)) = 0
        rw [hopfQuotientTransgression, hopfTransgression_mk]
        apply (Submodule.Quotient.mk_eq_zero _).2
        change P.evaluation (x : P.Free) ∈
          ⁅(⊤ : LieIdeal ℤ L), I⁆
        have hx : P.evaluation (x : P.Free) = 0 := x.property.1
        rw [hx]
        exact LieSubmodule.zero_mem _
  · intro z hz
    induction z using Submodule.Quotient.induction_on with
    | _ x =>
        rw [LinearMap.mem_ker] at hz
        change hopfQuotientTransgression P I
            (Submodule.Quotient.mk x) = 0 at hz
        rw [hopfQuotientTransgression, hopfTransgression_mk] at hz
        have hxcomm : P.evaluation (x : (P.quotient I).Free) ∈
            ⁅(⊤ : LieIdeal ℤ L), I⁆ := by
          have hmem : hopfTransgressionRaw P I x ∈
              (⁅(⊤ : LieIdeal ℤ L), I⁆).toSubmodule.comap
                I.toSubmodule.subtype :=
            (Submodule.Quotient.mk_eq_zero _).1 hz
          exact hmem
        have hxmap : P.evaluation (x : (P.quotient I).Free) ∈
            LieIdeal.map P.evaluation (P.quotient I).hopfDenominator := by
          rw [hmapDenominator]
          exact hxcomm
        obtain ⟨y, hy⟩ :=
          LieIdeal.mem_map_of_surjective P.surjective hxmap
        let xFree : P.Free := by
          change FreeLieAlgebra ℤ P.Generators
          simpa only [Free, quotient] using
            (x : (P.quotient I).Free)
        let yFree : P.Free := by
          exact y.1
        let xTarget : (P.quotient I).Free := x
        let yTarget : (P.quotient I).Free := by
          change FreeLieAlgebra ℤ P.Generators
          exact yFree
        have hyFree : P.evaluation yFree = P.evaluation xFree := by
          simpa only [xFree, yFree, Free, quotient] using hy
        have hyDenominator : yTarget ∈ (P.quotient I).hopfDenominator := by
          simpa only [yTarget, yFree, Free, quotient] using y.property
        have hxderived : xFree ∈ P.derived := by
          simpa only [xFree, derived, Free, quotient] using x.property.2
        have hyderived : yFree ∈ P.derived := by
          simpa only [yFree, derived, Free, quotient] using
            ((P.quotient I).hopfDenominator_le_hopfNumerator hyDenominator).2
        let r : P.hopfNumerator :=
          ⟨xFree - yFree, ⟨by
            change P.evaluation (xFree - yFree) = 0
            rw [map_sub, hyFree, sub_self],
            P.derived.sub_mem hxderived hyderived⟩⟩
        refine ⟨Submodule.Quotient.mk r, ?_⟩
        rw [Hom.hopfMap_mk]
        apply (Submodule.Quotient.eq _).2
        change
          ((quotientProjectionHom P I).numeratorMap r :
              (P.quotient I).Free) - (x : (P.quotient I).Free) ∈
            (P.quotient I).hopfDenominator
        have hdifference :
            ((quotientProjectionHom P I).numeratorMap r :
                (P.quotient I).Free) - (x : (P.quotient I).Free) =
              -yTarget := by
          have hr : ((quotientProjectionHom P I).numeratorMap r :
              (P.quotient I).Free) = xTarget - yTarget := by
            rfl
          rw [hr]
          change (xTarget - yTarget) - xTarget = -yTarget
          abel
        rw [hdifference]
        exact (P.quotient I).hopfDenominator.neg_mem hyDenominator

/-- The Hopf transgression is onto when `I/J` lies in the derived ideal of `L/J`. -/
theorem hopfTransgression_surjective
    (P : FreePresentation L) (hJI : J ≤ I)
    (hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J)
    (hstem : I ≤ ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆ ⊔ J) :
    Function.Surjective (hopfTransgression P hcentral) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ i =>
      have hi := hstem i.property
      rw [LieSubmodule.mem_sup] at hi
      obtain ⟨d, hd, j, hj, hdj⟩ := hi
      have hdmap : d ∈ LieIdeal.map P.evaluation P.derived := by
        rw [map_derived_eq_derived P]
        exact hd
      obtain ⟨x, hxeval⟩ :=
        LieIdeal.mem_map_of_surjective P.surjective hdmap
      have hdI : d ∈ I := by
        have hiSub : (i : L) - j ∈ I := I.sub_mem i.property (hJI hj)
        convert hiSub using 1
        rw [← hdj]
        abel
      let xn : (P.quotient I).hopfNumerator :=
        ⟨(x : P.Free), ⟨by
          rw [quotient_relations]
          change P.evaluation (x : P.Free) ∈ I
          rw [hxeval]
          exact hdI, x.property⟩⟩
      refine ⟨Submodule.Quotient.mk xn, ?_⟩
      rw [hopfTransgression_mk]
      apply (Submodule.Quotient.eq _).2
      change P.evaluation (x : P.Free) - (i : L) ∈ J
      rw [hxeval, ← hdj]
      simpa using J.neg_mem hj

/-- The cokernel of a linear map, as an explicit module quotient. -/
abbrev LinearCokernel {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (f : A →ₗ[ℤ] B) :=
  B ⧸ LinearMap.range f

/-- The specialized central-stem part of the five-term sequence, proved directly from the Hopf
formula using compatible free presentations. -/
def quotientPresentationCokernelEquiv
    (P : FreePresentation L) (hJI : J ≤ I)
    (hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J)
    (hstem : I ≤ ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆ ⊔ J) :
    LinearCokernel (quotientHom I J P hJI).hopfMap ≃ₗ[ℤ]
      IdealQuotient I J :=
  (Submodule.quotEquivOfEq
      (LinearMap.range (quotientHom I J P hJI).hopfMap)
      (LinearMap.ker (hopfTransgression P hcentral))
      (range_quotientHom_hopfMap_eq_ker_hopfTransgression P hJI hcentral)).trans
    ((hopfTransgression P hcentral).quotKerEquivOfSurjective
      (hopfTransgression_surjective P hJI hcentral hstem))

/-- The Hopf five-term cokernel calculation for an ideal contained in the derived ideal, at the
level of one chosen free presentation. -/
def quotientProjectionCokernelEquiv
    (P : FreePresentation L) (I : LieIdeal ℤ L)
    (hstem : I ≤ ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆) :
    LinearCokernel (quotientProjectionHom P I).hopfMap ≃ₗ[ℤ]
      IdealQuotient I ⁅(⊤ : LieIdeal ℤ L), I⁆ := by
  have hcommutator_le : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ I :=
    LieSubmodule.lie_le_right I (⊤ : LieIdeal ℤ L)
  have hsurjective : Function.Surjective (hopfQuotientTransgression P I) := by
    exact hopfTransgression_surjective P hcommutator_le
      (le_refl ⁅(⊤ : LieIdeal ℤ L), I⁆) (hstem.trans le_sup_left)
  exact
    (Submodule.quotEquivOfEq
      (LinearMap.range (quotientProjectionHom P I).hopfMap)
      (LinearMap.ker (hopfQuotientTransgression P I))
      (range_quotientProjectionHom_hopfMap_eq_ker_hopfQuotientTransgression P I)).trans
      ((hopfQuotientTransgression P I).quotKerEquivOfSurjective hsurjective)

/-- A commutative square with vertical equivalences induces an equivalence on cokernels. -/
def linearCokernelEquivOfCommute
    {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    (f : A →ₗ[ℤ] B) (g : C →ₗ[ℤ] D)
    (eA : A ≃ₗ[ℤ] C) (eB : B ≃ₗ[ℤ] D)
    (hcomm : eB.toLinearMap.comp f = g.comp eA.toLinearMap) :
    LinearCokernel f ≃ₗ[ℤ] LinearCokernel g := by
  apply Submodule.Quotient.equiv (LinearMap.range f) (LinearMap.range g) eB
  apply le_antisymm
  · rintro y ⟨x, ⟨a, rfl⟩, rfl⟩
    refine ⟨eA a, ?_⟩
    exact (LinearMap.congr_fun hcomm a).symm
  · intro y hy
    obtain ⟨c, rfl⟩ := hy
    obtain ⟨a, rfl⟩ := eA.surjective c
    refine ⟨f a, ⟨a, rfl⟩, ?_⟩
    exact LinearMap.congr_fun hcomm a

@[simp]
theorem hopfSecondHomologyEquiv_toLinearMap
    (P Q : FreePresentation L) :
    (hopfSecondHomologyEquiv P Q).toLinearMap =
      (chosenHom P Q LieHom.id).hopfMap :=
  rfl

/-- Naturality of comparison with an arbitrary free presentation. -/
theorem hopfSecondHomologyEquiv_naturality (f : Hom P Q) :
    (hopfSecondHomologyEquiv (canonicalPresentation M) Q).toLinearMap.comp
        (secondHomologyMap f.base) =
      f.hopfMap.comp
        (hopfSecondHomologyEquiv (canonicalPresentation L) P).toLinearMap := by
  rw [hopfSecondHomologyEquiv_toLinearMap,
    hopfSecondHomologyEquiv_toLinearMap]
  change ((chosenHom (canonicalPresentation M) Q LieHom.id).hopfMap.comp
      (canonicalHom f.base).hopfMap) =
    f.hopfMap.comp (chosenHom (canonicalPresentation L) P LieHom.id).hopfMap
  rw [← Hom.hopfMap_comp, ← Hom.hopfMap_comp]
  apply Hom.hopfMap_eq_of_base_eq
  apply LieHom.ext
  intro x
  rfl

/-- If `I` lies in the derived ideal of `L`, then the Hopf five-term sequence gives
`Coker(H₂(L) → H₂(L/I)) ≃ I/[L,I]`. -/
def stemIdealCokernelEquiv
    (I : LieIdeal ℤ L)
    (hstem : I ≤ ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆) :
    LinearCokernel (secondHomologyMap (quotientMk I)) ≃ₗ[ℤ]
      IdealQuotient I ⁅(⊤ : LieIdeal ℤ L), I⁆ := by
  let P := canonicalPresentation L
  let PI := P.quotient I
  let qHom : Hom P PI := quotientProjectionHom P I
  let eL := hopfSecondHomologyEquiv (canonicalPresentation L) P
  let eI := hopfSecondHomologyEquiv (canonicalPresentation (L ⧸ I)) PI
  have hcomm : eI.toLinearMap.comp
        (secondHomologyMap (quotientMk I)) =
      qHom.hopfMap.comp eL.toLinearMap := by
    simpa [qHom, eL, eI] using hopfSecondHomologyEquiv_naturality qHom
  exact (linearCokernelEquivOfCommute
    (secondHomologyMap (quotientMk I)) qHom.hopfMap eL eI hcomm).trans
      (quotientProjectionCokernelEquiv P I hstem)

/-- For a central stem extension `I/J → L/J → L/I`, the kernel is the cokernel of the
induced map on the concrete integral second-homology objects. -/
def centralStemCokernelEquiv
    (hJI : J ≤ I)
    (hcentral : ⁅(⊤ : LieIdeal ℤ L), I⁆ ≤ J)
    (hstem : I ≤ ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆ ⊔ J) :
    LinearCokernel (secondHomologyMap (quotientMap I J hJI)) ≃ₗ[ℤ]
      IdealQuotient I J := by
  let P := canonicalPresentation L
  let PJ := P.quotient J
  let PI := P.quotient I
  let qHom : Hom PJ PI := quotientHom I J P hJI
  let eJ := hopfSecondHomologyEquiv (canonicalPresentation (L ⧸ J)) PJ
  let eI := hopfSecondHomologyEquiv (canonicalPresentation (L ⧸ I)) PI
  have hcomm : eI.toLinearMap.comp
        (secondHomologyMap (quotientMap I J hJI)) =
      qHom.hopfMap.comp eJ.toLinearMap := by
    simpa [qHom, eJ, eI] using hopfSecondHomologyEquiv_naturality qHom
  exact (linearCokernelEquivOfCommute
    (secondHomologyMap (quotientMap I J hJI)) qHom.hopfMap eJ eI hcomm).trans
      (quotientPresentationCokernelEquiv P hJI hcentral hstem)

end Quotients

end FreePresentation

end


end Homological

end LieRings
