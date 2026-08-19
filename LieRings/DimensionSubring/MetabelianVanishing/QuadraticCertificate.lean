import LieRings.DimensionSubring.MetabelianVanishing.QuadraticCharacter
import LieRings.Homological.QuadraticBockstein
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The terminal quadratic vanishing certificate

This file follows the polarization certificate in the manuscript.  Its
coefficient modules are `A = Hom(U,C)` and `B = U/qU`; no double-dual
identification is used.
-/

namespace LieRings.MetabelianVanishing

open TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)

local instance certificateFiniteV : Finite (V L n) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)

local instance certificateFiniteU : Finite (U L n) := by
  let N := (lowerCentralSeries ℤ L n : Submodule ℤ L).comap
    (lowerCentralSeries ℤ L (n - 1) : Submodule ℤ L).subtype
  exact Finite.of_surjective N.mkQ (Submodule.mkQ_surjective _)

local instance certificateFiniteW : Finite (W L n) :=
  Finite.of_surjective
    (lowerCentralSeries ℤ L n : Submodule ℤ L).mkQ
    (Submodule.mkQ_surjective _)

local instance certificatePZeroFree : Module.Free ℤ (PZero L) :=
  Module.Free.of_basis (pZeroBasis L)

local instance certificatePZeroFinite : Module.Finite ℤ (PZero L) :=
  Module.Finite.of_basis (pZeroBasis L)

local instance certificatePOneFinite : Module.Finite ℤ (POne n L) :=
  Module.Finite.of_fg (IsNoetherian.noetherian _)

local instance certificatePOneFree : Module.Free ℤ (POne n L) :=
  Module.free_of_finite_type_torsion_free'

local instance certificateQZeroFree : Module.Free ℤ (QZero n L) :=
  Module.Free.of_basis (qZeroBasis n L)

local instance certificateQZeroFinite : Module.Finite ℤ (QZero n L) :=
  Module.Finite.of_basis (qZeroBasis n L)

local instance certificateQOneFinite (hn : 1 ≤ n) :
    Module.Finite ℤ (QOne n L data hn) :=
  Module.Finite.of_fg (IsNoetherian.noetherian _)

local instance certificateQOneFree (hn : 1 ≤ n) :
    Module.Free ℤ (QOne n L data hn) :=
  Module.free_of_finite_type_torsion_free'

/-- The subgroup `qU` used in the manuscript definition of `B`. -/
def qMultiples : Submodule ℤ (U L n) :=
  LinearMap.range (((2 ^ data.exponent : ℕ) : ℤ) • LinearMap.id)

/-- `B=U/qU`. -/
abbrev CertificateB := U L n ⧸ qMultiples n L data

/-- `A=Hom(U,C)`. -/
abbrev CertificateA := U L n →ₗ[ℤ] ZMod (2 ^ data.exponent)

/-- The quotient map `U → B`. -/
def toCertificateB : U L n →ₗ[ℤ] CertificateB n L data :=
  Submodule.mkQ (qMultiples n L data)

@[simp] theorem toCertificateB_q_smul (u : U L n) :
    toCertificateB n L data (((2 ^ data.exponent : ℕ) : ℤ) • u) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨u, ?_⟩
  exact LinearMap.smul_apply _ LinearMap.id u

/-- Evaluation before descent from `U` to `B`. -/
private def evalU : U L n →ₗ[ℤ] CertificateA n L data →ₗ[ℤ]
    ZMod (2 ^ data.exponent) where
  toFun u :=
    { toFun := fun χ ↦ χ u
      map_add' := by intro χ ψ; rfl
      map_smul' := by intro z χ; rfl }
  map_add' := by intro u v; ext χ; exact map_add χ u v
  map_smul' := by intro z u; ext χ; exact map_zsmul χ z u

/-- The evaluation pairing `B × A → C`. -/
def evalB : CertificateB n L data →ₗ[ℤ]
    CertificateA n L data →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  (qMultiples n L data).liftQ (evalU n L data) (by
    rintro _ ⟨u, rfl⟩
    ext χ
    change χ ((((2 ^ data.exponent : ℕ) : ℤ) • LinearMap.id) u) = 0
    calc
      χ ((((2 ^ data.exponent : ℕ) : ℤ) • LinearMap.id) u) =
          χ (((2 ^ data.exponent : ℕ) : ℤ) • u) := by
            congr 1
      _ = ((2 ^ data.exponent : ℕ) : ℤ) • χ u := map_zsmul χ _ _
      _ = 0 := by
        rw [natCast_zsmul]
        exact ZModModule.char_nsmul_eq_zero (2 ^ data.exponent) (χ u))

@[simp] theorem evalB_mk (u : U L n) (χ : CertificateA n L data) :
    evalB n L data (toCertificateB n L data u) χ = χ u := rfl

/-- Precomposition with `U → B`. -/
def dualBToA :
    (CertificateB n L data →ₗ[ℤ] ZMod (2 ^ data.exponent)) →ₗ[ℤ]
      CertificateA n L data where
  toFun f := f.comp (toCertificateB n L data)
  map_add' := by intro f g; ext u; rfl
  map_smul' := by intro z f; ext u; rfl

/-- Every character `U → C` descends uniquely through `B=U/qU`. -/
def aToDualB : CertificateA n L data →ₗ[ℤ]
    CertificateB n L data →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  LinearMap.flip (evalB n L data)

/-- The literal duality used by the certificate; it is quotient descent, not
finite double-duality. -/
def dualBEquivA :
    (CertificateB n L data →ₗ[ℤ] ZMod (2 ^ data.exponent)) ≃ₗ[ℤ]
      CertificateA n L data where
  toLinearMap := dualBToA n L data
  invFun := aToDualB n L data
  left_inv := by
    intro f
    apply LinearMap.ext
    intro b
    induction b using Submodule.Quotient.induction_on with
    | _ u => rfl
  right_inv := by intro χ; ext u; rfl

/-- The extension tail reduced modulo `q`. -/
def certificateTail (hn : 1 ≤ n) :
    POne n L →ₗ[ℤ] CertificateB n L data :=
  (toCertificateB n L data).comp (pTail n L hn)

/-- The bracket character `ρ(x) : U → C`. -/
def certificateRho (hn : 2 ≤ n) :
    PZero L →ₗ[ℤ] CertificateA n L data := by
  let t := (TensorProduct.lift.equiv (RingHom.id ℤ) (U L n) (PZero L)
    (ZMod (2 ^ data.exponent))).symm (terminalPair n L data hn)
  exact LinearMap.flip t

@[simp] theorem certificateRho_apply (hn : 2 ≤ n)
    (x : PZero L) (u : U L n) :
    certificateRho n L data hn x u =
      terminalPair n L data hn (u ⊗ₜ[ℤ] x) := rfl

/-- The fundamental evaluation identity
`⟨b(a),ρ(x)⟩=φ(a,x)`. -/
theorem eval_tail_rho (hn : 2 ≤ n) (a : POne n L) (x : PZero L) :
    evalB n L data (certificateTail n L data (by omega) a)
        (certificateRho n L data hn x) =
      terminalPhi n L data hn
        (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x) := by
  rw [certificateTail, LinearMap.comp_apply, evalB_mk,
    certificateRho_apply, terminalPhi_tmul]

theorem certificateRho_d_zero (hn : 2 ≤ n) (a : POne n L) :
    certificateRho n L data hn a.1 = 0 := by
  apply LinearMap.ext
  intro u
  rw [certificateRho_apply, terminalPair_tmul]
  change Theta n L data n hn le_rfl
    (u ⊗ₜ[ℤ] terminalTooth n L a.1) = 0
  have ha : pAugmentation n L a.1 = 0 := a.property
  rw [terminalTooth, LinearMap.comp_apply, LinearMap.comp_apply, ha,
    map_zero, map_zero, TensorProduct.tmul_zero, map_zero]

/-! ## The presentation extension and its alternating form -/

/-- The relation `(b(a),-d(a))` defining the extension `E`. -/
def certificateRelation (hn : 2 ≤ n) :
    POne n L →ₗ[ℤ] CertificateB n L data × PZero L :=
  LinearMap.prod (certificateTail n L data (by omega))
    (-(LinearMap.ker (pAugmentation n L)).subtype)

@[simp] theorem certificateRelation_apply (hn : 2 ≤ n) (a : POne n L) :
    certificateRelation n L data hn a =
      (certificateTail n L data (by omega) a, -a.1) := rfl

/-- The manuscript extension
`E=(B⊕P₀)/span{(b(a),-d(a))}`. -/
abbrev CertificateExtension (hn : 2 ≤ n) :=
  (CertificateB n L data × PZero L) ⧸
    LinearMap.range (certificateRelation n L data hn)

/-- Quotient map to the extension. -/
def certificateExtensionMk (hn : 2 ≤ n) :
    (CertificateB n L data × PZero L) →ₗ[ℤ]
      CertificateExtension n L data hn :=
  Submodule.mkQ (LinearMap.range (certificateRelation n L data hn))

/-- The inclusion `B → E`. -/
def certificateI (hn : 2 ≤ n) :
    CertificateB n L data →ₗ[ℤ] CertificateExtension n L data hn :=
  (certificateExtensionMk n L data hn).comp
    (LinearMap.inl ℤ (CertificateB n L data) (PZero L))

/-- The inclusion `P₀ → E`. -/
def certificateJ (hn : 2 ≤ n) :
    PZero L →ₗ[ℤ] CertificateExtension n L data hn :=
  (certificateExtensionMk n L data hn).comp
    (LinearMap.inr ℤ (CertificateB n L data) (PZero L))

/-- The defining equality `j(d a)=i(b a)` in `E`. -/
theorem certificate_extension_relation (hn : 2 ≤ n) (a : POne n L) :
    certificateJ n L data hn a.1 =
      certificateI n L data hn (certificateTail n L data (by omega) a) := by
  have hzero : certificateExtensionMk n L data hn
      (certificateRelation n L data hn a) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
  apply sub_eq_zero.mp
  change certificateExtensionMk n L data hn (0, a.1) -
      certificateExtensionMk n L data hn
        (certificateTail n L data (by omega) a, 0) = 0
  rw [← map_sub]
  rw [show (0, a.1) - (certificateTail n L data (by omega) a, 0) =
      -(certificateRelation n L data hn a) by
        rw [certificateRelation_apply]
        apply Prod.ext <;> simp]
  rw [map_neg, hzero, neg_zero]

/-- Embed a coefficient in the rational circle. -/
private def coeffToCircle : ZMod (2 ^ data.exponent) →ₗ[ℤ] RatCircle :=
  (zmodToRatCircle (2 ^ data.exponent)).toIntLinearMap

/-- The evaluation term `⟨χ,ρ(x)⟩`, already embedded in `ℚ/ℤ`. -/
private def certificatePair (hn : 2 ≤ n) :
    CertificateB n L data →ₗ[ℤ] PZero L →ₗ[ℤ] RatCircle where
  toFun b := (coeffToCircle n L data).comp
    ((evalB n L data b).comp (certificateRho n L data hn))
  map_add' := by
    intro b c
    apply LinearMap.ext
    intro x
    simp
  map_smul' := by
    intro z b
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, map_zsmul, LinearMap.smul_apply,
      RingHom.id_apply]

/-- The rational `ϑ` term, reduced modulo `ℤ`. -/
private def certificateThetaCircle (hn : 2 ≤ n) :
    PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] RatCircle where
  toFun x := Koszul.QuadraticUCT.ratToCircle.comp
    (terminalTheta n L data hn x)
  map_add' := by intro x y; ext z; simp
  map_smul' := by intro z x; ext y; simp

/-- Formula `(7)` on `B⊕P₀`, before quotienting by the defining relations. -/
def certificateOmegaAmbient (hn : 2 ≤ n) :
    (CertificateB n L data × PZero L) →ₗ[ℤ]
      (CertificateB n L data × PZero L) →ₗ[ℤ] RatCircle where
  toFun p :=
    { toFun := fun r ↦
        certificatePair n L data hn p.1 r.2 -
          certificatePair n L data hn r.1 p.2 +
          certificateThetaCircle n L data hn p.2 r.2
      map_add' := by intro r s; simp; abel
      map_smul' := by intro z r; simp; module }
  map_add' := by
    intro p r
    apply LinearMap.ext
    intro s
    simp
    abel
  map_smul' := by
    intro z p
    apply LinearMap.ext
    intro r
    simp
    module

theorem certificateOmegaAmbient_skew (hn : 2 ≤ n)
    (p r : CertificateB n L data × PZero L) :
    certificateOmegaAmbient n L data hn r p =
      -certificateOmegaAmbient n L data hn p r := by
  change _ - _ + ((terminalTheta n L data hn r.2 p.2 : ℚ) : RatCircle) =
    -(_ - _ + ((terminalTheta n L data hn p.2 r.2 : ℚ) : RatCircle))
  rw [terminalTheta_skew]
  change _ - _ + (-((terminalTheta n L data hn p.2 r.2 : ℚ)) : RatCircle) = _
  abel

theorem certificateOmegaAmbient_self (hn : 2 ≤ n)
    (p : CertificateB n L data × PZero L) :
    certificateOmegaAmbient n L data hn p p = 0 := by
  change _ - _ + ((terminalTheta n L data hn p.2 p.2 : ℚ) : RatCircle) = 0
  rw [terminalTheta_self]
  simp

theorem certificateOmegaAmbient_relation_left (hn : 2 ≤ n)
    (a : POne n L) (r : CertificateB n L data × PZero L) :
    certificateOmegaAmbient n L data hn
      (certificateRelation n L data hn a) r = 0 := by
  rw [certificateRelation_apply]
  change coeffToCircle n L data
        (evalB n L data (certificateTail n L data (by omega) a)
          (certificateRho n L data hn r.2)) -
      coeffToCircle n L data
        (evalB n L data r.1 (certificateRho n L data hn (-a.1))) +
      Koszul.QuadraticUCT.ratToCircle
        (terminalTheta n L data hn (-a.1) r.2) = 0
  have hrho : certificateRho n L data hn (-a.1) = 0 := by
    rw [map_neg, certificateRho_d_zero, neg_zero]
  rw [hrho, map_zero, eval_tail_rho]
  simp only [map_neg, LinearMap.neg_apply]
  rw [terminalTheta_d]
  rw [terminalLiftBilinear_apply]
  have hcast := terminalLift_cast n L data hn
    (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) r.2)
  rw [← hcast]
  change LieRings.zmodToRatCircle (2 ^ data.exponent)
        ((terminalLift n L data hn
          (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) r.2) : ℤ) :
            ZMod (2 ^ data.exponent)) -
      LieRings.zmodToRatCircle (2 ^ data.exponent) 0 + _ = 0
  rw [LieRings.zmodToRatCircle_intCast]
  simp only [map_zero, sub_zero, Koszul.QuadraticUCT.ratToCircle_apply]
  simp

theorem certificateOmegaAmbient_relation_right (hn : 2 ≤ n)
    (a : POne n L) (r : CertificateB n L data × PZero L) :
    certificateOmegaAmbient n L data hn r
      (certificateRelation n L data hn a) = 0 := by
  rw [certificateOmegaAmbient_skew,
    certificateOmegaAmbient_relation_left, neg_zero]

/-- The descended alternating form on `E`. -/
def certificateOmega (hn : 2 ≤ n) :
    CertificateExtension n L data hn →ₗ[ℤ]
      CertificateExtension n L data hn →ₗ[ℤ] RatCircle :=
  (certificateOmegaAmbient n L data hn).liftQ₂
    (LinearMap.range (certificateRelation n L data hn))
    (LinearMap.range (certificateRelation n L data hn))
    (by
      rintro _ ⟨a, rfl⟩
      apply LinearMap.ext
      intro r
      exact certificateOmegaAmbient_relation_left n L data hn a r)
    (by
      rintro _ ⟨a, rfl⟩
      apply LinearMap.ext
      intro r
      exact certificateOmegaAmbient_relation_right n L data hn a r)

@[simp] theorem certificateOmega_mk (hn : 2 ≤ n)
    (p r : CertificateB n L data × PZero L) :
    certificateOmega n L data hn
        (certificateExtensionMk n L data hn p)
        (certificateExtensionMk n L data hn r) =
      certificateOmegaAmbient n L data hn p r := rfl

theorem certificateOmega_skew (hn : 2 ≤ n)
    (p r : CertificateExtension n L data hn) :
    certificateOmega n L data hn r p =
      -certificateOmega n L data hn p r := by
  induction p using Submodule.Quotient.induction_on with
  | _ p =>
    induction r using Submodule.Quotient.induction_on with
    | _ r => exact certificateOmegaAmbient_skew n L data hn p r

theorem certificateOmega_self (hn : 2 ≤ n)
    (p : CertificateExtension n L data hn) :
    certificateOmega n L data hn p p = 0 := by
  induction p using Submodule.Quotient.induction_on with
  | _ p => exact certificateOmegaAmbient_self n L data hn p

private def certificateOmegaAlternating (hn : 2 ≤ n) :
    CertificateExtension n L data hn [⋀^Fin 2]→ₗ[ℤ] RatCircle :=
  AlternatingMap.mk
    (MultilinearMap.mk'
      (fun v ↦ certificateOmega n L data hn (v 0) (v 1))
      (by intro v i x y; fin_cases i <;> simp)
      (by intro v i z x; fin_cases i <;> simp))
    (by
      intro v i j hij hne
      fin_cases i <;> fin_cases j
      · exact (hne rfl).elim
      · change certificateOmega n L data hn (v 0) (v 1) = 0
        have : v 0 = v 1 := by simpa using hij
        rw [this, certificateOmega_self]
      · change certificateOmega n L data hn (v 0) (v 1) = 0
        have : v 1 = v 0 := by simpa using hij
        rw [this, certificateOmega_self]
      · exact (hne rfl).elim)

private def certificateOmegaExterior (hn : 2 ≤ n) :
    (⋀[ℤ]^2 (CertificateExtension n L data hn)) →ₗ[ℤ] RatCircle :=
  exteriorPower.alternatingMapLinearEquiv
    (certificateOmegaAlternating n L data hn)

/-- A polarization of the manuscript alternating form. -/
def certificateH (hn : 2 ≤ n) :
    CertificateExtension n L data hn →ₗ[ℤ]
      CertificateExtension n L data hn →ₗ[ℤ] RatCircle :=
  Classical.choose (IntegralPolarization.exists_bilinear_skew_eq
    (CertificateExtension n L data hn)
      (certificateOmegaExterior n L data hn))

theorem certificateH_skew (hn : 2 ≤ n)
    (p r : CertificateExtension n L data hn) :
    certificateH n L data hn r p - certificateH n L data hn p r =
      certificateOmega n L data hn p r := by
  have h := Classical.choose_spec (IntegralPolarization.exists_bilinear_skew_eq
    (CertificateExtension n L data hn)
      (certificateOmegaExterior n L data hn)) p r
  change certificateH n L data hn r p - certificateH n L data hn p r =
    certificateOmegaExterior n L data hn
      (exteriorPower.ιMulti ℤ 2 ![p, r]) at h
  exact h.trans (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (certificateOmegaAlternating n L data hn) ![p, r])

/-! ## Extraction of the certificate maps -/

/-- The quotient `B=U/qU` is annihilated by `q`. -/
theorem certificateB_q_nsmul (b : CertificateB n L data) :
    (2 ^ data.exponent) • b = 0 := by
  induction b using Submodule.Quotient.induction_on with
  | _ u =>
    change toCertificateB n L data ((2 ^ data.exponent) • u) = 0
    rw [← natCast_zsmul]
    exact toCertificateB_q_smul n L data u

/-- Restrict the second variable of `H` to the copy of `B` in `E`. -/
private def certificateHRightB (hn : 2 ≤ n) :
    CertificateExtension n L data hn →ₗ[ℤ]
      CertificateB n L data →ₗ[ℤ] RatCircle where
  toFun e := (certificateH n L data hn e).comp
    (certificateI n L data hn)
  map_add' := by
    intro e f
    apply LinearMap.ext
    intro b
    simp
  map_smul' := by
    intro z e
    apply LinearMap.ext
    intro b
    simp

/-- The `C`-valued version of the preceding restriction, obtained through
the proved `q`-torsion equivalence. -/
def certificateHRightBCoeff (hn : 2 ≤ n) :
    CertificateExtension n L data hn →ₗ[ℤ]
      CertificateB n L data →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  (ratCircleTorsionLinearMapToZMod (pow_pos (by decide) _)
    (certificateB_q_nsmul n L data)).comp
      (certificateHRightB n L data hn)

@[simp] theorem certificateHRightBCoeff_cast (hn : 2 ≤ n)
    (e : CertificateExtension n L data hn) (b : CertificateB n L data) :
    zmodToRatCircle (2 ^ data.exponent)
        (certificateHRightBCoeff n L data hn e b) =
      certificateH n L data hn e (certificateI n L data hn b) := by
  exact zmodToRatCircle_torsionLinearMapToZMod
    (pow_pos (by decide) _) (certificateB_q_nsmul n L data)
      (certificateHRightB n L data hn e) b

/-- The manuscript map `α : P₀ → A`. -/
def certificateAlpha (hn : 2 ≤ n) :
    PZero L →ₗ[ℤ] CertificateA n L data :=
  (dualBEquivA n L data).toLinearMap.comp
    ((certificateHRightBCoeff n L data hn).comp
      (certificateJ n L data hn))

/-- The manuscript pairing `λ : B → Hom(B,C)`. -/
def certificateLambda (hn : 2 ≤ n) :
    CertificateB n L data →ₗ[ℤ]
      CertificateB n L data →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  (certificateHRightBCoeff n L data hn).comp
    (certificateI n L data hn)

@[simp] theorem certificateAlpha_eval (hn : 2 ≤ n)
    (x : PZero L) (u : U L n) :
    certificateAlpha n L data hn x u =
      certificateHRightBCoeff n L data hn
        (certificateJ n L data hn x) (toCertificateB n L data u) := rfl

theorem certificateOmega_I_I (hn : 2 ≤ n)
    (b c : CertificateB n L data) :
    certificateOmega n L data hn (certificateI n L data hn b)
      (certificateI n L data hn c) = 0 := by
  change certificateOmegaAmbient n L data hn (b, 0) (c, 0) = 0
  simp [certificateOmegaAmbient]

/-- Symmetry of `λ` is forced by the vanishing of `Ω` on `B×B`. -/
theorem certificateLambda_symm (hn : 2 ≤ n)
    (b c : CertificateB n L data) :
    certificateLambda n L data hn b c =
      certificateLambda n L data hn c b := by
  apply zmodToRatCircle_injective (pow_pos (by decide) _)
  rw [show zmodToRatCircle (2 ^ data.exponent)
        (certificateLambda n L data hn b c) =
      certificateH n L data hn (certificateI n L data hn b)
        (certificateI n L data hn c) from
      certificateHRightBCoeff_cast n L data hn _ _]
  rw [show zmodToRatCircle (2 ^ data.exponent)
        (certificateLambda n L data hn c b) =
      certificateH n L data hn (certificateI n L data hn c)
        (certificateI n L data hn b) from
      certificateHRightBCoeff_cast n L data hn _ _]
  have h := certificateH_skew n L data hn
    (certificateI n L data hn b) (certificateI n L data hn c)
  rw [certificateOmega_I_I] at h
  exact (sub_eq_zero.mp h).symm

/-- The single certificate equation `α ∘ d = λ_* ∘ b`. -/
theorem certificateAlpha_d (hn : 2 ≤ n) (a : POne n L) :
    certificateAlpha n L data hn a.1 =
      dualBEquivA n L data
        (certificateLambda n L data hn
          (certificateTail n L data (by omega) a)) := by
  change dualBEquivA n L data
      (certificateHRightBCoeff n L data hn
        (certificateJ n L data hn a.1)) =
    dualBEquivA n L data
      (certificateHRightBCoeff n L data hn
        (certificateI n L data hn
          (certificateTail n L data (by omega) a)))
  congr 2
  exact certificate_extension_relation n L data hn a

/-! ## The certificate cocycle -/

/-- The manuscript cocycle `ψ(a,x)=b(a)(αx)`. -/
def certificatePsi (hn : 2 ≤ n) :
    Koszul.One (pPresentation n L) 1 →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
  (TensorProduct.lift
    { toFun := fun a ↦
        (evalB n L data (certificateTail n L data (by omega) a)).comp
          (certificateAlpha n L data hn)
      map_add' := by intro a b; ext x; simp
      map_smul' := by intro z a; ext x; simp }).toAddMonoidHom.toIntLinearMap |>.comp
    (TensorProduct.map LinearMap.id (pSymOneEquiv n L).toLinearMap)

@[simp] theorem certificatePsi_tmul (hn : 2 ≤ n)
    (a : POne n L) (x : PZero L) :
    certificatePsi n L data hn
        (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x) =
      evalB n L data (certificateTail n L data (by omega) a)
        (certificateAlpha n L data hn x) := by
  simp only [certificatePsi, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, TensorProduct.lift.tmul]
  change evalB n L data (certificateTail n L data (by omega) a)
    (certificateAlpha n L data hn
      (pSymOneEquiv n L (SymmetricPower.degreeOne (R := ℤ) x))) = _
  rw [show pSymOneEquiv n L (SymmetricPower.degreeOne (R := ℤ) x) = x from
    SymmetricPower.degreeOneLinearEquiv_degreeOne (pSmith n L).ambientBasis x]

/-- `ψ` is a quadratic degree-one cocycle; the proof is exactly the
certificate equation followed by symmetry of `λ`. -/
theorem certificatePsi_dTwo_zero (hn : 2 ≤ n)
    (a a' : POne n L) :
    certificatePsi n L data hn
        (Koszul.dTwo (pPresentation n L) 0
          (exteriorPower.ιMulti ℤ 2 ![a, a'] ⊗ₜ[ℤ]
            SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) = 0 := by
  rw [Koszul.dTwo_wedge_tmul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [map_sub]
  change certificatePsi n L data hn
      (a ⊗ₜ[ℤ] SymmetricPower.insert ℤ (PZero L) 0 a'.1
        (SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) -
    certificatePsi n L data hn
      (a' ⊗ₜ[ℤ] SymmetricPower.insert ℤ (PZero L) 0 a.1
        (SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) = 0
  rw [SymmetricPower.insert_monomialBasis_zero (pSmith n L).ambientBasis a'.1,
    SymmetricPower.insert_monomialBasis_zero (pSmith n L).ambientBasis a.1]
  change certificatePsi n L data hn
      (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) a'.1) -
    certificatePsi n L data hn
      (a' ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) a.1) = 0
  rw [certificatePsi_tmul, certificatePsi_tmul]
  rw [certificateAlpha_d, certificateAlpha_d]
  change certificateLambda n L data hn
      (certificateTail n L data (by omega) a')
      (certificateTail n L data (by omega) a) -
    certificateLambda n L data hn
      (certificateTail n L data (by omega) a)
      (certificateTail n L data (by omega) a') = 0
  rw [certificateLambda_symm]
  exact sub_self _

/-- The pulled-back cocycle on the block presentation `R`. -/
def certificatePsiPullback (hn : 2 ≤ n) :
    Koszul.One (rPresentation n L data (by omega)) 1 →ₗ[ℤ]
      ZMod (2 ^ data.exponent) :=
  (certificatePsi n L data hn).comp
    (Koszul.PresentationHomology.oneMap
      (rPresentation n L data (by omega)) (pPresentation n L)
      (rToP n L data (by omega)) 1)

/-! ## The explicit symmetric coboundary on `R₀` -/

/-- Evaluation of `α(x)` on the image of a `Q₀` element in `U`. -/
private def alphaOnQ (hn : 2 ≤ n) :
    PZero L →ₗ[ℤ] QZero n L →ₗ[ℤ] ZMod (2 ^ data.exponent) where
  toFun x := (certificateAlpha n L data hn x).comp
    (qAugmentation n L data (by omega))
  map_add' := by intro x y; ext z; simp
  map_smul' := by intro c x; ext z; simp

/-- The three-term symmetric form `T` from the manuscript. -/
def certificateCoboundaryForm (hn : 2 ≤ n) :
    (PZero L × QZero n L) →ₗ[ℤ]
      (PZero L × QZero n L) →ₗ[ℤ] ZMod (2 ^ data.exponent) := by
  let fst := LinearMap.fst ℤ (PZero L) (QZero n L)
  let snd := LinearMap.snd ℤ (PZero L) (QZero n L)
  let q : QZero n L →ₗ[ℤ] CertificateB n L data :=
    (toCertificateB n L data).comp (qAugmentation n L data (by omega))
  let first : (PZero L × QZero n L) →ₗ[ℤ]
      (PZero L × QZero n L) →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
    ((alphaOnQ n L data hn).compl₂ snd).comp fst
  let third : (PZero L × QZero n L) →ₗ[ℤ]
      (PZero L × QZero n L) →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
    (((certificateLambda n L data hn).compl₂ q).comp q |>.compl₂ snd).comp snd
  exact -(first + LinearMap.flip first + third)

@[simp] theorem certificateCoboundaryForm_apply (hn : 2 ≤ n)
    (p r : PZero L × QZero n L) :
    certificateCoboundaryForm n L data hn p r =
      -alphaOnQ n L data hn p.1 r.2 -
        alphaOnQ n L data hn r.1 p.2 -
        certificateLambda n L data hn
          (toCertificateB n L data
            (qAugmentation n L data (by omega) p.2))
          (toCertificateB n L data
            (qAugmentation n L data (by omega) r.2)) := by
  simp only [certificateCoboundaryForm, LinearMap.neg_apply,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearMap.flip_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    neg_add_rev]
  abel_nf

theorem certificateCoboundaryForm_symm (hn : 2 ≤ n)
    (p r : PZero L × QZero n L) :
    certificateCoboundaryForm n L data hn p r =
      certificateCoboundaryForm n L data hn r p := by
  rw [certificateCoboundaryForm_apply, certificateCoboundaryForm_apply]
  change -_ - _ - certificateLambda n L data hn _ _ =
    -_ - _ - certificateLambda n L data hn _ _
  rw [certificateLambda_symm]
  abel

/-- The cochain relation `T(∂(a,s),-)=ψ(a,-)` from the manuscript. -/
theorem certificateCoboundaryForm_d (hn : 2 ≤ n)
    (a : POne n L) (s : QOne n L data (by omega))
    (x : PZero L) (y : QZero n L) :
    certificateCoboundaryForm n L data hn
        (rDifferential n L data (by omega) (a, s)) (x, y) =
      evalB n L data (certificateTail n L data (by omega) a)
        (certificateAlpha n L data hn x) := by
  rw [rDifferential_apply]
  rw [certificateCoboundaryForm_apply]
  change -certificateAlpha n L data hn a.1
        (qAugmentation n L data (by omega) y) -
      certificateAlpha n L data hn x
        (qAugmentation n L data (by omega)
          (s.1 - btilde n L data (by omega) a)) -
      certificateLambda n L data hn
        (toCertificateB n L data
          (qAugmentation n L data (by omega)
            (s.1 - btilde n L data (by omega) a)))
        (toCertificateB n L data
          (qAugmentation n L data (by omega) y)) = _
  have hs : qAugmentation n L data (by omega) s.1 = 0 := s.property
  rw [map_sub, hs, qAugmentation_btilde, zero_sub]
  simp only [map_neg]
  have hAlpha : certificateAlpha n L data hn a.1
        (qAugmentation n L data (by omega) y) =
      certificateLambda n L data hn
        (certificateTail n L data (by omega) a)
        (toCertificateB n L data
          (qAugmentation n L data (by omega) y)) := by
    rw [certificateAlpha_d n L data hn a]
    rfl
  rw [hAlpha]
  have hEval : evalB n L data (certificateTail n L data (by omega) a)
        (certificateAlpha n L data hn x) =
      certificateAlpha n L data hn x (pTail n L (by omega) a) := rfl
  rw [hEval, LinearMap.neg_apply]
  change -certificateLambda n L data hn
        (certificateTail n L data (by omega) a)
        (toCertificateB n L data (qAugmentation n L data (by omega) y)) -
      (-certificateAlpha n L data hn x (pTail n L (by omega) a)) -
      (-certificateLambda n L data hn
        (certificateTail n L data (by omega) a)
        (toCertificateB n L data
          (qAugmentation n L data (by omega) y))) =
    certificateAlpha n L data hn x (pTail n L (by omega) a)
  abel

/-! ## The rational lift and the half-Bockstein identity -/

/-- A chosen rational representative of a point of `ℚ/ℤ`. -/
private def circleRepresentative (u : RatCircle) : ℚ :=
  Classical.choose (QuotientAddGroup.mk_surjective u)

private theorem circleRepresentative_cast (u : RatCircle) :
    (circleRepresentative u : RatCircle) = u :=
  Classical.choose_spec (QuotientAddGroup.mk_surjective u)

/-- A based rational lift of `(x,y) ↦ H(jx,jy)`. -/
private def certificateRawLift (hn : 2 ≤ n) :
    PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
  (pSmith n L).ambientBasis.constr ℤ (fun i ↦
    (pSmith n L).ambientBasis.constr ℤ (fun j ↦
      circleRepresentative
        (certificateH n L data hn
          (certificateJ n L data hn ((pSmith n L).ambientBasis i))
          (certificateJ n L data hn ((pSmith n L).ambientBasis j)))))

@[simp] private theorem certificateRawLift_basis (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    certificateRawLift n L data hn ((pSmith n L).ambientBasis i)
        ((pSmith n L).ambientBasis j) =
      circleRepresentative
        (certificateH n L data hn
          (certificateJ n L data hn ((pSmith n L).ambientBasis i))
          (certificateJ n L data hn ((pSmith n L).ambientBasis j))) := by
  simp [certificateRawLift]

/-- The raw lift really reduces to `H(j-,j-)`. -/
private theorem certificateRawLift_cast (hn : 2 ≤ n) (x y : PZero L) :
    (certificateRawLift n L data hn x y : RatCircle) =
      certificateH n L data hn (certificateJ n L data hn x)
        (certificateJ n L data hn y) := by
  let S := pSmith n L
  let f : PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] RatCircle :=
    { toFun := fun x ↦ Koszul.QuadraticUCT.ratToCircle.comp
        (certificateRawLift n L data hn x)
      map_add' := by intro x y; ext z; simp
      map_smul' := by intro z x; ext y; simp }
  let g : PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] RatCircle :=
    { toFun := fun x ↦ (certificateH n L data hn
        (certificateJ n L data hn x)).comp (certificateJ n L data hn)
      map_add' := by intro x y; ext z; simp
      map_smul' := by intro z x; ext y; simp }
  have hfg : f = g := by
    apply S.ambientBasis.ext
    intro i
    apply S.ambientBasis.ext
    intro j
    change (certificateRawLift n L data hn
        (S.ambientBasis i) (S.ambientBasis j) : RatCircle) =
      certificateH n L data hn
        (certificateJ n L data hn (S.ambientBasis i))
        (certificateJ n L data hn (S.ambientBasis j))
    rw [certificateRawLift_basis, circleRepresentative_cast]
  exact LinearMap.congr_fun (LinearMap.congr_fun hfg x) y

private theorem certificateRawDiscrepancy_circle_zero (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    ((certificateRawLift n L data hn ((pSmith n L).ambientBasis j)
          ((pSmith n L).ambientBasis i) -
        certificateRawLift n L data hn ((pSmith n L).ambientBasis i)
          ((pSmith n L).ambientBasis j) -
        terminalTheta n L data hn ((pSmith n L).ambientBasis i)
          ((pSmith n L).ambientBasis j) : ℚ) : RatCircle) = 0 := by
  rw [AddCircle.coe_sub, AddCircle.coe_sub,
    certificateRawLift_cast, certificateRawLift_cast]
  have h := certificateH_skew n L data hn
    (certificateJ n L data hn ((pSmith n L).ambientBasis i))
    (certificateJ n L data hn ((pSmith n L).ambientBasis j))
  have hOmega : certificateOmega n L data hn
      (certificateJ n L data hn ((pSmith n L).ambientBasis i))
      (certificateJ n L data hn ((pSmith n L).ambientBasis j)) =
    (terminalTheta n L data hn ((pSmith n L).ambientBasis i)
      ((pSmith n L).ambientBasis j) : RatCircle) := by
    change certificateOmegaAmbient n L data hn
        (0, (pSmith n L).ambientBasis i)
        (0, (pSmith n L).ambientBasis j) = _
    simp [certificateOmegaAmbient, certificateThetaCircle,
      terminalTheta_basis]
  rw [hOmega] at h
  exact sub_eq_zero.mpr h

/-- Integer discrepancy between the skew part of the raw lift and `ϑ`, on
the fixed Smith basis. -/
private def certificateDiscrepancy (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) : ℤ :=
  Classical.choose ((AddCircle.coe_eq_zero_iff (1 : ℚ)).mp
    (certificateRawDiscrepancy_circle_zero n L data hn i j))

private theorem certificateDiscrepancy_spec (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    (certificateDiscrepancy n L data hn i j : ℚ) =
      certificateRawLift n L data hn ((pSmith n L).ambientBasis j)
          ((pSmith n L).ambientBasis i) -
        certificateRawLift n L data hn ((pSmith n L).ambientBasis i)
          ((pSmith n L).ambientBasis j) -
        terminalTheta n L data hn ((pSmith n L).ambientBasis i)
          ((pSmith n L).ambientBasis j) := by
  unfold certificateDiscrepancy
  simpa only [zsmul_eq_mul, mul_one] using
    Classical.choose_spec ((AddCircle.coe_eq_zero_iff (1 : ℚ)).mp
      (certificateRawDiscrepancy_circle_zero n L data hn i j))

/-- Put the integral skew discrepancy in the strict upper triangle. -/
private def certificateCorrection (hn : 2 ≤ n) :
    PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
  (pSmith n L).ambientBasis.constr ℤ (fun i ↦
    (pSmith n L).ambientBasis.constr ℤ (fun j ↦
      if i < j then (certificateDiscrepancy n L data hn i j : ℚ) else 0))

@[simp] private theorem certificateCorrection_basis (hn : 2 ≤ n)
    (i j : Fin (pSmith n L).rank) :
    certificateCorrection n L data hn ((pSmith n L).ambientBasis i)
        ((pSmith n L).ambientBasis j) =
      if i < j then (certificateDiscrepancy n L data hn i j : ℚ) else 0 := by
  rw [certificateCorrection, Module.Basis.constr_basis,
    Module.Basis.constr_basis]

/-- The corrected rational form `P`. -/
def certificateRationalLift (hn : 2 ≤ n) :
    PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
  certificateRawLift n L data hn + certificateCorrection n L data hn

/-- The triangular correction gives exactly `Pᵀ-P=ϑ`. -/
theorem certificateRationalLift_skew (hn : 2 ≤ n) (x y : PZero L) :
    certificateRationalLift n L data hn y x -
      certificateRationalLift n L data hn x y =
    terminalTheta n L data hn x y := by
  let S := pSmith n L
  let f : PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
    LinearMap.flip (certificateRationalLift n L data hn) -
      certificateRationalLift n L data hn - terminalTheta n L data hn
  have hf : f = 0 := by
    apply S.ambientBasis.ext
    intro i
    apply S.ambientBasis.ext
    intro j
    change certificateRationalLift n L data hn
        ((pSmith n L).ambientBasis j) ((pSmith n L).ambientBasis i) -
      certificateRationalLift n L data hn ((pSmith n L).ambientBasis i)
        ((pSmith n L).ambientBasis j) -
      terminalTheta n L data hn ((pSmith n L).ambientBasis i)
        ((pSmith n L).ambientBasis j) = 0
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [certificateRationalLift, LinearMap.add_apply,
        certificateCorrection_basis, hij, if_pos,
        not_lt_of_ge hij.le, if_false]
      rw [certificateDiscrepancy_spec n L data hn i j]
      ring
    · subst j
      simp only [certificateRationalLift, LinearMap.add_apply,
        certificateCorrection_basis,
        lt_self_iff_false, if_false]
      rw [terminalTheta_self]
      ring
    · have hdisc := certificateDiscrepancy_spec n L data hn j i
      rw [terminalTheta_skew] at hdisc
      simp only [certificateRationalLift, LinearMap.add_apply,
        certificateCorrection_basis, hij, if_pos,
        not_lt_of_ge hij.le, if_false]
      rw [hdisc]
      ring
  have h := LinearMap.congr_fun (LinearMap.congr_fun hf x) y
  change certificateRationalLift n L data hn y x -
      certificateRationalLift n L data hn x y -
        terminalTheta n L data hn x y = 0 at h
  exact sub_eq_zero.mp h

/-- The triangular correction is integral, hence invisible in `ℚ/ℤ`. -/
private theorem certificateCorrection_cast (hn : 2 ≤ n) (x y : PZero L) :
    (certificateCorrection n L data hn x y : RatCircle) = 0 := by
  let S := pSmith n L
  let f : PZero L →ₗ[ℤ] PZero L →ₗ[ℤ] RatCircle :=
    { toFun := fun x ↦ Koszul.QuadraticUCT.ratToCircle.comp
        (certificateCorrection n L data hn x)
      map_add' := by intro x y; ext z; simp
      map_smul' := by intro z x; ext y; simp }
  have hf : f = 0 := by
    apply S.ambientBasis.ext
    intro i
    apply S.ambientBasis.ext
    intro j
    change (certificateCorrection n L data hn
      ((pSmith n L).ambientBasis i) ((pSmith n L).ambientBasis j) :
        RatCircle) = 0
    rw [certificateCorrection_basis]
    by_cases hij : i < j
    · rw [if_pos hij]
      exact Koszul.QuadraticUCT.ratToCircle_intCast _
    · rw [if_neg hij, AddCircle.coe_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun hf x) y

/-- The corrected lift has the same reduction in `ℚ/ℤ` as the raw lift. -/
theorem certificateRationalLift_cast (hn : 2 ≤ n) (x y : PZero L) :
    (certificateRationalLift n L data hn x y : RatCircle) =
      certificateH n L data hn (certificateJ n L data hn x)
        (certificateJ n L data hn y) := by
  change ((certificateRawLift n L data hn x y +
      certificateCorrection n L data hn x y : ℚ) : RatCircle) = _
  rw [AddCircle.coe_add,
    certificateCorrection_cast, add_zero, certificateRawLift_cast]

/-- `q P(x,da)` is an integer.  This is the exact integrality statement
needed to construct the lift of `ψ`. -/
theorem certificateRationalLift_q_d_integer (hn : 2 ≤ n)
    (x : PZero L) (a : POne n L) :
    ∃ z : ℤ, (z : ℚ) =
      (2 ^ data.exponent : ℚ) *
        certificateRationalLift n L data hn x a.1 := by
  have hcast : (certificateRationalLift n L data hn x a.1 : RatCircle) =
      certificateH n L data hn (certificateJ n L data hn x)
        (certificateJ n L data hn a.1) :=
    certificateRationalLift_cast n L data hn x a.1
  rw [certificate_extension_relation] at hcast
  have hq : (2 ^ data.exponent) •
      certificateH n L data hn (certificateJ n L data hn x)
        (certificateI n L data hn
          (certificateTail n L data (by omega) a)) = 0 := by
    rw [← map_nsmul
        (certificateH n L data hn (certificateJ n L data hn x)),
      ← map_nsmul (certificateI n L data hn),
      certificateB_q_nsmul, map_zero, map_zero]
  have hzero : (((2 ^ data.exponent : ℚ) *
      certificateRationalLift n L data hn x a.1 : ℚ) : RatCircle) = 0 := by
    rw [show ((2 ^ data.exponent : ℚ) *
        certificateRationalLift n L data hn x a.1 : RatCircle) =
      (2 ^ data.exponent) •
        (certificateRationalLift n L data hn x a.1 : RatCircle) by
          rw [← AddCircle.coe_nsmul]
          norm_num]
    rw [hcast]
    exact hq
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp hzero
  exact ⟨z, by simpa only [zsmul_eq_mul, mul_one] using hz⟩

/-- The integral lift `ψ̂(a,x)=qP(x,da)`. -/
def certificatePsiLiftBilinear (hn : 2 ≤ n) :
    POne n L →ₗ[ℤ] PZero L →ₗ[ℤ] ℤ :=
  (pSmith n L).relationBasis.constr ℤ (fun i ↦
    (pSmith n L).ambientBasis.constr ℤ (fun j ↦
      Classical.choose (certificateRationalLift_q_d_integer n L data hn
        ((pSmith n L).ambientBasis j) ((pSmith n L).relationBasis i))))

/-- Characterizing equality for the genuinely integral lift. -/
theorem certificatePsiLiftBilinear_spec (hn : 2 ≤ n)
    (a : POne n L) (x : PZero L) :
    (certificatePsiLiftBilinear n L data hn a x : ℚ) =
      (2 ^ data.exponent : ℚ) *
        certificateRationalLift n L data hn x a.1 := by
  let S := pSmith n L
  let castMap : ℤ →ₗ[ℤ] ℚ :=
    (Int.castRingHom ℚ).toIntAlgHom.toLinearMap
  let left : POne n L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
    { toFun := fun a ↦ castMap.comp (certificatePsiLiftBilinear n L data hn a)
      map_add' := by intro a b; ext x; simp
      map_smul' := by
        intro z a
        ext x
        simp only [LinearMap.comp_apply, map_zsmul,
          LinearMap.smul_apply, RingHom.id_apply] }
  let right : POne n L →ₗ[ℤ] PZero L →ₗ[ℤ] ℚ :=
    ((2 ^ data.exponent : ℤ) •
      ((LinearMap.flip (certificateRationalLift n L data hn)).comp
        (LinearMap.ker (pAugmentation n L)).subtype))
  have hlr : left = right := by
    apply S.relationBasis.ext
    intro i
    apply S.ambientBasis.ext
    intro j
    have hcastMap (z : ℤ) : castMap z = (z : ℚ) := rfl
    change castMap (certificatePsiLiftBilinear n L data hn
        (S.relationBasis i) (S.ambientBasis j)) =
      (2 ^ data.exponent : ℤ) •
        certificateRationalLift n L data hn
          (S.ambientBasis j) (S.relationBasis i).1
    rw [hcastMap]
    simp only [zsmul_eq_mul]
    change (certificatePsiLiftBilinear n L data hn
        (S.relationBasis i) (S.ambientBasis j) : ℚ) =
      ((2 ^ data.exponent : ℕ) : ℚ) *
        certificateRationalLift n L data hn
          (S.ambientBasis j) (S.relationBasis i).1
    rw [certificatePsiLiftBilinear, Module.Basis.constr_basis,
      Module.Basis.constr_basis]
    convert Classical.choose_spec
      (certificateRationalLift_q_d_integer n L data hn
        (S.ambientBasis j) (S.relationBasis i)) using 1 <;> norm_num
  have h := LinearMap.congr_fun (LinearMap.congr_fun hlr a) x
  have hcastMap (z : ℤ) : castMap z = (z : ℚ) := rfl
  change castMap (certificatePsiLiftBilinear n L data hn a x) =
    (2 ^ data.exponent : ℤ) •
      certificateRationalLift n L data hn x a.1 at h
  rw [hcastMap] at h
  simp only [zsmul_eq_mul] at h
  convert h using 1 <;> norm_num

/-- `ψ̂` reduces to the cocycle `ψ`. -/
theorem certificatePsiLiftBilinear_cast (hn : 2 ≤ n)
    (a : POne n L) (x : PZero L) :
    (certificatePsiLiftBilinear n L data hn a x :
        ZMod (2 ^ data.exponent)) =
      evalB n L data (certificateTail n L data (by omega) a)
        (certificateAlpha n L data hn x) := by
  apply zmodToRatCircle_injective (pow_pos (by decide) _)
  rw [zmodToRatCircle_intCast]
  calc
    (((certificatePsiLiftBilinear n L data hn a x : ℤ) : ℚ) /
          ((2 ^ data.exponent : ℕ) : ℚ) : RatCircle) =
        (certificateRationalLift n L data hn x a.1 : RatCircle) := by
      congr 1
      rw [certificatePsiLiftBilinear_spec]
      field_simp
      norm_num [Nat.cast_pow, Int.cast_pow]
      ring
    _ = certificateH n L data hn (certificateJ n L data hn x)
          (certificateI n L data hn
            (certificateTail n L data (by omega) a)) := by
      rw [certificateRationalLift_cast, certificate_extension_relation]
    _ = zmodToRatCircle (2 ^ data.exponent)
        (evalB n L data (certificateTail n L data (by omega) a)
          (certificateAlpha n L data hn x)) := by
      exact (certificateHRightBCoeff_cast n L data hn _ _).symm

/-- The integral lift `ψ̂` on the literal quadratic degree-one term. -/
def certificatePsiLift (hn : 2 ≤ n) :
    Koszul.One (pPresentation n L) 1 →ₗ[ℤ] ℤ :=
  (TensorProduct.lift (certificatePsiLiftBilinear n L data hn)
    ).toAddMonoidHom.toIntLinearMap.comp
      (TensorProduct.map LinearMap.id (pSymOneEquiv n L).toLinearMap)

@[simp] theorem certificatePsiLift_tmul (hn : 2 ≤ n)
    (a : POne n L) (x : PZero L) :
    certificatePsiLift n L data hn
        (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x) =
      certificatePsiLiftBilinear n L data hn a x := by
  change certificatePsiLiftBilinear n L data hn a
      (pSymOneEquiv n L (SymmetricPower.degreeOne (R := ℤ) x)) = _
  rw [show pSymOneEquiv n L (SymmetricPower.degreeOne (R := ℤ) x) = x from
    SymmetricPower.degreeOneLinearEquiv_degreeOne (pSmith n L).ambientBasis x]

theorem certificatePsiLift_cast (hn : 2 ≤ n)
    (z : Koszul.One (pPresentation n L) 1) :
    (certificatePsiLift n L data hn z : ZMod (2 ^ data.exponent)) =
      certificatePsi n L data hn z := by
  let castMap : ℤ →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
    (Int.castAddHom (ZMod (2 ^ data.exponent))).toIntLinearMap
  have hmaps : castMap.comp (certificatePsiLift n L data hn) =
      certificatePsi n L data hn := by
    apply (Koszul.QuadraticUCT.oneBasis (pAugmentation n L)
      (pAugmentation_surjective n L) (pSmith n L)).ext
    rintro ⟨i, j⟩
    rw [Koszul.QuadraticUCT.oneBasis_apply]
    change (certificatePsiLift n L data hn
      ((pSmith n L).relationBasis i ⊗ₜ[ℤ]
        SymmetricPower.degreeOne (R := ℤ) ((pSmith n L).ambientBasis j)) :
          ZMod (2 ^ data.exponent)) = _
    rw [certificatePsiLift_tmul]
    exact (certificatePsiLiftBilinear_cast n L data hn _ _).trans
      (certificatePsi_tmul n L data hn _ _).symm
  exact LinearMap.congr_fun hmaps z

/-- The Bockstein numerator of `ψ̂`. -/
def certificatePsiNumeratorBilinear (hn : 2 ≤ n) :
    POne n L →ₗ[ℤ] POne n L →ₗ[ℤ] ℤ :=
  let first := (certificatePsiLiftBilinear n L data hn).compl₂
    (LinearMap.ker (pAugmentation n L)).subtype
  first - LinearMap.flip first

@[simp] theorem certificatePsiNumeratorBilinear_apply (hn : 2 ≤ n)
    (a a' : POne n L) :
    certificatePsiNumeratorBilinear n L data hn a a' =
      certificatePsiLiftBilinear n L data hn a a'.1 -
        certificatePsiLiftBilinear n L data hn a' a.1 := by
  simp [certificatePsiNumeratorBilinear, LinearMap.compl₂_apply,
    LinearMap.flip_apply]

/-- The exact manuscript identity: the numerator for `β(ψ)` is the
undivided numerator defining `ηₙ`. -/
theorem certificatePsiNumerator_eq_terminal (hn : 2 ≤ n)
    (a a' : POne n L) :
    certificatePsiNumeratorBilinear n L data hn a a' =
      terminalNumeratorBilinear n L data hn a a' := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
  rw [certificatePsiNumeratorBilinear_apply,
    Int.cast_sub, certificatePsiLiftBilinear_spec,
    certificatePsiLiftBilinear_spec]
  rw [← mul_sub, certificateRationalLift_skew]
  rw [terminalTheta_d, terminalLiftBilinear_apply,
    terminalNumeratorBilinear_apply]
  have hq : (2 ^ data.exponent : ℚ) ≠ 0 := by positivity
  field_simp

/-! ## Bockstein identities and terminal pullback vanishing -/

/-- The terminal cocycle kills every quadratic degree-two boundary. -/
theorem terminalPhi_dTwo_zero (hn : 2 ≤ n)
    (y : Koszul.Two (pPresentation n L) 0) :
    terminalPhi n L data hn (Koszul.dTwo (pPresentation n L) 0 y) = 0 := by
  let g := (terminalPhi n L data hn).comp
    (Koszul.dTwo (pPresentation n L) 0)
  let t := Koszul.QuadraticUCT.twoToExterior (pAugmentation n L)
    (pAugmentation_surjective n L) (pSmith n L)
  let h : (⋀[ℤ]^2 (POne n L)) →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
    g.comp t.symm.toLinearMap
  have hg : g = 0 := by
    have hh : h = 0 := by
      apply exteriorPower.linearMap_ext
      ext a
      change terminalPhi n L data hn
        (Koszul.dTwo (pPresentation n L) 0
          (t.symm (exteriorPower.ιMulti ℤ 2 a))) = 0
      let y0 := exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil
      have hy0 : t.symm (exteriorPower.ιMulti ℤ 2 a) = y0 := by
        apply t.injective
        rw [t.apply_symm_apply]
        exact (Koszul.QuadraticUCT.twoToExterior_generator
          (pAugmentation n L) (pAugmentation_surjective n L)
            (pSmith n L) a).symm
      rw [hy0]
      change terminalPhi n L data hn
        (Koszul.dTwo (pPresentation n L) 0
          (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ]
            SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) = 0
      rw [Koszul.dTwo_wedge_tmul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_sub]
      change terminalPhi n L data hn
          (a 0 ⊗ₜ[ℤ] SymmetricPower.insert ℤ (PZero L) 0 (a 1).1
            (SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) -
        terminalPhi n L data hn
          (a 1 ⊗ₜ[ℤ] SymmetricPower.insert ℤ (PZero L) 0 (a 0).1
            (SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) = 0
      rw [SymmetricPower.insert_monomialBasis_zero,
        SymmetricPower.insert_monomialBasis_zero]
      change terminalPhi n L data hn
          (a 0 ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (a 1).1) -
        terminalPhi n L data hn
          (a 1 ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (a 0).1) = 0
      rw [terminalPhi_dOne_zero, terminalPhi_dOne_zero, sub_zero]
    apply LinearMap.ext
    intro y
    rw [← t.symm_apply_apply y]
    exact LinearMap.congr_fun hh (t y)
  exact LinearMap.congr_fun hg y

/-- The integral lift of the terminal cocycle `φ`. -/
def terminalPhiIntegralLift (hn : 2 ≤ n) :
    Koszul.QuadraticBockstein.IntegralLift (pPresentation n L)
      (2 ^ data.exponent) where
  cochain := terminalLift n L data hn
  boundary_zero y := by
    change (terminalLift n L data hn
      (Koszul.dTwo (pPresentation n L) 0 y) : ZMod (2 ^ data.exponent)) = 0
    rw [terminalLift_cast]
    exact terminalPhi_dTwo_zero n L data hn y

/-- The Bockstein degree-two quotient attached to the terminal lift `φ̂`.
The numerator is twice the exterior cochain defining `ηₙ`, exactly as in
the manuscript. -/
theorem terminalPhi_bockstein_cochain (hn : 2 ≤ n) :
    Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
      (pow_pos (by decide) _)
      ((terminalLift n L data hn).comp
        (Koszul.dTwo (pPresentation n L) 0))
      (fun y ↦ by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,
          LinearMap.comp_apply, terminalLift_cast]
        exact terminalPhi_dTwo_zero n L data hn y) =
      2 • terminalDividedCochain n L data hn := by
  let f := (terminalLift n L data hn).comp
    (Koszul.dTwo (pPresentation n L) 0)
  let hdiv : ∀ y, ((2 ^ data.exponent : ℕ) : ℤ) ∣ f y := fun y ↦ by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, LinearMap.comp_apply,
      terminalLift_cast]
    exact terminalPhi_dTwo_zero n L data hn y
  change Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
      (pow_pos (by decide) _) f hdiv =
    2 • terminalDividedCochain n L data hn
  apply LinearMap.ext
  intro y
  apply mul_left_cancel₀ (show (2 ^ data.exponent : ℤ) ≠ 0 by positivity)
  have hf := Koszul.QuadraticUCT.mul_divideLinear
    (2 ^ data.exponent) (pow_pos (by decide) _) f hdiv y
  change (2 ^ data.exponent : ℤ) *
      Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
        (pow_pos (by decide) _) f hdiv y =
    (2 ^ data.exponent : ℤ) * (2 * terminalDividedCochain n L data hn y)
  rw [show (2 ^ data.exponent : ℤ) *
      Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
        (pow_pos (by decide) _) f hdiv y = f y from hf]
  rw [show (2 ^ data.exponent : ℤ) *
      (2 * terminalDividedCochain n L data hn y) =
        2 * ((2 ^ data.exponent : ℤ) *
          terminalDividedCochain n L data hn y) by ring,
    terminalDividedCochain_spec]
  let t := Koszul.QuadraticUCT.twoToExterior (pAugmentation n L)
    (pAugmentation_surjective n L) (pSmith n L)
  obtain ⟨w, rfl⟩ := t.symm.surjective y
  change terminalLift n L data hn
      (Koszul.dTwo (pPresentation n L) 0 (t.symm w)) =
    2 * terminalNumeratorExterior n L data hn (t (t.symm w))
  rw [t.apply_symm_apply]
  let lhs : (⋀[ℤ]^2 (POne n L)) →ₗ[ℤ] ℤ := f.comp t.symm.toLinearMap
  let rhs : (⋀[ℤ]^2 (POne n L)) →ₗ[ℤ] ℤ :=
    2 • terminalNumeratorExterior n L data hn
  change lhs w = rhs w
  have hlr : lhs = rhs := by
    apply exteriorPower.linearMap_ext
    ext a
    let y0 := exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ]
      SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil
    have hy0 : t.symm (exteriorPower.ιMulti ℤ 2 a) = y0 := by
      apply t.injective
      rw [t.apply_symm_apply]
      exact (Koszul.QuadraticUCT.twoToExterior_generator
        (pAugmentation n L) (pAugmentation_surjective n L)
          (pSmith n L) a).symm
    change f (t.symm (exteriorPower.ιMulti ℤ 2 a)) =
      2 * terminalNumeratorExterior n L data hn
        (exteriorPower.ιMulti ℤ 2 a)
    rw [hy0]
    change terminalLift n L data hn
        (Koszul.dTwo (pPresentation n L) 0
          (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ]
            SymmetricPower.monomialBasis
              (pSmith n L).ambientBasis 0 Sym.nil)) =
      2 * terminalNumeratorExterior n L data hn
        (exteriorPower.ιMulti ℤ 2 a)
    rw [Koszul.dTwo_wedge_tmul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_sub]
    change terminalLift n L data hn
        (a 0 ⊗ₜ[ℤ] SymmetricPower.insert ℤ (PZero L) 0 (a 1).1
          (SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) -
      terminalLift n L data hn
        (a 1 ⊗ₜ[ℤ] SymmetricPower.insert ℤ (PZero L) 0 (a 0).1
          (SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) = _
    rw [SymmetricPower.insert_monomialBasis_zero
      (pSmith n L).ambientBasis (a 1).1,
      SymmetricPower.insert_monomialBasis_zero
        (pSmith n L).ambientBasis (a 0).1]
    rw [terminalNumeratorExterior_ιMulti]
    change terminalLift n L data hn
        (a 0 ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (a 1).1) -
      terminalLift n L data hn
        (a 1 ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (a 0).1) =
      2 * terminalLift n L data hn
        (a 0 ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (a 1).1)
    have hskew := terminalLift_exterior n L data hn (a 0) (a 1)
    linarith
  exact LinearMap.congr_fun hlr w

/-- The first Bockstein identity from the manuscript: `β(φ)=2ηₙ`. -/
theorem terminalPhi_bockstein_eq_two_eta (hn : 2 ≤ n) :
    Koszul.QuadraticBockstein.character (pPresentation n L)
      (2 ^ data.exponent) (pow_pos (by decide) _)
        (terminalPhiIntegralLift n L data hn) =
      2 • etaPresentation n L data hn := by
  let fphi := (terminalLift n L data hn).comp
    (Koszul.dTwo (pPresentation n L) 0)
  let hdivphi : ∀ y, ((2 ^ data.exponent : ℕ) : ℤ) ∣ fphi y := fun y ↦ by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,
      LinearMap.comp_apply, terminalLift_cast]
    exact terminalPhi_dTwo_zero n L data hn y
  let hphi := Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
    (pow_pos (by decide) _)
    fphi hdivphi
  let pphi : Koszul.QuadraticUCT.RationalPrimitive
      (pAugmentation n L) (pAugmentation_surjective n L) hphi :=
    { value :=
        ({ toFun := fun c ↦ (terminalLift n L data hn c.1 : ℚ) /
              (2 ^ data.exponent : ℚ)
           map_add' := by
             intro a b
             change (terminalLift n L data hn (a.1 + b.1) : ℚ) / _ = _
             rw [show terminalLift n L data hn (a.1 + b.1) =
               terminalLift n L data hn a.1 + terminalLift n L data hn b.1
                 from map_add _ _ _]
             push_cast
             ring
           map_smul' := by
             intro z a
             change (terminalLift n L data hn (z • a.1) : ℚ) / _ =
               (z : ℚ) • ((terminalLift n L data hn a.1 : ℚ) / _)
             rw [show terminalLift n L data hn (z • a.1) =
               z • terminalLift n L data hn a.1 from map_zsmul _ _ _]
             simp only [smul_eq_mul, Int.cast_mul]
             ring } : Koszul.cyclesOne (pPresentation n L) 1 →ₗ[ℤ] ℚ)
      boundary := by
        intro y
        have hs := Koszul.QuadraticUCT.mul_divideLinear
          (2 ^ data.exponent) (pow_pos (by decide) _)
          fphi hdivphi y
        change (terminalLift n L data hn
            (Koszul.dTwo (pPresentation n L) 0 y) : ℚ) /
            (2 ^ data.exponent : ℚ) = (hphi y : ℚ)
        apply (div_eq_iff (by positivity : (2 ^ data.exponent : ℚ) ≠ 0)).2
        have hs' : fphi y = hphi y * (2 ^ data.exponent : ℤ) :=
          hs.symm.trans (mul_comm _ _)
        exact_mod_cast hs' }
  have hco : hphi = 2 • terminalDividedCochain n L data hn :=
    terminalPhi_bockstein_cochain n L data hn
  let peta := Koszul.QuadraticUCT.rationalPrimitive
    (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L)
    (terminalDividedCochain n L data hn)
  let p2eta : Koszul.QuadraticUCT.RationalPrimitive
      (pAugmentation n L) (pAugmentation_surjective n L) hphi :=
    { value := 2 • peta.value
      boundary := by
        intro y
        have hp := peta.boundary y
        have hc := LinearMap.congr_fun hco y
        calc
          2 * peta.value (Koszul.boundaryMapOne (pPresentation n L) 1 y) =
              2 * (terminalDividedCochain n L data hn y : ℚ) :=
            congrArg (fun z : ℚ ↦ 2 * z) hp
          _ = (hphi y : ℚ) := by exact_mod_cast hc.symm }
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective
    (Koszul.boundariesOne (pPresentation n L) 1) x
  rw [Koszul.QuadraticBockstein.character_mk]
  change ((((terminalPhiIntegralLift n L data hn).cochain c.1 : ℤ) : ℚ) /
      ((2 ^ data.exponent : ℕ) : ℚ) : RatCircle) =
    2 • etaPresentation n L data hn
      ((Koszul.boundariesOne (pPresentation n L) 1).mkQ c)
  unfold etaPresentation
  change ((((terminalPhiIntegralLift n L data hn).cochain c.1 : ℤ) : ℚ) /
      ((2 ^ data.exponent : ℕ) : ℚ) : RatCircle) =
    2 • ((Koszul.QuadraticUCT.rationalPrimitive
      (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L)
        (terminalDividedCochain n L data hn)).value c : RatCircle)
  let pcan := Koszul.QuadraticUCT.rationalPrimitive
    (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L)
      hphi
  have hleft : ((pphi.value c : ℚ) : RatCircle) =
      ((pcan.value c : ℚ) : RatCircle) := by
    apply sub_eq_zero.mp
    rw [← AddCircle.coe_sub]
    exact Koszul.QuadraticUCT.rationalCycleExtensions_sub_integer
      (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L)
        hphi pphi c
  have hright : ((p2eta.value c : ℚ) : RatCircle) =
      ((pcan.value c : ℚ) : RatCircle) := by
    apply sub_eq_zero.mp
    rw [← AddCircle.coe_sub]
    exact Koszul.QuadraticUCT.rationalCycleExtensions_sub_integer
      (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L)
        hphi p2eta c
  calc
    ((((terminalPhiIntegralLift n L data hn).cochain c.1 : ℤ) : ℚ) /
        ((2 ^ data.exponent : ℕ) : ℚ) : RatCircle) =
        ((pphi.value c : ℚ) : RatCircle) := by
      congr 1
      change (terminalLift n L data hn c.1 : ℚ) /
          ((2 ^ data.exponent : ℕ) : ℚ) =
        (terminalLift n L data hn c.1 : ℚ) /
          (2 ^ data.exponent : ℚ)
      norm_num
    _ = ((p2eta.value c : ℚ) : RatCircle) := hleft.trans hright.symm
    _ = 2 • ((peta.value c : ℚ) : RatCircle) := by
      change (((2 • peta.value) c : ℚ) : RatCircle) =
        2 • ((peta.value c : ℚ) : RatCircle)
      rw [LinearMap.smul_apply]
      simpa only [Koszul.QuadraticUCT.ratToCircle_apply] using
        (map_zsmul Koszul.QuadraticUCT.ratToCircle
          (2 : ℤ) (peta.value c))

/-- The integral lift of the certificate cocycle `ψ`. -/
def certificatePsiIntegralLift (hn : 2 ≤ n) :
    Koszul.QuadraticBockstein.IntegralLift (pPresentation n L)
      (2 ^ data.exponent) where
  cochain := certificatePsiLift n L data hn
  boundary_zero y := by
    change (certificatePsiLift n L data hn
      (Koszul.dTwo (pPresentation n L) 0 y) : ZMod (2 ^ data.exponent)) = 0
    rw [certificatePsiLift_cast]
    let t := Koszul.QuadraticUCT.twoToExterior (pAugmentation n L)
      (pAugmentation_surjective n L) (pSmith n L)
    rw [← t.symm_apply_apply y]
    let h : (⋀[ℤ]^2 (POne n L)) →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
      (certificatePsi n L data hn).comp
        ((Koszul.dTwo (pPresentation n L) 0).comp t.symm.toLinearMap)
    have hh : h = 0 := by
      apply exteriorPower.linearMap_ext
      ext v
      let y0 := exteriorPower.ιMulti ℤ 2 v ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil
      have hy0 : t.symm (exteriorPower.ιMulti ℤ 2 v) = y0 := by
        apply t.injective
        rw [t.apply_symm_apply]
        exact (Koszul.QuadraticUCT.twoToExterior_generator
          (pAugmentation n L) (pAugmentation_surjective n L)
            (pSmith n L) v).symm
      change certificatePsi n L data hn
        (Koszul.dTwo (pPresentation n L) 0
          (t.symm (exteriorPower.ιMulti ℤ 2 v))) = 0
      rw [hy0]
      exact certificatePsi_dTwo_zero n L data hn (v 0) (v 1)
    exact LinearMap.congr_fun hh (t y)

/-- The Bockstein degree-two quotient of `ψ̂` is literally the terminal
cochain defining `ηₙ`. -/
theorem certificatePsi_bockstein_cochain (hn : 2 ≤ n) :
    Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
      (pow_pos (by decide) _)
      ((certificatePsiLift n L data hn).comp
        (Koszul.dTwo (pPresentation n L) 0))
      (fun y ↦ by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,
          LinearMap.comp_apply]
        exact (certificatePsiIntegralLift n L data hn).boundary_zero y) =
      terminalDividedCochain n L data hn := by
  let f := (certificatePsiLift n L data hn).comp
    (Koszul.dTwo (pPresentation n L) 0)
  let hdiv : ∀ y, ((2 ^ data.exponent : ℕ) : ℤ) ∣ f y := fun y ↦ by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, LinearMap.comp_apply]
    exact (certificatePsiIntegralLift n L data hn).boundary_zero y
  change Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
      (pow_pos (by decide) _) f hdiv =
    terminalDividedCochain n L data hn
  apply LinearMap.ext
  intro y
  apply mul_left_cancel₀ (show (2 ^ data.exponent : ℤ) ≠ 0 by positivity)
  have hf := Koszul.QuadraticUCT.mul_divideLinear
    (2 ^ data.exponent) (pow_pos (by decide) _) f hdiv y
  change (2 ^ data.exponent : ℤ) *
      Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
        (pow_pos (by decide) _) f hdiv y =
    (2 ^ data.exponent : ℤ) * terminalDividedCochain n L data hn y
  rw [show (2 ^ data.exponent : ℤ) *
      Koszul.QuadraticUCT.divideLinear (2 ^ data.exponent)
        (pow_pos (by decide) _) f hdiv y = f y from hf,
    terminalDividedCochain_spec]
  let t := Koszul.QuadraticUCT.twoToExterior (pAugmentation n L)
    (pAugmentation_surjective n L) (pSmith n L)
  have hnum : (certificatePsiLift n L data hn).comp
      (Koszul.dTwo (pPresentation n L) 0) =
    terminalNumerator n L data hn := by
    apply LinearMap.ext
    intro y
    obtain ⟨w, rfl⟩ := t.symm.surjective y
    change certificatePsiLift n L data hn
        (Koszul.dTwo (pPresentation n L) 0 (t.symm w)) =
      terminalNumeratorExterior n L data hn (t (t.symm w))
    rw [t.apply_symm_apply]
    let lhs : (⋀[ℤ]^2 (POne n L)) →ₗ[ℤ] ℤ :=
      ((certificatePsiLift n L data hn).comp
        (Koszul.dTwo (pPresentation n L) 0)).comp t.symm.toLinearMap
    let rhs : (⋀[ℤ]^2 (POne n L)) →ₗ[ℤ] ℤ :=
      terminalNumeratorExterior n L data hn
    change lhs w = rhs w
    have hlr : lhs = rhs := by
      apply exteriorPower.linearMap_ext
      ext a
      let y0 := exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ]
        SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil
      have hy0 : t.symm (exteriorPower.ιMulti ℤ 2 a) = y0 := by
        apply t.injective
        rw [t.apply_symm_apply]
        exact (Koszul.QuadraticUCT.twoToExterior_generator
          (pAugmentation n L) (pAugmentation_surjective n L)
            (pSmith n L) a).symm
      change ((certificatePsiLift n L data hn).comp
          (Koszul.dTwo (pPresentation n L) 0))
          (t.symm (exteriorPower.ιMulti ℤ 2 a)) =
        terminalNumeratorExterior n L data hn
          (exteriorPower.ιMulti ℤ 2 a)
      rw [hy0]
      change certificatePsiLift n L data hn
          (Koszul.dTwo (pPresentation n L) 0
            (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ]
              SymmetricPower.monomialBasis
                (pSmith n L).ambientBasis 0 Sym.nil)) =
        terminalNumeratorExterior n L data hn
          (exteriorPower.ιMulti ℤ 2 a)
      rw [Koszul.dTwo_wedge_tmul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_sub]
      change certificatePsiLift n L data hn
          (a 0 ⊗ₜ[ℤ] SymmetricPower.insert ℤ (PZero L) 0 (a 1).1
            (SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) -
        certificatePsiLift n L data hn
          (a 1 ⊗ₜ[ℤ] SymmetricPower.insert ℤ (PZero L) 0 (a 0).1
            (SymmetricPower.monomialBasis (pSmith n L).ambientBasis 0 Sym.nil)) = _
      rw [SymmetricPower.insert_monomialBasis_zero
        (pSmith n L).ambientBasis (a 1).1,
        SymmetricPower.insert_monomialBasis_zero
          (pSmith n L).ambientBasis (a 0).1]
      rw [terminalNumeratorExterior_ιMulti]
      calc
        certificatePsiLift n L data hn
              (a 0 ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (a 1).1) -
            certificatePsiLift n L data hn
              (a 1 ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (a 0).1) =
            certificatePsiLiftBilinear n L data hn (a 0) (a 1).1 -
              certificatePsiLiftBilinear n L data hn (a 1) (a 0).1 :=
          congrArg₂ (fun x y : ℤ ↦ x - y)
            (certificatePsiLift_tmul n L data hn (a 0) (a 1).1)
            (certificatePsiLift_tmul n L data hn (a 1) (a 0).1)
        _ = certificatePsiNumeratorBilinear n L data hn (a 0) (a 1) :=
          (certificatePsiNumeratorBilinear_apply n L data hn (a 0) (a 1)).symm
        _ = terminalNumeratorBilinear n L data hn (a 0) (a 1) :=
          certificatePsiNumerator_eq_terminal n L data hn (a 0) (a 1)
        _ = terminalLift n L data hn
            (a 0 ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (a 1).1) :=
          terminalNumeratorBilinear_apply n L data hn (a 0) (a 1)
    exact LinearMap.congr_fun hlr w
  exact LinearMap.congr_fun hnum y

/-- The rational primitive used by the Bockstein of `ψ̂`. -/
def certificatePsiPrimitive (hn : 2 ≤ n) :
    Koszul.QuadraticUCT.RationalPrimitive (pAugmentation n L)
      (pAugmentation_surjective n L)
      (terminalDividedCochain n L data hn) where
  value :=
    { toFun := fun c ↦ (certificatePsiLift n L data hn c.1 : ℚ) /
        (2 ^ data.exponent : ℚ)
      map_add' := by
        intro c d
        change (certificatePsiLift n L data hn (c.1 + d.1) : ℚ) / _ = _
        rw [show certificatePsiLift n L data hn (c.1 + d.1) =
          certificatePsiLift n L data hn c.1 +
            certificatePsiLift n L data hn d.1 from map_add _ _ _]
        push_cast
        ring
      map_smul' := by
        intro z c
        change (certificatePsiLift n L data hn (z • c.1) : ℚ) / _ =
          (z : ℚ) • ((certificatePsiLift n L data hn c.1 : ℚ) / _)
        rw [show certificatePsiLift n L data hn (z • c.1) =
          z • certificatePsiLift n L data hn c.1 from map_zsmul _ _ _]
        simp only [smul_eq_mul, Int.cast_mul]
        ring }
  boundary y := by
    change (certificatePsiLift n L data hn
        (Koszul.dTwo (pPresentation n L) 0 y) : ℚ) /
      (2 ^ data.exponent : ℚ) =
        (terminalDividedCochain n L data hn y : ℚ)
    have hs := terminalDividedCochain_spec n L data hn y
    have hnum : certificatePsiLift n L data hn
        (Koszul.dTwo (pPresentation n L) 0 y) =
      terminalNumerator n L data hn y := by
      have hmap := certificatePsi_bockstein_cochain n L data hn
      let fpsi := (certificatePsiLift n L data hn).comp
        (Koszul.dTwo (pPresentation n L) 0)
      let hdivpsi : ∀ x, ((2 ^ data.exponent : ℕ) : ℤ) ∣ fpsi x := fun x ↦ by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, LinearMap.comp_apply]
        exact (certificatePsiIntegralLift n L data hn).boundary_zero x
      have hq := Koszul.QuadraticUCT.mul_divideLinear
        (2 ^ data.exponent) (pow_pos (by decide) _)
        fpsi hdivpsi y
      rw [LinearMap.congr_fun hmap y] at hq
      exact hq.symm.trans hs
    rw [hnum]
    have hsQ : (2 ^ data.exponent : ℚ) *
        (terminalDividedCochain n L data hn y : ℚ) =
      (terminalNumerator n L data hn y : ℚ) := by exact_mod_cast hs
    have hq0 : (2 ^ data.exponent : ℚ) ≠ 0 := by positivity
    apply (div_eq_iff hq0).2
    calc
      (terminalNumerator n L data hn y : ℚ) =
          (2 ^ data.exponent : ℚ) *
            (terminalDividedCochain n L data hn y : ℚ) := hsQ.symm
      _ = (terminalDividedCochain n L data hn y : ℚ) *
          (2 ^ data.exponent : ℚ) := mul_comm _ _

/-- The second Bockstein identity from the manuscript:
`β(ψ)=ηₙ`. -/
theorem certificatePsi_bockstein_eq_eta (hn : 2 ≤ n) :
    Koszul.QuadraticBockstein.character (pPresentation n L)
      (2 ^ data.exponent) (pow_pos (by decide) _)
        (certificatePsiIntegralLift n L data hn) =
      etaPresentation n L data hn := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective
    (Koszul.boundariesOne (pPresentation n L) 1) x
  rw [Koszul.QuadraticBockstein.character_mk]
  change ((((certificatePsiIntegralLift n L data hn).cochain c.1 : ℤ) : ℚ) /
      ((2 ^ data.exponent : ℕ) : ℚ) : RatCircle) =
    etaPresentation n L data hn
      ((Koszul.boundariesOne (pPresentation n L) 1).mkQ c)
  unfold etaPresentation
  let pcan := Koszul.QuadraticUCT.rationalPrimitive
    (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L)
      (terminalDividedCochain n L data hn)
  have hprimitive :
      (((certificatePsiPrimitive n L data hn).value c : ℚ) : RatCircle) =
        ((pcan.value c : ℚ) : RatCircle) := by
    apply sub_eq_zero.mp
    rw [← AddCircle.coe_sub]
    exact Koszul.QuadraticUCT.rationalCycleExtensions_sub_integer
      (pAugmentation n L) (pAugmentation_surjective n L) (pSmith n L)
        (terminalDividedCochain n L data hn)
        (certificatePsiPrimitive n L data hn) c
  calc
    ((((certificatePsiIntegralLift n L data hn).cochain c.1 : ℤ) : ℚ) /
        ((2 ^ data.exponent : ℕ) : ℚ) : RatCircle) =
        (((certificatePsiPrimitive n L data hn).value c : ℚ) : RatCircle) := by
      congr 1
      change (certificatePsiLift n L data hn c.1 : ℚ) /
          ((2 ^ data.exponent : ℕ) : ℚ) =
        (certificatePsiLift n L data hn c.1 : ℚ) /
          (2 ^ data.exponent : ℚ)
      norm_num
    _ = ((pcan.value c : ℚ) : RatCircle) := hprimitive
    _ = Koszul.QuadraticUCT.uctCharacter (pAugmentation n L)
        (pAugmentation_surjective n L) (terminalDividedCochain n L data hn)
          pcan ((Koszul.boundariesOne (pPresentation n L) 1).mkQ c) := by
      exact (Koszul.QuadraticUCT.uctCharacter_mk
        (pAugmentation n L) (pAugmentation_surjective n L)
          (terminalDividedCochain n L data hn) pcan c).symm

/-! ## Coboundary vanishing after pullback to the block presentation -/

/-- The symmetric degree-zero cochain associated with the certificate form
`T`.  Its value on `uv` is the manuscript's `T(u,v)`. -/
def certificateSymmetricCochain (hn : 2 ≤ n) :
    Sym[ℤ] (Fin 2) (PZero L × QZero n L) →ₗ[ℤ]
      ZMod (2 ^ data.exponent) := by
  let m : MultilinearMap ℤ (fun _ : Fin 2 ↦ PZero L × QZero n L)
      (ZMod (2 ^ data.exponent)) :=
    MultilinearMap.mk'
      (fun v ↦ certificateCoboundaryForm n L data hn (v 0) (v 1))
      (by
        intro v i x y
        fin_cases i
        · change certificateCoboundaryForm n L data hn (x + y) (v 1) = _
          rw [map_add]
          rfl
        · exact map_add (certificateCoboundaryForm n L data hn (v 0)) x y)
      (by
        intro v i z x
        fin_cases i
        · change certificateCoboundaryForm n L data hn (z • x) (v 1) = _
          rw [map_zsmul]
          rfl
        · exact map_zsmul (certificateCoboundaryForm n L data hn (v 0)) z x)
  exact SymmetricPower.lift m (by
    intro e x
    change certificateCoboundaryForm n L data hn (x (e 0)) (x (e 1)) =
      certificateCoboundaryForm n L data hn (x 0) (x 1)
    by_cases h0 : e 0 = 0
    · have h10 : e 1 ≠ 0 := by
        intro h1
        have hz : (0 : Fin 2) = 1 := e.injective (h0.trans h1.symm)
        exact Fin.zero_ne_one hz
      rw [h0, Fin.eq_one_of_ne_zero (e 1) h10]
    · have he0 : e 0 = 1 := Fin.eq_one_of_ne_zero (e 0) h0
      have h1 : e 1 = 0 := by
        by_contra h10
        have he1 : e 1 = 1 := Fin.eq_one_of_ne_zero (e 1) h10
        have hz : (0 : Fin 2) = 1 := e.injective (he0.trans he1.symm)
        exact Fin.zero_ne_one hz
      rw [he0, h1]
      exact certificateCoboundaryForm_symm n L data hn _ _)

@[simp] theorem certificateSymmetricCochain_insert (hn : 2 ≤ n)
    (u v : PZero L × QZero n L) :
    certificateSymmetricCochain n L data hn
        (SymmetricPower.insert ℤ (PZero L × QZero n L) 1 u
          (SymmetricPower.degreeOne (R := ℤ) v)) =
      certificateCoboundaryForm n L data hn u v := by
  rw [SymmetricPower.degreeOne_apply, SymmetricPower.insert_tprod]
  rw [certificateSymmetricCochain, SymmetricPower.lift_tprod]
  rfl

/-- The pullback of `ψ` is the literal coboundary `T ∘ d₁`. -/
theorem certificatePsiPullback_eq_coboundary (hn : 2 ≤ n) :
    certificatePsiPullback n L data hn =
      (certificateSymmetricCochain n L data hn).comp
        (Koszul.dOne (rPresentation n L data (by omega)) 1) := by
  apply TensorProduct.ext'
  intro a s
  let e := SymmetricPower.degreeOneLinearEquiv
    ((pSmith n L).ambientBasis.prod (qSmith n L data (by omega)).ambientBasis)
  let z := e s
  have hs : SymmetricPower.degreeOne (R := ℤ) z = s := by
    apply e.injective
    rw [SymmetricPower.degreeOneLinearEquiv_degreeOne]
  rw [← hs]
  rcases a with ⟨a, t⟩
  rcases z with ⟨x, y⟩
  change certificatePsiPullback n L data hn
      ((a, t) ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (x, y)) =
    certificateSymmetricCochain n L data hn
      (Koszul.dOne (rPresentation n L data (by omega)) 1
        ((a, t) ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (x, y)))
  rw [Koszul.dOne_tmul]
  change certificatePsiPullback n L data hn
      ((a, t) ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (x, y)) =
    certificateSymmetricCochain n L data hn
      (SymmetricPower.insert ℤ (PZero L × QZero n L) 1
        (rDifferential n L data (by omega) (a, t))
        (SymmetricPower.degreeOne (R := ℤ) (x, y)))
  rw [certificateSymmetricCochain_insert]
  rw [certificatePsiPullback, LinearMap.comp_apply,
    Koszul.PresentationHomology.oneMap_tmul]
  rw [show SymmetricPower.map (R := ℤ) (ι := Fin 1)
      (rToP n L data (by omega)).genMap
      (SymmetricPower.degreeOne (R := ℤ) (x, y)) =
        SymmetricPower.degreeOne (R := ℤ) x by
    rw [SymmetricPower.degreeOne_apply, SymmetricPower.map_tprod,
      SymmetricPower.degreeOne_apply]
    congr 1
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i]
  change certificatePsi n L data hn
      (a ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x) = _
  rw [certificatePsi_tmul, certificateCoboundaryForm_d]

/-- The pulled-back certificate cocycle has zero Bockstein character. -/
theorem certificatePsi_pullback_bockstein_eq_zero (hn : 2 ≤ n) :
    Koszul.QuadraticBockstein.character
        (rPresentation n L data (by omega)) (2 ^ data.exponent)
        (pow_pos (by decide) _)
        (Koszul.QuadraticBockstein.pullback
          (rPresentation n L data (by omega)) (pPresentation n L)
          (rToP n L data (by omega)) (2 ^ data.exponent)
          (certificatePsiIntegralLift n L data hn)) = 0 := by
  apply Koszul.QuadraticBockstein.character_eq_zero_of_cycles_cast_zero
  intro c
  rw [show (((Koszul.QuadraticBockstein.pullback
      (rPresentation n L data (by omega)) (pPresentation n L)
      (rToP n L data (by omega)) (2 ^ data.exponent)
      (certificatePsiIntegralLift n L data hn)).cochain c.1 : ℤ) :
        ZMod (2 ^ data.exponent)) = certificatePsiPullback n L data hn c.1 by
    change ((certificatePsiLift n L data hn
      (Koszul.PresentationHomology.oneMap
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1 c.1) : ℤ) :
          ZMod (2 ^ data.exponent)) = _
    rw [certificatePsiLift_cast]
    rfl]
  rw [certificatePsiPullback_eq_coboundary]
  change certificateSymmetricCochain n L data hn
      (Koszul.dOne (rPresentation n L data (by omega)) 1 c.1) = 0
  rw [c.property]
  exact map_zero _

/-- Point 5 capstone on the chosen presentations: the terminal character
vanishes after the strict block projection `R → P`. -/
theorem etaPresentation_comp_rToP_eq_zero (hn : 2 ≤ n) :
    (etaPresentation n L data hn).comp
      (Koszul.PresentationHomology.map
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1) = 0 := by
  rw [← certificatePsi_bockstein_eq_eta n L data hn,
    ← Koszul.QuadraticBockstein.character_pullback]
  exact certificatePsi_pullback_bockstein_eq_zero n L data hn

/-- Point 5 capstone in the presentation-independent language of the
manuscript: `ηₙ ∘ L₁S²(π) = 0`. -/
theorem etaTerminal_comp_map_pi_eq_zero (hn : 2 ≤ n) :
    (etaTerminal n L data hn).comp
      (Koszul.FirstDerivedSymmetricPower.map 1 (pi L n)) = 0 := by
  let eR := Koszul.Presentation.homologyComparisonEquiv
    (rPresentation n L data (by omega)) 1
  let eP := Koszul.Presentation.homologyComparisonEquiv (pPresentation n L) 1
  have hnat := Koszul.Presentation.homologyComparison_natural
    (rPresentation n L data (by omega)) (pPresentation n L)
    (rToP n L data (by omega)) 1
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := eR.surjective x
  change etaPresentation n L data hn
      (eP.symm (Koszul.FirstDerivedSymmetricPower.map 1 (pi L n) (eR y))) = 0
  have hnatY := LinearMap.congr_fun hnat y
  have hnatY' : eP
      (Koszul.PresentationHomology.map
        (rPresentation n L data (by omega)) (pPresentation n L)
        (rToP n L data (by omega)) 1 y) =
      Koszul.FirstDerivedSymmetricPower.map 1 (pi L n) (eR y) := by
    simpa only [LinearMap.comp_apply] using hnatY
  rw [← hnatY', eP.symm_apply_apply]
  have hz := LinearMap.congr_fun
    (etaPresentation_comp_rToP_eq_zero n L data hn) y
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hz



end

end LieRings.MetabelianVanishing
