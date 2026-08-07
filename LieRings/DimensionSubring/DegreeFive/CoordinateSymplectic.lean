import LieRings.DimensionSubring.DegreeFive.CoordinateCertificate
import LieRings.DimensionSubring.DegreeFive.ExteriorAlternation
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The symplectic-extension certificate

This file follows Section 5 of `complete_proof_delta5_subset_gamma4.tex`.  Its first result is
the polarization lemma.  We prove it in a slightly stronger and cleaner form than the manuscript:
no finiteness or cyclic decomposition is needed.  The reason is that `ℚ/ℤ` is an injective
Abelian group, so a character of the exterior square extends across the integral alternation
embedding into the tensor square.
-/

namespace LieRings

namespace DegreeFive

namespace Coordinate

open scoped TensorProduct

noncomputable section

abbrev RatCircle := AddCircle (1 : ℚ)

/-- The standard embedding `ℤ/q ↪ ℚ/ℤ`, sending `m` to `m/q`. -/
def zmodToRatCircle (q : ℕ) : ZMod q →+ RatCircle :=
  ZMod.lift q ⟨CharacterModule.int.divByNat q,
    CharacterModule.int.divByNat_self q⟩

@[simp]
theorem zmodToRatCircle_intCast (q : ℕ) (m : ℤ) :
    zmodToRatCircle q (m : ZMod q) =
      ((m : ℚ) / (q : ℚ) : RatCircle) := by
  rw [zmodToRatCircle, ZMod.lift_coe]
  rfl

/-- A `q`-torsion point of `ℚ/ℤ` is represented by a unique class modulo `q`; this definition
chooses that class using the elementary normal form from `AddCircle.nsmul_eq_zero_iff`. -/
def ratCircleTorsionToZMod {q : ℕ} (hq : 0 < q) (u : RatCircle)
    (hu : q • u = 0) : ZMod q :=
  ((AddCircle.nsmul_eq_zero_iff hq).mp hu).choose

theorem zmodToRatCircle_torsionToZMod {q : ℕ} (hq : 0 < q) (u : RatCircle)
    (hu : q • u = 0) :
    zmodToRatCircle q (ratCircleTorsionToZMod hq u hu) = u := by
  let hex := (AddCircle.nsmul_eq_zero_iff hq).mp hu
  let m : ℕ := hex.choose
  have hm : (((m : ℚ) / (q : ℚ) : ℚ) : RatCircle) = u := by
    dsimp only [m]
    simpa only [mul_one] using hex.choose_spec.2
  change zmodToRatCircle q (m : ZMod q) = u
  calc
    zmodToRatCircle q (m : ZMod q) =
        zmodToRatCircle q ((m : ℤ) : ZMod q) := by norm_num
    _ = (((m : ℤ) : ℚ) / (q : ℚ) : RatCircle) :=
      zmodToRatCircle_intCast q (m : ℤ)
    _ = u := by simpa using hm

theorem zmodToRatCircle_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (zmodToRatCircle q) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  ext a
  constructor
  · intro ha
    rw [AddSubgroup.mem_bot]
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
    change zmodToRatCircle q (m : ZMod q) = 0 at ha
    rw [zmodToRatCircle_intCast] at ha
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℚ))).mp ha
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hmQ : (m : ℚ) = (q : ℚ) * (z : ℚ) := by
      simp only [zsmul_eq_mul, mul_one] at hz
      field_simp at hz ⊢
      linarith
    have hmZ : m = (q : ℤ) * z := by exact_mod_cast hmQ
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨z, hmZ⟩
  · intro ha
    change zmodToRatCircle q a = 0
    rw [ha, map_zero]

variable (A : Type*) [AddCommGroup A]

/-- An additive bilinear form, curried as a `ℤ`-linear map. -/
abbrev BilinearForm := A →ₗ[ℤ] A →ₗ[ℤ] RatCircle

/-- An alternating form represented by its universal map on the second exterior power. -/
abbrev ExteriorForm := (⋀[ℤ]^2 A) →ₗ[ℤ] RatCircle

/-- **Polarization without division by two.**  Every alternating `ℚ/ℤ`-valued form is the
skew-symmetrization `Hᵀ-H` of a bilinear form. -/
theorem exists_bilinear_skew_eq (Ω : ExteriorForm A) :
    ∃ H : BilinearForm A,
      ∀ x y, H y x - H x y = Ω (wedgeTwo A x y) := by
  let omegaCharacter : CharacterModule (⋀[ℤ]^2 A) :=
    (-Ω).toAddMonoidHom
  obtain ⟨tensorCharacter, htensor⟩ :=
    CharacterModule.dual_surjective_of_injective
      (exteriorToTensor A)
      (IntegralAlternation.exteriorToTensor_injective (M := A)) omegaCharacter
  let H : BilinearForm A :=
    { toFun := fun x ↦
        { toFun := fun y ↦ tensorCharacter (x ⊗ₜ[ℤ] y)
          map_add' := by
            intro y z
            rw [TensorProduct.tmul_add, map_add]
          map_smul' := by
            intro n y
            calc
              tensorCharacter (x ⊗ₜ[ℤ] (n • y)) =
                  tensorCharacter (n • (x ⊗ₜ[ℤ] y)) := by
                    rw [TensorProduct.tmul_smul]
                    rfl
              _ = n • tensorCharacter (x ⊗ₜ[ℤ] y) :=
                tensorCharacter.map_zsmul _ _ }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        change tensorCharacter ((x + y) ⊗ₜ[ℤ] z) =
          tensorCharacter (x ⊗ₜ[ℤ] z) + tensorCharacter (y ⊗ₜ[ℤ] z)
        rw [TensorProduct.add_tmul, map_add]
      map_smul' := by
        intro n x
        apply LinearMap.ext
        intro y
        change tensorCharacter ((n • x) ⊗ₜ[ℤ] y) =
          n • tensorCharacter (x ⊗ₜ[ℤ] y)
        calc
          tensorCharacter ((n • x) ⊗ₜ[ℤ] y) =
              tensorCharacter (n • (x ⊗ₜ[ℤ] y)) := by
                exact congrArg tensorCharacter
                  (TensorProduct.smul_tmul' (R := ℤ) n x y).symm
          _ = n • tensorCharacter (x ⊗ₜ[ℤ] y) :=
            tensorCharacter.map_zsmul _ _ }
  refine ⟨H, ?_⟩
  intro x y
  have hwedge := congrArg (fun c : CharacterModule (⋀[ℤ]^2 A) ↦
      c (wedgeTwo A x y)) htensor
  change tensorCharacter
      (exteriorToTensor A (wedgeTwo A x y)) =
        -Ω (wedgeTwo A x y) at hwedge
  rw [exteriorToTensor_wedge] at hwedge
  rw [map_sub] at hwedge
  change tensorCharacter (x ⊗ₜ[ℤ] y) - tensorCharacter (y ⊗ₜ[ℤ] x) =
      -Ω (wedgeTwo A x y) at hwedge
  change H x y - H y x = -Ω (wedgeTwo A x y) at hwedge
  apply eq_of_sub_eq_zero
  calc
    (H y x - H x y) - Ω (wedgeTwo A x y) =
        -(H x y - H y x) - Ω (wedgeTwo A x y) := by abel
    _ = 0 := by rw [hwedge]; abel

/-! ## The concrete extension attached to `D,E,B,G` -/

variable {I K : Type*} [Fintype I] [Fintype K] [LinearOrder I]
variable {q : ℕ}

namespace Data

variable (D : Data I K q)

abbrev ExtensionAmbient (_D : Data I K q) := (K → ZMod q) × (I → ℤ)
abbrev ExtensionRelations (_D : Data I K q) := (K → ℤ) × (I → ℤ)

/-- The relation map whose image is generated by `(e_k e_k,0)` and `(B_i,-d_i x_i)`.
Its cokernel is the group `𝓔` in equation `(5)` of the symplectic-extension proof. -/
def extensionRelationMap :
    D.ExtensionRelations →ₗ[ℤ] D.ExtensionAmbient where
  toFun w :=
    (fun k ↦ ((w.1 k * (D.e k : ℤ) : ℤ) : ZMod q) +
      ∑ i, ((w.2 i * D.B i k : ℤ) : ZMod q),
     fun i ↦ -(w.2 i * (D.d i : ℤ)))
  map_add' := by
    intro x y
    apply Prod.ext
    · funext k
      change (((x.1 k + y.1 k) * (D.e k : ℤ) : ℤ) : ZMod q) +
          ∑ i, (((x.2 i + y.2 i) * D.B i k : ℤ) : ZMod q) =
        ((((x.1 k * (D.e k : ℤ) : ℤ) : ZMod q) +
            ∑ i, ((x.2 i * D.B i k : ℤ) : ZMod q)) +
          (((y.1 k * (D.e k : ℤ) : ℤ) : ZMod q) +
            ∑ i, ((y.2 i * D.B i k : ℤ) : ZMod q)))
      push_cast
      simp_rw [add_mul, Finset.sum_add_distrib]
      ring
    · funext i
      change -((x.2 i + y.2 i) * (D.d i : ℤ)) =
        -(x.2 i * (D.d i : ℤ)) + -(y.2 i * (D.d i : ℤ))
      ring
  map_smul' := by
    intro n x
    apply Prod.ext
    · funext k
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      rw [← Int.cast_smul_eq_zsmul (R := ZMod q)]
      simp only [smul_eq_mul]
      change (((n * x.1 k) * (D.e k : ℤ) : ℤ) : ZMod q) +
          ∑ i, (((n * x.2 i) * D.B i k : ℤ) : ZMod q) =
        (n : ZMod q) * ((((x.1 k * (D.e k : ℤ) : ℤ) : ZMod q) +
          ∑ i, ((x.2 i * D.B i k : ℤ) : ZMod q)))
      push_cast
      rw [mul_add, Finset.mul_sum]
      ring
    · funext i
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      change -((n * x.2 i) * (D.d i : ℤ)) =
        n * (-(x.2 i * (D.d i : ℤ)))
      ring

/-- The concrete finite-presentation extension `𝓔`. -/
abbrev Extension :=
  D.ExtensionAmbient ⧸ LinearMap.range D.extensionRelationMap

def extensionMk : D.ExtensionAmbient →ₗ[ℤ] D.Extension :=
  Submodule.mkQ (LinearMap.range D.extensionRelationMap)

def extensionI : (K → ZMod q) →ₗ[ℤ] D.Extension :=
  D.extensionMk.comp (LinearMap.inl ℤ (K → ZMod q) (I → ℤ))

def extensionJ : (I → ℤ) →ₗ[ℤ] D.Extension :=
  D.extensionMk.comp (LinearMap.inr ℤ (K → ZMod q) (I → ℤ))

noncomputable def extensionIBasis (k : K) : D.Extension := by
  classical
  exact D.extensionI (Pi.single k 1)

noncomputable def extensionJBasis (i : I) : D.Extension := by
  classical
  exact D.extensionJ (Pi.single i 1)

theorem extensionMk_relation (w : D.ExtensionRelations) :
    D.extensionMk (D.extensionRelationMap w) = 0 := by
  exact Submodule.Quotient.mk_eq_zero
    (p := LinearMap.range D.extensionRelationMap) |>.mpr ⟨w, rfl⟩

/-- The diagonal `E`-relations inside the extension. -/
theorem extensionI_diagonal_relation (s : K → ℤ) :
    D.extensionI (fun k ↦ ((s k * (D.e k : ℤ) : ℤ) : ZMod q)) = 0 := by
  have h := D.extensionMk_relation (s, (0 : I → ℤ))
  dsimp [extensionRelationMap] at h
  change D.extensionMk
      (fun k ↦ ((s k * (D.e k : ℤ) : ℤ) : ZMod q), 0) = 0
  simpa only [Prod.fst_zero, Prod.snd_zero, zero_mul,
    Int.cast_zero, Finset.sum_const_zero, add_zero, neg_zero] using h

/-- The relations `d_i j(x_i)=i(B_i)` inside the extension, simultaneously for every
integer linear combination of rows. -/
theorem extension_B_d_relation (x : I → ℤ) :
    D.extensionI (fun k ↦ ∑ i, ((x i * D.B i k : ℤ) : ZMod q)) =
      D.extensionJ (fun i ↦ x i * (D.d i : ℤ)) := by
  have h := D.extensionMk_relation ((0 : K → ℤ), x)
  dsimp [extensionRelationMap] at h
  simp only [zero_mul, Int.cast_zero, zero_add] at h
  change D.extensionMk
      (fun k ↦ ∑ i, ((x i * D.B i k : ℤ) : ZMod q),
        fun i ↦ -(x i * (D.d i : ℤ))) = 0 at h
  apply sub_eq_zero.mp
  change D.extensionMk
      (fun k ↦ ∑ i, ((x i * D.B i k : ℤ) : ZMod q), 0) -
        D.extensionMk (0, fun i ↦ x i * (D.d i : ℤ)) = 0
  rw [← map_sub]
  rw [show
    (fun k ↦ ∑ i, ((x i * D.B i k : ℤ) : ZMod q), 0) -
        (0, fun i ↦ x i * (D.d i : ℤ)) =
      (fun k ↦ ∑ i, ((x i * D.B i k : ℤ) : ZMod q),
        fun i ↦ -(x i * (D.d i : ℤ))) by
      apply Prod.ext
      · funext k; simp
      · funext i; simp]
  exact h

/-! ## The lifted skew form `(15)` -/

/-- An integral lift of `Γ` satisfying the exact `D`-skew relation. -/
structure LiftedSkewForm where
  φ : I → I → ℤ
  cast_φ : ∀ i j, (φ i j : ZMod q) = D.gamma i j
  d_skew : ∀ i j,
    (D.d j : ℤ) * φ i j + (D.d i : ℤ) * φ j i = 0

/-- The upper-triangular integral representatives in equation `(15)`. -/
def liftedGammaEntry [NeZero q] (i j : I) : ℤ :=
  if i < j then ZMod.cast (D.gamma i j)
  else if j < i then -(D.dRatio j i : ℤ) * ZMod.cast (D.gamma j i)
  else 0

theorem exists_liftedSkewForm
    (hq : 0 < q) (hD : D.Identities) (hd : ∀ i, 0 < D.d i) :
    Nonempty D.LiftedSkewForm := by
  letI : NeZero q := ⟨hq.ne'⟩
  let φ := D.liftedGammaEntry
  have hcast : ∀ i j, (φ i j : ZMod q) = D.gamma i j := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [φ, liftedGammaEntry, hij, if_pos, ZMod.intCast_zmod_cast]
    · subst j
      simp only [φ, liftedGammaEntry, lt_self_iff_false, if_false, Int.cast_zero]
      exact (hD.gamma_diag i).symm
    · have hji : j < i := hij
      have hnot : ¬ i < j := not_lt_of_ge (le_of_lt hij)
      simp only [φ, liftedGammaEntry, hnot, if_false, hji, if_true, Int.cast_mul,
        Int.cast_neg, ZMod.intCast_zmod_cast]
      have hs := hD.gamma_skew hji
      rw [← ((eq_neg_iff_add_eq_zero).2 hs).symm]
      push_cast
      ring
  have hskew : ∀ i j,
      (D.d j : ℤ) * φ i j + (D.d i : ℤ) * φ j i = 0 := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · have hdvd := hD.d_dvd (le_of_lt hij)
      have hratio : D.d i * D.dRatio i j = D.d j := by
        exact Nat.mul_div_cancel' hdvd
      have hratioZ : (D.d i : ℤ) * (D.dRatio i j : ℤ) = (D.d j : ℤ) := by
        exact_mod_cast hratio
      have hnot : ¬ j < i := not_lt_of_ge (le_of_lt hij)
      simp only [φ, liftedGammaEntry, hij, if_true, hnot, if_false]
      rw [← hratioZ]
      ring
    · subst j
      simp [φ, liftedGammaEntry]
    · have hdvd := hD.d_dvd (le_of_lt hij)
      have hratio : D.d j * D.dRatio j i = D.d i := by
        exact Nat.mul_div_cancel' hdvd
      have hratioZ : (D.d j : ℤ) * (D.dRatio j i : ℤ) = (D.d i : ℤ) := by
        exact_mod_cast hratio
      have hnot : ¬ i < j := not_lt_of_ge (le_of_lt hij)
      simp only [φ, liftedGammaEntry, hij, if_true, hnot, if_false]
      rw [← hratioZ]
      ring
  exact ⟨⟨φ, hcast, hskew⟩⟩

/-! ## The rational alternating correction `ϑ` -/

variable (lift : D.LiftedSkewForm)

def thetaCoeff (hq : 0 < q) (hd : ∀ i, 0 < D.d i) (i j : I) : ℚ :=
  (lift.φ i j : ℚ) / ((q : ℚ) * (D.d i : ℚ))

theorem thetaCoeff_skew (hq : 0 < q) (hd : ∀ i, 0 < D.d i) (i j : I) :
    D.thetaCoeff lift hq hd j i = -D.thetaCoeff lift hq hd i j := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdi0 : (D.d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
  have hdj0 : (D.d j : ℚ) ≠ 0 := by exact_mod_cast (hd j).ne'
  have hskew := lift.d_skew i j
  have hskewQ :
      (D.d j : ℚ) * (lift.φ i j : ℚ) +
        (D.d i : ℚ) * (lift.φ j i : ℚ) = 0 := by exact_mod_cast hskew
  have ha : (D.d i : ℚ) * (lift.φ j i : ℚ) =
      -((D.d j : ℚ) * (lift.φ i j : ℚ)) :=
    (eq_neg_iff_add_eq_zero).2 (by simpa only [add_comm] using hskewQ)
  rw [thetaCoeff, thetaCoeff, ← neg_div]
  apply (div_eq_div_iff (mul_ne_zero hq0 hdj0)
    (mul_ne_zero hq0 hdi0)).2
  calc
    (lift.φ j i : ℚ) * ((q : ℚ) * (D.d i : ℚ)) =
        (q : ℚ) * ((D.d i : ℚ) * (lift.φ j i : ℚ)) := by ring
    _ = (q : ℚ) * (-((D.d j : ℚ) * (lift.φ i j : ℚ))) := by rw [ha]
    _ = (-(lift.φ i j : ℚ)) * ((q : ℚ) * (D.d j : ℚ)) := by ring

/-- The rational bilinear form `ϑ` of equation `(4)`, in coordinates. -/
def theta (hq : 0 < q) (hd : ∀ i, 0 < D.d i) :
    (I → ℤ) →ₗ[ℤ] (I → ℤ) →ₗ[ℤ] ℚ where
  toFun x :=
    { toFun := fun y ↦
        ∑ i, ∑ j, (x i : ℚ) * (y j : ℚ) * D.thetaCoeff lift hq hd i j
      map_add' := by
        intro y z
        simp only [Pi.add_apply, Int.cast_add]
        simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro n y
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Int.cast_mul]
        push_cast
        ring_nf
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change (∑ i, ∑ j, ((x i + y i : ℤ) : ℚ) * (z j : ℚ) *
        D.thetaCoeff lift hq hd i j) =
      (∑ i, ∑ j, (x i : ℚ) * (z j : ℚ) * D.thetaCoeff lift hq hd i j) +
        ∑ i, ∑ j, (y i : ℚ) * (z j : ℚ) * D.thetaCoeff lift hq hd i j
    simp only [Pi.add_apply, Int.cast_add, LinearMap.add_apply]
    simp_rw [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro n x
    apply LinearMap.ext
    intro y
    change (∑ i, ∑ j, (((n * x i : ℤ) : ℚ) * (y j : ℚ) *
        D.thetaCoeff lift hq hd i j)) =
      n • (∑ i, ∑ j, (x i : ℚ) * (y j : ℚ) * D.thetaCoeff lift hq hd i j)
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Int.cast_mul,
      LinearMap.smul_apply]
    push_cast
    ring_nf
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem theta_skew (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (x y : I → ℤ) :
    D.theta lift hq hd y x = -D.theta lift hq hd x y := by
  change (∑ i, ∑ j, (y i : ℚ) * (x j : ℚ) * D.thetaCoeff lift hq hd i j) =
    -(∑ i, ∑ j, (x i : ℚ) * (y j : ℚ) * D.thetaCoeff lift hq hd i j)
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [D.thetaCoeff_skew lift hq hd]
  ring

theorem theta_self (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (x : I → ℤ) : D.theta lift hq hd x x = 0 := by
  have h := D.theta_skew lift hq hd x x
  linarith

/-! ## The alternating form on the presentation extension -/

/-- The pairing of a row modulo `q` with the `G`-image of an integral generator row. -/
def rowPair : (K → ZMod q) →ₗ[ℤ] (I → ℤ) →ₗ[ℤ] ZMod q where
  toFun v :=
    { toFun := fun x ↦
        ∑ k, v k * ∑ i, (x i : ZMod q) * (D.G i k : ZMod q)
      map_add' := by
        intro x y
        change (∑ k, v k * ∑ i, ((x i + y i : ℤ) : ZMod q) *
            (D.G i k : ZMod q)) =
          (∑ k, v k * ∑ i, (x i : ZMod q) * (D.G i k : ZMod q)) +
            ∑ k, v k * ∑ i, (y i : ZMod q) * (D.G i k : ZMod q)
        push_cast
        simp_rw [add_mul, Finset.sum_add_distrib, mul_add]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro n x
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [← Int.cast_smul_eq_zsmul (R := ZMod q)]
        simp only [smul_eq_mul]
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        calc
          v k * ∑ i, (n : ZMod q) * (x i : ZMod q) * (D.G i k : ZMod q) =
              v k * ((n : ZMod q) *
                ∑ i, (x i : ZMod q) * (D.G i k : ZMod q)) := by
                  congr 1
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
          _ = (n : ZMod q) *
              (v k * ∑ i, (x i : ZMod q) * (D.G i k : ZMod q)) := by ring }
  map_add' := by
    intro v w
    apply LinearMap.ext
    intro x
    change (∑ k, (v k + w k) * ∑ i, (x i : ZMod q) * (D.G i k : ZMod q)) =
      (∑ k, v k * ∑ i, (x i : ZMod q) * (D.G i k : ZMod q)) +
        ∑ k, w k * ∑ i, (x i : ZMod q) * (D.G i k : ZMod q)
    simp_rw [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro n v
    apply LinearMap.ext
    intro x
    change (∑ k, (n • v k) *
        ∑ i, (x i : ZMod q) * (D.G i k : ZMod q)) =
      n • (∑ k, v k * ∑ i, (x i : ZMod q) * (D.G i k : ZMod q))
    rw [← Int.cast_smul_eq_zsmul (R := ZMod q)]
    simp only [smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Formula `(7)` on the ambient group before quotienting by the relations. -/
def omegaAmbient (hq : 0 < q) (hd : ∀ i, 0 < D.d i) :
    D.ExtensionAmbient →ₗ[ℤ] D.ExtensionAmbient →ₗ[ℤ] RatCircle where
  toFun p :=
    { toFun := fun r ↦
        zmodToRatCircle q (D.rowPair p.1 r.2) -
          zmodToRatCircle q (D.rowPair r.1 p.2) +
            ((D.theta lift hq hd p.2 r.2 : ℚ) : RatCircle)
      map_add' := by
        intro r s
        change zmodToRatCircle q (D.rowPair p.1 (r.2 + s.2)) -
              zmodToRatCircle q (D.rowPair (r.1 + s.1) p.2) +
                ((D.theta lift hq hd p.2 (r.2 + s.2) : ℚ) : RatCircle) =
          (zmodToRatCircle q (D.rowPair p.1 r.2) -
              zmodToRatCircle q (D.rowPair r.1 p.2) +
                ((D.theta lift hq hd p.2 r.2 : ℚ) : RatCircle)) +
            (zmodToRatCircle q (D.rowPair p.1 s.2) -
              zmodToRatCircle q (D.rowPair s.1 p.2) +
                ((D.theta lift hq hd p.2 s.2 : ℚ) : RatCircle))
        simp only [map_add, LinearMap.add_apply, AddMonoidHom.map_add,
          AddCircle.coe_add]
        abel
      map_smul' := by
        intro n r
        change zmodToRatCircle q (D.rowPair p.1 (n • r.2)) -
              zmodToRatCircle q (D.rowPair (n • r.1) p.2) +
                ((D.theta lift hq hd p.2 (n • r.2) : ℚ) : RatCircle) =
          n • (zmodToRatCircle q (D.rowPair p.1 r.2) -
              zmodToRatCircle q (D.rowPair r.1 p.2) +
                ((D.theta lift hq hd p.2 r.2 : ℚ) : RatCircle))
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, map_zsmul,
          AddCircle.coe_zsmul]
        change n • zmodToRatCircle q (D.rowPair p.1 r.2) -
              n • zmodToRatCircle q (D.rowPair r.1 p.2) +
                n • ((D.theta lift hq hd p.2 r.2 : ℚ) : RatCircle) =
          n • (zmodToRatCircle q (D.rowPair p.1 r.2) -
              zmodToRatCircle q (D.rowPair r.1 p.2) +
                ((D.theta lift hq hd p.2 r.2 : ℚ) : RatCircle))
        rw [smul_add, smul_sub] }
  map_add' := by
    intro p r
    apply LinearMap.ext
    intro s
    change zmodToRatCircle q (D.rowPair (p.1 + r.1) s.2) -
          zmodToRatCircle q (D.rowPair s.1 (p.2 + r.2)) +
            ((D.theta lift hq hd (p.2 + r.2) s.2 : ℚ) : RatCircle) =
      (zmodToRatCircle q (D.rowPair p.1 s.2) -
          zmodToRatCircle q (D.rowPair s.1 p.2) +
            ((D.theta lift hq hd p.2 s.2 : ℚ) : RatCircle)) +
        (zmodToRatCircle q (D.rowPair r.1 s.2) -
          zmodToRatCircle q (D.rowPair s.1 r.2) +
            ((D.theta lift hq hd r.2 s.2 : ℚ) : RatCircle))
    simp only [map_add, LinearMap.add_apply, AddMonoidHom.map_add,
      AddCircle.coe_add]
    abel_nf
  map_smul' := by
    intro n p
    apply LinearMap.ext
    intro r
    change zmodToRatCircle q (D.rowPair (n • p.1) r.2) -
          zmodToRatCircle q (D.rowPair r.1 (n • p.2)) +
            ((D.theta lift hq hd (n • p.2) r.2 : ℚ) : RatCircle) =
      n • (zmodToRatCircle q (D.rowPair p.1 r.2) -
          zmodToRatCircle q (D.rowPair r.1 p.2) +
            ((D.theta lift hq hd p.2 r.2 : ℚ) : RatCircle))
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, map_zsmul,
      AddCircle.coe_zsmul]
    change n • zmodToRatCircle q (D.rowPair p.1 r.2) -
          n • zmodToRatCircle q (D.rowPair r.1 p.2) +
            n • ((D.theta lift hq hd p.2 r.2 : ℚ) : RatCircle) =
      n • (zmodToRatCircle q (D.rowPair p.1 r.2) -
          zmodToRatCircle q (D.rowPair r.1 p.2) +
            ((D.theta lift hq hd p.2 r.2 : ℚ) : RatCircle))
    rw [smul_add, smul_sub]

theorem omegaAmbient_skew (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (p r : D.ExtensionAmbient) :
    D.omegaAmbient lift hq hd r p = -D.omegaAmbient lift hq hd p r := by
  change zmodToRatCircle q (D.rowPair r.1 p.2) -
        zmodToRatCircle q (D.rowPair p.1 r.2) +
          ((D.theta lift hq hd r.2 p.2 : ℚ) : RatCircle) =
    -(zmodToRatCircle q (D.rowPair p.1 r.2) -
        zmodToRatCircle q (D.rowPair r.1 p.2) +
          ((D.theta lift hq hd p.2 r.2 : ℚ) : RatCircle))
  rw [D.theta_skew lift hq hd]
  rw [AddCircle.coe_neg]
  abel

theorem omegaAmbient_self (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (p : D.ExtensionAmbient) : D.omegaAmbient lift hq hd p p = 0 := by
  change zmodToRatCircle q (D.rowPair p.1 p.2) -
        zmodToRatCircle q (D.rowPair p.1 p.2) +
          ((D.theta lift hq hd p.2 p.2 : ℚ) : RatCircle) = 0
  rw [D.theta_self lift hq hd]
  simp

/-! ## Verification on the defining relations -/

def eRow (s : K → ℤ) : K → ZMod q :=
  fun k ↦ ((s k * (D.e k : ℤ) : ℤ) : ZMod q)

def bRow (x : I → ℤ) : K → ZMod q :=
  fun k ↦ ∑ i, ((x i * D.B i k : ℤ) : ZMod q)

def dRow (x : I → ℤ) : I → ℤ :=
  fun i ↦ x i * (D.d i : ℤ)

theorem rowPair_eRow_eq_zero (hD : D.Identities) (s : K → ℤ) (y : I → ℤ) :
    D.rowPair (D.eRow s) y = 0 := by
  classical
  change (∑ k, (((s k * (D.e k : ℤ) : ℤ) : ZMod q) *
      ∑ i, (y i : ZMod q) * (D.G i k : ZMod q))) = 0
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  have h := hD.GE i k
  push_cast
  ring_nf at h ⊢
  rw [h]
  ring

theorem rowPair_dRow_eq_zero (hD : D.Identities)
    (v : K → ZMod q) (x : I → ℤ) :
    D.rowPair v (D.dRow x) = 0 := by
  classical
  change (∑ k, v k * ∑ i,
      (((x i * (D.d i : ℤ) : ℤ) : ZMod q) * (D.G i k : ZMod q))) = 0
  apply Finset.sum_eq_zero
  intro k _
  rw [show (∑ i, (((x i * (D.d i : ℤ) : ℤ) : ZMod q) *
      (D.G i k : ZMod q))) = 0 by
    apply Finset.sum_eq_zero
    intro i _
    have h := hD.DG i k
    push_cast
    ring_nf at h ⊢
    rw [h]
    ring]
  ring

theorem rowPair_bRow (x y : I → ℤ) :
    D.rowPair (D.bRow x) y =
      ∑ i, ∑ j, ((x i * y j : ℤ) : ZMod q) * D.gamma i j := by
  classical
  change (∑ k, (∑ i, ((x i * D.B i k : ℤ) : ZMod q)) *
      ∑ j, (y j : ZMod q) * (D.G j k : ZMod q)) =
    ∑ i, ∑ j, ((x i * y j : ℤ) : ZMod q) *
      (∑ k, (D.B i k : ZMod q) * (D.G j k : ZMod q))
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

/-- The rational expression whose class modulo `ℤ` is the `Γ`-pairing. -/
def phiPairRat (x y : I → ℤ) : ℚ :=
  ∑ i, ∑ j, ((x i : ℚ) * (y j : ℚ) * (lift.φ i j : ℚ)) / (q : ℚ)

theorem theta_neg_dRow (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (x y : I → ℤ) :
    D.theta lift hq hd (-D.dRow x) y = -D.phiPairRat lift x y := by
  classical
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  change (∑ i, ∑ j,
      ((-(x i * (D.d i : ℤ)) : ℤ) : ℚ) * (y j : ℚ) *
        ((lift.φ i j : ℚ) / ((q : ℚ) * (D.d i : ℚ)))) =
    -(∑ i, ∑ j,
      ((x i : ℚ) * (y j : ℚ) * (lift.φ i j : ℚ)) / (q : ℚ))
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hdi0 : (D.d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
  push_cast
  field_simp

theorem ratCircle_coe_sum {J : Type*} [Fintype J] (f : J → ℚ) :
    (((∑ j, f j) : ℚ) : RatCircle) = ∑ j, ((f j : ℚ) : RatCircle) := by
  change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) (∑ j, f j) =
    ∑ j, (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) (f j)
  rw [map_sum]

theorem zmod_gammaPair_eq_phiPair (hq : 0 < q) (x y : I → ℤ) :
    zmodToRatCircle q
        (∑ i, ∑ j, ((x i * y j : ℤ) : ZMod q) * D.gamma i j) =
      ((D.phiPairRat lift x y : ℚ) : RatCircle) := by
  classical
  simp only [map_sum]
  rw [phiPairRat, ratCircle_coe_sum]
  simp_rw [ratCircle_coe_sum]
  change (∑ i, ∑ j,
      zmodToRatCircle q (((x i * y j : ℤ) : ZMod q) * D.gamma i j)) =
    ∑ i, ∑ j,
      ((((x i : ℚ) * (y j : ℚ) * (lift.φ i j : ℚ)) / (q : ℚ) : ℚ) :
        RatCircle)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← lift.cast_φ i j]
  calc
    zmodToRatCircle q
        (((x i * y j : ℤ) : ZMod q) * (lift.φ i j : ZMod q)) =
        zmodToRatCircle q ((x i * y j * lift.φ i j : ℤ) : ZMod q) := by
          congr 1
          push_cast
          ring
    _ = ((((x i * y j * lift.φ i j : ℤ) : ℚ) / (q : ℚ) : ℚ) : RatCircle) :=
      zmodToRatCircle_intCast q (x i * y j * lift.φ i j)
    _ = ((((x i : ℚ) * (y j : ℚ) * (lift.φ i j : ℚ)) / (q : ℚ) : ℚ) :
        RatCircle) := by
      congr 1
      push_cast
      ring

/-- Equation `(7)` kills every defining relation in its first argument. -/
theorem omegaAmbient_extensionRelation (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (w : D.ExtensionRelations) (r : D.ExtensionAmbient) :
    D.omegaAmbient lift hq hd (D.extensionRelationMap w) r = 0 := by
  classical
  rcases w with ⟨s, x⟩
  rcases r with ⟨v, y⟩
  change zmodToRatCircle q
        (D.rowPair (D.eRow s + D.bRow x) y) -
      zmodToRatCircle q (D.rowPair v (-D.dRow x)) +
        ((D.theta lift hq hd (-D.dRow x) y : ℚ) : RatCircle) = 0
  rw [map_add, LinearMap.add_apply, D.rowPair_eRow_eq_zero hD, D.rowPair_bRow]
  rw [map_neg, D.rowPair_dRow_eq_zero hD]
  simp only [zero_add, neg_zero, map_zero, sub_zero]
  rw [D.theta_neg_dRow lift hq hd]
  rw [AddCircle.coe_neg]
  rw [D.zmod_gammaPair_eq_phiPair lift hq]
  abel

theorem extensionRelation_range_le_omegaAmbient_ker
    (hq : 0 < q) (hd : ∀ i, 0 < D.d i) (hD : D.Identities) :
    LinearMap.range D.extensionRelationMap ≤
      (D.omegaAmbient lift hq hd).ker := by
  rintro _ ⟨w, rfl⟩
  apply LinearMap.ext
  intro r
  exact D.omegaAmbient_extensionRelation lift hq hd hD w r

theorem extensionRelation_range_le_flip_omegaAmbient_ker
    (hq : 0 < q) (hd : ∀ i, 0 < D.d i) (hD : D.Identities) :
    LinearMap.range D.extensionRelationMap ≤
      (D.omegaAmbient lift hq hd).flip.ker := by
  rintro _ ⟨w, rfl⟩
  apply LinearMap.ext
  intro r
  change D.omegaAmbient lift hq hd r (D.extensionRelationMap w) = 0
  rw [D.omegaAmbient_skew lift hq hd]
  rw [D.omegaAmbient_extensionRelation lift hq hd hD]
  simp

/-- The alternating form `Ω` on the concrete extension `𝒬`. -/
def omega (hq : 0 < q) (hd : ∀ i, 0 < D.d i) (hD : D.Identities) :
    D.Extension →ₗ[ℤ] D.Extension →ₗ[ℤ] RatCircle :=
  (D.omegaAmbient lift hq hd).liftQ₂
    (LinearMap.range D.extensionRelationMap)
    (LinearMap.range D.extensionRelationMap)
    (D.extensionRelation_range_le_omegaAmbient_ker lift hq hd hD)
    (D.extensionRelation_range_le_flip_omegaAmbient_ker lift hq hd hD)

@[simp]
theorem omega_extensionMk (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (p r : D.ExtensionAmbient) :
    D.omega lift hq hd hD (D.extensionMk p) (D.extensionMk r) =
      D.omegaAmbient lift hq hd p r := by
  rfl

theorem omega_skew (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (p r : D.Extension) :
    D.omega lift hq hd hD r p = -D.omega lift hq hd hD p r := by
  induction p using Submodule.Quotient.induction_on with
  | _ p =>
    induction r using Submodule.Quotient.induction_on with
    | _ r => exact D.omegaAmbient_skew lift hq hd p r

theorem omega_self (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (p : D.Extension) :
    D.omega lift hq hd hD p p = 0 := by
  induction p using Submodule.Quotient.induction_on with
  | _ p => exact D.omegaAmbient_self lift hq hd p

/-- The two-variable form as a genuine alternating map. -/
def omegaAlternating (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) : D.Extension [⋀^Fin 2]→ₗ[ℤ] RatCircle where
  toFun v := D.omega lift hq hd hD (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i
    · simp
    · simp
  map_update_smul' v i n x := by
    fin_cases i
    · simp
    · simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change D.omega lift hq hd hD (v 0) (v 1) = 0
      change v 0 = v 1 at hv
      rw [hv]
      exact D.omega_self lift hq hd hD _
    · change D.omega lift hq hd hD (v 0) (v 1) = 0
      change v 1 = v 0 at hv
      rw [hv]
      exact D.omega_self lift hq hd hD _
    · exact (hij rfl).elim

def omegaExterior (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) : ExteriorForm D.Extension :=
  exteriorPower.alternatingMapLinearEquiv (D.omegaAlternating lift hq hd hD)

@[simp]
theorem omegaExterior_wedge (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (p r : D.Extension) :
    D.omegaExterior lift hq hd hD (wedgeTwo D.Extension p r) =
      D.omega lift hq hd hD p r := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (D.omegaAlternating lift hq hd hD) ![p, r]

theorem exists_polarizingForm (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) :
    ∃ H : BilinearForm D.Extension,
      ∀ p r, H r p - H p r = D.omega lift hq hd hD p r := by
  obtain ⟨H, hH⟩ := exists_bilinear_skew_eq D.Extension
    (D.omegaExterior lift hq hd hD)
  refine ⟨H, ?_⟩
  intro p r
  rw [hH]
  exact D.omegaExterior_wedge lift hq hd hD p r

/-! ## Coordinate values of the extension and of `Ω` -/

theorem q_nsmul_extensionIBasis (hq : 0 < q) (k : K) :
    q • D.extensionIBasis k = 0 := by
  classical
  change q • D.extensionI (Pi.single k 1) = 0
  rw [← map_nsmul]
  rw [show q • (Pi.single k 1 : K → ZMod q) = 0 by
    funext l
    simp]
  exact map_zero _

theorem e_nsmul_extensionIBasis (k : K) :
    D.e k • D.extensionIBasis k = 0 := by
  classical
  change D.e k • D.extensionI (Pi.single k 1) = 0
  rw [← map_nsmul]
  have h := D.extensionI_diagonal_relation
    (fun l ↦ if l = k then 1 else 0)
  have heq : D.e k • (Pi.single k 1 : K → ZMod q) =
      fun l ↦ (((if l = k then 1 else 0) * (D.e l : ℤ) : ℤ) : ZMod q) := by
    funext l
    by_cases hl : l = k
    · subst l
      simp
    · simp [hl]
  rw [heq]
  exact h

theorem integerRow_eq_sum_single_zmod [DecidableEq K] (b : K → ℤ) :
    (fun k ↦ (b k : ZMod q)) =
      ∑ k, b k • (Pi.single k 1 : K → ZMod q) := by
  classical
  funext l
  rw [Finset.sum_apply, Finset.sum_eq_single l]
  · simp
  · intro k _ hkl
    simp [Pi.single_eq_of_ne hkl.symm]
  · simp

theorem integerRow_eq_sum_single_int (a : I → ℤ) :
    a = ∑ i, a i • (Pi.single i 1 : I → ℤ) := by
  classical
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij.symm]
  · simp

theorem extensionI_integerRow (b : K → ℤ) :
    D.extensionI (fun k ↦ (b k : ZMod q)) =
      ∑ k, b k • D.extensionIBasis k := by
  classical
  calc
    D.extensionI (fun k ↦ (b k : ZMod q)) =
        D.extensionI (∑ k, b k • (Pi.single k 1 : K → ZMod q)) := by
          rw [integerRow_eq_sum_single_zmod (q := q)]
    _ = ∑ k, b k • D.extensionI (Pi.single k 1) := by
      rw [map_sum]
      simp only [map_smul]
    _ = ∑ k, b k • D.extensionIBasis k := by
      rfl

theorem extensionJ_integerRow (a : I → ℤ) :
    D.extensionJ a = ∑ i, a i • D.extensionJBasis i := by
  classical
  calc
    D.extensionJ a =
        D.extensionJ (∑ i, a i • (Pi.single i 1 : I → ℤ)) := by
          exact congrArg D.extensionJ (integerRow_eq_sum_single_int (I := I) a)
    _ = ∑ i, a i • D.extensionJ (Pi.single i 1) := by
      rw [map_sum]
      simp only [map_smul]
    _ = ∑ i, a i • D.extensionJBasis i := by
      rfl

/-- The basis form of the relations `d_i j_i = ∑_k B_{ik} i_k`. -/
theorem extension_basis_relation (i : I) :
    (D.d i : ℤ) • D.extensionJBasis i =
      ∑ k, D.B i k • D.extensionIBasis k := by
  classical
  have h := D.extension_B_d_relation (Pi.single i 1)
  have hleft :
      (fun k ↦ ∑ j, (((Pi.single i 1 : I → ℤ) j * D.B j k : ℤ) : ZMod q)) =
        fun k ↦ (D.B i k : ZMod q) := by
    funext k
    push_cast
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji]
      simp
    · simp
  have hright :
      (fun j ↦ (Pi.single i 1 : I → ℤ) j * (D.d j : ℤ)) =
        Pi.single i (D.d i : ℤ) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hji]
  rw [hleft, hright] at h
  rw [D.extensionI_integerRow] at h
  have hj : D.extensionJ (Pi.single i (D.d i : ℤ)) =
      (D.d i : ℤ) • D.extensionJBasis i := by
    change D.extensionJ (Pi.single i (D.d i : ℤ)) =
      (D.d i : ℤ) • D.extensionJ (Pi.single i 1)
    rw [← map_smul]
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hji]
  rw [hj] at h
  exact h.symm

theorem theta_basis (hq : 0 < q) (hd : ∀ i, 0 < D.d i) (i j : I) :
    D.theta lift hq hd (Pi.single i 1) (Pi.single j 1) =
      D.thetaCoeff lift hq hd i j := by
  classical
  change (∑ a, ∑ b,
      ((Pi.single i 1 : I → ℤ) a : ℚ) *
        ((Pi.single j 1 : I → ℤ) b : ℚ) *
          D.thetaCoeff lift hq hd a b) = D.thetaCoeff lift hq hd i j
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      rw [Pi.single_eq_of_ne hbj]
      simp
    · simp
  · intro a _ hai
    rw [Pi.single_eq_of_ne hai]
    simp
  · simp

theorem rowPair_basis [DecidableEq K] (k : K) (i : I) :
    D.rowPair (Pi.single k 1) (Pi.single i 1) = (D.G i k : ZMod q) := by
  classical
  change (∑ l, (Pi.single k 1 : K → ZMod q) l *
      ∑ j, ((Pi.single i 1 : I → ℤ) j : ZMod q) *
        (D.G j l : ZMod q)) = (D.G i k : ZMod q)
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji]
      simp
    · simp
  · intro l _ hlk
    rw [Pi.single_eq_of_ne hlk]
    simp
  · simp

theorem omega_JJ (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (i j : I) :
    D.omega lift hq hd hD (D.extensionJBasis i) (D.extensionJBasis j) =
      ((D.thetaCoeff lift hq hd i j : ℚ) : RatCircle) := by
  classical
  change D.omegaAmbient lift hq hd
      (0, Pi.single i 1) (0, Pi.single j 1) = _
  change zmodToRatCircle q (D.rowPair 0 (Pi.single j 1)) -
      zmodToRatCircle q (D.rowPair 0 (Pi.single i 1)) +
        ((D.theta lift hq hd (Pi.single i 1) (Pi.single j 1) : ℚ) : RatCircle) = _
  simp only [LinearMap.zero_apply, map_zero]
  rw [D.theta_basis lift hq hd]
  simp

theorem omega_JI (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (i : I) (k : K) :
    D.omega lift hq hd hD (D.extensionJBasis i) (D.extensionIBasis k) =
      -zmodToRatCircle q (D.G i k : ZMod q) := by
  classical
  change D.omegaAmbient lift hq hd
      (0, Pi.single i 1) (Pi.single k 1, 0) = _
  change zmodToRatCircle q (D.rowPair 0 0) -
      zmodToRatCircle q (D.rowPair (Pi.single k 1) (Pi.single i 1)) +
        ((D.theta lift hq hd (Pi.single i 1) 0 : ℚ) : RatCircle) = _
  simp only [LinearMap.zero_apply, map_zero]
  rw [D.rowPair_basis]
  simp

theorem omega_II (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (k l : K) :
    D.omega lift hq hd hD (D.extensionIBasis k) (D.extensionIBasis l) = 0 := by
  classical
  change D.omegaAmbient lift hq hd
      (Pi.single k 1, 0) (Pi.single l 1, 0) = 0
  change zmodToRatCircle q (D.rowPair (Pi.single k 1) 0) -
      zmodToRatCircle q (D.rowPair (Pi.single l 1) 0) +
        ((D.theta lift hq hd 0 0 : ℚ) : RatCircle) = 0
  simp only [map_zero]
  simp

/-! ## Extraction of the certificate matrices -/

theorem polarizing_JI_q_torsion (hq : 0 < q) (H : BilinearForm D.Extension)
    (i : I) (k : K) : q • H (D.extensionJBasis i) (D.extensionIBasis k) = 0 := by
  rw [← map_nsmul]
  rw [D.q_nsmul_extensionIBasis hq]
  exact map_zero _

theorem polarizing_II_q_torsion (hq : 0 < q) (H : BilinearForm D.Extension)
    (k l : K) : q • H (D.extensionIBasis k) (D.extensionIBasis l) = 0 := by
  rw [← map_nsmul]
  rw [D.q_nsmul_extensionIBasis hq]
  exact map_zero _

def alphaOf (hq : 0 < q) (H : BilinearForm D.Extension) (i : I) (k : K) : ZMod q :=
  ratCircleTorsionToZMod hq
    (H (D.extensionJBasis i) (D.extensionIBasis k))
    (D.polarizing_JI_q_torsion hq H i k)

def lambdaOf (hq : 0 < q) (H : BilinearForm D.Extension) (k l : K) : ZMod q :=
  ratCircleTorsionToZMod hq
    (H (D.extensionIBasis k) (D.extensionIBasis l))
    (D.polarizing_II_q_torsion hq H k l)

@[simp]
theorem zmodToRatCircle_alphaOf (hq : 0 < q) (H : BilinearForm D.Extension)
    (i : I) (k : K) :
    zmodToRatCircle q (D.alphaOf hq H i k) =
      H (D.extensionJBasis i) (D.extensionIBasis k) :=
  zmodToRatCircle_torsionToZMod hq _ _

@[simp]
theorem zmodToRatCircle_lambdaOf (hq : 0 < q) (H : BilinearForm D.Extension)
    (k l : K) :
    zmodToRatCircle q (D.lambdaOf hq H k l) =
      H (D.extensionIBasis k) (D.extensionIBasis l) :=
  zmodToRatCircle_torsionToZMod hq _ _

theorem lambdaOf_symmetric (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (H : BilinearForm D.Extension)
    (hH : ∀ p r, H r p - H p r = D.omega lift hq hd hD p r)
    (k l : K) : D.lambdaOf hq H k l = D.lambdaOf hq H l k := by
  apply zmodToRatCircle_injective hq
  rw [D.zmodToRatCircle_lambdaOf, D.zmodToRatCircle_lambdaOf]
  have h := hH (D.extensionIBasis k) (D.extensionIBasis l)
  rw [D.omega_II lift hq hd hD] at h
  exact (sub_eq_zero.mp h).symm

theorem alphaOf_P3 (hq : 0 < q) (H : BilinearForm D.Extension)
    (i : I) (k : K) :
    D.alphaOf hq H i k * (D.e k : ZMod q) = 0 := by
  rw [mul_comm]
  rw [← smul_eq_mul, Nat.cast_smul_eq_nsmul]
  apply zmodToRatCircle_injective hq
  rw [map_nsmul, D.zmodToRatCircle_alphaOf]
  rw [← map_nsmul]
  rw [D.e_nsmul_extensionIBasis]
  simp

theorem lambdaOf_P4 (hq : 0 < q) (H : BilinearForm D.Extension)
    (k l : K) :
    (D.e k : ZMod q) * D.lambdaOf hq H k l = 0 := by
  rw [← smul_eq_mul, Nat.cast_smul_eq_nsmul]
  apply zmodToRatCircle_injective hq
  rw [map_nsmul, D.zmodToRatCircle_lambdaOf]
  rw [map_zero]
  calc
    D.e k • H (D.extensionIBasis k) (D.extensionIBasis l) =
        H (D.e k • D.extensionIBasis k) (D.extensionIBasis l) := by
          exact (congrArg (fun f : D.Extension →ₗ[ℤ] RatCircle ↦
            f (D.extensionIBasis l)) (map_nsmul H (D.e k) (D.extensionIBasis k))).symm
    _ = 0 := by rw [D.e_nsmul_extensionIBasis]; simp

theorem alphaLambda_P2 (hq : 0 < q) (H : BilinearForm D.Extension)
    (i : I) (k : K) :
    (D.d i : ZMod q) * D.alphaOf hq H i k =
      ∑ l, (D.B i l : ZMod q) * D.lambdaOf hq H l k := by
  rw [← smul_eq_mul, Nat.cast_smul_eq_nsmul]
  have hterm (l : K) :
      (D.B i l : ZMod q) * D.lambdaOf hq H l k =
        D.B i l • D.lambdaOf hq H l k := by
    rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]
  simp_rw [hterm]
  apply zmodToRatCircle_injective hq
  rw [map_nsmul, D.zmodToRatCircle_alphaOf]
  simp only [map_sum, map_zsmul, D.zmodToRatCircle_lambdaOf]
  calc
    D.d i • H (D.extensionJBasis i) (D.extensionIBasis k) =
        H ((D.d i : ℤ) • D.extensionJBasis i) (D.extensionIBasis k) := by
          exact (congrArg (fun f : D.Extension →ₗ[ℤ] RatCircle ↦
            f (D.extensionIBasis k))
              (H.map_smul (D.d i : ℤ) (D.extensionJBasis i))).symm
    _ = H (∑ l, D.B i l • D.extensionIBasis l) (D.extensionIBasis k) := by
      rw [D.extension_basis_relation]
    _ = ∑ l, D.B i l • H (D.extensionIBasis l) (D.extensionIBasis k) := by
      rw [map_sum]
      simp only [map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem certificateX_alphaOf_image (hq : 0 < q) (H : BilinearForm D.Extension)
    (a b : I) :
    zmodToRatCircle q (D.certificateX (D.alphaOf hq H) a b) =
      D.d a • H (D.extensionJBasis b) (D.extensionJBasis a) := by
  classical
  unfold certificateX
  have hterm (k : K) :
      (D.B a k : ZMod q) * D.alphaOf hq H b k =
        D.B a k • D.alphaOf hq H b k := by
    rw [← smul_eq_mul, Int.cast_smul_eq_zsmul]
  simp_rw [hterm]
  rw [map_sum]
  simp only [map_zsmul, D.zmodToRatCircle_alphaOf]
  calc
    ∑ k, D.B a k • H (D.extensionJBasis b) (D.extensionIBasis k) =
        H (D.extensionJBasis b)
          (∑ k, D.B a k • D.extensionIBasis k) := by
            rw [map_sum]
            simp only [map_zsmul]
    _ = H (D.extensionJBasis b)
        ((D.d a : ℤ) • D.extensionJBasis a) := by
          rw [D.extension_basis_relation]
    _ = D.d a • H (D.extensionJBasis b) (D.extensionJBasis a) := by
      rw [map_smul, Nat.cast_smul_eq_nsmul]

theorem d_smul_omega_JJ (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) {i j : I} (hij : i < j) :
    D.d j • D.omega lift hq hd hD
        (D.extensionJBasis i) (D.extensionJBasis j) =
      D.dRatio i j • zmodToRatCircle q (D.gamma i j) := by
  have hdvd := hD.d_dvd (le_of_lt hij)
  have hratio : D.d i * D.dRatio i j = D.d j := Nat.mul_div_cancel' hdvd
  rw [D.omega_JJ lift hq hd hD]
  rw [← lift.cast_φ i j]
  rw [zmodToRatCircle_intCast]
  rw [← AddCircle.coe_nsmul, ← AddCircle.coe_nsmul]
  congr 1
  unfold thetaCoeff
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdi0 : (D.d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
  simp only [nsmul_eq_mul]
  push_cast
  field_simp
  have hratioQ : (D.d i : ℚ) * (D.dRatio i j : ℚ) = (D.d j : ℚ) := by
    exact_mod_cast hratio
  rw [← hratioQ]
  ring

theorem alphaLambda_P1 (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (H : BilinearForm D.Extension)
    (hH : ∀ p r, H r p - H p r = D.omega lift hq hd hD p r)
    {i j : I} (hij : i < j) :
    D.certificateX (D.alphaOf hq H) j i -
        (D.dRatio i j : ZMod q) * D.certificateX (D.alphaOf hq H) i j =
      D.gamma j i := by
  have hgamma : D.gamma j i =
      -((D.dRatio i j : ZMod q) * D.gamma i j) :=
    (eq_neg_iff_add_eq_zero).2 (hD.gamma_skew hij)
  rw [hgamma]
  have hmul :
      (D.dRatio i j : ZMod q) * D.certificateX (D.alphaOf hq H) i j =
        D.dRatio i j • D.certificateX (D.alphaOf hq H) i j := by
    rw [← smul_eq_mul, Nat.cast_smul_eq_nsmul]
  have hgammaMul :
      (D.dRatio i j : ZMod q) * D.gamma i j =
        D.dRatio i j • D.gamma i j := by
    rw [← smul_eq_mul, Nat.cast_smul_eq_nsmul]
  apply zmodToRatCircle_injective hq
  rw [map_sub, D.certificateX_alphaOf_image]
  rw [hmul, map_nsmul, D.certificateX_alphaOf_image]
  rw [map_neg, hgammaMul, map_nsmul]
  have hdvd := hD.d_dvd (le_of_lt hij)
  have hratio : D.d i * D.dRatio i j = D.d j := Nat.mul_div_cancel' hdvd
  rw [smul_smul, Nat.mul_comm, hratio]
  have hpol := hH (D.extensionJBasis i) (D.extensionJBasis j)
  have homega := D.d_smul_omega_JJ lift hq hd hD hij
  rw [← homega]
  rw [← hpol]
  module

/-- The matrices extracted from a polarizing form satisfy exactly `(P1)`--`(P4)`. -/
def certificateOf (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) (H : BilinearForm D.Extension)
    (hH : ∀ p r, H r p - H p r = D.omega lift hq hd hD p r) :
    D.Certificate where
  α := D.alphaOf hq H
  Λ := D.lambdaOf hq H
  symmetric := D.lambdaOf_symmetric lift hq hd hD H hH
  P1 := D.alphaLambda_P1 lift hq hd hD H hH
  P2 := D.alphaLambda_P2 hq H
  P3 := D.alphaOf_P3 hq H
  P4 := D.lambdaOf_P4 hq H

/-- Existence of the certificate, corresponding to the symplectic-extension argument in
Section 5 of the coordinate proof. -/
theorem exists_certificate (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) : Nonempty D.Certificate := by
  obtain ⟨lift⟩ := D.exists_liftedSkewForm hq hD hd
  obtain ⟨H, hH⟩ := D.exists_polarizingForm lift hq hd hD
  exact ⟨D.certificateOf lift hq hd hD H hH⟩

/-- The complete coordinate vanishing theorem: the PBW coefficient equations force the
class `ζ` to vanish. -/
theorem coefficientSystem_vanishes (hq : 0 < q) (hd : ∀ i, 0 < D.d i)
    (hD : D.Identities) {ζ : ZMod q} (system : D.CoefficientSystem ζ) :
    ζ = 0 := by
  obtain ⟨cert⟩ := D.exists_certificate hq hd hD
  exact D.certificateCriterion hD system cert

end Data

end

end Coordinate

end DegreeFive

end LieRings
