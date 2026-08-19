import LieRings.Homological.PresentationComparison
import LieRings.Metabelian.FreeEvaluation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The canonical lower-central tower

This file builds the literal tower used in the manuscript from the homogeneous
coordinates of the truncated free metabelian Lie ring.  A relation is always a
full element of `ker ev`; `D k` remembers only its prefix through weight `k`.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)

/-- The deliberately nonminimal free generator module. -/
abbrev Generator := L →₀ ℤ

/-- The free metabelian model, cut off after manuscript weight `n+1`. -/
abbrev FreeModel := FreeMetabelian.Free (Generator L) (n + 1)

/-- The canonical evaluation of the free model. -/
def evaluation : FreeModel n L →ₗ⁅ℤ⁆ L :=
  FreeMetabelian.Evaluation.canonicalEvaluation data.metabelian data.classBound

/-- Full relations in the free model. -/
abbrev Relations := LieHom.ker (evaluation n L data)

/-- `W_k=L/gamma_(k+1)` in Mathlib's zero-based lower-central indexing. -/
abbrev W (k : ℕ) := L ⧸ lowerCentralSeries ℤ L k

/-- `V_k=L/gamma_k`. -/
abbrev V (k : ℕ) := L ⧸ lowerCentralSeries ℤ L (k - 1)

/-- `U_k=gamma_k/gamma_(k+1)`, represented as a quotient of the subtype of
`gamma_k`. -/
abbrev U (k : ℕ) :=
  (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L) ⧸
    (lowerCentralSeries ℤ L k : Submodule ℤ L).comap
      (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype

/-- The quotient map `W_k -> V_k`. -/
def pi (k : ℕ) : W L k →ₗ[ℤ] V L k :=
  (lowerCentralSeries ℤ L k : Submodule ℤ L).mapQ
    (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L)
    LinearMap.id (by
      intro x hx
      change x ∈ lowerCentralSeries ℤ L (k - 1)
      exact LieModule.antitone_lowerCentralSeries ℤ L L (by omega) hx)

@[simp]
theorem pi_mk (k : ℕ) (x : L) :
    pi L k ((lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ x) =
      (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ x := rfl

/-- The canonical map from the lower-central layer into `ker(pi_k)`. -/
def layerToKer (k : ℕ) : U L k →ₗ[ℤ] LinearMap.ker (pi L k) := by
  let N := (lowerCentralSeries ℤ L k : Submodule ℤ L).comap
    (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype
  let f : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L) →ₗ[ℤ]
      LinearMap.ker (pi L k) :=
    { toFun := fun x ↦ ⟨(lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ x.1, by
          change (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ x.1 = 0
          exact Submodule.Quotient.mk_eq_zero _ |>.2 x.2⟩
      map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro z x; apply Subtype.ext; exact map_smul _ _ _ }
  exact N.liftQ f (by
    intro x hx
    apply Subtype.ext
    change (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ x.1 = 0
    exact Submodule.Quotient.mk_eq_zero _ |>.2 hx)

/-- The kernel of `W_k -> V_k` is precisely `U_k`. -/
def layerEquivKer (k : ℕ) : U L k ≃ₗ[ℤ] LinearMap.ker (pi L k) := by
  let f := layerToKer L k
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        rw [Submodule.Quotient.eq]
        have hv := congrArg Subtype.val hxy
        change (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ x.1 =
          (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ y.1 at hv
        change x.1 - y.1 ∈ lowerCentralSeries ℤ L k
        have hz : LieSubmodule.Quotient.mk'
            (lowerCentralSeries ℤ L k) (x.1 - y.1) = 0 := by
          rw [map_sub]
          exact sub_eq_zero.mpr hv
        exact (LieSubmodule.Quotient.mk_eq_zero').mp hz
  · rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
      (lowerCentralSeries ℤ L k : Submodule ℤ L) z
    change (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ x = 0 at hz
    have hx : x ∈ lowerCentralSeries ℤ L (k - 1) :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    let x' : (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L) := ⟨x, hx⟩
    refine ⟨((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
        (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).mkQ x', ?_⟩
    apply Subtype.ext
    rfl

/-- The finite direct sum of manuscript weights at most `k`. -/
abbrev A (k : ℕ) := FreeMetabelian.Free (Generator L) k

/-- Literal projection of the full free model to weights at most `k`. -/
def prLE (k : ℕ) (hk : k ≤ n + 1) :
    FreeModel n L →ₗ[ℤ] A L k :=
  FreeMetabelian.Free.projectPrefix k hk

/-- A full relation projected through weight `k`. -/
def relationPrefix (k : ℕ) (hk : k ≤ n + 1) :
    Relations n L data →ₗ[ℤ] A L k :=
  (prLE n L k hk).domRestrict (Relations n L data)

/-- The canonical relation module `D_k`. -/
def D (k : ℕ) (hk : k ≤ n + 1) : Submodule ℤ (A L k) :=
  LinearMap.range (relationPrefix n L data k hk)

/-- Evaluation of a prefix, prior to quotienting by the next lower-central
term. -/
def prefixEvaluation (k : ℕ) : A L k →ₗ[ℤ] L :=
  FreeMetabelian.Evaluation.linear data.metabelian
    (FreeMetabelian.Evaluation.canonicalGeneratorMap L) k

/-- Augmentation of the canonical presentation of `W_k`. -/
def augmentation (k : ℕ) : A L k →ₗ[ℤ] W L k :=
  (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ.comp
    (prefixEvaluation (n := n) L data k)

theorem evaluation_prefixIncl (k : ℕ) (hk : k ≤ n + 1) (x : A L k) :
    evaluation n L data (FreeMetabelian.Free.prefixIncl k hk x) =
      prefixEvaluation (n := n) L data k x := by
  rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation,
    FreeMetabelian.Evaluation.lieHom_apply]
  exact FreeMetabelian.Evaluation.linear_prefixIncl data.metabelian
    (FreeMetabelian.Evaluation.canonicalGeneratorMap L) k hk x

theorem augmentation_surjective (k : ℕ) (hk : 1 ≤ k) :
    Function.Surjective (augmentation (n := n) L data k) := by
  intro z
  obtain ⟨l, rfl⟩ := Submodule.mkQ_surjective
    (lowerCentralSeries ℤ L k : Submodule ℤ L) z
  let x : A L k := FreeMetabelian.Free.weightIncl 0 hk
    (Finsupp.single l 1)
  refine ⟨x, ?_⟩
  change (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ
      (prefixEvaluation (n := n) L data k x) =
    (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ l
  apply congrArg (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ
  change FreeMetabelian.Evaluation.linear data.metabelian
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L) k
        (FreeMetabelian.Free.incl (⟨0, hk⟩ : Fin k) (Finsupp.single l 1)) = l
  rw [FreeMetabelian.Evaluation.linear_incl]
  change FreeMetabelian.Evaluation.canonicalGeneratorMap L
      (Finsupp.single l 1) = l
  simp

theorem D_le_ker_augmentation (k : ℕ) (hk : k ≤ n + 1) :
    D n L data k hk ≤ LinearMap.ker (augmentation (n := n) L data k) := by
  rintro x ⟨rho, rfl⟩
  change augmentation (n := n) L data k (prLE n L k hk rho.1) = 0
  change (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ
      (prefixEvaluation (n := n) L data k (prLE n L k hk rho.1)) = 0
  rw [← evaluation_prefixIncl n L data k hk]
  have hdiff : rho.1 - FreeMetabelian.Free.prefixIncl k hk
      (prLE n L k hk rho.1) ∈ FreeMetabelian.Free.tail k := by
    intro i hi
    rw [Pi.sub_apply, FreeMetabelian.Free.prefixIncl_apply_of_lt k hk _ i hi]
    change rho.val i - rho.val ⟨i.val, hi.trans_le hk⟩ = 0
    exact sub_self _
  have hevalTail : evaluation n L data
      (rho.1 - FreeMetabelian.Free.prefixIncl k hk (prLE n L k hk rho.1)) ∈
        lowerCentralSeries ℤ L k := by
    change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (rho.1 - FreeMetabelian.Free.prefixIncl k hk
            (prLE n L k hk rho.1)) ∈ lowerCentralSeries ℤ L k
    exact FreeMetabelian.Evaluation.linear_mem_lowerCentralSeries_of_mem_tail
      data.metabelian (FreeMetabelian.Evaluation.canonicalGeneratorMap L) _ hdiff
  have hrhozero : evaluation n L data rho.1 = 0 := rho.property
  rw [map_sub, hrhozero, zero_sub] at hevalTail
  exact (Submodule.Quotient.mk_eq_zero _).2 (by
    simpa only [neg_neg] using
      (lowerCentralSeries ℤ L k).neg_mem hevalTail)

theorem ker_augmentation_le_D (k : ℕ) (hk : k < n + 1) :
    LinearMap.ker (augmentation (n := n) L data k) ≤ D n L data k (Nat.le_of_lt hk) := by
  intro x hx
  change (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ
      (prefixEvaluation (n := n) L data k x) = 0 at hx
  have heval : prefixEvaluation (n := n) L data k x ∈ lowerCentralSeries ℤ L k :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  have hrange := FreeMetabelian.Evaluation.canonicalPiece_range_eq_lowerCentralSeries
    (L := L) data.metabelian k
  have hevalRange : prefixEvaluation (n := n) L data k x ∈ LinearMap.range
      (FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) k) := by
    rw [hrange]
    exact heval
  obtain ⟨y, hy⟩ := hevalRange
  let rho : FreeModel n L :=
    FreeMetabelian.Free.prefixIncl k (Nat.le_of_lt hk) x -
      FreeMetabelian.Free.weightIncl k hk y
  have hrho : rho ∈ Relations n L data := by
    change evaluation n L data rho = 0
    rw [map_sub, evaluation_prefixIncl]
    change prefixEvaluation (n := n) L data k x -
      evaluation n L data (FreeMetabelian.Free.weightIncl k hk y) = 0
    rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
    change prefixEvaluation (n := n) L data k x -
      FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl (⟨k, hk⟩ : Fin (n + 1)) y) = 0
    rw [FreeMetabelian.Evaluation.linear_incl]
    rw [hy]
    exact sub_self _
  refine ⟨⟨rho, hrho⟩, ?_⟩
  change prLE n L k (Nat.le_of_lt hk) rho = x
  rw [map_sub]
  have htop := FreeMetabelian.Free.projectPrefix_weightIncl_eq_zero
    (X := Generator L) k k (Nat.le_of_lt hk) hk le_rfl y
  change FreeMetabelian.Free.projectPrefix k (Nat.le_of_lt hk)
      (FreeMetabelian.Free.prefixIncl k (Nat.le_of_lt hk) x) -
      FreeMetabelian.Free.projectPrefix k (Nat.le_of_lt hk)
        (FreeMetabelian.Free.weightIncl k hk y) = x
  rw [htop, sub_zero]
  exact LinearMap.congr_fun
    (FreeMetabelian.Free.projectPrefix_prefixIncl
      (X := Generator L) k (Nat.le_of_lt hk)) x

theorem exact_D_augmentation (k : ℕ) (hk : k < n + 1) :
    D n L data k (Nat.le_of_lt hk) = LinearMap.ker (augmentation (n := n) L data k) :=
  le_antisymm (D_le_ker_augmentation n L data k (Nat.le_of_lt hk))
    (ker_augmentation_le_D n L data k hk)

/-- Hall basis of the finite prefix. -/
def prefixBasis (k : ℕ) :
    Module.Basis ((i : Fin k) × FreeMetabelian.Free.PieceIndex
      (Fin (Nat.card L)) i.val)
      ℤ (A L k) :=
  let e := Finite.equivFin L
  FreeMetabelian.Free.hallGradedBasis
    ((Finsupp.basisSingleOne (R := ℤ) (ι := L)).reindex e)

/-- The canonical finite free presentation of `W_k`. -/
def presentation (k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) :
    Koszul.Presentation (W L k) := by
  let b := prefixBasis L k
  letI : Module.Free ℤ (A L k) := Module.Free.of_basis b
  letI : Module.Finite ℤ (A L k) := Module.Finite.of_basis b
  letI : Module.Finite ℤ (D n L data k (Nat.le_of_lt hkn)) :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  letI : Module.Free ℤ (D n L data k (Nat.le_of_lt hkn)) :=
    Module.free_of_finite_type_torsion_free'
  exact
    { rel := D n L data k (Nat.le_of_lt hkn)
      gen := A L k
      relAddCommGroup := inferInstance
      genAddCommGroup := inferInstance
      relFree := inferInstance
      genFree := inferInstance
      relFinite := inferInstance
      genFinite := inferInstance
      d := (D n L data k (Nat.le_of_lt hkn)).subtype
      augmentation := augmentation (n := n) L data k
      d_injective := Subtype.val_injective
      augmentation_surjective := augmentation_surjective (n := n) L data k hk
      exact := by
        ext x
        simp only [LinearMap.mem_range]
        rw [← exact_D_augmentation n L data k hkn]
        constructor
        · rintro ⟨y, rfl⟩
          exact y.2
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩ }

/-- Projection of relation modules in the tower. -/
def relationProjection (k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1) :
    D n L data k (Nat.le_of_lt hkn) →ₗ[ℤ]
      D n L data (k - 1) (by omega) :=
  LinearMap.codRestrict (D n L data (k - 1) (by omega))
    ((FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k (by omega)).domRestrict
      (D n L data k (Nat.le_of_lt hkn))) (by
        rintro ⟨x, ⟨rho, rfl⟩⟩
        refine ⟨rho, ?_⟩
        change FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k (by omega)
            (prLE n L k (Nat.le_of_lt hkn) rho.1) =
          prLE n L (k - 1) (by omega) rho.1
        exact LinearMap.congr_fun
          (FreeMetabelian.Free.projectPrefix_trans
            (X := Generator L) (k - 1) k (n + 1) (by omega)
              (Nat.le_of_lt hkn)) rho.1)

theorem relationProjection_surjective (k : ℕ) (hk : 1 ≤ k)
    (hkn : k < n + 1) :
    Function.Surjective (relationProjection n L data k hk hkn) := by
  rintro ⟨x, rho, hrho⟩
  refine ⟨⟨prLE n L k (Nat.le_of_lt hkn) rho.1, ⟨rho, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k (by omega)
      (prLE n L k (Nat.le_of_lt hkn) rho.1) = x
  rw [← hrho]
  exact LinearMap.congr_fun
    (FreeMetabelian.Free.projectPrefix_trans
      (X := Generator L) (k - 1) k (n + 1) (by omega)
        (Nat.le_of_lt hkn)) rho.1

/-- The strict presentation morphism inducing `pi_k`. -/
def presentationProjection (k : ℕ) (hk : 2 ≤ k) (hkn : k < n + 1) :
    Koszul.Presentation.Hom
      (presentation n L data k (by omega) hkn)
      (presentation (n := n) L data (k - 1) (by omega) (by omega))
      (pi L k) where
  relMap := relationProjection n L data k (by omega) hkn
  genMap := FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k (by omega)
  commutes := by ext x; rfl
  induces := by
    ext x
    change A L k at x
    change (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).mkQ
        (prefixEvaluation (n := n) L data (k - 1)
          (FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k (by omega) x)) =
      pi L k ((lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ
        (prefixEvaluation (n := n) L data k x))
    rw [pi_mk]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply LieSubmodule.Quotient.mk_eq_zero'.2
    let low : A L (k - 1) :=
      FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k (by omega) x
    let high : A L k := x - FreeMetabelian.Free.prefixIncl (X := Generator L)
      (k - 1) (by omega) low
    have hhigh : high ∈ FreeMetabelian.Free.tail (k - 1) := by
      intro i hi
      dsimp only [high]
      rw [Pi.sub_apply, FreeMetabelian.Free.prefixIncl_apply_of_lt
        (k - 1) (by omega) low i hi]
      dsimp only [low, FreeMetabelian.Free.prefixMap,
        FreeMetabelian.Free.projectPrefix]
      change x i - x ⟨i.val, hi.trans_le (by omega)⟩ = 0
      exact sub_self _
    have hevalHigh : prefixEvaluation (n := n) L data k high ∈
        lowerCentralSeries ℤ L (k - 1) :=
      FreeMetabelian.Evaluation.linear_mem_lowerCentralSeries_of_mem_tail
        data.metabelian (FreeMetabelian.Evaluation.canonicalGeneratorMap L) _ hhigh
    have hsplit : prefixEvaluation (n := n) L data k high =
        prefixEvaluation (n := n) L data k x -
          prefixEvaluation (n := n) L data (k - 1) low := by
      change prefixEvaluation (n := n) L data k
          (x - FreeMetabelian.Free.prefixIncl (X := Generator L)
            (k - 1) (by omega) low) = _
      rw [map_sub]
      change _ - FreeMetabelian.Evaluation.linear data.metabelian
          (FreeMetabelian.Evaluation.canonicalGeneratorMap L) k
            (FreeMetabelian.Free.prefixIncl (X := Generator L)
              (k - 1) (by omega) low) = _
      rw [FreeMetabelian.Evaluation.linear_prefixIncl]
      rfl
    rw [hsplit] at hevalHigh
    simpa only [neg_sub] using
      (lowerCentralSeries ℤ L (k - 1)).neg_mem hevalHigh

/-- Evaluation of the homogeneous weight-`k` piece in the layer `U_k`. -/
def pieceToU (k : ℕ) (hk : 1 ≤ k) :
    FreeMetabelian.Piece (Generator L) (k - 1) →ₗ[ℤ] U L k :=
  ((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
      (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).mkQ.comp
    (LinearMap.codRestrict (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L)
      (FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (k - 1)) (by
          intro x
          cases k with
          | zero => omega
          | succ r =>
            simpa using
              (show FreeMetabelian.Evaluation.pieceEval data.metabelian
                  (FreeMetabelian.Evaluation.canonicalGeneratorMap L) r x ∈
                    LieModule.lowerCentralSeries ℤ L L r from by
                cases r with
                | zero =>
                  rw [LieModule.lowerCentralSeries_zero]
                  exact LieSubmodule.mem_top _
                | succ q =>
                  exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
                    data.metabelian (FreeMetabelian.Evaluation.canonicalGeneratorMap L) q x)))

theorem pieceToU_surjective (k : ℕ) (hk : 1 ≤ k) :
    Function.Surjective (pieceToU (n := n) L data k hk) := by
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    ((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
      (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype) z
  have hrange := FreeMetabelian.Evaluation.canonicalPiece_range_eq_lowerCentralSeries
    (L := L) data.metabelian (k - 1)
  have hx : x.1 ∈ LinearMap.range
      (FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (k - 1)) := by
    rw [hrange]
    exact x.2
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  apply congrArg (((lowerCentralSeries ℤ L k : Submodule ℤ L).comap
      (lowerCentralSeries ℤ L (k - 1) : Submodule ℤ L).subtype).mkQ)
  apply Subtype.ext
  exact hy

/-- The manuscript intersection `D_k ∩ F_k`, on the homogeneous carrier. -/
abbrev PieceRelations (k : ℕ) (hk : 1 ≤ k) :=
  LinearMap.ker (pieceToU (n := n) L data k hk)

/-- `F_k/(D_k∩F_k) ≃ U_k`. -/
def pieceQuotientEquiv (k : ℕ) (hk : 1 ≤ k) :
    (FreeMetabelian.Piece (Generator L) (k - 1) ⧸
      PieceRelations (n := n) L data k hk) ≃ₗ[ℤ]
      U L k :=
  (pieceToU (n := n) L data k hk).quotKerEquivOfSurjective
    (pieceToU_surjective (n := n) L data k hk)

theorem piece_mem_relations_iff (k : ℕ) (hk : 1 ≤ k) (hkn : k < n + 1)
    (x : FreeMetabelian.Piece (Generator L) (k - 1)) :
    x ∈ PieceRelations (n := n) L data k hk ↔
      FreeMetabelian.Free.weightIncl (k - 1) (by omega) x ∈
        D n L data k (Nat.le_of_lt hkn) := by
  rw [show D n L data k (Nat.le_of_lt hkn) =
      LinearMap.ker (augmentation (n := n) L data k) from
        exact_D_augmentation n L data k hkn]
  change pieceToU (n := n) L data k hk x = 0 ↔
    augmentation (n := n) L data k
      (FreeMetabelian.Free.weightIncl (k - 1) (by omega) x) = 0
  change pieceToU (n := n) L data k hk x = 0 ↔
    (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ
      (prefixEvaluation (n := n) L data k
        (FreeMetabelian.Free.weightIncl (k - 1) (by omega) x)) = 0
  change pieceToU (n := n) L data k hk x = 0 ↔
    (lowerCentralSeries ℤ L k : Submodule ℤ L).mkQ
      (FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) k
          (FreeMetabelian.Free.incl (⟨k - 1, by omega⟩ : Fin k) x)) = 0
  rw [FreeMetabelian.Evaluation.linear_incl]
  constructor
  · intro hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx'
  · intro hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx'

/-- The negative new homogeneous component on `D_k`. -/
def negativeTopOnD (k : ℕ) (hk : 2 ≤ k) (hkn : k < n + 1) :
    D n L data k (Nat.le_of_lt hkn) →ₗ[ℤ] U L k :=
  -(pieceToU (n := n) L data k (by omega)).comp
    ((FreeMetabelian.Free.weightProject (X := Generator L) (k - 1) (by omega)).comp
      (D n L data k (Nat.le_of_lt hkn)).subtype)

theorem ker_relationProjection_le_ker_negativeTopOnD
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n + 1) :
    LinearMap.ker (relationProjection n L data k (by omega) hkn) ≤
      LinearMap.ker (negativeTopOnD n L data k hk hkn) := by
  intro x hx
  have hxlow : ∀ i : Fin k, i.val < k - 1 → x.1 i = 0 := by
    intro i hi
    have hv := congrArg Subtype.val hx
    change FreeMetabelian.Free.prefixMap (X := Generator L) (k - 1) k (by omega) x.1 = 0 at hv
    have := congrFun hv ⟨i.val, hi⟩
    exact this
  have hxdecomp : x.1 = FreeMetabelian.Free.weightIncl (X := Generator L)
      (k - 1) (by omega)
        (FreeMetabelian.Free.weightProject (X := Generator L) (k - 1) (by omega) x.1) := by
    funext i
    by_cases hi : i.val < k - 1
    · rw [hxlow i hi]
      apply Eq.symm
      apply FreeMetabelian.Free.incl_apply_of_ne
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    · let last : Fin k := ⟨k - 1, by omega⟩
      have hilast : i = last := Fin.ext (by simp only [last]; omega)
      simp only [FreeMetabelian.Free.weightIncl,
        FreeMetabelian.Free.weightProject]
      rw [hilast]
      exact (FreeMetabelian.Free.incl_apply_same last
        (FreeMetabelian.Free.project last x.1)).symm
  have hmem : FreeMetabelian.Free.weightProject (X := Generator L)
      (k - 1) (by omega) x.1 ∈ PieceRelations (n := n) L data k (by omega) :=
    (piece_mem_relations_iff n L data k (by omega) hkn _).2 (by
      rw [← hxdecomp]
      exact x.2)
  change -(pieceToU (n := n) L data k (by omega)
      (FreeMetabelian.Free.weightProject (X := Generator L)
        (k - 1) (by omega) x.1)) = 0
  rw [hmem, neg_zero]

/-- The extension tail `b_k`, descended through the quotient by the kernel of
`D_k -> D_(k-1)`.  Lift-independence is part of this definition. -/
def extensionTail (k : ℕ) (hk : 2 ≤ k) (hkn : k < n + 1) :
    D n L data (k - 1) (by omega) →ₗ[ℤ] U L k := by
  let p := relationProjection n L data k (by omega) hkn
  let t := negativeTopOnD n L data k hk hkn
  let tq : (D n L data k (Nat.le_of_lt hkn) ⧸ LinearMap.ker p) →ₗ[ℤ] U L k :=
    (LinearMap.ker p).liftQ t
      (ker_relationProjection_le_ker_negativeTopOnD n L data k hk hkn)
  exact tq.comp ((p.quotKerEquivOfSurjective
    (relationProjection_surjective n L data k (by omega) hkn)).symm.toLinearMap)

theorem extensionTail_relation (k : ℕ) (hk : 2 ≤ k) (hkn : k < n + 1)
    (rho : Relations n L data) :
    extensionTail n L data k hk hkn
        ⟨prLE n L (k - 1) (by omega) rho.1, ⟨rho, rfl⟩⟩ =
      -pieceToU (n := n) L data k (by omega)
        (FreeMetabelian.Free.weightProject (X := Generator L)
          (k - 1) (by omega) (prLE n L k (Nat.le_of_lt hkn) rho.1)) := by
  change ((LinearMap.ker (relationProjection n L data k (by omega) hkn)).liftQ
      (negativeTopOnD n L data k hk hkn)
      (ker_relationProjection_le_ker_negativeTopOnD n L data k hk hkn))
    (((relationProjection n L data k (by omega) hkn).quotKerEquivOfSurjective
      (relationProjection_surjective n L data k (by omega) hkn)).symm
        ⟨prLE n L (k - 1) (by omega) rho.1, ⟨rho, rfl⟩⟩) = _
  have hp : relationProjection n L data k (by omega) hkn
      ⟨prLE n L k (Nat.le_of_lt hkn) rho.1, ⟨rho, rfl⟩⟩ =
        ⟨prLE n L (k - 1) (by omega) rho.1, ⟨rho, rfl⟩⟩ := by
    apply Subtype.ext
    exact LinearMap.congr_fun
      (FreeMetabelian.Free.projectPrefix_trans
        (X := Generator L) (k - 1) k (n + 1) (by omega)
          (Nat.le_of_lt hkn)) rho.1
  rw [← hp, LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- Full elements which evaluate into the terminal lower-central layer. -/
abbrev TopPreimage :=
  (lowerCentralSeries ℤ L n : Submodule ℤ L).comap
    (evaluation n L data).toLinearMap

/-- Evaluation in the terminal cyclic coordinate. -/
def terminalEval : TopPreimage n L data →ₗ[ℤ] ZMod (2 ^ data.exponent) :=
  data.topEquiv.toIntLinearEquiv.toLinearMap.comp
    (LinearMap.codRestrict (lowerCentralSeries ℤ L n : Submodule ℤ L)
      ((evaluation n L data).toLinearMap.domRestrict (TopPreimage n L data))
      (fun x ↦ x.2))

/-- A homogeneous top piece, regarded as a full element whose evaluation lies
in the terminal lower-central layer. -/
def topInclPreimage : FreeMetabelian.Piece (Generator L) n →ₗ[ℤ]
    TopPreimage n L data :=
  LinearMap.codRestrict (TopPreimage n L data)
      (FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega)) (by
        intro x
        change evaluation n L data
          (FreeMetabelian.Free.weightIncl (X := Generator L) n (by omega) x) ∈
            lowerCentralSeries ℤ L n
        rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
        change FreeMetabelian.Evaluation.linear data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
              (FreeMetabelian.Free.incl (⟨n, by omega⟩ : Fin (n + 1)) x) ∈ _
        rw [FreeMetabelian.Evaluation.linear_incl]
        cases n with
        | zero =>
          change FreeMetabelian.Evaluation.pieceEval data.metabelian
              (FreeMetabelian.Evaluation.canonicalGeneratorMap L) 0 x ∈
            LieModule.lowerCentralSeries ℤ L L 0
          rw [LieModule.lowerCentralSeries_zero]
          exact LieSubmodule.mem_top _
        | succ q =>
          exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
            data.metabelian (FreeMetabelian.Evaluation.canonicalGeneratorMap L) q x)

/-- Terminal coordinate of the homogeneous piece of manuscript weight
`n+1`. -/
def topCoord : FreeMetabelian.Piece (Generator L) n →ₗ[ℤ]
    ZMod (2 ^ data.exponent) :=
  (terminalEval n L data).comp (topInclPreimage n L data)

end

end LieRings.MetabelianVanishing
