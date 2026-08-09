import LieRings.DimensionSubring.Centrality
import LieRings.Graded.Associated

/-!
# The graded dimension quotient

The canonical map `gr_γ(L) → gr_δ(L)` has ideal image, and its quotient is abelian.
All constructions are over an arbitrary commutative base ring.
-/

namespace LieRings

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The lower-central filtration, indexed by conventional positive degrees. -/
def lowerCentralFiltration : LieFiltration R L where
  term n := lowerCentralSeries R L n.natPred
  antitone' _ _ h := LieModule.antitone_lowerCentralSeries R L L
    (PNat.natPred_monotone h)
  lie_le' i j := by
    calc
      ⁅lowerCentralSeries R L i.natPred, lowerCentralSeries R L j.natPred⁆ ≤
          ⁅dimensionSubring R L i, dimensionSubring R L j⁆ :=
        LieSubmodule.mono_lie
          (by simpa using lowerCentralSeries_le_dimensionSubring R L i.natPred)
          (by simpa using lowerCentralSeries_le_dimensionSubring R L j.natPred)
      _ ≤ lowerCentralSeries R L (i + j - 1) :=
        bracket_dimensionSubring_le_lowerCentralSeries_of_pos R L i.property j.property
      _ = lowerCentralSeries R L (i + j).natPred := by
        congr 1

/-- The dimension-subring filtration, indexed by positive degrees. -/
def dimensionFiltration : LieFiltration R L where
  term n := dimensionSubring R L n
  antitone' _ _ h := dimensionSubring_antitone R L h
  lie_le' i j := by
    refine (bracket_dimensionSubring_le_lowerCentralSeries_of_pos R L
      i.property j.property).trans ?_
    simpa using lowerCentralSeries_le_dimensionSubring R L ((i + j).natPred)

/-- The standard inclusions `γₙ(L) ≤ δₙ(L)`. -/
theorem lowerCentralFiltration_le_dimensionFiltration (n : ℕ+) :
    lowerCentralFiltration R L n ≤ dimensionFiltration R L n := by
  simpa [lowerCentralFiltration, dimensionFiltration] using
    lowerCentralSeries_le_dimensionSubring R L n.natPred

/-- The associated graded Lie algebra of the lower central series. -/
abbrev LowerCentralGraded := (lowerCentralFiltration R L).AssociatedGraded

/-- The associated graded Lie algebra of the dimension filtration. -/
abbrev DimensionGraded := (dimensionFiltration R L).AssociatedGraded

/-- The canonical graded Lie homomorphism `gr_γ(L) → gr_δ(L)`. -/
def lowerCentralToDimensionGraded : LowerCentralGraded R L →ₗ⁅R⁆ DimensionGraded R L :=
  LieFiltration.inclusionHom (lowerCentralFiltration R L) (dimensionFiltration R L)
    (lowerCentralFiltration_le_dimensionFiltration R L)

private theorem lcs_lowerCentralSeries (m n : ℕ) :
    LieSubmodule.lcs n (lowerCentralSeries R L m) =
      lowerCentralSeries R L (m + n) := by
  induction n with
  | zero => simp [LieSubmodule.lcs_zero]
  | succ n ih =>
    rw [LieSubmodule.lcs_succ, ih,
      show m + (n + 1) = (m + n) + 1 by omega]
    change ⁅(⊤ : LieIdeal R L), LieModule.lowerCentralSeries R L L (m + n)⁆ =
      LieModule.lowerCentralSeries R L L (m + n + 1)
    rw [LieModule.lowerCentralSeries_succ]

private theorem bracket_dimension_lowerCentral_mem {i j : ℕ+} {x y : L}
    (hx : x ∈ dimensionSubring R L i) (hy : y ∈ lowerCentralSeries R L j.natPred) :
    ⁅x, y⁆ ∈ lowerCentralSeries R L (i + j).natPred := by
  have hyx : ⁅y, x⁆ ∈ LieSubmodule.lcs (i : ℕ)
      (lowerCentralSeries R L j.natPred) :=
    (bracket_dimensionSubring_le_lcs R L (lowerCentralSeries R L j.natPred) i)
      (LieSubmodule.lie_mem_lie hy hx)
  have hxy : ⁅x, y⁆ ∈ LieSubmodule.lcs (i : ℕ)
      (lowerCentralSeries R L j.natPred) := by
    rw [← lie_skew]
    exact (LieSubmodule.lcs (i : ℕ) (lowerCentralSeries R L j.natPred)).neg_mem hyx
  rw [lcs_lowerCentralSeries] at hxy
  have hdeg : j.natPred + (i : ℕ) = (i + j).natPred := by
    have hi : i.natPred + 1 = (i : ℕ) := PNat.natPred_add_one i
    have hj : j.natPred + 1 = (j : ℕ) := PNat.natPred_add_one j
    have hij : (i + j).natPred + 1 = ((i + j : ℕ+) : ℕ) :=
      PNat.natPred_add_one (i + j)
    have hadd : ((i + j : ℕ+) : ℕ) = (i : ℕ) + (j : ℕ) := rfl
    omega
  rwa [hdeg] at hxy

private theorem bracket_piece_lift {i j : ℕ+}
    (x : (dimensionFiltration R L).GradedPiece i)
    (y : (lowerCentralFiltration R L).GradedPiece j) :
    ∃ z : (lowerCentralFiltration R L).GradedPiece (i + j),
      LieFiltration.inclusionPiece (lowerCentralFiltration R L)
          (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L)
          (i + j) z =
        (dimensionFiltration R L).gradedBracket x
          (LieFiltration.inclusionPiece (lowerCentralFiltration R L)
            (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L) j y) := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      let z : lowerCentralFiltration R L (i + j) :=
        ⟨⁅(x : L), (y : L)⁆,
          bracket_dimension_lowerCentral_mem R L x.property y.property⟩
      refine ⟨(lowerCentralFiltration R L).toGradedPiece (i + j) z, ?_⟩
      change LieFiltration.inclusionPiece (lowerCentralFiltration R L)
          (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L)
            (i + j) ((lowerCentralFiltration R L).toGradedPiece (i + j) z) =
        (dimensionFiltration R L).gradedBracket
          ((dimensionFiltration R L).toGradedPiece i x)
          (LieFiltration.inclusionPiece (lowerCentralFiltration R L)
            (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L) j
              ((lowerCentralFiltration R L).toGradedPiece j y))
      rw [LieFiltration.inclusionPiece_toGradedPiece,
        LieFiltration.inclusionPiece_toGradedPiece,
        LieFiltration.gradedBracket_toGradedPiece]

private theorem bracket_mem_lowerCentralToDimensionGraded_range
    (x : DimensionGraded R L) (y : LowerCentralGraded R L) :
    ⁅x, lowerCentralToDimensionGraded R L y⁆ ∈
      (lowerCentralToDimensionGraded R L).range := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      obtain ⟨z, hz⟩ := bracket_piece_lift R L x y
      refine ⟨DirectSum.of (lowerCentralFiltration R L).GradedPiece (i + j) z, ?_⟩
      change LieFiltration.inclusionLinear (lowerCentralFiltration R L)
          (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L)
            (DirectSum.of (lowerCentralFiltration R L).GradedPiece (i + j) z) = _
      rw [LieFiltration.inclusionLinear_of]
      change DirectSum.of (dimensionFiltration R L).GradedPiece (i + j) _ =
        ⁅DirectSum.of (dimensionFiltration R L).GradedPiece i x,
          LieFiltration.inclusionLinear (lowerCentralFiltration R L)
            (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L)
              (DirectSum.of (lowerCentralFiltration R L).GradedPiece j y)⁆
      rw [LieFiltration.inclusionLinear_of]
      change DirectSum.of (dimensionFiltration R L).GradedPiece (i + j) _ =
        DirectSum.of (dimensionFiltration R L).GradedPiece i x *
          DirectSum.of (dimensionFiltration R L).GradedPiece j _
      rw [DirectSum.of_mul_of]
      change DirectSum.of (dimensionFiltration R L).GradedPiece (i + j) _ =
        DirectSum.of (dimensionFiltration R L).GradedPiece (i + j)
          ((dimensionFiltration R L).gradedBracket x _)
      rw [hz]
    | add y z hy hz =>
      rw [map_add, lie_add]
      exact (lowerCentralToDimensionGraded R L).range.add_mem hy hz
  | add x y hx hy =>
    rw [add_lie]
    exact (lowerCentralToDimensionGraded R L).range.add_mem hx hy

/-- The image of `gr_γ(L) → gr_δ(L)`, promoted to a Lie ideal by dimension centrality. -/
def dimensionGradedImage : LieIdeal R (DimensionGraded R L) where
  __ := (lowerCentralToDimensionGraded R L).range.toSubmodule
  lie_mem := by
    rintro x _ ⟨y, rfl⟩
    exact bracket_mem_lowerCentralToDimensionGraded_range R L x y

@[simp]
theorem mem_dimensionGradedImage (x : DimensionGraded R L) :
    x ∈ dimensionGradedImage R L ↔ x ∈ (lowerCentralToDimensionGraded R L).range :=
  Iff.rfl

/-- The canonical image is homogeneous as well as being a Lie ideal. -/
theorem dimensionGradedImage_isGraded :
    (dimensionFiltration R L).IsGradedIdeal (dimensionGradedImage R L) := by
  intro x hx n
  rw [mem_dimensionGradedImage] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨DirectSum.of (lowerCentralFiltration R L).GradedPiece n (y n), ?_⟩
  change LieFiltration.inclusionLinear (lowerCentralFiltration R L)
      (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L)
        (DirectSum.of (lowerCentralFiltration R L).GradedPiece n (y n)) =
    DirectSum.of (dimensionFiltration R L).GradedPiece n
      ((LieFiltration.inclusionLinear (lowerCentralFiltration R L)
        (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L) y) n)
  rw [LieFiltration.inclusionLinear_of, LieFiltration.inclusionLinear_apply]

private theorem bracket_dimension_piece_lift {i j : ℕ+}
    (x : (dimensionFiltration R L).GradedPiece i)
    (y : (dimensionFiltration R L).GradedPiece j) :
    ∃ z : (lowerCentralFiltration R L).GradedPiece (i + j),
      LieFiltration.inclusionPiece (lowerCentralFiltration R L)
          (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L)
          (i + j) z = (dimensionFiltration R L).gradedBracket x y := by
  induction x using Quotient.inductionOn' with
  | _ x =>
    induction y using Quotient.inductionOn' with
    | _ y =>
      have hxy : ⁅(x : L), (y : L)⁆ ∈ lowerCentralFiltration R L (i + j) :=
        (bracket_dimensionSubring_le_lowerCentralSeries_of_pos R L
          i.property j.property) (LieSubmodule.lie_mem_lie x.property y.property)
      let z : lowerCentralFiltration R L (i + j) := ⟨⁅(x : L), (y : L)⁆, hxy⟩
      refine ⟨(lowerCentralFiltration R L).toGradedPiece (i + j) z, ?_⟩
      change LieFiltration.inclusionPiece (lowerCentralFiltration R L)
          (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L)
            (i + j) ((lowerCentralFiltration R L).toGradedPiece (i + j) z) =
        (dimensionFiltration R L).gradedBracket
          ((dimensionFiltration R L).toGradedPiece i x)
          ((dimensionFiltration R L).toGradedPiece j y)
      rw [LieFiltration.inclusionPiece_toGradedPiece,
        LieFiltration.gradedBracket_toGradedPiece]

/-- Every bracket in `gr_δ(L)` belongs to the canonical image of `gr_γ(L)`. -/
theorem bracket_mem_dimensionGradedImage (x y : DimensionGraded R L) :
    ⁅x, y⁆ ∈ dimensionGradedImage R L := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      obtain ⟨z, hz⟩ := bracket_dimension_piece_lift R L x y
      rw [mem_dimensionGradedImage]
      refine ⟨DirectSum.of (lowerCentralFiltration R L).GradedPiece (i + j) z, ?_⟩
      change LieFiltration.inclusionLinear (lowerCentralFiltration R L)
          (dimensionFiltration R L) (lowerCentralFiltration_le_dimensionFiltration R L)
            (DirectSum.of (lowerCentralFiltration R L).GradedPiece (i + j) z) = _
      rw [LieFiltration.inclusionLinear_of]
      change DirectSum.of (dimensionFiltration R L).GradedPiece (i + j) _ =
        DirectSum.of (dimensionFiltration R L).GradedPiece i x *
          DirectSum.of (dimensionFiltration R L).GradedPiece j y
      rw [DirectSum.of_mul_of]
      change DirectSum.of (dimensionFiltration R L).GradedPiece (i + j) _ =
        DirectSum.of (dimensionFiltration R L).GradedPiece (i + j)
          ((dimensionFiltration R L).gradedBracket x y)
      rw [hz]
    | add y z hy hz =>
      rw [lie_add]
      exact (dimensionGradedImage R L).add_mem hy hz
  | add x y hx hy =>
    rw [add_lie]
    exact (dimensionGradedImage R L).add_mem hx hy

/-- The cokernel of `gr_γ(L) → gr_δ(L)`. -/
abbrev DimensionGradedCokernel := DimensionGraded R L ⧸ dimensionGradedImage R L

/-- The graded dimension cokernel is an abelian Lie algebra. -/
theorem dimensionGradedCokernel_isLieAbelian : IsLieAbelian (DimensionGradedCokernel R L) :=
  ⟨by
    intro x y
    induction x, y using Quotient.inductionOn₂' with
    | _ x y =>
      change LieSubmodule.Quotient.mk (N := dimensionGradedImage R L) ⁅x, y⁆ = 0
      rw [LieSubmodule.Quotient.mk_eq_zero']
      exact bracket_mem_dimensionGradedImage R L x y⟩

end LieRings
