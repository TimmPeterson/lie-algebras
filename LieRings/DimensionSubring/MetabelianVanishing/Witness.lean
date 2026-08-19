import LieRings.DimensionSubring.MetabelianVanishing.TriangularBasis
import LieRings.PBW.WeightedGraded

/-!
# The Smith-adapted weighted PBW witness

This file implements the governing equation from the manuscript.  The global
basis changes only the homogeneous pieces of weights one and `n`; hence every
basis vector remains homogeneous.  A dimension-subring element is lifted in
the top homogeneous piece and its difference from a high augmentation word is
written as an actual finite sum with a full relation on the left.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance witnessFintype : Fintype L := Fintype.ofFinite L

/-- Rank of one homogeneous piece in the adapted global basis. -/
def PieceRank (s : Fin (n + 1)) : ℕ :=
  if s.val = 0 then Nat.card L
  else if s.val = n - 1 then (qSmith n L data (by omega)).rank
  else Nat.card (FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s.val)

/-- The chosen homogeneous basis: the Smith ambient bases in weights `1` and
`n`, and the Hall basis in all other weights. -/
def pieceAdaptedBasis (s : Fin (n + 1)) :
    Module.Basis (Fin (PieceRank n L data hn s)) ℤ
      (FreeMetabelian.Piece (Generator L) s.val) := by
  by_cases hs0 : s.val = 0
  · have hs : s = ⟨0, by omega⟩ := Fin.ext hs0
    rw [hs]
    rw [PieceRank, if_pos rfl]
    exact (triangularSmith n L data 0 (by omega)).ambientBasis
  · by_cases hsn : s.val = n - 1
    · rw [PieceRank, if_neg hs0, if_pos hsn]
      have hs : s = ⟨n - 1, by omega⟩ := Fin.ext hsn
      rw [hs]
      simpa only using (qSmith n L data (by omega)).ambientBasis
    · let old := FreeMetabelian.Free.pieceBasis (generatorBasis L) s.val
      rw [PieceRank, if_neg hs0, if_neg hsn]
      exact old.reindex (Finite.equivFin _)

/-- Weight-first indices for the adapted PBW basis. -/
abbrev AdaptedIndex := (s : Fin (n + 1)) × Fin (PieceRank n L data hn s)

private def adaptedIndexCode : AdaptedIndex n L data hn → ℕ ×ₗ ℕ :=
  fun i ↦ toLex (i.1.val, i.2.val)

private theorem adaptedIndexCode_injective :
    Function.Injective (adaptedIndexCode n L data hn) := by
  rintro ⟨s, i⟩ ⟨t, j⟩ h
  simp only [adaptedIndexCode, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq] at h
  rcases h with ⟨hst, hij⟩
  have hs : s = t := Fin.ext hst
  subst t
  have hi : i = j := Fin.ext hij
  subst j
  rfl

noncomputable instance : LinearOrder (AdaptedIndex n L data hn) :=
  LinearOrder.lift' (adaptedIndexCode n L data hn)
    (adaptedIndexCode_injective n L data hn)

/-- The global homogeneous integral basis used for PBW collection. -/
def adaptedBasis : Module.Basis (AdaptedIndex n L data hn) ℤ (FreeModel n L) :=
  Pi.basis (pieceAdaptedBasis n L data hn)

@[simp] theorem adaptedBasis_apply (i : AdaptedIndex n L data hn) :
    adaptedBasis n L data hn i =
      FreeMetabelian.Free.incl i.1 (pieceAdaptedBasis n L data hn i.1 i.2) := by
  rw [adaptedBasis, Pi.basis_apply]
  rfl

private theorem adapted_bracket_homogeneous (i j k : AdaptedIndex n L data hn)
    (h : (adaptedBasis n L data hn).repr
      ⁅adaptedBasis n L data hn i, adaptedBasis n L data hn j⁆ k ≠ 0) :
    k.1.val + 1 = (i.1.val + 1) + (j.1.val + 1) := by
  by_contra hweight
  apply h
  have hv : ⁅adaptedBasis n L data hn i,
      adaptedBasis n L data hn j⁆ k.1 = 0 := by
    rw [adaptedBasis_apply, adaptedBasis_apply]
    exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
      i.1.val j.1.val i.1.isLt j.1.isLt
      (pieceAdaptedBasis n L data hn i.1 i.2)
      (pieceAdaptedBasis n L data hn j.1 j.2) k.1 (by omega)
  change ((pieceAdaptedBasis n L data hn k.1).repr
    (⁅adaptedBasis n L data hn i, adaptedBasis n L data hn j⁆ k.1)) k.2 = 0
  rw [hv, map_zero]
  rfl

private theorem iota_mem_augmentation_pow_of_lcs (s : ℕ)
    {x : FreeModel n L}
    (hx : x ∈ lowerCentralSeries ℤ (FreeModel n L) s) :
    UniversalEnvelopingAlgebra.ι ℤ x ∈
      UEA.augmentationIdeal ℤ (FreeModel n L) ^ (s + 1) := by
  exact (mem_dimensionSubring ℤ (FreeModel n L)).mp
    (lowerCentralSeries_le_dimensionSubring ℤ (FreeModel n L) s hx)

/-- The concrete Smith-adapted weighted basis. -/
def adaptedWeightedBasis :
    LieRings.PBW.WeightedBasis
      (L := FreeModel n L) (ι := AdaptedIndex n L data hn) where
  basis := adaptedBasis n L data hn
  weight i := i.1.val + 1
  weight_pos i := by omega
  bracket_homogeneous := adapted_bracket_homogeneous n L data hn
  iota_mem_augmentation_pow i := by
    apply iota_mem_augmentation_pow_of_lcs (n := n) (L := L) i.1.val
    rw [adaptedBasis_apply]
    exact FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
      (generatorBasis L) i.1.val i.1.isLt _

/-- A homogeneous piece is recovered exactly by the one-factor PBW projection
at its manuscript weight. -/
theorem adapted_proj_iota_weightIncl (s : ℕ) (hs : s < n + 1)
    (x : FreeMetabelian.Piece (Generator L) s) :
    (adaptedWeightedBasis n L data hn).proj (s + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl s hs x) := by
  let b := pieceAdaptedBasis n L data hn (⟨s, hs⟩ : Fin (n + 1))
  rw [← b.sum_repr x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  have hb : FreeMetabelian.Free.weightIncl s hs (b i) =
      adaptedBasis n L data hn ⟨⟨s, hs⟩, i⟩ := by
    dsimp only [b]
    exact (adaptedBasis_apply n L data hn ⟨⟨s, hs⟩, i⟩).symm
  rw [hb]
  have hp := (adaptedWeightedBasis n L data hn).proj_iota_basis
    ⟨⟨s, hs⟩, i⟩ (s + 1) 1
  change (adaptedWeightedBasis n L data hn).proj (s + 1) 1
      (UniversalEnvelopingAlgebra.ι ℤ
        (adaptedBasis n L data hn ⟨⟨s, hs⟩, i⟩)) = _ at hp
  rw [hp]
  simp [adaptedWeightedBasis]

/-- Other exact bidegrees of a homogeneous enveloping inclusion vanish. -/
theorem adapted_proj_iota_weightIncl_eq_zero (s : ℕ) (hs : s < n + 1)
    (x : FreeMetabelian.Piece (Generator L) s) (w p : ℕ)
    (hne : w ≠ s + 1 ∨ p ≠ 1) :
    (adaptedWeightedBasis n L data hn).proj w p
        (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x)) = 0 := by
  let b := pieceAdaptedBasis n L data hn (⟨s, hs⟩ : Fin (n + 1))
  rw [← b.sum_repr x]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_eq_zero
  intro i hi
  have hb : FreeMetabelian.Free.weightIncl s hs (b i) =
      adaptedBasis n L data hn ⟨⟨s, hs⟩, i⟩ := by
    dsimp only [b]
    exact (adaptedBasis_apply n L data hn ⟨⟨s, hs⟩, i⟩).symm
  rw [hb]
  have hp := (adaptedWeightedBasis n L data hn).proj_iota_basis
    ⟨⟨s, hs⟩, i⟩ w p
  change (adaptedWeightedBasis n L data hn).proj w p
      (UniversalEnvelopingAlgebra.ι ℤ
        (adaptedBasis n L data hn ⟨⟨s, hs⟩, i⟩)) = _ at hp
  rw [hp]
  split_ifs with hwp
  · have hsw : s + 1 = w := by
      simpa only [adaptedWeightedBasis] using hwp.1
    exact (hne.elim (fun h ↦ h hsw.symm) (fun h ↦ h hwp.2)).elim
  · simp

/-- The exact terminal-weight, one-factor projection of an arbitrary free
element is its literal terminal homogeneous coordinate. -/
theorem adapted_proj_top_iota (x : FreeModel n L) :
    (adaptedWeightedBasis n L data hn).proj (n + 1) 1
        (UniversalEnvelopingAlgebra.ι ℤ x) =
      UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl n (by omega)
          (FreeMetabelian.Free.weightProject n (by omega) x)) := by
  conv_lhs =>
    rw [← FreeMetabelian.Free.sum_incl_project x, map_sum, map_sum]
  rw [Finset.sum_eq_single ⟨n, by omega⟩]
  · exact adapted_proj_iota_weightIncl n L data hn n (by omega)
      (FreeMetabelian.Free.project ⟨n, by omega⟩ x)
  · intro i _ hi
    have hin : i.val ≠ n := by
      intro h
      apply hi
      exact Fin.ext h
    exact adapted_proj_iota_weightIncl_eq_zero n L data hn i.val i.isLt
      (FreeMetabelian.Free.project i x) (n + 1) 1 (Or.inl (by omega))
  · simp

/-- If two homogeneous factors occur in increasing weight order, their
product is already ordered in the adapted global PBW basis and therefore has
no one-factor component. -/
theorem adapted_proj_one_iota_weightIncl_mul_of_lt
    (s t : ℕ) (hs : s < n + 1) (ht : t < n + 1) (hst : s < t)
    (x : FreeMetabelian.Piece (Generator L) s)
    (y : FreeMetabelian.Piece (Generator L) t) (w : ℕ) :
    (adaptedWeightedBasis n L data hn).proj w 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x) *
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl t ht y)) = 0 := by
  let bx := pieceAdaptedBasis n L data hn (⟨s, hs⟩ : Fin (n + 1))
  let byy := pieceAdaptedBasis n L data hn (⟨t, ht⟩ : Fin (n + 1))
  rw [← bx.sum_repr x, ← byy.sum_repr y]
  simp only [map_sum, map_zsmul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [smul_mul_smul, map_zsmul]
  have hxi : FreeMetabelian.Free.weightIncl s hs (bx j) =
      adaptedBasis n L data hn ⟨⟨s, hs⟩, j⟩ := by
    exact (adaptedBasis_apply n L data hn ⟨⟨s, hs⟩, j⟩).symm
  have hyj : FreeMetabelian.Free.weightIncl t ht (byy i) =
      adaptedBasis n L data hn ⟨⟨t, ht⟩, i⟩ := by
    exact (adaptedBasis_apply n L data hn ⟨⟨t, ht⟩, i⟩).symm
  rw [hxi, hyj]
  have hle : (⟨⟨s, hs⟩, j⟩ : AdaptedIndex n L data hn) ≤
      ⟨⟨t, ht⟩, i⟩ := by
    change toLex (s, j.val) ≤ toLex (t, i.val)
    exact Prod.Lex.left _ _ hst
  have hz := LieRings.PBW.WeightedBasis.proj_one_iota_basis_mul_iota_basis_of_le
    (adaptedWeightedBasis n L data hn)
    (⟨⟨s, hs⟩, j⟩ : AdaptedIndex n L data hn)
    (⟨⟨t, ht⟩, i⟩ : AdaptedIndex n L data hn) hle w
  have hz' : (adaptedWeightedBasis n L data hn).proj w 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn ⟨⟨s, hs⟩, j⟩) *
        UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn ⟨⟨t, ht⟩, i⟩)) = 0 := by
    simpa only [adaptedWeightedBasis] using hz
  rw [hz', smul_zero]

/-- Increasing homogeneous factors have no complete one-factor component.
Unlike `adapted_proj_one_iota_weightIncl_mul_of_lt`, this statement retains
all bracket weights and is therefore safe for full-relation transport. -/
theorem adapted_factorProj_one_iota_weightIncl_mul_of_lt
    (s t : ℕ) (hs : s < n + 1) (ht : t < n + 1) (hst : s < t)
    (x : FreeMetabelian.Piece (Generator L) s)
    (y : FreeMetabelian.Piece (Generator L) t) :
    (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x) *
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl t ht y)) = 0 := by
  let bx := pieceAdaptedBasis n L data hn (⟨s, hs⟩ : Fin (n + 1))
  let byy := pieceAdaptedBasis n L data hn (⟨t, ht⟩ : Fin (n + 1))
  rw [← bx.sum_repr x, ← byy.sum_repr y]
  simp only [map_sum, map_zsmul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [smul_mul_smul, map_zsmul]
  have hxi : FreeMetabelian.Free.weightIncl s hs (bx j) =
      adaptedBasis n L data hn ⟨⟨s, hs⟩, j⟩ := by
    exact (adaptedBasis_apply n L data hn ⟨⟨s, hs⟩, j⟩).symm
  have hyj : FreeMetabelian.Free.weightIncl t ht (byy i) =
      adaptedBasis n L data hn ⟨⟨t, ht⟩, i⟩ := by
    exact (adaptedBasis_apply n L data hn ⟨⟨t, ht⟩, i⟩).symm
  rw [hxi, hyj]
  have hle : (⟨⟨s, hs⟩, j⟩ : AdaptedIndex n L data hn) ≤
      ⟨⟨t, ht⟩, i⟩ := by
    change toLex (s, j.val) ≤ toLex (t, i.val)
    exact Prod.Lex.left _ _ hst
  have hz :=
    LieRings.PBW.WeightedBasis.factorProj_one_iota_basis_mul_iota_basis_of_le
      (adaptedWeightedBasis n L data hn)
      (⟨⟨s, hs⟩, j⟩ : AdaptedIndex n L data hn)
      (⟨⟨t, ht⟩, i⟩ : AdaptedIndex n L data hn) hle
  have hz' : (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn ⟨⟨s, hs⟩, j⟩) *
        UniversalEnvelopingAlgebra.ι ℤ
          (adaptedBasis n L data hn ⟨⟨t, ht⟩, i⟩)) = 0 := by
    simpa only [adaptedWeightedBasis] using hz
  rw [hz', smul_zero]

/-- A product of two derived homogeneous factors has no one-factor component.
Metabelianity makes an inverted pair commute, after which the preceding
ordered two-letter PBW calculation applies. -/
theorem adapted_proj_one_iota_derived_mul_derived
    (s t : ℕ) (hs : s < n + 1) (ht : t < n + 1)
    (hs0 : 0 < s) (ht0 : 0 < t)
    (x : FreeMetabelian.Piece (Generator L) s)
    (y : FreeMetabelian.Piece (Generator L) t) (w : ℕ) :
    (adaptedWeightedBasis n L data hn).proj w 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x) *
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl t ht y)) = 0 := by
  let bx := pieceAdaptedBasis n L data hn (⟨s, hs⟩ : Fin (n + 1))
  let byy := pieceAdaptedBasis n L data hn (⟨t, ht⟩ : Fin (n + 1))
  rw [← bx.sum_repr x, ← byy.sum_repr y]
  simp only [map_sum, map_zsmul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [smul_mul_smul, map_zsmul]
  let ix : AdaptedIndex n L data hn := ⟨⟨s, hs⟩, j⟩
  let iy : AdaptedIndex n L data hn := ⟨⟨t, ht⟩, i⟩
  have hxi : FreeMetabelian.Free.weightIncl s hs (bx j) =
      adaptedBasis n L data hn ix := by
    exact (adaptedBasis_apply n L data hn ix).symm
  have hyj : FreeMetabelian.Free.weightIncl t ht (byy i) =
      adaptedBasis n L data hn iy := by
    exact (adaptedBasis_apply n L data hn iy).symm
  rw [hxi, hyj]
  have hzero : ⁅adaptedBasis n L data hn ix,
      adaptedBasis n L data hn iy⁆ = 0 := by
    rw [← hxi, ← hyj]
    exact FreeMetabelian.Free.bracket_weightIncl_eq_zero_of_pos
      s t hs ht hs0 ht0 (bx j) (byy i)
  by_cases hle : ix ≤ iy
  · have hz := LieRings.PBW.WeightedBasis.proj_one_iota_basis_mul_iota_basis_of_le
      (adaptedWeightedBasis n L data hn) ix iy hle w
    have hz' : (adaptedWeightedBasis n L data hn).proj w 1
        (UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn ix) *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn iy)) = 0 := by
      simpa only [adaptedWeightedBasis] using hz
    rw [hz', smul_zero]
  · have hyx : iy ≤ ix := le_of_not_ge hle
    have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L)
      (adaptedBasis n L data hn ix) (adaptedBasis n L data hn iy)
    rw [hzero, map_zero, add_zero] at hswap
    rw [hswap]
    have hz := LieRings.PBW.WeightedBasis.proj_one_iota_basis_mul_iota_basis_of_le
      (adaptedWeightedBasis n L data hn) iy ix hyx w
    have hz' : (adaptedWeightedBasis n L data hn).proj w 1
        (UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn iy) *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn ix)) = 0 := by
      simpa only [adaptedWeightedBasis] using hz
    rw [hz', smul_zero]

/-- Two derived homogeneous factors have zero complete one-factor component.
This is the full-weight counterpart of
`adapted_proj_one_iota_derived_mul_derived`. -/
theorem adapted_factorProj_one_iota_derived_mul_derived
    (s t : ℕ) (hs : s < n + 1) (ht : t < n + 1)
    (hs0 : 0 < s) (ht0 : 0 < t)
    (x : FreeMetabelian.Piece (Generator L) s)
    (y : FreeMetabelian.Piece (Generator L) t) :
    (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x) *
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl t ht y)) = 0 := by
  let bx := pieceAdaptedBasis n L data hn (⟨s, hs⟩ : Fin (n + 1))
  let byy := pieceAdaptedBasis n L data hn (⟨t, ht⟩ : Fin (n + 1))
  rw [← bx.sum_repr x, ← byy.sum_repr y]
  simp only [map_sum, map_zsmul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [smul_mul_smul, map_zsmul]
  let ix : AdaptedIndex n L data hn := ⟨⟨s, hs⟩, j⟩
  let iy : AdaptedIndex n L data hn := ⟨⟨t, ht⟩, i⟩
  have hxi : FreeMetabelian.Free.weightIncl s hs (bx j) =
      adaptedBasis n L data hn ix := by
    exact (adaptedBasis_apply n L data hn ix).symm
  have hyj : FreeMetabelian.Free.weightIncl t ht (byy i) =
      adaptedBasis n L data hn iy := by
    exact (adaptedBasis_apply n L data hn iy).symm
  rw [hxi, hyj]
  have hzero : ⁅adaptedBasis n L data hn ix,
      adaptedBasis n L data hn iy⁆ = 0 := by
    rw [← hxi, ← hyj]
    exact FreeMetabelian.Free.bracket_weightIncl_eq_zero_of_pos
      s t hs ht hs0 ht0 (bx j) (byy i)
  by_cases hle : ix ≤ iy
  · have hz :=
      LieRings.PBW.WeightedBasis.factorProj_one_iota_basis_mul_iota_basis_of_le
        (adaptedWeightedBasis n L data hn) ix iy hle
    have hz' : (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn ix) *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn iy)) = 0 := by
      simpa only [adaptedWeightedBasis] using hz
    rw [hz', smul_zero]
  · have hyx : iy ≤ ix := le_of_not_ge hle
    have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L)
      (adaptedBasis n L data hn ix) (adaptedBasis n L data hn iy)
    rw [hzero, map_zero, add_zero] at hswap
    rw [hswap]
    have hz :=
      LieRings.PBW.WeightedBasis.factorProj_one_iota_basis_mul_iota_basis_of_le
        (adaptedWeightedBasis n L data hn) iy ix hyx
    have hz' : (adaptedWeightedBasis n L data hn).factorProj 1
        (UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn iy) *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn ix)) = 0 := by
      simpa only [adaptedWeightedBasis] using hz
    rw [hz', smul_zero]

/-- Collecting a reversed pair in the complete one-factor projection gives
its whole Lie bracket. -/
theorem adapted_factorProj_one_iota_weightIncl_mul_reverse
    (s t : ℕ) (hs : s < n + 1) (ht : t < n + 1) (hts : t < s)
    (x : FreeMetabelian.Piece (Generator L) s)
    (y : FreeMetabelian.Piece (Generator L) t) :
    (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x) *
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl t ht y)) =
      UniversalEnvelopingAlgebra.ι ℤ
        ⁅FreeMetabelian.Free.weightIncl s hs x,
          FreeMetabelian.Free.weightIncl t ht y⁆ := by
  let high := FreeMetabelian.Free.weightIncl s hs x
  let low := FreeMetabelian.Free.weightIncl t ht y
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L) high low
  rw [hswap, map_add]
  have hord := adapted_factorProj_one_iota_weightIncl_mul_of_lt
    n L data hn t s ht hs hts y x
  change (adaptedWeightedBasis n L data hn).factorProj 1
      (UniversalEnvelopingAlgebra.ι ℤ low *
        UniversalEnvelopingAlgebra.ι ℤ high) = 0 at hord
  rw [hord, zero_add]
  exact (adaptedWeightedBasis n L data hn).factorProj_one_iota _

/-- Collecting one reversed pair of homogeneous factors gives precisely its
bracket in the one-factor component at the summed manuscript weight. -/
theorem adapted_proj_one_iota_weightIncl_mul_reverse
    (s t : ℕ) (hs : s < n + 1) (ht : t < n + 1) (hts : t < s)
    (hu : s + t + 1 < n + 1)
    (x : FreeMetabelian.Piece (Generator L) s)
    (y : FreeMetabelian.Piece (Generator L) t) :
    (adaptedWeightedBasis n L data hn).proj (s + t + 2) 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x) *
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl t ht y)) =
      UniversalEnvelopingAlgebra.ι ℤ
        ⁅FreeMetabelian.Free.weightIncl s hs x,
          FreeMetabelian.Free.weightIncl t ht y⁆ := by
  let high := FreeMetabelian.Free.weightIncl s hs x
  let low := FreeMetabelian.Free.weightIncl t ht y
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L) high low
  rw [hswap, map_add]
  have hord := adapted_proj_one_iota_weightIncl_mul_of_lt n L data hn
    t s ht hs hts y x (s + t + 2)
  change (adaptedWeightedBasis n L data hn).proj (s + t + 2) 1
      (UniversalEnvelopingAlgebra.ι ℤ low *
        UniversalEnvelopingAlgebra.ι ℤ high) = 0 at hord
  rw [hord, zero_add]
  have hhom : ⁅high, low⁆ = FreeMetabelian.Free.weightIncl (s + t + 1) hu
      (FreeMetabelian.Free.weightProject (s + t + 1) hu ⁅high, low⁆) := by
    funext k
    by_cases hk : k.val = s + t + 1
    · have hkeq : k = ⟨s + t + 1, hu⟩ := Fin.ext hk
      subst k
      change ⁅high, low⁆ ⟨s + t + 1, hu⟩ =
        FreeMetabelian.Free.incl ⟨s + t + 1, hu⟩
          (FreeMetabelian.Free.project ⟨s + t + 1, hu⟩ ⁅high, low⁆)
            ⟨s + t + 1, hu⟩
      rw [FreeMetabelian.Free.incl_apply_same,
        FreeMetabelian.Free.project_apply]
    · rw [FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
        s t hs ht x y k hk]
      exact (FreeMetabelian.Free.incl_apply_of_ne
        ⟨s + t + 1, hu⟩ k (by
          intro h
          exact hk (congrArg Fin.val h))
        (FreeMetabelian.Free.weightProject (s + t + 1) hu ⁅high, low⁆)).symm
  rw [hhom]
  exact adapted_proj_iota_weightIncl n L data hn (s + t + 1) hu
    (FreeMetabelian.Free.weightProject (s + t + 1) hu ⁅high, low⁆)

/-- If the bracket weight of a reversed pair is beyond the truncation, the
bracket is zero and collection leaves no one-factor term. -/
theorem adapted_proj_one_iota_weightIncl_mul_of_overflow
    (s t : ℕ) (hs : s < n + 1) (ht : t < n + 1) (hts : t < s)
    (hover : n + 1 ≤ s + t + 1)
    (x : FreeMetabelian.Piece (Generator L) s)
    (y : FreeMetabelian.Piece (Generator L) t) (w : ℕ) :
    (adaptedWeightedBasis n L data hn).proj w 1
      (UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl s hs x) *
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl t ht y)) = 0 := by
  let high := FreeMetabelian.Free.weightIncl s hs x
  let low := FreeMetabelian.Free.weightIncl t ht y
  have hzero : ⁅high, low⁆ = 0 := by
    funext k
    exact FreeMetabelian.Free.bracket_weightIncl_apply_eq_zero_of_ne
      s t hs ht x y k (by omega)
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ (FreeModel n L) high low
  rw [hzero, map_zero, add_zero] at hswap
  rw [hswap]
  exact adapted_proj_one_iota_weightIncl_mul_of_lt n L data hn
    t s ht hs hts y x w

/-- The finite governing equation, with each label a full relation. -/
structure GoverningWitness (a : L) where
  atilde : FreeMetabelian.Piece (Generator L) n
  evaluates : evaluation n L data
      (FreeMetabelian.Free.weightIncl n (by omega) atilde) = a
  highWord : UEA ℤ (FreeModel n L)
  highWord_mem : highWord ∈
    UEA.augmentationIdeal ℤ (FreeModel n L) ^ (2 * n + 1)
  relationCoefficients :
    (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ
  governingEquation :
    relationCoefficients.sum (fun p z ↦ z •
      (UniversalEnvelopingAlgebra.ι ℤ (p.1 : FreeModel n L) * p.2)) =
      UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl n (by omega) atilde) - highWord

namespace GoverningWitness

variable {n L data hn}

/-- The relation-on-the-left side `theta` of the governing equation. -/
def theta {a : L} (w : GoverningWitness n L data a) :
    UEA ℤ (FreeModel n L) :=
  w.relationCoefficients.sum (fun p z ↦ z •
    (UniversalEnvelopingAlgebra.ι ℤ (p.1 : FreeModel n L) * p.2))

theorem theta_sub_iota {a : L} (w : GoverningWitness n L data a) :
    w.theta - UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) =
      -w.highWord := by
  rw [theta, w.governingEquation]
  abel

/-- The complete one-factor PBW component is precisely the chosen top
homogeneous lift: all other one-factor weights vanish. -/
theorem theta_proj {a : L} (w : GoverningWitness n L data a)
    (weight factors : ℕ) (hsmall : weight ≤ 2 * n) :
    (adaptedWeightedBasis n L data hn).proj weight factors w.theta =
      if weight = n + 1 ∧ factors = 1 then
        UniversalEnvelopingAlgebra.ι ℤ
          (FreeMetabelian.Free.weightIncl n (by omega) w.atilde)
      else 0 := by
  have hhigh : (adaptedWeightedBasis n L data hn).proj weight factors
      w.highWord = 0 := by
    have hmem : w.highWord ∈
        (adaptedWeightedBasis n L data hn).weightGE (2 * n + 1) := by
      rw [← (adaptedWeightedBasis n L data hn).augmentationIdeal_pow_eq_weightGE]
      exact w.highWord_mem
    apply LieRings.PBW.WeightedBasis.proj_eq_zero_of_mem_weightGE
      (B := adaptedWeightedBasis n L data hn)
      (r := 2 * n + 1) (w := weight) (p := factors) hmem
    omega
  have heq := congrArg
    (fun z ↦ (adaptedWeightedBasis n L data hn).proj weight factors z)
    w.theta_sub_iota
  simp only [map_sub, map_neg, hhigh, map_zero, neg_zero,
    sub_eq_zero] at heq
  rw [heq]
  by_cases h : weight = n + 1 ∧ factors = 1
  · rcases h with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩]
    exact adapted_proj_iota_weightIncl n L data hn n (by omega) w.atilde
  · rw [if_neg h]
    exact adapted_proj_iota_weightIncl_eq_zero n L data hn n (by omega)
      w.atilde weight factors (by tauto)

end GoverningWitness

/-- Extraction of the exact governing witness from a top-layer dimension
element. -/
theorem exists_governingWitness (a : L)
    (haDim : a ∈ dimensionSubring ℤ L (2 * n + 1))
    (haTop : a ∈ lowerCentralSeries ℤ L n) :
    Nonempty (GoverningWitness n L data a) := by
  have hrange := FreeMetabelian.Evaluation.canonicalPiece_range_eq_lowerCentralSeries
    data.metabelian n
  have haRange : a ∈ LinearMap.range
      (FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) n) := by
    rw [hrange]
    exact haTop
  obtain ⟨atilde, hatilde⟩ := haRange
  have heval : evaluation n L data
      (FreeMetabelian.Free.weightIncl n (by omega) atilde) = a := by
    rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
    change FreeMetabelian.Evaluation.lieHom data.metabelian data.classBound
      (FreeMetabelian.Evaluation.canonicalGeneratorMap L)
      (FreeMetabelian.Free.incl (⟨n, by omega⟩ : Fin (n + 1)) atilde) = a
    rw [FreeMetabelian.Evaluation.lieHom_incl]
    exact hatilde
  have haAug : UniversalEnvelopingAlgebra.ι ℤ a ∈
      UEA.augmentationIdeal ℤ L ^ (2 * n + 1) :=
    (mem_dimensionSubring ℤ L).mp haDim
  obtain ⟨highWord, hhigh, hhighEval⟩ :=
    UEA.exists_mem_augmentationIdeal_pow_succ_of_surjective ℤ
      (FreeModel n L) L (evaluation n L data)
      (FreeMetabelian.Evaluation.canonicalEvaluation_surjective
        data.metabelian data.classBound (by omega)) (2 * n) haAug
  have hzero : UEA.map ℤ (FreeModel n L) L (evaluation n L data)
      (UniversalEnvelopingAlgebra.ι ℤ
        (FreeMetabelian.Free.weightIncl n (by omega) atilde) - highWord) = 0 := by
    rw [map_sub, UEA.map_ι, heval, hhighEval, sub_self]
  have hideal := (LieRings.PBW.WeightedBasis.mem_ker_map_iff_mem_idealOfLieIdeal
    (evaluation n L data)
    (FreeMetabelian.Evaluation.canonicalEvaluation_surjective
      data.metabelian data.classBound (by omega)) _).mp hzero
  have hspan := (DegreeFive.mem_idealOfLieIdeal_iff_relation_sum ℤ
    (FreeModel n L) (Relations n L data) _).mp hideal
  obtain ⟨coeff, hcoeff⟩ :=
    DegreeFive.exists_relation_finsupp_of_mem_rightRelationSpan ℤ
      (FreeModel n L) (Relations n L data) hspan
  exact ⟨⟨atilde, heval, highWord, hhigh, coeff, hcoeff⟩⟩

end

end LieRings.MetabelianVanishing
