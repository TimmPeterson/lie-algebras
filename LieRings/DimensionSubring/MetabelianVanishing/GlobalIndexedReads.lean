import LieRings.DimensionSubring.MetabelianVanishing.GlobalPacketOccurrences
import LieRings.DimensionSubring.MetabelianVanishing.Assembly

/-!
# The two indexed reads on `J_k`

This file implements the occurrence-level heart of the corrected proof.
The horizontal full-relation read and the vertical homogeneous-component
read are compared on the same `PacketOccurrence`; filtering to `Delta_k`
therefore preserves ancestry, coefficient, orientation, and even copies
whose eventual value in the target is zero.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalIndexedReadsFintype : Fintype L :=
  Fintype.ofFinite L

namespace PacketOccurrence

/-- The manuscript bracket attached to a supported occurrence.  Written in
the already formalized polarized form, this is `Theta_k` with the active
relation component in its unique head slot and the ordinary factors in the
tooth slots. -/
def bracketRead
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (o : PacketOccurrence n L data hn k) : ZMod (2 ^ data.exponent) :=
  T n L data k hk hkn
    (o.occurrence.cell.factorEdge n L data hn
      (n - k + 2) k (by omega))

private theorem adaptedWeightSum_length_lt_of_exists_val_pos
    (xs : List (AdaptedIndex n L data hn))
    (hpos : ∃ i ∈ xs, 0 < i.1.val) :
    xs.length <
      (xs.map (adaptedWeightedBasis n L data hn).weight).sum := by
  let B := adaptedWeightedBasis n L data hn
  have length_le_weight_sum (ys : List (AdaptedIndex n L data hn)) :
      ys.length ≤ (ys.map B.weight).sum := by
    simpa only [List.length_map] using
      (List.length_le_sum_of_one_le (ys.map B.weight) (by
        intro q hq
        rw [List.mem_map] at hq
        obtain ⟨j, hj, rfl⟩ := hq
        exact B.weight_pos j))
  induction xs with
  | nil => simp at hpos
  | cons j xs ih =>
      obtain ⟨i, hi, hiPos⟩ := hpos
      simp only [List.mem_cons] at hi
      rcases hi with hij | hi
      · subst i
        have htail := length_le_weight_sum xs
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        change xs.length + 1 <
          (j.1.val + 1) + (xs.map B.weight).sum
        omega
      · have htail := ih ⟨i, hi, hiPos⟩
        have hj : 1 ≤
            (adaptedWeightedBasis n L data hn).weight j :=
          (adaptedWeightedBasis n L data hn).weight_pos j
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega

/-- An occurrence outside `Delta_k` has zero vertical read.  Positivity of
the adapted weights makes its total weight strictly larger than `n+1`, so
the governing transgression support cannot see it. -/
theorem bracketRead_eq_zero_of_not_supported
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (o : PacketOccurrence n L data hn k)
    (hs : ¬o.IsSupported n L data hn k) :
    o.bracketRead n L data hn k hk hkn = 0 := by
  apply ProvenancedCell.T_factorEdge_eq_zero_of_weight_ne
    n L data hn o.occurrence.cell k hk hkn
  intro hweight
  have hexists : ∃ i ∈ o.occurrence.cell.left, 0 < i.1.val := by
    by_contra hnone
    apply hs
    intro i hi
    have hnotpos : ¬0 < i.1.val := by
      intro hpos
      exact hnone ⟨i, hi, hpos⟩
    have hzero : i.1.val = 0 := Nat.eq_zero_of_not_pos hnotpos
    simp [adaptedWeightedBasis, hzero]
  have hlt := adaptedWeightSum_length_lt_of_exists_val_pos
    n L data hn o.occurrence.cell.left hexists
  rw [o.active_wall] at hweight
  rw [o.factor_count] at hlt
  omega

end PacketOccurrence

/-- The indexed sum over `Delta_k`; the subtype retains the original
`J_k` occurrence rather than constructing a new algebraic summand. -/
def GoverningWitness.supportedBracketRead
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) : ZMod (2 ^ data.exponent) :=
  (w.supportedPacketOccurrences n L data hn k).sum fun o z ↦
    z • o.1.bracketRead n L data hn k hk hkn

/-- Filtering from `J_k` to `Delta_k` changes no coefficient and discards
only occurrences whose read is already zero. -/
theorem GoverningWitness.packetBracketRead_eq_supportedBracketRead
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    (w.packetOccurrences n L data hn k).sum (fun o z ↦
        z • o.bracketRead n L data hn k hk hkn) =
      w.supportedBracketRead n L data hn k hk hkn := by
  classical
  rw [GoverningWitness.supportedBracketRead,
    GoverningWitness.supportedPacketOccurrences,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro o ho
  by_cases hs : o.IsSupported n L data hn k
  · rw [dif_pos hs, Finsupp.sum_single_index (by simp)]
  · rw [dif_neg hs]
    simp only [Finsupp.sum_zero_index]
    rw [o.bracketRead_eq_zero_of_not_supported n L data hn k hk hkn hs,
      smul_zero]

/-- The horizontal read of one occurrence and its vertical product read are
equal.  This is the local transfer--truncation square with the entire
contextual relation retained. -/
theorem PacketOccurrence.horizontal_eq_vertical_read
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (o : PacketOccurrence n L data hn k) :
    T n L data k hk hkn
        (rightSymbol n L data hn (n - k + 2) k (by omega)
          o.occurrence.cell.markedRow.value) =
      o.bracketRead n L data hn k hk hkn :=
  o.occurrence.cell.T_markedRow_eq_T_componentRow
    n L data hn k hk hkn o.factor_count o.active_wall

/-- Both indexed formulas, with literally identical occurrence indices,
coefficients, and orientations.  This is the formal capstone for `J_k` and
`Delta_k`. -/
theorem GoverningWitness.indexed_packet_reads
    {a : L} (w : GoverningWitness n L data a)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    let lower := Koszul.PresentationHomology.oneMap
      (presentation n L data k (by omega) (by omega))
      (presentation (n := n) L data (k - 1) (by omega) (by omega))
      (presentationProjection n L data k hk (by omega))
      (n - k + 1) (w.packetChain n L data hn k hk hkn)
    Phi n L data k hk hkn lower =
        w.supportedBracketRead n L data hn k hk hkn ∧
      T n L data k hk hkn
        (Koszul.dOne (presentation n L data k (by omega) (by omega))
          (n - k + 1) (w.packetChain n L data hn k hk hkn)) =
        w.supportedBracketRead n L data hn k hk hkn := by
  dsimp only
  have htrans := LinearMap.congr_fun (transgression n L data k hk hkn)
    (w.packetChain n L data hn k hk hkn)
  have hvertical :
      T n L data k hk hkn
          (Koszul.dOne (presentation n L data k (by omega) (by omega))
            (n - k + 1) (w.packetChain n L data hn k hk hkn)) =
        w.supportedBracketRead n L data hn k hk hkn := by
    rw [w.dOne_packetChain n L data hn k hk hkn, map_finsuppSum]
    calc
      _ = (w.packetOccurrences n L data hn k).sum (fun o z ↦
          z • o.bracketRead n L data hn k hk hkn) := by
        apply Finsupp.sum_congr
        intro o ho
        rw [map_zsmul, o.horizontal_eq_vertical_read n L data hn k hk hkn]
      _ = _ := w.packetBracketRead_eq_supportedBracketRead
        n L data hn k hk hkn
  exact ⟨htrans.trans hvertical, hvertical⟩

end


end LieRings.MetabelianVanishing
