import LieRings.DimensionSubring.MetabelianOdd.WeightedPresentation
import LieRings.DimensionSubring.DegreeFive.CoordinatePBW
import LieRings.DimensionSubring.DegreeFive.AdaptedSmith
import LieRings.DimensionSubring.DegreeFive.PacketCollector
import LieRings.DimensionSubring.DegreeFive.PlacedIdentities
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Sort

/-!
# The marked rewrite ledger

This module contains the provenance-preserving induction used by the metabelian collector.
It extends the existing deterministic `FiniteTaggedCollector` without changing that proved
infrastructure.  Occurrences are labelled by their path in the fixed rewrite tree, so equal
packets produced at different cells remain distinguishable.
-/

namespace LieRings.DimensionSubring.MetabelianOdd

noncomputable section

open LieRings.DegreeFive
open LieRings.PBW

universe u v

variable {P : Type u} {A : Type v} [AddCommGroup A]

/-! ## Reading the higher diagonal PBW cells -/

private theorem pbwCoeff_iota_eq_zero_of_factorNumber_ne_one
    (X : Type u) [Finite X] (N : ℕ)
    (x : TruncatedFreeLie X N)
    (e : TruncatedBasisIndex X N →₀ ℕ)
    (he : factorNumber X e ≠ 1) :
    pbwCoeff X N (UniversalEnvelopingAlgebra.ι ℤ x) e = 0 := by
  let b := truncatedHomogeneousBasis X N
  have hinverse :
      (truncatedPBWLinearEquiv X N).symm
          (UniversalEnvelopingAlgebra.ι ℤ x) =
        basisPolynomial ℤ (TruncatedFreeLie X N)
          (TruncatedBasisIndex X N) b x := by
    apply (truncatedPBWLinearEquiv X N).injective
    change (truncatedPBWLinearEquiv X N)
          ((truncatedPBWLinearEquiv X N).symm
            (UniversalEnvelopingAlgebra.ι ℤ x)) =
        (truncatedPBWLinearEquiv X N)
          (basisPolynomial ℤ (TruncatedFreeLie X N)
            (TruncatedBasisIndex X N) b x)
    rw [LinearEquiv.apply_symm_apply]
    change UniversalEnvelopingAlgebra.ι ℤ x =
      orderedPBWMap ℤ (TruncatedFreeLie X N)
        (TruncatedBasisIndex X N) b
          (basisPolynomial ℤ (TruncatedFreeLie X N)
            (TruncatedBasisIndex X N) b x)
    exact (orderedPBWMap_basisPolynomial ℤ (TruncatedFreeLie X N)
      (TruncatedBasisIndex X N) b x).symm
  unfold pbwCoeff
  rw [hinverse]
  unfold basisPolynomial
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  classical
  change MvPolynomial.coeff e
      ((b.repr x).sum (fun i c ↦ c • MvPolynomial.X i)) = 0
  unfold Finsupp.sum
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  suffices e ≠ Finsupp.single i 1 by
    dsimp
    change (MvPolynomial.coeffAddMonoidHom (R := ℤ) e)
      ((b.repr x) i • MvPolynomial.X i) = 0
    rw [(MvPolynomial.coeffAddMonoidHom (R := ℤ) e).map_zsmul
      (MvPolynomial.X i) ((b.repr x) i)]
    change (b.repr x) i • MvPolynomial.coeff e (MvPolynomial.X i) = 0
    rw [MvPolynomial.coeff_X']
    simp [Ne.symm this]
  intro hei
  apply he
  subst e
  simp [factorNumber]

/-- A direct finite read of the factor-`n+2-k`, weight-`n+1` PBW diagonal.  The coefficient
function is deliberately an argument: at its sole use below it is the top coordinate of the
long bracket appearing in `T_k`. -/
private def higherCellRead (X : Type u) [Finite X]
    (n k q : ℕ)
    (τ : (TruncatedBasisIndex X (2 * n) →₀ ℕ) → ZMod q)
    (z : UEA ℤ (TruncatedFreeLie X (2 * n))) : ZMod q := by
  classical
  exact ((truncatedPBWLinearEquiv X (2 * n)).symm z).support.sum fun e ↦
    if factorNumber X e = n + 2 - k ∧ totalWeight X e = n + 1 then
      (pbwCoeff X (2 * n) z e : ZMod q) * τ e
    else 0

private theorem higherCellRead_relationSide_eq_zero
    (n : ℕ) (hn : 3 ≤ n)
    (L : Type u) [LieRing L] [Finite L]
    (R : ReducedData n L) (a : L)
    (w : GoverningWitness n L a)
    (hgoverning : ∀ e : TruncatedBasisIndex L (2 * n) →₀ ℕ,
      totalWeight L e ≤ 2 * n →
        pbwCoeff L (2 * n) w.relationSide e =
          pbwCoeff L (2 * n)
            (UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk L (2 * n)
                (w.zTilde : CanonicalFreeLie L))) e)
    (k : ℕ) (hk : 2 ≤ k ∧ k < n)
    (τ : (TruncatedBasisIndex L (2 * n) →₀ ℕ) →
      ZMod (2 ^ R.topExponent)) :
    higherCellRead L n k (2 ^ R.topExponent) τ w.relationSide = 0 := by
  classical
  unfold higherCellRead
  apply Finset.sum_eq_zero
  intro e he
  split_ifs with hshape
  · obtain ⟨hfactors, hweight⟩ := hshape
    have hweightLe : totalWeight L e ≤ 2 * n := by omega
    have hfactorNe : factorNumber L e ≠ 1 := by
      rw [hfactors]
      omega
    have hrhs := pbwCoeff_iota_eq_zero_of_factorNumber_ne_one
      L (2 * n)
      (truncatedFreeLieMk L (2 * n)
        (w.zTilde : CanonicalFreeLie L)) e hfactorNe
    rw [hgoverning e hweightLe, hrhs]
    simp
  · rfl

private def homogeneousBasisLift (X : Type u) [Finite X] {N : ℕ}
    (i : TruncatedBasisIndex X N) : FreeLieAlgebra ℤ X :=
  ((freeLieExactBasis X (truncatedBasisWeight X i) i.2 :
      freeLieExact X (truncatedBasisWeight X i)) : FreeLieAlgebra ℤ X)

private def leftNormedBracket {M : Type*} [LieRing M] :
    M → List M → M :=
  List.foldl fun x y ↦ ⁅x, y⁆

private theorem leftNormedBracket_mem_lieHigh
    (X : Type u) [Finite X]
    {r : ℕ} {x : FreeLieAlgebra ℤ X}
    (hx : x ∈ FreeLieDimension.lieHigh X r)
    (xs : List (FreeLieAlgebra ℤ X))
    (hxs : ∀ y ∈ xs, y ∈ FreeLieDimension.lieHigh X 1) :
    leftNormedBracket x xs ∈
      FreeLieDimension.lieHigh X (r + xs.length) := by
  induction xs generalizing r x with
  | nil => simpa [leftNormedBracket] using hx
  | cons y ys ih =>
      have hy := hxs y (by simp)
      have hrest : ∀ z ∈ ys,
          z ∈ FreeLieDimension.lieHigh X 1 := by
        intro z hz
        exact hxs z (by simp [hz])
      have hbracket : ⁅x, y⁆ ∈
          FreeLieDimension.lieHigh X (r + 1) :=
        FreeLieDimension.lieHigh_lie_mem X hx hy
      have h := ih hbracket hrest
      change leftNormedBracket ⁅x, y⁆ ys ∈
        FreeLieDimension.lieHigh X (r + (y :: ys).length)
      have hindex : r + 1 + ys.length = r + (y :: ys).length := by
        simp
        omega
      rw [← hindex]
      exact h

private def exponentWord (X : Type u) [Finite X] {N : ℕ}
    (e : TruncatedBasisIndex X N →₀ ℕ) :
    List (TruncatedBasisIndex X N) :=
  (Finsupp.toMultiset e).sort (· ≤ ·)

/-- Formula `(T_k)` on one ordered PBW exponent vector.  Its `reverse` pattern merely picks the
unique possible weight-`k` factor; the teeth are reversed back before forming the long bracket.
Outside the diagonal shape the value is zero. -/
private def higherTCoordinate
    (n k : ℕ) (L : Type u) [LieRing L] [Finite L]
    (R : ReducedData n L)
    (e : TruncatedBasisIndex L (2 * n) →₀ ℕ) :
    ZMod (2 ^ R.topExponent) := by
  classical
  let is := exponentWord L e
  cases hrev : is.reverse with
  | nil => exact 0
  | cons d teeth =>
      by_cases hshape :
          k ≤ n + 1 ∧ truncatedBasisWeight L d = k ∧
            (∀ i ∈ teeth, truncatedBasisWeight L i = 1) ∧
            teeth.length = n + 1 - k
      · let comb : CanonicalFreeLie L :=
          leftNormedBracket (homogeneousBasisLift L d)
            (teeth.reverse.map (homogeneousBasisLift L))
        have hdHigh : homogeneousBasisLift L d ∈
            FreeLieDimension.lieHigh L k := by
          rw [← hshape.2.1]
          exact freeLieExact_mem_lieHigh L
            (freeLieExactBasis L (truncatedBasisWeight L d) d.2)
        have hteeth : ∀ y ∈
            teeth.reverse.map (homogeneousBasisLift L),
            y ∈ FreeLieDimension.lieHigh L 1 := by
          intro y hy
          simp only [List.mem_map] at hy
          obtain ⟨i, hi, rfl⟩ := hy
          have hi' : i ∈ teeth := by
            simpa using hi
          rw [← hshape.2.2.1 i hi']
          exact freeLieExact_mem_lieHigh L
            (freeLieExactBasis L (truncatedBasisWeight L i) i.2)
        have hcombHigh : comb ∈
            FreeLieDimension.lieHigh L (n + 1) := by
          have h := leftNormedBracket_mem_lieHigh L hdHigh
            (teeth.reverse.map (homogeneousBasisLift L)) hteeth
          simp only [List.length_map, List.length_reverse] at h
          simpa [comb, hshape.2.2.2, hshape.1] using h
        have hcombLcs : canonicalFreeLieEvaluation L comb ∈
            lowerCentralSeries ℤ L n := by
          have hfree : comb ∈
              lowerCentralSeries ℤ (CanonicalFreeLie L) n := by
            simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L n]
              using hcombHigh
          apply (LieIdeal.map_lowerCentralSeries_le
            (R := ℤ) (f := canonicalFreeLieEvaluation L) n)
          exact LieIdeal.mem_map hfree
        exact R.topEquiv ⟨canonicalFreeLieEvaluation L comb, hcombLcs⟩
      · exact 0

private theorem higherDiagonalCells_eq_zero
    (n : ℕ) (hn : 3 ≤ n)
    (L : Type u) [LieRing L] [Finite L]
    (R : ReducedData n L) (a : L)
    (w : GoverningWitness n L a)
    (hgoverning : ∀ e : TruncatedBasisIndex L (2 * n) →₀ ℕ,
      totalWeight L e ≤ 2 * n →
        pbwCoeff L (2 * n) w.relationSide e =
          pbwCoeff L (2 * n)
            (UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk L (2 * n)
                (w.zTilde : CanonicalFreeLie L))) e) :
    ∀ k, 2 ≤ k → k < n →
      higherCellRead L n k (2 ^ R.topExponent)
        (higherTCoordinate n k L R) w.relationSide = 0 := by
  intro k hk hkn
  exact higherCellRead_relationSide_eq_zero n hn L R a w hgoverning
    k ⟨hk, hkn⟩ (higherTCoordinate n k L R)

/-! ## The concrete marked truncation collector

This is the semantic instance required by the closed-square ledger.  A prefix packet retains
one full relation together with a truncation mark.  Splitting the mark produces the next prefix
and the exact homogeneous component; ordinary packets are then PBW-collected.  The quadratic
prefix and the terminal one-factor prefix are deliberately frozen. -/

private def markedBasisIndexOf
    (X : Type u) [Finite X] {n k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ 2 * n)
    (i : FreeLieExactBasisIndex X k) : TruncatedBasisIndex X (2 * n) := by
  cases k with
  | zero => omega
  | succ t => exact ⟨⟨t, by omega⟩, i⟩

@[simp] private theorem markedBasisIndexOf_weight
    (X : Type u) [Finite X] {n k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ 2 * n)
    (i : FreeLieExactBasisIndex X k) :
    truncatedBasisWeight X (markedBasisIndexOf X hk hkN i) = k := by
  cases k with
  | zero => omega
  | succ t => simp [markedBasisIndexOf, truncatedBasisWeight]

private theorem markedBasisIndexOf_value
    (X : Type u) [Finite X] {n k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ 2 * n)
    (i : FreeLieExactBasisIndex X k) :
    truncatedHomogeneousBasis X (2 * n)
        (markedBasisIndexOf X hk hkN i) =
      truncatedFreeLieMk X (2 * n)
        (((freeLieExactBasis X k i : freeLieExact X k)) :
          CanonicalFreeLie X) := by
  cases k with
  | zero => omega
  | succ t => simp [markedBasisIndexOf]

private def markedPrefixFree
    (X : Type u) [LieRing X] [Finite X] (k : ℕ)
    (r : CanonicalLieRelationsIdeal X) : CanonicalFreeLie X :=
  ∑ s : Fin k,
    (((⟨freeLieLengthComponent X (s.1 + 1) (r : CanonicalFreeLie X),
      freeLieLengthComponent_mem_exact X (s.1 + 1)
        (r : CanonicalFreeLie X)⟩ : freeLieExact X (s.1 + 1)) :
          CanonicalFreeLie X))

private inductive MarkedPBWPacket
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) where
  | marked (relation : CanonicalLieRelationsIdeal X)
      (mark : Fin (2 * n + 1))
      (factors : List (TruncatedBasisIndex X (2 * n)))
  | word (factors : List (TruncatedBasisIndex X (2 * n)))

private def MarkedPBWPacket.value
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    MarkedPBWPacket X n → UEA ℤ (TruncatedFreeLie X (2 * n))
  | .marked r k xs =>
      basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n))
            (truncatedHomogeneousBasis X (2 * n)) xs *
        UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk X (2 * n) (markedPrefixFree X k.1 r))
  | .word xs => basisWord ℤ (TruncatedFreeLie X (2 * n))
      (TruncatedBasisIndex X (2 * n))
        (truncatedHomogeneousBasis X (2 * n)) xs

private def markedInversionCount
    (X : Type u) [Finite X] {n : ℕ} :
    List (TruncatedBasisIndex X (2 * n)) → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + markedInversionCount X xs

private theorem markedInversionCount_swap
    (X : Type u) [Finite X] {n : ℕ}
    (left right : List (TruncatedBasisIndex X (2 * n)))
    (x y : TruncatedBasisIndex X (2 * n)) (hxy : y < x) :
    markedInversionCount X (left ++ x :: y :: right) =
      markedInversionCount X (left ++ y :: x :: right) + 1 := by
  induction left with
  | nil =>
      have hnx : ¬x < y := not_lt_of_ge (le_of_lt hxy)
      simp [markedInversionCount, hxy, hnx, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
  | cons z left ih =>
      simp only [List.cons_append, markedInversionCount]
      have hfilter :
          ((left ++ x :: y :: right).filter (· < z)).length =
            ((left ++ y :: x :: right).filter (· < z)).length := by
        simp only [List.filter_append, List.filter_cons, List.length_append]
        split <;> split <;> simp <;> omega
      rw [hfilter, ih]
      omega

private def markedBracketCoefficients
    (X : Type u) [Finite X] {n : ℕ}
    (x y : TruncatedBasisIndex X (2 * n))
    (hxy : truncatedBasisWeight X x + truncatedBasisWeight X y ≤ 2 * n) :
    TruncatedBasisIndex X (2 * n) →₀ ℤ :=
  (homogeneousBracketCoefficients X
      (freeLieExactBasis X (truncatedBasisWeight X x) x.2)
      (freeLieExactBasis X (truncatedBasisWeight X y) y.2)).mapDomain
    (markedBasisIndexOf X
      (Nat.add_pos_left (truncatedBasisWeight_pos X x) _) hxy)

private theorem markedBracketCoefficients_sum
    (X : Type u) [Finite X] {n : ℕ}
    (x y : TruncatedBasisIndex X (2 * n))
    (hxy : truncatedBasisWeight X x + truncatedBasisWeight X y ≤ 2 * n) :
    (markedBracketCoefficients X x y hxy).sum
        (fun i c ↦ c • truncatedHomogeneousBasis X (2 * n) i) =
      ⁅truncatedHomogeneousBasis X (2 * n) x,
        truncatedHomogeneousBasis X (2 * n) y⁆ := by
  unfold markedBracketCoefficients
  rw [Finsupp.sum_mapDomain_index]
  · let x' := freeLieExactBasis X (x.1.1 + 1) x.2
    let y' := freeLieExactBasis X (y.1.1 + 1) y.2
    let c := homogeneousBracketCoefficients X x' y'
    change c.sum (fun i z ↦ z •
        truncatedHomogeneousBasis X (2 * n)
          (markedBasisIndexOf X
            (Nat.add_pos_left (truncatedBasisWeight_pos X x) _) hxy i)) = _
    simp_rw [markedBasisIndexOf_value]
    calc
      c.sum (fun i z ↦ z • truncatedFreeLieMk X (2 * n)
          (((freeLieExactBasis X
            (truncatedBasisWeight X x + truncatedBasisWeight X y)) i :
              freeLieExact X
                (truncatedBasisWeight X x + truncatedBasisWeight X y)) :
                  CanonicalFreeLie X)) =
          truncatedFreeLieMk X (2 * n)
            (c.sum (fun i z ↦ z •
              (((freeLieExactBasis X
                (truncatedBasisWeight X x + truncatedBasisWeight X y)) i :
                  freeLieExact X
                    (truncatedBasisWeight X x + truncatedBasisWeight X y)) :
                      CanonicalFreeLie X))) := by
            rw [map_finsuppSum]
            apply Finsupp.sum_congr
            intro i hi
            rw [map_zsmul]
      _ = truncatedFreeLieMk X (2 * n) ⁅(x' : CanonicalFreeLie X),
          (y' : CanonicalFreeLie X)⁆ := by
            apply congrArg (truncatedFreeLieMk X (2 * n))
            exact homogeneousBracketCoefficients_sum X x' y'
      _ = ⁅truncatedHomogeneousBasis X (2 * n) x,
          truncatedHomogeneousBasis X (2 * n) y⁆ := by
            rw [LieHom.map_lie]
            simp [x', y']
  · intro i
    simp
  · intro i a b
    simp [add_smul]

private def markedComponentCoefficients
    (X : Type u) [LieRing X] [Finite X] {k : ℕ}
    (r : CanonicalLieRelationsIdeal X) :
    FreeLieExactBasisIndex X k →₀ ℤ :=
  (freeLieExactBasis X k).repr
    ⟨freeLieLengthComponent X k (r : CanonicalFreeLie X),
      freeLieLengthComponent_mem_exact X k (r : CanonicalFreeLie X)⟩

private theorem markedPrefixFree_step
    (X : Type u) [LieRing X] [Finite X] {k : ℕ} (hk : 0 < k)
    (r : CanonicalLieRelationsIdeal X) :
    markedPrefixFree X k r = markedPrefixFree X (k - 1) r +
      ((⟨freeLieLengthComponent X k (r : CanonicalFreeLie X),
          freeLieLengthComponent_mem_exact X k
            (r : CanonicalFreeLie X)⟩ : freeLieExact X k) :
        CanonicalFreeLie X) := by
  cases k with
  | zero => omega
  | succ t =>
      unfold markedPrefixFree
      rw [Fin.sum_univ_castSucc]
      rfl

private theorem markedComponentCoefficients_sum
    (X : Type u) [LieRing X] [Finite X] {k : ℕ}
    (r : CanonicalLieRelationsIdeal X) :
    (markedComponentCoefficients X (k := k) r).sum (fun i z ↦ z •
        (((freeLieExactBasis X k i : freeLieExact X k)) :
          CanonicalFreeLie X)) =
      ((⟨freeLieLengthComponent X k (r : CanonicalFreeLie X),
          freeLieLengthComponent_mem_exact X k
            (r : CanonicalFreeLie X)⟩ : freeLieExact X k) :
        CanonicalFreeLie X) := by
  let component : freeLieExact X k :=
    ⟨freeLieLengthComponent X k (r : CanonicalFreeLie X),
      freeLieLengthComponent_mem_exact X k (r : CanonicalFreeLie X)⟩
  have hrepr := (freeLieExactBasis X k).linearCombination_repr component
  calc
    (markedComponentCoefficients X (k := k) r).sum (fun i z ↦ z •
        (((freeLieExactBasis X k i : freeLieExact X k)) :
          CanonicalFreeLie X)) =
      (freeLieExact X k).subtype
        ((markedComponentCoefficients X (k := k) r).sum
          (fun i z ↦ z • freeLieExactBasis X k i)) := by
            rw [map_finsuppSum]
            apply Finsupp.sum_congr
            intro i hi
            rw [map_zsmul]
            rfl
    _ = (component : CanonicalFreeLie X) := by
      exact congrArg Subtype.val hrepr
    _ = _ := rfl

private def markedSupportPackets {I P : Type*} [DecidableEq I]
    (c : I →₀ ℤ) (f : I → P) : List (ℤ × P) :=
  c.support.toList.map fun i ↦ (c i, f i)

private theorem markedSupportPackets_value
    {I P B : Type*} [DecidableEq I] [AddCommGroup B]
    (c : I →₀ ℤ) (f : I → P) (v : P → B) :
    ((markedSupportPackets c f).map fun q ↦ q.1 • v q.2).sum =
      c.sum fun i z ↦ z • v (f i) := by
  classical
  simp [markedSupportPackets, Finsupp.sum]

private def markedPacketExpansion
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    MarkedPBWPacket X n → Option (List (ℤ × MarkedPBWPacket X n))
  | .marked r k xs =>
      if (xs.length = 0 ∧ k.1 = n + 1) ∨
          (xs.length = 1 ∧ k.1 = n) then none
      else if hk : k.1 = 0 then some []
      else
        let k' : Fin (2 * n + 1) := ⟨k.1 - 1, by omega⟩
        let c := markedComponentCoefficients X (k := k.1) r
        some ((1, .marked r k' xs) ::
          markedSupportPackets c fun i ↦
            .word (xs ++ [markedBasisIndexOf X (by omega) (by omega) i]))
  | .word xs =>
      match chooseAdjacentInversion? xs with
      | none => none
      | some d =>
          if hweight : truncatedBasisWeight X d.x +
              truncatedBasisWeight X d.y ≤ 2 * n then
            let c := markedBracketCoefficients X d.x d.y hweight
            some ((1, .word (d.left ++ d.y :: d.x :: d.right)) ::
              markedSupportPackets c fun i ↦
                .word (d.left ++ i :: d.right))
          else some [(1, .word (d.left ++ d.y :: d.x :: d.right))]

private def markedPacketComplexity
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    MarkedPBWPacket X n → ℕ × (ℕ × ℕ)
  | .marked _ k _ => (1, k.1, 0)
  | .word xs => (0, xs.length, markedInversionCount X xs)

private def MarkedPacketDescent
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    (new old : MarkedPBWPacket X n) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
    (markedPacketComplexity X new) (markedPacketComplexity X old)

private theorem markedPacketDescent_wellFounded
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    WellFounded (MarkedPacketDescent X (n := n)) :=
  InvImage.wf (markedPacketComplexity X)
    (Nat.lt_wfRel.wf.prod_lex (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))

private def markedPacketCollector
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    FiniteTaggedCollector (MarkedPBWPacket X n)
      (UEA ℤ (TruncatedFreeLie X (2 * n))) where
  relation := MarkedPacketDescent X
  wellFounded := markedPacketDescent_wellFounded X n
  expansion := markedPacketExpansion X n
  value := MarkedPBWPacket.value X n
  decreases := by
    classical
    intro p qs hp q hq
    cases p with
    | marked r k xs =>
        simp only [markedPacketExpansion] at hp
        split at hp
        · simp at hp
        · split at hp
          · rcases Option.some.inj hp with rfl
            simp at hq
          · rename_i hk
            rcases Option.some.inj hp with rfl
            rcases List.mem_cons.mp hq with hq | hq
            · subst q
              unfold MarkedPacketDescent markedPacketComplexity
              apply Prod.Lex.right 1
              apply Prod.Lex.left 0 0
              dsimp only
              omega
            · rcases q with ⟨cq, q⟩
              cases q with
              | marked r' k' ys =>
                  simp [markedSupportPackets] at hq
              | word ys =>
                  unfold MarkedPacketDescent markedPacketComplexity
                  exact Prod.Lex.left (ys.length, markedInversionCount X ys)
                    (k.1, 0) (by omega)
    | word xs =>
        simp only [markedPacketExpansion] at hp
        split at hp
        · simp at hp
        · rename_i d hchosen
          have hd := chooseAdjacentInversion?_eq_some_realizes hchosen
          rcases hd with ⟨hxs, hxy⟩
          split at hp
          · rename_i hweight
            rcases Option.some.inj hp with rfl
            rcases List.mem_cons.mp hq with hq | hq
            · subst q
              unfold MarkedPacketDescent markedPacketComplexity
              apply Prod.Lex.right 0
              have hlen :
                  (d.left ++ d.y :: d.x :: d.right).length = xs.length := by
                rw [hxs]
                simp
              rw [hlen]
              apply Prod.Lex.right xs.length
              have hinv := markedInversionCount_swap X d.left d.right
                d.x d.y hxy
              rw [hxs]
              omega
            · rcases q with ⟨cq, q⟩
              cases q with
              | marked r k ys =>
                  simp [markedSupportPackets] at hq
              | word ys =>
                  simp only [markedSupportPackets, List.mem_map] at hq
                  obtain ⟨i, hi, hci, rfl⟩ := hq
                  unfold MarkedPacketDescent markedPacketComplexity
                  apply Prod.Lex.right 0
                  apply Prod.Lex.left (markedInversionCount X
                    (d.left ++ i :: d.right)) (markedInversionCount X xs)
                  rw [hxs]
                  simp
          · rcases Option.some.inj hp with rfl
            simp only [List.mem_singleton] at hq
            subst q
            unfold MarkedPacketDescent markedPacketComplexity
            apply Prod.Lex.right 0
            have hlen :
                (d.left ++ d.y :: d.x :: d.right).length = xs.length := by
              rw [hxs]
              simp
            rw [hlen]
            apply Prod.Lex.right xs.length
            have hinv := markedInversionCount_swap X d.left d.right
              d.x d.y hxy
            rw [hxs]
            omega
  preserves := by
    classical
    intro p qs hp
    cases p with
    | marked r k xs =>
        simp only [markedPacketExpansion] at hp
        split at hp
        · simp at hp
        · split at hp
          · rename_i hk
            rcases Option.some.inj hp with rfl
            have hkFin : k = ⟨0, by omega⟩ := by
              apply Fin.ext
              exact hk
            rw [hkFin]
            simp [MarkedPBWPacket.value, markedPrefixFree]
          · rename_i hk
            rcases Option.some.inj hp with rfl
            let k' : Fin (2 * n + 1) := ⟨k.1 - 1, by omega⟩
            let c := markedComponentCoefficients X (k := k.1) r
            let b := truncatedHomogeneousBasis X (2 * n)
            let tail := basisWord ℤ (TruncatedFreeLie X (2 * n))
              (TruncatedBasisIndex X (2 * n)) b xs
            have hcomponent :
                c.sum (fun i z ↦ z •
                  truncatedFreeLieMk X (2 * n)
                    (((freeLieExactBasis X k.1 i : freeLieExact X k.1)) :
                      CanonicalFreeLie X)) =
                  truncatedFreeLieMk X (2 * n)
                    ((⟨freeLieLengthComponent X k.1
                        (r : CanonicalFreeLie X),
                        freeLieLengthComponent_mem_exact X k.1
                        (r : CanonicalFreeLie X)⟩ :
                        freeLieExact X k.1) : CanonicalFreeLie X) := by
              calc
                c.sum (fun i z ↦ z •
                    truncatedFreeLieMk X (2 * n)
                      (((freeLieExactBasis X k.1 i : freeLieExact X k.1)) :
                        CanonicalFreeLie X)) =
                    truncatedFreeLieMk X (2 * n)
                      (c.sum (fun i z ↦ z •
                        (((freeLieExactBasis X k.1 i : freeLieExact X k.1)) :
                          CanonicalFreeLie X))) := by
                            rw [map_finsuppSum]
                            apply Finsupp.sum_congr
                            intro i hi
                            rw [map_zsmul]
                _ = _ := congrArg (truncatedFreeLieMk X (2 * n))
                  (markedComponentCoefficients_sum X r)
            have hemitted :
                ((markedSupportPackets c fun i ↦
                    MarkedPBWPacket.word
                      (xs ++ [markedBasisIndexOf X (by omega) (by omega) i])).map
                    fun q ↦ q.1 • MarkedPBWPacket.value X n q.2).sum =
                  tail * UniversalEnvelopingAlgebra.ι ℤ
                    (truncatedFreeLieMk X (2 * n)
                      ((⟨freeLieLengthComponent X k.1
                          (r : CanonicalFreeLie X),
                        freeLieLengthComponent_mem_exact X k.1
                          (r : CanonicalFreeLie X)⟩ :
                          freeLieExact X k.1) : CanonicalFreeLie X)) := by
              rw [markedSupportPackets_value]
              have hbasisAppend (i : TruncatedBasisIndex X (2 * n)) :
                  basisWord ℤ (TruncatedFreeLie X (2 * n))
                      (TruncatedBasisIndex X (2 * n)) b (xs ++ [i]) =
                    tail * UniversalEnvelopingAlgebra.ι ℤ (b i) := by
                simp [tail, basisWord, word, List.map_append]
              change c.sum (fun i z ↦ z •
                basisWord ℤ (TruncatedFreeLie X (2 * n))
                  (TruncatedBasisIndex X (2 * n)) b
                    (xs ++ [markedBasisIndexOf X (by omega) (by omega) i])) = _
              simp_rw [hbasisAppend]
              change c.sum (fun i z ↦ z •
                  (tail * UniversalEnvelopingAlgebra.ι ℤ
                    (truncatedHomogeneousBasis X (2 * n)
                      (markedBasisIndexOf X (by omega) (by omega) i)))) = _
              simp_rw [markedBasisIndexOf_value]
              calc
                c.sum (fun i z ↦ z •
                    (tail * UniversalEnvelopingAlgebra.ι ℤ
                      (truncatedFreeLieMk X (2 * n)
                        (((freeLieExactBasis X k.1 i : freeLieExact X k.1)) :
                          CanonicalFreeLie X)))) =
                    c.sum (fun i z ↦ tail *
                      UniversalEnvelopingAlgebra.ι ℤ
                        (z • truncatedFreeLieMk X (2 * n)
                          (((freeLieExactBasis X k.1 i : freeLieExact X k.1)) :
                            CanonicalFreeLie X))) := by
                              apply Finsupp.sum_congr
                              intro i hi
                              rw [map_zsmul, mul_smul_comm]
                _ = tail * UniversalEnvelopingAlgebra.ι ℤ
                    (c.sum (fun i z ↦ z •
                      truncatedFreeLieMk X (2 * n)
                        (((freeLieExactBasis X k.1 i : freeLieExact X k.1)) :
                          CanonicalFreeLie X))) := by
                            rw [map_finsuppSum, Finsupp.mul_sum]
                _ = _ := by rw [hcomponent]
            simp only [List.map_cons, List.sum_cons, one_smul]
            rw [hemitted]
            change
              tail * UniversalEnvelopingAlgebra.ι ℤ
                    (truncatedFreeLieMk X (2 * n)
                      (markedPrefixFree X k'.1 r)) +
                  tail * UniversalEnvelopingAlgebra.ι ℤ
                    (truncatedFreeLieMk X (2 * n)
                      ((⟨freeLieLengthComponent X k.1
                          (r : CanonicalFreeLie X),
                        freeLieLengthComponent_mem_exact X k.1
                          (r : CanonicalFreeLie X)⟩ :
                          freeLieExact X k.1) : CanonicalFreeLie X)) =
                tail * UniversalEnvelopingAlgebra.ι ℤ
                    (truncatedFreeLieMk X (2 * n)
                      (markedPrefixFree X k.1 r))
            rw [← mul_add, ← map_add, ← map_add]
            congr 3
            simpa [k'] using (markedPrefixFree_step X (by omega) r).symm
    | word xs =>
        simp only [markedPacketExpansion] at hp
        split at hp
        · simp at hp
        · rename_i d hchosen
          have hd := chooseAdjacentInversion?_eq_some_realizes hchosen
          rcases hd with ⟨hxs, hxy⟩
          let swapped := d.left ++ d.y :: d.x :: d.right
          split at hp
          · rename_i hweight
            rcases Option.some.inj hp with rfl
            let c := markedBracketCoefficients X d.x d.y hweight
            let correction := fun i : TruncatedBasisIndex X (2 * n) ↦
              d.left ++ i :: d.right
            have hcoeff := markedBracketCoefficients_sum X d.x d.y hweight
            let context : TruncatedFreeLie X (2 * n) →+
                UEA ℤ (TruncatedFreeLie X (2 * n)) :=
              { toFun := fun z ↦
                  word ℤ (TruncatedFreeLie X (2 * n))
                      (d.left.map (truncatedHomogeneousBasis X (2 * n))) *
                    UniversalEnvelopingAlgebra.ι ℤ z *
                    word ℤ (TruncatedFreeLie X (2 * n))
                      (d.right.map (truncatedHomogeneousBasis X (2 * n)))
                map_zero' := by simp
                map_add' := by intro a b; simp [map_add, mul_add, add_mul] }
            have hcontext := congrArg context hcoeff
            rw [map_finsuppSum] at hcontext
            have hcorrection :
                ((markedSupportPackets c fun i ↦
                    MarkedPBWPacket.word (correction i)).map fun q ↦
                      q.1 • MarkedPBWPacket.value X n q.2).sum =
                  context ⁅truncatedHomogeneousBasis X (2 * n) d.x,
                    truncatedHomogeneousBasis X (2 * n) d.y⁆ := by
              rw [markedSupportPackets_value, ← hcontext]
              apply Finsupp.sum_congr
              intro i hi
              rw [map_zsmul]
              simp [MarkedPBWPacket.value, context, correction,
                basisWord, word, List.map_append]
              noncomm_ring
            have hswapWord := envelopingWord_adjacent_swap ℤ
              (TruncatedFreeLie X (2 * n))
              (d.left.map (truncatedHomogeneousBasis X (2 * n)))
              (d.right.map (truncatedHomogeneousBasis X (2 * n)))
              (truncatedHomogeneousBasis X (2 * n) d.x)
              (truncatedHomogeneousBasis X (2 * n) d.y)
            simp only [List.map_cons, List.sum_cons, one_smul]
            rw [hcorrection, hxs]
            simpa only [swapped, context, MarkedPBWPacket.value, basisWord,
              word, envelopingWord, List.map_append, List.map_cons,
              List.map_nil, List.map_map, Function.comp_apply] using hswapWord.symm
          · rename_i hweight
            rcases Option.some.inj hp with rfl
            have hbracket :
                ⁅truncatedHomogeneousBasis X (2 * n) d.x,
                  truncatedHomogeneousBasis X (2 * n) d.y⁆ = 0 := by
              rw [truncatedHomogeneousBasis_apply,
                truncatedHomogeneousBasis_apply, ← LieHom.map_lie]
              apply (LieSubmodule.Quotient.mk_eq_zero'
                (N := lowerCentralSeries ℤ (CanonicalFreeLie X) (2 * n))).mpr
              let bracketExact : freeLieExact X
                  (truncatedBasisWeight X d.x + truncatedBasisWeight X d.y) :=
                ⟨⁅((freeLieExactBasis X (d.x.1.1 + 1) d.x.2 :
                    freeLieExact X (d.x.1.1 + 1)) : CanonicalFreeLie X),
                  ((freeLieExactBasis X (d.y.1.1 + 1) d.y.2 :
                    freeLieExact X (d.y.1.1 + 1)) : CanonicalFreeLie X)⁆,
                  freeLieExact_bracket_mem X
                    (freeLieExactBasis X (d.x.1.1 + 1) d.x.2)
                    (freeLieExactBasis X (d.y.1.1 + 1) d.y.2)⟩
              have hb := freeLieExact_mem_lieHigh X bracketExact
              have hb' : (bracketExact : CanonicalFreeLie X) ∈
                  lowerCentralSeries ℤ (CanonicalFreeLie X)
                    (truncatedBasisWeight X d.x +
                      truncatedBasisWeight X d.y - 1) := by
                change (bracketExact : CanonicalFreeLie X) ∈
                  (lowerCentralSeries ℤ (CanonicalFreeLie X)
                    (truncatedBasisWeight X d.x +
                      truncatedBasisWeight X d.y - 1)).toLieSubalgebra.toSubmodule
                rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries]
                convert hb using 1 <;> omega
              exact LieModule.antitone_lowerCentralSeries ℤ
                (CanonicalFreeLie X) (CanonicalFreeLie X) (by omega) hb'
            have hswapWord := envelopingWord_adjacent_swap ℤ
              (TruncatedFreeLie X (2 * n))
              (d.left.map (truncatedHomogeneousBasis X (2 * n)))
              (d.right.map (truncatedHomogeneousBasis X (2 * n)))
              (truncatedHomogeneousBasis X (2 * n) d.x)
              (truncatedHomogeneousBasis X (2 * n) d.y)
            simp only [List.map_singleton, List.sum_singleton, one_smul]
            rw [hxs]
            rw [hbracket] at hswapWord
            simpa only [swapped, MarkedPBWPacket.value, basisWord, word,
              envelopingWord, List.map_append, List.map_cons, List.map_nil,
              List.map_map, Function.comp_apply, map_zero, mul_zero,
              zero_mul, add_zero] using hswapWord.symm

/-! ## Full-relation contexts for the two-filtered square

The preceding collector is the exact PBW/truncation engine.  The closed-square argument also
needs the mark to cross an ordinary factor *before* the marked relation is split.  A context
records the nested commutators created by those crossings.  Applying a context to a full
relation is still a full relation, while applying it to one homogeneous component is an
ordinary homogeneous Lie factor.  This is the finite, literal form of the two marked transfer
identities in the manuscript.
-/

private inductive RelationContext
    (X : Type u) [Finite X] (N : ℕ) where
  | hole
  | lieLeft (x : TruncatedBasisIndex X N) (c : RelationContext X N)
  | lieRight (c : RelationContext X N) (x : TruncatedBasisIndex X N)

private def RelationContext.weight
    (X : Type u) [Finite X] {N : ℕ} : RelationContext X N → ℕ
  | .hole => 0
  | .lieLeft x c => truncatedBasisWeight X x + c.weight X
  | .lieRight c x => c.weight X + truncatedBasisWeight X x

private def RelationContext.applyFree
    (X : Type u) [Finite X] {N : ℕ} :
    RelationContext X N → CanonicalFreeLie X → CanonicalFreeLie X
  | .hole, z => z
  | .lieLeft x c, z => ⁅homogeneousBasisLift X x, c.applyFree X z⁆
  | .lieRight c x, z => ⁅c.applyFree X z, homogeneousBasisLift X x⁆

private theorem RelationContext.applyFree_add
    (X : Type u) [Finite X] {N : ℕ} (c : RelationContext X N)
    (x y : CanonicalFreeLie X) :
    c.applyFree X (x + y) = c.applyFree X x + c.applyFree X y := by
  induction c with
  | hole => rfl
  | lieLeft z c ih => simp only [RelationContext.applyFree, ih, lie_add]
  | lieRight c z ih => simp only [RelationContext.applyFree, ih, add_lie]

private theorem RelationContext.applyFree_smul
    (X : Type u) [Finite X] {N : ℕ} (c : RelationContext X N)
    (a : ℤ) (x : CanonicalFreeLie X) :
    c.applyFree X (a • x) = a • c.applyFree X x := by
  induction c with
  | hole => rfl
  | lieLeft z c ih => simp only [RelationContext.applyFree, ih, lie_smul]
  | lieRight c z ih => simp only [RelationContext.applyFree, ih, smul_lie]

private theorem RelationContext.applyFree_mem_exact
    (X : Type u) [Finite X] {N k : ℕ} (c : RelationContext X N)
    (x : freeLieExact X k) :
    c.applyFree X (x : CanonicalFreeLie X) ∈
      freeLieExact X (k + c.weight X) := by
  induction c with
  | hole => simpa [RelationContext.applyFree, RelationContext.weight] using x.property
  | lieLeft z c ih =>
      have hbracket := freeLieExact_bracket_mem X
        (freeLieExactBasis X (truncatedBasisWeight X z) z.2)
        (⟨c.applyFree X (x : CanonicalFreeLie X), ih⟩ :
          freeLieExact X (k + c.weight X))
      change ⁅homogeneousBasisLift X z,
          c.applyFree X (x : CanonicalFreeLie X)⁆ ∈
        freeLieExact X (k +
          (truncatedBasisWeight X z + c.weight X))
      simpa [homogeneousBasisLift, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hbracket
  | lieRight c z ih =>
      have hbracket := freeLieExact_bracket_mem X
        (⟨c.applyFree X (x : CanonicalFreeLie X), ih⟩ :
          freeLieExact X (k + c.weight X))
        (freeLieExactBasis X (truncatedBasisWeight X z) z.2)
      change ⁅c.applyFree X (x : CanonicalFreeLie X),
          homogeneousBasisLift X z⁆ ∈
        freeLieExact X (k +
          (c.weight X + truncatedBasisWeight X z))
      simpa [homogeneousBasisLift, Nat.add_assoc] using hbracket

private theorem RelationContext.applyFree_mem_lieHigh
    (X : Type u) [Finite X] {N k : ℕ} (c : RelationContext X N)
    {x : CanonicalFreeLie X} (hx : x ∈ FreeLieDimension.lieHigh X k) :
    c.applyFree X x ∈
      FreeLieDimension.lieHigh X (k + c.weight X) := by
  induction c with
  | hole => simpa [RelationContext.applyFree, RelationContext.weight] using hx
  | lieLeft z c ih =>
      have hz := freeLieExact_mem_lieHigh X
        (freeLieExactBasis X (truncatedBasisWeight X z) z.2)
      have h := FreeLieDimension.lieHigh_lie_mem X hz ih
      simpa [RelationContext.applyFree, RelationContext.weight,
        homogeneousBasisLift, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h
  | lieRight c z ih =>
      have hz := freeLieExact_mem_lieHigh X
        (freeLieExactBasis X (truncatedBasisWeight X z) z.2)
      have h := FreeLieDimension.lieHigh_lie_mem X ih hz
      simpa [RelationContext.applyFree, RelationContext.weight,
        homogeneousBasisLift, Nat.add_assoc] using h

private def RelationContext.relation
    (X : Type u) [LieRing X] [Finite X] {N : ℕ}
    (c : RelationContext X N)
    (r : CanonicalLieRelationsIdeal X) : CanonicalLieRelationsIdeal X :=
  ⟨c.applyFree X (r : CanonicalFreeLie X), by
    induction c with
    | hole => exact r.property
    | lieLeft x c ih =>
        exact (CanonicalLieRelationsIdeal X).lie_mem ih
    | lieRight c x ih =>
        exact lie_mem_left ℤ (CanonicalFreeLie X)
          (CanonicalLieRelationsIdeal X) _ _ ih⟩

@[simp] private theorem RelationContext.relation_coe
    (X : Type u) [LieRing X] [Finite X] {N : ℕ}
    (c : RelationContext X N) (r : CanonicalLieRelationsIdeal X) :
    (c.relation X r : CanonicalFreeLie X) =
      c.applyFree X (r : CanonicalFreeLie X) := rfl

private def RelationContext.linearMap
    (X : Type u) [Finite X] {N : ℕ} (c : RelationContext X N) :
    CanonicalFreeLie X →ₗ[ℤ] CanonicalFreeLie X where
  toFun := c.applyFree X
  map_add' := c.applyFree_add X
  map_smul' := c.applyFree_smul X

private def contextBasisIndexOf
    (X : Type u) [Finite X] {N k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N)
    (i : FreeLieExactBasisIndex X k) : TruncatedBasisIndex X N := by
  cases k with
  | zero => omega
  | succ t => exact ⟨⟨t, by omega⟩, i⟩

@[simp] private theorem contextBasisIndexOf_weight
    (X : Type u) [Finite X] {N k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N)
    (i : FreeLieExactBasisIndex X k) :
    truncatedBasisWeight X (contextBasisIndexOf X hk hkN i) = k := by
  cases k with
  | zero => omega
  | succ t => simp [contextBasisIndexOf, truncatedBasisWeight]

private theorem contextBasisIndexOf_value
    (X : Type u) [Finite X] {N k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N)
    (i : FreeLieExactBasisIndex X k) :
    truncatedHomogeneousBasis X N (contextBasisIndexOf X hk hkN i) =
      truncatedFreeLieMk X N
        (((freeLieExactBasis X k i : freeLieExact X k)) :
          CanonicalFreeLie X) := by
  cases k with
  | zero => omega
  | succ t => simp [contextBasisIndexOf]

private def contextComponentExact
    (X : Type u) [LieRing X] [Finite X] {N : ℕ}
    (c : RelationContext X N) (r : CanonicalLieRelationsIdeal X)
    (k : ℕ) : freeLieExact X (k + c.weight X) :=
  ⟨c.applyFree X
      ((⟨freeLieLengthComponent X k (r : CanonicalFreeLie X),
        freeLieLengthComponent_mem_exact X k
          (r : CanonicalFreeLie X)⟩ : freeLieExact X k) :
            CanonicalFreeLie X),
    c.applyFree_mem_exact X
      ⟨freeLieLengthComponent X k (r : CanonicalFreeLie X),
        freeLieLengthComponent_mem_exact X k
          (r : CanonicalFreeLie X)⟩⟩

private def contextComponentCoefficients
    (X : Type u) [LieRing X] [Finite X] {N : ℕ}
    (c : RelationContext X N) (r : CanonicalLieRelationsIdeal X)
    (k : ℕ) : FreeLieExactBasisIndex X (k + c.weight X) →₀ ℤ :=
  (freeLieExactBasis X (k + c.weight X)).repr
    (contextComponentExact X c r k)

private theorem contextComponentCoefficients_sum
    (X : Type u) [LieRing X] [Finite X] {N : ℕ}
    (c : RelationContext X N) (r : CanonicalLieRelationsIdeal X)
    (k : ℕ) :
    (contextComponentCoefficients X c r k).sum (fun i z ↦ z •
        (((freeLieExactBasis X (k + c.weight X) i :
          freeLieExact X (k + c.weight X))) : CanonicalFreeLie X)) =
      (contextComponentExact X c r k : CanonicalFreeLie X) := by
  let z := contextComponentExact X c r k
  have h := (freeLieExactBasis X (k + c.weight X)).linearCombination_repr z
  calc
    (contextComponentCoefficients X c r k).sum (fun i a ↦ a •
        (((freeLieExactBasis X (k + c.weight X) i :
          freeLieExact X (k + c.weight X))) : CanonicalFreeLie X)) =
      (freeLieExact X (k + c.weight X)).subtype
        ((contextComponentCoefficients X c r k).sum
          (fun i a ↦ a • freeLieExactBasis X (k + c.weight X) i)) := by
            rw [map_finsuppSum]
            apply Finsupp.sum_congr
            intro i hi
            rw [map_zsmul]
            rfl
    _ = (z : CanonicalFreeLie X) := congrArg Subtype.val h
    _ = _ := rfl

private inductive SquarePacket
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) where
  | marked (relation : CanonicalLieRelationsIdeal X)
      (context : RelationContext X (2 * n))
      (mark : Fin (2 * n + 1))
      (left right : List (TruncatedBasisIndex X (2 * n)))
      (positionFuel : ℕ)
  | word (factors : List (TruncatedBasisIndex X (2 * n)))

private def SquarePacket.value
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    SquarePacket X n → UEA ℤ (TruncatedFreeLie X (2 * n))
  | .marked r c k left right _ =>
      basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n))
            (truncatedHomogeneousBasis X (2 * n)) left *
        UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk X (2 * n)
            (c.applyFree X (markedPrefixFree X k.1 r))) *
        basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n))
            (truncatedHomogeneousBasis X (2 * n)) right
  | .word xs =>
      basisWord ℤ (TruncatedFreeLie X (2 * n))
        (TruncatedBasisIndex X (2 * n))
          (truncatedHomogeneousBasis X (2 * n)) xs

private def SquarePacket.activeWeight
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    SquarePacket X n → ℕ
  | .marked _ c k _ _ _ => k.1 + c.weight X
  | .word _ => 0

private def squareTruncateExpansion
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n))
    (k : Fin (2 * n + 1))
    (left right : List (TruncatedBasisIndex X (2 * n))) :
    List (ℤ × SquarePacket X n) := by
  classical
  if hk : k.1 = 0 then exact []
  else
    let k' : Fin (2 * n + 1) := ⟨k.1 - 1, by omega⟩
    let residual : SquarePacket X n :=
      .marked r c k' left right (left.length + right.length)
    if hweight : k.1 + c.weight X ≤ 2 * n then
      let coeff := contextComponentCoefficients X c r k.1
      exact (1, residual) :: markedSupportPackets coeff fun i ↦
        .word (left ++ contextBasisIndexOf X (by omega) hweight i :: right)
    else exact [(1, residual)]

private def squarePacketExpansion
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    SquarePacket X n → Option (List (ℤ × SquarePacket X n))
  | .marked r c k left right fuel =>
      if hk : k.1 = 0 then some []
      else if hfuel : fuel = 0 then
        some (squareTruncateExpansion X n r c k left right)
      else
        match hleft : left.reverse with
        | x :: revLeft =>
            if hx : k.1 + c.weight X ≤ truncatedBasisWeight X x then
              some
                [(1, .marked r c k revLeft.reverse (x :: right) (fuel - 1)),
                 (1, .marked r (.lieLeft x c) k revLeft.reverse right
                    (revLeft.length + right.length))]
            else
              match right with
              | y :: ys =>
                  if hy : truncatedBasisWeight X y < k.1 + c.weight X then
                    some
                      [(1, .marked r c k (left ++ [y]) ys (fuel - 1)),
                       (1, .marked r (.lieRight c y) k left ys
                          (left.length + ys.length))]
                  else some (squareTruncateExpansion X n r c k left right)
              | [] => some (squareTruncateExpansion X n r c k left right)
        | [] =>
            match right with
            | y :: ys =>
                if hy : truncatedBasisWeight X y < k.1 + c.weight X then
                  some
                    [(1, .marked r c k [y] ys (fuel - 1)),
                     (1, .marked r (.lieRight c y) k [] ys ys.length)]
                else some (squareTruncateExpansion X n r c k left right)
            | [] => some (squareTruncateExpansion X n r c k left right)
  | .word xs =>
      match chooseAdjacentInversion? xs with
      | none => none
      | some d =>
          if hweight : truncatedBasisWeight X d.x +
              truncatedBasisWeight X d.y ≤ 2 * n then
            let coeff := markedBracketCoefficients X d.x d.y hweight
            some ((1, .word (d.left ++ d.y :: d.x :: d.right)) ::
              markedSupportPackets coeff fun i ↦
                .word (d.left ++ i :: d.right))
          else some [(1, .word (d.left ++ d.y :: d.x :: d.right))]

private def squarePacketComplexity
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    SquarePacket X n → ℕ × (ℕ × (ℕ × (ℕ × ℕ)))
  | .marked _ _ k left right fuel =>
      (left.length + right.length + 1, 1, k.1, fuel, 0)
  | .word xs => (xs.length, 0, 0, 0, markedInversionCount X xs)

private def SquarePacketDescent
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    (new old : SquarePacket X n) : Prop :=
  Prod.Lex (· < ·)
    (Prod.Lex (· < ·)
      (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))))
    (squarePacketComplexity X new) (squarePacketComplexity X old)

private theorem squarePacketDescent_wellFounded
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    WellFounded (SquarePacketDescent X (n := n)) :=
  InvImage.wf (squarePacketComplexity X)
    (Nat.lt_wfRel.wf.prod_lex
      (Nat.lt_wfRel.wf.prod_lex
        (Nat.lt_wfRel.wf.prod_lex
          (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))))

private theorem squareTruncateExpansion_decreases
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n))
    (k : Fin (2 * n + 1))
    (left right : List (TruncatedBasisIndex X (2 * n)))
    (fuel : ℕ) (q : ℤ × SquarePacket X n)
    (hq : q ∈ squareTruncateExpansion X n r c k left right) :
    SquarePacketDescent X q.2 (.marked r c k left right fuel) := by
  classical
  unfold squareTruncateExpansion at hq
  split at hq
  · simp at hq
  · rename_i hk
    split at hq
    · rename_i hweight
      rcases List.mem_cons.mp hq with hq | hq
      · subst q
        unfold SquarePacketDescent squarePacketComplexity
        apply Prod.Lex.right (left.length + right.length + 1)
        apply Prod.Lex.right 1
        apply Prod.Lex.left (left.length + right.length, 0) (fuel, 0)
        dsimp only
        omega
      · rcases q with ⟨z, q⟩
        cases q with
        | marked r' c' k' left' right' fuel' =>
            simp [markedSupportPackets] at hq
        | word xs =>
            simp only [markedSupportPackets, List.mem_map] at hq
            obtain ⟨i, hi, hzi, rfl⟩ := hq
            unfold SquarePacketDescent squarePacketComplexity
            simp only [Prod.snd, squarePacketComplexity, List.length_append,
              List.length_cons]
            apply Prod.Lex.right (left.length + right.length + 1)
            exact Prod.Lex.left
              (0, 0, markedInversionCount X
                (left ++ contextBasisIndexOf X (by omega) hweight i :: right))
              (k.1, fuel, 0) (by omega)
    · simp only [List.mem_singleton] at hq
      subst q
      unfold SquarePacketDescent squarePacketComplexity
      apply Prod.Lex.right (left.length + right.length + 1)
      apply Prod.Lex.right 1
      apply Prod.Lex.left (left.length + right.length, 0) (fuel, 0)
      dsimp only
      omega

private theorem squareTruncateExpansion_preserves
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n))
    (k : Fin (2 * n + 1))
    (left right : List (TruncatedBasisIndex X (2 * n))) :
    ((squareTruncateExpansion X n r c k left right).map fun q ↦
        q.1 • SquarePacket.value X n q.2).sum =
      SquarePacket.value X n (.marked r c k left right 0) := by
  classical
  unfold squareTruncateExpansion
  split
  · rename_i hk
    have hkFin : k = ⟨0, by omega⟩ := by
      apply Fin.ext
      exact hk
    rw [hkFin]
    change 0 =
      basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n))
            (truncatedHomogeneousBasis X (2 * n)) left *
        UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk X (2 * n) (c.applyFree X 0)) *
        basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n))
            (truncatedHomogeneousBasis X (2 * n)) right
    rw [show c.applyFree X 0 = 0 from (c.linearMap X).map_zero,
      map_zero, map_zero]
    simp
  · rename_i hk
    let k' : Fin (2 * n + 1) := ⟨k.1 - 1, by omega⟩
    let lword := basisWord ℤ (TruncatedFreeLie X (2 * n))
      (TruncatedBasisIndex X (2 * n))
        (truncatedHomogeneousBasis X (2 * n)) left
    let rword := basisWord ℤ (TruncatedFreeLie X (2 * n))
      (TruncatedBasisIndex X (2 * n))
        (truncatedHomogeneousBasis X (2 * n)) right
    have hkpos : 0 < k.1 := Nat.pos_of_ne_zero hk
    have hprefix : c.applyFree X (markedPrefixFree X k.1 r) =
        c.applyFree X (markedPrefixFree X k'.1 r) +
          (contextComponentExact X c r k.1 : CanonicalFreeLie X) := by
      have h := congrArg (c.linearMap X) (markedPrefixFree_step X hkpos r)
      rw [map_add] at h
      change c.applyFree X (markedPrefixFree X k.1 r) =
        c.applyFree X (markedPrefixFree X (k.1 - 1) r) +
          c.applyFree X
            ((⟨freeLieLengthComponent X k.1 (r : CanonicalFreeLie X),
              freeLieLengthComponent_mem_exact X k.1
                (r : CanonicalFreeLie X)⟩ : freeLieExact X k.1) :
                  CanonicalFreeLie X) at h
      simpa [k', RelationContext.linearMap, contextComponentExact] using h
    split
    · rename_i hweight
      let coeff := contextComponentCoefficients X c r k.1
      have hcomponent :
          coeff.sum (fun i z ↦ z •
            truncatedHomogeneousBasis X (2 * n)
              (contextBasisIndexOf X (by omega) hweight i)) =
            truncatedFreeLieMk X (2 * n)
              (contextComponentExact X c r k.1 : CanonicalFreeLie X) := by
        simp_rw [contextBasisIndexOf_value]
        calc
          coeff.sum (fun i z ↦ z •
              truncatedFreeLieMk X (2 * n)
                (((freeLieExactBasis X (k.1 + c.weight X) i :
                  freeLieExact X (k.1 + c.weight X))) :
                    CanonicalFreeLie X)) =
            truncatedFreeLieMk X (2 * n)
              (coeff.sum (fun i z ↦ z •
                (((freeLieExactBasis X (k.1 + c.weight X) i :
                  freeLieExact X (k.1 + c.weight X))) :
                    CanonicalFreeLie X))) := by
              rw [map_finsuppSum]
              apply Finsupp.sum_congr
              intro i hi
              rw [map_zsmul]
          _ = _ := congrArg (truncatedFreeLieMk X (2 * n))
            (contextComponentCoefficients_sum X c r k.1)
      have hemitted :
          ((markedSupportPackets coeff fun i ↦
              SquarePacket.word
                (left ++ contextBasisIndexOf X (by omega) hweight i :: right)).map
              fun q ↦ q.1 • SquarePacket.value X n q.2).sum =
            lword * UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk X (2 * n)
                (contextComponentExact X c r k.1 : CanonicalFreeLie X)) *
              rword := by
        rw [markedSupportPackets_value]
        change coeff.sum (fun i z ↦ z •
            basisWord ℤ (TruncatedFreeLie X (2 * n))
              (TruncatedBasisIndex X (2 * n))
                (truncatedHomogeneousBasis X (2 * n))
                  (left ++ contextBasisIndexOf X (by omega) hweight i :: right)) = _
        simp_rw [basisWord, List.map_append, List.map_cons, word_append,
          word_cons]
        change coeff.sum (fun i z ↦ z •
            (lword * (UniversalEnvelopingAlgebra.ι ℤ
              (truncatedHomogeneousBasis X (2 * n)
                (contextBasisIndexOf X (by omega) hweight i)) * rword))) = _
        calc
          _ = lword * UniversalEnvelopingAlgebra.ι ℤ
              (coeff.sum (fun i z ↦ z •
                truncatedHomogeneousBasis X (2 * n)
                  (contextBasisIndexOf X (by omega) hweight i))) * rword := by
                rw [map_finsuppSum]
                rw [Finsupp.mul_sum, Finsupp.sum_mul]
                apply Finsupp.sum_congr
                intro i hi
                rw [map_zsmul]
                rw [mul_smul_comm, smul_mul_assoc]
                simp only [mul_assoc]
          _ = _ := by rw [hcomponent]
      simp only [List.map_cons, List.sum_cons, one_smul]
      rw [hemitted]
      change
        lword * UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk X (2 * n)
                (c.applyFree X (markedPrefixFree X k'.1 r))) * rword +
          lword * UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk X (2 * n)
                (contextComponentExact X c r k.1 : CanonicalFreeLie X)) * rword =
        lword * UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk X (2 * n)
                (c.applyFree X (markedPrefixFree X k.1 r))) * rword
      rw [hprefix, map_add, map_add]
      noncomm_ring
    · rename_i hweight
      have hcomponentZero : truncatedFreeLieMk X (2 * n)
          (contextComponentExact X c r k.1 : CanonicalFreeLie X) = 0 := by
        apply (LieSubmodule.Quotient.mk_eq_zero'
          (N := lowerCentralSeries ℤ (CanonicalFreeLie X) (2 * n))).mpr
        have hhigh : (contextComponentExact X c r k.1 : CanonicalFreeLie X) ∈
            FreeLieDimension.lieHigh X (2 * n + 1) := by
          obtain ⟨p, hp, hpvalue⟩ :=
            (contextComponentExact X c r k.1).property
          refine ⟨p, ?_, hpvalue⟩
          intro w hw
          exact le_trans (by omega) (hp hw).ge
        simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries X (2 * n)]
          using hhigh
      simp only [List.map_singleton, List.sum_singleton, one_smul]
      change
        lword * UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk X (2 * n)
                (c.applyFree X (markedPrefixFree X k'.1 r))) * rword =
        lword * UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk X (2 * n)
                (c.applyFree X (markedPrefixFree X k.1 r))) * rword
      rw [hprefix, map_add, map_add, hcomponentZero, map_zero, add_zero]

private theorem squareMarked_fuel_desc
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n)) (k : Fin (2 * n + 1))
    (left right left' right' : List (TruncatedBasisIndex X (2 * n)))
    (fuel fuel' : ℕ)
    (hlen : left'.length + right'.length = left.length + right.length)
    (hfuel : fuel' < fuel) :
    SquarePacketDescent X (.marked r c k left' right' fuel')
      (.marked r c k left right fuel) := by
  unfold SquarePacketDescent squarePacketComplexity
  change Prod.Lex (· < ·)
    (Prod.Lex (· < ·)
      (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))))
    (left'.length + right'.length + 1, 1, k.1, fuel', 0)
    (left.length + right.length + 1, 1, k.1, fuel, 0)
  rw [hlen]
  apply Prod.Lex.right (left.length + right.length + 1)
  apply Prod.Lex.right 1
  apply Prod.Lex.right k.1
  exact Prod.Lex.left 0 0 hfuel

private theorem squareMarked_factor_desc
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    (r : CanonicalLieRelationsIdeal X)
    (c c' : RelationContext X (2 * n)) (k : Fin (2 * n + 1))
    (left right left' right' : List (TruncatedBasisIndex X (2 * n)))
    (fuel fuel' : ℕ)
    (hlen : left'.length + right'.length < left.length + right.length) :
    SquarePacketDescent X (.marked r c' k left' right' fuel')
      (.marked r c k left right fuel) := by
  unfold SquarePacketDescent squarePacketComplexity
  apply Prod.Lex.left (1, k.1, fuel', 0) (1, k.1, fuel, 0)
  omega

private theorem squareWord_inversion_desc
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    (xs ys : List (TruncatedBasisIndex X (2 * n)))
    (hlen : ys.length = xs.length)
    (hinv : markedInversionCount X ys < markedInversionCount X xs) :
    SquarePacketDescent X (.word ys) (.word xs) := by
  unfold SquarePacketDescent squarePacketComplexity
  change Prod.Lex (· < ·)
    (Prod.Lex (· < ·)
      (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))))
    (ys.length, 0, 0, 0, markedInversionCount X ys)
    (xs.length, 0, 0, 0, markedInversionCount X xs)
  rw [hlen]
  apply Prod.Lex.right xs.length
  apply Prod.Lex.right 0
  apply Prod.Lex.right 0
  apply Prod.Lex.right 0
  exact hinv

private theorem squareWord_factor_desc
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    (xs ys : List (TruncatedBasisIndex X (2 * n)))
    (hlen : ys.length < xs.length) :
    SquarePacketDescent X (.word ys) (.word xs) := by
  unfold SquarePacketDescent squarePacketComplexity
  exact Prod.Lex.left (0, 0, 0, markedInversionCount X ys)
    (0, 0, 0, markedInversionCount X xs) hlen

private theorem squarePacketExpansion_decreases
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {p : SquarePacket X n} {qs : List (ℤ × SquarePacket X n)}
    (hp : squarePacketExpansion X n p = some qs) :
    ∀ q ∈ qs, SquarePacketDescent X q.2 p := by
  classical
  intro q hq
  cases p with
  | marked r c k left right fuel =>
      simp only [squarePacketExpansion] at hp
      split at hp
      · rcases Option.some.inj hp with rfl
        simp at hq
      · rename_i hk
        split at hp
        · rename_i hfuel
          rcases Option.some.inj hp with rfl
          exact squareTruncateExpansion_decreases X n r c k left right fuel q hq
        · rename_i hfuel
          split at hp
          · rename_i x revLeft hleft
            have hleftEq : left = revLeft.reverse ++ [x] := by
              have h := congrArg List.reverse hleft
              simpa using h
            split at hp
            · rename_i hx
              rcases Option.some.inj hp with rfl
              rcases List.mem_pair.mp hq with hq | hq
              · subst q
                apply squareMarked_fuel_desc X r c k left right
                  revLeft.reverse (x :: right) fuel (fuel - 1)
                · simp [hleftEq]
                  omega
                · omega
              · subst q
                apply squareMarked_factor_desc X r c (.lieLeft x c) k
                  left right revLeft.reverse right fuel
                  (revLeft.length + right.length)
                simp [hleftEq]
            · rename_i hx
              cases hright : right with
              | nil =>
                  subst right
                  rcases Option.some.inj hp with rfl
                  exact squareTruncateExpansion_decreases X n r c k left [] fuel q hq
              | cons y ys =>
                  subst right
                  dsimp only at hp
                  split at hp
                  · rename_i hy
                    rcases Option.some.inj hp with rfl
                    rcases List.mem_pair.mp hq with hq | hq
                    · subst q
                      apply squareMarked_fuel_desc X r c k left (y :: ys)
                        (left ++ [y]) ys fuel (fuel - 1)
                      · simp only [List.length_append, List.length_singleton,
                          List.length_cons, List.length_nil]
                        omega
                      · omega
                    · subst q
                      apply squareMarked_factor_desc X r c (.lieRight c y) k
                        left (y :: ys) left ys fuel (left.length + ys.length)
                      simp
                  · rename_i hy
                    rcases Option.some.inj hp with rfl
                    exact squareTruncateExpansion_decreases X n r c k left
                      (y :: ys) fuel q hq
          · rename_i hleft
            have hleftEq : left = [] := by
              have h := congrArg List.reverse hleft
              simpa using h
            subst left
            cases hright : right with
            | nil =>
                subst right
                rcases Option.some.inj hp with rfl
                exact squareTruncateExpansion_decreases X n r c k [] [] fuel q hq
            | cons y ys =>
                subst right
                dsimp only at hp
                split at hp
                · rename_i hy
                  rcases Option.some.inj hp with rfl
                  rcases List.mem_pair.mp hq with hq | hq
                  · subst q
                    apply squareMarked_fuel_desc X r c k [] (y :: ys)
                      [y] ys fuel (fuel - 1)
                    · simp only [List.length_singleton, List.length_cons,
                        List.length_nil, zero_add]
                      omega
                    · omega
                  · subst q
                    apply squareMarked_factor_desc X r c (.lieRight c y) k
                      [] (y :: ys) [] ys fuel ys.length
                    simp
                · rename_i hy
                  rcases Option.some.inj hp with rfl
                  exact squareTruncateExpansion_decreases X n r c k []
                    (y :: ys) fuel q hq
  | word xs =>
      simp only [squarePacketExpansion] at hp
      split at hp
      · contradiction
      · rename_i d hchosen
        have hd := chooseAdjacentInversion?_eq_some_realizes hchosen
        rcases hd with ⟨hxs, hxy⟩
        split at hp
        · rename_i hweight
          rcases Option.some.inj hp with rfl
          rcases List.mem_cons.mp hq with hq | hq
          · subst q
            have hinv := markedInversionCount_swap X d.left d.right d.x d.y hxy
            apply squareWord_inversion_desc X xs
              (d.left ++ d.y :: d.x :: d.right)
            · rw [hxs]
              simp
            · rw [hxs]
              omega
          · rcases q with ⟨z, q⟩
            cases q with
            | marked r c k left right fuel => simp [markedSupportPackets] at hq
            | word ys =>
                simp only [markedSupportPackets, List.mem_map] at hq
                obtain ⟨i, hi, hzi, rfl⟩ := hq
                apply squareWord_factor_desc X xs (d.left ++ i :: d.right)
                rw [hxs]
                simp
        · rcases Option.some.inj hp with rfl
          simp only [List.mem_singleton] at hq
          subst q
          have hinv := markedInversionCount_swap X d.left d.right d.x d.y hxy
          apply squareWord_inversion_desc X xs
            (d.left ++ d.y :: d.x :: d.right)
          · rw [hxs]
            simp
          · rw [hxs]
            omega

private theorem squarePacketExpansion_preserves
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {p : SquarePacket X n} {qs : List (ℤ × SquarePacket X n)}
    (hp : squarePacketExpansion X n p = some qs) :
    (qs.map fun q ↦ q.1 • SquarePacket.value X n q.2).sum =
      SquarePacket.value X n p := by
  classical
  cases p with
  | marked r c k left right fuel =>
      simp only [squarePacketExpansion] at hp
      split at hp
      · rename_i hk
        rcases Option.some.inj hp with rfl
        have hkFin : k = ⟨0, by omega⟩ := by
          apply Fin.ext
          exact hk
        rw [hkFin]
        change 0 =
          basisWord ℤ (TruncatedFreeLie X (2 * n))
              (TruncatedBasisIndex X (2 * n))
                (truncatedHomogeneousBasis X (2 * n)) left *
            UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk X (2 * n) (c.applyFree X 0)) *
            basisWord ℤ (TruncatedFreeLie X (2 * n))
              (TruncatedBasisIndex X (2 * n))
                (truncatedHomogeneousBasis X (2 * n)) right
        rw [show c.applyFree X 0 = 0 from (c.linearMap X).map_zero,
          map_zero, map_zero]
        simp
      · rename_i hk
        split at hp
        · rcases Option.some.inj hp with rfl
          simpa only using
            (squareTruncateExpansion_preserves X n r c k left right)
        · rename_i hfuel
          split at hp
          · rename_i x revLeft hleft
            have hleftEq : left = revLeft.reverse ++ [x] := by
              have h := congrArg List.reverse hleft
              simpa using h
            split at hp
            · rename_i hx
              rcases Option.some.inj hp with rfl
              simp only [List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil, one_smul, add_zero]
              let b := truncatedHomogeneousBasis X (2 * n)
              let a := truncatedFreeLieMk X (2 * n)
                (c.applyFree X (markedPrefixFree X k.1 r))
              let xv := b x
              have hxv : xv = truncatedFreeLieMk X (2 * n)
                  (homogeneousBasisLift X x) := by
                simpa only [xv, b, homogeneousBasisLift,
                  truncatedBasisWeight] using
                    (truncatedHomogeneousBasis_apply X (2 * n) x)
              have hcorr : truncatedFreeLieMk X (2 * n)
                    ((RelationContext.lieLeft x c).applyFree X
                      (markedPrefixFree X k.1 r)) = ⁅xv, a⁆ := by
                change truncatedFreeLieMk X (2 * n)
                    ⁅homogeneousBasisLift X x,
                      c.applyFree X (markedPrefixFree X k.1 r)⁆ = _
                rw [LieHom.map_lie, hxv]
              have hswap := iota_mul_iota_swap ℤ
                (TruncatedFreeLie X (2 * n)) xv a
              change
                basisWord ℤ (TruncatedFreeLie X (2 * n))
                      (TruncatedBasisIndex X (2 * n)) b revLeft.reverse *
                    UniversalEnvelopingAlgebra.ι ℤ a *
                    basisWord ℤ (TruncatedFreeLie X (2 * n))
                      (TruncatedBasisIndex X (2 * n)) b (x :: right) +
                  basisWord ℤ (TruncatedFreeLie X (2 * n))
                      (TruncatedBasisIndex X (2 * n)) b revLeft.reverse *
                    UniversalEnvelopingAlgebra.ι ℤ
                      (truncatedFreeLieMk X (2 * n)
                        ((RelationContext.lieLeft x c).applyFree X
                          (markedPrefixFree X k.1 r))) *
                    basisWord ℤ (TruncatedFreeLie X (2 * n))
                      (TruncatedBasisIndex X (2 * n)) b right =
                  basisWord ℤ (TruncatedFreeLie X (2 * n))
                      (TruncatedBasisIndex X (2 * n)) b left *
                    UniversalEnvelopingAlgebra.ι ℤ a *
                    basisWord ℤ (TruncatedFreeLie X (2 * n))
                      (TruncatedBasisIndex X (2 * n)) b right
              rw [hleftEq]
              simp only [basisWord, List.map_append, List.map_singleton,
                List.map_cons, List.map_nil, word_append, word_cons,
                word_nil, mul_one]
              rw [hcorr]
              let lw := word ℤ (TruncatedFreeLie X (2 * n))
                (revLeft.reverse.map b)
              let rw' := word ℤ (TruncatedFreeLie X (2 * n))
                (right.map b)
              change lw * UniversalEnvelopingAlgebra.ι ℤ a *
                    (UniversalEnvelopingAlgebra.ι ℤ xv * rw') +
                  lw * UniversalEnvelopingAlgebra.ι ℤ ⁅xv, a⁆ * rw' =
                lw * UniversalEnvelopingAlgebra.ι ℤ xv *
                  UniversalEnvelopingAlgebra.ι ℤ a * rw'
              calc
                _ = lw * (UniversalEnvelopingAlgebra.ι ℤ a *
                      UniversalEnvelopingAlgebra.ι ℤ xv +
                    UniversalEnvelopingAlgebra.ι ℤ ⁅xv, a⁆) * rw' := by
                      noncomm_ring
                _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
                      UniversalEnvelopingAlgebra.ι ℤ a) * rw' := by
                      rw [← hswap]
                _ = _ := by noncomm_ring
            · rename_i hx
              cases hright : right with
              | nil =>
                  subst right
                  rcases Option.some.inj hp with rfl
                  simpa only using
                    (squareTruncateExpansion_preserves X n r c k left [])
              | cons y ys =>
                  subst right
                  dsimp only at hp
                  split at hp
                  · rename_i hy
                    rcases Option.some.inj hp with rfl
                    simp only [List.map_cons, List.map_nil, List.sum_cons,
                      List.sum_nil, one_smul, add_zero]
                    let b := truncatedHomogeneousBasis X (2 * n)
                    let a := truncatedFreeLieMk X (2 * n)
                      (c.applyFree X (markedPrefixFree X k.1 r))
                    let yv := b y
                    have hyv : yv = truncatedFreeLieMk X (2 * n)
                        (homogeneousBasisLift X y) := by
                      simpa only [yv, b, homogeneousBasisLift,
                        truncatedBasisWeight] using
                          (truncatedHomogeneousBasis_apply X (2 * n) y)
                    have hcorr : truncatedFreeLieMk X (2 * n)
                          ((RelationContext.lieRight c y).applyFree X
                            (markedPrefixFree X k.1 r)) = ⁅a, yv⁆ := by
                      change truncatedFreeLieMk X (2 * n)
                          ⁅c.applyFree X (markedPrefixFree X k.1 r),
                            homogeneousBasisLift X y⁆ = _
                      rw [LieHom.map_lie, hyv]
                    have hswap := iota_mul_iota_swap ℤ
                      (TruncatedFreeLie X (2 * n)) a yv
                    change
                      basisWord ℤ (TruncatedFreeLie X (2 * n))
                            (TruncatedBasisIndex X (2 * n)) b (left ++ [y]) *
                          UniversalEnvelopingAlgebra.ι ℤ a *
                          basisWord ℤ (TruncatedFreeLie X (2 * n))
                            (TruncatedBasisIndex X (2 * n)) b ys +
                        basisWord ℤ (TruncatedFreeLie X (2 * n))
                            (TruncatedBasisIndex X (2 * n)) b left *
                          UniversalEnvelopingAlgebra.ι ℤ
                            (truncatedFreeLieMk X (2 * n)
                              ((RelationContext.lieRight c y).applyFree X
                                (markedPrefixFree X k.1 r))) *
                          basisWord ℤ (TruncatedFreeLie X (2 * n))
                            (TruncatedBasisIndex X (2 * n)) b ys =
                        basisWord ℤ (TruncatedFreeLie X (2 * n))
                            (TruncatedBasisIndex X (2 * n)) b left *
                          UniversalEnvelopingAlgebra.ι ℤ a *
                          basisWord ℤ (TruncatedFreeLie X (2 * n))
                            (TruncatedBasisIndex X (2 * n)) b (y :: ys)
                    simp only [basisWord, List.map_append, List.map_singleton,
                      List.map_cons, List.map_nil, word_append, word_cons,
                      word_nil, mul_one]
                    rw [hcorr]
                    let lw := word ℤ (TruncatedFreeLie X (2 * n))
                      (left.map b)
                    let rw' := word ℤ (TruncatedFreeLie X (2 * n))
                      (ys.map b)
                    change lw * UniversalEnvelopingAlgebra.ι ℤ yv *
                          UniversalEnvelopingAlgebra.ι ℤ a * rw' +
                        lw * UniversalEnvelopingAlgebra.ι ℤ ⁅a, yv⁆ * rw' =
                      lw * UniversalEnvelopingAlgebra.ι ℤ a *
                        (UniversalEnvelopingAlgebra.ι ℤ yv * rw')
                    calc
                      _ = lw * (UniversalEnvelopingAlgebra.ι ℤ yv *
                            UniversalEnvelopingAlgebra.ι ℤ a +
                          UniversalEnvelopingAlgebra.ι ℤ ⁅a, yv⁆) * rw' := by
                            noncomm_ring
                      _ = lw * (UniversalEnvelopingAlgebra.ι ℤ a *
                            UniversalEnvelopingAlgebra.ι ℤ yv) * rw' := by
                            rw [← hswap]
                      _ = _ := by noncomm_ring
                  · rcases Option.some.inj hp with rfl
                    simpa only using
                      (squareTruncateExpansion_preserves X n r c k left (y :: ys))
          · rename_i hleft
            have hleftEq : left = [] := by
              have h := congrArg List.reverse hleft
              simpa using h
            subst left
            cases hright : right with
            | nil =>
                subst right
                rcases Option.some.inj hp with rfl
                simpa only using
                  (squareTruncateExpansion_preserves X n r c k [] [])
            | cons y ys =>
                subst right
                dsimp only at hp
                split at hp
                · rename_i hy
                  rcases Option.some.inj hp with rfl
                  simp only [List.map_cons, List.map_nil, List.sum_cons,
                    List.sum_nil, one_smul, add_zero]
                  let b := truncatedHomogeneousBasis X (2 * n)
                  let a := truncatedFreeLieMk X (2 * n)
                    (c.applyFree X (markedPrefixFree X k.1 r))
                  let yv := b y
                  have hyv : yv = truncatedFreeLieMk X (2 * n)
                      (homogeneousBasisLift X y) := by
                    simpa only [yv, b, homogeneousBasisLift,
                      truncatedBasisWeight] using
                        (truncatedHomogeneousBasis_apply X (2 * n) y)
                  have hcorr : truncatedFreeLieMk X (2 * n)
                        ((RelationContext.lieRight c y).applyFree X
                          (markedPrefixFree X k.1 r)) = ⁅a, yv⁆ := by
                    change truncatedFreeLieMk X (2 * n)
                        ⁅c.applyFree X (markedPrefixFree X k.1 r),
                          homogeneousBasisLift X y⁆ = _
                    rw [LieHom.map_lie, hyv]
                  have hswap := iota_mul_iota_swap ℤ
                    (TruncatedFreeLie X (2 * n)) a yv
                  simp only [SquarePacket.value, basisWord, List.map_cons,
                    List.map_nil, word_cons, word_nil, one_mul, mul_one]
                  rw [hcorr]
                  let rw' := word ℤ (TruncatedFreeLie X (2 * n))
                    (ys.map b)
                  change UniversalEnvelopingAlgebra.ι ℤ yv *
                        UniversalEnvelopingAlgebra.ι ℤ a * rw' +
                      UniversalEnvelopingAlgebra.ι ℤ ⁅a, yv⁆ * rw' =
                    UniversalEnvelopingAlgebra.ι ℤ a *
                      (UniversalEnvelopingAlgebra.ι ℤ yv * rw')
                  calc
                    _ = (UniversalEnvelopingAlgebra.ι ℤ yv *
                          UniversalEnvelopingAlgebra.ι ℤ a +
                        UniversalEnvelopingAlgebra.ι ℤ ⁅a, yv⁆) * rw' := by
                          noncomm_ring
                    _ = (UniversalEnvelopingAlgebra.ι ℤ a *
                          UniversalEnvelopingAlgebra.ι ℤ yv) * rw' := by
                          rw [← hswap]
                    _ = _ := by noncomm_ring
                · rcases Option.some.inj hp with rfl
                  simpa only using
                    (squareTruncateExpansion_preserves X n r c k [] (y :: ys))
  | word xs =>
      simp only [squarePacketExpansion] at hp
      split at hp
      · contradiction
      · rename_i d hchosen
        have hd := chooseAdjacentInversion?_eq_some_realizes hchosen
        rcases hd with ⟨hxs, hxy⟩
        split at hp
        · rename_i hweight
          rcases Option.some.inj hp with rfl
          let coeff := markedBracketCoefficients X d.x d.y hweight
          have hcoeff := markedBracketCoefficients_sum X d.x d.y hweight
          let context : TruncatedFreeLie X (2 * n) →+
              UEA ℤ (TruncatedFreeLie X (2 * n)) :=
            { toFun := fun z ↦
                word ℤ (TruncatedFreeLie X (2 * n))
                    (d.left.map (truncatedHomogeneousBasis X (2 * n))) *
                  UniversalEnvelopingAlgebra.ι ℤ z *
                  word ℤ (TruncatedFreeLie X (2 * n))
                    (d.right.map (truncatedHomogeneousBasis X (2 * n)))
              map_zero' := by simp
              map_add' := by intro a b; simp [map_add, mul_add, add_mul] }
          have hcontext := congrArg context hcoeff
          rw [map_finsuppSum] at hcontext
          have hcorrection :
              ((markedSupportPackets coeff fun i ↦
                  SquarePacket.word (d.left ++ i :: d.right)).map fun q ↦
                    q.1 • SquarePacket.value X n q.2).sum =
                context ⁅truncatedHomogeneousBasis X (2 * n) d.x,
                  truncatedHomogeneousBasis X (2 * n) d.y⁆ := by
            rw [markedSupportPackets_value, ← hcontext]
            apply Finsupp.sum_congr
            intro i hi
            rw [map_zsmul]
            simp [SquarePacket.value, context, basisWord, word,
              List.map_append]
            noncomm_ring
          have hswapWord := envelopingWord_adjacent_swap ℤ
            (TruncatedFreeLie X (2 * n))
            (d.left.map (truncatedHomogeneousBasis X (2 * n)))
            (d.right.map (truncatedHomogeneousBasis X (2 * n)))
            (truncatedHomogeneousBasis X (2 * n) d.x)
            (truncatedHomogeneousBasis X (2 * n) d.y)
          simp only [List.map_cons, List.sum_cons, one_smul]
          rw [hcorrection, hxs]
          simpa only [SquarePacket.value, context, basisWord, word,
            envelopingWord, List.map_append, List.map_cons, List.map_nil,
            List.map_map, Function.comp_apply] using hswapWord.symm
        · rename_i hweight
          rcases Option.some.inj hp with rfl
          have hbracket :
              ⁅truncatedHomogeneousBasis X (2 * n) d.x,
                truncatedHomogeneousBasis X (2 * n) d.y⁆ = 0 := by
            rw [truncatedHomogeneousBasis_apply,
              truncatedHomogeneousBasis_apply, ← LieHom.map_lie]
            apply (LieSubmodule.Quotient.mk_eq_zero'
              (N := lowerCentralSeries ℤ (CanonicalFreeLie X) (2 * n))).mpr
            let bracketExact : freeLieExact X
                (truncatedBasisWeight X d.x + truncatedBasisWeight X d.y) :=
              ⟨⁅((freeLieExactBasis X (d.x.1.1 + 1) d.x.2 :
                    freeLieExact X (d.x.1.1 + 1)) : CanonicalFreeLie X),
                  ((freeLieExactBasis X (d.y.1.1 + 1) d.y.2 :
                    freeLieExact X (d.y.1.1 + 1)) : CanonicalFreeLie X)⁆,
                freeLieExact_bracket_mem X
                  (freeLieExactBasis X (d.x.1.1 + 1) d.x.2)
                  (freeLieExactBasis X (d.y.1.1 + 1) d.y.2)⟩
            have hb := freeLieExact_mem_lieHigh X bracketExact
            have hb' : (bracketExact : CanonicalFreeLie X) ∈
                lowerCentralSeries ℤ (CanonicalFreeLie X)
                  (truncatedBasisWeight X d.x +
                    truncatedBasisWeight X d.y - 1) := by
              change (bracketExact : CanonicalFreeLie X) ∈
                (lowerCentralSeries ℤ (CanonicalFreeLie X)
                  (truncatedBasisWeight X d.x +
                    truncatedBasisWeight X d.y - 1)).toLieSubalgebra.toSubmodule
              rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries]
              convert hb using 1 <;> omega
            exact LieModule.antitone_lowerCentralSeries ℤ
              (CanonicalFreeLie X) (CanonicalFreeLie X) (by omega) hb'
          have hswapWord := envelopingWord_adjacent_swap ℤ
            (TruncatedFreeLie X (2 * n))
            (d.left.map (truncatedHomogeneousBasis X (2 * n)))
            (d.right.map (truncatedHomogeneousBasis X (2 * n)))
            (truncatedHomogeneousBasis X (2 * n) d.x)
            (truncatedHomogeneousBasis X (2 * n) d.y)
          simp only [List.map_singleton, List.sum_singleton, one_smul]
          rw [hxs]
          rw [hbracket] at hswapWord
          simpa only [SquarePacket.value, basisWord, word, envelopingWord,
            List.map_append, List.map_cons, List.map_nil, List.map_map,
            Function.comp_apply, map_zero, mul_zero, zero_mul, add_zero]
            using hswapWord.symm

private def squarePacketCollector
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    FiniteTaggedCollector (SquarePacket X n)
      (UEA ℤ (TruncatedFreeLie X (2 * n))) where
  relation := SquarePacketDescent X
  wellFounded := squarePacketDescent_wellFounded X n
  expansion := squarePacketExpansion X n
  value := SquarePacket.value X n
  decreases := squarePacketExpansion_decreases X n
  preserves := squarePacketExpansion_preserves X n

/-! ## Full-relation subset collection

The following is the concrete instance read by the marked ledger.  It is the manuscript's
identity `ρ x = x ρ + [ρ,x]`, iterated in one fixed order.  In particular, its correction is
again a full member of the canonical relation ideal; no homogeneous tail is ever used as a
relation. -/

private structure FullRelationRow
    (L : Type u) [LieRing L] [Finite L] (N : ℕ) where
  left : List (TruncatedBasisIndex L N)
  relation : CanonicalLieRelationsIdeal L
  right : List (TruncatedBasisIndex L N)

private def relationBracketRight
    (L : Type u) [LieRing L] [Finite L] {N : ℕ}
    (r : CanonicalLieRelationsIdeal L)
    (i : TruncatedBasisIndex L N) : CanonicalLieRelationsIdeal L :=
  ⟨⁅(r : CanonicalFreeLie L), homogeneousBasisLift L i⁆, by
    change canonicalFreeLieEvaluation L
      ⁅(r : CanonicalFreeLie L), homogeneousBasisLift L i⁆ = 0
    rw [LieHom.map_lie, show canonicalFreeLieEvaluation L
      (r : CanonicalFreeLie L) = 0 from r.property]
    simp⟩

private def FullRelationRow.value
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (p : FullRelationRow L N) : UEA ℤ (TruncatedFreeLie L N) :=
  basisWord ℤ (TruncatedFreeLie L N) (TruncatedBasisIndex L N)
      (truncatedHomogeneousBasis L N) p.left *
    UniversalEnvelopingAlgebra.ι ℤ
      (truncatedFreeLieMk L N (p.relation : CanonicalFreeLie L)) *
    basisWord ℤ (TruncatedFreeLie L N) (TruncatedBasisIndex L N)
      (truncatedHomogeneousBasis L N) p.right

private def fullRelationRowExpansion
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (p : FullRelationRow L N) :
    Option (List (ℤ × FullRelationRow L N)) :=
  match p.right with
  | [] => none
  | i :: is => some
      [(1, { left := p.left ++ [i], relation := p.relation, right := is }),
       (1, { left := p.left,
             relation := relationBracketRight L p.relation i,
             right := is })]

private def fullRelationRowCollector
    (L : Type u) [LieRing L] [Finite L] (N : ℕ) :
    FiniteTaggedCollector (FullRelationRow L N)
      (UEA ℤ (TruncatedFreeLie L N)) where
  relation q p := q.right.length < p.right.length
  wellFounded := (measure fun p : FullRelationRow L N ↦ p.right.length).wf
  expansion := fullRelationRowExpansion L N
  value := FullRelationRow.value L N
  decreases := by
    intro p qs h q hq
    unfold fullRelationRowExpansion at h
    split at h
    · contradiction
    · rename_i i is hright
      simp only [Option.some.injEq] at h
      subst qs
      have hq' := List.mem_pair.mp hq
      rcases hq' with hq' | hq' <;> subst q <;> simp [hright]
  preserves := by
    intro p qs h
    unfold fullRelationRowExpansion at h
    split at h
    · contradiction
    · rename_i i is hright
      simp only [Option.some.injEq] at h
      subst qs
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        one_smul, add_zero]
      unfold FullRelationRow.value
      simp only
      let b := truncatedHomogeneousBasis L N
      let r := truncatedFreeLieMk L N (p.relation : CanonicalFreeLie L)
      let x := truncatedHomogeneousBasis L N i
      let rxi := truncatedFreeLieMk L N
        (relationBracketRight L p.relation i : CanonicalFreeLie L)
      have hx : x = truncatedFreeLieMk L N (homogeneousBasisLift L i) := by
        simpa only [x, homogeneousBasisLift, truncatedBasisWeight] using
          (truncatedHomogeneousBasis_apply L N i)
      have hrxi : rxi = ⁅r, x⁆ := by
        dsimp only [rxi, relationBracketRight, r]
        rw [LieHom.map_lie, hx]
      have hswap := iota_mul_iota_swap ℤ (TruncatedFreeLie L N) r x
      rw [hright, basisWord_cons]
      change
        basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b (p.left ++ [i]) *
            UniversalEnvelopingAlgebra.ι ℤ r *
            basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b is +
          basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b p.left *
            UniversalEnvelopingAlgebra.ι ℤ rxi *
            basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b is =
        basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b p.left *
            UniversalEnvelopingAlgebra.ι ℤ r *
            (UniversalEnvelopingAlgebra.ι ℤ x *
              basisWord ℤ (TruncatedFreeLie L N)
                (TruncatedBasisIndex L N) b is)
      rw [show basisWord ℤ (TruncatedFreeLie L N)
          (TruncatedBasisIndex L N) b (p.left ++ [i]) =
          basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b p.left *
            UniversalEnvelopingAlgebra.ι ℤ x by
        simp only [basisWord, List.map_append, List.map_singleton,
          word_append, word_cons, word_nil, mul_one, x]
        rfl]
      rw [hrxi]
      calc
        (basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b p.left *
            UniversalEnvelopingAlgebra.ι ℤ x) *
            UniversalEnvelopingAlgebra.ι ℤ r *
            basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b is +
          basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b p.left *
            UniversalEnvelopingAlgebra.ι ℤ ⁅r, x⁆ *
            basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b is =
          basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b p.left *
            (UniversalEnvelopingAlgebra.ι ℤ x *
                UniversalEnvelopingAlgebra.ι ℤ r +
              UniversalEnvelopingAlgebra.ι ℤ ⁅r, x⁆) *
            basisWord ℤ (TruncatedFreeLie L N)
              (TruncatedBasisIndex L N) b is := by noncomm_ring
        _ = _ := by rw [← hswap]; noncomm_ring

private def rowsOfMultiplier
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (r : CanonicalLieRelationsIdeal L)
    (z : UEA ℤ (TruncatedFreeLie L N)) :
    FullRelationRow L N →₀ ℤ :=
  ((truncatedPBWLinearEquiv L N).symm z).sum fun e c ↦
    Finsupp.single
      { left := [], relation := r, right := exponentWord L e } c

private theorem basisWord_exponentWord
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (e : TruncatedBasisIndex L N →₀ ℕ) :
    basisWord ℤ (TruncatedFreeLie L N) (TruncatedBasisIndex L N)
        (truncatedHomogeneousBasis L N) (exponentWord L e) =
      orderedMonomial ℤ (TruncatedFreeLie L N)
        (TruncatedBasisIndex L N) (truncatedHomogeneousBasis L N) e := by
  classical
  unfold basisWord word exponentWord orderedMonomial
  rw [List.map_map]
  rfl

private theorem evaluate_rowsOfMultiplier
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (r : CanonicalLieRelationsIdeal L)
    (z : UEA ℤ (TruncatedFreeLie L N)) :
    (fullRelationRowCollector L N).evaluate
        (rowsOfMultiplier L N r z) =
      UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk L N (r : CanonicalFreeLie L)) * z := by
  classical
  unfold rowsOfMultiplier
  rw [map_finsuppSum]
  let p := (truncatedPBWLinearEquiv L N).symm z
  calc
    p.sum (fun e c ↦
        (fullRelationRowCollector L N).evaluate
          (Finsupp.single
            ({ left := [], relation := r, right := exponentWord L e } :
              FullRelationRow L N) c)) =
      p.sum (fun e c ↦ c •
        (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedFreeLieMk L N (r : CanonicalFreeLie L)) *
          orderedMonomial ℤ (TruncatedFreeLie L N)
            (TruncatedBasisIndex L N)
              (truncatedHomogeneousBasis L N) e)) := by
        apply Finsupp.sum_congr
        intro e he
        rw [FiniteTaggedCollector.evaluate_single]
        simp only [fullRelationRowCollector, FullRelationRow.value,
          basisWord_nil, one_mul]
        rw [basisWord_exponentWord]
    _ = UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk L N (r : CanonicalFreeLie L)) *
        (truncatedPBWLinearEquiv L N) p := by
          let ir := UniversalEnvelopingAlgebra.ι ℤ
            (truncatedFreeLieMk L N (r : CanonicalFreeLie L))
          calc
            p.sum (fun e c ↦ c •
                (ir * orderedMonomial ℤ (TruncatedFreeLie L N)
                  (TruncatedBasisIndex L N)
                    (truncatedHomogeneousBasis L N) e)) =
              ir * p.sum (fun e c ↦ c •
                orderedMonomial ℤ (TruncatedFreeLie L N)
                  (TruncatedBasisIndex L N)
                    (truncatedHomogeneousBasis L N) e) := by
                rw [Finsupp.mul_sum]
                apply Finsupp.sum_congr
                intro e he
                exact (mul_smul_comm (p e) ir
                  (orderedMonomial ℤ (TruncatedFreeLie L N)
                    (TruncatedBasisIndex L N)
                      (truncatedHomogeneousBasis L N) e)).symm
            _ = ir * (truncatedPBWLinearEquiv L N) p := by rfl
    _ = _ := by rw [LinearEquiv.apply_symm_apply]

private def GoverningWitness.initialRows
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    FullRelationRow L (2 * n) →₀ ℤ :=
  w.relationWords.sum fun p c ↦ c •
    rowsOfMultiplier L (2 * n) p.1
      (word ℤ (TruncatedFreeLie L (2 * n))
        (p.2.map fun x ↦
          truncatedFreeLieMk L (2 * n) (FreeLieAlgebra.of ℤ x)))

private theorem GoverningWitness.evaluate_initialRows
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (fullRelationRowCollector L (2 * n)).evaluate w.initialRows =
      w.relationSide := by
  classical
  unfold GoverningWitness.initialRows GoverningWitness.relationSide
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, evaluate_rowsOfMultiplier]

private def collectRowLedger
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (c : FullRelationRow L N →₀ ℤ) :
    FullRelationRow L N →₀ ℤ :=
  c.sum fun p z ↦ z • (fullRelationRowCollector L N).normalForm p

private theorem evaluate_collectRowLedger
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (c : FullRelationRow L N →₀ ℤ) :
    (fullRelationRowCollector L N).evaluate
        (collectRowLedger L N c) =
      (fullRelationRowCollector L N).evaluate c := by
  classical
  unfold collectRowLedger
  rw [map_finsuppSum]
  change c.sum (fun p z ↦
      (fullRelationRowCollector L N).evaluate
        (z • (fullRelationRowCollector L N).normalForm p)) =
    c.sum (fun p z ↦ z • (fullRelationRowCollector L N).value p)
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, FiniteTaggedCollector.evaluate_normalForm]

private theorem GoverningWitness.evaluate_collectedRows
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (fullRelationRowCollector L (2 * n)).evaluate
        (collectRowLedger L (2 * n) w.initialRows) =
      w.relationSide := by
  rw [evaluate_collectRowLedger, w.evaluate_initialRows]

private theorem ReducedData.lie_eq_zero_of_mem_derived
    {n : ℕ} {L : Type u} [LieRing L]
    (R : ReducedData n L) {x y : L}
    (hx : x ∈ lowerCentralSeries ℤ L 1)
    (hy : y ∈ lowerCentralSeries ℤ L 1) : ⁅x, y⁆ = 0 := by
  have hx' : x ∈ LieAlgebra.derivedSeries ℤ L 1 := by
    simpa [LieAlgebra.derivedSeries_def,
      LieAlgebra.derivedSeriesOfIdeal_succ,
      lowerCentralSeries, LieModule.lowerCentralSeries_succ,
      LieSubmodule.lie_comm] using hx
  have hy' : y ∈ LieAlgebra.derivedSeries ℤ L 1 := by
    simpa [LieAlgebra.derivedSeries_def,
      LieAlgebra.derivedSeriesOfIdeal_succ,
      lowerCentralSeries, LieModule.lowerCentralSeries_succ,
      LieSubmodule.lie_comm] using hy
  have hxy : ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ L 2 := by
    rw [show (2 : ℕ) = 1 + 1 by omega,
      LieAlgebra.derivedSeries_def,
      LieAlgebra.derivedSeriesOfIdeal_succ]
    exact LieSubmodule.lie_mem_lie hx' hy'
  rw [R.metabelian] at hxy
  exact hxy

/-- In a metabelian target, the ordinary teeth of a commutator with derived head may be
permuted integrally.  The adjacent transposition error is a bracket of two derived elements. -/
private theorem leftNormedBracket_eq_of_perm_of_mem_derived
    {n : ℕ} {L : Type u} [LieRing L]
    (R : ReducedData n L) {x : L}
    (hx : x ∈ lowerCentralSeries ℤ L 1)
    {xs ys : List L} (hperm : xs.Perm ys) :
    leftNormedBracket x xs = leftNormedBracket x ys := by
  have derived_lie (z a : L)
      (hz : z ∈ lowerCentralSeries ℤ L 1) :
      ⁅z, a⁆ ∈ lowerCentralSeries ℤ L 1 := by
    have hza : ⁅z, a⁆ ∈ lowerCentralSeries ℤ L (1 + 1) := by
      change ⁅z, a⁆ ∈ LieModule.lowerCentralSeries ℤ L L (1 + 1)
      rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
      exact LieSubmodule.lie_mem_lie hz (LieSubmodule.mem_top a)
    exact LieModule.antitone_lowerCentralSeries ℤ L L (by omega) hza
  have bracket_derived (a b : L) :
      ⁅a, b⁆ ∈ lowerCentralSeries ℤ L 1 := by
    change ⁅a, b⁆ ∈ LieModule.lowerCentralSeries ℤ L L (0 + 1)
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
    exact LieSubmodule.lie_mem_lie
      (LieSubmodule.mem_top a) (LieSubmodule.mem_top b)
  have adjacent (z a b : L)
      (hz : z ∈ lowerCentralSeries ℤ L 1) :
      ⁅⁅z, a⁆, b⁆ = ⁅⁅z, b⁆, a⁆ := by
    have hzero : ⁅z, ⁅a, b⁆⁆ = 0 :=
      R.lie_eq_zero_of_mem_derived hz (bracket_derived a b)
    have hfirst : ⁅a, ⁅b, z⁆⁆ = ⁅⁅z, b⁆, a⁆ := by
      rw [(lie_skew b z).symm, lie_neg, lie_skew]
    have hsecond : ⁅b, ⁅z, a⁆⁆ = -⁅⁅z, a⁆, b⁆ :=
      (lie_skew b (⁅z, a⁆)).symm
    have hj := lie_jacobi z a b
    rw [hzero, zero_add, hfirst, hsecond] at hj
    have hba := eq_neg_of_add_eq_zero_left hj
    have hba' : ⁅⁅z, b⁆, a⁆ = ⁅⁅z, a⁆, b⁆ := by
      simpa only [neg_neg] using hba
    exact hba'.symm
  induction hperm generalizing x with
  | nil => rfl
  | cons a hperm ih =>
      change leftNormedBracket ⁅x, a⁆ _ = leftNormedBracket ⁅x, a⁆ _
      exact ih (derived_lie x a hx)
  | swap a b l =>
      change leftNormedBracket ⁅⁅x, b⁆, a⁆ l =
        leftNormedBracket ⁅⁅x, a⁆, b⁆ l
      exact congrArg (fun z ↦ leftNormedBracket z l) (adjacent x a b hx).symm
  | trans hxy hyz ihxy ihyz =>
      exact (ihxy hx).trans (ihyz hx)

private theorem ReducedData.lie_eq_zero_of_mem_top
    {n : ℕ} {L : Type u} [LieRing L]
    (R : ReducedData n L) {x y : L}
    (hx : x ∈ lowerCentralSeries ℤ L n) : ⁅x, y⁆ = 0 := by
  have hxy : ⁅x, y⁆ ∈ lowerCentralSeries ℤ L (n + 1) := by
    change ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℤ L L (n + 1)
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
    exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top y)
  rw [R.classBound] at hxy
  exact hxy

/-! ## The terminal finite Smith bridge -/

private def lowFreeParts (X : Type u) [Finite X] (N : ℕ)
    (f : FreeLieAlgebra ℤ X) : LowTuple X N := fun s ↦
  ⟨freeLieLengthComponent X (s.1 + 1) f,
    freeLieLengthComponent_mem_exact X (s.1 + 1) f⟩

private def lowFreeSum (X : Type u) [Finite X] (N : ℕ) :
    LowTuple X N →ₗ[ℤ] FreeLieAlgebra ℤ X where
  toFun z := ∑ s, ((z s : freeLieExact X (s.1 + 1)) : FreeLieAlgebra ℤ X)
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' z x := by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower]
    exact Finset.smul_sum.symm

private theorem sub_lowFreeSum_mem_lieHigh
    (X : Type u) [Finite X] (N : ℕ)
    (f : FreeLieAlgebra ℤ X) :
    f - lowFreeSum X N (lowFreeParts X N f) ∈
      FreeLieDimension.lieHigh X (N + 1) := by
  let rem : FreeLieAlgebra ℤ X :=
    f - lowFreeSum X N (lowFreeParts X N f)
  have hcomponent (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
      freeLieLengthComponent X k rem = 0 := by
    let s : Fin N := ⟨k - 1, by omega⟩
    have hs : s.1 + 1 = k := by
      dsimp only [s]
      omega
    change freeLieLengthComponent X k
      (f - ∑ t : Fin N,
        (((lowFreeParts X N f) t : freeLieExact X (t.1 + 1)) :
          FreeLieAlgebra ℤ X)) = 0
    rw [map_sub, map_sum, Finset.sum_eq_single s]
    · rw [← hs, freeLieLengthComponent_coe_exact]
      change freeLieLengthComponent X (s.1 + 1) f -
        freeLieLengthComponent X (s.1 + 1) f = 0
      abel
    · intro t ht hts
      rw [freeLieLengthComponent_coe_exact_of_ne X]
      intro hweight
      apply hts
      apply Fin.ext
      omega
    · simp
  have hhigh : ∀ k, k ≤ N + 1 → 1 ≤ k →
      rem ∈ FreeLieDimension.lieHigh X k := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
        intro hkN hkpos
        by_cases hk0 : k = 0
        · subst k
          rw [FreeLieDimension.lieHigh_one]
          trivial
        · have hkpos' : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
          exact mem_lieHigh_succ_of_component_eq_zero X
            (ih (by omega) hkpos') (hcomponent k hkpos' (by omega))
  exact hhigh (N + 1) le_rfl (by omega)

private theorem truncated_markedPrefixFree_top
    (X : Type u) [LieRing X] [Finite X] (N : ℕ)
    (r : CanonicalLieRelationsIdeal X) :
    truncatedFreeLieMk X N (markedPrefixFree X N r) =
      truncatedFreeLieMk X N (r : CanonicalFreeLie X) := by
  have hsum : markedPrefixFree X N r =
      lowFreeSum X N (lowFreeParts X N (r : CanonicalFreeLie X)) := rfl
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ (CanonicalFreeLie X) N)).mpr
  rw [hsum]
  have hhigh := sub_lowFreeSum_mem_lieHigh X N
    (r : CanonicalFreeLie X)
  have hhighLcs : (r : CanonicalFreeLie X) -
      lowFreeSum X N (lowFreeParts X N (r : CanonicalFreeLie X)) ∈
        lowerCentralSeries ℤ (CanonicalFreeLie X) N := by
    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries X N] using hhigh
  simpa only [neg_sub] using
    (lowerCentralSeries ℤ (CanonicalFreeLie X) N).neg_mem hhighLcs

private theorem collectRowLedger_apply_eq_zero_of_right_ne_nil
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (c : FullRelationRow L N →₀ ℤ) (row : FullRelationRow L N)
    (hright : row.right ≠ []) : collectRowLedger L N c row = 0 := by
  classical
  unfold collectRowLedger
  rw [Finsupp.sum_apply]
  calc
    c.sum (fun p z ↦ (z • (fullRelationRowCollector L N).normalForm p) row) =
        c.sum (fun _ _ ↦ 0) := by
          apply Finsupp.sum_congr
          intro p hp
          rw [Finsupp.smul_apply,
            FiniteTaggedCollector.normalForm_apply_eq_zero_of_nonterminal]
          · simp
          · change fullRelationRowExpansion L N row ≠ none
            unfold fullRelationRowExpansion
            cases hrightCase : row.right with
            | nil => exact (hright hrightCase).elim
            | cons i is => simp
    _ = 0 := Finsupp.sum_zero

private def collectedRowsToMarked
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (c : FullRelationRow L (2 * n) →₀ ℤ) :
    MarkedPBWPacket L n →₀ ℤ :=
  c.sum fun row z ↦
    Finsupp.single (.marked row.relation ⟨2 * n, by omega⟩ row.left) z

private theorem evaluate_collectedRowsToMarked
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (c : FullRelationRow L (2 * n) →₀ ℤ)
    (hnormal : ∀ row, row.right ≠ [] → c row = 0) :
    (markedPacketCollector L n).evaluate (collectedRowsToMarked L n c) =
      (fullRelationRowCollector L (2 * n)).evaluate c := by
  classical
  unfold collectedRowsToMarked
  rw [map_finsuppSum]
  simp_rw [FiniteTaggedCollector.evaluate_single]
  change c.sum (fun row z ↦ z •
      MarkedPBWPacket.value L n
        (.marked row.relation ⟨2 * n, by omega⟩ row.left)) =
    c.sum (fun row z ↦ z • FullRelationRow.value L (2 * n) row)
  apply Finsupp.sum_congr
  intro row hrow
  cases row with
  | mk left relation right =>
      have hright : right = [] := by
        by_contra hne
        exact Finsupp.mem_support_iff.mp hrow
          (hnormal { left := left, relation := relation, right := right } hne)
      subst right
      simp only [MarkedPBWPacket.value, FullRelationRow.value,
        basisWord_nil, mul_one]
      rw [truncated_markedPrefixFree_top]

private def GoverningWitness.markedInitialPackets
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : MarkedPBWPacket L n →₀ ℤ :=
  collectedRowsToMarked L n (collectRowLedger L (2 * n) w.initialRows)

private theorem GoverningWitness.evaluate_markedInitialPackets
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (markedPacketCollector L n).evaluate w.markedInitialPackets =
      w.relationSide := by
  rw [GoverningWitness.markedInitialPackets,
    evaluate_collectedRowsToMarked]
  · exact w.evaluate_collectedRows
  · intro row hright
    exact collectRowLedger_apply_eq_zero_of_right_ne_nil L (2 * n)
      w.initialRows row hright

private def GoverningWitness.markedFrontier
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : MarkedPBWPacket L n →₀ ℤ :=
  w.markedInitialPackets.sum fun p c ↦
    c • (markedPacketCollector L n).normalForm p

private theorem GoverningWitness.evaluate_markedFrontier
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (markedPacketCollector L n).evaluate w.markedFrontier =
      w.relationSide := by
  classical
  unfold GoverningWitness.markedFrontier
  rw [map_finsuppSum]
  calc
    w.markedInitialPackets.sum (fun p c ↦
        (markedPacketCollector L n).evaluate
          (c • (markedPacketCollector L n).normalForm p)) =
      w.markedInitialPackets.sum (fun p c ↦
        c • (markedPacketCollector L n).value p) := by
          apply Finsupp.sum_congr
          intro p hp
          rw [map_zsmul, FiniteTaggedCollector.evaluate_normalForm]
    _ = (markedPacketCollector L n).evaluate w.markedInitialPackets := rfl
    _ = w.relationSide := w.evaluate_markedInitialPackets

private abbrev TerminalP0 (L : Type u) [LieRing L] [Finite L] (n : ℕ) :=
  LowTuple L (n - 1)

private abbrev TerminalQ0 (L : Type u) [LieRing L] [Finite L] (n : ℕ) :=
  freeLieExact L n

private abbrev TerminalV (L : Type u) [LieRing L] (n : ℕ) :=
  L ⧸ lowerCentralSeries ℤ L (n - 1)

private abbrev TerminalW (L : Type u) [LieRing L] (n : ℕ) :=
  L ⧸ lowerCentralSeries ℤ L n

private def terminalP0Basis
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    Module.Basis (TruncatedBasisIndex L (n - 1)) ℤ (TerminalP0 L n) :=
  Pi.basis fun s : Fin (n - 1) ↦ freeLieExactBasis L (s.1 + 1)

private def terminalP0Free (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    TerminalP0 L n →ₗ[ℤ] CanonicalFreeLie L :=
  lowFreeSum L (n - 1)

private def terminalP0ToV
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    TerminalP0 L n →ₗ[ℤ] TerminalV L n :=
  (UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (n - 1))).toLinearMap.comp
    ((canonicalFreeLieEvaluation L).toLinearMap.comp (terminalP0Free L n))

private def terminalP0ToW
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    TerminalP0 L n →ₗ[ℤ] TerminalW L n :=
  (UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L n)).toLinearMap.comp
    ((canonicalFreeLieEvaluation L).toLinearMap.comp (terminalP0Free L n))

private def terminalQ0ToW
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    TerminalQ0 L n →ₗ[ℤ] TerminalW L n :=
  (UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L n)).toLinearMap.comp
    ((canonicalFreeLieEvaluation L).toLinearMap.comp
      (freeLieExact L n).subtype)

private abbrev TerminalU (L : Type u) [LieRing L] [Finite L] (n : ℕ) :=
  LinearMap.range (terminalQ0ToW L n)

private def terminalQ0ToU
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    TerminalQ0 L n →ₗ[ℤ] TerminalU L n :=
  LinearMap.rangeRestrict (terminalQ0ToW L n)

private theorem terminalQ0ToU_surjective
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    Function.Surjective (terminalQ0ToU L n) := by
  rintro ⟨w, x, rfl⟩
  exact ⟨x, rfl⟩

private theorem canonicalEvaluation_mem_lowerCentralSeries
    (L : Type u) [LieRing L] {s : ℕ} {f : CanonicalFreeLie L}
    (hf : f ∈ FreeLieDimension.lieHigh L s) :
    canonicalFreeLieEvaluation L f ∈ lowerCentralSeries ℤ L (s - 1) := by
  cases s with
  | zero => simp
  | succ s =>
      have hf' : f ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) s := by
        simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries L s] using hf
      apply (LieIdeal.map_lowerCentralSeries_le
        (R := ℤ) (f := canonicalFreeLieEvaluation L) s)
      exact LieIdeal.mem_map hf'

private theorem terminalP0ToV_surjective
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (terminalP0ToV L n) := by
  intro z
  obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk'
    (lowerCentralSeries ℤ L (n - 1)) z
  obtain ⟨f, hf⟩ := canonicalFreeLieEvaluation_surjective L x
  refine ⟨lowFreeParts L (n - 1) f, ?_⟩
  apply sub_eq_zero.mp
  change UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (n - 1))
      (canonicalFreeLieEvaluation L
        (lowFreeSum L (n - 1) (lowFreeParts L (n - 1) f))) -
    UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (n - 1)) x = 0
  rw [← map_sub, ← hf]
  apply (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ L (n - 1))).mpr
  have hrem := sub_lowFreeSum_mem_lieHigh L (n - 1) f
  have heval := canonicalEvaluation_mem_lowerCentralSeries L hrem
  have hindex : n - 1 + 1 - 1 = n - 1 := by omega
  rw [hindex] at heval
  have hneg : lowFreeSum L (n - 1) (lowFreeParts L (n - 1) f) - f =
      -(f - lowFreeSum L (n - 1) (lowFreeParts L (n - 1) f)) := by abel
  have htarget : canonicalFreeLieEvaluation L
      (lowFreeSum L (n - 1) (lowFreeParts L (n - 1) f) - f) ∈
        lowerCentralSeries ℤ L (n - 1) := by
    rw [hneg, map_neg]
    exact (lowerCentralSeries ℤ L (n - 1)).neg_mem heval
  simpa only [map_sub] using htarget

private abbrev TerminalR0
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :=
  TerminalP0 L n × TerminalQ0 L n

private def terminalR0ToW
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    TerminalR0 L n →ₗ[ℤ] TerminalW L n where
  toFun z := terminalP0ToW L n z.1 + terminalQ0ToW L n z.2
  map_add' x y := by simp; abel
  map_smul' z x := by simp [smul_add]

private theorem terminalR0ToW_surjective
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (terminalR0ToW L n) := by
  intro z
  obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk'
    (lowerCentralSeries ℤ L n) z
  obtain ⟨f, hf⟩ := canonicalFreeLieEvaluation_surjective L x
  cases n with
  | zero => omega
  | succ m =>
      let p : TerminalP0 L (m + 1) := fun s ↦
        ⟨freeLieLengthComponent L (s.1 + 1) f,
          freeLieLengthComponent_mem_exact L (s.1 + 1) f⟩
      let q : TerminalQ0 L (m + 1) :=
        ⟨freeLieLengthComponent L (m + 1) f,
          freeLieLengthComponent_mem_exact L (m + 1) f⟩
      refine ⟨(p, q), ?_⟩
      apply sub_eq_zero.mp
      change UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (m + 1))
          (canonicalFreeLieEvaluation L (lowFreeSum L m p)) +
          UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (m + 1))
            (canonicalFreeLieEvaluation L (q : CanonicalFreeLie L)) -
        UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (m + 1)) x = 0
      rw [← map_add, ← map_sub, ← hf]
      apply (LieSubmodule.Quotient.mk_eq_zero'
        (N := lowerCentralSeries ℤ L (m + 1))).mpr
      have hsplit : lowFreeSum L m p + (q : CanonicalFreeLie L) =
          lowFreeSum L (m + 1) (lowFreeParts L (m + 1) f) := by
        unfold lowFreeSum
        change (∑ s : Fin m,
            ((p s : freeLieExact L (s.1 + 1)) : CanonicalFreeLie L)) +
            (q : CanonicalFreeLie L) =
          ∑ s : Fin (m + 1),
            (((lowFreeParts L (m + 1) f) s :
              freeLieExact L (s.1 + 1)) : CanonicalFreeLie L)
        rw [Fin.sum_univ_castSucc]
        congr 1
      rw [← map_add, hsplit]
      have hrem := sub_lowFreeSum_mem_lieHigh L (m + 1) f
      have heval := canonicalEvaluation_mem_lowerCentralSeries L hrem
      have hneg : lowFreeSum L (m + 1) (lowFreeParts L (m + 1) f) - f =
          -(f - lowFreeSum L (m + 1) (lowFreeParts L (m + 1) f)) := by abel
      have htarget : canonicalFreeLieEvaluation L
          (lowFreeSum L (m + 1) (lowFreeParts L (m + 1) f) - f) ∈
            lowerCentralSeries ℤ L (m + 1) := by
        rw [hneg, map_neg]
        simpa using (lowerCentralSeries ℤ L (m + 1)).neg_mem heval
      simpa only [map_sub] using htarget

private def terminalPSmith
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    PositiveSmithPresentation
      (ι := TruncatedBasisIndex L (n - 1))
      (terminalP0ToV L n).ker := by
  let b := terminalP0Basis L n
  letI : Module.Free ℤ (TerminalP0 L n) := Module.Free.of_basis b
  letI : Module.Finite ℤ (TerminalP0 L n) := Module.Finite.of_basis b
  letI : Finite (TerminalV L n) := Finite.of_surjective
    (UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (n - 1)))
    (LieSubmodule.Quotient.surjective_mk'
      (lowerCentralSeries ℤ L (n - 1)))
  let e := (terminalP0ToV L n).quotKerEquivOfSurjective
    (terminalP0ToV_surjective L n hn)
  let hfinite : Finite (TerminalP0 L n ⧸ (terminalP0ToV L n).ker) :=
    Finite.of_injective e e.injective
  exact PositiveSmithPresentation.ofFiniteQuotient b
    (terminalP0ToV L n).ker hfinite

private def terminalQSmith
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) :
    PositiveSmithPresentation
      (ι := FreeLieExactBasisIndex L n)
      (terminalQ0ToU L n).ker := by
  let b := freeLieExactBasis L n
  letI : Module.Free ℤ (TerminalQ0 L n) := Module.Free.of_basis b
  letI : Module.Finite ℤ (TerminalQ0 L n) := Module.Finite.of_basis b
  letI : Finite (TerminalW L n) := Finite.of_surjective
    (UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L n))
    (LieSubmodule.Quotient.surjective_mk' (lowerCentralSeries ℤ L n))
  let e := (terminalQ0ToU L n).quotKerEquivOfSurjective
    (terminalQ0ToU_surjective L n)
  let hfinite : Finite (TerminalQ0 L n ⧸ (terminalQ0ToU L n).ker) :=
    Finite.of_injective e e.injective
  exact PositiveSmithPresentation.ofFiniteQuotient b
    (terminalQ0ToU L n).ker hfinite

private def terminalPSort
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    Equiv.Perm (TruncatedBasisIndex L (n - 1)) :=
  let τ : Fin (Fintype.card (TruncatedBasisIndex L (n - 1))) ≃o
      TruncatedBasisIndex L (n - 1) :=
    monoEquivOfFin (TruncatedBasisIndex L (n - 1)) rfl
  τ.symm.toEquiv.trans
    ((Tuple.sort fun i ↦ (terminalPSmith L n hn).diagonal (τ i)).trans
      τ.toEquiv)

private def terminalPSmithSorted
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    PositiveSmithPresentation
      (ι := TruncatedBasisIndex L (n - 1))
      (terminalP0ToV L n).ker := by
  let P := terminalPSmith L n hn
  let σ := terminalPSort L n hn
  exact
    { ambientBasis := P.ambientBasis.reindex σ.symm
      relationBasis := P.relationBasis.reindex σ.symm
      diagonal := fun i ↦ P.diagonal (σ i)
      diagonal_pos := fun i ↦ P.diagonal_pos (σ i)
      relation_eq := by
        intro i
        simp only [Module.Basis.reindex_apply, Equiv.symm_symm]
        exact P.relation_eq (σ i) }

private theorem terminalPSmithSorted_mono
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    Monotone (terminalPSmithSorted L n hn).diagonal := by
  let τ : Fin (Fintype.card (TruncatedBasisIndex L (n - 1))) ≃o
      TruncatedBasisIndex L (n - 1) :=
    monoEquivOfFin (TruncatedBasisIndex L (n - 1)) rfl
  intro i j hij
  change (terminalPSmith L n hn).diagonal
      (τ ((Tuple.sort fun t ↦
        (terminalPSmith L n hn).diagonal (τ t)) (τ.symm i))) ≤
    (terminalPSmith L n hn).diagonal
      (τ ((Tuple.sort fun t ↦
        (terminalPSmith L n hn).diagonal (τ t)) (τ.symm j)))
  exact Tuple.monotone_sort
    (fun t ↦ (terminalPSmith L n hn).diagonal (τ t))
      (τ.symm.monotone hij)

private theorem terminalPSmithSorted_diagonal_dvd_card
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (n - 1)) :
    (terminalPSmithSorted L n hn).diagonal i ∣ Nat.card L := by
  let P := terminalPSmithSorted L n hn
  have hmem : (Nat.card L : ℤ) • P.ambientBasis i ∈
      (terminalP0ToV L n).ker := by
    rw [LinearMap.mem_ker]
    letI := Fintype.ofFinite L
    rw [map_smul]
    change (Nat.card L : ℤ) •
      UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (n - 1))
        (canonicalFreeLieEvaluation L
          (terminalP0Free L n (P.ambientBasis i))) = 0
    calc
      (Nat.card L : ℤ) •
          UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (n - 1))
            (canonicalFreeLieEvaluation L
              (terminalP0Free L n (P.ambientBasis i))) =
        UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (n - 1))
          ((Nat.card L : ℤ) • canonicalFreeLieEvaluation L
            (terminalP0Free L n (P.ambientBasis i))) := by
              rw [map_smul]
      _ = UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L (n - 1))
          (Nat.card L • canonicalFreeLieEvaluation L
            (terminalP0Free L n (P.ambientBasis i))) := by
              rw [Nat.cast_smul_eq_nsmul]
      _ = 0 := by
        rw [Nat.card_eq_fintype_card, card_nsmul_eq_zero, map_zero]
  have hdiv := P.diagonal_dvd_of_smul_mem i (Nat.card L : ℤ) hmem
  exact_mod_cast hdiv

private theorem terminalQSmith_diagonal_dvd_card
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (k : FreeLieExactBasisIndex L n) :
    (terminalQSmith L n).diagonal k ∣ Nat.card L := by
  let Q := terminalQSmith L n
  have hmem : (Nat.card L : ℤ) • Q.ambientBasis k ∈
      (terminalQ0ToU L n).ker := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    letI := Fintype.ofFinite L
    change terminalQ0ToW L n
      ((Nat.card L : ℤ) • Q.ambientBasis k) = 0
    change UEA.lieIdealQuotientMk ℤ L
        (lowerCentralSeries ℤ L n)
          (canonicalFreeLieEvaluation L
            (((Nat.card L : ℤ) • Q.ambientBasis k : TerminalQ0 L n) :
              CanonicalFreeLie L)) = 0
    rw [Submodule.coe_smul_of_tower, map_smul, Nat.cast_smul_eq_nsmul]
    change UEA.lieIdealQuotientMk ℤ L
        (lowerCentralSeries ℤ L n)
          (Nat.card L • canonicalFreeLieEvaluation L
            ((Q.ambientBasis k : TerminalQ0 L n) : CanonicalFreeLie L)) = 0
    rw [Nat.card_eq_fintype_card, card_nsmul_eq_zero, map_zero]
  have hdiv := Q.diagonal_dvd_of_smul_mem k (Nat.card L : ℤ) hmem
  exact_mod_cast hdiv

private theorem terminalPSmithSorted_dvd_of_le
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    {i j : TruncatedBasisIndex L (n - 1)} (hij : i ≤ j) :
    (terminalPSmithSorted L n hn).diagonal i ∣
      (terminalPSmithSorted L n hn).diagonal j := by
  obtain ⟨ν, hcard⟩ := R.two_group.exists_card_eq
  have hcardL : Nat.card L = 2 ^ ν := hcard
  have hi := terminalPSmithSorted_diagonal_dvd_card L n hn i
  have hj := terminalPSmithSorted_diagonal_dvd_card L n hn j
  rw [hcardL] at hi hj
  obtain ⟨a, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hi
  obtain ⟨b, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hj
  have hmono := terminalPSmithSorted_mono L n hn hij
  rw [ha.2, hb.2] at hmono ⊢
  exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by omega)).mp hmono)

private abbrev TerminalP1
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :=
  (terminalP0ToV L n).ker

private abbrev TerminalQ1
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :=
  (terminalQ0ToU L n).ker

private theorem exists_terminalQ0_eq_terminalP0
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (a : TerminalP1 L n) :
    ∃ y : TerminalQ0 L n,
      terminalQ0ToW L n y = terminalP0ToW L n a.1 := by
  have heval : canonicalFreeLieEvaluation L
      (terminalP0Free L n a.1) ∈ lowerCentralSeries ℤ L (n - 1) := by
    have ha := a.property
    rw [LinearMap.mem_ker] at ha
    exact (LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ L (n - 1))).mp ha
  have hmap := LieIdeal.lowerCentralSeries_map_eq (R := ℤ)
    (n - 1) (f := canonicalFreeLieEvaluation L)
      (canonicalFreeLieEvaluation_surjective L)
  change canonicalFreeLieEvaluation L (terminalP0Free L n a.1) ∈
    LieModule.lowerCentralSeries ℤ L L (n - 1) at heval
  rw [← hmap] at heval
  obtain ⟨g, hgeval⟩ := LieIdeal.mem_map_of_surjective
    (f := canonicalFreeLieEvaluation L)
      (canonicalFreeLieEvaluation_surjective L) heval
  let y : TerminalQ0 L n :=
    ⟨freeLieLengthComponent L n (g : CanonicalFreeLie L),
      freeLieLengthComponent_mem_exact L n (g : CanonicalFreeLie L)⟩
  have hgHigh : (g : CanonicalFreeLie L) ∈
      FreeLieDimension.lieHigh L n := by
    have heq : FreeLieDimension.lieHigh L n =
        lowerCentralSeries ℤ (CanonicalFreeLie L) (n - 1) := by
      calc
        FreeLieDimension.lieHigh L n =
            FreeLieDimension.lieHigh L (n - 1 + 1) := by
              congr 1
              omega
        _ = lowerCentralSeries ℤ (CanonicalFreeLie L) (n - 1) :=
          FreeLieDimension.lieHigh_eq_lowerCentralSeries L (n - 1)
    rw [heq]
    exact g.property
  have hrem : (g : CanonicalFreeLie L) - (y : CanonicalFreeLie L) ∈
      FreeLieDimension.lieHigh L (n + 1) := by
    apply mem_lieHigh_succ_of_component_eq_zero L
      ((FreeLieDimension.lieHigh L n).sub_mem hgHigh
        (freeLieExact_mem_lieHigh L y))
    rw [map_sub, freeLieLengthComponent_coe_exact]
    change freeLieLengthComponent L n (g : CanonicalFreeLie L) -
      freeLieLengthComponent L n (g : CanonicalFreeLie L) = 0
    abel
  have hevalRem : canonicalFreeLieEvaluation L
      (g - (y : CanonicalFreeLie L)) ∈ lowerCentralSeries ℤ L n := by
    have := canonicalEvaluation_mem_lowerCentralSeries L hrem
    simpa using this
  refine ⟨y, ?_⟩
  apply sub_eq_zero.mp
  change UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L n)
      (canonicalFreeLieEvaluation L (y : CanonicalFreeLie L)) -
    UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L n)
      (canonicalFreeLieEvaluation L (terminalP0Free L n a.1)) = 0
  rw [← map_sub]
  apply (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ L n)).mpr
  have hyG : canonicalFreeLieEvaluation L
      ((y : CanonicalFreeLie L) - (g : CanonicalFreeLie L)) ∈
        lowerCentralSeries ℤ L n := by
    rw [show (y : CanonicalFreeLie L) - g =
      -(g - (y : CanonicalFreeLie L)) by abel, map_neg]
    exact (lowerCentralSeries ℤ L n).neg_mem hevalRem
  rw [← hgeval]
  simpa only [map_sub] using hyG

private noncomputable def terminalBMap
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    TerminalP1 L n →ₗ[ℤ] TerminalQ0 L n :=
  let P := terminalPSmithSorted L n hn
  P.relationBasis.constr ℤ fun i ↦
    Classical.choose
      (exists_terminalQ0_eq_terminalP0 L n hn (P.relationBasis i))

private theorem terminalBMap_compat
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (a : TerminalP1 L n) :
    terminalQ0ToW L n (terminalBMap L n hn a) =
      terminalP0ToW L n a.1 := by
  let P := terminalPSmithSorted L n hn
  have hmaps : (terminalQ0ToW L n).comp (terminalBMap L n hn) =
      (terminalP0ToW L n).comp (TerminalP1 L n).subtype := by
    apply P.relationBasis.ext
    intro i
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    change terminalQ0ToW L n
        ((P.relationBasis.constr ℤ fun j ↦
          Classical.choose
            (exists_terminalQ0_eq_terminalP0 L n hn
              (P.relationBasis j))) (P.relationBasis i)) =
      terminalP0ToW L n (P.relationBasis i).1
    rw [Module.Basis.constr_basis]
    exact Classical.choose_spec
      (exists_terminalQ0_eq_terminalP0 L n hn (P.relationBasis i))
  exact LinearMap.congr_fun hmaps a

private abbrev TerminalR1
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :=
  TerminalP1 L n × TerminalQ1 L n

private def terminalBoundary
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    TerminalR1 L n →ₗ[ℤ] TerminalR0 L n where
  toFun z := (z.1.1, z.2.1 - terminalBMap L n hn z.1)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add,
      Prod.mk_add_mk]
    congr 1
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul_of_tower,
      map_smul, Prod.smul_mk]
    congr 1
    module

private theorem terminalBoundary_mem_ker
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (z : TerminalR1 L n) :
    terminalBoundary L n hn z ∈ (terminalR0ToW L n).ker := by
  rw [LinearMap.mem_ker]
  rcases z with ⟨a, s⟩
  have hs : terminalQ0ToW L n s.1 = 0 := by
    have hs' := s.property
    rw [LinearMap.mem_ker] at hs'
    exact congrArg Subtype.val hs'
  change terminalP0ToW L n a.1 +
      terminalQ0ToW L n (s.1 - terminalBMap L n hn a) = 0
  rw [map_sub, hs, terminalBMap_compat]
  abel

private def terminalBoundaryToKernel
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    TerminalR1 L n →ₗ[ℤ] (terminalR0ToW L n).ker where
  toFun z := ⟨terminalBoundary L n hn z,
    terminalBoundary_mem_ker L n hn z⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (terminalBoundary L n hn) x y
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (terminalBoundary L n hn) c x

private theorem terminalBoundaryToKernel_injective
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (terminalBoundaryToKernel L n hn) := by
  intro x y hxy
  have hxy' := congrArg
    (fun z : (terminalR0ToW L n).ker ↦ (z.1 : TerminalR0 L n)) hxy
  change (x.1.1, x.2.1 - terminalBMap L n hn x.1) =
    (y.1.1, y.2.1 - terminalBMap L n hn y.1) at hxy'
  have hp : x.1 = y.1 := by
    apply Subtype.ext
    exact congrArg Prod.fst hxy'
  have hq : x.2 = y.2 := by
    apply Subtype.ext
    have hs := congrArg Prod.snd hxy'
    rw [hp] at hs
    change x.2.1 - terminalBMap L n hn y.1 =
      y.2.1 - terminalBMap L n hn y.1 at hs
    exact sub_left_injective hs
  exact Prod.ext hp hq

private theorem terminalBoundaryToKernel_surjective
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (terminalBoundaryToKernel L n hn) := by
  intro z
  rcases z with ⟨⟨x, y⟩, hxy⟩
  rw [LinearMap.mem_ker] at hxy
  change terminalP0ToW L n x + terminalQ0ToW L n y = 0 at hxy
  have hsum : canonicalFreeLieEvaluation L
      (terminalP0Free L n x + (y : CanonicalFreeLie L)) ∈
        lowerCentralSeries ℤ L n := by
    apply (LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ L n)).mp
    simpa only [map_add] using hxy
  have hyLow : canonicalFreeLieEvaluation L (y : CanonicalFreeLie L) ∈
      lowerCentralSeries ℤ L (n - 1) := by
    have hyHigh := freeLieExact_mem_lieHigh L y
    have := canonicalEvaluation_mem_lowerCentralSeries L hyHigh
    simpa [show n - 1 = n - 1 by rfl] using this
  have hsumLow : canonicalFreeLieEvaluation L
      (terminalP0Free L n x + (y : CanonicalFreeLie L)) ∈
        lowerCentralSeries ℤ L (n - 1) :=
    LieModule.antitone_lowerCentralSeries ℤ L L (by omega) hsum
  have hxLow : canonicalFreeLieEvaluation L (terminalP0Free L n x) ∈
      lowerCentralSeries ℤ L (n - 1) := by
    have hsub := (lowerCentralSeries ℤ L (n - 1)).sub_mem hsumLow hyLow
    simpa only [map_add, add_sub_cancel_right] using hsub
  let a : TerminalP1 L n := ⟨x, by
    rw [LinearMap.mem_ker]
    exact (LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ L (n - 1))).mpr hxLow⟩
  have hsW : terminalQ0ToW L n (y + terminalBMap L n hn a) = 0 := by
    rw [map_add, terminalBMap_compat]
    change terminalQ0ToW L n y + terminalP0ToW L n x = 0
    rw [add_comm]
    exact hxy
  let s : TerminalQ1 L n := ⟨y + terminalBMap L n hn a, by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact hsW⟩
  refine ⟨(a, s), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (y + terminalBMap L n hn a) - terminalBMap L n hn a = y
    abel

private noncomputable def terminalBoundaryEquivKernel
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    TerminalR1 L n ≃ₗ[ℤ] (terminalR0ToW L n).ker :=
  LinearEquiv.ofBijective (terminalBoundaryToKernel L n hn)
    ⟨terminalBoundaryToKernel_injective L n hn,
      terminalBoundaryToKernel_surjective L n hn⟩

private def terminalX
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (n - 1)) : L :=
  canonicalFreeLieEvaluation L
    (terminalP0Free L n ((terminalPSmithSorted L n hn).ambientBasis i))

private def terminalY
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (k : FreeLieExactBasisIndex L n) : L :=
  canonicalFreeLieEvaluation L
    (((terminalQSmith L n).ambientBasis k : TerminalQ0 L n) :
      CanonicalFreeLie L)

private def terminalBTail
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (n - 1)) : TerminalQ0 L n :=
  terminalBMap L n hn ((terminalPSmithSorted L n hn).relationBasis i)

private def terminalB
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (n - 1))
    (k : FreeLieExactBasisIndex L n) : ℤ :=
  (terminalQSmith L n).ambientBasis.repr (terminalBTail L n hn i) k

private theorem terminalY_mem_lowerCentralSeries
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (k : FreeLieExactBasisIndex L n) :
    terminalY L n k ∈ lowerCentralSeries ℤ L (n - 1) := by
  exact canonicalEvaluation_mem_lowerCentralSeries L
    (freeLieExact_mem_lieHigh L ((terminalQSmith L n).ambientBasis k))

private theorem terminalBTail_mem_lowerCentralSeries
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (n - 1)) :
    canonicalFreeLieEvaluation L
        ((terminalBTail L n hn i : TerminalQ0 L n) : CanonicalFreeLie L) ∈
      lowerCentralSeries ℤ L (n - 1) := by
  exact canonicalEvaluation_mem_lowerCentralSeries L
    (freeLieExact_mem_lieHigh L (terminalBTail L n hn i))

private theorem terminalB_congruence
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (n - 1)) :
    ((terminalPSmithSorted L n hn).diagonal i : ℤ) •
        terminalX L n hn i -
      canonicalFreeLieEvaluation L
        ((terminalBTail L n hn i : TerminalQ0 L n) : CanonicalFreeLie L) ∈
      lowerCentralSeries ℤ L n := by
  let P := terminalPSmithSorted L n hn
  have hcompat := terminalBMap_compat L n hn (P.relationBasis i)
  rw [P.relation_eq] at hcompat
  apply (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ L n)).mp
  change Submodule.Quotient.mk
      (p := (lowerCentralSeries ℤ L n).toSubmodule)
        (((P.diagonal i : ℤ) • terminalX L n hn i) -
          canonicalFreeLieEvaluation L
            ((terminalBTail L n hn i : TerminalQ0 L n) :
              CanonicalFreeLie L)) = 0
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
  change (P.diagonal i : ℤ) • terminalP0ToW L n
      (P.ambientBasis i) -
    terminalQ0ToW L n (terminalBTail L n hn i) = 0
  rw [map_smul] at hcompat
  exact sub_eq_zero.mpr hcompat.symm

private theorem terminalQ_relation_mem_top
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (k : FreeLieExactBasisIndex L n) :
    ((terminalQSmith L n).diagonal k : ℤ) • terminalY L n k ∈
      lowerCentralSeries ℤ L n := by
  let Q := terminalQSmith L n
  have hk := (Q.relationBasis k).property
  rw [LinearMap.mem_ker] at hk
  have hkW : terminalQ0ToW L n (Q.relationBasis k).1 = 0 :=
    congrArg Subtype.val hk
  rw [Q.relation_eq] at hkW
  apply (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ L n)).mp
  simpa only [map_smul] using hkW

private theorem terminalBracket_mem_top
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (n - 1))
    (k : FreeLieExactBasisIndex L n) :
    ⁅terminalX L n hn i, terminalY L n k⁆ ∈
      lowerCentralSeries ℤ L n := by
  have h : ⁅terminalX L n hn i, terminalY L n k⁆ ∈
      LieModule.lowerCentralSeries ℤ L L ((n - 1) + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _)
      (terminalY_mem_lowerCentralSeries L n k)
  simpa only [show n - 1 + 1 = n by omega] using h

private def terminalBracketCoordinate
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (n - 1))
    (k : FreeLieExactBasisIndex L n) : ZMod (2 ^ R.topExponent) :=
  R.topEquiv ⟨⁅terminalX L n hn i, terminalY L n k⁆,
    terminalBracket_mem_top L n hn i k⟩

private def terminalData
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n) :
    Coordinate.Data (TruncatedBasisIndex L (n - 1))
      (FreeLieExactBasisIndex L n) (2 ^ R.topExponent) where
  d := (terminalPSmithSorted L n hn).diagonal
  e := (terminalQSmith L n).diagonal
  B := terminalB L n hn
  G := fun i k ↦ (terminalBracketCoordinate R hn i k).cast

private def terminalBGamma
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (i j : TruncatedBasisIndex L (n - 1)) :
    lowerCentralSeries ℤ L n :=
  ⟨⁅terminalX L n hn j,
      canonicalFreeLieEvaluation L
        ((terminalBTail L n hn i : TerminalQ0 L n) : CanonicalFreeLie L)⁆, by
    have h : ⁅terminalX L n hn j,
        canonicalFreeLieEvaluation L
          ((terminalBTail L n hn i : TerminalQ0 L n) : CanonicalFreeLie L)⁆ ∈
        LieModule.lowerCentralSeries ℤ L L ((n - 1) + 1) := by
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _)
        (terminalBTail_mem_lowerCentralSeries L n hn i)
    simpa only [show n - 1 + 1 = n by omega] using h⟩

private theorem terminalBGamma_coordinate
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (i j : TruncatedBasisIndex L (n - 1)) :
    R.topEquiv (terminalBGamma R hn i j) =
      (terminalData R hn).gamma i j := by
  classical
  let Q := terminalQSmith L n
  let bracketValue := fun k : FreeLieExactBasisIndex L n ↦
    (⟨⁅terminalX L n hn j, terminalY L n k⁆,
      terminalBracket_mem_top L n hn j k⟩ : lowerCentralSeries ℤ L n)
  have htail : terminalBTail L n hn i =
      ∑ k, terminalB L n hn i k • Q.ambientBasis k := by
    simpa [terminalB, Q] using
      (Q.ambientBasis.sum_repr (terminalBTail L n hn i)).symm
  have hsubtype : terminalBGamma R hn i j =
      ∑ k, terminalB L n hn i k • bracketValue k := by
    apply Subtype.ext
    change ⁅terminalX L n hn j,
        canonicalFreeLieEvaluation L
          ((terminalBTail L n hn i : TerminalQ0 L n) : CanonicalFreeLie L)⁆ =
      ((lowerCentralSeries ℤ L n).subtype
        (∑ k, terminalB L n hn i k • bracketValue k))
    rw [map_sum]
    simp only [map_zsmul]
    rw [htail, Submodule.coe_sum, map_sum, lie_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Submodule.coe_smul_of_tower, map_zsmul, lie_smul]
    rfl
  rw [hsubtype]
  change R.topEquiv.toAddMonoidHom
      (∑ k, terminalB L n hn i k • bracketValue k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_zsmul, zsmul_eq_mul]
  change (terminalB L n hn i k : ZMod (2 ^ R.topExponent)) *
      terminalBracketCoordinate R hn j k =
    (terminalB L n hn i k : ZMod (2 ^ R.topExponent)) *
      ((terminalBracketCoordinate R hn j k).cast : ℤ)
  rw [ZMod.intCast_zmod_cast]

private theorem terminalBGamma_eq_scaled_bracket
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (i j : TruncatedBasisIndex L (n - 1)) :
    (terminalBGamma R hn i j : L) =
      ((terminalPSmithSorted L n hn).diagonal i : ℤ) •
        ⁅terminalX L n hn j, terminalX L n hn i⁆ := by
  have hzero := R.lie_eq_zero_of_mem_top
    (terminalB_congruence L n hn i)
      (y := terminalX L n hn j)
  simp only [sub_lie, smul_lie] at hzero
  change ⁅terminalX L n hn j,
      canonicalFreeLieEvaluation L
        ((terminalBTail L n hn i : TerminalQ0 L n) : CanonicalFreeLie L)⁆ = _
  have htail : ⁅canonicalFreeLieEvaluation L
        ((terminalBTail L n hn i : TerminalQ0 L n) : CanonicalFreeLie L),
      terminalX L n hn j⁆ =
      ((terminalPSmithSorted L n hn).diagonal i : ℤ) •
        ⁅terminalX L n hn i, terminalX L n hn j⁆ := by
    exact (sub_eq_zero.mp hzero).symm
  calc
    ⁅terminalX L n hn j,
        canonicalFreeLieEvaluation L
          ((terminalBTail L n hn i : TerminalQ0 L n) : CanonicalFreeLie L)⁆ =
      -⁅canonicalFreeLieEvaluation L
          ((terminalBTail L n hn i : TerminalQ0 L n) : CanonicalFreeLie L),
        terminalX L n hn j⁆ := (lie_skew _ _).symm
    _ = -(((terminalPSmithSorted L n hn).diagonal i : ℤ) •
        ⁅terminalX L n hn i, terminalX L n hn j⁆) := by rw [htail]
    _ = ((terminalPSmithSorted L n hn).diagonal i : ℤ) •
        (-⁅terminalX L n hn i, terminalX L n hn j⁆) := by module
    _ = ((terminalPSmithSorted L n hn).diagonal i : ℤ) •
        ⁅terminalX L n hn j, terminalX L n hn i⁆ := by
          rw [lie_skew]

private def terminalDataIdentities
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 3 ≤ n) :
    (terminalData R (by omega)).Identities := by
  let hn1 : 1 ≤ n := by omega
  let D := terminalData R hn1
  refine
    { d_dvd := fun {_ _} hij ↦
        terminalPSmithSorted_dvd_of_le R hn1 hij
      DG := ?_
      GE := ?_
      gamma_diag := ?_
      gamma_skew := ?_ }
  · intro i k
    let P := terminalPSmithSorted L n hn1
    let d := P.diagonal i
    let x := terminalX L n hn1 i
    let y := terminalY L n k
    let b := canonicalFreeLieEvaluation L
      ((terminalBTail L n hn1 i : TerminalQ0 L n) : CanonicalFreeLie L)
    have hbDerived : b ∈ lowerCentralSeries ℤ L 1 :=
      LieModule.antitone_lowerCentralSeries ℤ L L (by omega)
        (terminalBTail_mem_lowerCentralSeries L n hn1 i)
    have hyDerived : y ∈ lowerCentralSeries ℤ L 1 :=
      LieModule.antitone_lowerCentralSeries ℤ L L (by omega)
        (terminalY_mem_lowerCentralSeries L n k)
    have hby : ⁅b, y⁆ = 0 :=
      R.lie_eq_zero_of_mem_derived hbDerived hyDerived
    have hcentral := R.lie_eq_zero_of_mem_top
      (terminalB_congruence L n hn1 i) (y := y)
    change ⁅(d : ℤ) • x - b, y⁆ = 0 at hcentral
    simp only [sub_lie, smul_lie, hby, sub_zero] at hcentral
    let bracketValue : lowerCentralSeries ℤ L n :=
      ⟨⁅x, y⁆, terminalBracket_mem_top L n hn1 i k⟩
    have hsubtype : d • bracketValue = 0 := by
      apply Subtype.ext
      change d • ⁅x, y⁆ = 0
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact hcentral
    change (d : ZMod (2 ^ R.topExponent)) *
        (((terminalBracketCoordinate R hn1 i k).cast : ℤ) :
          ZMod (2 ^ R.topExponent)) = 0
    rw [ZMod.intCast_zmod_cast, ← nsmul_eq_mul]
    calc
      d • terminalBracketCoordinate R hn1 i k =
          R.topEquiv (d • bracketValue) :=
        (R.topEquiv.toAddMonoidHom.map_nsmul bracketValue d).symm
      _ = R.topEquiv 0 := congrArg R.topEquiv hsubtype
      _ = 0 := R.topEquiv.toAddMonoidHom.map_zero
  · intro i k
    let e := (terminalQSmith L n).diagonal k
    let x := terminalX L n hn1 i
    let y := terminalY L n k
    have hcentral := R.lie_eq_zero_of_mem_top
      (terminalQ_relation_mem_top L n k) (y := x)
    change ⁅(e : ℤ) • y, x⁆ = 0 at hcentral
    simp only [smul_lie] at hcentral
    have hxy : (e : ℤ) • ⁅x, y⁆ = 0 := by
      calc
        (e : ℤ) • ⁅x, y⁆ =
            (e : ℤ) • (-⁅y, x⁆) := by
              rw [(lie_skew x y).symm]
        _ = -((e : ℤ) • ⁅y, x⁆) := by module
        _ = -0 := congrArg Neg.neg hcentral
        _ = 0 := neg_zero
    let bracketValue : lowerCentralSeries ℤ L n :=
      ⟨⁅x, y⁆, terminalBracket_mem_top L n hn1 i k⟩
    have hsubtype : e • bracketValue = 0 := by
      apply Subtype.ext
      change e • ⁅x, y⁆ = 0
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact hxy
    change (((terminalBracketCoordinate R hn1 i k).cast : ℤ) :
        ZMod (2 ^ R.topExponent)) *
      (e : ZMod (2 ^ R.topExponent)) = 0
    rw [ZMod.intCast_zmod_cast, mul_comm, ← nsmul_eq_mul]
    calc
      e • terminalBracketCoordinate R hn1 i k =
          R.topEquiv (e • bracketValue) :=
        (R.topEquiv.toAddMonoidHom.map_nsmul bracketValue e).symm
      _ = R.topEquiv 0 := congrArg R.topEquiv hsubtype
      _ = 0 := R.topEquiv.toAddMonoidHom.map_zero
  · intro i
    rw [← terminalBGamma_coordinate R hn1 i i]
    have hzero : terminalBGamma R hn1 i i = 0 := by
      apply Subtype.ext
      rw [terminalBGamma_eq_scaled_bracket R hn1 i i]
      simp
    rw [hzero]
    exact R.topEquiv.toAddMonoidHom.map_zero
  · intro i j hij
    have hdvd : (terminalPSmithSorted L n hn1).diagonal i ∣
        (terminalPSmithSorted L n hn1).diagonal j :=
      terminalPSmithSorted_dvd_of_le R hn1 hij.le
    have hratioNat : (terminalPSmithSorted L n hn1).diagonal i *
        D.dRatio i j = (terminalPSmithSorted L n hn1).diagonal j :=
      Nat.mul_div_cancel' hdvd
    have hratioInt :
        ((terminalPSmithSorted L n hn1).diagonal j : ℤ) =
          (D.dRatio i j : ℤ) *
            ((terminalPSmithSorted L n hn1).diagonal i : ℤ) := by
      exact_mod_cast hratioNat.symm.trans (Nat.mul_comm _ _)
    have hbg : terminalBGamma R hn1 j i +
        D.dRatio i j • terminalBGamma R hn1 i j = 0 := by
      apply Subtype.ext
      change (terminalBGamma R hn1 j i : L) +
        D.dRatio i j • (terminalBGamma R hn1 i j : L) = 0
      rw [
        terminalBGamma_eq_scaled_bracket R hn1 j i,
        terminalBGamma_eq_scaled_bracket R hn1 i j,
        ← Nat.cast_smul_eq_nsmul ℤ, smul_smul,
        ← lie_skew (terminalX L n hn1 i) (terminalX L n hn1 j),
        hratioInt]
      module
    rw [← terminalBGamma_coordinate R hn1 j i,
      ← terminalBGamma_coordinate R hn1 i j]
    change R.topEquiv (terminalBGamma R hn1 j i) +
      (D.dRatio i j : ZMod (2 ^ R.topExponent)) *
        R.topEquiv (terminalBGamma R hn1 i j) = 0
    rw [← nsmul_eq_mul]
    calc
      R.topEquiv (terminalBGamma R hn1 j i) +
          D.dRatio i j • R.topEquiv (terminalBGamma R hn1 i j) =
        R.topEquiv (terminalBGamma R hn1 j i) +
          R.topEquiv (D.dRatio i j • terminalBGamma R hn1 i j) := by
            congr 1
            exact (R.topEquiv.toAddMonoidHom.map_nsmul _ _).symm
      _ = R.topEquiv (terminalBGamma R hn1 j i +
          D.dRatio i j • terminalBGamma R hn1 i j) :=
        (R.topEquiv.toAddMonoidHom.map_add _ _).symm
      _ = R.topEquiv 0 := congrArg R.topEquiv hbg
      _ = 0 := R.topEquiv.toAddMonoidHom.map_zero

private def terminalR0Free
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    TerminalR0 L n →ₗ[ℤ] CanonicalFreeLie L where
  toFun z := terminalP0Free L n z.1 + (z.2 : CanonicalFreeLie L)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
      Submodule.coe_smul_of_tower]
    module

private def terminalR0Projection
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    CanonicalFreeLie L →ₗ[ℤ] TerminalR0 L n where
  toFun f :=
    (lowFreeParts L (n - 1) f,
      ⟨freeLieLengthComponent L n f,
        freeLieLengthComponent_mem_exact L n f⟩)
  map_add' x y := by
    apply Prod.ext
    · funext s
      apply Subtype.ext
      simp [lowFreeParts]
    · apply Subtype.ext
      simp
  map_smul' c x := by
    apply Prod.ext
    · funext s
      apply Subtype.ext
      simp [lowFreeParts]
    · apply Subtype.ext
      simp

/-- Projection of the bounded free Lie model to the weights used by the terminal
presentation.  It is the literal weight-`≤ n` projection, descended through the larger
weight-`2*n` quotient. -/
private def terminalR0ProjectionTruncated
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    TruncatedFreeLie L (2 * n) →ₗ[ℤ] TerminalR0 L n :=
  (lowerCentralSeries ℤ (CanonicalFreeLie L) (2 * n)).toSubmodule.liftQ
    (terminalR0Projection L n) (by
      intro f hf
      apply Prod.ext
      · funext s
        apply Subtype.ext
        change freeLieLengthComponent L (s.1 + 1) f = 0
        have hfhigh : f ∈ FreeLieDimension.lieHigh L (2 * n + 1) := by
          rw [FreeLieDimension.lieHigh_eq_lowerCentralSeries L (2 * n)]
          exact hf
        exact freeLieLengthComponent_eq_zero_of_mem_lieHigh L hfhigh (by
          have hs := s.2
          omega)
      · apply Subtype.ext
        change freeLieLengthComponent L n f = 0
        have hfhigh : f ∈ FreeLieDimension.lieHigh L (2 * n + 1) := by
          rw [FreeLieDimension.lieHigh_eq_lowerCentralSeries L (2 * n)]
          exact hf
        exact freeLieLengthComponent_eq_zero_of_mem_lieHigh L hfhigh (by
          omega))

@[simp] private theorem terminalR0ProjectionTruncated_mk
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (f : CanonicalFreeLie L) :
    terminalR0ProjectionTruncated L n hn (truncatedFreeLieMk L (2 * n) f) =
      terminalR0Projection L n f := rfl

private theorem terminalR0Projection_eq_of_sub_mem_lieHigh
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (f g : CanonicalFreeLie L)
    (hfg : f - g ∈ FreeLieDimension.lieHigh L (n + 1)) :
    terminalR0Projection L n f = terminalR0Projection L n g := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Prod.ext
  · funext s
    apply Subtype.ext
    change freeLieLengthComponent L (s.1 + 1) (f - g) = 0
    apply freeLieLengthComponent_eq_zero_of_mem_lieHigh L hfg
    have hs := s.2
    omega
  · apply Subtype.ext
    change freeLieLengthComponent L n (f - g) = 0
    exact freeLieLengthComponent_eq_zero_of_mem_lieHigh L hfg (by omega)

private theorem terminalR0Projection_contextPrefix
    (L : Type u) [LieRing L] [Finite L]
    (n k : ℕ) (hn : 1 ≤ n)
    (r : CanonicalLieRelationsIdeal L)
    (c : RelationContext L (2 * n))
    (hactive : k + c.weight L = n) :
    terminalR0Projection L n
        (c.applyFree L (markedPrefixFree L k r)) =
      terminalR0Projection L n (c.relation L r : CanonicalFreeLie L) := by
  symm
  apply terminalR0Projection_eq_of_sub_mem_lieHigh L n
  have hrem := sub_lowFreeSum_mem_lieHigh L k
    (r : CanonicalFreeLie L)
  have hprefix : markedPrefixFree L k r =
      lowFreeSum L k (lowFreeParts L k (r : CanonicalFreeLie L)) := rfl
  have hcontext := c.applyFree_mem_lieHigh L hrem
  rw [show (c.relation L r : CanonicalFreeLie L) =
    c.applyFree L (r : CanonicalFreeLie L) from rfl]
  change (c.linearMap L) (r : CanonicalFreeLie L) -
      (c.linearMap L) (markedPrefixFree L k r) ∈ _
  rw [← map_sub, hprefix]
  change c.applyFree L
      ((r : CanonicalFreeLie L) -
        lowFreeSum L k (lowFreeParts L k (r : CanonicalFreeLie L))) ∈ _
  have hindex : k + 1 + c.weight L = n + 1 := by omega
  rw [hindex] at hcontext
  exact hcontext

private theorem terminalR0Free_projection_remainder
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (f : CanonicalFreeLie L) :
    f - terminalR0Free L n (terminalR0Projection L n f) ∈
      FreeLieDimension.lieHigh L (n + 1) := by
  have hlow := sub_lowFreeSum_mem_lieHigh L n f
  have hsplit : terminalR0Free L n (terminalR0Projection L n f) =
      lowFreeSum L n (lowFreeParts L n f) := by
    cases n with
    | zero => omega
    | succ m =>
        change (∑ s : Fin m,
            (((lowFreeParts L m f) s : freeLieExact L (s.1 + 1)) :
              CanonicalFreeLie L)) +
            ((⟨freeLieLengthComponent L (m + 1) f,
              freeLieLengthComponent_mem_exact L (m + 1) f⟩ :
                freeLieExact L (m + 1)) : CanonicalFreeLie L) =
          ∑ s : Fin (m + 1),
            (((lowFreeParts L (m + 1) f) s :
              freeLieExact L (s.1 + 1)) : CanonicalFreeLie L)
        rw [Fin.sum_univ_castSucc]
        rfl
  rw [hsplit]
  exact hlow

private theorem terminalRelationProjection_mem_ker
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (r : CanonicalLieRelationsIdeal L) :
    terminalR0Projection L n (r : CanonicalFreeLie L) ∈
      (terminalR0ToW L n).ker := by
  rw [LinearMap.mem_ker]
  apply (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ L n)).mpr
  have hrem := terminalR0Free_projection_remainder L n hn
    (r : CanonicalFreeLie L)
  have hremEval : canonicalFreeLieEvaluation L
      ((r : CanonicalFreeLie L) - terminalR0Free L n
        (terminalR0Projection L n (r : CanonicalFreeLie L))) ∈
      lowerCentralSeries ℤ L n := by
    simpa using canonicalEvaluation_mem_lowerCentralSeries L hrem
  have hr : canonicalFreeLieEvaluation L (r : CanonicalFreeLie L) = 0 :=
    r.property
  have hneg : terminalR0Free L n
      (terminalR0Projection L n (r : CanonicalFreeLie L)) =
        -((r : CanonicalFreeLie L) - terminalR0Free L n
          (terminalR0Projection L n (r : CanonicalFreeLie L))) +
          (r : CanonicalFreeLie L) := by abel
  change canonicalFreeLieEvaluation L
        (terminalP0Free L n
          (terminalR0Projection L n (r : CanonicalFreeLie L)).1) +
      canonicalFreeLieEvaluation L
        (((terminalR0Projection L n (r : CanonicalFreeLie L)).2 :
          TerminalQ0 L n) : CanonicalFreeLie L) ∈
    lowerCentralSeries ℤ L n
  rw [← map_add]
  rw [show terminalP0Free L n
        (terminalR0Projection L n (r : CanonicalFreeLie L)).1 +
      (((terminalR0Projection L n (r : CanonicalFreeLie L)).2 :
        TerminalQ0 L n) : CanonicalFreeLie L) =
      terminalR0Free L n
        (terminalR0Projection L n (r : CanonicalFreeLie L)) by rfl]
  rw [hneg, map_add, map_neg, hr, add_zero]
  exact (lowerCentralSeries ℤ L n).neg_mem hremEval

private def terminalRelationR1
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (r : CanonicalLieRelationsIdeal L) : TerminalR1 L n :=
  (terminalBoundaryEquivKernel L n hn).symm
    ⟨terminalR0Projection L n (r : CanonicalFreeLie L),
      terminalRelationProjection_mem_ker L n hn r⟩

@[simp] private theorem terminalBoundary_terminalRelationR1
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (r : CanonicalLieRelationsIdeal L) :
    terminalBoundary L n hn (terminalRelationR1 L n hn r) =
      terminalR0Projection L n (r : CanonicalFreeLie L) := by
  have h := (terminalBoundaryEquivKernel L n hn).apply_symm_apply
    ⟨terminalR0Projection L n (r : CanonicalFreeLie L),
      terminalRelationProjection_mem_ker L n hn r⟩
  exact congrArg (fun z : (terminalR0ToW L n).ker ↦
    (z.1 : TerminalR0 L n)) h

private def terminalFactorR0
    (L : Type u) [LieRing L] [Finite L]
    (n N : ℕ) (x : TruncatedBasisIndex L N) : TerminalR0 L n :=
  terminalR0Projection L n (homogeneousBasisLift L x)

private theorem terminalFactorR0_eq_zero_of_weight_gt
    (L : Type u) [LieRing L] [Finite L]
    (n N : ℕ) (x : TruncatedBasisIndex L N)
    (hx : n < truncatedBasisWeight L x) :
    terminalFactorR0 L n N x = 0 := by
  apply Prod.ext
  · funext s
    apply Subtype.ext
    change freeLieLengthComponent L (s.1 + 1) (homogeneousBasisLift L x) = 0
    apply freeLieLengthComponent_eq_zero_of_mem_lieHigh L
      (freeLieExact_mem_lieHigh L
        (freeLieExactBasis L (truncatedBasisWeight L x) x.2))
    have hs := s.2
    omega
  · apply Subtype.ext
    change freeLieLengthComponent L n (homogeneousBasisLift L x) = 0
    apply freeLieLengthComponent_eq_zero_of_mem_lieHigh L
      (freeLieExact_mem_lieHigh L
        (freeLieExactBasis L (truncatedBasisWeight L x) x.2))
    omega

@[simp] private theorem terminalR0ProjectionTruncated_basis
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (2 * n)) :
    terminalR0ProjectionTruncated L n hn
        (truncatedHomogeneousBasis L (2 * n) i) =
      terminalFactorR0 L n (2 * n) i := by
  rw [truncatedHomogeneousBasis_apply]
  rfl

private def terminalPP
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i j : TruncatedBasisIndex L (n - 1)) : ℤ := by
  classical
  let P := terminalPSmithSorted L n hn
  exact (collectRowLedger L (2 * n) w.initialRows).sum fun row c ↦
    match row.left with
    | [x] => c * P.relationBasis.repr
        (terminalRelationR1 L n hn row.relation).1 i *
          P.ambientBasis.repr (terminalFactorR0 L n (2 * n) x).1 j
    | _ => 0

private def terminalPQ
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i : TruncatedBasisIndex L (n - 1))
    (k : FreeLieExactBasisIndex L n) : ℤ := by
  classical
  let P := terminalPSmithSorted L n hn
  let Q := terminalQSmith L n
  exact (collectRowLedger L (2 * n) w.initialRows).sum fun row c ↦
    match row.left with
    | [x] => c * P.relationBasis.repr
        (terminalRelationR1 L n hn row.relation).1 i *
          Q.ambientBasis.repr (terminalFactorR0 L n (2 * n) x).2 k
    | _ => 0

private def terminalQP
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (k : FreeLieExactBasisIndex L n)
    (i : TruncatedBasisIndex L (n - 1)) : ℤ := by
  classical
  let P := terminalPSmithSorted L n hn
  let Q := terminalQSmith L n
  exact (collectRowLedger L (2 * n) w.initialRows).sum fun row c ↦
    match row.left with
    | [x] => c * Q.relationBasis.repr
        (terminalRelationR1 L n hn row.relation).2 k *
          P.ambientBasis.repr (terminalFactorR0 L n (2 * n) x).1 i
    | _ => 0

private def terminalQQ
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (k l : FreeLieExactBasisIndex L n) : ℤ := by
  classical
  let Q := terminalQSmith L n
  exact (collectRowLedger L (2 * n) w.initialRows).sum fun row c ↦
    match row.left with
    | [x] => c * Q.relationBasis.repr
        (terminalRelationR1 L n hn row.relation).2 k *
          Q.ambientBasis.repr (terminalFactorR0 L n (2 * n) x).2 l
    | _ => 0

private def terminalCollectedExpression
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 1 ≤ n)
    (w : GoverningWitness n L a) :
    (terminalData R hn).CollectedExpression where
  u := fun i j ↦ -terminalPP hn w j i
  v := terminalPQ hn w
  v' := fun i k ↦ terminalQP hn w k i
  t := 0
  sY := fun k l ↦ if k ≤ l then terminalQQ hn w k l else 0
  Ys := fun k l ↦ if k < l then terminalQQ hn w l k else 0

private abbrev Occurrence (P : Type u) := List ℕ × P

/-- One labelled use of the collector's chosen rewrite. -/
private structure RewriteCell (C : FiniteTaggedCollector P A) where
  path : List ℕ
  coefficient : ℤ
  input : P
  output : List (ℤ × P)
  expansion_eq : C.expansion input = some output

/-- Boundary of one rewrite cell in the free abelian group on labelled occurrences. -/
private def RewriteCell.boundary (C : FiniteTaggedCollector P A)
    (cell : RewriteCell C) : Occurrence P →₀ ℤ := by
  classical
  exact
    Finsupp.single (cell.path, cell.input) cell.coefficient -
      (List.ofFn fun i : Fin cell.output.length ↦
        Finsupp.single
          (i.1 :: cell.path, (cell.output.get i).2)
          (cell.coefficient * (cell.output.get i).1)).sum

/-- One recursion layer of the flattened, provenance-preserving rewrite trace. -/
private def traceStep (C : FiniteTaggedCollector P A) (p : P)
    (rec : ∀ q, C.relation q p → List ℕ → ℤ → List (RewriteCell C))
    (path : List ℕ) (coefficient : ℤ) : List (RewriteCell C) :=
  match h : C.expansion p with
  | none => []
  | some qs =>
      { path := path
        coefficient := coefficient
        input := p
        output := qs
        expansion_eq := h } ::
        (List.ofFn fun i : Fin qs.length ↦
          rec (qs.get i).2 (C.decreases h (qs.get i) (List.get_mem qs i))
            (i.1 :: path) (coefficient * (qs.get i).1)).flatten

/-- The flattened finite rewrite tree, with a distinct path label on every occurrence. -/
private def rewriteTrace (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ) : List (RewriteCell C) :=
  C.wellFounded.fix (fun p rec ↦ traceStep C p rec) p path coefficient

/-- The signed terminal frontier of the same labelled rewrite tree. -/
private def frontierStep (C : FiniteTaggedCollector P A) (p : P)
    (rec : ∀ q, C.relation q p → List ℕ → ℤ → Occurrence P →₀ ℤ)
    (path : List ℕ) (coefficient : ℤ) : Occurrence P →₀ ℤ := by
  classical
  exact match h : C.expansion p with
  | none => Finsupp.single (path, p) coefficient
  | some qs =>
      (List.ofFn fun i : Fin qs.length ↦
        rec (qs.get i).2 (C.decreases h (qs.get i) (List.get_mem qs i))
          (i.1 :: path) (coefficient * (qs.get i).1)).sum

private def rewriteFrontier (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ) : Occurrence P →₀ ℤ :=
  C.wellFounded.fix (fun p rec ↦ frontierStep C p rec) p path coefficient

private def traceBoundary (C : FiniteTaggedCollector P A)
    (cells : List (RewriteCell C)) : Occurrence P →₀ ℤ :=
  (cells.map fun cell ↦ cell.boundary C).sum

/-- Forget occurrence paths, retaining the packet and its total coefficient. -/
private def forgetPaths : (Occurrence P →₀ ℤ) →ₗ[ℤ] (P →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Prod.snd

/-- Forgetting provenance from the labelled frontier recovers the ordinary normal form. -/
private theorem forgetPaths_rewriteFrontier (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ) :
    forgetPaths (rewriteFrontier C p path coefficient) =
      coefficient • C.normalForm p := by
  induction p using C.wellFounded.induction generalizing path coefficient with
  | h p ih =>
      rw [rewriteFrontier, C.wellFounded.fix_eq,
        FiniteTaggedCollector.normalForm, C.wellFounded.fix_eq]
      change
        forgetPaths
          (match hx : C.expansion p with
          | none => Finsupp.single (path, p) coefficient
          | some qs =>
              (List.ofFn fun i : Fin qs.length ↦
                rewriteFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1)).sum) =
          coefficient •
            (match hx : C.expansion p with
            | none => Finsupp.single p 1
            | some qs =>
                (qs.attach.map fun q : {x // x ∈ qs} ↦
                  q.1.1 • C.normalForm q.1.2).sum)
      split
      · simp [forgetPaths, Finsupp.lmapDomain_apply]
      · rename_i qs hexpand
        rw [map_list_sum]
        have hchildren :
            (List.ofFn fun i : Fin qs.length ↦
              forgetPaths
                (rewriteFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1))) =
              List.ofFn fun i : Fin qs.length ↦
                (coefficient * (qs.get i).1) • C.normalForm (qs.get i).2 := by
          apply congrArg List.ofFn
          funext i
          exact ih (qs.get i).2
            (C.decreases hexpand (qs.get i) (List.get_mem qs i))
            (i.1 :: path) (coefficient * (qs.get i).1)
        rw [List.map_ofFn]
        change
          (List.ofFn fun i : Fin qs.length ↦
            forgetPaths
              (rewriteFrontier C (qs.get i).2 (i.1 :: path)
                (coefficient * (qs.get i).1))).sum = _
        rw [hchildren]
        have hattach :
            (qs.attach.map fun q : {x // x ∈ qs} ↦
                q.1.1 • C.normalForm q.1.2).sum =
              (qs.map fun q ↦ q.1 • C.normalForm q.2).sum :=
          congrArg List.sum
            (List.attach_map_val
              (l := qs) (f := fun q ↦ q.1 • C.normalForm q.2))
        rw [hattach, List.smul_sum]
        apply congrArg List.sum
        rw [List.map_map]
        calc
          List.ofFn (fun i : Fin qs.length ↦
              (coefficient * (qs.get i).1) • C.normalForm (qs.get i).2) =
              List.ofFn (fun i : Fin qs.length ↦
                coefficient • ((qs.get i).1 • C.normalForm (qs.get i).2)) := by
            apply congrArg List.ofFn
            funext i
            rw [mul_smul]
          _ = qs.map (fun q ↦ coefficient • (q.1 • C.normalForm q.2)) := by
            calc
              List.ofFn (fun i : Fin qs.length ↦
                  coefficient • ((qs.get i).1 • C.normalForm (qs.get i).2)) =
                  (List.ofFn qs.get).map
                    (fun q ↦ coefficient • (q.1 • C.normalForm q.2)) := by
                rw [List.map_ofFn]
                rfl
              _ = qs.map (fun q ↦ coefficient • (q.1 • C.normalForm q.2)) :=
                congrArg (List.map
                  (fun q ↦ coefficient • (q.1 • C.normalForm q.2)))
                  (List.ofFn_get qs)

/-- The labelled frontier therefore has the already-proved normal-form evaluation. -/
private theorem evaluate_rewriteFrontier (C : FiniteTaggedCollector P A) (p : P) :
    C.evaluate (forgetPaths (rewriteFrontier C p [] 1)) = C.value p := by
  rw [forgetPaths_rewriteFrontier, one_smul, C.evaluate_normalForm]

/--
The prefix-ledger identity.  Its proof is the same well-founded induction as normalization:
each nonterminal frontier occurrence is replaced by precisely its signed, path-labelled
children.  No confluence or critical-pair statement is involved.
-/
private theorem prefixLedgerAt (C : FiniteTaggedCollector P A) (p : P)
    (path : List ℕ) (coefficient : ℤ) :
    Finsupp.single (path, p) coefficient -
        rewriteFrontier C p path coefficient =
      traceBoundary C (rewriteTrace C p path coefficient) := by
  induction p using C.wellFounded.induction generalizing path coefficient with
  | h p ih =>
      rw [rewriteTrace, C.wellFounded.fix_eq,
        rewriteFrontier, C.wellFounded.fix_eq]
      unfold traceStep frontierStep
      split
      · simp [traceBoundary]
      · rename_i qs hexpand
        let roots : List (Occurrence P →₀ ℤ) :=
          List.ofFn fun i : Fin qs.length ↦
            Finsupp.single (i.1 :: path, (qs.get i).2)
              (coefficient * (qs.get i).1)
        let fronts : List (Occurrence P →₀ ℤ) :=
          List.ofFn fun i : Fin qs.length ↦
            rewriteFrontier C (qs.get i).2 (i.1 :: path)
              (coefficient * (qs.get i).1)
        let traces : List (List (RewriteCell C)) :=
          List.ofFn fun i : Fin qs.length ↦
            rewriteTrace C (qs.get i).2 (i.1 :: path)
              (coefficient * (qs.get i).1)
        have hchildren :
            (List.ofFn fun i : Fin qs.length ↦
              Finsupp.single (i.1 :: path, (qs.get i).2)
                    (coefficient * (qs.get i).1) -
                rewriteFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1)).sum =
              (traces.map fun cells ↦ traceBoundary C cells).sum := by
          dsimp only [traces]
          rw [List.map_ofFn]
          apply congrArg List.sum
          apply congrArg List.ofFn
          funext i
          simpa [Function.comp_def] using
            ih (qs.get i).2
              (C.decreases hexpand (qs.get i) (List.get_mem qs i))
              (i.1 :: path) (coefficient * (qs.get i).1)
        have sum_ofFn_sub : ∀ (n : ℕ)
            (r f : Fin n → Occurrence P →₀ ℤ),
            (List.ofFn fun i ↦ r i - f i).sum =
              (List.ofFn r).sum - (List.ofFn f).sum := by
          intro n
          induction n with
          | zero =>
              intro r f
              simp
          | succ n ihN =>
              intro r f
              rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
              simp only [List.sum_cons]
              rw [ihN]
              abel
        have hsumDiff :
            (List.ofFn fun i : Fin qs.length ↦
              Finsupp.single (i.1 :: path, (qs.get i).2)
                    (coefficient * (qs.get i).1) -
                rewriteFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1)).sum =
              roots.sum - fronts.sum := by
          exact sum_ofFn_sub qs.length _ _
        change
          Finsupp.single (path, p) coefficient - fronts.sum =
            (Finsupp.single (path, p) coefficient - roots.sum) +
              traceBoundary C traces.flatten
        rw [traceBoundary, List.map_flatten, List.sum_flatten]
        rw [List.map_map]
        change
          Finsupp.single (path, p) coefficient - fronts.sum =
            (Finsupp.single (path, p) coefficient - roots.sum) +
              (traces.map fun cells ↦ traceBoundary C cells).sum
        rw [← hchildren]
        rw [hsumDiff]
        abel

/-! ## The closed square attached to the governing relation

The preceding trace construction is generic.  We now instantiate it with the single
full-relation collector above.  In contrast with the earlier two-stage bookkeeping, the initial
packet below puts the mark into the original relation-left word, so every subsequent transfer,
homogeneous edge, and ordinary PBW interchange belongs to one rewrite tree.
-/

private def squarePacketsOfMultiplier
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (r : CanonicalLieRelationsIdeal L)
    (z : UEA ℤ (TruncatedFreeLie L (2 * n))) : SquarePacket L n →₀ ℤ :=
  ((truncatedPBWLinearEquiv L (2 * n)).symm z).sum fun e c ↦
    Finsupp.single
      (.marked r .hole ⟨2 * n, by omega⟩ [] (exponentWord L e)
        (exponentWord L e).length) c

private theorem evaluate_squarePacketsOfMultiplier
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (r : CanonicalLieRelationsIdeal L)
    (z : UEA ℤ (TruncatedFreeLie L (2 * n))) :
    (squarePacketCollector L n).evaluate
        (squarePacketsOfMultiplier L n r z) =
      UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk L (2 * n) (r : CanonicalFreeLie L)) * z := by
  classical
  unfold squarePacketsOfMultiplier
  rw [map_finsuppSum]
  let p := (truncatedPBWLinearEquiv L (2 * n)).symm z
  calc
    p.sum (fun e c ↦
        (squarePacketCollector L n).evaluate
          (Finsupp.single
            (.marked r .hole ⟨2 * n, by omega⟩ [] (exponentWord L e)
              (exponentWord L e).length) c)) =
      p.sum (fun e c ↦ c •
        (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedFreeLieMk L (2 * n) (r : CanonicalFreeLie L)) *
          orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
            (TruncatedBasisIndex L (2 * n))
              (truncatedHomogeneousBasis L (2 * n)) e)) := by
        apply Finsupp.sum_congr
        intro e he
        rw [FiniteTaggedCollector.evaluate_single]
        simp only [squarePacketCollector, SquarePacket.value,
          basisWord_nil, one_mul, RelationContext.applyFree]
        rw [truncated_markedPrefixFree_top, basisWord_exponentWord]
    _ = UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk L (2 * n) (r : CanonicalFreeLie L)) *
        (truncatedPBWLinearEquiv L (2 * n)) p := by
          let ir := UniversalEnvelopingAlgebra.ι ℤ
            (truncatedFreeLieMk L (2 * n) (r : CanonicalFreeLie L))
          calc
            p.sum (fun e c ↦ c •
                (ir * orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
                  (TruncatedBasisIndex L (2 * n))
                    (truncatedHomogeneousBasis L (2 * n)) e)) =
              ir * p.sum (fun e c ↦ c •
                orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
                  (TruncatedBasisIndex L (2 * n))
                    (truncatedHomogeneousBasis L (2 * n)) e) := by
                rw [Finsupp.mul_sum]
                apply Finsupp.sum_congr
                intro e he
                exact (mul_smul_comm (p e) ir
                  (orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
                    (TruncatedBasisIndex L (2 * n))
                      (truncatedHomogeneousBasis L (2 * n)) e)).symm
            _ = ir * (truncatedPBWLinearEquiv L (2 * n)) p := by rfl
    _ = _ := by rw [LinearEquiv.apply_symm_apply]

private def GoverningWitness.squareInitialPackets
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : SquarePacket L n →₀ ℤ :=
  w.relationWords.sum fun p c ↦ c •
    squarePacketsOfMultiplier L n p.1
      (word ℤ (TruncatedFreeLie L (2 * n))
        (p.2.map fun x ↦
          truncatedFreeLieMk L (2 * n) (FreeLieAlgebra.of ℤ x)))

private theorem GoverningWitness.evaluate_squareInitialPackets
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (squarePacketCollector L n).evaluate w.squareInitialPackets =
      w.relationSide := by
  classical
  unfold GoverningWitness.squareInitialPackets GoverningWitness.relationSide
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, evaluate_squarePacketsOfMultiplier]

private def GoverningWitness.squareFrontier
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : SquarePacket L n →₀ ℤ :=
  w.squareInitialPackets.sum fun p c ↦
    c • (squarePacketCollector L n).normalForm p

private theorem GoverningWitness.evaluate_squareFrontier
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (squarePacketCollector L n).evaluate w.squareFrontier =
      w.relationSide := by
  classical
  unfold GoverningWitness.squareFrontier
  rw [map_finsuppSum]
  calc
    w.squareInitialPackets.sum (fun p c ↦
        (squarePacketCollector L n).evaluate
          (c • (squarePacketCollector L n).normalForm p)) =
      w.squareInitialPackets.sum (fun p c ↦
        c • (squarePacketCollector L n).value p) := by
          apply Finsupp.sum_congr
          intro p hp
          rw [map_zsmul, FiniteTaggedCollector.evaluate_normalForm]
    _ = (squarePacketCollector L n).evaluate w.squareInitialPackets := rfl
    _ = w.relationSide := w.evaluate_squareInitialPackets

/-! The one-factor projection is defined once from the ordered PBW coordinates.  It is the
literal projection onto the copy of the Lie ring inside its PBW module, not a Dynkin map and
does not divide by a factorial. -/

private def pbwOneFactorProjection
    (X : Type u) [LieRing X] [Finite X] (N : ℕ) :
    UEA ℤ (TruncatedFreeLie X N) →ₗ[ℤ] TruncatedFreeLie X N where
  toFun z := ∑ i : TruncatedBasisIndex X N,
    pbwCoeff X N z (Finsupp.single i 1) •
      truncatedHomogeneousBasis X N i
  map_add' x y := by
    simp only [pbwCoeff, LinearEquiv.map_add, MvPolynomial.coeff_add,
      add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul]
    congr 1
    unfold pbwCoeff
    rw [LinearEquiv.map_smul]
    simpa only [smul_eq_mul] using
      (MvPolynomial.coeff_smul (Finsupp.single i 1) c
        ((truncatedPBWLinearEquiv X N).symm x))

private theorem truncatedHomogeneousBasis_repr_pbwOneFactorProjection
    (X : Type u) [LieRing X] [Finite X] (N : ℕ)
    (z : UEA ℤ (TruncatedFreeLie X N))
    (i : TruncatedBasisIndex X N) :
    (truncatedHomogeneousBasis X N).repr
        (pbwOneFactorProjection X N z) i =
      pbwCoeff X N z (Finsupp.single i 1) := by
  classical
  let b := truncatedHomogeneousBasis X N
  change b.repr (∑ j : TruncatedBasisIndex X N,
      pbwCoeff X N z (Finsupp.single j 1) • b j) i = _
  rw [map_sum]
  simp only [map_zsmul, b.repr_self]
  simp [Finsupp.smul_apply, Finsupp.single_apply]

private theorem pbwOneFactorProjection_iota
    (X : Type u) [LieRing X] [Finite X] (N : ℕ)
    (x : TruncatedFreeLie X N) :
    pbwOneFactorProjection X N (UniversalEnvelopingAlgebra.ι ℤ x) = x := by
  let b := truncatedHomogeneousBasis X N
  have hinverse :
      (truncatedPBWLinearEquiv X N).symm
          (UniversalEnvelopingAlgebra.ι ℤ x) =
        basisPolynomial ℤ (TruncatedFreeLie X N)
          (TruncatedBasisIndex X N) b x := by
    apply (truncatedPBWLinearEquiv X N).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (orderedPBWMap_basisPolynomial ℤ (TruncatedFreeLie X N)
      (TruncatedBasisIndex X N) b x).symm
  apply b.ext_elem
  intro i
  rw [show b.repr (pbwOneFactorProjection X N
      (UniversalEnvelopingAlgebra.ι ℤ x)) i =
      pbwCoeff X N (UniversalEnvelopingAlgebra.ι ℤ x)
        (Finsupp.single i 1) from
          truncatedHomogeneousBasis_repr_pbwOneFactorProjection X N _ i]
  unfold pbwCoeff
  rw [hinverse]
  unfold basisPolynomial
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  classical
  change MvPolynomial.coeff (Finsupp.single i 1)
      ((b.repr x).sum (fun j c ↦ c • MvPolynomial.X j)) = b.repr x i
  unfold Finsupp.sum
  rw [MvPolynomial.coeff_sum]
  have hcoefficient (j : TruncatedBasisIndex X N) :
      MvPolynomial.coeff (Finsupp.single i 1)
          ((b.repr x j) • MvPolynomial.X j) =
        if j = i then b.repr x j else 0 := by
    change (MvPolynomial.coeffAddMonoidHom (R := ℤ)
      (Finsupp.single i 1)) ((b.repr x j) • MvPolynomial.X j) = _
    rw [(MvPolynomial.coeffAddMonoidHom (R := ℤ)
      (Finsupp.single i 1)).map_zsmul]
    change (b.repr x j) *
      MvPolynomial.coeff (Finsupp.single i 1) (MvPolynomial.X j) = _
    rw [MvPolynomial.coeff_X']
    by_cases hji : j = i
    · subst j
      simp
    ·
      have hsingle : Finsupp.single j (1 : ℕ) ≠ Finsupp.single i 1 := by
        intro h
        apply hji
        apply Finsupp.single_left_injective (M := ℕ) one_ne_zero h
      simp [hsingle, hji]
  simp_rw [hcoefficient]
  by_cases hi : i ∈ (b.repr x).support
  · simp [hi]
  · have hzero : b.repr x i = 0 := by
      by_contra hne
      exact hi (Finsupp.mem_support_iff.mpr hne)
    simp [hi, hzero]

private def truncatedExactComponent
    (X : Type u) [Finite X] (N k : ℕ) (hk : k ≤ N) :
    TruncatedFreeLie X N →ₗ[ℤ] freeLieExact X k :=
  (lowerCentralSeries ℤ (CanonicalFreeLie X) N).toSubmodule.liftQ
    { toFun := fun f ↦
        ⟨freeLieLengthComponent X k f,
          freeLieLengthComponent_mem_exact X k f⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add (freeLieLengthComponent X k) x y
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact map_smul (freeLieLengthComponent X k) c x }
    (by
      intro f hf
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change freeLieLengthComponent X k f = 0
      have hfhigh : f ∈ FreeLieDimension.lieHigh X (N + 1) := by
        rw [FreeLieDimension.lieHigh_eq_lowerCentralSeries X N]
        exact hf
      apply freeLieLengthComponent_eq_zero_of_mem_lieHigh X
      · exact hfhigh
      · omega)

@[simp] private theorem truncatedExactComponent_mk
    (X : Type u) [Finite X] (N k : ℕ) (hk : k ≤ N)
    (f : CanonicalFreeLie X) :
    truncatedExactComponent X N k hk (truncatedFreeLieMk X N f) =
      ⟨freeLieLengthComponent X k f,
        freeLieLengthComponent_mem_exact X k f⟩ := rfl

private def topComponentCoordinate
    {n : ℕ} {L : Type u} [LieRing L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (x : TruncatedFreeLie L (2 * n)) : ZMod (2 ^ R.topExponent) := by
  letI := R.finite_inst
  let z := truncatedExactComponent L (2 * n) (n + 1) (by omega) x
  have hz : canonicalFreeLieEvaluation L (z : CanonicalFreeLie L) ∈
      lowerCentralSeries ℤ L n := by
    have h := canonicalEvaluation_mem_lowerCentralSeries L
      (freeLieExact_mem_lieHigh L z)
    simpa using h
  exact R.topEquiv ⟨canonicalFreeLieEvaluation L
    (z : CanonicalFreeLie L), hz⟩

private def primitiveTopRead
    {n : ℕ} {L : Type u} [LieRing L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (z : UEA ℤ (TruncatedFreeLie L (2 * n))) : ZMod (2 ^ R.topExponent) := by
  letI := R.finite_inst
  exact topComponentCoordinate R hn (pbwOneFactorProjection L (2 * n) z)

private theorem primitiveTopRead_relationSide
    (n : ℕ) (hn : 1 ≤ n)
    (L : Type u) [LieRing L] [Finite L]
    (R : ReducedData n L) (a : L)
    (w : GoverningWitness n L a)
    (hgoverning : ∀ e : TruncatedBasisIndex L (2 * n) →₀ ℕ,
      totalWeight L e ≤ 2 * n →
        pbwCoeff L (2 * n) w.relationSide e =
          pbwCoeff L (2 * n)
            (UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk L (2 * n)
                (w.zTilde : CanonicalFreeLie L))) e) :
    primitiveTopRead R hn w.relationSide =
      R.topEquiv ⟨a, by
        rw [← w.evaluates]
        have h := canonicalEvaluation_mem_lowerCentralSeries L
          (freeLieExact_mem_lieHigh L w.zTilde)
        simpa using h⟩ := by
  have hprojection : pbwOneFactorProjection L (2 * n) w.relationSide =
      truncatedFreeLieMk L (2 * n) (w.zTilde : CanonicalFreeLie L) := by
    let b := truncatedHomogeneousBasis L (2 * n)
    apply b.ext_elem
    intro i
    rw [show b.repr (pbwOneFactorProjection L (2 * n) w.relationSide) i =
        pbwCoeff L (2 * n) w.relationSide (Finsupp.single i 1) from
      truncatedHomogeneousBasis_repr_pbwOneFactorProjection L (2 * n) _ i]
    rw [hgoverning (Finsupp.single i 1) (by
      simp [totalWeight, truncatedBasisWeight])]
    rw [← truncatedHomogeneousBasis_repr_pbwOneFactorProjection]
    rw [pbwOneFactorProjection_iota]
  change topComponentCoordinate R hn
      (pbwOneFactorProjection L (2 * n) w.relationSide) = _
  rw [hprojection]
  unfold topComponentCoordinate
  apply congrArg R.topEquiv
  apply Subtype.ext
  change canonicalFreeLieEvaluation L
      ((truncatedExactComponent L (2 * n) (n + 1) _
        (truncatedFreeLieMk L (2 * n)
          (w.zTilde : CanonicalFreeLie L)) : freeLieExact L (n + 1)) :
            CanonicalFreeLie L) = a
  rw [truncatedExactComponent_mk]
  change canonicalFreeLieEvaluation L
      (freeLieLengthComponent L (n + 1)
        (w.zTilde : CanonicalFreeLie L)) = a
  calc
    _ = canonicalFreeLieEvaluation L (w.zTilde : CanonicalFreeLie L) :=
      congrArg (canonicalFreeLieEvaluation L)
        (freeLieLengthComponent_coe_exact L (n + 1) w.zTilde)
    _ = a := w.evaluates

private theorem truncatedHomogeneousBasis_repr_mk_exact_eq_zero_of_weight_ne
    (L : Type u) [Finite L] (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N)
    (z : freeLieExact L k) (i : TruncatedBasisIndex L N)
    (hi : truncatedBasisWeight L i ≠ k) :
    (truncatedHomogeneousBasis L N).repr
        (truncatedFreeLieMk L N (z : CanonicalFreeLie L)) i = 0 := by
  classical
  let c := (freeLieExactBasis L k).repr z
  have hsum : c.sum (fun j a ↦ a •
      truncatedHomogeneousBasis L N (contextBasisIndexOf L hk hkN j)) =
      truncatedFreeLieMk L N (z : CanonicalFreeLie L) := by
    simp_rw [contextBasisIndexOf_value]
    calc
      c.sum (fun j a ↦ a • truncatedFreeLieMk L N
          (((freeLieExactBasis L k j : freeLieExact L k)) :
            CanonicalFreeLie L)) =
        truncatedFreeLieMk L N
          (c.sum (fun j a ↦ a •
            (((freeLieExactBasis L k j : freeLieExact L k)) :
              CanonicalFreeLie L))) := by
                rw [map_finsuppSum]
                apply Finsupp.sum_congr
                intro j hj
                rw [map_zsmul]
      _ = _ := by
        apply congrArg (truncatedFreeLieMk L N)
        calc
          c.sum (fun j a ↦ a •
              (((freeLieExactBasis L k j : freeLieExact L k)) :
                CanonicalFreeLie L)) =
            (freeLieExact L k).subtype
              (c.sum (fun j a ↦ a • freeLieExactBasis L k j)) := by
                rw [map_finsuppSum]
                apply Finsupp.sum_congr
                intro j hj
                rw [map_zsmul]
                rfl
          _ = (z : CanonicalFreeLie L) :=
            congrArg Subtype.val
              ((freeLieExactBasis L k).linearCombination_repr z)
  rw [← hsum, map_finsuppSum, Finsupp.sum_apply]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [map_zsmul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs with hij
  · subst i
    exact (hi (contextBasisIndexOf_weight L hk hkN j)).elim
  · simp

private theorem contextPrefix_repr_support_le_active
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (r : CanonicalLieRelationsIdeal L)
    (c : RelationContext L (2 * n)) (k : ℕ)
    (hactive : k + c.weight L ≤ 2 * n) :
    ∀ i ∈ (truncatedHomogeneousBasis L (2 * n)).repr
        (truncatedFreeLieMk L (2 * n)
          (c.applyFree L (markedPrefixFree L k r))) |>.support,
      truncatedBasisWeight L i ≤ k + c.weight L := by
  induction k with
  | zero =>
      intro i hi
      have hczero : c.applyFree L 0 = 0 := (c.linearMap L).map_zero
      simp [markedPrefixFree, hczero] at hi
  | succ k ih =>
      intro i hi
      let b := truncatedHomogeneousBasis L (2 * n)
      let previous := truncatedFreeLieMk L (2 * n)
        (c.applyFree L (markedPrefixFree L k r))
      let component := truncatedFreeLieMk L (2 * n)
        (contextComponentExact L c r (k + 1) : CanonicalFreeLie L)
      have hsplit : truncatedFreeLieMk L (2 * n)
          (c.applyFree L (markedPrefixFree L (k + 1) r)) =
          previous + component := by
        have hp := congrArg (c.linearMap L)
          (markedPrefixFree_step L (by omega : 0 < k + 1) r)
        rw [map_add] at hp
        change c.applyFree L (markedPrefixFree L (k + 1) r) =
          c.applyFree L (markedPrefixFree L k r) +
            (contextComponentExact L c r (k + 1) : CanonicalFreeLie L) at hp
        simpa [previous, component, map_add] using
          congrArg (truncatedFreeLieMk L (2 * n)) hp
      by_contra hnot
      have hiWeight : k + 1 + c.weight L < truncatedBasisWeight L i := by
        omega
      have hprevious : b.repr previous i = 0 := by
        by_contra hne
        have himem : i ∈ (b.repr previous).support :=
          Finsupp.mem_support_iff.mpr hne
        have hle := ih (by omega) i himem
        omega
      have hcomponent : b.repr component i = 0 := by
        apply truncatedHomogeneousBasis_repr_mk_exact_eq_zero_of_weight_ne
          L (2 * n) (k + 1 + c.weight L) (by omega) hactive
          (contextComponentExact L c r (k + 1)) i
        omega
      have hzero : b.repr
          (truncatedFreeLieMk L (2 * n)
            (c.applyFree L (markedPrefixFree L (k + 1) r))) i = 0 := by
        rw [hsplit, map_add, Finsupp.add_apply, hprevious, hcomponent,
          zero_add]
      exact Finsupp.mem_support_iff.mp hi hzero

/-
/-! The square trace below is used only to enumerate complete truncation-component families.
Each such family is immediately passed to the provenance-preserving aggregate collector; no
ordinary `SquarePacket.word` leaf is ever interpreted as a relation. -/

/-! The terminal chain is read at one and only one wall of the square: active Lie weight `n`
and one remaining ordinary factor.  The stored relation is the full contextual relation; the
mark is used only to recognize the wall and is never turned into a relation. -/

private def GoverningWitness.squareTrace
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    List (RewriteCell (squarePacketCollector L n)) := by
  classical
  exact w.squareInitialPackets.support.toList.flatMap fun p ↦
    rewriteTrace (squarePacketCollector L n) p [] (w.squareInitialPackets p)

/-!
`SquarePacket.word` is intentionally a lean semantic packet, so after an exact component has
been emitted it no longer carries its full-relation provenance.  The closed-square read must
therefore be made at the emitting truncation cell, not reconstructed from a later ordinary
leaf.  The following row is precisely that information and nothing more.
-/

private structure ComponentTraceRow
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) where
  coefficient : ℤ
  relation : CanonicalLieRelationsIdeal L
  context : RelationContext L (2 * n)
  mark : Fin (2 * n + 1)
  mark_pos : 0 < mark.1
  active_le : mark.1 + context.weight L ≤ 2 * n
  left : List (TruncatedBasisIndex L (2 * n))
  right : List (TruncatedBasisIndex L (2 * n))

private def ComponentTraceRow.value
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (row : ComponentTraceRow L n) :
    UEA ℤ (TruncatedFreeLie L (2 * n)) :=
  basisWord ℤ (TruncatedFreeLie L (2 * n))
      (TruncatedBasisIndex L (2 * n))
        (truncatedHomogeneousBasis L (2 * n)) row.left *
    UniversalEnvelopingAlgebra.ι ℤ
      (truncatedFreeLieMk L (2 * n)
        (contextComponentExact L row.context row.relation row.mark.1 :
          CanonicalFreeLie L)) *
    basisWord ℤ (TruncatedFreeLie L (2 * n))
      (TruncatedBasisIndex L (2 * n))
        (truncatedHomogeneousBasis L (2 * n)) row.right

private theorem componentSupportPackets_value
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (r : CanonicalLieRelationsIdeal L)
    (c : RelationContext L (2 * n))
    (k : Fin (2 * n + 1)) (hk : 0 < k.1)
    (hweight : k.1 + c.weight L ≤ 2 * n)
    (left right : List (TruncatedBasisIndex L (2 * n))) :
    ((markedSupportPackets (contextComponentCoefficients L c r k.1) fun i ↦
        SquarePacket.word
          (left ++ contextBasisIndexOf L (by omega) hweight i :: right)).map
        fun q ↦ q.1 • SquarePacket.value L n q.2).sum =
      (ComponentTraceRow.value L n
        { coefficient := 1
          relation := r
          context := c
          mark := k
          mark_pos := hk
          active_le := hweight
          left := left
          right := right }) := by
  classical
  let coeff := contextComponentCoefficients L c r k.1
  let lword := basisWord ℤ (TruncatedFreeLie L (2 * n))
    (TruncatedBasisIndex L (2 * n))
      (truncatedHomogeneousBasis L (2 * n)) left
  let rword := basisWord ℤ (TruncatedFreeLie L (2 * n))
    (TruncatedBasisIndex L (2 * n))
      (truncatedHomogeneousBasis L (2 * n)) right
  have hcomponent :
      coeff.sum (fun i z ↦ z •
        truncatedHomogeneousBasis L (2 * n)
          (contextBasisIndexOf L (by omega) hweight i)) =
        truncatedFreeLieMk L (2 * n)
          (contextComponentExact L c r k.1 : CanonicalFreeLie L) := by
    simp_rw [contextBasisIndexOf_value]
    calc
      coeff.sum (fun i z ↦ z •
          truncatedFreeLieMk L (2 * n)
            (((freeLieExactBasis L (k.1 + c.weight L) i :
              freeLieExact L (k.1 + c.weight L))) : CanonicalFreeLie L)) =
        truncatedFreeLieMk L (2 * n)
          (coeff.sum (fun i z ↦ z •
            (((freeLieExactBasis L (k.1 + c.weight L) i :
              freeLieExact L (k.1 + c.weight L))) : CanonicalFreeLie L))) := by
              rw [map_finsuppSum]
              apply Finsupp.sum_congr
              intro i hi
              rw [map_zsmul]
      _ = _ := congrArg (truncatedFreeLieMk L (2 * n))
        (contextComponentCoefficients_sum L c r k.1)
  rw [markedSupportPackets_value]
  change coeff.sum (fun i z ↦ z •
      basisWord ℤ (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n))
          (truncatedHomogeneousBasis L (2 * n))
            (left ++ contextBasisIndexOf L (by omega) hweight i :: right)) = _
  simp_rw [basisWord, List.map_append, List.map_cons, word_append, word_cons]
  change coeff.sum (fun i z ↦ z •
      (lword * UniversalEnvelopingAlgebra.ι ℤ
        (truncatedHomogeneousBasis L (2 * n)
          (contextBasisIndexOf L (by omega) hweight i)) * rword)) = _
  calc
    _ = lword * UniversalEnvelopingAlgebra.ι ℤ
        (coeff.sum (fun i z ↦ z •
          truncatedHomogeneousBasis L (2 * n)
            (contextBasisIndexOf L (by omega) hweight i))) * rword := by
          rw [map_finsuppSum, Finsupp.mul_sum, Finsupp.sum_mul]
          apply Finsupp.sum_congr
          intro i hi
          rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
          simp only [mul_assoc]
    _ = _ := by rw [hcomponent]; rfl

private def componentTraceRowOfCell
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (cell : RewriteCell (squarePacketCollector L n)) :
    Option (ComponentTraceRow L n) := by
  classical
  cases hinput : cell.input with
  | word _ => exact none
  | marked r c k left right fuel =>
      if hk : 0 < k.1 then
        if hweight : k.1 + c.weight L ≤ 2 * n then
          if htruncate :
              cell.output = squareTruncateExpansion L n r c k left right then
            exact some
              { coefficient := cell.coefficient
                relation := r
                context := c
                mark := k
                mark_pos := hk
                active_le := hweight
                left := left
                right := right }
          else exact none
        else exact none
      else exact none

private def GoverningWitness.componentTraceRows
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : List (ComponentTraceRow L n) :=
  w.squareTrace.filterMap (componentTraceRowOfCell L n)

private def squareWordValue
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    SquarePacket L n → UEA ℤ (TruncatedFreeLie L (2 * n))
  | .marked _ _ _ _ _ _ => 0
  | .word xs => SquarePacket.value L n (.word xs)

private def squareWordOccurrenceRead
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    (Occurrence (SquarePacket L n) →₀ ℤ) →ₗ[ℤ]
      UEA ℤ (TruncatedFreeLie L (2 * n)) :=
  Finsupp.linearCombination ℤ (fun o ↦ squareWordValue L n o.2)

@[simp] private theorem squareWordOccurrenceRead_single
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (o : Occurrence (SquarePacket L n)) (c : ℤ) :
    squareWordOccurrenceRead L n (Finsupp.single o c) =
      c • squareWordValue L n o.2 := by
  classical
  simp [squareWordOccurrenceRead]

private theorem squareWordOccurrenceRead_rewriteFrontier
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (p : SquarePacket L n) (path : List ℕ) (coefficient : ℤ) :
    squareWordOccurrenceRead L n
        (rewriteFrontier (squarePacketCollector L n) p path coefficient) =
      coefficient • SquarePacket.value L n p := by
  induction p using (squarePacketCollector L n).wellFounded.induction
      generalizing path coefficient with
  | h p ih =>
      rw [rewriteFrontier, (squarePacketCollector L n).wellFounded.fix_eq]
      unfold frontierStep
      split
      · rename_i hexpand
        cases p with
        | marked r c k left right fuel =>
            simp only [squarePacketCollector, squarePacketExpansion] at hexpand
            split at hexpand <;> contradiction
        | word xs =>
            simp [squareWordValue]
      · rename_i qs hexpand
        rw [map_list_sum]
        change
          (List.ofFn fun i : Fin qs.length ↦
            squareWordOccurrenceRead L n
              (rewriteFrontier (squarePacketCollector L n) (qs.get i).2
                (i.1 :: path) (coefficient * (qs.get i).1))).sum = _
        have hchildren :
            (List.ofFn fun i : Fin qs.length ↦
              squareWordOccurrenceRead L n
                (rewriteFrontier (squarePacketCollector L n) (qs.get i).2
                  (i.1 :: path) (coefficient * (qs.get i).1))) =
              List.ofFn fun i : Fin qs.length ↦
                (coefficient * (qs.get i).1) •
                  SquarePacket.value L n (qs.get i).2 := by
          apply congrArg List.ofFn
          funext i
          exact ih (qs.get i).2
            ((squarePacketCollector L n).decreases hexpand
              (qs.get i) (List.get_mem qs i))
            (i.1 :: path) (coefficient * (qs.get i).1)
        rw [hchildren]
        have hpreserves :=
          (squarePacketCollector L n).preserves hexpand
        rw [← hpreserves, List.smul_sum]
        apply congrArg List.sum
        rw [List.map_ofFn]
        apply congrArg List.ofFn
        funext i
        rw [mul_smul]

private theorem squareWordOccurrenceRead_cellBoundary
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (cell : RewriteCell (squarePacketCollector L n)) :
    squareWordOccurrenceRead L n
        (cell.boundary (squarePacketCollector L n)) =
      -((componentTraceRowOfCell L n cell).elim 0 fun row ↦
        row.coefficient • row.value L n) := by
  classical
  rcases cell with ⟨path, coefficient, input, output, hexpand⟩
  simp only [RewriteCell.boundary, map_sub,
    squareWordOccurrenceRead_single]
  cases input with
  | word xs =>
      simp only [componentTraceRowOfCell, squareWordValue, Option.elim_none,
        neg_zero]
      simp only [squarePacketCollector, squarePacketExpansion] at hexpand
      split at hexpand
      · contradiction
      · rename_i d hchosen
        split at hexpand
        · rename_i hweight
          rcases Option.some.inj hexpand with rfl
          simp only [List.length_cons, List.length_map, Finsupp.coe_neg,
            Pi.neg_apply]
          rw [List.sum_ofFn]
          simp only [Fin.sum_univ_two, List.get_cons_zero,
            List.get_cons_succ, List.get_eq_getElem, List.getElem_cons_succ]
          rw [← mul_smul]
          have hpres := squarePacketExpansion_preserves L n
            (p := SquarePacket.word xs)
            (qs := (1, SquarePacket.word (d.left ++ d.y :: d.x :: d.right)) ::
              markedSupportPackets (markedBracketCoefficients L d.x d.y hweight)
                (fun i ↦ SquarePacket.word (d.left ++ i :: d.right)))
            (by simp only [squarePacketExpansion, hchosen, hweight, ↓reduceIte])
          rw [List.ofFn_eq_map]
          simp only [squareWordValue]
          rw [← List.smul_sum]
          rw [hpres]
          abel
        · rcases Option.some.inj hexpand with rfl
          simp only [List.length_singleton, List.sum_ofFn, Fin.sum_univ_one,
            List.get_cons_zero, squareWordValue, one_mul, sub_self]
  | marked r c k left right fuel =>
      simp only [squareWordValue, zero_smul, zero_sub]
      simp only [squarePacketCollector, squarePacketExpansion] at hexpand
      split at hexpand
      · rcases Option.some.inj hexpand with rfl
        simp [componentTraceRowOfCell]
      · rename_i hk
        split at hexpand
        · rename_i hfuel
          rcases Option.some.inj hexpand with rfl
          unfold squareTruncateExpansion
          split
          · simp [componentTraceRowOfCell]
          · rename_i hk'
            split
            · rename_i hweight
              simp only [List.length_cons, List.length_map]
              rw [List.sum_ofFn, List.sum_cons]
              simp only [List.get_cons_zero, squareWordValue, zero_smul,
                zero_add]
              rw [← List.smul_sum]
              rw [componentSupportPackets_value L n r c k
                (Nat.pos_of_ne_zero hk') hweight left right]
              simp [componentTraceRowOfCell, hk', hweight]
            · simp [componentTraceRowOfCell, hk']
        · rename_i hfuel
          split at hexpand
          · rename_i x revLeft hleft
            split at hexpand
            · rcases Option.some.inj hexpand with rfl
              simp [componentTraceRowOfCell]
            · rename_i hx
              cases hright : right with
              | nil =>
                  subst right
                  rcases Option.some.inj hexpand with rfl
                  unfold squareTruncateExpansion
                  split
                  · simp [componentTraceRowOfCell]
                  · rename_i hk'
                    split
                    · rename_i hweight
                      simp only [List.length_cons, List.length_map]
                      rw [List.sum_ofFn, List.sum_cons]
                      simp only [List.get_cons_zero, squareWordValue, zero_smul,
                        zero_add]
                      rw [← List.smul_sum]
                      rw [componentSupportPackets_value L n r c k
                        (Nat.pos_of_ne_zero hk') hweight left []]
                      simp [componentTraceRowOfCell, hk', hweight]
                    · simp [componentTraceRowOfCell, hk']
              | cons y ys =>
                  subst right
                  split at hexpand
                  · rcases Option.some.inj hexpand with rfl
                    simp [componentTraceRowOfCell]
                  · rcases Option.some.inj hexpand with rfl
                    unfold squareTruncateExpansion
                    split
                    · simp [componentTraceRowOfCell]
                    · rename_i hk'
                      split
                      · rename_i hweight
                        simp only [List.length_cons, List.length_map]
                        rw [List.sum_ofFn, List.sum_cons]
                        simp only [List.get_cons_zero, squareWordValue,
                          zero_smul, zero_add]
                        rw [← List.smul_sum]
                        rw [componentSupportPackets_value L n r c k
                          (Nat.pos_of_ne_zero hk') hweight left (y :: ys)]
                        simp [componentTraceRowOfCell, hk', hweight]
                      · simp [componentTraceRowOfCell, hk']
          · rename_i hleft
            cases hright : right with
            | nil =>
                subst right
                rcases Option.some.inj hexpand with rfl
                unfold squareTruncateExpansion
                split
                · simp [componentTraceRowOfCell]
                · rename_i hk'
                  split
                  · rename_i hweight
                    simp only [List.length_cons, List.length_map]
                    rw [List.sum_ofFn, List.sum_cons]
                    simp only [List.get_cons_zero, squareWordValue, zero_smul,
                      zero_add]
                    rw [← List.smul_sum]
                    rw [componentSupportPackets_value L n r c k
                      (Nat.pos_of_ne_zero hk') hweight [] []]
                    simp [componentTraceRowOfCell, hk', hweight]
                  · simp [componentTraceRowOfCell, hk']
            | cons y ys =>
                subst right
                split at hexpand
                · rcases Option.some.inj hexpand with rfl
                  simp [componentTraceRowOfCell]
                · rcases Option.some.inj hexpand with rfl
                  unfold squareTruncateExpansion
                  split
                  · simp [componentTraceRowOfCell]
                  · rename_i hk'
                    split
                    · rename_i hweight
                      simp only [List.length_cons, List.length_map]
                      rw [List.sum_ofFn, List.sum_cons]
                      simp only [List.get_cons_zero, squareWordValue, zero_smul,
                        zero_add]
                      rw [← List.smul_sum]
                      rw [componentSupportPackets_value L n r c k
                        (Nat.pos_of_ne_zero hk') hweight [] (y :: ys)]
                      simp [componentTraceRowOfCell, hk', hweight]
                    · simp [componentTraceRowOfCell, hk']

private def componentTraceValue
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (cells : List (RewriteCell (squarePacketCollector L n))) :
    UEA ℤ (TruncatedFreeLie L (2 * n)) :=
  (cells.filterMap (componentTraceRowOfCell L n)).map
    (fun row ↦ row.coefficient • row.value L n) |>.sum

private theorem squareWordOccurrenceRead_traceBoundary
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (cells : List (RewriteCell (squarePacketCollector L n))) :
    squareWordOccurrenceRead L n
        (traceBoundary (squarePacketCollector L n) cells) =
      -componentTraceValue L n cells := by
  induction cells with
  | nil => simp [traceBoundary, componentTraceValue]
  | cons cell cells ih =>
      rw [traceBoundary]
      simp only [List.map_cons, List.sum_cons, map_add, ih]
      rw [squareWordOccurrenceRead_cellBoundary L n cell]
      unfold componentTraceValue
      simp only [List.filterMap_cons]
      cases hrow : componentTraceRowOfCell L n cell with
      | none => simp [hrow]
      | some row => simp [hrow]; abel

private theorem componentTraceValue_rewriteTrace_of_marked
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (r : CanonicalLieRelationsIdeal L)
    (c : RelationContext L (2 * n)) (k : Fin (2 * n + 1))
    (left right : List (TruncatedBasisIndex L (2 * n)))
    (fuel : ℕ) (path : List ℕ) (coefficient : ℤ) :
    componentTraceValue L n
        (rewriteTrace (squarePacketCollector L n)
          (.marked r c k left right fuel) path coefficient) =
      coefficient • SquarePacket.value L n
        (.marked r c k left right fuel) := by
  have hledger := prefixLedgerAt (squarePacketCollector L n)
    (.marked r c k left right fuel) path coefficient
  have hread := congrArg (squareWordOccurrenceRead L n) hledger
  rw [map_sub, squareWordOccurrenceRead_single,
    squareWordOccurrenceRead_rewriteFrontier,
    squareWordOccurrenceRead_traceBoundary] at hread
  simp only [squareWordValue, smul_zero, zero_sub] at hread
  exact neg_injective hread.symm

private theorem GoverningWitness.componentTraceValue_eq_relationSide
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    componentTraceValue L n w.squareTrace = w.relationSide := by
  classical
  unfold GoverningWitness.squareTrace componentTraceValue
  rw [List.filterMap_flatMap, List.map_flatMap, List.sum_flatten]
  change
    (w.squareInitialPackets.support.toList.map fun p ↦
      componentTraceValue L n
        (rewriteTrace (squarePacketCollector L n) p []
          (w.squareInitialPackets p))).sum = w.relationSide
  have hpMarked : ∀ p ∈ w.squareInitialPackets.support,
      ∃ r c k left right fuel,
        p = SquarePacket.marked r c k left right fuel := by
    intro p hp
    cases p with
    | marked r c k left right fuel => exact ⟨r, c, k, left, right, fuel, rfl⟩
    | word xs =>
        exfalso
        apply Finsupp.mem_support_iff.mp hp
        unfold GoverningWitness.squareInitialPackets
        rw [Finsupp.sum_apply]
        apply Finsupp.sum_eq_zero
        intro q hq
        rw [Finsupp.smul_apply]
        unfold squarePacketsOfMultiplier
        rw [Finsupp.sum_apply]
        apply Finsupp.sum_eq_zero
        intro e he
        simp
  rw [show (w.squareInitialPackets.support.toList.map fun p ↦
      componentTraceValue L n
        (rewriteTrace (squarePacketCollector L n) p []
          (w.squareInitialPackets p))) =
      w.squareInitialPackets.support.toList.map fun p ↦
        w.squareInitialPackets p • SquarePacket.value L n p by
    apply List.map_congr_left
    intro p hp
    have hp' : p ∈ w.squareInitialPackets.support := by simpa using hp
    obtain ⟨r, c, k, left, right, fuel, rfl⟩ := hpMarked p hp'
    exact componentTraceValue_rewriteTrace_of_marked L n
      r c k left right fuel [] _]
  rw [← Finsupp.sum]
  change (squarePacketCollector L n).evaluate w.squareInitialPackets = _
  exact w.evaluate_squareInitialPackets

private structure TerminalTraceRow
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) where
  coefficient : ℤ
  relation : CanonicalLieRelationsIdeal L
  factor : TruncatedBasisIndex L (2 * n)

private def terminalTraceRowOfCell
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (cell : RewriteCell (squarePacketCollector L n)) :
    Option (TerminalTraceRow L n) := by
  classical
  cases hinput : cell.input with
  | word xs => exact none
  | marked r c k left right fuel =>
      if hactive : k.1 + c.weight L = n ∧
          cell.output = squareTruncateExpansion L n r c k left right then
        exact match left, right with
        | [], [x] => some
            { coefficient := cell.coefficient
              relation := c.relation L r
              factor := x }
        | [x], [] => some
            { coefficient := cell.coefficient
              relation := c.relation L r
              factor := x }
        | _, _ => none
      else exact none

private def GoverningWitness.terminalTraceRows
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : List (TerminalTraceRow L n) :=
  w.squareTrace.filterMap (terminalTraceRowOfCell L n)

private abbrev GoverningWitness.TerminalTraceRowIndex
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) := Fin w.terminalTraceRows.length

private def GoverningWitness.terminalTraceRowAt
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) (t : w.TerminalTraceRowIndex) :
    TerminalTraceRow L n :=
  w.terminalTraceRows.get t

private def squareTerminalPP
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i j : TruncatedBasisIndex L (n - 1)) : ℤ := by
  classical
  let P := terminalPSmithSorted L n hn
  exact ∑ t : w.TerminalTraceRowIndex, let row := w.terminalTraceRowAt t
    row.coefficient * P.relationBasis.repr
        (terminalRelationR1 L n hn row.relation).1 i *
      P.ambientBasis.repr (terminalFactorR0 L n (2 * n) row.factor).1 j

private def squareTerminalPQ
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i : TruncatedBasisIndex L (n - 1))
    (k : FreeLieExactBasisIndex L n) : ℤ := by
  classical
  let P := terminalPSmithSorted L n hn
  let Q := terminalQSmith L n
  exact ∑ t : w.TerminalTraceRowIndex, let row := w.terminalTraceRowAt t
    row.coefficient * P.relationBasis.repr
        (terminalRelationR1 L n hn row.relation).1 i *
      Q.ambientBasis.repr (terminalFactorR0 L n (2 * n) row.factor).2 k

private def squareTerminalQP
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (k : FreeLieExactBasisIndex L n)
    (i : TruncatedBasisIndex L (n - 1)) : ℤ := by
  classical
  let P := terminalPSmithSorted L n hn
  let Q := terminalQSmith L n
  exact ∑ t : w.TerminalTraceRowIndex, let row := w.terminalTraceRowAt t
    row.coefficient * Q.relationBasis.repr
        (terminalRelationR1 L n hn row.relation).2 k *
      P.ambientBasis.repr (terminalFactorR0 L n (2 * n) row.factor).1 i

private def squareTerminalQQ
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (k l : FreeLieExactBasisIndex L n) : ℤ := by
  classical
  let Q := terminalQSmith L n
  exact ∑ t : w.TerminalTraceRowIndex, let row := w.terminalTraceRowAt t
    row.coefficient * Q.relationBasis.repr
        (terminalRelationR1 L n hn row.relation).2 k *
      Q.ambientBasis.repr (terminalFactorR0 L n (2 * n) row.factor).2 l

private def squareTerminalCollectedExpression
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 1 ≤ n)
    (w : GoverningWitness n L a) :
    (terminalData R hn).CollectedExpression where
  u := fun i j ↦ -squareTerminalPP hn w j i
  v := squareTerminalPQ hn w
  v' := fun i k ↦ squareTerminalQP hn w k i
  t := 0
  sY := fun k l ↦ if k ≤ l then squareTerminalQQ hn w k l else 0
  Ys := fun k l ↦ if k < l then squareTerminalQQ hn w l k else 0

-/

private abbrev TerminalR0Index
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :=
  TruncatedBasisIndex L (n - 1) ⊕ FreeLieExactBasisIndex L n

private def terminalR0Basis
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n) :
    Module.Basis (TerminalR0Index L n) ℤ (TerminalR0 L n) :=
  (terminalPSmithSorted L n hn).ambientBasis.prod
    (terminalQSmith L n).ambientBasis

@[simp] private theorem terminalR0Basis_repr_inl
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (z : TerminalR0 L n) (i : TruncatedBasisIndex L (n - 1)) :
    (terminalR0Basis L n hn).repr z (.inl i) =
      (terminalPSmithSorted L n hn).ambientBasis.repr z.1 i := by
  exact Module.Basis.prod_repr_inl _ _ _ _

@[simp] private theorem terminalR0Basis_repr_inr
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (z : TerminalR0 L n) (k : FreeLieExactBasisIndex L n) :
    (terminalR0Basis L n hn).repr z (.inr k) =
      (terminalQSmith L n).ambientBasis.repr z.2 k := by
  exact Module.Basis.prod_repr_inr _ _ _ _

private def terminalBasisPolynomial
    {I M : Type*} [AddCommGroup M] [Module ℤ M]
  (b : Module.Basis I ℤ M) (x : M) : MvPolynomial I ℤ :=
  (b.repr x).sum fun i c ↦ c • MvPolynomial.X i

private def terminalBasisPolynomialLinear
    {I M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis I ℤ M) : M →ₗ[ℤ] MvPolynomial I ℤ :=
  (Finsupp.linearCombination ℤ (MvPolynomial.X : I → MvPolynomial I ℤ)).comp
    b.repr.toLinearMap

@[simp] private theorem terminalBasisPolynomialLinear_apply
    {I M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis I ℤ M) (x : M) :
    terminalBasisPolynomialLinear b x = terminalBasisPolynomial b x := rfl

/-! ## The terminal kernel ledger

A reconstructed quadratic chain is stored coefficientwise in the second tensor factor.  Thus
`g s` is the complete first factor paired with the terminal basis vector `s`.  Crucially, the
kernel assertion is made about this complete sum, never about one homogeneous PBW child. -/

private def terminalKernelLedgerPolynomial
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (g : TerminalR0Index L n → TerminalR0 L n) :
    MvPolynomial (TerminalR0Index L n) ℤ :=
  ∑ s, terminalBasisPolynomial (terminalR0Basis L n hn) (g s) *
    terminalBasisPolynomial (terminalR0Basis L n hn)
      (terminalR0Basis L n hn s)

private theorem terminalKernelLedgerPolynomial_rankOne
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (x y : TerminalR0 L n) :
    terminalKernelLedgerPolynomial L n hn
        (fun s ↦ ((terminalR0Basis L n hn).repr y s) • x) =
      terminalBasisPolynomial (terminalR0Basis L n hn) x *
        terminalBasisPolynomial (terminalR0Basis L n hn) y := by
  classical
  let b := terminalR0Basis L n hn
  unfold terminalKernelLedgerPolynomial
  change ∑ s, terminalBasisPolynomialLinear b ((b.repr y s) • x) *
      terminalBasisPolynomial b (b s) = _
  simp_rw [map_zsmul, terminalBasisPolynomialLinear_apply]
  have hsum : ∑ s, (b.repr y s) • terminalBasisPolynomial b (b s) =
      terminalBasisPolynomial b y := by
    have h := congrArg (terminalBasisPolynomialLinear b) (b.sum_repr y)
    rw [map_sum] at h
    simpa only [map_zsmul, terminalBasisPolynomialLinear_apply] using h
  calc
    _ = terminalBasisPolynomial b x *
        (∑ s, (b.repr y s) • terminalBasisPolynomial b (b s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = _ := by rw [hsum]

private def terminalKernelLedgerPolynomialLinear
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    (TerminalR0Index L n → TerminalR0 L n) →ₗ[ℤ]
      MvPolynomial (TerminalR0Index L n) ℤ where
  toFun := terminalKernelLedgerPolynomial L n hn
  map_add' := by
    intro g h
    classical
    unfold terminalKernelLedgerPolynomial
    change (∑ s, terminalBasisPolynomialLinear (terminalR0Basis L n hn)
        (g s + h s) * _) = _
    simp only [map_add, terminalBasisPolynomialLinear_apply, add_mul,
      Finset.sum_add_distrib]
  map_smul' := by
    intro c g
    classical
    unfold terminalKernelLedgerPolynomial
    change (∑ s, terminalBasisPolynomialLinear (terminalR0Basis L n hn)
        (c • g s) * _) = _
    simp only [map_zsmul, terminalBasisPolynomialLinear_apply,
      smul_mul_assoc]
    change (∑ s, c •
        (terminalBasisPolynomial (terminalR0Basis L n hn) (g s) *
          terminalBasisPolynomial (terminalR0Basis L n hn)
            (terminalR0Basis L n hn s))) = c • ∑ s,
        terminalBasisPolynomial (terminalR0Basis L n hn) (g s) *
          terminalBasisPolynomial (terminalR0Basis L n hn)
            (terminalR0Basis L n hn s)
    let smulMap : MvPolynomial (TerminalR0Index L n) ℤ →+
        MvPolynomial (TerminalR0Index L n) ℤ :=
      { toFun := fun z ↦ c • z
        map_zero' := smul_zero c
        map_add' := smul_add c }
    simpa only [smulMap] using
      (map_sum smulMap (fun s ↦
        terminalBasisPolynomial (terminalR0Basis L n hn) (g s) *
          terminalBasisPolynomial (terminalR0Basis L n hn)
            (terminalR0Basis L n hn s)) Finset.univ).symm

@[simp] private theorem terminalKernelLedgerPolynomialLinear_apply
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (g : TerminalR0Index L n → TerminalR0 L n) :
    terminalKernelLedgerPolynomialLinear L n hn g =
      terminalKernelLedgerPolynomial L n hn g := rfl

private def terminalKernelLedgerLift
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (g : TerminalR0Index L n → TerminalR0 L n)
    (hker : ∀ s, g s ∈ (terminalR0ToW L n).ker)
    (s : TerminalR0Index L n) : TerminalR1 L n :=
  (terminalBoundaryEquivKernel L n hn).symm ⟨g s, hker s⟩

@[simp] private theorem terminalBoundary_terminalKernelLedgerLift
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (g : TerminalR0Index L n → TerminalR0 L n)
    (hker : ∀ s, g s ∈ (terminalR0ToW L n).ker)
    (s : TerminalR0Index L n) :
    terminalBoundary L n hn
        (terminalKernelLedgerLift L n hn g hker s) = g s := by
  have h := (terminalBoundaryEquivKernel L n hn).apply_symm_apply
    (⟨g s, hker s⟩ : (terminalR0ToW L n).ker)
  exact congrArg (fun z : (terminalR0ToW L n).ker ↦
    (z.1 : TerminalR0 L n)) h

/-- Smith coordinates of the chain `∑ s lift(g s) ⊗ s`. -/
private def terminalKernelLedgerExpression
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (g : TerminalR0Index L n → TerminalR0 L n)
    (hker : ∀ s, g s ∈ (terminalR0ToW L n).ker) :
    (terminalData R hn).CollectedExpression := by
  let P := terminalPSmithSorted L n hn
  let Q := terminalQSmith L n
  let lift := terminalKernelLedgerLift L n hn g hker
  exact
    { u := fun i j ↦ -P.relationBasis.repr (lift (.inl i)).1 j
      v := fun i k ↦ P.relationBasis.repr (lift (.inr k)).1 i
      v' := fun i k ↦ Q.relationBasis.repr (lift (.inl i)).2 k
      t := 0
      sY := fun k l ↦
        if k ≤ l then Q.relationBasis.repr (lift (.inr l)).2 k else 0
      Ys := fun k l ↦
        if k < l then Q.relationBasis.repr (lift (.inr k)).2 l else 0 }

/-- The factor-two PBW symbol after discarding Lie factors above the terminal presentation
degree.  Writing it as a linear map makes the one global marked-ledger induction insensitive
to how its finite sums are parenthesized.  The diagonal divided-power convention is retained
integrally (there is no hidden division by two). -/
private def terminalLowQuadraticPBWLinear
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    : UEA ℤ (TruncatedFreeLie L (2 * n)) →ₗ[ℤ]
      MvPolynomial (TerminalR0Index L n) ℤ := by
  classical
  let b := terminalR0Basis L n hn
  let symbol : (TruncatedBasisIndex L (2 * n) →₀ ℕ) →
      MvPolynomial (TerminalR0Index L n) ℤ := fun e ↦
    if factorNumber L e = 2 ∧
        ∀ i ∈ e.support, truncatedBasisWeight L i ≤ n then
      e.prod fun i m ↦
        terminalBasisPolynomial b
          (terminalFactorR0 L n (2 * n) i) ^ m
    else 0
  exact (Finsupp.linearCombination ℤ symbol).comp
    (truncatedPBWLinearEquiv L (2 * n)).symm.toLinearMap

private def terminalLowQuadraticPBW
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (z : UEA ℤ (TruncatedFreeLie L (2 * n))) :
    MvPolynomial (TerminalR0Index L n) ℤ :=
  terminalLowQuadraticPBWLinear L n hn z

@[simp] private theorem terminalLowQuadraticPBW_iota
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (x : TruncatedFreeLie L (2 * n)) :
    terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ x) = 0 := by
  classical
  unfold terminalLowQuadraticPBW terminalLowQuadraticPBWLinear
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro e he
  split_ifs with hshape
  · change pbwCoeff L (2 * n)
        (UniversalEnvelopingAlgebra.ι ℤ x) e • _ = 0
    rw [pbwCoeff_iota_eq_zero_of_factorNumber_ne_one L (2 * n) x e
      (by omega), zero_smul]
  · simp

set_option maxHeartbeats 800000 in
private theorem terminalLowQuadraticPBW_basis_mul_basis_all
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (i j : TruncatedBasisIndex L (2 * n)) :
    terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedHomogeneousBasis L (2 * n) i) *
          UniversalEnvelopingAlgebra.ι ℤ
            (truncatedHomogeneousBasis L (2 * n) j)) =
      if truncatedBasisWeight L i ≤ n ∧ truncatedBasisWeight L j ≤ n then
        terminalBasisPolynomial (terminalR0Basis L n hn)
            (terminalFactorR0 L n (2 * n) i) *
          terminalBasisPolynomial (terminalR0Basis L n hn)
            (terminalFactorR0 L n (2 * n) j)
      else 0 := by
  classical
  letI : DecidableEq (TruncatedBasisIndex L (2 * n)) :=
    LinearOrder.toDecidableEq
  let E := truncatedPBWLinearEquiv L (2 * n)
  let b := truncatedHomogeneousBasis L (2 * n)
  have hordered (a c : TruncatedBasisIndex L (2 * n))
      (hac : a ≤ c) :
      terminalLowQuadraticPBW L n hn
          (UniversalEnvelopingAlgebra.ι ℤ (b a) *
            UniversalEnvelopingAlgebra.ι ℤ (b c)) =
        if truncatedBasisWeight L a ≤ n ∧
            truncatedBasisWeight L c ≤ n then
          terminalBasisPolynomial (terminalR0Basis L n hn)
              (terminalFactorR0 L n (2 * n) a) *
            terminalBasisPolynomial (terminalR0Basis L n hn)
              (terminalFactorR0 L n (2 * n) c)
        else 0 := by
    let e : TruncatedBasisIndex L (2 * n) →₀ ℕ :=
      Multiset.toFinsupp (([a, c] : List
        (TruncatedBasisIndex L (2 * n))) : Multiset _)
    have hpair : MvPolynomial.X a *
        (MvPolynomial.X c : MvPolynomial
          (TruncatedBasisIndex L (2 * n)) ℤ) =
        MvPolynomial.monomial e 1 := by
      simpa only [List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, e] using
        (LieRings.PBW.Higgins.OrderedCyclic.prod_X_eq_monomial_toFinsupp
          ([a, c] : List (TruncatedBasisIndex L (2 * n))))
    have hword : orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n)) b e =
          UniversalEnvelopingAlgebra.ι ℤ (b a) *
            UniversalEnvelopingAlgebra.ι ℤ (b c) := by
      simpa only [basisWord, word, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, e] using
        (orderedMonomial_multiset_toFinsupp ℤ
          (TruncatedFreeLie L (2 * n))
          (TruncatedBasisIndex L (2 * n)) b [a, c] (by simp [hac]))
    have hE : E (MvPolynomial.X a * MvPolynomial.X c) =
        UniversalEnvelopingAlgebra.ι ℤ (b a) *
          UniversalEnvelopingAlgebra.ι ℤ (b c) := by
      rw [hpair]
      change orderedPBWMap ℤ (TruncatedFreeLie L (2 * n))
          (TruncatedBasisIndex L (2 * n)) b
            (MvPolynomial.monomial e 1) = _
      rw [orderedPBWMap_monomial]
      calc
        (1 : ℤ) • orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
            (TruncatedBasisIndex L (2 * n)) b e =
            orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
              (TruncatedBasisIndex L (2 * n)) b e := by module
        _ = _ := hword
    have hcoordinate : E.symm
          (UniversalEnvelopingAlgebra.ι ℤ (b a) *
            UniversalEnvelopingAlgebra.ι ℤ (b c)) =
        MvPolynomial.monomial e 1 := by
      rw [← hE, E.symm_apply_apply, hpair]
    unfold terminalLowQuadraticPBW terminalLowQuadraticPBWLinear
    change (Finsupp.linearCombination ℤ _)
        (E.symm (UniversalEnvelopingAlgebra.ι ℤ (b a) *
          UniversalEnvelopingAlgebra.ι ℤ (b c))) = _
    rw [hcoordinate]
    change (Finsupp.linearCombination ℤ _) (Finsupp.single e 1) = _
    rw [Finsupp.linearCombination_single]
    have hfactor : factorNumber L e = 2 := by
      let s : Multiset (TruncatedBasisIndex L (2 * n)) := [a, c]
      unfold factorNumber
      change (Multiset.toFinsupp s).sum
        (fun _ m ↦ m) = 2
      simpa only [id_eq, List.length_cons, List.length_nil] using
        Multiset.toFinsupp_sum_eq s
    by_cases hlow : truncatedBasisWeight L a ≤ n ∧
        truncatedBasisWeight L c ≤ n
    · have hsupport : ∀ x ∈ e.support,
          truncatedBasisWeight L x ≤ n := by
        intro x hx
        have hx' : x = a ∨ x = c := by
          simpa [e, Multiset.toFinsupp_apply] using hx
        rcases hx' with rfl | rfl
        · exact hlow.1
        · exact hlow.2
      rw [if_pos ⟨hfactor, hsupport⟩, if_pos hlow]
      rw [one_smul]
      have he : e = Finsupp.single a 1 + Finsupp.single c 1 := by
        ext x
        by_cases hxa : x = a <;> by_cases hxc : x = c <;>
          simp [e, Multiset.toFinsupp_apply, Finsupp.single_apply,
            List.count_cons, hxa, hxc] <;> omega
      rw [he, Finsupp.prod_add_index'
        (fun _ ↦ pow_zero _)
        (fun _ p q ↦ pow_add _ p q)]
      simp
    · have hnotSupport : ¬(∀ x ∈ e.support,
          truncatedBasisWeight L x ≤ n) := by
        intro hs
        apply hlow
        constructor
        · apply hs a
          simp [e, Multiset.toFinsupp_apply]
        · apply hs c
          simp [e, Multiset.toFinsupp_apply]
      rw [if_neg (fun h ↦ hnotSupport h.2), if_neg hlow]
      simp
  by_cases hij : i ≤ j
  · simpa only [b] using hordered i j hij
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    have hswap := iota_mul_iota_swap ℤ (TruncatedFreeLie L (2 * n))
      (b i) (b j)
    rw [hswap]
    change (terminalLowQuadraticPBWLinear L n hn)
      (UniversalEnvelopingAlgebra.ι ℤ (b j) *
          UniversalEnvelopingAlgebra.ι ℤ (b i) +
        UniversalEnvelopingAlgebra.ι ℤ ⁅b i, b j⁆) = _
    rw [map_add]
    have hzero := terminalLowQuadraticPBW_iota L n hn ⁅b i, b j⁆
    change (terminalLowQuadraticPBWLinear L n hn)
        (UniversalEnvelopingAlgebra.ι ℤ ⁅b i, b j⁆) = 0 at hzero
    have hord := hordered j i hji
    change (terminalLowQuadraticPBWLinear L n hn)
        (UniversalEnvelopingAlgebra.ι ℤ (b j) *
          UniversalEnvelopingAlgebra.ι ℤ (b i)) = _ at hord
    rw [hzero, add_zero, hord]
    by_cases hlow : truncatedBasisWeight L i ≤ n ∧
        truncatedBasisWeight L j ≤ n
    · rw [if_pos hlow, if_pos ⟨hlow.2, hlow.1⟩]
      exact mul_comm _ _
    · rw [if_neg hlow, if_neg]
      exact fun h ↦ hlow ⟨h.2, h.1⟩

private theorem terminalLowQuadraticPBW_basis_mul_basis
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (i j : TruncatedBasisIndex L (2 * n))
    (hi : truncatedBasisWeight L i ≤ n)
    (hj : truncatedBasisWeight L j ≤ n) :
    terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedHomogeneousBasis L (2 * n) i) *
          UniversalEnvelopingAlgebra.ι ℤ
            (truncatedHomogeneousBasis L (2 * n) j)) =
      terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalFactorR0 L n (2 * n) i) *
        terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalFactorR0 L n (2 * n) j) := by
  rw [terminalLowQuadraticPBW_basis_mul_basis_all, if_pos ⟨hi, hj⟩]

private theorem terminalLowQuadraticPBW_iota_mul_basis_eq_zero_of_high
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (x : TruncatedFreeLie L (2 * n))
    (i : TruncatedBasisIndex L (2 * n))
    (hi : n < truncatedBasisWeight L i) :
    terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ
            (truncatedHomogeneousBasis L (2 * n) i)) = 0 := by
  classical
  let b := truncatedHomogeneousBasis L (2 * n)
  have hxsum : (b.repr x).sum (fun j c ↦ c • b j) = x :=
    b.linearCombination_repr x
  change (terminalLowQuadraticPBWLinear L n hn)
    (UniversalEnvelopingAlgebra.ι ℤ x *
      UniversalEnvelopingAlgebra.ι ℤ (b i)) = 0
  rw [← hxsum, map_finsuppSum, Finsupp.sum_mul, map_finsuppSum]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [map_zsmul, smul_mul_assoc, map_zsmul]
  change (b.repr x j) • terminalLowQuadraticPBW L n hn
      (UniversalEnvelopingAlgebra.ι ℤ (b j) *
        UniversalEnvelopingAlgebra.ι ℤ (b i)) = 0
  rw [terminalLowQuadraticPBW_basis_mul_basis_all, if_neg]
  · simp
  · exact fun h ↦ (not_le_of_gt hi) h.2

private theorem terminalLowQuadraticPBW_basis_mul_iota_eq_zero_of_high
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (i : TruncatedBasisIndex L (2 * n))
    (x : TruncatedFreeLie L (2 * n))
    (hi : n < truncatedBasisWeight L i) :
    terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedHomogeneousBasis L (2 * n) i) *
          UniversalEnvelopingAlgebra.ι ℤ x) = 0 := by
  rw [iota_mul_iota_swap]
  change (terminalLowQuadraticPBWLinear L n hn)
    (UniversalEnvelopingAlgebra.ι ℤ x *
        UniversalEnvelopingAlgebra.ι ℤ
          (truncatedHomogeneousBasis L (2 * n) i) +
      UniversalEnvelopingAlgebra.ι ℤ
        ⁅truncatedHomogeneousBasis L (2 * n) i, x⁆) = 0
  rw [map_add]
  have hfirst := terminalLowQuadraticPBW_iota_mul_basis_eq_zero_of_high
    L n hn x i hi
  change (terminalLowQuadraticPBWLinear L n hn)
    (UniversalEnvelopingAlgebra.ι ℤ x *
      UniversalEnvelopingAlgebra.ι ℤ
        (truncatedHomogeneousBasis L (2 * n) i)) = 0 at hfirst
  have hsecond := terminalLowQuadraticPBW_iota L n hn
    ⁅truncatedHomogeneousBasis L (2 * n) i, x⁆
  change (terminalLowQuadraticPBWLinear L n hn)
    (UniversalEnvelopingAlgebra.ι ℤ
      ⁅truncatedHomogeneousBasis L (2 * n) i, x⁆) = 0 at hsecond
  rw [hfirst, hsecond, add_zero]

private theorem terminalLowQuadraticPBW_iota_mul_iota_of_lowSupport
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (x y : TruncatedFreeLie L (2 * n))
    (hx : ∀ i ∈ (truncatedHomogeneousBasis L (2 * n)).repr x |>.support,
      truncatedBasisWeight L i ≤ n)
    (hy : ∀ i ∈ (truncatedHomogeneousBasis L (2 * n)).repr y |>.support,
      truncatedBasisWeight L i ≤ n) :
    terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ y) =
      terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalR0ProjectionTruncated L n hn x) *
        terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalR0ProjectionTruncated L n hn y) := by
  classical
  let b := truncatedHomogeneousBasis L (2 * n)
  let q := terminalLowQuadraticPBWLinear L n hn
  let p := (terminalBasisPolynomialLinear (terminalR0Basis L n hn)).comp
    (terminalR0ProjectionTruncated L n hn)
  have hxsum : (b.repr x).sum (fun i c ↦ c • b i) = x :=
    b.linearCombination_repr x
  have hysum : (b.repr y).sum (fun i c ↦ c • b i) = y :=
    b.linearCombination_repr y
  change q (UniversalEnvelopingAlgebra.ι ℤ x *
      UniversalEnvelopingAlgebra.ι ℤ y) = p x * p y
  have hq : q (UniversalEnvelopingAlgebra.ι ℤ x *
        UniversalEnvelopingAlgebra.ι ℤ y) =
      (b.repr x).sum (fun i ci ↦
        (b.repr y).sum (fun j cj ↦
          (ci * cj) • q
            (UniversalEnvelopingAlgebra.ι ℤ (b i) *
              UniversalEnvelopingAlgebra.ι ℤ (b j)))) := by
    conv_lhs =>
      rw [← hxsum, ← hysum]
    rw [map_finsuppSum, map_finsuppSum]
    simp_rw [map_zsmul]
    rw [Finsupp.sum_mul, map_finsuppSum]
    apply Finsupp.sum_congr
    intro i hi
    rw [Finsupp.mul_sum, map_finsuppSum]
    apply Finsupp.sum_congr
    intro j hj
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, map_zsmul]
  have hp : p x * p y =
      (b.repr x).sum (fun i ci ↦
        (b.repr y).sum (fun j cj ↦
          (ci * cj) • (p (b i) * p (b j)))) := by
    conv_lhs =>
      rw [← hxsum, ← hysum]
    rw [map_finsuppSum, map_finsuppSum]
    simp_rw [map_zsmul]
    rw [Finsupp.sum_mul]
    apply Finsupp.sum_congr
    intro i hi
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro j hj
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hq, hp]
  apply Finsupp.sum_congr
  intro i hi
  apply Finsupp.sum_congr
  intro j hj
  change ((b.repr x) i * (b.repr y) j) •
      terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ (b i) *
          UniversalEnvelopingAlgebra.ι ℤ (b j)) = _
  have hpi : p (b i) =
      terminalBasisPolynomial (terminalR0Basis L n hn)
        (terminalFactorR0 L n (2 * n) i) := by
    simp only [p, b, LinearMap.comp_apply,
      terminalBasisPolynomialLinear_apply,
      terminalR0ProjectionTruncated_basis]
  have hpj : p (b j) =
      terminalBasisPolynomial (terminalR0Basis L n hn)
        (terminalFactorR0 L n (2 * n) j) := by
    simp only [p, b, LinearMap.comp_apply,
      terminalBasisPolynomialLinear_apply,
      terminalR0ProjectionTruncated_basis]
  rw [hpi, hpj, terminalLowQuadraticPBW_basis_mul_basis L n hn i j
    (hx i hi) (hy j hj)]

/-- The factor-two symbol of a product of two arbitrary Lie elements is the symmetric product
of their terminal projections.  Components above weight `n` disappear on both sides; no
support hypothesis is needed. -/
private theorem terminalLowQuadraticPBW_iota_mul_iota
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (x y : TruncatedFreeLie L (2 * n)) :
    terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ y) =
      terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalR0ProjectionTruncated L n hn x) *
        terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalR0ProjectionTruncated L n hn y) := by
  classical
  let b := truncatedHomogeneousBasis L (2 * n)
  let q := terminalLowQuadraticPBWLinear L n hn
  let p := (terminalBasisPolynomialLinear (terminalR0Basis L n hn)).comp
    (terminalR0ProjectionTruncated L n hn)
  have hxsum : (b.repr x).sum (fun i c ↦ c • b i) = x :=
    b.linearCombination_repr x
  have hysum : (b.repr y).sum (fun i c ↦ c • b i) = y :=
    b.linearCombination_repr y
  change q (UniversalEnvelopingAlgebra.ι ℤ x *
      UniversalEnvelopingAlgebra.ι ℤ y) = p x * p y
  have hq : q (UniversalEnvelopingAlgebra.ι ℤ x *
        UniversalEnvelopingAlgebra.ι ℤ y) =
      (b.repr x).sum (fun i ci ↦
        (b.repr y).sum (fun j cj ↦
          (ci * cj) • q
            (UniversalEnvelopingAlgebra.ι ℤ (b i) *
              UniversalEnvelopingAlgebra.ι ℤ (b j)))) := by
    conv_lhs => rw [← hxsum, ← hysum]
    rw [map_finsuppSum, map_finsuppSum]
    simp_rw [map_zsmul]
    rw [Finsupp.sum_mul, map_finsuppSum]
    apply Finsupp.sum_congr
    intro i hi
    rw [Finsupp.mul_sum, map_finsuppSum]
    apply Finsupp.sum_congr
    intro j hj
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, map_zsmul]
  have hp : p x * p y =
      (b.repr x).sum (fun i ci ↦
        (b.repr y).sum (fun j cj ↦
          (ci * cj) • (p (b i) * p (b j)))) := by
    conv_lhs => rw [← hxsum, ← hysum]
    rw [map_finsuppSum, map_finsuppSum]
    simp_rw [map_zsmul]
    rw [Finsupp.sum_mul]
    apply Finsupp.sum_congr
    intro i hi
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro j hj
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hq, hp]
  apply Finsupp.sum_congr
  intro i hi
  apply Finsupp.sum_congr
  intro j hj
  change ((b.repr x i * b.repr y j) : ℤ) •
      terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ (b i) *
          UniversalEnvelopingAlgebra.ι ℤ (b j)) =
    (b.repr x i * b.repr y j) • (p (b i) * p (b j))
  rw [terminalLowQuadraticPBW_basis_mul_basis_all]
  simp only [p, b, LinearMap.comp_apply,
    terminalBasisPolynomialLinear_apply,
    terminalR0ProjectionTruncated_basis]
  by_cases hilow : truncatedBasisWeight L i ≤ n
  · by_cases hjlow : truncatedBasisWeight L j ≤ n
    · rw [if_pos ⟨hilow, hjlow⟩]
    · rw [if_neg (fun h ↦ hjlow h.2),
          terminalFactorR0_eq_zero_of_weight_gt L n (2 * n) j (by omega)]
      simp [terminalBasisPolynomial]
  · rw [if_neg (fun h ↦ hilow h.1),
        terminalFactorR0_eq_zero_of_weight_gt L n (2 * n) i (by omega)]
    simp [terminalBasisPolynomial]

private theorem terminalLowQuadraticPBW_basisWord_eq_zero_of_sorted
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) (hn : 1 ≤ n)
    (xs : List (TruncatedBasisIndex L (2 * n)))
    (hsorted : xs.Pairwise (· ≤ ·)) (hlen : xs.length ≠ 2) :
    terminalLowQuadraticPBW L n hn
        (basisWord ℤ (TruncatedFreeLie L (2 * n))
          (TruncatedBasisIndex L (2 * n))
          (truncatedHomogeneousBasis L (2 * n)) xs) = 0 := by
  classical
  letI : DecidableEq (TruncatedBasisIndex L (2 * n)) :=
    LinearOrder.toDecidableEq
  let E := truncatedPBWLinearEquiv L (2 * n)
  let b := truncatedHomogeneousBasis L (2 * n)
  let e : TruncatedBasisIndex L (2 * n) →₀ ℕ :=
    Multiset.toFinsupp (xs : Multiset _)
  have hword : orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
      (TruncatedBasisIndex L (2 * n)) b e =
        basisWord ℤ (TruncatedFreeLie L (2 * n))
          (TruncatedBasisIndex L (2 * n)) b xs := by
    simpa only [e] using
      (orderedMonomial_multiset_toFinsupp ℤ
        (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n)) b xs hsorted)
  have hE : E (MvPolynomial.monomial e 1) =
      basisWord ℤ (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n)) b xs := by
    change orderedPBWMap ℤ (TruncatedFreeLie L (2 * n))
      (TruncatedBasisIndex L (2 * n)) b
        (MvPolynomial.monomial e 1) = _
    rw [orderedPBWMap_monomial]
    exact (one_smul ℤ _).trans hword
  have hcoordinate : E.symm
      (basisWord ℤ (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n)) b xs) =
      MvPolynomial.monomial e 1 := by
    rw [← hE, E.symm_apply_apply]
  have hfactor : factorNumber L e = xs.length := by
    unfold factorNumber
    simpa only [id_eq] using
      (Multiset.toFinsupp_sum_eq (xs : Multiset
        (TruncatedBasisIndex L (2 * n))))
  unfold terminalLowQuadraticPBW terminalLowQuadraticPBWLinear
  change (Finsupp.linearCombination ℤ _)
      (E.symm (basisWord ℤ (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n)) b xs)) = 0
  rw [hcoordinate]
  change (Finsupp.linearCombination ℤ _)
      (Finsupp.single e 1) = 0
  rw [Finsupp.linearCombination_single]
  have hfactorNe : factorNumber L e ≠ 2 := by
    rw [hfactor]
    exact hlen
  rw [if_neg (fun h ↦ hfactorNe h.1)]
  simp

private theorem terminalWallQuadratic_right
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (r : CanonicalLieRelationsIdeal L)
    (c : RelationContext L (2 * n))
    (k : ℕ) (hactive : k + c.weight L = n)
    (x : TruncatedBasisIndex L (2 * n)) :
    terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedFreeLieMk L (2 * n)
              (c.applyFree L (markedPrefixFree L k r))) *
          UniversalEnvelopingAlgebra.ι ℤ
            (truncatedHomogeneousBasis L (2 * n) x)) =
      terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalBoundary L n hn
            (terminalRelationR1 L n hn (c.relation L r))) *
        terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalFactorR0 L n (2 * n) x) := by
  by_cases hx : truncatedBasisWeight L x ≤ n
  · rw [terminalLowQuadraticPBW_iota_mul_iota_of_lowSupport]
    · rw [terminalR0ProjectionTruncated_mk,
        terminalR0Projection_contextPrefix L n k hn r c hactive,
        terminalBoundary_terminalRelationR1,
        terminalR0ProjectionTruncated_basis]
    · simpa [hactive] using
        contextPrefix_repr_support_le_active L n r c k (by omega)
    · intro i hi
      rw [Module.Basis.repr_self] at hi
      have hi' : i = x := by
        by_contra hne
        exact Finsupp.mem_support_iff.mp hi (by
          simp [Finsupp.single_apply, hne])
      subst i
      exact hx
  · have hx' : n < truncatedBasisWeight L x := by omega
    rw [terminalLowQuadraticPBW_iota_mul_basis_eq_zero_of_high
      L n hn _ x hx', terminalFactorR0_eq_zero_of_weight_gt L n (2 * n) x hx']
    simp [terminalBasisPolynomial]

private theorem terminalWallQuadratic_left
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (r : CanonicalLieRelationsIdeal L)
    (c : RelationContext L (2 * n))
    (k : ℕ) (hactive : k + c.weight L = n)
    (x : TruncatedBasisIndex L (2 * n)) :
    terminalLowQuadraticPBW L n hn
        (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedHomogeneousBasis L (2 * n) x) *
          UniversalEnvelopingAlgebra.ι ℤ
            (truncatedFreeLieMk L (2 * n)
              (c.applyFree L (markedPrefixFree L k r)))) =
      terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalBoundary L n hn
            (terminalRelationR1 L n hn (c.relation L r))) *
        terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalFactorR0 L n (2 * n) x) := by
  by_cases hx : truncatedBasisWeight L x ≤ n
  · rw [terminalLowQuadraticPBW_iota_mul_iota_of_lowSupport]
    · rw [terminalR0ProjectionTruncated_basis,
        terminalR0ProjectionTruncated_mk,
        terminalR0Projection_contextPrefix L n k hn r c hactive,
        terminalBoundary_terminalRelationR1]
      exact mul_comm _ _
    · intro i hi
      rw [Module.Basis.repr_self] at hi
      have hi' : i = x := by
        by_contra hne
        exact Finsupp.mem_support_iff.mp hi (by
          simp [Finsupp.single_apply, hne])
      subst i
      exact hx
    · simpa [hactive] using
        contextPrefix_repr_support_le_active L n r c k (by omega)
  · have hx' : n < truncatedBasisWeight L x := by omega
    rw [terminalLowQuadraticPBW_basis_mul_iota_eq_zero_of_high
      L n hn x _ hx', terminalFactorR0_eq_zero_of_weight_gt L n (2 * n) x hx']
    simp [terminalBasisPolynomial]

private theorem totalWeight_le_two_mul_of_factorNumber_two
    (L : Type u) [Finite L] {N n : ℕ}
    (e : TruncatedBasisIndex L N →₀ ℕ)
    (hfactors : factorNumber L e = 2)
    (hlow : ∀ i ∈ e.support, truncatedBasisWeight L i ≤ n) :
    totalWeight L e ≤ 2 * n := by
  unfold factorNumber at hfactors
  unfold totalWeight
  calc
    e.sum (fun i m ↦ m * truncatedBasisWeight L i) ≤
        e.sum (fun _ m ↦ m * n) := by
          apply Finsupp.sum_le_sum
          intro i hi
          exact Nat.mul_le_mul_left (e i) (hlow i hi)
    _ = n * e.sum (fun _ m ↦ m) := by
          simp [Finsupp.sum, Nat.mul_comm, Finset.mul_sum]
    _ = 2 * n := by rw [hfactors, Nat.mul_comm]

private theorem terminalLowQuadraticPBW_relationSide_eq_zero
    (n : ℕ) (hn : 1 ≤ n)
    (L : Type u) [LieRing L] [Finite L]
    (a : L) (w : GoverningWitness n L a)
    (hgoverning : ∀ e : TruncatedBasisIndex L (2 * n) →₀ ℕ,
      totalWeight L e ≤ 2 * n →
        pbwCoeff L (2 * n) w.relationSide e =
          pbwCoeff L (2 * n)
            (UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk L (2 * n)
                (w.zTilde : CanonicalFreeLie L))) e) :
    terminalLowQuadraticPBW L n hn w.relationSide = 0 := by
  classical
  unfold terminalLowQuadraticPBW terminalLowQuadraticPBWLinear
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro e he
  split_ifs with hshape
  · have hweight := totalWeight_le_two_mul_of_factorNumber_two
      L e hshape.1 hshape.2
    have hne : factorNumber L e ≠ 1 := by omega
    have hiota := pbwCoeff_iota_eq_zero_of_factorNumber_ne_one
      L (2 * n)
      (truncatedFreeLieMk L (2 * n)
        (w.zTilde : CanonicalFreeLie L)) e hne
    change pbwCoeff L (2 * n) w.relationSide e • _ = 0
    rw [hgoverning e hweight, hiota, zero_smul]
  · simp

private theorem positiveSmith_ambient_repr_subtype
    {I M : Type*} [Fintype I] [AddCommGroup M] [Module ℤ M]
    {N : Submodule ℤ M} (P : PositiveSmithPresentation (ι := I) N)
    (x : N) (i : I) :
    P.ambientBasis.repr (x : M) i =
      (P.diagonal i : ℤ) * P.relationBasis.repr x i := by
  classical
  have hmodule : (inferInstance : Module ℤ M) =
      AddCommGroup.toIntModule M := Subsingleton.elim _ _
  cases hmodule
  have hexpand := P.relationBasis.sum_repr x
  have hexpandM :
      ∑ j, (P.relationBasis.repr x) j • (P.relationBasis j : M) =
        (x : M) := by
    have hcoe := congrArg (N.subtype : N →ₗ[ℤ] M) hexpand
    simpa only [map_sum, map_smul, LinearMap.coe_coe,
      LinearMap.coe_mk, AddHom.coe_mk] using hcoe
  have hre := congrArg P.ambientBasis.repr hexpandM
  rw [map_sum] at hre
  simp only [P.relation_eq, smul_smul, map_smul,
    Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one] at hre
  have hi := congrArg (Finsupp.lapply i : (I →₀ ℤ) →ₗ[ℤ] ℤ) hre
  rw [map_sum] at hi
  simpa [Finsupp.single_apply, mul_comm] using hi.symm

private theorem terminalBMap_coordinate
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (a : TerminalP1 L n)
    (k : FreeLieExactBasisIndex L n) :
    (terminalQSmith L n).ambientBasis.repr (terminalBMap L n hn a) k =
      ∑ i, (terminalPSmithSorted L n hn).relationBasis.repr a i *
        terminalB L n hn i k := by
  classical
  let P := terminalPSmithSorted L n hn
  let Q := terminalQSmith L n
  have ha := P.relationBasis.sum_repr a
  calc
    Q.ambientBasis.repr (terminalBMap L n hn a) k =
        Q.ambientBasis.repr
          (terminalBMap L n hn
            (∑ i, (P.relationBasis.repr a) i • P.relationBasis i)) k := by
              rw [ha]
    _ = Q.ambientBasis.repr
          (∑ i, (P.relationBasis.repr a) i •
            terminalBMap L n hn (P.relationBasis i)) k := by
              rw [map_sum]
              simp_rw [map_zsmul]
    _ = ∑ i, (P.relationBasis.repr a) i *
          Q.ambientBasis.repr
            (terminalBMap L n hn (P.relationBasis i)) k := by
              rw [map_sum]
              change (Finsupp.lapply k :
                  (FreeLieExactBasisIndex L n →₀ ℤ) →ₗ[ℤ] ℤ)
                  (∑ i, Q.ambientBasis.repr
                    ((P.relationBasis.repr a) i •
                      terminalBMap L n hn (P.relationBasis i))) = _
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro i hi
              simp
    _ = _ := by rfl

private theorem terminalBoundary_coordinate_inl
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (z : TerminalR1 L n)
    (i : TruncatedBasisIndex L (n - 1)) :
    (terminalR0Basis L n hn).repr (terminalBoundary L n hn z) (.inl i) =
      ((terminalPSmithSorted L n hn).diagonal i : ℤ) *
        (terminalPSmithSorted L n hn).relationBasis.repr z.1 i := by
  change (terminalPSmithSorted L n hn).ambientBasis.repr z.1.1 i = _
  exact positiveSmith_ambient_repr_subtype
    (terminalPSmithSorted L n hn) z.1 i

private theorem terminalBoundary_coordinate_inr
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (z : TerminalR1 L n)
    (k : FreeLieExactBasisIndex L n) :
    (terminalR0Basis L n hn).repr (terminalBoundary L n hn z) (.inr k) =
      ((terminalQSmith L n).diagonal k : ℤ) *
          (terminalQSmith L n).relationBasis.repr z.2 k -
        ∑ i, (terminalPSmithSorted L n hn).relationBasis.repr z.1 i *
          terminalB L n hn i k := by
  change (terminalQSmith L n).ambientBasis.repr
      (z.2.1 - terminalBMap L n hn z.1) k = _
  rw [map_sub, Finsupp.sub_apply,
    positiveSmith_ambient_repr_subtype (terminalQSmith L n) z.2 k,
    terminalBMap_coordinate L n hn z.1 k]

/-
The obsolete side-forgetting terminal comparison is retained here until its purely mechanical
retargeting to `terminalPP/PQ/QP/QQ` at compile gate 6.  The repaired packet never consumes
these `squareTerminal*` arrays.

private def terminalCyclePolynomial
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    MvPolynomial (TerminalR0Index L n) ℤ := by
  classical
  let b := terminalR0Basis L n hn
  exact ∑ t : w.TerminalTraceRowIndex, let row := w.terminalTraceRowAt t
    row.coefficient •
    (terminalBasisPolynomial b
        (terminalBoundary L n hn (terminalRelationR1 L n hn row.relation)) *
      terminalBasisPolynomial b
        (terminalFactorR0 L n (2 * n) row.factor))

/-- The same terminal boundary read on an arbitrary finite part of the marked rewrite trace.
This is kept separate from `terminalCyclePolynomial` only so that the one closed-square
induction can recurse on a single marked subtree. -/
private def terminalTracePolynomial
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (cells : List (RewriteCell (squarePacketCollector L n))) :
    MvPolynomial (TerminalR0Index L n) ℤ := by
  classical
  let b := terminalR0Basis L n hn
  exact (cells.filterMap (terminalTraceRowOfCell L n)).map (fun row ↦
    row.coefficient •
      (terminalBasisPolynomial b
          (terminalBoundary L n hn
            (terminalRelationR1 L n hn row.relation)) *
        terminalBasisPolynomial b
          (terminalFactorR0 L n (2 * n) row.factor))) |>.sum

private theorem terminalCyclePolynomial_eq_trace
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    terminalCyclePolynomial hn w =
      terminalTracePolynomial L n hn w.squareTrace := by
  classical
  unfold terminalCyclePolynomial terminalTracePolynomial
  rw [List.filterMap_eq_map_filter]
  simp only [GoverningWitness.TerminalTraceRowIndex,
    GoverningWitness.terminalTraceRows, GoverningWitness.terminalTraceRowAt]
  rw [Fin.sum_univ_eq_sum_range]
  simp

/-- One coefficient of the symmetric boundary of the terminal factor-two chain.  On the
diagonal the monomial occurs once; off the diagonal it has the two possible placements. -/
private def terminalCycleCoefficient
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i j : TerminalR0Index L n) : ℤ := by
  classical
  let b := terminalR0Basis L n hn
  exact ∑ t : w.TerminalTraceRowIndex, let row := w.terminalTraceRowAt t
    let dr := b.repr
      (terminalBoundary L n hn
        (terminalRelationR1 L n hn row.relation))
    let fx := b.repr (terminalFactorR0 L n (2 * n) row.factor)
    row.coefficient *
      (if i = j then dr i * fx i else dr i * fx j + dr j * fx i)

private theorem terminalCycleCoefficient_eq_coeff
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i j : TerminalR0Index L n) :
    terminalCycleCoefficient hn w i j =
      MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
        (terminalCyclePolynomial hn w) := by
  classical
  let b := terminalR0Basis L n hn
  have hpair (x y : TerminalR0 L n) :
      MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
          (terminalBasisPolynomial b x * terminalBasisPolynomial b y) =
        if i = j then b.repr x i * b.repr y i
        else b.repr x i * b.repr y j + b.repr x j * b.repr y i := by
    unfold terminalBasisPolynomial
    change MvPolynomial.coeff _
      ((b.repr x).sum (fun a z ↦ z • MvPolynomial.X a) *
        (b.repr y).sum (fun c z ↦ z • MvPolynomial.X c)) = _
    rw [Finsupp.sum_mul, map_finsuppSum]
    simp only [smul_eq_mul, mul_assoc]
    rw [Finsupp.mul_sum, map_finsuppSum]
    simp only [mul_smul_comm, smul_eq_mul, map_smul]
    by_cases hij : i = j
    · subst j
      simp [MvPolynomial.coeff_X_mul_X, Finsupp.single_add]
    · simp [MvPolynomial.coeff_X_mul_X, hij, Finsupp.single_apply]
  unfold terminalCycleCoefficient terminalCyclePolynomial
  rw [map_sum]
  simp_rw [map_zsmul, hpair]
  rfl

private theorem terminalCycleCoefficient_inl_inl
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i j : TruncatedBasisIndex L (n - 1)) :
    terminalCycleCoefficient hn w (.inl i) (.inl j) =
      if i = j then
        ((terminalPSmithSorted L n hn).diagonal i : ℤ) *
          squareTerminalPP hn w i i
      else
        ((terminalPSmithSorted L n hn).diagonal i : ℤ) *
            squareTerminalPP hn w i j +
          ((terminalPSmithSorted L n hn).diagonal j : ℤ) *
            squareTerminalPP hn w j i := by
  classical
  let P := terminalPSmithSorted L n hn
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    unfold terminalCycleCoefficient squareTerminalPP
    simp only [↓reduceIte]
    simp_rw [terminalBoundary_coordinate_inl]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only
    simp only [terminalR0Basis_repr_inl]
    ring
  · rw [if_neg hij]
    have hij' : (Sum.inl i : TerminalR0Index L n) ≠ Sum.inl j := by
      exact fun h ↦ hij (Sum.inl_injective h)
    unfold terminalCycleCoefficient squareTerminalPP
    simp only [hij', if_false]
    simp_rw [terminalBoundary_coordinate_inl]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only
    simp only [terminalR0Basis_repr_inl]
    ring

private theorem terminalCycleCoefficient_inl_inr
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i : TruncatedBasisIndex L (n - 1))
    (k : FreeLieExactBasisIndex L n) :
    terminalCycleCoefficient hn w (.inl i) (.inr k) =
      ((terminalPSmithSorted L n hn).diagonal i : ℤ) *
          squareTerminalPQ hn w i k +
        ((terminalQSmith L n).diagonal k : ℤ) *
          squareTerminalQP hn w k i -
        ∑ j, terminalB L n hn j k * squareTerminalPP hn w j i := by
  classical
  let P := terminalPSmithSorted L n hn
  let Q := terminalQSmith L n
  unfold terminalCycleCoefficient squareTerminalPP squareTerminalPQ
    squareTerminalQP
  simp only [reduceCtorEq, if_false]
  simp_rw [terminalBoundary_coordinate_inl,
    terminalBoundary_coordinate_inr]
  simp only [terminalR0Basis_repr_inl, terminalR0Basis_repr_inr]
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only
  simp only [mul_add, mul_sub, sub_mul, Finset.sum_mul, Finset.mul_sum]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem terminalCycleCoefficient_inr_inr
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (k l : FreeLieExactBasisIndex L n) :
    terminalCycleCoefficient hn w (.inr k) (.inr l) =
      if k = l then
        ((terminalQSmith L n).diagonal k : ℤ) *
            squareTerminalQQ hn w k k -
          ∑ i, terminalB L n hn i k * squareTerminalPQ hn w i k
      else
        ((terminalQSmith L n).diagonal k : ℤ) *
            squareTerminalQQ hn w k l +
          ((terminalQSmith L n).diagonal l : ℤ) *
            squareTerminalQQ hn w l k -
          ∑ i, (terminalB L n hn i k * squareTerminalPQ hn w i l +
            terminalB L n hn i l * squareTerminalPQ hn w i k) := by
  classical
  let Q := terminalQSmith L n
  by_cases hkl : k = l
  · subst l
    rw [if_pos rfl]
    unfold terminalCycleCoefficient squareTerminalQQ squareTerminalPQ
    simp only [if_true]
    simp_rw [terminalBoundary_coordinate_inr]
    simp only [terminalR0Basis_repr_inr]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only
    simp only [mul_add, mul_sub, sub_mul, Finset.sum_mul, Finset.mul_sum]
    ring_nf
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [if_neg hkl]
    have hkl' : (Sum.inr k : TerminalR0Index L n) ≠ Sum.inr l := by
      exact fun h ↦ hkl (Sum.inr_injective h)
    unfold terminalCycleCoefficient squareTerminalQQ squareTerminalPQ
    simp only [hkl', if_false]
    simp_rw [terminalBoundary_coordinate_inr]
    simp only [terminalR0Basis_repr_inr]
    have hcross :
        (∑ i, (terminalB L n hn i k *
              (∑ t : w.TerminalTraceRowIndex,
                let row := w.terminalTraceRowAt t
                row.coefficient *
                    (terminalPSmithSorted L n hn).relationBasis.repr
                      (terminalRelationR1 L n hn row.relation).1 i *
                  Q.ambientBasis.repr
                    (terminalFactorR0 L n (2 * n) row.factor).2 l) +
            terminalB L n hn i l *
              (∑ t : w.TerminalTraceRowIndex,
                let row := w.terminalTraceRowAt t
                row.coefficient *
                    (terminalPSmithSorted L n hn).relationBasis.repr
                      (terminalRelationR1 L n hn row.relation).1 i *
                  Q.ambientBasis.repr
                    (terminalFactorR0 L n (2 * n) row.factor).2 k))) =
          ∑ t : w.TerminalTraceRowIndex,
            let row := w.terminalTraceRowAt t
            ∑ i, (terminalB L n hn i k *
                  (row.coefficient *
                      (terminalPSmithSorted L n hn).relationBasis.repr
                        (terminalRelationR1 L n hn row.relation).1 i *
                    Q.ambientBasis.repr
                      (terminalFactorR0 L n (2 * n) row.factor).2 l) +
                terminalB L n hn i l *
                  (row.coefficient *
                      (terminalPSmithSorted L n hn).relationBasis.repr
                        (terminalRelationR1 L n hn row.relation).1 i *
                    Q.ambientBasis.repr
                      (terminalFactorR0 L n (2 * n) row.factor).2 k)) := by
      calc
        _ = (∑ i, terminalB L n hn i k *
                (∑ t : w.TerminalTraceRowIndex,
                  let row := w.terminalTraceRowAt t
                  row.coefficient *
                      (terminalPSmithSorted L n hn).relationBasis.repr
                        (terminalRelationR1 L n hn row.relation).1 i *
                    Q.ambientBasis.repr
                      (terminalFactorR0 L n (2 * n) row.factor).2 l)) +
              (∑ i, terminalB L n hn i l *
                (∑ t : w.TerminalTraceRowIndex,
                  let row := w.terminalTraceRowAt t
                  row.coefficient *
                      (terminalPSmithSorted L n hn).relationBasis.repr
                        (terminalRelationR1 L n hn row.relation).1 i *
                    Q.ambientBasis.repr
                      (terminalFactorR0 L n (2 * n) row.factor).2 k)) :=
            Finset.sum_add_distrib
        _ = (∑ t : w.TerminalTraceRowIndex,
                ∑ i, terminalB L n hn i k *
                  (let row := w.terminalTraceRowAt t
                   row.coefficient *
                       (terminalPSmithSorted L n hn).relationBasis.repr
                         (terminalRelationR1 L n hn row.relation).1 i *
                     Q.ambientBasis.repr
                       (terminalFactorR0 L n (2 * n) row.factor).2 l)) +
              (∑ t : w.TerminalTraceRowIndex,
                ∑ i, terminalB L n hn i l *
                  (let row := w.terminalTraceRowAt t
                   row.coefficient *
                       (terminalPSmithSorted L n hn).relationBasis.repr
                         (terminalRelationR1 L n hn row.relation).1 i *
                     Q.ambientBasis.repr
                       (terminalFactorR0 L n (2 * n) row.factor).2 k)) := by
            congr 1
            · simp_rw [Finset.mul_sum]
              exact Finset.sum_comm
            · simp_rw [Finset.mul_sum]
              exact Finset.sum_comm
        _ = _ := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro t ht
          dsimp only
          rw [← Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [hcross]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only
    simp only [mul_add, mul_sub, sub_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    ring_nf
    congr 1
    · congr 1
      first
      | funext i; ring
      | apply Finset.sum_congr rfl
        intro i hi
        ring
    · congr 1
      first
      | funext i; ring
      | apply Finset.sum_congr rfl
        intro i hi
        ring

/-- The terminal Smith conversion is deliberately isolated from the marked-square argument:
the latter has to supply exactly a zero symmetric boundary and the oriented primitive
coefficient.  Everything after those two facts is the already formalized integral quadratic
certificate. -/
private def terminalComparisonOfClosedSquare
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 3 ≤ n)
    (w : GoverningWitness n L a)
    (hcycle : ∀ i j : TerminalR0Index L n,
      terminalCycleCoefficient (by omega) w i j = 0)
    (hz : ((Coordinate.Data.CollectedExpression.zCoefficient
        (terminalData R (by omega))
        (squareTerminalCollectedExpression R (by omega) w) : ℤ) :
          ZMod (2 ^ R.topExponent)) = primitiveTopRead R (by omega) w.relationSide) :
    Coordinate.Data.CollectedExpression.Comparison
      (terminalData R (by omega))
      (squareTerminalCollectedExpression R (by omega) w)
      (primitiveTopRead R (by omega) w.relationSide) := by
  classical
  let hn1 : 1 ≤ n := by omega
  let D := terminalData R hn1
  let E := squareTerminalCollectedExpression R hn1 w
  let P := terminalPSmithSorted L n hn1
  have hdiag (i : TruncatedBasisIndex L (n - 1)) :
      squareTerminalPP hn1 w i i = 0 := by
    have h := hcycle (.inl i) (.inl i)
    rw [terminalCycleCoefficient_inl_inl hn1 w i i, if_pos rfl] at h
    have hd : ((P.diagonal i : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (P.diagonal_pos i))
    exact (Int.mul_eq_zero.mp h).resolve_left hd
  have hbelow {j i : TruncatedBasisIndex L (n - 1)} (hji : j < i) :
      squareTerminalPP hn1 w j i =
        (D.dRatio j i : ℤ) * (-squareTerminalPP hn1 w i j) := by
    have hne : j ≠ i := ne_of_lt hji
    have h := hcycle (.inl j) (.inl i)
    rw [terminalCycleCoefficient_inl_inl hn1 w j i, if_neg hne] at h
    have hdvd : P.diagonal j ∣ P.diagonal i :=
      terminalPSmithSorted_dvd_of_le R hn1 hji.le
    have hratioNat : P.diagonal j * D.dRatio j i = P.diagonal i := by
      exact Nat.mul_div_cancel' hdvd
    have hratio : (P.diagonal i : ℤ) =
        (P.diagonal j : ℤ) * (D.dRatio j i : ℤ) := by
      exact_mod_cast hratioNat.symm
    have hd : (P.diagonal j : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (P.diagonal_pos j))
    apply mul_left_cancel₀ hd
    calc
      (P.diagonal j : ℤ) * squareTerminalPP hn1 w j i =
          -(P.diagonal i : ℤ) * squareTerminalPP hn1 w i j := by
            linarith
      _ = (P.diagonal j : ℤ) *
          ((D.dRatio j i : ℤ) * (-squareTerminalPP hn1 w i j)) := by
            rw [hratio]
            ring
  have hupper (i : TruncatedBasisIndex L (n - 1))
      (k : FreeLieExactBasisIndex L n) :
      D.upperSkewMul E.u i k =
        -∑ j, terminalB L n hn1 j k * squareTerminalPP hn1 w j i := by
    change
      ((∑ j ∈ Finset.univ.filter (i < ·),
          (-squareTerminalPP hn1 w j i) * terminalB L n hn1 j k) -
        ∑ j ∈ Finset.univ.filter (· < i),
          (D.dRatio j i : ℤ) * (-squareTerminalPP hn1 w i j) *
            terminalB L n hn1 j k) = _
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy j i with hji | rfl | hij
    · simp only [hji, not_lt_of_ge hji.le, if_false, if_true, zero_sub]
      rw [hbelow hji]
      ring
    · simp only [lt_self_iff_false, if_false, sub_zero, hdiag]
      ring
    · simp only [hij, not_lt_of_ge hij.le, if_false, if_true, sub_zero]
      ring
  refine
    { xy_zero := ?_
      z_mod := hz
      yy_zero := ?_
      ySquare_zero := ?_ }
  · intro i k
    have h := hcycle (.inl i) (.inr k)
    rw [terminalCycleCoefficient_inl_inr hn1 w i k] at h
    unfold Coordinate.Data.CollectedExpression.xyCoefficient
    rw [hupper]
    change
      -(∑ j, terminalB L n hn1 j k * squareTerminalPP hn1 w j i) +
          (P.diagonal i : ℤ) * squareTerminalPQ hn1 w i k +
          squareTerminalQP hn1 w k i *
            ((terminalQSmith L n).diagonal k : ℤ) = 0
    linarith

  · intro k l hkl
    have h := hcycle (.inr k) (.inr l)
    rw [terminalCycleCoefficient_inr_inr hn1 w k l,
      if_neg (ne_of_lt hkl)] at h
    unfold Coordinate.Data.CollectedExpression.yyCoefficient
    simp only [squareTerminalCollectedExpression, terminalData,
      if_pos hkl.le, if_pos hkl]
    change
      -(∑ i, (squareTerminalPQ hn1 w i k * terminalB L n hn1 i l +
          terminalB L n hn1 i k * squareTerminalPQ hn1 w i l)) +
        ((terminalQSmith L n).diagonal k : ℤ) *
            squareTerminalQQ hn1 w k l +
        ((terminalQSmith L n).diagonal l : ℤ) *
            squareTerminalQQ hn1 w l k = 0
    have hsum :
        (∑ i, (squareTerminalPQ hn1 w i k * terminalB L n hn1 i l +
          terminalB L n hn1 i k * squareTerminalPQ hn1 w i l)) =
        ∑ i, (terminalB L n hn1 i k * squareTerminalPQ hn1 w i l +
          terminalB L n hn1 i l * squareTerminalPQ hn1 w i k) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    linarith
  · intro k
    have h := hcycle (.inr k) (.inr k)
    rw [terminalCycleCoefficient_inr_inr hn1 w k k, if_pos rfl] at h
    unfold Coordinate.Data.CollectedExpression.ySquareCoefficient
    simp only [squareTerminalCollectedExpression, terminalData,
      if_pos le_rfl, lt_self_iff_false, if_false]
    change
      -(∑ i, squareTerminalPQ hn1 w i k * terminalB L n hn1 i k) +
        ((terminalQSmith L n).diagonal k : ℤ) *
          (squareTerminalQQ hn1 w k k + 0) = 0
    have hsum :
        (∑ i, squareTerminalPQ hn1 w i k * terminalB L n hn1 i k) =
          ∑ i, terminalB L n hn1 i k * squareTerminalPQ hn1 w i k := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    linarith

private theorem primitiveTopRead_eq_zero_of_closedSquare
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 3 ≤ n)
    (w : GoverningWitness n L a)
    (hcycle : ∀ i j : TerminalR0Index L n,
      terminalCycleCoefficient (by omega) w i j = 0)
    (hz : ((Coordinate.Data.CollectedExpression.zCoefficient
        (terminalData R (by omega))
        (squareTerminalCollectedExpression R (by omega) w) : ℤ) :
          ZMod (2 ^ R.topExponent)) = primitiveTopRead R (by omega) w.relationSide) :
    primitiveTopRead R (by omega) w.relationSide = 0 := by
  let hn1 : 1 ≤ n := by omega
  let D := terminalData R hn1
  let E := squareTerminalCollectedExpression R hn1 w
  let comparison := terminalComparisonOfClosedSquare R hn w hcycle hz
  let system := Coordinate.Data.CollectedExpression.toCoefficientSystem
    D E comparison
  exact Coordinate.Data.coefficientSystem_vanishes D
    (pow_pos (by omega) R.topExponent)
    (fun i ↦ (terminalPSmithSorted L n hn1).diagonal_pos i)
    (terminalDataIdentities R hn) system

-/

/-! ## The repaired provenance-preserving square packet

The former `SquarePacket` turns an emitted homogeneous component into an unlabelled word.
That representation is retained above only until the closed-square bridge is replaced.  The
packet below is the replacement: both marked rows and ordinary component edges retain the
original relation, its context, its mark, and the placement of the ordinary factors.  A
component edge additionally stores the *actual* exact homogeneous piece being normalized; it
is never interpreted as a member of the relation ideal.
-/

private inductive ProvenancedSquarePacket
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) where
  | marked
      (root : CanonicalLieRelationsIdeal X)
      (context : RelationContext X (2 * n))
      (mark : Fin (2 * n + 1))
      (left right : List (TruncatedBasisIndex X (2 * n)))
  | component
      (root : CanonicalLieRelationsIdeal X)
      (context : RelationContext X (2 * n))
      (mark : Fin (2 * n + 1))
      (left right : List (TruncatedBasisIndex X (2 * n)))

private def ProvenancedSquarePacket.root
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    ProvenancedSquarePacket X n → CanonicalLieRelationsIdeal X
  | .marked r _ _ _ _ => r
  | .component r _ _ _ _ => r

private def ProvenancedSquarePacket.context
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    ProvenancedSquarePacket X n → RelationContext X (2 * n)
  | .marked _ c _ _ _ => c
  | .component _ c _ _ _ => c

private def ProvenancedSquarePacket.mark
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    ProvenancedSquarePacket X n → Fin (2 * n + 1)
  | .marked _ _ k _ _ => k
  | .component _ _ k _ _ => k

private def ProvenancedSquarePacket.left
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    ProvenancedSquarePacket X n →
      List (TruncatedBasisIndex X (2 * n))
  | .marked _ _ _ left _ => left
  | .component _ _ _ left _ => left

private def ProvenancedSquarePacket.right
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    ProvenancedSquarePacket X n →
      List (TruncatedBasisIndex X (2 * n))
  | .marked _ _ _ _ right => right
  | .component _ _ _ _ right => right

private def ProvenancedSquarePacket.value
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    ProvenancedSquarePacket X n →
      UEA ℤ (TruncatedFreeLie X (2 * n))
  | .marked r c k left right =>
      basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n))
            (truncatedHomogeneousBasis X (2 * n)) left *
        UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk X (2 * n)
            (c.applyFree X (markedPrefixFree X k.1 r))) *
        basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n))
            (truncatedHomogeneousBasis X (2 * n)) right
  | .component r c k left right =>
      basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n))
            (truncatedHomogeneousBasis X (2 * n)) left *
        UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk X (2 * n)
            (contextComponentExact X c r k.1 : CanonicalFreeLie X)) *
        basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n))
            (truncatedHomogeneousBasis X (2 * n)) right

private def ProvenancedSquarePacket.activeWeight
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    ProvenancedSquarePacket X n → ℕ
  | .marked _ c k _ _ => k.1 + c.weight X
  | .component _ c k _ _ => k.1 + c.weight X

/-- The deterministic repaired rewrite.  Transfers are performed first.  Once `right` is
empty, a non-wall marked row lowers its mark and emits the complete contextual component.
A component edge is then moved back across the factors on its left.  Its negative bracket
child is the complete shifted contextual component, so it cancels the corresponding positive
marked transfer/truncation edge before any basis-dependent PBW expansion. -/
private def provenancedSquareExpansion
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    ProvenancedSquarePacket X n →
      Option (List (ℤ × ProvenancedSquarePacket X n)) := by
  classical
  intro p
  exact match p with
  | .component r c k left right =>
      match hleft : left.reverse with
      | [] => none
      | x :: leftRev =>
          let leftPrefix := leftRev.reverse
          let main : ProvenancedSquarePacket X n :=
            .component r c k leftPrefix (x :: right)
          if hweight : k.1 + (c.lieRight x).weight X ≤ 2 * n then
            some
              [(1, main),
               (-1, .component r (.lieRight c x) k leftPrefix right)]
          else some [(1, main)]
  | .marked r c k left (x :: right) =>
      some
        [(1, .marked r c k (left ++ [x]) right),
         (1, .marked r (.lieRight c x) k left right)]
  | .marked r c k left [] =>
      if hk : k.1 = 0 then some []
      else if hwall :
          (left = [] ∧ k.1 + c.weight X = n + 1) ∨
          (∃ x, left = [x] ∧ k.1 + c.weight X = n) then
        none
      else
        let k' : Fin (2 * n + 1) := ⟨k.1 - 1, by omega⟩
        let residual : ProvenancedSquarePacket X n :=
          .marked r c k' left []
        if hweight : k.1 + c.weight X ≤ 2 * n then
          some
            [(1, residual),
             (1, .component r c k left [])]
        else some [(1, residual)]

private def provenancedSquareComplexity
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    ProvenancedSquarePacket X n → ℕ × (ℕ × ℕ)
  | .marked _ _ k _ right => (1, right.length, k.1)
  | .component _ _ _ left _ => (0, left.length, 0)

private def ProvenancedSquareDescent
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    (new old : ProvenancedSquarePacket X n) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
    (provenancedSquareComplexity X new)
    (provenancedSquareComplexity X old)

private theorem provenancedSquareDescent_wellFounded
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    WellFounded (ProvenancedSquareDescent X (n := n)) :=
  InvImage.wf (provenancedSquareComplexity X)
    (Nat.lt_wfRel.wf.prod_lex
      (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))

private theorem provenancedSquareExpansion_decreases
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {p : ProvenancedSquarePacket X n}
    {qs : List (ℤ × ProvenancedSquarePacket X n)}
    (hp : provenancedSquareExpansion X n p = some qs) :
    ∀ q ∈ qs, ProvenancedSquareDescent X q.2 p := by
  classical
  intro q hq
  cases p with
  | component r c k left right =>
      simp only [provenancedSquareExpansion] at hp
      split at hp
      · contradiction
      · rename_i x leftRev hleft
        have hleftEq : left = leftRev.reverse ++ [x] := by
          have h := congrArg List.reverse hleft
          simpa using h
        split at hp
        · rcases Option.some.inj hp with rfl
          rcases List.mem_pair.mp hq with hq | hq <;> subst q <;>
            unfold ProvenancedSquareDescent provenancedSquareComplexity <;>
            apply Prod.Lex.right 0 <;>
            exact Prod.Lex.left 0 0 (by simp [hleftEq])
        · rcases Option.some.inj hp with rfl
          simp only [List.mem_singleton] at hq
          subst q
          unfold ProvenancedSquareDescent provenancedSquareComplexity
          apply Prod.Lex.right 0
          exact Prod.Lex.left 0 0 (by simp [hleftEq])
  | marked r c k left right =>
      cases right with
      | cons x right =>
          simp only [provenancedSquareExpansion, Option.some.injEq] at hp
          subst qs
          rcases List.mem_pair.mp hq with hq | hq <;> subst q
          · unfold ProvenancedSquareDescent provenancedSquareComplexity
            apply Prod.Lex.right 1
            exact Prod.Lex.left k.1 k.1 (by simp)
          · unfold ProvenancedSquareDescent provenancedSquareComplexity
            apply Prod.Lex.right 1
            exact Prod.Lex.left k.1 k.1 (by simp)
      | nil =>
          simp only [provenancedSquareExpansion] at hp
          split at hp
          · rcases Option.some.inj hp with rfl
            simp at hq
          · split at hp
            · contradiction
            · rename_i hk hwall
              split at hp
              · rename_i hweight
                rcases Option.some.inj hp with rfl
                rcases List.mem_pair.mp hq with hq | hq <;> subst q
                · unfold ProvenancedSquareDescent provenancedSquareComplexity
                  apply Prod.Lex.right 1
                  apply Prod.Lex.right 0
                  change k.1 - 1 < k.1
                  omega
                · unfold ProvenancedSquareDescent provenancedSquareComplexity
                  apply Prod.Lex.left
                  omega
              · rcases Option.some.inj hp with rfl
                simp only [List.mem_singleton] at hq
                subst q
                unfold ProvenancedSquareDescent provenancedSquareComplexity
                apply Prod.Lex.right 1
                apply Prod.Lex.right 0
                change k.1 - 1 < k.1
                omega

private theorem provenancedSquareExpansion_preserves
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {p : ProvenancedSquarePacket X n}
    {qs : List (ℤ × ProvenancedSquarePacket X n)}
    (hp : provenancedSquareExpansion X n p = some qs) :
    (qs.map fun q ↦ q.1 • ProvenancedSquarePacket.value X n q.2).sum =
      ProvenancedSquarePacket.value X n p := by
  classical
  cases p with
  | component r c k left right =>
      simp only [provenancedSquareExpansion] at hp
      split at hp
      · contradiction
      · rename_i x leftRev hleft
        have hleftEq : left = leftRev.reverse ++ [x] := by
          have h := congrArg List.reverse hleft
          simpa using h
        let b := truncatedHomogeneousBasis X (2 * n)
        let a := truncatedFreeLieMk X (2 * n)
          (contextComponentExact X c r k.1 : CanonicalFreeLie X)
        let xv := b x
        let lw := word ℤ (TruncatedFreeLie X (2 * n))
          (leftRev.reverse.map b)
        let rw' := word ℤ (TruncatedFreeLie X (2 * n))
          (right.map b)
        have hxv : xv = truncatedFreeLieMk X (2 * n)
            (homogeneousBasisLift X x) := by
          simpa only [xv, b, homogeneousBasisLift,
            truncatedBasisWeight] using
              (truncatedHomogeneousBasis_apply X (2 * n) x)
        have hcorr : truncatedFreeLieMk X (2 * n)
              (contextComponentExact X (.lieRight c x) r k.1 :
                CanonicalFreeLie X) = ⁅a, xv⁆ := by
          dsimp only [a, contextComponentExact, RelationContext.applyFree]
          rw [LieHom.map_lie, hxv]
        have hswap := iota_mul_iota_swap ℤ
          (TruncatedFreeLie X (2 * n)) a xv
        split at hp
        · rcases Option.some.inj hp with rfl
          simp only [List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, one_smul, neg_one_smul, add_zero]
          unfold ProvenancedSquarePacket.value
          rw [hleftEq]
          simp only [basisWord, List.map_append, List.map_singleton,
            List.map_cons, List.map_nil, word_append, word_cons,
            word_nil, mul_one]
          rw [hcorr]
          rw [← sub_eq_add_neg]
          change
            lw * UniversalEnvelopingAlgebra.ι ℤ a *
                  (UniversalEnvelopingAlgebra.ι ℤ xv * rw') -
                lw * UniversalEnvelopingAlgebra.ι ℤ ⁅a, xv⁆ * rw' =
              (lw * UniversalEnvelopingAlgebra.ι ℤ xv) *
                UniversalEnvelopingAlgebra.ι ℤ a * rw'
          calc
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ a *
                  UniversalEnvelopingAlgebra.ι ℤ xv -
                UniversalEnvelopingAlgebra.ι ℤ ⁅a, xv⁆) * rw' := by
                  noncomm_ring
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
                UniversalEnvelopingAlgebra.ι ℤ a) * rw' := by
                  rw [hswap]
                  noncomm_ring
            _ = _ := by noncomm_ring
        · rename_i hweight
          rcases Option.some.inj hp with rfl
          have hbracketZero : truncatedFreeLieMk X (2 * n)
              (contextComponentExact X (.lieRight c x) r k.1 :
                CanonicalFreeLie X) = 0 := by
            apply (LieSubmodule.Quotient.mk_eq_zero'
              (N := lowerCentralSeries ℤ
                (CanonicalFreeLie X) (2 * n))).mpr
            have hhigh :
                (contextComponentExact X (.lieRight c x) r k.1 :
                  CanonicalFreeLie X) ∈
                  FreeLieDimension.lieHigh X (2 * n + 1) := by
              obtain ⟨words, hwords, hvalue⟩ :=
                (contextComponentExact X (.lieRight c x) r k.1).property
              refine ⟨words, ?_, hvalue⟩
              intro w hw
              exact le_trans (by omega) (hwords hw).ge
            simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries X (2 * n)]
              using hhigh
          rw [hcorr] at hbracketZero
          rw [hbracketZero, map_zero, add_zero] at hswap
          simp only [List.map_singleton, List.sum_singleton, one_smul]
          unfold ProvenancedSquarePacket.value
          rw [hleftEq]
          simp only [basisWord, List.map_append, List.map_singleton,
            List.map_cons, List.map_nil, word_append, word_cons,
            word_nil, mul_one]
          change
            lw * UniversalEnvelopingAlgebra.ι ℤ a *
                (UniversalEnvelopingAlgebra.ι ℤ xv * rw') =
              (lw * UniversalEnvelopingAlgebra.ι ℤ xv) *
                UniversalEnvelopingAlgebra.ι ℤ a * rw'
          calc
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ a *
                UniversalEnvelopingAlgebra.ι ℤ xv) * rw' := by noncomm_ring
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
                UniversalEnvelopingAlgebra.ι ℤ a) * rw' := by rw [hswap]
            _ = _ := by noncomm_ring
  | marked r c k left right =>
      cases right with
      | cons x right =>
          simp only [provenancedSquareExpansion, Option.some.injEq] at hp
          subst qs
          simp only [List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, one_smul, add_zero]
          let b := truncatedHomogeneousBasis X (2 * n)
          let a := truncatedFreeLieMk X (2 * n)
            (c.applyFree X (markedPrefixFree X k.1 r))
          let xv := b x
          have hxv : xv = truncatedFreeLieMk X (2 * n)
              (homogeneousBasisLift X x) := by
            simpa only [xv, b, homogeneousBasisLift,
              truncatedBasisWeight] using
                (truncatedHomogeneousBasis_apply X (2 * n) x)
          have hcorr : truncatedFreeLieMk X (2 * n)
                ((RelationContext.lieRight c x).applyFree X
                  (markedPrefixFree X k.1 r)) = ⁅a, xv⁆ := by
            change truncatedFreeLieMk X (2 * n)
                ⁅c.applyFree X (markedPrefixFree X k.1 r),
                  homogeneousBasisLift X x⁆ = _
            rw [LieHom.map_lie, hxv]
          have hswap := iota_mul_iota_swap ℤ
            (TruncatedFreeLie X (2 * n)) a xv
          unfold ProvenancedSquarePacket.value
          simp only [basisWord, List.map_append, List.map_singleton,
            List.map_cons, List.map_nil, word_append, word_cons,
            word_nil, mul_one]
          rw [hcorr]
          let lw := word ℤ (TruncatedFreeLie X (2 * n))
            (left.map b)
          let rw' := word ℤ (TruncatedFreeLie X (2 * n))
            (right.map b)
          change lw * UniversalEnvelopingAlgebra.ι ℤ xv *
                UniversalEnvelopingAlgebra.ι ℤ a * rw' +
              lw * UniversalEnvelopingAlgebra.ι ℤ ⁅a, xv⁆ * rw' =
            lw * UniversalEnvelopingAlgebra.ι ℤ a *
              (UniversalEnvelopingAlgebra.ι ℤ xv * rw')
          calc
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
                    UniversalEnvelopingAlgebra.ι ℤ a +
                  UniversalEnvelopingAlgebra.ι ℤ ⁅a, xv⁆) * rw' := by
                    noncomm_ring
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ a *
                    UniversalEnvelopingAlgebra.ι ℤ xv) * rw' := by
                    rw [← hswap]
            _ = _ := by noncomm_ring
      | nil =>
          simp only [provenancedSquareExpansion] at hp
          split at hp
          · rename_i hk
            rcases Option.some.inj hp with rfl
            have hkFin : k = ⟨0, by omega⟩ := by
              apply Fin.ext
              exact hk
            rw [hkFin]
            change 0 =
              basisWord ℤ (TruncatedFreeLie X (2 * n))
                  (TruncatedBasisIndex X (2 * n))
                    (truncatedHomogeneousBasis X (2 * n)) left *
                UniversalEnvelopingAlgebra.ι ℤ
                  (truncatedFreeLieMk X (2 * n) (c.applyFree X 0)) * 1
            rw [show c.applyFree X 0 = 0 from (c.linearMap X).map_zero,
              map_zero, map_zero]
            simp
          · rename_i hk
            split at hp
            · contradiction
            · rename_i hwall
              let k' : Fin (2 * n + 1) := ⟨k.1 - 1, by omega⟩
              let lword := basisWord ℤ (TruncatedFreeLie X (2 * n))
                (TruncatedBasisIndex X (2 * n))
                  (truncatedHomogeneousBasis X (2 * n)) left
              have hkpos : 0 < k.1 := Nat.pos_of_ne_zero hk
              have hprefix : c.applyFree X (markedPrefixFree X k.1 r) =
                  c.applyFree X (markedPrefixFree X k'.1 r) +
                    (contextComponentExact X c r k.1 : CanonicalFreeLie X) := by
                have h := congrArg (c.linearMap X)
                  (markedPrefixFree_step X hkpos r)
                rw [map_add] at h
                change c.applyFree X (markedPrefixFree X k.1 r) =
                  c.applyFree X (markedPrefixFree X (k.1 - 1) r) +
                    c.applyFree X
                      ((⟨freeLieLengthComponent X k.1
                            (r : CanonicalFreeLie X),
                          freeLieLengthComponent_mem_exact X k.1
                            (r : CanonicalFreeLie X)⟩ : freeLieExact X k.1) :
                        CanonicalFreeLie X) at h
                simpa [k', RelationContext.linearMap,
                  contextComponentExact] using h
              split at hp
              · rename_i hweight
                rcases Option.some.inj hp with rfl
                simp only [List.map_cons, List.map_nil, List.sum_cons,
                  List.sum_nil, one_smul, add_zero]
                change
                  lword * UniversalEnvelopingAlgebra.ι ℤ
                        (truncatedFreeLieMk X (2 * n)
                          (c.applyFree X (markedPrefixFree X k'.1 r))) * 1 +
                    lword * UniversalEnvelopingAlgebra.ι ℤ
                        (truncatedFreeLieMk X (2 * n)
                          (contextComponentExact X c r k.1 :
                            CanonicalFreeLie X)) * 1 =
                  lword * UniversalEnvelopingAlgebra.ι ℤ
                        (truncatedFreeLieMk X (2 * n)
                          (c.applyFree X (markedPrefixFree X k.1 r))) * 1
                rw [hprefix, map_add, map_add]
                noncomm_ring
              · rename_i hweight
                rcases Option.some.inj hp with rfl
                have hcomponentZero : truncatedFreeLieMk X (2 * n)
                    (contextComponentExact X c r k.1 : CanonicalFreeLie X) = 0 := by
                  apply (LieSubmodule.Quotient.mk_eq_zero'
                    (N := lowerCentralSeries ℤ
                      (CanonicalFreeLie X) (2 * n))).mpr
                  have hhigh :
                      (contextComponentExact X c r k.1 : CanonicalFreeLie X) ∈
                        FreeLieDimension.lieHigh X (2 * n + 1) := by
                    obtain ⟨p, hp, hpvalue⟩ :=
                      (contextComponentExact X c r k.1).property
                    refine ⟨p, ?_, hpvalue⟩
                    intro word hword
                    exact le_trans (by omega) (hp hword).ge
                  simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries X (2 * n)]
                    using hhigh
                simp only [List.map_singleton, List.sum_singleton, one_smul]
                change
                  lword * UniversalEnvelopingAlgebra.ι ℤ
                      (truncatedFreeLieMk X (2 * n)
                        (c.applyFree X (markedPrefixFree X k'.1 r))) * 1 =
                    lword * UniversalEnvelopingAlgebra.ι ℤ
                      (truncatedFreeLieMk X (2 * n)
                        (c.applyFree X (markedPrefixFree X k.1 r))) * 1
                rw [hprefix, map_add, map_add, hcomponentZero,
                  map_zero, add_zero]

private def provenancedSquareCollector
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    FiniteTaggedCollector (ProvenancedSquarePacket X n)
      (UEA ℤ (TruncatedFreeLie X (2 * n))) where
  relation := ProvenancedSquareDescent X
  wellFounded := provenancedSquareDescent_wellFounded X n
  expansion := provenancedSquareExpansion X n
  value := ProvenancedSquarePacket.value X n
  decreases := provenancedSquareExpansion_decreases X n
  preserves := provenancedSquareExpansion_preserves X n

/-! ### Initial packets and the labelled trace -/

private def provenancedSquarePacketsOfMultiplier
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (r : CanonicalLieRelationsIdeal L)
    (z : UEA ℤ (TruncatedFreeLie L (2 * n))) :
    ProvenancedSquarePacket L n →₀ ℤ :=
  ((truncatedPBWLinearEquiv L (2 * n)).symm z).sum fun e c ↦
    Finsupp.single
      (.marked r .hole ⟨2 * n, by omega⟩ [] (exponentWord L e)) c

private theorem evaluate_provenancedSquarePacketsOfMultiplier
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (r : CanonicalLieRelationsIdeal L)
    (z : UEA ℤ (TruncatedFreeLie L (2 * n))) :
    (provenancedSquareCollector L n).evaluate
        (provenancedSquarePacketsOfMultiplier L n r z) =
      UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk L (2 * n) (r : CanonicalFreeLie L)) * z := by
  classical
  unfold provenancedSquarePacketsOfMultiplier
  rw [map_finsuppSum]
  let p := (truncatedPBWLinearEquiv L (2 * n)).symm z
  calc
    p.sum (fun e c ↦
        (provenancedSquareCollector L n).evaluate
          (Finsupp.single
            (.marked r .hole ⟨2 * n, by omega⟩ [] (exponentWord L e)) c)) =
      p.sum (fun e c ↦ c •
        (UniversalEnvelopingAlgebra.ι ℤ
            (truncatedFreeLieMk L (2 * n) (r : CanonicalFreeLie L)) *
          orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
            (TruncatedBasisIndex L (2 * n))
              (truncatedHomogeneousBasis L (2 * n)) e)) := by
        apply Finsupp.sum_congr
        intro e he
        rw [FiniteTaggedCollector.evaluate_single]
        simp only [provenancedSquareCollector,
          ProvenancedSquarePacket.value, basisWord_nil, one_mul,
          RelationContext.applyFree]
        rw [truncated_markedPrefixFree_top, basisWord_exponentWord]
    _ = UniversalEnvelopingAlgebra.ι ℤ
          (truncatedFreeLieMk L (2 * n) (r : CanonicalFreeLie L)) *
        (truncatedPBWLinearEquiv L (2 * n)) p := by
          let ir := UniversalEnvelopingAlgebra.ι ℤ
            (truncatedFreeLieMk L (2 * n) (r : CanonicalFreeLie L))
          calc
            p.sum (fun e c ↦ c •
                (ir * orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
                  (TruncatedBasisIndex L (2 * n))
                    (truncatedHomogeneousBasis L (2 * n)) e)) =
              ir * p.sum (fun e c ↦ c •
                orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
                  (TruncatedBasisIndex L (2 * n))
                    (truncatedHomogeneousBasis L (2 * n)) e) := by
                rw [Finsupp.mul_sum]
                apply Finsupp.sum_congr
                intro e he
                exact (mul_smul_comm (p e) ir
                  (orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
                    (TruncatedBasisIndex L (2 * n))
                      (truncatedHomogeneousBasis L (2 * n)) e)).symm
            _ = ir * (truncatedPBWLinearEquiv L (2 * n)) p := by rfl
    _ = _ := by rw [LinearEquiv.apply_symm_apply]

private def GoverningWitness.provenancedSquareInitialPackets
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : ProvenancedSquarePacket L n →₀ ℤ :=
  w.relationWords.sum fun p c ↦ c •
    provenancedSquarePacketsOfMultiplier L n p.1
      (word ℤ (TruncatedFreeLie L (2 * n))
        (p.2.map fun x ↦
          truncatedFreeLieMk L (2 * n) (FreeLieAlgebra.of ℤ x)))

private theorem GoverningWitness.evaluate_provenancedSquareInitialPackets
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (provenancedSquareCollector L n).evaluate
        w.provenancedSquareInitialPackets = w.relationSide := by
  classical
  unfold GoverningWitness.provenancedSquareInitialPackets
    GoverningWitness.relationSide
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, evaluate_provenancedSquarePacketsOfMultiplier]

private def GoverningWitness.provenancedSquareTrace
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    List (RewriteCell (provenancedSquareCollector L n)) := by
  classical
  exact w.provenancedSquareInitialPackets.support.toList.flatMap fun p ↦
    rewriteTrace (provenancedSquareCollector L n) p []
      (w.provenancedSquareInitialPackets p)

/-- A root label for the global occurrence ledger.  Local child labels are prepended to this
final entry, so occurrences belonging to distinct initial packets cannot collide. -/
private abbrev GoverningWitness.ProvenancedRootIndex
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :=
  Fin w.provenancedSquareInitialPackets.support.toList.length

private def GoverningWitness.provenancedRootAt
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) (t : w.ProvenancedRootIndex) :
    ProvenancedSquarePacket L n :=
  w.provenancedSquareInitialPackets.support.toList.get t

private def GoverningWitness.provenancedGlobalInitialOccurrences
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : Occurrence (ProvenancedSquarePacket L n) →₀ ℤ := by
  classical
  exact ∑ t : w.ProvenancedRootIndex,
    Finsupp.single ([t.1], w.provenancedRootAt t)
      (w.provenancedSquareInitialPackets (w.provenancedRootAt t))

private def GoverningWitness.provenancedGlobalFrontier
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : Occurrence (ProvenancedSquarePacket L n) →₀ ℤ := by
  classical
  exact ∑ t : w.ProvenancedRootIndex,
    rewriteFrontier (provenancedSquareCollector L n)
      (w.provenancedRootAt t) [t.1]
      (w.provenancedSquareInitialPackets (w.provenancedRootAt t))

/-- The genuinely global prefix ledger.  Unlike the earlier convenience trace, its paths also
remember the initial support entry. -/
private theorem GoverningWitness.provenancedGlobalPrefixLedger
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    w.provenancedGlobalInitialOccurrences - w.provenancedGlobalFrontier =
      ∑ t : w.ProvenancedRootIndex,
        traceBoundary (provenancedSquareCollector L n)
          (rewriteTrace (provenancedSquareCollector L n)
            (w.provenancedRootAt t) [t.1]
            (w.provenancedSquareInitialPackets (w.provenancedRootAt t))) := by
  classical
  unfold GoverningWitness.provenancedGlobalInitialOccurrences
    GoverningWitness.provenancedGlobalFrontier
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact prefixLedgerAt (provenancedSquareCollector L n)
    (w.provenancedRootAt t) [t.1]
    (w.provenancedSquareInitialPackets (w.provenancedRootAt t))

private def GoverningWitness.provenancedSquareFrontier
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : ProvenancedSquarePacket L n →₀ ℤ :=
  w.provenancedSquareInitialPackets.sum fun p c ↦
    c • (provenancedSquareCollector L n).normalForm p

private theorem GoverningWitness.evaluate_provenancedSquareFrontier
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (provenancedSquareCollector L n).evaluate
        w.provenancedSquareFrontier = w.relationSide := by
  classical
  unfold GoverningWitness.provenancedSquareFrontier
  rw [map_finsuppSum]
  calc
    w.provenancedSquareInitialPackets.sum (fun p c ↦
        (provenancedSquareCollector L n).evaluate
          (c • (provenancedSquareCollector L n).normalForm p)) =
      w.provenancedSquareInitialPackets.sum (fun p c ↦
        c • (provenancedSquareCollector L n).value p) := by
          apply Finsupp.sum_congr
          intro p hp
          rw [map_zsmul, FiniteTaggedCollector.evaluate_normalForm]
    _ = (provenancedSquareCollector L n).evaluate
        w.provenancedSquareInitialPackets := rfl
    _ = w.relationSide := w.evaluate_provenancedSquareInitialPackets

/-! For the load-bearing closed-square fold we start after the full-relation transfer
collector.  At this point every row has `right = []`; putting its already contextualized full
relation at the top mark avoids repeating the transfer proof inside the two-filtered fold. -/

private def collectedRowsToProvenanced
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (c : FullRelationRow L (2 * n) →₀ ℤ) :
    ProvenancedSquarePacket L n →₀ ℤ :=
  c.sum fun row z ↦
    Finsupp.single
      (.marked row.relation .hole ⟨2 * n, by omega⟩ row.left []) z

private theorem evaluate_collectedRowsToProvenanced
    (L : Type u) [LieRing L] [Finite L] (n : ℕ)
    (c : FullRelationRow L (2 * n) →₀ ℤ)
    (hnormal : ∀ row, row.right ≠ [] → c row = 0) :
    (provenancedSquareCollector L n).evaluate
        (collectedRowsToProvenanced L n c) =
      (fullRelationRowCollector L (2 * n)).evaluate c := by
  classical
  unfold collectedRowsToProvenanced
  rw [map_finsuppSum]
  simp_rw [FiniteTaggedCollector.evaluate_single]
  apply Finsupp.sum_congr
  intro row hrow
  cases row with
  | mk left relation right =>
      have hright : right = [] := by
        by_contra hne
        exact Finsupp.mem_support_iff.mp hrow
          (hnormal { left := left, relation := relation, right := right } hne)
      subst right
      change c { left := left, relation := relation, right := [] } •
          ProvenancedSquarePacket.value L n
            (.marked relation .hole ⟨2 * n, by omega⟩ left []) =
        c { left := left, relation := relation, right := [] } •
          FullRelationRow.value L (2 * n)
            { left := left, relation := relation, right := [] }
      simp only [ProvenancedSquarePacket.value, FullRelationRow.value,
        basisWord_nil, mul_one, RelationContext.applyFree]
      rw [truncated_markedPrefixFree_top]

private def GoverningWitness.closedSquareInitialPackets
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : ProvenancedSquarePacket L n →₀ ℤ :=
  collectedRowsToProvenanced L n
    (collectRowLedger L (2 * n) w.initialRows)

private theorem GoverningWitness.evaluate_closedSquareInitialPackets
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (provenancedSquareCollector L n).evaluate
        w.closedSquareInitialPackets = w.relationSide := by
  rw [GoverningWitness.closedSquareInitialPackets,
    evaluate_collectedRowsToProvenanced]
  · exact w.evaluate_collectedRows
  · intro row hright
    exact collectRowLedger_apply_eq_zero_of_right_ne_nil L (2 * n)
      w.initialRows row hright

private def GoverningWitness.closedSquareFrontier
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) : ProvenancedSquarePacket L n →₀ ℤ :=
  w.closedSquareInitialPackets.sum fun p c ↦
    c • (provenancedSquareCollector L n).normalForm p

private theorem GoverningWitness.evaluate_closedSquareFrontier
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    (provenancedSquareCollector L n).evaluate
        w.closedSquareFrontier = w.relationSide := by
  classical
  unfold GoverningWitness.closedSquareFrontier
  rw [map_finsuppSum]
  calc
    w.closedSquareInitialPackets.sum (fun p c ↦
        (provenancedSquareCollector L n).evaluate
          (c • (provenancedSquareCollector L n).normalForm p)) =
      w.closedSquareInitialPackets.sum (fun p c ↦
        c • ProvenancedSquarePacket.value L n p) := by
          apply Finsupp.sum_congr
          intro p hp
          rw [map_zsmul, FiniteTaggedCollector.evaluate_normalForm]
          rfl
    _ = (provenancedSquareCollector L n).evaluate
        w.closedSquareInitialPackets := rfl
    _ = w.relationSide := w.evaluate_closedSquareInitialPackets

/- The three compile-time examples are deliberately concrete one-step checks.  In particular,
the last one verifies the formerly broken path: after a transfer and then a truncation, the
emitted component still exposes the unchanged `root`, shifted `context`, and original `mark`.
-/

private example
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n))
    (k : Fin (2 * n + 1))
    (left right : List (TruncatedBasisIndex X (2 * n)))
    (x : TruncatedBasisIndex X (2 * n)) :
    provenancedSquareExpansion X n (.marked r c k left (x :: right)) =
      some
        [(1, .marked r c k (left ++ [x]) right),
         (1, .marked r (.lieRight c x) k left right)] := by
  simp [provenancedSquareExpansion]

private example
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n))
    (k : Fin (2 * n + 1))
    (left : List (TruncatedBasisIndex X (2 * n)))
    (hk : k.1 ≠ 0)
    (hwall : ¬((left = [] ∧ k.1 + c.weight X = n + 1) ∨
      ∃ x, left = [x] ∧ k.1 + c.weight X = n))
    (hweight : k.1 + c.weight X ≤ 2 * n) :
    provenancedSquareExpansion X n (.marked r c k left []) =
      some
        [(1, .marked r c ⟨k.1 - 1, by omega⟩ left []),
         (1, .component r c k left [])] := by
  simp only [provenancedSquareExpansion, hk, hwall, hweight]
  simp

private example
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n))
    (k : Fin (2 * n + 1))
    (left : List (TruncatedBasisIndex X (2 * n)))
    (x : TruncatedBasisIndex X (2 * n))
    (hk : k.1 ≠ 0)
    (hwall : ¬((left = [] ∧
          k.1 + (RelationContext.lieRight c x).weight X = n + 1) ∨
        ∃ y, left = [y] ∧
          k.1 + (RelationContext.lieRight c x).weight X = n))
    (hweight :
      k.1 + (RelationContext.lieRight c x).weight X ≤ 2 * n) :
    let edge : ProvenancedSquarePacket X n :=
      .component r (.lieRight c x) k left []
    provenancedSquareExpansion X n (.marked r c k left [x]) =
        some
          [(1, .marked r c k (left ++ [x]) []),
           (1, .marked r (.lieRight c x) k left [])] ∧
      provenancedSquareExpansion X n
          (.marked r (.lieRight c x) k left []) =
        some
          [(1, .marked r (.lieRight c x) ⟨k.1 - 1, by omega⟩ left []),
           (1, edge)] ∧
      edge.root X = r ∧ edge.context X = .lieRight c x ∧
        edge.mark X = k := by
  dsimp only
  constructor
  · simp [provenancedSquareExpansion]
  constructor
  · simp only [provenancedSquareExpansion, hk, hwall, hweight]
    simp
  · exact ⟨rfl, rfl, rfl⟩

/-! ### Erasure to the retained full-relation ledger -/

private def ProvenancedSquarePacket.eraseMarked
    (X : Type u) [LieRing X] [Finite X] {n : ℕ} :
    ProvenancedSquarePacket X n → Option (FullRelationRow X (2 * n))
  | .marked r c _ left right =>
      some { left := left, relation := c.relation X r, right := right }
  | .component _ _ _ _ _ => none

private def provenancedMarkedErasureLinear
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    : (ProvenancedSquarePacket X n →₀ ℤ) →ₗ[ℤ]
      (FullRelationRow X (2 * n) →₀ ℤ) := by
  classical
  exact Finsupp.lsum ℤ fun p ↦
    match p.eraseMarked X with
    | none => 0
    | some row => Finsupp.lsingle row

private def eraseProvenancedMarkedRows
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (s : ProvenancedSquarePacket X n →₀ ℤ) :
    FullRelationRow X (2 * n) →₀ ℤ :=
  provenancedMarkedErasureLinear X n s

private theorem relationBracketRight_contextRelation
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n))
    (x : TruncatedBasisIndex X (2 * n)) :
    relationBracketRight X (c.relation X r) x =
      (c.lieRight x).relation X r := by
  apply Subtype.ext
  rfl

/-- A transfer step is literally the old full-relation step after forgetting only the mark.
Component edges are not involved in this statement and are never coerced to relations. -/
private theorem provenancedSquareExpansion_erase_transfer
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n))
    (k : Fin (2 * n + 1))
    (left right : List (TruncatedBasisIndex X (2 * n)))
    (x : TruncatedBasisIndex X (2 * n)) :
    (provenancedSquareExpansion X n
        (.marked r c k left (x :: right))).map
        (List.filterMap fun q ↦
          match q.2.eraseMarked X with
          | none => none
          | some row => some (q.1, row)) =
      fullRelationRowExpansion X (2 * n)
        { left := left, relation := c.relation X r, right := x :: right } := by
  simp [provenancedSquareExpansion, fullRelationRowExpansion,
    ProvenancedSquarePacket.eraseMarked,
    relationBracketRight_contextRelation]

private theorem eraseProvenancedSquarePacketsOfMultiplier
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (r : CanonicalLieRelationsIdeal X)
    (z : UEA ℤ (TruncatedFreeLie X (2 * n))) :
    eraseProvenancedMarkedRows X n
        (provenancedSquarePacketsOfMultiplier X n r z) =
      rowsOfMultiplier X (2 * n) r z := by
  classical
  unfold eraseProvenancedMarkedRows
    provenancedSquarePacketsOfMultiplier rowsOfMultiplier
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro e he
  simp [provenancedMarkedErasureLinear,
    ProvenancedSquarePacket.eraseMarked]
  have hhole :
      (RelationContext.hole : RelationContext X (2 * n)).relation X r = r := by
    apply Subtype.ext
    rfl
  rw [hhole]

private theorem GoverningWitness.erase_provenancedSquareInitialPackets
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    eraseProvenancedMarkedRows L n w.provenancedSquareInitialPackets =
      w.initialRows := by
  classical
  unfold GoverningWitness.provenancedSquareInitialPackets
    GoverningWitness.initialRows eraseProvenancedMarkedRows
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul]
  exact congrArg (fun s ↦ w.relationWords p • s)
    (eraseProvenancedSquarePacketsOfMultiplier L n p.1
      (word ℤ (TruncatedFreeLie L (2 * n))
        (p.2.map fun x ↦
          truncatedFreeLieMk L (2 * n) (FreeLieAlgebra.of ℤ x))))

private theorem GoverningWitness.collectRowLedger_erased_initial
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    collectRowLedger L (2 * n)
        (eraseProvenancedMarkedRows L n
          w.provenancedSquareInitialPackets) =
      collectRowLedger L (2 * n) w.initialRows := by
  rw [w.erase_provenancedSquareInitialPackets]

private example
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) (hn : 1 ≤ n)
    (r : CanonicalLieRelationsIdeal X)
    (c : RelationContext X (2 * n))
    (k : Fin (2 * n + 1))
    (x : TruncatedBasisIndex X (2 * n))
    (hactive : k.1 + c.weight X = n) :
    terminalLowQuadraticPBW X n hn
        (ProvenancedSquarePacket.value X n
          (.marked r c k [x] [])) =
      terminalBasisPolynomial (terminalR0Basis X n hn)
          (terminalBoundary X n hn
            (terminalRelationR1 X n hn (c.relation X r))) *
        terminalBasisPolynomial (terminalR0Basis X n hn)
          (terminalFactorR0 X n (2 * n) x) := by
  simpa only [ProvenancedSquarePacket.value, basisWord_cons,
    basisWord_nil, mul_one] using
      terminalWallQuadratic_left X n hn r c k.1 hactive x

private example
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 1 ≤ n)
    (w : GoverningWitness n L a)
    (i j : TruncatedBasisIndex L (n - 1)) :
    (terminalCollectedExpression R hn w).u i j = -terminalPP hn w j i := rfl

private example
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 1 ≤ n)
    (w : GoverningWitness n L a)
    (i : TruncatedBasisIndex L (n - 1))
    (k : FreeLieExactBasisIndex L n) :
    (terminalCollectedExpression R hn w).v i k = terminalPQ hn w i k ∧
      (terminalCollectedExpression R hn w).v' i k = terminalQP hn w k i :=
  ⟨rfl, rfl⟩

/-! ### The hierarchical aggregate component account

There is exactly one distinguished homogeneous factor.  Its ordinary neighbours remain in
the two lists.  A basis split points back to the complete parent, and an oriented bracket
correction points back to the precise partial parent that created it.  Thus no basis summand is
ever promoted to a full relation, while late factor drops retain the original square-edge
provenance.
-/

private inductive AggregateComponentAccount
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) : ℕ → Type u where
  | edge
      (root : CanonicalLieRelationsIdeal X)
      (context : RelationContext X (2 * n))
      (mark : Fin (2 * n + 1))
      (path : List ℕ)
      {pieceWeight : ℕ}
      (positive : 1 ≤ pieceWeight)
      (cutoff : pieceWeight ≤ 2 * n)
      (piece : freeLieExact X pieceWeight)
      (left right : List (TruncatedBasisIndex X (2 * n))) :
      AggregateComponentAccount X n pieceWeight
  | basis {pieceWeight : ℕ}
      (parent : AggregateComponentAccount X n pieceWeight)
      (index : FreeLieExactBasisIndex X pieceWeight) :
      AggregateComponentAccount X n pieceWeight
  | placed {pieceWeight : ℕ}
      (parent : AggregateComponentAccount X n pieceWeight)
      (left right : List (TruncatedBasisIndex X (2 * n))) :
      AggregateComponentAccount X n pieceWeight
  | bracketLeft {pieceWeight : ℕ}
      (parent : AggregateComponentAccount X n pieceWeight)
      (factor : TruncatedBasisIndex X (2 * n))
      (cutoff : truncatedBasisWeight X factor + pieceWeight ≤ 2 * n)
      (left right : List (TruncatedBasisIndex X (2 * n))) :
      AggregateComponentAccount X n
        (truncatedBasisWeight X factor + pieceWeight)
  | bracketRight {pieceWeight : ℕ}
      (parent : AggregateComponentAccount X n pieceWeight)
      (factor : TruncatedBasisIndex X (2 * n))
      (cutoff : pieceWeight + truncatedBasisWeight X factor ≤ 2 * n)
      (left right : List (TruncatedBasisIndex X (2 * n))) :
      AggregateComponentAccount X n
        (pieceWeight + truncatedBasisWeight X factor)

private abbrev AggregateComponentState
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :=
  Σ pieceWeight, AggregateComponentAccount X n pieceWeight

private def AggregateComponentAccount.root
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight →
      CanonicalLieRelationsIdeal X
  | .edge root _ _ _ _ _ _ _ _ => root
  | .basis parent _ => parent.root X
  | .placed parent _ _ => parent.root X
  | .bracketLeft parent _ _ _ _ => parent.root X
  | .bracketRight parent _ _ _ _ => parent.root X

private def AggregateComponentAccount.context
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight → RelationContext X (2 * n)
  | .edge _ context _ _ _ _ _ _ _ => context
  | .basis parent _ => parent.context X
  | .placed parent _ _ => parent.context X
  | .bracketLeft parent _ _ _ _ => parent.context X
  | .bracketRight parent _ _ _ _ => parent.context X

private def AggregateComponentAccount.mark
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight → Fin (2 * n + 1)
  | .edge _ _ mark _ _ _ _ _ _ => mark
  | .basis parent _ => parent.mark X
  | .placed parent _ _ => parent.mark X
  | .bracketLeft parent _ _ _ _ => parent.mark X
  | .bracketRight parent _ _ _ _ => parent.mark X

private def AggregateComponentAccount.path
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight → List ℕ
  | .edge _ _ _ path _ _ _ _ _ => path
  | .basis parent _ => parent.path X
  | .placed parent _ _ => parent.path X
  | .bracketLeft parent _ _ _ _ => parent.path X
  | .bracketRight parent _ _ _ _ => parent.path X

private def AggregateComponentAccount.left
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight →
      List (TruncatedBasisIndex X (2 * n))
  | .edge _ _ _ _ _ _ _ left _ => left
  | .basis parent _ => parent.left X
  | .placed _ left _ => left
  | .bracketLeft _ _ _ left _ => left
  | .bracketRight _ _ _ left _ => left

private def AggregateComponentAccount.right
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight →
      List (TruncatedBasisIndex X (2 * n))
  | .edge _ _ _ _ _ _ _ _ right => right
  | .basis parent _ => parent.right X
  | .placed _ _ right => right
  | .bracketLeft _ _ _ _ right => right
  | .bracketRight _ _ _ _ right => right

private def AggregateComponentAccount.positive
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ}
    (p : AggregateComponentAccount X n pieceWeight) : 1 ≤ pieceWeight := by
  induction p with
  | edge _ _ _ _ positive => exact positive
  | basis _ _ ih | placed _ _ _ ih => exact ih
  | bracketLeft parent factor cutoff left right ih =>
      have hfactor := truncatedBasisWeight_pos X factor
      omega
  | bracketRight parent factor cutoff left right ih =>
      have hfactor := truncatedBasisWeight_pos X factor
      omega

private def AggregateComponentAccount.cutoff
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ}
    (p : AggregateComponentAccount X n pieceWeight) : pieceWeight ≤ 2 * n := by
  induction p with
  | edge _ _ _ _ _ cutoff _ _ _ => exact cutoff
  | basis _ _ ih | placed _ _ _ ih => exact ih
  | bracketLeft _ _ cutoff _ _ _ | bracketRight _ _ cutoff _ _ _ => exact cutoff

private def AggregateComponentAccount.exact
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight → freeLieExact X pieceWeight
  | .edge _ _ _ _ _ _ piece _ _ => piece
  | .basis _ index => freeLieExactBasis X pieceWeight index
  | .placed parent _ _ => parent.exact X
  | .bracketLeft parent factor _ _ _ =>
      ⟨⁅homogeneousBasisLift X factor,
          (parent.exact X : CanonicalFreeLie X)⁆,
        freeLieExact_bracket_mem X
          (freeLieExactBasis X (truncatedBasisWeight X factor) factor.2)
          (parent.exact X)⟩
  | .bracketRight parent factor _ _ _ =>
      ⟨⁅(parent.exact X : CanonicalFreeLie X),
          homogeneousBasisLift X factor⁆,
        freeLieExact_bracket_mem X (parent.exact X)
          (freeLieExactBasis X (truncatedBasisWeight X factor) factor.2)⟩

private def AggregateComponentAccount.basisIndex?
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight →
      Option (TruncatedBasisIndex X (2 * n))
  | .edge _ _ _ _ _ _ _ _ _ => none
  | .basis parent index =>
      some (contextBasisIndexOf X (parent.positive X) (parent.cutoff X) index)
  | .placed parent _ _ => parent.basisIndex? X
  | .bracketLeft _ _ _ _ _ => none
  | .bracketRight _ _ _ _ _ => none

private def AggregateComponentAccount.twoDerived
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight → Prop
  | .edge _ _ _ _ _ _ _ _ _ => False
  | .basis parent _ => parent.twoDerived X
  | .placed parent _ _ => parent.twoDerived X
  | .bracketLeft parent factor _ _ _ =>
      parent.twoDerived X ∨
        (2 ≤ truncatedBasisWeight X factor ∧ 2 ≤ pieceWeight)
  | .bracketRight parent factor _ _ _ =>
      parent.twoDerived X ∨
        (2 ≤ pieceWeight ∧ 2 ≤ truncatedBasisWeight X factor)

private def AggregateComponentAccount.teeth
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight →
      List (TruncatedBasisIndex X (2 * n))
  | .edge _ _ _ _ _ _ _ _ _ => []
  | .basis parent _ => parent.teeth X
  | .placed parent _ _ => parent.teeth X
  | .bracketLeft parent factor _ _ _ =>
      (if truncatedBasisWeight X factor = 1 then [factor] else []) ++
        parent.teeth X
  | .bracketRight parent factor _ _ _ =>
      parent.teeth X ++
        if truncatedBasisWeight X factor = 1 then [factor] else []

/-- The sign with which the account's eventual comb is oriented.  Moving the distinguished
factor across an entry on its left creates `[x,a] = -[a,x]`; a right correction creates
`[a,x]` and does not change the sign. -/
private def AggregateComponentAccount.combSign
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ} :
    AggregateComponentAccount X n pieceWeight → ℤ
  | .edge _ _ _ _ _ _ _ _ _ => 1
  | .basis parent _ => parent.combSign X
  | .placed parent _ _ => parent.combSign X
  | .bracketLeft parent _ _ _ _ => -parent.combSign X
  | .bracketRight parent _ _ _ _ => parent.combSign X

private def AggregateComponentAccount.value
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {pieceWeight : ℕ} (p : AggregateComponentAccount X n pieceWeight) :
    UEA ℤ (TruncatedFreeLie X (2 * n)) :=
  basisWord ℤ (TruncatedFreeLie X (2 * n))
      (TruncatedBasisIndex X (2 * n))
      (truncatedHomogeneousBasis X (2 * n)) (p.left X) *
    UniversalEnvelopingAlgebra.ι ℤ
      (truncatedFreeLieMk X (2 * n)
        (p.exact X : CanonicalFreeLie X)) *
    basisWord ℤ (TruncatedFreeLie X (2 * n))
      (TruncatedBasisIndex X (2 * n))
      (truncatedHomogeneousBasis X (2 * n)) (p.right X)

private def AggregateComponentAccount.factorNumber
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ}
    (p : AggregateComponentAccount X n pieceWeight) : ℕ :=
  (p.left X).length + 1 + (p.right X).length

private def AggregateComponentAccount.totalWeight
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ}
    (p : AggregateComponentAccount X n pieceWeight) : ℕ :=
  ((p.left X).map (truncatedBasisWeight X)).sum + pieceWeight +
    ((p.right X).map (truncatedBasisWeight X)).sum

private def aggregateComponentBasisChildren
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {pieceWeight : ℕ} (p : AggregateComponentAccount X n pieceWeight) :
    List (ℤ × AggregateComponentState X n) :=
  markedSupportPackets
    ((freeLieExactBasis X pieceWeight).repr (p.exact X)) fun i ↦
      ⟨pieceWeight, .basis p i⟩

private def aggregateComponentMoveRight
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {pieceWeight : ℕ} (p : AggregateComponentAccount X n pieceWeight)
    (i : TruncatedBasisIndex X (2 * n)) :
    Option (List (ℤ × AggregateComponentState X n)) :=
  match p.right X with
  | [] => none
  | x :: right =>
      if hxi : x < i then
        let main : AggregateComponentState X n :=
          ⟨pieceWeight, .placed p (p.left X ++ [x]) right⟩
        if hcut : pieceWeight + truncatedBasisWeight X x ≤ 2 * n then
          some
            [(1, main),
             (1, ⟨pieceWeight + truncatedBasisWeight X x,
               .bracketRight p x hcut (p.left X) right⟩)]
        else some [(1, main)]
      else none

private def aggregateComponentExpansion
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    AggregateComponentState X n →
      Option (List (ℤ × AggregateComponentState X n))
  | ⟨pieceWeight, p⟩ =>
      match p.basisIndex? X with
      | none => some (aggregateComponentBasisChildren X n p)
      | some i =>
          match hleft : (p.left X).reverse with
          | x :: leftRev =>
              if hix : i < x then
                let left := leftRev.reverse
                let main : AggregateComponentState X n :=
                  ⟨pieceWeight, .placed p left (x :: p.right X)⟩
                if hcut : truncatedBasisWeight X x + pieceWeight ≤ 2 * n then
                  some
                    [(1, main),
                     (1, ⟨truncatedBasisWeight X x + pieceWeight,
                       .bracketLeft p x hcut left (p.right X)⟩)]
                else some [(1, main)]
              else aggregateComponentMoveRight X n p i
          | [] => aggregateComponentMoveRight X n p i

private theorem AggregateComponentAccount.exact_eq_basis_of_basisIndex
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ}
    (p : AggregateComponentAccount X n pieceWeight)
    (i : TruncatedBasisIndex X (2 * n))
    (hi : p.basisIndex? X = some i) :
    truncatedFreeLieMk X (2 * n)
        (p.exact X : CanonicalFreeLie X) =
      truncatedHomogeneousBasis X (2 * n) i := by
  induction p with
  | edge => simp [AggregateComponentAccount.basisIndex?] at hi
  | basis parent j ih =>
      simp only [AggregateComponentAccount.basisIndex?, Option.some.injEq] at hi
      subst i
      exact (contextBasisIndexOf_value X
        (parent.positive X) (parent.cutoff X) j).symm
  | placed parent left right ih =>
      exact ih hi
  | bracketLeft => simp [AggregateComponentAccount.basisIndex?] at hi
  | bracketRight => simp [AggregateComponentAccount.basisIndex?] at hi

private def aggregateComponentValue
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (s : AggregateComponentState X n) :
    UEA ℤ (TruncatedFreeLie X (2 * n)) :=
  s.2.value X n

private def aggregateComponentFactorNumber
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    : AggregateComponentState X n → ℕ
  | ⟨_, p⟩ => p.factorNumber X

private def aggregateComponentTotalWeight
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    : AggregateComponentState X n → ℕ
  | ⟨_, p⟩ => p.totalWeight X

private def AggregateComponentAccount.unbasedRank
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ}
    (p : AggregateComponentAccount X n pieceWeight) : ℕ :=
  if (p.basisIndex? X).isNone then 1 else 0

private def AggregateComponentAccount.disorder
    (X : Type u) [LieRing X] [Finite X] {n pieceWeight : ℕ}
    (p : AggregateComponentAccount X n pieceWeight) : ℕ :=
  match p.basisIndex? X with
  | none => 0
  | some i =>
      ((p.left X).filter (i < ·)).length +
        ((p.right X).filter (· < i)).length

private def aggregateComponentComplexity
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    : AggregateComponentState X n → ℕ × (ℕ × ℕ)
  | ⟨_, p⟩ => (p.factorNumber X, p.unbasedRank X, p.disorder X)

private def AggregateComponentDescent
    (X : Type u) [LieRing X] [Finite X] {n : ℕ}
    (new old : AggregateComponentState X n) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
    (aggregateComponentComplexity X new)
    (aggregateComponentComplexity X old)

private theorem aggregateComponentDescent_wellFounded
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    WellFounded (AggregateComponentDescent X (n := n)) :=
  InvImage.wf (aggregateComponentComplexity X)
    (Nat.lt_wfRel.wf.prod_lex
      (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))

private theorem aggregateComponentMoveRight_decreases
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {pieceWeight : ℕ} (p : AggregateComponentAccount X n pieceWeight)
    (i : TruncatedBasisIndex X (2 * n))
    (hindex : p.basisIndex? X = some i)
    {qs : List (ℤ × AggregateComponentState X n)}
    (hp : aggregateComponentMoveRight X n p i = some qs) :
    ∀ q ∈ qs, AggregateComponentDescent X q.2 ⟨pieceWeight, p⟩ := by
  classical
  intro q hq
  unfold aggregateComponentMoveRight at hp
  split at hp
  · contradiction
  · rename_i x right hright
    split at hp
    · rename_i hxi
      split at hp
      · rename_i hcut
        rcases Option.some.inj hp with rfl
        rcases List.mem_pair.mp hq with rfl | rfl
        · dsimp only [Prod.snd, Sigma.snd]
          unfold AggregateComponentDescent
          simp only [aggregateComponentComplexity]
          have hfactor :
              (AggregateComponentAccount.placed p
                (p.left X ++ [x]) right).factorNumber X =
                p.factorNumber X := by
            unfold AggregateComponentAccount.factorNumber
            rw [hright]
            simp [AggregateComponentAccount.left,
              AggregateComponentAccount.right]
            omega
          rw [hfactor]
          apply Prod.Lex.right (p.factorNumber X)
          apply Prod.Lex.right (p.unbasedRank X)
          unfold AggregateComponentAccount.disorder
          rw [hright]
          simp only [AggregateComponentAccount.left,
            AggregateComponentAccount.right,
            AggregateComponentAccount.basisIndex?, hindex,
            Option.isNone_some, if_false, List.filter_append,
            List.filter_singleton, hxi, if_true, List.length_append,
            List.length_singleton, List.length_cons]
          have hnix : ¬i < x := not_lt_of_ge (le_of_lt hxi)
          simp [hright, hxi, hnix]
        · dsimp only [Prod.snd, Sigma.snd]
          unfold AggregateComponentDescent
          simp only [aggregateComponentComplexity]
          apply Prod.Lex.left
          unfold AggregateComponentAccount.factorNumber
          rw [hright]
          simp [AggregateComponentAccount.left,
            AggregateComponentAccount.right]
      · rcases Option.some.inj hp with rfl
        simp only [List.mem_singleton] at hq
        rcases hq with rfl
        dsimp only [Prod.snd, Sigma.snd]
        unfold AggregateComponentDescent
        simp only [aggregateComponentComplexity]
        have hfactor :
            (AggregateComponentAccount.placed p
              (p.left X ++ [x]) right).factorNumber X =
              p.factorNumber X := by
          unfold AggregateComponentAccount.factorNumber
          rw [hright]
          simp [AggregateComponentAccount.left,
            AggregateComponentAccount.right]
          omega
        rw [hfactor]
        apply Prod.Lex.right (p.factorNumber X)
        apply Prod.Lex.right (p.unbasedRank X)
        unfold AggregateComponentAccount.disorder
        rw [hright]
        simp only [AggregateComponentAccount.left,
          AggregateComponentAccount.right,
          AggregateComponentAccount.basisIndex?, hindex,
          Option.isNone_some, if_false, List.filter_append,
          List.filter_singleton, hxi, if_true, List.length_append,
          List.length_singleton, List.length_cons]
        have hnix : ¬i < x := not_lt_of_ge (le_of_lt hxi)
        simp [hright, hxi, hnix]
    · contradiction

private theorem aggregateComponentExpansion_decreases
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {p : AggregateComponentState X n}
    {qs : List (ℤ × AggregateComponentState X n)}
    (hp : aggregateComponentExpansion X n p = some qs) :
    ∀ q ∈ qs, AggregateComponentDescent X q.2 p := by
  classical
  rcases p with ⟨pieceWeight, p⟩
  intro q hq
  simp only [aggregateComponentExpansion] at hp
  split at hp
  · rename_i hindex
    rcases Option.some.inj hp with rfl
    simp only [aggregateComponentBasisChildren, markedSupportPackets,
      List.mem_map] at hq
    obtain ⟨i, hi, hci, rfl⟩ := hq
    dsimp only [Prod.snd, Sigma.snd]
    unfold AggregateComponentDescent
    simp only [aggregateComponentComplexity]
    apply Prod.Lex.right (p.factorNumber X)
    apply Prod.Lex.left (AggregateComponentAccount.disorder X
      (AggregateComponentAccount.basis p i))
      (p.disorder X)
    unfold AggregateComponentAccount.unbasedRank
    simp [AggregateComponentAccount.left,
      AggregateComponentAccount.right,
      AggregateComponentAccount.basisIndex?, hindex]
  · rename_i i hindex
    split at hp
    · rename_i x leftRev hleft
      split at hp
      · rename_i hix
        split at hp
        · rename_i hcut
          rcases Option.some.inj hp with rfl
          rcases List.mem_pair.mp hq with rfl | rfl
          · dsimp only [Prod.snd, Sigma.snd]
            have hleftEq : p.left X = leftRev.reverse ++ [x] := by
              have h := congrArg List.reverse hleft
              simpa using h
            unfold AggregateComponentDescent
            simp only [aggregateComponentComplexity]
            have hfactor :
                (AggregateComponentAccount.placed p leftRev.reverse
                  (x :: p.right X)).factorNumber X =
                  p.factorNumber X := by
              unfold AggregateComponentAccount.factorNumber
              rw [hleftEq]
              simp [AggregateComponentAccount.left,
                AggregateComponentAccount.right]
              omega
            rw [hfactor]
            apply Prod.Lex.right (p.factorNumber X)
            apply Prod.Lex.right (p.unbasedRank X)
            unfold AggregateComponentAccount.disorder
            simp only [AggregateComponentAccount.left,
              AggregateComponentAccount.right,
              AggregateComponentAccount.basisIndex?, hindex,
              Option.isNone_some, if_false, List.filter_cons,
              List.length_cons]
            rw [hleftEq, List.filter_append]
            have hnxi : ¬x < i := not_lt_of_ge (le_of_lt hix)
            simp [hix, hnxi]
          · dsimp only [Prod.snd, Sigma.snd]
            unfold AggregateComponentDescent
            simp only [aggregateComponentComplexity]
            apply Prod.Lex.left
            unfold AggregateComponentAccount.factorNumber
            have hleftEq : p.left X = leftRev.reverse ++ [x] := by
              have h := congrArg List.reverse hleft
              simpa using h
            rw [hleftEq]
            simp [AggregateComponentAccount.left,
              AggregateComponentAccount.right]
        · rcases Option.some.inj hp with rfl
          simp only [List.mem_singleton] at hq
          rcases hq with rfl
          dsimp only [Prod.snd, Sigma.snd]
          have hleftEq : p.left X = leftRev.reverse ++ [x] := by
            have h := congrArg List.reverse hleft
            simpa using h
          unfold AggregateComponentDescent
          simp only [aggregateComponentComplexity]
          have hfactor :
              (AggregateComponentAccount.placed p leftRev.reverse
                (x :: p.right X)).factorNumber X =
                p.factorNumber X := by
            unfold AggregateComponentAccount.factorNumber
            rw [hleftEq]
            simp [AggregateComponentAccount.left,
              AggregateComponentAccount.right]
            omega
          rw [hfactor]
          apply Prod.Lex.right (p.factorNumber X)
          apply Prod.Lex.right (p.unbasedRank X)
          unfold AggregateComponentAccount.disorder
          simp only [AggregateComponentAccount.left,
            AggregateComponentAccount.right,
            AggregateComponentAccount.basisIndex?, hindex,
            Option.isNone_some, if_false, List.filter_cons,
            List.length_cons]
          rw [hleftEq, List.filter_append]
          have hnxi : ¬x < i := not_lt_of_ge (le_of_lt hix)
          simp [hix, hnxi]
      · exact aggregateComponentMoveRight_decreases X n p i hindex hp q hq
    · exact aggregateComponentMoveRight_decreases X n p i hindex hp q hq

private theorem truncatedFreeLieMk_exact_eq_zero_of_above_cutoff
    (X : Type u) [LieRing X] [Finite X] (N weight : ℕ)
    (z : freeLieExact X weight) (hweight : N < weight) :
    truncatedFreeLieMk X N (z : CanonicalFreeLie X) = 0 := by
  apply (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ (CanonicalFreeLie X) N)).mpr
  have hz := freeLieExact_mem_lieHigh X z
  have hweightPos : 1 ≤ weight := by omega
  have hz' : (z : CanonicalFreeLie X) ∈
      lowerCentralSeries ℤ (CanonicalFreeLie X) (weight - 1) := by
    change (z : CanonicalFreeLie X) ∈
      (lowerCentralSeries ℤ (CanonicalFreeLie X)
        (weight - 1)).toLieSubalgebra.toSubmodule
    rw [← FreeLieDimension.lieHigh_eq_lowerCentralSeries]
    simpa [Nat.sub_add_cancel hweightPos] using hz
  exact LieModule.antitone_lowerCentralSeries ℤ
    (CanonicalFreeLie X) (CanonicalFreeLie X) (by omega) hz'

private theorem aggregateComponentMoveRight_preserves
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {pieceWeight : ℕ} (p : AggregateComponentAccount X n pieceWeight)
    (i : TruncatedBasisIndex X (2 * n))
    {qs : List (ℤ × AggregateComponentState X n)}
    (hp : aggregateComponentMoveRight X n p i = some qs) :
    (qs.map fun q ↦ q.1 • aggregateComponentValue X n q.2).sum =
      p.value X n := by
  classical
  unfold aggregateComponentMoveRight at hp
  split at hp
  · contradiction
  · rename_i x right hright
    split at hp
    · rename_i hxi
      let b := truncatedHomogeneousBasis X (2 * n)
      let a := truncatedFreeLieMk X (2 * n)
        (p.exact X : CanonicalFreeLie X)
      let xv := b x
      let lw := basisWord ℤ (TruncatedFreeLie X (2 * n))
        (TruncatedBasisIndex X (2 * n)) b (p.left X)
      let rw' := basisWord ℤ (TruncatedFreeLie X (2 * n))
        (TruncatedBasisIndex X (2 * n)) b right
      have hxv : xv = truncatedFreeLieMk X (2 * n)
          (homogeneousBasisLift X x) := by
        simpa only [xv, b, homogeneousBasisLift,
          truncatedBasisWeight] using
            (truncatedHomogeneousBasis_apply X (2 * n) x)
      have hswap := iota_mul_iota_swap ℤ
        (TruncatedFreeLie X (2 * n)) a xv
      split at hp
      · rename_i hcut
        rcases Option.some.inj hp with rfl
        have hcorr : truncatedFreeLieMk X (2 * n)
            ⁅(p.exact X : CanonicalFreeLie X),
              homogeneousBasisLift X x⁆ = ⁅a, xv⁆ := by
          rw [LieHom.map_lie, hxv]
        simp only [List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, one_smul, add_zero]
        unfold aggregateComponentValue AggregateComponentAccount.value
        rw [hright]
        simp only [AggregateComponentAccount.left,
          AggregateComponentAccount.right, AggregateComponentAccount.exact,
          basisWord, List.map_append, List.map_singleton, List.map_cons,
          List.map_nil, word_append, word_cons, word_nil, mul_one]
        rw [hcorr]
        change lw * UniversalEnvelopingAlgebra.ι ℤ xv *
              UniversalEnvelopingAlgebra.ι ℤ a * rw' +
            lw * UniversalEnvelopingAlgebra.ι ℤ ⁅a, xv⁆ * rw' =
          lw * UniversalEnvelopingAlgebra.ι ℤ a *
            (UniversalEnvelopingAlgebra.ι ℤ xv * rw')
        calc
          _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
                  UniversalEnvelopingAlgebra.ι ℤ a +
                UniversalEnvelopingAlgebra.ι ℤ ⁅a, xv⁆) * rw' := by
                  noncomm_ring
          _ = lw * (UniversalEnvelopingAlgebra.ι ℤ a *
                  UniversalEnvelopingAlgebra.ι ℤ xv) * rw' := by
                  rw [← hswap]
          _ = _ := by noncomm_ring
      · rename_i hcut
        rcases Option.some.inj hp with rfl
        let bracketExact : freeLieExact X
            (pieceWeight + truncatedBasisWeight X x) :=
          ⟨⁅(p.exact X : CanonicalFreeLie X), homogeneousBasisLift X x⁆,
            freeLieExact_bracket_mem X (p.exact X)
              (freeLieExactBasis X (truncatedBasisWeight X x) x.2)⟩
        have hbracket : ⁅a, xv⁆ = 0 := by
          rw [hxv]
          change truncatedFreeLieMk X (2 * n)
              (bracketExact : CanonicalFreeLie X) = 0
          exact truncatedFreeLieMk_exact_eq_zero_of_above_cutoff X
            (2 * n) (pieceWeight + truncatedBasisWeight X x)
              bracketExact (by omega)
        rw [hbracket, map_zero, add_zero] at hswap
        simp only [List.map_singleton, List.sum_singleton, one_smul]
        unfold aggregateComponentValue AggregateComponentAccount.value
        rw [hright]
        simp only [AggregateComponentAccount.left,
          AggregateComponentAccount.right, AggregateComponentAccount.exact,
          basisWord, List.map_append, List.map_singleton, List.map_cons,
          List.map_nil, word_append, word_cons, word_nil, mul_one]
        change lw * UniversalEnvelopingAlgebra.ι ℤ xv *
              UniversalEnvelopingAlgebra.ι ℤ a * rw' =
          lw * UniversalEnvelopingAlgebra.ι ℤ a *
            (UniversalEnvelopingAlgebra.ι ℤ xv * rw')
        calc
          _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
                UniversalEnvelopingAlgebra.ι ℤ a) * rw' := by
                  noncomm_ring
          _ = lw * (UniversalEnvelopingAlgebra.ι ℤ a *
                UniversalEnvelopingAlgebra.ι ℤ xv) * rw' := by
                  rw [← hswap]
          _ = _ := by noncomm_ring
    · contradiction

private theorem aggregateComponentExpansion_preserves
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    {p : AggregateComponentState X n}
    {qs : List (ℤ × AggregateComponentState X n)}
    (hp : aggregateComponentExpansion X n p = some qs) :
    (qs.map fun q ↦ q.1 • aggregateComponentValue X n q.2).sum =
      aggregateComponentValue X n p := by
  classical
  rcases p with ⟨pieceWeight, p⟩
  simp only [aggregateComponentExpansion] at hp
  split at hp
  · rename_i hindex
    rcases Option.some.inj hp with rfl
    let c := (freeLieExactBasis X pieceWeight).repr (p.exact X)
    let b := truncatedHomogeneousBasis X (2 * n)
    let lw := basisWord ℤ (TruncatedFreeLie X (2 * n))
      (TruncatedBasisIndex X (2 * n)) b (p.left X)
    let rw' := basisWord ℤ (TruncatedFreeLie X (2 * n))
      (TruncatedBasisIndex X (2 * n)) b (p.right X)
    have hexact : c.sum (fun i z ↦ z •
          (freeLieExactBasis X pieceWeight i)) = p.exact X := by
      simpa only [c, Finsupp.linearCombination_apply] using
        ((freeLieExactBasis X pieceWeight).linearCombination_repr
          (p.exact X))
    have hcomponent : c.sum (fun i z ↦ z •
          truncatedFreeLieMk X (2 * n)
            (((freeLieExactBasis X pieceWeight i :
              freeLieExact X pieceWeight)) : CanonicalFreeLie X)) =
        truncatedFreeLieMk X (2 * n)
          (p.exact X : CanonicalFreeLie X) := by
      let exactToTruncated : freeLieExact X pieceWeight →ₗ[ℤ]
          TruncatedFreeLie X (2 * n) :=
        (truncatedFreeLieMk X (2 * n)).toLinearMap.comp
          (freeLieExact X pieceWeight).subtype
      have h := congrArg exactToTruncated hexact
      rw [map_finsuppSum] at h
      simpa [exactToTruncated, map_zsmul] using h
    let context : TruncatedFreeLie X (2 * n) →+
        UEA ℤ (TruncatedFreeLie X (2 * n)) :=
      { toFun := fun z ↦ lw * UniversalEnvelopingAlgebra.ι ℤ z * rw'
        map_zero' := by simp
        map_add' := by intro a b; simp [map_add, mul_add, add_mul] }
    have hcontext := congrArg context hcomponent
    rw [map_finsuppSum] at hcontext
    rw [aggregateComponentBasisChildren, markedSupportPackets_value]
    simpa [aggregateComponentValue, AggregateComponentAccount.value,
      AggregateComponentAccount.left, AggregateComponentAccount.right,
      AggregateComponentAccount.exact, context, lw, rw', b, map_zsmul]
      using hcontext
  · rename_i i hindex
    split at hp
    · rename_i x leftRev hleft
      split at hp
      · rename_i hix
        have hleftEq : p.left X = leftRev.reverse ++ [x] := by
          have h := congrArg List.reverse hleft
          simpa using h
        let b := truncatedHomogeneousBasis X (2 * n)
        let a := truncatedFreeLieMk X (2 * n)
          (p.exact X : CanonicalFreeLie X)
        let xv := b x
        let lw := basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n)) b leftRev.reverse
        let rw' := basisWord ℤ (TruncatedFreeLie X (2 * n))
          (TruncatedBasisIndex X (2 * n)) b (p.right X)
        have hxv : xv = truncatedFreeLieMk X (2 * n)
            (homogeneousBasisLift X x) := by
          simpa only [xv, b, homogeneousBasisLift,
            truncatedBasisWeight] using
              (truncatedHomogeneousBasis_apply X (2 * n) x)
        have hswap := iota_mul_iota_swap ℤ
          (TruncatedFreeLie X (2 * n)) xv a
        split at hp
        · rename_i hcut
          rcases Option.some.inj hp with rfl
          have hcorr : truncatedFreeLieMk X (2 * n)
              ⁅homogeneousBasisLift X x,
                (p.exact X : CanonicalFreeLie X)⁆ = ⁅xv, a⁆ := by
            rw [LieHom.map_lie, hxv]
          simp only [List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, one_smul, add_zero]
          unfold aggregateComponentValue AggregateComponentAccount.value
          rw [hleftEq]
          simp only [AggregateComponentAccount.left,
            AggregateComponentAccount.right, AggregateComponentAccount.exact,
            basisWord, List.map_append, List.map_singleton, List.map_cons,
            List.map_nil, word_append, word_cons, word_nil, mul_one]
          rw [hcorr]
          change lw * UniversalEnvelopingAlgebra.ι ℤ a *
                (UniversalEnvelopingAlgebra.ι ℤ xv * rw') +
              lw * UniversalEnvelopingAlgebra.ι ℤ ⁅xv, a⁆ * rw' =
            (lw * UniversalEnvelopingAlgebra.ι ℤ xv) *
              UniversalEnvelopingAlgebra.ι ℤ a * rw'
          calc
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ a *
                    UniversalEnvelopingAlgebra.ι ℤ xv +
                  UniversalEnvelopingAlgebra.ι ℤ ⁅xv, a⁆) * rw' := by
                    noncomm_ring
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
                    UniversalEnvelopingAlgebra.ι ℤ a) * rw' := by
                    rw [← hswap]
            _ = _ := by noncomm_ring
        · rename_i hcut
          rcases Option.some.inj hp with rfl
          let bracketExact : freeLieExact X
              (truncatedBasisWeight X x + pieceWeight) :=
            ⟨⁅homogeneousBasisLift X x,
                (p.exact X : CanonicalFreeLie X)⁆,
              freeLieExact_bracket_mem X
                (freeLieExactBasis X (truncatedBasisWeight X x) x.2)
                (p.exact X)⟩
          have hbracket : ⁅xv, a⁆ = 0 := by
            rw [hxv]
            change truncatedFreeLieMk X (2 * n)
                (bracketExact : CanonicalFreeLie X) = 0
            exact truncatedFreeLieMk_exact_eq_zero_of_above_cutoff X
              (2 * n) (truncatedBasisWeight X x + pieceWeight)
                bracketExact (by omega)
          rw [hbracket, map_zero, add_zero] at hswap
          simp only [List.map_singleton, List.sum_singleton, one_smul]
          unfold aggregateComponentValue AggregateComponentAccount.value
          rw [hleftEq]
          simp only [AggregateComponentAccount.left,
            AggregateComponentAccount.right, AggregateComponentAccount.exact,
            basisWord, List.map_append, List.map_singleton, List.map_cons,
            List.map_nil, word_append, word_cons, word_nil, mul_one]
          change lw * UniversalEnvelopingAlgebra.ι ℤ a *
                (UniversalEnvelopingAlgebra.ι ℤ xv * rw') =
            (lw * UniversalEnvelopingAlgebra.ι ℤ xv) *
              UniversalEnvelopingAlgebra.ι ℤ a * rw'
          calc
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ a *
                  UniversalEnvelopingAlgebra.ι ℤ xv) * rw' := by
                    noncomm_ring
            _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
                  UniversalEnvelopingAlgebra.ι ℤ a) * rw' := by
                    rw [← hswap]
            _ = _ := by noncomm_ring
      · exact aggregateComponentMoveRight_preserves X n p i hp
    · exact aggregateComponentMoveRight_preserves X n p i hp

private def aggregateComponentCollector
    (X : Type u) [LieRing X] [Finite X] (n : ℕ) :
    FiniteTaggedCollector (AggregateComponentState X n)
      (UEA ℤ (TruncatedFreeLie X (2 * n))) where
  relation := AggregateComponentDescent X
  wellFounded := aggregateComponentDescent_wellFounded X n
  expansion := aggregateComponentExpansion X n
  value := aggregateComponentValue X n
  decreases := aggregateComponentExpansion_decreases X n
  preserves := aggregateComponentExpansion_preserves X n

private example
    (X : Type u) [LieRing X] [Finite X] (n pieceWeight : ℕ)
    (root : CanonicalLieRelationsIdeal X)
    (context : RelationContext X (2 * n))
    (mark : Fin (2 * n + 1)) (path : List ℕ)
    (positive : 1 ≤ pieceWeight) (cutoff : pieceWeight ≤ 2 * n)
    (piece : freeLieExact X pieceWeight)
    (a x : TruncatedBasisIndex X (2 * n))
    (j : FreeLieExactBasisIndex X pieceWeight)
    (hleft : ¬contextBasisIndexOf X positive cutoff j < a)
    (hright : x < contextBasisIndexOf X positive cutoff j)
    (hbracket : pieceWeight + truncatedBasisWeight X x ≤ 2 * n) :
    let edge : AggregateComponentAccount X n pieceWeight :=
      .edge root context mark path positive cutoff piece [a] [x]
    let based := AggregateComponentAccount.basis edge j
    let correction := AggregateComponentAccount.bracketRight based x
      hbracket [a] []
    aggregateComponentExpansion X n ⟨pieceWeight, based⟩ =
        some
          [(1, ⟨pieceWeight,
            AggregateComponentAccount.placed based [a, x] []⟩),
           (1, ⟨pieceWeight + truncatedBasisWeight X x, correction⟩)] ∧
      correction.root X = root ∧ correction.context X = context ∧
      correction.mark X = mark ∧ correction.path X = path ∧
      correction.factorNumber X + 1 = based.factorNumber X := by
  dsimp only
  simp [aggregateComponentExpansion,
    AggregateComponentAccount.basisIndex?, AggregateComponentAccount.left,
    AggregateComponentAccount.right, List.reverse, hleft,
    aggregateComponentMoveRight, hright,
    hbracket, AggregateComponentAccount.root,
    AggregateComponentAccount.context, AggregateComponentAccount.mark,
    AggregateComponentAccount.path, AggregateComponentAccount.factorNumber,
    List.length_cons, List.length_nil]

private theorem aggregateComponentAccount_specification
    (X : Type u) [LieRing X] [Finite X] (n : ℕ)
    (p : AggregateComponentState X n) :
    (aggregateComponentCollector X n).evaluate
        ((aggregateComponentCollector X n).normalForm p) =
        aggregateComponentValue X n p ∧
      ∀ q, (aggregateComponentCollector X n).normalForm p q ≠ 0 →
        aggregateComponentTotalWeight X q =
            aggregateComponentTotalWeight X p ∧
          aggregateComponentFactorNumber X q ≤
            aggregateComponentFactorNumber X p := by
  classical
  constructor
  · exact (aggregateComponentCollector X n).evaluate_normalForm p
  · have expansion_numerics :
        ∀ {p : AggregateComponentState X n}
          {qs : List (ℤ × AggregateComponentState X n)},
          aggregateComponentExpansion X n p = some qs →
          ∀ q ∈ qs,
            aggregateComponentTotalWeight X q.2 =
                aggregateComponentTotalWeight X p ∧
              aggregateComponentFactorNumber X q.2 ≤
                aggregateComponentFactorNumber X p := by
      intro p qs hp q hq
      have hfactor := aggregateComponentExpansion_decreases X n hp q hq
      have hfactorLe : aggregateComponentFactorNumber X q.2 ≤
          aggregateComponentFactorNumber X p := by
        have lex_fst_le : ∀ {a b : ℕ × (ℕ × ℕ)},
            Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) a b →
              a.1 ≤ b.1 := by
          intro a b hab
          cases hab with
          | left _ _ hlt => exact hlt.le
          | right _ _ => exact le_rfl
        unfold AggregateComponentDescent at hfactor
        have hle := lex_fst_le hfactor
        simpa [aggregateComponentComplexity,
          aggregateComponentFactorNumber] using hle
      refine ⟨?_, hfactorLe⟩
      have moveRight_weight :
          ∀ {pieceWeight : ℕ}
            (p : AggregateComponentAccount X n pieceWeight)
            (i : TruncatedBasisIndex X (2 * n))
            {qs : List (ℤ × AggregateComponentState X n)},
            aggregateComponentMoveRight X n p i = some qs →
            ∀ q ∈ qs,
              aggregateComponentTotalWeight X q.2 = p.totalWeight X := by
        intro pieceWeight p i qs hp q hq
        unfold aggregateComponentMoveRight at hp
        split at hp
        · contradiction
        · rename_i x right hright
          split at hp
          · split at hp
            · rcases Option.some.inj hp with rfl
              rcases List.mem_pair.mp hq with rfl | rfl <;>
                simp only [Prod.snd, aggregateComponentTotalWeight,
                  AggregateComponentAccount.totalWeight,
                  AggregateComponentAccount.left,
                  AggregateComponentAccount.right] <;>
                rw [hright] <;>
                simp [List.map_append] <;> omega
            · rcases Option.some.inj hp with rfl
              simp only [List.mem_singleton] at hq
              rcases hq with rfl
              simp only [Prod.snd, aggregateComponentTotalWeight,
                AggregateComponentAccount.totalWeight,
                AggregateComponentAccount.left,
                AggregateComponentAccount.right]
              rw [hright]
              simp [List.map_append]
              omega
          · contradiction
      rcases p with ⟨pieceWeight, p⟩
      simp only [aggregateComponentExpansion] at hp
      split at hp
      · rcases Option.some.inj hp with rfl
        simp only [aggregateComponentBasisChildren, markedSupportPackets,
          List.mem_map] at hq
        obtain ⟨i, hi, hci, rfl⟩ := hq
        simp [aggregateComponentTotalWeight,
          AggregateComponentAccount.totalWeight,
          AggregateComponentAccount.left,
          AggregateComponentAccount.right]
      · rename_i i hindex
        split at hp
        · rename_i x leftRev hleft
          split at hp
          · split at hp
            · rcases Option.some.inj hp with rfl
              rcases List.mem_pair.mp hq with rfl | rfl
              · simp only [Prod.snd, aggregateComponentTotalWeight,
                  AggregateComponentAccount.totalWeight,
                  AggregateComponentAccount.left,
                  AggregateComponentAccount.right]
                have hleftEq : p.left X = leftRev.reverse ++ [x] := by
                  have h := congrArg List.reverse hleft
                  simpa using h
                rw [hleftEq]
                simp [List.map_append]
                omega
              · simp only [Prod.snd, aggregateComponentTotalWeight,
                  AggregateComponentAccount.totalWeight,
                  AggregateComponentAccount.left,
                  AggregateComponentAccount.right]
                have hleftEq : p.left X = leftRev.reverse ++ [x] := by
                  have h := congrArg List.reverse hleft
                  simpa using h
                rw [hleftEq]
                simp [List.map_append]
                omega
            · rcases Option.some.inj hp with rfl
              simp only [List.mem_singleton] at hq
              rcases hq with rfl
              simp only [Prod.snd, aggregateComponentTotalWeight,
                AggregateComponentAccount.totalWeight,
                AggregateComponentAccount.left,
                AggregateComponentAccount.right]
              have hleftEq : p.left X = leftRev.reverse ++ [x] := by
                have h := congrArg List.reverse hleft
                simpa using h
              rw [hleftEq]
              simp [List.map_append]
              omega
          · exact moveRight_weight p i hp q hq
        · exact moveRight_weight p i hp q hq
    let C := aggregateComponentCollector X n
    have frontier_numerics :
        ∀ (p : AggregateComponentState X n) (path : List ℕ)
          (coefficient : ℤ)
          (occurrence : Occurrence (AggregateComponentState X n)),
          rewriteFrontier C p path coefficient occurrence ≠ 0 →
            aggregateComponentTotalWeight X occurrence.2 =
                aggregateComponentTotalWeight X p ∧
              aggregateComponentFactorNumber X occurrence.2 ≤
                aggregateComponentFactorNumber X p := by
      intro p
      induction p using C.wellFounded.induction with
      | h p ih =>
          intro path coefficient occurrence hoccurrence
          rw [rewriteFrontier, C.wellFounded.fix_eq] at hoccurrence
          unfold frontierStep at hoccurrence
          split at hoccurrence
          · by_cases hp : (path, p) = occurrence
            · subst occurrence
              exact ⟨rfl, le_rfl⟩
            · simp [hp] at hoccurrence
          · rename_i qs hexpand
            have hsum (xs : List
                (Occurrence (AggregateComponentState X n) →₀ ℤ)) :
                xs.sum occurrence =
                  (xs.map fun f ↦ f occurrence).sum := by
              induction xs with
              | nil => simp
              | cons x xs ihxs => simp [ihxs]
            rw [hsum] at hoccurrence
            have hexists : ∃ z ∈
                (List.ofFn fun i : Fin qs.length ↦
                  rewriteFrontier C (qs.get i).2 (i.1 :: path)
                    (coefficient * (qs.get i).1)),
                z occurrence ≠ 0 := by
              by_contra hall
              push Not at hall
              apply hoccurrence
              apply List.sum_eq_zero
              intro c hc
              simp only [List.mem_map] at hc
              obtain ⟨z, hz, rfl⟩ := hc
              exact hall z hz
            obtain ⟨z, hz, hzoccurrence⟩ := hexists
            rw [List.mem_ofFn'] at hz
            obtain ⟨i, rfl⟩ := hz
            have hchild := ih (qs.get i).2
              (C.decreases hexpand (qs.get i) (List.get_mem qs i))
              (i.1 :: path) (coefficient * (qs.get i).1)
              occurrence hzoccurrence
            have hstep := expansion_numerics hexpand
              (qs.get i) (List.get_mem qs i)
            exact ⟨hchild.1.trans hstep.1,
              hchild.2.trans hstep.2⟩
    intro q hq
    have hforget := forgetPaths_rewriteFrontier C p [] 1
    rw [one_smul] at hforget
    have hmapped : forgetPaths (rewriteFrontier C p [] 1) q ≠ 0 := by
      rw [hforget]
      exact hq
    have hsupport :
        q ∈ (forgetPaths (rewriteFrontier C p [] 1)).support :=
      Finsupp.mem_support_iff.mpr hmapped
    change q ∈
      (Finsupp.mapDomain Prod.snd (rewriteFrontier C p [] 1)).support at hsupport
    have himage := Finsupp.mapDomain_support hsupport
    rw [Finset.mem_image] at himage
    obtain ⟨occurrence, hoccurrence, hsnd⟩ := himage
    have hnonzero : rewriteFrontier C p [] 1 occurrence ≠ 0 :=
      Finsupp.mem_support_iff.mp hoccurrence
    have hnumerics := frontier_numerics p [] 1 occurrence hnonzero
    simpa [hsnd] using hnumerics

/-! ### The two terminal reads of an aggregate component

The distinguished exact factor is kept as the first entry of the kernel ledger even when its
ordered PBW position is second.  The polynomial is symmetric, while this convention retains
the relation provenance needed for the pointwise kernel proof. -/

private def aggregateComponentLeafQuadraticLedger
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (p : AggregateComponentState L n) :
    TerminalR0Index L n → TerminalR0 L n := by
  classical
  rcases p with ⟨pieceWeight, p⟩
  exact match p.left L ++ p.right L with
  | [x] => fun s ↦
      ((terminalR0Basis L n hn).repr
          (terminalFactorR0 L n (2 * n) x) s) •
        terminalR0Projection L n (p.exact L : CanonicalFreeLie L)
  | _ => 0

private def aggregateComponentQuadraticLedger
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (p : AggregateComponentState L n) :
    TerminalR0Index L n → TerminalR0 L n := by
  classical
  exact ((aggregateComponentCollector L n).normalForm p).sum fun q c ↦
    c • aggregateComponentLeafQuadraticLedger L n hn q

/-! The complete quadratic read used by the closed square.  A component is first restored as
one exact homogeneous element and only then normalized by the aggregate collector.  The
`Option` guards are data needed to build the dependent exact-weight account; every component
created by `provenancedSquareExpansion` satisfies them. -/

private def provenancedComponentAggregateStateAt?
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    List ℕ → ProvenancedSquarePacket L n → Option (AggregateComponentState L n)
  | _, .marked _ _ _ _ _ => none
  | path, .component r c k left right =>
      if hpos : 1 ≤ k.1 + c.weight L then
        if hcut : k.1 + c.weight L ≤ 2 * n then
          some ⟨k.1 + c.weight L,
            .edge r c k path hpos hcut
              (contextComponentExact L c r k.1) left right⟩
        else none
      else none

private def provenancedComponentAggregateState?
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    ProvenancedSquarePacket L n → Option (AggregateComponentState L n) :=
  provenancedComponentAggregateStateAt? L n []

private def provenancedOccurrenceAggregateState?
    (L : Type u) [LieRing L] [Finite L] (n : ℕ) :
    Occurrence (ProvenancedSquarePacket L n) →
      Option (AggregateComponentState L n)
  | (path, p) => provenancedComponentAggregateStateAt? L n path p

private def provenancedMarkedQuadraticLedger
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    ProvenancedSquarePacket L n →
      (TerminalR0Index L n → TerminalR0 L n)
  | .marked r c k [x] [] =>
      if k.1 + c.weight L = n then fun s ↦
        ((terminalR0Basis L n hn).repr
          (terminalFactorR0 L n (2 * n) x) s) •
            terminalR0Projection L n (c.relation L r : CanonicalFreeLie L)
      else 0
  | _ => 0

private def provenancedPacketQuadraticLedger
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (p : ProvenancedSquarePacket L n) :
    TerminalR0Index L n → TerminalR0 L n :=
  provenancedMarkedQuadraticLedger L n hn p +
    match provenancedComponentAggregateState? L n p with
    | none => 0
    | some q => aggregateComponentQuadraticLedger L n hn q

private def GoverningWitness.closedSquareKernelLedger
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    TerminalR0Index L n → TerminalR0 L n := by
  classical
  exact w.provenancedSquareFrontier.sum fun p c ↦
    c • provenancedPacketQuadraticLedger L n hn p

/-- The actual factor-two chain at the terminal wall.  Only marked singleton walls occur in
this ledger, so every first factor is a complete contextual relation.  In contrast with
`closedSquareKernelLedger`, this ledger is pointwise in `ker terminalR0ToW`. -/
private def GoverningWitness.provenancedTerminalKernelLedger
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    TerminalR0Index L n → TerminalR0 L n := by
  classical
  exact w.provenancedSquareFrontier.sum fun p c ↦
    c • provenancedMarkedQuadraticLedger L n hn p

private theorem GoverningWitness.provenancedTerminalKernelLedger_mem_ker
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (s : TerminalR0Index L n) :
    w.provenancedTerminalKernelLedger hn s ∈
      (terminalR0ToW L n).ker := by
  classical
  rw [LinearMap.mem_ker]
  unfold GoverningWitness.provenancedTerminalKernelLedger Finsupp.sum
  rw [Finset.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro p hp
  change terminalR0ToW L n
      (w.provenancedSquareFrontier p •
        provenancedMarkedQuadraticLedger L n hn p s) = 0
  rw [map_zsmul]
  cases p with
  | component => simp [provenancedMarkedQuadraticLedger]
  | marked r c k left right =>
      cases left with
      | nil => simp [provenancedMarkedQuadraticLedger]
      | cons x xs =>
          cases xs with
          | cons y ys => simp [provenancedMarkedQuadraticLedger]
          | nil =>
              cases right with
              | cons y ys => simp [provenancedMarkedQuadraticLedger]
              | nil =>
                  by_cases hactive : k.1 + c.weight L = n
                  · simp only [provenancedMarkedQuadraticLedger,
                      hactive, if_true]
                    rw [map_zsmul,
                      LinearMap.mem_ker.mp
                        (terminalRelationProjection_mem_ker L n hn
                          (c.relation L r))]
                    simp
                  · simp [provenancedMarkedQuadraticLedger, hactive]

private theorem aggregateComponentLeafQuadraticLedger_polynomial
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (pieceWeight : ℕ)
    (p : AggregateComponentAccount L n pieceWeight)
    (x : TruncatedBasisIndex L (2 * n))
    (hordinary : p.left L ++ p.right L = [x]) :
    terminalKernelLedgerPolynomial L n hn
        (aggregateComponentLeafQuadraticLedger L n hn ⟨pieceWeight, p⟩) =
      terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalR0Projection L n (p.exact L : CanonicalFreeLie L)) *
        terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalFactorR0 L n (2 * n) x) := by
  classical
  unfold aggregateComponentLeafQuadraticLedger
  simp only [hordinary]
  exact terminalKernelLedgerPolynomial_rankOne L n hn _ _

private theorem terminalBasisPolynomial_mul_coeff
    {I M : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis I ℤ M) (x y : M) (i j : I) :
    MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
        (terminalBasisPolynomial b x * terminalBasisPolynomial b y) =
      if i = j then b.repr x i * b.repr y i
      else b.repr x i * b.repr y j + b.repr x j * b.repr y i := by
  classical
  have hdiagExponent (a c i : I) :
      Finsupp.single a 1 + Finsupp.single c 1 =
          Finsupp.single i 1 + Finsupp.single i 1 ↔
        a = i ∧ c = i := by
    constructor
    · intro h
      have hm : ({a} + {c} : Multiset I) = {i} + {i} := by
        apply Multiset.toFinsupp.injective
        simpa only [Multiset.toFinsupp_add,
          Multiset.toFinsupp_singleton] using h
      have ha : a ∈ ({i} + {i} : Multiset I) := by rw [← hm]; simp
      have hc : c ∈ ({i} + {i} : Multiset I) := by rw [← hm]; simp
      simpa using And.intro ha hc
    · rintro ⟨rfl, rfl⟩
      rfl
  have hoffExponent (a c i j : I) (hij : i ≠ j) :
      Finsupp.single a 1 + Finsupp.single c 1 =
          Finsupp.single i 1 + Finsupp.single j 1 ↔
        (a = i ∧ c = j) ∨ (a = j ∧ c = i) := by
    constructor
    · intro h
      have hm : ({a} + {c} : Multiset I) = {i} + {j} := by
        apply Multiset.toFinsupp.injective
        simpa only [Multiset.toFinsupp_add,
          Multiset.toFinsupp_singleton] using h
      change a ::ₘ ({c} : Multiset I) = i ::ₘ ({j} : Multiset I) at hm
      rw [Multiset.cons_eq_cons] at hm
      rcases hm with h | h
      · exact Or.inl ⟨h.1, Multiset.singleton_inj.mp h.2⟩
      · obtain ⟨hai, cs, hc, hj⟩ := h
        have hcs : cs = 0 := by
          apply Multiset.card_eq_zero.mp
          have hcard := congrArg Multiset.card hc
          simpa using hcard
        subst cs
        simp only [Multiset.cons_zero, Multiset.singleton_inj] at hc hj
        exact Or.inr ⟨hj.symm, hc⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · exact add_comm _ _
  unfold terminalBasisPolynomial
  change MvPolynomial.coeff _
      ((b.repr x).sum (fun a z ↦ z • MvPolynomial.X a) *
        (b.repr y).sum (fun c z ↦ z • MvPolynomial.X c)) = _
  rw [Finsupp.sum_mul]
  change (MvPolynomial.coeffAddMonoidHom _)
      ((b.repr x).sum fun a z ↦ (z • MvPolynomial.X a) *
        (b.repr y).sum fun c z ↦ z • MvPolynomial.X c) = _
  rw [map_finsuppSum]
  simp_rw [Finsupp.mul_sum]
  change (b.repr x).sum (fun a za ↦
      (MvPolynomial.coeffAddMonoidHom _)
        ((b.repr y).sum fun c zc ↦
          (za • MvPolynomial.X a) * (zc • MvPolynomial.X c))) = _
  simp_rw [map_finsuppSum]
  simp only [smul_mul_smul, map_zsmul]
  have hmulSum (r : ℤ) (f : I →₀ ℤ) (k : I) :
      f.sum (fun c zc ↦ if c = k then r * zc else 0) = r * f k := by
    calc
      _ = r * f.sum (fun c zc ↦ if c = k then zc else 0) := by
        rw [Finsupp.mul_sum]
        apply Finsupp.sum_congr
        intro c hc
        by_cases hck : c = k <;> simp [hck]
      _ = _ := by rw [Finsupp.sum_ite_self_eq']
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    change (b.repr x).sum (fun a za ↦ (b.repr y).sum fun c zc ↦
      (za * zc) * MvPolynomial.coeff
        (Finsupp.single i 1 + Finsupp.single i 1)
          (MvPolynomial.X a * MvPolynomial.X c)) = _
    simp_rw [MvPolynomial.X, MvPolynomial.monomial_mul,
      MvPolynomial.coeff_monomial, hdiagExponent]
    simp only [mul_ite, mul_one, mul_zero]
    calc
      _ = (b.repr x).sum (fun a za ↦
          if a = i then za * b.repr y i else 0) := by
        apply Finsupp.sum_congr
        intro a ha
        by_cases hai : a = i
        · subst a
          simp only [true_and, if_true]
          exact hmulSum (b.repr x i) (b.repr y) i
        · simp [hai]
      _ = _ := by
        simpa [mul_comm] using hmulSum (b.repr y i) (b.repr x) i
  · simp only [if_neg hij]
    change (b.repr x).sum (fun a za ↦ (b.repr y).sum fun c zc ↦
      (za * zc) * MvPolynomial.coeff
        (Finsupp.single i 1 + Finsupp.single j 1)
          (MvPolynomial.X a * MvPolynomial.X c)) = _
    simp_rw [MvPolynomial.X, MvPolynomial.monomial_mul,
      MvPolynomial.coeff_monomial, hoffExponent _ _ _ _ hij]
    simp only [mul_ite, mul_one, mul_zero]
    calc
      _ = (b.repr x).sum (fun a za ↦
          (if a = i then za * b.repr y j else 0) +
          (if a = j then za * b.repr y i else 0)) := by
        apply Finsupp.sum_congr
        intro a ha
        by_cases hai : a = i
        · subst a
          simp only [true_and, eq_self, hij, false_and, or_false,
            if_true, if_false]
          simpa using hmulSum (b.repr x i) (b.repr y) j
        · by_cases haj : a = j
          · subst a
            simp only [hai, false_and, eq_self, true_and, false_or,
              if_false, if_true, zero_add]
            exact hmulSum (b.repr x j) (b.repr y) i
          · simp [hai, haj]
      _ = _ := by
        rw [Finsupp.sum_add]
        congr 1
        · simpa [mul_comm] using hmulSum (b.repr y j) (b.repr x) i
        · simpa [mul_comm] using hmulSum (b.repr y i) (b.repr x) j

private theorem terminalKernelLedgerPolynomial_coeff
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (g : TerminalR0Index L n → TerminalR0 L n)
    (i j : TerminalR0Index L n) :
    MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
        (terminalKernelLedgerPolynomial L n hn g) =
      if i = j then (terminalR0Basis L n hn).repr (g i) i
      else (terminalR0Basis L n hn).repr (g j) i +
        (terminalR0Basis L n hn).repr (g i) j := by
  classical
  let b := terminalR0Basis L n hn
  unfold terminalKernelLedgerPolynomial
  change (MvPolynomial.coeffAddMonoidHom
      (Finsupp.single i 1 + Finsupp.single j 1))
      (∑ s, terminalBasisPolynomial (terminalR0Basis L n hn) (g s) *
        terminalBasisPolynomial (terminalR0Basis L n hn)
          (terminalR0Basis L n hn s)) = _
  rw [map_sum]
  change (∑ s, MvPolynomial.coeff
      (Finsupp.single i 1 + Finsupp.single j 1)
        (terminalBasisPolynomial (terminalR0Basis L n hn) (g s) *
          terminalBasisPolynomial (terminalR0Basis L n hn)
            (terminalR0Basis L n hn s))) = _
  simp_rw [terminalBasisPolynomial_mul_coeff]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    rw [Finset.sum_eq_single i]
    · simp only [b, Module.Basis.repr_self, Finsupp.single_apply,
        if_pos, mul_one]
    · intro s hs hsi
      simp only [b, Module.Basis.repr_self, Finsupp.single_apply,
        if_neg hsi, mul_zero]
    · simp
  · simp only [if_neg hij]
    have hji : j ≠ i := Ne.symm hij
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single j]
      · simp only [Module.Basis.repr_self, Finsupp.single_apply,
          if_pos, mul_one]
      · intro s hs hsj
        simp only [Module.Basis.repr_self, Finsupp.single_apply,
          if_neg hsj, mul_zero]
      · simp
    · rw [Finset.sum_eq_single i]
      · simp only [Module.Basis.repr_self, Finsupp.single_apply,
          if_pos, mul_one]
      · intro s hs hsi
        simp only [Module.Basis.repr_self, Finsupp.single_apply,
          if_neg hsi, mul_zero]
      · simp

private def terminalCyclePolynomial
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    MvPolynomial (TerminalR0Index L n) ℤ := by
  classical
  let b := terminalR0Basis L n hn
  exact (collectRowLedger L (2 * n) w.initialRows).sum fun row c ↦
    match row.left with
    | [x] => c •
        (terminalBasisPolynomial b
            (terminalBoundary L n hn
              (terminalRelationR1 L n hn row.relation)) *
          terminalBasisPolynomial b
            (terminalFactorR0 L n (2 * n) x))
    | _ => 0

/-- The genuine terminal quadratic chain, grouped by its second basis factor.  Every first
factor is a complete projected relation; no homogeneous component produced by the aggregate
collector occurs in this definition. -/
private def terminalCycleKernelLedger
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    TerminalR0Index L n → TerminalR0 L n := by
  classical
  exact (collectRowLedger L (2 * n) w.initialRows).sum fun row c ↦
    match row.left with
    | [x] => c • fun s ↦
        ((terminalR0Basis L n hn).repr
          (terminalFactorR0 L n (2 * n) x) s) •
            terminalR0Projection L n (row.relation : CanonicalFreeLie L)
    | _ => 0

private theorem terminalCycleKernelLedger_mem_ker
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (s : TerminalR0Index L n) :
    terminalCycleKernelLedger hn w s ∈ (terminalR0ToW L n).ker := by
  classical
  rw [LinearMap.mem_ker]
  unfold terminalCycleKernelLedger Finsupp.sum
  rw [Finset.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro row hrow
  cases hleft : row.left with
  | nil => simp [hleft]
  | cons x xs =>
      cases xs with
      | nil =>
          simp only [hleft, Pi.smul_apply, map_zsmul]
          rw [LinearMap.mem_ker.mp
            (terminalRelationProjection_mem_ker L n hn row.relation)]
          simp
      | cons y ys => simp [hleft]

private theorem terminalCycleKernelLedger_polynomial
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    terminalKernelLedgerPolynomial L n hn
        (terminalCycleKernelLedger hn w) =
      terminalCyclePolynomial hn w := by
  classical
  change terminalKernelLedgerPolynomialLinear L n hn
      (terminalCycleKernelLedger hn w) = _
  unfold terminalCycleKernelLedger terminalCyclePolynomial
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro row hrow
  cases hleft : row.left with
  | nil =>
      change terminalKernelLedgerPolynomialLinear L n hn 0 = 0
      rw [map_zero]
  | cons x xs =>
      cases xs with
      | nil =>
          simp only [map_zsmul,
            terminalKernelLedgerPolynomialLinear_apply]
          rw [terminalKernelLedgerPolynomial_rankOne]
          rw [terminalBoundary_terminalRelationR1]
      | cons y ys =>
          change terminalKernelLedgerPolynomialLinear L n hn 0 = 0
          rw [map_zero]

/-- One coefficient of the symmetric boundary of the retained terminal factor-two chain. -/
private def terminalCycleCoefficient
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i j : TerminalR0Index L n) : ℤ := by
  classical
  let b := terminalR0Basis L n hn
  exact (collectRowLedger L (2 * n) w.initialRows).sum fun row c ↦
    match row.left with
    | [x] =>
        let dr := b.repr
          (terminalBoundary L n hn
            (terminalRelationR1 L n hn row.relation))
        let fx := b.repr (terminalFactorR0 L n (2 * n) x)
        c * (if i = j then dr i * fx i
          else dr i * fx j + dr j * fx i)
    | _ => 0

private theorem terminalCycleCoefficient_eq_coeff
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i j : TerminalR0Index L n) :
    terminalCycleCoefficient hn w i j =
      MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
        (terminalCyclePolynomial hn w) := by
  classical
  let b := terminalR0Basis L n hn
  have hpair (x y : TerminalR0 L n) :
      MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
          (terminalBasisPolynomial b x * terminalBasisPolynomial b y) =
        if i = j then b.repr x i * b.repr y i
        else b.repr x i * b.repr y j + b.repr x j * b.repr y i := by
    exact terminalBasisPolynomial_mul_coeff b x y i j
  /-
    have hdiagExponent (a c i : TerminalR0Index L n) :
        Finsupp.single a 1 + Finsupp.single c 1 =
            Finsupp.single i 1 + Finsupp.single i 1 ↔
          a = i ∧ c = i := by
      constructor
      · intro h
        have hm : ({a} + {c} : Multiset (TerminalR0Index L n)) =
            {i} + {i} := by
          apply Multiset.toFinsupp.injective
          simpa only [Multiset.toFinsupp_add,
            Multiset.toFinsupp_singleton] using h
        have ha : a ∈ ({i} + {i} :
            Multiset (TerminalR0Index L n)) := by rw [← hm]; simp
        have hc : c ∈ ({i} + {i} :
            Multiset (TerminalR0Index L n)) := by rw [← hm]; simp
        simpa using And.intro ha hc
      · rintro ⟨rfl, rfl⟩
        rfl
    have hoffExponent (a c i j : TerminalR0Index L n) (hij : i ≠ j) :
        Finsupp.single a 1 + Finsupp.single c 1 =
            Finsupp.single i 1 + Finsupp.single j 1 ↔
          (a = i ∧ c = j) ∨ (a = j ∧ c = i) := by
      constructor
      · intro h
        have hm : ({a} + {c} : Multiset (TerminalR0Index L n)) =
            {i} + {j} := by
          apply Multiset.toFinsupp.injective
          simpa only [Multiset.toFinsupp_add,
            Multiset.toFinsupp_singleton] using h
        change a ::ₘ ({c} : Multiset (TerminalR0Index L n)) =
          i ::ₘ ({j} : Multiset (TerminalR0Index L n)) at hm
        rw [Multiset.cons_eq_cons] at hm
        rcases hm with h | h
        · exact Or.inl ⟨h.1, Multiset.singleton_inj.mp h.2⟩
        · obtain ⟨hai, cs, hc, hj⟩ := h
          have hcs : cs = 0 := by
            apply Multiset.card_eq_zero.mp
            have hcard := congrArg Multiset.card hc
            simpa using hcard
          subst cs
          simp only [Multiset.cons_zero, Multiset.singleton_inj] at hc hj
          exact Or.inr ⟨hj.symm, hc⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · rfl
        · exact add_comm _ _
    unfold terminalBasisPolynomial
    change MvPolynomial.coeff _
        ((b.repr x).sum (fun a z ↦ z • MvPolynomial.X a) *
          (b.repr y).sum (fun c z ↦ z • MvPolynomial.X c)) = _
    rw [Finsupp.sum_mul]
    change (MvPolynomial.coeffAddMonoidHom _)
        ((b.repr x).sum fun a z ↦ (z • MvPolynomial.X a) *
          (b.repr y).sum fun c z ↦ z • MvPolynomial.X c) = _
    rw [map_finsuppSum]
    simp_rw [Finsupp.mul_sum]
    change (b.repr x).sum (fun a za ↦
        (MvPolynomial.coeffAddMonoidHom _)
          ((b.repr y).sum fun c zc ↦
            (za • MvPolynomial.X a) * (zc • MvPolynomial.X c))) = _
    simp_rw [map_finsuppSum]
    simp only [smul_mul_smul, map_zsmul]
    have hmulSum (r : ℤ)
        (f : TerminalR0Index L n →₀ ℤ) (k : TerminalR0Index L n) :
        f.sum (fun c zc ↦ if c = k then r * zc else 0) = r * f k := by
      calc
        _ = r * f.sum (fun c zc ↦ if c = k then zc else 0) := by
          rw [Finsupp.mul_sum]
          apply Finsupp.sum_congr
          intro c hc
          by_cases hck : c = k <;> simp [hck]
        _ = _ := by rw [Finsupp.sum_ite_self_eq']
    by_cases hij : i = j
    · subst j
      simp only [if_pos]
      change (b.repr x).sum (fun a za ↦ (b.repr y).sum fun c zc ↦
        (za * zc) * MvPolynomial.coeff
          (Finsupp.single i 1 + Finsupp.single i 1)
            (MvPolynomial.X a * MvPolynomial.X c)) = _
      simp_rw [MvPolynomial.X, MvPolynomial.monomial_mul,
        MvPolynomial.coeff_monomial, hdiagExponent]
      simp only [mul_ite, mul_one, mul_zero]
      calc
        _ = (b.repr x).sum (fun a za ↦
            if a = i then za * b.repr y i else 0) := by
          apply Finsupp.sum_congr
          intro a ha
          by_cases hai : a = i
          · subst a
            simp only [true_and, if_true]
            exact hmulSum (b.repr x i) (b.repr y) i
          · simp [hai]
        _ = _ := by
          simpa [mul_comm] using hmulSum (b.repr y i) (b.repr x) i
    · simp only [if_neg hij]
      change (b.repr x).sum (fun a za ↦ (b.repr y).sum fun c zc ↦
        (za * zc) * MvPolynomial.coeff
          (Finsupp.single i 1 + Finsupp.single j 1)
            (MvPolynomial.X a * MvPolynomial.X c)) = _
      simp_rw [MvPolynomial.X, MvPolynomial.monomial_mul,
        MvPolynomial.coeff_monomial, hoffExponent _ _ _ _ hij]
      simp only [mul_ite, mul_one, mul_zero]
      calc
        _ = (b.repr x).sum (fun a za ↦
            (if a = i then za * b.repr y j else 0) +
            (if a = j then za * b.repr y i else 0)) := by
          apply Finsupp.sum_congr
          intro a ha
          by_cases hai : a = i
          · subst a
            simp only [true_and, eq_self, hij, false_and, or_false,
              if_true, if_false]
            simpa using hmulSum (b.repr x i) (b.repr y) j
          · by_cases haj : a = j
            · subst a
              simp only [hai, false_and, eq_self, true_and, false_or,
                if_false, if_true, zero_add]
              exact hmulSum (b.repr x j) (b.repr y) i
            · simp [hai, haj]
        _ = _ := by
          rw [Finsupp.sum_add]
          congr 1
          · simpa [mul_comm] using hmulSum (b.repr y j) (b.repr x) i
          · simpa [mul_comm] using hmulSum (b.repr y i) (b.repr x) j
  -/
  unfold terminalCycleCoefficient terminalCyclePolynomial
  change (collectRowLedger L (2 * n) w.initialRows).sum (fun row c ↦
      match row.left with
      | [x] =>
          let dr := b.repr
            (terminalBoundary L n hn
              (terminalRelationR1 L n hn row.relation))
          let fx := b.repr (terminalFactorR0 L n (2 * n) x)
          c * (if i = j then dr i * fx i
            else dr i * fx j + dr j * fx i)
      | _ => 0) =
    (MvPolynomial.coeffAddMonoidHom (R := ℤ)
      (Finsupp.single i 1 + Finsupp.single j 1))
      ((collectRowLedger L (2 * n) w.initialRows).sum fun row c ↦
        match row.left with
        | [x] => c •
            (terminalBasisPolynomial b
                (terminalBoundary L n hn
                  (terminalRelationR1 L n hn row.relation)) *
              terminalBasisPolynomial b
                (terminalFactorR0 L n (2 * n) x))
        | _ => 0)
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro row hrow
  cases hleft : row.left with
  | nil => simp [hleft]
  | cons x xs =>
      cases xs with
      | nil =>
          simp only [hleft, List.cons.injEq, and_true, ↓reduceIte]
          rw [map_zsmul]
          change _ = (collectRowLedger L (2 * n) w.initialRows) row *
            MvPolynomial.coeff
              (Finsupp.single i 1 + Finsupp.single j 1)
              (terminalBasisPolynomial b
                  (terminalBoundary L n hn
                    (terminalRelationR1 L n hn row.relation)) *
                terminalBasisPolynomial b
                  (terminalFactorR0 L n (2 * n) x))
          rw [hpair]
      | cons y ys => simp [hleft]

private theorem terminalCycleCoefficient_inl_inl
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i j : TruncatedBasisIndex L (n - 1)) :
    terminalCycleCoefficient hn w (.inl i) (.inl j) =
      if i = j then
        ((terminalPSmithSorted L n hn).diagonal i : ℤ) *
          terminalPP hn w i i
      else
        ((terminalPSmithSorted L n hn).diagonal i : ℤ) *
            terminalPP hn w i j +
          ((terminalPSmithSorted L n hn).diagonal j : ℤ) *
            terminalPP hn w j i := by
  classical
  let P := terminalPSmithSorted L n hn
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    unfold terminalCycleCoefficient terminalPP
    simp only [Sum.inl.injEq, ↓reduceIte]
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro row hrow
    cases hleft : row.left with
    | nil => simp
    | cons x xs =>
        cases xs with
        | nil =>
            rw [terminalBoundary_coordinate_inl]
            simp only [terminalR0Basis_repr_inl]
            ring
        | cons y ys => simp

/-
/-! The terminal Smith conversion consumes only the zero symmetric boundary and the oriented
primitive coefficient supplied by the closed-square ledger. -/

private def terminalComparisonOfClosedSquare
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 3 ≤ n)
    (w : GoverningWitness n L a)
    (hcycle : ∀ i j : TerminalR0Index L n,
      terminalCycleCoefficient (by omega) w i j = 0)
    (hz : ((Coordinate.Data.CollectedExpression.zCoefficient
        (terminalData R (by omega))
        (terminalCollectedExpression R (by omega) w) : ℤ) :
          ZMod (2 ^ R.topExponent)) = primitiveTopRead R (by omega) w.relationSide) :
    Coordinate.Data.CollectedExpression.Comparison
      (terminalData R (by omega))
      (terminalCollectedExpression R (by omega) w)
      (primitiveTopRead R (by omega) w.relationSide) := by
  classical
  let hn1 : 1 ≤ n := by omega
  let D := terminalData R hn1
  let E := terminalCollectedExpression R hn1 w
  let P := terminalPSmithSorted L n hn1
  have hdiag (i : TruncatedBasisIndex L (n - 1)) :
      terminalPP hn1 w i i = 0 := by
    have h := hcycle (.inl i) (.inl i)
    rw [terminalCycleCoefficient_inl_inl hn1 w i i, if_pos rfl] at h
    have hd : ((P.diagonal i : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (P.diagonal_pos i))
    exact (Int.mul_eq_zero.mp h).resolve_left hd
  have hbelow {j i : TruncatedBasisIndex L (n - 1)} (hji : j < i) :
      terminalPP hn1 w j i =
        (D.dRatio j i : ℤ) * (-terminalPP hn1 w i j) := by
    have hne : j ≠ i := ne_of_lt hji
    have h := hcycle (.inl j) (.inl i)
    rw [terminalCycleCoefficient_inl_inl hn1 w j i, if_neg hne] at h
    have hdvd : P.diagonal j ∣ P.diagonal i :=
      terminalPSmithSorted_dvd_of_le R hn1 hji.le
    have hratioNat : P.diagonal j * D.dRatio j i = P.diagonal i := by
      exact Nat.mul_div_cancel' hdvd
    have hratio : (P.diagonal i : ℤ) =
        (P.diagonal j : ℤ) * (D.dRatio j i : ℤ) := by
      exact_mod_cast hratioNat.symm
    have hd : (P.diagonal j : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (P.diagonal_pos j))
    apply mul_left_cancel₀ hd
    calc
      (P.diagonal j : ℤ) * terminalPP hn1 w j i =
          -(P.diagonal i : ℤ) * terminalPP hn1 w i j := by
            linarith
      _ = (P.diagonal j : ℤ) *
          ((D.dRatio j i : ℤ) * (-terminalPP hn1 w i j)) := by
            rw [hratio]
            ring
  have hupper (i : TruncatedBasisIndex L (n - 1))
      (k : FreeLieExactBasisIndex L n) :
      D.upperSkewMul E.u i k =
        -∑ j, terminalB L n hn1 j k * terminalPP hn1 w j i := by
    change
      ((∑ j ∈ Finset.univ.filter (i < ·),
          (-terminalPP hn1 w j i) * terminalB L n hn1 j k) -
        ∑ j ∈ Finset.univ.filter (· < i),
          (D.dRatio j i : ℤ) * (-terminalPP hn1 w i j) *
            terminalB L n hn1 j k) = _
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy j i with hji | rfl | hij
    · simp only [hji, not_lt_of_ge hji.le, if_false, if_true, zero_sub]
      rw [hbelow hji]
      ring
    · simp only [lt_self_iff_false, if_false, sub_zero, hdiag]
      ring
    · simp only [hij, not_lt_of_ge hij.le, if_false, if_true, sub_zero]
      ring
  refine
    { xy_zero := ?_
      z_mod := hz
      yy_zero := ?_
      ySquare_zero := ?_ }
  · intro i k
    have h := hcycle (.inl i) (.inr k)
    rw [terminalCycleCoefficient_inl_inr hn1 w i k] at h
    unfold Coordinate.Data.CollectedExpression.xyCoefficient
    rw [hupper]
    change
      -(∑ j, terminalB L n hn1 j k * terminalPP hn1 w j i) +
          (P.diagonal i : ℤ) * terminalPQ hn1 w i k +
          terminalQP hn1 w k i *
            ((terminalQSmith L n).diagonal k : ℤ) = 0
    linear_combination h
  · intro k l hkl
    have h := hcycle (.inr k) (.inr l)
    rw [terminalCycleCoefficient_inr_inr hn1 w k l,
      if_neg (ne_of_lt hkl)] at h
    unfold Coordinate.Data.CollectedExpression.yyCoefficient
    simp only [terminalCollectedExpression, terminalData,
      if_pos hkl.le, if_pos hkl]
    change
      -(∑ i, (terminalPQ hn1 w i k * terminalB L n hn1 i l +
          terminalB L n hn1 i k * terminalPQ hn1 w i l)) +
        ((terminalQSmith L n).diagonal k : ℤ) *
            terminalQQ hn1 w k l +
        ((terminalQSmith L n).diagonal l : ℤ) *
            terminalQQ hn1 w l k = 0
    have hsum :
        (∑ i, (terminalPQ hn1 w i k * terminalB L n hn1 i l +
          terminalB L n hn1 i k * terminalPQ hn1 w i l)) =
        ∑ i, (terminalB L n hn1 i k * terminalPQ hn1 w i l +
          terminalB L n hn1 i l * terminalPQ hn1 w i k) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    linear_combination h
  · intro k
    have h := hcycle (.inr k) (.inr k)
    rw [terminalCycleCoefficient_inr_inr hn1 w k k, if_pos rfl] at h
    unfold Coordinate.Data.CollectedExpression.ySquareCoefficient
    simp only [terminalCollectedExpression, terminalData,
      if_pos le_rfl, lt_self_iff_false, if_false]
    change
      -(∑ i, terminalPQ hn1 w i k * terminalB L n hn1 i k) +
        ((terminalQSmith L n).diagonal k : ℤ) *
          (terminalQQ hn1 w k k + 0) = 0
    have hsum :
        (∑ i, terminalPQ hn1 w i k * terminalB L n hn1 i k) =
          ∑ i, terminalB L n hn1 i k * terminalPQ hn1 w i k := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    linear_combination h

private theorem primitiveTopRead_eq_zero_of_closedSquare
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 3 ≤ n)
    (w : GoverningWitness n L a)
    (hcycle : ∀ i j : TerminalR0Index L n,
      terminalCycleCoefficient (by omega) w i j = 0)
    (hz : ((Coordinate.Data.CollectedExpression.zCoefficient
        (terminalData R (by omega))
        (terminalCollectedExpression R (by omega) w) : ℤ) :
          ZMod (2 ^ R.topExponent)) = primitiveTopRead R (by omega) w.relationSide) :
    primitiveTopRead R (by omega) w.relationSide = 0 := by
  let hn1 : 1 ≤ n := by omega
  let D := terminalData R hn1
  let E := terminalCollectedExpression R hn1 w
  let comparison := terminalComparisonOfClosedSquare R hn w hcycle hz
  let system := Coordinate.Data.CollectedExpression.toCoefficientSystem
    D E comparison
  exact Coordinate.Data.coefficientSystem_vanishes D
    (pow_pos (by omega) R.topExponent)
    (fun i ↦ (terminalPSmithSorted L n hn1).diagonal_pos i)
    (terminalDataIdentities R hn) system
-/
  · rw [if_neg hij]
    have hij' : (Sum.inl i : TerminalR0Index L n) ≠ Sum.inl j := by
      exact fun h ↦ hij (Sum.inl_injective h)
    unfold terminalCycleCoefficient terminalPP
    simp only [hij', if_false]
    rw [Finsupp.mul_sum, Finsupp.mul_sum, ← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro row hrow
    cases hleft : row.left with
    | nil => simp
    | cons x xs =>
        cases xs with
        | nil =>
            rw [terminalBoundary_coordinate_inl,
              terminalBoundary_coordinate_inl]
            simp only [terminalR0Basis_repr_inl]
            ring
        | cons y ys => simp

private theorem terminalCycleCoefficient_inl_inr
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (i : TruncatedBasisIndex L (n - 1))
    (k : FreeLieExactBasisIndex L n) :
    terminalCycleCoefficient hn w (.inl i) (.inr k) =
      ((terminalPSmithSorted L n hn).diagonal i : ℤ) *
          terminalPQ hn w i k +
        ((terminalQSmith L n).diagonal k : ℤ) *
          terminalQP hn w k i -
        ∑ j, terminalB L n hn j k * terminalPP hn w j i := by
  classical
  let P := terminalPSmithSorted L n hn
  let Q := terminalQSmith L n
  unfold terminalCycleCoefficient terminalPP terminalPQ terminalQP Finsupp.sum
  simp only [reduceCtorEq, if_false]
  simp_rw [terminalBoundary_coordinate_inl,
    terminalBoundary_coordinate_inr]
  simp only [terminalR0Basis_repr_inl, terminalR0Basis_repr_inr]
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro row hrow
  cases hleft : row.left with
  | nil => simp
  | cons x xs =>
      cases xs with
      | nil =>
          simp only
          simp only [mul_add, mul_sub, sub_mul, Finset.sum_mul,
            Finset.mul_sum]
          ring_nf
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          ring
      | cons y ys => simp

private theorem terminalCycleCoefficient_inr_inr
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (k l : FreeLieExactBasisIndex L n) :
    terminalCycleCoefficient hn w (.inr k) (.inr l) =
      if k = l then
        ((terminalQSmith L n).diagonal k : ℤ) *
            terminalQQ hn w k k -
          ∑ i, terminalB L n hn i k * terminalPQ hn w i k
      else
        ((terminalQSmith L n).diagonal k : ℤ) *
            terminalQQ hn w k l +
          ((terminalQSmith L n).diagonal l : ℤ) *
            terminalQQ hn w l k -
          ∑ i, (terminalB L n hn i k * terminalPQ hn w i l +
            terminalB L n hn i l * terminalPQ hn w i k) := by
  classical
  let Q := terminalQSmith L n
  by_cases hkl : k = l
  · subst l
    rw [if_pos rfl]
    unfold terminalCycleCoefficient terminalQQ terminalPQ Finsupp.sum
    simp only [if_true]
    simp_rw [terminalBoundary_coordinate_inr]
    simp only [terminalR0Basis_repr_inr]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro row hrow
    cases hleft : row.left with
    | nil => simp
    | cons x xs =>
        cases xs with
        | nil =>
            simp only [mul_add, mul_sub, sub_mul, Finset.sum_mul,
              Finset.mul_sum]
            ring_nf
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            ring
        | cons y ys => simp
  · rw [if_neg hkl]
    have hkl' : (Sum.inr k : TerminalR0Index L n) ≠ Sum.inr l := by
      exact fun h ↦ hkl (Sum.inr_injective h)
    unfold terminalCycleCoefficient terminalQQ terminalPQ Finsupp.sum
    simp only [hkl', if_false]
    simp_rw [terminalBoundary_coordinate_inr]
    simp only [terminalR0Basis_repr_inr]
    rw [Finset.mul_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    have hswap
        (f : TruncatedBasisIndex L (n - 1) →
          FullRelationRow L (2 * n) → ℤ) :
        (∑ i, ∑ row ∈
            (collectRowLedger L (2 * n) w.initialRows).support, f i row) =
          ∑ row ∈ (collectRowLedger L (2 * n) w.initialRows).support,
            ∑ i, f i row := by
      exact Finset.sum_comm
    rw [Finset.sum_add_distrib]
    rw [hswap, hswap]
    rw [← Finset.sum_add_distrib]
    have hcombine
        (f g : FullRelationRow L (2 * n) → ℤ) :
        (∑ row ∈ (collectRowLedger L (2 * n) w.initialRows).support,
            f row) +
            ∑ row ∈ (collectRowLedger L (2 * n) w.initialRows).support,
              g row =
          ∑ row ∈ (collectRowLedger L (2 * n) w.initialRows).support,
            (f row + g row) := by
      rw [Finset.sum_add_distrib]
    rw [hcombine, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro row hrow
    cases hleft : row.left with
    | nil => simp
    | cons x xs =>
        cases xs with
        | nil =>
            simp only [mul_add, mul_sub, sub_mul, Finset.sum_mul,
              Finset.mul_sum]
            ring_nf
            congr 1
            · rw [sub_right_inj]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            · apply Finset.sum_congr rfl
              intro i hi
              ring
        | cons y ys => simp

/-! The terminal Smith conversion consumes only the zero symmetric boundary and the oriented
primitive coefficient supplied by the closed-square ledger. -/

private def terminalComparisonOfClosedSquare
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 3 ≤ n)
    (w : GoverningWitness n L a)
    (hcycle : ∀ i j : TerminalR0Index L n,
      terminalCycleCoefficient (by omega) w i j = 0)
    (hz : ((Coordinate.Data.CollectedExpression.zCoefficient
        (terminalData R (by omega))
        (terminalCollectedExpression R (by omega) w) : ℤ) :
          ZMod (2 ^ R.topExponent)) = primitiveTopRead R (by omega) w.relationSide) :
    Coordinate.Data.CollectedExpression.Comparison
      (terminalData R (by omega))
      (terminalCollectedExpression R (by omega) w)
      (primitiveTopRead R (by omega) w.relationSide) := by
  classical
  let hn1 : 1 ≤ n := by omega
  let D := terminalData R hn1
  let E := terminalCollectedExpression R hn1 w
  let P := terminalPSmithSorted L n hn1
  have hdiag (i : TruncatedBasisIndex L (n - 1)) :
      terminalPP hn1 w i i = 0 := by
    have h := hcycle (.inl i) (.inl i)
    rw [terminalCycleCoefficient_inl_inl hn1 w i i, if_pos rfl] at h
    have hd : ((P.diagonal i : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (P.diagonal_pos i))
    exact (Int.mul_eq_zero.mp h).resolve_left hd
  have hbelow {j i : TruncatedBasisIndex L (n - 1)} (hji : j < i) :
      terminalPP hn1 w j i =
        (D.dRatio j i : ℤ) * (-terminalPP hn1 w i j) := by
    have hne : j ≠ i := ne_of_lt hji
    have h := hcycle (.inl j) (.inl i)
    rw [terminalCycleCoefficient_inl_inl hn1 w j i, if_neg hne] at h
    have hdvd : P.diagonal j ∣ P.diagonal i :=
      terminalPSmithSorted_dvd_of_le R hn1 hji.le
    have hratioNat : P.diagonal j * D.dRatio j i = P.diagonal i := by
      exact Nat.mul_div_cancel' hdvd
    have hratio : (P.diagonal i : ℤ) =
        (P.diagonal j : ℤ) * (D.dRatio j i : ℤ) := by
      exact_mod_cast hratioNat.symm
    have hd : (P.diagonal j : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (P.diagonal_pos j))
    apply mul_left_cancel₀ hd
    calc
      (P.diagonal j : ℤ) * terminalPP hn1 w j i =
          -(P.diagonal i : ℤ) * terminalPP hn1 w i j := by
            linarith
      _ = (P.diagonal j : ℤ) *
          ((D.dRatio j i : ℤ) * (-terminalPP hn1 w i j)) := by
            rw [hratio]
            ring
  have hupper (i : TruncatedBasisIndex L (n - 1))
      (k : FreeLieExactBasisIndex L n) :
      D.upperSkewMul E.u i k =
        -∑ j, terminalB L n hn1 j k * terminalPP hn1 w j i := by
    change
      ((∑ j ∈ Finset.univ.filter (i < ·),
          (-terminalPP hn1 w j i) * terminalB L n hn1 j k) -
        ∑ j ∈ Finset.univ.filter (· < i),
          (D.dRatio j i : ℤ) * (-terminalPP hn1 w i j) *
            terminalB L n hn1 j k) = _
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy j i with hji | rfl | hij
    · simp only [hji, not_lt_of_ge hji.le, if_false, if_true, zero_sub]
      rw [hbelow hji]
      ring
    · simp only [lt_self_iff_false, if_false, sub_zero, hdiag]
      ring
    · simp only [hij, not_lt_of_ge hij.le, if_false, if_true, sub_zero]
      ring
  refine
    { xy_zero := ?_
      z_mod := hz
      yy_zero := ?_
      ySquare_zero := ?_ }
  · intro i k
    have h := hcycle (.inl i) (.inr k)
    rw [terminalCycleCoefficient_inl_inr hn1 w i k] at h
    unfold Coordinate.Data.CollectedExpression.xyCoefficient
    rw [hupper]
    change
      -(∑ j, terminalB L n hn1 j k * terminalPP hn1 w j i) +
          (P.diagonal i : ℤ) * terminalPQ hn1 w i k +
          terminalQP hn1 w k i *
            ((terminalQSmith L n).diagonal k : ℤ) = 0
    linarith
  · intro k l hkl
    have h := hcycle (.inr k) (.inr l)
    rw [terminalCycleCoefficient_inr_inr hn1 w k l,
      if_neg (ne_of_lt hkl)] at h
    unfold Coordinate.Data.CollectedExpression.yyCoefficient
    simp only [terminalCollectedExpression, terminalData,
      if_pos hkl.le, if_pos hkl]
    change
      -(∑ i, (terminalPQ hn1 w i k * terminalB L n hn1 i l +
          terminalB L n hn1 i k * terminalPQ hn1 w i l)) +
        ((terminalQSmith L n).diagonal k : ℤ) *
            terminalQQ hn1 w k l +
        ((terminalQSmith L n).diagonal l : ℤ) *
            terminalQQ hn1 w l k = 0
    have hsum :
        (∑ i, (terminalPQ hn1 w i k * terminalB L n hn1 i l +
          terminalB L n hn1 i k * terminalPQ hn1 w i l)) =
        ∑ i, (terminalB L n hn1 i k * terminalPQ hn1 w i l +
          terminalB L n hn1 i l * terminalPQ hn1 w i k) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    linarith
  · intro k
    have h := hcycle (.inr k) (.inr k)
    rw [terminalCycleCoefficient_inr_inr hn1 w k k, if_pos rfl] at h
    unfold Coordinate.Data.CollectedExpression.ySquareCoefficient
    simp only [terminalCollectedExpression, terminalData,
      if_pos le_rfl, lt_self_iff_false, if_false]
    change
      -(∑ i, terminalPQ hn1 w i k * terminalB L n hn1 i k) +
        ((terminalQSmith L n).diagonal k : ℤ) *
          (terminalQQ hn1 w k k + 0) = 0
    have hsum :
        (∑ i, terminalPQ hn1 w i k * terminalB L n hn1 i k) =
          ∑ i, terminalB L n hn1 i k * terminalPQ hn1 w i k := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    linarith

private theorem primitiveTopRead_eq_zero_of_closedSquare
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 3 ≤ n)
    (w : GoverningWitness n L a)
    (hcycle : ∀ i j : TerminalR0Index L n,
      terminalCycleCoefficient (by omega) w i j = 0)
    (hz : ((Coordinate.Data.CollectedExpression.zCoefficient
        (terminalData R (by omega))
        (terminalCollectedExpression R (by omega) w) : ℤ) :
          ZMod (2 ^ R.topExponent)) = primitiveTopRead R (by omega) w.relationSide) :
    primitiveTopRead R (by omega) w.relationSide = 0 := by
  let hn1 : 1 ≤ n := by omega
  let D := terminalData R hn1
  let E := terminalCollectedExpression R hn1 w
  let comparison := terminalComparisonOfClosedSquare R hn w hcycle hz
  let system := Coordinate.Data.CollectedExpression.toCoefficientSystem
    D E comparison
  exact Coordinate.Data.coefficientSystem_vanishes D
    (pow_pos (by omega) R.topExponent)
    (fun i ↦ (terminalPSmithSorted L n hn1).diagonal_pos i)
    (terminalDataIdentities R hn) system

/-! The following conversion is the terminal half of the repaired closed square.  Its input is
already a *complete* basis-indexed kernel ledger.  It contains no assertion about an individual
aggregate child. -/

private def terminalComparisonOfKernelLedger
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 3 ≤ n)
    (g : TerminalR0Index L n → TerminalR0 L n)
    (hker : ∀ s, g s ∈ (terminalR0ToW L n).ker)
    (hpoly : terminalKernelLedgerPolynomial L n (by omega) g = 0)
    (z : ZMod (2 ^ R.topExponent))
    (hz : ((Coordinate.Data.CollectedExpression.zCoefficient
        (terminalData R (by omega))
        (terminalKernelLedgerExpression R (by omega) g hker) : ℤ) :
          ZMod (2 ^ R.topExponent)) = z) :
    Coordinate.Data.CollectedExpression.Comparison
      (terminalData R (by omega))
      (terminalKernelLedgerExpression R (by omega) g hker) z := by
  classical
  let hn1 : 1 ≤ n := by omega
  let D := terminalData R hn1
  let P := terminalPSmithSorted L n hn1
  let Q := terminalQSmith L n
  let lift := terminalKernelLedgerLift L n hn1 g hker
  let E := terminalKernelLedgerExpression R hn1 g hker
  have hcoeff (s t : TerminalR0Index L n) :
      (if s = t then (terminalR0Basis L n hn1).repr (g s) s
        else (terminalR0Basis L n hn1).repr (g t) s +
          (terminalR0Basis L n hn1).repr (g s) t) = 0 := by
    have h := terminalKernelLedgerPolynomial_coeff L n hn1 g s t
    rw [hpoly] at h
    simpa using h.symm
  have hgInl (s : TerminalR0Index L n)
      (i : TruncatedBasisIndex L (n - 1)) :
      (terminalR0Basis L n hn1).repr (g s) (.inl i) =
        ((P.diagonal i : ℕ) : ℤ) *
          P.relationBasis.repr (lift s).1 i := by
    rw [← terminalBoundary_terminalKernelLedgerLift L n hn1 g hker s,
      terminalBoundary_coordinate_inl]
  have hgInr (s : TerminalR0Index L n)
      (k : FreeLieExactBasisIndex L n) :
      (terminalR0Basis L n hn1).repr (g s) (.inr k) =
        ((Q.diagonal k : ℕ) : ℤ) *
            Q.relationBasis.repr (lift s).2 k -
          ∑ i, P.relationBasis.repr (lift s).1 i *
            terminalB L n hn1 i k := by
    rw [← terminalBoundary_terminalKernelLedgerLift L n hn1 g hker s,
      terminalBoundary_coordinate_inr]
  have hdiag (i : TruncatedBasisIndex L (n - 1)) :
      P.relationBasis.repr (lift (.inl i)).1 i = 0 := by
    have h := hcoeff (.inl i) (.inl i)
    rw [if_pos rfl, hgInl] at h
    have hd : ((P.diagonal i : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (P.diagonal_pos i))
    exact (Int.mul_eq_zero.mp h).resolve_left hd
  have hbelow {j i : TruncatedBasisIndex L (n - 1)} (hji : j < i) :
      P.relationBasis.repr (lift (.inl i)).1 j =
        (D.dRatio j i : ℤ) *
          (-P.relationBasis.repr (lift (.inl j)).1 i) := by
    have hne : (Sum.inl j : TerminalR0Index L n) ≠ .inl i := by
      exact fun h ↦ (ne_of_lt hji) (Sum.inl_injective h)
    have h := hcoeff (.inl j) (.inl i)
    rw [if_neg hne, hgInl, hgInl] at h
    have hdvd : P.diagonal j ∣ P.diagonal i :=
      terminalPSmithSorted_dvd_of_le R hn1 hji.le
    have hratioNat : P.diagonal j * D.dRatio j i = P.diagonal i :=
      Nat.mul_div_cancel' hdvd
    have hratio : (P.diagonal i : ℤ) =
        (P.diagonal j : ℤ) * (D.dRatio j i : ℤ) := by
      exact_mod_cast hratioNat.symm
    have hd : (P.diagonal j : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (P.diagonal_pos j))
    apply mul_left_cancel₀ hd
    calc
      (P.diagonal j : ℤ) *
          P.relationBasis.repr (lift (.inl i)).1 j =
        -(P.diagonal i : ℤ) *
          P.relationBasis.repr (lift (.inl j)).1 i := by linarith
      _ = (P.diagonal j : ℤ) *
          ((D.dRatio j i : ℤ) *
            (-P.relationBasis.repr (lift (.inl j)).1 i)) := by
              rw [hratio]
              ring
  have hupper (i : TruncatedBasisIndex L (n - 1))
      (k : FreeLieExactBasisIndex L n) :
      D.upperSkewMul E.u i k =
        -∑ j, terminalB L n hn1 j k *
          P.relationBasis.repr (lift (.inl i)).1 j := by
    change
      ((∑ j ∈ Finset.univ.filter (i < ·),
          (-P.relationBasis.repr (lift (.inl i)).1 j) *
            terminalB L n hn1 j k) -
        ∑ j ∈ Finset.univ.filter (· < i),
          (D.dRatio j i : ℤ) *
              (-P.relationBasis.repr (lift (.inl j)).1 i) *
            terminalB L n hn1 j k) = _
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy j i with hji | rfl | hij
    · simp only [hji, not_lt_of_ge hji.le, if_false, if_true, zero_sub]
      rw [hbelow hji]
      ring
    · simp only [lt_self_iff_false, if_false, sub_zero, hdiag]
      ring
    · simp only [hij, not_lt_of_ge hij.le, if_false, if_true, sub_zero]
      ring
  refine
    { xy_zero := ?_
      z_mod := hz
      yy_zero := ?_
      ySquare_zero := ?_ }
  · intro i k
    have hne : (Sum.inl i : TerminalR0Index L n) ≠ .inr k := by simp
    have h := hcoeff (.inl i) (.inr k)
    rw [if_neg hne, hgInl, hgInr] at h
    unfold Coordinate.Data.CollectedExpression.xyCoefficient
    rw [hupper]
    change
      -(∑ j, terminalB L n hn1 j k *
          P.relationBasis.repr (lift (.inl i)).1 j) +
        (P.diagonal i : ℤ) *
          P.relationBasis.repr (lift (.inr k)).1 i +
        Q.relationBasis.repr (lift (.inl i)).2 k *
          (Q.diagonal k : ℤ) = 0
    have hsum :
        (∑ j, terminalB L n hn1 j k *
            P.relationBasis.repr (lift (.inl i)).1 j) =
          ∑ j, P.relationBasis.repr (lift (.inl i)).1 j *
            terminalB L n hn1 j k := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    linarith
  · intro k l hkl
    have hne : (Sum.inr k : TerminalR0Index L n) ≠ .inr l := by
      exact fun h ↦ (ne_of_lt hkl) (Sum.inr_injective h)
    have h := hcoeff (.inr k) (.inr l)
    rw [if_neg hne, hgInr, hgInr] at h
    unfold Coordinate.Data.CollectedExpression.yyCoefficient
    simp only [E, terminalKernelLedgerExpression, if_pos hkl.le,
      if_pos hkl]
    change
      -(∑ i, (P.relationBasis.repr (lift (.inr k)).1 i *
              terminalB L n hn1 i l +
            terminalB L n hn1 i k *
              P.relationBasis.repr (lift (.inr l)).1 i)) +
        (Q.diagonal k : ℤ) *
          Q.relationBasis.repr (lift (.inr l)).2 k +
        (Q.diagonal l : ℤ) *
          Q.relationBasis.repr (lift (.inr k)).2 l = 0
    have hsum :
        (∑ i, (P.relationBasis.repr (lift (.inr k)).1 i *
              terminalB L n hn1 i l +
            terminalB L n hn1 i k *
              P.relationBasis.repr (lift (.inr l)).1 i)) =
          ∑ i, (terminalB L n hn1 i k *
                P.relationBasis.repr (lift (.inr l)).1 i +
              terminalB L n hn1 i l *
                P.relationBasis.repr (lift (.inr k)).1 i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    rw [Finset.sum_add_distrib]
    have hsumK :
        (∑ i, P.relationBasis.repr (lift (.inr l)).1 i *
            terminalB L n hn1 i k) =
          ∑ i, terminalB L n hn1 i k *
            P.relationBasis.repr (lift (.inr l)).1 i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hsumL :
        (∑ i, P.relationBasis.repr (lift (.inr k)).1 i *
            terminalB L n hn1 i l) =
          ∑ i, terminalB L n hn1 i l *
            P.relationBasis.repr (lift (.inr k)).1 i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsumK, hsumL] at h
    linarith
  · intro k
    have h := hcoeff (.inr k) (.inr k)
    rw [if_pos rfl, hgInr] at h
    unfold Coordinate.Data.CollectedExpression.ySquareCoefficient
    simp only [E, terminalKernelLedgerExpression, if_pos le_rfl,
      lt_self_iff_false, if_false]
    change
      -(∑ i, P.relationBasis.repr (lift (.inr k)).1 i *
          terminalB L n hn1 i k) +
        (Q.diagonal k : ℤ) *
          (Q.relationBasis.repr (lift (.inr k)).2 k + 0) = 0
    linear_combination h

/-- The terminal certificate consumes only one collected expression and its four PBW
comparisons.  Keeping this statement independent of the construction of that expression
prevents the closed-square induction from being coupled to any particular wall-list
representation. -/
private theorem primitiveTopRead_eq_zero_of_comparison
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 3 ≤ n)
    (z : ZMod (2 ^ R.topExponent))
    (E : (terminalData R (by omega)).CollectedExpression)
    (hcomparison : Coordinate.Data.CollectedExpression.Comparison
      (terminalData R (by omega)) E z) :
    z = 0 := by
  let hn1 : 1 ≤ n := by omega
  let D := terminalData R hn1
  let system := Coordinate.Data.CollectedExpression.toCoefficientSystem
    D E hcomparison
  exact Coordinate.Data.coefficientSystem_vanishes D
    (pow_pos (by omega) R.topExponent)
    (fun i ↦ (terminalPSmithSorted L n hn1).diagonal_pos i)
    (terminalDataIdentities R hn) system

/-- The closed-square induction is required to return a genuine basis-indexed kernel ledger.
This wrapper is the entire terminal conversion: its zero symmetric polynomial supplies the
three integral PBW equations, while its primitive read supplies the fourth equation. -/
private theorem primitiveTopRead_eq_zero_of_kernelLedger
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 3 ≤ n)
    (g : TerminalR0Index L n → TerminalR0 L n)
    (hker : ∀ s, g s ∈ (terminalR0ToW L n).ker)
    (hpoly : terminalKernelLedgerPolynomial L n (by omega) g = 0)
    (z : ZMod (2 ^ R.topExponent))
    (hz : ((Coordinate.Data.CollectedExpression.zCoefficient
        (terminalData R (by omega))
        (terminalKernelLedgerExpression R (by omega) g hker) : ℤ) :
          ZMod (2 ^ R.topExponent)) = z) :
    z = 0 := by
  exact primitiveTopRead_eq_zero_of_comparison R hn z _
    (terminalComparisonOfKernelLedger R hn g hker hpoly z hz)

/-! ### The closed-square bridge -/

/-- The primitive top read as the linear map used by the single closed-square fold. -/
private def primitiveTopReadLinear
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n) :
    UEA ℤ (TruncatedFreeLie L (2 * n)) →ₗ[ℤ]
      ZMod (2 ^ R.topExponent) := by
  let exactEvaluation : freeLieExact L (n + 1) →ₗ[ℤ] L :=
    (canonicalFreeLieEvaluation L).toLinearMap.comp
      (freeLieExact L (n + 1)).subtype
  let topEvaluation : freeLieExact L (n + 1) →ₗ[ℤ]
      lowerCentralSeries ℤ L n :=
    exactEvaluation.codRestrict (lowerCentralSeries ℤ L n) fun z ↦ by
      have h := canonicalEvaluation_mem_lowerCentralSeries L
        (freeLieExact_mem_lieHigh L z)
      simpa using h
  exact R.topEquiv.toIntLinearEquiv.toLinearMap.comp
    (topEvaluation.comp
      ((truncatedExactComponent L (2 * n) (n + 1) (by omega)).comp
        (pbwOneFactorProjection L (2 * n))))

/-- The two external reads are kept in one linear map, so every signed occurrence family is
traversed once. -/
private def closedSquareProductRead
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n) :
    UEA ℤ (TruncatedFreeLie L (2 * n)) →ₗ[ℤ]
      MvPolynomial (TerminalR0Index L n) ℤ ×
        ZMod (2 ^ R.topExponent) :=
  (terminalLowQuadraticPBWLinear L n hn).prod
    (primitiveTopReadLinear R hn)

private def closedSquareOccurrenceRead
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n) :
    (Occurrence (ProvenancedSquarePacket L n) →₀ ℤ) →ₗ[ℤ]
      MvPolynomial (TerminalR0Index L n) ℤ ×
        ZMod (2 ^ R.topExponent) :=
  (closedSquareProductRead R hn).comp
    ((provenancedSquareCollector L n).evaluate.comp forgetPaths)

@[simp] private theorem closedSquareProductRead_apply
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (z : UEA ℤ (TruncatedFreeLie L (2 * n))) :
    closedSquareProductRead R hn z =
      (terminalLowQuadraticPBW L n hn z, primitiveTopRead R hn z) := by
  rfl

@[simp] private theorem primitiveTopReadLinear_apply
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (z : UEA ℤ (TruncatedFreeLie L (2 * n))) :
    primitiveTopReadLinear R hn z = primitiveTopRead R hn z := by
  rfl

private theorem primitiveTopRead_basisWord_eq_zero_of_sorted
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (R : ReducedData n L) (hn : 1 ≤ n)
    (xs : List (TruncatedBasisIndex L (2 * n)))
    (hsorted : xs.Pairwise (· ≤ ·)) (hlen : xs.length ≠ 1) :
    primitiveTopRead R hn
        (basisWord ℤ (TruncatedFreeLie L (2 * n))
          (TruncatedBasisIndex L (2 * n))
          (truncatedHomogeneousBasis L (2 * n)) xs) = 0 := by
  classical
  letI : DecidableEq (TruncatedBasisIndex L (2 * n)) :=
    LinearOrder.toDecidableEq
  let E := truncatedPBWLinearEquiv L (2 * n)
  let b := truncatedHomogeneousBasis L (2 * n)
  let e : TruncatedBasisIndex L (2 * n) →₀ ℕ :=
    Multiset.toFinsupp (xs : Multiset _)
  have hword : orderedMonomial ℤ (TruncatedFreeLie L (2 * n))
      (TruncatedBasisIndex L (2 * n)) b e =
        basisWord ℤ (TruncatedFreeLie L (2 * n))
          (TruncatedBasisIndex L (2 * n)) b xs := by
    simpa only [e] using
      (orderedMonomial_multiset_toFinsupp ℤ
        (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n)) b xs hsorted)
  have hE : E (MvPolynomial.monomial e 1) =
      basisWord ℤ (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n)) b xs := by
    change orderedPBWMap ℤ (TruncatedFreeLie L (2 * n))
      (TruncatedBasisIndex L (2 * n)) b
        (MvPolynomial.monomial e 1) = _
    rw [orderedPBWMap_monomial]
    exact (one_smul ℤ _).trans hword
  have hcoordinate : E.symm
      (basisWord ℤ (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n)) b xs) =
      MvPolynomial.monomial e 1 := by
    rw [← hE, E.symm_apply_apply]
  have hfactor : factorNumber L e = xs.length := by
    unfold factorNumber
    simpa only [id_eq] using
      (Multiset.toFinsupp_sum_eq (xs : Multiset
        (TruncatedBasisIndex L (2 * n))))
  have hcoeff (i : TruncatedBasisIndex L (2 * n)) :
      pbwCoeff L (2 * n)
          (basisWord ℤ (TruncatedFreeLie L (2 * n))
            (TruncatedBasisIndex L (2 * n))
            (truncatedHomogeneousBasis L (2 * n)) xs)
          (Finsupp.single i 1) = 0 := by
    change pbwCoeff L (2 * n)
        (basisWord ℤ (TruncatedFreeLie L (2 * n))
          (TruncatedBasisIndex L (2 * n)) b xs)
        (Finsupp.single i 1) = 0
    unfold pbwCoeff
    rw [hcoordinate, MvPolynomial.coeff_monomial]
    split_ifs with heq
    · have hfactorOne : factorNumber L e = 1 := by
        rw [heq]
        simp [factorNumber]
      exact (hlen (hfactor.symm.trans hfactorOne)).elim
    · rfl
  have hprojection : pbwOneFactorProjection L (2 * n)
      (basisWord ℤ (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n))
        (truncatedHomogeneousBasis L (2 * n)) xs) = 0 := by
    apply (truncatedHomogeneousBasis L (2 * n)).ext_elem
    intro i
    rw [truncatedHomogeneousBasis_repr_pbwOneFactorProjection]
    rw [map_zero]
    exact hcoeff i
  unfold primitiveTopRead
  rw [hprojection]
  unfold topComponentCoordinate
  rw [← R.topEquiv.toAddMonoidHom.map_zero]
  apply congrArg R.topEquiv
  apply Subtype.ext
  simp
  rfl

private theorem normalForm_eq_sum_of_expansion
    {P : Type u} {A : Type v} [AddCommGroup A]
    (C : FiniteTaggedCollector P A) (p : P)
    (qs : List (ℤ × P)) (h : C.expansion p = some qs) :
    C.normalForm p =
      (qs.map fun q => q.1 • C.normalForm q.2).sum := by
  rw [FiniteTaggedCollector.normalForm, C.wellFounded.fix_eq]
  change
    (match hx : C.expansion p with
    | none => Finsupp.single p 1
    | some rs => (rs.attach.map fun q : {x // x ∈ rs} =>
        q.1.1 • C.normalForm q.1.2).sum) = _
  rw [h]
  exact congrArg List.sum
    (List.attach_map_val (l := qs)
      (f := fun q => q.1 • C.normalForm q.2))

private theorem resolvedFrontier_ordered_of_initial
    {n : ℕ} {L : Type u} [LieRing L] [Finite L]
    (initial : ProvenancedSquarePacket L n →₀ ℤ)
    (hinitial : ∀ p, initial p ≠ 0 →
      (p.left L ++ p.right L).Pairwise (· ≤ ·) ∧
        match p with
        | .marked _ _ _ _ _ => True
        | .component _ c k _ _ =>
            1 ≤ k.1 + c.weight L ∧ k.1 + c.weight L ≤ 2 * n) :
    ∀ p,
      (initial.sum fun root c ↦
        c • (provenancedSquareCollector L n).normalForm root) p ≠ 0 →
      (p.left L ++ p.right L).Pairwise (· ≤ ·) ∧
      (∀ s, provenancedComponentAggregateState? L n p = some s →
        ∀ q, (aggregateComponentCollector L n).normalForm s q ≠ 0 →
          ∃ i,
            q.2.basisIndex? L = some i ∧
            (q.2.left L ++ i :: q.2.right L).Pairwise (· ≤ ·)) ∧
      match p with
      | .marked _ _ _ _ _ => True
      | .component _ _ _ _ _ =>
          ∃ s, provenancedComponentAggregateState? L n p = some s := by
  classical
  let outerGood : ProvenancedSquarePacket L n → Prop := fun p ↦
    (p.left L ++ p.right L).Pairwise (· ≤ ·) ∧
      match p with
      | .marked _ _ _ _ _ => True
      | .component _ c k _ _ =>
          1 ≤ k.1 + c.weight L ∧ k.1 + c.weight L ≤ 2 * n
  have outerExpansionGood :
      ∀ {p : ProvenancedSquarePacket L n}
        {qs : List (ℤ × ProvenancedSquarePacket L n)},
        provenancedSquareExpansion L n p = some qs → outerGood p →
          ∀ q ∈ qs, outerGood q.2 := by
    intro p qs hp hgood q hq
    rcases hgood with ⟨hordered, hguard⟩
    cases p with
    | component r c k left right =>
        simp only [provenancedSquareExpansion] at hp
        split at hp
        · contradiction
        · rename_i x leftRev hleft
          have hleftEq : left = leftRev.reverse ++ [x] :=
            List.reverse_eq_cons_iff.mp hleft
          split at hp
          · rename_i hweight
            rcases Option.some.inj hp with rfl
            rcases List.mem_pair.mp hq with rfl | rfl
            · refine ⟨?_, hguard⟩
              simpa [ProvenancedSquarePacket.left,
                ProvenancedSquarePacket.right, hleftEq, List.append_assoc]
                using hordered
            · refine ⟨?_, ?_⟩
              · have hsub : List.Sublist (leftRev.reverse ++ right)
                    (left ++ right) := by
                  rw [hleftEq, List.append_assoc]
                  exact List.Sublist.append (List.Sublist.refl leftRev.reverse)
                    (List.sublist_cons_of_sublist x (List.Sublist.refl right))
                exact hordered.sublist hsub
              · constructor
                · have hx := truncatedBasisWeight_pos L x
                  simp only [RelationContext.weight]
                  omega
                · exact hweight
          · rcases Option.some.inj hp with rfl
            simp only [List.mem_singleton] at hq
            subst q
            refine ⟨?_, hguard⟩
            simpa [ProvenancedSquarePacket.left,
              ProvenancedSquarePacket.right, hleftEq, List.append_assoc]
              using hordered
    | marked r c k left right =>
        cases right with
        | cons x right =>
            simp only [provenancedSquareExpansion, Option.some.injEq] at hp
            subst qs
            rcases List.mem_pair.mp hq with rfl | rfl
            · refine ⟨?_, trivial⟩
              simpa [ProvenancedSquarePacket.left,
                ProvenancedSquarePacket.right, List.append_assoc]
                using hordered
            · refine ⟨?_, trivial⟩
              have hsub : List.Sublist (left ++ right)
                  (left ++ x :: right) := by
                exact List.Sublist.append (List.Sublist.refl left)
                  (List.sublist_cons_of_sublist x (List.Sublist.refl right))
              exact hordered.sublist hsub
        | nil =>
            simp only [provenancedSquareExpansion] at hp
            split at hp
            · rcases Option.some.inj hp with rfl
              simp at hq
            · rename_i hk
              split at hp
              · contradiction
              · rename_i hwall
                split at hp
                · rename_i hweight
                  rcases Option.some.inj hp with rfl
                  rcases List.mem_pair.mp hq with rfl | rfl
                  · exact ⟨hordered, trivial⟩
                  · refine ⟨hordered, ?_⟩
                    constructor
                    · omega
                    · exact hweight
                · rcases Option.some.inj hp with rfl
                  simp only [List.mem_singleton] at hq
                  subst q
                  exact ⟨hordered, trivial⟩
  let C := provenancedSquareCollector L n
  have outerFrontierGood :
      ∀ (p : ProvenancedSquarePacket L n) (path : List ℕ)
        (coefficient : ℤ)
        (occurrence : Occurrence (ProvenancedSquarePacket L n)),
        outerGood p →
        rewriteFrontier C p path coefficient occurrence ≠ 0 →
          outerGood occurrence.2 := by
    intro p
    induction p using C.wellFounded.induction with
    | h p ih =>
        intro path coefficient occurrence hpGood hoccurrence
        rw [rewriteFrontier, C.wellFounded.fix_eq] at hoccurrence
        unfold frontierStep at hoccurrence
        split at hoccurrence
        · by_cases hpo : (path, p) = occurrence
          · subst occurrence
            exact hpGood
          · simp [hpo] at hoccurrence
        · rename_i qs hexpand
          have hsum (xs : List
              (Occurrence (ProvenancedSquarePacket L n) →₀ ℤ)) :
              xs.sum occurrence = (xs.map fun f ↦ f occurrence).sum := by
            induction xs with
            | nil => simp
            | cons x xs ihxs => simp [ihxs]
          rw [hsum] at hoccurrence
          have hexists : ∃ z ∈
              (List.ofFn fun i : Fin qs.length ↦
                rewriteFrontier C (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1)), z occurrence ≠ 0 := by
            by_contra hall
            push Not at hall
            apply hoccurrence
            apply List.sum_eq_zero
            intro z hz
            simp only [List.mem_map] at hz
            obtain ⟨z, hz, rfl⟩ := hz
            exact hall z hz
          obtain ⟨z, hz, hzoccurrence⟩ := hexists
          rw [List.mem_ofFn'] at hz
          obtain ⟨i, rfl⟩ := hz
          exact ih (qs.get i).2
            (C.decreases hexpand (qs.get i) (List.get_mem qs i))
            (i.1 :: path) (coefficient * (qs.get i).1) occurrence
            (outerExpansionGood hexpand hpGood
              (qs.get i) (List.get_mem qs i)) hzoccurrence
  have normalOuterGood :
      ∀ (root p : ProvenancedSquarePacket L n), outerGood root →
        (provenancedSquareCollector L n).normalForm root p ≠ 0 → outerGood p := by
    intro root p hroot hp
    have hforget := forgetPaths_rewriteFrontier
      (provenancedSquareCollector L n) root [] 1
    rw [one_smul] at hforget
    have hmapped : forgetPaths
        (rewriteFrontier (provenancedSquareCollector L n) root [] 1) p ≠ 0 := by
      rw [hforget]
      exact hp
    have hsupport : p ∈ (forgetPaths
        (rewriteFrontier (provenancedSquareCollector L n) root [] 1)).support :=
      Finsupp.mem_support_iff.mpr hmapped
    change p ∈ (Finsupp.mapDomain Prod.snd
      (rewriteFrontier (provenancedSquareCollector L n) root [] 1)).support at hsupport
    have himage := Finsupp.mapDomain_support hsupport
    rw [Finset.mem_image] at himage
    obtain ⟨occurrence, hoccurrence, hsnd⟩ := himage
    have hnonzero : rewriteFrontier (provenancedSquareCollector L n)
        root [] 1 occurrence ≠ 0 := Finsupp.mem_support_iff.mp hoccurrence
    simpa [C, hsnd] using outerFrontierGood root [] 1 occurrence hroot hnonzero
  have aggregateExpansionOrdinary :
      ∀ {p : AggregateComponentState L n}
        {qs : List (ℤ × AggregateComponentState L n)},
        aggregateComponentExpansion L n p = some qs →
          (p.2.left L ++ p.2.right L).Pairwise (· ≤ ·) →
          ∀ q ∈ qs, (q.2.2.left L ++ q.2.2.right L).Pairwise (· ≤ ·) := by
    intro p qs hp hordered q hq
    rcases p with ⟨pieceWeight, p⟩
    simp only [aggregateComponentExpansion] at hp
    split at hp
    · rcases Option.some.inj hp with rfl
      simp only [aggregateComponentBasisChildren, markedSupportPackets,
        List.mem_map] at hq
      obtain ⟨i, hi, hci, rfl⟩ := hq
      simpa [AggregateComponentAccount.left,
        AggregateComponentAccount.right] using hordered
    · rename_i i hindex
      split at hp
      · rename_i x leftRev hleft
        have hleftEq : p.left L = leftRev.reverse ++ [x] :=
          List.reverse_eq_cons_iff.mp hleft
        split at hp
        · split at hp
          · rcases Option.some.inj hp with rfl
            rcases List.mem_pair.mp hq with rfl | rfl
            · simpa [AggregateComponentAccount.left,
                AggregateComponentAccount.right, hleftEq,
                List.append_assoc] using hordered
            · have hsub : List.Sublist (leftRev.reverse ++ p.right L)
                  (p.left L ++ p.right L) := by
                rw [hleftEq, List.append_assoc]
                exact List.Sublist.append
                  (List.Sublist.refl leftRev.reverse)
                  (List.sublist_cons_of_sublist x
                    (List.Sublist.refl (p.right L)))
              exact hordered.sublist hsub
          · rcases Option.some.inj hp with rfl
            simp only [List.mem_singleton] at hq
            subst q
            simpa [AggregateComponentAccount.left,
              AggregateComponentAccount.right, hleftEq,
              List.append_assoc] using hordered
        · unfold aggregateComponentMoveRight at hp
          split at hp
          · contradiction
          · rename_i y right hright
            split at hp
            · split at hp
              · rcases Option.some.inj hp with rfl
                rcases List.mem_pair.mp hq with rfl | rfl
                · simpa [AggregateComponentAccount.left,
                    AggregateComponentAccount.right, hright,
                    List.append_assoc] using hordered
                · have hsub : List.Sublist (p.left L ++ right)
                      (p.left L ++ p.right L) := by
                    rw [hright]
                    exact List.Sublist.append (List.Sublist.refl (p.left L))
                      (List.sublist_cons_of_sublist y
                        (List.Sublist.refl right))
                  exact hordered.sublist hsub
              · rcases Option.some.inj hp with rfl
                simp only [List.mem_singleton] at hq
                subst q
                simpa [AggregateComponentAccount.left,
                  AggregateComponentAccount.right, hright,
                  List.append_assoc] using hordered
            · contradiction
      · unfold aggregateComponentMoveRight at hp
        split at hp
        · contradiction
        · rename_i y right hright
          split at hp
          · split at hp
            · rcases Option.some.inj hp with rfl
              rcases List.mem_pair.mp hq with rfl | rfl
              · simpa [AggregateComponentAccount.left,
                  AggregateComponentAccount.right, hright,
                  List.append_assoc] using hordered
              · have hsub : List.Sublist (p.left L ++ right)
                    (p.left L ++ p.right L) := by
                  rw [hright]
                  exact List.Sublist.append (List.Sublist.refl (p.left L))
                    (List.sublist_cons_of_sublist y
                      (List.Sublist.refl right))
                exact hordered.sublist hsub
            · rcases Option.some.inj hp with rfl
              simp only [List.mem_singleton] at hq
              subst q
              simpa [AggregateComponentAccount.left,
                AggregateComponentAccount.right, hright,
                List.append_assoc] using hordered
          · contradiction
  let D := aggregateComponentCollector L n
  have aggregateFrontierOrdinary :
      ∀ (s : AggregateComponentState L n) (path : List ℕ)
        (coefficient : ℤ)
        (occurrence : Occurrence (AggregateComponentState L n)),
        (s.2.left L ++ s.2.right L).Pairwise (· ≤ ·) →
        rewriteFrontier D s path coefficient occurrence ≠ 0 →
          (occurrence.2.2.left L ++ occurrence.2.2.right L).Pairwise (· ≤ ·) := by
    intro s
    induction s using D.wellFounded.induction with
    | h s ih =>
        intro path coefficient occurrence hs hoccurrence
        rw [rewriteFrontier, D.wellFounded.fix_eq] at hoccurrence
        unfold frontierStep at hoccurrence
        split at hoccurrence
        · by_cases hso : (path, s) = occurrence
          · subst occurrence
            exact hs
          · simp [hso] at hoccurrence
        · rename_i qs hexpand
          have hsum (xs : List
              (Occurrence (AggregateComponentState L n) →₀ ℤ)) :
              xs.sum occurrence = (xs.map fun f ↦ f occurrence).sum := by
            induction xs with
            | nil => simp
            | cons x xs ihxs => simp [ihxs]
          rw [hsum] at hoccurrence
          have hexists : ∃ z ∈
              (List.ofFn fun i : Fin qs.length ↦
                rewriteFrontier D (qs.get i).2 (i.1 :: path)
                  (coefficient * (qs.get i).1)), z occurrence ≠ 0 := by
            by_contra hall
            push Not at hall
            apply hoccurrence
            apply List.sum_eq_zero
            intro z hz
            simp only [List.mem_map] at hz
            obtain ⟨z, hz, rfl⟩ := hz
            exact hall z hz
          obtain ⟨z, hz, hzoccurrence⟩ := hexists
          rw [List.mem_ofFn'] at hz
          obtain ⟨i, rfl⟩ := hz
          exact ih (qs.get i).2
            (D.decreases hexpand (qs.get i) (List.get_mem qs i))
            (i.1 :: path) (coefficient * (qs.get i).1) occurrence
            (aggregateExpansionOrdinary hexpand hs
              (qs.get i) (List.get_mem qs i)) hzoccurrence
  have aggregateNormalOrdinary :
      ∀ (s q : AggregateComponentState L n),
        (s.2.left L ++ s.2.right L).Pairwise (· ≤ ·) →
        (aggregateComponentCollector L n).normalForm s q ≠ 0 →
          (q.2.left L ++ q.2.right L).Pairwise (· ≤ ·) := by
    intro s q hs hq
    have hforget := forgetPaths_rewriteFrontier
      (aggregateComponentCollector L n) s [] 1
    rw [one_smul] at hforget
    have hmapped : forgetPaths
        (rewriteFrontier (aggregateComponentCollector L n) s [] 1) q ≠ 0 := by
      rw [hforget]
      exact hq
    have hsupport : q ∈ (forgetPaths
        (rewriteFrontier (aggregateComponentCollector L n) s [] 1)).support :=
      Finsupp.mem_support_iff.mpr hmapped
    change q ∈ (Finsupp.mapDomain Prod.snd
      (rewriteFrontier (aggregateComponentCollector L n) s [] 1)).support at hsupport
    have himage := Finsupp.mapDomain_support hsupport
    rw [Finset.mem_image] at himage
    obtain ⟨occurrence, hoccurrence, hsnd⟩ := himage
    have hnonzero : rewriteFrontier (aggregateComponentCollector L n)
        s [] 1 occurrence ≠ 0 := Finsupp.mem_support_iff.mp hoccurrence
    subst q
    simpa [D] using aggregateFrontierOrdinary s [] 1 occurrence hs hnonzero
  intro p hp
  have hrootExists : ∃ root ∈ initial.support,
      (provenancedSquareCollector L n).normalForm root p ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hp
    rw [Finsupp.sum_apply]
    exact Finset.sum_eq_zero fun root hroot ↦ by
      simp [hall root hroot]
  obtain ⟨root, hrootSupport, hnormal⟩ := hrootExists
  have hpGood := normalOuterGood root p
    (hinitial root (Finsupp.mem_support_iff.mp hrootSupport)) hnormal
  refine ⟨hpGood.1, ?_, ?_⟩
  · intro s hs q hq
    have hsOrdinary : (s.2.left L ++ s.2.right L).Pairwise (· ≤ ·) := by
      cases p with
      | marked =>
          change (none : Option (AggregateComponentState L n)) = some s at hs
          cases hs
      | component r c k left right =>
          simp only [provenancedComponentAggregateState?,
            provenancedComponentAggregateStateAt?] at hs
          split at hs <;> try contradiction
          split at hs <;> try contradiction
          rcases Option.some.inj hs with rfl
          simpa [AggregateComponentAccount.left,
            AggregateComponentAccount.right] using hpGood.1
    have hordinary := aggregateNormalOrdinary s q hsOrdinary hq
    have hterminal :=
      FiniteTaggedCollector.expansion_eq_none_of_mem_normalForm_support
        (aggregateComponentCollector L n)
        (Finsupp.mem_support_iff.mpr hq)
    rcases q with ⟨pieceWeight, q⟩
    change aggregateComponentExpansion L n ⟨pieceWeight, q⟩ = none at hterminal
    simp only [aggregateComponentExpansion] at hterminal
    split at hterminal
    · contradiction
    · rename_i i hindex
      refine ⟨i, hindex, ?_⟩
      have hterminalData :
          aggregateComponentMoveRight L n q i = none ∧
            ∀ {last leftRev}, (q.left L).reverse = last :: leftRev → last ≤ i := by
        generalize hreverse : (q.left L).reverse = reversed at hterminal
        cases reversed with
        | nil =>
          dsimp only at hterminal
          refine ⟨hterminal, ?_⟩
          intro last leftRev hleft'
          simp at hleft'
        | cons last leftRev =>
          dsimp only at hterminal
          split at hterminal
          · rename_i hilast
            split at hterminal <;> simp at hterminal
          · rename_i hnotLast
            refine ⟨hterminal, ?_⟩
            intro last' leftRev' hleft'
            have hhead : last = last' := (List.cons.inj hleft').1
            subst last'
            exact le_of_not_gt hnotLast
      have hleftBound : ∀ x ∈ q.left L, x ≤ i := by
        intro x hx
        cases hrev : (q.left L).reverse with
        | nil =>
            have : q.left L = [] := by
              have := congrArg List.reverse hrev
              simpa using this
            simp [this] at hx
        | cons last leftRev =>
            have hleftEq : q.left L = leftRev.reverse ++ [last] :=
              List.reverse_eq_cons_iff.mp hrev
            have hlast : last ≤ i := hterminalData.2 hrev
            by_cases hxl : x = last
            · simpa [hxl]
            · have hxPrefix : x ∈ leftRev.reverse := by
                simpa [hleftEq, hxl] using hx
              have hparts := List.pairwise_append.mp (by
                simpa [hleftEq] using hordinary)
              exact (hparts.2.2 x hxPrefix last (by simp)).trans hlast
      have hrightBound : ∀ x ∈ q.right L, i ≤ x := by
        intro x hx
        cases hright : q.right L with
        | nil => simp [hright] at hx
        | cons first right =>
            have hfirst : i ≤ first := by
              have hmove := hterminalData.1
              unfold aggregateComponentMoveRight at hmove
              rw [hright] at hmove
              generalize hrest : first :: right = rest at hmove
              cases rest with
              | nil => simp at hrest
              | cons head tail =>
                dsimp only at hmove
                have hhead : head = first := by
                  rw [List.cons.injEq] at hrest
                  exact hrest.1.symm
                subst head
                split at hmove
                · rename_i hfirst
                  split at hmove <;> simp at hmove
                · rename_i hnotFirst
                  exact le_of_not_gt hnotFirst
            by_cases hxf : x = first
            · simpa [hxf]
            · have hxTail : x ∈ right := by simpa [hright, hxf] using hx
              have hrightPair : (first :: right).Pairwise (· ≤ ·) := by
                exact (List.pairwise_append.mp (by
                  simpa [hright] using hordinary)).2.1
              exact hfirst.trans ((List.pairwise_cons.mp hrightPair).1 x hxTail)
      apply List.pairwise_append.mpr
      refine ⟨(List.pairwise_append.mp hordinary).1,
        List.pairwise_cons.mpr ⟨hrightBound, ?_⟩, ?_⟩
      · exact (List.pairwise_append.mp hordinary).2.1
      · intro x hx y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hleftBound x hx
        · exact (List.pairwise_append.mp hordinary).2.2 x hx y hy
  · cases p with
    | marked => trivial
    | component r c k left right =>
        rcases hpGood.2 with ⟨hpos, hcut⟩
        refine ⟨⟨k.1 + c.weight L,
          .edge r c k [] hpos hcut
            (contextComponentExact L c r k.1) left right⟩, ?_⟩
        simp [provenancedComponentAggregateState?,
          provenancedComponentAggregateStateAt?, hpos, hcut]

private theorem resolvedFrontier_ordered
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    ∀ p, w.provenancedSquareFrontier p ≠ 0 →
      (p.left L ++ p.right L).Pairwise (· ≤ ·) ∧
      (∀ s, provenancedComponentAggregateState? L n p = some s →
        ∀ q, (aggregateComponentCollector L n).normalForm s q ≠ 0 →
          ∃ i,
            q.2.basisIndex? L = some i ∧
            (q.2.left L ++ i :: q.2.right L).Pairwise (· ≤ ·)) ∧
      match p with
      | .marked _ _ _ _ _ => True
      | .component _ _ _ _ _ =>
          ∃ s, provenancedComponentAggregateState? L n p = some s := by
  classical
  apply resolvedFrontier_ordered_of_initial w.provenancedSquareInitialPackets
  intro root hroot
  unfold GoverningWitness.provenancedSquareInitialPackets at hroot
  rw [Finsupp.sum_apply] at hroot
  have hexists : ∃ p ∈ w.relationWords.support,
      (w.relationWords p •
        provenancedSquarePacketsOfMultiplier L n p.1
          (word ℤ (TruncatedFreeLie L (2 * n))
            (p.2.map fun x ↦ truncatedFreeLieMk L (2 * n)
              (FreeLieAlgebra.of ℤ x)))) root ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hroot (Finset.sum_eq_zero fun p hp ↦ hall p hp)
  obtain ⟨p, hp, hpterm⟩ := hexists
  have hpacket : provenancedSquarePacketsOfMultiplier L n p.1
      (word ℤ (TruncatedFreeLie L (2 * n))
        (p.2.map fun x ↦ truncatedFreeLieMk L (2 * n)
          (FreeLieAlgebra.of ℤ x))) root ≠ 0 := by
    intro hz
    simp [hz] at hpterm
  unfold provenancedSquarePacketsOfMultiplier at hpacket
  rw [Finsupp.sum_apply] at hpacket
  let z := word ℤ (TruncatedFreeLie L (2 * n))
    (p.2.map fun x ↦ truncatedFreeLieMk L (2 * n)
      (FreeLieAlgebra.of ℤ x))
  let f := (truncatedPBWLinearEquiv L (2 * n)).symm z
  have heexists : ∃ e ∈ f.support,
      (Finsupp.single
        (.marked p.1 .hole ⟨2 * n, by omega⟩ [] (exponentWord L e))
        (f e)) root ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hpacket
    exact Finset.sum_eq_zero fun e he ↦ hall e he
  obtain ⟨e, he, heterm⟩ := heexists
  have hrootEq : root =
      .marked p.1 .hole ⟨2 * n, by omega⟩ [] (exponentWord L e) := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at heterm
  subst root
  constructor
  · simp only [ProvenancedSquarePacket.left,
      ProvenancedSquarePacket.right, List.nil_append]
    exact Multiset.pairwise_sort _ _
  · trivial

private theorem fullRelationRow_normalForm_ordered
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (root row : FullRelationRow L N)
    (hroot : (root.left ++ root.right).Pairwise (· ≤ ·))
    (hrow : (fullRelationRowCollector L N).normalForm root row ≠ 0) :
    (row.left ++ row.right).Pairwise (· ≤ ·) := by
  classical
  let C := fullRelationRowCollector L N
  let good (p : FullRelationRow L N) : Prop :=
    (p.left ++ p.right).Pairwise (· ≤ ·) →
      ∀ q, C.normalForm p q ≠ 0 →
        (q.left ++ q.right).Pairwise (· ≤ ·)
  have hall : ∀ p, good p := by
    intro p
    induction p using C.wellFounded.induction with
    | h p ih =>
        intro hp q hq
        by_cases hterminal : C.expansion p = none
        · rw [C.normalForm_eq_single_of_terminal hterminal] at hq
          by_cases hpq : p = q
          · simpa [hpq] using hp
          · simp [Finsupp.single_apply, hpq] at hq
        · obtain ⟨rows, hexpand⟩ : ∃ rows, C.expansion p = some rows := by
            cases h : C.expansion p with
            | none => exact (hterminal h).elim
            | some rows => exact ⟨rows, rfl⟩
          rw [normalForm_eq_sum_of_expansion C p rows hexpand] at hq
          have hexists : ∃ z ∈
              (rows.attach.map fun r : {x // x ∈ rows} ↦
                r.1.1 • C.normalForm r.1.2), z q ≠ 0 := by
            by_contra hz
            push Not at hz
            apply hq
            let terms := rows.attach.map fun r : {x // x ∈ rows} ↦
              r.1.1 • C.normalForm r.1.2
            have hsum : ∀ (xs : List (FullRelationRow L N →₀ ℤ)),
                (∀ z ∈ xs, z q = 0) → xs.sum q = 0 := by
              intro xs hxs
              induction xs with
              | nil => rfl
              | cons z zs ih =>
                  change z q + zs.sum q = 0
                  rw [hxs z (by simp), ih (fun y hy ↦ hxs y (by simp [hy])),
                    zero_add]
            simpa only [terms, List.attach_map_val] using hsum terms hz
          obtain ⟨z, hzmem, hzq⟩ := hexists
          simp only [List.mem_map] at hzmem
          obtain ⟨r, hrmem, rfl⟩ := hzmem
          have hr : r.1 ∈ rows := r.2
          have hrnormal : C.normalForm r.1.2 q ≠ 0 := by
            intro hzero
            simp [hzero] at hzq
          apply ih r.1.2 (C.decreases hexpand r.1 hr)
          · cases p with
            | mk left relation right =>
                simp only [C, fullRelationRowCollector,
                  fullRelationRowExpansion] at hexpand
                cases hright : right with
                | nil => simp [hright] at hexpand
                | cons x xs =>
                    have hp' : (left ++ x :: xs).Pairwise (· ≤ ·) := by
                      simpa [hright] using hp
                    simp only [hright, Option.some.injEq] at hexpand
                    subst rows
                    rcases List.mem_pair.mp hr with hr | hr
                    · rw [hr]
                      simpa [List.append_assoc] using hp'
                    · rw [hr]
                      have hsub : List.Sublist (left ++ xs)
                          (left ++ x :: xs) :=
                        List.Sublist.append (List.Sublist.refl left)
                          (List.sublist_cons_of_sublist x
                            (List.Sublist.refl xs))
                      simpa using hp'.sublist hsub
          · exact hrnormal
  exact hall root hroot row hrow

private theorem GoverningWitness.initialRows_ordered
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    ∀ row, w.initialRows row ≠ 0 →
      (row.left ++ row.right).Pairwise (· ≤ ·) := by
  classical
  intro row hrow
  unfold GoverningWitness.initialRows at hrow
  rw [Finsupp.sum_apply] at hrow
  have hpExists : ∃ p ∈ w.relationWords.support,
      (w.relationWords p •
        rowsOfMultiplier L (2 * n) p.1
          (word ℤ (TruncatedFreeLie L (2 * n))
            (p.2.map fun x ↦ truncatedFreeLieMk L (2 * n)
              (FreeLieAlgebra.of ℤ x)))) row ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hrow (Finset.sum_eq_zero fun p hp ↦ hall p hp)
  obtain ⟨p, hp, hpRow⟩ := hpExists
  have hmultiplier : rowsOfMultiplier L (2 * n) p.1
      (word ℤ (TruncatedFreeLie L (2 * n))
        (p.2.map fun x ↦ truncatedFreeLieMk L (2 * n)
          (FreeLieAlgebra.of ℤ x))) row ≠ 0 := by
    intro hz
    simp [hz] at hpRow
  unfold rowsOfMultiplier at hmultiplier
  rw [Finsupp.sum_apply] at hmultiplier
  let z := word ℤ (TruncatedFreeLie L (2 * n))
    (p.2.map fun x ↦ truncatedFreeLieMk L (2 * n)
      (FreeLieAlgebra.of ℤ x))
  let f := (truncatedPBWLinearEquiv L (2 * n)).symm z
  have heExists : ∃ e ∈ f.support,
      (Finsupp.single
        ({ left := [], relation := p.1, right := exponentWord L e } :
          FullRelationRow L (2 * n)) (f e)) row ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hmultiplier
    exact Finset.sum_eq_zero fun e he ↦ hall e he
  obtain ⟨e, he, heRow⟩ := heExists
  have hrowEq : row =
      ({ left := [], relation := p.1, right := exponentWord L e } :
        FullRelationRow L (2 * n)) := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at heRow
  subst row
  simp only [FullRelationRow.left, FullRelationRow.right, List.nil_append]
  exact Multiset.pairwise_sort _ _

private theorem collectRowLedger_ordered
    (L : Type u) [LieRing L] [Finite L] (N : ℕ)
    (c : FullRelationRow L N →₀ ℤ)
    (hc : ∀ root, c root ≠ 0 →
      (root.left ++ root.right).Pairwise (· ≤ ·)) :
    ∀ row, collectRowLedger L N c row ≠ 0 →
      (row.left ++ row.right).Pairwise (· ≤ ·) := by
  classical
  intro row hrow
  unfold collectRowLedger at hrow
  rw [Finsupp.sum_apply] at hrow
  have hrootExists : ∃ root ∈ c.support,
      (c root • (fullRelationRowCollector L N).normalForm root) row ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hrow (Finset.sum_eq_zero fun root hroot ↦ hall root hroot)
  obtain ⟨root, hroot, hterm⟩ := hrootExists
  have hnormal :
      (fullRelationRowCollector L N).normalForm root row ≠ 0 := by
    intro hz
    simp [hz] at hterm
  exact fullRelationRow_normalForm_ordered L N root row
    (hc root (Finsupp.mem_support_iff.mp hroot)) hnormal

private theorem closedSquareFrontier_ordered
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (w : GoverningWitness n L a) :
    ∀ p, w.closedSquareFrontier p ≠ 0 →
      (p.left L ++ p.right L).Pairwise (· ≤ ·) ∧
      (∀ s, provenancedComponentAggregateState? L n p = some s →
        ∀ q, (aggregateComponentCollector L n).normalForm s q ≠ 0 →
          ∃ i,
            q.2.basisIndex? L = some i ∧
            (q.2.left L ++ i :: q.2.right L).Pairwise (· ≤ ·)) ∧
      match p with
      | .marked _ _ _ _ _ => True
      | .component _ _ _ _ _ =>
          ∃ s, provenancedComponentAggregateState? L n p = some s := by
  classical
  unfold GoverningWitness.closedSquareFrontier
  apply resolvedFrontier_ordered_of_initial w.closedSquareInitialPackets
  intro root hroot
  unfold GoverningWitness.closedSquareInitialPackets
    collectedRowsToProvenanced at hroot
  rw [Finsupp.sum_apply] at hroot
  let c := collectRowLedger L (2 * n) w.initialRows
  have hrowExists : ∃ row ∈ c.support,
      (Finsupp.single
        (.marked row.relation .hole ⟨2 * n, by omega⟩ row.left [])
        (c row)) root ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hroot (Finset.sum_eq_zero fun row hrow ↦ hall row hrow)
  obtain ⟨row, hrow, hterm⟩ := hrowExists
  have hrootEq : root =
      .marked row.relation .hole ⟨2 * n, by omega⟩ row.left [] := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at hterm
  subst root
  constructor
  · simp only [ProvenancedSquarePacket.left,
      ProvenancedSquarePacket.right, List.append_nil]
    have hordered := collectRowLedger_ordered L (2 * n) w.initialRows
      w.initialRows_ordered row (Finsupp.mem_support_iff.mp hrow)
    have hright : row.right = [] := by
      by_contra hne
      exact Finsupp.mem_support_iff.mp hrow
        (collectRowLedger_apply_eq_zero_of_right_ne_nil L (2 * n)
          w.initialRows row hne)
    simpa [hright] using hordered
  · trivial

/-! The first local read needed by the closed square: after the distinguished component has
been completely PBW-collected, its quadratic kernel ledger is exactly the quadratic PBW
projection of its UEA value.  The ordering hypothesis is intentionally supplied by the outer
provenance theorem, rather than asserted for arbitrary aggregate roots. -/
private theorem aggregateComponentQuadraticLedger_polynomial_eq
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) (p : AggregateComponentState L n)
    (hordered : ∀ q,
      (aggregateComponentCollector L n).normalForm p q ≠ 0 →
        ∃ i,
          q.2.basisIndex? L = some i ∧
            (q.2.left L ++ i :: q.2.right L).Pairwise (· ≤ ·)) :
    terminalKernelLedgerPolynomial L n hn
        (aggregateComponentQuadraticLedger L n hn p) =
      terminalLowQuadraticPBW L n hn (aggregateComponentValue L n p) := by
  classical
  let C := aggregateComponentCollector L n
  let Q := terminalLowQuadraticPBWLinear L n hn
  have hevaluate : C.evaluate (C.normalForm p) = aggregateComponentValue L n p :=
    C.evaluate_normalForm p
  change terminalKernelLedgerPolynomialLinear L n hn
      (aggregateComponentQuadraticLedger L n hn p) = Q (aggregateComponentValue L n p)
  rw [← hevaluate]
  unfold aggregateComponentQuadraticLedger
  rw [map_finsuppSum]
  change _ = Q ((C.normalForm p).sum fun q c ↦
    c • aggregateComponentValue L n q)
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro q hq
  rw [map_zsmul, map_zsmul]
  congr 1
  obtain ⟨i, hi, hsorted⟩ := hordered q (Finsupp.mem_support_iff.mp hq)
  rcases q with ⟨pieceWeight, q⟩
  have hexact : truncatedFreeLieMk L (2 * n)
        (q.exact L : CanonicalFreeLie L) =
      truncatedHomogeneousBasis L (2 * n) i :=
    q.exact_eq_basis_of_basisIndex L i hi
  have hvalue : aggregateComponentValue L n ⟨pieceWeight, q⟩ =
      basisWord ℤ (TruncatedFreeLie L (2 * n))
        (TruncatedBasisIndex L (2 * n))
        (truncatedHomogeneousBasis L (2 * n))
        (q.left L ++ i :: q.right L) := by
    unfold aggregateComponentValue AggregateComponentAccount.value
    rw [hexact]
    simp only [basisWord, List.map_append, List.map_cons, word_append,
      word_cons]
    noncomm_ring
  by_cases hone : (q.left L ++ q.right L).length = 1
  · obtain ⟨x, hx⟩ : ∃ x, q.left L ++ q.right L = [x] := by
      exact List.length_eq_one_iff.mp hone
    change terminalKernelLedgerPolynomial L n hn
        (aggregateComponentLeafQuadraticLedger L n hn ⟨pieceWeight, q⟩) =
      terminalLowQuadraticPBW L n hn
        (aggregateComponentValue L n ⟨pieceWeight, q⟩)
    rw [aggregateComponentLeafQuadraticLedger_polynomial
      L n hn pieceWeight q x hx]
    have hprojection : terminalR0Projection L n
        (q.exact L : CanonicalFreeLie L) =
        terminalFactorR0 L n (2 * n) i := by
      have h := congrArg (terminalR0ProjectionTruncated L n hn) hexact
      simpa only [terminalR0ProjectionTruncated_mk,
        terminalR0ProjectionTruncated_basis] using h
    rw [hprojection, hvalue]
    cases hleft : q.left L with
    | nil =>
        have hright : q.right L = [x] := by simpa [hleft] using hx
        rw [hright]
        simp only [List.nil_append, List.map_cons, List.map_nil, basisWord,
          word_cons, word_nil, mul_one]
        rw [terminalLowQuadraticPBW_basis_mul_basis_all]
        by_cases hilow : truncatedBasisWeight L i ≤ n
        · by_cases hxlow : truncatedBasisWeight L x ≤ n
          · rw [if_pos ⟨hilow, hxlow⟩]
          · rw [if_neg (fun h ↦ hxlow h.2),
              terminalFactorR0_eq_zero_of_weight_gt L n (2 * n) x (by omega)]
            simp [terminalBasisPolynomial]
        · rw [if_neg (fun h ↦ hilow h.1),
            terminalFactorR0_eq_zero_of_weight_gt L n (2 * n) i (by omega)]
          simp [terminalBasisPolynomial]
    | cons y ys =>
        have hys : ys = [] := by
          by_contra hne
          have : 2 ≤ (q.left L ++ q.right L).length := by
            rw [hleft]
            cases ys with
            | nil => contradiction
            | cons z zs => simp
          omega
        subst ys
        have hyx : y = x := by
          have := congrArg List.head? hx
          simpa [hleft] using this
        subst y
        have hright : q.right L = [] := by
          simpa [hleft] using hx
        rw [hright]
        simp only [List.append_nil, List.singleton_append, List.map_cons,
          List.map_nil, basisWord,
          word_cons, word_nil, mul_one, one_mul]
        rw [terminalLowQuadraticPBW_basis_mul_basis_all]
        by_cases hxlow : truncatedBasisWeight L x ≤ n
        · by_cases hilow : truncatedBasisWeight L i ≤ n
          · rw [if_pos ⟨hxlow, hilow⟩, mul_comm]
          · rw [if_neg (fun h ↦ hilow h.2),
              terminalFactorR0_eq_zero_of_weight_gt L n (2 * n) i (by omega)]
            simp [terminalBasisPolynomial]
        · rw [if_neg (fun h ↦ hxlow h.1),
            terminalFactorR0_eq_zero_of_weight_gt L n (2 * n) x (by omega)]
          simp [terminalBasisPolynomial]
  · have hfullLength : (q.left L ++ i :: q.right L).length ≠ 2 := by
      simp only [List.length_append, List.length_cons] at hone ⊢
      omega
    have hleaf : aggregateComponentLeafQuadraticLedger L n hn
        ⟨pieceWeight, q⟩ = 0 := by
      unfold aggregateComponentLeafQuadraticLedger
      cases hordinary : q.left L ++ q.right L with
      | nil => simp [hordinary]
      | cons x xs =>
          cases xs with
          | nil =>
              exfalso
              apply hone
              simp [hordinary]
          | cons y ys => simp [hordinary]
    rw [hleaf, map_zero, hvalue]
    exact terminalLowQuadraticPBW_basisWord_eq_zero_of_sorted
      L n hn _ hsorted hfullLength |>.symm

/-! The quadratic part of the complete provenanced frontier is the literal quadratic PBW
read of the governing relation side.  This statement is unconditional; the governing PBW
vanishing is used only after this exact identity has been established. -/
private theorem closedSquareKernelLedger_polynomial_eq
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    terminalKernelLedgerPolynomial L n hn
        (w.closedSquareKernelLedger hn) =
      terminalLowQuadraticPBW L n hn w.relationSide := by
  classical
  let P := terminalKernelLedgerPolynomialLinear L n hn
  let Q := terminalLowQuadraticPBWLinear L n hn
  have hevaluate := w.evaluate_provenancedSquareFrontier
  change P (w.closedSquareKernelLedger hn) = Q w.relationSide
  rw [← hevaluate]
  unfold GoverningWitness.closedSquareKernelLedger
  rw [map_finsuppSum]
  change _ = Q (w.provenancedSquareFrontier.sum fun p c ↦
    c • ProvenancedSquarePacket.value L n p)
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, map_zsmul]
  congr 1
  have hpne : w.provenancedSquareFrontier p ≠ 0 :=
    Finsupp.mem_support_iff.mp hp
  have hdata := resolvedFrontier_ordered w p hpne
  have hterminal : provenancedSquareExpansion L n p = none := by
    by_contra hnonterminal
    apply hpne
    unfold GoverningWitness.provenancedSquareFrontier
    rw [Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro root hroot
    simp [(provenancedSquareCollector L n).normalForm_apply_eq_zero_of_nonterminal
      root p hnonterminal]
  cases p with
  | marked r c k left right =>
      have hright : right = [] := by
        cases right with
        | nil => rfl
        | cons x xs =>
            simp [provenancedSquareExpansion] at hterminal
      subst right
      simp only [provenancedSquareExpansion] at hterminal
      split at hterminal
      · contradiction
      · rename_i hk
        split at hterminal
        · rename_i hwall
          unfold provenancedPacketQuadraticLedger
            provenancedComponentAggregateState?
            provenancedComponentAggregateStateAt?
          simp only [provenancedMarkedQuadraticLedger, add_zero]
          rcases hwall with hwall | hwall
          · rcases hwall with ⟨rfl, hactive⟩
            simp only [ite_false, ProvenancedSquarePacket.value,
              basisWord_nil, one_mul, mul_one]
            change P 0 = Q
              (UniversalEnvelopingAlgebra.ι ℤ
                (truncatedFreeLieMk L (2 * n)
                  (c.applyFree L (markedPrefixFree L k.1 r))))
            rw [map_zero]
            exact (terminalLowQuadraticPBW_iota L n hn _).symm
          · obtain ⟨x, rfl, hactive⟩ := hwall
            simp only [ProvenancedSquarePacket.value, basisWord_cons,
              basisWord_nil, mul_one, one_mul]
            rw [if_pos hactive]
            change P (fun s ↦
                ((terminalR0Basis L n hn).repr
                  (terminalFactorR0 L n (2 * n) x) s) •
                    terminalR0Projection L n
                      (c.relation L r : CanonicalFreeLie L)) =
              Q (UniversalEnvelopingAlgebra.ι ℤ
                    (truncatedHomogeneousBasis L (2 * n) x) *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (truncatedFreeLieMk L (2 * n)
                      (c.applyFree L (markedPrefixFree L k.1 r))))
            rw [terminalKernelLedgerPolynomialLinear_apply,
              terminalKernelLedgerPolynomial_rankOne]
            simpa only [Q, terminalLowQuadraticPBWLinear,
              terminalBoundary_terminalRelationR1] using
              (terminalWallQuadratic_left L n hn r c k.1 hactive x).symm
        · split at hterminal <;> contradiction
  | component r c k left right =>
      have hleft : left = [] := by
        simp only [provenancedSquareExpansion] at hterminal
        generalize hreverse : left.reverse = reversed at hterminal
        cases reversed with
        | nil =>
          dsimp only at hterminal
          have := congrArg List.reverse hreverse
          simpa using this
        | cons x xs =>
          dsimp only at hterminal
          split at hterminal <;> simp at hterminal
      subst left
      obtain ⟨s, hs⟩ := hdata.2.2
      unfold provenancedPacketQuadraticLedger
        provenancedMarkedQuadraticLedger
      rw [hs]
      simp only [zero_add]
      have haggregate := aggregateComponentQuadraticLedger_polynomial_eq
        L n hn s (hdata.2.1 s hs)
      change terminalKernelLedgerPolynomial L n hn
          (aggregateComponentQuadraticLedger L n hn s) =
        terminalLowQuadraticPBW L n hn
          (ProvenancedSquarePacket.value L n
            (.component r c k [] right))
      rw [haggregate]
      congr 1
      simp only [provenancedComponentAggregateState?,
        provenancedComponentAggregateStateAt?] at hs
      split at hs <;> try contradiction
      split at hs <;> try contradiction
      have hstate := Option.some.inj hs
      rw [← hstate]
      rfl

/-! The governing coefficients kill the complete quadratic PBW read.  This is deliberately
stated for the raw closed-square ledger: the later correction-cancellation argument is still
needed before replacing it by the genuine pointwise-kernel terminal cycle. -/
private theorem closedSquareKernelLedger_polynomial_eq_zero
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a)
    (hgoverning : ∀ e : TruncatedBasisIndex L (2 * n) →₀ ℕ,
      totalWeight L e ≤ 2 * n →
        pbwCoeff L (2 * n) w.relationSide e =
          pbwCoeff L (2 * n)
            (UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk L (2 * n)
                (w.zTilde : CanonicalFreeLie L))) e) :
    terminalKernelLedgerPolynomial L n hn
        (w.closedSquareKernelLedger hn) = 0 := by
  rw [closedSquareKernelLedger_polynomial_eq hn w]
  exact terminalLowQuadraticPBW_relationSide_eq_zero
    n hn L a w hgoverning

/-! The primitive half of the same frontier evaluation.  Unlike the quadratic ledger this is
only a scalar equality; its terminal summands still have to be classified by the marked
rectangle before the Smith `z`-coordinate can be read. -/
private theorem closedSquareFrontier_primitive_eq
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    w.provenancedSquareFrontier.sum (fun p c ↦
        c • primitiveTopRead R hn (ProvenancedSquarePacket.value L n p)) =
      primitiveTopRead R hn w.relationSide := by
  have h := congrArg (primitiveTopReadLinear R hn)
    w.evaluate_provenancedSquareFrontier
  change primitiveTopReadLinear R hn
      (w.provenancedSquareFrontier.sum fun p c ↦
        c • ProvenancedSquarePacket.value L n p) =
    primitiveTopReadLinear R hn w.relationSide at h
  simpa only [map_finsuppSum, map_zsmul,
    primitiveTopReadLinear_apply] using h

/-! The terminal-wall part of the collected-row frontier.  These three small declarations
are the entry point of the closed-square induction: they identify the marked singleton wall
without making any claim about the quadratic corrections carried by component packets. -/

private def provenancedMarkedQuadraticRead
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n) :
    (ProvenancedSquarePacket L n →₀ ℤ) →ₗ[ℤ]
      (TerminalR0Index L n → TerminalR0 L n) :=
  Finsupp.linearCombination ℤ (provenancedMarkedQuadraticLedger L n hn)

private theorem provenancedMarkedQuadraticRead_normalForm_component
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (r : CanonicalLieRelationsIdeal L)
    (c : RelationContext L (2 * n))
    (k : Fin (2 * n + 1))
    (left right : List (TruncatedBasisIndex L (2 * n))) :
    provenancedMarkedQuadraticRead L n hn
        ((provenancedSquareCollector L n).normalForm
          (.component r c k left right)) = 0 := by
  classical
  let C := provenancedSquareCollector L n
  let M := provenancedMarkedQuadraticRead L n hn
  let good : ProvenancedSquarePacket L n → Prop
    | .marked _ _ _ _ _ => True
    | p@(.component _ _ _ _ _) => M (C.normalForm p) = 0
  have hall : ∀ p, good p := by
    intro p
    induction p using C.wellFounded.induction with
    | h p ih =>
        cases p with
        | marked => trivial
        | component r c k left right =>
            change M (C.normalForm (.component r c k left right)) = 0
            cases hleft : left.reverse with
            | nil =>
                have hexpand : C.expansion (.component r c k left right) = none := by
                  dsimp only [C, provenancedSquareCollector]
                  simp only [provenancedSquareExpansion]
                  rw [hleft]
                rw [C.normalForm_eq_single_of_terminal hexpand]
                simp [M, provenancedMarkedQuadraticRead,
                  provenancedMarkedQuadraticLedger]
            | cons x leftRev =>
                by_cases hweight : k.1 + (c.lieRight x).weight L ≤ 2 * n
                · have hexpand : C.expansion (.component r c k left right) =
                      some
                        [(1, .component r c k leftRev.reverse (x :: right)),
                         (-1, .component r (.lieRight c x) k
                            leftRev.reverse right)] := by
                    dsimp only [C, provenancedSquareCollector]
                    simp only [provenancedSquareExpansion]
                    rw [hleft]
                    simp [hweight]
                  rw [normalForm_eq_sum_of_expansion C _ _ hexpand,
                    List.map_cons]
                  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                    Prod.fst, Prod.snd, one_smul, neg_one_smul, add_zero,
                    map_sub]
                  have hmain := ih
                    (.component r c k leftRev.reverse (x :: right))
                    (C.decreases hexpand
                      (1, .component r c k leftRev.reverse (x :: right))
                      (by simp))
                  have hcorrection := ih
                    (.component r (.lieRight c x) k leftRev.reverse right)
                    (C.decreases hexpand
                      (-1, .component r (.lieRight c x) k
                        leftRev.reverse right) (by simp))
                  change M (C.normalForm
                      (.component r c k leftRev.reverse (x :: right))) = 0 at hmain
                  change M (C.normalForm
                      (.component r (.lieRight c x) k
                        leftRev.reverse right)) = 0 at hcorrection
                  rw [map_add, map_neg]
                  rw [hmain, hcorrection]
                  simp
                · have hexpand : C.expansion (.component r c k left right) =
                      some [(1, .component r c k leftRev.reverse (x :: right))] := by
                    dsimp only [C, provenancedSquareCollector]
                    simp only [provenancedSquareExpansion]
                    rw [hleft]
                    simp [hweight]
                  rw [normalForm_eq_sum_of_expansion C _ _ hexpand,
                    List.map_cons]
                  simp only [List.map_nil, List.sum_cons, List.sum_nil,
                    Prod.fst, Prod.snd, one_smul, add_zero]
                  have hmain := ih
                    (.component r c k leftRev.reverse (x :: right))
                    (C.decreases hexpand
                      (1, .component r c k leftRev.reverse (x :: right))
                      (by simp))
                  change M (C.normalForm
                      (.component r c k leftRev.reverse (x :: right))) = 0 at hmain
                  simpa using hmain
  simpa [good, C, M] using hall (.component r c k left right)

private theorem provenancedMarkedQuadraticRead_normalForm_collectedRoot
    (L : Type u) [LieRing L] [Finite L]
    (n : ℕ) (hn : 1 ≤ n)
    (r : CanonicalLieRelationsIdeal L)
    (k : Fin (2 * n + 1))
    (left : List (TruncatedBasisIndex L (2 * n))) :
    provenancedMarkedQuadraticRead L n hn
        ((provenancedSquareCollector L n).normalForm
          (.marked r .hole k left [])) =
      match left with
      | [x] => if n ≤ k.1 then fun s ↦
          ((terminalR0Basis L n hn).repr
            (terminalFactorR0 L n (2 * n) x) s) •
              terminalR0Projection L n (r : CanonicalFreeLie L)
        else 0
      | _ => 0 := by
  classical
  let C := provenancedSquareCollector L n
  let M := provenancedMarkedQuadraticRead L n hn
  let target (r : CanonicalLieRelationsIdeal L)
      (k : Fin (2 * n + 1))
      (left : List (TruncatedBasisIndex L (2 * n))) :=
    match left with
    | [x] => if n ≤ k.1 then fun s ↦
        ((terminalR0Basis L n hn).repr
          (terminalFactorR0 L n (2 * n) x) s) •
            terminalR0Projection L n (r : CanonicalFreeLie L)
      else 0
    | _ => 0
  let good (p : ProvenancedSquarePacket L n) : Prop :=
    ∀ (r : CanonicalLieRelationsIdeal L)
      (k : Fin (2 * n + 1))
      (left : List (TruncatedBasisIndex L (2 * n))),
      p = .marked r .hole k left [] →
        M (C.normalForm p) = target r k left
  have hall : ∀ p, good p := by
    intro p
    induction p using C.wellFounded.induction with
    | h p ih =>
        intro r k left hp
        subst p
        by_cases hk0 : k.1 = 0
        · have hexpand : C.expansion (.marked r .hole k left []) = some [] := by
            dsimp only [C, provenancedSquareCollector]
            simp only [provenancedSquareExpansion]
            simp [hk0, RelationContext.weight]
          rw [normalForm_eq_sum_of_expansion C _ _ hexpand]
          simp only [List.map_nil, List.sum_nil, map_zero]
          unfold target
          cases left with
          | nil => rfl
          | cons x xs =>
              cases xs with
              | nil =>
                  change 0 = if n ≤ k.1 then (fun s ↦
                    ((terminalR0Basis L n hn).repr
                      (terminalFactorR0 L n (2 * n) x) s) •
                        terminalR0Projection L n
                          (r : CanonicalFreeLie L)) else 0
                  rw [if_neg (by omega)]
              | cons y ys => rfl
        · by_cases hwall :
              (left = [] ∧ k.1 +
                (RelationContext.hole : RelationContext L (2 * n)).weight L = n + 1) ∨
              (∃ x, left = [x] ∧
                k.1 +
                  (RelationContext.hole : RelationContext L (2 * n)).weight L = n)
          · have hexpand : C.expansion (.marked r .hole k left []) = none := by
              dsimp only [C, provenancedSquareCollector]
              simp only [provenancedSquareExpansion]
              split <;> simp_all
            rw [C.normalForm_eq_single_of_terminal hexpand]
            unfold M provenancedMarkedQuadraticRead
            rw [Finsupp.linearCombination_single]
            rcases hwall with hwall | hwall
            · rcases hwall with ⟨rfl, hactive⟩
              simp [provenancedMarkedQuadraticLedger, target]
            · obtain ⟨x, rfl, hactive⟩ := hwall
              simp only [RelationContext.weight] at hactive
              have hnk : n ≤ k.1 := by omega
              simp only [one_smul]
              unfold provenancedMarkedQuadraticLedger target
              simp only [RelationContext.weight, zero_add]
              rw [if_pos hactive, if_pos hnk]
              have hrelation :
                  (RelationContext.hole : RelationContext L (2 * n)).relation L r = r := by
                apply Subtype.ext
                rfl
              rw [hrelation]
          · let k' : Fin (2 * n + 1) := ⟨k.1 - 1, by omega⟩
            have hweight :
              k.1 +
                  RelationContext.weight L
                    (RelationContext.hole : RelationContext L (2 * n)) ≤ 2 * n := by
              simp only [RelationContext.weight]
              omega
            have hexpand : C.expansion (.marked r .hole k left []) =
                some
                  [(1, .marked r .hole k' left []),
                   (1, .component r .hole k left [])] := by
              dsimp only [C, provenancedSquareCollector]
              simp only [provenancedSquareExpansion]
              rw [dif_neg hk0, dif_neg hwall, dif_pos hweight]
            rw [normalForm_eq_sum_of_expansion C _ _ hexpand,
              List.map_cons]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              Prod.fst, Prod.snd, one_smul, add_zero]
            rw [map_add]
            have hresidual := ih (.marked r .hole k' left [])
              (C.decreases hexpand
                (1, .marked r .hole k' left []) (by simp))
              r k' left rfl
            have hcomponent :=
              provenancedMarkedQuadraticRead_normalForm_component
                L n hn r .hole k left []
            change M (C.normalForm (.component r .hole k left [])) = 0
              at hcomponent
            change
              M (C.normalForm (.marked r .hole k' left [])) +
                  M (C.normalForm (.component r .hole k left [])) =
                target r k left
            rw [hresidual, hcomponent, add_zero]
            unfold target
            cases left with
            | nil => rfl
            | cons x xs =>
                cases xs with
                | nil =>
                    have hkn : k.1 ≠ n := by
                      intro hkn
                      apply hwall
                      exact Or.inr ⟨x, rfl, by
                        simpa [RelationContext.weight] using hkn⟩
                    simp only [target]
                    by_cases hnk : n ≤ k.1
                    · have hnlt : n < k.1 := lt_of_le_of_ne hnk
                        (Ne.symm hkn)
                      rw [if_pos hnk, if_pos (by dsimp [k']; omega)]
                    · rw [if_neg hnk, if_neg (by dsimp [k']; omega)]
                | cons y ys => rfl
  simpa [good, target, C, M] using
    hall (.marked r .hole k left []) r k left rfl

/-- The marked walls of the post-collection frontier are exactly the genuine terminal
Smith chain.  This statement deliberately says nothing about component packets: their PBW
corrections are accounted for separately in the closed-square read. -/
private theorem closedSquareFrontier_markedRead_eq_terminalCycleKernelLedger
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    provenancedMarkedQuadraticRead L n hn w.closedSquareFrontier =
      terminalCycleKernelLedger hn w := by
  classical
  unfold GoverningWitness.closedSquareFrontier
  rw [map_finsuppSum]
  unfold GoverningWitness.closedSquareInitialPackets
  unfold collectedRowsToProvenanced terminalCycleKernelLedger
  rw [Finsupp.sum_sum_index
    (fun _ ↦ by simp)
    (fun _ a b ↦ by simp [add_smul])]
  apply Finsupp.sum_congr
  intro row hrow
  rw [Finsupp.sum_single_index (by simp)]
  rw [map_zsmul,
    provenancedMarkedQuadraticRead_normalForm_collectedRoot]
  cases hleft : row.left with
  | nil => simp [hleft]
  | cons x xs =>
      cases xs with
      | nil =>
          simp only [hleft]
          rw [if_pos (by omega)]
      | cons y ys => simp [hleft]

private theorem closedSquareFrontier_markedPolynomial_eq_terminalCyclePolynomial
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (hn : 1 ≤ n) (w : GoverningWitness n L a) :
    terminalKernelLedgerPolynomial L n hn
        (provenancedMarkedQuadraticRead L n hn w.closedSquareFrontier) =
      terminalCyclePolynomial hn w := by
  rw [closedSquareFrontier_markedRead_eq_terminalCycleKernelLedger hn w,
    terminalCycleKernelLedger_polynomial]

/-- Both PBW reads of the post-collection closed-square frontier are its two reads of the
governing relation side.  This is the exact starting boundary for the Stokes calculation;
in particular it does not import a result about the distinct raw frontier. -/
private theorem closedSquareFrontier_productRead_eq
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 1 ≤ n)
    (w : GoverningWitness n L a) :
    w.closedSquareFrontier.sum (fun p c ↦
        c • closedSquareProductRead R hn
          (ProvenancedSquarePacket.value L n p)) =
      (terminalLowQuadraticPBW L n hn w.relationSide,
        primitiveTopRead R hn w.relationSide) := by
  have h := congrArg (closedSquareProductRead R hn)
    w.evaluate_closedSquareFrontier
  change closedSquareProductRead R hn
      (w.closedSquareFrontier.sum fun p c ↦
        c • ProvenancedSquarePacket.value L n p) =
    closedSquareProductRead R hn w.relationSide at h
  simpa only [map_finsuppSum, map_zsmul,
    closedSquareProductRead_apply] using h

private theorem closedSquareFrontier_productRead_eq_zero_primitive
    {n : ℕ} {L : Type u} [LieRing L] [Finite L] {a : L}
    (R : ReducedData n L) (hn : 1 ≤ n)
    (w : GoverningWitness n L a)
    (hgoverning : ∀ e : TruncatedBasisIndex L (2 * n) →₀ ℕ,
      totalWeight L e ≤ 2 * n →
        pbwCoeff L (2 * n) w.relationSide e =
          pbwCoeff L (2 * n)
            (UniversalEnvelopingAlgebra.ι ℤ
              (truncatedFreeLieMk L (2 * n)
                (w.zTilde : CanonicalFreeLie L))) e) :
    w.closedSquareFrontier.sum (fun p c ↦
        c • closedSquareProductRead R hn
          (ProvenancedSquarePacket.value L n p)) =
      (0, primitiveTopRead R hn w.relationSide) := by
  rw [closedSquareFrontier_productRead_eq R hn w,
    terminalLowQuadraticPBW_relationSide_eq_zero
      n hn L a w hgoverning]

end

end LieRings.DimensionSubring.MetabelianOdd
