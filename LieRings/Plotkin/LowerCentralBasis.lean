import LieRings.Plotkin.FilteredPBW
import LieRings.DimensionSubring.Centrality
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.SetTheory.Cardinal.Order

/-!
# A basis adapted to a finite lower-central filtration

Over a field, a finite descending chain of subspaces admits a simultaneous adapted basis.  We
construct it by repeatedly extending a basis set for the deeper term inside the preceding term.
The weight of a final basis vector is the largest lower-central term containing it.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

variable {R : Type u} [Field R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]

private structure AdaptedStage
    (R : Type u) (L : Type v) [Field R] [LieRing L] [LieAlgebra R L]
    (c : ℕ) (k : ℕ) where
  carrier : Set L
  independent : LinearIndepOn R id carrier
  subset_lowerCentral : carrier ⊆ lowerCentralSeries R L (c - k)
  span_eq : Submodule.span R carrier = lowerCentralSeries R L (c - k)

/-- Starting at the zero `c`th term, repeatedly extend an independent set inside the next
lower-central term. -/
private def adaptedStage (c : ℕ) (hclass : lowerCentralSeries R L c = ⊥) :
    (k : ℕ) → AdaptedStage R L c k
  | 0 =>
      { carrier := ∅
        independent := by simp
        subset_lowerCentral := Set.empty_subset _
        span_eq := by simp [hclass] }
  | k + 1 => by
      let previous := adaptedStage c hclass k
      let target : Submodule R L := lowerCentralSeries R L (c - (k + 1))
      have hindex : c - (k + 1) ≤ c - k := Nat.sub_le_sub_left (Nat.le_succ k) c
      have hlcs : lowerCentralSeries R L (c - k) ≤ target :=
        LieModule.antitone_lowerCentralSeries R L L hindex
      have hsubset : previous.carrier ⊆ (target : Set L) := fun x hx ↦
        hlcs (previous.subset_lowerCentral hx)
      let next := previous.independent.extend hsubset
      exact
        { carrier := next
          independent := previous.independent.linearIndepOn_extend hsubset
          subset_lowerCentral := previous.independent.extend_subset hsubset
          span_eq := by
            change Submodule.span R next = target
            rw [show next = previous.independent.extend hsubset by rfl,
              previous.independent.span_extend_eq_span hsubset,
              Submodule.span_eq] }

private theorem adaptedStage_subset_succ
    (c : ℕ) (hclass : lowerCentralSeries R L c = ⊥) (k : ℕ) :
    (adaptedStage c hclass k).carrier ⊆
      (adaptedStage c hclass (k + 1)).carrier := by
  let previous := adaptedStage c hclass k
  let target : Submodule R L := lowerCentralSeries R L (c - (k + 1))
  have hindex : c - (k + 1) ≤ c - k := Nat.sub_le_sub_left (Nat.le_succ k) c
  have hlcs : lowerCentralSeries R L (c - k) ≤ target :=
    LieModule.antitone_lowerCentralSeries R L L hindex
  let hsubset : previous.carrier ⊆ (target : Set L) := fun x hx ↦
    hlcs (previous.subset_lowerCentral hx)
  change previous.carrier ⊆ previous.independent.extend hsubset
  exact previous.independent.subset_extend hsubset

private theorem adaptedStage_mono
    (c : ℕ) (hclass : lowerCentralSeries R L c = ⊥)
    {a b : ℕ} (hab : a ≤ b) :
    (adaptedStage c hclass a).carrier ⊆
      (adaptedStage c hclass b).carrier := by
  induction b, hab using Nat.le_induction with
  | base => exact fun _ hx ↦ hx
  | succ b hab ih =>
      exact ih.trans (adaptedStage_subset_succ c hclass b)

/-- Index set of the final adapted basis. -/
def LowerCentralBasisIndex (c : ℕ)
    (hclass : lowerCentralSeries R L c = ⊥) : Type v :=
  (adaptedStage c hclass c).carrier

/-- The basis obtained after extending through all lower-central terms. -/
def lowerCentralBasis (c : ℕ)
    (hclass : lowerCentralSeries R L c = ⊥) :
    Module.Basis (LowerCentralBasisIndex c hclass) R L := by
  let S := adaptedStage c hclass c
  let v : LowerCentralBasisIndex c hclass → L := fun i ↦ i.1
  have hv : LinearIndependent R v := S.independent.linearIndependent_restrict
  apply Module.Basis.mk hv
  change ⊤ ≤ Submodule.span R (Set.range v)
  have hrange : Set.range v = S.carrier := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact i.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange, S.span_eq, Nat.sub_self]
  simp

@[simp] theorem lowerCentralBasis_apply
    (c : ℕ) (hclass : lowerCentralSeries R L c = ⊥)
    (i : LowerCentralBasisIndex c hclass) :
    lowerCentralBasis c hclass i = i.1 := by
  simp [lowerCentralBasis]

/-- Largest positive lower-central weight of an adapted basis vector, truncated at the declared
nilpotency class. -/
def lowerCentralWeight (c : ℕ)
    (hclass : lowerCentralSeries R L c = ⊥)
    (i : LowerCentralBasisIndex c hclass) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun r ↦ (i.1 : L) ∈ lowerCentralSeries R L (r - 1)) c

theorem lowerCentralWeight_le
    (c : ℕ) (hclass : lowerCentralSeries R L c = ⊥)
    (i : LowerCentralBasisIndex c hclass) :
    lowerCentralWeight c hclass i ≤ c := by
  classical
  simpa [lowerCentralWeight] using
    (Nat.findGreatest_le c : Nat.findGreatest
      (fun r ↦ (i.1 : L) ∈ lowerCentralSeries R L (r - 1)) c ≤ c)

theorem lowerCentralWeight_pos
    (c : ℕ) (hc : 1 ≤ c) (hclass : lowerCentralSeries R L c = ⊥)
    (i : LowerCentralBasisIndex c hclass) :
    0 < lowerCentralWeight c hclass i := by
  classical
  apply lt_of_lt_of_le Nat.zero_lt_one
  simpa [lowerCentralWeight] using
    (Nat.le_findGreatest (P := fun r ↦
      (i.1 : L) ∈ lowerCentralSeries R L (r - 1)) hc (by simp))

theorem lowerCentralBasis_mem_weight
    (c : ℕ) (hc : 1 ≤ c) (hclass : lowerCentralSeries R L c = ⊥)
    (i : LowerCentralBasisIndex c hclass) :
    lowerCentralBasis c hclass i ∈
      lowerCentralSeries R L (lowerCentralWeight c hclass i - 1) := by
  classical
  rw [lowerCentralBasis_apply]
  simpa [lowerCentralWeight] using
    (Nat.findGreatest_spec (P := fun r ↦
      (i.1 : L) ∈ lowerCentralSeries R L (r - 1)) hc (by simp))

private theorem lowerCentralBasis_image_stage
    (c : ℕ) (hclass : lowerCentralSeries R L c = ⊥)
    (k : ℕ) (hkc : k ≤ c) :
    lowerCentralBasis c hclass ''
        {i : LowerCentralBasisIndex c hclass |
          i.1 ∈ (adaptedStage c hclass k).carrier} =
      (adaptedStage c hclass k).carrier := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa using hi
  · intro hx
    have hfinal : x ∈ (adaptedStage c hclass c).carrier :=
      adaptedStage_mono c hclass hkc hx
    let i : LowerCentralBasisIndex c hclass := ⟨x, hfinal⟩
    refine ⟨i, hx, ?_⟩
    simp [i]

/-- Coordinates of a vector in the `r`th conventional lower-central term can occur only on basis
vectors of weight at least `r`. -/
theorem lowerCentralBasis_weight_le_of_repr_ne_zero
    (c : ℕ) (hc : 1 ≤ c) (hclass : lowerCentralSeries R L c = ⊥)
    {r : ℕ} (hr : 1 ≤ r) (hrc : r ≤ c) {x : L}
    (hx : x ∈ lowerCentralSeries R L (r - 1))
    (i : LowerCentralBasisIndex c hclass)
    (hi : (lowerCentralBasis c hclass).repr x i ≠ 0) :
    r ≤ lowerCentralWeight c hclass i := by
  classical
  let k := c - r + 1
  have hkc : k ≤ c := by
    dsimp [k]
    omega
  have hindex : c - k = r - 1 := by
    dsimp [k]
    omega
  have hxspan : x ∈ Submodule.span R (adaptedStage c hclass k).carrier := by
    rw [(adaptedStage c hclass k).span_eq, hindex]
    exact hx
  let s : Set (LowerCentralBasisIndex c hclass) :=
    {j | j.1 ∈ (adaptedStage c hclass k).carrier}
  have hxspan' : x ∈ Submodule.span R (lowerCentralBasis c hclass '' s) := by
    rw [lowerCentralBasis_image_stage c hclass k hkc]
    exact hxspan
  have hsupp :=
    (lowerCentralBasis c hclass).repr_support_subset_of_mem_span s hxspan'
  have his : i ∈ s := hsupp (Finsupp.mem_support_iff.mpr hi)
  have hisLcs := (adaptedStage c hclass k).subset_lowerCentral his
  have hir : (i.1 : L) ∈ lowerCentralSeries R L (r - 1) := by
    simpa [hindex] using hisLcs
  simpa [lowerCentralWeight] using
    (Nat.le_findGreatest (P := fun q ↦
      (i.1 : L) ∈ lowerCentralSeries R L (q - 1)) hrc hir)

/-- The adapted lower-central basis, packaged in the filtered PBW interface. -/
def lowerCentralFilteredBasis
    (c : ℕ) (hc : 1 ≤ c) (hclass : lowerCentralSeries R L c = ⊥) :
    FilteredBasis (R := R) (L := L)
      (ι := LowerCentralBasisIndex c hclass) where
  basis := lowerCentralBasis c hclass
  weight := lowerCentralWeight c hclass
  weight_pos := lowerCentralWeight_pos c hc hclass
  bracket_filtered := by
    intro i j k hk
    let wi := lowerCentralWeight c hclass i
    let wj := lowerCentralWeight c hclass j
    have hwi : 1 ≤ wi := lowerCentralWeight_pos c hc hclass i
    have hwj : 1 ≤ wj := lowerCentralWeight_pos c hc hclass j
    have hiLcs := lowerCentralBasis_mem_weight c hc hclass i
    have hjLcs := lowerCentralBasis_mem_weight c hc hclass j
    have hiDim : lowerCentralBasis c hclass i ∈ dimensionSubring R L wi := by
      have := lowerCentralSeries_le_dimensionSubring R L (wi - 1) hiLcs
      simpa [Nat.sub_add_cancel hwi] using this
    have hjDim : lowerCentralBasis c hclass j ∈ dimensionSubring R L wj := by
      have := lowerCentralSeries_le_dimensionSubring R L (wj - 1) hjLcs
      simpa [Nat.sub_add_cancel hwj] using this
    have hbracket : ⁅lowerCentralBasis c hclass i,
          lowerCentralBasis c hclass j⁆ ∈
        lowerCentralSeries R L (wi + wj - 1) :=
      bracket_dimensionSubring_le_lowerCentralSeries_of_pos R L hwi hwj
        (LieSubmodule.lie_mem_lie hiDim hjDim)
    have hsum : wi + wj ≤ c := by
      by_contra hnot
      have hle : lowerCentralSeries R L (wi + wj - 1) ≤
          lowerCentralSeries R L c := by
        apply LieModule.antitone_lowerCentralSeries R L L
        omega
      have hzero : ⁅lowerCentralBasis c hclass i,
          lowerCentralBasis c hclass j⁆ = 0 := by
        have := hle hbracket
        rw [hclass] at this
        simpa using this
      rw [hzero, map_zero, Finsupp.zero_apply] at hk
      exact hk rfl
    exact lowerCentralBasis_weight_le_of_repr_ne_zero c hc hclass
      (Nat.add_pos_left hwi wj) hsum hbracket k hk
  iota_mem_augmentation_pow := by
    intro i
    have hwi : 1 ≤ lowerCentralWeight c hclass i :=
      lowerCentralWeight_pos c hc hclass i
    have hiLcs := lowerCentralBasis_mem_weight c hc hclass i
    have hiDim := lowerCentralSeries_le_dimensionSubring R L
      (lowerCentralWeight c hclass i - 1) hiLcs
    rw [mem_dimensionSubring] at hiDim
    simpa [Nat.sub_add_cancel hwi] using hiDim

/-- Over a field, PBW with a lower-central adapted basis identifies primitives of augmentation
order `c + 1` with the zero `c`th lower-central term. -/
theorem dimensionSubring_succ_eq_bot_of_lowerCentralSeries_eq_bot_field
    (c : ℕ) (hclass : lowerCentralSeries R L c = ⊥) :
    dimensionSubring R L (c + 1) = ⊥ := by
  by_cases hc : 1 ≤ c
  · let ι := LowerCentralBasisIndex c hclass
    letI : LinearOrder ι := (exists_wellOrder ι).choose
    let B : FilteredBasis (R := R) (L := L) (ι := ι) :=
      lowerCentralFilteredBasis c hc hclass
    apply le_antisymm
    · intro x hx
      rw [mem_dimensionSubring] at hx
      exact B.primitive_eq_zero_of_mem_augmentation_pow c
        (lowerCentralWeight_le c hclass) x hx
    · exact bot_le
  · have hc0 : c = 0 := by omega
    subst c
    have htop : (⊤ : LieIdeal R L) = ⊥ := by simpa using hclass
    apply le_antisymm
    · intro x hx
      have : x ∈ (⊥ : LieIdeal R L) := by rw [← htop]; simp
      simpa using this
    · exact bot_le

end

end LieRings.Plotkin
