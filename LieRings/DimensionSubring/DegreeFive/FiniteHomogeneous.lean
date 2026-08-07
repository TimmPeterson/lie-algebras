import LieRings.DimensionSubring.DegreeFive.LowWeight
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

namespace LieRings.DegreeFive

noncomputable section

universe u

theorem finite_freeMagma_length_lt (X : Type u) [Finite X] (n : ℕ) :
    Set.Finite {w : FreeMagma X | w.length < n} := by
  induction n with
  | zero =>
      apply (Set.finite_empty : Set.Finite (∅ : Set (FreeMagma X))).subset
      intro w hw
      exact (Nat.not_lt_zero _ hw).elim
  | succ n ih =>
      let generators : Set (FreeMagma X) := FreeMagma.of '' Set.univ
      let products : Set (FreeMagma X) :=
        Set.image2 (fun a b : FreeMagma X ↦ a * b)
          {w : FreeMagma X | w.length < n}
          {w : FreeMagma X | w.length < n}
      have hgen : generators.Finite := Set.toFinite _
      have hprod : products.Finite := ih.image2 (fun a b : FreeMagma X ↦ a * b) ih
      apply (hgen.union hprod).subset
      intro w hw
      cases w with
      | of x =>
          left
          exact ⟨x, Set.mem_univ x, rfl⟩
      | mul a b =>
          right
          refine ⟨a, ?_, b, ?_, rfl⟩
          · have hb := FreeMagma.length_pos b
            change a.length + b.length < n + 1 at hw
            change a.length < n
            omega
          · have ha := FreeMagma.length_pos a
            change a.length + b.length < n + 1 at hw
            change b.length < n
            omega

theorem finite_freeMagma_length_eq (X : Type u) [Finite X] (n : ℕ) :
    Set.Finite {w : FreeMagma X | w.length = n} := by
  apply (finite_freeMagma_length_lt X (n + 1)).subset
  intro w hw
  change w.length < n + 1
  change w.length = n at hw
  omega

/-- Non-associative polynomials concentrated in one bracket weight. -/
def magmaExact (X : Type u) (n : ℕ) :
    Submodule ℤ (FreeNonUnitalNonAssocAlgebra ℤ X) :=
  Finsupp.supported ℤ ℤ {w : FreeMagma X | w.length = n}

/-- The homogeneous weight-`n` part of the free Lie ring. -/
def freeLieExact (X : Type u) (n : ℕ) :
    Submodule ℤ (FreeLieAlgebra ℤ X) :=
  (magmaExact X n).map (FreeLieDimension.freeLieMkLinear X)

/-- Projection of a bracketed polynomial to one bracket weight. -/
def magmaLengthComponent (X : Type u) (n : ℕ) :
    FreeNonUnitalNonAssocAlgebra ℤ X →ₗ[ℤ]
      FreeNonUnitalNonAssocAlgebra ℤ X where
  toFun p := Finsupp.filter (fun w : FreeMagma X ↦ w.length = n) p
  map_add' p q := by
    ext w
    by_cases h : w.length = n <;> simp [h]
  map_smul' a p := Finsupp.filter_smul

theorem magmaLengthComponent_mem (X : Type u) (n : ℕ)
    (p : FreeNonUnitalNonAssocAlgebra ℤ X) :
    magmaLengthComponent X n p ∈ magmaExact X n := by
  intro w hw
  have hnz := Finsupp.mem_support_iff.mp hw
  by_contra h
  apply hnz
  exact Finsupp.filter_apply_neg
    (fun w : FreeMagma X ↦ w.length = n) p h

theorem associativeLengthComponent_eq_self_of_mem_exact
    (X : Type u) {n : ℕ} {p : FreeAlgebra ℤ X}
    (hp : p ∈ FreeLieDimension.associativeExact X n) :
    associativeLengthComponent X n p = p := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  ext w
  rw [equiv_associativeLengthComponent]
  by_cases hlen : w.length = n
  · exact Finsupp.filter_apply_pos
      (p := fun w : FreeMonoid X ↦ w.length = n)
      (f := FreeAlgebra.equivMonoidAlgebraFreeMonoid p) (a := w) hlen
  · rw [Finsupp.filter_apply_neg
      (p := fun w : FreeMonoid X ↦ w.length = n)
      (f := FreeAlgebra.equivMonoidAlgebraFreeMonoid p) (a := w) hlen]
    by_contra hnz
    have hw : w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).support :=
      Finsupp.mem_support_iff.mpr (fun h ↦ hnz h.symm)
    exact hlen (hp hw)

theorem associativeLengthComponent_eq_zero_of_mem_exact_of_ne
    (X : Type u) {m n : ℕ} {p : FreeAlgebra ℤ X}
    (hp : p ∈ FreeLieDimension.associativeExact X m) (hmn : m ≠ n) :
    associativeLengthComponent X n p = 0 := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  ext w
  rw [equiv_associativeLengthComponent, map_zero]
  change Finsupp.filter (fun w : FreeMonoid X ↦ w.length = n)
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) w = 0
  by_cases hlen : w.length = n
  · rw [Finsupp.filter_apply_pos
      (p := fun w : FreeMonoid X ↦ w.length = n)
      (f := FreeAlgebra.equivMonoidAlgebraFreeMonoid p) (a := w) hlen]
    by_contra hnz
    have hw : w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).support :=
      Finsupp.mem_support_iff.mpr hnz
    exact hmn ((hp hw).symm.trans hlen)
  · rw [Finsupp.filter_apply_neg
      (p := fun w : FreeMonoid X ↦ w.length = n)
      (f := FreeAlgebra.equivMonoidAlgebraFreeMonoid p) (a := w) hlen]

theorem magmaToFreeAlgebra_magmaLengthComponent
    (X : Type u) (n : ℕ) (p : FreeNonUnitalNonAssocAlgebra ℤ X) :
    FreeLieDimension.magmaToFreeAlgebra X (magmaLengthComponent X n p) =
      associativeLengthComponent X n
        (FreeLieDimension.magmaToFreeAlgebra X p) := by
  induction p using Finsupp.induction with
  | zero =>
      change FreeLieDimension.magmaToFreeAlgebra X
          (magmaLengthComponent X n 0) =
        associativeLengthComponent X n
          (FreeLieDimension.magmaToFreeAlgebra X 0)
      rw [map_zero (magmaLengthComponent X n)]
      exact (map_zero (FreeLieDimension.magmaToFreeAlgebra X)).trans
        (map_zero (associativeLengthComponent X n)).symm
  | single_add w z p hw hz ih =>
      by_cases hlen : w.length = n
      · have hsingle : FreeLieDimension.magmaToFreeAlgebra X
              (magmaLengthComponent X n (Finsupp.single w z)) =
            associativeLengthComponent X n
              (FreeLieDimension.magmaToFreeAlgebra X
                (Finsupp.single w z)) := by
          have hfilter : magmaLengthComponent X n (Finsupp.single w z) =
            (Finsupp.single w z : FreeNonUnitalNonAssocAlgebra ℤ X) := by
            ext v
            simp [magmaLengthComponent, Finsupp.filter_apply, hlen]
          rw [hfilter]
          symm
          apply associativeLengthComponent_eq_self_of_mem_exact X
          have hsingle' : (Finsupp.single w z :
              FreeNonUnitalNonAssocAlgebra ℤ X) =
              z • Finsupp.single w 1 := by ext; simp
          rw [hsingle']
          have hmap : FreeLieDimension.magmaToFreeAlgebra X
                (z • (Finsupp.single w 1 : FreeNonUnitalNonAssocAlgebra ℤ X)) =
              z • FreeLieDimension.magmaToFreeAlgebra X
                (Finsupp.single w 1) :=
            (FreeLieDimension.magmaToFreeAlgebra X).map_smul z _
          rw [hmap]
          exact (FreeLieDimension.associativeExact X n).smul_mem z
            (hlen ▸ FreeLieDimension.magmaToFreeAlgebra_single_mem_exact X w)
        calc
          FreeLieDimension.magmaToFreeAlgebra X
              (magmaLengthComponent X n (Finsupp.single w z + p)) =
              FreeLieDimension.magmaToFreeAlgebra X
                  (magmaLengthComponent X n (Finsupp.single w z)) +
                FreeLieDimension.magmaToFreeAlgebra X
                  (magmaLengthComponent X n p) := by
            calc
              _ = FreeLieDimension.magmaToFreeAlgebra X
                    (magmaLengthComponent X n (Finsupp.single w z) +
                      magmaLengthComponent X n p) :=
                congrArg (FreeLieDimension.magmaToFreeAlgebra X)
                  ((magmaLengthComponent X n).map_add _ _)
              _ = _ := (FreeLieDimension.magmaToFreeAlgebra X).map_add _ _
          _ = associativeLengthComponent X n
                (FreeLieDimension.magmaToFreeAlgebra X (Finsupp.single w z)) +
              associativeLengthComponent X n
                (FreeLieDimension.magmaToFreeAlgebra X p) :=
            congrArg₂ (fun a b ↦ a + b) hsingle ih
          _ = associativeLengthComponent X n
              (FreeLieDimension.magmaToFreeAlgebra X (Finsupp.single w z + p)) := by
            calc
              _ = associativeLengthComponent X n
                    (FreeLieDimension.magmaToFreeAlgebra X (Finsupp.single w z) +
                      FreeLieDimension.magmaToFreeAlgebra X p) :=
                ((associativeLengthComponent X n).map_add _ _).symm
              _ = _ := congrArg (associativeLengthComponent X n)
                ((FreeLieDimension.magmaToFreeAlgebra X).map_add _ _).symm

      · have hsingle : FreeLieDimension.magmaToFreeAlgebra X
              (magmaLengthComponent X n (Finsupp.single w z)) =
            associativeLengthComponent X n
              (FreeLieDimension.magmaToFreeAlgebra X
                (Finsupp.single w z)) := by
          have hfilter : magmaLengthComponent X n (Finsupp.single w z) = 0 := by
            apply Finsupp.ext
            intro v
            change (Finsupp.filter (fun w : FreeMagma X ↦ w.length = n)
              (Finsupp.single w z)) v = (0 : ℤ)
            by_cases hv : v = w
            · subst v
              rw [Finsupp.filter_apply_neg
                (p := fun w : FreeMagma X ↦ w.length = n)
                (f := Finsupp.single w z) (a := w) hlen]
            · by_cases hvlen : v.length = n
              · rw [Finsupp.filter_apply_pos
                  (p := fun w : FreeMagma X ↦ w.length = n)
                  (f := Finsupp.single w z) (a := v) hvlen]
                simp [hv]
              · rw [Finsupp.filter_apply_neg
                  (p := fun w : FreeMagma X ↦ w.length = n)
                  (f := Finsupp.single w z) (a := v) hvlen]
          rw [hfilter, map_zero]
          have hsingle' : (Finsupp.single w z :
              FreeNonUnitalNonAssocAlgebra ℤ X) =
              z • Finsupp.single w 1 := by ext; simp
          have hexact : FreeLieDimension.magmaToFreeAlgebra X
                (Finsupp.single w z : FreeNonUnitalNonAssocAlgebra ℤ X) ∈
              FreeLieDimension.associativeExact X w.length := by
            rw [hsingle']
            have hmap : FreeLieDimension.magmaToFreeAlgebra X
                  (z • (Finsupp.single w 1 : FreeNonUnitalNonAssocAlgebra ℤ X)) =
                z • FreeLieDimension.magmaToFreeAlgebra X
                  (Finsupp.single w 1) :=
              (FreeLieDimension.magmaToFreeAlgebra X).map_smul z _
            rw [hmap]
            exact (FreeLieDimension.associativeExact X w.length).smul_mem z
              (FreeLieDimension.magmaToFreeAlgebra_single_mem_exact X w)
          exact (associativeLengthComponent_eq_zero_of_mem_exact_of_ne X
            hexact hlen).symm
        calc
          FreeLieDimension.magmaToFreeAlgebra X
              (magmaLengthComponent X n (Finsupp.single w z + p)) =
              FreeLieDimension.magmaToFreeAlgebra X
                  (magmaLengthComponent X n (Finsupp.single w z)) +
                FreeLieDimension.magmaToFreeAlgebra X
                  (magmaLengthComponent X n p) := by
            calc
              _ = FreeLieDimension.magmaToFreeAlgebra X
                    (magmaLengthComponent X n (Finsupp.single w z) +
                      magmaLengthComponent X n p) :=
                congrArg (FreeLieDimension.magmaToFreeAlgebra X)
                  ((magmaLengthComponent X n).map_add _ _)
              _ = _ := (FreeLieDimension.magmaToFreeAlgebra X).map_add _ _
          _ = associativeLengthComponent X n
                (FreeLieDimension.magmaToFreeAlgebra X (Finsupp.single w z)) +
              associativeLengthComponent X n
                (FreeLieDimension.magmaToFreeAlgebra X p) :=
            congrArg₂ (fun a b ↦ a + b) hsingle ih
          _ = associativeLengthComponent X n
              (FreeLieDimension.magmaToFreeAlgebra X (Finsupp.single w z + p)) := by
            calc
              _ = associativeLengthComponent X n
                    (FreeLieDimension.magmaToFreeAlgebra X (Finsupp.single w z) +
                      FreeLieDimension.magmaToFreeAlgebra X p) :=
                ((associativeLengthComponent X n).map_add _ _).symm
              _ = _ := congrArg (associativeLengthComponent X n)
                ((FreeLieDimension.magmaToFreeAlgebra X).map_add _ _).symm

theorem freeLieMkLinear_surjective (X : Type u) :
    Function.Surjective (FreeLieDimension.freeLieMkLinear X) := by
  intro x
  obtain ⟨p, rfl⟩ := Quot.mk_surjective x
  exact ⟨p, rfl⟩

/-- A fixed bracketed-polynomial representative of a free-Lie element. -/
def freeLieRepresentative (X : Type u) :
    FreeLieAlgebra ℤ X → FreeNonUnitalNonAssocAlgebra ℤ X :=
  Function.surjInv (freeLieMkLinear_surjective X)

@[simp]
theorem freeLieMkLinear_freeLieRepresentative (X : Type u)
    (x : FreeLieAlgebra ℤ X) :
    FreeLieDimension.freeLieMkLinear X (freeLieRepresentative X x) = x :=
  Function.rightInverse_surjInv (freeLieMkLinear_surjective X) x

/-- The underlying homogeneous projection before it is bundled as a linear map. -/
def freeLieLengthComponentFn (X : Type u) (n : ℕ)
    (x : FreeLieAlgebra ℤ X) : FreeLieAlgebra ℤ X :=
  FreeLieDimension.freeLieMkLinear X
    (magmaLengthComponent X n (freeLieRepresentative X x))

theorem freeLieToFreeAlgebra_freeLieLengthComponentFn
    (X : Type u) (n : ℕ) (x : FreeLieAlgebra ℤ X) :
    PBW.freeLieToFreeAlgebra ℤ X (freeLieLengthComponentFn X n x) =
      associativeLengthComponent X n
        (PBW.freeLieToFreeAlgebra ℤ X x) := by
  rw [freeLieLengthComponentFn, FreeLieDimension.freeLieToFreeAlgebra_mk,
    magmaToFreeAlgebra_magmaLengthComponent]
  congr 1
  rw [← FreeLieDimension.freeLieToFreeAlgebra_mk]
  exact congrArg (PBW.freeLieToFreeAlgebra ℤ X)
    (freeLieMkLinear_freeLieRepresentative X x)

/-- Homogeneous projection on the free Lie ring.  Its well-defined linearity is proved through
the integral Magnus embedding. -/
def freeLieLengthComponent (X : Type u) (n : ℕ) :
    FreeLieAlgebra ℤ X →ₗ[ℤ] FreeLieAlgebra ℤ X where
  toFun := freeLieLengthComponentFn X n
  map_add' x y := by
    apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
    calc
      PBW.freeLieToFreeAlgebra ℤ X (freeLieLengthComponentFn X n (x + y)) =
          associativeLengthComponent X n
            (PBW.freeLieToFreeAlgebra ℤ X (x + y)) :=
        freeLieToFreeAlgebra_freeLieLengthComponentFn X n (x + y)
      _ = associativeLengthComponent X n
            (PBW.freeLieToFreeAlgebra ℤ X x +
              PBW.freeLieToFreeAlgebra ℤ X y) :=
        congrArg (associativeLengthComponent X n)
          (map_add (PBW.freeLieToFreeAlgebra ℤ X) x y)
      _ = associativeLengthComponent X n
              (PBW.freeLieToFreeAlgebra ℤ X x) +
            associativeLengthComponent X n
              (PBW.freeLieToFreeAlgebra ℤ X y) :=
        (associativeLengthComponent X n).map_add _ _
      _ = PBW.freeLieToFreeAlgebra ℤ X (freeLieLengthComponentFn X n x) +
            PBW.freeLieToFreeAlgebra ℤ X (freeLieLengthComponentFn X n y) :=
        congrArg₂ (fun a b ↦ a + b)
          (freeLieToFreeAlgebra_freeLieLengthComponentFn X n x).symm
          (freeLieToFreeAlgebra_freeLieLengthComponentFn X n y).symm
      _ = PBW.freeLieToFreeAlgebra ℤ X
            (freeLieLengthComponentFn X n x + freeLieLengthComponentFn X n y) :=
        (map_add (PBW.freeLieToFreeAlgebra ℤ X) _ _).symm
  map_smul' z x := by
    apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
    calc
      PBW.freeLieToFreeAlgebra ℤ X (freeLieLengthComponentFn X n (z • x)) =
          associativeLengthComponent X n
            (PBW.freeLieToFreeAlgebra ℤ X (z • x)) :=
        freeLieToFreeAlgebra_freeLieLengthComponentFn X n (z • x)
      _ = associativeLengthComponent X n
            (z • PBW.freeLieToFreeAlgebra ℤ X x) :=
        congrArg (associativeLengthComponent X n)
          (map_smul (PBW.freeLieToFreeAlgebra ℤ X) z x)
      _ = z • associativeLengthComponent X n
            (PBW.freeLieToFreeAlgebra ℤ X x) :=
        (associativeLengthComponent X n).map_smul z _
      _ = z • PBW.freeLieToFreeAlgebra ℤ X
            (freeLieLengthComponentFn X n x) :=
        congrArg (z • ·)
          (freeLieToFreeAlgebra_freeLieLengthComponentFn X n x).symm
      _ = PBW.freeLieToFreeAlgebra ℤ X (z • freeLieLengthComponentFn X n x) :=
        (map_smul (PBW.freeLieToFreeAlgebra ℤ X) z _).symm

theorem freeLieToFreeAlgebra_freeLieLengthComponent
    (X : Type u) (n : ℕ) (x : FreeLieAlgebra ℤ X) :
    PBW.freeLieToFreeAlgebra ℤ X (freeLieLengthComponent X n x) =
      associativeLengthComponent X n
        (PBW.freeLieToFreeAlgebra ℤ X x) :=
  freeLieToFreeAlgebra_freeLieLengthComponentFn X n x

theorem freeLieLengthComponent_mem_exact
    (X : Type u) (n : ℕ) (x : FreeLieAlgebra ℤ X) :
    freeLieLengthComponent X n x ∈ freeLieExact X n := by
  exact ⟨magmaLengthComponent X n (freeLieRepresentative X x),
    magmaLengthComponent_mem X n _, rfl⟩

/-- If the first permitted homogeneous component vanishes, minimum associative length rises by
one. -/
theorem mem_associativeHigh_succ_of_component_eq_zero
    (X : Type u) {n : ℕ} {p : FreeAlgebra ℤ X}
    (hp : p ∈ FreeLieDimension.associativeHigh X n)
    (hcomponent : associativeLengthComponent X n p = 0) :
    p ∈ FreeLieDimension.associativeHigh X (n + 1) := by
  intro w hw
  have hnle : n ≤ w.length := hp hw
  by_contra hsucc
  change ¬n + 1 ≤ w.length at hsucc
  have hlength : w.length = n := by omega
  have hcoeff : (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) w ≠ 0 :=
    Finsupp.mem_support_iff.mp hw
  have hz := congrArg (fun q : FreeAlgebra ℤ X ↦
    FreeAlgebra.equivMonoidAlgebraFreeMonoid q w) hcomponent
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (associativeLengthComponent X n p)) w =
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (0 : FreeAlgebra ℤ X)) w at hz
  rw [equiv_associativeLengthComponent,
    Finsupp.filter_apply_pos
      (p := fun v : FreeMonoid X ↦ v.length = n)
      (f := FreeAlgebra.equivMonoidAlgebraFreeMonoid p)
      (a := w) hlength, map_zero] at hz
  exact hcoeff hz

/-- The corresponding filtration step in the free Lie ring. -/
theorem mem_lieHigh_succ_of_component_eq_zero
    (X : Type u) {n : ℕ} {x : FreeLieAlgebra ℤ X}
    (hx : x ∈ FreeLieDimension.lieHigh X n)
    (hcomponent : freeLieLengthComponent X n x = 0) :
    x ∈ FreeLieDimension.lieHigh X (n + 1) := by
  have hxAssoc : PBW.freeLieToFreeAlgebra ℤ X x ∈
      FreeLieDimension.associativeHigh X n := by
    rcases hx with ⟨p, hp, rfl⟩
    rw [FreeLieDimension.freeLieToFreeAlgebra_mk]
    exact FreeLieDimension.magmaToFreeAlgebra_mem_high X hp
  have hcomponentAssoc : associativeLengthComponent X n
      (PBW.freeLieToFreeAlgebra ℤ X x) = 0 := by
    rw [← freeLieToFreeAlgebra_freeLieLengthComponent X n x,
      hcomponent, map_zero]
  have hxAssoc' := mem_associativeHigh_succ_of_component_eq_zero X
    hxAssoc hcomponentAssoc
  have hrep : FreeLieDimension.magmaToFreeAlgebra X
      (freeLieRepresentative X x) = PBW.freeLieToFreeAlgebra ℤ X x := by
    rw [← FreeLieDimension.freeLieToFreeAlgebra_mk]
    exact congrArg (PBW.freeLieToFreeAlgebra ℤ X)
      (freeLieMkLinear_freeLieRepresentative X x)
  have hrepHigh : FreeLieDimension.magmaToFreeAlgebra X
      (freeLieRepresentative X x) ∈
        FreeLieDimension.associativeHigh X (n + 1) := by
    rw [hrep]
    exact hxAssoc'
  have hmk := FreeLieDimension.freeLieMkLinear_mem_lieHigh_of_magmaToFreeAlgebra_mem
    X hrepHigh
  simpa using hmk

theorem magmaExact_fg (X : Type u) [Finite X] (n : ℕ) :
    (magmaExact X n).FG := by
  rw [magmaExact, Finsupp.supported_eq_span_single]
  apply Submodule.fg_span
  exact (finite_freeMagma_length_eq X n).image _

instance freeLieExact_moduleFinite (X : Type u) [Finite X] (n : ℕ) :
    Module.Finite ℤ (freeLieExact X n) := by
  rw [Module.Finite.iff_fg]
  exact Submodule.FG.map (FreeLieDimension.freeLieMkLinear X)
    (magmaExact_fg X n)

instance freeLieExact_isTorsionFree (X : Type u) (n : ℕ) :
    Module.IsTorsionFree ℤ (freeLieExact X n) where
  isSMulRegular {z} hz x y hxy := by
    apply Subtype.ext
    apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
    apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
    ext w
    apply hz.isSMulRegular
    have hxy' : z • (x : FreeLieAlgebra ℤ X) =
        z • (y : FreeLieAlgebra ℤ X) := congrArg Subtype.val hxy
    have h := congrArg (fun q : FreeLieAlgebra ℤ X ↦
      FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (PBW.freeLieToFreeAlgebra ℤ X q) w) hxy'
    simpa only [map_smul, Finsupp.smul_apply] using h

/-- A finite integral basis of one homogeneous free-Lie component. -/
def freeLieExactBasisData (X : Type u) [Finite X] (n : ℕ) :
    Σ k : ℕ, Module.Basis (Fin k) ℤ (freeLieExact X n) :=
  Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := freeLieExact X n)

/-- The finite index type of the chosen homogeneous basis. -/
abbrev FreeLieExactBasisIndex (X : Type u) [Finite X] (n : ℕ) :=
  Fin (freeLieExactBasisData X n).1

/-- A finite integral basis of one homogeneous free-Lie component. -/
def freeLieExactBasis (X : Type u) [Finite X] (n : ℕ) :
    Module.Basis (FreeLieExactBasisIndex X n) ℤ (freeLieExact X n) :=
  (freeLieExactBasisData X n).2

end

end LieRings.DegreeFive
