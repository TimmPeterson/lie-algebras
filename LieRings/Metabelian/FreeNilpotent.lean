import LieRings.Metabelian.HallBasis
import LieRings.Metabelian.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Truncated relatively free metabelian Lie rings

The coordinate of index `0` has manuscript weight one.  Coordinate `q+1`
is the Hall component of weight `q+2`.  Thus the cutoff is represented by the
literal finite dependent product requested in the manuscript proof.
-/

namespace FreeMetabelian

universe u v

noncomputable section

variable (X : Type u) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

/-- The homogeneous piece whose zero-based coordinate is `n`. -/
def Piece : ℕ → Type u
  | 0 => X
  | q + 1 => Component X q

instance (n : ℕ) : AddCommGroup (Piece X n) := by
  cases n with
  | zero => exact inferInstanceAs (AddCommGroup X)
  | succ q => exact inferInstanceAs (AddCommGroup (Component X q))

/-- The class-`c` truncation, as a finite dependent product of weights
`1,...,c`.  The definition also makes sense for `c=0`, although the universal
property is only used for positive cutoffs. -/
abbrev Free (c : ℕ) := (i : Fin c) → Piece X i.val

namespace Free

variable {X : Type u} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable {c : ℕ}

/-- Projection to the degree-one generator coordinate. -/
def degreeOne (x : Free X c) (h : 0 < c) : X := x ⟨0, h⟩

/-- Projection to the derived component of manuscript weight `q+2`. -/
def derived (x : Free X c) (q : ℕ) (h : q + 1 < c) : Component X q :=
  x ⟨q + 1, h⟩

private def bracketAt (x y : Free X c) (i : Fin c) : Piece X i.val := by
  rcases i with ⟨(_ | _ | q), hi⟩
  · exact 0
  · exact generatorBracket X (degreeOne x (by omega))
      (degreeOne y (by omega))
  · exact Action.apply X q (degreeOne y (by omega))
        (derived x q (by omega)) -
      Action.apply X q (degreeOne x (by omega)) (derived y q (by omega))

/-- The truncated homogeneous bracket. -/
def bracket (x y : Free X c) : Free X c := fun i ↦ bracketAt x y i

@[simp]
theorem bracket_apply_zero (x y : Free X c) (h : 0 < c) :
    bracket x y ⟨0, h⟩ = 0 := rfl

@[simp]
theorem bracket_apply_one (x y : Free X c) (h : 1 < c) :
    bracket x y ⟨1, h⟩ =
      generatorBracket X (degreeOne x (by omega))
        (degreeOne y (by omega)) := rfl

@[simp]
theorem bracket_apply_succ_succ (x y : Free X c) (q : ℕ)
    (h : q + 2 < c) :
    bracket x y ⟨q + 2, h⟩ =
      Action.apply X q (degreeOne y (by omega)) (derived x q (by omega)) -
        Action.apply X q (degreeOne x (by omega))
          (derived y q (by omega)) := rfl

@[simp]
theorem degreeOne_bracket (x y : Free X c) (h : 0 < c) :
    degreeOne (bracket x y) h = 0 := rfl

@[simp]
theorem derived_bracket_zero (x y : Free X c) (h : 1 < c) :
    derived (bracket x y) 0 h =
      generatorBracket X (degreeOne x (by omega))
        (degreeOne y (by omega)) := rfl

@[simp]
theorem derived_bracket_succ (x y : Free X c) (q : ℕ)
    (h : q + 2 < c) :
    derived (bracket x y) (q + 1) h =
      Action.apply X q (degreeOne y (by omega)) (derived x q (by omega)) -
        Action.apply X q (degreeOne x (by omega))
          (derived y q (by omega)) := rfl

private theorem bracket_add_left (x y z : Free X c) :
    bracket (x + y) z = bracket x z + bracket y z := by
  funext i
  rcases i with ⟨(_ | _ | q), hi⟩
  · simp only [bracket_apply_zero, Pi.add_apply, add_zero]
  · norm_num at hi ⊢
    change generatorBracket X
        ((x + y) ⟨0, by omega⟩) (z ⟨0, by omega⟩) =
      generatorBracket X (x ⟨0, by omega⟩) (z ⟨0, by omega⟩) +
        generatorBracket X (y ⟨0, by omega⟩) (z ⟨0, by omega⟩)
    simp only [Pi.add_apply]
    exact LinearMap.congr_fun ((generatorBracket X).map_add
      (x ⟨0, by omega⟩) (y ⟨0, by omega⟩)) (z ⟨0, by omega⟩)
  ·
    let x0 := x ⟨0, by omega⟩
    let y0 := y ⟨0, by omega⟩
    let z0 := z ⟨0, by omega⟩
    let xq := x ⟨q + 1, by omega⟩
    let yq := y ⟨q + 1, by omega⟩
    let zq := z ⟨q + 1, by omega⟩
    change Action.apply X q (z ⟨0, by omega⟩)
          ((x + y) ⟨q + 1, by omega⟩) -
        Action.apply X q ((x + y) ⟨0, by omega⟩)
          (z ⟨q + 1, by omega⟩) =
      (Action.apply X q (z ⟨0, by omega⟩) (x ⟨q + 1, by omega⟩) -
          Action.apply X q (x ⟨0, by omega⟩) (z ⟨q + 1, by omega⟩)) +
        (Action.apply X q (z ⟨0, by omega⟩) (y ⟨q + 1, by omega⟩) -
          Action.apply X q (y ⟨0, by omega⟩) (z ⟨q + 1, by omega⟩))
    change Action.apply X q z0 (xq + yq) -
        Action.apply X q (x0 + y0) zq =
      (Action.apply X q z0 xq - Action.apply X q x0 zq) +
        (Action.apply X q z0 yq - Action.apply X q y0 zq)
    have hleft := (Action.apply X q z0).map_add xq yq
    have hright := LinearMap.congr_fun (Action.apply_add X q x0 y0) zq
    calc
      Action.apply X q z0 (xq + yq) - Action.apply X q (x0 + y0) zq =
          (Action.apply X q z0 xq + Action.apply X q z0 yq) -
            (Action.apply X q x0 zq + Action.apply X q y0 zq) :=
        congrArg₂ (fun a b ↦ a - b) hleft hright
      _ = (Action.apply X q z0 xq - Action.apply X q x0 zq) +
          (Action.apply X q z0 yq - Action.apply X q y0 zq) := by abel

private theorem bracket_add_right (x y z : Free X c) :
    bracket x (y + z) = bracket x y + bracket x z := by
  funext i
  rcases i with ⟨(_ | _ | q), hi⟩
  · simp only [bracket_apply_zero, Pi.add_apply, add_zero]
  · norm_num at hi ⊢
    change generatorBracket X (x ⟨0, by omega⟩)
        ((y + z) ⟨0, by omega⟩) =
      generatorBracket X (x ⟨0, by omega⟩) (y ⟨0, by omega⟩) +
        generatorBracket X (x ⟨0, by omega⟩) (z ⟨0, by omega⟩)
    simp only [Pi.add_apply]
    exact (generatorBracket X (x ⟨0, by omega⟩)).map_add
      (y ⟨0, by omega⟩) (z ⟨0, by omega⟩)
  ·
    let x0 := x ⟨0, by omega⟩
    let y0 := y ⟨0, by omega⟩
    let z0 := z ⟨0, by omega⟩
    let xq := x ⟨q + 1, by omega⟩
    let yq := y ⟨q + 1, by omega⟩
    let zq := z ⟨q + 1, by omega⟩
    change Action.apply X q ((y + z) ⟨0, by omega⟩)
          (x ⟨q + 1, by omega⟩) -
        Action.apply X q (x ⟨0, by omega⟩)
          ((y + z) ⟨q + 1, by omega⟩) =
      (Action.apply X q (y ⟨0, by omega⟩) (x ⟨q + 1, by omega⟩) -
          Action.apply X q (x ⟨0, by omega⟩) (y ⟨q + 1, by omega⟩)) +
        (Action.apply X q (z ⟨0, by omega⟩) (x ⟨q + 1, by omega⟩) -
          Action.apply X q (x ⟨0, by omega⟩) (z ⟨q + 1, by omega⟩))
    change Action.apply X q (y0 + z0) xq -
        Action.apply X q x0 (yq + zq) =
      (Action.apply X q y0 xq - Action.apply X q x0 yq) +
        (Action.apply X q z0 xq - Action.apply X q x0 zq)
    have hleft := LinearMap.congr_fun (Action.apply_add X q y0 z0) xq
    have hright := (Action.apply X q x0).map_add yq zq
    calc
      Action.apply X q (y0 + z0) xq - Action.apply X q x0 (yq + zq) =
          (Action.apply X q y0 xq + Action.apply X q z0 xq) -
            (Action.apply X q x0 yq + Action.apply X q x0 zq) :=
        congrArg₂ (fun a b ↦ a - b) hleft hright
      _ = (Action.apply X q y0 xq - Action.apply X q x0 yq) +
          (Action.apply X q z0 xq - Action.apply X q x0 zq) := by abel

private theorem bracket_self (x : Free X c) : bracket x x = 0 := by
  funext i
  rcases i with ⟨(_ | _ | q), hi⟩
  · exact bracket_apply_zero x x hi
  · simpa only [bracket_apply_one] using
      generatorBracket_self X (x ⟨0, by omega⟩)
  · simp only [bracket_apply_succ_succ, sub_self, Pi.zero_apply]
    rfl

private theorem bracket_leibniz (x y z : Free X c) :
    bracket x (bracket y z) =
      bracket (bracket x y) z + bracket y (bracket x z) := by
  funext i
  rcases i with ⟨(_ | _ | _ | q), hi⟩
  · simp only [bracket_apply_zero, Pi.add_apply, add_zero]
  · norm_num at hi ⊢
    simp only [Nat.zero_add, bracket_apply_zero, bracket_apply_one,
      Pi.add_apply] at ⊢
    change generatorBracket X (x ⟨0, by omega⟩) 0 =
      generatorBracket X 0 (z ⟨0, by omega⟩) +
        generatorBracket X (y ⟨0, by omega⟩) 0
    simp only [map_zero, LinearMap.zero_apply, zero_add]
  · norm_num at hi ⊢
    simp only [degreeOne_bracket, derived_bracket_zero,
      Action.apply_zero_apply, sub_zero, zero_sub, zero_add] at ⊢
    change -Action.apply X 0 (x ⟨0, by omega⟩)
        (generatorBracket X (y ⟨0, by omega⟩) (z ⟨0, by omega⟩)) =
      Action.apply X 0 (z ⟨0, by omega⟩)
          (generatorBracket X (x ⟨0, by omega⟩) (y ⟨0, by omega⟩)) -
        Action.apply X 0 (y ⟨0, by omega⟩)
          (generatorBracket X (x ⟨0, by omega⟩) (z ⟨0, by omega⟩))
    have hJ := Action.apply_generator_jacobi X
      (x ⟨0, by omega⟩) (y ⟨0, by omega⟩) (z ⟨0, by omega⟩)
    let A := Action.apply X 0 (x ⟨0, by omega⟩)
      (generatorBracket X (y ⟨0, by omega⟩) (z ⟨0, by omega⟩))
    let B := Action.apply X 0 (y ⟨0, by omega⟩)
      (generatorBracket X (x ⟨0, by omega⟩) (z ⟨0, by omega⟩))
    let C := Action.apply X 0 (z ⟨0, by omega⟩)
      (generatorBracket X (x ⟨0, by omega⟩) (y ⟨0, by omega⟩))
    change A - B + C = 0 at hJ
    change -A = C - B
    have hAB : A - B = -C := eq_neg_of_add_eq_zero_left hJ
    calc
      -A = -(A - B) - B := by abel
      _ = -(-C) - B := by rw [hAB]
      _ = C - B := by rw [neg_neg]
  · simp only [bracket_apply_succ_succ, Pi.add_apply, degreeOne_bracket,
      derived_bracket_succ, Action.apply_zero_apply, sub_zero, zero_sub,
      zero_add] at ⊢
    change -Action.apply X (q + 1) (degreeOne x (by omega))
          (Action.apply X q (degreeOne z (by omega))
              (derived y q (by omega)) -
            Action.apply X q (degreeOne y (by omega))
              (derived z q (by omega))) =
      Action.apply X (q + 1) (degreeOne z (by omega))
          (Action.apply X q (degreeOne y (by omega))
              (derived x q (by omega)) -
            Action.apply X q (degreeOne x (by omega))
              (derived y q (by omega))) +
        -Action.apply X (q + 1) (degreeOne y (by omega))
          (Action.apply X q (degreeOne z (by omega))
              (derived x q (by omega)) -
            Action.apply X q (degreeOne x (by omega))
              (derived z q (by omega)))
    simp only [map_sub]
    have hxy := LinearMap.congr_fun
      (Action.apply_comm X q
        (degreeOne y (by omega)) (degreeOne z (by omega)))
      (derived x q (by omega))
    have hyz := LinearMap.congr_fun
      (Action.apply_comm X q
        (degreeOne x (by omega)) (degreeOne z (by omega)))
      (derived y q (by omega))
    have hzx := LinearMap.congr_fun
      (Action.apply_comm X q
        (degreeOne x (by omega)) (degreeOne y (by omega)))
      (derived z q (by omega))
    simp only [LinearMap.comp_apply] at hxy hyz hzx
    rw [hxy, hyz, hzx]
    abel

instance : LieRing (Free X c) where
  toAddCommGroup := Pi.addCommGroup
  bracket := bracket
  add_lie := bracket_add_left
  lie_add := bracket_add_right
  lie_self := bracket_self
  leibniz_lie := bracket_leibniz

/-! ## Homogeneous coordinates and the Hall basis -/

/-- Inclusion of one homogeneous coordinate. -/
def incl (i : Fin c) : Piece X i.val →ₗ[ℤ] Free X c :=
  (LinearMap.single ℤ (fun j : Fin c ↦ Piece X j.val) i).toAddMonoidHom.toIntLinearMap

/-- Typed inclusion of manuscript component `q+2`; this wrapper keeps the
reduction `Piece X (q+1) = Component X q` out of downstream proofs. -/
def inclComponent (q : ℕ) (h : q + 1 < c) :
    Component X q →ₗ[ℤ] Free X c := by
  let e : Component X q ≃+ Piece X (q + 1) :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  exact (incl (X := X) (⟨q + 1, h⟩ : Fin c)).comp
    e.toIntLinearEquiv.toLinearMap

/-- Projection onto one homogeneous coordinate. -/
def project (i : Fin c) : Free X c →ₗ[ℤ] Piece X i.val :=
  ({ toFun := fun x ↦ x i
     map_zero' := rfl
     map_add' := fun _ _ ↦ rfl } : Free X c →+ Piece X i.val).toIntLinearMap

@[simp]
theorem project_apply (i : Fin c) (x : Free X c) : project i x = x i := rfl

@[simp]
theorem incl_apply_same (i : Fin c) (x : Piece X i.val) : incl i x i = x := by
  simp [incl]

@[simp]
theorem incl_apply_of_ne (i j : Fin c) (h : j ≠ i) (x : Piece X i.val) :
    incl i x j = 0 := by
  simp [incl, h]

/-- Every element is the finite sum of its homogeneous coordinates. -/
theorem sum_incl_project (x : Free X c) :
    ∑ i : Fin c, incl i (project i x) = x := by
  funext j
  simp [incl]

/-! ## Literal prefix maps

The canonical tower uses the grading itself, not an abstract filtration
splitting.  The next two maps are therefore the actual restriction to, and
zero-extension from, the first `k` coordinates of the dependent product.
-/

/-- Restriction to the first `k` homogeneous coordinates. -/
def projectPrefix (k : ℕ) (hk : k ≤ c) : Free X c →ₗ[ℤ] Free X k where
  toFun x i := x ⟨i, i.isLt.trans_le hk⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extension of a prefix by zero in all later homogeneous coordinates. -/
def prefixIncl (k : ℕ) (hk : k ≤ c) : Free X k →ₗ[ℤ] Free X c where
  toFun x i := if hi : i.val < k then x ⟨i.val, hi⟩ else 0
  map_add' x y := by
    funext i
    by_cases hi : i.val < k <;> simp [hi]
  map_smul' z x := by
    funext i
    by_cases hi : i.val < k <;> simp [hi]

@[simp]
theorem projectPrefix_apply (k : ℕ) (hk : k ≤ c) (x : Free X c) (i : Fin k) :
    projectPrefix k hk x i = x ⟨i, i.isLt.trans_le hk⟩ := rfl

@[simp]
theorem prefixIncl_apply_of_lt (k : ℕ) (hk : k ≤ c) (x : Free X k)
    (i : Fin c) (hi : i.val < k) :
    prefixIncl k hk x i = x ⟨i.val, hi⟩ := by
  simp [prefixIncl, hi]

@[simp]
theorem prefixIncl_apply_of_le (k : ℕ) (hk : k ≤ c) (x : Free X k)
    (i : Fin c) (hi : k ≤ i.val) :
    prefixIncl k hk x i = 0 := by
  simp [prefixIncl, Nat.not_lt.mpr hi]

@[simp]
theorem projectPrefix_prefixIncl (k : ℕ) (hk : k ≤ c) :
    (projectPrefix (X := X) k hk).comp (prefixIncl (X := X) k hk) =
      (LinearMap.id : Free X k →ₗ[ℤ] Free X k) := by
  ext x i
  simp

theorem projectPrefix_surjective (k : ℕ) (hk : k ≤ c) :
    Function.Surjective (projectPrefix (X := X) k hk) := by
  intro x
  exact ⟨prefixIncl k hk x,
    LinearMap.congr_fun (projectPrefix_prefixIncl (X := X) k hk) x⟩

/-- Restriction from a longer prefix to a shorter prefix. -/
def prefixMap (j k : ℕ) (hjk : j ≤ k) : Free X k →ₗ[ℤ] Free X j :=
  projectPrefix j hjk

@[simp]
theorem projectPrefix_trans (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    (projectPrefix (X := X) i hij).comp (projectPrefix (X := X) j hjk) =
      projectPrefix (X := X) i (hij.trans hjk) := by
  ext x t
  rfl

/-- Inclusion of the coordinate of manuscript weight `s`, with a natural
number index convenient for the tower. -/
def weightIncl (s : ℕ) (hs : s < c) : Piece X s →ₗ[ℤ] Free X c :=
  incl ⟨s, hs⟩

/-- Projection to the coordinate of manuscript weight `s`. -/
def weightProject (s : ℕ) (hs : s < c) : Free X c →ₗ[ℤ] Piece X s :=
  project ⟨s, hs⟩

@[simp]
theorem weightProject_weightIncl (s : ℕ) (hs : s < c) (x : Piece X s) :
    weightProject s hs (weightIncl s hs x) = x :=
  incl_apply_same ⟨s, hs⟩ x

/-- The bracket of two homogeneous inclusions has only the coordinate whose
manuscript weight is the sum of their manuscript weights.  This coordinate
form is independent of any choice of basis. -/
theorem bracket_weightIncl_apply_eq_zero_of_ne
    (s t : ℕ) (hs : s < c) (ht : t < c)
    (x : Piece X s) (y : Piece X t) (k : Fin c)
    (hk : k.val ≠ s + t + 1) :
    ⁅weightIncl s hs x, weightIncl t ht y⁆ k = 0 := by
  change bracket (weightIncl s hs x) (weightIncl t ht y) k = 0
  rcases k with ⟨(_ | _ | q), hkc⟩
  · exact bracket_apply_zero _ _ hkc
  · rw [bracket_apply_one]
    by_cases hs0 : s = 0 <;> by_cases ht0 : t = 0
    · subst s
      subst t
      exact (hk rfl).elim
    · have hy0 : degreeOne (weightIncl t ht y) (by omega) = 0 := by
        change weightIncl t ht y ⟨0, by omega⟩ = 0
        exact incl_apply_of_ne _ _ (by intro h; have hv := congrArg Fin.val h; simp at hv; omega) _
      rw [hy0, map_zero]
      rfl
    · have hx0 : degreeOne (weightIncl s hs x) (by omega) = 0 := by
        change weightIncl s hs x ⟨0, by omega⟩ = 0
        exact incl_apply_of_ne _ _ (by intro h; have hv := congrArg Fin.val h; simp at hv; omega) _
      rw [hx0]
      exact LinearMap.congr_fun (map_zero (generatorBracket X)) _
    · have hx0 : degreeOne (weightIncl s hs x) (by omega) = 0 := by
        change weightIncl s hs x ⟨0, by omega⟩ = 0
        exact incl_apply_of_ne _ _ (by intro h; have hv := congrArg Fin.val h; simp at hv; omega) _
      rw [hx0]
      exact LinearMap.congr_fun (map_zero (generatorBracket X)) _
  · rw [bracket_apply_succ_succ]
    by_cases hs0 : s = 0
    · subst s
      have hx0 : degreeOne (weightIncl 0 hs x) (by omega) = x := by
        exact incl_apply_same (⟨0, hs⟩ : Fin c) x
      rw [hx0]
      by_cases ht0 : t = 0
      · subst t
        have hy0 : derived (weightIncl 0 ht y) q (by omega) = 0 := by
            change weightIncl 0 ht y ⟨q + 1, by omega⟩ = 0
            exact incl_apply_of_ne _ _ (by
              intro h
              exact Nat.succ_ne_zero q (congrArg Fin.val h)) _
        have hxq : derived (weightIncl 0 hs x) q (by omega) = 0 := by
            change weightIncl 0 hs x ⟨q + 1, by omega⟩ = 0
            exact incl_apply_of_ne _ _ (by
              intro h
              exact Nat.succ_ne_zero q (congrArg Fin.val h)) _
        rw [hy0, hxq, map_zero, map_zero, sub_self]
        rfl
      · have hy0 : degreeOne (weightIncl t ht y) (by omega) = 0 := by
          change weightIncl t ht y ⟨0, by omega⟩ = 0
          exact incl_apply_of_ne _ _ (by intro h; have hv := congrArg Fin.val h; simp at hv; omega) _
        have hxq : derived (weightIncl 0 hs x) q (by omega) = 0 := by
          change weightIncl 0 hs x ⟨q + 1, by omega⟩ = 0
          exact incl_apply_of_ne _ _ (by
            intro h
            exact Nat.succ_ne_zero q (congrArg Fin.val h)) _
        rw [hy0, hxq]
        by_cases htq : t = q + 1
        · subst t
          exact (hk (by simp)).elim
        · have hyq : derived (weightIncl t ht y) q (by omega) = 0 := by
            change weightIncl t ht y ⟨q + 1, by omega⟩ = 0
            exact incl_apply_of_ne _ _ (by
              intro h
              exact htq (congrArg Fin.val h).symm) _
          rw [hyq, map_zero, zero_sub]
          rw [(Action.apply X q x).map_zero]
          exact neg_zero
    · have hx0 : degreeOne (weightIncl s hs x) (by omega) = 0 := by
        change weightIncl s hs x ⟨0, by omega⟩ = 0
        exact incl_apply_of_ne _ _ (by intro h; have hv := congrArg Fin.val h; simp at hv; omega) _
      rw [hx0, Action.apply_zero_apply, sub_zero]
      by_cases ht0 : t = 0
      · subst t
        have hy0 : degreeOne (weightIncl 0 ht y) (by omega) = y := by
          exact incl_apply_same (⟨0, ht⟩ : Fin c) y
        rw [hy0]
        by_cases hsq : s = q + 1
        · subst s
          exact (hk (by simp)).elim
        · have hxq : derived (weightIncl s hs x) q (by omega) = 0 := by
            change weightIncl s hs x ⟨q + 1, by omega⟩ = 0
            exact incl_apply_of_ne _ _ (by
              intro h
              exact hsq (congrArg Fin.val h).symm) _
          rw [hxq, map_zero]
          rfl
      · have hy0 : degreeOne (weightIncl t ht y) (by omega) = 0 := by
          change weightIncl t ht y ⟨0, by omega⟩ = 0
          exact incl_apply_of_ne _ _ (by intro h; have hv := congrArg Fin.val h; simp at hv; omega) _
        rw [hy0, Action.apply_zero_apply]
        rfl

@[simp]
theorem projectPrefix_weightIncl_eq_zero (k s : ℕ) (hk : k ≤ c) (hs : s < c)
    (hks : k ≤ s) (x : Piece X s) :
    projectPrefix k hk (weightIncl s hs x) = 0 := by
  funext i
  rw [projectPrefix_apply]
  apply incl_apply_of_ne
  intro h
  have := congrArg Fin.val h
  simp only at this
  omega

/-- Restricting a homogeneous coordinate which lies inside the prefix retains
that coordinate verbatim. -/
@[simp]
theorem projectPrefix_weightIncl_of_lt (k s : ℕ) (hk : k ≤ c) (hs : s < c)
    (hsk : s < k) (x : Piece X s) :
    projectPrefix k hk (weightIncl s hs x) = weightIncl s hsk x := by
  funext i
  rw [projectPrefix_apply]
  by_cases h : i.val = s
  · subst s
    simp [weightIncl, incl]
  · change incl (⟨s, hs⟩ : Fin c) x
        ⟨i.val, i.isLt.trans_le hk⟩ =
      incl (⟨s, hsk⟩ : Fin k) x i
    rw [incl_apply_of_ne, incl_apply_of_ne]
    · intro heq
      exact h (congrArg Fin.val heq)
    · intro heq
      exact h (congrArg Fin.val heq)

section Basis

variable {ι : Type v} [Fintype ι] [LinearOrder ι]

/-- Hall-basis indices for all homogeneous pieces, in zero-based coordinates. -/
def PieceIndex (ι : Type v) [LinearOrder ι] : ℕ → Type v
  | 0 => ι
  | q + 1 => HallIndex ι q

instance pieceIndexFinite (n : ℕ) : Finite (PieceIndex ι n) := by
  cases n with
  | zero => simpa [PieceIndex] using (inferInstance : Finite ι)
  | succ q => simpa [PieceIndex] using (inferInstance : Finite (HallIndex ι q))

/-- The manuscript basis in one homogeneous piece. -/
def pieceBasis (b : Module.Basis ι ℤ X) :
    (n : ℕ) → Module.Basis (PieceIndex ι n) ℤ (Piece X n)
  | 0 => b
  | q + 1 => by
      let hb := hallBasis b q
      exact Module.Basis.ofEquivFun hb.equivFun.toAddEquiv.toIntLinearEquiv

/-- The finite ordered Hall basis of the truncated free metabelian Lie ring.
Its index is literally a weight together with the appropriate generator/Hall
index in that weight. -/
def hallGradedBasis (b : Module.Basis ι ℤ X) :
    Module.Basis ((i : Fin c) × PieceIndex ι i.val) ℤ (Free X c) := by
  let bPi := Pi.basis (fun i : Fin c ↦ pieceBasis b i.val)
  exact Module.Basis.ofEquivFun bPi.equivFun.toAddEquiv.toIntLinearEquiv

end Basis

/-! ## Metabelianity and the lower-central cutoff -/

/-- The linear degree-one projection, used to recognize the derived ideal. -/
def degreeOneLinear (h : 0 < c) : Free X c →ₗ[ℤ] X := project ⟨0, h⟩

@[simp]
theorem degreeOneLinear_apply (h : 0 < c) (x : Free X c) :
    degreeOneLinear h x = degreeOne x h := by
  rfl

private theorem bracket_eq_zero_of_degreeOne_eq_zero (h : 0 < c)
    {x y : Free X c} (hx : degreeOne x h = 0) (hy : degreeOne y h = 0) :
    ⁅x, y⁆ = 0 := by
  funext i
  rcases i with ⟨(_ | _ | q), hi⟩
  · exact bracket_apply_zero x y hi
  · change generatorBracket X (degreeOne x (by omega))
        (degreeOne y (by omega)) = 0
    rw [show degreeOne x (by omega) = 0 by exact hx,
      show degreeOne y (by omega) = 0 by exact hy]
    simp
  · change Action.apply X q (degreeOne y (by omega))
          (derived x q (by omega)) -
        Action.apply X q (degreeOne x (by omega))
          (derived y q (by omega)) = 0
    rw [show degreeOne x (by omega) = 0 by exact hx,
      show degreeOne y (by omega) = 0 by exact hy]
    simp

/-- Two homogeneous components of weights at least two commute in the free
metabelian model.  Here the stored coordinate `s` has manuscript weight
`s+1`, so positivity of `s` and `t` is the precise derived-derived case. -/
theorem bracket_weightIncl_eq_zero_of_pos
    (s t : ℕ) (hs : s < c) (ht : t < c) (hs0 : 0 < s) (ht0 : 0 < t)
    (x : Piece X s) (y : Piece X t) :
    ⁅weightIncl s hs x, weightIncl t ht y⁆ = 0 := by
  apply bracket_eq_zero_of_degreeOne_eq_zero (X := X) (by omega)
  · change weightIncl s hs x ⟨0, by omega⟩ = 0
    exact incl_apply_of_ne ⟨s, hs⟩ ⟨0, by omega⟩ (by
      intro h
      have hval : (0 : ℕ) = s := by
        simpa using congrArg Fin.val h
      omega) x
  · change weightIncl t ht y ⟨0, by omega⟩ = 0
    exact incl_apply_of_ne ⟨t, ht⟩ ⟨0, by omega⟩ (by
      intro h
      have hval : (0 : ℕ) = t := by
        simpa using congrArg Fin.val h
      omega) y

private theorem degreeOne_eq_zero_of_mem_derived (h : 0 < c)
    {x : Free X c} (hx : x ∈ LieAlgebra.derivedSeries ℤ (Free X c) 1) :
    degreeOne x h = 0 := by
  let K : LieIdeal ℤ (Free X c) :=
    LieSubmodule.mk (LinearMap.ker (degreeOneLinear h)) (by
      intro a b _
      change degreeOneLinear h ⁅a, b⁆ = 0
      exact degreeOne_bracket a b h)
  have hle : LieAlgebra.derivedSeries ℤ (Free X c) 1 ≤ K := by
    rw [LieAlgebra.derivedSeries_def,
      LieAlgebra.derivedSeriesOfIdeal_succ,
      LieAlgebra.derivedSeriesOfIdeal_zero,
      LieSubmodule.lie_le_iff]
    intro a _ b _
    change degreeOneLinear h ⁅a, b⁆ = 0
    exact degreeOne_bracket a b h
  exact (show degreeOneLinear h x = 0 from hle hx)

/-- The explicitly constructed truncated free object is metabelian. -/
theorem isMetabelian : LieRings.IsMetabelian (Free X c) := by
  cases c with
  | zero =>
      rw [LieRings.IsMetabelian.iff_bracket_eq_zero]
      intro x y _ _
      exact Subsingleton.elim _ _
  | succ c =>
      rw [LieRings.IsMetabelian.iff_bracket_eq_zero]
      intro x y hx hy
      exact bracket_eq_zero_of_degreeOne_eq_zero (X := X) (Nat.succ_pos c)
        (degreeOne_eq_zero_of_mem_derived (X := X) (Nat.succ_pos c) hx)
        (degreeOne_eq_zero_of_mem_derived (X := X) (Nat.succ_pos c) hy)

/-- Elements with zero coordinates strictly below `k`.  Coordinate `i` has
manuscript weight `i+1`, so this is the filtration of weights at least `k+1`. -/
def tail (k : ℕ) : LieIdeal ℤ (Free X c) :=
  LieSubmodule.mk
    { carrier := {x | ∀ i : Fin c, i.val < k → x i = 0}
      zero_mem' := by intro i _; rfl
      add_mem' := by
        intro x y hx hy i hi
        rw [Pi.add_apply, hx i hi, hy i hi, add_zero]
      smul_mem' := by
        intro z x hx i hi
        change z • x i = 0
        rw [hx i hi]
        exact smul_zero z }
    (by
      intro x y hy i hi
      rcases i with ⟨(_ | _ | q), hic⟩
      · exact bracket_apply_zero x y hic
      · change 1 < k at hi
        have hk : 0 < k := by omega
        have hc : 0 < c := by omega
        have hy0 : degreeOne y hc = 0 := by
          simpa [degreeOne] using hy ⟨0, hc⟩ hk
        change generatorBracket X (degreeOne x (by omega))
            (degreeOne y (by omega)) = 0
        rw [show degreeOne y (by omega) = 0 by exact hy0]
        exact (generatorBracket X (degreeOne x (by omega))).map_zero
      · change q + 2 < k at hi
        have hk : 0 < k := by omega
        have hc : 0 < c := by omega
        have hy0 : degreeOne y hc = 0 := by
          simpa [degreeOne] using hy ⟨0, hc⟩ hk
        have hqc : q + 1 < c := by omega
        have hqk : q + 1 < k := by omega
        have hyq : derived y q hqc = 0 := by
          simpa [derived] using hy (⟨q + 1, hqc⟩ : Fin c) hqk
        change Action.apply X q (degreeOne y (by omega))
              (derived x q (by omega)) -
            Action.apply X q (degreeOne x (by omega))
              (derived y q (by omega)) = 0
        rw [hy0, hyq]
        simp)

@[simp]
theorem mem_tail_iff (x : Free X c) (k : ℕ) :
    x ∈ tail k ↔ ∀ i : Fin c, i.val < k → x i = 0 := Iff.rfl

private theorem bracket_mem_tail_succ (k : ℕ) (x y : Free X c)
    (hy : y ∈ tail k) : ⁅x, y⁆ ∈ tail (k + 1) := by
  intro i hi
  rcases i with ⟨(_ | _ | q), hic⟩
  · exact bracket_apply_zero x y hic
  · change 1 < k + 1 at hi
    have hk : 0 < k := by omega
    have hc : 0 < c := by omega
    have hy0 : degreeOne y hc = 0 := by
      simpa [degreeOne] using hy ⟨0, hc⟩ hk
    change generatorBracket X (degreeOne x (by omega))
        (degreeOne y (by omega)) = 0
    rw [show degreeOne y (by omega) = 0 by exact hy0]
    exact (generatorBracket X (degreeOne x (by omega))).map_zero
  · change q + 2 < k + 1 at hi
    have hk : 0 < k := by omega
    have hc : 0 < c := by omega
    have hy0 : degreeOne y hc = 0 := by
      simpa [degreeOne] using hy ⟨0, hc⟩ hk
    have hqc : q + 1 < c := by omega
    have hqk : q + 1 < k := by omega
    have hyq : derived y q hqc = 0 := by
      simpa [derived] using hy (⟨q + 1, hqc⟩ : Fin c) hqk
    change Action.apply X q (degreeOne y (by omega))
          (derived x q (by omega)) -
        Action.apply X q (degreeOne x (by omega))
          (derived y q (by omega)) = 0
    rw [hy0, hyq]
    simp

/-- The `k`-th lower-central term is supported in weights at least `k+1`. -/
theorem lowerCentralSeries_le_tail (k : ℕ) :
    LieModule.lowerCentralSeries ℤ (Free X c) (Free X c) k ≤ tail k := by
  induction k with
  | zero =>
      intro x _ i hi
      omega
  | succ k ih =>
      rw [LieModule.lowerCentralSeries_succ,
        LieSubmodule.lie_le_iff]
      intro x _ y hy
      exact bracket_mem_tail_succ k x y (ih hy)

@[simp]
theorem tail_cutoff_eq_bot : tail (X := X) (c := c) c = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  change x = 0
  funext i
  exact hx i i.isLt

/-- The cutoff really has nilpotency class at most `c`: in Mathlib's
zero-based convention its `c`-th lower-central term is zero. -/
theorem lowerCentralSeries_cutoff_eq_bot :
    LieModule.lowerCentralSeries ℤ (Free X c) (Free X c) c = ⊥ := by
  rw [eq_bot_iff]
  exact (lowerCentralSeries_le_tail c).trans (by rw [tail_cutoff_eq_bot])

end Free

end

end FreeMetabelian
