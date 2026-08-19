import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-!
# The missing functorial API for symmetric tensor powers

The underlying object is Mathlib's quotient `Sym[R] ι M`.  This file adds the
universal property and the functorial maps needed by the Koszul construction;
it does not replace symmetric powers by polynomial modules.
-/

open TensorProduct Equiv

namespace SymmetricPower

universe u v w x y

noncomputable section

variable {R : Type u} [CommSemiring R]
variable {ι : Type u} {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- A multilinear map is symmetric if permuting all input slots does not
change its value. -/
def IsSymmetric (f : MultilinearMap R (fun _ : ι ↦ M) N) : Prop :=
  ∀ (e : Equiv.Perm ι) (x : ι → M), f (x ∘ e) = f x

private def liftAddHom (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hf : IsSymmetric f) : Sym[R] ι M →+ N :=
  (addConGen (Rel R ι M)).lift (PiTensorProduct.lift f).toAddMonoidHom <|
    AddCon.addConGen_le fun x y hxy ↦
      (AddCon.ker_rel (PiTensorProduct.lift f).toAddMonoidHom).2 <| by
        cases hxy with
        | perm e g =>
            change PiTensorProduct.lift f (PiTensorProduct.tprod R g) =
              PiTensorProduct.lift f (PiTensorProduct.tprod R (g ∘ e))
            rw [PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
            exact (hf e g).symm

/-- Universal lift of a symmetric multilinear map through Mathlib's actual
symmetric-power quotient. -/
def lift (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hf : IsSymmetric f) : Sym[R] ι M →ₗ[R] N where
  __ := liftAddHom f hf
  map_smul' r x := by
    refine AddCon.induction_on x ?_
    intro z
    change PiTensorProduct.lift f (r • z) = r • PiTensorProduct.lift f z
    exact map_smul (PiTensorProduct.lift f) r z

@[simp]
theorem lift_tprod (f : MultilinearMap R (fun _ : ι ↦ M) N)
    (hf : IsSymmetric f) (x : ι → M) :
    lift f hf (⨂ₛ[R] i, x i) = f x := by
  change PiTensorProduct.lift f (PiTensorProduct.tprod R x) = f x
  exact PiTensorProduct.lift.tprod x

/-- Pure symmetric tensors determine a linear map. -/
theorem linearMap_ext {f g : Sym[R] ι M →ₗ[R] N}
    (h : ∀ x : ι → M, f (⨂ₛ[R] i, x i) = g (⨂ₛ[R] i, x i)) : f = g := by
  apply LinearMap.ext_on (span_tprod_eq_top R ι M)
  rintro _ ⟨x, rfl⟩
  exact h x

/-- Functoriality of symmetric powers. -/
def map (f : M →ₗ[R] N) : Sym[R] ι M →ₗ[R] Sym[R] ι N :=
  lift ((tprod R).compLinearMap (fun _ ↦ f)) <| by
    intro e x
    simpa [MultilinearMap.compLinearMap_apply, Function.comp_def] using
      (tprod_equiv (R := R) (M := N) e (f ∘ x))

@[simp]
theorem map_tprod (f : M →ₗ[R] N) (x : ι → M) :
    map (R := R) (ι := ι) f (⨂ₛ[R] i, x i) =
      ⨂ₛ[R] i, f (x i) := by
  rw [map, lift_tprod]
  rfl

@[simp]
theorem map_id : map (R := R) (ι := ι) (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  apply linearMap_ext
  intro x
  simp

@[simp]
theorem map_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map (R := R) (ι := ι) (g.comp f) =
      (map (R := R) (ι := ι) g).comp (map (R := R) (ι := ι) f) := by
  apply linearMap_ext
  intro x
  simp

/-- Reindex the tensor slots.  This is an equivalence at the symmetric-power
level; only its forward linear map is needed below. -/
def reindex {κ : Type u} (e : ι ≃ κ) : Sym[R] ι M →ₗ[R] Sym[R] κ M :=
  lift ((tprod R).domDomCongr e.symm) <| by
    intro p x
    change tprod R ((x ∘ p) ∘ e.symm) = tprod R (x ∘ e.symm)
    let q : Equiv.Perm κ := e.symm.trans p |>.trans e
    have : (x ∘ p) ∘ e.symm = (x ∘ e.symm) ∘ q := by
      funext i
      simp [q, Function.comp_def]
    rw [this]
    exact tprod_equiv q (x ∘ e.symm)

@[simp]
theorem reindex_tprod {κ : Type u} (e : ι ≃ κ) (x : ι → M) :
    reindex (R := R) e (tprod R x) = tprod R (x ∘ e.symm) := by
  rw [reindex, lift_tprod]
  change tprod R (fun i ↦ x (e.symm i)) = tprod R (x ∘ e.symm)
  rfl

@[simp]
theorem reindex_map {κ : Type u} (e : ι ≃ κ) (f : M →ₗ[R] N) :
    (reindex (R := R) (M := N) e).comp (map (R := R) (ι := ι) f) =
      (map (R := R) (ι := κ) f).comp (reindex (R := R) (M := M) e) := by
  apply linearMap_ext
  intro x
  simp only [LinearMap.comp_apply, map_tprod, reindex_tprod]
  congr 1

section Polarization

variable {R₀ : Type} [CommSemiring R₀]
variable {M₀ : Type v} [AddCommMonoid M₀] [Module R₀ M₀]
variable {U₀ : Type w} {V₀ : Type x} {N₀ : Type y}
variable [AddCommMonoid U₀] [Module R₀ U₀]
variable [AddCommMonoid V₀] [Module R₀ V₀]
variable [AddCommMonoid N₀] [Module R₀ N₀]

private def omitPerm {q : ℕ} (e : Equiv.Perm (Fin (q + 1)))
    (i : Fin (q + 1)) : Equiv.Perm (Fin q) :=
  ((finSuccAboveEquiv i).trans
    (Equiv.subtypeEquiv e (fun j ↦ by
      constructor
      · exact fun (h : j ≠ i) h' ↦ h (e.injective h')
      · exact fun (h : e j ≠ e i) h' ↦ h (congrArg e h')))).trans
      (finSuccAboveEquiv (e i)).symm

private theorem omitPerm_spec {q : ℕ} (e : Equiv.Perm (Fin (q + 1)))
    (i : Fin (q + 1)) (j : Fin q) :
    (e i).succAbove (omitPerm e i j) = e (i.succAbove j) := by
  change (finSuccAboveEquiv (e i)
    ((finSuccAboveEquiv (e i)).symm
      ⟨e (i.succAbove j), by
        exact fun h ↦ Fin.succAbove_ne i j (e.injective h)⟩)).1 = _
  rw [Equiv.apply_symm_apply]

/-- Polarization with one distinguished output slot.  On a pure tensor it is
the sum over every choice of the distinguished variable. -/
def polarizeMultilinear (q : ℕ) (headMap : M₀ →ₗ[R₀] U₀)
    (toothMap : M₀ →ₗ[R₀] V₀)
    (theta : U₀ ⊗[R₀] Sym[R₀] (Fin q) V₀ →ₗ[R₀] N₀) :
    MultilinearMap R₀ (fun _ : Fin (q + 1) ↦ M₀) N₀ := by
  let tooth : MultilinearMap R₀ (fun _ : Fin q ↦ M₀)
      (Sym[R₀] (Fin q) V₀) :=
    (tprod R₀).compLinearMap (fun _ ↦ toothMap)
  let theta' : U₀ →ₗ[R₀] Sym[R₀] (Fin q) V₀ →ₗ[R₀] N₀ :=
    (TensorProduct.lift.equiv (RingHom.id R₀) U₀
      (Sym[R₀] (Fin q) V₀) N₀).symm theta
  let head : M₀ →ₗ[R₀] MultilinearMap R₀ (fun _ : Fin q ↦ M₀) N₀ :=
    { toFun := fun x ↦ (theta' (headMap x)).compMultilinearMap tooth
      map_add' := by
        intro x y
        ext z
        simp [theta']
      map_smul' := by
        intro r x
        ext z
        simp [theta'] }
  exact ∑ i, head.uncurryMid i

theorem polarizeMultilinear_apply (q : ℕ) (headMap : M₀ →ₗ[R₀] U₀)
    (toothMap : M₀ →ₗ[R₀] V₀)
    (theta : U₀ ⊗[R₀] Sym[R₀] (Fin q) V₀ →ₗ[R₀] N₀)
    (x : Fin (q + 1) → M₀) :
    polarizeMultilinear q headMap toothMap theta x = ∑ i,
      theta (headMap (x i) ⊗ₜ[R₀] tprod R₀
        (fun j ↦ toothMap (i.removeNth x j))) := by
  simp [polarizeMultilinear, TensorProduct.lift.equiv_symm_apply]

theorem polarizeMultilinear_symmetric (q : ℕ)
    (headMap : M₀ →ₗ[R₀] U₀) (toothMap : M₀ →ₗ[R₀] V₀)
    (theta : U₀ ⊗[R₀] Sym[R₀] (Fin q) V₀ →ₗ[R₀] N₀) :
    IsSymmetric (polarizeMultilinear q headMap toothMap theta) := by
  intro e x
  rw [polarizeMultilinear_apply, polarizeMultilinear_apply]
  apply Fintype.sum_equiv e
  intro i
  simp only [Function.comp_apply]
  apply congrArg theta
  apply congrArg (fun s ↦ headMap (x (e i)) ⊗ₜ[R₀] s)
  let lhs : Fin q → V₀ := fun j ↦ toothMap (i.removeNth (x ∘ e) j)
  let rhs : Fin q → V₀ := fun j ↦ toothMap ((e i).removeNth x j)
  have hfun : lhs = rhs ∘ omitPerm e i := by
    funext j
    simp only [lhs, rhs, Function.comp_apply, Fin.removeNth_apply]
    rw [omitPerm_spec]
  change tprod R₀ lhs = tprod R₀ rhs
  rw [hfun]
  exact tprod_equiv (omitPerm e i) rhs

/-- The symmetric-power map induced by one-head polarization. -/
def polarize (q : ℕ) (headMap : M₀ →ₗ[R₀] U₀)
    (toothMap : M₀ →ₗ[R₀] V₀)
    (theta : U₀ ⊗[R₀] Sym[R₀] (Fin q) V₀ →ₗ[R₀] N₀) :
    Sym[R₀] (Fin (q + 1)) M₀ →ₗ[R₀] N₀ :=
  lift (polarizeMultilinear q headMap toothMap theta)
    (polarizeMultilinear_symmetric q headMap toothMap theta)

@[simp]
theorem polarize_tprod (q : ℕ) (headMap : M₀ →ₗ[R₀] U₀)
    (toothMap : M₀ →ₗ[R₀] V₀)
    (theta : U₀ ⊗[R₀] Sym[R₀] (Fin q) V₀ →ₗ[R₀] N₀)
    (x : Fin (q + 1) → M₀) :
    polarize q headMap toothMap theta (tprod R₀ x) = ∑ i,
      theta (headMap (x i) ⊗ₜ[R₀] tprod R₀
        (fun j ↦ toothMap (i.removeNth x j))) := by
  rw [polarize, lift_tprod, polarizeMultilinear_apply]

end Polarization

section Product

variable {R₀ : Type} [CommSemiring R₀]
variable {M₀ : Type v} [AddCommMonoid M₀] [Module R₀ M₀]

variable (R₀ M₀)

/-- The multilinear concatenation map before passing either block of variables
to a symmetric power.  Keeping this private makes the choice of
`finSumFinEquiv` an implementation detail. -/
private def concatMultilinear (a b : ℕ) :
    MultilinearMap R₀ (fun _ : Fin a ↦ M₀)
      (MultilinearMap R₀ (fun _ : Fin b ↦ M₀) Sym[R₀] (Fin (a + b)) M₀) :=
  MultilinearMap.currySum <|
    (tprod R₀ (M := M₀) (ι := Fin (a + b))).domDomCongr finSumFinEquiv.symm

@[simp]
private theorem concatMultilinear_apply (a b : ℕ) (x : Fin a → M₀) (y : Fin b → M₀) :
    concatMultilinear R₀ M₀ a b x y =
      tprod R₀ (Fin.append x y) := by
  unfold concatMultilinear
  rw [MultilinearMap.currySum_apply]
  change tprod R₀ (fun i ↦ Sum.elim x y (finSumFinEquiv.symm i)) = _
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

private theorem append_update_left (a b : ℕ) (x : Fin a → M₀) (y : Fin b → M₀)
    (i : Fin a) (p : M₀) :
    Fin.append (Function.update x i p) y =
      Function.update (Fin.append x y) (Fin.castAdd b i) p := by
  classical
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    simp [Function.update_apply]
  · intro j
    have hne : Fin.natAdd a j ≠ Fin.castAdd b i := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp [Function.update_apply, hne]

private theorem concatMultilinear_right_symmetric (a b : ℕ) (x : Fin a → M₀) :
    IsSymmetric (concatMultilinear R₀ M₀ a b x) := by
  intro e y
  rw [concatMultilinear_apply, concatMultilinear_apply]
  let E : Equiv.Perm (Fin (a + b)) :=
    finSumFinEquiv.symm.trans
      ((Equiv.refl (Fin a)).sumCongr e) |>.trans finSumFinEquiv
  have hfun : Fin.append x (y ∘ e) = Fin.append x y ∘ E := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [E, Function.comp_def]
    · intro j
      simp [E, Function.comp_def]
  rw [hfun]
  exact tprod_equiv E (Fin.append x y)

/-- The first block of the symmetric product, with the second block already
descended to a symmetric power. -/
private def productMultilinear (a b : ℕ) :
    MultilinearMap R₀ (fun _ : Fin a ↦ M₀)
      (Sym[R₀] (Fin b) M₀ →ₗ[R₀] Sym[R₀] (Fin (a + b)) M₀) :=
  MultilinearMap.mk' (fun x ↦
      lift (concatMultilinear R₀ M₀ a b x)
        (concatMultilinear_right_symmetric R₀ M₀ a b x))
    (fun x i p q ↦ by
      apply linearMap_ext
      intro y
      simp only [LinearMap.add_apply, lift_tprod, concatMultilinear_apply]
      rw [append_update_left, append_update_left, append_update_left]
      exact (tprod R₀ (M := M₀) (ι := Fin (a + b))).map_update_add
        (Fin.append x y) (Fin.castAdd b i) p q)
    (fun x i r p ↦ by
      apply linearMap_ext
      intro y
      simp only [LinearMap.smul_apply, lift_tprod, concatMultilinear_apply]
      rw [append_update_left, append_update_left]
      exact (tprod R₀ (M := M₀) (ι := Fin (a + b))).map_update_smul
        (Fin.append x y) (Fin.castAdd b i) r p)

private theorem productMultilinear_symmetric (a b : ℕ) :
    IsSymmetric (productMultilinear R₀ M₀ a b) := by
  intro e x
  apply linearMap_ext
  intro y
  change lift (concatMultilinear R₀ M₀ a b (x ∘ e)) _ (tprod R₀ y) =
    lift (concatMultilinear R₀ M₀ a b x) _ (tprod R₀ y)
  rw [lift_tprod, lift_tprod, concatMultilinear_apply, concatMultilinear_apply]
  let E : Equiv.Perm (Fin (a + b)) :=
    finSumFinEquiv.symm.trans
      (e.sumCongr (Equiv.refl (Fin b))) |>.trans finSumFinEquiv
  have hfun : Fin.append (x ∘ e) y = Fin.append x y ∘ E := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [E, Function.comp_def]
    · intro j
      simp [E, Function.comp_def]
  rw [hfun]
  exact tprod_equiv E (Fin.append x y)

/-- Multiplication of homogeneous symmetric tensors. -/
def product (a b : ℕ) :
    Sym[R₀] (Fin a) M₀ →ₗ[R₀]
      Sym[R₀] (Fin b) M₀ →ₗ[R₀] Sym[R₀] (Fin (a + b)) M₀ :=
  lift (productMultilinear R₀ M₀ a b) (productMultilinear_symmetric R₀ M₀ a b)

@[simp]
theorem product_tprod_tprod (a b : ℕ) (x : Fin a → M₀) (y : Fin b → M₀) :
    product R₀ M₀ a b (tprod R₀ x) (tprod R₀ y) =
      tprod R₀ (Fin.append x y) := by
  simp [product, productMultilinear]

/-- Multiplication by a degree-one element.  The order of variables agrees
with the manuscript: the new variable is inserted on the left. -/
def insert (n : ℕ) (x : M₀) :
    Sym[R₀] (Fin n) M₀ →ₗ[R₀] Sym[R₀] (Fin (n + 1)) M₀ :=
  (reindex (R := R₀) (finCongr (Nat.one_add n))).comp
    (product R₀ M₀ 1 n (tprod R₀ (Fin.cons x ![])))

@[simp]
theorem insert_tprod (n : ℕ) (x : M₀) (y : Fin n → M₀) :
    insert R₀ M₀ n x (tprod R₀ y) = tprod R₀ (Fin.cons x y) := by
  rw [insert, LinearMap.comp_apply, product_tprod_tprod, reindex_tprod]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      change Fin.append (Fin.cons x ![]) y
        (Fin.cast (Nat.one_add n).symm i.succ) = y i
      rw [show Fin.cast (Nat.one_add n).symm i.succ = Fin.natAdd 1 i by
        apply Fin.ext
        simp
        omega]
      exact Fin.append_right _ _ i

/-- Insertion, linear also in the element being inserted. -/
def insertLinear (n : ℕ) :
    M₀ →ₗ[R₀] Sym[R₀] (Fin n) M₀ →ₗ[R₀] Sym[R₀] (Fin (n + 1)) M₀ where
  toFun := insert R₀ M₀ n
  map_add' x y := by
    apply linearMap_ext
    intro z
    simp only [LinearMap.add_apply, insert_tprod]
    exact (tprod R₀).cons_add z x y
  map_smul' r x := by
    apply linearMap_ext
    intro z
    simp only [LinearMap.smul_apply, insert_tprod, RingHom.id_apply]
    exact (tprod R₀).cons_smul z r x

/-- Evaluation of `insertLinear` at a fixed symmetric tensor, linear in the
inserted factor. -/
def insertRight (n : ℕ) (s : Sym[R₀] (Fin n) M₀) :
    M₀ →ₗ[R₀] Sym[R₀] (Fin (n + 1)) M₀ where
  toFun x := insert R₀ M₀ n x s
  map_add' x y := LinearMap.congr_fun (insertLinear R₀ M₀ n |>.map_add x y) s
  map_smul' r x := LinearMap.congr_fun (insertLinear R₀ M₀ n |>.map_smul r x) s

@[simp]
theorem insertRight_apply (n : ℕ) (s : Sym[R₀] (Fin n) M₀) (x : M₀) :
    insertRight R₀ M₀ n s x = insert R₀ M₀ n x s := rfl

theorem insert_add (n : ℕ) (x y : M₀) :
    insert R₀ M₀ n (x + y) = insert R₀ M₀ n x + insert R₀ M₀ n y :=
  (insertLinear R₀ M₀ n).map_add x y

theorem insert_smul (n : ℕ) (r : R₀) (x : M₀) :
    insert R₀ M₀ n (r • x) = r • insert R₀ M₀ n x :=
  (insertLinear R₀ M₀ n).map_smul r x

theorem insert_add_apply (n : ℕ) (x y : M₀) (s : Sym[R₀] (Fin n) M₀) :
    insert R₀ M₀ n (x + y) s =
      insert R₀ M₀ n x s + insert R₀ M₀ n y s := by
  rw [insert_add, LinearMap.add_apply]

theorem insert_smul_apply (n : ℕ) (r : R₀) (x : M₀)
    (s : Sym[R₀] (Fin n) M₀) :
    insert R₀ M₀ n (r • x) s = r • insert R₀ M₀ n x s := by
  rw [insert_smul, LinearMap.smul_apply]

@[simp]
theorem insert_zero (n : ℕ) : insert R₀ M₀ n 0 = 0 := by
  rw [← zero_smul R₀ (0 : M₀), insert_smul]
  exact zero_smul R₀ _

@[simp]
theorem insert_zero_apply (n : ℕ) (s : Sym[R₀] (Fin n) M₀) :
    insert R₀ M₀ n 0 s = 0 := by
  rw [insert_zero]
  rfl

@[simp]
theorem map_insert {N₀ : Type*} [AddCommMonoid N₀] [Module R₀ N₀]
    (f : M₀ →ₗ[R₀] N₀) (n : ℕ) (x : M₀) :
    (map (R := R₀) (ι := Fin (n + 1)) f).comp (insert R₀ M₀ n x) =
      (insert R₀ N₀ n (f x)).comp (map (R := R₀) (ι := Fin n) f) := by
  apply linearMap_ext
  intro y
  simp only [LinearMap.comp_apply, insert_tprod, map_tprod]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

/-- The two degree-one insertion maps commute.  This is the precise
commutativity fact used in the cancellation proof for the Koszul
differential. -/
theorem insert_comm (n : ℕ) (x y : M₀) :
    (insert R₀ M₀ (n + 1) x).comp (insert R₀ M₀ n y) =
      (insert R₀ M₀ (n + 1) y).comp (insert R₀ M₀ n x) := by
  apply linearMap_ext
  intro z
  simp only [LinearMap.comp_apply, insert_tprod]
  let p : Equiv.Perm (Fin ((n + 1) + 1)) := Equiv.swap 0 1
  let lhs : Fin ((n + 1) + 1) → M₀ := Fin.cons x (Fin.cons y z)
  let rhs : Fin ((n + 1) + 1) → M₀ := Fin.cons y (Fin.cons x z)
  have hp : lhs = rhs ∘ p := by
    funext i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp [lhs, rhs, p, Equiv.swap_apply_def]
    · refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp [lhs, rhs, p, Equiv.swap_apply_def]
      · have h0 : (i.succ.succ : Fin ((n + 1) + 1)) ≠ 0 := by
          intro h
          have := congrArg Fin.val h
          simp at this
        have h1 : (i.succ.succ : Fin ((n + 1) + 1)) ≠ 1 := by
          intro h
          have := congrArg Fin.val h
          simp at this
        simp [lhs, rhs, p, Equiv.swap_apply_def, h0, h1]
  change tprod R₀ lhs = tprod R₀ rhs
  rw [hp]
  exact tprod_equiv p rhs

end Product

section Basis

variable {R₀ : Type} [CommSemiring R₀]
variable {M₀ : Type v} [AddCommMonoid M₀] [Module R₀ M₀]
variable {κ : Type x} [Finite κ]

local instance vectorPermSetoid (n : ℕ) : Setoid (List.Vector κ n) :=
  List.Vector.Perm.isSetoid κ n

/-- The unordered tuple represented by a function on `Fin n`.  Defining this
through `Sym.symEquivSym'` makes its permutation law exactly the quotient
relation used by `Sym`. -/
noncomputable def symIndexOfFun (n : ℕ) (p : Fin n → κ) : Sym κ n :=
  Sym.symEquivSym'.symm (Quotient.mk' (List.Vector.ofFn p))

theorem symIndexOfFun_perm (n : ℕ) (e : Equiv.Perm (Fin n))
    (p : Fin n → κ) : symIndexOfFun n (p ∘ e) = symIndexOfFun n p := by
  apply Sym.symEquivSym'.injective
  change Quotient.mk' (List.Vector.ofFn (p ∘ e)) =
    Quotient.mk' (List.Vector.ofFn p)
  apply Quotient.sound
  show (List.Vector.ofFn (p ∘ e)).toList.Perm
    (List.Vector.ofFn p).toList
  rw [List.Vector.toList_ofFn, List.Vector.toList_ofFn]
  exact e.ofFn_comp_perm p

/-- Adding a first entry to a representative adds that entry to the
corresponding unordered tuple. -/
theorem symIndexOfFun_cons (n : ℕ) (a : κ) (p : Fin n → κ) :
    symIndexOfFun (n + 1) (Fin.cons a p) = a ::ₛ symIndexOfFun n p := by
  apply Sym.symEquivSym'.injective
  rw [← Sym.cons_equiv_eq_equiv_cons]
  change Quotient.mk' (List.Vector.ofFn (Fin.cons a p)) =
    Sym.cons' a (Quotient.mk' (List.Vector.ofFn p))
  congr 1

theorem mem_symIndexOfFun (n : ℕ) (p : Fin n → κ) (a : κ) :
    a ∈ symIndexOfFun n p ↔ ∃ i, p i = a := by
  induction p using Fin.consInduction with
  | elim0 =>
      have hnil : symIndexOfFun 0 (Fin.elim0 : Fin 0 → κ) = (Sym.nil : Sym κ 0) :=
        Subsingleton.elim _ _
      rw [hnil]
      simp
  | cons x p ih =>
      rw [symIndexOfFun_cons, Sym.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨i, hi⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨i.succ, hi⟩
      · rintro ⟨i, hi⟩
        induction i using Fin.cases with
        | zero => exact Or.inl hi.symm
        | succ j => exact Or.inr ⟨j, hi⟩

/-- A chosen ordered representative of an unordered tuple.  It is private:
all public statements are independent of this choice. -/
private noncomputable def symRepresentative (n : ℕ) (s : Sym κ n) : Fin n → κ :=
  (Quotient.out (Sym.symEquivSym' s)).get

private theorem symIndexOfFun_representative (n : ℕ) (s : Sym κ n) :
    symIndexOfFun n (symRepresentative n s) = s := by
  apply Sym.symEquivSym'.injective
  change Quotient.mk' (List.Vector.ofFn
      (Quotient.out (Sym.symEquivSym' s)).get) = Sym.symEquivSym' s
  rw [show List.Vector.ofFn (Quotient.out (Sym.symEquivSym' s)).get =
      Quotient.out (Sym.symEquivSym' s) by
    exact List.Vector.ofFn_get _]
  exact Quotient.out_eq _

private theorem natCard_fiber_eq_count [DecidableEq κ]
    (n : ℕ) (p : Fin n → κ) (a : κ) :
    Nat.card {i // p i = a} = List.count a (List.ofFn p) := by
  induction p using Fin.consInduction with
  | elim0 => simp
  | cons x p ih =>
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
        Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, List.ofFn_succ]
      rw [← Finset.card_filter, ← Fintype.card_subtype (fun i ↦ p i = a),
        ← Nat.card_eq_fintype_card, ih]
      by_cases h : x = a <;> simp [h, Nat.add_comm]

theorem exists_perm_of_symIndexOfFun_eq (n : ℕ) (p q : Fin n → κ)
    (h : symIndexOfFun n p = symIndexOfFun n q) :
    ∃ e : Equiv.Perm (Fin n), p = q ∘ e := by
  classical
  have hquot : Quotient.mk' (List.Vector.ofFn p) =
      Quotient.mk' (List.Vector.ofFn q) := by
    have hh := congrArg Sym.symEquivSym' h
    change Quotient.mk' (List.Vector.ofFn p) =
      Quotient.mk' (List.Vector.ofFn q) at hh
    exact hh
  have hpq : (List.ofFn p).Perm (List.ofFn q) := by
    have hv := Quotient.exact hquot
    change (List.isSetoid κ).r (List.Vector.ofFn p).val
      (List.Vector.ofFn q).val at hv
    unfold List.isSetoid at hv
    have hv' : List.Perm (List.Vector.ofFn p).toList
        (List.Vector.ofFn q).toList := hv
    simpa only [List.Vector.toList_ofFn] using hv'
  have hc (a : κ) : Nat.card {i // p i = a} = Nat.card {i // q i = a} := by
    rw [natCard_fiber_eq_count, natCard_fiber_eq_count]
    exact hpq.count_eq a
  let fp (a : κ) : Fintype {i // p i = a} := Fintype.ofFinite _
  let fq (a : κ) : Fintype {i // q i = a} := Fintype.ofFinite _
  let fe (a : κ) : {i // p i = a} ≃ {i // q i = a} :=
    @Fintype.equivOfCardEq _ _ (fp a) (fq a)
      (by simpa [Nat.card_eq_fintype_card] using hc a)
  let e : Equiv.Perm (Fin n) :=
    (Equiv.sigmaFiberEquiv p).symm |>.trans
      ((Equiv.sigmaCongrRight fe).trans (Equiv.sigmaFiberEquiv q))
  refine ⟨e, ?_⟩
  funext i
  change p i = q (e i)
  exact ((fe (p i)) ((Equiv.sigmaFiberEquiv p).symm i).2).property.symm

private noncomputable def tensorBasis :
    (b : Module.Basis κ R₀ M₀) → (n : ℕ) →
    Module.Basis (Fin n → κ) R₀ (⨂[R₀] (_ : Fin n), M₀) :=
  fun b n ↦ Basis.piTensorProduct (fun _ ↦ b)

/-- Collapse ordered tensor-basis coordinates along permutation orbits. -/
private noncomputable def tensorOrbitCoords (b : Module.Basis κ R₀ M₀) (n : ℕ) :
    (⨂[R₀] (_ : Fin n), M₀) →ₗ[R₀] (Sym κ n →₀ R₀) :=
  (Finsupp.lmapDomain R₀ R₀ (symIndexOfFun n)).comp (tensorBasis b n).repr.toLinearMap

@[simp]
private theorem tensorOrbitCoords_basis (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (p : Fin n → κ) :
    tensorOrbitCoords b n (PiTensorProduct.tprod R₀ (b ∘ p)) =
      Finsupp.single (symIndexOfFun n p) 1 := by
  rw [tensorOrbitCoords, LinearMap.comp_apply]
  rw [show PiTensorProduct.tprod R₀ (b ∘ p) = tensorBasis b n p by
    simp [tensorBasis, Function.comp_def]]
  simp

private theorem tensorOrbitCoords_perm (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (e : Equiv.Perm (Fin n))
    (x : Fin n → M₀) :
    tensorOrbitCoords b n (PiTensorProduct.tprod R₀ (x ∘ e)) =
      tensorOrbitCoords b n (PiTensorProduct.tprod R₀ x) := by
  let re : (⨂[R₀] (_ : Fin n), M₀) ≃ₗ[R₀] (⨂[R₀] (_ : Fin n), M₀) :=
    PiTensorProduct.reindex R₀ (fun _ : Fin n ↦ M₀) e.symm
  have hre : (tensorOrbitCoords b n).comp re.toLinearMap = tensorOrbitCoords b n := by
    apply (tensorBasis b n).ext
    intro p
    rw [LinearMap.comp_apply]
    rw [show tensorBasis b n p = PiTensorProduct.tprod R₀ (b ∘ p) by
      simp [tensorBasis, Function.comp_def]]
    have hrep : re.toLinearMap (PiTensorProduct.tprod R₀ (b ∘ p)) =
        PiTensorProduct.tprod R₀ (b ∘ (p ∘ e)) := by
      change re (PiTensorProduct.tprod R₀ (b ∘ p)) = _
      dsimp [re]
      rw [PiTensorProduct.reindex_tprod]
      rfl
    rw [hrep]
    rw [tensorOrbitCoords_basis, tensorOrbitCoords_basis]
    congr 1
    exact symIndexOfFun_perm n e p
  calc
    tensorOrbitCoords b n (PiTensorProduct.tprod R₀ (x ∘ e)) =
        tensorOrbitCoords b n (re (PiTensorProduct.tprod R₀ x)) := by
          congr 1
          dsimp [re]
          rw [PiTensorProduct.reindex_tprod]
          rfl
    _ = tensorOrbitCoords b n (PiTensorProduct.tprod R₀ x) :=
      LinearMap.congr_fun hre (PiTensorProduct.tprod R₀ x)

private theorem tensorOrbitCoords_symmetric (b : Module.Basis κ R₀ M₀) (n : ℕ) :
    IsSymmetric ((tensorOrbitCoords b n).compMultilinearMap
      (PiTensorProduct.tprod R₀)) := by
  intro e x
  simpa using tensorOrbitCoords_perm b n e x

/-- Coordinates of a symmetric tensor in the monomial basis. -/
noncomputable def monomialRepr (b : Module.Basis κ R₀ M₀) (n : ℕ) :
    Sym[R₀] (Fin n) M₀ →ₗ[R₀] (Sym κ n →₀ R₀) :=
  lift ((tensorOrbitCoords b n).compMultilinearMap
    (PiTensorProduct.tprod R₀)) (tensorOrbitCoords_symmetric b n)

@[simp]
theorem monomialRepr_tprod (b : Module.Basis κ R₀ M₀) (n : ℕ) (x : Fin n → M₀) :
    monomialRepr b n (tprod R₀ x) =
      tensorOrbitCoords b n (PiTensorProduct.tprod R₀ x) := by
  simp [monomialRepr]

@[simp]
theorem monomialRepr_tprod_basis (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (p : Fin n → κ) :
    monomialRepr b n (tprod R₀ (b ∘ p)) =
      Finsupp.single (symIndexOfFun n p) 1 := by
  rw [monomialRepr_tprod, tensorOrbitCoords_basis]

/-- The symmetric monomial belonging to an unordered tuple. -/
noncomputable def monomial (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (s : Sym κ n) : Sym[R₀] (Fin n) M₀ :=
  tprod R₀ (b ∘ symRepresentative n s)

private noncomputable def monomialOfFinsupp (b : Module.Basis κ R₀ M₀) (n : ℕ) :
    (Sym κ n →₀ R₀) →ₗ[R₀] Sym[R₀] (Fin n) M₀ :=
  Finsupp.linearCombination R₀ (monomial b n)

@[simp]
private theorem monomialOfFinsupp_single (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (s : Sym κ n) (r : R₀) :
    monomialOfFinsupp b n (Finsupp.single s r) = r • monomial b n s := by
  simp [monomialOfFinsupp]

private theorem monomialRepr_monomial (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (s : Sym κ n) :
    monomialRepr b n (monomial b n s) = Finsupp.single s 1 := by
  rw [monomial, monomialRepr_tprod, tensorOrbitCoords_basis,
    symIndexOfFun_representative]

private theorem monomialRepr_monomialOfFinsupp (b : Module.Basis κ R₀ M₀) (n : ℕ) :
    (monomialRepr b n).comp (monomialOfFinsupp b n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s r
  simp [monomialRepr_monomial]

private theorem tprod_eq_of_symIndexOfFun_eq (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (p q : Fin n → κ) (h : symIndexOfFun n p = symIndexOfFun n q) :
    tprod R₀ (b ∘ p) = tprod R₀ (b ∘ q) := by
  obtain ⟨e, he⟩ := exists_perm_of_symIndexOfFun_eq n p q h
  rw [he]
  change tprod R₀ ((b ∘ q) ∘ e) = tprod R₀ (b ∘ q)
  exact tprod_equiv e (b ∘ q)

private theorem monomialOfFinsupp_monomialRepr
    (b : Module.Basis κ R₀ M₀) (n : ℕ) :
    (monomialOfFinsupp b n).comp (monomialRepr b n) = LinearMap.id := by
  have hTensor : (monomialOfFinsupp b n).comp (tensorOrbitCoords b n) =
      (mk R₀ (Fin n) M₀) := by
    apply (tensorBasis b n).ext
    intro p
    rw [LinearMap.comp_apply]
    rw [show tensorBasis b n p = PiTensorProduct.tprod R₀ (b ∘ p) by
      simp [tensorBasis, Function.comp_def]]
    rw [tensorOrbitCoords_basis, monomialOfFinsupp_single, one_smul]
    change monomial b n (symIndexOfFun n p) = tprod R₀ (b ∘ p)
    rw [monomial]
    apply tprod_eq_of_symIndexOfFun_eq b n
    exact symIndexOfFun_representative n (symIndexOfFun n p)
  apply linearMap_ext
  intro x
  rw [LinearMap.comp_apply, monomialRepr_tprod]
  have hx := LinearMap.congr_fun hTensor (PiTensorProduct.tprod R₀ x)
  simpa [LinearMap.comp_apply, tprod] using hx

/-- The coordinate equivalence which identifies the genuine quotient
`Sym[R]^n M` with the free module on unordered degree-`n` monomials. -/
noncomputable def monomialLinearEquiv (b : Module.Basis κ R₀ M₀) (n : ℕ) :
    Sym[R₀] (Fin n) M₀ ≃ₗ[R₀] (Sym κ n →₀ R₀) where
  toLinearMap := monomialRepr b n
  invFun := monomialOfFinsupp b n
  left_inv x := by
    have h := LinearMap.congr_fun (monomialOfFinsupp_monomialRepr b n) x
    simpa [LinearMap.comp_apply] using h
  right_inv x := by
    have h := LinearMap.congr_fun (monomialRepr_monomialOfFinsupp b n) x
    simpa [LinearMap.comp_apply] using h

/-- The monomial basis of a symmetric tensor power. -/
noncomputable def monomialBasis (b : Module.Basis κ R₀ M₀) (n : ℕ) :
    Module.Basis (Sym κ n) R₀ (Sym[R₀] (Fin n) M₀) :=
  Finsupp.basisSingleOne.map (monomialLinearEquiv b n).symm

@[simp]
theorem monomialBasis_apply (b : Module.Basis κ R₀ M₀) (n : ℕ) (s : Sym κ n) :
    monomialBasis b n s = monomial b n s := by
  apply (monomialLinearEquiv b n).injective
  simp [monomialBasis, monomialLinearEquiv, monomialRepr_monomial]

/-- A linear map kills a monomial if it kills one basis factor occurring in
that monomial. -/
theorem map_monomialBasis_eq_zero_of_mem (b : Module.Basis κ R₀ M₀) (n : ℕ)
    {N₀ : Type*} [AddCommMonoid N₀] [Module R₀ N₀]
    (f : M₀ →ₗ[R₀] N₀) (s : Sym κ n) (a : κ) (ha : a ∈ s)
    (hfa : f (b a) = 0) :
    map (R := R₀) (ι := Fin n) f (monomialBasis b n s) = 0 := by
  rw [monomialBasis_apply, monomial, map_tprod]
  have har : a ∈ symIndexOfFun n (symRepresentative n s) := by
    simpa [symIndexOfFun_representative]
  obtain ⟨i, hi⟩ := (mem_symIndexOfFun n (symRepresentative n s) a).mp har
  apply MultilinearMap.map_coord_zero _ i
  change f (b (symRepresentative n s i)) = 0
  rw [hi, hfa]

/-- A linear map fixes a monomial when it fixes every basis factor occurring
in that monomial. -/
theorem map_monomialBasis_eq_self_of_mem (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (f : M₀ →ₗ[R₀] M₀) (s : Sym κ n)
    (hf : ∀ a ∈ s, f (b a) = b a) :
    map (R := R₀) (ι := Fin n) f (monomialBasis b n s) =
      monomialBasis b n s := by
  rw [monomialBasis_apply, monomial, map_tprod]
  congr 1
  funext i
  apply hf
  have hi : symRepresentative n s i ∈
      symIndexOfFun n (symRepresentative n s) :=
    (mem_symIndexOfFun n (symRepresentative n s) _).mpr ⟨i, rfl⟩
  simpa only [symIndexOfFun_representative] using hi

@[simp]
theorem monomialBasis_zero_nil (b : Module.Basis κ R₀ M₀) :
    monomialBasis b 0 Sym.nil =
      tprod R₀ (fun i : Fin 0 => Fin.elim0 i) := by
  rw [monomialBasis_apply]
  unfold monomial
  apply congrArg (tprod R₀)
  funext i
  exact Fin.elim0 i

/-- The zeroth symmetric power is the coefficient ring. -/
noncomputable def degreeZeroLinearEquiv (b : Module.Basis κ R₀ M₀) :
    Sym[R₀] (Fin 0) M₀ ≃ₗ[R₀] R₀ :=
  (monomialLinearEquiv b 0).trans
    ((Finsupp.linearEquivFunOnFinite R₀ R₀ (Sym κ 0)).trans
      (LinearEquiv.funUnique (Sym κ 0) R₀ R₀))

@[simp]
theorem degreeZeroLinearEquiv_monomialBasis (b : Module.Basis κ R₀ M₀) :
    degreeZeroLinearEquiv b (monomialBasis b 0 Sym.nil) = 1 := by
  change ((Finsupp.linearEquivFunOnFinite R₀ R₀ (Sym κ 0)).trans
      (LinearEquiv.funUnique (Sym κ 0) R₀ R₀))
      ((monomialLinearEquiv b 0) (monomialBasis b 0 Sym.nil)) = 1
  rw [show (monomialLinearEquiv b 0) (monomialBasis b 0 Sym.nil) =
      Finsupp.single Sym.nil 1 by
    rw [monomialBasis_apply]
    exact monomialRepr_monomial b 0 Sym.nil]
  have hdef : (default : Sym κ 0) = Sym.nil := Subsingleton.elim _ _
  change (Finsupp.single Sym.nil (1 : R₀) : Sym κ 0 →₀ R₀)
      (default : Sym κ 0) = 1
  convert Finsupp.single_eq_same using 1 <;> exact Subsingleton.elim _ _

/-- The first symmetric power, in the monomial coordinates determined by a
basis, is the original module.  This is the coordinate form needed to identify
the weight-zero Koszul differential with the presentation injection. -/
noncomputable def degreeOneLinearEquiv (b : Module.Basis κ R₀ M₀) :
    Sym[R₀] (Fin 1) M₀ ≃ₗ[R₀] M₀ :=
  (monomialLinearEquiv b 1).trans
    ((Finsupp.lcongr (Sym.oneEquiv.symm : Sym κ 1 ≃ κ)
      (LinearEquiv.refl R₀ R₀)).trans b.repr.symm)

@[simp]
theorem degreeOneLinearEquiv_monomialBasis (b : Module.Basis κ R₀ M₀)
    (a : κ) :
    degreeOneLinearEquiv b (monomialBasis b 1 (Sym.oneEquiv a)) = b a := by
  change b.repr.symm
      (Finsupp.lcongr (Sym.oneEquiv.symm : Sym κ 1 ≃ κ)
        (LinearEquiv.refl R₀ R₀)
        (monomialLinearEquiv b 1 (monomialBasis b 1 (Sym.oneEquiv a)))) = b a
  rw [monomialBasis_apply]
  change b.repr.symm
      (Finsupp.lcongr (Sym.oneEquiv.symm : Sym κ 1 ≃ κ)
        (LinearEquiv.refl R₀ R₀)
        (monomialRepr b 1 (monomial b 1 (Sym.oneEquiv a)))) = b a
  rw [monomialRepr_monomial, Finsupp.lcongr_single]
  exact congrArg b (Sym.oneEquiv.symm_apply_apply a)

/-- Inserting a basis vector into a monomial adds its index to the unordered
tuple.  This is the coordinate rule used by the fixed-exponent contractions
and by the metabelian Hall normalizer. -/
@[simp]
theorem insert_monomialBasis (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (a : κ) (s : Sym κ n) :
    insert R₀ M₀ n (b a) (monomialBasis b n s) =
      monomialBasis b (n + 1) (a ::ₛ s) := by
  rw [monomialBasis_apply, monomialBasis_apply, monomial, monomial,
    insert_tprod]
  have hp : Fin.cons (b a) (b ∘ symRepresentative n s) =
      b ∘ Fin.cons a (symRepresentative n s) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hp]
  apply tprod_eq_of_symIndexOfFun_eq b (n + 1)
  rw [symIndexOfFun_cons, symIndexOfFun_representative,
    symIndexOfFun_representative]

/-- Every positive-degree symmetric basis monomial is obtained by inserting
one basis vector into a monomial of the preceding degree. -/
theorem monomialBasis_succ_exists (b : Module.Basis κ R₀ M₀) (n : ℕ)
    (s : Sym κ (n + 1)) :
    ∃ (a : κ) (t : Sym κ n),
      monomialBasis b (n + 1) s =
        insert R₀ M₀ n (b a) (monomialBasis b n t) := by
  obtain ⟨a, t, hst⟩ := Sym.exists_eq_cons_of_succ s
  refine ⟨a, t, ?_⟩
  rw [insert_monomialBasis, hst]

/-- Exponent vectors of total degree `n`, the coordinate notation used in the
stabilization calculation. -/
abbrev ExponentIndex (κ : Type x) (n : ℕ) :=
  {e : κ →₀ ℕ // e.sum (fun _ k ↦ k) = n}

/-- The monomial basis reindexed by exponent vectors. -/
noncomputable def exponentBasis (b : Module.Basis κ R₀ M₀) (n : ℕ) :
    Module.Basis (ExponentIndex κ n) R₀ (Sym[R₀] (Fin n) M₀) := by
  letI := Classical.decEq κ
  exact (monomialBasis b n).reindex (Sym.equivNatSum κ n)

end Basis

section QuadraticExactSequence

variable {R : Type} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

private def emptyFun : Fin 0 → M := fun i => nomatch i

def degreeOne : M →ₗ[R] Sym[R] (Fin 1) M where
  toFun x := tprod R (Fin.cons x emptyFun)
  map_add' x y := by
    exact (tprod R).cons_add emptyFun x y
  map_smul' r x := by
    exact (tprod R).cons_smul emptyFun r x

@[simp] theorem degreeOne_apply (x : M) :
    degreeOne (R := R) x = tprod R (Fin.cons x emptyFun) := rfl

@[simp] theorem map_degreeOne {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (x : M) :
    map (R := R) (ι := Fin 1) f (degreeOne (R := R) x) =
      degreeOne (R := R) (f x) := by
  rw [degreeOne_apply, map_tprod, degreeOne_apply]
  congr 1
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i

@[simp]
theorem insert_monomialBasis_zero {R₀ : Type} [CommRing R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    {κ : Type x} [Finite κ] (b : Module.Basis κ R₀ M₀) (x : M₀) :
    insert R₀ M₀ 0 x (monomialBasis b 0 Sym.nil) =
      degreeOne (R := R₀) x := by
  rw [monomialBasis_zero_nil, degreeOne_apply, insert_tprod]
  congr 1
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i

/-- The coordinate equivalence in degree one is inverse to the canonical
degree-one pure-tensor map. -/
@[simp]
theorem degreeOneLinearEquiv_degreeOne {R₀ : Type} [CommRing R₀]
    {M₀ : Type v} [AddCommGroup M₀] [Module R₀ M₀]
    {κ : Type x} [Finite κ] (b : Module.Basis κ R₀ M₀) (x : M₀) :
    degreeOneLinearEquiv b (degreeOne (R := R₀) x) = x := by
  let f : M₀ →ₗ[R₀] M₀ :=
    (degreeOneLinearEquiv b).toLinearMap.comp
      (degreeOne (R := R₀) (M := M₀))
  change f x = (LinearMap.id (R := R₀) (M := M₀)) x
  have hf : f = LinearMap.id (R := R₀) (M := M₀) := by
    apply b.ext
    intro a
    change degreeOneLinearEquiv b (degreeOne (R := R₀) (b a)) = b a
    rw [← insert_monomialBasis_zero b, insert_monomialBasis]
    apply degreeOneLinearEquiv_monomialBasis
  exact LinearMap.congr_fun hf x

private def tensorToSymTwoBilinear : M →ₗ[R] M →ₗ[R] Sym[R] (Fin 2) M where
  toFun x := (insert R M 1 x).comp degreeOne
  map_add' x y := by
    ext z
    simp only [LinearMap.add_apply, LinearMap.comp_apply, degreeOne_apply,
      insert_tprod]
    exact (tprod R).cons_add (Fin.cons z emptyFun) x y
  map_smul' r x := by
    ext z
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, degreeOne_apply,
      insert_tprod, RingHom.id_apply]
    exact (tprod R).cons_smul (Fin.cons z emptyFun) r x

def tensorToSymTwo : M ⊗[R] M →ₗ[R] Sym[R] (Fin 2) M :=
  TensorProduct.lift tensorToSymTwoBilinear

@[simp] theorem tensorToSymTwo_tmul (x y : M) :
    tensorToSymTwo (R := R) (x ⊗ₜ[R] y) =
      tprod R (Fin.cons x (Fin.cons y emptyFun)) := by
  rw [tensorToSymTwo, TensorProduct.lift.tmul]
  change insert R M 1 x (degreeOne (R := R) y) = _
  rw [degreeOne_apply, insert_tprod]

private def antisymTail : M →ₗ[R] M [⋀^Fin 1]→ₗ[R] M ⊗[R] M where
  toFun x := AlternatingMap.ofSubsingleton R M (M ⊗[R] M) 0
    (TensorProduct.mk R M M x)
  map_add' x y := by ext v; simp [add_tmul]
  map_smul' r x := by ext v; simp [smul_tmul']

private def antisymAlternating : M [⋀^Fin 2]→ₗ[R] M ⊗[R] M :=
  AlternatingMap.alternatizeUncurryFin antisymTail

def exteriorTwoToTensor : (⋀[R]^2 M) →ₗ[R] M ⊗[R] M :=
  exteriorPower.alternatingMapLinearEquiv
    (antisymAlternating (R := R) (M := M))

@[simp] theorem exteriorTwoToTensor_ιMulti (x : Fin 2 → M) :
    exteriorTwoToTensor (R := R) (exteriorPower.ιMulti R 2 x) =
      x 0 ⊗ₜ[R] x 1 - x 1 ⊗ₜ[R] x 0 := by
  change (exteriorPower.alternatingMapLinearEquiv
    (antisymAlternating (R := R) (M := M)))
      (exteriorPower.ιMulti R 2 x) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simp [antisymAlternating, AlternatingMap.alternatizeUncurryFin_apply,
    antisymTail]
  change x 0 ⊗ₜ[R] x 1 + -(x 1 ⊗ₜ[R] x 0) = _
  abel

theorem tensorToSymTwo_comp_exteriorTwoToTensor :
    (tensorToSymTwo (R := R) (M := M)).comp
      (exteriorTwoToTensor (R := R) (M := M)) = 0 := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R 2 M)
  rintro _ ⟨x, rfl⟩
  simp only [LinearMap.comp_apply, exteriorTwoToTensor_ιMulti, map_sub,
    tensorToSymTwo_tmul]
  rw [show tprod R (Fin.cons (x 0) (Fin.cons (x 1) emptyFun)) =
      tprod R (Fin.cons (x 1) (Fin.cons (x 0) emptyFun)) by
    let p : Equiv.Perm (Fin 2) := Equiv.swap 0 1
    have hp : Fin.cons (x 0) (Fin.cons (x 1) emptyFun) =
        Fin.cons (x 1) (Fin.cons (x 0) emptyFun) ∘ p := by
      funext i
      fin_cases i <;> rfl
    rw [hp]
    exact tprod_equiv (R := R) (M := M) p _]
  exact sub_self _

section Exact

variable {κ : Type x} [Finite κ] [LinearOrder κ]

private def pairFun (i j : κ) : Fin 2 → κ :=
  Fin.cons i (Fin.cons j emptyFun)

private theorem symIndex_pair_eq_iff (i j k l : κ) :
    symIndexOfFun 2 (pairFun i j) = symIndexOfFun 2 (pairFun k l) ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := exists_perm_of_symIndexOfFun_eq 2 (pairFun i j) (pairFun k l) h
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    by_cases he0 : e 0 = 0
    · left
      constructor
      · simpa [pairFun, he0] using h0
      · have he1 : e 1 = 1 := by
          apply Fin.eq_one_of_ne_zero (e 1)
          intro hz
          have hz' : (0 : Fin 2) = 1 := e.injective (he0.trans hz.symm)
          omega
        simpa [pairFun, he1] using h1
    · have he0' : e 0 = 1 := Fin.eq_one_of_ne_zero (e 0) he0
      right
      constructor
      · simpa [pairFun, he0'] using h0
      · have he1 : e 1 = 0 := by
          by_contra hz
          have he1' : e 1 = 1 := Fin.eq_one_of_ne_zero (e 1) hz
          have hz' : (0 : Fin 2) = 1 := e.injective (he0'.trans he1'.symm)
          omega
        simpa [pairFun, he1] using h1
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simpa [pairFun, Function.comp_def] using
        (symIndexOfFun_perm 2 (Equiv.swap 0 1) (pairFun j i))

/-- Equality of unordered pairs in the degree-two symmetric index. -/
theorem pairSym_eq_pairSym_iff (i j k l : κ) :
    Sym.cons i (Sym.cons j Sym.nil) = Sym.cons k (Sym.cons l Sym.nil) ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hij : symIndexOfFun 2 (pairFun i j) = Sym.cons i (Sym.cons j Sym.nil) := by
    rw [pairFun, symIndexOfFun_cons, symIndexOfFun_cons]
    exact congrArg (Sym.cons i ∘ Sym.cons j) (Subsingleton.elim _ _)
  have hkl : symIndexOfFun 2 (pairFun k l) = Sym.cons k (Sym.cons l Sym.nil) := by
    rw [pairFun, symIndexOfFun_cons, symIndexOfFun_cons]
    exact congrArg (Sym.cons k ∘ Sym.cons l) (Subsingleton.elim _ _)
  rw [← hij, ← hkl]
  exact symIndex_pair_eq_iff i j k l

private def orderedWedge (b : Module.Basis κ R M) (ij : κ × κ) :
    ⋀[R]^2 M :=
  if hij : ij.1 < ij.2 then
    exteriorPower.ιMulti R 2 (Fin.cons (b ij.1) (Fin.cons (b ij.2) emptyFun))
  else 0

def exteriorTwoLeftInverse (b : Module.Basis κ R M) :
    M ⊗[R] M →ₗ[R] ⋀[R]^2 M :=
  ((b.tensorProduct b).constr R) (orderedWedge b)

@[simp] private theorem exteriorTwoLeftInverse_basis_tmul
    (b : Module.Basis κ R M) (i j : κ) :
    exteriorTwoLeftInverse b (b i ⊗ₜ[R] b j) =
      if hij : i < j then
        exteriorPower.ιMulti R 2
          (Fin.cons (b i) (Fin.cons (b j) emptyFun))
      else 0 := by
  rw [← Module.Basis.tensorProduct_apply' b b (i, j)]
  rw [exteriorTwoLeftInverse, Module.Basis.constr_basis]
  rfl

theorem exteriorTwoLeftInverse_comp (b : Module.Basis κ R M) :
    (exteriorTwoLeftInverse b).comp
      (exteriorTwoToTensor (R := R) (M := M)) = LinearMap.id := by
  apply (b.exteriorPower 2).ext
  intro s
  rw [exteriorPower.basis_apply]
  let p : Fin 2 → κ := s.val.orderEmbOfFin s.property
  change exteriorTwoLeftInverse b
    (exteriorTwoToTensor (R := R) (M := M)
      (exteriorPower.ιMulti R 2 (b ∘ p))) = _
  rw [exteriorTwoToTensor_ιMulti, map_sub,
    show (b ∘ p) 0 = b (p 0) by rfl,
    show (b ∘ p) 1 = b (p 1) by rfl,
    exteriorTwoLeftInverse_basis_tmul, exteriorTwoLeftInverse_basis_tmul]
  have hp : p 0 < p 1 := by
    exact s.val.orderEmbOfFin s.property |>.strictMono (by decide)
  simp only [hp, ↓reduceDIte, LinearMap.id_apply]
  have hnp : ¬p 1 < p 0 := not_lt_of_ge hp.le
  simp only [hnp, ↓reduceDIte, sub_zero]
  rfl

theorem exteriorTwoToTensor_injective (b : Module.Basis κ R M) :
    Function.Injective (exteriorTwoToTensor (R := R) (M := M)) := by
  intro x y hxy
  have := congrArg (exteriorTwoLeftInverse b) hxy
  simpa [← LinearMap.comp_apply, exteriorTwoLeftInverse_comp b] using this

private def tensorCoord (b : Module.Basis κ R M) (i j : κ) :
    M ⊗[R] M →ₗ[R] R :=
  (b.tensorProduct b).coord (i, j)

private def symCoord (b : Module.Basis κ R M) (i j : κ) :
    Sym[R] (Fin 2) M →ₗ[R] R :=
  (monomialBasis b 2).coord (symIndexOfFun 2 (pairFun i j))

private theorem symCoord_tensor_basis (b : Module.Basis κ R M)
    (i j k l : κ) :
    symCoord b i j (tensorToSymTwo (R := R) (b k ⊗ₜ[R] b l)) =
      if symIndexOfFun 2 (pairFun k l) = symIndexOfFun 2 (pairFun i j)
      then 1 else 0 := by
  rw [tensorToSymTwo_tmul]
  rw [symCoord, Module.Basis.coord_apply, monomialBasis,
    Module.Basis.map_repr]
  simp only [LinearEquiv.symm_symm, Finsupp.basisSingleOne_repr,
    LinearEquiv.trans_apply, LinearEquiv.refl_apply]
  change (monomialRepr b 2
    (tprod R (Fin.cons (b k) (Fin.cons (b l) emptyFun))))
      (symIndexOfFun 2 (pairFun i j)) = _
  rw [show Fin.cons (b k) (Fin.cons (b l) emptyFun) = b ∘ pairFun k l by
    funext x
    fin_cases x <;> rfl]
  rw [monomialRepr_tprod_basis]
  by_cases h : symIndexOfFun 2 (pairFun k l) =
      symIndexOfFun 2 (pairFun i j)
  · rw [if_pos h]
    rw [← h]
    exact Finsupp.single_eq_same (M := R)
  · rw [if_neg h]
    exact Finsupp.single_eq_of_ne (M := R) (fun h' => h h'.symm)

private theorem offDiagonal_coord_identity (b : Module.Basis κ R M)
    (i j : κ) (hij : i < j) :
    (symCoord b i j).comp (tensorToSymTwo (R := R) (M := M)) =
      tensorCoord b i j + tensorCoord b j i := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, symCoord_tensor_basis,
    LinearMap.add_apply, tensorCoord, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  simp only [symIndex_pair_eq_iff]
  rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
    exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hki : k = i <;> by_cases hlj : l = j <;>
    by_cases hkj : k = j <;> by_cases hli : l = i <;>
    simp [hki, hlj, hkj, hli, hij.ne, hij.ne']

private theorem diagonal_coord_identity (b : Module.Basis κ R M) (i : κ) :
    (symCoord b i i).comp (tensorToSymTwo (R := R) (M := M)) =
      tensorCoord b i i := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, symCoord_tensor_basis, tensorCoord,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [symIndex_pair_eq_iff]
  rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
    exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hki : k = i <;> by_cases hli : l = i <;> simp [hki, hli]

private def tensorNormalization (b : Module.Basis κ R M) :
    M ⊗[R] M →ₗ[R] M ⊗[R] M :=
  (exteriorTwoToTensor (R := R) (M := M)).comp (exteriorTwoLeftInverse b)

@[simp] private theorem tensorNormalization_basis_tmul
    (b : Module.Basis κ R M) (i j : κ) :
    tensorNormalization b (b i ⊗ₜ[R] b j) =
      if hij : i < j then b i ⊗ₜ[R] b j - b j ⊗ₜ[R] b i else 0 := by
  rw [tensorNormalization, LinearMap.comp_apply, exteriorTwoLeftInverse_basis_tmul]
  split_ifs with hij
  · rw [exteriorTwoToTensor_ιMulti]
    rfl
  · rw [map_zero]

private theorem tensorNormalization_coord_lt (b : Module.Basis κ R M)
    (i j : κ) (hij : i < j) :
    (tensorCoord b i j).comp (tensorNormalization b) = tensorCoord b i j := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, tensorNormalization_basis_tmul]
  split_ifs with hkl
  · simp only [tensorCoord, Module.Basis.coord_apply, map_sub]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm,
      show b l ⊗ₜ[R] b k = (b.tensorProduct b) (l, k) by
      exact (Module.Basis.tensorProduct_apply' b b (l, k)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hki : k = i <;> by_cases hlj : l = j <;>
      by_cases hli : l = i <;> by_cases hkj : k = j <;>
      simp [hki, hlj, hli, hkj] <;> order
  · simp only [tensorCoord, Module.Basis.coord_apply, map_zero]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hki : k = i <;> by_cases hlj : l = j <;>
      simp [hki, hlj] <;> order

private theorem tensorNormalization_coord_gt (b : Module.Basis κ R M)
    (i j : κ) (hji : j < i) :
    (tensorCoord b i j).comp (tensorNormalization b) =
      -(tensorCoord b j i) := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, tensorNormalization_basis_tmul]
  split_ifs with hkl
  · simp only [tensorCoord, Module.Basis.coord_apply, map_sub,
      LinearMap.neg_apply]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm,
      show b l ⊗ₜ[R] b k = (b.tensorProduct b) (l, k) by
      exact (Module.Basis.tensorProduct_apply' b b (l, k)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hki : k = i <;> by_cases hlj : l = j <;>
      by_cases hli : l = i <;> by_cases hkj : k = j <;>
      simp [hki, hlj, hli, hkj] <;> order
  · simp only [tensorCoord, Module.Basis.coord_apply, map_zero,
      LinearMap.neg_apply]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hkj : k = j <;> by_cases hli : l = i <;>
      simp [hkj, hli] <;> order

private theorem tensorNormalization_coord_diag (b : Module.Basis κ R M) (i : κ) :
    (tensorCoord b i i).comp (tensorNormalization b) = 0 := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, tensorNormalization_basis_tmul]
  split_ifs with hkl
  · simp only [tensorCoord, Module.Basis.coord_apply, map_sub]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm,
      show b l ⊗ₜ[R] b k = (b.tensorProduct b) (l, k) by
      exact (Module.Basis.tensorProduct_apply' b b (l, k)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hki : k = i <;> by_cases hli : l = i <;>
      simp [hki, hli] <;> order
  · simp

private theorem tensorNormalization_eq_of_mem_ker (b : Module.Basis κ R M)
    (x : M ⊗[R] M) (hx : x ∈ LinearMap.ker (tensorToSymTwo (R := R) (M := M))) :
    tensorNormalization b x = x := by
  have hx0 : tensorToSymTwo (R := R) (M := M) x = 0 := hx
  have hoff (i j : κ) (hij : i < j) :
      tensorCoord b i j x + tensorCoord b j i x = 0 := by
    have h := LinearMap.congr_fun (offDiagonal_coord_identity b i j hij) x
    rw [LinearMap.comp_apply, hx0, map_zero] at h
    exact h.symm
  have hdiag (i : κ) : tensorCoord b i i x = 0 := by
    have h := LinearMap.congr_fun (diagonal_coord_identity b i) x
    rw [LinearMap.comp_apply, hx0, map_zero] at h
    exact h.symm
  apply (b.tensorProduct b).repr.injective
  ext ij
  rcases ij with ⟨i, j⟩
  change tensorCoord b i j (tensorNormalization b x) = tensorCoord b i j x
  rcases lt_trichotomy i j with hij | hij | hij
  · have h := LinearMap.congr_fun (tensorNormalization_coord_lt b i j hij) x
    exact h
  · subst j
    have h := LinearMap.congr_fun (tensorNormalization_coord_diag b i) x
    rw [LinearMap.comp_apply] at h
    have h' : tensorCoord b i i (tensorNormalization b x) = 0 := by
      simpa using h
    rw [h', hdiag]
  · have h := LinearMap.congr_fun (tensorNormalization_coord_gt b i j hij) x
    rw [LinearMap.comp_apply, LinearMap.neg_apply] at h
    rw [h]
    have hs := hoff j i hij
    exact neg_eq_of_add_eq_zero_right hs

theorem exteriorTwoToTensor_range_eq_ker (b : Module.Basis κ R M) :
    LinearMap.range (exteriorTwoToTensor (R := R) (M := M)) =
      LinearMap.ker (tensorToSymTwo (R := R) (M := M)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change tensorToSymTwo (R := R) (M := M)
      (exteriorTwoToTensor (R := R) (M := M) y) = 0
    exact LinearMap.congr_fun tensorToSymTwo_comp_exteriorTwoToTensor y
  · intro hx
    refine ⟨exteriorTwoLeftInverse b x, ?_⟩
    exact tensorNormalization_eq_of_mem_ker b x hx

end Exact


end QuadraticExactSequence

end

end SymmetricPower
