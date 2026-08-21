import LieRings.DimensionSubring.DegreeFive.LowWeight

/-!
# Finite word expansions in a free associative algebra
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u)

/-- A word in the generators of the free associative algebra. -/
def freeAlgebraWord (xs : List X) : FreeAlgebra ℤ X :=
  (xs.map (FreeAlgebra.ι ℤ)).prod

@[simp]
theorem freeAlgebraWord_nil : freeAlgebraWord X [] = 1 :=
  rfl

@[simp]
theorem freeAlgebraWord_cons (x : X) (xs : List X) :
    freeAlgebraWord X (x :: xs) =
      FreeAlgebra.ι ℤ x * freeAlgebraWord X xs :=
  rfl

@[simp]
theorem freeAlgebraWord_append (xs ys : List X) :
    freeAlgebraWord X (xs ++ ys) =
      freeAlgebraWord X xs * freeAlgebraWord X ys := by
  simp [freeAlgebraWord, List.map_append]

/-- The monoid-basis vector corresponding to a word is its product of free generators. -/
theorem monoidBasisElement_eq_freeAlgebraWord (w : FreeMonoid X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (Finsupp.single w 1) =
      freeAlgebraWord X (FreeMonoid.toList w) := by
  induction w using FreeMonoid.recOn with
  | h0 =>
      simpa only [MonoidAlgebra.of_apply] using
        (map_one FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm)
  | ih x w ih =>
      rw [FreeMonoid.toList_mul, FreeMonoid.toList_of,
        freeAlgebraWord_append, freeAlgebraWord_cons, freeAlgebraWord_nil, mul_one]
      rw [← ih]
      have hsingle :
          (MonoidAlgebra.single (FreeMonoid.of x * w) (1 : ℤ) :
              MonoidAlgebra ℤ (FreeMonoid X)) =
            MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ) *
              MonoidAlgebra.single w (1 : ℤ) := by
        rw [MonoidAlgebra.single_mul_single]
        simp
      rw [show (Finsupp.single (FreeMonoid.of x * w) 1 :
          MonoidAlgebra ℤ (FreeMonoid X)) =
        MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ) *
          MonoidAlgebra.single w (1 : ℤ) from hsingle]
      rw [map_mul]
      congr 1
      simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
      exact one_nsmul (FreeAlgebra.ι ℤ x)

/-- Every free associative polynomial is a finite integral sum of generator words. -/
theorem exists_freeAlgebra_word_finsupp (p : FreeAlgebra ℤ X) :
    ∃ c : FreeMonoid X →₀ ℤ,
      c.sum (fun w n ↦ n • freeAlgebraWord X (FreeMonoid.toList w)) = p := by
  let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid p
  refine ⟨c, ?_⟩
  calc
    c.sum (fun w n ↦ n • freeAlgebraWord X (FreeMonoid.toList w)) =
        c.sum (fun w n ↦ n •
          FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (Finsupp.single w 1)) := by
            apply Finsupp.sum_congr
            intro w hw
            rw [monoidBasisElement_eq_freeAlgebraWord]
    _ = FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm c := by
      symm
      calc
        FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm c =
            FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
              (c.sum Finsupp.single) := by
          congr 1
          exact (Finsupp.sum_single c).symm
        _ = c.sum (fun w n ↦
              FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
                (Finsupp.single w n)) := by rw [map_finsuppSum]
        _ = c.sum (fun w n ↦ n •
              FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
                (Finsupp.single w 1)) := by
          apply Finsupp.sum_congr
          intro w hw
          rw [← map_smul]
          congr 1
          symm
          calc
            (c w) • (Finsupp.single w (1 : ℤ) :
                MonoidAlgebra ℤ (FreeMonoid X)) =
                Finsupp.single w ((c w) • (1 : ℤ)) :=
              Finsupp.smul_single (c w) w (1 : ℤ)
            _ = Finsupp.single w (c w) := by
              rw [smul_eq_mul, mul_one]
    _ = p := FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm_apply_apply p

end


end DegreeFive

end LieRings
