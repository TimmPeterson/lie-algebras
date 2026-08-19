import LieRings.Homological.Koszul

/-!
# The first derived functor of a symmetric power

This file first constructs the map on the elementwise degree-one Koszul
homology of a strict two-term presentation.  The canonical finite free
presentation then makes `L₁Sᵐ` an honest functor on finite additive groups.
-/

open TensorProduct

namespace Koszul

universe u v w z v₂ w₂ u₃ v₃ w₃

noncomputable section

namespace PresentationHomology

variable {A : Type u} {B : Type z} [AddCommGroup A] [AddCommGroup B]
variable (P : Presentation.{u, v, w} A) (Q : Presentation.{z, v₂, w₂} B)
variable {f : A →ₗ[ℤ] B} (F : Presentation.Hom P Q f)

/-- The map in degree one of a Koszul complex. -/
def oneMap (q : ℕ) : One P q →ₗ[ℤ] One Q q :=
  TensorProduct.map F.relMap
    (SymmetricPower.map (R := ℤ) (ι := Fin q) F.genMap)

/-- The map in degree two of a Koszul complex. -/
def twoMap (q : ℕ) : Two P q →ₗ[ℤ] Two Q q :=
  TensorProduct.map (exteriorPower.map 2 F.relMap)
    (SymmetricPower.map (R := ℤ) (ι := Fin q) F.genMap)

@[simp]
theorem oneMap_tmul (q : ℕ) (r : P.rel)
    (s : Sym[ℤ] (Fin q) P.gen) :
    oneMap P Q F q (r ⊗ₜ[ℤ] s) =
      F.relMap r ⊗ₜ[ℤ]
        SymmetricPower.map (R := ℤ) (ι := Fin q) F.genMap s := by
  change (TensorProduct.map F.relMap
      (SymmetricPower.map (R := ℤ) (ι := Fin q) F.genMap))
        (r ⊗ₜ[ℤ] s) = _
  rw [TensorProduct.map_tmul]

@[simp]
theorem twoMap_wedge_tmul (q : ℕ) (a : Fin 2 → P.rel)
    (s : Sym[ℤ] (Fin q) P.gen) :
    twoMap P Q F q (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s) =
      exteriorPower.ιMulti ℤ 2 (F.relMap ∘ a) ⊗ₜ[ℤ]
        SymmetricPower.map (R := ℤ) (ι := Fin q) F.genMap s := by
  change (TensorProduct.map (exteriorPower.map 2 F.relMap)
      (SymmetricPower.map (R := ℤ) (ι := Fin q) F.genMap))
        (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s) = _
  rw [TensorProduct.map_tmul, exteriorPower.map_apply_ιMulti]
  rfl

theorem dOne_natural (q : ℕ) :
    (dOne Q q).comp (oneMap P Q F q) =
      (SymmetricPower.map (R := ℤ) (ι := Fin (q + 1)) F.genMap).comp
        (dOne P q) := by
  apply TensorProduct.ext'
  intro r s
  change dOne Q q
      (F.relMap r ⊗ₜ[ℤ]
        SymmetricPower.map (R := ℤ) (ι := Fin q) F.genMap s) =
    SymmetricPower.map (R := ℤ) (ι := Fin (q + 1)) F.genMap
      (dOne P q (r ⊗ₜ[ℤ] s))
  rw [dOne_tmul, dOne_tmul]
  have hdr : Q.d (F.relMap r) = F.genMap (P.d r) :=
    LinearMap.congr_fun F.commutes r
  rw [hdr]
  exact LinearMap.congr_fun
    (SymmetricPower.map_insert (R₀ := ℤ) (M₀ := P.gen) (N₀ := Q.gen)
      F.genMap q (P.d r)) s |>.symm

theorem dTwo_natural (q : ℕ) :
    (dTwo Q q).comp (twoMap P Q F q) =
      (oneMap P Q F (q + 1)).comp (dTwo P q) := by
  apply TensorProduct.ext'
  intro w s
  let G : (⋀[ℤ]^2 P.rel) →ₗ[ℤ] One Q (q + 1) :=
    ((dTwo Q q).comp (twoMap P Q F q)).comp
      ((TensorProduct.mk ℤ (⋀[ℤ]^2 P.rel) _).flip s)
  have hG : G = ((oneMap P Q F (q + 1)).comp (dTwo P q)).comp
      ((TensorProduct.mk ℤ (⋀[ℤ]^2 P.rel) _).flip s) := by
    apply exteriorPower.linearMap_ext
    ext a
    have hmid : dTwo Q q
        (exteriorPower.ιMulti ℤ 2 (F.relMap ∘ a) ⊗ₜ[ℤ]
          SymmetricPower.map (R := ℤ) (ι := Fin q) F.genMap s) =
      oneMap P Q F (q + 1)
        (dTwo P q (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s)) := by
      rw [dTwo_wedge_tmul, dTwo_wedge_tmul, map_sub]
      simp only [oneMap_tmul]
      have hd0 : Q.d (F.relMap (a 0)) = F.genMap (P.d (a 0)) :=
        LinearMap.congr_fun F.commutes (a 0)
      have hd1 : Q.d (F.relMap (a 1)) = F.genMap (P.d (a 1)) :=
        LinearMap.congr_fun F.commutes (a 1)
      simp only [Function.comp_apply]
      rw [hd0, hd1]
      congr 1
      · apply congrArg (fun t ↦ F.relMap (a 0) ⊗ₜ[ℤ] t)
        exact LinearMap.congr_fun
          (SymmetricPower.map_insert (R₀ := ℤ) (M₀ := P.gen) (N₀ := Q.gen)
            F.genMap q (P.d (a 1))) s |>.symm
      · apply congrArg (fun t ↦ F.relMap (a 1) ⊗ₜ[ℤ] t)
        exact LinearMap.congr_fun
          (SymmetricPower.map_insert (R₀ := ℤ) (M₀ := P.gen) (N₀ := Q.gen)
            F.genMap q (P.d (a 0))) s |>.symm
    calc
      _ = dTwo Q q (twoMap P Q F q
          (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s)) := rfl
      _ = dTwo Q q
          (exteriorPower.ιMulti ℤ 2 (F.relMap ∘ a) ⊗ₜ[ℤ]
            SymmetricPower.map (R := ℤ) (ι := Fin q) F.genMap s) := by
        rw [twoMap_wedge_tmul]
      _ = oneMap P Q F (q + 1)
          (dTwo P q (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s)) := hmid
      _ = _ := rfl
  exact LinearMap.congr_fun hG w

/-- The map on degree-one cycles. -/
def cyclesMap (q : ℕ) : cyclesOne P q →ₗ[ℤ] cyclesOne Q q :=
  LinearMap.codRestrict (cyclesOne Q q)
    ((oneMap P Q F q).domRestrict (cyclesOne P q)) (fun x => by
      change dOne Q q (oneMap P Q F q x.1) = 0
      have h := LinearMap.congr_fun (dOne_natural P Q F q) x.1
      rw [LinearMap.comp_apply, LinearMap.comp_apply, x.property, map_zero] at h
      exact h)

@[simp]
theorem cyclesMap_val (q : ℕ) (x : cyclesOne P q) :
    (cyclesMap P Q F q x).1 = oneMap P Q F q x.1 := rfl

private theorem cyclesMap_boundary (q : ℕ) :
    boundariesOne P q ≤ Submodule.comap (cyclesMap P Q F q) (boundariesOne Q q) := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  cases q with
  | zero =>
      change cyclesMap P Q F 0 (boundaryMapOne P 0 y) ∈ boundariesOne Q 0
      simp [boundaryMapOne]
  | succ r =>
      refine ⟨twoMap P Q F r y, ?_⟩
      apply Subtype.ext
      change (boundaryMapOne Q (r + 1) (twoMap P Q F r y)).1 =
        (cyclesMap P Q F (r + 1) (boundaryMapOne P (r + 1) y)).1
      simpa only [boundaryMapOne_succ_val, cyclesMap_val,
        LinearMap.comp_apply] using
        (LinearMap.congr_fun (dTwo_natural P Q F r) y)

/-- The homomorphism induced on degree-one Koszul homology. -/
def map (q : ℕ) : homologyOne P q →ₗ[ℤ] homologyOne Q q :=
  (boundariesOne P q).mapQ (boundariesOne Q q) (cyclesMap P Q F q)
    (cyclesMap_boundary P Q F q)

@[simp]
theorem map_mk (q : ℕ) (x : cyclesOne P q) :
    map P Q F q ((boundariesOne P q).mkQ x) =
      (boundariesOne Q q).mkQ (cyclesMap P Q F q x) := rfl

@[simp]
theorem oneMap_id (q : ℕ) :
    oneMap P P (Presentation.Hom.id P) q = LinearMap.id := by
  rw [oneMap]
  simp only [Presentation.Hom.id_relMap, Presentation.Hom.id_genMap,
    SymmetricPower.map_id]
  exact TensorProduct.map_id

theorem oneMap_comp {C : Type u₃} [AddCommGroup C]
    (S : Presentation.{u₃, v₃, w₃} C) {g : B →ₗ[ℤ] C}
    (G : Presentation.Hom Q S g) (q : ℕ) :
    oneMap P S (G.comp F) q =
      (oneMap Q S G q).comp (oneMap P Q F q) := by
  rw [oneMap, oneMap, oneMap]
  simp only [Presentation.Hom.comp_relMap, Presentation.Hom.comp_genMap,
    SymmetricPower.map_comp]
  exact TensorProduct.map_comp _ _ _ _

@[simp]
theorem map_id (q : ℕ) :
    map P P (Presentation.Hom.id P) q = LinearMap.id := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundariesOne P q) y
  change (boundariesOne P q).mkQ (cyclesMap P P (Presentation.Hom.id P) q x) =
    (boundariesOne P q).mkQ x
  apply congrArg (boundariesOne P q).mkQ
  apply Subtype.ext
  change oneMap P P (Presentation.Hom.id P) q x.1 = x.1
  rw [oneMap_id]
  rfl

theorem map_comp {C : Type u₃} [AddCommGroup C]
    (S : Presentation.{u₃, v₃, w₃} C) {g : B →ₗ[ℤ] C}
    (G : Presentation.Hom Q S g) (q : ℕ) :
    map P S (G.comp F) q =
      (map Q S G q).comp (map P Q F q) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundariesOne P q) y
  change (boundariesOne S q).mkQ (cyclesMap P S (G.comp F) q x) =
    (boundariesOne S q).mkQ
      (cyclesMap Q S G q (cyclesMap P Q F q x))
  apply congrArg (boundariesOne S q).mkQ
  apply Subtype.ext
  change oneMap P S (G.comp F) q x.1 =
    oneMap Q S G q (oneMap P Q F q x.1)
  exact LinearMap.congr_fun (oneMap_comp P Q F S G q) x.1

end PresentationHomology

/-- The first derived functor `L₁Sᵐ` on finite additive groups, computed from
the canonical finite free presentation.  The argument is the symmetric degree
in degree one, so `FirstDerivedSymmetricPower q A = L₁S^(q+1)(A)`. -/
abbrev FirstDerivedSymmetricPower (q : ℕ) (A : Type u)
    [AddCommGroup A] [Finite A] :=
  homologyOne (Presentation.canonical A) q

namespace FirstDerivedSymmetricPower

variable {A : Type u} {B : Type u} {C : Type u}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Finite A] [Finite B] [Finite C]

/-- Functoriality of `L₁S^(q+1)` on finite additive groups. -/
def map (q : ℕ) (f : A →ₗ[ℤ] B) :
    FirstDerivedSymmetricPower q A →ₗ[ℤ]
      FirstDerivedSymmetricPower q B :=
  PresentationHomology.map _ _ (Presentation.canonicalHom f) q

@[simp]
theorem map_id (q : ℕ) : map q (LinearMap.id (R := ℤ) (M := A)) = LinearMap.id := by
  rw [map, Presentation.canonicalHom_id]
  exact PresentationHomology.map_id (Presentation.canonical A) q

theorem map_comp (q : ℕ) (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C) :
    map q (g.comp f) = (map q g).comp (map q f) := by
  rw [map, map, map, Presentation.canonicalHom_comp]
  exact PresentationHomology.map_comp _ _ _ _ _ q

end FirstDerivedSymmetricPower

end
end Koszul
