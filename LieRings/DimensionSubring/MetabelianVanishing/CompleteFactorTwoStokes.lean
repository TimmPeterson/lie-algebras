import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoTailCorrection

/-!
# Ordinary Stokes ledger for the complete factor-two collector

The factor-two pass stops genuine marked rows at factor number two, but it
continues to collect ordinary rows.  This file records the exact part of that
calculation which is independent of the later full-label correction:

* the terminal support of the stopped collector; and
* the factor-two symbol of its ordinary terminal frontier, as the signed sum
  of the homogeneous components exposed at truncation steps.

No stopped tail is replaced by a full relation here.  In particular, the
full-label/cutoff contribution is deliberately not asserted to vanish.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeFactorTwoStokesFintype : Fintype L :=
  Fintype.ofFinite L

/-! ## Terminal support -/

/-- The two spellings of the stopped expansion are definitionally the same.
The separate name in the tail-correction file only emphasizes that ordinary
rows must continue to collect. -/
theorem completeFactorTwoExpansionWithOrdinary_eq
    (r : QuotientWeightRow n L data) :
    completeFactorTwoExpansionWithOrdinary n L data r =
      completeFactorTwoExpansion n L data r := by
  cases r <;>
    simp [completeFactorTwoExpansionWithOrdinary,
      completeFactorTwoExpansion]

/-- A marked row is terminal for the stopped pass exactly at factor number at
most two.  There is no additional cutoff family: above factor two a cutoff
row expands to the empty signed list, and hence is processed rather than
retained in the normal form. -/
theorem completeFactorTwoExpansion_marked_eq_none_iff
    (left right : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (s : Fin (n + 2)) :
    completeFactorTwoExpansion n L data
        (.marked left rho s right) = none ↔
      left.length + 1 + right.length ≤ 2 := by
  constructor
  · intro h
    by_contra hlarge
    have hnotSmall : ¬(QuotientWeightRow.factorCount n L data
        (.marked left rho s right) ≤ 2) := by
      simpa [QuotientWeightRow.factorCount] using hlarge
    simp only [completeFactorTwoExpansion, hnotSmall, if_false] at h
    simp only [quotientWeightExpansion] at h
    have hone : ¬(left.length + 1 + right.length ≤ 1) := by omega
    simp only [hone, if_false] at h
    by_cases hcut : s.val = n + 1
    · simp [hcut] at h
    · simp only [hcut, if_false] at h
      cases right with
      | nil => simp at h
      | cons v rest =>
          by_cases hv : v.1.val < s.val <;> simp [hv] at h
  · intro hsmall
    simp [completeFactorTwoExpansion,
      QuotientWeightRow.factorCount, hsmall]

/-- Complete terminal-shape classification.  Ordinary terminal rows are
precisely ordered PBW words; marked terminal rows are precisely the genuine
factor-one and factor-two walls. -/
theorem completeFactorTwoExpansion_eq_none_iff
    (r : QuotientWeightRow n L data) :
    completeFactorTwoExpansion n L data r = none ↔
      match r with
      | .ordinary xs => xs.Pairwise (· ≤ ·)
      | .marked left _ _ right => left.length + 1 + right.length ≤ 2 := by
  cases r with
  | ordinary xs =>
      simp only [completeFactorTwoExpansion, quotientWeightExpansion]
      split
      · rename_i hnone
        exact ⟨fun _ ↦
          (LieRings.DegreeFive.chooseAdjacentInversion?_eq_none_iff_pairwise
            xs).mp hnone,
          fun _ ↦ rfl⟩
      · rename_i d hsome
        constructor
        · intro h
          contradiction
        · intro hordered
          have hnone :=
            (LieRings.DegreeFive.chooseAdjacentInversion?_eq_none_iff_pairwise
              xs).mpr hordered
          rw [hsome] at hnone
          contradiction
  | marked left rho s right =>
      exact completeFactorTwoExpansion_marked_eq_none_iff
        n L data left right rho s

/-! ## The ordinary factor-two trace -/

/-- Exact factor-two read of an ordinary row.  Marked rows carry no ordinary
read in this ledger. -/
def completeOrdinaryFactorTwoSeed :
    QuotientWeightRow n L data → Sym[ℤ] (Fin 2) (A L n)
  | .ordinary xs =>
      rightSymbol n L data hn 2 n (by omega)
        (QuotientWeightRow.basisWord n L data xs)
  | .marked _ _ _ _ => 0

/-- The factor-two edge exposed at the current truncation step, if the
current row is a non-stopped marked row ready to expose its active
homogeneous component. -/
def completeTruncationFactorTwoSeed :
    QuotientWeightRow n L data → Sym[ℤ] (Fin 2) (A L n)
  | .ordinary _ => 0
  | r@(.marked left rho s right) =>
      if hlarge : 2 < r.factorCount n L then
        if hcut : s.val < n + 1 then
          match right with
          | v :: _ =>
              if v.1.val < s.val then 0 else
                rightSymbol n L data hn 2 n (by omega)
                  (QuotientWeightRow.basisWord n L data left *
                    UniversalEnvelopingAlgebra.ι ℤ
                      (FreeMetabelian.Free.weightIncl s.val hcut
                        (FreeMetabelian.Free.weightProject s.val hcut
                          (rho : FreeModel n L))) *
                    QuotientWeightRow.basisWord n L data right)
          | [] =>
              rightSymbol n L data hn 2 n (by omega)
                (QuotientWeightRow.basisWord n L data left *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (FreeMetabelian.Free.weightIncl s.val hcut
                      (FreeMetabelian.Free.weightProject s.val hcut
                        (rho : FreeModel n L))) *
                  QuotientWeightRow.basisWord n L data [])
        else 0
      else 0

/-- The signed sum of all factor-two truncation edges below a row.  This is
the direct value-valued version of the occurrence trace: every recursive
child is multiplied by the coefficient with which it was emitted. -/
private def completeFactorTwoTruncationTraceStep
    (r : QuotientWeightRow n L data)
    (rec : ∀ q, (completeFactorTwoCollector n L data).relation q r →
      Sym[ℤ] (Fin 2) (A L n)) : Sym[ℤ] (Fin 2) (A L n) :=
  completeTruncationFactorTwoSeed n L data hn r +
    match h : (completeFactorTwoCollector n L data).expansion r with
    | none => 0
    | some qs => (qs.attach.map fun q ↦ q.1.1 •
        rec q.1.2
          ((completeFactorTwoCollector n L data).decreases h q.1 q.2)).sum

def completeFactorTwoTruncationTrace
    (r : QuotientWeightRow n L data) : Sym[ℤ] (Fin 2) (A L n) :=
  (completeFactorTwoCollector n L data).wellFounded.fix
    (completeFactorTwoTruncationTraceStep n L data hn) r

theorem completeFactorTwoTruncationTrace_eq
    (r : QuotientWeightRow n L data) :
    completeFactorTwoTruncationTrace n L data hn r =
      completeFactorTwoTruncationTraceStep n L data hn r
        (fun q _ ↦ completeFactorTwoTruncationTrace n L data hn q) := by
  rw [completeFactorTwoTruncationTrace,
    (completeFactorTwoCollector n L data).wellFounded.fix_eq]
  congr 1

/-- Ordinary factor-two contribution of all terminal leaves below one row. -/
def completeNormalFormOrdinaryFactorTwo
    (r : QuotientWeightRow n L data) : Sym[ℤ] (Fin 2) (A L n) :=
  ((completeFactorTwoCollector n L data).normalForm r).sum
    (fun q z ↦ z • completeOrdinaryFactorTwoSeed n L data hn q)

private def completeOrdinaryFactorTwoLinear :
    (QuotientWeightRow n L data →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin 2) (A L n) :=
  Finsupp.linearCombination ℤ (completeOrdinaryFactorTwoSeed n L data hn)

@[simp] theorem completeOrdinaryFactorTwoLinear_apply
    (x : QuotientWeightRow n L data →₀ ℤ) :
    completeOrdinaryFactorTwoLinear n L data hn x =
      x.sum (fun q z ↦ z • completeOrdinaryFactorTwoSeed n L data hn q) := rfl

/-! ## The one-step Stokes identity -/

/-- Reading the ordinary children created by one quotient-weight truncation
gives exactly the factor-two symbol of the exposed homogeneous component.
This is the literal coordinate calculation used in the manuscript. -/
private theorem quotientTruncationRows_completeOrdinaryFactorTwoSeed
    (left right : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (s : ℕ) (hs : s < n + 1) :
    ((quotientTruncationRows n L data left right rho s hs).map
      (fun q ↦ q.1 • completeOrdinaryFactorTwoSeed n L data hn q.2)).sum =
      rightSymbol n L data hn 2 n (by omega)
        (QuotientWeightRow.basisWord n L data left *
          UniversalEnvelopingAlgebra.ι ℤ
            (FreeMetabelian.Free.weightIncl s hs
              (FreeMetabelian.Free.weightProject s hs
                (rho : FreeModel n L))) *
          QuotientWeightRow.basisWord n L data right) := by
  classical
  let component : FreeModel n L :=
    FreeMetabelian.Free.weightIncl s hs
      (FreeMetabelian.Free.weightProject s hs (rho : FreeModel n L))
  let context : FreeModel n L →ₗ[ℤ] Sym[ℤ] (Fin 2) (A L n) :=
    (rightSymbol n L data hn 2 n (by omega)).comp
      (show FreeModel n L →ₗ[ℤ] UEA ℤ (FreeModel n L) from
        { toFun := fun x ↦ QuotientWeightRow.basisWord n L data left *
              UniversalEnvelopingAlgebra.ι ℤ x *
              QuotientWeightRow.basisWord n L data right
          map_add' := by intro x y; rw [map_add, mul_add, add_mul]
          map_smul' := by
            intro z x
            rw [map_zsmul, mul_smul_comm, smul_mul_assoc]
            simp only [RingHom.id_apply] })
  have hc := congrArg context
    (triangularCoordinates_sum n L data component)
  rw [map_list_sum] at hc
  rw [quotientTruncationRows, List.map_map]
  calc
    ((triangularCoordinates n L data component).map
        (fun q ↦ q.1 • completeOrdinaryFactorTwoSeed n L data hn
          (.ordinary (left ++ q.2 :: right)))).sum =
        ((triangularCoordinates n L data component).map
          (fun q ↦ context
            (q.1 • triangularPBWBasis n L data q.2))).sum := by
      congr 1
      apply List.map_congr_left
      intro q hq
      rcases q with ⟨z, i⟩
      simp [completeOrdinaryFactorTwoSeed, context,
        QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word, List.map_append]
      noncomm_ring
    _ = context component := by
      simpa only [List.map_map, Function.comp_apply] using hc
    _ = _ := rfl

/-- Local factor-two Stokes balance for one deterministic step of the
complete stopped collector. -/
theorem completeFactorTwoExpansion_ordinaryFactorTwo
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (h : completeFactorTwoExpansion n L data r = some qs) :
    (qs.map (fun q ↦ q.1 •
      completeOrdinaryFactorTwoSeed n L data hn q.2)).sum =
      completeOrdinaryFactorTwoSeed n L data hn r +
        completeTruncationFactorTwoSeed n L data hn r := by
  classical
  cases r with
  | ordinary word =>
      simp only [completeFactorTwoExpansion] at h
      simp only [quotientWeightExpansion] at h
      split at h
      · contradiction
      · rename_i d hd
        rw [Option.some.injEq] at h
        subst qs
        let rows : List (ℤ × QuotientWeightRow n L data) :=
          (1, .ordinary (d.left ++ d.y :: d.x :: d.right)) ::
            quotientOrdinaryCorrection n L data d.left d.right d.x d.y
        have hpres :
            (rows.map (fun q ↦ q.1 • q.2.value n L data)).sum =
              (QuotientWeightRow.ordinary word :
                QuotientWeightRow n L data).value n L data :=
          completeFactorTwoExpansion_preserves n L data
            (show completeFactorTwoExpansion n L data (.ordinary word) =
                some rows by
              simp only [rows, completeFactorTwoExpansion,
                quotientWeightExpansion, hd])
        calc
          (rows.map (fun q ↦ q.1 •
              completeOrdinaryFactorTwoSeed n L data hn q.2)).sum =
              rightSymbol n L data hn 2 n (by omega)
                ((rows.map (fun q ↦ q.1 • q.2.value n L data)).sum) := by
            rw [map_list_sum, List.map_map]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            have hord : ∃ xs, q.2 = QuotientWeightRow.ordinary xs := by
              simp only [rows, List.mem_cons] at hq
              rcases hq with rfl | hq
              · exact ⟨_, rfl⟩
              · rw [quotientOrdinaryCorrection, List.mem_map] at hq
                obtain ⟨p, hp, rfl⟩ := hq
                exact ⟨_, rfl⟩
            rcases q with ⟨z, q⟩
            obtain ⟨xs, rfl⟩ := hord
            simp only [Function.comp_apply, completeOrdinaryFactorTwoSeed,
              QuotientWeightRow.value, map_zsmul]
          _ = rightSymbol n L data hn 2 n (by omega)
              (QuotientWeightRow.value n L data
                (.ordinary word : QuotientWeightRow n L data)) := by
            rw [hpres]
          _ = completeOrdinaryFactorTwoSeed n L data hn (.ordinary word) +
              completeTruncationFactorTwoSeed n L data hn (.ordinary word) := by
            simp [completeOrdinaryFactorTwoSeed,
              completeTruncationFactorTwoSeed, QuotientWeightRow.value]
  | marked left rho s right =>
      simp only [completeFactorTwoExpansion] at h
      split at h
      · contradiction
      · rename_i hlarge
        simp only [quotientWeightExpansion] at h
        split at h
        · contradiction
        · rename_i hone
          split at h
          · rename_i hcut
            rw [Option.some.injEq] at h
            subst qs
            simp [completeOrdinaryFactorTwoSeed,
              completeTruncationFactorTwoSeed, hlarge, hcut]
          · rename_i hcut
            have hslt : s.val < n + 1 := by omega
            split at h
            · rename_i v rest hright
              split at h
              · rename_i hv
                rw [Option.some.injEq] at h
                subst qs
                simp [completeOrdinaryFactorTwoSeed,
                  completeTruncationFactorTwoSeed, hlarge, hslt, hv]
              · rename_i hv
                rw [Option.some.injEq] at h
                subst qs
                rw [List.map_cons, List.sum_cons]
                change (1 : ℤ) • (0 : Sym[ℤ] (Fin 2) (A L n)) +
                    ((quotientTruncationRows n L data left (v :: rest)
                      rho s.val _).map (fun q ↦ q.1 •
                        completeOrdinaryFactorTwoSeed n L data hn q.2)).sum = _
                rw [one_smul, zero_add,
                  quotientTruncationRows_completeOrdinaryFactorTwoSeed
                    n L data hn left (v :: rest) rho s.val hslt]
                have hfactor : 2 < QuotientWeightRow.factorCount n L data
                    (.marked left rho s (v :: rest)) := by omega
                simp [completeOrdinaryFactorTwoSeed,
                  completeTruncationFactorTwoSeed, hfactor, hslt, hv]
            · rename_i hright
              rw [Option.some.injEq] at h
              subst qs
              rw [List.map_cons, List.sum_cons]
              change (1 : ℤ) • (0 : Sym[ℤ] (Fin 2) (A L n)) +
                  ((quotientTruncationRows n L data left [] rho s.val _).map
                    (fun q ↦ q.1 • completeOrdinaryFactorTwoSeed
                      n L data hn q.2)).sum = _
              rw [one_smul, zero_add,
                quotientTruncationRows_completeOrdinaryFactorTwoSeed
                  n L data hn left [] rho s.val hslt]
              have hfactor : 2 < QuotientWeightRow.factorCount n L data
                  (.marked left rho s []) := by omega
              simp [completeOrdinaryFactorTwoSeed,
                completeTruncationFactorTwoSeed, hfactor, hslt]

private theorem completeTruncationFactorTwoSeed_eq_zero_of_terminal
    (r : QuotientWeightRow n L data)
    (h : completeFactorTwoExpansion n L data r = none) :
    completeTruncationFactorTwoSeed n L data hn r = 0 := by
  cases r with
  | ordinary xs => rfl
  | marked left rho s right =>
      have hsmall : left.length + 1 + right.length ≤ 2 :=
        (completeFactorTwoExpansion_marked_eq_none_iff
          n L data left right rho s).mp h
      simp [completeTruncationFactorTwoSeed,
        QuotientWeightRow.factorCount, show ¬2 < left.length + 1 + right.length
          by omega]

private theorem sum_smul_add_completeFactorTwo
    (rows : List (ℤ × QuotientWeightRow n L data)) :
    (rows.map (fun q ↦ q.1 •
      (completeOrdinaryFactorTwoSeed n L data hn q.2 +
        completeFactorTwoTruncationTrace n L data hn q.2))).sum =
      (rows.map (fun q ↦ q.1 •
        completeOrdinaryFactorTwoSeed n L data hn q.2)).sum +
      (rows.map (fun q ↦ q.1 •
        completeFactorTwoTruncationTrace n L data hn q.2)).sum := by
  induction rows with
  | nil => simp
  | cons q rows ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      module

/-- Global ordinary-factor Stokes formula for the complete stopped collector.
The ordinary factor-two part of the terminal normal form is the initial
ordinary read plus the signed sum of all homogeneous truncation reads. -/
theorem completeNormalFormOrdinaryFactorTwo_eq_truncationTrace
    (r : QuotientWeightRow n L data) :
    completeNormalFormOrdinaryFactorTwo n L data hn r =
      completeOrdinaryFactorTwoSeed n L data hn r +
        completeFactorTwoTruncationTrace n L data hn r := by
  classical
  let C := completeFactorTwoCollector n L data
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : completeFactorTwoExpansion n L data r with
      | none =>
          have hseed := completeTruncationFactorTwoSeed_eq_zero_of_terminal
            n L data hn r hexp
          have hexp' :
              (completeFactorTwoCollector n L data).expansion r = none := hexp
          rw [completeNormalFormOrdinaryFactorTwo,
            C.normalForm_eq_single_of_terminal hexp,
            completeFactorTwoTruncationTrace_eq]
          unfold completeFactorTwoTruncationTraceStep
          rw [hseed]
          simp only [zero_add]
          split
          · simp
          · rename_i qs he
            rw [hexp'] at he
            contradiction
      | some rows =>
          have hnf :
              completeNormalFormOrdinaryFactorTwo n L data hn r =
                (rows.map (fun q ↦ q.1 •
                  completeNormalFormOrdinaryFactorTwo
                    n L data hn q.2)).sum := by
            change completeOrdinaryFactorTwoLinear n L data hn
              (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r rows hexp, map_list_sum]
            simp only [List.map_map, Function.comp_apply]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            change completeOrdinaryFactorTwoLinear n L data hn
                (q.1 • C.normalForm q.2) =
              q.1 • completeNormalFormOrdinaryFactorTwo n L data hn q.2
            rw [map_zsmul]
            rfl
          have htrace :
              completeFactorTwoTruncationTrace n L data hn r =
                completeTruncationFactorTwoSeed n L data hn r +
                  (rows.map (fun q ↦ q.1 •
                    completeFactorTwoTruncationTrace
                      n L data hn q.2)).sum := by
            have hexp' :
                (completeFactorTwoCollector n L data).expansion r =
                  some rows := hexp
            rw [completeFactorTwoTruncationTrace_eq]
            unfold completeFactorTwoTruncationTraceStep
            split
            · rename_i he
              rw [hexp'] at he
              contradiction
            · rename_i rows' he
              have hrows : rows' = rows := by
                rw [hexp'] at he
                exact (Option.some.inj he).symm
              subst rows'
              congr 1
              simpa only using congrArg List.sum
                (List.attach_map_val
                  (l := rows) (f := fun q ↦ q.1 •
                    completeFactorTwoTruncationTrace n L data hn q.2))
          have hih :
              (rows.map (fun q ↦ q.1 •
                completeNormalFormOrdinaryFactorTwo n L data hn q.2)).sum =
                (rows.map (fun q ↦ q.1 •
                  (completeOrdinaryFactorTwoSeed n L data hn q.2 +
                    completeFactorTwoTruncationTrace
                      n L data hn q.2))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            rw [ih q.2 (C.decreases hexp q hq)]
          have hsplit := sum_smul_add_completeFactorTwo
            n L data hn rows
          have hlocal := completeFactorTwoExpansion_ordinaryFactorTwo
            n L data hn hexp
          rw [hnf, hih, hsplit, hlocal, htrace]
          abel

/-! ## The governing frontier -/

/-- Ordinary factor-two read of the complete terminal frontier. -/
def GoverningWitness.completeFactorTwoOrdinaryFrontier {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  completeOrdinaryFactorTwoLinear n L data hn
    (w.completeFactorTwoFrontier n L data)

/-- The signed factor-two trace of all quotient-weight truncations below the
actual first-pass frontier. -/
def GoverningWitness.completeFactorTwoTruncationDefect {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (w.quotientWeightInitial n L data).sum (fun r z ↦
    z • completeFactorTwoTruncationTrace n L data hn r)

/-- Exact `q = 2` ordinary-frontier theorem.  Since every initial row is
marked by a genuine full relation, the initial ordinary seed is zero; hence
the ordinary terminal frontier is precisely the accumulated truncation
trace. -/
theorem GoverningWitness.completeFactorTwoOrdinaryFrontier_eq_truncationDefect
    {a : L} (w : GoverningWitness n L data a) :
    w.completeFactorTwoOrdinaryFrontier n L data hn =
      w.completeFactorTwoTruncationDefect n L data hn := by
  classical
  change completeOrdinaryFactorTwoLinear n L data hn
      ((w.quotientWeightInitial n L data).sum (fun r z ↦
        z • (completeFactorTwoCollector n L data).normalForm r)) =
    (w.quotientWeightInitial n L data).sum (fun r z ↦
      z • completeFactorTwoTruncationTrace n L data hn r)
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul]
  change (w.quotientWeightInitial n L data r) •
      completeNormalFormOrdinaryFactorTwo n L data hn r =
    (w.quotientWeightInitial n L data r) •
      completeFactorTwoTruncationTrace n L data hn r
  rw [completeNormalFormOrdinaryFactorTwo_eq_truncationTrace]
  have hseed : completeOrdinaryFactorTwoSeed n L data hn r = 0 := by
    have hrne := Finsupp.mem_support_iff.mp hr
    rw [GoverningWitness.quotientWeightInitial, Finsupp.sum_apply] at hrne
    cases r with
    | ordinary word =>
        exfalso
        apply hrne
        apply Finset.sum_eq_zero
        intro p hp
        simp [quotientWeightRowOfPlaced]
    | marked => rfl
  rw [hseed, zero_add]

end

end LieRings.MetabelianVanishing
