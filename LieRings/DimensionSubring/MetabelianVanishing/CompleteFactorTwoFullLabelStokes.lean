import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoStokes

/-!
# The full-label Stokes identity at the factor-two wall

The stopped quotient-weight collector has two exact reads.  Its ordinary
evaluation uses the active tail of a relation.  Its label evaluation keeps
the same relation whole.  Away from the cutoff the latter is preserved by
every transfer and truncation; at the cutoff the whole label is recorded as
an external term.  Comparing the two terminal decompositions gives the
literal identity

`ordinary factor-two frontier = stopped prefixes + cutoff full labels`.

No cutoff label is asserted to vanish, and no homogeneous component is
regarded as a relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeFactorTwoFullLabelFintype : Fintype L :=
  Fintype.ofFinite L

/-! ## The whole-relation read and its cutoff trace -/

/-- Replace the active tail in a marked quotient-weight row by its stored
whole relation.  Ordinary rows carry no full label. -/
def completeFactorTwoFullLabelWord :
    QuotientWeightRow n L data → UEA ℤ (FreeModel n L)
  | .ordinary _ => 0
  | .marked left rho _ right =>
      QuotientWeightRow.basisWord n L data left *
        UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
        QuotientWeightRow.basisWord n L data right

/-- Factor-two PBW read of the whole relation label. -/
def completeFactorTwoFullLabelRead
    (r : QuotientWeightRow n L data) : Sym[ℤ] (Fin 2) (A L n) :=
  rightSymbol n L data hn 2 n (by omega)
    (completeFactorTwoFullLabelWord n L data r)

/-- The full label lost when a marked row above factor two reaches the
zero-tail cutoff. -/
def completeFactorTwoCutoffFullLabelSeed
    (r : QuotientWeightRow n L data) : Sym[ℤ] (Fin 2) (A L n) :=
  match r with
  | .ordinary _ => 0
  | .marked left rho s right =>
      if 2 < left.length + 1 + right.length ∧ s.val = n + 1 then
        completeFactorTwoFullLabelRead n L data hn
          (.marked left rho s right)
      else 0

private def completeFactorTwoCutoffTraceStep
    (r : QuotientWeightRow n L data)
    (rec : ∀ q, (completeFactorTwoCollector n L data).relation q r →
      Sym[ℤ] (Fin 2) (A L n)) : Sym[ℤ] (Fin 2) (A L n) :=
  completeFactorTwoCutoffFullLabelSeed n L data hn r +
    match h : (completeFactorTwoCollector n L data).expansion r with
    | none => 0
    | some qs => (qs.attach.map fun q ↦ q.1.1 •
        rec q.1.2
          ((completeFactorTwoCollector n L data).decreases h q.1 q.2)).sum

/-- Signed sum of every whole relation label discarded at a cutoff below a
row. -/
def completeFactorTwoCutoffFullLabelTrace
    (r : QuotientWeightRow n L data) : Sym[ℤ] (Fin 2) (A L n) :=
  (completeFactorTwoCollector n L data).wellFounded.fix
    (completeFactorTwoCutoffTraceStep n L data hn) r

theorem completeFactorTwoCutoffFullLabelTrace_eq
    (r : QuotientWeightRow n L data) :
    completeFactorTwoCutoffFullLabelTrace n L data hn r =
      completeFactorTwoCutoffTraceStep n L data hn r
        (fun q _ ↦ completeFactorTwoCutoffFullLabelTrace n L data hn q) := by
  rw [completeFactorTwoCutoffFullLabelTrace,
    (completeFactorTwoCollector n L data).wellFounded.fix_eq]
  congr 1

/-! ## Local whole-label balance -/

private theorem completeFactorTwoFullLabelWord_markedTransfer
    (left rest : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (v : TriangularPBWIndex n L) :
    completeFactorTwoFullLabelWord n L data
        (.marked left rho ⟨0, by omega⟩ (v :: rest)) =
      completeFactorTwoFullLabelWord n L data
          (.marked (left ++ [v]) rho ⟨0, by omega⟩ rest) +
        completeFactorTwoFullLabelWord n L data
          (.marked left (triangularRelationRightBracket n L data rho v)
            ⟨0, by omega⟩ rest) := by
  let lw := QuotientWeightRow.basisWord n L data left
  let rwrd := QuotientWeightRow.basisWord n L data rest
  let R : FreeModel n L := rho
  let xv : FreeModel n L := triangularPBWBasis n L data v
  have hleftWord : QuotientWeightRow.basisWord n L data
      (left ++ [v]) = lw * UniversalEnvelopingAlgebra.ι ℤ xv := by
    simp [QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, List.map_append, lw, xv]
  have hrightWord : QuotientWeightRow.basisWord n L data (v :: rest) =
      UniversalEnvelopingAlgebra.ι ℤ xv * rwrd := by
    simp [QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, rwrd, xv]
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
    (FreeModel n L) R xv
  simp only [completeFactorTwoFullLabelWord]
  rw [hleftWord, hrightWord]
  change lw * UniversalEnvelopingAlgebra.ι ℤ R *
      (UniversalEnvelopingAlgebra.ι ℤ xv * rwrd) =
    (lw * UniversalEnvelopingAlgebra.ι ℤ xv) *
        UniversalEnvelopingAlgebra.ι ℤ R * rwrd +
      lw * UniversalEnvelopingAlgebra.ι ℤ
        ⁅R, xv⁆ * rwrd
  calc
    _ = lw * (UniversalEnvelopingAlgebra.ι ℤ R *
        UniversalEnvelopingAlgebra.ι ℤ xv) * rwrd := by
          noncomm_ring
    _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
          UniversalEnvelopingAlgebra.ι ℤ R +
        UniversalEnvelopingAlgebra.ι ℤ ⁅R, xv⁆) * rwrd := by
          rw [hswap]
    _ = _ := by noncomm_ring

private theorem quotientTruncationRows_completeFullLabelRead
    (left right : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (s : ℕ) (hs : s < n + 1) :
    ((quotientTruncationRows n L data left right rho s hs).map
      (fun q ↦ q.1 •
        completeFactorTwoFullLabelRead n L data hn q.2)).sum = 0 := by
  classical
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  rw [quotientTruncationRows, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  simp [completeFactorTwoFullLabelRead,
    completeFactorTwoFullLabelWord]
  exact smul_zero _

/-- Every nonterminal step preserves the whole-label read, except that a
cutoff emits exactly its recorded full-label seed. -/
theorem completeFactorTwoExpansion_fullLabel_balance
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (h : completeFactorTwoExpansion n L data r = some qs) :
    (qs.map fun q ↦ q.1 •
        completeFactorTwoFullLabelRead n L data hn q.2).sum +
      completeFactorTwoCutoffFullLabelSeed n L data hn r =
        completeFactorTwoFullLabelRead n L data hn r := by
  classical
  cases r with
  | ordinary xs =>
      simp only [completeFactorTwoExpansion] at h
      simp only [quotientWeightExpansion] at h
      split at h <;> try contradiction
      rename_i d hd
      rw [Option.some.injEq] at h
      subst qs
      simp [quotientOrdinaryCorrection, completeFactorTwoFullLabelRead,
        completeFactorTwoFullLabelWord,
        completeFactorTwoCutoffFullLabelSeed]
      apply List.sum_eq_zero
      intro z hz
      rw [List.mem_map] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      simp [completeFactorTwoFullLabelRead,
        completeFactorTwoFullLabelWord]
      exact smul_zero _
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
            have hfactor : 2 < left.length + 1 + right.length := by
              simpa [QuotientWeightRow.factorCount] using hlarge
            simp [completeFactorTwoCutoffFullLabelSeed,
              completeFactorTwoFullLabelRead,
              hfactor, hcut]
          · rename_i hcut
            have hslt : s.val < n + 1 := by omega
            split at h
            · rename_i v rest hright
              split at h
              · rename_i hv
                rw [Option.some.injEq] at h
                subst qs
                simp only [List.map_cons, List.map_nil, List.sum_cons,
                  List.sum_nil, one_smul, add_zero]
                have hword := completeFactorTwoFullLabelWord_markedTransfer
                  n L data hn left rest rho v
                have hread := congrArg
                  (rightSymbol n L data hn 2 n (by omega)) hword
                simp only [map_add] at hread
                simpa [completeFactorTwoFullLabelRead,
                  completeFactorTwoCutoffFullLabelSeed, hcut] using hread.symm
              · rename_i hv
                rw [Option.some.injEq] at h
                subst qs
                rw [List.map_cons, List.sum_cons,
                  quotientTruncationRows_completeFullLabelRead
                    n L data hn left (v :: rest) rho s.val hslt]
                simp [completeFactorTwoCutoffFullLabelSeed, hcut,
                  completeFactorTwoFullLabelRead,
                  completeFactorTwoFullLabelWord]
            · rename_i hright
              rw [Option.some.injEq] at h
              subst qs
              rw [List.map_cons, List.sum_cons,
                quotientTruncationRows_completeFullLabelRead
                  n L data hn left [] rho s.val hslt]
              simp [completeFactorTwoCutoffFullLabelSeed, hcut,
                completeFactorTwoFullLabelRead,
                completeFactorTwoFullLabelWord]

/-! ## Normal-form Stokes equation for the full-label read -/

/-- Whole-label read retained by terminal leaves below one row. -/
def completeNormalFormFullLabelRead
    (r : QuotientWeightRow n L data) : Sym[ℤ] (Fin 2) (A L n) :=
  ((completeFactorTwoCollector n L data).normalForm r).sum
    (fun q z ↦ z • completeFactorTwoFullLabelRead n L data hn q)

private def completeFactorTwoFullLabelLinear :
    (QuotientWeightRow n L data →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin 2) (A L n) :=
  Finsupp.linearCombination ℤ (completeFactorTwoFullLabelRead n L data hn)

private theorem sum_smul_add_completeFactorTwoFullLabel
    (rows : List (ℤ × QuotientWeightRow n L data)) :
    (rows.map (fun q ↦ q.1 •
      (completeNormalFormFullLabelRead n L data hn q.2 +
        completeFactorTwoCutoffFullLabelTrace n L data hn q.2))).sum =
      (rows.map (fun q ↦ q.1 •
        completeNormalFormFullLabelRead n L data hn q.2)).sum +
      (rows.map (fun q ↦ q.1 •
        completeFactorTwoCutoffFullLabelTrace n L data hn q.2)).sum := by
  induction rows with
  | nil => simp
  | cons q rows ih =>
      simp only [List.map_cons, List.sum_cons, smul_add]
      rw [ih]
      module

/-- The exact full-label Stokes formula below one arbitrary row. -/
theorem completeFullLabelRead_eq_normalForm_add_cutoff
    (r : QuotientWeightRow n L data) :
    completeFactorTwoFullLabelRead n L data hn r =
      completeNormalFormFullLabelRead n L data hn r +
        completeFactorTwoCutoffFullLabelTrace n L data hn r := by
  classical
  let C := completeFactorTwoCollector n L data
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : completeFactorTwoExpansion n L data r with
      | none =>
          have hseed : completeFactorTwoCutoffFullLabelSeed n L data hn r = 0 := by
            cases r with
            | ordinary xs => rfl
            | marked left rho s right =>
                have hsmall :=
                  (completeFactorTwoExpansion_marked_eq_none_iff
                    n L data left right rho s).mp hexp
                simp [completeFactorTwoCutoffFullLabelSeed, hsmall]
          rw [completeNormalFormFullLabelRead,
            C.normalForm_eq_single_of_terminal hexp,
            completeFactorTwoCutoffFullLabelTrace_eq]
          unfold completeFactorTwoCutoffTraceStep
          have hexp' : C.expansion r = none := hexp
          split
          · simp [hseed]
          · rename_i rows he
            rw [hexp'] at he
            contradiction
      | some qs =>
          have hnf :
              completeNormalFormFullLabelRead n L data hn r =
                (qs.map fun q ↦ q.1 •
                  completeNormalFormFullLabelRead n L data hn q.2).sum := by
            change completeFactorTwoFullLabelLinear n L data hn
              (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r qs hexp, map_list_sum]
            simp only [List.map_map, Function.comp_apply]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            change completeFactorTwoFullLabelLinear n L data hn
                (q.1 • C.normalForm q.2) =
              q.1 • completeNormalFormFullLabelRead n L data hn q.2
            rw [map_zsmul]
            rfl
          have htrace :
              completeFactorTwoCutoffFullLabelTrace n L data hn r =
                completeFactorTwoCutoffFullLabelSeed n L data hn r +
                  (qs.map fun q ↦ q.1 •
                    completeFactorTwoCutoffFullLabelTrace
                      n L data hn q.2).sum := by
            have hexp' : C.expansion r = some qs := hexp
            rw [completeFactorTwoCutoffFullLabelTrace_eq]
            unfold completeFactorTwoCutoffTraceStep
            split
            · rename_i he
              rw [hexp'] at he
              contradiction
            · rename_i rows he
              have hrows : rows = qs := by
                rw [hexp'] at he
                exact (Option.some.inj he).symm
              subst rows
              congr 1
              simpa only using congrArg List.sum
                (List.attach_map_val (l := qs)
                  (f := fun q ↦ q.1 •
                    completeFactorTwoCutoffFullLabelTrace
                      n L data hn q.2))
          rw [hnf, htrace]
          change completeFactorTwoFullLabelRead n L data hn r =
            (qs.map fun q ↦ q.1 •
                completeNormalFormFullLabelRead n L data hn q.2).sum +
              (completeFactorTwoCutoffFullLabelSeed n L data hn r +
                (qs.map fun q ↦ q.1 •
                  completeFactorTwoCutoffFullLabelTrace
                    n L data hn q.2).sum)
          have hchildren :
              (qs.map fun q ↦ q.1 •
                completeFactorTwoFullLabelRead n L data hn q.2).sum =
              (qs.map fun q ↦ q.1 •
                completeNormalFormFullLabelRead n L data hn q.2).sum +
              (qs.map fun q ↦ q.1 •
                completeFactorTwoCutoffFullLabelTrace
                  n L data hn q.2).sum := by
            calc
              _ = (qs.map fun q ↦ q.1 •
                    (completeNormalFormFullLabelRead n L data hn q.2 +
                      completeFactorTwoCutoffFullLabelTrace
                        n L data hn q.2)).sum := by
                    apply congrArg List.sum
                    apply List.map_congr_left
                    intro q hq
                    rw [ih q.2 (C.decreases hexp q hq)]
              _ = _ := sum_smul_add_completeFactorTwoFullLabel
                    n L data hn qs
          have hlocal := completeFactorTwoExpansion_fullLabel_balance
            n L data hn hexp
          rw [← hlocal, hchildren]
          module

end

end LieRings.MetabelianVanishing
