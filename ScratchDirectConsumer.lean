import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance scratchDirectConsumerFintype : Fintype L :=
  Fintype.ofFinite L

theorem GoverningWitness.eq_zero_of_terminalSourceCoordinate
    {a : L} (w : GoverningWitness n L data a)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (sourcePrimitive : TopPreimage n L data)
    (hsource : (sourcePrimitive : FreeModel n L) =
      terminalSourcePrimitive n L data hn cycle.1)
    (hcoordinate : terminalEval n L data sourcePrimitive =
      (w.externalMarkedWord n L data hn).value) :
    a = 0 := by
  let blockCycle := Koszul.PresentationHomology.cyclesMap
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega))
    (terminalComparisonHom n L data hn) 1 cycle
  let raw := terminalBlockCanonicalRawMarkedWord n L data hn blockCycle
  obtain ⟨rho, hrealization⟩ :=
    terminalMappedBlockPrimitive_eq_source_add_relation
      n L data hn cycle
  have hrawPrimitive : (raw.primitive : FreeModel n L) =
      pbwPrimitive n L data hn raw.word := by
    apply canonicalMap_injective_of_freeModulePBW
      ℤ (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis
      (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
        (adaptedWeightedBasis n L data hn).basis)
    rw [← raw.projection_eq,
      factorProj_one_eq_iota_pbwPrimitive n L data hn]
  have hrawTop : raw.primitive =
      sourcePrimitive + relationTopPreimage n L data rho := by
    apply Subtype.ext
    change (raw.primitive : FreeModel n L) =
      (sourcePrimitive : FreeModel n L) + (rho : FreeModel n L)
    rw [hrawPrimitive, hsource]
    exact hrealization
  have hrawValue : raw.value = terminalEval n L data sourcePrimitive := by
    change terminalEval n L data raw.primitive = _
    rw [hrawTop, map_add, terminalEval_relationTopPreimage, add_zero]
  have hcanonical : raw.value =
      (quadraticBlockMarkedWord n L data hn blockCycle).value :=
    (terminalBlockCanonicalRawCertificate n L data hn blockCycle).value_eq
  have hsourceZero : terminalEval n L data sourcePrimitive = 0 := by
    rw [← hrawValue, hcanonical,
      quadraticBlockMarkedWord_value,
      quadraticBlockValue_eq_zero]
  have hexternal : (w.externalMarkedWord n L data hn).value = 0 := by
    rw [← hcoordinate]
    exact hsourceZero
  have hcoord : data.topEquiv ⟨a, by
      rw [← w.evaluates]
      change evaluation n L data
        (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
          lowerCentralSeries ℤ L n
      rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
      change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl
            (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
      rw [FreeMetabelian.Evaluation.linear_incl]
      cases n with
      | zero => simp
      | succ t =>
          exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
            data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ = 0 := by
    rw [← w.externalMarkedWord_value n L data hn]
    exact hexternal
  have hsub : (⟨a, by
      rw [← w.evaluates]
      change evaluation n L data
        (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
          lowerCentralSeries ℤ L n
      rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
      change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl
            (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
      rw [FreeMetabelian.Evaluation.linear_incl]
      cases n with
      | zero => simp
      | succ t =>
          exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
            data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ :
        lowerCentralSeries ℤ L n) = 0 := by
    exact data.topEquiv.injective
      (hcoord.trans data.topEquiv.toAddMonoidHom.map_zero.symm)
  exact congrArg Subtype.val hsub

end

end LieRings.MetabelianVanishing
