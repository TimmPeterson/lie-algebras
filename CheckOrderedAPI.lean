import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalComb
namespace LieRings.MetabelianVanishing
open FreeMetabelian LieRings.PBW
#check RelationContext.bracket_weightIncl_right_mem_tail
#check FreeMetabelian.Free.tail_mono
#check FreeMetabelian.Free.mem_tail_iff
#check List.pairwise_cons
#check List.pairwise_append
#check List.Pairwise.imp
#check List.Pairwise.sublist
#check fullRightSymbol_basisWord_mul_iota_of_mem_tail_one_eq_zero
#check MarkedRow.basisWord
end LieRings.MetabelianVanishing
