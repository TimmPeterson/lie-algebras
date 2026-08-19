import LieRings.DimensionSubring.DegreeFive.PacketCollector

namespace LieRings.DegreeFive

noncomputable section

universe u v

variable {P : Type u} {A : Type v} [AddCommGroup A]

example (C : FiniteTaggedCollector P A) (p : P)
    (qs : List (ℤ × P)) (h : C.expansion p = some qs) :
    C.normalForm p =
      (qs.map fun q => q.1 • C.normalForm q.2).sum := by
  rw [FiniteTaggedCollector.normalForm, C.wellFounded.fix_eq]
  change
    (match hx : C.expansion p with
    | none => Finsupp.single p 1
    | some rs => (rs.attach.map fun q : {x // x ∈ rs} =>
        q.1.1 • C.normalForm q.1.2).sum) = _
  rw [h]
  exact congrArg List.sum
    (List.attach_map_val (l := qs)
      (f := fun q => q.1 • C.normalForm q.2))

end

end LieRings.DegreeFive
