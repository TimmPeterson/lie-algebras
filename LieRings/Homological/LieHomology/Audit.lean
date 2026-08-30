import LieRings.Homological.LieHomology

/-!
# Axiom audit for Lie homology

This file is intentionally not imported by the public module.  Compiling it records the axioms
used by the principal structural results and by the comparison with the project's older integral
Hopf-formula model.
-/

namespace LieRings.Homological.LieHomology

#print axioms differential_comp_differential
#print axioms homologyZeroEquivBaseRing
#print axioms homologyOneEquivAbelianization
#print axioms secondHomology_free_subsingleton
#print axioms homologyTwo_free_subsingleton
#print axioms secondHomologyHopfEquiv
#print axioms homologyTwoHopfEquiv
#print axioms PresentationHom.secondHomologyHopfEquiv_natural

end LieRings.Homological.LieHomology

namespace LieRings.Homological.FreePresentation

#print axioms ceSecondHomologyEquivHopfModel
#print axioms ceHomologyTwoEquivHopfModel

end LieRings.Homological.FreePresentation
