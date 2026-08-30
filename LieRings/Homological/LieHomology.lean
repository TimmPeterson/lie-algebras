import LieRings.Homological.LieHomology.LowDegreeHomology
import LieRings.Homological.LieHomology.HopfNaturality

/-!
# Chevalley--Eilenberg homology of Lie algebras

Public import for Lie algebra homology with trivial coefficients over a commutative ring.

The library provides:

* the all-degree Chevalley--Eilenberg differential and chain complex;
* functorial maps on complexes and homology;
* the formulas `H₀(L; R) ≃ R` and `H₁(L; R) ≃ L/[L,L]`;
* a concrete cycles-modulo-boundaries interface for `H₂`;
* the Hopf formula `H₂(L; R) ≃ (ker p ∩ [F,F])/[F,ker p]` for a free presentation;
* naturality of that Hopf isomorphism under commuting morphisms of free presentations.
-/
