# Lie homology

This directory implements Chevalley–Eilenberg homology with trivial coefficients over an
arbitrary commutative ring.

The dependency order is intentional:

1. `Differential.lean` constructs the all-degree boundary and proves `d ∘ d = 0` and naturality.
2. `Complex.lean` packages it as a Mathlib chain complex and defines all-degree homology.
3. `LowDegree.lean`, `DegreeTwo.lean`, and `LowDegreeHomology.lean` expose the concrete low-degree
   interfaces and prove the formulas for `H₀` and `H₁`.
4. `ReducedExteriorSquare.lean` and `ReducedExteriorUniversal.lean` identify `H₂` with the
   kernel of the bracket on the reduced exterior square.
5. `FreeVanishing.lean` proves the required free-Lie calculation directly.
6. `Presentation.lean` proves reduced-exterior exactness for a free presentation.
7. `HopfFormula.lean` proves the Hopf formula, and `HopfNaturality.lean` proves its naturality.

Import `LieRings.Homological.LieHomology` for the public API.  The older
`LieRings.Homological.SecondHomology` object is an integral, degree-two Hopf-formula model; the
canonical comparison with standard CE homology is exported from `HopfFormula.lean`.
