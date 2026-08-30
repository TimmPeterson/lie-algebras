# Lie rings in Lean 4

This package develops foundational results about Lie algebras over commutative rings, with an
emphasis on Lie rings (the case $R = \mathbb{Z}$). It uses mathlib's definitions of Lie algebras and
universal enveloping algebras.

## Build

From this directory run:

```bash
lake build
```

The project is pinned to Lean 4 and mathlib `v4.29.0`. The library contains no `sorry`
declarations.

## Main proven results

All statements in this section are restated as compiled examples in
[`LieRings/MainResults.lean`](LieRings/MainResults.lean).

### PBW and the canonical embedding

- For an Abelian Lie algebra, PBW is a basis-free algebra equivalence:
  `PBW.abelianEquivSymmetric R L`, giving
  $U_R(L) \simeq_R \mathrm{Sym}_R(L)$.
- If the underlying module has an ordered basis, ordered PBW monomials span the enveloping
  algebra: `PBW.orderedPBWMap_surjective R L ι b`.
- A `PBW.TriangularRepresentation R L ι b` proves the full ordered-basis statement
  `PBW.FreeModulePBW R L ι b` (the ordered PBW map is bijective), and hence the canonical
  embedding. The general non-Abelian ordered-basis PBW theorem is not claimed without this
  representation hypothesis.
- Over $\mathbb{Z}$, every Lie ring embeds canonically, without a basis or auxiliary parameter:

```lean
PBW.canonicalMap_injective_int L :
  Function.Injective (UniversalEnvelopingAlgebra.ι ℤ : L → UEA ℤ L)
```

### Dimension subrings and lower central series

With conventional positive indexing—where `dimensionSubring ℤ L n` denotes $\delta_n(L)$ and
`lowerCentralSeries ℤ L (n - 1)` denotes $\gamma_n(L)$—the following are proved:

- `UEA.quotientEquivLieIdeal R L I`: $U_R(L/I) \simeq_R U_R(L)/\langle I\rangle$, for every Lie
  ideal $I$.
- `dimensionSubring_two_eq_lowerCentralSeries_one`: $\delta_2(L)=\gamma_2(L)$ over every commutative
  base ring.
- `dimensionSubring_three_eq_lowerCentralSeries_two`: $\delta_3(L)=\gamma_3(L)$ for every Lie ring.
- `FreeLieDimension.dimensionSubring_succ_eq_lowerCentralSeries`: for the free Lie ring
  $F=\mathrm{FreeLie}_{\mathbb{Z}}(X)$, $\delta_n(F)=\gamma_n(F)$ in every positive degree.
- `dimensionSubring_bracket_eq_lowerCentralSeries_of_pos`:
  $[\delta_n(L),L]=\gamma_{n+1}(L)$ for $1\leq n$.
- `bracket_dimensionSubring_le_lowerCentralSeries_of_pos`:
  $[\delta_m(L),\delta_n(L)]\subseteq\gamma_{m+n}(L)$ for $1\leq m$ and $1\leq n$.
- `UEA.actionSubmodule_augmentationIdeal_pow_eq_lcs`:
  $A\cdot\omega(L)^n=[A,{}_nL]$ for a Lie submodule $A$.
- `DegreeFour.twoDeltaFourProperty`: Bartholdi--Passi's factor-two theorem
  $2\delta_4(L)\subseteq\gamma_4(L)$ for every Lie ring.

#### $H_2$-description

For every Lie ring $L$ and every $n\geq 2$, the following integral second-homology
descriptions are proved:

- `dimensionFactorEquivSecondHomologyCokernel`:
  ```math
  \frac{\delta_n(L)}{\gamma_n(L)}\simeq
  \operatorname{Coker}\!\left(
    H_2(L/\gamma_n(L);\mathbb Z)\longrightarrow
    H_2(L/\delta_n(L);\mathbb Z)
  \right).
  ```
- `dimensionSubringModNextLowerCentralEquivSecondHomologyCokernel`:
  ```math
  \frac{\delta_n(L)}{\gamma_{n+1}(L)}\simeq
  \operatorname{Coker}\!\left(
    H_2(L;\mathbb Z)\longrightarrow H_2(L/\delta_n(L);\mathbb Z)
  \right).
  ```
- `lowerCentralFactorEquivSecondHomologyCokernel`:
  ```math
  \frac{\gamma_n(L)}{\gamma_{n+1}(L)}\simeq
  \operatorname{Coker}\!\left(
    H_2(L;\mathbb Z)\longrightarrow H_2(L/\gamma_n(L);\mathbb Z)
  \right).
  ```

Here $H_2(-;\mathbb Z)$ is the concrete degree-two integral object defined directly by the
Hopf formula in `Homological/SecondHomology.lean`.

#### Odd-dimensional theorem for metabelian Lie rings

The main result is the following stronger nilpotent theorem:

- **Theorem.** If $K$ is metabelian of nilpotency class at most $c\geq 2$, then
  $\delta_{2c-1}(K)=0$.

It has the following corollaries:

- **Metabelian corollary.** For every metabelian Lie ring $L$ and every $n\geq 1$,
  $\delta_{2n+1}(L)\subseteq\gamma_{n+2}(L)$.
- **Omega corollary.** For every metabelian Lie ring $L$,
  $\delta_\omega(L)=\gamma_\omega(L)$, where both sides are the intersections of all their
  finite terms. Indeed, the preceding inclusion places every element of $\delta_\omega(L)$
  arbitrarily deep in the lower central series; the reverse inclusion holds in every degree.
- **Unconditional degree-five corollary.** For every Lie ring $L$,
  $\delta_5(L)\subseteq\gamma_4(L)$, with no metabelian, finiteness, or torsion hypothesis.

The degree-five statement is not used as a base case for the general theorem. It follows from
the theorem by applying the case $c=3$ to $L/\gamma_4(L)$: this quotient has nilpotency class
at most three and is automatically metabelian.

### Associated graded Lie algebras

- `LieFiltration R L` packages a descending positive filtration with
  $[F_i,F_j]\subseteq F_{i+j}$; `LieFiltration.AssociatedGraded` constructs
  $\bigoplus_{n>0}F_n/F_{n+1}$ as a Lie algebra over $R$.
- `lowerCentralFiltration R L` and `dimensionFiltration R L` define the lower-central and
  dimension filtrations, and `lowerCentralToDimensionGraded R L` is the canonical map
  $\mathrm{gr}_\gamma(L)\to\mathrm{gr}_\delta(L)$.
- `dimensionGradedImage R L` is its image as a Lie ideal, and
  `dimensionGradedImage_isGraded R L` proves that it is homogeneous.
- `DimensionGradedCokernel R L` is the quotient by this image, and
  `dimensionGradedCokernel_isLieAbelian R L` proves that it is Abelian.

## Definitions and how to use them

For downstream files, `import LieRings` imports the public library. Focused imports are also
available; the main definitions are located as follows.

| Mathematical object | Lean declaration | File |
|---|---|---|
| $U_R(L)$ | `UEA R L` (an abbreviation for mathlib's `UniversalEnvelopingAlgebra`) | `UniversalEnveloping/Basic.lean` |
| canonical map $\iota:L\to U_R(L)$ | `UniversalEnvelopingAlgebra.ι R` | `UniversalEnveloping/Basic.lean` |
| augmentation $\varepsilon$ and augmentation ideal $\omega(L)$ | `UEA.augmentation R L`, `UEA.augmentationIdeal R L` | `UniversalEnveloping/Basic.lean` |
| dimension subring $\delta_n(L)$ | `dimensionSubring R L n` | `DimensionSubring/Basic.lean` |
| lower central term $\gamma_{n+1}(L)$ | `lowerCentralSeries R L n` | `DimensionSubring/Basic.lean` |
| intersections $\delta_\omega(L)$, $\gamma_\omega(L)$ | `dimensionSubringOmega R L`, `lowerCentralSeriesOmega R L` | `DimensionSubring/Basic.lean` |
| associated graded of a Lie filtration | `LieFiltration.AssociatedGraded` | `Graded/Associated.lean` |
| $\mathrm{gr}_\gamma(L)\to\mathrm{gr}_\delta(L)$ and its Abelian cokernel | `lowerCentralToDimensionGraded`, `DimensionGradedCokernel` | `DimensionSubring/Graded.lean` |
| ideal generated by a Lie ideal | `UEA.idealOfLieIdeal R L I` | `UniversalEnveloping/Quotient.lean` |
| enveloping-algebra action | `UEA.representation R L M` | `UniversalEnveloping/Adjoint.lean` |
| ordered PBW map | `PBW.orderedPBWMap R L ι b` | `PBW/FreeModuleStatement.lean` |
| factor-two theorem | `DegreeFour.twoDeltaFourProperty` | `DimensionSubring/DegreeFour.lean` |
| odd metabelian theorem and its corollaries | `MetabelianTwoFactor.nilpotent_dimensionSubring_eq_bot`, `MetabelianTwoFactor.odd_dimensionSubring_le_lowerCentralSeries`, `MetabelianTwoFactor.dimensionSubringOmega_eq_lowerCentralSeriesOmega`, `MetabelianTwoFactor.dimensionSubring_five_le_lowerCentralSeries_three` | `DimensionSubring/MetabelianTwoFactor.lean` |

Mathlib numbers the lower central series from zero, so
`lowerCentralSeries R L 0` represents $\gamma_1(L)=L$. For example:

```lean
import LieRings.DimensionSubring.MetabelianTwoFactor

open LieRings

example (L : Type*) [LieRing L] :
    dimensionSubring ℤ L 3 = lowerCentralSeries ℤ L 2 :=
  dimensionSubring_three_eq_lowerCentralSeries_two L

example (L : Type*) [LieRing L] :
    dimensionSubring ℤ L 5 ≤ lowerCentralSeries ℤ L 3 :=
  MetabelianTwoFactor.dimensionSubring_five_le_lowerCentralSeries_three L
```

The directory [`LieRings/Examples`](LieRings/Examples) contains short, compiled examples for
PBW, quotients, dimension centrality, and free Lie rings.

## Project layout

```text
LieRings/UniversalEnveloping/   augmentation, actions, and quotients
LieRings/DimensionSubring/      dimension-subring and lower-central results
LieRings/Graded/                associated graded Lie algebras of filtrations
LieRings/Metabelian/            the finite free-metabelian model
LieRings/PBW/                   PBW statements, Higgins embedding, and conditions
LieRings/Examples/              copyable examples
lit/obstacle/short_natural_proof.tex  proof manuscript for the main theorem
```
