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
  \mathrm{Coker}\!\left(
    H_2(L/\gamma_n(L);\mathbb Z)\longrightarrow
    H_2(L/\delta_n(L);\mathbb Z)
  \right).
  ```
- `dimensionSubringModNextLowerCentralEquivSecondHomologyCokernel`:
  ```math
  \frac{\delta_n(L)}{\gamma_{n+1}(L)}\simeq
  \mathrm{Coker}\!\left(
    H_2(L;\mathbb Z)\longrightarrow H_2(L/\delta_n(L);\mathbb Z)
  \right).
  ```
- `lowerCentralFactorEquivSecondHomologyCokernel`:
  ```math
  \frac{\gamma_n(L)}{\gamma_{n+1}(L)}\simeq
  \mathrm{Coker}\!\left(
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
  [F<sub>i</sub>, F<sub>j</sub>] ⊆ F<sub>i+j</sub>; `LieFiltration.AssociatedGraded`
  constructs ⨁<sub>n&gt;0</sub> F<sub>n</sub>/F<sub>n+1</sub> as a Lie algebra over R.
- `lowerCentralFiltration R L` and `dimensionFiltration R L` define the lower-central and
  dimension filtrations, and `lowerCentralToDimensionGraded R L` is the canonical map
  gr<sub>γ</sub>(L) → gr<sub>δ</sub>(L).
- `dimensionGradedImage R L` is its image as a Lie ideal, and
  `dimensionGradedImage_isGraded R L` proves that it is homogeneous.
- `DimensionGradedCokernel R L` is the quotient by this image, and
  `dimensionGradedCokernel_isLieAbelian R L` proves that it is Abelian.

## Definitions and how to use them

For downstream files, `import LieRings` imports the public library. Focused imports are also
available; the main definitions are located as follows.

<table width="100%">
  <thead>
    <tr>
      <th width="38%">Mathematical object</th>
      <th width="42%">Lean declaration</th>
      <th width="20%">File</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>U<sub>R</sub>(L)</td>
      <td><code>UEA R L</code> (an abbreviation for mathlib's <code>UniversalEnvelopingAlgebra</code>)</td>
      <td><code>UniversalEnveloping/Basic.lean</code></td>
    </tr>
    <tr>
      <td>canonical map ι: L → U<sub>R</sub>(L)</td>
      <td><code>UniversalEnvelopingAlgebra.ι R</code></td>
      <td><code>UniversalEnveloping/Basic.lean</code></td>
    </tr>
    <tr>
      <td>augmentation ε and augmentation ideal ω(L)</td>
      <td><code>UEA.augmentation R L</code>, <code>UEA.augmentationIdeal R L</code></td>
      <td><code>UniversalEnveloping/Basic.lean</code></td>
    </tr>
    <tr>
      <td>dimension subring δ<sub>n</sub>(L)</td>
      <td><code>dimensionSubring R L n</code></td>
      <td><code>DimensionSubring/Basic.lean</code></td>
    </tr>
    <tr>
      <td>lower central term γ<sub>n+1</sub>(L)</td>
      <td><code>lowerCentralSeries R L n</code></td>
      <td><code>DimensionSubring/Basic.lean</code></td>
    </tr>
    <tr>
      <td>intersections δ<sub>ω</sub>(L), γ<sub>ω</sub>(L)</td>
      <td><code>dimensionSubringOmega R L</code>, <code>lowerCentralSeriesOmega R L</code></td>
      <td><code>DimensionSubring/Basic.lean</code></td>
    </tr>
    <tr>
      <td>associated graded of a Lie filtration</td>
      <td><code>LieFiltration.AssociatedGraded</code></td>
      <td><code>Graded/Associated.lean</code></td>
    </tr>
    <tr>
      <td>gr<sub>γ</sub>(L) → gr<sub>δ</sub>(L) and its Abelian cokernel</td>
      <td><code>lowerCentralToDimensionGraded</code>, <code>DimensionGradedCokernel</code></td>
      <td><code>DimensionSubring/Graded.lean</code></td>
    </tr>
    <tr>
      <td>ideal generated by a Lie ideal</td>
      <td><code>UEA.idealOfLieIdeal R L I</code></td>
      <td><code>UniversalEnveloping/Quotient.lean</code></td>
    </tr>
    <tr>
      <td>enveloping-algebra action</td>
      <td><code>UEA.representation R L M</code></td>
      <td><code>UniversalEnveloping/Adjoint.lean</code></td>
    </tr>
    <tr>
      <td>ordered PBW map</td>
      <td><code>PBW.orderedPBWMap R L ι b</code></td>
      <td><code>PBW/FreeModuleStatement.lean</code></td>
    </tr>
    <tr>
      <td>factor-two theorem</td>
      <td><code>DegreeFour.twoDeltaFourProperty</code></td>
      <td><code>DimensionSubring/DegreeFour.lean</code></td>
    </tr>
    <tr>
      <td>odd metabelian theorem and its corollaries</td>
      <td>
        <code>MetabelianTwoFactor.nilpotent_dimensionSubring_eq_bot</code>,
        <code>MetabelianTwoFactor.odd_dimensionSubring_le_lowerCentralSeries</code>,
        <code>MetabelianTwoFactor.dimensionSubringOmega_eq_lowerCentralSeriesOmega</code>,
        <code>MetabelianTwoFactor.dimensionSubring_five_le_lowerCentralSeries_three</code>
      </td>
      <td><code>DimensionSubring/MetabelianTwoFactor.lean</code></td>
    </tr>
  </tbody>
</table>

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
LieRings/MainResults.lean        compiled summary of the principal results
LieRings/UniversalEnveloping/    augmentation, actions, relations, and quotients
LieRings/PBW/                    PBW theorems, embeddings, and supporting constructions
LieRings/DimensionSubring/       dimension-subring results, including degrees four and five
LieRings/Metabelian/             free metabelian and nilpotent Lie-ring models
LieRings/Homological/            Lie homology, Hopf formulas, and dimension-factor descriptions
LieRings/Graded/                 associated graded Lie algebras of filtrations
LieRings/LinearAlgebra/          supporting integral linear algebra
LieRings/Examples/               short, copyable compiled examples
lit/{cnt,met,lie,hml}/           mathematical manuscripts organized by topic
lit/pbw/                         supporting PBW reference material
```
