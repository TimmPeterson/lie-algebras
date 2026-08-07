# Lie rings in Lean 4

This package develops foundational facts about Lie algebras over commutative rings, especially Lie
rings (the case `R = ℤ`). It uses mathlib's definitions of Lie algebras and universal enveloping
algebras throughout.

Current status:

- the augmentation ideal and Lie dimension subrings are defined;
- `U(L/I) ≃ U(L)/⟨I⟩` is proved for every Lie ideal `I`;
- the low-degree theorem `δ₂(L) = γ₂(L)` is proved over every commutative ring, without PBW;
- the integral low-degree theorem `δ₃(L) = γ₃(L)` is proved for every Lie ring;
- for every free Lie ring over `ℤ`, `δₙ(F) = γₙ(F)` is proved in every degree;
- the adjoint action of `U(L)` and the identity `A · 𝜔(L)^n = [A,ₙL]` are proved;
- `[δₙ(L),L] = γₙ₊₁(L)` and `[δₘ(L),δₙ(L)] ⊆ γₘ₊ₙ(L)` are proved over every commutative ring;
- complete PBW is proved for Abelian Lie algebras as `U(L) ≃ₐ[R] SymmetricAlgebra R L`;
- for a free underlying module, ordered PBW monomials are proved to span `U(L)`;
- the Cartan--Eilenberg triangular action is implemented degree by degree, and its ordered-word
  evaluation property is proved;
- the Higgins--Baer obstruction is defined from the canonical free presentation; its tensor and
  symmetric rows are exact, `C(M) → K(M)` is onto, and obstruction vanishing makes it an
  equivalence; the obstruction is proved to vanish for every Abelian group, and consequently
  Higgins's concrete commutator structure `K(M)` is universal;
- for every Lie ring `L`, the canonical map `L → U_ℤ(L)` is proved injective, with no basis,
  freeness, flatness, or representation parameter;
- the quotient reduction and free-presentation infrastructure for `δ₅(L) ⊆ γ₄(L)` are
  formalized, including relation truncation, finite tagged generator-word packets, exact
  associative components through weight four, semantic bracket-weight factors, and a proved
  well-founded collector recursion whose exact normal form is connected to the finite ledger;
  the integral scalar/linear/quadratic symbols of that ledger are now extracted exactly, while
  the final terminal-packet-to-certificate classification is not yet proved;
- the general PBW isomorphism is not yet proved. Nothing else in the package assumes it.

There are no `sorry` declarations.

## Build

From this directory, run:

```bash
lake build
```

The package is pinned to Lean 4 and mathlib `v4.29.0`.

## Mathematical notation in Lean

For a commutative ring `R` and a Lie algebra `L`:

| Mathematics | Lean |
|---|---|
| `U_R(L)` | `UEA R L` |
| `ι : L → U_R(L)` | `UniversalEnvelopingAlgebra.ι R` |
| augmentation `ε` | `UEA.augmentation R L` |
| augmentation ideal `𝜔(L)` | `UEA.augmentationIdeal R L` |
| `δₙ(L) = ι⁻¹(𝜔(L)^n)` | `dimensionSubring R L n` |
| `γₙ₊₁(L)` | `lowerCentralSeries R L n` |
| `[A,ₙL]` | `LieSubmodule.lcs n A` |

The only indexing point to remember is that mathlib starts its lower central series at zero:
`lowerCentralSeries R L 0 = L = γ₁(L)`.

## Applying dimension centrality

Import the centrality file:

```lean
import LieRings.DimensionSubring.Centrality
```

If your index is written as `n + 1`, apply the theorem without any side condition:

```lean
example (L : Type*) [LieRing L] [LieAlgebra ℤ L] (n : ℕ) :
    ⁅dimensionSubring ℤ L (n + 1), (⊤ : LieIdeal ℤ L)⁆ =
      lowerCentralSeries ℤ L (n + 1) :=
  dimensionSubring_bracket_eq_lowerCentralSeries ℤ L n
```

This says exactly `[δₙ₊₁(L),L] = γₙ₊₂(L)`.

If you already have a conventional positive index `1 ≤ n`, use:

```lean
dimensionSubring_bracket_eq_lowerCentralSeries_of_pos ℤ L hn
```

This says `[δₙ(L),L] = γₙ₊₁(L)`.

For the mixed commutator theorem, use:

```lean
bracket_dimensionSubring_le_lowerCentralSeries ℤ L m n
```

Its shifted statement is
`[δₘ₊₁(L),δₙ₊₁(L)] ⊆ γₘ₊ₙ₊₂(L)`.

With conventional positive indices `hm : 1 ≤ m` and `hn : 1 ≤ n`, use
`bracket_dimensionSubring_le_lowerCentralSeries_of_pos ℤ L hm hn`; this says directly
`[δₘ(L),δₙ(L)] ⊆ γₘ₊ₙ(L)`.

The copyable, compiled examples are in
[`LieRings/Examples/DimensionCentrality.lean`](LieRings/Examples/DimensionCentrality.lean).

## Free Lie rings: all dimension subrings

Import:

```lean
import LieRings.DimensionSubring.FreeLie
```

For `F = FreeLieAlgebra ℤ X`, the theorem with Lean's zero-based lower-central indexing is:

```lean
FreeLieDimension.dimensionSubring_succ_eq_lowerCentralSeries X n :
  dimensionSubring ℤ F (n + 1) = lowerCentralSeries ℤ F n
```

This says exactly `δₙ₊₁(F) = γₙ₊₁(F)`. If the index is already written conventionally,
use:

```lean
FreeLieDimension.dimensionSubring_eq_lowerCentralSeries_pred X n :
  dimensionSubring ℤ F n = lowerCentralSeries ℤ F (n - 1)
```

No basis, ordering, or auxiliary representation is required. The proof follows the length-grading
argument in Bartholdi--Passi: bracketed words give the free-Lie filtration, ordinary words give the
free-associative augmentation filtration, and the integral canonical embedding separates their
homogeneous degrees. Copyable examples are in
[`LieRings/Examples/FreeLieDimensionSubring.lean`](LieRings/Examples/FreeLieDimensionSubring.lean).

## Lie quotients and the degree-two theorem

For `I : LieIdeal R L`, the canonical quotient formula is

```lean
UEA.quotientEquivLieIdeal R L I :
  UEA R (L ⧸ I) ≃ₐ[R] UEA R L ⧸ UEA.idealOfLieIdeal R L I
```

Here `UEA.idealOfLieIdeal R L I` is the two-sided ideal generated by
`UniversalEnvelopingAlgebra.ι R x` for `x : I`. No freeness hypothesis is needed.

The second dimension-subring theorem is applied by

```lean
dimensionSubring_two_eq_lowerCentralSeries_one R L
```

and states `δ₂(L) = γ₂(L)`. Recall that the Lean index `1` on the right denotes the
conventional term `γ₂`. Copyable examples are in
[`LieRings/Examples/QuotientAndDegreeTwo.lean`](LieRings/Examples/QuotientAndDegreeTwo.lean).

## The third dimension subring

For an arbitrary Lie ring, import `LieRings.DimensionSubring.DegreeThree` and apply:

```lean
dimensionSubring_three_eq_lowerCentralSeries_two L
```

Its statement is exactly

```lean
dimensionSubring ℤ L 3 = lowerCentralSeries ℤ L 2
```

that is, `δ₃(L) = γ₃(L)` in conventional notation. No finite-generation, freeness, or
torsion-freeness assumption is required. For elementwise use, rewrite the goal or hypothesis with
this equality. Copyable examples are in
[`LieRings/Examples/DegreeThree.lean`](LieRings/Examples/DegreeThree.lean).

## Degree five (work in progress)

Import `LieRings.DimensionSubring.DegreeFive` for the proved infrastructure toward
`δ₅(L) ⊆ γ₄(L)`. The global quotient reduction is

```lean
DegreeFive.dimensionSubring_five_le_lowerCentralSeries_three_of_quotient
```

and `DegreeFive.exists_freeDimensionFiveWitness` converts membership in `δ₅` into a canonical
free-presentation witness. Its relation difference is an actual finite sum `∑ nᵢ ι(rᵢ)uᵢ`, not
merely abstract ideal membership. `FreeDimensionFiveWitness.exists_lowWeightRelationLedger`
then gives the four exact word-length equations used by the unpublished PBW calculation.
`DegreeFive.lowPacketWeightSequence_complete` proves the exhaustive finite source table for
every placed relation packet of total weight below five; the specialized row theorems spell out
the permitted external-factor weights for relation rows of least weights one through four.
`DegreeFive.weightedPacketStep_wellFounded` proves termination with the full paper measure
`(4-s,r,I)`. `DegreeFive.FiniteTaggedCollector.normalForm` is the generic coefficient-retaining
normalizer, and its evaluation theorem proves that normalization preserves the represented
algebra element.

`DegreeFive.semanticPacketCollector` is the instantiated collector on actual filtered free-Lie
factors. Its terminal packets are proved PBW-ordered, both rewrite branches strictly descend,
and every adjacent swap preserves the exact enveloping-algebra value. The theorem

```lean
FinitePlacedRelationLedger.evaluate_semanticNormalForm_eq_relationDifference
```

states that collecting every row and weight-three remainder in the nested finite ledger still
evaluates exactly to `ι(lieLift) - highWord`.

The quadratic truncation `DegreeFive.QuadraticTensorTruncation P = ℤ ⊕ P ⊕ (P ⊗ P)` performs the
coefficient comparison without dividing by two. The theorem

```lean
freeAlgebraToQuadraticTensor_freeLieToFreeAlgebra
```

identifies the associative low symbol of every free-Lie element with its basis-free class-two
truncation `P ⊕ ⋀²P`, using the integral alternation `x ∧ y ↦ x ⊗ y - y ⊗ x`. Associative words of
length at least three are proved to have zero symbol. Consequently

```lean
FinitePlacedRelationLedger.semanticNormalForm_lowSymbol_sum
```

turns the semantic normal form into an exact finite integral equation whose right side is the
class-two symbol of `lieLift`; the witness's augmentation-five word contributes zero.

The arbitrary enveloping factors have also been eliminated. The theorem

```lean
FreeDimensionFiveWitness.exists_finitePlacedRelationLedger
```

produces a nested, genuinely finite `Finsupp` of marked generator words.
`FinitePlacedRelationLedger.initialPacketValue_eq_relationDifference` identifies its evaluation
in `U(FreeLie(L))` exactly with `ι(lieLift) - highWord`. Row normalization, the adjacent PBW
swap, and their correction terms are equality-level theorems. `FilteredLieFactor` records the
actual free-Lie factor together with its positive bracket weight; its bracket constructor proves
that correction weights add, and lower associative components are proved to vanish.

The invariant certificate criterion and its global assembly are fully proved, but the finite
classification that turns the terminal low-symbol equation into that certificate is still
missing. Consequently this section does not yet export an unconditional theorem named
`dimensionSubring_five_le_lowerCentralSeries_three`.

## Applying the adjoint-module identity

For a Lie module `M`, a Lie submodule `N`, and `n : ℕ`, the theorem

```lean
UEA.actionSubmodule_augmentationIdeal_pow_eq_lcs R L M N n
```

states

```text
span_R {u • m | u ∈ 𝜔(L)^n, m ∈ N} = [N,ₙL].
```

Here `u • m` is written internally as `UEA.representation R L M u m`. For an ideal `A` of `L`,
take `M = L` and `N = A`.

## PBW statement

For an Abelian Lie algebra, the theorem is complete and basis-free:

```lean
PBW.abelianEquivSymmetric R L : UEA R L ≃ₐ[R] SymmetricAlgebra R L
```

The simplification theorem `PBW.abelianEquivSymmetric_ι` says that this equivalence sends the
canonical image of `x : L` to `SymmetricAlgebra.ι R L x`.

For the next, non-Abelian target, let `b : Module.Basis ι R L` be an ordered basis.

```lean
PBW.orderedPBWMap R L ι b : MvPolynomial ι R →ₗ[R] UEA R L
```

sends a commutative monomial to the corresponding ordered product of basis elements in `U(L)`.
The proposition

```lean
PBW.FreeModulePBW R L ι b
```

means precisely that this map is bijective. Its surjectivity half is the theorem
`PBW.orderedPBWMap_surjective R L ι b`. The representation-theoretic half is also complete:
`PBW.TriangularRepresentation.freeModulePBW` proves PBW from the Cartan--Eilenberg action, and
`PBW.canonicalMap_injective_of_freeModulePBW` derives the canonical embedding.

The recursive candidate action is `PBW.cartanAction`. Its ordered-product theorem is
`PBW.cartanBasisWordAction_sortedExponent_apply_one`. The remaining proof obligation is precisely
`PBW.CartanActionLieCompatible`, the Jacobi calculation showing that this candidate respects the
Lie bracket. See
[`ROADMAP.md`](ROADMAP.md) for the proof plan.

For Lie algebras over `ℤ`, the unconditional embedding theorem is now available directly:

```lean
PBW.canonicalMap_injective_int L :
  Function.Injective (UniversalEnvelopingAlgebra.ι ℤ : L → UEA ℤ L)
```

Its only hypothesis is `[LieRing L]`. The older
`PBW.TriangularRepresentation.canonicalMap_injective` remains useful over a general base ring when
a triangular representation is already available.

For the later extension beyond free modules, `PBW.flat_int_of_torsionFree` records that a
torsion-free Abelian group is a flat `ℤ`-module, and
`PBW.flat_of_torsionFree_of_dedekind` gives the Dedekind-domain version. The Govorov--Lazard
direct-limit transport of PBW is not yet in mathlib or this package. It will handle the
torsion-free case; the arbitrary integral case additionally needs Higgins's cyclic-module and
direct-limit argument. `PBW.Higgins` now contains the canonical presentation, the ideals `K(P)`,
`Q̃`, and `Z`, the obstruction `B(M)`, exact tensor and symmetric presentation rows, and the
full comparison `C(M) → K(M)` (surjective always and an equivalence when `B(M)=0`). It also proves
that `K(M)` is the two-sided ideal generated by the degree-one commutators, establishes
`K(P)Q̃ + Q̃K(P) ⊆ Z`, and descends commuting left and right tensor actions to `C(M)`. Both `C(M)`
and `K(M)` are packaged as Higgins Lie structures satisfying (L1)--(L3), and the comparison is
proved to preserve the actions and bracket. The bracket is proved independent of presentation
lifts, and the uniqueness half of the universal property of `C(M)` is complete. The file also proves
`PBW.Higgins.obstructionVanishes_of_projective`. The companion file `PBW.HigginsCyclic` proves
Higgins's cyclic-sum theorem: `PBW.Higgins.obstructionVanishes_of_directSumOfCyclic` gives
`B(M)=0` whenever the underlying Abelian group is an internal direct sum of cyclic groups.
`PBW.HigginsDirectLimit` then proves finite-stage compatibility for the directed union of finitely
generated subgroups and exports `PBW.Higgins.obstructionVanishes_all M`: `B(M)=0` for every
Abelian group. `PBW.HigginsPBW` transports this equivalence to the concrete commutator structure
and proves that `PBW.Higgins.tensorCommutatorLieStructure M` is universal for every Abelian group.
`PBW.HigginsFiltration` constructs the defining ideal `J`, its complete Higgins filtration `J(n)`,
the graded pieces `J(n)/J(n-1)`, and the degree-shifting left and right generator maps. It assembles
those maps into commuting tensor-algebra actions on the direct sum of graded pieces, defines the
bilinear relation bracket, and proves all three Higgins identities (L1)--(L3). The resulting
`PBW.Higgins.higginsFiltrationLieStructure` feeds into `PBW.HigginsEmbedding`, which constructs
the leading-term comparison, proves it injective by universality, descends the filtration in degree
one, and proves the parameter-free integral embedding theorem above.

To apply the cyclic-sum theorem, provide submodules `C i`, prove `DirectSum.IsInternal C`, and give
an `IsAddCyclic (C i)` instance for every summand. Package these data as
`PBW.Higgins.IsDirectSumOfCyclic M`; the theorem then returns the precise library predicate
`PBW.Higgins.ObstructionVanishes M`, definitionally the statement that the Baer obstruction
quotient is subsingleton.

For an arbitrary Abelian group no decomposition data are necessary:
`PBW.Higgins.obstructionVanishes_all M` proves the same predicate directly from
`[AddCommGroup M]`.

Two short, compiled uses of this API are in
[`LieRings/Examples/PBW.lean`](LieRings/Examples/PBW.lean).

## File layout

```text
LieRings/
  UniversalEnveloping/Basic.lean      augmentation and induction
  UniversalEnveloping/Adjoint.lean    U(L)-action and A · 𝜔ⁿ identity
  UniversalEnveloping/Quotient.lean   U(L/I) ≃ U(L)/⟨I⟩
  DimensionSubring/Basic.lean         definition of δₙ
  DimensionSubring/Centrality.lean    centrality theorems
  DimensionSubring/DegreeTwo.lean     δ₂ = γ₂ without PBW
  DimensionSubring/FreeLie.lean       δₙ(F) = γₙ(F) for free Lie rings over ℤ
  DimensionSubring/DegreeFive/LowSymbols.lean  integral symbols through tensor degree two
  DimensionSubring/DegreeFive/LowSymbolExtraction.lean  exact low-symbol ledger equation
  PBW/Reduction.lean                  rigorous PBW reductions
  PBW/Abelian.lean                    complete Abelian PBW theorem
  PBW/FreeModuleStatement.lean        exact ordered PBW map
  PBW/Surjectivity.lean               ordered monomials span U(L)
  PBW/TriangularRepresentation.lean   triangular action implies PBW and L ↪ U(L)
  PBW/CartanEilenberg.lean            recursive Cartan--Eilenberg action
  PBW/Conditions.lean                 free/torsion-free/Dedekind flatness bridges
  PBW/Higgins.lean                    integral Baer obstruction and exact-sequence infrastructure
  PBW/HigginsCyclic.lean              B(M)=0 for direct sums of cyclic Abelian groups
  PBW/HigginsDirectLimit.lean         directed finite-stage argument; B(M)=0 for every group
  PBW/HigginsPBW.lean                 B(M)=0 implies universality of the concrete K(M)
  PBW/HigginsFiltration.lean          filtration and its complete Higgins Lie structure
  PBW/HigginsEmbedding.lean           filtered proof that every Lie ring embeds in Uℤ(L)
  Examples/DimensionCentrality.lean   copyable examples
  Examples/QuotientAndDegreeTwo.lean  quotient and δ₂ examples
  Examples/FreeLieDimensionSubring.lean  free-Lie dimension-subring examples
  Examples/PBW.lean                   copyable PBW examples
```
