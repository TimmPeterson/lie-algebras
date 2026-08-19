# Aristotle task: complete the global terminal-cycle certificate

## 1. Deliverable

Work in the existing `lie-rings` Lean project and edit only
`Aristotle/BigTheorem.lean` unless a helper lemma in that same file is useful.
Fill the single `sorry` in
`LieRings.Aristotle.globalFactorTwoChain_cycle_and_external_coordinate`.

Preserve the theorem statement exactly. You may add a small number of direct
helper lemmas above it in the same file. Do not add axioms, theorem parameters,
typeclass assumptions, `admit`, further `sorry` declarations, `native_decide`,
or any conditional hypothesis standing for part of the closed-square proof.

Aristotle's Lean-file mode is designed to fill `sorry` placeholders. This
entry file therefore deliberately contains one placeholder and imports the
project modules that define its complete interface. It must be submitted from
the root of this project so that import resolution uses the pinned Lake
environment:

- Lean `v4.29.0`;
- mathlib `v4.29.0`;
- package root: the directory containing `lakefile.toml`;
- target file: `Aristotle/BigTheorem.lean`.

If the Aristotle client offers repository mode, upload the whole current
repository and select this file as the task. If it offers `prove_file`, invoke
it on this path from the project root; the imported project modules are
essential and must not be replaced by informal stubs.

## 2. Exact formal target

For `3 ≤ n`, a finite metabelian Lie ring with cyclic top-layer data, and a
`GoverningWitness n L data a`, prove that the already defined manuscript
packet `w.globalFactorTwoChain n L data (by omega)` is a cycle and that its
canonical primitive has the external governing coordinate:

```lean
∃ hcycle : Koszul.dOne
    (terminalSourcePresentation n L data (by omega)) 1
      (w.globalFactorTwoChain n L data (by omega)) = 0,
  terminalEval n L data
      (terminalSourceCyclePreimage n L data (by omega)
        ⟨w.globalFactorTwoChain n L data (by omega), hcycle⟩) =
    (w.externalMarkedWord n L data (by omega)).value
```

This is not an arbitrary cycle-existence statement: the theorem fixes the
cycle's underlying chain to the terminal factor-two packet obtained from the
occurrence-labelled global closed-square trace. Its boundary and primitive
must be read from that same signed occurrence list.

The statements following the placeholder in `BigTheorem.lean` are already
proved. They mechanically verify the implication

```text
this terminal-cycle certificate
  => GoverningWitness.eq_zero for every n >= 3
  => ReducedTopLayerVanishes
  => (ReductionProperty + PassiSickingProperty)
       => dimensionSubring Z L (2*n+1) = bottom.
```

Thus proving the one target really completes the entire desired implication;
no additional mathematical assumption is hidden in the wrappers.

## 3. Informal source of the proof

The copied file
`Aristotle/metabelian_dimension_vanishing_fixed_2.tex` is the authoritative
informal proof. The relevant portion is:

1. lines 807--1278: the **closed-square row lemma**;
2. lines 846--927: construction of the packet chains and the identical
   indexed horizontal and vertical reads;
3. lines 1020--1125: the saturated occurrence trace, cuts, internal gluing,
   and stopping rules;
4. lines 1127--1160: construction of the signed factor-two list `B`, its
   projected Smith expansion `B^(n)`, the cycle proof for `chi_n`, and the
   primitive read `Q_n(chi_n)`;
5. lines 1162--1210: the exhaustive terminal PBW/Hall classification;
6. lines 1212--1275: application of the single read map `P`, finite Stokes,
   diagonal cancellation, and vanishing of the terminal discrepancy;
7. lines 1280--1325: **PBW assembly** and intermediate packet vanishing.

The formal target packages the output of precisely this calculation. In the
manuscript, `chi_n` is the cycle, `Q_n(chi_n)` is the terminal primitive read,
and the closed-square identity identifies it with the outside governing
coordinate after the intermediate diagonals vanish.

## 4. Lean dictionary

The principal manuscript-to-Lean correspondences are:

| Manuscript object | Lean declaration |
| --- | --- |
| governing element `Theta = theta` | `GoverningWitness.theta` |
| full marked occurrence trace | `globalLabelledComparisonTrace` |
| complete upper vertical occurrences | `globalVerticalOccurrences` |
| complete lower horizontal/vertical occurrences | `globalHorizontalVerticalOccurrences` |
| factor-two cut `B` | `factorTwoPreSmithOccurrences` |
| projected/Smith packet `B^(n)` | `globalFactorTwoChain` |
| its placed word | `globalFactorTwoPlacedWord` |
| its one-factor primitive | `globalFactorTwoPrimitive` |
| terminal presentation `D_n -> A_n` | `terminalSourcePresentation` |
| terminal coordinate in `C` | `terminalEval` |
| outside governing term | `externalMarkedWord` |
| canonical realization of a terminal cycle | `terminalSourceCyclePreimage` |
| intermediate chain `chi_k` from the actual cut | `globalPacketChain` |
| indexed packet chain `chi_k` | `packetChain` |
| `Phi_k = T_k ∘ d` indexed read | `indexed_packet_reads` |

The formal target uses a cycle in the source presentation rather than merely
an element of the projected symmetric square. This is intentional: a value of
type `Koszul.cyclesOne` contains the genuine zero-boundary proof, and
`terminalSourceCyclePreimage` realizes its primitive using full relations.

## 5. High-value compiled facts

The following facts are already proved and should be reused rather than
reconstructed.

### Global factor-two packet

- `GoverningWitness.dOne_globalFactorTwoChain_eq_globalVerticalCutRead`
  rewrites the boundary of `globalFactorTwoChain` as the conditional
  factor-two read on the complete vertical occurrence ledger.
- `GoverningWitness.rightSymbol_globalFactorTwoPlacedWord` identifies the
  same boundary with the factor-two PBW symbol of the same placed word.
- `GoverningWitness.pbwPrimitive_globalFactorTwoPlacedWord` identifies its
  one-factor PBW primitive without changing the occurrence list.
- `GoverningWitness.terminalSourcePrimitive_globalFactorTwoChain` computes
  its source primitive up to one genuine aggregate full relation.
- `GoverningWitness.globalFactorTwoPrimitivePreimage_coe` and
  `GoverningWitness.terminalEval_globalFactorTwoCycle_eq_primitive` are
  available once the zero-boundary proof is supplied.

### Governing PBW coefficients

- `rightSymbol_theta_terminal_eq_zero` is the terminal factor-two governing
  coefficient.
- `GoverningWitness.T_componentTraceFactor_eq_zero` is the complete
  nonterminal governing coefficient after every factor-lowering correction.
- `GoverningWitness.rightSymbol_globalVerticalComponentValue_eq_zero` is the
  global, word-valued terminal factor-two consequence of the exact horizontal
  telescope. It is an aggregate theorem, not a pointwise statement.

### Global closed square and terminal partition

- `GoverningWitness.theta_eq_outsideInitialWord_add_globalVerticalComponentValue`
  is the exact word-valued horizontal telescope.
- `GoverningWitness.globalVerticalRead_eq_globalHorizontalVerticalRead` is
  the occurrence-level read form of the uncut square.
- `GoverningWitness.globalVerticalLowerMarkedRead_eq_internal` cancels all
  continuing lower-mark occurrences by numbered internal gluing.
- `GoverningWitness.externalHomogeneousRead_eq_globalVerticalComponentRead`
  and `GoverningWitness.externalHomogeneousRead_eq_terminalComponentRead`
  identify the two global reads without erasing ancestry early.
- `GoverningWitness.terminalComponentRead_wall_partition` and
  `GoverningWitness.externalHomogeneousRead_wall_partition` give the
  exhaustive terminal-family decomposition.
- `GoverningWitness.indexed_packet_reads` gives both `Phi` and `T ∘ d`
  on literally identical packet occurrences and coefficients.
- `GoverningWitness.T_dOne_globalPacketChain_eq_component_cut` gives the
  vertical read directly on an actual global diagonal cut.

### Final consumers

- `GoverningWitness.eq_zero_of_terminalCycleSourceValue` consumes exactly
  the existential certificate requested by the target.
- `terminalEval_terminalSourceCyclePreimage_eq_zero` is Point 6: every
  genuine terminal source cycle has zero terminal coordinate.
- `reducedTopLayerVanishes_of_stepSeven` supplies the already-formalized
  degree-three and degree-five cases and reduces all higher degrees to the
  governing-witness theorem.
- `finite_metabelian_odd_dimensionSubring_eq_bot_of_stepSeven` performs the
  final composition with Reduction and Passi--Sicking.

Use `#check` or `#print` in a temporary local buffer if an implicit argument
is unclear. Do not replace a failed application by weakening the target.

## 6. Intended proof architecture

The expected construction is the following.

1. Use `w.globalFactorTwoChain n L data hn` itself as the terminal packet.
   This is the formal `B^(n) = chi_n` fixed by the theorem statement; do not
   replace it by an unrelated or merely boundary-equivalent cycle.
2. Prove its boundary is zero from the *aggregate* global closed-square
   calculation. Rewrite its boundary with
   `dOne_globalFactorTwoChain_eq_globalVerticalCutRead`. The remaining
   factor-two cut read must be compared with the complete terminal PBW symbol
   while retaining the intermediate diagonal corrections.
3. Cancel every intermediate diagonal by the common occurrence read:
   `indexed_packet_reads` gives `Phi_k = T_k(d chi_k)`, and the governing
   coefficient theorem kills the complete `T_k` read. This is the formal
   counterpart of equations (indexed-horizontal-read),
   (indexed-vertical-read), and (evaluated-complete-ledger) in the manuscript.
4. Use the factor-two primitive theorem on the same signed list. Full source
   placement discrepancies are handled by
   `terminalSourcePrimitive_globalFactorTwoChain`; their terminal evaluation
   is zero. Do not replace a lower-context homogeneous component by a full
   relation.
5. Conclude that the canonical source-cycle preimage has the external marked
   coordinate and return the cycle together with this equality.

The corrected manuscript proves that `globalFactorTwoChain` itself has zero
boundary: its symmetric boundary is the projected factor-two PBW symbol of
`Theta`. Consequently a proposed proof that needs to alter the chain has not
yet matched the occurrence list `B^(n)` used in lines 1127--1158 of the
manuscript.

## 7. Forbidden shortcuts

Do not use any of the following.

- `rawCutoffExceptionalRelationLeftChain` or any construction defined as a
  known-boundary chain minus the subset-tail chain. In the final assembly
  that route cancels the very chain whose cycle is being constructed.
- A pointwise Smith-head replacement at lower contexts. It is valid only at
  the top context; the lower-context terms are the intermediate
  diagonal/`Phi`/`T` terms in the manuscript.
- A theorem asserting that an arbitrary signed relation-word family has zero
  terminal obstruction. The complete marked occurrence trace is essential.
- Treating a homogeneous component of a relation as though it were itself an
  element of the relation module.
- Proving only equality after equal-valued occurrences have been merged.
  Source path, output number, sign, and multiplicity must remain attached
  until the indexed sums are compared.
- New assumptions, local axioms, opaque `unsafe` escapes, or changes to the
  theorem statement and consequence wrappers.

The older `RawCutoff*` files remain in the repository only as historical
work and as a source of small independent algebraic lemmas. They are not the
architecture of this proof.

## 8. Verification

From the package root, run:

```bash
lake build LieRings.DimensionSubring.MetabelianVanishing.GlobalTerminalCorrection
lake build LieRings.DimensionSubring.MetabelianVanishing.Main
lake env lean -R . Aristotle/BigTheorem.lean
```

The completed file must report no errors and no `declaration uses sorry`
warning. Then check:

```bash
rg -n "sorry|admit|axiom" Aristotle/BigTheorem.lean
```

Only explanatory prose may mention those words. Finally, add temporary
`#print axioms` commands if needed to confirm that the target and the final
wrapper use only the project's expected foundational axioms; remove the
temporary commands before returning the file.

## 9. Main-development resumption marker

This Aristotle preparation is an isolated subtask. The main implementation
was paused immediately after adding and compiling
`GoverningWitness.dOne_globalFactorTwoChain_eq_globalVerticalCutRead` in
`GlobalTerminalCorrection.lean`. The next main-development task is the
aggregate intermediate-diagonal cancellation comparing the actual global cut
reads with the complete component trace. No main proof file or checklist was
changed while preparing this handoff.
