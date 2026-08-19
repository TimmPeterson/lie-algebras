# Direct implementation plan for the corrected closed-square proof

The mathematical source of truth for this plan is
`lit/obstacle/metabelian_dimension_vanishing_fixed_2.tex`, especially the
closed-square row lemma and PBW assembly.  The implementation must follow its
global occurrence/cell calculation.  The old local exceptional-chain
decomposition is not part of the new proof.

## Contract

The final public theorem must be
`finite_metabelian_odd_dimensionSubring_eq_bot`, with exactly the Reduction
Property and the Passi--Sicking Property as deferred theorem inputs.  There
must be no `sorry`, `admit`, new axiom, conditional Step-7 hypothesis, or
extra mathematical assumption.

The following architecture is frozen.

- Keep all compiled infrastructure through
  `MetabelianVanishing/MarkedCollector.lean`.
- Reuse the already proved tower, Koszul, transgression, Smith, quadratic
  character, canonical quadratic PBW block, CE-row, triangular-basis, marked
  transfer, marked truncation, and termination results.
- Preserve the old downstream files in the dirty worktree, but do not use the
  `RawCutoffExceptionalRelationLeftChain` subtraction or any theorem whose
  input is the missing local relation-left chain.
- Do not attempt to prove that an isolated homogeneous component read is a
  relation or vanishes.  It cancels only in the global two-filtered ledger.
- New definitions and lemmas must correspond directly to an object, equality,
  partition, or read appearing in the corrected manuscript.

## 0. Freeze and audit the reusable boundary

- [x] Compile `QuadraticPBWBlock.lean` independently.
- [x] Compile `RelativeRows.lean` independently.
- [x] Compile `MarkedCollector.lean` independently.
- [x] Confirm that `MarkedRow`, `ProvenancedRow`, exact transfer/truncation
  identities, occurrence labels, and a well-founded row measure are available.
- [x] Add a small audit module importing only the frozen boundary and checking
  the exact APIs used by the new proof.

Acceptance: the audit module compiles without importing
`ClosedSquare.lean` or any `RawCutoff*` module.

## 1. Indexed packet occurrences (J_k) and supported indices (Delta_k)

- [x] Define a labelled packet-occurrence type carrying the full relation,
  coefficient, quotient mark, and homogeneous ordinary inputs.
- [x] Define its realization in
  (K_{m_k}(D_k\to A_k)_1), retaining equal-valued occurrences separately.
- [x] Define the finite occurrence list (J_k) directly from the complete
  factor-(m_k) collection.
- [x] Define (chi_k) as the sum of the realization of (J_k), so the
  occurrence presentation is definitional.
- [ ] Prove that (partialchi_k) is the complete projected
  factor-(m_k) PBW symbol of the governing witness.
- [x] Define (Delta_k\subseteq J_k): all ordinary inputs have weight one and
  the relation's weight-(k) component is the distinguished (M)-input.
- [x] Prove the indexed horizontal-read formula
  [
    Phi_k(f_kchi_k)=
    sum_{alpha\in\Delta_k}c_alpha
      [\rho_{alpha,k},x_{alpha,1},\ldots,x_{alpha,m_k-1}].
  ]
- [x] Prove the coefficient-preserving bijection between (Delta_k) and all
  formally supported summands of (T_k(partialchi_k)), including the
  converse direction and zero-valued supported copies.

Acceptance: one capstone theorem packages both indexed read formulas with
identical indices, coefficients, and orientations.

## 2. The two literal operations (V) and (H)

- [x] Define (H) as one marked quotient-tower truncation on signed occurrence
  lists; give unmarked outputs mark (0) in the termination measure.
- [x] Define (V) as the complete deterministic factor/PBW pass: principal
  outputs remain at factor (p), every full-relation correction is returned
  to factor (p-1), and no correction is discarded.
- [x] Prove linearity of (H) and (V) on finitely supported occurrence lists.
- [x] Prove literal evaluation preservation for each operation.
- [x] Prove strict descent of every generated output for
  ((p,\text{unresolved adjacent pairs},k)).
- [x] Prove (H(VR)=V(HR)) after fixed canonical placed-basis expansion,
  treating disjoint transfers, ordinary Jacobi, relation Jacobi, and the
  transfer--truncation square.
- [x] State explicitly that raw route labels are not equated; equality is in
  the canonically expanded incidence group.

Acceptance: the commutation theorem is unconditional and coefficientwise.

## 3. Comparison cells and the finite saturated trace

- [x] Define a comparison cell based at (R), with oriented incidences
  [
  h(R),\quad-h(VR),\quad-v(R),\quad v(HR).
  ]
- [x] Prove that its evaluated boundary is (HVR-VHR=0).
- [x] Define the finite saturated closure from every labelled initial row by
  well-founded recursion on the existing lexicographic measure.
- [x] Expand every full relation in the tagged triangular basis, construct the
  literal double-support governing initial list, prove that forgetting its
  source labels is exactly the triangularized provenance initial ledger, and
  prove that this ledger evaluates exactly to the governing element
  (\(\Theta\)).
- [x] Prove the prefix ledger separately, solely to show that no raw output
  occurrence disappears.
- [x] Construct the occurrence-level complete vertical frontier below every
  comparison cell and prove that forgetting its paths is exactly (V R).
- [x] Prove occurrence-level terminality of that frontier and define the
  disjoint factor-two, intermediate-diagonal, and outside-one families.
- [x] Define internal gluing after canonical expansion and prove that every
  parent-left basis coefficient is the negative of the aggregate coefficient
  on its retained numbered horizontal successors.
- [x] Prove that saturation attaches each non-cut numbered successor to
  exactly one adjacent cell, so every non-cut copy occurs exactly twice.
- [x] Define the factor-two and diagonal cuts and retain the side containing
  the factor-one frontier.

Acceptance: a finite-Stokes theorem identifies the external boundary with the
sum of the retained cell boundaries and proves its evaluated sum is zero.

## 4. Exhaustive stopping rules and silent occurrences

- [x] Formalize the five stopping rules from the corrected manuscript.
- [x] Prove that every nonterminal syntactic row has an available factor,
  Smith, Hall, or truncation step.
- [x] Put every factor-one bracket tree into the fixed integral Hall/comb form.
- [x] Prove that a nonzero metabelian comb has at most one input in
  (M=F_{\ge2}).
- [x] Partition all terminal coefficient copies by the number and source of
  their (M)-inputs.
- [x] Prove silence for spectators, wrong total weight, two (M)-inputs,
  ordinary (M)-input full-commutator terms, and all-weight-one
  full-commutator terms.
- [x] Prove that the only nonsilent external families are terminal factor one,
  diagonal horizontal, factor two, and diagonal vertical.

Acceptance: the frontier partition is a disjoint exhaustive sum decomposition,
not merely a pointwise classification of possible values.

## 5. The exact factor-two occurrence list

- [x] Define the signed pre-Smith factor-two list (B).
- [x] Define (B^{(n)}) by projection to (D_n\otimes A_n), deletion of zero
  outputs, and canonical basis expansion.
- [x] Prove a sign- and multiplicity-preserving bijection between
  (B^{(n)}) and the occurrence presentation of (chi_n).
- [ ] Prove (partialchi_n=0) from the vanishing projected factor-two PBW
  symbol.
- [x] Prove that projection to (A_n) loses no possible one-factor descendant
  of weight (n+1).
- [ ] Feed exactly (B^{(n)}), without rebuilding it, to the canonical
  quadratic PBW block and identify its oriented primitive read as
  (-Q_n(chi_n)).

Acceptance: the factor-two boundary and quadratic primitive are definitionally
or theoremically tied to the same signed occurrence list.

## 6. One terminal read map and the closed-square identity

- [x] Define the single linear read map (mathcal P): complete deterministic
  PBW collection, followed by one-factor weight-(n+1) projection to (C).
- [x] Prove that (mathcal P) is unchanged across every internal gluing.
- [ ] Identify its four external reads, with orientations, as
  [
  iota_C(pr_{1,n+1}Theta),\quad
  -Phi_k(f_kchi_k),\quad
  -Q_n(chi_n),\quad
  +T_k(partialchi_k).
  ]
- [ ] Apply finite Stokes to prove the unconditional closed-square identity
  [
  0=iota_C(pr_{1,n+1}Theta)
    -\sum_{k=2}^{n-1}Phi_k(f_kchi_k)-Q_n(chi_n)
    +\sum_{k=2}^{n-1}T_k(partialchi_k).
  ]
- [ ] Verify the (n=2) empty-diagonal case through the same theorem.
- [ ] Use PBW support and the governing coefficients to prove every
  (T_k(partialchi_k)=0).

Acceptance: export the manuscript's closed-square row lemma with no local
exceptional-chain hypothesis.

## 7. PBW assembly and unconditional Step 7

- [ ] Identify the outside one-factor read with (zeta/q+\mathbb Z).
- [ ] Identify (Q_n(chi_n)) with
  (-\eta_n(L_1\operatorname{Sym}^2(pi_n)[chi_n])).
- [ ] Export the PBW normal-form equality exactly as in the corrected proof.
- [ ] Apply intermediate packet vanishing and the Passi--Sicking input.
- [ ] Prove unconditional `GoverningWitness.eq_zero` for (3\le n).
- [ ] Prove unconditional `reducedTopLayerVanishes`.

Acceptance: Step 7 has no correction-chain, relation-left-chain, terminal
coordinate, or other conditional hypothesis.

## 8. Final reduction and audit

- [ ] Rewire `Reduced.lean`, `Main.lean`, and `LieRings.lean` to the new
  unconditional Step-7 theorem.
- [ ] Export `finite_metabelian_odd_dimensionSubring_eq_bot` with exactly the
  Reduction Property and Passi--Sicking Property as deferred inputs.
- [ ] Compile every new module independently.
- [ ] Run `assert_no_sorry` on the closed-square lemma, Step 7, reduced
  theorem, and public theorem.
- [ ] Run `#print axioms` and verify only expected foundational axioms.
- [ ] Run the complete `lake build`.
- [ ] Update `LieRings/Audit.lean` and mark every checklist item complete.

Acceptance: the public theorem is unconditional apart from the two authorized
properties, and the entire project builds.
