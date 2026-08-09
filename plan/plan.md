# Direct Bartholdi--Passi plan for `2 delta_4 <= gamma_4`

## 1. Contract

The implementation will follow the proof of Theorem `deltan`, Theorem
`delta4`, and Corollary `2delta_4` in `lit/bartholdi-passi.tex`, specialized
to the only case needed here: associative degrees at most three and
`n = 4`.

The final new unconditional theorems must be:

```lean
theorem twoDeltaFourProperty : DegreeFive.TwoDeltaFourProperty

theorem dimensionSubring_five_le_lowerCentralSeries_three
    (L : Type u) [LieRing L] :
    dimensionSubring ℤ L 5 ≤ lowerCentralSeries ℤ L 3
```

The second theorem is obtained by applying the already compiled standing
reduction to the first one.  No additional hypothesis may occur in either
statement.

This plan deliberately does **not** formalize more than the corollary uses:

- no general `deltan` theorem for arbitrary `n`;
- no Hall or Lyndon basis;
- no new invariant-factor/Smith-normal-form algorithm;
- no converse direction of Passi's description of `delta_4`;
- no second Smith presentation;
- no placed packets, semantic ledgers, or degree-five PBW calculation.

## 2. Code which is already complete and must survive cleanup

Keep the following compiled spine in `DimensionSubring/DegreeFour.lean`:

1. `FreeDimensionFourWitness` and
   `exists_freeDimensionFourWitness_gammaTwo`;
2. `FreeDimensionFourWitness.exists_relation_finsupp`, because the existing
   finite-support reduction uses it;
3. `normalFormValue`, `normalFormRow`, `NormalFormCertificate`, and
   `NormalFormCertificate.two_smul_mem_lowerCentralSeries_three`;
4. the first-Smith presentation:
   `FirstSmithIndex`, `firstSmithGenerator`, `firstSmithValue`,
   `firstSmithDiagonal`, the first-row decomposition of an arbitrary kernel
   relation, `exists_strictBracketCoordinates`, and
   `freeAlgebraFirstSmithEquiv`;
5. `firstSmithTail`, `firstSmithTail_mem_lieHigh_two`, and
   `firstSmithDiagonal_smul_value_mem_gammaTwo`;
6. `FiniteBartholdiPassiExtractionProperty`, the finite-to-arbitrary
   residual-finiteness passage, and
   `twoDeltaFourProperty_of_finite_extraction`;
7. the already compiled implication
   `DegreeFive.dimensionSubring_five_le_lowerCentralSeries_three`.

After an `rg` dependency check, remove the abandoned routes:

- `AdaptedPresentationDimensionFourWitness` and its word-packet machinery;
- its old component-two/component-three wrappers;
- `exists_freeDimensionFourWitness_gammaThree` and
  `exists_freeDimensionFourWitness_exactTwo` if the dependency check confirms
  that only the abandoned route uses them;
- the second-Smith definitions and lemmas;
- only obsolete placeholder declarations which are not used by the compiled
  implication.  In particular, keep
  `twoDeltaFourProperty_of_finite_extraction` and
  `dimensionSubring_five_le_lowerCentralSeries_three_of_finite_extraction`:
  these are the preserved reduction spine, not cleanup targets.

Compile immediately after this cleanup.  No new proof starts until the
preserved spine compiles.

## 3. The finite preabelian presentation already available

Fix a finite Lie ring `L`, put

```text
F   = CanonicalFreeLie L,
R   = ker (canonicalFreeLieEvaluation L),
I   = FirstSmithIndex L,
X_i = firstSmithGenerator i,
x_i = firstSmithValue i,
d_i = collectedDiagonal ... 1 i : ℕ,
e_i = (d_i : ℤ) = firstSmithDiagonal i.
```

The existing lemmas give exactly Passi's preabelian data:

```text
rho_i = e_i X_i + xi_i,       rho_i in R,       xi_i in gamma_2(F),

r = sum_i lambda_i(r) rho_i + r_ge_2,
                              r_ge_2 in R cap gamma_2(F).
```

Here `rho_i` is `collectedRelationRow ... 1 i` and
`xi_i` is `firstSmithTail i`.  Thus no presentation theorem remains to be
proved.

Use the existing equivalences to work in the free associative algebra on the
Smith letters:

```text
Phi : U(F) ~= FreeAlgebra ℤ I
```

obtained by composing
`FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra` with
`freeAlgebraFirstSmithEquiv`.  Existing simp lemmas give

```text
Phi (iota X_i) = FreeAlgebra.iota ℤ i.
```

All coefficient comparisons below occur in this one algebra.  There is no
second basis change.

## 4. Three small pieces of paper-native infrastructure

These are the only general-purpose additions.  Each is an explicit Lean
version of a sentence used by Passi.

### 4.1 Relations on the right

The repository currently collects the enveloping relation ideal as sums
`iota(r) * u`.  Passi needs sums `u * iota(r)`.  Prove the exact mirror of
`DegreeFive.idealOfLieIdeal_eq_rightRelationIdeal`, specialized to `Z`:

```lean
private theorem exists_relation_on_right_finsupp
    (R : LieIdeal ℤ F) {z : UEA ℤ F}
    (hz : z ∈ UEA.idealOfLieIdeal ℤ F R) :
    ∃ c : (UEA ℤ F × R) →₀ ℤ,
      c.sum (fun p n ↦ n •
        (p.1 * UniversalEnvelopingAlgebra.ι ℤ (p.2 : F))) = z
```

The proof is the existing proof with left and right interchanged.  Its only
calculation is

```text
(u iota(r)) iota(x)
  = (u iota(x)) iota(r) + u iota([r,x]),
```

and `[r,x]` is again in `R`.  Extend from `iota(x)` by `UEA.induction`, then
use `TwoSidedIdeal.span_induction` and
`Finsupp.mem_span_range_iff_exists_finsupp` exactly as in the existing file.

### 4.2 The augmentation ideal as a free right module

In `FreeAlgebra ℤ I`, define the first-letter coefficient

```text
rightCoeff i : FreeAlgebra ℤ I →ₗ[ℤ] FreeAlgebra ℤ I
```

by conjugating `MonoidAlgebra.comapDomainAddMonoidHom` along the prefix
embedding

```text
w |-> FreeMonoid.of i * w.
```

Prove only the four identities used in the paper:

```text
rightCoeff i (iota j * q) = if i = j then q else 0;

p in associativeHigh 1
  -> p = sum_i iota i * rightCoeff i p;

p in associativeHigh (n+1)
  -> rightCoeff i p in associativeHigh n;

p in associativeHigh 1
  -> rightCoeff i (p*q) = rightCoeff i p * q.
```

The reconstruction proof evaluates both sides at a free-monoid word and
splits its nonempty list into head and tail.  The multiplication identity is
then obtained by reconstructing `p`; it does not require a convolution
library.  These four statements are precisely Passi's sentence that
`omega` is free as a right `U(F)`-module on the `X_i`.

### 4.3 The two word-length facts actually used

Do not prove a general theorem about arbitrary filtered target algebras.
Use `DegreeFive.exists_freeAlgebra_word_finsupp` once and record only these
two corollaries.

First, a free-algebra substitution which sends every letter to a finite
linear combination of letters preserves both `associativeExact n` and
`associativeHigh n`.  A source word of length `m` expands only into target
words of the same length `m`.  This applies to the two Smith substitutions
and to every cutoff `theta`.  It also gives

```text
component_n (freeAlgebraToFirstSmith p)
  = freeAlgebraToFirstSmith (component_n p),
```

and the analogous inverse identity.  These component identities are needed
only for `n=1,2,3` in Section 7.1.

Second, for the one evaluation homomorphism

```text
evalA : FreeAlgebra ℤ I -> U(L),
evalA(X_i) = iota(x_i),
```

a word of length `m >= n` maps into the `n`th power of the augmentation
ideal.  Each letter is in the augmentation ideal; split the word after its
first `n` letters, put their product in `omega^n`, and use two-sided closure
for the remaining suffix.  Finite word expansion then proves

```text
p in associativeHigh n -> evalA(p) in omega^n.
```

Thus this block contains one word expansion and two short specializations,
not an abstract filtration framework.  No equality of filtrations and no
new PBW theorem is required.

## 5. Normalize the dimension-four witness exactly as Passi does

Take `b in delta_4(L)` and a witness supplied by
`exists_freeDimensionFourWitness_gammaTwo`.  Regard its relation difference
as a member of the two-sided relation ideal and apply Section 4.1:

```text
iota(w) - h = sum_p c_p u_p iota(r_p),       h in omega^4.
```

Put

```text
u_p^+ = u_p - algebraMap(epsilon(u_p)),
q     = sum_p c_p epsilon(u_p) r_p,
v     = w - q.
```

Then prove, by linearity of `iota`, the exact equality

```text
iota(v) - h = sum_p c_p u_p^+ iota(r_p),
```

with `u_p^+ in omega`, and `ev(v)=b` because every `r_p` is in the kernel.
The right side and `h` lie in `omega^2`; hence `iota(v) in omega^2`.
Apply the already proved `delta_2 = gamma_2` to obtain

```text
v in gamma_2(F).
```

Package only the exact equality, evaluation, multiplier augmentation, and
`v in gamma_2(F)`.  Do not introduce another witness hierarchy.

## 6. Passi's `s`, cutoff maps, and the degree-three cancellation

This section is the specialization of Theorem `deltan` to `n=4`.

### 6.1 Define Passi's `a` and `s` literally

In `A = FreeAlgebra ℤ I`, let `a` be the two-sided ideal generated by all
associative commutators

```text
p*q - q*p.
```

This is the direct associative realization of Passi's
`a = U(F) gamma_2(F)`.  The only inclusion needed is that the Smith-PBW image
of `gamma_2(F)` lies in `a`; prove it by the existing linear-span
description of `[top,top]`, since PBW sends a Lie bracket to an associative
commutator.  No equality of ideals and no commutative quotient are needed.

Define `s` by one `TwoSidedIdeal.span`, on the union of those commutators and
the diagonal heads `e_i * iota(i)`, and then use `.asIdeal`.  Thus `a ≤ s`
is just `TwoSidedIdeal.span_mono`; no separate lemma about sums of noncommutative
ideals is needed.  Do not define a quotient.  Write `A_n` for
`associativeHighIdeal I n`, so the sums and products below are literal
operations on `Ideal A`.  The preabelian relation decomposition from
Section 3 now proves

```text
Phi(iota(r)) in s          for every r in R.
```

Indeed, its linear head is a sum of diagonal generators, while its remainder
lies in free `gamma_2` and hence maps into `a` by the preceding one-line span
induction.

The normalized equality now gives the literal membership

```text
Phi(iota(v)) in A_4 + A_1 * s.
```

There is no filtration inference hidden here.  The existing
`universalEnvelopingEquiv_mem_associativeHigh` sends `h in omega^4` to
word length at least four in the original letters; Section 4.3 transports
that membership through the Smith substitution.  The same two facts with
`n=1` send every normalized multiplier `u_p^+ in omega` into `A_1`.

### 6.2 A normalized cubic commutator expansion

Prove one homogeneous Lie lemma:

```text
every exact cubic free-Lie element is a finite sum of
  [[X_i,X_j],X_k] with i < j and i <= k.
```

This is not a Hall-basis construction and asserts no uniqueness.  Its proof
is bounded:

1. literal magma words of length three span `magmaExact 3` (the repository
   already contains the identical span argument in degrees two and three);
2. the two bracketings are converted by skew-symmetry and Jacobi;
3. expand each original degree-one generator in the first Smith basis;
4. order the first pair by skew-symmetry;
5. if `k < i < j`, use exactly Passi's identity

   ```text
   [[X_i,X_j],X_k]
     = [[X_k,X_j],X_i] - [[X_k,X_i],X_j].
   ```

Both terms on the right already satisfy the required inequalities, so there
is no recursive normalization algorithm.

Combining this with the existing strict quadratic coordinates writes, modulo
`gamma_4(F)`,

```text
v = sum_i v_i,

v_i = sum_{j>i} aCut_ij [X_i,X_j]
    + sum_{j>i, k>=i} b_ijk [[X_i,X_j],X_k].
```

The temporary name `aCut_ij` is intentional: this cutoff normalization uses
`i<j`, whereas the final `NormalFormCertificate` uses coefficients `a_ij`
with `i>j`.  Section 7 chooses the latter afresh from the same quadratic
component, so no sign-reindexing lemma connects the two conventions.

Here the equality modulo `gamma_4` is implemented, not assumed: remove the
exact components of weights two and three from `v`, twice apply
`mem_lieHigh_succ_of_component_eq_zero`, and then use the existing
`freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh`.  After the Smith
substitution this says that the displayed `sum_i v_i` itself still belongs
to `A_4 + A_1*s`, which is the precise input to the cutoff maps.

### 6.3 Isolate `v_i` by Passi's `theta_i`

For every `i`, define two free-algebra endomorphisms:

```text
theta_ge_i(X_j) = X_j if i <= j, and 0 otherwise;
theta_gt_i(X_j) = X_j if i <  j, and 0 otherwise.
```

This avoids choosing successors in a finite order.  Both maps preserve word
length, preserve `a` because algebra homomorphisms send commutators to
commutators, and preserve the diagonal-head ideal generator-by-generator.
The inequalities in Section 6.2 give

```text
theta_ge_i(sum_l v_l) - theta_gt_i(sum_l v_l) = v_i.
```

Applying the two maps to the membership at the end of Section 6.1 therefore
gives

```text
v_i in A_4 + A_1 * s.
```

This is exactly Passi's descending `theta` argument, expressed without an
index-successor lemma.

### 6.4 Apply the free right-module coefficient

For fixed `i<j`, put

```text
u_ij = aCut_ij + sum_{k>=i} b_ijk X_k.
```

Modulo `A_1 * s`, the adjoint expression in `v_i` is

```text
[X_i,X_j] u_ij.
```

More precisely, the omitted term is

```text
-(u_ij - aCut_ij) [X_i,X_j],
```

not `-u_ij[X_i,X_j]`: the scalar part of the adjoint action is
`aCut_ij[X_i,X_j]` and must remain.  Since `u_ij-aCut_ij` has minimum word length
one and `[X_i,X_j]` lies in `a ≤ s`, this omitted term lies in `A_1*s`.
Apply `rightCoeff j`.  A single `Submodule.mul_induction_on`, using the last
identity of Section 4.2, proves
`rightCoeff j (A_1*s) ≤ s`; no formula for coefficients of arbitrary ideal
elements is needed.  Section 4.2 then gives exactly

```text
X_i u_ij in A_3 + s.                               (Passi 3)
```

### 6.5 Lean realization of Passi's polynomial cancellation

The paper now passes to `Z[X_1,...,X_m]` and cancels `X_i`.  Constructing that
quotient and a new integral-domain API is unnecessary.  For each coefficient
`b_ijk`, set

```text
g = Nat.gcd d_i d_k
```

The existing `collectedDiagonal_pos` gives `0 < g`, so there is no `ZMod 0`
branch to manage.

Map `A` to `MvPolynomial I (ZMod g)` by

```text
X_i |-> X_i,   X_k |-> X_k,   every other X_l |-> 0.
```

This map kills `s`:

- commutators vanish in the commutative target;
- a head `e_l X_l` vanishes either because `X_l` was killed or because
  `g` divides `d_i` and `d_k`, so the integer casts `e_i` and `e_k`
  vanish in `ZMod g`.

The coefficient of total degree two also kills `associativeHigh 3`.  Prove
this locally from `exists_freeAlgebra_word_finsupp`: a surviving word of
length at least three maps to a monomial of total degree at least three.
There is no new homogeneous-polynomial API.  Taking the coefficient of
`X_i X_k` in `(Passi 3)` yields

```text
(b_ijk : ZMod g) = 0,
```

and `ZMod.intCast_zmod_eq_zero_iff_dvd` yields

```text
(g : ℤ) divides b_ijk.                              (Passi gcd)
```

There is one `i=k` branch, where the selected monomial is `X_i^2`; the same
coefficient computation applies.

Why this is the correct direct formalization: Passi has an invariant-factor
order and replaces the ideal `(e_i,e_k)` by `(e_i)` because `e_i | e_k`.
Mathlib's currently available positive diagonal presentation is not ordered
by divisibility for an arbitrary finite Lie ring.  Retaining the exact ideal
`(e_i,e_k)` is the result of the **same** polynomial coefficient comparison.
It is also exactly what the next Bezout step needs.  This avoids building a
second Smith-normal-form theory merely to throw away information.

### 6.6 Eliminate the cubic Lie component

Write `b_ijk = t*g`.  Expanding `(g : ℤ)` with
`Nat.gcd_eq_gcd_ab` gives

```text
b_ijk = alpha_ijk e_i + beta_ijk e_k.
```

After evaluation in `L`,

```text
b_ijk [[x_i,x_j],x_k]
 = alpha_ijk [[e_i x_i,x_j],x_k]
 + beta_ijk  [[x_i,x_j],e_k x_k].
```

The existing theorem
`firstSmithDiagonal_smul_value_mem_gammaTwo` puts both diagonal multiples in
`gamma_2(L)`.  The first summand is in `gamma_4` by successive lower-central
bracketing; the second is in `[gamma_2,gamma_2] <= gamma_4`.  Hence the entire
evaluated cubic component lies in `gamma_4(L)`.

This is the exact role of Theorem `deltan` in Passi's degree-four proof; no
general theorem is needed.

## 7. Passi's degree-four `D+F` calculation and the rows `W_i`

In the Smith free algebra, define `relationIdeal` once as the
`.asIdeal` of the two-sided span of all `Phi(iota(r))`, `r in R`.  Every
occurrence below comes from an explicit relation factor in the normalized
finite sum.  The evaluation map kills this ideal by one
`TwoSidedIdeal.span_induction`; no quotient or transported-ideal equality is
introduced.

Let `v_2` and `v_3` be the exact quadratic and cubic components of `v`.
Use `exists_strictBracketCoordinates` to write

```text
v_2 = sum_{i>j} a_ij [X_i,X_j].
```

Define the free row

```text
W_i = sum_{i>j} a_ij X_j - sum_{i<j} a_ji X_j.
```

A finite-sum rearrangement gives Passi's identity

```text
PBW(v_2) = sum_i X_i W_i.
```

The cubic component was eliminated in Section 6.6, and the remainder
`v-v_2-v_3` is in free `gamma_4`; therefore

```text
b - evaluation(v_2) in gamma_4(L).                 (representation)
```

It remains only to prove Passi's row condition.

### 7.1 Project the normalized relation sum in degrees two and three

For a normalized multiplier `u in associativeHigh 1` and a Lie relation `r`,
write `u_1,u_2` and `r_1,r_2` for their exact components.  Prove the two
specialized product identities

```text
component_2(u r) = u_1 r_1,
component_3(u r) = u_2 r_1 + u_1 r_2.
```

Proof: subtract components successively using
`mem_associativeHigh_succ_of_component_eq_zero`.  For `component_2`, the
omitted products have minimum length at least three.  For `component_3`,
first remove `u_1*r_1`; its third component is zero because it is exact
degree two.  After that removal, subtract `u_2*r_1 + u_1*r_2`; every
remaining product has minimum length at least four.  Before taking these
components, use the exact-degree compatibility from Section 4.3 to transport
the equality to the Smith letters.  This is a two-degree calculation, not a
general graded multiplication library.

The preabelian presentation gives

```text
r_1 = sum_k lambda_k(r) e_k X_k,
```

while `r_2` is an exact quadratic Lie element.  Thus the degree-three side
splits literally as in Passi:

```text
D = sum d_ijk e_k X_i X_j X_k,
F = sum X_i C_i,
```

where every `C_i` is an exact quadratic Lie element.  Expand each `C_i` by
the already proved strict bracket coordinates:

```text
C_i = sum_{j>k} f_ijk [X_j,X_k].
```

The coefficients `d_ijk` are read directly from
`FreeAlgebra.equivMonoidAlgebraFreeMonoid` on the exact quadratic
multipliers (equivalently from the existing finite word expansion).  They
are local definitions inside the certificate proof, not a packet or a new
basis theorem.

Set

```text
Y_i = D_i + PBW(C_i).
```

The exact degree-two/three equation is then

```text
PBW(v_2+v_3) = sum_i X_i (W_i+Y_i).
```

Passi also reads `e_i | a_ij` from the degree-two comparison because his
Theorem `delta4` states a full characterization.  That divisibility is never
used in Corollary `2delta_4`, and it is not a field of
`NormalFormCertificate`; the direct corollary proof therefore uses the same
degree-two equality only to identify the rows `W_i` and does not package an
unused lemma.

Apply `rightCoeff i` to the original normalized relation equality.  The
high term and the degree-at-least-four remainder land in
`associativeHigh 3`; `rightCoeff i (u r)=rightCoeff i(u) r` is still a right
relation product.  Therefore

```text
W_i + Y_i in associativeHigh 3 + relationIdeal.    (Passi row 1)
```

### 7.2 Prove the gcd condition on `f_ijk`

Use the free-monoid basis only for the coefficient that is actually needed.
Fix `i,j,k` with `j>k` and put

```text
g3 = Nat.gcd d_i (Nat.gcd d_j d_k).
```

For the coefficient of the single word `X_i X_j X_k` in `PBW(v_3)`, expand
each normalized triple commutator into its four associative words.  In each
of the four possible equality branches, the contributing triple has the
same three indices in a permuted order.  Section 6.5 says that its
coefficient is divisible by the gcd of its first and third diagonal; `g3`
divides that gcd.  The zero branches are discharged by `simp`.  Thus this
one coefficient of `PBW(v_3)` is divisible by `(g3 : ℤ)`.

The coefficient of the same word in `D` is divisible by `(g3 : ℤ)`
because every contributing term has the explicit last-letter factor `e_k`.
In

```text
F = PBW(v_3) - D,
```

take the coefficient of the word `[i,j,k]`.  The strict bracket expansion of
`C_i` says that this coefficient is exactly `f_ijk`.  Consequently

```text
(g3 : ℤ) divides f_ijk.                         (Passi f-gcd)
```

The Lean proof is one `Finsupp.sum` divisibility argument plus those four
explicit equality cases.  It introduces neither a general word-content
definition nor a coordinate packet.

### 7.3 Rewrite `Y_i` exactly as Passi does

Nested `Nat.gcd_eq_gcd_ab` turns `(Passi f-gcd)` into

```text
f_ijk = e_i f^i_ijk + e_j f^j_ijk + e_k f^k_ijk.
```

Now repeat Passi's displayed calculation term by term.

- In `D_i`, replace `e_k X_k` by `rho_k - xi_k`.  The `rho_k` term is a
  relation and `X_j xi_k` has minimum length three.
- In the `f^j` bracket, replace `e_j X_j` by `rho_j - xi_j`; the relation
  part vanishes modulo the relation ideal and the tail bracket has weight
  at least three.
- Do the same for the `f^k` bracket.
- The `f^i` part remains `e_i` times an exact quadratic Lie element.

Thus, with an explicitly constructed `Q_i in gamma_2(F)`, obtain

```text
Y_i - e_i PBW(Q_i) in associativeHigh 3 + relationIdeal.
```

Together with `(Passi row 1)` this gives—note the sign—

```text
W_i + e_i PBW(Q_i) in associativeHigh 3 + relationIdeal.
```

Map to `U(L)`.  Relation products map to zero, and the specialized evaluation
fact in Section 4.3 sends the high term into the third augmentation power.
Hence

```text
evaluation(W_i) + e_i evaluation(Q_i) in delta_3(L).
```

Invoke the already proved `delta_3 = gamma_3`.  With

```text
y_i = -evaluation(Q_i) in gamma_2(L),
z_i = evaluation(W_i) + e_i evaluation(Q_i) in gamma_3(L),
```

we have the required row decomposition

```text
normalFormRow x a i = e_i y_i + z_i.               (Passi row 2)
```

Together with `(representation)` and
`firstSmithDiagonal_smul_value_mem_gammaTwo`, these fields construct

```lean
private theorem finite_normalFormCertificate
    [Finite L] (b : L) (hb : b ∈ dimensionSubring ℤ L 4) :
    Nonempty (NormalFormCertificate.{u, 0} b)
```

directly.

## 8. Finish the two global theorems

Define

```lean
theorem finiteBartholdiPassiExtraction :
    FiniteBartholdiPassiExtractionProperty :=
  fun L _ _ b hb => finite_normalFormCertificate b hb
```

Then use only already compiled theorems:

```text
finiteBartholdiPassiExtraction
  -> twoDeltaFourProperty_of_finite_extraction
  -> DegreeFive.TwoDeltaFourProperty
  -> DegreeFive.dimensionSubring_five_le_lowerCentralSeries_three.
```

The wrapper named on the second line is already compiled; internally it is
exactly
`twoDeltaFourProperty_of_finite (finiteTwoDeltaFour_of_extraction ...)`.
The only two public declarations added at this stage are therefore

```lean
theorem twoDeltaFourProperty : DegreeFive.TwoDeltaFourProperty :=
  twoDeltaFourProperty_of_finite_extraction
    finiteBartholdiPassiExtraction

theorem dimensionSubring_five_le_lowerCentralSeries_three
    (L : Type u) [LieRing L] :
    dimensionSubring ℤ L 5 ≤ lowerCentralSeries ℤ L 3 :=
  DegreeFive.dimensionSubring_five_le_lowerCentralSeries_three L
    twoDeltaFourProperty
```

The last line is the requested unconditional integral result
`delta_5(L) <= gamma_4(L)` for every Lie ring `L`.

## 9. Expected proof surface

The implementation has six bounded conceptual blocks:

1. finite collection with the relation on the right, followed immediately
   by Passi's removal of the scalar parts of the multipliers;
2. the four free-right-module coordinate facts, kept together in one local
   namespace;
3. one supported-word calculation, specialized to graded substitutions and
   to the evaluation map;
4. normalized cubic commutator spanning;
5. the specialized Passi cutoff/cancellation result, returning the gcd
   divisibility of the cubic coefficients;
6. `finite_normalFormCertificate`.

The two low-product component equalities stay local to item 6.  Definitions
(`s`, `theta`, the polynomial probe, `D`, `C_i`, `Y_i`) and one-line simp
facts are not separate abstraction layers.  Lean may require some of these
identities to be separate private theorem declarations; that is harmless.
What is forbidden is introducing a new conceptual layer not present in one
of these six blocks.  If that appears necessary, stop and re-audit it first
instead of growing a new theory around it.

## 10. Final audit

### 10.1 Exact implication audit

| Paper step | Lean realization | Status |
|---|---|---|
| Choose `v=w+r in omega^4+omega r` | right-relation Finsupp plus removal of multiplier augmentations | PASS |
| `v in gamma_2(F)` | exact membership in `omega^2`, then compiled `delta_2=gamma_2` | PASS |
| Preabelian `s` | diagonal-head ideal plus Passi's associative commutator ideal `a`; first-Smith relation decomposition | PASS |
| Write modulo `gamma_4+F''` by adjoint commutators | exact weight-two/three decomposition; `F'' <= gamma_4`, so no quotient is formalized | PASS |
| Jacobi normalization | one application of Passi's displayed identity when `k<i` | PASS |
| Isolate `v_i` by `theta_i` | difference `theta_ge_i-theta_gt_i`; no successor or induction hidden | PASS |
| Use freeness of `omega` as a right module | `rightCoeff`; four explicit free-monoid identities | PASS |
| Perform Passi's polynomial cancellation | commutative polynomial probe modulo `gcd(e_i,e_k)` and one coefficient; no quotient object | PASS |
| Eliminate the cubic term | Bezout plus the compiled fact `e_i x_i in gamma_2` | PASS |
| Produce Passi's `D+F` expression | only components 1 and 2 of each multiplier/relation; two explicit product formulas | PASS |
| Compare degree two | use the equality to form `W_i`; omit only the unused characterization lemma `e_i | a_ij` | PASS |
| Obtain `W_i+Y_i in omega^3+r` | apply `rightCoeff i` to the exact normalized equality | PASS |
| Prove the `f_ijk` gcd | one length-three word coefficient in `v_3-D` | PASS |
| Rewrite `Y_i` | substitute `e_kX_k=rho_k-xi_k` and nested Bezout, term for term as in the paper | PASS |
| Use `delta_3=gamma_3` | map the row remainder to `U(L)` and invoke the compiled theorem | PASS |
| Derive `2a=sum_i[X_i,W_i]` | already compiled in `NormalFormCertificate` | PASS |
| Pass finite to arbitrary and apply standing reduction | already compiled | PASS |

### 10.2 Lean feasibility audit

| Needed operation | Existing API or bounded proof | Status |
|---|---|---|
| Two-sided relation collection | existing `RelationIdeal.lean`, mirrored with `UEA.induction` | PASS |
| Positive diagonal preabelian rows | existing `PositiveSmithPresentation`, first-row and tail lemmas | PASS |
| Change to Smith generators | existing `freeAlgebraFirstSmithEquiv` | PASS |
| Homogeneous projections | existing component/exact/high lemmas plus the supported-word proof that Smith substitutions preserve exact length | PASS |
| Right free-module coordinate | `MonoidAlgebra.comapDomainAddMonoidHom` along an injective prefix map | PASS |
| Cutoff endomorphisms | `FreeAlgebra.lift`; action on generators is `0` or the same generator | PASS |
| The ideals `a,s` | `TwoSidedIdeal.span`; one span induction sends free `gamma_2` into associative commutators | PASS |
| Polynomial coefficient probe | `FreeAlgebra.lift`, `MvPolynomial.coeff_X_mul`, `ZMod.intCast_zmod_eq_zero_iff_dvd` | PASS |
| Bezout | `Nat.gcd_eq_gcd_ab` / `Int.gcd_eq_gcd_ab` | PASS |
| Cubic spanning | the already used magma-word span method plus skew/Jacobi; no independence proof | PASS |
| High words under evaluation | the same finite word expansion, specialized only to the augmentation ideal of `U(L)` | PASS |
| `delta_2`, `delta_3`, final factor-two identity | already compiled | PASS |

### 10.3 Audit failures found and removed before this version

1. **Failed:** assume the current Smith diagonals satisfy
   `e_1 | ... | e_m`.
   **Repair:** retain the exact ideal `(e_i,e_k)` in Passi's cancellation and
   use its gcd.  No invariant-factor construction is added.

2. **Failed:** take `Y_i` to be the raw first-letter coefficient of the
   cubic Lie term.  Its `e_i` part can multiply an arbitrary quadratic word,
   not an element of `gamma_2`.
   **Repair:** keep Passi's actual `D+F` split; only the `f` part is a bracket
   sum.

3. **Failed:** use the existing PBW filtration lemma backwards.  The current
   theorem only sends augmentation powers to high word length.
   **Repair:** use one supported-word calculation for the two precise
   directions in Section 4.3; do not state an arbitrary filtered-target
   theorem.

4. **Failed:** formalize `U(F/F')` and an integral-domain cancellation
   theorem.  That would create a large quotient/polynomial infrastructure
   for one coefficient.
   **Repair:** the polynomial probe modulo the relevant gcd proves the same
   coefficient statement directly.

5. **Failed:** formalize a full Hall basis or general `deltan`.
   **Repair:** exact weights two and three plus one Jacobi normalization are
   all that `2 delta_4 <= gamma_4` uses.

6. **Failed:** replace the complete adjoint expression by
   `[X_i,X_j]u_ij` and discard `-u_ij[X_i,X_j]`.  Its scalar part is not in
   `A_1*s`.
   **Repair:** discard only
   `-(u_ij-aCut_ij)[X_i,X_j]`; this factor has positive word length and is
   exactly in `A_1*s`.

7. **Failed:** use filtration preservation alone when projecting the
   normalized relation equation to degrees two and three.
   **Repair:** the same word calculation proves that the Smith linear
   substitutions preserve exact degree and commute with the three required
   component maps.

8. **Failed:** infer `W_i-e_iQ_i` from
   `W_i+Y_i in H` and `Y_i-e_iQ_i in H`.
   **Repair:** the correct consequence is `W_i+e_iQ_i in H`; set the
   certificate entry to `y_i=-evaluation(Q_i)`.

9. **Failed:** say that every term omitted from the third product component
   has length at least four.  The term `u_1*r_1` has exact length two.
   **Repair:** kill its third component by exact-degree orthogonality first;
   only the terms remaining after that step have minimum length four.

10. **Failed:** use the same `a_ij` notation for the cutoff normalization
    (`i<j`) and for the final normal form (`i>j`).
    **Repair:** call the former `aCut_ij` and choose the certificate's
    `a_ij` independently in Section 7; no reindexing lemma is required.

After these repairs, the exact-implication audit and the Lean-feasibility
audit both pass.  The plan contains six bounded conceptual blocks, all tied
directly to a displayed step of Bartholdi--Passi; it contains no independent
coordinate theory whose proof is harder than the target theorem.
