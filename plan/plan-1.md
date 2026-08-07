• ## Part I plan: StandingReduction + DynkinProperties ⇒ δ₅ = 0

  This part should introduce only two named theorems:

  1. terminalZeta_eq_targetCoordinate
  2. dimensionSubring_five_eq_bot_of_dynkinProperties

  All packet calculations remain local inside the first theorem.

  ### 1. Prove the direct coordinate bridge

  Target statement:

  theorem terminalZeta_eq_targetCoordinate
      (R : StandingReductionData L)
      (hΦ : DynkinProperties R)
      {a : L}
      (w : AdaptedPresentationDimensionFiveWitness L L
        (canonicalFreeLieEvaluation L) a) :
      R.terminalZeta w 0 =
        R.gammaThreeEquiv ⟨a, proof_that_a_mem_gammaThree_from_w⟩

  The proof proceeds as follows.

  #### A. Extend the normalization property locally

  DynkinProperties.exactThree concerns homogeneous degree-three
  elements. Inside the theorem, derive:

  [
  f\in\gamma_3(F)
  \quad\Longrightarrow\quad
  \Phi(\iota(f))

  3,\operatorname{coord}(\operatorname{ev}(f)).
  ]

  Take the degree-three homogeneous component of (f). The
  remainder has weight at least four, hence:

  - (\Phi) kills it by the already-proved support theorem;
  - its evaluation in (L) vanishes because R.classThree.

  This should be a local have, not a new global lemma.

  #### B. Apply (\Phi) to the terminal equality

  Use the existing theorem

  w.terminalPackets_value

  which says that the terminal ledger evaluates to

  [
  \iota(w.\mathrm{lieLift})-w.\mathrm{highWord}.
  ]

  Apply the linear map (\Phi) to this equality.

  The right-hand side becomes

  [
  3,\operatorname{coord}(a):
  ]

  - highWord is killed because it has associative filtration at
    least five;

  - lieLift lies in (\gamma_3(F));
  - w.evaluates identifies its evaluation with (a).

  #### C. Calculate the left-hand side directly

  Prove, as one local calculation,

  [
  \Phi!\left(\sum_p n_p,p.\mathrm{value}\right)

  3,\texttt{terminalZeta}(w,0).
  ]

  Use map_finsuppSum and consider one packet in the terminal
  support.

  1. If its total weight is at least four, its value lies in
     associative filtration at least four, so (\Phi) kills it.

  2. A high relation tag has weight five and is therefore also
     killed.

  3. For a row packet of total weight at most three, use the
     existing terminal packet table. The only possible shapes are:
      - weight-one row with external weights
        [
        [],\ [1],\ [2],\ [1,1];
        ]

      - weight-two row with external weights
        [
        [],\ [1];
        ]

      - scalar weight-three row.

  4. Expand weight-one and weight-two rows using the already-
     defined data
     coordinateD, coordinateE, coordinateBValue,
     firstRelationTail, and secondRelationTail.

  5. Apply the three fields of DynkinProperties. After this
     calculation, the ledger value has the form
     [
     3,\texttt{terminalZeta}(w,0)
     +\text{ordered-}xy\text{ error}
     +\text{ordered-}xxx\text{ error}.
     ]

  The (xy)-error is exactly
  [
  2\sum_{i,k}G_{ik},
  \bigl(\text{terminal PBW coefficient of }x_i y_k\bigr).
  ]
  Every coefficient vanishes by the existing theorem

  w.terminalPackets_xyCoefficient_eq_zero

  The (xxx)-error comes only from weight-one rows with two
  external weight-one factors. Terminal ordering gives a sorted
  triple. Group these terms by their class-two PBW exponent and
  use the general theorem

  w.terminalPackets_adaptedPBWCoefficient_eq_zero

  for each exponent of weighted degree three.

  Thus both errors vanish.

  The remaining terms are precisely the formal (z)-coefficient
  obtained by unfolding

  terminalZeta
  terminalLieZ
  terminalPreTheta
  PreTheta.polynomial

  at (t=0). The sign identifications use only the existing
  theorems

  coordinateG_cast
  coordinateC_cast
  coordinateM_cast

  No new packet predicate or coordinate structure should be
  introduced.

  #### D. Cancel the factor (3)

  Combining B and C gives
  [
  3,\texttt{terminalZeta}(w,0)

  3,\operatorname{coord}(a).
  ]

  Because (q=2^\kappa), (3) is a unit in (\mathbb Z/q\mathbb Z).
  Use ZMod.isUnit_iff_coprime and cancel it. This proves
  terminalZeta_eq_targetCoordinate.

  ### 2. Deduce δ₅ = 0

  Target statement:

  theorem dimensionSubring_five_eq_bot_of_dynkinProperties
      (R : StandingReductionData L)
      (hΦ : DynkinProperties R) :
      dimensionSubring ℤ L 5 = ⊥

  Proof:

  1. Install the finite instance supplied by R.finite_inst.
  2. Rewrite with eq_bot_iff.
  3. Let (a\in\delta_5(L)).
  4. Obtain the witness using

     exists_adaptedPresentationDimensionFiveWitness

  5. Apply terminalZeta_eq_targetCoordinate R hΦ w.
  6. Apply the already-proved

     R.terminalZeta_eq_zero w 0

  7. Conclude that the (\gamma_3)-coordinate of (a) is zero.
  8. Use injectivity of R.gammaThreeEquiv to obtain (a=0).

  The final theorem has exactly two inputs:

  - R : StandingReductionData L;
  - hΦ : DynkinProperties R.

  It must not assume a witness, a collection equality, a
  coordinate equation, or any statement involving terminalZeta.
