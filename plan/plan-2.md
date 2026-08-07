My prompt:
› Okay, then I suggest you take a final look at the three
  properties we add under the Dynkin operator assumption and
  write a proof plan. I'll save this plan so we can prove all
  these properties in the future. The plan should be clear and
  understandable. It should be immediately implementable. I'll
  give it to you directly, but in the future.

Your answer:
• Here is the final implementable plan for proving
  DynkinProperties.

  ## 1. Define the map

  For a free associative word (w) in generators from (L), define
  [
  d_3(w)=
  \begin{cases}
  \operatorname{coord}[x,[y,z]],&w=xyz,\
  0,&\text{otherwise}.
  \end{cases}
  ]

  Extend this linearly through
  [
  U(F)\cong \operatorname{FreeAlgebra}_{\mathbb Z}(L)
  \cong \mathbb Z[\operatorname{FreeMonoid}(L)].
  ]

  This gives
  [
  \Phi_R:U(F)\longrightarrow\mathbb Z/q\mathbb Z.
  ]

  Linearity is part of the definition. Directly prove that
  (\Phi_R) vanishes on associative filtration degree at least
  four. Neither fact belongs in DynkinProperties.

  ## 2. Define exactly three properties

  structure DynkinProperties (R : StandingReductionData L) : Prop
  where
    exactThree : ...
    oneTwo : ...
    oneOneOne : ...

  ### Property 1: degree-three normalization

  # For every homogeneous (f\in F_3),
  [
  \Phi_R(\iota(f))

  3,\operatorname{coord}(\operatorname{ev}(f)).
  ]

  Lean formulation should use freeLieExact L 3,
  exactThreeEvaluation, and R.gammaThreeEquiv.

  Proof:

  1. Write (f) as the image of a nonassociative polynomial
     supported on bracketed words of length three.

  2. Use linearity to reduce to one bracketed word.
  3. A bracketed word of length three has one of the two forms
     [
     [x,[y,z]],\qquad [[x,y],z].
     ]

  4. Expand it into four associative words.
  5. Apply the definition of (\Phi_R).
  6. Use antisymmetry and Jacobi to obtain three times the
     original bracket.

  The existing freeLieExact, magmaExact, and freeLieMkLinear
  machinery supplies the required representative.

  ### Property 2: weight-one times weight-two

  For every adapted basis pair (x_i,y_k),
  [
  \Phi_R(\iota(x_i)\iota(y_k))=2G_{ik}.
  ]

  Proof:

  1. Expand (x_i) into degree-one generator terms.
  2. Expand (y_k) into degree-two bracket terms ([u,v]).
  3. For one term,
     [
     x[u,v]=xuv-xvu.
     ]

  4. By the definition of (\Phi_R),
     [
     \Phi_R(xuv-xvu)
     =[x,[u,v]]-[x,[v,u]]
     =2[x,[u,v]].
     ]

  5. Sum linearly and identify the result with R.coordinateGMod i
     k.

  Do not assume the reverse-order formula. Derive it later from
  Property 1 and
  [
  \iota([x_i,y_k])
  =\iota(x_i)\iota(y_k)-\iota(y_k)\iota(x_i).
  ]
  This gives automatically
  [
  \Phi_R(\iota(y_k)\iota(x_i))=-G_{ik}.
  ]

  ### Property 3: three weight-one factors

  # For all adapted degree-one basis elements,
  [
  \Phi_R(\iota(x_i)\iota(x_j)\iota(x_l))

  \operatorname{coord}[x_i,[x_j,x_l]].
  ]

  Proof:

  1. Expand each (x_i,x_j,x_l) into generator terms.
  2. Distribute the product using linearity.
  3. On each generator triple, the equality is exactly the
     definition of (\Phi_R).

  4. Reassemble using trilinearity of the bracket and
     gammaThreeEquiv.

  ## 3. Package the result

  After proving these three theorems, define:

  def dynkinProperties (R : StandingReductionData L) :
      DynkinProperties R where
    exactThree := ...
    oneTwo := ...
    oneOneOne := ...

  Only the three property theorems should be named globally. The
  expansions and case analyses should remain local inside their
  proofs. No theorem in this file should mention terminalZeta,
  terminal packets, a witness, or (\delta_5).
