This file contains the current work plan. If the file exists, then you should follow it.

So, we've now reduced the problem to the implication: Standing Reduction + terminalZeta = coord(a) for a in \delta_5 => a = 0.

Our overall goal is to eliminate the second assumption, that is, to obtain the theorem: Standing Reduction => \delta_5 = 0.

Our plan is to break this reduction into two steps by introducing the Dynkin map:
0) Define the Dynkin map. 1) Reduce to the implication: Standing Reduction + Dynkin Properties => \delta_5 = 0.
2) Prove Dynkin Properties, thereby reducing the problem to Standing Reduction => \delta_5 = 0.

Here, Standing Reduction is the assumption that our Lie algebra is a finite 2-primary Lie algebra of nilpotency class 3 with cyclic \gamma_3 = Z/qZ.

Let's take a closer look at how we proceed. Two requests are planned. In the first, we'll do (1), in the second (2) – no more, no less!

Important 1: Dynkin Properties must contain three specific properties and NO MORE:
1. Degree-three normalization:
[
\Phi(\iota(f))=3,\operatorname{coord}(\operatorname{ev}(f))
]
for every homogeneous degree-three (f).

2. The two mixed-product formulas, combined into one field:
[
\Phi(x_i y_k)=2G_{ik},\qquad
\Phi(y_k x_i)=-G_{ik}.
]

3. The triple-product formula:
[
\Phi(x_i x_j x_l)
=\operatorname{coord}[x_i,[x_j,x_l]].
]

The plan you wrote for implementing (1) is in the file "plan/plan-1.md".

The plan you wrote for solving (2) is in the file "plan/plan-2.md".

Important 2: Our philosophy is fundamentally to NOT create unnecessary intermediate lemmas. Small intermediate statements can be proved. But we don't make huge branching decisions or insert a large number of unnecessary lemmas, because in Lean, such activity would lead to us never obtaining the desired result. We prove directly what we need in the most direct way possible. The first query MUST fully formalize the implication: STANDING REDUCTION + DYNKIN PROPERTIES => \delta_5 = 0. If this implication isn't realized, it's a huge problem; we can't do that; this implication must be realized.

So, your current task is a complete, direct implementation of the first part of the plan: define the Dynkin map, prove its simplest properties, infer its more meaningful properties, and prove the desired equality concluding \delta_5 = 0.

So that you have a clear understanding of what this plan is, how it came about, what we're doing, and what the clear goal and methods are, I've saved the discussion we had about the plan at "plan/plan-context-discussion-save.md"
