[intro]
I’ll ground this against the current repo rather than answer abstractly. I’ll first locate the exact chapter file and landed helper names, then check whether the collision residue is meant to be false, reducible by loop deletion, or needs a new geometric lemma.

The connector sees the public repo, but it does not find the `openedWBS` / `CrossPiece*` names on default `main`; it finds the older Ch13 stack. I’ll still use the landed spherical-arm files to verify which structural route is actually supported and call out where the v11-local names are not visible.

[answer]
One caveat: the GitHub connector’s visible `main` does **not** contain the local `openedWBS` / `CrossPiece*` / `FFCT*` names, so I cannot compile-check the v11 theorem. The visible Ch13 stack still describes the remaining obstruction as the structural opening/witness assembly, including specific tight-support identification and recursion/cut transport issues. fileciteturn5file0L41-L is either:

1. discharged by a new global simplicity theorem  
   `WeakConvexSphArm + PositiveJoints → NoNonadjacentRepeat`, making the collision case impossible; or

2. kept as the genuine last geometric residue.

With the hypotheses as written, I would treat `CrossPieceCollisionEndpointAtSup` as **irreducible unless you add that no-repeat/simplicity theorem**.

## 1. Delete-the-loop route

Your `Ahat = [0..r] ++ [s+1..n]` idea has the right endpoint:

\[
\operatorname{endpt}(Ahat)=\operatorname{endpt}(A')
\]

because \(A'_r=A'_s\), and the glue edge is indeed the old rotated edge \((A'_s,A'_{s+1})\), so its shortness is inherited when \(s<n\).

But the route fails at the comparison target.

There is no natural `Bhat` that simultaneously has:

\[
SameSides(Ahat,Bhat),\quad JointLe(Ahat,Bhat),\quad \operatorname{endpt}(Bhat)\le \operatorname{endpt}(B).
\]

The three obvious choices all break:

* `Bhat = [0..r] ++ [s+1..n]`: endpoint is right, but the glue side is \(d(B_r,B_{s+1})\), not \(d(A'_s,A'_{s+1})=d(B_s,B_{s+1})\).
* `Bhat = [0..r] ++ rotated([s..n])` with \(B_s\) moved to \(B_r\): side lengths match, but endpoint is not `endpt B`, and no landed lemma gives `endpt Bhat ≤ endpt B`.
* `Bhat = [0..r] ++ [s..n]`: the corresponding `A` arm would have a zero edge \(A'_r=A'_s\), violating the short-edge arm hypotheses.

The two-subarm estimate also dies exactly where you said. The only landed triangle inequality direction is

\[
d(p,r)\le d(p,q)+d(q,r),
\]

with equality only under antipodal/betweenness conditions. It does **not** imply

\[
d(B_0,B_r)+d(B_s,B_n)\le d(B_0,B_n).
\]

That reverse inequality is false without a new betweenness/convex-order theorem. fileciteturn26file0 \(\delta^*\)” argument.

For example, with \(A_\theta = openedWBS_\theta A B k\),

\[
\sigma(\theta)
= sOrient(A_\theta r)(A_\theta(r+1))(A_\theta s)
\]

is strict positive at \(\theta=0\) by strict nonincidence, and at collision it becomes

\[
sOrient(A'_r)(A'_{r+1})(A'_r)=0.
\]

So this support can simply decrease to zero at the supremum. That is a legitimate first-binding event, not a contradiction. The same phenomenon occurs symmetrically with edge \((s,s+1)\) if \(s<n\). This matches the visible repo’s warning that the hard part is not “some support vanishes,” but identifying/converting the right tight support into the needed witness. file plausible vacuity proof is stronger:

```lean
WeakConvexSphArm P → PositiveJoints P → NoNonadjacentRepeat P
```

Then `hcollision` contradicts `NoNonadjacentRepeat`. But that is a real geometric theorem: simplicity of weakly convex spherical polygonal arms with nondegenerate joints. It is not a local support-continuity adapter.

## 3. Correct route, if you want to discharge it

The clean route is **not** loop deletion against `B`. It is:

```lean
theorem weakConvex_positiveJoints_noNonadjacentRepeat
    {n : ℕ} {P : Fin (n+1) → S2}
    (hweak : WeakConvexSphArm P)
    (hpos : PositiveJoints P) :
    NoNonadjacentRepeat P := ...
```

Then the master theorem is just contradiction:

```lean
theorem crossPieceCollisionEndpointAtSup_of_noRepeat :
    CrossPieceCollisionEndpointAtSup := by
  intro n A B hA hB hsame hjle k hlt hstuck r s hrs hrK hKs hcoll
  have hweak : WeakConvexSphArm (openedWBS A B k) :=
    openedWBS_weakConvex_at_sup A B k hstuck
  have hpos : PositiveJoints (openedWBS A B k) :=
    openedWBS_positiveJoints_at_sup A B k hstuck
  have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
    weakConvex_positiveJoints_noNonadjacentRepeat hweak hpos
  exact False.elim (hnr r s hrs hcoll)
```

The real worker proof would need these nontrivial pieces:

```lean
support_opposite_zero_of_repeat
face_interval_of_support_zero
positiveJoints_no_closed_face_run
```

Sketch:

1. From \(P_r=P_s\), weak support of edge \((r,r+1)\) against vertex \(s+1\), and weak support of edge \((s,s+1)\) against vertex \(r+1\), get opposite inequalities for  
   \(sOrient(P_r)(P_{r+1})(P_{s+1})\). Hence this determinant is zero.
2. Prove a face-propagation lemma: if a weakly convex spherical polygon has a nonincident vertex on the support great circle of an edge, then the whole intervening boundary interval lies on that same support great circle.
3. Since the interval returns to \(P_r=P_s\), the intervening run is a closed face-run on one great circle.
4. A closed face-run with short edges forces some joint angle to be \(0\) or \(\pi\), contradicting `PositiveJoints`.

Degenerate audit:

* `r = K`: rotation about `A K` fixes only the axis distance. If `rotS2 (A K) (-δ*) (A s) = A K`, then `A s = A K`, contradicting strict nonincident since `K+2 ≤ s`.
* `r = 0, s = n`: `endpt A' = 0`, so the desired inequality follows immediately from `sDist_nonneg`.
* `s = n, r > 0`: the no-repeat proof must use the closing edge \((n,0)\) in place of \((s,s+1)\).
* `r = 0, s < n`: use edge \((0,1)\) and edge \((s,s+1)\).
* `r+2 = s`: the loop is \(P_r,P_{r+1},P_r\), so the joint at \(r+1\) is degenerate, contradicting `PositiveJoints`.

## 4. Final classification

`CrossPieceCollisionEndpointAtSup` is **not dischargeable by the already-landed endpoint/IH/subarm bricks**.

It is dischargeable only after adding a substantial geometric simplicity lemma:

```lean
WeakConvexSphArm + PositiveJoints → NoNonadjacentRepeat
```

Without that, it is the genuine sharp residue. The loop-deletion route breaks on `Bhat`; the split-distance route breaks on triangle-inequality direction; and the support-supremum route does not produce `False` merely from nonnegativity.
