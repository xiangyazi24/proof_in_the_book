Commit to this path:

> **Avoid the weak-target comparison entirely.**  
> In the collision branch, do not use `MainPlusNR` with the opened subarm as target. Use the already-banked **interior-axis endpoint monotonicity** directly on the original strict subarm:
>
> \[
> \operatorname{endpt}(A^{r,s})
> \le
> \operatorname{endpt}(\operatorname{openTail}(A^{r,s},K-r,-\delta^*)).
> \]
>
> If the opened endpoints collide, the right side is `0`; the left side is strictly positive by strict no-repeat of `A`. Contradiction.

This avoids `Filter.Tendsto`, avoids weak-target `MainPlusNR`, and avoids proving strictness of the opened subarm below the supremum.

The repo already has the exact endpoint monotonicity theorem you need:

```lean
endpt_openTail_interior_mono :
  StrictConvexSphArm A →
  1 ≤ K.val →
  K.val < n →
  0 ≤ θ →
  θ + sphAngle (A 0) (A K) (A (Fin.last n)) ≤ Real.pi →
  endpt A ≤ endpt (openTail A K (-θ))
```

It is explicitly documented as a banked interior-axis endpoint bound, and its statement does **not** require the opened target arm to be strict. fileciteturn43file0L40-L61

---

## 1. Can weak-target be avoided entirely?

Yes. That is the cleanest solution.

Pure weak convexity cannot rule out endpoint collision: weak convex planar/spherical chains can close. So a direct theorem

```lean
WeakConvexSphArm P → PositiveJoints P → open_hemisphere P → endpt P > 0
```

is false in general.

But the opened subarm is not an arbitrary weak arm. It is

\[
\operatorname{openTail}(A^{r,s},K',-\delta^*)
\]

where \(A^{r,s}\) is a **strict** subarm of the original strict arm. Therefore compare it directly to \(A^{r,s}\) by the endpoint monotonicity theorem, not by `MainPlusNR`.

### Collision branch proof

Let

\[
K=(\operatorname{openingAxis} k).val,
\qquad
\delta^*=\operatorname{monitoredSupWBS} A B k.
\]

Assume a proper cross-piece collision:

\[
r\le K<s,\qquad r+2\le s,\qquad
\operatorname{openedWBS}(r)=\operatorname{openedWBS}(s).
\]

There are two cases.

---

## Case A: `r = K`

Then

\[
\operatorname{openedWBS}(r)=A_K
\]

because the axis is fixed, and

\[
\operatorname{openedWBS}(s)
=
\operatorname{rotS2}(A_K,-\delta^*)(A_s).
\]

If these are equal, then

\[
\operatorname{rotS2}(A_K,-\delta^*)(A_s)=A_K.
\]

But the axis is fixed:

\[
\operatorname{rotS2}(A_K,-\delta^*)(A_K)=A_K.
\]

By injectivity of the rotation,

\[
A_s=A_K.
\]

The repo already has `rotS2_axis_fixed` and `rotS2_injective`. fileciteturn32file0L71-L73 fileciteturn23file0L72-L77

Since `r = K` and `r + 2 ≤ s`, the vertices `K` and `s` are nonadjacent in the original strict arm, contradicting:

```lean
strictConvex_noNonadjacentRepeat hA
```

which is already proved. fileciteturn23file0L42-L70

So the `r = K` collision branch closes without endpoint monotonicity.

---

## Case B: `r < K < s`

Define the interval subarm

```lean
Aint : Fin (m + 1) → S2
Aint t := A ⟨r + t.val, by omega⟩
```

where

```lean
m := s - r
```

and define the local axis

```lean
Kint : Fin (m + 1) := ⟨K - r, by omega⟩
```

Then

\[
1\le Kint.val,\qquad Kint.val<m.
\]

The subarm is strict:

```lean
have hAint : StrictConvexSphArm Aint :=
  strictConvex_intervalArm hA ...
```

If the exact lemma does not already exist, prove it once. It is just restriction of:

* short edges,
* weak/strict nonincident supports,
* open hemisphere,
* positive joints.

Now apply:

```lean
endpt_openTail_interior_mono
  hAint
  (hK0 : 1 ≤ Kint.val)
  (hKn : Kint.val < m)
  (hδ0 : 0 ≤ δ*)
  (hcap : δ* + sphAngle (Aint 0) (Aint Kint) (Aint (Fin.last m)) ≤ Real.pi)
```

to get

```lean
hend_mono :
  endpt Aint ≤ endpt (openTail Aint Kint (-δ*))
```

This is the key: the target may be weak. The theorem only requires the source `Aint` to be strict.

The collision assumption gives

```lean
endpt (openTail Aint Kint (-δ*)) = 0
```

because the opened subarm endpoints are exactly the colliding openedWBS vertices.

The source endpoint is positive:

```lean
0 < endpt Aint
```

because

\[
endpt(Aint)=sDist(A_r,A_s),
\]

and `A_r ≠ A_s` by strict no-repeat of `A`, since `r + 2 ≤ s`.

Thus:

```lean
have hpos : 0 < endpt Aint := ...
have hle : endpt Aint ≤ 0 := by
  rw [hcollision_endpt_zero] at hend_mono
  exact hend_mono
linarith
```

That is the complete collision contradiction.

---

# 2. The only new lemma needed: the subarm cap

The only nontrivial side condition for `endpt_openTail_interior_mono` is:

```lean
hcap :
  δ* + sphAngle (Aint 0) (Aint Kint) (Aint (Fin.last m)) ≤ Real.pi
```

Do **not** prove this by a limit. Prove it from weak convexity of the opened WBS arm at the supremum.

You already construct weak convexity of `openedWBS` from support-stuck in FFCT86:

```lean
hPweak : WeakConvexSphArm (openedWBS A B k)
```

using `supportStuckWBS_weakConvex`. fileciteturn41file0L15-L23

The proof of `hcap` should be packaged as:

```lean
theorem openedWBS_subarm_angle_cap
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A)
    (hPweak : WeakConvexSphArm (openedWBS A B k))
    {r s : ℕ}
    (hrK : r < (openingAxis k).val)
    (hKs : (openingAxis k).val < s)
    (hrs : r + 2 ≤ s) :
    monitoredSupWBS A B k
      + sphAngle (A ⟨r, by omega⟩)
          (A (openingAxis k))
          (A ⟨s, by omega⟩)
      ≤ Real.pi
```

### Proof idea for `openedWBS_subarm_angle_cap`

Let

\[
P=\operatorname{openedWBS} A B k
=
\operatorname{openTail} A K (-\delta^*).
\]

For `r < K < s`,

\[
P_r=A_r,
\qquad
P_K=A_K,
\qquad
P_s=\operatorname{rotS2}(A_K,-\delta^*)A_s.
\]

From weak convexity of `P`, prove the weak diagonal support:

\[
0\le sOrient(P_r,P_K,P_s).
\]

This is a weak version of the strict diagonal support lemma used in the repo for strict arms. The strict version appears as `cut_diagonal_supports` in the proof of `orientedDatum_interior`. fileciteturn43file0L22-L31

You want the weak analogue:

```lean
theorem weak_cut_diagonal_supports
    (hP : WeakConvexSphArm P)
    {i j l : Fin (n + 1)}
    (hij : i < j) (hjl : j < l) :
    0 ≤ sOrient (P i) (P j) (P l)
```

This is standard and should be proved once from weak edge supports by the same diagonal-support induction as the strict version, replacing `<` with `≤`.

Then use the tangent-plane rotation sign lemma:

```lean
theorem angle_cap_of_rotated_support_nonneg
    {x axis y : S2} {δ : ℝ}
    (hstrict0 : 0 < sOrient x axis y)
    (hδ0 : 0 ≤ δ)
    (hδπ : δ ≤ Real.pi)
    (hrotSupp :
      0 ≤ sOrient x axis (rotS2 axis (-δ) y)) :
    δ + sphAngle x axis y ≤ Real.pi
```

This lemma is elementary in the tangent plane at `axis`.

Reason:

* strict original support gives the oriented tangent angle
  \[
  \alpha=\sphAngle(x,axis,y)
  \]
  satisfies
  \[
  0<\alpha<\pi.
  \]
* rotating `y` by `-δ` in the convex-opening direction changes the oriented tangent angle from \(\alpha\) to \(\alpha+\delta\);
* the weak support of the rotated triple says
  \[
  \sin(\alpha+\delta)\ge0;
  \]
* since \(0<\alpha<\pi\), \(0\le\delta\le\pi\), we have
  \[
  0<\alpha+\delta<2\pi;
  \]
* on this interval, \(\sin t\ge0\) implies \(t\le\pi\);
* therefore
  \[
  \delta+\alpha\le\pi.
  \]

The repo already has the tangent-plane machinery behind `endpt_openTail_interior_mono`: it uses `openedAngle_ge_of_oriented_neg`, `orientedSign_neg_of_support`, and `reach_base_endpoint_mono`. fileciteturn43file0L49-L57 The cap lemma is the same geometry, but used to justify the range condition.

You will also need:

```lean
monitoredSupWBS_nonneg :
  0 ≤ monitoredSupWBS A B k

monitoredSupWBS_le_pi :
  monitoredSupWBS A B k ≤ Real.pi
```

These should follow from the admissible-set cap. The monitored supremum infrastructure uses a bounded cap `Tcap`; in the general monitored-sup file, the admissible supremum is defined inside `[0,Tcap]` and membership gives the cap. fileciteturn34file0L177-L188

---

# 3. Exact Lean skeleton for the collision contradiction

Here is the theorem you want to put into the FFCT86 collision branch.

```lean
theorem crossPieceCollision_impossible_by_subarm_endpoint
    {n : ℕ} (ihdim : ∀ m : ℕ, m < n → MainPlusNR m) -- not used, but available
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B)
    (hangle : JointLe A B)
    (k : Fin (n - 1))
    (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k)
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (hrs : r + 2 ≤ s)
    (hrK : r ≤ (openingAxis k).val)
    (hKs : (openingAxis k).val < s)
    (heq :
      openedWBS A B k ⟨r, hr⟩ =
      openedWBS A B k ⟨s, hs⟩) :
    False := by
```

First set:

```lean
let K : Fin (n + 1) := openingAxis k
let δ : ℝ := monitoredSupWBS A B k
```

### Case `r = K.val`

```lean
by_cases hr_eq_K : r = K.val
```

If true:

```lean
have hleft :
    openedWBS A B k ⟨r, hr⟩ = A K := by
  -- unfold openedWBS; openTail_axis or openTail_fixed
  ...

have hright :
    openedWBS A B k ⟨s, hs⟩ =
      rotS2 (A K) (-δ) (A ⟨s, hs⟩) := by
  -- unfold openedWBS; openTail_rot, using K.val < s
  ...

have hrot_eq :
    rotS2 (A K) (-δ) (A ⟨s, hs⟩) =
    rotS2 (A K) (-δ) (A K) := by
  rw [← hright, ← hleft, heq]
  rw [rotS2_axis_fixed]

have hAs_eq_AK : A ⟨s, hs⟩ = A K :=
  rotS2_injective (A K) (-δ) hrot_eq

have hnrA : NoNonadjacentRepeat A :=
  strictConvex_noNonadjacentRepeat hA

-- K + 2 ≤ s follows from r = K and hrs.
exact hnrA K.val s K.isLt hs (by omega) hAs_eq_AK.symm
```

Adjust the final equality orientation as needed.

### Case `r < K.val`

Now define the subarm.

```lean
have hr_lt_K : r < K.val := by omega
let m : ℕ := s - r

have hm_lt_n : m < n := by
  -- proper subarm: r ≥ 1 or s < n; for the full closure r=0,s=n,
  -- handle separately outside this theorem.
  omega

let Aint : Fin (m + 1) → S2 :=
  fun t => A ⟨r + t.val, by omega⟩

let Kint : Fin (m + 1) :=
  ⟨K.val - r, by omega⟩
```

You need the proper-subarm exclusion `¬(r=0 ∧ s=n)` to prove `m<n`. If FFCT86’s collision branch includes full closure, split it first; the user says full closure is handled separately by `endpt = 0`, so keep this theorem for proper pairs only.

Now:

```lean
have hKint0 : 1 ≤ Kint.val := by
  simp [Kint]
  omega

have hKintm : Kint.val < m := by
  simp [Kint, m]
  omega

have hAint : StrictConvexSphArm Aint :=
  strictConvex_intervalArm hA (a := r) (m := m) ...
```

Get weak convexity of the opened WBS arm:

```lean
obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k

have hwrapArc :
    ShortArc
      (openTail A K (-δ) (Fin.last n))
      (openTail A K (-δ) 0) := by
  -- δ unfolds to monitoredSupWBS
  simpa [K, δ] using openedWrapShortArc_at_supWBS hA hB hka hkt hkdef

have hPweak : WeakConvexSphArm (openedWBS A B k) := by
  unfold openedWBS
  simpa [K, δ] using supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrapArc
```

Get the cap:

```lean
have hδ0 : 0 ≤ δ := monitoredSupWBS_nonneg A B k
have hcap :
    δ + sphAngle (Aint 0) (Aint Kint) (Aint (Fin.last m)) ≤ Real.pi := by
  -- rewrite Aint endpoints and Kint:
  -- Aint 0 = A r
  -- Aint Kint = A K
  -- Aint last = A s
  simpa [Aint, Kint, m, K, δ] using
    openedWBS_subarm_angle_cap hA hPweak hr_lt_K hKs hrs
```

Apply endpoint monotonicity:

```lean
have hmono :
    endpt Aint ≤ endpt (openTail Aint Kint (-δ)) :=
  endpt_openTail_interior_mono hAint hKint0 hKintm hδ0 hcap
```

Identify the opened subarm endpoints with the openedWBS endpoints.

```lean
have hopened0 :
    openTail Aint Kint (-δ) 0 =
      openedWBS A B k ⟨r, hr⟩ := by
  -- left endpoint fixed
  simp [Aint, openedWBS, Kint, K, δ, openTail_fixed]

have hopenedLast :
    openTail Aint Kint (-δ) (Fin.last m) =
      openedWBS A B k ⟨s, hs⟩ := by
  -- right endpoint rotated by the same axis and same angle
  simp [Aint, openedWBS, Kint, K, δ, openTail_rot]
```

Collision gives endpoint zero:

```lean
have htarget0 : endpt (openTail Aint Kint (-δ)) = 0 := by
  unfold endpt
  rw [hopened0, hopenedLast, heq]
  -- sDist p p = 0
  simp [sDist_self]
```

Source endpoint is positive:

```lean
have hnrA : NoNonadjacentRepeat A :=
  strictConvex_noNonadjacentRepeat hA

have hA_rs_ne : A ⟨r, hr⟩ ≠ A ⟨s, hs⟩ :=
  hnrA r s hr hs hrs

have hsource_pos : 0 < endpt Aint := by
  unfold endpt
  -- rewrite endpoints of Aint
  have : Aint 0 = A ⟨r, hr⟩ := by simp [Aint]
  have : Aint (Fin.last m) = A ⟨s, hs⟩ := by
    -- since m = s-r
    simp [Aint, m]
  -- close by sDist_pos_of_ne or sDist_eq_zero iff equality
  exact sDist_pos_of_ne hA_rs_ne
```

Contradiction:

```lean
rw [htarget0] at hmono
linarith
```

That closes the proper collision branch. Notice that `ihdim` was not used.

---

# 4. Why the limit route is not recommended

A limit proof would be:

1. for `δ < δ*`, show `openTail Aint Kint (-δ)` is strict;
2. apply `MainPlusNR m` to compare `Aint` with `openTail Aint Kint (-δ)`;
3. take `δ → δ*` from below using continuity of `endpt`.

This is much heavier because step 1 is not free from the generic `sSup` API. You need an interval property: every `δ < δ*` is strictly admissible. A closed admissible set defined by finitely many inequalities need not automatically have that interval property unless the WBS construction has proved it. The monitored-family file proves continuity and supremum membership for finite constraints, but the generic setup is still a closed-set/supremum framework, not a built-in “all smaller angles are strict” theorem. fileciteturn34file0L177-L188

If you nevertheless need the fallback, the clean statement is:

```lean
theorem endpt_openTail_limit_left
    (hmono_lt :
      ∀ δ, 0 ≤ δ → δ < δ* →
        endpt Aint ≤ endpt (openTail Aint Kint (-δ)))
    (hcont :
      ContinuousAt (fun δ => endpt (openTail Aint Kint (-δ))) δ*) :
    endpt Aint ≤ endpt (openTail Aint Kint (-δ*))
```

Prove it using order-closedness of `≤` under limits. In Mathlib this is usually easiest via `isClosed_le` rather than hunting for a specific `le_of_tendsto` lemma:

```lean
have hclosed :
    IsClosed {x : ℝ × ℝ | x.1 ≤ x.2} := isClosed_le continuous_fst continuous_snd
```

or use the sequential version if easier:

```lean
-- choose δ_j = δ* - 1/(j+1) clipped to [0,δ*)
-- prove Tendsto δ_j atTop (𝓝 δ*)
-- apply hmono_lt to each δ_j
-- pass to limit by continuity
```

Continuity pieces:

* `continuous_rot` exists. fileciteturn50file0L25-L35
* `openTail` vertex continuity is already proved in the monitored-sup file as `continuous_openTail_vec`. fileciteturn34file0L99-L116
* `sDist` continuity should be proved from its definition via inner product and `Real.arccos`/angle continuity, or use existing continuity lemmas if present.
* `endpt` continuity is just continuity of the two endpoint vertices composed with `sDist`.

But this route introduces substantially more topology and strict-admissibility bookkeeping than the direct endpoint monotonicity route.

---

# 5. No useful weak-target theorem by swapping

`MainPlusNR` is asymmetric:

```lean
WeakConvexSphArm A →
PositiveJoints A →
NoNonadjacentRepeat A →
StrictConvexSphArm B →
SameSides A B →
JointLe A B →
endpt A ≤ endpt B
```

fileciteturn39file0L62-L68

Swapping roles would require:

\[
JointLe(\text{opened}, Aint)
\]

instead of

\[
JointLe(Aint,\text{opened}),
\]

which is the wrong direction: the opened joint is larger. It would also require `Aint` as strict target and the opened arm as weak source, giving the inequality

\[
endpt(\text{opened}) \le endpt(Aint),
\]

the opposite of what you need.

So there is no symmetry trick here.

A weak-target theorem can be derived by limit, but it is unnecessary for the collision branch.

---

# 6. Should you prove `subarm_opened_endpt_pos` directly?

Yes. This is the right packaging.

Define:

```lean
theorem proper_openedWBS_subarm_endpt_pos
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (k : Fin (n - 1))
    (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k)
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (hrs : r + 2 ≤ s)
    (hrK : r ≤ (openingAxis k).val)
    (hKs : (openingAxis k).val < s)
    (hproper : ¬ (r = 0 ∧ s = n)) :
    0 < sDist
      (openedWBS A B k ⟨r, hr⟩)
      (openedWBS A B k ⟨s, hs⟩)
```

Then the collision branch is one line:

```lean
have hpos := proper_openedWBS_subarm_endpt_pos A B hA hB k hkdef hstuck
  hr hs hrs hrK hKs hproper
rw [heq, sDist_self] at hpos
linarith
```

Inside `proper_openedWBS_subarm_endpt_pos`, use the proof above:

* `r = K`: rotation-injectivity + strict no-repeat;
* `r < K`: interval subarm + `endpt_openTail_interior_mono`.

This lemma is non-circular, does not use `MainPlusNR`, does not use no-repeat of the opened arm, and does not require the opened subarm to be strict.

---

## Final recommendation

Implement `proper_openedWBS_subarm_endpt_pos`.

Dependencies to add/prove:

1. `strictConvex_intervalArm` if absent.
2. `weak_cut_diagonal_supports` for weak convex arms.
3. `openedWBS_subarm_angle_cap`, using weak diagonal support of the opened arm.
4. endpoint identification lemmas for `openTail` restricted to an interval.
5. `sDist_pos_of_ne` or the equivalent `sDist_eq_zero ↔ p = q`.

Do **not** implement the limit proof unless the cap lemma unexpectedly becomes harder than expected. The direct endpoint-monotonicity route is shorter, avoids weak-target `MainPlusNR`, and uses a theorem already banked exactly for interior openings.
