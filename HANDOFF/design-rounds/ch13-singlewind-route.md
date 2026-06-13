[intro]
I’ll pin one subtlety before recommending a route: “edge-direction span < 2π” only works if it is a lifted cyclic/single-wind certificate, not just the raw set of segment directions. A one-round triangle already has repeated endpoint with raw span `< 2π` unless the closing/wrap convention forbids it.

[answer]
## Verdict

The correction is right: the missing invariant is **single winding**, not local weak convexity. But I would not encode the final theorem as a raw spherical statement

```lean
∑ i, (Real.pi - jointAngle P i) < 2 * Real.pi
```

unless you already have a proved spherical Gauss–Bonnet / lifted-turn bridge. The Lean-friendly route is:

```text
gnomonic projection → finite lifted planar edge-turn certificate → no nonadjacent repeat
```

This matches the existing substrate: the public chain already uses gnomonic projection to transport spherical orientations to planar `det3` signs, and the later planar convex-position file succeeds with finite Plücker/`det3` algebra rather than Mathlib winding-number infrastructure. fileciteturn15file0, but strengthen it: do **not** use “all edge-direction arguments lie in an interval of length `< 2π`” as the theorem by itself. The telescoping proof with one covector `g` only works when the relevant subchain’s edge directions lie in an **open semicircle**—span `< π`, not `< 2π`.

The robust planar core should be stated with a lifted single-wind certificate:

```lean
/-- A finite lifted edge-direction certificate for a planar chain.  This avoids
Mathlib winding numbers.  The data says that every edge has a positive length
and a real lifted direction, consecutive turns are positive and bounded, and
the whole cyclic/open arm makes less than one forbidden extra turn. -/
structure PlanarLiftedTurnSpan
    {N : ℕ} (Q : Fin N → E3) (h u v : E3) : Prop where
  in_plane : ∀ i, (⟪h, Q i⟫ : ℝ) = 1
  u_perp_h : (⟪h, u⟫ : ℝ) = 0
  v_perp_h : (⟪h, v⟫ : ℝ) = 0
  uv_orthonormal : ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ (⟪u, v⟫ : ℝ) = 0
  θ : ℕ → ℝ
  ρ : Fin N → ℝ
  ρ_pos : ∀ i, 0 < ρ i
  edge_eq :
    ∀ i : Fin N,
      Q (i + 1) - Q i =
        ρ i • (Real.cos (θ i.val) • u + Real.sin (θ i.val) • v)
  turn_pos : ∀ i : Fin N, 0 < θ (i.val + 1) - θ i.val
  turn_lt_pi : ∀ i : Fin N, θ (i.val + 1) - θ i.val < Real.pi
  one_wind : θ N - θ 0 < 2 * Real.pi
```

Then the theorem should be:

```lean
/--
Weak planar convexity plus strict positive lifted turns plus a one-wind
turn-span forbids nonadjacent repeated vertices.

This is the corrected replacement for the false
`weakConvex_boundedJoints_noNonadjacentRepeat`.
-/
theorem planarWeakConvex_strictTurns_oneWind_noNonadjacentRepeat
    {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3}
    (hedge : ∀ i : Fin N, Q (i + 1) ≠ Q i)
    (hsupp : ∀ i j : Fin N, j ≠ i → j ≠ i + 1 →
      0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hlift : PlanarLiftedTurnSpan Q h u v) :
    NoNonadjacentRepeat Q := by
  -- proof outline:
  -- 1. Assume Q r = Q s with r + 2 ≤ s.
  -- 2. The subchain r..s is a closed positive-turn weakly-convex loop.
  -- 3. A closed positive-turn weakly-convex loop consumes a full lifted turn.
  -- 4. The remaining part of the arm has strictly positive turn as well.
  -- 5. Hence the total lifted span reaches at least 2π, contradicting `one_wind`.
  -- The small telescoping lemma is used only on subarcs known to lie in an
  -- open half-plane; it is not the whole proof.
  sorry
```

And the spherical transport layer:

```lean
/-- Gnomonic single-wind certificate for a spherical arm. -/
structure GnomonicSingleWind {n : ℕ} (P : Fin (n + 1) → S2) : Prop where
  h : E3
  hnorm : ‖h‖ = 1
  hpos : ∀ i, 0 < (⟪h, (P i : E3)⟫ : ℝ)
  u v : E3
  lifted :
    PlanarLiftedTurnSpan
      (fun i : Fin (n + 1) => gproj h (P i)) h u v

theorem weakConvex_positiveJoints_singleWind_noNonadjacentRepeat
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hW : WeakConvexSphArm P)
    (hpos : PositiveJoints P)
    (hsw : GnomonicSingleWind P) :
    NoNonadjacentRepeat P := by
  -- gnomonic injectivity + support sign transport + planar theorem
  sorry
```

This blocks the doubled triangle because its lifted edge directions go around twice. Locally it still satisfies weak convexity and positive joints, but it cannot produce `GnomonicSingleWind`.

## Q2. Proving `openedWBS` has the turn bound

There are two different “turn sums”; keep them separate.

For the **internal open-arm exterior sum**

```lean
def openExteriorTurnSum {n : ℕ} (P : Fin (n + 1) → S2) : ℝ :=
  ∑ i : Fin (n - 1), (Real.pi - jointAngle P i)
```

the WBS proof is clean:

```lean
theorem openExteriorTurnSum_openedWBS_le
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hreachOrStuck : SupportStuckWBS A B k)
    (hopen : jointAngle A k ≤ jointAngle (openedWBS A B k) k)
    (hpres :
      ∀ r : Fin (n - 1), r ≠ k →
        jointAngle (openedWBS A B k) r = jointAngle A r) :
    openExteriorTurnSum (openedWBS A B k) ≤ openExteriorTurnSum A := by
  -- all terms equal except k; at k, larger joint means smaller exterior angle
  sorry
```

Then:

```lean
theorem openExteriorTurnSum_openedWBS_lt_two_pi
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hAturn : openExteriorTurnSum A < 2 * Real.pi)
    ... :
    openExteriorTurnSum (openedWBS A B k) < 2 * Real.pi :=
  lt_of_le_of_lt (openExteriorTurnSum_openedWBS_le ...) hAturn
```

But: this scalar internal sum should be treated as a **certificate source**, not the final no-repeat theorem, unless you prove the bridge:

```lean
theorem openExteriorTurnSum_lt_two_pi_to_gnomonicSingleWind
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hW : WeakConvexSphArm P)
    (hpos : PositiveJoints P)
    (hturn : openExteriorTurnSum P < 2 * Real.pi) :
    GnomonicSingleWind P := by
  sorry
```

The cleanest route for strict `A` is not a spherical Gauss–Bonnet development. Use the hemisphere normal, gnomonic projection, and finite planar strict convexity:

```lean
theorem strictConvexSphArm_gnomonicSingleWind
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) :
    GnomonicSingleWind A := by
  -- open hemisphere normal from hA
  -- gnomonic projection to affine plane
  -- strict edge supports become strict planar convexity
  -- strict planar convex chain has one lifted turn
  sorry
```

Then preserve it under WBS opening:

```lean
theorem openedWBS_gnomonicSingleWind
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (hss : SameSides A B)
    (hle : JointLe A B)
    (hstuck : SupportStuckWBS A B k) :
    GnomonicSingleWind (openedWBS A B k) := by
  -- Either:
  --   derive from `openExteriorTurnSum_openedWBS_lt_two_pi`
  --   plus the bridge to `GnomonicSingleWind`,
  -- or prove single-wind preservation directly along the openTail homotopy.
  sorry
```

The direct homotopy proof is probably cleaner than a full spherical turn-sum theory.

## Q3. Continuity / first-binding route

Endpoint continuity is true and useful, but it does not remove the hard theorem by itself.

The formal limit lemma would be:

```lean
theorem endpoint_le_at_sup_of_eventually_endpoint_le
    {n : ℕ} {A B : Fin (n + 1) → S2} {K : Fin (n + 1)}
    {δstar : ℝ}
    (hcont :
      ContinuousWithinAt
        (fun δ => endpt (openTail A K (-δ)))
        (Set.Iic δstar) δstar)
    (hbelow :
      ∀ᶠ δ in 𝓝[<] δstar,
        endpt (openTail A K (-δ)) ≤ endpt B) :
    endpt (openTail A K (-δstar)) ≤ endpt B := by
  -- tendsto + closedness of `{x | x ≤ endpt B}`
  sorry
```

But the premise

```lean
∀ δ < δstar, endpt (openTail A K (-δ)) ≤ endpt B
```

is not free. For `δ < δstar`, the arm is merely an intermediate opened arm. It has not necessarily reached the target joint, and it has not necessarily produced the terminal stuck witness. To prove endpoint comparison for every intermediate `δ`, you would need essentially the same arm monotonicity theorem you are trying to finish.

So the continuity route is good only as a final topological wrapper **after** you already have a normal-case theorem for all pre-sup arms. It is not the shortest way to discharge `CrossPieceCollisionEndpointAtSup`.

## Q4. Recommended route to unconditional Ch13

Use the single-wind no-repeat route and make the collision branch vacuous.

Ordered bricks:

```lean
-- A. Finite planar lifted-turn API.
structure PlanarLiftedTurnSpan
    {N : ℕ} (Q : Fin N → E3) (h u v : E3) : Prop := ...

-- B. Planar theorem replacing the false FFCT92-style statement.
theorem planarWeakConvex_strictTurns_oneWind_noNonadjacentRepeat
    {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3}
    (hedge : ∀ i : Fin N, Q (i + 1) ≠ Q i)
    (hsupp : ∀ i j : Fin N, j ≠ i → j ≠ i + 1 →
      0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hlift : PlanarLiftedTurnSpan Q h u v) :
    NoNonadjacentRepeat Q

-- C. Gnomonic transport.
theorem weakConvex_positiveJoints_gnomonicSingleWind_noRepeat
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hW : WeakConvexSphArm P)
    (hpos : PositiveJoints P)
    (hsw : GnomonicSingleWind P) :
    NoNonadjacentRepeat P

-- D. WBS single-wind.
theorem openedWBS_gnomonicSingleWind
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (hss : SameSides A B)
    (hle : JointLe A B)
    (hstuck : SupportStuckWBS A B k) :
    GnomonicSingleWind (openedWBS A B k)

-- E. WBS no-repeat.
theorem openedWBS_noNonadjacentRepeat
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (hss : SameSides A B)
    (hle : JointLe A B)
    (hstuck : SupportStuckWBS A B k)
    (hW : WeakConvexSphArm (openedWBS A B k))
    (hpos : PositiveJoints (openedWBS A B k)) :
    NoNonadjacentRepeat (openedWBS A B k) :=
  weakConvex_positiveJoints_gnomonicSingleWind_noRepeat hW hpos
    (openedWBS_gnomonicSingleWind hA hB hss hle hstuck)

-- F. Collision contradiction.
theorem crossPieceCollision_false_of_openedWBS_noRepeat
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {r s : Fin (n + 1)}
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hrs : r.val + 2 ≤ s.val)
    (hcoll : openedWBS A B k r = openedWBS A B k s) :
    False := by
  exact hnr r s hrs hcoll

-- G. Discharge the residue.
theorem crossPieceCollisionEndpointAtSup_holds :
    CrossPieceCollisionEndpointAtSup := by
  intro n A B hA hB hss hle k hklt hstuck r s hrs hrK hKs hcoll
  have hW : WeakConvexSphArm (openedWBS A B k) := by
    -- FFCT46 / landed openedWBS weak convex
    sorry
  have hpos : PositiveJoints (openedWBS A B k) := by
    -- landed PositiveJoints for openedWBS
    sorry
  have hnr :=
    openedWBS_noNonadjacentRepeat hA hB hss hle hstuck hW hpos
  exact False.elim
    (crossPieceCollision_false_of_openedWBS_noRepeat hnr hrs hcoll)
```

Degenerate audit:

| Case | Handling |
|---|---|
| `r = K` | independently impossible by rotation-distance preservation, but no longer needed once `NoNonadjacentRepeat` is available |
| `r = 0, s = n` | if your `NoNonadjacentRepeat` includes endpoint repeats, covered; otherwise keep the trivial worker `endpt = 0 ≤ endpt B` |
| `s = n`, `r > 0` | covered by no-repeat if endpoint repeats are included |
| `r + 2 = s` | covered; the minimal loop cannot occur under single-wind no-repeat |
| doubled triangle | fails `GnomonicSingleWind` / lifted one-wind bound, so it no longer refutes the theorem |

Final recommendation: **do not use the continuity-limit route as the main proof**. Use the finite gnomonic single-wind invariant to prove `openedWBS` has `NoNonadjacentRepeat`; then `CrossPieceCollisionEndpointAtSup` is vacuous, and `spherical_arm_mono_final_ch13_v11` becomes unconditional.
