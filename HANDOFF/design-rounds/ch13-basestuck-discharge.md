[intro]
I’ll read FFCT41 and the relevant assembly/splice consumers now so the BaseStuck discharge lines up with the actual residual shape.

The key residual is exactly as FFCT41 states: `BaseStuckProgressW` must turn base-straightening into recursion-ready progress, not just endpoint monotonicity. I’m checking whether existing interval/splice IH wrappers already give the two diagonal comparisons needed for the straightening argument.

[answer]
1. **Core verdict**

`BaseStuckProgressW` in FFCT41 has the wrong output shape for the classical straightening case. Its current conclusion asks for `ReachWB ∨ ∃ vanishing NonIncident support`, but a genuine base-stuck branch may have neither: the base monitor binds, all W-supports stay strict, and the target joint has not reached. FFCT41 already says this branch needs route (b)’s straightening completion, not another W-monitor payload. filecite the clean repair is: **replace/supersede `BaseStuckProgressW` by a terminal endpoint branch**, then rethread the headline step with a third alternative: REACH / CUT / TERMINAL.

---

2. **Existing endpoint monotonicity is not enough**

FFCT41 already has:

```lean
theorem glueWB_clause_i ... :
  endpt A ≤ endpt (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)))
```

using the now-proved base cap. file endpt A'`. To finish the parent goal, we need `endpt A' ≤ endpt B` or, equivalently in your “maximal endpoint” framing, show `endpt B ≤ endpt A'` only if the comparison direction is being used as a contradiction/completion. In the MainPlus spine the goal is always `endpt A ≤ endpt B`, so the useful terminal theorem must be:

```lean
endpt A' ≤ endpt B
```

not `endpt A' ≥ endpt B`.

Audit: the classical straightening argument as phrased “A' has maximal endpoint” proves `B ≤ A'`, the opposite direction from `MainPlus`. That means the intended statement must be checked carefully: if base straightening maximizes the endpoint among configurations with the same side lengths and smaller/equal joints, then since `B` has **larger** joints, the endpoint should be **at least** the straightened A', not at most. The correct terminal target is therefore:

```lean
endpt A' ≤ endpt B
```

using sub-arm IH plus triangle inequality in the direction below.

---

3. **Straight base distance lemma**

Use this pointwise lemma:

```lean
theorem baseStraight_dist_add
    {a k q : S2}
    (hπ : sphAngle a k q = Real.pi)
    (hka : ShortArc k a) (hkq : ShortArc k q)
    (hhemi : ∃ h : E3, ‖h‖ = 1 ∧
      0 < (⟪h, (a : E3)⟫ : ℝ) ∧
      0 < (⟪h, (k : E3)⟫ : ℝ) ∧
      0 < (⟪h, (q : E3)⟫ : ℝ)) :
    sDist a q = sDist a k + sDist k q
```

Sketch: `sphAngle = π` gives antiparallel nonzero tangents at `k`, hence `a,k,q` lie on one great circle and `k` lies between `a` and `q`. The only branch risk is `sDist a k + sDist k q > π`, where arccos wraps; the open hemisphere kills it because a great circle intersects an open hemisphere in an open semicircle, so three points in that hemisphere lie on an arc of length `< π`. This is the right place to formalize your “open hemisphere kills bad case” observation.

Classification: **master**, 180–300 lines.

---

4. **Hemisphere-on-great-circle cap lemma**

Factor the hard branch-control part:

```lean
theorem greatCircle_openHemisphere_arc_sum_lt_pi
    {a k q : S2}
    (hcol : det3 (a : E3) (k : E3) (q : E3) = 0)
    (hka : ShortArc k a) (hkq : ShortArc k q)
    (hhemi : ∃ h : E3, ‖h‖ = 1 ∧
      0 < (⟪h, (a : E3)⟫ : ℝ) ∧
      0 < (⟪h, (k : E3)⟫ : ℝ) ∧
      0 < (⟪h, (q : E3)⟫ : ℝ))
    (hbetween : TangentsAntiparallelAt k a q) :
    sDist a k + sDist k q < Real.pi
```

Sketch: choose the oriented 2D coordinates on the great circle plane. The functional `x ↦ ⟪h,x⟫` restricts to a nonzero sinusoid on that great circle, positive exactly on an open semicircle. Since all three points are in its positive set and `k` is between the endpoints, the through-arc length is `< π`.

Classification: **master**, 200–350 lines.  
This is the real geometric kernel of the straightening branch.

---

5. **Sub-arm IH comparisons**

Let

```lean
A' := openTail A (openingAxis k) (-(monitoredSupWB A B k h₀))
K := (openingAxis k).val
```

Need two interval-arm comparisons:

```lean
theorem baseStuck_left_diag_le
    {n : ℕ} {A' B : Fin (n + 1) → S2}
    (ihdim : ∀ m, m < n → MainPlus m)
    (hA'weak : WeakConvexSphArm A')
    (hA'pos : PositiveJoints A')
    (hB : StrictConvexSphArm B)
    (hside : SameSides A' B) (hangle : JointLe A' B)
    {K : ℕ} (hK0 : 0 < K) (hKn : K < n) :
    sDist (A' 0) (A' ⟨K, by omega⟩)
      ≤ sDist (B 0) (B ⟨K, by omega⟩)
```

```lean
theorem baseStuck_right_diag_le
    {n : ℕ} {A' B : Fin (n + 1) → S2}
    (ihdim : ∀ m, m < n → MainPlus m)
    (hA'weak : WeakConvexSphArm A')
    (hA'pos : PositiveJoints A')
    (hB : StrictConvexSphArm B)
    (hside : SameSides A' B) (hangle : JointLe A' B)
    {K : ℕ} (hK0 : 0 < K) (hKn : K < n) :
    sDist (A' ⟨K, by omega⟩) (A' (Fin.last n))
      ≤ sDist (B ⟨K, by omega⟩) (B (Fin.last n))
```

Sketch: instantiate `MainPlus K` on `intervalArm A' 0 K` and `intervalArm B 0 K` for the left. Instantiate `MainPlus (n-K)` on `intervalArm A' K (n-K)` and `intervalArm B K (n-K)` for the right. Use `intervalArm_positiveJoints`, `intervalArm_sameSides`, `intervalArm_jointLe`, and interval convexity certificates already used by the ear machinery.

Classification: **needs-care**, 120–220 lines each.

---

6. **Straightened terminal comparison**

```lean
theorem baseStuck_terminal_endpt_le
    {n : ℕ} {A' B : Fin (n + 1) → S2}
    {K : ℕ} (hK0 : 0 < K) (hKn : K < n)
    (hstraight :
      sphAngle (A' 0) (A' ⟨K, by omega⟩) (A' (Fin.last n)) = Real.pi)
    (hhemi : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A' r : E3)⟫ : ℝ))
    (hleft :
      sDist (A' 0) (A' ⟨K, by omega⟩)
        ≤ sDist (B 0) (B ⟨K, by omega⟩))
    (hright :
      sDist (A' ⟨K, by omega⟩) (A' (Fin.last n))
        ≤ sDist (B ⟨K, by omega⟩) (B (Fin.last n))) :
    endpt A' ≤ endpt B
```

Sketch: `baseStraight_dist_add` gives `endpt A' = leftA + rightA`. Triangle inequality gives `sDist B0 Blast ≤ sDist B0 BK + sDist BK Blast`; but this is the wrong direction for `A' ≤ B`. So the sub-arm inequalities as written are also the wrong direction.

Correct comparison must be:

```lean
sDist (B 0) (B K) ≤ sDist (A' 0) (A' K)
sDist (B K) (B last) ≤ sDist (A' K) (A' last)
```

But `MainPlus` gives `A-subarm ≤ B-subarm`, not `B ≤ A`. Therefore **the classical “straightened A is maximal” route cannot close `MainPlus` in the stated direction through MainPlus IH**.

This is the crucial sign audit.

Classification: **blocking finding**.

---

7. **Consequence: route (b) as described is directionally wrong**

The proposed chain

```text
d(B0,BK) ≤ d(A0,AK), d(BK,Blast) ≤ d(AK,Alast)
```

does not follow from the SZ invariant. The invariant gives the opposite if the left arm is `A'` and right arm is `B`:

```text
d(A'0,A'K) ≤ d(B0,BK)
d(A'K,A'last) ≤ d(BK,Blast)
```

Then straightening gives

```text
endpt A' = leftA + rightA ≤ leftB + rightB
```

and triangle gives

```text
endpt B ≤ leftB + rightB
```

These do not compare `endpt A'` and `endpt B`.

So a base-straight terminal proof needs **additional structure**, not just the two sub-arm IHs.

---

8. **Correct replacement target for BaseStuckProgressW**

Do not try to prove direct endpoint completion from straightening alone. Instead prove that base-stuck forces an ordinary W outcome after all:

```lean
theorem baseStuck_forces_reach_or_support
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    {k : Fin (n - 1)} (hkdef : jointAngle A k < jointAngle B k)
    {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (hbase : BaseStuckWB A B k h₀) :
    ReachWB A B k h₀ ∨
      ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) i)
          (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (i + 1))
          (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) j) = 0
```

This is exactly `BaseStuckProgressW`’s current shape. FFCT41’s residual is therefore correctly shaped; the “straightening completion” route is not.

Classification: **master**, still open.

---

9. **How to attack `baseStuck_forces_reach_or_support`**

Use base straightening as a **support-production** mechanism, not endpoint completion.

When base support vanishes:

```lean
sOrient (A 0) (A K) (A' last) = 0
```

This is not a `NonIncident` edge support, but the strict W-support closure says every real edge support is `≥0`; if no real edge support vanishes, they are all `>0`, hence `A'` is strict. In that strict pure-base-stuck configuration, the base triple is a diagonal support crossing the polygon. Strict convexity plus diagonal support zero should force a chain of edge supports to vanish, by the same planar/gnomonic convex polygon logic used in B5/FFCT25.

Brick:

```lean
theorem baseDiagonal_zero_forces_edgeSupport_zero
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : StrictConvexSphArm P)
    {K : Fin (n + 1)} (hKint : 0 < K.val ∧ K.val < n)
    (hbase0 :
      sOrient (P 0) (P K) (P (Fin.last n)) = 0) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (P i) (P (i + 1)) (P j) = 0
```

This contradicts strictness, so if `P` is strict, base diagonal zero is impossible. Therefore base-stuck must coincide with either REACH or a W-support vanish.

Classification: **genuinely-hard**, 250–450 lines.  
This is the real discharge of `BaseStuckProgressW`.

---

10. **More precise finite version**

Because `P = A'_WB` is strict if no W-support/hemi vanished and edges are distinct, prove:

```lean
theorem no_baseStuck_without_W_stuck_or_reach
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    {k : Fin (n - 1)} (hkdef : jointAngle A k < jointAngle B k)
    {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (hbase : BaseStuckWB A B k h₀)
    (hnotReach : ¬ ReachWB A B k h₀)
    (hnoSupport :
      ¬ ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) i)
          (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (i + 1))
          (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) j) = 0) :
    False
```

Sketch: `hbase` gives base diagonal zero. `hnoSupport` + W closure gives all edge supports strict. `hhpos` plus WB hemi closure / no hemi-stuck gives strict hemisphere; or use pure-hemi strict-convex machinery from FFCT41. Then `baseDiagonal_zero_forces_edgeSupport_zero` contradicts `hnoSupport`.

Classification: **master wrapper**, 120–180 lines after diagonal lemma.

---

11. **Why SpliceBodyDiagMono is not the right tool here**

`SpliceStructuralData` / `SpliceBodyDiagMono` belong to CUT after a real nonincident support vanishes. `SphericalArmAssembly` states the CUT branch consumes a vanishing support, constructs splice bodies, then calls `splice_transport_of_diag_le`. fileciteturn140file0L120-L164

Base-stuck has no edge-support vanishing; its zero is the diagonal triple `(0,K,last)`. So it must first be converted into a genuine nonincident edge support vanish. Only then the existing CUT machinery applies.

---

12. **Degenerate audit**

`K = 0` or `K = last`: impossible; `openingAxis k = k+1` is interior, and FFCT41 already uses `openingAxis_interior`. fileciteturn134file0 equal endpoints, then `endpt A'=0`; in a strict convex arm this would force a repeated nonadjacent vertex. This should be killed by `NoNonadjacentRepeat` or strict support.

`δ*=0` with initial base `γbase=π`: strict convexity excludes the base diagonal zero for interior `K`; FFCT41’s `base_sphAngle_lt_pi` already proves `γbase < π` from strict base support. fileciteturn135file0L lemma is true, but it is not sufficient to close the endpoint comparison in the MainPlus direction. It may still be useful inside `baseStraight_dist_add`, but it is not the decisive route.

---

13. **Ordered bricks**

1. `baseDiagonal_zero_forces_edgeSupport_zero` — master, 250–450 lines.  
   Prove a zero diagonal support in a strict/weak positive convex spherical polygon forces a zero edge support.

2. `strict_no_baseDiagonal_zero` — worker wrapper, 40–70 lines.  
   ```lean
   theorem strict_no_baseDiagonal_zero
     (hP : StrictConvexSphArm P) ... :
     sOrient (P 0) (P K) (P (Fin.last n)) ≠ 0
   ```

3. `baseStuck_not_pure_strict` — needs-care, 80–140 lines.  
   Apply (2) to `P = A'_WB` under the no-support/no-hemi branch where FFCT41 can build strict convexity.

4. `no_baseStuck_without_W_stuck_or_reach` — master wrapper, 120–180 lines.  
   Contradict `BaseStuckWB ∧ ¬ReachWB ∧ no support vanish`.

5. `baseStuck_forces_reach_or_support` / `BaseStuckProgressW_holds` — worker wrapper, 50–90 lines.  
   This proves the exact FFCT41 residual shape.

6. Re-run:
   ```lean
   interiorOpeningOutcomeWB_basecapped
   mainPlus_headline_basecapped
   ```
   with `BaseStuckProgressW_holds`.

---

14. **Final recommendation**

Do **not** discharge BaseStuck by a straightened endpoint comparison; the inequality direction does not align with `MainPlus`. Discharge it by proving that a base-diagonal support zero cannot be the first/only boundary event in a strict convex opened arm: it must force an actual nonincident edge support zero, which is exactly the existing CUT-ready payload.
