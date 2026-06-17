The decisive answer: **closing-pinned does not rescue this field**, at least not from the current hypotheses/API. The honest fix is to make the stars in the realization **rooted/rotated consistently with `dartRep`**, not to keep a fixed `Quotient.out` root and try to prove `interiorActive` afterward.

The reason is exactly what you noticed: `interiorActive` is an arm statement about the opened link, whose interior joints exclude closed-link indices `0` and `n`. The repo’s full-link layer explicitly says the closed link has `n+1` angles, while the arm exposes only the `n-1` interior joints and hides the two closing angles `0` and `n`. fileciteturn106file0L8-L19 The `cauchyArmVertexFull_of_links` input still requires an interior witness

```lean
hactive : ∃ i : Fin (n - 1), jointAngle A i ≠ jointAngle B i
```

not merely a nonzero full-link `linkDiff`. fileciteturn106file0L129-L134

## 1. Why re-rooting only inside the proof does not work

Suppose the fixed-root links are

```lean
A := (fixedStarP Q).vertexLink
B := (fixedStarQ Q).vertexLink
```

and an active dart corresponds to full link index `k : Fin (n+1)`. If you rotate both links by `r`, then the active angle can be made an interior angle of

```lean
rotPoly A r
rotPoly B r
```

because `rotPoly_jointAngle` identifies rotated interior joints with cyclic triples in the original link. fileciteturn109file0L53-L61

But `interiorActive` for the realization asks for an interior index of the **original** field

```lean
(starP Q).vertexLink
```

not of a temporary rotated link. If the only nonzero full-link differences are at original indices `0` or `n`, then a rotated interior witness transports back to one of those original closing indices, not to an original `Fin (n-1)` joint.

So this implication is false as a pure index statement:

```lean
∃ k : Fin (n+1), linkDiff A B k ≠ 0
  → ∃ i : Fin (n-1), jointAngle A i ≠ jointAngle B i
```

unless you add a separate theorem ruling out nonzero differences at the closing indices.

## 2. Closing-pinned is not available from `sides_eq + close_eq`

The statement

```lean
linkDiff A B 0 = 0 ∧ linkDiff A B (Fin.last n) = 0
```

does **not** follow from just

```lean
hsides : ∀ i : Fin n, sideLen A i = sideLen B i
hclose : sDist (A 0) (A (Fin.last n)) =
         sDist (B 0) (B (Fin.last n))
```

The closing angle at `0` is the angle in the spherical triangle

```text
A n, A 0, A 1
```

so it depends on the diagonal distance `sDist (A n) (A 1)`. That diagonal is not one of the arm sides and is not the closing chord. Similarly, the closing angle at `n` depends on the diagonal `sDist (A 0) (A (n-1))`.

What is true, but much stronger, is something like:

```lean
all interior joint angles equal
+ all sides equal
+ closing chord equal
→ closing endpoint angles equal
```

That is a spherical chain-congruence theorem. It is not in the current Ch13 API, and proving it would be a substantial new spherical-geometry lemma. It is not the clean route for the final assembly.

So the precise status is:

```lean
sides_eq + close_eq
  ⊬ closing link angles equal
```

and therefore fixed-root `interiorActive` is not derivable from active full-link edge signs without additional structure.

## 3. The clean honest fix: rotate/root the actual `starP` and `starQ` fields

Do not keep

```lean
starP Q := vertexStarOfEuclidean P Q -- fixed at Quotient.out Q
```

if you need `interiorActive`.

Instead, define either:

```lean
vertexStarOfEuclideanAtDart P (r : D) (hr : M.tail r = Q) : VertexStar
```

or a cheaper wrapper:

```lean
VertexStar.rotate : VertexStar → Fin (n+1) → VertexStar
```

and set the realization fields to the rotated stars.

### Rotation wrapper

This is probably the least invasive if your geometric star is already built.

```lean
namespace VertexStar

noncomputable def rotate (S : VertexStar) (k : Fin (S.n + 1)) : VertexStar where
  n := S.n
  hn := S.hn
  o := S.o
  p := fun i => S.p (i + k)
  apex_ne := by
    intro i
    exact S.apex_ne (i + k)
  open_hemi := by
    rcases S.open_hemi with ⟨h, hn, hpos⟩
    exact ⟨h, hn, fun i => hpos (i + k)⟩
  turn_support := by
    intro i j
    -- (i+1)+k = (i+k)+1
    have hnext : (i + 1 : Fin (S.n + 1)) + k = (i + k) + 1 := by
      rw [add_right_comm]
    simpa [hnext] using S.turn_support (i + k) (j + k)
  turn_strict := by
    intro i j hji hji1
    have hnext : (i + 1 : Fin (S.n + 1)) + k = (i + k) + 1 := by
      rw [add_right_comm]
    apply S.turn_strict (i + k) (j + k)
    · intro h
      exact hji (add_right_cancel h)
    · intro h
      apply hji1
      have h' : j + k = (i + 1) + k := by
        rw [hnext]
        exact h
      exact add_right_cancel h'

end VertexStar
```

Then prove the link equation:

```lean
lemma vertexLink_rotate (S : VertexStar) (k : Fin (S.n + 1)) :
    (S.rotate k).vertexLink = rotPoly S.vertexLink k := by
  funext i
  -- both are the normalized direction of `S.p (i+k) - S.o`
  rfl
```

If `rfl` does not work because `edgeDir` unfolds with different definitional paths, prove it by extensionality on `S2` and simp through `rawDir`, `edgeDir`, and `rotPoly`.

This uses the existing repo fact that `rotPoly` preserves strict convexity, and its joint angles are cyclic reindexings. fileciteturn112file0L48-L87

## 4. Choose the root/rotation adaptively

For each vertex `Q`, choose the realization’s root/rotation using the already-defined edge signs.

Let `m := (fixedStarP Q).n + 1`.

If the vertex is active, choose an active dart `x` in the σ-cycle. Since the star order is reverse-σ, choose the star root so that `x` lands at link index `1`. Earlier arithmetic was right:

```lean
root := M.σ^[2] x
```

because in the forward σ-list rooted at `σ² x`, the dart `x` is at forward index `m - 2`; after reversing, it is at star index `1`.

If you use `VertexStar.rotate` from a fixed root instead, choose the corresponding rotation offset `kQ` so that the selected active dart’s old fixed-root star index becomes new index `1`.

The construction should expose this lemma:

```lean
lemma active_at_link_index_one
    (Q : M.Vertex)
    (hact : ActiveVertex M edgeSign (dartRep Q)) :
    edgeSign (starDart Q ⟨1, by have hn := (starP Q).hn; omega⟩) ≠ EdgeSign.zero
```

Here `starDart Q i` is the dart corresponding to link index `i` in the **actual** `starP Q` used in the realization.

Then `interiorActive` is short.

## 5. Final `interiorActive` proof after rooting the stars correctly

Assume you have:

```lean
starDart_value :
  ∀ Q i,
    edgeSign (starDart Q i)
      =
    realSignToEdgeSign
      (linkDiff (starP Q).vertexLink (linkQ Q) i)

active_at_link_index_one :
  ∀ Q,
    ActiveVertex M edgeSign (dartRep Q) →
      edgeSign (starDart Q ⟨1, by have hn := (starP Q).hn; omega⟩)
        ≠ EdgeSign.zero
```

Then:

```lean
theorem interiorActive_of_rooted_star
    (Q : M.Vertex)
    (hact : ActiveVertex M edgeSign (dartRep Q)) :
    ∃ i : Fin ((starP Q).n - 1),
      jointAngle (starP Q).vertexLink i ≠
        jointAngle (linkQ Q) i := by
  classical

  let A := (starP Q).vertexLink
  let B := linkQ Q

  let k : Fin ((starP Q).n + 1) :=
    ⟨1, by have hn := (starP Q).hn; omega⟩

  have hsign :
      realSignToEdgeSign (linkDiff A B k) ≠ EdgeSign.zero := by
    rw [← starDart_value Q k]
    exact active_at_link_index_one Q hact

  have hdiff : linkDiff A B k ≠ 0 := by
    intro h0
    exact hsign ((realSignToEdgeSign_eq_zero_iff _).2 h0)

  let i : Fin ((starP Q).n - 1) :=
    ⟨0, by have hn := (starP Q).hn; omega⟩

  refine ⟨i, ?_⟩

  have hk :
      k =
        (⟨i.val + 1, by
          have hi := i.isLt
          have hn := (starP Q).hn
          omega⟩ : Fin ((starP Q).n + 1)) := by
    apply Fin.ext
    simp [k, i]

  have hJD : jointDiff A B i ≠ 0 := by
    have h := hdiff
    rw [hk, linkDiff_interior A B i] at h
    exact h

  unfold jointDiff at hJD
  intro heq
  apply hJD
  rw [heq]
  ring
```

The repo’s `linkDiff_interior` is exactly the bridge used here: full link index `i+1` equals the arm joint difference at interior index `i`. fileciteturn106file0L111-L117

## 6. Why this is better than proving a closing-angle theorem

A closing-angle theorem would look like:

```lean
theorem closing_linkDiff_zero_of_no_interior_diff
    (hsides : ∀ i, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) =
              sDist (B 0) (B (Fin.last n)))
    (hint : ∀ i : Fin (n-1), jointAngle A i = jointAngle B i) :
    linkDiff A B 0 = 0 ∧ linkDiff A B (Fin.last n) = 0
```

This is plausible mathematically, but it is a new spherical chain-congruence theorem. It is not present in the repo. The current architecture instead deliberately asks for the interior witness as a field, because the arm lemma operates on the `n-1` exposed joints, not on the two hidden closing angles.

Rooting/rotating the actual stars avoids that whole theorem and is exactly compatible with the existing Ch13 machinery.

## 7. What to change in your assembly

Do this:

```lean
-- before:
starP Q := vertexStarOfEuclidean P Q  -- fixed root
starQ Q := vertexStarOfEuclidean Q Q

-- after:
starP Q := (vertexStarOfEuclidean P Q).rotate (chosenOffset Q)
starQ Q := (vertexStarOfEuclidean Q Q).rotate (chosenOffset Q)
```

or better:

```lean
starP Q := vertexStarOfEuclideanAtDart P (dartRep Q) (dartRep_tail Q)
starQ Q := vertexStarOfEuclideanAtDart Q (dartRep Q) (dartRep_tail Q)
```

where `dartRep Q` is chosen adaptively from `edgeSign`:

```lean
if h : ∃ x, M.σ.SameCycle base x ∧ edgeSign x ≠ EdgeSign.zero
then M.σ^[2] h.choose
else base
```

Then prove:

```lean
active_at_link_index_one
starDart_value
linkOrder
interiorActive
```

relative to that same rooted/rotated star. This keeps all load-bearing geometry honest and avoids relying on a false/simple “closing pinned” assertion.
