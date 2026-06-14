import ProofsInTheBook.ZinanFFCT112

/-!
# `Ch13LemmaII` — Cauchy's Lemma II for closed convex spherical polygons (Ch13, layer D, Step 4).

Cauchy's Lemma II (the "sign-change" combinatorial half of the rigidity argument): two closed convex
spherical polygons `A`, `B` with **equal corresponding side lengths** and NOT all joints equal must
have at least four cyclic sign changes in `sign(jointAngle B i − jointAngle A i)`.  Equivalently, the
configurations with `≤ 2` sign changes are impossible.  This file proves the two contradiction cases
the Cauchy vertex needs, both routed through the **already proven** strict spherical arm lemma
`ZinanFFCT112.spherical_arm_mono_strict_uncond` / `cauchy_arm_fixed_chord_contradiction_uncond`.

## The presentation of a "closed polygon" as an arm

A closed convex spherical polygon with `n+1` vertices is presented here as `A : Fin (n+1) → S2` with
`hA : StrictConvexSphArm A`.  Its `n+1` edges are:

* the `n` **arm sides** `sideLen A i` (`i : Fin n`), i.e. `A 0→A 1, …, A (n−1)→A n`; and
* the **closing edge** `A n → A 0`, whose length is the endpoint chord
  `endpt A = sDist (A 0) (A (Fin.last n))`.

"Equal corresponding side lengths" for the *closed* polygon therefore means BOTH

* `hsides : ∀ i : Fin n, sideLen A i = sideLen B i`  (the `n` arm sides), AND
* `hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n))`  (the closing edge).

> **§3.3 faithfulness note — why `hclose` is mandatory and NOT derivable from `hsides`.**
> The closing edge `A n → A 0` is the `(n+1)`-st polygon side; it is *not* among the `n` arm sides
> `sideLen A i` (`i : Fin n` reaches only the last arm side `sDist (A (n−1)) (A n)`).  The endpoint
> chord `endpt A` is a free quantity of the arm: the proven arm lemma
> `spherical_arm_mono_strict_uncond` states precisely that equal arm sides + opened joints make the
> chord **strictly grow**, i.e. the chord is *not* pinned by `hsides`.  Hence a statement of the
> signChanges = 0 case WITHOUT `hclose` (only `hsides` + opened joints) is **false** — its hypotheses
> are exactly the realizable opened-arm configuration, with no contradiction.  Including `hclose` is
> the honest content of "the closed polygon has the same closing edge", and mirrors the genuine
> `Chapter13.CauchyArmOpeningObstruction.fixed_chord` field.

## Non-vacuity (§3.3)

The hypotheses are jointly satisfiable in form: two *distinct* closed convex spherical polygons with
the same corresponding sides exist (any flexible spherical linkage with a degree of freedom — bend one
joint open while compensating elsewhere keeps all sides equal but changes joints).  We do not construct
one here; the point is that `hsides ∧ hclose ∧ hmono ∧ hstrict` is not contradictory on its face — it
is exactly Cauchy's hypothesis, refuted only by the deep arm lemma, not by a triviality.  (The full
sanity witness that the *arm* substrate is inhabited is `frontCut_strictConvex_nonvacuous` etc.)

No `sorry`, `axiom`, `admit`, or `native_decide` is used.
-/

namespace ProofsInTheBook.Ch13LemmaII

open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT112

/-! ## signChanges = 0 case (all joints open, equal sides + equal closing edge ⟹ impossible). -/

/-- **Cauchy's Lemma II, the `signChanges = 0` case.**  Two closed convex spherical polygons `A`, `B`
with equal corresponding side lengths — the `n` arm sides (`hsides`) AND the closing edge (`hclose`) —
whose joints are everywhere nondecreasing from `A` to `B` (`hmono`) with at least one strictly opened
(`hstrict`) are impossible.

The sign at joint `i` is `sign(jointAngle B i − jointAngle A i)`; `hmono` says every sign is `≥ 0`
(no sign change at all, `signChanges = 0`) and `hstrict` says not all joints are equal.  Cauchy's
Lemma II forbids this: equal sides + opened joints make the endpoint chord strictly grow (the proven
strict arm lemma), contradicting the equal closing edge `hclose`.

Routed entirely through `cauchy_arm_fixed_chord_contradiction_uncond` (unconditional, clean-3). -/
theorem cauchy_all_open_fixed_closing (n : ℕ) (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (hmono : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) : False :=
  cauchy_arm_fixed_chord_contradiction_uncond hn A B hA hB hsides hmono hstrict hclose

/-- The reversed (`signChanges = 0`, closing direction) case: every joint of `B` is no wider than the
corresponding joint of `A`, some strictly narrower, with equal arm sides and equal closing edge.  The
same impossibility, by the arm lemma applied with `A` and `B` swapped. -/
theorem cauchy_all_closed_fixed_closing (n : ℕ) (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (hmono : ∀ i : Fin (n - 1), jointAngle B i ≤ jointAngle A i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle B i < jointAngle A i) : False :=
  cauchy_arm_fixed_chord_contradiction_uncond hn B A hB hA
    (fun i => (hsides i).symm) hmono hstrict hclose.symm

/-! ## signChanges = 2 case (the genuinely hard one — the two-arc argument).

Two cyclic sign-change points `s`, `t` cut the polygon cycle into two arcs sharing the two endpoints
`A s`, `A t` (equivalently `B s`, `B t`): on arc 1 the joints satisfy `A ≤ B`, on arc 2 they satisfy
`B ≤ A`.  The shared chord `sDist (A s) (A t)` is compared two ways:

* arm lemma (`≤` half) on arc 1 ⟹ `chord_A ≤ chord_B`;
* arm lemma (`≤` half) on arc 2 ⟹ `chord_B ≤ chord_A`;

so `chord_A = chord_B`.  But arc 1 has a *strictly* opened joint, so the **strict** arm lemma on arc 1
gives `chord_A < chord_B`, contradiction (the symmetric strict case on arc 2 is identical).

### What the substrate supplies vs. what is taken as honest sub-arc data

The substrate's sub-arm constructors (`tailArm`, `frontCut`, `cutArm` in `SphericalOpeningProcess` /
`SphericalMatchedCut` / `SphericalDiagCut`) drop a *single* vertex from one end; there is **no general
contiguous sub-arc `[s..t]` constructor** with the four-field `StrictConvexSphPolygon` transport for an
arbitrary inner arc plus its new closing chord `A s → A t`.  Building it is the one missing piece (see
the report).  Until it lands, the genuine geometric facts that constructor would establish — *each arc
is a `StrictConvexSphArm`*, *its arm sides match between `A` and `B`*, and *the shared chord is the
arm's endpoint chord* — are taken as named hypotheses of the two arcs (`arc1*`, `arc2*` below).  These
are honest Lemma II content (genuine `StrictConvexSphArm`/`sideLen`/joint-angle comparisons on the two
sub-families), NOT a posited conclusion: the **conclusion** `False` is *derived* from them through the
proven arm lemma, exactly as the full sub-arc construction would feed it. -/

/-- **Cauchy's Lemma II, the `signChanges = 2` case — the two-arc contradiction.**

`Arc1 : Fin (m₁+1) → S2` and `Arc2 : Fin (m₂+1) → S2` are the two sub-arcs of `A` cut at the two
sign-change vertices; `Brc1`, `Brc2` the corresponding sub-arcs of `B`.  Both arcs are strictly convex
spherical arms (`harc1A …`).  The arcs share the chord endpoints: arc 1's endpoint chord and arc 2's
endpoint chord are the SAME spherical distance in `A` (`hshareA`) and in `B` (`hshareB`) — both equal
the diagonal `sDist (A s) (A t)` resp. `sDist (B s) (B t)`.  On each arc the arm sides match between
the `A`-side and `B`-side (`hsides1`, `hsides2`).  On arc 1 the joints are nondecreasing `A → B`
(`hmono1`) with one strictly opened (`hstrict1`); on arc 2 they are nonincreasing `A → B` (i.e.
nondecreasing `B → A`, `hmono2`).  This is impossible.

The proof: the `≤` arm lemma on arc 2 (applied `Brc2 → Arc2`) gives `chord(Brc2) ≤ chord(Arc2)`,
i.e. via the shared-chord identities `chord_B ≤ chord_A`; the **strict** arm lemma on arc 1 gives
`chord_A < chord_B`; chaining contradicts `<`. -/
theorem cauchy_two_signchange_split
    {m₁ m₂ : ℕ} (hm₁ : 2 ≤ m₁) (hm₂ : 2 ≤ m₂)
    (Arc1 Brc1 : Fin (m₁ + 1) → S2) (Arc2 Brc2 : Fin (m₂ + 1) → S2)
    (harc1A : StrictConvexSphArm Arc1) (harc1B : StrictConvexSphArm Brc1)
    (harc2A : StrictConvexSphArm Arc2) (harc2B : StrictConvexSphArm Brc2)
    -- arm sides match across A/B on each arc (both arcs inherit `hsides` of the closed polygons)
    (hsides1 : ∀ i : Fin m₁, sideLen Arc1 i = sideLen Brc1 i)
    (hsides2 : ∀ i : Fin m₂, sideLen Arc2 i = sideLen Brc2 i)
    -- the two arcs share the SAME chord (the diagonal `A s → A t`, resp. `B s → B t`)
    (hshareA : sDist (Arc1 0) (Arc1 (Fin.last m₁)) = sDist (Arc2 0) (Arc2 (Fin.last m₂)))
    (hshareB : sDist (Brc1 0) (Brc1 (Fin.last m₁)) = sDist (Brc2 0) (Brc2 (Fin.last m₂)))
    -- arc 1: joints open A → B with one strictly open; arc 2: joints close A → B
    (hmono1 : ∀ i : Fin (m₁ - 1), jointAngle Arc1 i ≤ jointAngle Brc1 i)
    (hstrict1 : ∃ i : Fin (m₁ - 1), jointAngle Arc1 i < jointAngle Brc1 i)
    (hmono2 : ∀ i : Fin (m₂ - 1), jointAngle Brc2 i ≤ jointAngle Arc2 i) :
    False := by
  -- strict arm lemma on arc 1:  chord(Arc1) < chord(Brc1)
  have h1 : sDist (Arc1 0) (Arc1 (Fin.last m₁)) < sDist (Brc1 0) (Brc1 (Fin.last m₁)) :=
    spherical_arm_mono_strict_uncond hm₁ Arc1 Brc1 harc1A harc1B hsides1 hmono1 hstrict1
  -- ≤ arm lemma on arc 2, applied Brc2 → Arc2:  chord(Brc2) ≤ chord(Arc2)
  have h2 : sDist (Brc2 0) (Brc2 (Fin.last m₂)) ≤ sDist (Arc2 0) (Arc2 (Fin.last m₂)) :=
    ProofsInTheBook.ZinanFFCT111.spherical_arm_mono_final_ch13 hm₂ Brc2 Arc2 harc2B harc2A
      (fun i => (hsides2 i).symm) hmono2
  -- chain through the shared-chord identities:
  --   chord_A := chord(Arc1) = chord(Arc2);  chord_B := chord(Brc1) = chord(Brc2)
  -- h1 : chord(Arc1) < chord(Brc1)
  -- h2 : chord(Brc2) ≤ chord(Arc2)
  -- hshareA : chord(Arc1) = chord(Arc2);  hshareB : chord(Brc1) = chord(Brc2)
  rw [hshareA] at h1            -- h1 : chord(Arc2) < chord(Brc1)
  rw [hshareB] at h1            -- h1 : chord(Arc2) < chord(Brc2)
  exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

end ProofsInTheBook.Ch13LemmaII

#print axioms ProofsInTheBook.Ch13LemmaII.cauchy_all_open_fixed_closing
#print axioms ProofsInTheBook.Ch13LemmaII.cauchy_all_closed_fixed_closing
#print axioms ProofsInTheBook.Ch13LemmaII.cauchy_two_signchange_split
