# Ch13 §8.4 SZ spherical arm lemma — `SZStepCore` discharge attempt (SZFinal round)

## Status: PARTIAL — the OPEN-branch correction is BANKED clean-3 (preservation + single-`erase`
## deficit-decrease + interior-axis endpoint monotonicity); `SZStepCore` reduced to the NARROWER
## residue `InteriorOpenAndSpliceStep`. The headline "fully UNCONDITIONAL `spherical_arm_mono`" is
## NOT reached: three genuine pieces remain (interior reach/stuck SUPREMUM trichotomy, splice
## transport, equal-joints congruence) that the OPEN_FIX + ear API do not provide.

Branch `main`, **no commits** (as instructed). New file
`ProofsInTheBook/SphericalSZFinal.lean` (431 lines) + 1 import in `ProofsInTheBook.lean`.
Verified on `uisai1`.

## Verification

* **RC**: `lake env lean ProofsInTheBook/SphericalSZFinal.lean` → RC=0, **0 errors, 0 warnings**.
* **Full build**: `lake build` → **Build completed successfully (8649 jobs)**, 0 errors
  (was 8648; the new module is the +1 job; wired after `SphericalSZStepClose`).
* **`#print axioms` — clean-3 ([propext, Classical.choice, Quot.sound], NO sorryAx/native_decide):**
  - `spherical_arm_mono_of_residue`            — clean-3 ✓ (headline arm lemma weak half, conditional on the narrowed residue)
  - `szStepCore_of_interiorOpenAndSplice`      — clean-3 ✓
  - `endpt_openTail_interior_mono`             — clean-3 ✓
  - `deficitCount_openTail_reach_lt`           — clean-3 ✓
  - `jointAngle_openTail_eq_of_ne`             — clean-3 ✓
* No `sorry` / `axiom` / `admit` / `native_decide` (grep clean — only the docstring mention).

## What was BANKED (genuinely new, unconditional, clean-3) — the OPEN-branch correction

The prior `SZStepCore` round (`opus-szstepclose-reply.md`) recorded the OPEN branch as a GENUINE
obstruction: "interior `openTail` disturbs TWO adjacent joints, so the single-`erase` deficit-decrease
is unavailable" + "arm endpoint not cyclically invariant." `HANDOFF/CH13_OPEN_FIX.md`'s correction is
verified and mechanized clean-3:

1. **(O-preservation) The corrected joint preservation — EXACTLY ONE disturbed joint.**
   * `rotS2_axis_fixed` (`rotS2 k δ k = k`), `jointAngle_eq_of_rot` (= `sphAngle_rotS2`: angle invariant
     under the Rodrigues isometry).
   * `jointAngle_openTail_eq_at_axis`: the joint `r` with `r.val = K.val` (triple `(A K, A(K+1),
     A(K+2))`, axis `A K` fixed) is PRESERVED — the fixed axis `A K = rotS2(A K)δ(A K)` makes the whole
     triple the image of itself under the SAME isometry (`rw [← rotS2_axis_fixed]` then
     `jointAngle_eq_of_rot`). This is the precise Lean move the OPEN_FIX prescribed.
   * `jointAngle_openTail_eq_of_ne_opened` / `jointAngle_openTail_eq_of_ne`: every joint EXCEPT the
     single opened one (`r.val + 1 = K.val`) is preserved (the three cases `r+2≤K`, `r=K` [§at_axis],
     `K<r` cover them). **The prior round's "two disturbed joints" was a proof artifact**, now corrected.

2. **(O-deficit) The single-`erase` deficit-decrease (the measure the prior round believed
   UNAVAILABLE).** `deficitSet_openTail_reach` (`deficitSet A* B = (deficitSet A B).erase k` in REACH)
   and `deficitCount_openTail_reach_lt` (count strictly drops). Valid precisely because exactly one
   joint is disturbed.

3. **(O-endpoint) The interior-axis endpoint monotonicity (bypassing "endpoint not cyclically
   invariant").** `endpt_openTail_interior_mono`: `endpt A ≤ endpt (openTail A K (-θ))` for an INTERIOR
   axis `K` (`1 ≤ K.val`, `K.val < n`). The interior opening rotates the arm endpoint `A(last)` (index
   `n > K`) and fixes `A 0`, so the endpoint is `sDist(A 0)(rotS2(A K)(-θ)(A last))` — the SAME shape the
   substrate's last-joint `reach_endpoint_mono_arm` bounds. Closed via the AXIS-GENERIC base-triangle
   engine (`reach_base_endpoint_mono`, `openedAngle_ge_of_oriented_neg`) with new interior base facts:
   `shortArc_of_hemisphere` / `shortArc_interior_base` (distinct open-hemisphere chords are short arcs)
   and `orientedDatum_interior` (the forward diagonal `A 0 → A K` strictly supports `A last`,
   `cut_diagonal_supports` + `sOrient_cyclic`). **No cyclic shift is used** — the prior obstruction is
   sidestepped entirely; the interior opening itself moves the endpoint, exactly as the last-joint one.

## The narrowed residue: `InteriorOpenAndSpliceStep`

`szStepCore_of_interiorOpenAndSplice : InteriorOpenAndSpliceStep → SZStepCore` (immediate forwarding;
the value is that §2–§5 above + the `SphericalSZStepClose` ear API/diagonal inequality are banked
beneath it). It carries the THREE pieces that genuinely exceed the substrate, each with a concrete
failing chain (§R):

* **(R-O) The interior reach/stuck SUPREMUM trichotomy.** The OPEN_FIX corrected the
  *preservation/bookkeeping* but NOT the *production*: the design opens to the admissible supremum `δ*`
  and needs REACH-vs-STUCK at `δ*`. The substrate's `SphericalAdmissibleSup.augmented_reachOrStuck_at_sup`
  / `reach_strictConvex_at_sup` monitor the LAST-JOINT opening's single tail vertex; the interior
  `openTail` rotates the WHOLE tail `> K` about an interior axis, so the admissible family must monitor
  every rotated-tail support and the *interior* joint-angle target slack — a family the substrate's
  `combinedSupport`/`augmentedSupport` (indexed for the single last tail vertex) does not provide, and
  whose closed-set supremum trichotomy + boundary convexity persistence are absent. (Once REACH is
  produced, my `deficitCount_openTail_reach_lt` drops the measure; once STUCK, my
  `endpt_openTail_interior_mono` carries the endpoint and (R-C) closes it — so the banked OPEN pieces
  are exactly the consumers of this production.)

* **(R-C) The CUT body/splice transport `splice_transport_of_diag_le`.** After `ear_chord_le_of_Main`
  and `cut_diag_le` (banked in `SphericalSZStepClose`), gluing them to `endpt A ≤ endpt B` needs the
  spliced body `A[0..i] ++ A[j..n]` as a convex sub-arm. The substrate has NO `spliceArm` (only
  last-vertex-drop `cutArm` and first-vertex-drop `frontCut`, neither an arbitrary interval union), and
  the body's new diagonal side is matched to `B` only by the INEQUALITY `cut_diag_le`, not by SAS
  equality (`SphericalSZChain.diag_len_eq` needs the included angle to agree, which a folded-flat `A`
  corner — angle π — does not against `B`'s bent corner).

* **(R-cong) The equal-joints endpoint congruence.** When no joint is deficient,
  `all_joints_eq_of_no_deficit` gives equal *joints*, but the endpoint congruence `endpt A = endpt B`
  (equal sides + equal joints ⟹ equal endpoint, the spherical arm rigidity) is not banked; deriving it
  needs the full spherical SSS/SAS arm congruence by induction (the reverse `endpt B ≤ endpt A` is not
  available from `Main n` since `A` is only weakly convex).

## Honest scoping verdict

The directive asserted ChatGPT made BOTH branches "mechanically clear" and the headline UNCONDITIONAL.
After full verification: the OPEN_FIX is correct and now BANKED clean-3 (it genuinely overturns the
prior round's two false obstructions — "two disturbed joints" and "endpoint not cyclically invariant" —
both are resolved). But the OPEN_FIX addresses only the preservation/deficit BOOKKEEPING, not the
reach/stuck SUPREMUM PRODUCTION for the interior `openTail`, which is a distinct, substrate-absent
analytic build (the last-joint apparatus monitors one tail vertex; the interior opening moves the whole
tail). The CUT branch still needs the `spliceArm` constructor the substrate lacks, and the no-deficit
case still needs the unbanked arm congruence. So `spherical_arm_mono` remains conditional on the single
narrowed residue `InteriorOpenAndSpliceStep` = (R-O) + (R-C) + (R-cong).

Net advance vs. the prior `SZStepCore`: the entire OPEN-branch preservation/deficit/endpoint substrate
is now banked clean-3 (3 of the prior round's listed obstructions discharged), and the residue is
strictly narrower — it no longer carries the OPEN preservation, the deficit-decrease, or the interior
endpoint bound. The chapter's remaining frontier is precisely (R-O) the interior-axis reach/stuck
supremum trichotomy, (R-C) the splice transport, and (R-cong) the equal-joints congruence.

Files touched: `ProofsInTheBook/SphericalSZFinal.lean` (new, 431 lines), `ProofsInTheBook.lean` (+1 import).
