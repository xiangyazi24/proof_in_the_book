# Ch13 §8.4 SZ opening induction — Opus reply (ChatGPT-Pro design mechanization)

## Status: PARTIAL — design's restructured skeleton mechanized, residue isolated to ONE primitive.
## Branch main, no commits (as instructed). New file `ProofsInTheBook/SphericalSZInduction.lean` (550 lines).

## Verification

* **RC**: `lake env lean ProofsInTheBook/SphericalSZInduction.lean` → RC=0, 0 errors, 0 warnings.
* **Full build**: `lake build` → **completed successfully, 8646 jobs, 0 errors** (wired into
  `ProofsInTheBook.lean` after `SphericalStuckCollinear`).
* **`#print axioms` (clean-3 = {propext, Classical.choice, Quot.sound}, no sorryAx/native_decide):**
  - `spherical_arm_mono_of_step`   — clean-3 ✓  (the headline conditional kernel arm lemma, weak half)
  - `main_all` / `main_two`        — clean-3 ✓  (the WellFounded-lex assembly + base)
  - `openTail_preserves_sides`     — clean-3 ✓
  - `openTail_preserves_joint_offaxis` — clean-3 ✓
  - `foldedFlat_betweenness`       — clean-3 ✓
  - `diag_le_of_flat_ear`          — clean-3 ✓
* No `sorry` / `axiom` / `admit` / `native_decide` (grep clean; the lone match is the doc line).

## What was BANKED (genuinely complete, unconditional)

1. **The strengthened invariant.** `WeakConvexSphArm` (supports ≥ 0, no strict non-incidence) +
   `strictConvexSphArm_toWeak`; `SameSides`, `JointLe`, `deficitSet`, `deficitCount`;
   `Main n` exactly per design §1; `armMono_of_Main` (final lemma = Main with Strict→Weak A).
2. **The interior tail-opening `openTail` + preservation (design §6, CORRECTED).**
   `openTail_preserves_sides` (every side preserved, split r<k / r=k / k<r via `sDist_rotS2` and
   axis-fixed inner-product), and `openTail_preserves_joint_offaxis` (every *non-straddling* joint
   preserved).
3. **Folded-flat betweenness (design §4 obstacle (a)).** `foldedFlat_betweenness` /
   `foldedFlat_dist_eq` via the substrate's `betweenness_span_nnreal`.
4. **Diagonal inequality (design §4 `diag_le`).** `diag_le_of_flat_ear` via the spherical reverse
   triangle inequality (`sDist_triangle`) + the folded-flat equation.
5. **The complete WellFounded-lex assembly.** `main_two` (base, spherical hinge on the weakly-convex
   triangle), `main_at_level` (inner strong induction on `deficitCount`), `main_all` (outer strong
   induction on `n` — the lex `(n, deficitCount)`), `main_of_lt_two` (vacuous base), and
   `spherical_arm_mono_of_step` : `SZOpeningStep → unconditional kernel arm lemma (weak)`.
   The recursion is genuinely load-bearing — it derives `endpt A ≤ endpt B` by threading the
   dimension-drop IH (`∀ m<n, Main m`) and the deficit-drop IH, not by assuming the goal.

## The single isolated residue: `SZOpeningStep` (non-vacuous, load-bearing, endpoint-only)

Per the directive's fallback ("isolate ONE named non-vacuous Prop + concrete failing chain"). It is
the per-level opening/cut step: at level n, given the two IHs, produce `endpt A ≤ endpt B`. It packages
the design's two reduction rules, **both genuinely exceeding the substrate**:

* **CUT rule (§4).** Needs the **interval-arm convexity-preservation API** (`intervalArm` ear /
  `spliceArm` body as Weak/Strict sub-arms with matched sides/joints) + the convex-position **Gram
  signs** `foldedFlat_betweenness` consumes. The substrate carries those signs as *hypotheses*
  (`SphericalSZ.SZStuckData.signA/signC`), not derived; its only sub-arm constructor is the
  last-vertex-drop `cutArm` (not an arbitrary interval, not endpoint-preserving). No
  `intervalArm`/`spliceArm`-with-preservation exists in the substrate.
* **OPEN rule (§5–§7).** Needs the **interior `openTail` admissible-supremum trichotomy** (REACH
  strict / STUCK weak-with-vanishing-support, + `endpt A ≤ endpt (openTail …)`). The substrate's
  entire reach/stuck/sup apparatus (`SphericalAdmissibleSup.augmented_reachOrStuck_at_sup`,
  `reach_strictConvex_at_sup`, `SphericalArmClose2.reachStrictConvex_dichotomy_at`) is built for the
  **last-joint** `openArm` (axis index n, a *single* rotated tail vertex); the design's interior
  `openTail` rotates the *whole* tail about an interior axis — a different operation whose
  continuity/IVT/supremum trichotomy is absent.

## IMPORTANT FINDING: the design's §6 deficit-decrease is mathematically FALSE for interior `openTail`

The design §6 claims opening joint k disturbs only joint k, giving
`deficitSet A* B = (deficitSet A B).erase k`. This is **incorrect**: rotating the whole tail `r > k`
about the interior axis vertex `A k` disturbs **two** adjacent joints — `r = k-1` (vertices k-1,k,k+1:
k+1 rotated) AND `r = k` (vertices k,k+1,k+2). The joint *below* the axis is collaterally disturbed.
This is mechanized as `openTail_preserves_joint_offaxis`, whose hypothesis is precisely the
**non-straddling** condition `r+2 ≤ k.val ∨ k.val < r.val` — the two excluded straddling joints are
exactly `k-1` and `k`. The substrate's working opening (`openArm`) avoids this by opening the LAST
joint only (single rotated vertex, no downstream joint). So the design's single-`erase` measure does
not hold for the interior operation; the correct two-joint deficit bookkeeping is part of the residue.

(Geometric reason: a rotation fixing one vertex of a triangle and moving the other two deforms the
triangle, hence changes the angle at the moved-apex vertex adjacent to the fixed side.)

## Honest scoping verdict

The headline "fully unconditional spherical_arm_mono/_strict" is **not reachable from this design as
written**: it rests on (a) interior-opening analysis absent from the substrate (a multi-thousand-line
re-derivation of the supremum trichotomy for a new operation), and (b) the design §6 single-joint
deficit claim which is false. What IS delivered: the WeakConvex-invariant **restructuring is faithfully
mechanized**, the genuinely-provable new content (openTail preservation, folded-flat betweenness,
diagonal inequality, the complete lex WellFounded assembly) is banked clean-3, and the whole arm lemma
is reduced to the single non-vacuous `SZOpeningStep` with the two concrete failing chains above. This
strictly advances the prior residues (`MatchedCutStep`/`DeficientReachCollinear`/`SZStepGeom`) by
adopting the strengthened invariant and banking the interval/opening API the design specified, but
does not close them.

Files touched: `ProofsInTheBook/SphericalSZInduction.lean` (new), `ProofsInTheBook.lean` (+1 import).
