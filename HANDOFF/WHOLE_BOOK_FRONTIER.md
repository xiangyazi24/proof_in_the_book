# Whole-book formalization frontier (2026-06-07) — 37/40, three chapters at genuine cores

All three open chapters are reduced to minimal, honest, machine-verified cores. ~7 false tracks
were machine-refuted this session (interior-openTail +δ sign bug; first-corner StuckWitnessExists;
EarHalfPlaneContainment; per-face hcompat; first-edge-binds support ordering; terminal-first;
arm-reversal mirror). Each core is a genuine Jordan-curve / convex-position theorem that needs
DESIGN INPUT (the ChatGPT bridge is broken — returns "Instant"-mode question echoes) or the
primary-source paper. The substrate has everything else proven (clean-3).

## Ch13 — Cauchy rigidity / spherical Schoenberg–Zaremba arm lemma
**Residue: `SphericalCutTransport.FoldedFlatCutTransport`** (the design-§4 folded-flat body/splice
transport at a general INTERIOR cut). TRIPLY confirmed unavoidable:
- The substrate's last-joint `openArm` (endpoint-increasing) gets stuck at the AXIS-INCIDENT
  interior cut (k=n-1: `det3(A⟨n-1⟩)(A⟨n⟩)(qstar)=0`), NOT the first corner (numerics n=2..5;
  first-corner support stays >0, so first-corner `StuckWitnessExists`/`StuckCollinearData` is FALSE).
- Arm-reversal can't map it to the proven first-corner transport (`StrictConvexSphArm` is
  orientation-sensitive: reversal negates det3).
- The interior folded vertex is the axis (an interior joint) with no matched contiguous sub-arm pair,
  so the splice's B-diagonal mismatches the folded A-diagonal — exactly FoldedFlatCutTransport's
  reverse-triangle content. The shorten-then-equal intermediate route fails (d²=a²+b²−2ab cosθ
  non-monotone). The book's first-corner proof does NOT cover this general-k case.
**What's PROVEN**: `stuckAtK_diag_le` (unconditional), `stuckAtK_endpt_le`/`lastCorner_endpt_pair`
(weak bound modulo FoldedFlatCutTransport), REACH `ReachStepDatum`, the recursion. Wiring fix in
progress to make `spherical_arm_mono` conditional on FoldedFlatCutTransport ALONE (the first-corner
STUCK disjunct in SphericalDefReachCollinear is unsatisfiable → being replaced by interior StuckAtKData).
**DESIGN NEEDED**: the general-k folded-flat body/splice transport — given a convex arm A with its
ear folded flat at interior cut (i,j) (so A's body has the diagonal A_i→A_j as a side, length =
sum of folded ear sides, with the body joints at i,j equal to A's originals) and the diagonal
inequality sDist(A_i,A_j) ≤ sDist(B_i,B_j), prove endpt A ≤ endpt B. Body-in-isolation comparison
is FALSE (numerics); whole-arm is TRUE. ChatGPT question 7d00b70b (queued, bridge-blocked).
Primary source: Aigner–Ziegler Cauchy-rigidity ch (BOOK_CH13_CAUCHY.txt) + Schoenberg–Zaremba [5].

## Ch35 — Thomassen Five Color (combinatorial maps)
**Residue: `ChordSeparation.ChordJordanInput`** = {faceCore (numCycles φ'₂ = F+2, kernel-anchored)
+ `gateCompat`}. `gateCompat` (the genuine discrete-Jordan content): supply, for each cycle edge,
the per-gate `SameFragment`/single-φ'₂-edge no-teleport datum from a bare dual path. The false
per-face hcompat is machine-refuted; `chi_le` and `SidesReach2` are eliminated.
**DESIGN NEEDED**: the discrete Jordan separation — why a bare dual path between the two sides of a
chord, through a face straddling the chord, can be replaced by one carrying per-gate single-φ'₂-edge
contiguity (rotation-system contiguity at the chord endpoints). ChatGPT question 64b92d49 (echoed).

## Ch36 — Chvátal art gallery (Fisk)
**Residue: `PolygonCutGeometry.PolygonGeometryInput` + peel oracle `M` (`DiagonalAttachInput`)**.
`IsConvexVertex'` is now PROVED end-to-end (extreme-vertex-is-convex seed at every 3-gon vertex,
n=3 base eliminated). `EarHalfPlaneContainment` machine-refuted false for non-convex pieces;
`OffDiagDisjoint`/`SubRegionContainment` discharged via the diagonal SEGMENT; `RegionSplitGenericity`
proved general-n. The chain `earDeletedExterior ⟸ OffDiagDisjoint ⟸ CutGeometry ⟸ PolygonGeometryInput`.
**DESIGN NEEDED**: (a) `PolygonGeometryInput` — the planar-Jordan bundle that builds a per-polygon
CutGeometry (segment-intersection region split for a simple-polygon diagonal, true for non-convex);
(b) `M` — the ear-deletion induction driver (two-ears / Meisters), deemed not leaf-level dischargeable.
ChatGPT questions 7550b8af/0b9ec59e (echoed).

## To unblock (Xiang)
1. Restore the ChatGPT bridge to Thinking mode (it returns prompt echoes ending in "Instant"), OR
   relay the deep-think answers for 7d00b70b (Ch13 §4 body transport), 64b92d49 (Ch35 discrete
   Jordan), 7550b8af (Ch36 region-split) from the browser.
2. Or provide the Schoenberg–Zaremba paper [5] (its §4 body-transport detail for general-k).
3. Reconcile uisai1's diverged proof_in_the_book mirror for whole-book builds (Spherical* chain is
   byte-identical/sound; Chapter wrapper files have uncommitted deletions on a diverged lineage).

---

## DEFINITIVE STATUS (2026-06-07, after exhaustive M-lesson re-examination of ALL cores)

The whole book is at 37/40. Each open chapter is reduced to ONE genuine, minimal, INHABITED/non-vacuous
core. The M lesson (combinatorial "design-blocked" verdicts can be premature) was applied to every core:

**Autonomously DISCHARGED / IMPROVED this session (combinatorial structure was recoverable):**
- Ch36 `M` (peel-order re-rooting): FULLY DISCHARGED — `PolygonReroot.lastToFirstAll_holds` (the dual-tree
  adjacency was in `.glue.hShared`). [wiring TODO: import PolygonReroot into PolygonMClose consumer + Audit.lean]
- Ch35 `gateCompat`: was UNINHABITABLE (`gateFragmentCompatible_uninhabited`); replaced by the INHABITED
  `gateCompat'` (cap-channel `EndpointCapLink` + `InteriorTriangleGates`), with the cap-channel route to
  `SphereChordSeparation` proved (`ChordSeparationClose.sphereChordSeparation_of_input'`). All interior
  gates + `SidesReach2` + `ReachesBank2` + faceCore + Euler discharged. [wiring TODO: replace `gateCompat`
  by `gateCompat'` in `ChordSeparation.ChordJordanInput`]
- Ch13 REACH: `hmix`/`hhem` solved via `by_cases stuck` (`SphericalReachConstruction`); blocker is the
  mechanical +δ→−δ sign fix to `SphericalMonitoredSup` + corrected `ReachStepDatum` banked.
- Ch36 `OffDiagDisjoint` + `RegionSplitGenericity` discharged unconditionally.

**Genuinely DESIGN-BLOCKED (geometric/Jordan content; re-pursuit confirmed, NOT recoverable from the substrate):**
- Ch13 `FoldedFlatCutTransport` — §4 spherical body transport (single ≤-diagonal + straight π splice-head joint).
  Machine-refuted: body-JointLe (splice-head straight), single-side monotonicity (~35% decrease), reversal
  (orientation), first-corner (numerics). TRUE numerically (100%). = ChatGPT 7d00b70b (in browser).
- Ch35 `gateCompat'` cross-bank crossing — discrete Jordan; circular with the Euler count at the comb-map layer.
  = ChatGPT 64b92d49 design.
- Ch36 `InteriorOddSeed` — planar Jordan (adjacent-triangle interior point inside polygon). windCross is a
  crossing-PARITY sum (not an angle-winding integral) → can't synthesize a nonzero interior winding; the
  winding route routes through the machine-refuted `EarHalfPlaneContainment`. = ChatGPT 7550b8af design.

**THE UNBLOCK (only Xiang can do):**
1. Relay the 3 browser ChatGPT designs (bridge returns "Instant" echoes / BRIDGE_ERROR — can't capture):
   `7d00b70b` (Ch13 §4 body transport), `64b92d49` (Ch35 discrete Jordan), `7550b8af` (Ch36 planar Jordan).
2. Reconcile uisai1's diverged `proof_in_the_book` mirror (diverged lineage cb5be71, dirty tree) so the
   integrated build + the wiring TODOs above + `#print axioms` via Audit.lean can run clean.
The Jordan curve theorem is famously hard to formalize; absent the relayed designs these 3 cores are
multi-week dedicated efforts each. Everything else (37 chapters + all the surrounding machinery of 13/35/36)
is proven clean-3.

---

## Ch36 deep-dive conclusion (2026-06-07, after 9 routes on earDeletedExterior)

Nine distinct routes drove Ch36's `earDeletedExterior` residue from the global planar Jordan theorem
down to the tiny-local `EarLeg1Free` (the extreme vertex's ear is empty / has no P-edge endpoint
inside). Major unconditional gains banked: the signed-angle winding foundation (`oWind`, algebraic
diagonal-cancellation), the P'-edge classification (`rightEdge_eq_or_diagonal`), the entire Leg-2
below-extreme-v tail + escape determinant, `¬OnBoundary P' x`, the two-leg transport, and the
region-free bridge `windCross=0 -> ¬ClosedRegion'`. `InteriorOddSeed` proven FALSE and discarded.

BUT closing `earDeletedExterior` does NOT close Ch36: `rest` (RemainingResidualData = the
disjoint/boundary/intersection region-split identities) and `M` (DiagonalAttachInput) remain
independent inputs, and `rest` is the SAME planar-Jordan content. So Ch36's residues all reduce to
ONE core theorem: **a simple-polygon diagonal splits the interior into two disjoint regions** =
**simple polygon winding ∈ {0,±1}** = the planar Jordan curve theorem (degree of a simple closed
curve). The winding foundation is the right scaffolding; the core bound (winding ∈ {0,±1}) is the
hard kernel (needs degree theory / a non-circular induction — every attempted split-induction is
circular because the disjointness IS the theorem). Mathlib has no winding-number/Jordan API.

**Efficient path: ONE core region-split/winding-bound theorem closes earDeletedExterior + rest
together** (vs grinding each residue). That is either ChatGPT 7550b8af (browser) or a from-scratch
planar-Jordan campaign (major; scope decision for Xiang). Same holistic situation for Ch35 (discrete
Jordan / cross-bank) and Ch13 (§4 spherical body transport).
