# Whole-book faithfulness audit — Proofs from THE BOOK (40 chapters)

Date: 2026-06-04. Method: per-chapter headline theorem `chapterNN`, statement-faithfulness + `#print axioms`.

## MACHINE-BACKED SCOPING (2026-06-06, end of campaign) — 37/40, the three needed developments
The fresh-angle campaign closed by MACHINE-PROVING what each irreducible core needs (no longer "angle not
found" but "existing tools proven insufficient + the exact development scoped"). ~52 files of unconditional
scaffolding banked. The three open chapters need these specific NEW developments (each substantial; not
closable by more structural one-shots, which now re-confirm):

1. **Ch36 → a winding-number / signed-degree development.** `OffDiagDisjoint` (the planar Jordan
   chord-separation = inside-XOR-outside) is PROVEN underivable from the substrate: `intCount_admits_both_inside`
   (the integer count identity cP+2d=cL+cR admits in_L∧in_R∧¬in_P — the diagonal term cancels, count engine
   blind at parity AND ℤ granularity) + `lineSide_blind_to_chord_endpoints` (affine det2-sign's zero set is the
   whole infinite line; a non-convex ear straddles it). NEEDED: a position-aware winding/degree argument tracking
   the probe ray's SIGNED intersection with the chord SEGMENT (or a Jordan-curve-theorem instance for the ear
   domain). Everything else in Ch36 is unconditional (parity core, general-n ray-independence, IsConvexVertex'
   via ear-deletion, the ⌊n/3⌋ headline modulo this one residue).
2. **Ch13 → boundary-strict-persistence + B-companion cut.** The terminating reach recursion DRIVER is built
   (defStep_endpt). `DeficientReachStep` needs: (a) a strict-convex persistence lemma UP TO the admissible
   supremum δ* (current reach_strictConvex_at_sup takes strictness as a hypothesis; the trichotomy gives only a
   boundary disjunction), and (b) the matched B-companion two-piece cut at an arbitrary stuck support (current
   stuckSupport_gives_cut gives one A-arm, no B-companion / endpoint-preservation / frontCut-alignment). Both are
   constructive/analytic, not classical-theorem-hard. Everything else is unconditional (PlanarConvexDiagPos,
   cyclicTriplePos, both keystones, the cut machinery, cone membership, congruent branch, the recursion driver).
3. **Ch35 → the discrete-planar chord-cap classification.** `SideTracePhiTwoCycle` (the post-splice tracePhi
   2-cycle = the correct chord-cap placement) needs the chord caps connected to the vertex rotation / the
   recursion's generic side map — the same vertex-rotation σ-contiguity / face-correspondence the CombMap layer
   defers (CutFaceLabel kernel-refuted the uniform-orbit-label route). Everything else is unconditional (genus
   core, connectivity, ι_surj, face-size, tOrbitCard, the 2-cycle algebra).

Next lever: a decision to invest in these three developments (or design rounds), notably the winding-number
machinery for Ch36 (the polygon Jordan curve theorem). Headlines stay clean-3, conditional only on these named
non-vacuous residues. Full build 8642 jobs.

## CONVERGED FRONTIER (2026-06-06, after the fresh-angle campaign) — 37/40
The fresh-angle campaign (per the don't-give-up doctrine) REVERSED every premature "blocked/needs-new-theorem"
verdict and drove all 3 open chapters, banking ~50 files of unconditional scaffolding, to a SINGLE unified
irreducible core each — and crucially, ALL distinct attack angles now CONVERGE to the same core per chapter
(a stronger signal than "angle not yet found"). Each core is the genuine Jordan / convex-geometry content the
crossing-parity / combinatorial-map abstraction deliberately defers. Many wrong framings were machine-caught
(vacuous Props: ChordBigonWrap.keptPhi-wrap, TerminalVisibility; false equalities: MatchedCutCornerStep joint-0;
the §6 closing-support determinant refutation).

- **Ch13 → `DeficientReachOpen`.** UNCONDITIONAL: PlanarConvexDiagPos (GP-syzygy), cyclicTriplePos, both-sign §8.1
  keystone, the full interior matched cut (frontCut, endpoint-preserving), the cut-corner angle inequality
  (sphAngle SSS + HINGE-11.3 additivity), the tangent-cone membership (gnomonic bridge → span ℝ≥0), full §8.3
  persistence + hemisphere augmentation, the any-support cut (stuckSupport_gives_cut), SZInductiveStep (qstar/
  betweenness ELIMINATED), the congruent branch (fully discharged), the reach/stuck dichotomy wiring. RESIDUE =
  the deficient-case matched-cut: (a) REACH-branch boundary STRICT positivity at the admissible sup δ* (the
  trichotomy gives nonneg; hemisphere strictness at the boundary), (b) STUCK-branch matched B-companion two-piece
  cut + the terminating reach recursion. The SZ-opening's terminating recursion.
- **Ch35 → `SideTracePhiTwoCycle`.** UNCONDITIONAL: SidesReach2, chord recursion, V/E/face-count theorems, the
  genus-0 no-handle core (genus-slack), kept-side connectivity, Side₁IsDisk, ι_surj, the face-SIZE=3 theorem,
  the face-orbit surjection, chord-choice contiguity, tOrbitCard=2 arithmetic, the post-splice 2-cycle algebra.
  RESIDUE = the post-splice tracePhi 2-cycle = the correct chord-cap placement (the swap closing the bigon across
  u↔v). Tangle: chord_case_recursive abstracts each side as a generic CombMap+ι (NOT sideMap₁), so the chord-side
  has non-unified framings (sideMap₁/anchors vs ChordSideReconstruction/generic vs cutCap); the residue is the
  discrete-planar chord-cap/face classification, unbuilt at the CombMap layer.
- **Ch36 → `OffDiagDisjoint` / `earDeletedExterior`.** UNCONDITIONAL: the entire ray-crossing-parity core, global
  + general-n ray-independence, hconv (crossTau-sign), SubRegionContainment, the det2-side geometry, the
  convex-vertex index, IsConvexVertex' for general n (ear-deletion induction: ear_delete_strict + the diagonal
  count-additivity + the n=3 base), the ⌊n/3⌋ headline modulo one residue. RESIDUE (UNIFIED — the ear step folds
  into it, no new residue) = OffDiagDisjoint: the two crossing-parity sub-regions are disjoint off the diagonal
  = inside-XOR-outside = the parity↔det2-side link = the planar Jordan curve theorem's disjointness. Parity alone
  admits (in_L,in_R)=(1,1) (parity_admits_both_inside); needs the geometric in_L ⟹ left-of-diagonal.

These three are the genuine irreducible cores: the planar Jordan curve theorem (Ch36), the SZ-opening terminating
recursion + boundary strictness (Ch13), the discrete-planar chord-cap classification (Ch35). All angles converge
here; closure needs substantial new discrete-Jordan / convex-geometry developments (or a design-level decision),
not more structural rounds. The headlines stay clean-3, conditional on these named non-vacuous residues.

## FINAL STABLE FRONTIER (2026-06-06, end of the deep closing campaign) — 37/40
After ~25 closing rounds, each open chapter is reduced to a SINGLE named, non-vacuous, multiply-confirmed
(kernel + source + machine-refutation) residue. ~40 new files of genuine unconditional infrastructure banked;
THREE "irreducible walls" cracked by a key insight (genus-slack monotonicity / Ch35 eulerChar; the
Grassmann–Plücker syzygy / Ch13 convex position; the general-n parity-pairing / Ch36 ray-independence);
every re-wrapper, unsound Prop, and wrong angle caught (incl. a machine-checked §6 refutation of the
"closing-support-vanishes-first" idea). The three residues are now genuine research-frontier data that need
design-level insight (the established unblock = a ChatGPT-Pro design round Xiang relays), NOT more structural
rounds (which now re-confirm rather than close):

- **Ch13 → `TerminalVisibility`** (spherical convex geometry). The §8.4 SZ-opening's stuck branch needs the
  closing triple (A 0, A 1, qstar); the augmented trichotomy yields only SOME vanishing support, and
  `closing_not_first` (machine-checked, design §6 config) PROVES the closing support is NOT the first to
  vanish — so the identification needs the design's §7 `terminal_visibility` theorem, which "ordinary strict
  spherical convexity gives no implication of." ALL scaffolding built (both-sign keystone, full §8.3
  persistence, hemisphere-augmented admissible-sup, cyclicTriplePos, DiagonalCutArm, two-sided cut, relabel,
  reach measure). Needs the terminal-visibility theorem itself (new math / design round).
- **Ch35 → `BoundaryOrbitClass` (chord) / `CleanFaceClass` (chordless)** = WHICH φ'-orbit is the boundary face
  (the face↔M-face correspondence). genus core (genus-slack), connectivity, vertex ι_surj, sphere field,
  chord-choice contiguity, the face-SIZE=3 theorem, and the face-orbit SURJECTION (sideFace_has_inl_rep, the
  face analogue of ι_surj) ALL proved. The lone residue is identifying the boundary orbit — CutFaceLabel
  kernel-refutes it as a genus-uniform orbit label; needs a genus-0-essential boundary-orbit certificate (the
  genus-slack-style route for orbit IDENTITY, not yet found) or the discrete-Jordan classification.
- **Ch36 → `PolygonGeomResidue` + `LastToFirstAll`**. PolygonGeomResidue = the per-edge `crossTau`-sign /
  single-edge-jump Jordan content for n≥4 (a point interior to P has odd crossing — the convex vertex's ear
  triangle is inside P): ray-independence transports parity between rays but seeds no interior odd-crossing;
  crossingNumber'_interior_eq_one gives 1 only at n=3. LastToFirstAll = the dual-tree re-root of the canonical
  glue (M's peel-order). The entire parity core, ray-independence (all n), region-split set-identities, det2
  geometry, convex-vertex index, triangle leaf are PROVED.

## CONSOLIDATED FRONTIER (2026-06-06, after the deep multi-round closing campaign) — 37/40
Three open chapters; each driven layer-by-layer to its precise final core, banking ~30 new files of
genuine unconditional infrastructure (all 0-sorry, clean-3, pushed). Multiple re-wrappers caught and NOT
banked; several unsound Props caught and corrected. The residues now require UPSTREAM single-file edits or
new sub-developments (leaf-new-file agents correctly refused to cross their write boundary) — the
orchestrator-coordination inflection point.

- **Ch13 (Cauchy rigidity), spherical arm lemma.** UNCONDITIONAL: PlanarConvexDiagPos (GP-syzygy,
  sign-definite), cyclicTriplePos, both-sign §8.1 keystone (oriented opening), DiagonalCutArm, tailArm
  (endpoint-preserving), the joint-angle-target reach/stuck trichotomy at the admissible sup, and the FULL
  §8.3 neighbourhood convexity persistence (openArm_strictConvex_nhds, all 5 fields incl. open_hemisphere).
  RESIDUE: BoundaryConvexPersist (extend §8.3 persistence to the admissible sup δ* — the admissible-sup
  family monitors only mixed-supports + targetSlack, NOT the rotated-tail open_hemisphere; needs adding it
  to the monitored family upstream in SphericalAdmissibleSup/SphericalCore) + OpeningStructuralAssembly
  (arbitrary-joint opening + reach recursion + matched-data cut). The prior BoundaryConvexPersistAtSup was
  found UNSOUND and replaced.
- **Ch35 (Five Color / Thomassen).** UNCONDITIONAL: SidesReach2, chord-case recursion knot, V/E/face-count
  theorems, the genus-0 no-handle core (genus-slack monotonicity — the deepest 3-kernel-round residue,
  closed), kept-side connectivity, Side₁IsDisk (fully unconditional), ι_surj (side-vertex orbit surjection).
  RESIDUE: ChordSideClassification = NearTriangulation(sideMap₁) — the outerCycle/inner_tri face
  classification (kernel-confirmed genus-dependent face structure, CutFaceLabel) + correct-anchor
  ContiguousInterval (for ι_inj / the fresh-chord-dart ι_adj) + the chordless FanSurgeryReconstruction
  outerCycle/inner_tri (no producer) + hcompat (Separates' input, obvious form false per CH35_BRIDGE §6).
  The genuine discrete-Jordan face-classification development.
- **Ch36 (Chvátal art gallery).** UNCONDITIONAL: the entire ray-crossing-parity core (global
  ray-independence, n=3 degenerate-wall transport), hconv (crossTau-sign), SubRegionContainment +
  OffDiagDisjoint (derived from a CutGeometry's primitive split-region fields), the det2-side diagonal-line
  geometry. RESIDUE: RegionSplitGenericity (= general-n GenericChainInput — the det2-side↔crossing-region
  link IS the wall-crossing parity transport ∘ general-n ray-genericity; n=3 done, general n needs extending
  the degenwall machinery; straight-segment shortcut blocked) + M peel-order (upstream
  PolygonLast.combinatorialGlue_of_attach edit).

Pattern: Ch35 + Ch36 both bottom out at discrete-Jordan face/region classification; Ch13 at the SZ-opening
boundary persistence + structural assembly. Genus-slack (Ch35) and the CutGeometry primitive-field
reduction (Ch36) proved that "irreducible Jordan walls" can crack — the remaining cores are coordinated
upstream extensions, not foundational impossibilities.

## Objective results (mechanical, definitive)
- **0 `sorry` / 0 `admit`** across all 54 `.lean` files.
- **0 top-level `axiom`** declarations.
- **`#print axioms chapterNN` = {propext, Classical.choice, Quot.sound} for ALL 40** (no sorryAx / ofReduceBool / native).
- Full library compilation succeeds (8474 jobs, 0 errors).

So the ONLY open audit axis is FAITHFULNESS (real theorem vs fragment / conditional-on-assumed-content).

## Per-chapter verdict
LEGEND: ✅ faithful · ⚠️ conditional/fragment (real content assumed) · ❓ needs deeper read · ★ faithful via alternate thm

| Ch | Theorem | Verdict |
|----|---------|---------|
| 01 | Infinite primes | ✅ |
| 02 | Bertrand: ∃ prime in (n,2n] | ✅ |
| 03 | binom(n,k) ≠ m^l (Erdős–Sylvester) | ✅ |
| 04 | p≡1(4) ⇒ p = a²+b² | ✅ |
| 05 | Quadratic reciprocity | ✅ |
| 06 | Wedderburn: finite division ring commutative | ✅ |
| 07 | √2 irrational | ✅ |
| 08 | Basel: Σ1/n² = π²/6 | ✅ |
| 09 | Dehn: cube ≠ tetra (invariants differ) | ❓ is Dehn-invariance-under-scissors established, or just the ≠ computation? |
| 10 | Sylvester–Gallai ordinary line | ✅ |
| 11 | ⌊n/2⌋ directions (Scott) | ✅ |
| 12 | {(p,q):3≤p,q, pq<2p+2q} finite (Platonic) | ❓ one of Euler's-formula applications; only "finite", full chapter? |
| 13 | Cauchy rigidity | ⚠️ conditional on CauchyRigidityCertificate (arm-lemma sign data + Euler assumed) |
| 14 | Perles touching simplices < 2^(d+1) | ⚠️ conditional on PerlesFacetSeparationData (separation crux assumed) |
| 15 | 2^d < #pts ⇒ obtuse triple | ✅ |
| 16 | Borsuk conjecture false | ✅ |
| 17 | Cantor: no surjection α→𝒫(α) | ✅ |
| 18 | AM-GM √(ab) ≤ (a+b)/2 | ❓ only 2-variable; chapter's full claim? |
| 19 | Fundamental theorem of algebra | ✅ |
| 20 | Monsky | ★ headline `chapter20` conditional on MonskyCertificate; FAITHFUL via `monsky_dissection` (verified) |
| 21 | Integer-valued polynomials = ℤ-comb of binomials | ✅ |
| 22 | van der Waerden/Gurvits permanent ≥ n!/n^n | ⚠️ conditional on GurvitsSquarefreeCoefficientFromCapacityCore (analytic core assumed) |
| 23 | Littlewood–Offord ≤ C(n,⌊n/2⌋) | ✅ |
| 24 | Herglotz/duplication uniqueness (cotangent) | ✅ (honest analytic hyps) |
| 25 | Buffon needle = 2ℓ/(πd) | ✅ |
| 26 | Erdős–Szekeres monotone subsequence | ✅ |
| 27 | n×1 tiling ⇔ n∣a ∨ n∣b (de Bruijn) | ✅ |
| 28 | Sperner+EKR+Dilworth (three) | ✅ |
| 29 | GSR riffle shuffle distribution | ✅ |
| 30 | Lindström–Gessel–Viennot | ✅ |
| 31 | Cayley: #labeled trees = n^(n-2) | ✅ |
| 32 | Three binomial identities | ✅ |
| 33 | Latin square completion (Evans/Smetaniuk) | ⚠️ conditional on EvansExactCardinalityCase = the =n-1 Smetaniuk core (whole hard content assumed) |
| 34 | Dinitz / list-edge-coloring | ✅ |
| 35 | Five color theorem | ⚠️? conditional on FiveColorReducible G — check if every planar G satisfies it |
| 36 | Art gallery ⌊n/3⌋ guards | ⚠️? conditional on TriangulatedPolygon — check faithfulness |
| 37 | Turán's theorem | ✅ |
| 38 | Singleton + GV code bounds | ✅ |
| 39 | Kneser–Lovász | ★ headline conditional on htucker; FAITHFUL via `chapter39_unconditional` + `tuckerLemma_pos` (verified) |
| 40 | Friendship theorem | ✅ |

## Triage (after deep reads, 2026-06-04)
- **CONFIRMED faithful + axiom-clean (30):** 01-08,10,11,15,16,17,18,19,21,23,24,25,26,27,28,29,30,31,32,34,37,38,40.
  - Ch18 CLOSED 2026-06-04 (was 2-var only; now headline = general n-AM-GM + `chapter18_cauchy_schwarz`).
  - Ch12 CLOSED 2026-06-04 (was bare nlinarith set-finiteness; now Platonic solids DERIVED from Euler via new `PlanarMap` infra).
- **FAITHFUL via verified alternate (3):** 20 (monsky_dissection), 39 (chapter39_unconditional + tuckerLemma_pos), 14 (chapter14_unconditional from FaithfulPairwiseTouching = touch along facet interiors, the faithful book 'touching'; #print axioms clean. NOTE: definition-faithfulness call flagged for Xiang).
- **TALLY: 34/40 faithful + axiom-clean.** (Ch22 CLOSED 2026-06-04: chapter22_unconditional, van der Waerden permanent bound via Gurvits capacity — fully formalized incl. Rouche-free root-continuity + half-plane Gauss-Lucas; #print axioms clean)
- **NEW INFRASTRUCTURE built (the Mathlib hole):** `ProofsInTheBook/PlanarMap.lean` — combinatorial maps, orbit-count V/E/F, `eulerChar`, faithful genus-zero `IsSphereMap`, edge structure (2E=|D|), regularity counting (pF=2E, qV=2E), `platonic_constraint` (1/p+1/q>1/2 from Euler), `platonic_pairs` (the five). 0-sorry, axiom-clean. This is Layer 1 + the Ch12 consequences; the Ch35 deletion+Kempe machinery (design in HANDOFF/EULER_DESIGN_r3.md) builds on it next.
- **CONFIRMED FRAGMENTS (6) — the genuine remaining work:**

  | Ch | What's assumed/missing | Closability |
  |----|------------------------|-------------|
  | 09 Dehn | no scissors-congruence predicate; no "scissors-congruent ⇒ equal Dehn" invariance thm; headline only states two Dehn values differ (the arccos(1/3)/π irrationality IS genuinely proved) | HARD: needs geometric equidecomposability + invariance (Mathlib lacks) |
  | 12 Euler | Euler's formula V-E+F=2 NOT proved (docstring only); chapter12 is a pure `nlinarith` finiteness fact, disconnected from graph theory; only 1 of 3 applications | MED-HARD: needs planar Euler formula |
  | 13 Cauchy | conditional on CauchyRigidityCertificate (arm-lemma sign-change data + Euler bundled as hypothesis) | MED: arm lemma is finite-combinatorial |
  | 14 Perles | conditional on PerlesFacetSeparationData (the separation crux `pairwiseOpposite_of_touching` is the hypothesis) | MED |
  | ~~18 AM-GM~~ | ✅ CLOSED 2026-06-04 | done |
  | ~~12 Euler/Platonic~~ | ✅ CLOSED 2026-06-04 (PlanarMap infra) | done |
  | 22 Gurvits | conditional on GurvitsSquarefreeCoefficientFromCapacityCore (the analytic capacity bound = heart of the proof) | HARD: analytic capacity argument |
  | 33 Latin | conditional on EvansExactCardinalityCase = the `=n-1` Smetaniuk switching core (whole hard content) | HARD: Smetaniuk's theorem |
  | 35 Five-color | FiveColorReducible is an inductive certificate ENCODING the Kempe-reduction steps; no planarity defined; needs `IsPlanar G → FiveColorReducible G` | HARD: Mathlib lacks planar graph theory |
  | 36 Art gallery | 3-coloring of triangulation IS proved (crux); but TriangulatedPolygon is abstract (no geometry), no visibility, polygon-triangulation existence excluded | HARD: needs polygon geometry |

  Closability order: **18 ✅ → 22,33 (research-grade, self-contained) → 13,14 (need polytope geometry) → 09,12,35,36 (need geometric/topological infra Mathlib lacks).**

## Remaining-work assessment (2026-06-04, refined after deep reads + design rounds)
The 8 open fragments, now with closability sharpened:
- **Ch33 (Evans/Smetaniuk):** REDUCED (codex df0eb2b) to the single statement `EvansNormalizedCellCase n (last,last,last)` for n≥4 = the genuine Smetaniuk diagonal/switching construction. Self-contained finite combinatorics. Needs a blueprint then formalize. Scaffold (Hall, rectangle extension, normalization, n≤3) all proven.
- **Ch22 (Gurvits/van der Waerden permanent):** scaffold complete (squarefree coeff = permanent, capacity≥1 from doubly-stochastic, n≤2 base, core-equivalences). Single gap = the capacity⇒coefficient inductive step `cap(p)≥1 ⇒ coeff ≥ n!/nⁿ` via the reduction with constant G(k)=(k-1)^{k-1}/k^{k-1}. Needs real-stable / capacity machinery (analysis). Research-grade.
- **Ch14 (Perles):** REACHABLE — NOT an infra wall. Combinatorial 2^(d+1) counting core (`PerlesMatrix.card_lt_two_pow_succ`) PROVEN; FacetHyperplanes/rowZeroCard/missingSignVector all constructed. The ONLY gap: prove `PairwiseTouching ⇒` opposite-vertices-on-opposite-sides (`PairwiseTouchingAcrossFacets`) — pure affine geometry in ℝᵈ, and Mathlib HAS the tools (AffineSubspace.signedInfDist, WSameSide/SSameSide, Affine.Simplex). A proof obligation, not missing infra.
- **Ch13 (Cauchy rigidity):** combinatorial counting+parity+Euler-contradiction core PROVEN; conclusion is `False` (no nontrivial flex). Gap = a polytope substrate (vertex-link as planar polygon) + ONE Euclidean arm-lemma inequality (chord strictly increases as angles open). The arm lemma is a single Euclidean fact, not a topology wall. Medium-hard, reachable.
- **Ch09 (Hilbert 3rd):** arithmetic obstruction (arccos(1/3)/π irrational, Dehn values differ) PROVEN. Gap = scissors-congruence relation + invariance (scissors-congruent ⇒ equal Dehn). Mathlib HAS `Equidecomp` (group-action equidecomposability) as a base; need the polytope+isometry instantiation + Dehn additivity.
- **Ch12 + Ch35 (Euler / 5-color):** building shared planar-map infrastructure (Xiang: "Mathlib 没有的我们补上"). Design converging over rounds: faithful def `IsSphereMap M := Connected ∧ EulerChar = 2` (genus-zero, NOT an inductive certificate — avoids the fragment trap), combinatorial maps (darts/α/σ), deletion-closure for the 5CT min-degree induction, σ-based Kempe non-crossing. Round 3 pinning deletion-closure + Lean encoding.
- **Ch36 (art gallery):** 3-coloring crux PROVEN; needs polygon-triangulation existence + visibility geometry. Hardest geometric build.

Reclassification: 13 and 14 move from "infra-blocked" to "reachable proof obligations" (Mathlib has the affine-geometry tools). The genuine new-infra builds are 12+35 (planar maps — in progress), 09 (Dehn invariance, partial base in Equidecomp), 36 (polygon geometry).

WORKERS (2026-06-04, /Xiang mode): Ch33 codex → reduced to Smetaniuk-switching (committed df0eb2b). Euler/planar design → round 3 (pbook serialized; bridge was flaky under concurrency, fixed by one-question-at-a-time).

## Session progress 2026-06-04 (cores reduced to precise named lemmas)
TALLY: **33/40** faithful+axiom-clean (closed this session: 39 Tucker, 18 AM-GM, 12 Platonic, 14 Perles).
New infra (the Mathlib hole): PlanarMap / PlanarMapEuler / PlaneSimpleGraph / PlanarMapDelete; Chapter22Gurvits.
Every remaining fragment is now reduced to ONE precise hard core:
- **09 Dehn:** scissors-congruence def + invariance (scissors-congruent ⇒ equal Dehn). Geometry; Mathlib `Equidecomp` base. (arithmetic obstruction PROVEN)
- **13 Cauchy:** the Euclidean arm-lemma (chord monotonic in opening angle) + a convex-polytope substrate. (combinatorial counting core PROVEN)
- **22 Gurvits:** `GurvitsIteratedCapacityCertificate` — the single analytic estimate `∏G(m) ≤ rowLinearSquarefreeCoeff A`. Needs real-stable polynomial theory (Mathlib hole) + the univariate Gurvits lemma. (telescoping `∏G=n!/nⁿ` PROVEN; everything else wired)
- **33 Smetaniuk:** the triangular normalization from the bare exact case ({2,2,0,0,0}-order-5 has no uniquely-occurring symbol — needs the real reordering, not pigeonhole). (the cunning-extension SWITCHING `SmetBackDiagonalCompletableCore` PROVEN)
- **35 Five-color:** graph-layer deletion redesign — the bare-CombMap closed-star deletion is provably false (deg-1 neighbors vanish, bridges repeat faces; counterexamples in PlanarMapDelete). Then Kempe non-crossing + coloring induction. (Euler half: 3F≤2E, E≤3V−6, min-degree-5 PROVEN; `Perm.deleteSet` splice PROVEN)
- **36 Art gallery:** polygon-triangulation existence + visibility geometry. (combinatorial 3-coloring PROVEN)

Design-gated (Ch09/13/36 + Ch33 normalization): the auto pbook bridge truncates long design answers; Xiang relaying ChatGPT-Pro (as with the Tucker proof) is the reliable unblock. Blueprints staged at /tmp/pbook_*.txt.

## Ch09 CLOSED (2026-06-06): chapter09_weighted — 37/40
`ProofsInTheBook.Chapter09Weighted.chapter09_weighted : ¬ Nonempty (TetEquidecomp regularTetSolid cubeSolid)`
— UNCONDITIONAL, axioms = {propext, Classical.choice, Quot.sound}. The Bricard angular obstruction
(Pearl/Cone route, book ch9): cone_lemma -> pearl_lemma -> sector sums -> tet substrate -> dihedral
angles (arccos(1/3) / Kuhn classification pi/2,pi,2pi) -> weighted Sigma double count -> mod-Qpi
contradiction via the proven arccos irrationality. Fixed-size pair (regular tet, unit Kuhn cube);
the obstruction is scale-invariant (no volume used) — the forall-size form is a cosmetic similarity
transport, noted honestly. 20 files, ~8000 lines built for this chapter.
Open = {13, 35, 36} = 3 chapters.

## Closing-round status (2026-06-06, latest)
In flight: polylast (Ch36: count bijection + half-plane + merge => unconditional artGallery),
bricardloc (Ch09: the two concrete LocationData certificates => unconditional headline),
sphcore (Ch13: SZOpeningCore => unconditional spherical arm; then vertex-link).
Ch35 queued: abstract seam characterization => BankComponentCert; bridge witness; deletion data.
Each chapter's full engine is proven and pushed; the in-flight rounds are pure instantiation.

## Endgame status (2026-06-06, late)
- Ch36: in-flight rayindep = ray-direction independence (span_mod_two in the direction variable) +
  Fisk bridge + artGallery_strict headline. Everything else proven.
- Ch09: in-flight bricardcube = Kuhn 6-simplex cube + EdgesNonOverlapping + pi/2 externals; then
  only the two LocationData certificates remain.
- Ch13: kernel + cosine rule + hinge proven; in-flight spharm = the SZ induction (triangle ineq,
  rotation operation, admissible sup, stuck chain).
- Ch35: queued = abstract seam characterization (the convergent missing layer) feeding
  BankComponentCert.same_component; bridge witness data; deletion orientation data; f13-16.

## Closing wave (2026-06-06, this session) — 37/40, residues named + closers dispatched
Three open chapters; each hard core REDUCED to a named 0-sorry residue (axioms clean-3, pushed),
with one Opus closer in flight per chapter:
- **Ch35**: WitnessFinal.lean closed `SidesReach2` UNCONDITIONALLY (refuted the prior bwitness
  "irreducible core" verdict — the corrected sigma'2 wiring threads cycle darts into one phi'2-orbit;
  sidesReach2_concrete is a total no-hypothesis theorem). separates_final assembled. Remaining surface =
  (1) F-side seam, (2) interior-dual fragment supplier (triangle-dischargeable per fragmentCompatible2_singleFace),
  (3) deletion-side + NumCyclesCutPhi2 + f13-16. CLOSER: jordanoracle — construct JordanOracle α
  unconditionally (the last hypothesis of nearTriangulation_five_colorable) → unconditional 5CT.
- **Ch13**: SphericalHinge.lean — load-bearing reduction openedArmReachOrStuck_of_hingeConvexPosition
  (stuck branch PRODUCES the 3 determinant/Gram fields from betweenness, not a re-wrapper); clean arm
  lemmas conditional only on the single residue HingeConvexPosition = OpeningData (the §8.4 SZ opening
  construction). CLOSER: szchain — prove openingData_holds via §8.4 Case-2 cut-and-induct (the
  diagonal cut from a NON-terminal tight determinant, which sidesteps the false terminal-first /
  terminal-visibility obstruction) → UNCONDITIONAL spherical arm lemma. Frontier after = vertex-link
  correspondence (Cauchy bridge §9-§13, full design in CH13_CAUCHY_FULL_DESIGN.md).
- **Ch36**: PolygonWall.lean — rfcount_eventually_zero_of_wall (each direction wall, generic OR
  degenerate, off-boundary contributes 0 crossing-count change in a nbhd). CLOSER: pwglobal — global
  assembly (local constancy everywhere + no-jump-at-walls over compact ℝ → ℤ-valued count constant →
  r1=r2 count equality → unconditional ray independence → discharge PolygonSeparation's ray oracle →
  unconditional artGallery_strict).
The Rodrigues rotation engine (SphericalRotation: rot/rotS2/group-law/isometry) is fully built — Ch13
§8.1 layer done, reused not rebuilt.

## Deep-grind frontier (2026-06-06, late — after the multi-round closing wave)
Still 37/40. Each of the three open chapters had its hard core driven layer-by-layer to a single
NAMED concrete residue, banking genuine unconditional content at every step (all 0-sorry, clean-3,
pushed). Two re-wrapper attempts caught and NOT banked (jordanoracle JordanInput, szchain SZStepGeom
co-extensive). The residues are the genuine mathematical cores of the three hardest BOOK chapters:

- **Ch13 (Cauchy rigidity)** — spherical arm lemma. UNCONDITIONAL now: PlanarConvexDiagPos (the
  convex-position core, via the quadratic Grassmann-Plucker syzygy = sign-definite arithmetic,
  avoiding oriented-angle/mod-2pi — a genuine breakthrough), hence cyclicTriplePos. BANKED base:
  reach_base_endpoint_mono (via spherical_hinge_mono), equalAngleCut_step, diag_len_eq,
  cut_endpt_transport. RESIDUE = 3 named Props (the §8 hinge/cut machinery, currently UNBUILT):
  OpenedBaseAngleMono (§8.1 oriented tangent-angle additivity), OpenArmConvexPersist (§8.3),
  StuckGivesCut (§8.4 diagonal cut). Closer: SphericalHingeCut.lean (in flight). Frontier after =
  vertex-link correspondence / Cauchy bridge (full design in CH13_CAUCHY_FULL_DESIGN.md).
- **Ch35 (Five Color / Thomassen)** — UNCONDITIONAL now: SidesReach2, the chord-case recursion knot
  (chord_case_recursive PRODUCES side colorings by recursing — colorings off the oracle hypothesis
  surface), freshMap V/E orbit counts, side-map connectivity. RESIDUE = FreshFaceCount (F1+F2=F+1,
  the genus-0 face certificate) — kernel-CONFIRMED (CutFaceLabel campaign, K4 sphere/torus mirror)
  genus-DEPENDENT, so Separates-reachability CANNOT give it; needs M's genus-0 face structure via an
  explicit face-permutation orbit bijection (the vertex bijection in ChordSplitEuler is the template).
  Closer: ChordFaceCount.lean (in flight). The repo architecturally makes this a structure field
  everywhere (CutCapSurgery.face_count, FanSurgeryReconstruction.facesMerge) — the deepest residue.
- **Ch36 (Chvatal art gallery)** — UNCONDITIONAL now: the ENTIRE ray-crossing-parity combinatorial
  core — global ray-independence (no-wall hyp eliminated), generic-stratum discharge, and the
  triangle degenerate-wall double-event transport ⟹ unconditionalRayIndepInput_triangle +
  triangleExteriorEven_unconditional (both 0-hypothesis, clean-3). RESIDUE = the Fisk
  triangulation-recursion planar geometry: ResidualGeometryData (convex-vertex existence, diagonal
  transversality, half-plane disjointness, intersection=diagonal), TriangleConvexLeaf (easy),
  DiagonalAttachInput. Closer: PolygonGeometryData.lean (in flight). The "hardest geometric build."

Honest note: these three residues are each substantial genuine geometry/topology (not fakeable),
likely multi-round. The campaign is converging (real lemmas banked each round, residues named and
shrinking), not looping.

## Frontier 2026-06-06 (the three-chapter endgame, all engines built)
- Ch35: chord wall = BankComponentCert.same_component (per-cycle bank-component fact; 13 passes of
  machinery all proven: chi_le_two, V'/E', touch-rank engine, word realization, Jordan-from-lower-
  bound) + bridge witness data + deletion-side orientation data (FanIncidenceData etc.) + f13-16
  assembly. The convergent missing layer: ABSTRACT symbolic characterization of faceCorr2's cycle
  structure (everything kernel-anchored, no abstract SimplePrimalCycle instance exists yet).
- Ch09: headline regularTet_cube_no_equidecomp_aggregated stands on {LocationData/PearlSectorModel
  certificates, concrete normalizations, EdgeSourceFaithful}; bricardconcrete agent closing these
  (cube tet-decomposition + concrete certificates).
- Ch36: exists_diagonal' UNCONDITIONAL under the corrected side-coordinate convention (the old
  fixed-ray parity was REFUTED by counterexample and repaired per ChatGPT ruling); polytri agent
  building EarTriangulation existence + region splits; then the art-gallery bridge to the proven
  combinatorial 3-coloring.
- Ch13: planar arm core proven (profile form); spherical substrate design not yet started (queue).

## Ch35 F-count state (2026-06-05 late, 7 passes deep — read before resuming)
The ONE remaining count: NumCyclesCutPhi2 (numCycles phi'2 = F+2 for the corrected cutCapMap2).
PROVEN stack: abstract seam-chain theorem (SeamChain), mixed-chain theorem + pure-cycle lemma +
two-factor assembly (SeamSpec), end-to-end closure FROM SeamDecomposition data (SeamInst).
KERNEL FACTS: F'=F+2 holds ACROSS GENUS (triangle, K4-sphere, K4-torus); but the two-disjoint-chain
factorization is GENUS-0-ONLY (torus: chains merge into one 7-cycle); chain shapes vary by cut even
at genus 0. CONCLUSION: the count needs either a genus-free route (local surgery identity chi'=chi+2?)
or genus-0 injection at the APPLICATION layer (our chords live in sphere near-triangulations).
Pbook question on the genus-free route pending. The Jordan chain otherwise COMPLETE: chi_le_two,
V'/E', bridge two-layer, witness wiring — all proven; separates2_of_core awaits only this count
(+ per-edge witness data SidesReach2/FragmentCompatible2, also application-layer).

## Frontier map 2026-06-05 (36/40; every open chapter has its verbatim book text + a ChatGPT design round in HANDOFF/)

Open = {09, 13, 35, 36}. New bricks landed this session (all 0-sorry, axiom-clean, in the root build):
- ConeLemma.lean: cone_lemma (book ch9 Cone Lemma) — rational-kernel density via flat base change.
- ArmLemma.lean: cauchy_arm_lemma (planar Cauchy arm lemma, direction-angle profile normal form,
  chord-formula monotonicity — slicker than the book's Schoenberg induction). AUX until the
  convex-position recognition theorem lands.
- ListColoring.lean: ch35 layer 4 (ProperOn/ListValidOn/IsListColoring, graph+list monotonicity,
  piecewise glue, rooted cut-vertex glue — the form that is TRUE for list colorings —, greedy extension).

Per-chapter state and the named hardest remaining lemma:
- 09 (Dehn): design = HANDOFF/CH09_GEOMETRY_DESIGN.md (simplices-only TetSolid; pearls by breakpoint
  partition; Bricard via ONE homogeneous system + the proven cone_lemma). Hardest:
  pearl_angle_sum_classification, normal form = 2D sector sums (disk 2π / half-disk π / wedge θ)
  via polar-interval additivity. Briefs staged: TASK_SectorSum.md, TASK_TetPearls.md.
- 13 (Cauchy): arm-lemma core PROVEN (profile form). Remaining: convex-position recognition
  (polygon design layer B) + the SPHERICAL arm lemma + vertex-link substrate (the true wall;
  design note HANDOFF/CH13_ARM_ROUTE.md).
- 35 (Five-color): route = book ch34 Thomassen list coloring ("does not use Euler's formula at
  all"); design = HANDOFF/CH35_DESIGN_ANSWER.md (NearTriangulation primitive, duplicated-dart chord
  split, filtered-rotation boundary deletion — restricted to exactly the cases excluded by our
  deletion counterexamples —, block-decomposition bridge with rooted glue). Adversarial design
  review in flight (c35review). Hardest: deleteBoundaryVertex surgery re-verification + the
  case-2 list bookkeeping (book reserves two colors from C(v0)).
- 36 (Art gallery): design = HANDOFF/CH36_13_POLYGON_DESIGN.md (StrictSimplePolygon; ray-crossing
  parity region, NO Jordan; EarTriangulation inductive existence -> GeomTriangulation finite data;
  visibility trivial by triangle convexity). Hardest: slide_last_vertex_visible_from_A + the
  region-split lemmas (A4). Substrate layers A0-A2 in flight (c36poly).

## Definitive frontier map (2026-06-04 end-of-session, each wall verified absent from Mathlib by direct probe) [SUPERSEDED by the 06-05 map above]
| Ch | Everything proven except | Mathlib status of the wall |
|----|--------------------------|----------------------------|
| 22 Gurvits | polynomial root-continuity / Hurwitz specialization (the ε→0 boundary argument); classical proof = Rouché | NO Rouché, NO argument principle, NO root-continuity (probed) |
| 33 Smetaniuk | the strengthened induction invariant handling no-singleton-symbol exact cases (my positional+unused-symbol design refuted by codex on counting; sharpened question with ChatGPT-Pro) | pure combinatorics; needs the literature's exact statement |
| 35 Five-color | deleted-star boundary topology (dart-model version proven FALSE by counterexample) + Kempe non-crossing | NO planar-graph topology (probed earlier) |
| 09 Dehn | scissors-congruence relation + Dehn additivity/invariance | only group-action `Equidecomp` exists; no polytope dissection theory |
| 13 Cauchy | Euclidean arm lemma + convex-polytope substrate | no convex-polyhedron incidence/dihedral theory |
| 36 Art gallery | polygon triangulation existence + visibility | no polygon/visibility geometry |

Proven THIS session toward these: Ch22 = telescoping + AM-GM bound + univariate Gurvits crux + capacity
iteration + RealStable framework + row-linear base + univariate Lieb-Sokal (derivative closure + UHP bridge).
Ch33 = cunning-extension switching + exists_perm_strictly_above (the permutation crux). Ch35 = Euler half
(3F≤2E, E≤3V-6, min-degree-5) + Perm.deleteSet splice + the deletion counterexamples. Plus closed outright:
Ch39 (Tucker), Ch18 (AM-GM), Ch12 (Platonic from Euler, via the new PlanarMap infra), Ch14 (faithful touching).

### Ch22 wall DOWNGRADED (route discovery, end of session)
The Hurwitz/root-continuity specialization does NOT require building Rouché. Assemblable route, all
ingredients verified present in Mathlib:
1. Factor each q_ε over ℂ: `Polynomial.Splits.eq_prod_roots` (alg. closed). Roots of q_ε have im ≤ 0 (stability).
2. Cauchy root bound (|root| ≤ 1 + max‖coeff‖/‖lead‖) — small elementary lemma to prove.
3. Bolzano–Weierstrass on the bounded root vectors (Mathlib compactness) along ε→0⁺: subsequence with
   root-vector limit, each limit root has im ≤ 0.
4. Vieta (`Multiset.prod_X_sub_C_coeff`): coefficients = ±lead·esymm(roots), continuous in the roots —
   so the coefficientwise limit q₀ equals lead₀·∏(X − limit-root), i.e. q₀'s roots all have im ≤ 0.
5. Degree-drop case (lead_ε → 0) handled separately in the application.
So Ch22 = one focused ~150-line analysis-lite formalization away (no missing Mathlib foundation).

## TALLY CORRECTION (2026-06-04, after Ch22 close)
Definitive recount: CLOSED = every chapter except {09, 13, 35, 36} = **36/40**.

## Ch33 CLOSED (2026-06-05): chapter33_unconditional
`ProofsInTheBook.Chapter33.chapter33_unconditional : ∀ n, LatinSquareCompletionTheorem n` —
the Evans conjecture (Smetaniuk's theorem), no hypotheses, axioms = {propext, Classical.choice, Quot.sound},
full build 8422 jobs. Route = the BOOK's own proof (HANDOFF/CH33_BOOK_ROUTE.md), not improper Latin squares:
book Lemma 2 (Chapter33Ryser.lean: conjugacy + row-by-row Hall with the quadratic inequality) for the
few-symbols case; otherwise a singleton symbol is renamed to the fresh symbol, normalized onto the diagonal,
deleted before the inductive call (card drops to <= N-1), and recovered automatically because the proven
back-diagonal extension prescribes the fresh symbol on the whole back diagonal. The improper-Latin-square
conditional route (chapter33_unconditional_of_improperExtensionStatements) remains in the file as the
documented alternative; its missing extension lemma is now moot.
(The earlier "33/40" line had an off-by-one: Ch12's close was recorded as a sub-bullet but not added to the
count.) Closed list: 01-08, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23-32, 34, 37, 38, 39, 40.
Open (5): 09 (Dehn invariance), 13 (Cauchy arm-lemma), 33 (Smetaniuk normalization — switching + permutation
crux proven, ChatGPT-Pro answer in flight), 35 (5-color deletion topology + Kempe — Euler half + deleteSet
proven), 36 (art gallery geometry — 3-coloring proven).
