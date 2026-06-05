# Whole-book faithfulness audit — Proofs from THE BOOK (40 chapters)

Date: 2026-06-04. Method: per-chapter headline theorem `chapterNN`, statement-faithfulness + `#print axioms`.

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

## Definitive frontier map (2026-06-04 end-of-session, each wall verified absent from Mathlib by direct probe)
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
