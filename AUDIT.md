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
- **CONFIRMED faithful + axiom-clean (29):** 01-08,10,11,15,16,17,18,19,21,23,24,25,26,27,28,29,30,31,32,34,37,38,40.
  - Ch18 CLOSED 2026-06-04 (was 2-var only; now headline = general n-AM-GM + `chapter18_cauchy_schwarz`).
- **FAITHFUL via verified alternate (2):** 20 (monsky_dissection), 39 (chapter39_unconditional + tuckerLemma_pos).
- **TALLY: 31/40 faithful + axiom-clean.**
- **CONFIRMED FRAGMENTS (8) — the genuine remaining work:**

  | Ch | What's assumed/missing | Closability |
  |----|------------------------|-------------|
  | 09 Dehn | no scissors-congruence predicate; no "scissors-congruent ⇒ equal Dehn" invariance thm; headline only states two Dehn values differ (the arccos(1/3)/π irrationality IS genuinely proved) | HARD: needs geometric equidecomposability + invariance (Mathlib lacks) |
  | 12 Euler | Euler's formula V-E+F=2 NOT proved (docstring only); chapter12 is a pure `nlinarith` finiteness fact, disconnected from graph theory; only 1 of 3 applications | MED-HARD: needs planar Euler formula |
  | 13 Cauchy | conditional on CauchyRigidityCertificate (arm-lemma sign-change data + Euler bundled as hypothesis) | MED: arm lemma is finite-combinatorial |
  | 14 Perles | conditional on PerlesFacetSeparationData (the separation crux `pairwiseOpposite_of_touching` is the hypothesis) | MED |
  | ~~18 AM-GM~~ | ✅ CLOSED 2026-06-04 | done |
  | 22 Gurvits | conditional on GurvitsSquarefreeCoefficientFromCapacityCore (the analytic capacity bound = heart of the proof) | HARD: analytic capacity argument |
  | 33 Latin | conditional on EvansExactCardinalityCase = the `=n-1` Smetaniuk switching core (whole hard content) | HARD: Smetaniuk's theorem |
  | 35 Five-color | FiveColorReducible is an inductive certificate ENCODING the Kempe-reduction steps; no planarity defined; needs `IsPlanar G → FiveColorReducible G` | HARD: Mathlib lacks planar graph theory |
  | 36 Art gallery | 3-coloring of triangulation IS proved (crux); but TriangulatedPolygon is abstract (no geometry), no visibility, polygon-triangulation existence excluded | HARD: needs polygon geometry |

  Closability order: **18 ✅ → 22,33 (research-grade, self-contained) → 13,14 (need polytope geometry) → 09,12,35,36 (need geometric/topological infra Mathlib lacks).**

## Remaining-work assessment (2026-06-04)
The 8 open fragments are the hard tail — none is a quick close:
- **Ch33 (Evans/Smetaniuk):** scaffold present (Hall, Latin-rectangle extension, normalization, padding reduction, n≤3 done); missing = the general `=n-1` Smetaniuk switching induction. Self-contained finite combinatorics, research-grade.
- **Ch22 (Gurvits/van der Waerden permanent):** missing = the analytic capacity lower bound (stable-polynomial / capacity argument). Self-contained analysis, research-grade.
- **Ch13/14 (Cauchy rigidity / Perles):** the combinatorial cores are reachable, but the *faithful* unconditional theorems need convex-polytope geometry (realization), which Mathlib lacks.
- **Ch09 (Hilbert 3rd):** needs a geometric scissors-congruence/equidecomposability relation + the invariance theorem (scissors-congruent ⇒ equal Dehn). The arithmetic obstruction (arccos(1/3)/π irrational, Dehn values differ) IS proved. Mathlib lacks equidecomposability.
- **Ch12 (Euler):** needs Euler's formula V-E+F=2 for planar graphs proved (Mathlib lacks planar-graph theory), then derive the Platonic constraint from it.
- **Ch35 (5-color):** needs a planarity predicate + `IsPlanar G → FiveColorReducible G` (Mathlib lacks planar graphs / Kempe-chain separation).
- **Ch36 (art gallery):** 3-coloring crux IS proved; needs polygon-triangulation existence + visibility geometry (Mathlib lacks).

DISPATCH STATUS: uisai1 saturated (load ~101, 6 codex, 89 lean) as of 2026-06-04 13:11 — codex dispatch on hold to avoid thrash; resume 33/22 dispatch when it drains.
