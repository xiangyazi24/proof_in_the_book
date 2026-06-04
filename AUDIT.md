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

## Triage
- **CONFIRMED faithful + axiom-clean (~28):** 01-08,10,11,15,16,17,19,21,23,24,25,26,27,28,29,30,31,32,34,37,38,40.
- **FAITHFUL via verified alternate (2):** 20 (monsky_dissection), 39 (chapter39_unconditional).
- **FRAGMENT / conditional-on-core (needs real proof) (≈4-6):** 13, 14, 22, 33, and check 35, 36.
- **FRAGMENT-RISK / needs deeper read (3):** 09, 12, 18.

Next: deep-read 09,12,13,14,18,22,33,35,36 to confirm fragment vs faithful, then close the genuine fragments.
