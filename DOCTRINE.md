# DOCTRINE.md — Proofs from THE BOOK, full-book closure

**Main goal (one sentence):** Remove every escape hypothesis from the 7 open
chapters so the whole repo is 0-sorry / 0-axiom **and passes the §3.1 audit**
(no fragment, no hypothesis-substitution, no trivial impostor) — each open
chapter ends in a theorem whose only inputs are raw mathematical objects.

## The 7 open chapters (escape currently taken)

| Ch | Escape field / hypothesis | Audit verdict today |
|----|---------------------------|---------------------|
| 20 Monsky | `RealEqualAreaUnitSquareTriangulation.hboundary` (full-edge mult ⟺ boundary) | FRAGMENT — edge-to-edge only; real dissections have T-vertices |
| 39 Kneser | `htucker` | CONDITIONAL (Tucker lemma) |
| 22 VdW permanent | only n≤2 done | FRAGMENT |
| 09 Dehn | `chapter09` disconnected from geometry | FRAGMENT |
| 13 Cauchy | `cert : CauchyRigidityCertificate` | CONDITIONAL |
| 35 five-color | `hG : FiveColorReducible G` | CONDITIONAL |
| 36 art gallery | `h : TriangulatedPolygon` | CONDITIONAL |

Order of attack = by how self-contained the missing math is. Ch20 first: its
algebraic heart (valuation extension via `IsLocalRing.exists_factor_valuationRing`,
Lemma 1 rainbow-area, Sperner parity engine) is ALREADY proved & unconditional.
Only Lemma 2's planar combinatorics remains.

---

## Chapter 20 — avenues

**Goal:** prove `∀ n, Odd n → ¬ ∃ dissection of [0,1]² into n equal-area
triangles`, faithful to arbitrary dissections (T-vertices allowed), reusing the
proved valuation + measure-bridge (`volume_convexHull_triangle`) machinery.

The book's Lemma 2 counts **atomic segments between consecutive vertices** and
uses "interior segment counted twice". The existing Lean engine counts FULL
triangle edges `triangleEdge : Fin 3 → Sym2 α`, which is the edge-to-edge
fragment. So a new atomic-segment front end is required. Five sub-facts:

- (E1) atomic-edge boundary list of a triangle = `consecutiveEdges` over each
  side subdivided at the dissection vertices lying on it.
- (E2) **[the wall]** each interior atomic edge lies on exactly 2 triangles'
  boundaries, each ∂-square atomic edge on exactly 1. (planar covering +
  disjoint interiors; reachable via `Wbtw`/`Sbtw` + `volume_convexHull_triangle`.)
- (E3) on any side, #red-blue atomic segments ≡ [endpoints are red&blue] (mod 2),
  from the ≤2-colors-per-line corollary (= `valuation_doubleArea_red_green_blue`
  + collinear⟹doubleArea=0).
- (E4) #red-blue corner-pairs of a triangle is odd ⟺ rainbow. (finite, decide.)
- (E5) bottom edge has odd atomic red-blue count, other 3 sides zero. (corner
  colors are fixed: (0,0)=red,(1,0)=green/blue per coloring; finite parity walk.)

(a) **Direct atomic engine.** Define `SquareDissection` (finite triangles,
    pairwise-disjoint interiors, ⋃closures = [0,1]²). Build E1,E3,E4,E5 (the
    finite/combinatorial 4) myself; grind E2 (geometry) as the focused single
    proof. Terminal success: `chapter20` re-stated over `SquareDissection`,
    0 sorry, `#print axioms` clean. Terminal failure: E2 needs a planar-graph
    Euler/Jordan fact with no Mathlib path AND no elementary betweenness proof
    after ≥3 concrete attempts (documented).

(b) **Measure-additivity engine for E2.** Instead of local covering, prove the
    sharing lemma by: for an atomic interior segment `s`, the two open
    half-disks at its midpoint are each covered (mod measure-zero) by exactly one
    triangle interior; use `volume_convexHull_triangle` + disjointness +
    covering to force exactly-2. Attack vector if (a)'s betweenness route stalls.

(c) **Refinement to a fan, parity-preserving.** Express each triangle's
    subdivided boundary via a canonical vertex order and prove the cancellation
    purely on the multiset of atomic `Sym2`-edges (combinatorial double count),
    deferring "exactly 2" to a single geometric incidence lemma stated minimally.

Fallback if all stall on E2: dispatch E2 alone to one Codex session on uisai1
as a bounded sub-goal ("prove this incidence lemma; close what you can, report
the exact tactic that blocks, no faking"), keep driving E1/E3/E4/E5 + the engine
wiring myself.

**Method-downgrade to edge-to-edge is NOT permitted** (fragment, fails audit) —
escalate to Xiang if E2 proves genuinely unreachable, do not silently weaken.

---

## Working rules (from /automode + playbook)

- Remote build only: `scripts/remote-build.sh proof_in_the_book [--file F]`.
  uisai1 is shared (≥9 codex sessions live) → I take hard single proofs with
  Opus, reserve ≤1 codex session for a bounded sub-task, never compete for the
  gpt-5.5 rate limit.
- One file, one writer. New work goes in `ProofsInTheBook/Chapter20Dissection.lean`;
  I wire imports + `#print axioms` myself.
- 0 sorry to commit. Each avenue → terminal verdict → commit.
- No time estimates, no choice questions mid-run, no abstractifying "needs infra"
  without concrete failing tactic, no naming-a-sorry-and-stopping.
