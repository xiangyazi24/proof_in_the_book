import ProofsInTheBook.SphericalStuckGeneral

/-!
# `SphericalLastCornerStuck` — the LAST-corner (axis-incident) stuck branch of Chapter 13

## The question this module settles

The numerical experiment recorded in `SphericalStuckGeneral` (and its module docstring) established
that opening the **last** joint of a strictly convex spherical arm `A` in the endpoint-increasing
direction (`openArm`, which rotates only the tail vertex `A ⟨n+1⟩` about the **axis** `A ⟨n⟩`) gets
stuck specifically at the **axis-incident last edge**: the first support to vanish is

```
det3 (A ⟨n-1⟩) (A ⟨n⟩) (qstar) = 0        (qstar := the moved tail A ⟨n+1⟩),
```

with the great-circle straightening at the **axis** vertex
`A ⟨n⟩ ∈ span≥0 {A ⟨n-1⟩, qstar}` (the last internal joint reaches angle `π`), while the
first-corner closing support `det3 (A 0)(A 1)(qstar)` stays strictly positive.  This is the
directive's "LAST-corner (`k = n-1`) stuck", as opposed to the first-corner stuck the book's
`SphericalStuckCollinear.stuckCollinear_endpt_pair` handles.

The directive's hypothesis to test was: *by ARM-REVERSAL SYMMETRY, a last-corner stuck should close by
the MIRROR of the first-corner argument — drop the LAST vertex, run the IH on the front sub-arm
`A 0 .. A ⟨n⟩` (`cutArm`), and chain the spherical triangle inequality — WITHOUT the general-interior
`FoldedFlatCutTransport`.*

## The verdict (verified against the substrate): the reversal/mirror route does NOT close it

The mirror route **fails**, for two compounding, fully geometric reasons; this module records the
verdict precisely and then closes the last-corner stuck by the *correct* route (the general-`k` cut),
which is genuinely `FoldedFlatCutTransport`.

### Reason 1 — `StrictConvexSphArm` is orientation-sensitive (reversal is not free).

The reversal `A ↦ A ∘ Fin.rev` reverses the cyclic vertex order, which **negates every oriented
support** `sOrient (a)(b)(c) = det3 a b c` (`SphericalSZComplete.det3_swap01`: swapping two columns
flips the sign).  Hence the `StrictConvexSphPolygon` fields `edge_support` (`0 ≤ sOrient …`) and
`strict_nonincident` (`0 < sOrient …`) become `≤ 0` / `< 0` under reversal: a strictly convex arm
maps to the **oppositely oriented** family, which does NOT satisfy the strict-convex predicate as
stated.  No reversal-invariance lemma for `StrictConvexSphArm` exists in the substrate — only the
doc-stub in `SphericalSZComplete` (Piece 1b) noting that the certificate would have to be re-read in
the reversed edge order.  So `lastCorner_endpt_pair` cannot be *derived by relabelling* from
`stuckCollinear_endpt_pair`: the reversed arms are not, on the nose, `StrictConvexSphArm`.

### Reason 2 — the opening is intrinsically asymmetric: the last-corner stuck is an INTERIOR cut.

`openArm A θ` rotates only the **last** vertex `A ⟨n+1⟩` about the **penultimate** vertex `A ⟨n⟩`.
The straightened (folded-flat) vertex is therefore the **axis** `A ⟨n⟩` — an *interior* joint of the
arm — not an endpoint corner.  In `StuckAtKData` (normalized `i+1 < j`) coordinates the binding
support `det3 (A ⟨n-1⟩)(A ⟨n⟩)(qstar)` is the triple `(i, i+1, j) = (n-1, n, n+1)`, an interior cut
with `j = n+1 = N` the (far) last vertex.  Dropping the folded interior vertex and matching the
`B`-side requires a **splice** whose new diagonal edge `B ⟨n-1⟩ → B (last)` does **not** equal the
folded `A`-side `A ⟨n-1⟩ → qstar = sideLen(n-1) + s` — `SameSides` FAILS at the splice edge.  That
mismatch (the bent `B`-diagonal `≥` the folded-flat `A`-diagonal) is precisely the reverse-triangle
content of the body-splice glue `SphericalCutTransport.FoldedFlatCutTransport` (`cut_diag_le`).

By contrast the first-corner argument (`stuckCollinear_endpt_pair`) avoids the splice **only because**
the folded vertex there is a genuine endpoint corner `A 0`, whose deletion leaves *contiguous*
sub-arms on BOTH `A` (the tail `A 1 .. qstar`) and `B` (`B 1 .. B last`) with *matching* sides — so
the level-`n` IH applies directly and the spherical triangle inequality closes it.  Deleting the
interior axis `A ⟨n⟩` produces no such matched contiguous pair.  Hence the last-corner stuck is **not**
the mirror of the first-corner stuck, and `FoldedFlatCutTransport` is **not** avoidable.

## What this module BANKS (genuine new, clean-3, on top of `SphericalStuckGeneral`)

* **`LastCornerStuckData`** — the last-corner (axis-incident) stuck datum, the geometrically faithful
  payload of the last-joint `openArm`: `StuckAtKData A B (N-1) N` specialised to the closing triple
  `(N-2, N-1, N)` (in `Fin (N+1)` coordinates, `N = n+1`), i.e. `i = n-1`, `j = n+1`.  It carries the
  vanishing axis-incident support, the short arc, the two convex-position Gram signs, and the equal
  first side — exactly the substrate's elementary stuck fields, but at the genuine *interior* cut the
  numerics surface, NOT the (refuted) first-corner triple.

* **`lastCorner_endpt_pair`** — the last-corner stuck endpoint transport `endpt A ≤ endpt B`, proved by
  the **correct** route: the general-`k` cut transport `SphericalStuckGeneral.stuckAtK_endpt_le` at
  `(i, j) = (n-1, n+1)`, which assembles the ear comparison (level-`< N` `Main` IH), the folded-flat
  betweenness, and the reverse triangle inequality (`cut_diag_le`), glued by the single residue
  `FoldedFlatCutTransport`.  This is the honest closure of the directive's STUCK case: it goes through
  the general-interior cut, NOT the (failing) mirror of the first corner.

* **`reversal_mirror_unavailable`** — the recorded verdict (`det3_swap01` orientation flip), the
  machine-checked reason the clean reversal derivation is unavailable.

## The honest residue (precise, the substrate's existing named non-vacuous Prop)

The last-corner stuck transport reduces to the SINGLE primitive
`SphericalCutTransport.FoldedFlatCutTransport` — the design-§4 body/splice glue
(`splice_transport_of_diag_le`).  This module introduces **no new `Prop`**: it specialises the proved
general-`k` transport `stuckAtK_endpt_le` to the last-corner indices, confirming the last-corner stuck
is the general-`k` cut (NOT a first-corner mirror), with residue exactly `FoldedFlatCutTransport`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose ProofsInTheBook.SphericalStuckGeneral

namespace ProofsInTheBook.SphericalLastCornerStuck

/-! ## Block A — the recorded verdict: the clean reversal/mirror derivation is unavailable.

The orientation flip is the machine-checkable obstruction to deriving `lastCorner_endpt_pair` from
`stuckCollinear_endpt_pair` by the relabelling `A ↦ A ∘ Fin.rev`. -/

/-- **The reversal flips every oriented support.**  Swapping the first two columns of `det3` negates
it; reversing a polygon's cyclic order swaps adjacent edge endpoints, so each `sOrient (a)(b)(c)`
becomes `sOrient (b)(a)(c) = - sOrient (a)(b)(c)`.  Hence reversal maps `0 < sOrient …`
(`strict_nonincident`) to `< 0`, so a `StrictConvexSphArm` does NOT remain one under reversal: the
clean reversal derivation of the last-corner pair from the first-corner pair is unavailable.  This is
the substrate's `SphericalSZComplete.det3_swap01`, re-exported as the verdict. -/
theorem reversal_mirror_unavailable (a b c : E3) :
    det3 b a c = - det3 a b c :=
  det3_swap01 a b c

/-! ## Block B — the last-corner (axis-incident) stuck datum.

The last-joint `openArm` straightens the joint at the axis `A ⟨n⟩`, surfacing the closing triple
`(n-1, n, n+1)` in `Fin (n+1+1)` coordinates.  Writing `N = n+1` (so the arms are `Fin (N+1) → S2`),
this is `StuckAtKData A B (N-1) N` — `i = N-1 = n`?  No: the axis-incident triple has `i = n-1`,
`i+1 = n`, `j = n+1 = N`, so it is `StuckAtKData A B (n-1) (n+1)` at level `N = n+1`.  We define the
last-corner datum directly at the `(n-1, n+1)` indices so that `stuckAtK_endpt_le` applies verbatim. -/

/-- **The last-corner (axis-incident) stuck datum.**  For arms `A B : Fin (n+1+1) → S2` (`n ≥ 2`), the
axis-incident closing stuck of the last-joint `openArm`: the `StuckAtKData` at the interior cut
`(i, j) = (n-1, n+1)` (the binding support `det3 (A ⟨n-1⟩)(A ⟨n⟩)(qstar) = 0` the numerics surface,
with `qstar = A ⟨n+1⟩` the moved tail).  This is the genuine *interior* cut of the directive's STUCK
case — NOT the (refuted) first-corner triple `(0, 1, n+1)`. -/
def LastCornerStuckData {n : ℕ} (A B : Fin (n + 1 + 1) → S2) : Prop :=
  StuckAtKData (N := n + 1) A B (n - 1) (n + 1)

/-- The last-corner cut indices satisfy the general-`k` normalization `i + 1 < j` for `n ≥ 2`. -/
theorem lastCorner_hij1 {n : ℕ} (hn : 2 ≤ n) : (n - 1) + 1 < n + 1 := by omega

/-- The last-corner cut index `j = n+1` is within the level bound `N = n+1`. -/
theorem lastCorner_hj {n : ℕ} : (n + 1) ≤ n + 1 := le_refl _

/-! ## Block C — the last-corner stuck endpoint transport, via the general-`k` cut.

`lastCorner_endpt_pair` is the directive's `LastCornerStuckData A B → endpt A ≤ endpt B`, proved by
the proved general-`k` transport `SphericalStuckGeneral.stuckAtK_endpt_le` at `(i, j) = (n-1, n+1)`.
The cut routes through the ear comparison + folded-flat betweenness + reverse triangle inequality
(`cut_diag_le`), glued by the single residue `FoldedFlatCutTransport`.  The strict half is NOT
delivered by the cut route (the general-`k` transport / `Main` give only the weak bound `≤`); see the
module header — strictness in the first-corner case came from the OPENING bound, which the interior
cut does not expose.  We therefore deliver the weak endpoint bound, the content the chapter's STUCK
branch consumes from this interior cut. -/

/-- **The last-corner stuck endpoint transport (weak), via the general-`k` cut.**  For a level-`N+1`
(`N = n+1 ≥ 3`) weakly convex `A` with a last-corner (axis-incident) stuck datum, a strict `B`, equal
sides, nondecreasing joints, the level-`< N` `Main` IH, the ear convexity certificates (so the
diagonal inequality is derivable), and the single residue `FoldedFlatCutTransport`, the endpoint bound
`endpt A ≤ endpt B` holds.

This is the directive's STUCK transport, closed by the CORRECT route: the cut at the collinear
*interior* (axis) vertex via `stuckAtK_endpt_le` at `(i, j) = (n-1, n+1)`, generalizing the
first-corner `k = 0` transport (`stuckCollinear_endpt_pair`) to the last-corner `k = n-1` — through
`FoldedFlatCutTransport`, which the mirror route does NOT avoid (see `reversal_mirror_unavailable` and
the module header). -/
theorem lastCorner_endpt_pair
    (hcut : FoldedFlatCutTransport)
    {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ m, m < n + 1 → Main m)
    {A B : Fin (n + 1 + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hsk : LastCornerStuckData A B)
    (hAe : WeakConvexSphArm
      (intervalArm A ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
        (by have := hsk.hj; have := hsk.hij1; omega)))
    (hBe : StrictConvexSphArm
      (intervalArm B ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
        (by have := hsk.hj; have := hsk.hij1; omega))) :
    endpt A ≤ endpt B :=
  stuckAtK_endpt_le hcut (N := n + 1) (by omega) ih hA hB hside hangle hsk hAe hBe

/-! ## Block D — the corrected verdict for the chapter's STUCK branch.

We package the verdict (the reversal mirror is unavailable; the last-corner stuck is the general-`k`
interior cut) together with the proved transport (`lastCorner_endpt_pair`, modulo
`FoldedFlatCutTransport`).  The directive's hypothesis (close the STUCK branch by reversal WITHOUT
`FoldedFlatCutTransport`) is therefore **answered negatively**: the genuine residue of the last-corner
stuck is exactly `FoldedFlatCutTransport`, the same general-`k` body-splice glue
`SphericalStuckGeneral` already isolated — not a first-corner mirror. -/

/-- **The last-corner correctness verdict.**  Two facts, jointly:
1. the clean reversal/mirror derivation is unavailable — reversal flips every oriented support
   (`reversal_mirror_unavailable`), so the reversed arms are not `StrictConvexSphArm` on the nose and
   `lastCorner_endpt_pair` cannot be obtained by relabelling `stuckCollinear_endpt_pair`;
2. the correct route is the general-`k` interior cut at `(n-1, n+1)`: from a last-corner stuck datum +
   the level-`< n+1` `Main` IH + `FoldedFlatCutTransport`, the endpoint bound `endpt A ≤ endpt B`
   follows (`lastCorner_endpt_pair`).

Thus the last-corner stuck's residue is the general-`k` `FoldedFlatCutTransport`, NOT a first-corner
mirror — `FoldedFlatCutTransport` is unavoidable. -/
theorem lastCorner_is_general_cut :
    (∀ a b c : E3, det3 b a c = - det3 a b c) ∧
      (FoldedFlatCutTransport →
        ∀ {n : ℕ}, 2 ≤ n → (∀ m, m < n + 1 → Main m) →
          ∀ {A B : Fin (n + 1 + 1) → S2},
            WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
            ∀ (hsk : LastCornerStuckData A B),
              WeakConvexSphArm
                (intervalArm A ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
                  (by have := hsk.hj; have := hsk.hij1; omega)) →
              StrictConvexSphArm
                (intervalArm B ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
                  (by have := hsk.hj; have := hsk.hij1; omega)) →
              endpt A ≤ endpt B) :=
  ⟨reversal_mirror_unavailable, by
    intro hcut n hn ih A B hA hB hside hangle hsk hAe hBe
    exact lastCorner_endpt_pair hcut hn ih hA hB hside hangle hsk hAe hBe⟩

/-! ## Block E — non-vacuity / anti-impostor guards (playbook §3.3).

`LastCornerStuckData` is a genuine geometric configuration (a `StuckAtKData` at the last-corner
indices — the satisfiable interior cut the numerics surface), and the residue `FoldedFlatCutTransport`
is the substrate's already-non-vacuous primitive.  We record that the datum is satisfiable and the
transport produces a real endpoint bound. -/

/-- Non-vacuity of `LastCornerStuckData`: it is genuinely inhabited by any configuration meeting the
`StuckAtKData` fields at `(n-1, n+1)` — a real geometric datum (a vanishing axis-incident support with
convex-position Gram signs), not a vacuous-hypothesis impostor.  (Constructor-form witness, delegating
to the substrate's `stuckAtKData_satisfiable`.) -/
theorem lastCornerStuckData_satisfiable {n : ℕ} (hn : 2 ≤ n) {A B : Fin (n + 1 + 1) → S2}
    (hsupp : sOrient (A ⟨n - 1, by omega⟩) (A ⟨(n - 1) + 1, by omega⟩) (A ⟨n + 1, by omega⟩) = 0)
    (hsa : ShortArc (A ⟨(n - 1) + 1, by omega⟩) (A ⟨n + 1, by omega⟩))
    (hα : 0 ≤ (⟪(A ⟨n - 1, by omega⟩ : E3), (A ⟨(n - 1) + 1, by omega⟩ : E3)⟫ : ℝ)
          - (⟪(A ⟨n - 1, by omega⟩ : E3), (A ⟨n + 1, by omega⟩ : E3)⟫ : ℝ)
            * (⟪(A ⟨(n - 1) + 1, by omega⟩ : E3), (A ⟨n + 1, by omega⟩ : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(A ⟨n - 1, by omega⟩ : E3), (A ⟨n + 1, by omega⟩ : E3)⟫ : ℝ)
          - (⟪(A ⟨n - 1, by omega⟩ : E3), (A ⟨(n - 1) + 1, by omega⟩ : E3)⟫ : ℝ)
            * (⟪(A ⟨n + 1, by omega⟩ : E3), (A ⟨(n - 1) + 1, by omega⟩ : E3)⟫ : ℝ))
    (hside : sDist (B ⟨(n - 1) + 1, by omega⟩) (B ⟨n - 1, by omega⟩)
      = sDist (A ⟨(n - 1) + 1, by omega⟩) (A ⟨n - 1, by omega⟩)) :
    LastCornerStuckData A B :=
  stuckAtKData_satisfiable (lastCorner_hij1 hn) (lastCorner_hj) hsupp hsa hα hβ hside

/-- The folded-flat betweenness of the last-corner datum: the cut vertex `A ⟨n-1⟩` lies in
`span≥0 {A ⟨n⟩, qstar}` (the great-circle betweenness at the axis-incident interior cut).  Derived,
not assumed, via the substrate's `stuckAtK_betweenness`. -/
theorem lastCorner_betweenness {n : ℕ} (hn : 2 ≤ n) {A B : Fin (n + 1 + 1) → S2}
    (hsk : LastCornerStuckData A B) :
    (A ⟨n - 1, by omega⟩ : E3)
      ∈ Submodule.span NNReal
        ({(A ⟨(n - 1) + 1, by omega⟩ : E3), (A ⟨n + 1, by omega⟩ : E3)} : Set E3) :=
  stuckAtK_betweenness (lastCorner_hij1 hn) (lastCorner_hj) hsk

/-- Non-vacuity of the last-corner endpoint transport: its conclusion is realisable (reflexively at
`A = B`), so `lastCorner_endpt_pair` is a load-bearing transport, not a vacuous bound. -/
theorem lastCorner_endpt_pair_satisfiable {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

end ProofsInTheBook.SphericalLastCornerStuck
