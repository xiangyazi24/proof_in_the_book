# SphericalFinish — §8.2–8.5 endgame substrate for `SZOpeningCore` (opus reply)

**Status: DELIVERED, clean compile, 0 sorry / 0 axiom / 0 admit / 0 native_decide.**
File: `ProofsInTheBook/SphericalFinish.lean` (343 lines, NEW, untracked on `main`, no commit per rules).
Imports `ProofsInTheBook.SphericalCore`; reuses the proven rotation engine + SZ + Core substrate.

**Honest headline.** `SZOpeningCore` is **NOT discharged unconditionally** this round. What is delivered:
the two genuinely-mechanizable §8 sub-facts the previous handoff flagged — **(a) the IVT realisation
law** and **(b) the tight-supremum sign-extraction machinery** — both proved unconditionally; the full
**derivation of three of `StuckData`'s seven fields** (the degenerate determinant + both Gram signs +
`firstSide`); and an honest **reduction of `SZOpeningCore` to a strictly-smaller geometric obligation
`OpeningData`** (sign-free, betweenness-form), composed all the way to `SchoenbergZarembaTarget`. The one
irreducible residue — the opening *construction* itself (convex-arm persistence + convex sub-arm) — is
isolated honestly, NOT faked, wrapped, or made vacuous.

## Verification (EXCLUSIVELY on uisai1 — nothing built/run locally; Mac kernel-panic rule honoured)

- `lake env lean ProofsInTheBook/SphericalFinish.lean` → EXIT 0, zero errors, zero warnings.
- `lake build ProofsInTheBook.SphericalFinish` → **Build completed successfully (8427 jobs).**
- `#print axioms` (from rebuilt oleans) on all 13 headline results → every one depends ONLY on
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `ofReduceBool`/native.
  Checked: `continuous_openedJointAngle`, `cos_openedJointAngle`, `openedJointAngle_surjOn(')`,
  `gramSigns_eq_coords`, `stuckSigns_of_between`, `stuckSigns_iff_between`, `nnreal_coords_of_mem_span`,
  `firstSide_of_equalSides`, `stuckData_of_between`, `szOpeningCore_of_openingData`,
  `schoenbergZaremba_of_openingData`, `openingData_membership_satisfiable`.
- `grep sorry|admit|axiom|native_decide` → none.
- Local and remote `SphericalFinish.lean` md5-identical (`fdd0b8a6…`). Temp audit file removed from server.
  Root `ProofsInTheBook.lean` untouched (not my file — see wiring note below).

## What is proved UNCONDITIONALLY (genuine new content above SphericalCore)

### (a) The opened-joint realisation (IVT surjectivity)
- `tangentTo_open_ne_zero` — the outgoing opened tangent stays nonzero for a short arc (`rot` isometry).
- `continuous_openedJointAngle` — `θ ↦ sphAngle p k (rotS2 k θ q)` is continuous, via
  `InnerProductGeometry.continuousAt_angle` + `tangentTo_rotS2_axis` + `continuous_rot`.
- `cos_openedJointAngle` — the opened joint cosine is the sinusoid
  `(cos θ·⟪u,w⟫ + sin θ·⟪u,k×w⟫)/(‖u‖·‖rot…‖)` (from `inner_tangent_opened` + `cos_angle`).
- `openedJointAngle_surjOn` / `openedJointAngle_surjOn'` — by `intermediate_value_Icc(')`, the opened
  joint angle **attains every value** between its endpoints on any admissible `[θ₀,θ₁]`. This is the
  realisation surjectivity the *reached* case needs (target joint angle is hit at some admissible θ).

### (b) The tight-supremum sign extraction (the flagged hard case — algebra fully closed)
- `gramSigns_eq_coords` — **the heart**: for a coplanar `A0 = s•A1 + t•qstar` (unit `A1,qstar`),
  `signA = s·‖A1×qstar‖²` and `signC = t·‖A1×qstar‖²` exactly (Lagrange `‖A1×qstar‖²=1−⟪A1,qstar⟫²`).
- `stuckSigns_of_between` — betweenness (`s,t ≥ 0`) ⟹ **both** Gram signs (`mul_nonneg`).
- `stuckSigns_iff_between` — for a short arc (`‖A1×qstar‖²>0`), `signA ⟺ s≥0` and `signC ⟺ t≥0` with
  **no slack**: the two Gram signs are *precisely* the convex-position betweenness. This pins down that
  the sign data is irreducible (equivalent to betweenness), confirming the previous round's assessment.
- `nnreal_coords_of_mem_span` — extracts nonnegative real coords from `span ℝ≥0` membership.

### (b→StuckData) Three of seven `StuckData` fields are PRODUCED, not assumed
- `firstSide_of_equalSides` — `sDist(B1)(B0)=sDist(A1)(A0)` is **forced by the equal-side hypothesis**
  (`sideLen A 0 = sideLen B 0` + `sDist_comm`).
- `stuckData_of_between` — assembles full `StuckData` from {betweenness membership, short arc, opening,
  subcomp} + equal sides: `det_zero` (via `det_zero_of_betweenness`), `signA`/`signC` (via §(b)),
  `firstSide` (via equal sides). Real derivation work.

### (c)+(d) Assembly and the strictly-smaller obligation
- `OpeningData : Prop` — the genuinely-missing opening **construction**, in sign-free geometric form.
  Strict branch carries only {`qstar`, `ShortArc (A1) qstar`, `A0 ∈ span ℝ≥0 {A1,qstar}`, opening bound,
  subcomp} ∨ direct strict. **Carries strictly less than `SZOpeningCore`** (3 `StuckData` fields shed).
- `szOpeningCore_of_openingData : OpeningData → SZOpeningCore` — the §8.2–8.5 bookkeeping reduction,
  routing the geometric output through `stuckData_of_between` (real work) and forwarding reached/cut.
- `schoenbergZaremba_of_openingData : OpeningData → SchoenbergZarembaTarget` — composed with the proven
  `schoenbergZaremba_of_openingCore`. So discharging `OpeningData` makes the **unconditional spherical
  arm lemma** (`spherical_arm_mono`/`_strict`) drop out.

## The single isolated residue (honest, after genuine exhaustion) — `OpeningData`

`OpeningData` packages the design §8 opening **construction**: the Rodrigues hinge to the admissible
supremum, **convexity persistence of the moved arm**, and the reach-or-stuck dichotomy *instantiated
as an actual convex sub-arm* (so IH `SZComparison n` applies, giving `subcomp`). Its analytic skeleton
is proved (the §(a) realisation here; `arm_reach_or_stuck`, side-length + orientation persistence in
`SphericalCore`). What remains is the **multi-vertex convex bookkeeping**: showing `openArm A θ` stays
a `StrictConvexSphArm` for admissible θ (all mixed-triple `edge_support`/`strict_nonincident` +
`open_hemisphere` for the opened arm) and that the dropped-first-vertex sub-arm is convex. That body is
several missing convexity-persistence theorems (design §8.3) — a substantial development, not a single
lemma, and not faithfully completable in one round.

**Why the sign content cannot be reduced further (genuine exhaustion of §(b)):** `stuckSigns_iff_between`
proves the two Gram signs are *equivalent* to betweenness (`s,t≥0`) — so any "sign-free" primitive must
still carry the betweenness membership, which is the same convex-position content. Deriving the signs
from raw *neighboring* `sOrient` constraints (the alternative the task names) requires locating `A0`
relative to the other vertices via the full convex chain — i.e. exactly the multi-vertex convexity
persistence that is the `OpeningData` residue. The signs are inseparable from that construction; the
**algebra** of the extraction (the iff, `signA=s‖cross‖²`) is what is closable, and it is closed.

## Non-vacuity / anti-impostor (playbook §3.3)
- `OpeningData`'s membership payload is satisfiable (`openingData_membership_satisfiable`); the bounds
  are free inequalities ⟹ not a vacuous-hypothesis impostor.
- `szOpeningCore_of_openingData` is a genuine reduction: it **produces** 3 of 7 `StuckData` fields, not
  a re-statement of its hypothesis. `OpeningData` is strictly smaller than `SZOpeningCore`.
- No `def : Prop` impostor for any *proved* goal; `OpeningData` is an honest named open obligation and
  is NOT claimed proved. `SZOpeningCore` itself is NOT proved (only reduced).

## Honest classification
- `tangentTo_open_ne_zero`, `continuous_openedJointAngle`, `cos_openedJointAngle`,
  `openedJointAngle_surjOn(')`, `gramSigns_eq_coords`, `stuckSigns_of_between`, `stuckSigns_iff_between`,
  `nnreal_coords_of_mem_span`, `firstSide_of_equalSides`, `stuckData_of_between`,
  `openingData_membership_satisfiable` : **FAITHFUL, UNCONDITIONAL** new content.
- `szOpeningCore_of_openingData`, `schoenbergZaremba_of_openingData` : **FAITHFUL** reductions
  (CONDITIONAL-honest chain links on the strictly-smaller `OpeningData`).
- `SZOpeningCore` : **OPEN** (reduced to `OpeningData`, not discharged).

## Wiring note (root file is not mine)
`SphericalFinish.lean` is NOT yet imported in `ProofsInTheBook.lean` (I own only my new file). To wire:
add `import ProofsInTheBook.SphericalFinish` after line 35 (`SphericalCore`). The module builds standalone
(8427 jobs) and `#print axioms` is clean from rebuilt oleans.

## Chapter 13's remaining frontier
1. **`OpeningData`** — the design §8.3 convex-persistence of the opened arm + the convex sub-arm
   construction (the multi-vertex bookkeeping), which together with this module's substrate
   (§(a) realisation, §(b) sign extraction, `arm_reach_or_stuck`, side/orientation persistence)
   discharges `SZOpeningCore` ⟹ `SchoenbergZarembaTarget` ⟹ the **unconditional spherical arm lemma**.
2. **The vertex-link correspondence** (design §9–§12): the Cauchy bridge identifying each convex-
   polyhedron vertex link with a `StrictConvexSphArm`, driving Cauchy's rigidity theorem.
