# FFCT7 Consumer Audit — what the downstream actually requires, and whether hinj/hfirst/hlast are dischargeable at the consumption sites

Branch: `zinan-overnight`. All paths absolute-ish to `ProofsInTheBook/`. Read-only audit; no tracked file edited.

---

## 0. TL;DR of the structural verdict

`FoldedFlatCutTransport` is **universally quantified over all non-incident `(i,j)`** (def in
`SphericalCutTransport.lean:187`). To *prove* it (the FFCT3 dispatch at `ZinanFFCT3.lean:223`) one must
discharge `interior_excluded`/`planar_interior` at **every** interior pair — *including* the
counterexample pair `(i,j)=(0,n-1)` that killed `planar_interior`. So the falsity is real for the
*statement as proved*.

BUT the only place the **whole engine is consumed non-vacuously** is the single pair
`(i,j) = (n-1, n+1) = (N-1, N)` (the last-corner / axis-incident cut). At that pair the role of
`interior_excluded` is purely `exfalso` (contradict the vanishing support), and the available spherical
data is richer than the bare planar residue sees. **hinj is dischargeable; hlast is automatically true at
the consumed pair (j is the LAST vertex, on the last edge, not beyond it); hfirst is NOT needed at the
consumed pair at all.** The catch is that the engine as currently factored proves the *universal*
`PlanarWeakNoflatStrictEdgeCore`, so it still pulls in `hfirst` for the unused pairs unless the engine is
re-cut to the consumed-pair-only obligation (see §4).

---

## 1. The consumer DAG (file:line for every edge) — up to the Ch13 headline

Definition site:
- `SphericalCutTransport.lean:187` — `def FoldedFlatCutTransport` (∀ n, ∀ A B, ∀ i j non-incident, …).

Producers (anything `: … → FoldedFlatCutTransport`), all definitionally equal forms:
- `ZinanFFCT8.lean:257` `zinan_ch13_ffct_of_planar (Ch13PlanarConvexResidue) → FFCT`  ← the corrected/planar route
- `ZinanFFCT7.lean:198` `zinan_ch13_ffct_of_core (WeakNonflatStrictCore) → FFCT`
- `ZinanFFCT6.lean:149` `zinan_ffct_final (FoldWitnessData) → FFCT`
- `ZinanFFCT3.lean:223` `zinan_ffct_of_nondeg (FoldNonDegeneracy) → FFCT`  ← **the index dispatch lives here**
- `ZinanFFCT4.lean:210`, `ZinanFFCT.lean:176`, `SphericalFoldedFlatDischarge.lean:165` — alternate equal forms.

Consumers (functions taking `(hcut : FoldedFlatCutTransport)`), bottom → top:

1. `SphericalCutTransport.lean:237` `cut_branch_endpt_le` — feeds a *given* `(i,j)` + support + diag into `hcut`.
2. `SphericalCutTransport.lean:255` `cut_branch_endpt_le_exists` — same, with `(i,j)` existentially packaged (`hvanish : ∃ i j, …`). Line 269 destructs and calls `cut_branch_endpt_le`.
3. `SphericalStuckGeneral.lean:252` `stuckAtK_endpt_le` calls `cut_branch_endpt_le hcut … hsk.hsupp hdiag` at the cut `(i,j)` carried by `StuckAtKData A B i j` (`hij1 : i+1 < j`).
4. `SphericalStuckGeneral.lean:295` `general_cut_endpt_le_exists` → `cut_branch_endpt_le_exists`.
5. `SphericalLastCornerStuck.lean:187` `lastCorner_endpt_pair … := stuckAtK_endpt_le hcut (N := n+1) …` at the **fixed** indices `(i,j) = (n-1, n+1)` — `LastCornerStuckData A B := StuckAtKData (N:=n+1) A B (n-1) (n+1)` (`SphericalLastCornerStuck.lean:248` and the `def` at the same file).
6. `SphericalArmCleanReduction.lean:180` and `:358` `… := lastCorner_endpt_pair hcut … hisd.hsk …` — `InteriorStuckData` carries the `LastCornerStuckData` (`SphericalArmCleanReduction.lean:119-120`).
7. `SphericalOpeningGeneral.lean:174` `… := stuckAtK_endpt_le hcut (N := n+1) …` — `GeneralStuckData A B i j` route (also general, but instantiated to `(n-1,n+1)` per the module header line 12/317).
8. `SphericalOpeningDichotomy.lean:116` `deficientReachCollinearInterior_holds (LastJointOpeningInterior) : DeficientReachCollinearInterior` (the STUCK disjunct = `InteriorStuckData`, i.e. `StuckAtKData A B (n-1)(n+1)`; see header lines 33-40, 84).
9. Headline `SphericalOpeningDichotomy.spherical_arm_mono_of_opening` / `SphericalOpeningGeneral` kernel-arm lemmas (lines 133/147, 285/299) — conditional on **exactly** `FoldedFlatCutTransport + InteriorStuckStrict + (LastJointOpeningInterior | GeneralStuckStrict)` + `hMain`. This is the Ch13 §8.4 "spherical arm monotone" headline, the SZ induction step that ultimately drives the spherical Bricard/strict-convex conclusion. Residue accounting at `ChapterMinimalResidue.lean:163-167` confirms FFCT is one of the named residues threaded into the arm-mono headline.

### Spherical data in scope at the headline / consumption (item 5 site)
- Arms `A B : Fin (n+1+1) → S2`, i.e. `N = n+1`, vertices `0 … n+1`.
- `A` is **`WeakConvexSphArm`** only (relaxed from strict precisely so the stuck/folded `A` qualifies — `SphericalOpeningDichotomy.lean:52-54`, `InteriorStuckData.hAweak`). `B` is `StrictConvexSphArm`.
- `SameSides A B`, `JointLe A B`.
- The folded-flat config: `qstar := A ⟨n+1⟩` (moved tail), straightened (axis) vertex is the **interior** `A ⟨n⟩`, with `A ⟨n⟩ ∈ span≥0 {A ⟨n-1⟩, qstar}` (`SphericalLastCornerStuck.lean:10-18`). The endpoints in scope are `A 0` (head, fixed by `openTail`) and `A (n+1)=qstar` (the moved last vertex). `StrictConvexSphPolygon` data is on `B` only; on `A` it is `WeakConvexSphPolygon` (`SphericalSZInduction.lean:75-84`).

---

## 2. `FoldWitnessData.interior_excluded` — which `(i,j)` is actually invoked

Definition: `ZinanFFCT6.lean:98-103` (∀ non-incident `(i,j)` with `¬(i=0∧j=n)` and `¬(i=n-1∧j=0)`,
`0 < sOrient (A i)(A i+1)(A j)`).

**The single invocation site** is `ZinanFFCT6.lean:133`, inside `interior_vacuous_of_data`:
```
have hpos := hw.interior_excluded hn hA hB hside hangle i j hji hji1 hi1 hj hhead htail
rw [hsupp] at hpos; exact lt_irrefl 0 hpos          -- exfalso
```
So `interior_excluded` is used **solely to refute a vanishing support** (`exfalso`). The `(i,j)` it is
queried at is whatever `interior_vacuous` is called with, which comes through the FFCT3 dispatch
(`ZinanFFCT3.lean:225-228` case split: head `(0,n)` / tail `(n-1,0)` / **interior = everything else →
`interior_vacuous`**).

Because `FoldedFlatCutTransport` (and hence `FoldNonDegeneracy.interior_vacuous`) is **∀-quantified over all
non-incident `(i,j)`**, *proving* the engine forces `interior_excluded` (⇐ `planar_interior`) at **every**
interior pair, e.g. `(0, n-1)`, `(1, n)`, … — including the counterexample pair. That is why
`planar_interior`/`PlanarWeakNoflatStrictEdge` are false as universal statements.

**Where the engine is actually *consumed* non-vacuously**: only `(i,j) = (n-1, n+1) = (N-1, N)`
(item 5/6 above). At that single pair the support genuinely vanishes (`hsk.hsupp`), so
`interior_vacuous`'s `exfalso` fires there. Every other interior pair is touched *only* during the proof
of the universal, never by the SZ consumer.

---

## 3. Inventory of available facts at the consumed pair `(i,j)=(N-1,N)` and dischargeability of hinj/hfirst/hlast

Index translation into the planar residue `Fin (m+1)`, `m = N = n+1`:
- consumed edge `(i,i+1) = (n-1, n) = (m-1, m... no: i+1=n=m-1)` → edge `(m-2, m-1)` is wrong; carefully:
  `i = n-1 = m-2`, `i+1 = n = m-1`, `j = n+1 = m`.
- So the queried support is `0 < det3 (Q⟨m-2⟩)(Q⟨m-1⟩)(Q⟨m⟩)` — **the last edge `(m-1,m)` is NOT the support
  edge; the support edge is `(m-2,m-1)` (second-to-last) and the test vertex `j=m` is the LAST vertex.**
- The boundary exclusion `¬(i=n-1 ∧ j=0)` in `interior_excluded`/the planar core is NOT triggered (here `j=m≠0`).
- The head exclusion `(0,m)` is NOT this pair either.
- This is exactly the consecutive interior triple at `v = m-1`: `(Q(v-1),Q v,Q(v+1))` with `v = m-1 = n`.
  **So the consumed support coincides with the `GnomonicNoflatJoint` interior-joint triple** (gap-2 / consecutive),
  NOT a long-range diagonal.

Available spherical data beyond `WeakConvexSphArm A + StrictConvexSphArm B + SameSides + JointLe` at this site:
- (a) **Injectivity of A?** There is **no `Nodup`/`Injective` field** anywhere in the SZ chain (grep of
  `Injective|Nodup|distinct|Pairwise` over `Spherical*.lean`/`ZinanFFCT*.lean` returns only:
  `S2.coe_injective` (`SphericalKernel.lean:65`), `gidx_injective` (`SphericalMatchedCut.lean:198`),
  `Fin.castSucc_injective` (`SphericalDiagCut.lean:210`) — index/coercion injectivity, never arm-vertex
  injectivity). `WeakConvexSphPolygon.edge_short` (`SphericalSZInduction.lean:77`) gives only **adjacent**
  vertices distinct+non-antipodal (`ShortArc p q := p≠q ∧ p≠-q`, `SphericalKernel.lean:159`). Non-adjacent
  coincidence is NOT excluded by weak convexity — exactly the degeneracy the counterexample exploits.

  **However** `SphericalDiagCut.lean:67-81` (`ne_of_sOrient_pos_ac`, `not_antipodal_of_sOrient_pos_ac`) shows a
  **strict** support `0 < sOrient a b c ⟹ a≠c ∧ a≠-c`. The arm `A` carries `edge_support : 0 ≤ sOrient`
  everywhere (weak), so this gives distinctness only at pairs where the support is *strictly* positive — which is
  precisely what we are trying to prove, so it cannot bootstrap injectivity at the vanishing pair.

  **Verdict on hinj:** dischargeable for the *gnomonic image* via `gproj` injectivity on the open hemisphere
  (`gproj` is central projection; `open_hemisphere` gives `0<⟪h,A i⟫` for all i, `SphericalSZInduction.lean:79`,
  so `gproj h` is injective on `{A i}` **iff the `A i` are distinct**). The missing premise is the distinctness of
  the `A i` themselves, which weak convexity does NOT supply. So hinj is **NOT cleanly dischargeable from
  `WeakConvexSphArm` alone**; it would need either (i) a new arm invariant `Function.Injective A` threaded from
  the opening process, or (ii) restricting the engine to the consumed pair (§4) where it can be sidestepped.

- (b) **Datum at FIRST / LAST edge.** At the consumed pair the relevant edge is the **last** edge region:
  the test vertex is `j = m` (the genuine last vertex `A⟨n+1⟩ = qstar`), and the support edge is `(m-2,m-1)`.
  * `hlast` asks: no vertex on the *forward extension* of the last edge `(Q⟨m-1⟩, Q⟨m⟩)`. The test vertex
    `j = m` **IS the last vertex** `Q⟨m⟩` itself — it is the endpoint of the last edge, not a point *beyond* it
    (`t>0`). So `hlast` is vacuously satisfied at `j=m` (the offending pattern `f⟨j⟩ = f⟨n⟩ + t•(f⟨n⟩-f⟨n-1⟩)`
    with `t>0` is exactly "strictly beyond the last vertex", which `j=m` is not). **hlast is automatically true at
    the consumed pair.**
  * `hfirst` (no vertex on backward extension of the FIRST edge `(Q⟨0⟩,Q⟨1⟩)`) is about the *head* edge; the
    consumed pair never touches `i=0`. **hfirst is NOT needed at the consumed pair.** (The counterexample pair
    `(0,n-1)` that *does* need hfirst is never consumed.)
  * Boundary geometry actually available on A here: `A⟨n⟩ ∈ span≥0 {A⟨n-1⟩, qstar}` (the fold), `qstar` is the
    moved tail with matched side `sDist(B n)(B(n-1))…` (`StuckAtKData.hside`), `ShortArc (A⟨n⟩,qstar)` from
    `edge_short`. None of these is a vertex-distinctness fact for the *non-incident* vertex, so they do not by
    themselves give hinj; but they DO give hlast/hfirst for free as argued.

**Net §3 verdict:** at the genuinely-consumed pair `(N-1,N)`, **hfirst is irrelevant, hlast is automatic, and hinj
reduces to "A has distinct vertices" which the SZ chain does not currently certify.** The only true residual
extra-input is `hinj` (vertex-distinctness of A) — and even that is needed only to license the gnomonic transport,
not the cut logic.

---

## 4. Does consumption need the FULL strict non-incident support, or a subset?

**A strict subset suffices.** The cut engine is consumed at exactly one index family:
`(i,j) = (n-1, n+1) = (N-1, N)` (item 5/6; the "general-k" wrappers in `SphericalOpeningGeneral`/`StuckGeneral`
are stated generically but are *instantiated only* at `(n-1,n+1)` per `SphericalOpeningDichotomy.lean:33-40, 84`
and `SphericalOpeningGeneral.lean:12, 317`). The `interior_excluded` query there is the **single consecutive
interior triple at `v=N-1`**, i.e. the `GnomonicNoflatJoint` no-flat-joint fact at the penultimate joint — NOT
any long-range diagonal, and never the head-adjacent `(0,·)` pairs.

Therefore the corrected core could be cut down to:
> for the consumed pair only — equivalently for the **no-flat interior joint** `0 < det3(Q⟨v-1⟩)(Q⟨v⟩)(Q⟨v+1⟩)`
> at `v = N-1` (and, to be safe, all interior `v` that any future general-k instantiation might reach) —
> strict positivity.

This is **exactly `GnomonicNoflatJoint`** (`ZinanFFCT8.lean:182`), the no-flat residue, with **no need for the
diagonal/long-range `PlanarWeakNoflatStrictEdge` content at all**, and hence **no `hfirst`/`hlast`/`hinj`**:
the consecutive triple `(v-1,v,v+1)` is incident to the edge at both ends and never tests a far vertex on an
edge's extension. **If the engine is re-cut so that `FoldedFlatCutTransport` only has to discharge the support at
the actually-consumed `(N-1,N)` pair (or, conservatively, at all consecutive interior triples), then
`PlanarWeakNoflatStrictEdgeCore` and its three extra inputs `hinj/hfirst/hlast` can be dropped entirely**, and
the residue collapses to `GnomonicNoflatJoint` (interior-joint no-flatness) + `TailFoldBetweenness` (tail).

The blocker to doing this *today* is purely structural: `FoldedFlatCutTransport`'s `def` (`SphericalCutTransport.lean:187`)
and the FFCT3 dispatch are universally quantified, so the linchpin theorem `zinan_ffct_of_nondeg` literally
demands `interior_excluded` at all pairs. The fix is to **narrow `FoldNonDegeneracy.interior_vacuous` /
`FoldedFlatCutTransport`** to the consumed index family before plugging in the planar engine — a pure
restatement on the FFCT side, no spherical edit.

---

## 5. SUSPECT/SOUND verdict for `GnomonicNoflatJoint` and `TailFoldBetweenness`

### `GnomonicNoflatJoint` (`ZinanFFCT8.lean:182`) — **SUSPECT**
Statement: every interior gnomonic joint `0 < det3(Q⟨v-1⟩)(Q⟨v⟩)(Q⟨v+1⟩)`, `1 ≤ v ≤ n-1`.
Available exclusions (its own docstring lines 176-179): the spherical consecutive triple is `≥0` (weak edge
support) and `< π`-non-collinear via `jointAngle_lt_pi` (`ZinanFFCT3.lean:154`). But `jointAngle_lt_pi` excludes
only `sphAngle = π` (the *straight* joint). It does **NOT** exclude `sphAngle = 0` — the **doubled-back / fully
folded** joint where `A⟨v+1⟩` falls back onto the ray `A⟨v⟩→A⟨v-1⟩`. The docstring itself flags this:
"the only remaining exclusion is the doubled-back (`sphAngle=0`) collinear joint, which a weakly convex polygon
forbids (… a genuine convex-position fact …)" — i.e. it is *asserted*, not derived. A degenerate weakly convex
arm can have `sphAngle = 0` at an interior joint with `jointAngle = 0 < π` (so `JointLe` is still satisfiable
against a strict B with a positive joint), `edge_support ≥ 0` everywhere, and `open_hemisphere` holding, yet the
gnomonic det3 of the doubled-back triple is **0, not >0** (the three planar points are collinear).
**This is the SAME failure family as `planar_interior`**: a doubled-back/collinear local configuration satisfies
all hypotheses while violating the strict conclusion. `GnomonicNoflatJoint` is therefore **as suspect as the
original `planar_interior`** and must be audited for a `sphAngle=0` counterexample exactly the way
`planar_interior` was. (Note: this residue IS still required under the corrected route — it is the `noflat` field
of `Ch13PlanarConvexResidue`, `ZinanFFCT8.lean:210`, feeding `hnoflat` into the corrected engine
`ZinanFFCT8.lean:234-237`. And by §4 it is, in fact, the *only* residue the consumed pair really needs.)

Mitigating note: the doubled-back exclusion at an *interior* joint is plausibly recoverable from
`WeakConvexSphPolygon` (a flat fold seen as a negative support by SOME non-incident vertex would contradict
`edge_support ≥ 0`) — but that recovery is itself a non-incident convex-position argument that has **not been
formalized**, and whether it survives a vertex-coincidence degeneracy (where "some non-incident vertex" might be a
*repeated* vertex) is precisely the open question. So: **SUSPECT, pending the same doubled-back/coincident-vertex
audit.**

### `TailFoldBetweenness` (`ZinanFFCT8.lean:194`) — **SOUND (not strengthened; faithful re-export)**
Statement: when the *tail* support `sOrient(A⟨n-1⟩)(A⟨n⟩)(A⟨0⟩)=0` already vanishes, deduce `ShortArc(A⟨n-1⟩,A⟨0⟩)`
and two **nonneg** Gram coefficients (`0 ≤ …`). This is purely the convex-position betweenness data feeding
`ZinanFFCT5.tail_witness_of_betweenness_inputs`; it asserts **`≥ 0`, not `> 0`**, so the doubled-back/collinear
degeneracies (which produce *equalities*, i.e. `= 0`) are *inside* the conclusion's tolerance, not violations.
The short-arc is for the tail chord `A⟨n-1⟩→A⟨0⟩`, with the head/tail closing edge being the genuine boundary
fold; no strict orientation of a far vertex on an edge-extension is claimed. There is no "strict positive where a
degenerate config gives zero" gap. Moreover this pair `(n-1, 0)` is a *boundary* pair (the tail case of the FFCT3
dispatch, `ZinanFFCT3.lean:228`), handled by `tail_witness`, and it is **not** even reached by the
last-corner consumer (which lives at `(n-1,n+1)`, `j≠0`). **Verdict: SOUND** — same audit that killed
`planar_interior` does NOT apply (nonneg conclusion, betweenness not strict-orientation).

---

## 6. Summary table

| input / residue | consumed pair `(N-1,N)`? | dischargeable there? | from what |
|---|---|---|---|
| `hinj` (planar image injective) | yes (for gnomonic transport) | **only if A's vertices distinct** — NOT supplied by `WeakConvexSphArm` | would need new `Function.Injective A` arm invariant; `edge_short` gives adjacent-only |
| `hfirst` (no vtx on backward ext. of FIRST edge) | **no** (pair never touches `i=0`) | **not needed** | n/a |
| `hlast` (no vtx on forward ext. of LAST edge) | yes | **automatic** | test vertex `j=N` **is** the last vertex (`t=0`, not `t>0`) |
| `GnomonicNoflatJoint` | yes — IS the consumed triple | **SUSPECT** | `jointAngle_lt_pi` kills `sphAngle=π` but not `sphAngle=0` (doubled-back); exclusion asserted, not proved |
| `TailFoldBetweenness` | no (tail/boundary pair `(n-1,0)`) | **SOUND** | nonneg (`≥0`) conclusion + betweenness; degeneracies are within tolerance |

