# Ch35 canonical side-1 hclass — bricks 1–6 report

**Worker:** Opus Lean worker
**File:** `ProofsInTheBook/ZinanCh35HclassCanonical.lean` (NEW; no other file touched)
**Verification:** uisai2 build server, `lake env lean` — **0 errors**, all `#print axioms` clean-3
(`[propext, Classical.choice, Quot.sound]` only). No `sorry`/`admit`/`axiom`/`native_decide`.

## CRITICAL FINDING — work already landed

Bricks 1–8 of this exact design are **already implemented and committed** in a sibling module
`ProofsInTheBook/ZinanCh35Hclass.lean` (commit `b7dffcc`, "Ch35 hclass CLOSED (8 bricks,
clean-3 x6) … [Opus worker, independently verified]"). That commit is present on BOTH the Mac and
uisai2.

- Mac HEAD `7dc7392` (one handoff-doc commit ahead of uisai2 HEAD `75a443f`; `75a443f` is a
  strict ancestor of `7dc7392`). The handoff commit message lists "Ch35 hclass bricks 1-6" as
  next work, but that is **stale** — the work landed in `b7dffcc`, which is already in the tree.
- My brief's claim "uisai2 HEAD 75a443f, same as Mac" is no longer accurate: the Mac advanced by
  one doc-only commit.

I produced the requested deliverable file anyway (`ZinanCh35HclassCanonical.lean`, own namespace
`ProofsInTheBook.ZinanCh35HclassCanonical`) implementing bricks 1–6 independently, reusing the
verified landed signatures. It compiles clean-3 on its own. It does NOT collide with
`ZinanCh35Hclass.lean` (distinct namespace, distinct file).

## Statements proven (all in namespace `ProofsInTheBook.ZinanCh35HclassCanonical`)

Abbrev: `β = data.sideAlpha₁ hsep`, `ρ = data.sideSigma₁`, `a₀/a₁ = side₁Anchor₀/₁ data hsep`,
`hne = side₁Anchors_ne data hsep`, `S = data.sideMap₁ hsep a₀ a₁ hne`, `τ = tracePhi β ρ a₀ a₁`.

- **Brick 2** `side₁_trace_beta_a0_to_face₁Dart₁` : `τ (β a₀) = face₁Dart₁ data`.
  Plus orbit form `side₁_betaA0_sameCycle_face₁Dart₁` : `τ.SameCycle (β a₀) (face₁Dart₁)`.
  Proof: `tracePhi_b0` (needs `β*β=1` via `sideAlpha₁_involutive`) + `sideSigma₁_side₁Anchor₁`.
- **Brick 3** `side₁_chord0_face_eq_face₁_canonical` : `S.dartFace (inr 0) = S.dartFace (inl
  (face₁Dart₁ data))`. Proof: `sideMap₁_chordDart_face_eq_b0` rewrites `inr 0 → inl (β a₀)`, then
  `(sideFace_inl_eq_iff_tracePhi …).2` with brick-2 SameCycle.
- **Brick 4** `Side₁OuterTraceData data hsep : Type u` — the DATA bundle, fields **exactly** per
  design §4: `outerFace`, `outerCycle : BoundaryCycle S outerFace`, `outer_simple :
  outerCycle.VertexNodup`, `outer_len : 3 ≤ outerCycle.length`, `chord1_is_outer : S.dartFace
  (inr 1) = outerFace`, `face₁_not_outer : S.dartFace (inl (face₁Dart₁ data)) ≠ outerFace`.
  (No instance constructed — that is a later brick, by design.)
- **Brick 5** `side₁Anchors_oneFresh_canonical (out : Side₁OuterTraceData data hsep)` : the
  indicator sum
  `(if τ.SameCycle (face₁Dart₁) (β a₀) then 1 else 0) + (if τ.SameCycle (face₁Dart₁) (β a₁) then
  1 else 0) = 1`. First indicator true via brick-2 `.symm`; second false via
  `sideFace_inl_eq_iff_tracePhi` + `chordDart_face_eq_b1` + `out.chord1_is_outer` contradicting
  `out.face₁_not_outer`.
- **Brick 6** `side₁_correctAnchor_face₁_canonical (out : Side₁OuterTraceData data hsep)` :
  `CorrectAnchorTwoCycle data hsep a₀ a₁ hne (S.dartFace (inl (face₁Dart₁ data)))`. Direct
  `correctAnchorTwoCycle_ofFace₁` with `side₁Anchors_trace12`, `side₁Anchors_trace21`, `hkf=rfl`,
  brick 5.

## Signature deltas vs the design

1. **Brick 3 uses the data-level wrapper `sideMap₁_chordDart_face_eq_b0`** (`ChordBoundaryOrbit`,
   line 357), not the raw `chordDart_face_eq_b0`. The wrapper is stated directly on
   `data.sideMap₁` (the design named the raw `freshMap` lemma). The raw one would also work
   defeq, but the wrapper is the clean match.
2. **Brick 5's b1 face bridge IS available as a landed lemma** — `chordDart_face_eq_b1`
   (`ChordFaceCount`/`ChordBoundaryOrbit`, line 113) exists; no local b1 analogue needed. It
   applies to `data.sideMap₁ …` directly (defeq `freshMap …`).
3. **Indicator orientation** in bricks 5/6 is `face₁Dart₁` vs `(β a₀, β a₁)` in that argument
   order — matches BOTH `sideTracePhiTwoCycle_canonical`'s `one_fresh` input
   (`ZinanCh35SideAnchors`, lines 247–252) AND `correctAnchorTwoCycle_ofFace₁`'s `one_fresh`
   (`ChordAnchor`, lines 359–363). Verified identical.
4. **Brick 4 omits any `inner_reps` field.** The design §4 lists six fields and this worker's
   scope (bricks 1–6) needs none beyond those — brick 6 only consumes `chord1_is_outer` and
   `face₁_not_outer`. (The committed `ZinanCh35Hclass.lean` added an `inner_reps :
   InnerRepsAvoidBoundary …` field, but that is needed only for brick 7's master classifier, which
   is out of scope here. My §4 bundle matches the design literally.)

## Blocked items

None. Bricks 1–6 fully closed, clean-3.

## Build invariant note

`ZinanCh35SideAnchors.olean` was absent on uisai2; I ran
`lake build ProofsInTheBook.ZinanCh35SideAnchors` (8467 jobs, clean) before compiling, then
`lake env lean ProofsInTheBook/ZinanCh35HclassCanonical.lean`. No commit made (per instructions).
