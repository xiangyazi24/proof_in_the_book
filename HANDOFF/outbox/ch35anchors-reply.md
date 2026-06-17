# Ch35 ContiguousInterval — canonical side-anchor bricks: DELIVERED

**File:** `ProofsInTheBook/ZinanCh35SideAnchors.lean` (NEW, sole writer; no other edits, no git).
**Verify:** `lake env lean ProofsInTheBook/ZinanCh35SideAnchors.lean` on uisai2 — 0 errors.
**Axioms:** all 9 audited decls = clean-3 `{propext, Classical.choice, Quot.sound}`. No
`sorry`/`axiom`/`admit`/`native_decide`. Deps built first
(`lake build ProofsInTheBook.ChordSigmaContig ProofsInTheBook.ZinanCh35Gates` — clean).

## Crucial finding before coding (read this)

The design round's anchor prescription `a₀ = sideSigma₁.symm (keptPhi d₂)`,
`a₁ = sideSigma₁.symm d₁` is CORRECT and consistent with the repo, **but** the design's
adjacent phrasing `keptPhi_face₁Dart₁ : keptPhi d₁ = d₂` plus an implied wrap
`keptPhi d₂ = d₁` is only HALF right. `ChordSigmaContig.lean` already PROVES UNCONDITIONALLY
that **`keptPhi d₂ ≠ d₁`** (`keptPhi_face₁Dart₂_ne_face₁Dart₁`): `keptPhi d₂` sits at vertex
`u = tail dart`, `d₁ = M.φ dart` at `v = head dart`, `u ≠ v`. The literal `keptPhi`-bigon
wrap is FALSE; `ChordBigonWrap`/`ChordCapData` are proven `IsEmpty`. The genuine residue is
the **post-splice** `tracePhi` 2-cycle (`SideTracePhiTwoCycle`), which crosses `u ↔ v`
through the spliced fresh chord edge.

The canonical anchors still work because they use `keptPhi d₂` as a *value* and `d₁` as a
*dart* — two genuinely distinct kept darts (distinct precisely because `keptPhi d₂ ≠ d₁`).
So I built distinctness FROM that proven inequality, and supplied the `tracePhi` 2-cycle
(not a `keptPhi`-wrap).

## Bricks delivered

**Brick 1 — canonical anchors + equations (all clean-3):**
- `side₁Anchor₀ := sideSigma₁.symm (keptPhi d₂)`, `side₁Anchor₁ := sideSigma₁.symm d₁`.
- `sideSigma₁_side₁Anchor₀ : sideSigma₁ a₀ = keptPhi d₂` (`@[simp]`, `Equiv.apply_symm_apply`).
- `sideSigma₁_side₁Anchor₁ : sideSigma₁ a₁ = d₁` (`@[simp]`).
- `side₁Anchors_ne : a₀ ≠ a₁` — from `keptPhi d₂ ≠ d₁` + injectivity of `.symm`.

**Brick 2 — anchor-incidence (clean-3):**
- `keptPhi_sameCycle_d₁_keptPhi_d₂ : keptPhi.SameCycle d₁ (keptPhi d₂)` — `d₁ → d₂ → keptPhi d₂`
  is a `keptPhi`-walk (`keptPhi_face₁Dart₁` + one forward step).
- `side₁AnchorsShareFace_canonical : ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁`
  (= `keptPhi.SameCycle (keptPhi d₂) d₁`). This is exactly the fact-2 input
  `ChordSideNT.side₁_sphere_unconditional` / `ChordDisk.side₁_isSphereMap_of_disk` consume,
  now SUPPLIED for the canonical anchors.

**Brick 3 — post-splice `tracePhi` 2-cycle (clean-3, FULL — both directions closed):**
- `side₁Anchors_trace21 : tracePhi a₀ a₁ d₂ = d₁` (the easy swap-left: `swap (keptPhi d₂) d₁`
  sends `keptPhi d₂ ↦ d₁`).
- `side₁Anchors_trace12 : tracePhi a₀ a₁ d₁ = d₂` (`keptPhi d₁ = d₂`, then swap fixes `d₂`
  since `d₂ ∉ {keptPhi d₂, d₁}` via `keptPhi_face₁Dart₂_ne_self` + `face₁Dart_distinct`).
- `side₁Anchors_traceTwoCycle` — the pair.
- `sideTracePhiTwoCycle_canonical` — packaging into `ChordSigmaContig.SideTracePhiTwoCycle`
  with `trace12`/`trace21` SUPPLIED; takes the rep face `f`, `hkf`, `one_fresh` as inputs.

## The one honest residue (not blocked, scoped out by design)

`SideTracePhiTwoCycle` has 5 fields beyond the anchors: `trace12`, `trace21` (both DONE
canonically here) and `f`, `hkf`, `one_fresh`. The latter three are splice-orbit data on
the ASSEMBLED `sideMap₁` (its `dartFace`/`SameCycle` on the fresh darts) — they are not
pinnable from the `tracePhi` permutation algebra alone, exactly as the task anticipated
("the full two-cycle incl. one_fresh indicator may need the orbit-reduction"). They are the
next downstream brick (the splice-orbit reduction / `hclass` trichotomy in the design), not a
defect of the anchor layer. `sideTracePhiTwoCycle_canonical` is the seam: feed those three in
and the canonical post-splice residue threads into
`ChordSigmaContig.correctAnchorTwoCycle_ofTrace → face₁_sideTriangle_ofTrace →
contiguousInterval_ofTrace → ContiguousInterval`.

## Faithfulness (§3.3)

No vacuity: `side₁AnchorsShareFace_canonical` and the 2-cycle are PROVED for the concrete
canonical anchors over genuine surgery darts (not conditional on a hypothesis). The
distinctness rests on the kernel-confirmed geometric fact `keptPhi d₂ ≠ d₁`, so the anchors
are genuinely two darts and the swap genuinely acts. No field weakened; `Side₁AnchorsShareFace`
is the verbatim `ChordDisk` def (the SameCycle the disk/sphere machinery consumes).
