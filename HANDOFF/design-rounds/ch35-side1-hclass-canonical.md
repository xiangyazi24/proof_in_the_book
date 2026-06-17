# Ch35 side1_hclass_canonical — execution design (pbook3 wave-5, 2026-06-09, via tab paste)

## 1. Inventory verdict

The "trace orbit = kept orbit when avoiding swap points" lemma ALREADY EXISTS — do NOT rebuild.

- `ChordInnerTri.lean`: `SpliceUntouched β ρ a₀ a₁ k` (¬SameCycle to β a₀ and β a₁ under keptPhi)
  + `tracePhi_sameCycle_iff_keptPhi`.
- `ChordBoundaryOrbit.lean`: `spliceUntouched_of_face_ne_chordOrbits` — if the side face of
  `Sum.inl k` is neither fresh chord-dart face, then k is SpliceUntouched.

So `side1_hclass_canonical` is a SPECIALIZATION/GLUING lemma, not a new orbit induction.

## 2. Canonical anchor facts already landed

With a₀ = side₁Anchor₀, a₁ = side₁Anchor₁, hne = side₁Anchors_ne, β = data.sideAlpha₁ hsep,
ρ = data.sideSigma₁, τ = tracePhi β ρ a₀ a₁, S = data.sideMap₁ hsep a₀ a₁ hne:

- `ρ a₀ = keptPhi β ρ (face₁Dart₂ data)`, `ρ a₁ = face₁Dart₁ data`
- post-splice 2-cycle: `side₁Anchors_trace12`, `side₁Anchors_trace21`, `side₁Anchors_traceTwoCycle`
  (τ d₁ = d₂, τ d₂ = d₁). The OLD wrap `keptPhi d₂ = d₁` is FALSE (refuted in ChordSigmaContig).

## 3. Which fresh dart joins which orbit

- `Sum.inr 0` joins the face₁ trace orbit: `freshMap_phi_inl_b0 : φ (inl (β a₀)) = inr 0`, and
  τ (β a₀) = ρ a₁ = face₁Dart₁ ⟹ β a₀ ~τ face₁Dart₁.
- `Sum.inr 1` joins the side-1 outer boundary trace: `freshMap_phi_inl_b1 : φ (inl (β a₁)) = inr 1`,
  provided the outer-trace brick pins `S.dartFace (inr 1) = outerFace`.

## 4. Outer boundary trace = genuine repo `BoundaryCycle S outerFace`

ChordSideNT.ContiguousInterval consumes: outerFace, outerCycle : BoundaryCycle S outerFace,
outer_simple : VertexNodup, outer_len : 3 ≤ length.

Dart list shape: `[Sum.inl (β a₁), Sum.inr 1] ++ outerKeptArc.map Sum.inl` where outerKeptArc is
the kept boundary arc from ρ a₀ until just before returning to β a₁ under tracePhi/keptPhi.
Cyclic-walk obligations: φ(inl (β a₁)) = inr 1 (freshMap_phi_inl_b1), φ(inr 1) = inl (ρ a₀)
(freshMap_phi_inr_one), kept-arc steps inl kᵢ → inl kᵢ₊₁, last → inl (β a₁). BoundaryCycle fields
(normalized dart list, consecutive_phi, consecutive_vertex, arcSplit) per PlanarMapBoundary.lean.

Recommended structural bundle:

```lean
structure Side₁OuterTraceData (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Type u where
  outerFace      : S.Face                       -- S = canonical sideMap₁
  outerCycle     : BoundaryCycle S outerFace
  outer_simple   : outerCycle.VertexNodup
  outer_len      : 3 ≤ outerCycle.length
  chord1_is_outer : S.dartFace (Sum.inr 1) = outerFace
  face₁_not_outer : S.dartFace (Sum.inl (face₁Dart₁ data)) ≠ outerFace
```

## 5. Trichotomy classifier (optional diagnostic)

`inductive Side₁KeptClass ... | outer (dartFace (inl k) = outerFace) | face₁ (τ.SameCycle k
(face₁Dart₁ data)) | untouched (SpliceUntouched β ρ a₀ a₁ k)` with
`side₁_kept_trichotomy_canonical` by two by_cases; the no-hit step uses
`spliceUntouched_of_face_ne_chordOrbits` with
`S.dartFace (inl k) ≠ S.dartFace (inr 1)` (from hk_outer + chord1_is_outer) and
`S.dartFace (inl k) ≠ S.dartFace (inr 0)` (from hk_face₁ + bridge 6.1).

## 6. Required bridge lemmas

### 6.1 `side₁_chord0_face_eq_face₁_canonical`
`S.dartFace (Sum.inr 0) = S.dartFace (Sum.inl (face₁Dart₁ data))`
via `chordDart_face_eq_b0` (dartFace (inr 0) = dartFace (inl (β a₀))) then
τ.SameCycle (β a₀) (face₁Dart₁) via τ (β a₀) = ρ a₁ = face₁Dart₁, through
`sideFace_inl_eq_iff_tracePhi`.

### 6.2 `side₁Anchors_oneFresh_canonical` — THE one missing small brick
The indicator sum
`(if τ.SameCycle (face₁Dart₁) (β a₀) then 1 else 0) + (if τ.SameCycle (face₁Dart₁) (β a₁) then 1 else 0) = 1`.
First indicator positive (β a₀ in face₁ orbit, §3); second negative: β a₁ is in the outer orbit and
`out.face₁_not_outer` separates it. (`ZinanCh35SideAnchors.sideTracePhiTwoCycle_canonical` currently
takes `one_fresh` as input — this discharges it.)

### 6.3 `side₁_correctAnchor_face₁_canonical`
Direct call to `correctAnchorTwoCycle_ofFace₁` with `side₁Anchors_trace12/21`, `rfl`, and the new
oneFresh — produces `CorrectAnchorTwoCycle data hsep a₀ a₁ hne (S.dartFace (inl (face₁Dart₁ data)))`.

## 7. Master hclass lemma

```lean
theorem side1_hclass_canonical (data) (hsep) (out : Side₁OuterTraceData data hsep) :
    ∀ g : S.Face, g ≠ out.outerFace →
      (∃ k : {d : D // d ∉ data.keptDel₁}, S.dartFace (Sum.inl k) = g ∧
          M.dartFace k.1 ∈ data.side₁ ∧ M.dartFace k.1 ≠ data.face₁ ∧
          SpliceUntouched β ρ a₀ a₁ k)
        ⊕' CorrectAnchorTwoCycle data hsep a₀ a₁ hne g
```

Proof skeleton: `sideFace_has_inl_rep` gives k with S.dartFace (inl k) = g; by_cases on
τ.SameCycle k (face₁Dart₁).
- face₁ case → right; g = S.dartFace (inl face₁Dart₁) via sideFace_inl_eq_iff_tracePhi; transport
  6.3 across the equality.
- no-hit → left; hside via keptDart_face_side₁_or_outer (rule out M.outerFace from hg + outer trace;
  may add a rep-avoidance field to Side₁OuterTraceData if needed); hnotFace₁: if M.dartFace k.1 =
  data.face₁ then k ∈ {d₁,d₂} (face₁_two_kept_darts) contradicting ¬SameCycle via the trace 2-cycle;
  huntouched via spliceUntouched_of_face_ne_chordOrbits with the two face non-equalities (≠ inr 0
  from hface₁ + 6.1; ≠ inr 1 from hg + chord1_is_outer).

Result shape = exactly what `ChordAnchor.innerFacesSide₁NoCarve_of_classifier` /
`contiguousInterval_of_correctAnchor` consume.

## 8. Ordered sub-bricks

1. Notation block (worker 10–20)
2. `side₁_trace_beta_a0_to_face₁Dart₁` : τ (β a₀) = face₁Dart₁ (worker 15–25, from tracePhi_b0 + sideSigma₁_side₁Anchor₁)
3. `side₁_chord0_face_eq_face₁_canonical` (worker 25–45)
4. `Side₁OuterTraceData` bundle (worker 20–40)
5. `side₁Anchors_oneFresh_canonical` (worker 40–80)
6. `side₁_correctAnchor_face₁_canonical` (worker 10–20)
7. `Side₁KeptClass` + trichotomy (optional diagnostic 70–120)
8. `side1_hclass_canonical` (MASTER 100–180)
9. `contiguousInterval_canonical` assembler (15–30)

## 9. Degenerate-cut audit

len = 3 is VALID (one internal vertex + fresh chord dart = triangular outer side face). The bad case
is chord endpoints adjacent on the old boundary (outer cycle length 2, chord parallel to a boundary
edge) — excluded by proper-boundary-chord/separation hypotheses, NOT patched inside hclass. The
boundary API exposes it: in `BoundaryArcSplit`, an arc has an internal vertex iff the endpoint pair
is not a boundary edge. The outer-trace brick should require/derive `s(u,v) ∉ outerCycle.edges`
(equivalently `BoundaryPath.HasInternalVertex`), giving outer_len = keptArc.length + 1 ≥ 3.
Length/simplicity obligations belong to the OUTER TRACE brick, not hclass.
