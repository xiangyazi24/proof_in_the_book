[BRIDGE_WARNING] Likely truncated capture. The server rejected this text 3 times as intro-only or short (reasons: intro_preamble_short; last elapsed: 617s); the extension force-finalized at the kickback cap. The full ChatGPT answer is likely still visible in the browser tab — paste the actual reply back manually if you need the complete response.

---

1. Inventory verdict

The needed “trace orbit = kept orbit when avoiding swap points” lemma already exists. Do not rebuild it.

In ChordInnerTri.lean:

def SpliceUntouched (β ρ : Equiv.Perm K) (a₀ a₁ k : K) : Prop :=
  ¬ (keptPhi β ρ).SameCycle k (β a₀) ∧
  ¬ (keptPhi β ρ).SameCycle k (β a₁)

lemma tracePhi_sameCycle_iff_keptPhi ...


This says that on a SpliceUntouched orbit, tracePhi and keptPhi have the same cycle relation. 

ChordInnerTri

 

ChordInnerTri

Even better, ChordBoundaryOrbit.lean already has the stronger worker you want for the “neither touched orbit” case:

theorem spliceUntouched_of_face_ne_chordOrbits ...


It says: if the side face of Sum.inl k is neither fresh chord-dart face, then k is SpliceUntouched. 

ChordBoundaryOrbit

So side1_hclass_canonical should be a specialization/gluing lemma, not a new orbit induction.

2. Canonical anchor facts already landed

For canonical side-1 anchors:

a₀ = side₁Anchor₀ data hsep
a₁ = side₁Anchor₁ data hsep
hne = side₁Anchors_ne data hsep
β = data.sideAlpha₁ hsep
ρ = data.sideSigma₁
τ = tracePhi β ρ a₀ a₁
S = data.sideMap₁ hsep a₀ a₁ hne


you already have:

ρ a₀ = keptPhi β ρ (face₁Dart₂ data)
ρ a₁ = face₁Dart₁ data


and the anchor inequality follows from the proved refutation of the false old wrap keptPhi d₂ = d₁. 

ZinanCh35SideAnchors

You also have the true post-splice 2-cycle:

τ (face₁Dart₁ data) = face₁Dart₂ data
τ (face₁Dart₂ data) = face₁Dart₁ data


as side₁Anchors_trace12, side₁Anchors_trace21, and side₁Anchors_traceTwoCycle. 

ZinanCh35SideAnchors

This is crucial: ChordSigmaContig explicitly says the old keptPhi d₂ = d₁ route is false; the real residue is the post-splice tracePhi 2-cycle. 

ChordSigmaContig

3. Which fresh dart joins which orbit

For the canonical anchors, the intended orientation is:

Sum.inr 0  joins the face₁ trace orbit.
Sum.inr 1  joins the side-1 outer boundary trace.


Reason:

freshMap_phi_inl_b0 says the side face has

φ (Sum.inl (β a₀)) = Sum.inr 0


and freshMap_phi_inl_b1 says

φ (Sum.inl (β a₁)) = Sum.inr 1.


The face-projection machinery identifies Sum.inr 0 with the τ-orbit of β a₀, and Sum.inr 1 with the τ-orbit of β a₁. 

ChordFaceCount

 

ChordBoundaryOrbit

Now, with canonical anchors,

τ (β a₀) = ρ a₁ = face₁Dart₁ data


so β a₀ lies in the same τ-orbit as face₁Dart₁; hence Sum.inr 0 joins the chord-triangle face. The other fresh dart, Sum.inr 1, is therefore the outer chord dart, provided the outer-trace brick pins

S.dartFace (Sum.inr 1) = outerFace.


That is the exact “one fresh chord dart closes face₁; the other closes the side outer boundary” split.

4. Outer boundary trace definition

The side-1 outer face should be phrased as a genuine repo BoundaryCycle:

BoundaryCycle S outerFace


because ChordSideNT.ContiguousInterval consumes exactly:

outerFace   : S.Face
outerCycle  : BoundaryCycle S outerFace
outer_simple : outerCycle.VertexNodup
outer_len    : 3 ≤ outerCycle.length


ChordSideNT

The concrete dart list should have the shape:

[Sum.inl (β a₁), Sum.inr 1] ++ outerKeptArc.map Sum.inl


where outerKeptArc is the kept boundary arc beginning at ρ a₀ and ending immediately before returning to β a₁ under tracePhi / keptPhi.

The cyclic-walk obligations are:

φ (Sum.inl (β a₁)) = Sum.inr 1
φ (Sum.inr 1)      = Sum.inl (ρ a₀)
φ (Sum.inl kᵢ)     = Sum.inl kᵢ₊₁   along the kept arc
φ (Sum.inl k_last) = Sum.inl (β a₁)


The first two are already generic fresh-map lemmas: freshMap_phi_inl_b1 and freshMap_phi_inr_one. 

ChordFaceCount

The final object must fill the BoundaryCycle fields: normalized dart list, vertices/edges by map tail/map dartEdge, consecutive_phi, consecutive_vertex, and arcSplit. The structure definition is in PlanarMapBoundary.lean. 

PlanarMapBoundary

Recommended local structure:

structure Side₁OuterTraceData
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Type u where
  outerFace :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).Face

  outerCycle :
    BoundaryCycle
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep))
      outerFace

  outer_simple : outerCycle.VertexNodup
  outer_len : 3 ≤ outerCycle.length

  chord1_is_outer :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) = outerFace

  face₁_not_outer :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) ≠ outerFace


This is cleaner than forcing side1_hclass_canonical to construct the entire boundary cycle internally.

5. The trichotomy type

Use a small inductive classifier:

inductive Side₁KeptClass
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (outerFace :
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).Face)
    (k : {d : D // d ∉ data.keptDel₁}) : Prop where

  | outer :
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl k) = outerFace →
      Side₁KeptClass data hsep outerFace k

  | face₁ :
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
          k (face₁Dart₁ data) →
      Side₁KeptClass data hsep outerFace k

  | untouched :
      SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) k →
      Side₁KeptClass data hsep outerFace k


Then prove the master no-hit trichotomy:

theorem side₁_kept_trichotomy_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (out : Side₁OuterTraceData data hsep)
    (k : {d : D // d ∉ data.keptDel₁}) :
    Side₁KeptClass data hsep out.outerFace k := by
  classical
  -- by_cases hk_outer : S.dartFace (Sum.inl k) = out.outerFace
  -- · exact .outer hk_outer
  -- by_cases hk_face₁ : τ.SameCycle k (face₁Dart₁ data)
  -- · exact .face₁ hk_face₁
  -- · prove untouched using spliceUntouched_of_face_ne_chordOrbits


The no-hit step should use:

spliceUntouched_of_face_ne_chordOrbits


with the two non-equalities:

S.dartFace (Sum.inl k) ≠ S.dartFace (Sum.inr 1)
S.dartFace (Sum.inl k) ≠ S.dartFace (Sum.inr 0)


The first follows from hk_outer and out.chord1_is_outer.

The second follows from hk_face₁ plus the lemma:

S.dartFace (Sum.inr 0) = S.dartFace (Sum.inl (face₁Dart₁ data))


which is the canonical “fresh 0 joins face₁” bridge.

6. Required bridge lemmas
6.1 Fresh dart 0 is the face₁ fresh dart
lemma side₁_chord0_face_eq_face₁_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    let a₀ := side₁Anchor₀ data hsep
    let a₁ := side₁Anchor₁ data hsep
    let hne := side₁Anchors_ne data hsep
    let S := data.sideMap₁ hsep a₀ a₁ hne
    S.dartFace (Sum.inr 0) = S.dartFace (Sum.inl (face₁Dart₁ data)) := by
  classical
  -- Use chordDart_face_eq_b0:
  --   dartFace (inr 0) = dartFace (inl (β a₀))
  -- Then prove τ.SameCycle (β a₀) (face₁Dart₁ data)
  -- via τ (β a₀) = ρ a₁ = face₁Dart₁.


The needed generic facts are already present: chordDart_face_eq_b0 and sideFace_inl_eq_iff_tracePhi. 

ChordBoundaryOrbit

 

ChordBoundaryOrbit

6.2 Canonical one-fresh indicator

If not already landed, add:

theorem side₁Anchors_oneFresh_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (out : Side₁OuterTraceData data hsep) :
    ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
          (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) then 1 else 0)
      + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
          (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) then 1 else 0)) = 1 := by
  classical
  -- first indicator positive: β a₀ is in face₁ orbit.
  -- second indicator negative: β a₁ is in outer orbit, and out.face₁_not_outer separates it.


This is the only small thing I do not see fully landed: ZinanCh35SideAnchors packages sideTracePhiTwoCycle_canonical, but it still takes one_fresh as an input. 

ZinanCh35SideAnchors

6.3 Correct-anchor datum for the face₁ side face
noncomputable def side₁_correctAnchor_face₁_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (out : Side₁OuterTraceData data hsep) :
    CorrectAnchorTwoCycle data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)
      ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))) :=
  correctAnchorTwoCycle_ofFace₁ data hsep
    (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep)
    _
    (side₁Anchors_trace12 data hsep)
    (side₁Anchors_trace21 data hsep)
    rfl
    (side₁Anchors_oneFresh_canonical data hsep out)


CorrectAnchorTwoCycle is exactly the structure expected by the downstream classifier. 

ChordAnchor

7. Master hclass lemma

This is the actual drop-in for contiguousInterval_ofTrace / contiguousInterval_of_correctAnchor.

theorem side1_hclass_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (out : Side₁OuterTraceData data hsep) :
    ∀ g :
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).Face,
      g ≠ out.outerFace →
        (∃ k : {d : D // d ∉ data.keptDel₁},
            (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).dartFace (Sum.inl k) = g ∧
            M.dartFace k.1 ∈ data.side₁ ∧
            M.dartFace k.1 ≠ data.face₁ ∧
            SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁
              (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) k)
          ⊕'
        CorrectAnchorTwoCycle data hsep
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep) g := by
  classical
  intro g hg
  obtain ⟨k, hkf⟩ :=
    ChordFaceClass.sideFace_has_inl_rep data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep) g

  by_cases hface₁ :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        k (face₁Dart₁ data)

  · -- face₁ case
    right
    -- first show g = S.dartFace (Sum.inl face₁Dart₁)
    -- from hkf and sideFace_inl_eq_iff_tracePhi.
    -- then transport side₁_correctAnchor_face₁_canonical across that equality.

  · -- no-hit case
    left
    refine ⟨k, hkf, ?hside, ?hnotFace₁, ?huntouched⟩

    -- hside:
    -- use keptDart_face_side₁_or_outer; rule out M.outerFace from hg + out.outerFace trace.
    -- or make this part of Side₁OuterTraceData as a rep-avoidance field if needed.

    -- hnotFace₁:
    -- if M.dartFace k.1 = data.face₁, then k is d₁ or d₂,
    -- hence hface₁ contradiction using side₁Anchors_traceTwoCycle / face₁_two_kept_darts.

    -- huntouched:
    -- use spliceUntouched_of_face_ne_chordOrbits.
    -- Need:
    --   S.dartFace (Sum.inl k) ≠ S.dartFace (Sum.inr 0)
    --   S.dartFace (Sum.inl k) ≠ S.dartFace (Sum.inr 1)
    -- First from hface₁ + chord0_face_eq_face₁.
    -- Second from hg + out.chord1_is_outer.


The result has exactly the shape consumed by ChordAnchor.innerFacesSide₁NoCarve_of_classifier / ChordAnchor.contiguousInterval_of_correctAnchor. 

ChordAnchor

8. Ordered sub-brick list

Notation/abbreviation block — worker, 10–20 lines.
Define local abbreviations for β, ρ, a₀, a₁, hne, S, τ.

side₁_trace_beta_a0_to_face₁Dart₁ — worker, 15–25 lines.
Prove τ (β a₀) = face₁Dart₁ data from tracePhi_b0 and sideSigma₁_side₁Anchor₁.

side₁_chord0_face_eq_face₁_canonical — worker, 25–45 lines.
Prove S.dartFace (Sum.inr 0) = S.dartFace (Sum.inl d₁) using chordDart_face_eq_b0 and sideFace_inl_eq_iff_tracePhi.

Side₁OuterTraceData — structural input bundle, 20–40 lines.
Bundle outerFace, outerCycle, outer_simple, outer_len, chord1_is_outer, face₁_not_outer.

side₁Anchors_oneFresh_canonical — worker, 40–80 lines.
First indicator true via β a₀ ~τ d₁; second false via chord1_is_outer and face₁_not_outer.

side₁_correctAnchor_face₁_canonical — worker, 10–20 lines.
Direct call to correctAnchorTwoCycle_ofFace₁ using landed trace12, trace21, and the new oneFresh.

Side₁KeptClass + side₁_kept_trichotomy_canonical — optional diagnostic, 70–120 lines.
Useful for debugging, but not strictly needed if you go directly to hclass.

side1_hclass_canonical — master, 100–180 lines.
Use sideFace_has_inl_rep; split face₁ vs no-hit; no-hit uses spliceUntouched_of_face_ne_chordOrbits.

contiguousInterval_canonical — final assembler, 15–30 lines.
Feed side1_hclass_canonical into contiguousInterval_ofTrace or directly into contiguousInterval_of_correctAnchor.

9. Degenerate-cut audit

The dangerous case is not len = 3; that is valid. It corresponds to a boundary arc with exactly one internal vertex plus the one fresh chord dart, giving a triangular outer side face.

The truly bad case is when the chord endpoints are adjacent on the old boundary. Then the “outer cycle” would have one old boundary edge plus the fresh chord edge, length 2, and the fresh chord is parallel to a boundary edge. That should be excluded by the proper-boundary-chord/separation hypotheses, not patched inside side1_hclass_canonical.

The existing boundary API already exposes the relevant condition: in BoundaryArcSplit, an arc has an internal vertex iff the endpoint pair is not a boundary edge. 

PlanarMapBoundary

So the outer-boundary brick should require or derive:

s(u, v) ∉ outerCycle.edges


or equivalently the appropriate BoundaryPath.HasInternalVertex. Then:

outer_len = keptArc.length + 1 ≥ 2 + 1 = 3.


Do not make side1_hclass_canonical responsible for this. Its job is the no-hit face classification; the length/simple-boundary obligations belong to the outer trace brick.
