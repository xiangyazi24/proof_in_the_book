═══ BRIDGE pbook | 6e8238b0 | 12423 chars 1661 words 325 lines | 298s | prov=network | OK ═══
═══ BRIDGE pbook | 6e8238b0 | 12423 chars 1661 words 325 lines | 298s | prov=network | OK ═══
The short answer is: **genus slack closes the genus/Euler-count part, but it does not by itself construct `ContiguousInterval` or `DeletedOuterBoundary`.** It can be used as a powerful **surjectivity/counting backstop** once you have an explicit candidate boundary orbit and candidate inner-face list, but the actual boundary-cycle normalization, simplicity, and face-orbit identification are still local dart-orbit/Schoenflies data.

So this is **not quite the same kind of collapse** as `OuterDualStep` coverage or `Side₁IsDisk`. The latter are component/Euler assertions. `ContiguousInterval` and `DeletedOuterBoundary` are **structured classification objects**: they name a specific outer face, build a `BoundaryCycle`, prove its vertex list is simple, prove length, and prove every other face is triangular.

The repo’s current file organization already reflects exactly this split: `ChordSideNT.lean` says the side’s sphere/disk core is already discharged by `ChordSideClose + SubmapPlanar + ChordDisk`, while `ContiguousInterval` carries the remaining near-triangulation fields beyond `sphere`: `simpleGraph`, `outerFace`, `outerCycle`, `outer_simple`, `outer_len`, and `inner_tri`. fileciteturn160file0L15-L25 fileciteturn160file0L49-L55

## 1. Chord side: what genus slack can and cannot do

`SubmapPlanar` gives the right genus-zero fact:

```lean
genusSlack = 0
```

for edge-deletion submaps of a sphere, and the file’s own design note states the logic: edge deletion from a genus-0 sphere has slack `0`, hence a connected kept map has Euler characteristic `2`. citeturn127file0 In the side-map chain this is already used: `side₁_sphere_unconditional` gives the `IsSphereMap` field of the side from the disk core plus the anchor-incidence fact. fileciteturn160file0L166-L175

But `ContiguousInterval` is more than `IsSphereMap`. It says the **correct anchors split the trace face contiguously** so that one piece is the chord triangle and the other is the side’s outer boundary cycle; otherwise an arbitrary split can leave a non-triangular inner face. The file states this explicitly: the faces of `sideMap₁` are trace-`φ` orbits, and under the anchor-sharing fact one kept boundary face is split; the *contiguity* of that split is the remaining classification condition. fileciteturn160file0L29-L47

So genus slack can prove:

```lean
(data.sideMap₁ hsep a₀ a₁ hne).eulerChar = 2
```

or, with connectedness, the right **number** of faces. It cannot by itself prove:

```lean
outerCycle : BoundaryCycle (sideMap₁ ...) outerFace
outer_simple : outerCycle.VertexNodup
inner_tri : ∀ f ≠ outerFace, faceLen f = 3
```

because those require knowing **which trace-φ orbit is the outer boundary** and **which trace-φ orbits are the surviving triangles**.

The clean genus-zero-assisted proof skeleton is:

```lean
-- candidate data from explicit chord+arc run
candidateOuterFace : (sideMap₁ ...).Face
candidateOuterCycle : BoundaryCycle (sideMap₁ ...) candidateOuterFace

-- local orbit proofs, not just Euler
candidate_outer_orbit :
  faceOrbit candidateOuterFace = chord_cap_darts ∪ arc_darts

candidate_inner_faces_triangle :
  ∀ f, f ≠ candidateOuterFace → candidateFace f → faceLen f = 3

candidate_face_injective :
  candidate face labels are pairwise distinct

candidate_face_count :
  number of candidate faces = (sideMap₁ ...).F
```

The last line is where genus slack/Euler is useful: once local injections are proved, the Euler face count can close **surjectivity** of the face classification. But it does not manufacture the candidate face labels.

The precise theorem to target is therefore not:

```lean
genus_zero_side_map_gives_ContiguousInterval
```

but:

```lean
theorem ContiguousInterval.of_explicit_orbit_classification
    (hsphere : (data.sideMap₁ hsep a₀ a₁ hne).IsSphereMap)
    (houter_orbit : ...)
    (houter_simple : ...)
    (houter_len : ...)
    (hinner_inj : ...)
    (hinner_tri_local : ...)
    (hface_count_from_genus0 : ... = (data.sideMap₁ ...).F) :
    ContiguousInterval data hsep a₀ a₁ hne
```

Genus slack supplies `hsphere` and `hface_count_from_genus0`; the rest is explicit dart-orbit bookkeeping.

## 2. Deleted boundary: same diagnosis

For boundary-vertex deletion, the repo has already separated the orbit-algebraic construction from the remaining planar certificate.

`PlanarMapDeletedBoundary.lean` says the new outer boundary is the explicit `φ'`-orbit of a root dart, and `boundaryCycleOfFace` can build the orbit-algebra fields of a `BoundaryCycle`; but the genuinely planar inputs remain: `arcSplit`, boundary vertex simplicity, length, and `inner_tri`. fileciteturn164file0L73-L83

The actual constructor

```lean
DeletedOuterBoundary.ofMergedFace
```

takes exactly these as inputs:

```lean
arcSplit
outer_simple
outer_len_ge_three
inner_tri
```

and then builds the `BoundaryCycle` from the explicit `φ'` dart list. fileciteturn166file0L21-L55

The certificate layer then bundles:

```lean
mergedOrbit : DeleteVertexMergedFaceSingleOrbit M d0
boundary : DeletedOuterBoundary hNT d0
```

as the remaining planar facts. fileciteturn166file0L57-L80

So even if you now have:

```lean
deleteVertex_connected_backward
genusSlack zero
(M.deleteVertex d0).eulerChar = 2
```

you still need to prove the **specific merged outer face orbit** and the **normalized boundary cycle**:

```lean
merged boundary darts form one φ'-cycle
their tail list is Nodup
length ≥ 3
all other φ'-orbits are triangular
arcSplit for that boundary list
```

Again, genus slack can close face-count equality after local candidate orbits are identified. It cannot identify the `φ'`-orbit or prove its vertex list is simple.

## 3. Why a single “connected genus-zero submap has a boundary cycle” theorem is too strong

A theorem of the form

```lean
connected genus-zero submap → well-formed simple BoundaryCycle + inner faces untouched
```

is not true without additional hypotheses.

A connected genus-zero combinatorial map can have a face boundary that visits a vertex more than once; a planar map with a cut vertex is the standard obstruction. Euler characteristic `2` does not imply every face boundary is a simple cycle. It also does not imply every non-outer face is a triangle. Those are **near-triangulation classification** facts, not genus facts.

This is why `BoundaryCycle` in the repo is data-rich: it stores a normalized dart list, vertices, edges, and an `arcSplit` function for every pair of boundary vertices. fileciteturn104file0L121-L154 The deleted-boundary file explicitly says `BoundaryCycle` is not derived in the codebase and that the `arcSplit` field is Jordan-curve data. fileciteturn164file0L19-L26

So the “single genus-zero lemma” would have to include extra hypotheses such as:

```lean
hCandidateOuterOrbit :
  the candidate dart list is exactly one φ'-orbit

hOuterNodup :
  candidate vertices are Nodup

hInnerOrbitClassification :
  every non-candidate φ'-orbit is an untouched old triangular face
  or a known chord/fan triangle

hArcSplit :
  the candidate boundary vertex list admits the required arc-splitting
```

At that point the theorem is a useful assembler, not a genus-slack consequence.

## 4. The right proof architecture

The shortest honest route is a **hybrid**:

### Layer A: genus-zero count, already mostly landed

Use the existing machinery:

```lean
SubmapPlanar.genusSlack_rawAlpha_eq_zero
SubmapPlanar.keptMap_eulerChar_eq_two
chi_le_two_of_connected
side₁IsDisk_unconditional
deleteVertex_connected_backward
```

This proves the side/deleted map has the right Euler characteristic and face count.

### Layer B: explicit boundary orbit construction

For each construction, produce a candidate boundary orbit.

For a chord side:

```lean
sideOuterDarts :=
  arcDarts ++ freshChordDarts
```

Prove:

```lean
tracePhi cycles exactly through sideOuterDarts
```

For a deleted boundary vertex:

```lean
deletedOuterDarts :=
  fan edge darts ++ surviving old-boundary arc darts
```

Prove:

```lean
deleted φ cycles exactly through deletedOuterDarts
```

This is not genus slack; it is a dart-by-dart `φ`/filtered-rotation itinerary.

### Layer C: local inner-face classification

Prove every other candidate face is triangular:

For chord side:

```lean
untouched old inner faces remain triangles
chord triangle remains triangle
```

For deletion:

```lean
old faces not incident to v0 remain triangles
fan triangles are absorbed into the merged outer face
```

### Layer D: use genus-zero face count for no-extra-faces

Once you have an injective list of candidate face orbits, use Euler/genus count to prove it is exhaustive:

```lean
candidateFaceCount = sideMap.F
```

or

```lean
candidateFaceCount = (M.deleteVertex d0).F
```

This is where the genus-zero machinery is powerful and avoids a genus-free closed-form label.

### Layer E: build `BoundaryCycle`

Use the existing constructor:

```lean
boundaryCycleOfFace
```

or `DeletedOuterBoundary.ofMergedFace`, supplying:

```lean
arcSplit
outer_simple
outer_len
inner_tri
```

For `arcSplit`, if the boundary vertex list is `Nodup`, it should be a list-combinatorics theorem to split a simple cyclic list. If the repo does not have it, that is a smaller residual than the whole Schoenflies theorem:

```lean
theorem arcSplit_of_nodup_cyclic_boundary_list
    (vertices edges : List ...)
    (hVnodup : vertices.Nodup)
    (hEdgesAlign : edges connect cyclic consecutive vertices) :
    ∀ u v, u ≠ v → u ∈ vertices → v ∈ vertices →
      BoundaryArcSplit ... u v
```

That would remove one of the current “BoundaryCycle as data” burdens.

## 5. How this answers your three questions

### Q1. Can `ContiguousInterval` be constructed by genus slack alone?

**No.** Genus slack proves the side map is genus zero / sphere once connected. It does not prove the correct anchor’s trace-φ split is contiguous, nor that all non-outer faces are triangular. The repo explicitly says the sphere field is already discharged and `ContiguousInterval` carries exactly the remaining boundary/inner-triangulation classification. fileciteturn160file0L63-L74

**Yes**, genus slack can be used as a count backstop in a proof of `ContiguousInterval` once you supply an explicit candidate orbit classification.

### Q2. Same for `DeletedOuterBoundary`?

Same answer. `deleteVertex_connected_backward + genusSlack` can prove the deleted map is genus zero/sphere. It does not prove the merged boundary orbit, boundary vertex simplicity, length, `arcSplit`, or `inner_tri`. The existing constructor `DeletedOuterBoundary.ofMergedFace` shows exactly what remains after orbit algebra: it still requires `arcSplit`, `outer_simple`, `outer_len_ge_three`, and `inner_tri`. fileciteturn166file0L21-L55

### Q3. Is there a single genus-zero discrete Schoenflies lemma for both?

There can be a single **assembler theorem**, but not a theorem whose only topological input is genus zero.

A useful shared theorem would be:

```lean
theorem NearTriangulation_of_explicit_boundary_classification
    (K : CombMap DK)
    (hsphere : K.IsSphereMap)
    (hsimple : K.IsSimpleGraph)
    (outerFace : K.Face)
    (root : DK)
    (houterOrbit : K.dartFace root = outerFace)
    (harcSplit : ...)
    (houter_simple : (K.faceDartList root).map K.tail).Nodup
    (houter_len : 3 ≤ (K.faceDartList root).length)
    (hinner_tri : ∀ f ≠ outerFace, K.faceLen f = 3) :
    NearTriangulation K
```

This is essentially `boundaryCycleOfFace` plus the `NearTriangulation` constructor. It would serve both chord sides and deleted maps. But it still requires the explicit boundary and inner-triangle data.

## Bottom line

The remaining obstruction is **not the genus** anymore. Genus slack has already done its job: it proves the smaller maps are disks/spheres and can close face-count surjectivity. The remaining work is **boundary-cycle normalization and face-orbit classification**:

```lean
which φ-orbit is the outer boundary,
why its vertex list is simple,
why the other face orbits are triangles,
and how to split its boundary list into arcs.
```

That is discrete Schoenflies data in a narrower, genus-zero setting. It is probably constructible from your explicit chord arcs and σ-backward fan, but not from genus slack alone. The best next target is a shared explicit-boundary assembler plus two construction-specific orbit itineraries, not another pure Euler/genus theorem.
