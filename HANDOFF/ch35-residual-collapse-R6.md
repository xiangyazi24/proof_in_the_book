═══ BRIDGE pbook | 915e4e6a | 17155 chars 2419 words 544 lines | 717s | prov=network | OK ═══
═══ BRIDGE pbook | 915e4e6a | 17155 chars 2419 words 544 lines | 717s | prov=network | OK ═══
The collapse is real for the **connectivity/separation residuals**, but it should be phrased as a **two-bank theorem for a simple primal cycle**, not merely as the scalar statement

```lean
numComp (DualAvoidsCycleStep M C) = 2
```

The scalar count gives “there are two components.” The remaining chord residuals also need **bank identification**: which local faces are in the `faceLeft` bank and which are in the `faceRight` bank. The same raw-`α`/boundary-bank orbit analysis gives that identification with only σ-orbit segment lemmas. No `FanIncidenceData` is needed for #1 and #2. It does **not** replace the full chordless fan/deletion reconstruction in #3.

The reason this route is compatible with the repo is that `SimplePrimalCycle` already exposes the cycle darts, successor/predecessor, source-vertex injectivity, and consecutive endpoint condition; `DualAvoidsCycleStep` is already exactly the “cross an edge not in `C.edgeSet`” face relation. fileciteturn80file0L84-L100 fileciteturn80file0L146-L179 fileciteturn113file0L28-L41 The landed `SubmapPlanar` machinery gives the genus-zero slack certificate for raw edge-deletion submaps. fileciteturn127file0L19-L32

---

## 0. The general theorem to target

Do **not** target only:

```lean
theorem genusSlack_twoComponent
    (C : SimplePrimalCycle M) :
    numComp (DualAvoidsCycleStep M C) = 2
```

Target this stronger structure:

```lean
structure SimpleCycleTwoBanks
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombMap D) (C : M.SimplePrimalCycle) where

  numComp_two :
    numComp (DualAvoidsCycleStep M C) = 2

  left_seed : M.Face
  right_seed : M.Face

  left_seed_eq : left_seed = C.faceLeft i₀
  right_seed_eq : right_seed = C.faceRight i₀

  left_bank :
    ∀ i : Fin C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        left_seed (C.faceLeft i)

  right_bank :
    ∀ i : Fin C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        right_seed (C.faceRight i)

  left_right_separated :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M C)
        left_seed right_seed

  coverage :
    ∀ f : M.Face,
      Relation.ReflTransGen (DualAvoidsCycleStep M C) left_seed f ∨
      Relation.ReflTransGen (DualAvoidsCycleStep M C) right_seed f
```

The scalar `numComp_two` plus one Jordan separation statement can give `coverage`, but `left_bank` and `right_bank` are the labels you need later. The repo’s Jordan theorem is separation-shaped: it rules out a `DualReachableAvoidingCycle` between the two faces of a cycle edge. fileciteturn112file0L8-L25

The orbit-count generalization is:

```lean
theorem simpleCycle_bankOrbitCount
    (C : SimplePrimalCycle M) :
    numCycles (M.φ * rawAlpha M C.dartSet hclosed) = M.V - C.len + 2
```

For an arbitrary simple cycle, this is **not** the same as the outer-boundary proof where the forward cycle darts themselves form one bank. For a general `C`, both banks thread through σ-segments.

At cycle vertex `vᵢ = tail (C.dart i)`, the two deleted darts in the σ-star are:

```lean
qᵢ       := C.dart i
rᵢ₋₁     := M.α (C.dart (C.prevIdx i))
```

and the key classifier is:

```lean
lemma cycleDel_inter_vertexOrbit
    {d : D} (hσ : M.σ.SameCycle (C.dart i) d) :
    d ∈ C.dartSet ↔
      d = C.dart i ∨ d = M.α (C.dart (C.prevIdx i))
```

Proof: if a forward cycle dart `C.dart j` is in the same σ-orbit as `C.dart i`, then the tails agree, so `j = i` by `C.tail_inj`. If a reverse dart `M.α (C.dart j)` is in that σ-orbit, then

```lean
tail (M.α (C.dart j)) = head (C.dart j) = tail (C.dart (C.nextIdx j)),
```

so `C.nextIdx j = i`, hence `j = C.prevIdx i`. The `SimplePrimalCycle` API has `nextIdx`, `prevIdx`, and the inverse lemmas. fileciteturn80file0L108-L140

Then define the two bank segments in the σ-star of `C.dart i`:

```lean
bankL segment at i:
  starts at M.σ (M.α (C.dart (C.prevIdx i)))
  runs by σ until C.dart i

bankR segment at i:
  starts at M.σ (C.dart i)
  runs by σ until M.α (C.dart (C.prevIdx i))
```

Under

```lean
P_C := M.φ * rawAlpha M C.dartSet hclosed
```

you have:

```lean
P_C d = M.σ d
```

off `C.dartSet`,

```lean
P_C (C.dart i) = M.φ (C.dart i)
               = M.σ (M.α (C.dart i))
```

which is the start of the corresponding bank segment at `nextIdx i`, and

```lean
P_C (M.α (C.dart (C.prevIdx i)))
  = M.φ (M.α (C.dart (C.prevIdx i)))
  = M.σ (C.dart (C.prevIdx i)),
```

which jumps to the other bank at `prevIdx i`.

Thus the disrupted `C.len` vertex stars become exactly **two** `P_C`-cycles. All untouched σ-cycles survive. So:

```lean
numCycles P_C = M.V - C.len + 2.
```

This is the genuine generalization of the R5 outer-boundary bank count. It uses only the cycle’s `tail_inj` and `consecutive`; it does not require fan orientation.

---

## 1. SideRegionInterChordEnds

You can avoid the full fan tower.

What you need is a local star lemma for any forbidden edge set.

Define a generic face adjacency avoiding a forbidden edge predicate:

```lean
def FaceAdjAvoiding
    (M : CombMap D) (Forbidden : Sym2 M.Vertex → Prop)
    (f g : M.Face) : Prop :=
  ∃ d : D,
    M.dartFace d = f ∧
    M.dartFace (M.α d) = g ∧
    ¬ Forbidden (M.dartEdge d)
```

The core one-step lemma is:

```lean
lemma sigma_step_faceAdjAvoiding
    {x : D}
    (hx : ¬ Forbidden (M.dartEdge x)) :
    FaceAdjAvoiding M Forbidden
      (M.dartFace x)
      (M.dartFace (M.σ x))
```

Proof: witness `x`. You need

```lean
M.dartFace (M.α x) = M.dartFace (M.σ x)
```

because

```lean
M.φ (M.α x) = M.σ x.
```

Then:

```lean
lemma star_connected_avoiding
    {x y : D}
    (hσ : M.σ.SameCycle x y)
    (havoid :
      ∀ z, M.σ.SameCycle x z →
        ¬ Forbidden (M.dartEdge z)) :
    Relation.ReflTransGen (FaceAdjAvoiding M Forbidden)
      (M.dartFace x) (M.dartFace y)
```

This is just induction over a σ-power from `x` to `y`.

For chord splitting, instantiate:

```lean
Forbidden e :=
  hNT.outerCycle.IsBoundaryEdge e ∨ e = s(u, v)
```

Then `FaceAdjAvoiding` is the same as `ChordSplitAdj`.

For a vertex `w` that is neither chord endpoint nor boundary, no dart in its σ-star has a forbidden edge, so all incident faces are in one `ChordSplitAdj` component.

For a boundary vertex `w ≠ u,v`, you use the **outer boundary local classifier**, not the fan:

```lean
lemma boundary_nonouter_star_connected
    (hw : hNT.outerCycle.IsBoundaryVertex w)
    (hwu : w ≠ u) (hwv : w ≠ v)
    {f g : M.Face}
    (hf : f ≠ hNT.outerFace)
    (hg : g ≠ hNT.outerFace)
    (hfw : IncidentVertexFace M w f)
    (hgw : IncidentVertexFace M w g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g
```

Its proof is the outer-cycle version of the σ-segment lemma: the two boundary darts cut the boundary vertex σ-star into one outer-face singleton/bank and one non-outer segment. Since `w` is not a chord endpoint, the chord edge is not incident to `w`; hence every edge inside the non-outer segment is non-boundary and non-chord.

Then:

```lean
theorem SideRegionInterChordEnds
    (h1 : sideRegion₁ w)
    (h2 : sideRegion₂ w) :
    w = u ∨ w = v := by
  by_contra hnot
  -- unpack h1, h2:
  rcases h1 with ⟨f, hf_side1, hfw⟩
  rcases h2 with ⟨g, hg_side2, hgw⟩

  have hf_nonouter := data.side₁_subset_nonouter hf_side1
  have hg_nonouter := data.side₂_subset_nonouter hg_side2
  -- side subset nonouter is already in ChordSplitData. 
  -- cite: side₁_subset_nonouter / side₂_subset_nonouter.
```

`side₁_subset_nonouter` and `side₂_subset_nonouter` are already available. fileciteturn103file0L40-L48

Now use `incident_faces_same_component_of_not_chord_end`:

```lean
have hfg :
  Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g :=
    incident_faces_same_component_of_not_chord_end hnot hfw hgw hf_nonouter hg_nonouter
```

Then compose:

```lean
face₁ ~* f ~* g ~* face₂
```

contradicting the chord separation/disjointness.

So yes: **StarFanOneSide collapses to σ-star connectivity plus the outer-boundary segment classifier.** No `BoundaryVertexFan` certificate is needed for this residual.

---

## 2. OppArcSeedReach

This also collapses, but not from the scalar count alone. You need the same local bank/star lemmas.

The clean chain is:

```lean
theorem OppArcSeedReach
    {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices)
    {f : M.Face}
    (hf_nonouter : f ≠ hNT.outerFace)
    (hfw : IncidentVertexFace M w f) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) f data.face₂
```

Prove by a boundary-arc induction.

Define for every boundary edge dart `b` on `path₂` its inner face:

```lean
innerFaceOfBoundaryDart b := M.dartFace (M.α b)
```

This is non-outer because crossing a boundary dart’s reverse enters the triangulated disk.

Then prove two local lemmas.

First, at an internal boundary vertex of `path₂`, consecutive boundary-edge inner faces are connected:

```lean
lemma pathInternal_innerFaces_connected
    {b₁ b₂ : D}
    (hb₁ : b₁ and b₂ are consecutive boundary darts at w along path₂)
    (hw_not_chord_end : w ≠ u ∧ w ≠ v) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v)
      (M.dartFace (M.α b₁))
      (M.dartFace (M.α b₂))
```

This is just `boundary_nonouter_star_connected`.

Second, at the chord endpoint where `path₂` starts, the first path₂ boundary inner face is connected to `data.face₂`:

```lean
lemma face₂_reaches_first_path₂_innerFace :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v)
      data.face₂
      (innerFaceOfBoundaryDart firstPath₂Dart)
```

This is an endpoint σ-segment lemma: at the chord endpoint, the chord dart and the first path₂ boundary dart lie in the same side segment; the other side segment contains `data.face₁`.

This endpoint lemma is precisely the **cycle-bank label** for the chord cycle, but it is small. You can get it from the general `SimpleCycleTwoBanks` theorem applied to the chord-plus-path₁ or chord-plus-path₂ simple cycle, depending on your orientation convention.

Then induct along `path₂`:

```lean
face₂
  ~ first boundary inner face
  ~ next boundary inner face
  ~ ...
  ~ a boundary inner face incident to w
  ~ f
```

The final step `inner face at w ~ f` is again `boundary_nonouter_star_connected`.

So the answer to #2 is:

* `numComp(DualAvoidsCycleStep M C)=2` helps by naming the two banks.
* The actual proof of `OppArcSeedReach` needs the **bank-labelled local theorem**, not just the scalar count.
* No full fan certificate is needed; the path induction uses only σ-star segment connectivity.

---

## 3. ChordlessBranchSupplier

This one does **not** collapse to genus slack alone.

`ChordlessBranchSupplier` / `FanSurgeryReconstruction` is not merely a statement that some faces are in the same dual component. It constructs the boundary-vertex deletion/reconstruction data: a neighbor path, exact fan triangles, merged outer boundary, and the deletion map’s near-triangulation structure.

The repo already makes this distinction explicit. `PlanarMapFanExistence.lean` says it constructs `BoundaryVertexFan hNT v0` from `FanIncidenceData`; the latter packages the orientation/Jordan incidence content not produced by orbit algebra alone. fileciteturn93file0L6-L15 It then states:

```lean
boundaryVertexFan_exists :
  FanIncidenceData hNT v0 → Nonempty (BoundaryVertexFan hNT v0)
```

not

```lean
NearTriangulation M → Nonempty (BoundaryVertexFan hNT v0).
```

fileciteturn94file0L78-L106

Likewise, boundary deletion needs a `BoundaryDeletionData` certificate with vertex quotient, face merge, and connectedness fields. The file explicitly says those are genuine dart-rotation surgery facts, not automatic from the generic deletion API. fileciteturn126file0L65-L99

So the honest assessment is:

* The σ-orbit/genus-slack machinery can prove the **connectivity/side-contiguity facts** formerly obtained from fan intuition.
* It does **not** by itself construct the full `FanSurgeryReconstruction`.
* The shortest route for `ChordlessBranchSupplier` is still to keep `FanIncidenceData` / `BoundaryDeletionData` as the residual, unless you weaken the supplier so it only asks for the connectivity facts now obtainable by the orbit method.

If the final chapter theorem no longer needs actual boundary-vertex deletion, remove the fan supplier. If it still needs deletion/reconstruction, this is the one genuinely irreducible construction left.

---

## 4. The right single general lemma

Target this, not merely `numComp = 2`:

```lean
structure SimpleCycleBankTheorem
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombMap D) (C : SimplePrimalCycle M) where

  rawAlpha : Equiv.Perm D
  rawAlpha_eq_self_on_cycle :
    ∀ d, d ∈ C.dartSet → rawAlpha d = d
  rawAlpha_eq_alpha_off_cycle :
    ∀ d, d ∉ C.dartSet → rawAlpha d = M.α d

  bankOrbitCount :
    numCycles (M.φ * rawAlpha) = M.V - C.len + 2

  slack_zero :
    genusSlack M.φ rawAlpha = 0

  dual_numComp_two :
    numComp (DualAvoidsCycleStep M C) = 2

  left_bank :
    ∀ i j : Fin C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (C.faceLeft i) (C.faceLeft j)

  right_bank :
    ∀ i j : Fin C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (C.faceRight i) (C.faceRight j)

  left_right_sep :
    ∀ i j : Fin C.len,
      ¬ Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (C.faceLeft i) (C.faceRight j)
```

Then:

* Outer-cycle coverage is the `C = outerCycle` specialization plus the already-proven outer-face isolation.
* Chord separation is the chord-cycle specialization.
* `SideRegionInterChordEnds` uses `star_connected_avoiding` plus boundary nonouter star connectivity.
* `OppArcSeedReach` uses `left_bank` / `right_bank` and the boundary-arc induction.

The general bank orbit count **does generalize**, but not in the literal R5 form “forward cycle darts form one cycle.” For an arbitrary `SimplePrimalCycle`, the two bank cycles are:

```lean
BankA:
  C.dart i
  → σ (α (C.dart i))
  → ... along the σ-segment at vertex nextIdx i
  → C.dart (nextIdx i)
  → ...

BankB:
  α (C.dart (prevIdx i))
  → σ (C.dart (prevIdx i))
  → ... along the opposite σ-segment at vertex prevIdx i
  → α (C.dart (prevIdx (prevIdx i)))
  → ...
```

Both are single cycles because `nextIdx` and `prevIdx` are single cycles on `Fin C.len`. This uses only `SimplePrimalCycle.consecutive`, `tail_inj`, `nextIdx_prevIdx`, and `prevIdx_nextIdx`. fileciteturn80file0L84-L100 fileciteturn80file0L108-L140

---

## Minimal lemma chain

Here is the shortest practical chain.

### A. Generic star connectivity

```lean
lemma sigma_step_faceAdjAvoiding
    {Forbidden : Sym2 M.Vertex → Prop} {x : D}
    (hx : ¬ Forbidden (M.dartEdge x)) :
    FaceAdjAvoiding M Forbidden
      (M.dartFace x) (M.dartFace (M.σ x))

lemma star_connected_avoiding
    {Forbidden : Sym2 M.Vertex → Prop} {x y : D}
    (hσ : M.σ.SameCycle x y)
    (havoid : ∀ z, M.σ.SameCycle x z → ¬ Forbidden (M.dartEdge z)) :
    Relation.ReflTransGen (FaceAdjAvoiding M Forbidden)
      (M.dartFace x) (M.dartFace y)
```

### B. Boundary nonouter star connectivity

```lean
lemma boundary_nonouter_star_connected
    {u v w : M.Vertex}
    (hw : hNT.outerCycle.IsBoundaryVertex w)
    (hwu : w ≠ u) (hwv : w ≠ v)
    {f g : M.Face}
    (hf : f ≠ hNT.outerFace)
    (hg : g ≠ hNT.outerFace)
    (hfw : IncidentVertexFace M w f)
    (hgw : IncidentVertexFace M w g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g
```

This is the local R5 outer-boundary σ-segment proof.

### C. Non-chord-end incident faces are one side

```lean
lemma incident_faces_same_component_of_not_chordEnd
    {u v w : M.Vertex}
    (hwu : w ≠ u) (hwv : w ≠ v)
    {f g : M.Face}
    (hf : f ≠ hNT.outerFace)
    (hg : g ≠ hNT.outerFace)
    (hfw : IncidentVertexFace M w f)
    (hgw : IncidentVertexFace M w g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g
```

Case split on whether `w` is a boundary vertex. Interior case uses `star_connected_avoiding`; boundary case uses `boundary_nonouter_star_connected`.

### D. Side intersection

```lean
theorem sideRegion_inter_chordEnds
    (h1 : sideRegion₁ w)
    (h2 : sideRegion₂ w) :
    w = u ∨ w = v
```

Uses C plus `data.side₁_subset_nonouter` / `data.side₂_subset_nonouter`. fileciteturn103file0L40-L48

### E. Opposite arc seed reach

```lean
lemma path₂_inner_faces_reach_face₂
    {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices)
    {f : M.Face}
    (hf : f ≠ hNT.outerFace)
    (hfw : IncidentVertexFace M w f) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) f data.face₂
```

Proof: boundary-path induction using `boundary_nonouter_star_connected`, with one endpoint bank lemma from `SimpleCycleBankTheorem`.

---

## Final recommendation

Build one file around:

```lean
SimpleCycleBankTheorem
```

with the raw-α deletion count

```lean
numCycles (M.φ * rawAlpha M C.dartSet _) = M.V - C.len + 2
```

and the bank-labelled reachability lemmas. Then use **tiny** local σ-star lemmas to discharge `SideRegionInterChordEnds` and `OppArcSeedReach`.

Do **not** try to use this to synthesize `FanSurgeryReconstruction`; that is a different kind of object. The fan/deletion supplier is the only residual that is not just a two-bank connectivity statement.
