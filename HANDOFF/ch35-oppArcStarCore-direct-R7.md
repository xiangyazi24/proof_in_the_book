═══ BRIDGE pbook | c23fd365 | 9652 chars 1399 words 323 lines | 257s | prov=network | OK ═══
═══ BRIDGE pbook | c23fd365 | 9652 chars 1399 words 323 lines | 257s | prov=network | OK ═══
The seed route is dead, but the **new direct route only works if you have one replacement lemma**:

```lean
path₂_internal_mem_sideRegion₂ :
  ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices →
      w ∈ sideRegion₂ data
```

or equivalently a kept-side-2 dart at every path₂-internal boundary vertex.

With that lemma, both conjuncts of `oppArc_star_core` close cleanly via `SideRegionInterChordEnds`. Without it, the proof does **not** close, and in the current data layer it is not automatic: `BoundaryArcSplit.path₂` is not visibly tied to the `face₂` bank selected by `data.dart`. That is the same orientation issue that killed `OppArcSeedReach`, just weakened from “dual-reach seed” to “vertex lies in the side-2 region.”

## 1. First conjunct reduces exactly as you suggest

You want:

```lean
M.dartFace d ∉ data.side₁
```

inside the second branch of

```lean
d = data.dart ∨ ...
```

Assume:

```lean
hw : w ∈ data.arc.path₂.internalVertices
htail : M.tail d = w
hd_ne : d ≠ data.dart
hface1 : M.dartFace d ∈ data.side₁
```

Then `d` is a kept side-1 dart. Indeed:

```lean
data.keptSet₁ = (data.sideDarts₁ ∪ data.outerArc₁) \ {data.dart}
```

and `data.sideDarts₁` is `{d | M.dartFace d ∈ data.side₁}`. The kept-set definition is in `PlanarMapChordSplit.lean`: side-1 keeps inner side-1 darts plus matching outer-arc darts, minus the chord dart. fileciteturn148file0L185-L201

So:

```lean
have hd_kept₁ : d ∈ data.keptSet₁ := by
  exact ⟨Or.inl hface1, by simpa using hd_ne⟩
```

Then:

```lean
have hw₁ : w ∈ sideRegion₁ data :=
  ⟨d, by
     -- depending on your definition:
     -- either hd_kept₁ directly, or via mem_keptDel₁_iff
     exact ..., htail⟩
```

The landed side-1 region is exactly “tails of kept side-1 darts”; `tail_mem_sideRegion₁` packages that direction. fileciteturn144file0L97-L105

Now use the replacement lemma:

```lean
have hw₂ : w ∈ sideRegion₂ data :=
  path₂_internal_mem_sideRegion₂ hw
```

and the endpoint exclusion from path-internality:

```lean
have hw_ne_v : w ≠ v := data.arc.path₂.internalVertex_ne_start hw
have hw_ne_u : w ≠ u := data.arc.path₂.internalVertex_ne_end hw
```

`path₂ : BoundaryPath v u`, so its internal vertices are distinct from both endpoints by the existing `internalVertex_ne_start` and `internalVertex_ne_end` lemmas. fileciteturn147file0L134-L156

Then:

```lean
have hends : w = u ∨ w = v :=
  SideRegionInterChordEnds data hw₁ hw₂
```

contradiction.

So first conjunct is done with:

```lean
path₂_internal_mem_sideRegion₂
SideRegionInterChordEnds
path₂.internalVertex_ne_start/end
```

No seed, no dual-reach, no arc↔cycle proof.

## 2. Second conjunct also closes the same way — use `tail d`, not `head d`

You want:

```lean
¬ (M.dartFace d = hNT.outerFace ∧ M.dartFace (M.α d) ∈ data.side₁)
```

Assume:

```lean
hd_outer : M.dartFace d = hNT.outerFace
hα_side1 : M.dartFace (M.α d) ∈ data.side₁
```

Do **not** argue through `head d`. That fails at the first/last internal vertex of `path₂`, where the boundary neighbor can be `u` or `v`.

Instead, use the **outer-arc kept dart** at the same tail `w`.

Since

```lean
data.outerArc₁ = {b | M.dartFace b = hNT.outerFace ∧
                      M.dartFace (M.α b) ∈ data.side₁}
```

you have:

```lean
have hd_outerArc₁ : d ∈ data.outerArc₁ :=
  ⟨hd_outer, hα_side1⟩
```

If `d ≠ data.dart`, then:

```lean
have hd_kept₁ : d ∈ data.keptSet₁ :=
  ⟨Or.inr hd_outerArc₁, by simpa using hd_ne⟩
```

and therefore:

```lean
have hw₁ : w ∈ sideRegion₁ data :=
  ⟨d, ..., htail⟩
```

Again combine with:

```lean
have hw₂ : w ∈ sideRegion₂ data :=
  path₂_internal_mem_sideRegion₂ hw
```

and `SideRegionInterChordEnds`, contradicting `w ≠ u,v`.

If your branch still requires handling the top-level disjunct, you are proving this only in the `d ≠ data.dart` branch. In the full theorem:

```lean
d = data.dart ∨ ...
```

you case split first. In the `d = data.dart` branch, return left. In the `d ≠ data.dart` branch, both conjuncts are proved by contradiction as above.

So yes: conjunct 2 closes by the **same mechanism** as conjunct 1, but through `d ∈ outerArc₁`, not through `head d`.

This avoids the “other endpoint may be a chord endpoint” trap.

## 3. The whole direct proof skeleton

Assume you add or already have the side-2 analogue:

```lean
def sideRegion₂ (data : hNT.ChordSplitData u v) : Set M.Vertex :=
  {w : M.Vertex | ∃ d : D, d ∈ data.keptSet₂ ∧ M.tail d = w}
```

or equivalently via `d ∉ data.keptDel₂`; `mem_keptDel₂_iff` gives equivalence between complement of the deleted set and membership in `keptSet₂`. fileciteturn149file0L44-L63

Then state the replacement lemma:

```lean
lemma path₂_internal_mem_sideRegion₂
    {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) :
    w ∈ sideRegion₂ data
```

Now prove:

```lean
theorem oppArc_star_core_direct
    {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices)
    (d : D)
    (htail : M.tail d = w) :
    d = data.dart ∨
      (M.dartFace d ∉ data.side₁ ∧
        ¬ (M.dartFace d = hNT.outerFace ∧
           M.dartFace (M.α d) ∈ data.side₁)) := by
  by_cases hd : d = data.dart
  · exact Or.inl hd
  · right

    have hw₂ : w ∈ sideRegion₂ data :=
      path₂_internal_mem_sideRegion₂ hw

    have hw_ne_v : w ≠ v :=
      data.arc.path₂.internalVertex_ne_start hw
    have hw_ne_u : w ≠ u :=
      data.arc.path₂.internalVertex_ne_end hw

    have no_sideRegion₁ : w ∉ sideRegion₁ data := by
      intro hw₁
      have hends : w = u ∨ w = v :=
        SideRegionInterChordEnds data hw₁ hw₂
      rcases hends with hwu | hwv
      · exact hw_ne_u hwu
      · exact hw_ne_v hwv

    constructor
    · -- first conjunct
      intro hface1
      have hd_kept₁ : d ∈ data.keptSet₁ := by
        exact ⟨Or.inl hface1, by simpa [Set.mem_singleton_iff] using hd⟩
      exact no_sideRegion₁ ⟨d, hd_kept₁, htail⟩

    · -- second conjunct
      rintro ⟨hd_outer, hα_side1⟩
      have hd_outerArc₁ : d ∈ data.outerArc₁ :=
        ⟨hd_outer, hα_side1⟩
      have hd_kept₁ : d ∈ data.keptSet₁ := by
        exact ⟨Or.inr hd_outerArc₁, by simpa [Set.mem_singleton_iff] using hd⟩
      exact no_sideRegion₁ ⟨d, hd_kept₁, htail⟩
```

This is the cleanest proof of `oppArc_star_core` once the path₂→sideRegion₂ lemma exists.

## 4. Is `path₂_internal_mem_sideRegion₂` clean or already implied?

This is the crucial point: **it is not implied by the current `ChordSplitData` as shown in the files I can read.**

`ChordSplitData` builds:

```lean
data.dart
data.face₁ := M.dartFace data.dart
data.face₂ := M.dartFace (M.α data.dart)
data.side₁ := Side face₁
data.side₂ := Side face₂
data.arc.path₁
data.arc.path₂
```

The chord dart and its two incident face labels are chosen from the chord edge; the two boundary arcs come from `BoundaryCycle.two_arcs`. The file defines `face₁`, `face₂`, `side₁`, and `side₂` from the chord dart, while the arcs are just the two opaque boundary paths between `u` and `v`. fileciteturn102file0L204-L250 The boundary-arc structure itself only stores path order, boundary membership, coverage, internal disjointness, and properness equivalences; it does not say which side/bank a path bounds. fileciteturn104file0L93-L119

So the lemma

```lean
path₂_internal_mem_sideRegion₂
```

is exactly a **bank-orientation bridge**:

```text
the second listed boundary arc is the side-2 boundary arc.
```

That is weaker than the dead `OppArcSeedReach`, because it only asks for vertex-region membership, not a particular dual path to `face₂`; but it is still an orientation statement. It cannot be derived from `path₂` being a boundary arc alone.

In fact, if the chosen chord dart is reversed, the names `face₁` and `face₂` swap while `path₁` and `path₂` do not. Then “path₂ vertices lie in side₂” swaps truth value. This is the same orientation mismatch that made the seed theorem false.

Therefore:

* The direct proof is valid and very short **conditional on** `path₂_internal_mem_sideRegion₂`.
* If your current `ChordSplitData` does not tie `data.dart` orientation to `data.arc.path₂`, this lemma is not automatic and may be false.
* To make it unconditional, you need either normalize the chord dart/arc labeling or state a symmetric version that chooses the opposite arc according to the side.

## 5. Recommended fix

Replace the false seed residual by the weakest honest orientation datum:

```lean
structure ChordArcBankOrientation
    (data : hNT.ChordSplitData u v) : Prop where
  path₂_internal_mem_sideRegion₂ :
    ∀ {w : M.Vertex},
      w ∈ data.arc.path₂.internalVertices →
        w ∈ sideRegion₂ data
```

or, if you also need boundary endpoints along path₂:

```lean
path₂_vertices_mem_sideRegion₂ :
  ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.vertices →
    w ≠ u → w ≠ v →
      w ∈ sideRegion₂ data
```

But for `oppArc_star_core`, the internal version is enough.

This is strictly weaker and cleaner than `OppArcSeedReach`:

```lean
OppArcSeedReach ⇒ path₂_internal_mem_sideRegion₂
```

but not conversely. It avoids the false “specific outer boundary dart seed reaches face₂” orientation.

## Final ruling

Yes, `oppArc_star_core` collapses to:

```text
SideRegionInterChordEnds
+ path₂_internal_mem_sideRegion₂
+ keptSet₁/outerArc₁ definitions
+ path₂ internal vertices are not u/v.
```

No seed, no fan, no arc↔cycle dual path is needed inside `oppArc_star_core`.

But the lemma “path₂-internal vertices are in sideRegion₂” is the remaining orientation bridge. It is not provided by the opaque `BoundaryArcSplit` data as currently defined, and it is not a consequence of `numComp = 2` unless you also identify which component corresponds to which boundary arc.
