[intro]
I’ll pin this against the current branch files, especially `ZinanCh35Iota.lean` and the boundary/arc definitions, because the constructor route depends on exact field names rather than topology folklore.

[answer]
## 0. Main correction

For the **supplier** of `Side₁OuterTraceData`, do **not** hand-build

```lean
[Sum.inl (β a₁), Sum.inr 1] ++ outerKeptArc.map Sum.inl
```

as the primary Lean object.

The current branch already has the better route in `ZinanCh35OuterTrace.lean`: define

```lean
outerFace := S.dartFace (Sum.inr 1)
```

and build the boundary cycle by the generic orbit-list constructor

```lean
CombMap.boundaryCycleOfFace S outerFace (root := Sum.inr 1) ...
```

That constructor uses

```lean
S.faceDartList (Sum.inr 1) = S.φ.toList (Sum.inr 1)
```

so the actual dart list is the normalized `φ`-orbit list rooted at `inr 1`, not a manually sliced arc list. The file header explicitly says this is the intended supplier route: `outerFace := S.dartFace (Sum.inr 1)`, `chord1_is_outer := rfl`, and the orbit-algebraic boundary-cycle fields are discharged by `CombMap.boundaryCycleOfFace`; the Jordan/cyclic-list inputs remain explicit residues. ₁OuterTraceData` constructor route

### 1(a). Defining `outerKeptArc`

Do **not** define `outerKeptArc` as a new object unless you need a human-readable certificate later.

The minimal route is:

```lean
let S :=
  data.sideMap₁ hsep
    (side₁Anchor₀ data hsep)
    (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep)

let outerFace : S.Face := S.dartFace (Sum.inr 1)

let outerCycle : BoundaryCycle S outerFace :=
  S.boundaryCycleOfFace outerFace
    (root := Sum.inr 1)
    hφ_root
    rfl
    arcSplit
```

where

```lean
hφ_root : S.φ (Sum.inr 1) ≠ Sum.inr 1
```

is easiest from `phi_ne_self_of_isSimpleGraph S hsimple (Sum.inr 1)`.

The generic constructor is in `PlanarMapDeletedBoundary.lean`:

```lean
def faceDartList (M : CombMap D) (root : D) : List D :=
  M.φ.toList root

def boundaryCycleOfFace
  (M : CombMap D) (f : M.Face) {root : D}
  (hφ : M.φ root ≠ root)
  (hroot : M.dartFace root = f)
  (arcSplit : ...)
  : BoundaryCycle M f
```

It discharges normalized list, `consecutive_phi`, `consecutive_vertex`, `vertices_eq`, and `edges_eq` from the `φ.toList` API; only `arcSplit` is supplied as planar data. fileciteturn40file0L4-L4

So the route that minimizes new orbit combinatorics is:

```lean
outerKeptArc = not defined
outerCycle.darts = S.faceDartList (Sum.inr 1)
```

The old boundary `hNT.outerCycle.arcSplit` / `data.arc` should be used only conceptually or later to *justify* the supplied `arcSplit`; it should not be unfolded into a new side-map dart list in this brick.

### 1(b). `consecutive_phi` / `consecutive_vertex`

With `boundaryCycleOfFace`, these are automatic:

```lean
consecutive_phi := S.faceDartList_consecutive_phi hφ_root
consecutive_vertex := S.faceDartList_consecutive_vertex hφ_root
```

No `SpliceUntouched` avoidance is needed in the constructor.

If you insist on the manual list, the split is:

```lean
S.φ (Sum.inl (β a₁)) = Sum.inr 1
S.φ (Sum.inr 1)      = Sum.inl (ρ a₀)
```

from `freshMap_phi_inl_b1` and `freshMap_phi_inr_one`, then along the kept arc use `tracePhi_other` / `tracePhi_apply_eq_keptPhi_of_avoid` away from `β a₀, β a₁`, and handle the final re-entry into `β a₁` explicitly. But this is exactly the complexity `boundaryCycleOfFace` avoids.

### 1(c). `outer_simple` and `outer_len ≥ 3`

In the landed supplier design, these remain inputs:

```lean
outer_simple : outerCycle.VertexNodup
outer_len    : 3 ≤ outerCycle.length
```

That is intentional. `BoundaryCycle` itself stores `arcSplit` as data, and `NearTriangulation` stores `outerCycle`, `outer_simple`, and `outer_len` as fields, so this repo does not derive normalized boundary simplicity from raw `CombMap` orbit algebra. The boundary-cycle structure confirms those are explicit data fields. fileciteturn30file0L121 endpoints is:

```lean
data.chord : hNT.outerCycle.Chord u v
```

Inside that, the killer field is the chord’s “not a boundary edge” fact, used in the repo as:

```lean
data.chord.not_boundary_edge
```

This is what prevents `s(u,v)` from already being an old boundary edge. `ChordSplitData` also carries:

```lean
arc₁_internal : data.arc.path₁.HasInternalVertex
arc₂_internal : data.arc.path₂.HasInternalVertex
```

so both boundary arcs have internal vertices; those are stronger than merely nonadjacent and are the strict-decrease witnesses. filecite `face₁_not_outer`

Use:

```lean
outerFace := S.dartFace (Sum.inr 1)
```

Then:

```lean
chord1_is_outer : S.dartFace (Sum.inr 1) = outerFace := rfl
```

For

```lean
face₁_not_outer :
  S.dartFace (Sum.inl (face₁Dart₁ data)) ≠ outerFace
```

do **not** prove it from `VertexNodup`. The landed route proves it orbit-theoretically:

1. `side₁_chord0_face_eq_face₁_canonical` gives

```lean
S.dartFace (Sum.inr 0) = S.dartFace (Sum.inl (face₁Dart₁ data))
```

2. So `face₁_not_outer` reduces to

```lean
S.dartFace (Sum.inr 0) ≠ S.dartFace (Sum.inr 1)
```

3. `chordOrbits_eq_iff_tracePhi` turns equality of those two fresh chord-dart faces into

```lean
τ.SameCycle (β a₀) (β a₁)
```

4. `ZinanCh35OuterTrace` proves the negation:

```lean
side₁_chordPred_notSameCycle_canonical :
  ¬ τ.SameCycle (β a₀) (β a₁)
```

by using the canonical share-face fact and a transposition-split lemma: swapping two points in the same `keptPhi` cycle splits that cycle.  Supplier signature

Use the landed shape, not the manual-arc shape:

```lean
noncomputable def side₁OuterTraceData_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hsimple :
      (data.sideMap₁ hsep
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).IsSimpleGraph)
    (arcSplit :
      ∀ ⦃p q :
          (data.sideMap₁ hsep
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).Vertex⦄,
        p ≠ q →
        p ∈
          ((data.sideMap₁ hsep
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
            (data.sideMap₁ hsep
              (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).tail →
        q ∈
          ((data.sideMap₁ hsep
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
            (data.sideMap₁ hsep
              (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).tail →
        BoundaryArcSplit
          (data.sideMap₁ hsep
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep))
          (((data.sideMap₁ hsep
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
              (data.sideMap₁ hsep
                (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
                (side₁Anchors_ne data hsep)).tail)
          (((data.sideMap₁ hsep
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
              (data.sideMap₁ hsep
                (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
                (side₁Anchors_ne data hsep)).dartEdge)
          p q)
    (outer_simple : ...)
    (outer_len : ...)
    (inner_reps :
      InnerRepsAvoidBoundary data hsep
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)
        ((data.sideMap₁ hsep
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1))) :
    Side₁OuterTraceData data hsep
```

The real implementation can shorten with `let S := ...` inside the theorem body, but theorem statements in this repo usually spell terms explicitly for `rw`/`simp` compatibility.

The constructor body:

```lean
let S := ...
let outerFace := S.dartFace (Sum.inr 1)
let hφ : S.φ (Sum.inr 1) ≠ Sum.inr 1 :=
  phi_ne_self_of_isSimpleGraph S hsimple (Sum.inr 1)
let outerCycle :=
  S.boundaryCycleOfFace outerFace
    (root := Sum.inr 1)
    hφ
    rfl
    arcSplit

{
  outerFace := outerFace
  outerCycle := outerCycle
  outer_simple := outer_simple
  outer_len := outer_len
  chord1_is_outer := rfl
  face₁_not_outer := side₁_face₁_not_outer_canonical data hsep
  inner_reps := inner_reps
}
```

Note the **reported addition** to `Side₁OuterTraceData`:

```lean
inner_reps :
  InnerRepsAvoidBoundary data hsep a₀ a₁ hne outerFace
```

`ZinanCh35Hclass` says this was added because the no-hit branch needs the real geometric statement that every non-outer side face has a kept representative avoiding the ambient outer face and `face₁`. fileciteturn44file0L4-L4

---

## 3. Remaining confinement residues: `hreflect` / `homit`

`ZinanCh35Iota.lean` says exactly what remains.

### `hreflect`

This is the reflection half of adjacency:

```lean
hreflect :
  ∀ {x y :
      (data.sideMap₁ hsep a₀ a₁ hne).Vertex},
    M.Adj
      (sideVertexToM₁ data hsep a₀ a₁ hne x)
      (sideVertexToM₁ data hsep a₀ a₁ hne y) →
    (data.sideMap₁ hsep a₀ a₁ hne).Adj x y
```

Conceptually: if two side-region vertices are adjacent in `M`, that edge is either a side edge or the chord edge. This is exactly the “edge confinement from separation” residue. The file header says no `ChordSplitRegions` producer exists yet, so `hreflect` is intentionally threaded as a named hypothesis. fileciteturn35file0L4-L4

### `homit`

This is the omitted-vertex witness for strict decrease:

```lean
homit :
  ∃ w : M.Vertex,
    w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne)
```

Then `sideVertexToM₁_injective_canonical` plus `card_lt_of_injective_of_not_mem_range` gives:

```lean
Fintype.card (data.sideMap₁ hsep a₀ a₁ hne).Vertex < Fintype.card M.Vertex
```

The intended source of `w` is an internal vertex of the **opposite** boundary arc. `ChordSplitData` already has internal-arc witnesses:

```lean
arc₁_internal : data.arc.path₁.HasInternalVertex
arc₂_internal : data.arc.path₂.HasInternalVertex
```

but converting “opposite arc internal vertex” into “not in the image of sideVertexToM₁” is again confinement/Jordan content, hence `homit`. filecite

### Discharge route from `separates_closed` / `jordan_simple_cycle2_unconditional`

The eventual producer should be a `RegionConfinement`-style theorem, not part of `ZinanCh35Iota`:

```lean
structure Side₁Confinement
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop where
  hreflect :
    ∀ {x y : S.Vertex},
      M.Adj (ι x) (ι y) → S.Adj x y
  homit :
    ∃ w : M.Vertex, w ∉ Set.range ι
```

Then prove:

```lean
theorem side₁Confinement_of_jordan
    (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (hjordan : jordan_simple_cycle2_unconditional data hsep)
    (hclosed : separates_closed data hsep hjordan) :
    Side₁Confinement data hsep
```

The logic:

1. `jordan_simple_cycle2_unconditional` gives the chord ∪ boundary-arc simple primal cycle.
2. `separates_closed` says side-1-region vertices and side-1 interior edges are confined to the corresponding closed disk.
3. For `hreflect`, take an ambient `M` edge between two `ι`-images. If it crosses the separating cycle, it must be a seam edge; if it lies inside the side-1 closed disk, it is represented by a side dart; if it is the chord, it is represented by the fresh dart.
4. For `homit`, take an internal vertex of the opposite arc, from `data.arc₂_internal` for side 1. `separates_closed` proves it is outside the side-1 image.

---

## 4. Ordered bricks

### A. Outer trace supplier

1. **`side₁_chordPred_notSameCycle_canonical`** — worker, already in `ZinanCh35OuterTrace`, about 70–100 lines.  
   Uses `side₁AnchorsShareFace_canonical` and `notSameCycle_swap_mul_left_of_sameCycle`.

2. **`side₁_face₁_not_outer_canonical`** — worker, already in `ZinanCh35OuterTrace`, about 25–45 lines.  
   Uses `side₁_chord0_face_eq_face₁_canonical`, `chordOrbits_eq_iff_tracePhi`, and brick A1.

3. **`side₁OuterTraceData_canonical`** — supplier/master, 40–80 lines.  
   Inputs: `hsimple`, `arcSplit`, `outer_simple`, `outer_len`, `inner_reps`.  
   Defines `outerFace := S.dartFace (Sum.inr 1)` and `outerCycle := S.boundaryCycleOfFace ...`.

4. **`contiguousInterval_canonical_of_outerTrace`** — already downstream in `ZinanCh35Hclass`, 10–20 lines.  
   Feed `out` into `side1_hclass_canonical` and then `contiguousInterval_of_correctAnchor`.

### B. Iota / confinement

5. **`sideVertexToM₁_injective_canonical`** — worker, landed in `ZinanCh35Iota`, 40–70 lines.  
   Pure orbit quotient proof.

6. **`sideVertexToM₁_adj_canonical`** — worker, landed modulo `hchord`, 50–90 lines.  
   Side adjacency implies ambient adjacency.

7. **`side₁Confinement_of_jordan`** — new confinement supplier, 150–250 lines.  
   Produces `hreflect` and `homit` from `jordan_simple_cycle2_unconditional` + `separates_closed`.

8. **`chordSideResidue₁_partial`** — master, landed modulo `hchord`, `hreflect`, `hLₛ`, `homit`.  
   Packages via `ChordSplitFinal.chordSideResidue_mk`; the file header identifies exactly these as the remaining inputs. -cut audit

The adjacent-endpoint cut is excluded upstream by:

```lean
data.chord : hNT.outerCycle.Chord u v
```

specifically the field used as

```lean
data.chord.not_boundary_edge
```

This prevents `s(u,v)` from being an old boundary edge. The data layer also stores:

```lean
data.arc₁_internal
data.arc₂_internal
```

so each of the two old boundary arcs has an internal vertex. Thus the side outer boundary has at least one old arc dart plus the fresh chord dart, and the intended `outer_len ≥ 3` is consistent; in the actual supplier it is still passed as `outer_len`, because the repo treats normalized boundary-cycle length as planar boundary data rather than deriving it from raw `CombMap`.
