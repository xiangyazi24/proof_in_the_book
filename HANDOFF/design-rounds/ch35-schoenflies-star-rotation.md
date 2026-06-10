## 1. Answer to the key question

Yes, the right local mechanism is a **rotation-at-a-vertex argument**, but with one important correction:

```lean
data.Separates
```

alone must **not** appear as the only hypothesis of

```lean
vertexStar_confined_of_separates
```

because your worker already verified it is only face-dual separation. The theorem should instead be named something like:

```lean
vertexStar_confined_of_schoenflies
```

or

```lean
vertexStar_confined_of_cycleBanks
```

and consume the landed primal-cycle/bank data:

```lean
jordan_simple_cycle2_unconditional
separates_closed
gateCompat'
crossBankBridge_of_dualReachable
```

The proof shape is exactly what you described: at each vertex, the `σ`-orbit is the cyclic order of incident darts/faces; the simple cycle contributes either `0` or `2` cut darts at that vertex; away from those cut darts, adjacent faces in the star are connected by a non-boundary, non-chord dual step, so side-membership cannot change. Thus the side-1 star is a contiguous bank interval.

---

## 2. The central abstraction

Do **not** try to prove `hreflect` and `homit` separately from low-level rotation lemmas. Package the missing content as one structure:

```lean
structure Side₁SchoenfliesConfinement
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop where
  /-- Any ambient edge whose two endpoints are in the side-1 vertex region
      is either represented in the side-1 carve or is the chord/fresh seam. -/
  edge_confined :
    ∀ {e : D},
      M.tail e ∈ sideRegion₁ data →
      M.head e ∈ sideRegion₁ data →
        ((e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁) ∨
          M.dartEdge e = s(u, v))

  /-- A strict internal vertex of the opposite boundary arc is omitted by side 1. -/
  opposite_arc_omitted :
    ∀ {w : M.Vertex},
      w ∈ data.arc.path₂.internalVertices →
        w ∉ sideRegion₁ data
```

This is the clean lever. Then:

```lean
hreflect
```

is obtained from `edge_confined`, and

```lean
homit
```

is obtained from `opposite_arc_omitted` plus `data.arc₂_internal`.

---

## 3. Star API

Define local star darts:

```lean
abbrev StarDart (M : CombMap D) (x : M.Vertex) : Type u :=
  {d : D // M.tail d = x}
```

The vertex rotation:

```lean
noncomputable def starSigma (M : CombMap D) (x : M.Vertex) :
    Equiv.Perm (StarDart M x) where
  toFun d := ⟨M.σ d.1, by
    rw [M.tail_sigma, d.2]⟩
  invFun d := ⟨M.σ⁻¹ d.1, by
    have h := M.tail_sigma (M.σ⁻¹ d.1)
    rw [Equiv.Perm.apply_inv_self] at h
    rw [← h, d.2]⟩
  left_inv := by
    intro d
    ext
    simp
  right_inv := by
    intro d
    ext
    simp
```

The face seen at a star dart:

```lean
def starFace (x : M.Vertex) (d : StarDart M x) : M.Face :=
  M.dartFace d.1
```

Core local identity:

```lean
lemma starFace_next_eq_alpha
    (x : M.Vertex) (d : StarDart M x) :
    starFace x (starSigma M x d) = M.dartFace (M.α d.1) := by
  -- uses φ = σ * α, i.e. the next dart around the vertex corresponds
  -- to the opposite face across the edge d.
```

Then package the local dual step:

```lean
lemma starStep_chordSplitAdj_of_not_seam
    (data : hNT.ChordSplitData u v)
    {x : M.Vertex} (d : StarDart M x)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d.1))
    (hc : M.dartEdge d.1 ≠ s(u, v)) :
    hNT.ChordSplitAdj u v
      (starFace x d)
      (starFace x (starSigma M x d)) := by
  refine ⟨d.1, rfl, ?_, hb, hc⟩
  exact starFace_next_eq_alpha x d
```

And the side-bank invariance step:

```lean
lemma star_side₁_next_iff_of_not_seam
    (data : hNT.ChordSplitData u v)
    {x : M.Vertex} (d : StarDart M x)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d.1))
    (hc : M.dartEdge d.1 ≠ s(u, v)) :
    starFace x d ∈ data.side₁ ↔
      starFace x (starSigma M x d) ∈ data.side₁ := by
  constructor
  · intro h
    exact data.side₁_closed h
      (starStep_chordSplitAdj_of_not_seam data d hb hc)
  · intro h
    exact data.side₁_closed h
      (hNT.chordSplitAdj_symm
        (starStep_chordSplitAdj_of_not_seam data d hb hc))
```

This is the key purely combinatorial lemma: side membership can change in the vertex rotation only across boundary/chord seam edges.

---

## 4. Cycle darts at a star

Define the cycle-star incidence against the primal cycle `C`:

```lean
def CycleStarDart
    (C : SimplePrimalCycle M)
    (x : M.Vertex) (d : StarDart M x) : Prop :=
  ∃ i : Fin C.len, M.dartEdge d.1 = M.dartEdge (C.dart i)
```

Then:

```lean
noncomputable def cycleStarDarts
    (C : SimplePrimalCycle M) (x : M.Vertex) :
    Finset (StarDart M x) :=
  Finset.univ.filter fun d => CycleStarDart C x d
```

Prove the two basic cardinality workers:

```lean
theorem cycleStarDarts_card_eq_zero_of_not_mem
    (C : SimplePrimalCycle M) {x : M.Vertex}
    (hx : x ∉ C.vertexSet) :
    (cycleStarDarts C x).card = 0
```

and

```lean
theorem cycleStarDarts_card_eq_two_of_mem
    (C : SimplePrimalCycle M) {x : M.Vertex}
    (hx : x ∈ C.vertexSet) :
    (cycleStarDarts C x).card = 2
```

The second proof uses the simple-cycle fields: one cycle edge enters `x`, one leaves `x`, and `tail_inj` / cycle simplicity gives distinctness. Package the result:

```lean
structure StarTwoCuts
    (C : SimplePrimalCycle M) (x : M.Vertex) where
  c₀ : StarDart M x
  c₁ : StarDart M x
  c_ne : c₀ ≠ c₁
  cuts_iff :
    ∀ d : StarDart M x,
      CycleStarDart C x d ↔ d = c₀ ∨ d = c₁
```

Then:

```lean
noncomputable def starTwoCuts_of_cycle_mem
    (C : SimplePrimalCycle M) {x : M.Vertex}
    (hx : x ∈ C.vertexSet) :
    StarTwoCuts C x
```

Use this instead of repeatedly manipulating `Finset.card = 2`.

---

## 5. Bank-contiguity statement

Define:

```lean
def StarSide₁
    (data : hNT.ChordSplitData u v)
    {x : M.Vertex} (d : StarDart M x) : Prop :=
  starFace x d ∈ data.side₁
```

Then the usable theorem should be stated as a no-change-between-cuts lemma:

```lean
theorem starSide₁_constant_on_cut_free_walk
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    {x : M.Vertex}
    {d₀ d₁ : StarDart M x}
    (hwalk :
      RotationArcWithoutCuts (starSigma M x)
        (CycleStarDart C x) d₀ d₁) :
    StarSide₁ data d₀ ↔ StarSide₁ data d₁
```

Where `RotationArcWithoutCuts` should be a small helper structure:

```lean
structure RotationArcWithoutCuts
    {K : Type u} [Fintype K] [DecidableEq K]
    (ρ : Equiv.Perm K) (Cut : K → Prop) (a b : K) : Prop where
  n : ℕ
  end_eq : ρ^[n] a = b
  no_cut :
    ∀ i : Fin n,
      ¬ Cut (ρ^[i.1] a)
```

This avoids needing a full cyclic interval library. The proof is induction on `n`, using `star_side₁_next_iff_of_not_seam`.

Then prove the bank split:

```lean
theorem starSide₁_two_bank_split
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    {x : M.Vertex}
    (cuts : StarTwoCuts C x) :
    ∀ d : StarDart M x,
      StarSide₁ data d →
        SameCutInterval (starSigma M x) cuts.c₀ cuts.c₁ d Side₁Bank
```

Implementation note: you probably do **not** need a sophisticated `SameCutInterval` theorem if the final confinement lemma is stated directly. The more economical route is:

```lean
theorem star_escape_crosses_cycle
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    {x : M.Vertex}
    {dside descape : StarDart M x}
    (hside : StarSide₁ data dside)
    (hescape : ¬ StarSide₁ data descape) :
    ∃ c : StarDart M x,
      CycleStarDart C x c ∧
      RotationArcBetween (starSigma M x) dside descape c
```

This is exactly what is needed: any star path from side bank to far bank crosses a cycle cut.

---

## 6. Master confinement theorem

The master theorem should **not** pretend to follow from `data.Separates` alone. Use this signature:

```lean
theorem vertexStar_confined_of_cycleBanks
    (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (C : SimplePrimalCycle M)
    (hC :
      ChordCycleData data C) -- or whatever landed wrapper names the chord∪arc cycle
    (hclosed :
      SeparatesClosed data hsep C) -- landed separates_closed shape
    (hgate :
      GateCompat' C) -- landed name
    (hbridge :
      CrossBankBridgeOfDualReachable C) :
    Side₁SchoenfliesConfinement data hsep
```

If the landed names are theorem-valued rather than structure-valued, make a small input bundle:

```lean
structure Side₁CycleBankInput
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) where
  C : SimplePrimalCycle M
  chord_cycle : ChordCycleData data C
  closed : SeparatesClosed data hsep C
  gate : GateCompat' C
  cross : CrossBankBridgeOfDualReachable C
```

Then:

```lean
theorem vertexStar_confined_of_cycleBanks
    (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (J : Side₁CycleBankInput data hsep) :
    Side₁SchoenfliesConfinement data hsep
```

Proof outline for `edge_confined`:

```lean
intro e htailRegion hheadRegion
by_cases hchord : M.dartEdge e = s(u,v)
· exact Or.inr hchord
by_cases heKept : e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁
· exact Or.inl heKept
-- Otherwise, one of the two incident faces is outside the side-1 carve.
-- At the star of `M.tail e`, pick a side-1 witness dart from `htailRegion`.
-- Rotate from that witness to `e`.
-- If bank changes, `star_escape_crosses_cycle` gives a cycle edge at that vertex.
-- Use `crossBankBridge_of_dualReachable` / `gateCompat'` to convert the escape
-- into a forbidden dual bridge from face₁ to face₂, contradicting hsep/closed.
```

Proof outline for `opposite_arc_omitted`:

```lean
intro w hwOppArc hwRegion
-- w is internal to opposite arc, so w ≠ u and w ≠ v.
-- The cycle C = chord ∪ side-1 arc does not pass through w.
-- If w ∈ sideRegion₁, choose a side-region star witness.
-- Since w lies on the opposite old boundary arc, its incident boundary-star bank
-- is the far bank. With no cycle cuts at w, `starSide₁_constant_on_cut_free_walk`
-- forces far-bank = side-bank, contradicting separates_closed / bank labeling.
```

This is where `arc₂_internal` is used.

---

## 7. `hreflect` corollary

With confinement packaged, prove:

```lean
theorem hreflect_of_schoenflies
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (H : Side₁SchoenfliesConfinement data hsep) :
    ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj
        (sideVertexToM₁ data hsep a₀ a₁ hne x)
        (sideVertexToM₁ data hsep a₀ a₁ hne y) →
      (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y
```

Proof:

1. Choose an ambient dart `e` witnessing the `M` adjacency.
2. Use upstream:

```lean
sideVertexToM₁_mem data hsep a₀ a₁ hne x
sideVertexToM₁_mem data hsep a₀ a₁ hne y
```

to show both endpoints lie in `sideRegion₁ data`.
3. Apply `H.edge_confined`.
4. If `e` and `M.α e` are kept, the side dart is:

```lean
Sum.inl ⟨e, he⟩
```

and its `α`-mate is also kept; use existing `sideVertexToM₁_*_inl` endpoint lemmas plus injectivity to identify the side vertices with `x,y`.

5. If the edge is the chord, use `Sum.inr 0` or `Sum.inr 1`, plus the canonical anchor endpoint lemmas.

The `ChordSideResidue` structure explicitly expects this `ι_adj_reflect` field. 

---

## 8. `homit` corollary

Use the opposite arc internal vertex.

```lean
theorem homit_of_schoenflies
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (H : Side₁SchoenfliesConfinement data hsep) :
    ∃ w : M.Vertex, w ∉ sideRegion₁ data := by
  obtain ⟨w, hw_mem, hw_ne_start, hw_ne_end⟩ :=
    data.arc.path₂.exists_internal_vertex data.arc₂_internal
  exact ⟨w, H.opposite_arc_omitted hw_mem⟩
```

If the exact theorem is namespaced, use:

```lean
BoundaryPath.exists_internal_vertex data.arc.path₂ data.arc₂_internal
```

The stored fields are:

```lean
data.arc₁_internal
data.arc₂_internal
```

and `BoundaryPath.exists_internal_vertex` gives a listed internal vertex distinct from endpoints.

---

## 9. Final assembler

Once `Side₁SchoenfliesConfinement` is produced, add:

```lean
theorem chordSideResidue₁_of_schoenflies
    (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (L : M.Vertex → Finset α)
    (out : Side₁OuterTraceData data hsep)
    (H : Side₁SchoenfliesConfinement data hsep)
    -- existing inputs: hchord, hLₛ, side p/q/colors, etc.
    :
    ChordSideResidue data hsep
      (side₁Anchor₀ data hsep)
      (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)
      L :=
by
  -- call chordSideResidue₁_partial
  -- hreflect := hreflect_of_schoenflies ...
  -- homit := homit_of_schoenflies ...
```

The two residues consumed by `chordSideResidue₁_partial` should now be generated from the single confinement package.

---

## 10. Ordered brick list

### Brick 1 — Star API  
**Worker, 80–120 lines**

```lean
abbrev StarDart
noncomputable def starSigma
def starFace
lemma starFace_next_eq_alpha
lemma starStep_chordSplitAdj_of_not_seam
lemma star_side₁_next_iff_of_not_seam
```

### Brick 2 — Cycle-star incidence  
**Worker, 120–180 lines**

```lean
def CycleStarDart
noncomputable def cycleStarDarts
theorem cycleStarDarts_card_eq_zero_of_not_mem
theorem cycleStarDarts_card_eq_two_of_mem
structure StarTwoCuts
noncomputable def starTwoCuts_of_cycle_mem
```

### Brick 3 — Cut-free rotation walks  
**Worker, 100–160 lines**

```lean
structure RotationArcWithoutCuts
theorem starSide₁_constant_on_cut_free_walk
theorem star_escape_crosses_cycle
```

### Brick 4 — Side-region/star bridge  
**Worker, 100–180 lines**

```lean
lemma sideRegion₁_has_incident_side₁_face_or_chordEndpoint
lemma sideRegion₁_endpoint_star_witness
lemma opposite_arc_internal_far_bank
```

This is where `sideRegion₁` definition is unfolded.

### Brick 5 — Master confinement package  
**Master, 150–300 lines**

```lean
structure Side₁SchoenfliesConfinement
theorem vertexStar_confined_of_cycleBanks :
  Side₁CycleBankInput data hsep →
  Side₁SchoenfliesConfinement data hsep
```

### Brick 6 — Residue producers  
**Worker, 80–140 lines**

```lean
theorem hreflect_of_schoenflies
theorem homit_of_schoenflies
```

### Brick 7 — Final Ch35 plug-in  
**Master, 20–50 lines**

```lean
theorem chordSideResidue₁_of_schoenflies
```

---

## 11. Degenerate audit

### `x` not on the cycle

Then `cycleStarDarts C x` has cardinality `0`. The star bank cannot change anywhere around the full `σ`-orbit. Thus a side-region vertex cannot have a non-seam edge escaping the side.

### `x = u` or `x = v`

The two cycle darts are the chord edge and one boundary-arc edge. The two cut darts may be adjacent in the rotation. The interval theorem must allow empty intervals.

### Internal vertex of side arc

There are two boundary-cycle darts through the vertex. Again they may be adjacent in the star. The side bank may occupy all non-far-bank darts.

### Internal vertex of opposite arc

This is the `homit` witness. It is not a chord endpoint by `BoundaryPath.internalVertex_ne_start` / `internalVertex_ne_end`. It lies on the far bank, so `opposite_arc_omitted` applies.

### Degree 1 or degree 2

Do not assume degree ≥ 3. The `RotationArcWithoutCuts` formulation works even when the star has one or two darts, because it is just an iterate statement over `starSigma`.

### Adjacent chord endpoints

Killed upstream by:

```lean
data.chord.not_boundary_edge
```

and strengthened by:

```lean
data.arc₁_internal
data.arc₂_internal
```

So the chord is not an old boundary edge and both arcs have genuine internal vertices.
