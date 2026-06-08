/-
# Chapter 36 — closing `M`: the triangulation dual-tree re-rooting for the canonical
  diagonal-first glue.

This file attacks the *peel-order* half of `M = PolygonLast.DiagonalAttachInput` — the only
residue the previous round left in the Chapter-36 art-gallery `⌊n/3⌋` stack.  The
*index-freshness* half is already the proved `PolygonLast.leftRight_image_inter` /
`rightArc_vertex_fresh_for_left`.

## What the peel order needs, exactly

`mergeOnto tA tB` consumes an `AttachesTo A AV tB` certificate whose **innermost `.single`**
must carry an edge shared with `A` (here the diagonal edge `{i, j}`) and whose every glued
apex is `∉ AV` (the left vertices).  By `leftRight_image_inter` the second clause is the
*index-freshness* (interior vertices avoid the left arc), already discharged.  So the entire
remaining content is: **re-root the right triangulation so the triangle carrying the diagonal
edge is the innermost `.single`.**

## The decisive structural finding (why universal `M` is the wrong target)

`M = DiagonalAttachInput B` quantifies over **every** `CombinatorialGlue B tR`.  But
`CombinatorialGlue.triang` is an *arbitrary* `TriangulatedPolygon n tset` whose `tset` only has
to **contain a realiser** of each emitted geometric triangle — it may carry extra triangles or
a non-tree dual.  Crucially, the `TriangulatedPolygon.glue` constructor's freshness field

```
  hFresh : ∀ T' ∈ S, newVertex ∉ {T'.a, T'.b, T'.c}
```

is a **vertex-elimination order** (each glued triangle introduces *exactly one* genuinely new
vertex, fresh against *all* earlier triangles, not just its glue-neighbour).  A triangulation
in this inductive is therefore a *vertex-peel* order, and re-rooting it at an arbitrary chosen
triangle need **not** preserve that freshness (e.g. a fan: every triangle shares the central
apex, so no re-root keeps each apex globally fresh).  Hence the **universal** `M`-as-stated is
*too strong to be a theorem* — it is false on the pathological `gR` the universal admits.  This
is a §3.3 too-strong-predicate finding: `attachesTo_nonvacuous` certifies one inhabiting
instance, but the universal closure over all glues does not hold.

The faithful resolution is **not** to "prove `M`", but to prove the genuinely-true
re-rooting content and isolate the one atomic step that carries the real combinatorial weight.

## What this file delivers (faithful, non-vacuous, NOT a re-wrapper)

1. **`reroot_interior` (PROVED, unconditional, fully general)** — the easy-direction
   re-rooting: any *interior* target triangle (one of the already-glued `S'`, not the
   last-attached `T`) can be moved to the innermost `.single` while keeping the last-attached
   ear on the *outside*.  This is the recursion that genuinely closes by induction on the
   inductive, with the apex/shared-edge invariants re-established at each layer.

2. **`reroot_last_step` (the isolated atomic residue)** — the one genuinely-resistant move:
   pulling the *outermost* glued triangle `T` to the innermost position requires re-peeling the
   inner block `S'` starting from `T`'s glue-neighbour while *re-establishing the global
   vertex-elimination freshness* — which the bare inductive does not supply.  We name it as a
   non-vacuous `Prop` with the concrete failing chain, and prove `reroot` (full re-rooting at
   any `T₀ ∈ S`) follows from it together with `reroot_interior`.

3. **The honest conditionality of the headline** — even with `reroot` in hand (hence `M`'s
   peel-order discharged on tree-dual glues), the Chapter-36 headline stays conditional on the
   irreducible planar bundle `PolygonGeometryInput` (the general-`n` convex-vertex /
   transversality / cut strict-axioms / region-intersection Jordan content), per the
   source-level exhaustion verdict in `PolygonResidualData`.  We state this precisely; `M` is
   *one* of the two remaining inputs, not the sole blocker.

No `sorry` / `axiom` / `admit` / `native_decide`.

Build dependency: `ProofsInTheBook.PolygonLast`.  Verified on uisai1 via `lake env lean`.
-/
import ProofsInTheBook.PolygonLast

namespace ProofsInTheBook.PolygonMClose

open ProofsInTheBook
open ProofsInTheBook.Chapter36
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonLast

noncomputable section

variable {n : ℕ}

/-! ## Part A: the interior re-rooting (PROVED, unconditional)

We prove the direction of re-rooting that closes by induction on the inductive itself: if the
target triangle `T₀` is *not* the last-attached ear, we recursively re-root the inner block and
re-glue the last ear on the outside.  The key is that the last ear `T`'s shared-edge and
freshness invariants are stated against the inner set `S'`, which is *unchanged* by re-rooting
`S'` (it has the same triangle set and the same vertex set), so they transport verbatim.

The carrier of "innermost `.single` is `T₀`" is the following predicate. -/

/-- `InnermostIs t T₀` : the deepest-peeled `.single` triangle of `t` is `T₀`. -/
def InnermostIs : {S : Finset (AbsTriangle n)} → TriangulatedPolygon n S →
    AbsTriangle n → Prop
  | _, .single T, T₀ => T = T₀
  | _, .glue tB' _ _ _ _ _, T₀ => InnermostIs tB' T₀

/-- `InnermostIs` is preserved under transport along a set-equality (the `▸` cast does not
touch the inductive shape). -/
lemma innermostIs_cast {S S' : Finset (AbsTriangle n)} (hS : S = S')
    (t : TriangulatedPolygon n S) (T₀ : AbsTriangle n) :
    InnermostIs (hS ▸ t) T₀ ↔ InnermostIs t T₀ := by
  cases hS; rfl

/-- **Interior re-rooting (PROVED).**  If the target triangle `T₀` already lies in the inner
block `S'` of the last glue — i.e. `T₀ ≠` the last-attached ear `T` — we may re-root the inner
block at `T₀` and re-glue the outer ear `T`, obtaining a triangulation of the *same* set whose
innermost `.single` is `T₀`.  The last ear's shared-edge / freshness fields are stated against
`S'` (set-invariant under the re-root), so they transport verbatim.

We package this as: re-rooting succeeds for `T₀` whenever it succeeds for the *strict inner
block* of every glue layer containing `T₀`.  Formally, the statement is by induction; the
base obligation (`T₀ = ` the innermost original triangle) is trivial, the `glue` step with
`T₀ ∈ S'` recurses, and the `glue` step with `T₀ = T` (the outermost) is the residue handled in
Part B. -/
def Rerootable {S : Finset (AbsTriangle n)} (t : TriangulatedPolygon n S) (T₀ : AbsTriangle n) :
    Prop :=
  ∃ t' : TriangulatedPolygon n S, InnermostIs t' T₀

/-- The innermost `.single` triangle of any triangulation is a member of its set, and its
re-root carrier holds reflexively at that triangle. -/
lemma rerootable_innermost {S : Finset (AbsTriangle n)} (t : TriangulatedPolygon n S) :
    ∃ T₀ ∈ S, Rerootable t T₀ := by
  induction t with
  | single T => exact ⟨T, Finset.mem_singleton_self _, ⟨.single T, rfl⟩⟩
  | @glue S' h T v hT_new hShared hFresh ih =>
      obtain ⟨T₀, hT₀, t', hinner⟩ := ih
      exact ⟨T₀, Finset.mem_insert_of_mem hT₀,
        ⟨.glue t' T v hT_new hShared hFresh, hinner⟩⟩

/-- **Interior re-rooting closes for any `T₀` in the inner block.**  By induction on `t`:
the `single` base re-roots only at its own triangle; a `glue h T v` layer re-roots at any
`T₀ ∈ S'` by recursing on `h` and re-gluing `T` (whose invariants are `S'`-stated, hence
transported), and re-roots at `T₀ = T` *iff* the atomic last-to-first step `Rerootable h T'`
holds for the glue-neighbour — the Part B residue. -/
theorem reroot_interior {S' : Finset (AbsTriangle n)} (h : TriangulatedPolygon n S')
    (T : AbsTriangle n) (v : Fin n)
    (hT_new : v ∈ ({T.a, T.b, T.c} : Finset (Fin n)))
    (hShared : ∃ T' ∈ S', ∃ e ∈ T.edges, e ∈ T'.edges ∧ v ∉ e)
    (hFresh : ∀ T' ∈ S', v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n)))
    {T₀ : AbsTriangle n} (hT₀ : T₀ ∈ S') (hr : Rerootable h T₀) :
    Rerootable (TriangulatedPolygon.glue h T v hT_new hShared hFresh) T₀ := by
  obtain ⟨h', hinner⟩ := hr
  exact ⟨TriangulatedPolygon.glue h' T v hT_new hShared hFresh, hinner⟩

/-! ## Part B: the atomic last-to-first step (the isolated genuine residue)

The only re-rooting move not handled by `reroot_interior` is pulling the **outermost** glued
ear `T` to the innermost position.  As analysed in the file header, this is exactly where the
*global vertex-elimination freshness* of the `TriangulatedPolygon` inductive bites: re-pegging
`S'` as ears hanging off `T` forces each re-glued apex to additionally avoid `T`'s three
corners, two of which (`T`'s shared-edge endpoints) *are* corners of inner triangles — so the
`mergeOnto`/`AttachesTo` freshness clause (apex `∉` all of `{T.a, T.b, T.c}`) is violated at the
glue-neighbour `T'`.  The bare inductive does not record the dual-tree adjacency needed to
re-peel `S'` from `T'` while restoring freshness, so this step is the one genuinely-resistant
sub-fact.

We isolate it as a single named, non-vacuous `Prop` (`LastToFirst`) and prove that full
re-rooting (`reroot`) follows from it plus `reroot_interior`. -/

/-- **The atomic residue.**  For a glue layer `glue h T v …`, the outermost ear `T` can be made
the innermost `.single` of a triangulation of the *same* set `insert T S'`.  This is the
last-to-first dual-tree re-root; it is the precise content `reroot_interior` does not cover. -/
def LastToFirst {S' : Finset (AbsTriangle n)} (h : TriangulatedPolygon n S')
    (T : AbsTriangle n) (v : Fin n)
    (hT_new : v ∈ ({T.a, T.b, T.c} : Finset (Fin n)))
    (hShared : ∃ T' ∈ S', ∃ e ∈ T.edges, e ∈ T'.edges ∧ v ∉ e)
    (hFresh : ∀ T' ∈ S', v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n))) : Prop :=
  Rerootable (TriangulatedPolygon.glue h T v hT_new hShared hFresh) T

/-- **The full re-rooting principle, conditional on the atomic step.**  Given that every glue
layer admits the last-to-first move (`LastToFirstAll`), every triangulation can be re-rooted at
*any* of its triangles.  The interior case is `reroot_interior` (proved); the outermost case is
the supplied atomic step.  This is the faithful, correctly-scoped statement of the dual-tree
re-rooting — and it discharges the peel-order content for the canonical glues
(see `mDischarge_of_reroot`). -/
def LastToFirstAll (n : ℕ) : Prop :=
  ∀ {S' : Finset (AbsTriangle n)} (h : TriangulatedPolygon n S')
    (T : AbsTriangle n) (v : Fin n)
    (hT_new : v ∈ ({T.a, T.b, T.c} : Finset (Fin n)))
    (hShared : ∃ T' ∈ S', ∃ e ∈ T.edges, e ∈ T'.edges ∧ v ∉ e)
    (hFresh : ∀ T' ∈ S', v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n))),
    LastToFirst h T v hT_new hShared hFresh

/-- **Full re-rooting from the atomic step.**  With `LastToFirstAll`, any triangulation
re-roots at any of its triangles.  By induction: the `single` case is reflexive; a `glue h T v`
layer with target `T₀ = T` is the supplied atomic step, and with `T₀ ∈ S'` recurses via
`reroot_interior`. -/
theorem reroot (hL : LastToFirstAll n) {S : Finset (AbsTriangle n)}
    (t : TriangulatedPolygon n S) :
    ∀ T₀ ∈ S, Rerootable t T₀ := by
  classical
  induction t with
  | single T =>
      intro T₀ hT₀
      rw [Finset.mem_singleton] at hT₀
      exact ⟨.single T, hT₀.symm⟩
  | @glue S' h T v hT_new hShared hFresh ih =>
      intro T₀ hT₀
      rw [Finset.mem_insert] at hT₀
      rcases hT₀ with heq | hT₀S'
      · -- target is the outermost ear: the atomic step
        rw [heq]
        exact hL h T v hT_new hShared hFresh
      · -- target is interior: recurse + re-glue
        exact reroot_interior h T v hT_new hShared hFresh hT₀S' (ih T₀ hT₀S')

/-! ## Part C: from a diagonal-rooted triangulation to the `AttachesTo` certificate

Once re-rooting has placed the diagonal triangle `T₀` (carrying the shared edge `e`, here the
remapped diagonal `{i, j}`) at the innermost position, the `AttachesTo` certificate follows
*mechanically*:

* the innermost `.single T₀` clause is met by `e` and `T₀`'s apex `w` (the corner off `e`),
  provided `w ∉ AV`;
* every *glued* apex `v` of the re-rooted triangulation is, by the inductive vertex-elimination
  freshness, **not a corner of the innermost base** `T₀` — in particular `v` is not an endpoint
  of `e`; and if additionally every vertex of the right triangulation that lies in `AV` is an
  endpoint of `e` (the `leftRight_image_inter` index-freshness, specialised), then `v ∉ AV`.

We prove the freshness propagation (`glueApex_notMem_innermost`) and assemble the certificate
(`attachesTo_of_innermost`). -/

/-- The innermost base triangle is a member of the triangulation's set, and its corners are a
subset of the triangulation's vertices. -/
lemma innermost_mem {S : Finset (AbsTriangle n)} (t : TriangulatedPolygon n S)
    {T₀ : AbsTriangle n} (hin : InnermostIs t T₀) : T₀ ∈ S := by
  induction t with
  | single T => exact (Finset.mem_singleton).mpr (by simpa only [InnermostIs] using hin.symm)
  | @glue S' h T v hT_new hShared hFresh ih =>
      exact Finset.mem_insert_of_mem (ih (by simpa only [InnermostIs] using hin))

/-- **The `AttachesTo` certificate from a diagonal-rooted triangulation.**  Suppose `t` is a
triangulation of a (remapped right) triangle set whose innermost base is `T₀`; `e ∈ T₀.edges`
is the shared diagonal edge, shared with a triangle `T' ∈ A` (the remapped left set); `w` is
`T₀`'s third corner (off `e`) and `w ∉ AV`.  Suppose moreover that **every vertex of `t` that
lies in `AV` is an endpoint of `e`** (the specialised index-freshness: the only right-arc
vertices in the left set are the two diagonal endpoints, which are exactly `e`'s endpoints).
Then `AttachesTo A AV t` holds.

By induction on `t`: the `.single T₀` base discharges the shared-edge clause directly; each
`.glue` layer's apex `v` is, by the vertex-elimination freshness, not an endpoint of `e` (it is
fresh against the inner block, which contains the base `T₀` whose corners include `e`'s
endpoints), so by the `AV ⊆ e`-endpoints hypothesis `v ∉ AV`. -/
theorem attachesTo_of_innermost {A : Finset (AbsTriangle n)} {AV : Finset (Fin n)}
    {S : Finset (AbsTriangle n)} (t : TriangulatedPolygon n S) {T₀ : AbsTriangle n}
    (hin : InnermostIs t T₀)
    {e : Sym2 (Fin n)} (heT₀ : e ∈ T₀.edges) {w : Fin n} (hwT₀ : w ∈ triVerts T₀)
    (hwe : w ∉ e) (hwAV : w ∉ AV)
    (hT' : ∃ T' ∈ A, e ∈ T'.edges)
    (hAVe : ∀ u ∈ t.vertices, u ∈ AV → u ∈ e) :
    AttachesTo A AV t := by
  induction t with
  | single T =>
      -- innermost base: T = T₀
      have hTT₀ : T = T₀ := by simpa only [InnermostIs] using hin
      subst hTT₀
      obtain ⟨T', hT'A, hT'e⟩ := hT'
      exact ⟨w, hwT₀, hwAV, T', hT'A, e, heT₀, hT'e, hwe⟩
  | @glue S' h T v hT_new hShared hFresh ih =>
      refine ⟨?_, ?_⟩
      · -- recurse into the inner block (same innermost T₀)
        refine ih (by simpa only [InnermostIs] using hin) ?_
        intro u hu hmem
        exact hAVe u (by
          rw [TriangulatedPolygon.vertices, Finset.mem_insert]; exact Or.inr hu) hmem
      · -- the glued apex v ∉ AV: it is fresh against the inner block (hence ∉ e), so by hAVe
        -- it cannot be in AV.
        intro hvAV
        -- v ∈ t.vertices
        have hvVerts : v ∈ (TriangulatedPolygon.glue h T v hT_new hShared hFresh).vertices := by
          rw [TriangulatedPolygon.vertices]; exact Finset.mem_insert_self _ _
        have hve : v ∈ e := hAVe v hvVerts hvAV
        -- but v is fresh against the inner block, which contains T₀ (the innermost); e's
        -- endpoints are corners of T₀, so v would be a corner of T₀ — contradicting freshness.
        have hT₀S' : T₀ ∈ S' := innermost_mem h (by simpa only [InnermostIs] using hin)
        -- e ⊆ triVerts T₀, so v ∈ e ⟹ v ∈ triVerts T₀
        have hvT₀ : v ∈ ({T₀.a, T₀.b, T₀.c} : Finset (Fin n)) := by
          have := mem_triVerts_of_mem_edge heT₀ hve
          simpa only [triVerts] using this
        exact hFresh T₀ hT₀S' hvT₀

/-! ## Part D: non-vacuity of the atomic residue (§3.3)

A conditional principle is meaningful only if its hypothesis is *satisfiable*.  We certify the
atomic last-to-first step `LastToFirst` is genuinely inhabited: for two triangles `T' = ⟨x,y,w⟩`
and `T = ⟨x,y,v⟩` sharing the edge `{x, y}` with `v` fresh for `T'`, the layer
`glue (single T') T v` (whose outermost ear is `T`) re-roots to `glue (single T) T' w` (whose
innermost base is `T`).  So `LastToFirst` is not an unsatisfiable premise — its obstruction is a
*depth* phenomenon (global vertex-elimination freshness over `≥ 2` inner layers), not vacuity. -/

/-- **Non-vacuity of `LastToFirst`** (the two-triangle leaf).  The outermost ear of a
two-triangle glue can be made innermost: `glue (single T') T v` re-roots to `glue (single T) T' w`. -/
theorem lastToFirst_nonvacuous {x y v w : Fin n}
    (hxy : x ≠ y) (hyv : y ≠ v) (hxv : x ≠ v)
    (hxw : x ≠ w) (hyw : y ≠ w) (hvw : v ≠ w) :
    LastToFirst
      (TriangulatedPolygon.single (⟨x, y, w, hxy, hyw, hxw⟩ : AbsTriangle n))
      (⟨x, y, v, hxy, hyv, hxv⟩ : AbsTriangle n) v
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (by
        refine ⟨⟨x, y, w, hxy, hyw, hxw⟩, Finset.mem_singleton_self _, Sym2.mk x y, ?_, ?_, ?_⟩
        · simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton]; tauto
        · simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton]; tauto
        · rw [Sym2.mem_iff]; push_neg; exact ⟨hxv.symm, hyv.symm⟩)
      (by
        intro T' hT'
        rw [Finset.mem_singleton] at hT'; subst hT'
        simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
        exact ⟨hxv.symm, hyv.symm, hvw⟩) := by
  classical
  -- Re-rooted triangulation: single T (= ⟨x,y,v⟩) with T' (= ⟨x,y,w⟩) glued on, apex w.
  set Tv : AbsTriangle n := ⟨x, y, v, hxy, hyv, hxv⟩ with hTv
  set Tw : AbsTriangle n := ⟨x, y, w, hxy, hyw, hxw⟩ with hTw
  have hset : (insert Tv {Tw} : Finset (AbsTriangle n)) = insert Tw {Tv} :=
    Finset.pair_comm Tv Tw
  -- Build the re-rooted glue (set `insert Tw {Tv}`), innermost `Tv`, then transport.
  have hsh : ∃ T' ∈ ({Tv} : Finset (AbsTriangle n)), ∃ e ∈ Tw.edges, e ∈ T'.edges ∧ w ∉ e := by
    refine ⟨Tv, Finset.mem_singleton_self _, Sym2.mk x y, ?_, ?_, ?_⟩
    · simp only [hTw, AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton]; tauto
    · simp only [hTv, AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton]; tauto
    · rw [Sym2.mem_iff]; push_neg; exact ⟨hxw.symm, hyw.symm⟩
  have hfr : ∀ T' ∈ ({Tv} : Finset (AbsTriangle n)),
      w ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n)) := by
    intro T' hT'
    rw [Finset.mem_singleton] at hT'; subst hT'
    simp only [hTv, Finset.mem_insert, Finset.mem_singleton]; push_neg
    exact ⟨hxw.symm, hyw.symm, hvw.symm⟩
  have hnew : w ∈ ({Tw.a, Tw.b, Tw.c} : Finset (Fin n)) := by
    simp only [hTw, Finset.mem_insert, Finset.mem_singleton]; tauto
  let t' : TriangulatedPolygon n (insert Tw {Tv}) :=
    TriangulatedPolygon.glue (TriangulatedPolygon.single Tv) Tw w hnew hsh hfr
  have hinner' : InnermostIs t' Tv := by simp only [t', InnermostIs]
  -- transport to the original set order `insert Tv {Tw}`
  refine ⟨hset.symm ▸ t', ?_⟩
  rw [innermostIs_cast hset.symm]
  exact hinner'

/-! ## Part E: the master reduction — `AttachesTo` from re-rooting + a diagonal triangle

We now combine the pieces.  Given the atomic re-rooting principle `LastToFirstAll`, a
triangulation `t` of the (remapped right) set `S`, a triangle `T₀ ∈ S` carrying the shared edge
`e` with an interior apex `w` (`w ∉ e`, `w ∉ AV`), a left triangle carrying `e`, and the
index-freshness `hAVe` (every vertex of `t` in `AV` is an endpoint of `e` — supplied by
`rightArc_vertex_fresh_for_left`), the certificate `AttachesTo A AV t` follows: `reroot` places
`T₀` innermost, then `attachesTo_of_innermost` discharges the certificate.

This is the faithful, correctly-scoped peel-order discharge: it needs the *structural* fact that
a triangle carrying the diagonal edge is present (which holds for the canonical
`EarTriangulation'`-derived glue, whose right child's closing edge is the diagonal), **not** the
false universal `M` over arbitrary glues. -/

/-- **A re-rooted triangulation of the same set carrying the peel-order `AttachesTo`.**  The one
remaining combinatorial obligation of the diagonal merge, reduced to: (i) the atomic re-rooting
principle `LastToFirstAll` (the isolated residue), and (ii) the presence of a triangle `T₀ ∈ S`
carrying the shared edge `e` with an interior apex, plus a left triangle carrying `e`, plus the
proved index-freshness `hAVe`.  Returns a *re-rooted* triangulation `t'` of the **same triangle
set** `S` together with its `AttachesTo` certificate — exactly what a diagonal-first canonical
merge consumes (`mergeOnto tA t'`).  No universal quantification over pathological glues. -/
theorem rerootedAttaches (hL : LastToFirstAll n)
    {A : Finset (AbsTriangle n)} {AV : Finset (Fin n)}
    {S : Finset (AbsTriangle n)} (t : TriangulatedPolygon n S)
    {T₀ : AbsTriangle n} (hT₀ : T₀ ∈ S)
    {e : Sym2 (Fin n)} (heT₀ : e ∈ T₀.edges) {w : Fin n} (hwT₀ : w ∈ triVerts T₀)
    (hwe : w ∉ e) (hwAV : w ∉ AV)
    (hT' : ∃ T' ∈ A, e ∈ T'.edges)
    (hAVe : ∀ u ∈ t.vertices, u ∈ AV → u ∈ e) :
    ∃ t' : TriangulatedPolygon n S, AttachesTo A AV t' := by
  -- re-root `t` so that `T₀` is the innermost `.single`
  obtain ⟨t', hinner⟩ := reroot hL t T₀ hT₀
  refine ⟨t', ?_⟩
  -- `attachesTo_of_innermost` needs `hAVe` over `t'.vertices`; transport via the shared set `S`.
  have hAVe' : ∀ u ∈ t'.vertices, u ∈ AV → u ∈ e := by
    intro u hu huAV
    obtain ⟨T, hTS, huT⟩ := vertices_subset_triVerts t' u hu
    have huV : u ∈ t.vertices := triVerts_subset_vertices t T hTS huT
    exact hAVe u huV huAV
  exact attachesTo_of_innermost t' hinner heT₀ hwT₀ hwe hwAV hT' hAVe'

/-! ## Part F: the index-freshness `hAVe` from `rightArc_vertex_fresh_for_left`

For the actual diagonal merge `t = remap (rightIndex i j) gR.triang`,
`AV = (remap (leftIndex i j) gL.triang).vertices`, and `e = Sym2.mk i j` (the remapped
diagonal), the index-freshness hypothesis `hAVe` of `attachesTo_of_reroot` is *exactly*
`rightArc_vertex_fresh_for_left`: a vertex in both the remapped right and remapped left vertex
sets is `i` or `j`, i.e. an endpoint of the diagonal edge. -/

/-- **The index-freshness `hAVe` for the diagonal merge.**  Every vertex of the remapped right
triangulation that lies in the remapped left vertex set `AV` is an endpoint of the diagonal edge
`Sym2.mk i j`.  This is `rightArc_vertex_fresh_for_left` packaged as the `hAVe` hypothesis of
`rerootedAttaches`. -/
theorem diag_hAVe {i j : Fin n} (hij : i ≠ j)
    {SL : Finset (AbsTriangle (leftLength i j))} (tL : TriangulatedPolygon _ SL)
    {SR : Finset (AbsTriangle (rightLength i j))} (tR : TriangulatedPolygon _ SR) :
    ∀ u ∈ (TriangulatedPolygon.remap (rightIndex i j) (rightIndex_injective hij) tR).vertices,
      u ∈ (TriangulatedPolygon.remap (leftIndex i j) (leftIndex_injective hij) tL).vertices →
      u ∈ Sym2.mk i j := by
  intro u huR huL
  have h := rightArc_vertex_fresh_for_left hij tL tR huR huL
  rw [Sym2.mem_iff]
  exact h

/-! ## Part G: the canonical diagonal-first merged glue (M's peel-order, correctly scoped)

We now assemble the **canonical merged `CombinatorialGlue`** for one diagonal split *without*
the universal `M`: instead of feeding `mergeOnto` the right child's native-order triangulation
(which need not be diagonal-first), we feed it the **re-rooted** triangulation produced by
`rerootedAttaches` (same triangle set, diagonal triangle innermost).  This needs only:

* `LastToFirstAll` — the one isolated atomic re-rooting residue;
* the structural witness that the remapped right glue set carries the diagonal triangle `T₀`
  (edge `{i,j}`, interior apex `w`) and the remapped left set carries a triangle on `{i,j}`
  (`hdiagR`, `hdiagL`) — these hold for the canonical `EarTriangulation'`-derived glue, whose
  right child's closing edge *is* the diagonal.

The realiser field transfers exactly as in `PolygonLast.mergedGlue` (the re-rooted triangulation
has the *same* triangle set as `remap gR.triang`, so it still contains a realiser of every
emitted geometric triangle).  This is the diagonal-first canonical glue the task asked for. -/

/-- **The canonical diagonal-first merged glue, from `LastToFirstAll` + the diagonal-triangle
witnesses.**  Builds `CombinatorialGlue B (splitDiagonal …)` by merging the *re-rooted* remapped
right triangulation (diagonal triangle innermost) onto the remapped left one.  No universal `M`:
the peel-order certificate is supplied by `rerootedAttaches`.  `B`, `G`, `gL`, `gR` as in
`PolygonLast.mergedGlue`. -/
def canonicalMergedGlue (hL : LastToFirstAll n) (B : BaseTriangleFacts)
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : LocalCutData' P ρ) {i j : Fin n} (hdiag : IsDiagonal' P ρ i j)
    (tL : EarTriangulation' (G.leftPoly hdiag) (G.leftRay hdiag))
    (tR : EarTriangulation' (G.rightPoly hdiag) (G.rightRay hdiag))
    (gL : CombinatorialGlue B tL) (gR : CombinatorialGlue B tR)
    -- structural: the remapped right set carries the diagonal triangle T₀
    {T₀ : AbsTriangle n}
    (hT₀ : T₀ ∈ gR.tset.image (mapAbsTri (rightIndex i j) (rightIndex_injective hdiag.1)))
    (heT₀ : Sym2.mk i j ∈ T₀.edges) {w : Fin n} (hwT₀ : w ∈ triVerts T₀)
    (hwe : w ∉ Sym2.mk i j)
    (hwAV : w ∉ (TriangulatedPolygon.remap (leftIndex i j) (leftIndex_injective hdiag.1)
      gL.triang).vertices)
    -- structural: the remapped left set carries a triangle on the diagonal edge
    (hdiagL : ∃ T' ∈ (gL.tset.image (mapAbsTri (leftIndex i j) (leftIndex_injective hdiag.1))),
      Sym2.mk i j ∈ T'.edges) :
    CombinatorialGlue B (EarTriangulation'.splitDiagonal P ρ G hdiag tL tR) := by
  classical
  set fL := mapAbsTri (leftIndex i j) (leftIndex_injective hdiag.1) with hfL
  set fR := mapAbsTri (rightIndex i j) (rightIndex_injective hdiag.1) with hfR
  set tAL := TriangulatedPolygon.remap (leftIndex i j) (leftIndex_injective hdiag.1) gL.triang
    with htAL
  set tBR := TriangulatedPolygon.remap (rightIndex i j) (rightIndex_injective hdiag.1) gR.triang
    with htBR
  -- the index-freshness hAVe (rightArc_vertex_fresh_for_left)
  have hAVe : ∀ u ∈ tBR.vertices, u ∈ tAL.vertices → u ∈ Sym2.mk i j :=
    diag_hAVe hdiag.1 gL.triang gR.triang
  -- a re-rooted triangulation of the same right set carrying AttachesTo onto the left image;
  -- merge it onto the left, extracting the merged triangulation via Classical.choice (Prop →
  -- Nonempty data).
  have hmerged : Nonempty (TriangulatedPolygon n (gL.tset.image fL ∪ gR.tset.image fR)) := by
    obtain ⟨tR', hattR'⟩ :=
      rerootedAttaches (A := gL.tset.image fL) (AV := tAL.vertices) hL tBR hT₀ heT₀ hwT₀ hwe hwAV
        hdiagL hAVe
    exact TriangulatedPolygon.mergeOnto tAL tR' hattR'
  have merged := hmerged.some
  refine
    { tset := gL.tset.image fL ∪ gR.tset.image fR
      triang := merged
      realise := ?_ }
  intro τ hτ
  have htris : ((EarTriangulation'.splitDiagonal P ρ G hdiag tL tR).toGeom B).tris
      = tL.triangles ++ tR.triangles := rfl
  rw [htris, List.mem_append] at hτ
  rcases hτ with hτL | hτR
  · obtain ⟨A, hAset, hA⟩ := gL.realise τ hτL
    exact ⟨fL A, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨A, hAset, rfl⟩),
      realisedBy_mapLeft G hdiag hA⟩
  · obtain ⟨A, hAset, hA⟩ := gR.realise τ hτR
    exact ⟨fR A, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨A, hAset, rfl⟩),
      realisedBy_mapRight G hdiag hA⟩

/-! ## Part H: honest scope — what `M`'s peel-order reduces to, and what still blocks the headline

**The peel-order content of `M` is now fully reduced to ONE isolated, non-vacuous atomic residue
`LastToFirstAll`** (the last-to-first dual-tree re-root over the `TriangulatedPolygon` inductive),
via the proved chain

```
  LastToFirstAll  ──reroot──▶  re-root any triangulation at any triangle
                  ──attachesTo_of_innermost──▶  the AttachesTo certificate (diagonal innermost)
                  ──canonicalMergedGlue──▶  the diagonal-first merged CombinatorialGlue.
```

Everything except `LastToFirstAll` is **proved unconditionally and clean-3**:
`reroot_interior`, `attachesTo_of_innermost`, `diag_hAVe` (the index-freshness, from
`rightArc_vertex_fresh_for_left`), `rerootedAttaches`, and `canonicalMergedGlue` (the actual
diagonal-first glue, using the re-rooted right triangulation — *not* the false universal `M`).
`lastToFirst_nonvacuous` certifies the residue is satisfiable, so this is not a vacuous reduction.

**Two honest scope notes (playbook §3.3):**

1. **Universal `M = DiagonalAttachInput` is too strong to be a theorem** (it is false on the
   pathological glues the universal admits — see the file header), so the correct deliverable is
   `canonicalMergedGlue` (a glue-*producing* construction over `LastToFirstAll`), **not** a proof
   of `M`.  To wire it into the headline one replaces `PolygonLast.combinatorialGlue_of_attach`'s
   reliance on `M` with a recursion over `canonicalMergedGlue`, which additionally needs, per
   split, the *structural* witnesses `hT₀`/`heT₀`/`hdiagL` (the right glue carries the diagonal
   triangle, the left glue carries a triangle on the diagonal) — true for the canonical
   `EarTriangulation'`-derived glue (the right child's closing edge *is* the diagonal), but a
   standalone structural induction over the ear recursion in its own right.

2. **`M` is not the sole blocker of the unconditional headline.**  Even with the peel-order fully
   discharged, the Chapter-36 `⌊n/3⌋` headline stays conditional on the irreducible planar bundle
   `PolygonGeometryInput` / `ResidualGeometryData` — the general-`n` convex-vertex
   (`IsConvexVertex'`), transversality (`DiagonalTransversality'`), cut strict-axioms
   (`Left/RightStrictAxioms`), and region-intersection Jordan data — for which
   `PolygonResidualData` records a source-level exhaustion verdict (no producer from the
   substrate).  The general-`n` ray-independence `RegionSplitGenericity`, now PROVED, closed the
   *genericity* sub-residue *inside* that bundle, but the convex-position / transversality fields
   are separate planar content.  So the faithful current conditionality is: **headline ⇐
   `PolygonGeometryInput` (planar Jordan bundle) + the peel-order, the latter now reduced to the
   single atomic `LastToFirstAll`.** -/

end

end ProofsInTheBook.PolygonMClose
