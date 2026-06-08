/-
# Chapter 36 — discharging `LastToFirstAll` by unconditional dual-tree re-rooting

This file closes the last combinatorial residue of the Chapter-36 art-gallery oracle `M`:
the peel-order last-to-first re-rooting `LastToFirstAll n`, isolated upstream in
`PolygonMClose` / `PolygonEarDeletionInduction`.

## The verdict on the substrate (correcting the prior "design-block" diagnosis)

The prior round (`PolygonEarDeletionInduction`) concluded `LastToFirstAll` was
**design-blocked at the substrate**, on the premise that the bare `TriangulatedPolygon`
inductive "has FORGOTTEN the dual-tree adjacency" and therefore cannot be re-peeled from a
chosen root.  **That premise is false.**  The `.glue` constructor carries the field

```
hShared : ∃ T' ∈ S, ∃ e ∈ T.edges, e ∈ T'.edges ∧ newVertex ∉ e
```

which records *exactly* the dual-tree edge from the newly-glued ear `T` to its neighbour
`T' ∈ S`.  The dual adjacency is therefore present at every layer, and the dual tree is
recoverable.  The re-rooting is genuine combinatorial tree surgery and goes through
**unconditionally** — no new substrate, no upstream refactor, no extra hypothesis.

## The proof structure

The prior reduction `lastToFirstAll_of_innerAttach` required `InnerAttachCert h T`, i.e.
`AttachesTo {T} (triVerts T) h` for the inner block `h` *in its native peel order*.  That
native order need not place `T`'s dual neighbour innermost, which is the (real) obstruction
the prior round hit.  The fix is to **not** use `h`'s native order: re-root `h` first so
that `T`'s neighbour `T'` becomes the innermost `.single`, then read off the certificate.

We prove the unconditional re-root principle `rerootAll` directly by structural induction on
the triangulation:

* `.single` — reflexive.
* `.glue h T v …`, target an interior triangle `T₀ ∈ S'` — `PolygonMClose.reroot_interior`
  (already unconditional) + the induction hypothesis on `h`.
* `.glue h T v …`, target the **outermost ear** `T` itself (the genuine last-to-first move)
  — the induction hypothesis re-roots `h` at `T`'s dual neighbour `T'` (from `hShared`),
  producing `h*` whose innermost is `T'`; then `PolygonMClose.attachesTo_of_innermost`
  yields `AttachesTo {T} (triVerts T) h*`; then
  `PolygonEarDeletionInduction.lastToFirst_of_attachesInner` re-glues `T` as the innermost.

The two freshness obligations of `attachesTo_of_innermost` are supplied *without* any new
fact: every glued apex `w` of `h*` is fresh against the inner block (so `w ∉ e`, `e` =
the shared edge), and the **outer** glue freshness `hFresh` (`v` avoids every corner of
every triangle of `S'`) forces `w ≠ v`; hence the only vertices of `h*` lying in
`triVerts T = {e-endpoints, v}` are the endpoints of `e`.  This is the `hAVe` input.

The induction hypothesis supplies the inner re-root, so there is **no circular dependency**
on `LastToFirstAll`/`reroot` (those are conditional; `rerootAll` here is not).

## Deliverable

`lastToFirstAll_holds : LastToFirstAll n` — unconditional, clean-3.  This discharges the
peel-order content of `M` (`PolygonMClose.canonicalMergedGlue` is now unconditionally
inhabited), leaving the Chapter-36 `⌊n/3⌋` headline conditional only on the planar Jordan
bundle `PolygonGeometryInput`.

No `sorry` / `axiom` / `admit` / `native_decide`.

Build dependency: `ProofsInTheBook.PolygonEarDeletionInduction`.
-/
import ProofsInTheBook.PolygonEarDeletionInduction

namespace ProofsInTheBook.PolygonReroot

open ProofsInTheBook
open ProofsInTheBook.Chapter36
open ProofsInTheBook.PolygonLast (triVerts mem_triVerts_of_mem_edge triVerts_subset_vertices
  vertices_subset_triVerts AttachesTo)
open ProofsInTheBook.PolygonMClose (InnermostIs Rerootable LastToFirst LastToFirstAll
  reroot_interior attachesTo_of_innermost)
open ProofsInTheBook.PolygonEarDeletionInduction (lastToFirst_of_attachesInner)

noncomputable section

variable {n : ℕ}

/-! ## A small triangle fact: a corner off a given edge -/

/-- A triangle has a corner not lying on any one of its edges (the apex opposite that
edge).  Concretely, the third corner of `T` relative to `e ∈ T.edges`. -/
lemma exists_corner_off_edge (T : AbsTriangle n) {e : Sym2 (Fin n)} (he : e ∈ T.edges) :
    ∃ w ∈ triVerts T, w ∉ e := by
  have hab := T.hab; have hbc := T.hbc; have hac := T.hac
  simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · -- e = {a, b}; apex c
    refine ⟨T.c, by simp only [triVerts, Finset.mem_insert, Finset.mem_singleton]; tauto, ?_⟩
    rw [Sym2.mem_iff]; push_neg; exact ⟨hac.symm, hbc.symm⟩
  · -- e = {b, c}; apex a
    refine ⟨T.a, by simp only [triVerts, Finset.mem_insert, Finset.mem_singleton]; tauto, ?_⟩
    rw [Sym2.mem_iff]; push_neg; exact ⟨hab, hac⟩
  · -- e = {a, c}; apex b
    refine ⟨T.b, by simp only [triVerts, Finset.mem_insert, Finset.mem_singleton]; tauto, ?_⟩
    rw [Sym2.mem_iff]; push_neg; exact ⟨hab.symm, hbc⟩

/-! ## The unconditional re-root principle

`rerootAll` re-roots any triangulation at any of its triangles, *unconditionally*.  The
outermost-ear case is the genuine last-to-first move, discharged by re-rooting the inner
block at the ear's dual neighbour (induction hypothesis) and grafting the ear back as the
new innermost via the proved `attachesTo_of_innermost` + `lastToFirst_of_attachesInner`
chain. -/

theorem rerootAll {S : Finset (AbsTriangle n)} (t : TriangulatedPolygon n S) :
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
      · -- Target is the outermost ear `T`: the last-to-first move.
        rw [heq]
        -- `T`'s dual neighbour `T'` (the shared-edge partner in `S'`), and the shared edge `e`.
        obtain ⟨T', hT'S', e, heT, heT', hve⟩ := id hShared
        -- Re-root the inner block `h` at `T'` (induction hypothesis), innermost = `T'`.
        obtain ⟨hStar, hStarInner⟩ := ih T' hT'S'
        -- A corner `w` of `T'` off the shared edge `e`.
        obtain ⟨w, hwT', hwe⟩ := exists_corner_off_edge T' heT'
        -- `w ∉ triVerts T`: `triVerts T = {e-endpoints, v}`; `w ∉ e`, and `w ≠ v` since `w` is a
        -- corner of `T' ∈ S'` while `v` avoids every `S'`-corner (`hFresh`).
        have hwv : w ≠ v := by
          intro hwv
          subst hwv
          exact hFresh T' hT'S' (by simpa only [triVerts] using hwT')
        have hwT : w ∉ triVerts T := by
          intro hwTmem
          -- `triVerts T ⊆ insert v e` since `T`'s corners are `e`'s two endpoints plus the apex `v`.
          -- Concretely: any corner of `T` is `v` or an endpoint of `e`.
          have : w ∈ e := by
            have hvT : v ∈ triVerts T := by simpa only [triVerts] using hT_new
            -- `w` is a corner of `T`, `w ≠ v` (the apex), and `e ∈ T.edges` with `v ∉ e`;
            -- hence `w` is an endpoint of `e`.
            exact PolygonLast.corner_mem_edge_of_ne_apex heT hvT hve hwTmem hwv
          exact hwe this
        -- `hAVe`: every vertex of `hStar` lying in `triVerts T` is an endpoint of `e`.
        have hAVe : ∀ u ∈ hStar.vertices, u ∈ triVerts T → u ∈ e := by
          intro u huV huT
          -- `u` is a corner of some `S'`-triangle.
          obtain ⟨U, hUS', huU⟩ := vertices_subset_triVerts hStar u huV
          -- `triVerts T = {e-endpoints, v}`; rule out `u = v` via `hFresh`.
          by_cases huv : u = v
          · subst huv
            exact absurd (by simpa only [triVerts] using huU) (hFresh U hUS')
          · have hvT : v ∈ triVerts T := by simpa only [triVerts] using hT_new
            exact PolygonLast.corner_mem_edge_of_ne_apex heT hvT hve huT huv
        -- `AttachesTo {T} (triVerts T) hStar` from the diagonal-rooted certificate.
        have hatt : AttachesTo ({T} : Finset (AbsTriangle n)) (triVerts T) hStar :=
          attachesTo_of_innermost (A := ({T} : Finset (AbsTriangle n))) (AV := triVerts T)
            hStar (T₀ := T') hStarInner (e := e) heT' (w := w) hwT' hwe hwT
            ⟨T, Finset.mem_singleton_self _, heT⟩ hAVe
        -- Re-glue `T` as the new innermost via the proved reduction.  `LastToFirst hStar …` and
        -- `LastToFirst h …` are the same `Prop` (`Rerootable` depends only on the set
        -- `insert T S'`, common to `glue hStar …` and `glue h …`).
        have hLTF : LastToFirst hStar T v hT_new hShared hFresh :=
          lastToFirst_of_attachesInner hStar T v hT_new hShared hFresh hatt
        -- `LastToFirst hStar … = Rerootable (glue hStar T v …) T`
        --                       = ∃ t', InnermostIs t' T  (set `insert T S'`)
        --                       = Rerootable (glue h T v …) T.
        exact hLTF
      · -- Target is interior to the inner block: recurse + re-glue the ear (unconditional).
        exact reroot_interior h T v hT_new hShared hFresh hT₀S' (ih T₀ hT₀S')

/-! ## `LastToFirstAll` discharged unconditionally -/

/-- **The Chapter-36 peel-order residue, closed.**  `LastToFirstAll n` holds
unconditionally: for every glue layer `glue h T v …`, the outermost ear `T` re-roots to the
innermost `.single` of a triangulation of the same set.  This is the `T₀ = T` case of
`rerootAll`. -/
theorem lastToFirstAll_holds : LastToFirstAll n := by
  intro S' h T v hT_new hShared hFresh
  -- `LastToFirst h T v … = Rerootable (glue h T v …) T`; the ear `T` is in the set.
  exact rerootAll (TriangulatedPolygon.glue h T v hT_new hShared hFresh) T
    (Finset.mem_insert_self _ _)

end

end ProofsInTheBook.PolygonReroot

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonReroot.rerootAll
#print axioms ProofsInTheBook.PolygonReroot.lastToFirstAll_holds
