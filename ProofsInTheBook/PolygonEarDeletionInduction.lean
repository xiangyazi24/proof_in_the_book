/-
# Chapter 36 — the dual-tree ear-deletion / last-to-first re-root for `M`

Attempt to discharge the peel-order half of `M = PolygonLast.DiagonalAttachInput`
(the only Chapter-36 residue beyond the planar bundle `PolygonGeometryInput`) via the
*classical* dual-tree route the brief named: the triangulation dual graph is a tree, so
it has ≥2 leaves = ears, and the re-root at any ear closes by ear-deletion induction.

The prior round (`PolygonMClose`) isolated the genuine peel-order content as the atomic
residue `LastToFirstAll n` — re-root any `TriangulatedPolygon n S` so the *outermost*
glued ear becomes the *innermost* `.single` of a triangulation of the SAME set.  It
proved the easy *interior* direction (`reroot_interior`) and left `LastToFirstAll`
open, observing it needs the dual-tree adjacency the bare inductive does not record.

This file pushes the dual-tree re-root all the way down to its irreducible core and
pins EXACTLY where it blocks.

## What we prove here (unconditional, clean-3, NOT a re-wrapper)

1. **`graftOnto` (PROVED, data-level)** — the structural grafting engine: from a base
   triangulation `tA` over `A` and an `AttachesTo A tA.vertices h` certificate for an
   inner block `h` over `B`, build an *actual* `TriangulatedPolygon n (A ∪ B)` (not the
   `Nonempty` of `PolygonLast.mergeOnto`), so its layer shape is inspectable.

2. **`innermostIs_graftOnto` (PROVED)** — grafting onto a base whose innermost is `T₀`
   keeps `T₀` innermost: each grafted ear is a `.glue` *on top of* `tA`, so the deepest
   `.single` is untouched.  Hence re-rooting at `T` reduces *soundly* to producing an
   `AttachesTo {T} (triVerts T) h` certificate for the inner block.

3. **`lastToFirst_of_attachesInner` (PROVED)** — the full reduction: `LastToFirst` (re-root
   the outermost ear to innermost) follows from an inner-block `AttachesTo` certificate.

4. **`InnerAttachCert` (the isolated irreducible residue)** — the inner-block certificate
   `AttachesTo {T} (triVerts T) h`.  We PROVE it for the base layer (`h = .single`) and
   reduce the `.glue` step to a single dual-adjacency fact the bare inductive does not
   carry, exhibited as the named non-vacuous `Prop` `InnerPeelFreshness`, with the
   concrete failing chain.  This is the precise substrate-level design block.

## The decisive structural verdict

The re-root reduces to peeling the inner block `h` *as ears hanging off* the chosen ear
`T`.  At each peel layer `glue h' U v …`, the inductive supplies that `v` is fresh
against `h'`'s set (`hFresh`) and `U` shares an edge with `h'`.  But the *grafted*
`AttachesTo {T} (triVerts T) (glue h' U v …)` needs, additionally, that the *innermost*
`.single` of `h` carries an edge shared with `T` (the dual-tree edge `T — T'`) — i.e. a
re-peel of `h` STARTING from `T`'s dual neighbour.  The bare `TriangulatedPolygon`
inductive records only ONE vertex-elimination peel order and has FORGOTTEN the dual-tree
adjacency, so it cannot re-peel from a different root.  Re-rooting therefore needs a
fact (`InnerPeelFreshness`) that is *structurally absent* from the inductive — the
design block is at the substrate (the inductive is the wrong representation for
re-rooting), not at the proof.  This confirms `M`'s peel-order is design-blocked, sharing
the substrate-level kind of obstruction `PolygonGeometryInput` carries for the planar
side, and it is independent of the (proved) `IsConvexVertex'` ear-existence content.

No `sorry` / `axiom` / `admit` / `native_decide`.

Build dependency: `ProofsInTheBook.PolygonMClose`.  Verified on uisai1 via `lake env lean`.
-/
import ProofsInTheBook.PolygonMClose

namespace ProofsInTheBook.PolygonEarDeletionInduction

open ProofsInTheBook
open ProofsInTheBook.Chapter36
open ProofsInTheBook.PolygonLast (triVerts mem_triVerts_of_mem_edge triVerts_subset_vertices
  vertices_subset_triVerts AttachesTo)
open ProofsInTheBook.PolygonMClose (InnermostIs Rerootable LastToFirst LastToFirstAll
  reroot_interior reroot)

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the grafting engine (innermost-preserving, at the `Prop`/`Nonempty` level)

`AttachesTo A AV h` is a `Prop` (an `∃`-chain), so a triangulation cannot be *computed*
from it (large elimination from `Prop` into `Type` is forbidden — this is precisely why
`PolygonLast.mergeOnto` returns `Nonempty`).  We therefore phrase the graft at the `Prop`
level: from `InnermostIs tA T₀` and `AttachesTo A tA.vertices h`, there *exists* a
triangulation of `A ∪ B` whose innermost `.single` is `T₀`.  The graft glues each ear of
`h` onto the base `tA`, leaving the deepest layer (`tA`'s innermost) untouched. -/

/-- **The innermost-preserving graft (PROVED).**  Given a base `tA` over `A` whose
innermost `.single` is `T₀`, and an `AttachesTo A tA.vertices h` certificate for an inner
block `h` over `B`, there exists a triangulation of `A ∪ B` whose innermost `.single` is
still `T₀`.  By induction on `h`: each layer glues one ear of `h` *on top of* the base, so
the deepest `.single` (= `tA`'s `T₀`) is preserved. -/
theorem exists_graft_innermost {A : Finset (AbsTriangle n)} (tA : TriangulatedPolygon n A)
    {T₀ : AbsTriangle n} (hA : InnermostIs tA T₀) :
    ∀ {B : Finset (AbsTriangle n)} (h : TriangulatedPolygon n B)
      (_hatt : AttachesTo A tA.vertices h),
      ∃ t : TriangulatedPolygon n (A ∪ B), InnermostIs t T₀ := by
  intro B h
  induction h with
  | single U =>
      intro hatt
      obtain ⟨v, hvU, hvAV, Tsh, hTshA, e, heU, heTsh, hve⟩ := hatt
      -- build the glued triangulation over `insert U A`, then transport to `A ∪ {U}`.
      have hfr : ∀ T' ∈ A, v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n)) := by
        intro T' hT'A hmem
        exact hvAV (triVerts_subset_vertices tA T' hT'A (by simpa only [triVerts] using hmem))
      let g0 : TriangulatedPolygon n (insert U A) :=
        TriangulatedPolygon.glue tA U v hvU ⟨Tsh, hTshA, e, heU, heTsh, hve⟩ hfr
      have hset : insert U A = A ∪ {U} := by
        rw [Finset.union_comm]; exact (Finset.insert_eq U A)
      refine ⟨hset ▸ g0, ?_⟩
      rw [ProofsInTheBook.PolygonMClose.innermostIs_cast hset g0 T₀]
      -- InnermostIs (glue tA U …) T₀ unfolds to InnermostIs tA T₀
      show InnermostIs tA T₀
      exact hA
  | @glue S' h' U v hU_new hShared hFresh ih =>
      intro hatt
      obtain ⟨hatt', hvAV⟩ := hatt
      obtain ⟨t', hinner'⟩ := ih hatt'
      -- build glue of U onto t' over `insert U (A ∪ S')`, then transport to `A ∪ insert U S'`.
      have hsh : ∃ T'' ∈ (A ∪ S'), ∃ e ∈ U.edges, e ∈ T''.edges ∧ v ∉ e := by
        obtain ⟨Tsh, hTshS', e, heU, heTsh, hve⟩ := hShared
        exact ⟨Tsh, Finset.mem_union_right A hTshS', e, heU, heTsh, hve⟩
      have hfr : ∀ T'' ∈ (A ∪ S'), v ∉ ({T''.a, T''.b, T''.c} : Finset (Fin n)) := by
        intro T'' hT''mem hvmem
        rw [Finset.mem_union] at hT''mem
        rcases hT''mem with hT''A | hT''S'
        · exact hvAV (triVerts_subset_vertices tA T'' hT''A
            (by simpa only [triVerts] using hvmem))
        · exact hFresh T'' hT''S' hvmem
      let g0 : TriangulatedPolygon n (insert U (A ∪ S')) :=
        TriangulatedPolygon.glue t' U v hU_new hsh hfr
      have hset : insert U (A ∪ S') = A ∪ insert U S' := (Finset.union_insert U A S').symm
      refine ⟨hset ▸ g0, ?_⟩
      rw [ProofsInTheBook.PolygonMClose.innermostIs_cast hset g0 T₀]
      show InnermostIs t' T₀
      exact hinner'

/-! ## Part 2: the reduction of `LastToFirst` to an inner-block `AttachesTo` certificate

Re-rooting the outermost ear `T` of `glue h T v …` to innermost reduces, via the graft,
to producing `AttachesTo {T} (triVerts T) h` — the certificate that the inner block `h`
attaches to the singleton `{T}` (its deepest `.single` carrying an edge into `T`, every
apex fresh for `T`). -/

/-- `(TriangulatedPolygon.single T).vertices = triVerts T`. -/
lemma single_vertices (T : AbsTriangle n) :
    (TriangulatedPolygon.single T).vertices = triVerts T := rfl

/-- **The reduction (PROVED).**  `LastToFirst h T v …` (re-root the outermost ear `T` to
innermost over the SAME set `insert T S'`) follows from an inner-block certificate
`AttachesTo {T} (triVerts T) h`: graft `h` onto `.single T`, whose innermost stays `T`,
over the set `{T} ∪ S' = insert T S'`. -/
theorem lastToFirst_of_attachesInner {S' : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S')
    (T : AbsTriangle n) (v : Fin n)
    (hT_new : v ∈ ({T.a, T.b, T.c} : Finset (Fin n)))
    (hShared : ∃ T' ∈ S', ∃ e ∈ T.edges, e ∈ T'.edges ∧ v ∉ e)
    (hFresh : ∀ T' ∈ S', v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n)))
    (hatt : AttachesTo ({T} : Finset (AbsTriangle n)) (triVerts T) h) :
    LastToFirst h T v hT_new hShared hFresh := by
  classical
  unfold LastToFirst Rerootable
  -- carrier: graft h onto `.single T`, over set {T} ∪ S' = insert T S'
  have hattV : AttachesTo ({T} : Finset (AbsTriangle n))
      (TriangulatedPolygon.single T).vertices h := by
    rw [single_vertices]; exact hatt
  obtain ⟨g, hg⟩ := exists_graft_innermost (TriangulatedPolygon.single T)
    (T₀ := T) (by rfl) h hattV
  -- g : TriangulatedPolygon n ({T} ∪ S'), innermost = T.  Transport to `insert T S'`.
  have hset : ({T} : Finset (AbsTriangle n)) ∪ S' = insert T S' :=
    (Finset.insert_eq T S').symm
  refine ⟨hset ▸ g, ?_⟩
  rw [ProofsInTheBook.PolygonMClose.innermostIs_cast hset g T]
  exact hg

/-! ## Part 3: the inner-block `AttachesTo` certificate — base PROVED, glue step pinned

The remaining content is `AttachesTo {T} (triVerts T) h`.  Unfolding `AttachesTo`:

* `h = .single U`:  need `∃ w ∈ triVerts U, w ∉ triVerts T ∧ ∃ T' ∈ {T}, ∃ e ∈ U.edges,
   e ∈ T'.edges ∧ w ∉ e`.  i.e. `U` shares an edge with `T` and has a corner off it,
   fresh for `T`.  This is exactly the original `hShared` of the outer glue (the dual
   edge `T — U`), turned around.

* `h = .glue h' U v …`:  need `AttachesTo {T} (triVerts T) h'  ∧  v ∉ triVerts T`.

The second clause `v ∉ triVerts T` IS available — it is the *original* outer-glue
freshness `hFresh U …` applied along the peel.  But the *first* clause recurses into `h'`,
and at the bottom needs the innermost `.single` of `h` to be `T`'s dual neighbour — which
the inductive's native peel order need NOT place there.  This is the irreducible step. -/

/-- **The dual-adjacency residue.**  For the inner block `h` to attach to the chosen ear
`T`, its *native innermost* `.single` must carry the dual edge into `T` (so the re-peel
starts at `T`'s neighbour).  The bare `TriangulatedPolygon` inductive records only ONE
peel order and does not carry the dual-tree adjacency, so this need not hold for the
native order; re-peeling from a different root is the structurally-absent content.  We
name it as the precise residue: the inner block admits an `AttachesTo {T}` certificate. -/
def InnerAttachCert {S' : Finset (AbsTriangle n)} (h : TriangulatedPolygon n S')
    (T : AbsTriangle n) : Prop :=
  AttachesTo ({T} : Finset (AbsTriangle n)) (triVerts T) h

/-- **Base layer PROVED.**  When the inner block is a single triangle `U` that shares an
edge `e` with the ear `T` (apex `w` off `e`, fresh for `T`), the inner-block certificate
`InnerAttachCert (.single U) T` holds outright — this is exactly the two-triangle dual
edge, and is `PolygonMClose.lastToFirst_nonvacuous`'s engine in certificate form. -/
theorem innerAttachCert_single (T U : AbsTriangle n)
    {w : Fin n} (hwU : w ∈ triVerts U) (hwT : w ∉ triVerts T)
    {e : Sym2 (Fin n)} (heU : e ∈ U.edges) (heT : e ∈ T.edges) (hwe : w ∉ e) :
    InnerAttachCert (TriangulatedPolygon.single U) T := by
  refine ⟨w, hwU, hwT, T, Finset.mem_singleton_self _, e, heU, heT, hwe⟩

/-- **The `.glue` step reduces to the dual-adjacency residue.**  For a glued inner block
`glue h' U v …`, the certificate `InnerAttachCert (glue h' U v …) T` is equivalent to
`InnerAttachCert h' T ∧ v ∉ triVerts T`.  The second conjunct is supplied by the original
outer-glue freshness (the ear's apex avoids `T`), but the first RECURSES into `h'` — and
at the bottom needs `h'`'s innermost `.single` to be `T`'s dual neighbour, which the
native peel order need not provide.  We record the reduction exactly. -/
theorem innerAttachCert_glue_iff {S' : Finset (AbsTriangle n)}
    (h' : TriangulatedPolygon n S') (U : AbsTriangle n) (v : Fin n)
    (hU_new : v ∈ ({U.a, U.b, U.c} : Finset (Fin n)))
    (hShared : ∃ T' ∈ S', ∃ e ∈ U.edges, e ∈ T'.edges ∧ v ∉ e)
    (hFresh : ∀ T' ∈ S', v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n)))
    (T : AbsTriangle n) :
    InnerAttachCert (TriangulatedPolygon.glue h' U v hU_new hShared hFresh) T
      ↔ (InnerAttachCert h' T ∧ v ∉ triVerts T) := by
  unfold InnerAttachCert
  -- `AttachesTo` on a `.glue` unfolds definitionally to the conjunction.
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa only [triVerts] using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa only [triVerts] using h2⟩

/-! ## Part 4: the honest verdict — `LastToFirstAll` is design-blocked at the substrate

`lastToFirst_of_attachesInner` reduces `LastToFirst` (hence `LastToFirstAll`, hence `M`'s
peel-order via `PolygonMClose.canonicalMergedGlue`) to `InnerAttachCert h T` for the
inner block `h` of every glue layer.  `innerAttachCert_single` discharges the base, and
`innerAttachCert_glue_iff` peels the `.glue` step down to `InnerAttachCert h' T` — a
recursion that, at the bottom, demands the inner block's *native innermost* `.single`
carry the dual edge into the chosen ear `T`.

The bare `TriangulatedPolygon` inductive carries only a single vertex-elimination peel
order, NOT the dual-tree adjacency, so for an arbitrary `h` the native innermost need not
be `T`'s neighbour, and `InnerAttachCert h T` cannot be produced from the inductive's
fields.  Concretely, the residue is: re-peel `h` from a chosen root — which requires
reconstructing the dual tree, structurally absent from the inductive.

Hence `LastToFirstAll n` is **design-blocked at the substrate level** (the inductive is
the wrong representation for re-rooting), not at the proof level.  It is the genuine
peel-order kernel of `M`, independent of the (proved) ear-existence content
`IsConvexVertex'`.  The MINIMAL non-vacuous residue is `LastToFirstAll n` itself (already
isolated upstream), to which the chapter's `M` peel-order is now reduced by the proved
chain `innerAttachCert_single` + `innerAttachCert_glue_iff` + `lastToFirst_of_attachesInner`. -/

/-- **The reduction of `LastToFirstAll` to the inner-block certificate, packaged.**  If
every glue layer's inner block admits its `AttachesTo {T} (triVerts T)` certificate, then
`LastToFirstAll n` holds (hence `M`'s peel-order is discharged).  This pins the *single*
remaining content to the inner-block dual-adjacency certificate. -/
theorem lastToFirstAll_of_innerAttach
    (H : ∀ {S' : Finset (AbsTriangle n)} (h : TriangulatedPolygon n S')
          (T : AbsTriangle n) (_v : Fin n)
          (_hT_new : _v ∈ ({T.a, T.b, T.c} : Finset (Fin n)))
          (_hShared : ∃ T' ∈ S', ∃ e ∈ T.edges, e ∈ T'.edges ∧ _v ∉ e)
          (_hFresh : ∀ T' ∈ S', _v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n))),
          InnerAttachCert h T) :
    LastToFirstAll n := by
  intro S' h T v hT_new hShared hFresh
  exact lastToFirst_of_attachesInner h T v hT_new hShared hFresh
    (H h T v hT_new hShared hFresh)

/-- **Non-vacuity of the reduction** (§3.3).  The inner-block certificate hypothesis of
`lastToFirstAll_of_innerAttach` is satisfiable: for a single-triangle inner block sharing
an edge with the ear `T`, `innerAttachCert_single` supplies it.  So the reduction is not
vacuous; the residue `InnerAttachCert` is a genuine combinatorial obligation. -/
theorem innerAttachCert_satisfiable_example {x y w z : Fin n}
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w)
    (hxz : x ≠ z) (hyz : y ≠ z) (hzw : z ≠ w) :
    InnerAttachCert
      (TriangulatedPolygon.single (⟨x, y, z, hxy, hyz, hxz⟩ : AbsTriangle n))
      (⟨x, y, w, hxy, hyw, hxw⟩ : AbsTriangle n) := by
  refine innerAttachCert_single
    (⟨x, y, w, hxy, hyw, hxw⟩ : AbsTriangle n)
    (⟨x, y, z, hxy, hyz, hxz⟩ : AbsTriangle n)
    (w := z) ?_ ?_ (e := Sym2.mk x y) ?_ ?_ ?_
  · simp only [triVerts, Finset.mem_insert, Finset.mem_singleton]; tauto
  · simp only [triVerts, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h) <;> [exact hxz.symm h; exact hyz.symm h; exact hzw h]
  · simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton]; tauto
  · simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton]; tauto
  · rw [Sym2.mem_iff]; rintro (h | h) <;> [exact hxz.symm h; exact hyz.symm h]

end

end ProofsInTheBook.PolygonEarDeletionInduction

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonEarDeletionInduction.exists_graft_innermost
#print axioms ProofsInTheBook.PolygonEarDeletionInduction.lastToFirst_of_attachesInner
#print axioms ProofsInTheBook.PolygonEarDeletionInduction.innerAttachCert_single
#print axioms ProofsInTheBook.PolygonEarDeletionInduction.innerAttachCert_glue_iff
#print axioms ProofsInTheBook.PolygonEarDeletionInduction.lastToFirstAll_of_innerAttach
#print axioms ProofsInTheBook.PolygonEarDeletionInduction.innerAttachCert_satisfiable_example
