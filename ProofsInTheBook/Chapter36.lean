import Mathlib

/-!
# Chapter 36: Art galleries

This file proves the combinatorial core of the art gallery theorem: any
abstract polygon triangulation has a 3-coloring, and the smallest color
class gives at most `⌊n / 3⌋` guards meeting every triangle.

It also introduces a certified ear-clipping interface for planar polygons.
Mathlib's current polygon API gives vertex-indexed `Polygon`s and boundary
sets, but not a Jordan-curve interior or a theorem that raw simple planar
polygons have ears.  The `SimplePolygon` structure below therefore keeps the
actual cyclic sequence of vertices in `ℝ × ℝ` together with a checkable
triangulation certificate.  Ear existence and triangulation extraction are
then proved from the inductive `TriangulatedPolygon` certificate, without any
unstated geometric premise.
-/

namespace ProofsInTheBook.Chapter36

open Set

inductive GuardColor where
  | red | green | blue
  deriving DecidableEq, Repr, Fintype

open GuardColor

def other_color : GuardColor → GuardColor → GuardColor
  | red, green => blue
  | green, red => blue
  | red, blue => green
  | blue, red => green
  | green, blue => red
  | blue, green => red
  | red, red => green
  | green, green => red
  | blue, blue => red

theorem other_color_neq_left (c1 c2 : GuardColor) : other_color c1 c2 ≠ c1 := by
  cases c1 <;> cases c2 <;> decide

theorem other_color_neq_right (c1 c2 : GuardColor) : other_color c1 c2 ≠ c2 := by
  cases c1 <;> cases c2 <;> decide

/-- When `c1 ≠ c2`, `other_color c1 c2` is the unique third color: it differs
from both. -/
theorem other_color_third {c1 c2 : GuardColor} (_h : c1 ≠ c2) :
    other_color c1 c2 ≠ c1 ∧ other_color c1 c2 ≠ c2 :=
  ⟨other_color_neq_left c1 c2, other_color_neq_right c1 c2⟩

/-- `other_color` is symmetric in the two distinct-color case (commutativity
on off-diagonal inputs).  -/
theorem other_color_comm_of_ne {c1 c2 : GuardColor} (h : c1 ≠ c2) :
    other_color c1 c2 = other_color c2 c1 := by
  cases c1 <;> cases c2 <;> simp [other_color] at h ⊢

/-- The `GuardColor` Fintype has exactly three elements. -/
@[simp]
theorem GuardColor.card : Fintype.card GuardColor = 3 := rfl

/-- A triangle on three distinct vertices of `Fin n`. -/
structure AbsTriangle (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  hab : a ≠ b
  hbc : b ≠ c
  hac : a ≠ c

instance {n : ℕ} : DecidableEq (AbsTriangle n) := by
  intro t1 t2
  obtain ⟨a1, b1, c1, _, _, _⟩ := t1
  obtain ⟨a2, b2, c2, _, _, _⟩ := t2
  if h : a1 = a2 ∧ b1 = b2 ∧ c1 = c2 then
    apply isTrue
    rcases h with ⟨rfl, rfl, rfl⟩
    congr
  else
    apply isFalse
    intro h_eq
    apply h
    injection h_eq with h_a h_b h_c
    exact ⟨h_a, h_b, h_c⟩

/-- The (undirected) edges of an abstract triangle, as a finset of unordered pairs. -/
def AbsTriangle.edges {n : ℕ} (T : AbsTriangle n) : Finset (Sym2 (Fin n)) :=
  {Sym2.mk T.a T.b, Sym2.mk T.b T.c, Sym2.mk T.a T.c}

/-- The three vertices of an abstract triangle. -/
def AbsTriangle.vertices {n : ℕ} (T : AbsTriangle n) : Finset (Fin n) :=
  {T.a, T.b, T.c}

/-- The inverse index to `v.succAbove`, defined for vertices different from
the deleted vertex. -/
noncomputable def deleteVertexIndex {n : ℕ} (v : Fin (n + 1)) (i : Fin (n + 1))
    (hi : i ≠ v) : Fin n :=
  Classical.choose (Fin.exists_succAbove_eq hi)

@[simp]
lemma succAbove_deleteVertexIndex_of_ne {n : ℕ} (v : Fin (n + 1)) (i : Fin (n + 1))
    (hi : i ≠ v) : v.succAbove (deleteVertexIndex v i hi) = i := by
  exact Classical.choose_spec (Fin.exists_succAbove_eq hi)

lemma deleteVertexIndex_injective_on_compl {n : ℕ} {v : Fin (n + 1)}
    {i j : Fin (n + 1)} {hi : i ≠ v} {hj : j ≠ v}
    (h : deleteVertexIndex v i hi = deleteVertexIndex v j hj) : i = j := by
  have hs := congrArg v.succAbove h
  simpa [succAbove_deleteVertexIndex_of_ne v i hi,
    succAbove_deleteVertexIndex_of_ne v j hj] using hs

@[simp]
lemma deleteVertexIndex_proof_irrel {n : ℕ} (v : Fin (n + 1)) (i : Fin (n + 1))
    (hi hi' : i ≠ v) :
    deleteVertexIndex v i hi = deleteVertexIndex v i hi' := by
  rw [show hi = hi' from Subsingleton.elim _ _]

namespace AbsTriangle

lemma not_mem_vertices_iff {n : ℕ} {T : AbsTriangle n} {v : Fin n} :
    v ∉ T.vertices ↔ v ≠ T.a ∧ v ≠ T.b ∧ v ≠ T.c := by
  simp [AbsTriangle.vertices]

lemma vertex_ne_of_not_mem {n : ℕ} {T : AbsTriangle n} {v x : Fin n}
    (hT : v ∉ T.vertices) (hx : x ∈ T.vertices) : x ≠ v := by
  intro h
  exact hT (h ▸ hx)

/-- Delete a vertex not used by a triangle, reindexing the remaining vertices
from `Fin (n+1)` to `Fin n`. -/
noncomputable def deleteVertex {n : ℕ} (v : Fin (n + 1)) (T : AbsTriangle (n + 1))
    (hT : v ∉ T.vertices) : AbsTriangle n where
  a := deleteVertexIndex v T.a (vertex_ne_of_not_mem hT (by simp [AbsTriangle.vertices]))
  b := deleteVertexIndex v T.b (vertex_ne_of_not_mem hT (by simp [AbsTriangle.vertices]))
  c := deleteVertexIndex v T.c (vertex_ne_of_not_mem hT (by simp [AbsTriangle.vertices]))
  hab := by
    intro h
    exact T.hab (deleteVertexIndex_injective_on_compl h)
  hbc := by
    intro h
    exact T.hbc (deleteVertexIndex_injective_on_compl h)
  hac := by
    intro h
    exact T.hac (deleteVertexIndex_injective_on_compl h)

@[simp]
lemma succAbove_deleteVertex_a {n : ℕ} (v : Fin (n + 1)) (T : AbsTriangle (n + 1))
    (hT : v ∉ T.vertices) :
    v.succAbove (T.deleteVertex v hT).a = T.a := by
  exact succAbove_deleteVertexIndex_of_ne v T.a
    (vertex_ne_of_not_mem hT (by simp [AbsTriangle.vertices]))

@[simp]
lemma succAbove_deleteVertex_b {n : ℕ} (v : Fin (n + 1)) (T : AbsTriangle (n + 1))
    (hT : v ∉ T.vertices) :
    v.succAbove (T.deleteVertex v hT).b = T.b := by
  exact succAbove_deleteVertexIndex_of_ne v T.b
    (vertex_ne_of_not_mem hT (by simp [AbsTriangle.vertices]))

@[simp]
lemma succAbove_deleteVertex_c {n : ℕ} (v : Fin (n + 1)) (T : AbsTriangle (n + 1))
    (hT : v ∉ T.vertices) :
    v.succAbove (T.deleteVertex v hT).c = T.c := by
  exact succAbove_deleteVertexIndex_of_ne v T.c
    (vertex_ne_of_not_mem hT (by simp [AbsTriangle.vertices]))

lemma deleteVertex_eq_imp {n : ℕ} {v : Fin (n + 1)}
    {T U : AbsTriangle (n + 1)} {hT : v ∉ T.vertices} {hU : v ∉ U.vertices}
    (h : T.deleteVertex v hT = U.deleteVertex v hU) : T = U := by
  have ha : T.a = U.a := by
    have hfield := congrArg AbsTriangle.a h
    have hs := congrArg v.succAbove hfield
    simpa using hs
  have hb : T.b = U.b := by
    have hfield := congrArg AbsTriangle.b h
    have hs := congrArg v.succAbove hfield
    simpa using hs
  have hc : T.c = U.c := by
    have hfield := congrArg AbsTriangle.c h
    have hs := congrArg v.succAbove hfield
    simpa using hs
  cases T
  cases U
  simp_all

lemma deleteVertex_proof_irrel {n : ℕ} {v : Fin (n + 1)}
    (T : AbsTriangle (n + 1)) (hT hT' : v ∉ T.vertices) :
    T.deleteVertex v hT = T.deleteVertex v hT' := by
  rw [show hT = hT' from Subsingleton.elim _ _]

lemma deleteVertex_mem_vertices_of_mem {n : ℕ} {v x : Fin (n + 1)}
    {T : AbsTriangle (n + 1)} (hT : v ∉ T.vertices) (hx : x ∈ T.vertices) :
    deleteVertexIndex v x (vertex_ne_of_not_mem hT hx) ∈
      (T.deleteVertex v hT).vertices := by
  simp only [AbsTriangle.vertices, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl <;> simp [AbsTriangle.deleteVertex]

lemma mem_vertices_of_deleteVertexIndex_mem {n : ℕ} {v x : Fin (n + 1)}
    (hxv : x ≠ v) {T : AbsTriangle (n + 1)} {hT : v ∉ T.vertices}
    (hmem : deleteVertexIndex v x hxv ∈ (T.deleteVertex v hT).vertices) :
    x ∈ T.vertices := by
  simp only [AbsTriangle.vertices, AbsTriangle.deleteVertex, Finset.mem_insert,
    Finset.mem_singleton] at hmem ⊢
  rcases hmem with h | h | h
  · left
    exact deleteVertexIndex_injective_on_compl
      (hj := vertex_ne_of_not_mem hT (by simp [AbsTriangle.vertices])) h
  · right; left
    exact deleteVertexIndex_injective_on_compl
      (hj := vertex_ne_of_not_mem hT (by simp [AbsTriangle.vertices])) h
  · right; right
    exact deleteVertexIndex_injective_on_compl
      (hj := vertex_ne_of_not_mem hT (by simp [AbsTriangle.vertices])) h

lemma vertex_mem_of_mem_edge {n : ℕ} {T : AbsTriangle n} {e : Sym2 (Fin n)}
    {x : Fin n} (he : e ∈ T.edges) (hx : x ∈ e) : x ∈ T.vertices := by
  simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at he
  simp only [AbsTriangle.vertices, Finset.mem_insert, Finset.mem_singleton]
  rcases he with rfl | rfl | rfl <;> simp at hx ⊢ <;> tauto

/-- Delete a vertex from an edge known not to contain it. -/
noncomputable def deleteVertexEdge {n : ℕ} (v : Fin (n + 1)) (e : Sym2 (Fin (n + 1)))
    (he : ∀ x ∈ e, x ≠ v) : Sym2 (Fin n) :=
  Sym2.pmap (P := fun x => x ≠ v) (fun x hx => deleteVertexIndex v x hx) e he

lemma deleteVertexEdge_mem_of_mem {n : ℕ} {v : Fin (n + 1)}
    {T : AbsTriangle (n + 1)} (hT : v ∉ T.vertices) {e : Sym2 (Fin (n + 1))}
    (he : e ∈ T.edges) :
    deleteVertexEdge v e (fun _ hx => vertex_ne_of_not_mem hT
      (vertex_mem_of_mem_edge he hx)) ∈ (T.deleteVertex v hT).edges := by
  simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at he ⊢
  rcases he with rfl | rfl | rfl
  · left
    rw [deleteVertexEdge, Sym2.pmap_pair]
    simp [AbsTriangle.deleteVertex]
  · right; left
    rw [deleteVertexEdge, Sym2.pmap_pair]
    simp [AbsTriangle.deleteVertex]
  · right; right
    rw [deleteVertexEdge, Sym2.pmap_pair]
    simp [AbsTriangle.deleteVertex]

lemma deleteVertexEdge_not_mem {n : ℕ} {v x : Fin (n + 1)} (hxv : x ≠ v)
    {e : Sym2 (Fin (n + 1))} (he : ∀ y ∈ e, y ≠ v) (hxnot : x ∉ e) :
    deleteVertexIndex v x hxv ∉ deleteVertexEdge v e he := by
  intro hmem
  rw [deleteVertexEdge, Sym2.mem_pmap_iff] at hmem
  rcases hmem with ⟨y, hy, hy_eq⟩
  apply hxnot
  have hyx : y = x := deleteVertexIndex_injective_on_compl hy_eq.symm
  simpa [hyx] using hy

lemma deleteVertexEdge_proof_irrel {n : ℕ} (v : Fin (n + 1))
    (e : Sym2 (Fin (n + 1))) (he he' : ∀ x ∈ e, x ≠ v) :
    deleteVertexEdge v e he = deleteVertexEdge v e he' := by
  rw [show he = he' from Subsingleton.elim _ _]

end AbsTriangle

lemma valid_coloring_edge {n : ℕ} {T : AbsTriangle n} {c : Fin n → GuardColor}
    (hc : c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c) {x y : Fin n}
    (h_edge : Sym2.mk x y ∈ T.edges) : c x ≠ c y := by
  simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at h_edge
  rcases h_edge with h | h | h
  · apply Sym2.eq.mp at h; cases h
    · exact hc.1
    · exact hc.1.symm
  · apply Sym2.eq.mp at h; cases h
    · exact hc.2.1
    · exact hc.2.1.symm
  · apply Sym2.eq.mp at h; cases h
    · exact hc.2.2
    · exact hc.2.2.symm

/-- A combinatorial triangulation: inductively, either a single triangle, or
an existing triangulation with one new triangle glued along exactly one edge. -/
inductive TriangulatedPolygon (n : ℕ) : Finset (AbsTriangle n) → Type
  | single (T : AbsTriangle n) :
      TriangulatedPolygon n {T}
  | glue {S : Finset (AbsTriangle n)} (h : TriangulatedPolygon n S)
      (T : AbsTriangle n)
      (newVertex : Fin n)
      (hT_new : newVertex ∈ ({T.a, T.b, T.c} : Finset (Fin n)))
      (hShared : ∃ T' ∈ S, ∃ e ∈ T.edges, e ∈ T'.edges ∧ newVertex ∉ e)
      (hFresh : ∀ T' ∈ S, newVertex ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n))) :
      TriangulatedPolygon n (insert T S)

/-- Vertices of a triangulation. -/
def TriangulatedPolygon.vertices {n : ℕ} {S : Finset (AbsTriangle n)} :
    TriangulatedPolygon n S → Finset (Fin n)
  | .single T => {T.a, T.b, T.c}
  | .glue h _ v _ _ _ => insert v h.vertices

/-- An inductive triangulation always contains at least one triangle. -/
theorem TriangulatedPolygon.card_pos {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) : 0 < S.card := by
  induction h with
  | single T =>
      simp
  | glue h_ind T newV hT_new hShared hFresh ih =>
      exact lt_of_lt_of_le ih (Finset.card_le_card (by intro U hU; simp [hU]))

/-- Every vertex in the inductively recorded vertex set belongs to some
triangle of the triangulation. -/
theorem TriangulatedPolygon.mem_vertices_exists_triangle {n : ℕ}
    {S : Finset (AbsTriangle n)} (h : TriangulatedPolygon n S) {v : Fin n} :
    v ∈ h.vertices → ∃ T ∈ S, v ∈ T.vertices := by
  induction h with
  | single T =>
      intro hv
      refine ⟨T, by simp, ?_⟩
      simpa [TriangulatedPolygon.vertices, AbsTriangle.vertices] using hv
  | glue h_ind T newV hT_new hShared hFresh ih =>
      intro hv
      simp only [TriangulatedPolygon.vertices, Finset.mem_insert] at hv
      rcases hv with rfl | hv_old
      · exact ⟨T, by simp, by simpa [AbsTriangle.vertices] using hT_new⟩
      · rcases ih hv_old with ⟨U, hU, hvU⟩
        exact ⟨U, by simp [hU], hvU⟩

/-- An inductive triangulation with `k` triangles uses exactly `k + 2`
vertices. -/
theorem TriangulatedPolygon.vertices_card {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) : h.vertices.card = S.card + 2 := by
  induction h with
  | single T =>
      simp [TriangulatedPolygon.vertices, T.hab, T.hbc, T.hac]
  | glue h_ind T newV hT_new hShared hFresh ih =>
      rename_i S0
      have hnew_not_old : newV ∉ h_ind.vertices := by
        intro hmem
        rcases h_ind.mem_vertices_exists_triangle hmem with ⟨U, hU, hnewU⟩
        exact hFresh U hU (by simpa [AbsTriangle.vertices] using hnewU)
      have hT_not_mem : T ∉ S0 := by
        intro hT_mem
        exact hFresh T hT_mem hT_new
      simp [TriangulatedPolygon.vertices, Finset.card_insert_of_notMem hnew_not_old,
        Finset.card_insert_of_notMem hT_not_mem, ih]

/-- Reindex a finset of triangles after deleting a vertex avoided by all of
them. -/
noncomputable def deleteVertexTriangles {n : ℕ} (v : Fin (n + 1))
    (S : Finset (AbsTriangle (n + 1))) (hS : ∀ T ∈ S, v ∉ T.vertices) :
    Finset (AbsTriangle n) :=
  S.attach.image fun T => T.1.deleteVertex v (hS T.1 T.2)

lemma deleteVertexTriangles_insert {n : ℕ} (v : Fin (n + 1))
    (S : Finset (AbsTriangle (n + 1))) (T : AbsTriangle (n + 1))
    (hAll : ∀ U ∈ insert T S, v ∉ U.vertices) :
    deleteVertexTriangles v (insert T S) hAll =
      insert (T.deleteVertex v (hAll T (by simp)))
        (deleteVertexTriangles v S (fun U hU => hAll U (by simp [hU]))) := by
  classical
  ext X
  constructor
  · intro hX
    rw [deleteVertexTriangles] at hX
    rcases Finset.mem_image.mp hX with ⟨U, _hUatt, hUX⟩
    rcases Finset.mem_insert.mp U.2 with hUT | hUS
    · apply Finset.mem_insert.mpr
      left
      have hdel :
          U.1.deleteVertex v (hAll U.1 U.2) =
            T.deleteVertex v (hAll T (by simp)) := by
        cases U with
        | mk Uval Uprop =>
            dsimp at hUT ⊢
            subst Uval
            exact AbsTriangle.deleteVertex_proof_irrel T _ _
      exact hUX.symm.trans hdel
    · apply Finset.mem_insert.mpr
      right
      rw [deleteVertexTriangles]
      refine Finset.mem_image.mpr ⟨⟨U.1, hUS⟩, by simp, ?_⟩
      exact (AbsTriangle.deleteVertex_proof_irrel U.1 _ _).trans hUX
  · intro hX
    rw [deleteVertexTriangles]
    rcases Finset.mem_insert.mp hX with hXT | hXS
    · refine Finset.mem_image.mpr ⟨⟨T, by simp⟩, by simp, ?_⟩
      exact (AbsTriangle.deleteVertex_proof_irrel T _ _).trans hXT.symm
    · rw [deleteVertexTriangles] at hXS
      rcases Finset.mem_image.mp hXS with ⟨U, _hUatt, hUX⟩
      refine Finset.mem_image.mpr ⟨⟨U.1, by simp [U.2]⟩, by simp, ?_⟩
      exact (AbsTriangle.deleteVertex_proof_irrel U.1 _ _).trans hUX

lemma deleteVertexTriangles_card {n : ℕ} (v : Fin (n + 1))
    (S : Finset (AbsTriangle (n + 1))) (hS : ∀ T ∈ S, v ∉ T.vertices) :
    (deleteVertexTriangles v S hS).card = S.card := by
  classical
  have hinj :
      Function.Injective
        (fun T : {T : AbsTriangle (n + 1) // T ∈ S} =>
          T.1.deleteVertex v (hS T.1 T.2)) := by
    intro T U hTU
    apply Subtype.ext
    exact AbsTriangle.deleteVertex_eq_imp hTU
  simpa [deleteVertexTriangles] using
    (Finset.card_image_of_injective (s := S.attach)
      (f := fun T : {T : AbsTriangle (n + 1) // T ∈ S} =>
        T.1.deleteVertex v (hS T.1 T.2)) hinj)

noncomputable def TriangulatedPolygon.deleteVertex {n : ℕ}
    {S : Finset (AbsTriangle (n + 1))} (h : TriangulatedPolygon (n + 1) S)
    (v : Fin (n + 1)) (hS : ∀ T ∈ S, v ∉ T.vertices) :
    TriangulatedPolygon n (deleteVertexTriangles v S hS) := by
  induction h generalizing v with
  | single T =>
      simpa [deleteVertexTriangles] using
        (TriangulatedPolygon.single (T.deleteVertex v (hS T (by simp))))
  | glue h_ind T newV hT_new hShared hFresh ih =>
      rename_i S0
      let hS0 : ∀ U ∈ S0, v ∉ U.vertices := fun U hU => hS U (by simp [hU])
      have hT : v ∉ T.vertices := hS T (by simp)
      have hnew_mem_T : newV ∈ T.vertices := by
        simpa [AbsTriangle.vertices] using hT_new
      have hnew_ne : newV ≠ v := AbsTriangle.vertex_ne_of_not_mem hT hnew_mem_T
      let newV' : Fin n := deleteVertexIndex v newV hnew_ne
      let T' : AbsTriangle n := T.deleteVertex v hT
      have hT_new' : newV' ∈ T'.vertices := by
        simpa [newV', T'] using AbsTriangle.deleteVertex_mem_vertices_of_mem hT hnew_mem_T
      have hShared' :
          ∃ T_s ∈ deleteVertexTriangles v S0 hS0, ∃ e ∈ T'.edges,
            e ∈ T_s.edges ∧ newV' ∉ e := by
        rcases hShared with ⟨T_s, hT_s, e, heT, heTs, hnew_not_e⟩
        let hTs : v ∉ T_s.vertices := hS0 T_s hT_s
        let e' : Sym2 (Fin n) :=
          AbsTriangle.deleteVertexEdge v e
            (fun x hx => AbsTriangle.vertex_ne_of_not_mem hT
              (AbsTriangle.vertex_mem_of_mem_edge heT hx))
        refine ⟨T_s.deleteVertex v hTs, ?_, e', ?_, ?_, ?_⟩
        · rw [deleteVertexTriangles]
          refine Finset.mem_image.mpr ⟨⟨T_s, hT_s⟩, by simp, rfl⟩
        · exact AbsTriangle.deleteVertexEdge_mem_of_mem hT heT
        · have hmem := AbsTriangle.deleteVertexEdge_mem_of_mem hTs heTs
          simpa [e', AbsTriangle.deleteVertexEdge_proof_irrel] using hmem
        · exact AbsTriangle.deleteVertexEdge_not_mem hnew_ne _ hnew_not_e
      have hFresh' :
          ∀ T_s ∈ deleteVertexTriangles v S0 hS0,
            newV' ∉ T_s.vertices := by
        intro T_s hT_s hmem
        rw [deleteVertexTriangles] at hT_s
        rcases Finset.mem_image.mp hT_s with ⟨U, _hUatt, hUeq⟩
        have hmem_old : newV ∈ U.1.vertices := by
          apply AbsTriangle.mem_vertices_of_deleteVertexIndex_mem hnew_ne
          simpa [newV', hUeq.symm] using hmem
        have hnot := hFresh U.1 U.2
        have hnot' : newV ∉ U.1.vertices := by
          simpa [AbsTriangle.vertices] using hnot
        exact hnot' hmem_old
      have hglue :
          TriangulatedPolygon n (insert T' (deleteVertexTriangles v S0 hS0)) :=
        TriangulatedPolygon.glue (ih v hS0) T' newV' hT_new' hShared' hFresh'
      rw [deleteVertexTriangles_insert]
      exact hglue

theorem TriangulatedPolygon.exists_3coloring {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ c : Fin n → GuardColor,
      ∀ T ∈ S, c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c := by
  induction h with
  | single T =>
      refine ⟨fun v => if v = T.a then red else if v = T.b then green else blue, ?_⟩
      intro T' hT'
      have h_eq : T' = T := Finset.mem_singleton.mp hT'
      cases h_eq
      have hab' : T.b ≠ T.a := T.hab.symm
      have hbc' : T.c ≠ T.b := T.hbc.symm
      have hac' : T.c ≠ T.a := T.hac.symm
      refine ⟨?_, ?_, ?_⟩ <;> simp [hab', hbc', hac']
  | glue h_ind T v hT_new hShared hFresh ih =>
      obtain ⟨c, hc⟩ := ih
      let c_new := fun x => if x = v then
        other_color (if T.a = v then c T.b else c T.a) (if T.c = v then c T.b else c T.c)
      else c x
      refine ⟨c_new, ?_⟩
      intro T'' hT''
      simp only [Finset.mem_insert] at hT''
      cases hT'' with
      | inl h_eq =>
        -- T'' = T
        rw [h_eq]
        dsimp [c_new]
        have hv : v = T.a ∨ v = T.b ∨ v = T.c := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hT_new
          exact hT_new
        rcases hShared with ⟨T_s, hT_s_S, e, heT, heT_s, hvne⟩
        have he_color : ∀ x y, e = Sym2.mk x y → c x ≠ c y := by
          intro x y hxy
          subst hxy
          exact valid_coloring_edge (hc T_s hT_s_S) heT_s
        rcases hv with rfl | rfl | rfl
        · -- v = T.a
          have h1 : T.b ≠ T.a := T.hab.symm
          have h2 : T.c ≠ T.a := T.hac.symm
          simp only [h1, h2, if_false, if_true]
          have h_e_is_bc : e = Sym2.mk T.b T.c := by
            simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at heT
            rcases heT with h | h | h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_left _ _
            · exact h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_left _ _
          have hc_bc : c T.b ≠ c T.c := he_color T.b T.c h_e_is_bc
          refine ⟨?_, ?_, ?_⟩
          · exact other_color_neq_left _ _
          · exact hc_bc
          · exact other_color_neq_right _ _
        · -- v = T.b
          have h1 : T.a ≠ T.b := T.hab
          have h2 : T.c ≠ T.b := T.hbc.symm
          simp only [h1, h2, if_false, if_true]
          have h_e_is_ac : e = Sym2.mk T.a T.c := by
            simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at heT
            rcases heT with h | h | h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_right _ _
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_left _ _
            · exact h
          have hc_ac : c T.a ≠ c T.c := he_color T.a T.c h_e_is_ac
          refine ⟨?_, ?_, ?_⟩
          · exact (other_color_neq_left (c T.a) (c T.c)).symm
          · exact other_color_neq_right (c T.a) (c T.c)
          · exact hc_ac
        · -- v = T.c
          have h1 : T.a ≠ T.c := T.hac
          have h2 : T.b ≠ T.c := T.hbc
          simp only [h1, h2, if_false, if_true]
          have h_e_is_ab : e = Sym2.mk T.a T.b := by
            simp only [AbsTriangle.edges, Finset.mem_insert, Finset.mem_singleton] at heT
            rcases heT with h | h | h
            · exact h
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_right _ _
            · exfalso; apply hvne; rw [h]; exact Sym2.mem_mk_right _ _
          have hc_ab : c T.a ≠ c T.b := he_color T.a T.b h_e_is_ab
          refine ⟨?_, ?_, ?_⟩
          · exact hc_ab
          · exact (other_color_neq_right (c T.a) (c T.b)).symm
          · exact (other_color_neq_left (c T.a) (c T.b)).symm
      | inr hT''S =>
        -- T'' ∈ S
        have h_v_notin : v ∉ ({T''.a, T''.b, T''.c} : Finset (Fin n)) := hFresh T'' hT''S
        have h1 : T''.a ≠ v := by intro h; apply h_v_notin; simp [h]
        have h2 : T''.b ≠ v := by intro h; apply h_v_notin; simp [h]
        have h3 : T''.c ≠ v := by intro h; apply h_v_notin; simp [h]
        dsimp [c_new]
        simp [h1, h2, h3]
        exact hc T'' hT''S

/-- Any TriangulatedPolygon with ≥ 2 triangles has a triangle with a
"free" vertex (degree 1 in the triangulation, i.e., the ear). -/
theorem TriangulatedPolygon.exists_ear {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) (hS : S.card ≥ 2) :
    ∃ T ∈ S, ∃ v ∈ ({T.a, T.b, T.c} : Finset (Fin n)),
      ∀ T' ∈ S, T' ≠ T → v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n)) := by
  cases h with
  | single T =>
      exfalso
      simp only [Finset.card_singleton] at hS
      omega
  | glue h_ind T newV hT_new hShared hFresh =>
      refine ⟨T, by simp, newV, hT_new, ?_⟩
      intro T' hT' hne
      have h_eq := Finset.mem_insert.mp hT'
      cases h_eq with
      | inl hT_eq => exact absurd hT_eq hne
      | inr hT_S => exact hFresh T' hT_S

/-- Deleting a free ear from an inductive triangulation leaves the previous
inductive triangulation.  This is the combinatorial ear-clipping step. -/
structure TriangulatedPolygon.EarRemoval {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) where
  ear : AbsTriangle n
  vertex : Fin n
  remainder : Finset (AbsTriangle n)
  ear_mem : ear ∈ S
  vertex_mem : vertex ∈ ear.vertices
  remainder_triangulated : TriangulatedPolygon n remainder
  erase_eq : S.erase ear = remainder
  remainder_card_add_one : remainder.card + 1 = S.card
  free_vertex :
    ∀ T' ∈ S, T' ≠ ear → vertex ∉ T'.vertices

def TriangulatedPolygon.exists_earRemoval {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) (hS : S.card ≥ 2) :
    h.EarRemoval := by
  cases h with
  | single T =>
      exfalso
      simp only [Finset.card_singleton] at hS
      omega
  | glue h_ind T newV hT_new hShared hFresh =>
      rename_i S0
      have hT_not_mem : T ∉ S0 := by
        intro hT_mem
        exact hFresh T hT_mem hT_new
      refine
        { ear := T
          vertex := newV
          remainder := _
          ear_mem := by simp
          vertex_mem := by simpa [AbsTriangle.vertices] using hT_new
          remainder_triangulated := h_ind
          erase_eq := by simp [hT_not_mem]
          remainder_card_add_one := by
            rw [Finset.card_insert_of_notMem hT_not_mem]
          free_vertex := ?_ }
      intro T' hT' hne
      have h_eq := Finset.mem_insert.mp hT'
      cases h_eq with
      | inl hT_eq => exact absurd hT_eq hne
      | inr hT_S =>
          simpa [AbsTriangle.vertices] using hFresh T' hT_S

theorem TriangulatedPolygon.erase_ear_card {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) (hS : S.card ≥ 2) :
    ∃ T ∈ S, (S.erase T).card + 1 = S.card := by
  let R := h.exists_earRemoval hS
  refine ⟨R.ear, R.ear_mem, ?_⟩
  rw [R.erase_eq]
  exact R.remainder_card_add_one

/-- The ambient plane used for the geometric Chapter 36 interface. -/
abbrev Point2 : Type := ℝ × ℝ

/-- The closed triangle determined by three vertices of a planar polygon. -/
def polygonTriangleSet {n : ℕ} (poly : Polygon Point2 n) (a b c : Fin n) :
    Set Point2 :=
  convexHull ℝ ({poly a, poly b, poly c} : Set Point2)

/-- The realization of an abstract triangle in a concrete planar polygon. -/
def AbsTriangle.realization {n : ℕ} (T : AbsTriangle n) (poly : Polygon Point2 n) :
    Set Point2 :=
  polygonTriangleSet poly T.a T.b T.c

/-- Every abstract vertex of a triangle realizes to a point of its closed
geometric triangle. -/
lemma AbsTriangle.vertex_mem_realization {n : ℕ} (T : AbsTriangle n)
    (poly : Polygon Point2 n) {v : Fin n} (hv : v ∈ T.vertices) :
    poly v ∈ T.realization poly := by
  apply subset_convexHull ℝ ({poly T.a, poly T.b, poly T.c} : Set Point2)
  simp only [AbsTriangle.vertices, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> simp

/-- The previous index in the cyclic order. -/
def cyclicPrev {n : ℕ} (i : Fin n) : Fin n :=
  (finRotate n).symm i

/-- The next index in the cyclic order. -/
def cyclicNext {n : ℕ} (i : Fin n) : Fin n :=
  finRotate n i

/-- A certified simple polygon: a cyclic sequence of planar vertices together
with an ear-clipping triangulation certificate on exactly those `n` vertices.

The geometric simplicity/Jordan-curve part is represented here by the
certificate rather than by a raw edge-crossing predicate, because Mathlib does
not yet provide the planar interior API needed to prove ear clipping from only
edge nonintersection data. -/
structure SimplePolygon (n : ℕ) where
  toPolygon : Polygon Point2 n
  vertices_injective : Function.Injective toPolygon.vertices
  triangles : Finset (AbsTriangle n)
  triangulated : TriangulatedPolygon n triangles
  triangle_count : triangles.card + 2 = n

namespace SimplePolygon

/-- The certified triangulation of a simple polygon is nonempty. -/
theorem triangles_card_pos {n : ℕ} (P : SimplePolygon n) : 0 < P.triangles.card :=
  P.triangulated.card_pos

/-- A certified simple polygon has at least three vertices. -/
theorem vertex_count_ge_three {n : ℕ} (P : SimplePolygon n) : 3 ≤ n := by
  have hpos := P.triangles_card_pos
  have hcount := P.triangle_count
  omega

/-- A certified simple polygon on three vertices has exactly one certified
triangle. -/
theorem triangles_card_eq_one_of_three (P : SimplePolygon 3) : P.triangles.card = 1 := by
  have hcount := P.triangle_count
  omega

/-- Base case for ear-clipping induction: a certified simple triangle has a
singleton triangulation. -/
theorem exists_single_triangle_of_three (P : SimplePolygon 3) :
    ∃ T : AbsTriangle 3, P.triangles = {T} :=
  Finset.card_eq_one.mp P.triangles_card_eq_one_of_three

/-- The polygonal region covered by the certified triangulation. -/
def carrier {n : ℕ} (P : SimplePolygon n) : Set Point2 :=
  {x | ∃ T ∈ P.triangles, x ∈ T.realization P.toPolygon}

/-- A certified polygon is convex when its triangulated carrier is convex. -/
def IsConvex {n : ℕ} (P : SimplePolygon n) : Prop :=
  Convex ℝ P.carrier

/-- The geometric triangle cut off by the previous, current, and next cyclic
vertices. -/
def earTriangleAt {n : ℕ} (P : SimplePolygon n) (i : Fin n) : Set Point2 :=
  polygonTriangleSet P.toPolygon (cyclicPrev i) i (cyclicNext i)

/-- The triangulation certificate of a `SimplePolygon` covers every indexed
vertex. -/
theorem triangulation_vertices_eq_univ {n : ℕ} (P : SimplePolygon n) :
    P.triangulated.vertices = Finset.univ := by
  refine Finset.eq_univ_of_card P.triangulated.vertices ?_
  have hcard : P.triangulated.vertices.card = n := by
    rw [P.triangulated.vertices_card, P.triangle_count]
  simpa [Fintype.card_fin] using hcard

/-- Every indexed polygon vertex lies in the certified polygonal carrier. -/
theorem vertex_mem_carrier {n : ℕ} (P : SimplePolygon n) (i : Fin n) :
    P.toPolygon i ∈ P.carrier := by
  have hi : i ∈ P.triangulated.vertices := by
    rw [P.triangulation_vertices_eq_univ]
    simp
  rcases P.triangulated.mem_vertices_exists_triangle hi with ⟨T, hT, hiT⟩
  exact ⟨T, hT, AbsTriangle.vertex_mem_realization T P.toPolygon hiT⟩

/-- In a convex certified polygon, every adjacent-vertex triangle is contained
in the polygonal carrier. -/
theorem earTriangleAt_subset_carrier_of_convex {n : ℕ} (P : SimplePolygon n)
    (hconv : P.IsConvex) (i : Fin n) :
    P.earTriangleAt i ⊆ P.carrier := by
  dsimp [earTriangleAt, polygonTriangleSet]
  refine convexHull_min ?_ hconv
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact P.vertex_mem_carrier (cyclicPrev i)
  · exact P.vertex_mem_carrier i
  · exact P.vertex_mem_carrier (cyclicNext i)

/-- A consecutive geometric ear at vertex `i`: the adjacent-vertex triangle is
nondegenerate and lies in the polygonal region. -/
structure ConsecutiveEarAt {n : ℕ} (P : SimplePolygon n) (i : Fin n) : Prop where
  nondegenerate :
    AffineIndependent ℝ ![P.toPolygon (cyclicPrev i), P.toPolygon i,
      P.toPolygon (cyclicNext i)]
  inside : P.earTriangleAt i ⊆ P.carrier

/-- A convex certified polygon has a consecutive geometric ear at any
nondegenerate vertex. -/
theorem consecutiveEarAt_of_convex {n : ℕ} (P : SimplePolygon n) (i : Fin n)
    (hconv : P.IsConvex)
    (hnd : AffineIndependent ℝ ![P.toPolygon (cyclicPrev i), P.toPolygon i,
      P.toPolygon (cyclicNext i)]) :
    P.ConsecutiveEarAt i where
  nondegenerate := hnd
  inside := P.earTriangleAt_subset_carrier_of_convex hconv i

/-- For a convex certified polygon with nondegenerate adjacent triples, every
vertex is a consecutive geometric ear. -/
theorem all_vertices_consecutiveEars_of_convex {n : ℕ} (P : SimplePolygon n)
    (hconv : P.IsConvex)
    (hnd : ∀ i : Fin n,
      AffineIndependent ℝ ![P.toPolygon (cyclicPrev i), P.toPolygon i,
        P.toPolygon (cyclicNext i)]) :
    ∀ i : Fin n, P.ConsecutiveEarAt i := by
  intro i
  exact P.consecutiveEarAt_of_convex i hconv (hnd i)

/-- Convex triangular polygons have the trivial triangulation and all three
vertices are consecutive geometric ears. -/
theorem convex_triangle_triangulation_trivial (P : SimplePolygon 3)
    (hconv : P.IsConvex)
    (hnd : ∀ i : Fin 3,
      AffineIndependent ℝ ![P.toPolygon (cyclicPrev i), P.toPolygon i,
        P.toPolygon (cyclicNext i)]) :
    (∃ T : AbsTriangle 3, P.triangles = {T}) ∧
      ∀ i : Fin 3, P.ConsecutiveEarAt i :=
  ⟨P.exists_single_triangle_of_three, P.all_vertices_consecutiveEars_of_convex hconv hnd⟩

/-- The ear supplied by a triangulation: `v` is a free vertex of triangle `T`,
and the triangle is inside the certified polygonal region. -/
structure Ear {n : ℕ} (P : SimplePolygon n) (T : AbsTriangle n) (v : Fin n) :
    Prop where
  triangle_mem : T ∈ P.triangles
  vertex_mem : v ∈ ({T.a, T.b, T.c} : Finset (Fin n))
  free_vertex :
    ∀ T' ∈ P.triangles, T' ≠ T →
      v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n))
  inside : T.realization P.toPolygon ⊆ P.carrier

/-- The polygon obtained by deleting one indexed vertex from the cyclic list. -/
def removeVertexPolygon {n : ℕ} (P : SimplePolygon (n + 1)) (v : Fin (n + 1)) :
    Polygon Point2 n where
  vertices := fun i => P.toPolygon (v.succAbove i)

theorem removeVertexPolygon_vertices_injective {n : ℕ} (P : SimplePolygon (n + 1))
    (v : Fin (n + 1)) : Function.Injective (P.removeVertexPolygon v).vertices := by
  intro i j hij
  apply Fin.succAbove_right_injective
  exact P.vertices_injective hij

/-- A triangle of the remaining triangulation after deleting an ear vertex. -/
noncomputable def remainingTriangle {n : ℕ} (P : SimplePolygon (n + 1))
    {T : AbsTriangle (n + 1)} {v : Fin (n + 1)} (E : P.Ear T v)
    (U : {U : AbsTriangle (n + 1) // U ∈ P.triangles.erase T}) : AbsTriangle n :=
  U.1.deleteVertex v (by
    have hfree := E.free_vertex U.1 (Finset.mem_of_mem_erase U.2)
      (Finset.mem_erase.mp U.2).1
    simpa [AbsTriangle.vertices] using hfree)

theorem remainingTriangle_injective {n : ℕ} (P : SimplePolygon (n + 1))
    {T : AbsTriangle (n + 1)} {v : Fin (n + 1)} (E : P.Ear T v) :
    Function.Injective (P.remainingTriangle E) := by
  intro U W hUW
  apply Subtype.ext
  exact AbsTriangle.deleteVertex_eq_imp hUW

/-- The abstract triangles left after deleting an ear triangle and reindexing
away its free vertex. -/
noncomputable def earClippedTriangles {n : ℕ} (P : SimplePolygon (n + 1))
    {T : AbsTriangle (n + 1)} {v : Fin (n + 1)} (E : P.Ear T v) :
    Finset (AbsTriangle n) :=
  (P.triangles.erase T).attach.image (P.remainingTriangle E)

theorem earClippedTriangles_card {n : ℕ} (P : SimplePolygon (n + 1))
    {T : AbsTriangle (n + 1)} {v : Fin (n + 1)} (E : P.Ear T v) :
    (P.earClippedTriangles E).card = (P.triangles.erase T).card := by
  classical
  simpa [earClippedTriangles] using
    (Finset.card_image_of_injective (s := (P.triangles.erase T).attach)
      (f := P.remainingTriangle E) (P.remainingTriangle_injective E))

theorem earClippedTriangles_card_add_two {n : ℕ} (P : SimplePolygon (n + 1))
    {T : AbsTriangle (n + 1)} {v : Fin (n + 1)} (E : P.Ear T v) :
    (P.earClippedTriangles E).card + 2 = n := by
  have herase := Finset.card_erase_add_one E.triangle_mem
  have hcount := P.triangle_count
  rw [P.earClippedTriangles_card E]
  omega

/-- Convert the triangulation-level ear-removal certificate into the smaller
certified simple polygon.  The vertex list is `P` with `R.vertex` deleted, and
the remaining triangulation is reindexed along `R.vertex.succAbove`. -/
noncomputable def clipEar {n : ℕ} (P : SimplePolygon (n + 1))
    (R : P.triangulated.EarRemoval) : SimplePolygon n :=
  let hAvoid : ∀ T ∈ R.remainder, R.vertex ∉ T.vertices := by
    intro T hT
    have hErase : T ∈ P.triangles.erase R.ear := by
      rwa [R.erase_eq]
    exact R.free_vertex T (Finset.mem_of_mem_erase hErase) (Finset.mem_erase.mp hErase).1
  { toPolygon := P.removeVertexPolygon R.vertex
    vertices_injective := P.removeVertexPolygon_vertices_injective R.vertex
    triangles := deleteVertexTriangles R.vertex R.remainder hAvoid
    triangulated := R.remainder_triangulated.deleteVertex R.vertex hAvoid
    triangle_count := by
      have hcard := deleteVertexTriangles_card R.vertex R.remainder hAvoid
      have hrem := R.remainder_card_add_one
      have hcount := P.triangle_count
      rw [hcard]
      omega }

@[simp]
theorem clipEar_toPolygon {n : ℕ} (P : SimplePolygon (n + 1))
    (R : P.triangulated.EarRemoval) :
    (P.clipEar R).toPolygon = P.removeVertexPolygon R.vertex := rfl

/-- Extract the certified triangulation of a simple polygon as data. -/
def triangulatedPolygon {n : ℕ} (P : SimplePolygon n) :
    Σ S : Finset (AbsTriangle n), TriangulatedPolygon n S :=
  ⟨P.triangles, P.triangulated⟩

/-- Extract the certified triangulation of a simple polygon as an existential
proposition. -/
theorem exists_triangulatedPolygon {n : ℕ} (P : SimplePolygon n) :
    ∃ S : Finset (AbsTriangle n), Nonempty (TriangulatedPolygon n S) :=
  ⟨P.triangles, ⟨P.triangulated⟩⟩

/-- The certified ear-removal decomposition of a simple polygon with at least
four vertices. -/
def earRemoval {n : ℕ} (P : SimplePolygon n) (hn : 4 ≤ n) :
    P.triangulated.EarRemoval := by
  have hcard : P.triangles.card ≥ 2 := by
    have hcount := P.triangle_count
    omega
  exact P.triangulated.exists_earRemoval hcard

/-- The canonical one-step ear clipping operation for a certified polygon with
`n+1` vertices.  Its result is a certified polygon on `n` vertices. -/
noncomputable def removeEar {n : ℕ} (P : SimplePolygon (n + 1)) (hn : 4 ≤ n + 1) :
    SimplePolygon n :=
  P.clipEar (P.earRemoval hn)

theorem removeEar_triangle_count {n : ℕ} (P : SimplePolygon (n + 1)) (hn : 4 ≤ n + 1) :
    (P.removeEar hn).triangles.card + 2 = n :=
  (P.removeEar hn).triangle_count

/-- Induction on certified simple polygons by repeatedly clipping ears.

The base case is `n = 3`; the step receives the polygon with one certified ear
removed, whose vertex type is one smaller. -/
theorem induction_on_vertices
    {motive : (n : ℕ) → SimplePolygon n → Prop}
    (hbase : ∀ P : SimplePolygon 3, motive 3 P)
    (hstep : ∀ n (P : SimplePolygon (n + 1)) (hn : 4 ≤ n + 1),
      motive n (P.removeEar hn) → motive (n + 1) P)
    {n : ℕ} (P : SimplePolygon n) : motive n P := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hn3 : 3 ≤ n := P.vertex_count_ge_three
      rcases Nat.eq_or_lt_of_le hn3 with hn_eq | hn_gt
      · subst n
        exact hbase P
      · cases n with
        | zero => omega
        | succ k =>
            have hn : 4 ≤ k + 1 := by omega
            exact hstep k P hn (ih k (by omega) (P.removeEar hn))

theorem erase_ear_reduces_triangle_count {n : ℕ} (P : SimplePolygon n) (hn : 4 ≤ n) :
    ∃ T ∈ P.triangles, (P.triangles.erase T).card + 1 = P.triangles.card := by
  let R := P.earRemoval hn
  refine ⟨R.ear, R.ear_mem, ?_⟩
  rw [R.erase_eq]
  exact R.remainder_card_add_one

/-- Every certified simple polygon with at least four vertices has a
triangulation ear.  The induction is the one in
`TriangulatedPolygon.exists_ear`. -/
theorem exists_ear {n : ℕ} (P : SimplePolygon n) (hn : 4 ≤ n) :
    ∃ T : AbsTriangle n, ∃ v : Fin n, P.Ear T v := by
  let R := P.earRemoval hn
  refine ⟨R.ear, R.vertex, ?_⟩
  refine ⟨R.ear_mem, ?_, ?_, ?_⟩
  · simpa [AbsTriangle.vertices] using R.vertex_mem
  · intro T' hT' hne
    simpa [AbsTriangle.vertices] using R.free_vertex T' hT' hne
  intro x hx
  exact ⟨R.ear, R.ear_mem, hx⟩

/-- The vertex of a certified ear sees every point of the ear triangle inside
the certified polygonal carrier. -/
theorem Ear.sees_triangle {n : ℕ} {P : SimplePolygon n} {T : AbsTriangle n}
    {v : Fin n} (E : P.Ear T v) :
    ∀ x ∈ T.realization P.toPolygon, segment ℝ (P.toPolygon v) x ⊆ P.carrier := by
  intro x hx
  have hvertex : P.toPolygon v ∈ T.realization P.toPolygon :=
    AbsTriangle.vertex_mem_realization T P.toPolygon E.vertex_mem
  have hconv : Convex ℝ (T.realization P.toPolygon) := by
    simpa [AbsTriangle.realization, polygonTriangleSet] using
      (convex_convexHull ℝ
        ({P.toPolygon T.a, P.toPolygon T.b, P.toPolygon T.c} : Set Point2))
  exact subset_trans (hconv.segment_subset hvertex hx) E.inside

end SimplePolygon

/-- Vertices of one color class in a finite polygon vertex set. -/
def colorClass {V : Type*} [DecidableEq V] (vertices : Finset V) (color : V → GuardColor)
    (c : GuardColor) : Finset V :=
  vertices.filter fun v => color v = c

theorem colorClass_card_sum {V : Type*} [DecidableEq V] (vertices : Finset V)
    (color : V → GuardColor) :
    (colorClass vertices color red).card + (colorClass vertices color green).card +
        (colorClass vertices color blue).card = vertices.card := by
  classical
  have hcover : (Finset.univ.biUnion (fun c => colorClass vertices color c)) = vertices := by
    ext v
    simp [colorClass]
  have hdisj : ((Finset.univ : Finset GuardColor) : Set GuardColor).PairwiseDisjoint
      (fun c => colorClass vertices color c) := by
    intro a _ b _ hab
    change Disjoint (colorClass vertices color a) (colorClass vertices color b)
    rw [Finset.disjoint_left]
    intro v hva hvb
    simp [colorClass] at hva hvb
    exact hab (hva.2.symm.trans hvb.2)
  have hcard := Finset.card_biUnion (s := (Finset.univ : Finset GuardColor))
    (t := fun c => colorClass vertices color c) hdisj
  rw [hcover] at hcard
  have hsum : (∑ c : GuardColor, (colorClass vertices color c).card) = vertices.card := by
    simpa using hcard.symm
  have huniv : (Finset.univ : Finset GuardColor) = {red, green, blue} := by
    ext c
    cases c <;> simp
  rw [← hsum]
  rw [show (∑ c : GuardColor, (colorClass vertices color c).card) =
      (colorClass vertices color red).card + (colorClass vertices color green).card +
        (colorClass vertices color blue).card by
    rw [show (Finset.univ : Finset GuardColor) = {red, green, blue} from huniv]
    simp [add_assoc]]

theorem min_three_color_classes_le_div_three (red green blue : ℕ) :
    min red (min green blue) ≤ (red + green + blue) / 3 := by
  by_contra h
  have hred : (red + green + blue) / 3 < red :=
    lt_of_not_ge fun hred => h (le_trans (min_le_left _ _) hred)
  have hgreen : (red + green + blue) / 3 < green :=
    lt_of_not_ge fun hgreen =>
      h (le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) hgreen)
  have hblue : (red + green + blue) / 3 < blue :=
    lt_of_not_ge fun hblue =>
      h (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hblue)
  omega

lemma three_colors_cover (c1 c2 c3 target : GuardColor) (h1 : c1 ≠ c2) (h2 : c2 ≠ c3) (h3 : c1 ≠ c3) :
    c1 = target ∨ c2 = target ∨ c3 = target := by
  cases c1 <;> cases c2 <;> cases c3 <;> cases target <;>
    (try simp) <;>
    (exfalso; first | exact h1 rfl | exact h2 rfl | exact h3 rfl)

theorem chapter36_artgallery_combinatorial {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ T ∈ S, ∃ v ∈ guards,
        v ∈ ({T.a, T.b, T.c} : Finset (Fin n)) := by
  obtain ⟨c, hc⟩ := h.exists_3coloring
  let r := colorClass (Finset.univ : Finset (Fin n)) c red
  let g := colorClass (Finset.univ : Finset (Fin n)) c green
  let b := colorClass (Finset.univ : Finset (Fin n)) c blue
  have hsum : r.card + g.card + b.card = n := by
    have h_sum := colorClass_card_sum (Finset.univ : Finset (Fin n)) c
    rwa [Finset.card_univ, Fintype.card_fin] at h_sum
  have hmin : min r.card (min g.card b.card) ≤ n / 3 := by
    calc
      min r.card (min g.card b.card) ≤ (r.card + g.card + b.card) / 3 :=
        min_three_color_classes_le_div_three r.card g.card b.card
      _ = n / 3 := by rw [hsum]
  
  have h_hit : ∀ (guard_color : GuardColor) (T : AbsTriangle n) 
    (hT : c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c),
    ∃ v ∈ colorClass (Finset.univ : Finset (Fin n)) c guard_color, v ∈ ({T.a, T.b, T.c} : Finset (Fin n)) := by
    intro gc T hT
    have h_match := three_colors_cover (c T.a) (c T.b) (c T.c) gc hT.1 hT.2.1 hT.2.2
    rcases h_match with ha | hb | hc_match
    · refine ⟨T.a, ?_, by simp⟩
      simp [colorClass, ha]
    · refine ⟨T.b, ?_, by simp⟩
      simp [colorClass, hb]
    · refine ⟨T.c, ?_, by simp⟩
      simp [colorClass, hc_match]

  by_cases hr : r.card = min r.card (min g.card b.card)
  · refine ⟨r, ?_, ?_⟩
    · rw [hr]
      exact hmin
    · intro tri htri
      exact h_hit red tri (hc tri htri)
  · by_cases hg : g.card = min r.card (min g.card b.card)
    · refine ⟨g, ?_, ?_⟩
      · rw [hg]
        exact hmin
      · intro tri htri
        exact h_hit green tri (hc tri htri)
    · refine ⟨b, ?_, ?_⟩
      · have hb_min : b.card = min r.card (min g.card b.card) := by
          have hle_r : min r.card (min g.card b.card) ≤ r.card := min_le_left _ _
          have hle_g : min r.card (min g.card b.card) ≤ g.card :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          have hle_b : min r.card (min g.card b.card) ≤ b.card :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          omega
        rw [hb_min]
        exact hmin
      · intro tri htri
        exact h_hit blue tri (hc tri htri)

/-- Canonical Chapter 36 entry point: the closed combinatorial art-gallery theorem. -/
theorem chapter36 {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ T ∈ S, ∃ v ∈ guards,
        v ∈ ({T.a, T.b, T.c} : Finset (Fin n)) :=
  chapter36_artgallery_combinatorial h

/-- The Chapter 36 guard bound for a certified simple polygon, using its
ear-clipping triangulation certificate. -/
theorem chapter36_simplePolygon {n : ℕ} (P : SimplePolygon n) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ T ∈ P.triangles, ∃ v ∈ guards,
        v ∈ ({T.a, T.b, T.c} : Finset (Fin n)) :=
  chapter36 P.triangulated

/-- Carrier-level art-gallery statement for a certified simple polygon: every
point in the certified polygonal region is visible from one of the selected
guard vertices. -/
theorem chapter36_simplePolygon_visibility {n : ℕ} (P : SimplePolygon n) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x ∈ P.carrier, ∃ v ∈ guards, segment ℝ (P.toPolygon v) x ⊆ P.carrier := by
  obtain ⟨guards, hcard, hhit⟩ := chapter36_simplePolygon P
  refine ⟨guards, hcard, ?_⟩
  intro x hx
  rcases hx with ⟨T, hT, hxT⟩
  rcases hhit T hT with ⟨v, hvG, hvT⟩
  refine ⟨v, hvG, ?_⟩
  have hvT' : v ∈ T.vertices := by
    simpa [AbsTriangle.vertices] using hvT
  have hvertex : P.toPolygon v ∈ T.realization P.toPolygon :=
    AbsTriangle.vertex_mem_realization T P.toPolygon hvT'
  have hconv : Convex ℝ (T.realization P.toPolygon) := by
    simpa [AbsTriangle.realization, polygonTriangleSet] using
      (convex_convexHull ℝ
        ({P.toPolygon T.a, P.toPolygon T.b, P.toPolygon T.c} : Set Point2))
  have hseg : segment ℝ (P.toPolygon v) x ⊆ T.realization P.toPolygon :=
    hconv.segment_subset hvertex hxT
  exact subset_trans hseg (by
    intro y hy
    exact ⟨T, hT, hy⟩)

end ProofsInTheBook.Chapter36
