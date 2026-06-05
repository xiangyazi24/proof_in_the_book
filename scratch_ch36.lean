import Mathlib

namespace ProofsInTheBook.Chapter36

inductive GuardColor where
  | red | green | blue
  deriving DecidableEq, Repr, Fintype

open GuardColor

def other_color (c1 c2 : GuardColor) : GuardColor :=
  if c1 = c2 then
    if c1 = red then green else red
  else
    if c1 = red ∧ c2 = green ∨ c2 = red ∧ c1 = green then blue
    else if c1 = red ∧ c2 = blue ∨ c2 = red ∧ c1 = blue then green
    else red

/-- A triangle on three distinct vertices of `Fin n`. -/
structure AbsTriangle (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  hab : a ≠ b
  hbc : b ≠ c
  hac : a ≠ c

/-- The (undirected) edges of an abstract triangle, as a finset of unordered
pairs. -/
def AbsTriangle.edges {n : ℕ} (T : AbsTriangle n) : Finset (Sym2 (Fin n)) :=
  {Sym2.mk (T.a, T.b), Sym2.mk (T.b, T.c), Sym2.mk (T.a, T.c)}

/-- A combinatorial triangulation: inductively, either a single triangle, or
an existing triangulation with one new triangle glued along exactly one edge. -/
inductive TriangulatedPolygon (n : ℕ) : Finset (AbsTriangle n) → Prop
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
  | .glue h T v _ _ _ => insert v h.vertices

theorem TriangulatedPolygon.exists_3coloring {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ c : Fin n → GuardColor,
      ∀ T ∈ S, c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c := by
  induction h with
  | single T =>
      refine ⟨fun v => if v = T.a then red else if v = T.b then green else blue, ?_⟩
      intro T' hT'
      simp only [Finset.mem_singleton] at hT'
      subst hT'
      refine ⟨?_, ?_, ?_⟩ <;> (simp [T.hab, T.hbc, T.hac, T.hab.symm, T.hbc.symm, T.hac.symm]; decide)
  | glue h_ind T v hT_new hShared hFresh ih =>
      obtain ⟨c, hc⟩ := ih
      let c_new := fun x => if x = v then
        other_color (if T.a = v then c T.b else c T.a) (if T.c = v then c T.b else c T.c)
      else c x
      refine ⟨c_new, ?_⟩
      intro T'' hT''
      simp only [Finset.mem_insert] at hT''
      rcases hT'' with rfl | hT''S
      · -- T'' = T
        dsimp [c_new]
        sorry
      · -- T'' ∈ S
        have h_v_notin : v ∉ ({T''.a, T''.b, T''.c} : Finset (Fin n)) := hFresh T'' hT''S
        simp only [Finset.mem_insert, Finset.mem_singleton] at h_v_notin
        have h1 : T''.a ≠ v := by intro h; apply h_v_notin; simp [h]
        have h2 : T''.b ≠ v := by intro h; apply h_v_notin; simp [h]
        have h3 : T''.c ≠ v := by intro h; apply h_v_notin; simp [h]
        dsimp [c_new]
        simp [h1, h2, h3]
        exact hc T'' hT''S

end ProofsInTheBook.Chapter36
