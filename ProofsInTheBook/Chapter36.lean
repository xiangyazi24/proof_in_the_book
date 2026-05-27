import Mathlib

/-!
# Chapter 36: Art galleries

This file proves the combinatorial core of the art gallery theorem: any
abstract polygon triangulation has a 3-coloring, and the smallest color
class gives at most `⌊n / 3⌋` guards meeting every triangle.

Geometry gap audit (2026-05-24): Mathlib has `Geometry.Polygon.Basic`, which
currently provides a vertex-indexed `Polygon`, edge sets, boundary, and
conversion between 3-polygons and affine triangles.  It does not yet provide
the infrastructure needed to state and prove the full geometric art gallery
theorem:

* a definition of a simple polygon as a planar polygonal Jordan curve,
* the polygon interior and the visibility relation from a guard point,
* diagonals lying inside the polygon,
* an ear theorem or equivalent induction step, and
* existence of a triangulation of every simple polygon, together with a proof
  that guards hitting all triangles cover the polygon.

Consequently `chapter36_artgallery_combinatorial` is the closed theorem in
this file.  Extending it to "every simple polygon with `n` vertices is guarded
by `⌊n / 3⌋` vertices" should wait for that geometry layer rather than adding
an unproved triangulation postulate or a placeholder structure here.
-/

namespace ProofsInTheBook.Chapter36

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

/-! ### Concrete combinatorial witnesses

The remaining frontier in this chapter is the geometric existence of a
`TriangulatedPolygon` for an arbitrary simple polygon (needs Mathlib planar
geometry).  The combinatorial layer is complete, so we can exhibit concrete
inductive witnesses on small vertex sets, validating the inductive constructors
and giving downstream callers ready instances to test against. -/

/-- The fundamental triangle as a `TriangulatedPolygon`: vertices `0, 1, 2`
form a single triangle, the smallest non-degenerate art-gallery instance. -/
def TriangulatedPolygon.unitTriangle : TriangulatedPolygon 3
    ({⟨0, 1, 2, by decide, by decide, by decide⟩} : Finset (AbsTriangle 3)) :=
  .single ⟨0, 1, 2, by decide, by decide, by decide⟩

/-- The unit square split along the `0 → 2` diagonal into two triangles
`(0, 1, 2)` and `(0, 2, 3)`, glued along their shared edge `{0, 2}`. -/
def TriangulatedPolygon.unitQuadrilateral :
    let T1 : AbsTriangle 4 := ⟨0, 1, 2, by decide, by decide, by decide⟩
    let T2 : AbsTriangle 4 := ⟨0, 2, 3, by decide, by decide, by decide⟩
    TriangulatedPolygon 4 (insert T2 ({T1} : Finset (AbsTriangle 4))) := by
  let T1 : AbsTriangle 4 := ⟨0, 1, 2, by decide, by decide, by decide⟩
  let T2 : AbsTriangle 4 := ⟨0, 2, 3, by decide, by decide, by decide⟩
  refine TriangulatedPolygon.glue (h := .single T1) (T := T2) (newVertex := 3)
    ?_ ?_ ?_
  · -- 3 ∈ {T2.a, T2.b, T2.c} = {0, 2, 3}
    decide
  · -- shared edge {0, 2} between T1 and T2, with 3 ∉ {0, 2}
    refine ⟨T1, Finset.mem_singleton.mpr rfl, Sym2.mk 0 2, ?_, ?_, ?_⟩
    · -- s(0,2) ∈ T2.edges = {s(0,2), s(2,3), s(0,3)}
      simp [T2, AbsTriangle.edges]
    · -- s(0,2) ∈ T1.edges = {s(0,1), s(1,2), s(0,2)}
      simp [T1, AbsTriangle.edges]
    · -- 3 ∉ s(0,2)
      decide
  · -- 3 ∉ {T1.a, T1.b, T1.c} = {0, 1, 2}
    intro T' hT'
    rw [Finset.mem_singleton] at hT'
    subst hT'
    decide

/-- The unit pentagon (vertices `0..4`) triangulated as a fan from vertex `0`:
triangles `(0,1,2)`, `(0,2,3)`, `(0,3,4)`, each glued to its predecessor along
a shared edge `{0,2}` then `{0,3}`. -/
def TriangulatedPolygon.unitPentagonFan :
    let T1 : AbsTriangle 5 := ⟨0, 1, 2, by decide, by decide, by decide⟩
    let T2 : AbsTriangle 5 := ⟨0, 2, 3, by decide, by decide, by decide⟩
    let T3 : AbsTriangle 5 := ⟨0, 3, 4, by decide, by decide, by decide⟩
    TriangulatedPolygon 5 (insert T3 (insert T2 ({T1} : Finset (AbsTriangle 5)))) := by
  let T1 : AbsTriangle 5 := ⟨0, 1, 2, by decide, by decide, by decide⟩
  let T2 : AbsTriangle 5 := ⟨0, 2, 3, by decide, by decide, by decide⟩
  let T3 : AbsTriangle 5 := ⟨0, 3, 4, by decide, by decide, by decide⟩
  -- Start from the quadrilateral (T1, T2) and glue T3 along {0, 3}.
  have h12 : TriangulatedPolygon 5 (insert T2 ({T1} : Finset (AbsTriangle 5))) := by
    refine TriangulatedPolygon.glue (h := .single T1) (T := T2) (newVertex := 3)
      ?_ ?_ ?_
    · decide
    · refine ⟨T1, Finset.mem_singleton.mpr rfl, Sym2.mk 0 2, ?_, ?_, ?_⟩
      · simp [T2, AbsTriangle.edges]
      · simp [T1, AbsTriangle.edges]
      · decide
    · intro T' hT'
      rw [Finset.mem_singleton] at hT'
      subst hT'
      decide
  refine TriangulatedPolygon.glue (h := h12) (T := T3) (newVertex := 4)
    ?_ ?_ ?_
  · decide
  · -- shared edge {0,3} between T2 and T3, with 4 ∉ {0, 3}
    refine ⟨T2, ?_, Sym2.mk 0 3, ?_, ?_, ?_⟩
    · -- T2 ∈ {T1, T2}
      simp
    · -- s(0,3) ∈ T3.edges = {s(0,3), s(3,4), s(0,4)}
      simp [T3, AbsTriangle.edges]
    · -- s(0,3) ∈ T2.edges = {s(0,2), s(2,3), s(0,3)}
      simp [T2, AbsTriangle.edges]
    · decide
  · -- 4 ∉ {T1.a..c} ∪ {T2.a..c} = {0, 1, 2, 3}
    intro T' hT'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT'
    rcases hT' with rfl | rfl <;> decide

end ProofsInTheBook.Chapter36
