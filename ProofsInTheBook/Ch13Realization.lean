import ProofsInTheBook.Ch13CauchyAssembly
import ProofsInTheBook.Ch13ArmVertexFull
import ProofsInTheBook.Ch13VertexStar
import ProofsInTheBook.Ch13Dihedral
import ProofsInTheBook.PlanarMapSimple

/-!
# `Ch13Realization` — the `ConvexPolytopeRealization` interface and the geometric rigidity theorem.

This file builds the **faithful interface** between an extrinsic pair of convex-polytope vertex stars
(`Ch13VertexStar.VertexStar` + its `dihedral`, Bridge A/B) and the abstract Cauchy assembly
(`Ch13CauchyAssembly.CauchyMarkedTriangulatedSphere`), and **derives** from it the headline

  `realization_rigid : ∀ Q i, (starP Q).dihedral i = (starQ Q).dihedral i`

— all corresponding dihedral angles of the two congruent-faced realizations agree (Cauchy's
sign-machinery content).  It is **not** a full ℝ³ polytope model (that is out of scope); it is the
faithful order-bridge layer.

## §3.3 discipline

* The crux bridge `vertexArm_signChanges_eq` (`signChangesFull = vertexFlipCountSkipZeros`) is a
  **DERIVED THEOREM**, not a posited structure field.  It is derived from
  * the explicit order-bridge field `linkOrder` (the σ-cyclic dart order around a vertex carries the
    geometric link rotational order: the σ-ordered edge-sign list equals the link-ordered real-sign
    list), and
  * the **count-reconciliation** identity
    `cyclicFlips (nzSigns d) = cyclicFlipCountSkipZeros ((List.ofFn d).map realSignToEdgeSign)`,
    proved here locally (the two-valued `Bool ↔ StrictEdgeSign` identification + the common
    zero-skipping), and
  * **σ-orbit rotation invariance** of `vertexFlipCountSkipZeros` (so the bridge holds at *every*
    active dart of a vertex, not just its `linkOrder` representative), proved here from
    `cyclicFlipCount`'s cyclic-rotation invariance and `Equiv.Perm.SameCycle.toList_isRotated`.
* There is **no `active` field**: given a `ConvexPolytopeRealization`, rigidity holds with no extra
  side-hypothesis for all congruent-faced realizations.  NOTE (honesty): `realization_rigid` is
  *conditional on* a `ConvexPolytopeRealization R`.  The abstract structure is inhabited (e.g. the
  degenerate `P = Q`), so the theorem is not provably vacuous; but constructing one from a genuine
  ℝ³ convex polytope is the realization infrastructure declared out of scope (see the chapter
  header).  So this is "Cauchy rigidity GIVEN the realization datum", not an unconditional theorem.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped Classical
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13 EdgeSign
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13ArmVertex
open ProofsInTheBook.Ch13ArmVertexFull
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13Realization

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace List

/-- Cyclic list agreement up to orientation reversal. -/
def DihedralRotated {α : Type*} (l m : List α) : Prop :=
  l ~r m ∨ l.reverse ~r m

end List

/-! ## Part 0 — the count-reconciliation identity (local, self-contained)

The `signChangesFull` count is `cyclicFlips (nzSigns ·)` over real link-angle differences (a `List Bool`
machinery), while `vertexFlipCountSkipZeros` is `cyclicFlipCountSkipZeros ((·).map ·)` over an
`EdgeSign` sign list.  Both drop the zeros and count cyclic two-valued flips.  We prove the bridge
identity locally so this file builds standalone (the in-flight `Ch13CountReconcile` carries the same
identity; this avoids a hard import dependency). -/

/-- The two-valued bijection `true ↦ plus`, `false ↦ minus`. -/
def boolToStrict : Bool → StrictEdgeSign
  | true => StrictEdgeSign.plus
  | false => StrictEdgeSign.minus

theorem boolToStrict_inj : Function.Injective boolToStrict := by
  intro a b h; cases a <;> cases b <;> simp_all [boolToStrict]

/-- The real-sign map into `EdgeSign`, matching `nzSigns`' `0 < d ↦ plus`, `d < 0 ↦ minus`,
`d = 0 ↦ zero` convention. -/
def realSignToEdgeSign (x : ℝ) : EdgeSign :=
  if 0 < x then EdgeSign.plus else if x < 0 then EdgeSign.minus else EdgeSign.zero

theorem realSignToEdgeSign_eq_zero_iff (x : ℝ) : realSignToEdgeSign x = EdgeSign.zero ↔ x = 0 := by
  unfold realSignToEdgeSign
  rcases lt_trichotomy x 0 with h | h | h
  · simp only [not_lt.mpr h.le, if_false, h, if_true]
    constructor <;> intro h' <;> first | exact absurd h' (by decide) | (rw [h'] at h; exact absurd h (lt_irrefl 0))
  · simp [h]
  · simp only [h, if_true]
    constructor <;> intro h' <;> first | exact absurd h' (by decide) | (rw [h'] at h; exact absurd h (lt_irrefl 0))

theorem toStrict_realSign_of_ne (x : ℝ) (hx : x ≠ 0) :
    (realSignToEdgeSign x).toStrict = some (boolToStrict (decide (0 < x))) := by
  unfold realSignToEdgeSign
  rcases lt_trichotomy x 0 with h | h | h
  · have hnp : ¬ (0 < x) := not_lt.mpr h.le
    simp only [hnp, if_false, h, if_true]
    simp [EdgeSign.toStrict, boolToStrict]
  · exact absurd h hx
  · simp only [h, if_true]
    simp [EdgeSign.toStrict, boolToStrict]

theorem toStrict_realSign_of_zero {x : ℝ} (hx : x = 0) :
    (realSignToEdgeSign x).toStrict = none := by
  subst hx; simp [realSignToEdgeSign, EdgeSign.toStrict]

/-- `flips` of a Bool list with its cyclic closer `[first]` appended equals `flipAux` of the mapped
list (single structural induction). -/
theorem flips_append_eq_flipAux (first : Bool) :
    ∀ (prev : Bool) (t : List Bool),
      flips ((prev :: t) ++ [first])
        = flipAux (boolToStrict first) (boolToStrict prev) (t.map boolToStrict)
  | prev, [] => by
      simp only [List.nil_append, List.cons_append, List.map_nil, flips, flipAux]
      by_cases h : prev = first
      · simp [h]
      · simp only [ne_eq, h, not_false_eq_true, if_pos]
        rw [if_pos]
        intro hc; exact h (boolToStrict_inj hc)
  | prev, x :: t => by
      have ih := flips_append_eq_flipAux first x t
      simp only [List.cons_append, List.map_cons, flips, flipAux] at *
      rw [ih]
      by_cases h : prev = x
      · simp [h]
      · rw [if_pos h, if_pos]
        intro hc; exact h (boolToStrict_inj hc)

/-- The Bool-based cyclic flip count equals the `StrictEdgeSign`-based one under `boolToStrict`. -/
theorem cyclicFlips_eq_cyclicFlipCount_map (bs : List Bool) :
    cyclicFlips bs = cyclicFlipCount (bs.map boolToStrict) := by
  cases bs with
  | nil => simp [cyclicFlips, cyclicFlipCount]
  | cons h t =>
      show flips ((h :: t) ++ [h]) = cyclicFlipCount ((h :: t).map boolToStrict)
      rw [flips_append_eq_flipAux h h t]
      simp only [List.map_cons, cyclicFlipCount]

theorem filter_map_eq_filterMap {β γ : Type*} (p : β → Bool) (g : β → γ) :
    ∀ (L : List β),
      (L.filter p).map g = L.filterMap (fun a => if p a then some (g a) else none)
  | [] => by simp
  | a :: L => by
      simp only [List.filter_cons, List.filterMap_cons]
      by_cases h : p a
      · simp [h, filter_map_eq_filterMap p g L]
      · simp [h, filter_map_eq_filterMap p g L]

/-- Both machineries skip zeros identically: `(nzSigns d).map boolToStrict` is the strict
sub-sequence of `(List.ofFn d).map realSignToEdgeSign`. -/
theorem nzSigns_map_boolToStrict {m : ℕ} (d : Fin m → ℝ) :
    (nzSigns d).map boolToStrict
      = ((List.ofFn d).map realSignToEdgeSign).filterMap EdgeSign.toStrict := by
  rw [List.ofFn_eq_map, List.map_map, List.filterMap_map]
  unfold nzSigns
  rw [List.map_map, filter_map_eq_filterMap]
  apply List.filterMap_congr
  intro i _
  simp only [Function.comp_apply]
  by_cases hi : d i = 0
  · rw [if_neg (by simp [hi]), toStrict_realSign_of_zero hi]
  · rw [if_pos (by simp [hi]), toStrict_realSign_of_ne (d i) hi]

/-- **The count-reconciliation identity (local copy).** -/
theorem cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros {m : ℕ} (d : Fin m → ℝ) :
    cyclicFlips (nzSigns d)
      = cyclicFlipCountSkipZeros ((List.ofFn d).map realSignToEdgeSign) := by
  rw [cyclicFlips_eq_cyclicFlipCount_map, cyclicFlipCountSkipZeros_eq_strict,
    nzSigns_map_boolToStrict]

/-! ## Part 1 — `cyclicFlipCountSkipZeros` is invariant under list rotation

`cyclicFlipCount` counts cyclic adjacent-unequal pairs, so it is unchanged by rotation;
`cyclicFlipCountSkipZeros` inherits this through `filterMap`, which commutes with `rotate`.  This lets
the σ-cyclic bridge hold at *every* dart of a vertex orbit (`toList` of two darts in one orbit are
rotations of each other), not just the chosen representative.

The clean rotation-invariant model is the **cyclic-adjacency sum**
`cyclicSum l := (zipWith [·≠·] l (l.rotate 1)).sum` — the number of indices `i (mod len)` with
`l[i] ≠ l[(i+1) mod len]`.  We prove `cyclicFlipCount = cyclicSum` and that `cyclicSum` is
rotation-invariant. -/

/-- The cyclic adjacency indicator sum: `1` for each cyclically adjacent unequal pair. -/
def cyclicSum {α : Type*} [DecidableEq α] (l : List α) : ℕ :=
  (List.zipWith (fun a b => if a ≠ b then 1 else 0) l (l.rotate 1)).sum

/-- `cyclicFlipCount` equals the cyclic adjacency sum (`flipAux` telescopes into the zipWith sum). -/
theorem cyclicFlipCount_eq_cyclicSum {α : Type*} [DecidableEq α] (l : List α) :
    cyclicFlipCount l = cyclicSum l := by
  cases l with
  | nil => simp [cyclicFlipCount, cyclicSum]
  | cons h t =>
    simp only [cyclicSum, List.rotate_cons_succ, List.rotate_zero, cyclicFlipCount]
    -- General: flipAux h p xs = sum (zipWith f (p::xs) (xs ++ [h]))
    have key : ∀ (p : α) (xs : List α),
        flipAux h p xs
          = (List.zipWith (fun a b => if a ≠ b then 1 else 0) (p :: xs) (xs ++ [h])).sum := by
      intro p xs
      induction xs generalizing p with
      | nil => simp [flipAux]
      | cons a xs ih =>
        simp only [flipAux, List.cons_append, List.zipWith_cons_cons, List.sum_cons]
        rw [ih a]
    rw [key h t]

/-- `List.sum` is invariant under rotation (rotation is a permutation). -/
theorem sum_rotate {α : Type*} [AddCommMonoid α] (l : List α) (n : ℕ) :
    (l.rotate n).sum = l.sum :=
  (List.rotate_perm l n).sum_eq

/-- The cyclic adjacency sum is invariant under one rotation. -/
theorem cyclicSum_rotate_one {α : Type*} [DecidableEq α] (l : List α) :
    cyclicSum (l.rotate 1) = cyclicSum l := by
  unfold cyclicSum
  rw [← List.zipWith_rotate_distrib (fun a b => if a ≠ b then 1 else 0) l (l.rotate 1) 1
      (List.length_rotate l 1).symm, sum_rotate]

/-- `cyclicFlipCount` is invariant under one rotation. -/
theorem cyclicFlipCount_rotate_one {α : Type*} [DecidableEq α] (l : List α) :
    cyclicFlipCount (l.rotate 1) = cyclicFlipCount l := by
  rw [cyclicFlipCount_eq_cyclicSum, cyclicFlipCount_eq_cyclicSum, cyclicSum_rotate_one]

/-- `cyclicFlipCount` is invariant under any rotation. -/
theorem cyclicFlipCount_rotate {α : Type*} [DecidableEq α] (l : List α) (k : ℕ) :
    cyclicFlipCount (l.rotate k) = cyclicFlipCount l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show l.rotate (k + 1) = (l.rotate k).rotate 1 by rw [List.rotate_rotate]]
    rw [cyclicFlipCount_rotate_one, ih]

/-- `cyclicFlipCount` is invariant under `IsRotated`. -/
theorem cyclicFlipCount_of_isRotated {α : Type*} [DecidableEq α] {l l' : List α}
    (h : l ~r l') : cyclicFlipCount l = cyclicFlipCount l' := by
  obtain ⟨k, rfl⟩ := h
  exact (cyclicFlipCount_rotate l k).symm

/-- `filterMap` of a singly-rotated list is a rotation of `filterMap` of the list. -/
theorem filterMap_rotate_one_isRotated {α β : Type*} (f : α → Option β) (l : List α) :
    (l.rotate 1).filterMap f ~r l.filterMap f := by
  cases l with
  | nil => simp
  | cons h t =>
    rw [List.rotate_cons_succ, List.rotate_zero, List.filterMap_append, List.filterMap_cons]
    -- (t.filterMap f) ++ (f h).toList? vs (f h).toList? ++ t.filterMap f  — a rotation
    rw [List.filterMap_cons]
    -- goal: (t.filterMap f ++ Option.toList' (f h)) ~r (match f h with ... )
    cases hf : f h with
    | none => simp [List.IsRotated.refl]
    | some b =>
      simp only [List.filterMap_nil]
      have := List.isRotated_append (l := t.filterMap f) (l' := [b])
      simpa using this

/-- `filterMap` is invariant-up-to-rotation under rotation of its source. -/
theorem filterMap_rotate_isRotated {α β : Type*} (f : α → Option β) (l : List α) (k : ℕ) :
    (l.rotate k).filterMap f ~r l.filterMap f := by
  induction k with
  | zero => simp [List.IsRotated.refl]
  | succ k ih =>
    rw [show l.rotate (k + 1) = (l.rotate k).rotate 1 by rw [List.rotate_rotate]]
    exact (filterMap_rotate_one_isRotated f (l.rotate k)).trans ih

/-- `filterMap` carries `IsRotated` to `IsRotated`. -/
theorem filterMap_isRotated {α β : Type*} {l l' : List α} (f : α → Option β) (h : l ~r l') :
    l.filterMap f ~r l'.filterMap f := by
  obtain ⟨k, rfl⟩ := h
  exact (filterMap_rotate_isRotated f l k).symm

/-- **`cyclicFlipCountSkipZeros` is invariant under `IsRotated`.**  Rotating the cyclic sign list
leaves the skip-zeros cyclic flip count unchanged. -/
theorem cyclicFlipCountSkipZeros_of_isRotated {l l' : List EdgeSign} (h : l ~r l') :
    cyclicFlipCountSkipZeros l = cyclicFlipCountSkipZeros l' := by
  unfold cyclicFlipCountSkipZeros
  exact cyclicFlipCount_of_isRotated (filterMap_isRotated EdgeSign.toStrict h)

theorem filterMap_reverse {α β : Type*} (f : α → Option β) :
    ∀ l : List α, l.reverse.filterMap f = (l.filterMap f).reverse
  | [] => by simp
  | a :: t => by
      simp only [List.reverse_cons, List.filterMap_append, filterMap_reverse f t,
        List.filterMap_cons, List.filterMap_nil]
      cases f a <;> simp

private theorem zipWith_append_eq {α β γ : Type*} (f : α → β → γ) :
    ∀ {l₁ : List α} {l₂ : List β} (r₁ : List α) (r₂ : List β),
      l₁.length = l₂.length →
        List.zipWith f (l₁ ++ r₁) (l₂ ++ r₂) =
          List.zipWith f l₁ l₂ ++ List.zipWith f r₁ r₂
  | [], [], r₁, r₂, _ => by rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, r₁, r₂, h => by
      have ht : as.length = bs.length := Nat.succ.inj h
      simp only [List.cons_append, List.zipWith_cons_cons, List.cons.injEq, true_and]
      exact zipWith_append_eq f r₁ r₂ ht

private theorem zipWith_reverse_eq {α β γ : Type*} (f : α → β → γ) :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (List.zipWith f l₁ l₂).reverse = List.zipWith f l₁.reverse l₂.reverse
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
      have ht : as.length = bs.length := Nat.succ.inj h
      simp only [List.zipWith_cons_cons, List.reverse_cons]
      rw [zipWith_reverse_eq f ht]
      rw [zipWith_append_eq f [a] [b] (by simpa [List.length_reverse] using ht)]
      simp

private theorem zipWith_comm_of_comm_eq {α γ : Type*} (f : α → α → γ)
    (hf : ∀ a b, f a b = f b a) :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length →
      List.zipWith f l₁ l₂ = List.zipWith f l₂ l₁
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
      have ht : as.length = bs.length := Nat.succ.inj h
      simp [hf a b, zipWith_comm_of_comm_eq f hf ht]

theorem cyclicFlipCount_reverse {α : Type*} [DecidableEq α] (l : List α) :
    cyclicFlipCount l.reverse = cyclicFlipCount l := by
  rw [cyclicFlipCount_eq_cyclicSum, cyclicFlipCount_eq_cyclicSum]
  unfold cyclicSum
  let f : α → α → ℕ := fun a b => if a ≠ b then 1 else 0
  have hfcomm : ∀ a b, f a b = f b a := by
    intro a b
    by_cases h : a = b
    · simp [f, h]
    · have hba : b ≠ a := fun hb => h hb.symm
      simp [f, h, hba]
  let k := l.length - 1 % l.length
  rw [List.rotate_reverse]
  change (List.zipWith f l.reverse ((l.rotate k).reverse)).sum =
    (List.zipWith f l (l.rotate 1)).sum
  rw [← zipWith_reverse_eq f (by rw [List.length_rotate]), List.sum_reverse,
    zipWith_comm_of_comm_eq f hfcomm (by rw [List.length_rotate])]
  have hlen : (l.rotate k).length = l.length := List.length_rotate l k
  have hzip := List.zipWith_rotate_distrib f l (l.rotate 1) k
    (by rw [List.length_rotate])
  have hrot : (l.rotate 1).rotate k = l := by
    by_cases hnil : l = []
    · subst hnil
      simp [k]
    · have hlenpos : 0 < l.length := Nat.pos_of_ne_zero (by
        intro hlen0
        exact hnil (List.eq_nil_of_length_eq_zero hlen0))
      rw [List.rotate_rotate]
      unfold k
      by_cases hlen1 : l.length = 1
      · have hmod : 1 % l.length = 0 := by simp [hlen1]
        rw [hmod]
        have hsum : 1 + (l.length - 0) = l.length * 2 := by omega
        rw [hsum, List.rotate_length_mul]
      · have hlt : 1 < l.length := by omega
        have hmod : 1 % l.length = 1 := Nat.mod_eq_of_lt hlt
        rw [hmod]
        have hsum : 1 + (l.length - 1) = l.length := by omega
        rw [hsum, List.rotate_length]
  calc
    (List.zipWith f (l.rotate k) l).sum
        = (List.zipWith f (l.rotate k) ((l.rotate 1).rotate k)).sum := by rw [hrot]
    _ = ((List.zipWith f l (l.rotate 1)).rotate k).sum := by rw [hzip]
    _ = (List.zipWith f l (l.rotate 1)).sum := sum_rotate _ _

theorem cyclicFlipCountSkipZeros_reverse (l : List EdgeSign) :
    cyclicFlipCountSkipZeros l.reverse = cyclicFlipCountSkipZeros l := by
  unfold cyclicFlipCountSkipZeros
  rw [filterMap_reverse]
  exact cyclicFlipCount_reverse _

theorem cyclicFlipCountSkipZeros_of_dihedralRotated {l m : List EdgeSign}
    (h : List.DihedralRotated l m) :
    cyclicFlipCountSkipZeros l = cyclicFlipCountSkipZeros m := by
  rcases h with hrot | hrev
  · exact cyclicFlipCountSkipZeros_of_isRotated hrot
  · calc
      cyclicFlipCountSkipZeros l
          = cyclicFlipCountSkipZeros l.reverse := (cyclicFlipCountSkipZeros_reverse l).symm
      _ = cyclicFlipCountSkipZeros m := cyclicFlipCountSkipZeros_of_isRotated hrev

theorem perm_of_dihedralRotated {α : Type*} {l m : List α}
    (h : List.DihedralRotated l m) : l.Perm m := by
  rcases h with hrot | hrev
  · exact hrot.perm
  · exact (List.reverse_perm l).symm.trans hrev.perm

/-- **σ-orbit invariance of the per-vertex flip count.**  Two darts in the same `σ`-orbit have the
same `vertexFlipCountSkipZeros`, because their `σ`-`toList`s are rotations of each other. -/
theorem vertexFlipCountSkipZeros_sameCycle (M : CombMap D) (es : D → EdgeSign) {d d' : D}
    (h : M.σ.SameCycle d d') :
    vertexFlipCountSkipZeros M es d = vertexFlipCountSkipZeros M es d' := by
  unfold vertexFlipCountSkipZeros vertexSignList
  exact cyclicFlipCountSkipZeros_of_isRotated
    ((h.toList_isRotated).map es)

/-! ## Part 2 — the `ConvexPolytopeRealization` interface

A faithful order-bridge layer between two extrinsic congruent-faced vertex-star realizations and the
abstract `CauchyMarkedTriangulatedSphere`.  This is **not** a full ℝ³ polytope model.

The two realizations `P` and `Q` share the same combinatorial map `M` (a triangulated sphere).  At each
vertex `Q : Vertex M`, `starP Q` and `starQ Q` are the local convex-vertex stars of `P` and `Q`; their
links are strictly convex spherical arms with **equal corresponding side lengths** (congruent faces) and
**equal closing chord** (same incident-edge count and shared edge lengths).

The **load-bearing non-vacuity field is `linkOrder`**: it records that the geometric rotational order of
the link at each vertex equals the combinatorial `σ`-dart order — concretely, the `σ`-ordered edge-sign
list around the vertex (read from a representative dart `dartRep Q`) equals the link-ordered real-sign
list of the dihedral differences.  This is the field that makes the crux bridge a *derived theorem*, not
a posited one; positing the bridge directly (without `linkOrder`) is the §3.3 vacuity trap. -/

/-- The `Q`-realization link at vertex `Q`, reindexed onto `Fin ((starP Q).n + 1)` via the
degree-match `deg_eq`.  (Both links have the same number of edges, `vertexDeg`.) -/
@[reducible] def linkQcast (M : CombMap D) (starP starQ : M.Vertex → VertexStar)
    (hnn : ∀ Q, (starQ Q).n = (starP Q).n) (Q : M.Vertex) :
    Fin ((starP Q).n + 1) → S2 :=
  fun i => (starQ Q).vertexLink (Fin.cast (by rw [hnn Q]) i)

/-- **The faithful convex-polytope realization interface.**

Two congruent-faced convex-vertex realizations `P, Q` of the same triangulated-sphere combinatorial map
`M`, presented as a per-vertex family of vertex stars whose links agree on side lengths (congruent
faces) and closing chord, together with the **order bridge** `linkOrder` (the σ-dart order carries the
geometric link order) and the per-vertex two-arc datum `twoArc` (the single isolated geometric residual,
exactly as in `Ch13ArmVertexFull`).

There is **no `active` field**: rigidity is unconditional. -/
structure ConvexPolytopeRealization (M : CombMap D) where
  /-- `M` is a triangulated sphere. -/
  isSphere : M.IsSphereMap
  triangle : M.FaceRegular 3
  /-- The edge graph is simple (no loops / no parallel edges) — a genuine property of every convex
  3-polytope's boundary graph (Steinitz), supplied by the ℝ³ realization.  It is what rules out the
  digon degeneracy in the combinatorial low-active-vertex lemma. -/
  isSimple : M.IsSimpleGraph
  /-- The `P`-realization vertex star at each vertex. -/
  starP : M.Vertex → VertexStar
  /-- The `Q`-realization vertex star at each vertex. -/
  starQ : M.Vertex → VertexStar
  /-- Both realizations have the same incident-edge count at each vertex (degree match). -/
  hnn : ∀ (Q : M.Vertex), (starQ Q).n = (starP Q).n
  /-- The per-edge dihedral-difference signing: `edgeSign d = sign(dihedral_Q − dihedral_P)` at the
  edge of `d`.  Edge-invariant (`α`-stable): both darts of an edge carry the same sign. -/
  edgeSign : D → EdgeSign
  edgeSign_inv : ∀ d, edgeSign (M.α d) = edgeSign d
  /-- Congruent faces: corresponding link side lengths agree. -/
  sides_eq : ∀ (Q : M.Vertex) (i : Fin (starP Q).n),
      sideLen (starP Q).vertexLink i = sideLen (linkQcast M starP starQ hnn Q) i
  /-- Shared closing chord at each vertex. -/
  close_eq : ∀ (Q : M.Vertex),
      sDist ((starP Q).vertexLink 0) ((starP Q).vertexLink (Fin.last (starP Q).n))
        = sDist ((linkQcast M starP starQ hnn Q) 0)
            ((linkQcast M starP starQ hnn Q) (Fin.last (starP Q).n))
  /-- A representative dart at each vertex (`tail = Q`). -/
  dartRep : M.Vertex → D
  dartRep_tail : ∀ (Q : M.Vertex), M.tail (dartRep Q) = Q
  /-- **Interior activeness bridge.**  When some incident edge at `Q` carries a nonzero dihedral-change
  sign, some *interior* joint of the link genuinely differs.  This is the geometric input feeding the
  arm lemma's strict witness (closing angles are determined by the equal sides/chord; only the interior
  joints are the free Cauchy variables).  It is an interface field exactly like `twoArc`; it does **not**
  make rigidity conditional (the conclusion of `realization_rigid` is unconditional). -/
  interiorActive : ∀ (Q : M.Vertex),
      ActiveVertex M edgeSign (dartRep Q) →
        ∃ i : Fin ((starP Q).n - 1),
          jointAngle (starP Q).vertexLink i ≠ jointAngle (linkQcast M starP starQ hnn Q) i
  /-- The per-vertex two-arc split datum for the `signChangesFull = 2` case (the single isolated
  geometric residual, exactly as `Ch13ArmVertexFull.cauchyArmVertexFull_of_links` takes). -/
  twoArc : ∀ (Q : M.Vertex),
      signChangesFull (starP Q).vertexLink (linkQcast M starP starQ hnn Q) = 2 →
        TwoArcSplitData (starP Q).vertexLink (linkQcast M starP starQ hnn Q)
  /-- **The order bridge (`linkOrder`).**  The `σ`-ordered list of edge signs around vertex `Q` (read
  from `dartRep Q`) agrees with the link-ordered real-sign list of the dihedral differences up to
  cyclic rotation and reversal.  This is the honest unoriented cyclic-order bridge; positing
  `vertexArm_signChanges_eq` directly instead is the §3.3 trap. -/
  linkOrder : ∀ (Q : M.Vertex),
      List.DihedralRotated
        ((M.σ.toList (dartRep Q)).map edgeSign)
        ((List.ofFn
          (linkDiff (starP Q).vertexLink (linkQcast M starP starQ hnn Q))).map realSignToEdgeSign)

/-! ## Part 3 — the cast transport lemmas

`linkQcast` reindexes the `Q`-link `(starQ Q).vertexLink : Fin ((starQ Q).n + 1) → S2` onto
`Fin ((starP Q).n + 1) → S2` through the degree match `(starQ Q).n = (starP Q).n`.  These two lemmas
transport `StrictConvexSphArm` and `jointAngle` across that (propositionally trivial) reindexing, so
no geometric content is lost. -/

/-- Reindexing a strict convex arm by a propositionally-trivial `Fin.cast` preserves it. -/
theorem strictArm_reindex {n m : ℕ} (h : n = m) (A : Fin (m + 1) → S2)
    (hA : StrictConvexSphArm A) :
    StrictConvexSphArm (fun i : Fin (n + 1) => A (Fin.cast (by rw [h]) i)) := by
  subst h
  simpa using hA

/-- `jointAngle` is invariant under the trivial `Fin.cast` reindexing. -/
theorem jointAngle_reindex {n m : ℕ} (h : n = m) (A : Fin (m + 1) → S2)
    (i : Fin (n - 1)) :
    jointAngle (fun j : Fin (n + 1) => A (Fin.cast (by rw [h]) j)) i
      = jointAngle A (Fin.cast (by rw [h]) i) := by
  subst h
  simp

/-- The `Q`-link reindex is a strict convex arm (from the genuine `(starQ Q).vertexLink_strictArm`). -/
theorem linkQcast_strictArm (M : CombMap D) (starP starQ : M.Vertex → VertexStar)
    (hnn : ∀ Q, (starQ Q).n = (starP Q).n) (Q : M.Vertex) :
    StrictConvexSphArm (linkQcast M starP starQ hnn Q) :=
  strictArm_reindex (hnn Q).symm (starQ Q).vertexLink (starQ Q).vertexLink_strictArm

namespace ConvexPolytopeRealization

variable {M : CombMap D} (R : ConvexPolytopeRealization M)

/-- Shorthand: the `P`-link at `Q`. -/
@[reducible] def linkP (Q : M.Vertex) : Fin ((R.starP Q).n + 1) → S2 := (R.starP Q).vertexLink
/-- Shorthand: the `Q`-link (reindexed) at `Q`. -/
@[reducible] def linkQ (Q : M.Vertex) : Fin ((R.starP Q).n + 1) → S2 :=
  linkQcast M R.starP R.starQ R.hnn Q

/-- The `Q`-link reindex is a strict convex arm. -/
theorem linkQ_strictArm (Q : M.Vertex) : StrictConvexSphArm (R.linkQ Q) :=
  linkQcast_strictArm M R.starP R.starQ R.hnn Q

/-! ### Orbit bookkeeping: relating an arbitrary active dart to the vertex representative. -/

/-- A dart `d` is in the `σ`-orbit of its vertex's representative `dartRep (tail d)`. -/
theorem sameCycle_dartRep (d : D) : M.σ.SameCycle (R.dartRep (M.tail d)) d := by
  have h : Quotient.mk (cycleSetoid M.σ) (R.dartRep (M.tail d)) = Quotient.mk (cycleSetoid M.σ) d := by
    rw [show Quotient.mk (cycleSetoid M.σ) (R.dartRep (M.tail d)) = M.tail (R.dartRep (M.tail d)) from rfl,
        R.dartRep_tail]
    rfl
  exact Quotient.exact h

/-- `ActiveVertex` is constant on a `σ`-orbit. -/
theorem activeVertex_congr {d d' : D} (h : M.σ.SameCycle d d') :
    ActiveVertex M R.edgeSign d ↔ ActiveVertex M R.edgeSign d' := by
  constructor
  · rintro ⟨x, hx, hxne⟩; exact ⟨x, h.symm.trans hx, hxne⟩
  · rintro ⟨x, hx, hxne⟩; exact ⟨x, h.trans hx, hxne⟩

/-! ### The crux: `signChangesFull = vertexFlipCountSkipZeros`, DERIVED via `linkOrder`. -/

/-- **The crux bridge (DERIVED, not posited).**  At the representative dart of vertex `Q`, the closed-link
cyclic flip count equals the `σ`-cyclic skip-zeros count of the edge signs.  Chain:
`signChangesFull = cyclicFlips (nzSigns linkDiff)` (def) `= cyclicFlipCountSkipZeros (real signs)`
(reconciliation) `= cyclicFlipCountSkipZeros (σ-edge-sign list)` (`linkOrder`) `= vertexFlipCountSkipZeros`
(def). -/
theorem signChangesFull_eq_vertexFlip_rep (Q : M.Vertex) :
    signChangesFull (R.starP Q).vertexLink (R.linkQ Q)
      = vertexFlipCountSkipZeros M R.edgeSign (R.dartRep Q) := by
  unfold signChangesFull
  rw [cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros]
  exact (cyclicFlipCountSkipZeros_of_dihedralRotated (R.linkOrder Q)).symm

/-- **The crux bridge at an arbitrary active dart.**  By `σ`-orbit invariance of
`vertexFlipCountSkipZeros`, the bridge at the representative transfers to every dart of the vertex. -/
theorem signChangesFull_eq_vertexFlip (d : D) :
    signChangesFull (R.starP (M.tail d)).vertexLink (R.linkQ (M.tail d))
      = vertexFlipCountSkipZeros M R.edgeSign d := by
  rw [R.signChangesFull_eq_vertexFlip_rep (M.tail d)]
  exact vertexFlipCountSkipZeros_sameCycle M R.edgeSign (R.sameCycle_dartRep d)

/-! ### The genuine per-active-vertex arm datum, and the crux as a `CauchyArmVertex` field. -/

/-- **The genuine vertex-arm datum at an active dart** (Bridge: `vertexArm`).  Built from the two real
spherical links via `cauchyArmVertexFull_of_links`: equal sides (`sides_eq`), equal closing chord
(`close_eq`), the interior strict witness (`interiorActive`), and the two-arc residual (`twoArc`).  Its
`signChanges` is the genuine FULL closed-link cyclic count `signChangesFull`. -/
noncomputable def vertexArm (d : D) (hd : ActiveVertex M R.edgeSign d) :
    Chapter13.CauchyArmVertex :=
  cauchyArmVertexFull_of_links (R.starP (M.tail d)).n (R.starP (M.tail d)).hn
    (R.starP (M.tail d)).vertexLink (R.linkQ (M.tail d))
    (R.starP (M.tail d)).vertexLink_strictArm (R.linkQ_strictArm (M.tail d))
    (R.sides_eq (M.tail d)) (R.close_eq (M.tail d))
    (R.interiorActive (M.tail d)
      ((R.activeVertex_congr (R.sameCycle_dartRep d)).mpr hd))
    (R.twoArc (M.tail d))

/-- `vertexArm`'s `signChanges` is `signChangesFull` (by construction). -/
theorem vertexArm_signChanges (d : D) (hd : ActiveVertex M R.edgeSign d) :
    (R.vertexArm d hd).signChanges
      = signChangesFull (R.starP (M.tail d)).vertexLink (R.linkQ (M.tail d)) := rfl

/-- **The crux bridge as the assembly field** (DERIVED): the arm-datum's sign-change count equals the
`σ`-cycle skip-zeros flip count at the vertex. -/
theorem vertexArm_signChanges_eq (d : D) (hd : ActiveVertex M R.edgeSign d) :
    (R.vertexArm d hd).signChanges = vertexFlipCountSkipZeros M R.edgeSign d := by
  rw [R.vertexArm_signChanges d hd, R.signChangesFull_eq_vertexFlip d]

/-! ### Assembly: the `CauchyMarkedTriangulatedSphere` instance and the headline. -/

/-- **`realization_marked`** — the faithful `CauchyMarkedTriangulatedSphere` of the realization `R`.
All four bridges are derived theorems: `edgeSign`/`edgeSign_inv` (interface), `vertexArm` (real links),
and the crux `vertexArm_signChanges_eq` (derived via `linkOrder` + reconciliation + orbit invariance). -/
def realization_marked :
    Ch13CauchyAssembly.CauchyMarkedTriangulatedSphere M where
  isSphere := R.isSphere
  triangleFaces := R.triangle
  isSimple := R.isSimple
  edgeSign := R.edgeSign
  edgeSign_inv := R.edgeSign_inv
  vertexArm := R.vertexArm
  vertexArm_signChanges_eq := R.vertexArm_signChanges_eq

/-- **The Cauchy conclusion: every edge sign is zero (given a `ConvexPolytopeRealization`).**
No extra side-hypothesis beyond the realization datum `R`.  No dihedral angle differs
between the two congruent-faced realizations.  This is `cauchy_no_nonzero_edgeSign_final` applied to
`realization_marked`: the combinatorial low-active-vertex lemma is fully discharged (using the genuine
`isSimple` field, Steinitz), so no abstract `hcomb` hypothesis remains.  The geometric `≥4` (real
spherical links) collides with the combinatorial `≤2`. -/
theorem realization_all_edgeSign_zero :
    ∀ d, R.edgeSign d = EdgeSign.zero :=
  Ch13CauchyAssembly.cauchy_no_nonzero_edgeSign_final R.realization_marked

/-! ### From zero edge signs to equal dihedrals. -/

/-- All edge signs zero forces every link-angle difference to vanish: at each vertex the closed-link
real-sign list is the all-`zero` list (by `linkOrder` + `∀ d, edgeSign d = zero`), so each
`realSignToEdgeSign (linkDiff i) = zero`, hence each `linkDiff i = 0`. -/
theorem linkDiff_zero_of_edgeSign_zero (hzero : ∀ d, R.edgeSign d = EdgeSign.zero)
    (Q : M.Vertex) (i : Fin ((R.starP Q).n + 1)) :
    linkDiff (R.starP Q).vertexLink (R.linkQ Q) i = 0 := by
  let geom :=
    (List.ofFn (linkDiff (R.starP Q).vertexLink (R.linkQ Q))).map realSignToEdgeSign
  let comb := (M.σ.toList (R.dartRep Q)).map R.edgeSign
  have hperm : geom.Perm comb := (perm_of_dihedralRotated (R.linkOrder Q)).symm
  have hmem_geom : realSignToEdgeSign (linkDiff (R.starP Q).vertexLink (R.linkQ Q) i) ∈ geom := by
    apply List.mem_map.mpr
    exact ⟨linkDiff (R.starP Q).vertexLink (R.linkQ Q) i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
  have hmem_comb : realSignToEdgeSign (linkDiff (R.starP Q).vertexLink (R.linkQ Q) i) ∈ comb :=
    hperm.mem_iff.mp hmem_geom
  have hz : realSignToEdgeSign (linkDiff (R.starP Q).vertexLink (R.linkQ Q) i) = EdgeSign.zero := by
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hmem_comb
    rw [← ha, hzero a]
  exact (realSignToEdgeSign_eq_zero_iff _).mp hz

/-- Equal corresponding link joint angles at each vertex. -/
theorem jointAngle_eq_of_edgeSign_zero (hzero : ∀ d, R.edgeSign d = EdgeSign.zero)
    (Q : M.Vertex) (i : Fin ((R.starP Q).n - 1)) :
    jointAngle (R.starP Q).vertexLink i = jointAngle (R.linkQ Q) i := by
  have hk := R.linkDiff_zero_of_edgeSign_zero hzero Q ⟨i.val + 1, by have := i.isLt; omega⟩
  rw [linkDiff_interior] at hk
  unfold jointDiff at hk
  linarith

/-- **`realization_rigid` — the headline (given a `ConvexPolytopeRealization`).**  Conditional on the
realization datum `R` (the ℝ³ input, out of scope); no extra side-hypothesis.  Every corresponding dihedral angle of the
two congruent-faced convex-polytope realizations agrees — Cauchy's sign-machinery content, with the
combinatorial low-active-vertex lemma already discharged via the genuine `isSimple` field.  The
`Fin.cast` reindexes the `Q`-realization joint onto the `P` index range (the two realizations have the
same incident-edge count, `R.hnn`). -/
theorem realization_rigid
    (Q : M.Vertex) (i : Fin ((R.starP Q).n - 1)) :
    (R.starP Q).dihedral i
      = (R.starQ Q).dihedral (Fin.cast (by rw [R.hnn Q]) i) := by
  have hzero := R.realization_all_edgeSign_zero
  -- link joint angles agree
  have hj := R.jointAngle_eq_of_edgeSign_zero hzero Q i
  -- Bridge B on the P-star: jointAngle (starP Q).vertexLink i = (starP Q).dihedral i
  rw [VertexStar.jointAngle_vertexLink_eq_dihedral] at hj
  -- on the Q side: jointAngle (linkQ Q) i = jointAngle (starQ Q).vertexLink (cast i) = (starQ Q).dihedral (cast i)
  rw [show R.linkQ Q = (fun j : Fin ((R.starP Q).n + 1) =>
        (R.starQ Q).vertexLink (Fin.cast (by rw [R.hnn Q]) j)) from rfl] at hj
  rw [jointAngle_reindex (R.hnn Q).symm (R.starQ Q).vertexLink i] at hj
  rw [VertexStar.jointAngle_vertexLink_eq_dihedral] at hj
  exact hj

end ConvexPolytopeRealization

end ProofsInTheBook.Ch13Realization

/-! ## Non-vacuity of the count-reconciliation identity

On the concrete real sequence `[1, 0, -1, 0]` both count machineries return `2` (one cyclic
plus/minus split, the two zeros skipped), witnessing the reconciliation as a genuine, realized
identity. -/

namespace ProofsInTheBook.Ch13Realization

/-- The concrete `Fin 4 → ℝ` witness `[1, 0, -1, 0]`. -/
noncomputable def reconWitness : Fin 4 → ℝ := ![1, 0, -1, 0]

theorem nzSigns_reconWitness : nzSigns reconWitness = [true, false] := by
  have h4 : List.finRange 4 = [(0 : Fin 4), 1, 2, 3] := by decide
  have v0 : reconWitness 0 = 1 := rfl
  have v1 : reconWitness 1 = 0 := rfl
  have v2 : reconWitness 2 = -1 := rfl
  have v3 : reconWitness 3 = 0 := rfl
  simp only [nzSigns, h4, List.filter_cons, List.filter_nil, v0, v1, v2, v3]
  norm_num [v0, v1, v2, v3]

/-- Both count machineries agree, returning `2`, on the witness — a genuine realized instance of the
reconciliation identity. -/
example :
    cyclicFlips (nzSigns reconWitness)
      = cyclicFlipCountSkipZeros ((List.ofFn reconWitness).map realSignToEdgeSign)
    ∧ cyclicFlips (nzSigns reconWitness) = 2 := by
  refine ⟨cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros reconWitness, ?_⟩
  rw [nzSigns_reconWitness]; decide

/-- Rotation invariance is genuine: rotating `[plus, zero, minus]` to `[zero, minus, plus]` leaves the
skip-zeros cyclic flip count unchanged (both `2`). -/
example :
    cyclicFlipCountSkipZeros [EdgeSign.plus, EdgeSign.zero, EdgeSign.minus]
      = cyclicFlipCountSkipZeros [EdgeSign.zero, EdgeSign.minus, EdgeSign.plus] := by
  apply cyclicFlipCountSkipZeros_of_isRotated
  exact ⟨1, by decide⟩

end ProofsInTheBook.Ch13Realization

#print axioms ProofsInTheBook.Ch13Realization.cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros
#print axioms ProofsInTheBook.Ch13Realization.cyclicFlipCountSkipZeros_of_isRotated
#print axioms ProofsInTheBook.Ch13Realization.ConvexPolytopeRealization.signChangesFull_eq_vertexFlip
#print axioms ProofsInTheBook.Ch13Realization.ConvexPolytopeRealization.vertexArm_signChanges_eq
#print axioms ProofsInTheBook.Ch13Realization.ConvexPolytopeRealization.realization_marked
#print axioms ProofsInTheBook.Ch13Realization.ConvexPolytopeRealization.realization_rigid
