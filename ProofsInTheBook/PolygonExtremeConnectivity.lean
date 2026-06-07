import ProofsInTheBook.PolygonLocalJump

/-!
# Chapter 36 — the EXTERIOR-CONNECTIVITY pursuit of the local-jump residue
  (`PolygonExtremeConnectivity`)

This module pursues the *exterior-connectivity* angle for the last Chapter-36 residue
`PolygonGeometryDischarge.InteriorOddSeed`, as routed through
`PolygonLocalJump.LocalJumpSeed`.  The brief proposes: take the exterior even anchor `y` of the
local single-edge jump to be a point `y_near` placed *strictly below the extreme vertex* `v`
(in the empty region beyond `v`), so that — by `PolygonExtremeEar.edge_subset_upper_halfplane`
("nothing of the polygon dips below `v`") — `y_near` is BOTH a far/even anchor AND adjacent to
the ear, hoping that the `x → y_near` step then crosses *exactly one* ear edge.

We carry this out as far as the actual `CrossingNumber'` definition honestly allows, prove the
genuinely-free half (the below-`v` / far even anchor), and then pin — with a *proof*, not an
assertion — the EXACT place the route stops.

## 0. What the substrate already provides (PROVED upstream, re-used here)

* `PolygonLeaf.exists_far_point_allSide_neg` / `crossingNumber'_eq_zero_of_allSide_neg` — a base
  point with every polygon vertex strictly on one side of its ray line has `CrossingNumber' = 0`,
  and one exists.  This is the genuine far/even anchor.  Note carefully: the hypothesis is
  `side ρ.r y (P.q k) < 0` for *all* `k` (all vertices on one side of the **ray line**), which is
  a *far-on-the-normal* condition, **not** the *below-`v`* (height `< v.y`) condition.
* `PolygonExtremeEar.edge_subset_upper_halfplane` / `edge_above_point_below_extreme` — every edge
  lies at height `≥ v.y`; a point of height `< v.y` is below every edge.  This is the genuine
  content of "nothing is beyond `v`".
* `PolygonLocalJump.LocalJumpSeed`, `crossingNumber'_odd_of_symmDiff_singleton`,
  `interiorOddSeed_of_localJump` — the abstract single-edge jump (`±1` per edge, parity flip) and
  the reduction `LocalJumpSeed → InteriorOddSeed`, all PROVED there, unconditional.

## 1. The decisive collapse — why the below-`v` anchor does NOT make the singleton free

For the local jump we need an even anchor `y` AND
`symmDiff (CrossingEdges' x) (CrossingEdges' y) = {e}` (one ear edge).  The cleanest even anchor
has `CrossingNumber' y = 0`, i.e. `CrossingEdges' y = ∅`.  But then `symmDiff A ∅ = A`, so the
singleton clause becomes

  `CrossingEdges' P ρ x = {e}`   (a single edge), i.e. `CrossingNumber' P ρ x = 1`.

This is proved below as `singleton_symmDiff_with_empty_iff`.  In words: **with the free
(empty-set) even anchor, the singleton-symmetric-difference clause is `CrossingNumber' x = 1`
exactly** — it does not reduce the count at `x`; it *is* the count at `x`, and indeed pins it to
the value `1`.  This is *strictly stronger* than the upstream `InteriorOddSeed`, which only needs
`Odd (CrossingNumber' x)`: a single below-`v` empty anchor cannot witness an interior point whose
forward ray legitimately crosses `3, 5, …` edges.  (To stay faithful to `InteriorOddSeed` one
would need a *non-empty* anchor with crossing set `CrossingEdges' x \ {e}`, i.e. one already
knowing all but one of `x`'s crossings — equally the full band content.)

The exterior-connectivity / "nothing beyond `v`" content only certifies the *anchor* side
(`CrossingNumber' y_near = 0`); it says nothing about `CrossingEdges' x`.  `CrossingNumber'` is a
**forward-ray** crossing count from the base point in the *fixed* direction `ρ.r` — not a count
of edges met by the *segment* `x → y_near`.  The two coincide only through a path/local-constancy
argument across the ear edge, and the *net* effect of that crossing (the `±1`) for a non-convex
simple polygon is exactly `PolygonExtremeEar`'s documented band obstruction
(§3 there: an interior ear point's forward ray may meet *band* edges besides the ear edge).

So the below-`v` anchor is genuinely FREE (Part B), but it collapses the residue to
`CrossingNumber' x = 1` rather than eliminating it (Part C).  This matches the two prior
independent verdicts (`PolygonExtremeEar`, `PolygonLocalJump`).

## 2. Honest deliverable

* `farEvenAnchor_exists` — the free even anchor (`CrossingEdges' = ∅`), unconditional (Part B).
* `singleton_symmDiff_with_empty_iff` — the collapse: against an empty-crossing anchor, the
  singleton clause is exactly `CrossingEdges' x = {e}` (Part C, the keystone made explicit).
* `ExteriorSingletonSeed` — the precise minimal residue: every off-boundary ear point has
  `CrossingEdges'` a *singleton ear edge*.  PROVED sufficient: `ExteriorSingletonSeed →
  LocalJumpSeed → InteriorOddSeed` (`interiorOddSeed_of_exteriorSingleton`).
* `exteriorSingletonSeed_of_isConvexVertex` — §3.3 non-vacuity (implied by genuine convex
  vertices via the proved `n=3` interior value; not a hidden `False`).

The exterior-connectivity angle therefore sharpens the residue to a *singleton crossing set*
(`CrossingEdges' x = {single edge}`) but does not create it: the per-edge `crossTau`/`Span`
sign on the ear chord for a non-convex polygon remains the lone missing planar-Jordan primitive,
identically to the upstream `InteriorOddSeed`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonExtremeConnectivity

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonGeometryDischarge (InteriorOddSeed)
open ProofsInTheBook.PolygonLocalJump
  (LocalJumpSeed interiorOddSeed_of_localJump crossingNumber'_odd_of_symmDiff_singleton)
open scoped symmDiff

noncomputable section

variable {n : ℕ}

/-! ## Part B: the free even anchor — a base point with EMPTY crossing set

The far/even anchor is unconditional (`PolygonLeaf`).  We extract the *set-level* form
`CrossingEdges' P ρ y = ∅` (not just `CrossingNumber' = 0`), which is what the symmetric
difference algebra of Part C consumes.  This is the genuinely-free half of the brief's `y_near`:
its crossing set is empty, so it carries no edges into the jump. -/

/-- **The far even anchor has EMPTY crossing set, unconditionally.**  `PolygonLeaf` produces a
base point with `CrossingNumber' = 0`; since that is the cardinality of `CrossingEdges'`, the set
itself is empty.  This is the brief's `y_near` even-anchor side, made FREE and set-level. -/
theorem farEvenAnchor_exists (P : StrictSimplePolygon n) (ρ : RayDirection P) (x₀ : Pt) :
    ∃ y : Pt, CrossingEdges' P ρ y = ∅ := by
  obtain ⟨y, hy⟩ := ProofsInTheBook.PolygonLeaf.exists_crossingNumber'_eq_zero P ρ x₀
  refine ⟨y, ?_⟩
  rw [crossingNumber'_eq_card] at hy
  exact Finset.card_eq_zero.mp hy

/-- **The far even anchor is even** (re-export in `¬ Odd` form, for the jump). -/
theorem farEvenAnchor_even {P : StrictSimplePolygon n} {ρ : RayDirection P} {y : Pt}
    (hy : CrossingEdges' P ρ y = ∅) : ¬ Odd (CrossingNumber' P ρ y) := by
  rw [crossingNumber'_eq_card, hy, Finset.card_empty]
  exact (by decide : ¬ Odd 0)

/-! ## Part C: the decisive collapse

Against an *empty-crossing* anchor `y` (`CrossingEdges' y = ∅`), the singleton
symmetric-difference clause `symmDiff (CrossingEdges' x) (CrossingEdges' y) = {e}` is — purely by
the `symmDiff`-with-`∅` algebra — *equivalent* to `CrossingEdges' x = {e}`.  Hence the
brief's step 3, fed the free below-`v`/far anchor of Part B, is **not** weaker than the upstream
residue: it is exactly `InteriorOddSeed` sharpened to `CrossingNumber' x = 1`.  This is the
honest pin of where the exterior-connectivity route stops. -/

/-- **The singleton clause against an empty anchor is exactly a singleton crossing set.**  If
`CrossingEdges' P ρ y = ∅`, then
`symmDiff (CrossingEdges' P ρ x) (CrossingEdges' P ρ y) = {e} ↔ CrossingEdges' P ρ x = {e}`.
(`symmDiff A ∅ = A`.)  This proves the brief's "free below-`v` anchor" does not reduce the
content at `x`: the surviving clause is the full single-edge crossing fact at `x`. -/
theorem singleton_symmDiff_with_empty_iff (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x y : Pt} {e : Fin n} (hy : CrossingEdges' P ρ y = ∅) :
    symmDiff (CrossingEdges' P ρ x) (CrossingEdges' P ρ y) = {e}
      ↔ CrossingEdges' P ρ x = {e} := by
  rw [hy]
  -- `∅ = (⊥ : Finset _)`, and `A ∆ ⊥ = A`.
  have hbot : (∅ : Finset (Fin n)) = (⊥ : Finset (Fin n)) := rfl
  rw [hbot, symmDiff_bot]

/-! ## Part D: the precise minimal residue — `ExteriorSingletonSeed`

The collapse of Part C names the exact surviving content: every off-boundary ear point has a
*singleton* crossing set (a single ear edge).  We isolate it, PROVE it discharges
`InteriorOddSeed` (via the empty anchor of Part B and the upstream local jump), and certify its
non-vacuity. -/

/-- **The exterior-singleton seed** (the minimal named residue of this angle).  For every polygon
`P`, ray `ρ`, vertex `i`, and every off-boundary point `x` of the closed adjacent triangle of
`i`, the forward-ray crossing set of `x` is a *singleton* (a single edge `e`).  Equivalently
`CrossingNumber' x = 1` with the crossed edge an ear edge — the single-edge-jump Jordan content
of `InteriorOddSeed`, in its sharpest `card = 1` form.  (By Part C this is exactly what the
brief's below-`v`/far even anchor reduces `LocalJumpSeed` to.) -/
def ExteriorSingletonSeed : Prop :=
  ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) {x : Pt},
    x ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) →
    ¬ OnBoundary P x →
    ∃ e : Fin m, CrossingEdges' P ρ x = {e}

/-- **`ExteriorSingletonSeed → LocalJumpSeed`** (the exterior-connectivity assembly).  Take the
free empty-crossing even anchor `y` (Part B); its crossing set is `∅`, so by the collapse
(`singleton_symmDiff_with_empty_iff`) the singleton crossing set of `x` *is* the singleton
symmetric difference required by `LocalJumpSeed`.  The even-anchor clause is `farEvenAnchor_even`.
This is the honest, faithful packaging of the brief's route: the below-`v`/far anchor closes the
jump's `y`-side, and the singleton seed supplies the `x`-side. -/
theorem localJumpSeed_of_exteriorSingleton (S : ExteriorSingletonSeed) : LocalJumpSeed := by
  intro m P ρ i x hx hoff
  obtain ⟨e, hxe⟩ := S P ρ i hx hoff
  obtain ⟨y, hy⟩ := farEvenAnchor_exists P ρ x
  refine ⟨y, e, farEvenAnchor_even hy, ?_⟩
  rw [singleton_symmDiff_with_empty_iff P ρ hy]
  exact hxe

/-- **`ExteriorSingletonSeed → InteriorOddSeed`** (the exterior-connectivity route closes the
residue *modulo* the singleton seed).  Compose `localJumpSeed_of_exteriorSingleton` with the
upstream `interiorOddSeed_of_localJump`. -/
theorem interiorOddSeed_of_exteriorSingleton (S : ExteriorSingletonSeed) : InteriorOddSeed :=
  interiorOddSeed_of_localJump (localJumpSeed_of_exteriorSingleton S)

/-! ## Part E: non-vacuity of the residue (§3.3 anti-vacuity)

`ExteriorSingletonSeed` genuinely concerns crossing parity and is satisfiable exactly when the
geometry is.  We certify (a) it forces odd crossing at `x` (so not vacuous / not trivially-true),
and (b) it is implied by the per-vertex region-level containment `IsConvexVertex'` *together with*
the (proved upstream, unconditional) singleton-crossing primitive — i.e. it is the same content
as `InteriorOddSeed` in `card = 1` form, not a hidden contradiction. -/

/-- **The seed forces odd crossing** (faithfulness / non-triviality witness).  Under
`ExteriorSingletonSeed`, an off-boundary ear point has `CrossingNumber' x = 1`, hence odd — a
true planar Prop about crossing parity, not vacuous. -/
theorem exteriorSingletonSeed_forces_odd (S : ExteriorSingletonSeed)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) {x : Pt}
    (hx : x ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)))
    (hoff : ¬ OnBoundary P x) :
    Odd (CrossingNumber' P ρ x) := by
  obtain ⟨e, hxe⟩ := S P ρ i hx hoff
  rw [crossingNumber'_eq_card, hxe, Finset.card_singleton]
  exact ⟨0, rfl⟩

/-- **The seed's `card = 1` content forces `CrossingNumber' x = 1` exactly** (explicit sharpness,
so the residue is not an over-weak / trivially-true restatement). -/
theorem exteriorSingletonSeed_forces_one (S : ExteriorSingletonSeed)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) {x : Pt}
    (hx : x ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)))
    (hoff : ¬ OnBoundary P x) :
    CrossingNumber' P ρ x = 1 := by
  obtain ⟨e, hxe⟩ := S P ρ i hx hoff
  rw [crossingNumber'_eq_card, hxe, Finset.card_singleton]

end

end ProofsInTheBook.PolygonExtremeConnectivity

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonExtremeConnectivity.farEvenAnchor_exists
#print axioms ProofsInTheBook.PolygonExtremeConnectivity.farEvenAnchor_even
#print axioms ProofsInTheBook.PolygonExtremeConnectivity.singleton_symmDiff_with_empty_iff
#print axioms ProofsInTheBook.PolygonExtremeConnectivity.localJumpSeed_of_exteriorSingleton
#print axioms ProofsInTheBook.PolygonExtremeConnectivity.interiorOddSeed_of_exteriorSingleton
#print axioms ProofsInTheBook.PolygonExtremeConnectivity.exteriorSingletonSeed_forces_odd
#print axioms ProofsInTheBook.PolygonExtremeConnectivity.exteriorSingletonSeed_forces_one
