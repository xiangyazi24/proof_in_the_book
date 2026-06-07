import ProofsInTheBook.PolygonEarExistence

/-!
# Chapter 36 — the EXTREME-vertex ear seed: how far the extreme-direction ray closes
  `InteriorOddSeed`, and the exact minimal residue it leaves (`PolygonExtremeEar`)

This file pursues, as far as the geometry honestly allows, the *new specific-structure*
angle requested in the brief: discharge the Chapter-36 residue `InteriorOddSeed` (equivalently
the region-level `IsConvexVertex'` / `EarCutData.earDeletedExterior`) at the
**lexicographically extreme vertex** `v = extremeVertex P` using a ray in the **extreme
(downward) direction**, hoping to bypass the general-chord crossing count that blocked the
prior routes.

## 0. What the prior stack already settled (pinned from source)

The entire Chapter-36 `⌊n/3⌋` headline (`PolygonEarExistence.artGallery_strict`) bottoms out at
a *single* region-level Jordan primitive, exposed under three equivalent names:

* `PolygonSideCrossing.IsConvexVertex' P ρ i`  :=  `closedTri (q (prev i)) (q i) (q (next i))
  ⊆ {x | ClosedRegion' P ρ x}`  — the closed adjacent-triangle containment;
* `PolygonGeometryDischarge.InteriorOddSeed`  — the same containment quantified uniformly
  over every vertex (the *interior odd-crossing seed*: an interior adjacent-triangle point off
  the boundary must carry an odd `CrossingNumber'`);
* `PolygonEarDelete.EarCutData.earDeletedExterior`  — its diagonal-cut reformulation (an
  interior ear point lies *outside* the ear-deleted `(n-1)`-gon).

Everything else is PROVED: the ray-direction independence off the boundary
(`PolygonCutGeometry.regionSplitGenericity_holds`), the diagonal count-additivity
(`PolygonOracle.crossingNumber'_split_identity_common`), the `n = 3` interior base
(`PolygonTriangleConvex.crossingNumber'_interior_eq_one`), and the parity bridge
(`PolygonEarDelete.interiorEar_parity_bridge`).  So `InteriorOddSeed` (for any one vertex per
recursion step) is the lone irreducible content; the brief asks whether the EXTREME vertex
makes it free.

## 1. The ear-deletion needs the seed only at ONE vertex per step — the chosen ear

`PolygonEarExistence.isConvexVertex'_holds` consumes `IsConvexVertex'` at exactly the vertex
`ear P` returned by an *arbitrary* ear selector (for `4 ≤ m`), plus the proved `n = 3` base at
that selector's vertex.  So — affirming the brief's first question — **the seed is needed only
at the selected ear vertex of each sub-polygon, not at every vertex.**  Instantiating the
selector at the extreme vertex (`extremeVertex`, existence PROVED) is admissible; the
question is purely whether the seed is *provable* there.

## 2. What the extreme direction genuinely gives FOR FREE (PROVED here, unconditional)

The extreme vertex `v` is the global `y`-minimiser (`PolygonGeomInput.extreme_vertex_lowest`).
Two clean consequences hold unconditionally and are the true content of the extreme angle:

* `edge_subset_upper_halfplane` — **every polygon edge lies in the closed upper half-plane
  `{z | (P.q v) 1 ≤ z 1}`.**  (A segment between two points of height `≥ y_v` stays at height
  `≥ y_v`; both endpoints qualify by lowest-ness.)  Hence:
* `not_onBoundary_below_extreme` — **no boundary point lies strictly below `v`.**

So a *downward* ray from any point `x` (a ray whose direction has negative second coordinate)
meets **no** edge at any height `< y_v`: the entire sub-ray below `v` is crossing-free, exactly
as the brief anticipated ("no polygon edge is crossed beyond `v`").

## 3. Why this does NOT close the seed — the exact gap (the honest verdict)

The brief's decisive claim — *"the extreme-direction ray meets only the two `v`-incident edges,
so `CrossingNumber' = 1`"* — is **false for non-convex simple polygons.**  Extreme-lowness
controls only the half-plane *below* `v` (height `< y_v`); it says nothing about the **band**
`y_v ≤ height ≤ y_x` directly beneath an interior ear point `x`.  A non-convex polygon may have
*other* edges (whose endpoints are all at height `≥ y_v`, so they respect §2) dipping into that
band directly under `x`'s downward ray, contributing extra crossings whose parity is *not*
pinned by the extreme property.  The crossing count is therefore **not** "exactly the two ear
edges"; it is `(two-ear-edge contribution) + (uncontrolled band contribution)`.

Architecturally there is no escape: `IsDiagonal'` (the ear base `prev v → next v` being a
*genuine* diagonal — chord inside, boundary only at endpoints, `PolygonSideCrossing.IsDiagonal'`)
is itself DERIVED from `IsConvexVertex'` (`convex_vertex_empty_triangle_gives_ear'`), and the
count-additivity split (`crossingNumber'_split_identity_common`) *requires* `IsDiagonal'`.  The
extreme vertex's ear base is a diagonal only when its adjacent triangle is empty — which
extreme-lowness does **not** guarantee.  The lone missing fact is exactly the band parity,
which is the planar-Jordan content the whole stack keeps as the named input.

## 4. The exact minimal residue

We isolate the precise gap as the single named, non-vacuous `Prop`
`ExtremeBandOddSeed`: at the extreme vertex, for an interior ear point off the boundary and a
downward ray, the crossing number is odd.  We PROVE: (a) the extreme half-plane facts feeding
it (§2); (b) that `ExtremeBandOddSeed` is *sufficient* to discharge `InteriorOddSeed` at the
extreme vertex (`interiorOddSeed_at_extreme_of_band`), via the proved off-boundary
ray-independence; and (c) non-vacuity (`extremeBandOddSeed_of_isConvexVertex`: it is implied by
a genuine `IsConvexVertex'`).  The residue `ExtremeBandOddSeed` is *not* smaller than
`InteriorOddSeed` — it is the same single-edge-jump band parity, now localized at the extreme
vertex with the below-`v` tail proved vacuous.  The extreme angle reduces the seed to the band
but does not eliminate it.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonExtremeEar

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonGeomInput
  (vy vx extremeVertex extreme_vertex_lowest exists_extreme_vertex region_ray_independent)

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the ear-deletion needs the seed only at the chosen ear vertex

`PolygonEarExistence.isConvexVertex'_holds` is parameterised by an *arbitrary* ear selector
`ear` and consumes `IsConvexVertex'` only at `ear P` (via `isConvexVertex'_of_earCutData` for
`4 ≤ m`, and the proved triangle base for `m = 3`).  Hence supplying the seed at one chosen
vertex per recursion step suffices; we may take that vertex to be the extreme vertex.  We
record the admissible selector. -/

/-- **The extreme-vertex ear selector** (the brief's choice).  A uniform ear selector that, at
every polygon, returns the lexicographically extreme vertex — the candidate at which the brief
proposes to discharge the seed.  Its combinatorial existence is PROVED
(`exists_extreme_vertex`); only the region-level seed at it is in question. -/
def extremeEar : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m :=
  fun {_m} P => extremeVertex P

/-- **The selector genuinely returns the extreme vertex** (anti-trivial-constant check). -/
theorem extremeEar_eq (P : StrictSimplePolygon n) : extremeEar P = extremeVertex P := rfl

/-! ## Part 2: what the extreme direction gives for free (PROVED, unconditional)

The extreme vertex `v` is the global `y`-minimiser, so every other vertex — hence every edge —
lies in the closed upper half-plane through `v`.  A downward ray therefore meets no edge below
`v`.  These are the genuine, true consequences of extreme-lowness. -/

/-- **Every vertex lies weakly above the extreme height.**  Restatement of
`extreme_vertex_lowest` in second-coordinate form: `(P.q (extremeVertex P)) 1 ≤ (P.q k) 1`. -/
theorem extremeHeight_le (P : StrictSimplePolygon n) (k : Fin n) :
    (P.q (extremeVertex P)) 1 ≤ (P.q k) 1 := by
  have h := extreme_vertex_lowest P k
  -- `vy P k = (P.q k) 1` definitionally.
  simpa [vy] using h

/-- **A segment between two points of height `≥ c` stays at height `≥ c`.**  Convexity of the
closed upper half-plane `{z | c ≤ z 1}`, phrased directly on `seg`. -/
theorem seg_subset_upper_halfplane {a b : Pt} {c : ℝ}
    (ha : c ≤ a 1) (hb : c ≤ b 1) :
    seg a b ⊆ {z : Pt | c ≤ z 1} := by
  intro z hz
  rw [seg, segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  -- `(lineMap a b t) 1 = (1 - t) * a 1 + t * b 1`.
  have hval : (AffineMap.lineMap a b t : Pt) 1 = (1 - t) * a 1 + t * b 1 := by
    rw [AffineMap.lineMap_apply_module]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [Set.mem_setOf_eq, hval]
  obtain ⟨ht0, ht1⟩ := Set.mem_Icc.mp ht
  nlinarith [mul_le_mul_of_nonneg_left ha (by linarith : (0:ℝ) ≤ 1 - t),
    mul_le_mul_of_nonneg_left hb ht0]

/-- **Every polygon edge lies in the closed upper half-plane through the extreme vertex.**  Both
endpoints of any edge are at height `≥ (P.q (extremeVertex P)) 1` (lowest-ness), and the
half-plane is convex.  This is the clean, true core of the extreme angle: nothing of the
polygon dips below `v`. -/
theorem edge_subset_upper_halfplane (P : StrictSimplePolygon n) (i : Fin n) :
    Edge P.q i ⊆ {z : Pt | (P.q (extremeVertex P)) 1 ≤ z 1} := by
  rw [Edge]
  exact seg_subset_upper_halfplane (extremeHeight_le P i) (extremeHeight_le P (cyclicNext i))

/-- **No boundary point lies strictly below the extreme vertex.**  Since every edge is in the
upper half-plane, an on-boundary point has height `≥ (P.q (extremeVertex P)) 1`. -/
theorem not_onBoundary_below_extreme (P : StrictSimplePolygon n) {z : Pt}
    (hz : z 1 < (P.q (extremeVertex P)) 1) :
    ¬ OnBoundary P z := by
  rintro ⟨i, hi⟩
  have := edge_subset_upper_halfplane P i hi
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- **The extreme tail is crossing-free: an edge is never span-crossed by a *downward* ray at a
height strictly below `v`.**  Concretely, if `r` is a downward direction (`r 1 < 0`) and a
point `z` is itself strictly below the extreme height, then `z` is below every edge, so the
forward (downward) ray from `z` cannot reach any edge.  We record the half-plane form used by
the band reduction: every edge's points are at height `≥ y_v > z 1`. -/
theorem edge_above_point_below_extreme (P : StrictSimplePolygon n) {z : Pt}
    (hz : z 1 < (P.q (extremeVertex P)) 1) (i : Fin n) :
    ∀ p ∈ Edge P.q i, z 1 < p 1 := by
  intro p hp
  have := edge_subset_upper_halfplane P i hp
  simp only [Set.mem_setOf_eq] at this
  linarith

/-! ## Part 3: the exact minimal residue — `ExtremeBandOddSeed`

The extreme half-plane facts make the *below-`v`* portion of a downward ray crossing-free, but
the *band* `y_v ≤ height ≤ y_x` directly under an interior ear point `x` is uncontrolled (a
non-convex polygon may have other edges there).  We isolate exactly this band parity as the
single named residue: at the extreme vertex, an interior ear point off the boundary has odd
crossing number for *some* ray.  This is the precise irreducible gap the extreme angle leaves;
it is the same single-edge-jump Jordan content as `InteriorOddSeed`, now localized. -/

/-- **The extreme-vertex band odd seed** (the minimal residue this angle leaves).  For every
polygon `P` (`4 ≤ m`) with extreme vertex `v = extremeVertex P`, every strict-interior point
`x` of `v`'s adjacent triangle that is off the boundary carries an odd crossing number for
*some* ray.  (The extreme half-plane facts of Part 2 discharge the below-`v` tail; the residue
is purely the band crossing parity, which extreme-lowness does not force.) -/
def ExtremeBandOddSeed : Prop :=
  ∀ {m : ℕ} (P : StrictSimplePolygon m), 4 ≤ m →
    ∀ {x : Pt} {w0 w1 w2 : ℝ},
      ¬ OnBoundary P x →
      0 < w0 → 0 < w1 → 0 < w2 → w0 + w1 + w2 = 1 →
      x = w0 • P.q (cyclicPrev (extremeVertex P)) + w1 • P.q (extremeVertex P)
          + w2 • P.q (cyclicNext (extremeVertex P)) →
      ∃ r : RayDirection P, Odd (CrossingNumber' P r x)

/-- **`ExtremeBandOddSeed` places every STRICT-INTERIOR ear point in the region, for every
ray** (the faithful "seed ⇒ region" reduction at the extreme vertex).  A strict-interior point
of the extreme vertex's adjacent triangle that is off the boundary gets the odd seed for *some*
ray (the residue), then is transported to the target ray `ρ` by the proved off-boundary
ray-independence (`region_ray_independent`).  This is the part of `IsConvexVertex'` the band
seed genuinely closes; the boundary strata (open ear base / incident polygon edges) are handled
separately (`isConvexVertex'_at_extreme_of_band`). -/
theorem interiorMem_at_extreme_of_band (S : ExtremeBandOddSeed)
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (hn : 4 ≤ n)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev (extremeVertex P)) + w1 • P.q (extremeVertex P)
        + w2 • P.q (cyclicNext (extremeVertex P))) :
    ClosedRegion' P ρ x := by
  obtain ⟨r, hodd⟩ := S P hn hoff hw0 hw1 hw2 hsum hx
  exact (region_ray_independent P r ρ hoff).mp (Or.inr hodd)

/-- **`ExtremeBandOddSeed` plus the open-base diagonal containment discharges `IsConvexVertex'`
at the extreme vertex** (for `4 ≤ m`).  Every point of the extreme vertex's adjacent triangle is
in the corrected region: the two incident-edge strata (`w0 = 0`, `w2 = 0`) are on the polygon
boundary (PROVED here); the strict-interior stratum uses the band seed
(`interiorMem_at_extreme_of_band`); and the *open ear-base* stratum (`w1 = 0`, off the
boundary) is supplied by `hbase` — the diagonal containment `seg (q (prev v)) (q (next v)) ⊆
ClosedRegion'`, which is itself part of the single-edge-jump Jordan residue (it is DERIVED from
`IsConvexVertex'` upstream via `convex_vertex_empty_triangle_gives_ear'`, so it cannot be
re-derived from the band seed alone — see the file header §3).  We expose it explicitly so the
reduction is faithful, not vacuous. -/
theorem isConvexVertex'_at_extreme_of_band (S : ExtremeBandOddSeed)
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (hn : 4 ≤ n)
    (hbase : seg (P.q (cyclicPrev (extremeVertex P))) (P.q (cyclicNext (extremeVertex P)))
      ⊆ {z : Pt | ClosedRegion' P ρ z}) :
    IsConvexVertex' P ρ (extremeVertex P) := by
  classical
  intro x hx
  set i := extremeVertex P with hi
  obtain ⟨w0, w1, w2, hw0, hw1, hw2, hsum, hxeq⟩ :=
    ProofsInTheBook.PolygonTriangleConvex.exists_barycentric_of_mem_closedTri hx
  rcases eq_or_lt_of_le hw1 with h1 | h1
  · -- w1 = 0 : on the open ear base; supplied by the diagonal containment `hbase`.
    apply hbase
    rw [seg]; refine ⟨w0, w2, hw0, hw2, by linarith, ?_⟩; rw [hxeq, ← h1]; module
  rcases eq_or_lt_of_le hw0 with h0 | h0
  · -- w0 = 0 : polygon edge i (between q i and q (next i)).
    refine closedRegion'_of_onBoundary P ρ ⟨i, ?_⟩
    rw [Edge, seg]; refine ⟨w1, w2, hw1, hw2, by linarith, ?_⟩; rw [hxeq, ← h0]; module
  rcases eq_or_lt_of_le hw2 with h2 | h2
  · -- w2 = 0 : polygon edge prev i (between q (prev i) and q i).
    refine closedRegion'_of_onBoundary P ρ ⟨cyclicPrev i, ?_⟩
    have hnp : cyclicNext (cyclicPrev i) = i :=
      ProofsInTheBook.PolygonJordan.cyclicNext_cyclicPrev_eq
        (le_trans (by norm_num) hn) i
    rw [Edge, hnp, seg]; refine ⟨w0, w1, hw0, hw1, by linarith, ?_⟩; rw [hxeq, ← h2]; module
  · -- strict interior.
    by_cases hoff : OnBoundary P x
    · exact closedRegion'_of_onBoundary P ρ hoff
    · exact interiorMem_at_extreme_of_band S P ρ hn hoff h0 h1 h2 hsum hxeq

/-! ## Part 4: non-vacuity of the residue (§3.3 anti-vacuity)

`ExtremeBandOddSeed` is satisfiable exactly when the geometry is: it is implied by a genuine
region-level `IsConvexVertex'` at the extreme vertex.  Hence the residue is not an
unsatisfiable premise; it is the faithful single-edge-jump band parity at the extreme vertex. -/

/-- **Non-vacuity: `ExtremeBandOddSeed` is implied by `IsConvexVertex'` at the extreme vertex.**
If every polygon (`4 ≤ m`) has its extreme-vertex adjacent triangle region-contained for some
ray (concretely, `IsConvexVertex'` holds there), then `ExtremeBandOddSeed` holds: a
strict-interior off-boundary point of the triangle is in the region, hence — being off the
boundary — has odd crossing number for that ray.  So the residue is satisfiable exactly when the
geometry is (a faithful re-packaging, not a strengthening, and certainly not a hidden `False`). -/
theorem extremeBandOddSeed_of_isConvexVertex
    (H : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), 4 ≤ m →
      IsConvexVertex' P ρ (extremeVertex P)) :
    ExtremeBandOddSeed := by
  intro m P hm x w0 w1 w2 hoff hw0 hw1 hw2 hsum hx
  classical
  obtain ⟨r⟩ := rayDirection_exists P
  refine ⟨r, ?_⟩
  have hxtri : x ∈ closedTri (P.q (cyclicPrev (extremeVertex P))) (P.q (extremeVertex P))
      (P.q (cyclicNext (extremeVertex P))) :=
    ProofsInTheBook.PolygonJordan.mem_closedTri_of_weights hw0.le hw1.le hw2.le hsum hx
  have hreg : ClosedRegion' P r x := H P r hm hxtri
  rcases hreg with hb | hodd
  · exact absurd hb hoff
  · exact hodd

/-- **The band seed genuinely concerns crossing parity** (faithfulness witness, non-triviality):
under `ExtremeBandOddSeed`, a strict-interior extreme-ear point off the boundary really does
carry an odd `CrossingNumber'` for the produced ray — a true planar Prop about crossing parity,
not a vacuous or trivially-true one. -/
theorem extremeBandOddSeed_forces_odd (S : ExtremeBandOddSeed)
    (P : StrictSimplePolygon n) (hn : 4 ≤ n)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev (extremeVertex P)) + w1 • P.q (extremeVertex P)
        + w2 • P.q (cyclicNext (extremeVertex P))) :
    ∃ r : RayDirection P, Odd (CrossingNumber' P r x) :=
  S P hn hoff hw0 hw1 hw2 hsum hx

end

end ProofsInTheBook.PolygonExtremeEar

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonExtremeEar.extremeHeight_le
#print axioms ProofsInTheBook.PolygonExtremeEar.seg_subset_upper_halfplane
#print axioms ProofsInTheBook.PolygonExtremeEar.edge_subset_upper_halfplane
#print axioms ProofsInTheBook.PolygonExtremeEar.not_onBoundary_below_extreme
#print axioms ProofsInTheBook.PolygonExtremeEar.edge_above_point_below_extreme
#print axioms ProofsInTheBook.PolygonExtremeEar.interiorMem_at_extreme_of_band
#print axioms ProofsInTheBook.PolygonExtremeEar.isConvexVertex'_at_extreme_of_band
#print axioms ProofsInTheBook.PolygonExtremeEar.extremeBandOddSeed_of_isConvexVertex
#print axioms ProofsInTheBook.PolygonExtremeEar.extremeBandOddSeed_forces_odd
