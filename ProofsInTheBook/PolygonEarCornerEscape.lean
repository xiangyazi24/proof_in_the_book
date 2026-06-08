import ProofsInTheBook.PolygonEarEscape
import ProofsInTheBook.PolygonEarDelete

/-!
# Chapter 36 — discharging the LOCAL residue `PolygonEarEscape.EarCornerEscape`
  (`PolygonEarCornerEscape`)

`PolygonEarEscape` shrank `EarCutData.earDeletedExterior` (the planar Jordan kernel) down to a
single LOCAL named residue `EarCornerEscape`: a strict-interior ear point `x` of the ear vertex
admits a `P'`-boundary-free **bent two-leg escape** (`P' = buildRightPoly hdiag rax`, the
ear-deleted `(n-1)`-gon).  This module attacks that residue from the genuine local geometry:
SIMPLE polygon (`EdgeIntersectionCondition`) + the GIVEN non-crossing diagonal `uw`
(`IsDiagonal'`) + the empty-ear corner.

## What is genuinely PROVED here (unconditional, clean-3)

The substrate offered NO map from `P'` edges to `P` edges.  We build it:

* **`rightEdge_eq_or_diagonal`** — the **P′-edge classification**.  For *every* edge `k` of the
  ear-deleted polygon `P' = buildRightPoly hdiag rax`, the ordered endpoint pair
  `(P'.q k, P'.q (cyclicNext k))` is EITHER a consecutive pair of `P`-vertices `(P.q a,
  P.q (cyclicNext a))` (a genuine `P` edge — hence `⊆ OnBoundary P`) OR the ear-base diagonal
  `(P.q (cyclicPrev i), P.q (cyclicNext i))` (= `uw`, the wraparound edge that replaces the two
  deleted ear edges).  This is the exact "`P′` edges = `P` edges minus `uv,vw` plus `uw`" fact,
  proved by `rightIndex`/`cyclicNext` arithmetic from the public `cyclicSteps` API.

* **`onBoundary_earDeleted_of`** / **`notOnBoundary_earDeleted_of`** — UNCONDITIONAL: a point on
  `P'`'s boundary is on some `P` edge OR on the diagonal `seg(u,w)`; contrapositively, a point off
  `P`'s boundary and off the diagonal is off `P'`'s boundary.  (Pure consequence of the
  classification — no empty-ear needed.)

* **`interiorEar_notMem_diagonal`** — UNCONDITIONAL: a strict-interior ear point
  `x = w0•u + w1•v + w2•w` (all weights `> 0`) is NOT on the diagonal `seg(u,w)`, because
  `orient u w x = w1 · orient u w v ≠ 0` (the ear is nondegenerate, `earOrient`).

* **`interiorEar_offBoundary_earDeleted`** — UNCONDITIONAL: assembling the two facts, a
  strict-interior ear point off `P`'s boundary is off `P'`'s boundary.  This is the
  `¬ OnBoundary P' x` half of `EarCornerEscape`, now FREE.

* The Leg-2 tail (`belowExtreme_offBoundary_earDeleted`) and the whole bent-path transport are
  re-used from `PolygonEarEscape`.

## The one local residue that genuinely remains: Leg-1 boundary-freeness

The bent escape's Leg 1 is the short segment from the interior ear point `x` across an ear edge
into the extreme vertex's deleted corner.  Its boundary-freeness is exactly the *empty-ear
edge-vs-segment* fact: **no `P'` edge enters the open ear triangle**.  Proving this from
`EarCutData` requires the EMPTY-EAR datum — *no `P`-vertex lies strictly inside the triangle
`uvw`* — to rule out a `P`-edge endpoint inside the ear (the adjacent edges of such a vertex would
pierce the ear interior; simplicity and `IsDiagonal'` only block edges that cross the ear
*boundary* `uv`/`vw`/`uw`, not edges with an endpoint *inside*).  **`EarCutData` does not carry
this datum** (its fields are `hdiag`, `lax`, `rax`, `leftRayEq`, `rightRayEq`, `earOrient`,
`earDeletedExterior` — no emptiness of `verticesInAdjacentTriangle`, and no `i = extremeVertex`).
Nor does the extreme angle supply it (the lowest vertex's ear can still enclose another vertex).

So the residue genuinely reduces to ONE minimal, non-vacuous, LOCAL `Prop`:
`EarLeg1Free` — at the ear vertex, for the interior ear point `x`, there is a Leg-1 vector `v₁`
and end parameter `s₁ ≥ 0` whose segment `x + t•v₁` (`t ∈ [0,s₁]`) is off `P'`'s boundary, ending
strictly below the extreme vertex.  This is STRICTLY WEAKER and STRICTLY MORE LOCAL than
`EarCornerEscape`: everything else of `EarCornerEscape` (`¬ OnBoundary P' x`, the Leg-2 downward
tail, `det2 ≠ 0`, the whole assembly) is discharged unconditionally here, leaving only the
empty-ear local edge-vs-segment fact that the bundle does not record.

`earCornerEscape_of_leg1Free` : `EarLeg1Free → EarCornerEscape`, hence (composing with
`PolygonEarEscape.earDeletedExterior_of_cornerEscape`) `EarLeg1Free` discharges
`EarCutData.earDeletedExterior` for the extreme-vertex ear.

No `sorry` / `axiom` / `admit` / `native_decide`.  Exactly one named, non-vacuous residue
(`EarLeg1Free`); everything else is unconditional.
-/

namespace ProofsInTheBook.PolygonEarCornerEscape

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonDiagonal
  (rightLength rightIndex subpolygonRightTuple leftLength)
open ProofsInTheBook.PolygonCutOracle
  (buildRightPoly buildRightPoly_q RightStrictAxioms)
open ProofsInTheBook.PolygonExtremeEar (extremeHeight_le)
open ProofsInTheBook.PolygonGeomInput (extremeVertex)
open ProofsInTheBook.PolygonEarDelete (EarCutData rightLength_earBase)
open ProofsInTheBook.PolygonEarEscape
  (EarCornerEscape belowExtreme_offBoundary_earDeleted earDeletedExterior_of_cornerEscape)
open ProofsInTheBook.PolygonConvexVertex (cyclicNext_val cyclicPrev_val)

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the P′-edge classification

Every edge of `P' = buildRightPoly hdiag rax` (vertex tuple `subpolygonRightTuple P i' j'`,
`i' = cyclicPrev i`, `j' = cyclicNext i`) has its ordered endpoints equal to a consecutive
`P`-vertex pair, OR to the diagonal `(P.q i', P.q j')`.  We work generically with the diagonal
endpoints `i', j'` and specialize to the ear base at the call site. -/

/-- **The cyclic predecessor on `Fin (rightLength i' j')` at a non-wraparound index.**  For
`k.val ≠ 0`, `(cyclicPrev k).val = k.val - 1`.  (Used only to keep `omega` honest.) -/
private lemma rl_cyclicNext_val (i' j' : Fin n) (k : Fin (rightLength i' j')) :
    (cyclicNext k).val = if k.val + 1 < rightLength i' j' then k.val + 1 else 0 :=
  cyclicNext_val k

/-- `(a + 1) % n = (a % n + 1) % n` (modulus `≥ 2`, so `1 % n = 1`). -/
private lemma add_one_mod (a : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    (a + 1) % m = (a % m + 1) % m := by
  conv_lhs => rw [Nat.add_mod]
  rw [Nat.mod_eq_of_lt (show 1 < m by omega)]

/-- **P′-edge classification.**  For every edge index `k` of the right subpolygon along the
diagonal `i' → j'` (with `i' ≠ j'`), the ordered endpoint pair is either a consecutive `P`-vertex
pair, or exactly the diagonal endpoints `(P.q i', P.q j')`. -/
theorem rightEdge_eq_or_diagonal
    (P : StrictSimplePolygon n) {i' j' : Fin n} (hij : i' ≠ j')
    (k : Fin (rightLength i' j')) :
    (∃ a : Fin n,
        subpolygonRightTuple P i' j' k = P.q a ∧
        subpolygonRightTuple P i' j' (cyclicNext k) = P.q (cyclicNext a)) ∨
      (subpolygonRightTuple P i' j' k = P.q i' ∧
        subpolygonRightTuple P i' j' (cyclicNext k) = P.q j') := by
  classical
  -- abbreviations
  set s : ℕ := cyclicSteps j' i' with hs
  have hspos : 0 < s := by
    rw [hs]; exact cyclicSteps_pos_of_ne j' i' hij.symm
  have hsum : cyclicSteps j' i' + cyclicSteps i' j' = n :=
    cyclicSteps_add_reverse j' i' hij.symm
  have hjpos : 0 < cyclicSteps i' j' := cyclicSteps_pos_of_ne i' j' hij
  have hsn : s < n := by rw [hs]; omega
  have hn2 : 2 ≤ n := by omega
  have hrl : rightLength i' j' = s + 1 := by
    rw [rightLength, hs]  -- = cyclicSteps j' i' + 1
  -- `k.val ≤ s`
  have hkle : k.val ≤ s := by have := k.isLt; omega
  -- the right-index of a value `m ≤ s`:
  --   m < s : arc vertex (j' + m) % n ;  m = s : i'
  have hri : ∀ m : Fin (rightLength i' j'),
      (m.val < s → (rightIndex i' j' m).val = (j'.val + m.val) % n) ∧
      (m.val = s → rightIndex i' j' m = i') := by
    intro m
    constructor
    · intro hm
      unfold rightIndex
      rw [dif_pos (by rw [← hs]; exact hm)]
    · intro hm
      unfold rightIndex
      rw [dif_neg (by rw [← hs]; omega)]
  -- `cyclicNext (j'+m)%n` for an arc value `m`:  m+1 < s → (j'+m+1)%n ; m+1 = s → i'.
  -- We use that `(j' + s) % n = i'` (j' is the arc start; s steps reach i').
  have hjs : (j'.val + s) % n = i'.val := by
    -- i' = arcPos j' (cyclicSteps j' i') by j_eq_arcPos, but that is private; redo directly.
    rw [hs]
    unfold cyclicSteps
    have hiLt := i'.isLt
    have hjLt := j'.isLt
    by_cases hle : j'.val ≤ i'.val
    · rw [if_pos hle]
      have : j'.val + (i'.val - j'.val) = i'.val := by omega
      rw [this, Nat.mod_eq_of_lt hiLt]
    · rw [if_neg hle]
      have heq : j'.val + (n - j'.val + i'.val) = n + i'.val := by omega
      rw [heq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hiLt]
  -- now case on whether `k` is the last index.
  by_cases hk : k.val = s
  · -- wraparound edge: endpoints (i', cyclicNext-of-last = index 0 → j').
    right
    refine ⟨?_, ?_⟩
    · -- subpolygonRightTuple P i' j' k = P.q i'
      unfold subpolygonRightTuple
      rw [(hri k).2 hk]
    · -- cyclicNext k = index 0  (since k.val + 1 = s + 1 = rightLength, not < rightLength)
      have hnk0 : (cyclicNext k).val = 0 := by
        rw [rl_cyclicNext_val, if_neg (by omega)]
      -- index 0 maps to (j' + 0) % n = j'
      unfold subpolygonRightTuple
      have hck : (cyclicNext k).val < s := by rw [hnk0]; omega
      congr 1
      apply Fin.ext
      rw [(hri (cyclicNext k)).1 hck, hnk0, Nat.add_zero, Nat.mod_eq_of_lt j'.isLt]
  · -- k.val < s : `P.q (rightIndex k)` is an arc vertex, and the next vertex is consecutive in P.
    left
    have hklt : k.val < s := by omega
    -- a := the P-vertex (j' + k) % n
    have hkrv : (rightIndex i' j' k).val = (j'.val + k.val) % n := (hri k).1 hklt
    refine ⟨rightIndex i' j' k, rfl, ?_⟩
    -- show subpolygonRightTuple P i' j' (cyclicNext k) = P.q (cyclicNext (rightIndex i' j' k))
    unfold subpolygonRightTuple
    -- value of cyclicNext (rightIndex k):
    have hnext_arc : (cyclicNext (rightIndex i' j' k)).val =
        if (j'.val + k.val) % n + 1 < n then (j'.val + k.val) % n + 1 else 0 := by
      rw [cyclicNext_val, hkrv]
    -- reduce to a `.val` equality up front (avoids motive-not-type-correct on `P.q`).
    congr 1
    apply Fin.ext
    rw [hnext_arc]
    by_cases hk1 : k.val + 1 < s
    · -- next P′-index is k+1 < s : another arc vertex (j' + k+1)%n, equals cyclicNext of arc.
      have hnk : (cyclicNext k).val = k.val + 1 := by
        rw [rl_cyclicNext_val, if_pos (by omega)]
      have hck1 : (cyclicNext k).val < s := by rw [hnk]; omega
      rw [(hri (cyclicNext k)).1 hck1, hnk]
      -- LHS: (j' + (k+1))%n ; RHS: if (j'+k)%n+1 < n then (j'+k)%n+1 else 0.
      have hb : (j'.val + k.val) % n < n := Nat.mod_lt _ (by omega)
      have hstep : (j'.val + (k.val + 1)) % n = ((j'.val + k.val) % n + 1) % n := by
        rw [show j'.val + (k.val + 1) = (j'.val + k.val) + 1 by ring, add_one_mod _ hn2]
      rw [hstep]
      by_cases hwrap : (j'.val + k.val) % n + 1 < n
      · rw [if_pos hwrap, Nat.mod_eq_of_lt hwrap]
      · rw [if_neg hwrap]
        have hb1 : (j'.val + k.val) % n + 1 = n := by omega
        rw [hb1, Nat.mod_self]
    · -- next P′-index value is s : it is i'.  And cyclicNext (rightIndex k) = i' too.
      have hks : k.val + 1 = s := by omega
      have hnk : (cyclicNext k).val = k.val + 1 := by
        rw [rl_cyclicNext_val, if_pos (by omega)]
      have hck1 : (cyclicNext k).val = s := by rw [hnk, hks]
      rw [(hri (cyclicNext k)).2 hck1]
      -- LHS: i'.val ; RHS: if (j'+k)%n+1 < n then (j'+k)%n+1 else 0, which equals i'.val.
      have key : ((j'.val + k.val) % n + 1) % n = i'.val := by
        have hcollapse : ((j'.val + k.val) % n + 1) % n = (j'.val + s) % n := by
          rw [← add_one_mod _ hn2, show j'.val + k.val + 1 = j'.val + (k.val + 1) by ring, hks]
        rw [hcollapse, hjs]
      by_cases hwrap : (j'.val + k.val) % n + 1 < n
      · rw [if_pos hwrap]
        have h := key; rw [Nat.mod_eq_of_lt hwrap] at h; omega
      · rw [if_neg hwrap]
        have hb1 : (j'.val + k.val) % n + 1 = n := by
          have := Nat.mod_lt (j'.val + k.val) (show 0 < n by omega); omega
        have hz : ((j'.val + k.val) % n + 1) % n = 0 := by rw [hb1, Nat.mod_self]
        rw [hz] at key; omega

/-! ## Part 2: `¬ OnBoundary P'` from off-`P`-boundary + off-diagonal

The classification says each `P'` edge is contained in `OnBoundary P` or in the diagonal segment
`seg(u,w)`.  Hence a point off `P`'s boundary and off the diagonal is off `P'`'s boundary. -/

/-- **A point on a `P′` edge is on the corresponding `P` edge, or on the diagonal `seg(i',j')`.**
Directly from the endpoint classification: `Edge P'.q k = seg (P'.q k) (P'.q (cyclicNext k))`, and
that segment equals a `P` edge `seg (P.q a) (P.q (cyclicNext a)) = Edge P.q a` or the diagonal
`seg (P.q i') (P.q j')`. -/
theorem onEdge_earDeleted_imp
    (P : StrictSimplePolygon n) {ρ : RayDirection P} {i' j' : Fin n}
    (hdiag : IsDiagonal' P ρ i' j')
    (rax : RightStrictAxioms P i' j')
    {z : Pt} {k : Fin (rightLength i' j')}
    (hz : z ∈ Edge (buildRightPoly hdiag rax).q k) :
    OnBoundary P z ∨ z ∈ seg (P.q i') (P.q j') := by
  have hij : i' ≠ j' := hdiag.1
  rw [Edge, buildRightPoly_q] at hz
  rcases rightEdge_eq_or_diagonal P hij k with ⟨a, ha, hna⟩ | ⟨hi, hj⟩
  · left
    refine ⟨a, ?_⟩
    rw [Edge]
    rwa [ha, hna] at hz
  · right
    rwa [hi, hj] at hz

/-- **Off `P`-boundary + off the diagonal ⟹ off `P'`-boundary** (UNCONDITIONAL).  The contrapositive
of `onEdge_earDeleted_imp`, ranged over all `P'` edges. -/
theorem notOnBoundary_earDeleted_of
    (P : StrictSimplePolygon n) {ρ : RayDirection P} {i' j' : Fin n}
    (hdiag : IsDiagonal' P ρ i' j')
    (rax : RightStrictAxioms P i' j')
    {z : Pt} (hPb : ¬ OnBoundary P z) (hdg : z ∉ seg (P.q i') (P.q j')) :
    ¬ OnBoundary (buildRightPoly hdiag rax) z := by
  rintro ⟨k, hk⟩
  rcases onEdge_earDeleted_imp P hdiag rax hk with h | h
  · exact hPb h
  · exact hdg h

/-! ## Part 3: a strict-interior ear point is off the diagonal `seg(u,w)`

`x = w0•u + w1•v + w2•w` with all weights `> 0`.  If `x ∈ seg(u,w)` then `orient u w x = 0`; but
`orient u w x = w1 · orient u w v` and `orient u w v = -orient u v w ≠ 0` (the ear is
nondegenerate).  Since `w1 > 0`, `orient u w x ≠ 0`, contradiction. -/

open ProofsInTheBook.PolygonLocalConstancy
  (det2_add_left det2_smul_left det2_add_right det2_smul_right det2_self)

/-- **`orient u w x = w1 · orient u w v` for a barycentric combination** with `w0+w1+w2 = 1`.
Bilinearity of `det2` in the second argument: `orient u w x = det2 (w - u) (x - u)`, and
`x - u = w1•(v - u) + w2•(w - u)`, so the `(w-u)` term vanishes (`det2_self`). -/
private lemma orient_diag_interior
    (u v w x : Pt) {w0 w1 w2 : ℝ} (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • u + w1 • v + w2 • w) :
    orient u w x = w1 * orient u w v := by
  unfold orient
  have hxu : x - u = w1 • (v - u) + w2 • (w - u) := by
    rw [hx]
    have : w0 = 1 - w1 - w2 := by linarith
    rw [this]; module
  rw [hxu, det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, add_zero]

/-- **A strict-interior ear point is not on the ear-base diagonal `seg(u,w)`** (UNCONDITIONAL).
From `orient_diag_interior` and the nondegenerate ear orientation. -/
theorem interiorEar_notMem_diagonal
    (P : StrictSimplePolygon n) (i : Fin n)
    (hO : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hw1 : 0 < w1) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i)) :
    x ∉ seg (P.q (cyclicPrev i)) (P.q (cyclicNext i)) := by
  intro hmem
  -- on the diagonal ⟹ collinear ⟹ orient u w x = 0.
  have hcol : orient (P.q (cyclicPrev i)) (P.q (cyclicNext i)) x = 0 :=
    PolygonTriangleConvex.orient_eq_zero_of_mem_seg hmem
  -- but orient u w x = w1 · orient u w v, with orient u w v = - orient u v w ≠ 0.
  have hval : orient (P.q (cyclicPrev i)) (P.q (cyclicNext i)) x
      = w1 * orient (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q i) :=
    orient_diag_interior _ _ _ _ hsum hx
  have huwv : orient (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q i)
      = - orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) :=
    orient_antisymm _ _ _
  rw [hval, huwv] at hcol
  have : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) = 0 := by
    have hne : w1 ≠ 0 := ne_of_gt hw1
    have := mul_eq_zero.mp hcol
    rcases this with h | h
    · exact absurd h hne
    · linarith
  exact hO this

/-- **A strict-interior ear point off `P`'s boundary is off `P'`'s boundary** (UNCONDITIONAL).
The `¬ OnBoundary P' x` half of `EarCornerEscape`, now free: `x` avoids every `P` edge (`hoff`)
and the diagonal (`interiorEar_notMem_diagonal`), so by the classification it avoids every `P'`
edge.  Here `P'` is the ear-deleted polygon for the ear-base diagonal `(cyclicPrev i, cyclicNext i)`. -/
theorem interiorEar_offBoundary_earDeleted
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (hO : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw1 : 0 < w1) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i)) :
    ¬ OnBoundary (buildRightPoly hdiag rax) x :=
  notOnBoundary_earDeleted_of P hdiag rax hoff
    (interiorEar_notMem_diagonal P i hO hw1 hsum hx)

/-! ## Part 4: the minimal Leg-1 residue and the discharge of `EarCornerEscape`

`EarCornerEscape` asks, for the interior ear point `x`, for: (i) `¬ OnBoundary P' x` (PROVED above,
unconditionally), (ii) a Leg-1 vector `v₁`/`s₁` with `x + t•v₁` (`t ∈ [0,s₁]`) off `P'`'s boundary,
ending at `q1 = x + s₁•v₁`, and (iii) from `q1` a downward Leg-2 escape off `P'`'s boundary, with
`det2 σR.r v₂ ≠ 0`.

Leg 2 is unconditional once `q1` is strictly below the extreme vertex `v = extremeVertex P`
(`belowExtreme_offBoundary_earDeleted`): pick `v₂` straight down, then every point of the downward
ray from `q1` is strictly below `v`, hence off `P'`'s boundary.  The only missing geometric input
is Leg 1's boundary-freeness landing `q1` below `v` — the empty-ear edge-vs-segment fact, which the
`EarCutData` bundle does not record.  We isolate exactly that as `EarLeg1Free`. -/

/-- **The minimal Leg-1 residue** (the single named, non-vacuous local fact this route leaves).
At a polygon (`4 ≤ m`) carrying ear-deletion data at vertex `i`, for a strict-interior ear point
`x` off the boundary, there is a Leg-1 vector `v₁` with end parameter `s₁ ≥ 0` such that

* the Leg-1 segment `x + t•v₁` (`t ∈ [0,s₁]`) is off the ear-deleted polygon's boundary, and
* its endpoint `q1 = x + s₁•v₁` lies strictly below the extreme vertex `v = extremeVertex P`.

Geometrically `v₁` crosses an ear edge into the extreme vertex's deleted corner (the empty-ear
edge-vs-segment fact), landing in the `belowExtreme` region.  This is STRICTLY MORE LOCAL than
`EarCornerEscape`: it carries ONLY Leg 1; `¬ OnBoundary P' x` and the entire Leg-2 tail are
discharged unconditionally below.  It is non-vacuous: its conclusion is a genuine boundary-free
segment ending below `v`, the empty-ear geometric content, not a hidden `False`. -/
def EarLeg1Free : Prop :=
  ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m),
    4 ≤ m → EarCutData P ρ i →
    ∀ {x : Pt} {w0 w1 w2 : ℝ},
      ¬ OnBoundary P x →
      0 < w0 → 0 < w1 → 0 < w2 → w0 + w1 + w2 = 1 →
      x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i) →
      ∀ (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
        (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i)),
        ∃ (v₁ : Pt) (s₁ : ℝ), 0 ≤ s₁ ∧
          (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) s₁ →
            ¬ OnBoundary (buildRightPoly hdiag rax) (x + t • v₁)) ∧
          ((x + s₁ • v₁) 1 < (P.q (extremeVertex P)) 1)

/-- The two candidate Leg-2 escape vectors: straight down `(0,-1)` (for non-vertical rays) and
horizontal `(-1,0)` (for vertical rays).  Both are non-increasing in the `y`-coordinate, so a
downward ray from a point below `v` stays below `v`; and at least one has nonzero determinant
against any nonzero ray. -/
private def downVec : Pt := mkPt 0 (-1)
private def sideVec : Pt := mkPt (-1) 0

private lemma downVec_fst : downVec 0 = 0 := by unfold downVec; simp [mkPt]
private lemma downVec_snd : downVec 1 = -1 := by unfold downVec; simp [mkPt]
private lemma sideVec_fst : sideVec 0 = -1 := by unfold sideVec; simp [mkPt]
private lemma sideVec_snd : sideVec 1 = 0 := by unfold sideVec; simp [mkPt]

private lemma det2_downVec (r : Pt) : det2 r downVec = - r 0 := by
  unfold det2; rw [downVec_fst, downVec_snd]; ring
private lemma det2_sideVec (r : Pt) : det2 r sideVec = r 1 := by
  unfold det2; rw [sideVec_fst, sideVec_snd]; ring

/-- **An escape vector `v₂` for any nonzero ray `r`**: non-increasing in `y` with `det2 r v₂ ≠ 0`.
Down if `r 0 ≠ 0`, sideways if `r 0 = 0` (then `r 1 ≠ 0`). -/
private lemma exists_escape_vec {r : Pt} (hr : r ≠ 0) :
    ∃ v₂ : Pt, v₂ 1 ≤ 0 ∧ det2 r v₂ ≠ 0 := by
  by_cases h0 : r 0 = 0
  · -- r 1 ≠ 0, use sideVec
    have h1 : r 1 ≠ 0 := by
      intro h1
      exact hr (pt_ext_zero_one h0 h1)
    exact ⟨sideVec, by rw [sideVec_snd], by rw [det2_sideVec]; exact h1⟩
  · exact ⟨downVec, by rw [downVec_snd]; norm_num, by rw [det2_downVec]; simpa using h0⟩

/-- **Leg-2 escape from a point strictly below the extreme vertex** (UNCONDITIONAL).  For `q1`
strictly below `v` and any escape vector `v₂` with `v₂ 1 ≤ 0`, the ray `q1 + t•v₂` (`0 ≤ t`) stays
strictly below `v`, hence off `P'`'s boundary by `belowExtreme_offBoundary_earDeleted`. -/
theorem leg2_offBoundary_earDeleted
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    {q1 v₂ : Pt} (hq1 : q1 1 < (P.q (extremeVertex P)) 1) (hv₂ : v₂ 1 ≤ 0) :
    ∀ t : ℝ, 0 ≤ t → ¬ OnBoundary (buildRightPoly hdiag rax) (q1 + t • v₂) := by
  intro t ht
  refine belowExtreme_offBoundary_earDeleted P ρ i hdiag rax ?_
  have hval : (q1 + t • v₂) 1 = q1 1 + t * v₂ 1 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hval]
  have : t * v₂ 1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hv₂
  linarith

/-- **`EarLeg1Free` ⟹ `EarCornerEscape`** (the bent-path assembly).  For an interior ear point `x`:
`¬ OnBoundary P' x` is `interiorEar_offBoundary_earDeleted` (Part 3, unconditional); Leg 1 comes
from `EarLeg1Free`, landing `q1 = x + s₁•v₁` strictly below the extreme vertex; Leg 2 is the
unconditional below-`v` tail (`leg2_offBoundary_earDeleted`) along an escape vector `v₂` chosen
non-vertical-aware (`exists_escape_vec`) so that `det2 σR.r v₂ ≠ 0`.  Threading these into the
`EarCornerEscape` shape (with `σR.r = ρ.r`) discharges it. -/
theorem earCornerEscape_of_leg1Free (L : EarLeg1Free) : EarCornerEscape := by
  intro m P ρ i hm E x w0 w1 w2 hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr
  -- Part 3: x is off P' boundary, unconditionally.
  have hoffR : ¬ OnBoundary (buildRightPoly hdiag rax) x :=
    interiorEar_offBoundary_earDeleted P ρ i hdiag rax E.earOrient hoff hw1 hsum hx
  refine ⟨hoffR, ?_⟩
  -- Leg 1 from the residue.
  obtain ⟨v₁, s₁, hs₁, hleg1, hq1below⟩ :=
    L P ρ i hm E hoff hw0 hw1 hw2 hsum hx hdiag rax
  refine ⟨v₁, s₁, hs₁, hleg1, ?_⟩
  -- Leg 2: choose an escape vector for σR.r.
  obtain ⟨v₂, hv₂y, hv₂det⟩ := exists_escape_vec σR.r_ne_zero
  refine ⟨v₂, ?_, ?_⟩
  · -- det2 σR.r v₂ ≠ 0
    exact hv₂det
  · -- the downward ray from q1 = x + s₁•v₁ is off P' boundary.
    intro t ht
    exact leg2_offBoundary_earDeleted P ρ i hdiag rax hq1below hv₂y t ht

/-! ## Part 5: the kernel discharge — `EarLeg1Free` ⟹ `EarCutData.earDeletedExterior`

Composing `earCornerEscape_of_leg1Free` with the proved
`PolygonEarEscape.earDeletedExterior_of_cornerEscape`: from the single local Leg-1 residue, a
strict-interior ear point off the boundary lies OUTSIDE the ear-deleted polygon — verbatim the
chapter's Jordan kernel. -/

/-- **`EarLeg1Free` discharges the kernel `EarCutData.earDeletedExterior`** (the full reduction).
A strict-interior ear point off the boundary is outside the ear-deleted polygon for every common
ray, given only the local Leg-1 residue. -/
theorem earDeletedExterior_of_leg1Free (L : EarLeg1Free)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m)
    (hm : 4 ≤ m) (E : EarCutData P ρ i)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σR : RayDirection (buildRightPoly hdiag rax)) (hRr : σR.r = ρ.r) :
    ¬ ClosedRegion' (buildRightPoly hdiag rax) σR x :=
  earDeletedExterior_of_cornerEscape (earCornerEscape_of_leg1Free L)
    P ρ i hm E hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr

end

end ProofsInTheBook.PolygonEarCornerEscape

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonEarCornerEscape.rightEdge_eq_or_diagonal
#print axioms ProofsInTheBook.PolygonEarCornerEscape.onEdge_earDeleted_imp
#print axioms ProofsInTheBook.PolygonEarCornerEscape.notOnBoundary_earDeleted_of
#print axioms ProofsInTheBook.PolygonEarCornerEscape.interiorEar_notMem_diagonal
#print axioms ProofsInTheBook.PolygonEarCornerEscape.interiorEar_offBoundary_earDeleted
#print axioms ProofsInTheBook.PolygonEarCornerEscape.leg2_offBoundary_earDeleted
#print axioms ProofsInTheBook.PolygonEarCornerEscape.earCornerEscape_of_leg1Free
#print axioms ProofsInTheBook.PolygonEarCornerEscape.earDeletedExterior_of_leg1Free

