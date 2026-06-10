import ProofsInTheBook.ZinanCh36InteriorValue

/-!
# `ZinanCh36SignSync` — worker bricks of the Ch36 sign-synchronization design

This file implements the INDEPENDENT worker bricks (1, 3, 6, 9) of the Chapter-36 peel-tree
sign-synchronization design (`HANDOFF/design-rounds/ch36-peel-tree-sign-sync.md`).  The master
bricks (2, 4, 5, 7, 10, 11, 12, 13) and the perturbation-dependent brick 8 are produced
elsewhere; here we land the ray-indexed guard-free package, the signed singleton jump, the omega
core, and the sub-boundary-implies-diagonal bookkeeping.

## Inventory answers (settled by reading source — see report)

* **(a)** There is NO landed `windCross_eq_sum_crossing_eSign`, but `windCross` is *derivably* a
  sum over `CrossingEdges'` of `eSign`: `windCross = ∑ i, sEdge` (`windCross_eq_sum_sEdge`,
  `PolygonWindingExterior`) and `sEdge P ρ z i = eSign P ρ i * [EdgeCrossesRay' P ρ z i]`
  (`sEdge_eq_eSign_mul`).  CRUCIALLY `eSign P ρ i = edgeSign ρ.r (P.q i) (P.q (cyclicNext i))` is
  BASE-POINT-INDEPENDENT (depends only on edge geometry vs ray direction, not on `x`).  So the
  signed jump (brick 3) needs NO shared-eSign hypothesis: `windCross x − windCross y` telescopes
  over the symmetric difference using the *same* `eSign`.  We package this as
  `windCross_eq_sum_crossingEdges_eSign` below.

* **(b)** `windCross_locally_constant_off_boundary` (`PolygonWindingExterior`) EXISTS with shape
  `∀ᶠ y in nhds x, windCross Q σ y = windCross Q σ x` for `¬ OnBoundary Q x`, WITHOUT vertex
  guards.  (Used by master bricks 5/11, not directly here.)

* **(c)** `windCross_mem_final` (`ZinanCh36Interval`) REQUIRES vertex guards
  (`hoff : ¬ OnBoundary P x` AND `hvert : ∀ k, side ρ.r x (P.q k) ≠ 0`).  No guard-free parent
  bound exists.  Hence ray-indexed brick 8 (`rayWindValues_split_offAll`) cannot derive its parent
  bound at a guard-violating off-all point without the perturb-to-generic machinery (the unlanded
  bricks 10–11).  **Brick 8 is SKIPPED** here (it belongs with 10–11), as the design's option (iii)
  predicted.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36SignSync

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonWinding (windCross windCross_eq)
open ProofsInTheBook.PolygonWindingExterior
  (eSign sEdge windCross_eq_sum_sEdge sEdge_eq_eSign_mul)
open ProofsInTheBook.PolygonWindingBound (eSign_mem)
open ProofsInTheBook.ZinanCh36InteriorValue (WindValuesWithSign)
open ProofsInTheBook.PolygonDiagonal
  (leftLength rightLength leftIndex rightIndex subpolygonLeftTuple subpolygonRightTuple)
open ProofsInTheBook.PolygonOracle
  (arcPt cyclicNext_arcPt left_arc_edge_endpoints left_diag_edge_endpoints)
open ProofsInTheBook.PolygonResidues (vertex_onBoundary)

noncomputable section

variable {n : ℕ}

/-! ## Brick 1 — the ray-indexed, GUARD-FREE value package -/

/-- **The ray-indexed signed value package (guard-free).**  `RayWindValuesWithSign P ρ s` asserts
that `s` is a unit sign and that at every off-boundary point of `P` the signed winding along the
fixed ray `ρ` is either `0` (exterior) or exactly `s` (interior) — with NO vertex-genericity
guard.  This is the master primitive of the sign-sync induction: local constancy (brick 11) covers
the vertex-ray points the guard-ful `WindValuesWithSign` would exclude. -/
def RayWindValuesWithSign (P : StrictSimplePolygon n) (ρ : RayDirection P) (s : ℤ) : Prop :=
  (s = 1 ∨ s = -1) ∧
    ∀ x : Pt, ¬ OnBoundary P x → windCross P ρ x = 0 ∨ windCross P ρ x = s

/-- The package's sign is a unit. -/
theorem RayWindValuesWithSign.sign_unit {P : StrictSimplePolygon n} {ρ : RayDirection P} {s : ℤ}
    (h : RayWindValuesWithSign P ρ s) : s = 1 ∨ s = -1 := h.1

/-- The package's value dichotomy at an off-boundary point. -/
theorem RayWindValuesWithSign.values {P : StrictSimplePolygon n} {ρ : RayDirection P} {s : ℤ}
    (h : RayWindValuesWithSign P ρ s) (x : Pt) (hoff : ¬ OnBoundary P x) :
    windCross P ρ x = 0 ∨ windCross P ρ x = s := h.2 x hoff

/-- **The oriented ray-wind data carrier.**  A `Type`-valued structure bundling the sign together
with the package, so the sign `s` is projectable as data.  (A `Prop`-valued structure could not
expose `s` as data without choice; we make this `Type`-valued since it is an auxiliary carrier for
the brick-12 induction — the design explicitly permits this.) -/
structure RayOrientedWindData (P : StrictSimplePolygon n) (ρ : RayDirection P) : Type where
  /-- the orientation sign. -/
  s : ℤ
  /-- the sign is a unit. -/
  hs : s = 1 ∨ s = -1
  /-- the guard-free value package at this sign. -/
  values : RayWindValuesWithSign P ρ s

/-- **Bridge to the landed guard-ful package.**  From the guard-free ray-wise package at every ray
(common sign `s`), the guard-ful `WindValuesWithSign P s` follows by weakening: the guard-ful
obligation `∀ ρ x, ¬OnBoundary → (∀ k, side ≠ 0) → windCross ∈ {0,s}` is implied because the
guard-free package does not even consult the vertex guard. -/
theorem WindValuesWithSign.of_raywise {P : StrictSimplePolygon n} {s : ℤ}
    (hs : s = 1 ∨ s = -1)
    (hray : ∀ ρ : RayDirection P, RayWindValuesWithSign P ρ s) :
    WindValuesWithSign P s :=
  ⟨hs, fun ρ x hoff _hvert => (hray ρ).values x hoff⟩

/-! ## Brick 3 — the signed singleton jump

`windCross` is the signed sum, over the span-crossed edges, of the BASE-POINT-INDEPENDENT
orientation signs `eSign`.  When the crossing sets at two points differ by exactly one edge `e`,
the two windings differ by `± eSign e = ±1 ≠ 0`, so they are unequal. -/

/-- **`windCross` as a signed sum over the crossing edges.**  Restricts the all-edges sum
`windCross = ∑ i, sEdge` to the span-crossed edges (the others contribute `0`), where each crossed
edge contributes its base-point-independent sign `eSign`. -/
theorem windCross_eq_sum_crossingEdges_eSign (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) :
    windCross P ρ x = ∑ i ∈ CrossingEdges' P ρ x, eSign P ρ i := by
  classical
  rw [windCross_eq_sum_sEdge]
  -- Each term `sEdge = eSign * [EdgeCrossesRay']`; restrict the universe sum to the crossing set.
  have hterm : ∀ i : Fin n, sEdge P ρ x i
      = if i ∈ CrossingEdges' P ρ x then eSign P ρ i else 0 := by
    intro i
    rw [sEdge_eq_eSign_mul]
    by_cases hc : EdgeCrossesRay' P ρ x i
    · rw [if_pos hc, if_pos ((mem_crossingEdges'_iff P ρ x i).mpr hc), mul_one]
    · rw [if_neg hc, if_neg (fun hm => hc ((mem_crossingEdges'_iff P ρ x i).mp hm)), mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_mem, Finset.univ_inter]

/-- **The signed singleton jump.**  If the span-crossed edge sets at `x` and `y` differ by exactly
the singleton `{e}`, then the signed windings at `x` and `y` are unequal: they differ by
`± eSign e`, and `eSign e = ±1 ≠ 0`.  No shared-eSign hypothesis is needed because `eSign` is
base-point-independent (it is the same function `eSign P ρ` at both `x` and `y`). -/
theorem windCross_ne_of_symmDiff_singleton {m : ℕ} (Q : StrictSimplePolygon m)
    (σ : RayDirection Q) {x y : Pt} {e : Fin m}
    (hsd : symmDiff (CrossingEdges' Q σ x) (CrossingEdges' Q σ y) = {e}) :
    windCross Q σ x ≠ windCross Q σ y := by
  classical
  set A := CrossingEdges' Q σ x with hA
  set B := CrossingEdges' Q σ y with hB
  -- Split each crossing-edge sum over the symmetric difference and the intersection.
  -- `∑_A f − ∑_B f = ∑_{A\B} f − ∑_{B\A} f`, and `(A\B) ∪ (B\A) = {e}`.
  intro hcontra
  rw [windCross_eq_sum_crossingEdges_eSign, windCross_eq_sum_crossingEdges_eSign,
    ← hA, ← hB] at hcontra
  -- Reorganize each sum into (over A∩B) + (over A\B).
  have hsplitA : ∑ i ∈ A, eSign Q σ i
      = ∑ i ∈ A ∩ B, eSign Q σ i + ∑ i ∈ A \ B, eSign Q σ i := by
    rw [← Finset.sum_inter_add_sum_diff A B (eSign Q σ)]
  have hsplitB : ∑ i ∈ B, eSign Q σ i
      = ∑ i ∈ A ∩ B, eSign Q σ i + ∑ i ∈ B \ A, eSign Q σ i := by
    rw [Finset.inter_comm]
    rw [← Finset.sum_inter_add_sum_diff B A (eSign Q σ)]
  -- Hence ∑_{A\B} = ∑_{B\A}.
  rw [hsplitA, hsplitB] at hcontra
  have hdiffEq : ∑ i ∈ A \ B, eSign Q σ i = ∑ i ∈ B \ A, eSign Q σ i := by omega
  -- The symmetric difference is the disjoint union (A\B) ∪ (B\A) = {e}; the two diff sets are
  -- disjoint and exactly one of them is {e}, the other ∅.
  have hsymm : (A \ B) ∪ (B \ A) = {e} := by
    -- `symmDiff` on `Finset` is `(A \ B) ⊔ (B \ A) = (A \ B) ∪ (B \ A)`.
    rw [← hsd, symmDiff_def, Finset.sup_eq_union]
  have hdisj : Disjoint (A \ B) (B \ A) := disjoint_sdiff_sdiff
  -- The disjoint union is the singleton {e}: each part is a subset of {e}, hence ∅ or {e}.
  have hsubAB : A \ B ⊆ {e} := by rw [← hsymm]; exact Finset.subset_union_left
  have hsubBA : B \ A ⊆ {e} := by rw [← hsymm]; exact Finset.subset_union_right
  -- e is in exactly one of the two parts.
  have hmem : e ∈ A \ B ∨ e ∈ B \ A := by
    have : e ∈ (A \ B) ∪ (B \ A) := by rw [hsymm]; exact Finset.mem_singleton_self e
    rwa [Finset.mem_union] at this
  have hsgn : eSign Q σ e = 1 ∨ eSign Q σ e = -1 :=
    eSign_mem Q σ e
  rcases hmem with heAB | heBA
  · -- A\B = {e}, B\A = ∅  (since they are disjoint and e ∈ A\B).
    have hBAe : e ∉ B \ A := Finset.disjoint_left.mp hdisj heAB
    have hBAemp : B \ A = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      have : a = e := Finset.mem_singleton.mp (hsubBA ha)
      rw [this] at ha; exact hBAe ha
    have hABe : A \ B = {e} := Finset.Subset.antisymm hsubAB (by
      intro a ha; rw [Finset.mem_singleton] at ha; rw [ha]; exact heAB)
    rw [hABe, hBAemp, Finset.sum_singleton, Finset.sum_empty] at hdiffEq
    rcases hsgn with h1 | h1 <;> rw [h1] at hdiffEq <;> simp at hdiffEq
  · -- symmetric: B\A = {e}, A\B = ∅.
    have hABe : e ∉ A \ B := Finset.disjoint_right.mp hdisj heBA
    have hABemp : A \ B = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      have : a = e := Finset.mem_singleton.mp (hsubAB ha)
      rw [this] at ha; exact hABe ha
    have hBAe : B \ A = {e} := Finset.Subset.antisymm hsubBA (by
      intro a ha; rw [Finset.mem_singleton] at ha; rw [ha]; exact heBA)
    rw [hABemp, hBAe, Finset.sum_singleton, Finset.sum_empty] at hdiffEq
    rcases hsgn with h1 | h1 <;> rw [h1] at hdiffEq <;> simp at hdiffEq

/-! ## Brick 6 — the omega core of sign synchronization -/

/-- **Sibling sign synchronization (pure arithmetic core).**  Two child polygons with unit signs
`sL, sR`, each contributing windings in `{0, sL}` / `{0, sR}` at two tube points `±`, with a jump
on each side (`L₊ ≠ L₋`, `R₊ ≠ R₋`), the additive split identities `L + R = P` at both points, and
the parent winding equal and nonzero across the two points (`P₊ = P₋ ≠ 0`), force `sL = sR`.

Reasoning: the jumps force each side to take BOTH values `0` and `s` across `±`, so
`{L₊, L₋} = {0, sL}` and `{R₊, R₋} = {0, sR}`.  The split `L + R = P` constant `= P₊ ≠ 0` then
pins `P₊ ∈ {sL, sR, sL + sR}`; the only assignment consistent with a constant nonzero parent and
opposite child jumps is `sL = sR`.  `omega` resolves the finite case bash. -/
theorem signs_eq_from_split_local {sL sR : ℤ} (hsL : sL = 1 ∨ sL = -1) (hsR : sR = 1 ∨ sR = -1)
    {Lp Lm Rp Rm Pp Pm : ℤ}
    (hLvals : (Lp = 0 ∨ Lp = sL) ∧ (Lm = 0 ∨ Lm = sL))
    (hRvals : (Rp = 0 ∨ Rp = sR) ∧ (Rm = 0 ∨ Rm = sR))
    (hLjump : Lp ≠ Lm) (hRjump : Rp ≠ Rm)
    (hsplitp : Lp + Rp = Pp) (hsplitm : Lm + Rm = Pm)
    (hPeq : Pp = Pm) (hPnz : Pp ≠ 0) : sL = sR := by
  obtain ⟨hLp, hLm⟩ := hLvals
  obtain ⟨hRp, hRm⟩ := hRvals
  rcases hsL with hsL | hsL <;> rcases hsR with hsR | hsR <;>
    rcases hLp with h1 | h1 <;> rcases hLm with h2 | h2 <;>
    rcases hRp with h3 | h3 <;> rcases hRm with h4 | h4 <;> omega

/-! ## Brick 9 — a sub-boundary point off the parent boundary lies on the diagonal

Every child (left or right) polygon edge is either a parent edge or the shared diagonal.  A point
off the parent boundary that lies on a child boundary must therefore lie on the diagonal segment;
its endpoints are parent vertices (hence on the parent boundary), so the point is in the OPEN
diagonal segment.

We prove the LEFT case in full, then derive the RIGHT case by the orientation identity
`subpolygonRightTuple P i j = subpolygonLeftTuple P j i` (`rightIndex i j = leftIndex j i`,
definitionally), which lets us reuse the left edge-endpoint lemmas with `(j, i)`. -/

/-- A point on a LEFT-subpolygon edge that is OFF the parent boundary lies in the open diagonal
segment `(P.q i, P.q j)`.  Each left edge has parent-vertex endpoints (an arc edge ⟹ parent edge ⟹
`OnBoundary P`, contradiction) except the final diagonal edge `j → i`; on the diagonal edge the
point is in `seg (P.q i) (P.q j)`, and excludes the endpoints because they are parent vertices. -/
theorem subBoundaryLeft_of_parentOff_is_diag {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j) (lax : LeftStrictAxioms P i j) {x : Pt}
    (hPoff : ¬ OnBoundary P x)
    (hL : OnBoundary (buildLeftPoly h lax) x) :
    x ∈ openSegment ℝ (P.q i) (P.q j) := by
  have hij : i ≠ j := h.1
  obtain ⟨k, hk⟩ := hL
  -- The child edge `k` joins `subpolygonLeftTuple P i j k` to its cyclic successor.
  rw [Edge, buildLeftPoly_q] at hk
  simp only [PolygonDiagonal.subpolygonLeftTuple] at hk
  -- `k.val ≤ cyclicSteps i j` since `leftLength = cyclicSteps + 1`.
  have hkle : k.val ≤ cyclicSteps i j := by
    have := k.isLt; unfold leftLength at this; omega
  rcases lt_or_eq_of_le hkle with hklt | hkeq
  · -- Arc edge: endpoints are parent vertices arcPt i k.val and arcPt i (k.val+1);
    -- this is parent edge arcPt i k.val, so x ∈ Edge P (arcPt i k.val) ⟹ OnBoundary P x.
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    obtain ⟨h1, h2⟩ := left_arc_edge_endpoints hij hklt
    rw [h1, h2] at hk
    exact absurd ⟨arcPt i k.val, by
      rw [Edge, cyclicNext_arcPt i k.val hn]; exact hk⟩ hPoff
  · -- Diagonal edge: endpoints are P.q j and P.q i, so x ∈ seg (P.q j) (P.q i).
    obtain ⟨h1, h2⟩ := left_diag_edge_endpoints hij hkeq
    rw [h1, h2] at hk
    -- x ∈ seg (P.q j) (P.q i) = segment ℝ (P.q j) (P.q i).
    -- exclude the endpoints: P.q i, P.q j are parent vertices ⟹ OnBoundary P ⟹ contradiction.
    have hxi : x ≠ P.q i := by rintro rfl; exact hPoff (vertex_onBoundary P i)
    have hxj : x ≠ P.q j := by rintro rfl; exact hPoff (vertex_onBoundary P j)
    -- openSegment is symmetric in its endpoints; hk : x ∈ seg (P.q j) (P.q i).
    rw [openSegment_symm]
    exact mem_openSegment_of_ne_left_right hxj.symm hxi.symm hk

/-- A point on a RIGHT-subpolygon edge that is OFF the parent boundary lies in the open diagonal
segment.  Reduced to the left case along the reversed diagonal `(j, i)`, since
`subpolygonRightTuple P i j = subpolygonLeftTuple P j i` (definitionally, as `rightIndex i j =
leftIndex j i` and `rightLength i j = leftLength j i`); the open segment is symmetric. -/
theorem subBoundaryRight_of_parentOff_is_diag {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j) (rax : RightStrictAxioms P i j) {x : Pt}
    (hPoff : ¬ OnBoundary P x)
    (hR : OnBoundary (buildRightPoly h rax) x) :
    x ∈ openSegment ℝ (P.q i) (P.q j) := by
  have hij : i ≠ j := h.1
  -- `subpolygonRightTuple P i j = subpolygonLeftTuple P j i` definitionally (rightIndex i j =
  -- leftIndex j i, rightLength i j = leftLength j i).  So the right polygon's boundary IS the
  -- left polygon's boundary along the reversed diagonal `(j, i)`; we reduce to the LEFT theorem.
  -- Each right edge `k` (length `rightLength i j = leftLength j i`) is a left-`(j,i)` edge.
  obtain ⟨k, hk⟩ := hR
  rw [Edge, buildRightPoly_q] at hk
  simp only [PolygonDiagonal.subpolygonRightTuple] at hk
  -- View `k` at the reversed-diagonal length (defeq types).
  set k' : Fin (leftLength j i) := Fin.cast rfl k with hk'def
  have hidx : rightIndex i j k = leftIndex j i k' := rfl
  have hidxn : rightIndex i j (cyclicNext k) = leftIndex j i (cyclicNext k') := rfl
  rw [hidx, hidxn] at hk
  have hkle : k'.val ≤ cyclicSteps j i := by
    have := k'.isLt; unfold leftLength at this; omega
  rcases lt_or_eq_of_le hkle with hklt | hkeq
  · have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    obtain ⟨h1, h2⟩ := left_arc_edge_endpoints (i := j) (j := i) hij.symm (k := k') hklt
    rw [h1, h2] at hk
    exact absurd ⟨arcPt j k'.val, by
      rw [Edge, cyclicNext_arcPt j k'.val hn]; exact hk⟩ hPoff
  · obtain ⟨h1, h2⟩ := left_diag_edge_endpoints (i := j) (j := i) hij.symm (k := k') hkeq
    rw [h1, h2] at hk
    -- now x ∈ seg (P.q i) (P.q j) (left-diag along (j,i): endpoints i then j).
    have hxi : x ≠ P.q i := by rintro rfl; exact hPoff (vertex_onBoundary P i)
    have hxj : x ≠ P.q j := by rintro rfl; exact hPoff (vertex_onBoundary P j)
    exact mem_openSegment_of_ne_left_right hxi.symm hxj.symm hk

/-- **Sub-boundary implies diagonal (combined).**  A point off the parent boundary lying on EITHER
child boundary lies in the open diagonal segment `(P.q i, P.q j)`. -/
theorem subBoundary_of_parentOff_is_diag {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j) (lax : LeftStrictAxioms P i j)
    (rax : RightStrictAxioms P i j) {x : Pt}
    (hPoff : ¬ OnBoundary P x)
    (hSub : OnBoundary (buildLeftPoly h lax) x ∨ OnBoundary (buildRightPoly h rax) x) :
    x ∈ openSegment ℝ (P.q i) (P.q j) := by
  rcases hSub with hL | hR
  · exact subBoundaryLeft_of_parentOff_is_diag h lax hPoff hL
  · exact subBoundaryRight_of_parentOff_is_diag h rax hPoff hR

end

end ProofsInTheBook.ZinanCh36SignSync

/-! ## Axiom audit (clean-3 expected: `propext`, `Classical.choice`, `Quot.sound`) -/

#print axioms ProofsInTheBook.ZinanCh36SignSync.WindValuesWithSign.of_raywise
#print axioms ProofsInTheBook.ZinanCh36SignSync.windCross_eq_sum_crossingEdges_eSign
#print axioms ProofsInTheBook.ZinanCh36SignSync.windCross_ne_of_symmDiff_singleton
#print axioms ProofsInTheBook.ZinanCh36SignSync.signs_eq_from_split_local
#print axioms ProofsInTheBook.ZinanCh36SignSync.subBoundary_of_parentOff_is_diag
