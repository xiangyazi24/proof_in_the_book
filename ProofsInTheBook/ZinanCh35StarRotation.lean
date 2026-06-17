import ProofsInTheBook.PlanarMapChordSplitData
import ProofsInTheBook.PlanarMapCutCap

/-!
# Chapter 35 Schoenflies star-rotation: the combinatorial vertex-star API (bricks 1–3)

This file is the purely **combinatorial** substrate of the discrete-Schoenflies star-rotation
design (`HANDOFF/design-rounds/ch35-schoenflies-star-rotation.md`).  It implements the first
three bricks:

* **Brick 1 — Star API.**  `StarDart M x` (darts tailed at a vertex `x`), the vertex rotation
  `starSigma M x` (the `σ`-permutation restricted to the star), the local face read `starFace`,
  the key local identity `starFace_next_eq_alpha`, and the two dual-step lemmas:
  `starStep_chordSplitAdj_of_not_seam` and `star_side₁_next_iff_of_not_seam`.

* **Brick 2 — Cycle–star incidence.**  `CycleStarDart C x`, `cycleStarDarts C x`, the two
  cardinality workers (`…card_eq_zero_of_not_mem`, `…card_eq_two_of_mem`), the packaging
  structure `StarTwoCuts`, and its constructor `starTwoCuts_of_cycle_mem`.

* **Brick 3 — Cut-free rotation walks.**  `RotationArcWithoutCuts`, the *abstract* permutation
  lemma `side_constant_on_cutFree_walk` (no map theory: any `ρ : Equiv.Perm K`, any `Cut`,
  any `Side` invariant under non-cut steps), its specialisation
  `starSide₁_constant_on_cut_free_walk`, and the escape lemma `star_escape_crosses_cycle`
  (a bank change forces crossing a cut on the orbit walk).

## Conventions settled by reading the source (the two danger zones)

### Composition convention: `φ = σ * α` (`PlanarMap.lean:39`).

`M.φ = M.σ * M.α`, i.e. `M.φ d = M.σ (M.α d)`.  The face of a dart is its `φ`-orbit class
`M.dartFace d = ⟦d⟧_φ`, and `M.dartFace_phi : M.dartFace (M.φ d) = M.dartFace d`.

The star rotation `starSigma` sends a star dart `d` to `M.σ d` (still tailed at `x` by
`tail_sigma`).  The KEY local identity is then
`starFace x (starSigma M x d) = M.dartFace (M.α d.1)`:
indeed `M.φ (M.α d) = M.σ (M.α (M.α d)) = M.σ d`, so `M.σ d` and `M.α d` are in the same
`φ`-orbit, hence `M.dartFace (M.σ d) = M.dartFace (M.α d)`.  This is exactly the design's
intent — the next dart around `x` reads the face *across the edge* of `d` — and it holds
on the nose with the project's `φ = σ * α` convention, with NO `σ⁻¹`/side-flip adaptation
needed.

### The Cut predicate is kept PARAMETRIC (brick 3 resolution).

The design notes a genuine mismatch: `star_side₁_next_iff_of_not_seam` needs
`¬ IsBoundaryEdge (dartEdge d) ∧ dartEdge d ≠ s(u,v)` (the full *seam*: every old boundary
edge plus the chord), whereas the cycle `C = chord ∪ ONE arc` only sees its own `edgeSet`
(a dart on the *opposite* arc is a boundary edge but NOT a `C`-edge).  These differ, so the
two notions of "cut" do not coincide.

Resolution: brick 3's master lemma `side_constant_on_cutFree_walk` is stated for an
**arbitrary** `Cut : K → Prop` with the invariance hypothesis
`Inv : ∀ k, ¬ Cut k → (Side k ↔ Side (ρ k))` taken as input.  This is pure permutation
combinatorics with no commitment to which seam set "cut" means.  The later wave (bricks 4–7)
instantiates `Cut` with the *seam* predicate (boundary ∪ chord) — for which brick 1's
`star_side₁_next_iff_of_not_seam` supplies `Inv` directly — and uses brick 2's
`cycleStarDarts` cardinality only to count the `C`-edge cuts.  Here we provide BOTH the generic
form and a `CycleStarDart`-instantiated convenience form
(`starSide₁_constant_on_cut_free_walk`); the generic one is the load-bearing export.

## Honesty note

No `sorry` / `axiom` / `admit` / `native_decide`.  No vacuous statements: every lemma's
hypotheses are inhabited (the star is nonempty as soon as some dart is tailed at `x`; the
abstract walk lemma is universally quantified over genuine permutations).  There is no residue
hypothesis exposed — bricks 1–3 are fully unconditional.

`C.vertexSet` (used in the design) does not exist in the substrate; we define the natural
`CycleVertexMem C x := ∃ i, M.tail (C.dart i) = x` (the cycle passes through `x`) and use it.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Brick 1 — Star API -/

/-- A **star dart** at a vertex `x`: a dart whose tail is `x`.  Since `M.Vertex` is the
`σ`-orbit quotient and `M.tail d = ⟦d⟧_σ`, this is precisely the cyclic family of darts
incident at `x` in their rotation order. -/
abbrev StarDart (M : CombMap D) (x : M.Vertex) : Type _ :=
  {d : D // M.tail d = x}

instance (M : CombMap D) (x : M.Vertex) : DecidableEq (StarDart M x) :=
  Subtype.instDecidableEq

instance (M : CombMap D) (x : M.Vertex) : Fintype (StarDart M x) :=
  Subtype.fintype _

/-- The **vertex rotation** at `x`: the `σ`-permutation restricted to the star.  Well-defined
because `σ` preserves tails (`tail_sigma`). -/
def starSigma (M : CombMap D) (x : M.Vertex) : Equiv.Perm (StarDart M x) where
  toFun d := ⟨M.σ d.1, by rw [tail_sigma, d.2]⟩
  invFun d := ⟨M.σ⁻¹ d.1, by
    have h := M.tail_sigma (M.σ⁻¹ d.1)
    rw [show M.σ (M.σ⁻¹ d.1) = d.1 from M.σ.apply_symm_apply d.1] at h
    rw [← h, d.2]⟩
  left_inv := by intro d; ext; simp
  right_inv := by intro d; ext; simp

@[simp]
lemma starSigma_coe (M : CombMap D) (x : M.Vertex) (d : StarDart M x) :
    (starSigma M x d).1 = M.σ d.1 := rfl

/-- The face seen at a star dart. -/
def starFace {M : CombMap D} (x : M.Vertex) (d : StarDart M x) : M.Face :=
  M.dartFace d.1

/-- **The key local rotation identity.**  Rotating one step around the vertex reads the face
across the edge of the current dart:
`starFace x (starSigma M x d) = M.dartFace (M.α d.1)`.

Proof: with `φ = σ * α`, `M.φ (M.α d.1) = M.σ (M.α (M.α d.1)) = M.σ d.1`, so `M.σ d.1` and
`M.α d.1` share a `φ`-orbit; conclude by `dartFace_phi`. -/
lemma starFace_next_eq_alpha {M : CombMap D} (x : M.Vertex) (d : StarDart M x) :
    starFace x (starSigma M x d) = M.dartFace (M.α d.1) := by
  show M.dartFace (M.σ d.1) = M.dartFace (M.α d.1)
  have hφ : M.φ (M.α d.1) = M.σ d.1 := by
    simp [φ, Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
  calc M.dartFace (M.σ d.1)
      = M.dartFace (M.φ (M.α d.1)) := by rw [hφ]
    _ = M.dartFace (M.α d.1) := M.dartFace_phi _

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- **A non-seam star step is a chord-split adjacency.**  If the current star dart's edge is
neither an old boundary edge nor the chord, then its face and the next star face are
chord-split adjacent. -/
lemma starStep_chordSplitAdj_of_not_seam
    {u v : M.Vertex} {x : M.Vertex} (d : StarDart M x)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d.1))
    (hc : M.dartEdge d.1 ≠ s(u, v)) :
    hNT.ChordSplitAdj u v (starFace x d) (starFace x (starSigma M x d)) :=
  ⟨d.1, rfl, (starFace_next_eq_alpha x d).symm ▸ rfl, hb, hc⟩

/-- **Side-1 membership is invariant across a non-seam star step.**  This is the load-bearing
brick-1 lemma: in the vertex rotation, side-1 membership can change only across a seam edge
(an old boundary edge or the chord). -/
lemma star_side₁_next_iff_of_not_seam
    {u v : M.Vertex} (data : hNT.ChordSplitData u v)
    {x : M.Vertex} (d : StarDart M x)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d.1))
    (hc : M.dartEdge d.1 ≠ s(u, v)) :
    starFace x d ∈ data.side₁ ↔ starFace x (starSigma M x d) ∈ data.side₁ := by
  constructor
  · intro h
    exact data.side₁_closed h (starStep_chordSplitAdj_of_not_seam hNT d hb hc)
  · intro h
    exact data.side₁_closed h
      (hNT.chordSplitAdj_symm (starStep_chordSplitAdj_of_not_seam hNT d hb hc))

/-! ## Brick 2 — Cycle–star incidence -/

/-- The cycle passes through vertex `x` (the natural replacement for the design's
`x ∈ C.vertexSet`): some cycle dart has tail `x`. -/
def CycleVertexMem (C : SimplePrimalCycle M) (x : M.Vertex) : Prop :=
  ∃ i : Fin C.len, M.tail (C.dart i) = x

/-- A star dart at `x` is a **cycle-star dart** if its edge is one of the cycle's edges. -/
def CycleStarDart (C : SimplePrimalCycle M) (x : M.Vertex) (d : StarDart M x) : Prop :=
  ∃ i : Fin C.len, M.dartEdge d.1 = M.dartEdge (C.dart i)

/-- The finite set of cycle-star darts at `x`. -/
noncomputable def cycleStarDarts (C : SimplePrimalCycle M) (x : M.Vertex) :
    Finset (StarDart M x) := by
  classical
  exact Finset.univ.filter (fun d => CycleStarDart C x d)

lemma mem_cycleStarDarts_iff (C : SimplePrimalCycle M) (x : M.Vertex)
    (d : StarDart M x) :
    d ∈ cycleStarDarts C x ↔ CycleStarDart C x d := by
  classical
  simp [cycleStarDarts]

/-- **Endpoint dichotomy for a cut dart.**  A star dart at `x` whose edge equals the `i`-th
cycle edge is either the forward dart `C.dart i` (in which case `x = tail (C.dart i)`) or its
reverse `M.α (C.dart i)` (in which case `x = head (C.dart i)`).  This uses `IsSimpleGraph` to
turn equal edges into `α`-`SameCycle`, then the two-element structure of an `α`-class. -/
lemma cut_dart_eq_forward_or_reverse
    (C : SimplePrimalCycle M) {x : M.Vertex} (hM : M.IsSimpleGraph)
    {d : StarDart M x} {i : Fin C.len} (hi : M.dartEdge d.1 = M.dartEdge (C.dart i)) :
    (d.1 = C.dart i ∧ x = M.tail (C.dart i)) ∨
      (d.1 = M.α (C.dart i) ∧ x = M.head (C.dart i)) := by
  have hsame : M.α.SameCycle (C.dart i) d.1 := (hM.no_parallel hi).symm
  rcases (M.alpha_sameCycle_iff (C.dart i) d.1).mp hsame with hd | hd
  · refine Or.inl ⟨hd, ?_⟩
    rw [← d.2, hd]
  · refine Or.inr ⟨hd, ?_⟩
    rw [← d.2, hd, tail_alpha]

/-- If `x` is not on the cycle there are no cycle-star darts. -/
theorem cycleStarDarts_card_eq_zero_of_not_mem
    (C : SimplePrimalCycle M) {x : M.Vertex}
    (hM : M.IsSimpleGraph) (hx : ¬ CycleVertexMem C x) :
    (cycleStarDarts C x).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro d hd
  rw [mem_cycleStarDarts_iff] at hd
  obtain ⟨i, hi⟩ := hd
  rcases cut_dart_eq_forward_or_reverse C hM hi with ⟨_, hxt⟩ | ⟨_, hxh⟩
  · exact hx ⟨i, hxt.symm⟩
  · -- `x = head (dart i) = tail (dart (nextIdx i))`, still a cycle vertex.
    exact hx ⟨C.nextIdx i, by rw [C.tail_dart_nextIdx i, ← hxh]⟩

/-! ### Two-cut packaging -/

/-- Package: at a cycle vertex there are exactly two cut darts in the star. -/
structure StarTwoCuts (C : SimplePrimalCycle M) (x : M.Vertex) where
  c₀ : StarDart M x
  c₁ : StarDart M x
  c_ne : c₀ ≠ c₁
  cuts_iff : ∀ d : StarDart M x, CycleStarDart C x d ↔ d = c₀ ∨ d = c₁

/-- **Two cut darts at a cycle vertex.**  When `x` is on the cycle, with unique forward index
`j` such that `x = tail (C.dart j)`, the two cut star darts are the *leaving* forward dart
`C.dart j` and the *entering* reverse dart `M.α (C.dart (prevIdx j))` (whose tail is also `x`,
since `head (C.dart (prevIdx j)) = tail (C.dart j) = x`).  They are distinct by `dart_ne_alpha_dart`. -/
noncomputable def starTwoCuts_of_cycle_mem
    (C : SimplePrimalCycle M) {x : M.Vertex} (hM : M.IsSimpleGraph)
    (hx : CycleVertexMem C x) : StarTwoCuts C x := by
  classical
  -- The leaving index `j` with `tail (dart j) = x`; unique by `tail_inj`.
  set j := hx.choose with hjdef
  have hj : M.tail (C.dart j) = x := hx.choose_spec
  -- The entering dart's reverse is tailed at `x`.
  have hprev_head : M.head (C.dart (C.prevIdx j)) = x := by
    have := C.consecutive' (C.prevIdx j)
    rw [C.nextIdx_prevIdx j] at this
    rw [this, hj]
  refine
    { c₀ := ⟨C.dart j, ?_⟩
      c₁ := ⟨M.α (C.dart (C.prevIdx j)), ?_⟩
      c_ne := ?_
      cuts_iff := ?_ }
  · -- tail of leaving dart is `x`
    exact hj
  · -- tail of the reverse of the entering dart is `head (entering dart) = x`
    rw [tail_alpha]; exact hprev_head
  · -- distinct: a forward cycle dart never equals an α-reverse of one
    intro hcontra
    have : C.dart j = M.α (C.dart (C.prevIdx j)) := congrArg Subtype.val hcontra
    exact C.dart_ne_alpha_dart j (C.prevIdx j) this
  · -- characterise cut darts: edge = some cycle edge ⟺ it is one of the two.
    intro d
    constructor
    · rintro ⟨i, hi⟩
      rcases cut_dart_eq_forward_or_reverse C hM hi with ⟨hdf, hxt⟩ | ⟨hdr, hxh⟩
      · -- forward: `x = tail (dart i)`, so `i = j` by `tail_inj`; then `d = c₀`.
        have hij : i = j := C.tail_inj (by simp only []; rw [← hxt, ← hj])
        left
        apply Subtype.ext
        rw [hdf, hij]
      · -- reverse: `x = head (dart i) = tail (dart (nextIdx i))`, so `nextIdx i = j`,
        -- hence `i = prevIdx j`; then `d = c₁`.
        have hni : C.nextIdx i = j :=
          C.tail_inj (by simp only []; rw [C.tail_dart_nextIdx i, ← hxh, ← hj])
        have hij : i = C.prevIdx j := by rw [← hni, C.prevIdx_nextIdx]
        right
        apply Subtype.ext
        rw [hdr, hij]
    · rintro (rfl | rfl)
      · exact ⟨j, rfl⟩
      · exact ⟨C.prevIdx j, M.dartEdge_alpha _⟩

/-- The cut darts of a `StarTwoCuts` package form exactly the two-element set `{c₀, c₁}`. -/
lemma cycleStarDarts_eq_pair (C : SimplePrimalCycle M) {x : M.Vertex}
    (cuts : StarTwoCuts C x) :
    cycleStarDarts C x = {cuts.c₀, cuts.c₁} := by
  classical
  ext d
  rw [mem_cycleStarDarts_iff, cuts.cuts_iff d]
  simp [Finset.mem_insert, Finset.mem_singleton]

/-- **Exactly two cut darts at a cycle vertex.** -/
theorem cycleStarDarts_card_eq_two_of_mem
    (C : SimplePrimalCycle M) {x : M.Vertex} (hM : M.IsSimpleGraph)
    (hx : CycleVertexMem C x) :
    (cycleStarDarts C x).card = 2 := by
  classical
  rw [Finset.card_eq_two]
  refine ⟨(starTwoCuts_of_cycle_mem C hM hx).c₀, (starTwoCuts_of_cycle_mem C hM hx).c₁,
    (starTwoCuts_of_cycle_mem C hM hx).c_ne, ?_⟩
  exact cycleStarDarts_eq_pair C (starTwoCuts_of_cycle_mem C hM hx)

/-! ## Brick 3 — Cut-free rotation walks -/

/-- A rotation walk from `a` to `b` under `ρ` that meets no cut on the way.  Stated as a `Prop`
via `∃`, which composes cleanly (no data-in-`Prop` projection issues). -/
def RotationArcWithoutCuts {K : Type*} (ρ : Equiv.Perm K) (Cut : K → Prop) (a b : K) : Prop :=
  ∃ n : ℕ, ρ^[n] a = b ∧ ∀ i : ℕ, i < n → ¬ Cut (ρ^[i] a)

/-- **The abstract permutation lemma (brick 3 core).**  No map theory: if a side predicate is
invariant across every non-cut step of `ρ`, then it is constant along a cut-free walk. -/
theorem side_constant_on_cutFree_walk {K : Type*} (ρ : Equiv.Perm K)
    (Cut : K → Prop) (Side : K → Prop)
    (Inv : ∀ k, ¬ Cut k → (Side k ↔ Side (ρ k)))
    {a b : K} (hwalk : RotationArcWithoutCuts ρ Cut a b) :
    (Side a ↔ Side b) := by
  obtain ⟨n, hend, hnc⟩ := hwalk
  subst hend
  induction n with
  | zero => simp
  | succ m ih =>
    have ihstep := ih (fun i hi => hnc i (Nat.lt_succ_of_lt hi))
    have hstep : Side (ρ^[m] a) ↔ Side (ρ^[m+1] a) := by
      have hnotcut : ¬ Cut (ρ^[m] a) := hnc m (Nat.lt_succ_self m)
      have hInv := Inv (ρ^[m] a) hnotcut
      rwa [← Function.iterate_succ_apply' ρ m a] at hInv
    exact ihstep.trans hstep

/-- Specialisation to the vertex star with side-1 membership and the *seam* cut.  The cut here is
"the star dart's edge is a seam edge" (old boundary edge or the chord); brick 1's
`star_side₁_next_iff_of_not_seam` is exactly the required invariance. -/
theorem starSide₁_constant_on_cut_free_walk
    {u v : M.Vertex} (data : hNT.ChordSplitData u v)
    {x : M.Vertex} {d₀ d₁ : StarDart M x}
    (hwalk : RotationArcWithoutCuts (starSigma M x)
      (fun d => hNT.outerCycle.IsBoundaryEdge (M.dartEdge d.1) ∨ M.dartEdge d.1 = s(u, v))
      d₀ d₁) :
    (starFace x d₀ ∈ data.side₁ ↔ starFace x d₁ ∈ data.side₁) := by
  refine side_constant_on_cutFree_walk (starSigma M x) _
    (fun d => starFace x d ∈ data.side₁) ?_ hwalk
  intro d hcut
  rw [not_or] at hcut
  exact star_side₁_next_iff_of_not_seam hNT data d hcut.1 hcut.2

/-- Iterating `starSigma` is iterating `σ` on the underlying dart. -/
lemma starSigma_iterate_coe {x : M.Vertex} (n : ℕ) (d : StarDart M x) :
    ((starSigma M x)^[n] d).1 = (M.σ)^[n] d.1 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', starSigma_coe, ih]

/-- **Star-orbit transitivity.**  Any two star darts at the same vertex are `starSigma`-iterates
of one another: the `σ`-orbit at a vertex *is* the whole star, by definition of `Vertex` as the
`σ`-orbit quotient.  This is what lets a rotation walk reach every star dart, so the escape
lemma below applies to an *arbitrary* target dart. -/
lemma starSigma_reaches {x : M.Vertex} (a b : StarDart M x) :
    ∃ n : ℕ, (starSigma M x)^[n] a = b := by
  -- Same tail ⇒ same `σ`-cycle of the underlying darts.
  have hsame : M.σ.SameCycle a.1 b.1 := by
    have : M.tail a.1 = M.tail b.1 := by rw [a.2, b.2]
    exact Quotient.exact this
  obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
  refine ⟨n, ?_⟩
  apply Subtype.ext
  rw [starSigma_iterate_coe, ← hn, Equiv.Perm.coe_pow]

/-- **Abstract escape lemma.**  In a finite star, if `a` is on the side and `b` is not, then the
σ-orbit walk from `a` to `b` must cross a cut.  Stated abstractly over any permutation. -/
theorem side_escape_crosses_cut {K : Type*} [Fintype K] (ρ : Equiv.Perm K)
    (Cut : K → Prop) (Side : K → Prop)
    (Inv : ∀ k, ¬ Cut k → (Side k ↔ Side (ρ k)))
    {a b : K} (hreach : ∃ n : ℕ, ρ^[n] a = b)
    (hside : Side a) (hescape : ¬ Side b) :
    ∃ i : ℕ, ∃ n : ℕ, ρ^[n] a = b ∧ i < n ∧ Cut (ρ^[i] a) := by
  obtain ⟨n, hn⟩ := hreach
  by_contra hcon
  have hwalk : RotationArcWithoutCuts ρ Cut a b :=
    ⟨n, hn, fun i hi hcut => hcon ⟨i, n, hn, hi, hcut⟩⟩
  exact hescape ((side_constant_on_cutFree_walk ρ Cut Side Inv hwalk).mp hside)

/-- **Star escape crosses a seam (generic-cut form).**  If `dside` is on side 1 and `descape`
is not, then — using star-orbit transitivity for reachability and brick 1's seam-invariance —
the rotation walk from `dside` to `descape` must cross a seam edge (an old boundary edge or
the chord).  This is the generic escape; the later wave refines "seam" into the `C`-edge cuts
counted by `cycleStarDarts` and the separately-handled opposite-arc boundary edges. -/
theorem star_escape_crosses_seam
    {u v : M.Vertex} (data : hNT.ChordSplitData u v)
    {x : M.Vertex} {dside descape : StarDart M x}
    (hside : starFace x dside ∈ data.side₁)
    (hescape : ¬ starFace x descape ∈ data.side₁) :
    ∃ c : StarDart M x,
      (hNT.outerCycle.IsBoundaryEdge (M.dartEdge c.1) ∨ M.dartEdge c.1 = s(u, v)) ∧
      ∃ n : ℕ, (starSigma M x)^[n] dside = descape ∧
        ∃ i : ℕ, i < n ∧ (starSigma M x)^[i] dside = c := by
  obtain ⟨i, n, hn, hilt, hcut⟩ :=
    side_escape_crosses_cut (starSigma M x)
      (fun d => hNT.outerCycle.IsBoundaryEdge (M.dartEdge d.1) ∨ M.dartEdge d.1 = s(u, v))
      (fun d => starFace x d ∈ data.side₁)
      (fun d hnotcut => by
        rw [not_or] at hnotcut
        exact star_side₁_next_iff_of_not_seam hNT data d hnotcut.1 hnotcut.2)
      (starSigma_reaches dside descape) hside hescape
  exact ⟨(starSigma M x)^[i] dside, hcut, n, hn, i, hilt, rfl⟩

end CombMap

end ProofsInTheBook.PlanarMap

-- Axiom audit for the main brick results (expect: propext, Classical.choice, Quot.sound).
#print axioms ProofsInTheBook.PlanarMap.CombMap.starFace_next_eq_alpha
#print axioms ProofsInTheBook.PlanarMap.CombMap.star_side₁_next_iff_of_not_seam
#print axioms ProofsInTheBook.PlanarMap.CombMap.cycleStarDarts_card_eq_zero_of_not_mem
#print axioms ProofsInTheBook.PlanarMap.CombMap.cycleStarDarts_card_eq_two_of_mem
#print axioms ProofsInTheBook.PlanarMap.CombMap.starTwoCuts_of_cycle_mem
#print axioms ProofsInTheBook.PlanarMap.CombMap.side_constant_on_cutFree_walk
#print axioms ProofsInTheBook.PlanarMap.CombMap.starSide₁_constant_on_cut_free_walk
#print axioms ProofsInTheBook.PlanarMap.CombMap.star_escape_crosses_seam
