import ProofsInTheBook.ZinanFFCT38

/-!
# `ZinanFFCT39` — the two headline `-δ` residuals of Chapter 13, audited.

`ZinanFFCT38` exposed the corrected `-δ` (widening) glue with a five-name residue surface, two of whose
names live in `ZinanFFCT38` itself:

* `OpenedEdgesDistinctW` — consecutive opened vertices of `A'_W = openTailW A K δ*_W` are distinct;
* `HemiMarginStrictPosAtSupW` — at a `StuckW` supremum the fixed-`h₀` hemisphere margin of `A'_W` is
  *strictly* `> 0` at every vertex.

This module carries out the honest reduction of both, **with the playbook §3.3 adversarial audit applied
to the consumer's demanded forms.** The audit turns up a load-bearing fact about *how* `ZinanFFCT38`
consumes the two names (`glueWClauseIII_of_residues`, line 289–298):

* `HemiMarginStrictPosAtSupW` is consumed as a *global* `Prop` quantified over **all** of `StuckW`,
  whose **hemi disjunct** is `∃ r, hemiMargin A K h₀ r (-δ*_W) = 0`, i.e. `⟪h₀, A'_W r⟫ = 0` at that
  vertex `r`.  But the conclusion of `HemiMarginStrictPosAtSupW` asserts `0 < ⟪h₀, A'_W r⟫` at **every**
  vertex.  At a hemi-stuck supremum these two are a direct contradiction, so the global Prop is
  **FALSE** (a proof of it would discharge `0 < x ∧ x = 0`).  We make this precise and unconditional in
  `hemiMarginStrictPosAtSupW_self_contradictory_on_hemiStuck`, and as the corollary
  `not_hemiMarginStrictPosAtSupW_of_hemiStuck_witness`.

* The `hdist` argument of `glueWClauseIII_of_residues` is `∀ {n} A B k h₀, OpenedEdgesDistinctW …`,
  i.e. opened-edge distinctness for **every** arm with **no** convexity / hemisphere / stuck premise.
  This too is **FALSE** (a constant arm `A ≡ p` has every opened edge degenerate), witnessed
  unconditionally by `not_openedEdgesDistinctW_constant`.

Neither falsity is a Lean unsoundness — `ZinanFFCT38.mainPlus_headline_final` is `clean-3` because it is
*conditional* on these two `Prop`s; the audit's content is that those two conditions are **unsatisfiable
as stated**, so the headline is, with the FFCT38 wiring, **vacuously conditional** on its clause-(iii)
half.  That is the §3.3 "VACUOUS conditional theorem via an unsatisfiable / false hypothesis" failure
mode, which `#print axioms` cannot see.

## What this module proves *positively* (the genuine, satisfiable content)

The salvageable, true statements — the ones a faithful clause-(iii) must rest on — are proved here in
full, with the **correct** hypotheses (strict convexity of `A`; for the closing edge, the genuine global
no-repeat input that the whole campaign carries as a named, satisfiable `Prop`):

* `openedEdgeDistinctW_fixed` — every *interior* opened edge `(i, i+1)` with both endpoints `≤ K`
  (head, fixed) is distinct, from `A`'s strict-convexity `edge_short`.  **Unconditional.**
* `openedEdgeDistinctW_tail` — every opened edge `(i, i+1)` with both endpoints `> K` (tail, rotated by
  the single isometry `rotS2 (A K) (-δ*_W)`) is distinct, from `A`'s `edge_short` + the rotation
  isometry `sDist_rotS2`.  **Unconditional.**
* `openedEdgeDistinctW_seam` — the seam edge `(K, K+1)` (axis fixed, successor rotated) is distinct, via
  the axis-fixing identity `rotS2 (A K) θ (A K) = A K` + `sDist_rotS2`.  **Unconditional.**
* `openedEdgesDistinctW_of_noRepeat` — the **full** `OpenedEdgesDistinctW A B k h₀` from strict
  convexity of `A` plus the campaign's standing no-repeat input
  `OpenedClosingEdgeDistinctW` (the single wraparound edge `(last, 0)` — the closure supports leave it
  open exactly as the `no_repeat` family documents, because two equal vertices give a `det3`-degenerate
  `= 0` support, consistent with the `≥ 0` closure).  This is the honest, satisfiable form of the
  residual; the FFCT38-demanded all-arms form is refuted above.

For `HemiMarginStrictPosAtSupW`, the positive content is `hemiMarginStrictPos_supportStuck` — strict
`h₀`-positivity at every vertex **in the support-stuck branch**, where the named-but-now-honest premise
is exactly that no `h₀`-margin vanishes (the support-stuck supremum, by definition, has all margins
`> 0` available; we expose it as `SupportStuckMarginsPos`, the satisfiable form), proved to imply the
per-vertex strictness.  The global all-of-`StuckW` form is refuted above.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38

namespace ProofsInTheBook.ZinanFFCT39

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §0. Axis-fixing of the spherical rotation (the seam ingredient). -/

/-- The spherical rotation fixes its axis vertex: `rotS2 k θ k = k`. -/
theorem rotS2_axis (k : S2) (θ : ℝ) : rotS2 k θ k = k := by
  apply S2.ext
  simp only [rotS2_coe]
  exact rot_axis k.2 θ

/-! ## §1. Brick 1 — opened-edge distinctness, the genuinely provable edges (unconditional).

`openTailW A K δ* = openTail A K (-δ*)` is `rfl`; we work with the opening angle `d := -δ*` throughout.
The base arm `A` is strictly convex, so its cyclic `edge_short` gives `A i ≠ A (i+1)` for **every**
`i : Fin (n+1)` (the polygon closure, including the wraparound). -/

/-- Base consecutive distinctness from strict convexity (cyclic, all `i`). -/
theorem base_consecutive_ne {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (i : Fin (n + 1)) : A i ≠ A (i + 1) :=
  (hA.closed_convex.edge_short i).1

/-- **(Brick 1, fixed edge.)**  If both endpoints of the opened edge `(i, i+1)` are at indices `≤ K`,
the edge is unchanged (`openTail` fixes `≤ K`), so its distinctness is the base distinctness. -/
theorem openedEdgeDistinctW_fixed {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (K : Fin (n + 1)) (d : ℝ) (i : Fin (n + 1))
    (hi : i.val ≤ K.val) (hi1 : (i + 1).val ≤ K.val) :
    openTail A K d i ≠ openTail A K d (i + 1) := by
  rw [openTail_fixed A K d hi, openTail_fixed A K d hi1]
  exact base_consecutive_ne hA i

/-- **(Brick 1, tail edge.)**  If both endpoints of the opened edge `(i, i+1)` are at indices `> K`,
both are rotated by the single isometry `rotS2 (A K) d`, which preserves spherical distance
(`sDist_rotS2`), so the edge is distinct iff the base edge is. -/
theorem openedEdgeDistinctW_tail {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (K : Fin (n + 1)) (d : ℝ) (i : Fin (n + 1))
    (hi : K.val < i.val) (hi1 : K.val < (i + 1).val) :
    openTail A K d i ≠ openTail A K d (i + 1) := by
  rw [openTail_rot A K d hi, openTail_rot A K d hi1]
  intro heq
  apply base_consecutive_ne hA i
  have hd : sDist (rotS2 (A K) d (A i)) (rotS2 (A K) d (A (i + 1))) = 0 := by
    rw [heq]; exact (sDist_eq_zero_iff).2 rfl
  rw [sDist_rotS2] at hd
  exact sDist_eq_zero_iff.1 hd

/-- **(Brick 1, seam edge.)**  The seam edge `(K, K+1)`: `openTail K = A K` (axis fixed) and
`openTail (K+1) = rotS2 (A K) d (A (K+1))`.  Equality would give
`rotS2 (A K) d (A K) = rotS2 (A K) d (A (K+1))` (using `rotS2_axis` to rewrite the fixed endpoint as the
rotation of the axis), hence `A K = A (K+1)` by the isometry — contradicting the base edge. -/
theorem openedEdgeDistinctW_seam {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (K : Fin (n + 1)) (d : ℝ) (i : Fin (n + 1))
    (hiK : i = K) (hi1 : K.val < (i + 1).val) :
    openTail A K d i ≠ openTail A K d (i + 1) := by
  subst hiK
  rw [openTail_axis A i d, openTail_rot A i d hi1]
  intro heq
  apply base_consecutive_ne hA i
  -- `heq : A i = rotS2 (A i) d (A (i+1))`.  Rewrite the LHS `A i` as `rotS2 (A i) d (A i)` (axis fixed),
  -- giving an equality of two rotations of the same isometry; cancel via `sDist_rotS2`.
  have heq2 : rotS2 (A i) d (A i) = rotS2 (A i) d (A (i + 1)) := by
    rw [rotS2_axis]; exact heq
  have hd : sDist (rotS2 (A i) d (A i)) (rotS2 (A i) d (A (i + 1))) = 0 :=
    sDist_eq_zero_iff.2 heq2
  rw [sDist_rotS2] at hd
  exact sDist_eq_zero_iff.1 hd

/-! ## §2. Brick 1 — the wraparound edge as the one honest sub-residual, and the full assembly.

The cyclic polygon has exactly two edges crossing the fixed/rotated partition at an interior axis `K`:
the **seam** `(K, K+1)` (handled in §1 by the axis-fixing trick) and the **wraparound** `(last, 0)`
(`openTail last = rotS2 (A K) d (A last)` rotated, `openTail 0 = A 0` fixed).  The wraparound is *not*
related to a base edge by the rotation isometry, and — crucially — it is **not** forced distinct by the
closure data: if `openTail last = openTail 0 =: v`, then every support `sOrient (openTail last)
(openTail 0) (openTail j) = sOrient v v (openTail j) = det3 v v · = 0`, which is `≥ 0`, *consistent* with
the closure.  So a repeated wraparound vertex is invisible to the `≥ 0` supports — exactly the
`no_repeat` family's global obstruction (`ch13-no-repeat-report.md`).  We isolate it as the single named,
satisfiable sub-residual. -/

/-- **The wraparound sub-residual.**  The single closing edge `(last, 0)` of the opened arm `A'_W` is
distinct.  This is the honest, *strictly smaller* remnant of `OpenedEdgesDistinctW`: §1 closes every
interior, tail, and seam edge unconditionally; only this one cyclic-closing edge requires the campaign's
standing global no-repeat content (the `≥ 0` supports leave a repeated wraparound vertex invisible).
Satisfiable (realised at `δ*_W = 0`, where it is the base `A last ≠ A 0`). -/
def OpenedClosingEdgeDistinctW {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) : Prop :=
  openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (Fin.last n)
    ≠ openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (Fin.last n + 1)

/-- **(Brick 1, full assembly.)**  `OpenedEdgesDistinctW A B k h₀` from strict convexity of `A` and the
single wraparound sub-residual `OpenedClosingEdgeDistinctW`.  Every non-closing edge is discharged
unconditionally by the §1 trichotomy on `i.val` versus `K.val`; the lone closing edge `i = last` is the
sub-residual. -/
theorem openedEdgesDistinctW_of_closing {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (k : Fin (n - 1)) (h₀ : E3)
    (hclose : OpenedClosingEdgeDistinctW A B k h₀) :
    OpenedEdgesDistinctW A B k h₀ := by
  classical
  set K : Fin (n + 1) := openingAxis k with hK
  set d : ℝ := -(monitoredSupW A B k h₀ Real.pi) with hd
  -- `openTailW A K δ* = openTail A K d` definitionally.
  have hAW : openTailW A K (monitoredSupW A B k h₀ Real.pi) = openTail A K d := rfl
  -- the axis is interior.
  obtain ⟨hK1, hKn⟩ := openingAxis_interior k
  have hKval : K.val < n := hKn
  intro i
  rw [hAW]
  -- split on whether `i` is the wraparound index.
  by_cases hlast : i = Fin.last n
  · -- the closing edge: the sub-residual (rewritten through `openTailW`/`openTail`).
    have := hclose
    rw [hlast]
    simpa only [openTailW, hK, hd] using this
  · -- `i.val < n`, so `(i+1).val = i.val + 1` (no wrap).
    have hival : i.val < n := by
      rcases Nat.lt_or_ge i.val n with h | h
      · exact h
      · exact absurd (Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)) hlast
    have hsucc : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add_one_of_lt]
      rwa [Fin.lt_def, Fin.val_last]
    rcases lt_trichotomy i.val K.val with hlt | heq | hgt
    · -- `i.val < K.val`: both `≤ K` (since `(i+1).val = i.val+1 ≤ K.val`), fixed edge.
      exact openedEdgeDistinctW_fixed hA K d i (le_of_lt hlt) (by rw [hsucc]; omega)
    · -- `i.val = K.val`: seam.
      exact openedEdgeDistinctW_seam hA K d i (Fin.ext heq) (by rw [hsucc]; omega)
    · -- `K.val < i.val`: tail (both `> K`).
      exact openedEdgeDistinctW_tail hA K d i hgt (by rw [hsucc]; omega)

/-! ## §3. Brick 1 — adversarial audit: the FFCT38-demanded *all-arms* form is FALSE.

`glueWClauseIII_of_residues` demands `hdist : ∀ {n} A B k h₀, OpenedEdgesDistinctW A B k h₀`, i.e.
opened-edge distinctness for **every** arm with no premise.  A constant arm refutes it. -/

/-- **Audit (anti-vacuity).**  `OpenedEdgesDistinctW` fails for a *constant* arm: every opened edge is
degenerate.  Hence the FFCT38 `hdist` hypothesis (the same `Prop` quantified over **all** arms with no
convexity premise) is unsatisfiable, so the headline that consumes it is vacuously conditional on its
clause-(iii) half. -/
theorem not_openedEdgesDistinctW_constant {n : ℕ} (p : S2) (B : Fin (n + 1) → S2) (k : Fin (n - 1))
    (h₀ : E3) : ¬ OpenedEdgesDistinctW (fun _ => p) B k h₀ := by
  intro h
  -- `openTailW (fun _ => p) K δ* i = p` for every `i` (every vertex is `p`, fixed or rotated).
  have hconst : ∀ i : Fin (n + 1),
      openTailW (fun _ => p) (openingAxis k) (monitoredSupW (fun _ => p) B k h₀ Real.pi) i = p := by
    intro i
    set K : Fin (n + 1) := openingAxis k
    set d : ℝ := -(monitoredSupW (fun _ => p) B k h₀ Real.pi)
    show openTail (fun _ => p) K d i = p
    by_cases hi : i.val ≤ K.val
    · rw [openTail_fixed _ K d hi]
    · rw [openTail_rot _ K d (by omega)]
      -- `rotS2 ((fun _ => p) K) d ((fun _ => p) i) = rotS2 p d p = p` (axis fixed).
      exact rotS2_axis p d
  exact (h 0) ((hconst 0).trans (hconst (0 + 1)).symm)

/-! ## §4. Brick 2 — the strict-hemi residual, audited.

`HemiMarginStrictPosAtSupW` is consumed (FFCT38 `glueWClauseIII_of_residues`) as a *global* `Prop`
quantified over all of `StuckW`.  `StuckW`'s **hemi** disjunct is `∃ r, hemiMargin A K h₀ r (-δ*_W) = 0`,
i.e. `⟪h₀, A'_W r⟫ = 0`; the conclusion of `HemiMarginStrictPosAtSupW` asserts `0 < ⟪h₀, A'_W r⟫` at
every vertex.  These contradict, so the global Prop is **false** on the hemi branch. -/

/-- **Audit (self-contradiction on the hemi branch).**  Suppose `HemiMarginStrictPosAtSupW` holds, and
suppose at some configuration `StuckW` holds via its **hemi** disjunct — a vanishing `h₀`-margin at a
vertex `r`.  Then `HemiMarginStrictPosAtSupW` forces `0 < ⟪h₀, A'_W r⟫` while the hemi-stuck datum is
`⟪h₀, A'_W r⟫ = 0`: a contradiction.  Thus `HemiMarginStrictPosAtSupW` is **incompatible** with any
hemi-stuck supremum — it is false exactly where `StuckW`'s hemi disjunct is realised. -/
theorem hemiMarginStrictPosAtSupW_self_contradictory_on_hemiStuck
    (hhem : HemiMarginStrictPosAtSupW)
    {n : ℕ} (A B : Fin (n + 1) → S2) (hA : StrictConvexSphArm A) (k : Fin (n - 1)) (h₀ : E3)
    (hnorm : ‖h₀‖ = 1) (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (r : Fin (n + 1))
    (hmargin0 : hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Real.pi)) = 0) :
    False := by
  -- `StuckW` via the hemi disjunct at `r`.
  have hstuck : StuckW A B k h₀ Real.pi := Or.inr ⟨r, hmargin0⟩
  -- the strict positivity at `r` from the global residual.
  have hpos : 0 < (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2)
      : E3)⟫ : ℝ) := hhem n A B hA k h₀ hnorm hhpos hstuck r
  -- but the hemi-stuck datum says that very inner product is `0`.
  have hval : hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Real.pi))
      = (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ) := by
    simp only [hemiMargin, openTailW]
  rw [hval] at hmargin0
  linarith

/-- **Audit corollary.**  If *any* configuration realises `StuckW`'s hemi disjunct (a vanishing
`h₀`-margin at the supremum), then `HemiMarginStrictPosAtSupW` is **false**.  This is the precise sense
in which the FFCT38 clause-(iii) residual, as demanded, is unsatisfiable: the hemi branch of `StuckW`
(a genuine disjunct of the boundary trichotomy `opening_boundary_trichotomyW`) is exactly its negation.
-/
theorem not_hemiMarginStrictPosAtSupW_of_hemiStuck_witness
    {n : ℕ} (A B : Fin (n + 1) → S2) (hA : StrictConvexSphArm A) (k : Fin (n - 1)) (h₀ : E3)
    (hnorm : ‖h₀‖ = 1) (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (r : Fin (n + 1))
    (hmargin0 : hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Real.pi)) = 0) :
    ¬ HemiMarginStrictPosAtSupW := fun hhem =>
  hemiMarginStrictPosAtSupW_self_contradictory_on_hemiStuck hhem A B hA k h₀ hnorm hhpos r hmargin0

/-! ## §5. Brick 2 — the genuine, satisfiable positive content (support-stuck branch).

The salvageable truth: in the **support-stuck** branch (a non-incident support vanishes; the hemisphere
margins need not), the fixed-`h₀` strict positivity at every vertex is exactly the statement that no
`h₀`-margin vanishes at the supremum.  The closure (`hemiMarginW_nonneg_at_sup`) gives `≥ 0`; the strict
`> 0` is the honest residual — but now correctly *scoped to the support branch*, where it is a genuine
geometric fact (the opened arm stays in the open hemisphere of `h₀`) rather than a self-contradiction.
We expose it as the satisfiable premise `SupportStuckMarginsPos` and prove it yields the per-vertex
strictness `ZinanFFCT38.stuckOutcomeW_of_supportVanish` consumes. -/

/-- The honest support-branch hemi premise: at the support-stuck supremum no `h₀`-margin vanishes.
Together with the closure `≥ 0` this is the strict per-vertex positivity.  Satisfiable (realised at
`δ*_W = 0`, the unopened arm, by `A`'s `open_hemisphere` at `h₀`). -/
def SupportStuckMarginsPos {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) : Prop :=
  ∀ r : Fin (n + 1),
    hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Real.pi)) ≠ 0

/-- **(Brick 2, positive content.)**  From the closure `≥ 0` hemi margins
(`ZinanFFCT38.hemiMarginW_nonneg_at_sup`) and the honest non-vanishing premise `SupportStuckMarginsPos`,
the fixed-`h₀` margin is *strictly* `> 0` at every vertex of `A'_W` — the exact per-vertex shape
`stuckOutcomeW_of_supportVanish` / `weakConvex_of_supportStuck_of_hemiPos` consume. -/
theorem hemiMarginStrictPos_supportStuck {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hpos : SupportStuckMarginsPos A B k h₀) :
    ∀ r : Fin (n + 1),
      0 < (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ) := by
  intro r
  -- closure: `≥ 0`.
  have hge : 0 ≤ (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2)
      : E3)⟫ : ℝ) := hemiW_inner_nonneg hka hkt h0 r
  -- non-vanishing: `≠ 0` (the support-branch premise, in the inner-product form).
  have hne : (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ)
      ≠ 0 := by
    have := hpos r
    -- `hemiMargin … r (-δ*) = ⟪h₀, A'_W r⟫`.
    have hval : hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Real.pi))
        = (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ) := by
      simp only [hemiMargin, openTailW]
    rwa [hval] at this
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-! ## §6. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `OpenedClosingEdgeDistinctW`: realised at `δ*_W = 0`, where it is the base
distinctness `A last ≠ A (last + 1)` (the polygon's closing edge), real geometric content. -/
theorem openedClosingEdgeDistinctW_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (i : Fin (n + 1)) (hne : openTailW A K 0 i ≠ openTailW A K 0 (i + 1)) :
    A i ≠ A (i + 1) := by rwa [openTailW_zero] at hne

/-- Non-vacuity of `SupportStuckMarginsPos`: at `δ*_W = 0` it is `⟪h₀, A r⟫ ≠ 0`, which holds for an arm
strictly inside the `h₀`-hemisphere — real geometric content, not `True`. -/
theorem supportStuckMarginsPos_nonvacuous {n : ℕ} {A : Fin (n + 1) → S2} {K : Fin (n + 1)} {h₀ : E3}
    (r : Fin (n + 1)) (hpos : 0 < (⟪h₀, (A r : E3)⟫ : ℝ)) :
    hemiMargin A K h₀ r 0 ≠ 0 := by
  rw [hemiMargin_zero]; exact ne_of_gt hpos

/-- Non-vacuity sanity: the strict positivity is a real inequality, realised at the unopened arm. -/
theorem hemiMarginStrictPos_supportStuck_conclusion_real {n : ℕ} {A : Fin (n + 1) → S2}
    {K : Fin (n + 1)} {h₀ : E3} (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (r : Fin (n + 1)) : 0 < (⟪h₀, ((openTailW A K 0 r : S2) : E3)⟫ : ℝ) := by
  rw [openTailW_zero]; exact hhpos r

end ProofsInTheBook.ZinanFFCT39

-- Brick 1 (positive content + assembly + audit)
#print axioms ProofsInTheBook.ZinanFFCT39.openedEdgeDistinctW_fixed
#print axioms ProofsInTheBook.ZinanFFCT39.openedEdgeDistinctW_tail
#print axioms ProofsInTheBook.ZinanFFCT39.openedEdgeDistinctW_seam
#print axioms ProofsInTheBook.ZinanFFCT39.openedEdgesDistinctW_of_closing
#print axioms ProofsInTheBook.ZinanFFCT39.not_openedEdgesDistinctW_constant
-- Brick 2 (audit + positive content)
#print axioms ProofsInTheBook.ZinanFFCT39.hemiMarginStrictPosAtSupW_self_contradictory_on_hemiStuck
#print axioms ProofsInTheBook.ZinanFFCT39.not_hemiMarginStrictPosAtSupW_of_hemiStuck_witness
#print axioms ProofsInTheBook.ZinanFFCT39.hemiMarginStrictPos_supportStuck
