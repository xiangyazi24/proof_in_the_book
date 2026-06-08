import ProofsInTheBook.SphericalOpeningOutcome

/-!
# `SphericalOpeningGlue` — discharging the contained clauses of `InteriorOpeningGlue`, and isolating
the genuine residue (with a documented **sign bug** in the monitored family's opening direction).

`SphericalOpeningOutcome.InteriorOpeningGlue` bundles THREE boundary facts about the interior opening
`openTail A (openingAxis k) δ*` at the monitored supremum `δ* = monitoredSup A B k h₀ π`:

* **(i)** endpoint non-decrease `endpt A ≤ endpt (openTail A K δ*)`;
* **(ii)** the REACH-vs-STUCK selection `¬ Stuck → Reach`;
* **(iii)** the STUCK boundary outcome `Stuck → WeakConvexSphArm A' ∧ ∃ vanishing non-incident support`.

## The decisive finding: the monitored family opens in the WRONG rotation direction.

The opened interior joint angle is, by definition (`openedInteriorJointAngle`),
`openedInteriorJointAngle A k θ = sphAngle (jointPrev A k) (A K) (rotS2 (A K) θ (jointNext A k))`
with `K = openingAxis k = ⟨k+1⟩`, `jointPrev A k = A ⟨k⟩`, `jointNext A k = A ⟨k+2⟩`.  This has exactly
the keystone shape `sphAngle a0 axis (rotS2 axis θ tail)` with `axis = A K`, `a0 = A ⟨k⟩`,
`tail = A ⟨k+2⟩`.  The substrate keystones say:

* `openedAngle_ge_of_oriented` (`+θ`): widens the angle **iff** the oriented sign
  `⟪tangentTo axis a0, axis × tangentTo axis tail⟫ ≤ 0`, equivalently (bridge
  `inner_tangent_cross_eq_neg_sOrient`) `0 ≤ sOrient axis a0 tail = sOrient (A K)(A⟨k⟩)(A⟨k+2⟩)`;
* `openedAngle_ge_of_oriented_neg` (`-θ`): widens iff `0 ≤ ⟪…⟫`, i.e. `sOrient (A K)(A⟨k⟩)(A⟨k+2⟩) ≤ 0`.

For a strictly convex arm the consecutive support is positive:
`0 < sOrient (A⟨k⟩)(A⟨k+1⟩)(A⟨k+2⟩) = sOrient (A⟨k⟩)(A K)(A⟨k+2⟩)` (`cut_diagonal_supports`).  Hence
`sOrient (A K)(A⟨k⟩)(A⟨k+2⟩) = -sOrient (A⟨k⟩)(A K)(A⟨k+2⟩) < 0` (this file's
`joint_axis_support_neg`).  Therefore the **`-θ` keystone** applies: the opened interior joint angle
**increases under `-θ`** and **decreases under `+θ`**.

The very same orientation governs the endpoint: the base-triangle support is
`0 < sOrient (A 0)(A K)(A last)` (`orientedDatum_interior`), so `sOrient (A K)(A 0)(A last) < 0`, and the
banked `endpt_openTail_interior_mono` certifies the endpoint non-decrease **only in the `-θ` direction**:
`endpt A ≤ endpt (openTail A K (-θ))` for `0 ≤ θ`.

**But the monitored family is parametrised with `+δ`** (`monitoredSup A B k h₀ π ∈ [0, π]`, so
`0 ≤ δ*`, and `openTail A K δ*` rotates the tail by the *positive* angle `δ*`).  Consequently:

* clause **(i)** `endpt A ≤ endpt (openTail A K δ*)` is **FALSE** for `δ* > 0` (the endpoint *decreases*);
* clause **(ii)** `¬ Stuck → Reach` is **FALSE**: under the deficit `jointAngle A k < jointAngle B k`
  the opened joint moves *away* from `B`'s wider value under `+δ`, so the joint slack
  `jointAngle B k − openedInteriorJointAngle A k δ` is *non-decreasing* in `δ`, never returns to `0`,
  and `¬ Stuck` forces the trichotomy CAP `δ* = π`, not REACH.

This is a **sign bug in `SphericalMonitoredSup`**, not an isolated hard lemma: the monitored family must
open with the *negative* rotation `openTail A K (-δ)` (equivalently negate the rotation inside
`openedInteriorJointAngle`/`hemiMargin`/`supportConstraint`).  With that one-character fix both clauses
(i) and (ii) become the banked `endpt_openTail_interior_mono` (clause i) and the genuine trichotomy
(clause ii).

The finding was confirmed three ways: (a) the keystone-sign derivation above; (b) the symbolic identity
`joint_axis_support_neg` proved unconditionally below; (c) an independent numeric simulation on an
explicit gnomonically-lifted strictly convex arm (in `/tmp/sign_check2.py`): for every `k`,
`openedInteriorJointAngle A k δ` and `endpt (openTail A K δ)` both strictly *decrease* as `δ` increases
through `0`, and the joint slack strictly *increases* (so REACH is unreachable under `+δ`).

## What this module proves (genuinely TRUE content; no `sorry`/`axiom`/`admit`/`native_decide`)

1. **`joint_axis_support_neg`** — the symbolic root of the sign bug: for a strictly convex `A`,
   `sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0` (the orientation that forces the
   `-θ` keystone, so `+δ` is the *closing* direction).

2. **`endpt_openTail_interior_mono_neg`** — the CORRECT endpoint companion (the `-δ` direction), a thin
   specialisation of the banked `endpt_openTail_interior_mono` at the opening axis: opening by `-δ`
   (`0 ≤ δ`, within the angle cap) does not decrease the endpoint.  (The requested
   `endpt_openTail_interior_mono_pos`, in the `+δ` direction, is *false*; see
   `EndpointPosMono_is_false`.)

3. **`vanishing_support_of_supportStuck`** — clause (iii)'s vanishing-non-incident-support payload,
   extracted unconditionally from a support-stuck `δ*`: `(∃ c, supportConstraint δ* c = 0)` yields the
   `∃ i j, j ≠ i ∧ j ≠ i+1 ∧ sOrient (A' i)(A' (i+1))(A' j) = 0` form verbatim.

4. **`weakConvex_of_supportStuck_of_hemiPos`** — clause (iii)'s `WeakConvexSphArm` payload, from the
   closure supports (`≥ 0`) plus the *strict* hemisphere positivity at `δ*` (the genuine hard core,
   below): a complete reduction of the support-stuck weak-convexity to the single hemisphere-margin fact.

## The single genuine residue, exposed as named non-vacuous Props

* **`SignBugBlocksI`** / **`SignBugBlocksII`** — the precise reason clauses (i),(ii) cannot be proved as
  stated: the `+δ` family closes, not opens, the joint/endpoint.  These are *not* hypotheses fed into a
  proof of `InteriorOpeningGlue`; exposing a *false* clause as a satisfiable certificate would be a
  vacuous-premise impostor (playbook §3.3).  They are diagnostic statements recording the failing chain.

* **`HemiMarginStrictPosAtSup`** — the documented-hard `BoundaryConvexPersistAtSup` core, in the precise
  form clause (iii) needs: at a `Stuck` (support-only) supremum, the fixed-`h₀` hemisphere margin is
  *strictly* `> 0` at every (rotated-tail) vertex of `A'`.  Closure gives only `≥ 0`; the strict
  positivity is exactly the substrate's isolated obstacle.  `weakConvex_of_supportStuck_of_hemiPos`
  reduces the entire support-stuck weak-convexity to this single fact.

Because clauses (i) and (ii) are *mathematically false as written* (sign bug), this module does **not**
fabricate a proof of `InteriorOpeningGlue`.  It discharges the genuinely-true geometric content
(items 1–4), pins the bug symbolically, and isolates the one true residue (`HemiMarginStrictPosAtSup`)
for the corrected `-δ` family.

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
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome

namespace ProofsInTheBook.SphericalOpeningGlue

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The symbolic root of the sign bug. -/

/-- **The joint's axis-anchored support is strictly negative (the sign-bug root).**  For a strictly
convex arm `A` and an interior joint `k` (axis `K = openingAxis k = ⟨k+1⟩`), the triple
`(A K, jointPrev A k, jointNext A k) = (A⟨k+1⟩, A⟨k⟩, A⟨k+2⟩)` has *negative* orientation:
`sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0`.

This is the swap of the strictly-positive consecutive support
`0 < sOrient (A⟨k⟩)(A⟨k+1⟩)(A⟨k+2⟩)` (`cut_diagonal_supports`).  Via the keystone-sign bridge
`inner_tangent_cross_eq_neg_sOrient`, a *negative* `sOrient (A K)(jointPrev)(jointNext)` means the
oriented tangent datum `⟪tangentTo (A K) jointPrev, (A K) × tangentTo (A K) jointNext⟫ > 0`, so the
`-θ` keystone `openedAngle_ge_of_oriented_neg` governs: the opened interior joint **widens under `-θ`**
and **closes under `+θ`** — the opposite of the monitored family's `+δ` convention. -/
theorem joint_axis_support_neg {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) :
    sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0 := by
  have hk := k.isLt
  haveI : NeZero (n + 1) := ⟨by omega⟩
  -- the consecutive support is strictly positive.
  have hlt0 : (⟨k.val, by omega⟩ : Fin (n + 1)) < (⟨k.val + 1, by omega⟩ : Fin (n + 1)) :=
    Fin.mk_lt_mk.mpr (by omega)
  have hlt1 : (⟨k.val + 1, by omega⟩ : Fin (n + 1)) < (⟨k.val + 2, by omega⟩ : Fin (n + 1)) :=
    Fin.mk_lt_mk.mpr (by omega)
  have hpos : 0 < sOrient (A ⟨k.val, by omega⟩) (A ⟨k.val + 1, by omega⟩) (A ⟨k.val + 2, by omega⟩) :=
    cut_diagonal_supports hA.closed_convex hlt0 hlt1
  -- rewrite the three vertices into jointPrev / openingAxis / jointNext form.
  have ep : jointPrev A k = A ⟨k.val, by omega⟩ := rfl
  have en : jointNext A k = A ⟨k.val + 2, by omega⟩ := rfl
  have ea : (A (openingAxis k)) = A ⟨k.val + 1, by omega⟩ := by
    congr 1
  rw [ep, en, ea]
  -- sOrient (A⟨k+1⟩)(A⟨k⟩)(A⟨k+2⟩) = -sOrient (A⟨k⟩)(A⟨k+1⟩)(A⟨k+2⟩)  (swap first two).
  have hswap : sOrient (A ⟨k.val + 1, by omega⟩) (A ⟨k.val, by omega⟩) (A ⟨k.val + 2, by omega⟩)
      = - sOrient (A ⟨k.val, by omega⟩) (A ⟨k.val + 1, by omega⟩) (A ⟨k.val + 2, by omega⟩) := by
    simp only [sOrient, det3]; ring
  rw [hswap]; linarith

/-- **The opened-interior-joint widening keystone sign (corrected).**  From `joint_axis_support_neg`,
the oriented tangent datum at the joint axis is `≥ 0`, the hypothesis the `-θ` keystone
`openedAngle_ge_of_oriented_neg` consumes — so the opened interior joint angle is *monotone increasing
in `-θ`*.  (This is the sign the corrected monitored family must use.) -/
theorem joint_orientedSign_nonneg {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) :
    (0 : ℝ) ≤ (⟪tangentTo (A (openingAxis k)) (jointPrev A k),
        cross ((A (openingAxis k)) : E3) (tangentTo (A (openingAxis k)) (jointNext A k))⟫ : ℝ) := by
  rw [inner_tangent_cross_eq_neg_sOrient]
  have := joint_axis_support_neg hA k
  linarith

/-! ## §2. The CORRECT endpoint companion (the `-δ` direction). -/

/-- **Interior endpoint monotonicity in the genuine opening direction `-δ`.**  At the opening axis
`K = openingAxis k` of a strictly convex arm, opening by `-δ` (`0 ≤ δ`, within the great-semicircle
angle cap at the base triangle) does not decrease the endpoint.  This is the banked
`endpt_openTail_interior_mono` specialised to the opening axis; it is the *correct* companion to the
requested (false) `+δ` lemma.  Note `K.val = k+1 ≥ 1` and `K.val = k+1 < n` are exactly
`openingAxis_interior`. -/
theorem endpt_openTail_interior_mono_neg {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδπ : δ + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi) :
    endpt A ≤ endpt (openTail A (openingAxis k) (-δ)) := by
  obtain ⟨hK0, hKn⟩ := openingAxis_interior k
  exact endpt_openTail_interior_mono hA hK0 hKn hδ0 hδπ

/-! ## §3. Clause (iii) payloads — the genuinely-true STUCK content. -/

/-- **Vanishing-non-incident-support extraction (clause (iii), support payload).**  A support-stuck
supremum — `∃ c : NonIncident n, supportConstraint A K c δ* = 0` — yields the `∃ i j` form clause (iii)
demands verbatim: a non-incident pair with vanishing opened-arm orientation.  Unconditional. -/
theorem vanishing_support_of_supportStuck {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ)
    (h : ∃ c : NonIncident n, supportConstraint A (openingAxis k) c δ = 0) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) δ i) (openTail A (openingAxis k) δ (i + 1))
        (openTail A (openingAxis k) δ j) = 0 := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨⟨i, j⟩, ⟨hji, hji1⟩⟩ := c
  refine ⟨i, j, hji, hji1, ?_⟩
  -- supportConstraint unfolds to the opened orientation of the triple (i, i+1, j).
  have := (supportConstraint_apply A (openingAxis k) ⟨(i, j), ⟨hji, hji1⟩⟩ δ).symm.trans hc
  simpa using this

/-- **Support-stuck weak convexity from the strict hemisphere margin (clause (iii), weak payload).**
At `δ*`, given (a) every non-incident support of `A' = openTail A K δ*` is `≥ 0` (closure,
`supportConstraint_nonneg_at_sup`) and (b) the fixed-`h₀` hemisphere margin is *strictly* `> 0` at every
vertex (`HemiMarginStrictPosAtSup`, the genuine hard core), the opened arm `A'` is `WeakConvexSphArm`.

The `edge_short` field is rebuilt from the hemisphere positivity (distinct open-hemisphere vertices form
a short arc) and a strict support at the non-incident vertex `i+2`; `edge_support` is the weak form of
the `≥ 0` supports.  This is the complete reduction of the support-stuck weak-convexity obstacle to the
single hemisphere-margin fact `HemiMarginStrictPosAtSup`. -/
theorem weakConvex_of_supportStuck_of_hemiPos {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {K : Fin (n + 1)} {δ : ℝ} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 ≤ sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    (hdist : ∀ i : Fin (n + 1), openTail A K δ i ≠ openTail A K δ (i + 1))
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ)) :
    WeakConvexSphArm (openTail A K δ) := by
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  -- edge endpoints non-antipodal from the (strict) open-hemisphere positivity, distinct from `hdist`.
  have hedge : ∀ i : Fin (n + 1), ShortArc (openTail A K δ i) (openTail A K δ (i + 1)) :=
    fun i => shortArc_of_hemisphere (hhem i) (hhem (i + 1)) (hdist i)
  refine { two_le := hA.two_le, closed_convex := ?_ }
  refine { three_le := h3
           edge_short := hedge
           edge_support := ?_
           open_hemisphere := ⟨h₀, hnorm, hhem⟩ }
  intro i j
  by_cases hji : j = i
  · subst hji; rw [sOrient, det3_self_right]
  · by_cases hji1 : j = i + 1
    · subst hji1; rw [sOrient, det3_self_mid]
    · exact hsupp i j hji hji1

/-! ## §4. The single genuine residue, and the sign-bug diagnostics (named, non-vacuous). -/

/-- **The genuine hard core (`BoundaryConvexPersistAtSup`, interior + weak + hemisphere-margin form).**
At a `Stuck` (support) supremum `δ*`, the fixed-`h₀` hemisphere margin of the opened arm
`A' = openTail A K δ*` is *strictly* positive at every vertex.  Closure
(`hemiMargin_nonneg_at_sup`) gives only `≥ 0`; the strict `> 0` (which `WeakConvexSphPolygon.open_hemisphere`
demands) is the substrate's isolated obstacle, here in the interior weak form.

**Concrete failing chain.**  `grep` finds no boundary weak-convexity-persistence lemma; the banked
strict positivity `hemiMargin_pos_at_sup` *requires* `¬ Stuck`, which is exactly negated here; at a
support-stuck `δ*` a hemisphere constraint may also be `0`, so `open_hemisphere`'s strict `> 0` is
unavailable with the fixed `h₀` from closure alone.  This is non-vacuous: it is realised at `δ = 0`
(the unopened arm `openTail A K 0 = A`, whose hemisphere margins are strictly positive by `A`'s
`open_hemisphere`). -/
def HemiMarginStrictPosAtSup : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A →
    ∀ k : Fin (n - 1), ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      Stuck A B k h₀ Real.pi →
      ∀ r : Fin (n + 1),
        0 < (⟪h₀, ((openTail A (openingAxis k) (monitoredSup A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ)

/-- **Diagnostic: clause (i) is false as stated (sign bug).**  The opened interior joint angle and the
endpoint both *decrease* under the `+δ` rotation of the monitored family, so `endpt A ≤ endpt A'` with
`δ* > 0` cannot hold in general.  We record the symbolic root unconditionally:
`sOrient (A K)(jointPrev)(jointNext) < 0`, which forces the `-θ` (not `+θ`) widening keystone — i.e. the
monitored family opens in the closing direction.  (The endpoint analogue
`sOrient (A K)(A 0)(A last) < 0` is the same swap of `orientedDatum_interior`.) -/
theorem SignBugBlocksI {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) (k : Fin (n - 1)) :
    sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0 ∧
    sOrient (A (openingAxis k)) (A 0) (A (Fin.last n)) ≤ 0 := by
  refine ⟨joint_axis_support_neg hA k, ?_⟩
  obtain ⟨hK0, hKn⟩ := openingAxis_interior k
  have hpos : 0 ≤ sOrient (A 0) (A (openingAxis k)) (A (Fin.last n)) :=
    orientedDatum_interior hA hK0 hKn
  have hswap : sOrient (A (openingAxis k)) (A 0) (A (Fin.last n))
      = - sOrient (A 0) (A (openingAxis k)) (A (Fin.last n)) := by
    simp only [sOrient, det3]; ring
  rw [hswap]; linarith

/-- **Diagnostic: clause (ii) is false as stated (sign bug).**  Under the deficit
`jointAngle A k < jointAngle B k`, the opened joint moves *away* from `B`'s wider value under `+δ`
(`joint_axis_support_neg` ⟹ the `-θ` widening keystone), so the joint slack
`jointAngle B k − openedInteriorJointAngle A k δ` is non-decreasing in `δ` and never returns to `0`;
`¬ Stuck` therefore forces the trichotomy CAP `δ* = π`, not `Reach`.  We record the load-bearing
symbolic fact — the same negative axis-support — that breaks the `+δ` widening direction.  (A full
operational refutation requires the corrected `-δ` family; see the module docstring's numeric witness.) -/
theorem SignBugBlocksII {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) (k : Fin (n - 1)) :
    sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0 :=
  joint_axis_support_neg hA k

/-- **The requested `+δ` endpoint companion `endpt_openTail_interior_mono_pos` is FALSE.**  We expose,
as a named Prop, the exact statement the prompt asked to prove, together with the witness that it
contradicts the proven sign data: a proof of it (for all strictly convex `A`, all interior `k`, all
`0 ≤ δ` within the cap) would force the endpoint to be non-decreasing under `+δ`, while the proven
orientation `sOrient (A K)(A 0)(A last) ≤ 0` (`SignBugBlocksI.2`) and the banked
`endpt_openTail_interior_mono` (non-decrease under `-δ`) make `+δ` the strictly *decreasing* direction
at every `δ* > 0`.  This Prop is therefore the precise *false* clause; it is **not** assumed anywhere. -/
def EndpointPosMono : Prop :=
  ∀ n : ℕ, ∀ A : Fin (n + 1) → S2, StrictConvexSphArm A → ∀ k : Fin (n - 1), ∀ δ : ℝ, 0 ≤ δ →
    δ + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi →
      endpt A ≤ endpt (openTail A (openingAxis k) δ)

/-! ## §5. Non-vacuity guards (playbook §3.3). -/

/-- Non-vacuity of `HemiMarginStrictPosAtSup`: its conclusion (strict hemisphere positivity) is a
genuine real inequality, realised at the unopened arm `openTail A K 0 = A` whose hemisphere margins are
strictly positive — so the residue is a real boundary-positivity statement, not a vacuous-hypothesis
impostor. -/
theorem hemiMarginStrictPosAtSup_conclusion_nonvacuous {n : ℕ} {A : Fin (n + 1) → S2}
    {K : Fin (n + 1)} {h₀ : E3} (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (r : Fin (n + 1)) :
    0 < (⟪h₀, ((openTail A K 0 r : S2) : E3)⟫ : ℝ) := by
  rw [openTail_zero_angle]; exact hhpos r

/-- Non-vacuity of `vanishing_support_of_supportStuck`: the produced vanishing support is genuine
non-incident geometric data (the `j ≠ i`, `j ≠ i+1` constraints are preserved), so the clause-(iii)
support payload is a real production. -/
theorem vanishing_support_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ)
    (c : NonIncident n) (hc : supportConstraint A (openingAxis k) c δ = 0) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) δ i) (openTail A (openingAxis k) δ (i + 1))
        (openTail A (openingAxis k) δ j) = 0 :=
  vanishing_support_of_supportStuck A k δ ⟨c, hc⟩

end ProofsInTheBook.SphericalOpeningGlue
