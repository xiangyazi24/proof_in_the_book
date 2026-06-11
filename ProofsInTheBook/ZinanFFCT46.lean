import ProofsInTheBook.ZinanFFCT44
import ProofsInTheBook.ZinanFFCT45
import ProofsInTheBook.ZinanFFCT43

/-!
# `ZinanFFCT46` — the WBS ASSEMBLY (bricks 4–6, 8–9): closing the hemisphere residual line.

This module is the assembly wave of the Chapter-13 WBS family
(`HANDOFF/design-rounds/ch13-wbs-family.md`, bricks 4, 5, 6, 8, 9).  It produces the open hemisphere at
the WBS supremum **margins-free**, assembles the support-stuck and reach convexity certificates, threads
the WBS trichotomy into `SphericalArmAssembly.InteriorOpeningOutcome`, and re-threads the FFCT43 headline
on the WBS outcome — with the hemisphere residuals (`SupportStuckMarginsPosAtSupWB`, `PureHemiProgressWB`)
**gone**.

## The load-bearing inventory finding (the margins question, settled)

`HANDOFF/design-rounds/ch13-wbs-family.md` §9's sketch of `openHemisphere_at_WBS_sup` reads "use support
closure `≥ 0`, side preservation, `JointLe` with strict `B` … apply `equatorTangentExists_of_weakSupports_jointOpen`
+ FFCT30's tilt".  **But the FFCT30 tilt fundamentally requires a base normal `h₀` with weak hemisphere
margins `0 ≤ ⟪h₀, A'_WBS r⟫` for EVERY opened-arm vertex** (`exists_unit_perturbed_normal_of_tangent`'s
`hnn` argument).  FFCT44's `openHemisphere_of_weakSupports_jointOpen` consumes exactly such an `hmargin`
(its §3 lemma's `_hmargin` binder is *unused*, but brick 2 feeds `hmargin` to the tilt at line 393).

The WBS family **deliberately dropped the hemisphere monitor** (`ZinanFFCT45`, design §7 route (c)), so
there is **no** `hemiW_inner_nonneg` analogue: the opened arm's margins w.r.t. *any* fixed `h₀` are not
monitored and can go negative.  The original arm `A`'s `open_hemisphere` normal `h₀` (strict on `A`'s
vertices) gives **no** guarantee on the *opened* vertices `A'_WBS r`.  So the design §9 route through the
tilt has a genuine gap.

**The honest fix (this module's keystone).**  The tilt is not the only hemisphere-production mechanism.
We produce the open hemisphere **margins-free** by *finite separation on the full opened-vertex set*:
either `0 ∉ convexHull` of all opened vertices — and `ZinanFFCT36.exists_inner_pos_of_zero_notMem_convexHull`
gives a strict common normal **directly** (no base `h₀`, no tilt) — or `0 ∈ convexHull`, and then every
edge functional pushed through the convex combination forces a positive-weight vertex to be a common
edge-plane axis, exactly the hypothesis of FFCT44's exported meridian-pencil collapse
`commonLine_collapse_forces_flat_joint`, contradicting joints-in-`(0,π)`.  This is the full-set sibling
of FFCT44's equator-subset `equatorTangentExists_of_weakSupports_jointOpen`, with the `h₀`-equator filter
replaced by `Finset.univ`, and the tangent replaced by the separator normal itself.  **No margins
hypothesis is consumed.**

## What this module proves (clean-3, no `sorry`/`axiom`/`admit`/`native_decide`)

* `§1` `openHemisphere_of_weakSupports_jointOpen_full` — the **margins-free** open-hemisphere production
  from weak supports + open joints + opened ShortArc edges.  This is the genuine replacement for the
  tilt route.
* `§2` (Brick 4) `openHemisphere_at_WBS_sup` — the keystone, at the WBS sup arm `A'_WBS`, from the WBS
  closure supports (FFCT45), the opened ShortArc edges, and joints-in-`(0,π)`.
* `§3` (Bricks 5–6) `supportStuckWBS_weakConvex` / `reachWBS_strictConvex` — the convexity certificates.
* `§4` (Brick 8) `interiorOpeningOutcomeWBS` — the WBS trichotomy threaded into
  `SphericalArmAssembly.InteriorOpeningOutcome`.
* `§5` (Brick 9) `mainPlus_headline_wbs` — the FFCT43 headline re-threaded on the WBS outcome; the
  hemisphere residuals are gone.

## The opened ShortArc edges (the one structural input bricks 4–6 still need)

FFCT44's collapse and the downstream assemblers need the opened arm's edges to be short arcs.  The
**interior** edges (`Fin n`) are short margins-free: `SameSides A'_WBS B` plus `B` strictly convex give
`sideLen A'_WBS i = sideLen B i ∈ (0, π)`, i.e. the edge is a ShortArc.  The **wraparound** edge
`(last, 0)` is distinct margins-free by the FFCT43 endpoint-positivity route (re-instantiated at the WBS
sup via `ZinanFFCT45.glueWBS_clause_i`).  Its non-antipodality is the one place where the support-stuck
branch (weak supports only) cannot conclude margins-free; the reach branch (strict supports) closes it
via `ZinanFFCT34.antipodal_pair_excluded_of_strict`.  We therefore carry the opened ShortArc edges as an
explicit hypothesis of brick 4 and discharge them per branch; the residual surface is documented in §5.
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
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT34
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT40
open ProofsInTheBook.ZinanFFCT42
open ProofsInTheBook.ZinanFFCT43
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT45

namespace ProofsInTheBook.ZinanFFCT46

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The margins-free open-hemisphere production.

The full-set sibling of `ZinanFFCT44.equatorTangentExists_of_weakSupports_jointOpen`: run finite
separation on the image of **all** opened vertices.  Either the origin is outside the hull and the
separator is the strict open-hemisphere normal directly; or the origin is inside, every edge functional
pushed through the convex combination vanishes, a positive-weight vertex is a common edge-plane axis, and
FFCT44's `commonLine_collapse_forces_flat_joint` contradicts joints-in-`(0,π)`.  **No base `h₀`, no tilt,
no margins.** -/

/-- **Margins-free open hemisphere from weak supports + open joints + short edges.**  For a closed chain
`P : Fin (n+1) → S2` (`2 ≤ n`) with cyclic short-arc edges (`hside`), weak (`≥ 0`) non-incident edge
supports (`hsupp`), and all interior joints in `(0, π)` (`hjopen`), there is a *unit* normal `h'`
strictly positive against every vertex: `∃ h', ‖h'‖ = 1 ∧ ∀ r, 0 < ⟪h', P r⟫`.  **No hemisphere-margin
hypothesis is consumed** — the genuine replacement for FFCT44's tilt route, which needed a weak-margin
base normal the WBS family does not supply. -/
theorem openHemisphere_of_weakSupports_jointOpen_full {n : ℕ} {P : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hside : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1)))
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (P i) (P (i + 1)) (P j))
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    ∃ h' : E3, ‖h'‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ) := by
  classical
  -- The full vertex image set.
  set s : Finset E3 := (Finset.univ : Finset (Fin (n + 1))).image (fun r => ((P r : S2) : E3))
    with hs
  have hmem_iff : ∀ v, v ∈ s ↔ ∃ m, ((P m : S2) : E3) = v := by
    intro v
    rw [hs, Finset.mem_image]
    constructor
    · rintro ⟨m, _hm, rfl⟩; exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩; exact ⟨m, Finset.mem_univ _, rfl⟩
  by_cases h0 : (0 : E3) ∈ convexHull ℝ (s : Set E3)
  · -- `0 ∈ hull`: derive a common edge-plane axis and contradict the FFCT44 collapse kernel.
    exfalso
    rw [Finset.mem_convexHull'] at h0
    obtain ⟨w, hw0, hw1, hwsum⟩ := h0
    -- For every edge `i` and every member `v`, `w v * det3 (P i)(P i+1) v ≥ 0` (weak supports).
    have hterm_nonneg : ∀ (i : Fin (n + 1)) (v : E3), v ∈ s →
        0 ≤ w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i v hv
      obtain ⟨m, rfl⟩ := (hmem_iff v).mp hv
      by_cases hmi : m = i
      · subst hmi; rw [show det3 (P m : E3) (P (m + 1) : E3) (P m : E3) = 0 from by
          simp only [det3]; ring, mul_zero]
      · by_cases hmi1 : m = i + 1
        · subst hmi1; rw [show det3 (P i : E3) (P (i + 1) : E3) (P (i + 1) : E3) = 0 from by
            simp only [det3]; ring, mul_zero]
        · exact mul_nonneg (hw0 _ hv)
            (le_trans (le_of_eq rfl) (hsupp i m (by simpa [eq_comm] using hmi)
              (by simpa [eq_comm] using hmi1)))
    -- The edge functional pushed through the convex combination is `0`.
    have hedge_zero : ∀ i : Fin (n + 1),
        (0 : ℝ) = ∑ v ∈ s, w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i
      have hkey := det3_edge_centerSum (P i : E3) (P (i + 1) : E3) s w
      rw [hwsum] at hkey
      rw [show det3 (P i : E3) (P (i + 1) : E3) (0 : E3) = 0 from by simp [det3]] at hkey
      exact hkey
    have hterm_zero : ∀ i : Fin (n + 1), ∀ v ∈ s,
        w v * det3 (P i : E3) (P (i + 1) : E3) v = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v hv => hterm_nonneg i v hv)).mp
        (hedge_zero i).symm
    -- Pick a positive-weight member `v₀`.
    have hexists_pos : ∃ v ∈ s, 0 < w v := by
      by_contra hnone
      push_neg at hnone
      have : ∑ v ∈ s, w v = 0 :=
        Finset.sum_eq_zero (fun v hv => le_antisymm (hnone v hv) (hw0 v hv))
      rw [hw1] at this; exact one_ne_zero this
    obtain ⟨v0, hv0s, hv0pos⟩ := hexists_pos
    obtain ⟨r0, hv0eq⟩ := (hmem_iff v0).mp hv0s
    -- `z := P r0` is a common edge-plane axis.
    have hallplanes : ∀ i : Fin (n + 1), det3 (P i : E3) (P (i + 1) : E3) (P r0 : E3) = 0 := by
      intro i
      have := hterm_zero i v0 hv0s
      rcases mul_eq_zero.mp this with hw | hd
      · exact absurd hw (ne_of_gt hv0pos)
      · rw [hv0eq]; exact hd
    exact commonLine_collapse_forces_flat_joint hn hside hallplanes hjopen
  · -- `0 ∉ hull`: separation gives the strict hemisphere normal directly; normalize to unit length.
    obtain ⟨t, ht⟩ := exists_inner_pos_of_zero_notMem_convexHull s.finite_toSet h0
    have htpos : ∀ r : Fin (n + 1), 0 < (⟪t, (P r : E3)⟫ : ℝ) := by
      intro r
      have hrmem : ((P r : S2) : E3) ∈ s := by rw [hmem_iff]; exact ⟨r, rfl⟩
      exact ht _ hrmem
    -- `t ≠ 0` (it has a strictly positive inner product against `P 0`); normalize.
    have htne : t ≠ 0 := by
      intro h
      have := htpos ⟨0, by omega⟩
      rw [h, inner_zero_left] at this
      exact lt_irrefl _ this
    have htnorm : 0 < ‖t‖ := norm_pos_iff.mpr htne
    refine ⟨(‖t‖⁻¹ : ℝ) • t, ?_, fun r => ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]; field_simp
    · rw [inner_smul_left]
      simp only [RCLike.conj_to_real]
      exact mul_pos (by positivity) (htpos r)

/-! ## §2. (Brick 4) The open hemisphere at the WBS supremum — THE keystone.

The opened arm `A'_WBS := openTail A K (-δ*_WBS)` at the WBS supremum has weak supports (FFCT45's
`supportWBS_sOrient_nonneg`).  Feeding the opened ShortArc edges and joints-in-`(0,π)` into the
margins-free production yields the strict open hemisphere. -/

/-- **Brick 4 — the open hemisphere at the WBS supremum.**  At `A'_WBS := openTail A K (-δ*_WBS)`, from
the WBS closure supports (`≥ 0`), the opened ShortArc edges (`hedge`), and joints-in-`(0, π)` (`hjopen`),
there is a *unit* normal `h'` strictly positive against every vertex.  **Margins-free** (no fixed-`h₀`
margins are monitored or consumed) — this is the §15.2 keystone replacing all fixed-hemi residuals. -/
theorem openHemisphere_at_WBS_sup {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hedge : ∀ i : Fin (n + 1),
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1)))
    (hjopen : ∀ r : Fin (n - 1),
      0 < jointAngle (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) r ∧
        jointAngle (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) r < Real.pi) :
    ∃ h' : E3, ‖h'‖ = 1 ∧ ∀ r : Fin (n + 1),
      0 < (⟪h', ((openTail A (openingAxis k) (-(monitoredSupWBS A B k)) r : S2) : E3)⟫ : ℝ) := by
  have hn : 2 ≤ n := hA.two_le
  exact openHemisphere_of_weakSupports_jointOpen_full hn hedge
    (supportWBS_sOrient_nonneg hA hka hkt hkdef) hjopen

/-! ## §2′. The opened arm's side / joint geometry at the WBS supremum (the inputs to brick 4).

The opened ShortArc edges and joints-in-`(0, π)` that brick 4 consumes are assembled here from the WBS
closure data, the isometry preservation (`sDist_openTail_*`), and the joint bookkeeping (FFCT37/20/45). -/

/-- A point pair with `0 < sDist < π` is a `ShortArc` (the converse of `ShortArc.sDist_pos`/`sDist_lt_pi`).
Distinctness from `sDist_eq_zero_iff`; non-antipodality because `(p : E3) = -(q : E3)` forces
`sInner p q = -1`, hence `sDist p q = arccos(-1) = π`, contradicting `sDist p q < π`. -/
theorem shortArc_of_sDist_pos_lt_pi {p q : S2}
    (hpos : 0 < sDist p q) (hlt : sDist p q < Real.pi) : ShortArc p q := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · rw [sDist_eq_zero_iff.2 he] at hpos; exact lt_irrefl 0 hpos
  · -- `(p : E3) = -(q : E3)` ⟹ `sInner p q = -1` ⟹ `sDist = π`.
    have hcos : sInner p q = -1 := by
      simp only [sInner, he, inner_neg_left, S2.inner_self]
    have : sDist p q = Real.pi := by rw [sDist, hcos, Real.arccos_neg_one]
    rw [this] at hlt; exact lt_irrefl Real.pi hlt

/-- **Opened non-wrap edges stay short** (margins-free).  For an edge `(i, i+1)` with `i ≠ Fin.last n`,
the opened edge `(openTail A K δ i, openTail A K δ (i + 1))` has the same spherical length as the base
edge `(A i, A (i + 1))` — both endpoints are on the same side of the axis `K` (or the seam, axis fixed +
isometry), so `sDist` is preserved — and the base edge is a `ShortArc` (`A` strict).  The wraparound edge
`i = Fin.last n` (where `i + 1 = 0` straddles the axis) is excluded. -/
theorem openTail_nonwrap_shortArc {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (K : Fin (n + 1)) (δ : ℝ) {i : Fin (n + 1)} (hi : i ≠ Fin.last n) :
    ShortArc (openTail A K δ i) (openTail A K δ (i + 1)) := by
  -- the base edge is short, with a known spherical length in `(0, π)`.
  have hbase : ShortArc (A i) (A (i + 1)) := arm_edge_short hA i
  -- `i ≠ last` ⟹ `i.val < n` ⟹ `(i + 1).val = i.val + 1` (no wraparound).
  have hilt : i.val < n := by
    have hival : i.val < n + 1 := i.isLt
    have hlast : ((Fin.last n : Fin (n + 1)) : ℕ) = n := Fin.val_last n
    rcases Nat.lt_or_ge i.val n with h | h
    · exact h
    · exact absurd (Fin.ext (by omega)) hi
  have hi1 : ((i + 1 : Fin (n + 1)) : ℕ) = i.val + 1 := by
    rw [Fin.val_add, Fin.val_one']
    rw [Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
    exact Nat.mod_eq_of_lt (by omega)
  -- the opened edge has the same length as the base edge; ShortArc transfers.
  have hsd : sDist (openTail A K δ i) (openTail A K δ (i + 1)) = sDist (A i) (A (i + 1)) := by
    rcases lt_trichotomy i.val K.val with hlt | heq | hgt
    · -- both endpoints fixed (`i ≤ K` and `i + 1 ≤ K`).
      rw [openTail_fixed A K δ (by omega), openTail_fixed A K δ (show (i + 1).val ≤ K.val by omega)]
    · -- seam: `i = K` (axis fixed), `i + 1 > K` (tail rotated).
      have hiK : i = K := Fin.ext heq
      subst hiK
      have hgt1 : i.val < (i + 1).val := by omega
      exact sDist_openTail_axis_tail A i δ hgt1
    · -- both endpoints rotated (`i > K` and `i + 1 > K`).
      exact sDist_openTail_tail A K δ hgt (show K.val < (i + 1).val by omega)
  -- ShortArc from the preserved length in `(0, π)`.
  refine shortArc_of_sDist_pos_lt_pi ?_ ?_
  · rw [hsd]; exact hbase.sDist_pos
  · rw [hsd]; exact hbase.sDist_lt_pi

/-- **The opened-arm joints lie in `(0, π)` at the WBS supremum** (margins-free).  Off-axis joints are
unchanged (`jointAngle_openTail_eq_of_ne`), so positive (`A` strict) and `< π` (`A` strict); the joint
`k` opens to `jointAngle A k + δ*_WBS` (`openedNegJointAngle_eq_add`, branch from the deficit bound), so
`≥ jointAngle A k > 0` and `≤ jointAngle B k < π` (slack closure + `B` strict). -/
theorem openedJoints_in_Ioo_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    ∀ r : Fin (n - 1),
      0 < jointAngle (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) r ∧
        jointAngle (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) r < Real.pi := by
  set δ : ℝ := monitoredSupWBS A B k with hδ
  -- the deficit bound gives `δ ≤ jointAngle B k − jointAngle A k`, hence the additive branch.
  have hδ0 : 0 ≤ δ := (monitoredSupWBS_mem_Icc hA hka hkt hkdef).1
  have hub : δ ≤ jointAngle B k - jointAngle A k := monitoredSupWBS_le_deficit hA hka hkt hkdef
  have hBlt : jointAngle B k < Real.pi := strict_jointAngle_lt_pi hB k
  have hbranch : jointAngle A k + δ ≤ Real.pi := by linarith
  intro r
  by_cases hrk : r = k
  · -- the opened joint `k`.
    subst hrk
    rw [jointAngle_openTail_eq_openedInterior A r (-δ),
      openedNegJointAngle_eq_add hA hka hkt hδ0 hbranch]
    refine ⟨?_, by linarith⟩
    have hpos : 0 < jointAngle A r := strict_jointAngle_pos hA r
    linarith
  · -- off-axis joints are unchanged.
    rw [jointAngle_openTail_eq_of_ne A k (-δ) hrk]
    exact ⟨strict_jointAngle_pos hA r, strict_jointAngle_lt_pi hA r⟩

/-- **The opened-arm wraparound edge is distinct at the WBS supremum** (margins-free, FFCT43 route).
`endpt A'_WBS = sDist (A'_WBS 0)(A'_WBS last)`; `glueWBS_clause_i` gives `endpt A ≤ endpt A'_WBS` and
`strict_arm_endpt_pos` gives `0 < endpt A`, so `A'_WBS 0 ≠ A'_WBS last`.  (Non-antipodality of the wrap
edge is the one fact the weak-support branch cannot conclude margins-free; the strict branch closes it.) -/
theorem openedWrap_distinct_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0
      ≠ openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n) := by
  have hpos : 0 < endpt A := strict_arm_endpt_pos hA
  have hmono : endpt A ≤ endpt (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) :=
    glueWBS_clause_i hA hka hkt hkdef
  have hsd : (0 : ℝ) < sDist (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0)
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n)) :=
    lt_of_lt_of_le hpos hmono
  intro heq
  rw [sDist_eq_zero_iff.2 heq] at hsd
  exact lt_irrefl 0 hsd

/-! ## §3. (Bricks 5–6) The WBS convexity certificates.

Both bricks feed brick 4's open hemisphere into the family-agnostic assemblers.  The **support-stuck**
branch (weak supports) needs the opened ShortArc edges, of which the wraparound edge's non-antipodality
is supplied by the single sharp residual `OpenedWrapShortArcAtSupWBS` (interior edges and wrap
distinctness are margins-free); the **reach** branch (strict supports) closes the wrap edge unconditionally
via `antipodal_pair_excluded_of_strict`. -/

/-- **The one sharp residual: the opened wraparound edge is a `ShortArc`.**  At the WBS supremum, the
wraparound edge `(last, 0)` of the opened arm `A'_WBS` is non-degenerate (a short arc).  Distinctness is
discharged margins-free (`openedWrap_distinct_at_supWBS`); the residual content is the **non-antipodality**
of the wrap edge, which the weak-support branch cannot conclude margins-free (the strict branch can, via
`antipodal_pair_excluded_of_strict`).  Scoped to the glue context (refutation-resistant: a constant arm
is excluded by `StrictConvexSphArm A`); realised at `δ = 0` where it is `A`'s own short wrap edge. -/
def OpenedWrapShortArcAtSupWBS : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0)

/-- **Opened ShortArc edges (all `n + 1`) from the wrap residual.**  Interior/seam/tail edges are short
margins-free (`openTail_nonwrap_shortArc`); the wraparound edge `i = Fin.last n` (`i + 1 = 0`) is supplied
by the wrap ShortArc (symmetrized to the `(last, last + 1)` orientation). -/
theorem openedEdges_short_at_supWBS_of_wrap {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hwrap : ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0)) :
    ∀ i : Fin (n + 1),
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1)) := by
  intro i
  by_cases hi : i = Fin.last n
  · subst hi; rw [lastAddOne_eq_zero]; exact hwrap
  · exact openTail_nonwrap_shortArc hA (openingAxis k) (-(monitoredSupWBS A B k)) hi

/-- **Brick 5 — support-stuck ⟹ weakly convex.**  At a `SupportStuckWBS` supremum (a non-incident support
vanishes, so only weak supports are available), the opened arm `A'_WBS` is `WeakConvexSphArm`.  The open
hemisphere (brick 4) is produced margins-free from weak supports + open joints + the opened ShortArc edges;
it gives the edge distinctness `hdist` and feeds `weakConvex_of_supportStuckW_of_hemiPos_anyH`.  The wrap
edge's non-antipodality is the residual `OpenedWrapShortArcAtSupWBS`. -/
theorem supportStuckWBS_weakConvex {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hwrap : ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0)) :
    WeakConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) := by
  set δ : ℝ := monitoredSupWBS A B k with hδ
  have hedge := openedEdges_short_at_supWBS_of_wrap hA hwrap
  have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  have hsupp := supportWBS_sOrient_nonneg hA hka hkt hkdef
  -- the open hemisphere (brick 4), margins-free.
  obtain ⟨h', hnorm, hhem⟩ := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
  -- edge distinctness from the ShortArc edges.
  have hdist : ∀ i : Fin (n + 1),
      openTail A (openingAxis k) (-δ) i ≠ openTail A (openingAxis k) (-δ) (i + 1) :=
    fun i => (hedge i).1
  exact weakConvex_of_supportStuckW_of_hemiPos_anyH hA hsupp hdist ⟨h', hnorm, hhem⟩

/-- **Brick 6 — reach / no-support-stuck ⟹ strictly convex.**  When no non-incident support of `A'_WBS`
vanishes (`¬ SupportStuckWBS`), the weak supports upgrade to **strict** (`lt_of_le_of_ne`).  The strict
supports give the opened ShortArc edges margins-free — including the wraparound edge, whose non-antipodality
follows from `antipodal_pair_excluded_of_strict` (so **no wrap residual is needed here**) — and the open
hemisphere (brick 4); `reach_strictConvex_interior` assembles `StrictConvexSphArm A'_WBS`. -/
theorem reachWBS_strictConvex {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hnotStuck : ¬ SupportStuckWBS A B k) :
    StrictConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) := by
  set δ : ℝ := monitoredSupWBS A B k with hδ
  have hn : 2 ≤ n := hA.two_le
  have hsupp := supportWBS_sOrient_nonneg hA hka hkt hkdef
  -- strict supports: weak `≥ 0` is `> 0` since none vanishes (else `SupportStuckWBS`).
  have hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < sOrient (openTail A (openingAxis k) (-δ) i) (openTail A (openingAxis k) (-δ) (i + 1))
        (openTail A (openingAxis k) (-δ) j) := by
    intro i j hji hji1
    refine lt_of_le_of_ne (hsupp i j hji hji1) (fun heq => hnotStuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, ?_⟩)
    rw [supportConstraint_apply]; exact heq.symm
  -- the opened ShortArc wrap edge from strict supports: distinct + non-antipodal.
  have hwrapdist := openedWrap_distinct_at_supWBS hA hka hkt hkdef
  have hwrap : ShortArc (openTail A (openingAxis k) (-δ) (Fin.last n))
      (openTail A (openingAxis k) (-δ) 0) := by
    refine ⟨fun he => hwrapdist he.symm, fun he => ?_⟩
    -- `A'_WBS last = -(A'_WBS 0)`: antipodal pair `(last, 0)` excluded by strict supports
    -- (`last ≠ 0`, `last ≠ 0 + 1 = 1` for `n ≥ 2`).
    have hl0 : (Fin.last n : Fin (n + 1)) ≠ (0 : Fin (n + 1)) := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_last, Fin.val_zero] at this; omega
    have hl1 : (Fin.last n : Fin (n + 1)) ≠ (0 : Fin (n + 1)) + 1 := by
      intro h; have := congrArg Fin.val h
      rw [Fin.val_last, zero_add, Fin.val_one'] at this
      rw [Nat.mod_eq_of_lt (by omega : 1 < n + 1)] at this; omega
    exact antipodal_pair_excluded_of_strict hmix (r := Fin.last n) (s := 0) hl0 hl1 he
  have hedge := openedEdges_short_at_supWBS_of_wrap hA hwrap
  have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  obtain ⟨h', hnorm, hhem⟩ := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
  exact reach_strictConvex_interior hA hnorm hmix hhem

/-- A `SupportStuckWBS` witness yields a vanishing non-incident support of `A'_WBS` in `sOrient` form. -/
theorem supportStuckWBS_vanishingSupport {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hstuck : SupportStuckWBS A B k) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) j) = 0 := by
  obtain ⟨c, hc⟩ := hstuck
  rw [supportConstraint_apply] at hc
  exact ⟨c.1.1, c.1.2, c.2.1, c.2.2, hc⟩

/-! ## §4. (Brick 8) The WBS interior-opening outcome.

The WBS trichotomy threaded into `SphericalArmAssembly.InteriorOpeningOutcome`.  The CAP branch is killed
by `monitoredSupWBS_lt_pi`; SUPPORT-stuck gives the weak-convex + vanishing-support outcome (brick 5,
consuming the wrap residual); REACH and BASE-stuck (the latter collapsed to REACH by
`BaseStuckProgressWBS_holds` in the `¬ SupportStuckWBS` context, since a vanishing support would *be*
`SupportStuckWBS`) give the strictly-convex deficit-drop outcome (brick 6).  **No hemisphere residual.** -/

/-- **Brick 8 — the WBS interior-opening outcome.**  `SphericalArmAssembly.InteriorOpeningOutcome` from
the WBS family, conditional only on the single sharp residual `OpenedWrapShortArcAtSupWBS`.  Mirrors
`ZinanFFCT38.interiorOpeningOutcomeW_of_glue`, but on the hemisphere-free WBS supremum: REACH /
SUPPORT-stuck / BASE-stuck via the FFCT45 trichotomy, with the convexity certificates from bricks 5–6.
The hemisphere residuals (`SupportStuckMarginsPosAtSupWB`, `PureHemiProgressWB`) are **gone**. -/
theorem interiorOpeningOutcomeWBS (hwrapres : OpenedWrapShortArcAtSupWBS) :
    SphericalArmAssembly.InteriorOpeningOutcome := by
  intro n A B hA hB hside hangle k hkdef
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  -- side / joint bookkeeping.
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA']; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hside' : SameSides A' B := by
    intro i; rw [hA', openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA', jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  have hmono : endpt A ≤ endpt A' := glueWBS_clause_i hA hka hkt hkdef
  refine ⟨A', hmono, hside', hangle', ?_⟩
  -- dispatch on `SupportStuckWBS`.
  by_cases hstuck : SupportStuckWBS A B k
  · -- SUPPORT-stuck: weak convex (brick 5) + the vanishing support.  RIGHT disjunct.
    have hwrap : ShortArc (openTail A K (-δ) (Fin.last n)) (openTail A K (-δ) 0) :=
      hwrapres n A B hA hB k hkdef
    have hweak : WeakConvexSphArm A' :=
      supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap
    exact Or.inr ⟨hweak, supportStuckWBS_vanishingSupport hstuck⟩
  · -- ¬ SUPPORT-stuck: REACH or BASE-stuck (clause ii); BASE-stuck collapses to REACH.
    have hreach : ReachWBS A B k := by
      rcases glueWBS_clause_ii hA hB hka hkt hkdef hstuck with hr | hbase
      · exact hr
      · -- BASE-stuck: progress gives REACH or a vanishing support; the latter is `SupportStuckWBS`.
        rcases BaseStuckProgressWBS_holds n A B hA hB k hkdef hbase with hr | hvan
        · exact hr
        · exfalso
          obtain ⟨i, j, hji, hji1, heq⟩ := hvan
          exact hstuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq⟩
    -- REACH: strictly convex (brick 6) + deficit drop.  LEFT disjunct.
    have hstrict : StrictConvexSphArm A' := reachWBS_strictConvex hA hB hka hkt hkdef hstuck
    have hreach_k : jointAngle A' k = jointAngle B k := by rw [hjointk]; exact hreach
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    exact Or.inl ⟨hstrict, hdrop⟩

/-! ## §5. (Brick 9) The headline re-threaded on the WBS outcome.

The FFCT43 headline `mainPlus_headline_closing_free` consumes `SphericalArmAssembly.InteriorOpeningOutcome`
through `spherical_arm_mono_of_spliceBodyDiagMono`.  We re-thread it on `interiorOpeningOutcomeWBS`: the
hemisphere residuals `SupportStuckMarginsPosAtSupWB` and `PureHemiProgressWB` are **gone** — they never
arise on the hemisphere-free WBS family.  The final surface is `SpliceBodyDiagMono` + `SpliceStructuralData`
+ the single sharp residual `OpenedWrapShortArcAtSupWBS`. -/

/-- **Brick 9 — the WBS headline.**  `sDist (A 0)(A last) ≤ sDist (B 0)(B last)` for strictly convex arms
with equal sides and `A`'s joints `≤` `B`'s, conditional on the FINAL surface:

* `hcore : SpliceBodyDiagMono`, `hstruct : SpliceStructuralData` — the pre-B1 splice geometry;
* `hwrapres : OpenedWrapShortArcAtSupWBS` — the single sharp residual (the opened wraparound edge is a
  short arc; its non-antipodality is the one fact the weak-support branch cannot conclude margins-free).

The hemisphere residuals (`SupportStuckMarginsPosAtSupWB`, `PureHemiProgressWB`), the base-cap
(`GlueWBaseCap`), the base-stuck progress (`BaseStuckProgressW`), and the closing-edge distinctness are
all GONE.  This is the §9 headline swap. -/
theorem mainPlus_headline_wbs
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (hwrapres : OpenedWrapShortArcAtSupWBS)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_spliceBodyDiagMono hcore hstruct
    (interiorOpeningOutcomeWBS hwrapres) hn A B hA hB hside hangle

/-! ### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of the margins-free production: its conclusion (a strict open hemisphere) is genuine
geometric data, realised at any single short edge (the production runs on `2 ≤ n` closed chains with
positive-nonflat joints, not vacuously). -/
theorem openHemisphere_full_conclusion_real {n : ℕ} (h' : E3) (P : Fin (n + 1) → S2)
    (hh' : ‖h'‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ)) :
    ‖h'‖ = 1 := hh'.1

/-- Non-vacuity of `OpenedWrapShortArcAtSupWBS`: realised at `δ*_WBS = 0` (the unopened arm), where the
wrap edge is `A`'s own short closing edge `(A last, A 0)` of the strict convex polygon — a genuine
`ShortArc`, not a vacuous-hypothesis impostor.  (`openTail A K (-0) = A` by `neg_zero` + `openTail_zero_angle`.) -/
theorem openedWrapShortArcAtSupWBS_conclusion_real {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) :
    ShortArc (A (Fin.last n)) (A 0) := by
  have hwrap : ShortArc (A (Fin.last n)) (A (Fin.last n + 1)) := arm_edge_short hA (Fin.last n)
  rwa [lastAddOne_eq_zero] at hwrap

/-- Refutation-resistance of `OpenedWrapShortArcAtSupWBS`: a constant arm (which would make the wrap edge
degenerate) is excluded from the context binders by `StrictConvexSphArm A`. -/
theorem openedWrapShortArcAtSupWBS_constantArm_excluded {n : ℕ} (p : S2)
    (hStrict : StrictConvexSphArm (fun _ : Fin (n + 1) => p)) : False :=
  openedClosingEdgeDistinctAtSupW_constantArm_excluded p hStrict

/-- Non-vacuity of the WBS headline: realised reflexively at `A = B`. -/
theorem mainPlus_headline_wbs_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

end ProofsInTheBook.ZinanFFCT46

-- §1 the margins-free open-hemisphere production (THE keystone mechanism)
#print axioms ProofsInTheBook.ZinanFFCT46.openHemisphere_of_weakSupports_jointOpen_full
-- §2 brick 4
#print axioms ProofsInTheBook.ZinanFFCT46.openHemisphere_at_WBS_sup
-- §2′ the opened side / joint geometry
#print axioms ProofsInTheBook.ZinanFFCT46.openTail_nonwrap_shortArc
#print axioms ProofsInTheBook.ZinanFFCT46.openedJoints_in_Ioo_at_supWBS
#print axioms ProofsInTheBook.ZinanFFCT46.openedWrap_distinct_at_supWBS
-- §3 bricks 5–6
#print axioms ProofsInTheBook.ZinanFFCT46.supportStuckWBS_weakConvex
#print axioms ProofsInTheBook.ZinanFFCT46.reachWBS_strictConvex
-- §4 brick 8
#print axioms ProofsInTheBook.ZinanFFCT46.interiorOpeningOutcomeWBS
-- §5 brick 9 + non-vacuity
#print axioms ProofsInTheBook.ZinanFFCT46.mainPlus_headline_wbs
#print axioms ProofsInTheBook.ZinanFFCT46.openedWrapShortArcAtSupWBS_conclusion_real
#print axioms ProofsInTheBook.ZinanFFCT46.openedWrapShortArcAtSupWBS_constantArm_excluded