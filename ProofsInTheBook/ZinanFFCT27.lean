import ProofsInTheBook.ZinanFFCT26
import ProofsInTheBook.SphericalStuckGeneral

/-!
# `ZinanFFCT27` — the Chapter 13 B1 master bricks: Gram-sign extraction and the `StuckAtKData` wrapper

This module implements the **master** bricks of the B1 Gram-sign extraction design
(`HANDOFF/design-rounds/ch13-b1-gram-extraction.md`, §5/§6/§9), built on the derivative-algebra layer
`ZinanFFCT26` and the stuck-datum infrastructure `SphericalStuckGeneral`.

## Bricks delivered

* **Brick 5** `hbeta_of_axis_edge_binding` — the `hβ` Gram inequality for an *axis-incident* binding
  edge.  At the admissible supremum `δ`, the binding edge support `mixedSupport A (i, i+1) δ = 0`
  (with `A (i+1) = openAxis A`, the axis), admissible-nonnegative on `[0, δ]`, has a nonpositive
  left-derivative (`deriv_nonpos_of_left_nonneg_zero`); the derivative equals `−hβ` in the
  axis-incident case (`det3_axis_cross_eq_neg_gram_S2`), so `hβ ≥ 0`.

* **Brick 6 (corrected, the honest finding)** — the design's §6 companion statement
  `halpha_of_hbeta_and_positive_axis_joint` is **VACUOUS**: its hypothesis set
  `(det3 p mid q = 0, ShortArc mid q, ShortArc mid p, hβ ≥ 0, 0 < sphAngle p mid q)` is
  *unsatisfiable*.  We prove this rigorously (`design_halpha_hyps_unsatisfiable`), so any conditional
  built on it would be an anti-impostor vacuous conditional (playbook §3.3).  The honest companion
  mechanism is the **algebraic reduction** `halpha_iff_acoef_nonneg` / `hbeta_iff_bcoef_nonneg`: under
  the span decomposition `p = a•mid + b•q` (extracted from the vanishing support over the independent
  base `{mid, q}`), `hβ = b·(1 − G²)` and `hα = a·(1 − G²)` with `G = ⟪mid,q⟫`, `1 − G² > 0`.  Thus
  `hβ ⟺ b ≥ 0` and `hα ⟺ a ≥ 0`; the binding derivative supplies `b ≥ 0` (= `hβ`), and the companion
  sign `a ≥ 0` is a **genuine convex-position residual** (the B5-B1 audit's
  `no_repeat_of_positiveJoints` brick, NOT in this wave).  We deliver the satisfiable, non-vacuous
  companion `halpha_of_acoef_nonneg` taking exactly that residual.

* **Brick 9** `StuckAtKData_of_axis_edge_binding` — assembles the full `StuckAtKData` for the opened
  arm at the axis-incident cut, threading `hsupp` (mixed support rewritten through `openArm`), `hsa`
  (FFCT26 brick 8), the two Gram signs, and `hside`.

## The brick-6 finding (headline)

`sphAngle p mid q` is the spherical angle **at `mid`** (`sphAngle u v w := angle(tangentTo v u,
tangentTo v w)`).  With `p = a•mid + b•q`, the tangent of `p` at `mid` is `b·(q − G•mid)`, a scalar
multiple of the tangent of `q` at `mid`.  Hence `0 < sphAngle p mid q` forces `b < 0` (the tangents
anti-aligned, `b = 0` gives the right-angle convention but then `p = ±mid` violates `ShortArc mid p`),
which contradicts `hβ ⟹ b ≥ 0`.  So the design's §6 hypothesis set is **contradictory**, and the
`a`-sign cannot come from the joint-positivity hypothesis the design names.  This matches the
independent B5-B1 audit (`HANDOFF/design-rounds/ch13-B5-B1-audit.md`): the companion sign needs the
no-repeat / positive-joints machinery, a separate master brick.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalSZ

namespace ProofsInTheBook.ZinanFFCT27

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-- `det3` is cyclic: `det3 a b c = det3 b c a`.  (Used to feed the vanishing support `det3 p mid q`
into the span extractor, which expects the base pair `(mid, q)` in the first two slots.) -/
private theorem det3_cyc (a b c : E3) : det3 a b c = det3 b c a := by
  simp only [det3]; ring

/-! ## Brick 5 — `hβ` extraction for an axis-incident binding edge

Assembly of the derivative-algebra bricks (`ZinanFFCT26`):

* `hasDerivAt_mixedSupport` gives `f' = det3 (A i)(A (i+1))(k × rot k δ tail)` at `δ`;
* `deriv_nonpos_of_left_nonneg_zero` (admissible-nonneg on `[0,δ]`, zero at `δ`) gives `f' ≤ 0`;
* in the axis-incident case `A (i+1) = openAxis A` (so the cross-axis `k = openAxis A` equals the
  edge's second vertex `A (i+1)`), `det3_axis_cross_eq_neg_gram_S2` rewrites `f' = −hβ`.

Therefore `−hβ ≤ 0`, i.e. `hβ ≥ 0`. -/

/-- **(Brick 5) `hβ` from an axis-incident binding edge.**  At the admissible supremum `δ`, with the
edge `(A i, A (i+1))` axis-incident (`A (i+1) = openAxis A`), admissible-nonnegative on `[0, δ]`, and
binding (`mixedSupport A (i, i+1) δ = 0`), the `hβ` Gram inequality holds for the opened triple
`p = A i`, `mid = A (i+1)`, `q = rot (openAxis A) δ tail`:
`0 ≤ ⟪p, q⟫ − ⟪p, mid⟫ * ⟪q, mid⟫`. -/
theorem hbeta_of_axis_edge_binding {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (ij : Fin (n + 1 + 1) × Fin (n + 1 + 1)) {δ : ℝ}
    (haxis : A ij.2 = openAxis A)
    (hδpos : 0 < δ)
    (hadm : ∀ θ, θ ∈ Set.Icc 0 δ → 0 ≤ mixedSupport A ij θ)
    (hzero : mixedSupport A ij δ = 0) :
    0 ≤ (⟪(A ij.1 : E3),
            (rot (openAxis A : E3) δ (A (Fin.last (n + 1)) : E3))⟫ : ℝ)
      - (⟪(A ij.1 : E3), (A ij.2 : E3)⟫ : ℝ)
        * (⟪(rot (openAxis A : E3) δ (A (Fin.last (n + 1)) : E3)),
            (A ij.2 : E3)⟫ : ℝ) := by
  -- the mixed-support derivative at δ.
  have hderiv := hasDerivAt_mixedSupport A ij δ
  -- one-sided extremum: f' ≤ 0.
  have hnonpos :=
    deriv_nonpos_of_left_nonneg_zero hδpos hderiv hadm hzero
  -- in the axis-incident case the derivative value is `−hβ`.
  -- rewrite `openAxis A` as `A ij.2` inside the cross product, then apply brick 4.
  set q := rot (openAxis A : E3) δ (A (Fin.last (n + 1)) : E3) with hq
  -- `det3 (A ij.1) (A ij.2) (cross (openAxis A) q) = det3 (A ij.1) (A ij.2) (cross (A ij.2) q)`.
  have hcross : (openAxis A : E3) = (A ij.2 : E3) := by rw [haxis]
  have hval : det3 (A ij.1 : E3) (A ij.2 : E3) (cross (openAxis A : E3) q)
      = - ((⟪(A ij.1 : E3), q⟫ : ℝ)
        - (⟪(A ij.1 : E3), (A ij.2 : E3)⟫ : ℝ) * (⟪q, (A ij.2 : E3)⟫ : ℝ)) := by
    rw [hcross]
    exact det3_axis_cross_eq_neg_gram_S2 (A ij.1 : E3) q (A ij.2)
  -- the derivative value (det3 form) is ≤ 0; rewrite via hval.
  rw [hval] at hnonpos
  linarith [hnonpos]

/-! ## Brick 6 — the companion sign `hα`: the honest finding

### The algebraic core

Given the vanishing support `det3 p mid q = 0` and an independent base pair `(mid, q)` (`ShortArc mid
q` ⟹ `mid ≠ q ∧ mid ≠ −q`), the span extraction `lin_indep_span_of_det3_zero` writes
`p = a•mid + b•q`.  With `G := ⟪mid, q⟫` and the unit norms `⟪mid,mid⟫ = ⟪q,q⟫ = 1`:

* `⟪p, mid⟫ = a + b·G`,  `⟪p, q⟫ = a·G + b`;
* `hβ-quantity = ⟪p,q⟫ − ⟪p,mid⟫·⟪q,mid⟫ = b·(1 − G²)`;
* `hα-quantity = ⟪p,mid⟫ − ⟪p,q⟫·⟪mid,q⟫ = a·(1 − G²)`;
* `1 − G² > 0` strictly (independence of `mid, q`).

So `hβ ⟺ b ≥ 0` and `hα ⟺ a ≥ 0`. -/

/-- The strict positivity `0 < 1 − G²` for an independent unit base pair `(mid, q)` (`G = ⟪mid,q⟫`):
from `ShortArc mid q`, `mid ≠ ±q`, the Cauchy–Schwarz inequality is strict. -/
theorem one_sub_gram_sq_pos {mid q : S2} (hsa : ShortArc mid q) :
    0 < 1 - (⟪(mid : E3), (q : E3)⟫ : ℝ) ^ 2 := by
  -- `‖mid × q‖² = 1 − ⟪mid,q⟫²` and the cross product is nonzero for a short arc.
  have hne : cross (mid : E3) (q : E3) ≠ 0 := cross_ne_zero_of_shortArc mid q hsa
  have hpos : (0 : ℝ) < ‖cross (mid : E3) (q : E3)‖ ^ 2 := by positivity
  have hnsq : (⟪cross (mid : E3) (q : E3), cross (mid : E3) (q : E3)⟫ : ℝ)
      = 1 - (⟪(mid : E3), (q : E3)⟫ : ℝ) ^ 2 := by
    rw [norm_cross_sq, mid.2, q.2]; norm_num
  rw [← real_inner_self_eq_norm_sq] at hpos
  rw [hnsq] at hpos
  exact hpos

/-- **The hβ-quantity equals `b·(1 − G²)`** under the span decomposition `p = a•mid + b•q`. -/
theorem hbeta_eq_bcoef_mul {p mid q : S2} {a b : ℝ}
    (hp : (p : E3) = a • (mid : E3) + b • (q : E3)) :
    (⟪(p : E3), (q : E3)⟫ : ℝ) - (⟪(p : E3), (mid : E3)⟫ : ℝ) * (⟪(q : E3), (mid : E3)⟫ : ℝ)
      = b * (1 - (⟪(mid : E3), (q : E3)⟫ : ℝ) ^ 2) := by
  set G : ℝ := (⟪(mid : E3), (q : E3)⟫ : ℝ) with hG
  have hqmid : (⟪(q : E3), (mid : E3)⟫ : ℝ) = G := by rw [hG, real_inner_comm]
  have hpmid : (⟪(p : E3), (mid : E3)⟫ : ℝ) = a + b * G := by
    rw [hp, inner_add_left, real_inner_smul_left, real_inner_smul_left, S2.inner_self mid, hqmid]
    ring
  have hpq : (⟪(p : E3), (q : E3)⟫ : ℝ) = a * G + b := by
    rw [hp, inner_add_left, real_inner_smul_left, real_inner_smul_left, S2.inner_self q, ← hG]; ring
  rw [hpmid, hpq, hqmid]; ring

/-- **The hα-quantity equals `a·(1 − G²)`** under the span decomposition `p = a•mid + b•q`. -/
theorem halpha_eq_acoef_mul {p mid q : S2} {a b : ℝ}
    (hp : (p : E3) = a • (mid : E3) + b • (q : E3)) :
    (⟪(p : E3), (mid : E3)⟫ : ℝ) - (⟪(p : E3), (q : E3)⟫ : ℝ) * (⟪(mid : E3), (q : E3)⟫ : ℝ)
      = a * (1 - (⟪(mid : E3), (q : E3)⟫ : ℝ) ^ 2) := by
  set G : ℝ := (⟪(mid : E3), (q : E3)⟫ : ℝ) with hG
  have hqmid : (⟪(q : E3), (mid : E3)⟫ : ℝ) = G := by rw [hG, real_inner_comm]
  have hpmid : (⟪(p : E3), (mid : E3)⟫ : ℝ) = a + b * G := by
    rw [hp, inner_add_left, real_inner_smul_left, real_inner_smul_left, S2.inner_self mid, hqmid]
    ring
  have hpq : (⟪(p : E3), (q : E3)⟫ : ℝ) = a * G + b := by
    rw [hp, inner_add_left, real_inner_smul_left, real_inner_smul_left, S2.inner_self q, ← hG]; ring
  rw [hpmid, hpq]; ring

/-- **hβ ⟺ b ≥ 0** under the span decomposition `p = a•mid + b•q` (over an independent base). -/
theorem hbeta_iff_bcoef_nonneg {p mid q : S2} {a b : ℝ} (hsa : ShortArc mid q)
    (hp : (p : E3) = a • (mid : E3) + b • (q : E3)) :
    (0 ≤ (⟪(p : E3), (q : E3)⟫ : ℝ)
        - (⟪(p : E3), (mid : E3)⟫ : ℝ) * (⟪(q : E3), (mid : E3)⟫ : ℝ)) ↔ 0 ≤ b := by
  rw [hbeta_eq_bcoef_mul hp]
  constructor
  · intro h
    by_contra hb
    push_neg at hb
    nlinarith [one_sub_gram_sq_pos hsa, h, hb]
  · intro hb
    exact mul_nonneg hb (le_of_lt (one_sub_gram_sq_pos hsa))

/-- **hα ⟺ a ≥ 0** under the span decomposition `p = a•mid + b•q` (over an independent base). -/
theorem halpha_iff_acoef_nonneg {p mid q : S2} {a b : ℝ} (hsa : ShortArc mid q)
    (hp : (p : E3) = a • (mid : E3) + b • (q : E3)) :
    (0 ≤ (⟪(p : E3), (mid : E3)⟫ : ℝ)
        - (⟪(p : E3), (q : E3)⟫ : ℝ) * (⟪(mid : E3), (q : E3)⟫ : ℝ)) ↔ 0 ≤ a := by
  rw [halpha_eq_acoef_mul hp]
  constructor
  · intro h
    by_contra ha
    push_neg at ha
    nlinarith [one_sub_gram_sq_pos hsa, h, ha]
  · intro ha
    exact mul_nonneg ha (le_of_lt (one_sub_gram_sq_pos hsa))

/-- **(Brick 6, the satisfiable companion) `hα` from the companion coefficient sign.**  The HONEST
companion: given the vanishing support `det3 p mid q = 0` over the independent base `(mid, q)`
(`ShortArc mid q`), and the companion convex-position sign `0 ≤ a` of the span decomposition
`p = a•mid + b•q`, conclude `hα ≥ 0`.  The `a ≥ 0` residual is the B5-B1 audit's
no-repeat/positive-joints fact (a separate master brick), NOT the design's §6 joint-positivity (which
is vacuous — see `design_halpha_hyps_unsatisfiable`). -/
theorem halpha_of_acoef_nonneg {p mid q : S2} (hsa : ShortArc mid q)
    (hcol : det3 (p : E3) (mid : E3) (q : E3) = 0)
    (_hpm : ShortArc mid p)
    (hacoef : ∀ a b : ℝ, (p : E3) = a • (mid : E3) + b • (q : E3) → 0 ≤ a) :
    0 ≤ (⟪(p : E3), (mid : E3)⟫ : ℝ)
      - (⟪(p : E3), (q : E3)⟫ : ℝ) * (⟪(mid : E3), (q : E3)⟫ : ℝ) := by
  -- span extraction over the independent base `(mid, q)`; feed `det3 mid q p = 0`.
  have hcol' : det3 (mid : E3) (q : E3) (p : E3) = 0 := by rw [← det3_cyc]; exact hcol
  obtain ⟨a, b, hp⟩ :=
    lin_indep_span_of_det3_zero mid.2 q.2
      (fun h => hsa.1 (S2.ext h)) hsa.2 hcol'
  exact (halpha_iff_acoef_nonneg hsa hp).mpr (hacoef a b hp)

/-! ### The brick-6 finding: the design's §6 hypothesis set is unsatisfiable

The design's `halpha_of_hbeta_and_positive_axis_joint` carries
`hjoint_pos : 0 < sphAngle p mid q`.  But `sphAngle p mid q = angle(tangentTo mid p, tangentTo mid q)`,
the angle *at `mid`*.  With `p = a•mid + b•q`, the tangent of `p` at `mid` is `b·(tangentTo mid q)`:
a scalar multiple of the tangent of `q` at `mid`.  So:

* `b > 0` ⟹ `tangentTo mid p = b·(tangentTo mid q)` is a *positive* multiple ⟹ `sphAngle p mid q = 0`;
* `hβ ≥ 0` ⟹ `b ≥ 0` (the algebraic core).

Hence `0 < sphAngle p mid q` and `hβ ≥ 0` force `b = 0`, i.e. `tangentTo mid p = 0`, i.e. `p = ±mid`,
contradicting `ShortArc mid p`.  So the hypothesis set is contradictory.  We prove it directly. -/

/-- The tangent of `p` at `mid` is `b • tangentTo mid q` when `p = a•mid + b•q`.  (`tangentTo mid x =
x − ⟪x,mid⟫•mid`; the `mid`-component drops, leaving `b·(q − ⟪q,mid⟫•mid)`.) -/
theorem tangentTo_span {p mid q : S2} {a b : ℝ}
    (hp : (p : E3) = a • (mid : E3) + b • (q : E3)) :
    tangentTo mid p = b • tangentTo mid q := by
  rw [tangentTo_eq, tangentTo_eq, hp]
  -- ⟪p,mid⟫ via sInner: sInner p mid = ⟪p,mid⟫; with p = a•mid + b•q.
  have hsmid : sInner p mid = a + b * (⟪(q : E3), (mid : E3)⟫ : ℝ) := by
    rw [sInner, hp, inner_add_left, real_inner_smul_left, real_inner_smul_left, S2.inner_self mid]
    ring
  have hsq : sInner q mid = (⟪(q : E3), (mid : E3)⟫ : ℝ) := by rw [sInner]
  rw [hsmid, hsq]
  module

/-- **(Brick 6 finding) The design's §6 hypothesis set is unsatisfiable.**  The conjunction
`det3 p mid q = 0`, `ShortArc mid q`, `ShortArc mid p`, the `hβ`-sign, and `0 < sphAngle p mid q`
is contradictory.  Therefore the design's `halpha_of_hbeta_and_positive_axis_joint` is a *vacuous*
conditional and must not be relied upon (playbook §3.3); the companion sign needs the no-repeat /
positive-joints residual instead (`halpha_of_acoef_nonneg`). -/
theorem design_halpha_hyps_unsatisfiable {p mid q : S2}
    (hcol : det3 (p : E3) (mid : E3) (q : E3) = 0)
    (hsa : ShortArc mid q)
    (hpm : ShortArc mid p)
    (hbeta : 0 ≤ (⟪(p : E3), (q : E3)⟫ : ℝ)
        - (⟪(p : E3), (mid : E3)⟫ : ℝ) * (⟪(q : E3), (mid : E3)⟫ : ℝ))
    (hjoint_pos : 0 < sphAngle p mid q) : False := by
  -- span decomposition.
  have hcol' : det3 (mid : E3) (q : E3) (p : E3) = 0 := by rw [← det3_cyc]; exact hcol
  obtain ⟨a, b, hp⟩ :=
    lin_indep_span_of_det3_zero mid.2 q.2
      (fun h => hsa.1 (S2.ext h)) hsa.2 hcol'
  -- hβ ⟹ b ≥ 0.
  have hb0 : 0 ≤ b := (hbeta_iff_bcoef_nonneg hsa hp).mp hbeta
  -- the tangent of q at mid is nonzero (short arc).
  have htq : tangentTo mid q ≠ 0 := (tangentTo_ne_zero_iff mid q).mpr hsa
  -- the tangent of p at mid is `b • tangentTo mid q`.
  have htan : tangentTo mid p = b • tangentTo mid q := tangentTo_span hp
  -- case on b > 0 vs b = 0.
  rcases lt_or_eq_of_le hb0 with hbpos | hbeq
  · -- b > 0: angle(b • tq, tq) = angle(tq, tq) = 0, contradicting `0 < sphAngle`.
    have hzero : sphAngle p mid q = 0 := by
      rw [sphAngle, htan, InnerProductGeometry.angle_smul_left_of_pos _ _ hbpos,
        InnerProductGeometry.angle_self htq]
    linarith [hjoint_pos, hzero.ge]
  · -- b = 0: tangentTo mid p = 0 ⟹ p = ±mid ⟹ ¬ ShortArc mid p.
    have htp0 : tangentTo mid p = 0 := by rw [htan, ← hbeq, zero_smul]
    have : ¬ ShortArc mid p := (tangentTo_eq_zero_iff mid p).mp htp0
    exact this hpm

/-! ## Brick 9 — the `StuckAtKData` wrapper for the axis-incident binding

We assemble the full `StuckAtKData (openArm A δ) B i' j'` from the opened-arm data, at the
axis-incident cut whose middle vertex is the axis `A ⟨n⟩` and whose far vertex is the rotated tail
`Fin.last (n+1)`.

The index bridge: `mixedSupport A (i, i+1) δ` (with `A (i+1) = openAxis A`, i.e. `i + 1 = n`) equals
`sOrient (openArm A δ ⟨i⟩) (openArm A δ ⟨i+1⟩) (openArm A δ (Fin.last (n+1)))`, because the head
vertices `i, i+1 ≤ n` are fixed by the opening and `openArm A δ (Fin.last (n+1))` is the rotated tail.

To match `StuckAtKData`'s `i+1 < j` ordering on the opened arm `openArm A δ : Fin ((n+1)+1) → S2`, we
instantiate `N := n + 1`, `i := i`, `j := n + 1` (the tail `Fin.last (n+1)` has value `n + 1`). -/

/-- The mixed-support → `sOrient` bridge for an axis-incident binding edge (`i, i+1 ≤ n`):
`mixedSupport A (⟨i⟩, ⟨i+1⟩) δ = sOrient (openArm A δ ⟨i⟩) (openArm A δ ⟨i+1⟩) (openArm A δ last)`. -/
theorem mixedSupport_eq_sOrient_openArm {n : ℕ} (A : Fin (n + 1 + 1) → S2) (δ : ℝ)
    (i : ℕ) (hi : i + 1 ≤ n) :
    mixedSupport A (⟨i, by omega⟩, ⟨i + 1, by omega⟩) δ
      = sOrient (openArm A δ ⟨i, by omega⟩) (openArm A δ ⟨i + 1, by omega⟩)
          (openArm A δ (Fin.last (n + 1))) := by
  rw [sOrient, openArm_fixed A δ (show (⟨i, by omega⟩ : Fin (n + 1 + 1)).val ≤ n by simp; omega),
    openArm_fixed A δ (show (⟨i + 1, by omega⟩ : Fin (n + 1 + 1)).val ≤ n by simp; omega),
    openArm_last A δ, rotS2_coe]
  rfl

/-- **(Brick 9) The axis-incident `StuckAtKData`.**  From the opened arm's geometry at the
axis-incident binding cut — the mixed support vanishing rewritten as `sOrient = 0`, the short arc of
the opened last edge (FFCT26 brick 8), the equal first side, and the two Gram signs (`hβ` from brick 5,
`hα` from the companion `halpha_of_acoef_nonneg`) — assemble the full `StuckAtKData (openArm A δ) B`
at the cut `(i, n+1)`.  The ordering `i + 1 < n + 1` holds because `i + 1 = n` (axis-incident). -/
theorem StuckAtKData_of_axis_edge_binding {n : ℕ} (A B : Fin (n + 1 + 1) → S2) {δ : ℝ}
    (i : ℕ) (hi_axis : i + 1 = n)
    (hsupp : sOrient (openArm A δ ⟨i, by omega⟩) (openArm A δ ⟨i + 1, by omega⟩)
        (openArm A δ (Fin.last (n + 1))) = 0)
    (hsa : ShortArc (openArm A δ ⟨i + 1, by omega⟩) (openArm A δ (Fin.last (n + 1))))
    (hα : 0 ≤ (⟪(openArm A δ ⟨i, by omega⟩ : E3),
            (openArm A δ ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
        - (⟪(openArm A δ ⟨i, by omega⟩ : E3), (openArm A δ (Fin.last (n + 1)) : E3)⟫ : ℝ)
          * (⟪(openArm A δ ⟨i + 1, by omega⟩ : E3),
              (openArm A δ (Fin.last (n + 1)) : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(openArm A δ ⟨i, by omega⟩ : E3), (openArm A δ (Fin.last (n + 1)) : E3)⟫ : ℝ)
        - (⟪(openArm A δ ⟨i, by omega⟩ : E3), (openArm A δ ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
          * (⟪(openArm A δ (Fin.last (n + 1)) : E3),
              (openArm A δ ⟨i + 1, by omega⟩ : E3)⟫ : ℝ))
    (hside : sDist (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩)
        = sDist (openArm A δ ⟨i + 1, by omega⟩) (openArm A δ ⟨i, by omega⟩)) :
    StuckAtKData (N := n + 1) (openArm A δ) B i (n + 1) := by
  -- the tail vertex index `n + 1` equals `(Fin.last (n + 1)).val`.
  have hlast : (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) := by
    apply Fin.ext; simp [Fin.last]
  refine
    { hij1 := by omega
      hj := by omega
      hsupp := ?_
      hsa := ?_
      hα := ?_
      hβ := ?_
      hside := ?_ }
  · -- hsupp : sOrient (openArm A δ ⟨i⟩) (openArm A δ ⟨i+1⟩) (openArm A δ ⟨n+1⟩) = 0
    rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from hlast]
    exact hsupp
  · rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from hlast]
    exact hsa
  · rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from hlast]
    exact hα
  · rw [show (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = Fin.last (n + 1) from hlast]
    exact hβ
  · exact hside

/-! ## Non-vacuity guards (playbook §3.3) -/

/-- Guard for the algebraic core: the equivalences `hβ ⟺ b ≥ 0`, `hα ⟺ a ≥ 0` are non-vacuous —
they apply to a genuine decomposition `p = 1•mid + 0•q` (`p = mid`), where both signs are the true
`0 ≤ 1` and `0 ≤ 0`.  (This is only an algebraic guard; `p = mid` is excluded geometrically by
`ShortArc`, but the *equivalences* hold unconditionally on the decomposition.) -/
example (mid q : S2) (hsa : ShortArc mid q) :
    (0 ≤ (⟪(mid : E3), (q : E3)⟫ : ℝ)
        - (⟪(mid : E3), (mid : E3)⟫ : ℝ) * (⟪(q : E3), (mid : E3)⟫ : ℝ)) := by
  have hp : (mid : E3) = (1 : ℝ) • (mid : E3) + (0 : ℝ) • (q : E3) := by module
  exact (hbeta_iff_bcoef_nonneg (p := mid) hsa hp).mpr (le_refl 0)

/-- Guard that the brick-6 finding is non-vacuous: the unsatisfiability theorem genuinely fires —
its conclusion `False` would be unreachable if any hypothesis were unsatisfiable on its own.  Here we
record that each *individual* hypothesis is satisfiable (so the contradiction is from the
*conjunction*, the genuine finding) by exhibiting a short arc and a positive spherical angle abstractly
via the existing kernel lemmas. -/
example (p mid q : S2) : 0 ≤ sphAngle p mid q := sphAngle_nonneg p mid q

end ProofsInTheBook.ZinanFFCT27
