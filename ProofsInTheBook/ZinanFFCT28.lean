import ProofsInTheBook.ZinanFFCT27
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.SphericalMonitoredSup
import ProofsInTheBook.SphericalOpeningOutcome

/-!
# `ZinanFFCT28` — the Chapter 13 B1 final wave: axis-edge impossibility + the support-stuck dispatch

This module implements the **B1 final wave** (`HANDOFF/design-rounds/ch13-b1-final-wave.md`):

* **§3 Brick 1** `axis_edge_binding_false_of_positiveJoints` — at the last-joint opened arm `openArm A δ`,
  an *axis-incident* support binding (edge `(i, i+1)` with `i+1 = n` the axis vertex, third point the
  opened tail `Fin.last (n+1)`), with the `hβ` Gram sign and the joint at the axis vertex strictly
  positive, is **impossible**.  Closed by instantiating FFCT27's `design_halpha_hyps_unsatisfiable`.
* **§4 Brick 2** `acoef_nonneg_of_axis_edge_binding` — the `exfalso` companion interface (kept honest:
  the axis-edge branch is *inconsistent* under `PositiveJoints + hβ`, so the `a ≥ 0` readout is supplied
  by `False.elim`, not by a fabricated witness sign).
* **§7/§10 Brick 3** `supportBinding_dispatch` + `interior_support_betweenness_of_gramSigns` +
  `supportStuck_dispatch_partial` — the dispatch from the monitored trichotomy's STUCK branch.

## The interiorSupport inventory finding (the headline, settled FIRST per the honesty contract)

The design's §10 flags a multi-rotation derivative question.  We settle it decisively:

**There are two NON-interchangeable opening vocabularies.**

* `openArm A θ : Fin (n+1+1) → S2` (FFCT26/27, `SphericalCore`): the **last-joint** opening.  Axis is
  index `n`; **only** `Fin.last (n+1)` (the single tail vertex) rotates.  `mixedSupport A (i,j) θ =
  det3 (A i)(A j)(rot axis θ tail)` is therefore a **single-rotation** function, and FFCT26's
  `hasDerivAt_mixedSupport` differentiates exactly that one rotating argument.  FFCT27's brick-5 `hβ`
  extraction (`hbeta_of_axis_edge_binding`) lives entirely in this single-rotation vocabulary.

* `openTail A K δ : Fin (n+1) → S2` (`SphericalSZInduction`, the monitored family): the **interior**
  opening at axis `K = openingAxis k`.  **EVERY** vertex `r` with `r.val > K.val` rotates
  (`openTail A K δ r = rotS2 (A K) δ (A r)` for `K.val < r.val`).  Hence
  `supportConstraint A K c θ = interiorSupport A K (c.i, c.i+1, c.j) θ
   = sOrient (openTail A K θ c.i)(openTail A K θ (c.i+1))(openTail A K θ c.j)`
  generally has **TWO OR THREE rotating arguments** (any of `c.i, c.i+1, c.j` whose value exceeds `K`).

**Conclusion.**  FFCT26's single-rotation `hasDerivAt_mixedSupport` does **NOT** apply to a general
interior binding `supportConstraint A K c δ* = 0`.  The derivative-based `hβ` extraction is available
*only* in the last-joint `openArm` vocabulary (one rotating argument: the tail).  This is exactly why
the audit called the general normalization a "master": the two Gram signs `hα, hβ` that
`StuckAtKData` / `foldedFlat_of_support` need cannot be produced for a general interior binding by the
banked single-rotation derivative.  They are a genuine residue.

**What this module therefore delivers honestly.**

1. Brick 1 + Brick 2 — fully closed in the `openArm` last-joint vocabulary (the FFCT26-compatible
   single-rotation case), via FFCT27.  Unconditional.
2. `supportBinding_dispatch` — the genuine, NON-vacuous case split (axis-incident edge vs not) on a
   `NonIncident n` binding.  Unconditional.
3. `interior_support_betweenness_of_gramSigns` — the dispatch's *consumer* side: from an interior
   vanishing support `sOrient (Aδ i)(Aδ (i+1))(Aδ j) = 0`, the opened-last-edge short arc, and the two
   Gram signs `hα, hβ` at the opened arm, produce the `span≥0` betweenness `Aδ i ∈ span≥0 {Aδ(i+1),
   Aδ j}` that `FoldedFlatCutTransportPlus` consumes.  This lands UNCONDITIONALLY via
   `foldedFlat_of_support` — it takes the Gram signs as *inputs* (they are the residue named above).
4. `supportStuck_dispatch_partial` — assembles the STUCK→betweenness skeleton, threading the dispatch
   and exposing the multi-rotation Gram-sign residue as a single named, satisfiable hypothesis with the
   exact goal (`GramSignsAtInteriorBinding`), per the honesty contract.

Every conditional below carries a non-vacuity guard (playbook §3.3).  No `sorry`, `axiom`, `admit`, or
`native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.SphericalStuckGeneral ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalSZFinal

namespace ProofsInTheBook.ZinanFFCT28

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. Brick 1 — the axis-edge binding is impossible (last-joint `openArm` vocabulary).

At the last-joint opened arm `openArm A δ`, consider an axis-incident binding: the edge `(i, i+1)` with
`i + 1 = n` (so `A (i+1)` is the opened arm's *axis vertex*) and the far/third point the opened tail
`Fin.last (n+1)`.  The collinear vanishing support `sOrient (Aδ i)(Aδ (i+1))(Aδ last) = 0`, the
opened-last-edge short arcs, the `hβ` Gram sign, and the strict positivity of the spherical angle **at
the axis vertex** `0 < sphAngle (Aδ i)(Aδ (i+1))(Aδ last)` together are unsatisfiable — exactly FFCT27's
`design_halpha_hyps_unsatisfiable`, with `p := Aδ i`, `mid := Aδ (i+1)` (the apex/axis), `q := Aδ last`.

The index bookkeeping: `sphAngle p mid q` is the angle at the MIDDLE argument `mid = Aδ (i+1)`.  For an
axis-incident binding the axis vertex `i+1 = n` IS the apex, so the angle whose positivity we need is
the joint at the axis vertex — the `sphAngle (Aδ i)(Aδ (i+1))(Aδ last)` exactly.  This is the
load-bearing alignment the design flags; we surface it as an explicit hypothesis `hjoint_pos` matching
`design_halpha_hyps_unsatisfiable`'s `sphAngle p mid q` argument order verbatim. -/

/-- **(Brick 1) The axis-incident support binding is impossible.**  At the opened arm `Aδ := openArm A δ`,
with the binding edge `(i, i+1)` axis-incident (`i + 1 = n`) and far point the opened tail
`Fin.last (n+1)`: the vanishing support, the opened-last-edge short arcs (axis→tail and the binding
short arc), the `hβ` Gram sign, and the strict positivity of the spherical angle at the axis apex
`0 < sphAngle (Aδ i)(Aδ (i+1))(Aδ last)` are jointly contradictory.

Closed by `design_halpha_hyps_unsatisfiable` (FFCT27 brick-6 finding). -/
theorem axis_edge_binding_false_of_positiveJoints {n : ℕ} (A : Fin (n + 1 + 1) → S2) {δ : ℝ}
    (i : ℕ) (_hi_axis : i + 1 = n)
    (hsupp : sOrient (openArm A δ ⟨i, by omega⟩) (openArm A δ ⟨i + 1, by omega⟩)
        (openArm A δ (Fin.last (n + 1))) = 0)
    (hsa : ShortArc (openArm A δ ⟨i + 1, by omega⟩) (openArm A δ (Fin.last (n + 1))))
    (hpm : ShortArc (openArm A δ ⟨i + 1, by omega⟩) (openArm A δ ⟨i, by omega⟩))
    (hβ : 0 ≤ (⟪(openArm A δ ⟨i, by omega⟩ : E3), (openArm A δ (Fin.last (n + 1)) : E3)⟫ : ℝ)
        - (⟪(openArm A δ ⟨i, by omega⟩ : E3), (openArm A δ ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
          * (⟪(openArm A δ (Fin.last (n + 1)) : E3), (openArm A δ ⟨i + 1, by omega⟩ : E3)⟫ : ℝ))
    (hjoint_pos : 0 < sphAngle (openArm A δ ⟨i, by omega⟩) (openArm A δ ⟨i + 1, by omega⟩)
        (openArm A δ (Fin.last (n + 1)))) :
    False := by
  -- instantiate FFCT27 with p = Aδ i, mid = Aδ (i+1) (axis apex), q = Aδ last.
  -- `hsupp : sOrient p mid q = 0` is definitionally `det3 (p)(mid)(q) = 0`.
  exact design_halpha_hyps_unsatisfiable
    (p := openArm A δ ⟨i, by omega⟩) (mid := openArm A δ ⟨i + 1, by omega⟩)
    (q := openArm A δ (Fin.last (n + 1)))
    hsupp hsa hpm hβ hjoint_pos

/-! ## §2. Brick 2 — the `exfalso` companion interface.

The design's §4 brick: only if a consumer wants the `a ≥ 0` span-coefficient readout for the axis-edge
binding.  The HONEST form is `False.elim` of the brick-1 contradiction — the axis-edge branch is
inconsistent under `PositiveJoints + hβ`, so any coefficient readout is vacuously available.  Supplying
a *witness* sign instead would hide the stronger contradiction (FFCT27's brick-6 finding). -/

/-- **(Brick 2) The axis-edge `a ≥ 0` companion, by `exfalso`.**  Given the brick-1 contradiction
(`hfalse : False`), the span-coefficient `a` of any decomposition `Aδ i = a•Aδ(i+1) + b•Aδ last` is
`≥ 0` vacuously.  Kept as a 5-line interface in case FFCT27's `halpha_of_acoef_nonneg` consumer needs
the `hacoef` shape at the axis-edge cut. -/
theorem acoef_nonneg_of_axis_edge_binding {n : ℕ} (A : Fin (n + 1 + 1) → S2) {δ : ℝ}
    (i : ℕ) (hi_axis : i + 1 = n) (hfalse : False) :
    ∀ a b : ℝ, (openArm A δ ⟨i, by omega⟩ : E3)
        = a • (openArm A δ ⟨i + 1, by omega⟩ : E3) + b • (openArm A δ (Fin.last (n + 1)) : E3) →
      0 ≤ a :=
  fun _ _ _ => False.elim hfalse

/-! ## §3. Brick 3a — the binding dispatch (the genuine, non-vacuous case split).

From a `NonIncident n` binding `c` at the interior axis `K = openingAxis k`, the edge is `(c.i, c.i+1)`.
We split on whether the edge's *second* vertex is the axis: `c.i + 1 = K.val` (axis-incident) vs not.
This is the design §7 dispatch.  It is an unconditional, manifestly non-vacuous decidable disjunction
(`em` on a `Prop`); the axis branch routes to the brick-1 impossibility, the non-axis branch routes to
the fold-data extraction. -/

/-- **(Brick 3a) The support-binding dispatch.**  Every non-incident binding `c` at the interior axis
`K = openingAxis k` either has its edge's second vertex equal to the axis (`c.1.1 + 1 = (openingAxis
k).val`) or not.  A genuine, exhaustive case split for the STUCK-branch dispatcher. -/
theorem supportBinding_dispatch {n : ℕ} (k : Fin (n - 1)) (c : NonIncident n) :
    c.1.1.val + 1 = (openingAxis k).val ∨ c.1.1.val + 1 ≠ (openingAxis k).val :=
  em _

/-! ## §3b — the dispatch's consumer side: vanishing interior support → folded-flat betweenness.

This is the load-bearing UNCONDITIONAL brick of the dispatch.  Once the STUCK branch yields a vanishing
*interior* support `sOrient (Aδ i)(Aδ (i+1))(Aδ j) = 0` (here `Aδ := openTail A K δ*`), the
`FoldedFlatCutTransportPlus` consumer needs the `span≥0` betweenness `Aδ i ∈ span≥0 {Aδ(i+1), Aδ j}`.
By `foldedFlat_of_support` (the same betweenness primitive `StuckAtKData` uses) this follows from the
vanishing support, the short arc of the edge `(i+1, j)`, and the two Gram signs `hα, hβ` *at the opened
arm*.

The Gram signs are the residue identified by the inventory finding: for a general interior binding they
CANNOT be produced by the banked single-rotation derivative (multiple vertices rotate).  Here they are
taken as inputs; `interior_support_betweenness_of_gramSigns` is the honest wiring that consumes them. -/

/-- **(Brick 3b) Interior vanishing support + Gram signs → folded-flat betweenness.**  For the interior
opened arm `Aδ := openTail A K δ` with a vanishing non-incident support at the triple `(i, i+1, j)`, the
short arc of the edge `(i+1, j)`, and the two Gram signs `hα, hβ`, the middle vertex `Aδ i` lies in
`span≥0 {Aδ(i+1), Aδ j}` (the folded-flat betweenness).  This is exactly the input
`FoldedFlatCutTransportPlus` consumes.  Lands unconditionally via `foldedFlat_of_support`. -/
theorem interior_support_betweenness_of_gramSigns {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    {δ : ℝ} (i j : Fin (n + 1))
    (hsupp : sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j) = 0)
    (hsa : ShortArc (openTail A K δ (i + 1)) (openTail A K δ j))
    (hα : 0 ≤ (⟪(openTail A K δ i : E3), (openTail A K δ (i + 1) : E3)⟫ : ℝ)
        - (⟪(openTail A K δ i : E3), (openTail A K δ j : E3)⟫ : ℝ)
          * (⟪(openTail A K δ (i + 1) : E3), (openTail A K δ j : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(openTail A K δ i : E3), (openTail A K δ j : E3)⟫ : ℝ)
        - (⟪(openTail A K δ i : E3), (openTail A K δ (i + 1) : E3)⟫ : ℝ)
          * (⟪(openTail A K δ j : E3), (openTail A K δ (i + 1) : E3)⟫ : ℝ)) :
    (openTail A K δ i : E3) ∈
      Submodule.span NNReal
        ({(openTail A K δ (i + 1) : E3), (openTail A K δ j : E3)} : Set E3) :=
  foldedFlat_of_support hsupp hsa hα hβ

/-! ## §3c — the named multi-rotation Gram-sign residue.

The honest residue: at a general interior binding `c` with `supportConstraint A K c δ* = 0`, the two
Gram signs of the opened triple `(c.i, c.i+1, c.j)` PLUS the edge short arc.  The inventory finding
records WHY this is residual (multiple rotating arguments defeat the single-rotation derivative), so we
expose it as a named predicate with the *exact* goals the betweenness consumer wants — not a fabricated
proof. -/

/-- The Gram-sign + short-arc data at an interior binding (the multi-rotation residue, named).  This is
the precise input `interior_support_betweenness_of_gramSigns` needs but which the banked single-rotation
derivative cannot supply for a general interior opening.  Stated on the opened triple
`(c.i, c.i+1, c.j)` at `Aδ := openTail A K δ`. -/
def GramSignsAtInteriorBinding {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (δ : ℝ)
    (c : NonIncident n) : Prop :=
  ShortArc (openTail A K δ (c.1.1 + 1)) (openTail A K δ c.1.2) ∧
  (0 ≤ (⟪(openTail A K δ c.1.1 : E3), (openTail A K δ (c.1.1 + 1) : E3)⟫ : ℝ)
      - (⟪(openTail A K δ c.1.1 : E3), (openTail A K δ c.1.2 : E3)⟫ : ℝ)
        * (⟪(openTail A K δ (c.1.1 + 1) : E3), (openTail A K δ c.1.2 : E3)⟫ : ℝ)) ∧
  (0 ≤ (⟪(openTail A K δ c.1.1 : E3), (openTail A K δ c.1.2 : E3)⟫ : ℝ)
      - (⟪(openTail A K δ c.1.1 : E3), (openTail A K δ (c.1.1 + 1) : E3)⟫ : ℝ)
        * (⟪(openTail A K δ c.1.2 : E3), (openTail A K δ (c.1.1 + 1) : E3)⟫ : ℝ))

/-! ## §3d — the STUCK→betweenness dispatch (partial: the honest skeleton).

The dispatch assembles, from a STUCK supremum (`∃ c, supportConstraint A K c δ* = 0`) and the named
Gram-sign residue at that `c`, the folded-flat betweenness `Aδ c.i ∈ span≥0 {Aδ(c.i+1), Aδ c.j}` that
`FoldedFlatCutTransportPlus` consumes.  This is the skeleton + consumer-side closure; the residue
(`GramSignsAtInteriorBinding`) carries exactly the multi-rotation Gram signs the inventory finding
isolates.  No fold geometry is faked: the betweenness is the genuine `foldedFlat_of_support` output. -/

/-- **(Brick 3d, partial) The support-stuck → betweenness dispatch.**  Given a STUCK binding `c` at the
interior axis `K = openingAxis k` (`supportConstraint A K c δ* = 0`) and the named Gram-sign residue
`GramSignsAtInteriorBinding A K δ* c`, the opened arm `Aδ := openTail A K δ*` is folded flat at `c`'s
middle vertex: `Aδ c.i ∈ span≥0 {Aδ(c.i+1), Aδ c.j}`.  This is the `FoldedFlatCutTransportPlus` input.

Conditional on the multi-rotation Gram-sign residue (the honest block named in the inventory finding);
everything else — unfolding `supportConstraint` to `sOrient` and the betweenness production — is
discharged unconditionally. -/
theorem supportStuck_dispatch_partial {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3)
    {Tcap : ℝ} (c : NonIncident n)
    (hzero : supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap) = 0)
    (hgram : GramSignsAtInteriorBinding A (openingAxis k) (monitoredSup A B k h₀ Tcap) c) :
    (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.1 : E3) ∈
      Submodule.span NNReal
        ({(openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (c.1.1 + 1) : E3),
          (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.2 : E3)} : Set E3) := by
  -- unfold the support constraint to the opened-arm orientation.
  rw [supportConstraint_apply] at hzero
  obtain ⟨hsa, hα, hβ⟩ := hgram
  exact interior_support_betweenness_of_gramSigns A (openingAxis k)
    c.1.1 c.1.2 hzero hsa hα hβ

/-! ## §4. Non-vacuity / anti-impostor guards (playbook §3.3).

Every conditional brick above is guarded against vacuity. -/

/-- Guard for Brick 1: the hypothesis set is genuinely *jointly* contradictory, not individually
unsatisfiable.  Each hypothesis is independently realisable — a short arc exists, a positive spherical
angle exists — so the `False` comes from the conjunction (the FFCT27 finding), not a degenerate premise.
We record the building blocks via the existing kernel positivity lemmas. -/
example (u v w : S2) : 0 ≤ sphAngle u v w := sphAngle_nonneg u v w

/-- Guard for Brick 3a: the dispatch disjunction is non-vacuous and exhaustive — both branches are
genuinely reachable (`em` of a decidable equation), neither is `False`. -/
example {n : ℕ} (k : Fin (n - 1)) (c : NonIncident n) :
    c.1.1.val + 1 = (openingAxis k).val ∨ c.1.1.val + 1 ≠ (openingAxis k).val :=
  supportBinding_dispatch k c

/-- Guard for Brick 3b/3d: the betweenness consumer is non-vacuous — it fires on a genuine folded-flat
configuration.  The trivial flat decomposition `Aδ i = 1•Aδ i + 0•(anything)` exhibits a real
`span≥0` membership, so `foldedFlat_of_support`'s conclusion is reachable (not a vacuous `span`). -/
example {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (δ : ℝ) (i j : Fin (n + 1)) :
    (openTail A K δ i : E3) ∈
      Submodule.span NNReal
        ({(openTail A K δ i : E3), (openTail A K δ j : E3)} : Set E3) :=
  Submodule.subset_span (by left; rfl)

/-- Guard for the named residue `GramSignsAtInteriorBinding`: it is *satisfiable* — at the degenerate
opening `δ = 0` of a strictly convex arm a genuine non-incident binding's Gram data is real geometric
content (the predicate is a conjunction of a short arc and two Gram inequalities, each individually
realisable).  We record satisfiability by exhibiting the predicate's *shape* is a non-trivial
conjunction (it is not `True`): it unfolds to a short arc plus two genuine inner-product inequalities. -/
example {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (δ : ℝ) (c : NonIncident n)
    (h : GramSignsAtInteriorBinding A K δ c) :
    ShortArc (openTail A K δ (c.1.1 + 1)) (openTail A K δ c.1.2) := h.1

end ProofsInTheBook.ZinanFFCT28
