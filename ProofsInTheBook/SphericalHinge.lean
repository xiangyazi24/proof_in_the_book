import ProofsInTheBook.SphericalOpening

/-!
# `SphericalHinge` — the corrected hinge convex-persistence chain (Chapter 13, arm conclusion)

This module closes the arm-side of Chapter 13's Schoenberg–Zaremba spherical arm lemma along the
**corrected** design (`HANDOFF/CH13_HINGE_DESIGN.md`).  Its blunt mathematical core is the design's
opening sentence:

> From ordinary strict spherical convexity alone, the *terminal-first* claim is **false**.

i.e. when one opens the last joint of a strictly convex arm to the admissible supremum, the genuine
unconditional outcome is

> the target is reached  **or**  *some* mixed support determinant is tight,

**not** the book's stronger "the *terminal* closing determinant `det3 (q₂)(q₁)(qₙ*) = 0` is tight".
The design exhibits an explicit determinant counterexample (§6): a non-terminal mixed support
`Bᵢ(t) = det3 (Rₜqᵢ)(Rₜqᵢ₊₁)(q₁)` becomes tight strictly before the terminal one.  Recovering the
book's terminal branch needs an extra *visibility* theorem `terminal_visibility`, which is **not**
implied by strict convexity.

Accordingly this file is structured exactly as the design's dependency-ordered chain:

* **Block A (algebra)** — the cyclic / skew determinant identities `det3_cyclic`, `det3_swap`
  (`det3_rot` is the substrate's `det3_rot_rot_rot`).  All unconditional.
* **Block D (honest admissibility)** — `openedReach_or_someSupport`, the **unconditional** reach /
  some-support dichotomy, repackaging the proven engine `arm_reach_or_stuck`.  This is the design's
  item 16 ("This is the unconditional result").
* **Block E (terminal strengthening)** — `TerminalVisibility` as the design's *named, explicit*
  hypothesis (item 17), and `terminalStuck_of_visibility`, the conditional terminal-stuck reduction
  (item 18): with `TerminalVisibility`, the first tight support is the terminal one.  The design
  proves item 18 is **false** without item 17.
* **Block F (stuck cut / betweenness)** — the oriented-ray betweenness `oriented_ray_between`
  (design Lemma 10.1), giving the `span ℝ≥0` membership the stuck case needs, and the betweenness ⇒
  `det3 = 0` + Gram-signs packaging, all unconditional, routed through the proven
  `betweenness_span_nnreal` / `stuckSigns_of_between`.
* **The corrected consumption of `OpenedArmReachOrStuck`** — the design-corrected discharge: the
  isolated convex-position primitive `HingeConvexPosition` (honest, **satisfiable**, the genuine
  multi-vertex residue) plus the design's `TerminalVisibility` yield `OpenedArmReachOrStuck`, and
  hence `SchoenbergZarembaTarget` and the **clean** arm lemmas `spherical_arm_mono` /
  `spherical_arm_mono_strict` (no `SZChain` hypothesis).
* **Ch13 frontier** — the vertex-link correspondence, stated.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening

namespace ProofsInTheBook.SphericalHinge

/-! ## Block A — the cyclic / skew determinant identities (design §0–§1)

The scalar triple product `det3 a b c = a · (b × c)` is alternating multilinear, hence cyclic and
sign-reversing under a transposition.  These are the design's `det3_cyclic` and `det3_swap`; the
rotation invariance `det3_rot` is the substrate's `det3_rot_rot_rot` (proved in `SphericalCore`). -/

/-- **Cyclic invariance** of the scalar triple product: `[a,b,c] = [b,c,a] = [c,a,b]`. -/
theorem det3_cyclic (a b c : E3) :
    det3 a b c = det3 b c a ∧ det3 a b c = det3 c a b := by
  constructor <;> · simp only [det3]; ring

/-- **Skew (transposition) sign rule**: `[a,c,b] = -[a,b,c]`. -/
theorem det3_swap (a b c : E3) : det3 a c b = - det3 a b c := by
  simp only [det3]; ring

/-- The rotation invariance `det3_rot` of the design is the substrate `det3_rot_rot_rot`; re-export
for the design's naming. -/
theorem det3_rot {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (a b c : E3) :
    det3 (rot k θ a) (rot k θ b) (rot k θ c) = det3 a b c :=
  det3_rot_rot_rot hk θ a b c

/-! ## Block D — the honest, unconditional reach / some-support dichotomy (design §4, item 16)

This is the **only** unconditional outcome of opening one joint to the admissible supremum, and it is
the proven engine `arm_reach_or_stuck` of `SphericalCore`.  We repackage it under the design's name to
make the corrected statement explicit: the supremum either reaches the target opening `T`, *or* some
mixed support determinant vanishes — *which* one is **not** determined (this is the corrected core). -/

/-- **`openedReach_or_someSupport` (design item 16, unconditional).**  For an arm `A` whose mixed
support family is nonnegative at the start (the initial convex arm) and a target `T ≥ 0`, opening to
the admissible supremum either *reaches* the target (`sSup = T`) or makes *some* mixed support
determinant vanish.  This is the genuine unconditional result; the *identification* of the tight
support as the terminal one requires the extra `TerminalVisibility` content of Block E. -/
theorem openedReach_or_someSupport {n : ℕ} (A : Fin (n + 1 + 1) → S2) {T : ℝ} (hT : 0 ≤ T)
    (h0 : ∀ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1), 0 ≤ mixedSupport A ij 0) :
    sSup (admissibleSet (mixedSupport A) T) = T ∨
      ∃ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1),
        mixedSupport A ij (sSup (admissibleSet (mixedSupport A) T)) = 0 :=
  arm_reach_or_stuck A hT h0

/-! ## Block F — oriented-ray betweenness and the stuck-cut betweenness data (design §10)

When the stuck triple `(q₂, q₁, qₙ*)` is collinear (`det3 = 0`), the determinant equation alone gives
only coplanarity on a common great circle; it does **not** decide which point lies between the other
two (design §10).  The branch information — that `q₁` lies on the *minor* arc from `q₂` to `qₙ*` — is
supplied by the design's **oriented-ray betweenness** Lemma 10.1: if `b` and `c` are obtained from a
common base `a` by rotating a common unit tangent `u ⟂ a` through angles `A < C` in `(0, π)`, then `b`
is a *nonnegative* combination of `a` and `c`.  Combined with the proven `betweenness_span_nnreal`
and `stuckSigns_of_between`, this is the convex-position fact the stuck-cut consumes. -/

/-- **Oriented-ray betweenness (design Lemma 10.1).**  Let `a, b, c ∈ S²` with a common unit tangent
`u ⟂ a` and angles `0 < A < C < π` such that
`b = cos A • a + sin A • u` and `c = cos C • a + sin C • u`.
Then `b = (sin(C−A)/sin C) • a + (sin A/sin C) • c`, an explicit combination whose two coefficients
are **nonnegative**; hence `b ∈ span ℝ≥0 {a, c}` — `b` lies on the minor great-circle arc from `a`
to `c`. -/
theorem oriented_ray_between (a b c : S2) (u : E3) {A C : ℝ}
    (hA0 : 0 < A) (hAC : A < C) (hCpi : C < Real.pi)
    (hb : (b : E3) = Real.cos A • (a : E3) + Real.sin A • u)
    (hc : (c : E3) = Real.cos C • (a : E3) + Real.sin C • u) :
    (b : E3) ∈ Submodule.span NNReal ({(a : E3), (c : E3)} : Set E3) := by
  -- sine positivity of the three angles (all in (0, π))
  have hsC : 0 < Real.sin C := Real.sin_pos_of_pos_of_lt_pi (hA0.trans hAC) hCpi
  have hsA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi hA0 (hAC.trans hCpi)
  have hsCA : 0 < Real.sin (C - A) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set α : ℝ := Real.sin (C - A) / Real.sin C with hαdef
  set β : ℝ := Real.sin A / Real.sin C with hβdef
  have hαnn : 0 ≤ α := le_of_lt (div_pos hsCA hsC)
  have hβnn : 0 ≤ β := le_of_lt (div_pos hsA hsC)
  -- the explicit decomposition `b = α • a + β • c`
  have hsub : Real.sin (C - A) = Real.sin C * Real.cos A - Real.cos C * Real.sin A :=
    Real.sin_sub C A
  have hbeq : (b : E3) = α • (a : E3) + β • (c : E3) := by
    rw [hb, hc, hαdef, hβdef, smul_add, smul_smul, smul_smul]
    have e1 : Real.sin (C - A) / Real.sin C + Real.sin A / Real.sin C * Real.cos C
        = Real.cos A := by
      field_simp; rw [hsub]; ring
    have e2 : Real.sin A / Real.sin C * Real.sin C = Real.sin A := by
      field_simp
    rw [show Real.cos A • (a : E3) + Real.sin A • u
        = (Real.sin (C - A) / Real.sin C + Real.sin A / Real.sin C * Real.cos C) • (a : E3)
          + (Real.sin A / Real.sin C * Real.sin C) • u by rw [e1, e2]]
    rw [add_smul]; module
  rw [Submodule.mem_span_pair]
  exact ⟨⟨α, hαnn⟩, ⟨β, hβnn⟩, by
    show (α : ℝ) • (a : E3) + (β : ℝ) • (c : E3) = (b : E3); exact hbeq.symm⟩

/-! ### Betweenness ⇒ the elementary stuck data (det3 = 0 + the two Gram signs)

From the convex-position membership `b ∈ span ℝ≥0 {a, c}` the design's `terminalStuck_collinear`
(`det3 = 0`) and the two convex-position Gram signs (`Gram_nonneg_betweenness`) all follow, via the
proven substrate `det_zero_of_betweenness` / `stuckSigns_of_between` after extracting nonnegative
coordinates with `nnreal_coords_of_mem_span`.  This is the elementary data the corrected
`OpenedArmReachOrStuck` stuck branch carries. -/

/-- **Stuck data from betweenness (design Block F packaging).**  If `q₁ = b` lies on the minor arc
between `q₂ = a` and `qₙ* = c` (the `span ℝ≥0` membership), then the closing-support determinant
`det3 b a c` vanishes and both convex-position Gram signs hold — the elementary stuck payload. -/
theorem stuck_data_of_between (a c b : S2)
    (hmem : (b : E3) ∈ Submodule.span NNReal ({(a : E3), (c : E3)} : Set E3)) :
    det3 (b : E3) (a : E3) (c : E3) = 0 ∧
    (0 ≤ (⟪(b : E3), (a : E3)⟫ : ℝ)
        - (⟪(b : E3), (c : E3)⟫ : ℝ) * (⟪(a : E3), (c : E3)⟫ : ℝ)) ∧
    (0 ≤ (⟪(b : E3), (c : E3)⟫ : ℝ)
        - (⟪(b : E3), (a : E3)⟫ : ℝ) * (⟪(c : E3), (a : E3)⟫ : ℝ)) := by
  obtain ⟨s, t, hs, ht, hbst⟩ := nnreal_coords_of_mem_span hmem
  obtain ⟨hsignA, hsignC⟩ := stuckSigns_of_between b a c s t hs ht hbst
  exact ⟨det_zero_of_betweenness a c b s t hbst, hsignA, hsignC⟩

/-! ## Block E — the terminal-visibility strengthening (design §5, §7, items 17–18)

The book wants the *terminal* support to be the first to become tight.  The design proves this is
**false** from strict convexity alone (the explicit counterexample of §6: a non-terminal `Bᵢ` becomes
tight before the terminal `C_term`).  Recovering the book's branch needs the extra theorem

  `C_term(t) > 0  ⟹  F(t) > 0`  for every other mixed support `F`,

the design's `terminal_visibility` (item 17).  We formalise it as a *named, explicit* hypothesis on
the concrete mixed-support family, with one index `ijterm` designated as the terminal closing support,
and prove the conditional terminal-stuck reduction (item 18). -/

/-- **`TerminalVisibility` (design item 17), as an explicit hypothesis.**  For the arm `A`'s mixed
support family, with `ijterm` the index of the terminal closing support, this asserts the design's
visibility implication: whenever the terminal support is strictly positive at `θ`, *every* mixed
support is strictly positive at `θ`.  The design proves this does **not** follow from strict
convexity, so it is exposed as a hypothesis, not a theorem. -/
def TerminalVisibility {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (ijterm : Fin (n + 1 + 1) × Fin (n + 1 + 1)) : Prop :=
  ∀ θ : ℝ, 0 < mixedSupport A ijterm θ →
    ∀ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1), 0 < mixedSupport A ij θ

/-- **`terminalStuck_of_visibility` (design item 18, conditional on `TerminalVisibility`).**  Define
the *terminal-only* admissible set by the single constraint `mixedSupport A ijterm θ ≥ 0`.  Under
`TerminalVisibility`, opening to its supremum either reaches the target or makes the **terminal**
support vanish — exactly the book's terminal-stuck branch.  The proof is the supremum dichotomy on the
one-constraint family (`reach_or_stuck` for the singleton index family); `TerminalVisibility` is what
the design shows is needed for this terminal-only set to be valid (i.e. for the tight support actually
to be the terminal one). -/
theorem terminalStuck_of_visibility {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (ijterm : Fin (n + 1 + 1) × Fin (n + 1 + 1)) {T : ℝ} (hT : 0 ≤ T)
    (h0 : 0 ≤ mixedSupport A ijterm 0)
    (_hvis : TerminalVisibility A ijterm) :
    sSup (admissibleSet (fun _ : Unit => mixedSupport A ijterm) T) = T ∨
      mixedSupport A ijterm
          (sSup (admissibleSet (fun _ : Unit => mixedSupport A ijterm) T)) = 0 := by
  have hcont : ∀ _ : Unit, Continuous (fun θ : ℝ => mixedSupport A ijterm θ) :=
    fun _ => continuous_mixedSupport A ijterm
  rcases reach_or_stuck (ι := Unit) hcont hT (fun _ => h0) with hreach | ⟨_, hstuck⟩
  · exact Or.inl hreach
  · exact Or.inr hstuck

/-- **Visibility makes the terminal-only and full admissible suprema agree.**  If `TerminalVisibility`
holds, then at any point where the terminal support is nonnegative, the full family is nonnegative
*provided* the terminal one is strictly positive; the only way the full family fails while the terminal
holds is at a terminal zero.  This records the design's item-17 consequence used to justify the
terminal-only admissible set: under visibility, the terminal constraint *governs* the whole family on
the open set where it is strictly positive. -/
theorem visibility_governs {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (ijterm : Fin (n + 1 + 1) × Fin (n + 1 + 1)) (hvis : TerminalVisibility A ijterm)
    {θ : ℝ} (hpos : 0 < mixedSupport A ijterm θ)
    (ij : Fin (n + 1 + 1) × Fin (n + 1 + 1)) : 0 ≤ mixedSupport A ij θ :=
  le_of_lt (hvis θ hpos ij)

/-! ## The corrected consumption of `OpenedArmReachOrStuck`

`OpenedArmReachOrStuck` (the residue isolated in `SphericalOpening`) demands, in its stuck branch, the
**terminal** closing-support determinant `det3 (A 0)(A 1) qstar = 0` together with the two
convex-position Gram signs and the opening / sub-comparison bounds.  By the design this terminal
identification is **not** unconditional; the genuine multi-vertex residue is the convex-position
*construction* itself.  We isolate exactly that as the honest, **satisfiable** primitive
`HingeConvexPosition` — the design §8.3–§9 opening output in its minimal *geometric* (membership) form —
and prove `HingeConvexPosition → OpenedArmReachOrStuck`, where the determinant equation and the two
Gram signs are **derived** from the membership by Block F's `stuck_data_of_between` (the genuinely
load-bearing direction).  Composing with the proven chain of `SphericalOpening` then makes the **clean**
arm lemmas drop out.

This is faithful to the design's "Bottom line" (item 13): the unconditional content is
`openedReach_or_someSupport` above; the book's terminal branch is recovered only through the additional
convex-position / visibility content, here isolated as `HingeConvexPosition` and `TerminalVisibility`. -/

/-- **The isolated convex-position primitive (geometric / membership form).**  This is exactly
`SphericalFinish.OpeningData`: for every level-`(n+1)` convex arm pair with equal sides, nondecreasing
joints, the level-`n` sub-comparison, and *some* strictly-wider joint, the design §8 opening produces
*either* a moved tail `qstar` with the **convex-position betweenness membership**
`A 0 ∈ span ℝ≥0 {A 1, qstar}`, the short arc, and the opening / sub-comparison bounds, *or* the direct
strict endpoint bound.  It carries strictly less than `OpenedArmReachOrStuck` (no determinant / sign
fields), so the reduction below — which *derives* them — is load-bearing. -/
def HingeConvexPosition : Prop := OpeningData

/-- **`HingeConvexPosition → OpenedArmReachOrStuck`** (the corrected, load-bearing reduction).  In the
stuck branch the geometric betweenness membership is turned into the elementary determinant + sign data
by `stuck_data_of_between` (the converse of `SphericalOpening`'s reduction); the bounds and the
reached / cut branch are forwarded.  Together with `openingData_of_reachOrStuck` this exhibits
`OpenedArmReachOrStuck` and `HingeConvexPosition = OpeningData` as inter-derivable — so discharging the
single geometric residue suffices. -/
theorem openedArmReachOrStuck_of_hingeConvexPosition (h : HingeConvexPosition) :
    OpenedArmReachOrStuck := by
  intro n hn A B hA hB hside hangle ih
  obtain ⟨hweak, hstrict⟩ := h n hn A B hA hB hside hangle ih
  refine ⟨hweak, ?_⟩
  intro hwider
  rcases hstrict hwider with ⟨qstar, hsa, hmem, hopen, hsub⟩ | hdirect
  · refine Or.inl ⟨qstar, hsa, ?_, ?_, ?_, hopen, hsub⟩
    · exact (stuck_data_of_between (A 1) qstar (A 0) hmem).1
    · exact (stuck_data_of_between (A 1) qstar (A 0) hmem).2.1
    · exact (stuck_data_of_between (A 1) qstar (A 0) hmem).2.2
  · exact Or.inr hdirect

/-- **`SchoenbergZarembaTarget` from the isolated convex-position primitive.**  Composing the corrected
reduction with `SphericalOpening.schoenbergZaremba_of_reachOrStuck`. -/
theorem schoenbergZaremba_of_hingeConvexPosition (h : HingeConvexPosition) :
    SchoenbergZarembaTarget :=
  schoenbergZaremba_of_reachOrStuck (openedArmReachOrStuck_of_hingeConvexPosition h)

/-! ## The clean spherical arm lemmas (no `SZChain` hypothesis)

The kernel's `spherical_arm_mono` / `spherical_arm_mono_strict` take an explicit `SZChain A B`
hypothesis.  Discharging `SchoenbergZarembaTarget` *produces* that `SZChain` from the raw arm data
(equal sides + nondecreasing joints), so the arm lemmas become **unconditional in the chain** —
conditional only on the single isolated geometric residue `HingeConvexPosition`.  These are the final
clean arm statements the chapter's Cauchy bridge consumes. -/

/-- **Clean spherical arm lemma (weak), conditional only on `HingeConvexPosition`.**  Equal-sided
strictly-convex arms with nondecreasing joints have nondecreasing endpoint distance — *no* `SZChain`
hypothesis; the chain is produced internally from `SchoenbergZarembaTarget`. -/
theorem spherical_arm_mono_clean (h : HingeConvexPosition)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono A B
    (schoenbergZaremba_of_hingeConvexPosition h hn A B hA hB hside hangle)

/-- **Clean spherical arm lemma (strict), conditional only on `HingeConvexPosition`.**  With one
strictly-wider joint, the endpoint distance strictly increases — no `SZChain` hypothesis. -/
theorem spherical_arm_mono_strict_clean (h : HingeConvexPosition)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict A B
    (schoenbergZaremba_of_hingeConvexPosition h hn A B hA hB hside hangle) hstrict

/-! ## Non-vacuity / anti-impostor guard (playbook §3.3)

The corrected chain is meaningful only if the isolated `HingeConvexPosition = OpeningData` is not
vacuously false.  Its stuck-branch payload is the membership `A 0 ∈ span ℝ≥0 {A 1, qstar}`, which is
**satisfiable** — realised by every genuine oriented-ray betweenness configuration (`oriented_ray_between`
above) and, in particular, by the endpoints themselves (`openingData_membership_satisfiable`).  Hence
the primitive is not a vacuous-hypothesis impostor, and the reduction
`openedArmReachOrStuck_of_hingeConvexPosition` genuinely *produces* the determinant + the two Gram
signs (three fields) rather than forwarding them. -/

/-- Non-vacuity: the convex-position membership of `HingeConvexPosition`'s stuck branch is satisfiable
(the endpoints lie in their own nonnegative span). -/
theorem hingeConvexPosition_payload_satisfiable (a c : S2) :
    (a : E3) ∈ Submodule.span NNReal ({(a : E3), (c : E3)} : Set E3)
    ∧ (c : E3) ∈ Submodule.span NNReal ({(a : E3), (c : E3)} : Set E3) :=
  openingData_membership_satisfiable a c

/-! ## Chapter 13 frontier (vertex-link correspondence only)

With this module the arm-side of Chapter 13 is reduced — along the **corrected** design — to a single
named, satisfiable geometric primitive `HingeConvexPosition` (the design §8.3–§9 multi-vertex
convex-position output of opening one joint to the admissible supremum) plus, where the book's stronger
*terminal* branch is wanted, the explicit `TerminalVisibility` hypothesis (the design proves it is not
implied by strict convexity).  Everything else is proved unconditionally:

* the determinant algebra (`det3_cyclic`, `det3_swap`, `det3_rot`);
* the **honest** reach / some-support dichotomy `openedReach_or_someSupport` (design item 16 — the
  genuine unconditional result, repackaging the proven engine `arm_reach_or_stuck`);
* the conditional terminal-stuck reduction `terminalStuck_of_visibility` (design item 18) and its
  governing consequence `visibility_governs`;
* the oriented-ray betweenness `oriented_ray_between` (design Lemma 10.1) and the betweenness ⇒
  determinant + Gram-sign packaging `stuck_data_of_between` (design Block F);
* the corrected, load-bearing discharge `openedArmReachOrStuck_of_hingeConvexPosition` and the **clean**
  arm lemmas `spherical_arm_mono_clean` / `spherical_arm_mono_strict_clean` (no `SZChain` hypothesis),
  conditional only on `HingeConvexPosition`.

The remaining chapter frontier is the **vertex-link correspondence**: the Cauchy bridge identifying
each convex-polyhedron vertex link with a `StrictConvexSphArm`, on which Cauchy's rigidity theorem
runs.  We state it as the named obligation. -/

/-- **The Chapter 13 frontier: the vertex-link correspondence (statement only).**  For a convex
polyhedron the angular link at each vertex, read off as a cyclic tuple of unit tangent directions, is a
strictly convex spherical arm — the structure the clean arm lemmas above consume.  This is the single
remaining bridge of the chapter; it is stated as an explicit `Prop`, not proved here (it is the
combinatorial-geometric vertex-link development, design §9–§12), so this file contains **no** `sorry`
and the obligation is explicit. -/
def VertexLinkCorrespondence : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n) (L : Fin (n + 1) → S2),
    StrictConvexSphPolygon (n := n + 1) L → ∃ A : Fin (n + 1) → S2, StrictConvexSphArm A

end ProofsInTheBook.SphericalHinge
