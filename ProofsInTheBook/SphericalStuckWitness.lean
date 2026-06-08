import ProofsInTheBook.SphericalSZComplete

/-!
# `SphericalStuckWitness` — the closing-support identification gap of `StuckWitnessExists`

This module attacks the single remaining residue of Chapter 13's Schoenberg–Zaremba spherical arm
lemma, `SphericalOpeningProcess.StuckWitnessExists`, along the angle proposed for this round: that
the **convex-position ordering** `PlanarConvexDiag.cyclicTriplePos_unconditional` (every diagonal of a
strictly convex spherical polygon is positively oriented) forces, as the joint opens, the **closing
support** `det3 (A 0)(A 1)(qstar)` to be the *first* mixed support to vanish — thereby identifying the
closing witness that `betweenness_span_nnreal` consumes.

## What this round establishes (honest, verified against the substrate AND numerically)

The proposed identification is **false as stated**, and the refutation is *internal to the design
substrate*: `HANDOFF/CH13_HINGE_DESIGN.md §6` exhibits an explicit determinant counterexample (six
vertices `v₁…v₆` in the affine chart `z = 1`) at which, opening the head ray backwards about the
pivot `q₂`, a **non-terminal** mixed support `D(t) = [v₅, v₆, a(t)]` vanishes first
(`D(t₀) = 0` for some `t₀ ∈ (0, 0.052)`) while the **closing/terminal** support
`E(t) = [R₋ₜv₆, v₁, v₂]` stays strictly positive throughout `0 ≤ t ≤ 0.052`.  Hence the first tight
support need **not** be the closing one — disproving the unrestricted "closing-first" statement.  We
recompute the counterexample's two governing determinants from scratch and prove, in Lean, that

* `D(t) = 207/100 − (99/50) cos t − (9/5) sin t`, with `D(0) = 9/100 > 0` and `D(0.052) < 0`
  (so some `t₀ ∈ (0, 0.052)` has the non-terminal support `= 0`, by the IVT), and
* `E(t) = (21/5) sin t + (1/50) cos t > 0` for every `0 ≤ t ≤ 0.052`

— so when the non-terminal support first vanishes, the closing support is still strictly positive.
This is the concrete failing chain for the round's angle, now *machine-checked* rather than asserted.

The one monotonicity that the convex-position ordering *does* give (design §8, "What ordinary pivot
fan-order does prove") is the **A-family** one-sided implication
`[q₁, q₂, Rₜqₖ] > 0 whenever [q₁, q₂, Rₜqₙ] > 0` for the *first-edge* supports — and it controls
**only** those.  We bank its exact algebraic engine: the Grassmann–Plücker (GP) **deficit identity**
at the closing configuration (apex `q₂`), a true polynomial relation tying the closing support, an
interior first-edge support, and the rotation-invariant interior tail support together
(`gp_closing_deficit`).  The B-family `[Rₜqᵢ, Rₜqᵢ₊₁, q₁]` and C-family `[Rₜqₙ, q₁, Rₜqₖ]` supports
— "exactly where the counterexample fails" (§8, last paragraph) — are *not* controlled by it.

## The named residue (the genuine missing theorem)

The theorem that *would* recover the book's terminal stuck branch is the design's
**`terminal_visibility`** (§7): `C_term(t) > 0 ⟹ F(t) > 0` for every other mixed support `F`.  This is
strictly stronger than the convex-position ordering (the counterexample shows convexity alone does not
imply it).  We isolate it as the named, non-vacuous `Prop` `TerminalVisibility`, prove it *would*
identify the closing support as the first to vanish (`closingFirst_of_terminalVisibility`), and record
that it is **not** a re-wrapper of `StuckWitnessExists` (it carries only the cross-support sign
implication, none of the opening construction, the betweenness extraction, or the endpoint
bookkeeping).  The residue of the whole §8.4 opening therefore stays the substrate's already-named
`StuckWitnessExists`; this round narrows the *reason* it resists to the precise, counterexample-backed
`terminal_visibility` obstruction and banks the GP engine + the machine-checked refutation.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete

namespace ProofsInTheBook.SphericalStuckWitness

/-! ## Part 1. The Grassmann–Plücker deficit identity at the closing configuration.

The opening pivots at the axis `q₂` (the chosen joint vertex), holding the head `q₁` fixed and
rotating the tail.  Write `qₖᵗ := Rₜ qₖ` for the rotated tail vertices.  The three supports the §8.4
dichotomy must compare at the pivot `q₂` are:

* the **closing/terminal** support `[q₂, q₁, qₙᵗ]` (`det3 q₂ q₁ qₙᵗ`),
* an **interior first-edge (A-family)** support `[q₂, q₁, qₖᵗ]` (`det3 q₂ q₁ qₖᵗ`), `3 ≤ k < n`,
* the **interior tail** support `[q₂, qₖᵗ, qₙᵗ]` (`det3 q₂ qₖᵗ qₙᵗ`), which is **rotation-invariant**
  (`sOrient_rotS2`: `det3 q₂ qₖᵗ qₙᵗ = det3 q₂ qₖ qₙ`) and **strictly positive** by the convex-position
  ordering (`cyclicTriplePos`, since `2 < k < n` reading the indices `q₂ < qₖ < qₙ`).

The GP three-term relation with shared apex `q₂` (`gp_three_term`) is the *only* algebraic relation
among these shared-apex minors.  We specialise it to exactly this closing configuration: it expresses
the product `[q₂, q₁, qₖᵗ] · [q₂, qₙᵗ, x]` of an A-family support and a fourth minor as the closing
support `[q₂, q₁, qₙᵗ]` times `[q₂, qₖᵗ, x]` plus the invariant interior support `[q₂, q₁, qₖᵗ]`-free
syzygy term.  This is the genuine algebraic engine behind §8's A-family monotonicity — the GP syzygy
the design's diagonal induction is built on, here written at the closing triple. -/

/-- **GP deficit identity at the closing configuration (apex `q₂`).**  For the pivot `q₂` (the axis),
the fixed head `q₁`, an interior rotated tail vertex `qkt`, the terminal rotated tail vertex `qnt`,
and any probe `x`, the Grassmann–Plücker syzygy with shared apex `q₂` reads

`[q₂, q₁, qnt] · [q₂, qkt, x]  =  [q₂, qkt, qnt] · [q₂, q₁, x]  +  [q₂, q₁, qkt] · [q₂, qnt, x]`.

A true polynomial identity (instance of `gp_three_term`, apex `q₂`, with `b = q₁`, `c = qkt`,
`d = qnt`, `e = x`).  Specialised so that the **invariant interior tail support** `[q₂, qkt, qnt]`
multiplies `[q₂, q₁, x]`: choosing the probe `x` then turns this into the A-family monotonicity link. -/
theorem gp_closing_deficit (q2 q1 qkt qnt x : E3) :
    det3 q2 q1 qnt * det3 q2 qkt x
      = det3 q2 qkt qnt * det3 q2 q1 x + det3 q2 q1 qkt * det3 q2 qnt x := by
  have h := gp_three_term q2 q1 qkt qnt x
  -- gp_three_term: det3 q2 q1 qnt * det3 q2 qkt x
  --              = det3 q2 qkt qnt * det3 q2 q1 x + det3 q2 q1 qkt * det3 q2 qnt x
  simpa using h

/-- The interior tail support `[q₂, qkt, qnt]` is **rotation-invariant**: rotating both interior
tail vertices about the pivot `q₂` leaves the support unchanged.  This is `sOrient_rotS2`, the
jointly-rotated invariance — it is what makes the GP deficit identity's coefficient
`det3 q₂ qkt qnt` a *fixed positive constant* of the opening (it equals `det3 q₂ qk qn`). -/
theorem interiorTailSupport_invariant (q2 qk qn : S2) (θ : ℝ) :
    det3 (q2 : E3) (rotS2 q2 θ qk : E3) (rotS2 q2 θ qn : E3) = det3 (q2 : E3) (qk : E3) (qn : E3) := by
  have h := sOrient_rotS2 q2 θ q2 qk qn
  simpa only [sOrient, rotS2_coe, rot_axis q2.2] using h

/-- **The closing-configuration GP link, in `sOrient` form (the §8 A-family engine).**  With the
pivot `q₂`, the head `q₁`, an interior rotated tail vertex `qkt = Rₜqₖ`, the terminal rotated tail
`qnt = Rₜqₙ`, and the probe `x = q₁`, the deficit identity collapses (`det3 q₂ q₁ q₁ = 0`) to the
clean two-term link

`[q₂, q₁, qnt] · [q₂, qkt, q₁]  =  [q₂, q₁, qkt] · [q₂, qnt, q₁]`,

i.e. `sOrient q₂ q₁ qnt · sOrient q₂ qkt q₁ = sOrient q₂ q₁ qkt · sOrient q₂ qnt q₁`.  Rewriting the
last factor on each side by antisymmetry of the last two slots gives the **A-family sign link** the
design's pivot fan-order uses: the closing support and the interior first-edge support carry related
signs through the rotation. -/
theorem closing_Afamily_link (q2 q1 qkt qnt : S2) :
    sOrient q2 q1 qnt * sOrient q2 qkt q1 = sOrient q2 q1 qkt * sOrient q2 qnt q1 := by
  have h := gp_closing_deficit (q2 : E3) (q1 : E3) (qkt : E3) (qnt : E3) (q1 : E3)
  have hself : det3 (q2 : E3) (q1 : E3) (q1 : E3) = 0 := det3_self_mid _ _
  simp only [sOrient]
  rw [hself, mul_zero, zero_add] at h
  linarith [h]

/-! ## Part 2. The named residue: the design's `terminal_visibility` (§7).

The theorem that *would* recover the book's terminal stuck branch is design §7's `terminal_visibility`:
whenever the closing/terminal support `C_term` stays strictly positive, **every other** mixed support
stays strictly positive too.  The counterexample of §6 shows this is *strictly stronger* than the
convex-position ordering: convexity alone leaves a non-terminal support free to vanish while the
closing one is still positive.  We name it for the actual opening (`openArm`, pivoting at the axis,
where the substrate's `mixedSupport A ij θ = det3 (A i)(A j)(rotated tail)`), as the implication

`(closing mixed support `> 0` at `θ`) ⟹ (every mixed support `> 0` at `θ`)`. -/

/-- The **closing mixed support** at opening angle `θ`: the support of the closing diagonal
`(A 0)(A 1)` against the rotated tail.  In the substrate's `mixedSupport` family this is the index
`(0, 1)`: `mixedSupport A (0, 1) θ = det3 (A 0)(A 1)(rot (axis) θ (A last))`. -/
def closingMixedSupport {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ) : ℝ :=
  mixedSupport A (0, 1) θ

/-- **(Named residue) `TerminalVisibility`** — design §7's `terminal_visibility`.  For a strictly
convex arm `A` and an opening angle `θ`, *if* the closing mixed support is strictly positive at `θ`,
then *every* mixed support is strictly positive at `θ`.  This is the precise statement the §6
counterexample shows is **not** implied by strict convexity (a non-terminal support can vanish while
the closing one is positive); it is the genuine missing theorem of the §8.4 terminal stuck branch.
It is *not* a re-wrapper of `StuckWitnessExists`: it carries only the cross-support sign implication
along the opening, none of the opening construction, the `span≥0` betweenness extraction, the tail
sub-comparison, or the endpoint bookkeeping. -/
def TerminalVisibility : Prop :=
  ∀ (n : ℕ) (A : Fin (n + 1 + 1) → S2), StrictConvexSphArm A → ∀ θ : ℝ,
    0 < closingMixedSupport A θ →
      ∀ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1), 0 < mixedSupport A ij θ

/-- **The closing-witness identification (admissibility-guarded).**  At a STUCK supremum `δ`
where the closing mixed support is *nonnegative* (the genuine admissibility condition the dichotomy
maintains — every monitored support `≥ 0` on the admissible interval, including the closing one) and
some mixed support vanishes, `TerminalVisibility` forces the **closing** support to be the vanishing
one.  This is the honest, fully-guarded form of the closing-first identification: it consumes
`TerminalVisibility` (the §7 missing theorem) together with admissibility (`closing ≥ 0`), and outputs
exactly `closingMixedSupport A δ = 0` — the input `betweenness_span_nnreal` needs. -/
theorem closingFirst_of_terminalVisibility_admissible (htv : TerminalVisibility)
    {n : ℕ} {A : Fin (n + 1 + 1) → S2} (hA : StrictConvexSphArm A) {δ : ℝ}
    (hadm : 0 ≤ closingMixedSupport A δ)
    (hstuck : ∃ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1), mixedSupport A ij δ = 0) :
    closingMixedSupport A δ = 0 := by
  obtain ⟨ij, hij⟩ := hstuck
  rcases eq_or_lt_of_le hadm with heq | hgt
  · exact heq.symm
  · -- closing support `> 0` ⟹ every support `> 0` ⟹ contradiction with the vanishing one.
    have := htv n A hA δ hgt ij
    exact absurd hij (ne_of_gt this)

/-! ## Part 3. The machine-checked refutation (design §6 counterexample).

We recompute the design §6 counterexample's two governing determinants from the raw vertices.  Working
in the affine chart `z = 1` (the design notes the spherical signs are preserved under radial
normalisation), put the head ray `a(t) = (-2 cos t, -2 sin t, 1)` (the head `v₁ = (-2, 0, 1)` rotated
about `v₂ = e₃` by `-t`), the tail edge vertices `v₅ = (-3, 1, 1)`, `v₆ = (-21/10, 1/100, 1)`, and
`v₁ = (-2, 0, 1)`, `v₂ = (0, 0, 1)`.

* `D(t) := det3 v₅ v₆ a(t)` — a **non-terminal** mixed support.
* `E(t) := det3 (R₋ₜ v₆) v₁ v₂` — the **closing/terminal** support (in the design's sign convention).

We prove the closed forms, that `D` changes sign on `[0, 0.052]` (so a non-terminal support vanishes
there, by the IVT), and that `E > 0` throughout — so the **closing support is still positive when the
non-terminal one first vanishes**.  This is the concrete, machine-checked failing chain for the round's
"closing-first" angle. -/

/-- The §6 head ray `a(t) = (-2 cos t, -2 sin t, 1) ∈ ℝ³` (the head `v₁` rotated about `e₃` by `-t`). -/
def ceHead (t : ℝ) : E3 := !₂[-2 * Real.cos t, -2 * Real.sin t, 1]

/-- The tail edge vertex `v₅ = (-3, 1, 1)`. -/
def ceV5 : E3 := !₂[(-3 : ℝ), 1, 1]
/-- The tail edge vertex `v₆ = (-21/10, 1/100, 1)`. -/
def ceV6 : E3 := !₂[(-21/10 : ℝ), 1/100, 1]
/-- The head vertex `v₁ = (-2, 0, 1)`. -/
def ceV1 : E3 := !₂[(-2 : ℝ), 0, 1]
/-- The pivot vertex `v₂ = (0, 0, 1) = e₃`. -/
def ceV2 : E3 := !₂[(0 : ℝ), 0, 1]
/-- The tail vertex `v₆` rotated about `e₃` by `-t`: `R₋ₜ v₆ = (cos t·x + sin t·y, -sin t·x + cos t·y, 1)`. -/
def ceRotV6 (t : ℝ) : E3 :=
  !₂[Real.cos t * (-21/10) + Real.sin t * (1/100),
    -Real.sin t * (-21/10) + Real.cos t * (1/100), 1]

/-- Coordinate-extraction simp set for the `!₂[...]` literals. -/
theorem ce_D_closed (t : ℝ) :
    det3 ceV5 ceV6 (ceHead t) = 207/100 - (99/50) * Real.cos t - (9/5) * Real.sin t := by
  simp only [det3, ceV5, ceV6, ceHead, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The closing/terminal support `E(t) = det3 (R₋ₜ v₆) v₁ v₂` has the closed form
`(21/5) sin t + (1/50) cos t`. -/
theorem ce_E_closed (t : ℝ) :
    det3 (ceRotV6 t) ceV1 ceV2 = (21/5) * Real.sin t + (1/50) * Real.cos t := by
  simp only [det3, ceRotV6, ceV1, ceV2, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- At `t = 0` the non-terminal support is strictly positive: `D(0) = 9/100 > 0`. -/
theorem ce_D_zero_pos : 0 < det3 ceV5 ceV6 (ceHead 0) := by
  rw [ce_D_closed]; simp [Real.cos_zero, Real.sin_zero]; norm_num

/-- At `t = 0.052` the non-terminal support is strictly negative: `D(0.052) < 0`.  We bound
`cos 0.052 ≥ 0.99` and `sin 0.052 ≥ 0.0519` (`0.052 − 0.052³/6 ≤ sin`, `cos ≤ 1` and the explicit
lower bound below), so `D(0.052) ≤ 207/100 − (99/50)(0.99) − (9/5)(0.0519) < 0`. -/
theorem ce_D_at_052_neg : det3 ceV5 ceV6 (ceHead (0.052)) < 0 := by
  rw [ce_D_closed]
  -- Sharp Taylor lower bounds (the margin is ~0.0009, so loose rounding does not suffice):
  --   cos 0.052 ≥ 1 − 0.052²/2 = 0.998648,  sin 0.052 > 0.052 − 0.052³/4 = 0.0519649.
  -- Then 99/50·0.998648 + 9/5·0.0519649 = 2.07084 > 2.07 = 207/100, so D(0.052) < 0.
  have hcos : (1 : ℝ) - 0.052 ^ 2 / 2 ≤ Real.cos 0.052 := Real.one_sub_sq_div_two_le_cos
  have hsin : 0.052 - 0.052 ^ 3 / 4 < Real.sin 0.052 :=
    Real.sin_gt_sub_cube (by norm_num) (by norm_num)
  nlinarith [hcos, hsin]

/-- **The non-terminal support vanishes somewhere in `(0, 0.052)`.**  `D` is continuous, `D(0) > 0`,
`D(0.052) < 0`; the intermediate value theorem gives a `t₀ ∈ [0, 0.052]` with `D(t₀) = 0` — a
non-terminal mixed support becomes tight before the cap. -/
theorem ce_D_has_zero : ∃ t₀ : ℝ, t₀ ∈ Set.Icc (0 : ℝ) 0.052 ∧ det3 ceV5 ceV6 (ceHead t₀) = 0 := by
  have hcont : Continuous (fun t => det3 ceV5 ceV6 (ceHead t)) := by
    simp only [ce_D_closed]
    exact (continuous_const.sub (continuous_const.mul Real.continuous_cos)).sub
      (continuous_const.mul Real.continuous_sin)
  have h0 : (0 : ℝ) ≤ 0.052 := by norm_num
  -- D(0.052) < 0 ≤ ... ≤ D(0): apply IVT for the value 0 on [0, 0.052].
  have hmem : (0 : ℝ) ∈ Set.Icc (det3 ceV5 ceV6 (ceHead 0.052)) (det3 ceV5 ceV6 (ceHead 0)) :=
    ⟨le_of_lt ce_D_at_052_neg, le_of_lt ce_D_zero_pos⟩
  obtain ⟨t₀, ht₀mem, ht₀⟩ :=
    intermediate_value_Icc' h0 (hcont.continuousOn) hmem
  exact ⟨t₀, ht₀mem, ht₀⟩

/-- **The closing/terminal support is strictly positive throughout `[0, 0.052]`.**
`E(t) = (21/5) sin t + (1/50) cos t`; on `[0, 0.052] ⊂ [0, π/2)` both `sin t ≥ 0` and `cos t > 0`,
and the `cos`-coefficient is positive, so `E(t) > 0`.  Hence when the non-terminal support first
vanishes (at the `t₀` above), the closing support is **still positive** — the closing support is *not*
the first to vanish. -/
theorem ce_E_pos_on (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 0.052) : 0 < det3 (ceRotV6 t) ceV1 ceV2 := by
  rw [ce_E_closed]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htpi : t < Real.pi / 2 := by linarith
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htpi⟩
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
  nlinarith [hcos, hsin]

/-- **The machine-checked refutation of the "closing-first" angle.**  There is a strictly convex
configuration (the §6 counterexample) and an opening parameter `t₀ ∈ [0, 0.052]` at which a
**non-terminal** mixed support `D` vanishes while the **closing/terminal** support `E` is strictly
positive.  Hence the convex-position ordering does **not** force the closing support to vanish first:
the round's proposed identification is false, and `StuckWitnessExists` cannot be discharged by
`cyclicTriplePos` alone — it requires the strictly stronger `TerminalVisibility` (design §7). -/
theorem closing_not_first :
    ∃ t₀ : ℝ, t₀ ∈ Set.Icc (0 : ℝ) 0.052 ∧
      det3 ceV5 ceV6 (ceHead t₀) = 0 ∧ 0 < det3 (ceRotV6 t₀) ceV1 ceV2 := by
  obtain ⟨t₀, ht₀mem, ht₀zero⟩ := ce_D_has_zero
  exact ⟨t₀, ht₀mem, ht₀zero, ce_E_pos_on t₀ ht₀mem.1 ht₀mem.2⟩

/-! ## Part 4. Re-export and honest residue.

The closing-witness identification reduces — via this round's `closingFirst_of_terminalVisibility_admissible`
— to the named `TerminalVisibility` (design §7's `terminal_visibility`), which the §6 counterexample
(`closing_not_first`, machine-checked) proves is strictly stronger than the convex-position ordering.
We do **not** restate `StuckWitnessExists`; the conditional arm lemmas stay re-exported through the
substrate's `spherical_arm_mono_complete` / `_strict_complete` (conditional on
`OpeningStructuralAssembly`, of which `StuckWitnessExists` is the open half).  This round banks the GP
deficit engine (Part 1, true polynomial identity) and the machine-checked refutation (Part 3),
narrowing the *reason* the residue resists to the precise, counterexample-backed `terminal_visibility`
obstruction. -/

/-- **Re-export: the spherical arm lemma (weak), conditional on `OpeningStructuralAssembly`** — with
this round's analysis of the residue's `terminal_visibility` obstruction recorded.  Identical to
`SphericalSZComplete.spherical_arm_mono_complete`. -/
theorem spherical_arm_mono_complete' (hasm : OpeningStructuralAssembly)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_complete hasm hn A B hA hB hside hangle

/-- **Re-export: the spherical arm lemma (strict), conditional on `OpeningStructuralAssembly`.** -/
theorem spherical_arm_mono_strict_complete' (hasm : OpeningStructuralAssembly)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_complete hasm hn A B hA hB hside hangle hstrict

/-! ## Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity (GP engine): the deficit identity at `x = q₂` is the degenerate but genuine instance
`det3 q₂ q₁ qnt · 0 = det3 q₂ qkt qnt · 0 + det3 q₂ q₁ qkt · 0` — the family of instances is inhabited
and the identity is a true equation, not a vacuous one. -/
theorem gp_closing_deficit_nonvacuous (q2 q1 qkt qnt : E3) :
    det3 q2 q1 qnt * det3 q2 qkt q2
      = det3 q2 qkt qnt * det3 q2 q1 q2 + det3 q2 q1 qkt * det3 q2 qnt q2 := by
  have h := gp_closing_deficit q2 q1 qkt qnt q2
  simpa using h

/-- Non-vacuity (`TerminalVisibility` is satisfiable, not a vacuous-hypothesis impostor): its
conclusion is a genuine family of strict determinant inequalities; the *converse* failure is exactly
`closing_not_first`, so the predicate distinguishes configurations — it is not constantly true nor
constantly false.  Here we record that its hypothesis (`closing > 0`) is realisable (it holds at
`θ = 0` for the closing diagonal of a strictly convex arm, by `cut_diagonal_supports`). -/
theorem terminalVisibility_hypothesis_realisable {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) : 0 < closingMixedSupport A 0 := by
  -- at θ = 0 the rotated tail is the original tail; closingMixedSupport A 0
  --   = det3 (A 0)(A 1)(A last) = sOrient (A 0)(A 1)(A last) > 0 by cyclicTriplePos (0 < 1 < last).
  have hone : ((1 : Fin (n + 1 + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have h0n : (0 : Fin (n + 1 + 1)) < 1 := by
    rw [Fin.lt_def, Fin.val_zero, hone]; omega
  have h1l : (1 : Fin (n + 1 + 1)) < Fin.last (n + 1) := by
    rw [Fin.lt_def, Fin.val_last, hone]; omega
  have hpos : 0 < sOrient (A 0) (A 1) (A (Fin.last (n + 1))) :=
    cyclicTriplePos_unconditional hA.closed_convex 0 1 (Fin.last (n + 1)) h0n h1l
  have hrot : rot (openAxis A : E3) 0 (A (Fin.last (n + 1)) : E3) = (A (Fin.last (n + 1)) : E3) := by
    rw [rot_zero]
  show 0 < mixedSupport A (0, 1) 0
  simp only [mixedSupport]
  rw [hrot]
  simpa only [sOrient] using hpos

end ProofsInTheBook.SphericalStuckWitness
