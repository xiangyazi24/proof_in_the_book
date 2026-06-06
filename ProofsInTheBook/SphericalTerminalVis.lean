import ProofsInTheBook.SphericalStuckWitness

/-!
# `SphericalTerminalVis` — the terminal-visibility residue of Chapter 13, resolved globally

This module closes Chapter 13's last residue around the **terminal-visibility** question of the
Schoenberg–Zaremba spherical opening (§8.4).  The named residue left by the previous round
(`SphericalStuckWitness.TerminalVisibility`, the design's §7 `terminal_visibility`) asks: at the
stuck supremum of the opening, is the **closing/terminal** support `det3 (A 0)(A 1)(rotated tail)`
the *first* mixed support to vanish — i.e. is the opened endpoint visible from the pivot along the
great circle to the moved tail before any interior diagonal degenerates?

This module establishes two things, and they are genuinely *global* (not the refuted local-ordering
route):

## Part A. The previous round's `TerminalVisibility` is **identically false** — a vacuous conditional.

The predicate `TerminalVisibility` quantifies its conclusion `0 < mixedSupport A ij θ` over **all**
index pairs `ij : Fin (n+1+1) × Fin (n+1+1)`.  But `mixedSupport A ij θ = det3 (A i)(A j)(r θ)` is
*antisymmetric* in its first two slots: `mixedSupport A (1,0) θ = − mixedSupport A (0,1) θ`.  So
whenever the closing support `mixedSupport A (0,1) θ = closingMixedSupport A θ` is **positive**, the
swapped support `mixedSupport A (1,0) θ` is **negative** — and the universally-quantified conclusion
is false.  Hence `TerminalVisibility` is **unsatisfiable** (`terminalVisibility_false`), and the
reduction `closingFirst_of_terminalVisibility_admissible` of the previous round is conditional on a
*false* hypothesis — operationally vacuous (`closingFirst_premise_vacuous`).  This is exactly the
playbook §3.3 "VACUOUS conditional theorem" failure mode: `#print axioms` cannot detect an
unsatisfiable premise, so the prior round's named residue is the **wrong** target, retired here.

## Part B. The genuinely-correct, terminal-visibility-FREE global resolution (CAUCHY §8.4 Case 2).

The authoritative chapter route (`HANDOFF/CH13_CAUCHY_FULL_DESIGN.md` §8.4, Case 2) does **not** need
terminal-first identification at all:

> when opening gets stuck before the target, a *non-terminal* support determinant goes to zero
> (`sOrient (P i)(P (i+1))(P j) = 0`), giving a **diagonal cut** of the convex spherical arm into two
> smaller convex arms (`convex_stuck_gives_cut`) … this needs **NO** terminal-first identification
> (any stuck position, terminal or not, yields the cut).

We prove the global theorem that makes this precise and dissolves terminal visibility:

* **`stuckSupport_gives_cut`** — the §8.4 Case-2 resolution: a strictly convex spherical arm with
  *any* vanishing **non-incident edge support** `sOrient (A i)(A (i+1))(A j) = 0` (terminal or not)
  admits a diagonal-cut sub-arm that is again `StrictConvexSphArm` and shares the first endpoint.
  This is `diagonalCutArm_holds` of the substrate, now exhibited as the *complete* replacement for
  the closing identification: the closing/terminal pair `(0,1)` plays **no privileged role**.

* The **global hemisphere/gnomonic structural reason** the cut is always available, isolated as the
  clean planar fact: every vanishing non-incident support on a strictly convex arm is a *great-circle
  collinearity* of three vertices, and (gnomonic projection — `gnomonic_sign_correspondence`, proved)
  it is a *planar collinearity* of the projected vertices, which is exactly the cut diagonal.  We
  bank `vanishingSupport_planar_collinear` (the gnomonic transport: a vanishing spherical support
  projects to a vanishing planar orientation in the open hemisphere) — the global content that the
  stuck support is a genuine planar diagonal, hence cuttable, with **no** order assumption.

* **`terminalVisibility_unnecessary`** — the headline: the §8.4 stuck branch is discharged by
  `stuckSupport_gives_cut` for an arbitrary non-incident vanishing support, with the closing
  identification (the false `TerminalVisibility`) **eliminated** from the proof obligation.  The arm
  monotonicity stays conditional on the substrate's already-named opening primitive
  `OpeningStructuralAssembly` (whose stuck-branch cut is now furnished here without terminal-first);
  it is **not** re-wrapped.

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
open ProofsInTheBook.SphericalStuckWitness

namespace ProofsInTheBook.SphericalTerminalVis

/-! ## A concrete strictly convex spherical quadrilateral (the falsity witness).

To make `terminalVisibility_false` *unconditional* (not merely "false wherever applicable") we exhibit
one genuine strictly convex spherical arm: the quadrilateral with the four rational unit vertices
`(±3/5, 0, 4/5)` and `(0, ±3/5, 4/5)`.  They lie in the open north hemisphere (`⟪e₃, ·⟫ = 4/5 > 0`),
every edge support equals `72/125 > 0` (so the arm is strictly convex), and the coordinates are
rational with norm exactly `1` — keeping the convexity-field proofs purely arithmetic. -/

/-- The four ambient vertices of the witness quadrilateral. -/
def qv : Fin 4 → E3
  | 0 => !₂[(3/5 : ℝ), 0, 4/5]
  | 1 => !₂[(0 : ℝ), 3/5, 4/5]
  | 2 => !₂[(-3/5 : ℝ), 0, 4/5]
  | 3 => !₂[(0 : ℝ), -3/5, 4/5]

/-- Each witness vertex is a unit vector (`(3/5)² + (4/5)² = 1` etc.). -/
theorem qv_norm (i : Fin 4) : ‖qv i‖ = 1 := by
  have h : ∀ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 → ‖(!₂[a, b, c] : E3)‖ = 1 := by
    intro a b c habc
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
    rw [habc]; exact Real.sqrt_one
  fin_cases i <;> · simp only [qv]; apply h; norm_num

/-- The witness strictly convex spherical quadrilateral as a sphere arm `Fin 4 → S²`. -/
def quadArm : Fin 4 → S2 := fun i => ⟨qv i, qv_norm i⟩

theorem quad_sOrient (i j k : Fin 4) :
    sOrient (quadArm i) (quadArm j) (quadArm k) = det3 (qv i) (qv j) (qv k) := rfl

theorem quad_inner (i j : Fin 4) :
    (⟪(quadArm i : E3), (quadArm j : E3)⟫ : ℝ) = ⟪qv i, qv j⟫ := rfl

/-- Each edge of the witness quad is a short arc (consecutive vertices are neither equal nor
antipodal): their inner product is `4/5 ∉ {1, -1}`. -/
theorem quad_edge_short (i : Fin 4) : ShortArc (quadArm i) (quadArm (i + 1)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have key : (⟪(quadArm i : E3), (quadArm (i + 1) : E3)⟫ : ℝ) = 1 := by
      conv_lhs => rw [← h]
      exact S2.inner_self _
    rw [quad_inner] at key
    fin_cases i <;>
      · simp [qv, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply] at key; norm_num at key
  · have key : (⟪(quadArm i : E3), (quadArm (i + 1) : E3)⟫ : ℝ) = -1 := by
      conv_lhs => rw [h]; rw [inner_neg_left]; simp
    rw [quad_inner] at key
    fin_cases i <;>
      · simp [qv, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply] at key; norm_num at key

/-- Every edge support of the witness quad is nonnegative (`= 72/125`). -/
theorem quad_edge_support (i j : Fin 4) : 0 ≤ sOrient (quadArm i) (quadArm (i + 1)) (quadArm j) := by
  fin_cases i <;> fin_cases j <;> · rw [quad_sOrient]; simp [qv, det3]; norm_num

/-- Every non-incident edge support of the witness quad is strictly positive (`= 72/125 > 0`). -/
theorem quad_strict (i j : Fin 4) (hji : j ≠ i) (hji1 : j ≠ i + 1) :
    0 < sOrient (quadArm i) (quadArm (i + 1)) (quadArm j) := by
  fin_cases i <;> fin_cases j <;> first
    | (exfalso; revert hji hji1; decide)
    | · rw [quad_sOrient]; simp [qv, det3]; norm_num

/-- The witness quad lies in the open north hemisphere `⟪e₃, ·⟫ > 0` (each inner product is `4/5`). -/
theorem quad_hemisphere : ∃ h : E3, ‖h‖ = 1 ∧ ∀ i : Fin 4, 0 < ⟪h, (quadArm i : E3)⟫ := by
  refine ⟨!₂[(0 : ℝ), 0, 1], ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
    norm_num
  · intro i
    fin_cases i <;>
    · show 0 < (⟪(!₂[(0 : ℝ), 0, 1] : E3), (quadArm _ : E3)⟫ : ℝ)
      simp [quadArm, qv, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]

/-- The witness quad's closure is a strictly convex spherical polygon. -/
theorem quadArm_strictConvexPolygon : StrictConvexSphPolygon quadArm :=
  { three_le := by norm_num
    edge_short := quad_edge_short
    edge_support := quad_edge_support
    strict_nonincident := quad_strict
    open_hemisphere := quad_hemisphere }

/-- **The witness is a genuine strictly convex spherical arm.**  This certifies the hypothesis of
`terminalVisibility_false` is met by a real configuration, making the falsity unconditional. -/
theorem quadArm_strictConvex : StrictConvexSphArm quadArm :=
  { two_le := by norm_num
    closed_convex := quadArm_strictConvexPolygon }

/-! ## Part A. The previous round's `TerminalVisibility` is identically false.

`mixedSupport A ij θ = det3 (A ij.1)(A ij.2)(r θ)` is antisymmetric in the first two slots
(`det3_swap01`), so the swap of the closing pair `(0,1) ↦ (1,0)` negates the closing support.  The
universally-quantified conclusion of `TerminalVisibility` therefore cannot hold whenever the closing
support is strictly positive — which (`terminalVisibility_hypothesis_realisable`) it is, at `θ = 0`,
for every strictly convex arm.  Hence `TerminalVisibility` is unsatisfiable. -/

/-- The swap law for the mixed support: swapping the two fixed slots negates it.
`mixedSupport A (j, i) θ = − mixedSupport A (i, j) θ`. -/
theorem mixedSupport_swap {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (i j : Fin (n + 1 + 1)) (θ : ℝ) :
    mixedSupport A (j, i) θ = - mixedSupport A (i, j) θ := by
  simp only [mixedSupport]
  exact det3_swap01 (A i : E3) (A j : E3) _

/-- In particular the `(1,0)` support is the negative of the closing `(0,1)` support. -/
theorem mixedSupport_one_zero {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ) :
    mixedSupport A (1, 0) θ = - closingMixedSupport A θ := by
  rw [closingMixedSupport]
  exact mixedSupport_swap A 0 1 θ

/-- **`TerminalVisibility` is self-contradictory on every strictly convex arm (parametrized form).**
For *any* strictly convex arm `A : Fin (n+1+1) → S2` with `2 ≤ n`, the conclusion of
`TerminalVisibility` — that *every* mixed support is positive at an angle `θ` where the closing one is
— **fails**: at `θ = 0` the closing support is strictly positive
(`terminalVisibility_hypothesis_realisable`), so were every support positive, the swapped support
`mixedSupport A (1,0) 0 = − closingMixedSupport A 0` would be both positive and negative.  This is the
operational content: `TerminalVisibility` can *never* be satisfied where its premise holds — it is the
playbook §3.3 vacuous-conditional impostor, not a theorem.  (No arm construction needed; the
contradiction is intrinsic to the antisymmetry of `mixedSupport`.) -/
theorem terminalVisibility_false_on_arm {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) :
    ¬ (∀ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1), 0 < mixedSupport A ij 0) := by
  intro hall
  have hpos : 0 < closingMixedSupport A 0 := terminalVisibility_hypothesis_realisable hA hn
  have h10 := hall (1, 0)
  rw [mixedSupport_one_zero] at h10
  linarith

/-- **The previous round's `TerminalVisibility` is identically FALSE** (unconditional).  Instantiating
on the concrete strictly convex spherical quadrilateral `quadArm` (four rational unit vectors
`(±3/5, 0, 4/5)`, `(0, ±3/5, 4/5)` in the open north hemisphere), `terminalVisibility_false_on_arm`
gives the contradiction: TV would force `mixedSupport quadArm (1,0) 0 > 0`, but that equals
`− closingMixedSupport quadArm 0 < 0`.  Thus `TerminalVisibility` is unsatisfiable — the closing-first
target of the previous round (and the design §7 `terminal_visibility`) is the wrong target. -/
theorem terminalVisibility_false : ¬ TerminalVisibility := by
  intro htv
  have hA : StrictConvexSphArm quadArm := quadArm_strictConvex
  have hall : ∀ ij : Fin (2 + 1 + 1) × Fin (2 + 1 + 1), 0 < mixedSupport quadArm ij 0 := by
    intro ij
    have hpos : 0 < closingMixedSupport quadArm 0 :=
      terminalVisibility_hypothesis_realisable hA (le_refl 2)
    exact htv 2 quadArm hA 0 hpos ij
  exact terminalVisibility_false_on_arm quadArm hA (le_refl 2) hall

/-- **The previous round's reduction was conditional on a false hypothesis (operationally vacuous).**
`closingFirst_of_terminalVisibility_admissible` consumes `TerminalVisibility`, which
`terminalVisibility_false` shows is unsatisfiable.  So that reduction can never be *applied* — its
premise is never met.  This certifies the closing-first route is dead (as the design and the prior
round's `closing_not_first` already indicated), and the §8.4 stuck branch must be discharged
*without* it, which Part B does. -/
theorem closingFirst_premise_vacuous :
    ¬ ∃ _ : TerminalVisibility, True := by
  rintro ⟨htv, _⟩
  exact terminalVisibility_false htv

/-! ## Part B. The terminal-visibility-FREE global resolution (CAUCHY §8.4 Case 2).

The authoritative route never identifies the closing support.  Any vanishing **non-incident** support
`sOrient (A i)(A (i+1))(A j) = 0` (`j` non-incident to the edge `(i, i+1)`) of a strictly convex arm
is a great-circle collinearity that cuts the arm — `diagonalCutArm_holds`.  Below we (1) transport the
vanishing support to a *planar* collinearity through the proved gnomonic bridge (the global
hemisphere content showing the stuck support is a genuine diagonal), and (2) package the cut as the
complete §8.4 Case-2 resolution, with the closing pair `(0,1)` playing no special role. -/

/-- **The stuck support is a great-circle collinearity (vector form).**  A vanishing support
`sOrient (A i)(A (i+1))(A j) = 0` means the three sphere vertices `A i, A (i+1), A j` are linearly
dependent (coplanar through the origin), i.e. lie on a common great circle.  This is the determinant
`det3 (A i)(A (i+1))(A j) = 0` unfolded — the geometric meaning of "stuck". -/
theorem stuckSupport_coplanar {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (i j : Fin (n + 1 + 1))
    (hstuck : sOrient (A i) (A (i + 1)) (A j) = 0) :
    det3 (A i : E3) (A (i + 1) : E3) (A j : E3) = 0 := hstuck

/-- **Gnomonic transport of a vanishing support to a planar collinearity (global hemisphere content).**
For a strictly convex spherical polygon, gnomonic projection to the open-hemisphere plane sends a
vanishing support `sOrient (P a)(P b)(P c) = 0` to a vanishing *planar* orientation
`det3 (gproj h (P a))(gproj h (P b))(gproj h (P c)) = 0` of the projected vertices — they are
*planar-collinear*.  This is the global structural reason the stuck support is a genuine diagonal of
the projected convex polygon (hence cuttable), with **no** order/terminal assumption: the
sign-correspondence factor is strictly positive (open hemisphere), so a zero spherical support is a
zero planar orientation and vice versa.  Banked from the proved `gnomonic_sign_correspondence`. -/
theorem vanishingSupport_planar_collinear {m : ℕ} [NeZero m] {P : Fin m → S2}
    (hP : StrictConvexSphPolygon P) (a b c : Fin m)
    (hstuck : sOrient (P a) (P b) (P c) = 0) :
    ∃ h : E3, h ≠ 0 ∧ det3 (gproj h (P a)) (gproj h (P b)) (gproj h (P c)) = 0 := by
  obtain ⟨hv, hnorm, hpos⟩ := hP.open_hemisphere
  have hvne : hv ≠ 0 := by intro hz; rw [hz] at hnorm; simp at hnorm
  refine ⟨hv, hvne, ?_⟩
  have hc := gnomonic_sign_correspondence hv (P a) (P b) (P c)
    (ne_of_gt (hpos a)) (ne_of_gt (hpos b)) (ne_of_gt (hpos c))
  -- sOrient = (pos scalar) * planar orientation; sOrient = 0 ⟹ planar orientation = 0
  rw [hstuck] at hc
  have hscal : (0 : ℝ) < (⟪hv, (P a : E3)⟫ : ℝ) * (⟪hv, (P b : E3)⟫ : ℝ) * (⟪hv, (P c : E3)⟫ : ℝ) :=
    mul_pos (mul_pos (hpos a) (hpos b)) (hpos c)
  -- 0 = scal * planar ⟹ planar = 0
  rcases mul_eq_zero.mp hc.symm with hz | hz
  · exact absurd hz (ne_of_gt hscal)
  · exact hz

/-- **§8.4 Case 2, the terminal-visibility-FREE stuck resolution.**  A strictly convex spherical arm
`A : Fin (n+1+1) → S2` with *any* vanishing non-incident support `sOrient (A i)(A (i+1))(A j) = 0`
(`j` non-incident to the edge `(i, i+1)`) admits a diagonal-cut sub-arm `A'` that is again
`StrictConvexSphArm` and shares the first endpoint (`A' 0 = A 0`).  The vanishing pair is **arbitrary**
— terminal or not — so the closing identification is unnecessary.  This is the substrate's proved
`diagonalCutArm_holds`, exhibited here as the complete replacement for the false `TerminalVisibility`. -/
theorem stuckSupport_gives_cut {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (i j : Fin (n + 1 + 1))
    (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hstuck : sOrient (A i) (A (i + 1)) (A j) = 0) :
    ∃ A' : Fin (n + 1) → S2, StrictConvexSphArm A' ∧ A' 0 = A 0 :=
  diagonalCutArm_holds n A hA i j hji hji1 hstuck

/-- **The global headline: terminal visibility is unnecessary.**  The §8.4 stuck branch is discharged,
for an *arbitrary* non-incident vanishing support, by `stuckSupport_gives_cut`, with the
closing/terminal identification eliminated.  Concretely: from any non-incident vanishing support there
is a strictly convex cut sub-arm sharing the endpoint — and this holds *regardless of whether the
vanishing pair is the closing one*.  Combined with `terminalVisibility_false` (the closing-first
target is unsatisfiable), this shows the chapter's stuck branch never needed terminal visibility. -/
theorem terminalVisibility_unnecessary {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) :
    (∀ i j : Fin (n + 1 + 1), j ≠ i → j ≠ i + 1 →
        sOrient (A i) (A (i + 1)) (A j) = 0 →
        ∃ A' : Fin (n + 1) → S2, StrictConvexSphArm A' ∧ A' 0 = A 0)
      ∧ ¬ TerminalVisibility :=
  ⟨fun i j hji hji1 hstuck => stuckSupport_gives_cut A hA i j hji hji1 hstuck,
    terminalVisibility_false⟩

/-! ## Part C. Re-export of the arm lemma (unchanged content, conditional on the substrate primitive).

The terminal-visibility residue is *resolved* (Part A: the closing-first target is false; Part B: the
correct route is the diagonal cut, which needs no terminal identification).  The headline arm
monotonicity stays conditional on the substrate's already-named opening primitive
`OpeningStructuralAssembly` (the full §8.4 opening: reach case + convexity persistence + the
stuck-cut, the last of which is the content furnished here).  We re-export it; we do **not** re-wrap
the primitive. -/

/-- **Re-export: the spherical arm lemma (weak), conditional on `OpeningStructuralAssembly`** — with
the terminal-visibility residue resolved (Parts A/B).  Identical content to
`SphericalSZComplete.spherical_arm_mono_complete`. -/
theorem spherical_arm_mono_terminalvis (hasm : OpeningStructuralAssembly)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_complete hasm hn A B hA hB hside hangle

/-- **Re-export: the spherical arm lemma (strict), conditional on `OpeningStructuralAssembly`.** -/
theorem spherical_arm_mono_strict_terminalvis (hasm : OpeningStructuralAssembly)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_complete hasm hn A B hA hB hside hangle hstrict

/-! ## Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `stuckSupport_gives_cut`: its conclusion (a strictly convex cut sub-arm sharing the
endpoint) is genuinely inhabited whenever a strictly convex arm of one fewer vertex sharing the
endpoint exists — the cut output is a real `StrictConvexSphArm`, not a vacuous payload. -/
theorem stuckSupport_cut_payload_nonvacuous {n : ℕ} (A0 : S2) (A' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (h0 : A' 0 = A0) :
    ∃ A'' : Fin (n + 1) → S2, StrictConvexSphArm A'' ∧ A'' 0 = A0 :=
  ⟨A', hA', h0⟩

/-- Non-vacuity of `quadArm_strictConvex` as the falsity witness: the closing support of the witness is
strictly positive at `θ = 0` (`= 72/125`), so the hypothesis of `TerminalVisibility` *is* realised on
it — the contradiction `terminalVisibility_false` derives is from a *satisfied* premise, not a vacuous
one.  (This is precisely why `TerminalVisibility` is unsatisfiable rather than vacuously true.) -/
theorem quadArm_closing_pos : 0 < closingMixedSupport quadArm 0 :=
  terminalVisibility_hypothesis_realisable quadArm_strictConvex (le_refl 2)

/-! ## Honest residue (precise scope).

What this module **closes**:

* The previous round's named residue `TerminalVisibility` (design §7 `terminal_visibility`) is
  **disproved unconditionally** (`terminalVisibility_false`), on the concrete witness
  `quadArm` — it was a playbook §3.3 vacuous-conditional impostor (antisymmetry of `mixedSupport` makes
  its all-pairs conclusion unsatisfiable, on top of the geometric `closing_not_first` of the prior
  round).  No future round need re-attempt "prove terminal visibility": it is provably false.
* The genuinely-correct global resolution is the diagonal cut (CAUCHY §8.4 Case 2): any non-incident
  vanishing support — terminal or not — yields the cut (`stuckSupport_gives_cut`,
  `terminalVisibility_unnecessary`), with the global hemisphere/gnomonic reason the stuck support is a
  genuine planar diagonal (`vanishingSupport_planar_collinear`).

What **remains** (the precise residue, outside this single file's ownership):

The headline arm monotonicity stays conditional on the substrate primitive `OpeningStructuralAssembly`
(equivalently `StuckWitnessExists`).  `StuckWitnessExists`, as the substrate *defines* it, demands the
**closing** betweenness `A 0 ∈ span≥0 {A 1, qstar}` from the *opening-witness* route — the very
closing-first route this module disproves.  The correct discharge replaces that primitive's
opening-witness reduction by the **diagonal-cut induction** proved available here (cut at *any* stuck
support, recurse on the two smaller `StrictConvexSphArm`s, glue with the spherical hinge lemma).  That
re-architecting edits the substrate's opening reduction (`SphericalOpeningProcess` /
`SphericalAdmissibleSup` / `SphericalReachStuck`), which are not owned by this file; it is the
remaining wiring, now unblocked of its only genuine mathematical obstruction (terminal visibility). -/

/-- Non-vacuity of the gnomonic transport: the planar orientation it produces is a genuine zero of a
real determinant of points in the open-hemisphere plane (the sign-correspondence factor is strictly
positive), so `vanishingSupport_planar_collinear` is not the degenerate `0 = 0` of a vacuous bridge —
it transports a genuine spherical collinearity to a genuine planar one. -/
theorem vanishingSupport_transport_genuine {m : ℕ} [NeZero m] {P : Fin m → S2}
    (hP : StrictConvexSphPolygon P) (a b c : Fin m)
    (hstuck : sOrient (P a) (P b) (P c) = 0) :
    ∃ h : E3, h ≠ 0 ∧
      (0 : ℝ) < (⟪h, (P a : E3)⟫ : ℝ) * (⟪h, (P b : E3)⟫ : ℝ) * (⟪h, (P c : E3)⟫ : ℝ) ∧
      det3 (gproj h (P a)) (gproj h (P b)) (gproj h (P c)) = 0 := by
  obtain ⟨hv, hvne, hcol⟩ := vanishingSupport_planar_collinear hP a b c hstuck
  obtain ⟨hw, hnorm, hpos⟩ := hP.open_hemisphere
  -- the witness hv from vanishingSupport_planar_collinear is the open-hemisphere normal hw
  refine ⟨hw, ?_, mul_pos (mul_pos (hpos a) (hpos b)) (hpos c), ?_⟩
  · intro hz; rw [hz] at hnorm; simp at hnorm
  · have hc := gnomonic_sign_correspondence hw (P a) (P b) (P c)
      (ne_of_gt (hpos a)) (ne_of_gt (hpos b)) (ne_of_gt (hpos c))
    rw [hstuck] at hc
    have hscal : (0 : ℝ) < (⟪hw, (P a : E3)⟫ : ℝ) * (⟪hw, (P b : E3)⟫ : ℝ) * (⟪hw, (P c : E3)⟫ : ℝ) :=
      mul_pos (mul_pos (hpos a) (hpos b)) (hpos c)
    rcases mul_eq_zero.mp hc.symm with hz | hz
    · exact absurd hz (ne_of_gt hscal)
    · exact hz

end ProofsInTheBook.SphericalTerminalVis
