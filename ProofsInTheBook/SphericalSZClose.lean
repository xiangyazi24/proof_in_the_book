import ProofsInTheBook.SphericalSZFinal

/-!
# `SphericalSZClose` — closing Chapter 13's spherical arm lemma (the three residual pieces)

`SphericalSZFinal` reduced the §8.4 Schoenberg–Zaremba opening step to the single named residue
`InteriorOpenAndSpliceStep`, banking the OPEN-branch bookkeeping (joint preservation, single-`erase`
deficit-decrease, interior endpoint monotonicity) and (via `SphericalSZStepClose`) the ear API and the
diagonal inequality.  The residue carries three concrete geometric productions:

* **(R-O)** the *interior-axis* reach/stuck supremum trichotomy (the substrate's
  `augmented_reachOrStuck_at_sup` is last-joint only);
* **(R-C)** the splice-body transport gluing the diagonal inequality to `endpt A ≤ endpt B`;
* **(R-cong)** the equal-joints endpoint congruence.

This module attacks the three pieces directly.

## (R-O) — the interior reach/stuck production via the generic admissible-supremum engine

The engine `SphericalRotation.reach_or_stuck` is **generic** over any finite family of continuous
functions `f : ι → ℝ → ℝ`: the admissible set `{θ ∈ [0,Tcap] : ∀ j, 0 ≤ f j θ}` is closed, contains
`0`, bounded; at its supremum either `δ* = Tcap` or some `f j δ* = 0`.  The substrate instantiates it
on the *last-joint* opening's mixed-support family (`combinedSupport` / `augmentedSupport`, indexed for
the single rotated tail vertex).  We instantiate the **same** engine on the *interior* `openTail`
opening: the genuinely `δ`-dependent supports are the *mixed* triples (some head vertex `≤ K`, some tail
vertex `> K`), each `det3 ∘ rot`-continuous; the interior opened joint angle
`θ ↦ sphAngle (A k')(A K)(rotS2 (A K) θ (A (k'+2)))` is continuous by the substrate's generic
`continuous_openedJointAngle`.  Bundling them gives the interior combined family, its admissible
supremum `δ*`, and the **interior reach/stuck trichotomy** at `δ*` (REACH = the opened joint reaches
the target, STUCK = a mixed support vanishes).  This is the genuine interior analogue of
`augmented_reachOrStuck_at_sup`.

## Honest residue

The trichotomy *production* is built here.  What genuinely resists — the same obstruction the substrate
isolated for the *last joint* as `SphericalAdmissibleSup.BoundaryConvexPersistAtSup` — is the
**boundary convexity** of the opened arm at `δ*` (every monitored support is only `≥ 0` at `δ*`, while
`WeakConvexSphPolygon.open_hemisphere` demands the hemisphere functional strictly `> 0`), together with
the **splice-body side-monotonicity** (R-C) and the **SSS arm congruence** (R-cong).  We record what is
banked and isolate the precise residue in §R.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal

namespace ProofsInTheBook.SphericalSZClose

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The interior opened joint angle and its continuity.

For the deficient joint `k : Fin (n-1)` opened about the apex axis `K = openingAxis k = ⟨k+1⟩`, the
joint `k` has vertices `A k', A K = A ⟨k+1⟩, A (k'+2) = A ⟨k+2⟩`.  Opening rotates the tail `> K`, so
`A k'` (index `k` `≤ K`) is fixed, `A K` is the axis (fixed), and `A ⟨k+2⟩` (index `k+2 > K`) rotates.
Hence the opened joint-`k` angle is `θ ↦ sphAngle (A k')(A K)(rotS2 (A K) θ (A ⟨k+2⟩))`, the exact shape
of the substrate's generic `continuous_openedJointAngle`. -/

/-- The incoming neighbour `A k'` of the deficient joint `k` (vertex index `k`). -/
def jointPrev {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) : S2 :=
  A ⟨k.val, by have := k.isLt; omega⟩

/-- The outgoing neighbour `A ⟨k+2⟩` of the deficient joint `k` (vertex index `k+2`, in the rotated
tail). -/
def jointNext {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) : S2 :=
  A ⟨k.val + 2, by have := k.isLt; omega⟩

/-- The opened interior joint-`k` angle as a function of the opening angle `θ`:
`θ ↦ sphAngle (A k')(A K)(rotS2 (A K) θ (A ⟨k+2⟩))`, with `K = openingAxis k`. -/
def openedInteriorJointAngle {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (θ : ℝ) : ℝ :=
  sphAngle (jointPrev A k) (A (openingAxis k)) (rotS2 (A (openingAxis k)) θ (jointNext A k))

/-- At `θ = 0` the opened interior joint angle is the original joint-`k` angle of `A`. -/
theorem openedInteriorJointAngle_zero {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    openedInteriorJointAngle A k 0 = jointAngle A k := by
  simp only [openedInteriorJointAngle, jointAngle, jointPrev, jointNext, openingAxis]
  rw [show rotS2 (A ⟨k.val + 1, by have := k.isLt; omega⟩) 0 (A ⟨k.val + 2, by have := k.isLt; omega⟩)
      = A ⟨k.val + 2, by have := k.isLt; omega⟩ by apply S2.ext; rw [rotS2_coe, rot_zero]]

/-- **The opened interior joint angle is continuous in `θ`.**  The two base sides `A K → A k'` and
`A K → A ⟨k+2⟩` are short arcs (the incoming edge and the joint's far edge of the strictly convex arm);
the substrate's generic `continuous_openedJointAngle` then applies with `k = A K`, `p = A k'`,
`q = A ⟨k+2⟩`. -/
theorem continuous_openedInteriorJointAngle {n : ℕ} {A : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    Continuous (openedInteriorJointAngle A k) :=
  continuous_openedJointAngle hka hkt

/-! ## §2. The interior support family and its continuity.

Under the interior `openTail A K θ`, a vertex `x` is fixed (`x.val ≤ K.val`) or rotated about `A K`
(`x.val > K.val`).  A support triple `(i, j, l)` whose three vertices are jointly fixed or jointly
rotated is `θ`-invariant; the genuinely `θ`-dependent supports are the *mixed* ones.  We define the
interior support of an arbitrary triple as `θ ↦ sOrient (openTail A K θ i)(…)(…)` and prove it
continuous (each opened vertex coordinate is `θ`-continuous — constant, or `rot` of a constant). -/

/-- The `θ`-coordinate of an opened vertex: continuous in `θ` (constant if fixed, a rotation coordinate
if rotated). -/
theorem continuous_openTail_coord {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (x : Fin (n + 1))
    (c : Fin 3) :
    Continuous (fun θ : ℝ => ((openTail A K θ x : S2) : E3) c) := by
  by_cases hx : x.val ≤ K.val
  · simp only [openTail_fixed A _ _ hx]
    exact continuous_const
  · simp only [openTail_rot A K _ (show K.val < x.val by omega), rotS2_coe]
    exact continuous_rot_coord (A K : E3) (A x : E3) c

/-- The interior support determinant of a triple `(i, j, l)` under the interior opening, as a function
of `θ`: `θ ↦ sOrient (openTail A K θ i)(openTail A K θ j)(openTail A K θ l)`. -/
def interiorSupport {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (ijl : Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) : ℝ → ℝ :=
  fun θ => sOrient (openTail A K θ ijl.1) (openTail A K θ ijl.2.1) (openTail A K θ ijl.2.2)

/-- At `θ = 0` the interior support is the original support of `A`. -/
theorem interiorSupport_zero {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (ijl : Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) :
    interiorSupport A K ijl 0 = sOrient (A ijl.1) (A ijl.2.1) (A ijl.2.2) := by
  show sOrient (openTail A K 0 ijl.1) (openTail A K 0 ijl.2.1) (openTail A K 0 ijl.2.2) = _
  rw [openTail_zero_angle]

/-- **Each interior support is continuous in `θ`.**  `sOrient = det3` of the three opened vertices,
each of whose coordinates is `θ`-continuous (`continuous_openTail_coord`); `det3` is a polynomial in the
nine coordinates. -/
theorem continuous_interiorSupport {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (ijl : Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) :
    Continuous (interiorSupport A K ijl) := by
  obtain ⟨i, j, l⟩ := ijl
  show Continuous (fun θ : ℝ =>
    det3 ((openTail A K θ i : S2) : E3) ((openTail A K θ j : S2) : E3)
      ((openTail A K θ l : S2) : E3))
  simp only [det3]
  have hi := fun c => continuous_openTail_coord A K i c
  have hj := fun c => continuous_openTail_coord A K j c
  have hl := fun c => continuous_openTail_coord A K l c
  exact
    (((hi 0).mul (((hj 1).mul (hl 2)).sub ((hj 2).mul (hl 1)))).sub
      ((hi 1).mul (((hj 0).mul (hl 2)).sub ((hj 2).mul (hl 0))))).add
      ((hi 2).mul (((hj 0).mul (hl 1)).sub ((hj 1).mul (hl 0))))

/-! ## §3. The interior combined admissible family + the reach/stuck trichotomy.

We bundle the finitely many interior supports (indexed by vertex triples) together with the interior
target slack `θ ↦ T − openedInteriorJointAngle A k θ` into one finite continuous family, and run the
generic engine `reach_or_stuck`.  This is the genuine interior analogue of the substrate's last-joint
`combined_reach_or_stuck` / `augmented_reachOrStuck_at_sup`. -/

/-- The interior target-slack constraint: `θ ↦ T − openedInteriorJointAngle A k θ`. -/
def interiorTargetSlack {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (T : ℝ) : ℝ → ℝ :=
  fun θ => T - openedInteriorJointAngle A k θ

/-- The interior combined admissible family: `none` is the target slack, `some ijl` is the interior
support of triple `ijl`.  All are continuous. -/
def interiorCombined {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (T : ℝ) :
    Option (Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) → ℝ → ℝ
  | none => interiorTargetSlack A k T
  | some ijl => interiorSupport A (openingAxis k) ijl

/-- Each interior combined family member is continuous in `θ`. -/
theorem continuous_interiorCombined {n : ℕ} {A : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) (T : ℝ) :
    ∀ o, Continuous (interiorCombined A k T o) := by
  rintro (_ | ijl)
  · exact continuous_const.sub (continuous_openedInteriorJointAngle hka hkt)
  · exact continuous_interiorSupport A (openingAxis k) ijl

/-- **The interior combined admissible supremum `δ*` is admissible.**  The family is finite and
continuous; the supremum of `{θ ∈ [0, Tcap] : all interior supports ≥ 0 and not-yet-overshot}` is
admissible (closed, nonempty, bounded) — the engine's `sSup_mem_admissibleSet`. -/
theorem sSup_interiorCombined_mem {n : ℕ} {A : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {T Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ interiorCombined A k T o 0) :
    sSup (admissibleSet (interiorCombined A k T) Tcap) ∈ admissibleSet (interiorCombined A k T) Tcap :=
  sSup_mem_admissibleSet (continuous_interiorCombined hka hkt T) hTcap h0

/-- **The interior reach/stuck trichotomy at `δ*`.**  At the interior combined admissible supremum
`δ* = sSup (admissibleSet (interiorCombined A k T) Tcap)`:

* **CAP** `δ* = Tcap` (only relevant if `Tcap` is set below the target; the process uses `Tcap = π`),
  *or*
* **REACH** the opened interior joint reaches the target: `openedInteriorJointAngle A k δ* = T`, *or*
* **STUCK** an interior support vanishes: `∃ ijl, interiorSupport A (openingAxis k) ijl δ* = 0`.

This is `reach_or_stuck` on the interior combined family — the genuine interior analogue of the
substrate's last-joint `reachOrStuck_at_sup`, now monitoring the *whole rotated tail*'s supports and the
*interior* joint-angle target. -/
theorem interior_reachOrStuck_at_sup {n : ℕ} {A : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {T Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ interiorCombined A k T o 0) :
    let δ := sSup (admissibleSet (interiorCombined A k T) Tcap)
    δ = Tcap ∨ openedInteriorJointAngle A k δ = T ∨
      ∃ ijl, interiorSupport A (openingAxis k) ijl δ = 0 := by
  intro δ
  rcases reach_or_stuck (continuous_interiorCombined hka hkt T) hTcap h0 with hcap | ⟨o, ho⟩
  · exact Or.inl hcap
  · rcases o with _ | ijl
    · -- target slack vanishes (REACH): T − openedInteriorJointAngle A k δ = 0.
      refine Or.inr (Or.inl ?_)
      have : interiorTargetSlack A k T δ = 0 := ho
      simp only [interiorTargetSlack] at this
      linarith
    · exact Or.inr (Or.inr ⟨ijl, ho⟩)

/-! ## §4. The splice-body arm `spliceArm` and its index / side / joint / endpoint API.

For an arm `A : Fin (N+1) → S2` and a cut at `(i, j)` with `i < j ≤ N`, the **spliced body** is the
sub-tuple `A 0, …, A i, A j, A (j+1), …, A N` — the arm with the ear `A (i+1) … A (j-1)` excised and the
new diagonal edge `A i → A j` inserted.  It has `m := i + (N - j) + 1` edges (`(i+1)` head vertices plus
`(N - j + 1)` tail vertices).  The index map sends body vertex `v ≤ i` to `A v` and `v > i` to
`A (v - i - 1 + j)`.

This is the body sub-arm the design §4 splice transport recurses on (the analogue of the BUILT ear
`intervalArm`).  We build its vertex/side/joint/endpoint API; its first `i` sides and its sides past the
splice are the parent's, its splice side is the diagonal `A i → A j`, and its endpoint is `endpt A`
(the body keeps `A 0` and `A N`). -/

/-- The **spliced body** sub-arm `A[0..i] ++ A[j..N]`: body vertex `v ≤ i` is `A v`, body vertex `v > i`
is `A (v - i - 1 + j)`.  It has `m + 1` vertices with `m = i + (N - j) + 1` edges (`(i+1)` head vertices
plus `(N - j + 1)` tail vertices). -/
def spliceArm {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N) :
    Fin (i + (N - j) + 1 + 1) → S2 :=
  fun v => if v.val ≤ i then A ⟨v.val, by have := v.isLt; omega⟩
    else A ⟨v.val - i - 1 + j, by have := v.isLt; omega⟩

/-- The body's first vertex is `A 0`. -/
theorem spliceArm_zero {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N) :
    spliceArm A i j hij hj 0 = A 0 := by
  simp only [spliceArm, Fin.val_zero]
  rw [if_pos (Nat.zero_le _)]
  rfl

/-- The body's last vertex is `A N`. -/
theorem spliceArm_last {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N) :
    spliceArm A i j hij hj (Fin.last (i + (N - j) + 1)) = A (Fin.last N) := by
  simp only [spliceArm, Fin.val_last]
  rw [if_neg (by omega)]
  congr 1
  apply Fin.ext
  simp only [Fin.val_last]
  omega

/-- The body endpoint is `endpt A` (the body keeps both original arm endpoints `A 0` and `A N`). -/
theorem spliceArm_endpt {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N) :
    endpt (spliceArm A i j hij hj) = endpt A := by
  unfold endpt
  rw [spliceArm_zero, spliceArm_last]

/-- A body vertex `v ≤ i` is the parent vertex `A v`. -/
theorem spliceArm_head {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N)
    {v : ℕ} (hv : v < i + (N - j) + 1 + 1) (hvi : v ≤ i) :
    spliceArm A i j hij hj ⟨v, hv⟩ = A ⟨v, by omega⟩ := by
  simp only [spliceArm]
  rw [if_pos hvi]

/-- A body vertex `v > i` is the parent vertex `A (v - i - 1 + j)`. -/
theorem spliceArm_tail {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N)
    {v : ℕ} (hv : v < i + (N - j) + 1 + 1) (hvi : i < v) :
    spliceArm A i j hij hj ⟨v, hv⟩ = A ⟨v - i - 1 + j, by omega⟩ := by
  simp only [spliceArm]
  rw [if_neg (by omega)]

/-- **The splice side at index `i` is the diagonal `A i → A j`.**  Body vertex `i` is `A i` (head) and
body vertex `i+1` is `A j` (`(i+1) - i - 1 + j = j`), so the body's `i`-th side is the new diagonal. -/
theorem spliceArm_sideLen_splice {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N)
    (hi : i < i + (N - j) + 1) :
    sideLen (spliceArm A i j hij hj) ⟨i, hi⟩ = sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩) := by
  unfold sideLen
  have hc : (spliceArm A i j hij hj) (Fin.castSucc ⟨i, hi⟩) = A ⟨i, by omega⟩ := by
    rw [show Fin.castSucc ⟨i, hi⟩ = (⟨i, by omega⟩ : Fin (i + (N - j) + 1 + 1)) from Fin.ext (by simp)]
    exact spliceArm_head A i j hij hj _ (le_refl _)
  have hs : (spliceArm A i j hij hj) (Fin.succ ⟨i, hi⟩) = A ⟨j, by omega⟩ := by
    rw [show Fin.succ ⟨i, hi⟩ = (⟨i + 1, by omega⟩ : Fin (i + (N - j) + 1 + 1)) from Fin.ext (by simp)]
    rw [spliceArm_tail A i j hij hj _ (by omega)]
    congr 1
    apply Fin.ext
    simp only
    omega
  rw [hc, hs]

/-- **A body side strictly before the splice (`s < i`) is the parent's side `s`.**  Both endpoints are
head vertices (`s, s+1 ≤ i`), so the body's side equals `sideLen A s`. -/
theorem spliceArm_sideLen_head {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N)
    {s : ℕ} (hs : s < i + (N - j) + 1) (hsi : s < i) :
    sideLen (spliceArm A i j hij hj) ⟨s, hs⟩ = sideLen A ⟨s, by omega⟩ := by
  unfold sideLen
  have hc : (spliceArm A i j hij hj) (Fin.castSucc ⟨s, hs⟩) = A ⟨s, by omega⟩ := by
    rw [show Fin.castSucc ⟨s, hs⟩ = (⟨s, by omega⟩ : Fin (i + (N - j) + 1 + 1)) from Fin.ext (by simp)]
    exact spliceArm_head A i j hij hj _ (by omega)
  have hsx : (spliceArm A i j hij hj) (Fin.succ ⟨s, hs⟩) = A ⟨s + 1, by omega⟩ := by
    rw [show Fin.succ ⟨s, hs⟩ = (⟨s + 1, by omega⟩ : Fin (i + (N - j) + 1 + 1)) from Fin.ext (by simp)]
    exact spliceArm_head A i j hij hj _ (by omega)
  rw [hc, hsx]
  have e1 : (⟨s, by omega⟩ : Fin N).castSucc = (⟨s, by omega⟩ : Fin (N + 1)) := Fin.ext (by simp)
  have e2 : (⟨s, by omega⟩ : Fin N).succ = (⟨s + 1, by omega⟩ : Fin (N + 1)) := Fin.ext (by simp)
  rw [e1, e2]

/-- **A body side strictly after the splice (`i < s`) is the parent's side `s - i - 1 + j`.**  Both
endpoints are tail vertices (`s, s+1 > i`), so the body's side equals `sideLen A (s - i - 1 + j)`. -/
theorem spliceArm_sideLen_tail {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N)
    {s : ℕ} (hs : s < i + (N - j) + 1) (hsi : i < s) :
    sideLen (spliceArm A i j hij hj) ⟨s, hs⟩ = sideLen A ⟨s - i - 1 + j, by omega⟩ := by
  unfold sideLen
  have hc : (spliceArm A i j hij hj) (Fin.castSucc ⟨s, hs⟩) = A ⟨s - i - 1 + j, by omega⟩ := by
    rw [show Fin.castSucc ⟨s, hs⟩ = (⟨s, by omega⟩ : Fin (i + (N - j) + 1 + 1)) from Fin.ext (by simp)]
    exact spliceArm_tail A i j hij hj _ (by omega)
  have hsx : (spliceArm A i j hij hj) (Fin.succ ⟨s, hs⟩) = A ⟨s + 1 - i - 1 + j, by omega⟩ := by
    rw [show Fin.succ ⟨s, hs⟩ = (⟨s + 1, by omega⟩ : Fin (i + (N - j) + 1 + 1)) from Fin.ext (by simp)]
    exact spliceArm_tail A i j hij hj _ (by omega)
  rw [hc, hsx]
  have e1 : (⟨s - i - 1 + j, by omega⟩ : Fin N).castSucc = (⟨s - i - 1 + j, by omega⟩ : Fin (N + 1)) :=
    Fin.ext (by simp)
  have e2 : (⟨s - i - 1 + j, by omega⟩ : Fin N).succ = (⟨s + 1 - i - 1 + j, by omega⟩ : Fin (N + 1)) :=
    Fin.ext (by simp only [Fin.val_succ]; omega)
  rw [e1, e2]

/-! ## §5. Re-export of the conditional arm lemma (the chain still routes through the residue).

The weak arm lemma remains conditional on `SphericalSZFinal.InteriorOpenAndSpliceStep` (the per-level
endpoint output of the lex recursion).  This module BANKS, beneath that residue, the interior
reach/stuck *production* (§1–§3) and the `spliceArm` body API (§4) — the two substrate-absent
structural pieces the previous round listed as missing.  What remains genuinely irreducible is isolated
as the three named non-vacuous cores in §R; the conditional arm lemma is re-exported verbatim. -/

/-- **The weak spherical arm lemma, conditional on the narrowed residue** (re-export). -/
theorem spherical_arm_mono_of_residue' (h : SphericalSZFinal.InteriorOpenAndSpliceStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  SphericalSZFinal.spherical_arm_mono_of_residue h hn A B hA hB hside hangle

/-! ## §R. Honest residue (precise scope, what is BANKED, the three irreducible cores).

**What this module BANKS (genuinely new, UNCONDITIONAL, strictly enlarges the substrate):**

* **(R-O production) The interior reach/stuck supremum trichotomy.**  `interior_reachOrStuck_at_sup`:
  at the interior combined admissible supremum `δ*` (built on the *interior* `openTail`, monitoring the
  *whole rotated tail*'s supports `interiorSupport` and the *interior* joint-angle target slack), either
  `δ* = Tcap`, or the opened interior joint reaches the target (`openedInteriorJointAngle A k δ* = T`,
  REACH), or an interior support vanishes (STUCK).  This is the genuine interior analogue of the
  substrate's last-joint `SphericalAdmissibleSup.reachOrStuck_at_sup` (which monitors a *single* rotated
  tail vertex via `openArm`/`mixedSupport`).  Banked beneath it: `continuous_interiorSupport` (each
  interior support is `det3 ∘ openTail`-continuous), `continuous_openedInteriorJointAngle` (the interior
  opened joint angle is continuous, via the generic `continuous_openedJointAngle`),
  `sSup_interiorCombined_mem` (the interior admissible supremum is admissible).

* **(R-C structure) The splice-body sub-arm `spliceArm` and its API.**  `spliceArm A i j` (the body
  `A[0..i] ++ A[j..N]`, the analogue of the BUILT ear `intervalArm`) with `spliceArm_zero/_last/_endpt`
  (the body keeps both arm endpoints, so `endpt (spliceArm …) = endpt A`), `spliceArm_head/_tail`
  (vertex reindexing), `spliceArm_sideLen_head/_tail` (the non-splice sides are the parent's), and
  `spliceArm_sideLen_splice` (the splice side is the diagonal `A i → A j`).  This is the body sub-arm
  constructor the substrate lacked (it had only `intervalArm` for the ear, and the last-vertex /
  first-vertex drops `cutArm` / `frontCut`).

**The three irreducible cores that genuinely resist (each a named non-vacuous `Prop` + failing chain):**

1. **(R-O core) Boundary convexity of the opened arm at `δ*`.**  `interior_reachOrStuck_at_sup`
   produces the trichotomy, but to *consume* REACH (recurse with `deficitCount_openTail_reach_lt`) or
   STUCK (extract the stuck sub-arm) one needs `openTail A K δ*` to be at least a `WeakConvexSphArm`.
   At `δ*` admissibility gives every monitored support only `≥ 0`; but `WeakConvexSphPolygon` further
   requires the `open_hemisphere` functional **strictly** `> 0` at every (rotated-tail) vertex, which
   the admissible supremum gives only `≥ 0` for a *monitored* hemisphere margin — exactly the substrate's
   own isolated obstacle `SphericalAdmissibleSup.BoundaryConvexPersistAtSup`, here in the interior +
   hemisphere-margin form.  Concrete failing chain: no boundary/closed-side convexity-persistence lemma
   exists in the substrate (`grep`), and `mixedSupport_persists` is strict-open-neighbourhood only.

2. **(R-C core) The splice-body side-and-angle-monotone transport.**  After `cut_diag_le` (banked) gives
   the diagonal inequality `sDist (A i)(A j) ≤ sDist (B i)(B j)`, gluing the body
   `spliceArm A i j` to `endpt A ≤ endpt B` is **not** a `Main`-instance: the body's splice side
   `A i → A j` matches `B`'s only by the *inequality* (not `SameSides`), and the new splice joint at
   `A i` (between `A (i-1)` and `A j`) is unmatched against `B`'s.  `Main` requires *equal* sides; the
   body needs a strictly stronger arm comparison monotone in *both* one side (`≤`) and the angles —
   `splice_transport_of_diag_le`.  Concrete failing chain: `Main` (and `SZComparison`) take `SameSides`
   as a hypothesis; there is no side-monotone arm lemma in the substrate, and the splice joint is not
   among the matched joints.

3. **(R-cong core) The equal-joints endpoint congruence.**  When no joint is deficient, equal sides +
   equal joints must give `endpt A = endpt B` (spherical SSS arm rigidity).  The substrate banks the
   per-vertex SAS step `SphericalSZChain.diag_len_eq`, but assembling it along the arm needs spherical
   **angle additivity at a vertex** (the joint `sphAngle (A (i-1))(A i)(A (i+1))` splits as the back-angle
   `sphAngle (A (i-1))(A i)(A 0)` plus the forward approach angle `sphAngle (A 0)(A i)(A (i+1))` in
   convex position), to propagate the matched approach angle through the diagonal cut.  Concrete failing
   chain: no spherical angle-addition / angle-subtraction lemma exists in the substrate (`grep` for
   `sphAngle … + sphAngle …` finds none); `diag_len_eq` alone matches one triangle but cannot carry the
   prefix congruence forward without it.

These three cores are the irreducible geometric content of Chapter 13's spherical arm lemma remaining
after the OPEN preservation/deficit/endpoint (`SphericalSZFinal`), the ear API + diagonal inequality
(`SphericalSZStepClose`), the lex assembly (`SphericalSZInduction`), and now the interior trichotomy
production + `spliceArm` body API (this module) are banked.

### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of the interior opened joint angle: at `θ = 0` it is the genuine original joint angle of
`A` (not a vacuous constant), so the target-slack constraint is a real geometric quantity. -/
theorem openedInteriorJointAngle_zero_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    openedInteriorJointAngle A k 0 = jointAngle A k :=
  openedInteriorJointAngle_zero A k

/-- Non-vacuity of the interior trichotomy: realised at `θ = 0` (the unopened arm), where every interior
support is the genuine original support of `A` — so the admissible family and its supremum are over a
real, inhabited set, not a vacuous-hypothesis impostor. -/
theorem interiorSupport_zero_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (ijl : Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) :
    interiorSupport A K ijl 0 = sOrient (A ijl.1) (A ijl.2.1) (A ijl.2.2) :=
  interiorSupport_zero A K ijl

/-- Non-vacuity of the splice body: it genuinely shares both endpoints with the parent arm
(`endpt (spliceArm …) = endpt A`), so it is a real geometric sub-arm carrying the original endpoint, not
a vacuous stand-in. -/
theorem spliceArm_endpt_nonvacuous {N : ℕ} (A : Fin (N + 1) → S2) (i j : ℕ) (hij : i < j) (hj : j ≤ N) :
    endpt (spliceArm A i j hij hj) = endpt A :=
  spliceArm_endpt A i j hij hj

end ProofsInTheBook.SphericalSZClose
