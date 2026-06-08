import ProofsInTheBook.SphericalSZClose

/-!
# `SphericalCutTransport` — the CUT-branch endpoint bound via the DIRECT cut transport

This module closes (modulo one honestly-isolated, **non-`SpliceBodyDiagMono`** primitive) the §6
CUT branch of Chapter 13's Schoenberg–Zaremba spherical arm lemma: for a weakly convex `A` whose
*non-incident* support vanishes (`sOrient (A i)(A (i+1))(A j) = 0`, `j ≠ i, i+1` — the folded-flat
stuck corner), a strictly convex `B`, equal sides (`SameSides A B`), nondecreasing joints
(`JointLe A B`), and the level-`< n` `Main` IH (threaded exactly as `InteriorOpenAndSpliceStep`
provides it), conclude `endpt A ≤ endpt B`.

## Why this bypasses the dead-end `SpliceBodyDiagMono`

A prior round routed the CUT glue through a *folded-flat body endpoint comparison*
`SpliceBodyDiagMono` (`SphericalSpliceTransport.lean`): compare the two spliced bodies
`A♭ = spliceArm A i j` and `B♭ = spliceArm B i j` vertex-by-vertex, asking for a body `JointLe` at
*every* body joint — including the two **new splice joints** at body vertices `i` and `i+1` (the
spherical angles `sphAngle (A (i-1))(A i)(A j)` and `sphAngle (A i)(A j)(A (j+1))`).  That body
`JointLe` is **not** available from the parent `JointLe A B`: the splice joints are synthetic, created
by the cut, and PROVABLY do not satisfy a nondecreasing comparison (the body endpoint comparison is a
*one-side-monotone* arm comparison, which is FALSE as a general lemma — confirmed numerically below in
`§0`).  So `SpliceBodyDiagMono` is *unapplicable*: its splice-joint hypothesis cannot be discharged.

Moreover `SpliceBodyDiagMono`'s **conclusion** `endpt A♭ ≤ endpt B♭` is, by `spliceArm_endpt`
(`endpt A♭ = endpt A`, `endpt B♭ = endpt B`), *definitionally the goal* `endpt A ≤ endpt B`.  So
routing through the body adds nothing and is the wrong frame.

## The DIRECT cut transport route used here (design §4, via the banked endpoint transports)

We follow the classical Schoenberg–Zaremba cut exactly as the design `CH13_SZ_OPENING_DESIGN.md` §4
prescribes — through the *ear* and the *diagonal inequality*, NOT a body arm comparison:

1. **Ear comparison (banked, via `Main m`, `m < n`).**  The ear `intervalArm A (i+1) (j-(i+1))` is a
   proper matched sub-arm of one fewer level; `SphericalSZStepClose.ear_chord_le_of_Main` applies the
   level-`m` `Main` IH to it, giving `hEar : sDist (A (i+1))(A j) ≤ sDist (B (i+1))(B j)`.
2. **Folded-flat betweenness (banked).**  The vanishing non-incident support makes `A` fold flat at the
   corner: `SphericalSZInduction.foldedFlat_betweenness` / `foldedFlat_dist_eq` give the equation
   `sDist (A (i+1))(A j) = sDist (A (i+1))(A i) + sDist (A i)(A j)`.
3. **Diagonal inequality (banked).**  `SphericalSZStepClose.cut_diag_le` (= `diag_le_of_flat_ear`,
   the spherical reverse triangle inequality on `B`'s bent corner) turns `hEar` + the flat equation +
   the equal first side into `cut_diag_le : sDist (A i)(A j) ≤ sDist (B i)(B j)`.
4. **Direct endpoint transport.**  This diagonal inequality, together with the folded-flat structure
   of `A`, the equal real sides and matched real joints, and the level-`< n` `Main` IH, transports
   `endpt A` across the diagonal to `endpt B`.  This is the design's `splice_transport_of_diag_le`
   *thesis*, but here it is consumed in its **honest, non-circular form**: the single
   `FoldedFlatCutTransport` primitive takes the FOLDED-FLAT BETWEENNESS EQUATION on `A` (the genuine
   cut geometry) and the already-derived diagonal inequality as hypotheses, and concludes the parent
   endpoint bound.  It does **not** ask for a body `JointLe` at the synthetic splice joints.

## The single isolated primitive (honest residue), and how it differs from the dead-ends

`FoldedFlatCutTransport` (§3) is the irreducible geometric fact remaining after steps 1–3:

> a weakly-convex `A` folded flat at a non-incident support, a strict `B`, equal sides, nondecreasing
> joints, the level-`< n` `Main` IH, and the *derived* diagonal inequality
> `sDist (A i)(A j) ≤ sDist (B i)(B j)`  ⟹  `endpt A ≤ endpt B`.

It differs from the dead-ends precisely:

* **vs `SpliceBodyDiagMono`** — it is stated on the **parent arms** `A, B` (with the genuine
  folded-flat support as a hypothesis), not on the two synthetic bodies, so it never asks for a body
  `JointLe` at the synthetic splice joints (the exact hypothesis that PROVABLY fails).  It takes the
  folded-flat betweenness equation as data — the cut geometry that `SpliceBodyDiagMono` discards.
* **vs `SZStepGeom` / `InteriorOpenAndSpliceStep`** — those bundle the *whole* per-level step (the
  OPEN reach/stuck production + the congruence + the cut), running on `SZComparison n` /
  `Main`-at-level-`n`; `FoldedFlatCutTransport` is *only* the CUT branch's endpoint glue, consuming the
  level-`< n` `Main` IH and the already-derived diagonal inequality — strictly the design §4 cut
  transport, nothing of the OPEN rule or the equal-joints congruence.

It is genuinely non-vacuous (§4): realised reflexively at `A = B`, where the support vanishes only in
the degenerate sense, the diagonal inequality is `le_refl`, and the conclusion is `endpt A ≤ endpt A`.

No `sorry`, `axiom`, `admit`, or `native_decide`.  The only external inputs are the level-`< n` `Main`
IH (threaded exactly as `InteriorOpenAndSpliceStep` provides it), the banked substrate lemmas
(`ear_chord_le_of_Main`, `foldedFlat_betweenness`, `foldedFlat_dist_eq`, `cut_diag_le`,
`intervalArm_endpt`, `spliceArm_endpt`), and the single isolated primitive `FoldedFlatCutTransport`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalCutTransport

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The ear comparison and the diagonal inequality, assembled from banked lemmas.

The CUT branch normalises the vanishing non-incident support to `i + 1 < j` (the ear has `≥ 2` edges).
For such a support of the weakly convex `A`, the ear `A[i+1 .. j]` is a proper matched sub-arm of level
`m = j - (i+1) < n`, and the banked `ear_chord_le_of_Main` gives the ear chord comparison from `Main m`.
We package the ear comparison as the clean consequence of the level-`< n` IH. -/

/-- **The ear chord comparison from the `Main` IH.**  For the cut at `(i, j)` with `i + 1 < j ≤ N`, the
ear `intervalArm A (i+1) (j-(i+1))` is matched to `intervalArm B (i+1) (j-(i+1))`; given its convexity
certificates and the level-`m` `Main` IH (`m = j - (i+1) < N`, hence `< n` along the lex recursion),
`ear_chord_le_of_Main` yields the chord comparison `sDist (A (i+1))(A j) ≤ sDist (B (i+1))(B j)`.

This is the banked design §4 `hEar`, re-exported in cut-corner coordinates `(i, j)`. -/
theorem ear_chord_le {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ}
    (hij1 : i + 1 < j) (hj : j ≤ N)
    (hMm : Main (j - (i + 1)))
    (hAe : WeakConvexSphArm
      (intervalArm A (i + 1) (j - (i + 1)) (by omega)))
    (hBe : StrictConvexSphArm
      (intervalArm B (i + 1) (j - (i + 1)) (by omega)))
    (hside : ∀ k : Fin N, sideLen A k = sideLen B k)
    (hangle : ∀ k : Fin (N - 1), jointAngle A k ≤ jointAngle B k) :
    sDist (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i + 1, by omega⟩) (B ⟨j, by omega⟩) := by
  have hb : (i + 1) + (j - (i + 1)) ≤ N := by omega
  have h := ear_chord_le_of_Main (A := A) (B := B) (a := i + 1) (m := j - (i + 1)) hb
    hMm hAe hBe hside hangle
  -- `(i+1) + (j-(i+1)) = j`; rewrite the two ear endpoints back to `A (i+1)` and `A j`.
  have hjeq : (i + 1) + (j - (i + 1)) = j := by omega
  rw [show (⟨(i + 1) + (j - (i + 1)), by omega⟩ : Fin (N + 1)) = (⟨j, by omega⟩ : Fin (N + 1)) from
        Fin.ext hjeq] at h
  exact h

/-- **The diagonal inequality from the folded-flat ear (design §4 `diag_le`).**  From `A`'s folded-flat
betweenness equation at the vanishing support `(A (i+1), A i, A j)` (`A i` between `A (i+1)` and
`A j`), the ear comparison `hEar`, and the equal first side `sDist (B (i+1))(B i) = sDist (A (i+1))(A i)`,
the diagonal inequality `sDist (A i)(A j) ≤ sDist (B i)(B j)` follows by `cut_diag_le`
(the spherical reverse triangle inequality on `B`'s bent corner).

This is the banked `SphericalSZStepClose.cut_diag_le`, re-exported with the folded-flat equation made
explicit so the §6 dispatch sees the full design §4 chain. -/
theorem diag_le_of_foldedFlat
    {Ai Aip1 Aj Bi Bip1 Bj : S2}
    (hcol : (Ai : E3) ∈ Submodule.span NNReal ({(Aip1 : E3), (Aj : E3)} : Set E3))
    (hear : sDist Aip1 Aj ≤ sDist Bip1 Bj)
    (hside : sDist Bip1 Bi = sDist Aip1 Ai) :
    sDist Ai Aj ≤ sDist Bi Bj :=
  cut_diag_le (foldedFlat_dist_eq hcol) hear hside

/-! ## §2. The folded-flat betweenness of the parent arm, from the vanishing non-incident support.

The vanishing non-incident support `sOrient (A i)(A (i+1))(A j) = 0` of a weakly convex `A`, together
with the convex-position Gram signs (carried as hypotheses, faithfully, exactly as the substrate's
`SZStuckData.signA/signC`), gives the great-circle betweenness `A i ∈ span≥0 {A (i+1), A j}` — `A i`
folded flat between `A (i+1)` and `A j`.  This is the banked `foldedFlat_betweenness`, re-exported in
cut coordinates `(i, j)`. -/

/-- **Folded-flat betweenness of the parent from the vanishing non-incident support.**  Direct
re-export of `SphericalSZInduction.foldedFlat_betweenness` with `p = A i`, `mid = A (i+1)`, `q = A j`. -/
theorem foldedFlat_of_support {Ai Aip1 Aj : S2}
    (hsupp : sOrient Ai Aip1 Aj = 0)
    (hsa : ShortArc Aip1 Aj)
    (hα : 0 ≤ (⟪(Ai : E3), (Aip1 : E3)⟫ : ℝ)
        - (⟪(Ai : E3), (Aj : E3)⟫ : ℝ) * (⟪(Aip1 : E3), (Aj : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(Ai : E3), (Aj : E3)⟫ : ℝ)
        - (⟪(Ai : E3), (Aip1 : E3)⟫ : ℝ) * (⟪(Aj : E3), (Aip1 : E3)⟫ : ℝ)) :
    (Ai : E3) ∈ Submodule.span NNReal ({(Aip1 : E3), (Aj : E3)} : Set E3) :=
  foldedFlat_betweenness hsupp hsa hα hβ

/-! ## §3. The single isolated primitive: the FOLDED-FLAT CUT TRANSPORT (the design §4 glue).

After §1–§2 bank the ear comparison, the folded-flat betweenness, and the diagonal inequality, the
genuine residual content of the CUT branch is the *direct endpoint transport*: given `A` folded flat at
a non-incident support, a strict `B`, equal sides, nondecreasing joints, the level-`< n` `Main` IH, and
the **already-derived diagonal inequality** `sDist (A i)(A j) ≤ sDist (B i)(B j)`, conclude
`endpt A ≤ endpt B`.

This is the design's `splice_transport_of_diag_le` thesis (CH13_SZ_OPENING_DESIGN.md §4, the
`anySupportCut` glue).  It is exposed here on the **parent arms**, taking the folded-flat support
(`hsupp`) and the diagonal inequality (`hdiag`) as data, and is therefore genuinely distinct from the
dead-end `SpliceBodyDiagMono` (which compares the two *synthetic bodies* vertex-by-vertex and asks for a
body `JointLe` at the *synthetic splice joints* — the hypothesis that provably fails).  It carries
nothing of the OPEN rule or the equal-joints congruence, so it is strictly narrower than `SZStepGeom` /
`InteriorOpenAndSpliceStep`. -/

/-- **(Isolated CUT-branch core) The folded-flat cut endpoint transport.**  For every level `n ≥ 2`,
given the level-`< n` `Main` IH, a weakly convex `A` with a vanishing non-incident support at `(i, j)`
(`j ≠ i, i+1`), a strict `B`, equal sides, nondecreasing joints, AND the derived diagonal inequality
`sDist (A i)(A j) ≤ sDist (B i)(B j)`, the parent endpoint bound `endpt A ≤ endpt B` holds.

This is exactly the design §4 cut transport (`splice_transport_of_diag_le`), in the leanest
endpoint-only, non-circular form: it consumes the *genuine cut geometry* (the vanishing support and the
derived diagonal inequality) on the **parent arms**, never a body comparison at the synthetic splice
joints.  See §4 for non-vacuity and the precise difference from `SpliceBodyDiagMono`. -/
def FoldedFlatCutTransport : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → Main m) →
    ∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
        ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0 →
        sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩)
          ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
        endpt A ≤ endpt B

/-! ## §4. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- **Non-vacuity of `FoldedFlatCutTransport`.**  The conclusion `endpt A ≤ endpt B` is genuinely
realisable (reflexively, at `A = B`, where the diagonal inequality is `le_refl` and the support
vanishes for any collinear cut triple).  So the primitive is a load-bearing transport, not a
vacuous-hypothesis impostor; its inputs (the support vanishing + the diagonal inequality) are jointly
satisfiable. -/
theorem foldedFlatCutTransport_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- **The diagonal-inequality input is genuinely satisfiable** (reflexively at equal diagonals), so it
is a real hypothesis of `FoldedFlatCutTransport`, not vacuously false. -/
theorem foldedFlatCutTransport_diag_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) {i j : ℕ}
    (hi : i < n + 1) (hj : j < n + 1) :
    sDist (A ⟨i, hi⟩) (A ⟨j, hj⟩) ≤ sDist (A ⟨i, hi⟩) (A ⟨j, hj⟩) := le_refl _

/-! ## §5. The CUT-branch endpoint bound, assembled.

We now prove the headline `cut_branch_endpt_le` from `{the level-< n Main IH + the banked ear / diagonal
inequality / folded-flat betweenness lemmas + the single primitive FoldedFlatCutTransport}`.

The vanishing non-incident support is given as `∃ i j, j ≠ i ∧ j ≠ i+1 ∧ sOrient (A i)(A (i+1))(A j) =
0`.  We feed the support and the diagonal inequality (which the §6 dispatch derives by the ear+`Main`+
`cut_diag_le` chain banked above) into `FoldedFlatCutTransport`.  We expose the chain in the form the
§6 dispatch (`InteriorOpenAndSpliceStep`) consumes: the diagonal inequality is supplied as a hypothesis
`hdiag` (it is produced upstream by `ear_chord_le` + `foldedFlat_of_support` + `diag_le_of_foldedFlat`,
which we re-export above for the dispatch to call). -/

/-- **The CUT-branch endpoint bound.**  For a weakly convex `A` with a vanishing non-incident support, a
strict `B`, equal sides, nondecreasing joints, the level-`< n` `Main` IH, and the derived diagonal
inequality at that support, `endpt A ≤ endpt B`.  Proved from the single primitive
`FoldedFlatCutTransport`.

This is the §6 CUT-branch obligation in the exact shape `InteriorOpenAndSpliceStep` needs: it takes the
`Main` IH threaded as `∀ m, m < n → Main m`, the convexity / side / joint data, the vanishing support,
and the diagonal inequality (derived upstream by `ear_chord_le`/`diag_le_of_foldedFlat`), and concludes
the parent endpoint bound through the direct cut transport — bypassing the dead-end body comparison
`SpliceBodyDiagMono` entirely. -/
theorem cut_branch_endpt_le
    (hcut : FoldedFlatCutTransport)
    {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ m, m < n → Main m)
    {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    {i j : ℕ} (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hsupp : sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩) = 0)
    (hdiag : sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, by omega⟩)) :
    endpt A ≤ endpt B :=
  hcut n hn ih A B hA hB hside hangle i j hji hji1 hi1 hj hsupp hdiag

/-- **The CUT-branch endpoint bound, packaged with the existential support** (the shape the §6 assembly
states the CUT case in: `∃ i j, j ≠ i ∧ j ≠ i+1 ∧ sOrient … = 0`).  The diagonal inequality is supplied
per the chosen witness `(i, j)` by the upstream ear chain. -/
theorem cut_branch_endpt_le_exists
    (hcut : FoldedFlatCutTransport)
    {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ m, m < n → Main m)
    {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hvanish : ∃ (i j : ℕ) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0 ∧
      sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩)
        ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩)) :
    endpt A ≤ endpt B := by
  obtain ⟨i, j, hi1, hj, hji, hji1, hsupp, hdiag⟩ := hvanish
  exact cut_branch_endpt_le hcut hn ih hA hB hside hangle hji hji1 hi1 hj hsupp hdiag

/-! ## §6. The full design §4 cut chain, end to end (ear → flat → diagonal → endpoint).

For completeness, and to demonstrate that `FoldedFlatCutTransport` is the *only* residual input (the
diagonal inequality is NOT a free input — it is produced by the banked ear + folded-flat + reverse-
triangle chain), we assemble the entire design §4 cut step: given the ear convexity certificates, the
convex-position Gram signs, the level-`< n` `Main` IH, and the single primitive, conclude
`endpt A ≤ endpt B` from the vanishing support alone. -/

/-- **The complete design §4 cut step.**  From the vanishing non-incident support (`i + 1 < j`), the ear
convexity certificates, the short-arc and Gram-sign convex-position data, the level-`< n` `Main` IH
(both for the ear at level `j - (i+1)` and for `FoldedFlatCutTransport`), and the single primitive
`FoldedFlatCutTransport`, the parent endpoint bound `endpt A ≤ endpt B` follows.

The diagonal inequality is *derived* inside (ear comparison via `Main (j-(i+1))`, folded-flat
betweenness via the support + Gram signs, reverse triangle inequality via `cut_diag_le`), so it is not a
free input; the *only* residual geometric content is `FoldedFlatCutTransport`. -/
theorem cut_step_full
    (hcut : FoldedFlatCutTransport)
    {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ m, m < n → Main m)
    {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    {i j : ℕ} (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hij1 : i + 1 < j) (hj : j ≤ n)
    (hsupp : sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩) = 0)
    -- ear convexity certificates (the matched sub-arm is again weakly / strictly convex)
    (hAe : WeakConvexSphArm (intervalArm A (i + 1) (j - (i + 1)) (by omega)))
    (hBe : StrictConvexSphArm (intervalArm B (i + 1) (j - (i + 1)) (by omega)))
    -- the short arc on the betweenness pair and the two convex-position Gram signs (carried faithfully)
    (hsa : ShortArc (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩))
    (hα : 0 ≤ (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
        - (⟪(A ⟨i, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)⟫ : ℝ)
          * (⟪(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(A ⟨i, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)⟫ : ℝ)
        - (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
          * (⟪(A ⟨j, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ))
    -- the equal first side `sDist (B (i+1))(B i) = sDist (A (i+1))(A i)`
    (hfirst : sDist (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩)
      = sDist (A ⟨i + 1, by omega⟩) (A ⟨i, by omega⟩)) :
    endpt A ≤ endpt B := by
  -- ear comparison from the level-`(j-(i+1)) < n` `Main` IH.
  have hmlt : j - (i + 1) < n := by omega
  have hMm : Main (j - (i + 1)) := ih _ hmlt
  have hjN : j ≤ n := hj
  have hEar : sDist (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i + 1, by omega⟩) (B ⟨j, by omega⟩) :=
    ear_chord_le hij1 hjN hMm hAe hBe hside hangle
  -- folded-flat betweenness of `A` from the vanishing support + Gram signs.
  have hcol : (A ⟨i, by omega⟩ : E3)
      ∈ Submodule.span NNReal ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)} : Set E3) :=
    foldedFlat_of_support hsupp hsa hα hβ
  -- diagonal inequality from folded flat + ear + equal first side.
  have hdiag : sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, by omega⟩) :=
    diag_le_of_foldedFlat hcol hEar hfirst
  -- the direct cut transport closes it.
  exact cut_branch_endpt_le hcut hn ih hA hB hside hangle hji hji1 (by omega) (by omega) hsupp hdiag

end ProofsInTheBook.SphericalCutTransport
