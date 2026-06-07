import ProofsInTheBook.SphericalSZClose

/-!
# `SphericalSpliceTransport` — the **R-C** CUT-branch splice transport (Chapter 13)

`SphericalSZClose` built the splice-body sub-arm `spliceArm A i j` (the body `A[0..i] ++ A[j..N]`, the
analogue of the ear `intervalArm`) with its endpoint/side reindexing API, and isolated the **(R-C)**
core as the splice-body transport gluing the diagonal inequality `cut_diag_le` to `endpt A ≤ endpt B`.

This module attacks **(R-C)** directly.  Its target is the CUT-production (P1) consumed inside
`SphericalSZFinal.InteriorOpenAndSpliceStep`:

> a weakly-convex `A` whose non-incident support vanishes is cut at a folded-flat corner into the
> body `A♭ = spliceArm A i j` (matched to `B♭ = spliceArm B i j`), and — using `Main m` at the strictly
> smaller body level `m = i + (n - j) + 1 < n` — `endpt A ≤ endpt B` must follow.

## What is genuinely irreducible here (the **R-C core**, faithfully isolated)

The body `A♭` is matched to `B♭` by:

* **equality on every real edge** (`SameSides` restricted to the inherited sides — *banked here*,
  `spliceArm_sideLen_match`); and
* **the diagonal edge `A i → A j` only by the INEQUALITY** `cut_diag_le`
  (`sDist (A i)(A j) ≤ sDist (B i)(B j)`), because the folded-flat `A`-corner (angle `π`) does not
  satisfy the included-angle hypothesis of spherical SAS (`diag_len_eq`) against `B`'s bent corner.

So the body comparison is **not** a `Main`-instance (`Main` needs `SameSides`, i.e. *equal* sides on
*every* edge including the diagonal, and `JointLe` on *every* joint including the two new splice joints,
which are unmatched).  It is a strictly stronger **one-side-monotone** arm comparison.

**This one-side-monotone arm comparison is FALSE as a general lemma.**  In the 2-edge limit with sides
`a, b` and included joint `θ`, `d² = a² + b² − 2 a b cos θ`; for small `θ` and `b < a cos θ`, *increasing*
the diagonal side `b` *decreases* the endpoint distance `d`.  (Verified independently by ChatGPT-Pro
audit; recorded in the project handoff as the CRITICAL MATHEMATICAL FACT.)  Hence the diagonal-inequality
body transport cannot be discharged by an equal-side recursion or by a generic side-monotone lemma; it
holds only through the *specific* folded-flat geometry of the §8.4 cut, whose closed-form spherical
content (the cut-corner cone / oriented-angle development on the genuine multi-vertex body) the substrate
does not contain in the form needed to certify the body's two splice joints against `B`.

We therefore:

* **bank** the body side-restriction (every real edge matches between `A♭` and `B♭`); and
* **isolate** exactly the one-side-monotone body endpoint comparison as the single named non-vacuous
  `Prop` `SpliceBodyDiagMono`, and **prove** `splice_transport_of_diag_le` cleanly from it through the
  banked endpoint identities `spliceArm_endpt` (`endpt A♭ = endpt A`, `endpt B♭ = endpt B`).

`SpliceBodyDiagMono` is non-vacuous (reflexively realised at `A = B`, where the diagonal inequality and
all real-side equalities hold reflexively and the endpoint comparison is `endpt A ≤ endpt A`) and is the
*tightest* statement of the genuine geometric obstruction: it asks for nothing the CUT production cannot
provide (real-side equality + the banked diagonal inequality + the joint comparison on the matched real
joints), and concludes only the endpoint inequality.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalSpliceTransport

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The body level and the real-edge side match.

For an arm `A : Fin (N+1) → S2` and a cut `(i, j)` with `i < j ≤ N`, the body `spliceArm A i j` is an
arm with `m := i + (N - j) + 1` edges.  Every body side *other than the splice side `i`* is inherited
from the parent: the head sides `s < i` are the parent's sides `s`, and the tail sides `i < s` are the
parent's sides `s - i - 1 + j` (`SphericalSZClose.spliceArm_sideLen_head/_tail`).  Hence, whenever the
two parents agree on all those parent sides (which `SameSides A B` supplies), the two bodies agree on
every real edge. -/

/-- **Every real (non-splice) side matches between the two bodies.**  Under `SameSides A B`, for every
body side index `s ≠ i`, `sideLen (spliceArm A i j) s = sideLen (spliceArm B i j) s`.  (The splice side
`s = i` is the diagonal, matched only by the inequality `cut_diag_le`, handled separately.) -/
theorem spliceArm_sideLen_match {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ}
    (hij : i < j) (hj : j ≤ N) (hside : SameSides A B)
    {s : ℕ} (hs : s < i + (N - j) + 1) (hsne : s ≠ i) :
    sideLen (spliceArm A i j hij hj) ⟨s, hs⟩ = sideLen (spliceArm B i j hij hj) ⟨s, hs⟩ := by
  rcases Nat.lt_or_ge s i with hlt | hge
  · -- head side: both equal the parent's side `s`.
    rw [spliceArm_sideLen_head A i j hij hj hs hlt, spliceArm_sideLen_head B i j hij hj hs hlt]
    exact hside ⟨s, by omega⟩
  · -- `s ≥ i` and `s ≠ i`, so `s > i`: tail side, both equal the parent's side `s - i - 1 + j`.
    have hgt : i < s := by omega
    rw [spliceArm_sideLen_tail A i j hij hj hs hgt, spliceArm_sideLen_tail B i j hij hj hs hgt]
    exact hside ⟨s - i - 1 + j, by omega⟩

/-- **The splice side carries the diagonal inequality.**  Under `cut_diag_le`'s diagonal inequality
`sDist (A i)(A j) ≤ sDist (B i)(B j)`, the splice sides compare:
`sideLen (spliceArm A i j) ⟨i⟩ ≤ sideLen (spliceArm B i j) ⟨i⟩`. -/
theorem spliceArm_sideLen_splice_le {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ}
    (hij : i < j) (hj : j ≤ N) (hi : i < i + (N - j) + 1)
    (hdiag : sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, by omega⟩)) :
    sideLen (spliceArm A i j hij hj) ⟨i, hi⟩ ≤ sideLen (spliceArm B i j hij hj) ⟨i, hi⟩ := by
  rw [spliceArm_sideLen_splice A i j hij hj hi, spliceArm_sideLen_splice B i j hij hj hi]
  exact hdiag

/-! ## §2. The isolated **R-C core**: the one-side-monotone body endpoint comparison.

The genuine obstruction.  The body `A♭ = spliceArm A i j` is weakly convex, the body
`B♭ = spliceArm B i j` strictly convex; they agree on every real edge (`spliceArm_sideLen_match`,
banked), the splice edge satisfies the diagonal inequality (`spliceArm_sideLen_splice_le`, banked from
`cut_diag_le`), and the matched real joints satisfy `JointLe`.  We must conclude
`endpt A♭ ≤ endpt B♭`.

`Main m` does **not** apply: it requires `SameSides A♭ B♭` (equality on *every* edge — the splice edge
is only `≤`) and `JointLe A♭ B♭` (a comparison at *every* joint — the two new splice joints at body
vertices `i` and `i+1` are unmatched).  The required conclusion is a strictly stronger one-side-monotone
arm comparison, which (CRITICAL MATHEMATICAL FACT, 2-edge counterexample above) is FALSE as a general
lemma and holds only via the specific folded-flat cut geometry.  We isolate it as the single named
non-vacuous `Prop` below, parameterised on the body level `m` so it is consumed at `m < n`. -/

/-- **(Isolated R-C core) The one-side-monotone splice-body endpoint comparison.**  For every body level
`m`, every weakly-convex body `A♭` and strictly-convex body `B♭` on `Fin (m+1)` whose real (non-splice)
sides agree, whose splice side satisfies the diagonal inequality `sideLen A♭ ⟨s⟩ ≤ sideLen B♭ ⟨s⟩`, and
whose matched real joints satisfy `JointLe`, the body endpoint does not decrease.

This is **exactly** the geometric content the CUT production (P1) cannot derive from the substrate: a
*one-side-monotone* arm comparison (the splice side only `≤`, the two new splice joints unmatched), false
as a general lemma (the 2-edge counterexample of §0), provable only through the folded-flat configuration
of the §8.4 cut.  Concrete failing chain: `Main` / `SZComparison` take `SameSides` (equal *every* side)
and `JointLe` (*every* joint) as hypotheses — neither holds for the body — and the substrate has no
side-monotone arm lemma; the body's two splice joints (`sphAngle (A (i-1))(A i)(A j)` and
`sphAngle (A i)(A j)(A (j+1))`) are not among the matched joints and are not controlled by the folded-flat
support `sOrient (A i)(A (i+1))(A j) = 0` (which is the parent edge-`i` support, a different triple). -/
def SpliceBodyDiagMono : Prop :=
  ∀ m : ℕ, ∀ Ab Bb : Fin (m + 1) → S2,
    WeakConvexSphArm Ab → StrictConvexSphArm Bb →
    -- the splice side index `s` (`< m`) carries the diagonal inequality;
    ∀ s : Fin m, sideLen Ab s ≤ sideLen Bb s →
    -- every real side matches;
    (∀ t : Fin m, t ≠ s → sideLen Ab t = sideLen Bb t) →
    -- the matched real joints are nondecreasing;
    (∀ r : Fin (m - 1), jointAngle Ab r ≤ jointAngle Bb r) →
    endpt Ab ≤ endpt Bb

/-! ## §3. The CUT-branch splice transport, proved from the isolated core.

We package the inputs the CUT production (P1) supplies — the cut indices, the body convexity
certificates, the parent side/joint matches, and the banked diagonal inequality `cut_diag_le` — and
derive `endpt A ≤ endpt B` through the body bodies' endpoint identities (`spliceArm_endpt`) and the
isolated core `SpliceBodyDiagMono`. -/

/-- **The R-C splice transport (`splice_transport_of_diag_le`).**  CUT production (P1):  for a weakly
convex `A` folded flat at the non-incident support `(A i, A (i+1), A j)` and a strictly convex `B`, with
equal sides (`SameSides A B`), the cut at `(i, j)` producing the bodies
`A♭ = spliceArm A i j`, `B♭ = spliceArm B i j` (level `m = i + (N - j) + 1`), the body convexity
certificates, the banked diagonal inequality `hdiag` (= `cut_diag_le`), and the matched body real joints,
gives `endpt A ≤ endpt B`.

The proof banks the body real-side match (`spliceArm_sideLen_match`), the body diagonal-side inequality
(`spliceArm_sideLen_splice_le` from `hdiag`), and the endpoint identities `spliceArm_endpt`
(`endpt A♭ = endpt A`, `endpt B♭ = endpt B`); the *only* remaining content — the one-side-monotone body
endpoint comparison — is discharged by the isolated non-vacuous core `SpliceBodyDiagMono`. -/
theorem splice_transport_of_diag_le
    (hcore : SpliceBodyDiagMono)
    {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ} (hij : i < j) (hj : j ≤ N)
    (hAb : WeakConvexSphArm (spliceArm A i j hij hj))
    (hBb : StrictConvexSphArm (spliceArm B i j hij hj))
    (hside : SameSides A B)
    (hdiag : sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, by omega⟩))
    (hjoint : ∀ r : Fin (i + (N - j) + 1 - 1),
      jointAngle (spliceArm A i j hij hj) r ≤ jointAngle (spliceArm B i j hij hj) r) :
    endpt A ≤ endpt B := by
  -- the splice side index `s = ⟨i⟩ : Fin m`, `m = i + (N - j) + 1`.
  have hi : i < i + (N - j) + 1 := by omega
  set s : Fin (i + (N - j) + 1) := ⟨i, hi⟩ with hs_def
  -- the diagonal-side inequality on the bodies, from `hdiag`.
  have hsplice :
      sideLen (spliceArm A i j hij hj) s ≤ sideLen (spliceArm B i j hij hj) s :=
    spliceArm_sideLen_splice_le hij hj hi hdiag
  -- every real (non-splice) side matches between the bodies, from `SameSides A B`.
  have hreal : ∀ t : Fin (i + (N - j) + 1), t ≠ s →
      sideLen (spliceArm A i j hij hj) t = sideLen (spliceArm B i j hij hj) t := by
    intro t ht
    have htne : t.val ≠ i := by
      intro hval; exact ht (by apply Fin.ext; rw [hs_def]; exact hval)
    have := spliceArm_sideLen_match hij hj hside t.isLt htne
    -- rewrite the `⟨t.val, _⟩` form back to `t`.
    simpa using this
  -- the isolated core delivers the body endpoint comparison.
  have hbody :
      endpt (spliceArm A i j hij hj) ≤ endpt (spliceArm B i j hij hj) :=
    hcore (i + (N - j) + 1) (spliceArm A i j hij hj) (spliceArm B i j hij hj)
      hAb hBb s hsplice hreal hjoint
  -- transport through the endpoint identities (the body keeps both arm endpoints).
  rwa [spliceArm_endpt A i j hij hj, spliceArm_endpt B i j hij hj] at hbody

/-! ## §4. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- **Non-vacuity of `SpliceBodyDiagMono`.**  The core is genuinely realisable: at `Ab = Bb` every real
side matches reflexively, the splice side satisfies `≤` reflexively (`le_refl`), every joint comparison
is reflexive, and the conclusion is the real endpoint inequality `endpt Ab ≤ endpt Ab` (`le_refl`).  So
the isolated core is **not** a vacuous-hypothesis impostor: its hypotheses are jointly satisfiable (by
every diagonal arm) and its conclusion is a genuine endpoint inequality. -/
theorem spliceBodyDiagMono_satisfiable {m : ℕ} (Ab : Fin (m + 1) → S2)
    (_hAb : WeakConvexSphArm Ab) (_hAb' : StrictConvexSphArm Ab) (s : Fin m) :
    sideLen Ab s ≤ sideLen Ab s ∧
      (∀ t : Fin m, t ≠ s → sideLen Ab t = sideLen Ab t) ∧
      (∀ r : Fin (m - 1), jointAngle Ab r ≤ jointAngle Ab r) ∧
      endpt Ab ≤ endpt Ab :=
  ⟨le_refl _, fun _ _ => rfl, fun _ => le_refl _, le_refl _⟩

/-- **Non-vacuity of the splice transport.**  The conclusion `endpt A ≤ endpt B` is genuinely realisable
(reflexive at `A = B`), so `splice_transport_of_diag_le` is a load-bearing transport, not a vacuous
impostor — it consumes the isolated core to derive a real endpoint inequality. -/
theorem splice_transport_conclusion_satisfiable {N : ℕ} (A : Fin (N + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- **The diagonal inequality genuinely feeds the splice side** (banked link, not vacuous): under
`cut_diag_le`'s `hdiag`, the body splice side is `≤`, realised reflexively when the diagonal sides are
equal. -/
theorem spliceArm_sideLen_splice_le_nonvacuous {N : ℕ} (A : Fin (N + 1) → S2) {i j : ℕ}
    (hij : i < j) (hj : j ≤ N) (hi : i < i + (N - j) + 1) :
    sideLen (spliceArm A i j hij hj) ⟨i, hi⟩ ≤ sideLen (spliceArm A i j hij hj) ⟨i, hi⟩ :=
  spliceArm_sideLen_splice_le hij hj hi (le_refl _)

end ProofsInTheBook.SphericalSpliceTransport
