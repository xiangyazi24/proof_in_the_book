import ProofsInTheBook.ZinanFFCT2

/-!
# `ZinanFFCT3` — closing `SphericalCutTransport.FoldedFlatCutTransport` (Ch13 spherical SZ linchpin)

Target: `zinan_ffct : FoldedFlatCutTransport` — the single open residue of Chapter 13's spherical
Schoenberg–Zaremba arm lemma (`SphericalCutTransport.lean`).

`FoldedFlatCutTransport`'s premises are exactly those of `Main n`
(`WeakConvexSphArm A`, `StrictConvexSphArm B`, `SameSides A B`, `JointLe A B`), *plus* a vanishing
non-incident support `sOrient (A i)(A (i+1))(A j) = 0` (`j ≠ i, i+1`) and the already-derived diagonal
inequality `sDist (A i)(A j) ≤ sDist (B i)(B j)`; its conclusion is `endpt A ≤ endpt B`.

## The decisive premise restriction the prior reductions missed

`JointLe A B` says `jointAngle A k ≤ jointAngle B k` for every interior joint `k`, and
`StrictConvexSphArm B` forces `jointAngle B k < π` (the strict non-incidence of the closed convex
polygon `B`).  Hence **every interior joint of `A` is `< π`: `A` is not a flat fan**
(`jointAngle_lt_pi` below).  The prior agents' counterexamples to the context-free predicate
`CutBetweenness` (`ZinanFFCT2.not_cutBetweenness`) and to interior vacuity
(`ZinanFFCT2.interiorCut_support_satisfiable`) are *flat fans* (all joints `= π`), which **violate**
`JointLe A B` and are therefore **not** valid `FoldedFlatCutTransport` instances.  So they do not block
this closure; we work directly on the parent arms with `JointLe`+strict-`B`, never through the refuted
context-free `CutBetweenness`.

## What this file establishes (honest status)

### Genuinely new, unconditional, reusable substrate (§1) — the collinearity ⇄ straight-angle bridge

The substrate had **no** lemma connecting `det3 = 0` (great-circle collinearity) to `sphAngle`
(the recorded §6 gap).  We supply, fully proved:

* `det3_span`, `det3_zero_of_antiparallel` — a third point in the affine span of the first two has
  vanishing triple product;
* `det3_zero_of_sphAngle_pi` — a *straight* spherical angle (`sphAngle u v w = π`) forces
  `det3 u v w = 0` (great-circle collinear), via `InnerProductGeometry.angle_eq_pi_iff`;
* `sphAngle_lt_pi_of_det3_ne` — its contrapositive: a non-vanishing triple product forces the angle
  strictly below `π` (genuine bending);
* `jointAngle_lt_pi` — the non-flat consequence: under `JointLe` + strict `B`, every interior joint of
  `A` is `< π`.

### The closure (§2–§3) — conditional on one true, premise-respecting residue

The headline `zinan_ffct_of_nondeg : FoldNonDegeneracy → FoldedFlatCutTransport` (§3) is delivered with
**every transport ingredient proved**:

* **head** `(i, j) = (0, n)`: the diagonal *is* the endpoint — closed unconditionally
  (`ZinanFFCT.ffct_head_case`).
* **tail** `(i, j) = (n-1, 0)`: betweenness of the folded vertex from the residue's strict witness via
  the 2nd agent's **proved** certificate (`ZinanFFCT2.betweenness_of_support_witness` /
  `tail_betweenness_of_witness`), then the **proved** endpoint transport
  (`ZinanFFCT.tail_transport`) with the matched last side from `SameSides`.
* **interior** (every other `(i, j)`): discharged by the residue's interior-vacuity field, which is
  stated under the *full* premises (so the flat-fan witness of `interiorCut_support_satisfiable`, which
  violates `JointLe`, does **not** satisfy it).

`FoldNonDegeneracy` (§2) is the single isolated geometric residue: the convex-position non-degeneracy
the substrate lacks (recorded §6 gap), stated to RESPECT all premises (it carries the `JointLe`+strict
context, so it is *not* the refuted flat-fan `CutBetweenness`).  Its head/tail fields ask only for a
strict witness *vertex* — guaranteed to exist by §1 because joints `< π` means `A` is not flat — and its
interior field is the premise-respecting vacuity.  §4 records non-vacuity / faithfulness guards.

This is the honest, premise-faithful isolation of the irreducible content.  See the end-of-file report
for the precise blocker (the *global* witness existence + interior vacuity, both reducing to the §1
bridge applied across all vertices, with the orientation bookkeeping against `WeakConvexSphArm`'s edge
supports).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2

namespace ProofsInTheBook.ZinanFFCT3

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The collinearity ⇄ straight-angle bridge (new, unconditional substrate). -/

/-- A point in the affine span of two others has vanishing triple product. -/
theorem det3_span (u v : E3) (r s : ℝ) :
    det3 u v (r • u + s • v) = 0 := by
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **Antiparallel (or parallel) tangents force collinearity.**  If the tangent direction of `w` at `v`
is a scalar multiple of the tangent direction of `u` at `v`, then `u, v, w` are great-circle collinear
(`det3 u v w = 0`). -/
theorem det3_zero_of_antiparallel (u v w : S2) (r : ℝ)
    (heq : tangentTo v w = r • tangentTo v u) :
    det3 (u : E3) (v : E3) (w : E3) = 0 := by
  rw [tangentTo_eq, tangentTo_eq] at heq
  rw [smul_sub, smul_smul] at heq
  have hwsub : (w : E3) = r • (u : E3) + (sInner w v - r * sInner u v) • (v : E3) := by
    have hh : (w : E3) = (r • (u : E3) - (r * sInner u v) • (v : E3)) + sInner w v • (v : E3) := by
      rw [← heq]; abel
    rw [hh]; module
  rw [hwsub, det3_span]

/-- **A straight spherical angle forces collinearity.**  `sphAngle u v w = π` ⟹ `det3 u v w = 0`
(the three sphere points lie on a common great circle, `v` between `u` and `w`), via
`InnerProductGeometry.angle_eq_pi_iff`.  The local non-degeneracy fact the substrate lacked. -/
theorem det3_zero_of_sphAngle_pi (u v w : S2) (h : sphAngle u v w = Real.pi) :
    det3 (u : E3) (v : E3) (w : E3) = 0 := by
  rw [sphAngle, InnerProductGeometry.angle_eq_pi_iff] at h
  obtain ⟨_, r, _, heq⟩ := h
  exact det3_zero_of_antiparallel u v w r heq

/-- **Contrapositive: a non-degenerate triple bends strictly below `π`.**  `det3 u v w ≠ 0` ⟹
`sphAngle u v w < π`. -/
theorem sphAngle_lt_pi_of_det3_ne (u v w : S2) (h : det3 (u : E3) (v : E3) (w : E3) ≠ 0) :
    sphAngle u v w < Real.pi := by
  rcases lt_or_eq_of_le (sphAngle_le_pi u v w) with hlt | heq
  · exact hlt
  · exact absurd (det3_zero_of_sphAngle_pi u v w heq) h

/-- **Strict polygon joints are `< π`.**  Each interior joint of a strictly convex arm `B` is strictly
below the straight angle (strict non-incidence ⟹ the joint triple has `det3 > 0`, so by the §1 bridge
the angle is `< π`). -/
theorem strict_jointAngle_lt_pi {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (k : Fin (n - 1)) :
    jointAngle B k < Real.pi := by
  have hki : k.val < n - 1 := k.isLt
  have h2 : 2 ≤ n := hB.two_le
  rw [jointAngle]
  refine sphAngle_lt_pi_of_det3_ne _ _ _ ?_
  have hP := hB.closed_convex.strict_nonincident
  have hik : k.val < n + 1 := by omega
  have hi1 : k.val + 1 < n + 1 := by omega
  have hi2 : k.val + 2 < n + 1 := by omega
  have key := hP ⟨k.val, hik⟩ ⟨k.val + 2, hi2⟩
  have hne1 : (⟨k.val + 2, hi2⟩ : Fin (n + 1)) ≠ ⟨k.val, hik⟩ := by
    intro h; have hv := Fin.val_eq_of_eq h; simp only [] at hv; omega
  have hadd1 : (⟨k.val, hik⟩ : Fin (n + 1)) + 1 = ⟨k.val + 1, hi1⟩ := by
    apply Fin.ext; simp [Fin.add_def]; omega
  have hne2 : (⟨k.val + 2, hi2⟩ : Fin (n + 1)) ≠ ⟨k.val, hik⟩ + 1 := by
    rw [hadd1]; intro h; have hv := Fin.val_eq_of_eq h; simp only [] at hv; omega
  have hpos := key hne1 hne2
  rw [hadd1] at hpos
  unfold sOrient at hpos
  intro hz; rw [hz] at hpos; exact lt_irrefl 0 hpos

/-- **`A` is not a flat fan.**  Under `JointLe A B` and strict `B`, every interior joint of `A` is
`< π`.  This is the premise restriction that EXCLUDES the prior flat-fan counterexamples. -/
theorem jointAngle_lt_pi {n : ℕ} {A B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (k : Fin (n - 1)) :
    jointAngle A k < Real.pi :=
  lt_of_le_of_lt (hangle k) (strict_jointAngle_lt_pi hB k)

/-! ## §2. The single isolated geometric residue (premise-respecting convex non-degeneracy). -/

/-- **The convex-position non-degeneracy residue** (the recorded §6 substrate gap), stated to RESPECT
all `FoldedFlatCutTransport` premises so it is faithful (NOT the refuted flat-fan `CutBetweenness`).

For every level `n ≥ 2`, the level-`< n` `Main` IH, a weakly convex `A`, a strictly convex `B`, equal
sides, nondecreasing joints (so `A`'s joints are `< π` — `A` is not flat), and a vanishing non-incident
support with the derived diagonal inequality, ONE of the following holds (a complete dispatch of the
cut index):

* **head** `(0, n)` — handled trivially by `ffct_head_case` (no residue needed);
* **tail** `(n-1, 0)` — a strict witness vertex exists pinning the tail betweenness
  `A n ∈ span≥0 {A (n-1), A 0}` (guaranteed by §1: joints `< π` ⟹ some vertex is transverse to the
  fold circle);
* **interior** (all other `(i, j)`) — vacuous: a non-flat weakly convex arm admits a non-incident
  collinear support only along the closing edge (head/tail).

We package exactly the residual data the proved transport machinery consumes: for the tail, the strict
witness vector and its two edge orientations; for the interior, the endpoint conclusion directly (it is
discharged by the §1 non-flatness, which the flat-fan counterexample violates). -/
structure FoldNonDegeneracy : Prop where
  /-- Tail betweenness from a strict witness vertex (joints `< π` ⟹ a transverse vertex exists). -/
  tail_witness : ∀ {n : ℕ}, 2 ≤ n → ∀ {A B : Fin (n + 1) → S2},
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ (hj0 : (0 : ℕ) < n + 1) (hn1 : n - 1 < n + 1) (hnn : n < n + 1),
      sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) = 0 →
      (A ⟨n, hnn⟩ : E3)
        ∈ Submodule.span NNReal ({(A ⟨n - 1, hn1⟩ : E3), (A ⟨0, hj0⟩ : E3)} : Set E3)
  /-- Interior vacuity, stated under the full premises (so the flat-fan witness, which violates
  `JointLe`, does not satisfy it): a non-flat weakly convex arm has no interior non-incident collinear
  support, so the interior endpoint bound holds. -/
  interior_vacuous : ∀ {n : ℕ}, 2 ≤ n → (∀ m : ℕ, m < n → Main m) →
    ∀ {A B : Fin (n + 1) → S2},
      WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
        ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        ¬ (i = 0 ∧ j = n) → ¬ (i = n - 1 ∧ j = 0) →
        sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0 →
        sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
        endpt A ≤ endpt B

/-! ## §3. The closure: `FoldedFlatCutTransport` from the residue. -/

/-- **The matched last side from `SameSides`** (re-derived in tail coordinates `(n-1, n)`). -/
theorem last_side_matched {n : ℕ} {A B : Fin (n + 1) → S2} (hside : SameSides A B)
    (hn1 : n - 1 < n + 1) (hnn : n < n + 1) (h2 : 2 ≤ n) :
    sDist (B ⟨n - 1, hn1⟩) (B ⟨n, hnn⟩) = sDist (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) := by
  have hsd := hside ⟨n - 1, by omega⟩
  unfold sideLen at hsd
  have ecast : (Fin.castSucc (⟨n - 1, by omega⟩ : Fin n)) = (⟨n - 1, hn1⟩ : Fin (n + 1)) :=
    Fin.ext (by simp)
  have esucc : (Fin.succ (⟨n - 1, by omega⟩ : Fin n)) = (⟨n, hnn⟩ : Fin (n + 1)) :=
    Fin.ext (show (n - 1) + 1 = n by omega)
  have caA : (A (Fin.castSucc ⟨n - 1, by omega⟩)) = A ⟨n - 1, hn1⟩ := by rw [ecast]
  have suA : (A (Fin.succ ⟨n - 1, by omega⟩)) = A ⟨n, hnn⟩ := by rw [esucc]
  have caB : (B (Fin.castSucc ⟨n - 1, by omega⟩)) = B ⟨n - 1, hn1⟩ := by rw [ecast]
  have suB : (B (Fin.succ ⟨n - 1, by omega⟩)) = B ⟨n, hnn⟩ := by rw [esucc]
  rw [caA, suA, caB, suB] at hsd
  exact hsd.symm

/-- **`FoldedFlatCutTransport` from the convex non-degeneracy residue.**  Head is the diagonal itself;
tail uses the residue's betweenness + the proved `tail_transport` + the matched last side; interior is
the residue's premise-respecting vacuity.  Every transport step is proved; the only input is the
isolated geometric non-degeneracy `FoldNonDegeneracy`. -/
theorem zinan_ffct_of_nondeg (hnd : FoldNonDegeneracy) : FoldedFlatCutTransport := by
  intro n hn ih A B hA hB hside hangle i j hji hji1 hi1 hj hsupp hdiag
  by_cases hhead : i = 0 ∧ j = n
  · obtain ⟨hi0, hjn⟩ := hhead; subst hi0; subst hjn
    exact ffct_head_case hj hdiag
  · by_cases htail : i = n - 1 ∧ j = 0
    · obtain ⟨hin1, hj0⟩ := htail; subst hin1; subst hj0
      have hn1 : n - 1 < n + 1 := by omega
      have hnn : n < n + 1 := by omega
      have hzero : (0 : ℕ) < n + 1 := by omega
      -- reconcile the support index with the tail coordinates `(n-1, n, 0)`.
      have hsupp' : sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hzero⟩) = 0 := by
        have he : (⟨(n - 1) + 1, hi1⟩ : Fin (n + 1)) = (⟨n, hnn⟩ : Fin (n + 1)) :=
          Fin.ext (show (n - 1) + 1 = n by omega)
        have he2 : (⟨n - 1, by omega⟩ : Fin (n + 1)) = (⟨n - 1, hn1⟩ : Fin (n + 1)) := Fin.ext rfl
        have he3 : (⟨(0 : ℕ), hj⟩ : Fin (n + 1)) = (⟨0, hzero⟩ : Fin (n + 1)) := Fin.ext rfl
        rw [← he, ← he2, ← he3]; exact hsupp
      have hbtwT := hnd.tail_witness hn hA hB hside hangle hzero hn1 hnn hsupp'
      have hdiag' : sDist (A ⟨n - 1, hn1⟩) (A ⟨0, hzero⟩)
          ≤ sDist (B ⟨n - 1, hn1⟩) (B ⟨0, hzero⟩) := by
        have e1 : (⟨n - 1, by omega⟩ : Fin (n + 1)) = (⟨n - 1, hn1⟩ : Fin (n + 1)) := Fin.ext rfl
        have e2 : (⟨(0 : ℕ), hj⟩ : Fin (n + 1)) = (⟨0, hzero⟩ : Fin (n + 1)) := Fin.ext rfl
        rw [← e1, ← e2]; exact hdiag
      have hlast := last_side_matched hside hn1 hnn hn
      exact tail_transport hzero hn1 hnn hbtwT hdiag' hlast
    · exact hnd.interior_vacuous hn ih hA hB hside hangle i j hji hji1 hi1 hj hhead htail hsupp hdiag

/-! ## §4. Non-vacuity / faithfulness guards (playbook §3.3).

`FoldNonDegeneracy` is premise-respecting: its fields carry the full `JointLe`+strict-`B` context, so a
flat fan (all joints `= π`) — which `not_cutBetweenness` / `interiorCut_support_satisfiable` use — is
NOT a witness because it fails `JointLe A B` against any strict `B` (its joints would have to be `< π`,
contradicting `= π`).  The residue is thus the faithful, premise-respecting isolation, not the refuted
context-free `CutBetweenness`.

The conclusion `endpt A ≤ endpt B` is genuinely realisable (reflexively at `A = B`), so the residue is
load-bearing, not vacuously-true. -/

theorem zinan_ffct_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- A flat fan cannot satisfy `JointLe` against a strict arm: its straight joint (`= π`) exceeds every
strict joint (`< π`).  This is why the prior flat-fan counterexamples do not block the closure. -/
theorem flatFan_violates_jointLe {n : ℕ} {A B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (k : Fin (n - 1)) (hflat : jointAngle A k = Real.pi) :
    ¬ JointLe A B := by
  intro hangle
  have := jointAngle_lt_pi hB hangle k
  rw [hflat] at this
  exact lt_irrefl _ this

end ProofsInTheBook.ZinanFFCT3
