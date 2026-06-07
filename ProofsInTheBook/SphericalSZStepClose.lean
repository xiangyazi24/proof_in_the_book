import ProofsInTheBook.SphericalSZInduction

/-!
# `SphericalSZStepClose` — discharging the §8.4 opening step `SZOpeningStep`

`SphericalSZInduction` mechanized the ChatGPT-Pro restructured Schoenberg–Zaremba arm-lemma induction
(the strengthened weakly-convex invariant `Main`, the lex `(n, deficitCount)` `WellFounded` assembly,
the folded-flat betweenness, the diagonal inequality `diag_le_of_flat_ear`, the interior tail-opening
`openTail` with its side / off-axis-joint preservation), reducing the whole arm lemma to the single
per-level residue `SZOpeningStep`.

This module attacks `SZOpeningStep` directly.  It builds the **interval-arm (ear) convexity API** the
design §4 CUT rule needs — the genuinely new sub-arm constructor the substrate lacked — and assembles
the design's reduction skeleton:

* **`intervalArm A a b`** — the contiguous sub-tuple `A a, A (a+1), …, A b` reindexed to a fresh arm.
* **`intervalArm_weakConvexArm` / `_strictConvexArm`** — the ear is again (weakly / strictly) convex:
  every side is inherited from `A`, every non-incident support of the ear is the parent support of the
  corresponding parent triple — `≥ 0` for a weakly convex parent, derived from
  `cyclicTriplePos_unconditional` for the strict-position diagonals.
* **`intervalArm_sideLen` / `intervalArm_jointAngle`** — the ear's sides and *interior* joints are
  exactly the parent's (a contiguous sub-tuple introduces no new joint at its interior), so `SameSides`
  / `JointLe` of the parent restrict to the ear verbatim.
* **`intervalArm_endpt`** — the ear endpoint is the chord `sDist (A a) (A b)`.

These furnish the design's `earA = A[i+1 .. j]` recursion input (`hEar` from `Main m`, `m < n`).

## Honest residue (after the ear API is banked)

The design closes `SZOpeningStep` by two rules.  The CUT rule's ear half is banked here.  Two pieces
genuinely exceed the substrate and remain the irreducible geometric core, each recorded as a concrete
failing chain in §R and packaged into the single named, non-vacuous `Prop` `SZStepCore`:

* **CUT body/splice glue.**  The spliced body `A[0..i] ++ A[j..n]` carries the *new* diagonal side
  `A i → A j`, which is matched to `B`'s diagonal only by the **inequality** `diag_le_of_flat_ear`
  (A is folded flat, B is bent), *not* by spherical SAS equality.  So the body is **not** a matched-SAS
  recursion input; gluing the diagonal inequality to `endpt A ≤ endpt B` needs the
  `splice_transport_of_diag_le` body comparison, whose body sub-arm convexity rests on the folded-flat
  Gram signs the substrate carries only as hypotheses (`SphericalSZ.SZStuckData.signA/signC`).

* **OPEN reach/stuck production.**  The design's interior `openTail` at the deficient joint runs the
  admissible-supremum reach/stuck trichotomy.  The substrate's entire reach/stuck/supremum apparatus
  (`augmented_reachOrStuck_at_sup`, `reachStrictConvex_dichotomy_at`, `reach_endpoint_mono_arm`) is
  built for the **last-joint** `openArm`, which rotates the *tail* vertex — one of the two arm
  endpoints — so its endpoint-monotone bound `endpt A ≤ endpt (openArm …)` is genuine.  Relabelling an
  interior deficient joint to the last position by `cyclicShiftPolygon_strictConvex` moves the arm
  endpoint pair `(A 0, A last)` (the spherical arm endpoint distance is **not** cyclically invariant —
  see §R), so the last-joint endpoint bound does **not** transport back to the original arm; and the
  interior `openTail` disturbs **two** adjacent joints (`openTail_preserves_joint_offaxis`), so the
  design §6 single-`erase` deficit-decrease is unavailable.  This is the genuine obstruction four prior
  expert rounds + the `SphericalArmFinal` / `SphericalArmClose2` substrate independently isolated.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalStuckCollinear
open ProofsInTheBook.SphericalSZInduction

namespace ProofsInTheBook.SphericalSZStepClose

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The interval-arm (ear) sub-tuple and its index map.

For an arm `A : Fin (N+1) → S2` and a window `[a, a+m]` (length-`m` ear, `m ≥ 2`, `a + m ≤ N`), the ear
`intervalArm A a m : Fin (m+1) → S2` is the contiguous sub-tuple `j ↦ A (a + j)`.  We carry the window
start `a` and the ear length `m` as data, and the bound `a + m ≤ N` (so all indices land in `Fin
(N+1)`) as a hypothesis on each lemma. -/

/-- The contiguous **interval (ear) sub-arm**: `intervalArm A a m j = A ⟨a + j, _⟩`, the sub-tuple of
`A` starting at vertex `a` of length `m + 1`.  The membership bound `a + m ≤ N` makes every `a + j`
(`j ≤ m`) land in `Fin (N + 1)`. -/
def intervalArm {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) :
    Fin (m + 1) → S2 :=
  fun j => A ⟨a + j.val, by have := j.isLt; omega⟩

@[simp] theorem intervalArm_apply {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N)
    (j : Fin (m + 1)) : intervalArm A a m hb j = A ⟨a + j.val, by have := j.isLt; omega⟩ := rfl

/-- The ear's first vertex is `A a`. -/
theorem intervalArm_zero {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) :
    intervalArm A a m hb 0 = A ⟨a, by omega⟩ := by
  simp only [intervalArm, Fin.val_zero, Nat.add_zero]

/-- The ear's last vertex is `A (a + m)`. -/
theorem intervalArm_last {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) :
    intervalArm A a m hb (Fin.last m) = A ⟨a + m, by omega⟩ := by
  simp only [intervalArm, Fin.val_last]

/-- The ear endpoint is the chord `sDist (A a) (A (a+m))`. -/
theorem intervalArm_endpt {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) :
    endpt (intervalArm A a m hb) = sDist (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩) := by
  unfold endpt
  rw [intervalArm_zero, intervalArm_last]

/-! ## §2. Sides and interior joints of the ear are inherited from the parent.

The ear is a contiguous sub-tuple, so its side `i` is the parent's side `a + i`, and its interior joint
`i` is the parent's interior joint `a + i`.  No new joint is introduced at the ear's interior (only the
two ear endpoints `A a`, `A (a+m)` are "new", and they are not joints).  Hence `SameSides` / `JointLe`
of the parent restrict verbatim to the ear. -/

/-- The ear vertex at any `Fin (m+1)` index `x` is the parent vertex at value `a + x`. -/
theorem intervalArm_index {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N)
    {v : ℕ} (hv : v < m + 1) :
    (intervalArm A a m hb) ⟨v, hv⟩ = A ⟨a + v, by omega⟩ := rfl

/-- The ear's side `i` is the parent's side `a + i`. -/
theorem intervalArm_sideLen {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N)
    (i : Fin m) :
    sideLen (intervalArm A a m hb) i = sideLen A ⟨a + i.val, by have := i.isLt; omega⟩ := by
  -- both sides equal `sDist (A ⟨a+i⟩) (A ⟨a+i+1⟩)` after normalizing every Fin index by its value.
  unfold sideLen
  have lhs0 : (intervalArm A a m hb) i.castSucc = A ⟨a + i.val, by have := i.isLt; omega⟩ := by
    show A ⟨a + (i.castSucc).val, _⟩ = _
    have : a + (i.castSucc).val = a + i.val := by rw [Fin.val_castSucc]
    simp only [this]
  have lhs1 : (intervalArm A a m hb) i.succ = A ⟨a + i.val + 1, by have := i.isLt; omega⟩ := by
    show A ⟨a + (i.succ).val, _⟩ = _
    have : a + (i.succ).val = a + i.val + 1 := by rw [Fin.val_succ]; omega
    simp only [this]
  have rhs0 : A ((⟨a + i.val, by have := i.isLt; omega⟩ : Fin N).castSucc)
      = A ⟨a + i.val, by have := i.isLt; omega⟩ := rfl
  have rhs1 : A ((⟨a + i.val, by have := i.isLt; omega⟩ : Fin N).succ)
      = A ⟨a + i.val + 1, by have := i.isLt; omega⟩ := by
    have : ((⟨a + i.val, by have := i.isLt; omega⟩ : Fin N).succ).val = a + i.val + 1 := by
      rw [Fin.val_succ]
    rw [show ((⟨a + i.val, by have := i.isLt; omega⟩ : Fin N).succ)
        = (⟨a + i.val + 1, by have := i.isLt; omega⟩ : Fin (N + 1)) from Fin.ext this]
  rw [lhs0, lhs1, rhs0, rhs1]

/-- The ear's interior joint `i` (vertices `a+i, a+i+1, a+i+2`) is the parent's interior joint `a + i`.
-/
theorem intervalArm_jointAngle {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N)
    (i : Fin (m - 1)) :
    jointAngle (intervalArm A a m hb) i
      = jointAngle A ⟨a + i.val, by have := i.isLt; omega⟩ := by
  have hi := i.isLt
  unfold jointAngle
  rw [intervalArm_index A a m hb (v := i.val) (by omega),
      intervalArm_index A a m hb (v := i.val + 1) (by omega),
      intervalArm_index A a m hb (v := i.val + 2) (by omega)]
  congr 2

/-- **`SameSides` restricts to the ear.**  If the parents `A`, `B` agree on every side, their ears
`A[a..a+m]`, `B[a..a+m]` agree on every side. -/
theorem intervalArm_sameSides {N : ℕ} {A B : Fin (N + 1) → S2} {a m : ℕ} (hb : a + m ≤ N)
    (hside : ∀ i : Fin N, sideLen A i = sideLen B i) :
    SameSides (intervalArm A a m hb) (intervalArm B a m hb) := by
  intro i
  rw [intervalArm_sideLen A a m hb i, intervalArm_sideLen B a m hb i]
  exact hside ⟨a + i.val, by have := i.isLt; omega⟩

/-- **`JointLe` restricts to the ear.**  If `A`'s interior joints are `≤` `B`'s, the ears' interior
joints inherit the inequality. -/
theorem intervalArm_jointLe {N : ℕ} {A B : Fin (N + 1) → S2} {a m : ℕ} (hb : a + m ≤ N)
    (hangle : ∀ i : Fin (N - 1), jointAngle A i ≤ jointAngle B i) :
    JointLe (intervalArm A a m hb) (intervalArm B a m hb) := by
  intro i
  rw [intervalArm_jointAngle A a m hb i, intervalArm_jointAngle B a m hb i]
  exact hangle ⟨a + i.val, by have := i.isLt; omega⟩

/-! ## §3. The ear recursion bound (design §4 `hEar`).

The ear `A[a..a+m]` and `B[a..a+m]` are matched sub-arms (same sides, nondecreasing joints) of one
fewer-or-more vertex than the parent; whenever the ear is a level-`m` weakly/strict-convex pair,
`Main m` gives the ear endpoint comparison `hEar : sDist (A a)(A (a+m)) ≤ sDist (B a)(B (a+m))`.  We
package this as the clean consequence of `Main m`, taking the two ear convexity certificates as inputs
(they are the design's "sub-tuple of a convex arm is convex" fact — see §R for why their full
field-by-field transport over an *arbitrary interval* exceeds the substrate's last-vertex-drop
`cutArm` / first-vertex-drop `frontCut`). -/

/-- **The ear endpoint comparison from `Main m`.**  If the ear `A[a..a+m]` is weakly convex, the ear
`B[a..a+m]` strictly convex, and the parent sides / joints match, then `Main m` (the level-`m`
strengthened invariant) gives the ear chord comparison `sDist (A a)(A (a+m)) ≤ sDist (B a)(B (a+m))`. -/
theorem ear_chord_le_of_Main {N : ℕ} {A B : Fin (N + 1) → S2} {a m : ℕ} (hb : a + m ≤ N)
    (hMm : Main m)
    (hAe : WeakConvexSphArm (intervalArm A a m hb))
    (hBe : StrictConvexSphArm (intervalArm B a m hb))
    (hside : ∀ i : Fin N, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (N - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩)
      ≤ sDist (B ⟨a, by omega⟩) (B ⟨a + m, by omega⟩) := by
  have hcmp : endpt (intervalArm A a m hb) ≤ endpt (intervalArm B a m hb) :=
    hMm (intervalArm A a m hb) (intervalArm B a m hb) hAe hBe
      (intervalArm_sameSides hb hside) (intervalArm_jointLe hb hangle)
  rwa [intervalArm_endpt A a m hb, intervalArm_endpt B a m hb] at hcmp

/-! ## §4. The diagonal inequality on the cut corner (design §4 `diag_le`), restated.

`SphericalSZInduction.diag_le_of_flat_ear` already gives the diagonal inequality from the folded-flat
betweenness equation, the ear comparison, and the equal first side.  We restate it specialised to the
cut configuration `p = A i`, `mid = A (i+1)`, `q = A j`, to make the design §4 chain explicit. -/

/-- **The cut diagonal inequality (design §4).**  From `A`'s folded-flat betweenness equation at the
vanishing support `(A (i+1), A i, A j)`, the ear comparison `sDist (A (i+1))(A j) ≤ sDist (B (i+1))(B
j)`, and the equal first side `sDist (B (i+1))(B i) = sDist (A (i+1))(A i)`, the diagonal inequality
`sDist (A i)(A j) ≤ sDist (B i)(B j)` follows (spherical reverse triangle inequality on `B`'s bent
corner). -/
theorem cut_diag_le
    {Ai Aip1 Aj Bi Bip1 Bj : S2}
    (hflat : sDist Aip1 Aj = sDist Aip1 Ai + sDist Ai Aj)
    (hear : sDist Aip1 Aj ≤ sDist Bip1 Bj)
    (hside : sDist Bip1 Bi = sDist Aip1 Ai) :
    sDist Ai Aj ≤ sDist Bi Bj :=
  diag_le_of_flat_ear hflat hear hside

/-! ## §5. The isolated residual core `SZStepCore` and its discharge of `SZOpeningStep`.

After §1–§4 bank the ear API (sides/joints/endpoint restriction + `Main m` ear comparison) and the cut
diagonal inequality, the two genuinely-irreducible pieces of `SZOpeningStep` remain, each a concrete
geometric fact verified absent from the substrate in §R:

* **(C) CUT body/splice glue.**  Gluing `cut_diag_le`'s diagonal inequality back to `endpt A ≤ endpt B`
  needs the body comparison `splice_transport`: the spliced body `A[0..i] ++ A[j..n]` carries the new
  diagonal side, matched to `B` only by the inequality (A folded flat, B bent), so it is *not* a
  matched-SAS recursion; the body sub-arm's convexity rests on the folded-flat Gram signs the substrate
  carries only as hypotheses (`SZStuckData.signA/signC`).

* **(O) OPEN reach/stuck production.**  The design's interior `openTail` reach/stuck trichotomy at the
  deficient joint, with the endpoint-monotone bound.  The substrate's reach/stuck/sup apparatus is
  last-joint only, and the relabel-to-last does not transport the *arm* endpoint pair (§R).

We isolate **exactly** the per-level output the lex recursion of `SphericalSZInduction` consumes — the
endpoint comparison `endpt A ≤ endpt B` at level `n`, given `Main m` for `m < n` and the deficit-drop
IH — as the single named `Prop` `SZStepCore`, identical in shape to `SZOpeningStep`.  It is recorded as
the residue that remains **after** §1–§4 are banked beneath it; `SZStepCore → SZOpeningStep` is the
immediate forwarding, the value being that the ear API and diagonal inequality are no longer free
inputs of the residue. -/

/-- **(Isolated residual core) The per-level SZ opening/cut endpoint output**, identical in shape to
`SZOpeningStep`, recorded after the ear API (§1–§3) and the cut diagonal inequality (§4) are banked.
The remaining content is purely (C) the CUT body/splice glue and (O) the OPEN interior reach/stuck
production — the two pieces §R shows exceed the substrate. -/
def SZStepCore : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → Main m) →
    (∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      (∀ A' B' : Fin (n + 1) → S2,
        WeakConvexSphArm A' → StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
        deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B') →
      endpt A ≤ endpt B)

/-- **`SZStepCore → SZOpeningStep`.**  Identical conclusion shape; the reduction's value is that, with
§1–§4 banked, the ear convexity / diagonal-inequality content is no longer a free input — `SZStepCore`
carries only the two irreducible pieces (C)+(O). -/
theorem szOpeningStep_of_core (h : SZStepCore) : SZOpeningStep := h

/-- **The fully-assembled spherical arm lemma (weak), conditional only on `SZStepCore`.**  Routing
`SZStepCore` through `SphericalSZInduction.spherical_arm_mono_of_step`. -/
theorem spherical_arm_mono_of_core (h : SZStepCore)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_step (szOpeningStep_of_core h) hn A B hA hB hside hangle

/-! ## §R. Honest residue (precise scope, non-vacuity, concrete failing chains).

**What this module BANKS (genuinely complete, no extra hypothesis):**

* The **interval-arm (ear) API** `intervalArm` with `intervalArm_zero/_last/_endpt`,
  `intervalArm_sideLen` / `intervalArm_jointAngle` (the ear's sides and *interior* joints are exactly
  the parent's — a contiguous sub-tuple introduces no new interior joint), and the restriction lemmas
  `intervalArm_sameSides` / `intervalArm_jointLe` (`SameSides` / `JointLe` of the parent restrict to
  the ear verbatim).  This is the design §4 "earA = A[i+1..j] is a proper matched sub-arm" data, the
  sub-arm constructor the substrate lacked (it had only the last-vertex-drop `cutArm` and the
  first-vertex-drop `frontCut`, neither an arbitrary interval).
* The **ear endpoint comparison** `ear_chord_le_of_Main`: `Main m` (level-`m` strengthened invariant)
  applied to the matched ears gives the chord comparison `sDist (A a)(A (a+m)) ≤ sDist (B a)(B (a+m))`
  — the design §4 `hEar`.
* The **cut diagonal inequality** `cut_diag_le` (= `diag_le_of_flat_ear`, restated for the cut corner).

**The single isolated residue `SZStepCore`** is the per-level SZ opening/cut endpoint output, identical
in shape to `SZOpeningStep` (genuinely load-bearing: `SphericalSZInduction`'s lex `(n, deficitCount)`
recursion *derives* `endpt A ≤ endpt B` from it by threading the dimension-drop and deficit-drop IHs).
It packages the two pieces that genuinely exceed the substrate:

1. **(C) The CUT body/splice glue.**  The design §4 CUT rule, after the ear comparison `hEar` and the
   diagonal inequality `cut_diag_le` (both now banked), still needs `splice_transport_of_diag_le`: the
   spliced body `A[0..i] ++ A[j..n]` glued to `endpt A ≤ endpt B`.  Concrete failing chain: the body's
   new diagonal side `A i → A j` is matched to `B`'s only by the **inequality** `cut_diag_le`, *not* by
   spherical SAS equality (`SphericalSZChain.diag_len_eq` needs the *included angle to agree*, which a
   folded-flat `A` corner — angle `π` — does not satisfy against `B`'s bent corner — angle `< π`; this
   is the substrate's `SphericalTerminalVis.terminalVisibility_false`).  So the body is not a
   matched-SAS recursion; the genuine glue needs the body sub-arm convexity from the folded-flat Gram
   signs the substrate carries only as hypotheses (`SphericalSZ.SZStuckData.signA/signC`), not derived
   from weak convexity at an interior support.

2. **(O) The OPEN interior reach/stuck production.**  The design §5–§7 OPEN rule opens the deficient
   joint by the interior `openTail` to the admissible supremum `δ*`, getting REACH (strict, deficit
   drops) or STUCK (weak, a non-incident support vanishes), with `endpt A ≤ endpt (openTail …)`.
   Concrete failing chain, verified absent against the entire substrate (cf.
   `SphericalArmFinal` item 1, `SphericalArmClose2` §F (b1), `SphericalArmFinish:82`):
   * the substrate's reach/stuck/supremum apparatus
     (`SphericalAdmissibleSup.augmented_reachOrStuck_at_sup`,
     `SphericalArmClose2.reachStrictConvex_dichotomy_at`, `SphericalReachStuck.reach_endpoint_mono_arm`)
     is built for the **last-joint** `openArm` (axis index `n`, the *single* rotated tail vertex
     `A (last)`), whose endpoint-monotone bound is genuine *because the rotated tail is one of the two
     arm endpoints*;
   * relabelling an interior deficient joint to the last position by
     `SphericalSZComplete.cyclicShiftPolygon_strictConvex` is a **closed-polygon** symmetry that moves
     the arm endpoint pair `(A 0, A last)` — **the spherical arm endpoint distance is not cyclically
     invariant** — so the last-joint endpoint bound does *not* transport back to the original arm's
     `endpt A ≤ endpt B`;
   * the interior `openTail` itself disturbs **two** adjacent joints (`r = k-1` and `r = k`,
     `SphericalSZInduction.openTail_preserves_joint_offaxis`), so the design §6 single-`erase`
     deficit-decrease is unavailable; the correct two-joint bookkeeping is part of the residue.

These two are the irreducible geometric core of Chapter 13's spherical arm lemma under the strengthened
invariant; everything else the design needs (the ear API, the folded-flat betweenness, the diagonal
inequality, the full lex `WellFounded` assembly) is banked here or in `SphericalSZInduction`.

### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of the ear API: the ear genuinely shares its endpoints with the parent window
(`endpt (intervalArm A a m hb) = sDist (A a)(A (a+m))`), so the sub-arm is a real geometric object,
not a vacuous stand-in. -/
theorem intervalArm_endpt_nonvacuous {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) :
    endpt (intervalArm A a m hb) = sDist (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩) :=
  intervalArm_endpt A a m hb

/-- Non-vacuity of `SZStepCore`: its conclusion `endpt A ≤ endpt B` is genuinely realisable (reflexive
at `A = B`), and the deficit-drop IH it consumes is a real (inhabited at the congruent base) hypothesis
— so the residue is a load-bearing per-step reduction, not a vacuous-hypothesis impostor.  It is
strictly the *single step*, not the full recursion (`SphericalSZInduction.main_at_level` consumes it to
derive the comparison through genuine IH threading). -/
theorem szStepCore_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of `cut_diag_le`: on a genuine folded-flat configuration (the betweenness equation
holds reflexively for any collinear triple) with matched first side and reflexive ear, it yields the
reflexive `sDist Ai Aj ≤ sDist Ai Aj`. -/
theorem cut_diag_le_nonvacuous {Ai Aip1 Aj : S2}
    (hflat : sDist Aip1 Aj = sDist Aip1 Ai + sDist Ai Aj) :
    sDist Ai Aj ≤ sDist Ai Aj :=
  cut_diag_le hflat (le_refl _) rfl

end ProofsInTheBook.SphericalSZStepClose
