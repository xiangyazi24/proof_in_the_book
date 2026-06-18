## Decisive answer

**(a) Yes: “exactly two nonzero `linkDiff` entries of opposite sign” is geometrically impossible for a real equal-sided strict Cauchy link with equal closing chord.** But I would **not** close the gap by proving a separate local lemma of the form:

```lean
all-but-two-adjacent link angles equal
  + equal cyclic sides
  ⟹ the two adjacent link angles are equal
```

That statement is true as a corollary of Cauchy’s Lemma II, but proving it directly is not the minimal Lean route. It drags you into endpoint-angle / equality-case polygon rigidity. The cleaner route is to fix the **two-arc extraction interface**, not to pre-exclude seam patterns.

The key observation is that the existing two-arc contradiction does **not** need both sign blocks to lie in open arc interiors. It needs only:

```lean
arc 1: A ≤ B at all interior joints, with one strict interior joint
arc 2: B ≤ A at all interior joints, weakly
```

Then the strict arm lemma gives `chord_A < chord_B` on arc 1, while the weak arm lemma gives `chord_B ≤ chord_A` on arc 2, contradiction. That is exactly the shape of `cauchy_two_signchange_split`: one arc has `hmono1` plus `hstrict1`; the other arc has only weak `hmono2`. fileciteturn8file1L93-L172 The strict arm lemma underneath says equal-sided strict spherical arms with nondecreasing joints and one strict joint have strictly larger endpoint chord. fileciteturn10file0L67-L76

So the seam pattern is not a special geometric animal to kill before the arm lemma. It is a valid two-arc contradiction once the strict singleton is allowed to be the interior of **one** arc and the opposite singleton is allowed to sit on a cut endpoint.

## The seam example `[+, -, 0, 0]` is actually handled by a wrap-strict cut

For your example on `Fin 4`, with `n = 3` and

```text
d 0 > 0
d 1 < 0
d 2 = 0
d 3 = 0
```

choose:

```lean
t = 1
s = 3
```

Then:

```text
nonwrap arc: 1 → 2 → 3
  interior: 2
  sign: zero, so weak closing inequality holds

wrap arc: 3 → 0 → 1
  interior: 0
  sign: positive, so strict opening inequality holds
```

Both arcs have parameter length `2`:

```lean
s - t = 2
wrapLen 3 3 1 = 2
```

The negative sign at vertex `1` is a cut endpoint. That is fine. It is not needed for strictness, because the positive singleton at vertex `0` already gives the strict arm comparison on the wrapped arc. The current failure comes from trying to force both sign blocks into open interiors, or from forcing the strict arc to be the non-wrapping arc. That requirement is stronger than Cauchy’s two-arc proof needs.

## What to prove instead

The minimal true combinatorial object is not your old `TwoArcCut`. It is an **oriented one-strict-arc cut**.

Conceptually:

```lean
inductive ArcKind
  | nonwrap
  | wrap

inductive SignDir
  | pos   -- strict arc has 0 < linkDiff, so A opens to B
  | neg   -- strict arc has linkDiff < 0, so B opens to A
```

Then use four concrete structures instead of dependent `if`s, because Lean will be happier:

```lean
structure PosNonwrapCut {n : ℕ} (d : Fin (n+1) → ℝ) where
  t s : ℕ
  hts : t < s
  hsn : s ≤ n
  hmN : 2 ≤ s - t
  hmW : 2 ≤ Ch13SubArcWrap.wrapLen n s t
  nonwrap_nonneg : ∀ i : Fin (s - t - 1), 0 ≤ d (nonwrapIdx t s i)
  nonwrap_pos    : ∃ i : Fin (s - t - 1), 0 < d (nonwrapIdx t s i)
  wrap_nonpos    : ∀ i : Fin (Ch13SubArcWrap.wrapLen n s t - 1),
                     d (wrapIdx n t s i) ≤ 0

structure PosWrapCut {n : ℕ} (d : Fin (n+1) → ℝ) where
  t s : ℕ
  hts : t < s
  hsn : s ≤ n
  hmN : 2 ≤ s - t
  hmW : 2 ≤ Ch13SubArcWrap.wrapLen n s t
  wrap_nonneg    : ∀ i : Fin (Ch13SubArcWrap.wrapLen n s t - 1),
                     0 ≤ d (wrapIdx n t s i)
  wrap_pos       : ∃ i : Fin (Ch13SubArcWrap.wrapLen n s t - 1),
                     0 < d (wrapIdx n t s i)
  nonwrap_nonpos : ∀ i : Fin (s - t - 1), d (nonwrapIdx t s i) ≤ 0
```

Then add the two negative variants by reversing the inequalities:

```lean
NegNonwrapCut
NegWrapCut
```

and bundle them as:

```lean
abbrev OneStrictTwoArcCut {n : ℕ} (d : Fin (n+1) → ℝ) :=
  PosNonwrapCut d ⊕ PosWrapCut d ⊕ NegNonwrapCut d ⊕ NegWrapCut d
```

The current repo already isolates the fact that `twoArcSplitData_of_indices` needs real numeric cuts, nondegenerate lengths, and per-arc monotonicity; the failed step is trying to derive those facts from `cyclicFlips (nzSigns d) = 2` in the too-rigid “both blocks interior” form. fileciteturn1file1L20-L44 It also explicitly notes that nondegenerate arc lengths are real extra requirements; for a triangular link, a `[+, -, 0]` Boolean pattern cannot provide two arms of length at least `2`. fileciteturn1file1L50-L57

## Builder route

Keep `TwoArcSplitData` and `cauchy_two_signchange_split`. Add symmetric builders.

For positive strict nonwrap, the existing orientation is essentially right:

```lean
noncomputable def twoArcSplitData_of_posNonwrapCut
    {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n+1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) =
              sDist (B 0) (B (Fin.last n)))
    (cut : PosNonwrapCut (Ch13ArmVertexFull.linkDiff A B)) :
    TwoArcSplitData A B :=
  Ch13SubArcWrap.twoArcSplitData_of_indices
    hn A B hA hB hsides hclose
    cut.t cut.s cut.hts cut.hsn cut.hmN cut.hmW
    (mono_nonwrap_pos A B cut)
    (strict_nonwrap_pos A B cut)
    (mono_wrap_nonpos A B cut)
```

For the seam case, add the symmetric wrap-strict builder:

```lean
noncomputable def twoArcSplitData_of_posWrapCut
    {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n+1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) =
              sDist (B 0) (B (Fin.last n)))
    (cut : PosWrapCut (Ch13ArmVertexFull.linkDiff A B)) :
    TwoArcSplitData A B := by
  -- Build `TwoArcSplitData` directly:
  -- Arc1/Brc1 are the WRAPPED strict-opening arcs.
  -- Arc2/Brc2 are the NONWRAPPING weak-closing arcs.
  refine
    { m₁ := Ch13SubArcWrap.wrapLen n cut.s cut.t
      m₂ := cut.s - cut.t
      hm₁ := cut.hmW
      hm₂ := cut.hmN
      Arc1 := Ch13SubArcWrap.subArcWrap A cut.t cut.s cut.hts cut.hsn
      Brc1 := Ch13SubArcWrap.subArcWrap B cut.t cut.s cut.hts cut.hsn
      Arc2 := Ch13SubArc.subArc A cut.t cut.s cut.hts cut.hsn
      Brc2 := Ch13SubArc.subArc B cut.t cut.s cut.hts cut.hsn
      harc1A := ...
      harc1B := ...
      harc2A := ...
      harc2B := ...
      hsides1 := ...
      hsides2 := ...
      hshareA := ...
      hshareB := ...
      hmono1 := mono_wrap_pos A B cut
      hstrict1 := strict_wrap_pos A B cut
      hmono2 := mono_nonwrap_nonpos A B cut }
```

The structural fields are already routine: the repo’s wrapped-subarc layer was built exactly so wrapped arcs become genuine contiguous spherical arms after rotation, and its notes say the structural pieces are discharged by `subArc_*`, `subArcWrap_*`, and `rotPoly_*`, while monotonicity is the input that must be transported from signs. fileciteturn1file1L234-L242 For nonwrapping monotonicity, the needed index map is already the one in your audit: subarc joint `i` corresponds to parent joint `t+i`, hence full link angle index `t+i+1`. fileciteturn1file1L226-L232

For negative strict cuts, do not invent new geometry. Swap the roles of `A` and `B` inside the constructed `TwoArcSplitData`:

```lean
-- strict negative means jointAngle B < jointAngle A.
-- So make the strict arc compare B ≤ A.

Arc1 := strict subarc of B
Brc1 := strict subarc of A
Arc2 := complement subarc of B
Brc2 := complement subarc of A
```

Then `hmono1` is `B ≤ A` with strictness, and `hmono2` is the weak opposite comparison. The contradiction theorem is insensitive to the original parameter names; it only consumes the four arms, side equalities, shared chords, and joint inequalities.

## The combinatorial lemma that is actually true

For `n ≥ 3` (`Fin (n+1)` has at least four link vertices), prove:

```lean
theorem oneStrictTwoArcCut_of_signChangesFull_eq_two
    {n : ℕ} (hn : 3 ≤ n) (A B : Fin (n+1) → S2)
    (h2 : Ch13ArmVertexFull.signChangesFull A B = 2) :
    OneStrictTwoArcCut (Ch13ArmVertexFull.linkDiff A B)
```

Proof idea:

Take the cyclic nonzero signs. Since `cyclicFlips = 2`, there are exactly two cyclic sign blocks. Pick one whole block as the **strict arc interior** and the complement as the weak opposite arc. If the chosen block would wrap across `0`, use `PosWrapCut` or `NegWrapCut`. If the chosen block has length `n` and its opposite block is a singleton, choose the singleton block instead. This is why the nondegeneracy bound works when `n ≥ 3`: a singleton strict block gives an arc of length `2`, and its complement has length at least `2`.

This lemma is pure combinatorics, but it is a different combinatorics from the false one. It does **not** require both sign blocks to be interior.

## The triangular base case

For `n = 2`, a link is a spherical triangle. There is no valid two-arc split with both arc parameters at least `2`. Handle it separately:

```lean
theorem triangle_linkDiff_eq_zero_of_equal_sides
    (A B : Fin 3 → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin 2, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last 2)) =
              sDist (B 0) (B (Fin.last 2))) :
    ∀ k : Fin 3, Ch13ArmVertexFull.linkDiff A B k = 0
```

Use spherical SSS, or derive each angle equality from the strict hinge lemma by contradiction: if one corresponding triangle angle were strictly larger, the opposite side would be strictly larger, contradicting the corresponding side equality. In the repo’s presentation, equal side lengths for the closed polygon are exactly `hsides` for the arm sides plus `hclose` for the closing side. fileciteturn8file1L19-L29

Then:

```lean
n = 2 ⟹ ∀ k, linkDiff A B k = 0 ⟹ nzSigns linkDiff = [] ⟹ signChangesFull = 0
```

so `signChangesFull = 2` is impossible.

## Bottom line

Do **not** close this by a special geometric exclusion lemma for seam patterns.

Close it by replacing the false extraction

```lean
signChangesFull = 2
  ⟹ both sign blocks are open-arc interiors
  ⟹ TwoArcSplitData
```

with the true extraction

```lean
signChangesFull = 2
  ⟹ one sign block is a strict open-arc interior
      and the complementary arc is weakly opposite
  ⟹ TwoArcSplitData
```

plus the `n = 2` spherical-triangle SSS base case.

So:

**(a)** exactly two nonzero opposite signs are impossible.

**(b)** the minimal Lean route is `OneStrictTwoArcCut` + symmetric nonwrap/wrap builders + triangle base case.

**(c)** the arm lemma itself does not need a new endpoint-strict theorem. The existing two-arc contradiction already has the right asymmetric strict/weak shape. What must be extended is the **cut certificate / `TwoArcSplitData` builder**, not the geometric arm engine.
