The short answer is: **there is no existing repo theorem that turns `signChangesFull A B = 2` directly into `TwoArcSplitData A B`**, and in the current API that is intentional. The files explicitly keep the two-arc cut extraction and per-arc monotonicity as the remaining geometric input: `cauchyArmVertexFull_of_links` takes `htwoArc : signChangesFull A B = 2 → TwoArcSplitData A B`, and the comments say this is the isolated two-arc residual. fileciteturn106file0L183-L197 The older arm file says the same for the non-full version: the cut selection and seam-joint comparison are supplied by `htwoArc`. fileciteturn113file0L61-L77

So the clean path is:

```lean
signChangesFull A B = 2
  + a real two-block/cut extraction certificate
  ⟹ t s + sign-definite arc hypotheses
  ⟹ twoArcSplitData_of_indices ...
```

not directly:

```lean
signChangesFull A B = 2 ⟹ twoArcSplitData_of_indices ...
```

## 1. Why `signChangesFull = 2` alone is not enough for your current builder

Your builder requires real numeric cuts

```lean
t s : ℕ
hts : t < s
hsn : s ≤ n
hm1 : 2 ≤ s - t
hm2 : 2 ≤ wrapLen n s t
```

and oriented monotonicity:

```lean
-- non-wrapping arc opens
hmono1   : ∀ i : Fin (s-t-1), jointAngle (subArc A t s ...) i ≤ jointAngle (subArc B t s ...) i
hstrict1 : ∃ i : Fin (s-t-1), jointAngle (subArc A t s ...) i < jointAngle (subArc B t s ...) i

-- wrapping arc closes
hmono2   : ∀ i : Fin (wrapLen n s t -1),
             jointAngle (subArcWrap B t s ...) i ≤ jointAngle (subArcWrap A t s ...) i
```

The file `Ch13SubArcWrap` says exactly that everything structural is discharged by `subArc_*`, `subArcWrap_*`, and `rotPoly_*`, but the per-arc monotonicity facts are **not** mechanically available from the cut indices and are taken as input. fileciteturn110file0L3-L16 The definition confirms that `twoArcSplitData_of_indices` consumes those three monotonicity hypotheses. fileciteturn110file0L24-L37

There are two reasons `cyclicFlips (nzSigns d) = 2` alone is too weak for the current builder.

First, zeros are skipped. The compressed nonzero sign list may have exactly two flips while the original full cyclic index set has zero-runs at the cut seams. You still need to choose how those zero-runs are assigned to the two closed arcs.

Second, the builder requires both arcs to be nondegenerate:

```lean
2 ≤ s - t
2 ≤ wrapLen n s t
```

A pure Boolean statement about the compressed nonzero signs does not automatically give those length bounds. For example, at a triangular link (`n = 2`, three link angles), a pattern like `[+, -, 0]` has `cyclicFlips (nzSigns d) = 2`, but no cut can make both complementary arcs have parameter at least `2`. The geometric two-arc lemma wants two genuine sub-arms, not just two sign blocks.

So the theorem you actually want should be phrased around a cut certificate, not only around `h2`.

## 2. Use a cut certificate as the bridge

Define the cut certificate directly over the full link-difference function:

```lean
structure TwoArcCut {n : ℕ} (d : Fin (n + 1) → ℝ) where
  t s : ℕ
  hts : t < s
  hsn : s ≤ n
  hm1 : 2 ≤ s - t
  hm2 : 2 ≤ Ch13SubArcWrap.wrapLen n s t

  /-- Non-wrapping arc interior vertices `t+1, ..., s-1` have `d ≥ 0`. -/
  nonwrap_nonneg :
    ∀ i : Fin (s - t - 1),
      0 ≤ d ⟨t + i.val + 1, by have := i.isLt; omega⟩

  /-- Some non-wrapping interior vertex has `d > 0`. -/
  nonwrap_pos :
    ∃ i : Fin (s - t - 1),
      0 < d ⟨t + i.val + 1, by have := i.isLt; omega⟩

  /-- Wrapping arc interior vertices `s+1, ..., n, 0, ..., t-1` have `d ≤ 0`. -/
  wrap_nonpos :
    ∀ i : Fin (Ch13SubArcWrap.wrapLen n s t - 1),
      d ((⟨i.val + 1, by
            have := i.isLt
            unfold Ch13SubArcWrap.wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩) ≤ 0
```

This is the exact content needed to feed your assembler.

Then prove:

```lean
noncomputable def twoArcSplitData_of_cut
    {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (cut : TwoArcCut (Ch13ArmVertexFull.linkDiff A B)) :
    TwoArcSplitData A B :=
  Ch13SubArcWrap.twoArcSplitData_of_indices
    hn A B hA hB hsides hclose
    cut.t cut.s cut.hts cut.hsn cut.hm1 cut.hm2
    (mono1_of_cut A B cut)
    (strict1_of_cut A B cut)
    (mono2_of_cut A B cut)
```

This gives you a small, honest `twoArc` field:

```lean
twoArc Q h2 :=
  twoArcSplitData_of_cut hn A B hA hB hsides hclose
    (twoArcCut_of_signChangesFull_eq_two h2)
```

where the hard theorem is now localized:

```lean
twoArcCut_of_signChangesFull_eq_two :
  signChangesFull A B = 2 →
  TwoArcCut (linkDiff A B)
```

or, more honestly if you have seam/length assumptions:

```lean
twoArcCut_of_signChangesFull_eq_two
  (husable : UsableTwoArcCut A B) :
  signChangesFull A B = 2 →
  TwoArcCut (linkDiff A B)
```

## 3. Monotonicity transfer: non-wrapping arc

This part is clean and already supported by repo lemmas.

`subArc_jointAngle` says:

```lean
jointAngle (subArc A t s hts hsn) i =
  jointAngle A ⟨t + i.val, ...⟩
```

for `i : Fin (s - t - 1)`. fileciteturn117file0L16-L28

`linkDiff_interior` says:

```lean
linkDiff A B ⟨i.val + 1, ...⟩ = jointDiff A B i
```

and `jointDiff A B i = jointAngle B i - jointAngle A i`. fileciteturn106file0L111-L117

So:

```lean
lemma mono1_of_cut
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (cut : TwoArcCut (Ch13ArmVertexFull.linkDiff A B)) :
    ∀ i : Fin (cut.s - cut.t - 1),
      jointAngle (subArc A cut.t cut.s cut.hts cut.hsn) i
        ≤ jointAngle (subArc B cut.t cut.s cut.hts cut.hsn) i := by
  intro i

  have hld :
      0 ≤ Ch13ArmVertexFull.linkDiff A B
        ⟨cut.t + i.val + 1, by have := i.isLt; omega⟩ :=
    cut.nonwrap_nonneg i

  let j : Fin (n - 1) := ⟨cut.t + i.val, by
    have hi := i.isLt
    have hsn := cut.hsn
    omega⟩

  have hj :
      Ch13ArmVertexFull.linkDiff A B
        ⟨j.val + 1, by have := j.isLt; omega⟩
        =
      jointDiff A B j :=
    Ch13ArmVertexFull.linkDiff_interior A B j

  have hld' : 0 ≤ jointDiff A B j := by
    simpa [j] using hld.trans_eq hj
  -- If `trans_eq` is awkward, rewrite the other direction:
  -- rw [show ⟨cut.t+i.val+1,_⟩ = ⟨j.val+1,_⟩ by ext; simp [j],
  --     Ch13ArmVertexFull.linkDiff_interior A B j] at hld

  rw [subArc_jointAngle, subArc_jointAngle]
  unfold jointDiff at hld'
  linarith
```

The strict witness is the same:

```lean
lemma strict1_of_cut
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (cut : TwoArcCut (Ch13ArmVertexFull.linkDiff A B)) :
    ∃ i : Fin (cut.s - cut.t - 1),
      jointAngle (subArc A cut.t cut.s cut.hts cut.hsn) i
        < jointAngle (subArc B cut.t cut.s cut.hts cut.hsn) i := by
  obtain ⟨i, hi⟩ := cut.nonwrap_pos
  refine ⟨i, ?_⟩

  let j : Fin (n - 1) := ⟨cut.t + i.val, by
    have hi' := i.isLt
    omega⟩

  have hld : 0 < jointDiff A B j := by
    have hk := hi
    rw [show (⟨cut.t + i.val + 1, by omega⟩ : Fin (n + 1))
          = (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (n + 1)) by
          apply Fin.ext; simp [j],
        Ch13ArmVertexFull.linkDiff_interior A B j] at hk
    exact hk

  rw [subArc_jointAngle, subArc_jointAngle]
  unfold jointDiff at hld
  linarith
```

The exact `omega` obligations depend on how you package `cut`, but the index map is:

```text
subArc joint i
↔ parent joint index       j = t + i
↔ full link angle index    k = t + i + 1
```

## 4. Monotonicity transfer: wrapped arc

For wrapped arcs, the repo already has:

```lean
subArcWrap_jointAngle :
  jointAngle (subArcWrap A t s hts hsn) i =
    jointAngle (rotPoly A ⟨s,...⟩) ⟨i.val,...⟩
```

fileciteturn109file0L170-L182

and

```lean
rotPoly_jointAngle :
  jointAngle (rotPoly A k) i =
    sphAngle (A (⟨i.val⟩ + k))
             (A (⟨i.val+1⟩ + k))
             (A (⟨i.val+2⟩ + k))
```

fileciteturn109file0L53-L61

You should add this helper once:

```lean
lemma linkDiff_wrap_joint
    {n : ℕ} (A B : Fin (n + 1) → S2)
    {t s : ℕ} (hts : t < s) (hsn : s ≤ n)
    (i : Fin (Ch13SubArcWrap.wrapLen n s t - 1)) :
    Ch13ArmVertexFull.linkDiff A B
      ((⟨i.val + 1, by
          have := i.isLt
          unfold Ch13SubArcWrap.wrapLen at this
          omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩)
      =
    jointAngle (Ch13SubArcWrap.subArcWrap B t s hts hsn) i
      -
    jointAngle (Ch13SubArcWrap.subArcWrap A t s hts hsn) i := by
  unfold Ch13ArmVertexFull.linkDiff
  rw [Ch13SubArcWrap.subArcWrap_jointAngle,
      Ch13SubArcWrap.subArcWrap_jointAngle]
  rw [Ch13SubArcWrap.rotPoly_jointAngle,
      Ch13SubArcWrap.rotPoly_jointAngle]
  unfold Ch13ArmVertexFull.linkAngle
  -- Now prove the three cyclic index equalities:
  -- k - 1 = ⟨i.val⟩ + s
  -- k     = ⟨i.val + 1⟩ + s
  -- k + 1 = ⟨i.val + 2⟩ + s
  congr 4 <;> apply Fin.ext <;>
    simp [Fin.val_add, Ch13SubArcWrap.wrapLen] <;> omega
```

Depending on how `Fin` addition normalizes, the last line may need separate `have` equations:

```lean
have hk_prev :
  (((⟨i.val + 1, _⟩ : Fin (n+1)) + ⟨s,_⟩) - 1)
    = (⟨i.val, _⟩ : Fin (n+1)) + ⟨s,_⟩ := by
  apply Fin.ext
  simp [Fin.sub_def, Fin.val_add, Ch13SubArcWrap.wrapLen]
  omega
```

Then `hmono2` is direct:

```lean
lemma mono2_of_cut
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (cut : TwoArcCut (Ch13ArmVertexFull.linkDiff A B)) :
    ∀ i : Fin (Ch13SubArcWrap.wrapLen n cut.s cut.t - 1),
      jointAngle (Ch13SubArcWrap.subArcWrap B cut.t cut.s cut.hts cut.hsn) i
        ≤ jointAngle (Ch13SubArcWrap.subArcWrap A cut.t cut.s cut.hts cut.hsn) i := by
  intro i
  have hld :
      Ch13ArmVertexFull.linkDiff A B
        ((⟨i.val + 1, by
            have := i.isLt
            unfold Ch13SubArcWrap.wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨cut.s, by omega⟩)
        ≤ 0 :=
    cut.wrap_nonpos i

  rw [linkDiff_wrap_joint A B cut.hts cut.hsn i] at hld
  linarith
```

The wrap index map is:

```text
subArcWrap joint i
↔ rotated joint index      i
↔ original full link index s + i + 1 mod (n+1)
```

That is precisely the interior of the wrapped arc:

```text
s+1, s+2, ..., n, 0, 1, ..., t-1
```

## 5. The cyclicFlips=2 decomposition lemma

There is no repo lemma of the form:

```lean
cyclicFlips (nzSigns d) = 2 →
  ∃ t s, TwoArcCut d
```

The current files only have:

```lean
cyclicFlips_even
cyclicFlips_eq_zero_iff_all_eq
all_same_sign
```

for the zero-change obstruction. fileciteturn111file0L45-L64 fileciteturn111file0L119-L141 fileciteturn111file0L173-L200

The correct new lemma should be a list-level block decomposition. I would not try to prove it directly on `nzSigns d`; include the original indices.

Define:

```lean
noncomputable def nzIdx {m : ℕ} (d : Fin m → ℝ) : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (d i ≠ 0))

noncomputable def nzSignedIdx {m : ℕ} (d : Fin m → ℝ) : List (Fin m × Bool) :=
  (nzIdx d).map (fun i => (i, decide (0 < d i)))
```

Then prove the purely list-theoretic lemma:

```lean
theorem cyclicFlips_two_blocks
    {ι : Type*} [DecidableEq ι]
    (xs : List (ι × Bool))
    (h2 : cyclicFlips (xs.map Prod.snd) = 2) :
    ∃ l₁ l₂ : List (ι × Bool),
      xs ~r (l₁ ++ l₂) ∧
      l₁ ≠ [] ∧ l₂ ≠ [] ∧
      (∀ x ∈ l₁, x.2 = true) ∧
      (∀ x ∈ l₂, x.2 = false)
    ∨
    ∃ l₁ l₂ : List (ι × Bool),
      xs ~r (l₁ ++ l₂) ∧
      l₁ ≠ [] ∧ l₂ ≠ [] ∧
      (∀ x ∈ l₁, x.2 = false) ∧
      (∀ x ∈ l₂, x.2 = true)
```

This proves the two-run fact on the compressed nonzero list.

Then a second theorem must lift from compressed nonzero runs to original full cyclic index intervals and produce `TwoArcCut`. That second step needs choices for zero runs and the nondegeneracy bounds:

```lean
theorem twoArcCut_of_two_blocks
    (hblocks : ...)
    (husable : both blocks determine arcs with hm1/hm2 and positive block can be made nonwrap)
    : TwoArcCut d
```

This split is far easier to debug than a monolithic theorem.

## 6. The positive block may be the wrapping block

Your `twoArcSplitData_of_indices` assumes:

```text
nonwrap arc opens: A ≤ B
wrap arc closes:   B ≤ A
```

If the positive/opening block crosses the `n → 0` seam, the nonwrapping block is the closing block and the wrapping block is the opening block. Then your current builder is oriented the wrong way.

You have three clean choices:

1. Choose `t,s` after a cyclic relabeling so the positive block is nonwrapping, then transport `TwoArcSplitData` back through a rotation. This is correct but adds a rotation-transport theorem for `TwoArcSplitData`.

2. Add a mirror builder:

```lean
twoArcSplitData_of_indices_wrapOpens
```

where `subArcWrap A` is Arc1/opening and `subArc A` is Arc2/closing.

3. Make `TwoArcCut` have two constructors:

```lean
inductive TwoArcCut d
| nonwrapOpens : ...
| wrapOpens : ...
```

and dispatch to the appropriate builder.

The least invasive is option 2: add a second builder with Arc1/Arc2 swapped. It uses the same structural lemmas; only the field assignments change.

## 7. Recommended implementation plan

Do it in this order:

1. **Keep `twoArcSplitData_of_indices`** as the assembler. It is already the right API.

2. Add local transfer lemmas:
   ```lean
   mono1_of_cut
   strict1_of_cut
   linkDiff_wrap_joint
   mono2_of_cut
   twoArcSplitData_of_cut
   ```

3. Define `TwoArcCut (linkDiff A B)` as the concrete certificate.

4. Only then decide whether to prove:
   ```lean
   signChangesFull A B = 2 → TwoArcCut (linkDiff A B)
   ```
   or keep this as the realization’s `twoArc` geometric residual.

Given the current repo architecture, the fully honest field can be:

```lean
twoArcCut : ∀ Q,
  signChangesFull (starP Q).vertexLink (linkQ Q) = 2 →
    TwoArcCut (linkDiff (starP Q).vertexLink (linkQ Q))
```

and then:

```lean
twoArc Q h2 :=
  twoArcSplitData_of_cut ... (twoArcCut Q h2)
```

This is strictly less circular than positing `TwoArcSplitData` directly: it says the real sign pattern has the expected two contiguous sign-definite arcs, while the actual sub-arms, side equalities, endpoint chords, and contradiction are still derived by the existing machinery.
